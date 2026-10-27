From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type function product programs own cont uninit int sum type_sum
  uniq_bor borrow place place_own place_sum.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

Section place_sum.
  Context `{!typeG Σ}.

  (*
  Reborrowing a field of the payload of a sum behind a unique borrow:

  ```
  fn get_some_first<'a>(x: &'a mut Option<(i32, i32)>) -> Option<&'a mut i32> {
      match x { Some(p) => Some(&mut p.0), None => None }
  }
  ```

  with the specification: if `old(x) == None`, then `result == None` and
  `fin(x) == None`; if `old(x) == Some(a)`, then `result == Some(r)` with
  `*r == a.0` and `fin(x) == Some(( *fin(r), a.1))`. The referent of `x` is a place
  ([tctx_uniq_to_place]); reading its discriminant ([type_case_place_root]) unfolds it,
  in the branch of `Some`, into the sum place `SumLty tyl 1 (OfTy (int * int))`, whose
  payload is unfolded into a pair ([tctx_unfold_place_prod] at the context
  `PSum tyl 1 _ PHole`). Field `.0` of the payload is reborrowed (at the path
  `PSum _ 1 _ (PFst PHole _)`, offset 1); to drop `x`, field `.1` is reborrowed too and
  this reborrow is resolved; `x` is dropped while both leaves are blocked
  ([tctx_drop_place_cpd]). In the branch of `None`, the sum place is folded back
  ([tctx_fold_place_sum]) and `x` is resolved.
  *)

  Notation opt_pair := (Σ! +[(); int * int])%T.
  Notation opt_pairₛ := (Σ! [unitₛ; (Zₛ * Zₛ)%ST])%ST.
  Notation opt_ref α := (Σ! +[(); &uniq{α} int])%T.
  Notation opt_refₛ := (Σ! [unitₛ; uniq_borₛ Zₛ])%ST.

  Definition get_some_first : val :=
    fn: ["x"] :=
      let: "b" := !"x" in
      delete [ #1; "x"];;
      let: "r" := new [ #2] in
      case: !"b" of
      [ Skip;;                  (* None: resolve b *)
        "r" <-{Σ 0} ();;
        return: ["r"];
        ReBor;;                 (* Some(p): &mut p.0 *)
        ReBor;;                 (* &mut p.1, to drop b *)
        Skip;;                  (* resolve the borrow of p.1, drop b *)
        "r" <-{Σ 1} "b" +ₗ #1;;
        return: ["r"]].

  Definition get_some_first_spec : fn_spec [uniq_borₛ opt_pairₛ] opt_refₛ () :=
    λ _ post '-[(_, m)], λ mask π,
      (∀ pad, uniq_bor_current (𝔄:=opt_pairₛ) m = (pinj (Xl:=[unitₛ; (Zₛ * Zₛ)%ST]) 0%fin (), pad) →
        uniq_bor_future (𝔄:=opt_pairₛ) m π = vπ (uniq_bor_current (𝔄:=opt_pairₛ) m) π →
        ∀ (lr: loc) pad', post (lr, (pinj (Xl:=[unitₛ; uniq_borₛ Zₛ]) 0%fin (), pad')) mask π) ∧
      (∀ (a: Z * Z) pad,
        uniq_bor_current (𝔄:=opt_pairₛ) m = (pinj (Xl:=[unitₛ; (Zₛ * Zₛ)%ST]) 1%fin a, pad) →
        ∀ (lr: loc) (r: ~~ (uniq_borₛ Zₛ)) pad',
          uniq_bor_current r = a.1 →
          uniq_bor_future (𝔄:=opt_pairₛ) m π =
            (pinj (Xl:=[unitₛ; (Zₛ * Zₛ)%ST]) 1%fin (uniq_bor_future r π, a.2), pad) →
          post (lr, (pinj (Xl:=[unitₛ; uniq_borₛ Zₛ]) 1%fin r, pad')) mask π).

  Lemma get_some_first_type :
    typed_val get_some_first
      ((fn<α>(∅; &uniq{α} opt_pair) → opt_ref α) get_some_first_spec)
      (get_some_first, ()).
  Proof.
    unfold get_some_first. unlock.
    opose proof (@type_fn _ _ _ [uniq_borₛ opt_pairₛ] opt_refₛ () ()
      (λ α, FP ∅ +[&uniq{α} opt_pair]%T (opt_ref α) AtomicClosed)
      get_some_first_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros α ϝ k wl. destruct wl as [vx []]. simpl_subst.
    (* [α] is alive (proved once and reused). *)
    have Alv: lctx_lft_alive (fp_E (FP ∅ +[&uniq{α} opt_pair]%T (opt_ref α) AtomicClosed) ϝ)
      [ϝ ⊑ₗ []] α.
    { eapply lctx_lft_alive_external; [rewrite /fp_E /=; by left|solve_typing]. }
    have Alv2: lctx_lft_alive (fp_E (FP ∅ +[&uniq{α} opt_pair]%T (opt_ref α) AtomicClosed) ϝ)
      [ϝ ⊑ₗ []] (α ⊓ α) by apply lctx_lft_alive_intersect.
    iApply (typed_body_impl with "[]"); last first. {
      (* let b := !x *)
      iApply (type_let with "[]").
      { eapply (type_deref_instr (own_ptr 1 (&uniq{α} opt_pair)) (&uniq{α} opt_pair)).
        - apply uniq_stack_okay.
        - done.
        - apply (read_own_move (&uniq{α} opt_pair)). }
      { apply tctx_extract_elt_here_exact. }
      { reflexivity. }
      iIntros (vb). simpl_subst.
      (* delete x *)
      iApply type_delete. { solve_typing. } { done. } { done. }
      (* the result *)
      iApply (type_new 2). { lia. } iIntros (vr). simpl_subst.
      (* the referent of b as a place; match *)
      iApply typed_body_tctx_incl.
      { eapply tctx_incl_trans; [apply tctx_incl_swap|].
        eapply (tctx_incl_frame_r +[_] +[_]). apply tctx_uniq_to_place. }
      iApply (type_case_place_root _ _ _ _ vb α +[(); int * int]%T _ _ _ -[_; _]); [done|].
      iSplitL; [|iSplitL; [|done]].
      - (* None: fold back, resolve b *)
        iApply typed_body_tctx_incl.
        { eapply tctx_incl_trans; [eapply (tctx_incl_frame_r +[_] +[_]);
            apply (tctx_fold_place_sum _ _ vb α PHole); [done|done]|].
          eapply (tctx_incl_frame_r +[_] +[_]). apply tctx_place_to_uniq. }
        iApply type_resolve. { solve_typing. } { by apply uniq_bor.uniq_resolve. }
        iApply (type_sum_unit +[(); &uniq{α} int]%T 0%fin);
          [reflexivity|solve_typing|by apply write_own|
           apply (resolve'_just _ _ _ (const True)); apply resolve_just|solve_typing|].
        iApply type_jump.
        { rewrite elem_of_list_singleton. reflexivity. }
        { solve_typing. }
        { solve_typing. }
        { reflexivity. }
      - (* Some(p): unfold the payload *)
        iApply typed_body_tctx_incl.
        { eapply (tctx_incl_frame_r +[_] +[_]).
          apply (tctx_unfold_place_prod _ _ vb α (PSum +[(); int * int]%T 1%fin (0, 0)%Z PHole)
            int int); [done|done]. }
        (* &mut p.0, at α ⊓ α *)
        iApply type_seq.
        { apply (type_reborrow_place_instr _ _ _ vb α α
            (PSum +[(); int * int]%T 1%fin (0, 0)%Z (PFst PHole (OfTy int))) int);
            [done|done|done]. }
        { solve_typing. } { reflexivity. }
        (* &mut p.1, at α ⊓ α *)
        iApply type_seq.
        { apply (type_reborrow_place_instr _ _ _ vb α α
            (PSum +[(); int * int]%T 1%fin (0, 0)%Z (PSnd (Blocked int (α ⊓ α)) PHole)) int);
            [done|done|done]. }
        { solve_typing. } { reflexivity. }
        (* resolve the borrow of p.1 *)
        iApply type_resolve. { solve_typing. } { by apply uniq_bor.uniq_resolve. }
        (* drop b while both leaves of the payload are blocked *)
        iApply typed_body_tctx_incl.
        { apply (tctx_incl_frame_r +[_] +[] +[_; _]). apply tctx_drop_place_cpd; [done|done|done]. }
        (* the result: Some(&mut p.0) *)
        iApply (type_sum_assign +[(); &uniq{α ⊓ α} int]%T 1%fin);
          [reflexivity|solve_typing|by apply write_own|
           apply (resolve'_just _ _ _ (const True)); apply resolve_just|].
        iApply type_jump.
        { rewrite elem_of_list_singleton. reflexivity. }
        { solve_typing. }
        { solve_typing. }
        { reflexivity. }
    }
    intros post [[lx m] []] mask π. simpl.
    destruct m as [[[[[l [s pad]] ξi] d] g] idx]. simpl.
    intros [HNone HSome].
    rewrite /trans_upper /trans_tail /=.
    destruct s as [[]|[a|[]]]; simpl.
    - intros z _ l0 _ _ Hres pad0 z0 ->.
      eapply HNone; [done|by rewrite uniq_bor_future_eq /= Hres].
    - intros z _ l0 _ m1 Hl1 Hc1 m2 Hl2 Hc2 Hres Hfin pad0 z0 ->. simpl.
      apply (HSome a pad); [done|by rewrite Hc1 /psum_proj_or /=|].
      rewrite Hfin.
      destruct m1 as [[[[[l1 y1] ζi] d1] g1] idx1].
      destruct m2 as [[[[[l2 y2] ηi] d2] g2] idx2].
      rewrite /psum_proj_or /= in Hc1 Hc2. simpl in Hres. subst y1 y2.
      rewrite /place_cur /place_rfn /= uniq_bor_future_eq. by rewrite Hres.
  Qed.

  (*
  Updating a local `Option<i32>` in place:

  ```
  fn bump(mut x: Option<i32>) -> Option<i32> {
      match x {
          None => x = Some(0),                  // a new variant
          Some(_) => { let r = &mut x.0; *r = 7; }
      }
      x
  }
  ```

  with the specification `ensures result == Some(if old(x) == None { 0 } else { 7 })`.
  The argument `x` is an owned place ([tctx_own_to_oplace]); reading its discriminant
  ([type_case_oplace]) unfolds it into a sum place. In the branch of `None`, it is
  folded back ([tctx_fold_oplace_sum]) and assigned `Some(0)`
  ([type_sum_assign_oplace_instr]). In the branch of `Some`, the payload is borrowed at a
  fresh lifetime (at the path `PSum _ 1 _ PHole`, [type_borrow_oplace_instr]), written
  through the borrow, unblocked when the lifetime ends ([unblock_tctx_oplace]), and the
  sum place is folded back.
  *)

  Notation opt_int := (Σ! +[(); int])%T.
  Notation opt_intₛ := (Σ! [unitₛ; Zₛ])%ST.

  Definition bump : val :=
    fn: ["x"] :=
      case: !"x" of
      [ let: "zero" := #0 in      (* None: x = Some(0) *)
        "x" <-{Σ 1} "zero";;
        return: ["x"];
        Newlft;;                  (* Some(_): *(&mut x.0) = 7 *)
        let: "r" := (Skip;; Skip);; "x" +ₗ #1 in
        let: "seven" := #7 in
        "r" <- "seven";;
        Skip;;                    (* resolve r *)
        Endlft;;                  (* unblock x.0 *)
        return: ["x"]].

  Definition bump_spec : fn_spec [opt_intₛ] opt_intₛ () :=
    λ _ post '-[(_, x)], λ mask π,
      (∀ pad, x = (pinj (Xl:=[unitₛ; Zₛ]) 0%fin (), pad) →
        ∀ (lr: loc) pad', post (lr, (pinj (Xl:=[unitₛ; Zₛ]) 1%fin 0%Z, pad')) mask π) ∧
      (∀ (a: Z) pad, x = (pinj (Xl:=[unitₛ; Zₛ]) 1%fin a, pad) →
        ∀ (lr: loc) pad', post (lr, (pinj (Xl:=[unitₛ; Zₛ]) 1%fin 7%Z, pad')) mask π).

  Lemma bump_type :
    typed_val bump ((fn(∅; opt_int) → opt_int) bump_spec) (bump, ()).
  Proof.
    unfold bump. unlock.
    opose proof (@type_fn _ _ _ [opt_intₛ] opt_intₛ () ()
      (λ _: (), FP ∅ +[opt_int] opt_int AtomicClosed)
      bump_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros c ϝ k wl. destruct wl as [vx []]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      (* x as an owned place; match *)
      iApply typed_body_tctx_incl. { apply tctx_own_to_oplace. }
      iApply (type_case_oplace _ _ _ _ vx 2 PHole +[(); int]%T _ _ _ -[_; _]).
      iSplitL; [|iSplitL; [|done]].
      - (* None: fold back, x = Some(0) *)
        iApply typed_body_tctx_incl. { apply (tctx_fold_oplace_sum _ _ vx 2 PHole +[(); int]%T 0%fin). }
        iApply type_int. iIntros (v0). simpl_subst.
        iApply type_seq.
        { apply (type_sum_assign_oplace_instr _ _ _ vx v0 2 PHole +[(); int]%T 1%fin
            (const (const True))); [done|apply resolve_just]. }
        { solve_typing. } { reflexivity. }
        iApply typed_body_tctx_incl.
        { eapply (tctx_incl_frame_r +[_] +[_]). apply tctx_oplace_to_own. }
        iApply type_jump.
        { rewrite elem_of_list_singleton. reflexivity. }
        { solve_typing. }
        { solve_typing. }
        { reflexivity. }
      - (* Some(_): borrow the payload, write through the borrow *)
        simpl.
        iApply (type_newlft []). iIntros (β).
        iApply (type_let with "[]").
        { eapply (type_borrow_oplace_instr _ _ _ vx _ β (PSum +[(); int]%T 1%fin 0%Z PHole) int).
          solve_typing. }
        { solve_typing. } { reflexivity. }
        iIntros (vr). simpl_subst.
        iApply type_int. iIntros (v7). simpl_subst.
        iApply type_assign. { solve_typing. } { apply write_uniq. solve_typing. }
        { apply (resolve'_just _ _ _ (const True)). apply resolve_just. }
        iApply type_resolve. { solve_typing. } { apply uniq_bor.uniq_resolve. solve_typing. }
        (* end β: unblock x.0 *)
        iApply (type_endlft _ _ _ _ β).
        { solve_typing. }
        { apply unblock_tctx_cons_just_hasty.
          apply (unblock_tctx_oplace _ _ _ (PSum +[(); int]%T 1%fin 0%Z PHole) int);
            [solve_typing|].
          apply unblock_tctx_nil. }
        (* fold back, return x *)
        iApply typed_body_tctx_incl.
        { eapply tctx_incl_trans; [apply tctx_incl_swap|].
          eapply (tctx_incl_frame_r +[_] +[_]).
          eapply tctx_incl_trans; [apply (tctx_fold_oplace_sum _ _ vx 2 PHole +[(); int]%T 1%fin)|].
          apply tctx_oplace_to_own. }
        iApply type_jump.
        { rewrite elem_of_list_singleton. reflexivity. }
        { solve_typing. }
        { solve_typing. }
        { reflexivity. }
    }
    intros post [[lx [s pad]] []] mask π. simpl.
    intros [HNone HSome].
    rewrite /trans_upper /trans_tail /=.
    destruct s as [[]|[a|[]]]; simpl.
    - intros _ pad0. by apply (HNone pad).
    - intros [[[[[l1 w1] ζi] d1] g1] idx1] Hc1 [[[[[l2 w2] ζi'] d2] g2] idx2] Hupd Hres
        [? [[[lx' [s' pad']] ζm'] []]] (_ & Hlx & Hs' & _ & Hfin & _).
      destruct Hupd as (_ & -> & ->). simpl in Hc1, Hres, Hfin, Hs', Hlx |- *.
      rewrite Hlx Hs' Hfin /oplace_blk_fin /= (uniq_prvar_app_irrel (𝔄:=[unitₛ; Zₛ] !!ₗ 1%fin) _ 7%Z ζi π) Hres.
      by apply (HSome a pad).
  Qed.

  (*
  Writing the payload of a sum directly, without a reborrow:

  ```
  fn set_some<'a>(x: &'a mut Option<i32>) {
      if let Some(v) = x { *v = 5 }
  }
  ```

  with the specification `ensures fin(x) == if old(x) == None { None } else { Some(5) }`.
  In the branch of `Some`, the payload is written in place ([type_write_place_instr] at
  the context `PSum _ 1 _ PHole`); in both branches, the sum place is folded back and
  `x` is resolved.
  *)

  Definition set_some : val :=
    fn: ["x"] :=
      let: "b" := !"x" in
      delete [ #1; "x"];;
      case: !"b" of
      [ Skip;;                  (* None: resolve b *)
        let: "r" := new [ #0] in
        return: ["r"];
        let: "five" := #5 in    (* Some(v): *v = 5 *)
        "b" +ₗ #1 <- "five";;
        Skip;;                  (* resolve b *)
        let: "r" := new [ #0] in
        return: ["r"]].

  Definition set_some_spec : fn_spec [uniq_borₛ opt_intₛ] () () :=
    λ _ post '-[(_, m)], λ mask π,
      (∀ pad, uniq_bor_current (𝔄:=opt_intₛ) m = (pinj (Xl:=[unitₛ; Zₛ]) 0%fin (), pad) →
        uniq_bor_future (𝔄:=opt_intₛ) m π = (pinj (Xl:=[unitₛ; Zₛ]) 0%fin (), pad) →
        ∀ (lr: loc), post (lr, ()) mask π) ∧
      (∀ (a: Z) pad, uniq_bor_current (𝔄:=opt_intₛ) m = (pinj (Xl:=[unitₛ; Zₛ]) 1%fin a, pad) →
        uniq_bor_future (𝔄:=opt_intₛ) m π = (pinj (Xl:=[unitₛ; Zₛ]) 1%fin 5%Z, pad) →
        ∀ (lr: loc), post (lr, ()) mask π).

  Lemma set_some_type :
    typed_val set_some ((fn<α>(∅; &uniq{α} opt_int) → ()) set_some_spec) (set_some, ()).
  Proof.
    unfold set_some. unlock.
    opose proof (@type_fn _ _ _ [uniq_borₛ opt_intₛ] () () ()
      (λ α, FP ∅ +[&uniq{α} opt_int]%T ()%T AtomicClosed)
      set_some_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros α ϝ k wl. destruct wl as [vx []]. simpl_subst.
    have Alv: lctx_lft_alive (fp_E (FP ∅ +[&uniq{α} opt_int]%T ()%T AtomicClosed) ϝ)
      [ϝ ⊑ₗ []] α.
    { eapply lctx_lft_alive_external; [rewrite /fp_E /=; by left|solve_typing]. }
    iApply (typed_body_impl with "[]"); last first. {
      iApply (type_let with "[]").
      { eapply (type_deref_instr (own_ptr 1 (&uniq{α} opt_int)) (&uniq{α} opt_int)).
        - apply uniq_stack_okay.
        - done.
        - apply (read_own_move (&uniq{α} opt_int)). }
      { apply tctx_extract_elt_here_exact. }
      { reflexivity. }
      iIntros (vb). simpl_subst.
      iApply type_delete. { solve_typing. } { done. } { done. }
      (* the referent of b as a place; match *)
      iApply typed_body_tctx_incl. { apply tctx_uniq_to_place. }
      iApply (type_case_place_root _ _ _ _ vb α +[(); int]%T _ _ _ -[_; _]); [done|].
      iSplitL; [|iSplitL; [|done]].
      - (* None: fold back, resolve b *)
        iApply typed_body_tctx_incl.
        { eapply tctx_incl_trans; [apply (tctx_fold_place_sum _ _ vb α PHole +[(); int]%T 0%fin);
            [done|done]|].
          apply tctx_place_to_uniq. }
        iApply type_resolve. { solve_typing. } { by apply uniq_bor.uniq_resolve. }
        iApply (type_new_subtype () 0). { lia. } { apply uninit_unit_1. }
        iIntros (vr). simpl_subst.
        iApply type_jump.
        { rewrite elem_of_list_singleton. reflexivity. }
        { solve_typing. }
        { solve_typing. }
        { reflexivity. }
      - (* Some(v): *v = 5 *)
        simpl.
        iApply type_int. iIntros (v5). simpl_subst.
        iApply type_seq.
        { apply (type_write_place_instr _ _ _ vb v5 α (PSum +[(); int]%T 1%fin 0%Z PHole) int
            (const (const True))); [done|done|done|done|apply resolve_just]. }
        { solve_typing. } { reflexivity. }
        iApply typed_body_tctx_incl.
        { eapply (tctx_incl_frame_r +[_] +[_]).
          eapply tctx_incl_trans; [apply (tctx_fold_place_sum _ _ vb α PHole +[(); int]%T 1%fin);
            [done|done]|].
          apply tctx_place_to_uniq. }
        iApply type_resolve. { solve_typing. } { by apply uniq_bor.uniq_resolve. }
        iApply (type_new_subtype () 0). { lia. } { apply uninit_unit_1. }
        iIntros (vr). simpl_subst.
        iApply type_jump.
        { rewrite elem_of_list_singleton. reflexivity. }
        { solve_typing. }
        { solve_typing. }
        { reflexivity. }
    }
    intros post [[lx m] []] mask π. simpl.
    destruct m as [[[[[l [s pad]] ξi] d] g] idx]. simpl.
    intros [HNone HSome]. rewrite /trans_upper /trans_tail /=.
    destruct s as [[]|[a|[]]]; simpl.
    - intros z _ _ Hres l0 junk. match goal with |- post (_, ?u) _ _ => destruct u end.
      eapply HNone; [done|by rewrite uniq_bor_future_eq].
    - intros z _ _ [[[[[[l' [s' pad']] ξi'] d'] g'] idx'] ζm'] Hl' Hcur Hfut _. simpl.
      intros _ Hres l1 junk. match goal with |- post (_, ?u) _ _ => destruct u end.
      eapply HSome; [done|].
      rewrite /place_bor /= in Hfut Hcur. injection Hcur as -> ->.
      rewrite -Hfut uniq_bor_future_eq. exact Hres.
    Unshelve. all: eapply (composeₛ empty_prod_to_unitₛ uninit0_to_unitₛ).
  Qed.
End place_sum.

Print Assumptions get_some_first_type.
Print Assumptions bump_type.
Print Assumptions set_some_type.


