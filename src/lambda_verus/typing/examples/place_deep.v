From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type function product programs own cont uninit int sum type_sum
  uniq_bor shr_bor borrow place place_own place_resolve place_puniq place_pshr place_deep.
From lrust.lang Require Import lang notation memcpy new_delete.
Set Default Proof Using "Type".

Section place_deep.
  Context `{!typeG Σ}.

  (*
  Copying and assigning a pair through two levels of mutable references:

  ```
  fn swap_snd<'a, 'b>(x: &'a mut &'b mut (i32, (i32, i32)), y: (i32, i32)) -> (i32, i32) {
      let c = ( **x).1;   // copy out of ( **x).1 (two cells)
      ( **x).1 = y;       // assign ( **x).1 (two cells)
      c
  }
  ```

  with the specification `ensures result == ( **old(x)).1,
  fin(x) == ((( **old(x)).0, y), fin( *old(x)))`. The argument slot is an owned place;
  `*x`, `**x` and the pair `**x` are unfolded; `( **x).1` (in [Owned] mode inside the node
  of the inner borrow) is copied out ([type_memcpy_copy_from_oplace_deep_instr]) and
  assigned ([type_memcpy_oplace_deep_instr]); the place is folded back and dropped.
  *)

  Definition swap_snd : val :=
    fn: ["x"; "y"] :=
      ReBor;; ReBor;; ReBor;;                   (* unfold *x, **x, **x as a pair *)
      let: "c" := new [ #2] in
      "c" <-{2} !(!(!"x") +ₗ #1);;               (* c = ( **x).1 *)
      !(!"x") +ₗ #1 <-{2} !"y";;                 (* ( **x).1 = y *)
      ReBor;; ReBor;; ReBor;;                   (* fold back *)
      (#☠;; delete [ #1; "x"]);;                 (* drop x, resolving it *)
      delete [ #2; "y"];;
      return: ["c"].

  Definition swap_snd_spec :
      fn_spec [uniq_borₛ (uniq_borₛ (Zₛ * (Zₛ * Zₛ))); (Zₛ * Zₛ)%ST] (Zₛ * Zₛ) () :=
    λ _ post '-[(_, m); (_, y)], λ mask π,
      let b := uniq_bor_current (𝔄:=uniq_borₛ (Zₛ * (Zₛ * Zₛ))) m in
      uniq_bor_future (𝔄:=uniq_borₛ (Zₛ * (Zₛ * Zₛ))) m π =
        (((uniq_bor_current (𝔄:=Zₛ * (Zₛ * Zₛ)) b).1, y),
          uniq_bor_future (𝔄:=Zₛ * (Zₛ * Zₛ)) b π) →
      ∀ (lr: loc), post (lr, (uniq_bor_current (𝔄:=Zₛ * (Zₛ * Zₛ)) b).2) mask π.

  Lemma swap_snd_type :
    typed_val swap_snd
      ((fn<(α, β)>(∅; &uniq{α} (&uniq{β} (int * (int * int))), int * int) → int * int)
        swap_snd_spec)
      (swap_snd, ()).
  Proof.
    unfold swap_snd. unlock.
    opose proof (@type_fn _ _ _ [uniq_borₛ (uniq_borₛ (Zₛ * (Zₛ * Zₛ))); (Zₛ * Zₛ)%ST]
      (Zₛ * Zₛ) () ()
      (λ '(α, β), FP ∅ +[&uniq{α} (&uniq{β} (int * (int * int))); (int * int)%T]%T
        (int * int)%T AtomicClosed)
      swap_snd_spec _ [BNamed "x"; BNamed "y"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros [α β] ϝ k wl. destruct wl as [vx [vy []]]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_r +[_] +[_]). apply tctx_own_to_oplace. }
      (* unfold *x, **x, **x as a pair *)
      iApply type_seq.
      { apply (type_unfold_oplace_uniq_instr _ _ _ vx 1 PHole (&uniq{β} (int * (int * int))) α).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_unfold_oplace_uniq_instr _ _ _ vx 1 (PUniq α PHole) (int * (int * int)) β).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_unfold_oplace_prod_instr _ _ _ vx 1 (PUniq α (PUniq β PHole)) int (int * int)).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply (type_new 2). { lia. } iIntros (vc). simpl_subst.
      (* c = ( **x).1 *)
      iApply type_seq.
      { apply (type_memcpy_copy_from_oplace_deep_instr _ _ _ vc vx 1
          (PUniq α (PUniq β (PSnd (OfTy int) PHole))) (int * int)
          (own_ptr 2 (↯ 2)) (own_ptr 2 (int * int)) (↯ 2));
          [apply _|by apply write_own| |done|solve_typing].
        apply (resolve'_just _ _ _ (const True)). apply resolve_just. }
      { solve_typing. } { reflexivity. }
      (* ( **x).1 = y *)
      iApply type_seq.
      { apply (type_memcpy_oplace_deep_instr _ _ _ vx vy 1
          (PUniq α (PUniq β (PSnd (OfTy int) PHole))) (int * int)
          (own_ptr 2 (int * int)) (own_ptr 2 (↯ (ty_size (int * int)))));
          [apply resolve_just|apply (read_own_move (int * int))|done|solve_typing]. }
      { solve_typing. } { reflexivity. }
      (* fold back *)
      iApply type_seq.
      { apply (type_fold_oplace_prod_instr _ _ _ vx 1 (PUniq α (PUniq β PHole)) int (int * int)).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_fold_oplace_uniq_instr _ _ _ vx 1 (PUniq α PHole) (int * (int * int)) β).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_fold_oplace_uniq_instr _ _ _ vx 1 PHole (&uniq{β} (int * (int * int))) α).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      (* drop x, resolving it *)
      iApply type_seq.
      { apply (type_drop_oplace_deep_instr _ _ _ vx 1 1
          (OfTy (&uniq{α} (&uniq{β} (int * (int * int)))))); [done|done|done|].
        apply lty_rslv_of, lty_resolve_ofty, uniq_bor.uniq_resolve. solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_delete. { solve_typing. } { done. } { done. }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lx m] [[ly [y1 y2]] []]] mask π. simpl.
    destruct m as [[[[[l [[[[[l' [x1 x2]] ξb] db] gb] idxb]] ξa] da] ga] idxa].
    simpl. intros Hspec. rewrite /trans_upper /trans_tail /=.
    intros l0 junk zw -> _ zr _ d g idx d0 g0 idx0 Hres. apply Hspec.
    rewrite !uniq_bor_future_eq /=.
    rewrite (uniq_prvar_app_irrel (𝔄:=uniq_borₛ (Zₛ * (Zₛ * Zₛ))) _
      (l', (x1, (y1, y2)), ξb, d, g, idx) ξa π).
    etrans; [exact Hres|]. f_equal.
    exact (uniq_prvar_app_irrel (𝔄:=Zₛ * (Zₛ * Zₛ)) (x1, (y1, y2)) (x1, x2) ξb π).
  Qed.
  (*
  Copying a pair out through two shared references:

  ```
  fn get_pair<'a, 'b>(x: &'a &'b (i32, i32)) -> (i32, i32) { **x }
  ```

  with the specification `ensures result == **x`. The argument slot is an owned place;
  `*x` is unfolded and the view of its referent changed to [ShrLty (OfTy (int * int)) 'b];
  `**x` (two cells) is copied out ([type_memcpy_copy_from_oplace_pshr_instr], [K = PHole],
  [K2 = PShr 'b PHole]: two loads of shared references); `x` is dropped.
  *)

  Definition get_pair : val :=
    fn: ["x"] :=
      ReBor;;                                       (* unfold *x *)
      ReBor;;                                       (* view **x *)
      let: "r" := new [ #2] in
      (Skip;; "r" <-{2} !(!(!"x")));;               (* r = **x *)
      (#☠;; delete [ #1; "x"]);;                     (* drop x *)
      return: ["r"].

  Definition get_pair_spec :
      fn_spec [at_clocₛ (at_clocₛ (Zₛ * Zₛ))] (Zₛ * Zₛ) () :=
    λ _ post '-[(_, m)], λ mask π, ∀ (lr: loc), post (lr, m.2.2) mask π.

  Lemma get_pair_type :
    typed_val get_pair
      ((fn<(α, β)>(∅; &shr{α} (&shr{β} (int * int))) → int * int) get_pair_spec)
      (get_pair, ()).
  Proof.
    unfold get_pair. unlock.
    opose proof (@type_fn _ _ _ [at_clocₛ (at_clocₛ (Zₛ * Zₛ))] (Zₛ * Zₛ) () ()
      (λ '(α, β), FP ∅ +[&shr{α} (&shr{β} (int * int))]%T (int * int)%T AtomicClosed)
      get_pair_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros [α β] ϝ k wl. destruct wl as [vx []]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply typed_body_tctx_incl; [apply tctx_own_to_oplace|].
      (* unfold *x *)
      iApply type_seq.
      { apply (type_unfold_oplace_shr_instr _ _ _ vx 1 PHole α (&shr{β} (int * int))).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      (* view **x *)
      iApply type_seq.
      { apply (type_change_oplace_shr_instr _ _ _ vx 1 PHole α PHole
          (OfTy (&shr{β} (int * int))) (ShrLty (OfTy (int * int)) β));
          [solve_typing|done|done|done]. }
      { solve_typing. } { reflexivity. }
      iApply (type_new 2). { lia. } iIntros (vr). simpl_subst.
      (* r = **x *)
      iApply type_seq.
      { apply (type_memcpy_copy_from_oplace_pshr_instr _ _ _ vr vx 1 PHole α
          (PShr β PHole) (OfTy (int * int)) (own_ptr 2 (↯ 2)) (own_ptr 2 (int * int)) (↯ 2));
          [apply _|by apply write_own| |done|solve_typing|solve_typing].
        apply (resolve'_just _ _ _ (const True)). apply resolve_just. }
      { solve_typing. } { reflexivity. }
      (* drop x *)
      iApply type_seq.
      { apply (type_drop_oplace_deep_instr _ _ _ vx 1 1
          (ShrLty (ShrLty (OfTy (int * int)) β) α)); [done|done|done|].
        apply lty_rslv_shr. }
      { solve_typing. } { reflexivity. }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lx [l1 [l2 [z1 z2]]]] []] mask π. simpl.
    intros Hspec. rewrite /trans_upper /trans_tail /=.
    intros l0 junk zw -> _. apply Hspec.
  Qed.
  Notation opt_pair := (Σ! +[(); int * int])%T.
  Notation opt_pairₛ := (Σ! [unitₛ; (Zₛ * Zₛ)%ST])%ST.

  (*
  Case analysis on an option behind two levels of mutable references, and a mutable
  borrow of a field of its payload:

  ```
  fn set_some_first<'a, 'b>(x: &'a mut &'b mut Option<(i32, i32)>) {
      if let Some(p) = &mut **x { p.0 = 1 }
  }
  ```

  with the specification `ensures fin(x) == (match **old(x) { None => None,
  Some(a) => Some((1, a.1)) }, fin( *old(x)))`. The argument slot is an owned place; `*x`
  and `**x` are unfolded; the case analysis on `**x` (the whole referent of the inner
  borrow, in [Uniq] mode) gives the sum place at the variant ([type_case_oplace_deep]). In
  the branch of `Some`, the payload (context step [PSum] below two [PUniq] steps) is
  unfolded as a pair, its field `.0` is reborrowed at a fresh lifetime
  ([type_borrow_oplace_deep_instr]), written through the new reference, and unblocked when
  the lifetime ends ([unblock_tctx_oplace_deep]); in both branches the place is folded back
  ([type_fold_oplace_sum_deep_instr]) and dropped.
  *)

  Definition set_some_first : val :=
    fn: ["x"] :=
      ReBor;; ReBor;;                               (* unfold *x, **x *)
      case: !(!(!"x")) of
      [ ReBor;; ReBor;; ReBor;;                     (* None: fold back *)
        (#☠;; delete [ #1; "x"]);;                   (* drop x *)
        let: "ret" := new [ #0] in
        return: ["ret"];
        ReBor;;                                     (* Some: the payload as a pair *)
        Newlft;;
        let: "r" := ReBor;; !(!"x") +ₗ #1 in        (* r = &mut p.0 *)
        let: "one" := #1 in
        "r" <- "one";;
        Skip;;                                      (* resolve r *)
        Endlft;;                                    (* unblock p.0 *)
        ReBor;; ReBor;; ReBor;; ReBor;;             (* fold back *)
        (#☠;; delete [ #1; "x"]);;                   (* drop x *)
        let: "ret" := new [ #0] in
        return: ["ret"]].

  Definition set_some_first_spec : fn_spec [uniq_borₛ (uniq_borₛ opt_pairₛ)] () () :=
    λ _ post '-[(_, m)], λ mask π,
      let b := uniq_bor_current (𝔄:=uniq_borₛ opt_pairₛ) m in
      let c := uniq_bor_current (𝔄:=opt_pairₛ) b in
      (∀ pad, c = (pinj (Xl:=[unitₛ; (Zₛ * Zₛ)%ST]) 0%fin (), pad) →
        uniq_bor_future (𝔄:=uniq_borₛ opt_pairₛ) m π = (c, uniq_bor_future (𝔄:=opt_pairₛ) b π) →
        ∀ ret, post ret mask π) ∧
      (∀ (a: Z * Z) pad, c = (pinj (Xl:=[unitₛ; (Zₛ * Zₛ)%ST]) 1%fin a, pad) →
        uniq_bor_future (𝔄:=uniq_borₛ opt_pairₛ) m π =
          ((pinj (Xl:=[unitₛ; (Zₛ * Zₛ)%ST]) 1%fin (1%Z, a.2), pad),
            uniq_bor_future (𝔄:=opt_pairₛ) b π) →
        ∀ ret, post ret mask π).

  Lemma set_some_first_type :
    typed_val set_some_first
      ((fn<(α, β)>(∅; &uniq{α} (&uniq{β} opt_pair)) → ()) set_some_first_spec)
      (set_some_first, ()).
  Proof.
    unfold set_some_first. unlock.
    opose proof (@type_fn _ _ _ [uniq_borₛ (uniq_borₛ opt_pairₛ)] () () ()
      (λ '(α, β), FP ∅ +[&uniq{α} (&uniq{β} opt_pair)]%T ()%T AtomicClosed)
      set_some_first_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros [α β] ϝ k wl. destruct wl as [vx []]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply typed_body_tctx_incl; [apply tctx_own_to_oplace|].
      (* unfold *x, **x *)
      iApply type_seq.
      { apply (type_unfold_oplace_uniq_instr _ _ _ vx 1 PHole (&uniq{β} opt_pair) α).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_unfold_oplace_uniq_instr _ _ _ vx 1 (PUniq α PHole) opt_pair β).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      (* match **x *)
      iApply (type_case_oplace_deep _ _ _ _ vx 1 (PUniq α (PUniq β PHole)) +[(); int * int]%T
        _ _ _ -[_; _]); [solve_typing|].
      iSplitL; [|iSplitL; [|done]].
      - (* None: fold back, drop x *)
        simpl.
        iApply type_seq.
        { apply (type_fold_oplace_sum_deep_instr _ _ _ vx 1 (PUniq α (PUniq β PHole))
            +[(); int * int]%T 0%fin). solve_typing. }
        { solve_typing. } { reflexivity. }
        iApply type_seq.
        { apply (type_fold_oplace_uniq_instr _ _ _ vx 1 (PUniq α PHole) opt_pair β).
          solve_typing. }
        { solve_typing. } { reflexivity. }
        iApply type_seq.
        { apply (type_fold_oplace_uniq_instr _ _ _ vx 1 PHole (&uniq{β} opt_pair) α).
          solve_typing. }
        { solve_typing. } { reflexivity. }
        iApply type_seq.
        { apply (type_drop_oplace_deep_instr _ _ _ vx 1 1 (OfTy (&uniq{α} (&uniq{β} opt_pair))));
            [done|done|done|].
          apply lty_rslv_of, lty_resolve_ofty, uniq_bor.uniq_resolve. solve_typing. }
        { solve_typing. } { reflexivity. }
        iApply (type_new_subtype () 0). { lia. } { apply uninit_unit_1. }
        iIntros (vret). simpl_subst.
        iApply type_jump.
        { rewrite elem_of_list_singleton. reflexivity. }
        { solve_typing. }
        { solve_typing. }
        { reflexivity. }
      - (* Some(p): p.0 = 1 through a reborrow *)
        simpl.
        iApply type_seq.
        { apply (type_unfold_oplace_prod_instr _ _ _ vx 1
            (PUniq α (PUniq β (PSum +[(); int * int]%T 1%fin (0%Z, 0%Z) PHole))) int int).
          solve_typing. }
        { solve_typing. } { reflexivity. }
        iApply (type_newlft []). iIntros (γ).
        iApply (type_let with "[]").
        { apply (type_borrow_oplace_deep_instr _ _ _ vx 1 γ
            (PUniq α (PUniq β (PSum +[(); int * int]%T 1%fin (0%Z, 0%Z) (PFst PHole (OfTy int)))))
            int); [done|solve_typing|solve_typing]. }
        { solve_typing. } { reflexivity. }
        iIntros (vr). simpl_subst.
        iApply type_int. iIntros (v1). simpl_subst.
        iApply type_assign. { solve_typing. } { apply write_uniq. solve_typing. }
        { apply (resolve'_just _ _ _ (const True)). apply resolve_just. }
        iApply type_resolve. { solve_typing. } { apply uniq_bor.uniq_resolve. solve_typing. }
        iApply (type_endlft _ _ _ _ γ).
        { solve_typing. }
        { apply unblock_tctx_cons_just_hasty.
          apply (unblock_tctx_oplace_deep _ _ _
            (PUniq α (PUniq β (PSum +[(); int * int]%T 1%fin (0%Z, 0%Z) (PFst PHole (OfTy int)))))
            int); [done|solve_typing|].
          apply unblock_tctx_nil. }
        (* fold back *)
        iApply type_seq.
        { apply (type_fold_oplace_prod_instr _ _ _ vx 1
            (PUniq α (PUniq β (PSum +[(); int * int]%T 1%fin (0%Z, 0%Z) PHole))) int int).
          solve_typing. }
        { solve_typing. } { reflexivity. }
        iApply type_seq.
        { apply (type_fold_oplace_sum_deep_instr _ _ _ vx 1 (PUniq α (PUniq β PHole))
            +[(); int * int]%T 1%fin). solve_typing. }
        { solve_typing. } { reflexivity. }
        iApply type_seq.
        { apply (type_fold_oplace_uniq_instr _ _ _ vx 1 (PUniq α PHole) opt_pair β).
          solve_typing. }
        { solve_typing. } { reflexivity. }
        iApply type_seq.
        { apply (type_fold_oplace_uniq_instr _ _ _ vx 1 PHole (&uniq{β} opt_pair) α).
          solve_typing. }
        { solve_typing. } { reflexivity. }
        iApply type_seq.
        { apply (type_drop_oplace_deep_instr _ _ _ vx 1 1 (OfTy (&uniq{α} (&uniq{β} opt_pair))));
            [done|done|done|].
          apply lty_rslv_of, lty_resolve_ofty, uniq_bor.uniq_resolve. solve_typing. }
        { solve_typing. } { reflexivity. }
        iApply (type_new_subtype () 0). { lia. } { apply uninit_unit_1. }
        iIntros (vret). simpl_subst.
        iApply type_jump.
        { rewrite elem_of_list_singleton. reflexivity. }
        { solve_typing. }
        { solve_typing. }
        { reflexivity. }
    }
    intros post [[lx m] []] mask π. simpl.
    destruct m as [[[[[l [[[[[l' [s pad]] ξb] db] gb] idxb]] ξa] da] ga] idxa]. simpl.
    intros [HNone HSome]. rewrite /trans_upper /trans_tail /=.
    destruct s as [[]|[a|[]]]; simpl.
    - intros d g idx d0 g0 idx0 Hres l0 junk. eapply HNone; [done|].
      rewrite !uniq_bor_future_eq /=.
      rewrite (uniq_prvar_app_irrel (𝔄:=uniq_borₛ opt_pairₛ) _
        (l', (inl (), pad), ξb, d, g, idx) ξa π).
      etrans; [exact Hres|]. f_equal.
    - intros [[[[[lr zr] ξr] dr] gr] idxr] Hc1 [[[[[lz zz] ξz] dz] gz] idxz] (_ & -> & ->) Hres.
      intros [? [[[lx' m'] ζm'] []]] (_ & Hlx & Hm' & _ & Hfin & _).
      intros d g idx d0 g0 idx0 Hres' l0 junk.
      destruct m' as [[[[[l2 [[[[[l2' [s2 pad2]] ξb2] db2] gb2] idxb2]] ξa2] da2] ga2] idxa2].
      simpl in *.
      injection Hm' as -> -> Hs2 -> -> -> -> -> -> -> -> ->.
      destruct a as [a1 a2]. destruct s2 as [[]|[[b1 b2]|[]]]; [done|]. simpl in *.
      injection Hs2 as <-.
      rewrite /oplace_blk_fin /= in Hfin.
      have Hb1: b1 = 1%Z. { rewrite Hfin (uniq_prvar_app_irrel (𝔄:=Zₛ) a1 1%Z). exact Hres. }
      subst b1. eapply HSome; [done|].
      rewrite !uniq_bor_future_eq /=.
      rewrite (uniq_prvar_app_irrel (𝔄:=uniq_borₛ opt_pairₛ) _
        (l', (inr (inl (1%Z, b2)), pad), ξb, d, g, idx) ξa π).
      rewrite Hb1 in Hres'.
      etrans; [exact Hres'|]. f_equal.
      exact (uniq_prvar_app_irrel (𝔄:=opt_pairₛ) (inr (inl (1%Z, b2)), pad) (inr (inl (a1, b2)), pad) ξb π).
    Unshelve. all: eapply (composeₛ empty_prod_to_unitₛ uninit0_to_unitₛ).
  Qed.
  (*
  Assigning variants through two levels of mutable references:

  ```
  fn reset<'a, 'b>(x: &'a mut &'b mut Option<(i32, i32)>, y: (i32, i32)) {
      **x = None;
      **x = Some(y);   // the payload has two cells
  }
  ```

  with the specification `ensures fin(x) == (Some(y), fin( *old(x)))` (up to the padding).
  `**x` is the whole referent of the inner borrow ([Uniq] mode); it gets the unit variant
  ([type_sum_unit_oplace_deep_instr], only the tag is written), then the variant `Some`
  with a payload of two cells copied from `y` ([type_sum_memcpy_oplace_deep_instr]).
  *)

  Definition reset : val :=
    fn: ["x"; "y"] :=
      ReBor;; ReBor;;                               (* unfold *x, **x *)
      (!(!"x") <-{Σ 0} ());;                        (* **x = None *)
      (!(!"x") <-{2,Σ 1} !"y");;                    (* **x = Some(y) *)
      ReBor;; ReBor;;                               (* fold back *)
      (#☠;; delete [ #1; "x"]);;                     (* drop x, resolving it *)
      delete [ #2; "y"];;
      let: "ret" := new [ #0] in
      return: ["ret"].

  Definition reset_spec :
      fn_spec [uniq_borₛ (uniq_borₛ opt_pairₛ); (Zₛ * Zₛ)%ST] () () :=
    λ _ post '-[(_, m); (_, y)], λ mask π,
      let b := uniq_bor_current (𝔄:=uniq_borₛ opt_pairₛ) m in
      ∀ pad, uniq_bor_future (𝔄:=uniq_borₛ opt_pairₛ) m π =
        ((pinj (Xl:=[unitₛ; (Zₛ * Zₛ)%ST]) 1%fin y, pad), uniq_bor_future (𝔄:=opt_pairₛ) b π) →
      ∀ ret, post ret mask π.

  Lemma reset_type :
    typed_val reset
      ((fn<(α, β)>(∅; &uniq{α} (&uniq{β} opt_pair), int * int) → ()) reset_spec)
      (reset, ()).
  Proof.
    unfold reset. unlock.
    opose proof (@type_fn _ _ _ [uniq_borₛ (uniq_borₛ opt_pairₛ); (Zₛ * Zₛ)%ST] () () ()
      (λ '(α, β), FP ∅ +[&uniq{α} (&uniq{β} opt_pair); (int * int)%T]%T ()%T AtomicClosed)
      reset_spec _ [BNamed "x"; BNamed "y"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros [α β] ϝ k wl. destruct wl as [vx [vy []]]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_r +[_] +[_]). apply tctx_own_to_oplace. }
      (* unfold *x, **x *)
      iApply type_seq.
      { apply (type_unfold_oplace_uniq_instr _ _ _ vx 1 PHole (&uniq{β} opt_pair) α).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_unfold_oplace_uniq_instr _ _ _ vx 1 (PUniq α PHole) opt_pair β).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      (* **x = None *)
      iApply type_seq.
      { apply (type_sum_unit_oplace_deep_instr _ _ _ vx 1 (PUniq α (PUniq β PHole))
          +[(); int * int]%T 0%fin idₛ (const (const True)));
          [apply subtype_refl|apply resolve_just|solve_typing]. }
      { solve_typing. } { reflexivity. }
      (* **x = Some(y) *)
      iApply type_seq.
      { apply (type_sum_memcpy_oplace_deep_instr _ _ _ vx vy 1 (PUniq α (PUniq β PHole))
          +[(); int * int]%T 1%fin (own_ptr 2 (int * int)) (own_ptr 2 (↯ (ty_size (int * int)))));
          [apply resolve_just|apply (read_own_move (int * int))|done|solve_typing]. }
      { solve_typing. } { reflexivity. }
      (* fold back, drop x *)
      iApply type_seq.
      { apply (type_fold_oplace_uniq_instr _ _ _ vx 1 (PUniq α PHole) opt_pair β).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_fold_oplace_uniq_instr _ _ _ vx 1 PHole (&uniq{β} opt_pair) α).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_drop_oplace_deep_instr _ _ _ vx 1 1 (OfTy (&uniq{α} (&uniq{β} opt_pair))));
          [done|done|done|].
        apply lty_rslv_of, lty_resolve_ofty, uniq_bor.uniq_resolve. solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_delete. { solve_typing. } { done. } { done. }
      iApply (type_new_subtype () 0). { lia. } { apply uninit_unit_1. }
      iIntros (vret). simpl_subst.
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lx m] [[ly [y1 y2]] []]] mask π. simpl.
    destruct m as [[[[[l [[[[[l' [s pad]] ξb] db] gb] idxb]] ξa] da] ga] idxa]. simpl.
    intros Hspec. rewrite /trans_upper /trans_tail /=.
    intros _ pad1 _ pad0 zr _ d g idx d0 g0 idx0 Hres l0 junk. apply (Hspec pad0).
    rewrite !uniq_bor_future_eq /=.
    rewrite (uniq_prvar_app_irrel (𝔄:=uniq_borₛ opt_pairₛ) _
      (l', (inr (inl (y1, y2)), pad0), ξb, d, g, idx) ξa π).
    etrans; [exact Hres|]. f_equal.
    exact (uniq_prvar_app_irrel (𝔄:=opt_pairₛ) (inr (inl (y1, y2)), pad0) (s, pad) ξb π).
    Unshelve. all: eapply (composeₛ empty_prod_to_unitₛ uninit0_to_unitₛ).
  Qed.
End place_deep.

Print Assumptions swap_snd_type.
Print Assumptions get_pair_type.
Print Assumptions set_some_first_type.
Print Assumptions reset_type.
