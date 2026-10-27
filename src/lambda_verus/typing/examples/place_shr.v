From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type function product programs own cont uninit int
  uniq_bor shr_bor borrow place place_own place_shr.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

Section place_shr.
  Context `{!typeG Σ}.

  (*
  A shared borrow of a field of a unique borrow, read while the field is shared, then
  a write once the shared borrow has ended:

  ```
  fn share_first<'a>(x: &'a mut (i32, i32)) -> i32 {
      let v;
      { let r = &x.0;      // shared borrow of x.0
        v = *r;            // read through r
        let _ = x.0;       // read x.0 while it is shared
        let _ = x.1; }     // read x.1; the shared borrow ends here
      x.0 = 5;
      v
  }
  ```

  with the specification `ensures result == old(x).0, fin(x) == (5, old(x).1)`. The
  referent of `x` is unfolded; field 0 is borrowed shared at `'a ⊓ 'b`
  ([type_share_place_instr]), which leaves it shared-blocked; it is read through the
  shared reference ([read_shr]) and directly ([type_read_place_shr_instr]); field 1 is
  read directly ([type_read_place_instr]). Once `'b` has ended, field 0 is unblocked
  ([unblock_tctx_place_shr]), with the same value, and written
  ([type_write_place_instr]).
  *)

  Definition share_first : val :=
    fn: ["x"] :=
      let: "b" := !"x" in
      delete [ #1; "x"];;
      Newlft;;
      let: "r" := Share;; "b" in          (* &( *b).0 *)
      let: "v" := !"r" in                 (* *r *)
      let: "v0" := !("b" +ₗ #0) in        (* ( *b).0, shared *)
      let: "v1" := !("b" +ₗ #1) in        (* ( *b).1 *)
      Endlft;;                            (* unblock ( *b).0 *)
      let: "five" := #5 in
      "b" +ₗ #0 <- "five";;               (* ( *b).0 = 5 *)
      Skip;;                              (* resolve b *)
      let: "ret" := new [ #1] in
      "ret" <- "v";;
      return: ["ret"].

  Definition share_first_spec : fn_spec [uniq_borₛ (Zₛ * Zₛ)] Zₛ () :=
    λ _ post '-[(_, m)], λ mask π,
      uniq_bor_future (𝔄:=Zₛ * Zₛ) m π = (5%Z, (uniq_bor_current (𝔄:=Zₛ * Zₛ) m).2) →
      ∀ (lr: loc), post (lr, (uniq_bor_current (𝔄:=Zₛ * Zₛ) m).1) mask π.

  Lemma share_first_type :
    typed_val share_first
      ((fn<α>(∅; &uniq{α} (int * int)) → int) share_first_spec)
      (share_first, ()).
  Proof.
    unfold share_first. unlock.
    opose proof (@type_fn _ _ _ [uniq_borₛ (Zₛ * Zₛ)] Zₛ () ()
      (λ α, FP ∅ +[&uniq{α} (int * int)]%T int%T AtomicClosed)
      share_first_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros α ϝ k wl. destruct wl as [vx []]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply (type_let with "[]").
      { eapply (type_deref_instr (own_ptr 1 (&uniq{α} (int * int)))
          (&uniq{α} (int * int))).
        - apply uniq_stack_okay.
        - done.
        - apply (read_own_move (&uniq{α} (int * int))). }
      { apply tctx_extract_elt_here_exact. }
      { reflexivity. }
      iIntros (vb). simpl_subst.
      iApply type_delete. { solve_typing. } { done. } { done. }
      iApply typed_body_tctx_incl.
      { apply (tctx_unfold_uniq_prod _ _ vb α int int). solve_typing. }
      iApply (type_newlft []). iIntros (β).
      (* &( *b).0, at α ⊓ β *)
      iApply (type_let with "[]").
      { apply (type_share_place_instr _ _ _ vb α β (PFst PHole (OfTy int)) int);
          [solve_typing|done]. }
      { solve_typing. } { reflexivity. }
      iIntros (vr). simpl_subst.
      (* *r *)
      iApply (type_let with "[]").
      { eapply (type_deref_instr (𝔅 := Zₛ) _ int); [apply int_stack_okay|done|].
        apply (read_shr int (α ⊓ β)); [apply int_copy|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iIntros (vv). simpl_subst.
      (* ( *b).0, while it is shared *)
      iApply (type_let with "[]").
      { apply (type_read_place_shr_instr _ _ _ vb α (α ⊓ β) (PFst PHole (OfTy int)) int);
          [solve_typing|solve_typing|done|done|done|apply _]. }
      { solve_typing. } { reflexivity. }
      iIntros (v0). simpl_subst.
      (* ( *b).1 *)
      iApply (type_let with "[]").
      { apply (type_read_place_instr _ _ _ vb α (PSnd (ShrBlocked int (α ⊓ β)) PHole) int);
          [solve_typing|done|done|done|apply _]. }
      { solve_typing. } { simpl. reflexivity. }
      iIntros (v1). simpl_subst.
      (* end β: unblock ( *b).0 *)
      iApply (type_endlft _ _ _ _ β).
      { solve_typing. }
      { apply unblock_tctx_cons_just_hasty.
        apply (unblock_tctx_place_shr _ _ _ (PFst PHole (OfTy int)) int); [solve_typing|done|].
        repeat apply unblock_tctx_cons_just_hasty. apply unblock_tctx_nil. }
      (* ( *b).0 = 5 *)
      iApply type_int. iIntros (v5). simpl_subst.
      iApply type_seq.
      { apply (type_write_place_instr _ _ _ vb v5 α (PFst PHole (OfTy int)) int
          (const (const True))); [solve_typing|done|done|done|apply resolve_just]. }
      { solve_typing. } { reflexivity. }
      (* fold back, and resolve b *)
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_r +[_] +[_]). apply (tctx_fold_uniq_prod _ _ vb α int int).
        solve_typing. }
      iApply type_resolve. { solve_typing. } { apply uniq_bor.uniq_resolve. solve_typing. }
      iApply (type_letalloc_1 int). { solve_typing. } 2: { done. }
      { eapply (_: ∀ x, x ≡ x). } iIntros (vret). simpl_subst.
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lx m] []] mask π. simpl.
    destruct m as [[[[[l [x1 x2]] ξi] d] g] idx]. simpl.
    intros Hspec. rewrite /trans_upper /trans_tail /=.
    intros z _ z0 _ [y0 [xp [y1 [y2 [w1 [w2 []]]]]]] (_ & -> & _ & <- & _).
    intros _ x' Hl' Hcur Hfut _.
    destruct x' as [[[[[[l' [y1' y2']] ξi'] d'] g'] idx'] ζm']. simpl.
    intros _ Hres l1. apply Hspec.
    rewrite /place_bor /= in Hfut Hcur. rewrite -Hfut uniq_bor_future_eq.
    rewrite (_: (π (uniq_prvar (𝔄:=Zₛ * Zₛ) (y1', y2') ξi')).1 = (y1', y2')); [|exact Hres].
    by injection Hcur as -> ->.
    Unshelve. by intros ?.
  Qed.

  (*
  Reading below an owned pointer below a shared reference:

  ```
  fn get_box_shr<'a, 'b>(r: &'a (Box<i32>, &'b mut i32)) -> i32 { *( *r).0 }
  ```

  with the specification `ensures result == *r.0`. A shared reference to the field is
  taken by [tctx_shr_place], the owned pointer is dereferenced through its (structural)
  sharing predicate ([type_deref_shr_own_instr]), and the integer is read ([read_shr]).
  (A unique borrow below a shared reference is dereferenced the same way, with
  [type_deref_shr_uniq_instr]: see [get_uniq_shr] below.)
  *)

  Definition get_box_shr : val :=
    fn: ["x"] :=
      let: "r" := !"x" in
      delete [ #1; "x"];;
      let: "p0" := !("r" +ₗ #0) in       (* &*( *r).0 *)
      let: "v0" := !"p0" in               (* *( *r).0 *)
      let: "ret" := new [ #1] in
      "ret" <- "v0";;
      return: ["ret"].

  Definition get_box_shr_spec :
      fn_spec [at_clocₛ (at_locₛ Zₛ * uniq_borₛ Zₛ)] Zₛ () :=
    λ _ post '-[(_, (_, ((_, a), _)))], λ mask π, ∀ (lr: loc), post (lr, a) mask π.

  Lemma get_box_shr_type :
    typed_val get_box_shr
      ((fn<(α, β)>(∅; &shr{α} (box int * &uniq{β} int)) → int) get_box_shr_spec)
      (get_box_shr, ()).
  Proof.
    unfold get_box_shr. unlock.
    opose proof (@type_fn _ _ _ [at_clocₛ (at_locₛ Zₛ * uniq_borₛ Zₛ)] Zₛ () ()
      (λ '(α, β), FP ∅ +[&shr{α} (box int * &uniq{β} int)]%T int%T AtomicClosed)
      get_box_shr_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros [α β] ϝ k wl. destruct wl as [vx []]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply (type_let with "[]").
      { eapply (type_deref_instr (own_ptr 1 (&shr{α} (box int * &uniq{β} int)))
          (&shr{α} (box int * &uniq{β} int))).
        - apply shr_stack_okay.
        - done.
        - apply (read_own_move (&shr{α} (box int * &uniq{β} int))). }
      { apply tctx_extract_elt_here_exact. }
      { reflexivity. }
      iIntros (vr). simpl_subst.
      iApply type_delete. { solve_typing. } { done. } { done. }
      (* &( *r).0, then through the box *)
      iApply typed_body_tctx_incl.
      { apply (tctx_shr_place _ _ vr α (PFst PHole (OfTy (&uniq{β} int))) (box int)). done. }
      iApply (type_let with "[]").
      { apply (type_deref_shr_own_instr α _ 1 int). solve_typing. }
      { solve_typing. } { reflexivity. }
      iIntros (vp0). simpl_subst.
      iApply (type_let with "[]").
      { eapply (type_deref_instr (𝔅 := Zₛ) _ int); [apply int_stack_okay|done|].
        apply (read_shr int α); [apply int_copy|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iIntros (vv0). simpl_subst.
      iApply (type_letalloc_1 int). { solve_typing. } 2: { done. }
      { eapply (_: ∀ x, x ≡ x). } iIntros (vret). simpl_subst.
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lx [l [[l0 a] m]]] []] mask π. simpl.
    intros Hspec. rewrite /trans_upper /trans_tail /=.
    intros z _ l2' _ z0 _ l2. apply Hspec.
    Unshelve. by intros ?.
  Qed.

  (*
  Reading below a unique borrow below a shared reference:

  ```
  fn get_uniq_shr<'a, 'b>(r: &'a (Box<i32>, &'b mut i32)) -> i32 { *( *r).1 }
  ```

  with the specification `ensures result == *r.1` (the current value of the unique
  borrow). A shared reference to the field is taken by [tctx_shr_place], the unique
  borrow is dereferenced through its sharing predicate ([type_deref_shr_uniq_instr], at
  [α ⊑ β] from the signature), and the integer is read ([read_shr]).
  *)

  Definition get_uniq_shr : val :=
    fn: ["x"] :=
      let: "r" := !"x" in
      delete [ #1; "x"];;
      let: "p1" := !("r" +ₗ #1) in       (* &*( *r).1 *)
      let: "v1" := !"p1" in               (* *( *r).1 *)
      let: "ret" := new [ #1] in
      "ret" <- "v1";;
      return: ["ret"].

  Definition get_uniq_shr_spec :
      fn_spec [at_clocₛ (at_locₛ Zₛ * uniq_borₛ Zₛ)] Zₛ () :=
    λ _ post '-[(_, (_, (_, m)))], λ mask π, ∀ (lr: loc),
      post (lr, uniq_bor_current (𝔄:=Zₛ) m) mask π.

  Lemma get_uniq_shr_type :
    typed_val get_uniq_shr
      ((fn<(α, β)>(∅; &shr{α} (box int * &uniq{β} int)) → int) get_uniq_shr_spec)
      (get_uniq_shr, ()).
  Proof.
    unfold get_uniq_shr. unlock.
    opose proof (@type_fn _ _ _ [at_clocₛ (at_locₛ Zₛ * uniq_borₛ Zₛ)] Zₛ () ()
      (λ '(α, β), FP ∅ +[&shr{α} (box int * &uniq{β} int)]%T int%T AtomicClosed)
      get_uniq_shr_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros [α β] ϝ k wl. destruct wl as [vx []]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply (type_let with "[]").
      { eapply (type_deref_instr (own_ptr 1 (&shr{α} (box int * &uniq{β} int)))
          (&shr{α} (box int * &uniq{β} int))).
        - apply shr_stack_okay.
        - done.
        - apply (read_own_move (&shr{α} (box int * &uniq{β} int))). }
      { apply tctx_extract_elt_here_exact. }
      { reflexivity. }
      iIntros (vr). simpl_subst.
      iApply type_delete. { solve_typing. } { done. } { done. }
      iApply typed_body_tctx_incl.
      { apply (tctx_shr_place _ _ vr α (PSnd (OfTy (box int)) PHole) (&uniq{β} int)). done. }
      iApply (type_let with "[]").
      { apply (type_deref_shr_uniq_instr α β _ int); solve_typing. }
      { solve_typing. } { reflexivity. }
      iIntros (vp1). simpl_subst.
      iApply (type_let with "[]").
      { eapply (type_deref_instr (𝔅 := Zₛ) _ int); [apply int_stack_okay|done|].
        apply (read_shr int α); [apply int_copy|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iIntros (vv1). simpl_subst.
      iApply (type_letalloc_1 int). { solve_typing. } 2: { done. }
      { eapply (_: ∀ x, x ≡ x). } iIntros (vret). simpl_subst.
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lx [l [[l0 a] m]]] []] mask π. simpl.
    intros Hspec. rewrite /trans_upper /trans_tail /=.
    intros z _ z0 _ z1. apply Hspec.
    Unshelve. by intros ?.
  Qed.

  (*
  A shared borrow of a field of a local pair:

  ```
  fn share_local(mut x: (i32, i32)) -> i32 {
      let v;
      { let r = &x.0;      // shared borrow of x.0
        v = *r;            // read through r
        let _ = x.0; }     // read x.0 while it is shared; the borrow ends here
      x.0 = 3;
      v
  }
  ```

  with the specification `ensures result == old(x).0`. The local `x` is an owned place
  ([tctx_own_to_oplace]); field 0 is borrowed shared at a fresh lifetime
  ([type_share_oplace_instr]), read through the reference and directly
  ([type_read_oplace_shr_instr]), unblocked once the lifetime has ended
  ([unblock_tctx_oplace_shr]) and written ([type_write_oplace_instr]).
  *)

  Definition share_local : val :=
    fn: ["x"] :=
      Newlft;;
      let: "r" := Share;; "x" in          (* &x.0 *)
      let: "v" := !"r" in                 (* *r *)
      let: "v0" := !"x" in                (* x.0, shared *)
      Endlft;;                            (* unblock x.0 *)
      let: "three" := #3 in
      "x" <- "three";;                    (* x.0 = 3 *)
      let: "ret" := new [ #1] in
      "ret" <- "v";;
      delete [ #2; "x"];;
      return: ["ret"].

  Definition share_local_spec : fn_spec [(Zₛ * Zₛ)%ST] Zₛ () :=
    λ _ post '-[(_, (a, _))], λ mask π, ∀ (lr: loc), post (lr, a) mask π.

  Lemma share_local_type :
    typed_val share_local ((fn(∅; int * int) → int) share_local_spec) (share_local, ()).
  Proof.
    unfold share_local. unlock.
    opose proof (@type_fn _ _ _ [(Zₛ * Zₛ)%ST] Zₛ () ()
      (λ _: (), FP ∅ +[(int * int)%T] int%T AtomicClosed)
      share_local_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros c ϝ k wl. destruct wl as [vx []]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      (* x as an owned place, unfolded *)
      iApply typed_body_tctx_incl.
      { eapply tctx_incl_trans; [apply tctx_own_to_oplace|].
        apply (tctx_unfold_oplace_prod _ _ _ _ PHole int int). }
      iApply (type_newlft []). iIntros (β).
      (* &x.0 *)
      iApply (type_let with "[]").
      { apply (type_share_oplace_instr _ _ _ vx 2 β (PFst PHole (OfTy int)) int);
          solve_typing. }
      { solve_typing. } { reflexivity. }
      iIntros (vr). simpl_subst.
      (* *r *)
      iApply (type_let with "[]").
      { eapply (type_deref_instr (𝔅 := Zₛ) _ int); [apply int_stack_okay|done|].
        apply (read_shr int β); [apply int_copy|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iIntros (vv). simpl_subst.
      (* x.0, while it is shared *)
      iApply (type_let with "[]").
      { apply (type_read_oplace_shr_instr _ _ _ vx 2 β (PFst PHole (OfTy int)) int);
          [solve_typing|done|apply _]. }
      { solve_typing. } { reflexivity. }
      iIntros (v0). simpl_subst.
      (* end β: unblock x.0 *)
      iApply (type_endlft _ _ _ _ β).
      { solve_typing. }
      { apply unblock_tctx_cons_just_hasty.
        apply (unblock_tctx_oplace_shr _ _ _ (PFst PHole (OfTy int)) int).
        repeat apply unblock_tctx_cons_just_hasty. apply unblock_tctx_nil. }
      (* x.0 = 3 *)
      iApply type_int. iIntros (v3). simpl_subst.
      iApply type_seq.
      { apply (type_write_oplace_instr _ _ _ vx v3 2 (PFst PHole (OfTy int)) int int
          (const (const True))); [done|done|apply resolve_just|done]. }
      { solve_typing. } { reflexivity. }
      (* fold x back, return v, free x *)
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_r +[_] +[_]).
        eapply tctx_incl_trans; [apply (tctx_fold_oplace_prod _ _ _ _ PHole int int)|].
        apply tctx_oplace_to_own. }
      iApply (type_letalloc_1 int). { solve_typing. } 2: { done. }
      { eapply (_: ∀ x, x ≡ x). } iIntros (vret). simpl_subst.
      iApply type_delete. { solve_typing. } { done. } { done. }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lx [a b]] []] mask π Hspec. rewrite /trans_upper /trans_tail /=.
    intros z _ [y0 [xp [y1 [y2 [y3 []]]]]] (_ & _ & <- & _) _ l. apply Hspec.
    Unshelve. by intros ?.
  Qed.
End place_shr.

Print Assumptions share_first_type.
Print Assumptions get_box_shr_type.
Print Assumptions get_uniq_shr_type.
Print Assumptions share_local_type.
