From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type function product programs own cont uninit int
  uniq_bor borrow place.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

Section get_first.
  Context `{!typeG Σ}.

  (*
  Taking a mutable reference to a field and returning it at the same lifetime, as in

  ```
  fn get_first<'a>(x: &'a mut (i32, i32)) -> &'a mut i32 {
      &mut x.0
  }
  ```

  with the specification (in Verus/Prusti notation)

  ```
  ensures *result == old(x).0,
          fin(x).0 == *fin(result),
          fin(x).1 == old(x).1
  ```

  (this is the shape of RefinedRust's `get_unchecked_mut`, Fig. 10 of the paper).

  The outer borrow `x` is dropped while its field 0 is still blocked by the
  returned reborrow, so its prophecy cannot be resolved to a current value. With
  place types:
    * the referent of `x` is unfolded into a place `ProdLty (OfTy int) (OfTy int)`
      ([tctx_unfold_uniq_prod]);
    * field 0 is reborrowed ([type_reborrow_place_instr]), which blocks it and
      reserves the prophecy of `x` for the reborrow's prophecy;
    * field 1 is reborrowed too, and this reborrow is resolved to its current value
      ([uniq_resolve]);
    * `x` is dropped while both fields are blocked ([tctx_drop_place]): its prophecy is
      resolved through the reservation to the final values of the two reborrows.
  *)

  Definition get_first : val :=
    fn: ["x"] :=
      let: "b" := !"x" in       (* b : &'a mut (i32, i32) *)
      delete [ #1; "x"];;
      ReBor;;                   (* &mut ( *b).0 *)
      ReBor;;                   (* &mut ( *b).1, to drop b *)
      Skip;;                    (* resolve the borrow of ( *b).1, drop b *)
      let: "r" := new [ #1] in
      "r" <- "b" +ₗ #0;;
      return: ["r"].

  Definition get_first_spec : fn_spec [uniq_borₛ (Zₛ * Zₛ)] (uniq_borₛ Zₛ) () :=
    λ _ post '-[(_, m)], λ mask π, ∀ (lr: loc) (r: ~~ (uniq_borₛ Zₛ)),
      uniq_bor_current r = (uniq_bor_current (𝔄:=Zₛ * Zₛ) m).1 →
      uniq_bor_future (𝔄:=Zₛ * Zₛ) m π =
        (uniq_bor_future r π, (uniq_bor_current (𝔄:=Zₛ * Zₛ) m).2) →
      post (lr, r) mask π.

  Lemma get_first_type :
    typed_val get_first
      ((fn<α>(∅; &uniq{α} (int * int)) → &uniq{α} int) get_first_spec)
      (get_first, ()).
  Proof.
    unfold get_first. unlock.
    opose proof (@type_fn _ _ _ [uniq_borₛ (Zₛ * Zₛ)] (uniq_borₛ Zₛ) () ()
      (λ α, FP ∅ +[&uniq{α} (int * int)]%T (&uniq{α} int)%T AtomicClosed)
      get_first_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros α ϝ k wl. destruct wl as [vx []]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      (* let b := !x *)
      iApply (type_let with "[]").
      { eapply (type_deref_instr (own_ptr 1 (&uniq{α} (int * int)))
          (&uniq{α} (int * int))).
        - apply uniq_stack_okay.
        - done.
        - apply (read_own_move (&uniq{α} (int * int))). }
      { apply tctx_extract_elt_here_exact. }
      { reflexivity. }
      iIntros (vb). simpl_subst.
      (* delete x *)
      iApply type_delete. { solve_typing. } { done. } { done. }
      (* unfold the referent of b *)
      iApply typed_body_tctx_incl.
      { apply (tctx_unfold_uniq_prod _ _ vb α int int). solve_typing. }
      (* &mut ( *b).0, at α ⊓ α *)
      iApply type_seq.
      { apply (type_reborrow_place_instr _ _ _ vb α α (PFst PHole (OfTy int)) int);
          [solve_typing|done]. }
      { solve_typing. } { reflexivity. }
      (* &mut ( *b).1, at α ⊓ α *)
      iApply type_seq.
      { apply (type_reborrow_place_instr _ _ _ vb α α (PSnd (Blocked int (α ⊓ α)) PHole) int);
          [solve_typing|done]. }
      { solve_typing. } { reflexivity. }
      (* resolve the borrow of field 1 *)
      iApply type_resolve. { solve_typing. } { apply uniq_bor.uniq_resolve. solve_typing. }
      (* drop b while both fields are blocked *)
      iApply typed_body_tctx_incl.
      { apply (tctx_incl_frame_r +[_] +[]). apply tctx_drop_place; [solve_typing|done|done]. }
      (* return the reborrow of field 0, in a box *)
      iApply (type_new 1). { lia. } iIntros (vr). simpl_subst.
      iApply type_assign. { solve_typing. } { by apply write_own. }
      { apply (resolve'_just _ _ _ (const True)). apply resolve_just. }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lx m] []] mask π. simpl.
    destruct m as [[[[[l [x1 x2]] ξi] d] g] idx]. simpl.
    intros Hspec. rewrite /trans_upper /trans_tail /=.
    intros z _ m1 Hl1 Hc1 m2 Hl2 Hc2 Hres Hfin lr junk w ->.
    apply Hspec; [done|]. rewrite Hfin.
    destruct m1 as [[[[[l1 y1] ζi] d1] g1] idx1].
    destruct m2 as [[[[[l2 y2] ηi] d2] g2] idx2].
    simpl in Hc1, Hc2, Hres. subst y1 y2.
    rewrite /place_cur /place_rfn /= ?prfn_den_inl /= !uniq_bor_future_eq. f_equal. exact Hres.
  Qed.

  (*
  Reborrowing a nested field:

  ```
  fn get_mid<'a>(x: &'a mut ((i32, i32), i32)) -> &'a mut i32 {
      &mut x.0.1
  }
  ```

  with the specification `ensures *result == old(x).0.1,
  fin(x) == ((old(x).0.0, *fin(result)), old(x).1)`. The referent of `x` is unfolded
  twice (at the root, then field 0, [tctx_unfold_place_prod]); field `.0.1` is
  reborrowed at the path `PFst (PSnd _ PHole) _`; to drop `x`, the other two leaves are
  reborrowed too, and these reborrows are resolved.
  *)

  Definition get_mid : val :=
    fn: ["x"] :=
      let: "b" := !"x" in
      delete [ #1; "x"];;
      ReBor;;                   (* &mut ( *b).0.1 *)
      ReBor;;                   (* &mut ( *b).0.0, to drop b *)
      ReBor;;                   (* &mut ( *b).1, to drop b *)
      Skip;;                    (* resolve the borrow of ( *b).0.0 *)
      Skip;;                    (* resolve the borrow of ( *b).1, drop b *)
      let: "r" := new [ #1] in
      "r" <- "b" +ₗ #1;;
      return: ["r"].

  Definition get_mid_spec : fn_spec [uniq_borₛ ((Zₛ * Zₛ) * Zₛ)] (uniq_borₛ Zₛ) () :=
    λ _ post '-[(_, m)], λ mask π, ∀ (lr: loc) (r: ~~ (uniq_borₛ Zₛ)),
      uniq_bor_current r = (uniq_bor_current (𝔄:=(Zₛ * Zₛ) * Zₛ) m).1.2 →
      uniq_bor_future (𝔄:=(Zₛ * Zₛ) * Zₛ) m π =
        (((uniq_bor_current (𝔄:=(Zₛ * Zₛ) * Zₛ) m).1.1, uniq_bor_future r π),
          (uniq_bor_current (𝔄:=(Zₛ * Zₛ) * Zₛ) m).2) →
      post (lr, r) mask π.

  Lemma get_mid_type :
    typed_val get_mid
      ((fn<α>(∅; &uniq{α} ((int * int) * int)) → &uniq{α} int) get_mid_spec)
      (get_mid, ()).
  Proof.
    unfold get_mid. unlock.
    opose proof (@type_fn _ _ _ [uniq_borₛ ((Zₛ * Zₛ) * Zₛ)] (uniq_borₛ Zₛ) () ()
      (λ α, FP ∅ +[&uniq{α} ((int * int) * int)]%T (&uniq{α} int)%T AtomicClosed)
      get_mid_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros α ϝ k wl. destruct wl as [vx []]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply (type_let with "[]").
      { eapply (type_deref_instr (own_ptr 1 (&uniq{α} ((int * int) * int)))
          (&uniq{α} ((int * int) * int))).
        - apply uniq_stack_okay.
        - done.
        - apply (read_own_move (&uniq{α} ((int * int) * int))). }
      { apply tctx_extract_elt_here_exact. }
      { reflexivity. }
      iIntros (vb). simpl_subst.
      iApply type_delete. { solve_typing. } { done. } { done. }
      (* unfold the referent of b, then its field 0 *)
      iApply typed_body_tctx_incl.
      { apply (tctx_unfold_uniq_prod _ _ vb α (int * int) int). solve_typing. }
      iApply typed_body_tctx_incl.
      { apply (tctx_unfold_place_prod _ _ vb α (PFst PHole (OfTy int)) int int);
          [solve_typing|done]. }
      (* &mut ( *b).0.1, at α ⊓ α *)
      iApply type_seq.
      { apply (type_reborrow_place_instr _ _ _ vb α α
          (PFst (PSnd (OfTy int) PHole) (OfTy int)) int); [solve_typing|done]. }
      { solve_typing. } { reflexivity. }
      (* &mut ( *b).0.0 and &mut ( *b).1 *)
      iApply type_seq.
      { apply (type_reborrow_place_instr _ _ _ vb α α
          (PFst (PFst PHole (Blocked int (α ⊓ α))) (OfTy int)) int); [solve_typing|done]. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_reborrow_place_instr _ _ _ vb α α
          (PSnd (ProdLty (Blocked int (α ⊓ α)) (Blocked int (α ⊓ α))) PHole) int);
          [solve_typing|done]. }
      { solve_typing. } { reflexivity. }
      (* resolve them, and drop b *)
      iApply type_resolve. { solve_typing. } { apply uniq_bor.uniq_resolve. solve_typing. }
      iApply type_resolve. { solve_typing. } { apply uniq_bor.uniq_resolve. solve_typing. }
      iApply typed_body_tctx_incl.
      { apply (tctx_incl_frame_r +[_] +[]).
        apply tctx_drop_place; [solve_typing|done|done]. }
      iApply (type_new 1). { lia. } iIntros (vr). simpl_subst.
      iApply type_assign. { solve_typing. } { by apply write_own. }
      { apply (resolve'_just _ _ _ (const True)). apply resolve_just. }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lx m] []] mask π. simpl.
    destruct m as [[[[[l [[x1 x2] x3]] ξi] d] g] idx]. simpl.
    intros Hspec. rewrite /trans_upper /trans_tail /=.
    intros z _ m1 Hl1 Hc1 m2 Hl2 Hc2 m3 Hl3 Hc3 Hres3 Hres2 Hfin lr junk w ->.
    apply Hspec; [done|]. rewrite Hfin.
    destruct m1 as [[[[[l1 y1] ζi1] d1] g1] idx1].
    destruct m2 as [[[[[l2 y2] ζi2] d2] g2] idx2].
    destruct m3 as [[[[[l3 y3] ζi3] d3] g3] idx3].
    simpl in Hc1, Hc2, Hc3, Hres2, Hres3. subst y1 y2 y3.
    rewrite /place_cur /place_rfn /= ?prfn_den_inl /= !uniq_bor_future_eq.
    f_equal; [f_equal|]; first [exact Hres2|exact Hres3|done].
  Qed.

  (*
  Writing through a reborrow of a field, then using the outer borrow again:

  ```
  fn set_first<'a>(x: &'a mut (i32, i32)) {
      { let r = &mut x.0; *r = 5; }   // the reborrow ends here
      // x is usable again
  }
  ```

  with the specification `ensures fin(x) == (5, old(x).1)`. Field 0 is blocked while
  the reborrow is alive; after its lifetime has ended, field 0 is unblocked
  ([unblock_tctx_place]), getting the final value of the reborrow, and the
  place is folded back ([tctx_fold_uniq_prod]).
  *)

  Definition set_first : val :=
    fn: ["x"] :=
      let: "b" := !"x" in
      delete [ #1; "x"];;
      Newlft;;
      ReBor;;                   (* &mut ( *b).0 *)
      let: "five" := #5 in
      "b" +ₗ #0 <- "five";;
      Skip;;                    (* resolve the reborrow *)
      Endlft;;                  (* unblock field 0 *)
      Skip;;                    (* resolve b *)
      let: "r" := new [ #0] in
      return: ["r"].

  Definition set_first_spec : fn_spec [uniq_borₛ (Zₛ * Zₛ)] () () :=
    λ _ post '-[(_, m)], λ mask π,
      uniq_bor_future (𝔄:=Zₛ * Zₛ) m π = (5%Z, (uniq_bor_current (𝔄:=Zₛ * Zₛ) m).2) →
      ∀ ret, post ret mask π.

  Lemma set_first_type :
    typed_val set_first
      ((fn<α>(∅; &uniq{α} (int * int)) → ()) set_first_spec)
      (set_first, ()).
  Proof.
    unfold set_first. unlock.
    opose proof (@type_fn _ _ _ [uniq_borₛ (Zₛ * Zₛ)] () () ()
      (λ α, FP ∅ +[&uniq{α} (int * int)]%T ()%T AtomicClosed)
      set_first_spec _ [BNamed "x"] _ _ _) as H.
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
      (* &mut ( *b).0, at α ⊓ β *)
      iApply type_seq.
      { apply (type_reborrow_place_instr _ _ _ vb α β (PFst PHole (OfTy int)) int);
          [solve_typing|done]. }
      { solve_typing. } { reflexivity. }
      (* write through the reborrow *)
      iApply type_int. iIntros (v5). simpl_subst.
      iApply type_assign. { solve_typing. } { apply write_uniq. solve_typing. }
      { apply (resolve'_just _ _ _ (const True)). apply resolve_just. }
      iApply type_resolve. { solve_typing. } { apply uniq_bor.uniq_resolve. solve_typing. }
      iApply typed_body_tctx_incl; [apply tctx_incl_resolve_head|].
      (* end β: unblock field 0 *)
      iApply (type_endlft _ _ _ _ β).
      { solve_typing. }
      { apply (unblock_tctx_place _ _ _ (PFst PHole (OfTy int))); [solve_typing|done|].
        apply unblock_tctx_nil. }
      (* fold back, and resolve b *)
      iApply typed_body_tctx_incl.
      { apply (tctx_fold_uniq_prod _ _ vb α int int). solve_typing. }
      iApply type_resolve. { solve_typing. } { apply uniq_bor.uniq_resolve. solve_typing. }
      iApply (type_new_subtype () 0). { lia. } { apply uninit_unit_1. }
      iIntros (vr). simpl_subst.
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lx m] []] mask π. simpl.
    destruct m as [[[[[l [x1 x2]] ξi] d] g] idx]. simpl.
    intros Hspec. rewrite /trans_upper /trans_tail /=.
    intros z _ m1 Hl1 Hc1 z0 Hupd Hres0 [x' []] (Hl' & Hfut & Hcur & _ & Hhole & _).
    destruct x' as [[[[[[l' [y1 y2]] ξi'] d'] g'] idx'] ζis']. simpl.
    intros _ Hres l1 junk. apply Hspec.
    rewrite /place_bor /= in Hfut Hcur Hhole. rewrite -Hfut uniq_bor_future_eq.
    rewrite (_: (π (uniq_prvar (𝔄:=Zₛ * Zₛ) (y1, y2) ξi')).1 = (y1, y2)); [|exact Hres].
    injection Hcur as ->. f_equal. rewrite Hhole /place_blk_fin /=.
    destruct m1 as [[[[[l1' w1] ζi] d1] g1] idx1].
    destruct z0 as [[[[[l2 w2] ζi'] d2] g2] idx2].
    destruct Hupd as (_ & -> & ->). simpl in Hres0 |- *. rewrite -Hres0.
    apply (uniq_prvar_app_irrel x1 5%Z ζi π).
    Unshelve. eapply (composeₛ empty_prod_to_unitₛ uninit0_to_unitₛ).
  Qed.
End get_first.
