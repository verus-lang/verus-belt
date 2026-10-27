From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type function product programs own cont uninit int
  uniq_bor borrow place.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

Section place_box.
  Context `{!typeG Σ}.

  (*
  Reborrowing through a box below a unique borrow:

  ```
  fn get_box<'a>(x: &'a mut (Box<i32>, i32)) -> &'a mut i32 {
      &mut *x.0
  }
  ```

  with the specification `ensures *result == *old(x).0,
  fin(x) == (Box( *fin(result)), old(x).1)` (the box keeps its address). The box is
  unfolded below `x` ([tctx_unfold_place_own]); its pointee is reborrowed at the path
  `PFst (POwn _ PHole) _`, which loads the box's address
  ([type_reborrow_place_deref_instr]); to drop `x`, field 1 is reborrowed too.
  *)

  Definition get_box : val :=
    fn: ["x"] :=
      let: "b" := !"x" in
      delete [ #1; "x"];;
      let: "r" := ReBor;; !"b" in   (* &mut *( *b).0 *)
      ReBor;;                       (* &mut ( *b).1, to drop b *)
      Skip;;                        (* resolve the borrow of ( *b).1, drop b *)
      let: "ret" := new [ #1] in
      "ret" <- "r";;
      return: ["ret"].

  Definition get_box_spec : fn_spec [uniq_borₛ (at_locₛ Zₛ * Zₛ)] (uniq_borₛ Zₛ) () :=
    λ _ post '-[(_, m)], λ mask π, ∀ (lr: loc) (r: ~~ (uniq_borₛ Zₛ)),
      uniq_bor_current r = (uniq_bor_current (𝔄:=at_locₛ Zₛ * Zₛ) m).1.2 →
      uniq_bor_future (𝔄:=at_locₛ Zₛ * Zₛ) m π =
        (((uniq_bor_current (𝔄:=at_locₛ Zₛ * Zₛ) m).1.1, uniq_bor_future r π),
          (uniq_bor_current (𝔄:=at_locₛ Zₛ * Zₛ) m).2) →
      post (lr, r) mask π.

  Lemma get_box_type :
    typed_val get_box
      ((fn<α>(∅; &uniq{α} (own_ptr 1 int * int)) → &uniq{α} int) get_box_spec)
      (get_box, ()).
  Proof.
    unfold get_box. unlock.
    opose proof (@type_fn _ _ _ [uniq_borₛ (at_locₛ Zₛ * Zₛ)] (uniq_borₛ Zₛ) () ()
      (λ α, FP ∅ +[&uniq{α} (own_ptr 1 int * int)]%T (&uniq{α} int)%T AtomicClosed)
      get_box_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros α ϝ k wl. destruct wl as [vx []]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply (type_let with "[]").
      { eapply (type_deref_instr (own_ptr 1 (&uniq{α} (own_ptr 1 int * int)))
          (&uniq{α} (own_ptr 1 int * int))).
        - apply uniq_stack_okay.
        - done.
        - apply (read_own_move (&uniq{α} (own_ptr 1 int * int))). }
      { apply tctx_extract_elt_here_exact. }
      { reflexivity. }
      iIntros (vb). simpl_subst.
      iApply type_delete. { solve_typing. } { done. } { done. }
      (* unfold the referent of b, then the box *)
      iApply typed_body_tctx_incl.
      { apply (tctx_unfold_uniq_prod _ _ vb α (own_ptr 1 int) int). solve_typing. }
      iApply typed_body_tctx_incl.
      { apply (tctx_unfold_place_own _ _ vb α (PFst PHole (OfTy int)) 1 int);
          [solve_typing|done|done]. }
      (* &mut *( *b).0, at α ⊓ α *)
      iApply (type_let with "[]").
      { apply (type_reborrow_place_deref_instr _ _ _ vb α α
          (PFst (POwn 1 PHole) (OfTy int)) int); [solve_typing|done]. }
      { solve_typing. } { reflexivity. }
      iIntros (vr). simpl_subst.
      (* &mut ( *b).1, at α ⊓ α *)
      iApply type_seq.
      { apply (type_reborrow_place_instr _ _ _ vb α α
          (PSnd (OwnPtrLty 1 (Blocked int (α ⊓ α))) PHole) int); [solve_typing|done|done]. }
      { solve_typing. } { reflexivity. }
      (* resolve it, and drop b *)
      iApply type_resolve. { solve_typing. } { apply uniq_bor.uniq_resolve. solve_typing. }
      iApply typed_body_tctx_incl.
      { apply (tctx_incl_frame_r +[_] +[]).
        apply tctx_drop_place; [solve_typing|done|done]. }
      iApply (type_new 1). { lia. } iIntros (vret). simpl_subst.
      iApply type_assign. { solve_typing. } { by apply write_own. }
      { apply (resolve'_just _ _ _ (const True)). apply resolve_just. }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lx m] []] mask π. simpl.
    destruct m as [[[[[l [[lb x1] x2]] ξi] d] g] idx]. simpl.
    intros Hspec. rewrite /trans_upper /trans_tail /=.
    intros z _ m1 Hl1 Hc1 m2 Hl2 Hc2 Hres Hfin lr junk w ->.
    apply Hspec; [done|]. rewrite Hfin.
    destruct m1 as [[[[[l1 y1] ζi1] d1] g1] idx1].
    destruct m2 as [[[[[l2 y2] ζi2] d2] g2] idx2].
    simpl in Hc1, Hc2, Hres. subst y1 y2.
    rewrite /place_cur /place_rfn /=.
    f_equal; first [exact Hres|done|f_equal; done].
  Qed.

End place_box.
