From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type function product programs own cont uninit int
  uniq_bor borrow vplace place_puniq place_resolve.
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
  fin(x) == (Box( *fin(result)), old(x).1)` (the box keeps its address). The borrow `x`
  is a place rooted at its value ([type_uniq_to_vplace_instr]); its referent and then
  the box are unfolded ([type_unfold_vplace_prod_instr], [type_unfold_vplace_own_deep_instr]);
  the pointee of the box is reborrowed at the path `PUniq 'a (PFst (POwn _ PHole) _)`,
  which loads the box's address ([type_borrow_vplace_deep_instr]); to drop `x`, field 1
  is reborrowed too.
  *)

  Definition get_box : val :=
    fn: ["x"] :=
      let: "b" := !"x" in
      delete [ #1; "x"];;
      Skip;;                        (* b as a place *)
      ReBor;; ReBor;;               (* unfold *b, then the box ( *b).0 *)
      let: "r" := ReBor;; !"b" in   (* &mut *( *b).0 *)
      let: "r1" := ReBor;; "b" +ₗ #1 in   (* &mut ( *b).1, to drop b *)
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
      iApply type_seq. { apply (type_uniq_to_vplace_instr _ _ _ vb α (own_ptr 1 int * int)). }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_unfold_vplace_prod_instr _ _ _ vb (PUniq α PHole) (own_ptr 1 int) int).
        simpl. solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_unfold_vplace_own_deep_instr _ _ _ vb (PUniq α (PFst PHole (OfTy int))) 1 int);
          [done|simpl; solve_typing]. }
      { solve_typing. } { reflexivity. }
      (* &mut *( *b).0, at α ⊓ α *)
      iApply (type_let with "[]").
      { apply (type_borrow_vplace_deep_instr _ _ _ vb α
          (PUniq α (PFst (POwn 1 PHole) (OfTy int))) int); [done|simpl; solve_typing|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iIntros (vr). simpl_subst.
      (* &mut ( *b).1, at α ⊓ α *)
      iApply (type_let with "[]").
      { apply (type_borrow_vplace_deep_instr _ _ _ vb α
          (PUniq α (PSnd (OwnPtrLty 1 (Blocked int (α ⊓ α))) PHole)) int);
          [done|simpl; solve_typing|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iIntros (vr1). simpl_subst.
      (* resolve it, and drop b *)
      iApply type_resolve. { solve_typing. } { apply uniq_bor.uniq_resolve. solve_typing. }
      iApply typed_body_tctx_incl.
      { apply (tctx_incl_frame_r +[_] +[]).
        apply tctx_drop_vplace_uniq; [solve_typing|done|done]. }
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
    intros z _ m1 Hc1 m2 Hc2 Hres Hfin lr junk w ->.
    apply Hspec; [done|]. rewrite Hfin.
    destruct m1 as [[[[[l1 y1] ζi1] d1] g1] idx1].
    destruct m2 as [[[[[l2 y2] ζi2] d2] g2] idx2].
    simpl in Hc1, Hc2, Hres. subst y1 y2.
    f_equal; first [exact Hres|done|f_equal; done].
  Qed.

End place_box.
