From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type function product programs own cont uninit int
  uniq_bor borrow vplace place_own place_resolve place_puniq.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

Section place_deep_box.
  Context `{!typeG Σ}.

  (*
  Reading through a box inside a box inside a local box:

  ```
  fn deep_read(b: Box<(Box<Box<i32>>, i32)>) -> i32 { ***b.0 }
  ```

  with the specification `ensures result == ***old(b).0`. The pointee of `b` is an owned
  place; its field 0 (a box, one later deep) is unfolded by [tctx_unfold_oplace_own],
  the box inside it (two laters deep) by [type_unfold_oplace_own_instr] (a program step,
  whose credits strip the laters); the integer is read ([type_read_oplace_instr], at
  `PFst (POwn 1 (POwn 1 PHole)) _`), and the place is dropped (the two inner boxes and
  `b` are freed, [type_drop_oplace_instr]).
  *)

  Notation deep_readₛ := (at_locₛ (at_locₛ (at_locₛ Zₛ) * Zₛ))%ST.

  Definition deep_read : val :=
    fn: ["x"] :=
      let: "b" := !"x" in
      delete [ #1; "x"];;
      Skip;;                                            (* unfold *( *b).0 *)
      let: "v" := !(!(!"b")) in                         (* ***b.0 *)
      ((((#☠;; delete [ #1; !(!"b")]);; delete [ #1; !"b"]);; #☠);;  (* drop b *)
       delete [ #2; "b"]);;
      let: "r" := new [ #1] in
      "r" <- "v";;
      return: ["r"].

  Definition deep_read_spec : fn_spec [deep_readₛ] Zₛ () :=
    λ _ post '-[(_, (l, ((l1, (l2, v)), w)))], λ mask π, ∀ (lr: loc), post (lr, v) mask π.

  Lemma deep_read_type :
    typed_val deep_read ((fn(∅; box (box (box int) * int)) → int) deep_read_spec)
      (deep_read, ()).
  Proof.
    unfold deep_read. unlock.
    opose proof (@type_fn _ _ _ [deep_readₛ] Zₛ () ()
      (λ _: (), FP ∅ +[box (box (box int) * int)] int AtomicClosed)
      deep_read_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros c ϝ k wl. destruct wl as [vx []]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply (type_let with "[]").
      { eapply (type_deref_instr (own_ptr 1 (box (box (box int) * int)))
          (box (box (box int) * int))).
        - apply own_stack_okay.
        - done.
        - apply (read_own_move (box (box (box int) * int))). }
      { apply tctx_extract_elt_here_exact. }
      { reflexivity. }
      iIntros (vb). simpl_subst.
      iApply type_delete. { solve_typing. } { done. } { done. }
      (* the pointee of b as an owned place; unfold the pair and the box in field 0 *)
      iApply typed_body_tctx_incl.
      { eapply tctx_incl_trans; [apply tctx_own_to_oplace|].
        eapply tctx_incl_trans;
          [apply (tctx_unfold_oplace_prod _ _ _ _ PHole (box (box int)) int)|].
        apply (tctx_unfold_oplace_own _ _ _ _ (PFst PHole (OfTy int)) 1 (box int)). done. }
      (* unfold the box inside it, two laters deep *)
      iApply type_seq.
      { apply (type_unfold_oplace_own_instr _ _ _ vb 2 (PFst (POwn 1 PHole) (OfTy int)) 1 int). }
      { solve_typing. } { reflexivity. }
      (* read ***b.0 *)
      iApply (type_let with "[]").
      { apply (type_read_oplace_instr _ _ _ vb 2 (PFst (POwn 1 (POwn 1 PHole)) (OfTy int)) int);
          [done|apply _]. }
      { solve_typing. } { reflexivity. }
      iIntros (vv). simpl_subst.
      (* drop b *)
      iApply type_seq.
      { apply (type_drop_oplace_instr _ _ _ vb 2 2
          (ProdLty (OwnPtrLty 1 (OwnPtrLty 1 (OfTy int))) (OfTy int)));
          [done|done|done|].
        apply lty_resolve_prod; [apply lty_resolve_own; apply lty_resolve_own|];
          apply lty_resolve_ofty; apply resolve_just. }
      { solve_typing. } { reflexivity. }
      iApply (type_new 1). { lia. } iIntros (vr). simpl_subst.
      iApply type_assign. { solve_typing. } { by apply write_own. }
      { apply (resolve'_just _ _ _ (const True)). apply resolve_just. }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lx [l [[l1 [l2 v]] w]]] []] mask π Hspec. rewrite /trans_upper /trans_tail /=.
    intros _ _ _ l0 _ z0 ->. apply Hspec.
  Qed.

  (*
  Reborrowing through a box inside a box behind a mutable reference:

  ```
  fn deep_get<'a>(x: &'a mut (Box<Box<i32>>, i32)) -> &'a mut i32 { &mut ***x.0 }
  ```

  with the specification `ensures *result == ***old(x).0,
  fin(x) == ((old(x).0 with ***.0 = *fin(result)), old(x).1)` (the boxes keep their
  addresses). The borrow `x` is a place rooted at its value ([type_uniq_to_vplace_instr]);
  its referent is unfolded into a pair, the box in field 0 and the box inside it are
  unfolded ([type_unfold_vplace_own_deep_instr]); the integer is reborrowed
  ([type_borrow_vplace_deep_instr], address `!(!b)`); `x` is resolved
  ([type_resolve_vplace_uniq_instr]).
  *)

  Notation deep_getₛ := (at_locₛ (at_locₛ Zₛ) * Zₛ)%ST.

  Definition deep_get : val :=
    fn: ["x"] :=
      let: "b" := !"x" in
      delete [ #1; "x"];;
      Skip;;                                    (* b as a place *)
      ReBor;; ReBor;; ReBor;;                   (* unfold *b, *( *b).0 and **( *b).0 *)
      let: "r" := (Skip;; Skip);; !(!"b") in    (* &mut ***( *b).0 *)
      (Skip;; Skip;; #☠);;                      (* resolve b *)
      let: "ret" := new [ #1] in
      "ret" <- "r";;
      return: ["ret"].

  Definition deep_get_spec : fn_spec [uniq_borₛ deep_getₛ] (uniq_borₛ Zₛ) () :=
    λ _ post '-[(_, m)], λ mask π, ∀ (lr: loc) (r: ~~ (uniq_borₛ Zₛ)),
      let c := uniq_bor_current (𝔄:=deep_getₛ) m in
      uniq_bor_current r = c.1.2.2 →
      uniq_bor_future (𝔄:=deep_getₛ) m π = ((c.1.1, (c.1.2.1, uniq_bor_future r π)), c.2) →
      post (lr, r) mask π.

  Lemma deep_get_type :
    typed_val deep_get
      ((fn<α>(∅; &uniq{α} (box (box int) * int)) → &uniq{α} int) deep_get_spec)
      (deep_get, ()).
  Proof.
    unfold deep_get. unlock.
    opose proof (@type_fn _ _ _ [uniq_borₛ deep_getₛ] (uniq_borₛ Zₛ) () ()
      (λ α, FP ∅ +[&uniq{α} (box (box int) * int)]%T (&uniq{α} int)%T AtomicClosed)
      deep_get_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros α ϝ k wl. destruct wl as [vx []]. simpl_subst.
    have Alv: lctx_lft_alive
      (fp_E (FP ∅ +[&uniq{α} (box (box int) * int)]%T (&uniq{α} int) AtomicClosed) ϝ)
      [ϝ ⊑ₗ []] α.
    { eapply lctx_lft_alive_external; [rewrite /fp_E /=; by left|solve_typing]. }
    iApply (typed_body_impl with "[]"); last first. {
      iApply (type_let with "[]").
      { eapply (type_deref_instr (own_ptr 1 (&uniq{α} (box (box int) * int)))
          (&uniq{α} (box (box int) * int))).
        - apply uniq_stack_okay.
        - done.
        - apply (read_own_move (&uniq{α} (box (box int) * int))). }
      { apply tctx_extract_elt_here_exact. }
      { reflexivity. }
      iIntros (vb). simpl_subst.
      iApply type_delete. { solve_typing. } { done. } { done. }
      (* unfold the referent of b, and the box in field 0 *)
      iApply type_seq. { apply (type_uniq_to_vplace_instr _ _ _ vb α (box (box int) * int)). }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_unfold_vplace_prod_instr _ _ _ vb (PUniq α PHole) (box (box int)) int).
        simpl. solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_unfold_vplace_own_deep_instr _ _ _ vb (PUniq α (PFst PHole (OfTy int))) 1
          (box int)); [done|simpl; solve_typing]. }
      { solve_typing. } { reflexivity. }
      (* unfold the box inside it *)
      iApply type_seq.
      { apply (type_unfold_vplace_own_deep_instr _ _ _ vb
          (PUniq α (PFst (POwn 1 PHole) (OfTy int))) 1 int); [done|simpl; solve_typing]. }
      { solve_typing. } { reflexivity. }
      (* &mut ***( *b).0, at α ⊓ α *)
      iApply (type_let with "[]").
      { apply (type_borrow_vplace_deep_instr _ _ _ vb α
          (PUniq α (PFst (POwn 1 (POwn 1 PHole)) (OfTy int))) int);
          [done|simpl; solve_typing|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iIntros (vr). simpl_subst.
      (* resolve b *)
      iApply type_seq.
      { apply (type_resolve_vplace_uniq_instr _ _ _ vb α
          (ProdLty (OwnPtrLty 1 (OwnPtrLty 1 (Blocked int (α ⊓ α)))) (OfTy int)));
          [done|done|done|set_solver]. }
      { solve_typing. } { reflexivity. }
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
    destruct m as [[[[[l [[l1 [l2 a]] b]] ξi] d] g] idx]. simpl.
    intros Hspec. rewrite /trans_upper /trans_tail /=.
    intros z _ m1 Hc1 Hres lr junk w ->.
    apply Hspec; [done|]. rewrite Hres.
    destruct m1 as [[[[[l1' y1] ζi1] d1] g1] idx1]. simpl in Hc1. subst y1.
    by rewrite /= !uniq_bor_future_eq.
  Qed.
End place_deep_box.

Print Assumptions deep_read_type.
Print Assumptions deep_get_type.
