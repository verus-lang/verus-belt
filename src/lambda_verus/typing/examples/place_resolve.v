From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type function product programs own cont uninit int sum type_sum
  uniq_bor borrow place place_own place_sum place_resolve.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

Section place_resolve.
  Context `{!typeG Σ}.

  Notation opt := (Σ! +[(); int])%T.
  Notation optₛ := (Σ! [unitₛ; Zₛ])%ST.

  (*
  Resolving a unique borrow while some of its leaves are blocked and others are not:

  ```
  fn get_last<'a>(x: &'a mut (Box<i32>, (Option<i32>, i32))) -> &'a mut i32 {
      &mut x.1.1
  }
  ```

  with the specification `ensures *result == old(x).1.1,
  fin(x) == (old(x).0, (old(x).1.0, *fin(result)))`. The referent of `x` is unfolded into
  the place `ProdLty (OwnPtrLty 1 (OfTy int)) (ProdLty (OfTy opt) (OfTy int))` (the box is
  unfolded, the sum is a leaf); `.1.1` is reborrowed; `x` is then resolved
  ([type_resolve_place_instr], two program steps for the two unblocked leaves `*x.0` and
  `x.1.0`, and one to open the borrow) while `.1.1` is blocked, without reborrowing
  the other leaves.
  *)

  Definition get_last : val :=
    fn: ["x"] :=
      let: "b" := !"x" in
      delete [ #1; "x"];;
      ReBor;;                       (* &mut ( *b).1.1 *)
      (Skip;; Skip;; Skip;; #☠);;   (* resolve b *)
      let: "r" := new [ #1] in
      "r" <- "b" +ₗ #3;;
      return: ["r"].

  Definition get_last_spec :
      fn_spec [uniq_borₛ (at_locₛ Zₛ * (optₛ * Zₛ))] (uniq_borₛ Zₛ) () :=
    λ _ post '-[(_, m)], λ mask π, ∀ (lr: loc) (r: ~~ (uniq_borₛ Zₛ)),
      uniq_bor_current r = (uniq_bor_current (𝔄:=at_locₛ Zₛ * (optₛ * Zₛ)) m).2.2 →
      uniq_bor_future (𝔄:=at_locₛ Zₛ * (optₛ * Zₛ)) m π =
        ((uniq_bor_current (𝔄:=at_locₛ Zₛ * (optₛ * Zₛ)) m).1,
         (@vπ optₛ (uniq_bor_current (𝔄:=at_locₛ Zₛ * (optₛ * Zₛ)) m).2.1 π,
          uniq_bor_future r π)) →
      post (lr, r) mask π.

  Lemma get_last_type :
    typed_val get_last
      ((fn<α>(∅; &uniq{α} (own_ptr 1 int * (opt * int))) → &uniq{α} int) get_last_spec)
      (get_last, ()).
  Proof.
    unfold get_last. unlock.
    opose proof (@type_fn _ _ _ [uniq_borₛ (at_locₛ Zₛ * (optₛ * Zₛ))] (uniq_borₛ Zₛ) () ()
      (λ α, FP ∅ +[&uniq{α} (own_ptr 1 int * (opt * int))]%T (&uniq{α} int)%T AtomicClosed)
      get_last_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros α ϝ k wl. destruct wl as [vx []]. simpl_subst.
    (* [α] is alive (proved once: the proof by [solve_typing] is slow to check). *)
    have Alv: lctx_lft_alive
      (fp_E (FP ∅ +[&uniq{α} (own_ptr 1 int * (opt * int))]%T (&uniq{α} int) AtomicClosed) ϝ)
      [ϝ ⊑ₗ []] α.
    { eapply lctx_lft_alive_external; [rewrite /fp_E /=; by left|solve_typing]. }
    iApply (typed_body_impl with "[]"); last first. {
      iApply (type_let with "[]").
      { eapply (type_deref_instr (own_ptr 1 (&uniq{α} (own_ptr 1 int * (opt * int))))
          (&uniq{α} (own_ptr 1 int * (opt * int)))).
        - apply uniq_stack_okay.
        - done.
        - apply (read_own_move (&uniq{α} (own_ptr 1 int * (opt * int)))). }
      { apply tctx_extract_elt_here_exact. }
      { reflexivity. }
      iIntros (vb). simpl_subst.
      iApply type_delete. { solve_typing. } { done. } { done. }
      (* unfold the referent of b, its field 1, and the box *)
      iApply typed_body_tctx_incl.
      { apply (tctx_unfold_uniq_prod _ _ vb α (own_ptr 1 int) (opt * int)). done. }
      iApply typed_body_tctx_incl.
      { apply (tctx_unfold_place_prod _ _ vb α (PSnd (OfTy (own_ptr 1 int)) PHole) opt int);
          [done|done]. }
      iApply typed_body_tctx_incl.
      { apply (tctx_unfold_place_own _ _ vb α
          (PFst PHole (ProdLty (OfTy opt) (OfTy int))) 1 int); [done|done|done]. }
      (* &mut ( *b).1.1, at α ⊓ α *)
      iApply type_seq.
      { apply (type_reborrow_place_instr _ _ _ vb α α
          (PSnd (OwnPtrLty 1 (OfTy int)) (PSnd (OfTy opt) PHole)) int); [done|done|done]. }
      { solve_typing. } { reflexivity. }
      (* resolve b, with the leaf .1.1 blocked *)
      iApply type_seq.
      { apply (type_resolve_place_instr _ _ _ vb α
          (ProdLty (OwnPtrLty 1 (OfTy int)) (ProdLty (OfTy opt) (Blocked int (α ⊓ α)))));
          [done|done|done]. }
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
    intros post [[lx m] []] mask π. simpl.
    destruct m as [[[[[l [[lb x1] [x2 x3]]] ξi] d] g] idx]. simpl.
    intros Hspec. rewrite /trans_upper /trans_tail /=.
    intros z _ m1 Hl1 Hc1 Hres lr junk w ->.
    apply Hspec; [done|]. rewrite Hres.
    destruct m1 as [[[[[l1 y1] ζi1] d1] g1] idx1]. simpl in Hc1. subst y1.
    rewrite /place_cur /place_rfn /=. done.
  Qed.

  (*
  Dropping a local box place after a move-out and a write:

  ```
  fn drop_local(b: Box<(Box<i32>, Option<i32>)>) -> i32 {
      let v = *b.0;   // move out of the inner box: its contents are uninitialized
      b.1 = Some(5);  // write a new variant
      v               // b is dropped: the inner box and b are freed
  }
  ```

  with the specification `ensures result == *old(b).0`. The pointee of `b` is an owned
  place, unfolded into `ProdLty (OwnPtrLty 1 (OfTy int)) (OfTy opt)`; the contents of the
  inner box are moved out ([type_move_oplace_instr]), leaving the leaf [OfTy (↯ 1)];
  field 1 gets a new variant ([type_sum_assign_oplace_instr]); then the place is dropped
  ([type_drop_oplace_instr]): its leaves are resolved ([lty_resolve]: nothing for the
  uninitialized leaf, the type's resolution for the sum), the inner box is freed
  ([drop_boxes]), then `b`.
  *)

  Notation drop_localₛ := (at_locₛ (at_locₛ Zₛ * optₛ))%ST.

  Definition drop_local : val :=
    fn: ["x"] :=
      let: "b" := !"x" in
      delete [ #1; "x"];;
      let: "v" := !(!"b") in                (* move *( *b).0 out *)
      let: "five" := #5 in
      ("b" +ₗ #1) <-{Σ 1} "five";;           (* ( *b).1 = Some(5) *)
      (((#☠;; delete [ #1; !"b"]);; #☠);;   (* drop b: free the inner box, *)
       delete [ #3; "b"]);;                  (* then b *)
      let: "r" := new [ #1] in
      "r" <- "v";;
      return: ["r"].

  Definition drop_local_spec : fn_spec [drop_localₛ] Zₛ () :=
    λ _ post '-[(_, (l, ((lb, v0), w)))], λ mask π, ∀ (lr: loc), post (lr, v0) mask π.

  Lemma drop_local_type :
    typed_val drop_local ((fn(∅; box (box int * opt)) → int) drop_local_spec)
      (drop_local, ()).
  Proof.
    unfold drop_local. unlock.
    opose proof (@type_fn _ _ _ [drop_localₛ] Zₛ () ()
      (λ _: (), FP ∅ +[box (box int * opt)] int AtomicClosed)
      drop_local_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros c ϝ k wl. destruct wl as [vx []]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply (type_let with "[]").
      { eapply (type_deref_instr (own_ptr 1 (box (box int * opt))) (box (box int * opt))).
        - apply own_stack_okay.
        - done.
        - apply (read_own_move (box (box int * opt))). }
      { apply tctx_extract_elt_here_exact. }
      { reflexivity. }
      iIntros (vb). simpl_subst.
      iApply type_delete. { solve_typing. } { done. } { done. }
      (* the pointee of b as an owned place; unfold the pair and the inner box *)
      iApply typed_body_tctx_incl.
      { eapply tctx_incl_trans; [apply tctx_own_to_oplace|].
        eapply tctx_incl_trans; [apply (tctx_unfold_oplace_prod _ _ _ _ PHole (box int) opt)|].
        apply (tctx_unfold_oplace_own _ _ _ _ (PFst PHole (OfTy opt)) 1 int). done. }
      (* move *( *b).0 out *)
      iApply (type_let with "[]").
      { apply (type_move_oplace_instr _ _ _ vb 3 (PFst (POwn 1 PHole) (OfTy opt)) int);
          [done|apply int_stack_okay|done]. }
      { solve_typing. } { reflexivity. }
      iIntros (vv). simpl_subst.
      (* ( *b).1 = Some(5) *)
      iApply type_int. iIntros (v5). simpl_subst.
      iApply type_seq.
      { apply (type_sum_assign_oplace_instr _ _ _ vb v5 3
          (PSnd (OwnPtrLty 1 (OfTy (↯ 1))) PHole) +[(); int]%T 1%fin (const (const True)));
          [done|apply resolve_just]. }
      { simpl. solve_typing. } { reflexivity. }
      (* drop b *)
      iApply type_seq.
      { apply (type_drop_oplace_instr _ _ _ vb 3 3
          (ProdLty (OwnPtrLty 1 (OfTy (↯ 1))) (OfTy opt)));
          [done|done|done|].
        apply lty_resolve_prod; [apply lty_resolve_own|];
          apply lty_resolve_ofty; [apply uninit_resolve|apply resolve_just]. }
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
    intros post [[lx [l [[lb v0] w]]] []] mask π Hspec. rewrite /trans_upper /trans_tail /=.
    intros _ _ _ _ _ _ l0 _ z ->. apply Hspec.
  Qed.
End place_resolve.

Print Assumptions get_last_type.
Print Assumptions drop_local_type.
