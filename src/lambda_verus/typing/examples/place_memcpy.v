From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type function product programs own cont uninit int
  uniq_bor borrow vplace place_own place_resolve place_memcpy place_puniq place_deep.
From lrust.lang Require Import lang notation memcpy new_delete.
Set Default Proof Using "Type".

Section place_memcpy.
  Context `{!typeG Σ}.

  (*
  Moving a pair out of a field of a local, and moving another pair in:

  ```
  fn replace_first(mut x: ((i32, i32), i32), y: (i32, i32)) -> (i32, i32) {
      let r = x.0;   // move out of x.0 (two cells): x.0 is uninitialized
      x.0 = y;       // move y into x.0
      r
  }
  ```

  with the specification `ensures result == old(x).0`. The argument `x` is an owned
  place, unfolded into `ProdLty (OfTy (int * int)) (OfTy int)`; `x.0` is moved out into
  the new local `r` ([type_memcpy_from_oplace_instr], `r <-{2} !x`), which leaves the
  leaf `OfTy (↯ 2)`, and `y` is moved into it ([type_memcpy_oplace_instr],
  `x <-{2} !y`, from [read_own_move]); the place is folded back and freed.
  *)

  Definition replace_first : val :=
    fn: ["x"; "y"] :=
      let: "r" := new [ #2] in
      "r" <-{2} !"x";;                    (* r = x.0 *)
      "x" <-{2} !"y";;                    (* x.0 = y *)
      delete [ #3; "x"];;
      delete [ #2; "y"];;
      return: ["r"].

  Definition replace_first_spec :
      fn_spec [((Zₛ * Zₛ) * Zₛ)%ST; (Zₛ * Zₛ)%ST] (Zₛ * Zₛ) () :=
    λ _ post '-[(_, x); _], λ mask π, ∀ (lr: loc), post (lr, x.1) mask π.

  Lemma replace_first_type :
    typed_val replace_first
      ((fn(∅; (int * int) * int, int * int) → int * int) replace_first_spec)
      (replace_first, ()).
  Proof.
    unfold replace_first. unlock.
    opose proof (@type_fn _ _ _ [((Zₛ * Zₛ) * Zₛ)%ST; (Zₛ * Zₛ)%ST] (Zₛ * Zₛ) () ()
      (λ _: (), FP ∅ +[((int * int) * int)%T; (int * int)%T] (int * int)%T AtomicClosed)
      replace_first_spec _ [BNamed "x"; BNamed "y"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros c ϝ k wl. destruct wl as [vx [vy []]]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      (* x as an owned place, unfolded *)
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_r +[_] +[_]).
        eapply tctx_incl_trans; [apply tctx_own_to_oplace|].
        apply (tctx_unfold_oplace_prod _ _ _ _ PHole (int * int) int). }
      iApply (type_new 2). { lia. } iIntros (vr). simpl_subst.
      (* r = x.0 *)
      iApply type_seq.
      { apply (type_memcpy_from_oplace_instr _ _ _ vr vx 3 (PFst PHole (OfTy int)) (int * int)
          (own_ptr 2 (↯ 2)) (own_ptr 2 (int * int)) (↯ 2)); [by apply write_own| |done|done].
        apply (resolve'_just _ _ _ (const True)). apply resolve_just. }
      { solve_typing. } { reflexivity. }
      (* x.0 = y *)
      iApply type_seq.
      { apply (type_memcpy_oplace_instr _ _ _ vx vy 3 (PFst PHole (OfTy int)) (↯ 2)
          (own_ptr 2 (int * int)) (own_ptr 2 (↯ (ty_size (int * int)))) (int * int));
          [done|apply uninit_resolve|apply (read_own_move (int * int))|done|done]. }
      { solve_typing. } { reflexivity. }
      (* fold x back, free x and y *)
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_r +[_] +[_]).
        eapply tctx_incl_trans; [apply (tctx_fold_oplace_prod _ _ _ _ PHole (int * int) int)|].
        apply tctx_oplace_to_own. }
      iApply type_delete. { solve_typing. } { done. } { done. }
      iApply type_delete. { solve_typing. } { done. } { done. }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lx [[a1 a2] b]] [[ly y] []]] mask π Hspec.
    rewrite /trans_upper /trans_tail /=.
    intros l _ zw _ -> _ zr _. apply Hspec.
  Qed.

  (*
  Copying a pair out of a field behind a mutable reference, and assigning to it:

  ```
  fn set_first_pair<'a>(x: &'a mut ((i32, i32), i32), y: (i32, i32)) -> (i32, i32) {
      let c = x.0;   // copy out of x.0 (two cells)
      x.0 = y;       // assign x.0 (two cells)
      c
  }
  ```

  with the specification `ensures result == old( *x).0, fin(x) == (y, old( *x).1)`. The
  value of `x` becomes a place rooted at it ([type_uniq_to_vplace_instr]), whose referent is
  unfolded into `ProdLty (OfTy (int * int)) (OfTy int)`; `x.0` is copied into the new local
  `c` ([type_memcpy_copy_from_vplace_deep_instr]) and assigned
  ([type_memcpy_vplace_deep_instr]); `x` is resolved ([type_resolve_vplace_uniq_instr]).
  *)

  Definition set_first_pair : val :=
    fn: ["x"; "y"] :=
      let: "b" := !"x" in
      delete [ #1; "x"];;
      Skip;; ReBor;;                      (* b as a place, unfold *b *)
      let: "c" := new [ #2] in
      "c" <-{2} !"b";;                    (* c = x.0 *)
      "b" <-{2} !"y";;                    (* x.0 = y *)
      (Skip;; Skip;; Skip;; #☠);;         (* resolve b *)
      delete [ #2; "y"];;
      return: ["c"].

  Definition set_first_pair_spec :
      fn_spec [uniq_borₛ ((Zₛ * Zₛ) * Zₛ); (Zₛ * Zₛ)%ST] (Zₛ * Zₛ) () :=
    λ _ post '-[(_, m); (_, y)], λ mask π, ∀ (lr: loc),
      uniq_bor_future (𝔄:=(Zₛ * Zₛ) * Zₛ) m π =
        (y, (uniq_bor_current (𝔄:=(Zₛ * Zₛ) * Zₛ) m).2) →
      post (lr, (uniq_bor_current (𝔄:=(Zₛ * Zₛ) * Zₛ) m).1) mask π.

  Lemma set_first_pair_type :
    typed_val set_first_pair
      ((fn<α>(∅; &uniq{α} ((int * int) * int), int * int) → int * int) set_first_pair_spec)
      (set_first_pair, ()).
  Proof.
    unfold set_first_pair. unlock.
    opose proof (@type_fn _ _ _ [uniq_borₛ ((Zₛ * Zₛ) * Zₛ); (Zₛ * Zₛ)%ST] (Zₛ * Zₛ) () ()
      (λ α, FP ∅ +[&uniq{α} ((int * int) * int); (int * int)%T]%T (int * int)%T AtomicClosed)
      set_first_pair_spec _ [BNamed "x"; BNamed "y"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros α ϝ k wl. destruct wl as [vx [vy []]]. simpl_subst.
    (* [α] is alive (proved once). *)
    have Alv: lctx_lft_alive
      (fp_E (FP ∅ +[&uniq{α} ((int * int) * int); (int * int)%T]%T (int * int) AtomicClosed) ϝ)
      [ϝ ⊑ₗ []] α.
    { eapply lctx_lft_alive_external; [rewrite /fp_E /=; by left|solve_typing]. }
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
      (* b as a place rooted at its value, and its referent unfolded *)
      iApply type_seq. { apply (type_uniq_to_vplace_instr _ _ _ vb α ((int * int) * int)). }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_unfold_vplace_prod_instr _ _ _ vb (PUniq α PHole) (int * int) int).
        simpl. solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply (type_new 2). { lia. } iIntros (vc). simpl_subst.
      (* c = x.0 *)
      iApply type_seq.
      { apply (type_memcpy_copy_from_vplace_deep_instr _ _ _ vc vb
          (PUniq α (PFst PHole (OfTy int))) (int * int)
          (own_ptr 2 (↯ 2)) (own_ptr 2 (int * int)) (↯ 2));
          [apply _|by apply write_own| |done|simpl; solve_typing].
        apply (resolve'_just _ _ _ (const True)). apply resolve_just. }
      { solve_typing. } { reflexivity. }
      (* x.0 = y *)
      iApply type_seq.
      { apply (type_memcpy_vplace_deep_instr _ _ _ vb vy (PUniq α (PFst PHole (OfTy int)))
          (int * int) (own_ptr 2 (int * int)) (own_ptr 2 (↯ (ty_size (int * int)))));
          [apply resolve_just|apply (read_own_move (int * int))|done|simpl; solve_typing]. }
      { solve_typing. } { reflexivity. }
      (* resolve b *)
      iApply type_seq.
      { apply (type_resolve_vplace_uniq_instr _ _ _ vb α (ProdLty (OfTy (int * int)) (OfTy int)));
          [done|done|done|set_solver]. }
      { solve_typing. } { reflexivity. }
      iApply type_delete. { solve_typing. } { done. } { done. }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lx m] [[ly y] []]] mask π. simpl.
    destruct m as [[[[[l [[x1 x2] x3]] ξi] d] g] idx]. simpl.
    intros Hspec. rewrite /trans_upper /trans_tail /=.
    intros z _ l0 _ zw -> _ zr _ Hres. apply Hspec.
    rewrite !uniq_bor_future_eq in Hres |- *.
    rewrite (uniq_prvar_app_irrel (𝔄:=(Zₛ * Zₛ) * Zₛ) _ (y, x3)) Hres. by destruct y.
  Qed.

  (*
  Moving a pair out of a box inside a box:

  ```
  fn take_inner(b: Box<(Box<(i32, i32)>, i32)>) -> (i32, i32) {
      let r = *b.0;   // move out of the inner box (two cells): its contents are uninitialized
      r               // b is dropped: the inner box and b are freed
  }
  ```

  with the specification `ensures result == *old(b).0`. The pointee of `b` is an owned
  place, unfolded into `ProdLty (OwnPtrLty 2 (OfTy (int * int))) (OfTy int)`; the
  contents of the inner box are moved out ([type_memcpy_from_oplace_instr] at the path
  `PFst (POwn 2 PHole) _`, address `!b`), then the place is dropped
  ([type_drop_oplace_instr]).
  *)

  Notation take_innerₛ := (at_locₛ (at_locₛ (Zₛ * Zₛ) * Zₛ))%ST.

  Definition take_inner : val :=
    fn: ["x"] :=
      let: "b" := !"x" in
      delete [ #1; "x"];;
      let: "r" := new [ #2] in
      "r" <-{2} !(!"b");;                   (* r = *( *b).0 *)
      (((#☠;; delete [ #2; !"b"]);; #☠);;   (* drop b: free the inner box, *)
       delete [ #2; "b"]);;                  (* then b *)
      return: ["r"].

  Definition take_inner_spec : fn_spec [take_innerₛ] (Zₛ * Zₛ) () :=
    λ _ post '-[(_, (l, ((lb, v0), w)))], λ mask π, ∀ (lr: loc), post (lr, v0) mask π.

  Lemma take_inner_type :
    typed_val take_inner ((fn(∅; box (box (int * int) * int)) → int * int) take_inner_spec)
      (take_inner, ()).
  Proof.
    unfold take_inner. unlock.
    opose proof (@type_fn _ _ _ [take_innerₛ] (Zₛ * Zₛ) () ()
      (λ _: (), FP ∅ +[box (box (int * int) * int)] (int * int) AtomicClosed)
      take_inner_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros c ϝ k wl. destruct wl as [vx []]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply (type_let with "[]").
      { eapply (type_deref_instr (own_ptr 1 (box (box (int * int) * int)))
          (box (box (int * int) * int))).
        - apply own_stack_okay.
        - done.
        - apply (read_own_move (box (box (int * int) * int))). }
      { apply tctx_extract_elt_here_exact. }
      { reflexivity. }
      iIntros (vb). simpl_subst.
      iApply type_delete. { solve_typing. } { done. } { done. }
      (* the pointee of b as an owned place; unfold the pair and the inner box *)
      iApply typed_body_tctx_incl.
      { eapply tctx_incl_trans; [apply tctx_own_to_oplace|].
        eapply tctx_incl_trans;
          [apply (tctx_unfold_oplace_prod _ _ _ _ PHole (box (int * int)) int)|].
        apply (tctx_unfold_oplace_own _ _ _ _ (PFst PHole (OfTy int)) 2 (int * int)). done. }
      iApply (type_new 2). { lia. } iIntros (vr). simpl_subst.
      (* r = *( *b).0 *)
      iApply type_seq.
      { apply (type_memcpy_from_oplace_instr _ _ _ vr vb 2 (PFst (POwn 2 PHole) (OfTy int))
          (int * int) (own_ptr 2 (↯ 2)) (own_ptr 2 (int * int)) (↯ 2));
          [by apply write_own| |done|done].
        apply (resolve'_just _ _ _ (const True)). apply resolve_just. }
      { solve_typing. } { reflexivity. }
      (* drop b *)
      iApply type_seq.
      { apply (type_drop_oplace_instr _ _ _ vb 2 2
          (ProdLty (OwnPtrLty 2 (OfTy (↯ 2))) (OfTy int)));
          [done|done|done|].
        apply lty_resolve_prod; [apply lty_resolve_own|];
          apply lty_resolve_ofty; [apply uninit_resolve|apply resolve_just]. }
      { solve_typing. } { reflexivity. }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lx [l [[lb [v1 v2]] w]]] []] mask π Hspec.
    rewrite /trans_upper /trans_tail /=.
    intros _ _ l0 _ zw _ -> _. apply Hspec.
  Qed.
End place_memcpy.

Print Assumptions replace_first_type.
Print Assumptions set_first_pair_type.
Print Assumptions take_inner_type.
