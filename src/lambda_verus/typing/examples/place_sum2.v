From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type function product programs own cont uninit int sum type_sum
  uniq_bor borrow place place_own place_sum place_resolve.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

Section place_sum2.
  Context `{!typeG Σ}.

  Notation opt := (Σ! +[(); int])%T.
  Notation optₛ := (Σ! [unitₛ; Zₛ])%ST.

  (*
  Assigning a unit variant to a field of a local:

  ```
  fn clear(mut x: (Option<i32>, i32)) -> (Option<i32>, i32) { x.0 = None; x }
  ```

  with the specification `ensures result.0 == None, result.1 == old(x).1`. The argument is
  an owned place, unfolded into a pair; `x.0` gets the variant `None`
  ([type_sum_unit_oplace_instr]: only the tag is written).
  *)

  Definition clear : val :=
    fn: ["x"] :=
      "x" <-{Σ 0} ();;
      return: ["x"].

  Definition clear_spec : fn_spec [(optₛ * Zₛ)%ST] (optₛ * Zₛ) () :=
    λ _ post '-[(_, x)], λ mask π, ∀ (lr: loc) pad,
      post (lr, ((pinj (Xl:=[unitₛ; Zₛ]) 0%fin (), pad), x.2)) mask π.

  Lemma clear_type :
    typed_val clear ((fn(∅; opt * int) → opt * int) clear_spec) (clear, ()).
  Proof.
    unfold clear. unlock.
    opose proof (@type_fn _ _ _ [(optₛ * Zₛ)%ST] (optₛ * Zₛ) () ()
      (λ _: (), FP ∅ +[(opt * int)%T] (opt * int)%T AtomicClosed)
      clear_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros c ϝ k wl. destruct wl as [vx []]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply typed_body_tctx_incl.
      { eapply tctx_incl_trans; [apply tctx_own_to_oplace|].
        apply (tctx_unfold_oplace_prod _ _ _ _ PHole opt int). }
      iApply type_seq.
      { apply (type_sum_unit_oplace_instr _ _ _ vx 3 (PFst PHole (OfTy int)) +[(); int]%T 0%fin
          idₛ (const (const True))); [apply subtype_refl|apply resolve_just]. }
      { solve_typing. } { reflexivity. }
      iApply typed_body_tctx_incl.
      { eapply tctx_incl_trans; [apply (tctx_fold_oplace_prod _ _ _ _ PHole opt int)|].
        apply tctx_oplace_to_own. }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lx [s b]] []] mask π Hspec. rewrite /trans_upper /trans_tail /=.
    intros _ pad. apply (Hspec lx pad).
  Qed.

  (*
  Assigning a variant to a field behind a mutable reference:

  ```
  fn set_some_fst<'a>(x: &'a mut (Option<i32>, i32), v: i32) -> i32 { x.0 = Some(v); v }
  ```

  with the specification `ensures result == v, fin(x).0 == Some(v),
  fin(x).1 == old(x).1`. The referent of `x` is unfolded into a pair; `x.0` gets the
  variant `Some(v)` in place ([type_sum_assign_place_instr]); `x` is resolved.
  *)

  Definition set_some_fst : val :=
    fn: ["x"; "v"] :=
      let: "b" := !"x" in
      delete [ #1; "x"];;
      let: "w" := !"v" in
      let: "w2" := !"v" in
      delete [ #1; "v"];;
      "b" <-{Σ 1} "w";;                 (* x.0 = Some(v) *)
      (Skip;; Skip;; Skip;; #☠);;        (* resolve b *)
      let: "r" := new [ #1] in
      "r" <- "w2";;
      return: ["r"].

  Definition set_some_fst_spec : fn_spec [uniq_borₛ (optₛ * Zₛ); Zₛ] Zₛ () :=
    λ _ post '-[(_, m); (_, v)], λ mask π, ∀ (lr: loc),
      (∃ pad, uniq_bor_future (𝔄:=optₛ * Zₛ) m π =
        ((pinj (Xl:=[unitₛ; Zₛ]) 1%fin v, pad), (uniq_bor_current (𝔄:=optₛ * Zₛ) m).2)) →
      post (lr, v) mask π.

  Lemma set_some_fst_type :
    typed_val set_some_fst
      ((fn<α>(∅; &uniq{α} (opt * int), int) → int) set_some_fst_spec) (set_some_fst, ()).
  Proof.
    unfold set_some_fst. unlock.
    opose proof (@type_fn _ _ _ [uniq_borₛ (optₛ * Zₛ); Zₛ] Zₛ () ()
      (λ α, FP ∅ +[&uniq{α} (opt * int); int]%T int AtomicClosed)
      set_some_fst_spec _ [BNamed "x"; BNamed "v"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros α ϝ k wl. destruct wl as [vx [vv []]]. simpl_subst.
    (* [α] is alive (proved once: the proof by [solve_typing] is slow to check). *)
    have Alv: lctx_lft_alive
      (fp_E (FP ∅ +[&uniq{α} (opt * int); int]%T int AtomicClosed) ϝ) [ϝ ⊑ₗ []] α.
    { eapply lctx_lft_alive_external; [rewrite /fp_E /=; by left|solve_typing]. }
    iApply (typed_body_impl with "[]"); last first. {
      iApply (type_let with "[]").
      { eapply (type_deref_instr (own_ptr 1 (&uniq{α} (opt * int))) (&uniq{α} (opt * int))).
        - apply uniq_stack_okay.
        - done.
        - apply (read_own_move (&uniq{α} (opt * int))). }
      { apply tctx_extract_elt_here_exact. }
      { reflexivity. }
      iIntros (vb). simpl_subst.
      iApply type_delete. { solve_typing. } { done. } { done. }
      (* unfold the referent of b *)
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_r +[_] +[_]).
        apply (tctx_unfold_uniq_prod _ _ vb α opt int). done. }
      iApply (type_let with "[]").
      { eapply (type_deref_instr (own_ptr 1 int) int).
        - apply int_stack_okay.
        - done.
        - apply (read_own_copy int). apply _. }
      { solve_typing. } { reflexivity. }
      iIntros (vw). simpl_subst.
      iApply (type_let with "[]").
      { eapply (type_deref_instr (own_ptr 1 int) int).
        - apply int_stack_okay.
        - done.
        - apply (read_own_copy int). apply _. }
      { solve_typing. } { reflexivity. }
      iIntros (vw2). simpl_subst.
      iApply type_delete. { solve_typing. } { done. } { done. }
      (* x.0 = Some(v) *)
      iApply type_seq.
      { apply (type_sum_assign_place_instr _ _ _ vb vw α (PFst PHole (OfTy int)) +[(); int]%T
          1%fin (const (const True))); [done|done|done|apply resolve_just]. }
      { solve_typing. } { reflexivity. }
      (* resolve b *)
      iApply type_seq.
      { apply (type_resolve_place_instr _ _ _ vb α (ProdLty (OfTy opt) (OfTy int)));
          [done|done|done|set_solver]. }
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
    intros post [[lx m] [[lv v] []]] mask π. simpl.
    destruct m as [[[[[l [s b]] ξi] d] g] idx]. simpl.
    intros Hspec. rewrite /trans_upper /trans_tail /=.
    intros z _ z0 <- z1 <- _ pad x' _ Hc Hf _ Hres l0 _ z2 ->. apply Hspec.
    exists pad. rewrite -Hf Hres.
    destruct x' as [[[[[[l' w] ξi'] d'] g'] idx'] ζm']. simpl in Hc. subst w.
    by rewrite /place_cur /place_rfn /=.
  Qed.
End place_sum2.

Print Assumptions clear_type.
Print Assumptions set_some_fst_type.
