From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type function product programs own cont uninit int
  uniq_bor shr_bor borrow place_own place_shr.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

(** (The kernel check of [get_mid_shr_type] used to take about 14 minutes, because of
    the [solve_typing] proofs of membership in [fp_E …]; see [list_spine_norm] in
    [typing/base.v].) *)

Section place_shr_mid.
  Context `{!typeG Σ}.

  (*
  Reading a field of a field below a shared reference:

  ```
  fn get_mid_shr<'a>(r: &'a ((i32, i32), i32)) -> i32 { ( *r).0.1 }
  ```

  with the specification `ensures result == r.0.1`. A shared reference to the subplace
  `( *r).0.1` is taken by [tctx_shr_place] (the path [PFst (PSnd _ PHole) _]), and read
  ([read_shr]).
  *)

  Definition get_mid_shr : val :=
    fn: ["x"] :=
      let: "r" := !"x" in
      delete [ #1; "x"];;
      let: "v" := !("r" +ₗ #1) in       (* ( *r).0.1 *)
      let: "ret" := new [ #1] in
      "ret" <- "v";;
      return: ["ret"].

  Definition get_mid_shr_spec : fn_spec [at_clocₛ ((Zₛ * Zₛ) * Zₛ)] Zₛ () :=
    λ _ post '-[(_, (_, ((_, b), _)))], λ mask π, ∀ (lr: loc), post (lr, b) mask π.

  Lemma get_mid_shr_type :
    typed_val get_mid_shr
      ((fn<α>(∅; &shr{α} ((int * int) * int)) → int) get_mid_shr_spec)
      (get_mid_shr, ()).
  Proof.
    unfold get_mid_shr. unlock.
    opose proof (@type_fn _ _ _ [at_clocₛ ((Zₛ * Zₛ) * Zₛ)] Zₛ () ()
      (λ α, FP ∅ +[&shr{α} ((int * int) * int)]%T int%T AtomicClosed)
      get_mid_shr_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros α ϝ k wl. destruct wl as [vx []]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply (type_let with "[]").
      { eapply (type_deref_instr (own_ptr 1 (&shr{α} ((int * int) * int)))
          (&shr{α} ((int * int) * int))).
        - apply shr_stack_okay.
        - done.
        - apply (read_own_move (&shr{α} ((int * int) * int))). }
      { apply tctx_extract_elt_here_exact. }
      { reflexivity. }
      iIntros (vr). simpl_subst.
      iApply type_delete. { solve_typing. } { done. } { done. }
      (* &( *r).0.1 *)
      iApply typed_body_tctx_incl.
      { apply (tctx_shr_place _ _ vr α (PFst (PSnd (OfTy int) PHole) (OfTy int)) int). done. }
      iApply (type_let with "[]").
      { eapply (type_deref_instr (𝔅 := Zₛ) _ int); [apply int_stack_okay|done|].
        apply (read_shr int α); [apply int_copy|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iIntros (vv). simpl_subst.
      iApply (type_letalloc_1 int). { solve_typing. } 2: { done. }
      { eapply (_: ∀ x, x ≡ x). } iIntros (vret). simpl_subst.
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lx [l [[a b] c]]] []] mask π. simpl.
    intros Hspec. rewrite /trans_upper /trans_tail /=.
    intros z _ z0 _ l0. apply Hspec.
    Unshelve. by intros ?.
  Qed.
End place_shr_mid.

Print Assumptions get_mid_shr_type.
