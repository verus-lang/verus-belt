From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type function product programs own cont uninit int
  uniq_bor shr_bor borrow vplace place_shr place_resolve place_puniq.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

Section place_shr_resolve.
  Context `{!typeG Σ}.

  (*
  Returning a shared borrow of a field of a mutable reference:

  ```
  fn first_ref<'a>(x: &'a mut (i32, i32)) -> &'a i32 { &x.0 }
  ```

  with the specification `ensures *result == old(x).0, fin(x) == old(x)`. The value of `x`
  becomes a place rooted at it ([type_uniq_to_vplace_instr]) and its referent is unfolded;
  field 0 is borrowed shared at `'a ⊓ 'a` ([type_share_vplace_deep_instr]);
  `x` is resolved while field 0 is still shared-blocked ([type_resolve_vplace_uniq_instr]:
  the shared lifetime is alive, so the prophecy tokens of the value of the field are
  available from its sharing predicate, and the field contributes its current value).
  *)

  Definition first_ref : val :=
    fn: ["x"] :=
      let: "b" := !"x" in
      delete [ #1; "x"];;
      Skip;; ReBor;;                       (* b as a place, unfold *b *)
      let: "r" := Share;; "b" in          (* &( *b).0 *)
      (Skip;; Skip;; Skip;; #☠);;          (* resolve b *)
      let: "ret" := new [ #1] in
      "ret" <- "r";;
      return: ["ret"].

  Definition first_ref_spec : fn_spec [uniq_borₛ (Zₛ * Zₛ)] (at_clocₛ Zₛ) () :=
    λ _ post '-[(_, m)], λ mask π, ∀ (lr: loc) (r: ~~ (at_clocₛ Zₛ)),
      r.2 = (uniq_bor_current (𝔄:=Zₛ * Zₛ) m).1 →
      uniq_bor_future (𝔄:=Zₛ * Zₛ) m π = uniq_bor_current (𝔄:=Zₛ * Zₛ) m →
      post (lr, r) mask π.

  Lemma first_ref_type :
    typed_val first_ref ((fn<α>(∅; &uniq{α} (int * int)) → &shr{α} int) first_ref_spec)
      (first_ref, ()).
  Proof.
    unfold first_ref. unlock.
    opose proof (@type_fn _ _ _ [uniq_borₛ (Zₛ * Zₛ)] (at_clocₛ Zₛ) () ()
      (λ α, FP ∅ +[&uniq{α} (int * int)]%T (&shr{α} int)%T AtomicClosed)
      first_ref_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros α ϝ k wl. destruct wl as [vx []]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply (type_let with "[]").
      { eapply (type_deref_instr (own_ptr 1 (&uniq{α} (int * int))) (&uniq{α} (int * int))).
        - apply uniq_stack_okay.
        - done.
        - apply (read_own_move (&uniq{α} (int * int))). }
      { apply tctx_extract_elt_here_exact. }
      { reflexivity. }
      iIntros (vb). simpl_subst.
      iApply type_delete. { solve_typing. } { done. } { done. }
      iApply type_seq. { apply (type_uniq_to_vplace_instr _ _ _ vb α (int * int)). }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_unfold_vplace_prod_instr _ _ _ vb (PUniq α PHole) int int). simpl. solve_typing. }
      { solve_typing. } { reflexivity. }
      (* &( *b).0, at α ⊓ α *)
      iApply (type_let with "[]").
      { apply (type_share_vplace_deep_instr _ _ _ vb α (PUniq α (PFst PHole (OfTy int))) int);
          [done|solve_typing|simpl; solve_typing]. }
      { solve_typing. } { reflexivity. }
      iIntros (vr). simpl_subst.
      (* resolve b, with field 0 shared *)
      iApply type_seq.
      { apply (type_resolve_vplace_uniq_instr _ _ _ vb α (ProdLty (ShrBlocked int (α ⊓ α)) (OfTy int)));
          [solve_typing|done|done|]. intros ? ->%elem_of_list_singleton. solve_typing. }
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
    destruct m as [[[[[l [x1 x2]] ξi] d] g] idx]. simpl.
    intros Hspec. rewrite /trans_upper /trans_tail /=.
    intros z _ Hres l0 _ z0 ->. by apply Hspec.
  Qed.
End place_shr_resolve.

Print Assumptions first_ref_type.
