From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type function product programs own cont uninit int
  uniq_bor shr_bor borrow place_own place_resolve place_puniq place_pshr place_res
  place_res_rslv place_res_ops place_res_copy.
From lrust.lang Require Import lang notation memcpy new_delete.
Set Default Proof Using "Type".

Section place_res_copy.
  Context `{!typeG Σ}.

  (*
  Copying a pair out of a resolved nested unique borrow:

  ```
  fn res_copy<'a, 'b>(x: &'a mut &'b mut ((i32, i32), i32)) -> (i32, i32) {
      /* resolve x */
      ( **x).0                    // x is dropped
  }
  ```

  with the specification `ensures result == ( **x).0, fin(x) == cur(x)` (for the outer
  borrow). The argument slot is an owned place; `*x`, `**x` and `**x` as a pair are
  unfolded; `x` is resolved ([lty_res_uniq_cpd]; its referent is viewed at `'a`, the
  nested borrow at `'a ⊓ 'b`); the pair `( **x).0` (two cells) is copied out of the view
  ([type_memcpy_copy_from_oplace_res_instr], [K = PHole],
  [K2 = PUniq 'b (PFst PHole _)]); the slot is dropped.
  *)

  Definition res_copy : val :=
    fn: ["x"] :=
      ReBor;; ReBor;; ReBor;;                       (* unfold *x, **x, **x as a pair *)
      (Skip;; #☠);;                                  (* resolve x *)
      let: "r" := new [ #2] in
      (Skip;; "r" <-{2} !(!(!"x")));;               (* r = ( **x).0 *)
      (#☠;; delete [ #1; "x"]);;                     (* drop x *)
      return: ["r"].

  Notation pairₛ := ((Zₛ * Zₛ) * Zₛ)%ST.

  Definition res_copy_spec : fn_spec [uniq_borₛ (uniq_borₛ pairₛ)] (Zₛ * Zₛ) () :=
    λ _ post '-[(_, m)], λ mask π,
      let b := uniq_bor_current (𝔄:=uniq_borₛ pairₛ) m in
      uniq_bor_future (𝔄:=uniq_borₛ pairₛ) m π = vπ (𝔄:=uniq_borₛ pairₛ) b π →
      ∀ (lr: loc), post (lr, (uniq_bor_current (𝔄:=pairₛ) b).1) mask π.

  Lemma res_copy_type :
    typed_val res_copy
      ((fn<(α, β)>(∅; &uniq{α} (&uniq{β} ((int * int) * int))) → int * int) res_copy_spec)
      (res_copy, ()).
  Proof.
    unfold res_copy. unlock.
    opose proof (@type_fn _ _ _ [uniq_borₛ (uniq_borₛ pairₛ)] (Zₛ * Zₛ) () ()
      (λ '(α, β), FP ∅ +[&uniq{α} (&uniq{β} ((int * int) * int))]%T (int * int)%T AtomicClosed)
      res_copy_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros [α β] ϝ k wl. destruct wl as [vx []]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply typed_body_tctx_incl; [apply tctx_own_to_oplace|].
      (* unfold *x, **x, **x as a pair *)
      iApply type_seq.
      { apply (type_unfold_oplace_uniq_instr _ _ _ vx 1 PHole (&uniq{β} ((int * int) * int)) α).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_unfold_oplace_uniq_instr _ _ _ vx 1 (PUniq α PHole) ((int * int) * int) β).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_unfold_oplace_prod_instr _ _ _ vx 1 (PUniq α (PUniq β PHole)) (int * int) int).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      (* resolve x *)
      iApply type_seq.
      { apply (type_resolve_oplace_res_instr _ _ _ vx 1
          (UniqLty (UniqLty (ProdLty (OfTy (int * int)) (OfTy int)) β) α)
          (ResUniqLty (UniqLty (ProdLty (OfTy (int * int)) (OfTy int)) β) α) 1).
        apply lty_res_uniq_cpd; [solve_typing|solve_typing|done|done]. }
      { solve_typing. } { reflexivity. }
      iApply (type_new 2). { lia. } iIntros (vr). simpl_subst.
      (* r = ( **x).0 *)
      iApply type_seq.
      { apply (type_memcpy_copy_from_oplace_res_instr _ _ _ vr vx 1 PHole α
          (PUniq β (PFst PHole (OfTy int))) (OfTy (int * int)) (int * int) static
          (own_ptr 2 (↯ 2)) (own_ptr 2 (int * int)) (↯ 2));
          [constructor|apply _|by apply write_own| |done|solve_typing].
        apply (resolve'_just _ _ _ (const True)). apply resolve_just. }
      { solve_typing. } { reflexivity. }
      (* drop x *)
      iApply type_seq.
      { apply (type_drop_oplace_res_instr _ _ _ vx 1 1
          (ResUniqLty (UniqLty (ProdLty (OfTy (int * int)) (OfTy int)) β) α)); [done|done|done]. }
      { solve_typing. } { reflexivity. }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lx m] []] mask π. simpl.
    intros Hspec. rewrite /trans_upper /trans_tail /=.
    intros Hres l _ zw ->. apply Hspec.
    destruct m as [[[[[l1 [[[[[l2 [[c1 c2] c3]] ξb] db] gb] idxb]] ξa] da] ga] idxa].
    simpl in *. rewrite uniq_bor_future_eq. exact Hres.
  Qed.
End place_res_copy.

Print Assumptions res_copy_type.
