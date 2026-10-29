From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type function product programs own cont uninit int
  uniq_bor shr_bor borrow place_own place_resolve place_puniq place_pshr place_res
  place_res_rslv place_res_ops.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

Section place_res_fold.
  Context `{!typeG Σ}.

  (*
  Resolving a unique borrow with a compound referent, and folding it to a shared
  reference:

  ```
  fn res_fold<'a>(x: &'a mut (i32, i32)) -> &'a (i32, i32) { /* resolve x */ &*x }
  ```

  with the specification `ensures result == cur(x), fin(x) == cur(x)`. The argument slot
  is an owned place; `*x` and `*x` as a pair are unfolded; `x` is resolved
  ([type_resolve_oplace_res_instr], [lty_res_uniq_cpd]) to
  [ResUniqLty (ProdLty (OfTy int) (OfTy int)) 'a], whose referent is viewed at `'a`; the
  view is folded ([tctx_fold_oplace_res_uniq], combining the guards of the cells of the
  two fields) to the shared reference [ShrLty (OfTy (int * int)) 'a], which is folded to a
  leaf [OfTy (&shr{'a} (int * int))] ([type_fold_oplace_shr_instr]), read and returned;
  the slot is dropped.
  *)

  Definition res_fold : val :=
    fn: ["x"] :=
      ReBor;; ReBor;;                               (* unfold *x, *x as a pair *)
      (Skip;; #☠);;                                  (* resolve x *)
      ReBor;;                                       (* fold the shared reference *)
      let: "r" := !"x" in
      (#☠;; delete [ #1; "x"]);;                     (* drop x *)
      let: "ret" := new [ #1] in
      "ret" <- "r";;
      return: ["ret"].

  Definition res_fold_spec : fn_spec [uniq_borₛ (Zₛ * Zₛ)] (at_clocₛ (Zₛ * Zₛ)) () :=
    λ _ post '-[(_, m)], λ mask π,
      uniq_bor_future (𝔄:=Zₛ * Zₛ) m π = uniq_bor_current (𝔄:=Zₛ * Zₛ) m →
      ∀ (lr: loc), post (lr, (uniq_bor_loc (𝔄:=Zₛ * Zₛ) m, uniq_bor_current (𝔄:=Zₛ * Zₛ) m)) mask π.

  Lemma res_fold_type :
    typed_val res_fold
      ((fn<α>(∅; &uniq{α} (int * int)) → &shr{α} (int * int)) res_fold_spec)
      (res_fold, ()).
  Proof.
    unfold res_fold. unlock.
    opose proof (@type_fn _ _ _ [uniq_borₛ (Zₛ * Zₛ)] (at_clocₛ (Zₛ * Zₛ)) () ()
      (λ α, FP ∅ +[&uniq{α} (int * int)]%T (&shr{α} (int * int))%T AtomicClosed)
      res_fold_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros α ϝ k wl. destruct wl as [vx []]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply typed_body_tctx_incl; [apply tctx_own_to_oplace|].
      (* unfold *x, *x as a pair *)
      iApply type_seq.
      { apply (type_unfold_oplace_uniq_instr _ _ _ vx 1 PHole (int * int) α). solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_unfold_oplace_prod_instr _ _ _ vx 1 (PUniq α PHole) int int).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      (* resolve x *)
      iApply type_seq.
      { apply (type_resolve_oplace_res_instr _ _ _ vx 1
          (UniqLty (ProdLty (OfTy int) (OfTy int)) α)
          (ResUniqLty (ProdLty (OfTy int) (OfTy int)) α) 1).
        apply lty_res_uniq_cpd; [solve_typing|solve_typing|done|done]. }
      { solve_typing. } { reflexivity. }
      (* fold the view to a shared reference, then to a leaf *)
      iApply typed_body_tctx_incl.
      { apply (tctx_fold_oplace_res_uniq _ _ vx 1 PHole α (ProdLty (OfTy int) (OfTy int)));
          done. }
      iApply type_seq.
      { apply (type_fold_oplace_shr_instr _ _ _ vx 1 PHole α (int * int)). solve_typing. }
      { solve_typing. } { reflexivity. }
      (* read it *)
      iApply (type_let with "[]").
      { apply (type_read_oplace_instr _ _ _ vx 1 PHole (&shr{α} (int * int))); [done|apply _]. }
      { solve_typing. } { reflexivity. }
      iIntros (vr). simpl_subst.
      (* drop x *)
      iApply type_seq.
      { apply (type_drop_oplace_res_instr _ _ _ vx 1 1 (OfTy (&shr{α} (int * int))));
          [done|done|done]. }
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
    intros Hspec. rewrite /trans_upper /trans_tail /=.
    intros Hres l0 _ z ->. apply Hspec.
    destruct m as [[[[[l' [c1 c2]] ξi] d] g] idx]. simpl in *.
    rewrite uniq_bor_future_eq. exact Hres.
  Qed.
End place_res_fold.

Print Assumptions res_fold_type.
