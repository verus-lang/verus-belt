From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type function product programs own cont uninit int sum type_sum
  uniq_bor shr_bor borrow place place_own place_resolve place_puniq place_pshr place_deep
  place_res place_res_rslv place_res_ops.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

Section place_res_sum_fold.
  Context `{!typeG Σ}.

  Notation opt_pair := (Σ! +[(); int * int])%T.
  Notation opt_pairₛ := (Σ! [unitₛ; (Zₛ * Zₛ)%ST])%ST.

  (*
  Resolving a unique borrow whose referent is a sum, after a case analysis, and folding
  it to a shared reference:

  ```
  fn res_opt_fold<'a>(x: &'a mut Option<(i32, i32)>) -> &'a Option<(i32, i32)> {
      match *x { None => { /* resolve x */ &*x }, Some(_) => { /* resolve x */ &*x } }
  }
  ```

  with the specification `ensures result == cur(x), fin(x) == cur(x)`. The argument slot
  is an owned place; `*x` is unfolded, and the case analysis on `*x`
  ([type_case_oplace_deep]) gives the sum place [SumLty tyl i (OfTy (tyl +!! i))] at the
  variant; in each branch, `x` is resolved ([lty_res_uniq_cpd]) and the view is folded
  ([tctx_fold_oplace_res_uniq], whose folded type is
  [Σ! (hlist_set tyl i (tyl +!! i))], i.e. [Σ! tyl], [lty_fold_sum_ofty]) to the shared
  reference [ShrLty (OfTy opt_pair) 'a], which is folded to a leaf, read and returned;
  the slot is dropped.
  *)

  Definition res_opt_fold : val :=
    fn: ["x"] :=
      ReBor;;                                       (* unfold *x *)
      case: !(!"x") of
      [ (Skip;; #☠);;                                (* None: resolve x *)
        ReBor;;                                     (* fold the shared reference *)
        let: "r" := !"x" in
        (#☠;; delete [ #1; "x"]);;                   (* drop x *)
        let: "ret" := new [ #1] in
        "ret" <- "r";;
        return: ["ret"];
        (Skip;; #☠);;                                (* Some: resolve x *)
        ReBor;;                                     (* fold the shared reference *)
        let: "r" := !"x" in
        (#☠;; delete [ #1; "x"]);;                   (* drop x *)
        let: "ret" := new [ #1] in
        "ret" <- "r";;
        return: ["ret"]].

  Definition res_opt_fold_spec : fn_spec [uniq_borₛ opt_pairₛ] (at_clocₛ opt_pairₛ) () :=
    λ _ post '-[(_, m)], λ mask π,
      uniq_bor_future (𝔄:=opt_pairₛ) m π = vπ (uniq_bor_current (𝔄:=opt_pairₛ) m) π →
      ∀ (lr: loc), post (lr, (uniq_bor_loc (𝔄:=opt_pairₛ) m, uniq_bor_current (𝔄:=opt_pairₛ) m))
        mask π.

  Lemma res_opt_fold_type :
    typed_val res_opt_fold
      ((fn<α>(∅; &uniq{α} opt_pair) → &shr{α} opt_pair) res_opt_fold_spec)
      (res_opt_fold, ()).
  Proof.
    unfold res_opt_fold. unlock.
    opose proof (@type_fn _ _ _ [uniq_borₛ opt_pairₛ] (at_clocₛ opt_pairₛ) () ()
      (λ α, FP ∅ +[&uniq{α} opt_pair]%T (&shr{α} opt_pair)%T AtomicClosed)
      res_opt_fold_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros α ϝ k wl. destruct wl as [vx []]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply typed_body_tctx_incl; [apply tctx_own_to_oplace|].
      (* unfold *x *)
      iApply type_seq.
      { apply (type_unfold_oplace_uniq_instr _ _ _ vx 1 PHole opt_pair α). solve_typing. }
      { solve_typing. } { reflexivity. }
      (* match *x *)
      iApply (type_case_oplace_deep _ _ _ _ vx 1 (PUniq α PHole) +[(); int * int]%T
        _ _ _ -[_; _]); [solve_typing|].
      iSplitL; [|iSplitL; [|done]].
      - (* None *)
        simpl.
        iApply type_seq.
        { apply (type_resolve_oplace_res_instr _ _ _ vx 1
            (UniqLty (SumLty +[(); int * int]%T 0%fin (OfTy ()%T)) α)
            (ResUniqLty (SumLty +[(); int * int]%T 0%fin (OfTy ()%T)) α) 1).
          apply lty_res_uniq_cpd; [solve_typing|solve_typing|done|done]. }
        { solve_typing. } { reflexivity. }
        iApply typed_body_tctx_incl.
        { apply (tctx_fold_oplace_res_uniq _ _ vx 1 PHole α
            (SumLty +[(); int * int]%T 0%fin (OfTy ()%T))); done. }
        iApply type_seq.
        { apply (type_fold_oplace_shr_instr _ _ _ vx 1 PHole α opt_pair). solve_typing. }
        { solve_typing. } { reflexivity. }
        iApply (type_let with "[]").
        { apply (type_read_oplace_instr _ _ _ vx 1 PHole (&shr{α} opt_pair)); [done|apply _]. }
        { solve_typing. } { reflexivity. }
        iIntros (vr). simpl_subst.
        iApply type_seq.
        { apply (type_drop_oplace_res_instr _ _ _ vx 1 1 (OfTy (&shr{α} opt_pair)));
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
      - (* Some *)
        simpl.
        iApply type_seq.
        { apply (type_resolve_oplace_res_instr _ _ _ vx 1
            (UniqLty (SumLty +[(); int * int]%T 1%fin (OfTy (int * int)%T)) α)
            (ResUniqLty (SumLty +[(); int * int]%T 1%fin (OfTy (int * int)%T)) α) 1).
          apply lty_res_uniq_cpd; [solve_typing|solve_typing|done|done]. }
        { solve_typing. } { reflexivity. }
        iApply typed_body_tctx_incl.
        { apply (tctx_fold_oplace_res_uniq _ _ vx 1 PHole α
            (SumLty +[(); int * int]%T 1%fin (OfTy (int * int)%T))); done. }
        iApply type_seq.
        { apply (type_fold_oplace_shr_instr _ _ _ vx 1 PHole α opt_pair). solve_typing. }
        { solve_typing. } { reflexivity. }
        iApply (type_let with "[]").
        { apply (type_read_oplace_instr _ _ _ vx 1 PHole (&shr{α} opt_pair)); [done|apply _]. }
        { solve_typing. } { reflexivity. }
        iIntros (vr). simpl_subst.
        iApply type_seq.
        { apply (type_drop_oplace_res_instr _ _ _ vx 1 1 (OfTy (&shr{α} opt_pair)));
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
    destruct m as [[[[[l' [[[]|[[z1 z2]|[]]] pad]] ξi] d] g] idx]; simpl;
      intros Hspec; rewrite /trans_upper /trans_tail /=;
      intros Hres l _ z ->; apply Hspec; rewrite uniq_bor_future_eq; exact Hres.
  Qed.
End place_res_sum_fold.

Print Assumptions res_opt_fold_type.
