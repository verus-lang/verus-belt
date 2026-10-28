From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type function product programs own cont uninit int
  uniq_bor borrow place place_own place_resolve place_puniq.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

Section place_puniq.
  Context `{!typeG Σ}.

  (*
  Reborrowing through a nested unique borrow, the argument being an owned place:

  ```
  fn get_inner_first<'a, 'b>(x: &'a mut &'b mut (i32, i32)) -> &'a mut i32 {
      &mut ( **x).0
  }
  ```

  with the specification `ensures *result == ( **old(x)).0,
  fin(x) == (( *fin(result), ( **old(x)).1), fin( *old(x)))` (as [get_inner_first] of
  [nested_uniq.v]). The argument slot `x` is an owned place
  [own (&uniq{'a} (&uniq{'b} (i32, i32)))] ([tctx_own_to_oplace]):
    * `*x` and `**x` are unfolded ([type_unfold_oplace_uniq_instr], at the root and below
      [PUniq 'a]), and `**x` as a pair ([type_unfold_oplace_prod_instr]);
    * `( **x).0` is reborrowed ([type_borrow_oplace_deep_instr]) at
      `'a ⊓ ('b ⊓ 'a)`, which reserves both enclosing prophecies for the reborrow's;
    * `( **x).1` is reborrowed too, and resolved;
    * the slot `x` is dropped ([type_drop_oplace_deep_instr]), resolving `*x` through its
      reservation ([lty_rslv_uniq_blk]: both leaves of the nested place are blocked).
  *)

  Definition get_inner_first_own : val :=
    fn: ["x"] :=
      ReBor;;                                       (* unfold *x *)
      ReBor;;                                       (* unfold **x *)
      ReBor;;                                       (* unfold **x as a pair *)
      let: "r" := ReBor;; !(!"x") in                (* &mut ( **x).0 *)
      let: "r2" := ReBor;; !(!"x") +ₗ #1 in         (* &mut ( **x).1, to drop x *)
      Skip;;                                        (* resolve r2 *)
      (#☠;; delete [ #1; "x"]);;                     (* drop x *)
      let: "ret" := new [ #1] in
      "ret" <- "r";;
      return: ["ret"].

  Definition get_inner_first_own_spec :
      fn_spec [uniq_borₛ (uniq_borₛ (Zₛ * Zₛ))] (uniq_borₛ Zₛ) () :=
    λ _ post '-[(_, m)], λ mask π, ∀ (lr: loc) (r: ~~ (uniq_borₛ Zₛ)),
      let b := uniq_bor_current (𝔄:=uniq_borₛ (Zₛ * Zₛ)) m in
      uniq_bor_current r = (uniq_bor_current (𝔄:=Zₛ * Zₛ) b).1 →
      uniq_bor_future (𝔄:=uniq_borₛ (Zₛ * Zₛ)) m π =
        ((uniq_bor_future r π, (uniq_bor_current (𝔄:=Zₛ * Zₛ) b).2),
          uniq_bor_future (𝔄:=Zₛ * Zₛ) b π) →
      post (lr, r) mask π.

  Lemma get_inner_first_own_type :
    typed_val get_inner_first_own
      ((fn<(α, β)>(∅; &uniq{α} (&uniq{β} (int * int))) → &uniq{α} int) get_inner_first_own_spec)
      (get_inner_first_own, ()).
  Proof.
    unfold get_inner_first_own. unlock.
    opose proof (@type_fn _ _ _ [uniq_borₛ (uniq_borₛ (Zₛ * Zₛ))] (uniq_borₛ Zₛ) () ()
      (λ '(α, β), FP ∅ +[&uniq{α} (&uniq{β} (int * int))]%T (&uniq{α} int)%T AtomicClosed)
      get_inner_first_own_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros [α β] ϝ k wl. destruct wl as [vx []]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply typed_body_tctx_incl; [apply tctx_own_to_oplace|].
      (* unfold *x *)
      iApply type_seq.
      { apply (type_unfold_oplace_uniq_instr _ _ _ vx 1 PHole (&uniq{β} (int * int)) α).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      (* unfold **x *)
      iApply type_seq.
      { apply (type_unfold_oplace_uniq_instr _ _ _ vx 1 (PUniq α PHole) (int * int) β).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      (* unfold **x as a pair *)
      iApply type_seq.
      { apply (type_unfold_oplace_prod_instr _ _ _ vx 1 (PUniq α (PUniq β PHole)) int int).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      (* &mut ( **x).0, at α ⊓ (β ⊓ α) *)
      iApply (type_let with "[]").
      { apply (type_borrow_oplace_deep_instr _ _ _ vx 1 α
          (PUniq α (PUniq β (PFst PHole (OfTy int)))) int); [done|solve_typing|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iIntros (vr). simpl_subst.
      (* &mut ( **x).1 *)
      iApply (type_let with "[]").
      { apply (type_borrow_oplace_deep_instr _ _ _ vx 1 α
          (PUniq α (PUniq β (PSnd (Blocked int (α ⊓ (β ⊓ α))) PHole))) int);
          [done|solve_typing|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iIntros (vr2). simpl_subst.
      (* resolve it, and drop x *)
      iApply type_resolve. { solve_typing. } { apply uniq_bor.uniq_resolve. solve_typing. }
      iApply type_seq.
      { apply (type_drop_oplace_deep_instr _ _ _ vx 1 1
          (UniqLty (UniqLty (ProdLty (Blocked int (α ⊓ (β ⊓ α))) (Blocked int (α ⊓ (β ⊓ α)))) β) α));
          [done|done|done|].
        apply lty_rslv_uniq_blk; [solve_typing|done|done]. }
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
    destruct m as [[[[[l [[[[[l' [x1 x2]] ξi'] d1] g1] idx']] ξi] d] g] idx]. simpl.
    intros Hspec. rewrite /trans_upper /trans_tail /=.
    intros m1 Hc1 m0 Hc0 Hres Hfin l0 junk z ->. apply Hspec; [done|].
    destruct m1 as [[[[[l1 w1] ζi] d3] g3] idx1]. destruct m0 as [[[[[l2 w2] ζi0] d4] g4] idx2].
    simpl in *. subst w1 w2. rewrite !uniq_bor_future_eq /=. rewrite Hfin.
    f_equal. f_equal. exact Hres.
  Qed.
End place_puniq.
