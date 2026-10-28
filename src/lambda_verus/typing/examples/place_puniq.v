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
  (*
  A write through three levels of mutable references:

  ```
  fn write_deep<'a, 'b, 'c>(x: &'a mut &'b mut &'c mut i32) { ***x = 5; }
  ```

  with the specification `ensures fin(x) == ((5, fin( **old(x))), fin( *old(x)))`. The
  argument slot is an owned place; `*x`, `**x` and `***x` are unfolded (the last two below
  unique borrows, in [Uniq] mode); `***x`, the whole referent of the innermost borrow, is
  written ([type_write_oplace_deep_instr]); the place is folded back
  ([type_fold_oplace_uniq_instr]) and dropped, resolving `x`.
  *)

  Definition write_deep : val :=
    fn: ["x"] :=
      ReBor;; ReBor;; ReBor;;                       (* unfold *x, **x, ***x *)
      let: "five" := #5 in
      (ReBor;; !(!(!"x")) <- "five");;              (* ***x = 5 *)
      ReBor;; ReBor;; ReBor;;                       (* fold back *)
      (#☠;; delete [ #1; "x"]);;                     (* drop x, resolving it *)
      let: "ret" := new [ #0] in
      return: ["ret"].

  Definition write_deep_spec :
      fn_spec [uniq_borₛ (uniq_borₛ (uniq_borₛ Zₛ))] () () :=
    λ _ post '-[(_, m)], λ mask π,
      let b := uniq_bor_current (𝔄:=uniq_borₛ (uniq_borₛ Zₛ)) m in
      let c := uniq_bor_current (𝔄:=uniq_borₛ Zₛ) b in
      uniq_bor_future (𝔄:=uniq_borₛ (uniq_borₛ Zₛ)) m π =
        ((5%Z, uniq_bor_future (𝔄:=Zₛ) c π), uniq_bor_future (𝔄:=uniq_borₛ Zₛ) b π) →
      ∀ ret, post ret mask π.

  Lemma write_deep_type :
    typed_val write_deep
      ((fn<(α, β, γ)>(∅; &uniq{α} (&uniq{β} (&uniq{γ} int))) → ()) write_deep_spec)
      (write_deep, ()).
  Proof.
    unfold write_deep. unlock.
    opose proof (@type_fn _ _ _ [uniq_borₛ (uniq_borₛ (uniq_borₛ Zₛ))] () () ()
      (λ '(α, β, γ), FP ∅ +[&uniq{α} (&uniq{β} (&uniq{γ} int))]%T ()%T AtomicClosed)
      write_deep_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros [[α β] γ] ϝ k wl. destruct wl as [vx []]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply typed_body_tctx_incl; [apply tctx_own_to_oplace|].
      (* unfold *x, **x, ***x *)
      iApply type_seq.
      { apply (type_unfold_oplace_uniq_instr _ _ _ vx 1 PHole (&uniq{β} (&uniq{γ} int)) α).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_unfold_oplace_uniq_instr _ _ _ vx 1 (PUniq α PHole) (&uniq{γ} int) β).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_unfold_oplace_uniq_instr _ _ _ vx 1 (PUniq α (PUniq β PHole)) int γ).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      (* ***x = 5 *)
      iApply type_int. iIntros (v5). simpl_subst.
      iApply type_seq.
      { apply (type_write_oplace_deep_instr _ _ _ vx v5 1 (PUniq α (PUniq β (PUniq γ PHole))) int
          (const (const True))); [done|apply resolve_just|solve_typing]. }
      { solve_typing. } { reflexivity. }
      (* fold back *)
      iApply type_seq.
      { apply (type_fold_oplace_uniq_instr _ _ _ vx 1 (PUniq α (PUniq β PHole)) int γ).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_fold_oplace_uniq_instr _ _ _ vx 1 (PUniq α PHole) (&uniq{γ} int) β).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_fold_oplace_uniq_instr _ _ _ vx 1 PHole (&uniq{β} (&uniq{γ} int)) α).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      (* drop x, resolving it *)
      iApply type_seq.
      { apply (type_drop_oplace_deep_instr _ _ _ vx 1 1 (OfTy (&uniq{α} (&uniq{β} (&uniq{γ} int)))));
          [done|done|done|].
        apply lty_rslv_of, lty_resolve_ofty, uniq_bor.uniq_resolve. solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply (type_new_subtype () 0). { lia. } { apply uninit_unit_1. }
      iIntros (vret). simpl_subst.
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lx m] []] mask π. simpl.
    destruct m as [[[[[l [[[[[l' [[[[[l'' z] ξc] dc] gc] idxc]] ξb] db] gb] idxb]] ξa] da] ga] idxa].
    simpl. intros Hspec. rewrite /trans_upper /trans_tail /=.
    intros _ d g idx d0 g0 idx0 d1 g1 idx1 Hres l1 junk. apply Hspec.
    rewrite !uniq_bor_future_eq /=.
    rewrite (uniq_prvar_app_irrel (𝔄:=uniq_borₛ (uniq_borₛ Zₛ)) _ (l', (l'', 5%Z, ξc, d, g, idx), ξb, d0, g0, idx0) ξa π).
    etrans; [exact Hres|]. f_equal; [f_equal|].
    - exact (uniq_prvar_app_irrel (𝔄:=Zₛ) 5%Z z ξc π).
    - exact (uniq_prvar_app_irrel (𝔄:=uniq_borₛ Zₛ) (l'', 5%Z, ξc, d, g, idx)
        (l'', z, ξc, dc, gc, idxc) ξb π).
    Unshelve. eapply (composeₛ empty_prod_to_unitₛ uninit0_to_unitₛ).
  Qed.
  (*
  An assignment through two levels of mutable references:

  ```
  fn assign_two<'a, 'b>(x: &'a mut &'b mut (i32, i32), v: i32) { ( **x).0 = v; }
  ```

  with the specification `ensures fin(x) == ((v, ( **old(x)).1), fin( *old(x)))`. The leaf
  `( **x).0` is in [Owned] mode inside the node of the inner borrow; it is written directly
  ([type_write_oplace_deep_instr]), the place is folded back (the pair in [Uniq] mode,
  [type_fold_oplace_prod_instr]) and dropped.
  *)

  Definition assign_two : val :=
    fn: ["x"; "v"] :=
      ReBor;; ReBor;; ReBor;;                       (* unfold *x, **x, **x as a pair *)
      let: "w" := !"v" in
      delete [ #1; "v"];;
      (ReBor;; !(!"x") <- "w");;                    (* ( **x).0 = w *)
      ReBor;; ReBor;; ReBor;;                       (* fold back *)
      (#☠;; delete [ #1; "x"]);;                     (* drop x, resolving it *)
      let: "ret" := new [ #0] in
      return: ["ret"].

  Definition assign_two_spec :
      fn_spec [uniq_borₛ (uniq_borₛ (Zₛ * Zₛ)); Zₛ] () () :=
    λ _ post '-[(_, m); (_, v)], λ mask π,
      let b := uniq_bor_current (𝔄:=uniq_borₛ (Zₛ * Zₛ)) m in
      uniq_bor_future (𝔄:=uniq_borₛ (Zₛ * Zₛ)) m π =
        ((v, (uniq_bor_current (𝔄:=Zₛ * Zₛ) b).2), uniq_bor_future (𝔄:=Zₛ * Zₛ) b π) →
      ∀ ret, post ret mask π.

  Lemma assign_two_type :
    typed_val assign_two
      ((fn<(α, β)>(∅; &uniq{α} (&uniq{β} (int * int)), int) → ()) assign_two_spec)
      (assign_two, ()).
  Proof.
    unfold assign_two. unlock.
    opose proof (@type_fn _ _ _ [uniq_borₛ (uniq_borₛ (Zₛ * Zₛ)); Zₛ] () () ()
      (λ '(α, β), FP ∅ +[&uniq{α} (&uniq{β} (int * int)); int]%T ()%T AtomicClosed)
      assign_two_spec _ [BNamed "x"; BNamed "v"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros [α β] ϝ k wl. destruct wl as [vx [vv []]]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_r +[_] +[_]). apply tctx_own_to_oplace. }
      (* unfold *x, **x, **x as a pair *)
      iApply type_seq.
      { apply (type_unfold_oplace_uniq_instr _ _ _ vx 1 PHole (&uniq{β} (int * int)) α).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_unfold_oplace_uniq_instr _ _ _ vx 1 (PUniq α PHole) (int * int) β).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_unfold_oplace_prod_instr _ _ _ vx 1 (PUniq α (PUniq β PHole)) int int).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      (* read v *)
      iApply (type_let with "[]").
      { eapply (type_deref_instr (own_ptr 1 int) int).
        - apply int_stack_okay.
        - done.
        - apply (read_own_copy int). apply _. }
      { solve_typing. } { reflexivity. }
      iIntros (vw). simpl_subst.
      iApply type_delete. { solve_typing. } { done. } { done. }
      (* ( **x).0 = w *)
      iApply type_seq.
      { apply (type_write_oplace_deep_instr _ _ _ vx vw 1
          (PUniq α (PUniq β (PFst PHole (OfTy int)))) int (const (const True)));
          [done|apply resolve_just|solve_typing]. }
      { solve_typing. } { reflexivity. }
      (* fold back *)
      iApply type_seq.
      { apply (type_fold_oplace_prod_instr _ _ _ vx 1 (PUniq α (PUniq β PHole)) int int).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_fold_oplace_uniq_instr _ _ _ vx 1 (PUniq α PHole) (int * int) β).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_fold_oplace_uniq_instr _ _ _ vx 1 PHole (&uniq{β} (int * int)) α).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      (* drop x, resolving it *)
      iApply type_seq.
      { apply (type_drop_oplace_deep_instr _ _ _ vx 1 1 (OfTy (&uniq{α} (&uniq{β} (int * int)))));
          [done|done|done|].
        apply lty_rslv_of, lty_resolve_ofty, uniq_bor.uniq_resolve. solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply (type_new_subtype () 0). { lia. } { apply uninit_unit_1. }
      iIntros (vret). simpl_subst.
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lx m] [[lv v] []]] mask π. simpl.
    destruct m as [[[[[l [[[[[l' [x1 x2]] ξb] db] gb] idxb]] ξa] da] ga] idxa].
    simpl. intros Hspec. rewrite /trans_upper /trans_tail /=.
    intros z <- _ d g idx d0 g0 idx0 Hres l0 junk. apply Hspec.
    rewrite !uniq_bor_future_eq /=.
    rewrite (uniq_prvar_app_irrel (𝔄:=uniq_borₛ (Zₛ * Zₛ)) _ (l', (v, x2), ξb, d, g, idx) ξa π).
    etrans; [exact Hres|]. f_equal.
    exact (uniq_prvar_app_irrel (𝔄:=Zₛ * Zₛ) (v, x2) (x1, x2) ξb π).
    Unshelve. eapply (composeₛ empty_prod_to_unitₛ uninit0_to_unitₛ).
  Qed.
End place_puniq.

Print Assumptions get_inner_first_own_type.
Print Assumptions write_deep_type.
Print Assumptions assign_two_type.
