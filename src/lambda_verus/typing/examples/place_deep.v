From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type function product programs own cont uninit int sum type_sum
  uniq_bor shr_bor borrow place place_own place_resolve place_puniq place_pshr place_deep.
From lrust.lang Require Import lang notation memcpy new_delete.
Set Default Proof Using "Type".

Section place_deep.
  Context `{!typeG Σ}.

  (*
  Copying and assigning a pair through two levels of mutable references:

  ```
  fn swap_snd<'a, 'b>(x: &'a mut &'b mut (i32, (i32, i32)), y: (i32, i32)) -> (i32, i32) {
      let c = ( **x).1;   // copy out of ( **x).1 (two cells)
      ( **x).1 = y;       // assign ( **x).1 (two cells)
      c
  }
  ```

  with the specification `ensures result == ( **old(x)).1,
  fin(x) == ((( **old(x)).0, y), fin( *old(x)))`. The argument slot is an owned place;
  `*x`, `**x` and the pair `**x` are unfolded; `( **x).1` (in [Owned] mode inside the node
  of the inner borrow) is copied out ([type_memcpy_copy_from_oplace_deep_instr]) and
  assigned ([type_memcpy_oplace_deep_instr]); the place is folded back and dropped.
  *)

  Definition swap_snd : val :=
    fn: ["x"; "y"] :=
      ReBor;; ReBor;; ReBor;;                   (* unfold *x, **x, **x as a pair *)
      let: "c" := new [ #2] in
      "c" <-{2} !(!(!"x") +ₗ #1);;               (* c = ( **x).1 *)
      !(!"x") +ₗ #1 <-{2} !"y";;                 (* ( **x).1 = y *)
      ReBor;; ReBor;; ReBor;;                   (* fold back *)
      (#☠;; delete [ #1; "x"]);;                 (* drop x, resolving it *)
      delete [ #2; "y"];;
      return: ["c"].

  Definition swap_snd_spec :
      fn_spec [uniq_borₛ (uniq_borₛ (Zₛ * (Zₛ * Zₛ))); (Zₛ * Zₛ)%ST] (Zₛ * Zₛ) () :=
    λ _ post '-[(_, m); (_, y)], λ mask π,
      let b := uniq_bor_current (𝔄:=uniq_borₛ (Zₛ * (Zₛ * Zₛ))) m in
      uniq_bor_future (𝔄:=uniq_borₛ (Zₛ * (Zₛ * Zₛ))) m π =
        (((uniq_bor_current (𝔄:=Zₛ * (Zₛ * Zₛ)) b).1, y),
          uniq_bor_future (𝔄:=Zₛ * (Zₛ * Zₛ)) b π) →
      ∀ (lr: loc), post (lr, (uniq_bor_current (𝔄:=Zₛ * (Zₛ * Zₛ)) b).2) mask π.

  Lemma swap_snd_type :
    typed_val swap_snd
      ((fn<(α, β)>(∅; &uniq{α} (&uniq{β} (int * (int * int))), int * int) → int * int)
        swap_snd_spec)
      (swap_snd, ()).
  Proof.
    unfold swap_snd. unlock.
    opose proof (@type_fn _ _ _ [uniq_borₛ (uniq_borₛ (Zₛ * (Zₛ * Zₛ))); (Zₛ * Zₛ)%ST]
      (Zₛ * Zₛ) () ()
      (λ '(α, β), FP ∅ +[&uniq{α} (&uniq{β} (int * (int * int))); (int * int)%T]%T
        (int * int)%T AtomicClosed)
      swap_snd_spec _ [BNamed "x"; BNamed "y"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros [α β] ϝ k wl. destruct wl as [vx [vy []]]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_r +[_] +[_]). apply tctx_own_to_oplace. }
      (* unfold *x, **x, **x as a pair *)
      iApply type_seq.
      { apply (type_unfold_oplace_uniq_instr _ _ _ vx 1 PHole (&uniq{β} (int * (int * int))) α).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_unfold_oplace_uniq_instr _ _ _ vx 1 (PUniq α PHole) (int * (int * int)) β).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_unfold_oplace_prod_instr _ _ _ vx 1 (PUniq α (PUniq β PHole)) int (int * int)).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply (type_new 2). { lia. } iIntros (vc). simpl_subst.
      (* c = ( **x).1 *)
      iApply type_seq.
      { apply (type_memcpy_copy_from_oplace_deep_instr _ _ _ vc vx 1
          (PUniq α (PUniq β (PSnd (OfTy int) PHole))) (int * int)
          (own_ptr 2 (↯ 2)) (own_ptr 2 (int * int)) (↯ 2));
          [apply _|by apply write_own| |done|solve_typing].
        apply (resolve'_just _ _ _ (const True)). apply resolve_just. }
      { solve_typing. } { reflexivity. }
      (* ( **x).1 = y *)
      iApply type_seq.
      { apply (type_memcpy_oplace_deep_instr _ _ _ vx vy 1
          (PUniq α (PUniq β (PSnd (OfTy int) PHole))) (int * int)
          (own_ptr 2 (int * int)) (own_ptr 2 (↯ (ty_size (int * int)))));
          [apply resolve_just|apply (read_own_move (int * int))|done|solve_typing]. }
      { solve_typing. } { reflexivity. }
      (* fold back *)
      iApply type_seq.
      { apply (type_fold_oplace_prod_instr _ _ _ vx 1 (PUniq α (PUniq β PHole)) int (int * int)).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_fold_oplace_uniq_instr _ _ _ vx 1 (PUniq α PHole) (int * (int * int)) β).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_fold_oplace_uniq_instr _ _ _ vx 1 PHole (&uniq{β} (int * (int * int))) α).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      (* drop x, resolving it *)
      iApply type_seq.
      { apply (type_drop_oplace_deep_instr _ _ _ vx 1 1
          (OfTy (&uniq{α} (&uniq{β} (int * (int * int)))))); [done|done|done|].
        apply lty_rslv_of, lty_resolve_ofty, uniq_bor.uniq_resolve. solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_delete. { solve_typing. } { done. } { done. }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lx m] [[ly [y1 y2]] []]] mask π. simpl.
    destruct m as [[[[[l [[[[[l' [x1 x2]] ξb] db] gb] idxb]] ξa] da] ga] idxa].
    simpl. intros Hspec. rewrite /trans_upper /trans_tail /=.
    intros l0 junk zw -> _ zr _ d g idx d0 g0 idx0 Hres. apply Hspec.
    rewrite !uniq_bor_future_eq /=.
    rewrite (uniq_prvar_app_irrel (𝔄:=uniq_borₛ (Zₛ * (Zₛ * Zₛ))) _
      (l', (x1, (y1, y2)), ξb, d, g, idx) ξa π).
    etrans; [exact Hres|]. f_equal.
    exact (uniq_prvar_app_irrel (𝔄:=Zₛ * (Zₛ * Zₛ)) (x1, (y1, y2)) (x1, x2) ξb π).
  Qed.
  (*
  Copying a pair out through two shared references:

  ```
  fn get_pair<'a, 'b>(x: &'a &'b (i32, i32)) -> (i32, i32) { **x }
  ```

  with the specification `ensures result == **x`. The argument slot is an owned place;
  `*x` is unfolded and the view of its referent changed to [ShrLty (OfTy (int * int)) 'b];
  `**x` (two cells) is copied out ([type_memcpy_copy_from_oplace_pshr_instr], [K = PHole],
  [K2 = PShr 'b PHole]: two loads of shared references); `x` is dropped.
  *)

  Definition get_pair : val :=
    fn: ["x"] :=
      ReBor;;                                       (* unfold *x *)
      ReBor;;                                       (* view **x *)
      let: "r" := new [ #2] in
      (Skip;; "r" <-{2} !(!(!"x")));;               (* r = **x *)
      (#☠;; delete [ #1; "x"]);;                     (* drop x *)
      return: ["r"].

  Definition get_pair_spec :
      fn_spec [at_clocₛ (at_clocₛ (Zₛ * Zₛ))] (Zₛ * Zₛ) () :=
    λ _ post '-[(_, m)], λ mask π, ∀ (lr: loc), post (lr, m.2.2) mask π.

  Lemma get_pair_type :
    typed_val get_pair
      ((fn<(α, β)>(∅; &shr{α} (&shr{β} (int * int))) → int * int) get_pair_spec)
      (get_pair, ()).
  Proof.
    unfold get_pair. unlock.
    opose proof (@type_fn _ _ _ [at_clocₛ (at_clocₛ (Zₛ * Zₛ))] (Zₛ * Zₛ) () ()
      (λ '(α, β), FP ∅ +[&shr{α} (&shr{β} (int * int))]%T (int * int)%T AtomicClosed)
      get_pair_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros [α β] ϝ k wl. destruct wl as [vx []]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply typed_body_tctx_incl; [apply tctx_own_to_oplace|].
      (* unfold *x *)
      iApply type_seq.
      { apply (type_unfold_oplace_shr_instr _ _ _ vx 1 PHole α (&shr{β} (int * int))).
        solve_typing. }
      { solve_typing. } { reflexivity. }
      (* view **x *)
      iApply type_seq.
      { apply (type_change_oplace_shr_instr _ _ _ vx 1 PHole α PHole
          (OfTy (&shr{β} (int * int))) (ShrLty (OfTy (int * int)) β));
          [solve_typing|done|done|done]. }
      { solve_typing. } { reflexivity. }
      iApply (type_new 2). { lia. } iIntros (vr). simpl_subst.
      (* r = **x *)
      iApply type_seq.
      { apply (type_memcpy_copy_from_oplace_pshr_instr _ _ _ vr vx 1 PHole α
          (PShr β PHole) (OfTy (int * int)) (own_ptr 2 (↯ 2)) (own_ptr 2 (int * int)) (↯ 2));
          [apply _|by apply write_own| |done|solve_typing|solve_typing].
        apply (resolve'_just _ _ _ (const True)). apply resolve_just. }
      { solve_typing. } { reflexivity. }
      (* drop x *)
      iApply type_seq.
      { apply (type_drop_oplace_deep_instr _ _ _ vx 1 1
          (ShrLty (ShrLty (OfTy (int * int)) β) α)); [done|done|done|].
        apply lty_rslv_shr. }
      { solve_typing. } { reflexivity. }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lx [l1 [l2 [z1 z2]]]] []] mask π. simpl.
    intros Hspec. rewrite /trans_upper /trans_tail /=.
    intros l0 junk zw -> _. apply Hspec.
  Qed.
End place_deep.

Print Assumptions swap_snd_type.
Print Assumptions get_pair_type.
