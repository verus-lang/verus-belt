From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type function product programs own cont uninit int
  uniq_bor borrow place place_nested place_resolve.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

Section nested_deep.
  Context `{!typeG Σ}.

  (*
  Reborrowing through a unique borrow stored in a field (a nested place below the root):

  ```
  fn get_snd_first<'a, 'b>(x: &'a mut (i32, &'b mut (i32, i32))) -> &'a mut i32 {
      &mut ( *x.1).0
  }
  ```

  with the specification `ensures *result == ( *old(x).1).0,
  fin(x) == (old(x).0, (( *fin(result), ( *old(x).1).1), fin(old(x).1)))`.
    * the referent of `x` is unfolded into a pair, and the borrow in field 1 into a nested
      place `UniqLty (ProdLty (OfTy int) (OfTy int)) 'b` at the path `PSnd _ PHole`
      ([type_unfold_place_uniq_prod_deep_instr]);
    * `( *x.1).0` is reborrowed at `'a ⊓ 'a` ([type_reborrow_place_nested_instr]), and
      `( *x.1).1` too, which is resolved;
    * `x` is resolved ([type_resolve_place_instr]) while the leaves of the nested place
      are blocked and `x.0` is not.
  *)

  Definition get_snd_first : val :=
    fn: ["x"] :=
      let: "b" := !"x" in
      delete [ #1; "x"];;
      ReBor;;                                       (* unfold *( *b).1 *)
      let: "r" := ReBor;; !("b" +ₗ #1) +ₗ #0 in     (* &mut ( *( *b).1).0 *)
      let: "r2" := ReBor;; !("b" +ₗ #1) +ₗ #1 in    (* &mut ( *( *b).1).1 *)
      Skip;;                                        (* resolve r2 *)
      (Skip;; Skip;; #☠);;                          (* resolve b *)
      let: "ret" := new [ #1] in
      "ret" <- "r";;
      return: ["ret"].

  Notation get_snd_firstₛ := (Zₛ * uniq_borₛ (Zₛ * Zₛ))%ST.

  Definition get_snd_first_spec : fn_spec [uniq_borₛ get_snd_firstₛ] (uniq_borₛ Zₛ) () :=
    λ _ post '-[(_, m)], λ mask π, ∀ (lr: loc) (r: ~~ (uniq_borₛ Zₛ)),
      let b := (uniq_bor_current (𝔄:=get_snd_firstₛ) m).2 in
      uniq_bor_current r = (uniq_bor_current (𝔄:=Zₛ * Zₛ) b).1 →
      uniq_bor_future (𝔄:=get_snd_firstₛ) m π =
        ((uniq_bor_current (𝔄:=get_snd_firstₛ) m).1,
         ((uniq_bor_future r π, (uniq_bor_current (𝔄:=Zₛ * Zₛ) b).2),
          uniq_bor_future (𝔄:=Zₛ * Zₛ) b π)) →
      post (lr, r) mask π.

  Lemma get_snd_first_type :
    typed_val get_snd_first
      ((fn<(α, β)>(∅; &uniq{α} (int * &uniq{β} (int * int))) → &uniq{α} int)
        get_snd_first_spec)
      (get_snd_first, ()).
  Proof.
    unfold get_snd_first. unlock.
    opose proof (@type_fn _ _ _ [uniq_borₛ get_snd_firstₛ] (uniq_borₛ Zₛ) () ()
      (λ '(α, β), FP ∅ +[&uniq{α} (int * &uniq{β} (int * int))]%T (&uniq{α} int)%T
        AtomicClosed)
      get_snd_first_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros [α β] ϝ k wl. destruct wl as [vx []]. simpl_subst.
    (* [α] is alive (proved once). *)
    have Alv: lctx_lft_alive
      (fp_E (FP ∅ +[&uniq{α} (int * &uniq{β} (int * int))]%T (&uniq{α} int) AtomicClosed) ϝ)
      [ϝ ⊑ₗ []] α.
    { eapply (lctx_lft_alive_external _ _ ϝ); [rewrite /fp_E /=; by right; left|solve_typing]. }
    iApply (typed_body_impl with "[]"); last first. {
      iApply (type_let with "[]").
      { eapply (type_deref_instr (own_ptr 1 (&uniq{α} (int * &uniq{β} (int * int))))
          (&uniq{α} (int * &uniq{β} (int * int)))).
        - apply uniq_stack_okay.
        - done.
        - apply (read_own_move (&uniq{α} (int * &uniq{β} (int * int)))). }
      { apply tctx_extract_elt_here_exact. }
      { reflexivity. }
      iIntros (vb). simpl_subst.
      iApply type_delete. { solve_typing. } { done. } { done. }
      (* unfold the referent of b, and the borrow in its field 1 *)
      iApply typed_body_tctx_incl.
      { apply (tctx_unfold_uniq_prod _ _ vb α int (&uniq{β} (int * int))). done. }
      iApply type_seq.
      { apply (type_unfold_place_uniq_prod_deep_instr _ _ _ vb α β (PSnd (OfTy int) PHole)
          int int); [done|done|done]. }
      { solve_typing. } { reflexivity. }
      (* &mut ( *( *b).1).0, at α ⊓ α *)
      iApply (type_let with "[]").
      { apply (type_reborrow_place_nested_instr _ _ _ vb α β α (PSnd (OfTy int) PHole)
          (PFst PHole (OfTy int)) int); [done|done|done|done]. }
      { solve_typing. } { reflexivity. }
      iIntros (vr). simpl_subst.
      (* &mut ( *( *b).1).1, at α ⊓ α *)
      iApply (type_let with "[]").
      { apply (type_reborrow_place_nested_instr _ _ _ vb α β α (PSnd (OfTy int) PHole)
          (PSnd (Blocked int (α ⊓ α)) PHole) int); [done|done|done|done]. }
      { solve_typing. } { reflexivity. }
      iIntros (vr2). simpl_subst.
      iApply type_resolve. { solve_typing. } { apply uniq_bor.uniq_resolve. solve_typing. }
      (* resolve b *)
      iApply type_seq.
      { apply (type_resolve_place_instr _ _ _ vb α
          (ProdLty (OfTy int) (UniqLty (ProdLty (Blocked int (α ⊓ α)) (Blocked int (α ⊓ α))) β)));
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
    destruct m as [[[[[l [a [[[[[l' [x1 x2]] ξi'] d1] g1] idx']]] ξi] d] g] idx]. simpl.
    intros Hspec. rewrite /trans_upper /trans_tail /=.
    intros z _ m1 Hl1 Hc1 m2 Hl2 Hc2 Hres Hfin lr junk w ->.
    apply Hspec; [done|]. rewrite Hfin.
    destruct m1 as [[[[[l1 y1] ζi1] d3] g3] idx1].
    destruct m2 as [[[[[l2 y2] ζi2] d4] g4] idx2].
    simpl in Hc1, Hc2, Hres. rewrite /nest_get /= in Hc1 Hc2. subst y1 y2.
    rewrite /place_cur /place_rfn /= ?prfn_den_inl /= !uniq_bor_future_eq.
    f_equal. f_equal. f_equal. exact Hres.
  Qed.

  (*
  Unfolding a nested place further:

  ```
  fn get_inner_mid<'a, 'b>(x: &'a mut &'b mut ((i32, i32), i32)) -> &'a mut i32 {
      &mut ( **x).0.1
  }
  ```

  with the specification `ensures *result == ( **old(x)).0.1,
  fin(x) == ((( **old(x)).0.0, *fin(result)), ( **old(x)).1), fin( *old(x)))`. The
  referent of `x` is unfolded into the nested place
  `UniqLty (ProdLty (OfTy (int * int)) (OfTy int)) 'b`, whose field 0 is then unfolded
  ([tctx_unfold_place_nested_prod]); `( **x).0.1` is reborrowed, the other two leaves are
  reborrowed and resolved, and `x` is dropped while all leaves are blocked.
  *)

  Definition get_inner_mid : val :=
    fn: ["x"] :=
      let: "b" := !"x" in
      delete [ #1; "x"];;
      ReBor;;                                       (* unfold **b *)
      let: "r" := ReBor;; !("b" +ₗ #0) +ₗ #1 in     (* &mut ( **b).0.1 *)
      let: "r2" := ReBor;; !("b" +ₗ #0) +ₗ #0 in    (* &mut ( **b).0.0 *)
      let: "r3" := ReBor;; !("b" +ₗ #0) +ₗ #2 in    (* &mut ( **b).1 *)
      Skip;; Skip;;                                 (* resolve r2, r3, drop b *)
      let: "ret" := new [ #1] in
      "ret" <- "r";;
      return: ["ret"].

  Notation get_inner_midₛ := (uniq_borₛ ((Zₛ * Zₛ) * Zₛ))%ST.

  Definition get_inner_mid_spec : fn_spec [uniq_borₛ get_inner_midₛ] (uniq_borₛ Zₛ) () :=
    λ _ post '-[(_, m)], λ mask π, ∀ (lr: loc) (r: ~~ (uniq_borₛ Zₛ)),
      let b := uniq_bor_current (𝔄:=get_inner_midₛ) m in
      let c := uniq_bor_current (𝔄:=(Zₛ * Zₛ) * Zₛ) b in
      uniq_bor_current r = c.1.2 →
      uniq_bor_future (𝔄:=get_inner_midₛ) m π =
        (((c.1.1, uniq_bor_future r π), c.2), uniq_bor_future (𝔄:=(Zₛ * Zₛ) * Zₛ) b π) →
      post (lr, r) mask π.

  Lemma get_inner_mid_type :
    typed_val get_inner_mid
      ((fn<(α, β)>(∅; &uniq{α} (&uniq{β} ((int * int) * int))) → &uniq{α} int)
        get_inner_mid_spec)
      (get_inner_mid, ()).
  Proof.
    unfold get_inner_mid. unlock.
    opose proof (@type_fn _ _ _ [uniq_borₛ get_inner_midₛ] (uniq_borₛ Zₛ) () ()
      (λ '(α, β), FP ∅ +[&uniq{α} (&uniq{β} ((int * int) * int))]%T (&uniq{α} int)%T
        AtomicClosed)
      get_inner_mid_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros [α β] ϝ k wl. destruct wl as [vx []]. simpl_subst.
    (* [α] is alive (proved once). *)
    have Alv: lctx_lft_alive
      (fp_E (FP ∅ +[&uniq{α} (&uniq{β} ((int * int) * int))]%T (&uniq{α} int) AtomicClosed) ϝ)
      [ϝ ⊑ₗ []] α.
    { eapply (lctx_lft_alive_external _ _ ϝ); [rewrite /fp_E /=; by right; left|solve_typing]. }
    iApply (typed_body_impl with "[]"); last first. {
      iApply (type_let with "[]").
      { eapply (type_deref_instr (own_ptr 1 (&uniq{α} (&uniq{β} ((int * int) * int))))
          (&uniq{α} (&uniq{β} ((int * int) * int)))).
        - apply uniq_stack_okay.
        - done.
        - apply (read_own_move (&uniq{α} (&uniq{β} ((int * int) * int)))). }
      { apply tctx_extract_elt_here_exact. }
      { reflexivity. }
      iIntros (vb). simpl_subst.
      iApply type_delete. { solve_typing. } { done. } { done. }
      (* unfold the referent of b into a nested place, and its field 0 *)
      iApply typed_body_tctx_incl.
      { apply (tctx_uniq_to_place _ _ vb α (&uniq{β} ((int * int) * int))). }
      iApply type_seq.
      { apply (type_unfold_place_uniq_prod_instr _ _ _ vb α β (int * int) int). done. }
      { solve_typing. } { reflexivity. }
      iApply typed_body_tctx_incl.
      { apply (tctx_unfold_place_nested_prod _ _ vb α β PHole (PFst PHole (OfTy int)) int int);
          [done|done|done|done|done]. }
      (* &mut ( **b).0.1, at α ⊓ α *)
      iApply (type_let with "[]").
      { apply (type_reborrow_place_nested_instr _ _ _ vb α β α PHole
          (PFst (PSnd (OfTy int) PHole) (OfTy int)) int); [done|done|done|done]. }
      { solve_typing. } { reflexivity. }
      iIntros (vr). simpl_subst.
      (* &mut ( **b).0.0 *)
      iApply (type_let with "[]").
      { apply (type_reborrow_place_nested_instr _ _ _ vb α β α PHole
          (PFst (PFst PHole (Blocked int (α ⊓ α))) (OfTy int)) int); [done|done|done|done]. }
      { solve_typing. } { reflexivity. }
      iIntros (vr2). simpl_subst.
      (* &mut ( **b).1 *)
      iApply (type_let with "[]").
      { apply (type_reborrow_place_nested_instr _ _ _ vb α β α PHole
          (PSnd (ProdLty (Blocked int (α ⊓ α)) (Blocked int (α ⊓ α))) PHole) int);
          [done|done|done|done]. }
      { solve_typing. } { reflexivity. }
      iIntros (vr3). simpl_subst.
      iApply type_resolve. { solve_typing. } { apply uniq_bor.uniq_resolve. solve_typing. }
      iApply type_resolve. { solve_typing. } { apply uniq_bor.uniq_resolve. solve_typing. }
      iApply typed_body_tctx_incl.
      { apply (tctx_incl_frame_r +[_] +[]). apply tctx_drop_place_cpd; [done|done|done]. }
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
    destruct m as [[[[[l [[[[[l' [[x1 x2] x3]] ξi'] d1] g1] idx']] ξi] d] g] idx]. simpl.
    intros Hspec. rewrite /trans_upper /trans_tail /=.
    intros z _ m1 Hl1 Hc1 m2 Hl2 Hc2 m3 Hl3 Hc3 Hres3 Hres2 Hfin lr junk w ->.
    apply Hspec; [done|]. rewrite Hfin.
    destruct m1 as [[[[[l1 y1] ζi1] d3] g3] idx1].
    destruct m2 as [[[[[l2 y2] ζi2] d4] g4] idx2].
    destruct m3 as [[[[[l3 y3] ζi3] d5] g5] idx3].
    simpl in Hc1, Hc2, Hc3, Hres2, Hres3. rewrite /nest_get /= in Hc1 Hc2 Hc3. subst y1 y2 y3.
    rewrite /place_cur /place_rfn /= ?prfn_den_inl /= !uniq_bor_future_eq.
    rewrite /uniq_prvar. by rewrite Hres2 Hres3.
  Qed.
End nested_deep.

Print Assumptions get_snd_first_type.
Print Assumptions get_inner_mid_type.
