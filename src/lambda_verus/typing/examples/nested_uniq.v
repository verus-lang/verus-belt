From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type function product programs own cont uninit int
  uniq_bor borrow vplace place_puniq place_resolve.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

Section nested_uniq.
  Context `{!typeG Σ}.

  (*
  Reborrowing through a nested unique borrow:

  ```
  fn get_inner_first<'a, 'b>(x: &'a mut &'b mut (i32, i32)) -> &'a mut i32 {
      &mut ( **x).0
  }
  ```

  with the specification `ensures *result == ( **old(x)).0,
  fin(x) == (( *fin(result), ( **old(x)).1), fin( *old(x)))`: the final value of `x` is a
  borrow whose current value has the final value of the reborrow in field 0, and whose
  final value is the one of the inner borrow `*x` (which is not replaced).
    * `*x` is a place rooted at its value ([type_uniq_to_vplace_instr]), whose referent
      is unfolded into a nested place `UniqLty (ProdLty (OfTy int) (OfTy int)) 'b`
      ([type_unfold_vplace_uniq_instr], [type_unfold_vplace_prod_instr]); the prophecy
      of `*x` is reserved for the one of `**x`;
    * `( **x).0` is reborrowed at `'a ⊓ ('b ⊓ 'a)` ([type_borrow_vplace_deep_instr]),
      which blocks it and reserves both prophecies for the reborrow's;
    * `( **x).1` is reborrowed too, and resolved;
    * `*x` is dropped while both leaves of the nested place are blocked
      ([tctx_drop_vplace_uniq]).
  *)

  Definition get_inner_first : val :=
    fn: ["x"] :=
      let: "b" := !"x" in
      delete [ #1; "x"];;
      Skip;;                                        (* b as a place *)
      ReBor;; ReBor;;                               (* unfold **b, as a pair *)
      let: "r" := ReBor;; !"b" in                   (* &mut ( **b).0 *)
      let: "r2" := ReBor;; !"b" +ₗ #1 in            (* &mut ( **b).1, to drop b *)
      Skip;;                                        (* resolve r2, drop b *)
      let: "ret" := new [ #1] in
      "ret" <- "r";;
      return: ["ret"].

  Definition get_inner_first_spec :
      fn_spec [uniq_borₛ (uniq_borₛ (Zₛ * Zₛ))] (uniq_borₛ Zₛ) () :=
    λ _ post '-[(_, m)], λ mask π, ∀ (lr: loc) (r: ~~ (uniq_borₛ Zₛ)),
      let b := uniq_bor_current (𝔄:=uniq_borₛ (Zₛ * Zₛ)) m in
      uniq_bor_current r = (uniq_bor_current (𝔄:=Zₛ * Zₛ) b).1 →
      uniq_bor_future (𝔄:=uniq_borₛ (Zₛ * Zₛ)) m π =
        ((uniq_bor_future r π, (uniq_bor_current (𝔄:=Zₛ * Zₛ) b).2),
          uniq_bor_future (𝔄:=Zₛ * Zₛ) b π) →
      post (lr, r) mask π.

  Lemma get_inner_first_type :
    typed_val get_inner_first
      ((fn<(α, β)>(∅; &uniq{α} (&uniq{β} (int * int))) → &uniq{α} int) get_inner_first_spec)
      (get_inner_first, ()).
  Proof.
    unfold get_inner_first. unlock.
    opose proof (@type_fn _ _ _ [uniq_borₛ (uniq_borₛ (Zₛ * Zₛ))] (uniq_borₛ Zₛ) () ()
      (λ '(α, β), FP ∅ +[&uniq{α} (&uniq{β} (int * int))]%T (&uniq{α} int)%T AtomicClosed)
      get_inner_first_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros [α β] ϝ k wl. destruct wl as [vx []]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply (type_let with "[]").
      { eapply (type_deref_instr (own_ptr 1 (&uniq{α} (&uniq{β} (int * int))))
          (&uniq{α} (&uniq{β} (int * int)))).
        - apply uniq_stack_okay.
        - done.
        - apply (read_own_move (&uniq{α} (&uniq{β} (int * int)))). }
      { apply tctx_extract_elt_here_exact. }
      { reflexivity. }
      iIntros (vb). simpl_subst.
      iApply type_delete. { solve_typing. } { done. } { done. }
      (* b as a place rooted at its value; unfold its referent into a nested place *)
      iApply type_seq. { apply (type_uniq_to_vplace_instr _ _ _ vb α (&uniq{β} (int * int))). }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_unfold_vplace_uniq_instr _ _ _ vb (PUniq α PHole) (int * int) β).
        simpl. solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_unfold_vplace_prod_instr _ _ _ vb (PUniq α (PUniq β PHole)) int int).
        simpl. solve_typing. }
      { solve_typing. } { reflexivity. }
      (* &mut ( **b).0, at α ⊓ (β ⊓ α) *)
      iApply (type_let with "[]").
      { apply (type_borrow_vplace_deep_instr _ _ _ vb α
          (PUniq α (PUniq β (PFst PHole (OfTy int)))) int); [done|simpl; solve_typing|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iIntros (vr). simpl_subst.
      (* &mut ( **b).1 *)
      iApply (type_let with "[]").
      { apply (type_borrow_vplace_deep_instr _ _ _ vb α
          (PUniq α (PUniq β (PSnd (Blocked int (α ⊓ (β ⊓ α))) PHole))) int);
          [done|simpl; solve_typing|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iIntros (vr2). simpl_subst.
      (* resolve it, and drop b *)
      iApply type_resolve. { solve_typing. } { apply uniq_bor.uniq_resolve. solve_typing. }
      iApply typed_body_tctx_incl.
      { apply (tctx_incl_frame_r +[_] +[]). apply tctx_drop_vplace_uniq; [solve_typing|done|done]. }
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
    intros z _ m1 Hc1 m2 Hc2 Hres Hfin lr junk w ->.
    apply Hspec; [done|]. rewrite Hfin.
    destruct m1 as [[[[[l1 y1] ζi1] d3] g3] idx1].
    destruct m2 as [[[[[l2 y2] ζi2] d4] g4] idx2].
    simpl in Hc1, Hc2, Hres. subst y1 y2.
    rewrite !uniq_bor_future_eq /=. f_equal. f_equal. exact Hres.
  Qed.

  (*
  Writing through a reborrow of a leaf of the nested place, then using the outer borrow
  again:

  ```
  fn set_inner_first<'a, 'b>(x: &'a mut &'b mut (i32, i32)) {
      { let r = &mut ( **x).0; *r = 5; }   // the reborrow ends here
  }
  ```

  with the specification `ensures fin(x) == ((5, ( **old(x)).1), fin( *old(x)))`. After
  the lifetime of the reborrow has ended, the leaf is unblocked
  ([unblock_tctx_vplace_deep]), the nested place is folded back
  ([type_fold_vplace_prod_instr], [type_fold_vplace_uniq_instr]), and `*x` is resolved.
  *)

  Definition set_inner_first : val :=
    fn: ["x"] :=
      let: "b" := !"x" in
      delete [ #1; "x"];;
      Skip;;                                        (* b as a place *)
      ReBor;; ReBor;;                               (* unfold **b, as a pair *)
      Newlft;;
      let: "r" := ReBor;; !"b" in                   (* &mut ( **b).0 *)
      let: "five" := #5 in
      "r" <- "five";;
      Skip;;                                        (* resolve the reborrow *)
      Endlft;;                                      (* unblock ( **b).0 *)
      ReBor;; ReBor;;                               (* fold **b *)
      Skip;;                                        (* resolve b *)
      let: "ret" := new [ #0] in
      return: ["ret"].

  Definition set_inner_first_spec : fn_spec [uniq_borₛ (uniq_borₛ (Zₛ * Zₛ))] () () :=
    λ _ post '-[(_, m)], λ mask π,
      let b := uniq_bor_current (𝔄:=uniq_borₛ (Zₛ * Zₛ)) m in
      uniq_bor_future (𝔄:=uniq_borₛ (Zₛ * Zₛ)) m π =
        ((5%Z, (uniq_bor_current (𝔄:=Zₛ * Zₛ) b).2), uniq_bor_future (𝔄:=Zₛ * Zₛ) b π) →
      ∀ ret, post ret mask π.

  Lemma set_inner_first_type :
    typed_val set_inner_first
      ((fn<(α, β)>(∅; &uniq{α} (&uniq{β} (int * int))) → ()) set_inner_first_spec)
      (set_inner_first, ()).
  Proof.
    unfold set_inner_first. unlock.
    opose proof (@type_fn _ _ _ [uniq_borₛ (uniq_borₛ (Zₛ * Zₛ))] () () ()
      (λ '(α, β), FP ∅ +[&uniq{α} (&uniq{β} (int * int))]%T ()%T AtomicClosed)
      set_inner_first_spec _ [BNamed "x"] _ _ _) as H.
    unlock in H. apply H. clear H.
    intros [α β] ϝ k wl. destruct wl as [vx []]. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply (type_let with "[]").
      { eapply (type_deref_instr (own_ptr 1 (&uniq{α} (&uniq{β} (int * int))))
          (&uniq{α} (&uniq{β} (int * int)))).
        - apply uniq_stack_okay.
        - done.
        - apply (read_own_move (&uniq{α} (&uniq{β} (int * int)))). }
      { apply tctx_extract_elt_here_exact. }
      { reflexivity. }
      iIntros (vb). simpl_subst.
      iApply type_delete. { solve_typing. } { done. } { done. }
      iApply type_seq. { apply (type_uniq_to_vplace_instr _ _ _ vb α (&uniq{β} (int * int))). }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_unfold_vplace_uniq_instr _ _ _ vb (PUniq α PHole) (int * int) β).
        simpl. solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_unfold_vplace_prod_instr _ _ _ vb (PUniq α (PUniq β PHole)) int int).
        simpl. solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply (type_newlft []). iIntros (γ).
      (* &mut ( **b).0, at α ⊓ (β ⊓ γ) *)
      iApply (type_let with "[]").
      { apply (type_borrow_vplace_deep_instr _ _ _ vb γ
          (PUniq α (PUniq β (PFst PHole (OfTy int)))) int); [done|simpl; solve_typing|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iIntros (vr). simpl_subst.
      (* write through the reborrow *)
      iApply type_int. iIntros (v5). simpl_subst.
      iApply type_assign. { solve_typing. } { apply write_uniq. solve_typing. }
      { apply (resolve'_just _ _ _ (const True)). apply resolve_just. }
      iApply type_resolve. { solve_typing. } { apply uniq_bor.uniq_resolve. solve_typing. }
      iApply typed_body_tctx_incl; [apply tctx_incl_resolve_head|].
      (* end γ: unblock ( **b).0 *)
      iApply (type_endlft _ _ _ _ γ).
      { solve_typing. }
      { apply (unblock_tctx_vplace_deep _ _ (PUniq α (PUniq β (PFst PHole (OfTy int)))));
          [done|simpl; solve_typing|].
        apply unblock_tctx_nil. }
      (* fold back, and resolve b *)
      iApply type_seq.
      { apply (type_fold_vplace_prod_instr _ _ _ vb (PUniq α (PUniq β PHole)) int int).
        simpl. solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_fold_vplace_uniq_instr _ _ _ vb (PUniq α PHole) (int * int) β).
        simpl. solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply typed_body_tctx_incl.
      { apply (tctx_vplace_to_uniq _ _ vb α (&uniq{β} (int * int))). }
      iApply type_resolve. { solve_typing. } { apply uniq_bor.uniq_resolve. solve_typing. }
      iApply (type_new_subtype () 0). { lia. } { apply uninit_unit_1. }
      iIntros (vret). simpl_subst.
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lx m] []] mask π. simpl.
    destruct m as [[[[[l [[[[[l' [x1 x2]] ξi'] d1] g1] idx']] ξi] d] g] idx]. simpl.
    intros Hspec. rewrite /trans_upper /trans_tail /=.
    intros z _ m1 Hc1 z0 Hupd Hres0 [x' []] (Hx & Hζ & Hhole & _).
    destruct x' as [[[[[[l'' [[[[[l3 [y1 y2]] ξi3] d3] g3] idx3]] ξi''] d''] g''] idx''] ζis'].
    simpl in Hx, Hζ, Hhole. injection Hx as -> -> -> -> -> -> -> -> -> -> ->.
    simpl. intros d0 g0 idx0 d2 g2 idx1 Hres l1 junk. apply Hspec.
    rewrite !uniq_bor_future_eq.
    rewrite (uniq_prvar_app_irrel (𝔄:=uniq_borₛ (Zₛ * Zₛ)) _ (l', (y1, x2), ξi', d2, g2, idx1) ξi π).
    etrans; [exact Hres|]. f_equal; [f_equal|].
    - destruct m1 as [[[[[l1' w1] ζi] d5] g5] idx5].
      destruct z0 as [[[[[l2 w2] ζi'] d6] g6] idx6].
      destruct Hupd as (_ & -> & ->). simpl in Hres0, Hhole |- *.
      rewrite Hhole /vplace_blk_fin /= -Hres0.
      exact (uniq_prvar_app_irrel (𝔄:=Zₛ) _ 5%Z ζi π).
    - exact (uniq_prvar_app_irrel (𝔄:=Zₛ * Zₛ) (y1, x2) (x1, x2) ξi' π).
    Unshelve. eapply (composeₛ empty_prod_to_unitₛ uninit0_to_unitₛ).
  Qed.
End nested_uniq.

