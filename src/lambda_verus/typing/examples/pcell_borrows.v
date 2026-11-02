From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type programs cont int product uninit value_ctx own shr_bor uniq_util uniq_bor place_own place_shr place_share place_puniq place_resolve place_read place_write subtype pcell pcell_borrow.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

(** * Borrows of the contents of a [PCell], with the unified place rules

Phase 4 of [design_docs/guarded-mutable-borrows-plan.md]: [PCell::borrow_mut] gives a unique
borrow [&uniq{κ} ty] of the contents, and [PCell::borrow] a shared reference [&shr{γ} ty];
below them, the generic place rules apply. A box of a pair is made into a cell; through
[borrow_mut], the first field of the pair is reborrowed (at [β ⊑ κ]) and written; after the
lifetimes end, the contents are borrowed with [borrow] and the first field is read through
the shared reference; after that borrow ends, the cell is moved into another box (the generic
move rule, which moves the contents of the cell with it), and destroyed with [into_inner]. *)

Section pcell_borrows.
  Context `{!typeG Σ}.

  Notation i32t := (int_ty i32).
  Notation pairt := (i32t * i32t)%T.
  Notation pm := (syn_mty (intₛ i32 * intₛ i32)).
  Notation cellt := (pcell_ty pairt.(ty_mty)).
  Notation permt := (cell_points_to_ty pairt).

  (*
  ```
  fn pcell_borrows(b: Box<(i32, i32)>) -> i32 {
      let (c, Tracked(perm)) = PCell::from_own(b);    // c: Box<(PCell<(i32, i32)>, PointsTo)>
      'α: { 'κ: {
          let m = c.0.borrow_mut(Tracked(&mut c.1));  // m: &'κ mut (i32, i32)
          'β: { let m0 = &mut ( *m).0; *m0 = 7; }      // a reborrow below the cell borrow
      } }
      let x = 'γ: { let s = c.0.borrow(Tracked(&c.1)); ( *s).0 };
      let d = Box::new(c.0);                           // move the cell after the borrows end
      let e = d.into_inner(Tracked(c.1));
      x
  }
  ```
  *)
  Definition pcell_borrows : expr := (
    let: "c" := PCellFromOwn ["b"] in                       (* c: (PCell, PointsTo) *)
    Newlft;;                                                (* α *)
    Newlft;;                                                (* κ ⊑ α *)
    let: "r" := &ˢ (ToLit "c") in                           (* &c.0, at α *)
    let: "q" := &ᵘ (ToLit "c" +ₗ #8) in                     (* &mut c.1, at κ *)
    let: "m" := PCellBorrowMut ["r"; "q"] in                (* m: &'κ mut (i32, i32) *)
    Skip;;                                                  (* m as a place *)
    ReBor;;                                                 (* unfold *m *)
    Newlft;;                                                (* β ⊑ κ *)
    let: "m0" := &ᵘ (ToLit "m") in                          (* &mut ( *m).0, at β *)
    let: "seven" := MLit (VInt 7) in
    Skip;;                                                  (* m0 as a place *)
    ToLit "m0" <-{MInt i32} "seven";;                       (* *m0 = 7 *)
    Skip;;                                                  (* resolve m0 *)
    Endlft;;                                                (* end β: unblock ( *m).0 *)
    ReBor;;                                                 (* fold *m *)
    Skip;;                                                  (* resolve m *)
    Endlft;;                                                (* end κ: unblock c.1 *)
    Endlft;;                                                (* end α: unblock c.0 *)
    Newlft;;                                                (* γ *)
    let: "rc" := &ˢ (ToLit "c") in                          (* &c *)
    let: "r2" := OfLit (ToLit "rc") in                      (* &c.0 *)
    let: "q2" := OfLit (ToLit "rc" +ₗ #8) in                (* &c.1 *)
    let: "s" := PCellBorrow ["r2"; "q2"] in                 (* s: &'γ (i32, i32) *)
    let: "x" := !ᶜ{MInt i32} (ToLit "s") in                 (* ( *s).0 *)
    Endlft;;                                                (* end γ: unblock c *)
    let: "d" := OfLit (Alloc #8) in                         (* d: Box<PCell<(i32, i32)>> *)
    let: "v" := !ᵐ{pm} (ToLit "c") in                       (* move c.0 out *)
    ToLit "d" <-{pm} "v";;                                  (* *d = v *)
    let: "pt" := !ᵐ{zst_mty} (ToLit "c" +ₗ #8) in           (* move c.1 out *)
    ((#☠;; #☠);; delete [ #8; ToLit "c"]);;                 (* drop c (moved out) *)
    let: "e" := PCellIntoInner ["d"; "pt"] in               (* d.into_inner(pt) *)
    (#☠;; delete [ #8; ToLit "e"]);;                        (* drop e *)
    jump: "return" ["x"])%E.

  Definition ret_z : predl_trans' [intₛ i32] (intₛ i32) := λ post '-[z], post z.

  Lemma pcell_borrows_type ϝ (k vb: val) :
    ⊢ typed_body [] [ϝ ⊑ₗ []] (InvCtx [] ϝ AtomicClosed)
        [k ◁cont{[ϝ ⊑ₗ []], InvCtx [] ϝ AtomicClosed, λ v: vec val 1, +[vhd v ◁ᵥ i32t] } ret_z]
        +[vb ◁ᵥ own_bytes 8 pairt]
        (subst "return" k (subst "b" vb pcell_borrows))
        (λ post '-[_], λ mask π, post 7%Z mask π).
  Proof.
    rewrite /pcell_borrows. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      (* PCell::from_own *)
      iApply (type_let with "[]").
      { apply (type_pcell_from_own_instr 8 pairt). }
      { solve_typing. } { reflexivity. }
      iIntros (vc). simpl_subst.
      iApply (type_newlft []). iIntros (α).
      iApply (type_newlft [α]). iIntros (κ).
      (* c as an owned place, unfolded *)
      iApply typed_body_tctx_incl.
      { eapply tctx_incl_trans; [apply tctx_own_to_oplace|].
        apply (tctx_unfold_oplace_prod _ _ _ _ PHole cellt permt). }
      (* &c.0 at α *)
      iApply (type_let with "[]").
      { eapply (type_share_place_instr _ _ _ vc (POwn 8 (PFst PHole (OfTy permt))) α
          (OfTy cellt) cellt); [apply lty_sleaf_ofty; solve_typing|simpl; solve_typing..]. }
      { solve_typing. } { reflexivity. }
      iIntros (vr). simpl_subst.
      (* &mut c.1 at κ *)
      iApply (type_let with "[]").
      { eapply (type_borrow_place_instr _ _ _ vc (POwn 8 (PSnd (ShrBlocked cellt α) PHole)) κ permt);
          solve_typing. }
      { solve_typing. } { simpl. reflexivity. }
      iIntros (vq). simpl_subst.
      (* the shared reference to the cell, at κ *)
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_l _ _ +[_; _]).
        apply (tctx_subtype_shr_bytes α κ cellt cellt idₛ); [solve_typing|apply subtype_refl]. }
      (* PCell::borrow_mut *)
      iApply (type_let with "[]").
      { apply (type_pcell_borrow_mut_instr κ pairt vr vq). solve_typing. }
      { solve_typing. } { reflexivity. }
      iIntros (vm). simpl_subst.
      (* m as a place; unfold *m *)
      iApply type_seq. { apply (type_uniq_to_vplace_instr _ _ _ vm κ pairt). }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { apply (type_unfold_vplace_prod_instr _ _ _ vm (PUniq κ PHole) i32t i32t). simpl. solve_typing. }
      { solve_typing. } { reflexivity. }
      (* the reborrow &mut ( *m).0 at β *)
      iApply (type_newlft [κ]). iIntros (β).
      iApply (type_let with "[]").
      { apply (type_borrow_place_instr _ _ _ vm (PUniq κ (PFst PHole (OfTy i32t))) β i32t);
          [solve_typing|simpl; solve_typing..]. }
      { solve_typing. } { simpl. reflexivity. }
      iIntros (vm0). simpl_subst.
      (* *m0 = 7, through m0 as a place; resolve m0 *)
      iApply (type_let with "[]").
      { apply (type_val_int_instr i32). apply (bool_decide_unpack _); by vm_compute. }
      { solve_typing. } { reflexivity. }
      iIntros (v7). simpl_subst.
      iApply type_seq. { apply (type_uniq_to_vplace_instr _ _ _ vm0 β i32t). }
      { solve_typing. } { reflexivity. }
      iApply type_seq.
      { eapply (type_write_place_instr _ _ _ vm0 v7 (PUniq β PHole) i32t i32t);
          [apply pctx_wty_same|apply resolve_just|simpl; solve_typing]. }
      { solve_typing. } { simpl. reflexivity. }
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_r +[_] +[_]). apply tctx_vplace_to_uniq. }
      iApply type_seq.
      { apply (type_resolve_val_instr vm0 (&uniq{β} i32t)). apply uniq_bor.uniq_resolve. solve_typing. }
      { solve_typing. } { reflexivity. }
      (* end β: unblock ( *m).0 *)
      iApply (type_endlft _ _ _ _ β).
      { solve_typing. }
      { (* (the unblock relation, computed: it does not mention the local lifetime) *)
        simpl. eapply unblock_tctx_impl; last first.
        { apply (unblock_tctx_vplace_deep _ _ (PUniq κ (PFst PHole (OfTy i32t))) i32t);
            [done|solve_typing|]. apply unblock_tctx_cons_just, unblock_tctx_nil. }
        intros π xl xl' H. unfold vplace_blk_fin in H. cbn [pctx_get pctx_set pctx_vpath] in H. exact H. }
      (* fold *m; m back as a unique borrow, resolved *)
      iApply type_seq.
      { apply (type_fold_vplace_prod_instr _ _ _ vm (PUniq κ PHole) i32t i32t). simpl. solve_typing. }
      { solve_typing. } { reflexivity. }
      iApply typed_body_tctx_incl. { eapply (tctx_incl_frame_r +[_] +[_]). apply tctx_vplace_to_uniq. }
      iApply type_seq.
      { apply (type_resolve_val_instr vm (&uniq{κ} pairt)). apply uniq_bor.uniq_resolve. solve_typing. }
      { solve_typing. } { reflexivity. }
      (* end κ: unblock c.1; end α: unblock c.0 *)
      iApply (type_endlft _ _ _ _ κ).
      { solve_typing. }
      { eapply unblock_tctx_impl; last first.
        { apply (unblock_tctx_oplace _ _ _ (PSnd (ShrBlocked cellt α) PHole) permt); [solve_typing|].
          apply unblock_tctx_nil. }
        intros π xl xl' H. unfold oplace_blk_fin in H. cbn [pctx_get pctx_set pctx_path] in H. exact H. }
      iApply (type_endlft _ _ _ _ α).
      { solve_typing. }
      { apply (unblock_tctx_oplace_shr _ _ _ (PFst PHole (OfTy permt)) cellt).
        apply unblock_tctx_nil. }
      (* &c, at γ, and its fields *)
      iApply (type_newlft []). iIntros (γ).
      iApply typed_body_tctx_incl. { apply (tctx_fold_oplace_prod _ _ _ _ PHole cellt permt). }
      iApply (type_let with "[]").
      { eapply (type_share_place_instr _ _ _ vc (POwn 8 PHole) γ (OfTy (cellt * permt))
          (cellt * permt)); [apply lty_sleaf_ofty; solve_typing|simpl; solve_typing..]. }
      { solve_typing. } { reflexivity. }
      iIntros (vrc). simpl_subst.
      iApply typed_body_tctx_incl.
      { apply (copy_val_tctx_incl _ _ _ _ _ (Copy0:=shr_bytes_copy γ (cellt * permt))). }
      iApply (type_let with "[]").
      { apply (type_shr_bytes_fst_instr γ cellt permt). }
      { solve_typing. } { reflexivity. }
      iIntros (vr2). simpl_subst.
      iApply (type_let with "[]").
      { apply (type_shr_bytes_snd_instr γ cellt permt). }
      { solve_typing. } { reflexivity. }
      iIntros (vq2). simpl_subst.
      (* PCell::borrow *)
      iApply (type_let with "[]").
      { apply (type_pcell_borrow_instr γ pairt vr2 vq2). }
      { solve_typing. } { reflexivity. }
      iIntros (vs). simpl_subst.
      (* ( *s).0, through s as a place rooted at its value *)
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_r +[_] +[_]).
        eapply tctx_incl_trans; [apply tctx_ty_to_vplace|].
        eapply tctx_incl_trans; [apply tctx_vplace_unfold_shr|].
        apply (tctx_change_vplace_shr _ _ vs γ PHole (OfTy pairt)
          (ProdLty (OfTy i32t) (OfTy i32t))); [done|done|by intros]. }
      iApply (type_let with "[]").
      { apply (type_read_place_instr _ _ _ vs (PShr γ (PFst PHole (OfTy i32t)))
          (OfTy i32t) i32t static); [by split|apply _|solve_typing]. }
      { solve_typing. } { simpl. reflexivity. }
      iIntros (vx). simpl_subst.
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_l _ _ +[_]). eapply (tctx_incl_frame_r +[_] +[]).
        apply tctx_drop_vplace_shr. }
      (* end γ: unblock c *)
      iApply (type_endlft _ _ _ _ γ).
      { solve_typing. }
      { apply unblock_tctx_cons_just.
        apply (unblock_tctx_oplace_shr _ _ _ PHole (cellt * permt)). apply unblock_tctx_nil. }
      (* d: a box; move c.0 into it *)
      iApply (type_new_bytes 8); [lia|]. iIntros (vd). simpl_subst.
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_l _ _ +[_; _]).
        apply (tctx_unfold_oplace_prod _ _ _ _ PHole cellt permt). }
      iApply (type_let with "[]").
      { apply (type_move_place_instr _ _ _ vc (POwn 8 (PFst PHole (OfTy permt))) cellt). done. }
      { solve_typing. } { reflexivity. }
      iIntros (vv). simpl_subst.
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_l _ _ +[_; _]). eapply (tctx_incl_frame_r +[_] +[_]).
        apply tctx_own_to_oplace. }
      iApply type_seq.
      { eapply (type_write_place_instr _ _ _ vd vv (POwn 8 PHole) (↯ 8) cellt);
          [by apply pctx_wty_strong|apply uninit_resolve|solve_typing]. }
      { solve_typing. } { reflexivity. }
      (* move c.1 out; drop c *)
      iApply (type_let with "[]").
      { apply (type_move_place_instr _ _ _ vc
          (POwn 8 (PSnd (OfTy (↯ (seq_size [MInt i32; MInt i32]))) PHole)) permt). done. }
      { solve_typing. } { reflexivity. }
      iIntros (vpt). simpl_subst.
      iApply type_seq.
      { apply (type_drop_oplace_instr _ _ _ vc 8 8 (ProdLty (OfTy (↯ 8)) (OfTy (↯ 0)))
          (const (const True))); [done|done|done|apply lty_resolve_just]. }
      { solve_typing. } { reflexivity. }
      (* d.into_inner(pt) *)
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_l _ _ +[_]). eapply (tctx_incl_frame_r +[_] +[_]).
        apply tctx_oplace_to_own. }
      iApply (type_let with "[]").
      { apply (type_pcell_into_inner_instr 8 pairt vd vpt). }
      { solve_typing. } { reflexivity. }
      iIntros (ve). simpl_subst.
      (* drop e *)
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_r +[_] +[_]). apply tctx_own_to_oplace. }
      iApply type_seq.
      { apply (type_drop_oplace_instr _ _ _ ve 8 8 (OfTy pairt) (const (const True)));
          [done|done|done|apply lty_resolve_just]. }
      { solve_typing. } { reflexivity. }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [[lb [a b]] []] mask π Hspec. rewrite /trans_upper /trans_tail /ret_z /=.
    intros g m1 Hm1.
    destruct m1 as [[[[[l1 [g1 [a1 b1]]] ξ1] d1] gg1] idx1]. simpl in Hm1. injection Hm1 as <- <- <-.
    rewrite /trans_lower /=. split; [done|].
    intros [[[[[l2 [a2 b2]] ξ2] d2] gg2] idx2] Hc2 Hf2 Hg2 Hl2. simpl in Hc2, Hl2. injection Hc2 as <- <-. subst l2.
    intros [[[[[l3 c3] ξ3] d3] gg3] idx3] Hc3 _ d4 g4 idx4 Hres3. simpl in Hc3, Hres3. subst c3.
    intros [x5 [x6 []]] (Hx5 & Hb5 & Hv5 & Hx6 & _). simpl in Hx5, Hb5, Hv5, Hx6. subst x6.
    destruct x5 as [[[[[[l5 [a5 b5]] ξ5] d5] gg5] idx5] bm5]. simpl in Hx5, Hb5, Hv5. injection Hx5 as -> <- -> -> -> ->.
    intros d6 g6 idx6 Hres5. simpl in Hres5.
    intros [x7 []] (Hx7a & Hx7b & Hx7c & Hx7d & _). simpl in Hx7a, Hx7b, Hx7c, Hx7d.
    intros [x8 []] [-> _]. simpl.
    (* the final value of the permission *)
    have H7 : a5 = 7%Z.
    { rewrite Hv5 (uniq_util.uniq_prvar_app_irrel (𝔄:=intₛ i32) a2 7%Z ξ3 π). exact Hres3. }
    have Hp : (π (uniq_prvar (𝔄:=trackedₛ (pcellₛ pm * (intₛ i32 * intₛ i32))) (g1, (a2, b5)) ξ1)).1
      = (g1, (7%Z, b5)).
    { rewrite !uniq_bor_future_eq in Hf2 Hg2.
      assert (∀ p : positive * (Z * Z), p.1 = g1 → p.2 = (7%Z, b5) → p = (g1, (7%Z, b5))) as Hpair.
      { intros [??] ??. simpl in *. congruence. }
      apply Hpair; [exact Hg2|]. rewrite -Hf2 -H7 -Hres5.
      exact (uniq_util.uniq_prvar_app_irrel (𝔄:=intₛ i32 * intₛ i32) (a2, b5) (a5, b5) ξ2 π). }
    destruct x7 as [[l7 [g7 [g7' [a7 b7]]]] bm7]. simpl in Hx7a, Hx7b, Hx7c, Hx7d.
    injection Hx7b as ->. rewrite Hp in Hx7d. injection Hx7d as -> -> ->.
    split; [done|].
    intros [y [x9 []]] [Hy [-> _]] _ _. simpl in Hy. subst y.
    intros _ _. split; [done|]. intros _. exact Hspec.
  Qed.
End pcell_borrows.

Print Assumptions pcell_borrows_type.
