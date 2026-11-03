From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type programs cont int product sum uninit value_ctx own shr_bor uniq_util uniq_bor place_own place_shr place_share place_resolve place_write place_sum subtype pcell pcell_borrow.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

(** * Values with cells built from parts

A cell moved out of its box is a value of [PCell<i32>] whose cell is in transit
([val_cells], [typing/gmb_cells.v]). It is a part of a pair built with [MkTuple]
([type_mk_pair_val_instr]) and of a variant built with [MkVariant]
([type_mk_variant_val_instr]): the cells in transit of the whole value are those of its
parts. The whole value is stored into a box, and the cell is used: moved out of the pair
and destroyed ([PCell::into_inner]), or borrowed through the payload of the variant
([PCell::borrow]). *)

Section pcell_parts.
  Context `{!typeG Σ}.

  Notation i32t := (int_ty i32).
  Notation cellt := (pcell_ty (MInt i32)).
  Notation pairₛ := (intₛ i32 * pcellₛ (MInt i32))%ST.

  (*
  ```
  fn pcell_pair() -> i32 {
      let (c, Tracked(perm)) = PCell::new(17);  // c: Box<PCell<i32>>
      let v = *c;                                // move the cell out of c
      let pair = (5, v);                         // a pair built from parts
      let r: Box<(i32, PCell<i32>)> = Box::new(pair);
      let mut s: Box<PCell<i32>> = Box::new_uninit();
      *s = r.1;                                  // move the cell out of the pair
      *s.into_inner(Tracked(perm))
  }
  ```
  *)
  Definition pcell_pair : expr := (
    let: "c" := OfLit (Alloc #4) in
    let: "seventeen" := MLit (VInt 17) in
    ToLit "c" <-{MInt i32} "seventeen";;
    let: "perm" := PCellNew ["c"] in                            (* c: a cell *)
    let: "v" := !ᵐ{MInt i32} (ToLit "c") in                     (* move *c out *)
    (#☠;; delete [ #4; ToLit "c"]);;                            (* drop c (moved out) *)
    let: "five" := MLit (VInt 5) in
    let: "pair" := MkTuple ["five"; "v"] in                     (* (5, v) *)
    let: "r" := OfLit (Alloc #8) in
    ToLit "r" <-{syn_mty pairₛ} "pair";;                        (* *r = pair *)
    let: "s" := OfLit (Alloc #4) in
    let: "w" := !ᵐ{MInt i32} (ToLit "r" +ₗ #4) in               (* move r.1 out *)
    ToLit "s" <-{MInt i32} "w";;                                (* *s = w *)
    ((#☠;; #☠);; delete [ #8; ToLit "r"]);;                      (* drop r *)
    let: "b" := PCellIntoInner ["s"; "perm"] in                 (* s.into_inner(perm) *)
    let: "x" := Load Na1Ord (MInt i32) (ToLit "b") in           (* *b *)
    (#☠;; delete [ #4; ToLit "b"]);;                            (* drop b *)
    jump: "return" ["x"])%E.

  Definition ret_z : predl_trans' [intₛ i32] (intₛ i32) := λ post '-[z], post z.

  Lemma pcell_pair_type ϝ (k: val) :
    ⊢ typed_body [] [ϝ ⊑ₗ []] (InvCtx [] ϝ AtomicClosed)
        [k ◁cont{[ϝ ⊑ₗ []], InvCtx [] ϝ AtomicClosed, λ v: vec val 1, +[vhd v ◁ᵥ i32t] } ret_z]
        +[] (subst "return" k pcell_pair)
        (λ post '-[], λ mask π, post 17%Z mask π).
  Proof.
    rewrite /pcell_pair. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply (type_new_bytes 4); [lia|]. iIntros (vc). simpl_subst.
      iApply (type_let with "[]").
      { apply (type_val_int_instr i32). apply (bool_decide_unpack _); by vm_compute. }
      { solve_typing. } { reflexivity. }
      iIntros (v17). simpl_subst.
      (* *c = 17 *)
      iApply typed_body_tctx_incl.
      { eapply tctx_incl_trans; [apply tctx_incl_swap|]. eapply (tctx_incl_frame_r +[_] +[_]). apply tctx_own_to_oplace. }
      iApply type_seq.
      { eapply (type_write_place_instr _ _ _ vc v17 (POwn 4 PHole) (↯ 4) i32t);
          [by apply pctx_wty_strong|apply uninit_resolve|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iApply typed_body_tctx_incl. { apply tctx_oplace_to_own. }
      (* PCell::new *)
      iApply (type_let with "[]").
      { apply (type_pcell_new_instr 4 i32t). }
      { solve_typing. } { reflexivity. }
      iIntros (vperm). simpl_subst.
      (* move *c out: the cell is in transit *)
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_r +[_] +[_]). apply tctx_own_to_oplace. }
      iApply (type_let with "[]").
      { apply (type_move_place_instr _ _ _ vc (POwn 4 PHole) cellt). done. }
      { solve_typing. } { reflexivity. }
      iIntros (vv). simpl_subst.
      (* drop c *)
      iApply type_seq.
      { apply (type_drop_oplace_instr _ _ _ vc 4 4 (OfTy (↯ 4)) (const (const True)));
          [done|done|done|apply lty_resolve_just]. }
      { solve_typing. } { reflexivity. }
      (* (5, v) *)
      iApply (type_let with "[]").
      { apply (type_val_int_instr i32). apply (bool_decide_unpack _); by vm_compute. }
      { solve_typing. } { reflexivity. }
      iIntros (v5). simpl_subst.
      iApply (type_let with "[]").
      { apply (type_mk_pair_val_instr i32t cellt v5 vv). }
      { solve_typing. } { reflexivity. }
      iIntros (vpair). simpl_subst.
      (* r: a box, uninitialized; *r = pair *)
      iApply (type_new_bytes 8); [lia|]. iIntros (vr). simpl_subst.
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_r +[_] +[_]). apply tctx_own_to_oplace. }
      iApply type_seq.
      { eapply (type_write_place_instr _ _ _ vr vpair (POwn 8 PHole) (↯ 8) (i32t * cellt));
          [by apply pctx_wty_strong|apply uninit_resolve|solve_typing]. }
      { solve_typing. } { reflexivity. }
      (* s: a box, uninitialized; move r.1 into it *)
      iApply (type_new_bytes 4); [lia|]. iIntros (vs). simpl_subst.
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_l _ _ +[_]). eapply (tctx_incl_frame_r +[_] +[_]).
        apply (tctx_unfold_oplace_prod _ _ _ _ PHole i32t cellt). }
      iApply (type_let with "[]").
      { apply (type_move_place_instr _ _ _ vr (POwn 8 (PSnd (OfTy i32t) PHole)) cellt). done. }
      { solve_typing. } { reflexivity. }
      iIntros (vw). simpl_subst.
      (* *s = w *)
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_l _ _ +[_; _]). eapply (tctx_incl_frame_r +[_] +[_]).
        apply tctx_own_to_oplace. }
      iApply type_seq.
      { eapply (type_write_place_instr _ _ _ vs vw (POwn 4 PHole) (↯ 4) cellt);
          [by apply pctx_wty_strong|apply uninit_resolve|solve_typing]. }
      { solve_typing. } { reflexivity. }
      (* drop r *)
      iApply type_seq.
      { apply (type_drop_oplace_instr _ _ _ vr 8 8 (ProdLty (OfTy i32t) (OfTy (↯ 4)))
          (const (const True))); [done|done|done|apply lty_resolve_just]. }
      { solve_typing. } { reflexivity. }
      (* s.into_inner(perm) *)
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_r +[_] +[_]). apply tctx_oplace_to_own. }
      iApply (type_let with "[]").
      { apply (type_pcell_into_inner_instr 4 i32t vs vperm). }
      { solve_typing. } { reflexivity. }
      iIntros (vb). simpl_subst.
      (* *b *)
      iApply (type_let with "[]").
      { apply (type_load_own_bytes_copy_instr 4 i32t vb). apply _. }
      { solve_typing. } { reflexivity. }
      iIntros (vx). simpl_subst.
      (* drop b *)
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_r +[_] +[_]). apply tctx_own_to_oplace. }
      iApply type_seq.
      { apply (type_drop_oplace_instr _ _ _ vb 4 4 (OfTy i32t) (const (const True)));
          [done|done|done|apply lty_resolve_just]. }
      { solve_typing. } { reflexivity. }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [] mask π Hspec. rewrite /trans_upper /trans_tail /ret_z /=.
    intros. simpl. intros. split; [done|]. intros _. done.
  Qed.

  Notation pairt := (pcell_ty (MInt i32) * cell_points_to_ty i32t)%T.
  Notation pair'ₛ := (pcellₛ (MInt i32) * trackedₛ (pcellₛ (syn_mty (intₛ i32)) * intₛ i32))%ST.
  Notation optt := (Σ! +[(); pairt])%T.
  Notation optₛ := (Σ! [unitₛ; pair'ₛ])%ST.

  (** A branch that the specification rules out. *)
  Local Lemma typed_body_false {𝔄l 𝔅} E L I (C: cctx 𝔅) (T: tctx 𝔄l) e :
    ⊢ typed_body E L I C T e (λ _ _ _ _, False%type).
  Proof.
    iIntros (?????) "_ _ #PROPH _ _ _ _ _ _ Obs".
    iMod (proph_obs_false with "PROPH Obs") as "[]"; [solve_ndisj|by intros ??].
  Qed.

  (*
  ```
  fn pcell_variant() -> i32 {
      let (c, Tracked(perm)) = PCell::new(17);  // c: Box<PCell<i32>>
      let cp = ( *c, perm);                      // the cell, moved out of c, with its permission
      let o: Box<Option<(PCell<i32>, PointsTo<i32>)>> = Box::new(Some(cp));
      match &*o {
          None => unreachable!(),
          Some(r) => *r.0.borrow(Tracked(&r.1)),
      }
  }
  ```
  *)
  Definition pcell_variant : expr := (
    let: "c" := OfLit (Alloc #4) in
    let: "seventeen" := MLit (VInt 17) in
    ToLit "c" <-{MInt i32} "seventeen";;
    let: "perm" := PCellNew ["c"] in                            (* c: a cell *)
    let: "v" := !ᵐ{MInt i32} (ToLit "c") in                     (* move *c out *)
    (#☠;; delete [ #4; ToLit "c"]);;                            (* drop c (moved out) *)
    let: "cp" := MkTuple ["v"; "perm"] in                       (* (v, perm) *)
    let: "opt" := MkVariant 1 "cp" in                           (* Some(cp) *)
    let: "o" := OfLit (Alloc #5) in
    ToLit "o" <-{syn_mty optₛ} "opt";;                          (* *o = opt *)
    case: ToLit (Load Na1Ord (MInt (sum_tag [unitₛ; pair'ₛ])) (ToLit "o")) of
    [ jump: "return" ["o"];                                     (* None: unreachable *)
      Newlft;;                                                  (* Some(r) *)
      let: "r" := &ˢ (ToLit "o" +ₗ #1) in                       (* r: &(PCell, PointsTo) *)
      let: "pcell_ref" := OfLit (ToLit "r") in                   (* &r.0 *)
      let: "perm_ref" := OfLit (ToLit "r" +ₗ #4) in              (* &r.1 *)
      let: "intref" := PCellBorrow ["pcell_ref"; "perm_ref"] in
      let: "x" := Load Na1Ord (MInt i32) (ToLit "intref") in     (* *intref *)
      Endlft;;
      (#☠;; delete [ #5; ToLit "o"]);;                          (* drop o *)
      jump: "return" ["x"]])%E.

  Lemma pcell_variant_type ϝ (k: val) :
    ⊢ typed_body [] [ϝ ⊑ₗ []] (InvCtx [] ϝ AtomicClosed)
        [k ◁cont{[ϝ ⊑ₗ []], InvCtx [] ϝ AtomicClosed, λ v: vec val 1, +[vhd v ◁ᵥ i32t] } ret_z]
        +[] (subst "return" k pcell_variant)
        (λ post '-[], λ mask π, post 17%Z mask π).
  Proof.
    rewrite /pcell_variant. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply (type_new_bytes 4); [lia|]. iIntros (vc). simpl_subst.
      iApply (type_let with "[]").
      { apply (type_val_int_instr i32). apply (bool_decide_unpack _); by vm_compute. }
      { solve_typing. } { reflexivity. }
      iIntros (v17). simpl_subst.
      (* *c = 17 *)
      iApply typed_body_tctx_incl.
      { eapply tctx_incl_trans; [apply tctx_incl_swap|]. eapply (tctx_incl_frame_r +[_] +[_]). apply tctx_own_to_oplace. }
      iApply type_seq.
      { eapply (type_write_place_instr _ _ _ vc v17 (POwn 4 PHole) (↯ 4) i32t);
          [by apply pctx_wty_strong|apply uninit_resolve|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iApply typed_body_tctx_incl. { apply tctx_oplace_to_own. }
      (* PCell::new *)
      iApply (type_let with "[]").
      { apply (type_pcell_new_instr 4 i32t). }
      { solve_typing. } { reflexivity. }
      iIntros (vperm). simpl_subst.
      (* move *c out: the cell is in transit *)
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_r +[_] +[_]). apply tctx_own_to_oplace. }
      iApply (type_let with "[]").
      { apply (type_move_place_instr _ _ _ vc (POwn 4 PHole) cellt). done. }
      { solve_typing. } { reflexivity. }
      iIntros (vv). simpl_subst.
      (* drop c *)
      iApply type_seq.
      { apply (type_drop_oplace_instr _ _ _ vc 4 4 (OfTy (↯ 4)) (const (const True)));
          [done|done|done|apply lty_resolve_just]. }
      { solve_typing. } { reflexivity. }
      (* Some((v, perm)) *)
      iApply (type_let with "[]").
      { apply (type_mk_pair_val_instr cellt (cell_points_to_ty i32t) vv vperm). }
      { solve_typing. } { reflexivity. }
      iIntros (vcp). simpl_subst.
      iApply (type_let with "[]").
      { apply (type_mk_variant_val_instr +[(); pairt]%T 1%fin). done. }
      { solve_typing. } { reflexivity. }
      iIntros (vopt). simpl_subst.
      (* o: a box, uninitialized; *o = opt *)
      iApply (type_new_bytes 5); [lia|]. iIntros (vo). simpl_subst.
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_r +[_] +[_]). apply tctx_own_to_oplace. }
      iApply type_seq.
      { eapply (type_write_place_instr _ _ _ vo vopt (POwn 5 PHole) (↯ 5) optt);
          [by apply pctx_wty_strong|apply uninit_resolve|solve_typing]. }
      { solve_typing. } { reflexivity. }
      (* match *o *)
      iApply (type_case_oplace _ _ _ _ vo 5 PHole +[(); pairt]%T _ _ _
        -[λ _ _ _ _, False%type; _]).
      iSplitL; [iApply typed_body_false|iSplitL; [|done]]. simpl.
      (* Some(r): share the payload *)
      iApply (type_newlft []). iIntros (κ).
      iApply (type_let with "[]").
      { eapply (type_share_place_instr _ _ _ vo
          (POwn 5 (PSum +[(); pairt]%T 1%fin (1%positive, (1%positive, 0%Z)) PHole)) κ (OfTy pairt) pairt);
          [apply lty_sleaf_ofty; solve_typing|simpl; solve_typing..]. }
      { solve_typing. } { reflexivity. }
      iIntros (vr). simpl_subst.
      iApply typed_body_tctx_incl.
      { apply (copy_val_tctx_incl _ _ _ _ _ (Copy0:=shr_bytes_copy κ pairt)). }
      iApply (type_let with "[]").
      { apply (type_shr_bytes_fst_instr κ (pcell_ty (MInt i32)) (cell_points_to_ty i32t)). }
      { solve_typing. } { reflexivity. }
      iIntros (vpc). simpl_subst.
      iApply (type_let with "[]").
      { apply (type_shr_bytes_snd_instr κ (pcell_ty (MInt i32)) (cell_points_to_ty i32t)). }
      { solve_typing. } { reflexivity. }
      iIntros (vpt). simpl_subst.
      (* borrow the contents, and read them *)
      iApply (type_let with "[]").
      { apply (type_pcell_borrow_instr κ i32t vpc vpt). }
      { solve_typing. } { reflexivity. }
      iIntros (vi). simpl_subst.
      iApply (type_let with "[]").
      { apply (type_load_shr_bytes_copy_instr κ i32t); [apply _|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iIntros (vx). simpl_subst.
      iApply typed_body_tctx_incl. { apply tctx_incl_resolve_head. }
      (* end κ: unblock the payload; drop o *)
      iApply (type_endlft _ _ _ _ κ).
      { solve_typing. }
      { apply unblock_tctx_cons_just.
        apply (unblock_tctx_oplace_shr _ _ _ (PSum +[(); pairt]%T 1%fin (1%positive, (1%positive, 0%Z)) PHole) pairt).
        apply unblock_tctx_nil. }
      iApply type_seq.
      { apply (type_drop_oplace_instr _ _ _ vo 5 5 (SumLty +[(); pairt]%T 1%fin (OfTy pairt))
          (const (const True))); [done|done|done|apply lty_resolve_just]. }
      { solve_typing. } { reflexivity. }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [] mask π Hspec. rewrite /trans_upper /trans_tail /ret_z /=.
    intros. simpl. split; [done|]. intros [x' [y' []]] [<- _] _. done.
  Qed.
End pcell_parts.

Print Assumptions pcell_pair_type.
Print Assumptions pcell_variant_type.
