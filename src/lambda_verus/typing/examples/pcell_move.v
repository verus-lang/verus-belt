From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type programs cont int unit uninit value_ctx own uniq_util place_own place_resolve place_write subtype pcell.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

(** * Moves of values that contain cells

Typed moves ([Load] of a place, [Store] of the loaded value) of values that contain
[PCell]s, without [NoCell]: the generic move rules move the cells (GMB instances,
[typing/gmb_cells.v]) with the moved value. A cell is moved out of its box into the second
field of a pair; the pair (whose fancy value is [FVTuple [FVInt 5; FVCell g]]) is moved
into another box; its cell field is moved into a third box, and the contents of the cell
are read back through [PCell::into_inner]. *)

Section pcell_move.
  Context `{!typeG Σ}.

  Notation i32t := (int_ty i32).
  Notation cellt := (pcell_ty (wfm (MInt i32))).
  (* The struct of an [i32] and a [PCell<i32>], laid out as the split of [↯ 8]
     ([uninit_pair_layout]). *)
  Notation UL := (uninit_pair_layout 4 4).
  Notation pairₛ := (structₛ UL [intₛ i32; pcellₛ (wfm (MInt i32))]).
  Notation pairt := (struct_ty UL +[i32t; cellt]).

  (*
  ```
  fn pcell_move() -> i32 {
      let (c, Tracked(perm)) = PCell::new(17);  // c: Box<PCell<i32>>
      let mut q: Box<(i32, PCell<i32>)> = Box::new_uninit();
      q.0 = 5;
      q.1 = *c;                                  // move the cell out of c
      let mut r: Box<(i32, PCell<i32>)> = Box::new_uninit();
      *r = *q;                                   // move the pair
      let mut s: Box<PCell<i32>> = Box::new_uninit();
      *s = r.1;                                  // move the cell out of the pair
      *s.into_inner(Tracked(perm))
  }
  ```
  *)
  Definition pcell_move : expr := (
    let: "c" := (Alloc #4) in
    let: "seventeen" := MLit (VInt 17) in
    "c" <-{MInt i32} "seventeen";;
    let: "perm" := PCellNew ["c"] in                            (* c: a cell *)
    let: "q" := (Alloc #8) in
    let: "five" := MLit (VInt 5) in
    ("q" +ₗ #(struct_off UL [uninitₛ 4; uninitₛ 4] 0)) <-{MInt i32} "five";;  (* q.0 = 5 *)
    let: "v" := !ᵐ{MInt i32} "c" in                     (* move *c out *)
    ("q" +ₗ #(struct_off UL [intₛ i32; uninitₛ 4] 1)) <-{MInt i32} "v";;  (* q.1 = v *)
    (#☠;; delete [ #4; "c"]);;                            (* drop c (moved out) *)
    let: "r" := (Alloc #8) in
    let: "pair" := !ᵐ{syn_mty pairₛ} "q" in             (* move *q out *)
    "r" <-{syn_mty pairₛ} "pair";;                        (* *r = pair *)
    (#☠;; delete [ #8; "q"]);;                            (* drop q (moved out) *)
    let: "s" := (Alloc #4) in
    let: "w" := !ᵐ{MInt i32} ("r" +ₗ #(struct_off UL [intₛ i32; pcellₛ (wfm (MInt i32))] 1)) in
                                                          (* move r.1 out *)
    "s" <-{MInt i32} "w";;                                (* *s = w *)
    ((#☠;; (#☠;; #☠));; delete [ #8; "r"]);;               (* drop r *)
    let: "b" := PCellIntoInner ["s"; "perm"] in                 (* s.into_inner(perm) *)
    let: "x" := Load Na1Ord (MInt i32) "b" in           (* *b *)
    (#☠;; delete [ #4; "b"]);;                            (* drop b *)
    jump: "return" ["x"])%E.

  Definition ret_z : predl_trans' [intₛ i32] (intₛ i32) := λ post '-[z], post z.

  Lemma pcell_move_type ϝ (k: val) :
    ⊢ typed_body [] [ϝ ⊑ₗ []] (InvCtx [] ϝ AtomicClosed)
        [k ◁cont{[ϝ ⊑ₗ []], InvCtx [] ϝ AtomicClosed, λ v: vec val 1, +[vhd v ◁ᵥ i32t] } ret_z]
        +[] (subst "return" k pcell_move)
        (λ post '-[], λ mask π, post 17%Z mask π).
  Proof.
    rewrite /pcell_move. simpl_subst.
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
      { eapply (type_write_place_instr _ _ _ vc v17 (POwn 4 PHole) (OfTy (↯ 4)) i32t);
          [by apply pctx_wty_strong|apply uninit_resolve|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iApply typed_body_tctx_incl. { apply tctx_oplace_to_own. }
      (* PCell::new *)
      iApply (type_let with "[]").
      { apply (type_pcell_new_instr 4 i32t). }
      { solve_typing. } { reflexivity. }
      iIntros (vperm). simpl_subst.
      (* q: a box of a pair, uninitialized *)
      iApply (type_new_bytes 8); [lia|]. iIntros (vq). simpl_subst.
      iApply typed_body_tctx_incl.
      { apply (tctx_subtype_own_bytes 8 (↯ (4 + 4)) (struct_ty UL +[↯ 4; ↯ 4]%T)
          uninit_split_structₛ).
        apply uninit_plus_struct_1. }
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_r +[_] +[_]).
        eapply tctx_incl_trans; [apply tctx_own_to_oplace|].
        apply (tctx_unfold_oplace_struct _ _ _ _ UL PHole +[↯ 4; ↯ 4]%T). }
      (* q.0 = 5 *)
      iApply (type_let with "[]").
      { apply (type_val_int_instr i32). apply (bool_decide_unpack _); by vm_compute. }
      { solve_typing. } { reflexivity. }
      iIntros (v5). simpl_subst.
      iApply type_seq.
      { eapply (type_write_place_instr _ _ _ vq v5 (POwn 8 (PField UL +[] PHole +[OfTy (↯ 4)])) (OfTy (↯ 4)) i32t);
          [by apply pctx_wty_strong|apply uninit_resolve|solve_typing]. }
      { solve_typing. } { reflexivity. }
      (* move *c out: the cell is in transit *)
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_l _ _ +[_]). eapply (tctx_incl_frame_r +[_] +[_]).
        apply tctx_own_to_oplace. }
      iApply (type_let with "[]").
      { apply (type_move_place_instr _ _ _ vc (POwn 4 PHole) cellt). }
      { solve_typing. } { reflexivity. }
      iIntros (vv). simpl_subst.
      (* q.1 = v *)
      iApply type_seq.
      { eapply (type_write_place_instr _ _ _ vq vv (POwn 8 (PField UL +[OfTy i32t] PHole +[])) (OfTy (↯ 4)) cellt);
          [by apply pctx_wty_strong|apply uninit_resolve|solve_typing]. }
      { solve_typing. } { reflexivity. }
      (* drop c *)
      iApply type_seq.
      { apply (type_drop_oplace_instr _ _ _ vc 4 4 (Moved cellt) (const (const True)));
          [done|done|done|apply lty_resolve_just]. }
      { solve_typing. } { reflexivity. }
      (* r: a box, uninitialized; move the pair *q into it *)
      iApply (type_new_bytes 8); [lia|]. iIntros (vr). simpl_subst.
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_l _ _ +[_]). eapply (tctx_incl_frame_r +[_] +[_]).
        apply (tctx_fold_oplace_struct _ _ _ _ UL PHole +[i32t; cellt]). }
      iApply (type_let with "[]").
      { apply (type_move_place_instr _ _ _ vq (POwn 8 PHole) pairt). }
      { solve_typing. } { reflexivity. }
      iIntros (vpair). simpl_subst.
      (* *r = pair *)
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_l _ _ +[_; _]). eapply (tctx_incl_frame_r +[_] +[_]).
        apply tctx_own_to_oplace. }
      iApply type_seq.
      { eapply (type_write_place_instr _ _ _ vr vpair (POwn 8 PHole) (OfTy (↯ 8)) pairt);
          [by apply pctx_wty_strong|apply uninit_resolve|solve_typing]. }
      { solve_typing. } { reflexivity. }
      (* drop q *)
      iApply type_seq.
      { apply (type_drop_oplace_instr _ _ _ vq 8 8 (Moved pairt) (const (const True)));
          [done|done|done|apply lty_resolve_just]. }
      { solve_typing. } { reflexivity. }
      (* s: a box, uninitialized; move r.1 into it *)
      iApply (type_new_bytes 4); [lia|]. iIntros (vs). simpl_subst.
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_l _ _ +[_]). eapply (tctx_incl_frame_r +[_] +[_]).
        apply (tctx_unfold_oplace_struct _ _ _ _ UL PHole +[i32t; cellt]). }
      iApply (type_let with "[]").
      { apply (type_move_place_instr _ _ _ vr (POwn 8 (PField UL +[OfTy i32t] PHole +[])) cellt). }
      { solve_typing. } { reflexivity. }
      iIntros (vw). simpl_subst.
      (* *s = w *)
      iApply typed_body_tctx_incl.
      { eapply (tctx_incl_frame_l _ _ +[_; _]). eapply (tctx_incl_frame_r +[_] +[_]).
        apply tctx_own_to_oplace. }
      iApply type_seq.
      { eapply (type_write_place_instr _ _ _ vs vw (POwn 4 PHole) (OfTy (↯ 4)) cellt);
          [by apply pctx_wty_strong|apply uninit_resolve|solve_typing]. }
      { solve_typing. } { reflexivity. }
      (* drop r *)
      iApply type_seq.
      { apply (type_drop_oplace_instr _ _ _ vr 8 8 (StructLty UL +[OfTy i32t; Moved cellt])
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
End pcell_move.

Print Assumptions pcell_move_type.
