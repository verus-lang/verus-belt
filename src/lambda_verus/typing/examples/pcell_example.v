From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type programs cont int product uninit value_ctx own shr_bor uniq_util uniq_bor place_own place_shr place_share place_resolve place_write subtype pcell pcell_borrow.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

(** * [PCell] on bytes

A box is initialized with [17], made into a cell ([PCellFromOwn]: the box holds the pair of
the cell and its permission), both fields are shared, the contents are borrowed through them
([PCellBorrow], which gives a shared reference [&shr{κ} i32] to the contents) and read with
the generic rule for shared references ([type_load_shr_bytes_copy_instr]). The body is
stated as a function body ([typed_body], with the return continuation [k]) that returns
the value read, and its specification says that this value is [17] (instead of the call
of [assert] of the legacy example). *)

Section pcell_example.
  Context `{!typeG Σ}.

  Notation i32t := (int_ty i32).

  (*
  ```
  fn pcell_example() -> i32 {
      let (pcell, Tracked(pointsto)) = PCell::new(17);
      let pcell_shr_ref = &pcell;
      let tracked pointsto_shr_ref = &pointsto;
      let intref = pcell_shr_ref.borrow(Tracked(pointsto_shr_ref));
      *intref
  }
  ```
  *)
  Definition pcell_example_b : expr := (
    let: "p" := (Alloc #4) in                         (* a box of 4 bytes *)
    let: "seventeen" := MLit (VInt 17) in
    "p" <-{MInt i32} "seventeen";;                    (* *p = 17 *)
    let: "pair" := PCellFromOwn ["p"] in                    (* (PCell, PointsTo) *)
    Newlft;;
    let: "r" := &ˢ "pair" in                         (* &pair *)
    let: "pcell_ref" := "r" in                 (* &pair.0 *)
    let: "perm_ref" := ("r" +ₗ #4) in            (* &pair.1 *)
    let: "intref" := PCellBorrow ["pcell_ref"; "perm_ref"] in
    let: "x" := Load Na1Ord (MInt i32) "intref" in   (* *intref *)
    Endlft;;
    (#☠;; delete [ #4; "pair"]);;                      (* drop the pair *)
    jump: "return" ["x"])%E.

  Definition ret_z : predl_trans' [intₛ i32] (intₛ i32) := λ post '-[z], post z.

  Notation pairt := (pcell_ty (wfm (MInt i32)) * cell_points_to_ty i32t)%T.

  Lemma pcell_example_type ϝ (k: val) :
    ⊢ typed_body [] [ϝ ⊑ₗ []] (InvCtx [] ϝ AtomicClosed)
        [k ◁cont{[ϝ ⊑ₗ []], InvCtx [] ϝ AtomicClosed, λ v: vec val 1, +[vhd v ◁ᵥ i32t] } ret_z]
        +[] (subst "return" k pcell_example_b)
        (λ post '-[], λ mask π, post 17%Z mask π).
  Proof.
    rewrite /pcell_example_b. simpl_subst.
    iApply (typed_body_impl with "[]"); last first. {
      iApply (type_new_bytes 4); [lia|]. iIntros (vp). simpl_subst.
      iApply (type_let with "[]").
      { apply (type_val_int_instr i32). apply (bool_decide_unpack _); by vm_compute. }
      { solve_typing. } { reflexivity. }
      iIntros (v17). simpl_subst.
      (* *p = 17, through p as an owned place *)
      iApply typed_body_tctx_incl.
      { eapply tctx_incl_trans; [apply tctx_incl_swap|]. eapply (tctx_incl_frame_r +[_] +[_]). apply tctx_own_to_oplace. }
      iApply type_seq.
      { eapply (type_write_place_instr _ _ _ vp v17 (POwn 4 PHole) (OfTy (↯ 4)) i32t);
          [by apply pctx_wty_strong|apply uninit_resolve|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iApply typed_body_tctx_incl. { apply tctx_oplace_to_own. }
      (* PCell::new *)
      iApply (type_let with "[]").
      { apply (type_pcell_from_own_instr 4 i32t). }
      { solve_typing. } { reflexivity. }
      iIntros (vpair). simpl_subst.
      iApply (type_newlft []). iIntros (κ).
      (* &pair, and its fields *)
      iApply typed_body_tctx_incl. { apply tctx_own_to_oplace. }
      iApply (type_let with "[]").
      { eapply (type_share_place_instr _ _ _ vpair (POwn 4 PHole) κ (OfTy pairt) pairt);
          [apply lty_sleaf_ofty; solve_typing|simpl; solve_typing..]. }
      { solve_typing. } { reflexivity. }
      iIntros (vr). simpl_subst.
      iApply typed_body_tctx_incl.
      { apply (copy_val_tctx_incl _ _ _ _ _ (Copy0:=shr_bytes_copy κ pairt)). }
      iApply (type_let with "[]").
      { apply (type_shr_bytes_fst_instr κ (pcell_ty (wfm (MInt i32))) (cell_points_to_ty i32t)). }
      { solve_typing. } { reflexivity. }
      iIntros (vpc). simpl_subst.
      iApply (type_let with "[]").
      { apply (type_shr_bytes_snd_instr κ (pcell_ty (wfm (MInt i32))) (cell_points_to_ty i32t)). }
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
      (* end κ: unblock the pair; drop it *)
      iApply (type_endlft _ _ _ _ κ).
      { solve_typing. }
      { apply unblock_tctx_cons_just. apply (unblock_tctx_oplace_shr _ _ _ PHole pairt). apply unblock_tctx_nil. }
      iApply type_seq.
      { apply (type_drop_oplace_instr _ _ _ vpair 4 4 (OfTy pairt) (const (const True)));
          [done|done|done|apply lty_resolve_just]. }
      { solve_typing. } { reflexivity. }
      iApply type_jump.
      { rewrite elem_of_list_singleton. reflexivity. }
      { solve_typing. }
      { solve_typing. }
      { reflexivity. }
    }
    intros post [] mask π Hspec. rewrite /trans_upper /trans_tail /ret_z /=.
    intros l junk _ g. split; [done|]. intros [x' [y' []]] [<- _] _. done.
  Qed.
End pcell_example.

Print Assumptions pcell_example_type.
