From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type programs cont int product uninit value_ctx own_bytes
  shr_bytes uniq_util uniq_bytes place_own place_shr place_resolve subtype pcell_bytes
  pcell_bytes_borrow.
From lrust.lang Require Import lang notation new_delete.
Set Default Proof Using "Type".

(** * [PCell] on bytes

The example of [typing/examples/pcell_example.v] on the byte layer (§10 step 5 of
[design_docs/pcell-multibyte-cells.md]): a box is initialized with [17], made into a cell
([PCellbFromOwn]: the box holds the pair of the cell and its permission), both fields are
shared, the contents are borrowed through them ([PCellbBorrow]) and read. The body is
stated as a function body ([typed_body], with the return continuation [k]) that returns
the value read, and its specification says that this value is [17] (instead of the call
of [assert] of the legacy example). *)

Section pcell_example_bytes.
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
    let: "p" := OfLit (Alloc #4) in                         (* a box of 4 bytes *)
    let: "seventeen" := MLit (VInt 17) in
    Store Na1Ord (MInt i32) (ToLit "p") "seventeen";;       (* *p = 17 *)
    let: "pair" := PCellbFromOwn ["p"] in                    (* (PCell, PointsTo) *)
    Newlft;;
    let: "r" := Share;; OfLit (ToLit "pair") in              (* &pair *)
    let: "pcell_ref" := OfLit (ToLit "r") in                 (* &pair.0 *)
    let: "perm_ref" := OfLit (ToLit "r" +ₗ #4) in            (* &pair.1 *)
    let: "intref" := PCellbBorrow ["pcell_ref"; "perm_ref"] in
    let: "x" := Load Na1Ord (MInt i32) (ToLit "intref") in   (* *intref *)
    Endlft;;
    (#☠;; delete [ #4; ToLit "pair"]);;                      (* drop the pair *)
    jump: "return" ["x"])%E.

  Definition ret_z : predl_trans' [intₛ i32] (intₛ i32) := λ post '-[z], post z.

  Notation pairt := (pcellb_ty (MInt i32) * bcell_points_to_ty i32t)%T.

  Lemma pcell_example_b_type ϝ (k: val) :
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
      { apply (type_write_oplace_instr _ _ _ vp v17 4 PHole (↯ 4) i32t (const (const True)));
          [done|apply uninit_resolve|done]. }
      { solve_typing. } { reflexivity. }
      iApply typed_body_tctx_incl. { apply tctx_oplace_to_own. }
      (* PCell::new *)
      iApply (type_let with "[]").
      { apply (type_pcellb_from_own_instr 4 i32t). rewrite /ty_bsize -ty_mty_eq /=. lia. }
      { solve_typing. } { reflexivity. }
      iIntros (vpair). simpl_subst.
      iApply (type_newlft []). iIntros (κ).
      (* &pair, and its fields *)
      iApply typed_body_tctx_incl. { apply tctx_own_to_oplace. }
      iApply (type_let with "[]").
      { apply (type_share_oplace_instr _ _ _ vpair 4 κ PHole pairt); solve_typing. }
      { solve_typing. } { reflexivity. }
      iIntros (vr). simpl_subst.
      iApply typed_body_tctx_incl.
      { apply (copy_val_tctx_incl _ _ _ _ _ (Copy0:=shr_bytes_copy κ pairt)). }
      iApply (type_let with "[]").
      { apply (type_shr_bytes_fst_instr κ (pcellb_ty (MInt i32)) (bcell_points_to_ty i32t)). }
      { solve_typing. } { reflexivity. }
      iIntros (vpc). simpl_subst.
      iApply (type_let with "[]").
      { apply (type_shr_bytes_snd_instr κ (pcellb_ty (MInt i32)) (bcell_points_to_ty i32t)). }
      { solve_typing. } { reflexivity. }
      iIntros (vpt). simpl_subst.
      (* borrow the contents, and read them *)
      iApply (type_let with "[]").
      { apply (type_pcellb_borrow_instr κ i32t vpc vpt). }
      { solve_typing. } { reflexivity. }
      iIntros (vi). simpl_subst.
      iApply (type_let with "[]").
      { apply (type_bcell_shr_load_instr κ i32t); [apply _|solve_typing]. }
      { solve_typing. } { reflexivity. }
      iIntros (vx). simpl_subst.
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
End pcell_example_bytes.

Print Assumptions pcell_example_b_type.
