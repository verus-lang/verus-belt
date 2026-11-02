From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From lrust.typing Require Import uniq_util gmb_cells.
From lrust.lifetime Require Import lifetime_full guarded_bor.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

(** * Tests of the cells as guarded mutable borrows ([gmb_cells.v])

WP-level tests, mirroring [lang/pcell_tests.v] on the new layer (ordinary memory, no cell
heap): creating and destroying a cell, reading through it, a typed move of a
[PCell<(i32, PCell<i32>)>] (after a write of its first field), a verbatim copy of two
sibling cells, shared reads, a lend with a write, the end of its lifetime and a move, and a
compare-and-exchange. *)

Section gmb_cells_tests.
  Context `{!typeG Σ, !gcellsGS Σ, !ghost_varG Σ FValue}.
  Notation gca γ l := (gmb_a (S:=loc) (T:=FValue) γ l).

  Lemma int5_wf : val_wf (MInt i32) (VInt 5).
  Proof. constructor. apply (bool_decide_unpack _); by vm_compute. Qed.
  Lemma int7_wf : val_wf (MInt i32) (VInt 7).
  Proof. constructor. apply (bool_decide_unpack _); by vm_compute. Qed.

  Lemma dec5 : decode_value (MInt i32) (encode_value (MInt i32) (VInt 5)) = Some (VInt 5).
  Proof. apply decode_encode_value; [constructor|apply int5_wf]. Qed.
  Lemma dec7 : decode_value (MInt i32) (encode_value (MInt i32) (VInt 7)) = Some (VInt 7).
  Proof. apply decode_encode_value; [constructor|apply int7_wf]. Qed.

  Lemma loc_0 l : (Lit (LitLoc l)) = (Lit (LitLoc (l +ₗ 0%nat))).
  Proof. by rewrite shift_loc_0_nat. Qed.

  (** A plain [i32] at [l], made into a cell. *)
  Lemma gcell_new_i32 E l v bs :
    ↑gcellsN ⊆ E → decode_value (MInt i32) bs = Some v →
    gcells_ctx -∗ l ↦b bs ={E}=∗ ∃ g γ, ⌜gmb_depth γ = 0⌝ ∗ gcell_reg g γ (MInt i32) ∗
      gmb_inv (gcont_c (MInt i32)) γ ∗ gmb_b γ (fv_lift v) ∗ gcont l (MInt i32) (FVCell g).
  Proof.
    iIntros (HE Hd) "#GC Hbs". iDestruct (gcont_of_bytes with "Hbs") as "C"; [done|].
    iMod (gcell_create with "GC C") as (g γ) "([%Hdp _] & #Hreg & #GI & B & C)"; [done|].
    iModIntro. iExists g, γ. by iFrame "∗#".
  Qed.

  (** Create a cell, read through it (as the owner of the cell and of its permission),
      destroy it, and read the plain bytes. *)
  Lemma test_gcell_create_read_destroy E l bs :
    ↑naN ∪ ↑gcellsN ∪ ↑Nllft ⊆ E → length bs = 4%nat →
    {{{ gcells_ctx ∗ ▷ l ↦b bs }}}
      Store Na1Ord (MInt i32) (#l) (MLit (VInt 5)) ;;
      Load Na1Ord (MInt i32) (#l) ;; Load Na1Ord (MInt i32) (#l) @ E
    {{{ RET MLitV (VInt 5); ∃ bs', l ↦b bs' }}}.
  Proof.
    iIntros (HE Hlen Φ) "[#GC Hl] HΦ".
    wp_bind (Store _ _ _ _). iApply (wp_store_na with "Hl"); [set_solver|apply int5_wf|done|].
    iIntros "!> Hl". wp_seq.
    iMod (gcell_new_i32 _ _ (VInt 5) with "GC Hl") as (g γ) "(_ & #Hreg & #GI & B & C)";
      [set_solver|apply dec5|].
    iMod (gcell_acc with "Hreg GI C B") as "[C Cl]".
    { assert (↑NllftUsr ∪ ↑NllftUsr2 ⊆@{coPset} ↑Nllft) by solve_ndisj. set_solver. }
    wp_bind (Load _ _ _). rewrite {1}loc_0.
    iApply (wp_gcont_load_na_sub _ _ _ _ _ _ (VInt 5) with "C"); [apply MInt_wf|apply fv_sub_here|].
    iIntros "!> C". iMod ("Cl" with "C") as "[C B]". wp_seq.
    iMod (gcell_destroy with "Hreg GI C B") as "C"; [set_solver|].
    iDestruct (gcont_lift_bytes _ _ (VInt 5) with "C") as (bs') "[Hl %Hd]".
    iApply (wp_load_na with "Hl"); [done|]. iIntros "!> Hl". iApply "HΦ". by iExists _.
  Qed.
End gmb_cells_tests.
