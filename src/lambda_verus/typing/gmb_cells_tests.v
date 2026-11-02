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
  Context `{!typeG Σ, !ghost_varG Σ FValue}.
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
    gcells_ctx -∗ l ↦b bs ={E}=∗ ∃ g γ, gcell_reg g γ (MInt i32) ∗
      gmb_inv (gcont_c (MInt i32)) γ ∗ gmb_b γ (fv_lift v) ∗ gcont l (MInt i32) (FVCell g).
  Proof.
    iIntros (HE Hd) "#GC Hbs". iDestruct (gcont_of_bytes with "Hbs") as "C"; [done|].
    iMod (gcell_create with "GC C") as (g γ) "(_ & #Hreg & #GI & B & C)"; [done|].
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
    iMod (gcell_new_i32 _ _ (VInt 5) with "GC Hl") as (g γ) "(#Hreg & #GI & B & C)";
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
  (** ** A [PCell<(i32, PCell<i32>)>] *)
  Definition pair_mty : mty := MTuple [(0%nat, MInt i32); (4%nat, MInt i32)] 8.

  Lemma pair_mty_wf : mty_wf pair_mty.
  Proof.
    constructor.
    - intros [|[|i]] [|[|j]] o1 m1 o2 m2 Hij; simpl; try done;
        intros [= <- <-] [= <- <-]; simpl; lia.
    - repeat constructor; simpl; lia.
    - repeat constructor.
  Qed.

  Lemma pair_in_field i : (i < 8)%nat → in_field [(0%nat, MInt i32); (4%nat, MInt i32)] i.
  Proof.
    intros Hi. destruct (decide (i < 4)%nat).
    - exists (0%nat, MInt i32). split; [set_solver|simpl; lia].
    - exists (4%nat, MInt i32). split; [set_solver|simpl; lia].
  Qed.

  Lemma frepr_pair R fbs0 fbs1 fv0 fv1 :
    length fbs0 = 4%nat → length fbs1 = 4%nat →
    frepr R (MInt i32) fbs0 fv0 → frepr R (MInt i32) fbs1 fv1 →
    frepr R pair_mty (fbs0 ++ fbs1) (FVTuple [fv0; fv1]).
  Proof.
    intros Hl0 Hl1 H0 H1. apply frepr_tuple.
    - rewrite length_app. lia.
    - done.
    - intros [|[|k]] f fv; simpl; try done; intros [= <-] [= <-]; simpl.
      + rewrite /list_slice drop_0 take_app_length' //.
      + rewrite /list_slice drop_app_length' // take_ge //. lia.
    - intros i fb Hi Hnf. exfalso. apply Hnf, pair_in_field. apply lookup_lt_Some in Hi.
      rewrite length_app in Hi. lia.
  Qed.

  Lemma gcells_pair l fv0 fv1 :
    gcells l pair_mty (FVTuple [fv0; fv1]) ⊣⊢
    gcells l (MInt i32) fv0 ∗ gcells (l +ₗ 4) (MInt i32) fv1.
  Proof. rewrite /pair_mty gcells_tuple /= shift_loc_0_nat right_id. done. Qed.

  (** The contents of the outer cell: a plain [i32] and the inner cell (or any contents). *)
  Lemma gcont_pair_intro l v bs fv1 :
    decode_value (MInt i32) bs = Some v →
    l ↦b bs -∗ gcont (l +ₗ 4) (MInt i32) fv1 -∗ gcont l pair_mty (FVTuple [fv_lift v; fv1]).
  Proof.
    iIntros (Hd) "Hbs (%R1 & %fbs1 & Hfb1 & [%Hrep1 %HR1] & Hc1)".
    have Hl1 := frepr_length _ _ _ _ HR1 Hrep1. have Hl0 := decode_value_length _ _ _ Hd.
    iExists R1, ((inr <$> bs) ++ fbs1). rewrite gfbytes_app gfbytes_bytes length_fmap Hl0.
    iFrame "Hbs Hfb1". iSplit.
    - iPureIntro. split; [|done]. apply frepr_pair; [by rewrite length_fmap|done|by constructor|done].
    - rewrite gcells_pair. iFrame "Hc1". iApply gcells_lift.
  Qed.

  Lemma gcont_pair_cells l g0 g1 :
    gcont l (MInt i32) (FVCell g0) -∗ gcont (l +ₗ 4) (MInt i32) (FVCell g1) -∗
    gcont l pair_mty (FVTuple [FVCell g0; FVCell g1]).
  Proof.
    iIntros "C0 C1". iDestruct (gcont_cell_inv with "C0") as (γ0) "[#Hreg0 Ha0]".
    iDestruct (gcont_cell_inv with "C1") as (γ1) "[#Hreg1 Ha1]".
    iExists (<[g0 := (MInt i32, replicate 4 g0)]> {[g1 := (MInt i32, replicate 4 g1)]}),
      ((inl <$> replicate 4 g0) ++ (inl <$> replicate 4 g1)).
    rewrite gfbytes_app !gfbytes_cells. iSplit; [done|]. iSplit.
    - iPureIntro. split.
      + apply frepr_pair; [done|done|constructor; by rewrite lookup_insert|constructor].
        destruct (decide (g1 = g0)) as [->|Hne]; [by rewrite lookup_insert|].
        by rewrite lookup_insert_ne // lookup_singleton.
      + intros g m cs. rewrite lookup_insert_Some lookup_singleton_Some.
        intros [[_ [= <- <-]]|[_ [_ [= <- <-]]]]; done.
    - rewrite gcells_pair /=. iSplitL "Ha0"; [iExists γ0; by iFrame "Hreg0 Ha0"|].
      iExists γ1. by iFrame "Hreg1 Ha1".
  Qed.

  Lemma gcont_pair_cell2 l fv0 g1 :
    gcont l pair_mty (FVTuple [fv0; FVCell g1]) -∗ gcont (l +ₗ 4) (MInt i32) (FVCell g1).
  Proof.
    iIntros "(%R & %fbs & _ & _ & Hc)". rewrite gcells_pair /=.
    iDestruct "Hc" as "[_ [%γ1 [Hreg Ha]]]". by iApply (gcont_cell with "Hreg Ha").
  Qed.

  Lemma gcont_pair_cell1 l g0 fv1 :
    gcont l pair_mty (FVTuple [FVCell g0; fv1]) -∗ gcont l (MInt i32) (FVCell g0).
  Proof.
    iIntros "(%R & %fbs & _ & _ & Hc)". rewrite gcells_pair /=.
    iDestruct "Hc" as "[[%γ0 [Hreg Ha]] _]". by iApply (gcont_cell with "Hreg Ha").
  Qed.

  Lemma gcont_pair_cells_inv l g0 g1 :
    gcont l pair_mty (FVTuple [FVCell g0; FVCell g1]) -∗
    gcont l (MInt i32) (FVCell g0) ∗ gcont (l +ₗ 4) (MInt i32) (FVCell g1).
  Proof.
    iIntros "(%R & %fbs & _ & _ & Hc)". rewrite gcells_pair /=.
    iDestruct "Hc" as "[[%γ0 [Hreg0 Ha0]] [%γ1 [Hreg1 Ha1]]]".
    iSplitL "Hreg0 Ha0"; [by iApply (gcont_cell with "Hreg0 Ha0")|by iApply (gcont_cell with "Hreg1 Ha1")].
  Qed.

  (** Write the first field of a [PCell<(i32, PCell<i32>)>] (as the owner of the cell and of
      its permission), move the outer cell by a typed copy (which moves the inner one along,
      re-encoding the bytes), destroy the outer cell, read the first field, destroy the inner
      cell, and read it. *)
  Lemma test_gcell_nested_move E l l' bs1 bs2 bs' :
    ↑naN ∪ ↑gcellsN ∪ lazyE ⊆ E →
    decode_value (MInt i32) bs1 = Some (VInt 5) → decode_value (MInt i32) bs2 = Some (VInt 9) →
    length bs' = 8%nat →
    {{{ gcells_ctx ∗ £ 1 ∗ l ↦b bs1 ∗ (l +ₗ 4) ↦b bs2 ∗ ▷ l' ↦b bs' }}}
      Store Na1Ord (MInt i32) (#l) (MLit (VInt 7)) ;;
      Store Na1Ord pair_mty (#l') (Load Na1Ord pair_mty (#l)) ;;
      Load Na1Ord (MInt i32) (#l') ;;
      Load Na1Ord (MInt i32) (#(l' +ₗ 4)) @ E
    {{{ RET MLitV (VInt 9); ∃ bs, l ↦b bs }}}.
  Proof.
    iIntros (HE Hd1 Hd2 Hlen Φ) "(#GC & Lc & Hl1 & Hl2 & Hl') HΦ".
    have HllftUsr : ↑NllftUsr ∪ ↑NllftUsr2 ⊆@{coPset} E.
    { trans lazyE; [apply lazyE_NllftUsr|set_solver]. }
    have HNllft : ↑Nllft ⊆@{coPset} E. { trans lazyE; [rewrite /lazyE; set_solver|set_solver]. }
    iMod (gcell_new_i32 _ (l +ₗ 4) (VInt 9) with "GC Hl2") as (g1 γ1) "(#Hreg1 & #GI1 & B1 & C1)";
      [set_solver|done|].
    iDestruct (gcont_pair_intro _ (VInt 5) with "Hl1 C1") as "C0"; [done|].
    iMod (gcell_create with "GC C0") as (g0 γ0) "(_ & #Hreg0 & #GI0 & B0 & C0)"; [set_solver|].
    (* write the first field *)
    iMod (gcell_acc with "Hreg0 GI0 C0 B0") as "[C Cl]"; [done|].
    wp_bind (Store _ _ _ _). rewrite {1}loc_0.
    iApply (wp_gcont_store_na_sub _ _ _ _ _ _ (VInt 5) (VInt 7) (FVTuple [FVInt 7; FVCell g1])
      with "C"); [set_solver|apply pair_mty_wf|apply int7_wf| |].
    { apply (fv_repl_field [(0%nat, MInt i32); (4%nat, MInt i32)] 8 [FVInt 5; FVCell g1] 0 0
        (MInt i32) (FVInt 5) 0 (MInt i32) (FVInt 5) (FVInt 7) (FVInt 7)); [done|done|constructor]. }
    iIntros "!> C". iMod ("Cl" with "C") as "[C0 B0]". wp_seq.
    (* move the outer cell *)
    wp_bind (Store _ _ _ _).
    iApply (wp_gcont_move with "[$GC $Lc $C0 $Hl']"); [set_solver|apply pair_mty_wf|done|].
    iIntros "!>" (bs) "[Hl C0]". wp_seq.
    (* destroy it at its new location, and read the first field *)
    iMod (gcell_destroy with "Hreg0 GI0 C0 B0") as "C"; [done|].
    wp_bind (Load _ _ _). rewrite {1}loc_0.
    iApply (wp_gcont_load_na_sub _ _ _ _ _ (MInt i32) (VInt 7) with "C"); [apply pair_mty_wf| |].
    { apply (fv_sub_field [(0%nat, MInt i32); (4%nat, MInt i32)] 8 [FVInt 7; FVCell g1] 0 0
        (MInt i32) (FVInt 7) 0 (MInt i32) (FVInt 7)); [done|done|constructor]. }
    iIntros "!> C". wp_seq.
    (* the inner cell is at its new location: destroy it, and read it *)
    iDestruct (gcont_pair_cell2 with "C") as "C1".
    iMod (gcell_destroy with "Hreg1 GI1 C1 B1") as "C1"; [done|].
    iDestruct (gcont_lift_bytes _ _ (VInt 9) with "C1") as (bs2') "[Hl2 %Hd2']".
    iApply (wp_load_na with "Hl2"); [done|]. iIntros "!> _". iApply "HΦ". by iExists _.
  Qed.

  (** Two sibling cells [(PCell<i32>, PCell<i32>)], moved together by a verbatim copy. *)
  Lemma test_gcell_siblings_memcopy E l l' bs1 bs2 bs' :
    ↑naN ∪ ↑gcellsN ∪ lazyE ⊆ E →
    decode_value (MInt i32) bs1 = Some (VInt 5) → decode_value (MInt i32) bs2 = Some (VInt 9) →
    length bs' = 8%nat →
    {{{ gcells_ctx ∗ £ 1 ∗ l ↦b bs1 ∗ (l +ₗ 4) ↦b bs2 ∗ ▷ l' ↦b bs' }}}
      MemCopy Na1Ord 8 (#l') (#l) ;;
      Load Na1Ord (MInt i32) (#l') ;;
      Load Na1Ord (MInt i32) (#(l' +ₗ 4)) @ E
    {{{ RET MLitV (VInt 9); ∃ bs, l ↦b bs }}}.
  Proof.
    iIntros (HE Hd1 Hd2 Hlen Φ) "(#GC & Lc & Hl1 & Hl2 & Hl') HΦ".
    have HNllft : ↑Nllft ⊆@{coPset} E. { trans lazyE; [rewrite /lazyE; set_solver|set_solver]. }
    iMod (gcell_new_i32 _ l (VInt 5) with "GC Hl1") as (g0 γ0) "(#Hreg0 & #GI0 & B0 & C0)";
      [set_solver|done|].
    iMod (gcell_new_i32 _ (l +ₗ 4) (VInt 9) with "GC Hl2") as (g1 γ1) "(#Hreg1 & #GI1 & B1 & C1)";
      [set_solver|done|].
    iDestruct (gcont_pair_cells with "C0 C1") as "C".
    wp_bind (MemCopy _ _ _ _).
    iApply (wp_gcont_memcopy _ _ _ pair_mty with "[$GC $Lc $C $Hl']"); [set_solver|apply pair_mty_wf|done|].
    iIntros "!>" (bs) "[Hl C]". wp_seq.
    iDestruct (gcont_pair_cells_inv with "C") as "[C0 C1]".
    iMod (gcell_destroy with "Hreg0 GI0 C0 B0") as "C0"; [done|].
    iDestruct (gcont_lift_bytes _ _ (VInt 5) with "C0") as (bs0') "[Hl0 %Hd0']".
    wp_bind (Load _ _ _). iApply (wp_load_na with "Hl0"); [done|]. iIntros "!> _". wp_seq.
    iMod (gcell_destroy with "Hreg1 GI1 C1 B1") as "C1"; [done|].
    iDestruct (gcont_lift_bytes _ _ (VInt 9) with "C1") as (bs1') "[Hl1 %Hd1']".
    iApply (wp_load_na with "Hl1"); [done|]. iIntros "!> _". iApply "HΦ". by iExists _.
  Qed.
  (** Shared reads (non-atomic and atomic) through guards of the move right and of the
      permission ((L2)); here both are owned, and guarded by themselves. *)
  Lemma test_gcell_shared_read E l bs :
    ↑naN ∪ ↑gcellsN ∪ ↑Nllft ⊆ E → length bs = 4%nat →
    {{{ gcells_ctx ∗ ▷ l ↦b bs }}}
      Store Na1Ord (MInt i32) (#l) (MLit (VInt 5)) ;;
      Load Na1Ord (MInt i32) (#l) ;; Load ScOrd (MInt i32) (#l) @ E
    {{{ RET MLitV (VInt 5); ∃ g γ, gcell_reg g γ (MInt i32) ∗ gcont l (MInt i32) (FVCell g) ∗
          gmb_b γ (FVInt 5) }}}.
  Proof.
    iIntros (HE Hlen Φ) "[#GC Hl] HΦ".
    wp_bind (Store _ _ _ _). iApply (wp_store_na with "Hl"); [set_solver|apply int5_wf|done|].
    iIntros "!> Hl". wp_seq.
    iMod (gcell_new_i32 _ _ (VInt 5) with "GC Hl") as (g γ) "(#Hreg & #GI & B & C)";
      [set_solver|apply dec5|].
    iDestruct (gcont_cell_inv with "C") as (γ') "[Hreg' A]".
    iDestruct (gcell_reg_agree with "Hreg Hreg'") as %[<- _].
    iAssert ((gca γ l ∗ gmb_b γ (FVInt 5)) &&{↑naN; 0}&&> gca γ l)%I as "#Ga".
    { iApply guards_weaken_sep_l. }
    iAssert ((gca γ l ∗ gmb_b γ (FVInt 5)) &&{↑naN; 0}&&> gmb_b γ (FVInt 5))%I as "#Gb".
    { iApply guards_weaken_sep_r. }
    iMod lc_zero as "Lc".
    wp_bind (Load _ _ _). rewrite {1}loc_0.
    iApply (wp_gcell_load_na_shared _ γ l (MInt i32) (FVInt 5) 0 (MInt i32) (VInt 5) _ 0
      with "[$GI $Ga $Gb $A $B $Lc]"); [set_solver|apply MInt_wf|apply fv_sub_here|].
    iIntros "!> [A B]". wp_seq. iMod lc_zero as "Lc". rewrite loc_0.
    iApply (wp_gcell_load_sc_shared _ γ l (MInt i32) (FVInt 5) 0 (MInt i32) (VInt 5) _ 0
      with "[$GI $Ga $Gb $A $B $Lc]"); [set_solver|apply MInt_wf|apply fv_sub_here|].
    iIntros "!> [A B]". iApply "HΦ". iExists g, γ. iSplitR; [done|].
    iSplitL "A"; [by iApply (gcont_cell with "Hreg A")|done].
  Qed.

  Lemma int9_wf : val_wf (MInt i32) (VInt 9).
  Proof. constructor. apply (bool_decide_unpack _); by vm_compute. Qed.

  (** A compare-and-exchange of the contents of a cell (by the owner of the cell and of its
      permission), a failing one, then an atomic shared read. *)
  Lemma test_gcell_mcas E l bs :
    ↑naN ∪ ↑gcellsN ∪ ↑Nllft ⊆ E → length bs = 4%nat →
    {{{ gcells_ctx ∗ ▷ l ↦b bs }}}
      Store Na1Ord (MInt i32) (#l) (MLit (VInt 5)) ;;
      MCAS (MInt i32) (#l) (MLit (VInt 5)) (MLit (VInt 7)) ;;
      MCAS (MInt i32) (#l) (MLit (VInt 5)) (MLit (VInt 9)) ;;
      Load ScOrd (MInt i32) (#l) @ E
    {{{ RET MLitV (VInt 7); ∃ g γ, gcell_reg g γ (MInt i32) ∗ gcont l (MInt i32) (FVCell g) ∗
          gmb_b γ (FVInt 7) }}}.
  Proof.
    iIntros (HE Hlen Φ) "[#GC Hl] HΦ".
    have HllftUsr : ↑NllftUsr ∪ ↑NllftUsr2 ⊆@{coPset} E.
    { assert (↑NllftUsr ∪ ↑NllftUsr2 ⊆@{coPset} ↑Nllft) by solve_ndisj. set_solver. }
    wp_bind (Store _ _ _ _). iApply (wp_store_na with "Hl"); [set_solver|apply int5_wf|done|].
    iIntros "!> Hl". wp_seq.
    iMod (gcell_new_i32 _ _ (VInt 5) with "GC Hl") as (g γ) "(#Hreg & #GI & B & C)";
      [set_solver|apply dec5|].
    iMod (gcell_acc with "Hreg GI C B") as "[C Cl]"; [done|].
    wp_bind (MCAS _ _ _ _). rewrite {1}loc_0.
    iApply (wp_gcont_mcas_sub _ _ _ _ _ _ (VInt 5) (VInt 5) (VInt 7) (FVInt 7) with "C");
      [set_solver|apply MInt_wf|apply int7_wf|constructor|].
    iIntros "!>" (b) "[[[-> _] C]|[[_ %Hne] _]]"; [|done].
    iMod ("Cl" with "C") as "[C B]". wp_seq.
    iMod (gcell_acc with "Hreg GI C B") as "[C Cl]"; [done|].
    wp_bind (MCAS _ _ _ _). rewrite {1}loc_0.
    iApply (wp_gcont_mcas_sub _ _ _ _ _ _ (VInt 7) (VInt 5) (VInt 9) (FVInt 9) with "C");
      [set_solver|apply MInt_wf|apply int9_wf|constructor|].
    iIntros "!>" (b) "[[[_ %Heq] _]|[[-> _] C]]"; [done|].
    iMod ("Cl" with "C") as "[C B]". wp_seq.
    iDestruct (gcont_cell_inv with "C") as (γ') "[Hreg' A]".
    iDestruct (gcell_reg_agree with "Hreg Hreg'") as %[<- _].
    iAssert ((gca γ l ∗ gmb_b γ (FVInt 7)) &&{↑naN; 0}&&> gca γ l)%I as "#Ga".
    { iApply guards_weaken_sep_l. }
    iAssert ((gca γ l ∗ gmb_b γ (FVInt 7)) &&{↑naN; 0}&&> gmb_b γ (FVInt 7))%I as "#Gb".
    { iApply guards_weaken_sep_r. }
    iMod lc_zero as "Lc". rewrite loc_0.
    iApply (wp_gcell_load_sc_shared _ γ l (MInt i32) (FVInt 7) 0 (MInt i32) (VInt 7) _ 0
      with "[$GI $Ga $Gb $A $B $Lc]"); [set_solver|apply MInt_wf|apply fv_sub_here|].
    iIntros "!> [A B]". iApply "HΦ". iExists g, γ. iSplitR; [done|].
    iSplitL "A"; [by iApply (gcont_cell with "Hreg A")|done].
  Qed.
  Lemma step_fupd_frame_Nllft E (P : iProp Σ) :
    ↑Nllft ⊆ E → (|={↑Nllft}[∅]▷=> P) ⊢ |={E}[E∖↑Nllft]▷=> P.
  Proof.
    intros HE. rewrite (step_fupd_mask_frame_r _ _ (E∖↑Nllft)); [|set_solver|set_solver].
    rewrite -union_difference_L // left_id_L. done.
  Qed.

  (** (L3) and (L4): the owner shares the move right at [κ], the permission holder lends
      the permission (with its value tracked by a ghost variable); a write through the
      borrow; the end of [κ] (during a [Skip]); the lender gets back the permission at the
      final value, the owner the move right, and the cell is moved by a verbatim copy and
      destroyed. *)
  Lemma test_gcell_lend_write_end_move E l l' bs bs' :
    ↑naN ∪ ↑gcellsN ∪ lazyE ⊆ E → length bs = 4%nat → length bs' = 4%nat →
    {{{ llft_ctx ∗ gcells_ctx ∗ £ 2 ∗ ▷ l ↦b bs ∗ ▷ l' ↦b bs' }}}
      Store Na1Ord (MInt i32) (#l) (MLit (VInt 5)) ;;
      Store Na1Ord (MInt i32) (#l) (MLit (VInt 7)) ;;
      Skip ;;
      MemCopy Na1Ord 4 (#l') (#l) ;;
      Load Na1Ord (MInt i32) (#l') @ E
    {{{ RET MLitV (VInt 7); ∃ bs1, l ↦b bs1 }}}.
  Proof using All.
    iIntros (HE Hlen Hlen' Φ) "(#LFT & #GC & Lc & Hl & Hl') HΦ".
    iDestruct (lc_split 1 1 with "Lc") as "[Lc1 Lc2]".
    have HNllft : ↑Nllft ⊆@{coPset} E. { trans lazyE; [rewrite /lazyE; set_solver|set_solver]. }
    wp_bind (Store _ _ _ _). iApply (wp_store_na with "Hl"); [set_solver|apply int5_wf|done|].
    iIntros "!> Hl". wp_seq.
    iMod (gcell_new_i32 _ _ (VInt 5) with "GC Hl") as (g γ) "(#Hreg & #GI & B & C)";
      [set_solver|apply dec5|].
    iDestruct (gcont_cell_inv with "C") as (γ') "[Hreg' A]".
    iDestruct (gcell_reg_agree with "Hreg Hreg'") as %[<- _].
    iMod (ghost_var_alloc (FVInt 5)) as (γv) "[V1 V2]".
    iMod (llftl_begin with "LFT") as (κ) "[Alive #End]"; [done|].
    (* the owner shares the move right; the permission holder lends the permission *)
    iMod (llftl_borrow_shared _ κ (gca γ l) with "[A]") as "[#Ga InhA]"; [done|by iNext|].
    iDestruct (guards_remove_later_rhs with "Ga") as "#Ga'".
    set Ψ := (λ fv : FValue, ⌜∃ v, fv = fv_lift v⌝ ∗ ghost_var γv (1/2) fv)%I.
    iMod (llftl_borrow _ κ (∃ fv, gmb_b γ fv ∗ Ψ fv) with "LFT [B V1]") as "[Bor InhB]"; [done| |].
    { iNext. iExists (FVInt 5). iFrame "B V1". iPureIntro. by exists (VInt 5). }
    iMod (gcell_lend_pred _ γ κ l (MInt i32) Ψ with "LFT GI Ga' Lc1 Bor Alive") as "[Bor Alive]";
      [done|].
    (* write through the borrow *)
    iMod (llftl_bor_acc with "LFT Bor Alive") as "[Cb Close]"; [done|].
    iMod (bi.later_exist_except_0 with "Cb") as (fv) "[>C [>%Hfv >V1]]".
    iDestruct (ghost_var_agree with "V1 V2") as %->.
    wp_bind (Store _ _ _ _). rewrite {1}loc_0.
    iApply (wp_gcont_store_na_sub _ _ _ _ _ _ (VInt 5) (VInt 7) (FVInt 7) with "C");
      [set_solver|apply MInt_wf|apply int7_wf|constructor|].
    iIntros "!> C".
    iMod (ghost_var_update_halves (FVInt 7) with "V1 V2") as "[V1 V2]".
    iDestruct ("Close" $! (∃ fv, gcont l (MInt i32) fv ∗ Ψ fv)%I with "[C V1]") as "X".
    { iSplitR. { iIntros "!> [$ _]". done. } iNext. iExists (FVInt 7). iFrame. iPureIntro. by exists (VInt 7). }
    iMod (fupd_mask_mono with "X") as "[_ Alive]"; [done|].
    wp_seq.
    (* the end of [κ] *)
    wp_bind Skip.
    iApply (wp_step_fupd _ E (E∖↑Nllft) _ [†κ] with "[Alive]"); [set_solver| |].
    { iApply step_fupd_frame_Nllft; [done|]. by iApply "End". }
    wp_seq. iIntros "#Dead". iModIntro. wp_seq.
    iMod ("InhA" with "Dead") as ">A".
    iMod (fupd_mask_mono with "(InhB Dead)") as (fv') "(>B & >%Hfv' & >V1)"; [done|].
    iDestruct (ghost_var_agree with "V1 V2") as %->.
    (* the owner moves the cell, and destroys it *)
    iDestruct (gcont_cell with "Hreg A") as "C".
    wp_bind (MemCopy _ _ _ _).
    iApply (wp_gcont_memcopy _ _ _ (MInt i32) with "[$GC $Lc2 $C $Hl']"); [set_solver|apply MInt_wf|done|].
    iIntros "!>" (bs1) "[Hl C]". wp_seq.
    iMod (gcell_destroy with "Hreg GI C B") as "C"; [done|].
    iDestruct (gcont_lift_bytes _ _ (VInt 7) with "C") as (bs2) "[Hl' %Hd2]".
    iApply (wp_load_na with "Hl'"); [done|]. iIntros "!> _". iApply "HΦ". by iExists _.
  Qed.
End gmb_cells_tests.

Print Assumptions test_gcell_create_read_destroy.
Print Assumptions test_gcell_nested_move.
Print Assumptions test_gcell_siblings_memcopy.
Print Assumptions test_gcell_shared_read.
Print Assumptions test_gcell_mcas.
Print Assumptions test_gcell_lend_write_end_move.
