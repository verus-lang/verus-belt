(** WP-level tests of the cells of the byte region ([PCell] on bytes): creating a cell,
    reading and writing through it (non-atomically and atomically), moving it (by a
    verbatim copy and by a typed [Load]/[Store]), destroying it, and moving a cell that
    contains a cell. *)
From lrust.lang Require Import proofmode notation.
From lrust.util Require Import non_atomic_cell_map.
From guarding Require Import guard.
Set Default Proof Using "Type".

Section pcell_tests.
  Context `{!lrustGS Σ}.

  (** Moving a [PCell] by a typed copy: [Load m] then [Store m]. The bytes at the new
      location are [encode_value m v], which may differ from the old bytes; the group may
      embed cells, whose bytes are rewritten too. *)
  Lemma wp_pcell_move E l l' g m cs bs0 :
    ↑naN ⊆ E → mty_wf m → length bs0 = mty_size m →
    {{{ loc_side l g m cs ∗ ▷ l' ↦b bs0 }}}
      Store Na1Ord m (Lit $ LitLoc l') (Load Na1Ord m (Lit $ LitLoc l)) @ E
    {{{ bs, RET LitV LitPoison; l ↦b bs ∗ loc_side l' g m cs }}}.
  Proof.
    iIntros (? Hm Hlen Φ) "(Hls & Hl') HΦ". iApply wp_bytes_ctx_pre. iIntros (σB) "HB".
    iMod (bytes_ctx_pcell_untether with "HB Hls") as (bs v) "(HB & Hl & %Hd & Hu)"; [done|].
    iModIntro. iFrame "HB".
    wp_bind (Load _ _ _). iApply (wp_load_na with "Hl"); [done|]. iIntros "!> Hl".
    iApply (wp_store_na_post with "Hl'"); [done|by eapply decode_value_wf|done|].
    iIntros "!> Hl'" (σB') "HB".
    iMod (bytes_ctx_pcell_retether_gen with "HB Hu Hl'") as "[HB Hls]"; [done| |].
    { rewrite decode_encode_value; [by rewrite Hd|done|by eapply decode_value_wf]. }
    iModIntro. iFrame "HB". iApply "HΦ". by iFrame.
  Qed.

  Lemma int5_wf : val_wf (MInt i32) (VInt 5).
  Proof. constructor. apply (bool_decide_unpack _); by vm_compute. Qed.
  Lemma int7_wf : val_wf (MInt i32) (VInt 7).
  Proof. constructor. apply (bool_decide_unpack _); by vm_compute. Qed.

  Lemma fv_lift_int v z : FVInt z = fv_lift v → v = VInt z.
  Proof. destruct v; simpl; congruence. Qed.

  (** Create a cell, then read through it. *)
  Lemma test_pcell_read E l bs :
    ↑naN ⊆ E → length bs = 4%nat →
    {{{ ▷ l ↦b bs }}}
      Store Na1Ord (MInt i32) (#l) (MLit (VInt 5)) ;; Load Na1Ord (MInt i32) (#l) @ E
    {{{ RET MLitV (VInt 5); ∃ g cs, loc_side l g (MInt i32) cs ∗ gdyn g (FVInt 5) }}}.
  Proof.
    iIntros (? Hlen Φ) "Hl HΦ".
    wp_bind (Store _ _ _ _). iApply (wp_store_na with "Hl"); [done|apply int5_wf|done|].
    iIntros "!> Hl". wp_seq.
    iApply (wp_pcell_create_plain _ _ _ (MInt i32) _ (VInt 5) with "Hl"); [done|apply Nat.ltb_lt; reflexivity|constructor|by apply (decode_encode_value (MInt i32) (VInt 5)); [constructor|apply int5_wf]|].
    iIntros (g cs) "Hls Hgd _".
    iApply (wp_pcell_load_na with "[$Hls $Hgd]"); [done|].
    iIntros "!>" (v) "(Hls & Hgd & %Hv)". have -> : v = VInt 5 by apply fv_lift_int, Hv.
    iApply "HΦ". iExists g, cs. iFrame.
  Qed.

  (** Create a cell, write through it, move it to [l'] by a verbatim copy, destroy it, and
      read the plain bytes. *)
  Lemma test_pcell_lifecycle E l l' bs bs' :
    ↑naN ⊆ E → length bs = 4%nat → length bs' = 4%nat →
    {{{ ▷ l ↦b bs ∗ ▷ l' ↦b bs' }}}
      Store Na1Ord (MInt i32) (#l) (MLit (VInt 5)) ;;
      Store Na1Ord (MInt i32) (#l) (MLit (VInt 7)) ;;
      MemCopy Na1Ord 4 (#l') (#l) ;;
      Load Na1Ord (MInt i32) (#l') @ E
    {{{ RET MLitV (VInt 7); ∃ bs1 bs2, l ↦b bs1 ∗ l' ↦b bs2 }}}.
  Proof.
    iIntros (? Hlen Hlen' Φ) "[Hl Hl'] HΦ".
    wp_bind (Store _ _ _ _). iApply (wp_store_na with "Hl"); [done|apply int5_wf|done|].
    iIntros "!> Hl". wp_seq.
    iApply (wp_pcell_create_plain _ _ _ (MInt i32) _ (VInt 5) with "Hl"); [done|apply Nat.ltb_lt; reflexivity|constructor|by apply (decode_encode_value (MInt i32) (VInt 5)); [constructor|apply int5_wf]|].
    iIntros (g cs) "Hls Hgd #Hnc".
    wp_bind (Store _ _ _ _).
    iApply (wp_pcell_store_na with "[$Hls $Hgd $Hnc]"); [done|constructor|apply int7_wf|].
    iIntros "!> [Hls Hgd]". wp_seq.
    wp_bind (MemCopy _ _ _ _). iApply (wp_pcell_memcopy _ l l' with "[$Hls $Hl']"); [done..|].
    iIntros "!>" (bs1) "[Hl Hls]". wp_seq.
    iApply (wp_pcell_destroy_plain _ _ _ _ _ _ (VInt 7) with "Hls Hgd"). iIntros (bs2) "Hl' %Hd".
    iApply (wp_load_na with "Hl'"); [done|]. iIntros "!> Hl'". iApply "HΦ". iFrame.
  Qed.

  (** Atomic accesses through a cell. *)
  Lemma test_pcell_atomic E l bs :
    ↑naN ⊆ E → length bs = 4%nat →
    {{{ ▷ l ↦b bs }}}
      Store Na1Ord (MInt i32) (#l) (MLit (VInt 5)) ;;
      Store ScOrd (MInt i32) (#l) (MLit (VInt 7)) ;;
      Load ScOrd (MInt i32) (#l) @ E
    {{{ RET MLitV (VInt 7); ∃ g cs, loc_side l g (MInt i32) cs ∗ gdyn g (FVInt 7) }}}.
  Proof.
    iIntros (? Hlen Φ) "Hl HΦ".
    wp_bind (Store _ _ _ _). iApply (wp_store_na with "Hl"); [done|apply int5_wf|done|].
    iIntros "!> Hl". wp_seq.
    iApply (wp_pcell_create_plain _ _ _ (MInt i32) _ (VInt 5) with "Hl"); [done|apply Nat.ltb_lt; reflexivity|constructor|by apply (decode_encode_value (MInt i32) (VInt 5)); [constructor|apply int5_wf]|].
    iIntros (g cs) "Hls Hgd #Hnc".
    wp_bind (Store _ _ _ _).
    iApply (wp_pcell_store_sc with "[$Hls $Hgd $Hnc]"); [done|constructor|apply int7_wf|].
    iIntros "!> [Hls Hgd]". wp_seq.
    iApply (wp_pcell_load_sc with "[$Hls $Hgd]"); [done|].
    iIntros "!>" (v) "(Hls & Hgd & %Hv)". have -> : v = VInt 7 by apply fv_lift_int, Hv.
    iApply "HΦ". iExists g, cs. iFrame.
  Qed.

  (** Reads through a cell whose location side and permission are only guarded. *)
  Lemma test_pcell_read_guarded E l bs :
    ↑naN ⊆ E → length bs = 4%nat →
    {{{ ▷ l ↦b bs }}}
      Store Na1Ord (MInt i32) (#l) (MLit (VInt 5)) ;;
      Load Na1Ord (MInt i32) (#l) ;; Load ScOrd (MInt i32) (#l) @ E
    {{{ RET MLitV (VInt 5); ∃ g cs, loc_side l g (MInt i32) cs ∗ gdyn g (FVInt 5) }}}.
  Proof.
    iIntros (? Hlen Φ) "Hl HΦ".
    wp_bind (Store _ _ _ _). iApply (wp_store_na with "Hl"); [done|apply int5_wf|done|].
    iIntros "!> Hl". wp_seq.
    iApply (wp_pcell_create_plain _ _ _ (MInt i32) _ (VInt 5) with "Hl");
      [done|apply Nat.ltb_lt; reflexivity|constructor|by apply (decode_encode_value (MInt i32) (VInt 5)); [constructor|apply int5_wf]|].
    iIntros (g cs) "Hls Hgd _". iDestruct "Hls" as "[#Hg Hedges]".
    iAssert (loc_side l g (MInt i32) cs) with "[Hedges]" as "Hls"; [by iFrame "Hg"|].
    set P := (loc_side l g (MInt i32) cs ∗ gdyn g (FVInt 5))%I.
    iAssert (P &&{↑naN; 0}&&> P)%I as "#Guard"; [iApply guards_refl|].
    iAssert (□ (P -∗ (loc_side l g (MInt i32) cs ∗ gdyn g (FVInt 5)) ∗
      (loc_side l g (MInt i32) cs -∗ gdyn g (FVInt 5) -∗ P)))%I as "#HP".
    { iIntros "!> [Hls Hgd]". iFrame. iIntros "Hls Hgd". iFrame. }
    iMod lc_zero as "£".
    wp_bind (Load _ _ _).
    iApply (wp_pcell_load_na_guarded with "[$Guard $HP $Hls $Hgd $Hg $£]"); [done|done|].
    iIntros "!>" (v) "[[Hls Hgd] _]". wp_seq. iMod lc_zero as "£".
    iApply (wp_pcell_load_sc_guarded with "[$Guard $HP $Hls $Hgd $Hg $£]"); [done|done|].
    iIntros "!>" (v') "[[Hls Hgd] %Hv]". have -> : v' = VInt 5 by apply fv_lift_int, Hv.
    iApply "HΦ". iExists g, cs. iFrame.
  Qed.

  (** A non-atomic write through a cell whose location side is only guarded, then a
      guarded read. *)
  Lemma test_pcell_write_guarded E l bs :
    ↑naN ⊆ E → length bs = 4%nat →
    {{{ ▷ l ↦b bs }}}
      Store Na1Ord (MInt i32) (#l) (MLit (VInt 5)) ;;
      Store Na1Ord (MInt i32) (#l) (MLit (VInt 7)) ;; Load Na1Ord (MInt i32) (#l) @ E
    {{{ RET MLitV (VInt 7); ∃ g cs, loc_side l g (MInt i32) cs ∗ gdyn g (FVInt 7) }}}.
  Proof.
    iIntros (? Hlen Φ) "Hl HΦ".
    wp_bind (Store _ _ _ _). iApply (wp_store_na with "Hl"); [done|apply int5_wf|done|].
    iIntros "!> Hl". wp_seq.
    iApply (wp_pcell_create_plain _ _ _ (MInt i32) _ (VInt 5) with "Hl");
      [done|apply Nat.ltb_lt; reflexivity|constructor|by apply (decode_encode_value (MInt i32) (VInt 5)); [constructor|apply int5_wf]|].
    iIntros (g cs) "Hls Hgd #Hnc".
    iDestruct "Hls" as "[#Hg Hedges]".
    iAssert (loc_side l g (MInt i32) cs) with "[Hedges]" as "Hls"; [by iFrame "Hg"|].
    iAssert (loc_side l g (MInt i32) cs &&{↑naN; 0}&&> loc_side l g (MInt i32) cs)%I
      as "#Guard"; [iApply guards_refl|].
    iAssert (□ (loc_side l g (MInt i32) cs -∗ loc_side l g (MInt i32) cs ∗
      (loc_side l g (MInt i32) cs -∗ loc_side l g (MInt i32) cs)))%I as "#HP".
    { iIntros "!> Hls". iFrame. by iIntros "Hls". }
    iMod lc_zero as "£".
    wp_bind (Store _ _ _ _).
    iApply (wp_pcell_store_na_guarded _ l g (MInt i32) cs (FVInt 5) _ (VInt 7)
      (loc_side l g (MInt i32) cs) (loc_side l g (MInt i32) cs) 0 with "[$Guard $HP $Hls $Hg $Hgd $£]");
      [done|done|constructor|apply int7_wf|].
    iIntros "!> [Hls Hgd]". wp_seq.
    set P2 := (loc_side l g (MInt i32) cs ∗ gdyn g (FVInt 7))%I.
    iAssert (P2 &&{↑naN; 0}&&> P2)%I as "#Guard2"; [iApply guards_refl|].
    iAssert (□ (P2 -∗ (loc_side l g (MInt i32) cs ∗ gdyn g (FVInt 7)) ∗
      (loc_side l g (MInt i32) cs -∗ gdyn g (FVInt 7) -∗ P2)))%I as "#HP2".
    { iIntros "!> [Hls Hgd]". iFrame. iIntros "Hls Hgd". iFrame. }
    iMod lc_zero as "£".
    iApply (wp_pcell_load_na_guarded with "[$Guard2 $HP2 $Hls $Hgd $Hg $£]"); [done|done|].
    iIntros "!>" (v) "[[Hls Hgd] %Hv]". have -> : v = VInt 7 by apply fv_lift_int, Hv.
    iApply "HΦ". iExists g, cs. iFrame.
  Qed.

  (** Atomic accesses through a cell whose location side is only guarded. *)
  Lemma test_pcell_atomic_guarded E l bs :
    ↑naN ⊆ E → length bs = 4%nat →
    {{{ ▷ l ↦b bs }}}
      Store Na1Ord (MInt i32) (#l) (MLit (VInt 5)) ;;
      Store ScOrd (MInt i32) (#l) (MLit (VInt 7)) ;; Load ScOrd (MInt i32) (#l) @ E
    {{{ RET MLitV (VInt 7); ∃ g cs, loc_side l g (MInt i32) cs ∗ gdyn g (FVInt 7) }}}.
  Proof.
    iIntros (? Hlen Φ) "Hl HΦ".
    wp_bind (Store _ _ _ _). iApply (wp_store_na with "Hl"); [done|apply int5_wf|done|].
    iIntros "!> Hl". wp_seq.
    iApply (wp_pcell_create_plain _ _ _ (MInt i32) _ (VInt 5) with "Hl");
      [done|apply Nat.ltb_lt; reflexivity|constructor|by apply (decode_encode_value (MInt i32) (VInt 5)); [constructor|apply int5_wf]|].
    iIntros (g cs) "Hls Hgd #Hnc".
    iDestruct "Hls" as "[#Hg Hedges]".
    iAssert (loc_side l g (MInt i32) cs) with "[Hedges]" as "Hls"; [by iFrame "Hg"|].
    iAssert (loc_side l g (MInt i32) cs &&{↑naN; 0}&&> loc_side l g (MInt i32) cs)%I
      as "#Guard"; [iApply guards_refl|].
    iAssert (□ (loc_side l g (MInt i32) cs -∗ loc_side l g (MInt i32) cs ∗
      (loc_side l g (MInt i32) cs -∗ loc_side l g (MInt i32) cs)))%I as "#HP".
    { iIntros "!> Hls". iFrame. by iIntros "Hls". }
    iMod lc_zero as "£".
    wp_bind (Store _ _ _ _).
    iApply (wp_pcell_store_sc_guarded _ l g (MInt i32) cs (FVInt 5) _ (VInt 7)
      (loc_side l g (MInt i32) cs) (loc_side l g (MInt i32) cs) 0 with "[$Guard $HP $Hls $Hg $Hgd $£]");
      [done|done|constructor|apply int7_wf|].
    iIntros "!> [Hls Hgd]". wp_seq.
    set P2 := (loc_side l g (MInt i32) cs ∗ gdyn g (FVInt 7))%I.
    iAssert (P2 &&{↑naN; 0}&&> P2)%I as "#Guard2"; [iApply guards_refl|].
    iAssert (□ (P2 -∗ (loc_side l g (MInt i32) cs ∗ gdyn g (FVInt 7)) ∗
      (loc_side l g (MInt i32) cs -∗ gdyn g (FVInt 7) -∗ P2)))%I as "#HP2".
    { iIntros "!> [Hls Hgd]". iFrame. iIntros "Hls Hgd". iFrame. }
    iMod lc_zero as "£".
    iApply (wp_pcell_load_sc_guarded with "[$Guard2 $HP2 $Hls $Hgd $Hg $£]"); [done|done|].
    iIntros "!>" (v) "[[Hls Hgd] %Hv]". have -> : v = VInt 7 by apply fv_lift_int, Hv.
    iApply "HΦ". iExists g, cs. iFrame.
  Qed.

  (** Move a cell by a typed copy. *)
  Lemma test_pcell_typed_move E l l' lp bs bs' :
    ↑naN ⊆ E → length bs = PTR_SIZE → length bs' = PTR_SIZE →
    {{{ ▷ l ↦b bs ∗ ▷ l' ↦b bs' }}}
      Store Na1Ord MPtr (#l) (MLit (VPtr lp)) ;;
      Store Na1Ord MPtr (#l') (Load Na1Ord MPtr (#l)) ;;
      Load Na1Ord MPtr (#l') @ E
    {{{ RET MLitV (VPtr lp); ∃ bs1 bs2, l ↦b bs1 ∗ l' ↦b bs2 }}}.
  Proof.
    iIntros (? Hlen Hlen' Φ) "[Hl Hl'] HΦ".
    wp_bind (Store _ _ _ _). iApply (wp_store_na with "Hl"); [done|constructor|done|].
    iIntros "!> Hl". wp_seq.
    iApply (wp_pcell_create_plain _ _ _ MPtr _ (VPtr lp) with "Hl");
      [done|apply PTR_SIZE_pos|constructor|by apply (decode_encode_value MPtr (VPtr lp)); constructor|].
    iIntros (g cs) "Hls Hgd #Hnc".
    wp_bind (Store _ _ _ _).
    iApply (wp_pcell_move _ l l' with "[$Hls $Hl']");
      [done|constructor|done|].
    iIntros "!>" (bs1) "[Hl Hls]". wp_seq.
    iApply (wp_pcell_destroy_plain _ _ _ _ _ _ (VPtr lp) with "Hls Hgd"). iIntros (bs2) "Hl' %Hd".
    iApply (wp_load_na with "Hl'"); [done|]. iIntros "!> Hl'". iApply "HΦ". iFrame.
  Qed.

  (** A cell inside a cell ([PCell<PCell<i32>>]): create the outer cell over the inner one,
      move the outer cell to [l'] (which moves the inner one along), destroy the outer cell,
      and read through the inner cell at its new location. *)
  Lemma test_pcell_nested E l l' g1 cs1 bs' :
    ↑naN ⊆ E → length bs' = 4%nat →
    {{{ loc_side l g1 (MInt i32) cs1 ∗ gdyn g1 (FVInt 5) ∗ ▷ l' ↦b bs' }}}
      MemCopy Na1Ord 4 (#l') (#l) ;; Load Na1Ord (MInt i32) (#l') @ E
    {{{ RET MLitV (VInt 5); ∃ bs1, l ↦b bs1 ∗ loc_side l' g1 (MInt i32) cs1 ∗ gdyn g1 (FVInt 5) }}}.
  Proof.
    iIntros (? Hlen' Φ) "(Hls1 & Hgd1 & Hl') HΦ".
    iDestruct "Hls1" as "[#Hg1 Hedges]".
    (* The outer cell, whose content is the inner cell. *)
    iApply (wp_pcell_create _ _ l (MInt i32) (inl <$> cs1 : list (positive + abyte)) (FVCell g1)
      with "[Hedges] [] [-]"); [done|apply Nat.ltb_lt; reflexivity|constructor|..].
    { rewrite /heap_mapsto_fbytes big_sepL_fmap. done. }
    { by iApply brepr_cell. }
    iIntros (g0 cs0) "Hls0 Hgd0 _".
    (* Moving the outer cell moves the inner one. *)
    wp_bind (MemCopy _ _ _ _).
    iApply (wp_pcell_memcopy _ l l' with "[$Hls0 $Hl']"); [done|exact Hlen'|].
    iIntros "!>" (bs1) "[Hl Hls0]". wp_seq.
    (* Destroying the outer cell gives back the location side of the inner one. *)
    iApply (wp_pcell_destroy with "Hls0 Hgd0"). iIntros (fbs) "Hl' Hrep".
    iDestruct (brepr_cell_inv with "Hrep Hg1") as %[_ ->].
    iAssert (loc_side l' g1 (MInt i32) cs1) with "[Hl']" as "Hls1".
    { iFrame "Hg1". rewrite /heap_mapsto_fbytes big_sepL_fmap. done. }
    iApply (wp_pcell_load_na with "[$Hls1 $Hgd1]"); [done|].
    iIntros "!>" (v) "(Hls1 & Hgd1 & %Hv)". have -> : v = VInt 5 by apply fv_lift_int, Hv.
    iApply "HΦ". iExists bs1. iFrame.
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

  Lemma frepr_pair R g1 cs1 (bs : list abyte) z :
    R !! g1 = Some (MInt i32, cs1) → length cs1 = 4%nat → decode_value (MInt i32) bs = Some (VInt z) →
    frepr R pair_mty ((inr <$> bs) ++ (inl <$> cs1)) (FVTuple [FVInt z; FVCell g1]).
  Proof.
    intros HR Hlen Hd. have Hlb : length bs = 4%nat by apply (decode_value_length _ _ _ Hd).
    apply frepr_tuple.
    - rewrite length_app !length_fmap. lia.
    - done.
    - intros [|[|k]] f fv; simpl; try done; intros [= <-] [= <-]; simpl.
      + rewrite /list_slice drop_0 take_app_length'; [|by rewrite length_fmap].
        exact (frepr_plain R (MInt i32) bs (VInt z) Hd).
      + rewrite /list_slice drop_app_length'; [|by rewrite length_fmap].
        rewrite take_ge; [|rewrite length_fmap; simpl; lia]. by constructor.
    - intros i fb Hi Hnf. exfalso. apply Hnf. apply lookup_lt_Some in Hi.
      rewrite length_app !length_fmap in Hi. destruct (decide (i < 4)%nat).
      + exists (0%nat, MInt i32). split; [set_solver|simpl; lia].
      + exists (4%nat, MInt i32). split; [set_solver|simpl; lia].
  Qed.

  (** Create the inner cell [g1] (holding [9]) at [l +ₗ 4], then the outer cell [g0] over
      [l] (holding [(5, g1)]), and record the nesting. *)
  Lemma wp_pair_setup E e l bs1 bs2 Φ :
    TCEq (to_val e) None → ↑naN ⊆ E →
    decode_value (MInt i32) bs1 = Some (VInt 5) → decode_value (MInt i32) bs2 = Some (VInt 9) →
    l ↦b bs1 -∗ (l +ₗ 4) ↦b bs2 -∗
    (∀ g0 cs0 g1 cs1, greg g0 pair_mty cs0 -∗ loc_side l g0 pair_mty cs0 -∗
       gdyn g0 (FVTuple [FVInt 5; FVCell g1]) -∗ greg g1 (MInt i32) cs1 -∗ gdyn g1 (FVInt 9) -∗
       gpath g0 g1 4 -∗ WP e @ E {{ Φ }}) -∗
    WP e @ E {{ Φ }}.
  Proof.
    iIntros (Hv ? Hd1 Hd2) "Hl1 Hl2 Hwp".
    have Hlb : length bs1 = 4%nat by apply (decode_value_length _ _ _ Hd1).
    iApply (wp_pcell_create_plain _ _ (l +ₗ 4) (MInt i32) _ (VInt 9) with "Hl2");
      [done|apply Nat.ltb_lt; reflexivity|constructor|done|].
    iIntros (g1 cs1) "[#Hg1 Hls1] Hgd1 _".
    iApply (wp_greg_length with "Hg1"). iIntros (Hlen1).
    iApply (wp_pcell_create _ _ l pair_mty ((inr <$> bs1) ++ (inl <$> cs1))
      (FVTuple [FVInt 5; FVCell g1]) with "[Hl1 Hls1] [] [-]");
      [done|apply Nat.ltb_lt; reflexivity|apply pair_mty_wf|..].
    { rewrite heap_mapsto_fbytes_app -heap_mapsto_fbytes_bytes length_fmap Hlb. iFrame "Hl1".
      rewrite /heap_mapsto_fbytes big_sepL_fmap. done. }
    { iExists {[g1 := (MInt i32, cs1)]}. rewrite big_sepM_singleton. iFrame "Hg1".
      iPureIntro. apply frepr_pair; [by rewrite lookup_singleton|done|done]. }
    iIntros (g0 cs0) "Hls0 Hgd0 _". iDestruct "Hls0" as "[#Hg0 Hedges0]".
    iApply (wp_pcell_gnest _ _ g0 pair_mty cs0 _ 4 (MInt i32) g1 with "Hg0 Hgd0").
    { by apply (fv_sub_field _ _ _ 1 4 (MInt i32) (FVCell g1) 0 (MInt i32) (FVCell g1));
        [|done|constructor]. }
    iIntros "Hgd0 #Hn". iApply ("Hwp" with "Hg0 [$Hg0 $Hedges0] Hgd0 Hg1 Hgd1").
    iApply (gpath_nest with "Hn"). iApply gpath_refl.
  Qed.

  (** Sub-position writes: write the first field of the outer cell (the second one is the
      inner cell), then read it. *)
  Lemma test_pcell_sub_write E l bs1 bs2 :
    ↑naN ⊆ E →
    decode_value (MInt i32) bs1 = Some (VInt 5) → decode_value (MInt i32) bs2 = Some (VInt 9) →
    {{{ l ↦b bs1 ∗ (l +ₗ 4) ↦b bs2 }}}
      Store Na1Ord (MInt i32) (#l) (MLit (VInt 7)) ;; Load Na1Ord (MInt i32) (#l) @ E
    {{{ RET MLitV (VInt 7); ∃ g0 cs0 g1, loc_side l g0 pair_mty cs0 ∗
          gdyn g0 (FVTuple [FVInt 7; FVCell g1]) ∗ gdyn g1 (FVInt 9) }}}.
  Proof.
    iIntros (? Hd1 Hd2 Φ) "[Hl1 Hl2] HΦ".
    iApply (wp_pair_setup with "Hl1 Hl2"); [done..|].
    iIntros (g0 cs0 g1 cs1) "#Hg0 Hls0 Hgd0 #Hg1 Hgd1 #Hp".
    iAssert (loc_side l g0 pair_mty cs0 &&{↑naN; 0}&&> loc_side l g0 pair_mty cs0)%I
      as "#Guard"; [iApply guards_refl|].
    iAssert (□ (loc_side l g0 pair_mty cs0 -∗ loc_side l g0 pair_mty cs0 ∗
      (loc_side l g0 pair_mty cs0 -∗ loc_side l g0 pair_mty cs0)))%I as "#HP".
    { iIntros "!> Hls". iFrame. by iIntros "Hls". }
    iMod lc_zero as "£".
    have -> : (Lit (LitLoc l)) = (Lit (LitLoc (l +ₗ (0 + 0)%nat))) by rewrite /= shift_loc_0_nat.
    wp_bind (Store _ _ _ _).
    iApply (wp_pcell_store_na_sub _ l g0 pair_mty cs0 g0 0 pair_mty cs0
      (FVTuple [FVInt 5; FVCell g1]) 0 (MInt i32) (FVInt 5) (FVTuple [FVInt 7; FVCell g1]) _
      (VInt 7) _ _ 0 with "[$Guard $HP $Hls0 $Hgd0 $£]").
    { done. }
    { by apply (fv_sub_field _ _ _ 0 0 (MInt i32) (FVInt 5) 0 (MInt i32) (FVInt 5));
        [|done|constructor]. }
    { done. }
    { by apply (fv_upd_field [(0%nat, MInt i32); (4%nat, MInt i32)] 8 [FVInt 5; FVCell g1] 0 0
        (MInt i32) (FVInt 5) 0 (MInt i32) (FVInt 7) (FVInt 7));
        [|done|constructor]. }
    { constructor. }
    { apply int7_wf. }
    { iSplitR; [iApply gpath_refl|iExact "Hg0"]. }
    iIntros "!> [Hls0 Hgd0]". wp_seq. iMod lc_zero as "£".
    iAssert ((loc_side l g0 pair_mty cs0 ∗ gdyn g0 (FVTuple [FVInt 7; FVCell g1])) &&{↑naN; 0}&&>
      (loc_side l g0 pair_mty cs0 ∗ gdyn g0 (FVTuple [FVInt 7; FVCell g1])))%I
      as "#Guard2"; [iApply guards_refl|].
    iApply (wp_pcell_load_na_sub _ l g0 pair_mty cs0 g0 0 pair_mty cs0
      (FVTuple [FVInt 7; FVCell g1]) 0 (MInt i32) (FVInt 7) with "[$Guard2 $Hls0 $Hgd0 $£]").
    { done. }
    { by apply (fv_sub_field _ _ _ 0 0 (MInt i32) (FVInt 7) 0 (MInt i32) (FVInt 7));
        [|done|constructor]. }
    { done. }
    { iSplitR; [|iSplitR; [iApply gpath_refl|iExact "Hg0"]]. iIntros "!> [Hls Hgd]".
      iSplitL "Hls Hgd"; [iFrame|]. iIntros "Hls Hgd". iFrame. }
    iIntros "!>" (v) "[[Hls0 Hgd0] %Hv]". have -> : v = VInt 7 by apply fv_lift_int, Hv.
    iApply "HΦ". iExists g0, cs0, g1. iFrame.
  Qed.

  (** Accesses through the inner cell while the outer one is live: write and read the inner
      cell, and read the first field of the outer one. *)
  Lemma test_pcell_inner_access E l bs1 bs2 :
    ↑naN ⊆ E →
    decode_value (MInt i32) bs1 = Some (VInt 5) → decode_value (MInt i32) bs2 = Some (VInt 9) →
    {{{ l ↦b bs1 ∗ (l +ₗ 4) ↦b bs2 }}}
      Store Na1Ord (MInt i32) (#(l +ₗ 4)) (MLit (VInt 11)) ;;
      Load ScOrd (MInt i32) (#l) ;; Load Na1Ord (MInt i32) (#(l +ₗ 4)) @ E
    {{{ RET MLitV (VInt 11); ∃ g0 cs0 g1, loc_side l g0 pair_mty cs0 ∗
          gdyn g0 (FVTuple [FVInt 5; FVCell g1]) ∗ gdyn g1 (FVInt 11) }}}.
  Proof.
    iIntros (? Hd1 Hd2 Φ) "[Hl1 Hl2] HΦ".
    iApply (wp_pair_setup with "Hl1 Hl2"); [done..|].
    iIntros (g0 cs0 g1 cs1) "#Hg0 Hls0 Hgd0 #Hg1 Hgd1 #Hp".
    iAssert (loc_side l g0 pair_mty cs0 &&{↑naN; 0}&&> loc_side l g0 pair_mty cs0)%I
      as "#Guard"; [iApply guards_refl|].
    iAssert (□ (loc_side l g0 pair_mty cs0 -∗ loc_side l g0 pair_mty cs0 ∗
      (loc_side l g0 pair_mty cs0 -∗ loc_side l g0 pair_mty cs0)))%I as "#HP".
    { iIntros "!> Hls". iFrame. by iIntros "Hls". }
    iMod lc_zero as "£".
    have -> : (Lit (LitLoc (l +ₗ 4))) = (Lit (LitLoc (l +ₗ (4 + 0)%nat))) by done.
    have -> : (Lit (LitLoc l)) = (Lit (LitLoc (l +ₗ (0 + 0)%nat))) by rewrite /= shift_loc_0_nat.
    (* A write through the inner cell. *)
    wp_bind (Store _ _ _ _).
    iApply (wp_pcell_store_na_sub _ l g0 pair_mty cs0 g1 4 (MInt i32) cs1 (FVInt 9) 0 (MInt i32)
      (FVInt 9) (FVInt 11) _ (VInt 11) _ _ 0 with "[$Guard $HP $Hls0 $Hgd1 $£ $Hp $Hg1]").
    { done. } { apply fv_sub_here. } { done. } { apply fv_upd_here. } { constructor. }
    { constructor. apply (bool_decide_unpack _); by vm_compute. }
    iIntros "!> [Hls0 Hgd1]". wp_seq. iMod lc_zero as "£".
    (* A read of the first field of the outer cell. *)
    iAssert ((loc_side l g0 pair_mty cs0 ∗ gdyn g0 (FVTuple [FVInt 5; FVCell g1])) &&{↑naN; 0}&&>
      (loc_side l g0 pair_mty cs0 ∗ gdyn g0 (FVTuple [FVInt 5; FVCell g1])))%I
      as "#Guard2"; [iApply guards_refl|].
    wp_bind (Load _ _ _).
    iApply (wp_pcell_load_sc_sub _ l g0 pair_mty cs0 g0 0 pair_mty cs0
      (FVTuple [FVInt 5; FVCell g1]) 0 (MInt i32) (FVInt 5) with "[$Guard2 $Hls0 $Hgd0 $£]").
    { done. }
    { by apply (fv_sub_field _ _ _ 0 0 (MInt i32) (FVInt 5) 0 (MInt i32) (FVInt 5));
        [|done|constructor]. }
    { done. }
    { iSplitR; [|iSplitR; [iApply gpath_refl|iExact "Hg0"]]. iIntros "!> [Hls Hgd]".
      iSplitL "Hls Hgd"; [iFrame|]. iIntros "Hls Hgd". iFrame. }
    iIntros "!>" (v) "[[Hls0 Hgd0] %Hv]". have -> : v = VInt 5 by apply fv_lift_int, Hv.
    wp_seq. iMod lc_zero as "£".
    (* A read through the inner cell. *)
    iAssert ((loc_side l g0 pair_mty cs0 ∗ gdyn g1 (FVInt 11)) &&{↑naN; 0}&&>
      (loc_side l g0 pair_mty cs0 ∗ gdyn g1 (FVInt 11)))%I as "#Guard3"; [iApply guards_refl|].
    iApply (wp_pcell_load_na_sub _ l g0 pair_mty cs0 g1 4 (MInt i32) cs1 (FVInt 11) 0 (MInt i32)
      (FVInt 11) with "[$Guard3 $Hls0 $Hgd1 $£ $Hp $Hg1]").
    { done. } { apply fv_sub_here. } { done. }
    { iIntros "!> [Hls Hgd]". iSplitL "Hls Hgd"; [iFrame|]. iIntros "Hls Hgd". iFrame. }
    iIntros "!>" (v') "[[Hls0 Hgd1] %Hv']". have -> : v' = VInt 11 by apply fv_lift_int, Hv'.
    iApply "HΦ". iExists g0, cs0, g1. iFrame.
  Qed.

  (** ** Typed compare-and-exchange *)
  Lemma int9_wf : val_wf (MInt i32) (VInt 9).
  Proof. constructor. apply (bool_decide_unpack _); by vm_compute. Qed.

  (** On plain bytes: a successful and a failing compare-and-exchange of an [i32]. *)
  Lemma test_mcas_int E l bs :
    ↑naN ⊆ E → length bs = 4%nat →
    {{{ ▷ l ↦b bs }}}
      Store Na1Ord (MInt i32) (#l) (MLit (VInt 5)) ;;
      MCAS (MInt i32) (#l) (MLit (VInt 5)) (MLit (VInt 7)) ;;
      MCAS (MInt i32) (#l) (MLit (VInt 5)) (MLit (VInt 9)) ;;
      Load Na1Ord (MInt i32) (#l) @ E
    {{{ RET MLitV (VInt 7); ∃ bs', l ↦b bs' }}}.
  Proof.
    iIntros (? Hlen Φ) "Hl HΦ".
    wp_bind (Store _ _ _ _). iApply (wp_store_na with "Hl"); [done|apply int5_wf|done|].
    iIntros "!> Hl". wp_seq.
    wp_bind (MCAS _ _ _ _). iApply (wp_mcas with "Hl"); [done|apply int7_wf|
      by apply (decode_encode_value (MInt i32) (VInt 5)); [constructor|apply int5_wf]|].
    iIntros "!>" (b) "[[[-> _] Hl]|[[_ %Hne] _]]"; [|done]. wp_seq.
    wp_bind (MCAS _ _ _ _). iApply (wp_mcas with "Hl"); [done|apply int9_wf|
      by apply (decode_encode_value (MInt i32) (VInt 7)); [constructor|apply int7_wf]|].
    iIntros "!>" (b) "[[[_ %Heq] _]|[[-> _] Hl]]"; [done|]. wp_seq.
    iApply (wp_load_na with "Hl");
      [by apply (decode_encode_value (MInt i32) (VInt 7)); [constructor|apply int7_wf]|].
    iIntros "!> Hl". iApply "HΦ". by iExists _.
  Qed.

  (** Through a cell: a successful compare-and-exchange of the value of the cell, then a
      read through the cell. *)
  Lemma test_pcell_mcas E l bs :
    ↑naN ⊆ E → length bs = 4%nat →
    {{{ ▷ l ↦b bs }}}
      Store Na1Ord (MInt i32) (#l) (MLit (VInt 5)) ;;
      MCAS (MInt i32) (#l) (MLit (VInt 5)) (MLit (VInt 7)) ;;
      Load ScOrd (MInt i32) (#l) @ E
    {{{ RET MLitV (VInt 7); ∃ g cs, loc_side l g (MInt i32) cs ∗ gdyn g (FVInt 7) }}}.
  Proof.
    iIntros (? Hlen Φ) "Hl HΦ".
    wp_bind (Store _ _ _ _). iApply (wp_store_na with "Hl"); [done|apply int5_wf|done|].
    iIntros "!> Hl". wp_seq.
    iApply (wp_pcell_create_plain _ _ _ (MInt i32) _ (VInt 5) with "Hl");
      [done|apply Nat.ltb_lt; reflexivity|constructor|by apply (decode_encode_value (MInt i32) (VInt 5)); [constructor|apply int5_wf]|].
    iIntros (g cs) "Hls Hgd _".
    iDestruct "Hls" as "[#Hg Hedges]".
    iAssert (loc_side l g (MInt i32) cs) with "[Hedges]" as "Hls"; [by iFrame "Hg"|].
    iAssert (loc_side l g (MInt i32) cs &&{↑naN; 0}&&> loc_side l g (MInt i32) cs)%I
      as "#Guard"; [iApply guards_refl|].
    iAssert (□ (loc_side l g (MInt i32) cs -∗ loc_side l g (MInt i32) cs ∗
      (loc_side l g (MInt i32) cs -∗ loc_side l g (MInt i32) cs)))%I as "#HP".
    { iIntros "!> Hls". iFrame. by iIntros "Hls". }
    iMod lc_zero as "£".
    have -> : (Lit (LitLoc l)) = (Lit (LitLoc (l +ₗ (0 + 0)%nat))) by rewrite /= shift_loc_0_nat.
    wp_bind (MCAS _ _ _ _).
    iApply (wp_pcell_mcas_sub _ l g (MInt i32) cs g 0 (MInt i32) cs (FVInt 5) 0 (MInt i32)
      (VInt 5) (FVInt 7) _ (VInt 5) _ (VInt 7) _ _ 0 with "[$Guard $HP $Hls $Hgd $£]").
    { done. } { apply fv_sub_here. } { apply fv_upd_here. } { constructor. } { apply int7_wf. }
    { iSplitR; [iApply gpath_refl|iExact "Hg"]. }
    iIntros "!>" (b) "[Hls [[[-> _] Hgd]|[[_ %Hne] _]]]"; [|done]. wp_seq.
    rewrite /= shift_loc_0_nat.
    iMod lc_zero as "£".
    iAssert ((loc_side l g (MInt i32) cs ∗ gdyn g (FVInt 7)) &&{↑naN; 0}&&>
      (loc_side l g (MInt i32) cs ∗ gdyn g (FVInt 7)))%I as "#Guard2"; [iApply guards_refl|].
    iApply (wp_pcell_load_sc_guarded _ l g (MInt i32) cs (FVInt 7) with "[$Guard2 $Hls $Hgd $£]"); [done|done| |].
    { iSplitR; [|iExact "Hg"]. iIntros "!> [Hls Hgd]". iSplitL "Hls Hgd"; [iFrame|]. iIntros "Hls Hgd". iFrame. }
    iIntros "!>" (v) "[[Hls Hgd] %Hv]". have -> : v = VInt 7 by apply fv_lift_int, Hv.
    iApply "HΦ". iExists g, cs. iFrame.
  Qed.

  (** ** A typed move of a [PCell<(i32, PCell<i32>)>] *)
  Lemma test_pcell_typed_move_nested E l l' bs1 bs2 bs' :
    ↑naN ⊆ E →
    decode_value (MInt i32) bs1 = Some (VInt 5) → decode_value (MInt i32) bs2 = Some (VInt 9) →
    length bs' = 8%nat →
    {{{ l ↦b bs1 ∗ (l +ₗ 4) ↦b bs2 ∗ ▷ l' ↦b bs' }}}
      Store Na1Ord pair_mty (#l') (Load Na1Ord pair_mty (#l)) ;;
      Load Na1Ord (MInt i32) (#(l' +ₗ 4)) @ E
    {{{ RET MLitV (VInt 9); ∃ bs g0 cs0 g1, l ↦b bs ∗ loc_side l' g0 pair_mty cs0 ∗
          gdyn g0 (FVTuple [FVInt 5; FVCell g1]) ∗ gdyn g1 (FVInt 9) }}}.
  Proof.
    iIntros (? Hd1 Hd2 Hlen Φ) "(Hl1 & Hl2 & Hl') HΦ".
    iApply (wp_pair_setup with "Hl1 Hl2"); [done..|].
    iIntros (g0 cs0 g1 cs1) "#Hg0 Hls0 Hgd0 #Hg1 Hgd1 #Hp".
    (* Move the outer cell (and the inner one along). *)
    wp_bind (Store _ _ _ _).
    iApply (wp_pcell_move _ l l' with "[$Hls0 $Hl']"); [done|apply pair_mty_wf|done|].
    iIntros "!>" (bs) "[Hl Hls0]". wp_seq.
    (* Read through the inner cell at its new location. *)
    iMod lc_zero as "£".
    have -> : (Lit (LitLoc (l' +ₗ 4))) = (Lit (LitLoc (l' +ₗ (4 + 0)%nat))) by done.
    iAssert ((loc_side l' g0 pair_mty cs0 ∗ gdyn g1 (FVInt 9)) &&{↑naN; 0}&&>
      (loc_side l' g0 pair_mty cs0 ∗ gdyn g1 (FVInt 9)))%I as "#Guard"; [iApply guards_refl|].
    iApply (wp_pcell_load_na_sub _ l' g0 pair_mty cs0 g1 4 (MInt i32) cs1 (FVInt 9) 0 (MInt i32)
      (FVInt 9) with "[$Guard $Hls0 $Hgd1 $£ $Hp $Hg1]").
    { done. } { apply fv_sub_here. } { done. }
    { iIntros "!> [Hls Hgd]". iSplitL "Hls Hgd"; [iFrame|]. iIntros "Hls Hgd". iFrame. }
    iIntros "!>" (v) "[[Hls0 Hgd1] %Hv]". have -> : v = VInt 9 by apply fv_lift_int, Hv.
    iApply "HΦ". iExists bs, g0, cs0, g1. iFrame.
  Qed.

  (** A verbatim copy of plain bytes into a cell, then a read through the cell. *)
  Lemma test_pcell_memcopy_into E l l2 bs bs2 :
    ↑naN ⊆ E → length bs = 4%nat → decode_value (MInt i32) bs2 = Some (VInt 7) →
    {{{ ▷ l ↦b bs ∗ ▷ l2 ↦b bs2 }}}
      Store Na1Ord (MInt i32) (#l) (MLit (VInt 5)) ;;
      MemCopy Na1Ord 4 (#l) (#l2) ;; Load ScOrd (MInt i32) (#l) @ E
    {{{ RET MLitV (VInt 7); ∃ g cs, loc_side l g (MInt i32) cs ∗ gdyn g (FVInt 7) ∗ l2 ↦b bs2 }}}.
  Proof.
    iIntros (? Hlen Hd2 Φ) "[Hl Hl2] HΦ".
    wp_bind (Store _ _ _ _). iApply (wp_store_na with "Hl"); [done|apply int5_wf|done|].
    iIntros "!> Hl". wp_seq.
    iApply (wp_pcell_create_plain _ _ _ (MInt i32) _ (VInt 5) with "Hl");
      [done|apply Nat.ltb_lt; reflexivity|constructor|by apply (decode_encode_value (MInt i32) (VInt 5)); [constructor|apply int5_wf]|].
    iIntros (g cs) "Hls Hgd _".
    iDestruct "Hls" as "[#Hg Hedges]".
    iAssert (loc_side l g (MInt i32) cs) with "[Hedges]" as "Hls"; [by iFrame "Hg"|].
    iAssert (loc_side l g (MInt i32) cs &&{↑naN; 0}&&> loc_side l g (MInt i32) cs)%I
      as "#Guard"; [iApply guards_refl|].
    iAssert (□ (loc_side l g (MInt i32) cs -∗ loc_side l g (MInt i32) cs ∗
      (loc_side l g (MInt i32) cs -∗ loc_side l g (MInt i32) cs)))%I as "#HP".
    { iIntros "!> Hls". iFrame. by iIntros "Hls". }
    iMod lc_zero as "£".
    have -> : (Lit (LitLoc l)) = (Lit (LitLoc (l +ₗ (0 + 0)%nat))) by rewrite /= shift_loc_0_nat.
    wp_bind (MemCopy _ _ _ _).
    iApply (wp_pcell_memcopy_into_sub _ l g (MInt i32) cs g 0 (MInt i32) cs (FVInt 5) 0 (MInt i32)
      (FVInt 5) (FVInt 7) l2 bs2 (VInt 7) _ _ 0 with "[$Guard $HP $Hls $Hgd $£ $Hl2]").
    { done. } { apply fv_sub_here. } { done. } { apply fv_upd_here. } { done. }
    { iSplitR; [iApply gpath_refl|iExact "Hg"]. }
    iIntros "!> (Hls & Hgd & Hl2)". wp_seq. rewrite /= shift_loc_0_nat.
    iMod lc_zero as "£".
    iAssert ((loc_side l g (MInt i32) cs ∗ gdyn g (FVInt 7)) &&{↑naN; 0}&&>
      (loc_side l g (MInt i32) cs ∗ gdyn g (FVInt 7)))%I as "#Guard2"; [iApply guards_refl|].
    iApply (wp_pcell_load_sc_guarded _ l g (MInt i32) cs (FVInt 7) with "[$Guard2 $Hls $Hgd $£]"); [done|done| |].
    { iSplitR; [|iExact "Hg"]. iIntros "!> [Hls Hgd]". iSplitL "Hls Hgd"; [iFrame|]. iIntros "Hls Hgd". iFrame. }
    iIntros "!>" (v) "[[Hls Hgd] %Hv]". have -> : v = VInt 7 by apply fv_lift_int, Hv.
    iApply "HΦ". iExists g, cs. iFrame.
  Qed.
End pcell_tests.

Print Assumptions test_pcell_read.
Print Assumptions test_pcell_lifecycle.
Print Assumptions test_pcell_atomic.
Print Assumptions test_pcell_read_guarded.
Print Assumptions test_pcell_write_guarded.
Print Assumptions test_pcell_atomic_guarded.
Print Assumptions test_pcell_typed_move.
Print Assumptions test_pcell_nested.
Print Assumptions test_pcell_sub_write.
Print Assumptions test_pcell_inner_access.
Print Assumptions test_mcas_int.
Print Assumptions test_pcell_mcas.
Print Assumptions test_pcell_typed_move_nested.
Print Assumptions test_pcell_memcopy_into.
