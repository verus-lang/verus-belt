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

  (** Moving a [PCell] without cells by a typed copy: [Load m] then [Store m]. The bytes at
      the new location are [encode_value m v], which may differ from the old bytes. *)
  Lemma wp_pcell_move E l l' g m cs bs0 :
    ↑naN ⊆ E → mty_wf m → (∀ (bs : list abyte) v, decode_value m bs = Some v → val_wf m v) →
    length bs0 = mty_size m →
    {{{ loc_side l g m cs ∗ gnocell g ∗ ▷ l' ↦b bs0 }}}
      Store Na1Ord m (Lit $ LitLoc l') (Load Na1Ord m (Lit $ LitLoc l)) @ E
    {{{ bs, RET LitV LitPoison; l ↦b bs ∗ loc_side l' g m cs }}}.
  Proof.
    iIntros (? Hm Hwf Hlen Φ) "(Hls & #Hnc & Hl') HΦ". iApply wp_bytes_ctx_pre. iIntros (σB) "HB".
    iMod (bytes_ctx_pcell_untether with "HB Hls") as (bs v) "(HB & Hl & %Hd & Hu)"; [done|].
    iModIntro. iFrame "HB".
    wp_bind (Load _ _ _). iApply (wp_load_na with "Hl"); [done|]. iIntros "!> Hl".
    iApply (wp_store_na_post with "Hl'"); [done|by eapply Hwf|done|].
    iIntros "!> Hl'" (σB') "HB".
    iMod (bytes_ctx_pcell_retether with "HB Hu Hl' [$Hnc]") as "[HB Hls]"; [done| |].
    { rewrite decode_encode_value; [by rewrite Hd|done|by eapply Hwf]. }
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
    iApply (wp_pcell_create_plain _ _ _ (MInt i32) _ (VInt 5) with "Hl"); [done|apply Nat.ltb_lt; reflexivity|by apply (decode_encode_value (MInt i32) (VInt 5)); [constructor|apply int5_wf]|].
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
    iApply (wp_pcell_create_plain _ _ _ (MInt i32) _ (VInt 5) with "Hl"); [done|apply Nat.ltb_lt; reflexivity|by apply (decode_encode_value (MInt i32) (VInt 5)); [constructor|apply int5_wf]|].
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
    iApply (wp_pcell_create_plain _ _ _ (MInt i32) _ (VInt 5) with "Hl"); [done|apply Nat.ltb_lt; reflexivity|by apply (decode_encode_value (MInt i32) (VInt 5)); [constructor|apply int5_wf]|].
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
      [done|apply Nat.ltb_lt; reflexivity|by apply (decode_encode_value (MInt i32) (VInt 5)); [constructor|apply int5_wf]|].
    iIntros (g cs) "Hls Hgd _".
    set P := (loc_side l g (MInt i32) cs ∗ gdyn g (FVInt 5))%I.
    iAssert (P &&{↑naN; 0}&&> P)%I as "#Guard"; [iApply guards_refl|].
    iAssert (□ (P -∗ (loc_side l g (MInt i32) cs ∗ gdyn g (FVInt 5)) ∗
      (loc_side l g (MInt i32) cs -∗ gdyn g (FVInt 5) -∗ P)))%I as "#HP".
    { iIntros "!> [Hls Hgd]". iFrame. iIntros "Hls Hgd". iFrame. }
    iMod lc_zero as "£".
    wp_bind (Load _ _ _).
    iApply (wp_pcell_load_na_guarded with "[$Guard $HP $Hls $Hgd $£]"); [done|].
    iIntros "!>" (v) "[[Hls Hgd] _]". wp_seq. iMod lc_zero as "£".
    iApply (wp_pcell_load_sc_guarded with "[$Guard $HP $Hls $Hgd $£]"); [done|].
    iIntros "!>" (v') "[[Hls Hgd] %Hv]". have -> : v' = VInt 5 by apply fv_lift_int, Hv.
    iApply "HΦ". iExists g, cs. iFrame.
  Qed.

  Lemma decode_ptr_wf (bs : list abyte) v : decode_value MPtr bs = Some v → val_wf MPtr v.
  Proof. simpl. destruct (decode_ptr bs); simpl; [|done]. intros [= <-]. constructor. Qed.

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
      [done|apply PTR_SIZE_pos|by apply (decode_encode_value MPtr (VPtr lp)); constructor|].
    iIntros (g cs) "Hls Hgd #Hnc".
    wp_bind (Store _ _ _ _).
    iApply (wp_pcell_move _ l l' with "[$Hls $Hnc $Hl']");
      [done|constructor|apply decode_ptr_wf|done|].
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
      with "[Hedges] [] [-]"); [done|apply Nat.ltb_lt; reflexivity|..].
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
End pcell_tests.

Print Assumptions test_pcell_read.
Print Assumptions test_pcell_lifecycle.
Print Assumptions test_pcell_atomic.
Print Assumptions test_pcell_read_guarded.
Print Assumptions test_pcell_typed_move.
Print Assumptions test_pcell_nested.
