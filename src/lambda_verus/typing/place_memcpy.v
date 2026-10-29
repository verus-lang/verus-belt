(** * Copying values of any size into and out of places

  The leaf rules of [place_own.v] read and write values of size 1, with
  a single load or store. This file adds memcpy-style rules ([e1 <-{n} !e2],
  [lang/lib/memcpy.v]) for values of any size, as [type_memcpy_instr] in [programs.v]:
  - into a leaf of an owned place ([type_memcpy_oplace_instr]), from any path that can be
    read ([typed_read], e.g. a local variable, moving out of it, or a unique borrow of a
    [Copy] type); the old value of the leaf is resolved and its type becomes the type of
    the new value, as [type_write_oplace_instr] (below no sum, [pctx_nosum], see
    [pctx_retype]); [type_memcpy_oplace_same_instr] keeps the type of the leaf, at any
    path (also through sums);
  - out of a leaf of an owned place ([type_memcpy_from_oplace_instr]: a move, which leaves
    the leaf uninitialized, [↯ n]; [type_memcpy_copy_from_oplace_instr]: a copy of a
    [Copy] value, at any path), into any path that can be written ([typed_write]).
  For places rooted at a value (e.g. at a unique borrow), below any number of unique
  borrows, see [type_memcpy_vplace_deep_instr] and [type_memcpy_copy_from_vplace_deep_instr]
  ([place_deep.v]).
  All rules work at any path, also below owned pointers: the address of the leaf is
  computed by the program ([pctx_expr], one load per owned pointer above the leaf). *)

From iris.proofmode Require Import proofmode.
From lrust.lang Require Import proofmode memcpy.
From lrust.typing Require Export type ltype lpath.
From lrust.typing Require Import type_context programs programs_util lft_contexts
  uniq_util uniq_bor product own uninit freeable_util place_own.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section typing.
  Context `{!typeG Σ}.

  (** * Owned places *)

  (** Copying a value of any size into the leaf at the hole of [K] of an owned place,
      from a path [pr] that can be read: the old value of the leaf is resolved, and the
      type of the leaf becomes the type of the new value. *)
  Lemma type_memcpy_oplace_instr {𝔅 𝔅' 𝔄 ℭ ℭ'} E L I p pr n (K: pctx 𝔅 𝔄) `{!PctxNoUniq K} (ty: type 𝔅)
      (tyr: type ℭ) (tyr': type ℭ') (tyb: type 𝔅') gtr str Φ (sz: Z) :
    ty_size ty = ty_size tyb → resolve E L ty Φ → typed_read E L tyr tyb tyr' gtr str →
    sz = ty_size tyb → pctx_nosum K →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K (OfTy ty); pr ◁ tyr] (pctx_expr K p <-{sz} !pr)
      (λ _, +[p ◁ₗown{n} pctx_plug (pctx_retype K 𝔅') (OfTy tyb); pr ◁ tyr'])
      (λ post '-[x; b], λ mask π, Φ (pctx_get K x.1.2) π →
        ∀ zr, str b zr → post -[((x.1.1, pctx_reset K x.1.2 (gtr b)), x.2); zr] mask π).
  Proof.
    iIntros (Hsz Rslv Rd -> Hns tid post mask iκs [x [b []]])
      "#LFT #TIME #PROPH #UNIQ #E L I (Tp & Tr & _) Obs".
    destruct x as [[l x₀] ζm].
    rewrite /tctx_elt_interp.
    iDestruct "Tp" as (v Hp D d g) "(#⧖ & ⧗p & -> & %Hle & Fr & Own)".
    have ?: Closed [] (pctx_expr K p).
    { apply pctx_expr_closed. by eapply eval_path_closed. }
    rewrite /ltype_own lty_pat_plug lty_rfn_plug ltype_own_plug.
    iDestruct "Own" as "[L1 Rest]". iSimpl in "L1".
    iDestruct "L1" as (? ->) "[Pt1 Gho1]".
    iDestruct (pctx_own_mode_le with "Rest") as %Hk.
    set k0 := pctx_mode K 0.
    set y := pctx_get K x₀.
    set lr := (l, repeat [] (lty_size (pctx_plug K (OfTy ty)))).
    set dh := pctx_depth K d.
    have Hdh: dh ≤ d. { rewrite /dh pctx_depth_sub. lia. }
    destruct (oplace_loc_empty K (OfTy ty) x₀ l) as [l' HlK]. simpl in HlK.
    (* The address of the hole, and the source. *)
    iMod lc_zero as "£0".
    wp_bind (pctx_expr K p).
    iApply (wp_wand with "[Rest £0]").
    { iApply (wp_pctx_expr K (ty_size ty) 1 x₀ ζm [] d g tid lr p True True 0
        with "[] £0 [] Rest").
      - rewrite /lr -heap_cloc_mapsto_empty. iApply guards_true.
      - iApply wp_wand; [by iApply wp_eval_path|]. by iIntros (?) "->". }
    iIntros (w) "(-> & _ & _ & Rest)".
    rewrite HlK /=.
    wp_bind pr. iApply (wp_hasty with "Tr"). iIntros (vr dr Hpr) "#⧖r Tr".
    (* The step gives cumulative time receipts: for credits, and to raise the depth of
       the place to the depth of the new value below [k0] owned pointers. *)
    iCombine "⧖ ⧖r" as "⧖m".
    iApply (wp_cumulative_time_receipt_linear with "TIME ⧖m"); [solve_ndisj|].
    iIntros "⧗". iApply wp_fupd.
    iDestruct (cumulative_time_receipt_mono (1 + S k0) with "⧗") as "⧗"; [lia|].
    iDestruct (cumulative_time_receipt_sep with "⧗") as "[⧗c ⧗k]".
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗c ⧖m") as "[#⧖S £]";
      [solve_ndisj|].
    iMod (cumulative_persistent_time_receipt with "TIME ⧗k ⧖r") as "#⧖k"; [solve_ndisj|].
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    set M := D `max` dr.
    iDestruct (lc_weaken (pctx_mode K 1 + (1 + (1 + dh*(g+1))) + (dr + 1) + 6 * (M + 1))%nat
      with "£") as "[[[£k [£r £s]] £d] £m]"; [rewrite /advance_credits pctx_mode_add; nia|].
    iMod (lc_fupd_elim_laterN with "£k Gho1") as "Gho1".
    (* Resolve the old value. *)
    iDestruct (Rslv _ (⊤ ∖ (⊤ ∖ ↑Nllft ∖ ↑prophN ∖ ↑timeN ∖ ↑uniqN))
      with "LFT PROPH UNIQ TIME E Ghalf H2 Gho1") as "ToObs"; [set_solver|].
    iMod (lc_fupd_elim_later with "£r ToObs") as "ToObs".
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iDestruct (lc_step_fupdN_elim_later with "£s ToObs") as "ToObs".
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iMod (fupd_mask_mono with "ToObs") as "[Obs' H2]"; [solve_ndisj|].
    (* Read the source. *)
    iMod (Rd with "LFT E Ghalf H2 Tr £d")
      as (lb vlb_c vlb HR Hvr Hlen) "(Hr & #Hrpt & Retether & _ & Own' & Totyr')".
    iDestruct "Own'" as "[Gb #>%Phys]".
    have Hlenb: length vlb = ty_size tyb by rewrite -Phys ty_size_eq.
    iMod (mapsto_vec_untether _ _ _ ∅ with "Pt1") as (vl) "[Pt1 [%Hvl _]]".
    have Hlenl: length vl = ty_size tyb by rewrite Hvl ty_size_eq.
    injection Hvr as ->.
    iApply (wp_memcpy_guarded _ (l', repeat [] (ty_size ty)) lb vl vlb_c True%I HR _ (M + 1)
      with "TIME [Pt1 Hr £m]"); [solve_ndisj|lia|lia| |].
    { iFrame "Pt1 Hr ⧖S £m". iSplit.
      - rewrite -heap_cloc_mapsto_empty. iApply guards_true.
      - iApply (lguards_weaken_later with "Hrpt"). lia. }
    iIntros "!> (Pt1 & _ & Hr)".
    iDestruct ("Retether" $! l' (repeat [] (ty_size ty)) with "[Pt1]") as "Ret".
    { rewrite -heap_cloc_mapsto_empty. by iFrame. }
    iMod (fupd_mask_mono with "Ret") as "[_ Pt1]"; [set_solver|].
    iMod ("Totyr'" with "Hr") as (zr Hzr) "(H2 & Tr)".
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    (* Close the place at the new value. *)
    set d'' := (dr + k0) `max` d. set g'' := dr `max` g.
    have Hdh'': dr ≤ pctx_depth K d''. { rewrite pctx_depth_sub. lia. }
    iAssert (▷ ty_gho_own tyb (gtr b) (pctx_depth K d'') g'' tid)%I with "[Gb]" as "Gb".
    { iNext. iDestruct (ty_gho_own_depth_mono _ dr dr (pctx_depth K d'') g'' with "Gb")
        as "[$ _]"; lia. }
    iDestruct (pctx_own_depth_mono _ _ _ _ _ _ _ _ d'' g'' with "Rest") as "Rest"; [lia..|].
    iCombine "⧖ ⧖k" as "⧖D".
    iModIntro. iExists -[((l, pctx_reset K x₀ (gtr b)), ζm); zr]. iFrame "L I".
    iSplitR "Obs Obs'".
    { iSplitR "Tr"; [|iSplitL; [|done]].
      - rewrite /tctx_elt_interp. iExists #l. iSplit; [done|].
        iExists (D `max` (S k0 + dr)), d'', g''. iFrame "⧖D".
        rewrite (lty_nrc_plug_retype K (OfTy ty) (OfTy tyb)) //.
        rewrite (lty_size_plug_retype K (OfTy ty) (OfTy tyb)) /=; [|done|lia].
        iFrame "⧗p Fr". iSplit; [done|]. iSplit; [iPureIntro; lia|].
        rewrite /ltype_own lty_pat_plug lty_rfn_plug pctx_get_reset ltype_own_plug
          pctx_own_reset // pctx_loc_reset // pctx_mode_retype pctx_depth_retype /= -Hsz.
        rewrite HlK. iFrame "Rest".
        iExists (gtr b). iSplit; [done|]. rewrite /ofty_owned Phys. iFrame "Pt1".
        rewrite pctx_mode_add /=. iNext. by iApply bi.laterN_intro.
      - iExists #lb.1, dr. iFrame "⧖r Tr". by rewrite Hpr. }
    iCombine "Obs Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=> π [Hπ HΦ].
    by apply Hπ.
  Qed.
  Lemma type_memcpy_oplace_same_instr {𝔅 𝔄 ℭ ℭ'} E L I p pr n (K: pctx 𝔅 𝔄) `{!PctxNoUniq K} (ty: type 𝔅)
      (tyr: type ℭ) (tyr': type ℭ') gtr str Φ (sz: Z) :
    resolve E L ty Φ → typed_read E L tyr ty tyr' gtr str → sz = ty_size ty →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K (OfTy ty); pr ◁ tyr] (pctx_expr K p <-{sz} !pr)
      (λ _, +[p ◁ₗown{n} pctx_plug K (OfTy ty); pr ◁ tyr'])
      (λ post '-[x; b], λ mask π, Φ (pctx_get K x.1.2) π →
        ∀ zr, str b zr → post -[((x.1.1, pctx_set K x.1.2 (gtr b)), x.2); zr] mask π).
  Proof.
    iIntros (Rslv Rd -> tid post mask iκs [x [b []]])
      "#LFT #TIME #PROPH #UNIQ #E L I (Tp & Tr & _) Obs".
    destruct x as [[l x₀] ζm].
    rewrite /tctx_elt_interp.
    iDestruct "Tp" as (v Hp D d g) "(#⧖ & ⧗p & -> & %Hle & Fr & Own)".
    have ?: Closed [] (pctx_expr K p).
    { apply pctx_expr_closed. by eapply eval_path_closed. }
    rewrite /ltype_own lty_pat_plug lty_rfn_plug ltype_own_plug.
    iDestruct "Own" as "[L1 Rest]". iSimpl in "L1".
    iDestruct "L1" as (? ->) "[Pt1 Gho1]".
    iDestruct (pctx_own_mode_le with "Rest") as %Hk.
    iDestruct (pctx_own_in with "Rest") as %Hin.
    set k0 := pctx_mode K 0.
    set y := pctx_get K x₀.
    set lr := (l, repeat [] (lty_size (pctx_plug K (OfTy ty)))).
    set dh := pctx_depth K d.
    have Hdh: dh ≤ d. { rewrite /dh pctx_depth_sub. lia. }
    destruct (oplace_loc_empty K (OfTy ty) x₀ l) as [l' HlK]. simpl in HlK.
    (* The address of the hole, and the source. *)
    iMod lc_zero as "£0".
    wp_bind (pctx_expr K p).
    iApply (wp_wand with "[Rest £0]").
    { iApply (wp_pctx_expr K (ty_size ty) 1 x₀ ζm [] d g tid lr p True True 0
        with "[] £0 [] Rest").
      - rewrite /lr -heap_cloc_mapsto_empty. iApply guards_true.
      - iApply wp_wand; [by iApply wp_eval_path|]. by iIntros (?) "->". }
    iIntros (w) "(-> & _ & _ & Rest)".
    rewrite HlK /=.
    wp_bind pr. iApply (wp_hasty with "Tr"). iIntros (vr dr Hpr) "#⧖r Tr".
    (* The step gives cumulative time receipts: for credits, and to raise the depth of
       the place to the depth of the new value below [k0] owned pointers. *)
    iCombine "⧖ ⧖r" as "⧖m".
    iApply (wp_cumulative_time_receipt_linear with "TIME ⧖m"); [solve_ndisj|].
    iIntros "⧗". iApply wp_fupd.
    iDestruct (cumulative_time_receipt_mono (1 + S k0) with "⧗") as "⧗"; [lia|].
    iDestruct (cumulative_time_receipt_sep with "⧗") as "[⧗c ⧗k]".
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗c ⧖m") as "[#⧖S £]";
      [solve_ndisj|].
    iMod (cumulative_persistent_time_receipt with "TIME ⧗k ⧖r") as "#⧖k"; [solve_ndisj|].
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    set M := D `max` dr.
    iDestruct (lc_weaken (pctx_mode K 1 + (1 + (1 + dh*(g+1))) + (dr + 1) + 6 * (M + 1))%nat
      with "£") as "[[[£k [£r £s]] £d] £m]"; [rewrite /advance_credits pctx_mode_add; nia|].
    iMod (lc_fupd_elim_laterN with "£k Gho1") as "Gho1".
    (* Resolve the old value. *)
    iDestruct (Rslv _ (⊤ ∖ (⊤ ∖ ↑Nllft ∖ ↑prophN ∖ ↑timeN ∖ ↑uniqN))
      with "LFT PROPH UNIQ TIME E Ghalf H2 Gho1") as "ToObs"; [set_solver|].
    iMod (lc_fupd_elim_later with "£r ToObs") as "ToObs".
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iDestruct (lc_step_fupdN_elim_later with "£s ToObs") as "ToObs".
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iMod (fupd_mask_mono with "ToObs") as "[Obs' H2]"; [solve_ndisj|].
    (* Read the source. *)
    iMod (Rd with "LFT E Ghalf H2 Tr £d")
      as (lb vlb_c vlb HR Hvr Hlen) "(Hr & #Hrpt & Retether & _ & Own' & Totyr')".
    iDestruct "Own'" as "[Gb #>%Phys]".
    have Hlenb: length vlb = ty_size ty by rewrite -Phys ty_size_eq.
    iMod (mapsto_vec_untether _ _ _ ∅ with "Pt1") as (vl) "[Pt1 [%Hvl _]]".
    have Hlenl: length vl = ty_size ty by rewrite Hvl ty_size_eq.
    injection Hvr as ->.
    iApply (wp_memcpy_guarded _ (l', repeat [] (ty_size ty)) lb vl vlb_c True%I HR _ (M + 1)
      with "TIME [Pt1 Hr £m]"); [solve_ndisj|lia|lia| |].
    { iFrame "Pt1 Hr ⧖S £m". iSplit.
      - rewrite -heap_cloc_mapsto_empty. iApply guards_true.
      - iApply (lguards_weaken_later with "Hrpt"). lia. }
    iIntros "!> (Pt1 & _ & Hr)".
    iDestruct ("Retether" $! l' (repeat [] (ty_size ty)) with "[Pt1]") as "Ret".
    { rewrite -heap_cloc_mapsto_empty. by iFrame. }
    iMod (fupd_mask_mono with "Ret") as "[_ Pt1]"; [set_solver|].
    iMod ("Totyr'" with "Hr") as (zr Hzr) "(H2 & Tr)".
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    (* Close the place at the new value. *)
    set d'' := (dr + k0) `max` d. set g'' := dr `max` g.
    have Hdh'': dr ≤ pctx_depth K d''. { rewrite pctx_depth_sub. lia. }
    iAssert (▷ ty_gho_own ty (gtr b) (pctx_depth K d'') g'' tid)%I with "[Gb]" as "Gb".
    { iNext. iDestruct (ty_gho_own_depth_mono _ dr dr (pctx_depth K d'') g'' with "Gb")
        as "[$ _]"; lia. }
    iDestruct (pctx_own_depth_mono _ _ _ _ _ _ _ _ d'' g'' with "Rest") as "Rest"; [lia..|].
    iCombine "⧖ ⧖k" as "⧖D".
    iModIntro. iExists -[((l, pctx_set K x₀ (gtr b)), ζm); zr]. iFrame "L I".
    iSplitR "Obs Obs'".
    { iSplitR "Tr"; [|iSplitL; [|done]].
      - rewrite /tctx_elt_interp. iExists #l. iSplit; [done|].
        iExists (D `max` (S k0 + dr)), d'', g''. iFrame "⧖D".
        iFrame "⧗p Fr". iSplit; [done|]. iSplit; [iPureIntro; lia|].
        rewrite /ltype_own lty_pat_plug lty_rfn_plug pctx_get_set ltype_own_plug
          pctx_own_set // pctx_loc_set //.
        rewrite HlK. iFrame "Rest".
        iExists (gtr b). iSplit; [done|]. rewrite /ofty_owned Phys. iFrame "Pt1".
        rewrite pctx_mode_add /=. iNext. by iApply bi.laterN_intro.
      - iExists #lb.1, dr. iFrame "⧖r Tr". by rewrite Hpr. }
    iCombine "Obs Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=> π [Hπ HΦ].
    by apply Hπ.
  Qed.
  Lemma vec_of_list_length {A} (vl: list A) n : length vl = n → ∃ w: vec A n, vec_to_list w = vl.
  Proof. intros <-. exists (list_to_vec vl). apply vec_to_list_to_vec. Qed.

  (** Moving a value of any size out of the leaf at the hole of [K] of an owned place,
      into a path [pw] that can be written: the leaf becomes uninitialized (its type is
      [↯ n], its value is the old contents of the cells), the old value of the
      destination is resolved. *)
  Lemma type_memcpy_from_oplace_instr {𝔅 𝔄 ℭ ℭ' 𝔇} E L I pw p n (K: pctx 𝔅 𝔄) `{!PctxNoUniq K} (ty: type 𝔅)
      (tyw: type ℭ) (tyw': type ℭ') (tyb: type 𝔇) gtw stw Φ (sz: Z) :
    typed_write E L tyw tyb tyw' ty gtw stw → resolve' E L tyb Φ →
    sz = ty_size ty → pctx_nosum K →
    typed_instr E L I +[pw ◁ tyw; p ◁ₗown{n} pctx_plug K (OfTy ty)] (pw <-{sz} !(pctx_expr K p))
      (λ _, +[pw ◁ tyw';
        p ◁ₗown{n} pctx_plug (pctx_retype K (uninitₛ (ty_size ty))) (OfTy (↯ (ty_size ty)))])
      (λ post '-[a; x], λ mask π, Φ (gtw a) π (∀ zw (junk: ~~ (uninitₛ (ty_size ty))),
        stw a (pctx_get K x.1.2) zw →
        post -[zw; ((x.1.1, pctx_reset K x.1.2 junk), x.2)] mask π)).
  Proof.
    iIntros ([Eq Wrt] Rslv -> Hns tid post mask iκs [a [x []]])
      "#LFT #TIME #PROPH #UNIQ #E L I (Tw & Tp & _) Obs".
    destruct x as [[l x₀] ζm].
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    wp_bind pw. iApply (wp_hasty with "Tw"). iIntros (vw dw Hpw) "#⧖w Tw".
    iMod (Wrt with "LFT UNIQ E Ghalf H1 Tw") as (lw dw' HW Heqv Hdw) "[Old (HW & #Hwpt & Totyw)]".
    injection Heqv as ->.
    rewrite /tctx_elt_interp.
    iDestruct "Tp" as (v Hp D d g) "(#⧖ & ⧗p & -> & %Hle & Fr & Own)".
    have ?: Closed [] (pctx_expr K p).
    { apply pctx_expr_closed. by eapply eval_path_closed. }
    rewrite /ltype_own lty_pat_plug lty_rfn_plug ltype_own_plug.
    iDestruct "Own" as "[L1 Rest]". iSimpl in "L1".
    iDestruct "L1" as (? ->) "[Pt1 Gho1]".
    iDestruct (pctx_own_mode_le with "Rest") as %Hk.
    set y := pctx_get K x₀.
    set lr := (l, repeat [] (lty_size (pctx_plug K (OfTy ty)))).
    set dh := pctx_depth K d.
    have Hdh: dh ≤ d. { rewrite /dh pctx_depth_sub. lia. }
    destruct (oplace_loc_empty K (OfTy ty) x₀ l) as [l' HlK]. simpl in HlK.
    (* The address of the hole. *)
    iMod lc_zero as "£0".
    wp_bind (pctx_expr K p).
    iApply (wp_wand with "[Rest £0]").
    { iApply (wp_pctx_expr K (ty_size ty) 1 x₀ ζm [] d g tid lr p True True 0
        with "[] £0 [] Rest").
      - rewrite /lr -heap_cloc_mapsto_empty. iApply guards_true.
      - iApply wp_wand; [by iApply wp_eval_path|]. by iIntros (?) "->". }
    iIntros (w) "(-> & _ & _ & Rest)".
    rewrite HlK /=.
    iCombine "⧖ ⧖w" as "⧖m".
    iApply wp_fupd. iApply (wp_persistent_time_receipt with "TIME ⧖m"); [solve_ndisj|].
    iIntros "£ #⧖S".
    set M := D `max` dw.
    iDestruct (lc_weaken (1 + (1 + (1 + dw'*(dw+1))) + pctx_mode K 1 + 6 * S M +
      (1 + (dw + 1)) + (2*M*M + 4*M + 2))%nat with "£")
      as "[[[[[£a [£r £s]] £k] £m] [£o £o']] £w]"; [rewrite /advance_credits pctx_mode_add; nia|].
    (* Resolve the old value of the destination. *)
    iMod (lc_fupd_elim_later with "£a Old") as "Old".
    iMod (guarded_upd_run with "Ghalf H2 Old") as "[H2 (%vl & Ptw & Gb & %Physb)]"; [solve_ndisj|].
    have Hlenw: length vl = ty_size ty by rewrite -Physb ty_size_eq Eq.
    iDestruct (Rslv _ (⊤ ∖ (⊤ ∖ ↑Nllft ∖ ↑prophN ∖ ↑timeN ∖ ↑uniqN))
      with "LFT PROPH UNIQ TIME E Ghalf H2 Gb") as "ToObs"; [set_solver|].
    iMod (lc_fupd_elim_later with "£r ToObs") as "ToObs".
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iDestruct (lc_step_fupdN_elim_later with "£s ToObs") as "ToObs".
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iMod (fupd_mask_mono with "ToObs") as "[Obs' H2]"; [solve_ndisj|].
    (* The contents of the leaf, as concrete values. *)
    iMod (lc_fupd_elim_laterN with "£k Gho1") as "Gho1".
    iMod (mapsto_vec_untether _ _ _ ∅ with "Pt1") as (vlc) "[Pt1 [%Hvlc Retether]]".
    have Hlenc: length vlc = ty_size ty by rewrite Hvlc ty_size_eq.
    iMod (mapsto_vec_untether _ _ _ ∅ with "Ptw") as (vlw) "[Ptw [%Hvlw _]]".
    iEval (rewrite -Hlenc -heap_cloc_mapsto_val_empty heap_mapsto_cells_empty) in "Pt1".
    iApply (wp_memcpy_guarded _ lw (l', repeat [] (length vlc)) vlw vlc HW
      (l' ↦[^ repeat [] (length vlc)]∗ vlc) _ (S M) with "TIME [Ptw Pt1 HW £m]");
      [solve_ndisj|lia|lia| |].
    { iFrame "Ptw Pt1 HW ⧖S £m". iSplit.
      - iApply (lguards_weaken_later with "Hwpt"). lia.
      - iApply (lguards_weaken_later _ _ _ 0); [lia|iApply guards_refl]. }
    iIntros "!> (Ptw & HW & Pt1)".
    (* Put the contents (with their ghost cells) into the destination. *)
    destruct lw as [lw1 cw].
    leaf_open_laters "Hwpt" with "HW" as "A"; [solve_ndisj|].
    iMod (lc_fupd_elim_later with "£o A") as "A".
    iMod (lc_fupd_elim_laterN with "£o' A") as "A". iMod "A" as "[Pre back]".
    iDestruct ("Retether" $! (lw1, cw) with "[Pre Ptw]") as "Ret"; [by iFrame|].
    iMod (fupd_mask_mono with "Ret") as "[Pre Ptw]"; [set_solver|].
    iMod ("back" with "Pre") as "HW".
    iMod ("Totyw" $! y M with "[Ptw Gho1] ⧖S £w HW") as (zw) "(H1 & %Hzw & Tw)".
    { iNext. iExists (ty_phys ty y tid). iFrame "Ptw". iSplit; [|done].
      iDestruct (ty_gho_own_depth_mono _ dh g M (S M) with "Gho1") as "[$ _]"; lia. }
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    (* The leaf is uninitialized. *)
    destruct (vec_of_list_length vlc (ty_size ty) Hlenc) as [junk Hjunk].
    iModIntro. iExists -[zw; ((l, pctx_reset (𝔅':=uninitₛ (ty_size ty)) K x₀ junk), ζm)]. iFrame "L I".
    iSplitR "Obs Obs'".
    { iSplitL "Tw"; [|iSplitL; [|done]].
      - iExists #lw1, (dw `max` S M). iSplit; [by rewrite Hpw|].
        iSplit; [iApply (persistent_time_receipt_mono with "⧖S"); lia|].
        iDestruct "Tw" as "[Gw Physw]". iFrame "Physw".
        iDestruct (ty_gho_own_depth_mono with "Gw") as "[$ _]"; lia.
      - rewrite /tctx_elt_interp. iExists #l. iSplit; [done|].
        iExists D, d, g. iFrame "⧖".
        rewrite (lty_nrc_plug_retype K (OfTy ty) (OfTy (↯ (ty_size ty)))) //.
        rewrite (lty_size_plug_retype K (OfTy ty) (OfTy (↯ (ty_size ty)))) /=; [|done|done].
        iFrame "⧗p Fr". iSplit; [done|]. iSplit; [done|].
        rewrite /ltype_own lty_pat_plug lty_rfn_plug pctx_get_reset ltype_own_plug
          pctx_own_reset // pctx_loc_reset // pctx_mode_retype pctx_depth_retype /=.
        rewrite HlK. iFrame "Rest".
        iExists junk. iSplit; [done|]. rewrite /ofty_owned /= Hjunk.
        rewrite -heap_mapsto_cells_empty heap_cloc_mapsto_val_empty Hlenc.
        iFrame "Pt1". by iApply bi.laterN_intro. }
    iCombine "Obs Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=> π [Hπ HΦ].
    apply HΦ in Hπ. by apply Hπ.
  Qed.

  (** Copying a value of any size of a [Copy] type out of the leaf at the hole of [K] of
      an owned place, into a path [pw] that can be written. The leaf does not change (so
      any [K] is allowed, also through sums). *)
  Lemma type_memcpy_copy_from_oplace_instr {𝔅 𝔄 ℭ ℭ' 𝔇} E L I pw p n (K: pctx 𝔅 𝔄) `{!PctxNoUniq K}
      (ty: type 𝔅) (tyw: type ℭ) (tyw': type ℭ') (tyb: type 𝔇) gtw stw Φ (sz: Z) :
    Copy ty → typed_write E L tyw tyb tyw' ty gtw stw → resolve' E L tyb Φ →
    sz = ty_size ty →
    typed_instr E L I +[pw ◁ tyw; p ◁ₗown{n} pctx_plug K (OfTy ty)] (pw <-{sz} !(pctx_expr K p))
      (λ _, +[pw ◁ tyw'; p ◁ₗown{n} pctx_plug K (OfTy ty)])
      (λ post '-[a; x], λ mask π, Φ (gtw a) π (∀ zw, stw a (pctx_get K x.1.2) zw →
        post -[zw; x] mask π)).
  Proof.
    iIntros (Hcopy [Eq Wrt] Rslv -> tid post mask iκs [a [x []]])
      "#LFT #TIME #PROPH #UNIQ #E L I (Tw & Tp & _) Obs".
    destruct x as [[l x₀] ζm].
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    wp_bind pw. iApply (wp_hasty with "Tw"). iIntros (vw dw Hpw) "#⧖w Tw".
    iMod (Wrt with "LFT UNIQ E Ghalf H1 Tw") as (lw dw' HW Heqv Hdw) "[Old (HW & #Hwpt & Totyw)]".
    injection Heqv as ->.
    rewrite /tctx_elt_interp.
    iDestruct "Tp" as (v Hp D d g) "(#⧖ & ⧗p & -> & %Hle & Fr & Own)".
    have ?: Closed [] (pctx_expr K p).
    { apply pctx_expr_closed. by eapply eval_path_closed. }
    rewrite /ltype_own lty_pat_plug lty_rfn_plug ltype_own_plug.
    iDestruct "Own" as "[L1 Rest]". iSimpl in "L1".
    iDestruct "L1" as (? ->) "[Pt1 #Gho1]".
    iDestruct (pctx_own_mode_le with "Rest") as %Hk.
    set y := pctx_get K x₀.
    set lr := (l, repeat [] (lty_size (pctx_plug K (OfTy ty)))).
    set dh := pctx_depth K d.
    have Hdh: dh ≤ d. { rewrite /dh pctx_depth_sub. lia. }
    destruct (oplace_loc_empty K (OfTy ty) x₀ l) as [l' HlK]. simpl in HlK.
    (* The address of the hole. *)
    iMod lc_zero as "£0".
    wp_bind (pctx_expr K p).
    iApply (wp_wand with "[Rest £0]").
    { iApply (wp_pctx_expr K (ty_size ty) 1 x₀ ζm [] d g tid lr p True True 0
        with "[] £0 [] Rest").
      - rewrite /lr -heap_cloc_mapsto_empty. iApply guards_true.
      - iApply wp_wand; [by iApply wp_eval_path|]. by iIntros (?) "->". }
    iIntros (w) "(-> & _ & _ & Rest)".
    rewrite HlK /=.
    iCombine "⧖ ⧖w" as "⧖m".
    iApply wp_fupd. iApply (wp_persistent_time_receipt with "TIME ⧖m"); [solve_ndisj|].
    iIntros "£ #⧖S".
    set M := D `max` dw.
    iDestruct (lc_weaken (1 + (1 + (1 + dw'*(dw+1))) + pctx_mode K 1 + 6 * S M +
      (2*M*M + 4*M + 2))%nat with "£")
      as "[[[[£a [£r £s]] £k] £m] £w]"; [rewrite /advance_credits pctx_mode_add; nia|].
    (* Resolve the old value of the destination. *)
    iMod (lc_fupd_elim_later with "£a Old") as "Old".
    iMod (guarded_upd_run with "Ghalf H2 Old") as "[H2 (%vl & Ptw & Gb & %Physb)]"; [solve_ndisj|].
    have Hlenw: length vl = ty_size ty by rewrite -Physb ty_size_eq Eq.
    iDestruct (Rslv _ (⊤ ∖ (⊤ ∖ ↑Nllft ∖ ↑prophN ∖ ↑timeN ∖ ↑uniqN))
      with "LFT PROPH UNIQ TIME E Ghalf H2 Gb") as "ToObs"; [set_solver|].
    iMod (lc_fupd_elim_later with "£r ToObs") as "ToObs".
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iDestruct (lc_step_fupdN_elim_later with "£s ToObs") as "ToObs".
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iMod (fupd_mask_mono with "ToObs") as "[Obs' H2]"; [solve_ndisj|].
    (* The contents of the leaf are concrete values. *)
    iMod (lc_fupd_elim_laterN with "£k Gho1") as "#Gho1'".
    iDestruct (copy_concrete with "Gho1'") as %Hconc.
    iMod (mapsto_vec_untether' _ _ _ ∅ with "Pt1") as (vlc) "(Pt1 & %Hvlc & _ & %Hc)".
    have Hphys := Hc Hconc.
    have Hlenc: length vlc = ty_size ty by rewrite Hvlc ty_size_eq.
    iMod (mapsto_vec_untether _ _ _ ∅ with "Ptw") as (vlw) "[Ptw [%Hvlw _]]".
    iEval (rewrite -Hlenc -heap_cloc_mapsto_val_empty heap_mapsto_cells_empty) in "Pt1".
    iApply (wp_memcpy_guarded _ lw (l', repeat [] (length vlc)) vlw vlc HW
      (l' ↦[^ repeat [] (length vlc)]∗ vlc) _ (S M) with "TIME [Ptw Pt1 HW £m]");
      [solve_ndisj|lia|lia| |].
    { iFrame "Ptw Pt1 HW ⧖S £m". iSplit.
      - iApply (lguards_weaken_later with "Hwpt"). lia.
      - iApply (lguards_weaken_later _ _ _ 0); [lia|iApply guards_refl]. }
    iIntros "!> (Ptw & HW & Pt1)".
    iMod ("Totyw" $! y M with "[Ptw] ⧖S £w HW") as (zw) "(H1 & %Hzw & Tw)".
    { iNext. iExists (ty_phys ty y tid). rewrite {1}Hphys. iFrame "Ptw". iSplit; [|done].
      iDestruct (ty_gho_own_depth_mono _ dh g M (S M) with "Gho1'") as "[$ _]"; lia. }
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iModIntro. iExists -[zw; ((l, x₀), ζm)]. iFrame "L I".
    iSplitR "Obs Obs'".
    { iSplitL "Tw"; [|iSplitL; [|done]].
      - iExists #lw.1, (dw `max` S M). iSplit; [by rewrite Hpw|].
        iSplit; [iApply (persistent_time_receipt_mono with "⧖S"); lia|].
        iDestruct "Tw" as "[Gw Physw]". iFrame "Physw".
        iDestruct (ty_gho_own_depth_mono with "Gw") as "[$ _]"; lia.
      - rewrite /tctx_elt_interp. iExists #l. iSplit; [done|].
        iExists D, d, g. iFrame "⧖ ⧗p Fr". iSplit; [done|]. iSplit; [done|].
        rewrite /ltype_own lty_pat_plug lty_rfn_plug ltype_own_plug /=.
        rewrite HlK. iFrame "Rest".
        iExists y. iSplit; [done|]. rewrite /ofty_owned Hphys. iFrame "Gho1".
        rewrite -heap_mapsto_cells_empty heap_cloc_mapsto_val_empty Hlenc. iFrame "Pt1". }
    iCombine "Obs Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=> π [Hπ HΦ].
    apply HΦ in Hπ. by apply Hπ.
  Qed.

  (** * Places rooted at a unique borrow *)

End typing.