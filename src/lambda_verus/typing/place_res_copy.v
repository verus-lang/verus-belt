(** * Copies of any size below resolved unique borrows

  A [Copy] leaf of any size (unblocked or shared-blocked, [view_rleaf]) in the view of a
  resolved unique borrow ([ResUniqLty], [typing/place_res_ops.v]) is copied into any path
  that can be written ([type_memcpy_copy_from_oplace_res_instr], memcpy-style
  [pw <-{n} !(pctx_expr K2 (!(pctx_expr K p)))], as [type_memcpy_copy_from_oplace_pshr_instr]
  of [typing/place_deep.v] below a shared reference). The leaf is shared at the lifetime
  of the view at the hole, which must be alive; the place does not change.

  Resolved leaves [OfRes ty] are copied after their conversion to [OfTy ty] ([ResOwn],
  [tctx_oplace_res_to_ofty]) or to a shared reference ([OfRes (&uniq{κ} ty)],
  [type_oplace_res_uniq_to_shr_instr]), with the rules of [typing/place_deep.v]. See
  [~/verus-belt-phase3-design.md], section "Resolve to a readable state". *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From lrust.lang Require Import proofmode memcpy.
From lrust.typing Require Export type ltype lpath pctx_acc place_own.
From lrust.typing Require Import type_context programs programs_util lft_contexts
  uniq_util uniq_bor product own uninit freeable_util place_sum place_puniq
  place_pshr sum type_sum place_deep place_resolve place_res place_res_view place_res_rslv
  place_res_ops.
From lrust.util Require Import proph_bor.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section memcpy_res.
  Context `{!typeG Σ}.

  Lemma type_memcpy_copy_from_oplace_res_instr {ℭ 𝔅 𝔄 𝔇 𝔈 𝔈'} E L I pw p n
      (K: pctx (uniq_borₛ 𝔅) 𝔄) `{!PctxNoUniq K} κ (K2: pctx ℭ 𝔅) `{!PctxNoShr K2}
      (lt0: lty ℭ) (ty: type ℭ) κs
      (tyw: type 𝔈) (tyw': type 𝔈') (tyb: type 𝔇) gtw stw Φ (sz: Z) :
    view_rleaf lt0 ty κs → Copy ty → typed_write E L tyw tyb tyw' ty gtw stw →
    resolve' E L tyb Φ → sz = ty_size ty → lctx_lft_alive E L (pctx_salv K2 κ ⊓ κs) →
    typed_instr E L I +[pw ◁ tyw; p ◁ₗown{n} pctx_plug K (ResUniqLty (pctx_plug K2 lt0) κ)]
      (Seq Skip (pw <-{sz} !(pctx_expr K2 (!(pctx_expr K p)))))%E
      (λ _, +[pw ◁ tyw'; p ◁ₗown{n} pctx_plug K (ResUniqLty (pctx_plug K2 lt0) κ)])
      (λ post '-[a; x], λ mask π, Φ (gtw a) π (∀ zw,
        stw a (pctx_get K2 (uniq_bor_current (pctx_get K x.1.2))) zw → post -[zw; x] mask π)).
  Proof.
    iIntros (Hl Hcopy [Eq Wrt] Rslv -> Alv tid post mask iκs [a [x []]])
      "#LFT #TIME #PROPH #UNIQ #E L I (Tw & Tp & _) Obs".
    destruct x as [[l x₀] ζm].
    rewrite /tctx_elt_interp.
    iDestruct "Tp" as (v Hp D d g) "(#⧖ & ⧗p & -> & %Hle & Fr & Own)".
    have ?: Closed [] (pctx_expr K p).
    { apply pctx_expr_closed. by eapply eval_path_closed. }
    have ?: Closed [] (pctx_expr K2 (!(pctx_expr K p))%E).
    { apply pctx_expr_closed. apply _. }
    iDestruct "Tw" as (vw dw Hpw) "(#⧖w & Tw)".
    have ?: Closed [] pw by eapply eval_path_closed.
    iDestruct (Alv with "L E") as "#Alv".
    (* A step, for the credits of the address. *)
    wp_bind Skip. iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [set_solver|].
    iIntros "£ #⧖S". wp_let. iModIntro. wp_let.
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iMod (fractional.frac_split_guard_in_half with "H2 Ghalf")
      as (γ2) "[H2 [H3 [#Ghalf2 #Halfback2]]]"; [solve_ndisj|].
    iAssert (fractional.half γ2 &&{↑NllftG}&&> @[pctx_salv K2 κ ⊓ κs])%I as "#Hss".
    { iApply (guards_transitive with "Ghalf2 Alv"). }
    iAssert (fractional.half γ2 &&{↑NllftG}&&> @[pctx_salv K2 κ])%I as "#Hs".
    { iApply (guards_transitive with "Hss"). iApply llftl_intersect_incl_l. }
    iAssert (fractional.half γ2 &&{↑NllftG}&&> @[pctx_slft K2 κ ⊓ κs])%I as "#Hsl".
    { iApply (guards_transitive with "Hss"). iApply llftl_incl_glb;
        [|iApply llftl_intersect_incl_r].
      iApply llftl_incl_trans; [iApply llftl_intersect_incl_l|iApply pctx_salv_slft]. }
    set lt1 := ResUniqLty (pctx_plug K2 lt0) κ.
    rewrite /ltype_own lty_pat_plug lty_rfn_plug ltype_own_plug.
    iDestruct "Own" as "[H Rest]".
    iDestruct (pctx_own_mode_le with "Rest") as %Hk.
    set y := pctx_get K x₀.
    set q0 := pctx_path K [].
    set lr := (l, repeat [] (lty_size (pctx_plug K lt1))).
    set lK := pctx_loc K (lty_size lt1) x₀ lr.
    destruct (pctx_loc_empty K 1 x₀ l) as [lK0 HlK].
    have HlK': lK = (lK0, repeat [] 1).
    { rewrite /lK /lr lty_size_plug. exact HlK. }
    destruct y as [[[[[ly z] ξi] d0] g0] idx0] eqn:Hy.
    rewrite /= /res_node /=. iDestruct "H" as "[Pt N]".
    iDestruct (lc_weaken (pctx_mode K 1 + (advance_credits D - pctx_mode K 1)) with "£")
      as "[£m £]"; [rewrite /advance_credits pctx_mode_add; lia|].
    iMod (lc_fupd_elim_laterN with "£m N") as "(#Incl & %d' & %g' & %Hle' & V)".
    rewrite lty_pat_plug lty_rfn_plug (view_rleaf_rfn _ _ _ _ _ _ Hl).
    iDestruct (view_pctx_acc K2 κ lt0 0 (lty_pat lt0)
      (inl (PlaceIn (pctx_get K2 z))) z ζm (false :: q0) d' g' tid ly (fractional.half γ2)
      with "Hs V") as (dh gh) "([%Hdh [%Hgh %Hin]] & Vh & #Gs & Cl)".
    iDestruct (view_rleaf_shared with "Vh") as "[Vh #(Gpt & Shr & Pers)]"; [done|].
    set zh := pctx_get K2 z.
    rewrite (view_rleaf_size _ _ _ Hl).
    set lh := pctx_loc K2 (ty_size ty) z ly.
    have Hdl: pctx_dlev K2 ≤ D.
    { destruct Hle' as [Hle' _]. rewrite pctx_depth_sub in Hle'. lia. }
    have Hg': g' ≤ D by lia. have Hgh': gh ≤ D by lia.
    have ?: pctx_depth K d ≤ d by (rewrite pctx_depth_sub; lia).
    have Hm: pctx_mode K 1 ≤ D by (rewrite pctx_mode_add; lia).
    iDestruct (lc_weaken (3 * (g' + 1) * pctx_dlev K2 + (gh + 1)) with "£")
      as "[£w £g]".
    { rewrite /advance_credits. clear - Hdl Hg' Hgh' Hm. nia. }
    (* The destination. *)
    wp_bind pw. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->".
    iMod (Wrt with "LFT UNIQ E Ghalf H1 Tw") as (lw dw' HW Heqv Hdw) "[Old (HW & #Hwpt & Totyw)]".
    injection Heqv as ->.
    (* The address of the hole. *)
    wp_bind (pctx_expr K2 (!(pctx_expr K p))%E).
    iApply (wp_pctx_sexpr ⊤ K2 (ty_size ty) (g' + 1) (fractional.half γ2) z ly);
      [solve_ndisj|].
    wp_bind (pctx_expr K p).
    iMod lc_zero as "£0".
    iApply (wp_wand with "[Rest £0]").
    { iApply (wp_pctx_expr K 1 1 x₀ ζm [] d g tid lr p True True 0 with "[] £0 [] Rest").
      - rewrite /lr -heap_cloc_mapsto_empty. iApply guards_true.
      - iApply wp_wand; [by iApply wp_eval_path|]. by iIntros (?) "->". }
    iIntros (w) "(-> & _ & _ & Rest)".
    rewrite -/lK HlK' cell_mapsto_val. wp_read. iFrame "Gs £w H2".
    iSplit; [done|]. iIntros "H2".
    (* The (persistent) ownership of the value, from the sharing predicate. *)
    iDestruct (copy_shr with "Shr") as "#GGho".
    iDestruct (guards_transitive_right with "Hsl GGho") as "#GGho'".
    iAssert (|={⊤}=> ty_gho_own ty zh dh gh tid ∗ fractional.half γ2)%I
      with "[H2 £g]" as ">[#Gho H2]".
    { leaf_open_laters "GGho'" with "H2" as "Gho1"; [solve_ndisj|].
      iMod (lc_fupd_add_laterN with "£g Gho1") as "[#Gho1 Hclose]".
      iMod ("Hclose" with "Gho1") as "$". by iModIntro. }
    iDestruct (copy_concrete with "Gho") as %Hconc.
    (* The copy gives the other credits. *)
    iCombine "⧖ ⧖w" as "⧖m".
    iApply wp_fupd. iApply (wp_persistent_time_receipt with "TIME ⧖m"); [solve_ndisj|].
    iIntros "£ #⧖S'".
    set M := D `max` dw.
    have HM: 1 ≤ M ∧ g ≤ M ∧ dw ≤ M by rewrite /M; lia.
    iDestruct (lc_weaken ((1 + (1 + (1 + dw'*(dw+1)))) + (6 * S M + (2*M*M + 4*M + 2))) with "£")
      as "[[£o [£r £s]] [£m £t]]"; [rewrite /advance_credits; nia|].
    (* Resolve the old value of the destination. *)
    iMod (lc_fupd_elim_later with "£o Old") as "Old".
    iMod (guarded_upd_run with "Ghalf2 H3 Old") as "[H3 (%vl & Ptw & Gb & %Physb)]";
      [solve_ndisj|].
    iDestruct (Rslv _ (⊤ ∖ (⊤ ∖ ↑Nllft ∖ ↑prophN ∖ ↑timeN ∖ ↑uniqN))
      with "LFT PROPH UNIQ TIME E Ghalf2 H3 Gb") as "ToObs"; [set_solver|].
    iMod (lc_fupd_elim_later with "£r ToObs") as "ToObs".
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iDestruct (lc_step_fupdN_elim_later with "£s ToObs") as "ToObs".
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iMod (fupd_mask_mono with "ToObs") as "[Obs' H3]"; [solve_ndisj|].
    (* Copy. *)
    iMod (mapsto_vec_untether _ _ _ ∅ with "Ptw") as (vlw) "[Ptw [%Hvlw _]]".
    set vlc := to_concrete (ty_phys ty zh tid).
    have Hlenw: length vl = ty_size ty by rewrite -Physb ty_size_eq Eq.
    have Hlenc: length vlc = ty_size ty by rewrite /vlc length_to_concrete ty_size_eq.
    iApply (wp_memcpy_guarded _ lw lh vlw vlc HW (fractional.half γ2) _ (S M)
      with "TIME [Ptw H2 HW £m]"); [solve_ndisj|lia|lia| |].
    { iFrame "Ptw H2 HW ⧖S' £m". iSplit.
      - iApply (lguards_weaken_later with "Hwpt"). lia.
      - iApply (lguards_weaken_later _ _ _ (gh + 1)); [lia|].
        iApply (guards_transitive_right with "Hsl").
        rewrite -heap_mapsto_cells_fancy_fmap_eq /vlc fmap_to_concrete //. }
    iIntros "!> (Ptw & HW & H2)".
    iMod ("Totyw" $! zh M with "[Ptw] ⧖S' £t HW") as (zw) "(H1 & %Hzw & Tw)".
    { iNext. iExists (ty_phys ty zh tid).
      rewrite -heap_complete_mapsto_fancy_fmap_eq /vlc fmap_to_concrete //. iFrame "Ptw".
      iSplit; [|done].
      iDestruct (ty_gho_own_depth_mono _ dh gh M (S M) with "Gho") as "[$ _]"; lia. }
    iMod (fupd_mask_mono with "(Halfback2 H2 H3)") as "H2"; [solve_ndisj|].
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iModIntro. iExists -[zw; ((l, x₀), ζm)]. iFrame "L I".
    iSplitR "Obs Obs'".
    { iSplitL "Tw"; [|iSplitL; [|done]].
      - iExists #lw.1, (dw `max` S M). iSplit; [by rewrite Hpw|].
        iSplit; [iApply (persistent_time_receipt_mono with "⧖S'"); lia|].
        iDestruct "Tw" as "[Gw' Physw]". iFrame "Physw".
        iDestruct (ty_gho_own_depth_mono with "Gw'") as "[$ _]"; lia.
      - rewrite /tctx_elt_interp. iExists #l. iSplit; [done|].
        iExists D, d, g. iFrame "⧖ ⧗p Fr". iSplit; [done|]. iSplit; [done|].
        rewrite /ltype_own lty_pat_plug lty_rfn_plug ltype_own_plug -/y Hy. iFrame "Rest".
        iEval (rewrite -cell_mapsto_val -HlK') in "Pt".
        rewrite /= /res_node /=. iFrame "Pt". iApply bi.laterN_intro. iFrame "Incl".
        iExists d', g'. iSplit; [done|]. rewrite lty_pat_plug lty_rfn_plug.
        rewrite (view_rleaf_rfn _ _ _ _ _ _ Hl).
        iApply ("Cl" $! lt0 (lty_pat lt0) (inl (PlaceIn zh)) dh gh d' g'
          with "[%] [//] [//] [%] Vh"); [by rewrite (view_rleaf_size _ _ _ Hl)|lia]. }
    iCombine "Obs Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=> π [Hπ HΦ].
    apply HΦ in Hπ. by apply Hπ.
  Qed.
End memcpy_res.
