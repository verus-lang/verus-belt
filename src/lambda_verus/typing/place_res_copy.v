(** * Byte copies below resolved unique borrows

  The byte version of the deleted legacy [place_res_copy.v]. A [Copy] leaf (unblocked or
  shared-blocked, [view_rleaf]) in the view of a resolved unique borrow ([ResUniqLty],
  [typing/place_res_ops.v]) is copied into a box ([own_bytes]) with a byte-level
  [MemCopy] whose source is guarded ([wp_memcopy_guarded_gen]), as
  [type_memcpy_copy_from_vplace_pshr_instr] below a shared reference
  ([typing/place_pshr.v]). The leaf is shared at the lifetime of the view at the hole,
  which must be alive; the place does not change; the old contents of the box are
  resolved. The first step (the address of the box) gives the credits for the address of
  the source, the copy itself those for the box and the copy.

  Resolved leaves [OfRes ty] are copied after their conversion to [OfTy ty] ([ResOwn],
  [tctx_oplace_res_to_ofty]) or to a shared reference ([OfRes (&uniqb{κ} ty)],
  [type_oplace_res_uniq_to_shr_instr]), with the rules of [typing/place_deep.v] and
  [typing/place_pshr.v]. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From lrust.lang Require Import proofmode memcpy.
From lrust.typing Require Export type ltype lpath pctx_acc vplace place_own shr_bytes.
From lrust.typing Require Import type_context programs programs_util lft_contexts
  uniq_util uniq_bor uniq_bytes_util uniq_bytes own_bytes bytes_layout value_ctx product own
  freeable_util sum type_sum place_shr place_resolve place_puniq place_sum place_pshr
  place_res place_res_view place_res_rslv place_res_ops.
From lrust.util Require Import proph_bor.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section memcpy_res.
  Context `{!typeG Σ}.

  Lemma type_memcpy_copy_from_oplace_res_instr {ℭ 𝔅 𝔄 𝔅'} E L I pw p n n'
      (K: pctx (uniq_borₛ 𝔅) 𝔄) `{!PctxNoUniq K} κ (K2: pctx ℭ 𝔅) `{!PctxNoShr K2}
      (lt0: lty ℭ) (ty: type ℭ) κs (tyw: type 𝔅') Φ (sz: nat) :
    view_rleaf lt0 ty κs → Copy ty → resolve E L tyw Φ → sz = ty_bsize ty →
    ty_bsize tyw = sz → lctx_lft_alive E L (pctx_salv K2 κ ⊓ κs) →
    typed_instr E L I
      +[pw ◁ᵥ own_bytes n' tyw; p ◁ₗown{n} pctx_plug K (ResUniqLty (pctx_plug K2 lt0) κ)]
      (MemCopy Na1Ord sz (ToLit pw)
        (pctx_expr K2 (ToLit (Load Na1Ord MPtr (pctx_expr K (ToLit p))))))
      (λ _, +[pw ◁ᵥ own_bytes n' ty; p ◁ₗown{n} pctx_plug K (ResUniqLty (pctx_plug K2 lt0) κ)])
      (λ post '-[b; x], λ mask π, Φ b.2 π →
        post -[(b.1, pctx_get K2 (uniq_bor_current (pctx_get K x.1.2))); x] mask π).
  Proof.
    iIntros (Hl Hcopy Rslv -> Hszw Alv tid post mask iκs [[lw zw0] [x []]])
      "#LFT #TIME #PROPH #UNIQ #E L I (Tw & Tp & _) Obs".
    destruct x as [[l x₀] ζm].
    rewrite /tctx_elt_interp.
    iDestruct "Tp" as (v Hp D d g) "(#⧖ & ⧗p & -> & %Hle & Fr & Own)".
    have ?: Closed [] (pctx_expr K (ToLit p)).
    { apply pctx_expr_closed. have ?: Closed [] p by eapply eval_path_closed. apply _. }
    iDestruct "Tw" as (vw Hpw ww dw [-> Hww]) "(#⧖w & Tw)". simpl in Hww. simplify_eq.
    destruct dw as [|dw]; [done|]. iDestruct "Tw" as "(Bs & Frw & Gw0)".
    iDestruct "Bs" as (bsw) "[Hbsw %Hbsw]".
    iDestruct (Alv with "L E") as "#Alv".
    iCombine "⧖ ⧖w" as "⧖m".
    set M := D `max` (S dw).
    have HM: D ≤ M ∧ S dw ≤ M by rewrite /M; lia.
    (* The first step (the address of the box): credits for the address of the source. *)
    wp_bind (ToLit pw).
    iApply (wp_persistent_time_receipt with "TIME ⧖m"); [solve_ndisj|].
    iIntros "£ #⧖S". wp_bind pw. iApply wp_wand; [by iApply wp_eval_path|].
    iIntros (?) "->". wp_pure _.
    (* The copy: credits for the box and the copy. *)
    iApply (wp_persistent_time_receipt with "TIME ⧖S"); [solve_ndisj|].
    iIntros "£' #⧖SS". iApply wp_fupd.
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_salv K2 κ ⊓ κs])%I as "#Hss".
    { iApply (guards_transitive with "Ghalf Alv"). }
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_salv K2 κ])%I as "#Hs".
    { iApply (guards_transitive with "Hss"). iApply llftl_intersect_incl_l. }
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_slft K2 κ ⊓ κs])%I as "#Hsl".
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
    destruct y as [[[[[ly z] ξi] d0] g0] idx0] eqn:Hy.
    rewrite /= /res_node /=. iDestruct "H" as "[Pt N]".
    have Hm: pctx_mode K 1 ≤ D by (rewrite pctx_mode_add; lia).
    iDestruct (lc_weaken (pctx_mode K 1 + (advance_credits M - pctx_mode K 1)) with "£")
      as "[£m £]"; [rewrite /advance_credits; nia|].
    iMod (lc_fupd_elim_laterN with "£m N") as "(#Incl & %d' & %g' & %Hle' & V)".
    rewrite lty_pat_plug lty_rfn_plug (view_rleaf_rfn _ _ _ _ _ _ Hl).
    iDestruct (view_pctx_acc K2 κ lt0 0 (lty_pat lt0)
      (inl (PlaceIn (pctx_get K2 z))) z ζm (false :: q0) d' g' tid ly (fractional.half γh)
      with "Hs V") as (dh gh) "([%Hdh [%Hgh %Hin]] & Vh & #Gs & Cl)".
    iDestruct (view_rleaf_shared with "Vh") as "[Vh #Vs]"; [done|].
    set zh := pctx_get K2 z.
    set lh := pctx_loc K2 (lty_size lt0) z ly.
    have Hdl: pctx_dlev K2 ≤ D.
    { destruct Hle' as [Hle' _]. rewrite pctx_depth_sub in Hle'. lia. }
    have Hg': g' ≤ D by lia. have Hgh': gh ≤ D by lia.
    have ?: pctx_depth K d ≤ d by (rewrite pctx_depth_sub; lia).
    iDestruct (lc_weaken (2 * (g' + 1) * pctx_dlev K2 + ((gh + 1) + (gh + 1))) with "£")
      as "[£w £c]".
    { rewrite /advance_credits. clear - Hdl Hg' Hgh' Hm HM. nia. }
    iDestruct (lc_weaken (1 + ((1 + M * (M + 1)) + (1 + 2 * (gh + 1)))) with "£'")
      as "(£r & £s & £b & £l)"; [rewrite /advance_credits; nia|].
    (* The address of the hole. *)
    wp_bind (pctx_expr K2 _).
    iApply (wp_pctx_sexpr _ K2 (lty_size lt0) (g' + 1) (fractional.half γh) z ly);
      [solve_ndisj|].
    wp_bind (pctx_expr K (ToLit p)).
    iMod lc_zero as "£0".
    iApply (wp_wand with "[Rest £0]").
    { iApply (wp_pctx_expr_mask _ K (lty_size lt1) 1 x₀ ζm [] d g tid lr (ToLit p) True True 0
        with "[] £0 [] Rest"); [solve_ndisj|..].
      - rewrite /lr -heap_cloc_mapsto_empty. iApply guards_true.
      - wp_bind p. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->".
        by wp_pure _. }
    iIntros (w) "(-> & _ & _ & Rest)".
    iDestruct "Pt" as (bs) "[Hbs %Hbs]".
    wp_bind (Load _ _ _). iApply (wp_load_na with "Hbs"); [exact Hbs|]. iIntros "!> Hbs".
    wp_pure _. iFrame "Gs £w H1". iSplit; [done|]. iIntros "H1".
    (* The (persistent) ownership of the value. *)
    iMod (shr_view_copy with "Hsl H1 £c Vs") as (u Hu) "[#Gho H1]"; [solve_ndisj|].
    (* Resolve the old contents of the box. *)
    iMod (lc_fupd_elim_later with "£b Gw0") as "Gw0".
    iDestruct (Rslv _ (⊤ ∖ (⊤ ∖ ↑Nllft ∖ ↑prophN ∖ ↑timeN ∖ ↑uniqN))
      with "LFT PROPH UNIQ TIME E Ghalf H2 Gw0") as "ToObs"; [set_solver|].
    iMod (lc_fupd_elim_later with "£r ToObs") as "ToObs".
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iDestruct (lc_step_fupdN_elim_later with "[£s] ToObs") as "ToObs".
    { iApply (lc_weaken with "£s"). nia. }
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iMod (fupd_mask_mono with "ToObs") as "[Obs' H2]"; [solve_ndisj|].
    (* Copy the bytes. *)
    iDestruct "Vs" as "(Gpt & _ & _)".
    iApply (wp_memcopy_guarded_gen _ lw lh.1 bsw (ty_bsize ty) (fractional.half γh)
      (cbytes ty zh lh) (ty_bytes ty zh) (gh + 1) with "[$Hbsw $H1 $£l]");
      [solve_ndisj|by rewrite (ty_bytes_length _ _ _ Hbsw) Hszw|intros ?; apply ty_bytes_length|..].
    { iSplit; [iApply (guards_transitive_right with "Hsl Gpt")|].
      iIntros "!> (%bs' & Hbs' & %Hbs')". iExists bs'. iFrame "Hbs'".
      iSplit; [done|]. iIntros "Hbs'". iExists bs'. by iFrame. }
    iIntros "!>" (bs2) "(%Hbs2 & Hbsw & H1)".
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iModIntro. iExists -[(lw, zh); ((l, x₀), ζm)]. iFrame "L I".
    iSplitR "Obs Obs'".
    { iSplitL "Hbsw Frw"; [|iSplitL; [|done]].
      - iExists _. iSplit; [done|]. iExists (VPtr lw), (S (S M)). iSplit; [done|].
        iSplit; [done|].
        iSplitL "Hbsw"; [iExists bs2; by iFrame|]. iSplitL "Frw".
        + by rewrite -Hszw.
        + iNext. iDestruct (ty_gho_own_depth_mono _ dh gh (S M) (S (S M)) with "Gho") as "[$ _]";
            lia.
      - iExists (MLitV (VPtr l)). iSplit; [done|]. iExists D, d, g.
        iFrame "⧖ ⧗p Fr". iSplit; [done|]. iSplit; [done|].
        rewrite /ltype_own lty_pat_plug lty_rfn_plug ltype_own_plug -/y Hy. iFrame "Rest".
        rewrite /= /res_node /=. iSplitL "Hbs"; [iExists bs; by iFrame|].
        iApply bi.laterN_intro. iFrame "Incl".
        iExists d', g'. iSplit; [done|]. rewrite lty_pat_plug lty_rfn_plug.
        rewrite (view_rleaf_rfn _ _ _ _ _ _ Hl).
        iApply ("Cl" $! lt0 (lty_pat lt0) (inl (PlaceIn zh)) dh gh d' g'
          with "[//] [//] [//] [%] Vh"). lia. }
    iCombine "Obs Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=> π [Hπ HΦ].
    by apply Hπ.
  Qed.
End memcpy_res.
