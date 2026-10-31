(** * Operations on resolved places, on bytes

  The byte version of the deleted legacy [place_res_ops.v]. Resolved places ([OfRes], [ResUniqLty],
  see [typing/place_res.v]) are read and shared, not written:
  - the access to a sub-place of a view ([view_pctx_acc]);
  - reading a [Copy] leaf (of any size, a guarded typed [Load]) below a resolved unique
    borrow ([type_read_oplace_res_instr], [type_read_oplace_res_shrblk_instr]), and a
    shared borrow of a leaf below it ([type_share_oplace_res_instr]);
  - folding a resolved unique borrow whose referent is a leaf to a shared reference
    ([tctx_fold_oplace_res_uniq_leaf]); compound referents are not folded on bytes (see
    the end of the file);
  - unblocking a blocked leaf ([unblock_tctx_oplace_res]) or a shared-blocked leaf
    ([unblock_tctx_oplace_res_shr]) of a view;
  - dropping a resolved place ([type_drop_oplace_res_instr]). *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From lrust.lang Require Import proofmode.
From lrust.lang.lib Require Import new_delete.
From lrust.util Require Import update.
From lrust.typing Require Export type ltype lpath pctx_acc vplace place_own shr_bytes.
From lrust.typing Require Import type_context programs programs_util lft_contexts uniq_util
  uniq_bytes_util uniq_bytes own_bytes bytes_layout value_ctx product freeable_util sum
  place_shr place_resolve place_puniq place_sum place_pshr place_res place_res_view
  place_res_rslv.
From lrust.util Require Import proph_bor.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

(** * The access to a sub-place of a view *)

Section view_acc.
  Context `{!typeG Σ}.

  Lemma lty_leafb_plug_eq {𝔅 𝔄} (K: pctx 𝔅 𝔄) (lt lt': lty 𝔅) :
    lty_leafb lt' = lty_leafb lt → lty_leafb (pctx_plug K lt') = lty_leafb (pctx_plug K lt).
  Proof. by destruct K. Qed.

  Lemma pctx_sguards_mono {𝔅 𝔄} (K: pctx 𝔅 𝔄) n k k' G x l :
    k ≤ k' → pctx_sguards K n k G x l ⊢ pctx_sguards K n k' G x l.
  Proof.
    intros ?. induction K in x, l |- *; simpl; [done|auto|auto| |auto| |];
      iIntros "[#G R]"; (iSplit; [iApply (lguards_weaken_later with "G"); lia|]);
      by iApply IHK.
  Qed.

  (** The view of a place [K[lt]] (with [K] below no shared reference) gives the view of
      its hole at the lifetime [pctx_slft K κ], the guards of the pointer cells on the
      path, and a closer for a new hole of the same folded type and size. *)
  Lemma view_pctx_acc {𝔅 𝔄} (K: pctx 𝔅 𝔄) `{!PctxNoShr K} κ (lt: lty 𝔅) m p r x ζm q
      d g tid l (R: iProp Σ) :
    (R &&{↑NllftG}&&> @[pctx_salv K κ]) -∗
    lty_view (pctx_plug K lt) κ m (pctx_pat K p) (pctx_rfn K x ζm q r) d g tid l -∗
    ∃ dh gh, ⌜dh + pctx_dlev K ≤ d ∧ gh ≤ g ∧ pctx_in K x⌝ ∗
      lty_view lt (pctx_slft K κ) (pctx_hmode K m) p r dh gh tid
        (pctx_loc K (lty_size lt) x l) ∗
      pctx_sguards K (lty_size lt) (g + 1) R x l ∗
      (∀ (lt': lty 𝔅) p' r' dh' gh' dn gn,
         ⌜lty_size lt' = lty_size lt⌝ -∗ ⌜lty_fold lt' = lty_fold lt⌝ -∗
         ⌜lty_leafb lt' = lty_leafb lt⌝ -∗
         ⌜d ≤ dn ∧ g ≤ gn ∧ dh' + pctx_dlev K ≤ dn ∧ gh' ≤ gn⌝ -∗
         lty_view lt' (pctx_slft K κ) (pctx_hmode K m) p' r' dh' gh' tid
           (pctx_loc K (lty_size lt) x l) -∗
         lty_view (pctx_plug K lt') κ m (pctx_pat K p') (pctx_rfn K x ζm q r') dn gn tid l).
  Proof.
    rename select (PctxNoShr K) into HK. rewrite /PctxNoShr in HK.
    induction K as [|𝔅 𝔄1 𝔄2 K IH lt2|𝔅 𝔄1 𝔄2 lt1 K IH|𝔅 𝔄' n' K IH|𝔅 𝔄l tyl i w K IH|
      𝔅 𝔄' κ' K IH|𝔅 𝔄' κ' K IH] in HK, κ, lt, m, p, r, x, q, d, g, l |- *;
      simpl; simpl in HK; try done; iIntros "#GR V".
    - iExists d, g. iSplit; [iPureIntro; lia|]. iFrame "V". iSplit; [done|].
      iIntros (lt' p' r' dh' gh' dn gn ??? (?&?&?&?)) "V'".
      iApply (lty_view_depth_mono with "V'"); lia.
    - rewrite /prod_node lty_size_plug. iDestruct "V" as "[V1 V2]".
      iDestruct (IH with "GR V1") as (dh gh) "(% & Vh & Gs & Cl)"; [done|].
      iExists dh, gh. iFrame "Vh". iSplit; [done|]. iFrame "Gs".
      iIntros (lt' p' r' dh' gh' dn gn Hsz Hf Hb Hle) "V'". rewrite /prod_node lty_size_plug Hsz.
      iSplitL "Cl V'"; [iApply ("Cl" with "[//] [//] [//] [//] V'")|].
      iApply (lty_view_depth_mono with "V2"); lia.
    - rewrite /prod_node. iDestruct "V" as "[V1 V2]".
      iDestruct (IH with "GR V2") as (dh gh) "(% & Vh & Gs & Cl)"; [done|].
      iExists dh, gh. iFrame "Vh Gs". iSplit; [done|].
      iIntros (lt' p' r' dh' gh' dn gn Hsz Hf Hb Hle) "V'". rewrite /prod_node.
      iSplitL "V1"; [iApply (lty_view_depth_mono with "V1"); lia|].
      iApply ("Cl" with "[//] [//] [//] [//] V'").
    - rewrite /view_own lty_size_plug. iDestruct "V" as "(#Gp & %Hd & V)".
      iDestruct (IH with "GR V") as (dh gh) "(% & Vh & Gs & Cl)"; [done|].
      iExists dh, gh. iFrame "Vh". iSplit; [iPureIntro; destruct_and!; split_and!; try lia; done|].
      iFrame "Gs". iSplit.
      { iApply (guards_transitive_right with "[] Gp").
        iApply (guards_transitive with "GR"). iApply pctx_salv_incl. }
      iIntros (lt' p' r' dh' gh' dn gn Hsz Hf Hb Hle) "V'". rewrite /view_own lty_size_plug Hsz.
      iSplit; [iApply (lguards_weaken_later with "Gp"); lia|]. iSplit; [iPureIntro; lia|].
      iApply ("Cl" with "[//] [//] [//] [%] V'"). lia.
    - rewrite /psum_proj_or. destruct (psum_proj i x.1) as [y|] eqn:Hy; last first.
      { by rewrite /prfn_dummy /view_sum. }
      rewrite /view_sum /prfn_sum psum_proj_pinj lty_size_plug.
      iDestruct "V" as "(#Gt & V & #Gq)".
      iDestruct (IH with "GR V") as (dh gh) "(% & Vh & Gs & Cl)"; [done|].
      iExists dh, gh. iFrame "Vh". iSplit; [done|]. iFrame "Gs".
      iIntros (lt' p' r' dh' gh' dn gn Hsz Hf Hb Hle) "V'".
      rewrite /view_sum /prfn_sum psum_proj_pinj lty_size_plug Hsz.
      iSplit; [iApply (lguards_weaken_later with "Gt"); lia|].
      iSplitL; [iApply ("Cl" with "[//] [//] [//] [%] V'"); lia|].
      iApply (lguards_weaken_later with "Gq"); lia.
    - destruct HK as [_ HK]. rewrite /view_uniq.
      iDestruct "V" as "(#Gp & #Incl & %d' & %g' & %Hle & V & I)".
      iDestruct (IH with "GR V") as (dh gh) "(% & Vh & Gs & Cl)"; [done|].
      iExists dh, gh. iFrame "Vh". iSplit; [iPureIntro; destruct_and!; split_and!; try lia; done|].
      iSplit.
      { iSplit.
        - iApply (guards_transitive_right with "[] Gp").
          iApply (guards_transitive with "GR"). iApply llftl_incl_trans; [iApply pctx_salv_incl|].
          iApply llftl_intersect_incl_l.
        - iApply (pctx_sguards_mono with "Gs"). lia. }
      iIntros (lt' p' r' dh' gh' dn gn Hsz Hf Hb Hle') "V'".
      have Hf': lty_fold (pctx_plug K lt') = lty_fold (pctx_plug K lt) by apply lty_fold_plug_eq'.
      rewrite /view_uniq Hf' (lty_leafb_plug_eq K lt lt' Hb).
      iSplit; [iApply (lguards_weaken_later with "Gp"); lia|].
      iFrame "Incl". iExists (pred dn), gn. iSplit; [iPureIntro; lia|].
      iSplitR "I"; [iApply ("Cl" with "[//] [//] [//] [%] V'"); lia|].
      destruct (lty_leafb (pctx_plug K lt)); [|done].
      iDestruct "I" as (x0 idx) "[T P]". iExists x0, idx. iSplitL "T".
      { iApply (lguards_weaken_later with "T"). lia. }
      by iEval (rewrite (uniq_pers_component_retarget _ x0 x0 _ _ _ (pred dn) gn)) in "P".
  Qed.
End view_acc.

(** * Reading below a resolved unique borrow *)

Section read.
  Context `{!typeG Σ}.

  (** The leaves read in a view: unblocked leaves (shared at the lifetime of the view)
      and shared-blocked leaves (shared at its intersection with their lifetime). *)
  Inductive view_rleaf {ℭ} : lty ℭ → type ℭ → lft → Prop :=
  | view_rleaf_ofty ty : view_rleaf (OfTy ty) ty static
  | view_rleaf_shrblk ty β : view_rleaf (ShrBlocked ty β) ty β.

  Lemma view_rleaf_rfn {ℭ} (lt0: lty ℭ) ty κs x ζm q :
    view_rleaf lt0 ty κs → lty_rfn lt0 x ζm q = inl (PlaceIn x).
  Proof. by destruct 1. Qed.

  Lemma view_rleaf_size {ℭ} (lt0: lty ℭ) ty κs :
    view_rleaf lt0 ty κs → lty_size lt0 = ty_bsize ty.
  Proof. intros _. apply lty_size_ty. Qed.

  Lemma view_rleaf_shared {ℭ} (lt0: lty ℭ) ty κs κ m x d g tid l :
    view_rleaf lt0 ty κs →
    lty_view lt0 κ m (lty_pat lt0) (inl (PlaceIn x)) d g tid l ⊢
    lty_view lt0 κ m (lty_pat lt0) (inl (PlaceIn x)) d g tid l ∗
    □ shr_view (κ ⊓ κs) ty x d g tid l.
  Proof.
    destruct 1; simpl; rewrite /view_leaf.
    - iIntros "#V". iFrame "V".
      iDestruct "V" as (x' ->) "(G & Shr & Pers)". iModIntro. iSplit; [|iSplit; [|done]].
      + iApply (guards_transitive_right with "[] G"). iApply llftl_intersect_incl_l.
      + iDestruct (ty_shr_lft_mono _ κ (κ ⊓ static) _ 0 with "[] Shr") as "Shr'";
          [iApply llftl_intersect_incl_l|].
        iApply (ty_shr_depth_mono with "Shr'"); lia.
    - iIntros "(%x' & -> & #G & #Shr & #Pers & Rest)". iSplitL.
      { iExists x. by iFrame "G Shr Pers Rest". }
      iModIntro. by iFrame "G Shr Pers".
  Qed.

  (** Copying a value of a [Copy] type (of any size) out of the hole of [K2], in the view of
      the resolved unique borrow at the hole of [K] (in the owned part of the place,
      [PctxNoUniq K]), with a guarded typed [Load]; the leaf [lt0] is unblocked or
      shared-blocked ([view_rleaf]), it is shared at [pctx_slft K2 κ ⊓ κs] (which must be
      alive); the place does not change. The first step gives the credits. *)
  Lemma type_read_oplace_res_leaf_instr {ℭ 𝔅 𝔄} E L I p n (K: pctx (uniq_borₛ 𝔅) 𝔄)
      `{!PctxNoUniq K} κ (K2: pctx ℭ 𝔅) `{!PctxNoShr K2} (lt0: lty ℭ) `{!NoCell ℭ} (ty: type ℭ) κs :
    view_rleaf lt0 ty κs → Copy ty → lctx_lft_alive E L (pctx_salv K2 κ ⊓ κs) →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K (ResUniqLty (pctx_plug K2 lt0) κ)]
      (Load Na1Ord ty.(ty_mty)
        (pctx_expr K2 (ToLit (Load Na1Ord MPtr (pctx_expr K (ToLit p))))))
      (λ v, +[v ◁ᵥ ty; p ◁ₗown{n} pctx_plug K (ResUniqLty (pctx_plug K2 lt0) κ)])
      (λ post '-[x], post -[pctx_get K2 (uniq_bor_current (pctx_get K x.1.2)); x]).
  Proof.
    iIntros (Hl Hcopy Alv tid post mask iκs [x []])
      "#LFT #TIME #PROPH #UNIQ #E L I (Tp & _) Obs".
    destruct x as [[l x₀] ζm].
    rewrite /tctx_elt_interp.
    iDestruct "Tp" as (v Hp D d g) "(#⧖ & ⧗p & -> & %Hle & Fr & Own)".
    have ?: Closed [] (pctx_expr K (ToLit p)).
    { apply pctx_expr_closed. have ?: Closed [] p by eapply eval_path_closed. apply _. }
    iDestruct (Alv with "L E") as "#Alv".
    (* The first step gives the credits. *)
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj|].
    iIntros "£ #⧖S". iApply wp_fupd.
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
    iDestruct (lc_weaken (pctx_mode K 1 + (advance_credits D - pctx_mode K 1)) with "£")
      as "[£m £]"; [rewrite /advance_credits pctx_mode_add; lia|].
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
    have Hm: pctx_mode K 1 ≤ D by (rewrite pctx_mode_add; lia).
    iDestruct (lc_weaken (2 * (g' + 1) * pctx_dlev K2 + 4 * (gh + 1)) with "£")
      as "[£w £r]".
    { rewrite /advance_credits. clear - Hdl Hg' Hgh' Hm. nia. }
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
    (* The pointer of the resolved borrow. *)
    iDestruct "Pt" as (bs) "[Hbs %Hbs]".
    wp_bind (Load _ _ _). iApply (wp_load_na with "Hbs"); [exact Hbs|]. iIntros "!> Hbs".
    wp_pure _. iFrame "Gs £w H1". iSplit; [done|]. iIntros "H1".
    (* The guarded typed load of the leaf. *)
    iApply (wp_load_shr_view with "Hsl H1 £r Vs"); [solve_ndisj|].
    iIntros (u Hu) "#Gho H1".
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iModIntro. iExists -[zh; ((l, x₀), ζm)]. iFrame "L I".
    iSplitL "Hbs Rest Cl Vh ⧗p Fr"; last first.
    { iExact "Obs". }
    iSplitR "Hbs Rest Cl Vh ⧗p Fr".
    { iExists _. iSplit; [by rewrite eval_path_of_val|]. iExists u, D. iSplit; [done|].
      iFrame "⧖". iDestruct (ty_gho_own_depth_mono _ dh gh D D with "Gho") as "[$ _]"; lia. }
    iSplit; [|done]. iExists (MLitV (VPtr l)). iSplit; [done|]. iExists D, d, g.
    iFrame "⧖ ⧗p Fr". iSplit; [done|]. iSplit; [done|].
    rewrite /ltype_own lty_pat_plug lty_rfn_plug ltype_own_plug -/y Hy. iFrame "Rest".
    rewrite /= /res_node /=. iSplitL "Hbs"; [iExists bs; by iFrame|].
    iApply bi.laterN_intro. iFrame "Incl".
    iExists d', g'. iSplit; [done|]. rewrite lty_pat_plug lty_rfn_plug.
    rewrite (view_rleaf_rfn _ _ _ _ _ _ Hl).
    iApply ("Cl" $! lt0 (lty_pat lt0) (inl (PlaceIn zh)) dh gh d' g' with "[//] [//] [//] [%] Vh").
    lia.
  Qed.

  Lemma type_read_oplace_res_instr {ℭ 𝔅 𝔄} E L I p n (K: pctx (uniq_borₛ 𝔅) 𝔄)
      `{!PctxNoUniq K} κ (K2: pctx ℭ 𝔅) `{!PctxNoShr K2} `{!NoCell ℭ} (ty: type ℭ) :
    Copy ty → lctx_lft_alive E L (pctx_salv K2 κ) →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K (ResUniqLty (pctx_plug K2 (OfTy ty)) κ)]
      (Load Na1Ord ty.(ty_mty)
        (pctx_expr K2 (ToLit (Load Na1Ord MPtr (pctx_expr K (ToLit p))))))
      (λ v, +[v ◁ᵥ ty; p ◁ₗown{n} pctx_plug K (ResUniqLty (pctx_plug K2 (OfTy ty)) κ)])
      (λ post '-[x], post -[pctx_get K2 (uniq_bor_current (pctx_get K x.1.2)); x]).
  Proof.
    intros ??. apply (type_read_oplace_res_leaf_instr _ _ _ _ _ K κ K2 _ _ static);
      [constructor|done|].
    apply lctx_lft_alive_intersect; [done|apply lctx_lft_alive_static].
  Qed.

  (** Reading a shared-blocked leaf (at [β]) of a view, while [β] is alive. *)
  Lemma type_read_oplace_res_shrblk_instr {ℭ 𝔅 𝔄} E L I p n (K: pctx (uniq_borₛ 𝔅) 𝔄)
      `{!PctxNoUniq K} κ (K2: pctx ℭ 𝔅) `{!PctxNoShr K2} `{!NoCell ℭ} (ty: type ℭ) β :
    Copy ty → lctx_lft_alive E L (pctx_salv K2 κ ⊓ β) →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K (ResUniqLty (pctx_plug K2 (ShrBlocked ty β)) κ)]
      (Load Na1Ord ty.(ty_mty)
        (pctx_expr K2 (ToLit (Load Na1Ord MPtr (pctx_expr K (ToLit p))))))
      (λ v, +[v ◁ᵥ ty; p ◁ₗown{n} pctx_plug K (ResUniqLty (pctx_plug K2 (ShrBlocked ty β)) κ)])
      (λ post '-[x], post -[pctx_get K2 (uniq_bor_current (pctx_get K x.1.2)); x]).
  Proof.
    intros ??. by apply (type_read_oplace_res_leaf_instr _ _ _ _ _ K κ K2 _ _ β);
      [constructor|..].
  Qed.
End read.

(** * Unblocking a leaf of a view *)

Section unblock.
  Context `{!typeG Σ}.

  Lemma pctx_nmm_nouniq {𝔅 𝔄} (K: pctx 𝔅 𝔄) `{!PctxNoUniq K} e mm :
    pctx_nmm K e mm = mm + pctx_mode K 0.
  Proof.
    rename select (PctxNoUniq K) into HK. rewrite /PctxNoUniq in HK.
    induction K in HK, e, mm |- *; simpl; simpl in HK; try done; rewrite ?IHK //;
      rewrite ?(pctx_mode_add K 1); lia.
  Qed.

  (** Once [α] has ended, the blocked leaf at the hole of [K2] in the view of the resolved
      unique borrow at the hole of [K] (it was reborrowed below the borrow, at
      [pctx_blft (PUniq κ K2) α]) is unblocked: its inheritance is fired (inside its
      borrow at the lifetime of the view), and it is shared at that lifetime. The value of
      the leaf is the final value of its reborrow. *)
  Lemma unblock_tctx_oplace_res {ℭ 𝔅 𝔄 𝔄l 𝔄l'} p n α (K: pctx (uniq_borₛ 𝔅) 𝔄)
      `{!PctxNoUniq K} κ (K2: pctx ℭ 𝔅) `{!PctxNoShr K2} (ty: type ℭ)
      (T: tctx 𝔄l) (T': tctx 𝔄l') E L f :
    lctx_lft_alive E L (pctx_salv K2 κ ⊓ ty_lft ty) →
    lctx_lft_incl E L (pctx_slft K2 κ) (ty_lft ty) →
    unblock_tctx E L α T T' f →
    unblock_tctx E L α
      (p ◁ₗown{n} pctx_plug K (ResUniqLty (pctx_plug K2 (Blocked ty (pctx_blft (PUniq κ K2) α))) κ)
        +:: T)
      (p ◁ₗown{n} pctx_plug K (ResUniqLty (pctx_plug K2 (OfTy ty)) κ) +:: T')
      (λ π '(x -:: xl), λ '(x' -:: xl'),
        let y := pctx_get K x.1.2 in let y' := pctx_get K x'.1.2 in
        x'.1.1 = x.1.1 ∧ x'.2 = x.2 ∧
        x'.1.2 = pctx_set K x.1.2 (uniq_bor_set_current y
          (pctx_set K2 (uniq_bor_current y) (pctx_get K2 (uniq_bor_current y')))) ∧
        vπ (pctx_get K2 (uniq_bor_current y')) π =
          (π (uniq_prvar (pctx_get K2 (uniq_bor_current y))
            (blk_lookup x.2 (pctx_path K2 (false :: pctx_path K []))))).1 ∧
        f π xl xl').
  Proof.
    iIntros (Alv Incl Un G tid [x xl] ?)
      "#LFT #TIME #PROPH #UNIQ #E #L G #†α /=[(%v & %Hp & Own) T]".
    destruct x as [[l x₀] ζm].
    set β := pctx_blft (PUniq κ K2) α.
    iDestruct "Own" as (D d g) "(#⧖0 & ⧗ & -> & %Hle & Fr & Own)".
    (* The receipts of the leaf. *)
    set e0 := pctx_mode K 0 + 1.
    set e' := pctx_ne K2 e0 0.
    have Hnrc: ∀ X: lty ℭ, lty_nrc (pctx_plug K (ResUniqLty (pctx_plug K2 X) κ)) 0 0 =
      pctx_nrc K 0 0 + pctx_nrc K2 e0 0 + lty_nrc X e' (pctx_nmm K2 e0 0).
    { intros X. rewrite lty_nrc_plug /= lty_nrc_plug pctx_ne_nouniq pctx_nmm_nouniq.
      rewrite (_: 0 + (0 + pctx_mode K 0) + 1 = e0); [|rewrite /e0; lia].
      rewrite /e'. lia. }
    rewrite Hnrc /=.
    iDestruct (cumulative_time_receipt_sep with "⧗") as "[⧗r ⧗]".
    have He'1: 1 ≤ e'. { unfold e', e0. have := pctx_ne_ge K2 (pctx_mode K 0 + 1) 0. lia. }
    iDestruct (cumulative_time_receipt_mono (1 + (1 + (e' - 1))) with "⧗") as "⧗"; [lia|].
    iDestruct (cumulative_time_receipt_sep with "⧗") as "[⧗a ⧗]".
    iDestruct (cumulative_time_receipt_sep with "⧗") as "[⧗b ⧗e]".
    have Hhn := pctx_hmode_ne K2 0 e0 0. set m2 := pctx_hmode K2 0.
    leaf_open "L" with "G" as "[L1 back]"; [set_solver|].
    iDestruct (Alv with "L1 E") as "#Lα". iDestruct (Incl with "L1 E") as "#Lincl".
    iMod ("back" with "L1") as "G".
    (* Half of [G] for the rest of the context, the other half for the place. *)
    iMod (fractional.frac_split_guard_in_half with "G L") as (γ1) "[GT [GP [#GhT #BackT]]]";
      [solve_ndisj|].
    iMod (Un with "LFT TIME PROPH UNIQ E GhT GT †α T") as (dT xl') "[#⧖T ToT']".
    iAssert (fractional.half γ1 &&{↑NllftG}&&> @[pctx_salv K2 κ])%I as "#Hs".
    { iApply (guards_transitive with "GhT"). iApply (guards_transitive with "Lα").
      iApply llftl_intersect_incl_l. }
    iAssert (fractional.half γ1 &&{↑NllftG}&&> @[pctx_slft K2 κ])%I as "#Hsl".
    { iApply (guards_transitive with "Hs"). iApply pctx_salv_slft. }
    iAssert (fractional.half γ1 &&{↑NllftG}&&> @[ty_lft ty])%I as "#Hty".
    { iApply (guards_transitive with "GhT"). iApply (guards_transitive with "Lα").
      iApply llftl_intersect_incl_r. }
    (* The hole of [K]: the resolved unique borrow. *)
    set lt1 := ResUniqLty (pctx_plug K2 (Blocked ty β)) κ.
    rewrite /ltype_own lty_pat_plug lty_rfn_plug ltype_own_plug.
    iDestruct "Own" as "[H Rest]".
    iDestruct (pctx_own_mode_le with "Rest") as %Hk.
    iDestruct (pctx_own_in with "Rest") as %HinK.
    set y := pctx_get K x₀.
    set q0 := pctx_path K [].
    set lr := (l, repeat [] (lty_size (pctx_plug K lt1))).
    destruct y as [[[[[ly z] ξi] d0] g0] idx0] eqn:Hy.
    rewrite /= /res_node /=. iDestruct "H" as "[Pt N]".
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗a ⧖0") as "[_ £]";
      [solve_ndisj|].
    iDestruct (lc_weaken (pctx_mode K 1 + 1) with "£") as "[£m £1]";
      [rewrite /advance_credits pctx_mode_add; nia|].
    iMod (lc_fupd_elim_laterN with "£m N") as "(#InclK & %d' & %g' & %Hle' & V)".
    rewrite lty_pat_plug lty_rfn_plug.
    set w := pctx_get K2 z. set ζi := blk_lookup ζm (pctx_path K2 (false :: q0)).
    iDestruct (view_pctx_acc K2 κ (Blocked ty β) 0 (PatBlocked β)
      (inl (PlaceGhost w ζi)) z ζm (false :: q0) d' g' tid ly (fractional.half γ1)
      with "Hs V") as (dh gh) "([%Hdh [%Hgh %Hin]] & Vh & #Gs & Cl)".
    iEval (rewrite /= /view_leaf) in "Vh". iDestruct "Vh" as "[#Gc Bor]".
    set κh := pctx_slft K2 κ.
    set lh := pctx_loc K2 (lty_size (Blocked ty β)) z ly.
    iMod (fractional.frac_split_guard_in_half NllftG (fractional.half γ1) (fractional.half γ1)
      with "GP []") as (γ2) "[H1 [H2 [#Gh2 #Back2]]]"; [solve_ndisj|iApply guards_refl|].
    iAssert (fractional.half γ2 &&{↑NllftG}&&> @[κh])%I as "#H2κ".
    { iApply (guards_transitive with "Gh2 Hsl"). }
    iAssert (fractional.half γ2 &&{↑NllftG}&&> @[ty_lft ty])%I as "#H2ty".
    { iApply (guards_transitive with "Gh2 Hty"). }
    (* Open the borrow of the leaf and fire its inheritance. *)
    iMod (llftl_bor_acc_guarded with "LFT Bor H2κ H1") as "[Inh Close]"; [solve_ndisj|].
    iMod (lc_fupd_elim_later with "£1 Inh") as "Inh".
    iMod (fupd_mask_mono with "(Inh [])") as "Upd1"; [rewrite /lazyE; solve_ndisj| |].
    { by iApply pctx_blft_dead. }
    iMod (guarded_upd_run with "H2ty H2 Upd1")
      as "(H2 & %x' & %d1 & %g1 & Eqz & #⧖1 & Pt1 & Gho1)"; [rewrite /lazyE; solve_ndisj|].
    (* The credits of the second receipt, for the leaf. *)
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗b ⧖1") as "[#⧖1' £]";
      [solve_ndisj|].
    iDestruct (lc_weaken (m2 + (1 + ((d1 + d1*(g1+2) + (0 + (d1+1)*(g1+1)) + 1 + 1) +
      (m2 + d1 + 1)))) with "£") as "[£k [£e [£o £s]]]"; [rewrite /advance_credits; nia|].
    iMod (lc_fupd_elim_laterN with "£k Gho1") as "Gho1".
    iSimpl in "Eqz". iMod (lc_fupd_elim_later with "£e Eqz") as "Eqz".
    iMod (proph_eqz_obs_by_share ty with "LFT H2ty H2 £o Eqz Gho1") as "(#Obs1 & H2 & Gho1)".
    (* Close the borrow at the restored contents. *)
    iMod (fupd_mask_subseteq (↑Nllft)) as "Upd"; [solve_ndisj|].
    iMod ("Close" $! (cbytes ty x' lh ∗ ▷^m2 ty_gho_own ty x' d1 g1 tid)%I
      with "[Pt1 Gho1]") as "[Bor H1]".
    { iSplitR "Pt1 Gho1"; [|iNext; iFrame "Pt1"; by iApply bi.laterN_intro].
      iIntros "!> Q !> !>". rewrite /bblocked_owned. iIntros "_ !>".
      iApply guarded_upd_intro. iModIntro. iExists x', d1, g1. iFrame "Q ⧖1".
      iNext. by iApply proph_eqz_obs. }
    iMod "Upd" as "_".
    iMod (fupd_mask_mono with "(Back2 H1 H2)") as "GP"; [solve_ndisj|].
    (* Share the leaf into the view. *)
    set g2 := g1 `max` gh.
    iMod (leaf_share_view κh m2 ty x' d1 g1 g2 tid lh (fractional.half γ1) ⊤
      with "LFT Hsl Lincl [] GP Bor") as "Upd"; [solve_ndisj|lia| |].
    { iApply (lguards_weaken_later with "Gc"). lia. }
    iMod (lc_step_fupdN_elim_later with "£s Upd") as ">[GP Vh]".
    (* The new depths. *)
    iMod (cumulative_persistent_time_receipt with "TIME ⧗e ⧖1'") as "#⧖2"; [solve_ndisj|].
    set dn := (d1 + pctx_dlev K2) `max` d'. set gn := g2 `max` g'.
    iDestruct ("Cl" $! (OfTy ty) PatLeaf (inl (PlaceIn x')) d1 g2 dn gn with "[//] [//] [//] [%] Vh")
      as "V'"; [lia|].
    set dr := d `max` (S dn + pctx_mode K 0). set gr := g `max` gn.
    set y' : ~~ (uniq_borₛ 𝔅) := uniq_bor_set_current (ly, z, ξi, d0, g0, idx0) (pctx_set K2 z x').
    iModIntro. iExists dT, (((l, pctx_set K x₀ y'), ζm) -:: xl').
    iSplitR; [done|].
    iMod "ToT'". iModIntro. iNext. iMod "ToT'". iModIntro.
    iApply (step_fupdN_wand with "ToT'"). iIntros ">(GT & T' & #Obs')".
    iMod (fupd_mask_mono with "(BackT GT GP)") as "$"; [solve_ndisj|].
    iModIntro. iSplitR "Obs'".
    { iFrame "T'". rewrite /tctx_elt_interp. iExists (MLitV (VPtr l)). iSplit; [done|].
      iExists (D `max` (e' - 1 + ((m2 + S d1) `max` g1 + 1))), dr, gr.
      iCombine "⧖0 ⧖2" as "⧖D". iFrame "⧖D".
      rewrite (lty_size_plug_eq K (ResUniqLty (pctx_plug K2 (OfTy ty)) κ) lt1) //.
      iFrame "Fr". rewrite Hnrc /=. rewrite Nat.add_0_r. iFrame "⧗r".
      iSplit; [done|]. iSplit.
      { iPureIntro. have Hhn': m2 + e' = pctx_dlev K2 + e0.
        { rewrite /m2 /e' Hhn. by destruct (pctx_ulfts K2). }
        have := pctx_depth_sub K d. rewrite /dr /dn /gr /gn /g2 /e0 in Hhn' |- *. lia. }
      rewrite /ltype_own lty_pat_plug lty_rfn_plug pctx_get_set pctx_rfn_set //
        ltype_own_plug.
      iSplitR "Rest"; last first.
      { iApply (pctx_own_depth_mono with "Rest"); lia. }
      rewrite /= /res_node /= (lty_fold_plug_eq' K2 (OfTy ty) (Blocked ty β)) //.
      iFrame "Pt". iApply bi.laterN_intro.
      iFrame "InclK". iExists dn, gn. iSplit.
      { iPureIntro. rewrite pctx_depth_sub. lia. }
      rewrite lty_pat_plug lty_rfn_plug pctx_get_set pctx_rfn_set //. }
    iCombine "Obs1 Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=> π [Heq Hf].
    rewrite /= pctx_get_set /y' uniq_bor_current_set pctx_get_set.
    split; [done|]. split; [done|]. split; [done|]. split; [|done]. symmetry. exact Heq.
  Qed.

  (** Once [α] has ended, the shared-blocked leaf at the hole of [K2] in the view of the
      resolved unique borrow at the hole of [K] (it was shared below the borrow, at
      [pctx_blft (PUniq κ K2) α]) is shared at the lifetime of the view: its inheritance
      is fired inside its borrow (kept in the view, [view_leaf]), and the restored leaf
      is shared ([leaf_share_view]), with the credits of its receipt. Its value does not
      change. *)
  Lemma unblock_tctx_oplace_res_shr {ℭ 𝔅 𝔄 𝔄l 𝔄l'} p n α (K: pctx (uniq_borₛ 𝔅) 𝔄)
      `{!PctxNoUniq K} κ (K2: pctx ℭ 𝔅) `{!PctxNoShr K2} (ty: type ℭ)
      (T: tctx 𝔄l) (T': tctx 𝔄l') E L f :
    lctx_lft_alive E L (pctx_salv K2 κ) →
    lctx_lft_incl E L (pctx_slft K2 κ) (ty_lft ty) →
    unblock_tctx E L α T T' f →
    unblock_tctx E L α
      (p ◁ₗown{n} pctx_plug K
        (ResUniqLty (pctx_plug K2 (ShrBlocked ty (pctx_blft (PUniq κ K2) α))) κ) +:: T)
      (p ◁ₗown{n} pctx_plug K (ResUniqLty (pctx_plug K2 (OfTy ty)) κ) +:: T')
      (λ π '(x -:: xl), λ '(x' -:: xl'), x' = x ∧ f π xl xl').
  Proof.
    iIntros (Alv Incl Un G tid [x xl] ?)
      "#LFT #TIME #PROPH #UNIQ #E #L G #†α /=[(%v & %Hp & Own) T]".
    destruct x as [[l x₀] ζm].
    set β := pctx_blft (PUniq κ K2) α.
    iDestruct "Own" as (D d g) "(#⧖0 & ⧗ & -> & %Hle & Fr & Own)".
    (* The receipt of the leaf. *)
    set e0 := pctx_mode K 0 + 1.
    set e' := pctx_ne K2 e0 0.
    have Hnrc: ∀ X: lty ℭ, lty_nrc (pctx_plug K (ResUniqLty (pctx_plug K2 X) κ)) 0 0 =
      pctx_nrc K 0 0 + pctx_nrc K2 e0 0 + lty_nrc X e' (pctx_nmm K2 e0 0).
    { intros X. rewrite lty_nrc_plug /= lty_nrc_plug pctx_ne_nouniq pctx_nmm_nouniq.
      rewrite (_: 0 + (0 + pctx_mode K 0) + 1 = e0); [|rewrite /e0; lia].
      rewrite /e'. lia. }
    have He'1: 1 ≤ e'. { unfold e', e0. have := pctx_ne_ge K2 (pctx_mode K 0 + 1) 0. lia. }
    have Hsb: lty_nrc (ShrBlocked ty β) e' (pctx_nmm K2 e0 0) = 1.
    { simpl. destruct e'; [lia|done]. }
    rewrite Hnrc Hsb.
    iDestruct (cumulative_time_receipt_sep with "⧗") as "[⧗r ⧗a]".
    have Hhn := pctx_hmode_ne K2 0 e0 0. set m2 := pctx_hmode K2 0.
    leaf_open "L" with "G" as "[L1 back]"; [set_solver|].
    iDestruct (Alv with "L1 E") as "#Lα". iDestruct (Incl with "L1 E") as "#Lincl".
    iMod ("back" with "L1") as "G".
    (* Half of [G] for the rest of the context, the other half for the place. *)
    iMod (fractional.frac_split_guard_in_half with "G L") as (γ1) "[GT [GP [#GhT #BackT]]]";
      [solve_ndisj|].
    iMod (Un with "LFT TIME PROPH UNIQ E GhT GT †α T") as (dT xl') "[#⧖T ToT']".
    iAssert (fractional.half γ1 &&{↑NllftG}&&> @[pctx_salv K2 κ])%I as "#Hs".
    { iApply (guards_transitive with "GhT Lα"). }
    iAssert (fractional.half γ1 &&{↑NllftG}&&> @[pctx_slft K2 κ])%I as "#Hsl".
    { iApply (guards_transitive with "Hs"). iApply pctx_salv_slft. }
    (* The hole of [K]: the resolved unique borrow. *)
    set lt1 := ResUniqLty (pctx_plug K2 (ShrBlocked ty β)) κ.
    rewrite /ltype_own lty_pat_plug lty_rfn_plug ltype_own_plug.
    iDestruct "Own" as "[H Rest]".
    iDestruct (pctx_own_mode_le with "Rest") as %Hk.
    set y := pctx_get K x₀.
    set q0 := pctx_path K [].
    destruct y as [[[[[ly z] ξi] d0] g0] idx0] eqn:Hy.
    rewrite /= /res_node /=. iDestruct "H" as "[Pt N]".
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗a ⧖0") as "[_ £]";
      [solve_ndisj|].
    have Hm: pctx_mode K 1 ≤ D by (rewrite pctx_mode_add; lia).
    iDestruct (lc_weaken (pctx_mode K 1 + (advance_credits D - pctx_mode K 1)) with "£")
      as "[£m £]"; [rewrite /advance_credits; lia|].
    iMod (lc_fupd_elim_laterN with "£m N") as "(#InclK & %d' & %g' & %Hle' & V)".
    rewrite lty_pat_plug lty_rfn_plug.
    set w := pctx_get K2 z.
    iDestruct (view_pctx_acc K2 κ (ShrBlocked ty β) 0 (PatShrBlocked β)
      (inl (PlaceIn w)) z ζm (false :: q0) d' g' tid ly (fractional.half γ1)
      with "Hs V") as (dh gh) "([%Hdh [%Hgh %Hin]] & Vh & #Gs & Cl)".
    iEval (rewrite /= /view_leaf) in "Vh".
    iDestruct "Vh" as (x1 ->) "(_ & _ & _ & #Gc & %d1 & %g1 & [%Hd1 %Hg1] & Bor)".
    set κh := pctx_slft K2 κ.
    set lh := pctx_loc K2 (lty_size (ShrBlocked ty β)) z ly.
    have Hdl: pctx_dlev K2 ≤ D.
    { rewrite pctx_depth_sub in Hle'. lia. }
    iDestruct (lc_weaken (1 + (m2 + d1 + 1)) with "£") as "[£1 £s]".
    { have Hm2: m2 ≤ pctx_dlev K2 + e0 by (rewrite /m2; destruct (pctx_ulfts K2); lia).
      rewrite pctx_depth_sub in Hle'. rewrite /advance_credits /e0 in Hm2 |- *. nia. }
    (* Open the borrow of the inheritance and fire it. *)
    iMod (llftl_bor_acc_guarded with "LFT Bor Hsl GP") as "[Inh Close]"; [solve_ndisj|].
    iMod (lc_fupd_elim_later with "£1 Inh") as "Inh".
    iMod (fupd_mask_mono with "(Inh [])") as "Own1"; [rewrite /lazyE; solve_ndisj| |].
    { by iApply pctx_blft_dead. }
    (* Close the borrow at the restored contents. *)
    iMod (fupd_mask_subseteq (↑Nllft)) as "Upd"; [solve_ndisj|].
    iMod ("Close" $! (bofty_owned m2 ty w d1 g1 tid lh) with "[Own1]") as "[Bor GP]".
    { iSplitR; [|by iNext]. iIntros "!> Q !> !>". iIntros "_ !>". iExact "Q". }
    iMod "Upd" as "_".
    (* Share the leaf into the view. *)
    iMod (leaf_share_view κh m2 ty w d1 g1 gh tid lh (fractional.half γ1) ⊤
      with "LFT Hsl Lincl Gc GP Bor") as "Upd"; [solve_ndisj|lia|].
    iMod (lc_step_fupdN_elim_later with "£s Upd") as ">[GP Vh]".
    iDestruct ("Cl" $! (OfTy ty) PatLeaf (inl (PlaceIn w)) d1 gh d' g' with "[//] [//] [//] [%] Vh")
      as "V'"; [lia|].
    iModIntro. iExists dT, (((l, x₀), ζm) -:: xl').
    iSplitR; [done|].
    iMod "ToT'". iModIntro. iNext. iMod "ToT'". iModIntro.
    iApply (step_fupdN_wand with "ToT'"). iIntros ">(GT & T' & #Obs')".
    iMod (fupd_mask_mono with "(BackT GT GP)") as "$"; [solve_ndisj|].
    iModIntro. iSplitR "Obs'"; last first.
    { iApply (proph_obs_impl with "Obs'")=> π Hf. done. }
    iFrame "T'". rewrite /tctx_elt_interp. iExists (MLitV (VPtr l)). iSplit; [done|].
    iExists D, d, g. iFrame "⧖0".
    rewrite (lty_size_plug_eq K (ResUniqLty (pctx_plug K2 (OfTy ty)) κ) lt1) //.
    iFrame "Fr". rewrite Hnrc /= Nat.add_0_r. iFrame "⧗r".
    iSplit; [done|]. iSplit; [done|].
    rewrite /ltype_own lty_pat_plug lty_rfn_plug ltype_own_plug -/y Hy. iFrame "Rest".
    rewrite /= /res_node /= (lty_fold_plug_eq' K2 (OfTy ty) (ShrBlocked ty β)) //.
    iFrame "Pt". iApply bi.laterN_intro.
    iFrame "InclK". iExists d', g'. iSplit; [done|].
    rewrite lty_pat_plug lty_rfn_plug. iExact "V'".
  Qed.
End unblock.

(** * Dropping a resolved place *)

Section drop.
  Context `{!typeG Σ}.

  (** A resolved place (or any place) is dropped without further resolution: the boxes of
      its owned part are freed ([drop_boxes]), the resolved and shared leaves are forgotten
      (the views of the resolved unique borrows go with them, their referents stay with
      their lenders), then the memory of the place is freed. *)
  Lemma type_drop_oplace_res_instr {𝔄} E L I p n (nz: Z) (lt: lty 𝔄) :
    lty_freeb lt = true → n = lty_size lt → nz = Z.of_nat n →
    typed_instr E L I +[p ◁ₗown{n} lt] (drop_boxes lt (ToLit p);; new_delete.delete [ #nz; ToLit p])%E
      (λ _, +[]) (λ post '-[x], post -[]).
  Proof.
    intros Hf Hn Hnz. eapply typed_instr_tr_impl;
      [|apply (type_drop_oplace_deep_instr _ _ _ _ _ _ lt (λ _ _ _ _, True)); [done..|]].
    - intros post [x []] mask π Hp _. done.
    - apply (lty_rslv_of _ _ _ (λ _ _, True)), lty_resolve_just.
  Qed.
End drop.

(** * Shared borrows below a resolved unique borrow, and folding *)

Section share_fold.
  Context `{!typeG Σ}.

  (** A shared reference to the leaf at the hole of [K2], in the view of the resolved
      unique borrow at the hole of [K] (the leaf is shared at [pctx_slft K2 κ]); the place
      does not change. The first step gives the credits. *)
  Lemma type_share_oplace_res_instr {ℭ 𝔅 𝔄} E L I p n (K: pctx (uniq_borₛ 𝔅) 𝔄)
      `{!PctxNoUniq K} κ (K2: pctx ℭ 𝔅) `{!PctxNoShr K2} (ty: type ℭ) :
    lctx_lft_alive E L (pctx_salv K2 κ) →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K (ResUniqLty (pctx_plug K2 (OfTy ty)) κ)]
      (OfLit (pctx_expr K2 (ToLit (Load Na1Ord MPtr (pctx_expr K (ToLit p))))))
      (λ v, +[v ◁ᵥ &shrb{pctx_slft K2 κ} ty;
        p ◁ₗown{n} pctx_plug K (ResUniqLty (pctx_plug K2 (OfTy ty)) κ)])
      (λ post '-[x], post -[(pctx_loc K2 (lty_size (OfTy ty))
          (uniq_bor_current (pctx_get K x.1.2)) (uniq_bor_loc (pctx_get K x.1.2)),
        pctx_get K2 (uniq_bor_current (pctx_get K x.1.2))); x]).
  Proof.
    iIntros (Alv tid post mask iκs [x []])
      "#LFT #TIME #PROPH #UNIQ #E L I (Tp & _) Obs".
    destruct x as [[l x₀] ζm].
    rewrite /tctx_elt_interp.
    iDestruct "Tp" as (v Hp D d g) "(#⧖ & ⧗p & -> & %Hle & Fr & Own)".
    have ?: Closed [] (pctx_expr K (ToLit p)).
    { apply pctx_expr_closed. have ?: Closed [] p by eapply eval_path_closed. apply _. }
    iDestruct (Alv with "L E") as "#Alv".
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj|].
    iIntros "£ #⧖S". iApply wp_fupd.
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_salv K2 κ])%I as "#Hs".
    { iApply (guards_transitive with "Ghalf Alv"). }
    set lt1 := ResUniqLty (pctx_plug K2 (OfTy ty)) κ.
    rewrite /ltype_own lty_pat_plug lty_rfn_plug ltype_own_plug.
    iDestruct "Own" as "[H Rest]".
    iDestruct (pctx_own_mode_le with "Rest") as %Hk.
    set y := pctx_get K x₀.
    set q0 := pctx_path K [].
    set lr := (l, repeat [] (lty_size (pctx_plug K lt1))).
    set lK := pctx_loc K (lty_size lt1) x₀ lr.
    destruct y as [[[[[ly z] ξi] d0] g0] idx0] eqn:Hy.
    rewrite /= /res_node /=. iDestruct "H" as "[Pt N]".
    iDestruct (lc_weaken (pctx_mode K 1 + (advance_credits D - pctx_mode K 1)) with "£")
      as "[£m £]"; [rewrite /advance_credits pctx_mode_add; lia|].
    iMod (lc_fupd_elim_laterN with "£m N") as "(#Incl & %d' & %g' & %Hle' & V)".
    rewrite lty_pat_plug lty_rfn_plug.
    iDestruct (view_pctx_acc K2 κ (OfTy ty) 0 PatLeaf
      (inl (PlaceIn (pctx_get K2 z))) z ζm (false :: q0) d' g' tid ly (fractional.half γh)
      with "Hs V") as (dh gh) "([%Hdh [%Hgh %Hin]] & #Vh & #Gs & Cl)".
    iEval (rewrite /= /view_leaf) in "Vh".
    iDestruct "Vh" as (z' ->) "(#Gpt & #Shr & #Pers)".
    set zh := pctx_get K2 z.
    set lh := pctx_loc K2 (lty_size (OfTy ty)) z ly.
    have Hdl: pctx_dlev K2 ≤ D.
    { destruct Hle' as [Hle' _]. rewrite pctx_depth_sub in Hle'. lia. }
    have Hg': g' ≤ D by lia.
    have ?: pctx_depth K d ≤ d by (rewrite pctx_depth_sub; lia).
    have Hm: pctx_mode K 1 ≤ D by (rewrite pctx_mode_add; lia).
    iDestruct (lc_weaken (2 * (g' + 1) * pctx_dlev K2) with "£") as "£w".
    { rewrite /advance_credits. clear - Hdl Hg' Hm. nia. }
    (* The address of the hole. *)
    wp_bind (pctx_expr K2 _).
    iApply (wp_pctx_sexpr _ K2 (lty_size (OfTy ty)) (g' + 1) (fractional.half γh) z ly);
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
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    wp_pure _. iModIntro. iExists -[(lh, zh); ((l, x₀), ζm)]. iFrame "L I".
    iSplitL "Hbs Rest Cl ⧗p Fr"; last first.
    { iExact "Obs". }
    iSplitR "Hbs Rest Cl ⧗p Fr".
    { iExists _. iSplit; [by rewrite eval_path_of_val|]. iExists _, D. iSplit; [done|].
      iFrame "⧖". destruct D as [|D']; [lia|]. simpl. iSplit.
      - iApply (lguards_weaken_later with "Gpt"). lia.
      - iSplit; [iApply (ty_shr_depth_mono with "Shr"); lia|].
        iNext. iApply (ty_gho_pers_depth_mono with "Pers"); lia. }
    iSplit; [|done]. iExists (MLitV (VPtr l)). iSplit; [done|]. iExists D, d, g.
    iFrame "⧖ ⧗p Fr". iSplit; [done|]. iSplit; [done|].
    rewrite /ltype_own lty_pat_plug lty_rfn_plug ltype_own_plug -/y Hy. iFrame "Rest".
    rewrite /= /res_node /=. iSplitL "Hbs"; [iExists bs; by iFrame|].
    iApply bi.laterN_intro. iFrame "Incl".
    iExists d', g'. iSplit; [done|]. rewrite lty_pat_plug lty_rfn_plug.
    iApply ("Cl" $! (OfTy ty) PatLeaf (inl (PlaceIn zh)) dh gh d' g' with "[//] [//] [//] [%]").
    { lia. }
    rewrite /= /view_leaf. iExists zh. by iFrame "Gpt Shr Pers".
  Qed.

  (** A resolved unique borrow whose referent is a leaf is folded to a shared reference
      to the referent at its lifetime (retyping the leaf, below no sum). *)
  Lemma tctx_fold_oplace_res_uniq_leaf {𝔅 𝔄} E L p n (K: pctx (uniq_borₛ 𝔅) 𝔄)
      `{!PctxNoUniq K} κ (ty: type 𝔅) :
    pctx_nosum K →
    tctx_incl E L +[p ◁ₗown{n} pctx_plug K (ResUniqLty (OfTy ty) κ)]
      +[p ◁ₗown{n} pctx_plug (pctx_retype K (at_clocₛ 𝔅)) (ShrLty (OfTy ty) κ)]
      (λ post '-[x], post -[((x.1.1, pctx_reset K x.1.2
        ((uniq_bor_loc (pctx_get K x.1.2), uniq_bor_current (pctx_get K x.1.2))
          : ~~ (at_clocₛ 𝔅))), x.2)]).
  Proof.
    intros Hns. split; [by intros ??? [? []]|].
    iIntros (G tid [[[l x₀] ζm] []] mask post ?) "_ _ _ _ _ $ [T _] Obs".
    iDestruct "T" as (v Hp D d g) "(⧖ & ⧗ & -> & %Hle & Fr & Own)".
    rewrite /ltype_own !lty_pat_plug !lty_rfn_plug !ltype_own_plug.
    iDestruct "Own" as "[H Rest]".
    set y := pctx_get K x₀.
    set y' := ((uniq_bor_loc y, uniq_bor_current y) : ~~ (at_clocₛ 𝔅)).
    iModIntro. iExists -[((l, pctx_reset K x₀ y'), ζm)]. iFrame "Obs". iSplit; [|done].
    rewrite /tctx_elt_interp. iExists (MLitV (VPtr l)). iSplit; [done|]. iExists D, d, g.
    rewrite (lty_nrc_plug_retype K (ResUniqLty (OfTy ty) κ) (ShrLty (OfTy ty) κ)) //.
    rewrite (lty_size_plug_retype K (ResUniqLty (OfTy ty) κ) (ShrLty (OfTy ty) κ)); [|done|done].
    iFrame "⧖ ⧗ Fr". iSplit; [done|]. iSplit; [done|].
    rewrite /ltype_own lty_pat_plug lty_rfn_plug pctx_get_reset ltype_own_plug pctx_own_reset //
      pctx_loc_reset // pctx_mode_retype pctx_depth_retype. iFrame "Rest".
    rewrite (_: lty_size (ShrLty (OfTy ty) κ) = lty_size (ResUniqLty (OfTy ty) κ)); [|done].
    destruct y as [[[[[l' x0] ξi] d0] g0] idx0] eqn:Hy.
    rewrite /= /res_node /leaf_owned_s /bleaf_owned /bofty_owned /=.
    iDestruct "H" as "[Pt H]". iSplit; [|done]. iExists (l', x0). iSplit; [done|].
    rewrite cbytes_at_cloc. iFrame "Pt". iNext.
    iDestruct "H" as "(_ & %d' & %g' & %Hle' & %x' & -> & #Gpt & #Shr & #Pers)".
    destruct (pctx_depth K d) as [|dK] eqn:HdK; [lia|]. simpl. iSplit.
    - iApply (lguards_weaken_later with "Gpt"). lia.
    - iSplit; [iApply (ty_shr_depth_mono with "Shr"); lia|].
      iNext. iApply (ty_gho_pers_depth_mono with "Pers"); lia.
  Qed.

  (* The fold of a resolved unique borrow with a compound referent ([lty_view_fold],
     [tctx_fold_oplace_res_uniq], [type_fold_oplace_res_uniq_meta_instr] of
     the deleted legacy [place_res_ops.v]) is not ported: on bytes, the guards of the bytes of the
     components ([cbytes], existential bytes) cannot be combined into a guard of the bytes
     of the whole ([guards_and_point] needs a point property); see
     [design_docs/minirust-memory-model.md], "Outcome: stage 4f". *)
End share_fold.
