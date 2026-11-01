(** * Writing a place

  One rule, [type_write_place_instr], writes a value [pb ◁ᵥ ty'] into the leaf [OfTy ty] at
  the hole of any writable place rooted at a value ([p ◁ₗ pctx_plug K (OfTy ty)],
  [vplace.v]), with the instruction [pctx_vexpr K p <-{ty_mty ty'} pb] ([write], a typed
  [Store]). The context [K] may mix fields, sums, owned pointers and unique borrows in any
  order and nesting (no shared reference and no resolved unique borrow on the path,
  [PctxNoShr]; the siblings below a unique borrow are simple); its root step is an owned
  pointer (a place rooted at an owned location, [p ◁ₗown{n} …]) or a unique borrow
  ([PctxVRoot]). The old value is resolved ([resolve E L ty Φ]); the lifetime of the
  folded type at the outermost unique borrow must be alive ([pctx_ulft]: [static] if there
  is none).

  - The new type ([pctx_wty K ty ty' K' f], computed by the constructors): in general the
    type of the leaf is kept ([pctx_wty_same]: [ty' = ty], the new context is [K] and the
    new value of the place [pctx_set K x b]); if the path is owned (no unique borrow,
    [pctx_nouniq], so the root is an owned pointer) and has no sum ([pctx_nosum]: the
    payload of a sum place has the type of its variant), the leaf may get any type of the
    same size (a strong update, [pctx_wty_strong]: the context is retyped, [pctx_retype],
    the value [pctx_reset K x b]), e.g. to initialize an uninitialized leaf [↯ n].
  - No [Skip]: the first program step (of the address) gives the credits to open the
    enclosing borrows and the cumulative time receipts to raise the depths of the place to
    the depth of the new value.

  The access to the leaf is [wp_vplace_wacc]: from the place, the bytes and the ownership
  of the old value of the leaf, and a closer for a new value of the new type
  ([vplace_wcloser]). It is used by the byte copies too ([place_memcpy.v]). *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From lrust.lang Require Import proofmode.
From lrust.typing Require Export type ltype lpath pctx_acc vplace place_own.
From lrust.typing Require Import type_context programs lft_contexts uniq_util uniq_bor own shr_bor bytes_layout value_ctx product uninit freeable_util place_puniq place_deep.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

(** * The new type of a written leaf *)

Section pctx_wty.
  Context `{!typeG Σ}.

  (** Writing a value of type [ty'] into the leaf [OfTy ty] at the hole of [K] gives the
      context [K'] and the value [f x b] of the place (from its value [x] and the new
      value [b] of the leaf). *)
  Inductive pctx_wty {𝔅 𝔄} (K: pctx 𝔅 𝔄) (ty: type 𝔅) :
      ∀ {𝔅' 𝔄'}, type 𝔅' → pctx 𝔅' 𝔄' → (~~𝔄 → ~~𝔅' → ~~𝔄') → Prop :=
  | pctx_wty_same : pctx_wty K ty ty K (pctx_set K)
  | pctx_wty_strong {𝔅'} (ty': type 𝔅') :
      pctx_nouniq K → pctx_nosum K → ty_bsize ty' = ty_bsize ty →
      pctx_wty K ty ty' (pctx_retype K 𝔅') (pctx_reset K).

  Lemma pctx_wty_bsize {𝔅 𝔄 𝔅' 𝔄'} (K: pctx 𝔅 𝔄) ty (ty': type 𝔅') (K': pctx 𝔅' 𝔄') f :
    pctx_wty K ty ty' K' f → ty_bsize ty' = ty_bsize ty.
  Proof. by destruct 1. Qed.

  Lemma pctx_ulft_nouniq {𝔅 𝔄} (K: pctx 𝔅 𝔄) `{!PctxNoUniq K} lt : pctx_ulft K lt = static.
  Proof.
    rename select (PctxNoUniq K) into HK. rewrite /PctxNoUniq in HK.
    induction K; simpl in *; by try apply IHK.
  Qed.
End pctx_wty.

(** * The access to a written leaf *)

Section write_acc.
  Context `{!typeG Σ}.

  (** The closer of the access: a new value [y'] of the new type, with its cells and its
      ownership, at new depths. *)
  Definition vplace_wcloser {𝔅 𝔄 𝔅' 𝔄'} (K: pctx 𝔅 𝔄) (ty': type 𝔅') (K': pctx 𝔅' 𝔄')
      (f: ~~𝔄 → ~~𝔅' → ~~𝔄') (x₀: ~~𝔄) (ζm: blk_map) (D: nat) (tid: thread_id) (v: val)
      (l: loc) (E: coPset) (G: iProp Σ) : iProp Σ :=
    ∀ y' dh' gh' D', ⌜D ≤ D' ∧ dh' + pctx_dlev K ≤ D' ∧ gh' ≤ D'⌝ -∗ ⧖D' -∗
      cbytes ty' y' l -∗ ty_gho_own ty' y' dh' gh' tid ={E}=∗
      vplace_own (pctx_plug K' (OfTy ty')) (f x₀ y', ζm) tid v ∗ G.

  (** The type is kept: the access of [vplace_leaf_acc] ([place_deep.v]), below any number
      of unique borrows, in both modes of the hole. *)
  Lemma wp_vplace_wacc_same {𝔅 𝔄} E (K: pctx 𝔅 𝔄) `{!PctxNoShr K} `{!PctxVRoot K}
      (ty: type 𝔅) x₀ ζm D tid p v (G: iProp Σ) Φ :
    Timeless G → lazyE ⊆ E → eval_path p = Some v →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[pctx_ulft K (OfTy ty)]) -∗ G -∗
    £((D + 1) * (D + 2) + 1) -∗ ⧖D -∗ ⧗(lty_vnrc (pctx_plug K (OfTy ty))) -∗
    vroot_own (pctx_plug K (OfTy ty)) (pctx_vrfn K x₀ ζm (inl (PlaceIn (pctx_get K x₀)))) D
      tid v -∗
    (∀ (l: loc) dh gh, ⌜dh + pctx_dlev K ≤ D ∧ gh ≤ D⌝ -∗
      cbytes ty (pctx_get K x₀) l -∗ ty_gho_own ty (pctx_get K x₀) dh gh tid -∗
      vplace_wcloser K ty K (pctx_set K) x₀ ζm D tid v l E G -∗ Φ #l) -∗
    WP pctx_vexpr K p @ E {{ Φ }}.
  Proof.
    iIntros (?? Hp) "#LFT #PROPH #UNIQ #Gu G £ #⧖ ⧗p Own HΦ".
    iMod (vplace_leaf_acc K ty x₀ ζm D tid v E G with "LFT PROPH UNIQ Gu G £ Own")
      as (G' dh gh) "(% & G' & -> & %Hdh & #G'u & Pt1 & Gho1 & P & Cl)"; [done|done|].
    destruct Hdh as (Hdh & Hgh & Hin).
    iApply (wp_wand with "[P G']").
    { iApply (wp_pctx_vptrs E K (lty_size (OfTy ty)) G' x₀ p True%I with "[G'] P").
      iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->". by iFrame. }
    iIntros (w) "(-> & _ & G' & P)".
    iApply ("HΦ" with "[%] Pt1 Gho1"); [done|].
    iIntros (y' dh' gh' D' HD) "#⧖' Pt Gho".
    iMod ("Cl" $! y' dh' gh' D' with "[//] ⧖' G' P Pt Gho") as "[Own $]".
    iModIntro. iApply (vplace_own_close K _ _ _ D' with "⧖' ⧗p").
    by rewrite pctx_get_set pctx_vrfn_set.
  Qed.

  (** A strong update of a leaf of an owned path without sums: the ownership of the place
      splits ([ltype_own_plug]), and the context is retyped. *)
  Lemma wp_vplace_wacc_strong {𝔅 𝔄 𝔅'} E n (K: pctx 𝔅 𝔄) `{!PctxNoUniq K} (ty: type 𝔅)
      (ty': type 𝔅') x₀ ζm D tid p v (G: iProp Σ) Φ :
    pctx_nosum K → ty_bsize ty' = ty_bsize ty → eval_path p = Some v →
    G -∗ £((D + 1) * (D + 2) + 1) -∗ ⧖D -∗ ⧗(lty_vnrc (pctx_plug (POwn n K) (OfTy ty))) -∗
    vroot_own (pctx_plug (POwn n K) (OfTy ty))
      (pctx_vrfn (POwn n K) x₀ ζm (inl (PlaceIn (pctx_get (POwn n K) x₀)))) D tid v -∗
    (∀ (l: loc) dh gh, ⌜dh + pctx_dlev (POwn n K) ≤ D ∧ gh ≤ D⌝ -∗
      cbytes ty (pctx_get (POwn n K) x₀) l -∗
      ty_gho_own ty (pctx_get (POwn n K) x₀) dh gh tid -∗
      vplace_wcloser (POwn n K) ty' (pctx_retype (POwn n K) 𝔅') (pctx_reset (POwn n K))
        x₀ ζm D tid v l E G -∗ Φ #l) -∗
    WP pctx_vexpr (POwn n K) p @ E {{ Φ }}.
  Proof.
    iIntros (Hns Hsz Hp) "G £ #⧖ ⧗p Own HΦ".
    destruct x₀ as [l x₀]. rewrite /=.
    iDestruct "Own" as (d g -> Hle) "[Fr Own]".
    rewrite /ltype_own lty_pat_plug ltype_own_plug.
    iDestruct "Own" as "[L1 Rest]". iSimpl in "L1".
    iDestruct "L1" as (? ->) "[Pt1 Gho1]".
    iDestruct (pctx_own_mode_le with "Rest") as %Hk.
    have Hdl: pctx_dlev K = pctx_mode K 0 by apply pctx_dlev_nouniq.
    iDestruct (lc_weaken (pctx_mode K 1) with "£") as "£"; [rewrite pctx_mode_add; nia|].
    iMod (lc_fupd_elim_laterN with "£ Gho1") as "Gho1".
    (* The address of the hole. *)
    iApply (wp_wand with "[Rest]").
    { iApply (wp_pctx_expr_mask E K (lty_size (OfTy ty)) 1 x₀ ζm [] d g tid l (ToLit p)
        True True with "[] Rest").
      wp_bind p. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->".
      by wp_pure _. }
    iIntros (w) "(-> & _ & _ & Rest)".
    iApply ("HΦ" with "[%] Pt1 Gho1").
    { rewrite /= pctx_depth_sub. lia. }
    iIntros (y' dh' gh' D' (HD & Hdh' & Hgh')) "#⧖' Pt Gho". simpl in Hdh'.
    iModIntro. iFrame "G".
    have Hsz' : lty_size (OfTy ty') = lty_size (OfTy ty).
    { by rewrite /lty_size -(ty_bsize_eq ty) -(ty_bsize_eq ty'). }
    iApply (vplace_own_close (POwn n (pctx_retype K 𝔅')) _ _ _ D' with "⧖' [⧗p]").
    { by rewrite /= (lty_nrc_plug_retype K (OfTy ty) (OfTy ty')). }
    rewrite /=. iExists (pred D'), D'. iSplit; [done|]. iSplit; [iPureIntro; lia|].
    rewrite (lty_size_plug_retype K (OfTy ty) (OfTy ty')) //. iFrame "Fr".
    rewrite /ltype_own lty_pat_plug pctx_get_reset ltype_own_plug pctx_own_reset //
      pctx_loc_reset // pctx_mode_retype pctx_depth_retype /= Hsz'.
    iSplitR "Rest".
    - iExists y'. iSplit; [done|]. rewrite /ofty_owned. iFrame "Pt".
      iApply bi.laterN_intro.
      iDestruct (ty_gho_own_depth_mono _ dh' gh' (pctx_depth K (pred D')) D' with "Gho")
        as "[$ _]"; [rewrite pctx_depth_sub; lia|lia].
    - iApply (pctx_own_depth_mono with "Rest"); lia.
  Qed.

  (** The access to the leaf [OfTy ty] at the hole of a writable context [K], for a write
      of a value of type [ty'] ([pctx_wty]): from the place, a CPS around the address of
      the hole ([pctx_vexpr K p]), which gives the bytes and the ownership of the old value
      of the leaf (without laters), and a closer for a new value of type [ty']. The
      enclosing borrows are opened with the later credits [£((D + 1) * (D + 2) + 1)]. *)
  Lemma wp_vplace_wacc {𝔅 𝔄 𝔅' 𝔄'} E (K: pctx 𝔅 𝔄) `{!PctxNoShr K} `{!PctxVRoot K}
      (ty: type 𝔅) (ty': type 𝔅') (K': pctx 𝔅' 𝔄') f x₀ ζm D tid p v (G: iProp Σ) Φ :
    pctx_wty K ty ty' K' f → Timeless G → lazyE ⊆ E → eval_path p = Some v →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[pctx_ulft K (OfTy ty)]) -∗ G -∗
    £((D + 1) * (D + 2) + 1) -∗ ⧖D -∗ ⧗(lty_vnrc (pctx_plug K (OfTy ty))) -∗
    vroot_own (pctx_plug K (OfTy ty)) (pctx_vrfn K x₀ ζm (inl (PlaceIn (pctx_get K x₀)))) D
      tid v -∗
    (∀ (l: loc) dh gh, ⌜dh + pctx_dlev K ≤ D ∧ gh ≤ D⌝ -∗
      cbytes ty (pctx_get K x₀) l -∗ ty_gho_own ty (pctx_get K x₀) dh gh tid -∗
      vplace_wcloser K ty' K' f x₀ ζm D tid v l E G -∗ Φ #l) -∗
    WP pctx_vexpr K p @ E {{ Φ }}.
  Proof.
    intros Hw. destruct Hw as [|𝔅'' ty'' Hnu Hns Hsz].
    - intros. iIntros "LFT PROPH UNIQ Gu G £ ⧖ ⧗p Own HΦ".
      iApply (wp_vplace_wacc_same with "LFT PROPH UNIQ Gu G £ ⧖ ⧗p Own HΦ"); done.
    - rename select (PctxVRoot K) into HR.
      destruct K as [| | |𝔄'' n K| | | |]; try done.
      have ?: PctxNoUniq K by done. intros _ _ Hp.
      iIntros "_ _ _ _ G £ ⧖ ⧗p Own HΦ".
      iApply (wp_vplace_wacc_strong with "G £ ⧖ ⧗p Own HΦ"); done.
  Qed.
End write_acc.

(** * The rule *)

Section write.
  Context `{!typeG Σ}.

  (** Writing a value of type [ty'] into the leaf [OfTy ty] at the hole of [K] ([pctx_wty]:
      of the same type, or of any type of the same size along an owned path without sums):
      a typed [Store] ([<-{ty_mty ty'}]) at the address of the hole. The old value is
      resolved. *)
  Lemma type_write_place_instr {𝔅 𝔄 𝔅' 𝔄'} E L I p pb (K: pctx 𝔅 𝔄) `{!PctxNoShr K}
      `{!PctxVRoot K} (ty: type 𝔅) (ty': type 𝔅') (K': pctx 𝔅' 𝔄') f Φ :
    pctx_wty K ty ty' K' f → resolve E L ty Φ → lctx_lft_alive E L (pctx_ulft K (OfTy ty)) →
    typed_instr E L I +[p ◁ₗ pctx_plug K (OfTy ty); pb ◁ᵥ ty']
      (pctx_vexpr K p <-{ty'.(ty_mty)} pb)
      (λ _, +[p ◁ₗ pctx_plug K' (OfTy ty')])
      (λ post '-[x; b], λ mask π, Φ (pctx_get K x.1) π → post -[(f x.1 b, x.2)] mask π).
  Proof.
    iIntros (Hw Rslv Alv tid post mask iκs [x [b []]])
      "#LFT #TIME #PROPH #UNIQ #E L I (Tp & Tb & _) Obs".
    destruct x as [x₀ ζm]. rewrite /write.
    iDestruct "Tp" as (v Hp) "Tp". iEval (rewrite vplace_own_open) in "Tp".
    iDestruct "Tp" as (D) "(#⧖ & ⧗p & Own)".
    iDestruct "Tb" as (vb Hpb wb db fvb [-> Hfvb]) "(Hcb & #⧖b & Gb)".
    have ?: Closed [] pb by eapply eval_path_closed.
    iDestruct (Alv with "L E") as "#Alv".
    (* The first step gives credits and cumulative time receipts. *)
    iCombine "⧖ ⧖b" as "⧖m".
    iApply (wp_cumulative_time_receipt_linear with "TIME ⧖m"); [solve_ndisj|].
    iIntros "⧗". set M := D `max` db.
    iDestruct (cumulative_time_receipt_sep 1 (S M) with "⧗") as "[⧗c ⧗k]".
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗c ⧖m") as "[_ £]";
      [solve_ndisj|].
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_ulft K (OfTy ty)])%I as "#Hu".
    { iApply (guards_transitive with "Ghalf Alv"). }
    have HM: D ≤ M by rewrite /M; lia.
    iDestruct (lc_weaken (((D + 1) * (D + 2) + 1) + (1 + (1 + D * (D + 1)))) with "£")
      as "[£a [£r £s]]"; [rewrite /advance_credits; nia|].
    (* The access to the leaf, and its address. *)
    wp_bind (pctx_vexpr K p).
    iApply (wp_vplace_wacc _ K ty ty' K' f with "LFT PROPH UNIQ Hu H1 £a ⧖ ⧗p Own");
      [done|apply _|solve_ndisj|done|].
    iIntros (lK dh gh [Hdh Hgh]) "Pt1 Gho1 Cl".
    wp_bind pb. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->".
    (* Resolve the old value. *)
    iDestruct (Rslv _ (⊤ ∖ (⊤ ∖ ↑Nllft ∖ ↑prophN ∖ ↑timeN ∖ ↑uniqN))
      with "LFT PROPH UNIQ TIME E Ghalf H2 Gho1") as "ToObs"; [set_solver|].
    iMod (lc_fupd_elim_later with "£r ToObs") as "ToObs".
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iDestruct (lc_step_fupdN_elim_later with "[£s] ToObs") as "ToObs".
    { iApply (lc_weaken with "£s"). nia. }
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iMod (fupd_mask_mono with "ToObs") as "[Obs' H2]"; [solve_ndisj|].
    (* Write. *)
    iApply wp_fupd.
    iApply (wp_bytes_own_forget with "Pt1"); [solve_ndisj|]. iIntros (bs) "Hbs %Hlen".
    iApply (wp_val_cells_store with "[$Hbs $Hcb]");
      [solve_ndisj|done|by rewrite Hlen (pctx_wty_bsize _ _ _ _ _ Hw)|].
    iIntros "!> Hbs".
    (* Close the place at the new value. *)
    iDestruct (cumulative_time_receipt_mono (pctx_dlev K) with "⧗k") as "⧗k"; [lia|].
    iMod (cumulative_persistent_time_receipt with "TIME ⧗k ⧖b") as "#⧖k"; [solve_ndisj|].
    set Dn := D `max` (pctx_dlev K + db).
    iCombine "⧖ ⧖k" as "⧖D".
    iMod ("Cl" $! b db db Dn with "[%] [] Hbs Gb") as "[Own H1]"; [rewrite /Dn; lia| |].
    { iApply (persistent_time_receipt_mono with "⧖D"). rewrite /Dn. lia. }
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iModIntro. iExists -[(f x₀ b, ζm)]. iFrame "L I".
    iSplitR "Obs Obs'". { iSplit; [|done]. iExists _. by iFrame. }
    iCombine "Obs Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=> π [Hπ HΦ].
    by apply Hπ.
  Qed.
End write.
