(** * Writing a place

  One rule, [type_write_place_instr], writes a value [pb ◁ᵥ ty'] into the leaf [lt] at the
  hole of any writable place rooted at a value ([p ◁ₗ pctx_plug K lt], [vplace.v]), with
  the instruction [pctx_vexpr K p <-{ty_mty ty'} pb] ([write], a typed [Store]). The
  context [K] may mix fields, sums, owned pointers and unique borrows in any order and
  nesting (no shared reference and no resolved unique borrow on the path, [PctxNoShr]; the
  siblings below a unique borrow are simple); its root step is an owned pointer (a place
  rooted at an owned location, [p ◁ₗown{n} …]) or a unique borrow ([PctxVRoot]). The old
  value of an [OfTy] leaf is resolved ([lty_wres E L lt Φ]: [resolve E L ty Φ]; nothing for
  a moved-out leaf, [lty_wres_moved]); the lifetimes needed to access the hole must be alive
  ([pctx_alv], [pctx_acc.v]: the lifetime of the folded type at each unique borrow,
  [static] if there is none).

  - The leaf and the new type ([pctx_wty K lt ty' K' f], by its constructors): a leaf
    [OfTy ty] keeps its type ([pctx_wty_same]: [ty' = ty], the new context is [K] and the
    new value of the place [pctx_set K x b]), or, if the path is owned (no unique borrow,
    [pctx_nouniq], so the root is an owned pointer) and has no sum ([pctx_nosum]: the
    payload of a sum place has the type of its variant), gets any type of the same size (a
    strong update, [pctx_wty_strong]: the context is retyped, [pctx_retype], the value
    [pctx_reset K x b]), e.g. to initialize an uninitialized leaf [↯ n]. A moved-out leaf
    [Moved ty] (only along an owned path) is re-initialized with a value of [ty]
    ([pctx_wty_moved], also in the payload of a sum), or, without sums, of any type of the
    same size ([pctx_wty_moved_strong]).
  - No [Skip]: the first program step (of the address) gives the credits to open the
    enclosing borrows and the cumulative time receipts to raise the depths of the place to
    the depth of the new value.

  The access to the leaf is [wp_vplace_wacc]: from the place, the old contents of the leaf
  ([lty_wold]) and a closer for a new value of the new type ([vplace_wcloser]); along an
  owned path, [wp_vplace_wacc_own] (any leaf without blocked parts). It is used by the
  byte copies too ([place_memcpy.v]). *)

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

  (** Writing a value of type [ty'] into the leaf [lt] at the hole of [K] gives the
      context [K'] and the value [f x b] of the place (from its value [x] and the new
      value [b] of the leaf). The leaf is [OfTy ty] (its old value is resolved) or a
      moved-out leaf [Moved ty] (re-initialization, along an owned path). *)
  Inductive pctx_wty {𝔅 𝔄} (K: pctx 𝔅 𝔄) :
      ∀ {𝔅' 𝔄'}, lty 𝔅 → type 𝔅' → pctx 𝔅' 𝔄' → (~~𝔄 → ~~𝔅' → ~~𝔄') → Prop :=
  | pctx_wty_same (ty: type 𝔅) : pctx_wty K (OfTy ty) ty K (pctx_set K)
  | pctx_wty_strong (ty: type 𝔅) {𝔅'} (ty': type 𝔅') :
      pctx_nouniq K → pctx_nosum K → ty_bsize ty' = ty_bsize ty →
      pctx_wty K (OfTy ty) ty' (pctx_retype K 𝔅') (pctx_reset K)
  | pctx_wty_moved (ty: type 𝔅) :
      pctx_nouniq K → pctx_wty K (Moved ty) ty K (pctx_set K)
  | pctx_wty_moved_strong (ty: type 𝔅) {𝔅'} (ty': type 𝔅') :
      pctx_nouniq K → pctx_nosum K → ty_bsize ty' = ty_bsize ty →
      pctx_wty K (Moved ty) ty' (pctx_retype K 𝔅') (pctx_reset K).

  (** The size of the new type is the size of the leaf. *)
  Lemma pctx_wty_bsize {𝔅 𝔄 𝔅' 𝔄'} (K: pctx 𝔅 𝔄) lt (ty': type 𝔅') (K': pctx 𝔅' 𝔄') f :
    pctx_wty K lt ty' K' f → ty_bsize ty' = lty_size lt.
  Proof.
    destruct 1 as [ty|ty ?? ? ? Hsz|ty ?|ty ?? ? ? Hsz]; by rewrite ?Hsz (lty_size_ty _ ty).
  Qed.

  Lemma pctx_ulft_nouniq {𝔅 𝔄} (K: pctx 𝔅 𝔄) `{!PctxNoUniq K} lt : pctx_ulft K lt = static.
  Proof.
    rename select (PctxNoUniq K) into HK. rewrite /PctxNoUniq in HK.
    induction K; simpl in *; by try apply IHK.
  Qed.

  (** The old contents of a written leaf: the bytes and the ownership of the value of
      [OfTy ty], the plain bytes of [Moved ty]. *)
  Definition lty_wold {𝔅} (lt: lty 𝔅) : ~~𝔅 → nat → nat → thread_id → loc → iProp Σ :=
    match lt in lty 𝔅 return ~~𝔅 → nat → nat → thread_id → loc → iProp Σ with
    | OfTy ty => λ y dh gh tid l, cbytes ty y l ∗ ty_gho_own ty y dh gh tid
    | Moved ty => λ _ _ _ _ l, pad_cell l (ty_bsize ty)
    | _ => λ _ _ _ _ _, False
    end%I.

  (** The resolution of the old value of a written leaf: [resolve] for [OfTy ty], nothing
      for [Moved ty] ([lty_wres_moved]). *)
  Definition lty_wres {𝔅} (E: elctx) (L: llctx) (lt: lty 𝔅) (Φ: ~~𝔅 → proph_asn → Prop) :
      Prop :=
    match lt in lty 𝔅 return (~~𝔅 → proph_asn → Prop) → Prop with
    | OfTy ty => λ Φ, resolve E L ty Φ
    | Moved _ => λ Φ, ∀ x π, Φ x π
    | _ => λ _, False
    end Φ.

  Lemma lty_wres_moved {𝔅} E L (ty: type 𝔅) : lty_wres E L (Moved ty) (λ _ _, True).
  Proof. done. Qed.
  (** Resolving the old contents of a written leaf, which gives its bytes. *)
  Lemma lty_wold_resolve {𝔅} E L (lt: lty 𝔅) Φ y dh gh D tid l G F :
    lty_wres E L lt Φ → Timeless G → dh ≤ D → gh ≤ D →
    ↑Nllft ∪ ↑prophN ∪ ↑uniqN ∪ ↑gmbN ∪ lazyE ∪ ↑gcellsN ⊆ F →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ time_ctx -∗ elctx_interp E -∗
    (G &&{↑NllftG}&&> llctx_interp L) -∗ G -∗ gcells_ctx -∗
    £(1 + (1 + D * (D + 1)) + 1) -∗ lty_wold lt y dh gh tid l ={F}=∗
      ⟨π, Φ y π⟩ ∗ G ∗ ∃ bs, l ↦b bs ∗ ⌜length bs = lty_size lt⌝.
  Proof.
    iIntros (Rslv ? Hdh Hgh HF) "#LFT #PROPH #UNIQ #TIME #E #L G #GC [[£r £s] £f] Old".
    destruct lt as [𝔅 ty| | | | | | | | | |𝔅 ty]; simpl in Rslv; try done.
    - iDestruct "Old" as "[Pt Gho]".
      iDestruct (Rslv _ F with "LFT PROPH UNIQ TIME E L G Gho") as "ToObs"; [set_solver|].
      iMod (lc_fupd_elim_later with "£r ToObs") as "ToObs".
      iMod "ToObs".
      iDestruct (lc_step_fupdN_elim_later with "[£s] ToObs") as "ToObs".
      { iApply (lc_weaken with "£s"). nia. }
      iMod "ToObs" as ">[$ $]".
      iMod (bytes_own_forget with "GC £f Pt") as (bs) "[Hbs %Hlen]"; [set_solver|].
      iModIntro. iExists bs. iFrame. by rewrite Hlen (lty_size_ty _ ty).
    - iFrame "G". iSplitR.
      { iApply proph_obs_true=> π. apply Rslv. }
      iDestruct "Old" as (bs) "[Hbs %Hlen]". iModIntro. iExists bs. iFrame.
      by rewrite Hlen (lty_size_ty _ ty).
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
    £(3 * D + 5) -∗ ⧖D -∗ ⧗(lty_vnrc (pctx_plug K (OfTy ty))) -∗
    vroot_own (pctx_plug K (OfTy ty)) (pctx_vrfn K x₀ ζm (inl (PlaceIn (pctx_get K x₀)))) D
      tid v -∗
    (∀ (l: loc) dh gh, ⌜dh + pctx_dlev K ≤ D ∧ gh ≤ D⌝ -∗
      cbytes ty (pctx_get K x₀) l -∗ ty_gho_own ty (pctx_get K x₀) dh gh tid -∗
      vplace_wcloser K ty K (pctx_set K) x₀ ζm D tid v l E G -∗ Φ #l) -∗
    WP pctx_vexpr K p @ E {{ Φ }}.
  Proof.
    iIntros (?? Hp) "#LFT #PROPH #UNIQ #Gu G £ #⧖ ⧗p Own HΦ".
    iMod (vplace_leaf_acc K ty x₀ ζm D tid v E G with "LFT PROPH UNIQ Gu G £ Own")
      as (G' dh gh) "(% & G' & -> & %Hdh & #G'u & Pt1 & Gho1 & P & Cl)"; [done|].
    destruct Hdh as (Hdh & Hgh & Hin).
    iApply (wp_wand with "[P G']").
    { iApply (wp_pctx_vptrs E K (lty_size (OfTy ty)) G' x₀ p True%I with "[G'] P").
      iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->". by iFrame. }
    iIntros (w) "(-> & _ & G' & P)".
    iApply ("HΦ" with "[%] Pt1 Gho1"); [done|]. rewrite /vplace_wcloser.
    iIntros (y' dh' gh' D' HD) "#⧖' Pt Gho".
    iMod ("Cl" $! y' dh' gh' D' with "[//] ⧖' G' P Pt Gho") as "[Own $]".
    iModIntro. iApply (vplace_own_close K _ _ _ D' with "⧖' ⧗p").
    by rewrite pctx_get_set pctx_vrfn_set.
  Qed.

  (** The new context of a write into a leaf of an owned path: the same type, or (without
      sums) any type, retyping the context. *)
  Inductive pctx_wown {𝔅 𝔄} (K: pctx 𝔅 𝔄) :
      ∀ {𝔅' 𝔄'}, type 𝔅' → pctx 𝔅' 𝔄' → (~~𝔄 → ~~𝔅' → ~~𝔄') → Prop :=
  | pctx_wown_same (ty: type 𝔅) : pctx_wown K ty K (pctx_set K)
  | pctx_wown_strong {𝔅'} (ty': type 𝔅') :
      pctx_nosum K → pctx_wown K ty' (pctx_retype K 𝔅') (pctx_reset K).

  (** The write access to any leaf [lt] (without blocked leaves, [lty_nrc]) of an owned
      path: the ownership of the place splits ([ltype_own_plug]); the closer puts a leaf
      [OfTy ty'] of the same size, in the same context or in the retyped one. *)
  Lemma wp_vplace_wacc_own {𝔅 𝔄 𝔅' 𝔄'} E n (K: pctx 𝔅 𝔄) `{!PctxNoUniq K} (lt: lty 𝔅)
      (ty': type 𝔅') (K': pctx 𝔅' 𝔄') f x₀ ζm D tid p v (G: iProp Σ) Φ :
    pctx_wown (POwn n K) ty' K' f → ty_bsize ty' = lty_size lt →
    (∀ e mm, lty_nrc lt e mm = 0) → eval_path p = Some v →
    G -∗ ⧖D -∗ ⧗(lty_vnrc (pctx_plug (POwn n K) lt)) -∗
    vroot_own (pctx_plug (POwn n K) lt)
      (pctx_vrfn (POwn n K) x₀ ζm (inl (PlaceIn (pctx_get (POwn n K) x₀)))) D tid v -∗
    (∀ (l: loc) dh gh, ⌜dh + pctx_dlev (POwn n K) ≤ D ∧ gh ≤ D⌝ -∗
      ltype_own (Owned (pctx_mode K 1)) lt (inl (PlaceIn (pctx_get (POwn n K) x₀))) dh gh
        tid l -∗
      vplace_wcloser (POwn n K) ty' K' f x₀ ζm D tid v l E G ={E}=∗ Φ #l) -∗
    WP pctx_vexpr (POwn n K) p @ E {{ Φ }}.
  Proof.
    iIntros (Hw Hsz Hnrc Hp) "G #⧖ ⧗p Own HΦ".
    destruct x₀ as [l x₀]. rewrite /=.
    iDestruct "Own" as (d g -> Hle) "[Fr Own]".
    rewrite /ltype_own lty_pat_plug ltype_own_plug.
    iDestruct "Own" as "[L1 Rest]".
    iDestruct (pctx_own_mode_le with "Rest") as %Hk.
    iDestruct (pctx_own_in with "Rest") as %Hin.
    have Hdl: pctx_dlev K = pctx_mode K 0 by apply pctx_dlev_nouniq.
    have Hsz' : lty_size (OfTy ty') = lty_size lt.
    { by rewrite /lty_size -(ty_bsize_eq ty'). }
    (* The address of the hole. *)
    iApply wp_fupd. iApply (wp_wand with "[Rest]").
    { iApply (wp_pctx_expr_mask E K (lty_size lt) 1 x₀ ζm [] d g tid l (p)
        True True with "[] Rest").
      wp_bind p. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->".
      iFrame; by iPureIntro. }
    iIntros (w) "(-> & _ & _ & Rest)".
    iApply ("HΦ" with "[%] L1").
    { rewrite /= pctx_depth_sub. lia. }
    rewrite /vplace_wcloser.
    iIntros (y' dh' gh' D' (HD & Hdh' & Hgh')) "#⧖' Pt Gho". simpl in Hdh'.
    iModIntro. iFrame "G".
    have Hgho: ty_gho_own ty' y' dh' gh' tid -∗
      ▷^(pctx_mode K 1) ty_gho_own ty' y' (pctx_depth K (pred D')) D' tid.
    { iIntros "Gho". iApply bi.laterN_intro.
      iDestruct (ty_gho_own_depth_mono _ dh' gh' (pctx_depth K (pred D')) D' with "Gho")
        as "[$ _]"; [rewrite pctx_depth_sub; lia|lia]. }
    destruct Hw as [ty|𝔅'' ty'' Hns]; [|simpl in Hns].
    - iApply (vplace_own_close (POwn n K) _ _ _ D' with "⧖' [⧗p]").
      { rewrite /= (lty_nrc_plug_eq K lt (OfTy ty)) //. fun_ext=> e. fun_ext=> mm.
        by rewrite Hnrc. }
      rewrite /=. iExists (pred D'), D'. iSplit; [done|]. iSplit; [iPureIntro; lia|].
      rewrite (lty_size_plug_eq K (OfTy ty) lt) //. iFrame "Fr".
      rewrite /ltype_own lty_pat_plug pctx_get_set pctx_rfn_set // ltype_own_plug /= Hsz'.
      iSplitR "Rest".
      + iExists y'. iSplit; [done|]. rewrite /ofty_owned. iFrame "Pt". by iApply Hgho.
      + iApply (pctx_own_depth_mono with "Rest"); lia.
    - iApply (vplace_own_close (POwn n (pctx_retype K 𝔅'')) _ _ _ D' with "⧖' [⧗p]").
      { rewrite /= (lty_nrc_plug_retype K lt (OfTy ty'')) //; intros e mm;
        by rewrite Hnrc. }
      rewrite /=. iExists (pred D'), D'. iSplit; [done|]. iSplit; [iPureIntro; lia|].
      rewrite (lty_size_plug_retype K lt (OfTy ty'')) //. iFrame "Fr".
      rewrite /ltype_own lty_pat_plug pctx_get_reset ltype_own_plug pctx_own_reset //
        pctx_loc_reset // pctx_mode_retype pctx_depth_retype /= Hsz'.
      iSplitR "Rest".
      + iExists y'. iSplit; [done|]. rewrite /ofty_owned. iFrame "Pt". by iApply Hgho.
      + iApply (pctx_own_depth_mono with "Rest"); lia.
  Qed.

  (** The access to the leaf [lt] at the hole of a writable context [K], for a write of a
      value of type [ty'] ([pctx_wty]): from the place, a CPS around the address of the
      hole ([pctx_vexpr K p]), which gives the old contents of the leaf ([lty_wold]: the
      bytes and the ownership of the old value, without laters, or the plain bytes of a
      moved-out leaf), and a closer for a new value of type [ty']. The enclosing borrows
      are opened with the later credits [£(3 * D + 5)]. *)
  Lemma wp_vplace_wacc {𝔅 𝔄 𝔅' 𝔄'} E (K: pctx 𝔅 𝔄) `{!PctxNoShr K} `{!PctxVRoot K}
      (lt: lty 𝔅) (ty': type 𝔅') (K': pctx 𝔅' 𝔄') f x₀ ζm D tid p v (G: iProp Σ) Φ :
    pctx_wty K lt ty' K' f → Timeless G → lazyE ⊆ E → eval_path p = Some v →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[pctx_ulft K lt]) -∗ G -∗
    £(3 * D + 5) -∗ ⧖D -∗ ⧗(lty_vnrc (pctx_plug K lt)) -∗
    vroot_own (pctx_plug K lt)
      (pctx_vrfn K x₀ ζm (lty_rfn lt (pctx_get K x₀) ζm (pctx_vpath K))) D tid v -∗
    (∀ (l: loc) dh gh, ⌜dh + pctx_dlev K ≤ D ∧ gh ≤ D⌝ -∗
      lty_wold lt (pctx_get K x₀) dh gh tid l -∗
      vplace_wcloser K ty' K' f x₀ ζm D tid v l E G -∗ Φ #l) -∗
    WP pctx_vexpr K p @ E {{ Φ }}.
  Proof.
    intros Hw. destruct Hw as [ty|ty 𝔅'' ty'' Hnu Hns Hsz|ty Hnu|ty 𝔅'' ty'' Hnu Hns Hsz].
    - intros. iIntros "LFT PROPH UNIQ Gu G £ ⧖ ⧗p Own HΦ".
      iApply (wp_vplace_wacc_same with "LFT PROPH UNIQ Gu G £ ⧖ ⧗p Own"); [done..|].
      iIntros (l dh gh ?) "Pt Gho". iApply ("HΦ" with "[//] [$Pt $Gho]").
    - rename select (PctxVRoot K) into HR.
      destruct K as [| | |? 𝔄'' n K| | | |]; try done; try (exfalso; exact Hnu).
      have ?: PctxNoUniq K by exact Hnu. intros _ _ Hp.
      iIntros "_ _ _ _ G £ ⧖ ⧗p Own HΦ".
      iApply (wp_vplace_wacc_own _ n K (OfTy ty) ty'' with "G ⧖ ⧗p Own");
        [by apply pctx_wown_strong|by rewrite Hsz (lty_size_ty _ ty)|done|done|].
      iIntros (l dh gh [Hdh Hgh]) "L1 Cl". iSimpl in "L1".
      iDestruct "L1" as (? ->) "[Pt Gho]".
      have Hdl: pctx_dlev K = pctx_mode K 0 by apply pctx_dlev_nouniq.
      iDestruct (lc_weaken (pctx_mode K 1) with "£") as "£";
        [simpl in Hdh; rewrite pctx_mode_add; lia|].
      iMod (lc_fupd_elim_laterN with "£ Gho") as "Gho".
      iModIntro. iApply ("HΦ" with "[//] [$Pt $Gho] Cl").
    - rename select (PctxVRoot K) into HR.
      destruct K as [| | |? 𝔄'' n K| | | |]; try done; try (exfalso; exact Hnu).
      have ?: PctxNoUniq K by exact Hnu. intros _ _ Hp.
      iIntros "_ _ _ _ G £ ⧖ ⧗p Own HΦ".
      iApply (wp_vplace_wacc_own _ n K (Moved ty) ty with "G ⧖ ⧗p Own");
        [by apply pctx_wown_same|by rewrite (lty_size_ty _ ty)|done|done|].
      iIntros (l dh gh ?) "L1 Cl !>". iApply ("HΦ" with "[//] L1 Cl").
    - rename select (PctxVRoot K) into HR.
      destruct K as [| | |? 𝔄'' n K| | | |]; try done; try (exfalso; exact Hnu).
      have ?: PctxNoUniq K by exact Hnu. intros _ _ Hp.
      iIntros "_ _ _ _ G £ ⧖ ⧗p Own HΦ".
      iApply (wp_vplace_wacc_own _ n K (Moved ty) ty'' with "G ⧖ ⧗p Own");
        [by apply pctx_wown_strong|by rewrite Hsz (lty_size_ty _ ty)|done|done|].
      iIntros (l dh gh ?) "L1 Cl !>". iApply ("HΦ" with "[//] L1 Cl").
  Qed.
End write_acc.

(** * The rule *)

Section write.
  Context `{!typeG Σ}.

  (** Writing a value of type [ty'] into the leaf [lt] at the hole of [K] ([pctx_wty]: a
      leaf [OfTy ty], of the same type or, along an owned path without sums, of any type of
      the same size; a moved-out leaf [Moved ty] along an owned path, likewise): a typed
      [Store] ([<-{ty_mty ty'}]) at the address of the hole. The old value of an [OfTy]
      leaf is resolved ([lty_wres]). *)
  Lemma type_write_place_instr {𝔅 𝔄 𝔅' 𝔄'} E L I p pb (K: pctx 𝔅 𝔄) `{!PctxNoShr K}
      `{!PctxVRoot K} (lt: lty 𝔅) (ty': type 𝔅') (K': pctx 𝔅' 𝔄') f Φ :
    pctx_wty K lt ty' K' f → lty_wres E L lt Φ → lctx_lft_alive E L (pctx_alv K lt) →
    typed_instr E L I +[p ◁ₗ pctx_plug K lt; pb ◁ᵥ ty']
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
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_ulft K lt])%I as "#Hu".
    { iApply (guards_transitive with "Ghalf"). iApply (guards_transitive with "Alv").
      by iApply pctx_alv_noshr. }
    have HM: D ≤ M by rewrite /M; lia.
    iDestruct (lc_weaken ((3 * D + 5) + (1 + (1 + D * (D + 1))) + 1) with "£")
      as "[[£a [£r £s]] £f]"; [rewrite /advance_credits; nia|].
    iDestruct (invctx_interp_gcells with "I") as "[#GC I]".
    (* The access to the leaf, and its address. *)
    wp_bind (pctx_vexpr K p).
    iApply (wp_vplace_wacc _ K lt ty' K' f with "LFT PROPH UNIQ Hu H1 £a ⧖ ⧗p Own");
      [done|solve_ndisj|done|].
    iIntros (lK dh gh [Hdh Hgh]) "Old Cl".
    wp_bind pb. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->".
    (* Resolve the old value; its bytes. *)
    iCombine "£r £s £f" as "£r".
    iDestruct (lc_weaken (1 + (1 + D * (D + 1)) + 1) with "£r") as "£r"; [lia|].
    iMod (lty_wold_resolve E L lt Φ _ dh gh D with "LFT PROPH UNIQ TIME E Ghalf H2 GC £r Old")
      as "(Obs' & H2 & %bs & Hbs & %Hlen)"; [done|lia|lia|solve_lazyE|].
    (* Write. *)
    iApply wp_fupd.
    iApply (wp_val_cells_store with "[$Hbs $Hcb]");
      [solve_lazyE|done|by rewrite Hlen (pctx_wty_bsize _ _ _ _ _ Hw)|].
    iIntros "!> Hbs".
    (* Close the place at the new value. *)
    iDestruct (cumulative_time_receipt_mono (pctx_dlev K) with "⧗k") as "⧗k"; [lia|].
    iMod (cumulative_persistent_time_receipt with "TIME ⧗k ⧖b") as "#⧖k"; [solve_ndisj|].
    set Dn := D `max` (pctx_dlev K + db).
    iCombine "⧖ ⧖k" as "⧖D".
    rewrite /vplace_wcloser.
    iMod ("Cl" $! b db db Dn with "[%] [] Hbs Gb") as "[Own H1]"; [rewrite /Dn; lia| |].
    { iApply (persistent_time_receipt_mono with "⧖D"). rewrite /Dn. lia. }
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iModIntro. iExists -[(f x₀ b, ζm)]. iFrame "L I".
    iSplitR "Obs Obs'". { iSplit; [|done]. iExists _. by iFrame. }
    iCombine "Obs Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=> π [Hπ HΦ].
    by apply Hπ.
  Qed.
End write.
