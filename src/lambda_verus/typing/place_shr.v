(** * Shared borrows of places, and places below shared references

  ** Shared borrows of a place

  A leaf [OfTy ty] of a place can be borrowed shared at a lifetime [α] (as RefinedRust's
  [type_borrow_shr]; the rule is [type_share_place_instr] of [place_share.v], for any place):
  its points-to and its ownership predicate are borrowed at [α], the borrow of the
  points-to becomes a guard and the borrow of the ownership predicate is shared
  ([ofty_owned_share]: [ty_share], whose steps are paid with later credits of the
  instruction). The leaf becomes _shared-blocked_, [ShrBlocked ty α] ([shr_blocked_owned]
  in [ltype.v]): its value does not change, it keeps the (persistent) sharing information,
  so that it can still be read ([type_read_place_instr] of [place_read.v]), and the
  inheritance of the borrow, which gives back the points-to and the ownership predicate
  once [α] has ended ([unblock_tctx_oplace_shr]; below unique borrows,
  [unblock_tctx_vplace_shr_deep] of [place_puniq.v]).

  ** Places below shared references

  The ownership of [&shr{κ} ty] is persistent, so the place type of the referent of a
  shared reference never changes: there is nothing to block or unblock, and no place
  element (nor a [Shared] borrow kind of [ltype_own]) is needed. A subplace below a
  shared reference is given by a place context [K] (whose siblings are only used for
  their folded types); [tctx_shr_place] gives a shared reference to the subplace at the
  hole of [K] (fields of nested products), from the structural sharing predicate of
  products; reads below a shared reference are [type_read_place_instr] ([place_read.v]).
  Owned pointers and unique borrows below a shared reference are
  traversed by the existing rules [type_deref_shr_own_instr] and
  [type_deref_shr_uniq_instr] (from their structural sharing predicates). *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From lrust.lang Require Import proofmode.
From lrust.typing Require Export type ltype lpath place_own shr_bor.
From lrust.typing Require Import type_context programs lft_contexts uniq_util uniq_bor own bytes_layout value_ctx product.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section place_shr.
  Context `{!typeG Σ}.

  (** * Sharing the contents of a leaf *)

  (** The contents of a leaf (its points-to and its ownership predicate) are borrowed
      at [α] and shared; the leaf becomes shared-blocked. [ty_share] takes [d] steps,
      paid with later credits. *)
  Lemma ofty_owned_share {𝔄} E m (ty: type 𝔄) α x d g tid (l: loc) G :
    Timeless G → lazyE ⊆ E →
    llft_ctx -∗ α ⊑ ty_lft ty -∗ (G &&{↑NllftG}&&> @[α]) -∗ G -∗ £(d + 1) -∗
    cbytes ty x l -∗ ty.(ty_gho_own) x d g tid ={E}=∗
      G ∗ ty.(ty_gho_pers) x d g tid ∗
      leaf_owned_s false m ty (PatShrBlocked α) (inl (PlaceIn x)) d g tid l.
  Proof.
    iIntros (? HE) "#LFT #Incl #Gα G [£d £1] Pt Gho".
    have ?: ↑Nllft ⊆ E. { trans lazyE; [rewrite /lazyE; solve_ndisj|done]. }
    iDestruct (ty_gho_pers_impl with "Gho") as "#Pers".
    iMod (llftl_borrow _ α (cbytes ty x l ∗ ty.(ty_gho_own) x d g tid)
      with "LFT [Pt Gho]") as "[Bor Inh]"; [done|by iFrame|].
    iMod (llftl_sep_split with "LFT Bor") as "[BorPt BorGho]"; [done|].
    iMod (llftl_bor_guard with "LFT BorPt") as "#GPt"; [done|].
    iMod (ty_share with "LFT Incl Pers Gα G BorGho") as "Upd"; [done..|].
    iMod (lc_step_fupdN_elim_later with "£d Upd") as ">[$ #Shr]".
    iModIntro. iSplitR; [done|]. rewrite /= /shr_blocked_owned. iExists x.
    iSplitR; [done|]. iSplitR; [iApply (lguards_weaken_later with "GPt"); lia|].
    iFrame "Shr Pers". iIntros "#†α".
    iMod (fupd_mask_mono with "(Inh †α)") as "Pl"; [rewrite /lazyE; solve_ndisj|].
    iMod (lc_fupd_elim_later with "£1 Pl") as "[$ Gho]". iModIntro. by iNext.
  Qed.

  Lemma pat_ok_shr_blocked κ α : α ⊑ κ -∗ pat_ok κ (PatShrBlocked α).
  Proof. rewrite /pat_ok /=. iIntros "$". Qed.

  (** The sharing predicate of [&shr{α} ty] at depth [S d'], from the guard of the
      points-to and the sharing and persistent predicates of [ty] at [d' g'], with
      [d' ≤ d'' ≤ D] and [g' ≤ D]. *)
  Lemma shr_bor_own_intro {𝔄} α (ty: type 𝔄) (l: loc) x d g D tid :
    d ≤ D → g ≤ S D →
    (@[α] &&{↑NllftG; S D + 1}&&> cbytes ty x l) -∗
    ty.(ty_shr) α x d g tid -∗ ty.(ty_gho_pers) x d g tid -∗
    (&shr{α} ty).(ty_gho_own) (l, x) (S D) (S D) tid.
  Proof.
    iIntros (??) "#Pt #Shr #Pers". rewrite /= /by_succ. iFrame "Pt". iSplit.
    - iApply (ty_shr_depth_mono with "Shr"); lia.
    - iNext. iApply (ty_gho_pers_depth_mono with "Pers"); lia.
  Qed.
End place_shr.

Section typing.
  Context `{!typeG Σ}.

  (** * Unblocking a shared-blocked leaf of a place rooted at an owned location *)

  Lemma unblock_tctx_oplace_shr {𝔅 𝔄 𝔄l 𝔄l'} p n α (K: pctx 𝔅 𝔄) `{!PctxNoUniq K} (ty: type 𝔅)
      (T: tctx 𝔄l) (T': tctx 𝔄l') E L f :
    unblock_tctx E L α T T' f →
    unblock_tctx E L α (p ◁ₗown{n} pctx_plug K (ShrBlocked ty α) +:: T)
      (p ◁ₗown{n} pctx_plug K (OfTy ty) +:: T')
      (λ π '(x -:: xl), λ '(x' -:: xl'), x' = x ∧ f π xl xl').
  Proof.
    iIntros (Un G tid [x xl] ?) "#LFT #TIME #PROPH #UNIQ #E #L G #†α /=[(%v & %Hp & Own) T]".
    destruct x as [[l x₀] ζm].
    iDestruct "Own" as (D d g) "(#⧖0 & ⧗ & -> & %Hle & Fr & Own)".
    iMod (Un with "LFT TIME PROPH UNIQ E L G †α T") as (dT xl') "[#⧖T ToT']".
    rewrite /ltype_own lty_pat_plug lty_rfn_plug ltype_own_plug.
    iDestruct "Own" as "[L1 Rest]".
    iDestruct (unblock_shr_blocked_owned (pctx_mode K 1) ty α with "†α L1") as "L1".
    iMod (fupd_mask_mono with "L1") as "L1"; [rewrite /lazyE; solve_ndisj|].
    iModIntro. iExists dT, (((l, x₀), ζm) -:: xl'). iSplitR; [done|].
    iApply (step_fupd_wand with "ToT'"). iIntros "ToT'".
    iApply (step_fupdN_wand with "ToT'"). iIntros ">(G & T' & #Obs')".
    iModIntro. iFrame "G T'". iSplitR "Obs'".
    { rewrite /tctx_elt_interp. iExists (MLitV (VPtr l)). iSplit; [done|]. iExists D, d, g.
      iFrame "⧖0". rewrite (lty_size_plug_eq K (OfTy ty) (ShrBlocked ty α)) //
        -(lty_nrc_plug_shr_nouniq K ty α).
      iFrame "⧗ Fr". iSplit; [done|]. iSplit; [done|].
      rewrite /ltype_own lty_pat_plug lty_rfn_plug ltype_own_plug /=. iFrame "Rest L1". }
    iApply (proph_obs_impl with "Obs'")=> π Hf. by split.
  Qed.
End typing.

(* [shr_pctx_split] and [tctx_shr_place] of the deleted legacy [place_shr.v] (subplaces of
   a folded shared place) are not ported as separate rules: they are subsumed by
   [type_share_place_instr] of [typing/place_share.v] and by the field projections
   below. *)

(** * Fields of shared references to bytes

The referent of [&shr{κ} (ty1 * ty2)] is the bytes of [ty1] followed by those of [ty2]
([cbytes_pair]), so a shared reference to a field is the shared reference at the offset
of the field (a pointer offset, no load); together with the shared places of
[typing/place_pshr.v], this replaces the reads below shared references of the legacy
layer. *)
Section shr_bytes_fields.
  Context `{!typeG Σ}.

  Lemma type_shr_bytes_snd_instr {𝔄 𝔅} κ (ty1: type 𝔄) (ty2: type 𝔅) p E L I :
    typed_instr E L I +[p ◁ᵥ &shr{κ} (ty1 * ty2)] (p +ₗ #(ty_bsize ty1))%E
      (λ v, +[v ◁ᵥ &shr{κ} ty2])
      (λ post '-[a], post -[((a.1 +ₗ ty_bsize ty1), a.2.2)]).
  Proof.
    iIntros (tid post mask iκs [[l [x1 x2]] []]) "_ _ _ _ _ $ $ [p _] Obs".
    wp_bind p. iApply (wp_val with "p"). iIntros (w d Hp Hw) "#⧖ #Own".
    simpl in Hw. simplify_eq. wp_op.
    iExists -[((l +ₗ ty_bsize ty1), x2)]. iFrame "Obs". iSplit; [|done].
    rewrite tctx_val_val. iExists d. iFrame "⧖". iSplit; [done|].
    destruct d as [|d]; [done|]. rewrite /= /by_succ.
    iDestruct "Own" as "(#Pt & [_ Shr] & [_ Pers])". iFrame "Shr Pers".
    rewrite /shr_bytes_own (bytes_own_pair _ ty1 ty2). by iApply (guards_weaken_rhs_sep_r with "Pt").
  Qed.

  Lemma type_shr_bytes_fst_instr {𝔄 𝔅} κ (ty1: type 𝔄) (ty2: type 𝔅) p E L I :
    typed_instr E L I +[p ◁ᵥ &shr{κ} (ty1 * ty2)] (p)
      (λ v, +[v ◁ᵥ &shr{κ} ty1])
      (λ post '-[a], post -[(a.1, a.2.1)]).
  Proof.
    iIntros (tid post mask iκs [[l [x1 x2]] []]) "_ _ _ _ _ $ $ [p _] Obs".
    wp_bind p. iApply (wp_val with "p"). iIntros (w d Hp Hw) "#⧖ #Own".
    simpl in Hw. simplify_eq. wp_value_head.
    iExists -[(l, x1)]. iFrame "Obs". iSplit; [|done].
    rewrite tctx_val_val. iExists d. iFrame "⧖". iSplit; [done|].
    destruct d as [|d]; [done|]. rewrite /= /by_succ.
    iDestruct "Own" as "(#Pt & [Shr _] & [Pers _])". iFrame "Shr Pers".
    rewrite /shr_bytes_own (bytes_own_pair _ ty1 ty2). by iApply (guards_weaken_rhs_sep_l with "Pt").
  Qed.
End shr_bytes_fields.
