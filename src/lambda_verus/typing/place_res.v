(** * Resolving owned places to a readable state

  Resolving a place ([p ◁ₗown{n} lt], [place_own.v]) gives up the unique borrows of its
  owned part (the part below no unique borrow: fields, sums, owned pointers) and learns
  the observations of its leaves, but keeps the place readable: the result is a place
  that can be read (and shared) but not written. See [~/verus-belt-phase3-design.md],
  section "Resolve to a readable state".

  ** Resolved place types ([typing/ltype.v])

  - [OfRes ty]: a leaf whose value has been resolved ([resolve_keep] of [type.v]); it
    holds the cells and the resolved ownership [ty_gho_res] of the value. For a type
    without unique borrows ([ResOwn]) this is the ownership, so [OfRes ty] is converted
    back to [OfTy ty]; [OfRes (&uniq{κ} ty)] is re-read as [ShrLty (OfTy ty) κ] (the
    referent shared at [κ], retyping the leaf); owned pointers and products are
    unfolded structurally.
  - [ResUniqLty lt κ]: an unfolded unique borrow whose prophecy variable has been
    (pre-)resolved: its referent is a _view_ at [κ] ([lty_view]): the unblocked leaves
    are shared at [κ], the blocked leaves keep their inheritances (in borrows at [κ]) and
    are shared at [κ] once they are unblocked; nested unique borrows at [κ'] are views at
    [κ ⊓ κ'] (they are not resolved: their lenders keep them).

  This file: (a) the conversions of resolved leaves. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From lrust.lang Require Import proofmode.
From lrust.typing Require Export type ltype lpath pctx_acc place_own.
From lrust.typing Require Import type_context programs programs_util lft_contexts
  uniq_util uniq_bor product own shr_bor sum type_sum freeable_util place place_shr
  place_resolve place_puniq place_sum place_pshr.
From lrust.util Require Import proph_bor.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

(** * Resolved leaves *)

Section res_leaf.
  Context `{!typeG Σ}.

  (** A resolved leaf whose resolved ownership is its ownership is an unresolved leaf. *)
  Lemma res_leaf_to_ofty m {𝔄} (ty: type 𝔄) `{!ResOwn ty} lr d g tid l :
    ltype_own (Owned m) (OfRes ty) (inl lr) d g tid l ⊢
    ltype_own (Owned m) (OfTy ty) (inl lr) d g tid l.
  Proof.
    rewrite /ltype_own /= /res_leaf /leaf_owned_s /leaf_owned /ofty_owned.
    iIntros "(%x & Rel & Pt & Gho)". iExists x. iFrame "Rel Pt". iNext.
    iDestruct "Gho" as (d' g' [??]) "Gho". rewrite res_own.
    iDestruct (ty_gho_own_depth_mono _ d' g' d g with "Gho") as "[$ _]"; lia.
  Qed.

  (** The resolved ownership of a pair. *)
  Lemma res_leaf_prod_unfold m {𝔄 𝔅} (ty1: type 𝔄) (ty2: type 𝔅) x1 x2 d g tid l :
    ltype_own (Owned m) (OfRes (prod_ty ty1 ty2)) (inl (PlaceIn (𝔄:=𝔄 * 𝔅) (x1, x2))) d g tid l ⊢
    ltype_own (Owned m) (ProdLty (OfRes ty1) (OfRes ty2))
      (inr (inl (PlaceIn x1), inl (PlaceIn x2))) d g tid l.
  Proof.
    rewrite /ltype_own /= /res_leaf /prod_node /=.
    iIntros "(%x & -> & Pt & Gho) /=".
    rewrite heap_cloc_mapsto_fancy_vec_app ty_size_eq. iDestruct "Pt" as "[Pt1 Pt2]".
    iAssert (▷^m (∃ d' g', ⌜d' ≤ d ∧ g' ≤ g⌝ ∗ ty_gho_res ty1 x1 d' g' tid) ∗
      ▷^m (∃ d' g', ⌜d' ≤ d ∧ g' ≤ g⌝ ∗ ty_gho_res ty2 x2 d' g' tid))%I
      with "[Gho]" as "[G1 G2]".
    { rewrite -bi.laterN_sep. iNext. iDestruct "Gho" as (d' g' ?) "[G1 G2]".
      iSplitL "G1"; iExists d', g'; by iFrame. }
    iSplitL "Pt1 G1"; [iExists x1|iExists x2]; iSplit; done || iFrame.
  Qed.

  (** The resolved ownership of an owned pointer below one owned pointer (the root): its
      pointee is a resolved leaf. *)
  Lemma res_leaf_own_unfold1 {𝔄} n (ty: type 𝔄) l' x d g tid l E :
    ltype_own (Owned 1) (OfRes (own_ptr n ty)) (inl (PlaceIn (𝔄:=at_locₛ 𝔄) (l', x))) d g tid l
      ={E}=∗
    ltype_own (Owned 1) (OwnPtrLty n (OfRes ty)) (inr (l', inl (PlaceIn x))) d g tid l.
  Proof.
    rewrite /ltype_own /= /res_leaf /own_node /=.
    iIntros "(%v & -> & Pt & H)". iDestruct "H" as (d' g') "[>[%Hd %Hg] H]".
    destruct d' as [|d']; simpl; [by iMod "H"|].
    iDestruct "H" as "(Pt' & Fr & Gho)".
    iEval (rewrite (heap_cloc_mapsto_fancy_empty l' (ty_phys ty x tid)) ty_size_eq) in "Pt'".
    iMod "Pt'". iModIntro. iFrame "Pt Fr". iSplit; [iPureIntro; lia|]. iExists x.
    iSplit; [done|]. iFrame "Pt'". iNext. iNext. iExists d', g'. iFrame "Gho".
    iPureIntro. lia.
  Qed.

  (** A resolved unique borrow is re-read as a shared reference to its referent, at its
      lifetime (the resolved ownership is the ownership of [&shr{κ} ty] at the current
      value of the referent). *)
  Lemma res_leaf_uniq_to_shr m {𝔄} κ (ty: type 𝔄) (y: ~~ (uniq_borₛ 𝔄)) d g tid l :
    ltype_own (Owned m) (OfRes (&uniq{κ} ty)) (inl (PlaceIn y)) d g tid l ⊢
    ltype_own (Owned m) (ShrLty (OfTy ty) κ)
      (inl (PlaceIn (𝔄:=at_clocₛ 𝔄) (uniq_bor_loc y, uniq_bor_current y))) d g tid l.
  Proof.
    rewrite /ltype_own /= /res_leaf /leaf_owned_s /leaf_owned /ofty_owned /=.
    iIntros "(%x & -> & Pt & Gho)". destruct y as [[[[[l0 x0] ξi] d0] g0] idx].
    iSplit; [|done]. iExists (l0, x0). iSplit; [done|]. iFrame "Pt". iNext.
    iDestruct "Gho" as (d' g' [??]) "(#In & %Hle & #Gc & #Gp & #Shr & #Pers)".
    destruct d as [|d]; [lia|]. simpl. iSplit.
    - iApply guard_cloc_combine_fancy.
      + iApply (lguards_weaken_later with "Gc"). lia.
      + iApply (lguards_weaken_later with "Gp"). lia.
    - iSplit; [iApply (ty_shr_depth_mono with "Shr"); lia|].
      iNext. iApply (ty_gho_pers_depth_mono with "Pers"); lia.
  Qed.
End res_leaf.

(** * (a) Conversions of resolved leaves (in the owned part of a place) *)

Section res_conv.
  Context `{!typeG Σ}.

  (** A resolved leaf of a type without unique borrows ([ResOwn]) is an unresolved leaf
      (e.g. [&shr{κ} ty], [own_ptr n int], products of such types). *)
  Lemma tctx_oplace_res_to_ofty {𝔅 𝔄} E L p n (K: pctx 𝔅 𝔄) `{!PctxNoUniq K}
      (ty: type 𝔅) `{!ResOwn ty} :
    tctx_incl E L +[p ◁ₗown{n} pctx_plug K (OfRes ty)] +[p ◁ₗown{n} pctx_plug K (OfTy ty)]
      (λ post '-[x], post -[x]).
  Proof.
    apply (tctx_oplace_change_hole _ _ _ _ K); [done|done|].
    iIntros (y ζm q d g tid l) "H !>". by iApply res_leaf_to_ofty.
  Qed.

  (** A resolved pair is a pair of resolved leaves. *)
  Lemma tctx_unfold_oplace_res_prod {𝔅1 𝔅2 𝔄} E L p n (K: pctx (𝔅1 * 𝔅2) 𝔄) `{!PctxNoUniq K}
      (ty1: type 𝔅1) (ty2: type 𝔅2) :
    tctx_incl E L +[p ◁ₗown{n} pctx_plug K (OfRes (ty1 * ty2))]
      +[p ◁ₗown{n} pctx_plug K (ProdLty (OfRes ty1) (OfRes ty2))] (λ post '-[x], post -[x]).
  Proof.
    apply (tctx_oplace_change_hole _ _ _ _ K); [done|done|].
    iIntros ([y1 y2] ??????) "H !>". by iApply res_leaf_prod_unfold.
  Qed.

  (** A resolved owned pointer (below the root only, as [tctx_unfold_oplace_own]): its
      pointee is resolved. *)
  Lemma tctx_unfold_oplace_res_own {𝔅 𝔄} E L p n' (K: pctx (at_locₛ 𝔅) 𝔄) `{!PctxNoUniq K}
      n (ty: type 𝔅) :
    pctx_mode K 1 = 1%nat →
    tctx_incl E L +[p ◁ₗown{n'} pctx_plug K (OfRes (own_ptr n ty))]
      +[p ◁ₗown{n'} pctx_plug K (OwnPtrLty n (OfRes ty))] (λ post '-[x], post -[x]).
  Proof.
    intros Hm. apply (tctx_oplace_change_hole _ _ _ _ K); [done|done|].
    iIntros ([l' y] ??????) "H". rewrite Hm. by iApply res_leaf_own_unfold1.
  Qed.

  (** A resolved unique borrow is re-read as a shared reference at its lifetime, whose
      referent is its current referent: [OfRes (&uniq{κ} ty)] becomes [ShrLty (OfTy ty) κ]
      (retyping the leaf, below no sum). *)
  Lemma tctx_oplace_res_uniq_to_shr {𝔅 𝔄} E L p n (K: pctx (uniq_borₛ 𝔅) 𝔄) `{!PctxNoUniq K}
      κ (ty: type 𝔅) :
    pctx_nosum K →
    tctx_incl E L +[p ◁ₗown{n} pctx_plug K (OfRes (&uniq{κ} ty))]
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
    rewrite /tctx_elt_interp. iExists #l. iSplit; [done|]. iExists D, d, g.
    rewrite (lty_nrc_plug_retype K (OfRes (&uniq{κ} ty)) (ShrLty (OfTy ty) κ)) //.
    rewrite (lty_size_plug_retype K (OfRes (&uniq{κ} ty)) (ShrLty (OfTy ty) κ)); [|done|done].
    iFrame "⧖ ⧗ Fr". iSplit; [done|]. iSplit; [done|].
    rewrite /ltype_own lty_pat_plug lty_rfn_plug pctx_get_reset ltype_own_plug pctx_own_reset //
      pctx_loc_reset // pctx_mode_retype pctx_depth_retype. iFrame "Rest".
    rewrite (_: lty_size (ShrLty (OfTy ty) κ) = lty_size (OfRes (&uniq{κ} ty))); [|done].
    by iApply res_leaf_uniq_to_shr.
  Qed.

  (** A resolved shared reference is a shared reference ([ResOwn]); unfolded. *)
  Lemma tctx_unfold_oplace_res_shr {𝔅 𝔄} E L p n (K: pctx (at_clocₛ 𝔅) 𝔄) `{!PctxNoUniq K}
      κ (ty: type 𝔅) :
    tctx_incl E L +[p ◁ₗown{n} pctx_plug K (OfRes (&shr{κ} ty))]
      +[p ◁ₗown{n} pctx_plug K (ShrLty (OfTy ty) κ)] (λ post '-[x], post -[x]).
  Proof.
    apply (tctx_oplace_change_hole _ _ _ _ K); [done|done|].
    iIntros (y ζm q d g tid l) "H !>". iDestruct (res_leaf_to_ofty with "H") as "H".
    rewrite /ltype_own /=. by iFrame.
  Qed.
End res_conv.
