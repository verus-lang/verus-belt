(** * N-ary products in byte places

  [Π! (𝔅 :: 𝔅l)] and [𝔅 * Π! 𝔅l] have different MiniRust types ([seq_tuple] of the
  fields, and a pair whose second field is a tuple), but the same bytes: the bytes of the
  head, then those of the tail ([syn_bytes_xprod_cons], from [syn_iso_bytes] of
  [isoₛ_cons_prod]). So the bytes of a leaf [OfTy (Π! (ty +:: tyl))] are those of the pair
  [OfTy (ty * Π! tyl)] at the converted value ([cbytes_xprod_cons]); its ownership is that
  of the pair ([xprod_ty] is [mod_ty] of the pair).

  [tctx_unfold_oplace_xprod] / [tctx_fold_oplace_xprod] (the byte versions of those of
  [typing/place_own.v]) turn a leaf [OfTy (Π! (ty +:: tyl))] of an owned place into
  [ProdLty (OfTy ty) (OfTy (Π! tyl))] and back; the syntactic type of the hole changes, so
  the context is retyped ([pctx_retype], below no sum) and the value converted
  ([of_cons_prodₛ]/[to_cons_prodₛ]). Unfolding the tail again gives the fields one by one;
  all leaf rules then apply. As in the deleted legacy version, this is for the owned part of a
  place only: below a unique borrow, the folded type of the referent would change. *)

From iris.proofmode Require Import proofmode.
From lrust.lang Require Import proofmode.
From lrust.typing Require Export type ltype lpath pctx_acc vplace place_own.
From lrust.typing Require Import type_context programs lft_contexts uniq_util own bytes_layout value_ctx product mod_ty.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

(** * The bytes of an n-ary product *)

Lemma syn_bytes_alt {𝔄} (x: ~~𝔄) bs :
  syn_bytes x bs ↔ decode_value (syn_mty 𝔄) bs = syn_val x ∧ is_Some (syn_val x).
Proof.
  rewrite /syn_bytes. split.
  - intros (v & Hv & Hd). rewrite Hv Hd. split; [done|by eexists].
  - intros [Hd [v Hv]]. exists v. split; [done|]. by rewrite Hd Hv.
Qed.

Lemma syn_val_cons_prod_some {𝔄 𝔅l} (y: ~~𝔄) (ys: ~~ (Π! 𝔅l)) :
  is_Some (syn_val (𝔄:=𝔄 * Π! 𝔅l) (y, ys)) ↔ is_Some (syn_val (𝔄:=Π! (𝔄 :: 𝔅l)) (y -:: ys)).
Proof.
  set M := mapM id (plist_to_list (pmap (λ _ x0, syn_val x0) ys)).
  change (is_Some (v₀ ← syn_val y; v₁ ← VTuple <$> M; Some (VTuple [v₀; v₁])) ↔
    is_Some (VTuple <$> (v ← syn_val y; vs ← M; Some (v :: vs)))).
  destruct (syn_val y); [|by split; intros [? ?]]. simpl.
  destruct M; simpl; [split; intros; by eexists|by split; intros [? ?]].
Qed.

Lemma syn_bytes_xprod_cons {𝔄 𝔅l} (y: ~~𝔄) (ys: ~~ (Π! 𝔅l)) bs :
  syn_bytes (𝔄:=Π! (𝔄 :: 𝔅l)) (y -:: ys) bs ↔ syn_bytes (𝔄:=𝔄 * Π! 𝔅l) (y, ys) bs.
Proof.
  rewrite !syn_bytes_alt -syn_val_cons_prod_some.
  have Hiso := syn_iso_bytes (f:=to_cons_prodₛ (𝔄:=𝔄) (𝔅l:=𝔅l)) (y, ys) bs.
  simpl in Hiso. rewrite Hiso. done.
Qed.

(** The same for fancy bytes. *)
Lemma syn_fbytes_xprod_cons {𝔄 𝔅l} R (y: ~~𝔄) (ys: ~~ (Π! 𝔅l)) fbs :
  syn_fbytes (𝔄:=Π! (𝔄 :: 𝔅l)) R (y -:: ys) fbs ↔ syn_fbytes (𝔄:=𝔄 * Π! 𝔅l) R (y, ys) fbs.
Proof.
  rewrite /syn_fbytes /syn_bsize.
  set M := mapM id (plist_to_list (pmap (λ _ x0, syn_fval x0) ys)).
  change (syn_mty (Π! (𝔄 :: 𝔅l))) with (seq_tuple (syn_mty 𝔄 :: (syn_mty <$> 𝔅l))).
  change (syn_mty (𝔄 * Π! 𝔅l)) with (seq_tuple [syn_mty 𝔄; seq_tuple (syn_mty <$> 𝔅l)]).
  change (syn_fval (𝔄:=Π! (𝔄 :: 𝔅l)) (y -:: ys)) with
    (FVTuple <$> (fv ← syn_fval y; fvs ← M; Some (fv :: fvs))).
  change (syn_fval (𝔄:=𝔄 * Π! 𝔅l) (y, ys)) with
    (fv₀ ← syn_fval y; fv₁ ← FVTuple <$> M; Some (FVTuple [fv₀; fv₁])).
  rewrite !mty_size_seq_tuple !seq_size_cons seq_size_nil mty_size_seq_tuple.
  destruct (syn_fval y) as [fv|]; simpl; [|split; by intros (_ & ? & ? & _)].
  destruct M as [fvs|]; simpl; [|split; by intros (_ & ? & ? & _)].
  split; intros [Hlen (fv' & [= <-] & Hrep)]; (split; [lia|]); eexists; (split; [done|]).
  - apply frepr_seq_tuple_cons in Hrep as (f1 & f2 & -> & Hl1 & H1 & H2).
    apply frepr_seq_tuple_cons. exists f1, f2. split_and!; [done..|].
    apply frepr_seq_tuple_cons. exists f2, []. rewrite app_nil_r. split_and!; [done| |done|].
    + apply frepr_seq_tuple in H2 as [? _]. by rewrite mty_size_seq_tuple.
    + by apply frepr_seq_tuple_nil.
  - apply frepr_seq_tuple_cons in Hrep as (f1 & f2' & -> & Hl1 & H1 & H2).
    apply frepr_seq_tuple_cons in H2 as (f2 & f3 & -> & _ & H2 & H3).
    apply frepr_seq_tuple_nil in H3 as [-> _]. rewrite app_nil_r.
    apply frepr_seq_tuple_cons. by exists f1, f2.
Qed.

Section xprod.
  Context `{!typeG Σ}.

  Lemma cbytes_xprod_cons {𝔄 𝔅l} (ty: type 𝔄) (tyl: typel 𝔅l) (y: ~~𝔄) (ys: ~~ (Π! 𝔅l)) l :
    cbytes (Π! (ty +:: tyl)) (y -:: ys) l ⊣⊢
      cbytes ty y l ∗ cbytes (Π! tyl) ys (l +ₗ ty_bsize ty).
  Proof.
    rewrite -(cbytes_pair (ty * Π! tyl) ty (Π! tyl)).
    rewrite /cbytes. apply bytes_own_iff.
    - intros R fbs. rewrite !ty_fbytes_syn. apply syn_fbytes_xprod_cons.
    - intros R fbs fv fv' _. rewrite -!ty_fval_eq -!ty_mty_eq. intros Hx Hx'.
      destruct (mcells_xprod_cons y ys fv Hx) as (f0 & f1 & H0 & H1 & ->).
      destruct (mcells_pair (𝔄:=𝔄) (𝔅:=Π! 𝔅l) y ys fv' Hx') as (f0' & f1' & H0' & H1' & ->).
      rewrite H0 in H0'. rewrite H1 in H1'. by simplify_eq.
  Qed.

  Lemma lty_size_xprod_cons {𝔄 𝔅l} (lt: lty 𝔄) (lts: lty (Π! 𝔅l)) (lt': lty (Π! (𝔄 :: 𝔅l))) :
    lty_size (ProdLty lt lts) = lty_size lt'.
  Proof. rewrite /lty_size. exact (syn_iso_bsize_eq (f:=to_cons_prodₛ)). Qed.

  (** A leaf of an n-ary product is a leaf of the pair of its head and its tail. *)
  Lemma xprod_ofty_own m {𝔄 𝔅l} (ty: type 𝔄) (tyl: typel 𝔅l) (y: ~~𝔄) (ys: ~~ (Π! 𝔅l)) d g tid l :
    ltype_own (Owned m) (OfTy (Π! (ty +:: tyl))) (inl (PlaceIn (𝔄:=Π! (𝔄 :: 𝔅l)) (y -:: ys)))
      d g tid l ⊣⊢
    ltype_own (Owned m) (ProdLty (OfTy ty) (OfTy (Π! tyl)))
      (inr (inl (PlaceIn y), inl (PlaceIn (𝔄:=Π! 𝔅l) ys)) : prfn (𝔄 * Π! 𝔅l)) d g tid l.
  Proof.
    rewrite prod_ofty_unfold_own /ltype_own /= /ofty_owned /=. iSplit.
    - iIntros "(%x & -> & Pt & Gho)". iExists (y, ys). iSplit; [done|].
      rewrite cbytes_xprod_cons (cbytes_pair _ ty (Π! tyl)). iFrame.
    - iIntros "(%x & -> & Pt & Gho)". iExists (y -:: ys). iSplit; [done|].
      rewrite cbytes_xprod_cons (cbytes_pair _ ty (Π! tyl)). iFrame.
  Qed.

  Lemma tctx_unfold_oplace_xprod {𝔅 𝔅l 𝔄} E L p n (K: pctx (Π! (𝔅 :: 𝔅l)) 𝔄) `{!PctxNoUniq K}
      (ty: type 𝔅) (tyl: typel 𝔅l) :
    pctx_nosum K →
    tctx_incl E L +[p ◁ₗown{n} pctx_plug K (OfTy (Π! (ty +:: tyl)))]
      +[p ◁ₗown{n} pctx_plug (pctx_retype K (𝔅 * Π! 𝔅l)) (ProdLty (OfTy ty) (OfTy (Π! tyl)))]
      (λ post '-[x], post -[((x.1.1,
        pctx_reset K x.1.2 (of_cons_prodₛ ~~$ₛ (pctx_get K x.1.2))), x.2)]).
  Proof.
    intros Hns. split; [by intros ??? [? []]|].
    iIntros (G tid [[[l x₀] ζm] []] mask post ?) "_ _ _ _ _ $ [T _] Obs".
    iDestruct "T" as (v Hp D d g) "(⧖ & ⧗ & -> & %Hle & Fr & Own)".
    rewrite /ltype_own !lty_pat_plug !lty_rfn_plug !ltype_own_plug.
    iDestruct "Own" as "[H Rest]".
    set y := pctx_get K x₀.
    set y' := (of_cons_prodₛ ~~$ₛ y : ~~ (𝔅 * Π! 𝔅l)).
    iModIntro. iExists -[((l, pctx_reset K x₀ y'), ζm)]. iFrame "Obs". iSplit; [|done].
    rewrite /tctx_elt_interp. iExists (MLitV (VPtr l)). iSplit; [done|]. iExists D, d, g.
    rewrite (lty_nrc_plug_retype K (OfTy (Π! (ty +:: tyl))) (ProdLty (OfTy ty) (OfTy (Π! tyl))))
      //.
    rewrite (lty_size_plug_retype K (OfTy (Π! (ty +:: tyl))) (ProdLty (OfTy ty) (OfTy (Π! tyl))));
      [|done|by rewrite (lty_size_xprod_cons _ _ (OfTy (Π! (ty +:: tyl))))].
    iFrame "⧖ ⧗ Fr". iSplit; [done|]. iSplit; [done|].
    rewrite /ltype_own lty_pat_plug lty_rfn_plug pctx_get_reset ltype_own_plug pctx_own_reset //
      pctx_loc_reset // pctx_mode_retype pctx_depth_retype.
    rewrite (lty_size_xprod_cons (OfTy ty) (OfTy (Π! tyl)) (OfTy (Π! (ty +:: tyl)))).
    iFrame "Rest".
    destruct y as [y1 y2] eqn:Hy.
    rewrite (_: y' = (y1, y2)); [|done].
    iDestruct (xprod_ofty_own with "H") as "H". iExact "H".
  Qed.

  Lemma tctx_fold_oplace_xprod {𝔅 𝔅l 𝔄} E L p n (K: pctx (𝔅 * Π! 𝔅l) 𝔄) `{!PctxNoUniq K}
      (ty: type 𝔅) (tyl: typel 𝔅l) :
    pctx_nosum K →
    tctx_incl E L +[p ◁ₗown{n} pctx_plug K (ProdLty (OfTy ty) (OfTy (Π! tyl)))]
      +[p ◁ₗown{n} pctx_plug (pctx_retype K (Π! (𝔅 :: 𝔅l))) (OfTy (Π! (ty +:: tyl)))]
      (λ post '-[x], post -[((x.1.1,
        pctx_reset K x.1.2 (to_cons_prodₛ ~~$ₛ (pctx_get K x.1.2))), x.2)]).
  Proof.
    intros Hns. split; [by intros ??? [? []]|].
    iIntros (G tid [[[l x₀] ζm] []] mask post ?) "_ _ _ _ _ $ [T _] Obs".
    iDestruct "T" as (v Hp D d g) "(⧖ & ⧗ & -> & %Hle & Fr & Own)".
    rewrite /ltype_own !lty_pat_plug !lty_rfn_plug !ltype_own_plug.
    iDestruct "Own" as "[H Rest]".
    set y := pctx_get K x₀.
    set y' := (to_cons_prodₛ ~~$ₛ y : ~~ (Π! (𝔅 :: 𝔅l))).
    iModIntro. iExists -[((l, pctx_reset K x₀ y'), ζm)]. iFrame "Obs". iSplit; [|done].
    rewrite /tctx_elt_interp. iExists (MLitV (VPtr l)). iSplit; [done|]. iExists D, d, g.
    rewrite (lty_nrc_plug_retype K (ProdLty (OfTy ty) (OfTy (Π! tyl))) (OfTy (Π! (ty +:: tyl))))
      //.
    rewrite (lty_size_plug_retype K (ProdLty (OfTy ty) (OfTy (Π! tyl))) (OfTy (Π! (ty +:: tyl))));
      [|done|by rewrite (lty_size_xprod_cons _ _ (OfTy (Π! (ty +:: tyl))))].
    iFrame "⧖ ⧗ Fr". iSplit; [done|]. iSplit; [done|].
    rewrite /ltype_own lty_pat_plug lty_rfn_plug pctx_get_reset ltype_own_plug pctx_own_reset //
      pctx_loc_reset // pctx_mode_retype pctx_depth_retype.
    rewrite -(lty_size_xprod_cons (OfTy ty) (OfTy (Π! tyl)) (OfTy (Π! (ty +:: tyl)))).
    iFrame "Rest".
    destruct y as [y1 y2] eqn:Hy.
    rewrite (_: y' = y1 -:: y2); [|done].
    iApply xprod_ofty_own. iExact "H".
  Qed.
End xprod.
