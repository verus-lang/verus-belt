(** * Shared borrows of places

  One rule, [type_share_place_instr], borrows shared the leaf at the hole of any place rooted
  at a value ([p ◁ₗ pctx_plug K lt], [vplace.v]), with the instruction [&ˢ (pctx_vexpr K p)]
  ([share], the pointer value of the address of the hole). The contexts are those of the read
  rule ([PctxVRoot], [PctxRead], [typing/place_read.v]): fields, sums, owned pointers, unique
  borrows, shared references and resolved unique borrows, in any order and nesting. What is
  shared, and what becomes of the place, is computed from [K]; the lifetime [α] of the new
  reference [&shr{α} ty] is given, constrained by side conditions:
  - [α] is included in [pctx_blft K] ([pctx_acc.v]): below no shared reference and no
    resolved unique borrow, the enclosing unique borrow lifetimes; otherwise the lifetime of
    the view of the hole below the first shared reference or resolved unique borrow;
  - the shared leaf and the new place type [pctx_sleaf E L K α lt ty lt'] (a computed
    relation, as [pctx_rleaf], with the leaf cases [lty_sleaf]): below no shared reference
    and no resolved unique borrow, an unblocked leaf [OfTy ty] (not the whole referent of a
    unique borrow, whose contents cannot be shared-blocked), whose type outlives [α], with
    [α] alive, becomes shared-blocked, [lt' = ShrBlocked ty α], until [α] ends
    ([unblock_tctx_vplace_shr_deep] of [place_puniq.v]), and a shared-blocked leaf
    [ShrBlocked ty β] with [α ⊑ β] is shared again (unchanged); below a shared reference,
    any leaf [lt], at its folded type, and the place does not change; below a resolved
    unique borrow, an unblocked or shared-blocked ([α ⊑ β]) leaf of its view, or any leaf
    below a shared reference in the view ([pctx_vsleaf]), and the place does not change;
  - the lifetimes to access the hole are alive ([pctx_alv K lt], as for the other place
    rules).

  The first program step (of the address, or the step of [share] itself) gives the credits and, for a
  shared-blocked leaf below a unique borrow, the receipt of the leaf ([lty_nrc]). The proof
  splits [K] as the read access does ([pctx_read_split]): below no shared reference, the access
  [vroot_acc] to the leaf and [ofty_owned_share] ([place_shr.v]); below a shared reference,
  [wp_pshr_open], [wp_pshr_open_root] ([place_pshr.v]); below a resolved unique borrow, the view
  access [wp_view_sacc] (from [view_pctx_acc] of [place_res_ops.v] and [shr_pctx_view]). *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From lrust.lang Require Import proofmode.
From lrust.typing Require Export type ltype lpath pctx_acc vplace place_own shr_bor place_pshr place_read.
From lrust.typing Require Import type_context programs lft_contexts uniq_util uniq_bor own bytes_layout value_ctx product freeable_util place_shr place_puniq place_res place_res_view place_res_ops.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

(** * The shared leaf and the new place *)

Section pctx_share.
  Context `{!typeG Σ}.

  (** The shareable leaves at a lifetime [α], and the new leaf: [b] if the leaf is in the
      owned part of the place (below no resolved unique borrow), where an unblocked leaf
      becomes shared-blocked at [α] (its type outlives [α], and [α] is alive); in a view
      (below a resolved unique borrow) an unblocked leaf is shared at the lifetime of the
      view and does not change; a shared-blocked leaf (at [β ⊒ α]) is shared again. *)
  Inductive lty_sleaf {𝔄} (E: elctx) (L: llctx) (α: lft) :
      bool → lty 𝔄 → type 𝔄 → lty 𝔄 → Prop :=
  | lty_sleaf_ofty ty :
      elctx_sat E L (ty_outlives_E ty α) → lctx_lft_alive E L α →
      lty_sleaf E L α true (OfTy ty) ty (ShrBlocked ty α)
  | lty_sleaf_view ty : lty_sleaf E L α false (OfTy ty) ty (OfTy ty)
  | lty_sleaf_shrblk b ty β :
      lctx_lft_incl E L α β → lty_sleaf E L α b (ShrBlocked ty β) ty (ShrBlocked ty β).

  (** The shareable leaves in a view (below a resolved unique borrow): [lty_sleaf] in the
      view, and any leaf below a shared reference. *)
  Fixpoint pctx_vsleaf {𝔅 𝔄} (E: elctx) (L: llctx) (K: pctx 𝔅 𝔄) (α: lft) :
      lty 𝔅 → type 𝔅 → Prop :=
    match K in pctx 𝔅 𝔄 return lty 𝔅 → type 𝔅 → Prop with
    | PHole => λ lt ty, lty_sleaf E L α false lt ty lt
    | PField _ _ K _ | POwn _ K | PSum _ _ _ K | PUniq _ K => pctx_vsleaf E L K α
    | PShr _ _ => λ lt ty, ty = lty_fold lt
    | PResUniq _ _ => λ _ _, False
    end.

  (** Sharing the leaf [lt] at the hole of [K] at [α] gives [&shr{α} ty] and leaves [lt'] at
      the hole. The hole is not the whole referent of a unique borrow ([PUniq κ PHole]: in
      [Uniq] mode a shared-blocked leaf has no interpretation of its own). *)
  Fixpoint pctx_sleaf {𝔅 𝔄} (E: elctx) (L: llctx) (K: pctx 𝔅 𝔄) (α: lft) :
      lty 𝔅 → type 𝔅 → lty 𝔅 → Prop :=
    match K in pctx 𝔅 𝔄 return lty 𝔅 → type 𝔅 → lty 𝔅 → Prop with
    | PHole => lty_sleaf E L α true
    | PField _ _ K _ | POwn _ K | PSum _ _ _ K => pctx_sleaf E L K α
    | PUniq _ K => match K in pctx _ _ return lty _ → type _ → lty _ → Prop with
        | PHole => λ _ _ _, False | _ => pctx_sleaf E L K α end
    | PShr _ _ => λ lt ty lt', ty = lty_fold lt ∧ lt' = lt
    | PResUniq _ K => λ lt ty lt', pctx_vsleaf E L K α lt ty ∧ lt' = lt
    end.

  Lemma pctx_sleaf_uniq {𝔅 𝔄'} E L κ (K: pctx 𝔅 𝔄') α lt ty lt' :
    pctx_sleaf E L (PUniq κ K) α lt ty lt' →
    pctx_sleaf E L K α lt ty lt' ∧ pctx_uend (PUniq κ K) = pctx_uend K.
  Proof. destruct K; simpl; tauto. Qed.

  Lemma pctx_sleaf_noshr {𝔅 𝔄} E L (K: pctx 𝔅 𝔄) α lt ty lt' :
    pctx_noshr K → pctx_sleaf E L K α lt ty lt' →
    lty_sleaf E L α true lt ty lt' ∧ pctx_uend K = None.
  Proof.
    induction K; simpl; [tauto|auto|auto|auto| |done|done].
    intros [_ HK] H. destruct (pctx_sleaf_uniq E L κ K _ _ _ _ H) as [H' Hu].
    cbn [pctx_uend] in Hu. rewrite Hu. by apply IHK.
  Qed.

  Lemma pctx_sleaf_app {ℭ 𝔅 𝔄} E L (K1: pctx 𝔅 𝔄) (K2: pctx ℭ 𝔅) α lt ty lt' :
    pctx_noshr K1 → pctx_sleaf E L (pctx_app K1 K2) α lt ty lt' → pctx_sleaf E L K2 α lt ty lt'.
  Proof.
    induction K1 as [| | | |? ? κ K1 IHK1| |] in K2 |- *; simpl;
      [done|auto|auto|auto| |done|done].
    intros [_ HK] H. destruct (pctx_sleaf_uniq E L κ _ _ _ _ _ H) as [H' _]. by apply IHK1.
  Qed.

  Lemma pctx_vsleaf_noshr {𝔅 𝔄} E L (K: pctx 𝔅 𝔄) α lt ty :
    pctx_noshr K → pctx_vsleaf E L K α lt ty → lty_sleaf E L α false lt ty lt.
  Proof.
    induction K; simpl; [done|auto|auto|auto| |done|done]. intros [_ HK]. auto.
  Qed.

  Lemma pctx_vsleaf_app {ℭ 𝔅 𝔄} E L (K1: pctx 𝔅 𝔄) (K2: pctx ℭ 𝔅) α lt ty :
    pctx_noshr K1 → pctx_vsleaf E L (pctx_app K1 K2) α lt ty → pctx_vsleaf E L K2 α lt ty.
  Proof.
    induction K1 in K2 |- *; simpl; [done|auto|auto|auto| |done|done]. intros [_ HK]. auto.
  Qed.

  (** The lifetime of the shared view of the hole of [K] in a view at [κ] (below a resolved
      unique borrow): the lifetime of the view of the hole ([pctx_slft]), intersected with
      the lifetime of a shared-blocked leaf (which is shared at both, [view_leaf]). *)
  Definition lty_vslft {𝔄} (κ: lft) (lt: lty 𝔄) : lft :=
    match lt with ShrBlocked _ β => κ ⊓ β | _ => κ end.

  Fixpoint pctx_vslft {𝔅 𝔄} (K: pctx 𝔅 𝔄) (κ: lft) : lty 𝔅 → lft :=
    match K with
    | PHole => λ lt, lty_vslft κ lt
    | PField _ _ K _ | POwn _ K | PSum _ _ _ K => pctx_vslft K κ
    | PUniq κ' K | PResUniq κ' K => pctx_vslft K (κ ⊓ κ')
    | PShr κ' K => λ _, pctx_slft K κ'
    end.

  Lemma pctx_vslft_noshr {𝔅 𝔄} (K: pctx 𝔅 𝔄) κ lt :
    pctx_noshr K → pctx_vslft K κ lt = lty_vslft (pctx_slft K κ) lt.
  Proof.
    induction K in κ, lt |- *; simpl; [done|auto|auto|auto| |done|done]. intros [_ HK]. auto.
  Qed.

  Lemma pctx_vslft_app {ℭ 𝔅 𝔄} (K1: pctx 𝔅 𝔄) (K2: pctx ℭ 𝔅) κ lt :
    pctx_noshr K1 → pctx_vslft (pctx_app K1 K2) κ lt = pctx_vslft K2 (pctx_slft K1 κ) lt.
  Proof.
    induction K1 in K2, κ, lt |- *; simpl; [done|auto|auto|auto| |done|done].
    intros [_ HK]. auto.
  Qed.

  Lemma pctx_vslft_incl {𝔅 𝔄} E L (K: pctx 𝔅 𝔄) κ α lt ty :
    pctx_vsleaf E L K α lt ty → lctx_lft_incl E L α (pctx_slft K κ) →
    lctx_lft_incl E L α (pctx_vslft K κ lt).
  Proof.
    induction K in κ, lt, ty |- *; simpl; intros Hl Hi; [|by eapply IHK..|done|done].
    inversion Hl; subst; [done|]. by apply lctx_lft_incl_intersect.
  Qed.

  Lemma pctx_vloc_app_shr {ℭ 𝔅 𝔄} (K1: pctx (at_locₛ 𝔅) 𝔄) κ (K2: pctx ℭ 𝔅) n x :
    pctx_vloc (pctx_app K1 (PShr κ K2)) n x =
      pctx_loc K2 n (pctx_get K1 x).2 (pctx_get K1 x).1.
  Proof. by rewrite /pctx_vloc pctx_loc_app. Qed.
End pctx_share.

(** * Sharing, by the shape of the context *)

Section share.
  Context `{!typeG Σ}.

  (** Below no shared reference and no resolved unique borrow (below any number of unique
      borrows, the hole in [Owned] mode): the leaf is shared at [α] (included in the
      enclosing borrow lifetimes) and becomes shared-blocked; its value does not change, so
      no reservation is extended. *)
  Lemma type_share_vplace_noshr {𝔅 𝔄} E L I p (K: pctx 𝔅 𝔄) `{!PctxNoShr K} `{!PctxVRoot K}
      (ty: type 𝔅) α :
    pctx_uend K = None → elctx_sat E L (ty_outlives_E ty α) →
    lctx_lft_incl E L α (pctx_blft K) → lctx_lft_alive E L (pctx_alv K (OfTy ty) ⊓ α) →
    typed_instr E L I +[p ◁ₗ pctx_plug K (OfTy ty)] (&ˢ (pctx_vexpr K p))
      (λ w, +[w ◁ᵥ &shr{α} ty; p ◁ₗ pctx_plug K (ShrBlocked ty α)])
      (λ post '-[x], post -[(pctx_vloc K (lty_size (OfTy ty)) x.1, pctx_get K x.1); x]).
  Proof.
    intros Hu Out Inclα Alv tid post mask iκs [x []].
    iIntros "#LFT #TIME #PROPH #UNIQ #E L I [T _] Obs".
    destruct x as [x₀ ζm]. rewrite /share.
    iDestruct "T" as (v Hp) "T". iEval (rewrite vplace_own_open) in "T".
    iDestruct "T" as (D) "(#⧖ & ⧗p & Own)". have Hdl: 1 ≤ pctx_dlev K by apply pctx_vroot_dlev.
    have ?: Closed [] (pctx_vexpr K p).
    { apply pctx_vexpr_closed. by eapply eval_path_closed. }
    iDestruct (Out with "L E") as "#Out".
    iDestruct (elctx_interp_ty_outlives_E with "Out") as "#InclT".
    iDestruct (Inclα with "L E") as "#Inclα".
    iDestruct (Alv with "L E") as "#Alv".
    (* The first step gives the credits and a cumulative time receipt (for the unblocking,
       if the leaf is below a unique borrow, see [lty_nrc]). *)
    iApply (wp_cumulative_time_receipt_linear with "TIME ⧖"); [solve_ndisj|].
    iIntros "⧗". iDestruct (cumulative_time_receipt_sep 1 (S D) with "⧗") as "[⧗c ⧗1]".
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗c ⧖") as "[_ £]";
      [solve_ndisj|].
    iDestruct (cumulative_time_receipt_mono 1 with "⧗1") as "⧗1"; [lia|].
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_ulft K (OfTy ty) ⊓ α])%I as "#Hua".
    { iApply (guards_transitive with "Ghalf"). iApply (guards_transitive with "Alv").
      iApply llftl_incl_glb; [|iApply llftl_intersect_incl_r].
      iApply llftl_incl_trans; [iApply llftl_intersect_incl_l|]. by iApply pctx_alv_noshr. }
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_ulft K (OfTy ty)])%I as "#Hu".
    { iApply (guards_transitive with "Hua"). iApply llftl_intersect_incl_l. }
    iAssert (fractional.half γh &&{↑NllftG}&&> @[α])%I as "#Hα".
    { iApply (guards_transitive with "Hua"). iApply llftl_intersect_incl_r. }
    set y := pctx_get K x₀.
    iDestruct (lc_weaken (pctx_vacc_cred K D + (D + (D + 1))) with "£") as "[£a [£k £s]]";
      [have := pctx_vacc_cred_le K D; rewrite /advance_credits; nia|].
    iMod (vroot_acc K (OfTy ty) with "LFT PROPH UNIQ Hu H1 £a Own")
      as (G' dh gh) "(% & G' & #G'G & -> & %Hdh & H & P & Cl)"; [solve_ndisj|].
    destruct Hdh as (Hdh & Hgh & Hin).
    have Hm := pctx_hmode_le K 0.
    iEval (rewrite (pctx_kind_owned K) //) in "H".
    iEval (rewrite /pctx_vcloser (pctx_kind_owned K) //) in "Cl".
    set mh := pctx_hmode K 0.
    set lK := pctx_vloc K (lty_size (OfTy ty)) x₀.
    iDestruct "H" as (? ->) "[Pt1 Gho1]".
    (* The address of the hole. *)
    iApply wp_fupd. wp_bind (pctx_vexpr K p).
    iApply (wp_wand with "[P G']").
    { iApply (wp_pctx_vptrs _ K (lty_size (OfTy ty)) G' x₀ p True%I with "[G'] P").
      iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->". by iFrame. }
    iIntros (w) "(-> & _ & G' & P)". wp_pure _.
    iDestruct (lc_weaken mh with "£k") as "£k"; [lia|].
    iMod (lc_fupd_elim_laterN with "£k Gho1") as "Gho1".
    (* Share the contents of the leaf. *)
    iMod (ofty_owned_share _ mh with "LFT InclT Hα H2 [£s] Pt1 Gho1") as "(H2 & #Pers & Leaf)";
      [solve_ndisj|..].
    { iApply (lc_weaken with "£s"). lia. }
    iAssert ((@[α] &&{↑NllftG; gh+1}&&> cbytes ty y lK) ∗
      ty.(ty_shr) α y dh gh tid)%I as "#[GPt Shr]".
    { by iDestruct "Leaf" as (? ->) "(#$ & #$ & _)". }
    iMod ("Cl" $! (ShrBlocked ty α) (inl (PlaceIn y)) dh gh D [] 1%Qp True%I
      with "[//] [//] [//] [%] [%] [] ⧖ G' P [] [Leaf]") as "(Own & H1 & _)".
    { intros ??. apply prfn_rsv_in. }
    { lia. }
    { iRight. by iApply (pat_ok_blft with "Inclα"); [apply pctx_no_shr|]. }
    { done. }
    { iIntros "_ !>". by iFrame "Leaf". }
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iModIntro. iExists -[(lK, y); (x₀, ζm)].
    iFrame "L I". iSplit; last first.
    { iApply (proph_obs_impl with "Obs")=> π Hπ. exact Hπ. }
    iSplitR.
    { iExists _. iSplit; [by rewrite eval_path_of_val|].
      rewrite -(val_own_intro_sep _ _ _ _ _ D); [|done|done].
      iFrame "⧖".
      destruct D as [|D']; [lia|].
      iApply (shr_bor_own_intro with "[] Shr Pers"); [lia|lia|].
      iApply (lguards_weaken_later with "GPt"). lia. }
    iSplit; [|done]. iExists _. iSplit; [done|].
    iApply (vplace_own_close with "⧖ [⧗p ⧗1]"); [|done].
    iDestruct (cumulative_time_receipt_sep with "[$⧗p $⧗1]") as "⧗".
    iApply (cumulative_time_receipt_mono with "⧗"). rewrite !lty_vnrc_plug /=.
    destruct (pctx_vne K); lia.
  Qed.

  (** A shared-blocked leaf (at [β]) below no shared reference and no resolved unique borrow
      (in [Owned] mode): it is shared again, at any [α ⊑ β], from its sharing; the place
      does not change. *)
  Lemma type_share_vplace_noshr_shrblk {𝔅 𝔄} E L I p (K: pctx 𝔅 𝔄) `{!PctxNoShr K}
      `{!PctxVRoot K} (ty: type 𝔅) β α :
    pctx_uend K = None → lctx_lft_incl E L α β →
    lctx_lft_alive E L (pctx_alv K (ShrBlocked ty β)) →
    typed_instr E L I +[p ◁ₗ pctx_plug K (ShrBlocked ty β)] (&ˢ (pctx_vexpr K p))
      (λ w, +[w ◁ᵥ &shr{α} ty; p ◁ₗ pctx_plug K (ShrBlocked ty β)])
      (λ post '-[x], post -[(pctx_vloc K (lty_size (ShrBlocked ty β)) x.1, pctx_get K x.1); x]).
  Proof.
    intros Hu Inclα Alv tid post mask iκs [x []].
    iIntros "#LFT #TIME #PROPH #UNIQ #E L I [T _] Obs".
    destruct x as [x₀ ζm]. rewrite /share.
    iDestruct "T" as (v Hp) "T". iEval (rewrite vplace_own_open) in "T".
    iDestruct "T" as (D) "(#⧖ & ⧗p & Own)". have Hdl: 1 ≤ pctx_dlev K by apply pctx_vroot_dlev.
    have ?: Closed [] (pctx_vexpr K p).
    { apply pctx_vexpr_closed. by eapply eval_path_closed. }
    iDestruct (Inclα with "L E") as "#Inclα".
    iDestruct (Alv with "L E") as "#Alv".
    (* The first step gives the credits. *)
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj|].
    iIntros "£ #⧖S".
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_ulft K (ShrBlocked ty β)])%I as "#Hu".
    { iApply (guards_transitive with "Ghalf"). iApply (guards_transitive with "Alv").
      by iApply pctx_alv_noshr. }
    set y := pctx_get K x₀.
    iDestruct (lc_weaken (pctx_vacc_cred K D) with "£") as "£a";
      [have := pctx_vacc_cred_le K D; rewrite /advance_credits; nia|].
    iMod (vroot_acc K (ShrBlocked ty β) with "LFT PROPH UNIQ Hu H1 £a Own")
      as (G' dh gh) "(% & G' & #G'G & -> & %Hdh & H & P & Cl)"; [solve_ndisj|].
    destruct Hdh as (Hdh & Hgh & Hin).
    iEval (rewrite (pctx_kind_owned K) //) in "H".
    iEval (rewrite /pctx_vcloser (pctx_kind_owned K) //) in "Cl".
    set lK := pctx_vloc K (lty_size (ShrBlocked ty β)) x₀.
    iDestruct "H" as (? ->) "(#GPt & #Shr & #Pers & Inh)".
    (* The address of the hole. *)
    iApply wp_fupd. wp_bind (pctx_vexpr K p).
    iApply (wp_wand with "[P G']").
    { iApply (wp_pctx_vptrs _ K (lty_size (ShrBlocked ty β)) G' x₀ p True%I with "[G'] P").
      iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->". by iFrame. }
    iIntros (w) "(-> & _ & G' & P)". wp_pure _.
    (* Close the place unchanged. *)
    iMod ("Cl" $! (ShrBlocked ty β) (inl (PlaceIn y)) dh gh D [] 1%Qp True%I
      with "[//] [//] [//] [%] [%] [] ⧖ G' P [] [Inh]") as "(Own & H1 & _)".
    { intros ??. apply prfn_rsv_in. }
    { lia. }
    { by iLeft. }
    { done. }
    { iIntros "_ !>". iSplit; [|done]. iExists y. by iFrame "GPt Shr Pers Inh". }
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iModIntro. iExists -[(lK, y); (x₀, ζm)].
    iFrame "L I". iSplit; last first.
    { iApply (proph_obs_impl with "Obs")=> π Hπ. exact Hπ. }
    iSplitR.
    { iExists _. iSplit; [by rewrite eval_path_of_val|].
      rewrite -(val_own_intro_sep _ _ _ _ _ D); [|done|done].
      iFrame "⧖".
      destruct D as [|D']; [lia|].
      iAssert (shr_view α ty y dh gh tid lK) as "#(GPt' & Shr' & Pers')".
      { iApply (shr_view_lft_mono with "Inclα"). by iFrame "GPt Shr Pers". }
      iApply (shr_bor_own_intro with "[] Shr' Pers'"); [lia|lia|].
      iApply (lguards_weaken_later with "GPt'"). lia. }
    iSplit; [|done]. iExists _. iSplit; [done|].
    by iApply (vplace_own_close with "⧖ ⧗p").
  Qed.

  (** The shared reference is the root ([p ◁ₗ ShrLty (K2[lt]) κ]): any sub-place, at a
      lifetime included in the lifetime of its view. The place does not change. *)
  Lemma type_share_vplace_pshr_root {ℭ 𝔅} E L I p κ (K2: pctx ℭ 𝔅) (lt: lty ℭ) α :
    lctx_lft_incl E L α (pctx_slft K2 κ) → lctx_lft_alive E L (pctx_alv (PShr κ K2) lt) →
    typed_instr E L I +[p ◁ₗ pctx_plug (PShr κ K2) lt] (&ˢ (pctx_vexpr (PShr κ K2) p))
      (λ v, +[v ◁ᵥ &shr{α} (lty_fold lt); p ◁ₗ pctx_plug (PShr κ K2) lt])
      (λ post '-[x], post -[(pctx_vloc (PShr κ K2) (lty_size lt) x.1,
        pctx_get (PShr κ K2) x.1); x]).
  Proof.
    iIntros (Inclα Alv tid post mask iκs [x []]) "#LFT #TIME #PROPH #UNIQ #E L I (Tp & _) Obs".
    destruct x as [x ζm]. rewrite /share /=.
    iDestruct "Tp" as (v Hp) "Tp". rewrite vplace_own_eq.
    iDestruct "Tp" as (D) "(#⧖ & ⧗p & Own)".
    iDestruct (Inclα with "L E") as "#Inclα".
    iDestruct (Alv with "L E") as "#Alv".
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj|].
    iIntros "£ #⧖S". iApply wp_fupd.
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_salv K2 κ])%I as "#Hs".
    { iApply (guards_transitive with "Ghalf Alv"). }
    iDestruct (lc_weaken (pshr_cred D) with "£") as "£a";
      [have := pshr_cred_step D; lia|].
    wp_bind (pctx_expr K2 p).
    iApply (wp_pshr_open_root _ κ K2 lt (pctx_plug K2 lt) x D tid v p (fractional.half γh)
      with "Hs H1 £a [] Own"); [solve_ndisj|done|done|..].
    { iApply wp_wand; [by iApply wp_eval_path|]. by iIntros (?) "->". }
    iIntros (dh Hdh [Hin2 Hvin]) "H1 Own #V".
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    wp_pure _. iModIntro.
    iExists -[(pctx_loc K2 (lty_size lt) x.2 x.1, pctx_get K2 x.2); (x, ζm)].
    iFrame "L I Obs". iSplitR "Own ⧗p".
    { rewrite tctx_val_val. iExists D. iFrame "⧖". iSplit; [done|].
      destruct D as [|D']; [lia|].
      iDestruct (shr_view_depth_mono _ _ _ _ _ D' (S D') with "V") as "#V'"; [lia|lia|].
      iApply shr_bor_gho_of_view. by iApply (shr_view_lft_mono with "Inclα V'"). }
    iSplit; [|done]. iExists _. iSplit; [done|]. rewrite vplace_own_eq. iExists D. by iFrame.
  Qed.

  (** Below the shared reference at the hole of [K1] (below a root owned pointer or unique
      borrow): [&( *r).f] for [r: &T], [&( **x).0] for [x: &mut &(T, U)], … The place does not
      change; [K1]'s borrows need only be alive during the instruction. *)
  Lemma type_share_vplace_pshr {ℭ 𝔅 𝔄} E L I p (K1: pctx (at_locₛ 𝔅) 𝔄)
      `{!PctxNoShr K1} `{!PctxVRoot K1} κ (K2: pctx ℭ 𝔅) (lt: lty ℭ) α :
    let K := pctx_app K1 (PShr κ K2) in
    lctx_lft_incl E L α (pctx_slft K2 κ) → lctx_lft_alive E L (pctx_alv K lt) →
    typed_instr E L I +[p ◁ₗ pctx_plug K lt] (&ˢ (pctx_vexpr K p))
      (λ v, +[v ◁ᵥ &shr{α} (lty_fold lt); p ◁ₗ pctx_plug K lt])
      (λ post '-[x], post -[(pctx_vloc K (lty_size lt) x.1, pctx_get K x.1); x]).
  Proof.
    intros K Inclα Alv. rewrite /K /share pctx_plug_app pctx_vexpr_app.
    iIntros (tid post mask iκs [x []]) "#LFT #TIME #PROPH #UNIQ #E L I (Tp & _) Obs".
    destruct x as [x₀ ζm]. rewrite pctx_vloc_app_shr pctx_get_app /=.
    iDestruct "Tp" as (v Hp) "Tp". iEval (rewrite vplace_own_open) in "Tp".
    iDestruct "Tp" as (D) "(#⧖ & ⧗p & Own)".
    iDestruct (Inclα with "L E") as "#Inclα".
    iDestruct (Alv with "L E") as "#Alv".
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj|].
    iIntros "£ #⧖S". iApply wp_fupd.
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iAssert (fractional.half γh &&{↑NllftG}&&>
      @[pctx_ulft K1 (ShrLty (pctx_plug K2 lt) κ) ⊓ pctx_salv K2 κ])%I as "#Hus".
    { iApply (guards_transitive with "Ghalf"). iApply (guards_transitive with "Alv").
      by iApply pctx_alv_app_shr. }
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_ulft K1 (ShrLty (pctx_plug K2 lt) κ)])%I
      as "#Hu". { iApply (guards_transitive with "Hus"). iApply llftl_intersect_incl_l. }
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_salv K2 κ])%I as "#Hs".
    { iApply (guards_transitive with "Hus"). iApply llftl_intersect_incl_r. }
    iDestruct (lc_weaken (pshr_cred D) with "£") as "£a";
      [have := pshr_cred_step D; lia|].
    set y := pctx_get K1 x₀.
    wp_bind (pctx_expr K2 _).
    iApply (wp_pshr_open _ K1 κ K2 lt (pctx_plug K2 lt) x₀ ζm D tid _ p (fractional.half γh)
      with "LFT PROPH UNIQ Hu Hs H1 £a ⧖ [] Own"); [solve_ndisj|done|done|..].
    { iApply wp_wand; [by iApply wp_eval_path|]. by iIntros (?) "->". }
    iIntros (dh Hdh [Hin1 [Hin2 Hvin]]) "H1 Own #V".
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    wp_pure _. iModIntro.
    iExists -[(pctx_loc K2 (lty_size lt) y.2 y.1, pctx_get K2 y.2); (x₀, ζm)].
    iFrame "L I Obs". iSplitR "Own ⧗p".
    { rewrite tctx_val_val. iExists D. iFrame "⧖". iSplit; [done|].
      destruct D as [|D']; [lia|].
      iDestruct (shr_view_depth_mono _ _ _ _ _ D' (S D') with "V") as "#V'"; [lia|lia|].
      iApply shr_bor_gho_of_view. by iApply (shr_view_lft_mono with "Inclα V'"). }
    iSplit; [|done]. iExists _. iSplit; [done|]. by iApply (vplace_own_close with "⧖ ⧗p").
  Qed.

  (** ** Sharing in a view

      The shared view of the hole of [K] in the view of a place at [l] (the referent of a
      resolved unique borrow, at [κ]): the access to a sub-place of the view
      ([view_pctx_acc]) down to the hole (an unblocked leaf, shared at the lifetime of the
      view) or to the first shared reference, whose shared view is then pushed through the
      rest of the context ([shr_pctx_view]). The base address [e] is evaluated first; [R] is
      what its evaluation keeps. The view is given back at once. *)
  Lemma wp_view_sacc {ℭ 𝔅} E (K: pctx ℭ 𝔅) `{!PctxRead K} κ (lt: lty ℭ) (ty: type ℭ)
      El Ll α m z ζm q d g tid (l: loc) M (G R: iProp Σ) (e: expr) (Φ: val → iProp Σ) :
    ↑NllftG ⊆ E → Timeless G → pctx_vsleaf El Ll K α lt ty → d ≤ M → g ≤ M →
    let V := lty_view (pctx_plug K lt) κ m (pctx_pat K (lty_pat lt))
      (pctx_rfn K z ζm q (lty_rfn lt (pctx_get K z) ζm (pctx_path K q))) d g tid l in
    (G &&{↑NllftG}&&> @[pctx_salv K κ]) -∗ G -∗ £(view_cred M) -∗ V -∗
    WP e @ E {{ v, ⌜v = #(l)⌝ ∗ R }} -∗
    (∀ dh, ⌜dh ≤ d⌝ -∗
      shr_view (pctx_vslft K κ lt) ty (pctx_get K z) dh M tid (pctx_loc K (lty_size lt) z l) -∗
      R -∗ G -∗ V -∗ Φ #(pctx_loc K (lty_size lt) z l)) -∗
    WP pctx_expr K e @ E {{ Φ }}.
  Proof.
    intros HE ? Hl Hd Hg V. subst V. iIntros "#Gs G £ V WPe HΦ".
    iApply wp_fupd.
    destruct (pctx_read_split K pctx_read_c)
      as [HK|[(𝔅' & κ' & K1 & K2 & -> & HK1)|(𝔅' & κ' & K1 & K2 & -> & HK1 & _ & _)]].
    - (* Below no shared reference: the leaf is shared in the view. *)
      have ?: PctxNoShr K by done.
      have Hl' := pctx_vsleaf_noshr El Ll K α lt ty HK Hl.
      rewrite pctx_vslft_noshr //.
      inversion Hl'; subst.
      + (* An unblocked leaf, shared at the lifetime of the view. *)
        iDestruct (view_pctx_acc K κ (OfTy ty) m (lty_pat (OfTy ty)) _ z ζm q d g tid l G
          with "Gs V") as (dh gh) "([%Hdh [%Hgh %Hin]] & #Vh & #Gp & Cl)".
        iEval (rewrite /= /view_leaf) in "Vh".
        iDestruct "Vh" as (z' ->) "(#Gpt & #Shr & #Pers)".
        iAssert (shr_view (pctx_slft K κ) ty (pctx_get K z) dh M tid
          (pctx_loc K (lty_size (OfTy ty)) z l)) as "#Vs".
        { iApply (shr_view_depth_mono _ _ _ dh gh); [lia|lia|]. by iFrame "Gpt Shr Pers". }
        iDestruct (lc_weaken (2 * (g + 1) * pctx_dlev K) with "£") as "£s";
          [rewrite /view_cred; nia|].
        iApply (wp_pctx_sexpr E K (lty_size (OfTy ty)) (g + 1) G z l e); [done|].
        iApply (wp_wand with "WPe"). iIntros (v) "[-> R]".
        iFrame "Gp £s G". iSplit; [done|]. iIntros "G !>".
        iApply ("HΦ" with "[%] Vs R G"); [lia|].
        iApply ("Cl" $! (OfTy ty) (lty_pat (OfTy ty)) _ dh gh d g with "[//] [//] [//] [%]");
          [lia|].
        rewrite /= /view_leaf. iExists (pctx_get K z). by iFrame "Gpt Shr Pers".
      + (* A shared-blocked leaf (at [β]), shared at the lifetime of the view and [β]. *)
        iDestruct (view_pctx_acc K κ (ShrBlocked ty β) m (lty_pat (ShrBlocked ty β)) _ z ζm q
          d g tid l G with "Gs V") as (dh gh) "([%Hdh [%Hgh %Hin]] & Vh & #Gp & Cl)".
        iEval (rewrite /= /view_leaf) in "Vh".
        iDestruct "Vh" as (z' ->) "(#Gpt & #Shr & #Pers & Inh)".
        iAssert (shr_view (pctx_slft K κ ⊓ β) ty (pctx_get K z) dh M tid
          (pctx_loc K (lty_size (ShrBlocked ty β)) z l)) as "#Vs".
        { iApply (shr_view_depth_mono _ _ _ dh gh); [lia|lia|]. by iFrame "Gpt Shr Pers". }
        iDestruct (lc_weaken (2 * (g + 1) * pctx_dlev K) with "£") as "£s";
          [rewrite /view_cred; nia|].
        iApply (wp_pctx_sexpr E K (lty_size (ShrBlocked ty β)) (g + 1) G z l e); [done|].
        iApply (wp_wand with "WPe"). iIntros (v) "[-> R]".
        iFrame "Gp £s G". iSplit; [done|]. iIntros "G !>".
        iApply ("HΦ" with "[%] Vs R G"); [lia|].
        iApply ("Cl" $! (ShrBlocked ty β) (lty_pat (ShrBlocked ty β)) _ dh gh d g
          with "[//] [//] [//] [%] [Inh]"); [lia|].
        rewrite /= /view_leaf. iExists (pctx_get K z). by iFrame "Gpt Shr Pers Inh".
    - (* Below a shared reference at the hole of [K1] in the view. *)
      have ?: PctxNoShr K1 by done.
      have Hl' := pctx_vsleaf_app El Ll K1 (PShr κ' K2) α lt ty HK1 Hl. simpl in Hl'. subst ty.
      rewrite pctx_plug_app pctx_pat_app pctx_rfn_app pctx_get_app pctx_path_app_ctx
        pctx_expr_app pctx_loc_app pctx_salv_app // pctx_vslft_app // ?pctx_slft_app //.
      cbn [pctx_plug pctx_pat pctx_rfn pctx_get pctx_salv pctx_slft pctx_vslft pctx_expr pctx_loc].
      iDestruct (view_pctx_acc K1 κ (ShrLty (pctx_plug K2 lt) κ') m PatLeaf
        (inl (PlaceIn (pctx_get K1 z))) z ζm q d g tid l G with "[] V")
        as (dh gh) "([%Hdh [%Hgh %Hin]] & Vh & #Gp & Cl)".
      { iApply (guards_transitive with "Gs"). rewrite (pctx_salv_slft_noshr K1) //.
        iApply llftl_intersect_incl_l. }
      set y := pctx_get K1 z. set κh := pctx_slft K1 κ.
      set lh := pctx_loc K1 (lty_size (ShrLty (pctx_plug K2 lt) κ')) z l.
      iDestruct "Vh" as "[Vl %Hvin]". iEval (rewrite /= /view_leaf) in "Vl".
      iDestruct "Vl" as (? ->) "#(Gb & Shr & Pers)".
      simpl in Hvin. have Hvin0 := Hvin. apply lty_vin_plug in Hvin as [Hvin2 _].
      iDestruct (lc_weaken (2 * (g + 1) * pctx_dlev K1 + (dh * (gh + 3) +
        2 * (g + 1) * (M + 1))) with "£") as "(£s & £v & £s2)".
      { rewrite /view_cred. nia. }
      iMod (shr_pctx_view (PShr κ' K2) κh lt y dh gh tid lh G with "[] £v [$Gb $Shr $Pers]")
        as "[#Gp2 (%dh' & %Hdh' & #Vh2)]".
      { simpl. by apply pctx_vin_in. }
      { iExact "Gs". }
      iDestruct (shr_view_depth_mono _ _ _ dh' gh dh' M with "Vh2") as "#Vh2'"; [lia|lia|].
      iApply (wp_pctx_sexpr E (PShr κ' K2) (lty_size lt) (gh + 1) G y lh (pctx_expr K1 e));
        [done|].
      iApply (wp_pctx_sexpr E K1 (lty_size (ShrLty (pctx_plug K2 lt) κ')) (g + 1) G z l e);
        [done|].
      iApply (wp_wand with "WPe"). iIntros (v) "[-> R]".
      iSplit; [done|]. iSplitR; [iExact "Gp"|]. iSplitL "£s"; [iExact "£s"|].
      iSplitL "G"; [iExact "G"|]. iIntros "G".
      iSplit; [done|]. iSplitR; [iExact "Gp2"|].
      iSplitL "£s2"; [iApply (lc_weaken with "£s2"); simpl in *; nia|].
      iSplitL "G"; [iExact "G"|]. iIntros "G !>".
      iApply ("HΦ" with "[%] Vh2' R G"); [simpl in *; lia|].
      iApply ("Cl" $! (ShrLty (pctx_plug K2 lt) κ') PatLeaf (inl (PlaceIn y)) dh gh d g
        with "[//] [//] [//] [%] []"); [lia|].
      rewrite /=. iSplit; [|done]. rewrite /view_leaf. iExists y. by iFrame "Gb Shr Pers".
    - (* A resolved unique borrow in a view: nothing is shareable. *)
      have ?: PctxNoShr K1 by done.
      by have := pctx_vsleaf_app El Ll K1 (PResUniq κ' K2) α lt ty HK1 Hl.
  Qed.

  (** Below a resolved unique borrow at the hole of [K1] (in the owned part of a place rooted
      at an owned location): the pointer of the resolved borrow is loaded, and the hole is
      shared in the view of its referent. The place does not change. *)
  Lemma type_share_vplace_res {ℭ 𝔅 𝔄} E L I p n (K1: pctx (uniq_borₛ 𝔅) 𝔄) `{!PctxNoUniq K1}
      κ (K2: pctx ℭ 𝔅) `{!PctxRead K2} (lt: lty ℭ) (ty: type ℭ) α :
    let K := POwn n (pctx_app K1 (PResUniq κ K2)) in
    pctx_vsleaf E L K2 α lt ty → lctx_lft_incl E L α (pctx_slft K2 κ) →
    lctx_lft_alive E L (pctx_alv K lt) →
    typed_instr E L I +[p ◁ₗ pctx_plug K lt] (&ˢ (pctx_vexpr K p))
      (λ v, +[v ◁ᵥ &shr{α} ty; p ◁ₗ pctx_plug K lt])
      (λ post '-[x], post -[(pctx_vloc K (lty_size lt) x.1, pctx_get K x.1); x]).
  Proof.
    have ?: PctxNoShr K1 by apply _.
    intros K Hl Inclα Alv.
    have Inclα' := pctx_vslft_incl E L K2 κ α lt ty Hl Inclα.
    iIntros (tid post mask iκs [x []]) "#LFT #TIME #PROPH #UNIQ #E L I (Tp & _) Obs".
    destruct x as [[l x₀] ζm]. rewrite /share.
    iDestruct "Tp" as (v Hp) "Tp". iEval (rewrite vplace_own_open) in "Tp".
    iDestruct "Tp" as (D) "(#⧖ & ⧗p & Own)".
    iDestruct (Inclα' with "L E") as "#Inclα".
    iDestruct (Alv with "L E") as "#Alv".
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj|].
    iIntros "£ #⧖S". iApply wp_fupd.
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_salv K2 κ])%I as "#Hs".
    { iApply (guards_transitive with "Ghalf"). iApply (guards_transitive with "Alv").
      iApply llftl_incl_trans; [by iApply (pctx_alv_app K1 (PResUniq κ K2))|].
      iApply llftl_intersect_incl_r. }
    rewrite /K /= pctx_plug_app pctx_expr_app pctx_rfn_app pctx_get_app
      pctx_path_app_ctx /pctx_vloc /= pctx_loc_app /=.
    iDestruct "Own" as (d g -> Hle) "[Fr Own]".
    set lt1 := ResUniqLty (pctx_plug K2 lt) κ.
    rewrite /ltype_own lty_pat_plug ltype_own_plug.
    iDestruct "Own" as "[H Rest]".
    iDestruct (pctx_own_mode_le with "Rest") as %Hk.
    set y := pctx_get K1 x₀.
    set q0 := pctx_path K1 [].
    set lK := pctx_loc K1 (lty_size lt1) x₀ l.
    destruct y as [[[[[ly z] ξi] d0] g0] idx0] eqn:Hy.
    rewrite /= /res_node /=. iDestruct "H" as "[Pt N]".
    iDestruct (lc_weaken (pctx_mode K1 1 + view_cred D) with "£") as "[£m £]";
      [rewrite /advance_credits /view_cred pctx_mode_add; nia|].
    iMod (lc_fupd_elim_laterN with "£m N") as "(#Incl & %d' & %g' & %Hle' & V)".
    rewrite lty_pat_plug.
    have ?: pctx_depth K1 d ≤ d by (rewrite pctx_depth_sub; lia).
    wp_bind (pctx_expr K2 _).
    iApply (wp_view_sacc _ K2 κ lt ty E L α 0 z ζm (false :: q0) d' g' tid ly D (fractional.half γh)
      (ptr_cell lK ly ∗ pctx_own K1 (lty_size lt1) 1 x₀ ζm [] d g tid l)%I
      with "Hs H1 £ V [Pt Rest]"); [solve_ndisj|done|lia|lia|..].
    { wp_bind (pctx_expr K1 p).
      iApply (wp_wand with "[Rest]").
      { iApply (wp_pctx_expr_mask _ K1 (lty_size lt1) 1 x₀ ζm [] d g tid l p True True
          with "[] Rest").
        wp_bind p. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->".
        iFrame; by iPureIntro. }
      iIntros (w) "(-> & _ & _ & Rest)".
      iDestruct "Pt" as (bs) "[Hbs %Hbs]".
      wp_bind (Load _ _ _). iApply (wp_load_na with "Hbs"); [exact Hbs|]. iIntros "!> Hbs".
      iSplit; [done|]. iFrame "Rest". iExists bs. by iFrame. }
    iIntros (dh Hdh) "#Vs [Pt Rest] H1 V".
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    wp_pure _. iModIntro.
    iExists -[(pctx_loc K2 (lty_size lt) z ly, pctx_get K2 z); ((l, x₀), ζm)].
    iFrame "L I Obs". iSplitR "Pt Rest V ⧗p Fr".
    { rewrite tctx_val_val. iExists D. iFrame "⧖". iSplit; [done|].
      destruct D as [|D']; [lia|].
      iDestruct (shr_view_depth_mono _ _ _ _ _ D' (S D') with "Vs") as "#V'"; [lia|lia|].
      iApply shr_bor_gho_of_view. by iApply (shr_view_lft_mono with "Inclα V'"). }
    iSplit; [|done]. iExists _. iSplit; [done|].
    iApply (vplace_own_close (POwn n K1) _ _ _ D with "⧖ ⧗p"). rewrite /=.
    iExists d, g. iSplit; [done|]. iSplit; [done|]. iFrame "Fr".
    rewrite /ltype_own lty_pat_plug lty_rfn_plug ltype_own_plug -/y Hy. iFrame "Rest".
    rewrite /= /res_node /=. iFrame "Pt".
    iApply bi.laterN_intro. iFrame "Incl".
    iExists d', g'. iSplit; [done|]. by rewrite lty_pat_plug.
  Qed.

  (** Below the resolved unique borrow at the root ([p ◁ₗ ResUniqLty (K2[lt]) κ]). *)
  Lemma type_share_vplace_res_root {ℭ 𝔅} E L I p κ (K2: pctx ℭ 𝔅) `{!PctxRead K2} (lt: lty ℭ)
      (ty: type ℭ) α :
    pctx_vsleaf E L K2 α lt ty → lctx_lft_incl E L α (pctx_slft K2 κ) →
    lctx_lft_alive E L (pctx_alv (PResUniq κ K2) lt) →
    typed_instr E L I +[p ◁ₗ pctx_plug (PResUniq κ K2) lt]
      (&ˢ (pctx_vexpr (PResUniq κ K2) p))
      (λ v, +[v ◁ᵥ &shr{α} ty; p ◁ₗ pctx_plug (PResUniq κ K2) lt])
      (λ post '-[x], post -[(pctx_vloc (PResUniq κ K2) (lty_size lt) x.1,
        pctx_get (PResUniq κ K2) x.1); x]).
  Proof.
    intros Hl Inclα Alv.
    have Inclα' := pctx_vslft_incl E L K2 κ α lt ty Hl Inclα.
    iIntros (tid post mask iκs [x []]) "#LFT #TIME #PROPH #UNIQ #E L I (Tp & _) Obs".
    destruct x as [x₀ ζm]. rewrite /share.
    iDestruct "Tp" as (v Hp) "Tp". iEval (rewrite vplace_own_open) in "Tp".
    iDestruct "Tp" as (D) "(#⧖ & ⧗p & Own)".
    iDestruct (Inclα' with "L E") as "#Inclα".
    iDestruct (Alv with "L E") as "#Alv".
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj|].
    iIntros "£ #⧖S". iApply wp_fupd.
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_salv K2 κ])%I as "#Hs".
    { iApply (guards_transitive with "Ghalf Alv"). }
    rewrite /pctx_vloc /=.
    destruct x₀ as [[[[[lx z] ξi] d0] g0] idx0].
    iDestruct "Own" as (d g [Hd Hg]) "[-> (#Incl & %d' & %g' & %Hle' & V)]".
    rewrite lty_pat_plug.
    iDestruct (lc_weaken (view_cred D) with "£") as "£";
      [rewrite /advance_credits /view_cred; nia|].
    wp_bind (pctx_expr K2 _).
    iApply (wp_view_sacc _ K2 κ lt ty E L α 0 z ζm [] d' g' tid lx D (fractional.half γh)
      True%I with "Hs H1 £ V [] [-]"); [solve_ndisj|done|lia|lia|..].
    { wp_bind p. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->". iFrame; by iPureIntro. }
    iIntros (dh Hdh) "#Vs _ H1 V".
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    wp_pure _. iModIntro.
    iExists -[(pctx_loc K2 (lty_size lt) z lx, pctx_get K2 z); (lx, z, ξi, d0, g0, idx0, ζm)].
    iFrame "L I Obs". iSplitR "V ⧗p".
    { rewrite tctx_val_val. iExists D. iFrame "⧖". iSplit; [done|].
      destruct D as [|D']; [lia|].
      iDestruct (shr_view_depth_mono _ _ _ _ _ D' (S D') with "Vs") as "#V'"; [lia|lia|].
      iApply shr_bor_gho_of_view. by iApply (shr_view_lft_mono with "Inclα V'"). }
    iSplit; [|done]. iExists _. iSplit; [done|].
    iApply (vplace_own_close (PResUniq κ K2) _ _ _ D with "⧖ ⧗p"). rewrite /=.
    iExists d, g. iSplit; [done|]. iSplit; [done|]. iFrame "Incl".
    iExists d', g'. iSplit; [done|]. by rewrite lty_pat_plug.
  Qed.
End share.

(** * The rule *)

Section share_rule.
  Context `{!typeG Σ}.

  (** A shared borrow of the leaf [lt] at the hole of [K], in any place rooted at a value, at
      a given lifetime [α]: the shared reference [&shr{α} ty] to the hole, and the place with
      the leaf [lt'] ([pctx_sleaf]: an unblocked leaf of the owned part becomes
      shared-blocked until [α] ends; otherwise the place is unchanged). [α] is included in
      the bound [pctx_blft K] (the enclosing unique borrow lifetimes, or the lifetime of the
      view below a shared reference or a resolved unique borrow), and in the lifetime of a
      shared-blocked leaf ([pctx_sleaf]); the lifetimes to access the hole are alive
      ([pctx_alv]). *)
  Lemma type_share_place_instr {𝔅 𝔄} E L I p (K: pctx 𝔅 𝔄) `{!PctxVRoot K} `{!PctxRead K}
      α (lt: lty 𝔅) (ty: type 𝔅) (lt': lty 𝔅) :
    pctx_sleaf E L K α lt ty lt' → lctx_lft_incl E L α (pctx_blft K) →
    lctx_lft_alive E L (pctx_alv K lt) →
    typed_instr E L I +[p ◁ₗ pctx_plug K lt] (&ˢ (pctx_vexpr K p))
      (λ v, +[v ◁ᵥ &shr{α} ty; p ◁ₗ pctx_plug K lt'])
      (λ post '-[x], post -[(pctx_vloc K (lty_size lt) x.1, pctx_get K x.1); x]).
  Proof.
    intros Hl Incl Alv.
    (* Below no shared reference: an unblocked or a shared-blocked leaf. *)
    have Hnoshr: ∀ K: pctx 𝔅 𝔄, PctxNoShr K → PctxVRoot K →
      pctx_sleaf E L K α lt ty lt' → lctx_lft_incl E L α (pctx_blft K) →
      lctx_lft_alive E L (pctx_alv K lt) →
      typed_instr E L I +[p ◁ₗ pctx_plug K lt] (&ˢ (pctx_vexpr K p))
        (λ v, +[v ◁ᵥ &shr{α} ty; p ◁ₗ pctx_plug K lt'])
        (λ post '-[x], post -[(pctx_vloc K (lty_size lt) x.1, pctx_get K x.1); x]).
    { clear dependent K. intros K ?? Hl Incl Alv.
      destruct (pctx_sleaf_noshr _ _ K _ _ _ _ pctx_no_shr Hl) as [Hl' Hu].
      inversion Hl' as [ty0 Out Alvα| |b ty0 β Inclβ]; subst.
      - apply (type_share_vplace_noshr _ _ _ _ K ty α); [done|done|done|].
        by apply lctx_lft_alive_intersect.
      - by apply (type_share_vplace_noshr_shrblk _ _ _ _ K ty β α). }
    rename select (PctxVRoot K) into HR. rename select (PctxRead K) into HK.
    destruct K as [| |? ? n K| |? ? κ K|? ? κ K|? ? κ K]; try done;
      rewrite /PctxRead /= in HK.
    - destruct (pctx_read_split K HK) as [HK'|[(𝔅' & κ & K1 & K2 & -> & HK1)|
        (𝔅' & κ & K1 & K2 & -> & HK1 & HKu & HK2)]].
      + by apply Hnoshr.
      + have ?: PctxNoShr (POwn n K1) by done.
        have [-> ->] := pctx_sleaf_app _ _ (POwn n K1) (PShr κ K2) _ _ _ _ HK1 Hl.
        rewrite (pctx_blft_app_view (POwn n K1) (PShr κ K2) (pctx_slft K2 κ)) // in Incl.
        by apply (type_share_vplace_pshr _ _ _ _ (POwn n K1) κ K2 lt α).
      + have ?: PctxNoUniq K1 by done. have ?: PctxRead K2 by done.
        have [? ->] := pctx_sleaf_app _ _ (POwn n K1) (PResUniq κ K2) _ _ _ _ HK1 Hl.
        rewrite (pctx_blft_app_view (POwn n K1) (PResUniq κ K2) (pctx_slft K2 κ)) // in Incl.
        by apply (type_share_vplace_res _ _ _ _ n K1 κ K2 lt ty α).
    - destruct HK as [HKs HK].
      destruct (pctx_read_split K HK) as [HK'|[(𝔅' & κ' & K1 & K2 & -> & HK1)|
        (𝔅' & κ' & K1 & K2 & -> & HK1 & _)]].
      + have ?: PctxNoShr (PUniq κ K) by done. by apply Hnoshr.
      + have ?: PctxNoShr (PUniq κ K1).
        { split; [by eapply pctx_simple_app_l|done]. }
        have [-> ->] := pctx_sleaf_app _ _ (PUniq κ K1) (PShr κ' K2) _ _ _ _ pctx_no_shr Hl.
        rewrite (pctx_blft_app_view (PUniq κ K1) (PShr κ' K2) (pctx_slft K2 κ')) // in Incl.
        by apply (type_share_vplace_pshr _ _ _ _ (PUniq κ K1) κ' K2 lt α).
      + exfalso. by apply (pctx_simple_app_not K1 (PResUniq κ' K2)); [intros ?|..].
    - destruct Hl as [-> ->]. by apply (type_share_vplace_pshr_root _ _ _ _ κ K lt α).
    - have ?: PctxRead K by done. destruct Hl as [? ->].
      by apply (type_share_vplace_res_root _ _ _ _ κ K lt ty α).
  Qed.
End share_rule.
