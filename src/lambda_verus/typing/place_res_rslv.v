(** * Resolving an owned place to a readable state

  [lty_res E L lt lt' k Φ]: the [Owned m] interpretation of [lt] is resolved, with [k]
  batches of later credits (one per program step, [ctask]), to the readable place type
  [lt'] (at the same value and blocking map), learning [Φ]. Instances per constructor
  (the mappings [R] and [S_κ] of the design):
  - [lty_res_id]: any place is unchanged (nothing learnt);
  - [lty_res_ofty]: a leaf [OfTy ty] becomes [OfRes ty], with [Φ] from [resolve_keep]
    (for any type, with nothing learnt, by [resolve_keep_just]);
  - [lty_res_copy]: a [Copy] leaf is kept as it is, with [Φ] from [resolve];
  - [lty_res_prod], [lty_res_own], [lty_res_sum]: structural;
  - [lty_res_uniq_leaf], [lty_res_uniq_cpd]: an unfolded unique borrow [UniqLty lt κ]
    becomes [ResUniqLty lt κ]: its prophecy variable is resolved to the denotation of its
    referent (the final values of the reborrows at the blocked leaves, through the
    reservation; the current values at the unblocked leaves, whose prophecy tokens are
    guarded by their sharing at [κ]), and the referent is shared at [κ] into its view
    ([lty_share_view]).

  The rule [type_resolve_oplace_res_instr] takes [k] program steps ([skipn k]). See
  [~/verus-belt-phase3-design.md], section "Resolve to a readable state". *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From lrust.lang Require Import proofmode.
From lrust.util Require Import update.
From lrust.typing Require Export type ltype lpath pctx_acc place_own.
From lrust.typing Require Import type_context programs programs_util lft_contexts
  uniq_util uniq_bor product own shr_bor sum type_sum freeable_util place place_shr
  place_resolve place_puniq place_sum place_pshr place_res place_res_view.
From lrust.util Require Import proph_bor.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

(** * Resolving a reserved prophetic borrow by sharing its contents *)

Section resolve_share_rsv.
  Context `{!typeG Σ}.

  (** As [proph_idx_bor_gen_resolve_share], for a reserved observer: the prophecy
      variable is resolved to [uπ], which may depend on the reserved [ζl] and on [ηl],
      whose tokens are guarded by the sharing of the contents ([Share]). *)
  Lemma proph_idx_bor_gen_resolve_share_rsv E κ κs ξ x idx ζl
      (P: pv_val ξ → pv_proph ξ → iProp Σ) (uπ: pv_proph ξ) (P0 S: iProp Σ) G n :
    Timeless G → ↑Nllft ∪ ↑prophN ∪ ↑uniqN ⊆ E →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ ⊓ κs]) -∗
    (∀ wπ, ▷ P x wπ -∗ ◇ (▷ P0 ∗ ▷ (P0 -∗ P x uπ))) -∗
    (∀ (H: iProp Σ), ⌜Timeless H⌝ -∗ (H &&{↑NllftG}&&> @[κ ⊓ κs]) -∗ H -∗ &{κ} P0 ={E}=∗
       H ∗ S ∗ £ n ∗ ∃ ηl, ⌜uπ ./ ζl ++ ηl⌝ ∗
         (∀ η, ⌜η ∈ ηl⌝ -∗ (H &&{↑NllftG; n}&&> 1:[η]))) -∗
    G -∗ proph_bor_tok_rsv ξ x idx ζl -∗ proph_idx_bor_gen κ ξ idx P ={E}=∗
      ⟨π, π ξ = uπ π⟩ ∗ G ∗ S.
  Proof.
    iIntros (Ti ?) "#LFT #PROPH #UNIQ #Gks Pin Share G Tok #IBor".
    iAssert (G &&{↑NllftG}&&> @[κ])%I as "#Gk".
    { iApply (guards_transitive with "Gks"). iApply llftl_intersect_incl_l. }
    rewrite proph_bor_tok_rsv_unfold. iDestruct "Tok" as "[Vo Tok]".
    iDestruct (llftl_bor_idx_to_full with "IBor Tok") as "Bor".
    iMod (llftl_bor_acc_guarded with "LFT Bor Gk G") as "[Body Back]"; [solve_ndisj|].
    iMod (bi.later_exist_except_0 with "Body") as (x') "Body".
    iMod (bi.later_exist_except_0 with "Body") as (wπ) "(Pc & P)".
    iMod (uniq_rsv_strip_later with "Vo Pc") as "(<- & Vo & Pc)".
    iMod ("Pin" with "P") as "[P0 Inv]".
    iMod (uniq_rsv_update ξ ζl x uπ with "UNIQ Vo Pc") as "[Vo Pc]".
    { pose proof (nclose_subseteq Nllft 0). solve_ndisj. }
    iMod (fupd_mask_subseteq (↑Nllft)) as "Upd"; [solve_ndisj|].
    iMod ("Back" $! (.PC[ξ] x uπ ∗ P0)%I with "[Pc P0 Inv]") as "[Bor G]".
    { iSplitR "Pc P0"; [|iNext; iFrame]. iNext. iIntros "[Pc P0]". iModIntro. iNext.
      iExists x, uπ. iFrame. by iApply "Inv". }
    iMod "Upd" as "_".
    iMod (llftl_sep_split with "LFT Bor") as "[PcBor PBor]"; [solve_ndisj|].
    iMod (fractional.frac_split_guard_in_half with "G Gks") as (γ) "[H1 [H2 [#Ghs #Halfback]]]".
    { solve_ndisj. }
    iAssert (fractional.half γ &&{↑NllftG}&&> @[κ])%I as "#Gh".
    { iApply (guards_transitive with "Ghs"). iApply llftl_intersect_incl_l. }
    iMod ("Share" with "[%] Ghs H1 PBor") as "(H1 & $ & £ & %ηl & %Hdep & #Deps)"; [apply _|].
    iMod (llftl_bor_acc_guarded with "LFT PcBor Gh H2") as "[Pc Back]"; [solve_ndisj|].
    iMod (uniq_rsv_strip_later with "Vo Pc") as "(_ & Vo & Pc)".
    iMod (uniq_resolve_reserved_guarded with "Deps UNIQ PROPH Vo Pc H1") as "X";
      [pose proof (nclose_subseteq Nllft 0); solve_ndisj|done|].
    iMod (lc_fupd_elim_laterN with "£ X") as "X". iMod "X" as "(Obs & Pc & H1)".
    iMod (fupd_mask_subseteq (↑Nllft)) as "Upd"; [solve_ndisj|].
    iMod ("Back" $! (.PC[ξ] x uπ)%I with "[Pc]") as "[_ H2]".
    { iSplitR "Pc"; [|by iNext]. iIntros "!> Pc". by iModIntro. }
    iMod "Upd" as "_".
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "$"; [solve_ndisj|].
    by iFrame "Obs".
  Qed.
End resolve_share_rsv.

(** * The resolution judgement *)

Definition lty_res `{!typeG Σ} {𝔄} (E: elctx) (L: llctx) (lt lt': lty 𝔄) (k: nat)
    (Φ: ~~𝔄 → blk_map → lpath → proph_asn → Prop) : Prop :=
  lty_size lt' = lty_size lt ∧ lty_nrc lt' = lty_nrc lt ∧
  ∀ G m x ζm q d g D tid l, Timeless G → m + d ≤ D → g ≤ D →
    ⊢ llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ time_ctx -∗ elctx_interp E -∗
      (G &&{↑NllftG}&&> llctx_interp L) -∗ G -∗ ⧖D -∗
      ltype_own (Owned m) lt (lty_rfn lt x ζm q) d g tid l -∗
      ctask (advance_credits D) k
        (⟨π, Φ x ζm q π⟩ ∗ G ∗ ltype_own (Owned m) lt' (lty_rfn lt' x ζm q) d g tid l).

Section lty_res.
  Context `{!typeG Σ}.

  (** Any place may be kept as it is. *)
  Lemma lty_res_id {𝔄} E L (lt: lty 𝔄) : lty_res E L lt lt 0 (λ _ _ _ _, True).
  Proof.
    split; [done|]. split; [done|].
    iIntros (G m x ζm q d g D tid l ???) "_ _ _ _ _ _ $ _ $ /=". iModIntro.
    by iApply proph_obs_true.
  Qed.

  Lemma lty_res_impl {𝔄} E L (lt lt': lty 𝔄) k Φ Φ' :
    lty_res E L lt lt' k Φ → (∀ x ζm q π, Φ x ζm q π → Φ' x ζm q π) →
    lty_res E L lt lt' k Φ'.
  Proof.
    intros (Hs & Hn & Rslv) Himp. split; [done|]. split; [done|].
    iIntros (G m x ζm q d g D tid l ???) "LFT PROPH UNIQ TIME E L G ⧖ Own".
    iDestruct (Rslv with "LFT PROPH UNIQ TIME E L G ⧖ Own") as "T"; [done..|].
    iApply (ctask_mono with "[] T"). iIntros "(Obs & $ & $) !>".
    iApply (proph_obs_impl with "Obs"). apply Himp.
  Qed.

  (** A leaf is resolved by [resolve_keep] of its type. *)
  Lemma lty_res_ofty {𝔄} E L (ty: type 𝔄) Φ :
    resolve_keep E L ty Φ → lty_res E L (OfTy ty) (OfRes ty) 1 (λ x _ _, Φ x).
  Proof.
    intros Rslv. split; [done|]. split; [done|].
    iIntros (G m x ζm q d g D tid l ? Hd Hg) "LFT PROPH UNIQ TIME E L G _ Own".
    rewrite /ltype_own /= /leaf_owned_s /leaf_owned /ofty_owned /=.
    iDestruct "Own" as (x' ->) "[Pt Gho]". iModIntro. iIntros "£".
    iDestruct (lc_weaken (m + d * (g + 1)) with "£") as "[£m £r]";
      [rewrite /advance_credits; nia|].
    iMod (lc_fupd_elim_laterN with "£m Gho") as "Gho".
    iMod (Rslv _ ⊤ with "LFT PROPH UNIQ TIME E L G Gho") as "Upd"; [solve_ndisj|].
    iMod (lc_step_fupdN_elim_later with "£r Upd") as ">(Obs & $ & Res)".
    iModIntro. iFrame "Obs". rewrite /res_leaf. iExists x. iSplit; [done|]. iFrame "Pt".
    iApply bi.laterN_intro. iExists d, g. by iFrame.
  Qed.

  (** A [Copy] leaf is resolved from a copy of its (persistent) ownership, and kept as it
      is: it stays readable by the rules for [OfTy] (no [ResOwn] needed). *)
  Lemma lty_res_copy {𝔄} E L (ty: type 𝔄) `{!Copy ty} Φ :
    resolve E L ty Φ → lty_res E L (OfTy ty) (OfTy ty) 1 (λ x _ _, Φ x).
  Proof.
    intros Rslv. split; [done|]. split; [done|].
    iIntros (G m x ζm q d g D tid l ? Hd Hg) "LFT PROPH UNIQ TIME E L G _ Own".
    rewrite /ltype_own /= /leaf_owned_s /leaf_owned /ofty_owned /=.
    iDestruct "Own" as (x' ->) "[Pt #Gho]". iModIntro. iIntros "£".
    iDestruct (lc_weaken (m + d * (g + 1)) with "£") as "[£m £r]";
      [rewrite /advance_credits; nia|].
    iMod (lc_fupd_elim_laterN with "£m Gho") as "#Gho'".
    iMod (Rslv _ ⊤ with "LFT PROPH UNIQ TIME E L G Gho'") as "Upd"; [solve_ndisj|].
    iMod (lc_step_fupdN_elim_later with "£r Upd") as ">(Obs & $)".
    iModIntro. iFrame "Obs". iExists x. iSplit; [done|]. by iFrame "Pt Gho".
  Qed.

  Lemma lty_res_prod {𝔄1 𝔄2} E L (lt1 lt1': lty 𝔄1) (lt2 lt2': lty 𝔄2) k1 k2 Φ1 Φ2 :
    lty_res E L lt1 lt1' k1 Φ1 → lty_res E L lt2 lt2' k2 Φ2 →
    lty_res E L (ProdLty lt1 lt2) (ProdLty lt1' lt2') (k1 + k2)
      (λ x ζm q π, Φ1 x.1 ζm (false :: q) π ∧ Φ2 x.2 ζm (true :: q) π).
  Proof.
    intros (Hs1 & Hn1 & Rslv1) (Hs2 & Hn2 & Rslv2).
    split; [by rewrite /= Hs1 Hs2|]. split; [by rewrite /= Hn1 Hn2|].
    iIntros (G m x ζm q d g D tid l ? Hd Hg) "#LFT #PROPH #UNIQ #TIME #E #L G #⧖ Own".
    rewrite /ltype_own /= /prod_node. iDestruct "Own" as "[Own1 Own2]".
    iApply ctask_fupd.
    iMod (fractional.frac_split_guard_in_half with "G L") as (γ) "[H1 [H2 [#Gh #Back]]]";
      [solve_ndisj|].
    iDestruct (Rslv1 _ m x.1 ζm (false :: q) d g D tid _ with
      "LFT PROPH UNIQ TIME E Gh H1 ⧖ Own1") as "T1"; [done..|].
    iDestruct (Rslv2 _ m x.2 ζm (true :: q) d g D tid _ with
      "LFT PROPH UNIQ TIME E Gh H2 ⧖ Own2") as "T2"; [done..|].
    iModIntro. iDestruct (ctask_sep with "T1 T2") as "T".
    iApply (ctask_mono with "[] T").
    iIntros "[(#Obs1 & H1 & Own1) (#Obs2 & H2 & Own2)]".
    iMod (fupd_mask_mono with "(Back H1 H2)") as "$"; [solve_ndisj|].
    iModIntro. rewrite Hs1. iFrame "Own1 Own2".
    iCombine "Obs1 Obs2" as "Obs". iApply (proph_obs_impl with "Obs")=> π [??]. done.
  Qed.

  Lemma lty_res_own {𝔄} E L n (lt lt': lty 𝔄) k Φ :
    lty_res E L lt lt' k Φ →
    lty_res E L (OwnPtrLty n lt) (OwnPtrLty n lt') k (λ x ζm q π, Φ x.2 ζm (false :: q) π).
  Proof.
    intros (Hs & Hn & Rslv). split; [done|]. split; [by rewrite /= Hn|].
    iIntros (G m x ζm q d g D tid l ? Hd Hg) "LFT PROPH UNIQ TIME E L G ⧖ Own".
    rewrite /ltype_own /=. destruct x as [l' x]. iDestruct "Own" as "(Pt & %Hd0 & Fr & Own)".
    iDestruct (Rslv G (m + 1) x ζm (false :: q) (pred d) g D tid _ with
      "LFT PROPH UNIQ TIME E L G ⧖ Own") as "T"; [lia|done|].
    iApply (ctask_mono with "[Pt Fr] T"). iIntros "(Obs & $ & Own) !>". iFrame "Obs".
    rewrite /own_node Hs. by iFrame.
  Qed.

  Lemma lty_res_sum {𝔄l} E L (tyl: typel 𝔄l) i (lt lt': lty (𝔄l !!ₗ i)) k Φ :
    lty_res E L lt lt' k Φ →
    lty_res E L (SumLty tyl i lt) (SumLty tyl i lt') k
      (λ x ζm q π, ∀ y, psum_proj i x.1 = Some y → Φ y ζm (false :: q) π).
  Proof.
    intros (Hs & Hn & Rslv). split; [by rewrite /= Hs|]. split; [done|].
    iIntros (G m x ζm q d g D tid l ? Hd Hg) "LFT PROPH UNIQ TIME E L G ⧖ Own".
    rewrite lty_rfn_sum. destruct (psum_proj i x.1) as [y|] eqn:Hy; last first.
    { by rewrite /ltype_own /= /prfn_dummy /sum_node /=. }
    rewrite /ltype_own ltype_own_cp_sum_owned sum_node_sum.
    iDestruct "Own" as "(Tag & Own & Pad)".
    iDestruct (Rslv G m y ζm (false :: q) d g D tid _ with
      "LFT PROPH UNIQ TIME E L G ⧖ Own") as "T"; [done..|].
    iApply (ctask_mono with "[Tag Pad] T"). iIntros "(Obs & $ & Own) !>".
    rewrite lty_rfn_sum Hy ltype_own_cp_sum_owned sum_node_sum Hs. iFrame.
    iApply (proph_obs_impl with "Obs")=> π ? y' [= <-]. done.
  Qed.
End lty_res.

Section lty_res_uniq.
  Context `{!typeG Σ}.

  (** An unfolded unique borrow whose referent is a leaf: resolved by
      [resolve_uniq_body]; its referent is viewed at [κ]. *)
  Lemma lty_res_uniq_leaf {𝔄} E L κ (ty: type 𝔄) :
    lctx_lft_alive E L κ →
    lty_res E L (UniqLty (OfTy ty) κ) (ResUniqLty (OfTy ty) κ) 1 (λ x _ _ π,
      (π (uniq_prvar (uniq_bor_current x) (uniq_bor_ξi x))).1 = vπ (uniq_bor_current x) π).
  Proof.
    intros Alv. split; [done|]. split; [done|].
    iIntros (G m x ζm q d g D tid l ? Hd Hg) "#LFT #PROPH #UNIQ #TIME #E #GL G #⧖ Own".
    destruct x as [[[[[l' x0] ξi] d0] g0] idx0].
    rewrite /ltype_own /= /uniq_node /=. iDestruct "Own" as "(Pt & _ & _ & N)".
    iModIntro. iIntros "£".
    iDestruct (lc_weaken m with "£") as "£"; [rewrite /advance_credits; nia|].
    iMod (lc_fupd_elim_laterN with "£ N") as "(#Incl & #Gc & %d' & %g' & %Hle & C)".
    rewrite /leaf_uniq /ofty_uniq. iDestruct "C" as (x idx ->) "Body".
    iAssert (⧖(S d' `max` g'))%I as "#⧖'".
    { iApply (persistent_time_receipt_mono with "⧖"). lia. }
    iMod (resolve_uniq_body ty x0 ξi d' g' idx κ tid l' E L G ⊤
      with "LFT PROPH UNIQ TIME Incl E GL G ⧖' Body") as "(#Obs & G & #Shr & #Pt' & #Pers)";
      [done|solve_ndisj|].
    iModIntro. iFrame "G". iSplitR.
    { iApply (proph_obs_impl with "Obs")=> π /= ->. done. }
    rewrite /res_node. iFrame "Pt". iApply bi.laterN_intro. iFrame "Incl".
    iExists d', g. iSplit; [iPureIntro; lia|]. rewrite /= /view_leaf.
    iExists x0. iSplit; [done|]. iSplit.
    - iApply guard_cloc_combine_fancy; [done|]. iApply (lguards_weaken_later with "Pt'"). lia.
    - iSplit; [iApply (ty_shr_depth_mono with "Shr"); lia|].
      iApply (ty_gho_pers_depth_mono with "Pers"); lia.
  Qed.

  (** An unfolded unique borrow whose referent is compound: its prophecy variable is
      resolved to the denotation of the referent (the blocked leaves through the
      reservation, the unblocked leaves by their sharing at [κ]), and the referent is
      shared into its view at [κ]. *)
  Lemma lty_res_uniq_cpd {𝔄} E L κ (lt: lty 𝔄) :
    lctx_lft_alive E L κ → lctx_lft_alive E L (lty_sbl lt) → lty_is_cpd lt → lty_vok lt →
    lty_res E L (UniqLty lt κ) (ResUniqLty lt κ) 1 (λ x ζm q π,
      (π (uniq_prvar (uniq_bor_current x) (uniq_bor_ξi x))).1 =
        prfn_den (lty_rfn lt (uniq_bor_current x) ζm (false :: q)) π).
  Proof.
    intros Alv Alvs Hc Hv. split; [done|]. split; [done|].
    iIntros (G m x ζm q d g D tid l ? Hd Hg) "#LFT #PROPH #UNIQ #TIME #E #GL G #⧖ Own".
    destruct x as [[[[[l' x0] ξi] d0] g0] idx0].
    rewrite /ltype_own /= /uniq_node /= ltype_own_cp_uniq_cpd //.
    set r' := lty_rfn lt x0 ζm (false :: q).
    iDestruct "Own" as "(Pt & _ & _ & N)".
    iModIntro. iIntros "£".
    iDestruct (lc_weaken (m + (advance_credits D - m)) with "£") as "[£m £]";
      [rewrite /advance_credits; nia|].
    iMod (lc_fupd_elim_laterN with "£m N") as "(#Incl & #Gc & %d' & %g' & %Hle & C)".
    leaf_open "GL" with "G" as "[L back]"; [solve_ndisj|].
    iDestruct (Alv with "L E") as "#Lκ". iDestruct (Alvs with "L E") as "#Lκs".
    iMod ("back" with "L") as "G".
    iDestruct (guards_transitive with "GL Lκ") as "#Gκ".
    iAssert (G &&{↑NllftG}&&> @[κ ⊓ lty_sbl lt])%I as "#Gκs".
    { iApply guards_llft_glb; [iApply "Gκ"|iApply (guards_transitive with "GL Lκs")]. }
    rewrite /cpd_own.
    iDestruct "C" as (x₀ κp γ γf idx ζl) "(#Inclp & %Hr & Tok & Gh & Tf & _ & #Bor)".
    set node := ltype_own_cp false lt (Owned 0).
    set P := cpd_gbody κp γf (lty_fold lt) node tid l'.
    set c := uniq_cell x₀ d' g' γ.
    set uπ : proph (uniq_cellₛ 𝔄) := λ π, (prfn_den r' π, c.2).
    set n := (d' + 1) * (g + 1).
    iDestruct (lc_weaken (1 + (0 + 2 * d' + 3) + d' * (g + 2) + n) with "£") as
      "[[[£1 £s] £t] £n]"; [rewrite /advance_credits /n; nia|].
    iMod (proph_idx_bor_gen_resolve_share_rsv ⊤ κ (lty_sbl lt) (uniq_prvar x₀ ξi) c idx ζl P uπ
      (pat_ok κp (lty_pat lt) ∗ ghost_var γ (1/2) (lstate (lty_pat lt) r') ∗
       guarded_upd lazyE @[ty_lft (lty_fold lt)] (⧖(S d' `max` g') ∗
         node (lty_pat lt) r' d' g' tid l'))
      (lty_view lt κ 0 (lty_pat lt) r' d' g tid l') G n
      with "LFT PROPH UNIQ Gκs [Gh Tf] [£1 £s £t £n] G Tok Bor") as "(#Obs & G & V)";
      [solve_ndisj| | |].
    { iIntros (wπ) "Body".
      iPoseProof (cpd_gbody_pin κp γ γf (lty_fold lt) node (lty_pat lt) r' x₀ d' g' tid l')
        as "#Iff".
      iAssert (▷ ((⌜∀ π, (wπ π).1 = prfn_den r' π⌝ ∗ ghost_var γ (1/2) (lstate (lty_pat lt) r') ∗
        cpd_tok γf) ∗ (pat_ok κp (lty_pat lt) ∗ ghost_var γ (1/2) (lstate (lty_pat lt) r') ∗
        guarded_upd lazyE @[ty_lft (lty_fold lt)] (⧖(S d' `max` g') ∗
          node (lty_pat lt) r' d' g' tid l'))))%I with "[Gh Tf Body]" as "H".
      { iNext. iApply ("Iff" $! wπ). iFrame. }
      iDestruct "H" as "[(_ & Gh & Tf) P0]". iModIntro. iFrame "P0". iNext.
      iIntros "P0". iDestruct ("Iff" $! uπ) as "[_ I2]".
      iDestruct ("I2" with "[Gh Tf P0]") as "[_ $]". iFrame. by iPureIntro. }
    { iIntros (Hh HTh) "#Hκs Hh Bb".
      iAssert (Hh &&{↑NllftG}&&> @[κ])%I as "#Hκ".
      { iApply (guards_transitive with "Hκs"). iApply llftl_intersect_incl_l. }
      iMod (llftl_sep_split with "LFT Bb") as "[_ Bb]"; [solve_ndisj|].
      iMod (llftl_sep_split with "LFT Bb") as "[_ Bb]"; [solve_ndisj|].
      iMod (llftl_bor_guarded_upd with "LFT Hκ Incl Hh £1 Bb") as "[Bb Hh]";
        [solve_ndisj|rewrite /lazyE; solve_ndisj|].
      iMod (llftl_sep_split with "LFT Bb") as "[_ Bb]"; [solve_ndisj|].
      iMod (lty_share_view lt Hv κ 0 x0 ζm (false :: q) d' g' g tid l' Hh ⊤ HTh
        ltac:(solve_ndisj) ltac:(lia) with "LFT PROPH UNIQ Hκ Incl Gc Hh [Bb]") as "Upd".
      { by rewrite /ltype_own. }
      iMod (lc_step_fupdN_elim_later with "£s Upd") as ">[Hh V]".
      iDestruct (lty_view_guard_proph with "LFT Incl V") as "[V (%ηl & %Hdep & T)]".
      iMod (lc_fupd_elim_laterN with "£t T") as "#T".
      iModIntro. iFrame "Hh V £n". iExists ηl. iSplit.
      - iPureIntro. apply (proph_dep_constr (λ a, (a, c.2))). by apply Hdep.
      - iIntros (η Hη). iApply ("T" $! η Hη Hh with "Hκs"). }
    iModIntro. iFrame "G". iSplitR.
    { iApply (proph_obs_impl with "Obs")=> π /= Heq.
      by rewrite (uniq_prvar_app_irrel x0 x₀) Heq. }
    rewrite /res_node. iFrame "Pt". iApply bi.laterN_intro. iFrame "Incl".
    iExists d', g. iSplit; [iPureIntro; lia|]. iExact "V".
  Qed.
End lty_res_uniq.

(** * The rule *)

Section typing.
  Context `{!typeG Σ}.

  (** Resolving an owned place to a readable state, in [k] program steps (no new
      lifetime, no new borrow; the place is kept, at the same value). *)
  Lemma type_resolve_oplace_res_instr {𝔄} E L I p n (lt lt': lty 𝔄) k Φ :
    lty_res E L lt lt' k Φ →
    typed_instr E L I +[p ◁ₗown{n} lt] (place_resolve.skipn k) (const +[p ◁ₗown{n} lt'])
      (λ post '-[x], λ mask π, Φ x.1.2 x.2 [] π → post -[x] mask π).
  Proof.
    iIntros ((Hs & Hn & Rslv) tid post mask iκs [x []])
      "#LFT #TIME #PROPH #UNIQ #E L I [(%v & %Hp & Own) _] Obs".
    destruct x as [[l x₀] ζm].
    iDestruct "Own" as (D d g) "(#⧖ & ⧗r & -> & %Hle & Fr & Own)".
    iMod (llctx_interp_make_guarded with "L") as (γ) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iDestruct (Rslv _ 1 x₀ ζm [] d g D tid _ with "LFT PROPH UNIQ TIME E Ghalf H1 ⧖ Own")
      as "T"; [lia|lia|].
    iDestruct (ctask_mono with "[H2] T") as "T".
    { iIntros "(#Obs' & H1 & Own)".
      iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
      iModIntro. iCombine "Obs' L Own" as "R". iExact "R". }
    iApply (wp_skipn_ctask _ (advance_credits D) D with "TIME ⧖ T"); [done|].
    iIntros "(#Obs' & L & Own)".
    iExists -[((l, x₀), ζm)]. iFrame "L I". iSplitL "⧗r Fr Own".
    - iSplit; [|done]. iExists #l. iSplit; [done|]. iExists D, d, g.
      rewrite Hs Hn. by iFrame "⧖ ⧗r Fr Own".
    - iCombine "Obs Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=>/= ?[Imp ?].
      by apply Imp.
  Qed.
End typing.
