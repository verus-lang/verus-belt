(** * Operations on resolved places

  Resolved places ([OfRes], [ResUniqLty], see [typing/place_res.v]) are read and shared,
  not written:
  - the access to a sub-place of a view ([view_pctx_acc]);
  - reading a [Copy] leaf of size 1 below a resolved unique borrow
    ([type_read_oplace_res_instr]), and a shared borrow of a sub-place below it
    ([type_share_oplace_res_instr]);
  - folding a resolved unique borrow whose view has no blocked leaf (and no nested unique
    borrow) to a shared reference ([tctx_fold_oplace_res_uniq]);
  - unblocking a blocked leaf of a view ([type_unblock_oplace_res_instr]);
  - dropping a resolved place ([type_drop_oplace_res_instr]). *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From lrust.lang Require Import proofmode.
From lrust.lang.lib Require Import new_delete.
From lrust.util Require Import update.
From lrust.typing Require Export type ltype lpath pctx_acc place_own.
From lrust.typing Require Import type_context programs programs_util lft_contexts
  uniq_util uniq_bor product own shr_bor sum type_sum freeable_util place place_shr
  place_resolve place_puniq place_sum place_pshr place_res place_res_view place_res_rslv.
From lrust.util Require Import proph_bor.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

(** * The access to a sub-place of a view *)

Section view_acc.
  Context `{!typeG Σ}.

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
      iIntros (lt' p' r' dh' gh' dn gn ?? (?&?&?&?)) "V'".
      iApply (lty_view_depth_mono with "V'"); lia.
    - rewrite /prod_node lty_size_plug. iDestruct "V" as "[V1 V2]".
      iDestruct (IH with "GR V1") as (dh gh) "(% & Vh & Gs & Cl)"; [done|].
      iExists dh, gh. iFrame "Vh". iSplit; [done|]. iFrame "Gs".
      iIntros (lt' p' r' dh' gh' dn gn Hsz Hf Hle) "V'". rewrite /prod_node lty_size_plug Hsz.
      iSplitL "Cl V'"; [iApply ("Cl" with "[//] [//] [//] V'")|].
      iApply (lty_view_depth_mono with "V2"); lia.
    - rewrite /prod_node. iDestruct "V" as "[V1 V2]".
      iDestruct (IH with "GR V2") as (dh gh) "(% & Vh & Gs & Cl)"; [done|].
      iExists dh, gh. iFrame "Vh Gs". iSplit; [done|].
      iIntros (lt' p' r' dh' gh' dn gn Hsz Hf Hle) "V'". rewrite /prod_node.
      iSplitL "V1"; [iApply (lty_view_depth_mono with "V1"); lia|].
      iApply ("Cl" with "[//] [//] [//] V'").
    - rewrite /view_own lty_size_plug. iDestruct "V" as "(#Gp & %Hd & V)".
      iDestruct (IH with "GR V") as (dh gh) "(% & Vh & Gs & Cl)"; [done|].
      iExists dh, gh. iFrame "Vh". iSplit; [iPureIntro; destruct_and!; split_and!; try lia; done|].
      iFrame "Gs". iSplit.
      { iApply (guards_transitive_right with "[] Gp").
        iApply (guards_transitive with "GR"). iApply pctx_salv_incl. }
      iIntros (lt' p' r' dh' gh' dn gn Hsz Hf Hle) "V'". rewrite /view_own lty_size_plug Hsz.
      iSplit; [iApply (lguards_weaken_later with "Gp"); lia|]. iSplit; [iPureIntro; lia|].
      iApply ("Cl" with "[//] [//] [%] V'"). lia.
    - rewrite /psum_proj_or. destruct (psum_proj i x.1) as [y|] eqn:Hy; last first.
      { by rewrite /prfn_dummy /view_sum. }
      rewrite /view_sum /prfn_sum psum_proj_pinj lty_size_plug.
      iDestruct "V" as "(#Gt & V & #Gq)".
      iDestruct (IH with "GR V") as (dh gh) "(% & Vh & Gs & Cl)"; [done|].
      iExists dh, gh. iFrame "Vh". iSplit; [done|]. iFrame "Gs".
      iIntros (lt' p' r' dh' gh' dn gn Hsz Hf Hle) "V'".
      rewrite /view_sum /prfn_sum psum_proj_pinj lty_size_plug Hsz.
      iSplit; [iApply (lguards_weaken_later with "Gt"); lia|].
      iSplitL; [iApply ("Cl" with "[//] [//] [%] V'"); lia|].
      iApply (lguards_weaken_later with "Gq"); lia.
    - destruct HK as [_ HK]. rewrite /view_uniq.
      iDestruct "V" as "(#Gp & #Incl & %d' & %g' & %Hle & V)".
      iDestruct (IH with "GR V") as (dh gh) "(% & Vh & Gs & Cl)"; [done|].
      iExists dh, gh. iFrame "Vh". iSplit; [iPureIntro; destruct_and!; split_and!; try lia; done|].
      iSplit.
      { iSplit.
        - iApply (guards_transitive_right with "[] Gp").
          iApply (guards_transitive with "GR"). iApply llftl_incl_trans; [iApply pctx_salv_incl|].
          iApply llftl_intersect_incl_l.
        - iApply (pctx_sguards_mono with "Gs"). lia. }
      iIntros (lt' p' r' dh' gh' dn gn Hsz Hf Hle') "V'".
      have Hf': lty_fold (pctx_plug K lt') = lty_fold (pctx_plug K lt) by apply lty_fold_plug_eq'.
      rewrite /view_uniq Hf'. iSplit; [iApply (lguards_weaken_later with "Gp"); lia|].
      iFrame "Incl". iExists (pred dn), gn. iSplit; [iPureIntro; lia|].
      iApply ("Cl" with "[//] [//] [%] V'"). lia.
  Qed.
End view_acc.
