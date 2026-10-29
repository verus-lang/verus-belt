(** * Views of the referents of resolved unique borrows

  The referent of a resolved unique borrow [ResUniqLty lt κ] is a _view_ at [κ]
  ([lty_view] of [typing/ltype.v]): its unblocked leaves are shared at [κ], its blocked
  leaves keep their inheritances in borrows at [κ], nested unique borrows at [κ'] are
  views at [κ ⊓ κ']. This file: laws of views (depth monotonicity, the guards of the
  prophecy tokens of the values of the unblocked leaves), and the sharing of a place in a
  borrow at [κ] into its view ([lty_share_view]), which is how a unique borrow is
  resolved ([typing/place_res_rslv.v]). See [~/verus-belt-phase3-design.md], section
  "Resolve to a readable state". *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From lrust.lang Require Import proofmode.
From lrust.typing Require Export type ltype lpath pctx_acc place_own.
From lrust.typing Require Import type_context programs programs_util lft_contexts
  uniq_util uniq_bor product own shr_bor sum type_sum freeable_util place place_shr
  place_resolve place_puniq place_sum place_pshr place_res.
From lrust.util Require Import proph_bor.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section view_laws.
  Context `{!typeG Σ}.

  (** ** Depth monotonicity *)

  Lemma view_leaf_depth_mono {𝔄} κ m (ty: type 𝔄) p r d g d' g' tid l :
    d ≤ d' → g ≤ g' → view_leaf κ m ty p r d g tid l ⊢ view_leaf κ m ty p r d' g' tid l.
  Proof.
    intros ??. destruct r as [lr|]; [|done]. rewrite /view_leaf.
    destruct p; try done; try (iIntros "[#G $]"; iApply (lguards_weaken_later with "G"); lia);
      iIntros "(%x & Rel & #G & #Shr & #Pers)"; iExists x; iFrame "Rel";
      (iSplit; [iApply (lguards_weaken_later with "G"); lia|]);
      (iSplit; [by iApply (ty_shr_depth_mono with "Shr")|]);
      by iApply (ty_gho_pers_depth_mono with "Pers").
  Qed.

  Lemma lty_view_depth_mono {𝔄} (lt: lty 𝔄) κ m p r d g d' g' tid l :
    d ≤ d' → g ≤ g' → lty_view lt κ m p r d g tid l ⊢ lty_view lt κ m p r d' g' tid l.
  Proof.
    induction lt as [𝔄 ty|𝔄 ty α|𝔄 lt IH κ'|𝔄 n lt IH|𝔄 𝔅 lt1 IH1 lt2 IH2|𝔄 ty α|
      𝔄l tyl i lt IH|𝔄 lt IH κ'|𝔄 ty|𝔄 lt IH κ'] in κ, m, p, r, d, g, d', g', tid, l |- *;
      intros Hd Hg; simpl; try by apply view_leaf_depth_mono.
    - destruct r as [?|[[l' r'] ξi]]; [done|]. rewrite /view_uniq.
      iIntros "(#G & $ & %d1 & %g1 & %Hle & C)". iSplitR.
      { iApply (lguards_weaken_later with "G"). lia. }
      iExists d1, g1. iFrame. iPureIntro. lia.
    - destruct r as [?|[l' r']]; [done|]. rewrite /view_own.
      iIntros "(#G & % & C)". iSplitR; [iApply (lguards_weaken_later with "G"); lia|].
      iSplit; [iPureIntro; lia|]. iApply (IH with "C"); lia.
    - destruct r as [?|[r1 r2]]; [done|]. rewrite /prod_node.
      iIntros "[A B]". iSplitL "A"; [iApply (IH1 with "A")|iApply (IH2 with "B")]; done.
    - destruct r as [?|[s pad]]; [done|]. rewrite /view_sum.
      case_match; [|done]. iIntros "(#G1 & C & #G2)".
      iSplitR; [iApply (lguards_weaken_later with "G1"); lia|].
      iSplitL; [iApply (IH with "C"); lia|]. iApply (lguards_weaken_later with "G2"); lia.
    - iIntros "[V $]". by iApply (view_leaf_depth_mono with "V").
    - done.
    - done.
  Qed.

  (** ** The guards of the prophecy tokens

      The denotation of the refinement of a view depends only on the variables of a
      reservation for it and on the prophecy variables of the values of its unblocked
      leaves, whose tokens are guarded by anything that guards [κ] (from their sharing
      predicates, [ty_shr_guard_proph]). *)

  Definition view_tguards (κ: lft) (ηl: list proph_var) (d g: nat) : iProp Σ :=
    ▷^(d * (g + 2)) □ (∀ η (_: η ∈ ηl) R, (R &&{↑NllftG}&&> @[κ]) -∗
      (R &&{↑NllftG; (d + 1) * (g + 1)}&&> 1:[η])).

  Global Instance view_tguards_persistent κ ηl d g : Persistent (view_tguards κ ηl d g).
  Proof. apply _. Qed.

  Lemma view_tguards_nil κ d g : ⊢ view_tguards κ [] d g.
  Proof. iIntros "!> !>" (η Hη R). by apply not_elem_of_nil in Hη. Qed.

  Lemma view_tguards_mono κ κ' ηl d g d' g' :
    d ≤ d' → g ≤ g' → (@[κ'] &&{↑NllftG}&&> @[κ]) -∗
    view_tguards κ ηl d g -∗ view_tguards κ' ηl d' g'.
  Proof.
    iIntros (??) "#Incl #T". iApply (bi.laterN_le (d * (g + 2))); [nia|]. iNext.
    iDestruct "T" as "#T". iIntros "!>" (η Hη R) "#R". iApply (lguards_weaken_later _ _ _ ((d + 1) * (g + 1))); [nia|].
    iApply ("T" with "[//]"). iApply (guards_transitive with "R Incl").
  Qed.

  Lemma view_tguards_app κ ηl1 ηl2 d g :
    view_tguards κ ηl1 d g -∗ view_tguards κ ηl2 d g -∗ view_tguards κ (ηl1 ++ ηl2) d g.
  Proof.
    iIntros "#T1 #T2". iNext. iDestruct "T1" as "#T1". iDestruct "T2" as "#T2".
    iIntros "!>" (η Hη R) "#R".
    apply elem_of_app in Hη as [Hη|Hη]; [by iApply "T1"|by iApply "T2"].
  Qed.

  Global Instance view_leaf_in_persistent {𝔄} κ m (ty: type 𝔄) x d g tid l :
    Persistent (view_leaf κ m ty PatLeaf (inl (PlaceIn x)) d g tid l).
  Proof. rewrite /view_leaf. apply _. Qed.

  Lemma view_leaf_unblocked_tguards {𝔄} κ m (ty: type 𝔄) x d g tid l :
    llft_ctx -∗ κ ⊑ ty_lft ty -∗ view_leaf κ m ty PatLeaf (inl (PlaceIn x)) d g tid l -∗
    view_tguards κ (ξl x) d g.
  Proof.
    iIntros "#LFT #Incl (%x' & -> & _ & #Shr & #Pers)".
    rewrite /view_tguards. iApply bi.laterN_intuitionistically_2. iModIntro.
    rewrite bi.laterN_forall. iIntros (η). rewrite bi.laterN_forall. iIntros (Hη).
    rewrite bi.laterN_forall. iIntros (R).
    rewrite -(Nat.add_0_l ((d + 1) * (g + 1))).
    iApply (ty_shr_guard_proph ty κ x 0 d g tid η R Hη with "LFT Incl Pers Shr").
  Qed.

  (** A shared-blocked leaf (at [α]) is shared at [κ ⊓ α]. *)
  Lemma view_leaf_shrblk_tguards {𝔄} κ m (ty: type 𝔄) α x d g tid l :
    llft_ctx -∗ κ ⊑ ty_lft ty -∗
    view_leaf κ m ty (PatShrBlocked α) (inl (PlaceIn x)) d g tid l -∗
    view_tguards (κ ⊓ α) (ξl x) d g.
  Proof.
    iIntros "#LFT #Incl (%x' & -> & _ & #Shr & #Pers)".
    iAssert (κ ⊓ α ⊑ ty_lft ty)%I as "#Incl'".
    { iApply llftl_incl_trans; [iApply llftl_intersect_incl_l|done]. }
    rewrite /view_tguards. iApply bi.laterN_intuitionistically_2. iModIntro.
    rewrite bi.laterN_forall. iIntros (η). rewrite bi.laterN_forall. iIntros (Hη).
    rewrite bi.laterN_forall. iIntros (R).
    rewrite -(Nat.add_0_l ((d + 1) * (g + 1))).
    iApply (ty_shr_guard_proph ty (κ ⊓ α) x 0 d g tid η R Hη with "LFT Incl' Pers Shr").
  Qed.

  (** The intersection of the lifetimes of the shared-blocked leaves of a place (below the
      nested unique borrows too); [static] if there are none. *)
  Fixpoint lty_sbl {𝔄} (lt: lty 𝔄) : lft :=
    match lt with
    | ShrBlocked _ α => α
    | UniqLty lt' _ | OwnPtrLty _ lt' | SumLty _ _ lt' => lty_sbl lt'
    | ProdLty lt1 lt2 => lty_sbl lt1 ⊓ lty_sbl lt2
    | _ => static
    end.

  (** [κ ⊓ (κ1 ⊓ κ2) ⊑ κ ⊓ κ1] and [⊑ κ ⊓ κ2]. *)
  Lemma lft_incl_inter_mono_l κ κ1 κ2 : ⊢ κ ⊓ (κ1 ⊓ κ2) ⊑ κ ⊓ κ1.
  Proof.
    iApply llftl_incl_glb; [iApply llftl_intersect_incl_l|].
    iApply llftl_incl_trans; [iApply llftl_intersect_incl_r|iApply llftl_intersect_incl_l].
  Qed.
  Lemma lft_incl_inter_mono_r κ κ1 κ2 : ⊢ κ ⊓ (κ1 ⊓ κ2) ⊑ κ ⊓ κ2.
  Proof.
    iApply llftl_incl_glb; [iApply llftl_intersect_incl_l|].
    iApply llftl_incl_trans; [iApply llftl_intersect_incl_r|iApply llftl_intersect_incl_r].
  Qed.

  (** The prophecy tokens of the values of the unblocked and shared-blocked leaves of a
      view are guarded by anything that guards [κ ⊓ lty_sbl lt]. *)
  Lemma lty_view_guard_proph {𝔄} (lt: lty 𝔄) κ m x ζm q d g tid l :
    llft_ctx -∗ κ ⊑ ty_lft (lty_fold lt) -∗
    lty_view lt κ m (lty_pat lt) (lty_rfn lt x ζm q) d g tid l -∗
    lty_view lt κ m (lty_pat lt) (lty_rfn lt x ζm q) d g tid l ∗
    ∃ ηl, ⌜∀ ζl, prfn_rsv (lty_rfn lt x ζm q) ζl → prfn_den (lty_rfn lt x ζm q) ./ ζl ++ ηl⌝ ∗
      view_tguards (κ ⊓ lty_sbl lt) ηl d g.
  Proof.
    induction lt as [𝔄 ty|𝔄 ty α|𝔄 lt IH κ'|𝔄 n lt IH|𝔄 𝔅 lt1 IH1 lt2 IH2|𝔄 ty α|
      𝔄l tyl i lt IH|𝔄 lt IH κ'|𝔄 ty|𝔄 lt IH κ'] in κ, m, x, q, d, g, tid, l |- *;
      iIntros "#LFT #Incl V"; simpl.
    - iDestruct "V" as "#V".
      iDestruct (view_leaf_unblocked_tguards κ m ty x d g tid l with "LFT Incl V") as "#T".
      iFrame "V". iExists (ξl x). iSplit.
      + iPureIntro. intros ζl _.
        rewrite prfn_den_in. eapply proph_dep_weaken; [|apply syn_indep]. set_solver.
      + iApply (view_tguards_mono with "[] T"); [lia|lia|]. iApply llftl_intersect_incl_l.
    - iFrame "V". iExists []. iSplit; [|iApply view_tguards_nil]. iPureIntro.
      intros ζl. rewrite prfn_rsv_inl prfn_den_inl app_nil_r. done.
    - rewrite /view_uniq. iDestruct "V" as "(#G & #Incl' & %d1 & %g1 & %Hle & V)".
      iAssert (κ ⊓ κ' ⊑ ty_lft (lty_fold lt))%I as "#Incl2".
      { iApply llftl_incl_trans; [iApply llftl_intersect_incl_r|done]. }
      iDestruct (IH with "LFT Incl2 V") as "[V (%ηl & %Hdep & #T)]".
      iSplitL "V". { iFrame "G Incl'". iExists d1, g1. by iFrame. }
      iExists ηl. iSplit.
      + iPureIntro. intros ζl [Hr Hξ].
        apply (proph_dep_weaken _ ((ζl ++ ηl) ++ (ζl ++ ηl))); [set_solver|].
        apply (proph_dep_constr2 pair); [by apply Hdep|].
        eapply proph_dep_weaken; [|apply Hξ]. set_solver.
      + iApply (view_tguards_mono with "[] T"); [lia|lia|].
        iApply llftl_incl_glb; [|iApply llftl_intersect_incl_r].
        iApply llftl_incl_glb; [iApply llftl_intersect_incl_l|].
        iApply llftl_incl_trans; [iApply llftl_intersect_incl_l|].
        iApply llftl_incl_trans; [iApply "Incl"|]. iApply llftl_intersect_incl_l.
    - destruct x as [l' x]. rewrite /view_own. iDestruct "V" as "(#G & %Hd & V)".
      iDestruct (IH with "LFT Incl V") as "[V (%ηl & %Hdep & #T)]".
      iSplitL "V". { by iFrame "G V". }
      iExists ηl. iSplit.
      + iPureIntro. intros ζl Hr. apply (proph_dep_constr (pair l')). by apply Hdep.
      + iApply (view_tguards_mono with "[] T"); [lia|lia|iApply guards_refl].
    - rewrite /prod_node. iDestruct "V" as "[V1 V2]".
      iAssert (κ ⊑ ty_lft (lty_fold lt1))%I as "#Incl1".
      { iApply (llftl_incl_trans with "Incl"). simpl. rewrite lft_intersect_list_app.
        iApply llftl_intersect_incl_l. }
      iAssert (κ ⊑ ty_lft (lty_fold lt2))%I as "#Incl2".
      { iApply (llftl_incl_trans with "Incl"). simpl. rewrite lft_intersect_list_app.
        iApply llftl_intersect_incl_r. }
      iDestruct (IH1 with "LFT Incl1 V1") as "[V1 (%ηl1 & %Hdep1 & #T1)]".
      iDestruct (IH2 with "LFT Incl2 V2") as "[V2 (%ηl2 & %Hdep2 & #T2)]".
      iFrame "V1 V2". iExists (ηl1 ++ ηl2). iSplit.
      + iPureIntro. intros ζl [Hr1 Hr2].
        apply (proph_dep_weaken _ ((ζl ++ ηl1) ++ (ζl ++ ηl2))); [set_solver|].
        apply (proph_dep_constr2 pair); [by apply Hdep1|by apply Hdep2].
      + iApply view_tguards_app.
        * iApply (view_tguards_mono with "[] T1"); [lia|lia|]. iApply lft_incl_inter_mono_l.
        * iApply (view_tguards_mono with "[] T2"); [lia|lia|]. iApply lft_incl_inter_mono_r.
    - iDestruct "V" as "#V".
      iDestruct (view_leaf_shrblk_tguards κ m ty α x d g tid l with "LFT Incl V") as "#T".
      iFrame "V". iExists (ξl x). iFrame "T". iPureIntro. intros ζl _.
      rewrite prfn_den_in. eapply proph_dep_weaken; [|apply syn_indep]. set_solver.
    - destruct (psum_proj i x.1) as [y|] eqn:Hy; last first.
      { by rewrite /prfn_dummy /view_sum /=. }
      iEval (rewrite /view_sum /prfn_sum psum_proj_pinj) in "V".
      iDestruct "V" as "(#G1 & V & #G2)".
      iAssert (κ ⊑ ty_lft (lty_fold lt))%I as "#Incl'".
      { iApply (llftl_incl_trans with "Incl"). iApply lty_lft_sum. }
      iDestruct (IH with "LFT Incl' V") as "[V (%ηl & %Hdep & #T)]".
      iSplitL "V". { rewrite /view_sum /prfn_sum psum_proj_pinj. by iFrame "G1 V G2". }
      iExists ηl. iFrame "T". iPureIntro.
      intros ζl. change (prfn_rsv (prfn_sum i (lty_rfn lt y ζm (false :: q)) x.2) ζl →
        prfn_den (prfn_sum i (lty_rfn lt y ζm (false :: q)) x.2) ./ ζl ++ ηl).
      rewrite prfn_rsv_sum prfn_den_sum. intros Hr.
      apply (proph_dep_constr (λ a, (pinj i a, x.2))). by apply Hdep.
    - iDestruct "V" as "[#V %Hv]".
      iDestruct (view_leaf_unblocked_tguards κ m (shr_bor κ' (lty_fold lt)) x d g tid l
        with "LFT Incl V") as "#T".
      iFrame "V". iSplit; [done|]. iExists (ξl x). iSplit.
      + iPureIntro. intros ζl _.
        eapply proph_dep_weaken; [|apply (syn_indep x)]. set_solver.
      + iApply (view_tguards_mono with "[] T"); [lia|lia|]. iApply llftl_intersect_incl_l.
    - done.
    - done.
  Qed.
End view_laws.

(** * Sharing a place into its view *)

Section share_view.
  Context `{!typeG Σ}.

  (** Taking [m] steps to remove [m] laters in front of the contents of a borrow. *)
  Lemma llftl_bor_laterN_step E κ G P m :
    Timeless G → ↑Nllft ⊆ E →
    llft_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗ G -∗ &{κ} (▷^m P) ={E}=∗
      |={E}▷=>^m |={E}=> G ∗ &{κ} P.
  Proof.
    iIntros (??) "#LFT #Gκ G Bor". iInduction m as [|m IH] forall "G Bor"; simpl.
    - by iFrame.
    - iMod (llftl_bor_later_step with "LFT Gκ G Bor") as "Upd"; [done..|].
      iModIntro. iModIntro. iNext. iMod "Upd" as "[G Bor]". by iApply ("IH" with "G Bor").
  Qed.

  (** Running a guarded update inside a borrow at [κ] by taking a step (instead of a
      later credit, as [llftl_bor_guarded_upd]). *)
  Lemma llftl_bor_guarded_upd_step E M κ P Q G :
    Timeless G → ↑Nllft ⊆ E → M ⊆ E →
    llft_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗ (@[κ] &&{↑NllftG}&&> P) -∗ G -∗
    &{κ} (guarded_upd M P Q) ={E}=∗ ▷ |={E}=> &{κ} Q ∗ G.
  Proof.
    iIntros (???) "#LFT #Gk #κP G Bor".
    iMod (fractional.frac_split_guard_in_half with "G Gk") as (γ) "[H1 [H2 [#Gh #Back]]]";
      [solve_ndisj|].
    iMod (llftl_bor_acc_guarded with "LFT Bor Gh H1") as "[Upd Close]"; [done|].
    iModIntro. iNext.
    iMod (guarded_upd_run M E P Q with "[] H2 Upd") as "[H2 Q]"; [done| |].
    { iApply (guards_transitive with "Gh κP"). }
    iDestruct ("Close" $! Q with "[Q]") as "Close".
    { iSplitR; [|by iNext]. iIntros "!> Q !> !>". iApply guarded_upd_intro. by iModIntro. }
    iMod (fupd_mask_mono with "Close") as "[$ H1]"; [done|].
    iApply (fupd_mask_mono with "(Back H1 H2)"). solve_ndisj.
  Qed.

  (** The view of a pointer cell, from a borrow of its points-to and a guard of its
      cells. *)
  Lemma ptr_cell_view E κ (l: cloc) (v: val) k :
    ↑Nllft ⊆ E →
    llft_ctx -∗ (@[κ] &&{↑NllftG; k+1}&&> l #↦∗_) -∗ &{κ} (l #↦!∗ [FVal v]) ={E}=∗
      @[κ] &&{↑NllftG; k+1}&&> l.1 ↦[^ l.2]∗ [v].
  Proof.
    iIntros (?) "#LFT #Gc Pt". iMod (llftl_bor_guard with "LFT Pt") as "#Pt"; [done|].
    iModIntro. iApply guard_cloc_combine; [done|].
    iApply (lguards_weaken_later with "Pt"). lia.
  Qed.

  (** Sharing an unblocked leaf. *)
  Lemma leaf_share_view {𝔄} κ m (ty: type 𝔄) x d g g' tid l G E :
    Timeless G → lazyE ⊆ E → g ≤ g' →
    llft_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗ κ ⊑ ty_lft ty -∗
    (@[κ] &&{↑NllftG; g'+1}&&> l #↦∗_) -∗ G -∗
    &{κ} (l #↦!∗ ty.(ty_phys) x tid ∗ ▷^m ty.(ty_gho_own) x d g tid) ={E}=∗
      |={E}▷=>^(m + d + 1) |={E}=> G ∗ view_leaf κ m ty PatLeaf (inl (PlaceIn x)) d g' tid l.
  Proof.
    iIntros (???) "#LFT #Gκ #Incl #Gc G Bor".
    have ?: ↑Nllft ⊆ E by (trans lazyE; [rewrite /lazyE; solve_ndisj|done]).
    iMod (llftl_sep_split with "LFT Bor") as "[Pt Bor]"; [done|].
    iMod (llftl_bor_guard with "LFT Pt") as "#Pt"; [done|].
    iMod (llftl_bor_laterN_step with "LFT Gκ G Bor") as "Upd"; [done..|].
    rewrite -Nat.add_assoc. iApply step_fupdN_add. iModIntro.
    iApply (step_fupdN_wand with "Upd"). iIntros "Upd". rewrite (Nat.add_1_r d) /=.
    iMod "Upd" as "[G Bor]".
    iMod (llftl_bor_guarded_extract _ _ _ _ (ty.(ty_gho_pers) x d g tid) with "LFT Gκ G Bor []")
      as "(G & Bor & Pers)"; [done| |].
    { iIntros "!> Gho". iApply (ty_gho_pers_impl with "Gho"). }
    iModIntro. iNext. iDestruct "Pers" as "#Pers".
    iMod (ty_share with "LFT Incl Pers Gκ G Bor") as "Shr"; [rewrite /lazyE in H0; solve_ndisj|].
    iModIntro. iApply (step_fupdN_wand with "Shr"). iIntros ">[$ #Shr] !>".
    rewrite /view_leaf. iExists x. iSplit; [done|]. iSplit.
    - iApply guard_cloc_combine_fancy; [done|]. iApply (lguards_weaken_later with "Pt"). lia.
    - iSplit; [by iApply (ty_shr_depth_mono with "Shr")|].
      by iApply (ty_gho_pers_depth_mono with "Pers").
  Qed.
End share_view.

(** * Unnesting a reserved prophetic borrow *)

Section unnest.
  Context `{!typeG Σ}.

  (** As [proph_bor_tok_share_gen], for a reserved observer: the body of the inner
      borrow, pinned by [Ex], is unnested (there is no token guard: the prophecy
      variable is reserved). *)
  Lemma proph_bor_tok_rsv_unnest E κ κ' ξ x idx ζl (P: pv_val ξ → pv_proph ξ → iProp Σ)
      (Ex P0: iProp Σ) (Φ: pv_proph ξ → iProp Σ) :
    ↑Nllft ⊆ E →
    llft_ctx -∗ proph_idx_bor_gen κ ξ idx P -∗
    ▷ □ (∀ wπ, (Ex ∗ P x wπ) ↔ (Φ wπ ∗ P0)) -∗
    &{κ'} (proph_bor_tok_rsv ξ x idx ζl ∗ Ex) ={E}=∗ &{κ' ⊓ κ} P0.
  Proof.
    iIntros (?) "#LFT #IBor #Iff Bor". rewrite proph_bor_tok_rsv_unfold proph_idx_bor_gen_unfold.
    iDestruct (llftl_bor_iff _ _ ((.VOR[ξ;ζl] x ∗ Ex) ∗ idx_bor_tok idx) with "[] Bor") as "Bor".
    { iIntros "!> !>". iSplit; [iIntros "[[$ $] $]"|iIntros "[[$ $] $]"]. }
    iMod (llftl_sep_split with "LFT Bor") as "[VoBor TokBor]"; [done|].
    iMod (llftl_idx_bor_unnest with "LFT IBor TokBor") as "Body"; [done|].
    iDestruct (llftl_bor_shorten _ (κ' ⊓ κ) with "[] Body") as "Body".
    { iApply llftl_incl_glb; [iApply llftl_intersect_incl_r|iApply llftl_intersect_incl_l]. }
    iDestruct (llftl_bor_shorten _ (κ' ⊓ κ) with "[] VoBor") as "VoBor".
    { iApply llftl_intersect_incl_l. }
    iMod (llftl_sep_join with "LFT VoBor Body") as "Bor"; [done|].
    iDestruct (llftl_bor_iff _ _ ((.VOR[ξ;ζl] x ∗ ∃ wπ, .PC[ξ] x wπ ∗ Φ wπ) ∗ P0)
      with "[] Bor") as "Bor".
    { iIntros "!> !>". iSplit.
      - iIntros "[[Vo Ex] Body]". iDestruct "Body" as (x' wπ) "[Pc P]".
        iDestruct (uniq_rsv_agree with "Vo Pc") as %<-.
        iDestruct ("Iff" $! wπ) as "[I1 _]".
        iDestruct ("I1" with "[$Ex $P]") as "[Φ $]". iFrame "Vo". iExists wπ. iFrame.
      - iIntros "[[Vo (%wπ & Pc & Φ)] P0]".
        iDestruct ("Iff" $! wπ) as "[_ I2]".
        iDestruct ("I2" with "[$Φ $P0]") as "[Ex P]".
        iFrame "Vo Ex". iExists x, wπ. iFrame. }
    iMod (llftl_sep_split with "LFT Bor") as "[_ $]"; [done|]. done.
  Qed.

  (** The body of a compound place in [Uniq] mode, pinned by the ghost variable of the
      state and the token of the owner of the compound place. *)
  Lemma cpd_gbody_pin {𝔄} κp γ γf (ty: type 𝔄)
      (node: lpat → prfn 𝔄 → nat → nat → thread_id → cloc → iProp Σ) p r x₀ d g tid l :
    ⊢ □ (∀ wπ, ((ghost_var γ (1/2) (lstate p r) ∗ cpd_tok γf) ∗
        cpd_gbody κp γf ty node tid l (uniq_cell x₀ d g γ) wπ) ↔
      ((⌜∀ π, (wπ π).1 = prfn_den r π⌝ ∗ ghost_var γ (1/2) (lstate p r) ∗ cpd_tok γf) ∗
        (pat_ok κp p ∗ ghost_var γ (1/2) (lstate p r) ∗
         guarded_upd lazyE @[ty_lft ty] (⧖(S d `max` g) ∗ node p r d g tid l)))).
  Proof.
    iIntros "!>" (wπ). iSplit.
    - iIntros "([Gh Tf] & [Body|[Tf' _]])"; [|by iDestruct (cpd_tok_excl with "Tf Tf'") as "[]"].
      rewrite cpd_body_cell. iDestruct "Body" as (p1 r1) "(Ok & % & Gh' & Upd)".
      iDestruct (ghost_var_agree with "Gh Gh'") as %[<- <-]%lstate_inj.
      by iFrame.
    - iIntros "[(% & Gh & Tf) (Ok & Gh' & Upd)]". iFrame "Gh Tf". iLeft.
      rewrite cpd_body_cell. iExists p, r. by iFrame.
  Qed.
End unnest.

(** * The sharing of a place into its view *)

Section lty_share_view.
  Context `{!typeG Σ}.

  (** The place types whose views can be produced: leaves are unblocked, blocked or
      shared-blocked; nested unique borrows have a leaf or a compound referent. *)
  Fixpoint lty_vok {𝔄} (lt: lty 𝔄) : Prop :=
    match lt with
    | OfTy _ | Blocked _ _ | ShrBlocked _ _ | ShrLty _ _ => True
    | UniqLty lt' _ =>
        (match lt' with
         | OfTy _ | ProdLty _ _ | OwnPtrLty _ _ | UniqLty _ _ | SumLty _ _ _ => True
         | _ => False
         end) ∧ lty_vok lt'
    | OwnPtrLty _ lt' | SumLty _ _ lt' => lty_vok lt'
    | ProdLty lt1 lt2 => lty_vok lt1 ∧ lty_vok lt2
    | OfRes _ | ResUniqLty _ _ => False
    end.

  (** A place in a borrow at [κ] (in [Owned m] mode) is shared into its view at [κ], in
      [m + 2*d + 3] steps (a level of nesting of unique borrows takes two steps, and
      decreases the depth). The view may be at a larger depth [g'], for which the cells
      of the location are guarded. *)
  Definition share_view_stmt {𝔄} (lt: lty 𝔄) : Prop :=
    ∀ κ m x ζm q d g g' tid l G E, Timeless G → lazyE ⊆ E → g ≤ g' →
    ⊢ llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗
      κ ⊑ ty_lft (lty_fold lt) -∗ (@[κ] &&{↑NllftG; g'+1}&&> l #↦∗_) -∗ G -∗
      &{κ} (ltype_own (Owned m) lt (lty_rfn lt x ζm q) d g tid l) ={E}=∗
        |={E}▷=>^(m + 2 * d + 3) |={E}=>
          G ∗ lty_view lt κ m (lty_pat lt) (lty_rfn lt x ζm q) d g' tid l.

  Lemma share_view_ofty {𝔄} (ty: type 𝔄) : share_view_stmt (OfTy ty).
  Proof.
    iIntros (κ m x ζm q d g g' tid l G E ???) "#LFT _ _ #Gκ #Incl #Gc G Bor".
    have ?: ↑Nllft ⊆ E by (trans lazyE; [rewrite /lazyE; solve_ndisj|done]).
    iDestruct (llftl_bor_iff _ _ (l #↦!∗ ty.(ty_phys) x tid ∗ ▷^m ty.(ty_gho_own) x d g tid)
      with "[] Bor") as "Bor".
    { iIntros "!> !>". rewrite /ltype_own /= /ofty_owned. iSplit.
      - iIntros "(%x' & -> & $)".
      - iIntros "H". iExists x. by iFrame. }
    iMod (leaf_share_view with "LFT Gκ Incl Gc G Bor") as "Upd"; [done..|].
    iModIntro. iApply (step_fupdN_nmono with "Upd"). lia.
  Qed.

  Lemma share_view_blocked {𝔄} (ty: type 𝔄) α : share_view_stmt (Blocked ty α).
  Proof.
    iIntros (κ m x ζm q d g g' tid l G E ???) "_ _ _ _ _ #Gc G Bor".
    iModIntro. iApply step_fupdN_intro; [done|]. iApply bi.laterN_intro. iModIntro.
    iFrame "G Gc". by rewrite /ltype_own /=.
  Qed.

  (** A shared-blocked leaf (at [α]): its sharing at [α] is taken out of the borrow (its
      inheritance stays in it) and viewed at [κ ⊓ α]. *)
  Lemma share_view_shrblk {𝔄} (ty: type 𝔄) α : share_view_stmt (ShrBlocked ty α).
  Proof.
    iIntros (κ m x ζm q d g g' tid l G E ???) "#LFT _ _ #Gκ #Incl #Gc G Bor".
    have ?: ↑Nllft ⊆ E by (trans lazyE; [rewrite /lazyE; solve_ndisj|done]).
    rewrite /ltype_own /= /shr_blocked_owned.
    iMod (llftl_bor_guarded_extract _ _ _ _
      ((@[α] &&{↑NllftG; g+1}&&> l #↦!∗ ty.(ty_phys) x tid) ∗ ty.(ty_shr) α x d g tid ∗
        ty.(ty_gho_pers) x d g tid)%I with "LFT Gκ G Bor []") as "(G & _ & S)"; [done| |].
    { iIntros "!> (%x' & -> & $ & $ & $ & _)". }
    iModIntro. iApply step_fupdN_intro; [done|].
    rewrite (_: m + 2 * d + 3 = S (m + 2 * d + 2)); [|lia]. simpl. iNext.
    iDestruct "S" as "#(Gpt & Shr & Pers)". iApply bi.laterN_intro. iModIntro. iFrame "G".
    rewrite /view_leaf. iExists x. iSplit; [done|]. iSplit.
    - iApply guard_cloc_combine_fancy.
      + iApply (guards_transitive_right with "[] Gc"). iApply llftl_intersect_incl_l.
      + iApply (guards_transitive_right with "[] [Gpt]"); [iApply llftl_intersect_incl_r|].
        iApply (lguards_weaken_later with "Gpt"). lia.
    - iSplit; [|by iApply (ty_gho_pers_depth_mono with "Pers")].
      iDestruct (ty_shr_lft_mono _ α (κ ⊓ α) _ 0 with "[] Shr") as "Shr'";
        [iApply llftl_intersect_incl_r|].
      iApply (ty_shr_depth_mono with "Shr'"); lia.
  Qed.

  Lemma share_view_shr {𝔄} (lt: lty 𝔄) κ' : share_view_stmt (ShrLty lt κ').
  Proof.
    iIntros (κ m x ζm q d g g' tid l G E ???) "#LFT _ _ #Gκ #Incl #Gc G Bor".
    have ?: ↑Nllft ⊆ E by (trans lazyE; [rewrite /lazyE; solve_ndisj|done]).
    set ty := shr_bor κ' (lty_fold lt).
    iDestruct (llftl_bor_iff _ _ ((l #↦!∗ ty.(ty_phys) x tid ∗ ▷^m ty.(ty_gho_own) x d g tid) ∗
      ⌜lty_vin lt x.2⌝) with "[] Bor") as "Bor".
    { iIntros "!> !>". rewrite /ltype_own /= /ofty_owned. iSplit.
      - iIntros "[(%x' & -> & $) $]".
      - iIntros "[H $]". iExists x. by iFrame. }
    iMod (llftl_sep_split with "LFT Bor") as "[Bor Bv]"; [done|].
    iMod (llftl_bor_guarded_pers with "LFT Gκ G Bv") as "[G >%Hv]"; [done|].
    iMod (leaf_share_view κ m ty with "LFT Gκ Incl Gc G Bor") as "Upd"; [done..|].
    iModIntro. iApply (step_fupdN_nmono (m + d + 1)); [lia|].
    iApply (step_fupdN_wand with "Upd"). iIntros ">[$ V] !>". by iFrame.
  Qed.
End lty_share_view.

Section lty_share_view2.
  Context `{!typeG Σ}.

  Lemma share_view_own {𝔄} n (lt: lty 𝔄) :
    share_view_stmt lt → share_view_stmt (OwnPtrLty n lt).
  Proof.
    iIntros (IH κ m x ζm q d g g' tid l G E ???) "#LFT #PROPH #UNIQ #Gκ #Incl #Gc G Bor".
    have ?: ↑Nllft ⊆ E by (trans lazyE; [rewrite /lazyE; solve_ndisj|done]).
    destruct x as [l' x]. rewrite /ltype_own /= /own_node.
    iMod (llftl_sep_split with "LFT Bor") as "[Pt Bor]"; [done|].
    iMod (ptr_cell_view with "LFT Gc Pt") as "#Gp"; [done|].
    iMod (llftl_sep_split with "LFT Bor") as "[Bd Bor]"; [done|].
    iMod (llftl_bor_guarded_pers with "LFT Gκ G Bd") as "[G >%Hd]"; [done|].
    iMod (llftl_sep_split with "LFT Bor") as "[_ Bor]"; [done|].
    iMod (IH κ (m + 1) x ζm (false :: q) (pred d) g g' tid (l', repeat [] (lty_size lt)) G E
      with "LFT PROPH UNIQ Gκ Incl [] G Bor") as "Upd"; [done..| |].
    { iEval (rewrite -heap_cloc_mapsto_empty). iApply guards_true. }
    iModIntro. iApply (step_fupdN_nmono ((m + 1) + 2 * pred d + 3)); [lia|].
    iApply (step_fupdN_wand with "Upd"). iIntros ">[$ V] !>". iFrame "Gp V". by iPureIntro.
  Qed.

  Lemma share_view_prod {𝔄1 𝔄2} (lt1: lty 𝔄1) (lt2: lty 𝔄2) :
    share_view_stmt lt1 → share_view_stmt lt2 → share_view_stmt (ProdLty lt1 lt2).
  Proof.
    iIntros (IH1 IH2 κ m x ζm q d g g' tid l G E ???) "#LFT #PROPH #UNIQ #Gκ #Incl #Gc G Bor".
    have ?: ↑Nllft ⊆ E by (trans lazyE; [rewrite /lazyE; solve_ndisj|done]).
    rewrite /ltype_own /= /prod_node.
    iMod (llftl_sep_split with "LFT Bor") as "[B1 B2]"; [done|].
    iEval (rewrite (heap_cloc_mapsto_emp_vec_app l (lty_size lt1))) in "Gc".
    iDestruct (guards_weaken_rhs_sep_l with "Gc") as "#Gc1".
    iDestruct (guards_weaken_rhs_sep_r with "Gc") as "#Gc2".
    iAssert (κ ⊑ ty_lft (lty_fold lt1))%I as "#Incl1".
    { iApply (llftl_incl_trans with "Incl"). simpl. rewrite lft_intersect_list_app.
      iApply llftl_intersect_incl_l. }
    iAssert (κ ⊑ ty_lft (lty_fold lt2))%I as "#Incl2".
    { iApply (llftl_incl_trans with "Incl"). simpl. rewrite lft_intersect_list_app.
      iApply llftl_intersect_incl_r. }
    iMod (share_par E κ G (m + 2 * d + 3) with "Gκ G [B1] [B2]") as "Upd";
      [trans lazyE; [apply lazyE_NllftG|done]|..].
    { iIntros (Hh ?) "#Hκ Hh". iApply (IH1 with "LFT PROPH UNIQ Hκ Incl1 Gc1 Hh B1"); done. }
    { iIntros (Hh ?) "#Hκ Hh". iApply (IH2 with "LFT PROPH UNIQ Hκ Incl2 Gc2 Hh B2"); done. }
    iModIntro. iApply (step_fupdN_wand with "Upd"). iIntros ">[$ [V1 V2]] !>". iFrame.
  Qed.

  Lemma share_view_sum {𝔄l} (tyl: typel 𝔄l) i (lt: lty (𝔄l !!ₗ i)) :
    share_view_stmt lt → share_view_stmt (SumLty tyl i lt).
  Proof.
    iIntros (IH κ m x ζm q d g g' tid l G E ???) "#LFT #PROPH #UNIQ #Gκ #Incl #Gc G Bor".
    have ?: ↑Nllft ⊆ E by (trans lazyE; [rewrite /lazyE; solve_ndisj|done]).
    rewrite /ltype_own lty_rfn_sum. destruct (psum_proj i x.1) as [y|] eqn:Hy; last first.
    { rewrite /= /prfn_dummy /sum_node /=.
      iMod (llftl_bor_acc_guarded with "LFT Bor Gκ G") as "[>[] _]"; done. }
    rewrite ltype_own_cp_sum_owned sum_node_sum /=.
    iMod (llftl_sep_split with "LFT Bor") as "[Tag Bor]"; [done|].
    iMod (llftl_sep_split with "LFT Bor") as "[Bor Pad]"; [done|].
    iEval (rewrite (heap_cloc_mapsto_emp_vec_app l 1)) in "Gc".
    iDestruct (guards_weaken_rhs_sep_l with "Gc") as "#Gt".
    iDestruct (guards_weaken_rhs_sep_r with "Gc") as "#Gc'".
    iEval (rewrite (heap_cloc_mapsto_emp_vec_app (cloc_skip l 1) (lty_size lt))) in "Gc'".
    iDestruct (guards_weaken_rhs_sep_l with "Gc'") as "#Gm".
    iDestruct (guards_weaken_rhs_sep_r with "Gc'") as "#Gq".
    iMod (llftl_bor_guard with "LFT Tag") as "#Tag"; [done|].
    iMod (llftl_bor_guard with "LFT Pad") as "#Pad"; [done|].
    iAssert (κ ⊑ ty_lft (lty_fold lt))%I as "#Incl'".
    { iApply (llftl_incl_trans with "Incl"). iApply lty_lft_sum. }
    iMod (IH κ m y ζm (false :: q) d g g' tid (cloc_take (cloc_skip l 1) (lty_size lt)) G E
      with "LFT PROPH UNIQ Gκ Incl' Gm G Bor") as "Upd"; [done..|].
    iModIntro. iApply (step_fupdN_wand with "Upd"). iIntros ">[$ V] !>".
    rewrite /view_sum /prfn_sum psum_proj_pinj. iFrame "V". iSplit.
    - iApply (guard_cloc_combine _ _ _ (cloc_take l 1)); [done|].
      iApply (lguards_weaken_later with "Tag"). lia.
    - iApply (guard_cloc_combine_fancy _ _ _ (cloc_skip (cloc_skip l 1) (lty_size lt)));
        [done|].
      iApply (lguards_weaken_later with "Pad"). lia.
  Qed.
End lty_share_view2.

Section lty_share_view3.
  Context `{!typeG Σ}.

  (** A nested unique borrow whose referent is a leaf: shared as [&uniq{κ'} ty] at [κ]
      (its sharing predicate gives the view of the referent at [κ ⊓ κ']). *)
  Lemma share_view_uniq_leaf {𝔄} (ty: type 𝔄) κ' : share_view_stmt (UniqLty (OfTy ty) κ').
  Proof.
    iIntros (κ m x ζm q d g g' tid l G E ???) "#LFT #PROPH #UNIQ #Gκ #Incl #Gc G Bor".
    have ?: ↑Nllft ⊆ E by (trans lazyE; [rewrite /lazyE; solve_ndisj|done]).
    destruct x as [[[[[l' x0] ξi] d0] g0] idx0].
    rewrite /ltype_own /= /uniq_node /=.
    iMod (llftl_sep_split with "LFT Bor") as "[Pt Bor]"; [done|].
    iMod (ptr_cell_view with "LFT Gc Pt") as "#Gp"; [done|].
    iMod (llftl_sep_split with "LFT Bor") as "[_ Bor]"; [done|].
    iMod (llftl_sep_split with "LFT Bor") as "[_ Bor]"; [done|].
    iMod (llftl_bor_laterN_step with "LFT Gκ G Bor") as "Upd"; [done..|].
    rewrite -!Nat.add_assoc. iApply step_fupdN_add. iModIntro.
    iApply (step_fupdN_wand with "Upd"). iIntros "Upd".
    iApply (step_fupdN_nmono (S (S (S (d + d))))); [lia|]. simpl.
    iMod "Upd" as "[G Bor]".
    iMod (llftl_bor_guarded_extract _ _ _ _
      (κ' ⊑ ty_lft ty ∗ (@[κ'] &&{↑NllftG; g+1}&&> l' #↦∗_))%I
      with "LFT Gκ G Bor []") as "(G & Bor & #Pp)"; [done| |].
    { iIntros "!> ($ & $ & _)". }
    iMod (llftl_sep_split with "LFT Bor") as "[_ Bor]"; [done|].
    iMod (llftl_sep_split with "LFT Bor") as "[_ Bor]"; [done|].
    iMod (llftl_bor_freeze with "LFT Bor") as (d1) "Bor"; [done|].
    iMod (llftl_bor_freeze with "LFT Bor") as (g1) "Bor"; [done|].
    iMod (llftl_sep_split with "LFT Bor") as "[Bp Bor]"; [done|].
    iMod (llftl_bor_guarded_pers with "LFT Gκ G Bp") as "[G >[%Hd1 %Hg1]]"; [done|].
    have ?: Inhabited Idx := populate idx_dummy.
    iDestruct (llftl_bor_iff _ _ (∃ idx, uniq_body ty x0 ξi d1 g1 idx κ' tid l')
      with "[] Bor") as "Bor".
    { iIntros "!> !>". rewrite /leaf_uniq /ofty_uniq. iSplit.
      - iIntros "(%x' & %idx & -> & B)". by iExists idx.
      - iIntros "(%idx & B)". iExists x0, idx. by iFrame. }
    iMod (llftl_bor_freeze with "LFT Bor") as (idx) "Bor"; [done|].
    set y : ~~ (uniq_borₛ 𝔄) := (l', x0, ξi, d1, g1, idx).
    iDestruct (llftl_bor_iff _ _ ((&uniq{κ'} ty)%T.(ty_gho_own) y d g tid) with "[] Bor")
      as "Bor".
    { iIntros "!>". iDestruct "Pp" as "#[I' C']". iIntros "!>". iSplit.
      - iIntros "B". iFrame "I' B C'". iPureIntro. lia.
      - by iIntros "(_ & _ & $ & _)". }
    iMod (llftl_bor_guarded_extract _ _ _ _ ((&uniq{κ'} ty)%T.(ty_gho_pers) y d g tid)
      with "LFT Gκ G Bor []") as "(G & Bor & Pers)"; [done| |].
    { iIntros "!> Gho". iApply (ty_gho_pers_impl with "Gho"). }
    iModIntro. iNext. iDestruct "Pers" as "#Pers". iDestruct "Pp" as "#[I' C']".
    iMod (ty_share (&uniq{κ'} ty)%T with "LFT Incl Pers Gκ G Bor") as "Shr";
      [rewrite /lazyE in H0; solve_ndisj|].
    iModIntro. iApply (step_fupdN_nmono (d + 2) (S (S (d + d)))); [lia|].
    iApply step_fupdN_add. iApply (step_fupdN_wand with "Shr"). iIntros "Upd".
    iApply (step_fupdN_nmono 2); [done|]. simpl. iMod "Upd" as "[G #Shr]".
    iDestruct "Shr" as (_) "(#Gpt & _ & Shr & Pers0)". simpl.
    iModIntro. iNext. iModIntro. iModIntro. iNext. iModIntro. iModIntro.
    iFrame "G". rewrite /view_uniq. iFrame "Gp I'". iExists d1, g'.
    iSplit; [iPureIntro; lia|]. rewrite /view_leaf. iExists x0. iSplit; [done|].
    iSplit; [iApply (lguards_weaken_later with "Gpt"); lia|].
    iSplit; [by iApply (ty_shr_depth_mono with "Shr")|].
    iApply (ty_gho_pers_depth_mono with "Pers0"); lia.
  Qed.
End lty_share_view3.

Section lty_share_view4.
  Context `{!typeG Σ}.

  (** A nested unique borrow whose referent is compound: its body is unnested (pinned by
      the state of the compound place), its lazy contents are run, and the referent is
      shared into its view at [κ ⊓ κ'] (two steps per level). *)
  Lemma share_view_uniq_cpd {𝔄} (lt: lty 𝔄) κ' :
    lty_is_cpd lt → share_view_stmt lt → share_view_stmt (UniqLty lt κ').
  Proof.
    iIntros (Hc IH κ m x ζm q d g g' tid l G E ???) "#LFT #PROPH #UNIQ #Gκ #Incl #Gc G Bor".
    have ?: ↑Nllft ⊆ E by (trans lazyE; [rewrite /lazyE; solve_ndisj|done]).
    destruct x as [[[[[l' x0] ξi] d0] g0] idx0].
    rewrite /ltype_own /= /uniq_node /= ltype_own_cp_uniq_cpd //.
    set r' := lty_rfn lt x0 ζm (false :: q).
    iMod (llftl_sep_split with "LFT Bor") as "[Pt Bor]"; [done|].
    iMod (ptr_cell_view with "LFT Gc Pt") as "#Gp"; [done|].
    iMod (llftl_sep_split with "LFT Bor") as "[_ Bor]"; [done|].
    iMod (llftl_sep_split with "LFT Bor") as "[_ Bor]"; [done|].
    iMod (llftl_bor_laterN_step with "LFT Gκ G Bor") as "Upd"; [done..|].
    rewrite -!Nat.add_assoc. iApply step_fupdN_add. iModIntro.
    iApply (step_fupdN_wand with "Upd"). iIntros "Upd".
    iApply (step_fupdN_nmono (S (2 * d + 2))); [lia|]. cbn [Nat.iter].
    iMod "Upd" as "[G Bor]".
    iMod (llftl_bor_guarded_extract _ _ _ _
      (κ' ⊑ ty_lft (lty_fold lt) ∗ (@[κ'] &&{↑NllftG; g+1}&&> l' #↦∗_))%I
      with "LFT Gκ G Bor []") as "(G & Bor & #Pp)"; [done| |].
    { iIntros "!> ($ & $ & _)". }
    iMod (llftl_sep_split with "LFT Bor") as "[_ Bor]"; [done|].
    iMod (llftl_sep_split with "LFT Bor") as "[_ Bor]"; [done|].
    iMod (llftl_bor_freeze with "LFT Bor") as (d1) "Bor"; [done|].
    iMod (llftl_bor_freeze with "LFT Bor") as (g1) "Bor"; [done|].
    iMod (llftl_sep_split with "LFT Bor") as "[Bp Bor]"; [done|].
    iMod (llftl_bor_guarded_pers with "LFT Gκ G Bp") as "[G >[%Hd1 %Hg1]]"; [done|].
    have ?: Inhabited (~~𝔄) := populate x0. have ?: Inhabited Idx := populate idx_dummy.
    rewrite /cpd_own.
    iMod (llftl_bor_freeze with "LFT Bor") as (x₀) "Bor"; [done|].
    iMod (llftl_bor_freeze with "LFT Bor") as (κp) "Bor"; [done|].
    iMod (llftl_bor_freeze with "LFT Bor") as (γ) "Bor"; [done|].
    iMod (llftl_bor_freeze with "LFT Bor") as (γf) "Bor"; [done|].
    iMod (llftl_bor_freeze with "LFT Bor") as (idx) "Bor"; [done|].
    iMod (llftl_bor_freeze with "LFT Bor") as (ζl) "Bor"; [done|].
    set node := ltype_own_cp false lt (Owned 0).
    set P := cpd_gbody κp γf (lty_fold lt) node tid l'.
    set c := uniq_cell x₀ d1 g1 γ.
    iMod (llftl_bor_guarded_extract _ _ _ _
      (proph_idx_bor_gen κ' (uniq_prvar x₀ ξi) idx P)%I
      with "LFT Gκ G Bor []") as "(G & Bor & #IBor)"; [done| |].
    { iIntros "!> (_ & _ & _ & _ & _ & _ & $)". }
    iDestruct (llftl_bor_iff _ _ ((proph_bor_tok_rsv (uniq_prvar x₀ ξi) c idx ζl ∗
      (ghost_var γ (1/2) (lstate (lty_pat lt) r') ∗ cpd_tok γf)) ∗
      (uniq_pat_lft κ' κp ∗ ⌜prfn_rsv r' ζl⌝ ∗ ⧗1 ∗
        proph_idx_bor_gen κ' (uniq_prvar x₀ ξi) idx P)) with "[] Bor") as "Bor".
    { iIntros "!> !>". iSplit.
      - iIntros "($ & $ & $ & $ & $ & $ & $)".
      - iIntros "[($ & $ & $) ($ & $ & $ & $)]". }
    iMod (llftl_sep_split with "LFT Bor") as "[Bor _]"; [done|].
    iModIntro. iNext. iDestruct "IBor" as "#IBor". iDestruct "Pp" as "#[I' C']".
    iMod (proph_bor_tok_rsv_unnest E κ' κ (uniq_prvar x₀ ξi) c idx ζl P _ _
      (λ wπ, ⌜∀ π, (wπ π).1 = prfn_den r' π⌝ ∗ ghost_var γ (1/2) (lstate (lty_pat lt) r') ∗
        cpd_tok γf)%I with "LFT IBor [] Bor") as "Bor"; [done| |].
    { iNext. iApply cpd_gbody_pin. }
    iMod (llftl_sep_split with "LFT Bor") as "[_ Bor]"; [done|].
    iMod (llftl_sep_split with "LFT Bor") as "[_ Bor]"; [done|].
    iAssert (G &&{↑NllftG}&&> @[κ ⊓ κ'])%I as "#Gκκ".
    { iApply (guards_transitive with "Gκ"). iApply llftl_incl_glb; [iApply guards_refl|].
      iApply llftl_incl_trans; [iApply "Incl"|]. iApply llftl_intersect_incl_l. }
    iAssert (@[κ ⊓ κ'] &&{↑NllftG}&&> @[ty_lft (lty_fold lt)])%I as "#Gty".
    { iApply llftl_incl_trans; [iApply llftl_intersect_incl_r|]. iApply "I'". }
    iMod (llftl_bor_guarded_upd_step with "LFT Gκκ Gty G Bor") as "Upd";
      [done|rewrite /lazyE in H0; solve_ndisj|].
    iModIntro. iApply (step_fupdN_nmono (S (2 * d1 + 3))); [lia|]. cbn [Nat.iter].
    iModIntro. iNext. iMod "Upd" as "[Bor G]".
    iMod (llftl_sep_split with "LFT Bor") as "[_ Bor]"; [done|].
    iAssert (κ ⊓ κ' ⊑ ty_lft (lty_fold lt))%I as "#Incl2".
    { iApply "Gty". }
    iAssert (@[κ ⊓ κ'] &&{↑NllftG; g'+1}&&> l' #↦∗_)%I as "#Gc2".
    { iApply guards_transitive_right; [iApply llftl_intersect_incl_r|].
      iApply (lguards_weaken_later with "C'"). lia. }
    iMod (IH (κ ⊓ κ') 0 x0 ζm (false :: q) d1 g1 g' tid l' G E _ H0 ltac:(lia)
      with "LFT PROPH UNIQ Gκκ Incl2 Gc2 G [Bor]") as "Upd".
    { rewrite /ltype_own. iExact "Bor". }
    iModIntro. iApply (step_fupdN_wand with "Upd"). iIntros ">[$ V] !>".
    rewrite /view_uniq. iFrame "Gp I'". iExists d1, g'. iSplit; [iPureIntro; lia|].
    iExact "V".
  Qed.

  Lemma lty_share_view {𝔄} (lt: lty 𝔄) : lty_vok lt → share_view_stmt lt.
  Proof.
    induction lt as [𝔄 ty|𝔄 ty α|𝔄 lt IH κ'|𝔄 n lt IH|𝔄 𝔅 lt1 IH1 lt2 IH2|𝔄 ty α|
      𝔄l tyl i lt IH|𝔄 lt IH κ'|𝔄 ty|𝔄 lt IH κ']; simpl; intros Hv; try done.
    - apply share_view_ofty.
    - apply share_view_blocked.
    - destruct Hv as [Hc Hv]. destruct lt; try done;
        [apply share_view_uniq_leaf|apply share_view_uniq_cpd; [done|by apply IH]..].
    - apply share_view_own, IH, Hv.
    - destruct Hv. apply share_view_prod; [by apply IH1|by apply IH2].
    - apply share_view_shrblk.
    - apply share_view_sum, IH, Hv.
    - apply share_view_shr.
  Qed.
End lty_share_view4.
