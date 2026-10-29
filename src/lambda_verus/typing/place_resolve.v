(** * Resolving and dropping places

  This file adds general rules for giving up a place element (see
  [~/verus-belt-phase3-design.md], section "Resolve and drop").

  ** Places rooted at a unique borrow

  [type_resolve_vplace_uniq_instr] gives up [p ◁ₗ{κ} lt] (a place rooted at the value of a
  unique borrow, [vplace.v]) for any compound place type [lt]
  whose leaves are unblocked ([OfTy], also below owned pointers and sums), blocked
  ([Blocked]) or shared-blocked ([ShrBlocked], see below), and whose nested unique
  borrows ([UniqLty]) have only blocked leaves
  ([lty_uniq_rslv]). The prophecy variable of the outer borrow is pre-resolved to the
  current value of the place: the final values of the reborrows at the blocked leaves,
  the current values at the unblocked leaves. This generalizes [tctx_drop_vplace_uniq]
  (all leaves blocked), without reborrowing the unblocked leaves first. No condition on
  the types of the leaves is needed: their contents are not consumed (they go back to
  the lender of the outer borrow, at the same values).

  The proof does not need the prophecy tokens of the current values of the unblocked
  leaves at the moment of the pre-resolution: each unblocked leaf gets a fresh prophecy
  variable [η] ([ltype_owned_rslv]); the outer prophecy is pre-resolved (through its
  reservation, [proph_idx_bor_gen_preresolve_rsv_acc]) to the denotation of the
  refinement in which the unblocked leaves are refined by their [η]s (whose tokens are
  fresh); then each [η] is resolved to the current value of its leaf, with tokens
  obtained by sharing the contents of the leaf at a fresh lifetime
  ([proph_eqz_obs_by_share]), and the body of the outer borrow is closed at the
  refinement with the [η]s (whose leaves are related to their contents by the
  observations). Sharing a leaf costs later credits depending on its depth, so the
  instruction takes one program step per unblocked leaf ([skipn], [ctask]).

  Shared-blocked leaves ([ShrBlocked]) are supported while their shared lifetimes are
  alive ([lty_shr_lfts], e.g. a returned shared reference to a field): their values do
  not change, and the tokens of the prophecies in them are obtained from their sharing
  predicates ([ty_shr_guard_proph], with the persistent predicate kept by the leaf, see
  [shr_blocked_owned]), guarded by the shared lifetime (from [L]); a fresh variable is
  resolved to the current value as for an unblocked leaf.

  ** Places rooted at an owned location

  [resolve_tctx_cons_oplace] and [type_resolve_oplace_instr] resolve (and leak)
  [p ◁ₗown{n} lt] for any place type, with a resolution condition per unblocked leaf
  ([lty_resolve], from [resolve] of the leaf's type; moved-out leaves [OfTy (↯ n)] need
  nothing); blocked and shared-blocked leaves are forgotten (their lender keeps the
  borrow, and gets the contents back at the end of the lifetime). [type_drop_oplace_instr]
  in addition frees the memory of the place and, recursively, the pointees of its
  unfolded owned pointers ([OwnPtrLty], [drop_boxes]), for places none of whose leaves
  (outside the pointees) is blocked or shared ([lty_freeb]): the memory of such a leaf
  is lent, so it must not be freed (a pointee with a blocked leaf is leaked instead,
  [own_freeb]). Owned pointers in unblocked leaves ([OfTy (own_ptr …)]) are resolved
  by their type and their pointees leaked, as by [type_delete_instr].

  ** Places below shared references

  These are plain [p ◁ &shr{κ} ty] elements (see [place_shr.v]); they are dropped as
  any element ([resolve_just]). *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From lrust.lang Require Import proofmode.
From lrust.lang.lib Require Import new_delete.
From lrust.util Require Import update.
From lrust.typing Require Export type ltype lpath place_own.
From lrust.typing Require Import type_context programs programs_util lft_contexts
  uniq_util uniq_bor product own uninit freeable_util.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

(** * Tasks paid by later credits, one batch per program step *)

Section ctask.
  Context `{!typeG Σ}.

  (** [ctask c k R]: [R] can be obtained given [k] batches of [c] later credits. *)
  Fixpoint ctask (c k: nat) (R: iProp Σ) : iProp Σ :=
    match k with
    | O => |={⊤}=> R
    | S k => |={⊤}=> (£c -∗ ctask c k R)
    end%I.

  Lemma ctask_fupd c k R : (|={⊤}=> ctask c k R) ⊢ ctask c k R.
  Proof. destruct k; simpl; iIntros ">$". Qed.

  Lemma ctask_mono c k R R' : (R ={⊤}=∗ R') -∗ ctask c k R -∗ ctask c k R'.
  Proof.
    induction k as [|k IH]; simpl; iIntros "W >T"; [by iApply "W"|].
    iIntros "!> £". iApply (IH with "W"). by iApply "T".
  Qed.

  Lemma ctask_sep c k1 k2 R1 R2 :
    ctask c k1 R1 -∗ ctask c k2 R2 -∗ ctask c (k1 + k2) (R1 ∗ R2).
  Proof.
    induction k1 as [|k1 IH]; simpl.
    - iIntros "R1 T2". iApply (ctask_mono with "[R1] T2"). iIntros "R2". iMod "R1". by iFrame.
    - iIntros "T1 T2". iMod "T1". iIntros "!> £". iApply (IH with "[T1 £] T2"). by iApply "T1".
  Qed.

  Lemma ctask_weaken c c' k R : c ≤ c' → ctask c k R -∗ ctask c' k R.
  Proof.
    intros ?. induction k as [|k IH]; simpl; iIntros ">T !>"; [done|]. iIntros "£".
    iApply IH. iApply "T". by iApply (lc_weaken with "£").
  Qed.

  (** A sequence of [k] program steps. *)
  Fixpoint skipn (k: nat) : expr :=
    match k with O => #☠ | S k => Skip;; skipn k end%E.

  Global Instance skipn_closed k : Closed [] (skipn k).
  Proof. induction k; simpl; [done|]. by apply _. Qed.

  (** Each step gives a batch of later credits (from the persistent time receipt). *)
  Lemma wp_skipn_ctask k c D R Φ :
    c ≤ advance_credits D →
    time_ctx -∗ ⧖D -∗ ctask c k R -∗ (R -∗ Φ #☠) -∗ WP skipn k {{ Φ }}.
  Proof.
    iIntros (Hc) "#TIME ⧖ T HΦ". iInduction k as [|k IH] forall (D Hc); simpl.
    - iMod "T". iApply wp_value. by iApply "HΦ".
    - iMod "T". wp_bind Skip.
      iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj|].
      iIntros "£ ⧖S". wp_let. wp_let.
      iApply ("IH" $! (S D) with "[] ⧖S [T £] HΦ").
      { iPureIntro. etrans; [done|]. apply advance_credits_mono. lia. }
      iApply "T". by iApply (lc_weaken with "£").
  Qed.
End ctask.

(** * Resolving the unblocked leaves of a place in [Owned] mode *)

Section rslv.
  Context `{!typeG Σ}.

  (** The place types that can be resolved below the root of a unique borrow: leaves
      are unblocked, blocked or shared-blocked (while their shared lifetimes are alive,
      [lty_shr_lfts]); nested unique borrows have only blocked leaves. *)
  Fixpoint lty_uniq_rslv {𝔄} (lt: lty 𝔄) : Prop :=
    match lt with
    | OfTy _ | Blocked _ _ | ShrBlocked _ _ => True
    | UniqLty lt _ => lty_blk_all lt
    | OwnPtrLty _ lt | SumLty _ _ lt => lty_uniq_rslv lt
    | ProdLty lt1 lt2 => lty_uniq_rslv lt1 ∧ lty_uniq_rslv lt2
    (* Not supported (fold the shared reference back first). *)
    | ShrLty _ _ => False
    (* Resolved places are only in the owned part of a place. *)
    | OfRes _ | ResUniqLty _ _ => False
    end.

  (** The lifetimes of the shared-blocked leaves. *)
  Fixpoint lty_shr_lfts {𝔄} (lt: lty 𝔄) : list lft :=
    match lt with
    | ShrBlocked _ α => [α]
    | OwnPtrLty _ lt | SumLty _ _ lt => lty_shr_lfts lt
    | ProdLty lt1 lt2 => lty_shr_lfts lt1 ++ lty_shr_lfts lt2
    | _ => []
    end.

  (** The number of unblocked and shared-blocked leaves (outside nested unique
      borrows). *)
  Fixpoint lty_nunblk {𝔄} (lt: lty 𝔄) : nat :=
    match lt with
    | OfTy _ | ShrBlocked _ _ => 1
    | OwnPtrLty _ lt | SumLty _ _ lt => lty_nunblk lt
    | ProdLty lt1 lt2 => lty_nunblk lt1 + lty_nunblk lt2
    | _ => 0
    end.

  (** The later credits for resolving one unblocked leaf at depth [d] below [m] owned
      pointers, with [m + d ≤ D] ([proph_eqz_obs_by_share], and [m] to strip the laters
      of the ghost ownership). *)
  Definition rslv_cost (D g: nat) : nat :=
    D + (D + D*(g+2) + (0 + (D+1)*(g+1)) + 1 + 1).

  Lemma rslv_cost_mono D g D' g' : D ≤ D' → g ≤ g' → rslv_cost D g ≤ rslv_cost D' g'.
  Proof. rewrite /rslv_cost. nia. Qed.

  (** Resolving the unblocked leaves of a place in [Owned m] mode, in two phases. First,
      a fresh prophecy variable is allocated for each unblocked leaf; [r'] is the
      refinement of the place in which these leaves are refined by their variables, so
      that its denotation depends only on the variables of a reservation of the
      original refinement and on the fresh ones ([ηl], whose tokens are given). Then,
      given the tokens back (after the pre-resolution of an outer prophecy to the
      denotation of [r']) and the ownership of the place, each fresh variable is
      resolved to the current value of its leaf (sharing it at a fresh lifetime, one
      batch of later credits per leaf), which shows that the denotations of [r'] and
      of the original refinement agree, and the place is owned at [r']. *)
  Lemma ltype_owned_rslv {𝔄} (lt: lty 𝔄) x ζm q :
    lty_uniq_rslv lt →
    proph_ctx ={⊤}=∗ ∃ (r': prfn 𝔄) (ηl: list proph_var),
      ⌜∀ ζl, prfn_rsv (lty_rfn lt x ζm q) ζl → prfn_den r' ./ ζl ++ ηl⌝ ∗ 1:+[ηl] ∗
      (∀ G m d g tid l, ⌜Timeless G⌝ -∗ llft_ctx -∗ proph_ctx -∗
        (G &&{↑NllftG}&&> @[ty_lft (lty_fold lt)]) -∗
        ([∗ list] α ∈ lty_shr_lfts lt, G &&{↑NllftG}&&> @[α]) -∗ G -∗ 1:+[ηl] -∗
        ltype_own (Owned m) lt (lty_rfn lt x ζm q) d g tid l -∗
        ctask (rslv_cost (m + d) g) (lty_nunblk lt)
          (⟨π, prfn_den r' π = prfn_den (lty_rfn lt x ζm q) π⟩ ∗ G ∗
           ltype_own (Owned m) lt r' d g tid l)).
  Proof.
    induction lt as [𝔄 ty|𝔄 ty α|𝔄 lt IH κ'|𝔄 n lt IH|𝔄 𝔅 lt1 IH1 lt2 IH2|𝔄 ty α|
      𝔄l tyl i lt IH|𝔄 lt IH κ'|𝔄 ty|𝔄 lt IH κ'] in x, q |- *; intros Hr; iIntros "#PROPH";
      simpl in Hr; try done.
    - (* An unblocked leaf: a fresh variable. *)
      iMod (proph_intro (uniq_cell_tyi x) ∅ with "PROPH") as (ηi) "[_ η]"; [solve_ndisj|].
      set η := uniq_prvar x ηi.
      iModIntro. iExists (inl (PlaceGhost x ηi)), [η].
      iSplit.
      { iPureIntro. intros ζl _. rewrite prfn_den_inl.
        eapply proph_dep_weaken; [|apply place_ghost_dep]. set_solver. }
      iSplitL "η"; [by iApply proph_tok_singleton|].
      iIntros (G m d g tid l ?) "#LFT _ #Gty _ G η Own".
      iDestruct (proph_tok_singleton with "η") as "η".
      rewrite /ltype_own /= /leaf_owned_s /leaf_owned /=.
      iDestruct "Own" as (x' Hx) "[Pt Gho]". simpl in Hx. subst x'.
      iIntros "!> £".
      iDestruct (lc_weaken (m + (d + d*(g+2) + (0 + (d+1)*(g+1)) + 1 + 1)) with "£")
        as "[£m £]"; [rewrite /rslv_cost; nia|].
      iMod (lc_fupd_elim_laterN with "£m Gho") as "Gho".
      iDestruct (proph_eqz_token η
        (λ π, (vπ x π, (1%positive, (1%positive, 1%positive))))
        with "PROPH η") as "Eqz".
      iDestruct (proph_eqz_fst_const with "Eqz") as "Eqz".
      iMod (proph_eqz_obs_by_share ty with "LFT Gty G £ Eqz Gho") as "(#Obs & $ & Gho)".
      iModIntro. iSplitR.
      { iApply (proph_obs_impl with "Obs")=> π /= Heq. by rewrite prfn_den_inl prfn_den_in. }
      iExists x. iFrame "Pt". iSplitR; [|by iNext].
      iNext. by iApply proph_eqz_obs.
    - (* A blocked leaf: nothing to do. *)
      iModIntro. iExists (lty_rfn (Blocked ty α) x ζm q), []. iSplit.
      { iPureIntro. intros ζl. cbn [lty_rfn]. rewrite prfn_rsv_inl prfn_den_inl app_nil_r.
        done. }
      iSplit; [done|]. iIntros (G m d g tid l ?) "_ _ _ _ $ _ $ /=".
      iModIntro. by iApply proph_obs_true.
    - (* A nested unique borrow whose leaves are all blocked: nothing to do. *)
      iModIntro. iExists (lty_rfn (UniqLty lt κ') x ζm q), []. iSplit.
      { iPureIntro. intros ζl Hrsv. rewrite app_nil_r.
        by apply (lty_blk_all_dep (UniqLty lt κ')). }
      iSplit; [done|]. iIntros (G m d g tid l ?) "_ _ _ _ $ _ $ /=".
      iModIntro. by iApply proph_obs_true.
    - (* An owned pointer. *)
      iMod (IH x.2 (false :: q) with "PROPH") as (r' ηl Hdep) "[ηl Cont]"; [done|].
      iModIntro. iExists (inr (x.1, r')), ηl. iFrame "ηl". iSplit.
      { iPureIntro. intros ζl Hrsv. apply (proph_dep_constr (pair x.1)). by apply Hdep. }
      iIntros (G m d g tid l ?) "#LFT _ #Gty #Gα G ηl Own".
      rewrite /ltype_own /=. iDestruct "Own" as "(Pt & %Hd & Fr & Own)".
      iDestruct ("Cont" $! G (m + 1) (pred d) g tid with "[//] LFT PROPH Gty Gα G ηl Own")
        as "T".
      iDestruct (ctask_weaken _ (rslv_cost (m + d) g) with "T") as "T";
        [apply rslv_cost_mono; lia|].
      iApply (ctask_mono with "[Pt Fr] T"). iIntros "(#Obs & $ & Own) !>".
      iFrame "Pt Fr Own". iSplit; [|done].
      iApply (proph_obs_impl with "Obs")=> π /= ->. done.
    - (* A product. *)
      destruct Hr as [Hr1 Hr2].
      iMod (IH1 x.1 (false :: q) with "PROPH") as (r1 ηl1 Hdep1) "[ηl1 Cont1]"; [done|].
      iMod (IH2 x.2 (true :: q) with "PROPH") as (r2 ηl2 Hdep2) "[ηl2 Cont2]"; [done|].
      iModIntro. iExists (inr (r1, r2)), (ηl1 ++ ηl2). iSplit.
      { iPureIntro. intros ζl [Hrsv1 Hrsv2].
        apply (proph_dep_weaken _ ((ζl ++ ηl1) ++ (ζl ++ ηl2))); [set_solver|].
        apply (proph_dep_constr2 pair); [by apply Hdep1|by apply Hdep2]. }
      iSplitL "ηl1 ηl2"; [iApply big_sepL_app; iFrame|].
      iIntros (G m d g tid l ?) "#LFT _ #Gty #Gα G ηl Own".
      iDestruct (big_sepL_app with "ηl") as "[ηl1 ηl2]".
      iDestruct (big_sepL_app with "Gα") as "[Gα1 Gα2]".
      rewrite /ltype_own /=. iDestruct "Own" as "[Own1 Own2]".
      iApply ctask_fupd.
      iMod (fractional.frac_split_in_half with "G") as (γ) "[H1 [H2 [#Gh #Back]]]";
        [solve_ndisj|].
      iAssert (fractional.half γ &&{↑NllftG}&&> @[ty_lft (lty_fold lt1)])%I as "#Gty1".
      { iApply (guards_transitive with "Gh"). iApply (guards_transitive with "Gty").
        rewrite /= lft_intersect_list_app. iApply llftl_intersect_incl_l. }
      iAssert (fractional.half γ &&{↑NllftG}&&> @[ty_lft (lty_fold lt2)])%I as "#Gty2".
      { iApply (guards_transitive with "Gh"). iApply (guards_transitive with "Gty").
        rewrite /= lft_intersect_list_app. iApply llftl_intersect_incl_r. }
      iAssert ([∗ list] α ∈ lty_shr_lfts lt1, fractional.half γ &&{↑NllftG}&&> @[α])%I
        as "#Gα1'".
      { iApply (big_sepL_impl with "Gα1"). iIntros "!>" (k α _) "#Gk".
        iApply (guards_transitive with "Gh Gk"). }
      iAssert ([∗ list] α ∈ lty_shr_lfts lt2, fractional.half γ &&{↑NllftG}&&> @[α])%I
        as "#Gα2'".
      { iApply (big_sepL_impl with "Gα2"). iIntros "!>" (k α _) "#Gk".
        iApply (guards_transitive with "Gh Gk"). }
      iDestruct ("Cont1" $! _ m d g tid with "[%] LFT PROPH Gty1 Gα1' H1 ηl1 Own1") as "T1";
        [apply _|].
      iDestruct ("Cont2" $! _ m d g tid with "[%] LFT PROPH Gty2 Gα2' H2 ηl2 Own2") as "T2";
        [apply _|].
      iModIntro. iDestruct (ctask_sep with "T1 T2") as "T".
      iApply (ctask_mono with "[] T").
      iIntros "[(#Obs1 & H1 & Own1) (#Obs2 & H2 & Own2)]".
      iMod (fupd_mask_mono with "(Back H1 H2)") as "$"; [solve_ndisj|].
      iModIntro. iFrame "Own1 Own2".
      iCombine "Obs1 Obs2" as "Obs". iApply (proph_obs_impl with "Obs")=> π /= [-> ->]. done.
    - (* A shared-blocked leaf: a fresh variable, resolved to the (unchanged) value of the
         leaf with the guards of its prophecy tokens given by the sharing predicate, while
         the shared lifetime is alive. *)
      iMod (proph_intro (uniq_cell_tyi x) ∅ with "PROPH") as (ηi) "[_ η]"; [solve_ndisj|].
      set η := uniq_prvar x ηi.
      iModIntro. iExists (inl (PlaceGhost x ηi)), [η].
      iSplit.
      { iPureIntro. intros ζl _. rewrite prfn_den_inl.
        eapply proph_dep_weaken; [|apply place_ghost_dep]. set_solver. }
      iSplitL "η"; [by iApply proph_tok_singleton|].
      iIntros (G m d g tid l ?) "#LFT _ #Gty #Gα G η Own".
      iDestruct (proph_tok_singleton with "η") as "η".
      rewrite /ltype_own /= /shr_blocked_owned.
      iDestruct "Gα" as "[Gα _]".
      iDestruct "Own" as (x' Hx) "(#GPt & #Shr & #Pers & Inh)". simpl in Hx. subst x'.
      iIntros "!> £".
      iDestruct (lc_weaken (d*(g+2) + (0 + (d+1)*(g+1))) with "£") as "[£k £k']";
        [rewrite /rslv_cost; nia|].
      set κs := α ⊓ ty_lft ty.
      iAssert (G &&{↑NllftG}&&> @[κs])%I as "#Gκs".
      { by iApply guards_llft_glb. }
      iAssert (κs ⊑ ty_lft ty)%I as "#Incl". { iApply llftl_intersect_incl_r. }
      iDestruct (ty_shr_lft_mono0 _ α κs with "[] Shr") as "#Shr'".
      { iApply llftl_intersect_incl_l. }
      iAssert (▷^(d*(g+2)) (∀ ζ, ⌜ζ ∈ ξl x⌝ -∗
        (G &&{↑NllftG; 0 + (d+1)*(g+1)}&&> 1:[ζ])))%I as "#Hallζlater".
      { iIntros (ζ) "%Hin".
        iDestruct (ty_shr_guard_proph ty κs x 0 d g tid ζ G Hin
          with "LFT Incl Pers Shr'") as "A".
        iNext. iApply "A". leaf_goal laters to 0; [lia|]. iFrame "Gκs". }
      iMod (lc_fupd_elim_laterN with "£k Hallζlater") as "#Hallζ".
      iDestruct (proph_eqz_token η
        (λ π, (vπ x π, (1%positive, (1%positive, 1%positive))))
        with "PROPH η") as "Eqz".
      iDestruct (proph_eqz_fst_const with "Eqz") as "Eqz".
      iMod (uniq_cmra.proph_eqz_to_obs_with_guard with "£k' Hallζ G Eqz")
        as "[#Obs $]"; [set_solver|apply syn_indep|].
      iModIntro. iSplitR.
      { iApply (proph_obs_impl with "Obs")=> π /= Heq. by rewrite prfn_den_inl prfn_den_in. }
      iExists x. iFrame "GPt Shr Pers Inh".
      iNext. by iApply proph_eqz_obs.
    - (* A sum. *)
      rewrite lty_rfn_sum. destruct (psum_proj i x.1) as [y|] eqn:Hy; last first.
      { iModIntro. iExists (prfn_dummy x), []. iSplit.
        { iPureIntro. intros ζl _. apply prfn_dummy_dep. }
        iSplit; [done|]. iIntros (G m d g tid l ?) "_ _ _ _ _ _ Own".
        by rewrite /ltype_own /= /prfn_dummy /sum_node /=. }
      iMod (IH y (false :: q) with "PROPH") as (r' ηl Hdep) "[ηl Cont]"; [done|].
      iModIntro. iExists (prfn_sum i r' x.2), ηl. iFrame "ηl". iSplit.
      { iPureIntro. intros ζl. rewrite prfn_rsv_sum prfn_den_sum. intros Hrsv.
        apply (proph_dep_constr (λ a, (pinj i a, x.2))). by apply Hdep. }
      iIntros (G m d g tid l ?) "#LFT _ #Gty #Gα G ηl Own".
      iEval (rewrite /ltype_own ltype_own_cp_sum_owned sum_node_sum) in "Own".
      iDestruct "Own" as "(Tag & Own & Pad)".
      iAssert (G &&{↑NllftG}&&> @[ty_lft (lty_fold lt)])%I as "#Gty'".
      { iApply (guards_transitive with "Gty"). iApply lty_lft_sum. }
      iDestruct ("Cont" $! G m d g tid with "[//] LFT PROPH Gty' Gα G ηl Own") as "T".
      iApply (ctask_mono with "[Tag Pad] T"). iIntros "(#Obs & $ & Own) !>".
      rewrite /ltype_own ltype_own_cp_sum_owned sum_node_sum. iFrame "Tag Own Pad".
      iApply (proph_obs_impl with "Obs")=> π Heq. by rewrite !prfn_den_sum /= Heq.
  Qed.
End rslv.

(** * Pre-resolving a reserved borrow while it is open *)

Section preresolve.
  Context `{!typeG Σ}.

  (** Open a reserved generalized prophetic borrow (with a lifetime guard); then
      pre-resolve its prophecy variable [ξ] to a prophecy [uπ] that depends on the
      reserved [ζl] and on [ηl] (whose tokens are needed and given back), and close the
      body at the controller [uπ]. The borrow is given up (the lender gets the body back
      when [κ] ends). As [proph_idx_bor_gen_preresolve_rsv], but the body is available
      before choosing [uπ], and it may be changed before closing. *)
  Lemma proph_idx_bor_gen_preresolve_rsv_acc E κ ξ x idx ζl
      (P: pv_val ξ → pv_proph ξ → iProp Σ) G :
    Timeless G → ↑Nllft ∪ ↑prophN ∪ ↑uniqN ⊆ E →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗ G -∗
    proph_bor_tok_rsv ξ x idx ζl -∗ proph_idx_bor_gen κ ξ idx P ={E}=∗ ∃ wπ,
      ▷ P x wπ ∗
      (∀ (uπ: pv_proph ξ) ηl q, ⌜uπ ./ ζl ++ ηl⌝ -∗ q:+[ηl] ={E}=∗
         ⟨π, π ξ = uπ π⟩ ∗ q:+[ηl] ∗ (▷ P x uπ ={E}=∗ G)).
  Proof.
    iIntros (??) "#LFT #PROPH #UNIQ #Gk G Tok #Bor".
    rewrite proph_bor_tok_rsv_unfold proph_idx_bor_gen_unfold.
    iDestruct "Tok" as "[Vo Tok]".
    iMod (llftl_bor_idx_acc_guarded with "LFT Bor Tok Gk G") as "[Body Back]"; [solve_ndisj|].
    iMod (bi.later_exist_except_0 with "Body") as (x') "Body".
    iMod (bi.later_exist_except_0 with "Body") as (wπ) "[Pc P]".
    iMod (uniq_rsv_strip_later with "Vo Pc") as "(<- & Vo & Pc)".
    iModIntro. iExists wπ. iFrame "P".
    iIntros (uπ ηl q Hdep) "ηl".
    iMod (uniq_preresolve_reserved ξ ζl ηl uπ q with "UNIQ PROPH Vo Pc ηl")
      as "(#Obs & $ & ToPc)"; [solve_ndisj|done|].
    iModIntro. iFrame "Obs". iIntros "P".
    iMod (fupd_mask_subseteq (↑Nllft)) as "Upd"; [solve_ndisj|].
    iMod ("Back" with "[ToPc P]") as "[_ G]". { iNext. iExists x, uπ. iFrame. iApply "ToPc". }
    iMod "Upd" as "_". by iFrame.
  Qed.

  (** The same for a compound place in [Uniq] mode: the contents are given at the
      current state; the prophecy variable is pre-resolved to the denotation of a new
      refinement [r'] (which may depend on the reservation and on [ηl]), and the body is
      closed at the state with [r'], with new contents. *)
  Lemma cpd_preresolve {𝔄} κ ξi (ty: type 𝔄) p
      (node: lpat → prfn 𝔄 → nat → nat → thread_id → cloc → iProp Σ)
      (r: prfn 𝔄) d g tid l E G :
    Timeless G → ↑Nllft ∪ ↑prophN ∪ ↑uniqN ⊆ E →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗ G -∗
    cpd_own κ ξi ty p node r d g tid l ={E}=∗ ∃ (x₀: ~~𝔄) ζl,
      ⌜prfn_rsv r ζl⌝ ∗
      ▷ guarded_upd lazyE @[ty_lft ty] (⧖(S d `max` g) ∗ node p r d g tid l) ∗
      (∀ (r': prfn 𝔄) ηl q, ⌜prfn_den r' ./ ζl ++ ηl⌝ -∗ q:+[ηl] ={E}=∗
         ⟨π, (π (uniq_prvar x₀ ξi)).1 = prfn_den r' π⟩ ∗ q:+[ηl] ∗
         (▷ guarded_upd lazyE @[ty_lft ty] (⧖(S d `max` g) ∗ node p r' d g tid l)
            ={E}=∗ G)).
  Proof.
    iIntros (??) "#LFT #PROPH #UNIQ #Gk G".
    iIntros "(%x₀ & %κp & %γ & %γf & %idx & %ζl & #Incl & %Hr & Tok & Gh & Tf & ⧗ & #Bor)".
    iMod (proph_idx_bor_gen_preresolve_rsv_acc with "LFT PROPH UNIQ Gk G Tok Bor")
      as (wπ) "[Body Close]"; [done..|].
    iDestruct (bi.later_or with "Body") as "[Body|[>Tf' _]]"; last first.
    { iDestruct (cpd_tok_excl with "Tf Tf'") as "[]". }
    rewrite cpd_body_cell.
    iMod (bi.later_exist_except_0 with "Body") as (p1) "Body".
    iMod (bi.later_exist_except_0 with "Body") as (r1) "(#Ok & _ & >Gh' & Upd)".
    iDestruct (ghost_var_agree with "Gh Gh'") as %[<- <-]%lstate_inj.
    iModIntro. iExists x₀, ζl. iFrame "Upd". iSplit; [done|].
    iIntros (r' ηl q Hdep) "ηl".
    iMod ("Close" $! (λ π, (prfn_den r' π, (uniq_cell x₀ d g γ).2)) ηl q with "[%] ηl")
      as "(#Obs & $ & Close)".
    { by apply (proph_dep_constr (λ a, (a, (uniq_cell x₀ d g γ).2))). }
    iMod (ghost_var_update_halves (lstate p r') with "Gh Gh'") as "[Gh Gh']".
    iModIntro. iSplitR. { iApply (proph_obs_impl with "Obs")=> π ->. done. }
    iIntros "Upd'". iApply "Close". iNext. iLeft. rewrite cpd_body_cell.
    iExists p, r'. iFrame "Ok Gh' Upd'". by iPureIntro.
  Qed.
End preresolve.

(** * Resolving a place rooted at a unique borrow *)

Section typing.
  Context `{!typeG Σ}.

  (** Give up the outer borrow of a place whose leaves are unblocked or blocked (also
      below owned pointers and sums; nested unique borrows with blocked leaves only):
      its prophecy variable is pre-resolved to the current value of the place, i.e. the
      final values of the reborrows at the blocked leaves and the current values at the
      unblocked ones. The lender gets the contents back when [κ] ends. One program step
      per unblocked leaf (and one to open the borrow). *)
  Lemma lctx_lft_alive_list E L (αl: list lft) :
    (∀ α, α ∈ αl → lctx_lft_alive E L α) →
    llctx_interp L ⊢ elctx_interp E -∗ [∗ list] α ∈ αl, llctx_interp L &&{↑NllftG}&&> @[α].
  Proof.
    induction αl as [|α αl IH]; intros Hl; [by iIntros "_ _"|]. iIntros "L #E".
    iDestruct (Hl α with "L E") as "#Gα"; [set_solver|].
    iDestruct (IH with "L E") as "#Gαl"; [set_solver|]. by iFrame "Gα Gαl".
  Qed.

End typing.

(** * Resolving a place rooted at a unique borrow value

  A place [p ◁ₗ{κ} lt], i.e. [p ◁ₗ UniqLty lt κ] ([vplace.v]): the root is the node value
  of the borrow ([uniq_nval]), whose referent is in [Uniq κ] mode. *)

Section vplace_uniq.
  Context `{!typeG Σ}.

  (** Give up the root borrow while all leaves of the (compound) referent are blocked: its
      prophecy variable is pre-resolved, through its reservation, to the current value of
      the place. *)
  Lemma tctx_drop_vplace_uniq {𝔄} E L p κ (lt: lty 𝔄) :
    lctx_lft_alive E L κ → lty_is_cpd lt → lty_blk_all lt →
    tctx_incl E L +[p ◁ₗ UniqLty lt κ] +[]
      (λ post '-[x], λ mask π,
        uniq_bor_future x.1 π = prfn_den (lty_rfn lt (uniq_bor_current x.1) x.2 []) π →
        post -[] mask π).
  Proof.
    intros Alv Hc Hb. split.
    { intros ?? Eq [? []] ??. split=> H ?; apply Eq, H; done. }
    iIntros (G tid [x []] mask post ?) "#LFT #PROPH #UNIQ #E #GL G [T _] Obs".
    destruct x as [[[[[[l x₀] ξi] d'] g'] idx] ζm].
    iDestruct "T" as (v ? D) "(_ & _ & %d & %g & %Hle & -> & _ & _ & #Incl & #Pt & %d1 & %g1 & %Hle1 & Own)".
    leaf_open "GL" with "G" as "[L back]"; [set_solver|].
    iDestruct (Alv with "L E") as "#Lκ". iMod ("back" with "L") as "G".
    iDestruct (guards_transitive with "GL Lκ") as "#Gκ".
    rewrite /ltype_own ltype_own_cp_uniq_cpd //.
    iDestruct "Own" as (x₀' κp γ γf idx' ζl) "(#Inclp & %Hr & Tok & Gh & Tf & ⧗o & #Bor)".
    set r : prfn 𝔄 := lty_rfn lt x₀ ζm [].
    set uπ : proph (uniq_cellₛ 𝔄) :=
      λ π, (prfn_den r π, (1%positive, (1%positive, 1%positive))).
    have Hdep: uπ ./ ζl.
    { apply (proph_dep_constr (λ a, (a, (1%positive, (1%positive, 1%positive))))).
      by apply lty_blk_all_dep. }
    iMod (proph_idx_bor_gen_preresolve_rsv ⊤ κ (uniq_prvar x₀' ξi) (uniq_cell x₀' d1 g1 γ) idx'
      ζl _ uπ G with "LFT PROPH UNIQ Gκ [Gh Tf] G Tok Bor") as "[#Obs' $]";
      [solve_ndisj|done| |].
    { iIntros (wπ) "Body". iNext.
      iDestruct "Body" as "[Body|[Tf' _]]"; [|iDestruct (cpd_tok_excl with "Tf Tf'") as "[]"].
      iLeft. rewrite !cpd_body_cell. iDestruct "Body" as (p1 r1) "(Ok & % & Gh' & Upd)".
      iDestruct (ghost_var_agree with "Gh Gh'") as %[<- <-]%lstate_inj.
      iExists _, _. by iFrame. }
    iModIntro. iExists -[]. iSplit; [done|].
    iCombine "Obs Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=> π [Hπ Heq].
    apply Hπ. rewrite uniq_bor_future_eq (uniq_prvar_app_irrel x₀ x₀') Heq. done.
  Qed.

  (** Give up the root borrow of a place whose leaves are unblocked or blocked: its prophecy variable is pre-resolved to the current
      value of the place. One program step per unblocked leaf (and one to open the
      borrow). *)
  Lemma type_resolve_vplace_uniq_instr {𝔄} E L I p κ (lt: lty 𝔄) :
    lctx_lft_alive E L κ → lty_is_cpd lt → lty_uniq_rslv lt →
    (∀ α, α ∈ lty_shr_lfts lt → lctx_lft_alive E L α) →
    typed_instr E L I +[p ◁ₗ UniqLty lt κ] (skipn (S (lty_nunblk lt))) (const +[])
      (λ post '-[x], λ mask π,
        uniq_bor_future x.1 π = prfn_den (lty_rfn lt (uniq_bor_current x.1) x.2 []) π →
        post -[] mask π).
  Proof.
    iIntros (Alv Hc Hrs Halv tid post mask iκs [x []])
      "#LFT #TIME #PROPH #UNIQ #E L I [T _] Obs".
    destruct x as [[[[[[l x₀] ξi] d'] g'] idx] ζm].
    iDestruct "T" as (v ? D) "(#⧖0 & _ & %d & %g & %Hle & -> & _ & _ & #Incl & #PtBase & %d1 & %g1 & %Hle1 & Own)".
    iDestruct (Alv with "L E") as "#Alv".
    iDestruct (lctx_lft_alive_list _ _ _ Halv with "L E") as "#Alvl".
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iDestruct (guards_transitive with "Ghalf Alv") as "#Hκ".
    iAssert ([∗ list] α ∈ lty_shr_lfts lt, fractional.half γh &&{↑NllftG}&&> @[α])%I
      as "#Hαl".
    { iApply (big_sepL_impl with "Alvl"). iIntros "!>" (k α _) "#Gk".
      iApply (guards_transitive with "Ghalf Gk"). }
    iAssert (fractional.half γh &&{↑NllftG}&&> @[ty_lft (lty_fold lt)])%I as "#Hty".
    { iApply (guards_transitive with "Hκ Incl"). }
    rewrite /ltype_own ltype_own_cp_uniq_cpd //.
    iMod (ltype_owned_rslv lt x₀ ζm [] with "PROPH") as (r' ηl Hdep) "[ηl Cont]"; [done|].
    iMod (cpd_preresolve with "LFT PROPH UNIQ Hκ H1 Own") as (x₀' ζl Hr) "[Upd Pre]";
      [solve_ndisj|].
    iMod ("Pre" $! r' ηl with "[%] ηl") as "(#Obs' & ηl & Close)"; [by apply Hdep|].
    set c := 1 + rslv_cost D D.
    iApply (wp_skipn_ctask _ c D
      (llctx_interp L ∗ ⟨π, prfn_den r' π = prfn_den (lty_rfn lt x₀ ζm []) π⟩)
      with "TIME ⧖0 [-Obs I]").
    { rewrite /c /rslv_cost /advance_credits. nia. }
    { iModIntro. iIntros "[£1 _]". iApply ctask_fupd.
      iMod (lc_fupd_elim_later with "£1 Upd") as "Upd".
      iMod (guarded_upd_run with "Hty H2 Upd") as "(H2 & #⧖' & N)";
        [rewrite /lazyE; solve_ndisj|].
      iDestruct ("Cont" $! _ 0 d1 g1 tid l with "[%] LFT PROPH Hty Hαl H2 ηl N") as "T";
        [apply _|].
      iDestruct (ctask_weaken _ c with "T") as "T".
      { rewrite /c. have := rslv_cost_mono (0 + d1) g1 D D. lia. }
      iApply (ctask_mono with "[Close] T").
      iIntros "(#Obs & H2 & N)".
      iMod ("Close" with "[N]") as "H1".
      { iNext. iApply guarded_upd_intro. iModIntro. iFrame "⧖' N". }
      iMod (fupd_mask_mono with "(Halfback H1 H2)") as "$"; [solve_ndisj|].
      by iModIntro. }
    iIntros "[$ #Obs2]". iExists -[]. iFrame "I". iSplit; [done|].
    iCombine "Obs Obs' Obs2" as "Obs3". iApply (proph_obs_impl with "Obs3")=> π [Hπ [H1 H2]].
    apply Hπ. rewrite uniq_bor_future_eq (uniq_prvar_app_irrel x₀ x₀') H1 H2. done.
  Qed.
End vplace_uniq.

(** * Resolving places in [Owned] mode

  [lty_resolve E L lt Φ]: the [Owned m] interpretation of [lt] at the refinement of a
  value [x] can be resolved (consumed) to the condition [Φ x] on the current value, in
  [m + d*(g+1)] steps (as [resolve] for types, plus one step per owned pointer above,
  for the laters of the ghost ownership). Only unblocked leaves contribute; the other
  leaves are forgotten ([lty_resolve_just]): a blocked leaf's lender keeps its borrow,
  and a shared-blocked leaf's value is persistent. The memory owned by the place is
  given back ([lty_omem]: the memory of the place itself if no leaf is blocked, and the
  pointees of its owned pointers), so that it can be freed ([type_drop_oplace_instr]). *)

Section lty_mem.
  Context `{!typeG Σ}.

  (** The memory of a place (outside the pointees of its owned pointers) is owned: no
      leaf is blocked or shared. *)
  Fixpoint lty_freeb {𝔄} (lt: lty 𝔄) : bool :=
    match lt with
    | OfTy _ | OwnPtrLty _ _ | UniqLty _ _ | ShrLty _ _ | OfRes _ | ResUniqLty _ _ => true
    | ProdLty lt1 lt2 => lty_freeb lt1 && lty_freeb lt2
    | SumLty _ _ lt => lty_freeb lt
    | Blocked _ _ | ShrBlocked _ _ => false
    end.

  (** The pointee of an owned pointer [OwnPtrLty n lt] is freed when the place is
      dropped if its memory is owned and its size is [n]. *)
  Definition own_freeb {𝔄} (n: nat) (lt: lty 𝔄) : bool :=
    lty_freeb lt && bool_decide (n = lty_size lt).

  (** The memory owned by a place in [Owned m] mode: the memory of the place itself
      (unless a leaf is blocked or shared) and the memory of the pointees of its owned
      pointers that are freed by [drop_boxes]; the right to free a pointee is under [m]
      laters, as in [own_node]. *)
  Fixpoint lty_omem {𝔄} (m: nat) (lt: lty 𝔄) : cloc → iProp Σ :=
    match lt in lty 𝔄 return cloc → iProp Σ with
    | OfTy ty | OfRes ty => λ l, ∃ vl, l #↦!∗ vl ∗ ⌜length vl = ty_size ty⌝
    | UniqLty _ _ | ShrLty _ _ | ResUniqLty _ _ => λ l, ∃ v, l #↦!∗ [v]
    | OwnPtrLty n lt' => λ l, ∃ l': loc, l #↦!∗ [FVal #l'] ∗
        if own_freeb n lt' then
          ▷^m freeable_sz n (lty_size lt') l' ∗
          lty_omem (m + 1) lt' (l', repeat [] (lty_size lt'))
        else True
    | ProdLty lt1 lt2 => λ l,
        lty_omem m lt1 (cloc_take l (lty_size lt1)) ∗
        lty_omem m lt2 (cloc_skip l (lty_size lt1))
    | SumLty tyl i lt' => λ l, ∃ vp: list val,
        cloc_take l 1 #↦∗ [ #i ] ∗ lty_omem m lt' (cloc_take (cloc_skip l 1) (lty_size lt')) ∗
        cloc_skip (cloc_skip l 1) (lty_size lt') #↦∗ vp ∗
        ⌜length vp = max_hlist_set (λ _, ty_size) tyl i (lty_size lt') - lty_size lt'⌝
    | Blocked _ _ | ShrBlocked _ _ => λ _, True
    end%I.

  (** The memory of any place. *)
  Lemma ltype_owned_omem {𝔄} (lt: lty 𝔄) m r d g tid l :
    ltype_own (Owned m) lt r d g tid l ⊢ lty_omem m lt l.
  Proof.
    induction lt as [𝔄 ty|𝔄 ty α|𝔄 lt IH κ'|𝔄 n lt IH|𝔄 𝔅 lt1 IH1 lt2 IH2|𝔄 ty α|
      𝔄l tyl i lt IH|𝔄 lt IH κ'|𝔄 ty|𝔄 lt IH κ'] in m, r, d, g, l |- *; rewrite /ltype_own /=;
      [..|rewrite /leaf_owned_s /leaf_owned;
        destruct r as [lr|]; [|by iIntros "[[] _]"]; iIntros "[(%x & _ & Pt & _) _]";
        iExists _; by iFrame "Pt"
       |rewrite /res_leaf; destruct r as [lr|]; [|by iIntros "[]"];
        iIntros "(%x & _ & Pt & _)"; iExists _; iFrame "Pt"; by rewrite ty_size_eq
       |rewrite /res_node; destruct r as [|[[l' r'] ξi]]; [by iIntros "[]"|];
        iIntros "[Pt _]"; iExists _; by iFrame]; try by iIntros.
    - rewrite /leaf_owned_s /leaf_owned.
      destruct r as [lr|]; [|by iIntros "[]"]. iIntros "(%x & _ & Pt & _)".
      iExists _. iFrame "Pt". by rewrite ty_size_eq.
    - rewrite /uniq_node. destruct r as [|[[l' r'] ξi]]; [by iIntros "[]"|].
      iIntros "[Pt _]". iExists _. iFrame.
    - rewrite /own_node. destruct r as [|[l' r']]; [by iIntros "[]"|].
      iIntros "(Pt & _ & Fr & O)". iExists l'. iFrame "Pt".
      destruct (own_freeb n lt); [|done]. iFrame "Fr". by iApply IH.
    - rewrite /prod_node. destruct r as [|[r1 r2]]; [by iIntros "[]"|]. iIntros "[O1 O2]".
      iSplitL "O1"; [by iApply IH1|by iApply IH2].
    - destruct r as [|[s pad]]; [by iIntros "[]"|]. rewrite /sum_node.
      case_match; [|by iIntros "[]"]. iIntros "(Tag & O & Pad)".
      iExists _. iFrame "Tag Pad". iSplitL; [by iApply IH|]. by rewrite length_vec_to_list.
  Qed.
End lty_mem.

Definition lty_resolve `{!typeG Σ} {𝔄} (E: elctx) (L: llctx) (lt: lty 𝔄)
    (Φ: ~~𝔄 → proph_asn → Prop) : Prop :=
  ∀ G F m x ζm q d g tid l, Timeless G → ↑Nllft ∪ ↑prophN ∪ ↑timeN ∪ ↑uniqN ⊆ F →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ time_ctx -∗ elctx_interp E -∗
    (G &&{↑NllftG}&&> llctx_interp L) -∗ G -∗
    ltype_own (Owned m) lt (lty_rfn lt x ζm q) d g tid l ={F}=∗
      lty_omem m lt l ∗ |={F}▷=>^(m + d*(g+1)) |={F}=> ⟨π, Φ x π⟩ ∗ G.

Section lty_resolve.
  Context `{!typeG Σ}.

  Lemma lty_resolve_impl {𝔄} E L (lt: lty 𝔄) (Φ Φ': ~~𝔄 → proph_asn → Prop) :
    lty_resolve E L lt Φ → (∀ x π, Φ x π → Φ' x π) → lty_resolve E L lt Φ'.
  Proof.
    iIntros (Rslv Imp G F m x ζm q d g tid l ??) "LFT PROPH UNIQ TIME E L G Own".
    iMod (Rslv with "LFT PROPH UNIQ TIME E L G Own") as "[$ Upd]"; [done..|].
    iModIntro. iApply (step_fupdN_wand with "Upd"). iIntros ">[Obs $] !>".
    iApply (proph_obs_impl with "Obs")=> ?. apply Imp.
  Qed.

  (** Any place can be forgotten. *)
  Lemma lty_resolve_just {𝔄} E L (lt: lty 𝔄) : lty_resolve E L lt (λ _ _, True).
  Proof.
    iIntros (G F m x ζm q d g tid l ??) "_ _ _ _ _ _ G Own".
    iDestruct (ltype_owned_omem with "Own") as "$". iModIntro.
    iApply step_fupdN_full_intro. iFrame "G". by iApply proph_obs_true.
  Qed.

  Lemma lty_resolve_ofty {𝔄} E L (ty: type 𝔄) Φ :
    resolve E L ty Φ → lty_resolve E L (OfTy ty) Φ.
  Proof.
    iIntros (Rslv G F m x ζm q d g tid l ??) "LFT PROPH UNIQ TIME E L G Own".
    rewrite /ltype_own /= /leaf_owned_s /leaf_owned /=.
    iDestruct "Own" as (x' Hx) "[Pt Gho]". simpl in Hx. subst x'.
    iSplitL "Pt". { iModIntro. iExists _. iFrame "Pt". by rewrite ty_size_eq. }
    iModIntro. iApply step_fupdN_add.
    iApply (step_fupdN_wand with "[Gho]"); [by iApply step_fupdN_intro|].
    iIntros "Gho". iApply fupd_step_fupdN_front.
    iApply (Rslv with "LFT PROPH UNIQ TIME E L G Gho"); done.
  Qed.

  Lemma lty_resolve_prod {𝔄1 𝔄2} E L (lt1: lty 𝔄1) (lt2: lty 𝔄2) Φ1 Φ2 :
    lty_resolve E L lt1 Φ1 → lty_resolve E L lt2 Φ2 →
    lty_resolve E L (ProdLty lt1 lt2) (λ x π, Φ1 x.1 π ∧ Φ2 x.2 π).
  Proof.
    iIntros (Rslv1 Rslv2 G F m x ζm q d g tid l ??) "#LFT #PROPH #UNIQ #TIME #E #L G Own".
    rewrite /ltype_own /=. iDestruct "Own" as "[Own1 Own2]".
    iMod (fractional.frac_split_guard_in_half with "G L") as (γ) "[H1 [H2 [#Gh #Back]]]";
      [solve_ndisj|].
    iMod (Rslv1 with "LFT PROPH UNIQ TIME E Gh H1 Own1") as "[M1 Upd1]"; [done..|].
    iMod (Rslv2 with "LFT PROPH UNIQ TIME E Gh H2 Own2") as "[M2 Upd2]"; [done..|].
    iSplitL "M1 M2". { iModIntro. iFrame. }
    iCombine "Upd1 Upd2" as "Upd". iModIntro.
    iApply (step_fupdN_wand with "Upd"). iIntros "[>[Obs1 H1] >[Obs2 H2]]".
    iMod (fupd_mask_mono with "(Back H1 H2)") as "$"; [solve_ndisj|].
    iModIntro. by iCombine "Obs1 Obs2" as "?".
  Qed.

  Lemma lty_resolve_own {𝔄} E L n (lt: lty 𝔄) Φ :
    lty_resolve E L lt Φ → lty_resolve E L (OwnPtrLty n lt) (λ x π, Φ x.2 π).
  Proof.
    iIntros (Rslv G F m x ζm q d g tid l ??) "LFT PROPH UNIQ TIME E L G Own".
    rewrite /ltype_own /=. destruct x as [l' x]. iDestruct "Own" as "(Pt & %Hd & Fr & Own)".
    iMod (Rslv with "LFT PROPH UNIQ TIME E L G Own") as "[M Upd]"; [done..|].
    iSplitL "Pt Fr M".
    { iModIntro. iExists l'. iFrame "Pt". destruct (own_freeb n lt); [|done]. iFrame. }
    iModIntro. iApply (step_fupdN_nmono with "Upd"). destruct d; [done|]. simpl. nia.
  Qed.

  Lemma lty_resolve_sum {𝔄l} E L (tyl: typel 𝔄l) i (lt: lty (𝔄l !!ₗ i)) Φ :
    lty_resolve E L lt Φ →
    lty_resolve E L (SumLty tyl i lt) (λ x π, ∀ y, psum_proj i x.1 = Some y → Φ y π).
  Proof.
    iIntros (Rslv G F m x ζm q d g tid l ??) "LFT PROPH UNIQ TIME E L G Own".
    rewrite lty_rfn_sum. destruct (psum_proj i x.1) as [y|] eqn:Hy; last first.
    { by rewrite /ltype_own /= /prfn_dummy /sum_node /=. }
    rewrite /ltype_own ltype_own_cp_sum_owned sum_node_sum.
    iDestruct "Own" as "(Tag & Own & Pad)".
    iMod (Rslv with "LFT PROPH UNIQ TIME E L G Own") as "[M Upd]"; [done..|].
    iSplitL "Tag M Pad".
    { iModIntro. iExists _. iFrame. by rewrite length_vec_to_list. }
    iModIntro. iApply (step_fupdN_wand with "Upd"). iIntros ">[Obs $] !>".
    iApply (proph_obs_impl with "Obs")=> π ? y' [= <-]. done.
  Qed.
End lty_resolve.

(** * Freeing the pointees of the owned pointers of a place *)

Section drop_boxes.
  Context `{!typeG Σ}.

  (** The program that frees the pointees of the owned pointers of a place (whose
      memory starts at the location computed by [e]), innermost first. The location of
      a pointee is computed again from [e] for each access (as [pctx_expr]): the memory
      of the place is only freed afterwards. *)
  Fixpoint drop_boxes {𝔄} (lt: lty 𝔄) (e: expr) : expr :=
    match lt with
    | OwnPtrLty n lt' =>
        if own_freeb n lt' then
          (drop_boxes lt' (!e);; new_delete.delete [ #(lty_size lt'); !e])%E
        else #☠%E
    | ProdLty lt1 lt2 => (drop_boxes lt1 e;; drop_boxes lt2 (e +ₗ #(lty_size lt1)))%E
    | SumLty _ _ lt' => drop_boxes lt' (e +ₗ #1)%E
    | _ => #☠%E
    end.

  Global Instance drop_boxes_closed {𝔄} (lt: lty 𝔄) e :
    Closed [] e → Closed [] (drop_boxes lt e).
  Proof.
    induction lt as [| | | 𝔄 n lt IH|𝔄 𝔅 lt1 IH1 lt2 IH2| |𝔄l tyl i lt IH| | |] in e |- *;
      intros ?; simpl; try done.
    - destruct (own_freeb n lt); [|done]. have ?: Closed [] (drop_boxes lt (!e)%E).
      { apply IH. apply _. }
      apply _.
    - have ?: Closed [] (drop_boxes lt1 e) by apply IH1.
      have ?: Closed [] (drop_boxes lt2 (e +ₗ #(lty_size lt1))%E) by apply IH2; apply _.
      apply _.
    - apply IH. apply _.
  Qed.

  Lemma cloc_take_repeat (l: loc) a b : cloc_take (l, repeat [] (a + b)) a = (l, repeat [] a).
  Proof. by rewrite /cloc_take /= take_repeat_add. Qed.

  Lemma cloc_skip_repeat (l: loc) a b :
    cloc_skip (l, repeat [] (a + b)) a = (l +ₗ a, repeat [] b).
  Proof. by rewrite /cloc_skip /= drop_repeat_add. Qed.

  Lemma lty_omem_sum_repeat {𝔄l} m (tyl: typel 𝔄l) i (lt: lty (𝔄l !!ₗ i)) (l: loc) :
    lty_omem m (SumLty tyl i lt) (l, repeat [] (lty_size (SumLty tyl i lt))) ⊣⊢
      ∃ vp: list val, (l, repeat [] 1) #↦∗ [ #i ] ∗
        lty_omem m lt (l +ₗ 1, repeat [] (lty_size lt)) ∗
        (l +ₗ 1 +ₗ lty_size lt,
          repeat [] (max_hlist_set (λ _, ty_size) tyl i (lty_size lt) - lty_size lt)) #↦∗ vp ∗
        ⌜length vp = max_hlist_set (λ _, ty_size) tyl i (lty_size lt) - lty_size lt⌝.
  Proof.
    have Hle := max_hlist_set_ge (λ _, ty_size) tyl i (lty_size lt).
    have Hsz: lty_size (SumLty tyl i lt) =
      1 + (lty_size lt + (max_hlist_set (λ _, ty_size) tyl i (lty_size lt) - lty_size lt)).
    { cbn [lty_size]. lia. }
    rewrite Hsz. cbn [lty_omem].
    by rewrite !cloc_take_repeat !cloc_skip_repeat.
  Qed.

  Lemma cell_mapsto_val (l: loc) v : (l, repeat [] 1) #↦!∗ [FVal v] ⊣⊢ l ↦ v.
  Proof.
    rewrite -heap_mapsto_vec_singleton -(heap_mapsto_fancy_fmap_eq l [v]).
    symmetry. apply (heap_cloc_mapsto_fancy_empty l [FVal v]).
  Qed.

  (** [drop_boxes lt e] frees the pointees of the owned pointers of the place (those in
      [lty_omem]) and gives back the memory of the place itself. [e] computes the
      location of the place, using some resource [R], in at least [k] steps; the rights
      to free the pointees are under [m] laters, with [m ≤ k + 1]: the pointee of an
      owned pointer is freed after its location has been computed again, i.e. after
      [k + 1] steps. *)
  Lemma wp_drop_boxes {𝔄} (lt: lty 𝔄) m k (l: loc) (e: expr) (R: iProp Σ) E Φ :
    ↑non_atomic_cell_map.naN ⊆ E → lty_freeb lt = true → Closed [] e → m ≤ k + 1 →
    (⊢ ∀ Ψ (P: iProp Σ), R -∗ ▷^k P -∗ (R -∗ P -∗ Ψ #l) -∗ WP e @ E {{ Ψ }}) →
    R -∗ lty_omem m lt (l, repeat [] (lty_size lt)) -∗
    (∀ vl, R -∗ (l, repeat [] (lty_size lt)) #↦!∗ vl -∗ ⌜length vl = lty_size lt⌝ -∗
      Φ #☠) -∗
    WP drop_boxes lt e @ E {{ Φ }}.
  Proof.
    intros ?. induction lt as [𝔄 ty| |𝔄 lt IH κ'|𝔄 n lt IH|𝔄 𝔅 lt1 IH1 lt2 IH2| |𝔄l tyl i lt IH|𝔄 lt IH κ'|𝔄 ty|𝔄 lt IH κ']
      in m, k, l, e, R, Φ |- *; intros Hf ? Hm Hev; simpl in Hf; try done; cbn [drop_boxes];
      iIntros "R M HΦ".
    6: { iDestruct "M" as (v) "Pt". iApply wp_value. by iApply ("HΦ" with "R Pt"). }
    6: { iDestruct "M" as (vl) "[Pt %Hl]". iApply wp_value. by iApply ("HΦ" with "R Pt"). }
    6: { iDestruct "M" as (v) "Pt". iApply wp_value. by iApply ("HΦ" with "R Pt"). }
    - iDestruct "M" as (vl) "[Pt %Hl]". iApply wp_value. by iApply ("HΦ" with "R Pt").
    - iDestruct "M" as (v) "Pt". iApply wp_value. by iApply ("HΦ" with "R Pt").
    - simpl. iDestruct "M" as (l') "[Pt M]". destruct (own_freeb n lt) eqn:Hfb; last first.
      { iApply wp_value. by iApply ("HΦ" with "R Pt"). }
      apply andb_true_iff in Hfb as [Hf' Hn%bool_decide_eq_true].
      iEval (rewrite cell_mapsto_val) in "Pt".
      have Hev': ⊢ ∀ Ψ (P: iProp Σ), (R ∗ l ↦ #l') -∗ ▷^(k + 1) P -∗
        ((R ∗ l ↦ #l') -∗ P -∗ Ψ #l') -∗ WP (!e)%E @ E {{ Ψ }}.
      { iIntros (Ψ P) "[R Pt] P HΨ". wp_bind e.
        iApply (Hev $! _ (▷ P)%I with "R [P]"); [by rewrite bi.laterN_add|]. iIntros "R P".
        wp_read. iApply ("HΨ" with "[$R $Pt] P"). }
      iDestruct "M" as "[Fr M]".
      wp_bind (drop_boxes lt (!e)%E).
      iApply (IH (m + 1) (k + 1) l' (!e)%E (R ∗ l ↦ #l')%I _ Hf' _ ltac:(lia) Hev'
        with "[$R $Pt] M").
      iIntros (vl) "[R Pt] Pt' %Hl". wp_seq.
      iMod (mapsto_vec_untether_emp _ _ _ ∅ with "[Pt']") as (vl') "[Pt' [%Hl' _]]".
      { by rewrite -Hl -heap_cloc_mapsto_fancy_empty. }
      wp_bind (!e)%E. iApply (Hev' with "[$R $Pt] [Fr]").
      { iApply (bi.laterN_le with "Fr"). lia. }
      iIntros "[R Pt] Fr".
      iApply (wp_delete vl' with "[Pt' Fr]"); [done|by rewrite Hl' Hl| |].
      { iFrame "Pt'". rewrite Hl' Hl -Hn. by iApply freeable_sz_full. }
      iIntros "!> _". iApply ("HΦ" $! [FVal #l'] with "R [Pt]"); [by rewrite /= cell_mapsto_val|done].
    - apply andb_true_iff in Hf as [Hf1 Hf2]. iDestruct "M" as "[M1 M2]".
      rewrite /cloc_take /cloc_skip /= take_repeat_add drop_repeat_add.
      have Hev2: ⊢ ∀ Ψ (P: iProp Σ), R -∗ ▷^(k + 1) P -∗ (R -∗ P -∗ Ψ #(l +ₗ lty_size lt1)) -∗
        WP (e +ₗ #(lty_size lt1))%E @ E {{ Ψ }}.
      { iIntros (Ψ P) "R P HΨ". wp_bind e.
        iApply (Hev $! _ (▷ P)%I with "R [P]"); [by rewrite bi.laterN_add|]. iIntros "R P".
        wp_op. by iApply ("HΨ" with "R P"). }
      wp_bind (drop_boxes lt1 e).
      iApply (IH1 m k l e R _ Hf1 _ Hm Hev with "R M1 [M2 HΦ]").
      iIntros (vl1) "R Pt1 %Hl1". wp_seq.
      iApply (IH2 m (k + 1) (l +ₗ lty_size lt1) (e +ₗ #(lty_size lt1))%E R _ Hf2 _ ltac:(lia)
        Hev2 with "R M2 [Pt1 HΦ]").
      iIntros (vl2) "R Pt2 %Hl2". iApply ("HΦ" $! (vl1 ++ vl2) with "R [Pt1 Pt2]").
      + rewrite heap_cloc_mapsto_fancy_vec_app Hl1 cloc_take_repeat cloc_skip_repeat.
        iFrame.
      + by rewrite length_app Hl1 Hl2.
    - iEval (rewrite lty_omem_sum_repeat) in "M".
      iDestruct "M" as (vp) "(Tag & M & Pad & %Hp)".
      have Hle := max_hlist_set_ge (λ _, ty_size) tyl i (lty_size lt).
      have Hsz: lty_size (SumLty tyl i lt) =
        1 + (lty_size lt + (max_hlist_set (λ _, ty_size) tyl i (lty_size lt) - lty_size lt)).
      { cbn [lty_size]. lia. }
      set sz := lty_size lt. set mx := max_hlist_set (λ _, ty_size) tyl i sz.
      rewrite Hsz.
      have Hev2: ⊢ ∀ Ψ (P: iProp Σ), R -∗ ▷^(k + 1) P -∗ (R -∗ P -∗ Ψ #(l +ₗ 1)) -∗
        WP (e +ₗ #1)%E @ E {{ Ψ }}.
      { iIntros (Ψ P) "R P HΨ". wp_bind e.
        iApply (Hev $! _ (▷ P)%I with "R [P]"); [by rewrite bi.laterN_add|]. iIntros "R P".
        wp_op. by iApply ("HΨ" with "R P"). }
      iApply (IH m (k + 1) (l +ₗ 1) (e +ₗ #1)%E R _ Hf _ ltac:(lia) Hev2 with "R M [-]").
      iIntros (vl) "R Pt %Hl".
      iApply ("HΦ" $! ([FVal #i] ++ (vl ++ fmap FVal vp)) with "R [-]").
      + rewrite heap_cloc_mapsto_fancy_vec_app. cbn [length].
        rewrite cloc_take_repeat cloc_skip_repeat.
        rewrite heap_cloc_mapsto_fancy_vec_app Hl cloc_take_repeat cloc_skip_repeat.
        by iFrame.
      + iPureIntro. rewrite /= length_app length_fmap Hl Hp. lia.
  Qed.
End drop_boxes.

(** * Resolving and dropping places rooted at an owned location *)

Section oplace.
  Context `{!typeG Σ}.

  Lemma oplace_resolve_steps {𝔄} E L n (lt: lty 𝔄) Φ x tid v :
    lty_resolve E L lt Φ →
    oplace_own n lt x tid v -∗ ∃ D, ⧖D ∗ ∀ G F, ⌜Timeless G⌝ -∗
      ⌜↑Nllft ∪ ↑prophN ∪ ↑timeN ∪ ↑uniqN ⊆ F⌝ -∗
      llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ time_ctx -∗ elctx_interp E -∗
      (G &&{↑NllftG}&&> llctx_interp L) -∗ G ={F}=∗
        |={F}▷=>^(D*(D+1)) |={F}=> ⟨π, Φ x.1.2 π⟩ ∗ G.
  Proof.
    iIntros (Rslv) "Own". destruct x as [[l x₀] ζm].
    iDestruct "Own" as (D d g) "(⧖ & _ & _ & %Hle & _ & Own)".
    iExists D. iFrame "⧖". iIntros (G F ??) "LFT PROPH UNIQ TIME E L G".
    iMod (Rslv with "LFT PROPH UNIQ TIME E L G Own") as "[_ Upd]"; [done..|].
    iModIntro. iApply (step_fupdN_nmono with "Upd"). nia.
  Qed.

  (** Resolving (and forgetting) an owned place, e.g. at the end of a function: the
      unblocked leaves are resolved, the memory is leaked. *)
  Lemma resolve_tctx_cons_oplace {𝔄 𝔅l} E L p n (lt: lty 𝔄) Φ (T: tctx 𝔅l) Ψ :
    lty_resolve E L lt Φ → resolve_tctx E L T Ψ →
    resolve_tctx E L (p ◁ₗown{n} lt +:: T) (λ '(x -:: bl) π φ, Φ x.1.2 π → Ψ bl π φ).
  Proof.
    iIntros (Rslv Rslv' G F tid [x xl] ? HF).
    iIntros "#LFT #PROPH #UNIQ #TIME #E #L G /=[(%v & _ & Own) T]".
    iMod (fractional.frac_split_guard_in_half NllftG with "G L")
      as (γ) "[F1 [F2 [#guards #back]]]"; [solve_ndisj|].
    iDestruct (oplace_resolve_steps with "Own") as (D) "[⧖ ToObs]"; [done|].
    iMod ("ToObs" $! _ F with "[%] [//] LFT PROPH UNIQ TIME E guards F1") as "ToObs";
      [apply _|].
    iMod (Rslv' with "LFT PROPH UNIQ TIME E guards F2 T") as (?) "[⧖' ToObs']"; [done|].
    iCombine "⧖ ⧖'" as "⧖". iCombine "ToObs ToObs'" as "ToObs".
    iModIntro. iExists _. iFrame "⧖". rewrite lemma_max_mul.
    iApply (step_fupdN_wand with "ToObs"). iIntros "[>[Obs F1] >[Obs' F2]]".
    iMod (fupd_mask_mono with "(back F1 F2)") as "$"; [solve_ndisj|].
    iCombine "Obs Obs'" as "Obs". iModIntro.
    iApply (proph_obs_impl with "Obs")=>/= ?[? Imp]? Imp'. by apply Imp, Imp'.
  Qed.

  (** Resolving (and forgetting) an owned place in the middle of a function. *)
  Lemma type_resolve_oplace_instr {𝔄} E L I p n (lt: lty 𝔄) Φ :
    lty_resolve E L lt Φ →
    typed_instr E L I +[p ◁ₗown{n} lt] Skip (λ _, +[])
      (λ post '-[x], λ mask π, Φ x.1.2 π → post -[] mask π).
  Proof.
    iIntros (Rslv tid post mask iκs [x []]) "#LFT #TIME #PROPH #UNIQ #E L I [(%v & _ & Own) _] Obs".
    iMod (llctx_interp_make_guarded with "L") as (γ) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iDestruct (oplace_resolve_steps with "Own") as (D) "[#⧖ Upd]"; [done|].
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj|]. iIntros "£ _".
    iMod ("Upd" $! _ (⊤∖↑advN) with "[%] [%] LFT PROPH UNIQ TIME E Ghalf H1") as "Upd";
      [apply _|solve_ndisj|].
    iMod (lc_step_fupdN_elim_later with "[£] Upd") as "Upd".
    { iApply (lc_weaken with "£"). rewrite /advance_credits. nia. }
    iMod "Upd" as "[Obs' H1]".
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    wp_seq. iExists -[]. iFrame "L I". iSplit; [done|].
    iCombine "Obs Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=>/= ?[Imp ?]. by apply Imp.
  Qed.

  (** Dropping an owned place: the unblocked leaves are resolved, the pointees of the
      owned pointers of the place are freed ([drop_boxes], recursively, if their memory
      is owned, [own_freeb]), and the memory of the place is freed. The pointees of
      owned pointers in unblocked leaves ([OfTy (own_ptr …)]) are leaked, as by
      [type_delete_instr]. No leaf of the place itself may be blocked or shared
      ([lty_freeb]): their memory is lent. *)
  Lemma type_drop_oplace_instr {𝔄} E L I p n (nz: Z) (lt: lty 𝔄) Φ :
    lty_freeb lt = true → n = lty_size lt → nz = Z.of_nat n → lty_resolve E L lt Φ →
    typed_instr E L I +[p ◁ₗown{n} lt] (drop_boxes lt p;; new_delete.delete [ #nz; p ])%E
      (λ _, +[]) (λ post '-[x], λ mask π, Φ x.1.2 π → post -[] mask π).
  Proof.
    iIntros (Hf -> -> Rslv tid post mask iκs [x []])
      "#LFT #TIME #PROPH #UNIQ #E L I [(%v & %Hp & Own) _] Obs".
    destruct x as [[l x₀] ζm].
    iDestruct "Own" as (D d g) "(#⧖ & _ & -> & %Hle & Fr & Own)".
    iMod (llctx_interp_make_guarded with "L") as (γ) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj|]. iIntros "£ _".
    iMod (Rslv _ (⊤∖↑advN) with "LFT PROPH UNIQ TIME E Ghalf H1 Own") as "[M Upd]";
      [solve_ndisj|].
    iMod (lc_step_fupdN_elim_later with "[£] Upd") as "Upd".
    { iApply (lc_weaken with "£"). rewrite /advance_credits. nia. }
    iMod "Upd" as "[Obs' H1]".
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    have ?: Closed [] p by eapply eval_path_closed.
    wp_bind (drop_boxes lt p).
    have Hev: ⊢ ∀ Ψ (P: iProp Σ), True -∗ ▷^0 P -∗ (True -∗ P -∗ Ψ #l) -∗
      WP p @ ⊤∖↑advN {{ Ψ }}.
    { iIntros (Ψ P) "_ P HΨ". iApply wp_wand; [by iApply wp_eval_path|].
      iIntros (?) "->". by iApply ("HΨ" with "[//] P"). }
    iApply (wp_drop_boxes lt 1 0 l p True%I (⊤∖↑advN) _ ltac:(solve_ndisj) Hf _ ltac:(lia) Hev
      with "[//] M").
    iIntros (vl) "_ Pt %Hl". wp_seq.
    wp_bind p. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->".
    iMod (mapsto_vec_untether_emp _ _ _ ∅ with "[Pt]") as (vl') "[Pt [%Hl' _]]".
    { by rewrite -Hl -heap_cloc_mapsto_fancy_empty. }
    iApply (wp_delete vl' with "[Pt Fr]"); [solve_ndisj|by rewrite Hl' Hl| |].
    { iFrame "Pt". rewrite Hl' Hl. by iApply freeable_sz_full. }
    iIntros "!> _". iExists -[]. iFrame "L I". iSplit; [done|].
    iCombine "Obs Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=>/= ?[Imp ?]. by apply Imp.
  Qed.
End oplace.
