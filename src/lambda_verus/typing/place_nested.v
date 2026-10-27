(** * Unique borrows below a unique borrow, as nested places

  A unique borrow [&uniq{κ'} ty] stored in a place behind a unique borrow at [κ] (e.g.
  [x: &uniq{κ} (&uniq{κ'} (int * int))]) can be unfolded into a _nested place_
  [UniqLty lt κ'] (see [~/verus-belt-phase3-design.md], section "Nested &uniq"): its
  referent is itself a compound place in [Uniq κ' ξi'] mode, held by the inner borrow
  (with its own prophecy variable, pinned body and reservation), inside the node of the
  outer borrow.

  A subplace of the nested place is reached through a pair of contexts [(K1, K2)]: the
  outer context [K1] (in [Owned] mode, to the node [UniqLty]) and the inner context [K2]
  (in the referent of the inner borrow). Its path from the root is
  [nest_path K1 K2 = pctx_path K2 (false :: pctx_path K1 [])], and its value in the
  current value of the root is [nest_get K1 K2].

  - [type_unfold_place_uniq_instr], [type_fold_place_uniq_instr]: unfold the referent of
    a unique borrow of a unique borrow (at the root) into a nested compound place, and
    fold back. Unfolding reserves the outer prophecy variable for the inner one (the
    denotation of the outer place contains the final value of the inner borrow).
  - [type_unfold_place_uniq_deep_instr], [type_fold_place_uniq_deep_instr]: the same,
    below the root (at the hole of any nonempty [K1], also below owned pointers).
  - [tctx_place_nested_change_hole] (e.g. [tctx_unfold_place_nested_prod]): change the
    place type of a subplace of the nested place (unfold it further).
  - [type_reborrow_place_nested_instr]: reborrow a leaf of the nested place at [κ ⊓ α];
    both the inner and the outer prophecy variables are reserved for the reborrow's.
  - [unblock_tctx_place_nested]: unblock it after [κ ⊓ α] has ended.
  - Dropping the outer borrow while all leaves of the nested place are blocked is
    [tctx_drop_place_cpd] ([place.v]).
  See [examples/nested_uniq.v]. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From lrust.lang Require Import proofmode.
From lrust.typing Require Export type ltype lpath place.
From lrust.typing Require Import type_context programs programs_util lft_contexts
  uniq_util uniq_bor product own.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

(** * Values and nested contexts *)

Section nest.
  Context `{!typeG Σ}.

  Definition uniq_bor_set_current {𝔄} (m: ~~ (uniq_borₛ 𝔄)) (y: ~~𝔄) : ~~ (uniq_borₛ 𝔄) :=
    match m with (l, _, ξi, d, g, idx) => (l, y, ξi, d, g, idx) end.

  (** The depths and the index of the value of a unique borrow (which are not part of the
      refinement of a nested place, see [lty_rfn]). *)
  Definition uniq_bor_set_meta {𝔄} (m: ~~ (uniq_borₛ 𝔄)) (d g: nat) (idx: Idx) :
      ~~ (uniq_borₛ 𝔄) :=
    match m with (l, y, ξi, _, _, _) => (l, y, ξi, d, g, idx) end.

  Definition nest_get {𝔅 𝔄' 𝔄} (K1: pctx (uniq_borₛ 𝔄') 𝔄) (K2: pctx 𝔅 𝔄') (x: ~~𝔄) : ~~𝔅 :=
    pctx_get K2 (uniq_bor_current (pctx_get K1 x)).

  Definition nest_set {𝔅 𝔄' 𝔄} (K1: pctx (uniq_borₛ 𝔄') 𝔄) (K2: pctx 𝔅 𝔄') (x: ~~𝔄)
      (y: ~~𝔅) : ~~𝔄 :=
    pctx_set K1 x (uniq_bor_set_current (pctx_get K1 x)
      (pctx_set K2 (uniq_bor_current (pctx_get K1 x)) y)).

  Definition nest_path {𝔅 𝔄' 𝔄} (K1: pctx (uniq_borₛ 𝔄') 𝔄) (K2: pctx 𝔅 𝔄') : lpath :=
    pctx_path K2 (false :: pctx_path K1 []).

  (** The location of the hole (of size [n]). *)
  Definition nest_loc {𝔅 𝔄' 𝔄} (K1: pctx (uniq_borₛ 𝔄') 𝔄) (K2: pctx 𝔅 𝔄') (n: nat)
      (x: ~~𝔄) : cloc :=
    pctx_loc K2 n (uniq_bor_current (pctx_get K1 x)) (uniq_bor_loc (pctx_get K1 x)).

  (** The final value of the reborrow of the blocked leaf at the hole. *)
  Definition place_nest_blk_fin {𝔅 𝔄' 𝔄} (K1: pctx (uniq_borₛ 𝔄') 𝔄) (K2: pctx 𝔅 𝔄')
      (x: ~~ (placeₛ 𝔄)) : proph 𝔅 := λ π,
    (π (uniq_prvar (nest_get K1 K2 (uniq_bor_current (place_bor x)))
      (blk_lookup (place_ζis x) (nest_path K1 K2)))).1.

  Lemma nest_path_below {𝔅 𝔄' 𝔄} (K1: pctx (uniq_borₛ 𝔄') 𝔄) (K2: pctx 𝔅 𝔄') :
    nest_path K1 K2 = (pctx_path K2 [] ++ [false]) ++ pctx_path K1 [].
  Proof. by rewrite /nest_path pctx_path_app -app_assoc. Qed.

  Lemma uniq_prvar_irrel {𝔄} (x x': ~~𝔄) ξi : uniq_prvar x ξi = uniq_prvar x' ξi.
  Proof. by rewrite /uniq_prvar (uniq_cell_tyi_irrel x x'). Qed.

  Lemma prfn_rsv_uniq {𝔄} l' (r: prfn 𝔄) ξi (x: ~~𝔄) ζl :
    prfn_rsv (inr (l', r, ξi) : prfn (uniq_borₛ 𝔄)) ζl ↔
      prfn_rsv r ζl ∧ (λ π, (π (uniq_prvar x ξi)).1) ./ ζl.
  Proof.
    simpl. split; intros [? Hd]; (split; [done|]); intros π π' Hπ; simpl.
    - rewrite (uniq_prvar_app_irrel x (prfn_wit r) ξi π)
        (uniq_prvar_app_irrel x (prfn_wit r) ξi π'). by apply Hd.
    - rewrite (uniq_prvar_app_irrel (prfn_wit r) x ξi π)
        (uniq_prvar_app_irrel (prfn_wit r) x ξi π'). by apply Hd.
  Qed.

  Lemma lty_is_cpd_plug {𝔅 𝔄} (K: pctx 𝔅 𝔄) lt : lty_is_cpd lt → lty_is_cpd (pctx_plug K lt).
  Proof. by destruct K. Qed.

  Lemma lty_is_cpd_plug_nonempty {𝔅 𝔄} (K: pctx 𝔅 𝔄) lt :
    pctx_nonempty K → lty_is_cpd (pctx_plug K lt).
  Proof. by destruct K. Qed.

  Lemma ltype_own_cp_uniq_plug_cpd {𝔅 𝔄} (K: pctx 𝔅 𝔄) lt κ ξi p :
    lty_is_cpd lt →
    ltype_own_cp false (pctx_plug K lt) (Uniq κ ξi) p =
      cpd_own κ ξi (lty_fold (pctx_plug K lt)) p (ltype_own_cp false (pctx_plug K lt) (Owned 0)).
  Proof. intros. destruct K; [by apply ltype_own_cp_uniq_cpd|done..]. Qed.

  Lemma ltype_own_cp_uniq_plug_nest {𝔄' 𝔄} (K1: pctx (uniq_borₛ 𝔄') 𝔄) lt κ' κ ξi p :
    ltype_own_cp false (pctx_plug K1 (UniqLty lt κ')) (Uniq κ ξi) p =
      cpd_own κ ξi (lty_fold (pctx_plug K1 (UniqLty lt κ'))) p
        (ltype_own_cp false (pctx_plug K1 (UniqLty lt κ')) (Owned 0)).
  Proof. by apply ltype_own_cp_uniq_plug_cpd. Qed.

  Lemma pat_ok_uniq_iff κ p : pat_ok κ (PatUniq p) ⊣⊢ pat_ok κ p.
  Proof. done. Qed.

  (** The lifetime of the folded type of a nested place. *)
  Lemma lty_lft_plug_nest_l {𝔄' 𝔄} (K1: pctx (uniq_borₛ 𝔄') 𝔄) lt κ' :
    ⊢ ty_lft (lty_fold (pctx_plug K1 (UniqLty lt κ'))) ⊑ κ'.
  Proof.
    iApply llftl_incl_trans; [iApply (lty_lft_plug K1 (UniqLty lt κ'))|].
    iApply llftl_intersect_incl_l.
  Qed.

  Lemma lty_lft_plug_nest_r {𝔄' 𝔄} (K1: pctx (uniq_borₛ 𝔄') 𝔄) lt κ' :
    ⊢ ty_lft (lty_fold (pctx_plug K1 (UniqLty lt κ'))) ⊑ ty_lft (lty_fold lt).
  Proof.
    iApply llftl_incl_trans; [iApply (lty_lft_plug K1 (UniqLty lt κ'))|].
    iApply llftl_intersect_incl_r.
  Qed.
End nest.

Section typing.
  Context `{!typeG Σ}.

  (** * Unfolding and folding a unique borrow of a unique borrow *)

  (** Unfold the referent [&uniq{κ'} (lty_fold lt)] of a place at the root into the
      nested compound place [UniqLty lt κ'] (with no blocked leaves), given a conversion
      of the inner payload into the node of [lt] (as [cpd_unfold_uniq]). The outer
      borrow is switched to the node of [UniqLty lt κ'] (whose closing view shift folds
      the nested place back lazily, [ltype_owned_leaf_node_uniq]) and reserved for the
      inner prophecy variable (whose token is taken from the inner borrow, before the
      inner place is unfolded and reserved itself). The node gets two cumulative time
      receipts from the program step. *)
  Lemma type_unfold_place_uniq_instr {𝔄} E L I p κ κ' (lt: lty 𝔄) :
    lctx_lft_alive E L κ → lty_is_cpd lt → lty_simple lt →
    pat_blk_lfts (lty_pat lt) = [] → lty_nblk lt = 0%nat →
    (∀ y ζm q, prfn_rsv (lty_rfn lt y ζm q) [] ∧ ∀ π, prfn_den (lty_rfn lt y ζm q) π = vπ y π) →
    (∀ y ζm q d g tid l, ty_gho_own (lty_fold lt) y d g tid ∗ l #↦!∗ ty_phys (lty_fold lt) y tid ⊢
       |={lazyE}=> ltype_own_cp false lt (Owned 0) (lty_pat lt) (lty_rfn lt y ζm q) d g tid l) →
    typed_instr E L I +[p ◁ₗ{κ} OfTy (&uniq{κ'} (lty_fold lt))] (Seq Skip Skip)
      (const +[p ◁ₗ{κ} UniqLty lt κ']) (λ post '-[x], post -[x]).
  Proof.
    intros Alv Hc Hs Hp Hnb Hr Hconv. apply typed_instr_of_skip_sem; [apply place_uniq_own_receipt|].
    iIntros ([[[[[[l x₀] ξi] d'] g'] idx] ζm] v d tid post mask iκs)
      "#LFT #TIME #PROPH #UNIQ #E L $ %Hpath Own _ Obs ⧗a ⧗b _ £".
    destruct x₀ as [[[[[l' y] ξi'] d1] g1] idx'].
    iDestruct "Own" as (d0) "(#⧖0 & ⧗p & -> & %Hle & #Incl & #PtBase & Own)".
    iDestruct (Alv with "L E") as "#Alv".
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iDestruct (guards_transitive with "Ghalf Alv") as "#Hκ".
    iDestruct (lc_weaken 1 with "£") as "£"; [rewrite /advance_credits; lia|].
    iAssert (fractional.half γh &&{↑NllftG}&&> @[κ'])%I as "#Hκ'".
    { iApply (guards_transitive with "Hκ"). iApply (llftl_incl_trans with "Incl").
      iApply llftl_intersect_incl_l. }
    rewrite /ltype_own /=.
    iDestruct "Own" as (x idx0 ->) "(%κp & %γ & #Inclp & (Gh & Tok) & ⧗o & #Bor)".
    iMod (ghost_var_alloc (lstate_triv (𝔄:=unitₛ) ())) as (γf) "Tf".
    set ty := lty_fold lt.
    set node := ltype_own_cp false (UniqLty lt κ') (Owned 0).
    iMod (proph_idx_bor_gen_acc_rebody_rsv ⊤ κ (uniq_prvar (𝔄:=uniq_borₛ 𝔄) (l', y, ξi', d1, g1, idx') ξi)
      (uniq_cell (𝔄:=uniq_borₛ 𝔄) (l', y, ξi', d1, g1, idx') d' g' γ) idx0 (uniq_gbody κp (&uniq{κ'} ty) tid l)
      (cpd_gbody κp γf (&uniq{κ'} ty) node tid l)
      with "LFT PROPH UNIQ Hκ Tok Bor H1") as (wπ) "[Body Close]"; [solve_ndisj|].
    iMod (uniq_gbody_triv_open with "Gh Body") as "(%Hw & Gh & Gh' & Pl)".
    iMod (lc_fupd_elim_later with "£ Pl") as "Pl".
    iMod (uniq_payload_run with "[] H2 Pl") as "(H2 & #⧖' & Gho & Pt)"; [solve_ndisj| |].
    { iApply (guards_transitive with "Hκ Incl"). }
    iDestruct "Gho" as "(#Incl' & %Hle1 & Body1 & #Gpt)".
    iDestruct "Body1" as (κp' γ') "(#Inclp' & (Gh1 & Tok1) & ⧗1 & #Bor1)".
    (* The token of the inner prophecy variable. *)
    iMod (proph_idx_bor_gen_tok_acc with "LFT Hκ' Tok1 Bor1 H2") as "[ξ'tok ξ'back]";
      [solve_ndisj|].
    set r_in := lty_rfn lt y ζm [false].
    set r_o : prfn (uniq_borₛ 𝔄) := inr (l', r_in, ξi').
    iMod (ghost_var_update_halves (lstate (PatUniq (lty_pat lt)) r_o) with "Gh Gh'")
      as "[Gh Gh']".
    iMod ("Close" $! (uniq_cell (𝔄:=uniq_borₛ 𝔄) (l', y, ξi', d1, g1, idx') d' g' γ) wπ [uniq_prvar y ξi'] 1%Qp (fractional.half γh)
      with "[] [ξ'tok] [Gh' Pt ⧗a ⧗b ⧗1 Gh1 ξ'back]") as (idx'') "(Tok & #Bor' & H1 & H2)".
    { (* Back to the body of [&uniq], at the same state. *)
      iIntros "!>" (c2 w2) "Q". iModIntro. iNext.
      iDestruct "Q" as "[Q|[_ $]]". rewrite /cpd_body /uniq_gbody /cpd_body.
      iDestruct "Q" as (p2 r2) "(#Ok & % & Gh2 & Upd)". iExists p2, r2. iFrame "Ok Gh2".
      iSplit; [done|]. iApply (guarded_upd_mono with "[] Upd").
      iIntros "[#⧖2 N] !>". iFrame "⧖2".
      by iApply (ltype_owned_leaf_node_uniq with "TIME LFT PROPH UNIQ Ok ⧖2 N"). }
    { by rewrite big_sepL_singleton. }
    { iIntros "ξ'tok". rewrite big_sepL_singleton.
      iMod ("ξ'back" with "ξ'tok") as "[Tok1 H2]".
      iMod (cpd_unfold_uniq lt κ' ξi' y r_in d1 g1 tid l' ⊤
        with "LFT PROPH UNIQ Hκ' H2 [Gh1 Tok1 ⧗1]") as "[Own1 $]";
        [done|done|done|apply Hr|apply Hr|intros; apply Hconv|solve_ndisj|..].
      { rewrite /ltype_own /=. iExists y, idx'. iSplit; [done|]. iExists κp', γ'.
        iFrame "∗#". }
      iModIntro. iNext. iLeft. rewrite cpd_body_cell.
      iExists (PatUniq (lty_pat lt)), r_o. iFrame "Gh'".
      iSplit; [by rewrite /pat_ok /= Hp|]. iSplit.
      { iPureIntro. intros π. rewrite Hw /r_o /= (proj2 (Hr _ _ _)).
        f_equal. apply uniq_prvar_app_irrel. }
      iApply guarded_upd_intro. iModIntro. iFrame "⧖'".
      rewrite /node /= /uniq_node. iFrame "Pt Incl' Gpt TIME".
      iSplitL "⧗a ⧗b". { iApply (cumulative_time_receipt_sep 1 1). iFrame. }
      iExists d1, g1. iSplit; [done|]. done. }
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "$"; [solve_ndisj|].
    iModIntro. iExists -[((l, (l', y, ξi', d1, g1, idx'), ξi, d', g', idx), ζm)].
    iSplit; [|by iApply (proph_obs_impl with "Obs")]. iSplit; [|done].
    rewrite /tctx_elt_interp. iExists #(l.1). iSplit; [done|]. iExists d0.
    iFrame "⧖0 Incl PtBase". iSplitL "⧗p". { by rewrite /= Hnb. }
    iSplit; [done|]. iSplit; [done|].
    rewrite /ltype_own /=. iExists _, κp, γ, γf, idx'', [uniq_prvar y ξi']. iFrame "∗#".
    iPureIntro. apply (prfn_rsv_uniq _ _ _ y). split.
    - eapply prfn_rsv_weaken; [|apply Hr]. set_solver.
    - apply (proph_dep_constr fst (λ π, π (uniq_prvar y ξi'))), proph_dep_one.
  Qed.

  (** Unfolding a unique borrow of a unique borrow of a pair. *)
  Lemma type_unfold_place_uniq_prod_instr {𝔄 𝔅} E L I p κ κ' (ty1: type 𝔄) (ty2: type 𝔅) :
    lctx_lft_alive E L κ →
    typed_instr E L I +[p ◁ₗ{κ} OfTy (&uniq{κ'} (ty1 * ty2))] (Seq Skip Skip)
      (const +[p ◁ₗ{κ} UniqLty (ProdLty (OfTy ty1) (OfTy ty2)) κ']) (λ post '-[x], post -[x]).
  Proof.
    intros Alv. apply (type_unfold_place_uniq_instr _ _ _ _ _ _ (ProdLty (OfTy ty1) (OfTy ty2)));
      [done|done|done|done|done| |].
    - intros [y1 y2] ζm q. split; [split; apply prfn_rsv_in|].
      intros π. by rewrite /= !prfn_den_in.
    - intros [y1 y2] ζm q d g tid l. iIntros "[Gho Pt] !>".
      iApply prod_ofty_unfold_own. iExists (y1, y2). by iFrame.
  Qed.

  (** Folding back (at the root) a nested place with no blocked leaves, given a
      conversion of its node into the inner payload (as [cpd_fold_uniq]). The outer
      borrow is unreserved and switched back to the body of [&uniq]; the nested place is
      folded back into the inner borrow, which gets a new index (the depths and the
      index of the inner value change, see [uniq_bor_set_meta]). *)
  Lemma type_fold_place_uniq_instr {𝔄} E L I p κ κ' (lt: lty 𝔄) :
    lctx_lft_alive E L κ → lty_is_cpd lt →
    (∀ y ζm q d g tid l, ltype_own_cp false lt (Owned 0) (lty_pat lt) (lty_rfn lt y ζm q) d g tid l ⊢
       |={lazyE}=> ty_gho_own (lty_fold lt) y d g tid ∗ l #↦!∗ ty_phys (lty_fold lt) y tid) →
    typed_instr E L I +[p ◁ₗ{κ} UniqLty lt κ'] (Seq Skip Skip)
      (const +[p ◁ₗ{κ} OfTy (&uniq{κ'} (lty_fold lt))])
      (λ post '-[x], λ mask π, ∀ d1 g1 idx1,
        post -[(uniq_bor_set_current (place_bor x)
          (uniq_bor_set_meta (uniq_bor_current (place_bor x)) d1 g1 idx1), place_ζis x)] mask π).
  Proof.
    intros Alv Hc Hconv. apply typed_instr_of_skip_sem; [apply place_uniq_own_receipt|].
    iIntros ([[[[[[l x₀] ξi] d'] g'] idx] ζm] v d tid post mask iκs)
      "#LFT #TIME #PROPH #UNIQ #E L $ %Hpath Own _ Obs _ _ _ £".
    destruct x₀ as [[[[[l' y] ξi'] d1] g1] idx'].
    iDestruct "Own" as (d0) "(#⧖0 & ⧗p & -> & %Hle & #Incl & #PtBase & Own)".
    iDestruct (Alv with "L E") as "#Alv".
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iDestruct (guards_transitive with "Ghalf Alv") as "#Hκ".
    iDestruct (lc_weaken 1 with "£") as "£"; [rewrite /advance_credits; lia|].
    iAssert (fractional.half γh &&{↑NllftG}&&> @[κ'])%I as "#Hκ'".
    { iApply (guards_transitive with "Hκ"). iApply (llftl_incl_trans with "Incl").
      iApply llftl_intersect_incl_l. }
    set ty := lty_fold lt.
    rewrite /ltype_own /=.
    iDestruct "Own" as (x₀w κp γ γf idx0 ζl) "(#Inclp & _ & Tok & Gh & Tf & ⧗o & #Bor)".
    iMod (proph_idx_bor_gen_unreserve with "LFT PROPH UNIQ Hκ H1 Tok Bor") as "[Tok H1]";
      [solve_ndisj|].
    have ?: Inhabited (~~ (uniq_borₛ 𝔄)) := populate x₀w.
    iMod (proph_idx_bor_gen_acc_rebody_guarded ⊤ κ (uniq_prvar x₀w ξi) (uniq_cell x₀w d' g' γ)
      idx0 _ (uniq_gbody κp (&uniq{κ'} ty) tid l)
      with "LFT UNIQ Hκ Tok Bor H1") as (wπ) "[Body Close]"; [solve_ndisj|].
    iDestruct (bi.later_or with "Body") as "[Body|[>Tf' _]]"; last first.
    { iDestruct (cpd_tok_excl with "Tf Tf'") as "[]". }
    rewrite cpd_body_cell.
    iMod (lc_fupd_elim_later with "£ Body") as (p1 r1) "(_ & _ & Gh' & Upd)".
    iDestruct (ghost_var_agree with "Gh Gh'") as %[<- <-]%lstate_inj.
    iMod (guarded_upd_run with "[] H2 Upd") as "(H2 & #⧖' & N)"; [solve_ndisj| |].
    { iApply (guards_transitive with "Hκ Incl"). }
    iDestruct "N" as "(Pt & _ & _ & #Incl' & #Gpt & %d2 & %g2 & %Hle2 & C)".
    iMod (cpd_fold_uniq lt κ' ξi' y _ d2 g2 tid l' ⊤ with "LFT PROPH UNIQ Hκ' H2 C")
      as "[Own1 H2]"; [done|intros; apply Hconv|solve_ndisj|].
    rewrite /ltype_own /=. iDestruct "Own1" as (y' idx1 ->) "Body1".
    iMod (ghost_var_update_halves (lstate_triv (𝔄:=uniq_borₛ 𝔄) (l', y, ξi', d2, g2, idx1)) with "Gh Gh'")
      as "[Gh Gh']".
    iSpecialize ("Close" $! (uniq_cell (𝔄:=uniq_borₛ 𝔄) (l', y, ξi', d2, g2, idx1) d' g' γ)
      (vπ (uniq_cell (𝔄:=uniq_borₛ 𝔄) (l', y, ξi', d2, g2, idx1) d' g' γ))).
    iMod (fupd_mask_mono with "(Close [Gh' Pt Body1] [Tf])") as (idx2) "(Tok & #Bor' & H1)";
      [solve_ndisj| | |].
    { iApply (uniq_gbody_triv_close with "Gh'"); [done|]. iNext.
      iApply (uniq_payload_intro (&uniq{κ'} ty) tid l (l', y, ξi', d2, g2, idx1) d' g'
        with "⧖' [Body1] Pt"). iFrame "Incl' Body1 Gpt".
      iPureIntro. lia. }
    { iIntros "!>" (c2 w2) "P". iModIntro. iNext. iRight. iFrame. }
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "$"; [solve_ndisj|].
    iModIntro. iExists -[((l, (l', y, ξi', d2, g2, idx1), ξi, d', g', idx), ζm)].
    iSplit; [|iApply (proph_obs_impl with "Obs"); by intros π Hπ; apply Hπ].
    iSplit; [|done].
    rewrite /tctx_elt_interp. iExists #(l.1). iSplit; [done|]. iExists d0.
    iFrame "⧖0 Incl PtBase". iSplitL "⧗p".
    { iApply (cumulative_time_receipt_mono with "⧗p"). simpl. lia. }
    iSplit; [done|]. iSplit; [done|].
    rewrite /ltype_own /=. iExists _, idx2. iSplit; [done|].
    iApply (uniq_body_from_parts with "Inclp [Gh Tok] ⧗o [Bor']").
    - rewrite /uniq_tokγ (uniq_bor_tok_retarget _ x₀w). iFrame.
    - by rewrite /uniq_persγ (uniq_idx_bor_gen_retarget _ _ x₀w).
  Qed.

  Lemma type_fold_place_uniq_prod_instr {𝔄 𝔅} E L I p κ κ' (ty1: type 𝔄) (ty2: type 𝔅) :
    lctx_lft_alive E L κ →
    typed_instr E L I +[p ◁ₗ{κ} UniqLty (ProdLty (OfTy ty1) (OfTy ty2)) κ'] (Seq Skip Skip)
      (const +[p ◁ₗ{κ} OfTy (&uniq{κ'} (ty1 * ty2))])
      (λ post '-[x], λ mask π, ∀ d1 g1 idx1,
        post -[(uniq_bor_set_current (place_bor x)
          (uniq_bor_set_meta (uniq_bor_current (place_bor x)) d1 g1 idx1), place_ζis x)] mask π).
  Proof.
    intros Alv. apply (type_fold_place_uniq_instr _ _ _ _ _ _ (ProdLty (OfTy ty1) (OfTy ty2)));
      [done|done|].
    intros [y1 y2] ζm q d g tid l. iIntros "H !>".
    iDestruct (prod_ofty_unfold_own with "H") as (? ->) "[$ $]".
  Qed.

  (** * Unfolding and folding a unique borrow below the root

      The same, for a unique borrow at the hole of a nonempty context [K1] (at any path,
      also below owned pointers) of a place rooted at a unique borrow. The body of the
      outer borrow is switched to the new node ([cpd_rebody_ext], whose closing view
      shift folds the nested place back lazily, [ltype_owned_leaf_node]) and its
      reservation is extended by the inner prophecy variable in the same opening. Below
      [m] owned pointers, the node of [UniqLty] holds [2 + m] cumulative time receipts
      (from the second program step) and the contents of the inner borrow are under [m]
      laters (stripped with the credits of the first step). *)
  Lemma type_unfold_place_uniq_deep_instr {𝔄' 𝔄} E L I p κ κ' (K1: pctx (uniq_borₛ 𝔄') 𝔄)
      (lt: lty 𝔄') :
    lctx_lft_alive E L κ → pctx_nonempty K1 → pctx_simple K1 →
    lty_is_cpd lt → lty_simple lt → pat_blk_lfts (lty_pat lt) = [] → lty_nblk lt = 0%nat →
    (∀ y ζm q, prfn_rsv (lty_rfn lt y ζm q) [] ∧ ∀ π, prfn_den (lty_rfn lt y ζm q) π = vπ y π) →
    (∀ y ζm q d g tid l, ty_gho_own (lty_fold lt) y d g tid ∗ l #↦!∗ ty_phys (lty_fold lt) y tid ⊢
       |={lazyE}=> ltype_own_cp false lt (Owned 0) (lty_pat lt) (lty_rfn lt y ζm q) d g tid l) →
    typed_instr E L I +[p ◁ₗ{κ} pctx_plug K1 (OfTy (&uniq{κ'} (lty_fold lt)))] (Seq Skip Skip)
      (const +[p ◁ₗ{κ} pctx_plug K1 (UniqLty lt κ')]) (λ post '-[x], post -[x]).
  Proof.
    intros Alv HK1 HKs Hc Hs Hp Hnb Hr Hconv tid post mask iκs [x []].
    iIntros "#LFT #TIME #PROPH #UNIQ #E L I [T _] Obs".
    destruct x as [[[[[[l x₀] ξi] d'] g'] idx] ζm].
    rewrite /tctx_elt_interp.
    iDestruct "T" as (v Hpath) "(%d0 & #⧖0 & ⧗p & -> & %Hle & #Incl & #PtBase & Own)".
    (* Two steps, for credits and cumulative time receipts. *)
    wp_bind Skip. iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME ⧖0"); [set_solver|].
    iIntros "£ #⧖S". wp_let. iModIntro. wp_let. iApply wp_fupd.
    iApply (wp_cumulative_time_receipt_linear with "TIME ⧖S"); [set_solver|].
    iIntros "⧗". wp_let.
    set ty := lty_fold lt. set m := pctx_mode K1 0.
    iDestruct (Alv with "L E") as "#Alv".
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iDestruct (guards_transitive with "Ghalf Alv") as "#Hκ".
    iAssert (fractional.half γh &&{↑NllftG}&&> @[κ'])%I as "#Hκ'".
    { iApply (guards_transitive with "Hκ"). iApply (llftl_incl_trans with "Incl").
      iApply llftl_incl_trans; [iApply (lty_lft_plug K1 (OfTy (&uniq{κ'} ty)))|].
      iApply llftl_intersect_incl_l. }
    rewrite /ltype_own ltype_own_cp_uniq_plug //.
    iMod (cpd_rebody_ext with "LFT PROPH UNIQ Hκ H1 Own") as (κp) "(#Inclp & #Ok & Upd & Close)";
      [solve_ndisj|].
    iDestruct (lc_weaken (1 + (advance_credits d0 - 1)) with "£") as "[£a £]";
      [rewrite /advance_credits; lia|].
    iMod (lc_fupd_elim_later with "£a Upd") as "Upd".
    iMod (guarded_upd_run with "[] H2 Upd") as "(H2 & #⧖' & N)"; [solve_ndisj| |].
    { iApply (guards_transitive with "Hκ Incl"). }
    rewrite lty_pat_plug lty_rfn_plug ltype_own_plug.
    iDestruct "N" as "[L1 Rest]". iSimpl in "L1".
    iDestruct "L1" as (? ->) "[Pt Gho]".
    iDestruct (pctx_own_mode_le with "Rest") as %Hk.
    iDestruct (lc_weaken m with "£") as "£"; [rewrite /advance_credits /m; nia|].
    iMod (lc_fupd_elim_laterN with "£ Gho") as "Gho".
    destruct (pctx_get K1 x₀) as [[[[[l' y] ξi'] d1] g1] idx'] eqn:Hm.
    iDestruct "Gho" as "(#Incl' & %Hle1 & Body1 & #Gpt)".
    iDestruct "Body1" as (κp' γ') "(#Inclp' & (Gh1 & Tok1) & ⧗1 & #Bor1)".
    iDestruct (cumulative_time_receipt_mono (2 + m) with "⧗") as "⧗"; [rewrite /m; lia|].
    (* The token of the inner prophecy variable. *)
    iMod (proph_idx_bor_gen_tok_acc with "LFT Hκ' Tok1 Bor1 H2") as "[ξ'tok ξ'back]";
      [solve_ndisj|].
    set q1 := false :: pctx_path K1 [].
    set r_in := lty_rfn lt y ζm q1.
    set dh := pctx_depth K1 d'.
    iMod ("Close" $! (pctx_pat K1 (PatUniq (lty_pat lt))) (pctx_rfn K1 x₀ ζm [] (inr (l', r_in, ξi')))
      d' g' [uniq_prvar y ξi'] 1%Qp (fractional.half γh)
      with "[] [] [ξ'tok] [Pt ⧗ ⧗1 Gh1 ξ'back Rest]") as "(Own & H1 & H2)".
    { iPureIntro. intros ζl. apply pctx_rfn_rsv_mono; [set_solver|]. intros _.
      apply (prfn_rsv_uniq _ _ _ y). split.
      - eapply prfn_rsv_weaken; [|apply Hr]. set_solver.
      - apply (proph_dep_weaken _ [uniq_prvar y ξi']); [set_solver|].
        apply (proph_dep_constr fst (λ π, π (uniq_prvar y ξi'))), proph_dep_one. }
    { iIntros "!>" (p2 r2 d2 g2) "Ok2 ⧖ N".
      rewrite -(lty_fold_plug_eq' K1 (UniqLty lt κ') (OfTy (&uniq{κ'} ty))); [|done].
      iApply (ltype_owned_leaf_node with "LFT PROPH UNIQ Ok2 ⧖ N");
        [by apply lty_is_cpd_plug|by apply lty_simple_plug]. }
    { by rewrite big_sepL_singleton. }
    { iIntros "ξ'tok". rewrite big_sepL_singleton.
      iMod ("ξ'back" with "ξ'tok") as "[Tok1 H2]".
      iMod (cpd_unfold_uniq lt κ' ξi' y r_in d1 g1 tid l' ⊤
        with "LFT PROPH UNIQ Hκ' H2 [Gh1 Tok1 ⧗1]") as "[Own1 H2]";
        [done|done|done|apply Hr|apply Hr|intros; apply Hconv|solve_ndisj|..].
      { rewrite /ltype_own /=. iExists y, idx'. iSplit; [done|]. iExists κp', γ'.
        iFrame "∗#". }
      iModIntro. iFrame "H2". iSplitR.
      { iNext. iApply (pat_ok_plug with "Ok"). by rewrite /pat_ok /= Hp. }
      iNext. iApply guarded_upd_intro. iModIntro. iFrame "⧖'".
      rewrite ltype_own_plug. iFrame "Rest".
      rewrite /= /uniq_node. iFrame "Pt ⧗ TIME". iApply bi.laterN_intro.
      iFrame "Incl' Gpt". iExists d1, g1. iSplit; [done|]. done. }
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "$"; [solve_ndisj|].
    iModIntro. iExists -[((l, x₀, ξi, d', g', idx), ζm)]. iFrame "I".
    iSplit; [|by iApply (proph_obs_impl with "Obs")]. iSplit; [|done].
    rewrite /tctx_elt_interp. iExists #(l.1). iSplit; [done|]. iExists d0.
    iFrame "⧖0 PtBase". iSplitL "⧗p". { by rewrite !lty_nblk_plug /= Hnb. }
    iSplit; [done|]. iSplit; [done|].
    iSplit. { by rewrite (lty_fold_plug_eq' K1 (UniqLty lt κ') (OfTy (&uniq{κ'} ty))). }
    rewrite /ltype_own ltype_own_cp_uniq_plug_nest lty_pat_plug lty_rfn_plug /= Hm /=.
    rewrite (lty_fold_plug_eq' K1 (UniqLty lt κ') (OfTy (&uniq{κ'} ty))) //.
  Qed.

  (** Folding back (below the root) a nested place with no blocked leaves, given a
      conversion of its node into the inner payload. The outer borrow is switched back
      to the node with the leaf [&uniq{κ'} (lty_fold lt)] ([cpd_rebody]; the
      reservation is kept, it may over-approximate), the nested place is folded back into
      the inner borrow ([cpd_fold_uniq]), which gets new depths and a new index. *)
  Lemma type_fold_place_uniq_deep_instr {𝔄' 𝔄} E L I p κ κ' (K1: pctx (uniq_borₛ 𝔄') 𝔄)
      (lt: lty 𝔄') :
    lctx_lft_alive E L κ → pctx_nonempty K1 → pctx_simple K1 → lty_is_cpd lt →
    (∀ y ζm q d g tid l, ltype_own_cp false lt (Owned 0) (lty_pat lt) (lty_rfn lt y ζm q) d g tid l ⊢
       |={lazyE}=> ty_gho_own (lty_fold lt) y d g tid ∗ l #↦!∗ ty_phys (lty_fold lt) y tid) →
    typed_instr E L I +[p ◁ₗ{κ} pctx_plug K1 (UniqLty lt κ')] (Seq Skip Skip)
      (const +[p ◁ₗ{κ} pctx_plug K1 (OfTy (&uniq{κ'} (lty_fold lt)))])
      (λ post '-[x], λ mask π, ∀ d1 g1 idx1,
        post -[(uniq_bor_set_current (place_bor x)
          (pctx_set K1 (uniq_bor_current (place_bor x))
            (uniq_bor_set_meta (pctx_get K1 (uniq_bor_current (place_bor x))) d1 g1 idx1)),
          place_ζis x)] mask π).
  Proof.
    intros Alv HK1 HKs Hc Hconv. apply typed_instr_of_skip_sem; [apply place_uniq_own_receipt|].
    iIntros ([[[[[[l x₀] ξi] d'] g'] idx] ζm] v d tid post mask iκs)
      "#LFT #TIME #PROPH #UNIQ #E L $ %Hpath Own _ Obs ⧗a _ _ _".
    iDestruct "Own" as (d0) "(#⧖0 & ⧗p & -> & %Hle & #Incl & #PtBase & Own)".
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗a ⧖0") as "[_ £]";
      [solve_ndisj|].
    set ty := lty_fold lt. set m := pctx_mode K1 0.
    iDestruct (Alv with "L E") as "#Alv".
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iDestruct (guards_transitive with "Ghalf Alv") as "#Hκ".
    iAssert (fractional.half γh &&{↑NllftG}&&> @[κ'])%I as "#Hκ'".
    { iApply (guards_transitive with "Hκ"). iApply (llftl_incl_trans with "Incl").
      iApply lty_lft_plug_nest_l. }
    rewrite /ltype_own ltype_own_cp_uniq_plug_nest.
    iMod (cpd_rebody with "LFT PROPH UNIQ Hκ H1 Own") as (κp) "(#Inclp & #Ok & Upd & Close)";
      [solve_ndisj|].
    iDestruct (lc_weaken (1 + (advance_credits d0 - 1)) with "£") as "[£a £]";
      [rewrite /advance_credits; lia|].
    iMod (lc_fupd_elim_later with "£a Upd") as "Upd".
    iMod (guarded_upd_run with "[] H2 Upd") as "(H2 & #⧖' & N)"; [solve_ndisj| |].
    { iApply (guards_transitive with "Hκ Incl"). }
    rewrite lty_pat_plug lty_rfn_plug ltype_own_plug.
    iDestruct "N" as "[N1 Rest]".
    iDestruct (pctx_own_in with "Rest") as %Hin.
    iDestruct (pctx_own_mode_le with "Rest") as %Hk.
    destruct (pctx_get K1 x₀) as [[[[[l' y] ξi'] d1] g1] idx'] eqn:Hm.
    iDestruct "N1" as "(Pt & _ & _ & N1)".
    iDestruct (lc_weaken m with "£") as "£"; [rewrite /advance_credits /m; nia|].
    iMod (lc_fupd_elim_laterN with "£ N1") as "(#Incl' & #Gpt & %d2 & %g2 & %Hle2 & C)".
    iMod (cpd_fold_uniq lt κ' ξi' y _ d2 g2 tid l' ⊤ with "LFT PROPH UNIQ Hκ' H2 C")
      as "[Own1 H2]"; [done|intros; apply Hconv|solve_ndisj|].
    rewrite /ltype_own /=. iDestruct "Own1" as (y' idx1 ->) "Body1".
    set m2 : ~~ (uniq_borₛ 𝔄') := (l', y, ξi', d2, g2, idx1).
    iMod ("Close" $! (pctx_pat K1 PatLeaf) (pctx_rfn K1 x₀ ζm [] (inl (PlaceIn m2))) d' g'
      with "[%] [] [] [Pt Body1 Rest]") as "[Own H1]".
    { intros ζl. apply pctx_rfn_rsv_mono; [done|]. intros _. apply prfn_rsv_in. }
    { iIntros "!>" (p2 r2 d3 g3) "Ok2 ⧖ N".
      rewrite (lty_fold_plug_eq' K1 (UniqLty lt κ') (OfTy (&uniq{κ'} ty))); [|done].
      iApply (ltype_owned_leaf_node with "LFT PROPH UNIQ Ok2 ⧖ N");
        [by apply lty_is_cpd_plug_nonempty|by apply lty_simple_plug]. }
    { iNext. iApply (pat_ok_plug with "Ok"). iApply pat_ok_leaf. }
    { iNext. iApply guarded_upd_intro. iModIntro. iFrame "⧖'".
      rewrite ltype_own_plug. iFrame "Rest".
      iExists m2. iSplit; [done|]. rewrite /ofty_owned /=. iFrame "Pt".
      iApply bi.laterN_intro. iFrame "Incl' Body1 Gpt". iPureIntro. lia. }
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "$"; [solve_ndisj|].
    iModIntro. iExists -[((l, pctx_set K1 x₀ m2, ξi, d', g', idx), ζm)].
    iSplit; last first.
    { iApply (proph_obs_impl with "Obs")=> π Hπ. move: (Hπ d2 g2 idx1). by rewrite /= Hm. }
    iSplit; [|done].
    rewrite /tctx_elt_interp. iExists #(l.1). iSplit; [done|]. iExists d0.
    iFrame "⧖0 PtBase". iSplitL "⧗p".
    { iApply (cumulative_time_receipt_mono with "⧗p"). rewrite !lty_nblk_plug /=. lia. }
    iSplit; [done|]. iSplit; [done|].
    iSplit. { by rewrite -(lty_fold_plug_eq' K1 (UniqLty lt κ') (OfTy (&uniq{κ'} ty))). }
    rewrite (lty_fold_plug_eq' K1 (UniqLty lt κ') (OfTy (&uniq{κ'} ty))) //.
    rewrite /ltype_own ltype_own_cp_uniq_plug // lty_pat_plug lty_rfn_plug pctx_get_set
      pctx_rfn_set //.
  Qed.

  (** * Changing the place type of a subplace of a nested place

      The subplace at the hole of [K2] (nonempty) of the nested place at the hole of [K1]
      (below no owned pointer) is changed from [lt] to [lt'], as in
      [tctx_place_change_hole]: the bodies of both borrows are switched to their new
      nodes ([cpd_rebody]), the inner one inside the lazy update of the contents of the
      outer one (so no program step is needed). This allows unfolding the nested place
      further after the nested unfold. *)
  Lemma tctx_place_nested_change_hole {𝔅 𝔄' 𝔄} E L p κ κ' (K1: pctx (uniq_borₛ 𝔄') 𝔄)
      (K2: pctx 𝔅 𝔄') (lt lt': lty 𝔅) :
    lctx_lft_alive E L κ → pctx_noderef K1 → pctx_simple K1 → pctx_nonempty K2 →
    pctx_simple K2 → lty_simple lt' →
    lty_size lt' = lty_size lt → lty_fold lt' = lty_fold lt → lty_nblk lt' = lty_nblk lt →
    (∀ α, α ∈ pat_blk_lfts (lty_pat lt') → α ∈ pat_blk_lfts (lty_pat lt)) →
    (∀ y ζm q ζl, prfn_rsv (lty_rfn lt y ζm q) ζl → prfn_rsv (lty_rfn lt' y ζm q) ζl) →
    (∀ y ζm q d g tid l, ltype_own (Owned (pctx_mode K2 0)) lt (lty_rfn lt y ζm q) d g tid l ⊢
       |={lazyE}=> ltype_own (Owned (pctx_mode K2 0)) lt' (lty_rfn lt' y ζm q) d g tid l) →
    tctx_incl E L +[p ◁ₗ{κ} pctx_plug K1 (UniqLty (pctx_plug K2 lt) κ')]
      +[p ◁ₗ{κ} pctx_plug K1 (UniqLty (pctx_plug K2 lt') κ')] (λ post '-[x], post -[x]).
  Proof.
    intros Alv HK1 HK1s HK2 HK2s Hs' Hsz Hfold Hnb Hpat Hrsv Hown.
    split; [by intros ??? [? []]|].
    iIntros (G tid [x []] mask post ?) "#LFT #PROPH #UNIQ #E #GL G [T _] Obs".
    destruct x as [[[[[[l x₀] ξi] d'] g'] idx] ζm].
    rewrite /tctx_elt_interp.
    iDestruct "T" as (v ?) "(%d & ⧖ & ⧗ & -> & %Hle & #Incl & #Pt & Own)".
    leaf_open "GL" with "G" as "[L back]"; [set_solver|].
    iDestruct (Alv with "L E") as "#Lκ". iMod ("back" with "L") as "G".
    iDestruct (guards_transitive with "GL Lκ") as "#Gκ".
    have Hfold': lty_fold (UniqLty (pctx_plug K2 lt') κ') = lty_fold (UniqLty (pctx_plug K2 lt) κ').
    { by rewrite /= (lty_fold_plug_eq' K2 lt' lt). }
    destruct (pctx_get K1 x₀) as [[[[[l' y] ξi'] d1] g1] idx'] eqn:Hm.
    set q1 := false :: pctx_path K1 [].
    rewrite /ltype_own !ltype_own_cp_uniq_plug_nest.
    iMod (cpd_rebody with "LFT PROPH UNIQ Gκ G Own") as (κp) "(#Inclp & #Ok & Upd & Close)";
      [solve_ndisj|].
    iMod ("Close" $! (lty_pat (pctx_plug K1 (UniqLty (pctx_plug K2 lt') κ')))
      (lty_rfn (pctx_plug K1 (UniqLty (pctx_plug K2 lt') κ')) x₀ ζm []) d' g'
      with "[%] [] [] [Upd]") as "[Own G]".
    - intros ζl. rewrite !lty_rfn_plug /= Hm /=. apply pctx_rfn_rsv_mono; [done|].
      intros Hr. apply (prfn_rsv_uniq _ _ _ y) in Hr as [Hr Hξ].
      apply (prfn_rsv_uniq _ _ _ y). split; [|done].
      rewrite !lty_rfn_plug in Hr |- *. eapply pctx_rfn_rsv_mono; [done| |exact Hr].
      by apply Hrsv.
    - iIntros "!>" (p2 r2 d2 g2) "Ok2 ⧖ N". rewrite -(lty_fold_plug_eq' K1 _ _ Hfold').
      iApply (ltype_owned_leaf_node with "LFT PROPH UNIQ Ok2 ⧖ N");
        [by apply lty_is_cpd_plug|apply lty_simple_plug; [done|by apply lty_simple_plug]].
    - iNext. rewrite !lty_pat_plug /=. iApply (pat_ok_plug with "Ok"). rewrite pat_ok_uniq_iff.
      iDestruct (pat_ok_plug_hole with "Ok") as "Ok1". rewrite pat_ok_uniq_iff.
      iEval (rewrite lty_pat_plug) in "Ok1". rewrite (lty_pat_plug K2 lt').
      iApply (pat_ok_plug with "Ok1"). iApply (pat_ok_incl with "[]"); [done|].
      iApply (pat_ok_plug_hole with "Ok1").
    - iNext. iApply (guarded_upd_wand with "[] Upd"). iIntros (G0 ?) "#G0k G0 [$ N]".
      rewrite !lty_pat_plug !lty_rfn_plug !ltype_own_plug pctx_mode_noderef //
        pctx_depth_noderef //.
      iDestruct "N" as "[H $]". rewrite Hm /=.
      iDestruct "H" as "(Pt' & ⧗n & #TIMEn & #Incl' & #Gpt' & %d1' & %g1' & %Hle1 & C)".
      iAssert (G0 &&{↑NllftG}&&> @[κ'])%I as "#G0κ'".
      { iApply (guards_transitive with "G0k"). iApply lty_lft_plug_nest_l. }
      iMod (ltype_own_uniq_change_hole_gen κ' ξi' K2 lt lt' y ζm q1 d1' g1' tid l' lazyE G0
        with "LFT PROPH UNIQ G0κ' G0 [C]") as "[C $]";
        [done|done|done|done|done|done| | |rewrite /lazyE; solve_ndisj| |].
      { intros ???. apply Hrsv. }
      { intros ??????. apply Hown. }
      { iExact "C". }
      iModIntro. rewrite /= /uniq_node (lty_fold_plug_eq' K2 lt' lt Hfold).
      iFrame "Pt' ⧗n TIMEn Incl' Gpt'". iExists d1', g1'. iSplit; [done|]. iExact "C".
    - iModIntro. iExists -[((l, x₀, ξi, d', g', idx), ζm)]. iFrame "G Obs".
      iSplit; [|done]. iExists #(l.1). iSplit; [done|]. iExists d.
      rewrite (lty_fold_plug_eq' K1 _ _ Hfold'). iFrame "⧖ Incl Pt". iSplitL "⧗".
      { by rewrite !lty_nblk_plug /= !lty_nblk_plug Hnb. }
      iSplit; [done|]. iSplit; [done|].
      rewrite /ltype_own ltype_own_cp_uniq_plug_nest (lty_fold_plug_eq' K1 _ _ Hfold').
      iExact "Own".
  Qed.

  (** Unfolding a unique borrow of a pair below the root. *)
  Lemma type_unfold_place_uniq_prod_deep_instr {𝔄1 𝔄2 𝔄} E L I p κ κ'
      (K1: pctx (uniq_borₛ (𝔄1 * 𝔄2)) 𝔄) (ty1: type 𝔄1) (ty2: type 𝔄2) :
    lctx_lft_alive E L κ → pctx_nonempty K1 → pctx_simple K1 →
    typed_instr E L I +[p ◁ₗ{κ} pctx_plug K1 (OfTy (&uniq{κ'} (ty1 * ty2)))] (Seq Skip Skip)
      (const +[p ◁ₗ{κ} pctx_plug K1 (UniqLty (ProdLty (OfTy ty1) (OfTy ty2)) κ')])
      (λ post '-[x], post -[x]).
  Proof.
    intros Alv HK1 HK1s.
    apply (type_unfold_place_uniq_deep_instr _ _ _ _ _ _ K1 (ProdLty (OfTy ty1) (OfTy ty2)));
      [done|done|done|done|done|done|done| |].
    - intros [y1 y2] ζm q. split; [split; apply prfn_rsv_in|].
      intros π. by rewrite /= !prfn_den_in.
    - intros [y1 y2] ζm q d g tid l. iIntros "[Gho Pt] !>".
      iApply prod_ofty_unfold_own. iExists (y1, y2). by iFrame.
  Qed.

  Lemma type_fold_place_uniq_prod_deep_instr {𝔄1 𝔄2 𝔄} E L I p κ κ'
      (K1: pctx (uniq_borₛ (𝔄1 * 𝔄2)) 𝔄) (ty1: type 𝔄1) (ty2: type 𝔄2) :
    lctx_lft_alive E L κ → pctx_nonempty K1 → pctx_simple K1 →
    typed_instr E L I +[p ◁ₗ{κ} pctx_plug K1 (UniqLty (ProdLty (OfTy ty1) (OfTy ty2)) κ')]
      (Seq Skip Skip) (const +[p ◁ₗ{κ} pctx_plug K1 (OfTy (&uniq{κ'} (ty1 * ty2)))])
      (λ post '-[x], λ mask π, ∀ d1 g1 idx1,
        post -[(uniq_bor_set_current (place_bor x)
          (pctx_set K1 (uniq_bor_current (place_bor x))
            (uniq_bor_set_meta (pctx_get K1 (uniq_bor_current (place_bor x))) d1 g1 idx1)),
          place_ζis x)] mask π).
  Proof.
    intros Alv HK1 HK1s.
    apply (type_fold_place_uniq_deep_instr _ _ _ _ _ _ K1 (ProdLty (OfTy ty1) (OfTy ty2)));
      [done|done|done|done|].
    intros [y1 y2] ζm q d g tid l. iIntros "H !>".
    iDestruct (prod_ofty_unfold_own with "H") as (? ->) "[$ $]".
  Qed.

  (** Unfolding and folding a pair inside a nested place. *)
  Lemma tctx_unfold_place_nested_prod {𝔅1 𝔅2 𝔄' 𝔄} E L p κ κ' (K1: pctx (uniq_borₛ 𝔄') 𝔄)
      (K2: pctx (𝔅1 * 𝔅2) 𝔄') (ty1: type 𝔅1) (ty2: type 𝔅2) :
    lctx_lft_alive E L κ → pctx_noderef K1 → pctx_simple K1 → pctx_nonempty K2 →
    pctx_simple K2 →
    tctx_incl E L +[p ◁ₗ{κ} pctx_plug K1 (UniqLty (pctx_plug K2 (OfTy (ty1 * ty2))) κ')]
      +[p ◁ₗ{κ} pctx_plug K1 (UniqLty (pctx_plug K2 (ProdLty (OfTy ty1) (OfTy ty2))) κ')]
      (λ post '-[x], post -[x]).
  Proof.
    intros. apply tctx_place_nested_change_hole; [done..| | |].
    - intros ?; simpl; set_solver.
    - intros ?????. split; apply prfn_rsv_in.
    - intros [y1 y2] ??????. iIntros "H !>". by iApply prod_ofty_unfold_own.
  Qed.

  Lemma tctx_fold_place_nested_prod {𝔅1 𝔅2 𝔄' 𝔄} E L p κ κ' (K1: pctx (uniq_borₛ 𝔄') 𝔄)
      (K2: pctx (𝔅1 * 𝔅2) 𝔄') (ty1: type 𝔅1) (ty2: type 𝔅2) :
    lctx_lft_alive E L κ → pctx_noderef K1 → pctx_simple K1 → pctx_nonempty K2 →
    pctx_simple K2 →
    tctx_incl E L +[p ◁ₗ{κ} pctx_plug K1 (UniqLty (pctx_plug K2 (ProdLty (OfTy ty1) (OfTy ty2))) κ')]
      +[p ◁ₗ{κ} pctx_plug K1 (UniqLty (pctx_plug K2 (OfTy (ty1 * ty2))) κ')]
      (λ post '-[x], post -[x]).
  Proof.
    intros. apply tctx_place_nested_change_hole; [done..| | |].
    - intros ?; simpl; set_solver.
    - intros ?????. apply prfn_rsv_in.
    - intros [y1 y2] ??????. iIntros "H !>". by iApply (prod_ofty_unfold_own with "H").
  Qed.

  (** * Reborrowing a leaf of a nested place *)

  (** The refinement of a nested place whose hole has refinement [r]. *)
  Lemma lty_rfn_plug_nest {𝔅 𝔄' 𝔄} (K1: pctx (uniq_borₛ 𝔄') 𝔄) (K2: pctx 𝔅 𝔄') lt κ' x ζm :
    lty_rfn (pctx_plug K1 (UniqLty (pctx_plug K2 lt) κ')) x ζm [] =
      pctx_rfn K1 x ζm [] (inr (uniq_bor_loc (pctx_get K1 x),
        pctx_rfn K2 (uniq_bor_current (pctx_get K1 x)) ζm (false :: pctx_path K1 [])
          (lty_rfn lt (nest_get K1 K2 x) ζm (nest_path K1 K2)),
        uniq_bor_ξi (pctx_get K1 x))).
  Proof. by rewrite lty_rfn_plug /= lty_rfn_plug. Qed.

  (** Adding an entry for the path of the hole. *)
  Lemma pctx_rfn_blk_cons_nest {𝔅 𝔄' 𝔄} (K1: pctx (uniq_borₛ 𝔄') 𝔄) (K2: pctx 𝔅 𝔄') x ζm ζi
      l' x' ξi' r :
    pctx_rfn K1 x ((nest_path K1 K2, ζi) :: ζm) []
      (inr (l', pctx_rfn K2 x' ((nest_path K1 K2, ζi) :: ζm) (false :: pctx_path K1 []) r, ξi')) =
    pctx_rfn K1 x ζm [] (inr (l', pctx_rfn K2 x' ζm (false :: pctx_path K1 []) r, ξi')).
  Proof.
    rewrite {1}nest_path_below pctx_rfn_blk_cons_below.
    by rewrite /nest_path pctx_rfn_blk_cons.
  Qed.

  Lemma pctx_own_blk_cons_nest {𝔅 𝔄' 𝔄} (K1: pctx (uniq_borₛ 𝔄') 𝔄) (K2: pctx 𝔅 𝔄') n m x ζm
      ζi d g tid l :
    pctx_own K1 n m x ((nest_path K1 K2, ζi) :: ζm) [] d g tid l = pctx_own K1 n m x ζm [] d g tid l.
  Proof. by rewrite nest_path_below pctx_own_blk_cons_below. Qed.

  (** Reborrow the leaf at the hole of [K2] of the nested place at the hole of [K1], at
      [κ ⊓ α] (included in [κ ⊑ κ']). The program computes the address of the hole:
      it loads the address of the referent of the inner borrow. Both borrows are
      opened ([cpd_acc]); the token of the fresh prophecy variable [ζ] of the reborrow
      extends the reservation of the outer borrow, is handed to the closer of the inner
      borrow, which extends the inner reservation, and is finally put back into the loan
      of [ζ], borrowed at [κ ⊓ α]. *)
  Lemma type_reborrow_place_nested_instr {𝔅 𝔄' 𝔄} E L I p κ κ' α
      (K1: pctx (uniq_borₛ 𝔄') 𝔄) (K2: pctx 𝔅 𝔄') (ty: type 𝔅) :
    lctx_lft_alive E L κ → pctx_noderef K1 → pctx_nonempty K2 → pctx_noderef K2 →
    typed_instr E L I +[p ◁ₗ{κ} pctx_plug K1 (UniqLty (pctx_plug K2 (OfTy ty)) κ')]
      (Seq (Seq Skip Skip) (!(p +ₗ #(pctx_off K1)) +ₗ #(pctx_off K2)))%E
      (λ w, +[w ◁ &uniq{κ ⊓ α} ty;
              p ◁ₗ{κ} pctx_plug K1 (UniqLty (pctx_plug K2 (Blocked ty (κ ⊓ α))) κ')])
      (λ post '-[x], λ mask π, ∀ m1: ~~ (uniq_borₛ 𝔅),
        uniq_bor_loc m1 = nest_loc K1 K2 (ty_size ty) (uniq_bor_current (place_bor x)) →
        uniq_bor_current m1 = nest_get K1 K2 (uniq_bor_current (place_bor x)) →
        post -[m1; (place_bor x, (nest_path K1 K2, uniq_bor_ξi m1) :: place_ζis x)] mask π).
  Proof.
    intros Alv HK1 HK2 HK2d tid post mask iκs [x []].
    iIntros "#LFT #TIME #PROPH #UNIQ #E L I [T _] Obs".
    destruct x as [[[[[[l x₀] ξi] d'] g'] idx] ζm].
    rewrite /tctx_elt_interp.
    iDestruct "T" as (v Hp) "(%d0 & #⧖0 & ⧗p & -> & %Hle & #Incl & #PtBase & Own)".
    have ?: Closed [] p by eapply eval_path_closed.
    (* Two steps, for credits and cumulative time receipts. *)
    wp_bind (Seq Skip Skip). wp_bind Skip. iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME ⧖0"); [set_solver|].
    iIntros "£ #⧖S". wp_let. iModIntro. wp_let. iApply wp_fupd.
    iApply (wp_cumulative_time_receipt_linear with "TIME ⧖S"); [set_solver|].
    iIntros "⧗". wp_let. iModIntro. wp_let.
    iDestruct (cumulative_time_receipt_mono (1 + (1 + 1)) with "⧗") as "⧗"; [lia|].
    iDestruct (cumulative_time_receipt_sep with "⧗") as "[⧗u ⧗]".
    set β := κ ⊓ α. set lt2 := pctx_plug K2 (OfTy ty).
    iDestruct (Alv with "L E") as "#Alv".
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iDestruct (guards_transitive with "Ghalf Alv") as "#Hκ".
    iAssert (κ ⊑ κ')%I as "#Hκκ'".
    { iApply (llftl_incl_trans with "Incl"). iApply lty_lft_plug_nest_l. }
    iAssert (β ⊑ κ')%I as "#Hβκ'".
    { iApply llftl_incl_trans; [iApply llftl_intersect_incl_l|done]. }
    iDestruct (lc_weaken (1 + 1 + 1 + 3 * (d0 + 1)) with "£") as "[[[£a £b] £c] £r]";
      [rewrite /advance_credits; nia|].
    (* Open the outer borrow. *)
    rewrite /ltype_own ltype_own_cp_uniq_plug_nest.
    iMod (cpd_acc with "LFT PROPH UNIQ Hκ H1 Own") as (κp) "(#Inclp & #Ok & Upd & Close)";
      [solve_ndisj|].
    iMod (lc_fupd_elim_later with "£a Upd") as "Upd".
    iMod (guarded_upd_run with "[] H2 Upd") as "(H2 & #⧖' & N)"; [solve_ndisj| |].
    { iApply (guards_transitive with "Hκ Incl"). }
    rewrite lty_pat_plug lty_rfn_plug ltype_own_plug pctx_mode_noderef // pctx_depth_noderef //.
    iDestruct "N" as "[N1 Rest1]".
    rewrite /nest_get /nest_loc /nest_path.
    destruct (pctx_get K1 x₀) as [[[[[l' y] ξi'] d1] g1] idx'] eqn:Hm.
    iDestruct "N1" as "(Pt' & ⧗n & #TIMEn & #Incl' & #Gpt' & %d1' & %g1' & %Hle1 & C)".
    set lK1 := pctx_loc K1 (lty_size (UniqLty lt2 κ')) x₀ l.
    (* Load the address of the referent of the inner borrow. *)
    iApply wp_fupd. wp_bind (!(p +ₗ #(pctx_off K1)))%E. wp_bind (p +ₗ #(pctx_off K1))%E.
    iApply wp_wand; [iApply (wp_eval_path _ _ #(l.1 +ₗ pctx_off K1)); by rewrite /= Hp|].
    iIntros (?) "->".
    have HlK1: l.1 +ₗ pctx_off K1 = lK1.1 by rewrite /lK1 pctx_loc_fst.
    rewrite HlK1.
    iApply (wp_read_na_guarded_cells_singleton _ lK1.1 lK1.2
      (fractional.half γh ∗ lK1 #↦!∗ [FVal (LitV l'.1)]) #(l'.1) (d0 + 1)
      with "[H2 Pt' £r]"); [solve_ndisj| |].
    { iFrame "H2 Pt' £r". iApply guard_cloc_combine.
      - iApply guards_weaken_lhs_sep_l. iApply (pctx_loc_guard with "[]").
        iApply (guards_transitive_right with "Hκ PtBase").
      - iApply (lguards_weaken_later _ _ _ 0); [lia|iApply guards_weaken_sep_r]. }
    iIntros "!> [H2 Pt']". wp_op.
    (* Open the inner borrow. *)
    iMod (fractional.frac_split_guard_in_half NllftG (fractional.half γh) (fractional.half γh)
      with "H2 []") as (γ3) "[H3 [H4 [#Gh3 #Back3]]]"; [solve_ndisj|iApply guards_refl|].
    iAssert (fractional.half γ3 &&{↑NllftG}&&> @[κ'])%I as "#H3κ'".
    { iApply (guards_transitive with "Gh3"). iApply (guards_transitive with "Hκ Hκκ'"). }
    iAssert (fractional.half γ3 &&{↑NllftG}&&> @[ty_lft (lty_fold lt2)])%I as "#H3ty".
    { iApply (guards_transitive with "Gh3"). iApply (guards_transitive with "Hκ").
      iApply (llftl_incl_trans with "Incl"). iApply lty_lft_plug_nest_r. }
    iAssert (fractional.half γ3 &&{↑NllftG}&&> @[ty_lft ty])%I as "#H3ty'".
    { iApply (guards_transitive with "H3ty"). iApply (lty_lft_plug K2 (OfTy ty)). }
    iAssert (cpd_own κ' ξi' (lty_fold lt2) (lty_pat lt2) (ltype_own_cp false lt2 (Owned 0))
      (lty_rfn lt2 y ζm (false :: pctx_path K1 [])) d1' g1' tid l') with "[C]" as "C".
    { rewrite /lt2 -(ltype_own_cp_uniq_plug K2) //. }
    iMod (cpd_acc with "LFT PROPH UNIQ H3κ' H3 C") as (κp') "(#Inclp' & #Ok' & Upd' & Close')";
      [solve_ndisj|].
    iMod (lc_fupd_elim_later with "£b Upd'") as "Upd'".
    iMod (guarded_upd_run with "H3ty H4 Upd'") as "(H4 & #⧖'' & N2)"; [solve_ndisj|].
    set q2 := false :: pctx_path K1 [].
    rewrite /lt2 lty_pat_plug lty_rfn_plug ltype_own_plug pctx_mode_noderef //
      pctx_depth_noderef //.
    iDestruct "N2" as "[L1 Rest2]". iSimpl in "L1".
    iDestruct "L1" as (? ->) "[Pt1 Gho1]".
    set yK := pctx_get K2 y. set lK := pctx_loc K2 (ty_size ty) y l'.
    iMod (ghost_var_alloc (lstate_triv yK)) as (γζ) "[Ghζ Ghζ']".
    iMod (proph_loan_intro (uniq_cell_tyi yK) ⊤ (uniq_cell yK d1' g1' γζ) with "PROPH UNIQ")
      as (ζi) "Loan"; [solve_ndisj|].
    set ζ := uniq_prvar yK ζi.
    rewrite proph_loan_unfold. iDestruct "Loan" as "[ζVo ζPc]".
    iDestruct (uniq_proph_tok with "ζVo ζPc") as "(ζVo & ζtok & ToζPc)".
    set r_in := pctx_rfn K2 y ζm q2 (inl (PlaceGhost yK ζi)).
    (* Close the outer borrow; its closer closes the inner one. *)
    iMod ("Close" $! (pctx_pat K1 (PatUniq (pctx_pat K2 (PatBlocked β))))
      (pctx_rfn K1 x₀ ζm [] (inr (l', r_in, ξi'))) d' g' [ζ] 1%Qp
      (fractional.half γ3 ∗ ∃ idx1, proph_bor_tok ζ (uniq_cell yK d1' g1' γζ) idx1 ∗
        proph_idx_bor_gen β ζ idx1 (uniq_gbody β ty tid lK))%I
      with "[] [ζtok] [ζVo ToζPc Ghζ' Pt1 Gho1 Rest2 Close' £c Pt' ⧗n Rest1]")
      as "(Own & H1 & H3 & Bor1)".
    { iPureIntro. intros ζl. apply pctx_rfn_rsv_mono; [set_solver|]. intros Hr.
      apply (prfn_rsv_uniq _ _ _ y) in Hr as [Hr Hξ].
      apply (prfn_rsv_uniq _ _ _ y). split.
      - eapply pctx_rfn_rsv; [|exact Hr|]; [set_solver|].
        rewrite prfn_rsv_inl. apply place_ghost_rsv_elem. set_solver.
      - eapply proph_dep_weaken; [|exact Hξ]. set_solver. }
    { by rewrite big_sepL_singleton. }
    { iIntros "ζtok".
      iMod ("Close'" $! (pctx_pat K2 (PatBlocked β)) r_in d1' g1' [ζ] 1%Qp
        (∃ idx1, proph_bor_tok ζ (uniq_cell yK d1' g1' γζ) idx1 ∗
          proph_idx_bor_gen β ζ idx1 (uniq_gbody β ty tid lK))%I
        with "[] ζtok [ζVo ToζPc Ghζ' Pt1 Gho1 Rest2 £c]") as "(Own2 & H3 & Bor1)".
      { iPureIntro. intros ζl Hr. eapply pctx_rfn_rsv; [|exact Hr|]; [set_solver|].
        rewrite prfn_rsv_inl. apply place_ghost_rsv_elem. set_solver. }
      { iIntros "ζtok". rewrite big_sepL_singleton.
        iDestruct ("ToζPc" with "ζtok") as "ζPc".
        iMod (proph_loan_borrow_gen_pc ⊤ β ζ (uniq_cell yK d1' g1' γζ)
          (vπ (uniq_cell yK d1' g1' γζ)) (uniq_gbody β ty tid lK)
          with "LFT UNIQ [ζVo ζPc] [Ghζ' Pt1 Gho1]") as (idx1) "(Tok1 & #Bor1 & Back1)";
          [solve_ndisj| by rewrite proph_loan_unfold; iFrame| |].
        { iApply (uniq_gbody_triv_close with "Ghζ'"); [done|].
          iApply uniq_payload_intro_later. iNext. iFrame "⧖'' Gho1 Pt1". }
        iModIntro. iSplitR; [|iSplitR "Tok1"; [|iExists idx1; by iFrame "Tok1 Bor1"]].
        { iNext. iApply (pat_ok_plug with "Ok'"). iApply pat_ok_blocked.
          iApply (llftl_incl_trans with "Hβκ' Inclp'"). }
        iNext. iApply guarded_upd_intro. iModIntro. iFrame "⧖''".
        rewrite ltype_own_plug pctx_mode_noderef // pctx_depth_noderef //. iFrame "Rest2".
        rewrite /= /leaf_owned /blocked_owned. iIntros "#†α".
        iMod (fupd_mask_mono with "(Back1 †α)") as "Lender"; [rewrite /lazyE; solve_ndisj|].
        iMod (lc_fupd_elim_later with "£c Lender") as "Lender". iModIntro.
        iApply (guarded_upd_mono with "[] [Lender]");
          [|iApply (uniq_lender_settle with "LFT PROPH †α Lender")].
        iIntros "(%x & %d2 & %g2 & Eqz & ⧖2 & Gho & Pt) !>". iExists x, d2, g2.
        rewrite /ofty_owned /=. by iFrame. }
      iModIntro. iFrame "H3 Bor1". iSplitR.
      { iNext. iApply (pat_ok_plug with "Ok"). rewrite pat_ok_uniq_iff.
        iApply (pat_ok_plug with "[]").
        { rewrite -pat_ok_uniq_iff. iApply (pat_ok_plug_hole with "Ok"). }
        iApply pat_ok_blocked. iApply (llftl_incl_trans with "[] Inclp").
        iApply llftl_intersect_incl_l. }
      iNext. iApply guarded_upd_intro. iModIntro. iFrame "⧖'".
      rewrite ltype_own_plug pctx_mode_noderef // pctx_depth_noderef //. iFrame "Rest1".
      rewrite /= /uniq_node. iFrame "Pt' ⧗n TIMEn Incl' Gpt'". iExists d1', g1'.
      iSplit; [done|]. by rewrite /= (ltype_own_cp_uniq_plug K2). }
    iMod (fupd_mask_mono with "(Back3 H3 H4)") as "H2"; [solve_ndisj|].
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "$"; [solve_ndisj|].
    iDestruct "Bor1" as (idx1) "[Tok1 #Bor1]".
    iModIntro.
    iExists -[(lK, yK, ζi, d1', g1', idx1); ((l, x₀, ξi, d', g', idx), (nest_path K1 K2, ζi) :: ζm)].
    iFrame "I". iSplit; last first.
    { iApply (proph_obs_impl with "Obs")=> π Hπ. apply Hπ; rewrite /nest_loc /nest_get ?Hm //. }
    iSplitL "Tok1 Ghζ ⧗u".
    { iExists #(lK.1), d0. iSplit; [by rewrite /lK pctx_loc_fst|]. iFrame "⧖0".
      iSplit; [|done]. iSplit.
      { iApply llftl_incl_trans; [iApply llftl_intersect_incl_l|].
        iApply (llftl_incl_trans with "Incl"). iApply llftl_incl_trans;
          [iApply lty_lft_plug_nest_r|iApply (lty_lft_plug K2 (OfTy ty))]. }
      iSplit; [iPureIntro; lia|]. iSplitL.
      { iExists β, γζ. iFrame "∗#". iApply guards_refl. }
      iApply (guards_transitive_right with "Hβκ' [Gpt']").
      iApply (lguards_weaken_later _ _ _ (g' + 1)); [lia|]. by iApply pctx_loc_guard. }
    iSplit; [|done].
    rewrite /tctx_elt_interp. iExists #(l.1). iSplit; [done|]. iExists d0.
    iFrame "⧖0 PtBase". iSplitL "⧗p ⧗".
    { iApply (cumulative_time_receipt_mono _ (2 * lty_nblk (pctx_plug K1
        (UniqLty (pctx_plug K2 (OfTy ty)) κ')) + (1 + 1)) with "[⧗p ⧗]");
        [rewrite !lty_nblk_plug /= !lty_nblk_plug /=; lia|].
      rewrite !cumulative_time_receipt_sep. iFrame. }
    iSplit; [done|]. iSplit; [done|].
    iSplit.
    { rewrite (lty_fold_plug_eq K1 (UniqLty (pctx_plug K2 (Blocked ty β)) κ')
        (UniqLty (pctx_plug K2 (OfTy ty)) κ')) //. by rewrite /= !lty_core_plug. }
    rewrite /ltype_own (ltype_own_cp_plug_core false K1
      (UniqLty (pctx_plug K2 (Blocked ty β)) κ') (UniqLty (pctx_plug K2 (OfTy ty)) κ'));
      [|by rewrite /= !lty_core_plug].
    rewrite ltype_own_cp_uniq_plug_nest lty_pat_plug lty_rfn_plug_nest /=.
    rewrite (lty_pat_plug K2) /= /nest_get /nest_path Hm /=.
    rewrite -/(nest_path K1 K2) pctx_rfn_blk_cons_nest. rewrite /nest_path.
    rewrite /lty_rfn decide_True //.
  Qed.

  (** * Unblocking a leaf of a nested place *)

  (** Once [κ ⊓ α] has ended, the leaf at the hole of [K2] of the nested place at the
      hole of [K1] is unblocked, as in [unblock_tctx_place]: both borrows are opened, the
      inheritance of the reborrow is fired, and both borrows are closed at the unblocked
      state. The outer node needs a receipt of one more than the (new) depth of the inner
      contents; it comes from the second cumulative time receipt of the blocked leaf, which
      also pays for the credits of the observation of the final value. *)
  Lemma unblock_tctx_place_nested {𝔅 𝔄' 𝔄 𝔄l 𝔄l'} p κ κ' α
      (K1: pctx (uniq_borₛ 𝔄') 𝔄) (K2: pctx 𝔅 𝔄') (ty: type 𝔅)
      (T: tctx 𝔄l) (T': tctx 𝔄l') E L f :
    lctx_lft_alive E L κ → pctx_noderef K1 → pctx_nonempty K2 → pctx_noderef K2 →
    unblock_tctx E L α T T' f →
    unblock_tctx E L α
      (p ◁ₗ{κ} pctx_plug K1 (UniqLty (pctx_plug K2 (Blocked ty (κ ⊓ α))) κ') +:: T)
      (p ◁ₗ{κ} pctx_plug K1 (UniqLty (pctx_plug K2 (OfTy ty)) κ') +:: T')
      (λ π '(x -:: xl), λ '(x' -:: xl'),
        uniq_bor_loc (place_bor x') = uniq_bor_loc (place_bor x) ∧
        uniq_bor_future (place_bor x') π = uniq_bor_future (place_bor x) π ∧
        uniq_bor_current (place_bor x') = nest_set K1 K2 (uniq_bor_current (place_bor x))
          (nest_get K1 K2 (uniq_bor_current (place_bor x'))) ∧
        place_ζis x' = place_ζis x ∧
        vπ (nest_get K1 K2 (uniq_bor_current (place_bor x'))) π = place_nest_blk_fin K1 K2 x π ∧
        f π xl xl').
  Proof.
    iIntros (Alv HK1 HK2 HK2d Un G tid [x xl] ?)
      "#LFT #TIME #PROPH #UNIQ #E #L G #†α /=[(%v & %Hp & Own) T]".
    destruct x as [[[[[[l x₀] ξi] d'] g'] idx] ζm].
    set β := κ ⊓ α.
    have Hcore: lty_core (UniqLty (pctx_plug K2 (Blocked ty β)) κ') =
      lty_core (UniqLty (pctx_plug K2 (OfTy ty)) κ') by rewrite /= !lty_core_plug.
    iDestruct "Own" as (d0) "(#⧖0 & ⧗ & -> & %Hle & #Incl & #PtBase & Own)".
    iDestruct (cumulative_time_receipt_mono (2 * lty_nblk (pctx_plug K1
      (UniqLty (pctx_plug K2 (OfTy ty)) κ')) + (1 + 1)) with "⧗") as "⧗";
      [rewrite !lty_nblk_plug /= !lty_nblk_plug /=; lia|].
    iDestruct (cumulative_time_receipt_sep with "⧗") as "[⧗r ⧗]".
    iDestruct (cumulative_time_receipt_sep 1 1 with "⧗") as "[⧗a ⧗b]".
    rewrite (lty_fold_plug_eq K1 _ _ Hcore).
    leaf_open "L" with "G" as "[L1 back]"; [set_solver|].
    iDestruct (Alv with "L1 E") as "#Lκ". iMod ("back" with "L1") as "G".
    (* Half of [G] for the rest of the context, the other half for the place. *)
    iMod (fractional.frac_split_guard_in_half with "G L") as (γ1) "[GT [GP [#GhT #BackT]]]";
      [solve_ndisj|].
    iMod (Un with "LFT TIME PROPH UNIQ E GhT GT †α T") as (dT xl') "[#⧖T ToT']".
    iDestruct (guards_transitive with "GhT Lκ") as "#GPκ".
    iMod (fractional.frac_split_guard_in_half with "GP GPκ") as (γ2) "[H1 [H2 [#Gh2 #Back2]]]";
      [solve_ndisj|].
    iAssert (κ ⊑ κ')%I as "#Hκκ'".
    { iApply (llftl_incl_trans with "Incl"). iApply lty_lft_plug_nest_l. }
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗a ⧖0") as "[_ £]";
      [solve_ndisj|].
    iDestruct (lc_weaken (1 + 1) with "£") as "[£a £b]"; [rewrite /advance_credits; lia|].
    (* Open the outer borrow. *)
    rewrite /ltype_own (ltype_own_cp_plug_core false K1 _ _ Hcore).
    rewrite ltype_own_cp_uniq_plug_nest.
    iMod (cpd_acc with "LFT PROPH UNIQ Gh2 H1 Own") as (κp) "(#Inclp & #Ok & Upd & Close)";
      [solve_ndisj|].
    iMod (lc_fupd_elim_later with "£a Upd") as "Upd".
    iMod (guarded_upd_run with "[] H2 Upd") as "(H2 & #⧖' & N)"; [solve_ndisj| |].
    { iApply (guards_transitive with "Gh2 Incl"). }
    rewrite lty_pat_plug lty_rfn_plug ltype_own_plug pctx_mode_noderef // pctx_depth_noderef //.
    iDestruct "N" as "[N1 Rest1]".
    iDestruct (pctx_own_in with "Rest1") as %Hin1.
    destruct (pctx_get K1 x₀) as [[[[[l' y] ξi'] d1] g1] idx'] eqn:Hm.
    iDestruct "N1" as "(Pt' & ⧗n & #TIMEn & #Incl' & #Gpt' & %d1' & %g1' & %Hle1 & C)".
    (* Open the inner borrow. *)
    iMod (fractional.frac_split_guard_in_half NllftG (fractional.half γ2) (fractional.half γ2)
      with "H2 []") as (γ3) "[H3 [H4 [#Gh3 #Back3]]]"; [solve_ndisj|iApply guards_refl|].
    iAssert (fractional.half γ3 &&{↑NllftG}&&> @[κ'])%I as "#H3κ'".
    { iApply (guards_transitive with "Gh3"). iApply (guards_transitive with "Gh2 Hκκ'"). }
    iAssert (fractional.half γ3 &&{↑NllftG}&&>
      @[ty_lft (lty_fold (pctx_plug K2 (OfTy ty)))])%I as "#H3ty".
    { iApply (guards_transitive with "Gh3"). iApply (guards_transitive with "Gh2").
      iApply (llftl_incl_trans with "Incl"). iApply lty_lft_plug_nest_r. }
    iAssert (fractional.half γ3 &&{↑NllftG}&&> @[ty_lft ty])%I as "#H3ty'".
    { iApply (guards_transitive with "H3ty"). iApply (lty_lft_plug K2 (OfTy ty)). }
    iAssert (cpd_own κ' ξi' (lty_fold (pctx_plug K2 (OfTy ty))) (lty_pat (pctx_plug K2 (Blocked ty β)))
      (ltype_own_cp false (pctx_plug K2 (OfTy ty)) (Owned 0))
      (lty_rfn (pctx_plug K2 (Blocked ty β)) y ζm (false :: pctx_path K1 [])) d1' g1' tid l')
      with "[C]" as "C".
    { rewrite -(ltype_own_cp_uniq_plug K2) //. }
    iMod (cpd_acc with "LFT PROPH UNIQ H3κ' H3 C") as (κp') "(#Inclp' & #Ok' & Upd' & Close')";
      [solve_ndisj|].
    iMod (lc_fupd_elim_later with "£b Upd'") as "Upd'".
    iMod (guarded_upd_run with "H3ty H4 Upd'") as "(H4 & #⧖'' & N2)"; [solve_ndisj|].
    set q2 := false :: pctx_path K1 [].
    rewrite lty_pat_plug lty_rfn_plug ltype_own_plug pctx_mode_noderef //
      pctx_depth_noderef //.
    iDestruct "N2" as "[L1 Rest2]". iSimpl in "L1".
    iDestruct (pctx_own_in with "Rest2") as %Hin2.
    set yK := pctx_get K2 y. set ζi := blk_lookup ζm (pctx_path K2 q2).
    (* Unblock the leaf: fire the inheritance of the reborrow and settle it. *)
    iAssert ([†β])%I as "#†β". { rewrite llftl_end_inter. by iRight. }
    iMod (fupd_mask_mono with "(L1 †β)") as "Upd1"; [rewrite /lazyE; solve_ndisj|].
    iMod (guarded_upd_run with "H3ty' H4 Upd1") as "(H4 & %y1 & %d2 & %g2 & Eqz & #⧖2 & O1)";
      [rewrite /lazyE; solve_ndisj|].
    iDestruct "O1" as "[Pt1 Gho1]".
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗b ⧖2") as "[#⧖2' £]";
      [solve_ndisj|].
    iDestruct (lc_weaken (1 + (d2 + d2*(g2+2) + (0 + (d2+1)*(g2+1)) + 1 + 1)) with "£")
      as "[£e £]"; [rewrite /advance_credits; nia|].
    iSimpl in "Eqz". iMod (lc_fupd_elim_later with "£e Eqz") as "Eqz".
    iMod (proph_eqz_obs_by_share ty with "LFT H3ty' H4 £ Eqz Gho1") as "(#Obs1 & H4 & Gho1)".
    (* Close the inner borrow at the unblocked state. *)
    set d2'' := d2 `max` d1'. set g2'' := g2 `max` g1'.
    iDestruct (ty_gho_own_depth_mono _ d2 g2 d2'' g2'' with "Gho1") as "[Gho1 _]"; [lia..|].
    iDestruct (pctx_own_depth_mono _ _ _ _ _ _ _ _ d2'' g2'' with "Rest2") as "Rest2"; [lia..|].
    iAssert (⧖(S d2'' `max` g2''))%I as "#⧖i".
    { iCombine "⧖'' ⧖2" as "⧖". iApply (persistent_time_receipt_mono with "⧖"). lia. }
    iMod ("Close'" $! (pctx_pat K2 PatLeaf) (pctx_rfn K2 y ζm q2 (inl (PlaceIn y1)))
      d2'' g2'' [] 1%Qp True%I with "[] [] [Pt1 Gho1 Rest2]") as "(Own2 & H3 & _)".
    { iPureIntro. intros ζl Hr. eapply pctx_rfn_rsv; [|exact Hr|apply prfn_rsv_in].
      set_solver. }
    { done. }
    { iIntros "_". iModIntro. iSplitR.
      { iNext. iApply (pat_ok_plug with "Ok'"). iApply pat_ok_leaf. }
      iSplitL; [|done].
      iNext. iApply guarded_upd_intro. iModIntro. iFrame "⧖i".
      rewrite ltype_own_plug pctx_mode_noderef // pctx_depth_noderef //. iFrame "Rest2".
      iExists y1. by iFrame. }
    (* Close the outer borrow at the unblocked state. *)
    set d'' := S d2'' `max` d'. set g'' := g2'' `max` g'.
    iDestruct (pctx_own_depth_mono _ _ _ _ _ _ _ _ d'' g'' with "Rest1") as "Rest1"; [lia..|].
    iAssert (⧖(S d'' `max` g''))%I as "#⧖o".
    { iCombine "⧖' ⧖2'" as "⧖". iApply (persistent_time_receipt_mono with "⧖"). lia. }
    iMod ("Close" $! (pctx_pat K1 (PatUniq (pctx_pat K2 PatLeaf)))
      (pctx_rfn K1 x₀ ζm [] (inr (l', pctx_rfn K2 y ζm q2 (inl (PlaceIn y1)), ξi')))
      d'' g'' [] 1%Qp True%I with "[] [] [Pt' ⧗n Rest1 Own2]") as "(Own & H1 & _)".
    { iPureIntro. intros ζl. apply pctx_rfn_rsv_mono; [set_solver|]. intros Hr.
      apply (prfn_rsv_uniq _ _ _ y) in Hr as [Hr Hξ].
      apply (prfn_rsv_uniq _ _ _ y). split.
      - change (prfn_rsv (lty_rfn (pctx_plug K2 (Blocked ty β)) y ζm q2) ζl) in Hr.
        rewrite lty_rfn_plug in Hr. eapply pctx_rfn_rsv; [|exact Hr|apply prfn_rsv_in]. set_solver.
      - eapply proph_dep_weaken; [|exact Hξ]. set_solver. }
    { done. }
    { iIntros "_". iModIntro. iSplitR.
      { iNext. iApply (pat_ok_plug with "Ok"). rewrite pat_ok_uniq_iff.
        iApply (pat_ok_plug _ K2 (PatBlocked β) with "[]"); [|iApply pat_ok_leaf].
        iDestruct (pat_ok_plug_hole with "Ok") as "Ok1".
        iEval (rewrite /= ?lty_pat_plug ?pat_ok_uniq_iff) in "Ok1". done. }
      iSplitL; [|done].
      iNext. iApply guarded_upd_intro. iModIntro. iFrame "⧖o".
      rewrite ltype_own_plug pctx_mode_noderef // pctx_depth_noderef //. iFrame "Rest1".
      rewrite /= /uniq_node. iFrame "Pt' ⧗n TIMEn Incl'".
      iSplitR. { iApply (lguards_weaken_later with "Gpt'"). lia. }
      iExists d2'', g2''. iSplit; [iPureIntro; lia|]. by rewrite /= (ltype_own_cp_uniq_plug K2). }
    iMod (fupd_mask_mono with "(Back3 H3 H4)") as "H2"; [solve_ndisj|].
    iMod (fupd_mask_mono with "(Back2 H1 H2)") as "GP"; [solve_ndisj|].
    iCombine "⧖0 ⧖o" as "⧖D".
    iModIntro. iExists dT,
      (((l, nest_set K1 K2 x₀ y1, ξi, d'', g'', idx), ζm) -:: xl').
    iSplitR; [done|].
    iMod "ToT'". iModIntro. iNext. iMod "ToT'". iModIntro.
    iApply (step_fupdN_wand with "ToT'"). iIntros ">(GT & T' & #Obs')".
    iMod (fupd_mask_mono with "(BackT GT GP)") as "$"; [solve_ndisj|].
    have Hget: nest_get K1 K2 (nest_set K1 K2 x₀ y1) = y1.
    { by rewrite /nest_get /nest_set pctx_get_set Hm /= pctx_get_set. }
    iModIntro. iSplitR "Obs'".
    { iFrame "T'". rewrite /tctx_elt_interp. iExists #(l.1). iSplit; [done|].
      iExists (d0 `max` (S d'' `max` g'')). iFrame "⧖D ⧗r Incl".
      iSplit; [done|]. iSplit; [iPureIntro; lia|].
      iSplitR. { iApply (lguards_weaken_later with "PtBase"). lia. }
      rewrite /ltype_own ltype_own_cp_uniq_plug_nest lty_pat_plug lty_rfn_plug_nest /=.
      rewrite /nest_set pctx_get_set pctx_rfn_set // Hm /= pctx_rfn_set //.
      rewrite /nest_get pctx_get_set /= pctx_get_set (lty_pat_plug K2) -/q2.
      rewrite (lty_pat_plug K2 (OfTy ty)). iExact "Own". }
    iCombine "Obs1 Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=> π [Heq Hf].
    split; [done|]. split.
    { rewrite !uniq_bor_future_eq. apply (uniq_prvar_app_irrel _ x₀). }
    split; [by rewrite /= Hget|]. split; [done|]. split; [|done].
    rewrite /place_nest_blk_fin /= Hget /nest_get Hm /=. symmetry. exact Heq.
  Qed.
End typing.
