(** * Owned places below unique borrows

  The operations on places rooted at an owned location ([p ◁ₗown{n} …], [place_own.v]) at
  a hole below any number of unique borrows ([PUniq] steps of the context, interleaved
  with fields, owned pointers and sums), through the access of [pctx_acc.v]: the enclosing
  borrows are opened (with the credits of a program step, bounded by the depth of the
  place) and closed again with the new hole, extending their reservations by the new
  prophecy variables of the hole. The hole is in [Owned] mode ([pctx_uend K = None]) or, if
  it is the whole referent of the innermost borrow ([pctx_uend K = Some κ], e.g. [**x] for
  [x: &mut &mut i32]), in [Uniq κ] mode.

  - [type_change_oplace_instr]: change the place type at the hole by a conversion
    ([vplace_conv]) at the mode of the hole. Instances: unfolding and folding a unique
    borrow ([OfTy (&uniq{κ'} ty)] ↔ [UniqLty (OfTy ty) κ']) and a pair (both modes), and an
    owned pointer ([Owned] mode).
  - [type_borrow_place_instr] (the unified mutable borrow, instruction [&ᵘ e]; by the mode
    of the hole, [type_borrow_vplace_owned] and [type_borrow_vplace_uniq]): mutable borrow of
    the hole at [pctx_blft K α], the intersection of all enclosing borrow lifetimes and [α];
    [unblock_tctx_oplace_deep], [unblock_tctx_oplace_uniq]: unblocking.
  - (Reads and writes are [type_read_place_instr] of [place_read.v] and
    [type_write_place_instr] of [place_write.v].)
  - [lty_rslv], [resolve_tctx_cons_oplace_deep], [type_drop_oplace_deep_instr]: resolving
    (in a context) and dropping an owned place with nested unique borrows whose leaves are
    blocked ([lty_rslv_uniq_blk]); resolving to a readable state is
    [type_resolve_place_instr] of [place_res_rslv.v].
  - [unblock_tctx_oplace_shr_deep]: unblocking a shared-blocked hole (the shared borrow is
    [type_share_place_instr] of [place_share.v]).

  See [design_docs/verus-belt-phase3-design.md], section "PUniq", and the examples [examples/get_first.v] and [examples/place_deep.v]. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From lrust.lang Require Import proofmode.
From lrust.typing Require Export type ltype lpath pctx_acc vplace place_own.
From lrust.lang.lib Require Import new_delete.
From lrust.typing Require Import type_context programs lft_contexts uniq_util uniq_bor own shr_bor bytes_layout value_ctx product freeable_util place_shr place_resolve.
From lrust.util Require Import proph_bor.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section puniq.
  Context `{!typeG Σ}.

  Lemma pctx_uend_ulfts {𝔅 𝔄} (K: pctx 𝔅 𝔄) κ : pctx_uend K = Some κ → κ ∈ pctx_ulfts K.
  Proof.
    induction K; simpl; try done.
    destruct K; [intros [= ->]; set_solver|..]; intros; apply elem_of_cons; right; by apply IHK.
  Qed.

  Lemma pctx_hmode_le {𝔅 𝔄} (K: pctx 𝔅 𝔄) m : pctx_hmode K m ≤ m + pctx_dlev K.
  Proof.
    induction K in m |- *; simpl; [lia|apply IHK|apply IHK| |apply IHK| | |];
      [specialize (IHK (m + 1))|specialize (IHK 0)|specialize (IHK (m + 1))|
       specialize (IHK (m + 1))]; lia.
  Qed.

  Lemma typed_instr_tr_impl {𝔄l 𝔅l} E L I (T: tctx 𝔄l) e (T': val → tctx 𝔅l) tr tr' :
    (∀ post xl mask π, tr' post xl mask π → tr post xl mask π) →
    typed_instr E L I T e T' tr → typed_instr E L I T e T' tr'.
  Proof.
    iIntros (Himp Hty tid post mask iκs xl) "LFT TIME PROPH UNIQ E L I T Obs".
    iApply (Hty with "LFT TIME PROPH UNIQ E L I T"). iApply (proph_obs_impl with "Obs").
    intros π. apply Himp.
  Qed.

  Lemma unblock_tctx_impl {𝔄l 𝔄l'} E L κ (T: tctx 𝔄l) (T': tctx 𝔄l') f f' :
    (∀ π xl xl', f π xl xl' → f' π xl xl') → unblock_tctx E L κ T T' f → unblock_tctx E L κ T T' f'.
  Proof.
    iIntros (Himp Un G tid xl ?) "LFT TIME PROPH UNIQ E L G †κ T".
    iMod (Un with "LFT TIME PROPH UNIQ E L G †κ T") as (d xl') "[⧖ Upd]".
    iModIntro. iExists d, xl'. iFrame "⧖".
    iApply (step_fupd_wand with "Upd"). iIntros "Upd".
    iApply (step_fupdN_wand with "Upd"). iIntros ">($ & $ & Obs)". iModIntro.
    iApply (proph_obs_impl with "Obs"). intros π. apply Himp.
  Qed.

  Lemma big_sepL_pat_ok_nil (κs: list lft) p :
    pat_blk_lfts p = [] → ⊢ [∗ list] κ ∈ κs, pat_ok κ p.
  Proof. iIntros (Hp). iApply big_sepL_intro. iIntros "!>" (???). by rewrite /pat_ok Hp. Qed.

  (** * Changing the place type at the hole *)

  (** A conversion of the hole of [K] from [lt] to [lt'] at its mode (in the place of root
      value [x]), with a relation [f] between the old and the new value of the hole. It
      gets a token for the lifetime of the enclosing borrows and of the folded type of the
      hole, later credits and cumulative time receipts; it may depend on new prophecy
      variables [ζl'], whose tokens it hands out (to extend the reservations of the
      enclosing borrows) and gets back. *)
  Definition vplace_conv {𝔅 𝔄} (K: pctx 𝔅 𝔄) (lt lt': lty 𝔅) (f: ~~𝔅 → ~~𝔅 → Prop) : Prop :=
    ∀ (x: ~~𝔄) ζm dh gh D tid lh (G: iProp Σ) E, Timeless G → lazyE ∪ ↑timeN ⊆ E →
      pctx_dlev K ≤ D → dh < D →
    ⊢ llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ time_ctx -∗
      (G &&{↑NllftG}&&> @[pctx_ulft K lt ⊓ ty_lft (lty_fold lt)]) -∗ G -∗
      ⧖D -∗ £(D + 1) -∗ ⧗(D + 2) -∗
      ltype_own_cp false lt (pctx_kind K (Owned 0) x) (lty_pat lt)
        (lty_rfn lt (pctx_get K x) ζm (pctx_vpath K)) dh gh tid lh ={E}=∗
      ∃ y' ζl' (q: Qp), ⌜f (pctx_get K x) y'⌝ ∗
        ⌜∀ ζl, prfn_rsv (lty_rfn lt (pctx_get K x) ζm (pctx_vpath K)) ζl →
          prfn_rsv (lty_rfn lt' y' ζm (pctx_vpath K)) (ζl ++ ζl')⌝ ∗
        q:+[ζl'] ∗ (q:+[ζl'] ={E}=∗
          ltype_own_cp false lt' (pctx_kind K (Owned 0) x) (lty_pat lt')
            (lty_rfn lt' y' ζm (pctx_vpath K)) dh gh tid lh ∗ G).

  Lemma type_change_vplace_instr {𝔅 𝔄} E L I p (K: pctx 𝔅 𝔄) `{!PctxNoShr K} `{!PctxVRoot K}
      (lt lt': lty 𝔅) f :
    lctx_lft_alive E L (pctx_ulft K lt ⊓ ty_lft (lty_fold lt)) →
    lty_fold lt' = lty_fold lt → lty_size lt' = lty_size lt → lty_nrc lt' = lty_nrc lt →
    pat_blk_lfts (lty_pat lt') = [] → lty_simple lt' → vplace_conv K lt lt' f →
    typed_instr E L I +[p ◁ₗ pctx_plug K lt] (Seq Skip Skip)
      (const +[p ◁ₗ pctx_plug K lt'])
      (λ post '-[x], λ mask π, ∀ x', x'.2 = x.2 → pctx_in K x.1 →
        (∃ y', f (pctx_get K x.1) y' ∧ x'.1 = pctx_set K x.1 y') → post -[x'] mask π).
  Proof.
    intros Alv Hf Hsz Hnrc Hp Hs Hconv tid post mask iκs [x []].
    iIntros "#LFT #TIME #PROPH #UNIQ #E L I [T _] Obs".
    destruct x as [x₀ ζm].
    iDestruct "T" as (v Hpv) "T". rewrite vplace_own_open.
    iDestruct "T" as (D) "(#⧖ & ⧗p & Own)". have Hdl: 1 ≤ pctx_dlev K by apply pctx_vroot_dlev.
    (* Two steps, for credits and cumulative time receipts. *)
    wp_bind Skip. iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [set_solver|].
    iIntros "£ #⧖S". wp_let. iModIntro. wp_let. iApply wp_fupd.
    iApply (wp_cumulative_time_receipt_linear with "TIME ⧖S"); [set_solver|].
    iIntros "⧗". wp_let.
    iDestruct (Alv with "L E") as "#Alv".
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_ulft K lt ⊓ ty_lft (lty_fold lt)])%I
      as "#Hα". { iApply (guards_transitive with "Ghalf Alv"). }
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_ulft K lt])%I as "#Hu".
    { iApply (guards_transitive with "Hα"). iApply llftl_intersect_incl_l. }
    iDestruct (lc_weaken (pctx_vacc_cred K D + (D + 1)) with "£") as "[£a £c]";
      [have := pctx_vacc_cred_le K D; rewrite /advance_credits; nia|].
    iMod (vroot_acc K lt with "LFT PROPH UNIQ Hu H1 £a Own")
      as (G' dh gh) "(% & G' & #G'G & -> & %Hdh & H & P & Cl)"; [solve_ndisj|].
    destruct Hdh as (Hdh & Hgh & Hin).
    iDestruct (cumulative_time_receipt_mono (D + 2) with "⧗") as "⧗"; [lia|].
    iMod (Hconv x₀ ζm dh gh D tid _ (fractional.half γh) with "LFT PROPH UNIQ TIME Hα H2 ⧖ £c ⧗ H")
      as (y' ζl' q Hfy Hrsv) "[toks VS]"; [solve_ndisj|lia|lia|].
    iMod ("Cl" $! lt' (lty_rfn lt' y' ζm (pctx_vpath K)) dh gh D ζl' q
      (fractional.half γh) with "[//] [//] [//] [//] [%] [] ⧖ G' P toks VS") as "(Own & H1 & H2)".
    { lia. }
    { iRight. by iApply big_sepL_pat_ok_nil. }
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iModIntro. iExists -[(pctx_set K x₀ y', ζm)]. iFrame "L I". iSplit; last first.
    { iApply (proph_obs_impl with "Obs")=> π Hπ. apply Hπ; [done..|]. by eexists. }
    iSplit; [|done]. iExists _. iSplit; [done|].
    iApply (vplace_own_close with "⧖ [⧗p]"); [by rewrite (lty_vnrc_plug_eq K lt lt' Hnrc)|].
    by rewrite pctx_get_set pctx_vrfn_set.
  Qed.

  (** The own-rooted instance. *)
  Lemma type_change_oplace_instr {𝔅 𝔄} E L I p n (K: pctx 𝔅 𝔄) `{!PctxNoShr K} (lt lt': lty 𝔅) f :
    lctx_lft_alive E L (pctx_ulft K lt ⊓ ty_lft (lty_fold lt)) →
    lty_fold lt' = lty_fold lt → lty_size lt' = lty_size lt → lty_nrc lt' = lty_nrc lt →
    pat_blk_lfts (lty_pat lt') = [] → lty_simple lt' → vplace_conv (POwn n K) lt lt' f →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K lt] (Seq Skip Skip)
      (const +[p ◁ₗown{n} pctx_plug K lt'])
      (λ post '-[x], λ mask π, ∀ x', x'.1.1 = x.1.1 → x'.2 = x.2 → pctx_in K x.1.2 →
        (∃ y', f (pctx_get K x.1.2) y' ∧ x'.1.2 = pctx_set K x.1.2 y') → post -[x'] mask π).
  Proof.
    intros. eapply typed_instr_tr_impl;
      [|by apply (type_change_vplace_instr _ _ _ _ (POwn n K) lt lt' f)].
    intros post [[[l x₀] ζm] []] mask π Hπ [[l' x₀'] ζm'] Hζ Hin (y' & Hf & Hx).
    simpl in *. injection Hx as -> ->. apply Hπ; [done..|]. by eexists.
  Qed.

  (** ** Pairs *)

  Lemma vplace_conv_prod_unfold {𝔅1 𝔅2 𝔄} (K: pctx (𝔅1 * 𝔅2) 𝔄) (ty1: type 𝔅1) (ty2: type 𝔅2) :
    vplace_conv K (OfTy (ty1 * ty2)) (ProdLty (OfTy ty1) (OfTy ty2)) (=).
  Proof.
    iIntros (x ζm dh gh D tid lh G E ? HE ??) "#LFT #PROPH #UNIQ _ #Gk G _ _ _ H".
    destruct (pctx_get K x) as [y1 y2] eqn:Hy.
    iModIntro. iExists (y1, y2), [], 1%Qp. iSplit; [done|]. iSplit.
    { iPureIntro. intros ??. split; apply prfn_rsv_in. }
    iSplitR; [done|]. iIntros "_".
    destruct (pctx_uend K) as [κ|] eqn:Hu.
    - rewrite (pctx_kind_uniq K κ) //.
      iApply (prod_ofty_unfold_uniq with "LFT PROPH UNIQ [] G H"); [trans lazyE; [|set_solver];
        rewrite /lazyE; solve_ndisj|].
      iApply (guards_transitive with "Gk"). iApply llftl_incl_trans; [iApply llftl_intersect_incl_l|].
      iApply pctx_ulft_ulfts. by apply pctx_uend_ulfts.
    - rewrite (pctx_kind_owned K) //. iModIntro. iFrame "G". by iApply prod_ofty_unfold_own.
  Qed.

  Lemma vplace_conv_prod_fold {𝔅1 𝔅2 𝔄} (K: pctx (𝔅1 * 𝔅2) 𝔄) (ty1: type 𝔅1) (ty2: type 𝔅2) :
    vplace_conv K (ProdLty (OfTy ty1) (OfTy ty2)) (OfTy (ty1 * ty2)) (=).
  Proof.
    iIntros (x ζm dh gh D tid lh G E ? HE ??) "#LFT #PROPH #UNIQ _ #Gk G _ _ _ H".
    destruct (pctx_get K x) as [y1 y2] eqn:Hy.
    iModIntro. iExists (y1, y2), [], 1%Qp. iSplit; [done|]. iSplit.
    { iPureIntro. intros ??. apply prfn_rsv_in. }
    iSplitR; [done|]. iIntros "_".
    destruct (pctx_uend K) as [κ|] eqn:Hu.
    - rewrite (pctx_kind_uniq K κ) //.
      iApply (prod_ofty_fold_uniq with "LFT PROPH UNIQ [] G H"); [trans lazyE; [|set_solver];
        rewrite /lazyE; solve_ndisj|].
      iApply (guards_transitive with "Gk"). iApply llftl_incl_trans; [iApply llftl_intersect_incl_l|].
      iApply pctx_ulft_ulfts. by apply pctx_uend_ulfts.
    - rewrite (pctx_kind_owned K) //. iModIntro. iFrame "G". by iApply prod_ofty_unfold_own.
  Qed.

  Lemma type_unfold_vplace_prod_instr {𝔅1 𝔅2 𝔄} E L I p (K: pctx (𝔅1 * 𝔅2) 𝔄) `{!PctxNoShr K} `{!PctxVRoot K}
      (ty1: type 𝔅1) (ty2: type 𝔅2) :
    lctx_lft_alive E L (pctx_ulft K (OfTy (ty1 * ty2)) ⊓ ty_lft (prod_ty ty1 ty2)) →
    typed_instr E L I +[p ◁ₗ pctx_plug K (OfTy (ty1 * ty2))] (Seq Skip Skip)
      (const +[p ◁ₗ pctx_plug K (ProdLty (OfTy ty1) (OfTy ty2))])
      (λ post '-[x], post -[x]).
  Proof.
    intros Alv. eapply typed_instr_tr_impl;
      [|apply (type_change_vplace_instr _ _ _ _ K _ _ (=)); [done..|apply vplace_conv_prod_unfold]].
    intros post [[x₀ ζm] []] mask π Hπ [x₀' ζm'] Hζ Hin (y' & <- & Hx).
    simpl in *. subst. by rewrite pctx_set_get.
  Qed.

  Lemma type_unfold_oplace_prod_instr {𝔅1 𝔅2 𝔄} E L I p n (K: pctx (𝔅1 * 𝔅2) 𝔄) `{!PctxNoShr K}
      (ty1: type 𝔅1) (ty2: type 𝔅2) :
    lctx_lft_alive E L (pctx_ulft K (OfTy (ty1 * ty2)) ⊓ ty_lft (prod_ty ty1 ty2)) →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K (OfTy (ty1 * ty2))] (Seq Skip Skip)
      (const +[p ◁ₗown{n} pctx_plug K (ProdLty (OfTy ty1) (OfTy ty2))])
      (λ post '-[x], post -[x]).
  Proof. intros. by apply (type_unfold_vplace_prod_instr _ _ _ _ (POwn n K)). Qed.

  Lemma type_fold_vplace_prod_instr {𝔅1 𝔅2 𝔄} E L I p (K: pctx (𝔅1 * 𝔅2) 𝔄) `{!PctxNoShr K} `{!PctxVRoot K}
      (ty1: type 𝔅1) (ty2: type 𝔅2) :
    lctx_lft_alive E L (pctx_ulft K (ProdLty (OfTy ty1) (OfTy ty2)) ⊓ ty_lft (prod_ty ty1 ty2)) →
    typed_instr E L I +[p ◁ₗ pctx_plug K (ProdLty (OfTy ty1) (OfTy ty2))] (Seq Skip Skip)
      (const +[p ◁ₗ pctx_plug K (OfTy (ty1 * ty2))])
      (λ post '-[x], post -[x]).
  Proof.
    intros Alv. eapply typed_instr_tr_impl;
      [|apply (type_change_vplace_instr _ _ _ _ K _ _ (=)); [done..|apply vplace_conv_prod_fold]].
    intros post [[x₀ ζm] []] mask π Hπ [x₀' ζm'] Hζ Hin (y' & <- & Hx).
    simpl in *. subst. by rewrite pctx_set_get.
  Qed.

  Lemma type_fold_oplace_prod_instr {𝔅1 𝔅2 𝔄} E L I p n (K: pctx (𝔅1 * 𝔅2) 𝔄) `{!PctxNoShr K}
      (ty1: type 𝔅1) (ty2: type 𝔅2) :
    lctx_lft_alive E L (pctx_ulft K (ProdLty (OfTy ty1) (OfTy ty2)) ⊓ ty_lft (prod_ty ty1 ty2)) →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K (ProdLty (OfTy ty1) (OfTy ty2))] (Seq Skip Skip)
      (const +[p ◁ₗown{n} pctx_plug K (OfTy (ty1 * ty2))])
      (λ post '-[x], post -[x]).
  Proof. intros. by apply (type_fold_vplace_prod_instr _ _ _ _ (POwn n K)). Qed.
  (** ** Unique borrows *)

  Lemma prfn_rsv_uniq_leaf {𝔄} l' (y: ~~𝔄) ξi ζl :
    prfn_rsv (inr (l', inl (PlaceIn y), ξi) : prfn (uniq_borₛ 𝔄)) (ζl ++ [uniq_prvar y ξi]).
  Proof.
    simpl. split; [apply prfn_rsv_in|]. rewrite prfn_wit_in.
    apply (proph_dep_weaken _ [uniq_prvar y ξi]); [set_solver|].
    apply (proph_dep_constr fst (λ π, π (uniq_prvar y ξi))), proph_dep_one.
  Qed.

  Lemma pctx_ulft_uend {𝔅 𝔄} (K: pctx 𝔅 𝔄) κ lt :
    pctx_uend K = Some κ → ⊢ pctx_ulft K lt ⊑ κ.
  Proof. intros Hu. iApply pctx_ulft_ulfts. by apply pctx_uend_ulfts. Qed.

  (** Unfolding a unique borrow at a hole in [Owned] mode: the token of the prophecy
      variable of the borrow is taken from its body, to extend the reservations of the
      enclosing borrows. *)
  Lemma vplace_conv_uniq_unfold_own {𝔅 𝔄} (K: pctx (uniq_borₛ 𝔅) 𝔄) (ty: type 𝔅) κ' :
    pctx_uend K = None →
    vplace_conv K (OfTy (&uniq{κ'} ty)) (UniqLty (OfTy ty) κ') (=).
  Proof.
    iIntros (Hu x ζm dh gh D tid lh G E ? HE HdK ?) "#LFT #PROPH #UNIQ #TIME #Gk G ⧖ £ ⧗ H".
    rewrite (pctx_kind_owned K) //. have Hm := pctx_hmode_le K 0.
    set mh := pctx_hmode K 0.
    destruct (pctx_get K x) as [[[[[l' y] ξi'] d1] g1] idx'] eqn:Hy.
    iDestruct "H" as (? ->) "[Pt Gho]".
    iDestruct (lc_weaken mh with "£") as "£"; [lia|].
    iMod (lc_fupd_elim_laterN with "£ Gho") as "(#Incl' & %Hle1 & Body1)".
    iDestruct "Body1" as (κp' γ') "(#Inclp' & (Gh1 & Tok1) & ⧗1 & #Bor1)".
    iAssert (G &&{↑NllftG}&&> @[κ'])%I as "#Gκ'".
    { iApply (guards_transitive with "Gk"). iApply llftl_incl_trans;
        [iApply llftl_intersect_incl_r|iApply llftl_intersect_incl_l]. }
    iMod (proph_idx_bor_gen_tok_acc with "LFT Gκ' Tok1 Bor1 G") as "[ξ'tok ξ'back]";
      [trans lazyE; [rewrite /lazyE; solve_ndisj|set_solver]|].
    iModIntro. iExists (l', y, ξi', d1, g1, idx'), [uniq_prvar y ξi'], 1%Qp.
    iSplit; [done|]. iSplit; [iPureIntro; intros ??; apply prfn_rsv_uniq_leaf|].
    rewrite big_sepL_singleton. iFrame "ξ'tok". iIntros "ξ'tok".
    iMod ("ξ'back" with "ξ'tok") as "[Tok1 $]". iModIntro.
    iDestruct (cumulative_time_receipt_mono (2 + mh) with "⧗") as "⧗"; [lia|].
    iApply (uniq_ofty_unfold_own mh ty κ' l' y ξi' d1 g1 idx' with "TIME ⧗").
    rewrite /ltype_own /= /ofty_owned /=. iExists (l', y, ξi', d1, g1, idx'). iSplit; [done|]. iFrame "Pt".
    iApply bi.laterN_intro. iFrame "Incl'". iSplit; [done|]. iExists κp', γ'. rewrite /uniq_bodyγ /uniq_tokγ. by iFrame "∗#".
  Qed.

  (** Unfolding a unique borrow at a hole in [Uniq κ] mode (the referent of the innermost
      enclosing borrow is the unique borrow): the enclosing borrow is switched to the node
      of [UniqLty], and reserved for the prophecy variable of the unfolded borrow (as
      [type_unfold_place_uniq_instr]). *)
  Lemma vplace_conv_uniq_unfold_uniq {𝔅 𝔄} (K: pctx (uniq_borₛ 𝔅) 𝔄) (ty: type 𝔅) κ κ' :
    pctx_uend K = Some κ →
    vplace_conv K (OfTy (&uniq{κ'} ty)) (UniqLty (OfTy ty) κ') (=).
  Proof.
    iIntros (Hu x ζm dh gh D tid lh G E ? HE HdK ?) "#LFT #PROPH #UNIQ #TIME #Gk G ⧖ £ ⧗ H".
    rewrite (pctx_kind_uniq K κ) //. set ξi := pctx_hξi K x.
    have HE': ↑Nllft ∪ ↑prophN ⊆ E. { trans lazyE; [rewrite /lazyE; solve_ndisj|set_solver]. }
    have HEG: ↑NllftG ⊆ E. { trans lazyE; [apply lazyE_NllftG|set_solver]. }
    destruct (pctx_get K x) as [[[[[l' y] ξi'] d1] g1] idx'] eqn:Hy.
    set v : ~~ (uniq_borₛ 𝔅) := (l', y, ξi', d1, g1, idx').
    iDestruct "H" as (x0 idx0 ->) "(%κp & %γ & #Inclp & (Gh & Tok) & ⧗o & #Bor)".
    iMod (fractional.frac_split_guard_in_half NllftG G G with "G []")
      as (γh) "[H1 [H2 [#Ghh #Back]]]"; [done|iApply guards_refl|].
    iAssert (fractional.half γh &&{↑NllftG}&&> @[κ])%I as "#Hκ".
    { iApply (guards_transitive with "Ghh"). iApply (guards_transitive with "Gk").
      iApply llftl_incl_trans; [iApply llftl_intersect_incl_l|]. by iApply pctx_ulft_uend. }
    iAssert (fractional.half γh &&{↑NllftG}&&> @[ty_lft (uniq_bytes κ' ty)])%I as "#Hty".
    { iApply (guards_transitive with "Ghh"). iApply (guards_transitive with "Gk").
      iApply llftl_intersect_incl_r. }
    iAssert (fractional.half γh &&{↑NllftG}&&> @[κ'])%I as "#Hκ'".
    { iApply (guards_transitive with "Hty"). iApply llftl_intersect_incl_l. }
    iMod (ghost_var_alloc (lstate_triv (𝔄:=unitₛ) ())) as (γf) "Tf".
    set node := ltype_own_cp false (UniqLty (OfTy ty) κ') (Owned 0).
    iMod (proph_idx_bor_gen_acc_rebody_rsv E κ (uniq_prvar v ξi) (uniq_cell v dh gh γ) idx0
      (uniq_gbody κp (&uniq{κ'} ty) tid lh) (cpd_gbody κp γf (&uniq{κ'} ty) node tid lh)
      with "LFT PROPH UNIQ Hκ Tok Bor H1") as (wπ) "[Body Close]"; [done|].
    iMod (uniq_gbody_triv_open with "Gh Body") as "(%Hw & Gh & Gh' & Pl)".
    iDestruct (lc_weaken 1 with "£") as "£"; [lia|].
    iMod (lc_fupd_elim_later with "£ Pl") as "Pl".
    iMod (uniq_payload_run with "Hty H2 Pl") as "(H2 & #⧖' & Gho & Pt)"; [set_solver|].
    iDestruct "Gho" as "(#Incl' & %Hle1 & Body1)".
    iDestruct "Body1" as (κp' γ') "(#Inclp' & (Gh1 & Tok1) & ⧗1 & #Bor1)".
    iMod (proph_idx_bor_gen_tok_acc with "LFT Hκ' Tok1 Bor1 H2") as "[ξ'tok ξ'back]";
      [solve_ndisj|].
    set r_o : prfn (uniq_borₛ 𝔅) := inr (l', inl (PlaceIn y), ξi').
    iModIntro. iExists v, [uniq_prvar y ξi'], 1%Qp.
    iSplit; [done|]. iSplit; [iPureIntro; intros ??; apply prfn_rsv_uniq_leaf|].
    rewrite big_sepL_singleton. iFrame "ξ'tok". iIntros "ξ'tok".
    iMod (ghost_var_update_halves (lstate (PatUniq PatLeaf) r_o) with "Gh Gh'") as "[Gh Gh']".
    iMod ("Close" $! (uniq_cell v dh gh γ) wπ [uniq_prvar y ξi'] 1%Qp (fractional.half γh)
      with "[] [ξ'tok] [Gh' Pt ⧗ ⧗1 Gh1 ξ'back]") as (idx'') "(Tok & #Bor' & H1 & H2)".
    { (* Back to the body of [&uniq], at the same state. *)
      iIntros "!>" (c2 w2) "Q". iModIntro. iNext.
      iDestruct "Q" as "[Q|[_ $]]". rewrite /cpd_body /uniq_gbody /cpd_body.
      iDestruct "Q" as (p2 r2) "(#Ok & % & Gh2 & Upd)". iExists p2, r2. iFrame "Ok Gh2".
      iSplit; [done|]. iApply (guarded_upd_mono with "[] Upd").
      iIntros "[#⧖2 N] !>". iFrame "⧖2".
      by iApply (ltype_owned_leaf_node_uniq with "TIME LFT PROPH UNIQ Ok ⧖2 N"). }
    { by rewrite big_sepL_singleton. }
    { iIntros "ξ'tok". rewrite big_sepL_singleton.
      iMod ("ξ'back" with "ξ'tok") as "[Tok1 $]".
      iModIntro. iNext. iLeft. rewrite cpd_body_cell.
      iExists (PatUniq PatLeaf), r_o. iFrame "Gh'".
      iSplit; [by rewrite /pat_ok|]. iSplit.
      { iPureIntro. intros π. rewrite Hw /r_o /= !prfn_den_in /= prfn_wit_in.
        f_equal; try apply uniq_prvar_app_irrel. }
      iApply guarded_upd_intro. iModIntro. iFrame "⧖'".
      rewrite /node /= /uniq_node. iEval (rewrite /v cbytes_uniq_bor) in "Pt".
      iFrame "Pt TIME Incl'".
      iSplitL "⧗". { iApply (cumulative_time_receipt_mono with "⧗"). lia. }
      iExists d1, g1. iSplit; [done|]. iExists y, idx'. iSplit; [done|].
      iExists κp', γ'. rewrite /uniq_bodyγ /uniq_tokγ. by iFrame "∗#". }
    iMod (fupd_mask_mono with "(Back H1 H2)") as "$"; [done|].
    iModIntro. rewrite /= /cpd_own. iExists v, κp, γ, γf, idx'', [uniq_prvar y ξi'].
    iFrame "∗#". iPureIntro. by apply (prfn_rsv_uniq_leaf _ _ _ []).
  Qed.

  Lemma vplace_conv_uniq_unfold {𝔅 𝔄} (K: pctx (uniq_borₛ 𝔅) 𝔄) (ty: type 𝔅) κ' :
    vplace_conv K (OfTy (&uniq{κ'} ty)) (UniqLty (OfTy ty) κ') (=).
  Proof.
    destruct (pctx_uend K) as [κ|] eqn:Hu;
      [by eapply vplace_conv_uniq_unfold_uniq|by apply vplace_conv_uniq_unfold_own].
  Qed.

  (** Folding back a unique borrow whose referent is a leaf, in [Owned] mode. The depths
      and the index of the value of the borrow change. *)
  Lemma vplace_conv_uniq_fold_own {𝔅 𝔄} (K: pctx (uniq_borₛ 𝔅) 𝔄) (ty: type 𝔅) κ' :
    pctx_uend K = None →
    vplace_conv K (UniqLty (OfTy ty) κ') (OfTy (&uniq{κ'} ty))
      (λ y y', ∃ d g idx, y' = uniq_bor_set_meta y d g idx).
  Proof.
    iIntros (Hu x ζm dh gh D tid lh G E ? HE HdK ?) "_ _ _ _ _ G _ _ _ H".
    rewrite (pctx_kind_owned K) //.
    destruct (pctx_get K x) as [[[[[l' y] ξi'] d1] g1] idx'] eqn:Hy.
    iDestruct (uniq_ofty_fold_own with "H") as "[_ (%d' & %g' & %idx & H)]".
    iModIntro. iExists (l', y, ξi', d', g', idx), [], 1%Qp.
    iSplit; [by iExists d', g', idx|]. iSplit; [iPureIntro; intros ??; apply prfn_rsv_in|].
    iSplitR; [done|]. iIntros "_ !>". iFrame.
  Qed.

  (** Folding back in [Uniq κ] mode: the enclosing borrow is unreserved and switched back
      to the body of [&uniq] (as [type_fold_place_uniq_instr]). *)
  Lemma vplace_conv_uniq_fold_uniq {𝔅 𝔄} (K: pctx (uniq_borₛ 𝔅) 𝔄) (ty: type 𝔅) κ κ' :
    pctx_uend K = Some κ →
    vplace_conv K (UniqLty (OfTy ty) κ') (OfTy (&uniq{κ'} ty))
      (λ y y', ∃ d g idx, y' = uniq_bor_set_meta y d g idx).
  Proof.
    iIntros (Hu x ζm dh gh D tid lh G E ? HE HdK ?) "#LFT #PROPH #UNIQ #TIME #Gk G ⧖ £ ⧗ H".
    rewrite (pctx_kind_uniq K κ) //. set ξi := pctx_hξi K x.
    have HE': ↑Nllft ∪ ↑prophN ⊆ E. { trans lazyE; [rewrite /lazyE; solve_ndisj|set_solver]. }
    have HEG: ↑NllftG ⊆ E. { trans lazyE; [apply lazyE_NllftG|set_solver]. }
    destruct (pctx_get K x) as [[[[[l' y] ξi'] d1] g1] idx'] eqn:Hy.
    iMod (fractional.frac_split_guard_in_half NllftG G G with "G []")
      as (γh) "[H1 [H2 [#Ghh #Back]]]"; [done|iApply guards_refl|].
    iAssert (fractional.half γh &&{↑NllftG}&&> @[κ])%I as "#Hκ".
    { iApply (guards_transitive with "Ghh"). iApply (guards_transitive with "Gk").
      iApply llftl_incl_trans; [iApply llftl_intersect_incl_l|]. by iApply pctx_ulft_uend. }
    iAssert (fractional.half γh &&{↑NllftG}&&> @[ty_lft (uniq_bytes κ' ty)])%I as "#Hty".
    { iApply (guards_transitive with "Ghh"). iApply (guards_transitive with "Gk").
      iApply llftl_intersect_incl_r. }
    iDestruct "H" as (x₀w κp γ γf idx0 ζl) "(#Inclp & _ & Tok & Gh & Tf & ⧗o & #Bor)".
    iMod (proph_idx_bor_gen_unreserve with "LFT PROPH UNIQ Hκ H1 Tok Bor") as "[Tok H1]"; [done|].
    have ?: Inhabited (~~ (uniq_borₛ 𝔅)) := populate x₀w.
    iMod (proph_idx_bor_gen_acc_rebody_guarded E κ (uniq_prvar x₀w ξi) (uniq_cell x₀w dh gh γ)
      idx0 _ (uniq_gbody κp (&uniq{κ'} ty) tid lh)
      with "LFT UNIQ Hκ Tok Bor H1") as (wπ) "[Body Close]"; [solve_ndisj|].
    iDestruct (bi.later_or with "Body") as "[Body|[>Tf' _]]"; last first.
    { iDestruct (cpd_tok_excl with "Tf Tf'") as "[]". }
    rewrite cpd_body_cell.
    iDestruct (lc_weaken 1 with "£") as "£"; [lia|].
    iMod (lc_fupd_elim_later with "£ Body") as (p1 r1) "(_ & _ & Gh' & Upd)".
    iDestruct (ghost_var_agree with "Gh Gh'") as %[<- <-]%lstate_inj.
    iMod (guarded_upd_run with "Hty H2 Upd") as "(H2 & #⧖' & N)"; [set_solver|].
    iDestruct "N" as "(Pt & _ & _ & #Incl' & %d2 & %g2 & %Hle2 & C)".
    iDestruct "C" as (y0 idx1 ->) "Body1".
    set v' : ~~ (uniq_borₛ 𝔅) := (l', y, ξi', d2, g2, idx1).
    iMod (ghost_var_update_halves (lstate_triv v') with "Gh Gh'") as "[Gh Gh']".
    iSpecialize ("Close" $! (uniq_cell v' dh gh γ) (vπ (uniq_cell v' dh gh γ))).
    iMod (fupd_mask_mono with "(Close [Gh' Pt Body1] [Tf])") as (idx2) "(Tok & #Bor' & H1)";
      [solve_ndisj| | |].
    { iApply (uniq_gbody_triv_close with "Gh'"); [done|]. iNext.
      iApply (uniq_payload_intro (&uniq{κ'} ty) tid lh v' dh gh with "⧖' [Body1] [Pt]").
      { iFrame "Incl' Body1". iPureIntro. lia. }
      by rewrite /v' cbytes_uniq_bor. }
    { iIntros "!>" (c2 w2) "P". iModIntro. iNext. iRight. iFrame. }
    iMod (fupd_mask_mono with "(Back H1 H2)") as "G"; [done|].
    iModIntro. iExists v', [], 1%Qp. iSplit; [by iExists d2, g2, idx1|].
    iSplit; [iPureIntro; intros ??; apply prfn_rsv_in|]. iSplitR; [done|]. iIntros "_ !>".
    iFrame "G". rewrite /= /ofty_uniq. iExists v', idx2. iSplit; [done|].
    iApply (uniq_body_from_parts with "Inclp [Gh Tok] ⧗o [Bor']").
    - rewrite /uniq_tokγ (uniq_bor_tok_retarget _ x₀w). iFrame.
    - by rewrite /uniq_persγ (uniq_idx_bor_gen_retarget _ _ x₀w).
  Qed.

  Lemma vplace_conv_uniq_fold {𝔅 𝔄} (K: pctx (uniq_borₛ 𝔅) 𝔄) (ty: type 𝔅) κ' :
    vplace_conv K (UniqLty (OfTy ty) κ') (OfTy (&uniq{κ'} ty))
      (λ y y', ∃ d g idx, y' = uniq_bor_set_meta y d g idx).
  Proof.
    destruct (pctx_uend K) as [κ|] eqn:Hu;
      [by eapply vplace_conv_uniq_fold_uniq|by apply vplace_conv_uniq_fold_own].
  Qed.

  (** Unfolding the unique borrow at the hole of [K] (at any path, also below other unique
      borrows) into a nested place. *)
  Lemma type_unfold_vplace_uniq_instr {𝔅 𝔄} E L I p (K: pctx (uniq_borₛ 𝔅) 𝔄) `{!PctxNoShr K} `{!PctxVRoot K} (ty: type 𝔅) κ' :
    lctx_lft_alive E L (pctx_ulft K (OfTy (&uniq{κ'} ty)) ⊓ ty_lft (uniq_bytes κ' ty)) →
    typed_instr E L I +[p ◁ₗ pctx_plug K (OfTy (&uniq{κ'} ty))] (Seq Skip Skip)
      (const +[p ◁ₗ pctx_plug K (UniqLty (OfTy ty) κ')])
      (λ post '-[x], post -[x]).
  Proof.
    intros Alv. eapply typed_instr_tr_impl;
      [|apply (type_change_vplace_instr _ _ _ _ K _ _ (=)); [done..|apply vplace_conv_uniq_unfold]].
    intros post [[x₀ ζm] []] mask π Hπ [x₀' ζm'] Hζ Hin (y' & <- & Hx).
    simpl in *. subst. by rewrite pctx_set_get.
  Qed.

  Lemma type_unfold_oplace_uniq_instr {𝔅 𝔄} E L I p n (K: pctx (uniq_borₛ 𝔅) 𝔄) `{!PctxNoShr K} (ty: type 𝔅) κ' :
    lctx_lft_alive E L (pctx_ulft K (OfTy (&uniq{κ'} ty)) ⊓ ty_lft (uniq_bytes κ' ty)) →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K (OfTy (&uniq{κ'} ty))] (Seq Skip Skip)
      (const +[p ◁ₗown{n} pctx_plug K (UniqLty (OfTy ty) κ')])
      (λ post '-[x], post -[x]).
  Proof. intros. by apply (type_unfold_vplace_uniq_instr _ _ _ _ (POwn n K)). Qed.

  (** Folding it back. *)
  Lemma type_fold_vplace_uniq_instr {𝔅 𝔄} E L I p (K: pctx (uniq_borₛ 𝔅) 𝔄) `{!PctxNoShr K} `{!PctxVRoot K} (ty: type 𝔅) κ' :
    lctx_lft_alive E L (pctx_ulft K (UniqLty (OfTy ty) κ') ⊓ ty_lft (uniq_bytes κ' ty)) →
    typed_instr E L I +[p ◁ₗ pctx_plug K (UniqLty (OfTy ty) κ')] (Seq Skip Skip)
      (const +[p ◁ₗ pctx_plug K (OfTy (&uniq{κ'} ty))])
      (λ post '-[x], λ mask π, ∀ d g idx,
        post -[(pctx_set K x.1 (uniq_bor_set_meta (pctx_get K x.1) d g idx), x.2)]
          mask π).
  Proof.
    intros Alv. eapply typed_instr_tr_impl;
      [|apply (type_change_vplace_instr _ _ _ _ K _ _ (λ y y', ∃ d g idx, y' = uniq_bor_set_meta y d g idx)); [done..|apply vplace_conv_uniq_fold]].
    intros post [[x₀ ζm] []] mask π Hπ [x₀' ζm'] Hζ Hin (y' & (d & g & idx & ->) & Hx).
    simpl in *. subst. apply Hπ.
  Qed.

  Lemma type_fold_oplace_uniq_instr {𝔅 𝔄} E L I p n (K: pctx (uniq_borₛ 𝔅) 𝔄) `{!PctxNoShr K} (ty: type 𝔅) κ' :
    lctx_lft_alive E L (pctx_ulft K (UniqLty (OfTy ty) κ') ⊓ ty_lft (uniq_bytes κ' ty)) →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K (UniqLty (OfTy ty) κ')] (Seq Skip Skip)
      (const +[p ◁ₗown{n} pctx_plug K (OfTy (&uniq{κ'} ty))])
      (λ post '-[x], λ mask π, ∀ d g idx,
        post -[((x.1.1, pctx_set K x.1.2 (uniq_bor_set_meta (pctx_get K x.1.2) d g idx)), x.2)]
          mask π).
  Proof. intros. by apply (type_fold_vplace_uniq_instr _ _ _ _ (POwn n K)). Qed.
  (** ** Owned pointers (in [Owned] mode; the laters in front of the pointee are stripped
      with the credits of the step) *)

  Lemma vplace_conv_own_unfold {𝔅 𝔄} (K: pctx (at_locₛ 𝔅) 𝔄) n (ty: type 𝔅) :
    pctx_uend K = None →
    vplace_conv K (OfTy (own_bytes n ty)) (OwnPtrLty n (OfTy ty)) (=).
  Proof.
    iIntros (Hu x ζm dh gh D tid lh G E ? HE HdK ?) "_ _ _ _ _ G _ £ _ H".
    rewrite (pctx_kind_owned K) //. have Hm := pctx_hmode_le K 0. set mh := pctx_hmode K 0.
    destruct (pctx_get K x) as [l' y] eqn:Hy.
    iDestruct "H" as (? ->) "[Pt Gho]".
    iDestruct (lc_weaken mh with "£") as "£"; [lia|].
    iMod (lc_fupd_elim_laterN with "£ Gho") as "Gho".
    destruct dh as [|dh']; [done|]. iDestruct "Gho" as "(Pt' & Fr' & Gho)".
    iModIntro. iExists (l', y), [], 1%Qp. iSplit; [done|].
    iSplit; [iPureIntro; intros ??; apply prfn_rsv_in|]. iSplitR; [done|]. iIntros "_ !>".
    iFrame "G". rewrite /= /own_node. iEval (rewrite cbytes_at_loc) in "Pt". iFrame "Pt".
    iSplit; [done|]. rewrite /lty_size -(ty_bsize_eq ty).
    iSplitL "Fr'"; [by iApply bi.laterN_intro|].
    iExists y. iSplit; [done|]. rewrite /ofty_owned.
    iFrame "Pt'". rewrite Nat.add_1_r /=. iNext. by iApply bi.laterN_intro.
  Qed.

  Lemma vplace_conv_own_fold {𝔅 𝔄} (K: pctx (at_locₛ 𝔅) 𝔄) n (ty: type 𝔅) :
    pctx_uend K = None →
    vplace_conv K (OwnPtrLty n (OfTy ty)) (OfTy (own_bytes n ty)) (=).
  Proof.
    iIntros (Hu x ζm dh gh D tid lh G E ? HE HdK ?) "_ _ _ _ _ G _ _ _ H".
    rewrite (pctx_kind_owned K) //.
    destruct (pctx_get K x) as [l' y] eqn:Hy.
    iModIntro. iExists (l', y), [], 1%Qp. iSplit; [done|].
    iSplit; [iPureIntro; intros ??; apply prfn_rsv_in|]. iSplitR; [done|]. iIntros "_ !>".
    iFrame "G". by iApply (ownptr_ofty_fold_own with "H").
  Qed.

  Lemma type_unfold_vplace_own_deep_instr {𝔅 𝔄} E L I p (K: pctx (at_locₛ 𝔅) 𝔄) `{!PctxNoShr K} `{!PctxVRoot K} n (ty: type 𝔅) :
    pctx_uend K = None →
    lctx_lft_alive E L (pctx_ulft K (OfTy (own_bytes n ty)) ⊓ ty_lft (own_bytes n ty)) →
    typed_instr E L I +[p ◁ₗ pctx_plug K (OfTy (own_bytes n ty))] (Seq Skip Skip)
      (const +[p ◁ₗ pctx_plug K (OwnPtrLty n (OfTy ty))])
      (λ post '-[x], post -[x]).
  Proof.
    intros Hu Alv. eapply typed_instr_tr_impl;
      [|apply (type_change_vplace_instr _ _ _ _ K _ _ (=)); [done..|by apply vplace_conv_own_unfold]].
    intros post [[x₀ ζm] []] mask π Hπ [x₀' ζm'] Hζ Hin (y' & <- & Hx).
    simpl in *. subst. by rewrite pctx_set_get.
  Qed.

  Lemma type_unfold_oplace_own_deep_instr {𝔅 𝔄} E L I p n' (K: pctx (at_locₛ 𝔅) 𝔄) `{!PctxNoShr K} n (ty: type 𝔅) :
    pctx_uend K = None →
    lctx_lft_alive E L (pctx_ulft K (OfTy (own_bytes n ty)) ⊓ ty_lft (own_bytes n ty)) →
    typed_instr E L I +[p ◁ₗown{n'} pctx_plug K (OfTy (own_bytes n ty))] (Seq Skip Skip)
      (const +[p ◁ₗown{n'} pctx_plug K (OwnPtrLty n (OfTy ty))])
      (λ post '-[x], post -[x]).
  Proof. intros. by apply (type_unfold_vplace_own_deep_instr _ _ _ _ (POwn n' K)). Qed.

  Lemma type_fold_vplace_own_deep_instr {𝔅 𝔄} E L I p (K: pctx (at_locₛ 𝔅) 𝔄) `{!PctxNoShr K} `{!PctxVRoot K} n (ty: type 𝔅) :
    pctx_uend K = None →
    lctx_lft_alive E L (pctx_ulft K (OwnPtrLty n (OfTy ty)) ⊓ ty_lft (own_bytes n ty)) →
    typed_instr E L I +[p ◁ₗ pctx_plug K (OwnPtrLty n (OfTy ty))] (Seq Skip Skip)
      (const +[p ◁ₗ pctx_plug K (OfTy (own_bytes n ty))])
      (λ post '-[x], post -[x]).
  Proof.
    intros Hu Alv. eapply typed_instr_tr_impl;
      [|apply (type_change_vplace_instr _ _ _ _ K _ _ (=)); [done..|by apply vplace_conv_own_fold]].
    intros post [[x₀ ζm] []] mask π Hπ [x₀' ζm'] Hζ Hin (y' & <- & Hx).
    simpl in *. subst. by rewrite pctx_set_get.
  Qed.

  Lemma type_fold_oplace_own_deep_instr {𝔅 𝔄} E L I p n' (K: pctx (at_locₛ 𝔅) 𝔄) `{!PctxNoShr K} n (ty: type 𝔅) :
    pctx_uend K = None →
    lctx_lft_alive E L (pctx_ulft K (OwnPtrLty n (OfTy ty)) ⊓ ty_lft (own_bytes n ty)) →
    typed_instr E L I +[p ◁ₗown{n'} pctx_plug K (OwnPtrLty n (OfTy ty))] (Seq Skip Skip)
      (const +[p ◁ₗown{n'} pctx_plug K (OfTy (own_bytes n ty))])
      (λ post '-[x], post -[x]).
  Proof. intros. by apply (type_fold_vplace_own_deep_instr _ _ _ _ (POwn n' K)). Qed.
  (** * Mutable borrow of a leaf below unique borrows *)

  Lemma pctx_hmode_ne {𝔅 𝔄} (K: pctx 𝔅 𝔄) `{!PctxNoShr K} m e mm :
    pctx_hmode K m + pctx_ne K e mm =
      pctx_dlev K + e + (match pctx_ulfts K with [] => m | _ => mm end).
  Proof.
    rename select (PctxNoShr K) into HK. rewrite /PctxNoShr in HK.
    induction K in HK, m, e, mm |- *; simpl; simpl in HK; [lia|auto|auto| |auto| |done|done].
    - rewrite IHK //. destruct (pctx_ulfts K); lia.
    - rewrite IHK; [|by destruct HK]. destruct (pctx_ulfts K); lia.
  Qed.

  (** The same for a context whose first step is the root pointer of a place rooted at a
      value. *)
  Lemma pctx_vhmode_ne_le {𝔅 𝔄} (K: pctx 𝔅 𝔄) `{!PctxNoShr K} `{!PctxVRoot K} :
    pctx_hmode K 0 + pctx_vne K ≤ pctx_dlev K.
  Proof.
    rename select (PctxVRoot K) into HR. rename select (PctxNoShr K) into HK.
    destruct K as [| | |𝔅 𝔄' n K| |𝔅 𝔄' κ K| |]; try done.
    - have ?: PctxNoShr K by exact HK.
      pose proof (pctx_hmode_ne K 1 0 0). simpl in *. destruct (pctx_ulfts K); lia.
    - have ?: PctxNoShr K by exact (proj2 HK).
      pose proof (pctx_hmode_ne K 0 1 0). simpl in *. destruct (pctx_ulfts K); lia.
  Qed.

  Lemma pctx_vhmode_ne_ge {𝔅 𝔄} (K: pctx 𝔅 𝔄) `{!PctxNoShr K} `{!PctxVRoot K} :
    pctx_dlev K ≤ pctx_hmode K 0 + pctx_vne K + 1.
  Proof.
    rename select (PctxVRoot K) into HR. rename select (PctxNoShr K) into HK.
    destruct K as [| | |𝔅 𝔄' n K| |𝔅 𝔄' κ K| |]; try done.
    - have ?: PctxNoShr K by exact HK.
      pose proof (pctx_hmode_ne K 1 0 0). simpl in *. destruct (pctx_ulfts K); lia.
    - have ?: PctxNoShr K by exact (proj2 HK).
      pose proof (pctx_hmode_ne K 0 1 0). simpl in *. destruct (pctx_ulfts K); lia.
  Qed.

  (** A mutable borrow of the leaf at the hole of [K] in [Owned] mode (at any path, below
      any number of unique borrows): the new borrow is at [pctx_blft K α], the intersection
      of the enclosing borrow lifetimes and [α] ([α] if there is none); its fresh prophecy
      variable extends the reservations of all enclosing borrows. *)
  Lemma type_borrow_vplace_owned {𝔅 𝔄} E L I p α (K: pctx 𝔅 𝔄) `{!PctxNoShr K} `{!PctxVRoot K} (ty: type 𝔅) :
    pctx_uend K = None →
    lctx_lft_alive E L (pctx_ulft K (OfTy ty) ⊓ α) → elctx_sat E L (ty_outlives_E ty α) →
    typed_instr E L I +[p ◁ₗ pctx_plug K (OfTy ty)] (&ᵘ (pctx_vexpr K p))
      (λ w, +[w ◁ᵥ &uniq{pctx_blft K α} ty; p ◁ₗ pctx_plug K (Blocked ty (pctx_blft K α))])
      (λ post '-[x], λ mask π, ∀ m1: ~~ (uniq_borₛ 𝔅),
        uniq_bor_current m1 = pctx_get K x.1 →
        post -[m1; (x.1, (pctx_vpath K, uniq_bor_ξi m1) :: x.2)] mask π).
  Proof.
    intros Hu Alv Out tid post mask iκs [x []].
    iIntros "#LFT #TIME #PROPH #UNIQ #E L I [T _] Obs".
    destruct x as [x₀ ζm].
    rewrite /tctx_elt_interp /borrow_uniq.
    iDestruct "T" as (v Hp) "T". iEval (rewrite vplace_own_open) in "T".
    iDestruct "T" as (D) "(#⧖ & ⧗p & Own)". have Hdl: 1 ≤ pctx_dlev K by apply pctx_vroot_dlev.
    have ?: Closed [] (pctx_vexpr K p).
    { apply pctx_vexpr_closed. by eapply eval_path_closed. }
    iDestruct (Out with "L E") as "#Out".
    iDestruct (elctx_interp_ty_outlives_E with "Out") as "#Incl".
    iDestruct (Alv with "L E") as "#Alv".
    set β := pctx_blft K α.
    (* Two steps, for credits and cumulative time receipts. *)
    wp_bind (Seq Skip Skip). wp_bind Skip. iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [set_solver|].
    iIntros "£ #⧖S". wp_let. iModIntro. wp_let. iApply wp_fupd.
    iApply (wp_cumulative_time_receipt_linear with "TIME ⧖S"); [set_solver|].
    iIntros "⧗". wp_let. iModIntro. wp_let.
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_ulft K (OfTy ty)])%I as "#Hu".
    { iApply (guards_transitive with "Ghalf"). iApply (guards_transitive with "Alv").
      iApply llftl_intersect_incl_l. }
    set y := pctx_get K x₀.
    iDestruct (lc_weaken (pctx_vacc_cred K D + (D + (3 * (D + 1) * D + 1))) with "£")
      as "[£a [£k [£w £c]]]"; [have := pctx_vacc_cred_le K D; rewrite /advance_credits; nia|].
    iMod (vroot_acc K (OfTy ty) with "LFT PROPH UNIQ Hu H1 £a Own")
      as (G' dh gh) "(% & G' & #G'G & -> & %Hdh & H & P & Cl)"; [solve_ndisj|].
    destruct Hdh as (Hdh & Hgh & Hin).
    have Hm := pctx_hmode_le K 0. have Hhn: pctx_hmode K 0 + pctx_vne K ≤ pctx_dlev K by apply pctx_vhmode_ne_le.
    iEval (rewrite (pctx_kind_owned K) //) in "H".
    set mh := pctx_hmode K 0.
    set lK := pctx_vloc K (lty_size (OfTy ty)) x₀.
    iDestruct "H" as (? ->) "[Pt1 Gho1]".
    (* The address of the hole. *)
    iApply wp_fupd. wp_bind (pctx_vexpr K p).
    iApply (wp_wand with "[P G' £w]").
    { iApply (wp_pctx_vptrs ⊤ K (lty_size (OfTy ty)) G' x₀ p True%I with "[G'] P").
      iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->". by iFrame. }
    iIntros (w) "(-> & _ & G' & P)". wp_pure _.
    (* The new borrow. *)
    iDestruct (lc_weaken mh with "£k") as "£k"; [lia|].
    iMod (lc_fupd_elim_laterN with "£k Gho1") as "Gho1".
    iMod (ghost_var_alloc (lstate_triv y)) as (γζ) "[Ghζ Ghζ']".
    iMod (proph_loan_intro (uniq_cell_tyi y) ⊤ (uniq_cell y dh gh γζ) with "PROPH UNIQ")
      as (ζi) "Loan"; [solve_ndisj|].
    set ζ := uniq_prvar y ζi.
    rewrite proph_loan_unfold. iDestruct "Loan" as "[ζVo ζPc]".
    iDestruct (uniq_proph_tok with "ζVo ζPc") as "(ζVo & ζtok & ToζPc)".
    iDestruct (cumulative_time_receipt_mono (1 + (mh + S (pctx_vne K))) with "⧗") as "⧗";
      [lia|].
    iDestruct (cumulative_time_receipt_sep with "⧗") as "[⧗u ⧗]".
    iDestruct (cumulative_time_receipt_sep with "⧗") as "[⧗k ⧗e]".
    iMod ("Cl" $! (Blocked ty β) (inl (PlaceGhost y ζi)) dh gh D [ζ] 1%Qp
      (∃ idx1, proph_bor_tok ζ (uniq_cell y dh gh γζ) idx1 ∗
        proph_idx_bor_gen β ζ idx1 (uniq_gbody β ty tid lK))%I
      with "[//] [//] [//] [%] [%] [] ⧖ G' P [ζtok] [ζVo ToζPc Ghζ' Pt1 Gho1 £c ⧗k]")
      as "(Own & H1 & Bor1)".
    { intros ζl _. rewrite prfn_rsv_inl. apply place_ghost_rsv_elem. set_solver. }
    { lia. }
    { iRight. iApply pat_ok_blft. }
    { by rewrite big_sepL_singleton. }
    { iIntros "ζtok". rewrite big_sepL_singleton.
      iDestruct ("ToζPc" with "ζtok") as "ζPc".
      iMod (proph_loan_borrow_gen_pc ⊤ β ζ (uniq_cell y dh gh γζ)
        (vπ (uniq_cell y dh gh γζ)) (uniq_gbody β ty tid lK)
        with "LFT UNIQ [ζVo ζPc] [Ghζ' Pt1 Gho1]") as (idx1) "(Tok1 & #Bor1 & Back1)";
        [solve_ndisj| by rewrite proph_loan_unfold; iFrame| |].
      { iApply (uniq_gbody_triv_close with "Ghζ'"); [done|].
        iApply uniq_payload_intro_later. iNext. iFrame "Gho1 Pt1".
        iApply (persistent_time_receipt_mono with "⧖"). lia. }
      iModIntro. iSplitR "Tok1"; [|iExists idx1; by iFrame "Tok1 Bor1"].
      rewrite (pctx_kind_owned K) // /= /blocked_owned. iIntros "#†β".
      iMod (fupd_mask_mono with "(Back1 †β)") as "Lender"; [rewrite /lazyE; solve_ndisj|].
      iMod (lc_fupd_elim_later with "£c Lender") as "Lender". iModIntro.
      iApply (guarded_upd_mono with "[⧗k] [Lender]");
        [|iApply (uniq_lender_settle with "LFT PROPH †β Lender")].
      iIntros "(%x & %d1 & %g1 & Eqz & #⧖1 & Gho & Pt)".
      iMod (cumulative_persistent_time_receipt with "TIME ⧗k ⧖1") as "#⧖1'";
        [rewrite /lazyE; solve_ndisj|].
      iModIntro. iExists x, d1, g1. rewrite /ofty_owned /=. iFrame "Eqz Pt Gho".
      iApply (persistent_time_receipt_mono with "⧖1'"). lia. }
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iDestruct "Bor1" as (idx1) "[Tok1 #Bor1]".
    iModIntro. iExists -[(lK, y, ζi, dh, gh, idx1); (x₀, (pctx_vpath K, ζi) :: ζm)].
    iFrame "L I". iSplit; last first.
    { iApply (proph_obs_impl with "Obs")=> π Hπ. by apply Hπ. }
    iSplitL "Tok1 Ghζ ⧗u".
    { iExists _. iSplit; [by rewrite eval_path_of_val|]. rewrite -(val_own_intro_sep _ _ _ _ _ D); [|done|done].
      iFrame "⧖".
      iSplit. { iApply llftl_incl_trans; [iApply pctx_blft_incl_r|]. iApply "Incl". }
      iSplit; [iPureIntro; lia|]. iExists β, γζ. iFrame "∗#". iApply guards_refl. }
    iSplit; [|done]. iExists _. iSplit; [done|].
    iApply (vplace_own_close with "⧖ [⧗p ⧗e]").
    { iDestruct (cumulative_time_receipt_sep with "[$⧗p $⧗e]") as "⧗".
      iApply (cumulative_time_receipt_mono with "⧗"). rewrite !lty_vnrc_plug /=. lia. }
    by rewrite pctx_vrfn_blk_cons /= decide_True.
  Qed.


  (** * Unblocking a leaf below unique borrows *)

  Lemma pctx_ne_ge {𝔅 𝔄} (K: pctx 𝔅 𝔄) e mm : e ≤ pctx_ne K e mm.
  Proof.
    induction K in e, mm |- *; simpl; [lia|auto|auto|auto|auto| |auto| ];
      specialize (IHK (e + mm + 1) 0); lia.
  Qed.

  Lemma pctx_ne_ulfts {𝔅 𝔄} (K: pctx 𝔅 𝔄) e mm : pctx_ne K e mm = e → pctx_ulfts K = [].
  Proof.
    induction K in e, mm |- *; simpl; [done|eauto|eauto|eauto|eauto| |eauto| ];
      have := pctx_ne_ge K (e + mm + 1) 0; lia.
  Qed.

  Lemma pctx_vne_ulfts {𝔅 𝔄} (K: pctx 𝔅 𝔄) `{!PctxVRoot K} : pctx_vne K = 0 → pctx_ulfts K = [].
  Proof.
    rename select (PctxVRoot K) into HR.
    destruct K as [| | |𝔅 𝔄' n K| |𝔅 𝔄' κ K|𝔅 𝔄' κ K|𝔅 𝔄' κ K]; try done.
    - simpl. apply pctx_ne_ulfts.
    - simpl. have := pctx_ne_ge K 1 0. lia.
    - simpl. apply pctx_ne_ulfts.
    - simpl. have := pctx_ne_ge K 1 0. lia.
  Qed.

  (** Once [α] has ended, the leaf at the hole of [K] is unblocked (as [unblock_tctx_oplace]):
      the enclosing borrows are opened (with the credits of one of the receipts of the leaf,
      if there are any), the inheritance of the borrow is fired and settled, the
      borrows are closed at the new value of the leaf, at depths raised by the other
      receipts of the leaf ([lty_nrc]). *)
  Lemma unblock_tctx_vplace_deep {𝔅 𝔄 𝔄l 𝔄l'} p α (K: pctx 𝔅 𝔄) `{!PctxNoShr K} `{!PctxVRoot K} (ty: type 𝔅)
      (T: tctx 𝔄l) (T': tctx 𝔄l') E L f :
    pctx_uend K = None →
    lctx_lft_alive E L (pctx_ulft K (OfTy ty) ⊓ ty_lft ty) → unblock_tctx E L α T T' f →
    unblock_tctx E L α (p ◁ₗ pctx_plug K (Blocked ty (pctx_blft K α)) +:: T)
      (p ◁ₗ pctx_plug K (OfTy ty) +:: T')
      (λ π '(x -:: xl), λ '(x' -:: xl'),
        x'.1 = pctx_set K x.1 (pctx_get K x'.1) ∧ x'.2 = x.2 ∧
        vπ (pctx_get K x'.1) π = vplace_blk_fin K x π ∧ f π xl xl').
  Proof.
    iIntros (Hu Alv Un G tid [x xl] ?) "#LFT #TIME #PROPH #UNIQ #E #L G #†α /=[(%v & %Hp & Own) T]".
    destruct x as [x₀ ζm].
    set β := pctx_blft K α.
    iEval (rewrite vplace_own_open) in "Own". iDestruct "Own" as (D) "(#⧖0 & ⧗ & Own)".
    rewrite (lty_vnrc_plug K (Blocked ty β)) /=.
    iDestruct (cumulative_time_receipt_sep with "⧗") as "[⧗r ⧗]".
    have Hhn: pctx_hmode K 0 + pctx_vne K ≤ pctx_dlev K by apply pctx_vhmode_ne_le. have Hhn': pctx_dlev K ≤ pctx_hmode K 0 + pctx_vne K + 1 by apply pctx_vhmode_ne_ge.
    have Hdl: 1 ≤ pctx_dlev K by apply pctx_vroot_dlev. have Hm := pctx_hmode_le K 0.
    set mh := pctx_hmode K 0. set ne := pctx_vne K.
    leaf_open "L" with "G" as "[L1 back]"; [set_solver|].
    iDestruct (Alv with "L1 E") as "#Lα". iMod ("back" with "L1") as "G".
    (* Half of [G] for the rest of the context, the other half for the place. *)
    iMod (fractional.frac_split_guard_in_half with "G L") as (γ1) "[GT [GP [#GhT #BackT]]]";
      [solve_ndisj|].
    iMod (Un with "LFT TIME PROPH UNIQ E GhT GT †α T") as (dT xl') "[#⧖T ToT']".
    iMod (fractional.frac_split_guard_in_half NllftG (fractional.half γ1) (fractional.half γ1)
      with "GP []") as (γ2) "[H1 [H2 [#Gh2 #Back2]]]"; [solve_ndisj|iApply guards_refl|].
    iAssert (fractional.half γ2 &&{↑NllftG}&&> @[pctx_ulft K (Blocked ty β)])%I as "#Hu".
    { iApply (guards_transitive with "Gh2"). iApply (guards_transitive with "GhT").
      iApply (guards_transitive with "Lα"). rewrite (pctx_ulft_eq K (Blocked ty β) (OfTy ty)) //.
      iApply llftl_intersect_incl_l. }
    iAssert (fractional.half γ2 &&{↑NllftG}&&> @[ty_lft ty])%I as "#Hty".
    { iApply (guards_transitive with "Gh2"). iApply (guards_transitive with "GhT").
      iApply (guards_transitive with "Lα"). iApply llftl_intersect_incl_r. }
    (* The credits for the access: none below no unique borrow, otherwise from one receipt. *)
    iAssert (|={⊤}=> £(pctx_vacc_cred K D) ∗ ⧗1 ∗ ⧗(ne - 1))%I with "[⧗]" as ">(£a & ⧗b & ⧗e)".
    { destruct ne as [|ne'] eqn:Hne.
      - rewrite /pctx_vacc_cred (pctx_vne_ulfts K Hne). iMod lc_zero as "$". iFrame "⧗".
        iMod cumulative_time_receipt_0 as "$". done.
      - iDestruct (cumulative_time_receipt_sep 1 (S ne') with "⧗") as "[⧗a ⧗]".
        iDestruct (cumulative_time_receipt_sep 1 ne' with "⧗") as "[$ ⧗e]".
        iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗a ⧖0") as "[_ £]";
          [solve_ndisj|].
        iModIntro. iSplitL "£".
        + iApply (lc_weaken with "£"). have := pctx_vacc_cred_le K D.
          rewrite /advance_credits. nia.
        + iApply (cumulative_time_receipt_mono with "⧗e"). lia. }
    iMod (vroot_acc K (Blocked ty β) with "LFT PROPH UNIQ Hu H1 £a Own")
      as (G' dh gh) "(% & G' & #G'G & -> & %Hdh & Hb & P & Cl)"; [solve_ndisj|].
    destruct Hdh as (Hdh & Hgh & Hin).
    iEval (rewrite (pctx_kind_owned K) //) in "Hb".
    set y := pctx_get K x₀. set ζi := blk_lookup ζm (pctx_vpath K).
    (* Unblock the leaf: fire the inheritance of the borrow and settle it. *)
    iMod (fupd_mask_mono with "(Hb [])") as "Upd1"; [rewrite /lazyE; solve_ndisj| |].
    { by iApply pctx_blft_dead. }
    iMod (guarded_upd_run with "Hty H2 Upd1") as "(H2 & %y1 & %d1 & %g1 & Eqz & #⧖1 & O1)";
      [rewrite /lazyE; solve_ndisj|].
    iDestruct "O1" as "[Pt1 Gho1]".
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗b ⧖1") as "[#⧖1' £]";
      [solve_ndisj|].
    iDestruct (lc_weaken (mh + (1 + (d1 + d1*(g1+2) + (0 + (d1+1)*(g1+1)) + 1 + 1)))
      with "£") as "[£k [£e £]]"; [rewrite /advance_credits; nia|].
    iMod (lc_fupd_elim_laterN with "£k Gho1") as "Gho1".
    iSimpl in "Eqz". iMod (lc_fupd_elim_later with "£e Eqz") as "Eqz".
    iMod (proph_eqz_obs_by_share ty with "LFT Hty H2 £ Eqz Gho1") as "(#Obs1 & H2 & Gho1)".
    iMod (cumulative_persistent_time_receipt with "TIME ⧗e ⧖1'") as "#⧖2"; [solve_ndisj|].
    (* Close the place at the unblocked state, at the maximal depths. *)
    set Dn := D `max` (ne - 1 + S ((mh + S d1) `max` g1)).
    iCombine "⧖0 ⧖2" as "⧖D".
    iMod ("Cl" $! (OfTy ty) (inl (PlaceIn y1)) d1 g1 Dn [] 1%Qp True%I
      with "[//] [//] [//] [%] [%] [] [] G' P [] [Pt1 Gho1]") as "(Own & H1 & _)".
    { intros ??. apply prfn_rsv_in. }
    { rewrite /Dn. lia. }
    { iRight. iApply pat_ok_ulfts_leaf. }
    { iApply (persistent_time_receipt_mono with "⧖D"). rewrite /Dn. lia. }
    { done. }
    { iIntros "_ !>". iSplit; [|done]. rewrite (pctx_kind_owned K) //. iExists y1.
      iSplit; [done|]. rewrite /ofty_owned. iFrame "Pt1". by iApply bi.laterN_intro. }
    iMod (fupd_mask_mono with "(Back2 H1 H2)") as "GP"; [solve_ndisj|].
    iModIntro. iExists dT, ((pctx_set K x₀ y1, ζm) -:: xl').
    iSplitR; [done|].
    iMod "ToT'". iModIntro. iNext. iMod "ToT'". iModIntro.
    iApply (step_fupdN_wand with "ToT'"). iIntros ">(GT & T' & #Obs')".
    iMod (fupd_mask_mono with "(BackT GT GP)") as "$"; [solve_ndisj|].
    iModIntro. iSplitR "Obs'".
    { iFrame "T'". iExists _. iSplit; [done|].
      iApply (vplace_own_close K _ _ _ Dn with "[] [⧗r]").
      { iApply (persistent_time_receipt_mono with "⧖D"). rewrite /Dn. lia. }
      { rewrite (lty_vnrc_plug K (OfTy ty)) /=. iApply (cumulative_time_receipt_mono with "⧗r"). lia. }
      by rewrite pctx_get_set pctx_vrfn_set. }
    iCombine "Obs1 Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=> π [Heq Hf].
    split; [by rewrite /= pctx_get_set|]. split; [done|]. split; [|done].
    rewrite /vplace_blk_fin /= pctx_get_set. symmetry. exact Heq.
  Qed.

  Lemma unblock_tctx_oplace_deep {𝔅 𝔄 𝔄l 𝔄l'} p n α (K: pctx 𝔅 𝔄) `{!PctxNoShr K} (ty: type 𝔅)
      (T: tctx 𝔄l) (T': tctx 𝔄l') E L f :
    pctx_uend K = None →
    lctx_lft_alive E L (pctx_ulft K (OfTy ty) ⊓ ty_lft ty) → unblock_tctx E L α T T' f →
    unblock_tctx E L α (p ◁ₗown{n} pctx_plug K (Blocked ty (pctx_blft K α)) +:: T)
      (p ◁ₗown{n} pctx_plug K (OfTy ty) +:: T')
      (λ π '(x -:: xl), λ '(x' -:: xl'),
        x'.1.1 = x.1.1 ∧ x'.1.2 = pctx_set K x.1.2 (pctx_get K x'.1.2) ∧ x'.2 = x.2 ∧
        vπ (pctx_get K x'.1.2) π = oplace_blk_fin K x π ∧ f π xl xl').
  Proof.
    intros. eapply unblock_tctx_impl; [|by apply (unblock_tctx_vplace_deep _ _ (POwn n K))].
    intros π [[[l x₀] ζm] xl] [[[l' x₀'] ζm'] xl'] (Hx & Hζ & Hv & Hf). simpl in *.
    injection Hx as -> Hx. naive_solver.
  Qed.
  (** * Lifetimes of a leaf below unique borrows (for reads and writes) *)

  Lemma pctx_ulft_fold {𝔅 𝔄} (K: pctx 𝔅 𝔄) lt :
    pctx_ulfts K ≠ [] → ⊢ pctx_ulft K lt ⊑ ty_lft (lty_fold lt).
  Proof.
    induction K in lt |- *; simpl; try done; [auto|auto|auto|auto| |auto|auto]. intros _.
    iApply llftl_incl_trans; [iApply llftl_intersect_incl_r|]. iApply lty_lft_plug.
  Qed.

  Lemma pctx_uend_ulfts_ne {𝔅 𝔄} (K: pctx 𝔅 𝔄) κ : pctx_uend K = Some κ → pctx_ulfts K ≠ [].
  Proof. intros Hu. have := pctx_uend_ulfts K κ Hu. destruct (pctx_ulfts K); [|done]. by intros ?%not_elem_of_nil. Qed.

  (** * Mutable borrow of the whole referent of a unique borrow below unique borrows

      E.g. [&mut **b] for [b: Box<&mut i32>]: the hole is in [Uniq κ] mode; the borrow at
      [κ] is reborrowed ([uniq_body_reborrow]) and the hole becomes [Blocked] in [Uniq]
      mode ([blocked_uniq]), whose inheritance settles the restored borrow once the
      reborrow has ended. *)

  Lemma pctx_ulft_blft {𝔅 𝔄} (K: pctx 𝔅 𝔄) lt α : ⊢ pctx_ulft K lt ⊓ α ⊑ pctx_blft K α.
  Proof.
    induction K in lt |- *; simpl; [iApply llftl_intersect_incl_r|iApply IHK|iApply IHK|
      iApply IHK|iApply IHK| |iApply IHK|iApply IHK].
    iApply llftl_incl_glb.
    - iApply llftl_incl_trans; [iApply llftl_intersect_incl_l|]. iApply llftl_intersect_incl_l.
    - iApply llftl_incl_trans; [|iApply IHK]. iApply llftl_incl_glb.
      + iApply llftl_incl_trans; [iApply llftl_intersect_incl_l|].
        iApply llftl_incl_trans; [iApply llftl_intersect_incl_r|]. iApply pctx_ulft_incl.
      + iApply llftl_intersect_incl_r.
  Qed.

  Lemma pctx_hmode_uend {𝔅 𝔄} (K: pctx 𝔅 𝔄) κ m : pctx_uend K = Some κ → pctx_hmode K m = 0%nat.
  Proof.
    induction K in m |- *; simpl; [done|auto|auto|auto|auto| |auto|auto].
    destruct K; [done|..]; intros; by apply IHK.
  Qed.

  (** As [uniq_restored_settle], with a guard for the lifetime of the type instead of the
      inclusion of the borrow lifetime in it. *)
  Lemma uniq_restored_settle' {𝔄} (ty: type 𝔄) x₀ ξi ζi κ κ' tid l E G :
    Timeless G → lazyE ⊆ E →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗
    (G &&{↑NllftG}&&> @[ty_lft ty]) -∗
    [†κ'] -∗ £1 -∗ £1 -∗ uniq_restored ty x₀ ξi ζi κ κ' tid l -∗ G ={E}=∗
      ∃ x d g idx, ⧖(S d `max` g) ∗ uniq_body ty x ξi d g idx κ tid l ∗
        ▷ ((λ π, (π (uniq_prvar x₀ ζi)).1) :== vπ x) ∗ G.
  Proof.
    iIntros (? HE) "#LFT #PROPH #UNIQ #Gk #Gty #†κ' £ £' Rst G".
    iDestruct "Rst" as (κp γ γk c wπ idx p lr) "(#Incl & Tok & ⧗ & #Bor & Rst)".
    iMod (lc_fupd_elim_later with "£ Rst") as "(Pc & Gh & %Hw & #Ok & _)".
    have ?: ↑Nllft ⊆ E. { etrans; [|done]. rewrite /lazyE. set_solver. }
    iMod (fractional.frac_split_guard_in_half NllftG G G with "G []")
      as (γh) "[H1 [H2 [#Ghh #Back]]]"; [solve_ndisj|iApply guards_refl|].
    iDestruct (guards_transitive with "Ghh Gk") as "#Gh2".
    iDestruct (guards_transitive with "Ghh Gty") as "#Ght".
    iMod (proph_idx_bor_gen_acc_idx with "LFT UNIQ Gh2 Tok Bor H1") as (wπ') "[Body Close]";
      [done|].
    rewrite /uniq_gbody cpd_body_cell.
    iMod (lc_fupd_elim_later with "£' Body") as "Body".
    iDestruct "Body" as (p' r') "(_ & %Hw' & Gh' & Upd)".
    iDestruct (ghost_var_agree with "Gh Gh'") as %[<- <-]%lstate_inj.
    iMod (guarded_upd_run with "[] H2 Upd") as "[H2 [#⧖ Node]]"; [done| |].
    { iApply "Ght". }
    rewrite leaf_node_inl.
    iDestruct (leaf_owned_unblock _ 0 with "LFT [] Ok †κ' H2 ⧖ Node") as "Upd".
    { iApply "Ght". }
    iMod (fupd_mask_mono with "Upd") as "[H2 (%y & %d' & %g' & Rel & #⧖' & Pt & Gho)]";
      [done|].
    iMod (ghost_var_update_halves (lstate_triv y) with "Gh Gh'") as "[Gh Gh']".
    iSpecialize ("Close" $! (uniq_cell y d' g' γ) (vπ (uniq_cell y d' g' γ))).
    iMod (fupd_mask_mono with "(Close [Gh' Pt Gho])") as "[Tok H1]"; [done| |].
    { iApply (uniq_gbody_triv_close with "Gh'"); [done|].
      iApply uniq_payload_intro_later. iNext. iFrame "∗#". }
    iMod (fupd_mask_mono with "(Back H1 H2)") as "$"; [solve_ndisj|].
    iModIntro. iExists y, d', g', idx. iFrame "⧖'". iSplitL "Gh Tok ⧗".
    { iApply (uniq_body_from_parts with "Incl [Gh Tok] ⧗ [Bor]").
      - rewrite -(uniq_tokγ_retarget y x₀). iFrame.
      - by rewrite (uniq_persγ_retarget _ y x₀). }
    iDestruct (place_rfn_rel_eqz with "Rel") as "Eqz". iNext.
    iApply (uniq_ctrl_eqz_fst with "PROPH Pc").
    iApply (proph_eqz_eq with "Eqz"); [|done]. fun_ext=> π /=. by rewrite Hw.
  Qed.
  (** The reborrow of the whole referent of the innermost borrow (in [Uniq κ] mode). *)
  Lemma type_borrow_vplace_uniq {𝔅 𝔄} E L I p α κ (K: pctx 𝔅 𝔄) `{!PctxNoShr K} `{!PctxVRoot K} (ty: type 𝔅) :
    pctx_uend K = Some κ →
    lctx_lft_alive E L (pctx_ulft K (OfTy ty) ⊓ α) → elctx_sat E L (ty_outlives_E ty α) →
    typed_instr E L I +[p ◁ₗ pctx_plug K (OfTy ty)] (&ᵘ (pctx_vexpr K p))
      (λ w, +[w ◁ᵥ &uniq{pctx_blft K α} ty; p ◁ₗ pctx_plug K (Blocked ty (pctx_blft K α))])
      (λ post '-[x], λ mask π, ∀ m1: ~~ (uniq_borₛ 𝔅),
        uniq_bor_current m1 = pctx_get K x.1 →
        post -[m1; (x.1, (pctx_vpath K, uniq_bor_ξi m1) :: x.2)] mask π).
  Proof.
    intros Hu Alv Out tid post mask iκs [x []].
    iIntros "#LFT #TIME #PROPH #UNIQ #E L I [T _] Obs".
    destruct x as [x₀ ζm].
    rewrite /tctx_elt_interp /borrow_uniq.
    iDestruct "T" as (v Hp) "T". iEval (rewrite vplace_own_open) in "T".
    iDestruct "T" as (D) "(#⧖ & ⧗p & Own)". have Hdl: 1 ≤ pctx_dlev K by apply pctx_vroot_dlev.
    have ?: Closed [] (pctx_vexpr K p).
    { apply pctx_vexpr_closed. by eapply eval_path_closed. }
    iDestruct (Out with "L E") as "#Out".
    iDestruct (elctx_interp_ty_outlives_E with "Out") as "#Incl".
    iDestruct (Alv with "L E") as "#Alv".
    set β := pctx_blft K α.
    have Hκ := pctx_uend_ulfts K κ Hu.
    (* Two steps, for credits and cumulative time receipts. *)
    wp_bind (Seq Skip Skip). wp_bind Skip. iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [set_solver|].
    iIntros "£ #⧖S". wp_let. iModIntro. wp_let. iApply wp_fupd.
    iApply (wp_cumulative_time_receipt_linear with "TIME ⧖S"); [set_solver|].
    iIntros "⧗". wp_let. iModIntro. wp_let.
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_ulft K (OfTy ty)])%I as "#Hu".
    { iApply (guards_transitive with "Ghalf"). iApply (guards_transitive with "Alv").
      iApply llftl_intersect_incl_l. }
    iAssert (fractional.half γh &&{↑NllftG}&&> @[β])%I as "#Hβ".
    { iApply (guards_transitive with "Ghalf"). iApply (guards_transitive with "Alv").
      iApply pctx_ulft_blft. }
    set y := pctx_get K x₀.
    iDestruct (lc_weaken (pctx_vacc_cred K D + (3 * (D + 1) * D + (1 + 1))) with "£")
      as "[£a [£w [£c1 £c2]]]"; [have := pctx_vacc_cred_le K D; rewrite /advance_credits; nia|].
    iMod (vroot_acc K (OfTy ty) with "LFT PROPH UNIQ Hu H1 £a Own")
      as (G' dh gh) "(% & G' & #G'G & -> & %Hdh & H & P & Cl)"; [solve_ndisj|].
    destruct Hdh as (Hdh & Hgh & Hin).
    iEval (rewrite (pctx_kind_uniq K κ) //) in "H".
    iEval (rewrite /pctx_vcloser (pctx_kind_uniq K κ) //) in "Cl".
    set ξi := pctx_hξi K x₀.
    set lK := pctx_vloc K (lty_size (OfTy ty)) x₀.
    iDestruct "H" as (? idx ->) "Body".
    (* The address of the hole. *)
    iApply wp_fupd. wp_bind (pctx_vexpr K p).
    iApply (wp_wand with "[P G' £w]").
    { iApply (wp_pctx_vptrs ⊤ K (lty_size (OfTy ty)) G' x₀ p True%I with "[G'] P").
      iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->". by iFrame. }
    iIntros (w) "(-> & _ & G' & P)". wp_pure _.
    (* The reborrow, and the token of its prophecy variable. *)
    have Hhn: pctx_hmode K 0 + pctx_vne K ≤ pctx_dlev K by apply pctx_vhmode_ne_le.
    iDestruct (cumulative_time_receipt_mono (1 + S (pctx_vne K)) with "⧗") as "⧗"; [lia|].
    iDestruct (cumulative_time_receipt_sep with "⧗") as "[⧗u ⧗e]".
    iMod (uniq_body_reborrow ty y ξi dh gh idx κ β tid lK ⊤ with "LFT PROPH UNIQ [] ⧗u Body")
      as (ζi idx') "[Body' Inh]"; [solve_ndisj| by iApply pctx_blft_incl|].
    set ζ := uniq_prvar y ζi.
    iDestruct "Body'" as (κp' γ') "(#Inclp' & (Gh' & Tok') & ⧗' & #Bor')".
    iMod (proph_idx_bor_gen_tok_acc with "LFT Hβ Tok' Bor' H2") as "[ζtok ζback]";
      [solve_ndisj|].
    iMod ("Cl" $! (Blocked ty β) (inl (PlaceGhost y ζi)) dh gh D [ζ] 1%Qp
      (proph_bor_tok ζ (uniq_cell y dh gh γ') idx' ∗ fractional.half γh)%I
      with "[//] [//] [//] [%] [%] [] ⧖ G' P [ζtok] [ζback Inh £c1 £c2]")
      as "(Own & H1 & Tok' & H2)".
    { intros ζl _. rewrite prfn_rsv_inl. apply place_ghost_rsv_elem. set_solver. }
    { lia. }
    { iRight. iApply pat_ok_blft. }
    { by rewrite big_sepL_singleton. }
    { iIntros "ζtok". rewrite big_sepL_singleton.
      iMod ("ζback" with "ζtok") as "[$ $]".
      iModIntro. rewrite /= /blocked_uniq. iIntros "#†β".
      iMod (fupd_mask_mono with "(Inh †β)") as "Rst"; [rewrite /lazyE; solve_ndisj|].
      iModIntro. iIntros (G0 ?) "#G0g G0".
      iMod (uniq_restored_settle' with "LFT PROPH UNIQ [] [] †β £c1 £c2 Rst G0")
        as (x d' g' idx'') "(#⧖'' & Body & Eqz & $)"; [done| | |].
      { iApply (guards_transitive with "G0g"). iApply llftl_intersect_incl_l. }
      { iApply (guards_transitive with "G0g"). iApply llftl_intersect_incl_r. }
      iModIntro. iExists d', g'. iFrame "⧖''". iExists x, idx''. by iFrame. }
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iModIntro. iExists -[(lK, y, ζi, dh, gh, idx'); (x₀, (pctx_vpath K, ζi) :: ζm)].
    iFrame "L I". iSplit; last first.
    { iApply (proph_obs_impl with "Obs")=> π Hπ. by apply Hπ. }
    iSplitL "Tok' Gh' ⧗'".
    { iExists _. iSplit; [by rewrite eval_path_of_val|]. rewrite -(val_own_intro_sep _ _ _ _ _ D); [|done|done].
      iFrame "⧖".
      iSplit. { iApply llftl_incl_trans; [iApply pctx_blft_incl_r|]. iApply "Incl". }
      iSplit; [iPureIntro; lia|]. iExists κp', γ'. iFrame "∗#". }
    iSplit; [|done]. iExists _. iSplit; [done|].
    iApply (vplace_own_close with "⧖ [⧗p ⧗e]").
    { iDestruct (cumulative_time_receipt_sep with "[$⧗p $⧗e]") as "⧗".
      iApply (cumulative_time_receipt_mono with "⧗"). rewrite !lty_vnrc_plug /=. lia. }
    by rewrite pctx_vrfn_blk_cons /= decide_True.
  Qed.

  (** * The unified mutable borrow

      A mutable borrow of the leaf [OfTy ty] at the hole of [K], on any path of fields, sums,
      owned pointers and unique borrows ([PctxNoShr]: no shared reference and no resolved
      unique borrow on the path; the siblings below a unique borrow are simple), rooted at
      an owned pointer ([p ◁ₗown{n} …]) or a unique borrow value ([PctxVRoot]). The new
      borrow [&uniq{pctx_blft K α} ty] is at the intersection of the enclosing borrow
      lifetimes and [α]; the leaf becomes [Blocked ty (pctx_blft K α)] until [α] ends, and the
      blocking map records the prophecy variable of the new borrow at the path of the hole.
      If the hole is the whole referent of the innermost unique borrow ([pctx_uend K = Some κ],
      e.g. [&mut **x]), that borrow is reborrowed ([type_borrow_vplace_uniq]); otherwise the
      leaf is borrowed in [Owned] mode ([type_borrow_vplace_owned]). *)
  Lemma type_borrow_place_instr {𝔅 𝔄} E L I p (K: pctx 𝔅 𝔄) `{!PctxNoShr K} `{!PctxVRoot K}
      α (ty: type 𝔅) :
    elctx_sat E L (ty_outlives_E ty α) → lctx_lft_alive E L (pctx_ulft K (OfTy ty) ⊓ α) →
    typed_instr E L I +[p ◁ₗ pctx_plug K (OfTy ty)] (&ᵘ (pctx_vexpr K p))
      (λ w, +[w ◁ᵥ &uniq{pctx_blft K α} ty; p ◁ₗ pctx_plug K (Blocked ty (pctx_blft K α))])
      (λ post '-[x], λ mask π, ∀ m1: ~~ (uniq_borₛ 𝔅),
        uniq_bor_current m1 = pctx_get K x.1 →
        post -[m1; (x.1, (pctx_vpath K, uniq_bor_ξi m1) :: x.2)] mask π).
  Proof.
    intros Out Alv. destruct (pctx_uend K) as [κ|] eqn:Hu.
    - by apply (type_borrow_vplace_uniq _ _ _ _ α κ K).
    - by apply (type_borrow_vplace_owned _ _ _ _ α K).
  Qed.

  (** Unblocking the whole referent of the innermost borrow, once [α] has ended: the
      enclosing borrows are opened, the restored borrow is settled
      ([uniq_restored_settle'], in the inheritance of [blocked_uniq]), and the final value
      of the reborrow is observed by sharing the contents of the restored borrow. *)
  Lemma unblock_tctx_vplace_uniq {𝔅 𝔄 𝔄l 𝔄l'} p α κ (K: pctx 𝔅 𝔄) `{!PctxNoShr K} `{!PctxVRoot K} (ty: type 𝔅)
      (T: tctx 𝔄l) (T': tctx 𝔄l') E L f :
    pctx_uend K = Some κ →
    lctx_lft_alive E L (pctx_ulft K (OfTy ty)) → unblock_tctx E L α T T' f →
    unblock_tctx E L α (p ◁ₗ pctx_plug K (Blocked ty (pctx_blft K α)) +:: T)
      (p ◁ₗ pctx_plug K (OfTy ty) +:: T')
      (λ π '(x -:: xl), λ '(x' -:: xl'),
        x'.1 = pctx_set K x.1 (pctx_get K x'.1) ∧ x'.2 = x.2 ∧
        vπ (pctx_get K x'.1) π = vplace_blk_fin K x π ∧ f π xl xl').
  Proof.
    iIntros (Hu Alv Un G tid [x xl] ?) "#LFT #TIME #PROPH #UNIQ #E #L G #†α /=[(%v & %Hp & Own) T]".
    destruct x as [x₀ ζm].
    set β := pctx_blft K α.
    have Hκ := pctx_uend_ulfts K κ Hu. have Hne0 := pctx_uend_ulfts_ne K κ Hu.
    iEval (rewrite vplace_own_open) in "Own". iDestruct "Own" as (D) "(#⧖0 & ⧗ & Own)".
    have Hdl: 1 ≤ pctx_dlev K by apply pctx_vroot_dlev.
    rewrite (lty_vnrc_plug K (Blocked ty β)) /=.
    iDestruct (cumulative_time_receipt_sep with "⧗") as "[⧗r ⧗]".
    have Hhn: pctx_hmode K 0 + pctx_vne K ≤ pctx_dlev K by apply pctx_vhmode_ne_le.
    have Hhn': pctx_dlev K ≤ pctx_hmode K 0 + pctx_vne K + 1 by apply pctx_vhmode_ne_ge.
    rewrite (pctx_hmode_uend K κ) // in Hhn Hhn'.
    have Hne1: 1 ≤ pctx_vne K.
    { destruct (pctx_vne K) eqn:Hz; [|lia]. by apply pctx_vne_ulfts in Hz. }
    set ne := pctx_vne K.
    iDestruct (cumulative_time_receipt_mono (1 + (1 + (ne - 1))) with "⧗") as "⧗"; [lia|].
    iDestruct (cumulative_time_receipt_sep with "⧗") as "[⧗a ⧗]".
    iDestruct (cumulative_time_receipt_sep with "⧗") as "[⧗b ⧗e]".
    leaf_open "L" with "G" as "[L1 back]"; [set_solver|].
    iDestruct (Alv with "L1 E") as "#Lα". iMod ("back" with "L1") as "G".
    (* Half of [G] for the rest of the context, the other half for the place. *)
    iMod (fractional.frac_split_guard_in_half with "G L") as (γ1) "[GT [GP [#GhT #BackT]]]";
      [solve_ndisj|].
    iMod (Un with "LFT TIME PROPH UNIQ E GhT GT †α T") as (dT xl') "[#⧖T ToT']".
    iMod (fractional.frac_split_guard_in_half NllftG (fractional.half γ1) (fractional.half γ1)
      with "GP []") as (γ2) "[H1 [H2 [#Gh2 #Back2]]]"; [solve_ndisj|iApply guards_refl|].
    iAssert (fractional.half γ2 &&{↑NllftG}&&> @[pctx_ulft K (OfTy ty)])%I as "#Hu'".
    { iApply (guards_transitive with "Gh2"). iApply (guards_transitive with "GhT Lα"). }
    iAssert (fractional.half γ2 &&{↑NllftG}&&> @[pctx_ulft K (Blocked ty β)])%I as "#Hu".
    { by rewrite (pctx_ulft_eq K (Blocked ty β) (OfTy ty)). }
    iAssert (fractional.half γ2 &&{↑NllftG}&&> @[κ])%I as "#Hκ".
    { iApply (guards_transitive with "Hu'"). by iApply pctx_ulft_ulfts. }
    iAssert (fractional.half γ2 &&{↑NllftG}&&> @[ty_lft ty])%I as "#Hty".
    { iApply (guards_transitive with "Hu'"). by iApply (pctx_ulft_fold K (OfTy ty)). }
    iDestruct (guards_lft_meet with "Hκ Hty") as "#Hκt".
    (* The credits for the access. *)
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗a ⧖0") as "[_ £a]";
      [solve_ndisj|].
    iDestruct (lc_weaken (pctx_vacc_cred K D) with "£a") as "£a";
      [have := pctx_vacc_cred_le K D; rewrite /advance_credits; nia|].
    iMod (vroot_acc K (Blocked ty β) with "LFT PROPH UNIQ Hu H1 £a Own")
      as (G' dh gh) "(% & G' & #G'G & -> & %Hdh & Hb & P & Cl)"; [solve_ndisj|].
    destruct Hdh as (Hdh & Hgh & Hin).
    iEval (rewrite (pctx_kind_uniq K κ) //) in "Hb".
    iEval (rewrite /pctx_vcloser (pctx_kind_uniq K κ) //) in "Cl".
    set y := pctx_get K x₀. set ζi := blk_lookup ζm (pctx_vpath K).
    (* Unblock: fire the inheritance and settle the restored borrow. *)
    iMod (fupd_mask_mono with "(Hb [])") as "Upd1"; [rewrite /lazyE; solve_ndisj| |].
    { by iApply pctx_blft_dead. }
    iMod (guarded_upd_run with "Hκt H2 Upd1") as "(H2 & %d1 & %g1 & #⧖1 & %y1 & %idx1 & Eqz & Body)";
      [rewrite /lazyE; solve_ndisj|].
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗b ⧖1") as "[#⧖1' £]";
      [solve_ndisj|].
    iDestruct (lc_weaken (1 + (1 + (d1 + d1*(g1+2) + (0 + (d1+1)*(g1+1)) + 1 + 1)))
      with "£") as "[£e [£p £]]"; [rewrite /advance_credits; nia|].
    iSimpl in "Eqz". iMod (lc_fupd_elim_later with "£e Eqz") as "Eqz".
    (* Observe the final value of the reborrow, by sharing the contents. *)
    iMod (fractional.frac_split_guard_in_half NllftG (fractional.half γ2) (fractional.half γ2)
      with "H2 []") as (γ3) "[A [B [#Gh3 #Back3]]]"; [solve_ndisj|iApply guards_refl|].
    iDestruct (guards_transitive with "Gh3 Hκ") as "#Aκ".
    iDestruct (guards_transitive with "Gh3 Hty") as "#Bty".
    iMod (uniq_body_acc with "LFT UNIQ Aκ Body A") as "(Pl & ⧗1 & CloseB)"; [solve_ndisj|].
    iMod (lc_fupd_elim_later with "£p Pl") as "Pl".
    iMod (uniq_payload_run with "Bty B Pl") as "(B & #⧖p & Gho & Pt)"; [solve_ndisj|].
    iMod (proph_eqz_obs_by_share ty with "LFT Bty B £ Eqz Gho") as "(#Obs1 & B & Gho)".
    iSpecialize ("CloseB" $! y1 d1 g1 with "[Pt Gho] ⧗1"). { iNext. iFrame "⧖p Gho Pt". }
    iMod (fupd_mask_mono with "CloseB") as "[Body A]"; [solve_ndisj|].
    iMod (fupd_mask_mono with "(Back3 A B)") as "H2"; [solve_ndisj|].
    iMod (cumulative_persistent_time_receipt with "TIME ⧗e ⧖1'") as "#⧖2"; [solve_ndisj|].
    (* Close the place at the unblocked state, at the maximal depths. *)
    set Dn := D `max` (ne - 1 + S (S d1 `max` g1)).
    iCombine "⧖0 ⧖2" as "⧖D".
    iMod ("Cl" $! (OfTy ty) (inl (PlaceIn y1)) d1 g1 Dn [] 1%Qp True%I
      with "[//] [//] [//] [%] [%] [] [] G' P [] [Body]") as "(Own & H1 & _)".
    { intros ??. apply prfn_rsv_in. }
    { rewrite /Dn. lia. }
    { iRight. iApply pat_ok_ulfts_leaf. }
    { iApply (persistent_time_receipt_mono with "⧖D"). rewrite /Dn. lia. }
    { done. }
    { iIntros "_ !>". iSplit; [|done]. iExists y1, idx1. by iFrame. }
    iMod (fupd_mask_mono with "(Back2 H1 H2)") as "GP"; [solve_ndisj|].
    iModIntro. iExists dT, ((pctx_set K x₀ y1, ζm) -:: xl').
    iSplitR; [done|].
    iMod "ToT'". iModIntro. iNext. iMod "ToT'". iModIntro.
    iApply (step_fupdN_wand with "ToT'"). iIntros ">(GT & T' & #Obs')".
    iMod (fupd_mask_mono with "(BackT GT GP)") as "$"; [solve_ndisj|].
    iModIntro. iSplitR "Obs'".
    { iFrame "T'". iExists _. iSplit; [done|].
      iApply (vplace_own_close K _ _ _ Dn with "[] [⧗r]").
      { iApply (persistent_time_receipt_mono with "⧖D"). rewrite /Dn. lia. }
      { rewrite (lty_vnrc_plug K (OfTy ty)) /=. iApply (cumulative_time_receipt_mono with "⧗r"). lia. }
      by rewrite pctx_get_set pctx_vrfn_set. }
    iCombine "Obs1 Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=> π [Heq Hf].
    split; [by rewrite /= pctx_get_set|]. split; [done|]. split; [|done].
    rewrite /vplace_blk_fin /= pctx_get_set. symmetry. exact Heq.
  Qed.

  Lemma unblock_tctx_oplace_uniq {𝔅 𝔄 𝔄l 𝔄l'} p n α κ (K: pctx 𝔅 𝔄) `{!PctxNoShr K} (ty: type 𝔅)
      (T: tctx 𝔄l) (T': tctx 𝔄l') E L f :
    pctx_uend K = Some κ →
    lctx_lft_alive E L (pctx_ulft K (OfTy ty)) → unblock_tctx E L α T T' f →
    unblock_tctx E L α (p ◁ₗown{n} pctx_plug K (Blocked ty (pctx_blft K α)) +:: T)
      (p ◁ₗown{n} pctx_plug K (OfTy ty) +:: T')
      (λ π '(x -:: xl), λ '(x' -:: xl'),
        x'.1.1 = x.1.1 ∧ x'.1.2 = pctx_set K x.1.2 (pctx_get K x'.1.2) ∧ x'.2 = x.2 ∧
        vπ (pctx_get K x'.1.2) π = oplace_blk_fin K x π ∧ f π xl xl').
  Proof.
    intros. eapply unblock_tctx_impl; [|by apply (unblock_tctx_vplace_uniq _ _ κ (POwn n K))].
    intros π [[[l x₀] ζm] xl] [[[l' x₀'] ζm'] xl'] (Hx & Hζ & Hv & Hf). simpl in *.
    injection Hx as -> Hx. naive_solver.
  Qed.

  (** * Unblocking a shared leaf below unique borrows *)

  (** Unblocking a shared leaf below unique borrows, once [α] has ended (as
      [unblock_tctx_oplace_shr]): the value and the depths do not change; the receipt of
      the leaf (if it is below a unique borrow) pays for opening the enclosing borrows. *)
  Lemma unblock_tctx_vplace_shr_deep {𝔅 𝔄 𝔄l 𝔄l'} p α (K: pctx 𝔅 𝔄) `{!PctxNoShr K} `{!PctxVRoot K} (ty: type 𝔅)
      (T: tctx 𝔄l) (T': tctx 𝔄l') E L f :
    pctx_uend K = None →
    lctx_lft_alive E L (pctx_ulft K (OfTy ty)) → unblock_tctx E L α T T' f →
    unblock_tctx E L α (p ◁ₗ pctx_plug K (ShrBlocked ty (pctx_blft K α)) +:: T)
      (p ◁ₗ pctx_plug K (OfTy ty) +:: T')
      (λ π '(x -:: xl), λ '(x' -:: xl'), x' = x ∧ f π xl xl').
  Proof.
    iIntros (Hu Alv Un G tid [x xl] ?) "#LFT #TIME #PROPH #UNIQ #E #L G #†α /=[(%v & %Hp & Own) T]".
    destruct x as [x₀ ζm].
    set β := pctx_blft K α.
    iEval (rewrite vplace_own_open) in "Own". iDestruct "Own" as (D) "(#⧖0 & ⧗ & Own)".
    have Hdl: 1 ≤ pctx_dlev K by apply pctx_vroot_dlev.
    rewrite (lty_vnrc_plug K (ShrBlocked ty β)) /=.
    iDestruct (cumulative_time_receipt_sep with "⧗") as "[⧗r ⧗]".
    leaf_open "L" with "G" as "[L1 back]"; [set_solver|].
    iDestruct (Alv with "L1 E") as "#Lα". iMod ("back" with "L1") as "G".
    (* Half of [G] for the rest of the context, the other half for the place. *)
    iMod (fractional.frac_split_guard_in_half with "G L") as (γ1) "[GT [GP [#GhT #BackT]]]";
      [solve_ndisj|].
    iMod (Un with "LFT TIME PROPH UNIQ E GhT GT †α T") as (dT xl') "[#⧖T ToT']".
    iAssert (fractional.half γ1 &&{↑NllftG}&&> @[pctx_ulft K (ShrBlocked ty β)])%I as "#Hu".
    { rewrite (pctx_ulft_eq K (ShrBlocked ty β) (OfTy ty)) //.
      iApply (guards_transitive with "GhT Lα"). }
    (* The credits for the access: none below no unique borrow, otherwise from the receipt. *)
    iAssert (|={⊤}=> £(pctx_vacc_cred K D))%I with "[⧗]" as ">£a".
    { destruct (pctx_vne K) as [|ne'] eqn:Hne.
      - rewrite /pctx_vacc_cred (pctx_vne_ulfts K Hne). iApply lc_zero.
      - iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗ ⧖0") as "[_ £]";
          [solve_ndisj|].
        iModIntro. iApply (lc_weaken with "£"). have := pctx_vacc_cred_le K D.
        rewrite /advance_credits. nia. }
    iMod (vroot_acc K (ShrBlocked ty β) with "LFT PROPH UNIQ Hu GP £a Own")
      as (G' dh gh) "(% & G' & #G'G & -> & %Hdh & Hb & P & Cl)"; [solve_ndisj|].
    destruct Hdh as (Hdh & Hgh & Hin).
    iEval (rewrite (pctx_kind_owned K) //) in "Hb".
    iEval (rewrite /pctx_vcloser (pctx_kind_owned K) //) in "Cl".
    iDestruct (unblock_shr_blocked_owned (pctx_hmode K 0) ty β with "[] Hb") as "Hb".
    { by iApply pctx_blft_dead. }
    iMod (fupd_mask_mono with "Hb") as "Hb"; [rewrite /lazyE; solve_ndisj|].
    iMod ("Cl" $! (OfTy ty) (inl (PlaceIn (pctx_get K x₀))) dh gh D [] 1%Qp True%I
      with "[//] [//] [//] [%] [%] [] ⧖0 G' P [] [Hb]") as "(Own & GP & _)".
    { intros ??. apply prfn_rsv_in. }
    { lia. }
    { iRight. iApply pat_ok_ulfts_leaf. }
    { done. }
    { iIntros "_ !>". iSplit; [|done]. iExact "Hb". }
    iModIntro. iExists dT, ((x₀, ζm) -:: xl'). iSplitR; [done|].
    iApply (step_fupd_wand with "ToT'"). iIntros "ToT'".
    iApply (step_fupdN_wand with "ToT'"). iIntros ">(GT & T' & #Obs')".
    iMod (fupd_mask_mono with "(BackT GT GP)") as "$"; [solve_ndisj|].
    iModIntro. iFrame "T'". iSplitR "Obs'".
    { iExists _. iSplit; [done|]. iApply (vplace_own_close with "⧖0 [⧗r]"); [|done].
      rewrite (lty_vnrc_plug K (OfTy ty)) /=. iApply (cumulative_time_receipt_mono with "⧗r"). lia. }
    iApply (proph_obs_impl with "Obs'")=> π Hf. by split.
  Qed.

  Lemma unblock_tctx_oplace_shr_deep {𝔅 𝔄 𝔄l 𝔄l'} p n α (K: pctx 𝔅 𝔄) `{!PctxNoShr K} (ty: type 𝔅)
      (T: tctx 𝔄l) (T': tctx 𝔄l') E L f :
    pctx_uend K = None →
    lctx_lft_alive E L (pctx_ulft K (OfTy ty)) → unblock_tctx E L α T T' f →
    unblock_tctx E L α (p ◁ₗown{n} pctx_plug K (ShrBlocked ty (pctx_blft K α)) +:: T)
      (p ◁ₗown{n} pctx_plug K (OfTy ty) +:: T')
      (λ π '(x -:: xl), λ '(x' -:: xl'), x' = x ∧ f π xl xl').
  Proof. intros. by apply (unblock_tctx_vplace_shr_deep _ _ (POwn n K)). Qed.

End puniq.

(** * Resolving and dropping owned places with nested unique borrows

    [lty_rslv E L lt Φ] generalizes [lty_resolve] (of [place_resolve.v]): the property [Φ]
    may also depend on the blocking map and the path of the place (the denotation of a
    blocked leaf is the final value of its reborrow, recorded in the blocking map). A
    nested unique borrow whose referent has only blocked leaves is resolved by
    pre-resolving its prophecy variable to the denotation of its referent, through its
    reservation ([lty_rslv_uniq_blk], as [tctx_drop_vplace_uniq]); its inner borrows and
    the reborrows of its leaves are kept by their lenders. *)

Definition lty_rslv `{!typeG Σ} {𝔄} (E: elctx) (L: llctx) (lt: lty 𝔄)
    (Φ: ~~𝔄 → blk_map → lpath → proph_asn → Prop) : Prop :=
  ∀ G F m x ζm q d g tid l, Timeless G → ↑Nllft ∪ ↑prophN ∪ ↑timeN ∪ ↑uniqN ⊆ F →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ time_ctx -∗ elctx_interp E -∗
    (G &&{↑NllftG}&&> llctx_interp L) -∗ G -∗
    ltype_own (Owned m) lt (lty_rfn lt x ζm q) d g tid l ={F}=∗
      lty_omem m lt l ∗ |={F}▷=>^(m + d*(g+1)) |={F}=> ⟨π, Φ x ζm q π⟩ ∗ G.

Section lty_rslv.
  Context `{!typeG Σ}.

  Lemma lty_rslv_of {𝔄} E L (lt: lty 𝔄) Φ :
    lty_resolve E L lt Φ → lty_rslv E L lt (λ x _ _, Φ x).
  Proof. intros Rslv ??????????. apply Rslv. Qed.

  Lemma lty_rslv_prod {𝔄1 𝔄2} E L (lt1: lty 𝔄1) (lt2: lty 𝔄2) Φ1 Φ2 :
    lty_rslv E L lt1 Φ1 → lty_rslv E L lt2 Φ2 →
    lty_rslv E L (ProdLty lt1 lt2)
      (λ x ζm q π, Φ1 x.1 ζm (false :: q) π ∧ Φ2 x.2 ζm (true :: q) π).
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

  Lemma lty_rslv_own {𝔄} E L n (lt: lty 𝔄) Φ :
    lty_rslv E L lt Φ → lty_rslv E L (OwnPtrLty n lt) (λ x ζm q π, Φ x.2 ζm (false :: q) π).
  Proof.
    iIntros (Rslv G F m x ζm q d g tid l ??) "LFT PROPH UNIQ TIME E L G Own".
    rewrite /ltype_own /=. destruct x as [l' x]. iDestruct "Own" as "(Pt & %Hd & Fr & Own)".
    iMod (Rslv with "LFT PROPH UNIQ TIME E L G Own") as "[M Upd]"; [done..|].
    iSplitL "Pt Fr M".
    { iModIntro. iExists l'. iFrame "Pt". destruct (own_freeb n lt); [|done]. iFrame. }
    iModIntro. iApply (step_fupdN_nmono with "Upd"). destruct d; [done|]. simpl. nia.
  Qed.

  (** A nested unique borrow whose referent (compound) has only blocked leaves: its
      prophecy variable is pre-resolved through its reservation. *)
  Lemma lty_rslv_uniq_blk {𝔄} E L κ (lt: lty 𝔄) :
    lctx_lft_alive E L κ → lty_is_cpd lt → lty_blk_all lt →
    lty_rslv E L (UniqLty lt κ) (λ x ζm q π,
      (π (uniq_prvar (uniq_bor_current x) (uniq_bor_ξi x))).1 =
        prfn_den (lty_rfn lt (uniq_bor_current x) ζm (false :: q)) π).
  Proof.
    iIntros (Alv Hc Hb G F m x ζm q d g tid l ? HF) "#LFT #PROPH #UNIQ #TIME #E #GL G Own".
    rewrite /ltype_own /= /uniq_node.
    iDestruct "Own" as "(Pt & ⧗ & _ & N)".
    iSplitL "Pt". { iModIntro. by iApply ptr_cell_mem_cell. }
    iModIntro. iApply step_fupdN_add.
    iApply (step_fupdN_wand with "[N]"); [iApply step_fupdN_intro; [done|]; iExact "N"|].
    iIntros "(_ & %d' & %g' & _ & C)". iApply fupd_step_fupdN_front.
    leaf_open "GL" with "G" as "[L back]"; [solve_ndisj|].
    iDestruct (Alv with "L E") as "#Lκ". iMod ("back" with "L") as "G".
    iDestruct (guards_transitive with "GL Lκ") as "#Gκ".
    rewrite ltype_own_cp_uniq_cpd //.
    iDestruct "C" as (x₀' κp γ γf idx' ζl) "(#Inclp & %Hr & Tok & Gh & Tf & ⧗o & #Bor)".
    set r : prfn 𝔄 := lty_rfn lt (uniq_bor_current x) ζm (false :: q).
    set uπ : proph (uniq_cellₛ 𝔄) :=
      λ π, (prfn_den r π, (1%positive, (1%positive, 1%positive))).
    have Hdep: uπ ./ ζl.
    { apply (proph_dep_constr (λ a, (a, (1%positive, (1%positive, 1%positive))))).
      by apply lty_blk_all_dep. }
    iMod (proph_idx_bor_gen_preresolve_rsv F κ (uniq_prvar x₀' (uniq_bor_ξi x))
      (uniq_cell x₀' d' g' γ) idx' ζl _ uπ G with "LFT PROPH UNIQ Gκ [Gh Tf] G Tok Bor")
      as "[#Obs' G]"; [solve_ndisj|done| |].
    { iIntros (wπ) "Body". iNext.
      iDestruct "Body" as "[Body|[Tf' _]]"; [|iDestruct (cpd_tok_excl with "Tf Tf'") as "[]"].
      iLeft. rewrite !cpd_body_cell. iDestruct "Body" as (p1 r1) "(Ok & % & Gh' & Upd)".
      iDestruct (ghost_var_agree with "Gh Gh'") as %[<- <-]%lstate_inj.
      iExists _, _. by iFrame. }
    iModIntro. iApply step_fupdN_full_intro. iModIntro. iFrame "G".
    iApply (proph_obs_impl with "Obs'")=> π Heq.
    by rewrite (uniq_prvar_app_irrel (uniq_bor_current x) x₀') Heq.
  Qed.
End lty_rslv.

Section oplace_rslv.
  Context `{!typeG Σ}.

  Lemma oplace_rslv_steps {𝔄} E L n (lt: lty 𝔄) Φ x tid v :
    lty_rslv E L lt Φ →
    oplace_own n lt x tid v -∗ ∃ D, ⧖D ∗ ∀ G F, ⌜Timeless G⌝ -∗
      ⌜↑Nllft ∪ ↑prophN ∪ ↑timeN ∪ ↑uniqN ⊆ F⌝ -∗
      llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ time_ctx -∗ elctx_interp E -∗
      (G &&{↑NllftG}&&> llctx_interp L) -∗ G ={F}=∗
        |={F}▷=>^(D*(D+1)) |={F}=> ⟨π, Φ x.1.2 x.2 [] π⟩ ∗ G.
  Proof.
    iIntros (Rslv) "Own". destruct x as [[l x₀] ζm].
    iDestruct "Own" as (D d g) "(⧖ & _ & _ & %Hle & _ & Own)".
    iExists D. iFrame "⧖". iIntros (G F ??) "LFT PROPH UNIQ TIME E L G".
    iMod (Rslv with "LFT PROPH UNIQ TIME E L G Own") as "[_ Upd]"; [done..|].
    iModIntro. iApply (step_fupdN_nmono with "Upd"). nia.
  Qed.

  Lemma resolve_tctx_cons_oplace_deep {𝔄 𝔅l} E L p n (lt: lty 𝔄) Φ (T: tctx 𝔅l) Ψ :
    lty_rslv E L lt Φ → resolve_tctx E L T Ψ →
    resolve_tctx E L (p ◁ₗown{n} lt +:: T) (λ '(x -:: bl) π φ, Φ x.1.2 x.2 [] π → Ψ bl π φ).
  Proof.
    iIntros (Rslv Rslv' G F tid [x xl] ? HF).
    iIntros "#LFT #PROPH #UNIQ #TIME #E #L G /=[(%v & _ & Own) T]".
    iMod (fractional.frac_split_guard_in_half NllftG with "G L")
      as (γ) "[F1 [F2 [#guards #back]]]"; [solve_ndisj|].
    iDestruct (oplace_rslv_steps with "Own") as (D) "[⧖ ToObs]"; [done|].
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

  Lemma type_drop_oplace_deep_instr {𝔄} E L I p n (nz: Z) (lt: lty 𝔄) Φ :
    lty_freeb lt = true → n = lty_size lt → nz = Z.of_nat n → lty_rslv E L lt Φ →
    typed_instr E L I +[p ◁ₗown{n} lt] (drop_boxes lt (ToLit p);; new_delete.delete [ #nz; ToLit p])%E
      (λ _, +[]) (λ post '-[x], λ mask π, Φ x.1.2 x.2 [] π → post -[] mask π).
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
    wp_bind (drop_boxes lt (ToLit p)).
    have Hev: ⊢ ∀ Ψ (P: iProp Σ), True -∗ ▷^0 P -∗ (True -∗ P -∗ Ψ #l) -∗
      WP ToLit p @ ⊤∖↑advN {{ Ψ }}.
    { iIntros (Ψ P) "_ P HΨ". wp_bind p. iApply wp_wand; [by iApply wp_eval_path|].
      iIntros (?) "->". wp_pure _. by iApply ("HΨ" with "[//] P"). }
    iApply (wp_drop_boxes lt 1 0 l (ToLit p) True%I (⊤∖↑advN) _ ltac:(solve_ndisj) Hf _
      ltac:(lia) Hev with "[//] M").
    iIntros "_ (%bs & Pt & %Hl)". wp_seq.
    wp_bind p. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->". wp_pure _.
    iEval (rewrite freeable_sz_full) in "Fr".
    iApply (wp_delete_fbytes bs with "[Pt Fr]"); [solve_ndisj|by rewrite Hl|..].
    { iFrame "Pt". rewrite Hl. iDestruct "Fr" as "[$|%]"; by iRight. }
    iIntros "!> _". iExists -[]. iFrame "L I". iSplit; [done|].
    iCombine "Obs Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=>/= ?[Imp ?]. by apply Imp.
  Qed.
End oplace_rslv.
