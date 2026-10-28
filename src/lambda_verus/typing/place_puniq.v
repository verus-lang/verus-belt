(** * Owned places below unique borrows

  The operations on places rooted at an owned location ([p ◁ₗown{n} …], [place_own.v]) at
  a hole below any number of unique borrows ([PUniq] steps of the context, interleaved
  with fields, owned pointers and sums), through the access of [pctx_acc.v]: the enclosing
  borrows are opened (with the credits of a program step, bounded by the depth of the
  place) and closed again with the new hole, extending their reservations by the new
  prophecy variables of the hole.

  - [type_change_oplace_instr]: change the place type at the hole by a conversion
    ([oplace_conv]) at the mode of the hole ([pctx_kind]: [Owned], or [Uniq] if the hole is
    the whole referent of the innermost borrow). Instances: unfolding and folding a unique
    borrow ([OfTy (&uniq{κ'} ty)] ↔ [UniqLty (OfTy ty) κ']) and a pair, at both modes.

  See [~/verus-belt-phase3-design.md], section "PUniq". *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From lrust.lang Require Import proofmode.
From lrust.typing Require Export type ltype lpath pctx_acc place_own.
From lrust.typing Require Import type_context programs programs_util lft_contexts
  uniq_util uniq_bor product own place.
From lrust.util Require Import proph_bor.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section puniq.
  Context `{!typeG Σ}.

  Lemma pctx_uend_ulfts {𝔅 𝔄} (K: pctx 𝔅 𝔄) κ : pctx_uend K = Some κ → κ ∈ pctx_ulfts K.
  Proof.
    induction K; simpl; try done; [auto..|].
    destruct K; [intros [= ->]; set_solver|..]; intros; apply elem_of_cons; right; by apply IHK.
  Qed.

  Lemma pctx_hmode_le {𝔅 𝔄} (K: pctx 𝔅 𝔄) m : pctx_hmode K m ≤ m + pctx_dlev K.
  Proof.
    induction K in m |- *; simpl; [lia|apply IHK|apply IHK| |apply IHK|];
      [specialize (IHK (m + 1))|specialize (IHK 0)]; lia.
  Qed.

  Lemma typed_instr_tr_impl {𝔄l 𝔅l} E L I (T: tctx 𝔄l) e (T': val → tctx 𝔅l) tr tr' :
    (∀ post xl mask π, tr' post xl mask π → tr post xl mask π) →
    typed_instr E L I T e T' tr → typed_instr E L I T e T' tr'.
  Proof.
    iIntros (Himp Hty tid post mask iκs xl) "LFT TIME PROPH UNIQ E L I T Obs".
    iApply (Hty with "LFT TIME PROPH UNIQ E L I T"). iApply (proph_obs_impl with "Obs").
    intros π. apply Himp.
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
  Definition oplace_conv {𝔅 𝔄} (K: pctx 𝔅 𝔄) (lt lt': lty 𝔅) (f: ~~𝔅 → ~~𝔅 → Prop) : Prop :=
    ∀ (x: ~~𝔄) ζm dh gh D tid lh (G: iProp Σ) E, Timeless G → lazyE ∪ ↑timeN ⊆ E →
      pctx_dlev K < D → dh < D →
    ⊢ llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ time_ctx -∗
      (G &&{↑NllftG}&&> @[pctx_ulft K lt ⊓ ty_lft (lty_fold lt)]) -∗ G -∗
      ⧖D -∗ £(D + 1) -∗ ⧗(D + 2) -∗
      ltype_own_cp false lt (pctx_kind K (Owned 1) x) (lty_pat lt)
        (lty_rfn lt (pctx_get K x) ζm (pctx_path K [])) dh gh tid lh ={E}=∗
      ∃ y' ζl' (q: Qp), ⌜f (pctx_get K x) y'⌝ ∗
        ⌜∀ ζl, prfn_rsv (lty_rfn lt (pctx_get K x) ζm (pctx_path K [])) ζl →
          prfn_rsv (lty_rfn lt' y' ζm (pctx_path K [])) (ζl ++ ζl')⌝ ∗
        q:+[ζl'] ∗ (q:+[ζl'] ={E}=∗
          ltype_own_cp false lt' (pctx_kind K (Owned 1) x) (lty_pat lt')
            (lty_rfn lt' y' ζm (pctx_path K [])) dh gh tid lh ∗ G).

  Lemma type_change_oplace_instr {𝔅 𝔄} E L I p n (K: pctx 𝔅 𝔄) (lt lt': lty 𝔅) f :
    lctx_lft_alive E L (pctx_ulft K lt ⊓ ty_lft (lty_fold lt)) →
    lty_fold lt' = lty_fold lt → lty_size lt' = lty_size lt → lty_nrc lt' = lty_nrc lt →
    pat_blk_lfts (lty_pat lt') = [] → oplace_conv K lt lt' f →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K lt] (Seq Skip Skip)
      (const +[p ◁ₗown{n} pctx_plug K lt'])
      (λ post '-[x], λ mask π, ∀ x', x'.1.1 = x.1.1 → x'.2 = x.2 → pctx_in K x.1.2 →
        (∃ y', f (pctx_get K x.1.2) y' ∧ x'.1.2 = pctx_set K x.1.2 y') → post -[x'] mask π).
  Proof.
    intros Alv Hf Hsz Hnrc Hp Hconv tid post mask iκs [x []].
    iIntros "#LFT #TIME #PROPH #UNIQ #E L I [T _] Obs".
    destruct x as [[l x₀] ζm].
    rewrite /tctx_elt_interp.
    iDestruct "T" as (v Hpv D d g) "(#⧖ & ⧗p & -> & %Hle & Fr & Own)".
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
    rewrite /ltype_own lty_pat_plug lty_rfn_plug.
    iDestruct (lc_weaken (pctx_acc_cred K 1 d + (D + 1)) with "£") as "[£a £c]";
      [have := pctx_acc_cred_le K 1 d; rewrite /advance_credits; nia|].
    iMod (pctx_acc K lt 1 with "LFT PROPH UNIQ Hu H1 £a Own")
      as (G' dh gh) "(% & G' & #G'G & %Hdh & H & P & #Gs & #HG & Cl)"; [solve_ndisj|].
    destruct Hdh as (Hdh & Hgh & Hin).
    iDestruct (cumulative_time_receipt_mono (D + 2) with "⧗") as "⧗"; [lia|].
    iMod (Hconv x₀ ζm dh gh D tid _ (fractional.half γh) with "LFT PROPH UNIQ TIME Hα H2 ⧖ £c ⧗ H")
      as (y' ζl' q Hfy Hrsv) "[toks VS]"; [solve_ndisj|lia|lia|].
    iMod ("Cl" $! lt' (lty_pat lt') (lty_rfn lt' y' ζm (pctx_path K [])) dh gh d g ζl' q
      (fractional.half γh) with "[//] [//] [//] [%] [] [] G' P toks VS") as "(Own & H1 & H2)".
    { lia. }
    { by iApply big_sepL_pat_ok_nil. }
    { iApply (persistent_time_receipt_mono with "⧖"). lia. }
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iModIntro. iExists -[((l, pctx_set K x₀ y'), ζm)]. iFrame "L I". iSplit; last first.
    { iApply (proph_obs_impl with "Obs")=> π Hπ. apply Hπ; [done..|]. by eexists. }
    iSplit; [|done]. rewrite /tctx_elt_interp. iExists #l. iSplit; [done|].
    iExists D, d, g. iFrame "⧖".
    rewrite (lty_nrc_plug_eq K lt lt' Hnrc) (lty_size_plug_eq K lt' lt) //. iFrame "⧗p Fr".
    iSplit; [done|]. iSplit; [done|].
    rewrite /ltype_own lty_pat_plug lty_rfn_plug pctx_get_set pctx_rfn_set //.
  Qed.

  (** ** Pairs *)

  Lemma oplace_conv_prod_unfold {𝔅1 𝔅2 𝔄} (K: pctx (𝔅1 * 𝔅2) 𝔄) (ty1: type 𝔅1) (ty2: type 𝔅2) :
    oplace_conv K (OfTy (ty1 * ty2)) (ProdLty (OfTy ty1) (OfTy ty2)) (=).
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

  Lemma oplace_conv_prod_fold {𝔅1 𝔅2 𝔄} (K: pctx (𝔅1 * 𝔅2) 𝔄) (ty1: type 𝔅1) (ty2: type 𝔅2) :
    oplace_conv K (ProdLty (OfTy ty1) (OfTy ty2)) (OfTy (ty1 * ty2)) (=).
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

  Lemma type_unfold_oplace_prod_instr {𝔅1 𝔅2 𝔄} E L I p n (K: pctx (𝔅1 * 𝔅2) 𝔄)
      (ty1: type 𝔅1) (ty2: type 𝔅2) :
    lctx_lft_alive E L (pctx_ulft K (OfTy (ty1 * ty2)) ⊓ ty_lft (prod_ty ty1 ty2)) →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K (OfTy (ty1 * ty2))] (Seq Skip Skip)
      (const +[p ◁ₗown{n} pctx_plug K (ProdLty (OfTy ty1) (OfTy ty2))])
      (λ post '-[x], post -[x]).
  Proof.
    intros Alv. eapply typed_instr_tr_impl;
      [|apply (type_change_oplace_instr _ _ _ _ _ K _ _ (=)); [done..|apply oplace_conv_prod_unfold]].
    intros post [[[l x₀] ζm] []] mask π Hπ [[l' x₀'] ζm'] Hl Hζ Hin (y' & <- & Hx).
    simpl in *. subst. by rewrite pctx_set_get.
  Qed.

  Lemma type_fold_oplace_prod_instr {𝔅1 𝔅2 𝔄} E L I p n (K: pctx (𝔅1 * 𝔅2) 𝔄)
      (ty1: type 𝔅1) (ty2: type 𝔅2) :
    lctx_lft_alive E L (pctx_ulft K (ProdLty (OfTy ty1) (OfTy ty2)) ⊓ ty_lft (prod_ty ty1 ty2)) →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K (ProdLty (OfTy ty1) (OfTy ty2))] (Seq Skip Skip)
      (const +[p ◁ₗown{n} pctx_plug K (OfTy (ty1 * ty2))])
      (λ post '-[x], post -[x]).
  Proof.
    intros Alv. eapply typed_instr_tr_impl;
      [|apply (type_change_oplace_instr _ _ _ _ _ K _ _ (=)); [done..|apply oplace_conv_prod_fold]].
    intros post [[[l x₀] ζm] []] mask π Hπ [[l' x₀'] ζm'] Hl Hζ Hin (y' & <- & Hx).
    simpl in *. subst. by rewrite pctx_set_get.
  Qed.
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
  Lemma oplace_conv_uniq_unfold_own {𝔅 𝔄} (K: pctx (uniq_borₛ 𝔅) 𝔄) (ty: type 𝔅) κ' :
    pctx_uend K = None →
    oplace_conv K (OfTy (&uniq{κ'} ty)) (UniqLty (OfTy ty) κ') (=).
  Proof.
    iIntros (Hu x ζm dh gh D tid lh G E ? HE HdK ?) "#LFT #PROPH #UNIQ #TIME #Gk G ⧖ £ ⧗ H".
    rewrite (pctx_kind_owned K) //. have Hm := pctx_hmode_le K 1.
    set mh := pctx_hmode K 1.
    destruct (pctx_get K x) as [[[[[l' y] ξi'] d1] g1] idx'] eqn:Hy.
    iDestruct "H" as (? ->) "[Pt Gho]".
    iDestruct (lc_weaken mh with "£") as "£"; [lia|].
    iMod (lc_fupd_elim_laterN with "£ Gho") as "(#Incl' & %Hle1 & Body1 & #Gpt)".
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
    iApply bi.laterN_intro. iFrame "Incl' Gpt". iSplit; [done|]. iExists κp', γ'. rewrite /uniq_bodyγ /uniq_tokγ. by iFrame "∗#".
  Qed.

  (** Unfolding a unique borrow at a hole in [Uniq κ] mode (the referent of the innermost
      enclosing borrow is the unique borrow): the enclosing borrow is switched to the node
      of [UniqLty], and reserved for the prophecy variable of the unfolded borrow (as
      [type_unfold_place_uniq_instr]). *)
  Lemma oplace_conv_uniq_unfold_uniq {𝔅 𝔄} (K: pctx (uniq_borₛ 𝔅) 𝔄) (ty: type 𝔅) κ κ' :
    pctx_uend K = Some κ →
    oplace_conv K (OfTy (&uniq{κ'} ty)) (UniqLty (OfTy ty) κ') (=).
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
    iAssert (fractional.half γh &&{↑NllftG}&&> @[ty_lft (uniq_bor κ' ty)])%I as "#Hty".
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
    iDestruct "Gho" as "(#Incl' & %Hle1 & Body1 & #Gpt)".
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
      rewrite /node /= /uniq_node. iFrame "Pt TIME Incl' Gpt".
      iSplitL "⧗". { iApply (cumulative_time_receipt_mono with "⧗"). lia. }
      iExists d1, g1. iSplit; [done|]. iExists y, idx'. iSplit; [done|].
      iExists κp', γ'. rewrite /uniq_bodyγ /uniq_tokγ. by iFrame "∗#". }
    iMod (fupd_mask_mono with "(Back H1 H2)") as "$"; [done|].
    iModIntro. rewrite /= /cpd_own. iExists v, κp, γ, γf, idx'', [uniq_prvar y ξi'].
    iFrame "∗#". iPureIntro. by apply (prfn_rsv_uniq_leaf _ _ _ []).
  Qed.

  Lemma oplace_conv_uniq_unfold {𝔅 𝔄} (K: pctx (uniq_borₛ 𝔅) 𝔄) (ty: type 𝔅) κ' :
    oplace_conv K (OfTy (&uniq{κ'} ty)) (UniqLty (OfTy ty) κ') (=).
  Proof.
    destruct (pctx_uend K) as [κ|] eqn:Hu;
      [by eapply oplace_conv_uniq_unfold_uniq|by apply oplace_conv_uniq_unfold_own].
  Qed.

  (** Folding back a unique borrow whose referent is a leaf, in [Owned] mode. The depths
      and the index of the value of the borrow change. *)
  Lemma oplace_conv_uniq_fold_own {𝔅 𝔄} (K: pctx (uniq_borₛ 𝔅) 𝔄) (ty: type 𝔅) κ' :
    pctx_uend K = None →
    oplace_conv K (UniqLty (OfTy ty) κ') (OfTy (&uniq{κ'} ty))
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
  Lemma oplace_conv_uniq_fold_uniq {𝔅 𝔄} (K: pctx (uniq_borₛ 𝔅) 𝔄) (ty: type 𝔅) κ κ' :
    pctx_uend K = Some κ →
    oplace_conv K (UniqLty (OfTy ty) κ') (OfTy (&uniq{κ'} ty))
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
    iAssert (fractional.half γh &&{↑NllftG}&&> @[ty_lft (uniq_bor κ' ty)])%I as "#Hty".
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
    iDestruct "N" as "(Pt & _ & _ & #Incl' & #Gpt & %d2 & %g2 & %Hle2 & C)".
    iDestruct "C" as (y0 idx1 ->) "Body1".
    set v' : ~~ (uniq_borₛ 𝔅) := (l', y, ξi', d2, g2, idx1).
    iMod (ghost_var_update_halves (lstate_triv v') with "Gh Gh'") as "[Gh Gh']".
    iSpecialize ("Close" $! (uniq_cell v' dh gh γ) (vπ (uniq_cell v' dh gh γ))).
    iMod (fupd_mask_mono with "(Close [Gh' Pt Body1] [Tf])") as (idx2) "(Tok & #Bor' & H1)";
      [solve_ndisj| | |].
    { iApply (uniq_gbody_triv_close with "Gh'"); [done|]. iNext.
      iApply (uniq_payload_intro (&uniq{κ'} ty) tid lh v' dh gh with "⧖' [Body1] Pt").
      iFrame "Incl' Body1 Gpt". iPureIntro. lia. }
    { iIntros "!>" (c2 w2) "P". iModIntro. iNext. iRight. iFrame. }
    iMod (fupd_mask_mono with "(Back H1 H2)") as "G"; [done|].
    iModIntro. iExists v', [], 1%Qp. iSplit; [by iExists d2, g2, idx1|].
    iSplit; [iPureIntro; intros ??; apply prfn_rsv_in|]. iSplitR; [done|]. iIntros "_ !>".
    iFrame "G". rewrite /= /ofty_uniq. iExists v', idx2. iSplit; [done|].
    iApply (uniq_body_from_parts with "Inclp [Gh Tok] ⧗o [Bor']").
    - rewrite /uniq_tokγ (uniq_bor_tok_retarget _ x₀w). iFrame.
    - by rewrite /uniq_persγ (uniq_idx_bor_gen_retarget _ _ x₀w).
  Qed.

  Lemma oplace_conv_uniq_fold {𝔅 𝔄} (K: pctx (uniq_borₛ 𝔅) 𝔄) (ty: type 𝔅) κ' :
    oplace_conv K (UniqLty (OfTy ty) κ') (OfTy (&uniq{κ'} ty))
      (λ y y', ∃ d g idx, y' = uniq_bor_set_meta y d g idx).
  Proof.
    destruct (pctx_uend K) as [κ|] eqn:Hu;
      [by eapply oplace_conv_uniq_fold_uniq|by apply oplace_conv_uniq_fold_own].
  Qed.

  (** Unfolding the unique borrow at the hole of [K] (at any path, also below other unique
      borrows) into a nested place. *)
  Lemma type_unfold_oplace_uniq_instr {𝔅 𝔄} E L I p n (K: pctx (uniq_borₛ 𝔅) 𝔄) (ty: type 𝔅) κ' :
    lctx_lft_alive E L (pctx_ulft K (OfTy (&uniq{κ'} ty)) ⊓ ty_lft (uniq_bor κ' ty)) →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K (OfTy (&uniq{κ'} ty))] (Seq Skip Skip)
      (const +[p ◁ₗown{n} pctx_plug K (UniqLty (OfTy ty) κ')])
      (λ post '-[x], post -[x]).
  Proof.
    intros Alv. eapply typed_instr_tr_impl;
      [|apply (type_change_oplace_instr _ _ _ _ _ K _ _ (=)); [done..|apply oplace_conv_uniq_unfold]].
    intros post [[[l x₀] ζm] []] mask π Hπ [[l' x₀'] ζm'] Hl Hζ Hin (y' & <- & Hx).
    simpl in *. subst. by rewrite pctx_set_get.
  Qed.

  (** Folding it back. *)
  Lemma type_fold_oplace_uniq_instr {𝔅 𝔄} E L I p n (K: pctx (uniq_borₛ 𝔅) 𝔄) (ty: type 𝔅) κ' :
    lctx_lft_alive E L (pctx_ulft K (UniqLty (OfTy ty) κ') ⊓ ty_lft (uniq_bor κ' ty)) →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K (UniqLty (OfTy ty) κ')] (Seq Skip Skip)
      (const +[p ◁ₗown{n} pctx_plug K (OfTy (&uniq{κ'} ty))])
      (λ post '-[x], λ mask π, ∀ d g idx,
        post -[((x.1.1, pctx_set K x.1.2 (uniq_bor_set_meta (pctx_get K x.1.2) d g idx)), x.2)]
          mask π).
  Proof.
    intros Alv. eapply typed_instr_tr_impl;
      [|apply (type_change_oplace_instr _ _ _ _ _ K _ _ (λ y y', ∃ d g idx, y' = uniq_bor_set_meta y d g idx)); [done..|apply oplace_conv_uniq_fold]].
    intros post [[[l x₀] ζm] []] mask π Hπ [[l' x₀'] ζm'] Hl Hζ Hin (y' & (d & g & idx & ->) & Hx).
    simpl in *. subst. apply Hπ.
  Qed.
  (** ** Owned pointers (in [Owned] mode; the laters in front of the pointee are stripped
      with the credits of the step) *)

  Lemma oplace_conv_own_unfold {𝔅 𝔄} (K: pctx (at_locₛ 𝔅) 𝔄) n (ty: type 𝔅) :
    pctx_uend K = None →
    oplace_conv K (OfTy (own_ptr n ty)) (OwnPtrLty n (OfTy ty)) (=).
  Proof.
    iIntros (Hu x ζm dh gh D tid lh G E ? HE HdK ?) "_ _ _ _ _ G _ £ _ H".
    rewrite (pctx_kind_owned K) //. have Hm := pctx_hmode_le K 1. set mh := pctx_hmode K 1.
    destruct (pctx_get K x) as [l' y] eqn:Hy.
    iDestruct "H" as (? ->) "[Pt Gho]".
    iDestruct (lc_weaken mh with "£") as "£"; [lia|].
    iMod (lc_fupd_elim_laterN with "£ Gho") as "Gho".
    destruct dh as [|dh']; [done|]. iDestruct "Gho" as "(Pt' & Fr' & Gho)".
    iModIntro. iExists (l', y), [], 1%Qp. iSplit; [done|].
    iSplit; [iPureIntro; intros ??; apply prfn_rsv_in|]. iSplitR; [done|]. iIntros "_ !>".
    iFrame "G". rewrite /= /own_node. iFrame "Pt". iSplit; [done|].
    iSplitL "Fr'"; [by iApply bi.laterN_intro|].
    iExists y. iSplit; [done|]. rewrite /ofty_owned.
    iEval (rewrite (heap_cloc_mapsto_fancy_empty l' (ty_phys ty y tid)) ty_size_eq) in "Pt'".
    iFrame "Pt'". rewrite Nat.add_1_r /=. iNext. by iApply bi.laterN_intro.
  Qed.

  Lemma oplace_conv_own_fold {𝔅 𝔄} (K: pctx (at_locₛ 𝔅) 𝔄) n (ty: type 𝔅) :
    pctx_uend K = None →
    oplace_conv K (OwnPtrLty n (OfTy ty)) (OfTy (own_ptr n ty)) (=).
  Proof.
    iIntros (Hu x ζm dh gh D tid lh G E ? HE HdK ?) "_ _ _ _ _ G _ _ _ H".
    rewrite (pctx_kind_owned K) //.
    destruct (pctx_get K x) as [l' y] eqn:Hy.
    iModIntro. iExists (l', y), [], 1%Qp. iSplit; [done|].
    iSplit; [iPureIntro; intros ??; apply prfn_rsv_in|]. iSplitR; [done|]. iIntros "_ !>".
    iFrame "G". by iApply (ownptr_ofty_fold_own with "H").
  Qed.

  Lemma type_unfold_oplace_own_deep_instr {𝔅 𝔄} E L I p n' (K: pctx (at_locₛ 𝔅) 𝔄) n (ty: type 𝔅) :
    pctx_uend K = None →
    lctx_lft_alive E L (pctx_ulft K (OfTy (own_ptr n ty)) ⊓ ty_lft (own_ptr n ty)) →
    typed_instr E L I +[p ◁ₗown{n'} pctx_plug K (OfTy (own_ptr n ty))] (Seq Skip Skip)
      (const +[p ◁ₗown{n'} pctx_plug K (OwnPtrLty n (OfTy ty))])
      (λ post '-[x], post -[x]).
  Proof.
    intros Hu Alv. eapply typed_instr_tr_impl;
      [|apply (type_change_oplace_instr _ _ _ _ _ K _ _ (=)); [done..|by apply oplace_conv_own_unfold]].
    intros post [[[l x₀] ζm] []] mask π Hπ [[l' x₀'] ζm'] Hl Hζ Hin (y' & <- & Hx).
    simpl in *. subst. by rewrite pctx_set_get.
  Qed.

  Lemma type_fold_oplace_own_deep_instr {𝔅 𝔄} E L I p n' (K: pctx (at_locₛ 𝔅) 𝔄) n (ty: type 𝔅) :
    pctx_uend K = None →
    lctx_lft_alive E L (pctx_ulft K (OwnPtrLty n (OfTy ty)) ⊓ ty_lft (own_ptr n ty)) →
    typed_instr E L I +[p ◁ₗown{n'} pctx_plug K (OwnPtrLty n (OfTy ty))] (Seq Skip Skip)
      (const +[p ◁ₗown{n'} pctx_plug K (OfTy (own_ptr n ty))])
      (λ post '-[x], post -[x]).
  Proof.
    intros Hu Alv. eapply typed_instr_tr_impl;
      [|apply (type_change_oplace_instr _ _ _ _ _ K _ _ (=)); [done..|by apply oplace_conv_own_fold]].
    intros post [[[l x₀] ζm] []] mask π Hπ [[l' x₀'] ζm'] Hl Hζ Hin (y' & <- & Hx).
    simpl in *. subst. by rewrite pctx_set_get.
  Qed.
  (** * Mutable borrow of a leaf below unique borrows *)

  Lemma pctx_hmode_ne {𝔅 𝔄} (K: pctx 𝔅 𝔄) m e mm :
    pctx_hmode K m + pctx_ne K e mm =
      pctx_dlev K + e + (match pctx_ulfts K with [] => m | _ => mm end).
  Proof.
    induction K in m, e, mm |- *; simpl; [lia|auto|auto| |auto|].
    - rewrite IHK. destruct (pctx_ulfts K); lia.
    - rewrite IHK. destruct (pctx_ulfts K); lia.
  Qed.

  (** A mutable borrow of the leaf at the hole of [K] (in [Owned] mode, at any path, below
      any number of unique borrows), at a lifetime [α] that the type of the leaf outlives.
      The new borrow is at [pctx_blft K α], the intersection of the enclosing borrow
      lifetimes and [α] ([α] if there is none, as [type_borrow_oplace_instr]); its fresh
      prophecy variable extends the reservations of all enclosing borrows. *)
  Lemma type_borrow_oplace_deep_instr {𝔅 𝔄} E L I p n α (K: pctx 𝔅 𝔄) (ty: type 𝔅) :
    pctx_uend K = None →
    lctx_lft_alive E L (pctx_ulft K (OfTy ty)) → elctx_sat E L (ty_outlives_E ty α) →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K (OfTy ty)] (Seq (Seq Skip Skip) (pctx_expr K p))
      (λ w, +[w ◁ &uniq{pctx_blft K α} ty; p ◁ₗown{n} pctx_plug K (Blocked ty (pctx_blft K α))])
      (λ post '-[x], λ mask π, ∀ m1: ~~ (uniq_borₛ 𝔅),
        uniq_bor_current m1 = pctx_get K x.1.2 →
        post -[m1; (x.1, (pctx_path K [], uniq_bor_ξi m1) :: x.2)] mask π).
  Proof.
    intros Hu Alv Out tid post mask iκs [x []].
    iIntros "#LFT #TIME #PROPH #UNIQ #E L I [T _] Obs".
    destruct x as [[l x₀] ζm].
    rewrite /tctx_elt_interp.
    iDestruct "T" as (v Hp D d g) "(#⧖ & ⧗p & -> & %Hle & Fr & Own)".
    have ?: Closed [] (pctx_expr K p).
    { apply pctx_expr_closed. by eapply eval_path_closed. }
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
    { iApply (guards_transitive with "Ghalf Alv"). }
    rewrite /ltype_own lty_pat_plug lty_rfn_plug.
    set lr := (l, repeat [] (lty_size (pctx_plug K (OfTy ty)))).
    set y := pctx_get K x₀.
    iDestruct (lc_weaken (pctx_acc_cred K 1 d + (D + (3 * (g + 1) * D + 1))) with "£")
      as "[£a [£k [£w £c]]]"; [have := pctx_acc_cred_le K 1 d; rewrite /advance_credits; nia|].
    iMod (pctx_acc K (OfTy ty) 1 with "LFT PROPH UNIQ Hu H1 £a Own")
      as (G' dh gh) "(% & G' & #G'G & %Hdh & H & P & #Gs & #HG & Cl)"; [solve_ndisj|].
    destruct Hdh as (Hdh & Hgh & Hin).
    have Hm := pctx_hmode_le K 1.
    iEval (rewrite (pctx_kind_owned K) //) in "H".
    set mh := pctx_hmode K 1.
    set lK := pctx_loc K (ty_size ty) x₀ lr.
    iDestruct "H" as (? ->) "[Pt1 Gho1]".
    (* The address of the hole. *)
    iApply wp_fupd.
    iApply (wp_wand with "[P G' £w]").
    { iApply (wp_pctx_ptrs ⊤ K (ty_size ty) (g + 1) G' x₀ lr p True%I with "[] Gs [£w] [G'] P");
        [solve_ndisj| | |].
      - iEval (rewrite /lr -heap_cloc_mapsto_empty). iApply guards_true.
      - iApply (lc_weaken with "£w"). nia.
      - iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->". by iFrame. }
    iIntros (w) "(-> & _ & G' & P)".
    (* The new borrow. *)
    iDestruct (lc_weaken mh with "£k") as "£k"; [lia|].
    iMod (lc_fupd_elim_laterN with "£k Gho1") as "Gho1".
    iMod (ghost_var_alloc (lstate_triv y)) as (γζ) "[Ghζ Ghζ']".
    iMod (proph_loan_intro (uniq_cell_tyi y) ⊤ (uniq_cell y dh gh γζ) with "PROPH UNIQ")
      as (ζi) "Loan"; [solve_ndisj|].
    set ζ := uniq_prvar y ζi.
    rewrite proph_loan_unfold. iDestruct "Loan" as "[ζVo ζPc]".
    iDestruct (uniq_proph_tok with "ζVo ζPc") as "(ζVo & ζtok & ToζPc)".
    have Hhn := pctx_hmode_ne K 1 0 0.
    iDestruct (cumulative_time_receipt_mono (1 + (mh + S (pctx_ne K 0 0))) with "⧗") as "⧗";
      [destruct (pctx_ulfts K); simpl in *; lia|].
    iDestruct (cumulative_time_receipt_sep with "⧗") as "[⧗u ⧗]".
    iDestruct (cumulative_time_receipt_sep with "⧗") as "[⧗k ⧗e]".
    iMod ("Cl" $! (Blocked ty β) (PatBlocked β) (inl (PlaceGhost y ζi)) dh gh d g [ζ] 1%Qp
      (∃ idx1, proph_bor_tok ζ (uniq_cell y dh gh γζ) idx1 ∗
        proph_idx_bor_gen β ζ idx1 (uniq_gbody β ty tid lK))%I
      with "[//] [//] [%] [%] [] [] G' P [ζtok] [ζVo ToζPc Ghζ' Pt1 Gho1 £c ⧗k]")
      as "(Own & H1 & Bor1)".
    { intros ζl _. rewrite prfn_rsv_inl. apply place_ghost_rsv_elem. set_solver. }
    { lia. }
    { iApply pat_ok_blft. }
    { iApply (persistent_time_receipt_mono with "⧖"). lia. }
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
    iModIntro. iExists -[(lK, y, ζi, dh, gh, idx1); ((l, x₀), (pctx_path K [], ζi) :: ζm)].
    iFrame "L I". iSplit; last first.
    { iApply (proph_obs_impl with "Obs")=> π Hπ. by apply Hπ. }
    iSplitL "Tok1 Ghζ ⧗u".
    { iExists _, D. iSplit; [by rewrite eval_path_of_val|]. iFrame "⧖". iSplit; [|done].
      iSplit. { iApply llftl_incl_trans; [iApply pctx_blft_incl_r|]. iApply "Incl". }
      iSplit; [iPureIntro; lia|]. iSplitL. { iExists β, γζ. iFrame "∗#". iApply guards_refl. }
      iApply (guards_transitive_right with "[] [HG]"); [iApply pctx_blft_hlft|].
      iApply (lguards_weaken_later with "[HG]"); last first.
      { iApply ("HG" $! α 0). iEval (rewrite /lr -heap_cloc_mapsto_empty). iApply guards_true. }
      lia. }
    iSplit; [|done]. rewrite /tctx_elt_interp. iExists #l. iSplit; [done|].
    iExists D, d, g. iFrame "⧖".
    rewrite (lty_size_plug_eq K (Blocked ty β) (OfTy ty)) //. iFrame "Fr".
    iSplitL "⧗p ⧗e".
    { iDestruct (cumulative_time_receipt_sep with "[$⧗p $⧗e]") as "⧗".
      iApply (cumulative_time_receipt_mono with "⧗"). rewrite !lty_nrc_plug /=. lia. }
    iSplit; [done|]. iSplit; [done|].
    rewrite /ltype_own lty_pat_plug lty_rfn_plug pctx_rfn_blk_cons /= decide_True //.
  Qed.
End puniq.
