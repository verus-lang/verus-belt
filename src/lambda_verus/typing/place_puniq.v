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
    iDestruct (lc_weaken ((d + 1) * (1 + d + 2) + (D + 1)) with "£") as "[£a £c]";
      [rewrite /advance_credits; nia|].
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
End puniq.
