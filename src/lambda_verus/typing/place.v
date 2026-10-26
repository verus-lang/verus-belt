(** * Typing rules with place types

  This file brings the place types of [ltype.v] into the type system (see
  [~/verus-belt-phase3-design.md]), for a minimal vertical slice:
  - a unique borrow of a pair is unfolded into a place, and folded back
    ([tctx_unfold_uniq_prod], [tctx_fold_uniq_prod]);
  - field 0 is reborrowed, which blocks it and reserves the prophecy of the outer
    borrow for the reborrow's prophecy ([type_reborrow_field0_instr]);
  - the outer borrow can be dropped while field 0 is still blocked: its prophecy is
    resolved through the reservation ([type_drop_blocked_field0_instr]);
  - or, once the reborrow's lifetime has ended, field 0 is unblocked
    ([unblock_tctx_place_field0]).
  See [examples/get_first.v].

  ** The place element

  [p ◁ₗ{κ} lt] (a semantic type-context element, [TCtx_sem]) says that [p] is a
  unique borrow at [κ] whose referent has the place type [lt] (in [Uniq] mode,
  [ltype_own]). Its value is a pair of the value of a unique borrow
  [(l, x₀, ξi, d', g', idx)] (the index [idx] is not used: the place holds its own)
  and the list of the prophecy ids of the blocked leaves of [lt], from left to
  right; [x₀] gives the values of the unblocked leaves (and witnesses for the
  blocked ones). The refinement of the place is [lty_rfn lt x₀ ζis]: an unblocked
  leaf is refined by its value, a blocked one by the final value of its reborrow
  ([PlaceGhost]). The current value of the place is the denotation of this
  refinement ([place_cur]); the final value is the one of the borrow. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From lrust.lang Require Import proofmode.
From lrust.typing Require Export type ltype.
From lrust.typing Require Import type_context programs programs_util lft_contexts
  uniq_util uniq_bor product.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

(** * Refinements of places *)

Section lty_rfn.
  Context `{!typeG Σ}.

  Fixpoint lty_rfn {𝔄} (lt: lty 𝔄) : ~~𝔄 → list positive → prfn 𝔄 * list positive :=
    match lt in lty 𝔄 return ~~𝔄 → list positive → prfn 𝔄 * list positive with
    | OfTy _ => λ x ζis, (inl (PlaceIn x), ζis)
    | Blocked _ _ => λ x ζis, (inl (PlaceGhost x (hd 1%positive ζis)), tl ζis)
    (* Unfolded borrows and owned pointers are not supported yet. *)
    | UniqLty _ _ => λ x ζis, (inl (PlaceIn x), ζis)
    | OwnPtrLty _ _ => λ x ζis, (inl (PlaceIn x), ζis)
    | ProdLty lt1 lt2 => λ x ζis,
        let '(r1, ζis1) := lty_rfn lt1 x.1 ζis in
        let '(r2, ζis2) := lty_rfn lt2 x.2 ζis1 in
        (inr (r1, r2), ζis2)
    end.

  (** The number of blocked leaves. *)
  Fixpoint lty_nblk {𝔄} (lt: lty 𝔄) : nat :=
    match lt with
    | Blocked _ _ => 1
    | ProdLty lt1 lt2 => lty_nblk lt1 + lty_nblk lt2
    | _ => 0
    end.
End lty_rfn.

(** The value of a place element. *)
Notation placeₛ 𝔄 := (uniq_borₛ 𝔄 * listₛ positiveₛ)%ST.

Definition place_bor {𝔄} (x: ~~ (placeₛ 𝔄)) : ~~ (uniq_borₛ 𝔄) := x.1.
Definition place_ζis {𝔄} (x: ~~ (placeₛ 𝔄)) : list positive := x.2.

Section place.
  Context `{!typeG Σ}.

  Definition place_rfn {𝔄} (lt: lty 𝔄) (x: ~~ (placeₛ 𝔄)) : prfn 𝔄 :=
    (lty_rfn lt (uniq_bor_current (place_bor x)) x.2).1.

  (** The current value of a place. *)
  Definition place_cur {𝔄} (lt: lty 𝔄) (x: ~~ (placeₛ 𝔄)) : proph 𝔄 :=
    prfn_den (place_rfn lt x).

  (** The current value of a pair whose field 0 is blocked (it does not depend on
      the blocking lifetime, see [place_cur_blk0]). *)
  Definition place_blk0_cur {𝔄 𝔅} (x: ~~ (placeₛ (𝔄 * 𝔅))) : proph (𝔄 * 𝔅) := λ π,
    ((π (uniq_prvar (uniq_bor_current (place_bor x)).1 (hd 1%positive (place_ζis x)))).1,
      vπ (uniq_bor_current (place_bor x)).2 π).

  Lemma place_cur_blk0 {𝔄 𝔅} (ty1: type 𝔄) (ty2: type 𝔅) α x :
    place_cur (ProdLty (Blocked ty1 α) (OfTy ty2)) x = place_blk0_cur x.
  Proof.
    destruct x as [[[[[[l [x1 x2]] ξi] d'] g'] idx] ζis].
    fun_ext=> π. by rewrite /place_cur /place_rfn /= !prfn_den_inl.
  Qed.

  (** The interpretation of a place element, as the ownership of [&uniq{κ}] with
      [uniq_body] replaced by the ownership of the place. It also holds two cumulative
      time receipts per blocked leaf, which pay for unblocking it (see
      [unblock_tctx_place_field0]). *)
  Definition place_uniq_own {𝔄} (κ: lft) (lt: lty 𝔄) (x: ~~ (placeₛ 𝔄))
      (tid: thread_id) (v: val) : iProp Σ :=
    match x with ((l, x₀, ξi, d', g', _), ζis) =>
      ∃ d, ⧖d ∗ ⧗(2 * lty_nblk lt) ∗ ⌜v = #(l.1)⌝ ∗ ⌜S d' ≤ d ∧ g' ≤ d⌝ ∗
        κ ⊑ ty_lft (lty_fold lt) ∗
        (@[κ] &&{↑NllftG; d+1}&&> l #↦∗_) ∗
        ltype_own (Uniq κ ξi) lt (lty_rfn lt x₀ ζis).1 d' g' tid l
    end%I.
End place.

Notation "p ◁ₗ{ κ } lt" := (TCtx_sem _ p (place_uniq_own κ lt))
  (at level 55, format "p  ◁ₗ{ κ }  lt").

Section typing.
  Context `{!typeG Σ}.

  Lemma place_uniq_own_receipt {𝔄} κ (lt: lty 𝔄) x tid v :
    place_uniq_own κ lt x tid v -∗ ∃ d, ⧖d.
  Proof.
    destruct x as [[[[[[l x₀] ξi] d'] g'] idx] ζis]. iIntros "(%d & ⧖ & _)". by iExists d.
  Qed.

  (** As [typed_instr_of_skip], for a semantic element with a time receipt. *)
  Lemma typed_instr_of_skip_sem {𝔄 𝔅l} (E: elctx) (L: llctx) (I: invctx)
      (p: path) (Φ: ~~𝔄 → thread_id → val → iProp Σ) (T': tctx 𝔅l) (tr: predl_trans [𝔄] 𝔅l) :
    (∀ x tid v, Φ x tid v -∗ ∃ d, ⧖d) →
    (∀ x v d tid post mask iκs, ⊢ (llft_ctx -∗ time_ctx -∗ proph_ctx -∗ uniq_ctx -∗
      elctx_interp E -∗ llctx_interp L -∗ invctx_interp tid mask iκs I -∗
      ⌜eval_path p = Some v⌝ -∗ Φ x tid v -∗ ⧖d -∗ ⟨π, tr post -[x] mask π⟩ -∗
      ⧗1 -∗ ⧗1 -∗ ⧗1 -∗ £(advance_credits d) -∗ |={⊤}=>
      ∃ xl', llctx_interp L ∗ invctx_interp tid mask iκs I ∗ tctx_interp tid T' xl' ∗
        ⟨π, post xl' mask π⟩)%I) →
    typed_instr E L I +[TCtx_sem _ p Φ] (Seq Skip Skip) (const T') tr.
  Proof.
    intros HΦ Hvs tid post mask iκs xl. destruct xl as [x []].
    iIntros "#LFT #TIME #PROPH #UNIQ #E L I [T _] Obs".
    rewrite /tctx_elt_interp. iDestruct "T" as (v) "(%Hp & Φ)".
    iDestruct (HΦ with "Φ") as (d) "#⧖".
    wp_bind Skip. iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [set_solver|].
    iIntros "£ #⧖S". wp_let. iModIntro. wp_let. iApply wp_fupd.
    iApply (wp_cumulative_time_receipt_linear with "TIME ⧖S"); [set_solver|].
    iIntros "⧗". iDestruct (cumulative_time_receipt_mono (1 + (1 + 1)) with "⧗") as "⧗";
      [lia|].
    iDestruct (cumulative_time_receipt_sep with "⧗") as "[⧗1 ⧗]".
    iDestruct (cumulative_time_receipt_sep with "⧗") as "[⧗2 ⧗3]".
    wp_let.
    iMod (Hvs x v d tid post with "LFT TIME PROPH UNIQ E L I [//] Φ ⧖ Obs ⧗1 ⧗2 ⧗3 £")
      as (xl') "(? & ? & ? & ?)".
    iModIntro. iExists xl'. iFrame.
  Qed.

  (** * Converting between [&uniq] and places *)

  Lemma tctx_uniq_to_place {𝔄} E L p κ (ty: type 𝔄) :
    tctx_incl E L +[p ◁ &uniq{κ} ty] +[p ◁ₗ{κ} OfTy ty] (λ post '-[m], post -[(m, [])]).
  Proof.
    split; [by intros ??? [? []]|].
    iIntros (G tid [m []] mask post ?) "_ _ _ _ _ $ [T _] Obs".
    destruct m as [[[[[l x₀] ξi] d'] g'] idx].
    iDestruct "T" as (v d Hp) "(⧖ & (#Incl & %Hle & Body & #Pt) & %Phys)".
    iMod cumulative_time_receipt_0 as "⧗".
    iModIntro. iExists -[((l, x₀, ξi, d', g', idx), [])]. iFrame "Obs".
    iSplit; [|done]. rewrite /tctx_elt_interp. iExists v. iSplit; [done|].
    iExists d. iFrame "⧖ ⧗ Incl Pt". iSplit; [by inversion Phys|]. iSplit; [done|].
    rewrite /ltype_own /=. iExists x₀, idx. by iFrame.
  Qed.

  Lemma tctx_place_to_uniq {𝔄} E L p κ (ty: type 𝔄) :
    tctx_incl E L +[p ◁ₗ{κ} OfTy ty] +[p ◁ &uniq{κ} ty]
      (λ post '-[((l, x₀, ξi, d', g', _), _)], λ mask π,
        ∀ idx, post -[(l, x₀, ξi, d', g', idx)] mask π).
  Proof.
    split.
    { intros ?? Eq [[[[[[[??]?]?]?]?]?] []] ??. apply forall_proper=> ?. apply Eq. }
    iIntros (G tid [[[[[[[l x₀] ξi] d'] g'] idx] ζis] []] mask post ?) "_ _ _ _ _ $ [T _] Obs".
    rewrite /tctx_elt_interp. iDestruct "T" as (v ?) "(%d & ⧖ & _ & -> & %Hle & #Incl & #Pt & Own)".
    rewrite /ltype_own /=. iDestruct "Own" as (x idx') "[-> Body]".
    iModIntro. iExists -[(l, x₀, ξi, d', g', idx')].
    iSplit; [|iApply (proph_obs_impl with "Obs"); by intros ? ?]. iSplit; [|done].
    iExists _, d. iSplit; [done|]. by iFrame "⧖ Incl Pt Body".
  Qed.

  (** * Unfolding and folding a product behind a unique borrow *)

  Lemma tctx_unfold_uniq_prod {𝔄 𝔅} E L p κ (ty1: type 𝔄) (ty2: type 𝔅) :
    lctx_lft_alive E L κ →
    tctx_incl E L +[p ◁ &uniq{κ} (ty1 * ty2)] +[p ◁ₗ{κ} ProdLty (OfTy ty1) (OfTy ty2)]
      (λ post '-[m], post -[(m, [])]).
  Proof.
    intros Alv. split; [by intros ??? [? []]|].
    iIntros (G tid [m []] mask post ?) "#LFT #PROPH #UNIQ #E #GL G [T _] Obs".
    destruct m as [[[[[l [x1 x2]] ξi] d'] g'] idx].
    iDestruct "T" as (v d Hp) "(⧖ & (#Incl & %Hle & Body & #Pt) & %Phys)".
    leaf_open "GL" with "G" as "[L back]"; [set_solver|].
    iDestruct (Alv with "L E") as "#Lκ". iMod ("back" with "L") as "G".
    iDestruct (guards_transitive with "GL Lκ") as "#Gκ".
    iMod (prod_ofty_unfold_uniq ty1 ty2 κ ξi x1 x2 d' g' tid l ⊤ G
      with "LFT PROPH UNIQ Gκ G [Body]") as "[Own $]"; [solve_ndisj|..].
    { rewrite /ltype_own /=. iExists (x1, x2), idx. by iFrame. }
    iMod cumulative_time_receipt_0 as "⧗".
    iModIntro. iExists -[((l, (x1, x2), ξi, d', g', idx), [])]. iFrame "Obs".
    iSplit; [|done]. rewrite /tctx_elt_interp. iExists v. iSplit; [done|].
    iExists d. iFrame "⧖ ⧗ Incl Pt Own". iSplit; [by inversion Phys|done].
  Qed.

  Lemma tctx_fold_uniq_prod {𝔄 𝔅} E L p κ (ty1: type 𝔄) (ty2: type 𝔅) :
    lctx_lft_alive E L κ →
    tctx_incl E L +[p ◁ₗ{κ} ProdLty (OfTy ty1) (OfTy ty2)] +[p ◁ &uniq{κ} (ty1 * ty2)]
      (λ post '-[((l, x₀, ξi, d', g', _), _)], λ mask π,
        ∀ idx, post -[(l, x₀, ξi, d', g', idx)] mask π).
  Proof.
    intros Alv. split.
    { intros ?? Eq [[[[[[[??]?]?]?]?]?] []] ??. apply forall_proper=> ?. apply Eq. }
    iIntros (G tid [[[[[[[l [x1 x2]] ξi] d'] g'] idx] ζis] []] mask post ?)
      "#LFT #PROPH #UNIQ #E #GL G [T _] Obs".
    rewrite /tctx_elt_interp. iDestruct "T" as (v ?) "(%d & ⧖ & _ & -> & %Hle & #Incl & #Pt & Own)".
    leaf_open "GL" with "G" as "[L back]"; [set_solver|].
    iDestruct (Alv with "L E") as "#Lκ". iMod ("back" with "L") as "G".
    iDestruct (guards_transitive with "GL Lκ") as "#Gκ".
    iMod (prod_ofty_fold_uniq ty1 ty2 κ ξi x1 x2 d' g' tid l ⊤ G
      with "LFT PROPH UNIQ Gκ G Own") as "[Own $]"; [solve_ndisj|].
    rewrite /ltype_own /=. iDestruct "Own" as (x idx') "[-> Body]".
    iModIntro. iExists -[(l, (x1, x2), ξi, d', g', idx')].
    iSplit; [|iApply (proph_obs_impl with "Obs"); by intros ? ?]. iSplit; [|done].
    iExists _, d. iSplit; [done|]. by iFrame "⧖ Incl Pt Body".
  Qed.

  Lemma uniq_bor_future_eq {𝔄} l (x₀: ~~𝔄) ξi d g idx π :
    uniq_bor_future (l, x₀, ξi, d, g, idx) π = (π (uniq_prvar x₀ ξi)).1.
  Proof. done. Qed.

  (** * Reborrowing field 0 *)

  Lemma place_ghost_rsv_elem {𝔄} (x₀: ~~𝔄) ζi ζl :
    uniq_prvar x₀ ζi ∈ ζl → place_rfn_rsv (PlaceGhost x₀ ζi) ζl.
  Proof.
    intros ?. eapply proph_dep_weaken; [|apply place_ghost_rsv]. set_solver.
  Qed.

  Lemma lft_incl_prod_l {𝔄 𝔅} (ty1: type 𝔄) (ty2: type 𝔅) :
    ⊢ ty_lft (prod_ty ty1 ty2) ⊑ ty_lft ty1.
  Proof. rewrite /= lft_intersect_list_app. iApply llftl_intersect_incl_l. Qed.

  Lemma lft_incl_prod_r {𝔄 𝔅} (ty1: type 𝔄) (ty2: type 𝔅) :
    ⊢ ty_lft (prod_ty ty1 ty2) ⊑ ty_lft ty2.
  Proof. rewrite /= lft_intersect_list_app. iApply llftl_intersect_incl_r. Qed.

  (** Reborrow field 0 of a pair behind a unique borrow, at [κ ⊓ α]: the new unique
      borrow gets a fresh prophecy variable; field 0 of the place is blocked until
      [κ ⊓ α] ends, refined by the final value of the reborrow. The prophecy
      variable of the outer borrow is reserved for the reborrow's. *)
  Lemma type_reborrow_field0_instr {𝔄 𝔅} E L I p κ α (ty1: type 𝔄) (ty2: type 𝔅) :
    lctx_lft_alive E L κ →
    typed_instr E L I +[p ◁ₗ{κ} ProdLty (OfTy ty1) (OfTy ty2)] ReBor
      (const +[p +ₗ #0 ◁ &uniq{κ ⊓ α} ty1; p ◁ₗ{κ} ProdLty (Blocked ty1 (κ ⊓ α)) (OfTy ty2)])
      (λ post '-[x], λ mask π, ∀ m1: ~~ (uniq_borₛ 𝔄),
        uniq_bor_loc m1 = cloc_take (uniq_bor_loc (place_bor x)) (ty_size ty1) →
        uniq_bor_current m1 = (uniq_bor_current (place_bor x)).1 →
        post -[m1; (place_bor x, [uniq_bor_ξi m1])] mask π).
  Proof.
    intros Alv. apply typed_instr_of_skip_sem; [apply place_uniq_own_receipt|].
    iIntros ([[[[[[l [x1 x2]] ξi] d'] g'] idx] ζis] v d tid post mask iκs)
      "#LFT #TIME #PROPH #UNIQ #E L $ %Hp Own _ Obs ⧗ ⧗' ⧗'' £".
    iDestruct "Own" as (d0) "(#⧖0 & _ & -> & %Hle & #Incl & #PtBase & Own)".
    iDestruct (Alv with "L E") as "#Alv".
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iDestruct (guards_transitive with "Ghalf Alv") as "#Hκ".
    iDestruct (lc_weaken (1 + 1) with "£") as "[£ £']"; [rewrite /advance_credits; lia|].
    rewrite /ltype_own /=.
    iMod (cpd_acc with "LFT PROPH UNIQ Hκ H1 Own") as (κp) "(#Inclp & _ & Upd & Close)";
      [solve_ndisj|].
    iMod (lc_fupd_elim_later with "£ Upd") as "Upd".
    iMod (guarded_upd_run with "[] H2 Upd") as "(H2 & #⧖' & N)";
      [rewrite /lazyE; solve_ndisj| |].
    { iApply (guards_transitive with "Hκ Incl"). }
    iSimpl in "N". iDestruct "N" as "[L1 L2]".
    iDestruct "L1" as (? ->) "[Pt1 Gho1]".
    set l0 := cloc_take l (ty_size ty1).
    iMod (ghost_var_alloc (lstate_triv x1)) as (γζ) "[Ghζ Ghζ']".
    iMod (proph_loan_intro (uniq_cell_tyi x1) ⊤ (uniq_cell x1 d' g' γζ) with "PROPH UNIQ")
      as (ζi) "Loan"; [solve_ndisj|].
    set ζ := uniq_prvar x1 ζi.
    rewrite proph_loan_unfold. iDestruct "Loan" as "[ζVo ζPc]".
    iDestruct (uniq_proph_tok with "ζVo ζPc") as "(ζVo & ζtok & ToζPc)".
    iMod ("Close" $! (PatProd (PatBlocked (κ ⊓ α)) PatLeaf)
      (inr (inl (PlaceGhost x1 ζi), inl (PlaceIn x2)) : prfn (𝔄 * 𝔅)) d' g' [ζ] 1%Qp
      (∃ idx1, proph_bor_tok ζ (uniq_cell x1 d' g' γζ) idx1 ∗
        proph_idx_bor_gen (κ ⊓ α) ζ idx1 (uniq_gbody (κ ⊓ α) ty1 tid l0))%I
      with "[] [ζtok] [ζVo ToζPc Ghζ' Pt1 Gho1 L2 £']") as "(Own & H1 & Bor1)".
    { iPureIntro. intros ζl _. split; [|apply prfn_rsv_in]. rewrite prfn_rsv_inl.
      apply place_ghost_rsv_elem. set_solver. }
    { by rewrite big_sepL_singleton. }
    { iIntros "ζtok". rewrite big_sepL_singleton.
      iDestruct ("ToζPc" with "ζtok") as "ζPc".
      iMod (proph_loan_borrow_gen_pc ⊤ (κ ⊓ α) ζ (uniq_cell x1 d' g' γζ)
        (vπ (uniq_cell x1 d' g' γζ)) (uniq_gbody (κ ⊓ α) ty1 tid l0)
        with "LFT UNIQ [ζVo ζPc] [Ghζ' Pt1 Gho1]") as (idx1) "(Tok1 & #Bor1 & Back1)";
        [solve_ndisj| by rewrite proph_loan_unfold; iFrame| |].
      { iApply (uniq_gbody_triv_close with "Ghζ'"); [done|].
        iApply uniq_payload_intro_later. iNext. iFrame "⧖' Gho1 Pt1". }
      iModIntro. iSplitR; [|iSplitR "Tok1"; [|iExists idx1; by iFrame "Tok1 Bor1"]].
      { iNext. rewrite /pat_ok /=. iSplit; [|done].
        iApply (llftl_incl_trans with "[] Inclp"). iApply llftl_intersect_incl_l. }
      iNext. iApply guarded_upd_intro. iModIntro. iFrame "⧖'". iSimpl. iFrame "L2".
      rewrite /leaf_owned /blocked_owned. iIntros "#†α".
      iMod (fupd_mask_mono with "(Back1 †α)") as "Lender"; [rewrite /lazyE; solve_ndisj|].
      iMod (lc_fupd_elim_later with "£' Lender") as "Lender". iModIntro.
      iApply (guarded_upd_mono with "[] [Lender]");
        [|iApply (uniq_lender_settle with "LFT PROPH †α Lender")].
      iIntros "(%x & %d1 & %g1 & Eqz & ⧖1 & Gho & Pt) !>". iExists x, d1, g1.
      rewrite /ofty_owned /=. by iFrame. }
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "$"; [solve_ndisj|].
    iDestruct "Bor1" as (idx1) "[Tok1 #Bor1]".
    iModIntro.
    iExists -[(l0, x1, ζi, d', g', idx1); ((l, (x1, x2), ξi, d', g', idx), [ζi])].
    iSplit; last first.
    { iApply (proph_obs_impl with "Obs")=> π Hπ. by apply Hπ. }
    iEval (rewrite (heap_cloc_mapsto_emp_vec_app l (ty_size ty1))) in "PtBase".
    iSplitL "Tok1 Ghζ ⧗".
    { rewrite /tctx_elt_interp. iExists #(l.1), d0.
      iSplit. { iPureIntro. rewrite /= Hp shift_loc_0. done. }
      iFrame "⧖0". iSplit; [|done]. iSplit.
      { iApply llftl_incl_trans; [iApply llftl_intersect_incl_l|].
        iApply (llftl_incl_trans with "Incl"). iApply lft_incl_prod_l. }
      iSplit; [iPureIntro; lia|]. iSplitL.
      { iExists (κ ⊓ α), γζ. iFrame "∗#". iApply guards_refl. }
      iApply (guards_transitive_right with "[] [PtBase]"); [iApply llftl_intersect_incl_l|].
      iApply (guards_weaken_rhs_sep_l with "PtBase"). }
    iSplit; [|done].
    rewrite /tctx_elt_interp. iExists #(l.1). iSplit; [done|]. iExists d0.
    iFrame "⧖0 Incl Own". iSplitL "⧗' ⧗''".
    { iApply (cumulative_time_receipt_sep 1 1). iFrame. }
    iSplit; [done|]. iSplit; [done|].
    by iEval (rewrite (heap_cloc_mapsto_emp_vec_app l (ty_size ty1))).
  Qed.

  (** * Dropping the outer borrow while field 0 is blocked *)

  (** The outer borrow is given up while field 0 is still blocked: field 1 is
      returned as a fresh unique borrow (at a fresh prophecy variable η), and the
      prophecy variable ξ of the outer borrow is resolved (through its reservation)
      to the final value of the reborrow of field 0 and the final value of η. *)
  Lemma type_drop_blocked_field0_instr {𝔄 𝔅} E L I p κ α (ty1: type 𝔄) (ty2: type 𝔅) :
    lctx_lft_alive E L κ →
    typed_instr E L I +[p ◁ₗ{κ} ProdLty (Blocked ty1 α) (OfTy ty2)] SplitBor
      (const +[p +ₗ #ty1.(ty_size) ◁ &uniq{κ} ty2])
      (λ post '-[x], λ mask π, ∀ m2: ~~ (uniq_borₛ 𝔅),
        uniq_bor_loc m2 = cloc_skip (uniq_bor_loc (place_bor x)) (ty_size ty1) →
        uniq_bor_current m2 = (uniq_bor_current (place_bor x)).2 →
        uniq_bor_future (place_bor x) π =
          ((place_blk0_cur x π).1, uniq_bor_future m2 π) →
        post -[m2] mask π).
  Proof.
    intros Alv. apply typed_instr_of_skip_sem; [apply place_uniq_own_receipt|].
    iIntros ([[[[[[l [x1 x2]] ξi] d'] g'] idx] ζis] v d tid post mask iκs)
      "#LFT #TIME #PROPH #UNIQ #E L $ %Hp Own _ Obs _ _ _ £".
    iDestruct "Own" as (d0) "(#⧖0 & _ & -> & %Hle & #Incl & #PtBase & Own)".
    iDestruct (Alv with "L E") as "#Alv".
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iDestruct (guards_transitive with "Ghalf Alv") as "#Hκ".
    iDestruct (lc_weaken 1 with "£") as "£"; [rewrite /advance_credits; lia|].
    set ζi := hd 1%positive ζis. set ζ := uniq_prvar x1 ζi.
    rewrite /ltype_own /=.
    iDestruct "Own" as (x₀ κp γ γf idx' ζl) "(#Inclp & %Hr & Tok & Gh & Tf & ⧗o & #Bor)".
    set l2 := cloc_skip l (ty_size ty1).
    iMod (ghost_var_alloc (lstate_triv x2)) as (γη) "[Ghη Ghη']".
    iMod (proph_loan_intro (uniq_cell_tyi x2) ⊤ (uniq_cell x2 d' g' γη) with "PROPH UNIQ")
      as (ηi) "Loan"; [solve_ndisj|].
    set η := uniq_prvar x2 ηi.
    set uπ : proph (uniq_cellₛ (𝔄 * 𝔅)) :=
      λ π, (((π ζ).1, (π η).1), (1%positive, (1%positive, 1%positive))).
    have Hdep: uπ ./ ζl ++ [η].
    { destruct Hr as [Hr _]. rewrite prfn_rsv_inl /= in Hr.
      apply (proph_dep_constr2 (λ a b, ((a, b), (1%positive, (1%positive, 1%positive))))
        (λ π, (π ζ).1) (λ π, (π η).1)); [done|].
      apply (proph_dep_constr fst (λ π, π η)), proph_dep_one. }
    iMod (proph_idx_bor_gen_map_rsv ⊤ κ (uniq_prvar x₀ ξi) (uniq_cell x₀ d' g' γ) idx' ζl _
      η (uniq_cell x2 d' g' γη) (uniq_gbody κ ty2 tid l2) uπ (fractional.half γh)
      with "LFT PROPH UNIQ Hκ [£ Gh Tf Ghη'] H1 Loan Tok Bor") as "(#Obs' & Bor2 & H1)";
      [solve_ndisj|done| |].
    { iIntros (G' wπ ?) "#G'κ G' Body".
      iDestruct (bi.later_or with "Body") as "[Body|[>Tf' _]]"; last first.
      { iDestruct (cpd_tok_excl with "Tf Tf'") as "[]". }
      iMod (lc_fupd_elim_later with "£ Body") as "Body".
      rewrite cpd_body_cell.
      iDestruct "Body" as (p1 r1) "(#Ok & _ & Gh' & Upd)".
      iDestruct (ghost_var_agree with "Gh Gh'") as %[<- <-]%lstate_inj.
      iMod (guarded_upd_run with "[] G' Upd") as "($ & #⧖' & N)";
        [rewrite /lazyE; solve_ndisj| |].
      { iApply (guards_transitive with "G'κ Incl"). }
      iSimpl in "N". iDestruct "N" as "[L1 L2]".
      iDestruct "L2" as (? ->) "[Pt2 Gho2]".
      set r'' : prfn (𝔄 * 𝔅) := inr (inl (PlaceGhost x1 ζi), inl (PlaceGhost x2 ηi)).
      iMod (ghost_var_update_halves (lstate (PatProd (PatBlocked α) (PatBlocked κ)) r'')
        with "Gh Gh'") as "[_ Gh']".
      iModIntro. iExists (vπ (uniq_cell x2 d' g' γη)).
      iSplitL "Ghη' Pt2 Gho2".
      { iApply (uniq_gbody_triv_close with "Ghη'"); [done|].
        iApply uniq_payload_intro_later. iNext. iFrame "⧖' Gho2 Pt2". }
      iIntros (y' wη') "Pc Q". iModIntro. iNext. iExists (uniq_cell x₀ d' g' γ). iLeft.
      rewrite cpd_body_cell. iExists (PatProd (PatBlocked α) (PatBlocked κ)), r''.
      iFrame "Gh'". iSplit.
      { rewrite /pat_ok /=. iDestruct "Ok" as "[$ _]". iSplit; [|done]. iApply "Inclp". }
      iSplit. { iPureIntro. intros π. by rewrite /= !prfn_den_inl. }
      iApply guarded_upd_intro. iModIntro. iFrame "⧖'". iSimpl. iFrame "L1".
      rewrite /leaf_owned /blocked_owned. iIntros "#†κ". iModIntro.
      iApply (guarded_upd_mono with "[] [Pc Q]");
        [|iApply (uniq_lender_settle with "LFT PROPH †κ"); iExists y', wη'; iFrame].
      iIntros "(%x & %d1 & %g1 & Eqz & ⧖1 & Gho & Pt) !>". iExists x, d1, g1.
      rewrite /ofty_owned /=. by iFrame. }
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "$"; [solve_ndisj|].
    iDestruct "Bor2" as (idx2) "[Tok2 #Bor2]".
    iModIntro. iExists -[(l2, x2, ηi, d', g', idx2)].
    iSplit; last first.
    { iCombine "Obs Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=> π [Hπ Heq].
      apply Hπ; [done|done|].
      rewrite !uniq_bor_future_eq (uniq_prvar_app_irrel (𝔄:=𝔄 * 𝔅) (x1, x2) x₀) Heq.
      done. }
    iSplit; [|done].
    rewrite /tctx_elt_interp. iExists #(l.1 +ₗ ty_size ty1), d0.
    iSplit. { iPureIntro. by rewrite /= Hp. }
    iFrame "⧖0". iSplit; [|done]. iSplit.
    { iApply (llftl_incl_trans with "Incl"). iApply lft_incl_prod_r. }
    iSplit; [iPureIntro; lia|]. iSplitL "Ghη Tok2 ⧗o".
    { iExists κ, γη. iFrame "∗#". iApply guards_refl. }
    iEval (rewrite (heap_cloc_mapsto_emp_vec_app l (ty_size ty1))) in "PtBase".
    iApply (guards_weaken_rhs_sep_r with "PtBase").
  Qed.

  (** * Unblocking field 0 *)

  (** Turning an equalizer of the value of some contents into an observation, by
      sharing the contents at a fresh lifetime to get guards of their prophecy tokens
      (as in [unblock_tctx_cons_unblock]). *)
  Lemma proph_eqz_obs_by_share {𝔄} (ty: type 𝔄) (xπ: proph 𝔄) x d g tid G :
    Timeless G →
    llft_ctx -∗ (G &&{↑NllftG}&&> @[ty_lft ty]) -∗ G -∗
    £(d + d*(g+2) + (0 + (d+1)*(g+1)) + 1 + 1) -∗
    (xπ :== vπ x) -∗ ty_gho_own ty x d g tid ={⊤}=∗
      ⟨π, xπ π = vπ x π⟩ ∗ G ∗ ty_gho_own ty x d g tid.
  Proof.
    iIntros (?) "#LFT #Gty G £ Eqz gho".
    iDestruct "£" as "[[[[£s £k] £k'] £e] £g]".
    iDestruct (ty_gho_pers_impl with "gho") as "#ghoPers".
    iMod (llftl_begin with "LFT") as (κf) "[κf #κfend]"; [solve_ndisj|].
    set κs := κf ⊓ ty_lft ty.
    iMod (llftl_borrow _ κs (ty_gho_own ty x d g tid) with "LFT [$gho]") as "[Bor Inh]";
      [solve_ndisj|].
    iAssert ((@[κf] ∗ G) &&{↑NllftG}&&> @[κs])%I as "#Wκs".
    { iApply guards_llft_glb; [iApply guards_weaken_sep_l|].
      iApply guards_weaken_lhs_sep_r. iApply "Gty". }
    iAssert (κs ⊑ ty_lft ty)%I as "#Incl". { iApply llftl_intersect_incl_r. }
    iMod (ty_share with "LFT Incl ghoPers Wκs [$κf $G] Bor") as "Upd"; [solve_ndisj|].
    iMod (lc_step_fupdN_elim_later with "£s Upd") as ">[[κf G] #Shr]".
    iAssert (▷^(d*(g+2)) (∀ ζ, ⌜ζ ∈ ξl x⌝ -∗
      ((@[κf] ∗ G) &&{↑NllftG; 0 + (d+1)*(g+1)}&&> 1:[ζ])))%I as "#Hallζlater".
    { iIntros (ζ) "%Hin".
      iDestruct (ty_shr_guard_proph ty κs x 0 d g tid ζ (@[κf] ∗ G)%I Hin
        with "LFT Incl ghoPers Shr") as "A".
      iNext. iApply "A". leaf_goal laters to 0; [lia|]. iFrame "Wκs". }
    iMod (lc_fupd_elim_laterN with "£k Hallζlater") as "#Hallζ".
    iMod (uniq_cmra.proph_eqz_to_obs_with_guard with "£k' Hallζ [κf G] Eqz")
      as "[#Obs [κf G]]"; [set_solver|apply syn_indep|iFrame|].
    iAssert (|={⊤}=> [†κf])%I with "[£e κf]" as ">#†κf".
    { iApply fupd_mask_mono; [|iApply (lc_step_fupd_elim_later with "£e"); by iApply "κfend"].
      solve_ndisj. }
    iAssert (|={⊤}=> ▷ ty_gho_own ty x d g tid)%I with "[Inh]" as ">gho".
    { iApply fupd_mask_mono; [|iApply "Inh"; iApply llftl_end_inter; by iLeft]. solve_ndisj. }
    iMod (lc_fupd_elim_later with "£g gho") as "gho".
    iModIntro. iFrame "∗#".
  Qed.

  (** Once [κ ⊓ α] has ended (by ending [α]), field 0 of the place is unblocked: it
      gets the final contents of its reborrow, whose value is the final value of the
      reborrow. The place stays unfolded (and reserved, for no prophetic leaf), and
      can then be folded back with [tctx_fold_uniq_prod]. Unblocking pays with the
      two cumulative time receipts of the blocked leaf. *)
  Lemma unblock_tctx_place_field0 {𝔄 𝔅 𝔄l 𝔄l'} p κ α (ty1: type 𝔄) (ty2: type 𝔅)
      (T: tctx 𝔄l) (T': tctx 𝔄l') E L f :
    lctx_lft_alive E L κ → unblock_tctx E L α T T' f →
    unblock_tctx E L α (p ◁ₗ{κ} ProdLty (Blocked ty1 (κ ⊓ α)) (OfTy ty2) +:: T)
      (p ◁ₗ{κ} ProdLty (OfTy ty1) (OfTy ty2) +:: T')
      (λ π '(x -:: xl), λ '(x' -:: xl'),
        uniq_bor_loc (place_bor x') = uniq_bor_loc (place_bor x) ∧
        uniq_bor_future (place_bor x') π = uniq_bor_future (place_bor x) π ∧
        place_cur (ProdLty (OfTy ty1) (OfTy ty2)) x' π =
          place_blk0_cur x π ∧
        f π xl xl').
  Proof.
    iIntros (Alv Un G tid [x xl] ?) "#LFT #TIME #PROPH #UNIQ #E #L G #†α /=[(%v & %Hp & Own) T]".
    destruct x as [[[[[[l [x1 x2]] ξi] d'] g'] idx] ζis].
    iDestruct "Own" as (d0) "(#⧖0 & ⧗ & -> & %Hle & #Incl & #PtBase & Own)".
    iDestruct (cumulative_time_receipt_sep 1 1 with "⧗") as "[⧗a ⧗b]".
    leaf_open "L" with "G" as "[L1 back]"; [set_solver|].
    iDestruct (Alv with "L1 E") as "#Lκ". iMod ("back" with "L1") as "G".
    (* Half of [G] for the rest of the context, the other half for the place. *)
    iMod (fractional.frac_split_guard_in_half with "G L") as (γ1) "[GT [GP [#GhT #BackT]]]";
      [solve_ndisj|].
    iMod (Un with "LFT TIME PROPH UNIQ E GhT GT †α T") as (dT xl') "[#⧖T ToT']".
    iDestruct (guards_transitive with "GhT Lκ") as "#GPκ".
    iMod (fractional.frac_split_guard_in_half with "GP GPκ") as (γ2) "[H1 [H2 [#Gh2 #Back2]]]";
      [solve_ndisj|].
    iAssert (fractional.half γ2 &&{↑NllftG}&&> @[ty_lft ty1])%I as "#Gty1".
    { iApply (guards_transitive with "Gh2"). iApply (llftl_incl_trans with "Incl").
      iApply lft_incl_prod_l. }
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗a ⧖0") as "[_ £]";
      [solve_ndisj|].
    iDestruct (lc_weaken 1 with "£") as "£"; [rewrite /advance_credits; lia|].
    rewrite /ltype_own /=.
    iMod (cpd_acc with "LFT PROPH UNIQ Gh2 H1 Own") as (κp) "(#Inclp & _ & Upd & Close)";
      [solve_ndisj|].
    iMod (lc_fupd_elim_later with "£ Upd") as "Upd".
    iMod (guarded_upd_run with "[] H2 Upd") as "(H2 & #⧖' & N)";
      [rewrite /lazyE; solve_ndisj| |].
    { iApply (guards_transitive with "Gh2 Incl"). }
    iSimpl in "N". iDestruct "N" as "[L1 L2]".
    iDestruct "L2" as (? ->) "[Pt2 Gho2]".
    (* Unblock field 0: fire the inheritance of the reborrow and settle it. *)
    iAssert ([†(κ ⊓ α)])%I as "#†κα". { rewrite llftl_end_inter. by iRight. }
    iMod (fupd_mask_mono with "(L1 †κα)") as "Upd1"; [rewrite /lazyE; solve_ndisj|].
    iMod (guarded_upd_run with "Gty1 H2 Upd1") as "(H2 & %y1 & %d1 & %g1 & Eqz & #⧖1 & O1)";
      [rewrite /lazyE; solve_ndisj|].
    iDestruct "O1" as "[Pt1 Gho1]".
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗b ⧖1") as "[_ £]";
      [solve_ndisj|].
    iDestruct (lc_weaken (1 + (d1 + d1*(g1+2) + (0 + (d1+1)*(g1+1)) + 1 + 1)) with "£")
      as "[£e £]"; [rewrite /advance_credits; nia|].
    iSimpl in "Eqz". iMod (lc_fupd_elim_later with "£e Eqz") as "Eqz".
    iMod (proph_eqz_obs_by_share ty1 with "LFT Gty1 H2 £ Eqz Gho1") as "(#Obs1 & H2 & Gho1)".
    (* Close the outer borrow at the unblocked state, at the maximal depths. *)
    set d'' := d1 `max` d'. set g'' := g1 `max` g'.
    iDestruct (ty_gho_own_depth_mono _ d1 g1 d'' g'' with "Gho1") as "[Gho1 _]"; [lia..|].
    iDestruct (ty_gho_own_depth_mono _ d' g' d'' g'' with "Gho2") as "[Gho2 _]"; [lia..|].
    iAssert (⧖(S d'' `max` g''))%I as "#⧖''".
    { iCombine "⧖' ⧖1" as "⧖". iApply (persistent_time_receipt_mono with "⧖"). lia. }
    iMod ("Close" $! (PatProd PatLeaf PatLeaf) (inr (inl (PlaceIn y1), inl (PlaceIn x2)) : prfn (𝔄 * 𝔅))
      d'' g'' [] 1%Qp True%I with "[] [] [Pt1 Gho1 Pt2 Gho2]") as "(Own & H1 & _)".
    { iPureIntro. intros ζl _. split; apply prfn_rsv_in. }
    { done. }
    { iIntros "_". iModIntro. iSplitR; [iNext; by rewrite /pat_ok|]. iSplitL; [|done].
      iNext. iApply guarded_upd_intro. iModIntro. iFrame "⧖''". iSimpl.
      iSplitL "Pt1 Gho1"; [iExists y1|iExists x2]; by iFrame. }
    iMod (fupd_mask_mono with "(Back2 H1 H2)") as "GP"; [solve_ndisj|].
    iMod cumulative_time_receipt_0 as "⧗0".
    iCombine "⧖0 ⧖''" as "⧖D".
    iModIntro. iExists dT, (((l, (y1, x2), ξi, d'', g'', idx), []) -:: xl').
    iSplitR; [done|].
    iMod "ToT'". iModIntro. iNext. iMod "ToT'". iModIntro.
    iApply (step_fupdN_wand with "ToT'"). iIntros ">(GT & T' & #Obs')".
    iMod (fupd_mask_mono with "(BackT GT GP)") as "$"; [solve_ndisj|].
    iModIntro. iSplitR "Obs'".
    { iFrame "T'". rewrite /tctx_elt_interp. iExists #(l.1). iSplit; [done|].
      iExists (d0 `max` (S d'' `max` g'')). iFrame "⧖D ⧗0 Incl Own".
      iSplit; [done|]. iSplit; [iPureIntro; lia|].
      iApply (lguards_weaken_later with "PtBase"). lia. }
    iCombine "Obs1 Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=> π [Heq Hf].
    split; [done|]. split.
    { rewrite !uniq_bor_future_eq. apply (uniq_prvar_app_irrel (𝔄:=𝔄 * 𝔅)). }
    split; [|done].
    rewrite /place_cur /place_rfn /place_blk0_cur /= !prfn_den_inl /=. f_equal.
    symmetry. exact Heq.
  Qed.
End typing.
