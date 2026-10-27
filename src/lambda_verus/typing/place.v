(** * Typing rules with place types

  This file brings the place types of [ltype.v] into the type system (see
  [~/verus-belt-phase3-design.md]). A unique borrow of a (nested) product can be
  unfolded into a place, whose subplaces are accessed through place contexts
  ([lpath.v], [K : pctx 𝔅 𝔄]):
  - unfold a leaf [OfTy (ty1 * ty2)] at any path into a pair of leaves, and fold back
    ([tctx_unfold_place_prod], [tctx_fold_place_prod]; at the root, these are
    [tctx_unfold_uniq_prod], [tctx_fold_uniq_prod]);
  - reborrow the leaf at any path at [κ ⊓ α], which blocks it and reserves the
    prophecy of the outer borrow for the reborrow's prophecy
    ([type_reborrow_place_instr]);
  - once the reborrow's lifetime has ended, unblock the leaf
    ([unblock_tctx_place]);
  - drop the outer borrow while all leaves are blocked: its prophecy is
    pre-resolved through the reservation ([tctx_drop_place]). The unblocked leaves
    of a place are first reborrowed (at [κ ⊓ κ]), so that the outer borrow can be
    dropped with an arbitrary blocking pattern.
  See [examples/get_first.v].

  ** The place element

  [p ◁ₗ{κ} lt] (a semantic type-context element, [TCtx_sem]) says that [p] is a
  unique borrow at [κ] whose referent has the place type [lt] (in [Uniq] mode,
  [ltype_own]). Its value is a pair of the value of a unique borrow
  [(l, x₀, ξi, d', g', idx)] (the index [idx] is not used: the place holds its own)
  and a blocking map [ζm] from the paths of the blocked leaves of [lt] to the
  prophecy ids of their reborrows; [x₀] gives the values of the unblocked leaves (and
  witnesses for the blocked ones). The refinement of the place is
  [lty_rfn lt x₀ ζm []]: an unblocked leaf is refined by its value, a blocked one by
  the final value of its reborrow ([PlaceGhost]). The current value of the place is
  the denotation of this refinement ([place_cur]); the final value is the one of
  the borrow. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From lrust.lang Require Import proofmode.
From lrust.typing Require Export type ltype lpath.
From lrust.typing Require Import type_context programs programs_util lft_contexts
  uniq_util uniq_bor product own.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

(** The value of a place element. *)
Notation placeₛ 𝔄 := (uniq_borₛ 𝔄 * blk_mapₛ)%ST.

Definition place_bor {𝔄} (x: ~~ (placeₛ 𝔄)) : ~~ (uniq_borₛ 𝔄) := x.1.
Definition place_ζis {𝔄} (x: ~~ (placeₛ 𝔄)) : blk_map := x.2.

Section place.
  Context `{!typeG Σ}.

  Definition place_rfn {𝔄} (lt: lty 𝔄) (x: ~~ (placeₛ 𝔄)) : prfn 𝔄 :=
    lty_rfn lt (uniq_bor_current (place_bor x)) (place_ζis x) [].

  (** The current value of a place. *)
  Definition place_cur {𝔄} (lt: lty 𝔄) (x: ~~ (placeₛ 𝔄)) : proph 𝔄 :=
    prfn_den (place_rfn lt x).

  (** The final value of the reborrow of the blocked leaf at the hole of [K]. *)
  Definition place_blk_fin {𝔅 𝔄} (K: pctx 𝔅 𝔄) (x: ~~ (placeₛ 𝔄)) : proph 𝔅 := λ π,
    (π (uniq_prvar (pctx_get K (uniq_bor_current (place_bor x)))
      (blk_lookup (place_ζis x) (pctx_path K [])))).1.

  Lemma place_cur_blocked {𝔅 𝔄} (K: pctx 𝔅 𝔄) (ty: type 𝔅) β x :
    place_cur (pctx_plug K (Blocked ty β)) x =
      λ π, prfn_den (pctx_rfn K (uniq_bor_current (place_bor x)) (place_ζis x) []
        (inl (PlaceProph (pctx_get K (uniq_bor_current (place_bor x))) (place_blk_fin K x)))) π.
  Proof. by rewrite /place_cur /place_rfn lty_rfn_plug. Qed.

  (** The interpretation of a place element, as the ownership of [&uniq{κ}] with
      [uniq_body] replaced by the ownership of the place. It also holds two cumulative
      time receipts per blocked leaf, which pay for unblocking it (see
      [unblock_tctx_place]). *)
  Definition place_uniq_own {𝔄} (κ: lft) (lt: lty 𝔄) (x: ~~ (placeₛ 𝔄))
      (tid: thread_id) (v: val) : iProp Σ :=
    match x with ((l, x₀, ξi, d', g', _), ζm) =>
      ∃ d, ⧖d ∗ ⧗(2 * lty_nblk lt) ∗ ⌜v = #(l.1)⌝ ∗ ⌜S d' ≤ d ∧ g' ≤ d⌝ ∗
        κ ⊑ ty_lft (lty_fold lt) ∗
        (@[κ] &&{↑NllftG; d+1}&&> l #↦∗_) ∗
        ltype_own (Uniq κ ξi) lt (lty_rfn lt x₀ ζm []) d' g' tid l
    end%I.
End place.

Notation "p ◁ₗ{ κ } lt" := (TCtx_sem _ p (place_uniq_own κ lt))
  (at level 55, format "p  ◁ₗ{ κ }  lt").

Section typing.
  Context `{!typeG Σ}.

  Lemma place_uniq_own_receipt {𝔄} κ (lt: lty 𝔄) x tid v :
    place_uniq_own κ lt x tid v -∗ ∃ d, ⧖d.
  Proof.
    destruct x as [[[[[[l x₀] ξi] d'] g'] idx] ζm]. iIntros "(%d & ⧖ & _)". by iExists d.
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
    iIntros (G tid [[[[[[[l x₀] ξi] d'] g'] idx] ζm] []] mask post ?) "_ _ _ _ _ $ [T _] Obs".
    rewrite /tctx_elt_interp. iDestruct "T" as (v ?) "(%d & ⧖ & _ & -> & %Hle & #Incl & #Pt & Own)".
    rewrite /ltype_own /=. iDestruct "Own" as (x idx') "[-> Body]".
    iModIntro. iExists -[(l, x₀, ξi, d', g', idx')].
    iSplit; [|iApply (proph_obs_impl with "Obs"); by intros ? ?]. iSplit; [|done].
    iExists _, d. iSplit; [done|]. by iFrame "⧖ Incl Pt Body".
  Qed.

  Lemma uniq_bor_future_eq {𝔄} l (x₀: ~~𝔄) ξi d g idx π :
    uniq_bor_future (l, x₀, ξi, d, g, idx) π = (π (uniq_prvar x₀ ξi)).1.
  Proof. done. Qed.

  (** * Changing the place type of a subplace

      The subplace at the hole of a context [K] is changed from [lt] to [lt'], without
      changing the value, by a conversion of the [Owned] interpretations (under the
      lazy update of the contents) if the hole is below the root, or by a conversion in
      [Uniq] mode if the hole is the root. Below the root, the core of the place
      changes: the body of the borrow is switched to the new node ([cpd_rebody]),
      which is why the place must be simple. *)

  Lemma ltype_own_uniq_change_hole_gen {𝔅 𝔄} κ ξi (K: pctx 𝔅 𝔄) (lt lt': lty 𝔅) x₀ ζm q0 d g tid l E G :
    pctx_nonempty K → pctx_simple K → lty_simple lt' →
    lty_size lt' = lty_size lt → lty_fold lt' = lty_fold lt →
    (∀ α, α ∈ pat_blk_lfts (lty_pat lt') → α ∈ pat_blk_lfts (lty_pat lt)) →
    (∀ y q ζl, prfn_rsv (lty_rfn lt y ζm q) ζl → prfn_rsv (lty_rfn lt' y ζm q) ζl) →
    (∀ y q d g tid l, ltype_own (Owned (pctx_mode K 0)) lt (lty_rfn lt y ζm q) d g tid l ⊢
       |={lazyE}=> ltype_own (Owned (pctx_mode K 0)) lt' (lty_rfn lt' y ζm q) d g tid l) →
    Timeless G → ↑Nllft ∪ ↑prophN ⊆ E →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗ G -∗
    ltype_own (Uniq κ ξi) (pctx_plug K lt) (lty_rfn (pctx_plug K lt) x₀ ζm q0) d g tid l ={E}=∗
    ltype_own (Uniq κ ξi) (pctx_plug K lt') (lty_rfn (pctx_plug K lt') x₀ ζm q0) d g tid l ∗ G.
  Proof.
    iIntros (HK HsK Hs' Hsz Hfold Hpat Hrsv Hown ? HE) "#LFT #PROPH #UNIQ #Gκ G Own".
    rewrite /ltype_own !ltype_own_cp_uniq_plug //.
    iMod (cpd_rebody with "LFT PROPH UNIQ Gκ G Own") as (κp) "(#Inclp & #Ok & Upd & Close)";
      [done|].
    rewrite (lty_fold_plug_eq' K lt' lt) //.
    iApply ("Close" with "[%] [] [] [Upd]").
    - intros ζl. rewrite !lty_rfn_plug. apply pctx_rfn_rsv_mono; [done|]. by apply Hrsv.
    - iIntros "!>" (p2 r2 d2 g2) "Ok2 ⧖ N". rewrite -(lty_fold_plug_eq' K lt' lt) //.
      iApply (ltype_owned_leaf_node with "LFT PROPH UNIQ Ok2 ⧖ N"); [by destruct K|by apply lty_simple_plug].
    - iNext. rewrite !lty_pat_plug. iApply (pat_ok_plug with "Ok").
      iApply (pat_ok_incl with "[]"); [done|]. iApply (pat_ok_plug_hole with "Ok").
    - iNext. iApply (guarded_upd_mono with "[] Upd"). iIntros "[$ N]".
      rewrite !lty_pat_plug !lty_rfn_plug !ltype_own_plug Hsz. iDestruct "N" as "[H $]".
      by iApply Hown.
  Qed.

  Lemma ltype_own_uniq_change_hole {𝔅 𝔄} κ ξi (K: pctx 𝔅 𝔄) (lt lt': lty 𝔅) x₀ ζm d g tid l G :
    pctx_nonempty K → pctx_simple K → lty_simple lt' →
    lty_size lt' = lty_size lt → lty_fold lt' = lty_fold lt →
    (∀ α, α ∈ pat_blk_lfts (lty_pat lt') → α ∈ pat_blk_lfts (lty_pat lt)) →
    (∀ y q ζl, prfn_rsv (lty_rfn lt y ζm q) ζl → prfn_rsv (lty_rfn lt' y ζm q) ζl) →
    (∀ y q d g tid l, ltype_own (Owned (pctx_mode K 0)) lt (lty_rfn lt y ζm q) d g tid l ⊢
       |={lazyE}=> ltype_own (Owned (pctx_mode K 0)) lt' (lty_rfn lt' y ζm q) d g tid l) →
    Timeless G →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗ G -∗
    ltype_own (Uniq κ ξi) (pctx_plug K lt) (lty_rfn (pctx_plug K lt) x₀ ζm []) d g tid l ={⊤}=∗
    ltype_own (Uniq κ ξi) (pctx_plug K lt') (lty_rfn (pctx_plug K lt') x₀ ζm []) d g tid l ∗ G.
  Proof. intros. by apply ltype_own_uniq_change_hole_gen; [..|solve_ndisj]. Qed.

  Lemma lty_is_cpd_plug_ne {𝔅 𝔄} (K: pctx 𝔅 𝔄) lt : pctx_nonempty K → lty_is_cpd (pctx_plug K lt).
  Proof. by destruct K. Qed.

  (** As [tctx_place_change_hole] below, without the (unused) condition on the
      denotations. *)
  Lemma tctx_place_change_hole' {𝔅 𝔄} E L p κ (K: pctx 𝔅 𝔄) (lt lt': lty 𝔅) :
    lctx_lft_alive E L κ → pctx_simple K → lty_simple lt' →
    lty_size lt' = lty_size lt → lty_fold lt' = lty_fold lt → lty_nblk lt' = lty_nblk lt →
    (∀ α, α ∈ pat_blk_lfts (lty_pat lt') → α ∈ pat_blk_lfts (lty_pat lt)) →
    (∀ y ζm q ζl, prfn_rsv (lty_rfn lt y ζm q) ζl → prfn_rsv (lty_rfn lt' y ζm q) ζl) →
    (∀ y ζm q d g tid l, ltype_own (Owned (pctx_mode K 0)) lt (lty_rfn lt y ζm q) d g tid l ⊢
       |={lazyE}=> ltype_own (Owned (pctx_mode K 0)) lt' (lty_rfn lt' y ζm q) d g tid l) →
    (∀ κ ξi y ζm d g tid l G, Timeless G →
       ⊢ llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗ G -∗
         ltype_own (Uniq κ ξi) lt (lty_rfn lt y ζm []) d g tid l ={⊤}=∗
         ltype_own (Uniq κ ξi) lt' (lty_rfn lt' y ζm []) d g tid l ∗ G) →
    tctx_incl E L +[p ◁ₗ{κ} pctx_plug K lt] +[p ◁ₗ{κ} pctx_plug K lt']
      (λ post '-[x], post -[x]).
  Proof.
    intros Alv HsK Hs' Hsz Hfold Hnb Hpat Hrsv Hown Hroot.
    split; [by intros ??? [? []]|].
    iIntros (G tid [x []] mask post ?) "#LFT #PROPH #UNIQ #E #GL G [T _] Obs".
    destruct x as [[[[[[l x₀] ξi] d'] g'] idx] ζm].
    rewrite /tctx_elt_interp. iDestruct "T" as (v ?) "(%d & ⧖ & ⧗ & -> & %Hle & #Incl & #Pt & Own)".
    leaf_open "GL" with "G" as "[L back]"; [set_solver|].
    iDestruct (Alv with "L E") as "#Lκ". iMod ("back" with "L") as "G".
    iDestruct (guards_transitive with "GL Lκ") as "#Gκ".
    have Hrsv' := λ y q ζl, Hrsv y ζm q ζl. have Hown' := λ y q, Hown y ζm q.
    iAssert (|={⊤}=> ltype_own (Uniq κ ξi) (pctx_plug K lt') (lty_rfn (pctx_plug K lt') x₀ ζm [])
      d' g' tid l ∗ G)%I with "[Own G]" as ">[Own G]".
    { destruct K as [|? ? ? K lt2|? ? ? lt1 K|? ? n K|? ? tyl i w K].
      - by iApply (Hroot with "LFT PROPH UNIQ Gκ G Own").
      - by iApply (ltype_own_uniq_change_hole with "LFT PROPH UNIQ Gκ G Own").
      - by iApply (ltype_own_uniq_change_hole with "LFT PROPH UNIQ Gκ G Own").
      - by iApply (ltype_own_uniq_change_hole with "LFT PROPH UNIQ Gκ G Own").
      - by iApply (ltype_own_uniq_change_hole with "LFT PROPH UNIQ Gκ G Own"). }
    iModIntro. iExists -[((l, x₀, ξi, d', g', idx), ζm)]. iFrame "G Obs".
    iSplit; [|done]. iExists #(l.1). iSplit; [done|]. iExists d.
    rewrite !lty_nblk_plug Hnb (lty_fold_plug_eq' K lt' lt) //. by iFrame "∗#".
  Qed.

  Lemma tctx_place_change_hole {𝔅 𝔄} E L p κ (K: pctx 𝔅 𝔄) (lt lt': lty 𝔅) :
    lctx_lft_alive E L κ → pctx_simple K → lty_simple lt' →
    lty_size lt' = lty_size lt → lty_fold lt' = lty_fold lt → lty_nblk lt' = lty_nblk lt →
    (∀ α, α ∈ pat_blk_lfts (lty_pat lt') → α ∈ pat_blk_lfts (lty_pat lt)) →
    (∀ y ζm q, prfn_den (lty_rfn lt' y ζm q) = prfn_den (lty_rfn lt y ζm q)) →
    (∀ y ζm q ζl, prfn_rsv (lty_rfn lt y ζm q) ζl → prfn_rsv (lty_rfn lt' y ζm q) ζl) →
    (∀ y ζm q d g tid l, ltype_own (Owned (pctx_mode K 0)) lt (lty_rfn lt y ζm q) d g tid l ⊢
       |={lazyE}=> ltype_own (Owned (pctx_mode K 0)) lt' (lty_rfn lt' y ζm q) d g tid l) →
    (∀ κ ξi y ζm d g tid l G, Timeless G →
       ⊢ llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗ G -∗
         ltype_own (Uniq κ ξi) lt (lty_rfn lt y ζm []) d g tid l ={⊤}=∗
         ltype_own (Uniq κ ξi) lt' (lty_rfn lt' y ζm []) d g tid l ∗ G) →
    tctx_incl E L +[p ◁ₗ{κ} pctx_plug K lt] +[p ◁ₗ{κ} pctx_plug K lt']
      (λ post '-[x], post -[x]).
  Proof.
    intros Alv HsK Hs' Hsz Hfold Hnb Hpat Hden. by apply tctx_place_change_hole'.
  Qed.

  (** ** Unfolding and folding products *)

  Lemma tctx_unfold_place_prod {𝔅1 𝔅2 𝔄} E L p κ (K: pctx (𝔅1 * 𝔅2) 𝔄)
      (ty1: type 𝔅1) (ty2: type 𝔅2) :
    lctx_lft_alive E L κ → pctx_simple K →
    tctx_incl E L +[p ◁ₗ{κ} pctx_plug K (OfTy (ty1 * ty2))]
      +[p ◁ₗ{κ} pctx_plug K (ProdLty (OfTy ty1) (OfTy ty2))] (λ post '-[x], post -[x]).
  Proof.
    intros Alv HsK. apply tctx_place_change_hole; [done|done|done|done|done|done|..].
    - intros ?; simpl; set_solver.
    - intros [y1 y2] ??. fun_ext=> π. by rewrite /= !prfn_den_in.
    - intros ?????. split; apply prfn_rsv_in.
    - intros [y1 y2] ??????. iIntros "H !>". by iApply prod_ofty_unfold_own.
    - iIntros (κ' ξi' [y1 y2] ζm' d g tid l G ?) "LFT PROPH UNIQ Gκ G Own".
      iApply (prod_ofty_unfold_uniq with "LFT PROPH UNIQ Gκ G Own"). solve_ndisj.
  Qed.

  Lemma tctx_fold_place_prod {𝔅1 𝔅2 𝔄} E L p κ (K: pctx (𝔅1 * 𝔅2) 𝔄)
      (ty1: type 𝔅1) (ty2: type 𝔅2) :
    lctx_lft_alive E L κ → pctx_simple K →
    tctx_incl E L +[p ◁ₗ{κ} pctx_plug K (ProdLty (OfTy ty1) (OfTy ty2))]
      +[p ◁ₗ{κ} pctx_plug K (OfTy (ty1 * ty2))] (λ post '-[x], post -[x]).
  Proof.
    intros Alv HsK. apply tctx_place_change_hole; [done|done|done|done|done|done|..].
    - intros ?; simpl; set_solver.
    - intros [y1 y2] ??. fun_ext=> π. by rewrite /= !prfn_den_in.
    - intros ?????. apply prfn_rsv_in.
    - intros [y1 y2] ??????. iIntros "H !>". by iApply (prod_ofty_unfold_own with "H").
    - iIntros (κ' ξi' [y1 y2] ζm' d g tid l G ?) "LFT PROPH UNIQ Gκ G Own".
      iApply (prod_ofty_fold_uniq with "LFT PROPH UNIQ Gκ G Own"). solve_ndisj.
  Qed.

  (** ** Unfolding and folding owned pointers

      Unfolding an owned pointer that is not itself below an owned pointer is a pure
      inclusion (the pointee's points-to is not under a later); folding back works
      below any number of owned pointers. When the body of the borrow is switched to
      the new node, its closing view shift folds the owned pointer back at a depth
      increased by one, which is paid for by the shifted time receipts of the leaves
      below it (see [blocked_owned] and [ltype_owned_unblock_fold]). *)

  Lemma tctx_unfold_place_own {𝔅 𝔄} E L p κ (K: pctx (at_locₛ 𝔅) 𝔄) n (ty: type 𝔅) :
    lctx_lft_alive E L κ → pctx_simple K → pctx_mode K 0 = 0 →
    tctx_incl E L +[p ◁ₗ{κ} pctx_plug K (OfTy (own_ptr n ty))]
      +[p ◁ₗ{κ} pctx_plug K (OwnPtrLty n (OfTy ty))] (λ post '-[x], post -[x]).
  Proof.
    intros Alv HsK Hm. apply tctx_place_change_hole; [done|done|done|done|done|done|..].
    - intros ?; simpl; set_solver.
    - intros [l' y] ??. fun_ext=> π. by rewrite /= !prfn_den_in.
    - intros ?????. apply prfn_rsv_in.
    - intros [l' y] ??????. rewrite Hm. iIntros "H !>". by iApply ownptr_ofty_unfold_own.
    - iIntros (κ' ξi' [l' y] ζm' d g tid l G ?) "LFT PROPH UNIQ Gκ G Own".
      iApply (cpd_unfold_uniq (OwnPtrLty n (OfTy ty)) with "LFT PROPH UNIQ Gκ G Own");
        [done|done|done|apply prfn_rsv_in|by intros π; rewrite /= !prfn_den_in| |solve_ndisj].
      iIntros (d' g') "[Gho Pt] !>". iApply ownptr_ofty_unfold_own. iExists (l', y).
      by iFrame.
  Qed.

  Lemma tctx_fold_place_own {𝔅 𝔄} E L p κ (K: pctx (at_locₛ 𝔅) 𝔄) n (ty: type 𝔅) :
    lctx_lft_alive E L κ → pctx_simple K →
    tctx_incl E L +[p ◁ₗ{κ} pctx_plug K (OwnPtrLty n (OfTy ty))]
      +[p ◁ₗ{κ} pctx_plug K (OfTy (own_ptr n ty))] (λ post '-[x], post -[x]).
  Proof.
    intros Alv HsK. apply tctx_place_change_hole; [done|done|done|done|done|done|..].
    - intros ?; simpl; set_solver.
    - intros [l' y] ??. fun_ext=> π. by rewrite /= !prfn_den_in.
    - intros ?????. apply prfn_rsv_in.
    - intros [l' y] ??????. iIntros "H !>". by iApply (ownptr_ofty_fold_own with "H").
    - iIntros (κ' ξi' [l' y] ζm' d g tid l G ?) "LFT PROPH UNIQ Gκ G Own".
      iApply (cpd_fold_uniq (OwnPtrLty n (OfTy ty)) _ _ (l', y) with "LFT PROPH UNIQ Gκ G Own");
        [done| |solve_ndisj].
      iIntros (d' g') "N !>". iDestruct (ownptr_ofty_fold_own 0 with "N") as (? ->) "[$ $]".
  Qed.

  (** Unfolding an owned pointer at any depth below the root (e.g. a box inside a box):
      below [k] laters ([pctx_mode K 0 = k]), the points-to of the pointee is stripped of
      its laters with the later credits of a program step; the body of the borrow is
      switched to the new node ([cpd_rebody]) at the time of the instruction. *)
  Lemma type_unfold_place_own_instr {𝔅 𝔄} E L I p κ (K: pctx (at_locₛ 𝔅) 𝔄) n (ty: type 𝔅) :
    lctx_lft_alive E L κ → pctx_nonempty K → pctx_simple K →
    typed_instr E L I +[p ◁ₗ{κ} pctx_plug K (OfTy (own_ptr n ty))] (Seq Skip Skip)
      (const +[p ◁ₗ{κ} pctx_plug K (OwnPtrLty n (OfTy ty))]) (λ post '-[x], post -[x]).
  Proof.
    intros Alv HK HKs. apply typed_instr_of_skip_sem; [apply place_uniq_own_receipt|].
    iIntros ([[[[[[l x₀] ξi] d'] g'] idx] ζm] v d tid post mask iκs)
      "#LFT #TIME #PROPH #UNIQ #E L $ %Hpath Own _ Obs ⧗a _ _ _".
    iDestruct "Own" as (d0) "(#⧖0 & ⧗p & -> & %Hle & #Incl & #PtBase & Own)".
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗a ⧖0") as "[_ £]";
      [solve_ndisj|].
    iDestruct (Alv with "L E") as "#Alv".
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iDestruct (guards_transitive with "Ghalf Alv") as "#Hκ".
    rewrite /ltype_own !ltype_own_cp_uniq_plug //.
    iMod (cpd_rebody with "LFT PROPH UNIQ Hκ H1 Own") as (κp) "(#Inclp & #Ok & Upd & Close)";
      [solve_ndisj|].
    iDestruct (lc_weaken (1 + (advance_credits d0 - 1)) with "£") as "[£a £]";
      [rewrite /advance_credits; lia|].
    iMod (lc_fupd_elim_later with "£a Upd") as "Upd".
    iMod (guarded_upd_run with "[] H2 Upd") as "(H2 & #⧖' & N)"; [solve_ndisj| |].
    { iApply (guards_transitive with "Hκ Incl"). }
    rewrite !lty_pat_plug !lty_rfn_plug !ltype_own_plug.
    iDestruct "N" as "[L1 Rest]". iSimpl in "L1".
    iDestruct (pctx_own_mode_le with "Rest") as %Hk.
    iDestruct "L1" as (? ->) "[Pt Gho]".
    destruct (pctx_get K x₀) as [l' y] eqn:Hm.
    iDestruct (lc_weaken (pctx_mode K 0) with "£") as "£"; [rewrite /advance_credits; nia|].
    iMod (lc_fupd_elim_laterN with "£ Gho") as "Gho".
    destruct (pctx_depth K d') as [|dh] eqn:Hdh; [done|].
    iDestruct "Gho" as "(Pt' & Fr' & Gho)".
    iMod ("Close" $! (pctx_pat K (PatOwn PatLeaf))
      (pctx_rfn K x₀ ζm [] (inr (l', inl (PlaceIn y)))) d' g'
      with "[%] [] [] [Pt Pt' Fr' Gho Rest]") as "[Own H1]".
    { intros ζl. apply pctx_rfn_rsv_mono; [done|]. intros _. apply prfn_rsv_in. }
    { iIntros "!>" (p2 r2 d2 g2) "Ok2 ⧖ N".
      rewrite -(lty_fold_plug_eq' K (OwnPtrLty n (OfTy ty)) (OfTy (own_ptr n ty))); [|done].
      iApply (ltype_owned_leaf_node with "LFT PROPH UNIQ Ok2 ⧖ N");
        [by apply lty_is_cpd_plug_ne|by apply lty_simple_plug]. }
    { iNext. iApply (pat_ok_plug with "Ok"). by rewrite /pat_ok. }
    { iNext. iApply guarded_upd_intro. iModIntro. iFrame "⧖'".
      rewrite ltype_own_plug Hdh /=. iFrame "Rest Pt". iSplit; [done|].
      iSplitL "Fr'"; [by iApply bi.laterN_intro|].
      iExists y. iSplit; [done|]. rewrite /ofty_owned.
      iEval (rewrite (heap_cloc_mapsto_fancy_empty l' (ty_phys ty y tid)) ty_size_eq) in "Pt'".
      iFrame "Pt'". iApply (bi.laterN_le 1); [lia|]. done. }
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "$"; [solve_ndisj|].
    iModIntro. iExists -[((l, x₀, ξi, d', g', idx), ζm)].
    iSplit; [|by iApply (proph_obs_impl with "Obs")]. iSplit; [|done].
    rewrite /tctx_elt_interp. iExists #(l.1). iSplit; [done|]. iExists d0.
    iFrame "⧖0 PtBase". iSplitL "⧗p". { by rewrite !lty_nblk_plug /=. }
    iSplit; [done|]. iSplit; [done|].
    rewrite (lty_fold_plug_eq' K (OwnPtrLty n (OfTy ty)) (OfTy (own_ptr n ty))) //.
    iFrame "Incl".
    rewrite /ltype_own ltype_own_cp_uniq_plug // lty_pat_plug lty_rfn_plug Hm /=.
    rewrite (lty_fold_plug_eq' K (OwnPtrLty n (OfTy ty)) (OfTy (own_ptr n ty))) //.
  Qed.

  (** At the root: unfolding a unique borrow of a pair, and folding back. *)
  Lemma tctx_unfold_uniq_prod {𝔄 𝔅} E L p κ (ty1: type 𝔄) (ty2: type 𝔅) :
    lctx_lft_alive E L κ →
    tctx_incl E L +[p ◁ &uniq{κ} (ty1 * ty2)] +[p ◁ₗ{κ} ProdLty (OfTy ty1) (OfTy ty2)]
      (λ post '-[m], post -[(m, [])]).
  Proof.
    intros Alv. eapply tctx_incl_ext; [eapply tctx_incl_trans;
      [apply tctx_uniq_to_place|apply (tctx_unfold_place_prod _ _ _ _ PHole); done]|].
    by intros ? [? []].
  Qed.

  Lemma tctx_fold_uniq_prod {𝔄 𝔅} E L p κ (ty1: type 𝔄) (ty2: type 𝔅) :
    lctx_lft_alive E L κ →
    tctx_incl E L +[p ◁ₗ{κ} ProdLty (OfTy ty1) (OfTy ty2)] +[p ◁ &uniq{κ} (ty1 * ty2)]
      (λ post '-[((l, x₀, ξi, d', g', _), _)], λ mask π,
        ∀ idx, post -[(l, x₀, ξi, d', g', idx)] mask π).
  Proof.
    intros Alv. eapply tctx_incl_ext; [eapply tctx_incl_trans;
      [apply (tctx_fold_place_prod _ _ _ _ PHole); done|apply tctx_place_to_uniq]|].
    by intros ? [[[[[[[??]?]?]?]?]?] []].
  Qed.

  (** * Reborrowing a leaf *)

  Lemma place_ghost_rsv_elem {𝔄} (x₀: ~~𝔄) ζi ζl :
    uniq_prvar x₀ ζi ∈ ζl → place_rfn_rsv (PlaceGhost x₀ ζi) ζl.
  Proof.
    intros ?. eapply proph_dep_weaken; [|apply place_ghost_rsv]. set_solver.
  Qed.

  (** Reborrow the leaf at the hole of [K] behind a unique borrow, at [κ ⊓ α]: the new
      unique borrow gets a fresh prophecy variable; the leaf is blocked until [κ ⊓ α]
      ends, refined by the final value of the reborrow (the blocking map gets an entry
      for the path of the hole). The prophecy variable of the outer borrow is
      reserved for the reborrow's. *)
  Lemma type_reborrow_place_instr {𝔅 𝔄} E L I p κ α (K: pctx 𝔅 𝔄) (ty: type 𝔅) :
    lctx_lft_alive E L κ → pctx_nonempty K → pctx_noderef K →
    typed_instr E L I +[p ◁ₗ{κ} pctx_plug K (OfTy ty)] ReBor
      (const +[p +ₗ #(pctx_off K) ◁ &uniq{κ ⊓ α} ty;
               p ◁ₗ{κ} pctx_plug K (Blocked ty (κ ⊓ α))])
      (λ post '-[x], λ mask π, ∀ m1: ~~ (uniq_borₛ 𝔅),
        uniq_bor_loc m1 = pctx_loc K (ty_size ty) (uniq_bor_current (place_bor x))
          (uniq_bor_loc (place_bor x)) →
        uniq_bor_current m1 = pctx_get K (uniq_bor_current (place_bor x)) →
        post -[m1; (place_bor x, (pctx_path K [], uniq_bor_ξi m1) :: place_ζis x)] mask π).
  Proof.
    intros Alv HK HKd. apply typed_instr_of_skip_sem; [apply place_uniq_own_receipt|].
    iIntros ([[[[[[l x₀] ξi] d'] g'] idx] ζm] v d tid post mask iκs)
      "#LFT #TIME #PROPH #UNIQ #E L $ %Hp Own _ Obs ⧗ ⧗' ⧗'' £".
    iDestruct "Own" as (d0) "(#⧖0 & ⧗p & -> & %Hle & #Incl & #PtBase & Own)".
    iDestruct (Alv with "L E") as "#Alv".
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iDestruct (guards_transitive with "Ghalf Alv") as "#Hκ".
    iDestruct (lc_weaken (1 + 1) with "£") as "[£ £']"; [rewrite /advance_credits; lia|].
    set β := κ ⊓ α.
    rewrite /ltype_own ltype_own_cp_uniq_plug //.
    iMod (cpd_acc with "LFT PROPH UNIQ Hκ H1 Own") as (κp) "(#Inclp & #Ok & Upd & Close)";
      [solve_ndisj|].
    iMod (lc_fupd_elim_later with "£ Upd") as "Upd".
    iMod (guarded_upd_run with "[] H2 Upd") as "(H2 & #⧖' & N)";
      [rewrite /lazyE; solve_ndisj| |].
    { iApply (guards_transitive with "Hκ Incl"). }
    rewrite lty_pat_plug lty_rfn_plug ltype_own_plug pctx_mode_noderef // pctx_depth_noderef //.
    iDestruct "N" as "[L1 Rest]". iSimpl in "L1".
    iDestruct "L1" as (? ->) "[Pt1 Gho1]".
    set y := pctx_get K x₀. set lK := pctx_loc K (ty_size ty) x₀ l.
    iMod (ghost_var_alloc (lstate_triv y)) as (γζ) "[Ghζ Ghζ']".
    iMod (proph_loan_intro (uniq_cell_tyi y) ⊤ (uniq_cell y d' g' γζ) with "PROPH UNIQ")
      as (ζi) "Loan"; [solve_ndisj|].
    set ζ := uniq_prvar y ζi.
    rewrite proph_loan_unfold. iDestruct "Loan" as "[ζVo ζPc]".
    iDestruct (uniq_proph_tok with "ζVo ζPc") as "(ζVo & ζtok & ToζPc)".
    iMod ("Close" $! (pctx_pat K (PatBlocked β)) (pctx_rfn K x₀ ζm [] (inl (PlaceGhost y ζi)))
      d' g' [ζ] 1%Qp
      (∃ idx1, proph_bor_tok ζ (uniq_cell y d' g' γζ) idx1 ∗
        proph_idx_bor_gen β ζ idx1 (uniq_gbody β ty tid lK))%I
      with "[] [ζtok] [ζVo ToζPc Ghζ' Pt1 Gho1 Rest £']") as "(Own & H1 & Bor1)".
    { iPureIntro. intros ζl Hr. eapply pctx_rfn_rsv; [|exact Hr|]; [set_solver|].
      rewrite prfn_rsv_inl. apply place_ghost_rsv_elem. set_solver. }
    { by rewrite big_sepL_singleton. }
    { iIntros "ζtok". rewrite big_sepL_singleton.
      iDestruct ("ToζPc" with "ζtok") as "ζPc".
      iMod (proph_loan_borrow_gen_pc ⊤ β ζ (uniq_cell y d' g' γζ)
        (vπ (uniq_cell y d' g' γζ)) (uniq_gbody β ty tid lK)
        with "LFT UNIQ [ζVo ζPc] [Ghζ' Pt1 Gho1]") as (idx1) "(Tok1 & #Bor1 & Back1)";
        [solve_ndisj| by rewrite proph_loan_unfold; iFrame| |].
      { iApply (uniq_gbody_triv_close with "Ghζ'"); [done|].
        iApply uniq_payload_intro_later. iNext. iFrame "⧖' Gho1 Pt1". }
      iModIntro. iSplitR; [|iSplitR "Tok1"; [|iExists idx1; by iFrame "Tok1 Bor1"]].
      { iNext. iApply (pat_ok_plug with "Ok"). iApply pat_ok_blocked.
        iApply (llftl_incl_trans with "[] Inclp"). iApply llftl_intersect_incl_l. }
      iNext. iApply guarded_upd_intro. iModIntro. iFrame "⧖'".
      rewrite ltype_own_plug pctx_mode_noderef // pctx_depth_noderef //. iFrame "Rest".
      rewrite /= /leaf_owned /blocked_owned. iIntros "#†α".
      iMod (fupd_mask_mono with "(Back1 †α)") as "Lender"; [rewrite /lazyE; solve_ndisj|].
      iMod (lc_fupd_elim_later with "£' Lender") as "Lender". iModIntro.
      iApply (guarded_upd_mono with "[] [Lender]");
        [|iApply (uniq_lender_settle with "LFT PROPH †α Lender")].
      iIntros "(%x & %d1 & %g1 & Eqz & ⧖1 & Gho & Pt) !>". iExists x, d1, g1.
      rewrite /ofty_owned /=. by iFrame. }
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "$"; [solve_ndisj|].
    iDestruct "Bor1" as (idx1) "[Tok1 #Bor1]".
    iModIntro.
    iExists -[(lK, y, ζi, d', g', idx1); ((l, x₀, ξi, d', g', idx), (pctx_path K [], ζi) :: ζm)].
    iSplit; last first.
    { iApply (proph_obs_impl with "Obs")=> π Hπ. by apply Hπ. }
    iSplitL "Tok1 Ghζ ⧗".
    { rewrite /tctx_elt_interp. iExists #(lK.1), d0.
      iSplit. { iPureIntro. rewrite /= Hp /lK pctx_loc_fst //. }
      iFrame "⧖0". iSplit; [|done]. iSplit.
      { iApply llftl_incl_trans; [iApply llftl_intersect_incl_l|].
        iApply (llftl_incl_trans with "Incl"). iApply (lty_lft_plug K (OfTy ty)). }
      iSplit; [iPureIntro; lia|]. iSplitL.
      { iExists β, γζ. iFrame "∗#". iApply guards_refl. }
      iApply (guards_transitive_right with "[] [PtBase]"); [iApply llftl_intersect_incl_l|].
      by iApply pctx_loc_guard. }
    iSplit; [|done].
    rewrite /tctx_elt_interp. iExists #(l.1). iSplit; [done|]. iExists d0.
    iFrame "⧖0 PtBase". iSplitL "⧗p ⧗' ⧗''".
    { iApply (cumulative_time_receipt_mono _ (2 * lty_nblk (pctx_plug K (OfTy ty)) + (1 + 1))
        with "[⧗p ⧗' ⧗'']"); [rewrite !lty_nblk_plug /=; lia|].
      rewrite !cumulative_time_receipt_sep. iFrame. }
    iSplit; [done|]. iSplit; [done|].
    iSplit. { by rewrite (lty_fold_plug_eq K (Blocked ty β) (OfTy ty)). }
    rewrite /ltype_own (ltype_own_cp_plug_core false K (Blocked ty β) (OfTy ty)) //.
    rewrite ltype_own_cp_uniq_plug // lty_pat_plug lty_rfn_plug pctx_rfn_blk_cons /=.
    by rewrite decide_True.
  Qed.


  (** Reborrowing a leaf below owned pointers: the address of the hole is computed by
      the program ([pctx_expr], a load per owned pointer), with the borrow of the place
      open. The blocked leaf below [k] owned pointers holds [k] cumulative time receipts,
      to shift the receipt of the contents it gives back (see [blocked_owned]). *)
  Lemma type_reborrow_place_deref_instr {𝔅 𝔄} E L I p κ α (K: pctx 𝔅 𝔄) (ty: type 𝔅) :
    lctx_lft_alive E L κ → pctx_nonempty K →
    typed_instr E L I +[p ◁ₗ{κ} pctx_plug K (OfTy ty)] (Seq (Seq Skip Skip) (pctx_expr K p))
      (λ w, +[w ◁ &uniq{κ ⊓ α} ty; p ◁ₗ{κ} pctx_plug K (Blocked ty (κ ⊓ α))])
      (λ post '-[x], λ mask π, ∀ m1: ~~ (uniq_borₛ 𝔅),
        uniq_bor_loc m1 = pctx_loc K (ty_size ty) (uniq_bor_current (place_bor x))
          (uniq_bor_loc (place_bor x)) →
        uniq_bor_current m1 = pctx_get K (uniq_bor_current (place_bor x)) →
        post -[m1; (place_bor x, (pctx_path K [], uniq_bor_ξi m1) :: place_ζis x)] mask π).
  Proof.
    intros Alv HK tid post mask iκs [x []].
    iIntros "#LFT #TIME #PROPH #UNIQ #E L I [T _] Obs".
    destruct x as [[[[[[l x₀] ξi] d'] g'] idx] ζm].
    rewrite /tctx_elt_interp.
    iDestruct "T" as (v Hp) "(%d0 & #⧖0 & ⧗p & -> & %Hle & #Incl & #PtBase & Own)".
    have ?: Closed [] (pctx_expr K p).
    { apply pctx_expr_closed. by eapply eval_path_closed. }
    (* Two steps, for credits and cumulative time receipts. *)
    wp_bind (Seq Skip Skip). wp_bind Skip. iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME ⧖0"); [set_solver|].
    iIntros "£ #⧖S". wp_let. iModIntro. wp_let. iApply wp_fupd.
    iApply (wp_cumulative_time_receipt_linear with "TIME ⧖0"); [set_solver|].
    iIntros "⧗". wp_let. iModIntro. wp_let.
    set β := κ ⊓ α. set k := pctx_mode K 0.
    iDestruct (Alv with "L E") as "#Alv".
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iDestruct (guards_transitive with "Ghalf Alv") as "#Hκ".
    rewrite /ltype_own ltype_own_cp_uniq_plug //.
    iMod (cpd_acc with "LFT PROPH UNIQ Hκ H1 Own") as (κp) "(#Inclp & #Ok & Upd & Close)";
      [solve_ndisj|].
    iDestruct (lc_weaken (1 + (advance_credits d0 - 1)) with "£") as "[£a £]";
      [rewrite /advance_credits; lia|].
    iMod (lc_fupd_elim_later with "£a Upd") as "Upd".
    iMod (guarded_upd_run with "[] H2 Upd") as "(H2 & #⧖' & N)";
      [rewrite /lazyE; solve_ndisj| |].
    { iApply (guards_transitive with "Hκ Incl"). }
    rewrite lty_pat_plug lty_rfn_plug ltype_own_plug.
    iDestruct "N" as "[L1 Rest]". iSimpl in "L1".
    iDestruct "L1" as (? ->) "[Pt1 Gho1]".
    iDestruct (pctx_own_mode_le with "Rest") as %Hk.
    set y := pctx_get K x₀. set lK := pctx_loc K (ty_size ty) x₀ l.
    set dh := pctx_depth K d'.
    have Hdh: dh ≤ d'. { rewrite /dh pctx_depth_sub. lia. }
    iDestruct (lc_weaken (3 * (d0 + 1) * k + (1 + k)) with "£") as "[£r [£' £k]]";
      [rewrite /advance_credits; nia|].
    iDestruct (cumulative_time_receipt_mono (1 + (2 + k)) with "⧗") as "⧗"; [lia|].
    iDestruct (cumulative_time_receipt_sep with "⧗") as "[⧗u ⧗]".
    iDestruct (cumulative_time_receipt_sep with "⧗") as "[⧗2 ⧗k]".
    (* The address of the hole. *)
    iApply wp_fupd.
    iApply (wp_wand with "[Rest H2 £r]").
    { iApply (wp_pctx_expr K (ty_size ty) 0 x₀ ζm [] d' g' tid l p (fractional.half γh) True
        (d0 + 1) with "[] £r [H2] Rest").
      - iApply (guards_transitive_right with "Hκ PtBase").
      - iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->". by iFrame. }
    iIntros (w) "(-> & _ & H2 & Rest)".
    iMod (lc_fupd_elim_laterN with "£k Gho1") as "Gho1".
    iMod (ghost_var_alloc (lstate_triv y)) as (γζ) "[Ghζ Ghζ']".
    iMod (proph_loan_intro (uniq_cell_tyi y) ⊤ (uniq_cell y dh g' γζ) with "PROPH UNIQ")
      as (ζi) "Loan"; [solve_ndisj|].
    set ζ := uniq_prvar y ζi.
    rewrite proph_loan_unfold. iDestruct "Loan" as "[ζVo ζPc]".
    iDestruct (uniq_proph_tok with "ζVo ζPc") as "(ζVo & ζtok & ToζPc)".
    iAssert (⧖(S dh `max` g'))%I as "#⧖h".
    { iApply (persistent_time_receipt_mono with "⧖'"). lia. }
    iMod ("Close" $! (pctx_pat K (PatBlocked β)) (pctx_rfn K x₀ ζm [] (inl (PlaceGhost y ζi)))
      d' g' [ζ] 1%Qp
      (∃ idx1, proph_bor_tok ζ (uniq_cell y dh g' γζ) idx1 ∗
        proph_idx_bor_gen β ζ idx1 (uniq_gbody β ty tid lK))%I
      with "[] [ζtok] [ζVo ToζPc Ghζ' Pt1 Gho1 Rest £' ⧗k]") as "(Own & H1 & Bor1)".
    { iPureIntro. intros ζl Hr. eapply pctx_rfn_rsv; [|exact Hr|]; [set_solver|].
      rewrite prfn_rsv_inl. apply place_ghost_rsv_elem. set_solver. }
    { by rewrite big_sepL_singleton. }
    { iIntros "ζtok". rewrite big_sepL_singleton.
      iDestruct ("ToζPc" with "ζtok") as "ζPc".
      iMod (proph_loan_borrow_gen_pc ⊤ β ζ (uniq_cell y dh g' γζ)
        (vπ (uniq_cell y dh g' γζ)) (uniq_gbody β ty tid lK)
        with "LFT UNIQ [ζVo ζPc] [Ghζ' Pt1 Gho1]") as (idx1) "(Tok1 & #Bor1 & Back1)";
        [solve_ndisj| by rewrite proph_loan_unfold; iFrame| |].
      { iApply (uniq_gbody_triv_close with "Ghζ'"); [done|].
        iApply uniq_payload_intro_later. iNext. iFrame "⧖h Gho1 Pt1". }
      iModIntro. iSplitR; [|iSplitR "Tok1"; [|iExists idx1; by iFrame "Tok1 Bor1"]].
      { iNext. iApply (pat_ok_plug with "Ok"). iApply pat_ok_blocked.
        iApply (llftl_incl_trans with "[] Inclp"). iApply llftl_intersect_incl_l. }
      iNext. iApply guarded_upd_intro. iModIntro. iFrame "⧖'".
      rewrite ltype_own_plug. iFrame "Rest".
      rewrite /= /leaf_owned /blocked_owned. iIntros "#†α".
      iMod (fupd_mask_mono with "(Back1 †α)") as "Lender"; [rewrite /lazyE; solve_ndisj|].
      iMod (lc_fupd_elim_later with "£' Lender") as "Lender". iModIntro.
      iApply (guarded_upd_mono with "[⧗k] [Lender]");
        [|iApply (uniq_lender_settle with "LFT PROPH †α Lender")].
      iIntros "(%x & %d1 & %g1 & Eqz & #⧖1 & Gho & Pt)".
      iMod (cumulative_persistent_time_receipt with "TIME ⧗k ⧖1") as "#⧖1'";
        [rewrite /lazyE; solve_ndisj|].
      iModIntro. iExists x, d1, g1. rewrite /ofty_owned /=. iFrame "Eqz Pt Gho".
      iApply (persistent_time_receipt_mono with "⧖1'"). lia. }
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "$"; [solve_ndisj|].
    iDestruct "Bor1" as (idx1) "[Tok1 #Bor1]".
    iModIntro.
    iExists -[(lK, y, ζi, dh, g', idx1); ((l, x₀, ξi, d', g', idx), (pctx_path K [], ζi) :: ζm)].
    iFrame "I". iSplit; last first.
    { iApply (proph_obs_impl with "Obs")=> π Hπ. by apply Hπ. }
    iSplitL "Tok1 Ghζ ⧗u".
    { iExists #(lK.1), d0. iSplit; [done|]. iFrame "⧖0". iSplit; [|done]. iSplit.
      { iApply llftl_incl_trans; [iApply llftl_intersect_incl_l|].
        iApply (llftl_incl_trans with "Incl"). iApply (lty_lft_plug K (OfTy ty)). }
      iSplit; [iPureIntro; lia|]. iSplitL.
      { iExists β, γζ. iFrame "∗#". iApply guards_refl. }
      iApply (guards_transitive_right with "[] [PtBase]"); [iApply llftl_intersect_incl_l|].
      by iApply pctx_loc_guard. }
    iSplit; [|done].
    rewrite /tctx_elt_interp. iExists #(l.1). iSplit; [done|]. iExists d0.
    iFrame "⧖0 PtBase". iSplitL "⧗p ⧗2".
    { iApply (cumulative_time_receipt_mono _ (2 * lty_nblk (pctx_plug K (OfTy ty)) + 2)
        with "[⧗p ⧗2]"); [rewrite !lty_nblk_plug /=; lia|].
      rewrite !cumulative_time_receipt_sep. iFrame. }
    iSplit; [done|]. iSplit; [done|].
    iSplit. { by rewrite (lty_fold_plug_eq K (Blocked ty β) (OfTy ty)). }
    rewrite /ltype_own (ltype_own_cp_plug_core false K (Blocked ty β) (OfTy ty)) //.
    rewrite ltype_own_cp_uniq_plug // lty_pat_plug lty_rfn_plug pctx_rfn_blk_cons /=.
    by rewrite decide_True.
  Qed.


  (** * Writing a leaf directly *)

  (** Writing a value of size 1 to the leaf at the hole of [K] (not below an owned
      pointer), without reborrowing: the borrow of the place is opened around the
      write, the old value is resolved, and the place is closed at the new value. *)
  Lemma type_write_place_instr {𝔅 𝔄} E L I p pb κ (K: pctx 𝔅 𝔄) (ty: type 𝔅) Φ :
    lctx_lft_alive E L κ → pctx_nonempty K → pctx_noderef K → ty_size ty = 1%nat →
    resolve E L ty Φ →
    typed_instr E L I +[p ◁ₗ{κ} pctx_plug K (OfTy ty); pb ◁ ty] (p +ₗ #(pctx_off K) <- pb)
      (λ _, +[p ◁ₗ{κ} pctx_plug K (OfTy ty)])
      (λ post '-[x; b], λ mask π, Φ (pctx_get K (uniq_bor_current (place_bor x))) π →
        ∀ x': ~~ (placeₛ 𝔄),
        uniq_bor_loc (place_bor x') = uniq_bor_loc (place_bor x) →
        uniq_bor_current (place_bor x') = pctx_set K (uniq_bor_current (place_bor x)) b →
        uniq_bor_future (place_bor x') π = uniq_bor_future (place_bor x) π →
        place_ζis x' = place_ζis x → post -[x'] mask π).
  Proof.
    iIntros (Alv HK HKd Hsz Rslv tid post mask iκs [x [b []]])
      "#LFT #TIME #PROPH #UNIQ #E L I (Tp & Tb & _) Obs".
    destruct x as [[[[[[l x₀] ξi] d'] g'] idx] ζm].
    rewrite /tctx_elt_interp.
    iDestruct "Tp" as (v Hp) "(%d0 & #⧖0 & ⧗p & -> & %Hle & #Incl & #PtBase & Own)".
    iDestruct "Tb" as (vb db Hpb) "(#⧖b & Gb & %Phys)".
    wp_bind (p +ₗ #(pctx_off K))%E.
    iApply wp_wand; [iApply (wp_eval_path _ _ #(l.1 +ₗ pctx_off K)); by rewrite /= Hp|].
    iIntros (?) "->". wp_bind pb. iApply wp_wand; [by iApply wp_eval_path|].
    iIntros (?) "->".
    iCombine "⧖0 ⧖b" as "⧖m".
    iApply (wp_persistent_time_receipt with "TIME ⧖m"); [solve_ndisj|].
    iIntros "£ #⧖S". iApply wp_fupd.
    iDestruct (Alv with "L E") as "#Alv".
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iDestruct (guards_transitive with "Ghalf Alv") as "#Hκ".
    iDestruct (lc_weaken (1 + (1 + d'*(g'+1)) + 3 * (d0 + 1))%nat with "£")
      as "[[£a [£r £s]] £w]"; [rewrite /advance_credits; nia|].
    rewrite /ltype_own ltype_own_cp_uniq_plug //.
    iMod (cpd_acc with "LFT PROPH UNIQ Hκ H1 Own") as (κp) "(#Inclp & #Ok & Upd & Close)";
      [solve_ndisj|].
    iMod (lc_fupd_elim_later with "£a Upd") as "Upd".
    iMod (guarded_upd_run with "[] H2 Upd") as "(H2 & #⧖' & N)";
      [rewrite /lazyE; solve_ndisj| |].
    { iApply (guards_transitive with "Hκ Incl"). }
    rewrite lty_pat_plug lty_rfn_plug ltype_own_plug pctx_mode_noderef // pctx_depth_noderef //.
    iDestruct "N" as "[L1 Rest]". iSimpl in "L1".
    iDestruct "L1" as (? ->) "[Pt1 Gho1]".
    iDestruct (pctx_own_in with "Rest") as %Hin.
    set y := pctx_get K x₀. set lK := pctx_loc K (ty_size ty) x₀ l.
    (* Resolve the old value. *)
    iDestruct (Rslv _ (⊤ ∖ (⊤ ∖ ↑Nllft ∖ ↑prophN ∖ ↑timeN ∖ ↑uniqN))
      with "LFT PROPH UNIQ TIME E Ghalf H2 Gho1") as "ToObs"; [set_solver|].
    iMod (lc_fupd_elim_later with "£r ToObs") as "ToObs".
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iDestruct (lc_step_fupdN_elim_later with "£s ToObs") as "ToObs".
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iMod (fupd_mask_mono with "ToObs") as "[Obs' H2]"; [solve_ndisj|].
    (* Write. *)
    have Hlen: length (ty_phys ty y tid) = 1%nat by rewrite ty_size_eq.
    destruct (ty_phys ty y tid) as [|fv [|]] eqn:Hphys; [done| |done].
    iMod (mapsto_vec_untether_singleton _ _ _ ∅ with "Pt1") as (v₀ l₀ c₀) "[%HlK [Pt1 _]]".
    iAssert (fractional.half γh &&{↑NllftG; d0 + 1}&&> (l₀, c₀) #↦_)%I as "#Gw".
    { rewrite -heap_complete_mapsto_singleton -HlK.
      iApply (pctx_loc_guard with "[]"). iApply (guards_transitive_right with "Hκ PtBase"). }
    have Hl0: l.1 +ₗ pctx_off K = l₀.
    { by rewrite -(pctx_loc_fst K (ty_size ty) x₀) // -/lK HlK. }
    rewrite Hl0.
    iApply (wp_write_na_guarded _ l₀ c₀ _ vb v₀ (d0 + 1) (fractional.half γh)
      with "[H2 Pt1 £w]"); [solve_ndisj| |].
    { iSplit; [iExact "Gw"|]. iFrame "H2 Pt1 £w". }
    iNext. iIntros "[Pt1 H2]".
    (* Close the place at the new value. *)
    set d'' := d' `max` db. set g'' := g' `max` db.
    iDestruct (ty_gho_own_depth_mono _ db db d'' g'' with "Gb") as "[Gb _]"; [lia..|].
    iDestruct (pctx_own_depth_mono _ _ _ _ _ _ _ _ d'' g'' with "Rest") as "Rest"; [lia..|].
    iAssert (⧖(S d'' `max` g''))%I as "#⧖''".
    { iCombine "⧖' ⧖S" as "⧖". iApply (persistent_time_receipt_mono with "⧖"). lia. }
    iMod ("Close" $! (pctx_pat K PatLeaf) (pctx_rfn K x₀ ζm [] (inl (PlaceIn b)))
      d'' g'' [] 1%Qp True%I with "[] [] [Pt1 Gb Rest]") as "(Own & H1 & _)".
    { iPureIntro. intros ζl Hr. eapply pctx_rfn_rsv; [|exact Hr|apply prfn_rsv_in].
      set_solver. }
    { done. }
    { iIntros "_". iModIntro. iSplitR.
      { iNext. iApply (pat_ok_plug with "Ok"). iApply pat_ok_leaf. }
      iSplitL; [|done].
      iNext. iApply guarded_upd_intro. iModIntro. iFrame "⧖''".
      rewrite ltype_own_plug pctx_mode_noderef // pctx_depth_noderef //. iFrame "Rest".
      iExists b. iSplit; [done|]. rewrite /ofty_owned Phys.
      rewrite (_: pctx_loc K (lty_size (OfTy ty)) x₀ l = (l₀, [c₀])); [|exact HlK].
      iFrame "Gb".
      by rewrite heap_complete_mapsto_fancy_singleton. }
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "$"; [solve_ndisj|].
    iCombine "⧖0 ⧖''" as "⧖D".
    iModIntro. iExists -[((l, pctx_set K x₀ b, ξi, d'', g'', idx), ζm)]. iFrame "I".
    iSplitR "Obs Obs'".
    { iSplit; [|done]. rewrite /tctx_elt_interp. iExists #(l.1). iSplit; [done|].
      iExists (d0 `max` (S d'' `max` g'')). iFrame "⧖D ⧗p Incl".
      iSplit; [done|]. iSplit; [iPureIntro; lia|].
      iSplitR. { iApply (lguards_weaken_later with "PtBase"). lia. }
      rewrite /ltype_own ltype_own_cp_uniq_plug // lty_pat_plug lty_rfn_plug pctx_get_set
        pctx_rfn_set //. }
    iCombine "Obs Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=> π [Hπ HΦ].
    apply Hπ; [exact HΦ|done|done| |done].
    rewrite !uniq_bor_future_eq. apply (uniq_prvar_app_irrel _ x₀).
  Qed.


  (** Reading (copying) a value of size 1 out of the leaf at the hole of [K] (not below an
      owned pointer), without reborrowing. *)
  Lemma type_read_place_instr {𝔅 𝔄} E L I p κ (K: pctx 𝔅 𝔄) (ty: type 𝔅) :
    lctx_lft_alive E L κ → pctx_nonempty K → pctx_noderef K → ty_size ty = 1%nat → Copy ty →
    typed_instr E L I +[p ◁ₗ{κ} pctx_plug K (OfTy ty)] (!(p +ₗ #(pctx_off K)))
      (λ v, +[v ◁ ty; p ◁ₗ{κ} pctx_plug K (OfTy ty)])
      (λ post '-[x], post -[pctx_get K (uniq_bor_current (place_bor x)); x]).
  Proof.
    iIntros (Alv HK HKd Hsz Hcopy tid post mask iκs [x []])
      "#LFT #TIME #PROPH #UNIQ #E L I (Tp & _) Obs".
    destruct x as [[[[[[l x₀] ξi] d'] g'] idx] ζm].
    rewrite /tctx_elt_interp.
    iDestruct "Tp" as (v Hp) "(%d0 & #⧖0 & ⧗p & -> & %Hle & #Incl & #PtBase & Own)".
    wp_bind (p +ₗ #(pctx_off K))%E.
    iApply wp_wand; [iApply (wp_eval_path _ _ #(l.1 +ₗ pctx_off K)); by rewrite /= Hp|].
    iIntros (?) "->".
    iApply (wp_persistent_time_receipt with "TIME ⧖0"); [solve_ndisj|].
    iIntros "£ #⧖S". iApply wp_fupd.
    iDestruct (Alv with "L E") as "#Alv".
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iDestruct (guards_transitive with "Ghalf Alv") as "#Hκ".
    iDestruct (lc_weaken (1 + 3 * (d0 + 1))%nat with "£") as "[£a £r]";
      [rewrite /advance_credits; nia|].
    rewrite /ltype_own ltype_own_cp_uniq_plug //.
    iMod (cpd_acc with "LFT PROPH UNIQ Hκ H1 Own") as (κp) "(#Inclp & #Ok & Upd & Close)";
      [solve_ndisj|].
    iMod (lc_fupd_elim_later with "£a Upd") as "Upd".
    iMod (guarded_upd_run with "[] H2 Upd") as "(H2 & #⧖' & N)";
      [rewrite /lazyE; solve_ndisj| |].
    { iApply (guards_transitive with "Hκ Incl"). }
    rewrite lty_pat_plug lty_rfn_plug ltype_own_plug pctx_mode_noderef // pctx_depth_noderef //.
    iDestruct "N" as "[L1 Rest]". iSimpl in "L1".
    iDestruct "L1" as (? ->) "[Pt1 #Gho1]".
    set y := pctx_get K x₀. set lK := pctx_loc K (ty_size ty) x₀ l.
    iDestruct (copy_concrete with "Gho1") as %Hconc.
    have Hlen: length (ty_phys ty y tid) = 1%nat by rewrite ty_size_eq.
    destruct (ty_phys ty y tid) as [|fv [|]] eqn:Hphys; [done| |done].
    destruct fv as [w|]; [|by destruct Hconc].
    have Hl0: (l.1 +ₗ pctx_off K) = lK.1 by rewrite /lK pctx_loc_fst.
    rewrite Hl0.
    iApply (wp_read_na_guarded_cells_singleton _ lK.1 lK.2
      (fractional.half γh ∗ pctx_loc K (lty_size (OfTy ty)) x₀ l #↦!∗ [FVal w]) w (d0 + 1)
      with "[H2 Pt1 £r]"); [solve_ndisj| |].
    { iFrame "H2 Pt1 £r". iApply guard_cloc_combine.
      - iApply guards_weaken_lhs_sep_l. iApply (pctx_loc_guard with "[]").
        iApply (guards_transitive_right with "Hκ PtBase").
      - iApply (lguards_weaken_later _ _ _ 0); [lia|iApply guards_weaken_sep_r]. }
    iIntros "!> [H2 Pt1]".
    iMod ("Close" $! (pctx_pat K PatLeaf) (pctx_rfn K x₀ ζm [] (inl (PlaceIn y)))
      d' g' [] 1%Qp True%I with "[] [] [Pt1 Rest]") as "(Own & H1 & _)".
    { iPureIntro. intros ζl Hr. by apply prfn_rsv_app_l. }
    { done. }
    { iIntros "_". iModIntro. iSplitR; [done|]. iSplitL; [|done].
      iNext. iApply guarded_upd_intro. iModIntro. iFrame "⧖'".
      rewrite ltype_own_plug pctx_mode_noderef // pctx_depth_noderef //. iFrame "Rest".
      iExists y. iSplit; [done|]. rewrite /ofty_owned Hphys. by iFrame "Pt1 Gho1". }
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "$"; [solve_ndisj|].
    iModIntro. iExists -[y; ((l, x₀, ξi, d', g', idx), ζm)]. iFrame "I Obs".
    iSplitR "Own ⧗p".
    { iExists w, (d' `max` g'). iSplit; [by rewrite eval_path_of_val|].
      iSplit. { iApply (persistent_time_receipt_mono with "⧖'"). lia. }
      iSplit; [|done].
      iDestruct (ty_gho_own_depth_mono _ d' g' (d' `max` g') (d' `max` g') with "Gho1")
        as "[$ _]"; lia. }
    iSplit; [|done]. iExists #(l.1). iSplit; [done|]. iExists d0. iFrame "⧖0 ⧗p Incl PtBase".
    iSplit; [done|]. iSplit; [done|].
    by rewrite /ltype_own ltype_own_cp_uniq_plug // lty_pat_plug lty_rfn_plug.
  Qed.

  (** * Unblocking a leaf *)

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

  (** Once [κ ⊓ α] has ended (by ending [α]), the leaf at the hole of [K] is unblocked:
      it gets the final contents of its reborrow, whose value is the final value of the
      reborrow. The current value of the place only changes at the hole. Unblocking pays
      with the two cumulative time receipts of the blocked leaf. *)
  Lemma unblock_tctx_place {𝔅 𝔄 𝔄l 𝔄l'} p κ α (K: pctx 𝔅 𝔄) (ty: type 𝔅)
      (T: tctx 𝔄l) (T': tctx 𝔄l') E L f :
    lctx_lft_alive E L κ → pctx_nonempty K → unblock_tctx E L α T T' f →
    unblock_tctx E L α (p ◁ₗ{κ} pctx_plug K (Blocked ty (κ ⊓ α)) +:: T)
      (p ◁ₗ{κ} pctx_plug K (OfTy ty) +:: T')
      (λ π '(x -:: xl), λ '(x' -:: xl'),
        uniq_bor_loc (place_bor x') = uniq_bor_loc (place_bor x) ∧
        uniq_bor_future (place_bor x') π = uniq_bor_future (place_bor x) π ∧
        uniq_bor_current (place_bor x') = pctx_set K (uniq_bor_current (place_bor x))
          (pctx_get K (uniq_bor_current (place_bor x'))) ∧
        place_ζis x' = place_ζis x ∧
        vπ (pctx_get K (uniq_bor_current (place_bor x'))) π = place_blk_fin K x π ∧
        f π xl xl').
  Proof.
    iIntros (Alv HK Un G tid [x xl] ?) "#LFT #TIME #PROPH #UNIQ #E #L G #†α /=[(%v & %Hp & Own) T]".
    destruct x as [[[[[[l x₀] ξi] d'] g'] idx] ζm].
    set β := κ ⊓ α.
    iDestruct "Own" as (d0) "(#⧖0 & ⧗ & -> & %Hle & #Incl & #PtBase & Own)".
    iDestruct (cumulative_time_receipt_mono (2 * lty_nblk (pctx_plug K (OfTy ty)) + (1 + 1))
      with "⧗") as "⧗"; [rewrite !lty_nblk_plug /=; lia|].
    iDestruct (cumulative_time_receipt_sep with "⧗") as "[⧗r ⧗]".
    iDestruct (cumulative_time_receipt_sep 1 1 with "⧗") as "[⧗a ⧗b]".
    rewrite (lty_fold_plug_eq K (Blocked ty β) (OfTy ty)) //.
    leaf_open "L" with "G" as "[L1 back]"; [set_solver|].
    iDestruct (Alv with "L1 E") as "#Lκ". iMod ("back" with "L1") as "G".
    (* Half of [G] for the rest of the context, the other half for the place. *)
    iMod (fractional.frac_split_guard_in_half with "G L") as (γ1) "[GT [GP [#GhT #BackT]]]";
      [solve_ndisj|].
    iMod (Un with "LFT TIME PROPH UNIQ E GhT GT †α T") as (dT xl') "[#⧖T ToT']".
    iDestruct (guards_transitive with "GhT Lκ") as "#GPκ".
    iMod (fractional.frac_split_guard_in_half with "GP GPκ") as (γ2) "[H1 [H2 [#Gh2 #Back2]]]";
      [solve_ndisj|].
    iAssert (fractional.half γ2 &&{↑NllftG}&&> @[ty_lft ty])%I as "#Gty".
    { iApply (guards_transitive with "Gh2"). iApply (llftl_incl_trans with "Incl").
      iApply (lty_lft_plug K (OfTy ty)). }
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗a ⧖0") as "[_ £]";
      [solve_ndisj|].
    iDestruct (lc_weaken 1 with "£") as "£"; [rewrite /advance_credits; lia|].
    rewrite /ltype_own (ltype_own_cp_plug_core false K (Blocked ty β) (OfTy ty)) //.
    rewrite ltype_own_cp_uniq_plug //.
    iMod (cpd_acc with "LFT PROPH UNIQ Gh2 H1 Own") as (κp) "(#Inclp & #Ok & Upd & Close)";
      [solve_ndisj|].
    iMod (lc_fupd_elim_later with "£ Upd") as "Upd".
    iMod (guarded_upd_run with "[] H2 Upd") as "(H2 & #⧖' & N)";
      [rewrite /lazyE; solve_ndisj| |].
    { iApply (guards_transitive with "Gh2 Incl"). }
    rewrite lty_pat_plug lty_rfn_plug ltype_own_plug.
    iDestruct "N" as "[L1 Rest]". iSimpl in "L1".
    iDestruct (pctx_own_in with "Rest") as %Hin.
    set y := pctx_get K x₀. set ζi := blk_lookup ζm (pctx_path K []).
    set k := pctx_mode K 0.
    (* Unblock the leaf: fire the inheritance of the reborrow and settle it. *)
    iAssert ([†β])%I as "#†β". { rewrite llftl_end_inter. by iRight. }
    iMod (fupd_mask_mono with "(L1 †β)") as "Upd1"; [rewrite /lazyE; solve_ndisj|].
    iMod (guarded_upd_run with "Gty H2 Upd1") as "(H2 & %y1 & %d1 & %g1 & Eqz & #⧖1 & O1)";
      [rewrite /lazyE; solve_ndisj|].
    iDestruct "O1" as "[Pt1 Gho1]".
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗b ⧖1") as "[_ £]";
      [solve_ndisj|].
    set m := (k + S d1) `max` g1.
    have Hm: k + S d1 ≤ m ∧ g1 ≤ m by lia.
    iDestruct (lc_weaken (k + (1 + (d1 + d1*(g1+2) + (0 + (d1+1)*(g1+1)) + 1 + 1))) with "£")
      as "[£k [£e £]]"; [rewrite /advance_credits; nia|].
    iMod (lc_fupd_elim_laterN with "£k Gho1") as "Gho1".
    iSimpl in "Eqz". iMod (lc_fupd_elim_later with "£e Eqz") as "Eqz".
    iMod (proph_eqz_obs_by_share ty with "LFT Gty H2 £ Eqz Gho1") as "(#Obs1 & H2 & Gho1)".
    (* Close the outer borrow at the unblocked state, at the maximal depths. *)
    set d'' := (d1 + k) `max` d'. set g'' := g1 `max` g'.
    have Hdh: d1 ≤ pctx_depth K d''. { rewrite pctx_depth_sub. lia. }
    iDestruct (ty_gho_own_depth_mono _ d1 g1 (pctx_depth K d'') g'' with "Gho1")
      as "[Gho1 _]"; [lia..|].
    iDestruct (pctx_own_depth_mono _ _ _ _ _ _ _ _ d'' g'' with "Rest") as "Rest"; [lia..|].
    iAssert (⧖(S d'' `max` g''))%I as "#⧖''".
    { iCombine "⧖' ⧖1" as "⧖". iApply (persistent_time_receipt_mono with "⧖"). lia. }
    iMod ("Close" $! (pctx_pat K PatLeaf) (pctx_rfn K x₀ ζm [] (inl (PlaceIn y1)))
      d'' g'' [] 1%Qp True%I with "[] [] [Pt1 Gho1 Rest]") as "(Own & H1 & _)".
    { iPureIntro. intros ζl Hr. eapply pctx_rfn_rsv; [|exact Hr|apply prfn_rsv_in].
      set_solver. }
    { done. }
    { iIntros "_". iModIntro. iSplitR.
      { iNext. iApply (pat_ok_plug with "Ok"). iApply pat_ok_leaf. }
      iSplitL; [|done].
      iNext. iApply guarded_upd_intro. iModIntro. iFrame "⧖''".
      rewrite ltype_own_plug. iFrame "Rest".
      iExists y1. by iFrame. }
    iMod (fupd_mask_mono with "(Back2 H1 H2)") as "GP"; [solve_ndisj|].
    iCombine "⧖0 ⧖''" as "⧖D".
    iModIntro. iExists dT, (((l, pctx_set K x₀ y1, ξi, d'', g'', idx), ζm) -:: xl').
    iSplitR; [done|].
    iMod "ToT'". iModIntro. iNext. iMod "ToT'". iModIntro.
    iApply (step_fupdN_wand with "ToT'"). iIntros ">(GT & T' & #Obs')".
    iMod (fupd_mask_mono with "(BackT GT GP)") as "$"; [solve_ndisj|].
    iModIntro. iSplitR "Obs'".
    { iFrame "T'". rewrite /tctx_elt_interp. iExists #(l.1). iSplit; [done|].
      iExists (d0 `max` (S d'' `max` g'')). iFrame "⧖D ⧗r Incl".
      iSplit; [done|]. iSplit; [iPureIntro; lia|].
      iSplitR. { iApply (lguards_weaken_later with "PtBase"). lia. }
      rewrite /ltype_own ltype_own_cp_uniq_plug // lty_pat_plug lty_rfn_plug pctx_get_set
        pctx_rfn_set //. }
    iCombine "Obs1 Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=> π [Heq Hf].
    split; [done|]. split.
    { rewrite !uniq_bor_future_eq. apply (uniq_prvar_app_irrel _ x₀). }
    split; [by rewrite /= pctx_get_set|]. split; [done|]. split; [|done].
    rewrite /place_blk_fin /= pctx_get_set. symmetry. exact Heq.
  Qed.

  (** * Dropping the outer borrow while all leaves are blocked *)

  (** The outer borrow is given up while all leaves of the (compound) place are blocked
      (also the leaves of nested places, [UniqLty]): its prophecy variable is
      pre-resolved (through its reservation, without tokens) to the current value of the
      place, i.e. the final values of the reborrows of the leaves (and, for a nested
      place, the final value of the nested borrow, for which the outer one is reserved,
      see [type_unfold_place_uniq_instr]). The lender gets the body back when [κ] ends,
      as usual. To drop a place with some unblocked leaves, these are first reborrowed
      (e.g. at [κ ⊓ κ]). *)
  Lemma tctx_drop_place_cpd {𝔄} E L p κ (lt: lty 𝔄) :
    lctx_lft_alive E L κ → lty_is_cpd lt → lty_blk_all lt →
    tctx_incl E L +[p ◁ₗ{κ} lt] +[]
      (λ post '-[x], λ mask π,
        uniq_bor_future (place_bor x) π = place_cur lt x π → post -[] mask π).
  Proof.
    intros Alv Hc Hb. split.
    { intros ?? Eq [? []] ??. split=> H ?; apply Eq, H; done. }
    iIntros (G tid [x []] mask post ?) "#LFT #PROPH #UNIQ #E #GL G [T _] Obs".
    destruct x as [[[[[[l x₀] ξi] d'] g'] idx] ζm].
    rewrite /tctx_elt_interp. iDestruct "T" as (v ?) "(%d & ⧖ & _ & -> & %Hle & #Incl & #Pt & Own)".
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
    iMod (proph_idx_bor_gen_preresolve_rsv ⊤ κ (uniq_prvar x₀' ξi) (uniq_cell x₀' d' g' γ) idx'
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

  Lemma tctx_drop_place {𝔄1 𝔄2} E L p κ (lt1: lty 𝔄1) (lt2: lty 𝔄2) :
    lctx_lft_alive E L κ → lty_blk_all lt1 → lty_blk_all lt2 →
    tctx_incl E L +[p ◁ₗ{κ} ProdLty lt1 lt2] +[]
      (λ post '-[x], λ mask π,
        uniq_bor_future (place_bor x) π = place_cur (ProdLty lt1 lt2) x π → post -[] mask π).
  Proof. intros. by apply tctx_drop_place_cpd. Qed.
End typing.
