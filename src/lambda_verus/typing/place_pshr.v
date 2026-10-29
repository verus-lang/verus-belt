(** * Owned places below shared references

  The referent of a shared reference [&shr{κ}] in an owned place ([p ◁ₗown{n} …],
  [place_own.v]) is a context step [PShr κ K] ([lpath.v]): the place type [ShrLty lt κ]
  ([ltype.v]) is the leaf of [&shr{κ} (lty_fold lt)] together with the variants of the
  sums of [lt] at the (unchanging) referent ([lty_vin]). Nothing below a shared reference
  is owned, blocked or written; the referent is only _viewed_, through the (persistent,
  structural) sharing predicates of its folded type.

  A context with a [PShr] step is written [K1[ShrLty (K2[lt]) κ]], with [PctxNoShr K1]
  (the first [PShr] step; [K2] is arbitrary). The address of the hole is
  [pctx_expr K2 (!(pctx_expr K1 p))].

  - Phase 1 (the owned part [K1], [wp_pshr_addr]): the access of [pctx_acc.v] to the
    [ShrLty] leaf (in [Owned] or [Uniq] mode, below any number of unique borrows), the load
    of the pointer of the shared reference, and a copy of its persistent ownership
    predicate; the access is closed again with the same leaf. (The leaf need not be
    blocked: its ownership is persistent.)
  - Phase 2 (the shared part [K2]): the _shared view_ ([shr_view]: a guard of the cells,
    the sharing predicate and the persistent predicate) is pushed through [K2]
    ([shr_pctx_view]): fields and sums split it, an owned pointer steps into its pointee,
    a unique borrow at [κ'] continues at [κ ⊓ κ'] and a shared reference at [κ'] at [κ']
    ([pctx_slft]); the pointers on the path are loaded with the guards of the views
    ([pctx_sguards], [wp_pctx_sexpr]), for which all lifetimes on the path must be alive
    ([pctx_salv]).

  Rules:
  - (a) [type_(un)fold_oplace_shr_instr]: [OfTy (&shr{κ} ty)] ↔ [ShrLty (OfTy ty) κ] at the
    hole of any [K] (both modes), and [type_change_oplace_shr_instr]: changing the
    referent place type of a [ShrLty] for one with the same folded type and fewer
    variant constraints (unfolding pairs, boxes, unique borrows and shared references
    below [PShr]), instances of [type_change_oplace_instr];
  - (b) [type_read_oplace_pshr_instr]: copy of a leaf of size 1 below [PShr];
  - (c) [type_share_oplace_pshr_instr]: a shared reference to a sub-place below [PShr]
    at [pctx_slft K2 κ];
  - (d) [type_case_oplace_pshr]: case analysis on a sum below [PShr], recording the
    variant in the place type;
  - (e) resolve/drop: a [ShrLty] is a leaf ([lty_resolve_just], [lty_rslv_shr]).
  - [type_read_oplace_shr_deep_instr]: reading a shared-blocked leaf below unique borrows
    (the leaf of [type_share_oplace_deep_instr]).

  See [~/verus-belt-phase3-design.md], section "PShr". *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From lrust.lang Require Import proofmode.
From lrust.typing Require Export type ltype lpath pctx_acc vplace place_own.
From lrust.typing Require Import type_context programs programs_util lft_contexts
  uniq_util uniq_bor product own shr_bor sum type_sum freeable_util place_shr
  place_resolve place_puniq place_sum.
From lrust.util Require Import proph_bor.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

(** * Shared views *)

Section shr_view.
  Context `{!typeG Σ}.

  (** The shared view of the value [y] of type [ty] at [l], at the lifetime [κ]: the
      ownership predicate of [&shr{κ} ty] without its laters. *)
  Definition shr_view {𝔄} (κ: lft) (ty: type 𝔄) (y: ~~𝔄) (d g: nat) (tid: thread_id)
      (l: cloc) : iProp Σ :=
    (@[κ] &&{↑NllftG; g+1}&&> l.1 ↦[^ l.2]!∗ ty.(ty_phys) y tid) ∗
    ty.(ty_shr) κ y d g tid ∗ ty.(ty_gho_pers) y d g tid.

  Global Instance shr_view_persistent {𝔄} κ (ty: type 𝔄) y d g tid l :
    Persistent (shr_view κ ty y d g tid l) := _.

  Lemma shr_view_depth_mono {𝔄} κ (ty: type 𝔄) y d g d' g' tid l :
    d ≤ d' → g ≤ g' → shr_view κ ty y d g tid l -∗ shr_view κ ty y d' g' tid l.
  Proof.
    iIntros (??) "#(Pt & Shr & Pers)". iSplit; [iApply (lguards_weaken_later with "Pt"); lia|].
    iSplit; [by iApply (ty_shr_depth_mono with "Shr")|].
    by iApply (ty_gho_pers_depth_mono with "Pers").
  Qed.

  (** The ownership predicate of a shared reference gives the shared view of its
      referent, after [g+1] laters. *)
  Lemma shr_bor_gho_view {𝔄} κ (ty: type 𝔄) (l: cloc) y d g tid :
    (shr_bor κ ty).(ty_gho_own) (l, y) d g tid -∗
      ⌜d ≠ 0%nat⌝ ∗ ▷^(g+1) shr_view κ ty y (pred d) g tid l.
  Proof.
    destruct d as [|d]; [by iIntros "[]"|]. iIntros "#(Pt & Shr & Pers)".
    iSplit; [done|]. iNext. by iFrame "Pt Shr Pers".
  Qed.

  (** And back. *)
  Lemma shr_bor_gho_of_view {𝔄} κ (ty: type 𝔄) (l: cloc) y d g tid :
    shr_view κ ty y d g tid l -∗ (shr_bor κ ty).(ty_gho_own) (l, y) (S d) g tid.
  Proof. iIntros "#(Pt & Shr & Pers)". iFrame "Pt Shr". by iNext. Qed.

  Lemma xsum_shr_pinj {𝔄l} (tyl: typel 𝔄l) i κ x0 pad d g tid :
    ty_shr (Σ! tyl) κ (pinj i x0, pad) d g tid ⊣⊢ ty_shr (tyl +!! i) κ x0 d g tid.
  Proof. rewrite [ty_shr (Σ! tyl)]/ty_shr /xsum_ty /=. by rewrite to_xsum_pinj. Qed.

  Lemma xsum_pers_pinj {𝔄l} (tyl: typel 𝔄l) i x0 pad d g tid :
    ty_gho_pers (Σ! tyl) (pinj i x0, pad) d g tid ⊣⊢ ty_gho_pers (tyl +!! i) x0 d g tid.
  Proof. rewrite [ty_gho_pers (Σ! tyl)]/ty_gho_pers /xsum_ty /=. by rewrite to_xsum_pinj. Qed.
End shr_view.

(** * Paths below a shared reference *)

Section pctx_shr.
  Context `{!typeG Σ}.

  (** The lifetime of the shared view of the hole of [K], below a shared reference at
      [κ]: a unique borrow at [κ'] gives [κ ⊓ κ'] (its sharing predicate), a shared
      reference at [κ'] gives [κ'] (its ownership predicate is persistent). *)
  Fixpoint pctx_slft {𝔅 𝔄} (K: pctx 𝔅 𝔄) (κ: lft) : lft :=
    match K with
    | PHole => κ
    | PFst K _ | PSnd _ K | POwn _ K | PSum _ _ _ K => pctx_slft K κ
    | PUniq κ' K => pctx_slft K (κ ⊓ κ')
    | PShr κ' K => pctx_slft K κ'
    end.

  (** The lifetimes that must be alive to load the pointers on the path (and the hole):
      their intersection. *)
  Fixpoint pctx_salv {𝔅 𝔄} (K: pctx 𝔅 𝔄) (κ: lft) : lft :=
    match K with
    | PHole => κ
    | PFst K _ | PSnd _ K | POwn _ K | PSum _ _ _ K => pctx_salv K κ
    | PUniq κ' K => pctx_salv K (κ ⊓ κ')
    | PShr κ' K => κ ⊓ pctx_salv K κ'
    end.

  Lemma pctx_salv_incl {𝔅 𝔄} (K: pctx 𝔅 𝔄) κ : ⊢ pctx_salv K κ ⊑ κ.
  Proof.
    induction K in κ |- *; simpl; [iApply guards_refl|by iApply IHK|by iApply IHK|by iApply IHK|
      by iApply IHK| |].
    - iApply llftl_incl_trans; [iApply IHK|]. iApply llftl_intersect_incl_l.
    - iApply llftl_intersect_incl_l.
  Qed.

  Lemma pctx_salv_slft {𝔅 𝔄} (K: pctx 𝔅 𝔄) κ : ⊢ pctx_salv K κ ⊑ pctx_slft K κ.
  Proof.
    induction K in κ |- *; simpl; [iApply guards_refl|by iApply IHK|by iApply IHK|by iApply IHK|
      by iApply IHK|by iApply IHK|].
    iApply llftl_incl_trans; [iApply llftl_intersect_incl_r|]. iApply IHK.
  Qed.

  Lemma pctx_in_sum_inv {𝔅 𝔄l} (tyl: typel 𝔄l) i w (K: pctx 𝔅 (𝔄l !!ₗ i)) y :
    pctx_in (PSum tyl i w K) y → ∃ z, y.1 = pinj i z ∧ pctx_in K z.
  Proof.
    simpl. destruct (psum_proj i y.1) as [z|] eqn:Hs; [|done]. intros ?.
    exists z. split; [by apply psum_proj_Some|done].
  Qed.

  (** The guards (by [G], with [k] laters) of the pointer cells on the path. *)
  Fixpoint pctx_sguards {𝔅 𝔄} (K: pctx 𝔅 𝔄) (n k: nat) (G: iProp Σ) : ~~𝔄 → cloc → iProp Σ :=
    match K in pctx 𝔅 𝔄 return ~~𝔄 → cloc → iProp Σ with
    | PHole => λ _ _, True
    | PFst K _ => λ y l, pctx_sguards K n k G y.1 (cloc_take l (pctx_size K n))
    | PSnd lt1 K => λ y l, pctx_sguards K n k G y.2 (cloc_skip l (lty_size lt1))
    | POwn _ K => λ y l, (G &&{↑NllftG; k}&&> l.1 ↦[^ l.2]∗ [ #y.1]) ∗
        pctx_sguards K n k G y.2 (y.1, repeat [] (pctx_size K n))
    | PSum _ i w K => λ y l,
        pctx_sguards K n k G (psum_proj_or i y.1 w) (cloc_take (cloc_skip l 1) (pctx_size K n))
    | PUniq _ K => λ y l, (G &&{↑NllftG; k}&&> l.1 ↦[^ l.2]∗ [ #(uniq_bor_loc y).1]) ∗
        pctx_sguards K n k G (uniq_bor_current y) (uniq_bor_loc y)
    | PShr _ K => λ y l, (G &&{↑NllftG; k}&&> l.1 ↦[^ l.2]∗ [ #y.1.1]) ∗
        pctx_sguards K n k G y.2 y.1
    end%I.

  Global Instance pctx_sguards_persistent {𝔅 𝔄} (K: pctx 𝔅 𝔄) n k G y l :
    Persistent (pctx_sguards K n k G y l).
  Proof. induction K in y, l |- *; apply _. Qed.

  (** The address of the hole, computed by loading the pointers on the path with the
      guards of the shared views. *)
  Lemma wp_pctx_sexpr {𝔅 𝔄} E (K: pctx 𝔅 𝔄) n k (G: iProp Σ) y (l: cloc) (e: expr)
      (Φ: val → iProp Σ) :
    ↑NllftG ⊆ E →
    WP e @ E {{ v, ⌜v = #(l.1)⌝ ∗ pctx_sguards K n k G y l ∗ £(3 * k * pctx_dlev K) ∗ G ∗
      (G -∗ Φ #(pctx_loc K n y l).1) }} -∗
    WP pctx_expr K e @ E {{ Φ }}.
  Proof.
    intros HE. induction K in y, l, e, Φ |- *; simpl.
    - iIntros "WP". iApply (wp_wand with "WP"). iIntros (v) "(-> & _ & _ & G & HΦ)".
      by iApply "HΦ".
    - iIntros "WP". iApply (IHK y.1 (cloc_take l (pctx_size K n))). iApply (wp_wand with "WP").
      iIntros (v) "($ & $ & $ & $ & $)".
    - iIntros "WP". iApply (IHK y.2 (cloc_skip l (lty_size lt1))). wp_bind e. iApply (wp_wand with "WP").
      iIntros (v) "(-> & Gs & £ & G & HΦ)". wp_op. by iFrame.
    - iIntros "WP". iApply (IHK y.2 (y.1, repeat [] (pctx_size K n))). wp_bind e. iApply (wp_wand with "WP").
      iIntros (v) "(-> & [#Gp Gs] & £ & G & HΦ)".
      iDestruct (lc_weaken (3 * k + 3 * k * pctx_dlev K) with "£") as "[£1 £]"; [lia|].
      iApply (wp_read_na_guarded_cells_singleton _ l.1 l.2 G #(y.1) k with "[G £1]");
        [solve_ndisj|by iFrame "Gp G £1"|].
      iIntros "!> G". by iFrame.
    - iIntros "WP". iApply (IHK (psum_proj_or i y.1 w) (cloc_take (cloc_skip l 1) (pctx_size K n))). wp_bind e. iApply (wp_wand with "WP").
      iIntros (v) "(-> & Gs & £ & G & HΦ)". wp_op. by iFrame.
    - iIntros "WP". iApply (IHK (uniq_bor_current y) (uniq_bor_loc y)). wp_bind e. iApply (wp_wand with "WP").
      iIntros (v) "(-> & [#Gp Gs] & £ & G & HΦ)".
      iDestruct (lc_weaken (3 * k + 3 * k * pctx_dlev K) with "£") as "[£1 £]"; [lia|].
      iApply (wp_read_na_guarded_cells_singleton _ l.1 l.2 G #((uniq_bor_loc y).1) k
        with "[G £1]"); [solve_ndisj|by iFrame "Gp G £1"|].
      iIntros "!> G". by iFrame.
    - iIntros "WP". iApply (IHK y.2 y.1). wp_bind e. iApply (wp_wand with "WP").
      iIntros (v) "(-> & [#Gp Gs] & £ & G & HΦ)".
      iDestruct (lc_weaken (3 * k + 3 * k * pctx_dlev K) with "£") as "[£1 £]"; [lia|].
      iApply (wp_read_na_guarded_cells_singleton _ l.1 l.2 G #(y.1.1) k with "[G £1]");
        [solve_ndisj|by iFrame "Gp G £1"|].
      iIntros "!> G". by iFrame.
  Qed.

  (** The shared view of a place gives the shared view of the hole of [K] (and the guards
      of the pointers on the path), with one batch of later credits per pointer. *)
  Lemma shr_pctx_view {𝔅 𝔄} (K: pctx 𝔅 𝔄) κ (lt: lty 𝔅) y d g tid (l: cloc) (G: iProp Σ) E :
    pctx_in K y →
    (G &&{↑NllftG}&&> @[pctx_salv K κ]) -∗ £(d * (g + 3)) -∗
    shr_view κ (lty_fold (pctx_plug K lt)) y d g tid l ={E}=∗
      pctx_sguards K (lty_size lt) (g + 1) G y l ∗
      ∃ dh, ⌜dh + pctx_dlev K ≤ d⌝ ∗
        shr_view (pctx_slft K κ) (lty_fold lt) (pctx_get K y) dh g tid
          (pctx_loc K (lty_size lt) y l).
  Proof.
    induction K as [|𝔅 𝔄1 𝔄2 K IH lt2|𝔅 𝔄1 𝔄2 lt1 K IH|𝔅 𝔄' n' K IH|𝔅 𝔄l tyl i w K IH|
      𝔅 𝔄' κ' K IH|𝔅 𝔄' κ' K IH] in κ, y, d, l, lt |- *; simpl; intros Hin.
    - iIntros "_ _ #V !>". iSplit; [done|]. iExists d. iFrame "V". iPureIntro. lia.
    - iIntros "#Gs £ #(Pt & [Shr _] & [Pers _])".
      iApply (IH with "Gs £"); [done|]. iFrame "Shr Pers".
      rewrite heap_mapsto_cells_fancy_vec_app ty_size_eq -lty_size_fold lty_size_plug.
      by iApply (guards_weaken_rhs_sep_l with "Pt").
    - iIntros "#Gs £ #(Pt & [_ Shr] & [_ Pers])".
      iApply (IH with "Gs £"); [done|]. iFrame "Shr Pers".
      rewrite heap_mapsto_cells_fancy_vec_app ty_size_eq -lty_size_fold.
      by iApply (guards_weaken_rhs_sep_r with "Pt").
    - iIntros "#Gs £ #(Pt & Shr & Pers)". destruct y as [l' z].
      destruct d as [|d']; [by iDestruct "Pers" as "[]"|].
      iDestruct (lc_weaken (1 + (1 + d' * (g + 3))) with "£") as "(£a & £b & £)"; [lia|].
      iMod (lc_fupd_elim_later with "£a Shr") as "#Shr'".
      iDestruct "Shr'" as "[Pt' Shr']".
      iMod (lc_fupd_elim_later with "£b Pers") as "#Pers'".
      iMod (IH κ lt z d' (l', repeat [] (pctx_size K (lty_size lt))) with "Gs £ [$Shr' $Pers']")
        as "[$ (%dh & %Hdh & V)]"; [done| |].
      { rewrite /= -lty_size_plug lty_size_fold -(ty_size_eq (lty_fold (pctx_plug K lt)) z tid).
        iExact "Pt'". }
      iModIntro. iSplit.
      + iApply (guards_transitive_right with "[] Pt").
        iApply (guards_transitive with "Gs"). iApply pctx_salv_incl.
      + iExists dh. iFrame "V". iPureIntro. lia.
    - destruct (pctx_in_sum_inv tyl i w K y Hin) as (z & Hy & Hin').
      destruct y as [s pad]. simpl in Hy. subst s. rewrite psum_proj_or_pinj.
      iIntros "#Gs £ #(Pt & Shr & Pers)".
      rewrite xsum_shr_pinj xsum_pers_pinj hlookup_hlist_set.
      iApply (IH with "Gs £"); [done|]. iFrame "Shr Pers".
      iEval (rewrite split_pt_xsum_cells hlookup_hlist_set) in "Pt".
      rewrite -lty_size_plug lty_size_fold /cloc_take /cloc_skip /=.
      iDestruct (guards_weaken_rhs_sep_r with "Pt") as "Pt'".
      by iApply (guards_weaken_rhs_sep_l with "Pt'").
    - iIntros "#Gs £ #(Pt & Shr & Pers)". destruct y as [[[[[l' z] ξi] d'] g'] idx].
      iDestruct "Shr" as "(%Hle & Pt' & _ & Shr0 & Pers0)".
      iDestruct (lc_weaken (1 + (1 + (1 + d' * (g + 3)))) with "£") as "(£a & £b & £c & £)";
        [nia|].
      iMod (lc_fupd_elim_later with "£a Shr0") as "#Shr1".
      iMod (lc_fupd_elim_later with "£b Pers0") as "#Pers1".
      iMod (lc_fupd_elim_later with "£c Pers1") as "#Pers2".
      iMod (IH (κ ⊓ κ') lt z d' l' with "Gs £ [$Pt' $Shr1]") as "[$ (%dh & %Hdh & V)]";
        [done|..].
      { iApply (ty_gho_pers_depth_mono with "Pers2"); lia. }
      iModIntro. iSplit.
      + iApply (guards_transitive_right with "[] Pt").
        iApply (guards_transitive with "Gs"). iApply llftl_incl_trans; [iApply pctx_salv_incl|].
        iApply llftl_intersect_incl_l.
      + iExists dh. iFrame "V". iPureIntro. lia.
    - iIntros "#Gs £ #(Pt & _ & Pers)". destruct y as [l' z].
      iDestruct (shr_bor_gho_view with "Pers") as "[%Hd Pers']".
      iDestruct (lc_weaken ((g + 1) + pred d * (g + 3)) with "£") as "[£g £]";
        [destruct d; [done|]; simpl; nia|].
      iMod (lc_fupd_elim_laterN with "£g Pers'") as "#V".
      iAssert (G &&{↑NllftG}&&> @[pctx_salv K κ'])%I as "#Gs'".
      { iApply (guards_transitive with "Gs"). iApply llftl_intersect_incl_r. }
      iMod (IH κ' lt z (pred d) l' with "Gs' £ V") as "[$ (%dh & %Hdh & V')]"; [done|].
      iModIntro. iSplit.
      + iApply (guards_transitive_right with "[] Pt").
        iApply (guards_transitive with "Gs"). iApply llftl_intersect_incl_l.
      + iExists dh. iFrame "V'". iPureIntro. lia.
  Qed.
End pctx_shr.

(** * The variants below a shared reference *)

Section pctx_vin.
  Context `{!typeG Σ}.

  (** The value [y] of the root is of the variants of the sums of the siblings and of the
      path of [K]. *)
  Fixpoint pctx_vin {𝔅 𝔄} (K: pctx 𝔅 𝔄) : ~~𝔄 → Prop :=
    match K in pctx 𝔅 𝔄 return ~~𝔄 → Prop with
    | PHole => λ _, True
    | PFst K lt2 => λ y, pctx_vin K y.1 ∧ lty_vin lt2 y.2
    | PSnd lt1 K => λ y, lty_vin lt1 y.1 ∧ pctx_vin K y.2
    | POwn _ K | PShr _ K => λ y, pctx_vin K y.2
    | PSum _ i _ K => λ y, match psum_proj i y.1 with Some z => pctx_vin K z | None => False end
    | PUniq _ K => λ y, pctx_vin K (uniq_bor_current y)
    end.

  Lemma lty_vin_plug {𝔅 𝔄} (K: pctx 𝔅 𝔄) lt y :
    lty_vin (pctx_plug K lt) y ↔ pctx_vin K y ∧ lty_vin lt (pctx_get K y).
  Proof.
    induction K in y, lt |- *; simpl; [naive_solver|rewrite IHK; naive_solver|
      rewrite IHK; naive_solver|by rewrite IHK| |by rewrite IHK|by rewrite IHK].
    rewrite /psum_proj_or. destruct (psum_proj i y.1); [by rewrite IHK|naive_solver].
  Qed.

  Lemma pctx_vin_in {𝔅 𝔄} (K: pctx 𝔅 𝔄) y : pctx_vin K y → pctx_in K y.
  Proof.
    induction K in y |- *; simpl; [done|naive_solver|naive_solver|auto| |auto|auto].
    destruct (psum_proj i y.1); [auto|done].
  Qed.
End pctx_vin.

(** * Phase 1: the shared reference at the hole of an owned context *)

Section pshr_addr.
  Context `{!typeG Σ}.

  (** The later credits for [wp_pshr_addr], for a place of depths at most [D] (a bound on
      all the accesses: each pointer on the path decreases the depth). *)
  Definition pshr_cred (D: nat) : nat := 5 * D * D + 13 * D + 3.

  (** The address of the hole of [K2], below the shared reference at the hole of [K1] in
      an owned place: the access to the hole of [K1] ([pctx_acc]), the load of the pointer
      of the shared reference (in [Owned] or [Uniq] mode), and the loads on the path of
      [K2] ([wp_pctx_sexpr]); the place is unchanged, and the postcondition gets the
      shared view of the hole at [pctx_slft K2 κ]. The view of the referent may be changed
      to [lt''], of the same folded type, if the referent is of its variants (e.g. after
      reading the tag of a sum, [type_case_oplace_pshr]). *)
  Lemma wp_vpshr_addr {𝔅 𝔄 𝔄'} (K1: pctx (at_clocₛ 𝔄') 𝔄) `{!PctxNoShr K1} `{!PctxVRoot K1} κ
      (K2: pctx 𝔅 𝔄') (lt: lty 𝔅) (lt'': lty 𝔄') x₀ ζm D tid (v: val) (e: expr)
      (G: iProp Σ) (Φ: val → iProp Σ) :
    Timeless G → lty_fold lt'' = lty_fold (pctx_plug K2 lt) →
    let lt1 := ShrLty (pctx_plug K2 lt) κ in
    let lt1' := ShrLty lt'' κ in
    let y := pctx_get K1 x₀ in
    (lty_vin (pctx_plug K2 lt) y.2 → lty_vin lt'' y.2) →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗
    (G &&{↑NllftG}&&> @[pctx_ulft K1 lt1]) -∗ (G &&{↑NllftG}&&> @[pctx_salv K2 κ]) -∗
    G -∗ £(pshr_cred D) -∗ ⧖D -∗ WP e {{ w, ⌜w = v⌝ }} -∗
    vroot_own (pctx_plug K1 lt1) (pctx_vrfn K1 x₀ ζm (lty_rfn lt1 y ζm (pctx_vpath K1))) D tid v -∗
    (∀ dh, ⌜dh < D⌝ -∗ ⌜pctx_in K1 x₀ ∧ pctx_vin K2 y.2 ∧ lty_vin lt (pctx_get K2 y.2)⌝ -∗
      G -∗
      vroot_own (pctx_plug K1 lt1') (pctx_vrfn K1 x₀ ζm (lty_rfn lt1' y ζm (pctx_vpath K1))) D tid v -∗
      shr_view (pctx_slft K2 κ) (lty_fold lt) (pctx_get K2 y.2) dh D tid
        (pctx_loc K2 (lty_size lt) y.2 y.1) -∗
      Φ #(pctx_loc K2 (lty_size lt) y.2 y.1).1) -∗
    WP pctx_expr K2 (!(pctx_vexpr K1 e)) {{ Φ }}.
  Proof.
    iIntros (? Hfold lt1 lt1' y Hv) "#LFT #PROPH #UNIQ #Gu #Gs G £ #⧖ WPe Own HΦ".
    have Hdl: 1 ≤ pctx_dlev K1 by apply pctx_vroot_dlev.
    set T := lty_fold (pctx_plug K2 lt).
    have ?: Copy (shr_bor κ T) := shr_copy κ T.
    iDestruct (lc_weaken (pctx_vacc_cred K1 D + (pshr_cred D - pctx_vacc_cred K1 D)) with "£")
      as "[£a £]"; [have := pctx_vacc_cred_le K1 D; rewrite /pshr_cred; nia|].
    (* Access the shared reference. *)
    iMod (vroot_acc K1 lt1 with "LFT PROPH UNIQ Gu G £a Own")
      as (G' dh1 gh1) "(% & G' & #G'G & -> & %Hdh & H & P & #Gp & #HG & Cl)"; [solve_ndisj|].
    destruct Hdh as (Hdh1 & Hgh1 & Hin1).
    set lK := pctx_vloc K1 (lty_size lt1) x₀.
    iAssert (G' &&{↑NllftG}&&> @[pctx_ulft K1 lt1])%I as "#G'u".
    { iApply (guards_transitive with "G'G Gu"). }
    iDestruct (pctx_vhguard K1 lt1 (lty_size lt1) x₀ G' D with "G'u HG") as "#Gw".
    iApply (wp_pctx_sexpr ⊤ K2 (lty_size lt) (D + 1) G y.2 y.1); [solve_ndisj|].
    wp_bind (pctx_vexpr K1 e).
    iDestruct (lc_weaken (3 * (D + 1) * pred (pctx_dlev K1) +
      (pshr_cred D - pctx_vacc_cred K1 D - 3 * (D + 1) * pred (pctx_dlev K1))) with "£")
      as "[£w £]"; [have := pctx_vacc_cred_le K1 D; rewrite /pshr_cred; nia|].
    iApply (wp_wand with "[P G' £w WPe]").
    { iApply (wp_pctx_vptrs ⊤ K1 (lty_size lt1) (D + 1) G' x₀ e True%I with "Gp [£w] [G' WPe] P");
        [solve_ndisj| |].
      - iApply (lc_weaken with "£w"). nia.
      - iApply (wp_wand with "WPe"). iIntros (?) "->". by iFrame. }
    iIntros (w) "(-> & _ & G' & P)".
    iApply wp_fupd.
    set rest := (pshr_cred D - pctx_vacc_cred K1 D - 3 * (D + 1) * pred (pctx_dlev K1)).
    have Hrest: (1 + pctx_dlev K1) + (3 * (D + 1) + ((D + 1) +
      ((D - pctx_dlev K1) * (D + 3) + 3 * (D + 1) * (D - pctx_dlev K1)))) ≤ rest.
    { rewrite /rest. have := pctx_vacc_cred_le K1 D. rewrite /pshr_cred. nia. }
    iDestruct (lc_weaken _ Hrest with "£") as "(£m & £r & £p & £t & £s)".
    (* The (persistent) ownership of the shared reference, and the closed access. *)
    iAssert (WP ! #lK.1 {{ v, ⌜v = #y.1.1⌝ ∗ G ∗
      vroot_own (pctx_plug K1 lt1') (pctx_vrfn K1 x₀ ζm (lty_rfn lt1' y ζm (pctx_vpath K1))) D tid
        #(pctx_vrloc K1 (lty_size lt1) x₀).1 ∗
      ⌜lty_vin (pctx_plug K2 lt) y.2⌝ ∗ (shr_bor κ T).(ty_gho_own) y dh1 gh1 tid }})%I
      with "[H Cl P G' £m £r]" as "WPr".
    { iApply wp_fupd. destruct (pctx_uend K1) as [κ1|] eqn:Hu.
      - iEval (rewrite (pctx_kind_uniq K1 κ1) //) in "H".
        iEval (rewrite /pctx_vcloser (pctx_kind_uniq K1 κ1) //) in "Cl".
        iDestruct "H" as "[(%x' & %idx & -> & Body) %Hvin]".
        iMod (fractional.frac_split_guard_in_half NllftG G' G' with "G' []")
          as (γ2) "[A [B [#Gh2 #Back2]]]"; [solve_ndisj|iApply guards_refl|].
        iAssert (fractional.half γ2 &&{↑NllftG}&&> @[κ1])%I as "#Aκ".
        { iApply (guards_transitive with "Gh2"). iApply (guards_transitive with "G'u").
          by iApply pctx_ulft_uend. }
        iAssert (fractional.half γ2 &&{↑NllftG}&&> @[ty_lft (shr_bor κ T)])%I as "#Aty".
        { iApply (guards_transitive with "Gh2"). iApply (guards_transitive with "G'u").
          iApply (pctx_ulft_fold K1 lt1). by eapply pctx_uend_ulfts_ne. }
        iMod (uniq_body_acc with "LFT UNIQ Aκ Body A") as "(Pl & ⧗1 & CloseB)"; [solve_ndisj|].
        iDestruct (lc_weaken 1 with "£m") as "£1"; [lia|].
        iMod (lc_fupd_elim_later with "£1 Pl") as "Pl".
        iMod (uniq_payload_run with "Aty B Pl") as "(B & #⧖' & #Gho1 & Pt1)"; [solve_ndisj|].
        iApply (wp_read_na_guarded_cells_singleton _ lK.1 lK.2
          (fractional.half γ2 ∗ lK #↦!∗ [FVal #y.1.1]) #y.1.1 (D + 1) with "[B Pt1 £r]");
          [solve_ndisj| |].
        { iFrame "B Pt1 £r". iApply guard_cloc_combine.
          - iApply guards_weaken_lhs_sep_l. iApply (guards_transitive_right with "Gh2 Gw").
          - iApply (lguards_weaken_later _ _ _ 0); [lia|iApply guards_weaken_sep_r]. }
        iIntros "!> [B Pt1]".
        iSpecialize ("CloseB" $! y dh1 gh1 with "[Pt1] ⧗1"); [by iFrame "⧖' Gho1"|].
        iMod (fupd_mask_mono with "CloseB") as "[Body A]"; [solve_ndisj|].
        iMod (fupd_mask_mono with "(Back2 A B)") as "G'"; [solve_ndisj|].
        iMod ("Cl" $! lt1' (inl (PlaceIn y)) dh1 gh1 D [] 1%Qp True%I
          with "[//] [%] [//] [%] [%] [] ⧖ G' P [] [Body]") as "(Own & G & _)".
        { by rewrite /= Hfold. }
        { intros ??. apply prfn_rsv_in. }
        { lia. }
        { iApply pat_ok_ulfts_leaf. }
        { done. }
        { iIntros "_ !>". iSplit; [|done]. iSplit; [|iPureIntro; by apply Hv].
          rewrite /= Hfold. iExists y, idx. by iFrame. }
        iModIntro. iSplit; [done|]. by iFrame "G Own Gho1".
      - iEval (rewrite (pctx_kind_owned K1) //) in "H".
        iEval (rewrite /pctx_vcloser (pctx_kind_owned K1) //) in "Cl".
        have Hm := pctx_hmode_le K1 0. set mh := pctx_hmode K1 0.
        iDestruct "H" as "[(%x' & -> & Pt1 & #Gho1) %Hvin]".
        iDestruct (lc_weaken mh with "£m") as "£m"; [lia|].
        iMod (lc_fupd_elim_laterN with "£m Gho1") as "#Gho1'".
        iApply (wp_read_na_guarded_cells_singleton _ lK.1 lK.2 (G' ∗ lK #↦!∗ [FVal #y.1.1])
          #y.1.1 (D + 1) with "[G' Pt1 £r]"); [solve_ndisj| |].
        { iFrame "G' Pt1 £r". iApply guard_cloc_combine.
          - iApply guards_weaken_lhs_sep_l. iApply "Gw".
          - iApply (lguards_weaken_later _ _ _ 0); [lia|iApply guards_weaken_sep_r]. }
        iIntros "!> [G' Pt1]".
        iMod ("Cl" $! lt1' (inl (PlaceIn y)) dh1 gh1 D [] 1%Qp True%I
          with "[//] [%] [//] [%] [%] [] ⧖ G' P [] [Pt1]") as "(Own & G & _)".
        { by rewrite /= Hfold. }
        { intros ??. apply prfn_rsv_in. }
        { lia. }
        { iApply pat_ok_ulfts_leaf. }
        { done. }
        { iIntros "_ !>". iSplit; [|done]. iSplit; [|iPureIntro; by apply Hv].
          rewrite /= Hfold. iExists y. iSplit; [done|].
          rewrite /ofty_owned. by iFrame "Pt1 Gho1". }
        iModIntro. iSplit; [done|]. by iFrame "G Own Gho1'". }
    iApply (wp_wand with "WPr"). iIntros (v) "(-> & G & Own & %Hvin & #Gho)".
    apply lty_vin_plug in Hvin as [Hvin2 Hvin].
    iDestruct (shr_bor_gho_view with "Gho") as "[%Hdh1' V0]".
    iDestruct (lc_weaken (gh1 + 1) with "£p") as "£p"; [lia|].
    iMod (lc_fupd_elim_laterN with "£p V0") as "#V".
    iDestruct (shr_view_depth_mono _ _ _ _ _ (pred dh1) D with "V") as "#V'"; [lia|lia|].
    iDestruct (lc_weaken (pred dh1 * (D + 3)) with "£t") as "£t"; [nia|].
    iMod (shr_pctx_view K2 κ lt y.2 (pred dh1) D tid y.1 G with "Gs £t V'")
      as "[#Gs2 (%dh & %Hdh & #Vh)]"; [by apply pctx_vin_in|].
    iModIntro. iSplit; [done|]. iFrame "Gs2 G". iSplitL "£s".
    { iApply (lc_weaken with "£s"). nia. }
    iIntros "G". iApply ("HΦ" with "[%] [%] G Own Vh"); [lia|done].
  Qed.
End pshr_addr.

(** * Rules *)

Section typing.
  Context `{!typeG Σ}.

  (** ** (a) Unfolding and folding a shared reference, and changing the view of its
      referent *)

  (** The interpretation of [ShrLty lt κ] is the leaf of its folded type and the variants
      (in both modes), so the view of the referent can be changed for one with the same
      folded type and fewer variant constraints. *)
  Lemma vplace_conv_shr {ℭ 𝔄} (K: pctx (at_clocₛ ℭ) 𝔄) κ (lt lt': lty ℭ) :
    lty_fold lt' = lty_fold lt → (∀ y, lty_vin lt y → lty_vin lt' y) →
    vplace_conv K (ShrLty lt κ) (ShrLty lt' κ) (=).
  Proof.
    iIntros (Hf Hv x ζm dh gh D tid lh G E ? HE HdK ?) "_ _ _ _ _ G _ _ _ H".
    iDestruct "H" as "[H %Hin]".
    iModIntro. iExists (pctx_get K x), [], 1%Qp. iSplit; [done|].
    iSplit; [iPureIntro; intros ??; apply prfn_rsv_in|]. iSplitR; [done|]. iIntros "_ !>".
    iFrame "G". rewrite /= Hf. iFrame "H". iPureIntro. by apply Hv.
  Qed.

  Lemma vplace_conv_shr_unfold {𝔅 𝔄} (K: pctx (at_clocₛ 𝔅) 𝔄) κ (ty: type 𝔅) :
    vplace_conv K (OfTy (&shr{κ} ty)%T) (ShrLty (OfTy ty) κ) (=).
  Proof.
    iIntros (x ζm dh gh D tid lh G E ? HE HdK ?) "_ _ _ _ _ G _ _ _ H".
    iModIntro. iExists (pctx_get K x), [], 1%Qp. iSplit; [done|].
    iSplit; [iPureIntro; intros ??; apply prfn_rsv_in|]. iSplitR; [done|]. iIntros "_ !>".
    by iFrame "G H".
  Qed.

  Lemma vplace_conv_shr_fold {𝔅 𝔄} (K: pctx (at_clocₛ 𝔅) 𝔄) κ (ty: type 𝔅) :
    vplace_conv K (ShrLty (OfTy ty) κ) (OfTy (&shr{κ} ty)%T) (=).
  Proof.
    iIntros (x ζm dh gh D tid lh G E ? HE HdK ?) "_ _ _ _ _ G _ _ _ H".
    iDestruct "H" as "[H _]".
    iModIntro. iExists (pctx_get K x), [], 1%Qp. iSplit; [done|].
    iSplit; [iPureIntro; intros ??; apply prfn_rsv_in|]. iSplitR; [done|]. iIntros "_ !>".
    by iFrame "G H".
  Qed.

  Lemma type_unfold_vplace_shr_instr {𝔅 𝔄} E L I p (K: pctx (at_clocₛ 𝔅) 𝔄) `{!PctxNoShr K} `{!PctxVRoot K}
      κ (ty: type 𝔅) :
    lctx_lft_alive E L (pctx_ulft K (OfTy (&shr{κ} ty)%T) ⊓ ty_lft (&shr{κ} ty)%T) →
    typed_instr E L I +[p ◁ₗ pctx_plug K (OfTy (&shr{κ} ty)%T)] (Seq Skip Skip)
      (const +[p ◁ₗ pctx_plug K (ShrLty (OfTy ty) κ)])
      (λ post '-[x], post -[x]).
  Proof.
    intros Alv. eapply typed_instr_tr_impl;
      [|apply (type_change_vplace_instr _ _ _ _ K _ _ (=)); [done..|apply vplace_conv_shr_unfold]].
    intros post [[x₀ ζm] []] mask π Hπ [x₀' ζm'] Hζ Hin (y' & <- & Hx).
    simpl in *. subst. by rewrite pctx_set_get.
  Qed.

  Lemma type_unfold_oplace_shr_instr {𝔅 𝔄} E L I p n (K: pctx (at_clocₛ 𝔅) 𝔄) `{!PctxNoShr K}
      κ (ty: type 𝔅) :
    lctx_lft_alive E L (pctx_ulft K (OfTy (&shr{κ} ty)%T) ⊓ ty_lft (&shr{κ} ty)%T) →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K (OfTy (&shr{κ} ty)%T)] (Seq Skip Skip)
      (const +[p ◁ₗown{n} pctx_plug K (ShrLty (OfTy ty) κ)])
      (λ post '-[x], post -[x]).
  Proof. intros. by apply (type_unfold_vplace_shr_instr _ _ _ _ (POwn n K)). Qed.

  Lemma type_fold_vplace_shr_instr {𝔅 𝔄} E L I p (K: pctx (at_clocₛ 𝔅) 𝔄) `{!PctxNoShr K} `{!PctxVRoot K}
      κ (ty: type 𝔅) :
    lctx_lft_alive E L (pctx_ulft K (ShrLty (OfTy ty) κ) ⊓ ty_lft (&shr{κ} ty)%T) →
    typed_instr E L I +[p ◁ₗ pctx_plug K (ShrLty (OfTy ty) κ)] (Seq Skip Skip)
      (const +[p ◁ₗ pctx_plug K (OfTy (&shr{κ} ty)%T)])
      (λ post '-[x], post -[x]).
  Proof.
    intros Alv. eapply typed_instr_tr_impl;
      [|apply (type_change_vplace_instr _ _ _ _ K _ _ (=)); [done..|apply vplace_conv_shr_fold]].
    intros post [[x₀ ζm] []] mask π Hπ [x₀' ζm'] Hζ Hin (y' & <- & Hx).
    simpl in *. subst. by rewrite pctx_set_get.
  Qed.

  Lemma type_fold_oplace_shr_instr {𝔅 𝔄} E L I p n (K: pctx (at_clocₛ 𝔅) 𝔄) `{!PctxNoShr K}
      κ (ty: type 𝔅) :
    lctx_lft_alive E L (pctx_ulft K (ShrLty (OfTy ty) κ) ⊓ ty_lft (&shr{κ} ty)%T) →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K (ShrLty (OfTy ty) κ)] (Seq Skip Skip)
      (const +[p ◁ₗown{n} pctx_plug K (OfTy (&shr{κ} ty)%T)])
      (λ post '-[x], post -[x]).
  Proof. intros. by apply (type_fold_vplace_shr_instr _ _ _ _ (POwn n K)). Qed.

  (** Changing the view of the hole of [K2] below the shared reference at the hole of [K]
      (at any depth below it): e.g. unfolding a pair, an owned pointer, a unique borrow or
      a shared reference ([ShrLty] again) below [PShr]. *)
  Lemma type_change_vplace_shr_instr {ℭ 𝔅 𝔄} E L I p (K: pctx (at_clocₛ 𝔅) 𝔄) `{!PctxNoShr K} `{!PctxVRoot K}
      κ (K2: pctx ℭ 𝔅) (lt lt': lty ℭ) :
    lctx_lft_alive E L (pctx_ulft K (ShrLty (pctx_plug K2 lt) κ) ⊓
      ty_lft (&shr{κ} (lty_fold (pctx_plug K2 lt)))%T) →
    lty_fold lt' = lty_fold lt → lty_nrc lt' = lty_nrc lt →
    (∀ y, lty_vin lt y → lty_vin lt' y) →
    typed_instr E L I +[p ◁ₗ pctx_plug K (ShrLty (pctx_plug K2 lt) κ)] (Seq Skip Skip)
      (const +[p ◁ₗ pctx_plug K (ShrLty (pctx_plug K2 lt') κ)])
      (λ post '-[x], post -[x]).
  Proof.
    intros Alv Hf Hn Hv.
    have Hf': lty_fold (pctx_plug K2 lt') = lty_fold (pctx_plug K2 lt) by apply lty_fold_plug_eq'.
    eapply typed_instr_tr_impl; [|apply (type_change_vplace_instr _ _ _ _ K _ _ (=));
      [done|by rewrite /= Hf'|done|..|apply vplace_conv_shr; [done|]]].
    - intros post [[x₀ ζm] []] mask π Hπ [x₀' ζm'] Hζ Hin (y' & <- & Hx).
      simpl in *. subst. by rewrite pctx_set_get.
    - fun_ext=> e. fun_ext=> mm. rewrite /= !lty_nrc_plug. by rewrite Hn.
    - done.
    - done.
    - intros y. rewrite !lty_vin_plug. intros [? ?]. split; [done|]. by apply Hv.
  Qed.

  Lemma type_change_oplace_shr_instr {ℭ 𝔅 𝔄} E L I p n (K: pctx (at_clocₛ 𝔅) 𝔄) `{!PctxNoShr K}
      κ (K2: pctx ℭ 𝔅) (lt lt': lty ℭ) :
    lctx_lft_alive E L (pctx_ulft K (ShrLty (pctx_plug K2 lt) κ) ⊓
      ty_lft (&shr{κ} (lty_fold (pctx_plug K2 lt)))%T) →
    lty_fold lt' = lty_fold lt → lty_nrc lt' = lty_nrc lt →
    (∀ y, lty_vin lt y → lty_vin lt' y) →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K (ShrLty (pctx_plug K2 lt) κ)] (Seq Skip Skip)
      (const +[p ◁ₗown{n} pctx_plug K (ShrLty (pctx_plug K2 lt') κ)])
      (λ post '-[x], post -[x]).
  Proof. intros. by apply (type_change_vplace_shr_instr _ _ _ _ (POwn n K)). Qed.

  (** ** (b) Reading a leaf below a shared reference *)

  (** Copying a value of size 1 out of the hole of [K2], below the shared reference at
      the hole of [K] (both at any path: below owned pointers, unique borrows, and
      further shared references), as [read_shr]. The place is unchanged. *)
  Lemma type_read_vplace_pshr_instr {ℭ 𝔅 𝔄} E L I p (K: pctx (at_clocₛ 𝔅) 𝔄) `{!PctxNoShr K} `{!PctxVRoot K}
      κ (K2: pctx ℭ 𝔅) (lt: lty ℭ) :
    ty_size (lty_fold lt) = 1%nat → Copy (lty_fold lt) →
    lctx_lft_alive E L (pctx_ulft K (ShrLty (pctx_plug K2 lt) κ)) →
    lctx_lft_alive E L (pctx_salv K2 κ) →
    typed_instr E L I +[p ◁ₗ pctx_plug K (ShrLty (pctx_plug K2 lt) κ)]
      (Seq Skip (!(pctx_expr K2 (!(pctx_vexpr K p)))))%E
      (λ v, +[v ◁ lty_fold lt; p ◁ₗ pctx_plug K (ShrLty (pctx_plug K2 lt) κ)])
      (λ post '-[x], post -[pctx_get K2 (pctx_get K x.1).2; x]).
  Proof.
    iIntros (Hsz Hcopy Alv1 Alv2 tid post mask iκs [x []])
      "#LFT #TIME #PROPH #UNIQ #E L I (Tp & _) Obs".
    destruct x as [x₀ ζm].
    rewrite /tctx_elt_interp.
    iDestruct "Tp" as (v Hp) "Tp". iEval (rewrite vplace_own_open) in "Tp".
    iDestruct "Tp" as (D) "(#⧖ & ⧗p & Own)". have Hdl := pctx_vroot_dlev K.
    have ?: Closed [] (pctx_vexpr K p).
    { apply pctx_vexpr_closed. by eapply eval_path_closed. }
    have ?: Closed [] (pctx_expr K2 (!(pctx_vexpr K p))%E).
    { apply pctx_expr_closed. apply _. }
    iDestruct (Alv1 with "L E") as "#Alv1". iDestruct (Alv2 with "L E") as "#Alv2".
    (* A step, for the credits. *)
    wp_bind Skip. iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [set_solver|].
    iIntros "£ #⧖S". wp_let. iModIntro. wp_let.
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_ulft K (ShrLty (pctx_plug K2 lt) κ)])%I
      as "#Hu". { iApply (guards_transitive with "Ghalf Alv1"). }
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_salv K2 κ])%I as "#Hs".
    { iApply (guards_transitive with "Ghalf Alv2"). }
    iDestruct (lc_weaken (pshr_cred D + ((D + 1) + 3 * (D + 1))) with "£") as "[£a [£g £r]]";
      [rewrite /pshr_cred /advance_credits; clear; destruct D as [|[|D]]; [lia|lia|nia]|].
    set y := pctx_get K x₀.
    wp_bind (pctx_expr K2 (!(pctx_vexpr K p))%E).
    iApply (wp_vpshr_addr K κ K2 lt (pctx_plug K2 lt) x₀ ζm D tid _ p (fractional.half γh)
      with "LFT PROPH UNIQ Hu Hs H1 £a ⧖ [] Own"); [done|done|..].
    { iApply wp_wand; [by iApply wp_eval_path|]. by iIntros (?) "->". }
    iIntros (dh Hdh [Hin1 [Hin2 Hvin]]) "H1 Own #(Pt & Shr & Pers)".
    set z := pctx_get K2 y.2.
    set lK := pctx_loc K2 (lty_size lt) y.2 y.1.
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_slft K2 κ])%I as "#Hsl".
    { iApply (guards_transitive with "Hs"). iApply pctx_salv_slft. }
    (* The (persistent) ownership of the value, from the sharing predicate. *)
    iDestruct (copy_shr with "Shr") as "#GGho".
    iDestruct (guards_transitive_right with "Hsl GGho") as "#GGho'".
    iAssert (|={⊤}=> ty_gho_own (lty_fold lt) z dh D tid ∗ fractional.half γh)%I
      with "[H1 £g]" as ">[#Gho H1]".
    { leaf_open_laters "GGho'" with "H1" as "Gho1"; [solve_ndisj|].
      iMod (lc_fupd_add_laterN with "£g Gho1") as "[#Gho1 Hclose]".
      iMod ("Hclose" with "Gho1") as "$". by iModIntro. }
    iDestruct (copy_concrete with "Gho") as %Hconc.
    have Hlen: length (ty_phys (lty_fold lt) z tid) = 1%nat by rewrite ty_size_eq.
    destruct (ty_phys (lty_fold lt) z tid) as [|fv [|]] eqn:Hphys; [done| |done].
    destruct fv as [w|]; [|by destruct Hconc].
    iApply wp_fupd.
    iApply (wp_read_na_guarded_cells_singleton _ lK.1 lK.2 (fractional.half γh) w (D + 1)
      with "[H1 £r]"); [solve_ndisj| |].
    { iFrame "H1 £r". iApply (guards_transitive_right with "Hsl Pt"). }
    iIntros "!> H1".
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iModIntro. iExists -[z; (x₀, ζm)]. iFrame "L I Obs".
    iSplitR "Own ⧗p".
    { iExists w, D. iSplit; [by rewrite eval_path_of_val|]. iFrame "⧖".
      iSplit; [|done].
      iDestruct (ty_gho_own_depth_mono _ dh D D D with "Gho") as "[$ _]"; lia. }
    iSplit; [|done]. iExists _. iSplit; [done|]. by iApply (vplace_own_close with "⧖ ⧗p").
  Qed.

  Lemma type_read_oplace_pshr_instr {ℭ 𝔅 𝔄} E L I p n (K: pctx (at_clocₛ 𝔅) 𝔄) `{!PctxNoShr K}
      κ (K2: pctx ℭ 𝔅) (lt: lty ℭ) :
    ty_size (lty_fold lt) = 1%nat → Copy (lty_fold lt) →
    lctx_lft_alive E L (pctx_ulft K (ShrLty (pctx_plug K2 lt) κ)) →
    lctx_lft_alive E L (pctx_salv K2 κ) →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K (ShrLty (pctx_plug K2 lt) κ)]
      (Seq Skip (!(pctx_expr K2 (!(pctx_expr K p)))))%E
      (λ v, +[v ◁ lty_fold lt; p ◁ₗown{n} pctx_plug K (ShrLty (pctx_plug K2 lt) κ)])
      (λ post '-[x], post -[pctx_get K2 (pctx_get K x.1.2).2; x]).
  Proof. intros. by apply (type_read_vplace_pshr_instr _ _ _ _ (POwn n K)). Qed.

  (** ** (c) Shared borrow of a sub-place below a shared reference *)

  (** A shared reference to the hole of [K2] below the shared reference at the hole of [K]
      ([&( *r).f] for [r: &T], [&( **x).0] for [x: &mut &(T, U)], …), at the lifetime of
      the view of the hole ([pctx_slft K2 κ]: the innermost shared reference, intersected
      with the unique borrows below it). The place is unchanged; [K]'s borrows need only
      be alive during the instruction. *)
  Lemma type_share_vplace_pshr_instr {ℭ 𝔅 𝔄} E L I p (K: pctx (at_clocₛ 𝔅) 𝔄)
      `{!PctxNoShr K} `{!PctxVRoot K} κ (K2: pctx ℭ 𝔅) (lt: lty ℭ) :
    lctx_lft_alive E L (pctx_ulft K (ShrLty (pctx_plug K2 lt) κ)) →
    lctx_lft_alive E L (pctx_salv K2 κ) →
    typed_instr E L I +[p ◁ₗ pctx_plug K (ShrLty (pctx_plug K2 lt) κ)]
      (Seq Skip (pctx_expr K2 (!(pctx_vexpr K p))))%E
      (λ v, +[v ◁ &shr{pctx_slft K2 κ} (lty_fold lt);
        p ◁ₗ pctx_plug K (ShrLty (pctx_plug K2 lt) κ)])
      (λ post '-[x], post -[(pctx_loc K2 (lty_size lt) (pctx_get K x.1).2 (pctx_get K x.1).1,
        pctx_get K2 (pctx_get K x.1).2); x]).
  Proof.
    iIntros (Alv1 Alv2 tid post mask iκs [x []]) "#LFT #TIME #PROPH #UNIQ #E L I (Tp & _) Obs".
    destruct x as [x₀ ζm].
    rewrite /tctx_elt_interp.
    iDestruct "Tp" as (v Hp) "Tp". iEval (rewrite vplace_own_open) in "Tp".
    iDestruct "Tp" as (D) "(#⧖ & ⧗p & Own)". have Hdl := pctx_vroot_dlev K.
    have ?: Closed [] (pctx_vexpr K p).
    { apply pctx_vexpr_closed. by eapply eval_path_closed. }
    have ?: Closed [] (pctx_expr K2 (!(pctx_vexpr K p))%E).
    { apply pctx_expr_closed. apply _. }
    iDestruct (Alv1 with "L E") as "#Alv1". iDestruct (Alv2 with "L E") as "#Alv2".
    (* A step, for the credits. *)
    wp_bind Skip. iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [set_solver|].
    iIntros "£ #⧖S". wp_let. iModIntro. wp_let.
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_ulft K (ShrLty (pctx_plug K2 lt) κ)])%I
      as "#Hu". { iApply (guards_transitive with "Ghalf Alv1"). }
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_salv K2 κ])%I as "#Hs".
    { iApply (guards_transitive with "Ghalf Alv2"). }
    iDestruct (lc_weaken (pshr_cred D) with "£") as "£a";
      [rewrite /pshr_cred /advance_credits; clear; destruct D as [|[|D]]; [lia|lia|nia]|].
    set y := pctx_get K x₀.
    iApply wp_fupd.
    iApply (wp_vpshr_addr K κ K2 lt (pctx_plug K2 lt) x₀ ζm D tid _ p (fractional.half γh)
      with "LFT PROPH UNIQ Hu Hs H1 £a ⧖ [] Own"); [done|done|..].
    { iApply wp_wand; [by iApply wp_eval_path|]. by iIntros (?) "->". }
    iIntros (dh Hdh [Hin1 [Hin2 Hvin]]) "H1 Own #V".
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iModIntro. iExists -[(pctx_loc K2 (lty_size lt) y.2 y.1, pctx_get K2 y.2); (x₀, ζm)].
    iFrame "L I Obs". iSplitR "Own ⧗p".
    { iExists _, D. iSplit; [by rewrite eval_path_of_val|]. iFrame "⧖". iSplit; [|done].
      destruct D as [|D']; [lia|].
      iDestruct (shr_view_depth_mono _ _ _ _ _ D' (S D') with "V") as "#V'"; [lia|lia|].
      iApply (shr_bor_gho_of_view with "V'"). }
    iSplit; [|done]. iExists _. iSplit; [done|]. by iApply (vplace_own_close with "⧖ ⧗p").
  Qed.

  Lemma type_share_oplace_pshr_instr {ℭ 𝔅 𝔄} E L I p n (K: pctx (at_clocₛ 𝔅) 𝔄)
      `{!PctxNoShr K} κ (K2: pctx ℭ 𝔅) (lt: lty ℭ) :
    lctx_lft_alive E L (pctx_ulft K (ShrLty (pctx_plug K2 lt) κ)) →
    lctx_lft_alive E L (pctx_salv K2 κ) →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K (ShrLty (pctx_plug K2 lt) κ)]
      (Seq Skip (pctx_expr K2 (!(pctx_expr K p))))%E
      (λ v, +[v ◁ &shr{pctx_slft K2 κ} (lty_fold lt);
        p ◁ₗown{n} pctx_plug K (ShrLty (pctx_plug K2 lt) κ)])
      (λ post '-[x], post -[(pctx_loc K2 (lty_size lt) (pctx_get K x.1.2).2 (pctx_get K x.1.2).1,
        pctx_get K2 (pctx_get K x.1.2).2); x]).
  Proof. intros. by apply (type_share_vplace_pshr_instr _ _ _ _ (POwn n K)). Qed.

  (** ** (d) Case analysis on a sum below a shared reference *)

  (** Case analysis on the sum at the hole of [K2], below the shared reference at the hole
      of [K]: the tag is read through the view, and the branch of the variant [i] gets the
      place with the view [SumLty tyl i (OfTy (tyl +!! i))] at the hole (the referent does
      not change, so the variant is recorded in the place type, [lty_vin]). The [Skip]
      gives the credits of the access. *)
  Lemma type_case_vplace_pshr {𝔄l 𝔅 𝔄 𝔅l 𝔇} E L I (C: cctx 𝔇) p (K: pctx (at_clocₛ 𝔅) 𝔄)
      `{!PctxNoShr K} `{!PctxVRoot K} κ (K2: pctx (Σ! 𝔄l) 𝔅) (tyl: typel 𝔄l) (T: tctx 𝔅l) el el' trl :
    IntoPlistc el el' →
    lctx_lft_alive E L (pctx_ulft K (ShrLty (pctx_plug K2 (OfTy (Σ! tyl))) κ)) →
    lctx_lft_alive E L (pctx_salv K2 κ) →
    ([∗ nat] i < length 𝔄l, typed_body E L I C
      (p ◁ₗ pctx_plug K (ShrLty (pctx_plug K2 (SumLty tyl i (OfTy (tyl +!! i)))) κ) +:: T)
      (el' -!! i) (trl -!! i)) -∗
    typed_body E L I C (p ◁ₗ pctx_plug K (ShrLty (pctx_plug K2 (OfTy (Σ! tyl))) κ) +:: T)
      (case: (Skip;; !(pctx_expr K2 (!(pctx_vexpr K p)))) of el)
      (λ post '(x -:: cl), let 'xinj i _ := to_xsum (pctx_get K2 (pctx_get K x.1).2).1 in
        (trl -!! i) post (x -:: cl))%type.
  Proof.
    move=> -> Alv1 Alv2. iIntros "el".
    iIntros (tid [x xl] mask post iκs) "#LFT #TIME #PROPH #UNIQ #E L I C /=[Tp T] #Obs".
    destruct x as [x₀ ζm].
    rewrite /tctx_elt_interp.
    iDestruct "Tp" as (v Hp) "Tp". iEval (rewrite vplace_own_open) in "Tp".
    iDestruct "Tp" as (D) "(#⧖ & ⧗p & Own)". have Hdl := pctx_vroot_dlev K.
    have ?: Closed [] (pctx_vexpr K p).
    { apply pctx_vexpr_closed. by eapply eval_path_closed. }
    have ?: Closed [] (pctx_expr K2 (!(pctx_vexpr K p))%E).
    { apply pctx_expr_closed. apply _. }
    iDestruct (Alv1 with "L E") as "#Alv1". iDestruct (Alv2 with "L E") as "#Alv2".
    set y := pctx_get K x₀.
    remember (pctx_get K2 y.2) as z eqn:Hz. destruct z as [s pad].
    destruct (to_xsum s) as [j a] eqn:Hj.
    have Hs: s = pinj j a. { by rewrite -(semi_iso' to_xsum of_xsum s) Hj. }
    subst s.
    (* A step, for the credits. *)
    wp_bind Skip. iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [set_solver|].
    iIntros "£ #⧖S". wp_let. iModIntro. wp_let.
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iAssert (fractional.half γh &&{↑NllftG}&&>
      @[pctx_ulft K (ShrLty (pctx_plug K2 (OfTy (Σ! tyl))) κ)])%I
      as "#Hu". { iApply (guards_transitive with "Ghalf Alv1"). }
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_salv K2 κ])%I as "#Hs".
    { iApply (guards_transitive with "Ghalf Alv2"). }
    iDestruct (lc_weaken (pshr_cred D + 3 * (D + 1)) with "£") as "[£a £r]";
      [rewrite /pshr_cred /advance_credits; clear; destruct D as [|[|D]]; [lia|lia|nia]|].
    set lt'' := pctx_plug K2 (SumLty tyl j (OfTy (tyl +!! j))).
    wp_bind (pctx_expr K2 (!(pctx_vexpr K p))%E).
    iApply (wp_vpshr_addr K κ K2 (OfTy (Σ! tyl)) lt'' x₀ ζm D tid _ p (fractional.half γh)
      with "LFT PROPH UNIQ Hu Hs H1 £a ⧖ [] Own"); [|..].
    { apply lty_fold_plug_eq'. by rewrite lty_fold_sum_ofty. }
    { rewrite !lty_vin_plug -/y -Hz /= psum_proj_pinj. naive_solver. }
    { iApply wp_wand; [by iApply wp_eval_path|]. by iIntros (?) "->". }
    iIntros (dh Hdh [Hin1 [Hin2 Hvin]]) "H1 Own #(Pt & _ & _)".
    set lK := pctx_loc K2 (lty_size (OfTy (Σ! tyl))) y.2 y.1.
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_slft K2 κ])%I as "#Hsl".
    { iApply (guards_transitive with "Hs"). iApply pctx_salv_slft. }
    (* Read the discriminant. *)
    rewrite -Hz.
    iEval (rewrite split_pt_xsum_cells) in "Pt".
    wp_bind (!(LitV _))%E.
    iApply (wp_read_na_guarded_cells_singleton _ lK.1 (take 1 lK.2) (fractional.half γh) #j (D + 1)
      with "[H1 £r]"); [solve_ndisj| |].
    { iFrame "H1 £r". iApply (guards_transitive_right with "Hsl").
      iApply (guards_weaken_rhs_sep_l with "Pt"). }
    iIntros "!> H1".
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    wp_case. { split; [lia|]. by rewrite Nat2Z.id -vlookup_lookup plistc_to_vec_lookup. }
    iDestruct (big_sepN_lookup _ _ j with "el") as "el".
    iApply ("el" $! _ ((x₀, ζm) -:: xl)
      with "LFT TIME PROPH UNIQ E L I C [-] []"); last first.
    { iApply proph_obs_impl; [|done]=>/= ?. by rewrite to_xsum_pinj. }
    iFrame "T". iExists _. iSplit; [done|].
    iApply (vplace_own_close with "⧖ [⧗p]"); [|done].
    rewrite (lty_vnrc_plug_eq K (ShrLty lt'' κ) (ShrLty (pctx_plug K2 (OfTy (Σ! tyl))) κ)) //.
    by rewrite /= /lt'' (lty_nrc_plug_eq K2 (SumLty tyl j (OfTy (tyl +!! j))) (OfTy (Σ! tyl))).
  Qed.

  Lemma type_case_oplace_pshr {𝔄l 𝔅 𝔄 𝔅l 𝔇} E L I (C: cctx 𝔇) p n (K: pctx (at_clocₛ 𝔅) 𝔄)
      `{!PctxNoShr K} κ (K2: pctx (Σ! 𝔄l) 𝔅) (tyl: typel 𝔄l) (T: tctx 𝔅l) el el' trl :
    IntoPlistc el el' →
    lctx_lft_alive E L (pctx_ulft K (ShrLty (pctx_plug K2 (OfTy (Σ! tyl))) κ)) →
    lctx_lft_alive E L (pctx_salv K2 κ) →
    ([∗ nat] i < length 𝔄l, typed_body E L I C
      (p ◁ₗown{n} pctx_plug K (ShrLty (pctx_plug K2 (SumLty tyl i (OfTy (tyl +!! i)))) κ) +:: T)
      (el' -!! i) (trl -!! i)) -∗
    typed_body E L I C (p ◁ₗown{n} pctx_plug K (ShrLty (pctx_plug K2 (OfTy (Σ! tyl))) κ) +:: T)
      (case: (Skip;; !(pctx_expr K2 (!(pctx_expr K p)))) of el)
      (λ post '(x -:: cl), let 'xinj i _ := to_xsum (pctx_get K2 (pctx_get K x.1.2).2).1 in
        (trl -!! i) post (x -:: cl))%type.
  Proof.
    iIntros (???) "el".
    iApply (type_case_vplace_pshr E L I C p (POwn n K) κ K2 tyl T el el' trl with "el"); done.
  Qed.
End typing.

(** * (e) Resolving and dropping places with shared references *)

Section rslv.
  Context `{!typeG Σ}.

  (** A shared reference (with any view of its referent) is a leaf: it is forgotten (its
      ownership is persistent; nothing below it is owned), and its memory, the pointer
      cell, is given back ([lty_omem]). With [type_drop_oplace_deep_instr] and
      [resolve_tctx_cons_oplace_deep], owned places containing shared references are
      dropped and resolved. *)
  Lemma lty_rslv_shr {𝔄} E L (lt: lty 𝔄) κ : lty_rslv E L (ShrLty lt κ) (λ _ _ _ _, True).
  Proof. apply (lty_rslv_of _ _ _ (λ _ _, True)), lty_resolve_just. Qed.
End rslv.

(** * Reading a shared-blocked leaf below unique borrows *)

Section shr_blocked_deep.
  Context `{!typeG Σ}.

  (** Copying a value of size 1 out of a shared-blocked leaf at the hole of [K] (in
      [Owned] mode, below any number of unique borrows; the leaf of
      [type_share_oplace_deep_instr]), while the shared lifetime is alive, as
      [type_read_oplace_shr_instr]: the enclosing borrows are opened for the persistent
      sharing information of the leaf, and closed at the same state. *)
  Lemma type_read_vplace_shr_deep_instr {𝔅 𝔄} E L I p α (K: pctx 𝔅 𝔄) `{!PctxNoShr K} `{!PctxVRoot K}
      (ty: type 𝔅) :
    pctx_uend K = None → ty_size ty = 1%nat → Copy ty →
    lctx_lft_alive E L (pctx_ulft K (ShrBlocked ty (pctx_blft K α))) →
    lctx_lft_alive E L (pctx_blft K α) →
    typed_instr E L I +[p ◁ₗ pctx_plug K (ShrBlocked ty (pctx_blft K α))]
      (Seq Skip (!(pctx_vexpr K p)))%E
      (λ v, +[v ◁ ty; p ◁ₗ pctx_plug K (ShrBlocked ty (pctx_blft K α))])
      (λ post '-[x], post -[pctx_get K x.1; x]).
  Proof.
    iIntros (Hu Hsz Hcopy Alv1 Alv2 tid post mask iκs [x []])
      "#LFT #TIME #PROPH #UNIQ #E L I (Tp & _) Obs".
    destruct x as [x₀ ζm].
    rewrite /tctx_elt_interp.
    iDestruct "Tp" as (v Hp) "Tp". iEval (rewrite vplace_own_open) in "Tp".
    iDestruct "Tp" as (D) "(#⧖ & ⧗p & Own)". have Hdl := pctx_vroot_dlev K.
    have ?: Closed [] (pctx_vexpr K p).
    { apply pctx_vexpr_closed. by eapply eval_path_closed. }
    iDestruct (Alv1 with "L E") as "#Alv1". iDestruct (Alv2 with "L E") as "#Alv2".
    set β := pctx_blft K α.
    set lt := ShrBlocked ty β.
    (* A step, for the credits. *)
    wp_bind Skip. iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [set_solver|].
    iIntros "£ #⧖S". wp_let. iModIntro. wp_let.
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_ulft K lt])%I as "#Hu".
    { iApply (guards_transitive with "Ghalf Alv1"). }
    iAssert (fractional.half γh &&{↑NllftG}&&> @[β])%I as "#Hβ".
    { iApply (guards_transitive with "Ghalf Alv2"). }
    set y := pctx_get K x₀.
    iDestruct (lc_weaken (pctx_vacc_cred K D + (3 * (D + 1) * D + ((D + 1) + 3 * (D + 1))))
      with "£") as "[£a [£w [£g £r]]]";
      [have := pctx_vacc_cred_le K D; rewrite /advance_credits; nia|].
    iMod (vroot_acc K lt with "LFT PROPH UNIQ Hu H1 £a Own")
      as (G' dh gh) "(% & G' & #G'G & -> & %Hdh & H & P & #Gs & #HG & Cl)"; [solve_ndisj|].
    destruct Hdh as (Hdh & Hgh & Hin).
    set lK := pctx_vloc K (ty_size ty) x₀.
    iAssert (G' &&{↑NllftG}&&> @[pctx_ulft K lt])%I as "#G'u".
    { iApply (guards_transitive with "G'G Hu"). }
    iDestruct (pctx_vhguard K lt (ty_size ty) x₀ G' D with "G'u HG") as "#Gw".
    (* The address of the hole. *)
    wp_bind (pctx_vexpr K p).
    iApply (wp_wand with "[P G' £w]").
    { iApply (wp_pctx_vptrs ⊤ K (ty_size ty) (D + 1) G' x₀ p True%I with "Gs [£w] [G'] P");
        [solve_ndisj| |].
      - iApply (lc_weaken with "£w"). nia.
      - iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->". by iFrame. }
    iIntros (w) "(-> & _ & G' & P)".
    iApply wp_fupd.
    iEval (rewrite (pctx_kind_owned K) //) in "H".
    iEval (rewrite /pctx_vcloser (pctx_kind_owned K) //) in "Cl".
    iDestruct "H" as (? ->) "(#GPt & #Shr & #PersL & Inh)".
    (* The (persistent) ownership predicate of the value, from the sharing predicate. *)
    iDestruct (copy_shr with "Shr") as "#GGho".
    iDestruct (guards_transitive_right with "Hβ GGho") as "#GGho'".
    iAssert (|={⊤}=> ty.(ty_gho_own) y dh gh tid ∗ fractional.half γh)%I
      with "[H2 £g]" as ">[#Gho1 H2]".
    { leaf_open_laters "GGho'" with "H2" as "Gho1"; [solve_ndisj|].
      iDestruct (lc_weaken (gh + 1) with "£g") as "£g"; [lia|].
      iMod (lc_fupd_add_laterN with "£g Gho1") as "[#Gho1 Hclose]".
      iMod ("Hclose" with "Gho1") as "$". by iModIntro. }
    iDestruct (copy_concrete with "Gho1") as %Hconc.
    have Hlen: length (ty_phys ty y tid) = 1%nat by rewrite ty_size_eq.
    destruct (ty_phys ty y tid) as [|fv [|]] eqn:Hphys; [done| |done].
    destruct fv as [wv|]; [|by destruct Hconc].
    iApply (wp_read_na_guarded_cells_singleton _ lK.1 lK.2 (G' ∗ fractional.half γh) wv (D + 1)
      with "[G' H2 £r]"); [solve_ndisj| |].
    { iFrame "G' H2 £r". iApply guard_cloc_combine_fancy.
      - iApply guards_weaken_lhs_sep_l. iApply "Gw".
      - iApply guards_weaken_lhs_sep_r. iApply (lguards_weaken_later with "[]"); last first.
        { iApply (guards_transitive_right with "Hβ GPt"). } lia. }
    iIntros "!> [G' H2]".
    iMod ("Cl" $! lt (inl (PlaceIn y)) dh gh D [] 1%Qp True%I
      with "[//] [//] [//] [%] [%] [] ⧖ G' P [] [Inh]") as "(Own & H1 & _)".
    { intros ??. apply prfn_rsv_in. }
    { lia. }
    { iApply big_sepL_intro. iIntros "!>" (i κ Hi). iApply pat_ok_shr_blocked.
      iApply pctx_blft_incl. by eapply elem_of_list_lookup_2. }
    { done. }
    { iIntros "_ !>". iSplit; [|done]. iExists y. rewrite Hphys. by iFrame "GPt Shr PersL Inh". }
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iModIntro. iExists -[y; (x₀, ζm)]. iFrame "L I Obs".
    iSplitR "Own ⧗p".
    { iExists wv, D. iSplit; [by rewrite eval_path_of_val|]. iFrame "⧖".
      iSplit; [|done].
      iDestruct (ty_gho_own_depth_mono _ dh gh D D with "Gho1") as "[$ _]"; lia. }
    iSplit; [|done]. iExists _. iSplit; [done|]. by iApply (vplace_own_close with "⧖ ⧗p").
  Qed.

  Lemma type_read_oplace_shr_deep_instr {𝔅 𝔄} E L I p n α (K: pctx 𝔅 𝔄) `{!PctxNoShr K}
      (ty: type 𝔅) :
    pctx_uend K = None → ty_size ty = 1%nat → Copy ty →
    lctx_lft_alive E L (pctx_ulft K (ShrBlocked ty (pctx_blft K α))) →
    lctx_lft_alive E L (pctx_blft K α) →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K (ShrBlocked ty (pctx_blft K α))]
      (Seq Skip (!(pctx_expr K p)))%E
      (λ v, +[v ◁ ty; p ◁ₗown{n} pctx_plug K (ShrBlocked ty (pctx_blft K α))])
      (λ post '-[x], post -[pctx_get K x.1.2; x]).
  Proof. intros. by apply (type_read_vplace_shr_deep_instr _ _ _ _ α (POwn n K)). Qed.
End shr_blocked_deep.
