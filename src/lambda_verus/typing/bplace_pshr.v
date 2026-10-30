(** * Places below shared references, on bytes

  The byte version of [typing/place_pshr.v]. The referent of a shared reference [&shrb{κ}]
  in a place rooted at a value is a context step [PShr κ K] ([blpath.v]): the place type
  [ShrLty lt κ] ([bltype.v]) is the leaf of [&shrb{κ} (lty_fold lt)] together with the
  variants of the sums of [lt] at the (unchanging) referent ([lty_vin]). Nothing below a
  shared reference is owned, blocked or written; the referent is only _viewed_, through the
  guards of its bytes and the (persistent, structural) sharing predicates of its folded
  type.

  The places below a shared reference are of two forms:
  - [p ◁ₗ ShrLty (K2[lt]) κ]: the root is the shared reference itself, a value (e.g. a
    function argument [x: &T]); the address of the hole is [pctx_expr K2 (ToLit p)];
  - [p ◁ₗ K1[ShrLty (K2[lt]) κ]], with [PctxNoShr K1] and [PctxVRoot K1] (the first
    [PShr] step, below an owned pointer or a unique borrow at the root, e.g.
    [p ◁ₗown{n} …] or [x: &mut &T]); the address of the hole is
    [pctx_expr K2 (ToLit (Load Na1Ord MPtr (pctx_vexpr K1 p)))].

  - Phase 1 (only for the second form, [wp_vpshr_root]): the access of [bpctx_acc.v] to
    the [ShrLty] leaf (in [Owned] or [Uniq] mode, below any number of unique borrows), the
    typed load of the pointer of the shared reference from the bytes of the leaf, and a
    copy of its persistent ownership predicate; the access is closed again with the same
    leaf. (The leaf need not be blocked: its ownership is persistent.)
  - Phase 2 (the shared part [K2]): the _shared view_ ([shr_view]: a guard of the bytes,
    the sharing predicate and the persistent predicate, i.e. the ownership of [&shrb]
    without its laters) is pushed through [K2] ([shr_pctx_view]): fields split the guard of
    the bytes ([cbytes_pair]), a sum at its variant gives the guard of its payload
    ([cbytes_sum]), an owned pointer steps into its pointee, a unique borrow at [κ']
    continues at [κ ⊓ κ'] and a shared reference at [κ'] at [κ'] ([pctx_slft]). The
    pointers on the path are loaded with guarded typed loads of [MPtr]
    ([wp_load_na_guarded_gen]) from the guards of their bytes ([pctx_sguards],
    [wp_pctx_sexpr]), for which all lifetimes on the path must be alive ([pctx_salv]).

  The leaf below [PShr] is read with a guarded typed [Load] of its MiniRust type, so a
  [Copy] value of any size can be read. The credits come from the first program step of the
  address and, for phase 2, from the load of the pointer of the shared reference (or the
  first step of the address, for the first form); no [Skip] is needed.

  Rules (for both forms):
  - (a) [tctx_change_vplace_shr]/[type_change_vplace_shr_instr]: changing the view of the
    referent for one with the same folded type and fewer variant constraints (unfolding
    pairs, boxes, unique borrows and shared references below [PShr]);
    [type_(un)fold_vplace_shr_instr]: [OfTy (&shrb{κ} ty)] ↔ [ShrLty (OfTy ty) κ] at the
    hole of [K1];
  - (b) [type_read_vplace_pshr_instr]: a guarded typed [Load] of a [Copy] leaf;
  - (c) [type_share_vplace_pshr_instr]: a shared reference to a sub-place, at
    [pctx_slft K2 κ];
  - (d) [type_case_vplace_pshr]: case analysis on a sum (a guarded typed [Load] of its
    tag), recording the variant in the place type;
  - (e) resolve/drop: a [ShrLty] is a leaf ([lty_rslv_shr]).

  See [design_docs/verus-belt-phase3-design.md], section "PShr", and
  [design_docs/minirust-memory-model.md], "Outcome: stage 4f". *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From lrust.lang Require Import proofmode.
From lrust.typing Require Export type bltype blpath bpctx_acc bvplace bplace_own shr_bytes.
From lrust.typing Require Import type_context programs programs_util lft_contexts
  uniq_util uniq_bor buniq_util buniq_bor own_bytes bytes_layout value_ctx product own
  freeable_util sum type_sum bplace_shr bplace_resolve bplace_puniq bplace_sum bplace_deep.
From lrust.util Require Import proph_bor.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

(** * Shared views *)

Section shr_view.
  Context `{!typeG Σ}.

  (** The shared view of the value [y] of type [ty] at [l], at the lifetime [κ]: the
      ownership predicate of [&shrb{κ} ty] without its laters. *)
  Definition shr_view {𝔄} (κ: lft) (ty: type 𝔄) (y: ~~𝔄) (d g: nat) (tid: thread_id)
      (l: cloc) : iProp Σ :=
    (@[κ] &&{↑NllftG; g+1}&&> cbytes ty y l) ∗
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
    (&shrb{κ} ty).(ty_gho_own) (l, y) d g tid -∗
      ⌜d ≠ 0%nat⌝ ∗ ▷^(g+1) shr_view κ ty y (pred d) g tid l.
  Proof.
    destruct d as [|d]; [by iIntros "[]"|]. iIntros "#(Pt & Shr & Pers)".
    iSplit; [done|]. iNext. by iFrame "Pt Shr Pers".
  Qed.

  (** And back. *)
  Lemma shr_bor_gho_of_view {𝔄} κ (ty: type 𝔄) (l: cloc) y d g tid :
    shr_view κ ty y d g tid l -∗ (&shrb{κ} ty).(ty_gho_own) (l, y) (S d) g tid.
  Proof. iIntros "#(Pt & Shr & Pers)". iFrame "Pt Shr". by iNext. Qed.

  Lemma xsum_shr_pinj {𝔄l} (tyl: typel 𝔄l) i κ x0 pad d g tid :
    ty_shr (Σ! tyl) κ (pinj i x0, pad) d g tid ⊣⊢ ty_shr (tyl +!! i) κ x0 d g tid.
  Proof. rewrite [ty_shr (Σ! tyl)]/ty_shr /xsum_ty /=. by rewrite to_xsum_pinj. Qed.

  Lemma xsum_pers_pinj {𝔄l} (tyl: typel 𝔄l) i x0 pad d g tid :
    ty_gho_pers (Σ! tyl) (pinj i x0, pad) d g tid ⊣⊢ ty_gho_pers (tyl +!! i) x0 d g tid.
  Proof. rewrite [ty_gho_pers (Σ! tyl)]/ty_gho_pers /xsum_ty /=. by rewrite to_xsum_pinj. Qed.

  (** A guarded typed load of a pointer from the guard of its bytes. *)
  Lemma wp_load_ptr_guarded E (l: cloc) (l': loc) (G: iProp Σ) k :
    ↑NllftG ⊆ E →
    {{{ (G &&{↑NllftG; k}&&> ptr_cell l l') ∗ G ∗ £(2 * k) }}}
      Load Na1Ord MPtr #(l.1) @ E
    {{{ RET MLitV (VPtr l'); G }}}.
  Proof.
    iIntros (? Φ) "(#Gp & G & £) HΦ".
    iApply (wp_load_na_guarded_gen _ _ _ (VPtr l') G (ptr_cell l l') (ptr_bytes l') k
      with "[$G $£]"); [done|by intros ??|..].
    { iSplit; [done|]. iIntros "!> (%bs & Hbs & %Hbs)". iExists 1%Qp, bs. iFrame "Hbs".
      iSplit; [done|]. iIntros "Hbs". iExists bs. by iFrame. }
    done.
  Qed.

  (** The value of a [Copy] type from its sharing predicate, guarded by [G]. *)
  Lemma shr_view_copy {𝔄} κ (ty: type 𝔄) `{!Copy ty} y d g tid l (G: iProp Σ) E :
    ↑NllftG ⊆ E → Timeless G →
    (G &&{↑NllftG}&&> @[κ]) -∗ G -∗ £((g + 1) + (g + 1)) -∗
    shr_view κ ty y d g tid l ={E}=∗
      ∃ w, ⌜ty.(ty_val) y = Some w⌝ ∗ ty.(ty_gho_own) y d g tid ∗ G.
  Proof.
    iIntros (??) "#Gκ G [£g £v] #(Pt & Shr & _)".
    iDestruct (copy_shr with "Shr") as "#GGho".
    iDestruct (guards_transitive_right with "Gκ GGho") as "#GGho'".
    iAssert (|={E}=> ty.(ty_gho_own) y d g tid ∗ G)%I with "[G £g]" as ">[#Gho G]".
    { leaf_open_laters "GGho'" with "G" as "Gho1"; [solve_ndisj|].
      iMod (lc_fupd_add_laterN with "£g Gho1") as "[#Gho1 Hclose]".
      iMod ("Hclose" with "Gho1") as "$". by iModIntro. }
    iDestruct (guards_transitive_right with "Gκ Pt") as "#GP".
    iMod (guards_open_later with "GP G") as "Open"; [solve_ndisj|].
    iMod (lc_fupd_elim_laterN with "£v Open") as ">[(%bs & Pt1 & %Hbs) Back]".
    iMod ("Back" with "[Pt1]") as "G"; [iExists bs; by iFrame|].
    destruct (ty_bytes_val _ _ _ Hbs) as [w Hw].
    iModIntro. iExists w. by iFrame "Gho G".
  Qed.
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

  (** The guards (by [G], with [k] laters) of the bytes of the pointers on the path. *)
  Fixpoint pctx_sguards {𝔅 𝔄} (K: pctx 𝔅 𝔄) (n k: nat) (G: iProp Σ) : ~~𝔄 → cloc → iProp Σ :=
    match K in pctx 𝔅 𝔄 return ~~𝔄 → cloc → iProp Σ with
    | PHole => λ _ _, True
    | PFst K _ => λ y l, pctx_sguards K n k G y.1 (cloc_take l (pctx_size K n))
    | PSnd lt1 K => λ y l, pctx_sguards K n k G y.2 (cloc_skip l (lty_size lt1))
    | POwn _ K => λ y l, (G &&{↑NllftG; k}&&> ptr_cell l y.1) ∗
        pctx_sguards K n k G y.2 (y.1, repeat [] (pctx_size K n))
    | @PSum _ _ _ 𝔄l _ i w K => λ y l,
        pctx_sguards K n k G (psum_proj_or i y.1 w)
          (cloc_take (cloc_skip l (tag_size 𝔄l)) (pctx_size K n))
    | PUniq _ K => λ y l, (G &&{↑NllftG; k}&&> ptr_cell l (uniq_bor_loc y).1) ∗
        pctx_sguards K n k G (uniq_bor_current y) (uniq_bor_loc y)
    | PShr _ K => λ y l, (G &&{↑NllftG; k}&&> ptr_cell l y.1.1) ∗
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
    WP e @ E {{ v, ⌜v = #(l.1)⌝ ∗ pctx_sguards K n k G y l ∗ £(2 * k * pctx_dlev K) ∗ G ∗
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
    - iIntros "WP". iApply (IHK y.2 (y.1, repeat [] (pctx_size K n))).
      wp_bind e. iApply (wp_wand with "WP").
      iIntros (v) "(-> & [#Gp Gs] & £ & G & HΦ)".
      iDestruct (lc_weaken (2 * k + 2 * k * pctx_dlev K) with "£") as "[£1 £]"; [lia|].
      wp_bind (Load _ _ _).
      iApply (wp_load_ptr_guarded _ l y.1 G k with "[$Gp $G $£1]"); [done|].
      iIntros "!> G". wp_pure _. by iFrame.
    - iIntros "WP". iApply (IHK (psum_proj_or i y.1 w)
        (cloc_take (cloc_skip l (tag_size 𝔄l)) (pctx_size K n))).
      wp_bind e. iApply (wp_wand with "WP").
      iIntros (v) "(-> & Gs & £ & G & HΦ)". wp_op. by iFrame.
    - iIntros "WP". iApply (IHK (uniq_bor_current y) (uniq_bor_loc y)).
      wp_bind e. iApply (wp_wand with "WP").
      iIntros (v) "(-> & [#Gp Gs] & £ & G & HΦ)".
      iDestruct (lc_weaken (2 * k + 2 * k * pctx_dlev K) with "£") as "[£1 £]"; [lia|].
      wp_bind (Load _ _ _).
      iApply (wp_load_ptr_guarded _ l (uniq_bor_loc y).1 G k with "[$Gp $G $£1]"); [done|].
      iIntros "!> G". wp_pure _. by iFrame.
    - iIntros "WP". iApply (IHK y.2 y.1). wp_bind e. iApply (wp_wand with "WP").
      iIntros (v) "(-> & [#Gp Gs] & £ & G & HΦ)".
      iDestruct (lc_weaken (2 * k + 2 * k * pctx_dlev K) with "£") as "[£1 £]"; [lia|].
      wp_bind (Load _ _ _).
      iApply (wp_load_ptr_guarded _ l y.1.1 G k with "[$Gp $G $£1]"); [done|].
      iIntros "!> G". wp_pure _. by iFrame.
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
    - iIntros "#Gs £ #(Pt & [Shr _] & [Pers _])". destruct y as [y1 y2].
      iApply (IH with "Gs £"); [done|]. iFrame "Shr Pers".
      iEval (rewrite (cbytes_pair _ (lty_fold (pctx_plug K lt)) (lty_fold lt2))) in "Pt".
      rewrite -lty_size_fold lty_size_plug.
      by iApply (guards_weaken_rhs_sep_l with "Pt").
    - iIntros "#Gs £ #(Pt & [_ Shr] & [_ Pers])". destruct y as [y1 y2].
      iApply (IH with "Gs £"); [done|]. iFrame "Shr Pers".
      iEval (rewrite (cbytes_pair _ (lty_fold lt1) (lty_fold (pctx_plug K lt)))) in "Pt".
      rewrite -lty_size_fold.
      by iApply (guards_weaken_rhs_sep_r with "Pt").
    - iIntros "#Gs £ #(Pt & Shr & Pers)". destruct y as [l' z].
      destruct d as [|d']; [by iDestruct "Pers" as "[]"|].
      iDestruct (lc_weaken (1 + (1 + d' * (g + 3))) with "£") as "(£a & £b & £)"; [lia|].
      iMod (lc_fupd_elim_later with "£a Shr") as "#Shr'".
      iDestruct "Shr'" as "[Pt' Shr']".
      iMod (lc_fupd_elim_later with "£b Pers") as "#Pers'".
      iMod (IH κ lt z d' (l', repeat [] (pctx_size K (lty_size lt))) with "Gs £ [$Shr' $Pers']")
        as "[$ (%dh & %Hdh & V)]"; [done|done|].
      iModIntro. iSplit.
      + rewrite cbytes_at_loc /=.
        iApply (guards_transitive_right with "[] Pt").
        iApply (guards_transitive with "Gs"). iApply pctx_salv_incl.
      + iExists dh. iFrame "V". iPureIntro. lia.
    - destruct (pctx_in_sum_inv tyl i w K y Hin) as (z & Hy & Hin').
      destruct y as [s pad]. simpl in Hy. subst s. rewrite psum_proj_or_pinj.
      iIntros "#Gs £ #(Pt & Shr & Pers)".
      rewrite xsum_shr_pinj xsum_pers_pinj hlookup_hlist_set.
      iApply (IH with "Gs £"); [done|]. iFrame "Shr Pers".
      iEval (rewrite (cbytes_sum _ i (lty_fold (pctx_plug K lt)))) in "Pt".
      rewrite -lty_size_plug.
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
      + rewrite cbytes_uniq_bor.
        iApply (guards_transitive_right with "[] Pt").
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
      + rewrite cbytes_at_cloc.
        iApply (guards_transitive_right with "[] Pt").
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
