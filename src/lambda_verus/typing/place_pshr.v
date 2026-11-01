(** * Places below shared references, on bytes

  The byte version of the deleted legacy [place_pshr.v]. The referent of a shared reference [&shr{κ}]
  in a place rooted at a value is a context step [PShr κ K] ([lpath.v]): the place type
  [ShrLty lt κ] ([ltype.v]) is the leaf of [&shr{κ} (lty_fold lt)] together with the
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

  - Phase 1 (only for the second form, [wp_vpshr_root]): the access of [pctx_acc.v] to
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
    [type_(un)fold_vplace_shr_instr]: [OfTy (&shr{κ} ty)] ↔ [ShrLty (OfTy ty) κ] at the
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
From lrust.typing Require Export type ltype lpath pctx_acc vplace place_own shr_bor.
From lrust.typing Require Import type_context programs lft_contexts uniq_util uniq_bor own bytes_layout value_ctx product freeable_util sum place_shr place_resolve place_puniq place_sum place_deep.
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
      (l: loc) : iProp Σ :=
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
  Lemma shr_bor_gho_view {𝔄} κ (ty: type 𝔄) (l: loc) y d g tid :
    (&shr{κ} ty).(ty_gho_own) (l, y) d g tid -∗
      ⌜d ≠ 0%nat⌝ ∗ ▷^(g+1) shr_view κ ty y (pred d) g tid l.
  Proof.
    destruct d as [|d]; [by iIntros "[]"|]. iIntros "#(Pt & Shr & Pers)".
    iSplit; [done|]. iNext. by iFrame "Pt Shr Pers".
  Qed.

  (** And back. *)
  Lemma shr_bor_gho_of_view {𝔄} κ (ty: type 𝔄) (l: loc) y d g tid :
    shr_view κ ty y d g tid l -∗ (&shr{κ} ty).(ty_gho_own) (l, y) (S d) g tid.
  Proof. iIntros "#(Pt & Shr & Pers)". iFrame "Pt Shr". by iNext. Qed.

  Lemma xsum_shr_pinj {𝔄l} (tyl: typel 𝔄l) i κ x0 d g tid :
    ty_shr (Σ! tyl) κ (pinj i x0) d g tid ⊣⊢ ty_shr (tyl +!! i) κ x0 d g tid.
  Proof. rewrite [ty_shr (Σ! tyl)]/ty_shr /xsum_ty /=. by rewrite to_xsum_pinj. Qed.

  Lemma xsum_pers_pinj {𝔄l} (tyl: typel 𝔄l) i x0 d g tid :
    ty_gho_pers (Σ! tyl) (pinj i x0) d g tid ⊣⊢ ty_gho_pers (tyl +!! i) x0 d g tid.
  Proof. rewrite [ty_gho_pers (Σ! tyl)]/ty_gho_pers /xsum_ty /=. by rewrite to_xsum_pinj. Qed.

  (** A guarded typed load of a pointer from the guard of its bytes. *)
  Lemma wp_load_ptr_guarded E (l: loc) (l': loc) (G: iProp Σ) k :
    ↑NllftG ⊆ E →
    {{{ (G &&{↑NllftG; k}&&> ptr_cell l l') ∗ G ∗ £(2 * k) }}}
      Load Na1Ord MPtr #(l) @ E
    {{{ RET MLitV (VPtr l'); G }}}.
  Proof.
    iIntros (? Φ) "(#Gp & G & £) HΦ".
    iApply (wp_load_na_guarded_gen _ _ _ (VPtr l') G (ptr_cell l l') (ptr_bytes l') k
      with "[$G $£]"); [done|by intros ??|..].
    { iSplit; [done|]. iIntros "!> (%bs & Hbs & %Hbs)". iExists bs. iFrame "Hbs".
      iSplit; [done|]. iIntros "Hbs". iExists bs. by iFrame. }
    done.
  Qed.

  (** The value of a [Copy] type from its sharing predicate, guarded by [G]. *)
  Lemma shr_view_copy {𝔄} `{!NoCell 𝔄} κ (ty: type 𝔄) `{!Copy ty} y d g tid l (G: iProp Σ) E :
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
    iMod (lc_fupd_elim_laterN with "£v Open") as ">[Pt1 Back]".
    iDestruct (bytes_own_val with "Pt1") as %[w Hw].
    iMod ("Back" with "Pt1") as "G".
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
    simpl. destruct (psum_proj i y) as [z|] eqn:Hs; [|done]. intros ?.
    exists z. split; [by apply psum_proj_Some|done].
  Qed.

  (** The guards (by [G], with [k] laters) of the bytes of the pointers on the path. *)
  Fixpoint pctx_sguards {𝔅 𝔄} (K: pctx 𝔅 𝔄) (n k: nat) (G: iProp Σ) : ~~𝔄 → loc → iProp Σ :=
    match K in pctx 𝔅 𝔄 return ~~𝔄 → loc → iProp Σ with
    | PHole => λ _ _, True
    | PFst K _ => λ y l, pctx_sguards K n k G y.1 l
    | PSnd lt1 K => λ y l, pctx_sguards K n k G y.2 (l +ₗ lty_size lt1)
    | POwn _ K => λ y l, (G &&{↑NllftG; k}&&> ptr_cell l y.1) ∗
        pctx_sguards K n k G y.2 y.1
    | @PSum _ _ _ 𝔄l _ i w K => λ y l,
        pctx_sguards K n k G (psum_proj_or i y w)
          (l +ₗ tag_size 𝔄l)
    | PUniq _ K => λ y l, (G &&{↑NllftG; k}&&> ptr_cell l (uniq_bor_loc y)) ∗
        pctx_sguards K n k G (uniq_bor_current y) (uniq_bor_loc y)
    | PShr _ K => λ y l, (G &&{↑NllftG; k}&&> ptr_cell l y.1) ∗
        pctx_sguards K n k G y.2 y.1
    end%I.

  Global Instance pctx_sguards_persistent {𝔅 𝔄} (K: pctx 𝔅 𝔄) n k G y l :
    Persistent (pctx_sguards K n k G y l).
  Proof. induction K in y, l |- *; apply _. Qed.

  (** The address of the hole, computed by loading the pointers on the path with the
      guards of the shared views. *)
  Lemma wp_pctx_sexpr {𝔅 𝔄} E (K: pctx 𝔅 𝔄) n k (G: iProp Σ) y (l: loc) (e: expr)
      (Φ: val → iProp Σ) :
    ↑NllftG ⊆ E →
    WP e @ E {{ v, ⌜v = #(l)⌝ ∗ pctx_sguards K n k G y l ∗ £(2 * k * pctx_dlev K) ∗ G ∗
      (G -∗ Φ #(pctx_loc K n y l)) }} -∗
    WP pctx_expr K e @ E {{ Φ }}.
  Proof.
    intros HE. induction K in y, l, e, Φ |- *; simpl.
    - iIntros "WP". iApply (wp_wand with "WP"). iIntros (v) "(-> & _ & _ & G & HΦ)".
      by iApply "HΦ".
    - iIntros "WP". iApply (IHK y.1 l). iApply (wp_wand with "WP").
      iIntros (v) "($ & $ & $ & $ & $)".
    - iIntros "WP". iApply (IHK y.2 (l +ₗ lty_size lt1)). wp_bind e. iApply (wp_wand with "WP").
      iIntros (v) "(-> & Gs & £ & G & HΦ)". wp_op. by iFrame.
    - iIntros "WP". iApply (IHK y.2 y.1).
      wp_bind e. iApply (wp_wand with "WP").
      iIntros (v) "(-> & [#Gp Gs] & £ & G & HΦ)".
      iDestruct (lc_weaken (2 * k + 2 * k * pctx_dlev K) with "£") as "[£1 £]"; [lia|].
      wp_bind (Load _ _ _).
      iApply (wp_load_ptr_guarded _ l y.1 G k with "[$Gp $G $£1]"); [done|].
      iIntros "!> G". wp_pure _. by iFrame.
    - iIntros "WP". iApply (IHK (psum_proj_or i y w)
        (l +ₗ tag_size 𝔄l)).
      wp_bind e. iApply (wp_wand with "WP").
      iIntros (v) "(-> & Gs & £ & G & HΦ)". wp_op. by iFrame.
    - iIntros "WP". iApply (IHK (uniq_bor_current y) (uniq_bor_loc y)).
      wp_bind e. iApply (wp_wand with "WP").
      iIntros (v) "(-> & [#Gp Gs] & £ & G & HΦ)".
      iDestruct (lc_weaken (2 * k + 2 * k * pctx_dlev K) with "£") as "[£1 £]"; [lia|].
      wp_bind (Load _ _ _).
      iApply (wp_load_ptr_guarded _ l (uniq_bor_loc y) G k with "[$Gp $G $£1]"); [done|].
      iIntros "!> G". wp_pure _. by iFrame.
    - iIntros "WP". iApply (IHK y.2 y.1). wp_bind e. iApply (wp_wand with "WP").
      iIntros (v) "(-> & [#Gp Gs] & £ & G & HΦ)".
      iDestruct (lc_weaken (2 * k + 2 * k * pctx_dlev K) with "£") as "[£1 £]"; [lia|].
      wp_bind (Load _ _ _).
      iApply (wp_load_ptr_guarded _ l y.1 G k with "[$Gp $G $£1]"); [done|].
      iIntros "!> G". wp_pure _. by iFrame.
  Qed.

  (** The shared view of a place gives the shared view of the hole of [K] (and the guards
      of the pointers on the path), with one batch of later credits per pointer. *)
  Lemma shr_pctx_view {𝔅 𝔄} (K: pctx 𝔅 𝔄) κ (lt: lty 𝔅) y d g tid (l: loc) (G: iProp Σ) E :
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
      iMod (IH κ lt z d' l' with "Gs £ [$Shr' $Pers']")
        as "[$ (%dh & %Hdh & V)]"; [done|done|].
      iModIntro. iSplit.
      + rewrite cbytes_at_loc /=.
        iApply (guards_transitive_right with "[] Pt").
        iApply (guards_transitive with "Gs"). iApply pctx_salv_incl.
      + iExists dh. iFrame "V". iPureIntro. lia.
    - destruct (pctx_in_sum_inv tyl i w K y Hin) as (z & Hy & Hin').
      simpl in Hy. subst y. rewrite psum_proj_or_pinj.
      iIntros "#Gs £ #(Pt & Shr & Pers)".
      rewrite xsum_shr_pinj xsum_pers_pinj hlookup_hlist_set.
      iApply (IH with "Gs £"); [done|]. iFrame "Shr Pers".
      iEval (rewrite (cbytes_sum _ i (lty_fold (pctx_plug K lt)))) in "Pt".
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
      + rewrite cbytes_at_loc.
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
    | PSum _ i _ K => λ y, match psum_proj i y with Some z => pctx_vin K z | None => False end
    | PUniq _ K => λ y, pctx_vin K (uniq_bor_current y)
    end.

  Lemma lty_vin_plug {𝔅 𝔄} (K: pctx 𝔅 𝔄) lt y :
    lty_vin (pctx_plug K lt) y ↔ pctx_vin K y ∧ lty_vin lt (pctx_get K y).
  Proof.
    induction K in y, lt |- *; simpl; [naive_solver|rewrite IHK; naive_solver|
      rewrite IHK; naive_solver|by rewrite IHK| |by rewrite IHK|by rewrite IHK].
    rewrite /psum_proj_or. destruct (psum_proj i y); [by rewrite IHK|naive_solver].
  Qed.

  Lemma pctx_vin_in {𝔅 𝔄} (K: pctx 𝔅 𝔄) y : pctx_vin K y → pctx_in K y.
  Proof.
    induction K in y |- *; simpl; [done|naive_solver|naive_solver|auto| |auto|auto].
    destruct (psum_proj i y); [auto|done].
  Qed.
End pctx_vin.

(** * The address of the hole below a shared reference *)

Section pshr_addr.
  Context `{!typeG Σ}.

  (** The later credits for the address of a hole below a shared reference, in a place of
      depth at most [D] (each pointer on the path decreases the depth). With [4 * (D + 1)]
      more (for a guarded typed load of a [Copy] leaf), they are the credits of one program
      step. *)
  Definition pshr_cred (D: nat) : nat := 7 * D * D + 12 * D + 3.

  Lemma pshr_cred_step D : pshr_cred D + 4 * (D + 1) ≤ advance_credits D.
  Proof. rewrite /pshr_cred /advance_credits. destruct D; [lia|nia]. Qed.

  (** Phase 2: the address of the hole of [K2] below a shared reference whose referent is
      at [y.1] (the value of [e]), from the shared view of the referent (given once [e] has
      been evaluated): the guarded loads of the pointers on the path. *)
  Lemma wp_pshr_hole {𝔅 𝔄'} E κ (K2: pctx 𝔅 𝔄') (lt: lty 𝔅) (y: ~~ (at_locₛ 𝔄')) D tid
      (e: expr) (G: iProp Σ) (Φ: val → iProp Σ) :
    ↑NllftG ⊆ E →
    (G &&{↑NllftG}&&> @[pctx_salv K2 κ]) -∗
    WP e @ E {{ v, ⌜v = #(y.1)⌝ ∗ ∃ dh, ⌜dh ≤ D⌝ ∗ ⌜pctx_in K2 y.2⌝ ∗ G ∗
      £(D * (D + 3) + 2 * (D + 1) * D) ∗
      shr_view κ (lty_fold (pctx_plug K2 lt)) y.2 dh D tid y.1 ∗
      (∀ dh', ⌜dh' + pctx_dlev K2 ≤ dh⌝ -∗ G -∗
        shr_view (pctx_slft K2 κ) (lty_fold lt) (pctx_get K2 y.2) dh' D tid
          (pctx_loc K2 (lty_size lt) y.2 y.1) -∗
        Φ #(pctx_loc K2 (lty_size lt) y.2 y.1)) }} -∗
    WP pctx_expr K2 e @ E {{ Φ }}.
  Proof.
    iIntros (?) "#Gs WP".
    iApply (wp_pctx_sexpr E K2 (lty_size lt) (D + 1) G y.2 y.1); [done|].
    iApply wp_fupd. iApply (wp_wand with "WP").
    iIntros (v) "(-> & %dh & %Hdh & %Hin & G & £ & #V & HΦ)".
    iDestruct (lc_weaken (dh * (D + 3) + 2 * (D + 1) * D) with "£") as "[£v £s]"; [nia|].
    iMod (shr_pctx_view K2 κ lt y.2 dh D tid y.1 G with "Gs £v V")
      as "[#Gs2 (%dh' & %Hdh' & #Vh)]"; [done|].
    iModIntro. iSplit; [done|]. iFrame "Gs2 G". iSplitL "£s".
    { iApply (lc_weaken with "£s"). nia. }
    iIntros "G". iApply ("HΦ" with "[%] G Vh"). lia.
  Qed.

  (** The root of the place is the shared reference (a value [v], the value of [e]). The
      view of the referent may be changed to [lt''], of the same folded type, if the
      referent is of its variants (e.g. after reading the tag of a sum). *)
  Lemma wp_pshr_open_root {𝔅 𝔄'} E κ (K2: pctx 𝔅 𝔄') (lt: lty 𝔅) (lt'': lty 𝔄')
      (x: ~~ (at_locₛ 𝔄')) D tid
      (v: val) (e: expr) (G: iProp Σ) (Φ: val → iProp Σ) :
    ↑NllftG ⊆ E → lty_fold lt'' = lty_fold (pctx_plug K2 lt) →
    (lty_vin (pctx_plug K2 lt) x.2 → lty_vin lt'' x.2) →
    (G &&{↑NllftG}&&> @[pctx_salv K2 κ]) -∗ G -∗ £(pshr_cred D) -∗
    WP e @ E {{ w, ⌜w = v⌝ }} -∗
    vroot_own (ShrLty (pctx_plug K2 lt) κ) (inl (PlaceIn x)) D tid v -∗
    (∀ dh, ⌜dh < D⌝ -∗ ⌜pctx_vin K2 x.2 ∧ lty_vin lt (pctx_get K2 x.2)⌝ -∗ G -∗
      vroot_own (ShrLty lt'' κ) (inl (PlaceIn x)) D tid v -∗
      shr_view (pctx_slft K2 κ) (lty_fold lt) (pctx_get K2 x.2) dh D tid
        (pctx_loc K2 (lty_size lt) x.2 x.1) -∗
      Φ #(pctx_loc K2 (lty_size lt) x.2 x.1)) -∗
    WP pctx_expr K2 (ToLit e) @ E {{ Φ }}.
  Proof.
    iIntros (? Hfold Hv) "#Gs G £ WPe Own HΦ".
    iDestruct "Own" as (d g Hle) "[Leaf %Hvin]".
    iDestruct "Leaf" as (x' ->) "[%Hrep #Gho]".
    destruct Hrep as (w & -> & Hw). simpl in Hw. simplify_eq.
    simpl in Hvin. apply lty_vin_plug in Hvin as [Hvin2 Hvin].
    iDestruct (shr_bor_gho_view with "Gho") as "[%Hd V0]".
    iDestruct (lc_weaken ((g + 1) + (D * (D + 3) + 2 * (D + 1) * D)) with "£") as "[£g £]";
      [rewrite /pshr_cred; nia|].
    iMod (lc_fupd_elim_laterN with "£g V0") as "#V".
    iDestruct (shr_view_depth_mono _ _ _ _ _ (pred d) D with "V") as "#V'"; [lia|lia|].
    iApply (wp_pshr_hole E κ K2 lt x D tid with "Gs"); [done|].
    wp_bind e. iApply (wp_wand with "WPe"). iIntros (?) "->". wp_pure _.
    iSplit; [done|]. iExists (pred d). iFrame "G £ V'".
    iSplit; [iPureIntro; lia|]. iSplit; [iPureIntro; by apply pctx_vin_in|].
    iIntros (dh' Hdh') "G Vh". iApply ("HΦ" with "[%] [%] G [] Vh"); [lia|done|].
    iExists d, g. iSplit; [done|]. iSplit; [|iPureIntro; simpl; by apply Hv, lty_vin_plug].
    rewrite /= Hfold. iExists x. iSplit; [done|]. iSplit; [|done].
    iPureIntro. by eexists.
  Qed.

  (** Phase 1: the shared reference is at the hole of [K1] (whose first step is the root
      pointer): the access to the leaf, the typed load of the pointer from the bytes of the
      leaf (in [Owned] or [Uniq] mode), and a copy of its persistent ownership predicate;
      the access is closed again, with the view [lt''] of the referent. *)
  Lemma wp_pshr_open {𝔅 𝔄 𝔄'} E (K1: pctx (at_locₛ 𝔄') 𝔄) `{!PctxNoShr K1} `{!PctxVRoot K1} κ
      (K2: pctx 𝔅 𝔄') (lt: lty 𝔅) (lt'': lty 𝔄') x₀ ζm D tid (v: val) (e: expr)
      (G: iProp Σ) (Φ: val → iProp Σ) :
    Timeless G → lazyE ⊆ E → lty_fold lt'' = lty_fold (pctx_plug K2 lt) →
    let lt1 := ShrLty (pctx_plug K2 lt) κ in
    let lt1' := ShrLty lt'' κ in
    let y := pctx_get K1 x₀ in
    (lty_vin (pctx_plug K2 lt) y.2 → lty_vin lt'' y.2) →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗
    (G &&{↑NllftG}&&> @[pctx_ulft K1 lt1]) -∗ (G &&{↑NllftG}&&> @[pctx_salv K2 κ]) -∗
    G -∗ £(pshr_cred D) -∗ ⧖D -∗ WP e @ E {{ w, ⌜w = v⌝ }} -∗
    vroot_own (pctx_plug K1 lt1) (pctx_vrfn K1 x₀ ζm (inl (PlaceIn y))) D tid v -∗
    (∀ dh, ⌜dh < D⌝ -∗ ⌜pctx_in K1 x₀ ∧ pctx_vin K2 y.2 ∧ lty_vin lt (pctx_get K2 y.2)⌝ -∗
      G -∗
      vroot_own (pctx_plug K1 lt1') (pctx_vrfn K1 x₀ ζm (inl (PlaceIn y))) D tid v -∗
      shr_view (pctx_slft K2 κ) (lty_fold lt) (pctx_get K2 y.2) dh D tid
        (pctx_loc K2 (lty_size lt) y.2 y.1) -∗
      Φ #(pctx_loc K2 (lty_size lt) y.2 y.1)) -∗
    WP pctx_expr K2 (ToLit (Load Na1Ord MPtr (pctx_vexpr K1 e))) @ E {{ Φ }}.
  Proof.
    iIntros (? HE Hfold lt1 lt1' y Hv) "#LFT #PROPH #UNIQ #Gu #Gs G £ #⧖ WPe Own HΦ".
    have Hdl: 1 ≤ pctx_dlev K1 by apply pctx_vroot_dlev.
    have ?: ↑NllftG ⊆ E. { trans lazyE; [apply lazyE_NllftG|done]. }
    have ?: ↑Nllft ⊆ E. { trans lazyE; [rewrite /lazyE; solve_ndisj|done]. }
    set T := lty_fold (pctx_plug K2 lt).
    iDestruct (lc_weaken (pctx_vacc_cred K1 D + (pshr_cred D - pctx_vacc_cred K1 D)) with "£")
      as "[£a £]"; [have := pctx_vacc_cred_le K1 D; rewrite /pshr_cred; nia|].
    (* Access the shared reference. *)
    iMod (vroot_acc K1 lt1 with "LFT PROPH UNIQ Gu G £a Own")
      as (G' dh1 gh1) "(% & G' & #G'G & -> & %Hdh & H & P & Cl)"; [done|].
    destruct Hdh as (Hdh1 & Hgh1 & Hin1).
    set lK := pctx_vloc K1 (lty_size lt1) x₀.
    iAssert (G' &&{↑NllftG}&&> @[pctx_ulft K1 lt1])%I as "#G'u".
    { iApply (guards_transitive with "G'G Gu"). }
    have Hrest: 3 * (D + 1) * pred (pctx_dlev K1) + ((D + 1) + ((D + 1) +
      (D * (D + 3) + 2 * (D + 1) * D))) ≤ pshr_cred D - pctx_vacc_cred K1 D.
    { have := pctx_vacc_cred_le K1 D. rewrite /pshr_cred. nia. }
    iDestruct (lc_weaken _ Hrest with "£") as "(£w & £m & £g & £r)".
    iApply (wp_pshr_hole E κ K2 lt y D tid with "Gs"); [done|].
    (* The address of the leaf. *)
    wp_bind (pctx_vexpr K1 e).
    iApply (wp_wand with "[P G' £w WPe]").
    { iApply (wp_pctx_vptrs E K1 (lty_size lt1) G' x₀ e True%I with "[G' WPe] P").
      iApply (wp_wand with "WPe"). iIntros (?) "->". by iFrame. }
    iIntros (w) "(-> & _ & G' & P)".
    (* The pointer, and the (persistent) ownership of the shared reference; the closed
       access. *)
    iAssert (WP Load Na1Ord MPtr #lK @ E {{ v, ⌜v = MLitV (VPtr y.1)⌝ ∗ G ∗
      vroot_own (pctx_plug K1 lt1') (pctx_vrfn K1 x₀ ζm (inl (PlaceIn y))) D tid
        (MLitV (VPtr (pctx_vrloc K1 (lty_size lt1) x₀))) ∗
      ⌜lty_vin (pctx_plug K2 lt) y.2⌝ ∗ (shr_bytes κ T).(ty_gho_own) y dh1 gh1 tid }})%I
      with "[H Cl P G' £m]" as "WPr".
    { iApply wp_fupd. destruct (pctx_uend K1) as [κ1|] eqn:Hu.
      - iEval (rewrite (pctx_kind_uniq K1 κ1) //) in "H".
        iEval (rewrite /pctx_vcloser (pctx_kind_uniq K1 κ1) //) in "Cl".
        iDestruct "H" as "[H %Hvin]". iDestruct "H" as (? idx ->) "Body".
        iMod (fractional.frac_split_guard_in_half NllftG G' G' with "G' []")
          as (γ2) "[A [B [#Gh2 #Back2]]]"; [done|iApply guards_refl|].
        iAssert (fractional.half γ2 &&{↑NllftG}&&> @[κ1])%I as "#Aκ".
        { iApply (guards_transitive with "Gh2"). iApply (guards_transitive with "G'u").
          by iApply pctx_ulft_uend. }
        iAssert (fractional.half γ2 &&{↑NllftG}&&> @[ty_lft (shr_bytes κ T)])%I as "#Aty".
        { iApply (guards_transitive with "Gh2"). iApply (guards_transitive with "G'u").
          iApply (pctx_ulft_fold K1 lt1). by eapply pctx_uend_ulfts_ne. }
        iMod (uniq_body_acc with "LFT UNIQ Aκ Body A") as "(Pl & ⧗1 & CloseB)"; [done|].
        iDestruct (lc_weaken 1 with "£m") as "£1"; [lia|].
        iMod (lc_fupd_elim_later with "£1 Pl") as "Pl".
        iMod (uniq_payload_run with "Aty B Pl") as "(B & #⧖' & #Gho1 & Pt1)"; [done|].
        iEval (rewrite cbytes_at_loc) in "Pt1". iDestruct "Pt1" as (bs) "[Hbs %Hbs]".
        iApply (wp_load_na with "Hbs"); [exact Hbs|]. iIntros "!> Hbs".
        iSpecialize ("CloseB" $! y dh1 gh1 with "[Hbs] ⧗1").
        { iNext. iFrame "⧖' Gho1". rewrite cbytes_at_loc. iExists bs. by iFrame. }
        iMod (fupd_mask_mono with "CloseB") as "[Body A]"; [done|].
        iMod (fupd_mask_mono with "(Back2 A B)") as "G'"; [done|].
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
        iDestruct "H" as "[H %Hvin]". iDestruct "H" as (? ->) "[Pt1 #Gho1]".
        iDestruct (lc_weaken mh with "£m") as "£m"; [lia|].
        iMod (lc_fupd_elim_laterN with "£m Gho1") as "#Gho1'".
        iEval (rewrite cbytes_at_loc) in "Pt1". iDestruct "Pt1" as (bs) "[Hbs %Hbs]".
        iApply (wp_load_na with "Hbs"); [exact Hbs|]. iIntros "!> Hbs".
        iMod ("Cl" $! lt1' (inl (PlaceIn y)) dh1 gh1 D [] 1%Qp True%I
          with "[//] [%] [//] [%] [%] [] ⧖ G' P [] [Hbs]") as "(Own & G & _)".
        { by rewrite /= Hfold. }
        { intros ??. apply prfn_rsv_in. }
        { lia. }
        { iApply pat_ok_ulfts_leaf. }
        { done. }
        { iIntros "_ !>". iSplit; [|done]. iSplit; [|iPureIntro; by apply Hv].
          rewrite /= Hfold. iExists y. iSplit; [done|].
          rewrite /ofty_owned cbytes_at_loc. iFrame "Gho1". iExists bs. by iFrame. }
        iModIntro. iSplit; [done|]. by iFrame "G Own Gho1'". }
    wp_bind (Load _ _ _). iApply (wp_wand with "WPr"). iIntros (v) "(-> & G & Own & %Hvin & #Gho)".
    apply lty_vin_plug in Hvin as [Hvin2 Hvin].
    iDestruct (shr_bor_gho_view with "Gho") as "[%Hdh1' V0]".
    iDestruct (lc_weaken (gh1 + 1) with "£g") as "£g"; [lia|].
    iMod (lc_fupd_elim_laterN with "£g V0") as "#V".
    iDestruct (shr_view_depth_mono _ _ _ _ _ (pred dh1) D with "V") as "#V'"; [lia|lia|].
    wp_pure _. iSplit; [done|]. iExists (pred dh1). iFrame "G £r V'".
    iSplit; [iPureIntro; lia|]. iSplit; [iPureIntro; by apply pctx_vin_in|].
    iIntros (dh' Hdh') "G Vh". iApply ("HΦ" with "[%] [%] G Own Vh"); [lia|done].
  Qed.
End pshr_addr.

(** * Rules *)

Section typing.
  Context `{!typeG Σ}.

  (** ** (a) Changing the view of the referent of a shared reference *)

  (** At the root: the interpretation of [ShrLty lt κ] at a value is the leaf of its folded
      type and the variants, so the view of the referent can be changed for one with the
      same folded type and fewer variant constraints, without a program step. *)
  Lemma tctx_change_vplace_shr {ℭ 𝔅} E L p κ (K2: pctx ℭ 𝔅) (lt lt': lty ℭ) :
    lty_fold lt' = lty_fold lt → lty_nrc lt' = lty_nrc lt →
    (∀ y, lty_vin lt y → lty_vin lt' y) →
    tctx_incl E L +[p ◁ₗ ShrLty (pctx_plug K2 lt) κ] +[p ◁ₗ ShrLty (pctx_plug K2 lt') κ]
      (λ post '-[x], post -[x]).
  Proof.
    intros Hf Hn Hv.
    have Hf': lty_fold (pctx_plug K2 lt') = lty_fold (pctx_plug K2 lt) by apply lty_fold_plug_eq'.
    have Hn': lty_nrc (pctx_plug K2 lt') = lty_nrc (pctx_plug K2 lt) by apply lty_nrc_plug_eq.
    split; [by intros ??? [? []]|].
    iIntros (G tid [[x ζm] []] mask post ?) "_ _ _ _ _ $ [T _] Obs".
    iDestruct "T" as (v Hp D) "(⧖ & ⧗ & %d & %g & %Hle & Leaf & %Hvin)".
    iModIntro. iExists -[(x, ζm)]. iFrame "Obs". iSplit; [|done].
    iExists v. iSplit; [done|]. iExists D. iFrame "⧖". rewrite /lty_vnrc /= Hn'. iFrame "⧗".
    iExists d, g. iSplit; [done|]. rewrite Hf'. iFrame "Leaf". iPureIntro.
    move: Hvin. rewrite /= !lty_vin_plug. intros [? ?]. split; [done|]. by apply Hv.
  Qed.

  (** Below a root pointer, at the hole of [K]: an instance of [type_change_vplace_instr]. *)
  Lemma vplace_conv_shr {ℭ 𝔄} (K: pctx (at_locₛ ℭ) 𝔄) κ (lt lt': lty ℭ) :
    lty_fold lt' = lty_fold lt → (∀ y, lty_vin lt y → lty_vin lt' y) →
    vplace_conv K (ShrLty lt κ) (ShrLty lt' κ) (=).
  Proof.
    iIntros (Hf Hv x ζm dh gh D tid lh G E ? HE HdK ?) "_ _ _ _ _ G _ _ _ H".
    iDestruct "H" as "[H %Hin]".
    iModIntro. iExists (pctx_get K x), [], 1%Qp. iSplit; [done|].
    iSplit; [iPureIntro; intros ??; apply prfn_rsv_in|]. iSplitR; [done|]. iIntros "_ !>".
    iFrame "G". rewrite /= Hf. iFrame "H". iPureIntro. by apply Hv.
  Qed.

  Lemma vplace_conv_shr_unfold {𝔅 𝔄} (K: pctx (at_locₛ 𝔅) 𝔄) κ (ty: type 𝔅) :
    vplace_conv K (OfTy (&shr{κ} ty)%T) (ShrLty (OfTy ty) κ) (=).
  Proof.
    iIntros (x ζm dh gh D tid lh G E ? HE HdK ?) "_ _ _ _ _ G _ _ _ H".
    iModIntro. iExists (pctx_get K x), [], 1%Qp. iSplit; [done|].
    iSplit; [iPureIntro; intros ??; apply prfn_rsv_in|]. iSplitR; [done|]. iIntros "_ !>".
    by iFrame "G H".
  Qed.

  Lemma vplace_conv_shr_fold {𝔅 𝔄} (K: pctx (at_locₛ 𝔅) 𝔄) κ (ty: type 𝔅) :
    vplace_conv K (ShrLty (OfTy ty) κ) (OfTy (&shr{κ} ty)%T) (=).
  Proof.
    iIntros (x ζm dh gh D tid lh G E ? HE HdK ?) "_ _ _ _ _ G _ _ _ H".
    iDestruct "H" as "[H _]".
    iModIntro. iExists (pctx_get K x), [], 1%Qp. iSplit; [done|].
    iSplit; [iPureIntro; intros ??; apply prfn_rsv_in|]. iSplitR; [done|]. iIntros "_ !>".
    by iFrame "G H".
  Qed.

  Lemma type_unfold_vplace_shr_instr {𝔅 𝔄} E L I p (K: pctx (at_locₛ 𝔅) 𝔄) `{!PctxNoShr K}
      `{!PctxVRoot K} κ (ty: type 𝔅) :
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

  Lemma type_unfold_oplace_shr_instr {𝔅 𝔄} E L I p n (K: pctx (at_locₛ 𝔅) 𝔄) `{!PctxNoShr K}
      κ (ty: type 𝔅) :
    lctx_lft_alive E L (pctx_ulft K (OfTy (&shr{κ} ty)%T) ⊓ ty_lft (&shr{κ} ty)%T) →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K (OfTy (&shr{κ} ty)%T)] (Seq Skip Skip)
      (const +[p ◁ₗown{n} pctx_plug K (ShrLty (OfTy ty) κ)])
      (λ post '-[x], post -[x]).
  Proof. intros. by apply (type_unfold_vplace_shr_instr _ _ _ _ (POwn n K)). Qed.

  Lemma type_fold_vplace_shr_instr {𝔅 𝔄} E L I p (K: pctx (at_locₛ 𝔅) 𝔄) `{!PctxNoShr K}
      `{!PctxVRoot K} κ (ty: type 𝔅) :
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

  Lemma type_fold_oplace_shr_instr {𝔅 𝔄} E L I p n (K: pctx (at_locₛ 𝔅) 𝔄) `{!PctxNoShr K}
      κ (ty: type 𝔅) :
    lctx_lft_alive E L (pctx_ulft K (ShrLty (OfTy ty) κ) ⊓ ty_lft (&shr{κ} ty)%T) →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K (ShrLty (OfTy ty) κ)] (Seq Skip Skip)
      (const +[p ◁ₗown{n} pctx_plug K (OfTy (&shr{κ} ty)%T)])
      (λ post '-[x], post -[x]).
  Proof. intros. by apply (type_fold_vplace_shr_instr _ _ _ _ (POwn n K)). Qed.

  (** Changing the view of the hole of [K2] below the shared reference at the hole of [K]:
      e.g. unfolding a pair, an owned pointer, a unique borrow or a shared reference
      ([ShrLty] again) below [PShr]. *)
  Lemma type_change_vplace_shr_instr {ℭ 𝔅 𝔄} E L I p (K: pctx (at_locₛ 𝔅) 𝔄) `{!PctxNoShr K}
      `{!PctxVRoot K} κ (K2: pctx ℭ 𝔅) (lt lt': lty ℭ) :
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

  Lemma type_change_oplace_shr_instr {ℭ 𝔅 𝔄} E L I p n (K: pctx (at_locₛ 𝔅) 𝔄) `{!PctxNoShr K}
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

  (** The guarded typed load of a [Copy] value from its shared view. *)
  Lemma wp_load_shr_view {𝔄} `{!NoCell 𝔄} E κ (ty: type 𝔄) `{!Copy ty} z dh D tid (l: loc) (G: iProp Σ)
      (Φ: val → iProp Σ) :
    ↑NllftG ⊆ E → Timeless G →
    (G &&{↑NllftG}&&> @[κ]) -∗ G -∗ £(4 * (D + 1)) -∗ shr_view κ ty z dh D tid l -∗
    (∀ w, ⌜ty.(ty_val) z = Some w⌝ -∗ ty.(ty_gho_own) z dh D tid -∗ G -∗ Φ (MLitV w)) -∗
    WP Load Na1Ord ty.(ty_mty) #(l) @ E {{ Φ }}.
  Proof.
    iIntros (??) "#Gκ G £ #V HΦ".
    iDestruct (lc_weaken (((D + 1) + (D + 1)) + 2 * (D + 1)) with "£") as "[£c £l]"; [lia|].
    iMod (shr_view_copy with "Gκ G £c V") as (w Hw) "[#Gho G]"; [done..|].
    iDestruct "V" as "(Pt & _ & _)".
    iApply (wp_load_na_guarded_gen _ _ _ w G (cbytes ty z l) (ty_bytes ty z) (D + 1)
      with "[$G $£l]"); [done|intros; by eapply ty_bytes_decode| |].
    { iSplit; [iApply (guards_transitive_right with "Gκ Pt")|]. by iApply bytes_own_view. }
    iIntros "!> G". by iApply ("HΦ" with "[//] Gho G").
  Qed.

  (** Copying a value out of the hole of [K2], below the shared reference at the root
      (a guarded typed load). The place is unchanged. *)
  Lemma type_read_vplace_pshr_root_instr {ℭ 𝔅} E L I p κ (K2: pctx ℭ 𝔅) `{!NoCell ℭ} (lt: lty ℭ) :
    Copy (lty_fold lt) → lctx_lft_alive E L (pctx_salv K2 κ) →
    typed_instr E L I +[p ◁ₗ ShrLty (pctx_plug K2 lt) κ]
      (Load Na1Ord (lty_fold lt).(ty_mty) (pctx_expr K2 (ToLit p)))
      (λ v, +[v ◁ᵥ lty_fold lt; p ◁ₗ ShrLty (pctx_plug K2 lt) κ])
      (λ post '-[x], post -[pctx_get K2 x.1.2; x]).
  Proof.
    iIntros (Hcopy Alv tid post mask iκs [x []]) "#LFT #TIME #PROPH #UNIQ #E L I (Tp & _) Obs".
    destruct x as [x ζm].
    iDestruct "Tp" as (v Hp) "Tp". rewrite vplace_own_eq.
    iDestruct "Tp" as (D) "(#⧖ & ⧗p & Own)".
    iDestruct (Alv with "L E") as "#Alv".
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj|].
    iIntros "£ #⧖S". iApply wp_fupd.
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_salv K2 κ])%I as "#Hs".
    { iApply (guards_transitive with "Ghalf Alv"). }
    iDestruct (lc_weaken (pshr_cred D + 4 * (D + 1)) with "£") as "[£a £r]";
      [apply pshr_cred_step|].
    wp_bind (pctx_expr K2 (ToLit p)).
    iApply (wp_pshr_open_root _ κ K2 lt (pctx_plug K2 lt) x D tid v p (fractional.half γh)
      with "Hs H1 £a [] Own"); [solve_ndisj|done|done|..].
    { iApply wp_wand; [by iApply wp_eval_path|]. by iIntros (?) "->". }
    iIntros (dh Hdh [Hin2 Hvin]) "H1 Own #V".
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_slft K2 κ])%I as "#Hsl".
    { iApply (guards_transitive with "Hs"). iApply pctx_salv_slft. }
    iApply (wp_load_shr_view with "Hsl H1 £r V"); [solve_ndisj|].
    iIntros (w Hw) "#Gho H1".
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iModIntro. iExists -[pctx_get K2 x.2; (x, ζm)]. iFrame "L I Obs".
    iSplitR "Own ⧗p".
    { iExists _. iSplit; [by rewrite eval_path_of_val|]. iExists w, D. iSplit; [done|].
      iFrame "⧖". iDestruct (ty_gho_own_depth_mono _ dh D D D with "Gho") as "[$ _]"; lia. }
    iSplit; [|done]. iExists _. iSplit; [done|]. rewrite vplace_own_eq. iExists D. by iFrame.
  Qed.

  (** Copying a value out of the hole of [K2], below the shared reference at the hole of
      [K] (both at any path: below owned pointers, unique borrows, and further shared
      references), as [read_shr]. The place is unchanged. *)
  Lemma type_read_vplace_pshr_instr {ℭ 𝔅 𝔄} E L I p (K: pctx (at_locₛ 𝔅) 𝔄) `{!PctxNoShr K}
      `{!PctxVRoot K} κ (K2: pctx ℭ 𝔅) `{!NoCell ℭ} (lt: lty ℭ) :
    Copy (lty_fold lt) →
    lctx_lft_alive E L (pctx_ulft K (ShrLty (pctx_plug K2 lt) κ)) →
    lctx_lft_alive E L (pctx_salv K2 κ) →
    typed_instr E L I +[p ◁ₗ pctx_plug K (ShrLty (pctx_plug K2 lt) κ)]
      (Load Na1Ord (lty_fold lt).(ty_mty)
        (pctx_expr K2 (ToLit (Load Na1Ord MPtr (pctx_vexpr K p)))))
      (λ v, +[v ◁ᵥ lty_fold lt; p ◁ₗ pctx_plug K (ShrLty (pctx_plug K2 lt) κ)])
      (λ post '-[x], post -[pctx_get K2 (pctx_get K x.1).2; x]).
  Proof.
    iIntros (Hcopy Alv1 Alv2 tid post mask iκs [x []])
      "#LFT #TIME #PROPH #UNIQ #E L I (Tp & _) Obs".
    destruct x as [x₀ ζm].
    iDestruct "Tp" as (v Hp) "Tp". iEval (rewrite vplace_own_open) in "Tp".
    iDestruct "Tp" as (D) "(#⧖ & ⧗p & Own)".
    iDestruct (Alv1 with "L E") as "#Alv1". iDestruct (Alv2 with "L E") as "#Alv2".
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj|].
    iIntros "£ #⧖S". iApply wp_fupd.
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_ulft K (ShrLty (pctx_plug K2 lt) κ)])%I
      as "#Hu". { iApply (guards_transitive with "Ghalf Alv1"). }
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_salv K2 κ])%I as "#Hs".
    { iApply (guards_transitive with "Ghalf Alv2"). }
    iDestruct (lc_weaken (pshr_cred D + 4 * (D + 1)) with "£") as "[£a £r]";
      [apply pshr_cred_step|].
    set y := pctx_get K x₀.
    wp_bind (pctx_expr K2 _).
    iApply (wp_pshr_open _ K κ K2 lt (pctx_plug K2 lt) x₀ ζm D tid _ p (fractional.half γh)
      with "LFT PROPH UNIQ Hu Hs H1 £a ⧖ [] Own"); [solve_ndisj|done|done|..].
    { iApply wp_wand; [by iApply wp_eval_path|]. by iIntros (?) "->". }
    iIntros (dh Hdh [Hin1 [Hin2 Hvin]]) "H1 Own #V".
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_slft K2 κ])%I as "#Hsl".
    { iApply (guards_transitive with "Hs"). iApply pctx_salv_slft. }
    iApply (wp_load_shr_view with "Hsl H1 £r V"); [solve_ndisj|].
    iIntros (w Hw) "#Gho H1".
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iModIntro. iExists -[pctx_get K2 y.2; (x₀, ζm)]. iFrame "L I Obs".
    iSplitR "Own ⧗p".
    { iExists _. iSplit; [by rewrite eval_path_of_val|]. iExists w, D. iSplit; [done|].
      iFrame "⧖". iDestruct (ty_gho_own_depth_mono _ dh D D D with "Gho") as "[$ _]"; lia. }
    iSplit; [|done]. iExists _. iSplit; [done|]. by iApply (vplace_own_close with "⧖ ⧗p").
  Qed.

  Lemma type_read_oplace_pshr_instr {ℭ 𝔅 𝔄} E L I p n (K: pctx (at_locₛ 𝔅) 𝔄) `{!PctxNoShr K}
      κ (K2: pctx ℭ 𝔅) `{!NoCell ℭ} (lt: lty ℭ) :
    Copy (lty_fold lt) →
    lctx_lft_alive E L (pctx_ulft K (ShrLty (pctx_plug K2 lt) κ)) →
    lctx_lft_alive E L (pctx_salv K2 κ) →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K (ShrLty (pctx_plug K2 lt) κ)]
      (Load Na1Ord (lty_fold lt).(ty_mty)
        (pctx_expr K2 (ToLit (Load Na1Ord MPtr (pctx_expr K (ToLit p))))))
      (λ v, +[v ◁ᵥ lty_fold lt; p ◁ₗown{n} pctx_plug K (ShrLty (pctx_plug K2 lt) κ)])
      (λ post '-[x], post -[pctx_get K2 (pctx_get K x.1.2).2; x]).
  Proof. intros. by apply (type_read_vplace_pshr_instr _ _ _ _ (POwn n K)). Qed.

  (** ** (c) Shared borrow of a sub-place below a shared reference *)

  Lemma type_share_vplace_pshr_root_instr {ℭ 𝔅} E L I p κ (K2: pctx ℭ 𝔅) (lt: lty ℭ) :
    lctx_lft_alive E L (pctx_salv K2 κ) →
    typed_instr E L I +[p ◁ₗ ShrLty (pctx_plug K2 lt) κ] (OfLit (pctx_expr K2 (ToLit p)))
      (λ v, +[v ◁ᵥ &shr{pctx_slft K2 κ} (lty_fold lt); p ◁ₗ ShrLty (pctx_plug K2 lt) κ])
      (λ post '-[x], post -[(pctx_loc K2 (lty_size lt) x.1.2 x.1.1, pctx_get K2 x.1.2); x]).
  Proof.
    iIntros (Alv tid post mask iκs [x []]) "#LFT #TIME #PROPH #UNIQ #E L I (Tp & _) Obs".
    destruct x as [x ζm].
    iDestruct "Tp" as (v Hp) "Tp". rewrite vplace_own_eq.
    iDestruct "Tp" as (D) "(#⧖ & ⧗p & Own)".
    iDestruct (Alv with "L E") as "#Alv".
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj|].
    iIntros "£ #⧖S". iApply wp_fupd.
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_salv K2 κ])%I as "#Hs".
    { iApply (guards_transitive with "Ghalf Alv"). }
    iDestruct (lc_weaken (pshr_cred D) with "£") as "£a";
      [have := pshr_cred_step D; lia|].
    wp_bind (pctx_expr K2 (ToLit p)).
    iApply (wp_pshr_open_root _ κ K2 lt (pctx_plug K2 lt) x D tid v p (fractional.half γh)
      with "Hs H1 £a [] Own"); [solve_ndisj|done|done|..].
    { iApply wp_wand; [by iApply wp_eval_path|]. by iIntros (?) "->". }
    iIntros (dh Hdh [Hin2 Hvin]) "H1 Own #V".
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    wp_pure _. iModIntro.
    iExists -[(pctx_loc K2 (lty_size lt) x.2 x.1, pctx_get K2 x.2); (x, ζm)].
    iFrame "L I Obs". iSplitR "Own ⧗p".
    { rewrite tctx_val_val. iExists D. iFrame "⧖". iSplit; [done|].
      destruct D as [|D']; [lia|].
      iDestruct (shr_view_depth_mono _ _ _ _ _ D' (S D') with "V") as "#V'"; [lia|lia|].
      iApply (shr_bor_gho_of_view with "V'"). }
    iSplit; [|done]. iExists _. iSplit; [done|]. rewrite vplace_own_eq. iExists D. by iFrame.
  Qed.

  (** A shared reference to the hole of [K2] below the shared reference at the hole of [K]
      ([&( *r).f] for [r: &T], [&( **x).0] for [x: &mut &(T, U)], …), at the lifetime of
      the view of the hole ([pctx_slft K2 κ]: the innermost shared reference, intersected
      with the unique borrows below it). The place is unchanged; [K]'s borrows need only
      be alive during the instruction. *)
  Lemma type_share_vplace_pshr_instr {ℭ 𝔅 𝔄} E L I p (K: pctx (at_locₛ 𝔅) 𝔄)
      `{!PctxNoShr K} `{!PctxVRoot K} κ (K2: pctx ℭ 𝔅) (lt: lty ℭ) :
    lctx_lft_alive E L (pctx_ulft K (ShrLty (pctx_plug K2 lt) κ)) →
    lctx_lft_alive E L (pctx_salv K2 κ) →
    typed_instr E L I +[p ◁ₗ pctx_plug K (ShrLty (pctx_plug K2 lt) κ)]
      (OfLit (pctx_expr K2 (ToLit (Load Na1Ord MPtr (pctx_vexpr K p)))))
      (λ v, +[v ◁ᵥ &shr{pctx_slft K2 κ} (lty_fold lt);
        p ◁ₗ pctx_plug K (ShrLty (pctx_plug K2 lt) κ)])
      (λ post '-[x], post -[(pctx_loc K2 (lty_size lt) (pctx_get K x.1).2 (pctx_get K x.1).1,
        pctx_get K2 (pctx_get K x.1).2); x]).
  Proof.
    iIntros (Alv1 Alv2 tid post mask iκs [x []]) "#LFT #TIME #PROPH #UNIQ #E L I (Tp & _) Obs".
    destruct x as [x₀ ζm].
    iDestruct "Tp" as (v Hp) "Tp". iEval (rewrite vplace_own_open) in "Tp".
    iDestruct "Tp" as (D) "(#⧖ & ⧗p & Own)".
    iDestruct (Alv1 with "L E") as "#Alv1". iDestruct (Alv2 with "L E") as "#Alv2".
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj|].
    iIntros "£ #⧖S". iApply wp_fupd.
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_ulft K (ShrLty (pctx_plug K2 lt) κ)])%I
      as "#Hu". { iApply (guards_transitive with "Ghalf Alv1"). }
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_salv K2 κ])%I as "#Hs".
    { iApply (guards_transitive with "Ghalf Alv2"). }
    iDestruct (lc_weaken (pshr_cred D) with "£") as "£a";
      [have := pshr_cred_step D; lia|].
    set y := pctx_get K x₀.
    wp_bind (pctx_expr K2 _).
    iApply (wp_pshr_open _ K κ K2 lt (pctx_plug K2 lt) x₀ ζm D tid _ p (fractional.half γh)
      with "LFT PROPH UNIQ Hu Hs H1 £a ⧖ [] Own"); [solve_ndisj|done|done|..].
    { iApply wp_wand; [by iApply wp_eval_path|]. by iIntros (?) "->". }
    iIntros (dh Hdh [Hin1 [Hin2 Hvin]]) "H1 Own #V".
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    wp_pure _. iModIntro.
    iExists -[(pctx_loc K2 (lty_size lt) y.2 y.1, pctx_get K2 y.2); (x₀, ζm)].
    iFrame "L I Obs". iSplitR "Own ⧗p".
    { rewrite tctx_val_val. iExists D. iFrame "⧖". iSplit; [done|].
      destruct D as [|D']; [lia|].
      iDestruct (shr_view_depth_mono _ _ _ _ _ D' (S D') with "V") as "#V'"; [lia|lia|].
      iApply (shr_bor_gho_of_view with "V'"). }
    iSplit; [|done]. iExists _. iSplit; [done|]. by iApply (vplace_own_close with "⧖ ⧗p").
  Qed.

  Lemma type_share_oplace_pshr_instr {ℭ 𝔅 𝔄} E L I p n (K: pctx (at_locₛ 𝔅) 𝔄)
      `{!PctxNoShr K} κ (K2: pctx ℭ 𝔅) (lt: lty ℭ) :
    lctx_lft_alive E L (pctx_ulft K (ShrLty (pctx_plug K2 lt) κ)) →
    lctx_lft_alive E L (pctx_salv K2 κ) →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K (ShrLty (pctx_plug K2 lt) κ)]
      (OfLit (pctx_expr K2 (ToLit (Load Na1Ord MPtr (pctx_expr K (ToLit p))))))
      (λ v, +[v ◁ᵥ &shr{pctx_slft K2 κ} (lty_fold lt);
        p ◁ₗown{n} pctx_plug K (ShrLty (pctx_plug K2 lt) κ)])
      (λ post '-[x], post -[(pctx_loc K2 (lty_size lt) (pctx_get K x.1.2).2 (pctx_get K x.1.2).1,
        pctx_get K2 (pctx_get K x.1.2).2); x]).
  Proof. intros. by apply (type_share_vplace_pshr_instr _ _ _ _ (POwn n K)). Qed.
End typing.

(** * (d) Case analysis on a sum below a shared reference *)

Section case.
  Context `{!typeG Σ}.

  (** The guarded typed load of the tag of a sum from its shared view. *)
  Lemma wp_load_tag_shr_view {𝔄l} E κ (tyl: typel 𝔄l) j a dh D tid (l: loc)
      (G: iProp Σ) (Φ: val → iProp Σ) :
    ↑NllftG ⊆ E →
    (G &&{↑NllftG}&&> @[κ]) -∗ G -∗ £(2 * (D + 1)) -∗
    shr_view κ (Σ! tyl)%T (pinj j a) dh D tid l -∗
    (G -∗ Φ (MLitV (VInt (Z.of_nat (fin_to_nat j))))) -∗
    WP Load Na1Ord (MInt (sum_tag 𝔄l)) #(l) @ E {{ Φ }}.
  Proof.
    iIntros (?) "#Gκ G £ #(Pt & _ & _) HΦ".
    iEval (rewrite (cbytes_sum _ j (tyl +!! j))) in "Pt".
    iDestruct (guards_weaken_rhs_sep_l with "Pt") as "Pt'".
    iApply (wp_load_na_guarded_gen _ _ _ (VInt (Z.of_nat j)) G
      (tag_cell 𝔄l l j)
      (λ bs, decode_value (MInt (sum_tag 𝔄l)) bs = Some (VInt (Z.of_nat j))) (D + 1)
      with "[$G $£]"); [done|done| |].
    { iSplit; [iApply (guards_transitive_right with "Gκ Pt'")|].
      iIntros "!> (%bs & Hbs & %Hbs)". iExists bs. iFrame "Hbs".
      iSplit; [done|]. iIntros "Hbs". iExists bs. by iFrame. }
    iIntros "!> G". by iApply "HΦ".
  Qed.

  (** At the root: case analysis on the sum at the hole of [K2], below the shared reference
      at the root; the branch of the variant [i] gets the view
      [SumLty tyl i (OfTy (tyl +!! i))] at the hole. *)
  Lemma type_case_vplace_pshr_root {𝔄l 𝔅 𝔅l 𝔇} E L I (C: cctx 𝔇) p κ (K2: pctx (Σ! 𝔄l) 𝔅)
      (tyl: typel 𝔄l) (T: tctx 𝔅l) el el' trl :
    IntoPlistc el el' →
    lctx_lft_alive E L (pctx_salv K2 κ) →
    ([∗ nat] i < length 𝔄l, typed_body E L I C
      (p ◁ₗ ShrLty (pctx_plug K2 (SumLty tyl i (OfTy (tyl +!! i)))) κ +:: T)
      (el' -!! i) (trl -!! i)) -∗
    typed_body E L I C (p ◁ₗ ShrLty (pctx_plug K2 (OfTy (Σ! tyl))) κ +:: T)
      (case: ToLit (Load Na1Ord (MInt (sum_tag 𝔄l)) (pctx_expr K2 (ToLit p))) of el)
      (λ post '(x -:: cl), let 'xinj i _ := to_xsum (pctx_get K2 x.1.2).1 in
        (trl -!! i) post (x -:: cl))%type.
  Proof.
    move=> -> Alv. iIntros "el".
    iIntros (tid [x xl] mask post iκs) "#LFT #TIME #PROPH #UNIQ #E L I C /=[Tp T] #Obs".
    destruct x as [x ζm].
    iDestruct "Tp" as (v Hp) "Tp". rewrite vplace_own_eq.
    iDestruct "Tp" as (D) "(#⧖ & ⧗p & Own)".
    iDestruct (Alv with "L E") as "#Alv".
    remember (pctx_get K2 x.2) as s eqn:Hz.
    destruct (to_xsum s) as [j a] eqn:Hj.
    have Hs: s = pinj j a. { by rewrite -(semi_iso' to_xsum of_xsum s) Hj. }
    subst s.
    wp_bind (Load Na1Ord (MInt (sum_tag 𝔄l)) _)%E.
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj|].
    iIntros "£ #⧖S". iApply wp_fupd.
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_salv K2 κ])%I as "#Hs".
    { iApply (guards_transitive with "Ghalf Alv"). }
    iDestruct (lc_weaken (pshr_cred D + 2 * (D + 1)) with "£") as "[£a £r]";
      [have := pshr_cred_step D; lia|].
    set lt'' := pctx_plug K2 (SumLty tyl j (OfTy (tyl +!! j))).
    wp_bind (pctx_expr K2 (ToLit p)).
    iApply (wp_pshr_open_root _ κ K2 (OfTy (Σ! tyl)) lt'' x D tid v p (fractional.half γh)
      with "Hs H1 £a [] Own"); [solve_ndisj| |..].
    { apply lty_fold_plug_eq'. by rewrite lty_fold_sum_ofty. }
    { rewrite !lty_vin_plug -Hz /= psum_proj_pinj. naive_solver. }
    { iApply wp_wand; [by iApply wp_eval_path|]. by iIntros (?) "->". }
    iIntros (dh Hdh [Hin2 Hvin]) "H1 Own #V".
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_slft K2 κ])%I as "#Hsl".
    { iApply (guards_transitive with "Hs"). iApply pctx_salv_slft. }
    rewrite -Hz.
    iApply (wp_load_tag_shr_view with "Hsl H1 £r V"); [solve_ndisj|].
    iIntros "H1".
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iModIntro. wp_pure _.
    wp_case. { split; [lia|]. by rewrite Nat2Z.id -vlookup_lookup plistc_to_vec_lookup. }
    iDestruct (big_sepN_lookup _ _ j with "el") as "el".
    iApply ("el" $! _ ((x, ζm) -:: xl)
      with "LFT TIME PROPH UNIQ E L I C [-] []"); last first.
    { iApply proph_obs_impl; [|done]=>/= ?. by rewrite to_xsum_pinj. }
    iFrame "T". iExists _. iSplit; [done|]. rewrite vplace_own_eq. iExists D. iFrame "⧖ Own".
    rewrite /lty_vnrc /= /lt'' !lty_nrc_plug /=. iFrame "⧗p".
  Qed.

  (** Case analysis on the sum at the hole of [K2], below the shared reference at the hole
      of [K]: the tag is read through the view (a guarded typed load), and the branch of the
      variant [i] gets the place with the view [SumLty tyl i (OfTy (tyl +!! i))] at the
      hole (the referent does not change, so the variant is recorded in the place type,
      [lty_vin]). *)
  Lemma type_case_vplace_pshr {𝔄l 𝔅 𝔄 𝔅l 𝔇} E L I (C: cctx 𝔇) p (K: pctx (at_locₛ 𝔅) 𝔄)
      `{!PctxNoShr K} `{!PctxVRoot K} κ (K2: pctx (Σ! 𝔄l) 𝔅) (tyl: typel 𝔄l) (T: tctx 𝔅l)
      el el' trl :
    IntoPlistc el el' →
    lctx_lft_alive E L (pctx_ulft K (ShrLty (pctx_plug K2 (OfTy (Σ! tyl))) κ)) →
    lctx_lft_alive E L (pctx_salv K2 κ) →
    ([∗ nat] i < length 𝔄l, typed_body E L I C
      (p ◁ₗ pctx_plug K (ShrLty (pctx_plug K2 (SumLty tyl i (OfTy (tyl +!! i)))) κ) +:: T)
      (el' -!! i) (trl -!! i)) -∗
    typed_body E L I C (p ◁ₗ pctx_plug K (ShrLty (pctx_plug K2 (OfTy (Σ! tyl))) κ) +:: T)
      (case: ToLit (Load Na1Ord (MInt (sum_tag 𝔄l))
        (pctx_expr K2 (ToLit (Load Na1Ord MPtr (pctx_vexpr K p))))) of el)
      (λ post '(x -:: cl), let 'xinj i _ := to_xsum (pctx_get K2 (pctx_get K x.1).2).1 in
        (trl -!! i) post (x -:: cl))%type.
  Proof.
    move=> -> Alv1 Alv2. iIntros "el".
    iIntros (tid [x xl] mask post iκs) "#LFT #TIME #PROPH #UNIQ #E L I C /=[Tp T] #Obs".
    destruct x as [x₀ ζm].
    iDestruct "Tp" as (v Hp) "Tp". iEval (rewrite vplace_own_open) in "Tp".
    iDestruct "Tp" as (D) "(#⧖ & ⧗p & Own)".
    iDestruct (Alv1 with "L E") as "#Alv1". iDestruct (Alv2 with "L E") as "#Alv2".
    set y := pctx_get K x₀.
    remember (pctx_get K2 y.2) as s eqn:Hz.
    destruct (to_xsum s) as [j a] eqn:Hj.
    have Hs: s = pinj j a. { by rewrite -(semi_iso' to_xsum of_xsum s) Hj. }
    subst s.
    wp_bind (Load Na1Ord (MInt (sum_tag 𝔄l)) _)%E.
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj|].
    iIntros "£ #⧖S". iApply wp_fupd.
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iAssert (fractional.half γh &&{↑NllftG}&&>
      @[pctx_ulft K (ShrLty (pctx_plug K2 (OfTy (Σ! tyl))) κ)])%I
      as "#Hu". { iApply (guards_transitive with "Ghalf Alv1"). }
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_salv K2 κ])%I as "#Hs".
    { iApply (guards_transitive with "Ghalf Alv2"). }
    iDestruct (lc_weaken (pshr_cred D + 2 * (D + 1)) with "£") as "[£a £r]";
      [have := pshr_cred_step D; lia|].
    set lt'' := pctx_plug K2 (SumLty tyl j (OfTy (tyl +!! j))).
    wp_bind (pctx_expr K2 _).
    iApply (wp_pshr_open _ K κ K2 (OfTy (Σ! tyl)) lt'' x₀ ζm D tid _ p (fractional.half γh)
      with "LFT PROPH UNIQ Hu Hs H1 £a ⧖ [] Own"); [solve_ndisj| |..].
    { apply lty_fold_plug_eq'. by rewrite lty_fold_sum_ofty. }
    { rewrite !lty_vin_plug -/y -Hz /= psum_proj_pinj. naive_solver. }
    { iApply wp_wand; [by iApply wp_eval_path|]. by iIntros (?) "->". }
    iIntros (dh Hdh [Hin1 [Hin2 Hvin]]) "H1 Own #V".
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_slft K2 κ])%I as "#Hsl".
    { iApply (guards_transitive with "Hs"). iApply pctx_salv_slft. }
    rewrite -Hz.
    iApply (wp_load_tag_shr_view with "Hsl H1 £r V"); [solve_ndisj|].
    iIntros "H1".
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iModIntro. wp_pure _.
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

  Lemma type_case_oplace_pshr {𝔄l 𝔅 𝔄 𝔅l 𝔇} E L I (C: cctx 𝔇) p n (K: pctx (at_locₛ 𝔅) 𝔄)
      `{!PctxNoShr K} κ (K2: pctx (Σ! 𝔄l) 𝔅) (tyl: typel 𝔄l) (T: tctx 𝔅l) el el' trl :
    IntoPlistc el el' →
    lctx_lft_alive E L (pctx_ulft K (ShrLty (pctx_plug K2 (OfTy (Σ! tyl))) κ)) →
    lctx_lft_alive E L (pctx_salv K2 κ) →
    ([∗ nat] i < length 𝔄l, typed_body E L I C
      (p ◁ₗown{n} pctx_plug K (ShrLty (pctx_plug K2 (SumLty tyl i (OfTy (tyl +!! i)))) κ) +:: T)
      (el' -!! i) (trl -!! i)) -∗
    typed_body E L I C (p ◁ₗown{n} pctx_plug K (ShrLty (pctx_plug K2 (OfTy (Σ! tyl))) κ) +:: T)
      (case: ToLit (Load Na1Ord (MInt (sum_tag 𝔄l))
        (pctx_expr K2 (ToLit (Load Na1Ord MPtr (pctx_expr K (ToLit p)))))) of el)
      (λ post '(x -:: cl), let 'xinj i _ := to_xsum (pctx_get K2 (pctx_get K x.1.2).2).1 in
        (trl -!! i) post (x -:: cl))%type.
  Proof.
    iIntros (???) "el".
    iApply (type_case_vplace_pshr E L I C p (POwn n K) κ K2 tyl T el el' trl with "el"); done.
  Qed.
End case.

(** * (e) Resolving and dropping places with shared references *)

Section rslv.
  Context `{!typeG Σ}.

  (** A shared reference (with any view of its referent) is a leaf: it is forgotten (its
      ownership is persistent; nothing below it is owned), and its memory, the bytes of the
      pointer, is given back ([lty_omem]). With [type_drop_oplace_deep_instr] and
      [resolve_tctx_cons_oplace_deep], owned places containing shared references are
      dropped and resolved. *)
  Lemma lty_rslv_shr {𝔄} E L (lt: lty 𝔄) κ : lty_rslv E L (ShrLty lt κ) (λ _ _ _ _, True).
  Proof. apply (lty_rslv_of _ _ _ (λ _ _, True)), lty_resolve_just. Qed.

  (** A place rooted at a shared reference is dropped: its ownership is persistent. *)
  Lemma tctx_drop_vplace_shr {𝔄} E L p κ (lt: lty 𝔄) :
    tctx_incl E L +[p ◁ₗ ShrLty lt κ] +[] (λ post _, post -[]).
  Proof.
    split; [intros ?? Eq [? []] ??; by apply Eq|].
    iIntros (G tid [x []] mask post ?) "_ _ _ _ _ $ _ Obs".
    iModIntro. iExists -[]. by iFrame "Obs".
  Qed.
End rslv.

(** * Byte copies below shared references *)

Section memcpy.
  Context `{!typeG Σ}.

  (** Copying the value of a [Copy] type out of the hole of [K2] below the shared reference
      at the hole of [K] into a box: a byte-level [MemCopy] whose source is guarded
      ([wp_memcopy_guarded_gen]). The old contents of the box are resolved; the place does
      not change. The first step (the address of the box) gives the credits for the
      address of the source, the copy itself those for the box. *)
  Lemma type_memcpy_copy_from_vplace_pshr_instr {ℭ 𝔅 𝔄 𝔅'} E L I pw p n
      (K: pctx (at_locₛ 𝔅) 𝔄) `{!PctxNoShr K} `{!PctxVRoot K} κ (K2: pctx ℭ 𝔅) `{!NoCell ℭ} (lt: lty ℭ)
      (tyw: type 𝔅') Φ (sz: nat) :
    Copy (lty_fold lt) → resolve E L tyw Φ → sz = ty_bsize (lty_fold lt) → ty_bsize tyw = sz →
    lctx_lft_alive E L (pctx_ulft K (ShrLty (pctx_plug K2 lt) κ)) →
    lctx_lft_alive E L (pctx_salv K2 κ) →
    typed_instr E L I +[pw ◁ᵥ own_bytes n tyw; p ◁ₗ pctx_plug K (ShrLty (pctx_plug K2 lt) κ)]
      (MemCopy Na1Ord sz (ToLit pw) (pctx_expr K2 (ToLit (Load Na1Ord MPtr (pctx_vexpr K p)))))
      (λ _, +[pw ◁ᵥ own_bytes n (lty_fold lt); p ◁ₗ pctx_plug K (ShrLty (pctx_plug K2 lt) κ)])
      (λ post '-[b; x], λ mask π, Φ b.2 π →
        post -[(b.1, pctx_get K2 (pctx_get K x.1).2); x] mask π).
  Proof.
    iIntros (Hcopy Rslv -> Hszw Alv1 Alv2 tid post mask iκs [[lw z] [x []]])
      "#LFT #TIME #PROPH #UNIQ #E L I (Tw & Tp & _) Obs".
    destruct x as [x₀ ζm].
    iDestruct "Tp" as (v Hp) "Tp". iEval (rewrite vplace_own_open) in "Tp".
    iDestruct "Tp" as (D) "(#⧖ & ⧗p & Own)".
    iDestruct "Tw" as (vw Hpw ww dw [-> Hww]) "(#⧖w & Tw)". simpl in Hww. simplify_eq.
    destruct dw as [|dw]; [done|]. iDestruct "Tw" as "(Bs & Fr & Gw0)".
    iApply (wp_bytes_own_forget with "Bs"); [solve_ndisj|]. iIntros (bsw) "Hbsw %Hlenw".
    iDestruct (Alv1 with "L E") as "#Alv1". iDestruct (Alv2 with "L E") as "#Alv2".
    iCombine "⧖ ⧖w" as "⧖m".
    set M := D `max` (S dw).
    have HM: D ≤ M ∧ S dw ≤ M by rewrite /M; lia.
    iDestruct (vroot_own_depth_mono _ _ D M with "Own") as "Own"; [lia|].
    (* The first step (the address of the box): credits for the address of the source. *)
    wp_bind (ToLit pw).
    iApply (wp_persistent_time_receipt with "TIME ⧖m"); [solve_ndisj|].
    iIntros "£ #⧖S". wp_bind pw. iApply wp_wand; [by iApply wp_eval_path|].
    iIntros (?) "->". wp_pure _.
    (* The copy: credits for the box and the copy. *)
    iApply (wp_persistent_time_receipt with "TIME ⧖S"); [solve_ndisj|].
    iIntros "£' #⧖SS". iApply wp_fupd.
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_ulft K (ShrLty (pctx_plug K2 lt) κ)])%I
      as "#Hu". { iApply (guards_transitive with "Ghalf Alv1"). }
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_salv K2 κ])%I as "#Hs".
    { iApply (guards_transitive with "Ghalf Alv2"). }
    iDestruct (lc_weaken (pshr_cred M) with "£") as "£a"; [have := pshr_cred_step M; lia|].
    iDestruct (lc_weaken (((M + 1) + (M + 1)) + (1 + ((1 + M * (M + 1)) + (1 + 2 * (M + 1)))))
      with "£'") as "(£c & £r & £s & £b & £m)"; [rewrite /advance_credits; nia|].
    set y := pctx_get K x₀.
    wp_bind (pctx_expr K2 _).
    iApply (wp_pshr_open _ K κ K2 lt (pctx_plug K2 lt) x₀ ζm M tid _ p (fractional.half γh)
      with "LFT PROPH UNIQ Hu Hs H1 £a ⧖m [] Own"); [solve_ndisj|done|done|..].
    { iApply wp_wand; [by iApply wp_eval_path|]. by iIntros (?) "->". }
    iIntros (dh Hdh [Hin1 [Hin2 Hvin]]) "H1 Own #V".
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_slft K2 κ])%I as "#Hsl".
    { iApply (guards_transitive with "Hs"). iApply pctx_salv_slft. }
    set zz := pctx_get K2 y.2.
    set lK := pctx_loc K2 (lty_size lt) y.2 y.1.
    iMod (shr_view_copy with "Hsl H1 £c V") as (w Hw) "[#Gho H1]"; [solve_ndisj|].
    (* Resolve the old contents of the box. *)
    iMod (lc_fupd_elim_later with "£b Gw0") as "Gw0".
    iDestruct (Rslv _ (⊤ ∖ (⊤ ∖ ↑Nllft ∖ ↑prophN ∖ ↑timeN ∖ ↑uniqN))
      with "LFT PROPH UNIQ TIME E Ghalf H2 Gw0") as "ToObs"; [set_solver|].
    iMod (lc_fupd_elim_later with "£r ToObs") as "ToObs".
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iDestruct (lc_step_fupdN_elim_later with "[£s] ToObs") as "ToObs".
    { iApply (lc_weaken with "£s"). nia. }
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iMod (fupd_mask_mono with "ToObs") as "[Obs' H2]"; [solve_ndisj|].
    (* Copy the bytes. *)
    iDestruct "V" as "(Pt & _ & _)".
    iApply (wp_memcopy_guarded_gen _ lw lK bsw (ty_bsize (lty_fold lt)) (fractional.half γh)
      (cbytes (lty_fold lt) zz lK) (ty_bytes (lty_fold lt) zz) (M + 1) with "[$Hbsw $H1 $£m]");
      [solve_ndisj|by rewrite Hlenw Hszw|intros ?; apply ty_bytes_length|..].
    { iSplit; [iApply (guards_transitive_right with "Hsl Pt")|]. iApply bytes_own_view_nocell. }
    iIntros "!>" (bs2) "(%Hbs2 & Hbsw & H1)".
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iModIntro. iExists -[(lw, zz); (x₀, ζm)]. iFrame "L I".
    iSplitR "Obs Obs'".
    { iSplitL "Hbsw Fr"; [|iSplitL; [|done]].
      - iExists _. iSplit; [done|]. iExists (VPtr lw), (S (S M)). iSplit; [done|].
        iSplit; [done|].
        iSplitL "Hbsw"; [by iApply bytes_own_of_bytes|]. iSplitL "Fr".
        + by rewrite -Hszw.
        + iNext. iDestruct (ty_gho_own_depth_mono _ dh M (S M) (S (S M)) with "Gho") as "[$ _]";
            lia.
      - iExists _. iSplit; [done|]. by iApply (vplace_own_close with "⧖m ⧗p Own"). }
    iCombine "Obs Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=> π [Hπ HΦ].
    by apply Hπ.
  Qed.

  Lemma type_memcpy_copy_from_oplace_pshr_instr {ℭ 𝔅 𝔄 𝔅'} E L I pw p n n'
      (K: pctx (at_locₛ 𝔅) 𝔄) `{!PctxNoShr K} κ (K2: pctx ℭ 𝔅) `{!NoCell ℭ} (lt: lty ℭ)
      (tyw: type 𝔅') Φ (sz: nat) :
    Copy (lty_fold lt) → resolve E L tyw Φ → sz = ty_bsize (lty_fold lt) → ty_bsize tyw = sz →
    lctx_lft_alive E L (pctx_ulft K (ShrLty (pctx_plug K2 lt) κ)) →
    lctx_lft_alive E L (pctx_salv K2 κ) →
    typed_instr E L I
      +[pw ◁ᵥ own_bytes n tyw; p ◁ₗown{n'} pctx_plug K (ShrLty (pctx_plug K2 lt) κ)]
      (MemCopy Na1Ord sz (ToLit pw)
        (pctx_expr K2 (ToLit (Load Na1Ord MPtr (pctx_expr K (ToLit p))))))
      (λ _, +[pw ◁ᵥ own_bytes n (lty_fold lt);
        p ◁ₗown{n'} pctx_plug K (ShrLty (pctx_plug K2 lt) κ)])
      (λ post '-[b; x], λ mask π, Φ b.2 π →
        post -[(b.1, pctx_get K2 (pctx_get K x.1.2).2); x] mask π).
  Proof. intros. by apply (type_memcpy_copy_from_vplace_pshr_instr _ _ _ _ _ _ (POwn n' K)). Qed.

  (** The same, below the shared reference at the root. *)
  Lemma type_memcpy_copy_from_vplace_pshr_root_instr {ℭ 𝔅 𝔅'} E L I pw p n κ
      (K2: pctx ℭ 𝔅) `{!NoCell ℭ} (lt: lty ℭ) (tyw: type 𝔅') Φ (sz: nat) :
    Copy (lty_fold lt) → resolve E L tyw Φ → sz = ty_bsize (lty_fold lt) → ty_bsize tyw = sz →
    lctx_lft_alive E L (pctx_salv K2 κ) →
    typed_instr E L I +[pw ◁ᵥ own_bytes n tyw; p ◁ₗ ShrLty (pctx_plug K2 lt) κ]
      (MemCopy Na1Ord sz (ToLit pw) (pctx_expr K2 (ToLit p)))
      (λ _, +[pw ◁ᵥ own_bytes n (lty_fold lt); p ◁ₗ ShrLty (pctx_plug K2 lt) κ])
      (λ post '-[b; x], λ mask π, Φ b.2 π → post -[(b.1, pctx_get K2 x.1.2); x] mask π).
  Proof.
    iIntros (Hcopy Rslv -> Hszw Alv tid post mask iκs [[lw z] [x []]])
      "#LFT #TIME #PROPH #UNIQ #E L I (Tw & Tp & _) Obs".
    destruct x as [x ζm].
    iDestruct "Tp" as (v Hp) "Tp". rewrite vplace_own_eq.
    iDestruct "Tp" as (D) "(#⧖ & ⧗p & Own)".
    iDestruct "Tw" as (vw Hpw ww dw [-> Hww]) "(#⧖w & Tw)". simpl in Hww. simplify_eq.
    destruct dw as [|dw]; [done|]. iDestruct "Tw" as "(Bs & Fr & Gw0)".
    iApply (wp_bytes_own_forget with "Bs"); [solve_ndisj|]. iIntros (bsw) "Hbsw %Hlenw".
    iDestruct (Alv with "L E") as "#Alv".
    iCombine "⧖ ⧖w" as "⧖m".
    set M := D `max` (S dw).
    have HM: D ≤ M ∧ S dw ≤ M by rewrite /M; lia.
    iDestruct (vroot_own_depth_mono _ _ D M with "Own") as "Own"; [lia|].
    wp_bind (ToLit pw).
    iApply (wp_persistent_time_receipt with "TIME ⧖m"); [solve_ndisj|].
    iIntros "£ #⧖S". wp_bind pw. iApply wp_wand; [by iApply wp_eval_path|].
    iIntros (?) "->". wp_pure _.
    iApply (wp_persistent_time_receipt with "TIME ⧖S"); [solve_ndisj|].
    iIntros "£' #⧖SS". iApply wp_fupd.
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_salv K2 κ])%I as "#Hs".
    { iApply (guards_transitive with "Ghalf Alv"). }
    iDestruct (lc_weaken (pshr_cred M) with "£") as "£a"; [have := pshr_cred_step M; lia|].
    iDestruct (lc_weaken (((M + 1) + (M + 1)) + (1 + ((1 + M * (M + 1)) + (1 + 2 * (M + 1)))))
      with "£'") as "(£c & £r & £s & £b & £m)"; [rewrite /advance_credits; nia|].
    wp_bind (pctx_expr K2 (ToLit p)).
    iApply (wp_pshr_open_root _ κ K2 lt (pctx_plug K2 lt) x M tid v p (fractional.half γh)
      with "Hs H1 £a [] Own"); [solve_ndisj|done|done|..].
    { iApply wp_wand; [by iApply wp_eval_path|]. by iIntros (?) "->". }
    iIntros (dh Hdh [Hin2 Hvin]) "H1 Own #V".
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_slft K2 κ])%I as "#Hsl".
    { iApply (guards_transitive with "Hs"). iApply pctx_salv_slft. }
    set zz := pctx_get K2 x.2.
    set lK := pctx_loc K2 (lty_size lt) x.2 x.1.
    iMod (shr_view_copy with "Hsl H1 £c V") as (w Hw) "[#Gho H1]"; [solve_ndisj|].
    iMod (lc_fupd_elim_later with "£b Gw0") as "Gw0".
    iDestruct (Rslv _ (⊤ ∖ (⊤ ∖ ↑Nllft ∖ ↑prophN ∖ ↑timeN ∖ ↑uniqN))
      with "LFT PROPH UNIQ TIME E Ghalf H2 Gw0") as "ToObs"; [set_solver|].
    iMod (lc_fupd_elim_later with "£r ToObs") as "ToObs".
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iDestruct (lc_step_fupdN_elim_later with "[£s] ToObs") as "ToObs".
    { iApply (lc_weaken with "£s"). nia. }
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iMod (fupd_mask_mono with "ToObs") as "[Obs' H2]"; [solve_ndisj|].
    iDestruct "V" as "(Pt & _ & _)".
    iApply (wp_memcopy_guarded_gen _ lw lK bsw (ty_bsize (lty_fold lt)) (fractional.half γh)
      (cbytes (lty_fold lt) zz lK) (ty_bytes (lty_fold lt) zz) (M + 1) with "[$Hbsw $H1 $£m]");
      [solve_ndisj|by rewrite Hlenw Hszw|intros ?; apply ty_bytes_length|..].
    { iSplit; [iApply (guards_transitive_right with "Hsl Pt")|]. iApply bytes_own_view_nocell. }
    iIntros "!>" (bs2) "(%Hbs2 & Hbsw & H1)".
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iModIntro. iExists -[(lw, zz); (x, ζm)]. iFrame "L I".
    iSplitR "Obs Obs'".
    { iSplitL "Hbsw Fr"; [|iSplitL; [|done]].
      - iExists _. iSplit; [done|]. iExists (VPtr lw), (S (S M)). iSplit; [done|].
        iSplit; [done|].
        iSplitL "Hbsw"; [by iApply bytes_own_of_bytes|]. iSplitL "Fr".
        + by rewrite -Hszw.
        + iNext. iDestruct (ty_gho_own_depth_mono _ dh M (S M) (S (S M)) with "Gho") as "[$ _]";
            lia.
      - iExists _. iSplit; [done|]. rewrite vplace_own_eq. iExists M. by iFrame. }
    iCombine "Obs Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=> π [Hπ HΦ].
    by apply Hπ.
  Qed.
End memcpy.
