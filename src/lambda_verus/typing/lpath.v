(** * Paths and place contexts

  Access to a subplace of a (nested) place type, in the style of the place
  contexts of RefinedRust (paper §5.3; [typed_place] in [rust_typing/programs.v]
  of the RefinedRust development). For now, the subplaces are fields of (nested)
  products.

  - A _place context_ [K : pctx 𝔅 𝔄] is a place type of [𝔄] with a hole of
    type [𝔅]. It is given from the root: [PFst K lt2] is a pair whose field 0 is
    the context [K] and whose field 1 has the place type [lt2] ([PSnd] dually).
    [pctx_plug K lt] plugs a place type into the hole.
  - The hole has a value ([pctx_get], [pctx_set] on values of the root), a
    _path_ from the root ([pctx_path], a list of field selectors, innermost
    first), an offset from the root ([pctx_off]) and a location ([pctx_loc]),
    which depends on the size of the hole.
  - The refinement of a place is computed from the current value of the root and
    a _blocking map_ [ζm] from the paths of blocked leaves to the prophecy ids of
    their reborrows ([lty_rfn]); a blocked leaf is refined by the final value of
    its reborrow ([PlaceGhost]). The blocking map is stored in the value of a place
    element ([typing/place.v]). The refinement of a plugged place is the plugged
    refinement ([lty_rfn_plug], [pctx_rfn]); adding an entry for the path of the
    hole does not change the refinements of the rest ([pctx_rfn_blk_cons]).
  - In [Owned] mode, the ownership of a plugged place splits into the ownership
    of the hole and of the rest ([ltype_own_plug]); the rest does not depend on
    the hole. *)

From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type ltype.
From lrust.typing Require Import uniq_util.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅 ℭ: syn_type.

(** * Paths and blocking maps *)

(** A path from the root of a place: field selectors ([false] for field 0, [true]
    for field 1), innermost first. *)
Notation lpath := (list bool).

(** The value of a blocking map, as stored in a place element. *)
Notation blk_mapₛ := (listₛ (listₛ boolₛ * positiveₛ))%ST.
Notation blk_map := (list (list bool * positive)).

Fixpoint blk_lookup (ζm: blk_map) (q: lpath) : positive :=
  match ζm with
  | [] => 1%positive
  | (q', ζi) :: ζm' => if decide (q = q') then ζi else blk_lookup ζm' q
  end.

Lemma lpath_app_cons_ne (r s q: lpath) (a b: bool) :
  a ≠ b → r ++ a :: q ≠ s ++ b :: q.
Proof.
  intros Hab Heq. have Hlen: length r = length s.
  { have := f_equal length Heq. rewrite !length_app /=. lia. }
  apply app_inj_1 in Heq as [_ Heq]; [|done]. by injection Heq.
Qed.

(** * Refinements of places *)

Section lty_rfn.
  Context `{!typeG Σ}.

  (** The refinement of a place [lt] at path [q], with current value [x] and blocking
      map [ζm]. *)
  Fixpoint lty_rfn {𝔄} (lt: lty 𝔄) : ~~𝔄 → blk_map → lpath → prfn 𝔄 :=
    match lt in lty 𝔄 return ~~𝔄 → blk_map → lpath → prfn 𝔄 with
    | OfTy _ => λ x _ _, inl (PlaceIn x)
    | Blocked _ _ => λ x ζm q, inl (PlaceGhost x (blk_lookup ζm q))
    (* Unfolded borrows and owned pointers are not supported yet. *)
    | UniqLty _ _ => λ x _ _, inl (PlaceIn x)
    | OwnPtrLty _ _ => λ x _ _, inl (PlaceIn x)
    | ProdLty lt1 lt2 => λ x ζm q,
        inr (lty_rfn lt1 x.1 ζm (false :: q), lty_rfn lt2 x.2 ζm (true :: q))
    end.

  (** The refinement only depends on the entries of the blocking map below [q]. *)
  Lemma lty_rfn_blk_irrel {𝔄} (lt: lty 𝔄) x ζm ζm' q :
    (∀ r, blk_lookup ζm (r ++ q) = blk_lookup ζm' (r ++ q)) →
    lty_rfn lt x ζm q = lty_rfn lt x ζm' q.
  Proof.
    induction lt as [| |𝔄 lt IH κ|𝔄 n lt IH|𝔄 𝔅 lt1 IH1 lt2 IH2] in x, q |- *;
      intros Heq; simpl; [done| |done|done|].
    - by rewrite (Heq []).
    - rewrite (IH1 _ (false :: q)); [rewrite (IH2 _ (true :: q)); [done|]|].
      + intros r. rewrite (_: r ++ true :: q = (r ++ [true]) ++ q); [apply Heq|].
        by rewrite -app_assoc.
      + intros r. rewrite (_: r ++ false :: q = (r ++ [false]) ++ q); [apply Heq|].
        by rewrite -app_assoc.
  Qed.

  (** The number of blocked leaves. *)
  Fixpoint lty_nblk {𝔄} (lt: lty 𝔄) : nat :=
    match lt with
    | Blocked _ _ => 1
    | ProdLty lt1 lt2 => lty_nblk lt1 + lty_nblk lt2
    | _ => 0
    end.

  (** All leaves are blocked. *)
  Fixpoint lty_blk_all {𝔄} (lt: lty 𝔄) : Prop :=
    match lt with
    | Blocked _ _ => True
    | ProdLty lt1 lt2 => lty_blk_all lt1 ∧ lty_blk_all lt2
    | _ => False
    end.

  (** If all leaves are blocked, the denotation of the refinement depends only on
      the variables of any reservation for it. *)
  Lemma lty_blk_all_dep {𝔄} (lt: lty 𝔄) x ζm q ζl :
    lty_blk_all lt → prfn_rsv (lty_rfn lt x ζm q) ζl → prfn_den (lty_rfn lt x ζm q) ./ ζl.
  Proof.
    induction lt as [| |𝔄 lt IH κ|𝔄 n lt IH|𝔄 𝔅 lt1 IH1 lt2 IH2] in x, q |- *;
      intros Hb Hr; try done.
    - simpl in *. rewrite prfn_den_inl. by rewrite prfn_rsv_inl in Hr.
    - destruct Hb as [Hb1 Hb2]. destruct Hr as [Hr1 Hr2].
      apply (proph_dep_weaken _ (ζl ++ ζl)); [set_solver|].
      apply (proph_dep_constr2 pair); [by apply IH1|by apply IH2].
  Qed.
End lty_rfn.

(** * Place contexts *)

Section pctx.
  Context `{!typeG Σ}.

  Inductive pctx : syn_type → syn_type → Type :=
  | PHole {𝔅} : pctx 𝔅 𝔅
  | PFst {𝔅 𝔄1 𝔄2} (K: pctx 𝔅 𝔄1) (lt2: lty 𝔄2) : pctx 𝔅 (𝔄1 * 𝔄2)
  | PSnd {𝔅 𝔄1 𝔄2} (lt1: lty 𝔄1) (K: pctx 𝔅 𝔄2) : pctx 𝔅 (𝔄1 * 𝔄2).

  Definition pctx_nonempty {𝔅 𝔄} (K: pctx 𝔅 𝔄) : Prop :=
    match K with PHole => False | _ => True end.

  Fixpoint pctx_plug {𝔅 𝔄} (K: pctx 𝔅 𝔄) : lty 𝔅 → lty 𝔄 :=
    match K in pctx 𝔅 𝔄 return lty 𝔅 → lty 𝔄 with
    | PHole => λ lt, lt
    | PFst K lt2 => λ lt, ProdLty (pctx_plug K lt) lt2
    | PSnd lt1 K => λ lt, ProdLty lt1 (pctx_plug K lt)
    end.

  Fixpoint pctx_get {𝔅 𝔄} (K: pctx 𝔅 𝔄) : ~~𝔄 → ~~𝔅 :=
    match K in pctx 𝔅 𝔄 return ~~𝔄 → ~~𝔅 with
    | PHole => λ x, x
    | PFst K _ => λ x, pctx_get K x.1
    | PSnd _ K => λ x, pctx_get K x.2
    end.

  Fixpoint pctx_set {𝔅 𝔄} (K: pctx 𝔅 𝔄) : ~~𝔄 → ~~𝔅 → ~~𝔄 :=
    match K in pctx 𝔅 𝔄 return ~~𝔄 → ~~𝔅 → ~~𝔄 with
    | PHole => λ _ y, y
    | PFst K _ => λ x y, (pctx_set K x.1 y, x.2)
    | PSnd _ K => λ x y, (x.1, pctx_set K x.2 y)
    end.

  (** The path of the hole, from a place at path [q]. *)
  Fixpoint pctx_path {𝔅 𝔄} (K: pctx 𝔅 𝔄) (q: lpath) : lpath :=
    match K with
    | PHole => q
    | PFst K _ => pctx_path K (false :: q)
    | PSnd _ K => pctx_path K (true :: q)
    end.

  (** The size of the place, for a hole of size [n]. *)
  Fixpoint pctx_size {𝔅 𝔄} (K: pctx 𝔅 𝔄) (n: nat) : nat :=
    match K with
    | PHole => n
    | PFst K lt2 => pctx_size K n + lty_size lt2
    | PSnd lt1 K => lty_size lt1 + pctx_size K n
    end.

  (** The offset of the hole. *)
  Fixpoint pctx_off {𝔅 𝔄} (K: pctx 𝔅 𝔄) : nat :=
    match K with
    | PHole => 0
    | PFst K _ => pctx_off K
    | PSnd lt1 K => lty_size lt1 + pctx_off K
    end.

  (** The location of the hole (of size [n]), in a place at [l]. *)
  Fixpoint pctx_loc {𝔅 𝔄} (K: pctx 𝔅 𝔄) (n: nat) (l: cloc) : cloc :=
    match K with
    | PHole => l
    | PFst K _ => pctx_loc K n (cloc_take l (pctx_size K n))
    | PSnd lt1 K => pctx_loc K n (cloc_skip l (lty_size lt1))
    end.

  (** The pattern of the place, with pattern [p] at the hole. *)
  Fixpoint pctx_pat {𝔅 𝔄} (K: pctx 𝔅 𝔄) (p: lpat) : lpat :=
    match K with
    | PHole => p
    | PFst K lt2 => PatProd (pctx_pat K p) (lty_pat lt2)
    | PSnd lt1 K => PatProd (lty_pat lt1) (pctx_pat K p)
    end.

  (** The refinement of the place (at path [q], with current value [x] and blocking
      map [ζm]), with refinement [r] at the hole. *)
  Fixpoint pctx_rfn {𝔅 𝔄} (K: pctx 𝔅 𝔄) : ~~𝔄 → blk_map → lpath → prfn 𝔅 → prfn 𝔄 :=
    match K in pctx 𝔅 𝔄 return ~~𝔄 → blk_map → lpath → prfn 𝔅 → prfn 𝔄 with
    | PHole => λ _ _ _ r, r
    | PFst K lt2 => λ x ζm q r,
        inr (pctx_rfn K x.1 ζm (false :: q) r, lty_rfn lt2 x.2 ζm (true :: q))
    | PSnd lt1 K => λ x ζm q r,
        inr (lty_rfn lt1 x.1 ζm (false :: q), pctx_rfn K x.2 ζm (true :: q) r)
    end.

  (** The number of blocked leaves outside the hole. *)
  Fixpoint pctx_nblk {𝔅 𝔄} (K: pctx 𝔅 𝔄) : nat :=
    match K with
    | PHole => 0
    | PFst K lt2 => pctx_nblk K + lty_nblk lt2
    | PSnd lt1 K => lty_nblk lt1 + pctx_nblk K
    end.

  (** The core of the context. *)
  Fixpoint pctx_core {𝔅 𝔄} (K: pctx 𝔅 𝔄) : pctx 𝔅 𝔄 :=
    match K with
    | PHole => PHole
    | PFst K lt2 => PFst (pctx_core K) (lty_core lt2)
    | PSnd lt1 K => PSnd (lty_core lt1) (pctx_core K)
    end.

  (** ** Basic laws *)

  Lemma pctx_get_set {𝔅 𝔄} (K: pctx 𝔅 𝔄) x y : pctx_get K (pctx_set K x y) = y.
  Proof. induction K in x, y |- *; simpl; auto. Qed.

  Lemma pctx_set_get {𝔅 𝔄} (K: pctx 𝔅 𝔄) x : pctx_set K x (pctx_get K x) = x.
  Proof. induction K in x |- *; simpl; [done|by rewrite IHK -surjective_pairing..]. Qed.

  Lemma pctx_path_app {𝔅 𝔄} (K: pctx 𝔅 𝔄) q : pctx_path K q = pctx_path K [] ++ q.
  Proof.
    induction K in q |- *; simpl; [done| |].
    - rewrite IHK (IHK [false]) -app_assoc. done.
    - rewrite IHK (IHK [true]) -app_assoc. done.
  Qed.

  Lemma lty_size_plug {𝔅 𝔄} (K: pctx 𝔅 𝔄) lt : lty_size (pctx_plug K lt) = pctx_size K (lty_size lt).
  Proof. induction K in lt |- *; simpl; by rewrite ?IHK. Qed.

  Lemma lty_pat_plug {𝔅 𝔄} (K: pctx 𝔅 𝔄) lt : lty_pat (pctx_plug K lt) = pctx_pat K (lty_pat lt).
  Proof. induction K in lt |- *; simpl; by rewrite ?IHK. Qed.

  Lemma lty_nblk_plug {𝔅 𝔄} (K: pctx 𝔅 𝔄) lt : lty_nblk (pctx_plug K lt) = pctx_nblk K + lty_nblk lt.
  Proof. induction K in lt |- *; simpl; rewrite ?IHK; lia. Qed.

  Lemma lty_core_plug {𝔅 𝔄} (K: pctx 𝔅 𝔄) lt :
    lty_core (pctx_plug K lt) = pctx_plug (pctx_core K) (lty_core lt).
  Proof. induction K in lt |- *; simpl; by rewrite ?IHK. Qed.

  Lemma lty_fold_plug_core {𝔅 𝔄} (K: pctx 𝔅 𝔄) lt :
    lty_fold (pctx_plug K lt) = lty_fold (pctx_plug (pctx_core K) (lty_core lt)).
  Proof. by rewrite -lty_core_plug lty_fold_core. Qed.

  Lemma lty_rfn_plug {𝔅 𝔄} (K: pctx 𝔅 𝔄) lt x ζm q :
    lty_rfn (pctx_plug K lt) x ζm q =
      pctx_rfn K x ζm q (lty_rfn lt (pctx_get K x) ζm (pctx_path K q)).
  Proof. induction K in lt, x, q |- *; simpl; by rewrite ?IHK. Qed.

  Lemma pctx_rfn_set {𝔅 𝔄} (K: pctx 𝔅 𝔄) x y ζm q r :
    pctx_rfn K (pctx_set K x y) ζm q r = pctx_rfn K x ζm q r.
  Proof. induction K in x, y, q, r |- *; simpl; by rewrite ?IHK. Qed.

  (** Adding an entry for the path of the hole does not change the refinements of
      the rest. *)
  Lemma pctx_rfn_blk_cons {𝔅 𝔄} (K: pctx 𝔅 𝔄) x ζm ζi q r :
    pctx_rfn K x ((pctx_path K q, ζi) :: ζm) q r = pctx_rfn K x ζm q r.
  Proof.
    induction K in x, q, r |- *; simpl; [done| |].
    - rewrite IHK. f_equal. f_equal. apply lty_rfn_blk_irrel=> r' /=.
      rewrite decide_False; [done|]. rewrite pctx_path_app. by apply lpath_app_cons_ne.
    - rewrite IHK. f_equal. f_equal. apply lty_rfn_blk_irrel=> r' /=.
      rewrite decide_False; [done|]. rewrite pctx_path_app. by apply lpath_app_cons_ne.
  Qed.

  Lemma pctx_rfn_rsv {𝔅 𝔄} (K: pctx 𝔅 𝔄) x ζm q (r r': prfn 𝔅) ζl ζl' :
    (∀ ζ, ζ ∈ ζl → ζ ∈ ζl') →
    prfn_rsv (pctx_rfn K x ζm q r) ζl → prfn_rsv r' ζl' → prfn_rsv (pctx_rfn K x ζm q r') ζl'.
  Proof.
    intros Hin. induction K in x, q, r, r' |- *; simpl; [done| |].
    - intros [H1 H2] H'. split; [by eapply IHK|]. by eapply prfn_rsv_weaken.
    - intros [H1 H2] H'. split; [by eapply prfn_rsv_weaken|]. by eapply IHK.
  Qed.

  Lemma pctx_rfn_rsv_hole {𝔅 𝔄} (K: pctx 𝔅 𝔄) x ζm q (r: prfn 𝔅) ζl :
    prfn_rsv (pctx_rfn K x ζm q r) ζl → prfn_rsv r ζl.
  Proof. induction K in x, q, r |- *; simpl; [done|intros [? _]|intros [_ ?]]; by eapply IHK. Qed.

  Lemma pctx_loc_fst {𝔅 𝔄} (K: pctx 𝔅 𝔄) n l : (pctx_loc K n l).1 = l.1 +ₗ pctx_off K.
  Proof.
    induction K in l |- *; simpl; [by rewrite shift_loc_0|by rewrite IHK|].
    rewrite IHK /= shift_loc_assoc. f_equal. lia.
  Qed.

  (** ** Ownership in [Owned] mode *)

  (** The ownership of the rest of the place (at path [q], with current value [x] and
      blocking map [ζm]), for a hole of size [n]. *)
  Fixpoint pctx_own {𝔅 𝔄} (K: pctx 𝔅 𝔄) (n m: nat) :
      ~~𝔄 → blk_map → lpath → nat → nat → thread_id → cloc → iProp Σ :=
    match K in pctx 𝔅 𝔄 return ~~𝔄 → blk_map → lpath → nat → nat → thread_id → cloc → iProp Σ with
    | PHole => λ _ _ _ _ _ _ _, True
    | PFst K lt2 => λ x ζm q d g tid l,
        pctx_own K n m x.1 ζm (false :: q) d g tid (cloc_take l (pctx_size K n)) ∗
        ltype_own (Owned m) lt2 (lty_rfn lt2 x.2 ζm (true :: q)) d g tid
          (cloc_skip l (pctx_size K n))
    | PSnd lt1 K => λ x ζm q d g tid l,
        ltype_own (Owned m) lt1 (lty_rfn lt1 x.1 ζm (false :: q)) d g tid
          (cloc_take l (lty_size lt1)) ∗
        pctx_own K n m x.2 ζm (true :: q) d g tid (cloc_skip l (lty_size lt1))
    end%I.

  Lemma ltype_own_plug {𝔅 𝔄} (K: pctx 𝔅 𝔄) (lt: lty 𝔅) m p r x ζm q d g tid l :
    ltype_own_cp false (pctx_plug K lt) (Owned m) (pctx_pat K p) (pctx_rfn K x ζm q r)
      d g tid l ⊣⊢
    ltype_own_cp false lt (Owned m) p r d g tid (pctx_loc K (lty_size lt) l) ∗
    pctx_own K (lty_size lt) m x ζm q d g tid l.
  Proof.
    induction K in lt, r, x, q, l |- *; simpl.
    - by rewrite right_id.
    - rewrite lty_size_plug IHK. rewrite /ltype_own. by rewrite assoc.
    - rewrite IHK. rewrite /ltype_own. rewrite assoc (comm _ (ltype_own_cp _ _ _ _ _ _ _ _ _)).
      by rewrite -assoc.
  Qed.

  Lemma pctx_own_set {𝔅 𝔄} (K: pctx 𝔅 𝔄) n m x y ζm q d g tid l :
    pctx_own K n m (pctx_set K x y) ζm q d g tid l = pctx_own K n m x ζm q d g tid l.
  Proof. induction K in x, y, q, l |- *; simpl; by rewrite ?IHK. Qed.

  Lemma pctx_own_blk_cons {𝔅 𝔄} (K: pctx 𝔅 𝔄) n m x ζm ζi q d g tid l :
    pctx_own K n m x ((pctx_path K q, ζi) :: ζm) q d g tid l = pctx_own K n m x ζm q d g tid l.
  Proof.
    induction K in x, q, l |- *; simpl; [done| |].
    - rewrite IHK. f_equal. f_equal. apply lty_rfn_blk_irrel=> r' /=.
      rewrite decide_False; [done|]. rewrite pctx_path_app. by apply lpath_app_cons_ne.
    - rewrite IHK. f_equal. f_equal. apply lty_rfn_blk_irrel=> r' /=.
      rewrite decide_False; [done|]. rewrite pctx_path_app. by apply lpath_app_cons_ne.
  Qed.

  Lemma pctx_own_depth_mono {𝔅 𝔄} (K: pctx 𝔅 𝔄) n m x ζm q d g d' g' tid l :
    d ≤ d' → g ≤ g' →
    pctx_own K n m x ζm q d g tid l ⊢ pctx_own K n m x ζm q d' g' tid l.
  Proof.
    intros ??. induction K in x, q, l |- *; simpl; [done| |].
    - iIntros "[A B]". iSplitL "A"; [by iApply IHK|].
      by iApply (ltype_own_owned_depth_mono with "B").
    - iIntros "[A B]". iSplitL "A"; [by iApply (ltype_own_owned_depth_mono with "A")|].
      by iApply IHK.
  Qed.

  (** The location of the hole is part of the location of the place. *)
  Lemma pctx_loc_guard {𝔅 𝔄} (K: pctx 𝔅 𝔄) n l (G: iProp Σ) E k :
    (G &&{E; k}&&> l #↦∗_) -∗ (G &&{E; k}&&> pctx_loc K n l #↦∗_).
  Proof.
    induction K in l |- *; simpl; [by iIntros "$"|..]; iIntros "G"; iApply IHK.
    - rewrite (heap_cloc_mapsto_emp_vec_app l (pctx_size K n)).
      iApply (guards_weaken_rhs_sep_l with "G").
    - rewrite (heap_cloc_mapsto_emp_vec_app l (lty_size lt1)).
      iApply (guards_weaken_rhs_sep_r with "G").
  Qed.

  (** ** Patterns *)

  Lemma pat_blk_lfts_plug {𝔅 𝔄} (K: pctx 𝔅 𝔄) p p' α :
    α ∈ pat_blk_lfts (pctx_pat K p') → α ∈ pat_blk_lfts p' ∨ α ∈ pat_blk_lfts (pctx_pat K p).
  Proof.
    induction K; simpl; [by left|..]; rewrite !elem_of_app.
    - intros [Hα|Hα]; [destruct (IHK Hα); [by left|by right; left]|by right; right].
    - intros [Hα|Hα]; [by right; left|destruct (IHK Hα); [by left|by right; right]].
  Qed.

  Lemma pat_ok_plug κ {𝔅 𝔄} (K: pctx 𝔅 𝔄) p p' :
    pat_ok κ (pctx_pat K p) -∗ pat_ok κ p' -∗ pat_ok κ (pctx_pat K p').
  Proof.
    iIntros "#Ok #Ok'". rewrite /pat_ok. iApply big_sepL_intro. iIntros "!>" (i α Hi).
    apply elem_of_list_lookup_2, (pat_blk_lfts_plug K p) in Hi as [Hi|Hi].
    - by iApply (big_sepL_elem_of with "Ok'").
    - by iApply (big_sepL_elem_of with "Ok").
  Qed.

  Lemma pat_ok_plug_hole κ {𝔅 𝔄} (K: pctx 𝔅 𝔄) p :
    pat_ok κ (pctx_pat K p) -∗ pat_ok κ p.
  Proof.
    rewrite /pat_ok. induction K; simpl; [by iIntros "$"|..]; rewrite big_sepL_app.
    - iIntros "[A _]". by iApply IHK.
    - iIntros "[_ A]". by iApply IHK.
  Qed.

  Lemma pat_ok_incl κ p p' :
    (∀ α, α ∈ pat_blk_lfts p' → α ∈ pat_blk_lfts p) → pat_ok κ p -∗ pat_ok κ p'.
  Proof.
    iIntros (Hin) "#Ok". rewrite /pat_ok. iApply big_sepL_intro. iIntros "!>" (i α Hi).
    apply elem_of_list_lookup_2, Hin in Hi. by iApply (big_sepL_elem_of with "Ok").
  Qed.

  (** ** Folded types *)

  Lemma lty_fold_plug_eq' {𝔅 𝔄} (K: pctx 𝔅 𝔄) lt lt' :
    lty_fold lt = lty_fold lt' → lty_fold (pctx_plug K lt) = lty_fold (pctx_plug K lt').
  Proof. intros Heq. induction K in lt, lt', Heq |- *; simpl; by rewrite ?(IHK lt lt'). Qed.

  Lemma lty_lft_plug {𝔅 𝔄} (K: pctx 𝔅 𝔄) lt :
    ⊢ ty_lft (lty_fold (pctx_plug K lt)) ⊑ ty_lft (lty_fold lt).
  Proof.
    induction K in lt |- *; simpl; [iApply guards_refl|..];
      (iApply llftl_incl_trans; [|iApply IHK]); rewrite lft_intersect_list_app;
      [iApply llftl_intersect_incl_l|iApply llftl_intersect_incl_r].
  Qed.

  Lemma pctx_rfn_den {𝔅 𝔄} (K: pctx 𝔅 𝔄) x ζm q (r r': prfn 𝔅) π :
    prfn_den r π = prfn_den r' π →
    prfn_den (pctx_rfn K x ζm q r) π = prfn_den (pctx_rfn K x ζm q r') π.
  Proof. intros Heq. induction K in x, q, r, r', Heq |- *; simpl; by rewrite ?(IHK _ _ r r'). Qed.

  (** ** Simple places and compound places *)

  Fixpoint pctx_simple {𝔅 𝔄} (K: pctx 𝔅 𝔄) : Prop :=
    match K with
    | PHole => True
    | PFst K lt2 => pctx_simple K ∧ lty_simple lt2
    | PSnd lt1 K => lty_simple lt1 ∧ pctx_simple K
    end.

  Lemma lty_simple_plug {𝔅 𝔄} (K: pctx 𝔅 𝔄) lt :
    pctx_simple K → lty_simple lt → lty_simple (pctx_plug K lt).
  Proof. induction K in lt |- *; simpl; naive_solver. Qed.

  (** In [Uniq] mode, a plugged place (with a nonempty context) is a compound place,
      whose node is the [Owned 0] interpretation. *)
  Lemma ltype_own_cp_uniq_plug {𝔅 𝔄} (K: pctx 𝔅 𝔄) lt κ ξi p :
    pctx_nonempty K →
    ltype_own_cp false (pctx_plug K lt) (Uniq κ ξi) p =
      cpd_own κ ξi (lty_fold (pctx_plug K lt)) p (ltype_own_cp false (pctx_plug K lt) (Owned 0)).
  Proof. by destruct K. Qed.

  (** Only the core matters. *)
  Lemma ltype_own_cp_plug_core c {𝔅 𝔄} (K: pctx 𝔅 𝔄) lt lt' :
    lty_core lt = lty_core lt' →
    ltype_own_cp c (pctx_plug K lt) = ltype_own_cp c (pctx_plug K lt').
  Proof.
    intros Hc. by rewrite -(ltype_own_cp_core c (pctx_plug K lt))
      -(ltype_own_cp_core c (pctx_plug K lt')) !lty_core_plug Hc.
  Qed.

  Lemma lty_fold_plug_eq {𝔅 𝔄} (K: pctx 𝔅 𝔄) lt lt' :
    lty_core lt = lty_core lt' → lty_fold (pctx_plug K lt) = lty_fold (pctx_plug K lt').
  Proof. intros Hc. by rewrite lty_fold_plug_core (lty_fold_plug_core K lt') Hc. Qed.

  Lemma lty_size_plug_eq {𝔅 𝔄} (K: pctx 𝔅 𝔄) lt lt' :
    lty_size lt = lty_size lt' → lty_size (pctx_plug K lt) = lty_size (pctx_plug K lt').
  Proof. intros Hc. by rewrite !lty_size_plug Hc. Qed.
End pctx.
