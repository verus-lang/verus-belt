(** * Paths and place contexts

  Access to a subplace of a (nested) place type, in the style of the place
  contexts of RefinedRust (paper §5.3; [typed_place] in [rust_typing/programs.v]
  of the RefinedRust development). The subplaces are fields of (nested) products,
  pointees of owned pointers and payloads of sums.

  - A _place context_ [K : pctx 𝔅 𝔄] is a place type of [𝔄] with a hole of
    type [𝔅]. It is given from the root: [PFst K lt2] is a pair whose field 0 is
    the context [K] and whose field 1 has the place type [lt2] ([PSnd] dually);
    [POwn n K] is an owned pointer whose pointee is the context [K]; [PSum tyl i w K] is
    a sum of variant [i] whose payload is the context [K] (at offset 1, after the tag;
    [w] is a default payload value, only used by [pctx_get] for values of other
    variants, which are not owned: see [pctx_in]); [PUniq κ K] is a unique borrow at [κ]
    whose referent is the context [K] (a nested place, [UniqLty]); [PShr κ K] is a shared
    reference at [κ] whose referent is the context [K] (a read-only view, [ShrLty]: the
    plugged place is a leaf, nothing below it is owned, see [place_pshr.v]).
    [pctx_plug K lt] plugs a place type into the hole.
  - The hole has a value ([pctx_get], [pctx_set] on values of the root), a
    _path_ from the root ([pctx_path], a list of field selectors, innermost
    first), an offset from the root ([pctx_off], below no owned pointer) and a
    location ([pctx_loc]), which depends on the size of the hole and (below an owned
    pointer) on the value of the root.
  - The refinement of a place is computed from the current value of the root and
    a _blocking map_ [ζm] from the paths of blocked leaves to the prophecy ids of
    their reborrows ([lty_rfn]); a blocked leaf is refined by the final value of
    its reborrow ([PlaceGhost]). The blocking map is stored in the value of a place
    element ([typing/place.v]). The refinement of a plugged place is the plugged
    refinement ([lty_rfn_plug], [pctx_rfn]); adding an entry for the path of the
    hole does not change the refinements of the rest ([pctx_rfn_blk_cons]).
  - In [Owned] mode, the ownership of a plugged place splits into the ownership
    of the hole and of the rest ([ltype_own_plug]); the rest does not depend on
    the hole. Below [k] owned pointers, the hole is owned with [k] more laters
    ([pctx_mode]) at a depth decreased by [k] ([pctx_depth]). This needs the hole to be
    below no unique borrow and no shared reference ([PctxNoUniq]): below [PUniq] the hole
    is inside the borrow, which has to be opened ([pctx_acc] in [pctx_acc.v]); below
    [PShr] it is not owned ([PctxNoShr], needed by [pctx_acc] and [pctx_rfn_set]). *)

From iris.proofmode Require Import proofmode.
From lrust.lang Require Import proofmode.
From lrust.typing Require Export type ltype.
From lrust.typing Require Import uniq_util uniq_bor freeable_util sum type_sum.
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

  (** A refinement with a constant denotation. *)
  Definition prfn_dummy {𝔄} (x: ~~𝔄) : prfn 𝔄 := inl (PlaceProph x (λ _, vπ x inhabitant)).

  Lemma prfn_dummy_rsv {𝔄} (x: ~~𝔄) ζl : prfn_rsv (prfn_dummy x) ζl.
  Proof. rewrite prfn_rsv_inl. by intros ???. Qed.

  Lemma prfn_dummy_dep {𝔄} (x: ~~𝔄) ζl : prfn_den (prfn_dummy x) ./ ζl.
  Proof. rewrite prfn_den_inl. by intros ???. Qed.

  (** The refinement of a place [lt] at path [q], with current value [x] and blocking
      map [ζm]. *)
  Fixpoint lty_rfn {𝔄} (lt: lty 𝔄) : ~~𝔄 → blk_map → lpath → prfn 𝔄 :=
    match lt in lty 𝔄 return ~~𝔄 → blk_map → lpath → prfn 𝔄 with
    | OfTy _ => λ x _ _, inl (PlaceIn x)
    | Blocked _ _ => λ x ζm q, inl (PlaceGhost x (blk_lookup ζm q))
    (* A nested unique borrow: the referent location, the refinement of the
       referent (below the path [false :: q]) and the prophecy variable id. *)
    | UniqLty lt _ => λ x ζm q,
        inr (uniq_bor_loc x, lty_rfn lt (uniq_bor_current x) ζm (false :: q), uniq_bor_ξi x)
    | OwnPtrLty _ lt => λ x ζm q, inr (x.1, lty_rfn lt x.2 ζm (false :: q))
    | ProdLty lt1 lt2 => λ x ζm q,
        inr (lty_rfn lt1 x.1 ζm (false :: q), lty_rfn lt2 x.2 ζm (true :: q))
    (* A shared-blocked leaf keeps its value. *)
    | ShrBlocked _ _ => λ x _ _, inl (PlaceIn x)
    (* A sum at variant [i]: the refinement of the payload (below the path
       [false :: q]) and the padding. (If the value is of another variant, the place is
       not owned, see [sum_node]; the refinement is a constant.) *)
    | SumLty _ i lt => λ x ζm q,
        match psum_proj i x.1 with
        | Some y => prfn_sum i (lty_rfn lt y ζm (false :: q)) x.2
        | None => prfn_dummy x
        end
    (* A shared reference (whose referent does not change) keeps its value. *)
    | ShrLty _ _ => λ x _ _, inl (PlaceIn x)
    end.

  Lemma lty_rfn_sum {𝔄l} (tyl: typel 𝔄l) i (lt: lty (𝔄l !!ₗ i)) x ζm q :
    lty_rfn (SumLty tyl i lt) x ζm q =
      match psum_proj i x.1 with
      | Some y => prfn_sum i (lty_rfn lt y ζm (false :: q)) x.2
      | None => prfn_dummy x
      end.
  Proof. done. Qed.

  (** The refinement only depends on the entries of the blocking map below [q]. *)
  Lemma lty_rfn_blk_irrel {𝔄} (lt: lty 𝔄) x ζm ζm' q :
    (∀ r, blk_lookup ζm (r ++ q) = blk_lookup ζm' (r ++ q)) →
    lty_rfn lt x ζm q = lty_rfn lt x ζm' q.
  Proof.
    induction lt as [| |𝔄 lt IH κ|𝔄 n lt IH|𝔄 𝔅 lt1 IH1 lt2 IH2| |𝔄l tyl i lt IH|] in x, q |- *;
      intros Heq; simpl; [done| | | | |done| |done].
    5: { destruct (psum_proj i x.1); [|done].
      rewrite (IH _ (false :: q)); [done|].
      intros r. rewrite (_: r ++ false :: q = (r ++ [false]) ++ q); [apply Heq|].
      by rewrite -app_assoc. }
    - by rewrite (Heq []).
    - rewrite (IH _ (false :: q)); [done|].
      intros r. rewrite (_: r ++ false :: q = (r ++ [false]) ++ q); [apply Heq|].
      by rewrite -app_assoc.
    - rewrite (IH _ (false :: q)); [done|].
      intros r. rewrite (_: r ++ false :: q = (r ++ [false]) ++ q); [apply Heq|].
      by rewrite -app_assoc.
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
    | UniqLty lt _ | OwnPtrLty _ lt | SumLty _ _ lt | ShrLty lt _ => lty_nblk lt
    | ProdLty lt1 lt2 => lty_nblk lt1 + lty_nblk lt2
    | _ => 0
    end.

  (** The number of cumulative time receipts held by an owned place for its blocked
      leaves ([place_own.v]): one per blocked leaf, plus, for a leaf below unique borrows,
      one per level (owned pointer or unique borrow) above it that is not an owned pointer
      after the last unique borrow. Unblocking such a leaf opens the enclosing borrows
      (later credits) and raises the depths of all levels above it, while the receipt of
      its inheritance is only shifted by the owned pointers after the last unique borrow
      (see [blocked_owned]). A shared-blocked leaf below a unique borrow holds one receipt,
      for the credits to open the enclosing borrows when it is unblocked (its depths do not
      change). [e] is the number of such levels so far, [mm] the number of owned pointers
      since the last unique borrow. (Nothing is blocked below a shared reference; the
      count passes through [ShrLty] only so that the laws of [pctx_plug] hold.) *)
  Fixpoint lty_nrc {𝔄} (lt: lty 𝔄) (e mm: nat) : nat :=
    match lt with
    | Blocked _ _ => S e
    | ShrBlocked _ _ => match e with O => 0 | S _ => 1 end
    | UniqLty lt _ => lty_nrc lt (e + mm + 1) 0
    | OwnPtrLty _ lt => lty_nrc lt e (S mm)
    | SumLty _ _ lt => lty_nrc lt e mm
    | ShrLty lt _ => lty_nrc lt e (S mm)
    | ProdLty lt1 lt2 => lty_nrc lt1 e mm + lty_nrc lt2 e mm
    | _ => 0
    end.

  (** All leaves are blocked. *)
  Fixpoint lty_blk_all {𝔄} (lt: lty 𝔄) : Prop :=
    match lt with
    | Blocked _ _ => True
    | UniqLty lt _ | OwnPtrLty _ lt | SumLty _ _ lt => lty_blk_all lt
    | ProdLty lt1 lt2 => lty_blk_all lt1 ∧ lty_blk_all lt2
    | _ => False
    end.

  (** If all leaves are blocked, the denotation of the refinement depends only on
      the variables of any reservation for it. *)
  (** The dependency of the final value of a unique borrow does not depend on the
      witness of its prophecy variable. *)
  Lemma uniq_prvar_dep_irrel {𝔄} (x x': ~~𝔄) ξi ζl :
    (λ π, (π (uniq_prvar x ξi)).1) ./ ζl → (λ π, (π (uniq_prvar x' ξi)).1) ./ ζl.
  Proof.
    intros Hd π π' Hπ. rewrite (uniq_prvar_app_irrel x' x ξi π) (uniq_prvar_app_irrel x' x ξi π').
    by apply Hd.
  Qed.

  Lemma lty_blk_all_dep {𝔄} (lt: lty 𝔄) x ζm q ζl :
    lty_blk_all lt → prfn_rsv (lty_rfn lt x ζm q) ζl → prfn_den (lty_rfn lt x ζm q) ./ ζl.
  Proof.
    induction lt as [| |𝔄 lt IH κ|𝔄 n lt IH|𝔄 𝔅 lt1 IH1 lt2 IH2| |𝔄l tyl i lt IH|] in x, q |- *;
      intros Hb Hr; try done.
    5: { revert Hr. rewrite lty_rfn_sum. destruct (psum_proj i x.1) as [y|];
        [|intros; apply prfn_dummy_dep].
      rewrite prfn_rsv_sum prfn_den_sum. intros Hr.
      apply (proph_dep_constr (λ a, (pinj i a, x.2))). by apply IH. }
    - simpl in *. rewrite prfn_den_inl. by rewrite prfn_rsv_inl in Hr.
    - destruct Hr as [Hr Hξ]. apply (proph_dep_weaken _ (ζl ++ ζl)); [set_solver|].
      apply (proph_dep_constr2 pair); [by apply IH|exact Hξ].
    - apply (proph_dep_constr (pair x.1)). by apply IH.
    - destruct Hb as [Hb1 Hb2]. destruct Hr as [Hr1 Hr2].
      apply (proph_dep_weaken _ (ζl ++ ζl)); [set_solver|].
      apply (proph_dep_constr2 pair); [by apply IH1|by apply IH2].
  Qed.
End lty_rfn.

(** * Values of unique borrows *)

Section uniq_bor_val.
  Context `{!typeG Σ}.

  Definition uniq_bor_set_current {𝔄} (m: ~~ (uniq_borₛ 𝔄)) (y: ~~𝔄) : ~~ (uniq_borₛ 𝔄) :=
    match m with (l, _, ξi, d, g, idx) => (l, y, ξi, d, g, idx) end.

  (** The depths and the index of the value of a unique borrow (which are not part of the
      refinement of a nested place, see [lty_rfn]). *)
  Definition uniq_bor_set_meta {𝔄} (m: ~~ (uniq_borₛ 𝔄)) (d g: nat) (idx: Idx) :
      ~~ (uniq_borₛ 𝔄) :=
    match m with (l, y, ξi, _, _, _) => (l, y, ξi, d, g, idx) end.

  (** The same, with a current value of another type. *)
  Definition uniq_bor_retype {𝔄 𝔅} (m: ~~ (uniq_borₛ 𝔄)) (y: ~~𝔅) : ~~ (uniq_borₛ 𝔅) :=
    match m with (l, _, ξi, d, g, idx) => (l, y, ξi, d, g, idx) end.

  Lemma uniq_bor_current_set {𝔄} (m: ~~ (uniq_borₛ 𝔄)) y :
    uniq_bor_current (uniq_bor_set_current m y) = y.
  Proof. by destruct m as [[[[[??]?]?]?]?]. Qed.
  Lemma uniq_bor_loc_set {𝔄} (m: ~~ (uniq_borₛ 𝔄)) y :
    uniq_bor_loc (uniq_bor_set_current m y) = uniq_bor_loc m.
  Proof. by destruct m as [[[[[??]?]?]?]?]. Qed.
  Lemma uniq_bor_ξi_set {𝔄} (m: ~~ (uniq_borₛ 𝔄)) y :
    uniq_bor_ξi (uniq_bor_set_current m y) = uniq_bor_ξi m.
  Proof. by destruct m as [[[[[??]?]?]?]?]. Qed.
  Lemma uniq_bor_set_current_id {𝔄} (m: ~~ (uniq_borₛ 𝔄)) :
    uniq_bor_set_current m (uniq_bor_current m) = m.
  Proof. by destruct m as [[[[[??]?]?]?]?]. Qed.
  Lemma uniq_bor_current_retype {𝔄 𝔅} (m: ~~ (uniq_borₛ 𝔄)) (y: ~~𝔅) :
    uniq_bor_current (uniq_bor_retype m y) = y.
  Proof. by destruct m as [[[[[??]?]?]?]?]. Qed.
  Lemma uniq_bor_loc_retype {𝔄 𝔅} (m: ~~ (uniq_borₛ 𝔄)) (y: ~~𝔅) :
    uniq_bor_loc (uniq_bor_retype m y) = uniq_bor_loc m.
  Proof. by destruct m as [[[[[??]?]?]?]?]. Qed.
End uniq_bor_val.

(** * Place contexts *)

Section pctx.
  Context `{!typeG Σ}.

  Inductive pctx : syn_type → syn_type → Type :=
  | PHole {𝔅} : pctx 𝔅 𝔅
  | PFst {𝔅 𝔄1 𝔄2} (K: pctx 𝔅 𝔄1) (lt2: lty 𝔄2) : pctx 𝔅 (𝔄1 * 𝔄2)
  | PSnd {𝔅 𝔄1 𝔄2} (lt1: lty 𝔄1) (K: pctx 𝔅 𝔄2) : pctx 𝔅 (𝔄1 * 𝔄2)
  | POwn {𝔅 𝔄'} (n: nat) (K: pctx 𝔅 𝔄') : pctx 𝔅 (at_locₛ 𝔄')
  (* The payload of a sum at variant [i]; [w] is a default value of the payload,
     used (by [pctx_get]) only for values of other variants. *)
  | PSum {𝔅 𝔄l} (tyl: typel 𝔄l) (i: fin (length 𝔄l)) (w: ~~ (𝔄l !!ₗ i))
      (K: pctx 𝔅 (𝔄l !!ₗ i)) : pctx 𝔅 (Σ! 𝔄l)
  (* The referent of a unique borrow at [κ] (a nested place, see [UniqLty]). *)
  | PUniq {𝔅 𝔄'} (κ: lft) (K: pctx 𝔅 𝔄') : pctx 𝔅 (uniq_borₛ 𝔄')
  (* The referent of a shared reference at [κ] (a read-only view, see [ShrLty]). *)
  | PShr {𝔅 𝔄'} (κ: lft) (K: pctx 𝔅 𝔄') : pctx 𝔅 (at_clocₛ 𝔄').

  (** The plugged place is compound (the referent of a shared reference is a view, the
      plugged place is a leaf). *)
  Definition pctx_nonempty {𝔅 𝔄} (K: pctx 𝔅 𝔄) : Prop :=
    match K with PHole | PShr _ _ => False | _ => True end.

  Fixpoint pctx_plug {𝔅 𝔄} (K: pctx 𝔅 𝔄) : lty 𝔅 → lty 𝔄 :=
    match K in pctx 𝔅 𝔄 return lty 𝔅 → lty 𝔄 with
    | PHole => λ lt, lt
    | PFst K lt2 => λ lt, ProdLty (pctx_plug K lt) lt2
    | PSnd lt1 K => λ lt, ProdLty lt1 (pctx_plug K lt)
    | POwn n K => λ lt, OwnPtrLty n (pctx_plug K lt)
    | PSum tyl i _ K => λ lt, SumLty tyl i (pctx_plug K lt)
    | PUniq κ K => λ lt, UniqLty (pctx_plug K lt) κ
    | PShr κ K => λ lt, ShrLty (pctx_plug K lt) κ
    end.

  Fixpoint pctx_get {𝔅 𝔄} (K: pctx 𝔅 𝔄) : ~~𝔄 → ~~𝔅 :=
    match K in pctx 𝔅 𝔄 return ~~𝔄 → ~~𝔅 with
    | PHole => λ x, x
    | PFst K _ => λ x, pctx_get K x.1
    | PSnd _ K => λ x, pctx_get K x.2
    | POwn _ K => λ x, pctx_get K x.2
    | PSum _ i w K => λ x, pctx_get K (psum_proj_or i x.1 w)
    | PUniq _ K => λ x, pctx_get K (uniq_bor_current x)
    | PShr _ K => λ x, pctx_get K x.2
    end.

  Fixpoint pctx_set {𝔅 𝔄} (K: pctx 𝔅 𝔄) : ~~𝔄 → ~~𝔅 → ~~𝔄 :=
    match K in pctx 𝔅 𝔄 return ~~𝔄 → ~~𝔅 → ~~𝔄 with
    | PHole => λ _ y, y
    | PFst K _ => λ x y, (pctx_set K x.1 y, x.2)
    | PSnd _ K => λ x y, (x.1, pctx_set K x.2 y)
    | POwn _ K => λ x y, (x.1, pctx_set K x.2 y)
    | PSum _ i w K => λ x y, (pinj i (pctx_set K (psum_proj_or i x.1 w) y), x.2)
    | PUniq _ K => λ x y, uniq_bor_set_current x (pctx_set K (uniq_bor_current x) y)
    | PShr _ K => λ x y, (x.1, pctx_set K x.2 y)
    end.

  (** The path of the hole, from a place at path [q]. *)
  Fixpoint pctx_path {𝔅 𝔄} (K: pctx 𝔅 𝔄) (q: lpath) : lpath :=
    match K with
    | PHole => q
    | PFst K _ => pctx_path K (false :: q)
    | PSnd _ K => pctx_path K (true :: q)
    | POwn _ K => pctx_path K (false :: q)
    | PSum _ _ _ K => pctx_path K (false :: q)
    | PUniq _ K | PShr _ K => pctx_path K (false :: q)
    end.

  (** The size of the place, for a hole of size [n]. *)
  Fixpoint pctx_size {𝔅 𝔄} (K: pctx 𝔅 𝔄) (n: nat) : nat :=
    match K with
    | PHole => n
    | PFst K lt2 => pctx_size K n + lty_size lt2
    | PSnd lt1 K => lty_size lt1 + pctx_size K n
    | POwn _ _ => 1
    | PSum tyl i _ K => S (max_hlist_set (λ _, ty_size) tyl i (pctx_size K n))
    | PUniq _ _ | PShr _ _ => 1
    end.

  (** The hole is not below an owned pointer. *)
  Fixpoint pctx_noderef {𝔅 𝔄} (K: pctx 𝔅 𝔄) : Prop :=
    match K with
    | PHole => True
    | PFst K _ | PSnd _ K | PSum _ _ _ K => pctx_noderef K
    | POwn _ _ | PUniq _ _ | PShr _ _ => False
    end.

  (** The hole is not in the payload of a sum. *)
  Fixpoint pctx_nosum {𝔅 𝔄} (K: pctx 𝔅 𝔄) : Prop :=
    match K with
    | PHole => True
    | PFst K _ | PSnd _ K | POwn _ K | PUniq _ K | PShr _ K => pctx_nosum K
    | PSum _ _ _ _ => False
    end.

  (** The hole is a field of (nested) products. *)
  Fixpoint pctx_fields {𝔅 𝔄} (K: pctx 𝔅 𝔄) : Prop :=
    match K with
    | PHole => True
    | PFst K _ | PSnd _ K => pctx_fields K
    | POwn _ _ | PSum _ _ _ _ | PUniq _ _ | PShr _ _ => False
    end.

  (** The hole is below no unique borrow and no shared reference (a context of the place
      of a single borrow or owned location; see [PctxNoUniq]). *)
  Fixpoint pctx_nouniq {𝔅 𝔄} (K: pctx 𝔅 𝔄) : Prop :=
    match K with
    | PHole => True
    | PFst K _ | PSnd _ K | POwn _ K | PSum _ _ _ K => pctx_nouniq K
    | PUniq _ _ | PShr _ _ => False
    end.

  (** The hole is below no shared reference (it is owned; see [PctxNoShr]). *)
  Fixpoint pctx_noshr {𝔅 𝔄} (K: pctx 𝔅 𝔄) : Prop :=
    match K with
    | PHole => True
    | PFst K _ | PSnd _ K | POwn _ K | PSum _ _ _ K | PUniq _ K => pctx_noshr K
    | PShr _ _ => False
    end.

  (** The value [x] is of the variants of the sums of [K]. *)
  Fixpoint pctx_in {𝔅 𝔄} (K: pctx 𝔅 𝔄) : ~~𝔄 → Prop :=
    match K in pctx 𝔅 𝔄 return ~~𝔄 → Prop with
    | PHole => λ _, True
    | PFst K _ => λ x, pctx_in K x.1
    | PSnd _ K | POwn _ K | PShr _ K => λ x, pctx_in K x.2
    | PSum _ i _ K => λ x, match psum_proj i x.1 with Some y => pctx_in K y | None => False end
    | PUniq _ K => λ x, pctx_in K (uniq_bor_current x)
    end.

  (** The offset of the hole (if it is not below an owned pointer). *)
  Fixpoint pctx_off {𝔅 𝔄} (K: pctx 𝔅 𝔄) : nat :=
    match K with
    | PHole => 0
    | PFst K _ => pctx_off K
    | PSnd lt1 K => lty_size lt1 + pctx_off K
    | POwn _ _ => 0
    | PSum _ _ _ K => S (pctx_off K)
    | PUniq _ _ | PShr _ _ => 0
    end.

  (** The location of the hole (of size [n]), in a place at [l] with value [x]. *)
  Fixpoint pctx_loc {𝔅 𝔄} (K: pctx 𝔅 𝔄) (n: nat) : ~~𝔄 → cloc → cloc :=
    match K in pctx 𝔅 𝔄 return ~~𝔄 → cloc → cloc with
    | PHole => λ _ l, l
    | PFst K _ => λ x l, pctx_loc K n x.1 (cloc_take l (pctx_size K n))
    | PSnd lt1 K => λ x l, pctx_loc K n x.2 (cloc_skip l (lty_size lt1))
    | POwn _ K => λ x _, pctx_loc K n x.2 (x.1, repeat [] (pctx_size K n))
    | PSum _ i w K => λ x l,
        pctx_loc K n (psum_proj_or i x.1 w) (cloc_take (cloc_skip l 1) (pctx_size K n))
    | PUniq _ K => λ x _, pctx_loc K n (uniq_bor_current x) (uniq_bor_loc x)
    | PShr _ K => λ x _, pctx_loc K n x.2 x.1
    end.

  (** The number of laters of the hole, in a place with [m] laters. (Only meaningful
      below no unique borrow, [PctxNoUniq]; see [pctx_kind] otherwise.) *)
  Fixpoint pctx_mode {𝔅 𝔄} (K: pctx 𝔅 𝔄) (m: nat) : nat :=
    match K with
    | PHole => m
    | PFst K _ | PSnd _ K | PSum _ _ _ K => pctx_mode K m
    | POwn _ K | PUniq _ K | PShr _ K => pctx_mode K (m + 1)
    end.

  (** The depth of the hole, in a place at depth [d]. *)
  Fixpoint pctx_depth {𝔅 𝔄} (K: pctx 𝔅 𝔄) (d: nat) : nat :=
    match K with
    | PHole => d
    | PFst K _ | PSnd _ K | PSum _ _ _ K => pctx_depth K d
    | POwn _ K | PUniq _ K | PShr _ K => pctx_depth K (pred d)
    end.

  (** The pattern of the place, with pattern [p] at the hole. *)
  Fixpoint pctx_pat {𝔅 𝔄} (K: pctx 𝔅 𝔄) (p: lpat) : lpat :=
    match K with
    | PHole => p
    | PFst K lt2 => PatProd (pctx_pat K p) (lty_pat lt2)
    | PSnd lt1 K => PatProd (lty_pat lt1) (pctx_pat K p)
    | POwn _ K => PatOwn (pctx_pat K p)
    | PSum _ _ _ K => PatSum (pctx_pat K p)
    | PUniq _ K => PatUniq (pctx_pat K p)
    | PShr _ _ => PatLeaf
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
    | POwn _ K => λ x ζm q r, inr (x.1, pctx_rfn K x.2 ζm (false :: q) r)
    | PSum _ i _ K => λ x ζm q r,
        match psum_proj i x.1 with
        | Some y => prfn_sum i (pctx_rfn K y ζm (false :: q) r) x.2
        | None => prfn_dummy x
        end
    | PUniq _ K => λ x ζm q r,
        inr (uniq_bor_loc x, pctx_rfn K (uniq_bor_current x) ζm (false :: q) r, uniq_bor_ξi x)
    | PShr _ _ => λ x _ _ _, inl (PlaceIn x)
    end.

  (** The number of blocked leaves outside the hole. *)
  Fixpoint pctx_nblk {𝔅 𝔄} (K: pctx 𝔅 𝔄) : nat :=
    match K with
    | PHole => 0
    | PFst K lt2 => pctx_nblk K + lty_nblk lt2
    | PSnd lt1 K => lty_nblk lt1 + pctx_nblk K
    | POwn _ K | PSum _ _ _ K | PUniq _ K | PShr _ K => pctx_nblk K
    end.

  (** The receipts of the blocked leaves outside the hole ([lty_nrc]), and the values of
      [e] and [mm] at the hole. *)
  Fixpoint pctx_nrc {𝔅 𝔄} (K: pctx 𝔅 𝔄) (e mm: nat) : nat :=
    match K with
    | PHole => 0
    | PFst K lt2 => pctx_nrc K e mm + lty_nrc lt2 e mm
    | PSnd lt1 K => lty_nrc lt1 e mm + pctx_nrc K e mm
    | POwn _ K => pctx_nrc K e (S mm)
    | PSum _ _ _ K => pctx_nrc K e mm
    | PShr _ K => pctx_nrc K e (S mm)
    | PUniq _ K => pctx_nrc K (e + mm + 1) 0
    end.

  Fixpoint pctx_ne {𝔅 𝔄} (K: pctx 𝔅 𝔄) (e mm: nat) : nat :=
    match K with
    | PHole => e
    | PFst K _ | PSnd _ K | PSum _ _ _ K => pctx_ne K e mm
    | POwn _ K | PShr _ K => pctx_ne K e (S mm)
    | PUniq _ K => pctx_ne K (e + mm + 1) 0
    end.

  Fixpoint pctx_nmm {𝔅 𝔄} (K: pctx 𝔅 𝔄) (e mm: nat) : nat :=
    match K with
    | PHole => mm
    | PFst K _ | PSnd _ K | PSum _ _ _ K => pctx_nmm K e mm
    | POwn _ K | PShr _ K => pctx_nmm K e (S mm)
    | PUniq _ K => pctx_nmm K (e + mm + 1) 0
    end.

  (** The core of the context. *)
  Fixpoint pctx_core {𝔅 𝔄} (K: pctx 𝔅 𝔄) : pctx 𝔅 𝔄 :=
    match K with
    | PHole => PHole
    | PFst K lt2 => PFst (pctx_core K) (lty_core lt2)
    | PSnd lt1 K => PSnd (lty_core lt1) (pctx_core K)
    | POwn n K => POwn n (pctx_core K)
    | PSum tyl i w K => PSum tyl i w (pctx_core K)
    | PUniq κ K => PUniq κ (pctx_core K)
    | PShr κ K => PShr κ (pctx_core K)
    end.

  (** The hole is below no shared reference (it is owned): a type class, solved by the
      structure of the context (or from [PctxNoUniq]). *)
  Class PctxNoShr {𝔅 𝔄} (K: pctx 𝔅 𝔄) : Prop := pctx_no_shr : pctx_noshr K.

  Global Instance pctx_no_shr_hole {𝔅} : PctxNoShr (PHole (𝔅:=𝔅)).
  Proof. done. Qed.
  Global Instance pctx_no_shr_fst {𝔅 𝔄1 𝔄2} (K: pctx 𝔅 𝔄1) (lt2: lty 𝔄2) :
    PctxNoShr K → PctxNoShr (PFst K lt2).
  Proof. done. Qed.
  Global Instance pctx_no_shr_snd {𝔅 𝔄1 𝔄2} (lt1: lty 𝔄1) (K: pctx 𝔅 𝔄2) :
    PctxNoShr K → PctxNoShr (PSnd lt1 K).
  Proof. done. Qed.
  Global Instance pctx_no_shr_own {𝔅 𝔄'} n (K: pctx 𝔅 𝔄') :
    PctxNoShr K → PctxNoShr (POwn n K).
  Proof. done. Qed.
  Global Instance pctx_no_shr_sum {𝔅 𝔄l} (tyl: typel 𝔄l) i w (K: pctx 𝔅 (𝔄l !!ₗ i)) :
    PctxNoShr K → PctxNoShr (PSum tyl i w K).
  Proof. done. Qed.
  Global Instance pctx_no_shr_uniq {𝔅 𝔄'} κ (K: pctx 𝔅 𝔄') :
    PctxNoShr K → PctxNoShr (PUniq κ K).
  Proof. done. Qed.
  Global Instance pctx_no_shr_core {𝔅 𝔄} (K: pctx 𝔅 𝔄) :
    PctxNoShr K → PctxNoShr (pctx_core K).
  Proof. rewrite /PctxNoShr. induction K; simpl; auto. Qed.

  (** ** Basic laws *)

  Lemma pctx_get_set {𝔅 𝔄} (K: pctx 𝔅 𝔄) x y : pctx_get K (pctx_set K x y) = y.
  Proof.
    induction K in x, y |- *; simpl; auto; [by rewrite psum_proj_or_pinj IHK|].
    by rewrite uniq_bor_current_set IHK.
  Qed.

  Lemma pctx_set_get {𝔅 𝔄} (K: pctx 𝔅 𝔄) x : pctx_in K x → pctx_set K x (pctx_get K x) = x.
  Proof.
    induction K in x |- *; simpl;
      [by intros|intros; by rewrite IHK // -surjective_pairing..| | |
       intros; by rewrite IHK // -surjective_pairing].
    - rewrite /psum_proj_or. destruct x as [s pad]. simpl.
      case_match eqn:Hs; [|intros []]. intros Hin.
      rewrite IHK //. by rewrite -(psum_proj_Some _ _ _ Hs).
    - intros. by rewrite IHK // uniq_bor_set_current_id.
  Qed.

  Lemma pctx_mode_add {𝔅 𝔄} (K: pctx 𝔅 𝔄) m : pctx_mode K m = m + pctx_mode K 0.
  Proof.
    induction K in m |- *; simpl; [lia|done|done| |apply IHK| |];
      rewrite IHK (IHK (0 + 1)); lia.
  Qed.

  Lemma pctx_mode_noderef {𝔅 𝔄} (K: pctx 𝔅 𝔄) m : pctx_noderef K → pctx_mode K m = m.
  Proof. induction K; simpl; naive_solver. Qed.

  Lemma pctx_depth_noderef {𝔅 𝔄} (K: pctx 𝔅 𝔄) d : pctx_noderef K → pctx_depth K d = d.
  Proof. induction K in d |- *; simpl; naive_solver. Qed.

  Lemma pctx_depth_mono {𝔅 𝔄} (K: pctx 𝔅 𝔄) d d' : d ≤ d' → pctx_depth K d ≤ pctx_depth K d'.
  Proof. induction K in d, d' |- *; simpl; [done|auto|auto| |auto| |]; intros; apply IHK; lia. Qed.

  (** The depth of the hole decreases by one per owned pointer. *)
  Lemma pctx_depth_sub {𝔅 𝔄} (K: pctx 𝔅 𝔄) d : pctx_depth K d = d - pctx_mode K 0.
  Proof.
    induction K in d |- *; simpl; [lia|done|done| |apply IHK| |];
      rewrite IHK (pctx_mode_add K (0 + 1)); lia.
  Qed.

  Lemma pctx_path_app {𝔅 𝔄} (K: pctx 𝔅 𝔄) q : pctx_path K q = pctx_path K [] ++ q.
  Proof.
    induction K in q |- *; simpl; [done| | | | | |].
    - rewrite IHK (IHK [false]) -app_assoc. done.
    - rewrite IHK (IHK [true]) -app_assoc. done.
    - rewrite IHK (IHK [false]) -app_assoc. done.
    - rewrite IHK (IHK [false]) -app_assoc. done.
    - rewrite IHK (IHK [false]) -app_assoc. done.
    - rewrite IHK (IHK [false]) -app_assoc. done.
  Qed.

  Lemma lty_size_plug {𝔅 𝔄} (K: pctx 𝔅 𝔄) lt : lty_size (pctx_plug K lt) = pctx_size K (lty_size lt).
  Proof. induction K in lt |- *; simpl; by rewrite ?IHK. Qed.

  Lemma lty_pat_plug {𝔅 𝔄} (K: pctx 𝔅 𝔄) lt : lty_pat (pctx_plug K lt) = pctx_pat K (lty_pat lt).
  Proof. induction K in lt |- *; simpl; by rewrite ?IHK. Qed.

  Lemma lty_nblk_plug {𝔅 𝔄} (K: pctx 𝔅 𝔄) lt : lty_nblk (pctx_plug K lt) = pctx_nblk K + lty_nblk lt.
  Proof. induction K in lt |- *; simpl; rewrite ?IHK; lia. Qed.

  Lemma lty_nrc_plug {𝔅 𝔄} (K: pctx 𝔅 𝔄) lt e mm :
    lty_nrc (pctx_plug K lt) e mm = pctx_nrc K e mm + lty_nrc lt (pctx_ne K e mm) (pctx_nmm K e mm).
  Proof. induction K in lt, e, mm |- *; simpl; rewrite ?IHK; lia. Qed.

  (** Changing the hole for one with the same receipts. *)
  Lemma lty_nrc_plug_eq {𝔅 𝔄} (K: pctx 𝔅 𝔄) lt lt' :
    lty_nrc lt' = lty_nrc lt → lty_nrc (pctx_plug K lt') = lty_nrc (pctx_plug K lt).
  Proof. intros Heq. fun_ext=> e. fun_ext=> mm. by rewrite !lty_nrc_plug Heq. Qed.

  Lemma lty_core_plug {𝔅 𝔄} (K: pctx 𝔅 𝔄) lt :
    lty_core (pctx_plug K lt) = pctx_plug (pctx_core K) (lty_core lt).
  Proof. induction K in lt |- *; simpl; by rewrite ?IHK. Qed.

  Lemma lty_fold_plug_core {𝔅 𝔄} (K: pctx 𝔅 𝔄) lt :
    lty_fold (pctx_plug K lt) = lty_fold (pctx_plug (pctx_core K) (lty_core lt)).
  Proof. by rewrite -lty_core_plug lty_fold_core. Qed.

  Lemma lty_rfn_plug {𝔅 𝔄} (K: pctx 𝔅 𝔄) lt x ζm q :
    lty_rfn (pctx_plug K lt) x ζm q =
      pctx_rfn K x ζm q (lty_rfn lt (pctx_get K x) ζm (pctx_path K q)).
  Proof.
    induction K in lt, x, q |- *; simpl; try by rewrite ?IHK.
    rewrite /psum_proj_or. destruct (psum_proj i x.1); [by rewrite IHK|done].
  Qed.

  Lemma pctx_rfn_set {𝔅 𝔄} (K: pctx 𝔅 𝔄) `{!PctxNoShr K} x y ζm q r :
    pctx_in K x → pctx_rfn K (pctx_set K x y) ζm q r = pctx_rfn K x ζm q r.
  Proof.
    rename select (PctxNoShr K) into HK. rewrite /PctxNoShr in HK.
    induction K in HK, x, y, q, r |- *; simpl; simpl in HK; try done;
      try (intros; by rewrite ?IHK).
    - rewrite psum_proj_pinj /psum_proj_or. destruct (psum_proj i x.1); [|done].
      intros. by rewrite IHK.
    - intros. by rewrite uniq_bor_loc_set uniq_bor_current_set uniq_bor_ξi_set IHK.
  Qed.

  Lemma pctx_in_set {𝔅 𝔄} (K: pctx 𝔅 𝔄) x y : pctx_in K x → pctx_in K (pctx_set K x y).
  Proof.
    induction K in x, y |- *; simpl; [by intros|apply IHK|apply IHK|apply IHK| | |apply IHK].
    - rewrite psum_proj_pinj /psum_proj_or. case_match; [apply IHK|intros []].
    - rewrite uniq_bor_current_set. apply IHK.
  Qed.

  (** Adding an entry for the path of the hole does not change the refinements of
      the rest. *)
  Lemma pctx_rfn_blk_cons {𝔅 𝔄} (K: pctx 𝔅 𝔄) x ζm ζi q r :
    pctx_rfn K x ((pctx_path K q, ζi) :: ζm) q r = pctx_rfn K x ζm q r.
  Proof.
    induction K in x, q, r |- *; simpl; [done| | |by rewrite IHK| |by rewrite IHK|done].
    - rewrite IHK. f_equal. f_equal. apply lty_rfn_blk_irrel=> r' /=.
      rewrite decide_False; [done|]. rewrite pctx_path_app. by apply lpath_app_cons_ne.
    - rewrite IHK. f_equal. f_equal. apply lty_rfn_blk_irrel=> r' /=.
      rewrite decide_False; [done|]. rewrite pctx_path_app. by apply lpath_app_cons_ne.
    - destruct (psum_proj i x.1); [by rewrite IHK|done].
  Qed.

  (** More generally, adding an entry for a path below the hole. *)
  Lemma pctx_rfn_blk_cons_below {𝔅 𝔄} (K: pctx 𝔅 𝔄) x ζm ζi q s r :
    pctx_rfn K x ((s ++ pctx_path K q, ζi) :: ζm) q r = pctx_rfn K x ζm q r.
  Proof.
    induction K in x, q, r |- *; simpl; [done| | | | |by rewrite IHK|done].
    - rewrite IHK.
      f_equal. f_equal. apply lty_rfn_blk_irrel=> r' /=.
      rewrite decide_False; [done|]. rewrite pctx_path_app app_assoc. by apply lpath_app_cons_ne.
    - rewrite IHK.
      f_equal. f_equal. apply lty_rfn_blk_irrel=> r' /=.
      rewrite decide_False; [done|]. rewrite pctx_path_app app_assoc. by apply lpath_app_cons_ne.
    - by rewrite IHK.
    - destruct (psum_proj i x.1); [by rewrite IHK|done].
  Qed.

  Lemma pctx_rfn_rsv {𝔅 𝔄} (K: pctx 𝔅 𝔄) x ζm q (r r': prfn 𝔅) ζl ζl' :
    (∀ ζ, ζ ∈ ζl → ζ ∈ ζl') →
    prfn_rsv (pctx_rfn K x ζm q r) ζl → prfn_rsv r' ζl' → prfn_rsv (pctx_rfn K x ζm q r') ζl'.
  Proof.
    intros Hin. induction K in x, q, r, r' |- *; simpl; [done| | | | | |].
    - intros [H1 H2] H'. split; [by eapply IHK|]. by eapply prfn_rsv_weaken.
    - intros [H1 H2] H'. split; [by eapply prfn_rsv_weaken|]. by eapply IHK.
    - intros H H'. by eapply IHK.
    - destruct (psum_proj i x.1); [|intros; rewrite /prfn_dummy /=; by intros ???].
      rewrite !(prfn_rsv_sum' _ _ x.2). intros H H'. by eapply IHK.
    - intros [H1 H2] H'. split; [by eapply IHK|].
      eapply uniq_prvar_dep_irrel, proph_dep_weaken; [|exact H2]. done.
    - intros _ _. exact (prfn_rsv_in (𝔄:=at_clocₛ 𝔄') x ζl').
  Qed.

  (** If a new hole refinement [r'] depends on what [r] depends on (and [ζl']), so does
      the plugged refinement. *)
  Lemma pctx_rfn_rsv_mono {𝔅 𝔄} (K: pctx 𝔅 𝔄) x ζm q (r r': prfn 𝔅) ζl ζl' :
    (∀ ζ, ζ ∈ ζl → ζ ∈ ζl') → (prfn_rsv r ζl → prfn_rsv r' ζl') →
    prfn_rsv (pctx_rfn K x ζm q r) ζl → prfn_rsv (pctx_rfn K x ζm q r') ζl'.
  Proof.
    intros Hin. induction K in x, q, r, r' |- *; simpl; [done| | | | | |].
    - intros H [H1 H2]. split; [by eapply IHK|]. by eapply prfn_rsv_weaken.
    - intros H [H1 H2]. split; [by eapply prfn_rsv_weaken|]. by eapply IHK.
    - intros H H'. by eapply IHK.
    - destruct (psum_proj i x.1); [|intros; rewrite /prfn_dummy /=; by intros ???].
      rewrite !(prfn_rsv_sum' _ _ x.2). intros H H'. by eapply IHK.
    - intros H [H1 H2]. split; [by eapply IHK|].
      eapply uniq_prvar_dep_irrel, proph_dep_weaken; [|exact H2]. done.
    - intros _ _. exact (prfn_rsv_in (𝔄:=at_clocₛ 𝔄') x ζl').
  Qed.

  Lemma pctx_loc_fst {𝔅 𝔄} (K: pctx 𝔅 𝔄) n x l :
    pctx_noderef K → (pctx_loc K n x l).1 = l.1 +ₗ pctx_off K.
  Proof.
    induction K in x, l |- *; simpl; [by rewrite shift_loc_0|intros ?; by rewrite IHK| |done| |done|done].
    - intros ?. rewrite IHK // /= shift_loc_assoc. f_equal. lia.
    - intros ?. rewrite IHK // /= shift_loc_assoc. f_equal. lia.
  Qed.

  (** ** Contexts below no unique borrow

      The ownership of a place in [Owned] mode splits into the ownership of the hole and
      of the rest ([ltype_own_plug]) only if the hole is below no unique borrow (across
      [PUniq] the hole is inside a borrow, which has to be opened: see [pctx_acc.v]). The
      condition is a type class, solved by the structure of the context. *)
  Class PctxNoUniq {𝔅 𝔄} (K: pctx 𝔅 𝔄) : Prop := pctx_no_uniq : pctx_nouniq K.

  Global Instance pctx_no_uniq_hole {𝔅} : PctxNoUniq (PHole (𝔅:=𝔅)).
  Proof. done. Qed.
  Global Instance pctx_no_uniq_fst {𝔅 𝔄1 𝔄2} (K: pctx 𝔅 𝔄1) (lt2: lty 𝔄2) :
    PctxNoUniq K → PctxNoUniq (PFst K lt2).
  Proof. done. Qed.
  Global Instance pctx_no_uniq_snd {𝔅 𝔄1 𝔄2} (lt1: lty 𝔄1) (K: pctx 𝔅 𝔄2) :
    PctxNoUniq K → PctxNoUniq (PSnd lt1 K).
  Proof. done. Qed.
  Global Instance pctx_no_uniq_own {𝔅 𝔄'} n (K: pctx 𝔅 𝔄') :
    PctxNoUniq K → PctxNoUniq (POwn n K).
  Proof. done. Qed.
  Global Instance pctx_no_uniq_sum {𝔅 𝔄l} (tyl: typel 𝔄l) i w (K: pctx 𝔅 (𝔄l !!ₗ i)) :
    PctxNoUniq K → PctxNoUniq (PSum tyl i w K).
  Proof. done. Qed.
  Global Instance pctx_no_uniq_core {𝔅 𝔄} (K: pctx 𝔅 𝔄) :
    PctxNoUniq K → PctxNoUniq (pctx_core K).
  Proof. rewrite /PctxNoUniq. induction K; simpl; auto. Qed.

  (** Below no unique borrow and no shared reference, in particular below no shared
      reference. *)
  Global Instance pctx_no_uniq_no_shr {𝔅 𝔄} (K: pctx 𝔅 𝔄) : PctxNoUniq K → PctxNoShr K.
  Proof. rewrite /PctxNoUniq /PctxNoShr. induction K; simpl; tauto. Qed.

  Lemma pctx_no_uniq_noderef {𝔅 𝔄} (K: pctx 𝔅 𝔄) : pctx_noderef K → PctxNoUniq K.
  Proof. rewrite /PctxNoUniq. induction K; simpl; tauto. Qed.

  Lemma pctx_ne_nouniq {𝔅 𝔄} (K: pctx 𝔅 𝔄) `{!PctxNoUniq K} e mm : pctx_ne K e mm = e.
  Proof.
    rename select (PctxNoUniq K) into HK. rewrite /PctxNoUniq in HK.
    induction K in HK, e, mm |- *; simpl; simpl in HK; auto; done.
  Qed.

  (** Sharing a leaf below no unique borrow adds no receipt. *)
  Lemma lty_nrc_plug_shr_nouniq {𝔅 𝔄} (K: pctx 𝔅 𝔄) `{!PctxNoUniq K} (ty: type 𝔅) α :
    lty_nrc (pctx_plug K (ShrBlocked ty α)) 0 0 = lty_nrc (pctx_plug K (OfTy ty)) 0 0.
  Proof. rewrite !lty_nrc_plug /= pctx_ne_nouniq. lia. Qed.

  (** Blocking a leaf below no unique borrow adds one receipt. *)
  Lemma lty_nrc_plug_blocked {𝔅 𝔄} (K: pctx 𝔅 𝔄) `{!PctxNoUniq K} (ty: type 𝔅) α :
    lty_nrc (pctx_plug K (Blocked ty α)) 0 0 = lty_nrc (pctx_plug K (OfTy ty)) 0 0 + 1.
  Proof. rewrite !lty_nrc_plug /= pctx_ne_nouniq. lia. Qed.

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
    | POwn n' K => λ x ζm q d g tid l,
        l #↦!∗ [FVal (LitV x.1)] ∗ ⌜d ≠ 0%nat⌝ ∗ ▷^m (freeable_sz n' (pctx_size K n) x.1) ∗
        pctx_own K n (m + 1) x.2 ζm (false :: q) (pred d) g tid (x.1, repeat [] (pctx_size K n))
    | PSum tyl i _ K => λ x ζm q d g tid l,
        match psum_proj i x.1 with
        | Some y =>
            cloc_take l 1 #↦∗ [ #i ] ∗
            pctx_own K n m y ζm (false :: q) d g tid (cloc_take (cloc_skip l 1) (pctx_size K n)) ∗
            cloc_skip (cloc_skip l 1) (pctx_size K n) #↦!∗ fmap FVal (vec_to_list
              (padding_to_vec (max_hlist_set (λ _, ty_size) tyl i (pctx_size K n) -
                pctx_size K n) x.2))
        | None => False
        end
    (* Below a unique borrow, the ownership does not split (see [pctx_acc.v]); below a
       shared reference, nothing is owned. *)
    | PUniq _ _ | PShr _ _ => λ _ _ _ _ _ _ _, False
    end%I.

  Lemma ltype_own_plug {𝔅 𝔄} (K: pctx 𝔅 𝔄) `{!PctxNoUniq K} (lt: lty 𝔅) m p r x ζm q d g tid l :
    ltype_own_cp false (pctx_plug K lt) (Owned m) (pctx_pat K p) (pctx_rfn K x ζm q r)
      d g tid l ⊣⊢
    ltype_own_cp false lt (Owned (pctx_mode K m)) p r (pctx_depth K d) g tid
      (pctx_loc K (lty_size lt) x l) ∗
    pctx_own K (lty_size lt) m x ζm q d g tid l.
  Proof.
    rename select (PctxNoUniq K) into HK. rewrite /PctxNoUniq in HK.
    induction K in HK, lt, r, m, x, q, d, l |- *; simpl; simpl in HK; [|..|done|done].
    - by rewrite right_id.
    - rewrite lty_size_plug IHK //. rewrite /ltype_own. by rewrite assoc.
    - rewrite IHK //. rewrite /ltype_own. rewrite assoc (comm _ (ltype_own_cp _ _ _ _ _ _ _ _ _)).
      by rewrite -assoc.
    - rewrite /own_node lty_size_plug IHK //. iSplit.
      + iIntros "($ & $ & $ & $ & $)".
      + iIntros "($ & $ & $ & $ & $)".
    - rewrite /psum_proj_or. destruct (psum_proj i x.1) as [y|].
      + rewrite sum_node_sum lty_size_plug IHK //. iSplit.
        * iIntros "($ & [$ $] & $)".
        * iIntros "[$ ($ & $ & $)]".
      + rewrite /sum_node. iSplit; [by iIntros "[]"|by iIntros "[_ []]"].
  Qed.

  (** The ownership of the rest of the place implies that the value is of the
      variants of [K]. *)
  Lemma pctx_own_in {𝔅 𝔄} (K: pctx 𝔅 𝔄) n m x ζm q d g tid l :
    pctx_own K n m x ζm q d g tid l -∗ ⌜pctx_in K x⌝.
  Proof.
    induction K in m, x, q, d, l |- *; simpl; [by iIntros| | | | |by iIntros "[]"|by iIntros "[]"].
    - iIntros "[A _]". by iApply IHK.
    - iIntros "[_ A]". by iApply IHK.
    - iIntros "(_ & _ & _ & A)". by iApply IHK.
    - destruct (psum_proj i x.1); [|by iIntros "[]"]. iIntros "(_ & A & _)". by iApply IHK.
  Qed.

  Lemma pctx_own_set {𝔅 𝔄} (K: pctx 𝔅 𝔄) n m x y ζm q d g tid l :
    pctx_in K x →
    pctx_own K n m (pctx_set K x y) ζm q d g tid l = pctx_own K n m x ζm q d g tid l.
  Proof.
    induction K in m, x, y, q, d, l |- *; simpl; try (intros; by rewrite ?IHK).
    rewrite psum_proj_pinj /psum_proj_or. destruct (psum_proj i x.1); [|done].
    intros. by rewrite IHK.
  Qed.

  Lemma pctx_loc_set {𝔅 𝔄} (K: pctx 𝔅 𝔄) n x y l :
    pctx_in K x → pctx_loc K n (pctx_set K x y) l = pctx_loc K n x l.
  Proof.
    induction K in x, y, l |- *; simpl; try (intros; by rewrite ?IHK).
    - rewrite psum_proj_or_pinj /psum_proj_or. destruct (psum_proj i x.1); [|done].
      intros. by rewrite IHK.
    - intros. by rewrite uniq_bor_current_set uniq_bor_loc_set IHK.
  Qed.

  Lemma pctx_own_blk_cons {𝔅 𝔄} (K: pctx 𝔅 𝔄) n m x ζm ζi q d g tid l :
    pctx_own K n m x ((pctx_path K q, ζi) :: ζm) q d g tid l = pctx_own K n m x ζm q d g tid l.
  Proof.
    induction K in m, x, q, d, l |- *; simpl; [done| | |by rewrite IHK| |done|done].
    - rewrite IHK. f_equal. f_equal. apply lty_rfn_blk_irrel=> r' /=.
      rewrite decide_False; [done|]. rewrite pctx_path_app. by apply lpath_app_cons_ne.
    - rewrite IHK. f_equal. f_equal. apply lty_rfn_blk_irrel=> r' /=.
      rewrite decide_False; [done|]. rewrite pctx_path_app. by apply lpath_app_cons_ne.
    - destruct (psum_proj i x.1); [by rewrite IHK|done].
  Qed.

  Lemma pctx_own_blk_cons_below {𝔅 𝔄} (K: pctx 𝔅 𝔄) n m x ζm ζi q s d g tid l :
    pctx_own K n m x ((s ++ pctx_path K q, ζi) :: ζm) q d g tid l =
      pctx_own K n m x ζm q d g tid l.
  Proof.
    induction K in m, x, q, d, l |- *; simpl; [done| | | | |done|done].
    - rewrite IHK.
      f_equal. f_equal. apply lty_rfn_blk_irrel=> r' /=.
      rewrite decide_False; [done|]. rewrite pctx_path_app app_assoc. by apply lpath_app_cons_ne.
    - rewrite IHK.
      f_equal. f_equal. apply lty_rfn_blk_irrel=> r' /=.
      rewrite decide_False; [done|]. rewrite pctx_path_app app_assoc. by apply lpath_app_cons_ne.
    - by rewrite IHK.
    - destruct (psum_proj i x.1); [by rewrite IHK|done].
  Qed.

  Lemma pctx_own_depth_mono {𝔅 𝔄} (K: pctx 𝔅 𝔄) n m x ζm q d g d' g' tid l :
    d ≤ d' → g ≤ g' →
    pctx_own K n m x ζm q d g tid l ⊢ pctx_own K n m x ζm q d' g' tid l.
  Proof.
    induction K in m, x, q, d, d', l |- *; intros ??; simpl; [done| | | | |done|done].
    - iIntros "[A B]". iSplitL "A"; [by iApply IHK|].
      by iApply (ltype_own_owned_depth_mono with "B").
    - iIntros "[A B]". iSplitL "A"; [by iApply (ltype_own_owned_depth_mono with "A")|].
      by iApply IHK.
    - iIntros "($ & % & $ & A)". iSplit; [iPureIntro; lia|]. iApply (IHK with "A"); lia.
    - destruct (psum_proj i x.1); [|by iIntros "[]"].
      iIntros "($ & A & $)". by iApply IHK.
  Qed.

  (** The depth of the place is at least the number of owned pointers above the hole. *)
  Lemma pctx_own_mode_le {𝔅 𝔄} (K: pctx 𝔅 𝔄) n m x ζm q d g tid l :
    pctx_own K n m x ζm q d g tid l -∗ ⌜pctx_mode K 0 ≤ d⌝.
  Proof.
    induction K in m, x, q, d, l |- *; simpl; [iIntros "_"; iPureIntro; lia| | | | |by iIntros "[]"|by iIntros "[]"].
    - iIntros "[A _]". by iApply IHK.
    - iIntros "[_ A]". by iApply IHK.
    - iIntros "(_ & %Hd & _ & A)". iDestruct (IHK with "A") as %?.
      rewrite pctx_mode_add. iPureIntro. lia.
    - destruct (psum_proj i x.1); [|by iIntros "[]"]. iIntros "(_ & A & _)". by iApply IHK.
  Qed.

  (** The location of the hole is part of the location of the place (below an owned
      pointer, its cells are trivially owned). *)
  Lemma pctx_loc_guard {𝔅 𝔄} (K: pctx 𝔅 𝔄) `{!PctxNoUniq K} n x l (G: iProp Σ) E k :
    (G &&{E; k}&&> l #↦∗_) -∗ (G &&{E; k}&&> pctx_loc K n x l #↦∗_).
  Proof.
    rename select (PctxNoUniq K) into HK. rewrite /PctxNoUniq in HK.
    induction K in HK, x, l |- *; simpl; simpl in HK; [by iIntros "$"| | | | |done|done];
      iIntros "G"; (iApply IHK; [done|]).
    - rewrite (heap_cloc_mapsto_emp_vec_app l (pctx_size K n)).
      iApply (guards_weaken_rhs_sep_l with "G").
    - rewrite (heap_cloc_mapsto_emp_vec_app l (lty_size lt1)).
      iApply (guards_weaken_rhs_sep_r with "G").
    - rewrite -heap_cloc_mapsto_empty. iApply guards_true.
    - rewrite (heap_cloc_mapsto_emp_vec_app l 1).
      iDestruct (guards_weaken_rhs_sep_r with "G") as "G".
      rewrite (heap_cloc_mapsto_emp_vec_app (cloc_skip l 1) (pctx_size K n)).
      iApply (guards_weaken_rhs_sep_l with "G").
  Qed.

  (** ** The address of the hole

      [pctx_expr K e] computes the address of the hole, from the address [e] of the
      place: field offsets, and a load per owned pointer. *)
  Fixpoint pctx_expr {𝔅 𝔄} (K: pctx 𝔅 𝔄) (e: expr) : expr :=
    match K with
    | PHole => e
    | PFst K _ => pctx_expr K e
    | PSnd lt1 K => pctx_expr K (e +ₗ #(lty_size lt1))%E
    | POwn _ K => pctx_expr K (!e)%E
    | PSum _ _ _ K => pctx_expr K (e +ₗ #1)%E
    | PUniq _ K | PShr _ K => pctx_expr K (!e)%E
    end.

  Lemma pctx_expr_closed {𝔅 𝔄} (K: pctx 𝔅 𝔄) e : Closed [] e → Closed [] (pctx_expr K e).
  Proof. induction K in e |- *; simpl; [done|auto|intros ?; apply IHK; apply _..]. Qed.

  Lemma wp_pctx_expr_mask {𝔅 𝔄} E (K: pctx 𝔅 𝔄) n m x ζm q d g tid (l: cloc) (e: expr) (G R: iProp Σ) k :
    ↑NllftG ⊆ E →
    (G &&{↑NllftG; k}&&> l #↦∗_) -∗ £(3 * k * pctx_mode K 0) -∗
    WP e @ E {{ v, ⌜v = #(l.1)⌝ ∗ R ∗ G }} -∗ pctx_own K n m x ζm q d g tid l -∗
    WP pctx_expr K e @ E {{ v, ⌜v = #(pctx_loc K n x l).1⌝ ∗ R ∗ G ∗ pctx_own K n m x ζm q d g tid l }}.
  Proof.
    intros HE. induction K in m, x, q, d, l, e, R |- *; simpl.
    - iIntros "_ _ WP $". iApply (wp_wand with "WP"). iIntros (v) "($ & $ & $)".
    - iIntros "#Gl £ WP [Own Sib]". iApply (wp_wand with "[- Sib]").
      { iApply (IHK m x.1 (false :: q) d (cloc_take l (pctx_size K n)) with "[] £ WP Own").
        rewrite (heap_cloc_mapsto_emp_vec_app l (pctx_size K n)).
        iApply (guards_weaken_rhs_sep_l with "Gl"). }
      iIntros (v) "($ & $ & $ & $)". iFrame.
    - iIntros "#Gl £ WP [Sib Own]". iApply (wp_wand with "[- Sib]").
      { iApply (IHK m x.2 (true :: q) d (cloc_skip l (lty_size lt1)) _ R with "[] £ [WP] Own").
        - rewrite (heap_cloc_mapsto_emp_vec_app l (lty_size lt1)).
          iApply (guards_weaken_rhs_sep_r with "Gl").
        - wp_bind e. iApply (wp_wand with "WP"). iIntros (v) "(-> & R & G)". wp_op.
          iFrame. done. }
      iIntros (v) "($ & $ & $ & $)". iFrame.
    - rewrite pctx_mode_add. iIntros "#Gl £ WP (Pt & %Hd & Fr & Own)".
      iDestruct (lc_weaken (3 * k + 3 * k * pctx_mode K 0) with "£") as "[£1 £]"; [lia|].
      iApply (wp_wand with "[- Fr]").
      { iApply (IHK (m + 1) x.2 (false :: q) (pred d) (x.1, repeat [] (pctx_size K n)) _
          (R ∗ l #↦!∗ [FVal (LitV x.1)])%I with "[] £ [WP Pt £1] Own").
        - rewrite -heap_cloc_mapsto_empty. iApply guards_true.
        - wp_bind e. iApply (wp_wand with "WP"). iIntros (v) "(-> & R & G)".
          iApply (wp_read_na_guarded_cells_singleton _ l.1 l.2 (G ∗ l #↦!∗ [FVal (LitV x.1)])
            #(x.1) k with "[G Pt £1]"); [solve_ndisj| |].
          + iFrame "G Pt £1". iApply guard_cloc_combine.
            * by iApply guards_weaken_lhs_sep_l.
            * iApply (lguards_weaken_later _ _ _ 0); [lia|iApply guards_weaken_sep_r].
          + iIntros "!> [G Pt]". iFrame. done. }
      iIntros (v) "($ & [$ $] & $ & $)". by iFrame.
    - destruct (psum_proj i x.1) as [y|] eqn:Hy; [|by iIntros "_ _ _ []"].
      iIntros "#Gl £ WP (Tag & Own & Pad)". iApply (wp_wand with "[- Tag Pad]").
      { iApply (IHK m y (false :: q) d (cloc_take (cloc_skip l 1) (pctx_size K n)) _ R
          with "[] £ [WP] Own").
        - rewrite (heap_cloc_mapsto_emp_vec_app l 1).
          iDestruct (guards_weaken_rhs_sep_r with "Gl") as "Gl'".
          rewrite (heap_cloc_mapsto_emp_vec_app (cloc_skip l 1) (pctx_size K n)).
          iApply (guards_weaken_rhs_sep_l with "Gl'").
        - wp_bind e. iApply (wp_wand with "WP"). iIntros (v) "(-> & R & G)". wp_op.
          iFrame. done. }
      rewrite /psum_proj_or Hy. iIntros (v) "($ & $ & $ & $)". iFrame.
    - by iIntros "_ _ _ []".
    - by iIntros "_ _ _ []".
  Qed.

  Lemma wp_pctx_expr {𝔅 𝔄} (K: pctx 𝔅 𝔄) n m x ζm q d g tid (l: cloc) (e: expr) (G R: iProp Σ) k :
    (G &&{↑NllftG; k}&&> l #↦∗_) -∗ £(3 * k * pctx_mode K 0) -∗
    WP e {{ v, ⌜v = #(l.1)⌝ ∗ R ∗ G }} -∗ pctx_own K n m x ζm q d g tid l -∗
    WP pctx_expr K e {{ v, ⌜v = #(pctx_loc K n x l).1⌝ ∗ R ∗ G ∗ pctx_own K n m x ζm q d g tid l }}.
  Proof. by apply wp_pctx_expr_mask. Qed.

  (** ** Patterns *)

  Lemma pat_blk_lfts_plug {𝔅 𝔄} (K: pctx 𝔅 𝔄) p p' α :
    α ∈ pat_blk_lfts (pctx_pat K p') → α ∈ pat_blk_lfts p' ∨ α ∈ pat_blk_lfts (pctx_pat K p).
  Proof.
    induction K; simpl; [by left| | |done|done|done|by intros ?%not_elem_of_nil]; rewrite !elem_of_app.
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

  Lemma pat_ok_plug_hole κ {𝔅 𝔄} (K: pctx 𝔅 𝔄) `{!PctxNoShr K} p :
    pat_ok κ (pctx_pat K p) -∗ pat_ok κ p.
  Proof.
    rename select (PctxNoShr K) into HK. rewrite /PctxNoShr in HK.
    rewrite /pat_ok. induction K; simpl; simpl in HK; [by iIntros "$"| | |auto|auto|auto|done];
      rewrite big_sepL_app.
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
    induction K in lt |- *; simpl; [iApply guards_refl| | |iApply IHK|
      iApply llftl_incl_trans; [iApply (lty_lft_sum _ _ (pctx_plug K lt))|iApply IHK]|
      iApply llftl_incl_trans; [iApply llftl_intersect_incl_r|iApply IHK]|
      iApply llftl_incl_trans; [iApply llftl_intersect_incl_r|iApply IHK]];
      (iApply llftl_incl_trans; [|iApply IHK]); rewrite lft_intersect_list_app;
      [iApply llftl_intersect_incl_l|iApply llftl_intersect_incl_r].
  Qed.

  Lemma pctx_rfn_den {𝔅 𝔄} (K: pctx 𝔅 𝔄) x ζm q (r r': prfn 𝔅) π :
    prfn_den r π = prfn_den r' π →
    prfn_den (pctx_rfn K x ζm q r) π = prfn_den (pctx_rfn K x ζm q r') π.
  Proof.
    intros Heq. induction K in x, q, r, r', Heq |- *; simpl; try by rewrite ?(IHK _ _ r r').
    - destruct (psum_proj i x.1); [|done]. rewrite /prfn_sum /= !psum_map1_pinj.
      by rewrite (IHK _ _ r r').
    - rewrite (IHK _ _ r r') //. f_equal. apply uniq_prvar_app_irrel.
  Qed.

  (** ** Simple places and compound places *)

  Fixpoint pctx_simple {𝔅 𝔄} (K: pctx 𝔅 𝔄) : Prop :=
    match K with
    | PHole => True
    | PFst K lt2 => pctx_simple K ∧ lty_simple lt2
    | PSnd lt1 K => lty_simple lt1 ∧ pctx_simple K
    | POwn _ K | PSum _ _ _ K | PUniq _ K | PShr _ K => pctx_simple K
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

  (** ** Changing the type of the hole

      [pctx_retype K 𝔅'] is the context [K] with a hole of type [𝔅'] (the same
      siblings and owned pointers), a context for the root type [pctx_root K 𝔅'].
      [pctx_reset K x y] replaces the value of the hole of [x] by [y] (of the new
      type). Used when the type of a subplace changes, e.g. when a value is moved out
      of it (it becomes uninitialized) or written into it. *)
  Fixpoint pctx_root {𝔅 𝔄} (K: pctx 𝔅 𝔄) (𝔅': syn_type) : syn_type :=
    match K with
    | PHole => 𝔅'
    | @PFst _ _ 𝔄2 K _ => (pctx_root K 𝔅' * 𝔄2)%ST
    | @PSnd _ 𝔄1 _ _ K => (𝔄1 * pctx_root K 𝔅')%ST
    | POwn _ K => at_locₛ (pctx_root K 𝔅')
    (* Not supported: changing the type of the payload of a sum (the layer is
       dropped, see [pctx_nosum]). *)
    | PSum _ _ _ K => pctx_root K 𝔅'
    | PUniq _ K => uniq_borₛ (pctx_root K 𝔅')
    | PShr _ K => at_clocₛ (pctx_root K 𝔅')
    end.

  Fixpoint pctx_retype {𝔅 𝔄} (K: pctx 𝔅 𝔄) (𝔅': syn_type) : pctx 𝔅' (pctx_root K 𝔅') :=
    match K as K0 in pctx _ _ return pctx 𝔅' (pctx_root K0 𝔅') with
    | PHole => PHole
    | PFst K lt2 => PFst (pctx_retype K 𝔅') lt2
    | PSnd lt1 K => PSnd lt1 (pctx_retype K 𝔅')
    | POwn n K => POwn n (pctx_retype K 𝔅')
    | PSum _ _ _ K => pctx_retype K 𝔅'
    | PUniq κ K => PUniq κ (pctx_retype K 𝔅')
    | PShr κ K => PShr κ (pctx_retype K 𝔅')
    end.

  Fixpoint pctx_reset {𝔅 𝔄} (K: pctx 𝔅 𝔄) {𝔅'} : ~~𝔄 → ~~𝔅' → ~~(pctx_root K 𝔅') :=
    match K as K0 in pctx _ 𝔄0 return ~~𝔄0 → ~~𝔅' → ~~(pctx_root K0 𝔅') with
    | PHole => λ _ y, y
    | PFst K _ => λ x y, (pctx_reset K x.1 y, x.2)
    | PSnd _ K => λ x y, (x.1, pctx_reset K x.2 y)
    | POwn _ K => λ x y, (x.1, pctx_reset K x.2 y)
    | PSum _ i w K => λ x y, pctx_reset K (psum_proj_or i x.1 w) y
    | PUniq _ K => λ x y, uniq_bor_retype x (pctx_reset K (uniq_bor_current x) y)
    | PShr _ K => λ x y, (x.1, pctx_reset K x.2 y)
    end.

  Lemma pctx_get_reset {𝔅 𝔄 𝔅'} (K: pctx 𝔅 𝔄) x (y: ~~𝔅') :
    pctx_get (pctx_retype K 𝔅') (pctx_reset K x y) = y.
  Proof. induction K in x |- *; simpl; auto. by rewrite uniq_bor_current_retype. Qed.

  Lemma pctx_size_retype {𝔅 𝔄} (K: pctx 𝔅 𝔄) 𝔅' n :
    pctx_nosum K → pctx_size (pctx_retype K 𝔅') n = pctx_size K n.
  Proof. induction K; simpl; try done; intros; by rewrite ?IHK. Qed.

  Lemma pctx_mode_retype {𝔅 𝔄} (K: pctx 𝔅 𝔄) 𝔅' m : pctx_mode (pctx_retype K 𝔅') m = pctx_mode K m.
  Proof. induction K in m |- *; simpl; by rewrite ?IHK. Qed.

  Lemma pctx_depth_retype {𝔅 𝔄} (K: pctx 𝔅 𝔄) 𝔅' d : pctx_depth (pctx_retype K 𝔅') d = pctx_depth K d.
  Proof. induction K in d |- *; simpl; by rewrite ?IHK. Qed.

  Lemma pctx_path_retype {𝔅 𝔄} (K: pctx 𝔅 𝔄) 𝔅' q :
    pctx_nosum K → pctx_path (pctx_retype K 𝔅') q = pctx_path K q.
  Proof. induction K in q |- *; simpl; try done; intros; by rewrite ?IHK. Qed.

  Lemma pctx_nblk_retype {𝔅 𝔄} (K: pctx 𝔅 𝔄) 𝔅' : pctx_nblk (pctx_retype K 𝔅') = pctx_nblk K.
  Proof. induction K; simpl; by rewrite ?IHK. Qed.

  Lemma pctx_expr_retype {𝔅 𝔄} (K: pctx 𝔅 𝔄) 𝔅' e :
    pctx_nosum K → pctx_expr (pctx_retype K 𝔅') e = pctx_expr K e.
  Proof. induction K in e |- *; simpl; try done; intros; by rewrite ?IHK. Qed.

  Lemma pctx_loc_reset {𝔅 𝔄 𝔅'} (K: pctx 𝔅 𝔄) n x (y: ~~𝔅') l :
    pctx_nosum K → pctx_loc (pctx_retype K 𝔅') n (pctx_reset K x y) l = pctx_loc K n x l.
  Proof.
    induction K in x, l |- *; simpl; try done; intros;
      by rewrite ?pctx_size_retype ?uniq_bor_current_retype ?uniq_bor_loc_retype ?IHK.
  Qed.

  Lemma pctx_own_reset {𝔅 𝔄 𝔅'} (K: pctx 𝔅 𝔄) n m x (y: ~~𝔅') ζm q d g tid l :
    pctx_nosum K →
    pctx_own (pctx_retype K 𝔅') n m (pctx_reset K x y) ζm q d g tid l =
      pctx_own K n m x ζm q d g tid l.
  Proof.
    induction K in m, x, q, d, l |- *; simpl; try done; intros; by rewrite ?pctx_size_retype ?IHK.
  Qed.

  Lemma lty_size_plug_retype {𝔅 𝔄 𝔅'} (K: pctx 𝔅 𝔄) (lt: lty 𝔅) (lt': lty 𝔅') :
    pctx_nosum K → lty_size lt' = lty_size lt →
    lty_size (pctx_plug (pctx_retype K 𝔅') lt') = lty_size (pctx_plug K lt).
  Proof. intros ? Hsz. by rewrite !lty_size_plug pctx_size_retype // Hsz. Qed.

  Lemma pctx_nrc_retype {𝔅 𝔄} (K: pctx 𝔅 𝔄) 𝔅' e mm :
    pctx_nrc (pctx_retype K 𝔅') e mm = pctx_nrc K e mm.
  Proof. induction K in e, mm |- *; simpl; by rewrite ?IHK. Qed.
  Lemma pctx_ne_retype {𝔅 𝔄} (K: pctx 𝔅 𝔄) 𝔅' e mm :
    pctx_ne (pctx_retype K 𝔅') e mm = pctx_ne K e mm.
  Proof. induction K in e, mm |- *; simpl; by rewrite ?IHK. Qed.
  Lemma pctx_nmm_retype {𝔅 𝔄} (K: pctx 𝔅 𝔄) 𝔅' e mm :
    pctx_nmm (pctx_retype K 𝔅') e mm = pctx_nmm K e mm.
  Proof. induction K in e, mm |- *; simpl; by rewrite ?IHK. Qed.

  Lemma lty_nrc_plug_retype {𝔅 𝔄 𝔅'} (K: pctx 𝔅 𝔄) (lt: lty 𝔅) (lt': lty 𝔅') :
    (∀ e mm, lty_nrc lt' e mm = lty_nrc lt e mm) →
    lty_nrc (pctx_plug (pctx_retype K 𝔅') lt') = lty_nrc (pctx_plug K lt).
  Proof.
    intros Hn. fun_ext=> e. fun_ext=> mm.
    by rewrite !lty_nrc_plug pctx_nrc_retype pctx_ne_retype pctx_nmm_retype Hn.
  Qed.

  Lemma lty_nblk_plug_retype {𝔅 𝔄 𝔅'} (K: pctx 𝔅 𝔄) (lt: lty 𝔅) (lt': lty 𝔅') :
    lty_nblk lt' = lty_nblk lt →
    lty_nblk (pctx_plug (pctx_retype K 𝔅') lt') = lty_nblk (pctx_plug K lt).
  Proof. intros Hn. by rewrite !lty_nblk_plug pctx_nblk_retype Hn. Qed.

  (** ** Locations without ghost cells

      A place rooted at an owned location has no ghost cells, nor have its subplaces. *)
  Lemma take_repeat_add {A} (a: A) n k : take n (repeat a (n + k)) = repeat a n.
  Proof. induction n; simpl; by f_equal. Qed.

  Lemma drop_repeat_add {A} (a: A) n k : drop n (repeat a (n + k)) = repeat a k.
  Proof. induction n; simpl; done. Qed.

  Lemma pctx_loc_empty {𝔅 𝔄} (K: pctx 𝔅 𝔄) `{!PctxNoUniq K} n x (l: loc) :
    ∃ l', pctx_loc K n x (l, repeat [] (pctx_size K n)) = (l', repeat [] n).
  Proof.
    rename select (PctxNoUniq K) into HK. rewrite /PctxNoUniq in HK.
    induction K in HK, x, l |- *; simpl; simpl in HK; [by eexists|..|done|done].
    - rewrite /cloc_take /= take_repeat_add. by apply IHK.
    - rewrite /cloc_skip /= drop_repeat_add. by apply IHK.
    - by apply IHK.
    - rewrite /cloc_take /cloc_skip /=.
      have Hle := max_hlist_set_ge (λ _, ty_size) tyl i (pctx_size K n).
      rewrite -(Nat.sub_add (pctx_size K n) (max_hlist_set _ tyl i _)) //.
      rewrite drop_0 Nat.add_comm repeat_app take_app_length'; [by apply IHK|by rewrite repeat_length].
  Qed.

  Global Instance pctx_no_uniq_retype {𝔅 𝔄} (K: pctx 𝔅 𝔄) 𝔅' :
    PctxNoUniq K → PctxNoUniq (pctx_retype K 𝔅').
  Proof. rewrite /PctxNoUniq. induction K; simpl; auto. Qed.

  Global Instance pctx_no_shr_retype {𝔅 𝔄} (K: pctx 𝔅 𝔄) 𝔅' :
    PctxNoShr K → PctxNoShr (pctx_retype K 𝔅').
  Proof. rewrite /PctxNoShr. induction K; simpl; auto. Qed.
End pctx.

(** A context with a [PUniq] step is not [PctxNoUniq]. *)
Ltac pctx_no_uniq_contra :=
  match goal with
  | H : PctxNoUniq (PUniq _ _) |- _ => exfalso; exact H
  | H : PctxNoUniq (PShr _ _) |- _ => exfalso; exact H
  | H : PctxNoShr (PShr _ _) |- _ => exfalso; exact H
  end.
