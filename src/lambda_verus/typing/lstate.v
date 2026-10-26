(** * States of place types

  The [Σ]-independent part of the place types of [typing/ltype.v]: place
  refinements and blocking patterns. The state of the pinned body of a unique
  borrow (see [uniq_util.v]) is a pair of a blocking pattern and a place
  refinement, held in a (Leibniz) ghost variable; this is why these are defined
  before the types. *)

From iris.proofmode Require Import proofmode.
From lrust.prophecy Require Export syn_type prophecy.
From lrust.lang Require Import heap.
From lrust.lifetime Require Import lifetime_full.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅 ℭ: syn_type.

(** * Place refinements

  A blocked place has no current value of type [~~𝔄] (e.g. [~~Zₛ = Z] cannot
  mention a prophecy). As in RefinedRust, refinements are therefore _place
  refinements_: [PlaceIn x] (a current value) or [PlaceProph x₀ f], denoting the
  prophecy [f] ([x₀] only witnesses inhabitation). Typically, [f] is the final
  value of the prophecy variable of a reborrow ([PlaceGhost]). *)

Inductive place_rfn (𝔄: syn_type) : Type :=
| PlaceIn (x: ~~𝔄)
| PlaceProph (x₀: ~~𝔄) (f: proph 𝔄).
Global Arguments PlaceIn {_} _.
Global Arguments PlaceProph {_} _ _.

(** The final value of (the prophecy variable of) a unique borrow. *)
Definition PlaceGhost {𝔄} (x₀: ~~𝔄) (ζi: positive) : place_rfn 𝔄 :=
  PlaceProph x₀ (λ π, (π (uniq_prvar x₀ ζi)).1).

(** Structured refinements of compound places. *)
Fixpoint prfn_struct (𝔄: syn_type) : Type :=
  match 𝔄 with
  | uniq_borₛ 𝔅 => cloc * (place_rfn 𝔅 + prfn_struct 𝔅) * positive
  | at_locₛ 𝔅 => loc * (place_rfn 𝔅 + prfn_struct 𝔅)
  | prodₛ 𝔅 ℭ => (place_rfn 𝔅 + prfn_struct 𝔅) * (place_rfn ℭ + prfn_struct ℭ)
  | _ => Empty_set
  end%type.

(** A refinement is either a place refinement (for a leaf, or a folded compound
    place) or a structured refinement (for an unfolded compound place). *)
Definition prfn (𝔄: syn_type) : Type := (place_rfn 𝔄 + prfn_struct 𝔄)%type.

Definition place_rfn_wit {𝔄} (r: place_rfn 𝔄) : ~~𝔄 :=
  match r with PlaceIn x => x | PlaceProph x₀ _ => x₀ end.

Definition place_rfn_den {𝔄} (r: place_rfn 𝔄) : proph 𝔄 :=
  match r with
  | PlaceIn x => vπ x
  | PlaceProph _ f => f
  end.

Definition idx_dummy : Idx := (1%positive, ∅).

(** A witness value (only used for inhabitation of prophecy variables). *)
Fixpoint prfn_wit {𝔄} : prfn 𝔄 → ~~𝔄 :=
  match 𝔄 return prfn 𝔄 → ~~𝔄 with
  | uniq_borₛ 𝔅 => λ r, match r with
      | inl lr => place_rfn_wit lr
      | inr (l', r', ξi) => (l', prfn_wit r', ξi, 0%nat, 0%nat, idx_dummy)
      end
  | at_locₛ 𝔅 => λ r, match r with
      | inl lr => place_rfn_wit lr
      | inr (l', r') => (l', prfn_wit r')
      end
  | prodₛ 𝔅 ℭ => λ r, match r with
      | inl lr => place_rfn_wit lr
      | inr (r1, r2) => (prfn_wit r1, prfn_wit r2)
      end
  | _ => λ r, match r with inl lr => place_rfn_wit lr | inr e => match e with end end
  end.

(** The denotation of a refinement. *)
Fixpoint prfn_den {𝔄} : prfn 𝔄 → proph 𝔄 :=
  match 𝔄 return prfn 𝔄 → proph 𝔄 with
  | uniq_borₛ 𝔅 => λ r, match r with
      | inl lr => place_rfn_den lr
      | inr (l', r', ξi) => λ π, (prfn_den r' π, (π (uniq_prvar (prfn_wit r') ξi)).1)
      end
  | at_locₛ 𝔅 => λ r, match r with
      | inl lr => place_rfn_den lr
      | inr (l', r') => λ π, (l', prfn_den r' π)
      end
  | prodₛ 𝔅 ℭ => λ r, match r with
      | inl lr => place_rfn_den lr
      | inr (r1, r2) => λ π, (prfn_den r1 π, prfn_den r2 π)
      end
  | _ => λ r, match r with inl lr => place_rfn_den lr | inr e => match e with end end
  end.

Lemma prfn_den_inl {𝔄} (lr: place_rfn 𝔄) : prfn_den (inl lr) = place_rfn_den lr.
Proof. by destruct 𝔄. Qed.

Lemma prfn_den_in {𝔄} (x: ~~𝔄) : prfn_den (inl (PlaceIn x)) = vπ x.
Proof. by destruct 𝔄. Qed.

Lemma prfn_wit_inl {𝔄} (lr: place_rfn 𝔄) : prfn_wit (inl lr) = place_rfn_wit lr.
Proof. by destruct 𝔄. Qed.

Lemma prfn_wit_in {𝔄} (x: ~~𝔄) : prfn_wit (inl (PlaceIn x)) = x.
Proof. by destruct 𝔄. Qed.

(** A refinement as a place refinement: a structured refinement is seen as the
    prophecy of its denotation. *)
Definition prfn_place {𝔄} (r: prfn 𝔄) : place_rfn 𝔄 :=
  match r with inl lr => lr | inr _ => PlaceProph (prfn_wit r) (prfn_den r) end.

Lemma prfn_place_den {𝔄} (r: prfn 𝔄) : place_rfn_den (prfn_place r) = prfn_den r.
Proof. destruct r; [by rewrite prfn_den_inl|done]. Qed.

(** * Blocking patterns *)

(** The [Σ]-independent part of a place type: which subplaces are blocked,
    and at which lifetime. *)
Inductive lpat :=
| PatLeaf
| PatBlocked (α: lft)
| PatUniq (p: lpat)
| PatOwn (p: lpat)
| PatProd (p1 p2: lpat).

Global Instance lpat_inhabited : Inhabited lpat := populate PatLeaf.

Definition pat_uniq (p: lpat) : lpat := match p with PatUniq p' => p' | _ => PatLeaf end.
Definition pat_own (p: lpat) : lpat := match p with PatOwn p' => p' | _ => PatLeaf end.
Definition pat_l (p: lpat) : lpat := match p with PatProd p1 _ => p1 | _ => PatLeaf end.
Definition pat_r (p: lpat) : lpat := match p with PatProd _ p2 => p2 | _ => PatLeaf end.

(** The blocked lifetimes of a pattern that have to be dead to get back to
    the core in [Owned] mode. Blocked places behind a nested unique borrow
    (also the borrow's referent itself) are not included: those belong to
    the nested borrow. *)
Fixpoint pat_blk_lfts (p: lpat) : list lft :=
  match p with
  | PatLeaf | PatUniq _ => []
  | PatBlocked α => [α]
  | PatOwn p' => pat_blk_lfts p'
  | PatProd p1 p2 => pat_blk_lfts p1 ++ pat_blk_lfts p2
  end.

(** The pattern of a leaf at a state: a structured refinement (of an unfolded
    compound place) is seen by a leaf as blocked at [κ]. *)
Definition norm_pat (κ: lft) {𝔄} (p: lpat) (r: prfn 𝔄) : lpat :=
  match r with inl _ => p | inr _ => PatBlocked κ end.

(** * States *)

(** The state of the pinned body of a unique borrow: a pattern and a
    refinement. *)
Definition ltype_state : Type := (lpat * {𝔄 : syn_type & prfn 𝔄})%type.

Definition lstate {𝔄} (p: lpat) (r: prfn 𝔄) : ltype_state := (p, existT 𝔄 r).

(** The trivial state: an unblocked place at a current value. *)
Definition lstate_triv {𝔄} (x: ~~𝔄) : ltype_state := lstate PatLeaf (inl (PlaceIn x)).

Lemma lstate_inj {𝔄} (p p': lpat) (r r': prfn 𝔄) :
  lstate p r = lstate p' r' → p = p' ∧ r = r'.
Proof.
  rewrite /lstate. intros Heq. split; [exact (f_equal fst Heq)|].
  apply (Eqdep_dec.inj_pair2_eq_dec _ syn_type_beq_dec). exact (f_equal snd Heq).
Qed.
