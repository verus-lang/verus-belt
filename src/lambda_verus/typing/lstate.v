(** * States of place types

  The [Σ]-independent part of the place types of [typing/ltype.v]: place
  refinements and blocking patterns. The state of the pinned body of a unique
  borrow (see [uniq_util.v]) is a pair of a blocking pattern and a place
  refinement, held in a (Leibniz) ghost variable; this is why these are defined
  before the types. *)

From iris.proofmode Require Import proofmode.
From lrust.prophecy Require Export syn_type prophecy.
From lrust.lang Require Import heap.
From lrust.util Require Import basic fancy_lists.
From lrust.lifetime Require Import lifetime_full.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅 ℭ: syn_type.

(** * Utilities for sums

  Sum places ([SumLty] in [typing/ltype.v]) are refined by a sum of refinements
  ([prfn_struct] of [xsumₛ]), whose payload is accessed with [psum_proj]; the folded
  type of a sum place replaces the type of its variant ([hlist_set]). *)

Section psum_proj.
  Context {A: Type} {F: A → Type}.

  (** The payload of a sum, if it is of variant [i]. *)
  Fixpoint psum_proj {Xl: list A} : ∀ i, psum F Xl → option (F (Xl !!ₗ i)) :=
    match Xl with
    | [] => fin_0_inv _
    | X :: Xl' => fin_S_inv (λ i, psum F (X :: Xl') → option (F ((X :: Xl') !!ₗ i)))
        (λ s, match s with inl a => Some a | inr _ => None end)
        (λ j s, match s with inl _ => None | inr s' => psum_proj j s' end)
    end.

  Lemma psum_proj_pinj {Xl: list A} i (x: F (Xl !!ₗ i)) : psum_proj i (pinj i x) = Some x.
  Proof.
    move: Xl i x. elim; [move=> i; by inv_fin i|]=> X Xl IH i.
    inv_fin i; [done|]=> j x /=. apply IH.
  Qed.

  Lemma psum_proj_Some {Xl: list A} i (s: psum F Xl) y : psum_proj i s = Some y → s = pinj i y.
  Proof.
    move: Xl i s y. elim; [move=> i; by inv_fin i|]=> X Xl IH i.
    inv_fin i; [by move=> [a|s'] y //= [=->]|]=> j [a|s'] y //= ?. f_equal. by apply IH.
  Qed.

  Definition psum_proj_or {Xl: list A} i (s: psum F Xl) (w: F (Xl !!ₗ i)) : F (Xl !!ₗ i) :=
    match psum_proj i s with Some y => y | None => w end.

  Lemma psum_proj_or_pinj {Xl: list A} i (x w: F (Xl !!ₗ i)) : psum_proj_or i (pinj i x) w = x.
  Proof. by rewrite /psum_proj_or psum_proj_pinj. Qed.
End psum_proj.
Global Arguments psum_proj_or : simpl never.

(** A property of the payload of a sum. *)
Fixpoint psum_all {A} {F: A → Type} (P: ∀ X, F X → Prop) {Xl} : psum F Xl → Prop :=
  match Xl with
  | [] => λ _, True
  | _ :: _ => λ s, match s with inl a => P _ a | inr s' => psum_all P s' end
  end.

Lemma psum_all_pinj_eq {A} {F: A → Type} (P: ∀ X, F X → Prop) {Xl: list A} i (x: F (Xl !!ₗ i)) :
  psum_all P (pinj i x) = P _ x.
Proof.
  move: Xl i x. elim; [move=> i; by inv_fin i|]=> X Xl IH i.
  inv_fin i; [done|]=> j x /=. apply IH.
Qed.

Lemma psum_all_pinj {A} {F: A → Type} (P: ∀ X, F X → Prop) {Xl: list A} i (x: F (Xl !!ₗ i)) :
  psum_all P (pinj i x) ↔ P _ x.
Proof. by rewrite psum_all_pinj_eq. Qed.

Section hlist_set.
  Context {A: Type} {F: A → Type}.

  (** Replacing the element at [i]. *)
  Fixpoint hlist_set {Xl} (xl: hlist F Xl) : ∀ i, F (Xl !!ₗ i) → hlist F Xl :=
    match xl in hlist _ Xl return ∀ i, F (Xl !!ₗ i) → hlist F Xl with
    | +[] => fin_0_inv _
    | @hcons _ _ X Xl' x xl' => fin_S_inv (λ i, F ((X :: Xl') !!ₗ i) → hlist F (X :: Xl'))
        (λ y, y +:: xl') (λ j y, x +:: hlist_set xl' j y)
    end.

  Lemma hlookup_hlist_set {Xl} (xl: hlist F Xl) i y : hlist_set xl i y +!! i = y.
  Proof. induction xl; inv_fin i; [done|]=> j y /=. apply IHxl. Qed.

  Lemma hlist_set_hlookup {Xl} (xl: hlist F Xl) i : hlist_set xl i (xl +!! i) = xl.
  Proof. induction xl; inv_fin i; [done|]=> j /=. by rewrite IHxl. Qed.

  (** The maximum of [f] over [xl], with the value at [i] replaced by [n]. *)
  Fixpoint max_hlist_set (f: ∀ X, F X → nat) {Xl} (xl: hlist F Xl) :
      fin (length Xl) → nat → nat :=
    match xl in hlist _ Xl return fin (length Xl) → nat → nat with
    | +[] => fin_0_inv _
    | x +:: xl' => fin_S_inv (λ _, nat → nat) (λ n, n `max` max_hlist_with f xl')
        (λ j n, f _ x `max` max_hlist_set f xl' j n)
    end.

  Lemma max_hlist_with_hlist_set (f: ∀ X, F X → nat) {Xl} (xl: hlist F Xl) i y :
    max_hlist_with f (hlist_set xl i y) = max_hlist_set f xl i (f _ y).
  Proof. induction xl; inv_fin i; [done|]=> j y /=. by rewrite IHxl. Qed.

  Lemma max_hlist_set_ge (f: ∀ X, F X → nat) {Xl} (xl: hlist F Xl) i n :
    n ≤ max_hlist_set f xl i n.
  Proof. induction xl; inv_fin i=>/=; [lia|]=> j. have := IHxl j. lia. Qed.
End hlist_set.

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
  (* A sum at a fixed variant: the refinement of the payload, and the padding. *)
  | xsumₛ 𝔅l => psum (λ 𝔅, place_rfn 𝔅 + prfn_struct 𝔅) 𝔅l * list val
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
  | xsumₛ 𝔅l => λ r, match r with
      | inl lr => place_rfn_wit lr
      | inr (s, pad) => (psum_map1 (λ _ r', prfn_wit r') s, pad)
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
  | xsumₛ 𝔅l => λ r, match r with
      | inl lr => place_rfn_den lr
      | inr (s, pad) => λ π, (psum_map1 (λ _ r', prfn_den r' π) s, pad)
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

(** * Reservations

  [prfn_rsv r ζl]: the denotations of the prophetic leaves ([PlaceProph]) of [r]
  depend only on [ζl]; so do the final values of the nested unique borrows with a
  structured refinement (which are part of the denotation of [r]). A compound place behind a unique borrow holds a reservation
  of the borrow's prophecy variable for such a [ζl] (see [cpd_own] in
  [typing/ltype.v]), so that it can be resolved while some of its leaves are
  blocked. *)

Definition place_rfn_rsv {𝔄} (r: place_rfn 𝔄) (ζl: list proph_var) : Prop :=
  match r with PlaceIn _ => True | PlaceProph _ f => f ./ ζl end.

Fixpoint prfn_rsv {𝔄} : prfn 𝔄 → list proph_var → Prop :=
  match 𝔄 return prfn 𝔄 → list proph_var → Prop with
  | uniq_borₛ 𝔅 => λ r ζl, match r with
      | inl lr => place_rfn_rsv lr ζl
      | inr (_, r', ξi) => prfn_rsv r' ζl ∧
          (λ π, (π (uniq_prvar (prfn_wit r') ξi)).1) ./ ζl
      end
  | at_locₛ 𝔅 => λ r ζl, match r with
      | inl lr => place_rfn_rsv lr ζl
      | inr (_, r') => prfn_rsv r' ζl
      end
  | prodₛ 𝔅 ℭ => λ r ζl, match r with
      | inl lr => place_rfn_rsv lr ζl
      | inr (r1, r2) => prfn_rsv r1 ζl ∧ prfn_rsv r2 ζl
      end
  | xsumₛ 𝔅l => λ r ζl, match r with
      | inl lr => place_rfn_rsv lr ζl
      | inr (s, _) => psum_all (λ _ r', prfn_rsv r' ζl) s
      end
  | _ => λ r ζl, match r with inl lr => place_rfn_rsv lr ζl | inr e => match e with end end
  end.

Lemma prfn_rsv_inl {𝔄} (lr: place_rfn 𝔄) ζl : prfn_rsv (inl lr) ζl = place_rfn_rsv lr ζl.
Proof. by destruct 𝔄. Qed.

Lemma prfn_rsv_in {𝔄} (x: ~~𝔄) ζl : prfn_rsv (inl (PlaceIn x)) ζl.
Proof. by rewrite prfn_rsv_inl. Qed.

Lemma proph_dep_weaken {A} (vπ: proph A) ζl ζl' :
  (∀ ζ, ζ ∈ ζl → ζ ∈ ζl') → vπ ./ ζl → vπ ./ ζl'.
Proof. move=> In Dep π π' Eqv. apply Dep=> ζ ?. by apply Eqv, In. Qed.

Lemma prfn_rsv_weaken {𝔄} (r: prfn 𝔄) ζl ζl' :
  (∀ ζ, ζ ∈ ζl → ζ ∈ ζl') → prfn_rsv r ζl → prfn_rsv r ζl'.
Proof.
  move=> In. have Hl: ∀ (𝔅: syn_type) (lr: place_rfn 𝔅),
    place_rfn_rsv lr ζl → place_rfn_rsv lr ζl'.
  { move=> ? [?|??] /=; [done|]. by apply proph_dep_weaken. }
  move: 𝔄 r. fix FIX 1. move=> 𝔄 r.
  destruct 𝔄; destruct r as [lr|r]; simpl; try apply Hl; try (destruct r; fail).
  - destruct r as [r1 r2]. move=> [??]. split; by apply FIX.
  - destruct r as [s pad]. simpl. move: s. elim: l=> [|𝔅 𝔅l IH] s /=; [by destruct s|].
    destruct s as [r'|s']; [by apply FIX|by apply IH].
  - destruct r as [l' r']. apply FIX.
  - destruct r as [[l' r'] ξi]. move=> [??]. split; [by apply FIX|].
    by eapply proph_dep_weaken.
Qed.

Lemma prfn_rsv_app_l {𝔄} (r: prfn 𝔄) ζl ζl' : prfn_rsv r ζl → prfn_rsv r (ζl ++ ζl').
Proof. apply prfn_rsv_weaken=> ??. set_solver. Qed.

Lemma prfn_rsv_app_r {𝔄} (r: prfn 𝔄) ζl ζl' : prfn_rsv r ζl' → prfn_rsv r (ζl ++ ζl').
Proof. apply prfn_rsv_weaken=> ??. set_solver. Qed.

(** The refinement of a sum at variant [i], with payload refinement [r] and padding
    [pad]. *)
Definition prfn_sum {𝔄l} (i: fin (length 𝔄l)) (r: prfn (𝔄l !!ₗ i)) (pad: list val) :
    prfn (Σ! 𝔄l) :=
  inr (pinj (F:=λ 𝔅, (place_rfn 𝔅 + prfn_struct 𝔅)%type) i r, pad).

Global Arguments prfn_sum : simpl never.

Lemma prfn_den_sum {𝔄l} i (r: prfn (𝔄l !!ₗ i)) pad :
  prfn_den (prfn_sum i r pad) = λ π, (pinj i (prfn_den r π), pad).
Proof. rewrite /prfn_sum /=. fun_ext=> π. by rewrite psum_map1_pinj. Qed.

Lemma prfn_wit_sum {𝔄l} i (r: prfn (𝔄l !!ₗ i)) pad :
  prfn_wit (prfn_sum i r pad) = (pinj i (prfn_wit r), pad).
Proof. by rewrite /prfn_sum /= psum_map1_pinj. Qed.

Lemma prfn_rsv_sum {𝔄l} i (r: prfn (𝔄l !!ₗ i)) pad ζl :
  prfn_rsv (prfn_sum i r pad) ζl = prfn_rsv r ζl.
Proof. rewrite /prfn_sum /=. apply (psum_all_pinj_eq (λ _ r', prfn_rsv r' ζl)). Qed.

(** As [prfn_rsv_sum], [prfn_den_sum], after [simpl]. *)
Lemma prfn_rsv_sum' {𝔄l} i (r: prfn (𝔄l !!ₗ i)) pad ζl :
  match prfn_sum i r pad with
  | inl lr => place_rfn_rsv lr ζl
  | inr (s, _) => psum_all (λ _ r', prfn_rsv r' ζl) s
  end = prfn_rsv r ζl.
Proof. exact (prfn_rsv_sum i r pad ζl). Qed.

(** The denotation of [PlaceGhost x₀ ζi] depends only on the prophecy variable. *)
Lemma place_ghost_dep {𝔄} (x₀: ~~𝔄) ζi :
  place_rfn_den (PlaceGhost x₀ ζi) ./ [uniq_prvar x₀ ζi].
Proof. apply (proph_dep_constr fst (λ π, π (uniq_prvar x₀ ζi))), proph_dep_one. Qed.

Lemma place_ghost_rsv {𝔄} (x₀: ~~𝔄) ζi : place_rfn_rsv (PlaceGhost x₀ ζi) [uniq_prvar x₀ ζi].
Proof. apply place_ghost_dep. Qed.

(** * Blocking patterns *)

(** The [Σ]-independent part of a place type: which subplaces are blocked,
    and at which lifetime. *)
Inductive lpat :=
| PatLeaf
| PatBlocked (α: lft)
| PatUniq (p: lpat)
| PatOwn (p: lpat)
| PatProd (p1 p2: lpat)
(* A shared-blocked leaf: shared at [α] (its value does not change), see
   [ShrBlocked] in [typing/ltype.v]. *)
| PatShrBlocked (α: lft)
(* A sum at a fixed variant, see [SumLty] in [typing/ltype.v]. *)
| PatSum (p: lpat).

Global Instance lpat_inhabited : Inhabited lpat := populate PatLeaf.

Definition pat_uniq (p: lpat) : lpat := match p with PatUniq p' => p' | _ => PatLeaf end.
Definition pat_own (p: lpat) : lpat := match p with PatOwn p' => p' | _ => PatLeaf end.
Definition pat_l (p: lpat) : lpat := match p with PatProd p1 _ => p1 | _ => PatLeaf end.
Definition pat_r (p: lpat) : lpat := match p with PatProd _ p2 => p2 | _ => PatLeaf end.
Definition pat_sum (p: lpat) : lpat := match p with PatSum p' => p' | _ => PatLeaf end.

(** The blocked lifetimes of a pattern. Blocked places behind a nested unique
    borrow are included: this is the _nested membership condition_ (the pinned body
    of a borrow only admits states whose blocked lifetimes, also behind nested
    unique borrows, are included in its pattern lifetime, so that a nested borrow
    can be folded back once the outer one has ended; see [uniq_node_unblock_fold]
    in [typing/ltype.v]). *)
Fixpoint pat_blk_lfts (p: lpat) : list lft :=
  match p with
  | PatLeaf => []
  | PatUniq p' => pat_blk_lfts p'
  | PatBlocked α => [α]
  | PatOwn p' => pat_blk_lfts p'
  | PatProd p1 p2 => pat_blk_lfts p1 ++ pat_blk_lfts p2
  | PatSum p' => pat_blk_lfts p'
  | PatShrBlocked α => [α]
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
