From iris.prelude Require Import prelude.
From lrust.util Require Import basic vector fancy_lists.
From lrust.lang Require Import lang heap.
From lrust.lifetime Require Import lifetime_full.
Set Default Proof Using "Type".

(** * Syntax for Coq type *)

Definition Mask := coPset.

Inductive syn_type := intₛ (_: IntType) | boolₛ | unitₛ | Propₛ | positiveₛ
| optionₛ (_: syn_type) | listₛ (_: syn_type) | vecₛ (_: syn_type) (_: nat)
| prodₛ (_ _: syn_type) | sumₛ (_ _: syn_type)
| xprodₛ (_: list syn_type) | xsumₛ (_: list syn_type)
| at_locₛ (_: syn_type)
| uniq_borₛ (_: syn_type)
| blockedₛ (_: syn_type)
| ghostₛ (_: syn_type)
| trackedₛ (_: syn_type)
| storableₛ (_: syn_type)
| invₛ (_: syn_type)
| local_invₛ (_: syn_type)
| pcellₛ (_: mty)
| namespaceₛ
| uninitₛ (_: nat)
| locₛ
| paddingₛ
| funₛ (_: syn_type) (_: syn_type)
| exec_funₛ (_: syn_type)
| join_handleₛ (_: syn_type)
| maskₛ
.

(** The syntactic type of the integers of an [IntType]. [Zₛ] is the one of [isize]
    (the legacy integer type, see [typing/int.v]). *)
Notation Zₛ := (intₛ isize).

Notation syn_typel := (list syn_type).
Implicit Type (𝔄 𝔅: syn_type) (𝔄l 𝔅l: syn_typel).

Declare Scope syn_type_scope.
Bind Scope syn_type_scope with syn_type.
Delimit Scope syn_type_scope with ST.
Notation "()" := unitₛ : syn_type_scope.
Infix "*" := prodₛ : syn_type_scope.
Infix "+" := sumₛ : syn_type_scope.
Notation "Π!" := xprodₛ : syn_type_scope.
Notation "Σ!" := xsumₛ : syn_type_scope.
(* We use the following notation because
  [psum proph_interp_of_syn_type []] is equal to [Empty_set] *)
Notation Empty_setₛ := (xsumₛ []).

Global Instance Empty_setₛ_empty: Empty syn_type := Empty_setₛ.

Fixpoint indep_interp_of_syn_type (𝔄: syn_type) : Type :=
  match 𝔄 with
  | intₛ _ => Z | boolₛ => bool | unitₛ => () | Propₛ => Prop | positiveₛ => positive
  | optionₛ 𝔄₀ => option (indep_interp_of_syn_type 𝔄₀) | listₛ 𝔄₀ => list (indep_interp_of_syn_type 𝔄₀)
  | vecₛ 𝔄₀ n => vec (indep_interp_of_syn_type 𝔄₀) n
  | prodₛ 𝔄₀ 𝔄₁ => indep_interp_of_syn_type 𝔄₀ * indep_interp_of_syn_type 𝔄₁
  | sumₛ 𝔄₀ 𝔄₁ => indep_interp_of_syn_type 𝔄₀ + indep_interp_of_syn_type 𝔄₁
  | xprodₛ 𝔄l => plist indep_interp_of_syn_type 𝔄l
  | xsumₛ 𝔄l => psum indep_interp_of_syn_type 𝔄l * list val
  | at_locₛ 𝔄₀  => loc * indep_interp_of_syn_type 𝔄₀ 
  | uniq_borₛ 𝔄₀  => loc * indep_interp_of_syn_type 𝔄₀ * positive * nat * nat * Idx
  | blockedₛ 𝔄₀ => indep_interp_of_syn_type 𝔄₀ * positive * positive  (* first elem is only to show inhabitness *)
  | ghostₛ 𝔄₀ => indep_interp_of_syn_type 𝔄₀
  | trackedₛ 𝔄₀ => indep_interp_of_syn_type 𝔄₀
  | storableₛ 𝔄₀ => indep_interp_of_syn_type 𝔄₀ * (nat * nat) * lft
  | invₛ 𝔄₀ => namespace * gname * indep_interp_of_syn_type 𝔄₀
  | local_invₛ 𝔄₀ => namespace * (gname * gname * nat) * indep_interp_of_syn_type 𝔄₀
  | namespaceₛ => namespace
  | uninitₛ n => vec val n
  | pcellₛ _ => positive
  | locₛ => loc
  | paddingₛ => list val
  | funₛ 𝔄₀ 𝔄₁ => (indep_interp_of_syn_type 𝔄₀ → indep_interp_of_syn_type 𝔄₁)
  | exec_funₛ 𝔄₀ => val * indep_interp_of_syn_type 𝔄₀
  | join_handleₛ 𝔄₀ => indep_interp_of_syn_type 𝔄₀
  | maskₛ => Mask
  end.

Notation "~~" := indep_interp_of_syn_type.

Fixpoint proph_interp_of_syn_type (𝔄: syn_type) : Type :=
  match 𝔄 with
  | intₛ _ => Z | boolₛ => bool | unitₛ => () | Propₛ => Prop | positiveₛ => positive
  | optionₛ 𝔄₀ => option (proph_interp_of_syn_type 𝔄₀) | listₛ 𝔄₀ => list (proph_interp_of_syn_type 𝔄₀)
  | vecₛ 𝔄₀ n => vec (proph_interp_of_syn_type 𝔄₀) n
  | prodₛ 𝔄₀ 𝔄₁ => proph_interp_of_syn_type 𝔄₀ * proph_interp_of_syn_type 𝔄₁
  | sumₛ 𝔄₀ 𝔄₁ => proph_interp_of_syn_type 𝔄₀ + proph_interp_of_syn_type 𝔄₁
  | xprodₛ 𝔄l => plist proph_interp_of_syn_type 𝔄l
  | xsumₛ 𝔄l => psum proph_interp_of_syn_type 𝔄l * list val
  | at_locₛ 𝔄 => loc * proph_interp_of_syn_type 𝔄
  | uniq_borₛ 𝔄 => proph_interp_of_syn_type 𝔄 * proph_interp_of_syn_type 𝔄
  | blockedₛ 𝔄₀  => ()
  | ghostₛ 𝔄₀ => indep_interp_of_syn_type 𝔄₀
  | trackedₛ 𝔄₀ => proph_interp_of_syn_type 𝔄₀
  | storableₛ 𝔄₀ => indep_interp_of_syn_type 𝔄₀ * (nat * nat) * lft
  | uninitₛ n => ()
  | pcellₛ _ => positive
  | locₛ => loc
  | paddingₛ => list val
  | invₛ 𝔄₀ => namespace * gname * indep_interp_of_syn_type 𝔄₀
  | local_invₛ 𝔄₀ => namespace * (gname * gname * nat) * indep_interp_of_syn_type 𝔄₀
  | namespaceₛ => namespace
  | funₛ 𝔄₀ 𝔄₁ => indep_interp_of_syn_type 𝔄₀ → indep_interp_of_syn_type 𝔄₁
  | exec_funₛ 𝔄₀ => val * indep_interp_of_syn_type 𝔄₀
  | join_handleₛ 𝔄₀ => indep_interp_of_syn_type 𝔄₀
  | maskₛ => Mask
  end.
Coercion proph_interp_of_syn_type: syn_type >-> Sortclass.

Fixpoint abstracted_syn_type (𝔄: syn_type) : Type :=
  match 𝔄 with
  | intₛ _ => Z | boolₛ => bool | unitₛ => () | Propₛ => Prop | positiveₛ => positive
  | optionₛ 𝔄₀ => option (abstracted_syn_type 𝔄₀) | listₛ 𝔄₀ => list (abstracted_syn_type 𝔄₀)
  | vecₛ 𝔄₀ n => vec (abstracted_syn_type 𝔄₀) n
  | prodₛ 𝔄₀ 𝔄₁ => abstracted_syn_type 𝔄₀ * abstracted_syn_type 𝔄₁
  | sumₛ 𝔄₀ 𝔄₁ => abstracted_syn_type 𝔄₀ + abstracted_syn_type 𝔄₁
  | xprodₛ 𝔄l => plist abstracted_syn_type 𝔄l
  | xsumₛ 𝔄l => psum abstracted_syn_type 𝔄l * list val
  | at_locₛ 𝔄₀  => loc * abstracted_syn_type 𝔄₀ 
  | uniq_borₛ 𝔄₀  => loc * abstracted_syn_type 𝔄₀ * positive
  | blockedₛ 𝔄₀ => ()
  | ghostₛ 𝔄₀ => abstracted_syn_type 𝔄₀
  | trackedₛ 𝔄₀ => abstracted_syn_type 𝔄₀
  | storableₛ 𝔄₀ => abstracted_syn_type 𝔄₀ * (nat * nat) * lft
  | invₛ 𝔄₀ => namespace * gname * abstracted_syn_type 𝔄₀
  | local_invₛ 𝔄₀ => namespace * abstracted_syn_type 𝔄₀
  | namespaceₛ => namespace
  | uninitₛ n => vec val n
  | pcellₛ _ => positive
  | locₛ => loc
  | paddingₛ => list val
  | funₛ 𝔄₀ 𝔄₁ => (indep_interp_of_syn_type 𝔄₀ → indep_interp_of_syn_type 𝔄₁)
  | exec_funₛ 𝔄₀ => val * abstracted_syn_type 𝔄₀
  | join_handleₛ 𝔄₀ => abstracted_syn_type 𝔄₀
  | maskₛ => Mask
  end.
  
(** Decidable Equality *)

Fixpoint syn_type_beq 𝔄 𝔅 : bool :=
  match 𝔄, 𝔅 with
  | boolₛ, boolₛ | (), () | Propₛ, Propₛ | positiveₛ, positiveₛ
  | locₛ, locₛ | paddingₛ, paddingₛ | namespaceₛ, namespaceₛ | maskₛ, maskₛ
    => true
  | intₛ it, intₛ it' => bool_decide (it = it')
  | uninitₛ n, uninitₛ m => bool_decide (n = m)
  | pcellₛ m, pcellₛ m' => bool_decide (m = m')
  | optionₛ 𝔄₀, optionₛ 𝔅₀ | listₛ 𝔄₀, listₛ 𝔅₀ | at_locₛ 𝔄₀, at_locₛ 𝔅₀
  | uniq_borₛ 𝔄₀, uniq_borₛ 𝔅₀
  | blockedₛ 𝔄₀, blockedₛ 𝔅₀ | ghostₛ 𝔄₀, ghostₛ 𝔅₀ | invₛ 𝔄₀, invₛ 𝔅₀
  | local_invₛ 𝔄₀, local_invₛ 𝔅₀ | trackedₛ 𝔄₀, trackedₛ 𝔅₀
  | exec_funₛ 𝔄₀, exec_funₛ 𝔅₀ | join_handleₛ 𝔄₀, join_handleₛ 𝔅₀
  | storableₛ 𝔄₀, storableₛ 𝔅₀
    => syn_type_beq 𝔄₀ 𝔅₀
  | 𝔄₀ * 𝔄₁, 𝔅₀ * 𝔅₁ | 𝔄₀ + 𝔄₁, 𝔅₀ + 𝔅₁ | funₛ 𝔄₀ 𝔄₁, funₛ 𝔅₀ 𝔅₁
    => syn_type_beq 𝔄₀ 𝔅₀ && syn_type_beq 𝔄₁ 𝔅₁
  | vecₛ 𝔄₀ n, vecₛ 𝔅₀ m => syn_type_beq 𝔄₀ 𝔅₀ && bool_decide (n = m)
  | Π! 𝔄l, Π! 𝔅l | Σ! 𝔄l, Σ! 𝔅l => forall2b syn_type_beq 𝔄l 𝔅l
  | _, _ => false
  end%ST.

Lemma syn_type_beq_correct 𝔄 𝔅 : syn_type_beq 𝔄 𝔅 ↔ 𝔄 = 𝔅.
Proof.
  move: 𝔄 𝔅. fix FIX 1.
  assert (FIXl : ∀ 𝔄l 𝔅l, forall2b syn_type_beq 𝔄l 𝔅l ↔ 𝔄l = 𝔅l).
  { elim=> [|?? IH][|??]//=. rewrite andb_True IH FIX.
    split; [move=> [??]|move=> [=]]; by subst. }
  move=> 𝔄 𝔅; case 𝔄; case 𝔅=>//= *;
    rewrite ?andb_True ?FIX ?FIXl ?bool_decide_spec;
    try (by split; [move=> ->|move=> [=]]);
    by split; [move=> [->->]|move=> [=]].
Qed.
Global Instance syn_type_beq_dec: EqDecision syn_type.
Proof.
  refine (λ 𝔄 𝔅, cast_if (decide (syn_type_beq 𝔄 𝔅)));
  by rewrite -syn_type_beq_correct.
Qed.

(** Decidable Inhabitedness *)

Fixpoint inh_syn_type' 𝔄 : bool :=
  match 𝔄 with
  | vecₛ 𝔄₀ n => bool_decide (n = 0%nat) || inh_syn_type' 𝔄₀
  | prodₛ 𝔄₀ 𝔄₁ => inh_syn_type' 𝔄₀ && inh_syn_type' 𝔄₁
  | sumₛ 𝔄₀ 𝔄₁ => inh_syn_type' 𝔄₀ || inh_syn_type' 𝔄₁
  | funₛ 𝔄₀ 𝔄₁ => negb (inh_syn_type' 𝔄₀) || inh_syn_type' 𝔄₁
  | xprodₛ 𝔄l => forallb inh_syn_type' 𝔄l
  | xsumₛ 𝔄l => existsb inh_syn_type' 𝔄l
  | at_locₛ 𝔄₀ | uniq_borₛ 𝔄₀ | blockedₛ 𝔄₀ | exec_funₛ 𝔄₀ | ghostₛ 𝔄₀ | trackedₛ 𝔄₀
  | invₛ 𝔄₀ | local_invₛ 𝔄₀ | join_handleₛ 𝔄₀ | storableₛ 𝔄₀
    => inh_syn_type' 𝔄₀
  | _ => true
  end.

Fixpoint inh_syn_type 𝔄 : bool :=
  match 𝔄 with
  | vecₛ 𝔄₀ n => bool_decide (n = 0%nat) || inh_syn_type 𝔄₀
  | prodₛ 𝔄₀ 𝔄₁ => inh_syn_type 𝔄₀ && inh_syn_type 𝔄₁
  | sumₛ 𝔄₀ 𝔄₁ => inh_syn_type 𝔄₀ || inh_syn_type 𝔄₁
  | funₛ 𝔄₀ 𝔄₁ => negb (inh_syn_type' 𝔄₀) || inh_syn_type' 𝔄₁
  | xprodₛ 𝔄l => forallb inh_syn_type 𝔄l
  | xsumₛ 𝔄l => existsb inh_syn_type 𝔄l
  | at_locₛ 𝔄₀ | uniq_borₛ 𝔄₀ | trackedₛ 𝔄₀ => inh_syn_type 𝔄₀
  | exec_funₛ 𝔄₀ | ghostₛ 𝔄₀ | storableₛ 𝔄₀ | invₛ 𝔄₀ | local_invₛ 𝔄₀ | join_handleₛ 𝔄₀ => inh_syn_type' 𝔄₀
  | _ => true
  end.

Local Instance namespace_inhabited : Inhabited namespace := populate nroot.

Local Lemma of_just_and_neg_inh_syn_type' {𝔄} :
  (inh_syn_type' 𝔄 → ~~𝔄) * (negb (inh_syn_type' 𝔄) → ~~𝔄 → ∅).
Proof.
  move: 𝔄. fix FIX 1. move=> 𝔄. split.
  - case: 𝔄=>//=; try by (move=> *; exact inhabitant).
    + move=> ? n. case Eq: (bool_decide (n = 0%nat))=>/=.
      * move: Eq=> /bool_decide_eq_true ->?. exact [#].
      * move=> ?. by apply (vreplicate n), FIX.
    + move=> ?? /andb_True[??]. constructor; by apply FIX.
    + move=> 𝔄?. case Eq: (inh_syn_type' 𝔄)=>/= H.
      * apply inl, FIX. by rewrite Eq.
      * by apply inr, FIX.
    + elim; [move=> ?; exact -[]|]=> ?? IH /andb_True [??].
      split; by [apply FIX|apply IH].
    + elim; [done|]=>/= 𝔄 ? IH. case Eq: (inh_syn_type' 𝔄)=>/= H.
      * split; last by exact []. left. apply FIX. by rewrite Eq.
      * split; last by exact []. right. by apply IH.
    + move=> 𝔄 x. exact (inhabitant, fst (FIX 𝔄) x).
    + move=> 𝔄 x. exact (inhabitant, fst (FIX 𝔄) x, inhabitant, 0, 0, inhabitant).
    + move=> 𝔄 x. exact (fst (FIX 𝔄) x, inhabitant, inhabitant).
    + move=> 𝔄 x. exact (fst (FIX 𝔄) x).
    + move=> 𝔄 x. exact (fst (FIX 𝔄) x).
    + move=> 𝔄 x. exact (fst (FIX 𝔄) x, inhabitant, (∅ : lft)).
    + move=> 𝔄 x. exact (inhabitant, inhabitant, fst (FIX 𝔄) x).
    + move=> 𝔄 x. exact (inhabitant, inhabitant, fst (FIX 𝔄) x).
    + move=> 𝔄?. case Eq: (inh_syn_type' 𝔄)=>/= ??; [by apply FIX|].
      apply (@absurd ∅ _). eapply FIX; [|done]. by rewrite Eq. 
    + move=> 𝔄 x. exact (inhabitant, fst (FIX 𝔄) x).
    + move=> 𝔄 x. exact (fst (FIX 𝔄) x).
  - case: 𝔄=>//=.
    + move=> ?[|?]; rewrite negb_orb=> /andb_True[/negb_True/bool_decide_spec ??] v;
      [lia|]. by eapply FIX, vhd.
    + move=> 𝔄?. rewrite negb_andb.
      case Eq: (inh_syn_type' 𝔄)=>/= ?[a?]; [by eapply FIX|].
      eapply FIX; [|apply a]. by rewrite Eq.
    + move=> ??. by rewrite negb_orb=> /andb_True[??] [a|b];
      eapply FIX; [|apply a| |apply b].
    + elim; [done|]=> 𝔄 ? IH. rewrite negb_andb. case Eq: (inh_syn_type' 𝔄)
      =>/= ?[??]; [by apply IH|]. eapply FIX; [|done]. by rewrite Eq.
    + move=> l n [ps _]. move: l n ps.
      elim; [move=> ?; by apply absurd|]=> ?? IH.
      rewrite negb_orb=> /andb_True[??] [?|?]; by [eapply FIX|apply IH].
    + move=> 𝔄 Hneg [_ x]. exact (snd (FIX 𝔄) Hneg x).
    + move=> 𝔄 Hneg [x _]. exact (snd (FIX 𝔄) Hneg (snd (fst (fst (fst x))))).
    + move=> 𝔄 Hneg [x _]. exact (snd (FIX 𝔄) Hneg (fst x)).
    + move=> 𝔄 Hneg x. exact (snd (FIX 𝔄) Hneg x).
    + move=> 𝔄 Hneg x. exact (snd (FIX 𝔄) Hneg x).
    + move=> 𝔄 Hneg x. exact (snd (FIX 𝔄) Hneg x.1.1).
    + move=> 𝔄 Hneg x. exact (snd (FIX 𝔄) Hneg (snd x)).
    + move=> 𝔄 Hneg x. exact (snd (FIX 𝔄) Hneg (snd x)).
    + move=> ??. rewrite negb_negb_orb=> /andb_True[??] f. eapply FIX; [done|].
      by apply f, FIX. 
    + move=> 𝔄 Hneg x. exact (snd (FIX 𝔄) Hneg (snd x)).
    + move=> 𝔄 Hneg x. exact (snd (FIX 𝔄) Hneg x).
Qed.

Local Lemma of_just_and_neg_inh_syn_type {𝔄} :
  (inh_syn_type 𝔄 → 𝔄) * (negb (inh_syn_type 𝔄) → 𝔄 → ∅).
Proof.
  move: 𝔄. fix FIX 1. move=> 𝔄. split.
  - case: 𝔄=>//=; try by (move=> *; exact inhabitant).
    + move=> ? n. case Eq: (bool_decide (n = 0%nat))=>/=.
      * move: Eq=> /bool_decide_eq_true ->?. exact [#].
      * move=> ?. by apply (vreplicate n), FIX.
    + move=> ?? /andb_True[??]. constructor; by apply FIX.
    + move=> 𝔄?. case Eq: (inh_syn_type 𝔄)=>/= H.
      * apply inl, FIX. by rewrite Eq.
      * by apply inr, FIX.
    + elim; [move=> ?; exact -[]|]=> ?? IH /andb_True [??].
      split; by [apply FIX|apply IH].
    + elim; [done|]=>/= 𝔄 ? IH. case Eq: (inh_syn_type 𝔄)=>/= H.
      * split; last by exact []. left. apply FIX. by rewrite Eq.
      * split; last by exact []. right. by apply IH.
    + move=> 𝔄 x. exact (inhabitant, fst (FIX 𝔄) x).
    + move=> 𝔄 x. exact (fst (FIX 𝔄) x, fst (FIX 𝔄) x).
    + move=> 𝔄 x. exact (fst (@of_just_and_neg_inh_syn_type' 𝔄) x).
    + move=> 𝔄 x. exact (fst (FIX 𝔄) x).
    + move=> 𝔄 x. exact (fst (@of_just_and_neg_inh_syn_type' 𝔄) x, inhabitant, (∅ : lft)).
    + move=> 𝔄 x. exact (inhabitant, inhabitant, fst (@of_just_and_neg_inh_syn_type' 𝔄) x).
    + move=> 𝔄 x. exact (inhabitant, inhabitant, fst (@of_just_and_neg_inh_syn_type' 𝔄) x).
    + move=> 𝔄?. case Eq: (inh_syn_type' 𝔄)=>/= ??; [by apply @of_just_and_neg_inh_syn_type'|].
      apply (@absurd ∅ _). eapply @of_just_and_neg_inh_syn_type'; [|done]. by rewrite Eq. 
    + move=> 𝔄 x. exact (inhabitant, fst (@of_just_and_neg_inh_syn_type' 𝔄) x).
    + move=> 𝔄 x. exact (fst (@of_just_and_neg_inh_syn_type' 𝔄) x).
  - case: 𝔄=>//=.
    + move=> ?[|?]; rewrite negb_orb=> /andb_True[/negb_True/bool_decide_spec ??] v;
      [lia|]. by eapply FIX, vhd.
    + move=> 𝔄?. rewrite negb_andb.
      case Eq: (inh_syn_type 𝔄)=>/= ?[a?]; [by eapply FIX|].
      eapply FIX; [|apply a]. by rewrite Eq.
    + move=> ??. by rewrite negb_orb=> /andb_True[??] [a|b];
      eapply FIX; [|apply a| |apply b].
    + elim; [done|]=> 𝔄 ? IH. rewrite negb_andb. case Eq: (inh_syn_type 𝔄)
      =>/= ?[??]; [by apply IH|]. eapply FIX; [|done]. by rewrite Eq.
    + move=> l n [x _]. move: l n x.
      elim; [move=> ?; by apply absurd|]=> ?? IH.
      rewrite negb_orb=> /andb_True[??] [?|?]; by [eapply FIX|apply IH].
    + move=> 𝔄 Hneg [_ x]. exact (snd (FIX 𝔄) Hneg x).
    + move=> 𝔄 Hneg [x _]. exact (snd (FIX 𝔄) Hneg x).
    + move=> 𝔄 Hneg x. exact (snd (@of_just_and_neg_inh_syn_type' 𝔄) Hneg x).
    + move=> 𝔄 Hneg x. exact (snd (FIX 𝔄) Hneg x).
    + move=> 𝔄 Hneg x. exact (snd (@of_just_and_neg_inh_syn_type' 𝔄) Hneg x.1.1).
    + move=> 𝔄 Hneg x. exact (snd (@of_just_and_neg_inh_syn_type' 𝔄) Hneg (snd x)).
    + move=> 𝔄 Hneg x. exact (snd (@of_just_and_neg_inh_syn_type' 𝔄) Hneg (snd x)).
    + move=> ??. rewrite negb_negb_orb=> /andb_True[??] f. eapply @of_just_and_neg_inh_syn_type'; [done|].
      by apply f, @of_just_and_neg_inh_syn_type'.
    + move=> 𝔄 Hneg x. exact (snd (@of_just_and_neg_inh_syn_type' 𝔄) Hneg (snd x)).
    + move=> 𝔄 Hneg x. exact (snd (@of_just_and_neg_inh_syn_type' 𝔄) Hneg x).
Qed.
  
Lemma of_inh_syn_type {𝔄} : inh_syn_type 𝔄 → 𝔄.
Proof. apply of_just_and_neg_inh_syn_type. Qed.
Lemma of_neg_inh_syn_type {𝔄} : negb (inh_syn_type 𝔄) → 𝔄 → ∅.
Proof. apply of_just_and_neg_inh_syn_type. Qed.
Lemma to_inh_syn_type {𝔄} (x: 𝔄) : inh_syn_type 𝔄.
Proof.
  case Eq: (inh_syn_type 𝔄); [done|]. apply (absurd (A:=∅)).
  eapply of_neg_inh_syn_type; [|done]. by rewrite Eq.
Qed.
Lemma to_neg_inh_syn_type {𝔄} (f: 𝔄 → ∅) : negb (inh_syn_type 𝔄).
Proof.
  case Eq: (inh_syn_type 𝔄); [|done].
  apply (absurd (A:=∅)), f, of_inh_syn_type. by rewrite Eq.
Qed.

Definition syn_typei: Type := {𝔄 | inh_syn_type 𝔄}.
Implicit Type 𝔄i 𝔅i: syn_typei.

Definition of_syn_typei 𝔄i : Type := `𝔄i.
Coercion of_syn_typei: syn_typei >-> Sortclass.


Record proph_var := PrVar { pv_ty: syn_typei; pv_id: positive }.
Add Printing Constructor proph_var.

Global Instance proph_var_eq_dec: EqDecision proph_var.
Proof. solve_decision. Qed.

Definition indep_interp_of_syn_typei 𝔄i : Type := indep_interp_of_syn_type (`𝔄i).

Definition proph_asn := ∀ξ: proph_var, ξ.(pv_ty).
Notation proph A := (proph_asn → A).

Global Instance syn_typei_inhabited 𝔄i : Inhabited 𝔄i.
Proof. apply populate. case 𝔄i=> ??. by apply of_inh_syn_type. Qed.

Global Instance proph_asn_inhabited: Inhabited proph_asn.
Proof. apply populate. case=> ??. apply inhabitant. Qed.

Fixpoint vπ {𝔄} : ~~𝔄 → proph_asn → 𝔄 :=
  match 𝔄 return ~~𝔄 → proph_asn → 𝔄 with
  | intₛ _ => λ x π , x
  | boolₛ => λ x π , x
  | unitₛ => λ x π , x
  | Propₛ => λ x π , x
  | positiveₛ => λ x π , x
  | locₛ => λ x π , x
  | optionₛ 𝔄₀ => λ x π , (match x with Some x0 => Some (@vπ 𝔄₀ x0 π) | None => None end)
  | listₛ 𝔄₀ => λ x π , fmap (λ x0 , @vπ 𝔄₀ x0 π) x
  | vecₛ 𝔄₀ n => λ x π , vmap (λ x0 , @vπ 𝔄₀ x0 π) x
  | prodₛ 𝔄₀ 𝔄₁ => λ x π , (@vπ 𝔄₀ (fst x) π, @vπ 𝔄₁ (snd x) π)
  | sumₛ 𝔄₀ 𝔄₁ => λ x π , match x with inl x0 => inl (@vπ 𝔄₀ x0 π) | inr x1 => inr (@vπ 𝔄₁ x1 π) end
  | xprodₛ 𝔄l => λ x π , pmap (λ _ x0 , vπ x0 π) x
  | xsumₛ 𝔄l => λ x π , (psum_map1 (λ _ x0, vπ x0 π) x.1, x.2)
  | at_locₛ 𝔄₀  => λ x π , (fst x, @vπ 𝔄₀ (snd x) π)
  | invₛ 𝔄₀  => λ x π , (fst (fst x), snd (fst x), snd x)
  | local_invₛ 𝔄₀  => λ x π , (fst (fst x), snd (fst x), snd x)
  | uniq_borₛ 𝔄₀  => λ x π ,
      (match x with
        (l, x₀, ξi, d', g', idx) =>
          (@vπ 𝔄₀ x₀ π,
           (π (PrVar ((𝔄₀ * (positiveₛ * (positiveₛ * positiveₛ)))%ST
                ↾ @to_inh_syn_type ((𝔄₀ * (positiveₛ * (positiveₛ * positiveₛ)))%ST) (@vπ 𝔄₀ x₀ inhabitant, (1%positive, (1%positive, 1%positive)))) ξi)).1)
      end)
  | blockedₛ 𝔄₀ => λ '(x₀, ξi, ζi) π , ()
  (*| blockedₛ 𝔄₀  => λ '(x₀, ξi) π , π (PrVar (𝔄₀ ↾ to_inh_syn_type (@vπ 𝔄₀ x₀ inhabitant)) ξi)*)
  | ghostₛ 𝔄₀ => λ x π, x
  | trackedₛ 𝔄₀ => λ x π, (@vπ 𝔄₀ x π)
  | storableₛ 𝔄₀ => λ x π, x
  | uninitₛ n => λ x π, ()
  | pcellₛ _ => λ x π, x
  | paddingₛ => λ x π, x
  | funₛ 𝔄₀ 𝔄₁ => λ x π, x
  | join_handleₛ 𝔄₀  => λ x π , x
  | exec_funₛ 𝔄₀  => λ x π , x
  | maskₛ => λ x π, x
  | namespaceₛ => λ x π, x
  end.
  
Fixpoint plist_to_list {A: Type} {U: Type} {Xl} (xl: plist (λ (_ : A), U) Xl) : list U :=
  match Xl, xl with [], _ => [] | _::_, x -:: xl' => x :: (plist_to_list xl') end.
  
Fixpoint ξl {𝔄} : ~~𝔄 → list proph_var :=
  match 𝔄 return ~~𝔄 → list proph_var with
  | intₛ _ => λ x , []
  | boolₛ => λ x , []
  | unitₛ => λ x , []
  | Propₛ => λ x , []
  | positiveₛ => λ x , []
  | locₛ => λ x , []
  | optionₛ 𝔄₀ => λ x , (match x with Some x0 => (@ξl 𝔄₀ x0) | None => [] end)
  | listₛ 𝔄₀ => λ x , List.concat (fmap (λ x0 , @ξl 𝔄₀ x0) x)
  | vecₛ 𝔄₀ n => λ x , List.concat (fmap (λ x0 , @ξl 𝔄₀ x0) (vec_to_list x))
  | prodₛ 𝔄₀ 𝔄₁ => λ x , (@ξl 𝔄₀ (fst x) ++ @ξl 𝔄₁ (snd x))
  | sumₛ 𝔄₀ 𝔄₁ => λ x , match x with inl x0 => (@ξl 𝔄₀ x0) | inr x1 => (@ξl 𝔄₁ x1) end
  | xprodₛ 𝔄l => λ x , List.concat (plist_to_list (pmap (λ _ x0 , ξl x0) x))
  | xsumₛ 𝔄l => λ '(x, pad) ,
      match to_xsum (psum_map1 (λ _ x0, ξl x0) x) return (list proph_var) with
          xinj _ l => l
      end
  | at_locₛ 𝔄₀  => λ x , (@ξl 𝔄₀ (snd x))
  | invₛ 𝔄₀  => λ x , []
  | local_invₛ 𝔄₀  => λ x , []
  | uniq_borₛ 𝔄₀  => λ x ,
      (match x with
        (l, x₀, ξi, d', g', idx) =>
          let ξ := PrVar ((𝔄₀ * (positiveₛ * (positiveₛ * positiveₛ)))%ST
            ↾ @to_inh_syn_type ((𝔄₀ * (positiveₛ * (positiveₛ * positiveₛ)))%ST) (@vπ 𝔄₀ x₀ inhabitant, (1%positive, (1%positive, 1%positive)))) ξi in
          ξ :: @ξl 𝔄₀ x₀
      end)
  | blockedₛ 𝔄₀ => λ '(x₀, ξi, ζi) , []
  (*| blockedₛ 𝔄₀  => λ '(x₀, ξi) π , π (PrVar (𝔄₀ ↾ to_inh_syn_type (@vπ 𝔄₀ x₀ inhabitant)) ξi)*)
  | ghostₛ 𝔄₀ => λ x, []
  | trackedₛ 𝔄₀ => λ x, (@ξl 𝔄₀ x)
  | storableₛ 𝔄₀ => λ x , []
  | uninitₛ n => λ x , []
  | pcellₛ _ => λ x , []
  | paddingₛ => λ x , []
  | funₛ 𝔄₀ 𝔄₁ => λ x , []
  | join_handleₛ 𝔄₀  => λ x , []
  | exec_funₛ 𝔄₀  => λ x , []
  | maskₛ => λ x , []
  | namespaceₛ => λ x , []
  end.
  
  
Fixpoint size_of 𝔄 : nat :=
  match 𝔄 return nat with
  | intₛ _ => 1
  | boolₛ => 1
  | unitₛ => 0
  | Propₛ => 0
  | positiveₛ => 0
  | locₛ => 1
  | optionₛ 𝔄₀ => 0
  | listₛ 𝔄₀ => 0
  | vecₛ 𝔄₀ n => 0
  | prodₛ 𝔄₀ 𝔄₁ => (size_of 𝔄₀ + size_of 𝔄₁)
  | sumₛ 𝔄₀ 𝔄₁ => 0
  | xprodₛ 𝔄l => list_sum (fmap size_of 𝔄l)
  | xsumₛ 𝔄l => S (list_max (fmap size_of 𝔄l))
  | at_locₛ 𝔄₀  => 1
  | invₛ 𝔄₀  => 0
  | local_invₛ 𝔄₀  => 0
  | uniq_borₛ 𝔄₀  => 1
  | blockedₛ 𝔄₀ => 0
  | ghostₛ 𝔄₀ => 0
  | trackedₛ 𝔄₀ => 0
  | storableₛ 𝔄₀ => 0
  | uninitₛ n => n
  | pcellₛ _ => 0
  | paddingₛ => 0
  | funₛ 𝔄₀ 𝔄₁ => 0
  | join_handleₛ 𝔄₀  => 0
  | exec_funₛ 𝔄₀  => 1
  | maskₛ => 0
  | namespaceₛ => 0
  end.
  
Definition pad (l: list fancy_val) (n: nat) : list fancy_val :=
  if bool_decide (n < length l) then
    take n l
  else
    l ++ List.repeat (FVal (LitV LitPoison)) (n - length l).
  
Fixpoint syn_phys {𝔄} : (~~𝔄) → list fancy_val :=
  match 𝔄 return (~~𝔄) → list fancy_val with
  | intₛ _ => λ x, [ FVal (LitV (LitInt x)) ]
  | boolₛ => λ x, [FVal (LitV (lit_of_bool x))]
  | unitₛ => λ x, []
  | Propₛ => λ x, []
  | positiveₛ => λ x, []
  | locₛ => λ x, [FVal (LitV (LitLoc x))]
  | optionₛ 𝔄₀ => λ x, []
  | listₛ 𝔄₀ => λ x, []
  | vecₛ 𝔄₀ n => λ x, []
  | prodₛ 𝔄₀ 𝔄₁ => λ '(x₀, x₁), @syn_phys 𝔄₀ x₀ ++ @syn_phys 𝔄₁ x₁
  | sumₛ 𝔄₀ 𝔄₁ => λ x, []
  | xprodₛ 𝔄l => λ x , List.concat (plist_to_list (pmap (λ _ x0 , syn_phys x0) x))
  | xsumₛ 𝔄l => λ '(x, padding) ,
      match to_xsum (psum_map1 (λ _ x0, syn_phys x0) x) return (list fancy_val) with
          xinj i l => pad (FVal (LitV (LitInt i)) :: l ++ (fmap FVal padding)) (size_of 𝔄)
      end
  | at_locₛ 𝔄₀  => λ x, [FVal (LitV (LitLoc (x.1)))]
  | invₛ 𝔄₀  => λ x, []
  | local_invₛ 𝔄₀  => λ x, []
  | uniq_borₛ 𝔄₀  =>  λ x,
      (match x with
        (l, x₀, ξi, d', g', idx) => [FVal (LitV (LitLoc l))]
      end)
  | blockedₛ 𝔄₀ => λ x, []
  | ghostₛ 𝔄₀ => λ x, []
  | trackedₛ 𝔄₀ => λ x, []
  | storableₛ 𝔄₀ => λ x, []
  | uninitₛ n => λ x, fmap FVal (vec_to_list x)
  | pcellₛ _ => λ _, []
  | paddingₛ => λ x, []
  | funₛ 𝔄₀ 𝔄₁ => λ x, []
  | join_handleₛ 𝔄₀  => λ x, []
  | exec_funₛ 𝔄₀  => λ x, [FVal (fst x)]
  | maskₛ => λ x, []
  | namespaceₛ => λ x, []
  end.
      
Local Lemma length_pad l n : length (pad l n) = n.
Proof.
  unfold pad. case_decide; simpl.
    - rewrite length_take; lia.
    - rewrite length_app. rewrite repeat_length. lia.
Qed.
Lemma syn_phys_size_eq 𝔄 (x: ~~𝔄) : length (@syn_phys 𝔄 x) = size_of 𝔄.
  move: 𝔄 x. fix FIX 1. move=> 𝔄 x. destruct 𝔄; try (clear FIX; done).
  - destruct x. simpl. rewrite List.length_app. do 2 (rewrite FIX). clear FIX; trivial.
  - induction l.
    + clear FIX; trivial.
    + destruct x as [x₀ x']. simpl. rewrite List.length_app. f_equal.
      * apply FIX.
      * rewrite IHl. clear FIX; trivial.
  - destruct x as [x padding].
    simpl. destruct (to_xsum (psum_map1 (λ (A : syn_type) (x0 : ~~ A), syn_phys x0) x)).
    apply length_pad.
  - destruct x as [[[[[[l ?] ?] ?] ?] ?] ?]. clear FIX; trivial.
  - simpl. rewrite length_fmap. rewrite length_vec_to_list. clear FIX; trivial.
Qed.

Definition blockedπ {𝔄} : ~~(blockedₛ 𝔄) → proph_asn → 𝔄 :=
  match 𝔄 return ~~(blockedₛ 𝔄) → proph_asn → 𝔄 with
    | uniq_borₛ 𝔄₀ => λ '(x, ξi, ζi) π ,
      (match x with
        (l, x₀, ξi', d', g', idx) =>
          ((π (PrVar ((𝔄₀ * (positiveₛ * (positiveₛ * positiveₛ)))%ST
               ↾ @to_inh_syn_type ((𝔄₀ * (positiveₛ * (positiveₛ * positiveₛ)))%ST) (@vπ 𝔄₀ x₀ inhabitant, (1%positive, (1%positive, 1%positive)))) ξi')).1,
           (π (PrVar ((𝔄₀ * (positiveₛ * (positiveₛ * positiveₛ)))%ST
               ↾ @to_inh_syn_type ((𝔄₀ * (positiveₛ * (positiveₛ * positiveₛ)))%ST) (@vπ 𝔄₀ x₀ inhabitant, (1%positive, (1%positive, 1%positive)))) ζi)).1)
      end)
    | 𝔄₀ => λ '(x, ξi, ζi) π , π (PrVar (𝔄₀ ↾ to_inh_syn_type (@vπ 𝔄₀ x inhabitant)) ξi)
  end.

(** The prophecy variable backing a unique borrow. It ranges over the borrow's
    value together with a pair of depth indices and a ghost name: the depth indices
    are tracked at the type-system level by embedding [positiveₛ] into the
    variable's type (a depth [d] is encoded as [Pos.of_succ_nat d]); the ghost name
    is the name of the ghost variable holding the state of the borrow's pinned body
    (see [typing/uniq_util.v]). *)
Definition uniq_cellₛ (𝔄: syn_type) : syn_type := (𝔄 * (positiveₛ * (positiveₛ * positiveₛ)))%ST.
Definition uniq_cell_tyi {𝔄} (x₀: ~~𝔄) : syn_typei :=
  (𝔄 * (positiveₛ * (positiveₛ * positiveₛ)))%ST
    ↾ @to_inh_syn_type ((𝔄 * (positiveₛ * (positiveₛ * positiveₛ)))%ST)
        (@vπ 𝔄 x₀ inhabitant, (1%positive, (1%positive, 1%positive))).
Definition uniq_prvar {𝔄} (x₀: ~~𝔄) (ξi: positive) : proph_var :=
  PrVar (uniq_cell_tyi x₀) ξi.

Lemma uniq_cell_tyi_irrel {𝔄} (x₀ x₀': ~~𝔄) : uniq_cell_tyi x₀ = uniq_cell_tyi x₀'.
Proof. rewrite /uniq_cell_tyi. f_equal. apply proof_irrel. Qed.

Lemma uniq_prvar_irrel {𝔄} (x₀ x₀': ~~𝔄) ξi : uniq_prvar x₀ ξi = uniq_prvar x₀' ξi.
Proof. rewrite /uniq_prvar. f_equal. apply uniq_cell_tyi_irrel. Qed.

Lemma vπ_uniq_bor {𝔄} l (x₀: ~~𝔄) ξi d' g' idx :
  @vπ (uniq_borₛ 𝔄) (l, x₀, ξi, d', g', idx) =
    λ π, (vπ x₀ π, (π (uniq_prvar x₀ ξi)).1).
Proof. done. Qed.

Lemma ξl_uniq_bor {𝔄} l (x₀: ~~𝔄) ξi d' g' idx :
  @ξl (uniq_borₛ 𝔄) (l, x₀, ξi, d', g', idx) = uniq_prvar x₀ ξi :: ξl x₀.
Proof. done. Qed.

Fixpoint syn_abstract {𝔄} : ~~𝔄 → abstracted_syn_type 𝔄 :=
  match 𝔄 return ~~𝔄 → abstracted_syn_type 𝔄 with
  | intₛ _ => λ x , x
  | boolₛ => λ x , x
  | unitₛ => λ x , x
  | Propₛ => λ x , x
  | positiveₛ => λ x , x
  | locₛ => λ x , x
  | optionₛ 𝔄₀ => λ x , (match x with Some x0 => Some (@syn_abstract 𝔄₀ x0) | None => None end)
  | listₛ 𝔄₀ => λ x , fmap (λ x0 , @syn_abstract 𝔄₀ x0) x
  | vecₛ 𝔄₀ n => λ x , vmap (λ x0 , @syn_abstract 𝔄₀ x0) x
  | prodₛ 𝔄₀ 𝔄₁ => λ x , (@syn_abstract 𝔄₀ (fst x), @syn_abstract 𝔄₁ (snd x))
  | sumₛ 𝔄₀ 𝔄₁ => λ x , match x with inl x0 => inl (@syn_abstract 𝔄₀ x0) | inr x1 => inr (@syn_abstract 𝔄₁ x1) end
  | xprodₛ 𝔄l => λ x , pmap (λ _ x0 , syn_abstract x0) x
  | xsumₛ 𝔄l => λ '(x, padding) , (psum_map1 (λ _ x0, syn_abstract x0) x, padding)
  | at_locₛ 𝔄₀  => λ x , (fst x, @syn_abstract 𝔄₀ (snd x))
  | invₛ 𝔄₀  => λ x , (fst (fst x), snd (fst x), @syn_abstract 𝔄₀ (snd x))
  | local_invₛ 𝔄₀  => λ x , (fst (fst x), @syn_abstract 𝔄₀ (snd x))
  | uniq_borₛ 𝔄₀  => λ x ,
      (match x with (l, x₀, ξi, d', g', idx) => (l, @syn_abstract 𝔄₀ x₀, ξi) end)
  | blockedₛ 𝔄₀ => λ '(x₀, ξi, ζi) , ()
  | ghostₛ 𝔄₀ => λ x , @syn_abstract 𝔄₀ x
  | trackedₛ 𝔄₀ => λ x , @syn_abstract 𝔄₀ x
  | storableₛ 𝔄₀ => λ x , (@syn_abstract 𝔄₀ x.1.1, x.1.2, x.2)
  | uninitₛ n => λ x , x
  | pcellₛ _ => λ x , x
  | paddingₛ => λ x , x
  | funₛ 𝔄₀ 𝔄₁ => λ x , x
  | join_handleₛ 𝔄₀  => λ x , @syn_abstract 𝔄₀ x
  | exec_funₛ 𝔄₀  => λ x  , (fst x, @syn_abstract 𝔄₀ (snd x))
  | maskₛ => λ x , x
  | namespaceₛ => λ x , x
  end.

Lemma syn_abstract_phys_eq 𝔄 x x' :
  @syn_abstract 𝔄 x = @syn_abstract 𝔄 x' → (@syn_phys 𝔄 x = @syn_phys 𝔄 x').
Proof.
  move: 𝔄 x x'. fix FIX 1. move=> 𝔄 x x' Hab. destruct 𝔄;
    try (clear FIX; done);
    try (clear FIX; simpl in Hab; subst; done).
  - simpl in Hab. inversion Hab as [[Ha Hb]]. destruct x, x'. simpl.
    rewrite (FIX _ _ _ Ha). rewrite (FIX _ _ _ Hb). clear FIX; trivial.
  - induction l; first by (clear FIX; trivial). destruct x as [x xl]. destruct x' as [x' xl'].
    simpl. inversion Hab. f_equal.
      * apply FIX. clear FIX. trivial.
      * apply IHl. clear FIX. trivial.
  - assert (∀ (i: fin (length l)) (x1 x2 : ~~ (l !!ₗ i)),
        syn_abstract x1 = syn_abstract x2 → syn_phys x1 = syn_phys x2
    ) as Hall.
    { 
       clear Hab. clear x. clear x'. induction l as [|𝔄0 𝔄l].
        - clear FIX. intros i. inversion i.
        - intros i. dependent destruction i. + apply FIX. + apply IH𝔄l.
    } 
    clear FIX.
    destruct x as [x padding]. destruct x' as [x' padding'].
    simpl. simpl in Hab. inversion Hab as [[Ha Hb]]. subst padding'.
    replace x with (of_xsum (to_xsum x)) in Ha; last by rewrite semi_iso'.
    replace x' with (of_xsum (to_xsum x')) in Ha; last by rewrite semi_iso'.
    replace x with (of_xsum (to_xsum x)); last by rewrite semi_iso'.
    replace x' with (of_xsum (to_xsum x')); last by rewrite semi_iso'.
    destruct (to_xsum x). destruct (to_xsum x'). simpl in Ha.
    do 2 (rewrite psum_map1_pinj in Ha). 
    destruct (pinj_inj _ _ _ _ Ha) as [Hb Hc]. subst i1.
    have Hd := JMeq_eq Hc.
    have He := Hall _ _ _ Hd.
    simpl. do 2 (rewrite psum_map1_pinj). do 2 (rewrite to_xsum_pinj).
    rewrite He. trivial.
  - inversion Hab as [[Ha Hb]]. simpl. rewrite Ha. clear FIX. trivial.
  - destruct x as [[[[[[? ?] ?] ?] ?] ?] ?].
    destruct x' as [[[[[[? ?] ?] ?] ?] ?] ?].
    inversion Hab as [[Ha Hb]]. clear FIX. trivial.
  - inversion Hab as [[Ha Hb]]. simpl. rewrite Ha. clear FIX. trivial.
Qed.

(** * MiniRust types and values of syntactic types

The MiniRust type [syn_mty 𝔄] (see [lang/minirust.v]) of a syntactic type, and the
MiniRust value [syn_val x] (if any) of [x : ~~𝔄]. Like [size_of] and [syn_phys], they
are determined by the syntactic type: every semantic type [ty : type 𝔄] has
[ty_mty ty = syn_mty 𝔄] and [ty_val ty = syn_val] (see [typing/type.v]). They are
shallow: a pointer is [MPtr] whatever its pointee.

Layouts (sizes are abstract and there is no alignment yet):
- [intₛ it] is [MInt it], [boolₛ] is [MBool], and the pointer-like types ([locₛ],
  [at_locₛ], [uniq_borₛ], [exec_funₛ]) are [MPtr];
- a product is a tuple whose fields are laid out one after the other ([seq_tuple]);
- [Σ! 𝔄l] is an enum with a tag of type [enum_tag (length 𝔄l)] at offset 0 and the
  data of each variant right after the tag ([seq_enum]); the legacy padding component
  of [~~(Σ! 𝔄l)] is ignored;
- [uninitₛ n] is [n] bytes of padding ([MTuple [] n]);
- a cell [pcellₛ m] (a multi-byte cell, whose value [~~(pcellₛ m)] is its group, see
  [lang/heap_cells.v]) is its content's MiniRust type [m], if [m] is well formed (and
  zero-sized otherwise, so that [syn_mty_wf] holds);
- every other syntactic type is zero-sized ([zst_mty]).

[syn_val x] is [None] for the values that have no MiniRust representation: integers
out of the range of their [IntType], closures ([exec_funₛ]) and cells
([pcellₛ]); so is a product or sum with such a component. *)

Fixpoint layout_fields (o : nat) (ms : list mty) : list (nat * mty) :=
  match ms with [] => [] | m :: ms => (o, m) :: layout_fields (o + mty_size m) ms end.
Definition seq_size (ms : list mty) : nat := list_sum (mty_size <$> ms).
Definition seq_tuple (ms : list mty) : mty := MTuple (layout_fields 0 ms) (seq_size ms).

(** A one-byte tag for up to 256 variants. *)
Definition enum_tag (n : nat) : IntType :=
  IntTy false (if decide (n ≤ 256)%nat then 1 else n).
Definition seq_enum (ms : list mty) : mty :=
  MEnum ms (enum_tag (length ms))
    (int_size (enum_tag (length ms)) + list_max (mty_size <$> ms)).

Definition zst_mty : mty := MTuple [] 0.

Fixpoint syn_mty (𝔄: syn_type) : mty :=
  match 𝔄 with
  | intₛ it => MInt it
  | boolₛ => MBool
  | locₛ | at_locₛ _ | uniq_borₛ _ | exec_funₛ _ => MPtr
  | prodₛ 𝔄₀ 𝔄₁ => seq_tuple [syn_mty 𝔄₀; syn_mty 𝔄₁]
  | xprodₛ 𝔄l => seq_tuple (syn_mty <$> 𝔄l)
  | xsumₛ 𝔄l => seq_enum (syn_mty <$> 𝔄l)
  | uninitₛ n => MTuple [] n
  | pcellₛ m => if decide (mty_wf m) then m else zst_mty
  | _ => zst_mty
  end.

Fixpoint syn_val {𝔄} : ~~𝔄 → option Value :=
  match 𝔄 return ~~𝔄 → option Value with
  | intₛ it => λ z, if decide (int_in_range it z) then Some (VInt z) else None
  | boolₛ => λ b, Some (VBool b)
  | locₛ => λ l, Some (VPtr l)
  | at_locₛ _ => λ x, Some (VPtr x.1)
  | uniq_borₛ _ => λ x, match x with (l, _, _, _, _, _) => Some (VPtr l) end
  | exec_funₛ _ => λ _, None
  | pcellₛ _ => λ _, None
  | prodₛ 𝔄₀ 𝔄₁ => λ '(x₀, x₁),
      v₀ ← @syn_val 𝔄₀ x₀; v₁ ← @syn_val 𝔄₁ x₁; Some (VTuple [v₀; v₁])
  | xprodₛ 𝔄l => λ x, VTuple <$> mapM id (plist_to_list (pmap (λ _ x0, syn_val x0) x))
  | xsumₛ 𝔄l => λ '(x, _),
      match to_xsum (psum_map1 (λ _ x0, syn_val x0) x) return option Value with
        xinj i ov => VVariant (Z.of_nat (fin_to_nat i)) <$> ov
      end
  | _ => λ _, Some (VTuple [])
  end.

(** [syn_fval x] is the fancy value of [x] (see [lang/fvalue.v]): its MiniRust value,
    where a cell is its group. So [syn_fval (x: ~~(pcellₛ m)) = Some (FVCell x)]; it is
    structural on products and sums (as [syn_val]); on every other type it is
    [fv_lift <$> syn_val x]. It agrees with [syn_val] on the types without cells
    ([syn_fval_nocell]). *)
Fixpoint syn_fval {𝔄} : ~~𝔄 → option FValue :=
  match 𝔄 return ~~𝔄 → option FValue with
  | pcellₛ _ => λ g, Some (FVCell g)
  | prodₛ 𝔄₀ 𝔄₁ => λ '(x₀, x₁),
      fv₀ ← @syn_fval 𝔄₀ x₀; fv₁ ← @syn_fval 𝔄₁ x₁; Some (FVTuple [fv₀; fv₁])
  | xprodₛ 𝔄l => λ x, FVTuple <$> mapM id (plist_to_list (pmap (λ _ x0, syn_fval x0) x))
  | xsumₛ 𝔄l => λ '(x, _),
      match to_xsum (psum_map1 (λ _ x0, syn_fval x0) x) return option FValue with
        xinj i ofv => FVVariant (Z.of_nat (fin_to_nat i)) <$> ofv
      end
  | 𝔄 => λ x, fv_lift <$> @syn_val 𝔄 x
  end.

(** The syntactic types whose values embed no cells ([pcellₛ]): those with no
    [pcellₛ] in a product or sum component. (A cell under another type constructor, e.g.
    [ghostₛ (pcellₛ m)], is not part of the MiniRust value.) *)
Fixpoint syn_nocell (𝔄: syn_type) : bool :=
  match 𝔄 with
  | pcellₛ _ => false
  | prodₛ 𝔄₀ 𝔄₁ => syn_nocell 𝔄₀ && syn_nocell 𝔄₁
  | xprodₛ 𝔄l | xsumₛ 𝔄l => forallb syn_nocell 𝔄l
  | _ => true
  end.

(** The size in bytes of a syntactic type. (The legacy [size_of] counts words.) *)
Definition syn_bsize (𝔄: syn_type) : nat := mty_size (syn_mty 𝔄).

(** ** Layout lemmas *)

Lemma layout_fields_snd o ms : (layout_fields o ms).*2 = ms.
Proof. revert o. induction ms as [|m ms IH]; intros o; [done|]. simpl. f_equal. apply IH. Qed.

Lemma seq_size_cons m ms : seq_size (m :: ms) = (mty_size m + seq_size ms)%nat.
Proof. done. Qed.

Lemma seq_size_nil : seq_size [] = 0%nat.
Proof. done. Qed.
Lemma mty_size_seq_tuple ms : mty_size (seq_tuple ms) = seq_size ms.
Proof. done. Qed.

Lemma layout_fields_bounds o ms :
  Forall (λ f, o ≤ f.1 ∧ f.1 + mty_size f.2 ≤ o + seq_size ms)%nat (layout_fields o ms).
Proof.
  revert o. induction ms as [|m ms IH]; intros o; constructor; rewrite ?seq_size_cons /=; [lia|].
  eapply Forall_impl; [apply IH|]. intros [o' m'] ?. simpl in *. lia.
Qed.

Lemma layout_fields_disjoint o ms : fields_disjoint (layout_fields o ms).
Proof.
  revert o. induction ms as [|m ms IH]; intros o i j o1 m1 o2 m2 Hij Hi Hj; [done|].
  have Hb := layout_fields_bounds (o + mty_size m) ms. rewrite Forall_lookup in Hb.
  destruct i as [|i], j as [|j]; simplify_eq/=.
  all: first [ left; by destruct (Hb _ _ Hj) | right; by destruct (Hb _ _ Hi)
             | apply (IH (o + mty_size m) i j o1 m1 o2 m2); [congruence|done..] ].
Qed.

Lemma layout_fields_wf o ms : Forall mty_wf ms → Forall (λ f, mty_wf f.2) (layout_fields o ms).
Proof.
  intros Hms. revert o. induction Hms as [|m ms ?? IH]; intros o; constructor; [done|]. apply IH.
Qed.

Lemma seq_tuple_wf ms : Forall mty_wf ms → mty_wf (seq_tuple ms).
Proof.
  intros. constructor; [apply layout_fields_disjoint| |by apply layout_fields_wf].
  eapply Forall_impl; [apply (layout_fields_bounds 0)|]. simpl. lia.
Qed.

Lemma Forall2_layout_fields {A} (P : mty → A → Prop) o ms xs :
  Forall2 (λ f x, P f.2 x) (layout_fields o ms) xs ↔ Forall2 P ms xs.
Proof.
  revert o xs. induction ms as [|m ms IH]; intros o [|x xs]; simpl;
    rewrite ?Forall2_cons ?IH; split; inversion 1; by constructor.
Qed.

Lemma list_max_lookup (ns : list nat) i n : ns !! i = Some n → (n ≤ list_max ns)%nat.
Proof.
  intros Hi. have [Hle _] := list_max_le ns (list_max ns).
  have := Hle (le_n _). rewrite Forall_lookup. intros H. by apply (H i).
Qed.

Lemma seq_enum_wf ms : Forall mty_wf ms → mty_wf (seq_enum ms).
Proof.
  intros Hms. constructor; [|lia]. rewrite Forall_lookup in Hms. apply Forall_lookup.
  intros i m Hi. split; [|by eapply Hms].
  pose proof (list_max_lookup (mty_size <$> ms) i (mty_size m)) as Hn.
  rewrite list_lookup_fmap Hi in Hn. have := Hn eq_refl. lia.
Qed.

Lemma enum_tag_in_range n i : (i < n)%nat → int_in_range (enum_tag n) (Z.of_nat i).
Proof.
  intros Hi. rewrite /int_in_range /int_modulus /=. case_decide.
  - rewrite Z.pow_1_r. lia.
  - split; [lia|]. have := Z.pow_gt_lin_r 256 (Z.of_nat n). lia.
Qed.

Lemma llookup_lookup {A} (xl : list A) (i : fin (length xl)) : xl !! fin_to_nat i = Some (xl !!ₗ i).
Proof.
  induction xl as [|x xl IH]; [inv_fin i|]. inv_fin i; [done|]. intros i. apply IH.
Qed.

Lemma syn_mty_wf 𝔄 : mty_wf (syn_mty 𝔄).
Proof.
  move: 𝔄. fix FIX 1. move=> 𝔄. destruct 𝔄; simpl;
    try (clear FIX; by repeat constructor).
  - apply seq_tuple_wf. constructor; [apply FIX|]. constructor; [apply FIX|]. constructor.
  - apply seq_tuple_wf. induction l as [|𝔄 l IH]; constructor; [apply FIX|apply IH].
  - apply seq_enum_wf. induction l as [|𝔄 l IH]; constructor; [apply FIX|apply IH].
  - clear FIX. case_decide; [done|by repeat constructor].
Qed.

Lemma syn_val_wf 𝔄 (x: ~~𝔄) v : syn_val x = Some v → val_wf (syn_mty 𝔄) v.
Proof.
  move: 𝔄 x v. fix FIX 1. move=> 𝔄 x v. destruct 𝔄; simpl;
    try (clear FIX; intros; simplify_eq; by repeat constructor).
  - clear FIX. case_decide; intros; simplify_eq. by constructor.
  - destruct x as [x₀ x₁].
    destruct (syn_val x₀) as [v₀|] eqn:H₀; [|done]. destruct (syn_val x₁) as [v₁|] eqn:H₁; [|done].
    intros [= <-]. constructor. simpl. constructor; [by eapply FIX|].
    constructor; [by eapply FIX|]. constructor.
  - intros (vs&Hvs&->)%fmap_Some_1. constructor. apply Forall2_layout_fields.
    revert x vs Hvs. induction l as [|𝔄 l IH]; [intros []|intros [x xl]]; simpl.
    + intros vs [= <-]. constructor.
    + intros vs. destruct (syn_val x) as [w|] eqn:Hw; [|done]. simpl.
      destruct (mapM _ _) as [ws|] eqn:Hws; [|done]. intros [= <-].
      constructor; [by apply (FIX _ x w Hw)|]. by apply (IH xl).
  - destruct x as [x pad].
    assert (∀ (i: fin (length l)) (x0 : ~~ (l !!ₗ i)) v0,
      syn_val x0 = Some v0 → val_wf (syn_mty (l !!ₗ i)) v0) as Hall.
    { clear x pad v. induction l as [|𝔄0 l IH]; intros i; [inv_fin i|].
      inv_fin i; [apply FIX|apply IH]. }
    clear FIX.
    replace x with (of_xsum (to_xsum x)); last by rewrite semi_iso'.
    destruct (to_xsum x) as [i x0]. simpl. rewrite psum_map1_pinj to_xsum_pinj.
    intros (d&Hd&->)%fmap_Some_1. econstructor; [lia| | |by eapply Hall, Hd].
    + rewrite Nat2Z.id list_lookup_fmap llookup_lookup //.
    + rewrite length_fmap. apply enum_tag_in_range, fin_to_nat_lt.
  - clear FIX. destruct x as [[[[[??]?]?]?]?]. intros; simplify_eq. constructor.
Qed.

Lemma mapM_fmap_fv_lift (ovs : list (option Value)) :
  mapM id (fmap fv_lift <$> ovs) = fmap fv_lift <$> mapM id ovs.
Proof.
  induction ovs as [|[v|] ovs IH]; [done| |done]. simpl. rewrite IH.
  by destruct (mapM id ovs).
Qed.

Lemma syn_fval_nocell 𝔄 (x: ~~𝔄) : syn_nocell 𝔄 → syn_fval x = fv_lift <$> syn_val x.
Proof.
  move: 𝔄 x. fix FIX 1. move=> 𝔄 x. destruct 𝔄; simpl; try (clear FIX; done).
  - move=> /andb_True[H₀ H₁]. destruct x as [x₀ x₁]. rewrite (FIX _ x₀ H₀) (FIX _ x₁ H₁).
    clear FIX. by destruct (syn_val x₀), (syn_val x₁).
  - move=> Hl. rewrite -option_fmap_compose.
    assert (plist_to_list (pmap (λ _ x0, syn_fval x0) x) =
      fmap fv_lift <$> plist_to_list (pmap (λ _ x0, syn_val x0) x)) as ->.
    { induction l as [|𝔄 l IH]; [done|]. destruct x as [x xl].
      move: Hl=> /= /andb_True[H Hl]. by rewrite (FIX _ x H) (IH xl Hl). }
    clear FIX. rewrite mapM_fmap_fv_lift -option_fmap_compose. done.
  - destruct x as [x pad]. move=> Hl.
    assert (∀ (i: fin (length l)) (x0 : ~~ (l !!ₗ i)),
      syn_fval x0 = fv_lift <$> syn_val x0) as Hall.
    { clear x pad. induction l as [|𝔄0 l IH]; intros i; [inv_fin i|].
      move: Hl=> /= /andb_True[H Hl]. inv_fin i; [intros x0; by apply (FIX _ x0)|by apply IH]. }
    clear FIX.
    replace x with (of_xsum (to_xsum x)); last by rewrite semi_iso'.
    destruct (to_xsum x) as [i x0]. simpl. rewrite !psum_map1_pinj !to_xsum_pinj Hall.
    by destruct (syn_val x0).
Qed.

(** ** Decoding tuples laid out by [seq_tuple] *)
Section decode_seq.
  Implicit Types bs : list (AbstractByte).

  Fixpoint decode_seq (ms : list mty) bs : option (list Value) :=
    match ms with
    | [] => Some []
    | m :: ms =>
        v ← decode_value m (take (mty_size m) bs);
        vs ← decode_seq ms (drop (mty_size m) bs); Some (v :: vs)
    end.

  Lemma decode_seq_tuple ms bs :
    decode_value (seq_tuple ms) bs =
    if decide (length bs = seq_size ms) then VTuple <$> decode_seq ms bs else None.
  Proof.
    rewrite /seq_tuple decode_value_tuple. case_decide as Hlen; [|done]. f_equal. clear Hlen.
    rewrite -{2}(drop_0 bs). generalize 0%nat as o. induction ms as [|m ms IH]; intros o; [done|].
    simpl. rewrite IH drop_drop. done.
  Qed.

  Lemma decode_zst bs : decode_value zst_mty bs = if decide (bs = []) then Some (VTuple []) else None.
  Proof.
    rewrite /zst_mty decode_value_tuple.
    destruct bs; simpl; [done|]. done.
  Qed.

  Lemma decode_value_length_None m bs :
    length bs ≠ mty_size m → decode_value m bs = None.
  Proof.
    intros Hlen. destruct (decode_value m bs) eqn:Hd; [|done].
    by apply decode_value_length in Hd.
  Qed.
End decode_seq.

Lemma fmap_eq_iff {A B} (f : A → B) `{!Inj (=) (=) f} (o1 o2 : option A) :
  f <$> o1 = f <$> o2 ↔ o1 = o2.
Proof. destruct o1, o2; simpl; split; intros; simplify_eq; done. Qed.

(** The layout of [() * 𝔄], [𝔄 * ()] and [𝔄 * Π! 𝔅l] (for the isomorphisms below). *)
Lemma decode_prod_unit_l m (bs : list (AbstractByte)) :
  decode_value (seq_tuple [zst_mty; m]) bs = (λ v, VTuple [VTuple []; v]) <$> decode_value m bs.
Proof.
  rewrite decode_seq_tuple /seq_size /=. rewrite drop_0.
  case_decide.
  - rewrite take_ge; [|lia]. by destruct (decode_value m bs).
  - rewrite decode_value_length_None //. lia.
Qed.

Lemma decode_prod_unit_r m (bs : list (AbstractByte)) :
  decode_value (seq_tuple [m; zst_mty]) bs = (λ v, VTuple [v; VTuple []]) <$> decode_value m bs.
Proof.
  rewrite decode_seq_tuple /seq_size /=. case_decide.
  - rewrite take_ge; [|lia]. by destruct (decode_value m bs).
  - rewrite decode_value_length_None //. lia.
Qed.

Lemma decode_prod_cons m ms (bs : list (AbstractByte)) :
  decode_value (seq_tuple [m; seq_tuple ms]) bs =
  (λ v, match v with VTuple (v :: vs) => VTuple [v; VTuple vs] | _ => v end) <$>
    decode_value (seq_tuple (m :: ms)) bs.
Proof.
  rewrite !decode_seq_tuple !seq_size_cons seq_size_nil mty_size_seq_tuple.
  destruct (decide (length bs = _)) as [H1|H1];
    destruct (decide (length bs = _)) as [H2|H2]; try lia; [|done].
  rewrite /decode_seq -/decode_seq mty_size_seq_tuple.
  rewrite (decode_seq_tuple ms) length_take length_drop decide_True; [|lia].
  rewrite (take_ge (drop _ _)); [|rewrite length_drop; lia].
  destruct (decode_value m _); [|done]. simpl.
  by destruct (decode_seq ms _).
Qed.

(** Three-way binds, for the associativity of products. *)
Definition bind3 {A} (f : A → A → A → A) (o1 o2 o3 : option A) : option A :=
  a ← o1; b ← o2; c ← o3; Some (f a b c).

Lemma bind3_iff {A} (f g : A → A → A → A) o1 o2 o3 p1 p2 p3 :
  (∀ a b c a' b' c', f a b c = f a' b' c' → a = a' ∧ b = b' ∧ c = c') →
  (∀ a b c a' b' c', g a b c = g a' b' c' → a = a' ∧ b = b' ∧ c = c') →
  bind3 f o1 o2 o3 = bind3 f p1 p2 p3 ↔ bind3 g o1 o2 o3 = bind3 g p1 p2 p3.
Proof.
  intros Hf Hg. rewrite /bind3.
  destruct o1, o2, o3, p1, p2, p3; simpl; split; intros H; simplify_eq; try done;
    [apply Hf in H|apply Hg in H]; destruct H as (->&->&->); done.
Qed.

Lemma bind3_None {A} (f g : A → A → A → A) o1 o2 o3 :
  None = bind3 f o1 o2 o3 ↔ None = bind3 g o1 o2 o3.
Proof. rewrite /bind3. destruct o1, o2, o3; simpl; split; done. Qed.

Lemma decode_assoc_l a b c (bs : list (AbstractByte)) :
  decode_value (seq_tuple [a; seq_tuple [b; c]]) bs =
  if decide (length bs = mty_size a + mty_size b + mty_size c)%nat then
    bind3 (λ x y z, VTuple [x; VTuple [y; z]])
      (decode_value a (take (mty_size a) bs))
      (decode_value b (take (mty_size b) (drop (mty_size a) bs)))
      (decode_value c (take (mty_size c) (drop (mty_size a + mty_size b) bs)))
  else None.
Proof.
  rewrite decode_seq_tuple ?seq_size_cons ?mty_size_seq_tuple ?seq_size_cons ?seq_size_nil.
  destruct (decide (length bs = _)) as [H1|H1];
    destruct (decide (length bs = _)) as [H2|H2]; try lia; [|done].
  rewrite /decode_seq -/decode_seq ?mty_size_seq_tuple ?seq_size_cons ?seq_size_nil.
  rewrite (decode_seq_tuple [b; c]) length_take length_drop decide_True; [|rewrite ?seq_size_cons ?seq_size_nil; lia].
  rewrite (take_ge (drop _ _)); [|rewrite length_drop ?seq_size_cons ?seq_size_nil; lia].
  rewrite /decode_seq !drop_drop /bind3.
  destruct (decode_value a _); [|done]. simpl. destruct (decode_value b _); [|done]. simpl.
  by destruct (decode_value c _).
Qed.

Lemma decode_assoc_r a b c (bs : list (AbstractByte)) :
  decode_value (seq_tuple [seq_tuple [a; b]; c]) bs =
  if decide (length bs = mty_size a + mty_size b + mty_size c)%nat then
    bind3 (λ x y z, VTuple [VTuple [x; y]; z])
      (decode_value a (take (mty_size a) bs))
      (decode_value b (take (mty_size b) (drop (mty_size a) bs)))
      (decode_value c (take (mty_size c) (drop (mty_size a + mty_size b) bs)))
  else None.
Proof.
  rewrite decode_seq_tuple ?seq_size_cons ?mty_size_seq_tuple ?seq_size_cons ?seq_size_nil.
  destruct (decide (length bs = _)) as [H1|H1];
    destruct (decide (length bs = _)) as [H2|H2]; try lia; [|done].
  rewrite /decode_seq -/decode_seq ?mty_size_seq_tuple ?seq_size_cons ?seq_size_nil.
  rewrite (decode_seq_tuple [a; b]) length_take decide_True; [|rewrite ?seq_size_cons ?seq_size_nil; lia].
  rewrite /decode_seq /bind3 !Nat.add_0_r -(take_drop_commute bs (mty_size b) (mty_size a)).
  rewrite !take_take Nat.min_id (_: (mty_size a `min` (mty_size a + mty_size b) = mty_size a)%nat); [|lia].
  destruct (decode_value a _); [|done]. simpl. destruct (decode_value b _); [|done]. simpl.
  by destruct (decode_value c _).
Qed.

(** The byte laws of the associativity of products. *)
Lemma prod_assoc_bsize 𝔄 𝔅 ℭ : syn_bsize (𝔄 * (𝔅 * ℭ)) = syn_bsize (𝔄 * 𝔅 * ℭ).
Proof.
  change (seq_size [syn_mty 𝔄; seq_tuple [syn_mty 𝔅; syn_mty ℭ]] =
    seq_size [seq_tuple [syn_mty 𝔄; syn_mty 𝔅]; syn_mty ℭ]).
  rewrite !seq_size_cons !mty_size_seq_tuple !seq_size_cons !seq_size_nil. lia.
Qed.

Lemma prod_assoc_bytes 𝔄 𝔅 ℭ (x: ~~(𝔄 * (𝔅 * ℭ))) (bs: list abyte) :
  decode_value (syn_mty (𝔄 * (𝔅 * ℭ))) bs = syn_val x ↔
  decode_value (syn_mty (𝔄 * 𝔅 * ℭ)) bs = @syn_val (𝔄 * 𝔅 * ℭ) (prod_assoc x).
Proof.
  destruct x as [x [y z]].
  change (decode_value (seq_tuple [syn_mty 𝔄; seq_tuple [syn_mty 𝔅; syn_mty ℭ]]) bs =
      (v₀ ← syn_val x; v₁ ← (v₀ ← syn_val y; v₁ ← syn_val z; Some (VTuple [v₀; v₁]));
       Some (VTuple [v₀; v₁])) ↔
    decode_value (seq_tuple [seq_tuple [syn_mty 𝔄; syn_mty 𝔅]; syn_mty ℭ]) bs =
      (v₀ ← (v₀ ← syn_val x; v₁ ← syn_val y; Some (VTuple [v₀; v₁])); v₁ ← syn_val z;
       Some (VTuple [v₀; v₁]))).
  rewrite (_: (v₀ ← syn_val x; v₁ ← (v₀ ← syn_val y; v₁ ← syn_val z; Some (VTuple [v₀; v₁]));
       Some (VTuple [v₀; v₁])) =
    bind3 (λ x y z, VTuple [x; VTuple [y; z]]) (syn_val x) (syn_val y) (syn_val z)); last first.
  { rewrite /bind3. destruct (syn_val x), (syn_val y), (syn_val z); done. }
  rewrite (_: (v₀ ← (v₀ ← syn_val x; v₁ ← syn_val y; Some (VTuple [v₀; v₁])); v₁ ← syn_val z;
       Some (VTuple [v₀; v₁])) =
    bind3 (λ x y z, VTuple [VTuple [x; y]; z]) (syn_val x) (syn_val y) (syn_val z)); last first.
  { rewrite /bind3. destruct (syn_val x), (syn_val y), (syn_val z); done. }
  rewrite (decode_assoc_l ) (decode_assoc_r ). case_decide.
  - apply bind3_iff; intros; by simplify_eq.
  - apply bind3_None.
Qed.

(** [n + m] bytes of padding are a pair of [n] and [m] bytes of padding. *)
Lemma decode_pad n (bs : list (AbstractByte)) :
  decode_value (MTuple [] n) bs = if decide (length bs = n) then Some (VTuple []) else None.
Proof. rewrite decode_value_tuple. by case_decide. Qed.

Lemma decode_pad_pair n m (bs : list (AbstractByte)) :
  decode_value (seq_tuple [MTuple [] n; MTuple [] m]) bs =
  if decide (length bs = n + m)%nat then Some (VTuple [VTuple []; VTuple []]) else None.
Proof.
  rewrite decode_seq_tuple !seq_size_cons seq_size_nil /=.
  destruct (decide (length bs = _)) as [H1|H1];
    destruct (decide (length bs = _)) as [H2|H2]; try lia; [|done].
  rewrite length_take length_drop length_take. rewrite !decide_True //; lia.
Qed.

(** The MiniRust value only depends on the abstracted value (as [syn_phys], see
    [syn_abstract_phys_eq]); this is what the [Send] arguments need. *)
Lemma syn_abstract_val_eq 𝔄 x x' :
  @syn_abstract 𝔄 x = @syn_abstract 𝔄 x' → (@syn_val 𝔄 x = @syn_val 𝔄 x').
Proof.
  move: 𝔄 x x'. fix FIX 1. move=> 𝔄 x x' Hab. destruct 𝔄;
    try (clear FIX; done);
    try (clear FIX; simpl in Hab; subst; done).
  - simpl in Hab. inversion Hab as [[Ha Hb]]. destruct x, x'. simpl.
    rewrite (FIX _ _ _ Ha). rewrite (FIX _ _ _ Hb). clear FIX; trivial.
  - simpl. f_equal. f_equal. induction l; first by (clear FIX; destruct x, x'; trivial).
    destruct x as [x xl]. destruct x' as [x' xl'].
    simpl. inversion Hab. f_equal.
      * apply FIX. clear FIX. trivial.
      * apply IHl. clear FIX. trivial.
  - assert (∀ (i: fin (length l)) (x1 x2 : ~~ (l !!ₗ i)),
        syn_abstract x1 = syn_abstract x2 → syn_val x1 = syn_val x2
    ) as Hall.
    {
       clear Hab. clear x. clear x'. induction l as [|𝔄0 𝔄l].
        - clear FIX. intros i. inversion i.
        - intros i. dependent destruction i. + apply FIX. + apply IH𝔄l.
    }
    clear FIX.
    destruct x as [x padding]. destruct x' as [x' padding'].
    simpl. simpl in Hab. inversion Hab as [[Ha Hb]]. subst padding'.
    replace x with (of_xsum (to_xsum x)) in Ha; last by rewrite semi_iso'.
    replace x' with (of_xsum (to_xsum x')) in Ha; last by rewrite semi_iso'.
    replace x with (of_xsum (to_xsum x)); last by rewrite semi_iso'.
    replace x' with (of_xsum (to_xsum x')); last by rewrite semi_iso'.
    destruct (to_xsum x). destruct (to_xsum x'). simpl in Ha.
    do 2 (rewrite psum_map1_pinj in Ha).
    destruct (pinj_inj _ _ _ _ Ha) as [Hb Hc]. subst i1.
    have Hd := JMeq_eq Hc.
    have He := Hall _ _ _ Hd.
    simpl. do 2 (rewrite psum_map1_pinj). do 2 (rewrite to_xsum_pinj).
    rewrite He. trivial.
  - inversion Hab as [[Ha Hb]]. simpl. rewrite Ha. clear FIX. trivial.
  - destruct x as [[[[[[? ?] ?] ?] ?] ?] ?].
    destruct x' as [[[[[[? ?] ?] ?] ?] ?] ?].
    inversion Hab as [[Ha Hb]]. clear FIX. simpl. by subst.
Qed.

(** So does the fancy value. *)
Lemma syn_abstract_fval_eq 𝔄 x x' :
  @syn_abstract 𝔄 x = @syn_abstract 𝔄 x' → (@syn_fval 𝔄 x = @syn_fval 𝔄 x').
Proof.
  move: 𝔄 x x'. fix FIX 1. move=> 𝔄 x x' Hab. destruct 𝔄;
    try (clear FIX; match goal with |- @syn_fval ?A _ = _ =>
      change (fv_lift <$> @syn_val A x = fv_lift <$> @syn_val A x') end;
      by rewrite (syn_abstract_val_eq _ _ _ Hab)).
  - simpl in Hab. inversion Hab as [[Ha Hb]]. destruct x, x'. simpl.
    rewrite (FIX _ _ _ Ha). rewrite (FIX _ _ _ Hb). clear FIX; trivial.
  - simpl. f_equal. f_equal. induction l; first by (clear FIX; destruct x, x'; trivial).
    destruct x as [x xl]. destruct x' as [x' xl'].
    simpl. inversion Hab. f_equal.
      * apply FIX. clear FIX. trivial.
      * apply IHl. clear FIX. trivial.
  - assert (∀ (i: fin (length l)) (x1 x2 : ~~ (l !!ₗ i)),
        syn_abstract x1 = syn_abstract x2 → syn_fval x1 = syn_fval x2
    ) as Hall.
    {
       clear Hab. clear x. clear x'. induction l as [|𝔄0 𝔄l].
        - clear FIX. intros i. inversion i.
        - intros i. dependent destruction i. + apply FIX. + apply IH𝔄l.
    }
    clear FIX.
    destruct x as [x padding]. destruct x' as [x' padding'].
    simpl. simpl in Hab. inversion Hab as [[Ha Hb]]. subst padding'.
    replace x with (of_xsum (to_xsum x)) in Ha; last by rewrite semi_iso'.
    replace x' with (of_xsum (to_xsum x')) in Ha; last by rewrite semi_iso'.
    replace x with (of_xsum (to_xsum x)); last by rewrite semi_iso'.
    replace x' with (of_xsum (to_xsum x')); last by rewrite semi_iso'.
    destruct (to_xsum x). destruct (to_xsum x'). simpl in Ha.
    do 2 (rewrite psum_map1_pinj in Ha).
    destruct (pinj_inj _ _ _ _ Ha) as [Hb Hc]. subst i1.
    have Hd := JMeq_eq Hc.
    have He := Hall _ _ _ Hd.
    simpl. do 2 (rewrite psum_map1_pinj). do 2 (rewrite to_xsum_pinj).
    rewrite He. trivial.
  - clear FIX. simpl in Hab. by subst.
Qed.

Record syn_type_morphism (𝔄 𝔅 : syn_type) := {
    syn_type_morphism_fn : ~~𝔄 → ~~𝔅;
    syn_type_morphism_proph_fn : 𝔄 → 𝔅;
    syn_type_morphism_commutes : ∀ x π ,
        syn_type_morphism_proph_fn (@vπ 𝔄 x π) = @vπ 𝔅 (syn_type_morphism_fn x) π;
    syn_type_morphism_ξl : ∀ x , @ξl 𝔄 x = @ξl 𝔅 (syn_type_morphism_fn x);
}. 

Arguments syn_type_morphism_fn {_ _} _ _.
Arguments syn_type_morphism_proph_fn {_ _} _ _.

Infix "→ₛ" := (syn_type_morphism) (at level 50).
Infix "$ₛ" := (syn_type_morphism_proph_fn) (at level 50).
Infix "~~$ₛ" := (syn_type_morphism_fn) (at level 50).

Notation "!ₛ" := (syn_type_morphism_proph_fn) (at level 50).
Notation "~~!ₛ" := (syn_type_morphism_fn) (at level 50).

Program Definition idₛ {𝔄} : 𝔄 →ₛ 𝔄 := {|
  syn_type_morphism_fn := id;
  syn_type_morphism_proph_fn := id;
|}.
Next Obligation. done. Qed.
Next Obligation. done. Qed.

Program Definition composeₛ {𝔄 𝔅 ℭ} (g : 𝔅 →ₛ ℭ) (f : 𝔄 →ₛ 𝔅) : (𝔄 →ₛ ℭ) := {|
  syn_type_morphism_fn := (syn_type_morphism_fn g) ∘ (syn_type_morphism_fn f);
  syn_type_morphism_proph_fn := (syn_type_morphism_proph_fn g) ∘ (syn_type_morphism_proph_fn f)
|}.
Next Obligation.
  intros 𝔄 𝔅 ℭ f g x π. simpl.
  rewrite syn_type_morphism_commutes.
  rewrite syn_type_morphism_commutes. trivial.
Qed.
Next Obligation.
  intros. simpl. rewrite (syn_type_morphism_ξl _ _ f). by rewrite (syn_type_morphism_ξl _ _ g).
Qed.

Program Definition prod_mapₛ {𝔄 𝔄' 𝔅 𝔅'} (f : 𝔄 →ₛ 𝔄') (g : 𝔅 →ₛ 𝔅') : (𝔄 * 𝔅 →ₛ 𝔄' * 𝔅') := {|
  syn_type_morphism_fn := prod_map (syn_type_morphism_fn f) (syn_type_morphism_fn g);
  syn_type_morphism_proph_fn := prod_map (syn_type_morphism_proph_fn f) (syn_type_morphism_proph_fn g)
|}.
Next Obligation.
  intros 𝔄 𝔄' 𝔅 𝔅' f g x π. simpl.
  rewrite syn_type_morphism_commutes.
  rewrite syn_type_morphism_commutes. trivial.
Qed.
Next Obligation.
  intros. simpl. rewrite (syn_type_morphism_ξl _ _ f). by rewrite (syn_type_morphism_ξl _ _ g).
Qed.

Program Definition at_loc_mapₛ {𝔄 𝔄'} (f : 𝔄 →ₛ 𝔄') : ((at_locₛ 𝔄) →ₛ (at_locₛ 𝔄')) := {|
  syn_type_morphism_fn :=       λ (x : ~~ (at_locₛ 𝔄)), match x with (l, v) => (l, (~~!ₛ f) v) : (~~ (at_locₛ 𝔄')) end ;
  syn_type_morphism_proph_fn := λ (x : (at_locₛ 𝔄)), match x with (l, v) => (l, (!ₛ f) v) : ((at_locₛ 𝔄')) end ;
|}.
Next Obligation.
  intros 𝔄 𝔄' f x π. simpl.
  rewrite syn_type_morphism_commutes. destruct x. done.
Qed.
Next Obligation.
  intros. simpl. rewrite (syn_type_morphism_ξl _ _ f). destruct x; trivial.
Qed.

Program Definition fst_mapₛ {𝔄 𝔄' 𝔅} (f: 𝔄 →ₛ 𝔄') : (𝔄 * 𝔅) →ₛ (𝔄' * 𝔅) := {|
  syn_type_morphism_fn := λ x , (f ~~$ₛ (x.1), x.2);
  syn_type_morphism_proph_fn := λ x , (f $ₛ (x.1), x.2);
|}.
Next Obligation. intros. simpl. rewrite syn_type_morphism_commutes. done. Qed.
Next Obligation. intros. simpl. by rewrite (syn_type_morphism_ξl _ _ f). Qed.

Program Definition snd_mapₛ {𝔄 𝔄' 𝔅} (f: 𝔄 →ₛ 𝔄') : (𝔅 * 𝔄) →ₛ (𝔅 * 𝔄') := {|
  syn_type_morphism_fn := λ x , (x.1, f ~~$ₛ (x.2));
  syn_type_morphism_proph_fn := λ x , (x.1, f $ₛ (x.2));
|}.
Next Obligation. intros. simpl. rewrite syn_type_morphism_commutes. done. Qed.
Next Obligation. intros. simpl. by rewrite (syn_type_morphism_ξl _ _ f). Qed.

Program Definition tracked_mapₛ {𝔄 𝔄'} (f: 𝔄 →ₛ 𝔄') : (trackedₛ 𝔄 →ₛ trackedₛ 𝔄') := {|
  syn_type_morphism_fn := (λ x, (f ~~$ₛ x)) ;
  syn_type_morphism_proph_fn := (λ x, (f $ₛ x)) ;
|}.
Next Obligation. intros. simpl. by rewrite syn_type_morphism_commutes. Qed.
Next Obligation. intros. simpl. by rewrite <- syn_type_morphism_ξl. Qed.

Program Definition pair_with_locₛ {𝔄} (l: loc) : 𝔄 →ₛ (at_locₛ 𝔄) := {|
  syn_type_morphism_fn := (λ x, (l, x)) ;
  syn_type_morphism_proph_fn := (λ x, (l, x)) ;
|}.
Next Obligation. intros 𝔄 x π. done. Qed.
Next Obligation. intros. done. Qed.

Program Definition pair_with_loc_trackedₛ {𝔄} (l: loc) : 𝔄 →ₛ (trackedₛ (at_locₛ 𝔄)) := {|
  syn_type_morphism_fn := (λ x, (l, x)) ;
  syn_type_morphism_proph_fn := (λ x, (l, x)) ;
|}.
Next Obligation. intros 𝔄 x π. done. Qed.
Next Obligation. intros. done. Qed.

Program Definition prod_assocₛ {𝔄 𝔅 ℭ} : (𝔄 * (𝔅 * ℭ)) →ₛ (𝔄 * 𝔅 * ℭ) := {|
  syn_type_morphism_fn := prod_assoc ;
  syn_type_morphism_proph_fn := prod_assoc ;
|}.
Next Obligation. intros 𝔄 𝔅 ℭ x. destruct x as [x [y z]]. done. Qed.
Next Obligation. intros 𝔄 𝔅 ℭ x. destruct x as [x [y z]]. apply List.app_assoc. Qed.

Program Definition prod_assoc'ₛ {𝔄 𝔅 ℭ} : (𝔄 * 𝔅 * ℭ) →ₛ (𝔄 * (𝔅 * ℭ)) := {|
  syn_type_morphism_fn := prod_assoc' ;
  syn_type_morphism_proph_fn := prod_assoc' ;
|}.
Next Obligation. intros 𝔄 𝔅 ℭ x. destruct x as [[x y] z]. done. Qed.
Next Obligation. intros 𝔄 𝔅 ℭ x. destruct x as [[x y] z]. symmetry. apply List.app_assoc. Qed.

Program Definition to_cons_prodₛ {𝔄 𝔅l} : (𝔄 * Π! 𝔅l) →ₛ (Π! (𝔄 :: 𝔅l)) := {|
  syn_type_morphism_fn := to_cons_prod ;
  syn_type_morphism_proph_fn := to_cons_prod ;
|}.
Next Obligation. intros 𝔄 𝔅l x π. destruct x; trivial. Qed.
Next Obligation. intros 𝔄 𝔅l x. destruct x; trivial. Qed.

Program Definition of_cons_prodₛ {𝔄 𝔅l} : (Π! (𝔄 :: 𝔅l)) →ₛ (𝔄 * Π! 𝔅l) := {|
  syn_type_morphism_fn := of_cons_prod ;
  syn_type_morphism_proph_fn := of_cons_prod ;
|}.
Next Obligation. intros 𝔄 𝔅l x π. destruct x; trivial. Qed.
Next Obligation. intros 𝔄 𝔅l x. destruct x; trivial. Qed.

Program Definition empty_prod_to_unitₛ : (Π! []) →ₛ unitₛ := {|
  syn_type_morphism_fn := const () ;
  syn_type_morphism_proph_fn := const () ;
|}.
Next Obligation. done. Qed.
Next Obligation. done. Qed.

Program Definition empty_prod_of_unitₛ : unitₛ →ₛ (Π! []) := {|
  syn_type_morphism_fn := const -[] ;
  syn_type_morphism_proph_fn := const -[] ;
|}.
Next Obligation. done. Qed.
Next Obligation. done. Qed.

Program Definition cons_prodₛ {𝔄 𝔄l 𝔅 𝔅l} (f: 𝔄 →ₛ 𝔅) (fl: Π! 𝔄l →ₛ Π! 𝔅l)
      : (Π! (𝔄 :: 𝔄l) →ₛ Π! (𝔅 :: 𝔅l)) := {|
    syn_type_morphism_fn := λ '(x -:: xl), (f ~~$ₛ x) -:: (fl ~~$ₛ xl) ;
    syn_type_morphism_proph_fn := λ '(x -:: xl), (f $ₛ x) -:: (fl $ₛ xl) ;
|}.
Next Obligation. 
  intros 𝔄 𝔄l 𝔅 𝔅l f fl [x xl] π. simpl. do 2 rewrite syn_type_morphism_commutes. trivial.
Qed.
Next Obligation. 
  intros 𝔄 𝔄l 𝔅 𝔅l f fl [x xl]. simpl.
    rewrite (syn_type_morphism_ξl _ _ f). by setoid_rewrite (syn_type_morphism_ξl _ _ fl).
Qed.

Fixpoint plist_mapₛ {𝔄l 𝔅l} :
  (plist2 (λ 𝔄 𝔅, 𝔄 →ₛ 𝔅) 𝔄l 𝔅l) → (Π! 𝔄l →ₛ Π! 𝔅l) :=
  match 𝔄l, 𝔅l with
  | [], [] => λ _, idₛ
  | _::_, _::_ => λ '(f -:: fl'), cons_prodₛ f (plist_mapₛ fl')
  | _, _ => absurd
  end.

Lemma extensₛ {𝔄 𝔅} (f: 𝔄 →ₛ 𝔅) (f': 𝔄 →ₛ 𝔅) :
  (!ₛ f) = (!ₛ f') →
  (~~!ₛ f) = (~~!ₛ f') →
  f = f'.
Proof.
  intros Ha Hb. destruct f, f'. simpl in Ha. simpl in Hb. 
  destruct Ha. destruct Hb.
  f_equal; repeat fun_ext_dep=> ?; apply Eqdep.EqdepTheory.UIP.
Qed.

Program Definition prod_left_idₛ {𝔄} : () * 𝔄 →ₛ 𝔄 := {|
  syn_type_morphism_fn := prod_left_id ;
  syn_type_morphism_proph_fn := prod_left_id ;
|}.
Next Obligation. intros 𝔄 [[]x] π. done. Qed.
Next Obligation. intros 𝔄 [[]x]. done. Qed.

Program Definition prod_left_id'ₛ {𝔄} : 𝔄 →ₛ () * 𝔄 := {|
  syn_type_morphism_fn := prod_left_id' ;
  syn_type_morphism_proph_fn := prod_left_id' ;
|}.
Next Obligation. intros 𝔄 x π. done. Qed.
Next Obligation. intros 𝔄 x. done. Qed.

Program Definition prod_right_idₛ {𝔄} : 𝔄 * () →ₛ 𝔄 := {|
  syn_type_morphism_fn := prod_right_id ;
  syn_type_morphism_proph_fn := prod_right_id ;
|}.
Next Obligation. intros 𝔄 [x[]] π. done. Qed.
Next Obligation. intros 𝔄 [x[]]. apply List.app_nil_r. Qed.

Program Definition prod_right_id'ₛ {𝔄} : 𝔄 →ₛ 𝔄 * () := {|
  syn_type_morphism_fn := prod_right_id' ;
  syn_type_morphism_proph_fn := prod_right_id' ;
|}.
Next Obligation. intros 𝔄 x π. done. Qed.
Next Obligation. intros 𝔄 x. simpl. rewrite List.app_nil_r. done. Qed.

Program Definition psum_mapₛ {𝔄l 𝔅l} (fl : plist2 (λ 𝔄 𝔅, 𝔄 →ₛ 𝔅) 𝔄l 𝔅l) : ((xsumₛ 𝔄l) →ₛ (xsumₛ 𝔅l)) := {|
  syn_type_morphism_fn := λ '(x0, padding) , (psum_map (p2map (@syn_type_morphism_fn) fl) x0, padding) ;
  syn_type_morphism_proph_fn := λ '(x0, padding) , (psum_map (p2map (@syn_type_morphism_proph_fn) fl) x0, padding) ;
|}.
Next Obligation. induction 𝔄l; intros 𝔅l fl [x padding] π.
  - destruct 𝔅l; trivial. contradiction.
  - destruct 𝔅l; first by contradiction.
    simpl. simpl in IH𝔄l.
    destruct fl, x; trivial.
    + simpl. rewrite <- syn_type_morphism_commutes. trivial.
    + simpl. simpl in IH𝔄l. have j := IH𝔄l 𝔅l ptl (p, padding) π. simpl in j.
      inversion j as [j1]. rewrite j1. trivial.
Qed.
Next Obligation. induction 𝔄l; intros 𝔅l fl [x padding].
  - destruct 𝔅l; contradiction.
  - destruct 𝔅l; first by contradiction.
    simpl. simpl in IH𝔄l.
    destruct fl, x; trivial.
    + simpl. rewrite <- syn_type_morphism_ξl. trivial.
    + simpl. simpl in IH𝔄l. have j := IH𝔄l 𝔅l ptl (p, padding).
      destruct (to_xsum (psum_map1 (λ (A : syn_type) (x0 : ~~ A), ξl x0) p)).
      destruct (to_xsum (psum_map1 (λ (A : syn_type) (x0 : ~~ A), ξl x0)
           (psum_map (@syn_type_morphism_fn -2<$> ptl) p))).
      apply j.
Qed.

Infix "∘ₛ" := (composeₛ) (at level 50).

(** An isomorphism of syntactic types. Besides the legacy [size_of] and [syn_phys], it
    preserves the byte size and the byte representations: bytes that decode to the
    MiniRust value of [x] at [𝔄] are exactly those that decode to the value of [f x] at
    [𝔅] (the MiniRust types and values themselves may differ, e.g. [() * 𝔄] and [𝔄]). *)
Class Isoₛ {𝔄 𝔅 : syn_type} (f : 𝔄 →ₛ 𝔅) (g : 𝔅 →ₛ 𝔄) := {
    syn_iso : Iso (syn_type_morphism_fn f) (syn_type_morphism_fn g) ;
    syn_iso_proph : Iso (syn_type_morphism_proph_fn f) (syn_type_morphism_proph_fn g) ;
    syn_iso_size_eq : size_of 𝔄 = size_of 𝔅 ;
    syn_iso_phys_eq : ∀ (x: ~~𝔄), @syn_phys 𝔄 x = @syn_phys 𝔅 (syn_type_morphism_fn f x) ;
    syn_iso_bsize_eq : syn_bsize 𝔄 = syn_bsize 𝔅 ;
    syn_iso_bytes : ∀ (x: ~~𝔄) (bs: list abyte),
      decode_value (syn_mty 𝔄) bs = syn_val x ↔
      decode_value (syn_mty 𝔅) bs = syn_val (syn_type_morphism_fn f x) ;
}.
Global Existing Instance syn_iso.
Global Existing Instance syn_iso_proph.

Global Instance isoₛ_id_id {𝔄} : @Isoₛ 𝔄 𝔄 idₛ idₛ.
Proof. split; try apply _; done. Qed.

Global Instance isoₛ_compose {𝔄 𝔅 ℭ} `{!@Isoₛ 𝔄 𝔅 f f'} `{!@Isoₛ 𝔅 ℭ g g'}
    : Isoₛ (g ∘ₛ f) (f' ∘ₛ g').
Proof.
  inversion H. inversion H0. split.
    - typeclasses eauto. - typeclasses eauto. - congruence.
    - intros. simpl. rewrite <- syn_iso_phys_eq1. by rewrite <- syn_iso_phys_eq0.
    - congruence.
    - intros x bs. simpl. by rewrite syn_iso_bytes0 syn_iso_bytes1.
Qed.

Local Definition cons_to_pair (v : Value) : Value :=
  match v with VTuple (v :: vs) => VTuple [v; VTuple vs] | _ => v end.
Local Instance cons_to_pair_inj : Inj (=) (=) cons_to_pair.
Proof.
  intros [| | |[|??]|] [| | |[|??]|]; simpl; intros; simplify_eq; done.
Qed.

Global Instance isoₛ_cons_prod {𝔄 𝔅l} : @Isoₛ (𝔄 * Π! 𝔅l) (Π! (𝔄 :: 𝔅l)) to_cons_prodₛ of_cons_prodₛ.
Proof.
  split; [apply _|apply _|done|by intros [??]| |].
  - change (seq_size [syn_mty 𝔄; seq_tuple (syn_mty <$> 𝔅l)] =
      seq_size (syn_mty 𝔄 :: (syn_mty <$> 𝔅l))).
    rewrite !seq_size_cons seq_size_nil mty_size_seq_tuple. lia.
  - intros [a xs] bs.
    set M := mapM id (plist_to_list (pmap (λ _ x0, syn_val x0) xs)).
    change (decode_value (seq_tuple [syn_mty 𝔄; seq_tuple (syn_mty <$> 𝔅l)]) bs =
        (v₀ ← syn_val a; v₁ ← VTuple <$> M; Some (VTuple [v₀; v₁])) ↔
      decode_value (seq_tuple (syn_mty 𝔄 :: (syn_mty <$> 𝔅l))) bs =
        VTuple <$> (v ← syn_val a; vs ← M; Some (v :: vs))).
    rewrite (decode_prod_cons ) -/(cons_to_pair).
    rewrite (_: (v₀ ← syn_val a; v₁ ← VTuple <$> M; Some (VTuple [v₀; v₁])) =
      cons_to_pair <$> (VTuple <$> (v ← syn_val a; vs ← M; Some (v :: vs)))).
    + apply fmap_eq_iff, _.
    + destruct (syn_val a); [|done]. simpl. by destruct M.
Qed.

Global Instance isoₛ_empty_prod_unit : @Isoₛ (Π! []) unitₛ empty_prod_to_unitₛ empty_prod_of_unitₛ.
Proof.
  split; [split; fun_ext; destruct x; done|split; fun_ext; destruct x; done|done|by intros []|done|].
  intros [] bs. done.
Qed.

Global Instance Isoₛ_prod_left_id {𝔄} : @Isoₛ (() * 𝔄) 𝔄 prod_left_idₛ prod_left_id'ₛ.
Proof.
  split; [apply _|apply _|done|by intros [[]?]| |].
  - change (seq_size [zst_mty; syn_mty 𝔄] = syn_bsize 𝔄).
    rewrite !seq_size_cons seq_size_nil /= /syn_bsize. lia.
  - intros [[] a] bs.
    change (decode_value (seq_tuple [zst_mty; syn_mty 𝔄]) bs =
        (v₀ ← Some (VTuple []); v₁ ← syn_val a; Some (VTuple [v₀; v₁])) ↔
      decode_value (syn_mty 𝔄) bs = syn_val a).
    rewrite (decode_prod_unit_l ).
    rewrite (_: (v₀ ← Some (VTuple []); v₁ ← syn_val a; Some (VTuple [v₀; v₁])) =
      (λ v, VTuple [VTuple []; v]) <$> syn_val a); [|by destruct (syn_val a)].
    apply fmap_eq_iff. intros ???. by simplify_eq.
Qed.

Global Instance Isoₛ_prod_right_id {𝔄} : @Isoₛ (𝔄 * ()) 𝔄 prod_right_idₛ prod_right_id'ₛ.
Proof.
  split; [apply _|apply _|simpl; lia|intros [?[]]; simpl; by rewrite List.app_nil_r| |].
  - change (seq_size [syn_mty 𝔄; zst_mty] = syn_bsize 𝔄).
    rewrite !seq_size_cons seq_size_nil /=. rewrite /syn_bsize. lia.
  - intros [a []] bs.
    change (decode_value (seq_tuple [syn_mty 𝔄; zst_mty]) bs =
        (v₀ ← syn_val a; v₁ ← Some (VTuple []); Some (VTuple [v₀; v₁])) ↔
      decode_value (syn_mty 𝔄) bs = syn_val a).
    rewrite (decode_prod_unit_r ).
    rewrite (_: (v₀ ← syn_val a; v₁ ← Some (VTuple []); Some (VTuple [v₀; v₁])) =
      (λ v, VTuple [v; VTuple []]) <$> syn_val a); [|by destruct (syn_val a)].
    apply fmap_eq_iff. intros ???. by simplify_eq.
Qed.
