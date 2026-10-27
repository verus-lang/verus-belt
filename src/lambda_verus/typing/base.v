From Coq.Program Require Import Tactics.
From lrust.lang Require Export proofmode.

(* Last, so that we make sure we shadow the defintion of delete for
   sets coming from the prelude. *)
From lrust.lang.lib Require Export new_delete.

Open Scope Z_scope.

Create HintDb lrust_typing.
Create HintDb lrust_typing_merge.

(* We first try to solve everything without the merging rules, and
   then start from scratch with them.

   The reason is that we want we want the search proof search for
   [tctx_extract_hasty] to suceed even if the type is an evar, and
   merging makes it diverge in this case. *)
Ltac solve_typing :=
  (typeclasses eauto with lrust_typing typeclass_instances core; fail) ||
  (typeclasses eauto with lrust_typing lrust_typing_merge typeclass_instances core; fail).

Global Hint Constructors Forall Forall2 elem_of_list : lrust_typing.
Global Hint Resolve submseteq_cons submseteq_inserts_l submseteq_inserts_r
  : lrust_typing.

(** Membership in (and inclusion between) lists that are not syntactically built from
    [cons]/[nil], typically the external lifetime context [fp_E fp ϝ] of a function body.
    Without this, unification of [elem_of_list_here] with such a list instantiates the
    tail by a partially reduced term (inlined [app]/[fmap] fixpoints over [ty_lfts …]),
    and the kernel's conversion of that term with the original list at [Qed] is
    exponential in the depth of the types of the signature (30 s for
    [&uniq (own_ptr 1 int * int)], more than 10 minutes for [&shr ((int * int) * int)]).
    So the spine of the list is normalized first (by [hnf], element by element); the
    kernel then compares the original list with a list in normal form, which is linear. *)
Ltac list_spine_norm l :=
  let l' := eval hnf in l in
  lazymatch l' with
  | ?x :: ?k => let x := eval cbv beta in x in
      let k := list_spine_norm k in constr:(x :: k)
  | [] => l'
  | _ => l
  end.
Ltac list_spine_norm_progress l :=
  lazymatch l with
  | _ :: _ => fail
  | [] => fail
  | _ => let l' := list_spine_norm l in
      lazymatch l' with _ :: _ => l' | [] => l' end
  end.
Global Hint Extern 0 (@elem_of _ (list _) _ ?x ?l) =>
  (let l' := list_spine_norm_progress l in change (x ∈ l')) : lrust_typing.
Global Hint Extern 0 (?l1 ⊆+ ?l2) =>
  (first [let l' := list_spine_norm_progress l1 in change (l' ⊆+ l2)
         |let l' := list_spine_norm_progress l2 in change (l1 ⊆+ l')]) : lrust_typing.

Global Hint Extern 1 (@eq nat _ (Z.to_nat _)) =>
  (etrans; [symmetry; exact: Nat2Z.id | reflexivity]) : lrust_typing.
Global Hint Extern 1 (@eq nat (Z.to_nat _) _) =>
  (etrans; [exact: Nat2Z.id | reflexivity]) : lrust_typing.

Global Hint Resolve <- elem_of_app : lrust_typing.

(* done is there to handle equalities with constants *)
Global Hint Extern 100 (_ ≤ _) => simpl; first [done|lia] : lrust_typing.
Global Hint Extern 100 (@eq Z _ _) => simpl; first [done|lia] : lrust_typing.
Global Hint Extern 100 (@eq nat _ _) => simpl; first [done|lia] : lrust_typing.
