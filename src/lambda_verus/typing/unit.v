From iris.proofmode Require Import proofmode.
From lrust.typing Require Export type.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

(** * The unit type

[() : type unitₛ] is the zero-sized type with no ownership. *)

Section unit.
  Context `{!typeG Σ}.

  Program Definition unit_ty : type unitₛ :=
    {| ty_lfts := [];
       ty_E := [];
       ty_gho_own x d g tid := True%I;
       ty_gho_res x d g tid := True%I;
       ty_gho_pers x d g tid := True%I;
       ty_mty := syn_mty _; ty_val := syn_val; ty_mty_eq := eq_refl; ty_val_eq _ := eq_refl;
       ty_fval := syn_fval; ty_fval_eq _ := eq_refl;
       ty_shr κ x d g tid := True%I;
    |}%I.
  Next Obligation. intros. iIntros. done. Qed.
  Next Obligation. intros. iIntros. done. Qed.
  Next Obligation. iIntros. done. Qed.
  Next Obligation. iIntros. done. Qed.
  Next Obligation. iIntros. done. Qed.
  Next Obligation.
    iIntros. iFrame. iModIntro. iApply step_fupdN_intro; [done|].
    by iApply bi.laterN_intro.
  Qed.
  Next Obligation. intros. set_solver. Qed.
  Next Obligation. by iIntros. Qed.
End unit.

Notation "()" := unit_ty : lrust_type_scope.

Section typing.
  Context `{!typeG Σ}.

  Global Instance unit_copy : Copy ().
  Proof.
    split. - apply _. - by apply _. - intros. iIntros. iApply guards_true.
  Qed.

  Global Instance unit_send : Send ().
  Proof. done. Qed.

  Global Instance unit_sync : Sync ().
  Proof. intros. split; [|split]; trivial. Qed.

  Global Instance unit_res_own : ResOwn ().
  Proof. done. Qed.

  Lemma unit_resolve E L : resolve E L () (const (const True)).
  Proof. apply resolve_just. Qed.
End typing.

Global Hint Resolve unit_resolve : lrust_typing.
