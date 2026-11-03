From lrust.typing Require Import type int own product shr_bor uniq_bor pcell.
Set Default Proof Using "Type".

(** * Tests: [Send] and [Sync] of the references [&shr{κ}] and [&uniq{κ}]

The instances are found by type class search, also nested ([&shr] of [&uniq], references
to boxes, pairs and cells). *)

Section ref_send_sync_tests.
  Context `{!typeG Σ}.

  Goal ∀ κ, Send (&shr{κ} int) ∧ Sync (&shr{κ} int).
  Proof. split; apply _. Qed.

  Goal ∀ κ, Send (&uniq{κ} int) ∧ Sync (&uniq{κ} int).
  Proof. split; apply _. Qed.

  Goal ∀ κ κ' n, Send (&shr{κ} (&uniq{κ'} (own_bytes n int))).
  Proof. apply _. Qed.

  Goal ∀ κ κ', Sync (&uniq{κ} (&shr{κ'} (int * int))%T).
  Proof. apply _. Qed.

  (** A shared reference to a cell can be sent (as [&PCell<T>] in Verus). *)
  Goal ∀ κ, Send (&shr{κ} (pcell_ty (wfm (MInt i32)))).
  Proof. apply _. Qed.
End ref_send_sync_tests.
