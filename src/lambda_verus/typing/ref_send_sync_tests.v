From lrust.typing Require Import type int own product shr_bor uniq_bor pcell.
Set Default Proof Using "Type".

(** * Tests: [Send], [SendUpd] and [Sync] of the references [&shr{κ}] and [&uniq{κ}]

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

  (** [uniq_send]: [&uniq{κ} ty] is [Send] when [ty] is [Send] (not necessarily [Sync]). *)
  Goal ∀ 𝔄 (ty: type 𝔄) κ, Send ty → Send (&uniq{κ} ty).
  Proof. intros. apply _. Qed.

  Goal ∀ 𝔄 (ty: type 𝔄) κ κ' n, Send ty → Send (&uniq{κ} (own_bytes n (&uniq{κ'} ty) * int))%T.
  Proof. intros. apply _. Qed.

  (** Every [Send] type is [SendUpd] ([send_send_upd]), also below the structural instances
      of [SendUpd]. *)
  Goal ∀ 𝔄 (ty: type 𝔄) κ n, Send ty → SendUpd (own_bytes n (&uniq{κ} ty) * int)%T.
  Proof. intros. apply _. Qed.

  Goal ∀ 𝔄 (ty: type 𝔄) n, SendUpd ty → SendUpd (own_bytes n ty * int)%T.
  Proof. intros. apply _. Qed.

  (** A shared reference to a cell can be sent (as [&PCell<T>] in Verus). *)
  Goal ∀ κ, Send (&shr{κ} (pcell_ty (wfm (MInt i32)))).
  Proof. apply _. Qed.
End ref_send_sync_tests.
