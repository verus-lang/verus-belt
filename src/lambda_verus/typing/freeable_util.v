From lrust.typing Require Export type.
From lrust.typing Require Import uninit type_context programs.
From guarding Require Import guard tactics.
From lrust.lifetime Require Import lifetime_full.
Set Default Proof Using "Type".

Section freeable.
  Context `{!typeG Σ}.

  Definition freeable_sz (n sz: nat) (l: loc) : iProp Σ :=
    match sz, n with 0%nat, _ => True | _, 0%nat => False |
      sz, n => †{pos_to_Qp (Pos.of_nat sz) / pos_to_Qp (Pos.of_nat n)}l…sz end.
  Arguments freeable_sz: simpl never.

  Global Instance freeable_sz_timeless n sz l : Timeless (freeable_sz n sz l).
  Proof. case sz, n; apply _. Qed.

  Lemma freeable_sz_full n l : freeable_sz n n l ⊣⊢ †{1}l…n ∨ ⌜Z.of_nat n = 0⌝.
  Proof.
    case n=> [|n']. { iSplit; iIntros; by [iRight|]. }
    have ->: Z.of_nat (S n') = 0 ↔ False by done.
    by rewrite right_id /freeable_sz Qp.div_diag.
  Qed.

  Lemma freeable_sz_full_S n l : freeable_sz (S n) (S n) l ⊣⊢ †{1}l…(S n).
  Proof.
    rewrite freeable_sz_full. iSplit; [|iIntros; by iLeft]. by iIntros "[$|%]".
  Qed.

  Lemma freeable_sz_split n sz sz' l :
    freeable_sz n sz l ∗ freeable_sz n sz' (l +ₗ sz) ⊣⊢
    freeable_sz n (sz + sz') l.
  Proof.
    case sz; [|case sz'; [|rewrite /freeable_sz; case n]]=>/= *.
    - by rewrite left_id shift_loc_0.
    - by rewrite right_id Nat.add_0_r.
    - iSplit; by [iIntros "[??]"|iIntros].
    - rewrite heap_freeable_op_eq. f_equiv; [|done].
      by rewrite -Qp.div_add_distr pos_to_Qp_add -Nat2Pos.inj_add.
  Qed.

  Lemma freeable_sz_eq n sz sz' l :
    sz = sz' → freeable_sz n sz l -∗ freeable_sz n sz' l.
  Proof. iIntros (->) "$". Qed.

  (* Make sure 'simpl' doesn't unfold. *)
  Global Opaque freeable_sz.
End freeable.
