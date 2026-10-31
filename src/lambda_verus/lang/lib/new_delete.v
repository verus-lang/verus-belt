From lrust.lang Require Export notation.
From lrust.lang Require Import heap lifting proofmode.
Set Default Proof Using "Type".

Definition new : val :=
  λ: ["n"],
    if: "n" ≤ #0 then #((42%positive, 1337):loc)
    else Alloc "n".

Definition delete : val :=
  λ: ["n"; "loc"],
    if: "n" ≤ #0 then #☠
    else Free "n" "loc".

Section specs.
  Context `{!lrustGS Σ}.

  Lemma wp_new E n:
    0 ≤ n →
    {{{ True }}} new [ #n ] @ E
    {{{ l, RET LitV $ LitLoc l;
        (†l…(Z.to_nat n) ∨ ⌜n = 0⌝) ∗ l ↦b replicate (Z.to_nat n) Uninit }}}.
  Proof.
    iIntros (? Φ) "_ HΦ". wp_lam. wp_op; case_bool_decide.
    - wp_if. assert (n = 0) as -> by lia. iApply "HΦ".
      rewrite heap_mapsto_bytes_nil. auto.
    - wp_if. iApply wp_alloc_bytes; [lia|done|]. iIntros "!>" (l sz) "(-> & H† & H↦)".
      iApply "HΦ". rewrite Nat2Z.id. iFrame.
  Qed.

  Lemma wp_delete bs (n: Z) l E :
    ↑naN ⊆ E → n = length bs →
    {{{ l ↦b bs ∗ (†l…(length bs) ∨ ⌜n = 0⌝) }}}
      delete [ #n; #l] @ E
    {{{ RET #☠; True }}}.
  Proof.
    iIntros (?? Φ) "(H↦ & [H†|%]) HΦ";
      wp_lam; wp_op; case_bool_decide; try lia; wp_if; try by iApply "HΦ".
    iApply (wp_free_bytes with "[$H↦ $H†]"); [done..|]. iIntros "!> _". by iApply "HΦ".
  Qed.
End specs.
