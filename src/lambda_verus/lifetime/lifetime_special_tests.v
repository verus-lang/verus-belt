From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import excl.
Require Import guarding.guard.
From lrust.lifetime Require Import lifetime_full.
From iris.prelude Require Import options.

(** Tests of the special openings of the lifetime logic ([llftl_bor_acc_special]). *)

Section SpecialTests.
  Context {Σ: gFunctors}.
  Context `{!llft_logicGS Σ}.
  Context `{!invGS Σ}.
  Context `{!inG Σ (exclR unitO)}.

  (** Open specially, close with changed contents, end the lifetime, and get the
      inheritance. The back-map gets the token back from a user invariant in [NllftUsr],
      through a handshake with an exclusive key: the pattern of (L3) of the GMB plan. *)
  Lemma test_special_close_end P Q κ γ :
    κ ≠ llft_empty →
    llft_ctx -∗ ▷ P -∗ @[κ] -∗ own γ (Excl ()) -∗ (P -∗ Q) -∗ (Q -∗ P) -∗
    |={↑Nllft}=> |={↑Nllft}[∅]▷=> |={↑Nllft}=> ▷ P.
  Proof.
    iIntros (Hne) "#ctx P Alive Key PQ QP".
    iMod (llftl_borrow with "ctx P") as "[Bor Inh]"; first done.
    iMod (llftl_bor_acc_special with "ctx Bor Alive") as "(P & Tok & Close)"; first done.
    iMod (inv_alloc NllftUsr _ (special_open κ ∨ own γ (Excl ())) with "[Tok]") as "#I".
    { iNext. by iLeft. }
    iMod ("Close" $! Q with "[Key QP PQ P]") as "[Bor Alive]".
    { iSplitR "PQ P"; last first. { iNext. by iApply "PQ". }
      iNext. iIntros "[Q _]". iInv "I" as "[>T|>K]" "Hc".
      - iMod ("Hc" with "[Key]") as "_". { iNext. by iRight. }
        iModIntro. iFrame "T". iNext. by iApply "QP".
      - iDestruct (own_valid_2 with "Key K") as %[]. }
    iModIntro.
    iMod (llftl_end' with "ctx Alive") as "End"; first done.
    iModIntro. iNext. iMod "End" as "#Dead". iModIntro.
    by iMod ("Inh" with "Dead").
  Qed.

  (** After a special opening and closing, reopen the borrow normally, close it again,
      reborrow it, and then end the lifetime. *)
  Lemma test_special_reopen_reborrow P κ :
    κ ≠ llft_empty →
    llft_ctx -∗ ▷ P -∗ @[κ] -∗
    |={↑Nllft}=> |={↑Nllft}[∅]▷=> |={↑Nllft}=> ▷ P.
  Proof.
    iIntros (Hne) "#ctx P Alive".
    iMod (llftl_borrow with "ctx P") as "[Bor Inh]"; first done.
    iMod (llftl_bor_acc_special with "ctx Bor Alive") as "(P & Tok & Close)"; first done.
    (* close with the token as part of the new contents *)
    iMod ("Close" $! (P ∗ special_open κ)%I with "[P Tok]") as "[Bor Alive]".
    { iSplitR; last first. { iNext. iFrame. }
      iNext. iIntros "[[P >T] _]". iModIntro. by iFrame. }
    (* a normal opening *)
    iMod (llftl_bor_acc with "ctx Bor Alive") as "[PT Close]"; first done.
    iMod ("Close" $! (P ∗ special_open κ)%I with "[PT]") as "[Bor Alive]".
    { iSplitR "PT"; last done. iNext. iIntros "[PT _]". by iModIntro. }
    (* a reborrow *)
    iMod (llftl_reborrow with "ctx [] Bor") as "[Bor2 Back]"; first done.
    { iApply guards_refl. }
    iMod (llftl_sep_split with "ctx Bor2") as "[Bor2 Bor3]"; first done.
    iMod (llftl_sep_join with "ctx Bor2 Bor3") as "Bor2"; first done.
    iModIntro.
    iMod (llftl_end' with "ctx Alive") as "End"; first done.
    iModIntro. iNext. iMod "End" as "#Dead". iModIntro.
    by iMod ("Inh" with "Dead").
  Qed.

  (** A client-style use of the guard law: the token is stored in an [NllftUsr] invariant,
      and an owned exclusive resource that is guarded by [@[κ]] gives a contradiction
      (cf. (L1) of the GMB plan, in state [Out κ]). *)
  Lemma test_special_guard_excl E γ κ :
    ↑NllftUsr ⊆ E →
    ↑NllftG ∪ ↑NllftO ⊆ E ∖ ↑NllftUsr →
    llft_ctx -∗ inv NllftUsr (special_open κ) -∗
    (@[κ] &&{↑NllftG ∪ ↑NllftO}&&> own γ (Excl ())) -∗ own γ (Excl ()) ={E}=∗ False.
  Proof.
    iIntros (Hmask1 Hmask2) "#ctx #I #G Own".
    iInv "I" as ">Tok" "Hclose".
    iDestruct (llftl_special_open_guard κ with "ctx") as "#SG".
    iDestruct (guards_transitive with "SG G") as "#SG2".
    iMod (guards_and_pers_with_excl (special_open κ) (own γ (Excl ())) (own γ (Excl ()))
            False%I (own γ (Excl ())) (E ∖ ↑NllftUsr) (↑NllftG ∪ ↑NllftO) 0
            with "[] SG2 SG2 Tok Own") as "J"; first done.
    { iModIntro. iIntros "[[A _] B]". iDestruct (own_valid_2 with "A B") as %[]. }
    iMod "J" as "(_ & _ & [])".
  Qed.
End SpecialTests.
