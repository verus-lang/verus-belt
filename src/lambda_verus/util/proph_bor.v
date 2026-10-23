(** * Prophetic borrows.

  This library packages a full borrow (from the leaf lifetime logic) together with the
  value-observer/prophecy-controller ghost state of [uniq_cmra.v] into a standalone
  _prophetic borrow_ abstraction:

    &proph{κ ; ξ ➤ x} P

  The intuitive reading: we hold a mutable borrow, at lifetime [κ], of a proposition
  [P y] whose value [y] can be mutated; the current value is [x], and when the borrow is
  "frozen" (resolved), the prophecy variable [ξ] gets resolved to the value of [y] at
  that time. The values range over [pv_val ξ = ~~ (`ξ.(pv_ty))].

  Like the full borrow library, there is an "indexed" variant [proph_ibor] which is split
  into a timeless ghost resource ([proph_bor_tok], with an arbitrary index name) and a
  persistent part ([proph_idx_bor]).

  All definitions are opaque; clients manipulate them only through the lemmas proved here,
  which completely abstract away the underlying [.VO]/[.PC] resources. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import fancy_updates.
From lrust.prophecy Require Import syn_type prophecy.
From lrust.lifetime Require Import lifetime_full.
From lrust.util Require Import basic update.
From lrust.typing Require Import uniq_cmra.
From guarding Require Import guard tactics.
From guarding.lib Require Import fractional.
Set Default Proof Using "Type".

(** The type of values of a prophecy variable. *)
Notation pv_val ξ := (~~ (proj1_sig (pv_ty ξ))) (only parsing).

Section proph_bor.
Context `{!invGS Σ, !prophG Σ, !uniqG Σ, !llft_logicGS Σ, !frac_logicG Σ}.
Implicit Types (ξ ζ: proph_var) (κ: lft).

(** The contents of a prophetic borrow: the prophecy controller for the current value,
    together with the payload. *)
Local Definition pbor_body ξ (P: (pv_val ξ) → iProp Σ) : iProp Σ :=
  ∃ x', .PC[ξ] x' (vπ x') ∗ P x'.

(** A "loan": an unborrowed prophecy cell, as created by [proph_loan_intro]. *)
Definition proph_loan ξ (x: pv_val ξ) : iProp Σ :=
  .VO[ξ] x ∗ .PC[ξ] x (vπ x).

(** The persistent part of an indexed prophetic borrow. *)
Definition proph_idx_bor κ ξ (idx: Idx) (P: (pv_val ξ) → iProp Σ) : iProp Σ :=
  &{κ, idx} (pbor_body ξ P).

(** The timeless part of an indexed prophetic borrow. *)
Definition proph_bor_tok ξ (x: pv_val ξ) (idx: Idx) : iProp Σ :=
  .VO[ξ] x ∗ idx_bor_tok idx.

(** Indexed prophetic borrow. *)
Definition proph_ibor κ ξ (x: pv_val ξ) (idx: Idx) (P: (pv_val ξ) → iProp Σ) : iProp Σ :=
  proph_bor_tok ξ x idx ∗ proph_idx_bor κ ξ idx P.

(** Prophetic borrow. *)
Definition proph_bor κ ξ (x: pv_val ξ) (P: (pv_val ξ) → iProp Σ) : iProp Σ :=
  ∃ idx, proph_ibor κ ξ x idx P.

(** ** Basic structural lemmas *)

Global Instance proph_bor_tok_timeless ξ x idx : Timeless (proph_bor_tok ξ x idx) := _.
Global Instance proph_idx_bor_persistent κ ξ idx P : Persistent (proph_idx_bor κ ξ idx P) := _.

Lemma proph_bor_idx κ ξ x P :
  proph_bor κ ξ x P ⊣⊢ ∃ idx, proph_ibor κ ξ x idx P.
Proof. done. Qed.

Lemma proph_ibor_sep κ ξ x idx P :
  proph_ibor κ ξ x idx P ⊣⊢ proph_bor_tok ξ x idx ∗ proph_idx_bor κ ξ idx P.
Proof. done. Qed.

(** ** Non-expansiveness / properness in the payload *)

Local Lemma pbor_body_proper ξ (P Q: (pv_val ξ) → iProp Σ) :
  (∀ x', P x' ⊣⊢ Q x') → pbor_body ξ P ⊣⊢ pbor_body ξ Q.
Proof. intros HPQ. rewrite /pbor_body. by setoid_rewrite HPQ. Qed.

Local Lemma pbor_body_ne ξ (P Q: (pv_val ξ) → iProp Σ) n :
  (∀ x', P x' ≡{n}≡ Q x') → pbor_body ξ P ≡{n}≡ pbor_body ξ Q.
Proof. intros HPQ. rewrite /pbor_body. f_equiv=> ?. f_equiv. apply HPQ. Qed.

Lemma proph_idx_bor_proper κ ξ idx (P Q: (pv_val ξ) → iProp Σ) :
  (∀ x', P x' ⊣⊢ Q x') → proph_idx_bor κ ξ idx P ⊣⊢ proph_idx_bor κ ξ idx Q.
Proof. intros HPQ. rewrite /proph_idx_bor. f_equiv. by apply pbor_body_proper. Qed.

Lemma proph_idx_bor_ne κ ξ idx (P Q: (pv_val ξ) → iProp Σ) n :
  (∀ x', P x' ≡{n}≡ Q x') → proph_idx_bor κ ξ idx P ≡{n}≡ proph_idx_bor κ ξ idx Q.
Proof. intros HPQ. rewrite /proph_idx_bor. f_equiv. by apply pbor_body_ne. Qed.

(** The borrow body is only used under a later, so the payload may be given
    one step later. *)
Lemma proph_idx_bor_contractive κ ξ idx (P Q: (pv_val ξ) → iProp Σ) n :
  (∀ x', dist_later n (P x') (Q x')) →
  proph_idx_bor κ ξ idx P ≡{n}≡ proph_idx_bor κ ξ idx Q.
Proof.
  intros HPQ. rewrite /proph_idx_bor. apply idx_bor_contractive.
  destruct n as [|n]. { split. lia. }
  apply dist_later_S. apply pbor_body_ne => x'.
  have := HPQ x'. rewrite dist_later_S. done.
Qed.

Lemma proph_ibor_proper κ ξ x idx (P Q: (pv_val ξ) → iProp Σ) :
  (∀ x', P x' ⊣⊢ Q x') → proph_ibor κ ξ x idx P ⊣⊢ proph_ibor κ ξ x idx Q.
Proof. intros HPQ. rewrite /proph_ibor. f_equiv. by apply proph_idx_bor_proper. Qed.

Lemma proph_ibor_ne κ ξ x idx (P Q: (pv_val ξ) → iProp Σ) n :
  (∀ x', P x' ≡{n}≡ Q x') → proph_ibor κ ξ x idx P ≡{n}≡ proph_ibor κ ξ x idx Q.
Proof. intros HPQ. rewrite /proph_ibor. f_equiv. by apply proph_idx_bor_ne. Qed.

Lemma proph_ibor_contractive κ ξ x idx (P Q: (pv_val ξ) → iProp Σ) n :
  (∀ x', dist_later n (P x') (Q x')) →
  proph_ibor κ ξ x idx P ≡{n}≡ proph_ibor κ ξ x idx Q.
Proof. intros HPQ. rewrite /proph_ibor. f_equiv. by apply proph_idx_bor_contractive. Qed.

(** ** Shortening and payload change *)

Lemma proph_idx_bor_shorten κ κ' ξ idx (P Q: (pv_val ξ) → iProp Σ) :
  κ' ⊑ κ -∗ ▷ □ (∀ x', P x' ↔ Q x') -∗
  proph_idx_bor κ ξ idx P -∗ proph_idx_bor κ' ξ idx Q.
Proof.
  iIntros "#InLft #Iff Bor". rewrite /proph_idx_bor.
  iApply (llftl_idx_shorten with "InLft").
  iApply llftl_idx_bor_iff; [|done]. iIntros "!> !>".
  iSplit; iDestruct 1 as (x') "(Pc & p)"; iExists x'; iFrame; by iApply "Iff".
Qed.

Lemma proph_ibor_shorten κ κ' ξ x idx (P Q: (pv_val ξ) → iProp Σ) :
  κ' ⊑ κ -∗ ▷ □ (∀ x', P x' ↔ Q x') -∗
  proph_ibor κ ξ x idx P -∗ proph_ibor κ' ξ x idx Q.
Proof.
  iIntros "#InLft #Iff [Tok Bor]". iFrame "Tok".
  iApply (proph_idx_bor_shorten with "InLft Iff Bor").
Qed.

(** ** Loans and allocation *)

(** Borrow against the loan's prophecy token. *)
Lemma proph_loan_tok ξ x :
  proph_loan ξ x -∗ 1:[ξ] ∗ (1:[ξ] -∗ proph_loan ξ x).
Proof.
  iIntros "[Vo Pc]".
  iDestruct (uniq_proph_tok with "Vo Pc") as "(Vo & $ & Pc)".
  iIntros "tok". iFrame "Vo". by iApply "Pc".
Qed.

(** Create a full prophetic borrow at lifetime [κ] from a loan; after [κ] ends,
    we recover the contents with the controller weakened to an equalizer. *)
Lemma proph_loan_borrow E κ ξ x (P: (pv_val ξ) → iProp Σ) :
  ↑Nllft ⊆ E →
  llft_ctx -∗ proph_ctx -∗ proph_loan ξ x -∗ ▷ P x ={E}=∗
    proph_bor κ ξ x P ∗
    ([†κ] ={↑Nllft}=∗ ▷ ∃ x', ((.$ ξ) :== vπ x') ∗ P x').
Proof.
  iIntros (?) "#LFT #PROPH [Vo Pc] P".
  iMod (llftl_borrow E κ (pbor_body ξ P) with "LFT [Pc P]") as "[Bor Back]"; [done| |].
  { iNext. iExists x. iFrame. }
  iDestruct (llftl_bor_idx with "Bor") as (idx) "[Bor Tok]".
  iModIntro. iSplitR "Back".
  - iExists idx. iFrame.
  - iIntros "†κ". iMod ("Back" with "†κ") as "Body". iModIntro. iNext.
    iDestruct "Body" as (x') "[Pc P]". iExists x'. iFrame.
    iApply (proph_ctrl_eqz with "PROPH Pc").
Qed.

(** ** Accessors *)

(** Open an indexed prophetic borrow (keeping the same index). The opening
    reveals that the contents is at the current value [x]; closing may update
    the value. *)
Lemma proph_ibor_acc E κ ξ x idx (P: (pv_val ξ) → iProp Σ) G :
  Timeless G → ↑Nllft ⊆ E →
  llft_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗
  proph_ibor κ ξ x idx P -∗ G ={E}=∗
    ▷ P x ∗ (∀ x1, ▷ P x1 ={↑Nllft}=∗ proph_ibor κ ξ x1 idx P ∗ G).
Proof.
  iIntros (??) "#LFT #UNIQ #Gk ((Vo & Tok) & #Bor) G".
  iMod (llftl_bor_idx_acc_guarded with "LFT Bor Tok Gk G") as "[Body Back]"; [done|].
  iMod (bi.later_exist_except_0 with "Body") as (x') "(Pc & P)".
  iMod (uniq_strip_later with "Vo Pc") as "(<- & Vo & Pc)".
  iModIntro. iFrame "P".
  iIntros (x1) "P".
  iMod (uniq_update ξ x1 (vπ x1) with "UNIQ Vo Pc") as "[Vo Pc]".
  { pose proof (nclose_subseteq Nllft 0). solve_ndisj. }
  iMod ("Back" with "[Pc P]") as "[Tok G]".
  { iNext. iExists x1. iFrame. }
  iModIntro. iFrame "∗#".
Qed.

(** Open a prophetic borrow with a lifetime token, closing with a possibly
    different payload (resulting in a fresh index). The caller must provide a
    way to transform the contents of the new payload back into the old
    payload; this is only required once the lifetime has ended. *)
Lemma proph_ibor_acc_rebody E κ ξ x idx (P Q: (pv_val ξ) → iProp Σ) :
  ↑Nllft ⊆ E →
  llft_ctx -∗ uniq_ctx -∗ @[κ] -∗
  proph_ibor κ ξ x idx P ={E}=∗ ▷ ◇ (
    P x ∗
    (∀ x1, ▷ Q x1 -∗
       ▷ (∀ x2, ▷ Q x2 ∗ [†κ] ={↑NllftUsr ∪ ↑NllftUsr2}=∗ ▷ P x2)
       ={↑Nllft}=∗
       ∃ idx', proph_ibor κ ξ x1 idx' Q ∗ @[κ])).
Proof.
  iIntros (?) "#LFT #UNIQ κ ((Vo & Tok) & #IBor)".
  iDestruct (llftl_bor_idx_to_full with "IBor Tok") as "Bor".
  iMod (llftl_bor_acc with "LFT Bor κ") as "[Body Back]"; [done|].
  iModIntro. iNext.
  iDestruct "Body" as (x') "(Pc & P)".
  iMod (uniq_strip_later with "Vo Pc") as "(<- & Vo & Pc)".
  iModIntro. iFrame "P".
  iIntros (x1) "Q W".
  iMod (uniq_update ξ x1 (vπ x1) with "UNIQ Vo Pc") as "[Vo Pc]".
  { pose proof (nclose_subseteq Nllft 0). solve_ndisj. }
  iAssert (▷ (▷ pbor_body ξ Q ∗ [†κ] ={↑NllftUsr ∪ ↑NllftUsr2}=∗ ▷ pbor_body ξ P))%I
    with "[W]" as "VS".
  { iNext. iIntros "[Body †κ]".
    iMod (bi.later_exist_except_0 with "Body") as (x2) "(Pc2 & Q)".
    iMod ("W" $! x2 with "[$Q $†κ]") as "P".
    iModIntro. iNext. iExists x2. iFrame. }
  iMod ("Back" $! (pbor_body ξ Q) with "[VS Pc Q]") as "[Bor κ]".
  { iFrame "VS". iNext. iExists x1. iFrame. }
  iDestruct (llftl_bor_idx with "Bor") as (idx') "[IBor' Tok']".
  iModIntro. iExists idx'. iFrame.
Qed.

(** Open a prophetic borrow, pre-resolving its prophecy variable to an
    arbitrary prophecy [uπ] (typically a function of fresh prophecy
    variables). The caller receives the payload, and may close the borrow
    with completely new contents [Q], provided future contents of [Q] can be
    transformed back into the old payload together with an equalizer
    witnessing that [uπ] matches the payload's final value. *)
Lemma proph_ibor_acc_preresolve E κ ξ x idx (P: (pv_val ξ) → iProp Σ)
    (uπ: proph (proj1_sig (pv_ty ξ))) ζl q G :
  Timeless G → ↑Nllft ∪ ↑prophN ⊆ E → uπ ./ ζl →
  llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗
  G -∗ q:+[ζl] -∗ proph_ibor κ ξ x idx P ={E}=∗
    ⟨π, π ξ = uπ π⟩ ∗ q:+[ζl] ∗ ▷ P x ∗
    ∀ (Q: iProp Σ),
       ▷ (▷ Q ={↑NllftUsr ∪ ↑NllftUsr2}=∗ ▷ ∃ x', (uπ :== vπ x') ∗ P x') -∗
       ▷ Q ={↑Nllft}=∗ (&{κ} Q) ∗ G.
Proof.
  iIntros (???) "#LFT #PROPH #UNIQ #Gk G ζl ((Vo & Tok) & #IBor)".
  iDestruct (llftl_bor_idx_to_full with "IBor Tok") as "Bor".
  iMod (llftl_bor_acc_guarded with "LFT Bor Gk G") as "[Body Back]"; [solve_ndisj|].
  iMod (bi.later_exist_except_0 with "Body") as (x') "(Pc & P)".
  iMod (uniq_strip_later with "Vo Pc") as "(<- & Vo & Pc)".
  iMod (uniq_preresolve ξ ζl uπ q with "UNIQ PROPH Vo Pc ζl")
    as "(#Obs & ζl & ToPc)"; [solve_ndisj|done|].
  iModIntro. iFrame "Obs ζl P".
  iIntros (Q) "W Q".
  iMod ("Back" $! Q with "[W ToPc $Q]") as "[$ $]"; [|done].
  iNext. iIntros "Q". iMod ("W" with "Q") as "Big".
  iModIntro. iNext.
  iDestruct "Big" as (x1) "(Eqz & P)".
  iExists x1. iFrame "P".
  iApply ("ToPc" with "Eqz").
Qed.

(** ** Mapping

    Replace a prophetic borrow [ξ] by a fresh one [ζ] (allocated by the caller
    as a loan), whose payload [Q] is related to the old payload [P] via [f]:
    the old prophecy is resolved to [fπ] of the new one. *)
Lemma proph_ibor_map E κ ξ x idx (P: (pv_val ξ) → iProp Σ) ζ y (Q: (pv_val ζ) → iProp Σ)
    (f: pv_val ζ → pv_val ξ) (fπ: proj1_sig (pv_ty ζ) → proj1_sig (pv_ty ξ)) G :
  Timeless G → ↑Nllft ∪ ↑prophN ⊆ E →
  (∀ y' π, vπ (f y') π = fπ (vπ y' π)) →
  (∀ y' ζl, fπ ∘ vπ y' ./ ζl → vπ y' ./ ζl) →
  llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗
  (▷ P x ={E}=∗ ▷ Q y ∗ (∀ y', ▷ Q y' ={↑NllftUsr ∪ ↑NllftUsr2}=∗ ▷ P (f y'))) -∗
  G -∗ proph_loan ζ y -∗ proph_ibor κ ξ x idx P ={E}=∗
    ⟨π, π ξ = fπ (π ζ)⟩ ∗ (∃ idx', proph_ibor κ ζ y idx' Q) ∗ G.
Proof.
  iIntros (Ti Hmask Hcomm Hrefl) "#LFT #PROPH #UNIQ #Gk Wand G Loan IBor".
  iDestruct (proph_loan_tok with "Loan") as "[ζtok ToLoan]".
  have Hdep: (λ π, fπ (π ζ)) ./ [ζ].
  { apply (proph_dep_constr fπ (λ π, π ζ)). apply proph_dep_one. }
  iMod (proph_ibor_acc_preresolve E κ ξ x idx P (λ π, fπ (π ζ)) [ζ] 1%Qp G Ti Hmask Hdep
    with "LFT PROPH UNIQ Gk G [ζtok] IBor") as "(#Obs & ζtok & P & Close)".
  { by rewrite big_sepL_singleton. }
  rewrite big_sepL_singleton.
  iDestruct ("ToLoan" with "ζtok") as "[Vo Pc]".
  iMod ("Wand" with "P") as "[Q Back]".
  iMod (fupd_mask_subseteq (↑Nllft)) as "Upd"; [solve_ndisj|].
  iMod ("Close" $! (pbor_body ζ Q) with "[Back] [Pc Q]") as "[Bor G]".
  { iNext. iIntros "Body".
    iMod (bi.later_exist_except_0 with "Body") as (y') "(Pc & Q)".
    iMod ("Back" with "Q") as "P". iModIntro. iNext. iExists (f y'). iFrame "P".
    iDestruct (proph_ctrl_eqz with "PROPH Pc") as "Eqz".
    iDestruct (proph_eqz_constr_refl fπ with "Eqz") as "Eqz"; [apply Hrefl|].
    iApply (proph_eqz_eq with "Eqz"); [done|]. fun_ext=> π /=. by rewrite Hcomm. }
  { iNext. iExists y. iFrame. }
  iMod "Upd" as "_".
  iDestruct (llftl_bor_idx with "Bor") as (idx') "[IBor' Tok']".
  iModIntro. iFrame "Obs G". iExists idx'. iFrame.
Qed.

(** ** Splitting

    Replace a prophetic borrow [ξ] by two fresh ones [ζ1], [ζ2] (allocated by
    the caller as loans); the old prophecy is resolved to [fπ] of the new ones. *)
Lemma proph_ibor_split E κ ξ x idx (P: (pv_val ξ) → iProp Σ)
    ζ1 y1 (Q1: (pv_val ζ1) → iProp Σ) ζ2 y2 (Q2: (pv_val ζ2) → iProp Σ)
    (f: pv_val ζ1 → pv_val ζ2 → pv_val ξ)
    (fπ: proj1_sig (pv_ty ζ1) → proj1_sig (pv_ty ζ2) → proj1_sig (pv_ty ξ)) G :
  Timeless G → ↑Nllft ∪ ↑prophN ⊆ E →
  (∀ a b π, vπ (f a b) π = fπ (vπ a π) (vπ b π)) →
  (∀ a b ζl, (λ π, fπ (vπ a π) (vπ b π)) ./ ζl → vπ a ./ ζl ∧ vπ b ./ ζl) →
  llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗
  (▷ P x ={E}=∗ ▷ Q1 y1 ∗ ▷ Q2 y2 ∗
      (∀ a b, ▷ Q1 a -∗ ▷ Q2 b ={↑NllftUsr ∪ ↑NllftUsr2}=∗ ▷ P (f a b))) -∗
  G -∗ proph_loan ζ1 y1 -∗ proph_loan ζ2 y2 -∗ proph_ibor κ ξ x idx P ={E}=∗
    ⟨π, π ξ = fπ (π ζ1) (π ζ2)⟩ ∗
    (∃ i1, proph_ibor κ ζ1 y1 i1 Q1) ∗ (∃ i2, proph_ibor κ ζ2 y2 i2 Q2) ∗ G.
Proof.
  iIntros (Ti Hmask Hcomm Hrefl) "#LFT #PROPH #UNIQ #Gk Wand G Loan1 Loan2 IBor".
  iDestruct (proph_loan_tok with "Loan1") as "[tok1 ToLoan1]".
  iDestruct (proph_loan_tok with "Loan2") as "[tok2 ToLoan2]".
  have Hdep: (λ π, fπ (π ζ1) (π ζ2)) ./ [ζ1; ζ2].
  { apply (proph_dep_constr2 fπ (λ π, π ζ1) (λ π, π ζ2) [ζ1] [ζ2]); apply proph_dep_one. }
  iMod (proph_ibor_acc_preresolve E κ ξ x idx P (λ π, fπ (π ζ1) (π ζ2)) [ζ1; ζ2] 1%Qp G
    Ti Hmask Hdep with "LFT PROPH UNIQ Gk G [tok1 tok2] IBor") as "(#Obs & toks & P & Close)".
  { simpl. iFrame. }
  iDestruct "toks" as "(tok1 & tok2 & _)".
  iDestruct ("ToLoan1" with "tok1") as "[Vo1 Pc1]".
  iDestruct ("ToLoan2" with "tok2") as "[Vo2 Pc2]".
  iMod ("Wand" with "P") as "(Q1 & Q2 & Back)".
  iMod (fupd_mask_subseteq (↑Nllft)) as "Upd"; [solve_ndisj|].
  iMod ("Close" $! (pbor_body ζ1 Q1 ∗ pbor_body ζ2 Q2)%I with "[Back] [Pc1 Q1 Pc2 Q2]")
    as "[Bor G]".
  { iNext. iIntros "[Body1 Body2]".
    iMod (bi.later_exist_except_0 with "Body1") as (a) "(Pc1 & Q1)".
    iMod (bi.later_exist_except_0 with "Body2") as (b) "(Pc2 & Q2)".
    iMod ("Back" with "Q1 Q2") as "P". iModIntro. iNext. iExists (f a b). iFrame "P".
    iDestruct (proph_ctrl_eqz with "PROPH Pc1") as "Eqz1".
    iDestruct (proph_ctrl_eqz with "PROPH Pc2") as "Eqz2".
    iIntros (E' ζl' q') "[% %Dep] ζl".
    have [Dep1 Dep2]: vπ a ./ ζl' ∧ vπ b ./ ζl'.
    { apply Hrefl.
      have Heq: vπ (f a b) = λ π, fπ (vπ a π) (vπ b π) by fun_ext=> π; apply Hcomm.
      by rewrite -Heq. }
    iMod ("Eqz1" with "[%//] ζl") as "[Obs1 ζl]".
    iMod ("Eqz2" with "[%//] ζl") as "[Obs2 $]". iModIntro.
    iCombine "Obs1 Obs2" as "Obs'".
    iApply (proph_obs_impl with "Obs'")=> π /= [-> ->]. by rewrite Hcomm. }
  { iNext. iSplitL "Pc1 Q1"; [iExists y1|iExists y2]; iFrame. }
  iMod "Upd" as "_".
  iMod (llftl_sep_split with "LFT Bor") as "[Bor1 Bor2]"; [solve_ndisj|].
  iDestruct (llftl_bor_idx with "Bor1") as (i1) "[IBor1 Tok1]".
  iDestruct (llftl_bor_idx with "Bor2") as (i2) "[IBor2 Tok2]".
  iModIntro. iFrame "Obs G". iSplitL "Vo1 IBor1 Tok1"; [iExists i1|iExists i2]; iFrame.
Qed.

(** ** Reborrowing

    Reborrow at a shorter lifetime [κ'], under a fresh prophecy variable [ζ]
    of the same type (allocated by the caller as a loan at the current value).
    Once [κ'] has ended, we get the original borrow back, with the value
    being the final value of the reborrow. A persistent summary [R] of the
    payload is maintained, so that it is available for the final value
    (even if [κ] has ended). *)
Lemma proph_ibor_reborrow E κ κ' ξ x idx (P: (pv_val ξ) → iProp Σ) (R: (pv_val ξ) → iProp Σ) ζi :
  (∀ x', Persistent (R x')) →
  ↑Nllft ⊆ E →
  llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ κ' ⊑ κ -∗
  □ (∀ x', P x' -∗ R x') -∗ R x -∗
  proph_loan (PrVar (pv_ty ξ) ζi) x -∗ proph_ibor κ ξ x idx P ={E}=∗
    (∃ idx', proph_ibor κ' (PrVar (pv_ty ξ) ζi) x idx' P) ∗
    ([†κ'] ={↑Nllft}=∗ ∃ x' idx'', proph_ibor κ ξ x' idx'' P ∗ ▷ R x' ∗
        ▷ ((.$ (PrVar (pv_ty ξ) ζi)) :== vπ x')).
Proof.
  set ζ := PrVar (pv_ty ξ) ζi.
  iIntros (??) "#LFT #PROPH #UNIQ #κ'⊑κ #PR #R [ζVo ζPc] ((ξVo & Tok) & #IBor)".
  iDestruct (llftl_bor_idx_to_full with "IBor Tok") as "ξBor".
  iMod (llftl_reborrow with "LFT κ'⊑κ ξBor") as "[ξBor ToξBor]"; [done|].
  iMod (llftl_borrow _ κ' (∃ x', .VO[ξ] x' ∗ R x' ∗ .PC[ζ] x' (vπ x'))%I with "LFT [ξVo ζPc]")
    as "[ζBor ToζBig]"; [done| |].
  { iNext. iExists x. iFrame "∗#". }
  iMod (llftl_sep_join with "LFT ξBor ζBor") as "Bor"; [done|].
  iAssert (|={↑Nllft}=> &{κ'} (pbor_body ζ P))%I with "[Bor]" as "Bor".
  { iMod (llftl_bor_acc_atomic with "LFT Bor") as "[[[H1 H2] Back']|[Dead Back']]".
    - iMod (bi.later_exist_except_0 with "H1") as (x1) "(Pc1 & P1)".
      iMod (bi.later_exist_except_0 with "H2") as (x2) "(Vo2 & _ & Pc2)".
      iMod (uniq_strip_later with "Vo2 Pc1") as "(<- & Vo2 & Pc1)".
      iApply ("Back'" with "[Vo2 Pc1] [Pc2 P1]").
      + iNext. iIntros "[H3 _]".
        iMod (bi.later_exist_except_0 with "H3") as (x3) "(Pc3 & P3)".
        iMod (uniq_update ξ x3 (vπ x3) with "UNIQ Vo2 Pc1") as "[Vo4 Pc4]".
        { pose proof (nclose_subseteq NllftUsr 0). solve_ndisj. }
        iDestruct ("PR" with "P3") as "#R3".
        iModIntro. iNext. iSplitL "Pc4 P3"; iExists x3; iFrame "∗#".
      + iNext. iExists x2. iFrame.
    - iMod "Back'". iApply (llftl_bor_fake with "LFT Dead"). { set_solver. } }
  iMod (fupd_mask_mono with "Bor") as "Bor"; [done|].
  iDestruct (llftl_bor_idx with "Bor") as (ζidx) "[#Bor Tok]".
  iModIntro. iSplitL "Tok ζVo".
  { iExists ζidx. iFrame "∗#". }
  iIntros "#†κ'".
  iMod ("ToξBor" with "†κ'") as "ξBor".
  iMod ("ToζBig" with "†κ'") as "Back".
  iMod (bi.later_exist_except_0 with "Back") as (x'') "(>Vo & R'' & Pc)".
  iDestruct (llftl_bor_idx with "ξBor") as (idx'') "[ξBor Tok]".
  iModIntro. iExists x'', idx''. iFrame.
  iNext. iApply (proph_ctrl_eqz with "PROPH Pc").
Qed.

(** ** Extracting persistent information from the payload *)

Lemma proph_ibor_pers E κ ξ x idx (P: (pv_val ξ) → iProp Σ) (R: iProp Σ) :
  Persistent R → ↑Nllft ⊆ E →
  llft_ctx -∗ proph_ibor κ ξ x idx P -∗ (P x -∗ R) ={E}=∗
    (∃ idx', proph_ibor κ ξ x idx' P) ∗ (▷ R ∨ [†κ]).
Proof.
  iIntros (??) "#LFT ((Vo & Tok) & #IBor) Wand".
  iDestruct (llftl_bor_idx_to_full with "IBor Tok") as "Bor".
  iMod (llftl_bor_pers_from_wand2 _ _ _ R with "LFT Bor [Wand] Vo") as "[Bor [R Vo]]";
    [done| |].
  { iIntros "Vo". iDestruct 1 as (x') "(Pc & P)".
    iDestruct (uniq_agree with "Vo Pc") as %<-. by iApply "Wand". }
  iDestruct (llftl_bor_idx with "Bor") as (idx') "[IBor' Tok']".
  iModIntro. iFrame "R". iExists idx'. iFrame.
Qed.

(** ** Unnesting

    The payload [Pout] of an outer prophetic borrow [ξ] (at lifetime [κ])
    contains the timeless part of an inner prophetic borrow [ω] (at
    lifetime [κ'], with [κ ⊑ κ']). We obtain a new prophetic borrow [ζ] at
    lifetime [κ] of the inner payload, starting at the inner value [y]. The
    outer prophecy is resolved to [Hπ] of the final value of [ζ] (and of the
    final value of the inner borrow).

    A persistent summary [S] of the inner payload is recorded for the final
    value of the inner borrow (it is computed by a one-shot update), so that
    the outer payload can be rebuilt. *)
Lemma proph_ibor_unnest E κ κ' ξ x idx (Pout: (pv_val ξ) → iProp Σ)
    ω y idxω (Q: (pv_val ω) → iProp Σ) ζi (R: iProp Σ) (S: (pv_val ω) → iProp Σ)
    (h: pv_val ω → pv_val ξ)
    (Hπ: proj1_sig (pv_ty ω) → proj1_sig (pv_ty ω) → proj1_sig (pv_ty ξ)) G :
  Timeless G → ↑Nllft ∪ ↑prophN ⊆ E →
  Inj (=) (=) h →
  (∀ y', Persistent (S y')) →
  (∀ y' π, vπ (h y') π = Hπ (vπ y' π) (π ω)) →
  (∀ y' ζl, (λ π, Hπ (vπ y' π) (π ω)) ./ ζl → vπ y' ./ ζl) →
  (λ π, Hπ (π (PrVar (pv_ty ω) ζi)) (π ω)) ./ [PrVar (pv_ty ω) ζi; ω] →
  llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗ κ ⊑ κ' -∗
  proph_idx_bor κ' ω idxω Q -∗
  (▷ Pout x ={E}=∗ ▷ proph_bor_tok ω y idxω ∗ ▷ R ∗
     (∀ y', ▷ proph_bor_tok ω y' idxω -∗ ▷ S y' -∗ ▷ R ={↑NllftUsr ∪ ↑NllftUsr2}=∗
        ▷ Pout (h y'))) -∗
  S y -∗ (∀ y', ▷ Q y' ={↑NllftUsr ∪ ↑NllftUsr2}=∗ ▷ Q y' ∗ ▷ S y') -∗
  G -∗ proph_loan (PrVar (pv_ty ω) ζi) y -∗ proph_ibor κ ξ x idx Pout ={E}=∗
    ⟨π, π ξ = Hπ (π (PrVar (pv_ty ω) ζi)) (π ω)⟩ ∗
    (∃ idx', proph_ibor κ (PrVar (pv_ty ω) ζi) y idx' Q) ∗ G.
Proof.
  set ζ := PrVar (pv_ty ω) ζi.
  iIntros (?? Hinj HS Hcomm Hrefl Hdep) "#LFT #PROPH #UNIQ #Gk #κ⊑κ' #ωBor Wand #Sy SWand G [ζVo ζPc]".
  iIntros "((ξVo & ξTok) & #ξIBor)".
  (* Step 1: open the outer borrow, and move the inner observer into it. *)
  iDestruct (llftl_bor_idx_to_full with "ξIBor ξTok") as "ξBor".
  iMod (llftl_bor_acc_guarded with "LFT ξBor Gk G") as "[Body Back]"; [solve_ndisj|].
  iMod (bi.later_exist_except_0 with "Body") as (x') "(ξPc & P)".
  iMod (uniq_strip_later with "ξVo ξPc") as "(<- & ξVo & ξPc)".
  iMod ("Wand" with "P") as "(ωTok & R & Rebuild)".
  iMod "ωTok" as "[ωVo ωIdxTok]".
  iMod (uniq_update ξ (h y) (vπ (h y)) with "UNIQ ξVo ξPc") as "[ξVo ξPc]".
  { pose proof (nclose_subseteq Nllft 0). solve_ndisj. }
  iMod (fupd_mask_subseteq (↑Nllft)) as "Upd"; [solve_ndisj|].
  iMod ("Back" $! ((∃ y', .VO[ω] y' ∗ S y' ∗ .PC[ξ] (h y') (vπ (h y'))) ∗ R ∗ idx_bor_tok idxω)%I
    with "[Rebuild ωVo ξPc R ωIdxTok]") as "[Bor G]".
  { iSplitL "Rebuild"; last first.
    { iNext. iFrame "∗#". }
    iNext. iIntros "(A & R & ωIdxTok)".
    iMod (bi.later_exist_except_0 with "A") as (y') "(ωVo & Sy' & ξPc)".
    iMod ("Rebuild" $! y' with "[ωVo ωIdxTok] Sy' R") as "P".
    { iNext. iFrame. }
    iModIntro. iNext. iExists (h y'). iFrame. }
  iMod "Upd" as "_".
  (* Step 2: unnest the inner borrow. *)
  iMod (llftl_sep_split with "LFT Bor") as "[ABor Bor]"; [solve_ndisj|].
  iMod (llftl_sep_split with "LFT Bor") as "[_ TokBor]"; [solve_ndisj|].
  iMod (llftl_idx_bor_unnest with "LFT ωBor TokBor") as "InBor"; [solve_ndisj|].
  iDestruct (llftl_bor_shorten (κ' ⊓ κ) κ with "[] InBor") as "InBor".
  { iApply llftl_incl_glb; [done|iApply guards_refl]. }
  iMod (llftl_sep_join with "LFT ABor InBor") as "Bor"; [solve_ndisj|].
  (* Step 3: open the combination, pre-resolve the outer prophecy, and
     close with the new borrow [ζ]. *)
  iMod (llftl_bor_acc_guarded with "LFT Bor Gk G") as "[[A InBody] Close]"; [solve_ndisj|].
  iMod (bi.later_exist_except_0 with "A") as (y') "(ωVo & _ & ξPc)".
  iMod (bi.later_exist_except_0 with "InBody") as (y'') "(ωPc & Q)".
  iMod (uniq_strip_later with "ξVo ξPc") as "(%Heq & ξVo & ξPc)".
  apply Hinj in Heq. subst y'.
  iMod (uniq_strip_later with "ωVo ωPc") as "(<- & ωVo & ωPc)".
  iDestruct (uniq_proph_tok with "ζVo ζPc") as "(ζVo & ζtok & ToζPc)".
  iDestruct (uniq_proph_tok with "ωVo ωPc") as "(ωVo & ωtok & ToωPc)".
  have Hmask': ↑uniqN ∪ ↑prophN ⊆ E.
  { pose proof (nclose_subseteq Nllft 0). solve_ndisj. }
  iMod (uniq_preresolve ξ [ζ; ω] (λ π, Hπ (π ζ) (π ω)) 1%Qp _ _ _ E Hmask' Hdep
    with "UNIQ PROPH ξVo ξPc [$ζtok $ωtok]") as "(#Obs & (ζtok & ωtok & _) & ToξPc)".
  { done. }
  iDestruct ("ToζPc" with "ζtok") as "ζPc".
  iDestruct ("ToωPc" with "ωtok") as "ωPc".
  iMod (fupd_mask_subseteq (↑Nllft)) as "Upd"; [solve_ndisj|].
  iMod ("Close" $! (pbor_body ζ Q) with "[ωVo ωPc ToξPc ζPc Q SWand]") as "[Bor G]".
  { iSplitR "ζPc Q"; last first.
    { iNext. iExists y. iFrame. }
    iNext. iIntros "Body".
    iMod (bi.later_exist_except_0 with "Body") as (y3) "(ζPc & Q)".
    iMod ("SWand" with "Q") as "[Q Sy3]".
    iMod (uniq_update ω y3 (vπ y3) with "UNIQ ωVo ωPc") as "[ωVo ωPc]".
    { pose proof (nclose_subseteq NllftUsr 0). solve_ndisj. }
    iDestruct (proph_ctrl_eqz with "PROPH ζPc") as "Eqz".
    iModIntro. iNext. iSplitR "ωPc Q"; last first.
    { iExists y3. iFrame. }
    iExists y3. iFrame "ωVo Sy3". iApply "ToξPc".
    iIntros (E' ζl' q') "[% %Dep] ζl".
    have Dep': vπ y3 ./ ζl'.
    { apply Hrefl.
      have Heq: vπ (h y3) = λ π, Hπ (vπ y3 π) (π ω) by fun_ext=> π; apply Hcomm.
      by rewrite -Heq. }
    iMod ("Eqz" with "[%//] ζl") as "[Obs' $]". iModIntro.
    iApply (proph_obs_impl with "Obs'")=> π /= ->. by rewrite Hcomm. }
  iMod "Upd" as "_".
  iDestruct (llftl_bor_idx with "Bor") as (idx') "[IBor' Tok']".
  iModIntro. iFrame "Obs G". iExists idx'. iFrame.
Qed.

(** ** Guard-level reasoning *)

(** Generic helper: a guard on an existential can be pinned down to a specific
    witness, given an agreement entailment. *)
Lemma guards_exist_eq1 {A} (a' : A) (P Q : iProp Σ) (X : A → iProp Σ) F n1 n2 n :
  (∀ a, ((Q ∧ X a)%I ⊢ ⌜a = a'⌝)%I) →
  (n1 ≤ n) → (n2 ≤ n) →
  (P &&{F;n1}&&> Q) -∗ (P &&{F;n2}&&> (∃ a, X a)) -∗ P &&{F;n}&&> (X a').
Proof.
  intros Hent He1 He2. iIntros "PguardsQ PguardsBig".
  assert ((∃ a : A, X a ∗ ⌜a = a'⌝) ⊣⊢ X a') as Hequiv2.
  { iSplit. { iDestruct 1 as (a) "[A %Heqs]". subst a. iFrame "A". }
    iIntros "X". iExists a'. iFrame. done. }
  leaf_hyp "PguardsQ" laters to n as "PguardsQ'"; first by trivial.
  leaf_hyp "PguardsBig" laters to n as "PguardsBig'"; first by trivial.
  iDestruct (guards_strengthen_exists _ _ _ (λ a, ⌜a = a'⌝)%I with "PguardsQ' PguardsBig'") as "T".
  { intros a. simpl. iIntros "A". by iDestruct (Hent with "A") as "%Heqs". }
  setoid_rewrite Hequiv2. iFrame.
Qed.

Local Lemma guards_pinned_body κ ξ x idx (P: (pv_val ξ) → iProp Σ) R n :
  llft_ctx -∗ proph_idx_bor κ ξ idx P -∗
  (R &&{↑NllftG; n}&&> @[κ]) -∗
  (R &&{↑NllftG; n}&&> proph_bor_tok ξ x idx) -∗
  (R &&{↑NllftG; n+1}&&> (.PC[ξ] x (vπ x) ∗ P x)).
Proof.
  iIntros "#LFT #Bor #Gk #Gtok".
  iDestruct (guards_weaken_rhs_sep_l with "Gtok") as "Gvo".
  iDestruct (guards_weaken_rhs_sep_r with "Gtok") as "Gidxtok".
  iDestruct (llftl_idx_bor_guard' κ idx _ R n with "LFT Bor Gk Gidxtok") as "Ginner".
  iDestruct (guards_weaken_rhs_sep_r with "Ginner") as "Ginner2".
  iDestruct (guards_later_absorb_1 with "Ginner2") as "Ginner3".
  rewrite /pbor_body.
  iApply (guards_exist_eq1 x _ _ (λ x', .PC[ξ] x' (vπ x') ∗ P x')%I _ n (n+1) (n+1)
    with "Gvo Ginner3"); [|lia..].
  intros x'. iIntros "And".
  iDestruct (uniq_and_agree ξ x x' with "[And]") as "%Heq"; [|done].
  iSplit.
  + iDestruct "And" as "[Vo _]". iFrame "Vo".
  + iDestruct "And" as "[_ (Pc & _)]". iFrame "Pc".
Qed.

(** From a guard on (the timeless part of) a prophetic borrow, obtain a guard
    on the payload at the current value. *)
Lemma proph_ibor_guard_payload κ ξ x idx (P: (pv_val ξ) → iProp Σ) R n :
  llft_ctx -∗ proph_idx_bor κ ξ idx P -∗
  (R &&{↑NllftG; n}&&> @[κ]) -∗
  (R &&{↑NllftG; n}&&> proph_bor_tok ξ x idx) -∗
  (R &&{↑NllftG; n+1}&&> P x).
Proof.
  iIntros "#LFT #Bor #Gk #Gtok".
  iDestruct (guards_pinned_body with "LFT Bor Gk Gtok") as "G".
  iApply (guards_weaken_rhs_sep_r with "G").
Qed.

(** From a guard on (the timeless part of) a prophetic borrow, obtain a guard
    on the prophecy token of its variable. *)
Lemma proph_ibor_guard_tok κ ξ x idx (P: (pv_val ξ) → iProp Σ) R n :
  llft_ctx -∗ proph_idx_bor κ ξ idx P -∗
  (R &&{↑NllftG; n}&&> @[κ]) -∗
  (R &&{↑NllftG; n}&&> proph_bor_tok ξ x idx) -∗
  (R &&{↑NllftG; n+1}&&> 1:[ξ]).
Proof.
  iIntros "#LFT #Bor #Gk #Gtok".
  iDestruct (guards_pinned_body with "LFT Bor Gk Gtok") as "G".
  iDestruct (lguards_weaken_later _ _ _ n (n+1) with "Gtok") as "Gtok'"; [lia|].
  iApply (guards_and_point with "Gtok' G").
  - apply proph_tok_point_prop.
  - iIntros "And". iApply proph_ctrl_and_value_obs_entails_proph_tok. iSplit.
    + iDestruct "And" as "[_ (Pc & _)]". iFrame "Pc".
    + iDestruct "And" as "[(Vo & _) _]". iFrame "Vo".
Qed.

(** ** Freezing (resolution)

    Resolve the prophecy variable of a prophetic borrow to its current value.
    The borrow is relinquished; in exchange, the payload (at the current value)
    becomes available under the lifetime token.

    Resolving requires prophecy tokens for the dependencies [ζl] of the current
    value; these are provided in guard form by the [Deps] premise
    (c.f. [ty_guard_proph]). [Deps] is given access to the payload (which it
    must return), and it must also provide the later credits needed for
    opening its guards ([n] laters), plus two more. *)
Lemma proph_ibor_resolve E κ ξ x idx (P: (pv_val ξ) → iProp Σ) (ζl: list proph_var) G n :
  Timeless G →
  ↑Nllft ∪ ↑prophN ⊆ E →
  vπ x ./ ζl →
  llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗
  (G &&{↑NllftG}&&> @[κ]) -∗
  (∀ (W: iProp Σ), (W &&{↑NllftG}&&> @[κ]) -∗ (W &&{↑NllftG}&&> P x) -∗
     ▷ P x ={E}=∗ ▷ P x ∗ £ (n + 2) ∗
     □ (∀ ζ, ⌜ζ ∈ ζl⌝ -∗ (W &&{↑NllftG; n}&&> 1:[ζ]))) -∗
  G -∗ proph_ibor κ ξ x idx P ={E}=∗
    ⟨π, π ξ = vπ x π⟩ ∗ G ∗ (@[κ] &&{↑NllftG; 1}&&> P x).
Proof using All.
  iIntros (Ti ? Hdep).
  iIntros "#LFT #PROPH #UNIQ #Gk Deps G ((Vo & Tok) & #IBor)".
  iMod (frac_split_guard_in_half with "G Gk") as (γ2) "[H2 [H3 [#Ghalf2 #Halfback2]]]".
  { solve_ndisj. }
  iMod (llftl_begin with "LFT") as (κ') "[κ' #κ'end]". { solve_ndisj. }
  iMod (llftl_borrow_shared _ κ' with "H2") as "[#Guards2Lat InhH2]". { solve_ndisj. }
  iDestruct (guards_remove_later_rhs with "Guards2Lat") as "Guard2". iClear "Guards2Lat".
  iDestruct (guards_transitive with "Guard2 Ghalf2") as "Incl".

  iDestruct (llftl_bor_idx_to_full with "IBor Tok") as "Bor".
  have Inh: Inhabited (pv_val ξ). { split. apply x. }
  rewrite {1}/pbor_body.
  iMod (llftl_bor_freeze with "LFT Bor") as (x') "Bor". { set_solver. }

  iMod (llftl_reborrow with "LFT Incl Bor") as "[Bor OriginalBor]". { solve_ndisj. }
  iMod (llftl_bor_acc with "LFT Bor κ'") as "[Inner ForallQ]". { solve_ndisj. }
  iDestruct "Inner" as "(Pc & Payload)".
  iMod (uniq_strip_later with "Vo Pc") as "(<- & Vo & Pc)".
  iMod ("Deps" $! (fractional.half γ2 ∗ P x)%I with "[] [] Payload")
    as "(Payload & [Creditk [Credit1 Credit1']] & #Hallζ)".
  { iApply guards_weaken_lhs_sep_l. iApply "Ghalf2". }
  { iApply guards_weaken_sep_r. }
  iMod (lc_fupd_elim_later with "Credit1' Payload") as "Payload".

  iMod (uniq_resolve_guarded with "Hallζ UNIQ PROPH Vo Pc [H3 Payload]") as "X".
  { pose proof (nclose_subseteq Nllft 0). solve_ndisj. } { apply Hdep. } { iFrame. }
  iMod (lc_fupd_elim_laterN with "Creditk X") as "X". iMod "X".
  iDestruct "X" as "[Obs [Pc [H3 Payload]]]".

  iDestruct ("ForallQ" $! (.PC[ξ] x (vπ x) ∗ P x)%I with "[Pc Payload]") as "ForallQ".
  { iSplitR. { iNext. iIntros "[A dead]". iModIntro. iFrame "A". }
    { iNext. iFrame. } }
  iMod (fupd_mask_mono with "ForallQ") as "[Borrow Al]". { solve_ndisj. }
  iDestruct ("κ'end" with "Al") as "κ'ended".
  iDestruct (lc_step_fupd_elim_later with "Credit1 κ'ended") as "κ'ended".
  iMod (fupd_mask_mono with "κ'ended") as "#κ'ended". { solve_ndisj. }
  iMod ("InhH2" with "κ'ended") as ">H2".
  iDestruct ("Halfback2" with "H2 H3") as "G".
  iMod (fupd_mask_mono with "G") as "G". { solve_ndisj. }

  iDestruct ("OriginalBor" with "κ'ended") as "OriginalBor".
  iMod (fupd_mask_mono with "OriginalBor") as "OriginalBor". { solve_ndisj. }

  (* Turn the recovered borrow into a guard on the payload. *)
  iDestruct (llftl_bor_idx with "OriginalBor") as (idx2) "[#Bor2 Tok2]".
  iMod (llftl_borrow_shared _ κ (idx_bor_tok idx2) with "Tok2") as "[#Glat _]".
  { solve_ndisj. }
  iDestruct (guards_remove_later_rhs with "Glat") as "Gidxtok".
  iDestruct (llftl_idx_bor_guard' κ idx2 _ (@[κ])%I with "LFT Bor2 [] Gidxtok") as "GBor".
  { iApply guards_refl. }
  iDestruct (guards_weaken_rhs_sep_r with "GBor") as "GBor2".
  iDestruct (guards_later_absorb_1 with "GBor2") as "GBor3".
  iDestruct (guards_weaken_rhs_sep_r with "GBor3") as "GBor4".
  iModIntro. iFrame "Obs G GBor4".
Qed.

End proph_bor.

Section proph_loan_intro.
Context `{!invGS Σ, !prophG Σ, !uniqG Σ}.

(** Create a fresh prophecy cell of type [𝔄i] with current value [x]. *)
Lemma proph_loan_intro (𝔄i: syn_typei) E (x: ~~ (`𝔄i)) :
  ↑prophN ∪ ↑uniqN ⊆ E →
  proph_ctx -∗ uniq_ctx ={E}=∗ ∃ ξi, proph_loan (PrVar 𝔄i ξi) x.
Proof.
  move: x. case: 𝔄i => [𝔄 i] x. iIntros (?) "PROPH UNIQ".
  iMod (uniq_intro (𝔄:=𝔄) x (vπ x) with "PROPH UNIQ") as (ξi) "[Vo Pc]"; [done|].
  iModIntro. iExists ξi. rewrite /proph_loan.
  rewrite (proof_irrel (prval_to_inh (𝔄:=𝔄) (vπ x)) i). iFrame.
Qed.
End proph_loan_intro.

Global Opaque proph_loan proph_idx_bor proph_bor_tok proph_ibor proph_bor.

Notation "&proph{ κ ; ξ ➤ x } P" := (proph_bor κ ξ x P)
  (at level 20, format "&proph{ κ ;  ξ  ➤  x }  P") : bi_scope.
Notation "&iproph{ κ , idx ; ξ ➤ x } P" := (proph_ibor κ ξ x idx P)
  (at level 20, format "&iproph{ κ , idx ;  ξ  ➤  x }  P") : bi_scope.
