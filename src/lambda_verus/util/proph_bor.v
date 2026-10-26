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
(** The type of prophecies of a prophecy variable. *)
Notation pv_proph ξ := (proph (proj1_sig (pv_ty ξ))) (only parsing).

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

(** The timeless part of a reserved indexed prophetic borrow: as
    [proph_bor_tok], but the prophecy variable is reserved for [ζl]. *)
Definition proph_bor_tok_rsv ξ (x: pv_val ξ) (idx: Idx) (ζl: list proph_var) : iProp Σ :=
  .VOR[ξ;ζl] x ∗ idx_bor_tok idx.

(** Reserved indexed prophetic borrow (see the section on reservations). *)
Definition proph_ibor_rsv κ ξ (x: pv_val ξ) (idx: Idx) (ζl: list proph_var)
    (P: (pv_val ξ) → iProp Σ) : iProp Σ :=
  proph_bor_tok_rsv ξ x idx ζl ∗ proph_idx_bor κ ξ idx P.

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

(** As [proph_ibor_acc], closing with the same value; this needs no [uniq_ctx]. *)
Lemma proph_ibor_acc_keep E κ ξ x idx (P: (pv_val ξ) → iProp Σ) G :
  Timeless G → ↑Nllft ⊆ E →
  llft_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗
  proph_ibor κ ξ x idx P -∗ G ={E}=∗
    ▷ P x ∗ (▷ P x ={↑Nllft}=∗ proph_ibor κ ξ x idx P ∗ G).
Proof.
  iIntros (??) "#LFT #Gk ((Vo & Tok) & #Bor) G".
  iMod (llftl_bor_idx_acc_guarded with "LFT Bor Tok Gk G") as "[Body Back]"; [done|].
  iMod (bi.later_exist_except_0 with "Body") as (x') "(Pc & P)".
  iMod (uniq_strip_later with "Vo Pc") as "(<- & Vo & Pc)".
  iModIntro. iFrame "P". iIntros "P".
  iMod ("Back" with "[Pc P]") as "[Tok G]".
  { iNext. iExists x. iFrame. }
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

(* The pre-resolving operations (mapping, splitting and unnesting) are only provided
   for generalized prophetic borrows (see below), on which unique borrows are built:
   the pre-resolved variable's controller is then left at the pre-resolved prophecy
   ([uniq_preresolve]). *)

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
    value; these are provided in guard form by the [Deps] premise, given a guard of
    the payload. [Deps] is given access to the payload (which it must return), and it
    must also provide the later credits needed for opening its guards ([n] laters),
    plus two more. (The typing rules use the variant [proph_ibor_resolve_share]
    below, which shares the payload instead of guarding it.) *)
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

(** ** Sharing

    The structural sharing of a prophetic borrow whose timeless part is itself borrowed
    (at [κ']), as done by the sharing predicate of [&uniq]: we obtain a borrow of the
    payload at the current value, at [κ' ⊓ κ], and a guard of the prophecy token. This
    needs no step, since the persistent part of the borrow is given. *)
Lemma proph_bor_tok_share E κ κ' ξ x idx (P: (pv_val ξ) → iProp Σ) :
  ↑Nllft ⊆ E →
  llft_ctx -∗ proph_idx_bor κ ξ idx P -∗ &{κ'} (proph_bor_tok ξ x idx) ={E}=∗
    &{κ' ⊓ κ} (P x) ∗ (@[κ' ⊓ κ] &&{↑NllftG; 1}&&> 1:[ξ]).
Proof.
  iIntros (?) "#LFT #IBor Bor". rewrite /proph_bor_tok /proph_idx_bor.
  iMod (llftl_sep_split with "LFT Bor") as "[VoBor TokBor]"; [done|].
  iMod (llftl_idx_bor_unnest with "LFT IBor TokBor") as "Body"; [done|].
  iDestruct (llftl_bor_shorten _ (κ' ⊓ κ) with "[] Body") as "Body".
  { iApply llftl_incl_glb; [iApply llftl_intersect_incl_r|iApply llftl_intersect_incl_l]. }
  iDestruct (llftl_bor_shorten _ (κ' ⊓ κ) with "[] VoBor") as "VoBor".
  { iApply llftl_intersect_incl_l. }
  iMod (llftl_sep_join with "LFT VoBor Body") as "Bor"; [done|].
  iDestruct (llftl_bor_iff _ _ ((.VO[ξ] x ∗ .PC[ξ] x (vπ x)) ∗ P x) with "[] Bor") as "Bor".
  { iIntros "!> !>". rewrite /pbor_body. iSplit.
    - iIntros "[Vo Body]". iDestruct "Body" as (x') "[Pc P]".
      iDestruct (uniq_agree with "Vo Pc") as %<-. iFrame.
    - iIntros "[[Vo Pc] P]". iFrame "Vo". iExists x. iFrame. }
  iMod (llftl_sep_split with "LFT Bor") as "[TokBor $]"; [done|].
  iMod (llftl_bor_guard with "LFT TokBor") as "#G"; [done|].
  iModIntro. iApply (guards_transitive_left with "G"). leaf_by_sep. iIntros "[Vo Pc]".
  iDestruct (uniq_proph_tok with "Vo Pc") as "(Vo & $ & Pc)". iIntros "tok". iFrame "Vo".
  by iApply "Pc".
Qed.

(** Freezing by sharing: a variant of [proph_ibor_resolve] in which the payload is not
    guarded but given as a borrow to the [Share] premise, which may share it (into the
    persistent [S]) and must provide the guarded tokens of the dependencies [ζl] (for
    any timeless [H] guarding [@[κ]], which it gets and returns), together with the later
    credits for opening these guards. *)
Lemma proph_ibor_resolve_share E κ ξ x idx (P: (pv_val ξ) → iProp Σ) (ζl: list proph_var)
    (S: iProp Σ) G n :
  Timeless G →
  ↑Nllft ∪ ↑prophN ⊆ E →
  vπ x ./ ζl →
  llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗
  (G &&{↑NllftG}&&> @[κ]) -∗
  (∀ (H: iProp Σ), ⌜Timeless H⌝ -∗ (H &&{↑NllftG}&&> @[κ]) -∗ H -∗ &{κ} (P x) ={E}=∗
     H ∗ S ∗ £ n ∗ (∀ ζ, ⌜ζ ∈ ζl⌝ -∗ (H &&{↑NllftG; n}&&> 1:[ζ]))) -∗
  G -∗ proph_ibor κ ξ x idx P ={E}=∗
    ⟨π, π ξ = vπ x π⟩ ∗ G ∗ S.
Proof using All.
  iIntros (Ti ? Hdep) "#LFT #PROPH #UNIQ #Gk Share G ((Vo & Tok) & #IBor)".
  iDestruct (llftl_bor_idx_to_full with "IBor Tok") as "Bor".
  (* Pin the contents to the current value, and split off the payload. *)
  iMod (llftl_bor_acc_guarded with "LFT Bor Gk G") as "[Body Back]"; [solve_ndisj|].
  iMod (bi.later_exist_except_0 with "Body") as (x') "(Pc & P)".
  iMod (uniq_strip_later with "Vo Pc") as "(<- & Vo & Pc)".
  iMod (fupd_mask_subseteq (↑Nllft)) as "Upd"; [solve_ndisj|].
  iMod ("Back" $! (.PC[ξ] x (vπ x) ∗ P x)%I with "[Pc P]") as "[Bor G]".
  { iSplitR "Pc P"; [|iNext; iFrame]. iIntros "!> [Pc P] !> !>". rewrite /pbor_body.
    iExists x. iFrame. }
  iMod "Upd" as "_".
  iMod (llftl_sep_split with "LFT Bor") as "[PcBor PBor]"; [solve_ndisj|].
  (* Share the payload, and resolve with the guarded tokens. *)
  iMod (frac_split_guard_in_half with "G Gk") as (γ) "[H1 [H2 [#Gh #Halfback]]]".
  { solve_ndisj. }
  iMod ("Share" with "[%] Gh H1 PBor") as "(H1 & $ & £ & #Deps)"; [apply _|].
  iMod (llftl_bor_acc_guarded with "LFT PcBor Gh H2") as "[Pc Back]"; [solve_ndisj|].
  iMod (uniq_strip_later with "Vo Pc") as "(_ & Vo & Pc)".
  iMod (uniq_resolve_guarded with "Deps UNIQ PROPH Vo Pc H1") as "X".
  { pose proof (nclose_subseteq Nllft 0). solve_ndisj. } { apply Hdep. }
  iMod (lc_fupd_elim_laterN with "£ X") as "X". iMod "X" as "(Obs & Pc & H1)".
  iMod (fupd_mask_subseteq (↑Nllft)) as "Upd"; [solve_ndisj|].
  iMod ("Back" $! (.PC[ξ] x (vπ x))%I with "[Pc]") as "[_ H2]".
  { iSplitR "Pc"; [|by iNext]. iIntros "!> Pc". by iModIntro. }
  iMod "Upd" as "_".
  iMod (fupd_mask_mono with "(Halfback H1 H2)") as "$"; [solve_ndisj|].
  by iFrame "Obs".
Qed.

(** ** Reservations

    A prophetic borrow can be _reserved_ for a list [ζl] of prophecy variables
    (see [proph_reserved]): its prophecy variable [ξ] is then committed to be
    resolved to a value that may depend on [ζl], and in exchange no tokens for
    [ζl] are needed at resolution time. Reserving keeps the index (and hence
    the persistent part [proph_idx_bor]) unchanged; only the timeless part
    changes, from [proph_bor_tok] to [proph_bor_tok_rsv]. *)

Lemma proph_ibor_rsv_sep κ ξ x idx ζl P :
  proph_ibor_rsv κ ξ x idx ζl P ⊣⊢ proph_bor_tok_rsv ξ x idx ζl ∗ proph_idx_bor κ ξ idx P.
Proof. done. Qed.

Global Instance proph_bor_tok_rsv_timeless ξ x idx ζl :
  Timeless (proph_bor_tok_rsv ξ x idx ζl) := _.

Lemma proph_ibor_rsv_proper κ ξ x idx ζl (P Q: (pv_val ξ) → iProp Σ) :
  (∀ x', P x' ⊣⊢ Q x') → proph_ibor_rsv κ ξ x idx ζl P ⊣⊢ proph_ibor_rsv κ ξ x idx ζl Q.
Proof. intros HPQ. rewrite /proph_ibor_rsv. f_equiv. by apply proph_idx_bor_proper. Qed.

Lemma proph_ibor_rsv_shorten κ κ' ξ x idx ζl (P Q: (pv_val ξ) → iProp Σ) :
  κ' ⊑ κ -∗ ▷ □ (∀ x', P x' ↔ Q x') -∗
  proph_ibor_rsv κ ξ x idx ζl P -∗ proph_ibor_rsv κ' ξ x idx ζl Q.
Proof.
  iIntros "#InLft #Iff [Tok Bor]". iFrame "Tok".
  iApply (proph_idx_bor_shorten with "InLft Iff Bor").
Qed.

(** Reserve the prophecy variable of a prophetic borrow for [ζl] (whose
    tokens are needed now, and returned). *)
Lemma proph_ibor_reserve E κ ξ x idx (P: (pv_val ξ) → iProp Σ) ζl q G :
  Timeless G → ↑Nllft ∪ ↑prophN ⊆ E →
  llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗
  G -∗ q:+[ζl] -∗ proph_ibor κ ξ x idx P ={E}=∗
    proph_ibor_rsv κ ξ x idx ζl P ∗ q:+[ζl] ∗ G.
Proof.
  iIntros (??) "#LFT #PROPH #UNIQ #Gk G ζl ((Vo & Tok) & #Bor)".
  iMod (llftl_bor_idx_acc_guarded with "LFT Bor Tok Gk G") as "[Body Back]"; [solve_ndisj|].
  iMod (bi.later_exist_except_0 with "Body") as (x') "(Pc & P)".
  iMod (uniq_strip_later with "Vo Pc") as "(<- & Vo & Pc)".
  iMod (uniq_reserve with "UNIQ PROPH Vo Pc ζl") as "(Vo & Pc & $)"; [solve_ndisj|].
  iMod (fupd_mask_subseteq (↑Nllft)) as "Upd"; [solve_ndisj|].
  iMod ("Back" with "[Pc P]") as "[Tok $]". { iNext. iExists x. iFrame. }
  iMod "Upd" as "_". iModIntro. iFrame "∗#".
Qed.

(** Give up a reservation. *)
Lemma proph_ibor_unreserve E κ ξ x idx (P: (pv_val ξ) → iProp Σ) ζl G :
  Timeless G → ↑Nllft ∪ ↑prophN ⊆ E →
  llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗
  G -∗ proph_ibor_rsv κ ξ x idx ζl P ={E}=∗ proph_ibor κ ξ x idx P ∗ G.
Proof.
  iIntros (??) "#LFT #PROPH #UNIQ #Gk G ((Vo & Tok) & #Bor)".
  iMod (llftl_bor_idx_acc_guarded with "LFT Bor Tok Gk G") as "[Body Back]"; [solve_ndisj|].
  iMod (bi.later_exist_except_0 with "Body") as (x') "(Pc & P)".
  iMod (uniq_rsv_strip_later with "Vo Pc") as "(<- & Vo & Pc)".
  iMod (uniq_unreserve with "UNIQ PROPH Vo Pc") as "(Vo & Pc)"; [solve_ndisj|].
  iMod (fupd_mask_subseteq (↑Nllft)) as "Upd"; [solve_ndisj|].
  iMod ("Back" with "[Pc P]") as "[Tok $]". { iNext. iExists x. iFrame. }
  iMod "Upd" as "_". iModIntro. iFrame "∗#".
Qed.

(** Extend a reservation by [ζl'] (whose tokens are needed now, and returned). *)
Lemma proph_ibor_reserve_extend E κ ξ x idx (P: (pv_val ξ) → iProp Σ) ζl ζl' q G :
  Timeless G → ↑Nllft ∪ ↑prophN ⊆ E →
  llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗
  G -∗ q:+[ζl'] -∗ proph_ibor_rsv κ ξ x idx ζl P ={E}=∗
    proph_ibor_rsv κ ξ x idx (ζl ++ ζl') P ∗ q:+[ζl'] ∗ G.
Proof.
  iIntros (??) "#LFT #PROPH #UNIQ #Gk G ζl' ((Vo & Tok) & #Bor)".
  iMod (llftl_bor_idx_acc_guarded with "LFT Bor Tok Gk G") as "[Body Back]"; [solve_ndisj|].
  iMod (bi.later_exist_except_0 with "Body") as (x') "(Pc & P)".
  iMod (uniq_rsv_strip_later with "Vo Pc") as "(<- & Vo & Pc)".
  iMod (uniq_reserve_extend with "UNIQ PROPH Vo Pc ζl'") as "(Vo & Pc & $)"; [solve_ndisj|].
  iMod (fupd_mask_subseteq (↑Nllft)) as "Upd"; [solve_ndisj|].
  iMod ("Back" with "[Pc P]") as "[Tok $]". { iNext. iExists x. iFrame. }
  iMod "Upd" as "_". iModIntro. iFrame "∗#".
Qed.

(** Analogue of [proph_ibor_acc] for a reserved prophetic borrow; the
    reservation is kept. *)
Lemma proph_ibor_rsv_acc E κ ξ x idx ζl (P: (pv_val ξ) → iProp Σ) G :
  Timeless G → ↑Nllft ⊆ E →
  llft_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗
  proph_ibor_rsv κ ξ x idx ζl P -∗ G ={E}=∗
    ▷ P x ∗ (∀ x1, ▷ P x1 ={↑Nllft}=∗ proph_ibor_rsv κ ξ x1 idx ζl P ∗ G).
Proof.
  iIntros (??) "#LFT #UNIQ #Gk ((Vo & Tok) & #Bor) G".
  iMod (llftl_bor_idx_acc_guarded with "LFT Bor Tok Gk G") as "[Body Back]"; [done|].
  iMod (bi.later_exist_except_0 with "Body") as (x') "(Pc & P)".
  iMod (uniq_rsv_strip_later with "Vo Pc") as "(<- & Vo & Pc)".
  iModIntro. iFrame "P".
  iIntros (x1) "P".
  iMod (uniq_rsv_update ξ ζl x1 (vπ x1) with "UNIQ Vo Pc") as "[Vo Pc]".
  { pose proof (nclose_subseteq Nllft 0). solve_ndisj. }
  iMod ("Back" with "[Pc P]") as "[Tok G]".
  { iNext. iExists x1. iFrame. }
  iModIntro. iFrame "∗#".
Qed.

Local Lemma guards_pinned_body_rsv κ ξ x idx ζl (P: (pv_val ξ) → iProp Σ) R n :
  llft_ctx -∗ proph_idx_bor κ ξ idx P -∗
  (R &&{↑NllftG; n}&&> @[κ]) -∗
  (R &&{↑NllftG; n}&&> proph_bor_tok_rsv ξ x idx ζl) -∗
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
  iDestruct (uniq_rsv_and_agree ξ ζl x x' with "[And]") as "%Heq"; [|done].
  iSplit.
  + iDestruct "And" as "[Vo _]". iFrame "Vo".
  + iDestruct "And" as "[_ (Pc & _)]". iFrame "Pc".
Qed.

(** Analogue of [proph_ibor_guard_payload] for a reserved prophetic borrow. *)
Lemma proph_ibor_rsv_guard_payload κ ξ x idx ζl (P: (pv_val ξ) → iProp Σ) R n :
  llft_ctx -∗ proph_idx_bor κ ξ idx P -∗
  (R &&{↑NllftG; n}&&> @[κ]) -∗
  (R &&{↑NllftG; n}&&> proph_bor_tok_rsv ξ x idx ζl) -∗
  (R &&{↑NllftG; n+1}&&> P x).
Proof.
  iIntros "#LFT #Bor #Gk #Gtok".
  iDestruct (guards_pinned_body_rsv with "LFT Bor Gk Gtok") as "G".
  iApply (guards_weaken_rhs_sep_r with "G").
Qed.

(** Analogue of [proph_ibor_resolve] for a reserved prophetic borrow: the
    current value may depend on the reserved [ζl], and the [Deps] premise only
    needs to provide guarded tokens for the remaining dependencies [ηl]. *)
Lemma proph_ibor_resolve_reserved E κ ξ x idx ζl (P: (pv_val ξ) → iProp Σ)
    (ηl: list proph_var) G n :
  Timeless G →
  ↑Nllft ∪ ↑prophN ⊆ E →
  vπ x ./ ζl ++ ηl →
  llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗
  (G &&{↑NllftG}&&> @[κ]) -∗
  (∀ (W: iProp Σ), (W &&{↑NllftG}&&> @[κ]) -∗ (W &&{↑NllftG}&&> P x) -∗
     ▷ P x ={E}=∗ ▷ P x ∗ £ (n + 2) ∗
     □ (∀ η, ⌜η ∈ ηl⌝ -∗ (W &&{↑NllftG; n}&&> 1:[η]))) -∗
  G -∗ proph_ibor_rsv κ ξ x idx ζl P ={E}=∗
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
  iMod (uniq_rsv_strip_later with "Vo Pc") as "(<- & Vo & Pc)".
  iMod ("Deps" $! (fractional.half γ2 ∗ P x)%I with "[] [] Payload")
    as "(Payload & [Creditk [Credit1 Credit1']] & #Hallη)".
  { iApply guards_weaken_lhs_sep_l. iApply "Ghalf2". }
  { iApply guards_weaken_sep_r. }
  iMod (lc_fupd_elim_later with "Credit1' Payload") as "Payload".

  iMod (uniq_resolve_reserved_guarded ξ ζl ηl
    with "Hallη UNIQ PROPH Vo Pc [H3 Payload]") as "X".
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

(** ** Generalized prophetic borrows

    In the body of a prophetic borrow, the prophecy controller is fixed to
    [vπ] of the current value. In a _generalized_ prophetic borrow, the
    controller's prophecy [wπ] is arbitrary, and the payload [P x wπ] may
    constrain it. This is used by the place types of [typing/ltype.v], whose
    current state may contain blocked components (which do not have a
    current value): there, [wπ] is the denotation of a place refinement.

    The timeless part is the same [proph_bor_tok] (or [proph_bor_tok_rsv])
    as for ordinary prophetic borrows; an ordinary prophetic borrow is a
    generalized one with payload [λ x wπ, ⌜wπ = vπ x⌝ ∗ P x]
    ([proph_idx_bor_to_gen]). *)

Local Definition pbor_body_gen ξ (P: pv_val ξ → pv_proph ξ → iProp Σ) : iProp Σ :=
  ∃ x' wπ', .PC[ξ] x' wπ' ∗ P x' wπ'.

(** The persistent part of a generalized indexed prophetic borrow. *)
Definition proph_idx_bor_gen κ ξ (idx: Idx) (P: pv_val ξ → pv_proph ξ → iProp Σ) : iProp Σ :=
  &{κ, idx} (pbor_body_gen ξ P).

Global Instance proph_idx_bor_gen_persistent κ ξ idx P :
  Persistent (proph_idx_bor_gen κ ξ idx P) := _.

Lemma proph_idx_bor_gen_shorten κ κ' ξ idx (P Q: pv_val ξ → pv_proph ξ → iProp Σ) :
  κ' ⊑ κ -∗ ▷ □ (∀ x wπ, P x wπ ↔ Q x wπ) -∗
  proph_idx_bor_gen κ ξ idx P -∗ proph_idx_bor_gen κ' ξ idx Q.
Proof.
  iIntros "#InLft #Iff Bor". rewrite /proph_idx_bor_gen.
  iApply (llftl_idx_shorten with "InLft").
  iApply llftl_idx_bor_iff; [|done]. iIntros "!> !>".
  iSplit; iDestruct 1 as (x' wπ') "(Pc & p)"; iExists x', wπ'; iFrame; by iApply "Iff".
Qed.

(** An ordinary prophetic borrow is a generalized one. *)
Lemma proph_idx_bor_to_gen κ ξ idx (P: pv_val ξ → iProp Σ) :
  proph_idx_bor κ ξ idx P ⊣⊢ proph_idx_bor_gen κ ξ idx (λ x wπ, ⌜wπ = vπ x⌝ ∗ P x).
Proof.
  rewrite /proph_idx_bor /proph_idx_bor_gen.
  iSplit; iIntros "Bor"; iApply (llftl_idx_bor_iff with "[] Bor"); iIntros "!> !>"; iSplit.
  - iDestruct 1 as (x') "[Pc P]". iExists x', (vπ x'). by iFrame.
  - iDestruct 1 as (x' wπ') "(Pc & -> & P)". iExists x'. iFrame.
  - iDestruct 1 as (x' wπ') "(Pc & -> & P)". iExists x'. iFrame.
  - iDestruct 1 as (x') "[Pc P]". iExists x', (vπ x'). by iFrame.
Qed.

(** Create a generalized prophetic borrow from a loan, choosing the initial
    controller prophecy [wπ]. After [κ] ends, we recover the contents with
    the controller weakened to an equalizer. *)
Lemma proph_loan_borrow_gen E κ ξ x wπ (P: pv_val ξ → pv_proph ξ → iProp Σ) :
  ↑Nllft ⊆ E →
  llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ proph_loan ξ x -∗ ▷ P x wπ ={E}=∗ ∃ idx,
    proph_bor_tok ξ x idx ∗ proph_idx_bor_gen κ ξ idx P ∗
    ([†κ] ={↑Nllft}=∗ ▷ ∃ x' wπ', ((.$ ξ) :== wπ') ∗ P x' wπ').
Proof.
  iIntros (?) "#LFT #PROPH #UNIQ [Vo Pc] P".
  iMod (uniq_update ξ x wπ with "UNIQ Vo Pc") as "[Vo Pc]".
  { pose proof (nclose_subseteq Nllft 0). solve_ndisj. }
  iMod (llftl_borrow E κ (pbor_body_gen ξ P) with "LFT [Pc P]") as "[Bor Back]"; [done| |].
  { iNext. iExists x, wπ. iFrame. }
  iDestruct (llftl_bor_idx with "Bor") as (idx) "[Bor Tok]".
  iModIntro. iExists idx. iFrame. iIntros "†κ".
  iMod ("Back" with "†κ") as "Body". iModIntro. iNext.
  iDestruct "Body" as (x' wπ') "[Pc P]". iExists x', wπ'. iFrame.
  iApply (proph_ctrl_eqz with "PROPH Pc").
Qed.

(** Open a generalized prophetic borrow (guarded by a lifetime token). The
    closer may change the value and the controller prophecy, and may also
    change the payload (giving a fresh index), provided the new payload can
    be shifted back into the old one once the lifetime has ended. *)
Lemma proph_idx_bor_gen_acc E κ ξ x idx (P: pv_val ξ → pv_proph ξ → iProp Σ) G :
  Timeless G → ↑Nllft ⊆ E →
  llft_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗
  proph_bor_tok ξ x idx -∗ proph_idx_bor_gen κ ξ idx P -∗ G ={E}=∗ ∃ wπ,
    ▷ P x wπ ∗
    (∀ x1 wπ1 (Q: pv_val ξ → pv_proph ξ → iProp Σ),
       ▷ (∀ x2 wπ2, ▷ Q x2 wπ2 ={↑NllftUsr ∪ ↑NllftUsr2}=∗ ▷ P x2 wπ2) -∗ ▷ Q x1 wπ1
       ={↑Nllft}=∗ ∃ idx', proph_bor_tok ξ x1 idx' ∗ proph_idx_bor_gen κ ξ idx' Q ∗ G).
Proof.
  iIntros (??) "#LFT #UNIQ #Gk [Vo Tok] #Bor G".
  iDestruct (llftl_bor_idx_to_full with "Bor Tok") as "Bor'".
  iMod (llftl_bor_acc_guarded with "LFT Bor' Gk G") as "[Body Back]"; [done|].
  iMod (bi.later_exist_except_0 with "Body") as (x') "Body".
  iMod (bi.later_exist_except_0 with "Body") as (wπ') "[Pc P]".
  iMod (uniq_strip_later with "Vo Pc") as "(<- & Vo & Pc)".
  iModIntro. iExists wπ'. iFrame "P".
  iIntros (x1 wπ1 Q) "VS Q".
  iMod (uniq_update ξ x1 wπ1 with "UNIQ Vo Pc") as "[Vo Pc]".
  { pose proof (nclose_subseteq Nllft 0). solve_ndisj. }
  iMod ("Back" $! (pbor_body_gen ξ Q) with "[VS Pc Q]") as "[Bor2 G]".
  { iSplitL "VS".
    - iNext. iIntros "Body".
      iMod (bi.later_exist_except_0 with "Body") as (x2) "Body".
      iMod (bi.later_exist_except_0 with "Body") as (wπ2) "[Pc Q]".
      iMod ("VS" with "Q") as "P". iModIntro. iNext. iExists x2, wπ2. iFrame.
    - iNext. iExists x1, wπ1. iFrame. }
  iDestruct (llftl_bor_idx with "Bor2") as (idx') "[IBor Tok]".
  iModIntro. iExists idx'. iFrame "∗#".
Qed.

(** Analogue of [proph_idx_bor_gen_acc] for a reserved observer; the
    reservation is kept. *)
Lemma proph_idx_bor_gen_rsv_acc E κ ξ x idx ζl (P: pv_val ξ → pv_proph ξ → iProp Σ) G :
  Timeless G → ↑Nllft ⊆ E →
  llft_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗
  proph_bor_tok_rsv ξ x idx ζl -∗ proph_idx_bor_gen κ ξ idx P -∗ G ={E}=∗ ∃ wπ,
    ▷ P x wπ ∗
    (∀ x1 wπ1 (Q: pv_val ξ → pv_proph ξ → iProp Σ),
       ▷ (∀ x2 wπ2, ▷ Q x2 wπ2 ={↑NllftUsr ∪ ↑NllftUsr2}=∗ ▷ P x2 wπ2) -∗ ▷ Q x1 wπ1
       ={↑Nllft}=∗ ∃ idx', proph_bor_tok_rsv ξ x1 idx' ζl ∗ proph_idx_bor_gen κ ξ idx' Q ∗ G).
Proof.
  iIntros (??) "#LFT #UNIQ #Gk [Vo Tok] #Bor G".
  iDestruct (llftl_bor_idx_to_full with "Bor Tok") as "Bor'".
  iMod (llftl_bor_acc_guarded with "LFT Bor' Gk G") as "[Body Back]"; [done|].
  iMod (bi.later_exist_except_0 with "Body") as (x') "Body".
  iMod (bi.later_exist_except_0 with "Body") as (wπ') "[Pc P]".
  iMod (uniq_rsv_strip_later with "Vo Pc") as "(<- & Vo & Pc)".
  iModIntro. iExists wπ'. iFrame "P".
  iIntros (x1 wπ1 Q) "VS Q".
  iMod (uniq_rsv_update ξ ζl x1 wπ1 with "UNIQ Vo Pc") as "[Vo Pc]".
  { pose proof (nclose_subseteq Nllft 0). solve_ndisj. }
  iMod ("Back" $! (pbor_body_gen ξ Q) with "[VS Pc Q]") as "[Bor2 G]".
  { iSplitL "VS".
    - iNext. iIntros "Body".
      iMod (bi.later_exist_except_0 with "Body") as (x2) "Body".
      iMod (bi.later_exist_except_0 with "Body") as (wπ2) "[Pc Q]".
      iMod ("VS" with "Q") as "P". iModIntro. iNext. iExists x2, wπ2. iFrame.
    - iNext. iExists x1, wπ1. iFrame. }
  iDestruct (llftl_bor_idx with "Bor2") as (idx') "[IBor Tok]".
  iModIntro. iExists idx'. iFrame "∗#".
Qed.

(** Give up a reservation of a generalized prophetic borrow. *)
Lemma proph_idx_bor_gen_unreserve E κ ξ x idx ζl (P: pv_val ξ → pv_proph ξ → iProp Σ) G :
  Timeless G → ↑Nllft ∪ ↑prophN ⊆ E →
  llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗
  G -∗ proph_bor_tok_rsv ξ x idx ζl -∗ proph_idx_bor_gen κ ξ idx P ={E}=∗
    proph_bor_tok ξ x idx ∗ G.
Proof.
  iIntros (??) "#LFT #PROPH #UNIQ #Gk G (Vo & Tok) #Bor".
  iMod (llftl_bor_idx_acc_guarded with "LFT Bor Tok Gk G") as "[Body Back]"; [solve_ndisj|].
  iMod (bi.later_exist_except_0 with "Body") as (x') "Body".
  iMod (bi.later_exist_except_0 with "Body") as (wπ') "[Pc P]".
  iMod (uniq_rsv_strip_later with "Vo Pc") as "(<- & Vo & Pc)".
  iMod (uniq_unreserve with "UNIQ PROPH Vo Pc") as "(Vo & Pc)"; [solve_ndisj|].
  iMod (fupd_mask_subseteq (↑Nllft)) as "Upd"; [solve_ndisj|].
  iMod ("Back" with "[Pc P]") as "[Tok $]". { iNext. iExists x, wπ'. iFrame. }
  iMod "Upd" as "_". iModIntro. iFrame.
Qed.

(** Reserve the prophecy variable of a generalized prophetic borrow for [ζl]
    (whose tokens are needed now, and returned). *)
Lemma proph_idx_bor_gen_reserve E κ ξ x idx ζl q (P: pv_val ξ → pv_proph ξ → iProp Σ) G :
  Timeless G → ↑Nllft ∪ ↑prophN ⊆ E →
  llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗
  G -∗ q:+[ζl] -∗ proph_bor_tok ξ x idx -∗ proph_idx_bor_gen κ ξ idx P ={E}=∗
    proph_bor_tok_rsv ξ x idx ζl ∗ q:+[ζl] ∗ G.
Proof.
  iIntros (??) "#LFT #PROPH #UNIQ #Gk G ζl (Vo & Tok) #Bor".
  iMod (llftl_bor_idx_acc_guarded with "LFT Bor Tok Gk G") as "[Body Back]"; [solve_ndisj|].
  iMod (bi.later_exist_except_0 with "Body") as (x') "Body".
  iMod (bi.later_exist_except_0 with "Body") as (wπ') "[Pc P]".
  iMod (uniq_strip_later with "Vo Pc") as "(<- & Vo & Pc)".
  iMod (uniq_reserve with "UNIQ PROPH Vo Pc ζl") as "(Vo & Pc & $)"; [solve_ndisj|].
  iMod (fupd_mask_subseteq (↑Nllft)) as "Upd"; [solve_ndisj|].
  iMod ("Back" with "[Pc P]") as "[Tok $]". { iNext. iExists x, wπ'. iFrame. }
  iMod "Upd" as "_". iModIntro. iFrame.
Qed.

(** Open a reserved generalized prophetic borrow, closing it with the same payload
    and index, and extending the reservation by [ζl']. The tokens for [ζl'] are needed
    when closing; they are then handed to a view shift that produces the new contents
    (e.g. by putting them back into a fresh loan that the new contents borrow). *)
Lemma proph_idx_bor_gen_rsv_acc_ext E κ ξ x idx ζl (P: pv_val ξ → pv_proph ξ → iProp Σ) G :
  Timeless G → ↑Nllft ∪ ↑prophN ⊆ E →
  llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗
  proph_bor_tok_rsv ξ x idx ζl -∗ proph_idx_bor_gen κ ξ idx P -∗ G ={E}=∗ ∃ wπ,
    ▷ P x wπ ∗
    (∀ x1 wπ1 ζl' q (R: iProp Σ), q:+[ζl'] -∗ (q:+[ζl'] ={E}=∗ ▷ P x1 wπ1 ∗ R) ={E}=∗
       proph_bor_tok_rsv ξ x1 idx (ζl ++ ζl') ∗ G ∗ R).
Proof.
  iIntros (??) "#LFT #PROPH #UNIQ #Gk [Vo Tok] #Bor G".
  iMod (llftl_bor_idx_acc_guarded with "LFT Bor Tok Gk G") as "[Body Back]"; [solve_ndisj|].
  iMod (bi.later_exist_except_0 with "Body") as (x') "Body".
  iMod (bi.later_exist_except_0 with "Body") as (wπ') "[Pc P]".
  iMod (uniq_rsv_strip_later with "Vo Pc") as "(<- & Vo & Pc)".
  iModIntro. iExists wπ'. iFrame "P".
  iIntros (x1 wπ1 ζl' q R) "ζl' VS".
  iMod (uniq_reserve_extend with "UNIQ PROPH Vo Pc ζl'") as "(Vo & Pc & ζl')"; [solve_ndisj|].
  iMod (uniq_rsv_update ξ (ζl ++ ζl') x1 wπ1 with "UNIQ Vo Pc") as "[Vo Pc]".
  { pose proof (nclose_subseteq Nllft 0). solve_ndisj. }
  iMod ("VS" with "ζl'") as "[P $]".
  iMod (fupd_mask_subseteq (↑Nllft)) as "Upd"; [solve_ndisj|].
  iMod ("Back" with "[Pc P]") as "[Tok $]". { iNext. iExists x1, wπ1. iFrame. }
  iMod "Upd" as "_". iModIntro. iFrame.
Qed.


(** Non-expansiveness / properness of generalized prophetic borrows in the payload. *)

Local Lemma pbor_body_gen_proper ξ (P Q: pv_val ξ → pv_proph ξ → iProp Σ) :
  (∀ x wπ, P x wπ ⊣⊢ Q x wπ) → pbor_body_gen ξ P ⊣⊢ pbor_body_gen ξ Q.
Proof. intros HPQ. rewrite /pbor_body_gen. by setoid_rewrite HPQ. Qed.

Local Lemma pbor_body_gen_ne ξ (P Q: pv_val ξ → pv_proph ξ → iProp Σ) n :
  (∀ x wπ, P x wπ ≡{n}≡ Q x wπ) → pbor_body_gen ξ P ≡{n}≡ pbor_body_gen ξ Q.
Proof. intros HPQ. rewrite /pbor_body_gen. do 2 (f_equiv=> ?). f_equiv. apply HPQ. Qed.

Lemma proph_idx_bor_gen_proper κ ξ idx (P Q: pv_val ξ → pv_proph ξ → iProp Σ) :
  (∀ x wπ, P x wπ ⊣⊢ Q x wπ) → proph_idx_bor_gen κ ξ idx P ⊣⊢ proph_idx_bor_gen κ ξ idx Q.
Proof. intros HPQ. rewrite /proph_idx_bor_gen. f_equiv. by apply pbor_body_gen_proper. Qed.

Lemma proph_idx_bor_gen_ne κ ξ idx (P Q: pv_val ξ → pv_proph ξ → iProp Σ) n :
  (∀ x wπ, P x wπ ≡{n}≡ Q x wπ) → proph_idx_bor_gen κ ξ idx P ≡{n}≡ proph_idx_bor_gen κ ξ idx Q.
Proof. intros HPQ. rewrite /proph_idx_bor_gen. f_equiv. by apply pbor_body_gen_ne. Qed.

Lemma proph_idx_bor_gen_contractive κ ξ idx (P Q: pv_val ξ → pv_proph ξ → iProp Σ) n :
  (∀ x wπ, dist_later n (P x wπ) (Q x wπ)) →
  proph_idx_bor_gen κ ξ idx P ≡{n}≡ proph_idx_bor_gen κ ξ idx Q.
Proof.
  intros HPQ. rewrite /proph_idx_bor_gen. apply idx_bor_contractive.
  destruct n as [|n]. { split. lia. }
  apply dist_later_S. apply pbor_body_gen_ne => x wπ.
  have := HPQ x wπ. rewrite dist_later_S. done.
Qed.

(** Unfolding lemmas. Clients that build their own operations on generalized
    prophetic borrows directly on top of the lifetime logic and the observer/controller
    ghost state (the unique borrows of [typing/uniq_util.v], whose operations depend on
    the structure of their payloads) can use these. *)

Lemma proph_idx_bor_gen_unfold κ ξ idx (P: pv_val ξ → pv_proph ξ → iProp Σ) :
  proph_idx_bor_gen κ ξ idx P ⊣⊢ &{κ, idx} (∃ x' wπ', .PC[ξ] x' wπ' ∗ P x' wπ').
Proof. done. Qed.

Lemma proph_bor_tok_unfold ξ x idx : proph_bor_tok ξ x idx ⊣⊢ .VO[ξ] x ∗ idx_bor_tok idx.
Proof. done. Qed.

Lemma proph_bor_tok_rsv_unfold ξ x idx ζl :
  proph_bor_tok_rsv ξ x idx ζl ⊣⊢ .VOR[ξ;ζl] x ∗ idx_bor_tok idx.
Proof. done. Qed.

Lemma proph_loan_unfold ξ x : proph_loan ξ x ⊣⊢ .VO[ξ] x ∗ .PC[ξ] x (vπ x).
Proof. done. Qed.

(** As [proph_loan_borrow_gen], the lender getting the controller (instead of an
    equalizer). *)
Lemma proph_loan_borrow_gen_pc E κ ξ x wπ (P: pv_val ξ → pv_proph ξ → iProp Σ) :
  ↑Nllft ⊆ E →
  llft_ctx -∗ uniq_ctx -∗ proph_loan ξ x -∗ ▷ P x wπ ={E}=∗ ∃ idx,
    proph_bor_tok ξ x idx ∗ proph_idx_bor_gen κ ξ idx P ∗
    ([†κ] ={↑Nllft}=∗ ▷ ∃ x' wπ', .PC[ξ] x' wπ' ∗ P x' wπ').
Proof.
  iIntros (?) "#LFT #UNIQ [Vo Pc] P".
  iMod (uniq_update ξ x wπ with "UNIQ Vo Pc") as "[Vo Pc]".
  { pose proof (nclose_subseteq Nllft 0). solve_ndisj. }
  iMod (llftl_borrow E κ (pbor_body_gen ξ P) with "LFT [Pc P]") as "[Bor Back]"; [done| |].
  { iNext. iExists x, wπ. iFrame. }
  iDestruct (llftl_bor_idx with "Bor") as (idx) "[Bor Tok]".
  iModIntro. iExists idx. iFrame.
Qed.

(** Open a generalized prophetic borrow, closing it with the same payload and index;
    the value and the controller prophecy may change. *)
Lemma proph_idx_bor_gen_acc_idx E κ ξ x idx (P: pv_val ξ → pv_proph ξ → iProp Σ) G :
  Timeless G → ↑Nllft ⊆ E →
  llft_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗
  proph_bor_tok ξ x idx -∗ proph_idx_bor_gen κ ξ idx P -∗ G ={E}=∗ ∃ wπ,
    ▷ P x wπ ∗ (∀ x1 wπ1, ▷ P x1 wπ1 ={↑Nllft}=∗ proph_bor_tok ξ x1 idx ∗ G).
Proof.
  iIntros (??) "#LFT #UNIQ #Gk [Vo Tok] #Bor G".
  iMod (llftl_bor_idx_acc_guarded with "LFT Bor Tok Gk G") as "[Body Back]"; [done|].
  iMod (bi.later_exist_except_0 with "Body") as (x') "Body".
  iMod (bi.later_exist_except_0 with "Body") as (wπ') "[Pc P]".
  iMod (uniq_strip_later with "Vo Pc") as "(<- & Vo & Pc)".
  iModIntro. iExists wπ'. iFrame "P".
  iIntros (x1 wπ1) "P".
  iMod (uniq_update ξ x1 wπ1 with "UNIQ Vo Pc") as "[Vo Pc]".
  { pose proof (nclose_subseteq Nllft 0). solve_ndisj. }
  iMod ("Back" with "[Pc P]") as "[Tok G]". { iNext. iExists x1, wπ1. iFrame. }
  iModIntro. iFrame.
Qed.

(** As [proph_idx_bor_gen_acc_idx], closing with the same value and controller
    prophecy; this needs no [uniq_ctx]. *)
Lemma proph_idx_bor_gen_acc_idx_keep E κ ξ x idx (P: pv_val ξ → pv_proph ξ → iProp Σ) G :
  Timeless G → ↑Nllft ⊆ E →
  llft_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗
  proph_bor_tok ξ x idx -∗ proph_idx_bor_gen κ ξ idx P -∗ G ={E}=∗ ∃ wπ,
    ▷ P x wπ ∗ (▷ P x wπ ={↑Nllft}=∗ proph_bor_tok ξ x idx ∗ G).
Proof.
  iIntros (??) "#LFT #Gk [Vo Tok] #Bor G".
  iMod (llftl_bor_idx_acc_guarded with "LFT Bor Tok Gk G") as "[Body Back]"; [done|].
  iMod (bi.later_exist_except_0 with "Body") as (x') "Body".
  iMod (bi.later_exist_except_0 with "Body") as (wπ') "[Pc P]".
  iMod (uniq_strip_later with "Vo Pc") as "(<- & Vo & Pc)".
  iModIntro. iExists wπ'. iFrame "P". iIntros "P".
  iMod ("Back" with "[Pc P]") as "[Tok G]". { iNext. iExists x, wπ'. iFrame. }
  iModIntro. iFrame.
Qed.

(** As [proph_idx_bor_gen_acc_idx], for a reserved observer; the reservation is
    kept. *)
Lemma proph_idx_bor_gen_rsv_acc_idx E κ ξ x idx ζl (P: pv_val ξ → pv_proph ξ → iProp Σ) G :
  Timeless G → ↑Nllft ⊆ E →
  llft_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗
  proph_bor_tok_rsv ξ x idx ζl -∗ proph_idx_bor_gen κ ξ idx P -∗ G ={E}=∗ ∃ wπ,
    ▷ P x wπ ∗ (∀ x1 wπ1, ▷ P x1 wπ1 ={↑Nllft}=∗ proph_bor_tok_rsv ξ x1 idx ζl ∗ G).
Proof.
  iIntros (??) "#LFT #UNIQ #Gk [Vo Tok] #Bor G".
  iMod (llftl_bor_idx_acc_guarded with "LFT Bor Tok Gk G") as "[Body Back]"; [done|].
  iMod (bi.later_exist_except_0 with "Body") as (x') "Body".
  iMod (bi.later_exist_except_0 with "Body") as (wπ') "[Pc P]".
  iMod (uniq_rsv_strip_later with "Vo Pc") as "(<- & Vo & Pc)".
  iModIntro. iExists wπ'. iFrame "P".
  iIntros (x1 wπ1) "P".
  iMod (uniq_rsv_update ξ ζl x1 wπ1 with "UNIQ Vo Pc") as "[Vo Pc]".
  { pose proof (nclose_subseteq Nllft 0). solve_ndisj. }
  iMod ("Back" with "[Pc P]") as "[Tok G]". { iNext. iExists x1, wπ1. iFrame. }
  iModIntro. iFrame.
Qed.


(** Open a generalized prophetic borrow with a lifetime token, closing it with a
    possibly different payload (resulting in a fresh index). The new payload has to be
    shifted back into the old one once the lifetime has ended. *)
Lemma proph_idx_bor_gen_acc_rebody E κ ξ x idx (P Q: pv_val ξ → pv_proph ξ → iProp Σ) :
  ↑Nllft ⊆ E →
  llft_ctx -∗ uniq_ctx -∗ @[κ] -∗
  proph_bor_tok ξ x idx -∗ proph_idx_bor_gen κ ξ idx P ={E}=∗ ▷ ◇ (∃ wπ,
    P x wπ ∗
    (∀ x1 wπ1, ▷ Q x1 wπ1 -∗
       ▷ (∀ x2 wπ2, ▷ Q x2 wπ2 ∗ [†κ] ={↑NllftUsr ∪ ↑NllftUsr2}=∗ ▷ P x2 wπ2)
       ={↑Nllft}=∗
       ∃ idx', proph_bor_tok ξ x1 idx' ∗ proph_idx_bor_gen κ ξ idx' Q ∗ @[κ])).
Proof.
  iIntros (?) "#LFT #UNIQ κ [Vo Tok] #IBor".
  iDestruct (llftl_bor_idx_to_full with "IBor Tok") as "Bor".
  iMod (llftl_bor_acc with "LFT Bor κ") as "[Body Back]"; [done|].
  iModIntro. iNext.
  iDestruct "Body" as (x' wπ) "(Pc & P)".
  iMod (uniq_strip_later with "Vo Pc") as "(<- & Vo & Pc)".
  iModIntro. iExists wπ. iFrame "P".
  iIntros (x1 wπ1) "Q W".
  iMod (uniq_update ξ x1 wπ1 with "UNIQ Vo Pc") as "[Vo Pc]".
  { pose proof (nclose_subseteq Nllft 0). solve_ndisj. }
  iAssert (▷ (▷ pbor_body_gen ξ Q ∗ [†κ] ={↑NllftUsr ∪ ↑NllftUsr2}=∗ ▷ pbor_body_gen ξ P))%I
    with "[W]" as "VS".
  { iNext. iIntros "[Body †κ]".
    iMod (bi.later_exist_except_0 with "Body") as (x2) "Body".
    iMod (bi.later_exist_except_0 with "Body") as (wπ2) "(Pc2 & Q)".
    iMod ("W" $! x2 wπ2 with "[$Q $†κ]") as "P".
    iModIntro. iNext. iExists x2, wπ2. iFrame. }
  iMod ("Back" $! (pbor_body_gen ξ Q) with "[VS Pc Q]") as "[Bor κ]".
  { iFrame "VS". iNext. iExists x1, wπ1. iFrame. }
  iDestruct (llftl_bor_idx with "Bor") as (idx') "[IBor' Tok']".
  iModIntro. iExists idx'. iFrame.
Qed.

(** As [proph_idx_bor_gen_acc_rebody], with a lifetime guard instead of the token; the
    closing view shift does not get [[†κ]]. *)
Lemma proph_idx_bor_gen_acc_rebody_guarded E κ ξ x idx (P Q: pv_val ξ → pv_proph ξ → iProp Σ) G :
  Timeless G → ↑Nllft ⊆ E →
  llft_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗
  proph_bor_tok ξ x idx -∗ proph_idx_bor_gen κ ξ idx P -∗ G ={E}=∗ ∃ wπ,
    ▷ P x wπ ∗
    (∀ x1 wπ1, ▷ Q x1 wπ1 -∗
       ▷ (∀ x2 wπ2, ▷ Q x2 wπ2 ={↑NllftUsr ∪ ↑NllftUsr2}=∗ ▷ P x2 wπ2)
       ={↑Nllft}=∗
       ∃ idx', proph_bor_tok ξ x1 idx' ∗ proph_idx_bor_gen κ ξ idx' Q ∗ G).
Proof.
  iIntros (??) "#LFT #UNIQ #Gk [Vo Tok] #IBor G".
  iDestruct (llftl_bor_idx_to_full with "IBor Tok") as "Bor".
  iMod (llftl_bor_acc_guarded with "LFT Bor Gk G") as "[Body Back]"; [done|].
  iMod (bi.later_exist_except_0 with "Body") as (x') "Body".
  iMod (bi.later_exist_except_0 with "Body") as (wπ) "[Pc P]".
  iMod (uniq_strip_later with "Vo Pc") as "(<- & Vo & Pc)".
  iModIntro. iExists wπ. iFrame "P".
  iIntros (x1 wπ1) "Q W".
  iMod (uniq_update ξ x1 wπ1 with "UNIQ Vo Pc") as "[Vo Pc]".
  { pose proof (nclose_subseteq Nllft 0). solve_ndisj. }
  iAssert (▷ (▷ pbor_body_gen ξ Q ={↑NllftUsr ∪ ↑NllftUsr2}=∗ ▷ pbor_body_gen ξ P))%I
    with "[W]" as "VS".
  { iNext. iIntros "Body".
    iMod (bi.later_exist_except_0 with "Body") as (x2) "Body".
    iMod (bi.later_exist_except_0 with "Body") as (wπ2) "(Pc2 & Q)".
    iMod ("W" $! x2 wπ2 with "Q") as "P".
    iModIntro. iNext. iExists x2, wπ2. iFrame. }
  iMod ("Back" $! (pbor_body_gen ξ Q) with "[VS Pc Q]") as "[Bor G]".
  { iFrame "VS". iNext. iExists x1, wπ1. iFrame. }
  iDestruct (llftl_bor_idx with "Bor") as (idx') "[IBor' Tok']".
  iModIntro. iExists idx'. iFrame.
Qed.

(** ** Mapping, splitting and reborrowing generalized prophetic borrows *)

(** Replace a generalized prophetic borrow [ξ] by a fresh one [ζ] (allocated by the
    caller as a loan), pre-resolving [ξ] to [fπ] of [ζ]. The old payload is
    transformed into the new one (with a guard for [κ]), at a chosen controller
    prophecy [wζ] for [ζ]. Once [κ] has ended, the final contents of [ζ] (with its
    controller) have to be shifted back into the old payload, at the controller
    prophecy [fπ] of [ζ] (the controller of [ξ] is left at the pre-resolved
    prophecy, see [uniq_preresolve]). *)
Lemma proph_idx_bor_gen_map E κ ξ x idx (P: pv_val ξ → pv_proph ξ → iProp Σ)
    ζ y (Q: pv_val ζ → pv_proph ζ → iProp Σ)
    (fπ: proj1_sig (pv_ty ζ) → proj1_sig (pv_ty ξ)) G :
  Timeless G → ↑Nllft ∪ ↑prophN ⊆ E →
  llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗
  (∀ G' wπ, ⌜Timeless G'⌝ -∗ (G' &&{↑NllftG}&&> @[κ]) -∗ G' -∗ ▷ P x wπ ={E}=∗
     G' ∗ ∃ wζ, ▷ Q y wζ ∗
     (∀ y' wζ', ▷ .PC[ζ] y' wζ' -∗ ▷ Q y' wζ' ={↑NllftUsr ∪ ↑NllftUsr2}=∗
        ▷ ∃ x', P x' (λ π, fπ (π ζ)))) -∗
  G -∗ proph_loan ζ y -∗ proph_bor_tok ξ x idx -∗ proph_idx_bor_gen κ ξ idx P ={E}=∗
    ⟨π, π ξ = fπ (π ζ)⟩ ∗
    (∃ idx', proph_bor_tok ζ y idx' ∗ proph_idx_bor_gen κ ζ idx' Q) ∗ G.
Proof using All.
  iIntros (Ti Hmask) "#LFT #PROPH #UNIQ #Gk Wand G [ζVo ζPc] [Vo Tok] #IBor".
  iDestruct (uniq_proph_tok with "ζVo ζPc") as "(ζVo & ζtok & ToζPc)".
  have Hdep: (λ π, fπ (π ζ)) ./ [ζ].
  { apply (proph_dep_constr fπ (λ π, π ζ)). apply proph_dep_one. }
  (* Half of [G] opens the borrow, the other half is for the transformation. *)
  iMod (frac_split_guard_in_half with "G Gk") as (γ) "[H1 [H2 [#Gh #Halfback]]]";
    [solve_ndisj|].
  iDestruct (llftl_bor_idx_to_full with "IBor Tok") as "Bor".
  iMod (llftl_bor_acc_guarded with "LFT Bor Gh H1") as "[Body Back]"; [solve_ndisj|].
  iMod (bi.later_exist_except_0 with "Body") as (x') "Body".
  iMod (bi.later_exist_except_0 with "Body") as (wπ) "(Pc & P)".
  iMod (uniq_strip_later with "Vo Pc") as "(<- & Vo & Pc)".
  iMod (uniq_preresolve ξ [ζ] (λ π, fπ (π ζ)) 1%Qp with "UNIQ PROPH Vo Pc [ζtok]")
    as "(#Obs & ζtok & ToPc)"; [solve_ndisj|done|by rewrite big_sepL_singleton|].
  rewrite big_sepL_singleton.
  iDestruct ("ToζPc" with "ζtok") as "ζPc".
  iMod ("Wand" with "[%] Gh H2 P") as "(H2 & %wζ & Q & Back')"; [apply _|].
  iMod (uniq_update ζ y wζ with "UNIQ ζVo ζPc") as "[ζVo ζPc]".
  { pose proof (nclose_subseteq Nllft 0). solve_ndisj. }
  iMod (fupd_mask_subseteq (↑Nllft)) as "Upd"; [solve_ndisj|].
  iMod ("Back" $! (pbor_body_gen ζ Q) with "[Back' ToPc ζPc Q]") as "[Bor H1]".
  { iSplitR "ζPc Q"; [|iNext; iExists y, wζ; iFrame].
    iNext. iIntros "Body".
    iMod (bi.later_exist_except_0 with "Body") as (y') "Body".
    iMod (bi.later_exist_except_0 with "Body") as (wζ') "[ζPc' Q']".
    iMod ("Back'" with "ζPc' Q'") as "P". iModIntro. iNext.
    iDestruct "P" as (x1) "P". iExists x1, (λ π, fπ (π ζ)). iFrame "P".
    iApply "ToPc". }
  iMod "Upd" as "_".
  iMod (fupd_mask_mono with "(Halfback H1 H2)") as "G"; [solve_ndisj|].
  iDestruct (llftl_bor_idx with "Bor") as (idx') "[IBor' Tok']".
  iModIntro. iFrame "Obs G". iExists idx'. iFrame.
Qed.

(** As [proph_idx_bor_gen_map], for a borrow whose prophecy variable [ξ] is reserved
    for [ζl]: [ξ] is pre-resolved to a prophecy [uπ] that may depend on [ζl] (whose
    tokens are not needed) and on the fresh [ζ]. *)
Lemma proph_idx_bor_gen_map_rsv E κ ξ x idx ζl (P: pv_val ξ → pv_proph ξ → iProp Σ)
    ζ y (Q: pv_val ζ → pv_proph ζ → iProp Σ) (uπ: pv_proph ξ) G :
  Timeless G → ↑Nllft ∪ ↑prophN ⊆ E → uπ ./ ζl ++ [ζ] →
  llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗
  (∀ G' wπ, ⌜Timeless G'⌝ -∗ (G' &&{↑NllftG}&&> @[κ]) -∗ G' -∗ ▷ P x wπ ={E}=∗
     G' ∗ ∃ wζ, ▷ Q y wζ ∗
     (∀ y' wζ', ▷ .PC[ζ] y' wζ' -∗ ▷ Q y' wζ' ={↑NllftUsr ∪ ↑NllftUsr2}=∗
        ▷ ∃ x', P x' uπ)) -∗
  G -∗ proph_loan ζ y -∗ proph_bor_tok_rsv ξ x idx ζl -∗ proph_idx_bor_gen κ ξ idx P ={E}=∗
    ⟨π, π ξ = uπ π⟩ ∗
    (∃ idx', proph_bor_tok ζ y idx' ∗ proph_idx_bor_gen κ ζ idx' Q) ∗ G.
Proof using All.
  iIntros (Ti Hmask Hdep) "#LFT #PROPH #UNIQ #Gk Wand G [ζVo ζPc] [Vo Tok] #IBor".
  iDestruct (uniq_proph_tok with "ζVo ζPc") as "(ζVo & ζtok & ToζPc)".
  iMod (frac_split_guard_in_half with "G Gk") as (γ) "[H1 [H2 [#Gh #Halfback]]]";
    [solve_ndisj|].
  iDestruct (llftl_bor_idx_to_full with "IBor Tok") as "Bor".
  iMod (llftl_bor_acc_guarded with "LFT Bor Gh H1") as "[Body Back]"; [solve_ndisj|].
  iMod (bi.later_exist_except_0 with "Body") as (x') "Body".
  iMod (bi.later_exist_except_0 with "Body") as (wπ) "(Pc & P)".
  iMod (uniq_rsv_strip_later with "Vo Pc") as "(<- & Vo & Pc)".
  iMod (uniq_preresolve_reserved ξ ζl [ζ] uπ 1%Qp with "UNIQ PROPH Vo Pc [ζtok]")
    as "(#Obs & ζtok & ToPc)"; [solve_ndisj|done|by rewrite big_sepL_singleton|].
  rewrite big_sepL_singleton.
  iDestruct ("ToζPc" with "ζtok") as "ζPc".
  iMod ("Wand" with "[%] Gh H2 P") as "(H2 & %wζ & Q & Back')"; [apply _|].
  iMod (uniq_update ζ y wζ with "UNIQ ζVo ζPc") as "[ζVo ζPc]".
  { pose proof (nclose_subseteq Nllft 0). solve_ndisj. }
  iMod (fupd_mask_subseteq (↑Nllft)) as "Upd"; [solve_ndisj|].
  iMod ("Back" $! (pbor_body_gen ζ Q) with "[Back' ToPc ζPc Q]") as "[Bor H1]".
  { iSplitR "ζPc Q"; [|iNext; iExists y, wζ; iFrame].
    iNext. iIntros "Body".
    iMod (bi.later_exist_except_0 with "Body") as (y') "Body".
    iMod (bi.later_exist_except_0 with "Body") as (wζ') "[ζPc' Q']".
    iMod ("Back'" with "ζPc' Q'") as "P". iModIntro. iNext.
    iDestruct "P" as (x1) "P". iExists x1, uπ. iFrame "P".
    iApply "ToPc". }
  iMod "Upd" as "_".
  iMod (fupd_mask_mono with "(Halfback H1 H2)") as "G"; [solve_ndisj|].
  iDestruct (llftl_bor_idx with "Bor") as (idx') "[IBor' Tok']".
  iModIntro. iFrame "Obs G". iExists idx'. iFrame.
Qed.


(** Replace a generalized prophetic borrow [ξ] by two fresh ones [ζ1], [ζ2]
    (allocated by the caller as loans), pre-resolving [ξ] to [fπ] of them (see
    [proph_idx_bor_gen_map]). *)
Lemma proph_idx_bor_gen_split E κ ξ x idx (P: pv_val ξ → pv_proph ξ → iProp Σ)
    ζ1 y1 (Q1: pv_val ζ1 → pv_proph ζ1 → iProp Σ) ζ2 y2 (Q2: pv_val ζ2 → pv_proph ζ2 → iProp Σ)
    (fπ: proj1_sig (pv_ty ζ1) → proj1_sig (pv_ty ζ2) → proj1_sig (pv_ty ξ)) G :
  Timeless G → ↑Nllft ∪ ↑prophN ⊆ E →
  llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗
  (∀ G' wπ, ⌜Timeless G'⌝ -∗ (G' &&{↑NllftG}&&> @[κ]) -∗ G' -∗ ▷ P x wπ ={E}=∗
     G' ∗ ∃ w1 w2, ▷ Q1 y1 w1 ∗ ▷ Q2 y2 w2 ∗
     (∀ y1' w1' y2' w2', ▷ .PC[ζ1] y1' w1' -∗ ▷ Q1 y1' w1' -∗
        ▷ .PC[ζ2] y2' w2' -∗ ▷ Q2 y2' w2' ={↑NllftUsr ∪ ↑NllftUsr2}=∗
        ▷ ∃ x', P x' (λ π, fπ (π ζ1) (π ζ2)))) -∗
  G -∗ proph_loan ζ1 y1 -∗ proph_loan ζ2 y2 -∗
  proph_bor_tok ξ x idx -∗ proph_idx_bor_gen κ ξ idx P ={E}=∗
    ⟨π, π ξ = fπ (π ζ1) (π ζ2)⟩ ∗
    (∃ i1, proph_bor_tok ζ1 y1 i1 ∗ proph_idx_bor_gen κ ζ1 i1 Q1) ∗
    (∃ i2, proph_bor_tok ζ2 y2 i2 ∗ proph_idx_bor_gen κ ζ2 i2 Q2) ∗ G.
Proof using All.
  iIntros (Ti Hmask) "#LFT #PROPH #UNIQ #Gk Wand G [Vo1 Pc1] [Vo2 Pc2] [Vo Tok] #IBor".
  iDestruct (uniq_proph_tok with "Vo1 Pc1") as "(Vo1 & tok1 & ToPc1)".
  iDestruct (uniq_proph_tok with "Vo2 Pc2") as "(Vo2 & tok2 & ToPc2)".
  have Hdep: (λ π, fπ (π ζ1) (π ζ2)) ./ [ζ1; ζ2].
  { apply (proph_dep_constr2 fπ (λ π, π ζ1) (λ π, π ζ2) [ζ1] [ζ2]); apply proph_dep_one. }
  iMod (frac_split_guard_in_half with "G Gk") as (γ) "[H1 [H2 [#Gh #Halfback]]]";
    [solve_ndisj|].
  iDestruct (llftl_bor_idx_to_full with "IBor Tok") as "Bor".
  iMod (llftl_bor_acc_guarded with "LFT Bor Gh H1") as "[Body Back]"; [solve_ndisj|].
  iMod (bi.later_exist_except_0 with "Body") as (x') "Body".
  iMod (bi.later_exist_except_0 with "Body") as (wπ) "(Pc & P)".
  iMod (uniq_strip_later with "Vo Pc") as "(<- & Vo & Pc)".
  iMod (uniq_preresolve ξ [ζ1; ζ2] (λ π, fπ (π ζ1) (π ζ2)) 1%Qp
    with "UNIQ PROPH Vo Pc [tok1 tok2]") as "(#Obs & toks & ToPc)";
    [solve_ndisj|done|by iFrame|].
  iDestruct "toks" as "(tok1 & tok2 & _)".
  iDestruct ("ToPc1" with "tok1") as "Pc1".
  iDestruct ("ToPc2" with "tok2") as "Pc2".
  iMod ("Wand" with "[%] Gh H2 P") as "(H2 & %w1 & %w2 & Q1 & Q2 & Back')"; [apply _|].
  iMod (uniq_update ζ1 y1 w1 with "UNIQ Vo1 Pc1") as "[Vo1 Pc1]".
  { pose proof (nclose_subseteq Nllft 0). solve_ndisj. }
  iMod (uniq_update ζ2 y2 w2 with "UNIQ Vo2 Pc2") as "[Vo2 Pc2]".
  { pose proof (nclose_subseteq Nllft 0). solve_ndisj. }
  iMod (fupd_mask_subseteq (↑Nllft)) as "Upd"; [solve_ndisj|].
  iMod ("Back" $! (pbor_body_gen ζ1 Q1 ∗ pbor_body_gen ζ2 Q2)%I
    with "[Back' ToPc Pc1 Q1 Pc2 Q2]") as "[Bor H1]".
  { iSplitR "Pc1 Q1 Pc2 Q2"; last first.
    { iNext. iSplitL "Pc1 Q1"; [iExists y1, w1|iExists y2, w2]; iFrame. }
    iNext. iIntros "[Body1 Body2]".
    iMod (bi.later_exist_except_0 with "Body1") as (y1') "Body1".
    iMod (bi.later_exist_except_0 with "Body1") as (w1') "[Pc1' Q1']".
    iMod (bi.later_exist_except_0 with "Body2") as (y2') "Body2".
    iMod (bi.later_exist_except_0 with "Body2") as (w2') "[Pc2' Q2']".
    iMod ("Back'" with "Pc1' Q1' Pc2' Q2'") as "P". iModIntro. iNext.
    iDestruct "P" as (x1) "P". iExists x1, (λ π, fπ (π ζ1) (π ζ2)). iFrame "P".
    iApply "ToPc". }
  iMod "Upd" as "_".
  iMod (fupd_mask_mono with "(Halfback H1 H2)") as "G"; [solve_ndisj|].
  iMod (llftl_sep_split with "LFT Bor") as "[Bor1 Bor2]"; [solve_ndisj|].
  iDestruct (llftl_bor_idx with "Bor1") as (i1) "[IBor1 Tok1]".
  iDestruct (llftl_bor_idx with "Bor2") as (i2) "[IBor2 Tok2]".
  iModIntro. iFrame "Obs G". iSplitL "Vo1 IBor1 Tok1"; [iExists i1|iExists i2]; iFrame.
Qed.

(** Reborrow a generalized prophetic borrow at a shorter lifetime [κ'], under a fresh
    prophecy variable [ζ] of the same type (allocated by the caller as a loan at a value
    [y] with [F y = x]; [F] maps the values of the reborrow to values of the original
    borrow). The payload of the reborrow is [Q]: the old payload (at any
    controller prophecy), together with the initial [R], is transformed into [Q] (at
    the controller prophecy of [R]), with an update at the empty mask, and the caller
    provides a way
    back, once [κ'] has ended, which also gives [R] at the final value. When [κ'] has
    ended, the original borrow is given back, at the final value of the reborrow
    (and with its final controller prophecy, see [R]), together with [R] and the
    reborrow's controller. *)
Lemma proph_idx_bor_gen_reborrow E κ κ' ξ x idx (P Q R: pv_val ξ → pv_proph ξ → iProp Σ)
    (F: pv_val ξ → pv_val ξ) y ζi :
  ↑Nllft ⊆ E → F y = x →
  llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ κ' ⊑ κ -∗
  (∀ wπ wζ, ▷ P x wπ -∗ ▷ R y wζ ={∅}=∗ ▷ Q y wζ ∗
     ▷ (∀ x2 wπ2, ▷ Q x2 wπ2 -∗ [†κ'] ={↑NllftUsr ∪ ↑NllftUsr2}=∗
        ▷ P (F x2) wπ2 ∗ ▷ R x2 wπ2)) -∗
  R y (vπ y) -∗
  proph_loan (PrVar (pv_ty ξ) ζi) y -∗ proph_bor_tok ξ x idx -∗ proph_idx_bor_gen κ ξ idx P
  ={E}=∗
    (∃ idx', proph_bor_tok (PrVar (pv_ty ξ) ζi) y idx' ∗
      proph_idx_bor_gen κ' (PrVar (pv_ty ξ) ζi) idx' Q) ∗
    ([†κ'] ={↑Nllft}=∗ ∃ x' wπ' idx'', proph_bor_tok ξ (F x') idx'' ∗
        proph_idx_bor_gen κ ξ idx'' P ∗ ▷ (.PC[PrVar (pv_ty ξ) ζi] x' wπ' ∗ R x' wπ')).
Proof.
  set ζ := PrVar (pv_ty ξ) ζi.
  iIntros (? HF) "#LFT #PROPH #UNIQ #κ'⊑κ Spl R [ζVo ζPc] [ξVo Tok] #IBor".
  iDestruct (llftl_bor_idx_to_full with "IBor Tok") as "ξBor".
  iMod (llftl_reborrow with "LFT κ'⊑κ ξBor") as "[ξBor ToξBor]"; [done|].
  iMod (llftl_borrow _ κ' (∃ x' wπ', .VO[ξ] (F x') ∗ .PC[ζ] x' wπ' ∗ R x' wπ')%I
    with "LFT [ξVo ζPc R]") as "[ζBor ToζBig]"; [done| |].
  { iNext. iExists y, (vπ y). rewrite HF. iFrame. }
  iMod (llftl_sep_join with "LFT ξBor ζBor") as "Bor"; [done|].
  iAssert (|={↑Nllft}=> &{κ'} (pbor_body_gen ζ Q) ∗ .VO[ζ] y)%I with "[Bor Spl ζVo]"
    as "Bor".
  { iMod (llftl_bor_acc_atomic with "LFT Bor") as "[[[H1 H2] Back']|[Dead Back']]".
    - iMod (bi.later_exist_except_0 with "H1") as (x1) "H1".
      iMod (bi.later_exist_except_0 with "H1") as (w1) "(Pc1 & P1)".
      iMod (bi.later_exist_except_0 with "H2") as (x2) "H2".
      iMod (bi.later_exist_except_0 with "H2") as (w2) "(Vo2 & Pc2 & R2)".
      iMod (uniq_strip_later with "Vo2 Pc1") as "(<- & Vo2 & Pc1)".
      iMod (uniq_strip_later with "ζVo Pc2") as "(<- & ζVo & Pc2)".
      rewrite HF.
      iMod ("Spl" with "P1 R2") as "[Q Bk]". iFrame "ζVo".
      iApply ("Back'" with "[Vo2 Pc1 Bk] [Pc2 Q]").
      + iNext. iIntros "[Body †κ']".
        iMod (bi.later_exist_except_0 with "Body") as (x3) "Body".
        iMod (bi.later_exist_except_0 with "Body") as (w3) "(Pc3 & Q3)".
        iMod ("Bk" with "Q3 †κ'") as "[P3 R3]".
        iMod (uniq_update ξ (F x3) w3 with "UNIQ Vo2 Pc1") as "[Vo4 Pc4]".
        { pose proof (nclose_subseteq NllftUsr 0). solve_ndisj. }
        iModIntro. iNext. iSplitL "Pc4 P3"; [iExists (F x3), w3|iExists x3, w3]; iFrame.
      + iNext. iExists y, w2. iFrame.
    - iMod "Back'". iFrame "ζVo". iApply (llftl_bor_fake with "LFT Dead"). { set_solver. } }
  iMod (fupd_mask_mono with "Bor") as "[Bor ζVo]"; [done|].
  iDestruct (llftl_bor_idx with "Bor") as (ζidx) "[#Bor Tok]".
  iModIntro. iSplitL "Tok ζVo".
  { iExists ζidx. iFrame "∗#". }
  iIntros "#†κ'".
  iMod ("ToξBor" with "†κ'") as "ξBor".
  iMod ("ToζBig" with "†κ'") as "Back".
  iMod (bi.later_exist_except_0 with "Back") as (x'') "Back".
  iMod (bi.later_exist_except_0 with "Back") as (w'') "(>Vo & Pc & R)".
  iDestruct (llftl_bor_idx with "ξBor") as (idx'') "[ξBor Tok]".
  iModIntro. iExists x'', w'', idx''. iFrame.
Qed.


(** ** Freezing and sharing generalized prophetic borrows *)

(** Freezing by sharing (see [proph_ibor_resolve_share]), for a generalized
    prophetic borrow whose payload can be pinned to the current value: [Pin] takes
    the payload (at the current controller prophecy) to [P0], with a way back to the
    payload at the controller [vπ x]. *)
Lemma proph_idx_bor_gen_resolve_share E κ ξ x idx (P: pv_val ξ → pv_proph ξ → iProp Σ)
    (P0: iProp Σ) (ζl: list proph_var) (S: iProp Σ) G n :
  Timeless G →
  ↑Nllft ∪ ↑prophN ⊆ E →
  vπ x ./ ζl →
  llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗
  (G &&{↑NllftG}&&> @[κ]) -∗
  (∀ wπ, ▷ P x wπ -∗ ◇ (▷ P0 ∗ ▷ (P0 -∗ P x (vπ x)))) -∗
  (∀ (H: iProp Σ), ⌜Timeless H⌝ -∗ (H &&{↑NllftG}&&> @[κ]) -∗ H -∗ &{κ} P0 ={E}=∗
     H ∗ S ∗ £ n ∗ (∀ ζ, ⌜ζ ∈ ζl⌝ -∗ (H &&{↑NllftG; n}&&> 1:[ζ]))) -∗
  G -∗ proph_bor_tok ξ x idx -∗ proph_idx_bor_gen κ ξ idx P ={E}=∗
    ⟨π, π ξ = vπ x π⟩ ∗ G ∗ S.
Proof using All.
  iIntros (Ti ? Hdep) "#LFT #PROPH #UNIQ #Gk Pin Share G (Vo & Tok) #IBor".
  iDestruct (llftl_bor_idx_to_full with "IBor Tok") as "Bor".
  (* Pin the contents to the current value, and split off the payload. *)
  iMod (llftl_bor_acc_guarded with "LFT Bor Gk G") as "[Body Back]"; [solve_ndisj|].
  iMod (bi.later_exist_except_0 with "Body") as (x') "Body".
  iMod (bi.later_exist_except_0 with "Body") as (wπ) "(Pc & P)".
  iMod (uniq_strip_later with "Vo Pc") as "(<- & Vo & Pc)".
  iMod ("Pin" with "P") as "[P0 Inv]".
  iMod (uniq_update ξ x (vπ x) with "UNIQ Vo Pc") as "[Vo Pc]".
  { pose proof (nclose_subseteq Nllft 0). solve_ndisj. }
  iMod (fupd_mask_subseteq (↑Nllft)) as "Upd"; [solve_ndisj|].
  iMod ("Back" $! (.PC[ξ] x (vπ x) ∗ P0)%I with "[Pc P0 Inv]") as "[Bor G]".
  { iSplitR "Pc P0"; [|iNext; iFrame]. iNext. iIntros "[Pc P0]". iModIntro. iNext.
    rewrite /pbor_body_gen. iExists x, (vπ x). iFrame. by iApply "Inv". }
  iMod "Upd" as "_".
  iMod (llftl_sep_split with "LFT Bor") as "[PcBor PBor]"; [solve_ndisj|].
  (* Share the payload, and resolve with the guarded tokens. *)
  iMod (frac_split_guard_in_half with "G Gk") as (γ) "[H1 [H2 [#Gh #Halfback]]]".
  { solve_ndisj. }
  iMod ("Share" with "[%] Gh H1 PBor") as "(H1 & $ & £ & #Deps)"; [apply _|].
  iMod (llftl_bor_acc_guarded with "LFT PcBor Gh H2") as "[Pc Back]"; [solve_ndisj|].
  iMod (uniq_strip_later with "Vo Pc") as "(_ & Vo & Pc)".
  iMod (uniq_resolve_guarded with "Deps UNIQ PROPH Vo Pc H1") as "X".
  { pose proof (nclose_subseteq Nllft 0). solve_ndisj. } { apply Hdep. }
  iMod (lc_fupd_elim_laterN with "£ X") as "X". iMod "X" as "(Obs & Pc & H1)".
  iMod (fupd_mask_subseteq (↑Nllft)) as "Upd"; [solve_ndisj|].
  iMod ("Back" $! (.PC[ξ] x (vπ x))%I with "[Pc]") as "[_ H2]".
  { iSplitR "Pc"; [|by iNext]. iIntros "!> Pc". by iModIntro. }
  iMod "Upd" as "_".
  iMod (fupd_mask_mono with "(Halfback H1 H2)") as "$"; [solve_ndisj|].
  by iFrame "Obs".
Qed.

(** The structural sharing of a generalized prophetic borrow whose timeless part is
    itself borrowed (at [κ']), together with some [Ex] that pins the payload: we obtain
    a borrow of [P0] at [κ' ⊓ κ], and a guard of the prophecy token. *)
Lemma proph_bor_tok_share_gen E κ κ' ξ x idx (P: pv_val ξ → pv_proph ξ → iProp Σ)
    (Ex P0: iProp Σ) (Φ: pv_proph ξ → iProp Σ) :
  ↑Nllft ⊆ E →
  llft_ctx -∗ proph_idx_bor_gen κ ξ idx P -∗
  ▷ □ (∀ wπ, (Ex ∗ P x wπ) ↔ (Φ wπ ∗ P0)) -∗
  &{κ'} (proph_bor_tok ξ x idx ∗ Ex) ={E}=∗
    &{κ' ⊓ κ} P0 ∗ (@[κ' ⊓ κ] &&{↑NllftG; 1}&&> 1:[ξ]).
Proof.
  iIntros (?) "#LFT #IBor #Iff Bor". rewrite /proph_bor_tok /proph_idx_bor_gen.
  iDestruct (llftl_bor_iff _ _ ((.VO[ξ] x ∗ Ex) ∗ idx_bor_tok idx) with "[] Bor") as "Bor".
  { iIntros "!> !>". iSplit; [iIntros "[[$ $] $]"|iIntros "[[$ $] $]"]. }
  iMod (llftl_sep_split with "LFT Bor") as "[VoBor TokBor]"; [done|].
  iMod (llftl_idx_bor_unnest with "LFT IBor TokBor") as "Body"; [done|].
  iDestruct (llftl_bor_shorten _ (κ' ⊓ κ) with "[] Body") as "Body".
  { iApply llftl_incl_glb; [iApply llftl_intersect_incl_r|iApply llftl_intersect_incl_l]. }
  iDestruct (llftl_bor_shorten _ (κ' ⊓ κ) with "[] VoBor") as "VoBor".
  { iApply llftl_intersect_incl_l. }
  iMod (llftl_sep_join with "LFT VoBor Body") as "Bor"; [done|].
  iDestruct (llftl_bor_iff _ _ ((.VO[ξ] x ∗ ∃ wπ, .PC[ξ] x wπ ∗ Φ wπ) ∗ P0) with "[] Bor")
    as "Bor".
  { iIntros "!> !>". rewrite /pbor_body_gen. iSplit.
    - iIntros "[[Vo Ex] Body]". iDestruct "Body" as (x' wπ) "[Pc P]".
      iDestruct (uniq_agree with "Vo Pc") as %<-.
      iDestruct ("Iff" $! wπ) as "[I1 _]".
      iDestruct ("I1" with "[$Ex $P]") as "[Φ $]". iFrame "Vo". iExists wπ. iFrame.
    - iIntros "[[Vo (%wπ & Pc & Φ)] P0]".
      iDestruct ("Iff" $! wπ) as "[_ I2]".
      iDestruct ("I2" with "[$Φ $P0]") as "[Ex P]".
      iFrame "Vo Ex". iExists x, wπ. iFrame. }
  iMod (llftl_sep_split with "LFT Bor") as "[TokBor $]"; [done|].
  iMod (llftl_bor_guard with "LFT TokBor") as "#G"; [done|].
  iModIntro. iApply (guards_transitive_left with "G"). leaf_by_sep.
  iIntros "[Vo (%wπ & Pc & Φ)]".
  iDestruct (uniq_proph_tok with "Vo Pc") as "(Vo & $ & Pc)". iIntros "tok". iFrame "Vo".
  iExists wπ. iFrame. by iApply "Pc".
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

Global Opaque proph_loan proph_idx_bor proph_bor_tok proph_ibor proph_bor
  proph_bor_tok_rsv proph_ibor_rsv proph_idx_bor_gen.

Notation "&proph{ κ ; ξ ➤ x } P" := (proph_bor κ ξ x P)
  (at level 20, format "&proph{ κ ;  ξ  ➤  x }  P") : bi_scope.
Notation "&iproph{ κ , idx ; ξ ➤ x } P" := (proph_ibor κ ξ x idx P)
  (at level 20, format "&iproph{ κ , idx ;  ξ  ➤  x }  P") : bi_scope.
Notation "&iproph_rsv{ κ , idx ; ξ ➤ x ; ζl } P" := (proph_ibor_rsv κ ξ x idx ζl P)
  (at level 20, format "&iproph_rsv{ κ , idx ;  ξ  ➤  x ;  ζl }  P") : bi_scope.
