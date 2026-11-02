From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants.
From lrust.prophecy Require Import syn_type prophecy.
From lrust.lifetime Require Import lifetime_full guarded_bor.
From lrust.typing Require Import uniq_cmra.
From lrust.util Require Import proph_bor.
From guarding Require Import guard.
From guarding.lib Require Import fractional.
Set Default Proof Using "Type".

(** * Prophetic lends of guarded mutable borrows (L3p)

This is the prophetic companion of [guarded_bor.v] (phase 2 of
[design_docs/guarded-mutable-borrows-plan.md]; see "Outcome: phase 2" there). The prophetic
lend (L3p) is (L3) for the generalized prophetic borrows of [util/proph_bor.v]: given the
owner's share guard of [gmb_a γ s] at [κ], a prophetic borrow at [κ] whose payload holds the
permission [gmb_b γ t] gives a prophetic borrow at [κ] whose payload holds the contents
[c s t].
- [gmb_lend_proph] keeps the prophecy variable [ξ] (and its current value and controller
  prophecy): the payload is changed in place (a special opening of the borrow, with
  [proph_idx_bor_gen_acc_rebody_special_guarded]). Resolving the borrow resolves [ξ].
- [gmb_lend_proph_map] replaces the borrow by a fresh one of another prophecy variable [ζ]
  (allocated by the caller as a loan), whose values may be of another type, and
  pre-resolves [ξ] to [fπ] of [ζ] ([proph_idx_bor_gen_map_special]): resolving the new
  borrow resolves the old one consistently. This is the shape of the typing rule of
  [PCell::borrow_mut], which maps the value [(g, x)] of the permission to the value [x] of
  the contents.

The payloads are arbitrary; the caller splits the permission off the old payload and builds
the new payload from the contents. The way back, run by the back-map of the borrow when [κ]
ends (mask [↑NllftUsr ∪ ↑NllftUsr2]), must give back the contents _eagerly_ from the final
new payload: the back-map returns the contents to the instance ([gmb_lend_stop]), so that
the owner can move after [κ] without the lender (L4). [gmb_lend_proph_map_lazy] instead
stores the final contents lazily, with a settle law ([gmb_lend_stop_lazy]); this is the
form for the bodies of [&uniq], whose bytes can be forced without a guard (see the plan,
"Outcome: phase 2b"). *)

Section GuardedBorProph.
  Context `{!invGS Σ, !prophG Σ, !uniqG Σ, !llft_logicGS Σ, !frac_logicG Σ}.
  Context {S T : Type}.
  Context `{!gmbG Σ S T}.
  Context (c : S → T → iProp Σ).
  Context `{c_timeless : !∀ s t, Timeless (c s t)}.

  Implicit Types (γ : gmb_name) (s : S) (t : T) (κ : lft) (ξ ζ : proph_var).

  (** (L3p), keeping the prophecy variable, its value and its controller prophecy. *)
  Lemma gmb_lend_proph E κ ξ x idx (P Q: pv_val ξ → pv_proph ξ → iProp Σ) G γ s n :
    Timeless G → ↑Nllft ⊆ E →
    llft_ctx -∗ uniq_ctx -∗ gmb_inv c γ -∗
    (@[κ] &&{↑NllftG; n}&&> gmb_a γ s) -∗ £ n -∗ £ (1 + n) -∗
    (G &&{↑NllftG}&&> @[κ]) -∗
    (∀ wπ, ▷ P x wπ ={E}=∗ ∃ t, gmb_b γ t ∗ (c s t ={E}=∗ ▷ Q x wπ ∗
       (∀ x2 wπ2, ▷ Q x2 wπ2 ={↑NllftUsr ∪ ↑NllftUsr2}=∗
          ∃ t', ▷ c s t' ∗ (gmb_b γ t' -∗ ▷ P x2 wπ2)))) -∗
    G -∗ proph_bor_tok ξ x idx -∗ proph_idx_bor_gen κ ξ idx P ={E}=∗
      ∃ idx', proph_bor_tok ξ x idx' ∗ proph_idx_bor_gen κ ξ idx' Q ∗ G.
  Proof using c_timeless.
    iIntros (HG Hmask) "#LFT #UNIQ #GI #Ga Lc Pre #Gk Wand G Tok IBor".
    iMod (proph_idx_bor_gen_acc_rebody_special_guarded _ _ _ _ _ P Q
            with "LFT UNIQ Gk Tok IBor G") as (wπ) "(P & Sp & Close)"; [done|].
    iMod ("Wand" with "P") as (t) "[B ToQ]".
    iMod (gmb_lend_start with "LFT GI Ga Lc Pre Sp B") as "[C Lent]"; [done..|].
    iMod ("ToQ" with "C") as "[Q Back]".
    iMod (fupd_mask_subseteq (↑Nllft)) as "Upd"; [done|].
    iMod ("Close" $! x wπ with "Q [Back Lent]") as "R".
    { iNext. iIntros (x2 wπ2) "Q".
      iMod ("Back" with "Q") as (t') "[>C ToP]".
      iMod (gmb_lend_stop with "GI Lent C") as "[B $]".
      iModIntro. by iApply "ToP". }
    by iMod "Upd" as "_".
  Qed.

  (** (L3p), replacing the borrow by a fresh one of [ζ], to which [ξ] is pre-resolved. *)
  Lemma gmb_lend_proph_map E κ ξ x idx (P: pv_val ξ → pv_proph ξ → iProp Σ)
      ζ y (Q: pv_val ζ → pv_proph ζ → iProp Σ)
      (fπ: proj1_sig (pv_ty ζ) → proj1_sig (pv_ty ξ)) G γ s n :
    Timeless G → ↑Nllft ∪ ↑prophN ⊆ E →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ gmb_inv c γ -∗
    (@[κ] &&{↑NllftG; n}&&> gmb_a γ s) -∗ £ n -∗ £ (1 + n) -∗
    (G &&{↑NllftG}&&> @[κ]) -∗
    (∀ G' wπ, ⌜Timeless G'⌝ -∗ (G' &&{↑NllftG}&&> @[κ]) -∗ G' -∗ ▷ P x wπ ={E}=∗
       G' ∗ ∃ t, gmb_b γ t ∗ (c s t ={E}=∗ ∃ wζ, ▷ Q y wζ ∗
         (∀ y' wζ', ▷ .PC[ζ] y' wζ' -∗ ▷ Q y' wζ' ={↑NllftUsr ∪ ↑NllftUsr2}=∗
            ∃ t', ▷ c s t' ∗ (gmb_b γ t' -∗ ▷ ∃ x', P x' (λ π, fπ (π ζ)))))) -∗
    G -∗ proph_loan ζ y -∗ proph_bor_tok ξ x idx -∗ proph_idx_bor_gen κ ξ idx P ={E}=∗
      ⟨π, π ξ = fπ (π ζ)⟩ ∗
      (∃ idx', proph_bor_tok ζ y idx' ∗ proph_idx_bor_gen κ ζ idx' Q) ∗ G.
  Proof using All.
    iIntros (HG Hmask) "#LFT #PROPH #UNIQ #GI #Ga Lc Pre #Gk Wand G Loan Tok IBor".
    iApply (proph_idx_bor_gen_map_special with "LFT PROPH UNIQ Gk [Wand Lc Pre] G Loan Tok IBor");
      [done..|].
    iIntros (G' wπ ?) "#G'k G' Sp P".
    iMod ("Wand" with "[//] G'k G' P") as "($ & %t & B & ToQ)".
    iMod (gmb_lend_start with "LFT GI Ga Lc Pre Sp B") as "[C Lent]"; [solve_ndisj|].
    iMod ("ToQ" with "C") as (wζ) "[Q Back]".
    iModIntro. iExists wζ. iFrame "Q".
    iIntros (y' wζ') "Pc Q".
    iMod ("Back" with "Pc Q") as (t') "[>C ToP]".
    iMod (gmb_lend_stop with "GI Lent C") as "[B $]".
    iModIntro. by iApply "ToP".
  Qed.
  (** Lazy (L3p): as [gmb_lend_proph_map], but the way back stores the final contents
      lazily ([gmb_lend_stop_lazy]): it gets a dead token for an outer lifetime of [κ]
      ([proph_idx_bor_gen_map_special_dead]) and splits the final new payload into a stored
      part [QS], with a settle law that forces the contents with the bytes mask of the
      instance, and a way to build the old payload from the lender's claim. The four
      credits are stored for the settlement. *)
  Lemma gmb_lend_proph_map_lazy E κ ξ x idx (P: pv_val ξ → pv_proph ξ → iProp Σ)
      ζ y (Q: pv_val ζ → pv_proph ζ → iProp Σ)
      (fπ: proj1_sig (pv_ty ζ) → proj1_sig (pv_ty ξ)) G γ s n :
    Timeless G → ↑Nllft ∪ ↑prophN ⊆ E →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ gmb_inv c γ -∗
    (@[κ] &&{↑NllftG; n}&&> gmb_a γ s) -∗ £ n -∗ £ (1 + n) -∗ £ 4 -∗
    (G &&{↑NllftG}&&> @[κ]) -∗
    (∀ G' wπ, ⌜Timeless G'⌝ -∗ (G' &&{↑NllftG}&&> @[κ]) -∗ G' -∗ ▷ P x wπ ={E}=∗
       G' ∗ ∃ t, gmb_b γ t ∗ (c s t ={E}=∗ ∃ wζ, ▷ Q y wζ ∗
         (∀ y' wζ', ▷ .PC[ζ] y' wζ' -∗ ▷ Q y' wζ' -∗ gmb_bdead κ ={↑NllftUsr ∪ ↑NllftUsr2}=∗
            ∃ (QS: iProp Σ) (R: T → iProp Σ), ▷ QS ∗
              (QS -∗ gmb_bdead κ ={gmb_bmask γ}=∗ ∃ t', c s t' ∗ R t') ∗
              (gmb_claim c γ R -∗ ▷ ∃ x', P x' (λ π, fπ (π ζ)))))) -∗
    G -∗ proph_loan ζ y -∗ proph_bor_tok ξ x idx -∗ proph_idx_bor_gen κ ξ idx P ={E}=∗
      ⟨π, π ξ = fπ (π ζ)⟩ ∗
      (∃ idx', proph_bor_tok ζ y idx' ∗ proph_idx_bor_gen κ ζ idx' Q) ∗ G.
  Proof using All.
    iIntros (HG Hmask) "#LFT #PROPH #UNIQ #GI #Ga Lc Pre £3 #Gk Wand G Loan Tok IBor".
    iApply (proph_idx_bor_gen_map_special_dead with "LFT PROPH UNIQ Gk [Wand Lc Pre £3] G Loan Tok IBor");
      [done..|].
    iIntros (G' wπ ?) "#G'k G' Sp P".
    iMod ("Wand" with "[//] G'k G' P") as "($ & %t & B & ToQ)".
    iMod (gmb_lend_start_lazy with "LFT GI Ga Lc Pre £3 Sp B") as "[C Lent]"; [solve_ndisj|].
    iMod ("ToQ" with "C") as (wζ) "[Q Back]".
    iModIntro. iExists wζ. iFrame "Q".
    iIntros (y' wζ') "Pc Q #Dead".
    iMod ("Back" with "Pc Q Dead") as (QS R) "(QS & Law & ToP)".
    iMod (gmb_lend_stop_lazy with "GI Lent QS Dead Law") as "[Cl $]".
    iModIntro. by iApply "ToP".
  Qed.
End GuardedBorProph.
