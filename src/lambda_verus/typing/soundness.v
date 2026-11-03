From iris.algebra Require Import frac dfrac_agree.
From iris.base_logic.lib Require Import ghost_var.
From lrust.util Require Import cancellable_na_invariants.
From iris.proofmode Require Import proofmode.
From lrust.lang Require Import races adequacy proofmode notation.
From lrust.lifetime Require Import lifetime_full.
From guarding.lib Require Import fractional cancellable.
From guarding Require Import guard.
From lrust.typing Require Import type product programs value_ctx function.
Set Default Proof Using "Type".

Class typePreG Σ := PreTypeG {
  #[global] type_preG_lrustGS :: lrustGpreS Σ;
  #[global] type_preG_prophG :: prophPreG Σ;
  #[global] type_preG_uniqG :: uniqPreG Σ;
  #[global] type_preG_lftGS :: llft_logicGpreS Σ;
  #[global] type_preG_frac_logicG :: frac_logicG Σ;
  #[global] type_preG_ecInv_logicΣ :: ecInv_logicG Σ;
  #[global] type_preG_agree_pairΣ :: inG Σ (dfrac_agreeR (leibnizO nat));
  #[global] type_preG_lstate_ghost_varG :: ghost_varG Σ ltype_state;
  #[global] type_preG_gcellsGpreS :: gcellsGpreS Σ
}.

Definition typeΣ : gFunctors :=
  #[lrustΣ; llft_logicΣ; cancellable_na_invariants.na_invΣ;
    GFunctor (constRF fracR); uniqΣ; prophΣ; frac_logicΣ; ecInv_logicΣ;
    GFunctor ((dfrac_agreeR (leibnizO (nat)))); ghost_varΣ ltype_state; gcellsΣ].
Global Instance subG_typePreG {Σ} : subG typeΣ Σ → typePreG Σ.
Proof. solve_inG. Qed.

(** * Type soundness

A [main] function typed with the function type [fn] ([typing/function.v]), whose
result is a MiniRust value of the unit type, runs without data races and does not get
stuck. *)

Section type_soundness.
  Definition exit_cont : val := λ: [<>], #☠.

  (* function type with trivial precondition and postcondition *)
  Definition main_type `{!typeG Σ} :=
    (fn(∅) → unit_ty)%T (λ (_: ~~()), (λ post '-[], λ mask π, ∀ x, post x mask π)).

  Theorem type_soundness `{!typePreG Σ} (main : val) σ t c :
    (∀ `{!typeG Σ}, typed_val main main_type c) →
    rtc erased_step ([main [exit_cont]%E], (∅, false)) (t, σ) →
    nonracing_threadpool t σ ∧
    (∀ e, e ∈ t → is_Some (to_val e) ∨ reducible e σ).
  Proof.
    intros Hmain Hrtc.
    cut (adequate NotStuck (main [exit_cont]%E) (∅, false) (λ _ _, True)).
    { split. by eapply adequate_nonracing.
      intros. by eapply (adequate_not_stuck _ (main [exit_cont]%E)). }
    apply: lrust_adequacy=>?. iIntros "£ #TIME".
    iMod (llft_alloc with "£") as (?) "#LFT".
    iMod proph_init as (?) "#PROPH"; first done.
    iMod uniq_init as (?) "#UNIQ"; first done.
    iMod (gcells_ctx_alloc ⊤) as (?) "#GC".
    set (Htype := TypeG Σ _ _ _ _ _ _ _ _ _).
    iMod (invctx_alloc ⊤ with "GC") as (tid) "Hinvctx".
    wp_bind (of_val main). iApply (wp_wand with "[Hinvctx]").
    iApply (Hmain Htype [] [] (InvCtx [] static AtomicClosed)
        tid (λ xl mask π, True) ⊤ [] -[]
      with "LFT TIME PROPH UNIQ [] [] [Hinvctx] [$]").
    { by rewrite /elctx_interp. }
    { by rewrite /llctx_interp big_sepL_nil. }
    { iFrame "Hinvctx". }
    { by iApply proph_obs_true. }
    clear Hrtc Hmain main. iIntros (main) "Hmain".
    iDestruct "Hmain" as ([[fxval fx] []]) "/= (Htl & Invctx & [Hmain _] & #Obs)".
    iDestruct "Hmain" as (?) "(EQ & %d & %Hv & ? & Hmain)". rewrite eval_path_of_val.
    iDestruct "EQ" as %[= <-]. simpl in Hv. subst fxval.
    iDestruct "Hmain" as (f k j e ?) "(EQ & Hmain)". iDestruct "EQ" as %[= ->].
    wp_rec.
    iMod (llftl_begin' with "LFT") as (ϝ) "Hϝ"; first done.
    iDestruct (function.invctx_interp_call [] static AtomicClosed tid ⊤ ϝ [] with "[] [] [Invctx]")
        as (iκs') "[Invctx InvctxBack]".
      { iApply lft_incl_static. }
      { simpl. iApply lft_incl_static. }
      { iFrame "Invctx". }
    iDestruct ("Hmain" $! () ϝ exit_cont -[] tid -[] ⊤ (λ _ _ _, True) iκs') as "X".
    iDestruct("X" with "LFT TIME PROPH UNIQ [] [Hϝ] [Invctx] [] [] []") as "X".
    { by rewrite /elctx_interp /=. }
    { rewrite /llctx_interp /=. iSplit; last done. iExists ϝ. iFrame. by rewrite /= left_id. }
    { iApply "Invctx". }
    { rewrite cctx_interp_singleton. simpl. iIntros (args [? []] mask) "_ _".
      inv_vec args. iIntros (x) "_ /= ?". by wp_lam. }
    { simpl. done. }
    { iApply (proph_obs_impl with "Obs"). done. }
    iApply "X".
  Qed.
End type_soundness.

Theorem type_soundness_closed (main : val) σ t c :
  (∀ `{!typeG typeΣ}, typed_val main main_type c) →
  rtc erased_step ([main [exit_cont]%E], (∅, false)) (t, σ) →
  nonracing_threadpool t σ ∧
  (∀ e, e ∈ t → is_Some (to_val e) ∨ reducible e σ).
Proof.
  intros. eapply @type_soundness; try done. apply _.
Qed.

