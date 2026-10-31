From iris.proofmode Require Import proofmode.
From iris.algebra Require Import gmap.
From lrust.typing Require Import lft_contexts.
From lrust.typing Require Export protocol ra_bytes.
From lrust.typing Require Import type programs ghost tracked product value_ctx own_bytes shr_bytes
  uniq_bytes uniq_bytes_util.
From lrust.typing Require uniq_util.
From guarding Require Import guard tactics guard_later_pers own_and.
From lrust.typing Require Import ra proph_protocol.
From lrust.lifetime Require Import lifetime_full.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

(** * Storage protocols on the byte layer

The typing rules of [typing/protocol.v], with the ghost values as MiniRust values ([◁ᵥ],
as in [typing/ra_bytes.v]) instead of boxes of size [0], shared references as [&shrb] and
unique borrows as [&uniqb]. The definitions ([storable_ty], [storage_resource_ty]) and the
lemmas of the storage protocol ([typing/proph_protocol.v]) are those of
[typing/protocol.v]. A ghost operation is [GhostOp] (it returns the empty tuple) or
[GhostRet [p]] (it returns the pointer [p], for a result that is a shared reference to a
ghost value: a zero-sized referent is at any location). The operations that return a pair
in [typing/protocol.v] (a box of a pair) here update their first argument and return the
second component. *)

Local Lemma proph_sub_diff' (γ : gname) :
  {[ γ ]} ⊆ (↑NllftG : coPset) → ↑prophN ⊆ (⊤ ∖ {[ γ ]} : coPset).
Proof. intros. assert (↑prophN ## (↑NllftG : coPset)) by solve_ndisj. set_solver. Qed.

Local Lemma proph_sub_diff_NllftG' : ↑prophN ⊆ (⊤ ∖ ↑NllftG : coPset).
Proof. solve_ndisj. Qed.

(** A ghost operation that returns a pair of ghost values. *)
Definition GhostOp2 : expr := (Skip ;; MkTuple [MkTuple []; MkTuple []])%E.

Section ghost_vals.
  Context `{!typeG Σ}.

  Lemma wp_ghost_op2 E Φ :
    ▷ ▷ Φ (MLitV (VTuple [VTuple []; VTuple []])) -∗ WP GhostOp2 @ E {{ Φ }}.
  Proof.
    iIntros "HΦ". rewrite /GhostOp2. wp_seq. wp_seq.
    wp_bind (MkTuple []).
    eapply (tac_wp_pure []); [apply (pure_mk_tuple [])|done|tc_solve|simpl; iApply wp_value].
    wp_bind (MkTuple []).
    eapply (tac_wp_pure []); [apply (pure_mk_tuple [])|done|tc_solve|simpl; iApply wp_value].
    eapply (tac_wp_pure []); [apply (pure_mk_tuple [VTuple []; VTuple []])|done|tc_solve|].
    simpl. iApply wp_value. done.
  Qed.

  (** A ghost value (whose MiniRust value is the empty tuple). *)
  Lemma ghost_val_intro {𝔄} tid (ty: type 𝔄) x d :
    ty.(ty_val) x = Some (VTuple []) →
    ⧖d -∗ ty.(ty_gho_own) x d d tid -∗ tctx_elt_interp tid (MLitV (VTuple []) ◁ᵥ ty) x.
  Proof. iIntros (?) "⧖ Gho". rewrite tctx_val_val. iExists d. by iFrame. Qed.

  (** A shared reference to a zero-sized value of a type with the default sharing
      predicate and a trivial persistent predicate, at any location. *)
  Lemma ghost_shr_intro {𝔄} tid κ (ty: type 𝔄) l x d :
    ty_bsize ty = 0 → is_Some (ty.(ty_val) x) → ty_shr_is_default ty →
    (∀ d g, ⊢ ty.(ty_gho_pers) x d g tid) →
    ⧖(S d) -∗ (@[κ] &&{↑NllftG; S d + 1}&&> ty.(ty_gho_own) x d (S d) tid) -∗
    tctx_elt_interp tid (MLitV (VPtr l.1) ◁ᵥ &shrb{κ} ty) (l, x).
  Proof.
    iIntros (Hz Hv Hdef Hpers) "⧖ #G". rewrite tctx_val_val. iExists (S d). iFrame "⧖".
    iSplit; [done|]. rewrite /= /by_succ. iSplit; [by iApply shr_bytes_own_zst|].
    iSplit; [by iApply (ty_shr_default_from_guard ty)|]. iNext. iApply Hpers.
  Qed.

  Lemma ghost_shr_elim {𝔄} tid κ (ty: type 𝔄) l x d :
    ty_shr_is_default ty →
    (&shrb{κ} ty).(ty_gho_own) (l, x) (S d) (S d) tid -∗
    (@[κ] &&{↑NllftG; S d + 1}&&> ty.(ty_gho_own) x d (S d) tid).
  Proof.
    iIntros (?) "(_ & #Shr & _)". by iApply (ty_shr_default_to_guard ty with "Shr").
  Qed.
End ghost_vals.

(** ** Storable values *)
Section storable_bytes.
  Context `{!typeG Σ}.

  (** Making a value storable ([storable_new] of [typing/protocol.v]). *)
  Lemma storable_new_bytes {𝔄} E L I p (ty : type 𝔄) :
    lctx_lft_alive E L (ty_lft ty) →
    typed_instr E L I +[p ◁ᵥ tracked_ty ty] GhostOp (λ v, +[v ◁ᵥ storable_ty ty])
      (λ post '-[x], λ mask π, ∀ n α, post -[(x, n, α)] mask π).
  Proof.
    iIntros (Alv tid post mask iκs [x1 []]) "#LFT #TIME _ _ #E L $ [p _] Obs".
    iDestruct "p" as (vp Hp w d [-> Hw]) "[#⧖ Gho]".
    iApply wp_fupd. rewrite /GhostOp.
    iApply (wp_cumulative_time_receipt2 with "TIME"); [solve_ndisj|]. iIntros "⧗".
    iDestruct (cumulative_time_receipt_sep 1 1 with "⧗") as "[⧗ _]".
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗ ⧖") as "[#⧖S £]";
      [solve_ndisj|].
    iDestruct (lc_weaken d with "£") as "£"; [unfold advance_credits; nia|].
    iDestruct (Alv with "L E") as "#Alv".
    iDestruct (ty_gho_pers_impl with "Gho") as "#Pers".
    iMod (llftl_begin' with "LFT") as (α) "[α %Hne]"; [solve_ndisj|].
    iMod (llftl_borrow (⊤ ∖ ↑advN) (α ⊓ ty_lft ty) (ty.(ty_gho_own) x1 d d tid)
      with "LFT [Gho]") as "[Bor Inh]"; [solve_ndisj|by iNext|].
    iAssert ((@[α] ∗ llctx_interp L) &&{↑NllftG}&&> @[α ⊓ ty_lft ty])%I as "#Gκ".
    { iApply guards_llft_glb; [iApply guards_weaken_sep_l|].
      iApply (guards_transitive with "[] Alv"). iApply guards_weaken_sep_r. }
    iMod (ty_share with "LFT [] Pers Gκ [$α $L] Bor") as "Upd"; [solve_ndisj| |].
    { iApply llftl_intersect_incl_r. }
    iMod (lc_step_fupdN_elim_later with "£ Upd") as ">[[α $] #Shr]".
    wp_seq. wp_seq.
    eapply (tac_wp_pure []); [apply (pure_mk_tuple [])|done|tc_solve|simpl; iApply wp_value].
    iModIntro. iExists -[(x1, (d, d), α)]. iSplitR "Obs".
    - iSplit; [|done]. iApply (ghost_val_intro _ (storable_ty ty) with "⧖S"); [done|]. simpl.
      iFrame "α Shr Pers". iSplit; [done|]. iSplitL "Inh".
      + iIntros "#Dead". iApply "Inh". rewrite llftl_end_inter. by iLeft.
      + iApply (persistent_time_receipt_mono with "⧖S"). lia.
    - iApply (proph_obs_impl with "Obs"). done.
  Qed.

  (** Getting the value back ([storable_into_inner]). *)
  Lemma storable_into_inner_bytes {𝔄} E L I p (ty : type 𝔄) :
    typed_instr E L I +[p ◁ᵥ storable_ty ty] GhostOp (λ v, +[v ◁ᵥ tracked_ty ty])
      (λ post '-[(x, n, α)], λ mask π, post -[x] mask π).
  Proof.
    iIntros (tid post mask iκs [[[x0 [d0 g0]] α] []]) "#LFT #TIME _ _ _ $ $ [p _] Obs".
    iDestruct "p" as (vp Hp w d [-> Hw]) "[_ Gho]".
    iDestruct "Gho" as (Hne) "(α & _ & Inh & #⧖2 & _)".
    iApply wp_fupd. rewrite /GhostOp.
    iApply (wp_cumulative_time_receipt2 with "TIME"); [solve_ndisj|]. iIntros "⧗".
    iDestruct (cumulative_time_receipt_sep 1 1 with "⧗") as "[⧗ _]".
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗ ⧖2") as "[#⧖S £]";
      [solve_ndisj|].
    iDestruct (lc_weaken (1 + 1) with "£") as "[£ £']"; [unfold advance_credits; nia|].
    iAssert (|={⊤ ∖ ↑advN}=> ▷ ty.(ty_gho_own) x0 d0 g0 tid)%I with "[α Inh £]" as ">Gho".
    { iMod (fupd_mask_subseteq (↑Nllft)) as "Close"; [solve_ndisj|].
      iMod (llftl_end' with "LFT α") as "End"; [done|].
      iMod (lc_fupd_elim_later with "£ End") as "End".
      iMod "End" as "#Dead".
      iMod ("Inh" with "Dead") as "Gho".
      by iMod "Close" as "_". }
    iMod (lc_fupd_elim_later with "£' Gho") as "Gho".
    wp_seq. wp_seq.
    eapply (tac_wp_pure []); [apply (pure_mk_tuple [])|done|tc_solve|simpl; iApply wp_value].
    iModIntro. iExists -[x0]. iSplitR "Obs".
    - iSplit; [|done]. rewrite tctx_val_val. iExists (S d0 `max` g0 + 1). iSplit; [done|].
      iFrame "⧖S". iDestruct (ty_gho_own_depth_mono with "Gho") as "[$ _]"; lia.
    - iApply (proph_obs_impl with "Obs"). done.
  Qed.
End storable_bytes.
