From iris.algebra Require Import numbers list dfrac_agree.
From iris.base_logic.lib Require Export ghost_var.
From lrust.util Require Export basic vector update fancy_lists cancellable cancellable_na_invariants.
From lrust.prophecy Require Export prophecy.
From lrust.lang Require Export proofmode notation heap.
From lrust.typing Require Export base uniq_cmra lstate.
From lrust.typing Require Export lft_contexts.
From lrust.typing Require Export lifetime.
From lrust.lifetime Require Import lifetime_full.
From guarding.lib Require Import fractional cancellable.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type (𝔄 𝔅 ℭ: syn_type) (𝔄l 𝔅l: syn_typel).

Class typeG Σ := TypeG {
  #[global] type_lrustGS :: lrustGS Σ;
  #[global] type_prophG :: prophG Σ;
  #[global] type_uniqG :: uniqG Σ;
  #[global] type_lftGS :: llft_logicGS Σ;
  #[global] type_frac_logicG :: frac_logicG Σ;
  #[global] type_ecInv_logicΣ :: ecInv_logicG Σ;
  #[global] type_agree_pairΣ :: inG Σ (dfrac_agreeR (leibnizO nat));
  (** The states of the pinned bodies of unique borrows (see [uniq_util.v]). *)
  #[global] type_lstate_ghost_varG :: ghost_varG Σ ltype_state
}.

Definition lrustN := nroot .@ "lrust".
Definition shrN := lrustN .@ "shr".

Definition thread_id := na_inv_pool_name.

(** * Sharing *)

(** About steps in the sharing law [ty_share]. As in RustBelt, the sharing law ends in a
    step-update [|={E}▷=>^d |={E}=> …] whose number of steps is the depth [d] of the
    ownership predicate. A structural type uses the steps to look under the laters in
    front of its contents: [own_ptr] takes one step to turn the borrow of the
    [▷ gho_own] of its contents into a borrow of [gho_own], and [&uniq] takes one step
    to strip the later in front of the lazy contents of its borrow (whose ownership
    predicate also gives the persistent predicate that the recursive call needs). Both decrease the depth by one, so [d] steps suffice. A
    product shares its components in parallel (splitting the guard [G] in halves), so
    the number of steps does not grow with the width of the type.

    The sharing law is also given the persistent predicate [ty_gho_pers]. This is what
    lets [&uniq] unnest the borrow of its contents right away: the persistent part of
    the inner borrow is in the persistent predicate of [&uniq], not under a later. The
    payload of [&uniq] is lazy (see [uniq_payload]): [&uniq] opens the borrow of its
    contents before its step and runs the lazy update after the step, so the step count
    stays [d].

    An earlier version took no steps and instead kept laters ([▷^k]) in front of both
    the borrowed ownership predicate and the resulting sharing predicate. That does not
    work for [&uniq] below [own_ptr], which needs non-timeless information from under
    those laters right away.

    Callers pay for the steps with later credits (e.g. obtained from time receipts, as in
    [resolve_uniq_body]) or with program steps. *)

Section guards_sep.
  Context `{!typeG Σ}.

  (** A guard of a persistent proposition and a guard of another proposition by the
      same left-hand side can be combined. *)
  Lemma guards_sep_pers (P Q1 Q2 : iProp Σ) F n :
    Persistent Q1 →
    (P &&{F; n}&&> Q1) -∗ (P &&{F; n}&&> Q2) -∗ (P &&{F; n}&&> Q1 ∗ Q2).
  Proof.
    iIntros (?) "#G1 #G2".
    iAssert (P &&{F; n}&&> ∃ _: unit, Q2)%I as "#G2'".
    { iApply (guards_transitive_left with "G2"). iApply guards_weaken.
      iIntros "!> Q2". iSplitL; [by iExists ()|]. by iIntros "[% $]". }
    iDestruct (guards_strengthen_exists unit P Q1 (λ _, Q1) (λ _, Q2) F n
      (λ _, bi.and_elim_l _ _) _ with "G1 G2'") as "G".
    iApply (guards_transitive_left with "G"). iApply guards_weaken.
    iIntros "!> [%u [Q2 #Q1]]". iFrame "Q1 Q2". iIntros "[_ Q2]". iExists u. by iFrame.
  Qed.
End guards_sep.

Section share_util.
  Context `{!typeG Σ}.

  (** A guard of the tokens of two lifetimes is a guard of the token of their
      intersection. *)
  Lemma guards_llft_glb (W: iProp Σ) κ κ' F n :
    (W &&{F; n}&&> @[κ]) -∗ (W &&{F; n}&&> @[κ']) -∗ (W &&{F; n}&&> @[κ ⊓ κ']).
  Proof.
    iIntros "A B". iApply (guards_and_point with "A B"); [exact: point_prop_llft_alive|].
    by rewrite llftl_tok_inter_and.
  Qed.

  (** Taking a step to remove the later in front of the contents of a borrow. *)
  Lemma llftl_bor_later_step E κ G P :
    Timeless G → ↑Nllft ⊆ E →
    llft_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗ G -∗ &{κ} (▷ P) ={E}=∗ ▷ |={E}=> G ∗ &{κ} P.
  Proof.
    iIntros (??) "#LFT #Gκ G Bor".
    iMod (llftl_bor_acc_guarded with "LFT Bor Gκ G") as "[P Back]"; [done|].
    iModIntro. iNext. iMod (fupd_mask_subseteq (↑Nllft)) as "Upd"; [done|].
    iMod ("Back" $! P with "[P]") as "[$ $]"; [|done].
    iSplitR "P"; [|done]. iIntros "!> P". iModIntro. by iNext.
  Qed.

  (** Reading a persistent consequence of the contents of a borrow, given a guard for
      [κ]. The borrow is kept. *)
  Lemma llftl_bor_guarded_extract E κ G P Q :
    Timeless G → Persistent Q → ↑Nllft ⊆ E →
    llft_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗ G -∗ &{κ} P -∗ □ (P -∗ Q) ={E}=∗
      G ∗ &{κ} P ∗ ▷ Q.
  Proof.
    iIntros (???) "#LFT #Gκ G Bor #PQ".
    iMod (llftl_bor_acc_guarded with "LFT Bor Gκ G") as "[P Back]"; [done|].
    iAssert (▷ Q)%I as "#Q". { iNext. by iApply "PQ". }
    iMod (fupd_mask_subseteq (↑Nllft)) as "Upd"; [done|].
    iMod ("Back" $! P with "[P]") as "[$ $]".
    { iSplitR "P"; [|done]. iIntros "!> P". by iModIntro. }
    iMod "Upd" as "_". by iModIntro.
  Qed.

  (** Running two sharing-like step-updates in parallel, each with half of a guard for
      [κ]. This is how a product shares its components without adding up the steps. *)
  Lemma share_par E κ G n (S1 S2: iProp Σ) :
    Timeless G → ↑NllftG ⊆ E →
    (G &&{↑NllftG}&&> @[κ]) -∗ G -∗
    (∀ H, ⌜Timeless H⌝ -∗ (H &&{↑NllftG}&&> @[κ]) -∗ H ={E}=∗ |={E}▷=>^n |={E}=> H ∗ S1) -∗
    (∀ H, ⌜Timeless H⌝ -∗ (H &&{↑NllftG}&&> @[κ]) -∗ H ={E}=∗ |={E}▷=>^n |={E}=> H ∗ S2) ={E}=∗
      |={E}▷=>^n |={E}=> G ∗ S1 ∗ S2.
  Proof.
    iIntros (??) "#Gκ G Sh1 Sh2".
    iMod (fractional.frac_split_guard_in_half with "G Gκ") as (γ) "[H1 [H2 [#Gh #Back]]]";
      [done|].
    iMod ("Sh1" with "[%] Gh H1") as "Sh1"; [apply _|].
    iMod ("Sh2" with "[%] Gh H2") as "Sh2"; [apply _|].
    iCombine "Sh1 Sh2" as "Sh". iModIntro. iApply (step_fupdN_wand with "Sh").
    iIntros "[>[H1 $] >[H2 $]]". iApply (fupd_mask_mono with "[H1 H2]"); [done|].
    iApply ("Back" with "H1 H2").
  Qed.

  (** Reading a persistent proposition out of a borrow, given a guard for [κ]. *)
  Lemma llftl_bor_guarded_pers E κ G P :
    Timeless G → Persistent P → ↑Nllft ⊆ E →
    llft_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗ G -∗ &{κ} P ={E}=∗ G ∗ ▷ P.
  Proof.
    iIntros (???) "#LFT #Gκ G Bor".
    iMod (llftl_bor_acc_guarded with "LFT Bor Gκ G") as "[#P Back]"; [done..|].
    iDestruct ("Back" $! P with "[]") as "Close". { iFrame "P". iIntros "!> H". by iModIntro. }
    iMod (fupd_mask_mono with "Close") as "[_ $]"; [done|]. by iModIntro.
  Qed.
End share_util.

(** * Guarded updates

    [guarded_upd E P Q] is a fancy update (with mask [E]) to [Q] that can only be run
    given a guard for [P]: whoever runs it lends it a timeless proposition [G] that
    guards [P], and gets [G] back. This is how lazy contents can depend on a lifetime
    being alive. The payload of [&uniq] ([uniq_payload]) is a guarded update for the
    lifetime of the referent type, so that running it can open borrows at that lifetime
    (e.g. the restored inner borrow of an unnested [&uniq &uniq], see
    [type_deref_uniq_uniq_instr]); the old contents handed out by [typed_write] are a
    guarded update for the lifetime context. *)
Section guarded_upd.
  Context `{!typeG Σ}.

  Definition guarded_upd (E: coPset) (P Q: iProp Σ) : iProp Σ :=
    ∀ G, ⌜Timeless G⌝ -∗ (G &&{↑NllftG}&&> P) -∗ G ={E}=∗ G ∗ Q.

  Global Instance guarded_upd_ne E P : NonExpansive (guarded_upd E P).
  Proof. solve_proper. Qed.
  Global Instance guarded_upd_proper E P : Proper ((≡) ==> (≡)) (guarded_upd E P).
  Proof. solve_proper. Qed.

  Lemma guarded_upd_intro E P Q : (|={E}=> Q) -∗ guarded_upd E P Q.
  Proof. iIntros "Q" (G ?) "_ G". iMod "Q". by iFrame. Qed.

  Lemma guarded_upd_run E E' P Q G :
    Timeless G → E ⊆ E' →
    (G &&{↑NllftG}&&> P) -∗ G -∗ guarded_upd E P Q ={E'}=∗ G ∗ Q.
  Proof. iIntros (??) "Gk G Upd". iApply (fupd_mask_mono with "(Upd [%] Gk G)"); done. Qed.

  (** Mapping, where the map may use the guard. *)
  Lemma guarded_upd_wand E P Q Q' :
    (∀ G, ⌜Timeless G⌝ -∗ (G &&{↑NllftG}&&> P) -∗ G -∗ Q ={E}=∗ G ∗ Q') -∗
    guarded_upd E P Q -∗ guarded_upd E P Q'.
  Proof.
    iIntros "W Upd" (G ?) "#Gk G". iMod ("Upd" with "[//] Gk G") as "[G Q]".
    iApply ("W" with "[//] Gk G Q").
  Qed.

  Lemma guarded_upd_mono E P Q Q' :
    (Q ={E}=∗ Q') -∗ guarded_upd E P Q -∗ guarded_upd E P Q'.
  Proof.
    iIntros "W". iApply guarded_upd_wand. iIntros (G ?) "_ $ Q". by iApply "W".
  Qed.

  Lemma guarded_upd_weaken E P P' Q :
    (P' &&{↑NllftG}&&> P) -∗ guarded_upd E P Q -∗ guarded_upd E P' Q.
  Proof.
    iIntros "#P'P Upd" (G ?) "#Gk G". iApply ("Upd" with "[//] [] G").
    iApply (guards_transitive with "Gk P'P").
  Qed.

  Lemma guarded_upd_mask_mono E E' P Q :
    E ⊆ E' → guarded_upd E P Q -∗ guarded_upd E' P Q.
  Proof.
    iIntros (HE) "Upd". iIntros (G ?) "Gk G".
    iApply (fupd_mask_mono with "(Upd [%] Gk G)"); done.
  Qed.

  Lemma guarded_upd_sep E P Q1 Q2 :
    guarded_upd E P Q1 -∗ guarded_upd E P Q2 -∗ guarded_upd E P (Q1 ∗ Q2).
  Proof.
    iIntros "U1 U2" (G ?) "#Gk G". iMod ("U1" with "[//] Gk G") as "[G $]".
    iApply ("U2" with "[//] Gk G").
  Qed.

  (** Guarded updates for equivalent lifetimes are equivalent. *)
  Lemma guarded_upd_lft_equiv E κ κ' Q :
    (⊢ κ ≡ₗ κ') → guarded_upd E @[κ] Q ⊣⊢ guarded_upd E @[κ'] Q.
  Proof.
    intros Hκ. iDestruct Hκ as "#[A B]".
    iSplit; iApply guarded_upd_weaken; done.
  Qed.

  (** Running a guarded update inside a full borrow at [κ], given a guard for [κ] (half
      of which keeps the borrow open, the other half runs the update) and a later credit
      for the later in front of the borrowed contents. *)
  Lemma llftl_bor_guarded_upd E M κ P Q G :
    Timeless G → ↑Nllft ⊆ E → M ⊆ E →
    llft_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗ (@[κ] &&{↑NllftG}&&> P) -∗ G -∗ £1 -∗
    &{κ} (guarded_upd M P Q) ={E}=∗ &{κ} Q ∗ G.
  Proof.
    iIntros (???) "#LFT #Gk #κP G £ Bor".
    iMod (fractional.frac_split_guard_in_half with "G Gk") as (γ) "[H1 [H2 [#Gh #Back]]]";
      [solve_ndisj|].
    iMod (llftl_bor_acc_guarded with "LFT Bor Gh H1") as "[Upd Close]"; [done|].
    iMod (lc_fupd_elim_later with "£ Upd") as "Upd".
    iMod (guarded_upd_run M E P Q with "[] H2 Upd") as "[H2 Q]"; [done| |].
    { iApply (guards_transitive with "Gh κP"). }
    iDestruct ("Close" $! Q with "[Q]") as "Close".
    { iSplitR; [|by iNext]. iIntros "!> Q !> !>". iApply guarded_upd_intro. by iModIntro. }
    iMod (fupd_mask_mono with "Close") as "[$ H1]"; [done|].
    iApply (fupd_mask_mono with "(Back H1 H2)"). solve_ndisj.
  Qed.
End guarded_upd.

(** The default sharing predicate: a guard of the ownership predicate by [@[κ]] (with
    [g+1] laters), at some depth no larger than the given one. Closing it downwards in
    the depth makes depth monotonicity hold for any ownership predicate; for a type whose
    ownership predicate is depth monotone, see [default_shr_guard]. *)
Definition default_shr `{!typeG Σ} {𝔄} (gho: ~~𝔄 → nat → nat → thread_id → iProp Σ)
    (κ: lft) (x: ~~𝔄) (d g: nat) (tid: thread_id) : iProp Σ :=
  ∃ d0 g0, ⌜(d0 ≤ d)%nat ∧ (g0 ≤ g)%nat⌝ ∗ (@[κ] &&{↑NllftG; g+1}&&> gho x d0 g0 tid).
Global Instance: Params (@default_shr) 3 := {}.
Global Arguments default_shr : simpl never.

(** Depth monotonicity of an ownership predicate, and the guarding of the prophecy
    tokens by a guard of the ownership predicate. A type with the default sharing
    predicate proves [ty_shr_guard_proph] from these two (see
    [default_shr_guard_proph]). *)
Definition gho_own_depth_mono_stmt `{!typeG Σ} {𝔄}
    (gho: ~~𝔄 → nat → nat → thread_id → iProp Σ) : Prop :=
  ∀ d g d' g' x tid, (d ≤ d')%nat → (g ≤ g')%nat → gho x d g tid -∗
    gho x d' g' tid ∗ (gho x d' g' tid -∗ gho x d g tid).

Definition guard_proph_stmt `{!typeG Σ} {𝔄} (lfts: list lft)
    (gho pers: ~~𝔄 → nat → nat → thread_id → iProp Σ) : Prop :=
  ∀ κ x n d g tid ξ R, ξ ∈ ξl x →
    llft_ctx -∗ κ ⊑ lft_intersect_list lfts -∗ pers x d g tid -∗
    ▷^(d*(g+2)) (
        (R &&{↑NllftG; n}&&> @[κ]) -∗
        (R &&{↑NllftG; n}&&> gho x d g tid) -∗
        (R &&{↑NllftG; n + d*(g+1)}&&> 1:[ξ])).

Section default_shr.
  Context `{!typeG Σ} {𝔄} (gho: ~~𝔄 → nat → nat → thread_id → iProp Σ).

  Global Instance default_shr_persistent κ x d g tid :
    Persistent (default_shr gho κ x d g tid).
  Proof. rewrite /default_shr. apply _. Qed.

  Lemma default_shr_lft_mono κ κ' x n d g tid :
    (@[κ'] &&{↑NllftG; n}&&> @[κ]) -∗ default_shr gho κ x d g tid -∗
    default_shr gho κ' x d (g+n) tid.
  Proof.
    iIntros "#Incl Shr". iDestruct "Shr" as (d0 g0) "[%Le #Guard]". iExists d0, g0.
    iSplit. { iPureIntro. lia. } replace (g + n + 1) with (n + (g + 1)) by lia.
    iApply (guards_transitive_additive with "Incl Guard").
  Qed.

  Lemma default_shr_depth_mono κ d g d' g' x tid :
    (d ≤ d')%nat → (g ≤ g')%nat →
    default_shr gho κ x d g tid -∗ default_shr gho κ x d' g' tid.
  Proof.
    iIntros (??) "Shr". iDestruct "Shr" as (d0 g0) "[%Le #Guard]". iExists d0, g0.
    iSplit. { iPureIntro. lia. } leaf_goal laters to (g+1). { lia. } iFrame "Guard".
  Qed.

  (** The sharing law for the default sharing predicate. It takes no steps. *)
  Lemma default_shr_share E κ x d g tid (G: iProp Σ) :
    ↑Nllft ⊆ E →
    llft_ctx -∗ G -∗ &{κ} (gho x d g tid) ={E}=∗
      |={E}▷=>^d |={E}=> G ∗ default_shr gho κ x d g tid.
  Proof.
    iIntros (?) "#LFT G Bor".
    iMod (llftl_bor_guard with "LFT Bor") as "#Guard"; [done|].
    iModIntro. iApply step_fupdN_intro; [done|]. iApply bi.laterN_intro. iModIntro.
    iFrame "G". iExists d, g. iSplit; [done|]. leaf_goal laters to 1. { lia. }
    iFrame "Guard".
  Qed.

  Lemma default_shr_from_guard κ x d g tid :
    (@[κ] &&{↑NllftG; g+1}&&> gho x d g tid) -∗ default_shr gho κ x d g tid.
  Proof. iIntros "#Guard". iExists d, g. by iFrame "Guard". Qed.

  Lemma default_shr_guard κ x d g tid :
    gho_own_depth_mono_stmt gho →
    default_shr gho κ x d g tid ⊣⊢ (@[κ] &&{↑NllftG; g+1}&&> gho x d g tid).
  Proof.
    move=> Mono. iSplit.
    - iIntros "Shr". iDestruct "Shr" as (d0 g0) "[[%Le %Le'] #Guard]".
      iApply (guards_transitive_left with "Guard"). leaf_by_sep. by iApply Mono.
    - iApply default_shr_from_guard.
  Qed.

  Lemma default_shr_guard_proph lfts pers κ x n d g tid ξ R :
    gho_own_depth_mono_stmt gho → guard_proph_stmt lfts gho pers → ξ ∈ ξl x →
    llft_ctx -∗ κ ⊑ lft_intersect_list lfts -∗ pers x d g tid -∗
    default_shr gho κ x d g tid -∗
    ▷^(d*(g+2)) (
        (R &&{↑NllftG; n}&&> @[κ]) -∗
        (R &&{↑NllftG; n + (d+1)*(g+1)}&&> 1:[ξ])).
  Proof.
    iIntros (Mono GP Hin) "#LFT #Incl Pers #Shr".
    iDestruct (GP κ x (n + (g+1)) d g tid ξ R Hin with "LFT Incl Pers") as "GP".
    iNext. iIntros "#Rκ".
    iDestruct (default_shr_guard with "Shr") as "#Guard"; [done|].
    replace (n + (d+1)*(g+1)) with (n + (g+1) + d*(g+1)) by lia.
    iApply "GP".
    - leaf_goal laters to n. { lia. } iFrame "Rκ".
    - iApply (guards_transitive_additive with "Rκ Guard").
  Qed.

  Lemma default_shr_change_tid κ x d g tid tid' :
    (∀ d g, gho x d g tid ⊣⊢ gho x d g tid') →
    default_shr gho κ x d g tid ⊣⊢ default_shr gho κ x d g tid'.
  Proof. move=> Eq. rewrite /default_shr. by setoid_rewrite Eq. Qed.

  Lemma default_shr_ne n gho' κ x d g tid :
    (∀ x d g tid, gho x d g tid ≡{n}≡ gho' x d g tid) →
    default_shr gho κ x d g tid ≡{n}≡ default_shr gho' κ x d g tid.
  Proof. move=> Eq. rewrite /default_shr. do 6 f_equiv. apply Eq. Qed.

  Lemma default_shr_proper gho' κ x d g tid :
    (∀ x d g tid, gho x d g tid ≡ gho' x d g tid) →
    default_shr gho κ x d g tid ≡ default_shr gho' κ x d g tid.
  Proof. move=> Eq. rewrite /default_shr. do 6 f_equiv. apply Eq. Qed.

  Lemma default_shr_contractive n gho' κ x d g tid :
    (∀ x d g tid, dist_later n (gho x d g tid) (gho' x d g tid)) →
    default_shr gho κ x d g tid ≡{n}≡ default_shr gho' κ x d g tid.
  Proof.
    move=> Eq. rewrite /default_shr. do 5 f_equiv.
    apply guards_contractive_right_if_n_ge_1; [lia|]. apply Eq.
  Qed.

  Lemma default_shr_incl {𝔅} (gho': ~~𝔅 → nat → nat → thread_id → iProp Σ) (h: ~~𝔄 → ~~𝔅) :
    □ (∀ x d g tid, gho x d g tid -∗ gho' (h x) d g tid ∗ (gho' (h x) d g tid -∗ gho x d g tid)) -∗
    □ (∀ κ x d g tid, default_shr gho κ x d g tid -∗ default_shr gho' κ (h x) d g tid).
  Proof.
    iIntros "#In !>" (κ x d g tid) "Shr". iDestruct "Shr" as (d0 g0) "[%Le #Guard]".
    iExists d0, g0. iSplit; [done|]. iApply (guards_transitive_left with "Guard").
    leaf_by_sep. iApply "In".
  Qed.
End default_shr.

Lemma default_shr_True `{!typeG Σ} {𝔄} κ (x: ~~𝔄) d g tid :
  ⊢ default_shr (λ _ _ _ _, True%I) κ x d g tid.
Proof. iExists d, g. iSplit; [done|]. iApply guards_true. Qed.

(** Discharges the obligations about [ty_shr] of a type defined with [default_shr]. *)
Ltac solve_default_shr :=
  intros; first
    [ apply _
    | apply default_shr_lft_mono
    | apply default_shr_depth_mono; assumption
    | iIntros "#LFT _ _ _ G Bor";
      iApply (default_shr_share with "LFT G [Bor]"); first [solve_ndisj | iExact "Bor"]
      (* [ty_shr_guard_proph] for a type without prophecy variables *)
    | lazymatch goal with H : _ ∈ ξl _ |- _ => exfalso; simpl in H; set_solver end ].

(** * Type *)

Record type `{!typeG Σ} 𝔄 := {
  ty_size: nat;
  ty_lfts: list lft;
  ty_E: elctx;
  
  ty_gho_pers: ~~𝔄 → nat → nat → thread_id → iProp Σ;
  ty_gho_own: ~~𝔄 → nat → nat → thread_id → iProp Σ;
  (* The resolved ownership: what remains of the ownership of a value once it has been
     resolved ([resolve_keep]), and can still be read (see the place type [OfRes] of
     [typing/ltype.v]). For [&uniq{κ} ty] it is the shared view of the referent at κ
     (as produced by [resolve_uniq_body]); it is structural for [own_ptr], products,
     sums, [mod_ty] and [tracked]; for the other types it is [ty_gho_own]. There is no
     law about it in the record: its relation to [ty_gho_own] is given by [resolve_keep]
     (per type) and by [ResOwn] (types where it is [ty_gho_own]); it is not part of
     the OFE structure of types (it is not used for fixpoints: [fix_ty] takes its
     [ty_gho_own]). *)
  ty_gho_res: ~~𝔄 → nat → nat → thread_id → iProp Σ;
  (* TODO: no type has actually phys depending on tid, we should remove it *)
  ty_phys: ~~𝔄 → thread_id → list fancy_val;
  
  ty_size_eq x tid : length (ty_phys x tid) = ty_size;
  ty_size_eq2 : size_of 𝔄 = ty_size;
  ty_phys_eq2 x tid : syn_phys x = ty_phys x tid;
  
  ty_gho_own_depth_mono d g d' g' x tid :
    (d ≤ d')%nat → (g ≤ g')%nat → ty_gho_own x d g tid -∗
        ty_gho_own x d' g' tid ∗ (ty_gho_own x d' g' tid -∗ ty_gho_own x d g tid) ;
        
  ty_gho_pers_depth_mono d g d' g' x tid :
    (d ≤ d')%nat → (g ≤ g')%nat → ty_gho_pers x d g tid -∗ ty_gho_pers x d' g' tid;
  
  ty_gho_pers_pers x d g tid :
      Persistent (ty_gho_pers x d g tid) ;
  ty_gho_pers_impl x d g tid :
      ty_gho_own x d g tid -∗ ty_gho_pers x d g tid ;

  (* The sharing predicate, for sharing at the lifetime κ. *)
  ty_shr: lft → ~~𝔄 → nat → nat → thread_id → iProp Σ;
  ty_shr_persistent κ x d g tid : Persistent (ty_shr κ x d g tid);
  (* Lifetime monotonicity, for an inclusion with laters: the laters of the inclusion
     are absorbed into the depth [g]. *)
  ty_shr_lft_mono κ κ' x n d g tid :
      (@[κ'] &&{↑NllftG; n}&&> @[κ]) -∗ ty_shr κ x d g tid -∗ ty_shr κ' x d (g+n) tid;
  ty_shr_depth_mono κ d g d' g' x tid :
      (d ≤ d')%nat → (g ≤ g')%nat → ty_shr κ x d g tid -∗ ty_shr κ x d' g' tid;
  (* The sharing law: a full borrow of the ownership predicate at κ can be turned into
     the sharing predicate at κ, given the persistent predicate and a guard G for κ.
     The guard (rather than a token) lets the borrow be opened non-atomically, so that
     fancy updates (e.g. a lazy payload) can be run inside. The law ends in [d] steps;
     see the comment at the top of the file. *)
  ty_share E κ x d g tid G :
      ↑Nllft ∪ ↑prophN ∪ ↑uniqN ⊆ E → Timeless G →
      llft_ctx -∗ κ ⊑ lft_intersect_list ty_lfts -∗ ty_gho_pers x d g tid -∗
      (G &&{↑NllftG}&&> @[κ]) -∗ G -∗
      &{κ} (ty_gho_own x d g tid) ={E}=∗ |={E}▷=>^d |={E}=> G ∗ ty_shr κ x d g tid;
  (* The prophecy tokens of the value are guarded by anything that guards [@[κ]], given
     the sharing predicate at κ. The sharing predicate is taken before the laters,
     since a structural sharing predicate has the sharing predicates of its contents
     under a later. The budget of laters is [g+2] per level of depth (rather than the
     [g+1] laters of the resulting guard): [&uniq] gets the persistent predicate of its
     contents from its sharing predicate, where it is under two laters (see
     [uniq_bor]), and needs one more later than the [g+1] of a level of depth when
     [g = 0]. *)
  ty_shr_guard_proph κ x n d g tid ξ R :
      ξ ∈ ξl x →
      llft_ctx -∗
      κ ⊑ lft_intersect_list ty_lfts -∗
      ty_gho_pers x d g tid -∗
      ty_shr κ x d g tid -∗
      ▷^(d*(g+2)) (
          (R &&{↑NllftG; n}&&> @[κ]) -∗
          (R &&{↑NllftG; n + (d+1)*(g+1)}&&> 1:[ξ])
      );
  
 (* ty_gho_own_depth_mono d g d' g' vπ tid :
    (d ≤ d')%nat → (g ≤ g')%nat → ty_gho_own vπ d g tid -∗ ty_gho_own vπ d' g' tid;
  ty_gho_own_depth_mono_guard d g d' g' vπ tid :
    (d ≤ d')%nat → (g ≤ g')%nat → ⊢ ty_gho_own vπ d g tid &&{↑NllftG}&&> ty_gho_own vπ d' g' tid;
 *)

  (* not sure if straight guard will work here
    (we need to use the lifetimes somewhere here)
  ty_proph E vπ d κ tid l κ' q :
    ty_gho_own vπ d g tid &&{↑NllftG}&&> 1:+[ξl]
    *)

  (*
  ty_own: proph 𝔄 → nat → thread_id → list val → iProp Σ;
  ty_shr: proph 𝔄 → nat → lft → thread_id → loc → iProp Σ;

  ty_shr_persistent vπ d κ tid l : Persistent (ty_shr vπ d κ tid l);

  ty_size_eq vπ d tid vl : ty_own vπ d tid vl -∗ ⌜length vl = ty_size⌝;
  ty_own_depth_mono d d' vπ tid vl :
    (d ≤ d')%nat → ty_own vπ d tid vl -∗ ty_own vπ d' tid vl;
  ty_shr_depth_mono d d' vπ κ tid l :
    (d ≤ d')%nat → ty_shr vπ d κ tid l -∗ ty_shr vπ d' κ tid l;
  ty_shr_lft_mono κ κ' vπ d tid l :
    κ' ⊑ κ -∗ ty_shr vπ d κ tid l -∗ ty_shr vπ d κ' tid l;

  (* The mask for starting the sharing does /not/ include the
      namespace N, for allowing more flexibility for the user of
      this type (typically for the [own] type). AFAIK, there is no
      fundamental reason for this.
      This should not be harmful, since sharing typically creates
      invariants, which does not need the mask.  Moreover, it is
      more consistent with thread-local tokens, which we do not
      give any.

      The lifetime token is needed (a) to make the definition of simple types
      nicer (they would otherwise require a "∨ □|=>[†κ]"), and (b) so that
      we can have emp == sum [].
    *)
  ty_share E vπ d κ l tid q : ↑lftN ⊆ E → lft_ctx -∗
    κ ⊑ lft_intersect_list ty_lfts -∗ &{κ} (l ↦∗: ty_own vπ d tid) -∗ q.[κ]
    ={E}=∗ |={E}▷=>^d |={E}=> ty_shr vπ d κ tid l ∗ q.[κ];

  ty_own_proph E vπ d tid vl κ q : ↑lftN ⊆ E → lft_ctx -∗
    κ ⊑ lft_intersect_list ty_lfts -∗ ty_own vπ d tid vl -∗ q.[κ]
    ={E}=∗ |={E}▷=>^d |={E}=> ∃ξl q', ⌜vπ ./ ξl⌝ ∗
      q':+[ξl] ∗ (q':+[ξl] ={E}=∗ ty_own vπ d tid vl ∗ q.[κ]);
  ty_shr_proph E vπ d κ tid l κ' q : ↑lftN ⊆ E → lft_ctx -∗ κ' ⊑ κ -∗
    κ' ⊑ lft_intersect_list ty_lfts -∗ ty_shr vπ d κ tid l -∗ q.[κ']
    ={E}▷=∗ |={E}▷=>^d |={E}=> ∃ξl q', ⌜vπ ./ ξl⌝ ∗
      q':+[ξl] ∗ (q':+[ξl] ={E}=∗ q.[κ']);
   *)
}.
(*Global Existing Instance ty_shr_persistent.*)
Global Instance: Params (@ty_size) 3 := {}.
Global Instance: Params (@ty_lfts) 3 := {}.
Global Instance: Params (@ty_E) 3 := {}.
Global Instance: Params (@ty_gho_own) 3 := {}.
Global Instance: Params (@ty_gho_pers) 3 := {}.
Global Instance: Params (@ty_gho_res) 3 := {}.
Global Instance: Params (@ty_phys) 3 := {}.
Arguments ty_size {_ _ _} _ / : simpl nomatch.
Arguments ty_lfts {_ _ _} _ / : simpl nomatch.
Arguments ty_E {_ _ _} _ / : simpl nomatch.
Arguments ty_gho_own {_ _ _} _ _ _ _ / : simpl nomatch.
Arguments ty_gho_pers {_ _ _} _ _ _ _ / : simpl nomatch.
Arguments ty_gho_res {_ _ _} _ _ _ _ / : simpl nomatch.
Arguments ty_phys {_ _ _} _ _ _ / : simpl nomatch.
Arguments ty_size_eq {_ _ _}.
Arguments ty_gho_own_depth_mono {_ _ _}.
Arguments ty_gho_pers_depth_mono {_ _ _}.
Global Existing Instance ty_gho_pers_pers.
Global Existing Instance ty_shr_persistent.
Global Instance: Params (@ty_shr) 3 := {}.
Arguments ty_shr {_ _ _} _ _ _ _ _ _ / : simpl nomatch.
Arguments ty_shr_lft_mono {_ _ _}.
Arguments ty_shr_depth_mono {_ _ _}.
Arguments ty_share {_ _ _}.
Arguments ty_shr_guard_proph {_ _ _}.

Notation ty_lft ty := (lft_intersect_list ty.(ty_lfts)).

Section ty_shr_lemmas.
  Context `{!typeG Σ}.

  (** Lifetime monotonicity for a lifetime inclusion (without laters). *)
  Lemma ty_shr_lft_mono0 {𝔄} (ty: type 𝔄) κ κ' x d g tid :
    κ' ⊑ κ -∗ ty.(ty_shr) κ x d g tid -∗ ty.(ty_shr) κ' x d g tid.
  Proof.
    iIntros "Incl Shr". iDestruct (ty_shr_lft_mono with "Incl Shr") as "Shr".
    by rewrite Nat.add_0_r.
  Qed.

  (** Whether a type uses the default sharing predicate. This is the case for every
      type defined with [ty_shr := default_shr ...] (and provable by [done]). *)
  Definition ty_shr_is_default {𝔄} (ty: type 𝔄) : Prop :=
    ∀ κ x d g tid, ty.(ty_shr) κ x d g tid = default_shr ty.(ty_gho_own) κ x d g tid.

  Lemma ty_shr_default_guard {𝔄} (ty: type 𝔄) κ x d g tid :
    ty_shr_is_default ty →
    ty.(ty_shr) κ x d g tid ⊣⊢ (@[κ] &&{↑NllftG; g+1}&&> ty.(ty_gho_own) x d g tid).
  Proof.
    move=> Def. rewrite Def. apply default_shr_guard. exact (ty_gho_own_depth_mono ty).
  Qed.
  Lemma ty_shr_default_to_guard {𝔄} (ty: type 𝔄) κ x d g tid :
    ty_shr_is_default ty →
    ty.(ty_shr) κ x d g tid -∗ (@[κ] &&{↑NllftG; g+1}&&> ty.(ty_gho_own) x d g tid).
  Proof. move=> ?. rewrite ty_shr_default_guard //. iIntros "$". Qed.

  Lemma ty_shr_default_from_guard {𝔄} (ty: type 𝔄) κ x d g tid :
    ty_shr_is_default ty →
    (@[κ] &&{↑NllftG; g+1}&&> ty.(ty_gho_own) x d g tid) -∗ ty.(ty_shr) κ x d g tid.
  Proof. move=> ?. rewrite ty_shr_default_guard //. iIntros "$". Qed.
End ty_shr_lemmas.

Notation typel := (hlist type).

Definition ty_own `{!typeG Σ} {𝔄} (ty: type 𝔄)
  (x: ~~ 𝔄) (d: nat) (g: nat) (tid: thread_id) (lv: list fancy_val) : iProp Σ :=
      ty.(ty_gho_own) x d g tid ∗ ⌜ty.(ty_phys) x tid = lv⌝.

Definition ty_outlives_E `{!typeG Σ} {𝔄} (ty: type 𝔄) (κ: lft) : elctx :=
  (λ α, κ ⊑ₑ α) <$> ty.(ty_lfts).

Lemma ty_outlives_E_elctx_sat `{!typeG Σ} {𝔄} E L (ty: type 𝔄) α β :
  ty_outlives_E ty β ⊆+ E → lctx_lft_incl E L α β →
  elctx_sat E L (ty_outlives_E ty α).
Proof.
  rewrite /ty_outlives_E. elim ty.(ty_lfts)=> [|?? IH]; [by solve_typing|].
  move=> Sub Incl. apply elctx_sat_lft_incl.
  - etrans; [by apply Incl|].
    eapply lctx_lft_incl_external, elem_of_submseteq, Sub. set_solver.
  - apply IH, Incl. etrans; [|by apply Sub]. by apply submseteq_cons.
Qed.

Lemma ty_outlives_E_elctx_sat_mono `{!typeG Σ} {𝔄} κ κ' (ty: type 𝔄) E L :
  lctx_lft_incl E L κ' κ → elctx_sat E L (ty_outlives_E ty κ) →
  elctx_sat E L (ty_outlives_E ty κ').
Proof.
  move=> ?. rewrite /ty_outlives_E. elim (ty_lfts ty); [done|]=>/= ?? IH ?.
  apply elctx_sat_lft_incl. { etrans; [done|]. by eapply elctx_sat_head. }
  apply IH. by eapply elctx_sat_tail.
Qed.

Lemma elctx_interp_ty_outlives_E `{!typeG Σ} {𝔄} (ty: type 𝔄) α :
  elctx_interp (ty_outlives_E ty α) ⊣⊢ α ⊑ ty_lft ty.
Proof.
  rewrite /ty_outlives_E /elctx_elt_interp big_sepL_fmap /=.
  elim ty.(ty_lfts)=>/= [|κ l ->].
  { iSplit; iIntros "_"; [|done]. iApply lft_incl_static. }
  iSplit.
  - iIntros "#[??]". by iApply llftl_incl_glb.
  - iIntros "#Incl".
    iSplit; (iApply llftl_incl_trans; [iApply "Incl"|]);
      [iApply llftl_intersect_incl_l|iApply llftl_intersect_incl_r].
Qed.

Definition tyl_lfts `{!typeG Σ} {𝔄l} (tyl: typel 𝔄l) : list lft :=
  concat ((λ _, ty_lfts) +c<$> tyl).
Definition tyl_lft `{!typeG Σ} {𝔄l} (tyl: typel 𝔄l) : lft :=
  lft_intersect_list (tyl_lfts tyl).
Definition tyl_E `{!typeG Σ} {𝔄l} (tyl: typel 𝔄l) : elctx :=
  concat ((λ _, ty_E) +c<$> tyl).
Definition tyl_outlives_E `{!typeG Σ} {𝔄l} (tyl: typel 𝔄l) (κ: lft) : elctx :=
  concat ((λ _ ty, ty_outlives_E ty κ) +c<$> tyl).

Lemma tyl_lfts_lookup_sublist `{!typeG Σ} {𝔄l} (tyl: typel 𝔄l) i :
  ty_lfts (tyl +!! i) `sublist_of` tyl_lfts tyl.
Proof.
  move: i. elim: tyl=>/=. { move=> i. inv_fin i. }
  move=> > IH i. inv_fin i=>/=. { exact: sublist_inserts_r. }
  etrans; [exact: IH|]. exact: sublist_inserts_l.
Qed.

Lemma tyl_outlives_E_elctx_sat `{!typeG Σ} {𝔄l} E L (tyl: typel 𝔄l) α β :
  tyl_outlives_E tyl β ⊆+ E → lctx_lft_incl E L α β →
  elctx_sat E L (tyl_outlives_E tyl α).
Proof.
  elim tyl; [solve_typing|]=> > IH Outlv Incl. apply elctx_sat_app.
  - eapply ty_outlives_E_elctx_sat; [|by apply Incl]. etrans; [|by apply Outlv].
    by apply submseteq_inserts_r.
  - apply IH; [|done]. etrans; [|by apply Outlv]. by apply submseteq_inserts_l.
Qed.

Lemma tyl_outlives_E_elctx_sat_mono `{!typeG Σ} {𝔄l} κ κ' (tyl: typel 𝔄l) E L :
  lctx_lft_incl E L κ' κ → elctx_sat E L (tyl_outlives_E tyl κ) →
  elctx_sat E L (tyl_outlives_E tyl κ').
Proof.
  move=> ?. rewrite /tyl_outlives_E. elim tyl; [done|]=>/= ???? IH ?.
  apply elctx_sat_app; last first. { apply IH. by eapply elctx_sat_app_r. }
  eapply ty_outlives_E_elctx_sat_mono; [done|]. by eapply elctx_sat_app_l.
Qed.

(** Simple Type *)

Record simple_type `{!typeG Σ} 𝔄 := {
  st_size: nat;
  st_lfts: list lft;
  st_E: elctx;
  
  st_gho: ~~𝔄 → nat → nat → thread_id → iProp Σ;
  st_phys: ~~𝔄 → thread_id → list fancy_val;
  
  st_gho_persistent x d g tid: Persistent (st_gho x d g tid);
  
  st_size_eq x tid : length (st_phys x tid) = st_size;
  st_size_eq2 : size_of 𝔄 = st_size;
  st_phys_eq2 x tid : syn_phys x = st_phys x tid;
  
  st_gho_depth_mono d g d' g' x tid :
    (d ≤ d')%nat → (g ≤ g')%nat → st_gho x d g tid -∗
        st_gho x d' g' tid ;
        
  st_guard_proph κ x n d g tid ξ R :
      ξ ∈ ξl x →
      llft_ctx -∗
      κ ⊑ lft_intersect_list st_lfts -∗ 
      st_gho x d g tid -∗
      
      ▷^(d*(g+2)) (
          (R &&{↑NllftG; n}&&> @[κ]) -∗
          (R &&{↑NllftG; n}&&> st_gho x d g tid) -∗
          (R &&{↑NllftG; n + d*(g+1)}&&> 1:[ξ])
      );
      
  st_concrete x tid : all_concrete (st_phys x tid) ;
}.
Global Existing Instance st_gho_persistent.
Global Instance: Params (@vπ) 3 := {}.
Global Instance: Params (@st_size) 3 := {}.
Global Instance: Params (@st_lfts) 3 := {}.
Global Instance: Params (@st_E) 3 := {}.
Global Instance: Params (@st_gho) 3 := {}.
Arguments st_size {_ _ _} _ / : simpl nomatch.
Arguments st_lfts {_ _ _} _ / : simpl nomatch.
Arguments st_E {_ _ _} _ / : simpl nomatch.
Arguments st_gho {_ _ _} _ _ _ _ / : simpl nomatch.
Arguments st_phys {_ _ _} _ _ / : simpl nomatch.

Program Definition ty_of_st `{!typeG Σ} {𝔄} (st: simple_type 𝔄) : type 𝔄 := {|
  ty_size := st.(st_size);
  ty_lfts := st.(st_lfts);
  ty_E := st.(st_E);
  ty_gho_own := st.(st_gho);
  ty_gho_res := st.(st_gho);
  ty_gho_pers := st.(st_gho);
  ty_phys := st.(st_phys);
  ty_shr := default_shr st.(st_gho);
|}%I.
Next Obligation. move=> >. apply st_size_eq. Qed.
Next Obligation. move=> >. apply st_size_eq2. Qed.
Next Obligation. move=> >. apply st_phys_eq2. Qed.
Next Obligation. move=> >. intros. iIntros "#A".
  iSplit. { by iApply st_gho_depth_mono. } iIntros "_". iFrame "A".
Qed.
Next Obligation. move=> >. intros. iIntros "#A". by iApply st_gho_depth_mono. Qed.
Next Obligation. move=> >. iIntros. iFrame "#". Qed.
Solve All Obligations with solve_default_shr.
Next Obligation.
  intros Σ ? 𝔄 st κ x n d g tid ξ R Hin. eapply default_shr_guard_proph; [| |done].
  - move=> > ??. iIntros "#A". iSplit; [by iApply st_gho_depth_mono|]. by iIntros "_".
  - move=> >. apply st_guard_proph.
Qed.

Coercion ty_of_st: simple_type >-> type.

(** Plain Type *)

Record plain_type `{!typeG Σ} 𝔄 := {
  pt_size: nat;
  pt_gho: ~~𝔄 → thread_id → iProp Σ;
  pt_phys: ~~𝔄 → thread_id → list fancy_val;
  pt_gho_persistent x tid : Persistent (pt_gho x tid);
  pt_size_eq x tid : length (pt_phys x tid) = pt_size;
  pt_size_eq2 : size_of 𝔄 = pt_size;
  pt_phys_eq2 x tid : syn_phys x = pt_phys x tid;
  pt_const : ∀ (x : ~~𝔄) π1 π2 , @vπ 𝔄 x π1 = @vπ 𝔄 x π2;
  pt_concrete x tid : all_concrete (pt_phys x tid);
  pt_non_prophetic (x: ~~𝔄) : ξl x = [];
}.
Global Existing Instance pt_gho_persistent.
Global Instance: Params (@pt_size) 3 := {}.
Global Instance: Params (@pt_gho) 3 := {}.
Global Instance: Params (@pt_phys) 3 := {}.
Arguments pt_size {_ _ _} _ / : simpl nomatch.
Arguments pt_gho {_ _ _} _ _ _ / : simpl nomatch.
Arguments pt_phys {_ _ _} _ _ _ / : simpl nomatch.

Program Definition st_of_pt `{!typeG Σ} {𝔄} (pt: plain_type 𝔄) : simple_type 𝔄 := {|
  st_size := pt.(pt_size);
  st_lfts := [];
  st_E := [];
  st_gho x d g tid := pt.(pt_gho) x tid;
  st_phys x tid := pt.(pt_phys) x tid;
|}%I.
Next Obligation. move=> >. apply pt_size_eq. Qed.
Next Obligation. move=> >. apply pt_size_eq2. Qed.
Next Obligation. move=> >. apply pt_phys_eq2. Qed.
Next Obligation. iIntros. iFrame "#". Qed.
Next Obligation. move=> >. intros Hin.
  rewrite (pt_non_prophetic) in Hin; trivial. set_solver. Qed.
Next Obligation. intros. apply pt_concrete. Qed.

Coercion st_of_pt: plain_type >-> simple_type.

Declare Scope lrust_type_scope.
Delimit Scope lrust_type_scope with T.
Bind Scope lrust_type_scope with type.

(** Ghost Type *)

Record ghost_type `{!typeG Σ} 𝔄 := {
  gt_gho : ~~𝔄 → thread_id → iProp Σ;
  gt_const : ∀ (x : ~~𝔄) π1 π2 , @vπ 𝔄 x π1 = @vπ 𝔄 x π2;
  gt_non_prophetic (x: ~~𝔄) : @ξl 𝔄 x = [];
  gt_size0 : size_of 𝔄 = 0;
  gt_phys0 (x: ~~𝔄) : @syn_phys 𝔄 x = [];
}.
Global Instance: Params (@gt_gho) 3 := {}.
Arguments gt_gho {_ _ _} _ _ / : simpl nomatch.

Program Definition ty_of_gt `{!typeG Σ} {𝔄} (gt: ghost_type 𝔄) : type 𝔄 := {|
  ty_size := 0;
  ty_lfts := [];
  ty_E := [];
  ty_gho_own x d g tid := gt.(gt_gho) x tid;
  ty_gho_res x d g tid := gt.(gt_gho) x tid;
  ty_gho_pers x d g tid := True%I;
  ty_phys x tid := [];
  ty_shr := default_shr (λ x d g tid, gt.(gt_gho) x tid);
|}%I.
Next Obligation. move=> * //=. Qed.
Next Obligation. move=> * //=. by rewrite gt_size0. Qed.
Next Obligation. move=> * //=. by rewrite gt_phys0. Qed.
Next Obligation. iIntros "**". iFrame. iIntros. done. Qed.
Next Obligation. iIntros "**". iFrame. iIntros. done. Qed.
Next Obligation. iIntros. done. Qed.
Solve All Obligations with solve_default_shr.
Next Obligation.
  intros. exfalso.
  match goal with H : _ ∈ ξl _ |- _ => rewrite gt_non_prophetic in H; set_solver end.
Qed.

Coercion ty_of_gt: ghost_type >-> type.

(** * OFE Structures on Types *)

Section ofe.
  Context `{!typeG Σ}.

  (**  Type *)

  Inductive type_equiv' {𝔄} (ty ty': type 𝔄) : Prop := TypeEquiv :
    ty.(ty_size) = ty'.(ty_size) →
    ty.(ty_lfts) = ty'.(ty_lfts) →
    ty.(ty_E) = ty'.(ty_E) →
    (∀x d g tid, ty.(ty_gho_own) x d g tid ≡ ty'.(ty_gho_own) x d g tid) →
    (∀x d g tid, (ty.(ty_gho_pers) x d g tid)%I ≡ (ty'.(ty_gho_pers) x d g tid)%I) →
    (∀x tid, ty.(ty_phys) x tid = ty'.(ty_phys) x tid) →
    (∀κ x d g tid, ty.(ty_shr) κ x d g tid ≡ ty'.(ty_shr) κ x d g tid) →
    type_equiv' ty ty'.
  Global Instance type_equiv {𝔄} : Equiv (type 𝔄) := type_equiv'.
  Inductive type_dist' {𝔄} (n: nat) (ty ty': type 𝔄) : Prop := TypeDist:
    ty.(ty_size) = ty'.(ty_size) → ty.(ty_lfts) = ty'.(ty_lfts) → ty.(ty_E) = ty'.(ty_E) →
    (∀x d g tid, ty.(ty_gho_own) x d g tid ≡{n}≡ ty'.(ty_gho_own) x d g tid) →
    (∀x d g tid, (ty.(ty_gho_pers) x d g tid)%I ≡{n}≡ (ty'.(ty_gho_pers) x d g tid)%I) →
    (∀x tid, ty.(ty_phys) x tid = ty'.(ty_phys) x tid) →
    (∀κ x d g tid, ty.(ty_shr) κ x d g tid ≡{n}≡ ty'.(ty_shr) κ x d g tid) →
    type_dist' n ty ty'.
  Global Instance type_dist {𝔄} : Dist (type 𝔄) := type_dist'.

  Definition type_unpack {𝔄} (ty: type 𝔄)
    : prodO (prodO (prodO (prodO (prodO (prodO
        natO (listO lftO))
        (listO (prodO lftO lftO)))
        (~~𝔄 -d> nat -d> nat -d> thread_id -d> iProp Σ))
        (~~𝔄 -d> nat -d> nat -d> thread_id -d> iProp Σ))
        (~~𝔄 -d> thread_id -d> leibnizO (list fancy_val)))
        (lft -d> ~~𝔄 -d> nat -d> nat -d> thread_id -d> iProp Σ) :=
    (ty.(ty_size), ty.(ty_lfts), ty.(ty_E), ty.(ty_gho_own), ty.(ty_gho_pers), 
      ty.(ty_phys), ty.(ty_shr)).

  Definition type_ofe_mixin {𝔄} : OfeMixin (type 𝔄).
  Proof.
    apply (iso_ofe_mixin type_unpack);
    (rewrite /type_unpack; split; [by move=> [->->->???]|]);
    move=> [[[[[[/=??]?]?]?]?]?]; constructor; try apply leibniz_equiv;
    try done; by eapply (discrete_iff _ _).
  Qed.
  Canonical Structure typeO 𝔄 : ofe := Ofe (type 𝔄) type_ofe_mixin.
End ofe.

Section ofe_lemmas.
  Context `{!typeG Σ}.

  Global Instance ty_size_ne {𝔄} n : Proper (dist n ==> (=)) (ty_size (𝔄:=𝔄)).
  Proof. move=> ?? Eqv. apply Eqv. Qed.
  Global Instance ty_size_proper {𝔄} : Proper ((≡) ==> (=)) (ty_size (𝔄:=𝔄)).
  Proof. move=> ?? Eqv. apply Eqv. Qed.
  Global Instance ty_lfts_ne {𝔄} n : Proper (dist n ==> (=)) (ty_lfts (𝔄:=𝔄)).
  Proof. move=> ?? Eqv. apply Eqv. Qed.
  Global Instance ty_lfts_proper {𝔄} : Proper ((≡) ==> (=)) (ty_lfts (𝔄:=𝔄)).
  Proof. move=> ?? Eqv. apply Eqv. Qed.
  Global Instance ty_E_ne {𝔄} n : Proper (dist n ==> (=)) (ty_E (𝔄:=𝔄)).
  Proof. move=> ?? Eqv. apply Eqv. Qed.
  Global Instance ty_E_proper {𝔄} : Proper ((≡) ==> (=)) (ty_E (𝔄:=𝔄)).
  Proof. move=> ?? Eqv. apply Eqv. Qed.
  Global Instance ty_outlives_E_ne {𝔄} n :
    Proper (dist n ==> (=) ==> (=)) (ty_outlives_E (𝔄:=𝔄)).
  Proof. rewrite /ty_outlives_E. by move=> ?? [_ -> _ _ _]. Qed.
  Global Instance ty_outlives_E_proper {𝔄} :
    Proper ((≡) ==> (=) ==> (=)) (ty_outlives_E (𝔄:=𝔄)).
  Proof. rewrite /ty_outlives_E. by move=> ?? [_ -> _ _ _]. Qed.

  Global Instance tyl_lfts_ne {𝔄l} n : Proper (dist n ==> (=)) (tyl_lfts (𝔄l:=𝔄l)).
  Proof.
    rewrite /tyl_lfts /dist=> tyl tyl' Eq. f_equal.
    induction Eq; [done|]. by rewrite/= H IHEq.
  Qed.
  Global Instance tyl_lfts_proper {𝔄l} : Proper ((≡) ==> (=)) (tyl_lfts (𝔄l:=𝔄l)).
  Proof.
    rewrite /tyl_lfts /equiv=> tyl tyl' Eq. f_equal.
    induction Eq; [done|]. by rewrite/= H IHEq.
  Qed.
  Global Instance tyl_lft_ne {𝔄l} n : Proper (dist n ==> (=)) (tyl_lft (𝔄l:=𝔄l)).
  Proof. rewrite /tyl_lft. by move=> ??->. Qed.
  Global Instance tyl_lft_proper {𝔄l} : Proper ((≡) ==> (=)) (tyl_lft (𝔄l:=𝔄l)).
  Proof. rewrite /tyl_lft. by move=> ??->. Qed.
  Global Instance tyl_E_ne {𝔄l} n : Proper (dist n ==> (=)) (tyl_E (𝔄l:=𝔄l)).
  Proof.
    rewrite /tyl_E /dist=> tyl tyl' Eq.
    induction Eq; [done|]. by rewrite/= H IHEq.
  Qed.
  Global Instance tyl_E_proper {𝔄l} : Proper ((≡) ==> (=)) (tyl_E (𝔄l:=𝔄l)).
  Proof.
    rewrite /tyl_E /equiv=> tyl tyl' Eq.
    induction Eq; [done|]. by rewrite/= H IHEq.
  Qed.
  Global Instance tyl_outlives_E_ne {𝔄l} n :
    Proper (dist n ==> (=) ==> (=)) (tyl_outlives_E (𝔄l:=𝔄l)).
  Proof.
    rewrite /tyl_outlives_E /dist=> tyl tyl' Eq ??->.
    induction Eq; [done|]. by rewrite/= H IHEq.
  Qed.
  Global Instance tyl_outlives_E_proper {𝔄l} :
    Proper ((≡) ==> (=) ==> (=)) (tyl_outlives_E (𝔄l:=𝔄l)).
  Proof.
    rewrite /tyl_outlives_E /equiv=> tyl tyl' Eq ??->.
    induction Eq; [done|]. by rewrite/= H IHEq.
  Qed.

  Global Instance ty_gho_own_ne {𝔄} n:
    Proper (dist n ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n) (ty_gho_own (𝔄:=𝔄)).
  Proof. move=> ?? Eqv ??->??->??->??->. apply Eqv. Qed.
  Global Instance ty_gho_pers_ne {𝔄} n:
    Proper (dist n ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n) (ty_gho_pers (𝔄:=𝔄)).
  Proof. move=> ?? Eqv ??->??->??->??->. apply Eqv. Qed.
  Global Instance ty_gho_own_proper {𝔄} :
    Proper ((≡) ==> (=) ==> (=) ==> (=) ==> (=) ==> (≡)) (ty_gho_own (𝔄:=𝔄)).
  Proof. move=> ?? Eqv ??->??->??->??->. apply Eqv. Qed.
  Global Instance ty_gho_pers_proper {𝔄} :
    Proper ((≡) ==> (=) ==> (=) ==> (=) ==> (=) ==> (≡)) (ty_gho_pers (𝔄:=𝔄)).
  Proof. move=> ?? Eqv ??->??->??->??->. apply Eqv. Qed.
  Global Instance ty_shr_ne {𝔄} n:
    Proper (dist n ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n) (ty_shr (𝔄:=𝔄)).
  Proof. move=> ?? Eqv ??->??->??->??->??->. apply Eqv. Qed.
  Global Instance ty_shr_proper {𝔄} :
    Proper ((≡) ==> (=) ==> (=) ==> (=) ==> (=) ==> (=) ==> (≡)) (ty_shr (𝔄:=𝔄)).
  Proof. move=> ?? Eqv ??->??->??->??->??->. apply Eqv. Qed.
  Global Instance ty_phys_ne {𝔄} n :
    Proper (dist n ==> (=) ==> (=) ==> (=)) (ty_phys (𝔄:=𝔄)).
  Proof. move=> ?? Eqv ??->??->. apply Eqv. Qed.
  Global Instance ty_phys_proper {𝔄} :
    Proper ((≡) ==> (=) ==> (=) ==> (=)) (ty_phys (𝔄:=𝔄)).
  Proof. move=> ?? Eqv ??->??->. apply Eqv. Qed.
  
  (** Simple Type *)

  Section simple_type_ofe.
  Inductive simple_type_equiv' {𝔄} (st st': simple_type 𝔄) : Prop := SimpleTypeEquiv:
    st.(st_size) = st'.(st_size) → st.(st_lfts) = st'.(st_lfts) → st.(st_E) = st'.(st_E) →
    (∀x d g tid, st.(st_gho) x d g tid ≡ st'.(st_gho) x d g tid) →
    (∀x tid, st.(st_phys) x tid = st'.(st_phys) x tid) →
    simple_type_equiv' st st'.
  Global Instance simple_type_equiv {𝔄} : Equiv (simple_type 𝔄) := simple_type_equiv'.
  Inductive simple_type_dist' {𝔄} (n: nat) (st st': simple_type 𝔄) : Prop :=
    SimpleTypeDist:
    st.(st_size) = st'.(st_size) → st.(st_lfts) = st'.(st_lfts) → st.(st_E) = st'.(st_E) →
    (∀x d g tid, st.(st_gho) x d g tid ≡{n}≡ st'.(st_gho) x d g tid) →
    (∀x tid, st.(st_phys) x tid = st'.(st_phys) x tid) →
    simple_type_dist' n st st'.
  Global Instance simple_type_dist {𝔄} : Dist (simple_type 𝔄) := simple_type_dist'.

  Definition simple_type_ofe_mixin {𝔄} : OfeMixin (simple_type 𝔄).
  Proof.
    apply (iso_ofe_mixin ty_of_st); (split=> Eqv; split; try by apply Eqv);
    move=> > /=; (apply default_shr_proper || apply default_shr_ne); apply Eqv.
  Qed.
  Canonical Structure simple_typeO 𝔄 : ofe := Ofe (simple_type 𝔄) simple_type_ofe_mixin.
  End simple_type_ofe.
  
  Global Instance st_gho_ne {𝔄} n:
    Proper (dist n ==> (=) ==> (=) ==> (=) ==> (=) ==> dist n) (st_gho (𝔄:=𝔄)).
  Proof. move=> ?? Eqv ??->??->??->??->. apply Eqv. Qed.
  Global Instance st_gho_proper {𝔄} :
    Proper ((≡) ==> (=) ==> (=) ==> (=) ==> (=) ==> (≡)) (st_gho (𝔄:=𝔄)).
  Proof. move=> ?? Eqv ??->??->??->??->. apply Eqv. Qed.
  Global Instance st_phys_ne {𝔄} n :
    Proper (dist n ==> (=) ==> (=) ==> (=)) (st_phys (𝔄:=𝔄)).
  Proof. move=> ?? Eqv ??->??->. apply Eqv. Qed.
  Global Instance st_phys_proper {𝔄} :
    Proper ((≡) ==> (=) ==> (=) ==> (=)) (st_phys (𝔄:=𝔄)).
  Proof. move=> ?? Eqv ??->??->. apply Eqv. Qed.

  Global Instance ty_of_st_ne {𝔄} : NonExpansive (@ty_of_st _ _ 𝔄).
  Proof.
    move=> ??? Eqv. split; try apply Eqv. move=> */=. apply default_shr_ne, Eqv.
  Qed.
  Global Instance ty_of_st_proper {𝔄} : Proper ((≡) ==> (≡)) (ty_of_st (𝔄:=𝔄)).
  Proof. apply (ne_proper _). Qed.

  (** Plain Type *)

  Section plain_type_ofe.
  Inductive plain_type_equiv' {𝔄} (pt pt': plain_type 𝔄) : Prop := PlainTypeEquiv:
    pt.(pt_size) = pt'.(pt_size) →
    (∀x tid, pt.(pt_gho) x tid ≡ pt'.(pt_gho) x tid) →
    (∀x tid, pt.(pt_phys) x tid = pt'.(pt_phys) x tid) →
    plain_type_equiv' pt pt'.
  Global Instance plain_type_equiv {𝔄} : Equiv (plain_type 𝔄) := plain_type_equiv'.
  Inductive plain_type_dist' {𝔄} (n: nat) (pt pt': plain_type 𝔄) : Prop := PlainTypeDist:
    pt.(pt_size) = pt'.(pt_size) →
    (∀x tid, pt.(pt_gho) x tid ≡{n}≡ (pt'.(pt_gho) x tid)) →
    (∀x tid, pt.(pt_phys) x tid = (pt'.(pt_phys) x tid)) →
    plain_type_dist' n pt pt'.
  Global Instance plain_type_dist {𝔄} : Dist (plain_type 𝔄) := plain_type_dist'.

  Definition plain_type_unpack {𝔄} (pt: plain_type 𝔄)
    : prodO (prodO natO
        (~~𝔄 -d> thread_id -d> iPropO Σ))
        (~~𝔄 -d> thread_id -d> leibnizO (list fancy_val)) :=
    (pt.(pt_size), pt.(pt_gho), pt.(pt_phys)).

  Definition plain_type_ofe_mixin {𝔄} : OfeMixin (plain_type 𝔄).
  Proof.
    apply (iso_ofe_mixin plain_type_unpack);
    (rewrite /plain_type_unpack; split; [by move=> [->?]|]);
    move=> [/=[??]?]; constructor; try apply leibniz_equiv;
    try done; by eapply (discrete_iff _ _).
  Qed.
  Canonical Structure plain_typeO 𝔄 : ofe := Ofe (plain_type 𝔄) plain_type_ofe_mixin.
  End plain_type_ofe.

  Global Instance pt_gho_ne n {𝔄} :
    Proper (dist n ==> (=) ==> (=) ==> dist n) (pt_gho (𝔄:=𝔄)).
  Proof. move=> ?? Eqv ??->??->. apply Eqv. Qed.
  Global Instance pt_gho_proper {𝔄} :
    Proper ((≡) ==> (=) ==> (=) ==> (≡)) (pt_gho (𝔄:=𝔄)).
  Proof. move=> ?? Eqv ??->??->. apply Eqv. Qed.
  
  Global Instance pt_phys_ne n {𝔄} :
    Proper (dist n ==> (=) ==> (=) ==> (=)) (pt_phys (𝔄:=𝔄)).
  Proof. move=> ?? Eqv ??->??->. apply Eqv. Qed.
  Global Instance pt_phys_proper {𝔄} :
    Proper ((≡) ==> (=) ==> (=) ==> (=)) (pt_phys (𝔄:=𝔄)).
  Proof. move=> ?? Eqv ??->??->. apply Eqv. Qed.

  Global Instance st_of_pt_ne {𝔄} : NonExpansive (@st_of_pt _ _ 𝔄).
  Proof.
    move=> ??? [? Eqv ?]. split=>//= *.
  Qed.
  Global Instance st_of_pt_proper {𝔄} : Proper ((≡) ==> (≡)) (st_of_pt (𝔄:=𝔄)).
  Proof. apply (ne_proper _). Qed.

  (** Ghost Type *)

  Section ghost_type_ofe.
  Inductive ghost_type_equiv' {𝔄} (gt gt': ghost_type 𝔄) : Prop := GhostTypeEquiv:
    (∀vπ tid, gt.(gt_gho) vπ tid ≡ gt'.(gt_gho) vπ tid) →
    ghost_type_equiv' gt gt'.
  Global Instance ghost_type_equiv {𝔄} : Equiv (ghost_type 𝔄) := ghost_type_equiv'.
  Inductive ghost_type_dist' {𝔄} (n: nat) (gt gt': ghost_type 𝔄) : Prop :=
    GhostTypeDist:
    (∀vπ tid, gt.(gt_gho) vπ tid ≡{n}≡ gt'.(gt_gho) vπ tid) →
    ghost_type_dist' n gt gt'.
  Global Instance ghost_type_dist {𝔄} : Dist (ghost_type 𝔄) := ghost_type_dist'.

  Definition ghost_type_unpack {𝔄} (gt: ghost_type 𝔄)
    : (~~𝔄 -d> thread_id -d> iPropO Σ) :=
    gt.(gt_gho).

  Definition ghost_type_ofe_mixin {𝔄} : OfeMixin (ghost_type 𝔄).
  Proof.
    apply (iso_ofe_mixin ghost_type_unpack); rewrite /ghost_type_unpack=> *;
    split=>//; by case.
  Qed.
  Canonical Structure ghost_typeO 𝔄 : ofe := Ofe (ghost_type 𝔄) ghost_type_ofe_mixin.
  End ghost_type_ofe.
  
  Global Instance gt_gho_ne {𝔄} n:
    Proper (dist n ==> (=) ==> (=) ==> dist n) (gt_gho (𝔄:=𝔄)).
  Proof. move=> ?? Eqv ??->??->. apply Eqv. Qed.
  Global Instance gt_gho_proper {𝔄} :
    Proper ((≡) ==> (=) ==> (=) ==> (≡)) (gt_gho (𝔄:=𝔄)).
  Proof. move=> ?? Eqv ??->??->. apply Eqv. Qed.

  Global Instance ty_of_gt_ne {𝔄} : NonExpansive (@ty_of_gt _ _ 𝔄).
  Proof.
    move => n x y [Eqv].
    constructor => //= *. by apply default_shr_ne.
  Qed.
  Global Instance ty_of_gt_proper {𝔄} : Proper ((≡) ==> (≡)) (ty_of_gt (𝔄:=𝔄)).
  Proof. apply (ne_proper _). Qed.

  (** For types with the default sharing predicate, the sharing predicates are as
      close as the ownership predicates. *)
  Lemma type_dist_default {𝔄} n (ty ty': type 𝔄) :
    ty_shr_is_default ty → ty_shr_is_default ty' →
    ty.(ty_size) = ty'.(ty_size) → ty.(ty_lfts) = ty'.(ty_lfts) → ty.(ty_E) = ty'.(ty_E) →
    (∀x d g tid, ty.(ty_gho_own) x d g tid ≡{n}≡ ty'.(ty_gho_own) x d g tid) →
    (∀x d g tid, ty.(ty_gho_pers) x d g tid ≡{n}≡ ty'.(ty_gho_pers) x d g tid) →
    (∀x tid, ty.(ty_phys) x tid = ty'.(ty_phys) x tid) →
    ty ≡{n}≡ ty'.
  Proof.
    move=> Def Def' ?????. split=>// *. rewrite Def Def'. by apply default_shr_ne.
  Qed.
End ofe_lemmas.

Ltac solve_ne_type :=
  constructor;
  solve_proper_core ltac:(fun _ => (
    (eapply ty_size_ne || eapply ty_lfts_ne || eapply ty_E_ne ||
     eapply ty_outlives_E_ne || eapply ty_gho_own_ne || eapply ty_phys_ne ||
     eapply ty_shr_ne); try reflexivity
  ) || (apply default_shr_ne; intros) || f_equiv).

(** * Nonexpansiveness/Contractiveness of Type Morphisms *)

Inductive TypeLftMorphism `{!typeG Σ} {𝔄 𝔅} (T: type 𝔄 → type 𝔅) : Prop :=
| type_lft_morphism_add α βs E :
    (∀ty, ⊢ ty_lft (T ty) ≡ₗ α ⊓ ty_lft ty) →
    (∀ty, elctx_interp (T ty).(ty_E) ⊣⊢
      elctx_interp E ∗ elctx_interp ty.(ty_E) ∗ [∗ list] β ∈ βs, β ⊑ ty_lft ty) →
    TypeLftMorphism T
| type_lft_morphism_const α E :
    (∀ty, ⊢ ty_lft (T ty) ≡ₗ α) →
    (∀ty, elctx_interp (T ty).(ty_E) ⊣⊢ elctx_interp E) →
    TypeLftMorphism T.
Existing Class TypeLftMorphism.

Section type_lft_morphism.
Context `{!typeG Σ}.

Lemma type_lft_morphism_id_like {𝔄 𝔅} (T: type 𝔄 → type 𝔅) :
  (∀ty, (T ty).(ty_lfts) = ty.(ty_lfts)) → (∀ty, (T ty).(ty_E) = ty.(ty_E)) →
  TypeLftMorphism T.
Proof.
  move=> EqLfts EqE. apply (type_lft_morphism_add _ static [] [])=> ?.
  + rewrite left_id EqLfts. apply lft_equiv_refl.
  + by rewrite/= left_id right_id EqE.
Qed.

Lemma type_lft_morphism_add_one {𝔄 𝔅} κ (T: type 𝔄 → type 𝔅) :
  (∀ty, (T ty).(ty_lfts) = κ :: ty.(ty_lfts)) →
  (∀ty, (T ty).(ty_E) = ty.(ty_E) ++ ty_outlives_E ty κ) →
  TypeLftMorphism T.
Proof.
  move=> EqLfts EqE. apply (type_lft_morphism_add _ κ [κ] [])=> ?.
  + rewrite EqLfts. apply lft_equiv_refl.
  + by rewrite EqE elctx_interp_app elctx_interp_ty_outlives_E /= left_id right_id.
Qed.

Global Instance type_lft_morphism_compose {𝔄 𝔅 ℭ}
    (T: type 𝔅 → type ℭ) (U: type 𝔄 → type 𝔅) :
  TypeLftMorphism T → TypeLftMorphism U → TypeLftMorphism (T ∘ U).
Proof.
  case=> [αT βst ET HTα HTE|αT ET HTα HTE]; case=> [αU βsU EU HUα HUE|αU EU HUα HUE].
  - apply (type_lft_morphism_add _ (αT ⊓ αU) (βst ++ βsU)
                                 (ET ++ EU ++ ((λ β, β ⊑ₑ αU) <$> βst)))=>ty.
    + iApply lft_equiv_trans. iApply HTα. rewrite -assoc.
      iApply lft_intersect_equiv_proper; [iApply lft_equiv_refl|iApply HUα].
    + rewrite HTE HUE !elctx_interp_app big_sepL_app -!assoc.
      setoid_rewrite (lft_incl_equiv_proper_r _ _ _ (HUα _)). iSplit.
      * iIntros "($ & $ & $ & $ & H)". rewrite big_sepL_fmap.
        iSplit; iApply (big_sepL_impl with "H"); iIntros "!> * _ #H";
        (iApply llftl_incl_trans; [done|]);
        [iApply llftl_intersect_incl_l|iApply llftl_intersect_incl_r].
      * iIntros "($ & $ & H1 & $ & H2 & $)".
        rewrite big_sepL_fmap. iCombine "H1 H2" as "H".
        rewrite -big_sepL_sep. iApply (big_sepL_impl with "H").
        iIntros "!> * _ #[??]". by iApply llftl_incl_glb.
  - apply (type_lft_morphism_const _ (αT ⊓ αU)
            (ET ++ EU ++ ((λ β, β ⊑ₑ αU) <$> βst)))=>ty.
    + iApply lft_equiv_trans. iApply HTα.
      iApply lft_intersect_equiv_proper; [iApply lft_equiv_refl|iApply HUα].
    + rewrite HTE HUE !elctx_interp_app big_sepL_fmap.
      do 5 f_equiv. by apply lft_incl_equiv_proper_r.
  - apply (type_lft_morphism_const _ αT ET)=>//=.
  - apply (type_lft_morphism_const _ αT ET)=>//=.
Qed.

Lemma type_lft_morphism_lft_equiv_proper {𝔄 𝔅} (T: type 𝔄 → type 𝔅)
  {HT: TypeLftMorphism T} ty ty' :
  ty_lft ty ≡ₗ ty_lft ty' -∗ ty_lft (T ty) ≡ₗ ty_lft (T ty').
Proof.
  iIntros "#?". case HT=> [α βs E Hα HE|α E Hα HE].
  - iApply lft_equiv_trans; [|iApply lft_equiv_sym; iApply Hα].
    iApply lft_equiv_trans; [iApply Hα|].
    iApply lft_intersect_equiv_proper; [iApply lft_equiv_refl|done].
  - iApply lft_equiv_trans; [|iApply lft_equiv_sym; iApply Hα].
    iApply lft_equiv_trans; [iApply Hα|]. iApply lft_equiv_refl.
Qed.

Lemma type_lft_morphism_elctx_interp_proper {𝔄 𝔅} (T: type 𝔄 → type 𝔅)
  {HT: TypeLftMorphism T} ty ty' :
  elctx_interp ty.(ty_E) ≡ elctx_interp ty'.(ty_E) → (⊢ ty_lft ty ≡ₗ ty_lft ty') →
  elctx_interp (T ty).(ty_E) ≡ elctx_interp (T ty').(ty_E).
Proof.
  move=> EqvE EqvLft. move: HT=> [|] > ? HE; [|by rewrite !HE].
  rewrite !HE EqvE. do 5 f_equiv. by apply lft_incl_equiv_proper_r.
Qed.
End type_lft_morphism.

(** The sharing predicate is treated as living "one step later" than the ownership
    predicates (as in RustBelt): the ownership predicates of [T ty] may depend on the
    sharing predicate of [ty] without a later (e.g. [&shr{κ} ty]), but then the sharing
    predicate of [T ty] may only depend on the ownership predicates of [ty] under one
    more later than on its sharing predicate. Concretely, a non-expansive [T] maps types
    that are n-close in their ownership predicates and (n+1)-close in their sharing
    predicates to such types, and a contractive [T] does so given types that are
    (n-1)-close in their ownership predicates and n-close in their sharing predicates. *)
Class TypeNonExpansive `{!typeG Σ} {𝔄 𝔅} (T: type 𝔄 → type 𝔅) : Prop := {
  #[global] type_ne_type_lft_morphism :: TypeLftMorphism T;
  type_ne_ty_size ty ty' :
    ty.(ty_size) = ty'.(ty_size) → (T ty).(ty_size) = (T ty').(ty_size);
  type_ne_ty_gho_own n ty ty' :
    ty.(ty_size) = ty'.(ty_size) → (⊢ ty_lft ty ≡ₗ ty_lft ty') →
    elctx_interp ty.(ty_E) ≡ elctx_interp ty'.(ty_E) →
    (∀vπ d g tid, ty.(ty_gho_own) vπ d g tid ≡{n}≡ ty'.(ty_gho_own) vπ d g tid) →
    (∀vπ d g tid, ty.(ty_gho_pers) vπ d g tid ≡{n}≡ ty'.(ty_gho_pers) vπ d g tid) →
    (∀vπ tid, ty.(ty_phys) vπ tid = ty'.(ty_phys) vπ tid) →
    (∀κ vπ d g tid, ty.(ty_shr) κ vπ d g tid ≡{S n}≡ ty'.(ty_shr) κ vπ d g tid) →
    (∀vπ d g tid, (T ty).(ty_gho_own) vπ d g tid ≡{n}≡ (T ty').(ty_gho_own) vπ d g tid);
  type_ne_ty_gho_pers n ty ty' :
    ty.(ty_size) = ty'.(ty_size) → (⊢ ty_lft ty ≡ₗ ty_lft ty') →
    elctx_interp ty.(ty_E) ≡ elctx_interp ty'.(ty_E) →
    (∀vπ d g tid, ty.(ty_gho_own) vπ d g tid ≡{n}≡ ty'.(ty_gho_own) vπ d g tid) →
    (∀vπ d g tid, ty.(ty_gho_pers) vπ d g tid ≡{n}≡ ty'.(ty_gho_pers) vπ d g tid) →
    (∀vπ tid, ty.(ty_phys) vπ tid = ty'.(ty_phys) vπ tid) →
    (∀κ vπ d g tid, ty.(ty_shr) κ vπ d g tid ≡{S n}≡ ty'.(ty_shr) κ vπ d g tid) →
    (∀vπ d g tid, (T ty).(ty_gho_pers) vπ d g tid ≡{n}≡ (T ty').(ty_gho_pers) vπ d g tid);
  type_ne_ty_phys ty ty' :
    ty.(ty_size) = ty'.(ty_size) →
    (∀vπ tid, ty.(ty_phys) vπ tid = ty'.(ty_phys) vπ tid) →
    (∀vπ tid, (T ty).(ty_phys) vπ tid = (T ty').(ty_phys) vπ tid);
  type_ne_ty_shr n ty ty' :
    ty.(ty_size) = ty'.(ty_size) → (⊢ ty_lft ty ≡ₗ ty_lft ty') →
    elctx_interp ty.(ty_E) ≡ elctx_interp ty'.(ty_E) →
    (∀vπ d g tid, dist_later n (ty.(ty_gho_own) vπ d g tid) (ty'.(ty_gho_own) vπ d g tid)) →
    (∀vπ d g tid, dist_later n (ty.(ty_gho_pers) vπ d g tid) (ty'.(ty_gho_pers) vπ d g tid)) →
    (∀vπ tid, ty.(ty_phys) vπ tid = ty'.(ty_phys) vπ tid) →
    (∀κ vπ d g tid, ty.(ty_shr) κ vπ d g tid ≡{n}≡ ty'.(ty_shr) κ vπ d g tid) →
    (∀κ vπ d g tid, (T ty).(ty_shr) κ vπ d g tid ≡{n}≡ (T ty').(ty_shr) κ vπ d g tid);
}.

Class TypeContractive `{!typeG Σ} {𝔄 𝔅} (T: type 𝔄 → type 𝔅) : Prop := {
  type_contractive_type_lft_morphism : TypeLftMorphism T;
  type_contractive_ty_size ty ty' : (T ty).(ty_size) = (T ty').(ty_size);
  type_contractive_ty_gho_own n ty ty' :
    ty.(ty_size) = ty'.(ty_size) → (⊢ ty_lft ty ≡ₗ ty_lft ty') →
    elctx_interp ty.(ty_E) ≡ elctx_interp ty'.(ty_E) →
    (∀vπ d g tid, dist_later n (ty.(ty_gho_own) vπ d g tid) (ty'.(ty_gho_own) vπ d g tid)) →
    (∀vπ d g tid, dist_later n (ty.(ty_gho_pers) vπ d g tid) (ty'.(ty_gho_pers) vπ d g tid)) →
    (∀vπ tid, ty.(ty_phys) vπ tid = ty'.(ty_phys) vπ tid) →
    (∀κ vπ d g tid, ty.(ty_shr) κ vπ d g tid ≡{n}≡ ty'.(ty_shr) κ vπ d g tid) →
    (∀vπ d g tid, (T ty).(ty_gho_own) vπ d g tid ≡{n}≡ (T ty').(ty_gho_own) vπ d g tid);
  type_contractive_ty_gho_pers n ty ty' :
    ty.(ty_size) = ty'.(ty_size) → (⊢ ty_lft ty ≡ₗ ty_lft ty') →
    elctx_interp ty.(ty_E) ≡ elctx_interp ty'.(ty_E) →
    (∀vπ d g tid, dist_later n (ty.(ty_gho_own) vπ d g tid) (ty'.(ty_gho_own) vπ d g tid)) →
    (∀vπ d g tid, dist_later n (ty.(ty_gho_pers) vπ d g tid) (ty'.(ty_gho_pers) vπ d g tid)) →
    (∀vπ tid, ty.(ty_phys) vπ tid = ty'.(ty_phys) vπ tid) →
    (∀κ vπ d g tid, ty.(ty_shr) κ vπ d g tid ≡{n}≡ ty'.(ty_shr) κ vπ d g tid) →
    (∀vπ d g tid, (T ty).(ty_gho_pers) vπ d g tid ≡{n}≡ (T ty').(ty_gho_pers) vπ d g tid);
  type_contractive_ty_phys ty ty' :
    ty.(ty_size) = ty'.(ty_size) →
    (∀vπ tid, ty.(ty_phys) vπ tid = ty'.(ty_phys) vπ tid) →
    (∀vπ tid, (T ty).(ty_phys) vπ tid = (T ty').(ty_phys) vπ tid);
  (* The ownership predicates are only required to be (n-2)-close here. *)
  type_contractive_ty_shr n ty ty' :
    ty.(ty_size) = ty'.(ty_size) → (⊢ ty_lft ty ≡ₗ ty_lft ty') →
    elctx_interp ty.(ty_E) ≡ elctx_interp ty'.(ty_E) →
    (∀vπ d g tid, dist_later (pred n) (ty.(ty_gho_own) vπ d g tid) (ty'.(ty_gho_own) vπ d g tid)) →
    (∀vπ d g tid, dist_later (pred n) (ty.(ty_gho_pers) vπ d g tid) (ty'.(ty_gho_pers) vπ d g tid)) →
    (∀vπ tid, ty.(ty_phys) vπ tid = ty'.(ty_phys) vπ tid) →
    (∀κ vπ d g tid, dist_later n (ty.(ty_shr) κ vπ d g tid) (ty'.(ty_shr) κ vπ d g tid)) →
    (∀κ vπ d g tid, (T ty).(ty_shr) κ vπ d g tid ≡{n}≡ (T ty').(ty_shr) κ vπ d g tid);
}.

Class ListTypeNonExpansive `{!typeG Σ} {𝔄 𝔅l} (T: type 𝔄 → typel 𝔅l) : Prop :=
  type_list_non_expansive: ∃Tl, T = (Tl +$.) ∧ TCHForall (λ _, TypeNonExpansive) Tl.

Class ListTypeContractive `{!typeG Σ} {𝔄 𝔅l} (T: type 𝔄 → typel 𝔅l) : Prop :=
  type_list_contractive: ∃Tl, T = (Tl +$.) ∧ TCHForall (λ _, TypeContractive) Tl.

Section type_contractive.
  Context `{!typeG Σ}.

  Lemma dist_later_pred {A: ofe} n (x y: A) : dist_later n x y → dist_later (pred n) x y.
  Proof. move=> [Eq]. split=> ??. apply Eq. lia. Qed.

  Global Instance type_contractive_type_ne {𝔄 𝔅} (T: type 𝔄 → type 𝔅) :
    TypeContractive T → TypeNonExpansive T.
  Proof.
    move=> HT. split; [by apply HT|move=> *; by apply HT| | | |].
    - move=> *. apply HT=>// *; by [apply dist_dist_later|apply dist_S].
    - move=> *. apply HT=>// *; by [apply dist_dist_later|apply dist_S].
    - move=> n *. apply HT=>// *.
    - move=> *. apply HT=>// *; by [apply dist_later_pred|apply dist_dist_later].
  Qed.

  (* The hypotheses on [ty] and [ty'], weakened to a smaller step-index. *)
  Local Ltac type_ne_hyps :=
    intros; repeat match goal with
    | H: ∀ _ _ _ _, dist_later _ _ _ |- dist_later _ _ _ =>
        split=> ??; eapply dist_later_lt; [apply H|lia]
    | H: ∀ _ _ _ _ _, dist_later _ _ _ |- dist_later _ _ _ =>
        split=> ??; eapply dist_later_lt; [apply H|lia]
    | H: ∀ _ _ _ _, dist_later _ _ _ |- dist _ _ _ =>
        eapply dist_later_lt; [apply H|lia]
    | H: ∀ _ _ _ _ _, dist_later _ _ _ |- dist _ _ _ =>
        eapply dist_later_lt; [apply H|lia]
    | H: ∀ _ _ _ _, dist _ _ _ |- dist_later _ _ _ =>
        split=> ??; eapply dist_le; [apply H|lia]
    | H: ∀ _ _ _ _, dist _ _ _ |- dist _ _ _ => eapply dist_le; [apply H|lia]
    | H: ∀ _ _ _ _ _, dist _ _ _ |- dist_later _ _ _ =>
        split=> ??; eapply dist_le; [apply H|lia]
    | H: ∀ _ _ _ _ _, dist _ _ _ |- dist _ _ _ => eapply dist_le; [apply H|lia]
    end.

  (* Applies the clause [clause] of the class instance [HT'] for the inner type morphism,
     at a step-index to be determined, and discharges its hypotheses. *)
  Local Ltac type_ne_inner HT' :=
    intros; first
      [ apply HT'; first [done|type_ne_hyps]
      | split=> ??; apply HT'; first [done|type_ne_hyps] ].

  Local Ltac type_ne_outer HT HT' :=
    move=> n ty ty' *; apply HT;
    [ by apply HT'
    | by iApply type_lft_morphism_lft_equiv_proper
    | apply type_lft_morphism_elctx_interp_proper=>//; apply _
    | type_ne_inner HT' .. ].

  Global Instance type_ne_ne_compose {𝔄 𝔅 ℭ} (T: type 𝔅 → type ℭ) (T': type 𝔄 → type 𝔅) :
    TypeNonExpansive T → TypeNonExpansive T' → TypeNonExpansive (T ∘ T').
  Proof.
    move=> HT HT'. split; [by apply _|move=> *; by apply HT, HT'| | | |].
    - type_ne_outer HT HT'.
    - type_ne_outer HT HT'.
    - move=> *. apply HT; try apply HT'; trivial.
    - type_ne_outer HT HT'.
  Qed.

  Global Instance type_contractive_compose_right {𝔄 𝔅 ℭ} (T: type 𝔅 → type ℭ) (T': type 𝔄 → type 𝔅) :
    TypeContractive T → TypeNonExpansive T' → TypeContractive (T ∘ T').
  Proof.
    move=> HT HT'. split; [by apply _|move=> *; by apply HT| | | |].
    - type_ne_outer HT HT'.
    - type_ne_outer HT HT'.
    - intros. apply HT; apply HT'; trivial.
    - type_ne_outer HT HT'.
  Qed.

  Global Instance type_contractive_compose_left {𝔄 𝔅 ℭ}
         (T: type 𝔅 → type ℭ) (T': type 𝔄 → type 𝔅) :
    TypeNonExpansive T → TypeContractive T' → TypeContractive (T ∘ T').
  Proof.
    move=> HT HT'. split; [by apply _|move=> *; by apply HT, HT'| | | |].
    - type_ne_outer HT HT'.
    - type_ne_outer HT HT'.
    - intros. apply HT; apply HT'; trivial.
    - type_ne_outer HT HT'.
  Qed.

  Global Instance const_type_contractive {𝔄 𝔅} (ty: type 𝔄) :
    TypeContractive (λ _: type 𝔅, ty).
  Proof. split; move=>// *. eright=> _; by [iApply lft_equiv_refl|]. Qed.

  Global Instance id_type_ne {𝔄} : TypeNonExpansive (id: type 𝔄 → type 𝔄).
  Proof. split=>//. by apply type_lft_morphism_id_like. Qed.

  Global Instance type_list_non_expansive_nil {𝔄} :
    ListTypeNonExpansive (λ _: type 𝔄, +[]).
  Proof. exists +[]. split; by [|constructor]. Qed.
  Global Instance type_list_contractive_nil {𝔄} :
    ListTypeContractive (λ _: type 𝔄, +[]).
  Proof. exists +[]. split; by [|constructor]. Qed.
  Global Instance type_list_non_expansive_cons {𝔄 𝔅 𝔅l}
         (T: type 𝔄 → type 𝔅) (T': type 𝔄 → typel 𝔅l) :
    TypeNonExpansive T → ListTypeNonExpansive T' →
    ListTypeNonExpansive (λ ty, T ty +:: T' ty).
  Proof. move=> ? [Tl[->?]]. exists (T +:: Tl). split; by [|constructor]. Qed.
  Global Instance type_list_contractive_cons {𝔄 𝔅 𝔅l}
         (T: type 𝔄 → type 𝔅) (T': type 𝔄 → typel 𝔅l) :
    TypeContractive T → ListTypeContractive T' →
    ListTypeContractive (λ ty, T ty +:: T' ty).
  Proof. move=> ? [Tl[->?]]. exists (T +:: Tl). split; by [|constructor]. Qed.
  (** For type morphisms producing types with the default sharing predicate, the
      clauses about the sharing predicate follow from the others. *)
  Lemma type_ne_default {𝔄 𝔅} (T: type 𝔄 → type 𝔅) :
    (∀ty, ty_shr_is_default (T ty)) →
    TypeLftMorphism T →
    (∀ ty ty', ty.(ty_size) = ty'.(ty_size) → (T ty).(ty_size) = (T ty').(ty_size)) →
    (∀ n ty ty',
      ty.(ty_size) = ty'.(ty_size) → (⊢ ty_lft ty ≡ₗ ty_lft ty') →
      elctx_interp ty.(ty_E) ≡ elctx_interp ty'.(ty_E) →
      (∀vπ d g tid, ty.(ty_gho_own) vπ d g tid ≡{n}≡ ty'.(ty_gho_own) vπ d g tid) →
      (∀vπ d g tid, ty.(ty_gho_pers) vπ d g tid ≡{n}≡ ty'.(ty_gho_pers) vπ d g tid) →
      (∀vπ tid, ty.(ty_phys) vπ tid = ty'.(ty_phys) vπ tid) →
      (∀κ vπ d g tid, ty.(ty_shr) κ vπ d g tid ≡{S n}≡ ty'.(ty_shr) κ vπ d g tid) →
      (∀vπ d g tid, (T ty).(ty_gho_own) vπ d g tid ≡{n}≡ (T ty').(ty_gho_own) vπ d g tid)) →
    (∀ n ty ty',
      ty.(ty_size) = ty'.(ty_size) → (⊢ ty_lft ty ≡ₗ ty_lft ty') →
      elctx_interp ty.(ty_E) ≡ elctx_interp ty'.(ty_E) →
      (∀vπ d g tid, ty.(ty_gho_own) vπ d g tid ≡{n}≡ ty'.(ty_gho_own) vπ d g tid) →
      (∀vπ d g tid, ty.(ty_gho_pers) vπ d g tid ≡{n}≡ ty'.(ty_gho_pers) vπ d g tid) →
      (∀vπ tid, ty.(ty_phys) vπ tid = ty'.(ty_phys) vπ tid) →
      (∀κ vπ d g tid, ty.(ty_shr) κ vπ d g tid ≡{S n}≡ ty'.(ty_shr) κ vπ d g tid) →
      (∀vπ d g tid, (T ty).(ty_gho_pers) vπ d g tid ≡{n}≡ (T ty').(ty_gho_pers) vπ d g tid)) →
    (∀ ty ty',
      ty.(ty_size) = ty'.(ty_size) →
      (∀vπ tid, ty.(ty_phys) vπ tid = ty'.(ty_phys) vπ tid) →
      (∀vπ tid, (T ty).(ty_phys) vπ tid = (T ty').(ty_phys) vπ tid)) →
    TypeNonExpansive T.
  Proof.
    move=> Def ?? Own ??. split=>//. move=> n ty ty' ???????? *. rewrite !Def.
    apply default_shr_contractive=> *. split=> ??. apply Own; first [done|type_ne_hyps].
  Qed.

  Lemma type_contractive_default {𝔄 𝔅} (T: type 𝔄 → type 𝔅) :
    (∀ty, ty_shr_is_default (T ty)) →
    TypeLftMorphism T →
    (∀ ty ty', (T ty).(ty_size) = (T ty').(ty_size)) →
    (∀ n ty ty',
      ty.(ty_size) = ty'.(ty_size) → (⊢ ty_lft ty ≡ₗ ty_lft ty') →
      elctx_interp ty.(ty_E) ≡ elctx_interp ty'.(ty_E) →
      (∀vπ d g tid, dist_later n (ty.(ty_gho_own) vπ d g tid) (ty'.(ty_gho_own) vπ d g tid)) →
      (∀vπ d g tid, dist_later n (ty.(ty_gho_pers) vπ d g tid) (ty'.(ty_gho_pers) vπ d g tid)) →
      (∀vπ tid, ty.(ty_phys) vπ tid = ty'.(ty_phys) vπ tid) →
      (∀κ vπ d g tid, ty.(ty_shr) κ vπ d g tid ≡{n}≡ ty'.(ty_shr) κ vπ d g tid) →
      (∀vπ d g tid, (T ty).(ty_gho_own) vπ d g tid ≡{n}≡ (T ty').(ty_gho_own) vπ d g tid)) →
    (∀ n ty ty',
      ty.(ty_size) = ty'.(ty_size) → (⊢ ty_lft ty ≡ₗ ty_lft ty') →
      elctx_interp ty.(ty_E) ≡ elctx_interp ty'.(ty_E) →
      (∀vπ d g tid, dist_later n (ty.(ty_gho_own) vπ d g tid) (ty'.(ty_gho_own) vπ d g tid)) →
      (∀vπ d g tid, dist_later n (ty.(ty_gho_pers) vπ d g tid) (ty'.(ty_gho_pers) vπ d g tid)) →
      (∀vπ tid, ty.(ty_phys) vπ tid = ty'.(ty_phys) vπ tid) →
      (∀κ vπ d g tid, ty.(ty_shr) κ vπ d g tid ≡{n}≡ ty'.(ty_shr) κ vπ d g tid) →
      (∀vπ d g tid, (T ty).(ty_gho_pers) vπ d g tid ≡{n}≡ (T ty').(ty_gho_pers) vπ d g tid)) →
    (∀ ty ty',
      ty.(ty_size) = ty'.(ty_size) →
      (∀vπ tid, ty.(ty_phys) vπ tid = ty'.(ty_phys) vπ tid) →
      (∀vπ tid, (T ty).(ty_phys) vπ tid = (T ty').(ty_phys) vπ tid)) →
    TypeContractive T.
  Proof.
    move=> Def ?? Own ??. split=>//. move=> n ty ty' ???????? *. rewrite !Def.
    apply default_shr_contractive=> *. split=> ??. apply Own; first [done|type_ne_hyps].
  Qed.
End type_contractive.

(** * Traits *)

Fixpoint shr_locsE (l: loc) (n: nat) : coPset :=
  match n with O => ∅ | S n => ↑shrN.@l ∪ shr_locsE (l +ₗ 1) n end.

Class Copy `{!typeG Σ} {𝔄} (ty: type 𝔄) := {
  copy_persistent x d g tid : Persistent (ty.(ty_gho_own) x d g tid);
  copy_concrete x d g tid : ty.(ty_gho_own) x d g tid ⊢ ⌜all_concrete (ty.(ty_phys) x tid)⌝;
  (* Copying out of a shared reference: the sharing predicate gives (persistent)
     access to the ownership predicate while κ is alive. *)
  copy_shr κ x d g tid :
    ty.(ty_shr) κ x d g tid ⊢ (@[κ] &&{↑NllftG; g+1}&&> ty.(ty_gho_own) x d g tid);
}.
Global Existing Instance copy_persistent.
Global Instance: Params (@Copy) 3 := {}.

Notation ListCopy := (TCHForall (λ 𝔄, @Copy _ _ 𝔄)).

Class Send `{!typeG Σ} {𝔄} (ty: type 𝔄) := {
  send_change_tid_phys tid tid' x x' :
      @syn_abstract 𝔄 x = @syn_abstract 𝔄 x' → (ty.(ty_phys) x tid = ty.(ty_phys) x' tid');
  send_change_tid tid tid' x d g G H κs d0 :
    d + 1 ≤ d0 →
    Timeless G →
    Timeless H →
    (llft_ctx -∗ uniq_ctx -∗ time_ctx -∗
      (H &&{↑SendN}&&> cna_lifetimes tid κs) -∗ H -∗
      (∀ (κ: lft) , ⌜κ ∈ κs⌝ -∗ (G &&{↑NllftG}&&> @[κ])) -∗ G -∗
      ty.(ty_gho_own) x d g tid -∗ ⧖(d0) -∗
      |={↑Nllft ∪ ↑SendN ∪ ↑nainvN ∪ ↑uniqN ∪ (↑timeN ∪ ↑prophN)}▷=>^(d) |={↑Nllft ∪ ↑SendN ∪ ↑nainvN ∪ ↑uniqN ∪ (↑timeN ∪ ↑prophN)}=>
      ∃ x' off, 
      ty.(ty_gho_own) x' (d+off) g tid' ∗ ⧖(d0+off) ∗ ⌜@syn_abstract 𝔄 x' = @syn_abstract 𝔄 x⌝ ∗ G ∗ H
     )
}.
Global Instance: Params (@Send) 3 := {}.

Notation ListSend := (TCHForall (λ 𝔄, @Send _ _ 𝔄)).

Class Sync `{!typeG Σ} {𝔄} (ty: type 𝔄) :=
  sync_change_tid tid tid' x d g :
    (ty.(ty_phys) x tid = ty.(ty_phys) x tid') ∧
    (ty.(ty_gho_own) x d g tid ⊣⊢ ty.(ty_gho_own) x d g tid') ∧
    (ty.(ty_gho_pers) x d g tid ⊣⊢ ty.(ty_gho_pers) x d g tid') ∧
    (∀κ, ty.(ty_shr) κ x d g tid ⊣⊢ ty.(ty_shr) κ x d g tid').
Global Instance: Params (@Sync) 3 := {}.

Notation ListSync := (TCHForall (λ 𝔄, @Sync _ _ 𝔄)).

Class JustLoc `{!typeG Σ} {𝔄} (ty: type 𝔄) : Prop :=
  just_loc vπ d g tid : ty.(ty_gho_own) vπ d g tid -∗ ⌜∃l: loc, ty.(ty_phys) vπ tid = [FVal (#l)]⌝.

Section traits.
  Context `{!typeG Σ}.

  (** Lemmas on Copy *)

  Global Instance copy_equiv {𝔄} : Proper ((≡) ==> impl) (Copy (𝔄:=𝔄)).
  Proof.
    move=> ty ty' [EqSz ? ? EqOwn EqPers EqPhys EqShr] Hcopy. split=> >.
    - rewrite -EqOwn. apply _.
    - rewrite -EqPhys. inversion Hcopy as [_ Hconc]. rewrite -EqOwn. apply Hconc.
    - rewrite -EqShr. setoid_rewrite <-EqOwn. apply copy_shr.
  Qed.

  Lemma copy_shr_default {𝔄} (ty: type 𝔄) κ x d g tid :
    ty_shr_is_default ty →
    ty.(ty_shr) κ x d g tid ⊢ (@[κ] &&{↑NllftG; g+1}&&> ty.(ty_gho_own) x d g tid).
  Proof. move=> ?. by iApply ty_shr_default_to_guard. Qed.

  Global Program Instance simple_type_copy {𝔄} (st: simple_type 𝔄) : Copy st.
  Next Obligation. iIntros. iPureIntro. apply st_concrete. Qed.
  Next Obligation. intros. by apply copy_shr_default. Qed.

  (** Lemmas on Send and Sync *)

  Global Instance send_equiv {𝔄} : Proper ((≡) ==> impl) (Send (𝔄:=𝔄)).
  Proof.
    move=> ?? [_ _ _ Eqv Eqv2 Eqv3 _] Hyp. destruct Hyp as [Hphys Hgho].
    split.
    - intros tid tid' x x'. rewrite -!Eqv3. apply Hphys.
    - intros. setoid_rewrite <- Eqv. apply Hgho; trivial.
  Qed.

  Global Instance sync_equiv {𝔄} : Proper ((≡) ==> impl) (Sync (𝔄:=𝔄)).
  Proof. move=> ?? [_ _ _ Eqv Eqv2 Eqv3 Eqv4] Hyp. rewrite /Sync=> *. split.
    - rewrite -!Eqv3. apply Hyp. { auto. } { auto. }
    - split; [|split].
      + rewrite -!Eqv. apply Hyp.
      + rewrite -!Eqv2. apply Hyp.
      + move=> ?. rewrite -!Eqv4. apply Hyp.
  Qed.

  (** For a type with the default sharing predicate, Sync follows from the
      tid-independence of the other components. *)
  Lemma sync_default {𝔄} (ty: type 𝔄) :
    ty_shr_is_default ty →
    (∀ tid tid' x d g,
      (ty.(ty_phys) x tid = ty.(ty_phys) x tid') ∧
      (ty.(ty_gho_own) x d g tid ⊣⊢ ty.(ty_gho_own) x d g tid') ∧
      (ty.(ty_gho_pers) x d g tid ⊣⊢ ty.(ty_gho_pers) x d g tid')) →
    Sync ty.
  Proof.
    move=> Def Hyp tid tid' x d g. destruct (Hyp tid tid' x d g) as (?&?&?).
    do 3 (split; [done|]). move=> ?. rewrite !Def. apply default_shr_change_tid.
    move=> *. apply Hyp.
  Qed.

  (* VerusBelt: this doesn't work anymore; Sync is proved on a per-type basis
  Global Instance simple_type_sync {𝔄} (st: simple_type 𝔄) : Send st → Sync st.
  Proof. move=> Eq >/=. by setoid_rewrite Eq at 1. Qed.
  *)
    
  (* anything that can go in a "stack variable", i.e., in `p ◁ ty` without needing to be
    behind a pointer: int, bool, own, &shr, &uniq, ptr.
    This is mostly to prevent cells from going outside the heap, which would be annoying
    and unnecessary to support *)
  Definition StackOkay {𝔄} (ty: type 𝔄) :=
    (∀ x tid, all_concrete (ty.(ty_phys) x tid)).
End traits.

(** * resolve *)

Definition resolve `{!typeG Σ} {𝔄} (E: elctx) (L: llctx) (ty: type 𝔄) (Φ: ~~ 𝔄 → proph_asn → Prop) : Prop :=
  ∀G F x d g tid, Timeless G → ↑Nllft ∪ ↑prophN ∪ ↑timeN ∪ ↑uniqN ⊆ F →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ time_ctx -∗ elctx_interp E -∗ (G &&{↑NllftG}&&> llctx_interp L) -∗ G -∗
    ty.(ty_gho_own) x d g tid ={F}=∗ |={F}▷=>^(d*(g+1)) |={F}=> ⟨π, Φ x π⟩ ∗ G.
Global Instance: Params (@resolve) 3 := {}.

Definition resolvel `{!typeG Σ} {𝔄l} (E: elctx) (L: llctx) (tyl: typel 𝔄l)
                 (Φl: plist (λ 𝔄, ~~ 𝔄 → proph_asn → Prop) 𝔄l) : Prop :=
  HForall_1 (λ _, resolve E L) tyl Φl.

Definition resolve' `{!typeG Σ} {𝔄} (E: elctx) (L: llctx) (ty: type 𝔄)
                 (Φ: ~~ 𝔄 → proph_asn → Prop → Prop) :=
  resolve E L ty (λ a π, ∀φ, Φ a π φ → φ).

(** Resolution that keeps the resolved ownership [ty_gho_res] (see the place type [OfRes]
    of [typing/ltype.v]): as [resolve], and in addition the resolved ownership of the
    value is left. *)
Definition resolve_keep `{!typeG Σ} {𝔄} (E: elctx) (L: llctx) (ty: type 𝔄)
    (Φ: ~~ 𝔄 → proph_asn → Prop) : Prop :=
  ∀G F x d g tid, Timeless G → ↑Nllft ∪ ↑prophN ∪ ↑timeN ∪ ↑uniqN ⊆ F →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ time_ctx -∗ elctx_interp E -∗ (G &&{↑NllftG}&&> llctx_interp L) -∗ G -∗
    ty.(ty_gho_own) x d g tid ={F}=∗ |={F}▷=>^(d*(g+1)) |={F}=>
      ⟨π, Φ x π⟩ ∗ G ∗ ty.(ty_gho_res) x d g tid.
Global Instance: Params (@resolve_keep) 3 := {}.

(** The types whose resolved ownership is their ownership (no unique borrow is reachable
    from their values). *)
Class ResOwn `{!typeG Σ} {𝔄} (ty: type 𝔄) :=
  res_own x d g tid : ty.(ty_gho_res) x d g tid ⊣⊢ ty.(ty_gho_own) x d g tid.
Global Instance: Params (@ResOwn) 3 := {}.

Section resolve.
  Context `{!typeG Σ}.

  Global Instance simple_type_res_own {𝔄} (st: simple_type 𝔄) : ResOwn st.
  Proof. done. Qed.
  Global Instance ghost_type_res_own {𝔄} (gt: ghost_type 𝔄) : ResOwn gt.
  Proof. done. Qed.

  Lemma resolve_keep_resolve {𝔄} (ty: type 𝔄) E L Φ :
    resolve_keep E L ty Φ → resolve E L ty Φ.
  Proof.
    move=> Rslv > ?. iIntros "LFT PROPH UNIQ TIME E L G ty".
    iMod (Rslv with "LFT PROPH UNIQ TIME E L G ty") as "Upd"; [done..|].
    iApply (step_fupdN_wand with "Upd"). iIntros "!> >($ & $ & _)". done.
  Qed.

  Lemma resolve_keep_impl {𝔄} (ty: type 𝔄) E L (Φ Φ': ~~𝔄 → proph_asn → Prop) :
    resolve_keep E L ty Φ → (∀a π, Φ a π → Φ' a π) → resolve_keep E L ty Φ'.
  Proof.
    move=> Rslv Imp > ?. iIntros "LFT PROPH UNIQ TIME E L G ty".
    iMod (Rslv with "LFT PROPH UNIQ TIME E L G ty") as "Upd"; [done..|].
    iApply (step_fupdN_wand with "Upd"). iIntros "!> >(Obs & $ & $) !>".
    iApply proph_obs_impl; [|done]=>/= ?. apply Imp.
  Qed.

  (** Nothing is learnt from a type whose resolved ownership is its ownership. *)
  Lemma resolve_keep_just {𝔄} (ty: type 𝔄) `{!ResOwn ty} E L :
    resolve_keep E L ty (const (const True)).
  Proof.
    move=> > ?. iIntros "_ _ _ _ _ _ $ ty !>". iApply step_fupdN_full_intro.
    rewrite res_own. iFrame. by iApply proph_obs_true.
  Qed.
End resolve.

Section resolve.
  Context `{!typeG Σ}.

  Lemma resolve_just {𝔄} (ty: type 𝔄) E L : resolve E L ty (const (const True)).
  Proof.
    move=> > ?. iIntros "_ _ _ _ _ _ $ _!>". iApply step_fupdN_full_intro.
    by iApply proph_obs_true.
  Qed.

  Lemma resolve_impl {𝔄} (ty: type 𝔄) E L (Φ Φ': ~~𝔄 → proph_asn → Prop) :
    resolve E L ty Φ → (∀a π, Φ a π → Φ' a π) → resolve E L ty Φ'.
  Proof.
    move=> Rslv Imp > ?. iIntros "LFT PROPH UNIQ TIME E #L G ty".
    iMod (Rslv with "LFT PROPH UNIQ TIME E L G ty") as "ToObs"; [done|].
    iApply (step_fupdN_wand with "ToObs"). iIntros "!> >[? $] !>".
    iApply proph_obs_impl; [|done]=>/= ?. apply Imp.
  Qed.

  Lemma resolvel_nil E L : resolvel E L +[] -[].
  Proof. constructor. Qed.
  Lemma resolvel_cons {𝔄 𝔄l} E L (ty: type 𝔄) (tyl: typel 𝔄l) Φ Φl :
    resolve E L ty Φ → resolvel E L tyl Φl → resolvel E L (ty +:: tyl) (Φ -:: Φl).
  Proof. by constructor. Qed.

  Lemma resolve'_post {𝔄} (ty: type 𝔄) E L Φ :
    resolve E L ty Φ → resolve' E L ty (λ a π φ, Φ a π → φ).
  Proof. move=> ?. eapply resolve_impl; [done|]=>/= ???? Imp. by apply Imp. Qed.

  Lemma resolve'_just {𝔄} (ty: type 𝔄) E L Φ :
    resolve E L ty (const Φ) → resolve' E L ty (const (const id)).
  Proof. move=> _. by eapply resolve_impl; [apply resolve_just|]=>/=. Qed.

  (** A [Copy] type is resolved from a copy of its (persistent) ownership. *)
  Lemma resolve_keep_copy {𝔄} (ty: type 𝔄) `{!Copy ty, !ResOwn ty} E L Φ :
    resolve E L ty Φ → resolve_keep E L ty Φ.
  Proof.
    move=> Rslv > ?. iIntros "LFT PROPH UNIQ TIME E L G #ty".
    iMod (Rslv with "LFT PROPH UNIQ TIME E L G ty") as "Upd"; [done..|].
    iApply (step_fupdN_wand with "Upd"). iIntros "!> >[$ $] !>". by rewrite res_own.
  Qed.
End resolve.

(** * Subtyping *)

Set Printing Implicit.
Definition type_incl `{!typeG Σ} {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) (f: 𝔄 →ₛ 𝔅)
  : iProp Σ :=
  ⌜ty.(ty_size) = ty'.(ty_size)⌝ ∗ (ty_lft ty' ⊑ ty_lft ty) ∗
  (□ ∀x d g tid, ty.(ty_gho_own) x d g tid -∗ ty'.(ty_gho_own) (f ~~$ₛ x) d g tid
                    ∗ (ty'.(ty_gho_own) (f ~~$ₛ x) d g tid -∗ ty.(ty_gho_own) x d g tid)) ∗
  (□ ∀x d g tid, ty.(ty_gho_pers) x d g tid -∗ ty'.(ty_gho_pers) (f ~~$ₛ x) d g tid) ∗
  ⌜∀x tid, ty.(ty_phys) x tid = ty'.(ty_phys) (f ~~$ₛ x) tid⌝ ∗
  (□ ∀κ x d g tid, ty.(ty_shr) κ x d g tid -∗ ty'.(ty_shr) κ (f ~~$ₛ x) d g tid).
Global Instance: Params (@type_incl) 4 := {}.

Definition subtype `{!typeG Σ} {𝔄 𝔅} E L (ty: type 𝔄) (ty': type 𝔅) (f: 𝔄 →ₛ 𝔅)
  : Prop := llctx_interp L -∗ □ (elctx_interp E -∗ type_incl ty ty' f).
Global Instance: Params (@subtype) 6 := {}.

Definition eqtype `{!typeG Σ} {𝔄 𝔅} E L (ty: type 𝔄) (ty': type 𝔅)
  (f: 𝔄 →ₛ 𝔅) (g: 𝔅 →ₛ 𝔄) : Prop := subtype E L ty ty' f ∧ subtype E L ty' ty g.
Global Instance: Params (@eqtype) 6 := {}.

Definition subtype_id `{!typeG Σ} {𝔄} E L (ty ty': type 𝔄) : Prop
  := subtype E L ty ty' idₛ.
Definition eqtype_id `{!typeG Σ} {𝔄} E L (ty ty': type 𝔄) : Prop
  := eqtype E L ty ty' idₛ idₛ.

Definition subtypel `{!typeG Σ} {𝔄l 𝔅l} E L (tyl: typel 𝔄l) (tyl': typel 𝔅l)
  (fl: plist2 (λ 𝔄 𝔅, 𝔄 →ₛ 𝔅) 𝔄l 𝔅l) : Prop :=
  HForall2_1 (λ _ _ ty ty' f, subtype E L ty ty' f) tyl tyl' fl.
Definition eqtypel `{!typeG Σ} {𝔄l 𝔅l} E L (tyl: typel 𝔄l) (tyl': typel 𝔅l)
  (fl: plist2 (λ 𝔄 𝔅, 𝔄 →ₛ 𝔅) 𝔄l 𝔅l) (gl: plist2 (λ 𝔄 𝔅, 𝔄 →ₛ 𝔅) 𝔅l 𝔄l) : Prop :=
  HForall2_2flip (λ _ _ ty ty' f g, eqtype E L ty ty' f g) tyl tyl' fl gl.

Section subtyping.
  Context `{!typeG Σ}.

  (** Subtyping *)

  Lemma eqtype_unfold {𝔄 𝔅} E L f g `{!Isoₛ f g} (ty : type 𝔄) (ty' : type 𝔅) :
    (llctx_interp L -∗ □ (elctx_interp E -∗
      ⌜ty.(ty_size) = ty'.(ty_size)⌝ ∗ ty_lft ty ≡ₗ ty_lft ty' ∗
      (□ ∀x d g tid, ty.(ty_gho_own) x d g tid ↔ ty'.(ty_gho_own) (f ~~$ₛ x) d g tid) ∗
      (□ ∀x d g tid, ty.(ty_gho_pers) x d g tid ↔ ty'.(ty_gho_pers) (f ~~$ₛ x) d g tid) ∗
      ⌜∀x tid, ty.(ty_phys) x tid = ty'.(ty_phys) (f ~~$ₛ x) tid⌝ ∗
      (□ ∀κ x d g tid, ty.(ty_shr) κ x d g tid ↔ ty'.(ty_shr) κ (f ~~$ₛ x) d g tid)))
    ↔ eqtype E L ty ty' f g.
  Proof.
    split.
    - move=> Eqt. split; iIntros "L".
      + iDestruct (Eqt with "L") as "#Eqt". iIntros "!> #E".
        iDestruct ("Eqt" with "E") as "(%EqSize & [#EqLft1 #EqLft2] & EqOwn & EqOwnPers & %EqPhys & EqShr)".
        iSplit; [done|]. iSplit; [done|]. iSplit.
        * iIntros "!>". iIntros. iSplitL.
          { iApply "EqOwn". iFrame. }
          { iIntros. iApply "EqOwn". iFrame. }
        * iSplitL.
          { iModIntro. iIntros. iApply "EqOwnPers". iFrame "#". } 
          iSplit; [done|].
          { iModIntro. iIntros. iApply "EqShr". iFrame "#". }
      + iDestruct (Eqt with "L") as "#Eqt". iIntros "!> #E".
        iDestruct ("Eqt" with "E") as "(%EqSize & [#EqLft1 #EqLft2] & EqOwn & EqOwnPers & %EqPhys & EqShr)".
        iSplit; [done|]. iSplit; [done|]. iSplit; [|iSplit; [|iSplit]].
        * iIntros "!>". iIntros. iSplitL. { iApply "EqOwn". iFrame.
            destruct Isoₛ0. rewrite semi_iso'. done. }
          { iIntros "x". iDestruct ("EqOwn" with "x") as "x".
            destruct Isoₛ0. rewrite semi_iso'. done. }
        * iIntros "!>". iIntros.
            { iIntros. iApply "EqOwnPers". destruct Isoₛ0. rewrite semi_iso'. done. }
        * iPureIntro. iIntros (x tid). rewrite (EqPhys (g ~~$ₛ x)).
            destruct Isoₛ0. rewrite semi_iso'. trivial.
        * iIntros "!>". iIntros.
            { iIntros. iApply "EqShr". destruct Isoₛ0. rewrite semi_iso'. done. }
    - iIntros ([Sub Sub']) "L". iDestruct (Sub with "L") as "#Sub".
      iDestruct (Sub' with "L") as "#Sub'". iIntros "!> #E".
      iDestruct ("Sub" with "E") as "[A[B[InOwn [InPers [InPhys InShr]]]]]".
      iDestruct ("Sub'" with "E") as "[D[F[InOwn' [InPers' [InPhys' InShr']]]]]".
      iFrame "A". iFrame "B". iFrame "F".
      iSplit; [|iSplit; [|iSplit]].
      + iIntros "!>*". iSplit.
        { iIntros "x". iDestruct ("InOwn" with "x") as "[y y']". iFrame "y". }
        { iIntros "x". iDestruct ("InOwn'" with "x") as "[y y']".
          destruct Isoₛ0. rewrite semi_iso'. iFrame "y". }
      + iIntros "!>*". iSplit.
        { iIntros "X". iApply "InPers". iFrame "X". }
        { iIntros "X". iDestruct ("InPers'" with "X") as "X".
            destruct Isoₛ0. rewrite semi_iso'. iFrame "X". }
      + iApply "InPhys".
      + iIntros "!>*". iSplit.
        { iIntros "X". iApply "InShr". iFrame "X". }
        { iIntros "X". iDestruct ("InShr'" with "X") as "X".
            destruct Isoₛ0. rewrite semi_iso'. iFrame "X". }
  Qed.

  (** A variant of [eqtype_unfold] for types whose sharing predicate is (equivalent to)
      the default one: the equivalence of the sharing predicates is derived. *)
  Lemma eqtype_unfold_default {𝔄 𝔅} E L f g `{!Isoₛ f g} (ty : type 𝔄) (ty' : type 𝔅) :
    (∀κ x d g tid, ty.(ty_shr) κ x d g tid ⊣⊢ default_shr ty.(ty_gho_own) κ x d g tid) →
    (∀κ x d g tid, ty'.(ty_shr) κ x d g tid ⊣⊢ default_shr ty'.(ty_gho_own) κ x d g tid) →
    (llctx_interp L -∗ □ (elctx_interp E -∗
      ⌜ty.(ty_size) = ty'.(ty_size)⌝ ∗ ty_lft ty ≡ₗ ty_lft ty' ∗
      (□ ∀x d g tid, ty.(ty_gho_own) x d g tid ↔ ty'.(ty_gho_own) (f ~~$ₛ x) d g tid) ∗
      (□ ∀x d g tid, ty.(ty_gho_pers) x d g tid ↔ ty'.(ty_gho_pers) (f ~~$ₛ x) d g tid) ∗
      ⌜∀x tid, ty.(ty_phys) x tid = ty'.(ty_phys) (f ~~$ₛ x) tid⌝)) →
    eqtype E L ty ty' f g.
  Proof.
    move=> Def Def' Eqt. apply eqtype_unfold; [done|]. iIntros "L".
    iDestruct (Eqt with "L") as "#Eqt". iIntros "!> #E".
    iDestruct ("Eqt" with "E") as "($ & $ & #EqOwn & $ & $)". iFrame "EqOwn".
    iIntros "!>" (κ x d g' tid). rewrite Def Def' /default_shr. iSplit.
    - iIntros "Shr". iDestruct "Shr" as (d0 g0) "[% Guard]". iExists d0, g0.
      iSplit; [done|]. iApply (guards_transitive_left with "Guard"). leaf_by_sep.
      iIntros "Own". iDestruct ("EqOwn" with "Own") as "$". iIntros "Own".
      by iApply "EqOwn".
    - iIntros "Shr". iDestruct "Shr" as (d0 g0) "[% Guard]". iExists d0, g0.
      iSplit; [done|]. iApply (guards_transitive_left with "Guard"). leaf_by_sep.
      iIntros "Own". iDestruct ("EqOwn" with "Own") as "$". iIntros "Own".
      by iApply "EqOwn".
  Qed.

  Lemma eqtype_id_unfold {𝔄} E L (ty ty': type 𝔄) :
    (llctx_interp L -∗ □ (elctx_interp E -∗
      ⌜ty.(ty_size) = ty'.(ty_size)⌝ ∗ ty_lft ty ≡ₗ ty_lft ty' ∗
      (□ ∀vπ d g tid, ty.(ty_gho_own) vπ d g tid ↔ ty'.(ty_gho_own) vπ d g tid) ∗
      (□ ∀vπ d g tid, ty.(ty_gho_pers) vπ d g tid ↔ ty'.(ty_gho_pers) vπ d g tid) ∗
      ⌜∀vπ tid, ty.(ty_phys) vπ tid = ty'.(ty_phys) vπ tid⌝ ∗
      (□ ∀κ vπ d g tid, ty.(ty_shr) κ vπ d g tid ↔ ty'.(ty_shr) κ vπ d g tid))) ↔
    eqtype E L ty ty' idₛ idₛ.
  Proof. split.
    + intros X. apply eqtype_unfold.
        - done.
        - iIntros "L". iDestruct (X with "L") as "#Q".
          iModIntro. iIntros "E". iDestruct ("Q" with "E") as "[B [C [D [E F]]]]".
          iFrame.
    + intros X. rewrite <- eqtype_unfold in X. apply X. done.
  Qed.

  Global Instance type_incl_ne {𝔄 𝔅} n :
    Proper (dist n ==> dist n ==> (=) ==> dist n) (type_incl (𝔄:=𝔄) (𝔅:=𝔅)).
  Proof.
    rewrite /type_incl.
    move=> ??[->->_ EqvOwn EqvOwnPers EqvPhys EqvShr]??[->->_ EqvOwn' EqvOwnPers' EqvPhys' EqvShr']??->.
    do 4 f_equiv.
      + do 8 f_equiv. by rewrite EqvOwn EqvOwn'.
      + do 9 f_equiv. by rewrite EqvOwnPers EqvOwnPers'.
      + f_equiv.
        * f_equiv. setoid_rewrite EqvPhys. setoid_rewrite EqvPhys'. trivial.
        * do 11 f_equiv. by rewrite EqvShr EqvShr'.
  Qed.

  Global Instance type_incl_persistent {𝔄 𝔅} (ty : type 𝔄) (ty' : type 𝔅) f :
    Persistent (type_incl ty ty' f) := _.

  (** For types with the default sharing predicate, the inclusion of the sharing
      predicates follows from that of the ownership predicates. *)
  Lemma type_incl_default {𝔄 𝔅} (ty : type 𝔄) (ty' : type 𝔅) f :
    ty_shr_is_default ty → ty_shr_is_default ty' →
    (⌜ty.(ty_size) = ty'.(ty_size)⌝ ∗ (ty_lft ty' ⊑ ty_lft ty) ∗
      (□ ∀x d g tid, ty.(ty_gho_own) x d g tid -∗ ty'.(ty_gho_own) (f ~~$ₛ x) d g tid
                    ∗ (ty'.(ty_gho_own) (f ~~$ₛ x) d g tid -∗ ty.(ty_gho_own) x d g tid)) ∗
      (□ ∀x d g tid, ty.(ty_gho_pers) x d g tid -∗ ty'.(ty_gho_pers) (f ~~$ₛ x) d g tid) ∗
      ⌜∀x tid, ty.(ty_phys) x tid = ty'.(ty_phys) (f ~~$ₛ x) tid⌝) -∗
    type_incl ty ty' f.
  Proof.
    iIntros (Def Def') "($ & $ & #InOwn & $ & $)". iSplit; [done|].
    iIntros "!>" (κ x d g tid). rewrite !Def Def'.
    iDestruct (default_shr_incl with "InOwn") as "#InShr". iApply "InShr".
  Qed.

  Lemma type_incl_shr_default {𝔄 𝔅} (ty : type 𝔄) (ty' : type 𝔅) f :
    ty_shr_is_default ty → ty_shr_is_default ty' →
    □ (∀x d g tid, ty.(ty_gho_own) x d g tid -∗ ty'.(ty_gho_own) (f ~~$ₛ x) d g tid
                    ∗ (ty'.(ty_gho_own) (f ~~$ₛ x) d g tid -∗ ty.(ty_gho_own) x d g tid)) -∗
    □ (∀κ x d g tid, ty.(ty_shr) κ x d g tid -∗ ty'.(ty_shr) κ (f ~~$ₛ x) d g tid).
  Proof.
    iIntros (Def Def') "#In". setoid_rewrite Def. setoid_rewrite Def'.
    by iApply default_shr_incl.
  Qed.

  Lemma type_incl_refl {𝔄} (ty: type 𝔄) : ⊢ type_incl ty ty idₛ.
  Proof.
    iIntros. 
    iSplit; [done|]. iSplit; [by iApply lft_incl_refl|].
      iSplit. { iModIntro. iIntros. iFrame. iIntros. done. }
      iSplit. { iModIntro. iIntros. iIntros. iFrame "#". }
      iSplit; [done|]. iModIntro. iIntros. iFrame "#".
  Qed.

  Lemma type_incl_trans {𝔄 𝔅 ℭ} f g (ty : type 𝔄) (ty' : type 𝔅) (ty'' : type ℭ) :
    type_incl ty ty' f -∗ type_incl ty' ty'' g -∗ type_incl ty ty'' (g ∘ₛ f).
  Proof.
    iIntros "A B".
    iDestruct "A" as "[%Sz[#InLft [#InOwn [#InOwnPers [%Phys #InShr]]]]]".
    iDestruct "B" as "[%Sz'[#InLft' [#InOwn' [#InOwnPers' [%Phys' #InShr']]]]]".
    iSplit; [|iSplit; [|iSplit; [|iSplit; [|iSplit]]]].
    - iPureIntro. by etrans.
    - iApply llftl_incl_trans; [iApply "InLft'"|iApply "InLft"].
    - iIntros "!>*". iIntros "x".
      iDestruct ("InOwn" with "x") as "[y yx]".
      iDestruct ("InOwn'" with "y") as "[z zy]".
      iFrame "z". iIntros. iApply "yx". iApply "zy". done.
    - iModIntro. iIntros (x d g0 tid) "x".
        iDestruct ("InOwnPers" with "x") as "x".
        iDestruct ("InOwnPers'" with "x") as "x".
        iFrame "x".
    - iPureIntro. intros. etrans. { apply Phys. } { apply Phys'. } 
    - iModIntro. iIntros (κ x d g0 tid) "x".
        iDestruct ("InShr" with "x") as "x".
        iDestruct ("InShr'" with "x") as "x".
        iFrame "x".
  Qed.

  Lemma equiv_subtype {𝔄} (ty ty': type 𝔄) E L : ty ≡ ty' → subtype E L ty ty' idₛ.
  Proof.
    move=> Eqv. iIntros "_!>_".
    iSplit. { iPureIntro. apply Eqv. }
    iSplit. { rewrite Eqv. iApply lft_incl_refl. }
    iSplit. { iIntros "!>*"; rewrite Eqv; iIntros "$". iIntros "x". done. }
    iSplit. { iIntros "!>*"; rewrite Eqv. iIntros. iFrame "#". }
    iSplit. { iPureIntro. intros. rewrite Eqv. trivial. }
    { iIntros "!>*"; rewrite Eqv. iIntros. iFrame "#". }
  Qed.

  Lemma equiv_eqtype {𝔄} (ty ty': type 𝔄) E L : ty ≡ ty' → eqtype E L ty ty' idₛ idₛ.
  Proof. by split; apply equiv_subtype. Qed.

  Lemma subtype_refl {E L 𝔄} (ty: type 𝔄) : subtype E L ty ty idₛ.
  Proof. by apply equiv_subtype. Qed.

  Lemma eqtype_refl {E L 𝔄} (ty: type 𝔄) : eqtype E L ty ty idₛ idₛ.
  Proof. split; apply subtype_refl. Qed.

  Lemma eqtype_symm {𝔄 𝔅} f g (ty: type 𝔄) (ty': type 𝔅) E L :
    eqtype E L ty ty' f g → eqtype E L ty' ty g f.
  Proof. move=> [??]. by split. Qed.

  Lemma subtype_trans {𝔄 𝔅 ℭ} ty ty' ty'' (f: 𝔄 →ₛ 𝔅) (g: 𝔅 →ₛ ℭ) E L :
    subtype E L ty ty' f → subtype E L ty' ty'' g → subtype E L ty ty'' (g ∘ₛ f).
  Proof.
    move=> Sub Sub'. iIntros "L". iDestruct (Sub with "L") as "#Incl".
    iDestruct (Sub' with "L") as "#Incl'". iIntros "!> #E".
    iApply type_incl_trans; by [iApply "Incl"|iApply "Incl'"].
  Qed.

  Lemma eqtype_trans {𝔄 𝔅 ℭ} ty ty' ty'' (f: 𝔄 →ₛ 𝔅) f' (g: 𝔅 →ₛ ℭ) g' E L :
    eqtype E L ty ty' f f' → eqtype E L ty' ty'' g g' →
    eqtype E L ty ty'' (g ∘ₛ f) (f' ∘ₛ g').
  Proof.
    move=> [Sub1 Sub1'] [??]. split; eapply subtype_trans;
    [apply Sub1| | |apply Sub1']; done.
  Qed.

  Lemma subtype_weaken {𝔄 𝔅} f (ty: type 𝔄) (ty': type 𝔅) E E' L L' :
    E ⊆+ E' → L ⊆+ L' → subtype E L ty ty' f → subtype E' L' ty ty' f.
  Proof.
    move=> ?? Sub. iIntros "L".
    iDestruct (Sub with "[L]") as "#Incl"; [by iApply big_sepL_submseteq|].
    iIntros "!> #E". iApply "Incl". by iApply big_sepL_submseteq.
  Qed.

  Lemma subtype_eq {𝔄 𝔅} f g (ty: type 𝔄) (ty': type 𝔅) E L :
    subtype E L ty ty' f → f = g → subtype E L ty ty' g.
  Proof. by move=> ? <-. Qed.

  Lemma eqtype_eq {𝔄 𝔅} f f' g g' (ty: type 𝔄) (ty': type 𝔅) E L :
    eqtype E L ty ty' f g → f = f' → g = g' → eqtype E L ty ty' f' g'.
  Proof. by move=> ? <-<-. Qed.

  Global Instance subtype_proper {𝔄 𝔅} E L :
    Proper (eqtype_id E L ==> eqtype_id E L ==> (=@{𝔄 →ₛ 𝔅}) ==> (↔)) (subtype E L).
  Proof.
    move=> ??[Sub1 Sub1']??[Sub2 Sub2']??->. split; move=> ?;
    eapply (subtype_trans _ _ _ idₛ _); [by apply Sub1'| |by apply Sub1|];
    eapply (subtype_trans _ _ _ _ idₛ); [|by apply Sub2| |by apply Sub2']; done.
  Qed.

  (** List *)

  Lemma subtypel_nil E L : subtypel E L +[] +[] -[].
  Proof. constructor. Qed.

  Lemma eqtypel_nil E L : eqtypel E L +[] +[] -[] -[].
  Proof. constructor. Qed.

  Lemma subtypel_cons {𝔄 𝔅 𝔄l 𝔅l} f fl (ty: type 𝔄) (ty': type 𝔅)
        (tyl : typel 𝔄l) (tyl' : typel 𝔅l) E L :
    subtype E L ty ty' f → subtypel E L tyl tyl' fl →
    subtypel E L (ty +:: tyl) (ty' +:: tyl') (f -:: fl).
  Proof. by constructor. Qed.

  Lemma eqtypel_cons {𝔄 𝔅 𝔄l 𝔅l} f g fl gl
        (ty: type 𝔄) (ty': type 𝔅) (tyl: typel 𝔄l) (tyl': typel 𝔅l) E L :
    eqtype E L ty ty' f g → eqtypel E L tyl tyl' fl gl →
    eqtypel E L (ty +:: tyl) (ty' +:: tyl') (f -:: fl) (g -:: gl).
  Proof. by constructor. Qed.

  Lemma eqtypel_subtypel {𝔄l 𝔅l} fl gl (tyl: typel 𝔄l) (tyl': typel 𝔅l) E L :
    eqtypel E L tyl tyl' fl gl →
    subtypel E L tyl tyl' fl ∧ subtypel E L tyl' tyl gl.
  Proof.
    elim; [split; by constructor|]=>/= > [??] _ [??]; split; by constructor.
  Qed.

  Lemma subtypel_llctx_lookup {𝔄l 𝔅l} (tyl: typel 𝔄l) (tyl': typel 𝔅l) fl E L :
    subtypel E L tyl tyl' fl →
    llctx_interp L -∗ □ (elctx_interp E -∗ ∀i,
      type_incl (tyl +!! i) (tyl' +!! fin_renew_by_plist2 fl i) (fl -2!! i)).
  Proof.
    elim=> [|>Sub _ IH]. { iIntros "_!>_" (i). inv_fin i. }
    iIntros "L". iDestruct (Sub with "L") as "#Sub".
    iDestruct (IH with "L") as "#IH". iIntros "!> #E" (i).
    iSpecialize ("Sub" with "E"). iSpecialize ("IH" with "E"). by inv_fin i.
  Qed.

  (** Simple Type *)

  Lemma type_incl_simple_type {𝔄 𝔅} (f : 𝔄 →ₛ 𝔅) (st: simple_type 𝔄) (st': simple_type 𝔅):
    st.(st_size) = st'.(st_size) → ty_lft st' ⊑ ty_lft st -∗
    (□ ∀x d g tid, st.(st_gho) x d g tid -∗ st'.(st_gho) (f ~~$ₛ x) d g tid) -∗
    ⌜∀x tid, st.(st_phys) x tid = st'.(st_phys) (f ~~$ₛ x) tid⌝ -∗
    type_incl st st' f.
  Proof.
    move=> ?. iIntros "#InLft #InOwn #Phys".
    iAssert (□ ∀x d g tid, st.(st_gho) x d g tid -∗ st'.(st_gho) (f ~~$ₛ x) d g tid
      ∗ (st'.(st_gho) (f ~~$ₛ x) d g tid -∗ st.(st_gho) x d g tid))%I as "#InOwn'".
    { iModIntro. iIntros (x d g tid) "#Gho".
      iSplit.
        { iApply "InOwn". done. }
        { iIntros. iApply "Gho". } }
    iSplit; [done|].
    iSplit; [done|].
    iSplit; [done|]. iSplit; [done|]. iSplit; [done|].
    by iApply type_incl_shr_default.
  Qed.

  Lemma subtype_simple_type {𝔄 𝔅} E L (f : 𝔄 →ₛ 𝔅) (st: simple_type 𝔄) (st': simple_type 𝔅) :
    (llctx_interp L -∗ □ (elctx_interp E -∗
      ⌜st.(st_size) = st'.(st_size)⌝ ∗ ty_lft st' ⊑ ty_lft st ∗
      (□ ∀x d g tid, st.(st_gho) x d g tid -∗ st'.(st_gho) (f ~~$ₛ x) d g tid) ∗
      ⌜∀x tid, st.(st_phys) x tid = st'.(st_phys) (f ~~$ₛ x) tid⌝)) →
    subtype E L st st' f.
  Proof.
    move=> Sub. iIntros "L". iDestruct (Sub with "L") as "#Incl".
    iIntros "!> #E". iDestruct ("Incl" with "E") as (?) "[?[??]]".
    by iApply type_incl_simple_type.
  Qed.

  (** Plain Type *)
  
  Lemma type_incl_plain_type {𝔄 𝔅} (f : 𝔄 →ₛ 𝔅) (pt: plain_type 𝔄) (pt': plain_type 𝔅):
    pt.(pt_size) = pt'.(pt_size) → ty_lft pt' ⊑ ty_lft pt -∗
    □ (∀v tid, pt.(pt_gho) v tid -∗ pt'.(pt_gho) (f ~~$ₛ v) tid
            ∗ (pt'.(pt_gho) (f ~~$ₛ v) tid -∗ pt.(pt_gho) v tid)
    ) -∗
    ⌜∀v tid, pt.(pt_phys) v tid = pt'.(pt_phys) (f ~~$ₛ v) tid⌝ -∗
    type_incl pt pt' f.
  Proof.
    move=> ?. iIntros "#InLft #InOwn %Phys".
    iSplit. { iPureIntro. trivial. }
    do 1 (iSplit; [done|]).
      iSplit; [|iSplit; [|iSplit]].
    - iIntros "!>*/=". iIntros "gho".
      iDestruct ("InOwn" with "gho") as "[x y]". iFrame.
    - iModIntro. iIntros (x d g tid) "x". iDestruct ("InOwn" with "x") as "[x _]". iFrame "x".
    - intros. iPureIntro. intros. apply Phys.
    - iApply type_incl_shr_default; [done|done|]. iIntros "!>*/=". iApply "InOwn".
  Qed.

  Lemma subtype_plain_type {𝔄 𝔅} E L (f : 𝔄 →ₛ 𝔅) (pt: plain_type 𝔄) (pt': plain_type 𝔅) :
    (llctx_interp L -∗ □ (elctx_interp E -∗
      ⌜pt.(pt_size) = pt'.(pt_size)⌝ ∗ ty_lft pt' ⊑ ty_lft pt ∗
      (∀v tid, pt.(pt_gho) v tid -∗ pt'.(pt_gho) (f ~~$ₛ v) tid
          ∗ (pt'.(pt_gho) (f ~~$ₛ v) tid -∗ pt.(pt_gho) v tid)
      ) ∗
      ⌜∀v tid, pt.(pt_phys) v tid = pt'.(pt_phys) (f ~~$ₛ v) tid⌝
      )) →
    subtype E L pt pt' f.
  Proof.
    move=> Sub. iIntros "L". iDestruct (Sub with "L") as "#Sub".
    iIntros "!> #E". iDestruct ("Sub" with "E") as (?) "[?[??]]".
    iApply type_incl_plain_type; trivial.
  Qed.

  (** Ghost Type *)

  Lemma type_incl_ghost_type {𝔄 𝔅} (f : 𝔄 →ₛ 𝔅) (gt: ghost_type 𝔄) (gt': ghost_type 𝔅):
    □ (∀v tid, gt.(gt_gho) v tid -∗ gt'.(gt_gho) (f ~~$ₛ v) tid
            ∗ (gt'.(gt_gho) (f ~~$ₛ v) tid -∗ gt.(gt_gho) v tid)) -∗
    type_incl gt gt' f.
  Proof.
    iIntros "#InOwn".
    iSplit. { iPureIntro. trivial. }
    do 1 (iSplit; try done).
    { simpl. by iApply lft_incl_static. }
    iAssert (□ ∀x d g tid, ty_gho_own gt x d g tid -∗ ty_gho_own gt' (f ~~$ₛ x) d g tid
      ∗ (ty_gho_own gt' (f ~~$ₛ x) d g tid -∗ ty_gho_own gt x d g tid))%I as "#InOwn'".
    { rewrite /ty_gho_own /ty_of_gt //=.
      iIntros "!> % % % % H".
      iDestruct ("InOwn" with "H") as "[H H']".
      iFrame. }
    iSplit; [done|]. iSplit; [done|]. iSplit; [done|].
    by iApply type_incl_shr_default.
  Qed.

  Lemma subtype_ghost_type {𝔄 𝔅} E L (f : 𝔄 →ₛ 𝔅) (gt: ghost_type 𝔄) (gt': ghost_type 𝔅) :
    (llctx_interp L -∗ □ (elctx_interp E -∗
    □ (∀v tid, gt.(gt_gho) v tid -∗ gt'.(gt_gho) (f ~~$ₛ v) tid ∗ (gt'.(gt_gho) (f ~~$ₛ v) tid -∗ gt.(gt_gho) v tid)))) →
    subtype E L gt gt' f.
  Proof.
    move=> Sub. iIntros "L". iDestruct (Sub with "L") as "#Incl".
    iIntros "!> #E". iDestruct ("Incl" with "E") as "#H".
    by iApply type_incl_ghost_type.
  Qed.

  (** resolve *)

  Lemma resolve_subtype {𝔄 𝔅} E L (ty: type 𝔄) (ty': type 𝔅) f Φ :
    subtype E L ty ty' f → resolve E L ty' Φ → resolve E L ty (Φ ∘ ~~!ₛ f).
  Proof.
    iIntros (Sub Rslv) "* LFT PROPH UNIQ TIME E #L G ty".
    leaf_open "L" with "G" as "[L1 back]". { solve_ndisj. }
    iDestruct (Sub with "L1") as "#Sub".
    iMod ("back" with "L1") as "G".
    iDestruct ("Sub" with "E") as "#(_ & _ & #InOwn & _)".
    iDestruct ("InOwn" with "ty") as "[ty' _]".
    unfold "∘".
    by iApply (Rslv with "LFT PROPH UNIQ TIME E L G ty'").
  Qed.
End subtyping.

(** * Utility *)

Section type_util.
  Context `{!typeG Σ}.

  Definition by_succ (d: nat) (Φ: nat → iProp Σ) : iProp Σ :=
    match d with S d' => Φ d' | _ => False end.
  Lemma by_succ_ex d Φ : by_succ d Φ ⊣⊢ ∃d', ⌜d = S d'⌝ ∗ Φ d'.
  Proof.
    iSplit; [|by iIntros "[%[->$]]"]. iIntros. case d; [done|]=> d'.
    iExists d'. by iFrame.
  Qed.
  Global Instance by_succ_proper :
    Proper ((=) ==> pointwise_relation _ (⊣⊢) ==> (⊣⊢)) by_succ.
  Proof. move=> ??->?? Eq. rewrite !by_succ_ex. by setoid_rewrite Eq. Qed.
  Global Instance by_succ_ne n :
    Proper ((=) ==> pointwise_relation _ (dist n) ==> dist n) by_succ.
  Proof. move=> ??->?? Eq. rewrite !by_succ_ex. by setoid_rewrite Eq. Qed.
  Global Instance by_succ_mono :
    Proper ((=) ==> pointwise_relation _ (⊢) ==> (⊢)) by_succ.
  Proof. move=> ??->?? In. rewrite !by_succ_ex. by setoid_rewrite In. Qed.
  Global Instance by_succ_persistent d Φ :
    (∀d', Persistent (Φ d')) → Persistent (by_succ d Φ).
  Proof. case d; apply _. Qed.

  Definition by_just_loc (vl: list val) (Φ: loc → iProp Σ) : iProp Σ :=
    match vl with [ #(LitLoc l)] => Φ l | _ => False end.
  Lemma by_just_loc_ex vl Φ : by_just_loc vl Φ ⊣⊢ ∃l: loc, ⌜vl = [ #l]⌝ ∗ Φ l.
  Proof.
    iSplit; [|by iIntros "[%[->$]]"]. iIntros. case vl=> [|[[|l|?]|?][|??]]//.
    iExists l. by iFrame.
  Qed.
  Global Instance by_just_loc_proper :
    Proper ((=) ==> pointwise_relation _ (⊣⊢) ==> (⊣⊢)) by_just_loc.
  Proof. move=> ??->?? Eq. rewrite !by_just_loc_ex. by setoid_rewrite Eq. Qed.
  Global Instance by_just_loc_ne n :
    Proper ((=) ==> pointwise_relation _ (dist n) ==> dist n) by_just_loc.
  Proof. move=> ??->?? Eq. rewrite !by_just_loc_ex. by setoid_rewrite Eq. Qed.
  Global Instance by_just_loc_mono :
    Proper ((=) ==> pointwise_relation _ (⊢) ==> (⊢)) by_just_loc.
  Proof. move=> ??->?? In. rewrite !by_just_loc_ex. by setoid_rewrite In. Qed.
  Global Instance by_just_loc_persistent vl Φ :
    (∀l, Persistent (Φ l)) → Persistent (by_just_loc vl Φ).
  Proof. rewrite by_just_loc_ex. apply _. Qed.
End type_util.

Notation "[S( d' ) := d ] P" := (by_succ d (λ d', P)) (at level 200,
  right associativity, format "[S( d' )  :=  d ]  P") : bi_scope.

Notation "[loc[ l ] := vl ] P" := (by_just_loc vl (λ l, P)) (at level 200,
  right associativity, format "[loc[ l ]  :=  vl ]  P") : bi_scope.

Section type_util.
  Context `{!typeG Σ}.

  (* Splitting for a standard pointer *)
  Lemma split_mt_ptr d Φ l' :
    (l' ↦∗: λ vl, [S(d') := d] [loc[l] := vl] Φ d' l) ⊣⊢
    [S(d') := d] ∃l: loc, l' ↦ #l ∗ Φ d' l.
  Proof.
    iSplit.
    - iIntros "(%vl & ↦ &?)". case d as [|]=>//. case vl as [|[[]|][]]=>//.
      rewrite heap_mapsto_vec_singleton. iExists _. iFrame.
    - iIntros "big". case d as [|]=>//. iDestruct "big" as (?) "[??]".
      iExists [_]. rewrite heap_mapsto_vec_singleton. by iFrame.
  Qed.

  Lemma split_mt_ptr' Φ l' :
    (l' ↦∗: λ vl, [loc[l] := vl] Φ l) ⊣⊢ ∃l: loc, l' ↦ #l ∗ Φ l.
  Proof.
    set Φ' := λ _: nat, Φ. have ->: Φ = Φ' 0%nat by done.
    by apply (split_mt_ptr (S _)).
  Qed.

  (*Lemma heap_mapsto_ty_own {𝔄} l (ty: type 𝔄) vπ d tid :
    l ↦∗: ty.(ty_own) vπ d tid ⊣⊢
    ∃vl: vec val ty.(ty_size), l ↦∗ vl ∗ ty.(ty_own) vπ d tid vl.
  Proof.
    iSplit; iIntros "[%vl[? ty]]"; [|iExists vl; by iFrame].
    iDestruct (ty_size_eq with "ty") as %<-. iExists (list_to_vec vl).
    rewrite vec_to_list_to_vec. iFrame.
  Qed.*)

  Definition freeable_sz' (sz: nat) (l: loc) : iProp Σ :=
    †{1}l…sz ∨ ⌜Z.of_nat sz = 0%Z⌝.
End type_util.

Global Hint Resolve ty_outlives_E_elctx_sat tyl_outlives_E_elctx_sat : lrust_typing.
Global Hint Resolve resolve'_post | 5 : lrust_typing.
Global Hint Resolve resolvel_nil resolve'_just
  subtype_refl eqtype_refl subtypel_nil eqtypel_nil : lrust_typing.
(* We use [Hint Extern] instead of [Hint Resolve] here, because
  [resolvel_cons], [subtypel_cons] and [eqtypel_cons]
  work with [apply] but not with [simple apply] *)
Global Hint Extern 0 (resolvel _ _ _ _) => apply resolvel_cons : lrust_typing.
Global Hint Extern 0 (subtypel _ _ _ _ _) => apply subtypel_cons : lrust_typing.
Global Hint Extern 0 (eqtypel _ _ _ _ _ _) => apply eqtypel_cons : lrust_typing.

Global Hint Opaque resolve resolve' subtype eqtype : lrust_typing.
