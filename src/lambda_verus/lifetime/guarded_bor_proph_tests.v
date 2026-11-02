From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import invariants ghost_map.
From lrust.prophecy Require Import syn_type prophecy.
From lrust.lifetime Require Import lifetime_full guarded_bor guarded_bor_proph.
From lrust.typing Require Import uniq_cmra.
From lrust.util Require Import proph_bor.
From guarding Require Import guard.
From guarding.lib Require Import fractional.
From iris.prelude Require Import options.
Local Unset Default Proof Using.
Local Unset Suggest Proof Using.

(** Tests of the prophetic lends of guarded mutable borrows ([guarded_bor_proph.v]), on the
    toy instance of [guarded_bor_tests.v]: [c s t := s ↪ t] in a ghost map (here with
    contents in [positive], a type of prophecy values). The tests hold the authority of
    the ghost map, so they can observe the contents.

    The permission is lent through a generalized prophetic borrow, as the typing layer
    does for [&uniq]; in [test_proph_map_write_resolve_end_move] its prophecy variable
    ranges over pairs [(g, t)] and the contents' over [t], the shape of
    [PCell::borrow_mut] (the permission's value [(g, x)] mapped to the contents' value
    [x]). *)

Section GmbProphTests.
  Context `{!invGS Σ, !prophG Σ, !uniqG Σ, !llft_logicGS Σ, !frac_logicG Σ}.
  Context `{!gmbG Σ nat positive}.
  Context `{!ghost_mapG Σ nat positive}.
  Context (γm : gname).

  Local Definition cc (s : nat) (t : positive) : iProp Σ := s ↪[γm] t.
  Local Instance cc_timeless s t : Timeless (cc s t).
  Proof. apply _. Qed.

  Local Definition posi : syn_typei := exist _ positiveₛ I.
  Local Definition pairi : syn_typei := exist _ (positiveₛ * positiveₛ)%ST I.

  Local Definition E0 : coPset := ↑Nllft ∪ ↑prophN ∪ ↑uniqN ∪ ↑gmbN.

  (* a share of an owned (timeless) resource at [κ], as the typing layer makes it *)
  Local Lemma share_timeless E κ (P : iProp Σ) :
    Timeless P → ↑Nllft ⊆ E →
    P ={E}=∗ (@[κ] &&{↑NllftG}&&> P) ∗ ([†κ] ={E}=∗ ▷ P).
  Proof.
    iIntros (??) "P". iMod (llftl_borrow_shared with "[P]") as "[#G $]"; [done|by iNext|].
    iModIntro. by iApply guards_remove_later_rhs.
  Qed.

  (* Resolving a borrow of the contents at a constant (prophecy-free) value [t], dropping
     its payload. *)
  Local Lemma resolve_cont κ ζi idx s (t: positive) :
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ @[κ] -∗ proph_bor_tok (PrVar posi ζi) t idx -∗
    proph_idx_bor_gen κ (PrVar posi ζi) idx (λ y _, cc s y) ={E0}=∗
      ⟨π, π (PrVar posi ζi) = t⟩ ∗ @[κ].
  Proof.
    iIntros "#LFT #PROPH #UNIQ Alive Tok #IBor".
    iMod (proph_idx_bor_gen_resolve_share E0 κ (PrVar posi ζi) t idx (λ y _, cc s y) (cc s t)
            [] True%I (@[κ]) 0 with "LFT PROPH UNIQ [] [] [] Alive Tok IBor")
      as "($ & $ & _)".
    - rewrite /E0. solve_ndisj.
    - by intros ?? _.
    - iApply guards_refl.
    - iIntros (?) "C !>". iFrame "C". by iIntros "!> $".
    - iIntros (H ?) "_ $ _". iMod lc_zero as "$". iModIntro.
      iIntros (ζ0 Hin). by apply elem_of_nil in Hin.
    - done.
  Qed.

  (** The payloads: the permission at value [(g, t)] (or [t]), the contents at [t]. *)
  Local Definition perm_pl γ ξi : pv_val (PrVar pairi ξi) → pv_proph (PrVar pairi ξi) → iProp Σ :=
    λ x _, gmb_b γ x.2.
  Local Definition perm_pl1 γ ξi : pv_val (PrVar posi ξi) → pv_proph (PrVar posi ξi) → iProp Σ :=
    λ x _, gmb_b γ x.
  Local Definition cont_pl s ζi : pv_val (PrVar posi ζi) → pv_proph (PrVar posi ζi) → iProp Σ :=
    λ y _, cc s y.

  (** (L3p) with a value map, (L4): the owner shares [gmb_a] at [κ]; the permission holder
      has a prophetic borrow at [κ] of [gmb_b] at value [(g0, t)] (prophecy variable [ξ]),
      and lends it prophetically: a fresh borrow of the contents at value [t] (prophecy
      variable [ζ]), [ξ] being pre-resolved to [(g0, ζ)]. Write [t'] through the new
      borrow, resolve it ([ζ] to [t'], hence [ξ] to [(g0, t')]), end [κ]. The lender's
      inheritance gives back [gmb_b] at the final value [t'] (observed with (L2)); the owner
      then moves. *)
  Lemma test_proph_map_write_resolve_end_move m s (g0 t t' : positive) :
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ ghost_map_auth γm 1 m -∗ cc s t -∗ £ 1 -∗
    |={E0}=> |={↑Nllft}[∅]▷=> |={E0}=> ∃ m' γ ξi,
      ghost_map_auth γm 1 m' ∗ ⌜m' !! s = Some t'⌝ ∗
      gmb_inv cc γ ∗ gmb_a γ s ∗ gmb_b γ t' ∗
      ⟨π, π (PrVar pairi ξi) = ((g0, t') : positive * positive)⟩.
  Proof.
    iIntros "#LFT #PROPH #UNIQ Auth C Lc".
    have ? : ↑Nllft ⊆ E0 by rewrite /E0; solve_ndisj.
    iMod (gmb_create cc _ 0 with "C") as (γ) "([%Hd %Hb] & #Inv & A & B)".
    iMod (llftl_begin with "LFT") as (κ) "[Alive #End]"; first done.
    (* the owner shares [gmb_a] *)
    iMod (share_timeless with "A") as "[#Ga InhA]"; [done|].
    (* the lender's prophetic borrow of the permission *)
    iMod (proph_loan_intro pairi E0 ((g0, t) : positive * positive) with "PROPH UNIQ")
      as (ξi) "Loan"; first (rewrite /E0; solve_ndisj).
    iMod (proph_loan_borrow_gen E0 κ (PrVar pairi ξi) (g0, t) (vπ (𝔄:=(positiveₛ * positiveₛ)%ST) (g0, t))
            (perm_pl γ ξi) with "LFT PROPH UNIQ Loan [B]") as (idx) "(Tok & #IBor & Inh)";
      [done|by iNext|].
    (* (L3p) *)
    iMod (proph_loan_intro posi E0 t with "PROPH UNIQ") as (ζi) "Loanζ";
      first (rewrite /E0; solve_ndisj).
    iMod lc_zero as "Lc0".
    iMod (gmb_lend_proph_map cc E0 κ (PrVar pairi ξi) (g0, t) idx (perm_pl γ ξi)
            (PrVar posi ζi) t (cont_pl s ζi) (λ y, (g0, y)) (@[κ]) γ s 0
            with "LFT PROPH UNIQ Inv Ga Lc0 [] [] Alive Loanζ Tok IBor")
      as "(#Obs & (%idx' & Tokζ & #IBorζ) & Alive)"; [rewrite /E0; solve_ndisj|lia| | |].
    { iApply guards_refl. }
    { iIntros (G' wπ ?) "_ $ >B". iModIntro. iExists t. iFrame "B". iIntros "C".
      iModIntro. iExists (vπ (𝔄:=positiveₛ) t). iSplitL "C"; [by iNext|].
      iIntros (y' wζ') "_ C". iModIntro. iExists y'. iFrame "C". iIntros "B !>".
      by iExists (g0, y'). }
    (* write [t'] through the new borrow *)
    iMod (proph_idx_bor_gen_acc_idx E0 κ (PrVar posi ζi) t idx' (cont_pl s ζi) (@[κ])
            with "LFT UNIQ [] Tokζ IBorζ Alive") as (wπ) "[>C Close]"; [done| |].
    { iApply guards_refl. }
    iMod (ghost_map_update t' with "Auth C") as "[Auth C]".
    iMod (fupd_mask_subseteq (↑Nllft)) as "Upd"; first done.
    iMod ("Close" $! t' (vπ (𝔄:=positiveₛ) t') with "[C]") as "[Tokζ Alive]"; first by iNext.
    iMod "Upd" as "_".
    (* resolve the new borrow *)
    iMod (resolve_cont with "LFT PROPH UNIQ Alive Tokζ IBorζ") as "[#Obsζ Alive]".
    (* end [κ] *)
    iModIntro. iMod ("End" with "Alive") as "Dead". iModIntro. iNext. iMod "Dead" as "#Dead".
    iModIntro. iMod ("InhA" with "Dead") as ">A".
    iMod (fupd_mask_mono with "(Inh Dead)") as "Inh"; first done.
    iDestruct "Inh" as (x' wπ') "[_ >B]".
    (* (L4): the permission is at the final value *)
    iDestruct (gmb_share cc (gmb_a γ s ∗ gmb_b γ x'.2) (↑NllftG) 0 with "Inv [] []") as "#Gc".
    { solve_ndisj. } { iApply guards_weaken_sep_l. } { iApply guards_weaken_sep_r. }
    iMod (guards_open with "Gc [$A $B]") as "[C Hcl]"; first (rewrite /E0; solve_ndisj).
    iDestruct (ghost_map_lookup with "Auth C") as %Hs. rewrite lookup_insert in Hs.
    simplify_eq.
    iMod ("Hcl" with "C") as "[A B]".
    (* (L4): the owner moves, without the lender *)
    iMod (gmb_move cc with "Inv [Lc] A") as (t2) "[C Back]"; [rewrite Hb; solve_ndisj|by rewrite Hd|].
    iDestruct (ghost_map_lookup with "Auth C") as %Hs2. rewrite lookup_insert in Hs2.
    simplify_eq.
    iMod ("Back" with "C") as "A".
    iModIntro. iExists _, γ, ξi. iFrame "∗#". rewrite lookup_insert. iSplit; [done|].
    iDestruct (proph_obs_and with "Obs Obsζ") as "O".
    iApply (proph_obs_impl with "O"). intros π [-> ->]. done.
  Qed.

  (** (L4), the owner's side alone, after (L3p): the lender drops its new borrow, its
      observation and its inheritance; after [κ] ends, the owner moves. *)
  Lemma test_proph_lend_abandoned s (g0 t : positive) :
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ cc s t -∗ £ 1 -∗
    |={E0}=> |={↑Nllft}[∅]▷=> |={E0}=> ∃ t', cc s t'.
  Proof.
    iIntros "#LFT #PROPH #UNIQ C Lc".
    have ? : ↑Nllft ⊆ E0 by rewrite /E0; solve_ndisj.
    iMod (gmb_create cc _ 0 with "C") as (γ) "([%Hd %Hb] & #Inv & A & B)".
    iMod (llftl_begin with "LFT") as (κ) "[Alive #End]"; first done.
    iMod (share_timeless with "A") as "[#Ga InhA]"; [done|].
    iMod (proph_loan_intro pairi E0 ((g0, t) : positive * positive) with "PROPH UNIQ")
      as (ξi) "Loan"; first (rewrite /E0; solve_ndisj).
    iMod (proph_loan_borrow_gen E0 κ (PrVar pairi ξi) (g0, t) (vπ (𝔄:=(positiveₛ * positiveₛ)%ST) (g0, t))
            (perm_pl γ ξi) with "LFT PROPH UNIQ Loan [B]") as (idx) "(Tok & #IBor & _)";
      [done|by iNext|].
    iMod (proph_loan_intro posi E0 t with "PROPH UNIQ") as (ζi) "Loanζ";
      first (rewrite /E0; solve_ndisj).
    iMod lc_zero as "Lc0".
    iMod (gmb_lend_proph_map cc E0 κ (PrVar pairi ξi) (g0, t) idx (perm_pl γ ξi)
            (PrVar posi ζi) t (cont_pl s ζi) (λ y, (g0, y)) (@[κ]) γ s 0
            with "LFT PROPH UNIQ Inv Ga Lc0 [] [] Alive Loanζ Tok IBor")
      as "(_ & _ & Alive)"; [rewrite /E0; solve_ndisj|lia| | |].
    { iApply guards_refl. }
    { iIntros (G' wπ ?) "_ $ >B". iModIntro. iExists t. iFrame "B". iIntros "C".
      iModIntro. iExists (vπ (𝔄:=positiveₛ) t). iSplitL "C"; [by iNext|].
      iIntros (y' wζ') "_ C". iModIntro. iExists y'. iFrame "C". iIntros "B !>".
      by iExists (g0, y'). }
    iModIntro. iMod ("End" with "Alive") as "Dead". iModIntro. iNext. iMod "Dead" as "#Dead".
    iModIntro. iMod ("InhA" with "Dead") as ">A".
    iMod (gmb_move cc with "Inv [Lc] A") as (t') "[C _]"; [rewrite Hb; solve_ndisj|by rewrite Hd|].
    iModIntro. by iExists t'.
  Qed.

  (** (L3p) in place, (L4): the lend keeps the prophecy variable [ξ] of the lender's borrow
      (the payload changes from the permission to the contents). Write [t'], resolve [ξ]
      (to [t']), end [κ]; the lender gets back [gmb_b] at [t'], and the owner moves. *)
  Lemma test_proph_inplace_write_resolve_end_move m s (t t' : positive) :
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ ghost_map_auth γm 1 m -∗ cc s t -∗ £ 1 -∗
    |={E0}=> |={↑Nllft}[∅]▷=> |={E0}=> ∃ m' γ ξi,
      ghost_map_auth γm 1 m' ∗ ⌜m' !! s = Some t'⌝ ∗
      gmb_inv cc γ ∗ gmb_a γ s ∗ gmb_b γ t' ∗ ⟨π, π (PrVar posi ξi) = t'⟩.
  Proof.
    iIntros "#LFT #PROPH #UNIQ Auth C Lc".
    have ? : ↑Nllft ⊆ E0 by rewrite /E0; solve_ndisj.
    iMod (gmb_create cc _ 0 with "C") as (γ) "([%Hd %Hb] & #Inv & A & B)".
    iMod (llftl_begin with "LFT") as (κ) "[Alive #End]"; first done.
    iMod (share_timeless with "A") as "[#Ga InhA]"; [done|].
    iMod (proph_loan_intro posi E0 t with "PROPH UNIQ") as (ξi) "Loan";
      first (rewrite /E0; solve_ndisj).
    iMod (proph_loan_borrow_gen E0 κ (PrVar posi ξi) t (vπ (𝔄:=positiveₛ) t)
            (perm_pl1 γ ξi) with "LFT PROPH UNIQ Loan [B]") as (idx) "(Tok & #IBor & Inh)";
      [done|by iNext|].
    (* (L3p), in place *)
    iMod lc_zero as "Lc0".
    iMod (gmb_lend_proph cc E0 κ (PrVar posi ξi) t idx (perm_pl1 γ ξi) (cont_pl s ξi) (@[κ])
            γ s 0 with "LFT UNIQ Inv Ga Lc0 [] [] Alive Tok IBor")
      as (idx') "(Tok & #IBor' & Alive)"; [done|lia| | |].
    { iApply guards_refl. }
    { iIntros (wπ) ">B". iModIntro. iExists t. iFrame "B". iIntros "C". iModIntro.
      iSplitL "C"; [by iNext|].
      iIntros (x2 wπ2) "C". iModIntro. iExists x2. iFrame "C". by iIntros "B !>". }
    (* write [t'] *)
    iMod (proph_idx_bor_gen_acc_idx E0 κ (PrVar posi ξi) t idx' (cont_pl s ξi) (@[κ])
            with "LFT UNIQ [] Tok IBor' Alive") as (wπ) "[>C Close]"; [done| |].
    { iApply guards_refl. }
    iMod (ghost_map_update t' with "Auth C") as "[Auth C]".
    iMod (fupd_mask_subseteq (↑Nllft)) as "Upd"; first done.
    iMod ("Close" $! t' (vπ (𝔄:=positiveₛ) t') with "[C]") as "[Tok Alive]"; first by iNext.
    iMod "Upd" as "_".
    (* resolve [ξ] *)
    iMod (resolve_cont with "LFT PROPH UNIQ Alive Tok IBor'") as "[#Obs Alive]".
    (* end [κ] *)
    iModIntro. iMod ("End" with "Alive") as "Dead". iModIntro. iNext. iMod "Dead" as "#Dead".
    iModIntro. iMod ("InhA" with "Dead") as ">A".
    iMod (fupd_mask_mono with "(Inh Dead)") as "Inh"; first done.
    iDestruct "Inh" as (x' wπ') "[_ >B]".
    iDestruct (gmb_share cc (gmb_a γ s ∗ gmb_b γ x') (↑NllftG) 0 with "Inv [] []") as "#Gc".
    { solve_ndisj. } { iApply guards_weaken_sep_l. } { iApply guards_weaken_sep_r. }
    iMod (guards_open with "Gc [$A $B]") as "[C Hcl]"; first (rewrite /E0; solve_ndisj).
    iDestruct (ghost_map_lookup with "Auth C") as %Hs. rewrite lookup_insert in Hs.
    simplify_eq.
    iMod ("Hcl" with "C") as "[A B]".
    iMod (gmb_move cc with "Inv [Lc] A") as (t2) "[C Back]"; [rewrite Hb; solve_ndisj|by rewrite Hd|].
    iDestruct (ghost_map_lookup with "Auth C") as %Hs2. rewrite lookup_insert in Hs2.
    simplify_eq.
    iMod ("Back" with "C") as "A".
    iModIntro. iExists _, γ, ξi. iFrame "∗#". by rewrite lookup_insert.
  Qed.
End GmbProphTests.
