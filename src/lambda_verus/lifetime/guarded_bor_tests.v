From iris.proofmode Require Import tactics.
From iris.base_logic.lib Require Import invariants ghost_map.
Require Import guarding.guard.
From lrust.lifetime Require Import lifetime_full guarded_bor.
From iris.prelude Require Import options.
Local Unset Default Proof Using.
Local Unset Suggest Proof Using.

(** Tests of the guarded-mutable-borrows library ([guarded_bor.v]), on a toy instance: the
    placement is a key of a ghost map, the contents are a value, and [c s t := s ↪ t]. The
    tests hold the authority of the ghost map, so they can observe the contents. *)

Section GmbTests.
  Context {Σ: gFunctors}.
  Context `{!llft_logicGS Σ}.
  Context `{!invGS Σ}.
  Context `{!gmbG Σ nat nat}.
  Context `{!ghost_mapG Σ nat nat}.
  Context (γm : gname).

  Local Definition cc (s t : nat) : iProp Σ := s ↪[γm] t.
  Local Instance cc_timeless s t : Timeless (cc s t).
  Proof. apply _. Qed.

  (* a share of an owned (timeless) resource at [κ], as the typing layer makes it *)
  Local Lemma share_timeless κ (P : iProp Σ) :
    Timeless P →
    P ={↑Nllft}=∗ (@[κ] &&{↑NllftG}&&> P) ∗ ([†κ] ={↑Nllft}=∗ ▷ P).
  Proof.
    iIntros (?) "P". iMod (llftl_borrow_shared with "[P]") as "[#G $]"; [done|by iNext|].
    iModIntro. by iApply guards_remove_later_rhs.
  Qed.

  (** (L0) Create and destroy. *)
  Lemma test_create_destroy s t :
    cc s t ={↑Nllft}=∗ cc s t.
  Proof.
    iIntros "C". iMod (gmb_create cc _ 0 with "C") as (γ) "([%Hd %Hb] & #Inv & A & B)".
    by iMod (gmb_destroy cc with "Inv A B") as "C".
  Qed.

  (** (L1) A move that changes the placement; then destroy. The mover learns the value of
      the contents only from the contents themselves. *)
  Lemma test_move m s s' t :
    m !! s' = None →
    ghost_map_auth γm 1 m -∗ cc s t ={↑Nllft ∪ ↑gmbN}=∗
      ∃ m', ghost_map_auth γm 1 m' ∗ cc s' t.
  Proof.
    iIntros (Hs') "Auth C".
    iDestruct (ghost_map_lookup with "Auth C") as %Hs.
    iMod (gmb_create cc _ 0 with "C") as (γ) "([%Hd %Hb] & #Inv & A & B)".
    iMod (gmb_move cc with "Inv A") as (t0) "[C Back]"; first (rewrite Hb; solve_ndisj).
    iDestruct (ghost_map_lookup with "Auth C") as %Hs0. rewrite Hs in Hs0. simplify_eq.
    (* re-encode at the new placement *)
    iMod (ghost_map_delete with "Auth C") as "Auth".
    iMod (ghost_map_insert s' t0 with "Auth") as "[Auth C]".
    { rewrite lookup_delete_ne //. intros ->. by rewrite Hs in Hs'. }
    iMod ("Back" with "C") as "A".
    iMod (gmb_destroy cc with "Inv A B") as "C"; first solve_ndisj.
    iModIntro. iExists _. iFrame.
  Qed.

  (** (L2) Shared read: the owner shares the move right and the permission holder shares
      the permission, at the same lifetime; the contents are then readable. *)
  Lemma test_share_read m s t :
    llft_ctx -∗ ghost_map_auth γm 1 m -∗ cc s t ={↑Nllft}=∗
      ⌜m !! s = Some t⌝ ∗ ghost_map_auth γm 1 m.
  Proof.
    iIntros "#LFT Auth C".
    iMod (gmb_create cc _ 0 with "C") as (γ) "([%Hd %Hb] & #Inv & A & B)".
    iMod (llftl_begin with "LFT") as (κ) "[Alive _]"; first done.
    iMod (share_timeless κ with "A") as "[#Ga _]".
    iMod (share_timeless κ with "B") as "[#Gb _]".
    iDestruct (gmb_share cc with "Inv Ga Gb") as "#Gc"; first solve_ndisj.
    iMod (guards_open with "Gc Alive") as "[C Hcl]"; first solve_ndisj.
    iDestruct (ghost_map_lookup with "Auth C") as %Hs.
    iMod ("Hcl" with "C") as "_". by iFrame.
  Qed.

  (** (L3) and (L4): lend the contents for [κ], write through the borrow, and end [κ].
      The permission side gets back [gmb_b] at the final value (observed with (L2), from the
      owned [gmb_a] and [gmb_b]); the owner can then move. *)
  Lemma test_lend_write_end_move m s t t' :
    llft_ctx -∗ ghost_map_auth γm 1 m -∗ cc s t -∗ £ 1 -∗
    |={↑Nllft}=> |={↑Nllft}[∅]▷=> |={↑Nllft ∪ ↑gmbN}=> ∃ m' γ,
      ghost_map_auth γm 1 m' ∗ gmb_inv cc γ ∗ gmb_a γ s ∗ gmb_b γ t' ∗ ⌜m' !! s = Some t'⌝.
  Proof.
    iIntros "#LFT Auth C Lc".
    iMod (gmb_create cc _ 0 with "C") as (γ) "([%Hd %Hb] & #Inv & A & B)".
    iMod (llftl_begin with "LFT") as (κ) "[Alive #End]"; first done.
    (* the owner shares [gmb_a]; the permission holder lends [gmb_b] *)
    iMod (share_timeless κ with "A") as "[#Ga InhA]".
    iMod (llftl_borrow _ κ (∃ t, gmb_b γ t) with "LFT [B]") as "[Bor InhB]"; first done.
    { iNext. by iExists t. }
    (* (L3) *)
    iMod (gmb_lend cc with "LFT Inv Ga [Lc] Bor Alive") as "[Bor Alive]"; [done|by rewrite Hd|].
    (* write through the borrow *)
    iMod (llftl_bor_acc with "LFT Bor Alive") as "[C Close]"; first done.
    iDestruct "C" as ">[%t0 C]".
    iMod (ghost_map_update t' with "Auth C") as "[Auth C]".
    iMod ("Close" $! (∃ t, cc s t)%I with "[C]") as "[Bor Alive]".
    { iSplitR; last by iExists t'. iNext. iIntros "[$ _]". done. }
    (* end [κ] *)
    iModIntro. iMod ("End" with "Alive") as "Dead". iModIntro. iNext. iMod "Dead" as "#Dead".
    iMod ("InhA" with "Dead") as ">A".
    iMod ("InhB" with "Dead") as ">[%t1 B]".
    (* (L4): the permission is at the final value *)
    iDestruct (gmb_share cc (gmb_a γ s ∗ gmb_b γ t1) (↑NllftG) 0 with "Inv [] []") as "#Gc".
    { solve_ndisj. } { iApply guards_weaken_sep_l. } { iApply guards_weaken_sep_r. }
    iMod (guards_open with "Gc [$A $B]") as "[C Hcl]"; first solve_ndisj.
    iDestruct (ghost_map_lookup with "Auth C") as %Hs. rewrite lookup_insert in Hs.
    simplify_eq.
    iMod ("Hcl" with "C") as "[A B]".
    (* (L4): the owner moves, without the lender *)
    iModIntro. iMod (gmb_move cc with "Inv A") as (t2) "[C Back]"; first (rewrite Hb; solve_ndisj).
    iDestruct (ghost_map_lookup with "Auth C") as %Hs2. rewrite lookup_insert in Hs2.
    simplify_eq.
    iMod ("Back" with "C") as "A".
    iModIntro. iExists _, γ. iFrame "∗#". by rewrite lookup_insert.
  Qed.

  (** (L4), the owner's side alone: the lender never touches its borrow or its
      inheritance again; after [κ] ends, the owner moves. *)
  Lemma test_lend_abandoned s t :
    llft_ctx -∗ cc s t -∗ £ 1 -∗
    |={↑Nllft}=> |={↑Nllft}[∅]▷=> |={↑Nllft ∪ ↑gmbN}=> ∃ t', cc s t'.
  Proof.
    iIntros "#LFT C Lc".
    iMod (gmb_create cc _ 0 with "C") as (γ) "([%Hd %Hb] & #Inv & A & B)".
    iMod (llftl_begin with "LFT") as (κ) "[Alive #End]"; first done.
    iMod (share_timeless κ with "A") as "[#Ga InhA]".
    iMod (llftl_borrow _ κ (∃ t, gmb_b γ t) with "LFT [B]") as "[Bor _]"; first done.
    { iNext. by iExists t. }
    iMod (gmb_lend cc with "LFT Inv Ga [Lc] Bor Alive") as "[_ Alive]"; [done|by rewrite Hd|].
    iModIntro. iMod ("End" with "Alive") as "Dead". iModIntro. iNext. iMod "Dead" as "#Dead".
    iMod ("InhA" with "Dead") as ">A".
    iModIntro. iMod (gmb_move cc with "Inv A") as (t') "[C _]"; first (rewrite Hb; solve_ndisj).
    iModIntro. by iExists t'.
  Qed.

  (** (L3) with a share at step-index 1 (an instance of depth 1): the owner's share is a
      frozen full borrow ([llftl_bor_guard]). The lend costs one credit, and prepays two
      for the move. *)
  Lemma test_lend_later s t :
    llft_ctx -∗ cc s t -∗ £ 1 -∗ £ 2 -∗
    |={↑Nllft}=> |={↑Nllft}[∅]▷=> |={↑Nllft ∪ ↑gmbN}=> ∃ t', cc s t'.
  Proof.
    iIntros "#LFT C Lc1 Lc2".
    iMod (gmb_create cc _ 1 with "C") as (γ) "([%Hd %Hb] & #Inv & A & B)".
    iMod (llftl_begin with "LFT") as (κ) "[Alive #End]"; first done.
    iMod (llftl_borrow _ κ (gmb_a γ s) with "LFT [A]") as "[BorA InhA]"; [done|by iNext|].
    iMod (llftl_bor_guard with "LFT BorA") as "#Ga"; first done.
    iMod (llftl_borrow _ κ (∃ t, gmb_b γ t) with "LFT [B]") as "[Bor _]"; first done.
    { iNext. by iExists t. }
    iMod (gmb_lend_later cc _ _ _ _ 1 with "LFT Inv Ga Lc1 [Lc2] Bor Alive") as "[_ Alive]";
      [done|lia|by rewrite Hd|].
    iModIntro. iMod ("End" with "Alive") as "Dead". iModIntro. iNext. iMod "Dead" as "#Dead".
    iMod ("InhA" with "Dead") as ">A".
    iModIntro. iMod (gmb_move cc with "Inv A") as (t') "[C _]"; first (rewrite Hb; solve_ndisj).
    iModIntro. by iExists t'.
  Qed.

  (** The shape of the typing layer: the owner shares [gmb_a] at [α]; two successive mutable
      lends at [α ⊓ β1] and [α ⊓ β2] (through the guarded accessor, holding [@[α] ∗ @[βi]]);
      each lend ends with its [βi]. The owner gets [gmb_a] back only from the inheritance of
      its share, i.e. after [α] has ended, and then every lend lifetime [α ⊓ βi] has ended
      too. So the case of (L1) in which the state is still lent out ([Out κ]), refuted
      inside [gmb_move] with the guard stored by the lend, is never reached: the move below
      finds the state [In]. *)
  Lemma test_relend_sub_lifetime s t :
    llft_ctx -∗ cc s t -∗ £ 2 -∗
    |={↑Nllft}=> |={↑Nllft}[∅]▷=> |={↑Nllft}=> |={↑Nllft}[∅]▷=> |={↑Nllft}=>
    |={↑Nllft}[∅]▷=> |={↑Nllft ∪ ↑gmbN}=> ∃ t', cc s t'.
  Proof.
    iIntros "#LFT C Lc". iDestruct (lc_split 1 1 with "Lc") as "[Lc1 Lc2]".
    iMod (gmb_create cc _ 0 with "C") as (γ) "([%Hd %Hb] & #Inv & A & B)".
    iMod (llftl_begin with "LFT") as (α) "[Alpha #EndA]"; first done.
    iMod (share_timeless α with "A") as "[#Ga InhA]".
    (* first lend, at [α ⊓ β1] *)
    iMod (llftl_begin with "LFT") as (β1) "[Beta1 #EndB1]"; first done.
    iMod (llftl_borrow _ (α ⊓ β1) (∃ t, gmb_b γ t) with "LFT [B]") as "[Bor InhB]"; first done.
    { iNext. by iExists t. }
    iAssert (@[α ⊓ β1] &&{↑NllftG}&&> gmb_a γ s)%I as "#Ga1".
    { iApply (guards_transitive with "[] Ga"). iApply llftl_intersect_incl_l. }
    iAssert ((@[α] ∗ @[β1]) &&{↑NllftG}&&> @[α ⊓ β1])%I as "#Gk1".
    { iApply (guards_and_point with "[] []").
      - apply point_prop_llft_alive.
      - by rewrite llftl_tok_inter_and.
      - iApply guards_weaken_sep_l.
      - iApply guards_weaken_sep_r. }
    iMod (gmb_lend_guarded cc with "LFT Inv Ga1 [Lc1] Bor Gk1 [$Alpha $Beta1]")
      as "[_ [Alpha Beta1]]"; [done|by rewrite Hd|].
    iModIntro. iMod ("EndB1" with "Beta1") as "Dead". iModIntro. iNext.
    iMod "Dead" as "#Dead1".
    iMod ("InhB" with "[]") as ">[%t1 B]". { rewrite llftl_end_inter. by iRight. }
    (* second lend, at [α ⊓ β2] *)
    iMod (llftl_begin with "LFT") as (β2) "[Beta2 #EndB2]"; first done.
    iMod (llftl_borrow _ (α ⊓ β2) (∃ t, gmb_b γ t) with "LFT [B]") as "[Bor InhB]"; first done.
    { iNext. by iExists t1. }
    iAssert (@[α ⊓ β2] &&{↑NllftG}&&> gmb_a γ s)%I as "#Ga2".
    { iApply (guards_transitive with "[] Ga"). iApply llftl_intersect_incl_l. }
    iAssert ((@[α] ∗ @[β2]) &&{↑NllftG}&&> @[α ⊓ β2])%I as "#Gk2".
    { iApply (guards_and_point with "[] []").
      - apply point_prop_llft_alive.
      - by rewrite llftl_tok_inter_and.
      - iApply guards_weaken_sep_l.
      - iApply guards_weaken_sep_r. }
    iMod (gmb_lend_guarded cc with "LFT Inv Ga2 [Lc2] Bor Gk2 [$Alpha $Beta2]")
      as "[_ [Alpha Beta2]]"; [done|by rewrite Hd|].
    do 2 iModIntro. iMod ("EndB2" with "Beta2") as "Dead". iModIntro. iNext.
    iMod "Dead" as "#Dead2".
    (* end [α]; the owner moves *)
    do 2 iModIntro. iMod ("EndA" with "Alpha") as "Dead". iModIntro. iNext.
    iMod "Dead" as "#DeadA".
    iMod ("InhA" with "DeadA") as ">A".
    iModIntro. iMod (gmb_move cc with "Inv A") as (t') "[C _]"; first (rewrite Hb; solve_ndisj).
    iModIntro. by iExists t'.
  Qed.
  (** A lazy lend (the back-map stores the final contents with a settle law), in an
      instance whose bytes mask is [↑Nllft]: write through the borrow, end [κ]; the lender's
      inheritance is a claim, which it takes: it settles the lend, and gets the permission at
      the final value (observed with (L2)). *)
  Lemma test_lazy_lend_claim m s t t' :
    llft_ctx -∗ ghost_map_auth γm 1 m -∗ cc s t -∗ £ 7 -∗
    |={↑Nllft ∪ ↑gmbN}=> |={↑Nllft}[∅]▷=> |={↑Nllft ∪ ↑gmbN}=> ∃ m' γ,
      ghost_map_auth γm 1 m' ∗ gmb_inv cc γ ∗ gmb_a γ s ∗ gmb_b γ t' ∗ ⌜m' !! s = Some t'⌝.
  Proof.
    iIntros "#LFT Auth C £".
    iDestruct (lc_split 1 6 with "£") as "[£i £]". iDestruct (lc_split 1 5 with "£") as "[£1 £]".
    iDestruct (lc_split 1 4 with "£") as "[Pre £3]".
    iMod (gmb_create_mask cc _ 0 (↑Nllft) with "C") as (γ) "([%Hd %Hb] & #Inv & A & B)";
      first solve_ndisj.
    iMod (llftl_begin with "LFT") as (κ) "[Alive #End]"; first solve_ndisj.
    iDestruct (share_timeless κ with "A") as "X".
    iMod (fupd_mask_mono with "X") as "[#Ga InhA]"; first solve_ndisj.
    iMod (llftl_borrow _ κ (gmb_b_uniq cc γ (λ _, True%I)) with "LFT [B]") as "[Bor InhB]";
      first solve_ndisj.
    { iNext. by iApply (gmb_b_uniq_intro with "B"). }
    iMod lc_zero as "Lc0".
    iMod (gmb_lend_guarded_lazy cc _ _ _ _ _ 0 (∃ t, cc s t)%I with
      "LFT Inv Ga Lc0 [Pre] £1 £3 Bor [] Alive [] []") as "[Bor Alive]".
    { rewrite Hb. solve_ndisj. } { lia. } { by rewrite Hd. } { iApply guards_refl. }
    { iIntros (t0) "_ C !> !>". by iExists t0. }
    { iIntros "!> [%t0 C] _ !>". iExists t0. by iFrame. }
    (* write through the borrow *)
    iDestruct (llftl_bor_acc with "LFT Bor Alive") as "X"; first done.
    iMod (fupd_mask_mono with "X") as "[C Close]"; first solve_ndisj.
    iDestruct "C" as ">[%t0 C]".
    iMod (ghost_map_update t' with "Auth C") as "[Auth C]".
    iDestruct ("Close" $! (∃ t, cc s t)%I with "[C]") as "X".
    { iSplitR; last by iExists t'. iNext. iIntros "[$ _]". done. }
    iMod (fupd_mask_mono with "X") as "[Bor Alive]"; first solve_ndisj.
    (* end [κ] *)
    iModIntro. iMod ("End" with "Alive") as "Dead". iModIntro. iNext. iMod "Dead" as "#Dead".
    iMod ("InhA" with "Dead") as ">A".
    iMod ("InhB" with "Dead") as "Cl".
    iModIntro. iMod (lc_fupd_elim_later with "£i Cl") as "Cl".
    (* the lender takes its claim: the lend is settled *)
    iMod (gmb_b_uniq_settle cc with "Inv Cl") as (t1) "[B _]"; first (rewrite Hb; solve_ndisj).
    iDestruct (gmb_share cc (gmb_a γ s ∗ gmb_b γ t1) (↑NllftG) 0 with "Inv [] []") as "#Gc".
    { solve_ndisj. } { iApply guards_weaken_sep_l. } { iApply guards_weaken_sep_r. }
    iMod (guards_open with "Gc [$A $B]") as "[C Hcl]"; first solve_ndisj.
    iDestruct (ghost_map_lookup with "Auth C") as %Hs. rewrite lookup_insert in Hs.
    simplify_eq.
    iMod ("Hcl" with "C") as "[A B]".
    iModIntro. iExists _, γ. iFrame "∗#". by rewrite lookup_insert.
  Qed.

  (** A lazy lend whose lender abandons its borrow and its inheritance: after [κ] ends, the
      owner moves; the move settles the pending lend (it forces the stored contents, with
      the bytes mask and the dead token, without the lender). *)
  Lemma test_lazy_lend_abandoned s t :
    llft_ctx -∗ cc s t -∗ £ 6 -∗
    |={↑Nllft ∪ ↑gmbN}=> |={↑Nllft}[∅]▷=> |={↑Nllft ∪ ↑gmbN}=> ∃ t', cc s t'.
  Proof.
    iIntros "#LFT C £".
    iDestruct (lc_split 1 5 with "£") as "[Pre £]". iDestruct (lc_split 1 4 with "£") as "[£1 £3]".
    iMod (gmb_create_mask cc _ 0 (↑Nllft) with "C") as (γ) "([%Hd %Hb] & #Inv & A & B)";
      first solve_ndisj.
    iMod (llftl_begin with "LFT") as (κ) "[Alive #End]"; first solve_ndisj.
    iDestruct (share_timeless κ with "A") as "X".
    iMod (fupd_mask_mono with "X") as "[#Ga InhA]"; first solve_ndisj.
    iMod (llftl_borrow _ κ (gmb_b_uniq cc γ (λ _, True%I)) with "LFT [B]") as "[Bor _]";
      first solve_ndisj.
    { iNext. by iApply (gmb_b_uniq_intro with "B"). }
    iMod lc_zero as "Lc0".
    iMod (gmb_lend_guarded_lazy cc _ _ _ _ _ 0 (∃ t, cc s t)%I with
      "LFT Inv Ga Lc0 [Pre] £1 £3 Bor [] Alive [] []") as "[_ Alive]".
    { rewrite Hb. solve_ndisj. } { lia. } { by rewrite Hd. } { iApply guards_refl. }
    { iIntros (t0) "_ C !> !>". by iExists t0. }
    { iIntros "!> [%t0 C] _ !>". iExists t0. by iFrame. }
    iModIntro. iMod ("End" with "Alive") as "Dead". iModIntro. iNext. iMod "Dead" as "#Dead".
    iMod ("InhA" with "Dead") as ">A".
    iModIntro.
    iMod (gmb_move cc with "Inv A") as (t') "[C _]"; first (rewrite Hb; solve_ndisj).
    iModIntro. by iExists t'.
  Qed.
End GmbTests.
