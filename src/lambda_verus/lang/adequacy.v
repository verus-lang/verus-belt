Require Import guarding.internal.na_invariants_fork.
From iris.program_logic Require Export adequacy weakestpre.
From iris.algebra.lib Require Import mono_nat.
From iris.algebra Require Import numbers.
From iris.algebra.lib Require Import gmap_view.
From lrust.lang Require Export heap.
From lrust.lang Require Import proofmode notation.
From lrust.util Require Import adequacy_util non_atomic_cell_map atomic_lock_counter.
Set Default Proof Using "Type".

Class lrustGpreS Σ := HeapGpreS {
  #[global] lrustGpreS_iris :: invGpreS Σ;
  #[global] lrustGpreS_heap :: inG Σ (authR heapUR);
  #[global] lrustGpreS_heap_freeable :: inG Σ (authR heap_freeableUR);
  #[global] lrustGpreS_heap_na_logic :: na_logicG loc lang.val Σ;
  #[global] lrustGpreS_heap_bbank :: inG Σ (gmap_viewR nat (agreeR (prodO
    (leibnizO (loc * list abyte)) (laterO (iPropO Σ)))));
  #[global] lrustGpreS_heap_na_inv :: na_invG Σ;
  #[global] lrustGpreS_atomic_lock_ctr :: alc_logicG Σ;
  #[global] lrustGpreS_time :: timePreG Σ
}.

Definition lrustΣ : gFunctors :=
  #[invΣ; timeΣ;
    GFunctor (constRF (authR heapUR));
    GFunctor (constRF (authR heap_freeableUR));
    na_logicΣ loc lang.val;
    GFunctor (gmap_viewRF nat (agreeRF (prodOF (leibnizO (loc * list abyte)) (laterOF idOF))));
    alc_logicΣ;
    na_invΣ
    ].
Global Instance subG_heapPreG {Σ} : subG lrustΣ Σ → lrustGpreS Σ.
Proof. solve_inG. Qed.

Definition lrust_adequacy Σ `{!lrustGpreS Σ} e φ k :
  (∀ `{!lrustGS Σ}, £k -∗ time_ctx -∗ WP e {{ v, ⌜φ v⌝ }}) →
  adequate NotStuck e (∅,false) (λ v _, φ v).
Proof.
  intros Hwp. apply adequate_alt. intros t2 σ2 [n [κs ?]]%erased_steps_nsteps.
  (* use a variant that lets us start at step 1 with some later credits *)
  eapply (adequacy_util.wp_strong_adequacy Σ _); [|done]=>?.
  iMod (non_atomic_map_alloc_empty) as (vγ) "Hvγ".
  iMod (own_alloc (● (∅ : heapUR))) as (bγ) "Hbγ";
    first by apply auth_auth_valid.
  iMod (own_alloc (● (∅ : heap_freeableUR))) as (fγ) "Hfγ";
    first by apply auth_auth_valid.
  iMod (own_alloc (gmap_view_auth (V:=agreeR (prodO (leibnizO (loc * list abyte))
    (laterO (iPropO Σ)))) (DfracOwn 1) ∅)) as (kγ) "Hkγ";
    first by apply gmap_view_auth_valid.
  iIntros "H£". iDestruct "H£" as "[H£1 H£2]".
  iMod (time_init with "H£1") as (Htime) "[TIME Htime]"; [done|].
  iMod (na_alloc) as (atomic_poolname) "pool".
  iMod (atomic_lock_ctr_alloc) as (atomic_lock_ctr_name) "ctr".
  set (Hheap := HeapGS _ _ _ _ _ vγ bγ kγ fγ atomic_poolname atomic_lock_ctr_name).
  iModIntro. iExists _, [_], _, _. simpl.
  iDestruct (Hwp (LRustGS _ _ _ _ Hheap Htime) with "H£2 TIME") as "$".
  iSplitL. { iFrame. iSplitL "Hbγ Hkγ". { iExists ∅. iSplit; [iPureIntro; apply phys_rel_empty|].
      iApply (bytes_ctx_empty with "[Hbγ] [Hkγ]"); [by rewrite /to_heap fmap_empty|done]. } iPureIntro. intros ?? Hb. by rewrite lookup_empty in Hb. }
  iIntros ([|e' [|]]? -> ??) "//".
  iIntros "[??] [?_] _". iApply fupd_mask_weaken; [|iIntros "_ !>"]; [done|].
  iSplit; [|done]. iIntros (v2 t2'' [= -> <-]). by rewrite to_of_val.
Qed.
