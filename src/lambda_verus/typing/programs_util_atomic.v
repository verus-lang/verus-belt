From lrust.typing Require Export type.
From lrust.typing Require Import type_context programs ghost.
From iris.program_logic Require Import ectx_lifting.
From lrust.lang Require Import lang.
From lrust.util Require Import atomic_lock_counter.
From guarding Require Import guard tactics.
From guarding.lib Require Import cancellable.
From lrust.lifetime Require Import lifetime_full.
Set Default Proof Using "Type".

(* TODO move these to lang directory *)
Definition GlobalAtomicLock: expr := (
    rec: "global_atomic_lock" [] :=
        if: GlobalLock then
          "global_atomic_lock" []
        else
          #☠
)%V [].
Notation GlobalAtomicUnlock := (GlobalUnlock) (only parsing).

Section programs_util_atomic.
  Context `{!typeG Σ}. 
  
  Local Lemma wp_global_try_atomic_lock E :
     {{{ True }}}
     GlobalLock @ E
     {{{ (b: Z), RET LitV (LitInt b);
      match b with 0%Z => heap_ato_ctx | 1%Z => True | _ => False end }}}.
  Proof.
    iIntros (Φ) "ato ToΦ".
    iApply wp_lift_atomic_base_step_no_fork; auto. iIntros (σ1 stepcnt κ κs n) "[Hσ Ht]".
    iDestruct "Hσ" as (hF) "(Hσ & HhF & %REL & ato2)".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iSplit. { iExists _, _, _, _. iPureIntro. apply GlobalLockS. }
    iNext; iIntros (e2 σ2 efs Hstep); inv_head_step. iMod "Hclose" as "_".
    iMod (time_interp_step with "Ht") as "$". iIntros "credit !>". iFrame.
    iSplit; first by done. iSplit; first by done.
    iApply "ToΦ". destruct σ1 as [σ1 [|]]; done.
  Qed.
    
  Lemma wp_global_atomic_lock E :
     {{{ True }}}
     GlobalAtomicLock @ E
     {{{ RET LitV LitPoison; heap_ato_ctx }}}.
  Proof.
    iIntros (Φ) "_ ToΦ". iLöb as "IH".
    wp_rec.
    wp_bind (GlobalLock).
    iApply wp_global_try_atomic_lock; first done.
    iNext. iIntros (z) "A".
    destruct (decide (z = 0)) as [Heq0|Hn]; last destruct (decide (z = 1)) as [Heq1|Hn2].
     - subst z. wp_if. iApply "ToΦ". done.
     - subst z. wp_if. iApply "IH". iNext. done.
     - destruct z as [|[ | | ]|]; try done.
  Qed.
  
  Lemma wp_global_atomic_unlock E :
     {{{ heap_ato_ctx }}}
     GlobalAtomicUnlock @ E
     {{{ RET LitV LitPoison; True }}}.
  Proof.
    iIntros (Φ) "ato ToΦ".
    iApply wp_lift_atomic_base_step_no_fork; auto. iIntros (σ1 stepcnt κ κs n) "[Hσ Ht]".
    iDestruct "Hσ" as (hF) "(Hσ & HhF & %REL & ato2)".
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    destruct σ1 as [σ1 [|]].
      - iSplit. { iExists _, _, _, _. iPureIntro. apply GlobalUnlockS. trivial. }
        iNext; iIntros (e2 σ2 efs Hstep); inv_head_step. iMod "Hclose" as "_".
        iMod (time_interp_step with "Ht") as "$". iIntros "credit !>". iFrame.
        iSplit; first by done. iSplit; first by done.
        iApply "ToΦ". done.
      - iDestruct "ato" as "[pool1 _]". iDestruct "ato2" as "[pool2 _]".
        iDestruct (na_invariants_fork.na_own_disjoint with "pool1 pool2") as "%disj". exfalso.
        assert (xH ∈ (⊤: coPset)) by set_solver. solve_ndisj.
  Qed.
  
  (** A ghost operation ([GhostOp], see [typing/ghost.v]) while the atomic invariants are
      open: the update may change the depth of the atomic context and its mask. *)
  Lemma typed_atomic_ghost_op {𝔄l 𝔅l} (E: elctx) (L: llctx) Il ϝ n n'
      (T: tctx 𝔄l) (T': val → tctx 𝔅l) (tr: predl_trans 𝔄l 𝔅l) :
    (∀ xl tid post mask na_mask at_mask iκs,
      na_mask ∪ at_mask = ⊤ → na_mask ∩ at_mask = mask →
      ⊢ (llft_ctx -∗ time_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
      llctx_interp L -∗ atomic_ctx at_mask (AtomicOpen n) -∗
      (cna_lifetimes tid (invctx_to_multiset Il ⊎ (list_to_set_disj iκs))) -∗
      ϝ ⊑ lft_intersect_list iκs -∗
      tctx_interp tid T xl -∗ ⟨π, tr post xl mask π⟩ -∗ ⧗1 -∗ ⧗1 ={⊤}=∗
      ∃ xl' mask' at_mask',
      ⌜na_mask ∪ at_mask' = ⊤ ∧ na_mask ∩ at_mask' = mask'⌝ ∗
      llctx_interp L ∗ atomic_ctx at_mask' (AtomicOpen n') ∗
      (cna_lifetimes tid (invctx_to_multiset Il ⊎ (list_to_set_disj iκs))) ∗
      tctx_interp tid (T' (MLitV (VTuple []))) xl' ∗ ⟨π, post xl' mask' π⟩
    )%I)
    → typed_inv_instr E L (InvCtx Il ϝ (AtomicOpen n)) T GhostOp
        (InvCtx Il ϝ (AtomicOpen n')) T' tr.
  Proof.
    intros Hvs. apply typed_inv_instr_ghost_op.
    iIntros (tid post mask iκs xl) "#LFT #TIME #PROPH #UNIQ #E L I T Obs ⧗ ⧗'".
    iDestruct "I" as (na_mask at_mask) "[[%Hm1 %Hm2] [[I1 #I1'] [I2 Iat]]]".
    iMod (Hvs xl tid post mask na_mask at_mask iκs Hm1 Hm2 with
      "LFT TIME PROPH UNIQ E L Iat I1 I1' T Obs ⧗ ⧗'") as
      (xl' mask' at_mask' Hmasks') "(L & Iat & I1 & T & Obs)".
    iModIntro. iExists xl', mask'. iFrame "L T Obs". iExists na_mask, at_mask'. iFrame "#∗". by iPureIntro.
  Qed.
End programs_util_atomic.
