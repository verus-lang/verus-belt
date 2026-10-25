From lrust.typing Require Export type.
From lrust.typing Require Import type_context programs own.
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
  
  Lemma typed_atomic_instr
    {𝔄 𝔅l} (E: elctx) (L: llctx) Il ϝ n n'
    (p : path) (ty : type 𝔄)
    (T': tctx 𝔅l) (tr: predl_trans [𝔄] 𝔅l) :
    (∀ x v d tid post mask na_mask at_mask iκs,
      na_mask ∪ at_mask = ⊤ →
      na_mask ∩ at_mask = mask →
      ⊢ (llft_ctx -∗ time_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
      llctx_interp L -∗ atomic_ctx at_mask (AtomicOpen n) -∗
      (cna_lifetimes tid (invctx_to_multiset Il ⊎ (list_to_set_disj iκs))) -∗
      ϝ ⊑ lft_intersect_list iκs -∗
      ⌜eval_path p = Some v⌝ -∗ ty_own ty x d d tid [FVal v] -∗
      ⟨π, tr post -[x] mask π⟩ -∗
      ⧖(S d) -∗
      ⧗1 -∗ £(advance_credits d) -∗ |={⊤}=>
      ∃ xl' mask' at_mask',
      ⌜na_mask ∪ at_mask' = ⊤ ∧ na_mask ∩ at_mask' = mask'⌝ ∗
      llctx_interp L ∗ atomic_ctx at_mask' (AtomicOpen n') ∗
      (cna_lifetimes tid (invctx_to_multiset Il ⊎ (list_to_set_disj iκs))) ∗
      tctx_interp tid T' xl' ∗ ⟨π, post xl' mask' π⟩
    )%I)
    → typed_inv_instr E L
      (InvCtx Il ϝ (AtomicOpen n)) +[p ◁ ty]
      (Seq Skip Skip)
      (InvCtx Il ϝ (AtomicOpen n')) (const T') tr.
  Proof.
    intros Hvs tid post mask iκs xl. destruct xl as [x []].
    iIntros "#LFT #TIME #PROPH #UNIQ #E L I [T _] Obs".
    iDestruct "T" as (v d) "(p & #⧖1 & own)".
    iDestruct "I" as (na_mask at_mask) "[%Hmask [[I1 #I1'] [I2 Iat]]]".
    wp_bind Skip.
    iApply wp_fupd.
    iApply (wp_cumulative_time_receipt2 with "TIME"); first by set_solver.
    iIntros "⧗". replace 2 with (1 + 1); last by done.
    iDestruct (cumulative_time_receipt_sep with "⧗") as "[⧗1 ⧗2]".
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗1 ⧖1") as "[⧖ £]";
        first by solve_ndisj.
    wp_let. iModIntro. wp_let. replace (d + 1) with (S d) by lia.
    
    iMod (Hvs x v d tid post mask na_mask at_mask with "LFT TIME PROPH UNIQ E L Iat I1 I1' p own Obs ⧖ ⧗2 £") as (xl' mask' at_mask' Hmasks') "(L & Iat & I1 & T)".
      { intuition. } { intuition. } 
    wp_let.
    iFrame. iFrame "#". done.
  Qed.
  
  Lemma typed2_atomic_instr
    {𝔄1 𝔄2 𝔅l} (E: elctx) (L: llctx) Il ϝ n n'
    (p1 : path) (ty1 : type 𝔄1)
    (p2 : path) (ty2 : type 𝔄2)
    (T': tctx 𝔅l) (tr: predl_trans [𝔄1; 𝔄2] 𝔅l) :
    (∀ x1 x2 v1 v2 d tid post mask na_mask at_mask iκs,
      na_mask ∪ at_mask = ⊤ →
      na_mask ∩ at_mask = mask →
      ⊢ (llft_ctx -∗ time_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
      llctx_interp L -∗ atomic_ctx at_mask (AtomicOpen n) -∗
      (cna_lifetimes tid (invctx_to_multiset Il ⊎ (list_to_set_disj iκs))) -∗
      ϝ ⊑ lft_intersect_list iκs -∗
      ⌜eval_path p1 = Some v1⌝ -∗ ty_own ty1 x1 d d tid [FVal v1] -∗
      ⌜eval_path p2 = Some v2⌝ -∗ ty_own ty2 x2 d d tid [FVal v2] -∗
      ⟨π, tr post -[x1; x2] mask π⟩ -∗
      ⧖(S d) -∗
      ⧗1 -∗ £(advance_credits d) -∗ |={⊤}=>
      ∃ xl' mask' at_mask' ,
      ⌜na_mask ∪ at_mask' = ⊤ ∧ na_mask ∩ at_mask' = mask'⌝ ∗
      llctx_interp L ∗ atomic_ctx at_mask' (AtomicOpen n') ∗
      (cna_lifetimes tid (invctx_to_multiset Il ⊎ (list_to_set_disj iκs))) ∗
      tctx_interp tid T' xl' ∗ ⟨π, post xl' mask' π⟩
    )%I)
    → typed_inv_instr E L
      (InvCtx Il ϝ (AtomicOpen n)) +[p1 ◁ ty1; p2 ◁ ty2]
      (Seq Skip Skip)
      (InvCtx Il ϝ (AtomicOpen n')) (const T') tr.
  Proof.
    intros Hvs tid post mask iκs xl. destruct xl as [x1 [x2 []]].
    iIntros "#LFT #TIME #PROPH #UNIQ #E L I [T1 [T2 _]] Obs".
    iDestruct "T1" as (v1 d1) "(p1 & #⧖1 & own1)".
    iDestruct "T2" as (v2 d2) "(p2 & #⧖2 & own2)".
    iDestruct "I" as (na_mask at_mask) "[%Hmask [[I1 #I1'] [I2 Iat]]]".
    wp_bind Skip.
    iApply wp_fupd.
    iApply (wp_cumulative_time_receipt2 with "TIME"); first by set_solver.
    iIntros "⧗". replace 2 with (1 + 1); last by done.
    iDestruct (cumulative_time_receipt_sep with "⧗") as "[⧗1 ⧗2]".
    iCombine "⧖1 ⧖2" as "⧖max".
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗1 ⧖max") as "[⧖Smax £]";
        first by solve_ndisj.
    wp_let. iModIntro. wp_let.
    replace ((d1 `max` d2) + 1) with (S (d1 `max` d2)) by lia.
    
    iMod (Hvs x1 x2 v1 v2 (d1 `max` d2) tid post mask na_mask at_mask with "LFT TIME PROPH UNIQ E L Iat I1 I1' p1 [own1] p2 [own2] Obs ⧖Smax ⧗2 £") as (xl' mask' at_mask' Hmasks') "(L & Iat & I1 & T)".
      { intuition. } { intuition. } 
      { iDestruct "own1" as "[gho phys]". iFrame.
       iDestruct (ty_gho_own_depth_mono with "gho") as "[gho _]"; last by iFrame "gho".
       { lia. } { lia. }
     }
     { iDestruct "own2" as "[gho phys]". iFrame.
       iDestruct (ty_gho_own_depth_mono with "gho") as "[gho _]"; last by iFrame "gho".
       { lia. } { lia. }
     }
    wp_let.
    iFrame. iFrame "#". done.
  Qed.
  
  Lemma typed_atomic_instr_own_own_t
    {𝔄1 𝔅} (E: elctx) (L: llctx) Il ϝ n n'
    (p1 : path) (ty1 : type 𝔄1)
    (tyret: type 𝔅)
    (tr: predl_trans ([at_locₛ 𝔄1]) [at_locₛ 𝔅]) :
    (ty_size ty1 = 0) →
    (ty_size tyret = 0) →
    (∀ l1 x1 d tid post mask na_mask at_mask iκs,
      na_mask ∪ at_mask = ⊤ → na_mask ∩ at_mask = mask →
      ⊢ (llft_ctx -∗ time_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
      llctx_interp L -∗ atomic_ctx at_mask (AtomicOpen n) -∗
      (cna_lifetimes tid (invctx_to_multiset Il ⊎ (list_to_set_disj iκs))) -∗
      ϝ ⊑ lft_intersect_list iκs -∗
      ty_gho_own ty1 x1 d (S d) tid -∗
      ⟨π, tr post -[(l1, x1)] mask π⟩ -∗
      ⧖(S (S d)) -∗
      ⧗1 -∗
      £(2*d+5) -∗
      |={⊤}=>
      ∃ d' xret mask' at_mask',
      ⌜na_mask ∪ at_mask' = ⊤ ∧ na_mask ∩ at_mask' = mask'⌝ ∗
      ⧖(S d') ∗ llctx_interp L ∗ atomic_ctx at_mask' (AtomicOpen n') ∗
      (cna_lifetimes tid (invctx_to_multiset Il ⊎ (list_to_set_disj iκs))) ∗
      ▷ ty_gho_own tyret xret (d') (S d') tid ∗
          ⟨π, post -[(l1, xret)] mask' π⟩
    )%I)
    → typed_inv_instr E L
        (InvCtx Il ϝ (AtomicOpen n)) +[p1 ◁ own_ptr 0 ty1]
       (Seq Skip Skip)
       (InvCtx Il ϝ (AtomicOpen n')) (const +[p1 ◁ own_ptr 0 tyret])
       tr.
  Proof.
    intros Hsize0 Hsize0' Ha. apply typed_atomic_instr.
    iIntros ([l1 x1] v1 d tid post mask na_mask at_mask iκs Hm1 Hm2) "#LFT #TIME #PROPH #UNIQ #E L I I1 I2 %He1 Own1 Obs #⧖ ⧗ £".
    iDestruct "Own1" as "[Gho1 %Phys1]".
    destruct d as [|d]; first by done.
    iDestruct "Gho1" as "[Pt1 [Free1 Gho1]]".
    iDestruct (lc_weaken (_ + _)%nat with "£") as "[£1 £2]"; first last. {
    iMod (lc_fupd_elim_later with "£1 Gho1") as "Gho1". 
    iMod (Ha l1 x1 d tid post mask na_mask at_mask iκs Hm1 Hm2 with "LFT TIME PROPH UNIQ E L I I1 I2 Gho1 Obs [] ⧗ £2") as "X". { iApply (persistent_time_receipt_mono with "⧖"). lia. }
    iDestruct "X" as (d' xret mask' at_mask' Hmasks') "[⧖' [L [I [I1 [GhoRet Obs]]]]]".
    iModIntro. iExists -[(l1, xret)]. iFrame. iSplit; first by done.
    iExists v1. iFrame "%". iFrame.
    rewrite Hsize0. rewrite Hsize0'. iFrame.
    assert (ty_phys tyret (l1, xret).2 tid = []) as Hlen. {
      simpl. have Hl := ty_size_eq tyret xret tid. destruct (ty_phys tyret xret tid); try done.
      simpl in Hl. lia.
    }
    rewrite Hlen. rewrite heap_mapsto_fancy_vec_nil. done.
    }
    unfold advance_credits; lia.
  Qed.
  
   Lemma typed_atomic_instr_own2_emp
    {𝔄1 𝔄2} (E: elctx) (L: llctx) Il ϝ n n'
    (p1 : path) (ty1 : type 𝔄1)
    (p2 : path) (ty2 : type 𝔄2)
    (tr: predl_trans (at_locₛ 𝔄1 :: [at_locₛ 𝔄2]) []) :
    (∀ l1 l2 x1 x2 d tid post mask na_mask at_mask iκs,
      na_mask ∪ at_mask = ⊤ → na_mask ∩ at_mask = mask →
      ⊢ (llft_ctx -∗ time_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
      llctx_interp L -∗ atomic_ctx at_mask (AtomicOpen n) -∗
      (cna_lifetimes tid (invctx_to_multiset Il ⊎ (list_to_set_disj iκs))) -∗
      ϝ ⊑ lft_intersect_list iκs -∗
      ty_gho_own ty1 x1 d (S d) tid -∗
      ty_gho_own ty2 x2 d (S d) tid -∗
      ⟨π, tr post -[(l1, x1); (l2, x2)] mask π⟩ -∗
      ⧖(S (S (S d))) -∗
      £(d+1) -∗
      |={⊤}=>
      ∃ mask' at_mask',
      ⌜na_mask ∪ at_mask' = ⊤ ∧ na_mask ∩ at_mask' = mask'⌝ ∗
      llctx_interp L ∗ atomic_ctx at_mask' (AtomicOpen n') ∗
      (cna_lifetimes tid (invctx_to_multiset Il ⊎ (list_to_set_disj iκs))) ∗
      ⟨π, post -[] mask' π⟩
    )%I)
    → typed_inv_instr E L (InvCtx Il ϝ (AtomicOpen n))
        +[p1 ◁ own_ptr 0 ty1; p2 ◁ own_ptr 0 ty2]
       (Seq Skip Skip) (InvCtx Il ϝ (AtomicOpen n'))
       (const +[])
       tr.
  Proof.
    intros Ha. apply typed2_atomic_instr.
    iIntros ([l1 x1] [l2 x2] v1 v2 d tid post mask na_mask at_mask iκs Hm1 Hm2) "#LFT #TIME #PROPH #UNIQ #E L I I1 #I2 %He1 Own1 %He2 Own2 Obs #⧖ ⧗ £".
    iDestruct "Own1" as "[Gho1 %Phys1]".
    iDestruct "Own2" as "[Gho2 %Phys2]".
    destruct d as [|d]; first by done.
    iDestruct "Gho1" as "[Pt1 [Free1 Gho1]]".
    iDestruct "Gho2" as "[Pt2 [Free2 Gho2]]".
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗ ⧖") as "[#⧖S £2]". { set_solver. }
    iCombine "Gho1 Gho2" as "Gho".
    iMod (lc_fupd_elim_later with "[£] Gho") as "[Gho1 Gho2]". { iApply (lc_weaken with "£"). unfold advance_credits. lia. }
    iMod (Ha l1 l2 x1 x2 d tid post mask na_mask at_mask iκs Hm1 Hm2 with "LFT TIME PROPH UNIQ E L I I1 I2 Gho1 Gho2 Obs [] [£2]") as "X". { iApply (persistent_time_receipt_mono with "⧖S"). lia. }
    { iApply (lc_weaken with "£2"). unfold advance_credits. lia. }
    iDestruct "X" as (mask' at_mask' Hmasks') "[L [Iat [I1 Obs]]]".
    iModIntro. iExists -[]. iFrame. done.
  Qed.
End programs_util_atomic.
