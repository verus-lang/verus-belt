From lrust.typing Require Export type.
From lrust.typing Require Import type_context programs programs_util_own programs_util_atomic own ghost tracked shr_bor product.
From lrust.util Require Import atomic_lock_counter.
From guarding Require Import guard tactics.
From lrust.lifetime Require Import lifetime_full.
From guarding.lib Require Import cancellable.
Set Default Proof Using "Type".
From Coq.Logic Require Import Classical_Prop.

Implicit Type 𝔄 𝔅: syn_type.

Section atomic_invariants.
  Context `{!typeG Σ}. 
  
  Definition null_tid : positive := atomic_pool_name.

  (*
  In Verus, the AtomicInvariant is parameterized as:

  ```
  AtomicInvariant<K, V, Pred>`
  where Pred: InvariantPredicate<K, V>
  ```

  The `K` here is given by `ℭ`, the V by `ty: type 𝔄`. The trait bound is given by the `pred`.
 
  We use `abstracted_syn_type` for the predicate since it needs to be independent of the thread id.

  We use law of excluded middle to case on whether `ty` is Send or not, because I couldn't
  otherwise find a model that works smoothly in both cases.  In practice, there's
  usually no reason to use AtomicInvariant if `ty` _isn't_ Send, but it is technically allowed.
  *)
  
  Program Definition atomic_inv_ty {𝔄 ℭ} (ty: type 𝔄) (pred: (abstracted_syn_type 𝔄) → ~~ℭ → proph_asn → Prop) : type (invₛ ℭ) := ({|
    ty_size := 0;
    ty_lfts := [];
    ty_E := [];
    ty_gho_pers x d g tid := True%I ;
    ty_gho_own x d g tid := match x with (N, γ, c) =>
        Active γ ∗ external_na_inv γ ATOMIC_POOL N
          (∃ x' d' g' tid' , ⧖(S d' `max` g') ∗ ty.(ty_gho_own) x' d' g' tid'
              (* casing on `Send ty` like this requires LEM. The reason we need to case is that:
                  * For the non-Send case, we can never move to any other tid.
                  * For the Send case, we specifically need it at null_tid.
                 Initially it seems like you could just have it at an unspecified tid' for the
                 Send case(which would let us unify the cases) but the problem there is that
                 you can't move from tid' because you don't have access to the tid' invariant context.
              *)
              ∗ ⟨ π, pred (syn_abstract x') c π ⟩ ∗ ⌜(Send ty ∧ tid' = null_tid) ∨ (¬(Send ty) ∧ tid = tid')⌝)
    end;
    ty_gho_res x d g tid := match x with (N, γ, c) =>
        Active γ ∗ external_na_inv γ ATOMIC_POOL N
          (∃ x' d' g' tid' , ⧖(S d' `max` g') ∗ ty.(ty_gho_own) x' d' g' tid'
              ∗ ⟨ π, pred (syn_abstract x') c π ⟩ ∗ ⌜(Send ty ∧ tid' = null_tid) ∨ (¬(Send ty) ∧ tid = tid')⌝)
    end;
    ty_phys x tid := [];
    ty_shr := default_shr (λ (x: ~~(invₛ ℭ)) d g tid, match x with (N, γ, c) =>
          Active γ ∗ external_na_inv γ ATOMIC_POOL N
            (∃ x' d' g' tid' , ⧖(S d' `max` g') ∗ ty.(ty_gho_own) x' d' g' tid'
                ∗ ⟨ π, pred (syn_abstract x') c π ⟩ ∗ ⌜(Send ty ∧ tid' = null_tid) ∨ (¬(Send ty) ∧ tid = tid')⌝)
      end);
  |})%I.
  Next Obligation. done. Qed. 
  Next Obligation. done. Qed. 
  Next Obligation. done. Qed. 
  Next Obligation. iIntros. iFrame. iIntros. done. Qed.
  Next Obligation. iIntros. done. Qed.
  Next Obligation. iIntros. done. Qed.
  Solve All Obligations with solve_default_shr.
  Next Obligation. intros. iIntros "H". iExact "H". Qed.
  
  Definition atomic_closer γ N P : iProp Σ :=
      (∀ E, (▷ (P ∨ Active γ)) ∗ na_invariants_fork.na_own ATOMIC_POOL E ={⊤}=∗ na_invariants_fork.na_own ATOMIC_POOL (E ∪ ↑N)).
  
  Program Definition atomic_closer_ty {𝔄 ℭ} (κ: lft) (ty: type 𝔄) (pred: (abstracted_syn_type 𝔄) → ~~ℭ → proph_asn → Prop) : type (invₛ ℭ) := ({|
    ty_size := 0;
    ty_lfts := [];
    ty_E := [];
    ty_gho_pers x d g tid := True%I ;
    ty_gho_own x d g tid := match x with (N, γ, c) =>
        atomic_lock_handle atomic_lock_ctr_name (↑N) ∗
        atomic_closer γ N (∃ x' d' g' tid' , ⧖(S d' `max` g') ∗ ty.(ty_gho_own) x' d' g' tid'
              ∗ ⟨ π, pred (syn_abstract x') c π ⟩ ∗ ⌜(Send ty ∧ tid' = null_tid) ∨ (¬(Send ty) ∧ tid = tid')⌝)
    end;
    ty_gho_res x d g tid := match x with (N, γ, c) =>
        atomic_lock_handle atomic_lock_ctr_name (↑N) ∗
        atomic_closer γ N (∃ x' d' g' tid' , ⧖(S d' `max` g') ∗ ty.(ty_gho_own) x' d' g' tid'
              ∗ ⟨ π, pred (syn_abstract x') c π ⟩ ∗ ⌜(Send ty ∧ tid' = null_tid) ∨ (¬(Send ty) ∧ tid = tid')⌝)
    end;
    ty_phys x tid := [];
    ty_shr := default_shr (λ (x: ~~(invₛ ℭ)) d g tid, match x with (N, γ, c) =>
          atomic_lock_handle atomic_lock_ctr_name (↑N) ∗
          atomic_closer γ N (∃ x' d' g' tid' , ⧖(S d' `max` g') ∗ ty.(ty_gho_own) x' d' g' tid'
                ∗ ⟨ π, pred (syn_abstract x') c π ⟩ ∗ ⌜(Send ty ∧ tid' = null_tid) ∨ (¬(Send ty) ∧ tid = tid')⌝)
      end);
  |})%I.
  Next Obligation. done. Qed. 
  Next Obligation. done. Qed. 
  Next Obligation. done. Qed. 
  Next Obligation. iIntros. iFrame. iIntros. done. Qed.
  Next Obligation. iIntros. done. Qed.
  Next Obligation. iIntros. done. Qed.
  Solve All Obligations with solve_default_shr.
  Next Obligation. intros. iIntros "H". iExact "H". Qed.

  Lemma atomic_inv_ty_resolve E L {𝔄 ℭ} (ty: type 𝔄) (pred: (abstracted_syn_type 𝔄) → ~~ℭ → proph_asn → Prop)
      : resolve E L (atomic_inv_ty ty pred) (const (const True)).
  Proof. apply resolve_just. Qed.

  Global Instance atomic_inv_ty_res_own {𝔄 ℭ} (ty: type 𝔄) pred :
    ResOwn (atomic_inv_ty (ℭ:=ℭ) ty pred).
  Proof. done. Qed.
  Global Instance atomic_closer_ty_res_own {𝔄 ℭ} κ (ty: type 𝔄) pred :
    ResOwn (atomic_closer_ty (ℭ:=ℭ) κ ty pred).
  Proof. done. Qed.
  
  Local Lemma gho_equiv_of_send {𝔄 ℭ} (ty: type 𝔄) (pred: (abstracted_syn_type 𝔄) → ~~ℭ → proph_asn → Prop) x d g tid tid'
      : Send ty →
      ty_gho_own (atomic_inv_ty ty pred) x d g tid ⊣⊢ ty_gho_own (atomic_inv_ty ty pred) x d g tid'.
  Proof.
    intros Hsend. unfold ty_gho_own, atomic_inv_ty. destruct x as [[ns γ] c].
    assert (
      (∃ (x' : ~~ 𝔄) (d' g' : nat) (tid'0 : thread_id), ⧖(S d' `max` g') ∗ 
       ty_gho_own ty x' d' g' tid'0 ∗ ⟨ π, pred (syn_abstract x') c π ⟩  ∗ ⌜(Send ty ∧ tid'0 = null_tid) ∨ (¬(Send ty) ∧ tid = tid'0)⌝)
      ⊣⊢ (∃ (x' : ~~ 𝔄) (d' g' : nat) (tid'0 : thread_id), ⧖(S d' `max` g') ∗ 
       ty_gho_own ty x' d' g' tid'0 ∗ ⟨ π, pred (syn_abstract x') c π ⟩ ∗ ⌜(Send ty ∧ tid'0 = null_tid) ∨ (¬(Send ty) ∧ tid' = tid'0)⌝) ) as X.
     { iSplit.
         - iDestruct 1 as (x' d' g' tid0) "(? & ? & ? & [?|%A])"; last by intuition.
           iFrame. iLeft. done.
         - iDestruct 1 as (x' d' g' tid0) "(? & ? & ? & [?|%A])"; last by intuition.
           iFrame. iLeft. done.
     }
     setoid_rewrite X.
     done. 
  Qed.
  
  Lemma atomic_inv_ty_send {𝔄 ℭ} (ty: type 𝔄) (pred: (abstracted_syn_type 𝔄) → ~~ℭ → proph_asn → Prop)
      : Send ty → Send (atomic_inv_ty ty pred).
  Proof.
    intros Hsend. split; [done|].
    intros.
    rewrite gho_equiv_of_send.
    iIntros. iApply step_fupdN_intro; first by solve_ndisj. iNext. iModIntro.
    iExists x, 0. simpl. iFrame. replace (d0 + 0) with d0 by lia. iFrame "#". done.
  Qed.
  
  Lemma atomic_inv_ty_sync {𝔄 ℭ} (ty: type 𝔄) (pred: (abstracted_syn_type 𝔄) → ~~ℭ → proph_asn → Prop)
      : Send ty → Sync (atomic_inv_ty ty pred).
  Proof.
    intros Hsend. apply sync_default; [done|].
    split; [done|split; [|done]].
    apply gho_equiv_of_send; trivial.
  Qed.
  
  Lemma typed_atomic_lock E L Il ϝ :
      typed_inv_instr E L
      (InvCtx Il ϝ AtomicClosed) +[]
      GlobalAtomicLock
      (InvCtx Il ϝ (AtomicOpen 0)) (const +[])
      id.
  Proof.
    iIntros (tid post mask iκs xl) "#LFT #TIME #PROPH #UNIQ #E L I _ Obs".
    destruct xl. iDestruct "I" as (na_mask at_mask Hmask) "[I1 [I2 %Iat2]]".
    subst at_mask.
    iApply wp_global_atomic_lock; first by done.
    iNext. iIntros "[pool ctr]".
    iExists -[], mask. iFrame. iPureIntro; set_solver.
  Qed.
  
  Lemma typed_atomic_unlock E L Il ϝ :
      typed_inv_instr E L
      (InvCtx Il ϝ (AtomicOpen 0)) +[]
      GlobalAtomicUnlock
      (InvCtx Il ϝ AtomicClosed) (const +[])
      id.
  Proof.
    iIntros (tid post mask iκs xl) "#LFT #TIME #PROPH #UNIQ #E L I _ Obs".
    destruct xl. iDestruct "I" as (na_mask at_mask Hmask) "[I1 [I2 [Iat1 Iat2]]]".
    iDestruct (atomic_lock_ctr_top with "Iat1") as "%Hat_mask". subst at_mask.
    iApply (wp_global_atomic_unlock with "[Iat1 Iat2]"). { iFrame. }
    iNext. iIntros "_".
    iExists -[], mask. iFrame. iExists ⊤. iSplit; iPureIntro; set_solver.
  Qed.
  
  Local Lemma change_tid_in {𝔄} (ty : type 𝔄) x d g tid κs L : 
      Timeless L →
      ⊢ llft_ctx -∗ uniq_ctx -∗ time_ctx -∗ £(d + 1) -∗ ⧖(d+1) -∗
        ▷ ty_gho_own ty x d g tid -∗
        (∀ (κ: lft) , ⌜κ ∈ κs⌝ -∗ (L &&{↑NllftG}&&> @[κ])) -∗ L -∗
        cna_lifetimes tid κs
        ={⊤}=∗ ∃ tid' x' d',
          ⌜((Send ty ∧ tid' = null_tid) ∨ (¬(Send ty) ∧ tid = tid'))⌝ ∗
          ty_gho_own ty x' d' g tid' ∗ ⧖(S d') ∗ ⌜syn_abstract x' = syn_abstract x⌝
          ∗ L ∗ cna_lifetimes tid κs.
  Proof.
    destruct (classic (Send ty)) as [Send|NotSend].
    - iIntros (TL) "LFT UNIQ TIME [£s £1] #⧖ gho #AllGuards L cna_lifetimes".
      iMod (lc_fupd_elim_later with "£1 gho") as "gho".
      iDestruct (send_change_tid tid null_tid x d g L _ κs (d+1) with "LFT UNIQ TIME [] cna_lifetimes AllGuards L gho ⧖") as "vs"; try done. { iApply guards_refl. }
      
      iDestruct (lc_step_fupdN_elim_later with "£s vs") as "vs".
      do 2 (iMod (fupd_mask_mono with "vs") as "vs"; first by set_solver).
      iDestruct "vs" as (x' off) "[gho [⧖off [%Habs GH]]]".
      iModIntro. iExists null_tid, x', (d + off). iFrame.
      iDestruct (persistent_time_receipt_mono with "⧖off") as "$"; first lia.
      iSplit; last by done. iPureIntro. left. split; trivial.
    - iIntros (TL) "LFT UNIQ TIME [£s £1] #⧖ gho #AllGuards L cna_lifetimes".
      iMod (lc_fupd_elim_later with "£1 gho") as "gho".
      iModIntro. iExists tid, x, d. iFrame. replace (S d) with (d + 1) by lia. iFrame "#".
      iSplit; last by done. iPureIntro. right. split; trivial.
  Qed.

  Local Lemma change_tid_out {𝔄} (ty : type 𝔄) x d g tid tid' : 
      ((Send ty ∧ tid' = null_tid) ∨ (¬(Send ty) ∧ tid = tid')) →
      ⊢ llft_ctx -∗ uniq_ctx -∗ time_ctx -∗ £(d + 1) -∗ ⧖(d+1) -∗ ▷ ty_gho_own ty x d g tid'
          ={⊤}=∗ ∃ x' d', ty_gho_own ty x' d' g tid ∗ ⧖(S d') ∗ ⌜syn_abstract x' = syn_abstract x⌝.
  Proof.
      intros Ha. 
      iIntros "LFT #UNIQ TIME [£s £1] #⧖ gho".
      iMod (lc_fupd_elim_later with "£1 gho") as "gho".
      iDestruct (uniq_ctx_get_cna_lifetimes_inv with "UNIQ") as "Gnull".
      destruct Ha as [[Send EqTid]|[_ EqTid]].
        - subst tid'.
          iDestruct (send_change_tid null_tid tid x d g True%I True%I ∅ (d+1) with "LFT UNIQ TIME [] [] [] [] gho ⧖") as "vs"; try done. { iIntros (κ) "%Hin". set_solver. }
          iDestruct (lc_step_fupdN_elim_later with "£s vs") as "vs".
          do 2 (iMod (fupd_mask_mono with "vs") as "vs"; first by set_solver).
          iDestruct "vs" as (x' off) "[gho [⧖off [%Habs GH]]]".
          iModIntro. iExists x', (d + off). iFrame.
          iDestruct (persistent_time_receipt_mono with "⧖off") as "$"; first lia. done.
        - rewrite EqTid. iModIntro. iExists x, d. iFrame.
          iDestruct (persistent_time_receipt_mono with "⧖") as "$"; first lia. done.
  Qed.
  
  Lemma typed_atomic_inv_alloc {𝔄 ℭ} (p1 p2 : path) (ty : type 𝔄) (pred: (abstracted_syn_type 𝔄) → ~~ℭ → proph_asn → Prop) (tyCN : type (ℭ * namespaceₛ)) E L I :
    lctx_ictx_alive E L I →
    typed_inv_instr E L I
      +[p1 ◁ own_ptr 0 (ghost_ty tyCN);
        p2 ◁ own_ptr 0 ty
       ]
      (Seq Skip Skip) I
      (const +[p2 ◁ own_ptr 0 (atomic_inv_ty ty pred)])
      (λ post '-[(_, (c, N)); (_, v)], λ mask π, pred (syn_abstract v) c π ∧ ∀ l γ, post -[(l, (N, γ, c))] mask π).
  Proof.
    intros IAlv.
    apply typed_instr_of_skip_own2_own. { trivial. } { trivial. }
    intros l1 l2 x1 x2 d tid post mask iκs.
    iIntros "#LFT #TIME #PROPH #UNIQ #E L I Gho Tra #Obs #⧖ £".
    destruct I as [Il fnlft al].
    iDestruct "I" as (na_mask at_mask) "[IA [[cna_lifetimes IB] IC]]".
    destruct x1 as [c ns].
    iDestruct (lctx_ictx_alive_all_guards _ _ _ _ _ _ IAlv with "L E IB") as "#AllGuards".
    iMod (change_tid_in _ _ d with "LFT UNIQ TIME £ [] Tra AllGuards L cna_lifetimes") as (tid' x' d') "[%TidsEq [gho' [#⧖' [%Habs [L cna_lifetimes]]]]]"; first by (iApply (persistent_time_receipt_mono with "⧖"); lia).
    iMod (external_inv_na_alloc ATOMIC_POOL ns with "[gho']") as (γ) "[inv active]"; last first.
     - iModIntro. iExists (ns, γ, c). iFrame. 
       iApply (proph_obs_impl with "Obs"). intuition.
     - iFrame. iCombine "⧖ ⧖'" as "⧖max".
       iDestruct (persistent_time_receipt_mono with "⧖max") as "$"; first lia.
       iSplit; last done. iNext.
       iApply (proph_obs_impl with "Obs"). intros π [H1 H2]. rewrite Habs. trivial.
  Qed.
  
  Lemma typed_atomic_inv_destroy {𝔄 ℭ} (p : path) (ty : type 𝔄) (pred: (abstracted_syn_type 𝔄) → ~~ℭ → proph_asn → Prop) E L Il ϝ n :
    lctx_ictx_alive E L (InvCtx Il ϝ (AtomicOpen n)) →
    typed_inv_instr E L
      (InvCtx Il ϝ (AtomicOpen n))
      +[p ◁ own_ptr 0 (atomic_inv_ty ty pred)]
      (Seq Skip Skip)
      (InvCtx Il ϝ (AtomicOpen n))
      (const +[p ◁ own_ptr 0 (tracked_ty ty)]) 
      (λ post '-[(_, (N, γ, c))], λ mask π, ↑N ⊆ mask ∧ ∀ l v, pred (syn_abstract v) c π → post -[(l, v)] mask π).
  Proof.
    intros Halive. apply typed_atomic_instr_own_own_t. { trivial. } { trivial. }
    intros l [[ns γ] c] d tid post mask na_mask at_mask iκs Hm1 Hm2.
    iIntros "#LFT #TIME #PROPH #UNIQ #E L I cna_lifetimes fnincl [active #inv] #Obs #⧖ ⧗ £".
    iMod (proph_obs_sat with "PROPH Obs") as "%Sat". { set_solver. }
    iDestruct "I" as "[ctr pool]".
    iMod (external_na_inv_cancel with "inv active pool") as "[P pool]". { set_solver. }
      { destruct Sat as [π [a b]]. set_solver. }
    iMod (bi.later_exist_except_0 with "P") as (x'' d' g' tid') "[>⧖' [gho [>#Hpred >%Htids]]]".
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗ ⧖'") as "[#⧖' £2]". { set_solver. }
    iMod (change_tid_out _ _ _ _ _ _ Htids with "LFT UNIQ TIME [£2] [] gho")
      as (x' d0) "[gho [⧖2 %Habs]]".
      { iApply (lc_weaken with "£2"). unfold advance_credits. lia. }
      { iApply (persistent_time_receipt_mono with "⧖'"). lia. }
    iModIntro. iExists (d0 `max` g'), x', mask, at_mask. 
    iFrame. iFrame "#". iSplit; first by done.
    iDestruct (ty_gho_own_depth_mono with "gho") as "[$ _]". { lia. } { lia. }
    iSplit. { iCombine "⧖2 ⧖'" as "⧖max". iApply (persistent_time_receipt_mono with "⧖max"). lia. }
    iCombine "Obs Hpred" as "Obs2".
    iApply (proph_obs_impl with "Obs2").
    intros π [Ha Hpred]. apply Ha. rewrite Habs. trivial. 
  Qed.

  Local Lemma mask_lemma (na_mask at_mask X : coPset) :
      na_mask ∪ at_mask = ⊤ →
      X ⊆ na_mask ∩ at_mask →
      na_mask ∪ (at_mask ∖ X) = ⊤.
  Proof.
    move=> eq sub. apply leibniz_equiv, set_equiv_subseteq. split=>//. 
    rewrite -eq. etrans; [|by apply union_mono_l, difference_mono_l].
    move=> a /elem_of_union[?|?]; [set_solver|].
    case (decide (a ∈ na_mask)); set_solver.
  Qed.

  Lemma typed_atomic_inv_open {𝔄 ℭ} (p : path) (ty : type 𝔄) (pred: (abstracted_syn_type 𝔄) → ~~ℭ → proph_asn → Prop) E L Il ϝ n κ :
    lctx_lft_alive E L κ →
    lctx_ictx_alive E L (InvCtx Il ϝ (AtomicOpen n)) →
    typed_inv_instr E L
      (InvCtx Il ϝ (AtomicOpen n))
      +[p ◁ own_ptr 0 (tracked_ty (&shr{κ} (atomic_inv_ty ty pred)))]
      (Seq Skip Skip)
      (InvCtx Il ϝ (AtomicOpen (n+1)))
      (const +[p ◁ own_ptr 0 (tracked_ty ty * atomic_closer_ty κ ty pred)])
      (λ post '-[(_, (_, (N, γ, c)))], λ mask π, (↑N ⊆ mask) ∧ ∀ l v, pred (syn_abstract v) c π → post -[(l, (v, (N, γ, c)))] (mask ∖ ↑N) π).
  Proof.
    intros Halive HaliveI. apply typed_atomic_instr_own_own_t. { trivial. } { trivial. }
    intros l [l1 [[ns γ] c]] d tid post mask na_mask at_mask iκs Hm1 Hm2.
    iIntros "#LFT #TIME #PROPH #UNIQ #E L [ctr pool] cna_lifetimes #fincl shrgho #Obs #⧖ ⧗ £".
    iDestruct (lc_weaken (_ + _)%nat with "£") as "[£1 £2]"; first last.
    {
    destruct d as [|d]; first by done.
    iDestruct "shrgho" as "[_ [#KShr _]]".
    iDestruct (ty_shr_default_to_guard (atomic_inv_ty ty pred) with "KShr") as "#KguardsGho"; [done|].
    iDestruct (Halive with "L E") as "#LguardsK".
    iDestruct (guards_transitive_right with "LguardsK KguardsGho") as "LguardsGho".
    
    leaf_open_laters "LguardsGho" with "L" as "Open". { set_solver. }
    iMod (lc_fupd_elim_laterN with "£1 Open") as "Open".
    iMod "Open" as "[[a #inv] back]".
    iMod ("back" with "[a]") as "L". { iFrame. iFrame "#". }
    
    leaf_hyp "KguardsGho" rhs to (Active γ) as "#KguardsActive".
      { leaf_by_sep. iIntros "(? & ?)". iFrame. iIntros. done. }
    iDestruct (guards_transitive_right with "LguardsK KguardsActive") as "LguardsActive".
    
    iMod (proph_obs_sat with "PROPH Obs") as "%Sat". { set_solver. }
    
    iMod (external_na_inv_acc_strong_later _ _ ns _ _ _ _ at_mask with "£2 inv LguardsActive L pool") as "(pool & L & P & closer)". 
      { destruct Sat as [π [a b]]; trivial. }
      { set_solver. }
      
    iMod (bi.later_exist_except_0 with "P") as (x'' d' g' tid') "[>⧖' [gho [>#Hpred >%Htids]]]".
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗ ⧖'") as "[#⧖' £2]". { set_solver. }
    
    iMod (change_tid_out _ _ d' _ _ _ Htids with "LFT UNIQ TIME [£2] [] gho") as (x' d'0) "[gho [⧖2 %Habs]]".
      { iApply (lc_weaken with "£2"). unfold advance_credits. lia. }
      { iApply (persistent_time_receipt_mono with "⧖'"). lia. }
      iDestruct (atomic_lock_ctr_inc _ _ _ (↑ns) with "ctr") as "[ctr handle]".
      { pose proof (fresh_inv_name ∅ ns) as [? [??]]. set_solver. }
    iModIntro. iExists (d'0 `max` g'), (x', (ns, γ, c)), (mask ∖ ↑ns), (at_mask ∖ ↑ns). iFrame.
    iSplit. { iPureIntro. split; last by set_solver. apply mask_lemma; set_solver. }
    iSplit. {
      iCombine "⧖' ⧖2" as "⧖max".
      iApply (persistent_time_receipt_mono with "⧖max"). lia. }
    iDestruct (ty_gho_own_depth_mono with "gho") as "[$ _]". { lia. } { lia. }
    iCombine "Obs Hpred" as "Obs2".
    iApply (proph_obs_impl with "Obs2").
    intros π [Ha Hpred]. apply Ha. rewrite Habs. trivial.
    }
    lia.
  Qed.
 
  Lemma typed_atomic_inv_close {𝔄 ℭ} (p1 p2 : path) (ty : type 𝔄) (pred: (abstracted_syn_type 𝔄) → ~~ℭ → proph_asn → Prop) E L Il ϝ n κ :
    lctx_ictx_alive E L (InvCtx Il ϝ (AtomicOpen (n+1))) →
    typed_inv_instr E L (InvCtx Il ϝ (AtomicOpen (n+1)))
      +[p2 ◁ own_ptr 0 (tracked_ty (ty));
        p1 ◁ own_ptr 0 (tracked_ty (atomic_closer_ty κ ty pred))
      ]
      (Seq Skip Skip)
      (InvCtx Il ϝ (AtomicOpen n))
      (const +[])
      (λ post '-[(_, v); (_, (N, γ, c))], λ mask π,
        pred (syn_abstract v) c π ∧ post -[] (mask ∪ ↑N) π
      ).
  Proof.
    intros IAlv. apply typed_atomic_instr_own2_emp.
    intros l1 l2 v [[ns γ] c] d tid post mask na_mask at_mask iκs Hm1 Hm2.
    iIntros "#LFT #TIME #PROPH #UNIQ E L [ctr pool] cna_lifetimes #fincl gho1 gho2 #Obs #⧖ £".
    iMod (proph_obs_sat with "PROPH Obs") as "%Sat". { set_solver. }
    iDestruct "gho2" as "[handle closer]".
    
    iDestruct (lctx_ictx_alive_all_guards _ _ _ _ _ _ IAlv with "L E fincl") as "#AllGuards".
    iMod (change_tid_in ty _ d with "LFT UNIQ TIME £ [] gho1 AllGuards L cna_lifetimes")
     as (tid' x' d') "[%TidsEq [gho' [#⧖' [%Habs [L cna_lifetimes]]]]]".
    { iApply (persistent_time_receipt_mono with "⧖"). lia. }
    
    iMod ("closer" with "[gho' pool]") as "pool". {
      iFrame. iNext. iLeft. iExists x', d', (S d), tid'. iFrame.
      iSplit. {
        iCombine "⧖ ⧖'" as "⧖max".
        iApply (persistent_time_receipt_mono with "⧖max"). lia.
      }
      iSplit. { 
        iApply (proph_obs_impl with "Obs"). intros π [a b]. by rewrite Habs.
      }
      iPureIntro. apply TidsEq.
    }
    iDestruct (atomic_lock_ctr_handle_disjoint with "ctr handle") as "%disj".
    iDestruct (atomic_lock_ctr_dec _ (n) with "ctr handle") as "ctr". 
    iModIntro.
    iExists (mask ∪ ↑ns), (at_mask ∪ ↑ns). iFrame.
    iSplit. { iPureIntro. split; set_solver. }
    iApply (proph_obs_impl with "Obs"). intros π Ha. apply Ha.
  Qed.
End atomic_invariants.

Global Hint Resolve atomic_inv_ty_resolve : lrust_typing.
