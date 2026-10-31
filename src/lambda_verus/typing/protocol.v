From iris.proofmode Require Import proofmode.
From iris.algebra Require Import gmap.
From lrust.typing Require Import lft_contexts.
From lrust.typing Require Import type programs ghost.
From guarding Require Import guard tactics guard_later_pers own_and.
From lrust.typing Require Import ra proph_protocol.
From lrust.lifetime Require Import lifetime_full.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section StorageProtocol.

  Context `{!typeG Σ}.
    
  (** The ghost type of storable values, used to put values of a real type [ty] into a
      storage protocol. A value is made storable by sharing it up front, at a fresh
      lifetime [α] (which is part of the storable value), with [ty_share]. The storable
      value holds the token of [α] (to keep the sharing period alive), the resulting
      persistent sharing predicate at [α ⊓ ty_lft ty] (for shared access, see
      [storable_borrow]) and the inheritance of the borrow (to get the ownership
      predicate back after ending [α], see [storable_into_inner]). *)
  Program Definition storable_ty {𝔄} (ty: type 𝔄) : ghost_type (storableₛ 𝔄) := {|
    gt_gho x tid := match x with
        (x0, (d, g), α) =>
          ⌜α ≠ llft_empty⌝ ∗ @[α] ∗ ty.(ty_shr) (α ⊓ ty_lft ty) x0 d g tid ∗
          ([†α] ={↑Nllft}=∗ ▷ ty.(ty_gho_own) x0 d g tid) ∗
          ⧖(S d `max` g) ∗ ty.(ty_gho_pers) x0 d g tid
    end
  |}%I.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.

  Local Lemma storable_ty_gho_change_tid {𝔄} (ty : type 𝔄) tid tid' x :
    Sync ty → (storable_ty ty).(gt_gho) x tid ⊣⊢ (storable_ty ty).(gt_gho) x tid'.
  Proof.
    intros Hsync. destruct x as [[x0 [d0 g0]] α].
    destruct (Hsync tid tid' x0 d0 g0) as [_ [Hgho [Hpers Hshr]]]. simpl.
    by rewrite Hgho Hpers Hshr.
  Qed.

  (* this shouldn't really require Sync, but we would need another layer of step-indexing
    accounting to fix it (similar to how local_inv works). At least in this case,
    it doesn't matter, since the Storage Protocol requires Sync anyway. *)
  Global Instance storable_ty_send {𝔄} (ty : type 𝔄) : Send ty → Sync ty → Send (storable_ty ty).
  Proof. intros Hsend. intros Hsync. split; trivial.
    iIntros (tid tid' x d g G H κs d1 Hineq TG TH) "LFT UNIQ TIME Hg H Gg G gho ⧖".
    iDestruct (storable_ty_gho_change_tid ty tid tid' x with "gho") as "gho".
    iApply step_fupdN_intro; first done. iNext. iModIntro.
    iExists x, 0. iFrame. replace (d1 + 0) with d1 by lia. iFrame.
    done.
  Qed.

  Global Instance storable_ty_sync {𝔄} (ty : type 𝔄) : Sync ty → Sync (storable_ty ty).
  Proof. intros Hsync. apply sync_default; [done|]. split; trivial.
    split; last trivial. by apply storable_ty_gho_change_tid.
  Qed.

  Context {𝔄 ℭ : syn_type}.
  Context {K : Type} `{Countable K}.
  (** The storage protocol, given as a Verus-style [VerusSP] over protocol elements [~~𝔄]
      storing maps from [K] to ghost values [~~ℭ]. *)
  Context `{SP: !VerusSP K (~~ℭ) (~~𝔄)}.
  Context `{G𝔄: !inG Σ (authUR (vra_carUR (vsp_vra K (~~ℭ) (~~𝔄))))}.
  Hypothesis (𝔄_const  : ∀ (x : ~~𝔄) π1 π2 , @vπ 𝔄 x π1 = @vπ 𝔄 x π2).
  Variable (tyC : ghost_type ℭ).

  Set Printing Coercions.
    Program Definition storage_resource_ty : type (ghostₛ (positiveₛ * 𝔄)) :=
    ty_of_gt ({|
          gt_gho v tid :=
            let '(γ, p) := v in
            ⌜ @subseteq coPset _ {[ γ ]} (↑NllftG) ⌝ ∗
            sp_sto γ (λ _ c, tyC.(gt_gho) c tid) ∗ sp_own γ p;
        |}%I : ghost_type (ghostₛ (positiveₛ * 𝔄))).
      Next Obligation.
        move => v.
        unfold indep_interp_of_syn_type in v.
        fold indep_interp_of_syn_type in v.
        destruct v as [γ v].
        move => π1 π2.
        specialize (𝔄_const v π1 π2).
        simpl.
        by f_equal.
      Qed.
      Next Obligation. done. Qed.
      Next Obligation. done. Qed.
      Next Obligation. done. Qed.

  Lemma storage_ty_sync : Send tyC → Sync tyC → Sync storage_resource_ty.
  Proof.
    intros Hsend Hsync. apply sync_default; [done|]. split; first by done. split; last by done.
    simpl. unfold gt_gho. destruct x as [γ p].
    have Hg : ∀ c, tyC.(gt_gho) c tid ⊣⊢ tyC.(gt_gho) c tid'.
    { intros c. destruct (Hsync tid tid' c 0 0) as [H1 [H2 [H3 _]]]. apply H2. }
    rewrite /sp_sto /sp_inv_body. by setoid_rewrite Hg.
  Qed.

  Lemma storage_ty_send : Send tyC → Sync tyC → Send storage_resource_ty.
  Proof.
    intros Hsend. intros Hsync. split; trivial.
    iIntros (tid tid' x d g G H' κs d1 Hineq TG TH) "LFT UNIQ TIME Hg H Gg G gho ⧖".
    have H1 := storage_ty_sync Hsend Hsync.
    destruct (H1 tid tid' x d g) as [H2 [H3 [H4 _]]]. rewrite H3. iIntros.
    iIntros. iApply step_fupdN_intro; first done. iNext. iModIntro.
    iExists x, 0. iFrame. replace (d1 + 0) with d1 by lia. iFrame.
    done.
  Qed.
End StorageProtocol.
