From lrust.typing Require Export type.
From lrust.typing Require Import programs.
From lrust.typing Require Import own.

Set Default Proof Using "Type".

Section ghost.
  Context `{!typeG Σ}.

  Program Definition ghost_ty {𝔄} (ty: type 𝔄) : type (ghostₛ 𝔄) := @ty_of_st _ _ (ghostₛ 𝔄)
    ({|
      st_size := 0;
      st_lfts := ty.(ty_lfts);
      st_E := [];
      st_gho x d g tid := True%I;
      st_phys x tid := [];
    |}%I : simple_type (ghostₛ 𝔄)).
  Next Obligation. move=> *. trivial. Qed.
  Next Obligation. move=> *. trivial. Qed.
  Next Obligation. move=> *. trivial. Qed.
  Next Obligation. intros. iIntros. done. Qed.
  Next Obligation. intros 𝔄 ty κ x n d g tid ξ R Hin. exfalso. simpl in Hin. set_solver. Qed.
  Next Obligation. done. Qed.
  
  Global Instance tracked_ne {𝔄} : NonExpansive (@ghost_ty 𝔄).
  Proof. move=> ????. apply ty_of_st_ne. solve_ne_type. Qed.

  Global Instance ghost_send {𝔄} (ty : type 𝔄) : Send (ghost_ty ty).
  Proof.
    intros. split; trivial. iIntros. iApply step_fupdN_intro; first done. iNext.
    iExists x, 0%nat. iModIntro. iFrame. simpl.
    replace (d0 + 0)%nat with d0 by lia. iFrame "#". done.
  Qed.
  
  Global Instance ghost_sync {𝔄} (ty : type 𝔄) : Sync (ghost_ty ty).
  Proof. apply sync_default; [done|]. split; trivial. split; iSplit; done. Qed.
  
  Global Instance ghost_copy {𝔄} (ty : type 𝔄) : Copy (ghost_ty ty).
  Proof.
    split; [typeclasses eauto|done|]. intros. by apply copy_shr_default.
  Qed.

  Lemma ghost_resolve {𝔄} (ty: type 𝔄) E L : resolve E L (ghost_ty ty) (const (const True)).
  Proof. apply resolve_just. Qed.
  
  Lemma ghost_constant {𝔄} E L I (ty : type 𝔄) (c: ~~𝔄) :
    typed_instr E L I
      +[] (new [ #0 ]%E)
      (λ q, +[q ◁ own_ptr 0 (ghost_ty ty)])
      (λ post '-[], λ mask π, ∀ l, post -[(l, c)] mask π).
  Proof.
    move => tid postπ mask iκs [].
    iIntros "LFT TIME #PROPH UNIQ E L $ TY #Obs" => /=.
    iMod (persistent_time_receipt_0) as "⧖".
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|]. iIntros "_ ⧖".
    iApply wp_new=>//. iIntros "!>" (l) "(† & ↦)". iExists -[(l, c)]. iFrame. iSplitL.
    - iExists (#l). iSplit; first done. iSplit; last done.
      unfold own_ptr, ty_gho_own. rewrite !freeable_util.freeable_sz_full. iFrame. done.
    - iApply (proph_obs_impl with "Obs"). done.
  Qed.
  
  Lemma ghost_snapshot {𝔄} E L I p (ty : type 𝔄) :
    typed_instr E L I
      +[p ◁ ty]
      (new [ #0 ]%E)
      (λ q, +[p ◁ ty; q ◁ own_ptr 0 (ghost_ty ty)])
      (λ post '-[x], λ mask π, ∀ l, post -[x; (l, x)] mask π).
  Proof.
    move => tid postπ mask iκs [x []].
    iIntros "LFT TIME #PROPH UNIQ E L $ [T TY] #Obs" => /=.
    iMod (persistent_time_receipt_0) as "⧖".
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|]. iIntros "_ ⧖".
    iApply wp_new=>//. iIntros "!>" (l) "(† & ↦)". iExists -[x; (l, x)]. iFrame "T".
    iFrame. iSplitL.
    - iExists (#l). iSplit; first done. iSplit; last done.
      unfold own_ptr, ty_gho_own. rewrite !freeable_util.freeable_sz_full. iFrame. done.
    - iApply (proph_obs_impl with "Obs"). done.
  Qed.
  
  Lemma ghost_compute {𝔄 𝔅 ℭ} E L I p1 p2 (ty1 : type 𝔄) (ty2 : type 𝔅) (ty: type ℭ)
      (f : (~~𝔄) → (~~𝔅) → (~~ℭ)) :
    typed_instr E L I
      +[p1 ◁ ty1; p2 ◁ ty2]
      (new [ #0 ]%E)
      (λ q, +[p1 ◁ ty1; p2 ◁ ty2; q ◁ own_ptr 0 (ghost_ty ty)])
      (λ post '-[x; y], λ mask π, ∀ l, post -[x; y; (l, f x y)] mask π).
  Proof.
    move => tid postπ mask iκs [x [y []]].
    iIntros "LFT TIME #PROPH UNIQ E L $ [T1 [T2 TY]] #Obs" => /=.
    iMod (persistent_time_receipt_0) as "⧖".
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|]. iIntros "_ ⧖".
    iApply wp_new=>//. iIntros "!>" (l) "(† & ↦)". iExists -[x; y; (l, f x y)].
    iFrame "T1 T2". iFrame. iSplitL.
    - iExists (#l). iSplit; first done. iSplit; last done.
      unfold own_ptr, ty_gho_own. rewrite !freeable_util.freeable_sz_full. iFrame. done.
    - iApply (proph_obs_impl with "Obs"). done.
  Qed.
End ghost.

Global Hint Resolve ghost_resolve : lrust_typing.
