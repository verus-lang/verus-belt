From lrust.typing Require Export type.
From lrust.typing Require Import type_context programs programs_util own.
From guarding Require Import guard tactics.
From guarding.lib Require Import cancellable.
From lrust.lifetime Require Import lifetime_full.
Set Default Proof Using "Type".

Section programs_util_own.
  Context `{!typeG Σ}. 
  
  Lemma typed_instr_of_skip_own2_own
    {𝔄1 𝔄2 𝔅} (E: elctx) (L: llctx) (I: invctx)
    (p1 : path) (ty1 : type 𝔄1)
    (p2 : path) (ty2 : type 𝔄2)
    (tyret: type 𝔅)
    (tr: predl_trans (at_locₛ 𝔄1 :: [at_locₛ 𝔄2]) [at_locₛ 𝔅]) :
    (ty_size ty1 = 0) →
    (ty_size tyret = 0) →
    (∀ l1 l2 x1 x2 d tid post mask iκs, ⊢ (llft_ctx -∗ time_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
      llctx_interp L -∗
      invctx_interp tid mask iκs I -∗
      ty_gho_own ty1 x1 d (S d) tid -∗
      ty_gho_own ty2 x2 d (S d) tid -∗
      ⟨π, tr post -[(l1, x1); (l2, x2)] mask π⟩ -∗
      ⧖(S (S (S d))) -∗
      £(d+1) -∗
      |={⊤}=>
      ∃ xret , llctx_interp L ∗ invctx_interp tid mask iκs I ∗  ▷ ty_gho_own tyret xret (S d) (S (S d)) tid ∗
          ⟨π, post -[(l2, xret)] mask π⟩
    )%I)
    → typed_inv_instr E L I
        +[p1 ◁ own_ptr 0 ty1; p2 ◁ own_ptr 0 ty2]
       (Seq Skip Skip) I
       (const +[p2 ◁ own_ptr 0 tyret])
       tr.
  Proof.
    intros Hsize0 Hsize0' Ha. apply typed2_inv_instr_of_skip.
    iIntros ([l1 x1] [l2 x2] v1 v2 d tid post mask iκs) "#LFT #TIME #PROPH #UNIQ #E L I %He1 Own1 %He2 Own2 Obs #⧖ ⧗big ⧗ £x".
    iDestruct "Own1" as "[Gho1 %Phys1]".
    iDestruct "Own2" as "[Gho2 %Phys2]".
    destruct d as [|d]; first by done.
    iDestruct "Gho1" as "[Pt1 [Free1 Gho1]]".
    iDestruct "Gho2" as "[Pt2 [Free2 Gho2]]".
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗ ⧖") as "[#⧖S £]". { set_solver. }
    iDestruct (lc_weaken (_ + _)%nat with "£") as "[£1 £2]"; last first. {
    iCombine "Gho1 Gho2" as "Gho".
    iMod (lc_fupd_elim_later with "£1 Gho") as "[Gho1 Gho2]". 
    iMod (Ha l1 l2 x1 x2 d tid post mask iκs with "LFT TIME PROPH UNIQ E L I Gho1 Gho2 Obs [] £2") as "X". { iApply (persistent_time_receipt_mono with "⧖S"). lia. }
    iDestruct "X" as (xret) "[L [I [GhoRet Obs]]]".
    iModIntro. iExists -[(l2, xret)]. iFrame.
    iSplit; last by done. iExists v2. iExists (S (S d)).
    iFrame "%". iSplit. { iApply (persistent_time_receipt_mono with "⧖S"). lia. }
    iFrame.
    rewrite Hsize0. rewrite Hsize0'. iFrame.
    assert (ty_phys tyret (l2, xret).2 tid = []) as Hlen. {
      simpl. have Hl := ty_size_eq tyret xret tid. destruct (ty_phys tyret xret tid); try done.
      simpl in Hl. lia.
    }
    rewrite Hlen. rewrite heap_mapsto_fancy_vec_nil. done.
    } unfold advance_credits; lia.
  Qed.
  
  Lemma typed_instr_of_skip_own_own_t
    {𝔄1 𝔅} (E: elctx) (L: llctx) (I: invctx)
    (p1 : path) (ty1 : type 𝔄1)
    (tyret: type 𝔅)
    (tr: predl_trans ([at_locₛ 𝔄1]) [at_locₛ 𝔅]) :
    (ty_size ty1 = 0) →
    (ty_size tyret = 0) →
    (∀ l1 x1 d tid iκs post mask, ⊢ (llft_ctx -∗ time_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
      llctx_interp L -∗ invctx_interp tid mask iκs I -∗
      ty_gho_own ty1 x1 d (S d) tid -∗
      ⟨π, tr post -[(l1, x1)] mask π⟩ -∗
      ⧖(S (S d)) -∗
      ⧗1 -∗
      |={⊤}=>
      ∃ d' xret , ⧖(S d') ∗ llctx_interp L ∗ invctx_interp tid mask iκs I ∗ ▷ ty_gho_own tyret xret (d') (S d') tid ∗
          ⟨π, post -[(l1, xret)] mask π⟩
    )%I)
    → typed_instr E L I
        +[p1 ◁ own_ptr 0 ty1]
       (Seq Skip Skip)
       (const +[p1 ◁ own_ptr 0 tyret])
       tr.
  Proof.
    intros Hsize0 Hsize0' Ha. apply typed_instr_of_skip.
    iIntros ([l1 x1] v1 d tid post mask iκs) "#LFT #TIME #PROPH #UNIQ #E L I %He1 Own1 Obs #⧖ ⧗ ⧗' £".
    iDestruct "Own1" as "[Gho1 %Phys1]".
    destruct d as [|d]; first by done.
    iDestruct "Gho1" as "[Pt1 [Free1 Gho1]]".
    iMod (lc_fupd_elim_later with "[£] Gho1") as "Gho1". { iApply (lc_weaken with "£"). unfold advance_credits. lia. }
    iMod (Ha l1 x1 d tid iκs post mask with "LFT TIME PROPH UNIQ E L I Gho1 Obs [] ⧗") as "X". { iApply (persistent_time_receipt_mono with "⧖"). lia. }
    iDestruct "X" as (d' xret) "[⧖' [L [I [GhoRet Obs]]]]".
    iModIntro. iExists -[(l1, xret)]. iFrame.
    iExists v1. iFrame "%". iFrame.
    rewrite Hsize0. rewrite Hsize0'. iFrame.
    assert (ty_phys tyret (l1, xret).2 tid = []) as Hlen. {
      simpl. have Hl := ty_size_eq tyret xret tid. destruct (ty_phys tyret xret tid); try done.
      simpl in Hl. lia.
    }
    rewrite Hlen. rewrite heap_mapsto_fancy_vec_nil. done.
  Qed.
  
  Lemma typed_inv_instr_of_skip_own_own_t
    {𝔄1 𝔅} (E: elctx) (L: llctx) (I: invctx) (I': invctx)
    (p1 : path) (ty1 : type 𝔄1)
    (tyret: type 𝔅)
    (tr: predl_trans ([at_locₛ 𝔄1]) [at_locₛ 𝔅]) :
    (ty_size ty1 = 0) →
    (ty_size tyret = 0) →
    (∀ l1 x1 d tid iκs post mask, ⊢ (llft_ctx -∗ time_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
      llctx_interp L -∗ invctx_interp tid mask iκs I -∗
      ty_gho_own ty1 x1 d (S d) tid -∗
      ⟨π, tr post -[(l1, x1)] mask π⟩ -∗
      ⧖(S (S d)) -∗
      ⧗1 -∗
      £(2*d + 5) -∗
      |={⊤}=>
      ∃ d' xret mask' , ⧖(S d') ∗ llctx_interp L ∗ invctx_interp tid mask' iκs I' ∗ ▷ ty_gho_own tyret xret (d') (S d') tid ∗
          ⟨π, post -[(l1, xret)] mask' π⟩
    )%I)
    → typed_inv_instr E L I
        +[p1 ◁ own_ptr 0 ty1]
       (Seq Skip Skip)
       I' (const +[p1 ◁ own_ptr 0 tyret])
       tr.
  Proof.
    intros Hsize0 Hsize0' Ha. apply typed_inv_instr_of_skip.
    iIntros ([l1 x1] v1 d tid post mask iκs) "#LFT #TIME #PROPH #UNIQ #E L I %He1 Own1 Obs #⧖ ⧗ £".
    iDestruct "Own1" as "[Gho1 %Phys1]".
    destruct d as [|d]; first by done.
    iDestruct "Gho1" as "[Pt1 [Free1 Gho1]]".
    iDestruct (lc_weaken (_ + _)%nat with "£") as "[£1 £2]"; first last.
    {
    iMod (lc_fupd_elim_later with "£1 Gho1") as "Gho1". 
    iMod (Ha l1 x1 d tid iκs post mask with "LFT TIME PROPH UNIQ E L I Gho1 Obs [] ⧗ £2") as "X". { iApply (persistent_time_receipt_mono with "⧖"). lia. }
    iDestruct "X" as (d' xret mask') "[⧖' [L [I [GhoRet Obs]]]]".
    iModIntro. iExists -[(l1, xret)]. iFrame.
    iExists v1. iFrame "%". iFrame.
    rewrite Hsize0. rewrite Hsize0'. iFrame.
    assert (ty_phys tyret (l1, xret).2 tid = []) as Hlen. {
      simpl. have Hl := ty_size_eq tyret xret tid. destruct (ty_phys tyret xret tid); try done.
      simpl in Hl. lia.
    }
    rewrite Hlen. rewrite heap_mapsto_fancy_vec_nil. done.
    }
    unfold advance_credits. lia.
  Qed.
  
  Lemma typed_inv_instr_of_skip_own2_emp
    {𝔄1 𝔄2} (E: elctx) (L: llctx) (I I': invctx)
    (p1 : path) (ty1 : type 𝔄1)
    (p2 : path) (ty2 : type 𝔄2)
    (tr: predl_trans (at_locₛ 𝔄1 :: [at_locₛ 𝔄2]) []) :
    (∀ l1 l2 x1 x2 d tid iκs post mask, ⊢ (llft_ctx -∗ time_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
      llctx_interp L -∗ invctx_interp tid mask iκs I -∗
      ty_gho_own ty1 x1 d (S d) tid -∗
      ty_gho_own ty2 x2 d (S d) tid -∗
      ⟨π, tr post -[(l1, x1); (l2, x2)] mask π⟩ -∗
      ⧖(S (S (S d))) -∗
      ⧗(S d) -∗
      £(S d) -∗
      |={⊤}=>
      ∃ mask' , llctx_interp L ∗ invctx_interp tid mask' iκs I' ∗
          ⟨π, post -[] mask' π⟩
    )%I)
    → typed_inv_instr E L I
        +[p1 ◁ own_ptr 0 ty1; p2 ◁ own_ptr 0 ty2]
       (Seq Skip Skip) I'
       (const +[])
       tr.
  Proof.
    intros Ha. apply typed2_inv_instr_of_skip.
    iIntros ([l1 x1] [l2 x2] v1 v2 d tid post mask iκs) "#LFT #TIME #PROPH #UNIQ #E L I %He1 Own1 %He2 Own2 Obs #⧖ ⧗big ⧗ £1".
    iDestruct "Own1" as "[Gho1 %Phys1]".
    iDestruct "Own2" as "[Gho2 %Phys2]".
    destruct d as [|d]; first by done.
    iDestruct "Gho1" as "[Pt1 [Free1 Gho1]]".
    iDestruct "Gho2" as "[Pt2 [Free2 Gho2]]".
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗ ⧖") as "[#⧖S £]". { set_solver. }
    iCombine "Gho1 Gho2" as "Gho".
    iMod (lc_fupd_elim_later with "[£] Gho") as "[Gho1 Gho2]". { iApply (lc_weaken with "£"). unfold advance_credits. lia. }
    iMod (Ha l1 l2 x1 x2 d tid iκs post mask with "LFT TIME PROPH UNIQ E L I Gho1 Gho2 Obs [] ⧗big £1") as "X". { iApply (persistent_time_receipt_mono with "⧖S"). lia. }
    iDestruct "X" as (mask') "[L [I' Obs]]".
    iModIntro. iExists -[]. iFrame.
  Qed.
End programs_util_own.
