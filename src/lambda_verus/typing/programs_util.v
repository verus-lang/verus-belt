From iris.proofmode Require Import environments.
From lrust.lang Require Import proofmode memcpy.
From lrust.typing Require Export type lft_contexts type_context cont_context programs.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Section programs_util.
  Context `{!typeG Σ}.
  
  Lemma typed_instr_of_skip
    {𝔄 𝔅l} (E: elctx) (L: llctx) (I: invctx)
    (p : path) (ty : type 𝔄)
    (T': tctx 𝔅l) (tr: predl_trans [𝔄] 𝔅l) :
    (∀ x v d tid post mask iκs, ⊢ (llft_ctx -∗ time_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
      llctx_interp L -∗ invctx_interp tid mask iκs I -∗
      ⌜eval_path p = Some v⌝ -∗ ty_own ty x d d tid [FVal v] -∗
      ⟨π, tr post -[x] mask π⟩ -∗
      ⧖(S d) -∗
      ⧗1 -∗ ⧗1 -∗ £(advance_credits d) -∗ |={⊤}=>
      ∃ xl' , llctx_interp L ∗ invctx_interp tid mask iκs I ∗ tctx_interp tid T' xl' ∗ ⟨π, post xl' mask π⟩
    )%I)
    → typed_instr E L I +[p ◁ ty] (Seq Skip Skip) (const T') tr.
  Proof.
    intros Hvs tid post mask iκs xl. destruct xl as [x []].
    iIntros "#CTX #TIME #PROPH #UNIQ #E L I [T _] Obs".
    iDestruct "T" as (v d) "(p & #⧖1 & own)".
    wp_bind Skip.
    iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME ⧖1"). { set_solver. } 
    iIntros "£ #⧖". wp_let. iModIntro. wp_let.
    iApply wp_fupd.
    iApply (wp_cumulative_time_receipt2 with "TIME"). { set_solver. } 
    iIntros "⧗". replace 2 with (1 + 1)%nat by done.
    iDestruct (cumulative_time_receipt_sep with "⧗") as "[⧗1 ⧗2]".
    wp_let.
    iMod (Hvs x v d tid post with "CTX TIME PROPH UNIQ E L I p own Obs ⧖ ⧗1 ⧗2 £") as (xl') "(? & ? & ? & ?)".
    iModIntro. iFrame.
  Qed.
  
  Lemma typed_inv_instr_of_skip
    {𝔄 𝔅l} (E: elctx) (L: llctx) (I: invctx) (I': invctx)
    (p : path) (ty : type 𝔄)
    (T': tctx 𝔅l) (tr: predl_trans [𝔄] 𝔅l) :
    (∀ x v d tid post mask iκs, ⊢ (llft_ctx -∗ time_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
      llctx_interp L -∗ invctx_interp tid mask iκs I -∗
      ⌜eval_path p = Some v⌝ -∗ ty_own ty x d d tid [FVal v] -∗
      ⟨π, tr post -[x] mask π⟩ -∗
      ⧖(S d) -∗
      ⧗1 -∗ £(advance_credits d) -∗ |={⊤}=>
      ∃ xl' mask', llctx_interp L ∗ invctx_interp tid mask' iκs I' ∗ tctx_interp tid T' xl' ∗ ⟨π, post xl' mask' π⟩
    )%I)
    → typed_inv_instr E L I +[p ◁ ty] (Seq Skip Skip) I' (const T') tr.
  Proof.
    intros Hvs tid post mask iκs xl. destruct xl as [x []].
    iIntros "#CTX #TIME #PROPH #UNIQ #E L I [T _] Obs".
    iDestruct "T" as (v d) "(p & #⧖1 & own)".
    wp_bind Skip.
    iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME ⧖1"). { set_solver. } 
    iIntros "£ #⧖". wp_let. iModIntro. wp_let.
    iApply wp_fupd.
    iApply (wp_cumulative_time_receipt1 with "TIME"). { set_solver. } 
    iIntros "⧗".
    wp_let.
    iMod (Hvs x v d tid post with "CTX TIME PROPH UNIQ E L I p own Obs ⧖ ⧗ £") as (xl' mask') "(? & ? & ? & ?)".
    iModIntro. iFrame.
  Qed.
   
  Lemma typed2_instr_of_skip
    {𝔄1 𝔄2 𝔅l} (E: elctx) (L: llctx) (I: invctx)
    (p1 : path) (ty1 : type 𝔄1)
    (p2 : path) (ty2 : type 𝔄2)
    (T': tctx 𝔅l) (tr: predl_trans (𝔄1 :: [𝔄2]) 𝔅l) :
    (∀ x1 x2 v1 v2 d tid post mask, ⊢ (llft_ctx -∗ time_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
      llctx_interp L -∗
      ⌜eval_path p1 = Some v1⌝ -∗ ty_own ty1 x1 d d tid [FVal v1] -∗
      ⌜eval_path p2 = Some v2⌝ -∗ ty_own ty2 x2 d d tid [FVal v2] -∗
      ⟨π, tr post -[x1; x2] mask π⟩ -∗
      ⧖(S d) -∗
      ⧗1 -∗ |={⊤}=>
      ∃ xl' , llctx_interp L ∗ tctx_interp tid T' xl' ∗ ⟨π, post xl' mask π⟩
    )%I)
    → typed_instr E L I +[p1 ◁ ty1; p2 ◁ ty2] (Seq Skip Skip) (const T') tr.
  Proof.
    intros Hvs tid post mask iκs xl. destruct xl as [x1 [x2 []]].
    iIntros "#CTX #TIME #PROPH #UNIQ #E L I [T1 [T2 _]] Obs".
    iDestruct "T1" as (v1 d1) "(p1 & #⧖1 & own1)".
    iDestruct "T2" as (v2 d2) "(p2 & #⧖2 & own2)".
    iCombine "⧖1 ⧖2" as "⧖".
    wp_bind Skip. iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME ⧖"). { set_solver. } 
    iIntros "£ #S⧖". wp_let. iModIntro. wp_let.
    iApply wp_fupd.
    iApply (wp_cumulative_time_receipt1 with "TIME"). { set_solver. } 
    iIntros "⧗".
    wp_let.
    iMod (Hvs x1 x2 v1 v2 (d1 `max` d2) tid post with "CTX TIME PROPH UNIQ E L p1 [own1] p2 [own2] Obs S⧖ ⧗") as "J".
     { iDestruct "own1" as "[gho phys]". iFrame.
       iDestruct (ty_gho_own_depth_mono with "gho") as "[gho _]"; last by iFrame "gho".
       { lia. } { lia. }
     }
     { iDestruct "own2" as "[gho phys]". iFrame.
       iDestruct (ty_gho_own_depth_mono with "gho") as "[gho _]"; last by iFrame "gho".
       { lia. } { lia. }
     }
     iDestruct "J" as (xl') "(? & ? & ?)". iModIntro. iFrame.
  Qed.
  
  Lemma typed2_inv_instr_of_skip
    {𝔄1 𝔄2 𝔅l} (E: elctx) (L: llctx) (I I': invctx)
    (p1 : path) (ty1 : type 𝔄1)
    (p2 : path) (ty2 : type 𝔄2)
    (T': tctx 𝔅l) (tr: predl_trans (𝔄1 :: [𝔄2]) 𝔅l) :
    (∀ x1 x2 v1 v2 d tid post mask iκs, ⊢ (llft_ctx -∗ time_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
      llctx_interp L -∗ invctx_interp tid mask iκs I -∗
      ⌜eval_path p1 = Some v1⌝ -∗ ty_own ty1 x1 d d tid [FVal v1] -∗
      ⌜eval_path p2 = Some v2⌝ -∗ ty_own ty2 x2 d d tid [FVal v2] -∗
      ⟨π, tr post -[x1; x2] mask π⟩ -∗
      ⧖(S d) -∗
      ⧗d -∗
      ⧗1 -∗
      £d -∗
      |={⊤}=>
      ∃ xl' mask' , llctx_interp L ∗ invctx_interp tid mask' iκs I' ∗ tctx_interp tid T' xl' ∗ ⟨π, post xl' mask' π⟩
    )%I)
    → typed_inv_instr E L I +[p1 ◁ ty1; p2 ◁ ty2] (Seq Skip Skip) I' (const T') tr.
  Proof.
    intros Hvs tid post mask iκs xl. destruct xl as [x1 [x2 []]].
    iIntros "#CTX #TIME #PROPH #UNIQ #E L I [T1 [T2 _]] Obs".
    iDestruct "T1" as (v1 d1) "(p1 & #⧖1 & own1)".
    iDestruct "T2" as (v2 d2) "(p2 & #⧖2 & own2)".
    iCombine "⧖1 ⧖2" as "⧖".
    wp_bind Skip. iApply wp_fupd.
    iApply (wp_cumulative_time_receipt2 with "TIME"). { set_solver. } 
    iIntros "⧗". wp_let. iModIntro. wp_let.
    replace 2 with (1 + 1)%nat by done.
    iDestruct (cumulative_time_receipt_sep with "⧗") as "[⧗1 ⧗2]".
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗1 ⧖") as "[#S⧖ £]"; first by set_solver.
    iDestruct (lc_weaken with "£") as "£"; last first. {
    iApply wp_fupd.
    replace (d1 `max` d2 + 1) with (S (d1 `max` d2)) by lia.
    iApply (wp_cumulative_time_receipt_linear with "TIME S⧖"). { set_solver. } 
    iIntros "⧗big".
    wp_let.
    replace (S (S (S (d1 `max` d2)))) with (d1 `max` d2 + 3)%nat by lia.
    iDestruct "⧗big" as "[⧗big ⧗3]".
    iMod (Hvs x1 x2 v1 v2 (d1 `max` d2) tid post with "CTX TIME PROPH UNIQ E L I p1 [own1] p2 [own2] Obs S⧖ ⧗big ⧗2 £") as "J".
     { iDestruct "own1" as "[gho phys]". iFrame.
       iDestruct (ty_gho_own_depth_mono with "gho") as "[gho _]"; last by iFrame "gho".
       { lia. } { lia. }
     }
     { iDestruct "own2" as "[gho phys]". iFrame.
       iDestruct (ty_gho_own_depth_mono with "gho") as "[gho _]"; last by iFrame "gho".
       { lia. } { lia. }
     }
     iDestruct "J" as (xl' mask') "(? & ? & ? & ?)". iModIntro. iFrame.
     } unfold advance_credits. lia.
  Qed.
  
  Lemma typed_instr_of_memload_with_cumutime1
    {𝔄 𝔅} (E: elctx) (L: llctx) (I: invctx)
    (p : path)
    (ty : type 𝔄)
    (ty' : type 𝔅)
    (tr: predl_trans' [𝔄] 𝔅) :
    (∀ x v d tid post mask, ⊢ (llft_ctx -∗ time_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
      llctx_interp L -∗
      ⌜eval_path p = Some v⌝ -∗ ty_own ty x d d tid [FVal v] -∗
      ⟨π, tr post -[x] mask π⟩ -∗
      ⧗1 -∗
      ⧖(d) -∗
      £(2*d*d + 4*d + 2) -∗ |={⊤ ∖ ↑advN}=> ∃ (l: cloc) (l': loc) H, ⌜v = #l.1⌝ ∗ H ∗ (H &&{↑NllftG; d+1}&&> (l.1 ↦[^ l.2]∗ [ #l' ])) ∗ (H ={⊤}=∗
      ∃ x' , llctx_interp L ∗ ty_own ty' x' d d tid [FVal #l' ] ∗ ⟨π, post x' mask π⟩
    ))%I)
    → typed_instr_ty E L I +[p ◁ ty] (!p) (ty') tr.
  Proof. 
    intros Rd tid post mask iκs xl. destruct xl as [x []].
    iIntros "#LFT #TIME #PROPH #UNIQ #E L I [T _] Obs".
    wp_bind p.
    iApply (wp_hasty with "T").
    iIntros (v d) "%Hp #⧖ ty".
    iApply wp_fupd.
    iApply (wp_cumulative_time_receipt2 with "TIME"); first by set_solver.
    iIntros "⧗". replace 2 with (1 + 1); last by done.
    iDestruct (cumulative_time_receipt_sep with "⧗") as "[⧗1 ⧗2]".
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗1 ⧖") as "[⧖' £]";
        first by solve_ndisj.
    iDestruct (lc_weaken (_ + _)%nat with "£") as "[£1 £2]"; first last. {
    iMod (Rd x v d tid with "LFT TIME PROPH UNIQ E L [] ty Obs ⧗2 ⧖ £1") as (l l' H) "[%Hvl [H [#Hpt VsBack]]]"; first by trivial.
    subst v.
    iApply (wp_read_na_guarded_cells_singleton with "[H £2]"); first by solve_ndisj.
     { iFrame "Hpt". iFrame "H". iFrame "£2". }
    iNext. iIntros "H". iMod ("VsBack" with "H") as (x') "(L & Ty' & #Obs)".
    iModIntro. iExists -[x']. iFrame. iFrame "#". done.
    }
    unfold advance_credits. lia.
  Qed.

  Lemma typed_instr_of_memload
    {𝔄 𝔅} (E: elctx) (L: llctx) (I: invctx)
    (p : path)
    (ty : type 𝔄)
    (ty' : type 𝔅)
    (tr: predl_trans' [𝔄] (𝔅)) :
    (∀ x v d tid post mask, ⊢ (llft_ctx -∗ time_ctx -∗ proph_ctx -∗ uniq_ctx -∗ elctx_interp E -∗
      llctx_interp L -∗
      ⌜eval_path p = Some v⌝ -∗ ty_own ty x d d tid [FVal v] -∗
      ⟨π, tr post -[x] mask π⟩ -∗
      ⧖(d) -∗
      £(2*d*d + 4*d + 2) -∗ |={⊤ ∖ ↑advN}=> ∃ (l: cloc) (l': loc) H, ⌜v = #l.1⌝ ∗ H ∗ (H &&{↑NllftG; d+1}&&> (l.1 ↦[^ l.2]∗ [ #l' ])) ∗ (H ={⊤}=∗
      ∃ x' , llctx_interp L ∗ ty_own ty' x' (S d) (S d) tid [FVal #l' ] ∗ ⟨π, post x' mask π⟩
    ))%I)
    → typed_instr_ty E L I +[p ◁ ty] (!p) (ty') tr.
  Proof.
    intros Rd tid post mask iκs xl. destruct xl as [x []].
    iIntros "#LFT #TIME #PROPH #UNIQ #E L I [T _] Obs".
    
    wp_bind p.
    iApply (wp_hasty with "T").
    iIntros (v d) "%Hp #time ty".
    iApply (wp_fupd).
    iApply (wp_persistent_time_receipt with "TIME time"). { set_solver. }
    iIntros "H£ #⧖S".
    iDestruct (lc_weaken (_ + _)%nat with "H£") as "[£1 £2]"; first last.
    {
    iApply fupd_wp; iMod (fupd_mask_subseteq (⊤∖↑advN)). { trivial. }
    iMod (Rd x v d tid with "LFT TIME PROPH UNIQ E L [] ty Obs time £1") as (l l' H) "[%Hvl [H [#Hpt VsBack]]]"; first by trivial.
    subst v.
    
    iApply (wp_read_na_guarded_cells_singleton with "[H £2]"). { solve_ndisj. } { iFrame "Hpt". iFrame "H". iFrame "£2". }
    iModIntro. iNext. iIntros "H". iMod ("VsBack" with "H") as (x') "(L & Ty' & #Obs)".
    iModIntro. iExists -[x']. iFrame. iFrame "#". done.
    } unfold advance_credits; lia.
  Qed.
  
End programs_util.
