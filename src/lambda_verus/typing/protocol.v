From iris.proofmode Require Import proofmode.
From iris.algebra Require Import gmap.
From lrust.typing Require Import lft_contexts.
From lrust.typing Require Import type programs ghost own product tracked shr_bor uniq_bor programs_util_own programs_util.
From guarding Require Import guard tactics guard_later_pers own_and.
From lrust.typing Require Import ra proph_protocol uniq_util.
From lrust.lifetime Require Import lifetime_full.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Local Lemma proph_sub_diff (γ : gname) :
  {[ γ ]} ⊆ (↑NllftG : coPset) → ↑prophN ⊆ (⊤ ∖ {[ γ ]} : coPset).
Proof. intros. assert (↑prophN ## (↑NllftG : coPset)) by solve_ndisj. set_solver. Qed.

Local Lemma proph_sub_diff_NllftG : ↑prophN ⊆ (⊤ ∖ ↑NllftG : coPset).
Proof. solve_ndisj. Qed.

Section StorageProtocol.

  Context `{!typeG Σ}.
    
  (* very hacky type used to instantiate storage protocols *)
  Program Definition storable_ty {𝔄} (ty: type 𝔄) : ghost_type (storableₛ 𝔄) := {|
    gt_gho x tid := match x with
        (x0, (d, g)) => ty.(ty_gho_own) x0 d g tid ∗ ⧖(S d `max` g)
    end
  |}%I.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  
  (* this shouldn't really require Sync, but we would need another layer of step-indexing
    accounting to fix it (similar to how local_inv works). At least in this case,
    it doesn't matter, since the Storage Protocol requires Sync anyway. *)
  Global Instance storable_ty_send {𝔄} (ty : type 𝔄) : Send ty → Sync ty → Send (storable_ty ty).
  Proof. intros Hsend. intros Hsync. split; trivial.
    destruct x as [x0 [d0 g0]].
    destruct (Hsync tid tid' x0 d0 g0) as [A [B [C _]]].
    iIntros (d g G H κs d1 Hineq TG TH) "LFT UNIQ TIME Hg H Gg G gho ⧖".
    iDestruct "gho" as "[gho1 A]".
    setoid_rewrite B.
    iIntros. iApply step_fupdN_intro; first done. iNext. iModIntro.
    iExists (x0, (d0, g0)), 0. iFrame. replace (d1 + 0) with d1 by lia. iFrame.
    done.
  Qed.

  Global Instance storable_ty_sync {𝔄} (ty : type 𝔄) : Sync ty → Sync (storable_ty ty).
  Proof. intros Hsync. apply sync_default; [done|]. split; trivial.
    split; last trivial. destruct x as [x0 [d0 g0]].
    destruct (Hsync tid tid' x0 d0 g0) as [A [B [C _]]]. unfold storable_ty, gt_gho. simpl.
    setoid_rewrite B. done.
  Qed.
  
  Global Instance storable_ty_copy {𝔄} (ty : type 𝔄) : Copy ty → Copy (storable_ty ty).
  Proof.
    intros Hcopy. destruct Hcopy. split.
    - intros. destruct x as [x0 [d0 g0]]. unfold storable_ty, gt_gho. simpl. typeclasses eauto.
    - intros. destruct x as [x0 [d0 g0]]. iIntros "[gho _]".
      iDestruct (copy_concrete with "gho") as "%Hconc". iPureIntro. done.
    - intros. by apply copy_shr_default.
  Qed.
  
  Lemma storable_new {𝔄} E L I p (ty : type 𝔄) :
    typed_instr E L I
      +[p ◁ own_ptr 0 (tracked_ty ty)]
      (Seq Skip Skip)
      (const +[p ◁ own_ptr 0 (storable_ty ty)])
      (λ post '-[(l, x)], λ mask π, ∀ l n, post -[(l, (x, n))] mask π).
  Proof.
    apply typed_instr_of_skip_own_own_t; trivial.
    intros l1 x1 d tid iκs post mask.
    iIntros "#LFT #TIME #PROPH #UNIQ #E L Inv Gho Obs #⧖ ⧗".
    iExists (S d), (x1, (d, S d)). iModIntro. iFrame. iFrame "#".
    iSplit.
       - iApply (persistent_time_receipt_mono with "⧖"). lia.
       - iApply (proph_obs_impl with "Obs"). done.
  Qed.
  
  Lemma storable_into_inner {𝔄} E L I p (ty : type 𝔄) :
    typed_instr E L I
      +[p ◁ own_ptr 0 (storable_ty ty)]
      (Seq Skip Skip)
      (const +[p ◁ own_ptr 0 (tracked_ty ty)])
      (λ post '-[(l, (x, n))], λ mask π, ∀ l, post -[(l, x)] mask π).
  Proof.
    apply typed_instr_of_skip_own_own_t; trivial.
    intros l1 x1 d tid iκs post mask.
    iIntros "#LFT #TIME #PROPH #UNIQ #E L Inv Gho Obs ⧖ ⧗".
    destruct x1 as [x0 [d0 g0]].
    iDestruct "Gho" as "[Gho #⧖2]".
    iMod (cumulative_persistent_time_receipt with "TIME ⧗ ⧖2") as "⧖S2"; first solve_ndisj.
    iExists ((S d0 `max` g0)), x0. iModIntro. iFrame. iFrame "#".
    iDestruct (ty_gho_own_depth_mono with "Gho") as "[$ _]". { lia. } { lia. } 
    iApply (proph_obs_impl with "Obs"). done.
  Qed.

  Lemma storable_borrow {𝔄} κ E L I p (ty : type 𝔄) :
    lctx_lft_alive E L κ →
    typed_instr E L I
      +[p ◁ (&shr{κ} (storable_ty ty))]
      (Seq Skip Skip)
      (const +[p ◁ (&shr{κ} (tracked_ty ty))])
      (λ post '-[(l, (x, n))], λ mask π, ∀ l, post -[(l, x)] mask π).
  Proof.
    intros Alv. apply typed_instr_of_skip; trivial.
    intros [l [x0 [d0 g0]]] v d tid post mask iκs.
    iIntros "#LFT #TIME #PROPH #UNIQ #E L Inv %Path Gho Obs ⧖ ⧗ ⧗' £".
    iDestruct "Gho" as "[Gho #phys]".
    destruct d as [|d]; first done.
    iDestruct "Gho" as "[#pt [#shr #pers]]".
    iDestruct (ty_shr_default_to_guard (storable_ty ty) with "shr") as "#gho"; [done|].
    iDestruct (Alv with "L E") as "#Alv".
    iDestruct (guards_transitive_right with "Alv gho") as "LguardsGho".
    iDestruct (lc_weaken (_)%nat with "£") as "£1"; first last. {
    leaf_open_laters "LguardsGho" with "L" as "Opened"; first solve_ndisj.
    iMod (lc_fupd_elim_laterN with "£1 Opened") as ">[Inner back]".
    iDestruct "Inner" as "[Inner #Inner⧖]".
    iDestruct (ty_gho_pers_impl with "Inner") as "#InnerPers".
    iMod ("back" with "[Inner]") as "L". { iFrame. iFrame "Inner⧖". }
    iCombine "⧖ Inner⧖" as "⧖max".
    iMod (cumulative_persistent_time_receipt with "TIME ⧗ ⧖max") as "#⧖maxS";
        first solve_ndisj.
    iExists -[(l, x0)]. iModIntro. iFrame "L Inv". iSplit.
     - iSplit; last by done. iExists v, (1 + S (S d) `max` (S d0 `max` g0)).
       iSplit; first by done. iSplit; first by done.
       iSplit; last by done. unfold shr_bor. simpl.
       iSplit. { leaf_goal laters to (S (d+1)); first lia. iFrame "pt". }
       iSplit. { (* TEMPORARY: uses [ty_shr_from_guard]. *)
          iApply (ty_shr_from_guard (tracked_ty ty)).
          leaf_goal laters to (S (d+1)); first lia. 
          iApply (guards_transitive_left with "gho []").
          leaf_by_sep. iIntros "[A ⧖]". iDestruct (ty_gho_own_depth_mono with "A") as "[$ back]".
            { lia. } { lia. } iIntros "A". iFrame "⧖". iApply "back". iFrame.
       }
       iNext. iNext.
       iDestruct (ty_gho_pers_depth_mono with "InnerPers") as "$"; lia.
     - iApply (proph_obs_impl with "Obs"). done.
    }
    unfold advance_credits. lia.
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

  Notation "SP_Alloc: p s" := (new [ #0])%E (at level 102, p,s at level 1): expr_scope.

  Lemma typed_sp_alloc (k : K) (p s : path) (tyA : type 𝔄) E L I :
    typed_instr E L I
    +[p ◁ own_ptr 0 (ghost_ty tyA); s ◁ own_ptr 0 (tracked_ty tyC)]
    (SP_Alloc: p s)
    (λ v, +[v ◁ own_ptr 0 (storage_resource_ty)])
    (λ post '-[(_, a); (_, c)], λ mask π, vsp_rel a {[ k := c ]} π ∧ ∀ l γ, post -[(l, (γ, a))] mask π).
  Proof.
    move => tid postπ mask iκs vπl.
    iIntros "LFT TIME #PROPH UNIQ E L $ TY #Obs" => /=.
    destruct vπl as [[pl a] [[pl' c] []]].
    iDestruct "TY" as "((% & %d & % & Hd & Hgho & %Hphys) & TY' & _)".
    iDestruct "TY'" as "(% & %d' & % & Hd' & Hgho' & %)".
    destruct d, d' => //=.
    iDestruct "Hgho'" as "(_ & _ & HghoC)".
    iApply wp_fupd.
    iApply wp_new=>//.
    iIntros "!>" (l) "(† & ↦) ".
    iMod (sp_alloc_ns ⊤ NllftG a {[ k := c ]} (λ _ c, tyC.(gt_gho) c tid)
      with "PROPH [] [HghoC]") as "(%γ & % & Hsto & Htok)"; first solve_ndisj.
    { iApply (proph_obs_impl with "Obs"). by intros π [? _]. }
    { by rewrite big_sepM_singleton. }
    iExists -[(l, (γ, a))].
    iFrame "L Hd".
    iSplitL.
    - iExists _; iSplitR => //=.
      iFrame. iModIntro; iSplit => //. simpl.
      repeat rewrite heap_mapsto_fancy_vec_nil.
      iPureIntro; set_solver.
    - iApply (proph_obs_impl with "Obs").
      intros π' (? & Hpost).
      apply Hpost.
  Qed.

  Notation "SP_Join: a b" := (new [ #0])%E (at level 102, a,b at level 1): expr_scope.

  Lemma typed_sp_join (p1 p2 : path) E L I :
    typed_instr E L I
    +[p1 ◁ own_ptr 0 storage_resource_ty; p2 ◁ own_ptr 0 storage_resource_ty]
    (SP_Join: p1 p2)
    (λ v, +[v ◁ own_ptr 0 storage_resource_ty])
    (λ post '-[(_, (γ1, a1)); (_, (γ2, a2))], λ mask π, γ1 = γ2 ∧ ∀ l, post -[(l, (γ1, vsp_op a1 a2))] mask π).
  Proof.
    move => tid postπ mask iκs vπl.
    iIntros "LFT TIME #PROPH UNIQ E L $ TY #Obs" => /=.
    destruct vπl as [[pl1 [γ1 a1]] [[pl2 [γ2 a2]] []]].
    iMod (proph_obs_sat with "PROPH Obs") as "(%π & <- & _)" => //.
    iDestruct "TY" as "(H1 & H2 & _)".
    iDestruct "H1" as "(%l1 & %d1 & % & Hd1 & Hown1 & %Hphys1)".
    iDestruct "H2" as "(%l2 & %d2 & % & Hd2 & Hown2 & %Hphys2)".
    destruct d1,d2 => //.
    iDestruct "Hown1" as "(?&?&Hγ&#Hsto&Hown1)" => /=.
    iDestruct "Hown2" as "(_&_&_&_&Hown2)".
    iApply wp_new=>//.
    iIntros "!>" (l) "(† & ↦) ".
    iAssert (sp_own γ1 (vsp_op a1 a2)) with "[Hown1 Hown2]" as "Hown".
    { rewrite sp_own_op. iFrame. }
    iExists -[(l, (γ1, (vsp_op a1 a2)))].
    iFrame "L Hd1".
    iSplitL.
    - iExists _; iSplitR => //=.
      rewrite /ty_own/ty_gho_own/ty_phys/=.
      repeat rewrite heap_mapsto_fancy_vec_nil.
      iFrame; iSplitL => //.
    - iApply (proph_obs_impl with "Obs").
      intros π' [_ Hpost].
      apply Hpost.
  Qed.

  Notation "SP_Split: p p1 p2" := (new [ #0])%E (at level 102, p, p1, p2 at level 1): expr_scope.

  Lemma typed_sp_split (self p1 p2 : path) (ty : type 𝔄) E L I :
    typed_instr E L I
    +[self ◁ own_ptr 0 storage_resource_ty; p1 ◁ own_ptr 0 (ghost_ty ty); p2 ◁ own_ptr 0 (ghost_ty ty)]
    (SP_Split: self p1 p2)
    (λ v, +[v ◁ own_ptr 0 (prod_ty storage_resource_ty storage_resource_ty)])
    (λ post '-[(_, (γ, x)); (_, x1); (_, x2)], λ mask π, x = vsp_op x1 x2 ∧ ∀ l, post -[(l, ((γ, x1), (γ, x2)))] mask π).
  Proof.
    move => tid postπ mask iκs vπl.
    iIntros "LFT TIME #PROPH UNIQ E L $ TY #Obs" => /=.
    destruct vπl as [[pl [γ x]] [[plx1 x1] [[plx2 x2] []]]].
    simpl in x1, x2.
    iDestruct "TY" as "(H & _ & _ & _)".
    iDestruct "H" as "(%pl' & %d & % & #Hd & Hown & %Hphys)".
    injection Hphys => ? /=; subst pl'.
    destruct d => //.
    iMod (proph_obs_sat with "PROPH Obs") as "(%π & -> & _)" => //.
    iApply (wp_persistent_time_receipt with "TIME Hd"); [done|].
    iIntros "? #Hd'".
    iApply wp_new=>//.
    iIntros "!>" (l) "(† & ↦)".
    iExists -[(l, ((γ, x1), (γ, x2)))].
    iFrame "L".
    iFrame "Hd'".
    iSplitL.
    - iExists _; iSplitR => //=.
      rewrite sp_own_op.
      iDestruct "Hown" as "(?&?&%&#?&Hown1&Hown2)".
      iFrame.
      rewrite /ty_own/=!heap_mapsto_vec_nil !freeable_util.freeable_sz_full.
      repeat rewrite heap_mapsto_fancy_vec_nil.
      by iFrame "#".
    - iApply (proph_obs_impl with "Obs").
      intros π' [_ Hpost].
      apply Hpost.
  Qed.

  Notation "SP_Exchange: p1 p2 p3 p4" := (new [ #0])%E (at level 102, p1,p2,p3,p4 at level 1): expr_scope.

  Lemma typed_sp_exchange (k : K) (p1 p2 p3 p4 : path) (tyA : type 𝔄) E L I :
    typed_instr E L I
    +[p1 ◁ own_ptr 0 storage_resource_ty; p2 ◁ own_ptr 0 (tracked_ty tyC); p3 ◁  own_ptr 0 (ghost_ty tyA); p4 ◁ own_ptr 0 (ghost_ty tyC)]
    (SP_Exchange: p1 p2 p3 p4)
    (λ v, +[v ◁ own_ptr 0 (prod_ty storage_resource_ty (tracked_ty tyC))])
    (λ post '-[(_, (γ, p)); (_, s); (_, new_p); (_, new_s)], λ mask π, vsp_exchanges p {[ k := s ]} new_p {[ k := new_s ]} π ∧ ∀ l, post -[(l, ((γ, new_p), new_s))] mask π).
  Proof.
    move => tid postπ mask iκs vπl.
    iIntros "LFT TIME #PROPH UNIQ E L $ TY #Obs" => /=.
    destruct vπl as [[pl [γ p]] [[pls s] [[plnew_p new_p] [[plnew_s new_s] []]]]].
    simpl in γ,p,s,new_p, new_s.
    iDestruct "TY" as "(Hp & Hs & _ & _)".
    iDestruct "Hp" as "(% & %d & % & #Hd & Hown & %Hphys)".
    iDestruct "Hs" as "(% & %d' & % & #Hd' & Hown' & %Hphys')".
    injection Hphys => ? /=; subst v. injection Hphys' => ? /=; subst v0.
    destruct d,d' => //.
    iDestruct "Hown" as "(?&?&Hγ&#Hsto&Hown)".
    iDestruct "Hown'" as "(?&?&HghoC)".
    iApply wp_fupd; iApply wp_new=>//.
    iIntros "!>" (l) "(† & ↦)".
    iDestruct "Hγ" as %Hγ.
    iMod (sp_exchange p new_p {[ k := s ]} {[ k := new_s ]} γ _ ⊤ ltac:(set_solver)
      (proph_sub_diff γ Hγ) with "PROPH Hsto [] Hown [HghoC]") as "(Hown & HghoC)".
    { iApply (proph_obs_impl with "Obs"). by intros π [? _]. }
    { iNext. by rewrite big_sepM_singleton. }
    iModIntro.
    iExists -[(l, ((γ, new_p, new_s)))].
    iFrame "L Hd".
    iSplitL.
    - iExists _; iSplitR => //=.
      rewrite /ty_own/=!heap_mapsto_vec_nil !freeable_util.freeable_sz_full.
      repeat rewrite heap_mapsto_fancy_vec_nil.
      repeat iFrame.
      iSplit => //; iNext; iFrame "#".
      rewrite big_sepM_singleton. iFrame. by iPureIntro.
    - iApply (proph_obs_impl with "Obs").
      intros π' (? & Hpost).
      apply Hpost.
  Qed.

  Notation "SP_Deposit: p1 p2 p3" := (new [ #0])%E (at level 102, p1,p2,p3 at level 1): expr_scope.

  Lemma typed_sp_deposit (k : K) (p1 p2 p3 : path) (tyA : type 𝔄) E L I :
    typed_instr E L I
    +[p1 ◁ own_ptr 0 storage_resource_ty; p2 ◁ own_ptr 0 (tracked_ty tyC); p3 ◁  own_ptr 0 (ghost_ty tyA)]
    (SP_Deposit: p1 p2 p3)
    (λ v, +[v ◁ own_ptr 0 storage_resource_ty])
    (λ post '-[(_, (γ, p)); (_, s); (_, new_p)], λ mask π, vsp_deposits p {[ k := s ]} new_p π ∧ ∀ l, post -[(l, (γ, new_p))] mask π).
  Proof.
    move => tid postπ mask iκs vπl.
    iIntros "LFT TIME #PROPH UNIQ E L $ TY #Obs" => /=.
    destruct vπl as [[pl [γ p]] [[pls s] [[plnew_p new_p] []]]].
    simpl in γ,p,s,new_p.
    iDestruct "TY" as "(Hp & Hs & _ & _)".
    iDestruct "Hp" as "(% & %d & % & #Hd & Hown & %Hphys)".
    iDestruct "Hs" as "(% & %d' & % & #Hd' & Hown' & %Hphys')".
    injection Hphys => ? /=; subst v. injection Hphys' => ? /=; subst v0.
    destruct d,d' => //.
    iDestruct "Hown" as "(?&?&Hγ&#Hsto&Hown)".
    iDestruct "Hown'" as "(?&?&HghoC)".
    iApply wp_fupd; iApply wp_new=>//.
    iIntros "!>" (l) "(† & ↦)".
    iDestruct "Hγ" as %Hγ.
    iMod (sp_deposit p new_p {[ k := s ]} γ _ ⊤ ltac:(set_solver)
      (proph_sub_diff γ Hγ) with "PROPH Hsto [] Hown [HghoC]") as "Hown".
    { iApply (proph_obs_impl with "Obs"). by intros π [? _]. }
    { iNext. by rewrite big_sepM_singleton. }
    iModIntro.
    iExists -[(l, ((γ, new_p)))].
    iFrame "L Hd".
    iSplitL.
    - iExists _; iSplitR => //=.
      rewrite /ty_own/=!heap_mapsto_vec_nil !freeable_util.freeable_sz_full.
      repeat rewrite heap_mapsto_fancy_vec_nil.
      repeat iFrame.
      by iFrame "#".
    - iApply (proph_obs_impl with "Obs").
      intros π' (? & Hpost).
      apply Hpost.
  Qed.

  Notation "SP_Withdraw: p1 p2 p3" := (new [ #0])%E (at level 102, p1,p2,p3 at level 1): expr_scope.

  Lemma typed_sp_withdraw (k : K) (p1 p2 p3 : path) (tyA : type 𝔄) E L I :
    typed_instr E L I
    +[p1 ◁ own_ptr 0 storage_resource_ty; p2 ◁ own_ptr 0 (ghost_ty tyA); p3 ◁  own_ptr 0 (ghost_ty tyC)]
    (SP_Withdraw: p1 p2 p3)
    (λ v, +[v ◁ own_ptr 0 (prod_ty storage_resource_ty (tracked_ty tyC))])
    (λ post '-[(_, (γ, p)); (_, new_p); (_, new_s)], λ mask π, vsp_withdraws p new_p {[ k := new_s ]} π ∧ ∀ l, post -[(l, ((γ, new_p) , new_s))] mask π).
  Proof.
    move => tid postπ mask iκs vπl.
    iIntros "LFT TIME #PROPH UNIQ E L $ TY #Obs" => /=.
    destruct vπl as [[pl [γ p]] [[plnew_p new_p] [[plnew_s new_s] []]]].
    simpl in γ,p,new_s,new_p.
    iDestruct "TY" as "(Hp & _ & _ & _)".
    iDestruct "Hp" as "(% & %d & % & #Hd & Hown & %Hphys)".
    injection Hphys => ? /=; subst v.
    destruct d => //.
    iDestruct "Hown" as "(?&?&Hγ&#Hsto&Hown)".
    iApply wp_fupd; iApply wp_new=>//.
    iIntros "!>" (l) "(† & ↦)".
    iDestruct "Hγ" as %Hγ.
    iMod (sp_withdraw p new_p {[ k := new_s ]} γ _ ⊤ ltac:(set_solver)
      (proph_sub_diff γ Hγ) with "PROPH Hsto [] Hown") as "[Hown HghoC]".
    { iApply (proph_obs_impl with "Obs"). by intros π [? _]. }
    iModIntro.
    iExists -[(l, ((γ, new_p), new_s))].
    iFrame "L Hd".
    iSplitL.
    - iExists _; iSplitR => //=.
      rewrite /ty_own/=!heap_mapsto_vec_nil !freeable_util.freeable_sz_full.
      repeat rewrite heap_mapsto_fancy_vec_nil.
      repeat iFrame.
      iFrame "#".
      rewrite big_sepM_singleton. by iFrame.
    - iApply (proph_obs_impl with "Obs").
      intros π' (? & Hpost).
      apply Hpost.
  Qed.

  Notation "SP_Update: p1 p2" := (new [ #0])%E (at level 102, p1,p2 at level 1): expr_scope.

  Lemma typed_sp_update (p1 p2 : path) (tyA : type 𝔄) E L I :
    typed_instr E L I
    +[p1 ◁ own_ptr 0 storage_resource_ty; p2 ◁ own_ptr 0 (ghost_ty tyA)]
    (SP_Update: p1 p2)
    (λ v, +[v ◁ own_ptr 0 storage_resource_ty])
    (λ post '-[(_, (γ, p)); (_, new_p)], λ mask π, vsp_updates p new_p π ∧ ∀ l, post -[(l, (γ, new_p))] mask π).
  Proof.
    move => tid postπ mask iκs vπl.
    iIntros "LFT TIME #PROPH UNIQ E L $ TY #Obs" => /=.
    destruct vπl as [[pl [γ p]] [[plnew_p new_p] []]].
    simpl in γ,p,new_p.
    iDestruct "TY" as "(Hp & _ & _)".
    iDestruct "Hp" as "(% & %d & % & #Hd & Hown & %Hphys)".
    injection Hphys => ? /=; subst v.
    destruct d => //.
    iDestruct "Hown" as "(?&?&Hγ&#Hsto&Hown)".
    iApply wp_fupd; iApply wp_new=>//.
    iIntros "!>" (l) "(† & ↦)".
    iDestruct "Hγ" as %Hγ.
    iMod (sp_update p new_p γ _ ⊤ ltac:(set_solver)
      (proph_sub_diff γ Hγ) with "PROPH Hsto [] Hown") as "Hown".
    { iApply (proph_obs_impl with "Obs"). by intros π [? _]. }
    iModIntro.
    iExists -[(l, (γ, new_p))].
    iFrame "L Hd".
    iSplitL.
    - iExists _; iSplitR => //=.
      rewrite /ty_own/=!heap_mapsto_vec_nil !freeable_util.freeable_sz_full.
      repeat rewrite heap_mapsto_fancy_vec_nil.
      repeat iFrame.
      by iFrame "#".
    - iApply (proph_obs_impl with "Obs").
      intros π' (? & Hpost).
      apply Hpost.
  Qed.

  Notation "SP_ExchangeNonDet: p1 p2 p3" := (new [ #0])%E (at level 102, p1,p2,p3 at level 1): expr_scope.

  Lemma typed_sp_exchange_nondeterministic (k : K) (p1 p2 p3 : path) (n : nat) (ty : type (vecₛ (𝔄 * ℭ) n)) E L I :
    typed_instr E L I
    +[p1 ◁ own_ptr 0 storage_resource_ty; p2 ◁ own_ptr 0 (tracked_ty tyC); p3 ◁  own_ptr 0 (ghost_ty ty)]
    (SP_ExchangeNonDet: p1 p2 p3)
    (λ v, +[v ◁ own_ptr 0 (prod_ty storage_resource_ty (tracked_ty tyC))])
    (λ post '-[(_, (γ, p)); (_, s); (_, new_pss)], λ mask π,
      vsp_exchanges_nondeterministic p {[ k := s ]}
        (λ new_p new_b, ∃ new_s, new_b = {[ k := new_s ]} ∧ (new_p, new_s) ∈ vec_to_list new_pss) ∧
      ∀ l, Forall (λ '(new_p, new_s), post -[(l, ((γ, new_p), new_s))] mask π) (vec_to_list new_pss)).
  Proof.
    move => tid postπ mask iκs vπl.
    iIntros "LFT TIME #PROPH UNIQ E L $ TY #Obs" => /=.
    fold indep_interp_of_syn_type.
    destruct vπl as [[pl [γ p]] [[pls s] [[pl' new_pss] []]]].
    simpl in γ,p,s,new_pss.
    iDestruct "TY" as "(Hp & Hs & _ & _)".
    iDestruct "Hp" as "(% & %d & % & #Hd & Hown & %Hphys)".
    iDestruct "Hs" as "(% & %d' & % & #Hd' & Hown' & %Hphys')".
    injection Hphys => ? /=; subst v. injection Hphys' => ? /=; subst v0.
    destruct d,d' => //.
    iDestruct "Hown" as "(?&?&Hγ&#Hsto&Hown)".
    iDestruct "Hown'" as "(?&?&HghoC)".
    iMod (proph_obs_sat with "PROPH Obs") as "(%π & %exchng & _)" => //.
    iApply wp_fupd; iApply wp_new=>//.
    iIntros "!>" (l) "(† & ↦)".
    iDestruct "Hγ" as %Hγ.
    iMod (sp_exchange_nondeterministic p {[ k := s ]} _ γ _ ⊤ exchng ltac:(set_solver)
      (proph_sub_diff γ Hγ) with "PROPH Hsto Hown [HghoC]")
      as "(%new_p & %new_b & %Hin & Hown & HghoC)".
    { iNext. by rewrite big_sepM_singleton. }
    destruct Hin as (new_s & -> & Hin).
    iModIntro.
    iExists -[(l, ((γ, new_p, new_s)))].
    iFrame "L Hd".
    iSplitL.
    - iExists _; iSplitR => //=.
      rewrite /ty_own/=!heap_mapsto_vec_nil !freeable_util.freeable_sz_full.
      repeat rewrite heap_mapsto_fancy_vec_nil.
      repeat iFrame.
      iSplit => //; iNext; iFrame "#".
      rewrite big_sepM_singleton. iFrame. by iPureIntro.
    - iApply (proph_obs_impl with "Obs").
      intros π' (_ & Hpost).
      specialize (Hpost l).
      rewrite Forall_forall in Hpost.
      by apply (Hpost (new_p, new_s)).
  Qed.

  Notation "SP_Guard: p1 p2" := (new [ #0])%E (at level 102, p1,p2 at level 1): expr_scope.

  Lemma typed_sp_guard (k : K) (p1 p2 : path) E L I κ :
    lctx_lft_alive E L κ →
    typed_instr E L I
    +[p1 ◁ shr_bor κ storage_resource_ty; p2 ◁ own_ptr 0 (ghost_ty tyC)]
    (SP_Guard: p1 p2)
    (λ v, +[v ◁ shr_bor κ (tracked_ty tyC)])
    (λ post '-[(l, (γ, p)); (_, s)], λ mask π, vsp_guards p {[ k := s ]} ∧ ∀ l, post -[(l, s)] mask π).
  Proof.
    move => Alv tid mask iκs postπ [[pl [γ p]] [[pls s] []]].
    fold indep_interp_of_syn_type in *.
    iIntros "LFT #TIME #PROPH UNIQ E L $ TY #Obs" => /=.
    iDestruct "TY" as "(Hp & _)".
    iDestruct "Hp" as "(% & %d & % & #Hd & Hshr & %Hphys)".
    injection Hphys => ? /=; subst v.
    destruct d => //.
    iDestruct "Hshr" as "(_&#Hshr_shr&_)".
    iDestruct (ty_shr_default_to_guard storage_resource_ty with "Hshr_shr") as "#Hshr"; [done|].
    iSimpl in "Hshr".
    iMod (proph_obs_sat with "PROPH Obs") as "(%π & %guard & _)" => //.
    iDestruct (Alv with "L E") as "#Alv".
    iApply wp_fupd.
    wp_lam.
    wp_bind (_ ≤ _)%E.
    iApply (wp_persistent_time_receipt with "TIME Hd"); [done|].
    iIntros "H£ #Hd'".
    wp_pure (_ ≤ _)%E.
    iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME Hd'"); [done|].
    iIntros "H£' #Hd''".
    wp_if.
    iIntros "!>".

    rewrite bi.sep_assoc.
    iPoseProof (guards_weaken_rhs_sep_l with "Hshr") as "#Hshr1".
    iDestruct (guards_transitive_right with "Alv Hshr1") as "Hshr2".
    iMod (guards_extract_persistent_later with "Hshr2 L []") as "Hγ_Hshr".
    3: { iIntros "H". iExact "H". }
    1: exact _.
    set_solver.
    rewrite Nat.add_1_r -bi.later_laterN.
    iMod (lc_fupd_add_laterN _ _ _ (S (S d)) with "[H£'] Hγ_Hshr") as "(L & % & #Hsto)".
    { iApply (lc_weaken with "H£'"). rewrite /advance_credits. nia. }
    iPoseProof (sp_guard _ _ _ {[ γ ]} with "Hsto") as "Hguard'" => //; first set_solver.
    iPoseProof (guards_later_absorb_1 with "Hguard'") as "#Hguard''" => /=.
    iPoseProof (guards_weaken_mask _ (↑NllftG) with "Hguard''") as "Hguard"; first set_solver.
    (* iPoseProof (lguards_weaken_later _ _ _ _ (S (S d)) with "Hguard'''") as "#Hguard"; first lia. *)
    iPoseProof (guards_weaken_rhs_sep_r with "Hshr") as "#Hshr'".
    iClear "Hguard' Hguard'' Hshr1 Hshr2 Hshr"; iRename "Hshr'" into "Hshr".
    iDestruct (guards_transitive_additive with "Hshr Hguard") as "Hshr1".
    (* guard is proper *)

    iModIntro.
    iExists -[(((42%positive, 1337%Z), []), s)].
    iFrame "L Hd''".
    iSplitL.
    - iExists _; iSplitR => //=.
      rewrite /ty_own/=.
      iSplitR; first iSplit; last done.
      { by iApply guards_true. }
      rewrite -!bi.later_laterN.
      iSplitL => //.
      (* TEMPORARY: uses [ty_shr_from_guard]. *)
      iApply (ty_shr_from_guard (tracked_ty tyC)).
      iApply (lguards_weaken_later _ _ _ (S (S (d + 1))) ); first lia.
      by rewrite big_sepM_singleton.
    - iApply (proph_obs_impl with "Obs").
      intros π' (? & Hpost).
      apply Hpost.
  Qed.

  Notation "SP_JoinShared: p1 p2" := (new [ #0])%E (at level 102, p1, p2 at level 1): expr_scope.

  (*Lemma typed_sp_join_shared κ (p1 p2 : path) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I +[p1 ◁ shr_bor κ storage_resource_ty; p2 ◁ shr_bor κ storage_resource_ty] (SP_JoinShared: p1 p2) (λ v, +[v ◁ shr_bor κ storage_resource_ty]) (λ post '-[(l1, (γ1, x1)); (l2, (γ2, x2))], λ mask π, γ1 = γ2 ∧ ∀ y l, x1 ≼ y → x2 ≼ y → post -[(l, (γ1, y))] mask π).
  Proof.
    move => Alv tid mask postπ iκs vπl.
    fold indep_interp_of_syn_type.
    iIntros "LFT #TIME #PROPH UNIQ E L $ TY #Obs" => /=.
    destruct vπl as [[pl1 [γ1 x1]] [[pl2 [γ2 x2]] []]].
    iDestruct "TY" as "(H1 & H2 & _)".
    iDestruct "H1" as "(%pl1' & %d1 & % & #Hd1 & Hown1 & %Hphys1)".
    iDestruct "H2" as "(%pl2' & %d2 & % & #Hd2 & Hown2 & %Hphys2)".
    simpl in Hphys1, Hphys2.
    injection Hphys1 => ? /=; subst pl1'.
    injection Hphys2 => ? /=; subst pl2'.
    destruct d1 => //.
    destruct d2 => //.
    iDestruct "Hown1" as "(_ & #Hshr1_shr & _)".
    iDestruct (ty_shr_default_to_guard storage_resource_ty with "Hshr1_shr") as "#Hshr1"; [done|].
    iSimpl in "Hshr1".
    iDestruct "Hown2" as "(_ & #Hshr2_shr & _)".
    iDestruct (ty_shr_default_to_guard storage_resource_ty with "Hshr2_shr") as "#Hshr2"; [done|].
    iSimpl in "Hshr2".
    iDestruct (Alv with "L E") as "#Alv".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & _)" => //.
    destruct (decide (d1 ≤ d2)) as [Hle | Hgt].
    - do 2 rewrite bi.sep_assoc.
      iPoseProof (guards_weaken_rhs_sep_r with "Hshr1") as "#Hshr1'".
      iPoseProof (guards_weaken_rhs_sep_r with "Hshr2") as "#Hshr2'".
      (* Same issue with RA_JoinShared, we can apply sp_own_and but the resulting proposition is not a point_prop*)
  *)

  Notation "SP_JoinSharedDet: p1 p2 p3" := (new [ #0])%E (at level 102, p1, p2, p3 at level 1): expr_scope.

  Lemma typed_sp_join_shared_to_target κ (p1 p2 p3 : path) (ty : type 𝔄) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
    +[p1 ◁ shr_bor κ storage_resource_ty; p2 ◁ shr_bor κ storage_resource_ty; p3 ◁ own_ptr 0 (ghost_ty ty)]
    (SP_JoinSharedDet: p1 p2 p3)
    (λ v, +[v ◁ shr_bor κ storage_resource_ty])
    (λ post '-[(l1, (γ1, x1)); (l2, (γ2, x2)); (_, y)], λ mask π, γ1 = γ2 ∧ (∀ p, vsp_incl x1 p → vsp_incl x2 p → vsp_incl y p) ∧ ∀ l, post -[(l, (γ1, y))] mask π).
  Proof.
    move => Alv tid mask postπ iκs vπl.
    fold indep_interp_of_syn_type.
    iIntros "LFT #TIME #PROPH UNIQ E L $ TY #Obs" => /=.
    destruct vπl as [[pl1 [γ1 x1]] [[pl2 [γ2 x2]] [[pl3 y] []]]].
    iDestruct "TY" as "(H1 & H2 & _)".
    iDestruct "H1" as "(%pl1' & %d1 & % & #Hd1 & Hown1 & %Hphys1)".
    iDestruct "H2" as "(%pl2' & %d2 & % & #Hd2 & Hown2 & %Hphys2)".
    simpl in Hphys1, Hphys2.
    injection Hphys1 => ? /=; subst pl1'.
    injection Hphys2 => ? /=; subst pl2'.
    destruct d1 => //.
    destruct d2 => //.
    iDestruct "Hown1" as "(_ & #Hshr1_shr & _)".
    iDestruct (ty_shr_default_to_guard storage_resource_ty with "Hshr1_shr") as "#Hshr1"; [done|].
    iSimpl in "Hshr1".
    iDestruct "Hown2" as "(_ & #Hshr2_shr & _)".
    iDestruct (ty_shr_default_to_guard storage_resource_ty with "Hshr2_shr") as "#Hshr2"; [done|].
    iSimpl in "Hshr2".
    iDestruct (Alv with "L E") as "#Alv".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & %Hy & _)" => //.
    destruct (decide (d1 ≤ d2)) as [Hle | Hgt].
    - iApply wp_fupd.
      wp_lam.
      wp_bind (_ ≤ _)%E.
      iApply (wp_persistent_time_receipt with "TIME Hd2"); [done|].
      iIntros "H£ #Hd'".
      wp_pure (_ ≤ _)%E.
      iApply wp_fupd.
      iApply (wp_persistent_time_receipt with "TIME Hd'"); [done|].
      iIntros "H£' #Hd''".
      wp_if.
      iIntros "!>".

      rewrite bi.sep_assoc.
      iPoseProof (guards_weaken_rhs_sep_l with "Hshr1") as "#Hshr_sto".
      iDestruct (guards_transitive_right with "Alv Hshr_sto") as "Hshr_sto'".
      iMod (guards_extract_persistent_later with "Hshr_sto' L []") as "Hγ_Hshr".
      3: { iIntros "H". iExact "H". }
      1: exact _.
      set_solver.
      rewrite Nat.add_1_r -bi.later_laterN.
      iMod (lc_fupd_add_laterN _ _ _ (S (S d1)) with "[H£'] Hγ_Hshr") as "(L & % & #Hsto)".
      { iApply (lc_weaken with "H£'"). rewrite /advance_credits. nia. }

      iPoseProof (lguards_weaken_later _ _ _ _ (S (d2 + 1)) with "Hshr1") as "Hshr1'"; first lia.
      rewrite (bi.sep_assoc _ _ (sp_own γ1 _)).
      iPoseProof (guards_weaken_rhs_sep_r with "Hshr2") as "#Hshr2'".
      iPoseProof (guards_weaken_rhs_sep_r with "Hshr1'") as "#Hshr1''".
      iPoseProof (guards_and_point _ _ _ (sp_own γ1 y) with "Hshr1'' Hshr2'") as "Hshr3".
      { apply point_prop_p_own. }
      { by iApply sp_own_and_specific. }
      iPoseProof (guards_include_pers (⌜ {[γ1]} ⊆ ↑NllftG ⌝ ∗ (sp_sto _ _)) with "[] Hshr3") as "Hshr4".
      { iSplit => //. }

      iIntros "!>".
      iExists -[(((42%positive, 1337%Z), []), (γ1, y))].
      iFrame "L Hd2".
      iSplitL.
      + iExists _; iSplitR => //=.
        rewrite /ty_own/=.
        iSplitR; first iSplit; last done.
        { by iApply guards_true. }
        iSplitL => //.
        iApply (ty_shr_default_from_guard storage_resource_ty); first done. iSimpl.
        by rewrite (bi.sep_comm (sp_own γ1 y)) bi.sep_assoc.
      + iApply (proph_obs_impl with "Obs").
        intros π' (? & ? & Hpost).
        apply Hpost.
    - iApply wp_fupd.
      wp_lam.
      wp_bind (_ ≤ _)%E.
      iApply (wp_persistent_time_receipt with "TIME Hd1"); [done|].
      iIntros "H£ #Hd'".
      wp_pure (_ ≤ _)%E.
      iApply wp_fupd.
      iApply (wp_persistent_time_receipt with "TIME Hd'"); [done|].
      iIntros "H£' #Hd''".
      wp_if.
      iIntros "!>".

      rewrite (bi.sep_assoc _ _ (sp_own _ x2)).
      iPoseProof (guards_weaken_rhs_sep_l with "Hshr2") as "#Hshr_sto".
      iDestruct (guards_transitive_right with "Alv Hshr_sto") as "Hshr_sto'".
      iMod (guards_extract_persistent_later with "Hshr_sto' L []") as "Hγ_Hshr".
      3: { iIntros "H". iExact "H". }
      1: exact _.
      set_solver.
      rewrite !Nat.add_1_r -!bi.later_laterN.
      iMod (lc_fupd_add_laterN _ _ _ (S (S d2)) with "[H£'] Hγ_Hshr") as "(L & % & #Hsto)".
      { iApply (lc_weaken with "H£'"). rewrite /advance_credits. nia. }

      iPoseProof (lguards_weaken_later _ _ _ _ (S (d1 + 1)) with "Hshr2") as "Hshr2'"; first lia.
      rewrite (bi.sep_assoc _ _ (sp_own γ1 _)).
      iPoseProof (guards_weaken_rhs_sep_r with "Hshr1") as "#Hshr1'".
      iPoseProof (guards_weaken_rhs_sep_r with "Hshr2'") as "#Hshr2''".
      rewrite !Nat.add_1_r.
      iPoseProof (guards_and_point _ _ _ (sp_own γ1 y) with "Hshr1' Hshr2''") as "Hshr3".
      { apply point_prop_p_own. }
      { by iApply sp_own_and_specific. }
      iPoseProof (guards_include_pers (⌜ {[γ1]} ⊆ ↑NllftG ⌝ ∗ (sp_sto _ _)) with "[] Hshr3") as "Hshr4".
      { iSplit => //. }

      iIntros "!>".
      iExists -[(((42%positive, 1337%Z), []), (γ1, y))].
      iFrame "L Hd1".
      iSplitL.
      + iExists _; iSplitR => //=.
        rewrite /ty_own/=.
        iSplitR; first iSplit; last done.
        { by iApply guards_true. }
        iSplitL => //.
        iApply (ty_shr_default_from_guard storage_resource_ty); first done. iSimpl.
        by rewrite Nat.add_1_r (bi.sep_comm (sp_own γ1 y)) (bi.sep_assoc _ _ (sp_own _ y)).
      + iApply (proph_obs_impl with "Obs").
        intros π' (? & ? & Hpost).
        apply Hpost.
  Qed.

  Notation "SP_Weaken: p1 p2" := (new [ #0])%E (at level 102, p1, p2 at level 1): expr_scope.

  Lemma typed_sp_weaken κ (p1 p2 : path) (tyA : type 𝔄) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
    +[p1 ◁ shr_bor κ storage_resource_ty; p2 ◁ own_ptr 0 (ghost_ty tyA)]
    (SP_Weaken: p1 p2)
    (λ v, +[v ◁ shr_bor κ storage_resource_ty])
    (λ post '-[(l1, (γ, x1)); (l2, x2)], λ mask π, vsp_incl x2 x1 ∧ ∀ l, post -[(l, (γ, x2))] mask π).
  Proof.
    move => Alv tid postπ mask iκs vπl.
    iIntros "LFT #TIME #PROPH UNIQ E L $ TY #Obs" => /=.
    destruct vπl as [[pl1 [γ x1]] [[pl2 x2] []]].
    iDestruct "TY" as "(H & _)".
    iDestruct "H" as "(%pl1' & %d & % & #Hd & Hshr & %Hphys)".
    destruct d => //.
    injection Hphys => ? /=; subst pl1'.
    iDestruct "Hshr" as "(_ & #Hshr_shr & _)".
    iDestruct (ty_shr_default_to_guard storage_resource_ty with "Hshr_shr") as "#Hshr"; [done|].
    iSimpl in "Hshr".

    iDestruct (Alv with "L E") as "#Alv".
    iApply wp_fupd.
    wp_lam.
    wp_bind (_ ≤ _)%E.
    iApply (wp_persistent_time_receipt with "TIME Hd"); [done|].
    iIntros "H£ #Hd'".
    wp_pure (_ ≤ _)%E.
    iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME Hd'"); [done|].
    iIntros "H£' #Hd''".
    wp_if.
    iIntros "!>".

    rewrite bi.sep_assoc.
    iPoseProof (guards_weaken_rhs_sep_l with "Hshr") as "#Hshr1".
    iDestruct (guards_transitive_right with "Alv Hshr1") as "Hshr2".
    iMod (guards_extract_persistent_later with "Hshr2 L []") as "Hγ_Hshr".
    3: { iIntros "H". iExact "H". }
    1: exact _.
    set_solver.
    rewrite Nat.add_1_r -bi.later_laterN.
    iMod (lc_fupd_add_laterN _ _ _ (S (S d)) with "[H£'] Hγ_Hshr") as "(L & % & #Hsto)".
    { iApply (lc_weaken with "H£'"). rewrite /advance_credits. nia. }

    iMod (proph_obs_sat with "PROPH Obs") as "(% & %Hincl & _)" => //.
    iPoseProof (guards_weaken_rhs_sep_r with "Hshr") as "#Hsp_own1".
    iPoseProof (guards_weaken_rhs_point with "Hsp_own1") as "Hsp_own2".
    2: by apply sp_own_mono.
    apply point_prop_p_own.

    iModIntro.
    iExists -[(((42%positive, 1337%Z), []), (γ, x2))].
    iFrame "L Hd''".
    iSplitL.
    - iExists _; iSplitR => //=.
      rewrite /ty_own/=.
      iSplitR; first iSplit; last done.
      { by iApply guards_true. }
      rewrite -!bi.later_laterN.
      iSplitL => //.
      iApply (ty_shr_default_from_guard storage_resource_ty); first done. iSimpl.
      iClear "Hshr".
      iPoseProof (guards_include_pers (⌜{[γ]} ⊆ ↑NllftG⌝ ∗ sp_sto γ (λ _ c, gt_gho tyC c tid))%I with "[] Hsp_own2") as "Hshr".
      { by iSplit. }
      rewrite (bi.sep_comm (sp_own _ _) (⌜ _ ⌝ ∗ _))%I.
      rewrite bi.sep_assoc.
      by iApply (lguards_weaken_later _ _ _ (S (S d)) ); first lia.
    - iApply (proph_obs_impl with "Obs").
      intros π' (? & Hpost).
      apply Hpost.
  Qed.

  Notation "SP_Validate: p1" := (new [ #0])%E (at level 102, p1 at level 1): expr_scope.

  Lemma typed_sp_validate `{!Inhabited (~~ℭ)} κ (p1 : path) (tyA : type 𝔄) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
    +[p1 ◁ shr_bor κ storage_resource_ty]
    (SP_Validate: p1)
    (λ v, +[v ◁ own_ptr 0 (prod_ty (ghost_ty tyA) (ghost_ty tyC))])
    (λ post '-[(l1, (γ, p))], λ mask π, ∀ l q t, vsp_rel (vsp_op p q) t π →
      (∀ k s, t !! k = Some s → post -[(l, (q, s))] mask π) ∧
      (t = ∅ → post -[(l, (q, inhabitant))] mask π)).
  Proof.
    move => Alv tid mask postπ iκs vπl.
    iIntros "LFT #TIME #PROPH UNIQ E L $ TY #Obs" => /=.
    fold indep_interp_of_syn_type.
    destruct vπl as [[pl [γ p]] []].
    iDestruct "TY" as "(H & _)".
    iDestruct "H" as "(%pl' & %d & % & #Hd & Hshr & %Hphys)".
    destruct d => //.
    injection Hphys => ? /=; subst pl'.
    iDestruct "Hshr" as "(_ & #Hshr_shr & _)".
    iDestruct (ty_shr_default_to_guard storage_resource_ty with "Hshr_shr") as "#Hshr"; [done|].
    iSimpl in "Hshr".

    iDestruct (Alv with "L E") as "#Alv".
    iApply wp_fupd.
    wp_lam.
    wp_bind (_ ≤ _)%E.
    iApply (wp_persistent_time_receipt with "TIME Hd"); [done|].
    iIntros "H£ #Hd'".
    wp_pure (_ ≤ _)%E.
    iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME Hd'"); [done|].
    iIntros "H£' #Hd''".
    wp_if.
    iIntros "!>".
    rewrite bi.sep_assoc.
    iPoseProof (guards_weaken_rhs_sep_l with "Hshr") as "#Hshr1".
    iDestruct (guards_transitive_right with "Alv Hshr1") as "Hshr2".
    iMod (guards_extract_persistent_later with "Hshr2 L []") as "Hγ_Hshr".
    3: { iIntros "H". iExact "H". }
    1: exact _.
    set_solver.
    rewrite Nat.add_1_r -bi.later_laterN.
    iMod (lc_fupd_add_laterN _ _ _ (S (S d)) with "[H£'] Hγ_Hshr") as "(L & %Hγ & #Hsto)".
    { iApply (lc_weaken with "H£'"). rewrite /advance_credits. nia. }
    iPoseProof (guards_weaken_rhs_sep_r with "Hshr") as "#Hshr3".
    iDestruct (guards_transitive_right with "Alv Hshr3") as "Hshr4".
    iDestruct (sp_own_unit with "Hsto") as "#Hunit".
    iMod (sp_validate_with_extra_guard_with_later vsp_unit p γ _ _ ⊤ (↑NllftG) _
      ltac:(set_solver) ltac:(set_solver) proph_sub_diff_NllftG
      with "PROPH Hsto Hshr4 L Hunit") as "J".
    iMod (lc_fupd_add_laterN _ _ _ (S (S d)) with "[H£] J") as (q t) "(#Hobs & L & _)".
    { iApply (lc_weaken with "H£"). rewrite /advance_credits. nia. }
    iModIntro.
    iCombine "Obs Hobs" as "Obs'".
    destruct (decide (t = ∅)) as [ Hempty | Hnempty ].
    { iExists -[((42%positive, 1337%Z), (q, inhabitant))].
      iFrame "L Hd''".
      iSplitL.
      - iExists _; iSplitR => //=.
      - iApply (proph_obs_impl with "Obs'").
        intros π [Hpost Hrel]. rewrite vsp_unit_op in Hrel.
        by apply (Hpost _ _ _ Hrel). }
    apply map_choose in Hnempty as (k & s & Hlookup).
    iExists -[((42%positive, 1337%Z), (q, s))].
    iFrame "L Hd''".
    iSplitL.
    - iExists _; iSplitR => //=.
    - iApply (proph_obs_impl with "Obs'").
      intros π [Hpost Hrel]. rewrite vsp_unit_op in Hrel.
      by eapply (Hpost _ _ _ Hrel).
  Qed.

  Notation "SP_ExchangeWithShr: p1 p2 p3 p4 p5" := (new [ #0])%E (at level 102, p1,p2,p3,p4,p5 at level 1): expr_scope.

  Lemma typed_sp_exchange_with_shr (k : K) κ (p1 p2 p3 p4 p5 : path) (tyA : type 𝔄) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
    +[p1 ◁ own_ptr 0 storage_resource_ty; p2 ◁ shr_bor κ storage_resource_ty; p3 ◁ own_ptr 0 (tracked_ty tyC); p4 ◁  own_ptr 0 (ghost_ty tyA); p5 ◁ own_ptr 0 (ghost_ty tyC)]
    (SP_ExchangeWithShr: p1 p2 p3 p4 p5)
    (λ v, +[v ◁ own_ptr 0 (prod_ty storage_resource_ty (tracked_ty tyC))])
    (λ post '-[(_, (γ, p)); (_, (γ', p')); (_, s); (_, new_p); (_, new_s)], λ mask π, γ = γ' ∧ vsp_exchanges (vsp_op p p') {[ k := s ]} (vsp_op new_p p') {[ k := new_s ]} π ∧ ∀ l, post -[(l, ((γ, new_p), new_s))] mask π).
  Proof.
    move => Alv tid mask postπ iκs vπl.
    iIntros "LFT #TIME #PROPH UNIQ E L $ TY #Obs" => /=.
    destruct vπl as [[pl [γ p]] [[pl' [γ' p']] [[pls s] [[plnew_p new_p] [[plnew_s new_s] []]]]]].
    simpl in γ,p,γ',p',s,new_p, new_s.
    iDestruct "TY" as "(Hp & Hp' & Hs & _ & _)".
    iDestruct "Hp" as "(% & %d & % & #Hd & Hown & %Hphys)".
    iDestruct "Hp'" as "(% & %d' & % & #Hd' & Hown' & %Hphys')".
    iDestruct "Hs" as "(% & %d'' & % & #Hd'' & Hown'' & %Hphys'')".
    injection Hphys => ? /=; subst v. injection Hphys' => ? /=; subst v0. injection Hphys'' => ? /=; subst v1.
    destruct d,d',d'' => //.
    iDestruct "Hown" as "(_&_&Hγ&#Hsto&Hown)".
    iDestruct "Hown'" as "(_&#Hshr_shr&_)".
    iDestruct (ty_shr_default_to_guard storage_resource_ty with "Hshr_shr") as "#Hshr"; [done|].
    iSimpl in "Hshr".
    iDestruct "Hown''" as "(_&_&HghoC)".

    iDestruct (Alv with "L E") as "#Alv".
    wp_lam.
    wp_bind (_ ≤ _)%E.
    iApply (wp_persistent_time_receipt with "TIME Hd'"); [done|].
    iIntros "H£ #Hd1".
    wp_pure (_ ≤ _)%E.
    iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME Hd1"); [done|].
    iIntros "H£' #Hd2".
    wp_if.
    iDestruct "Hγ" as "%Hγ".
    iDestruct (guards_transitive_right with "Alv Hshr") as "Hshr1".
    rewrite bi.sep_assoc.
    iPoseProof (guards_weaken_rhs_sep_r with "Hshr1") as "#Hshr2".
    iMod (proph_obs_sat with "PROPH Obs") as "(%π & <- & _)" => //.
    iMod (sp_exchange_with_extra_guard_with_later p new_p p' {[ k := s ]} {[ k := new_s ]} γ _ _ ⊤ (↑NllftG) _
      ltac:(set_solver) ltac:(set_solver) proph_sub_diff_NllftG
      with "PROPH Hsto Hshr2 [] L Hown [HghoC]") as "Hguard".
    { iApply (proph_obs_impl with "Obs"). by intros π' (_ & ? & _). }
    { iNext. by rewrite big_sepM_singleton. }

    rewrite Nat.add_1_r.
    iMod (lc_fupd_add_laterN _ _ _ (S (S d')) with "[H£'] Hguard") as "(L & Hown & Hgho)".
    { iApply (lc_weaken with "H£'"). rewrite /advance_credits. nia. }
    iMod (lc_fupd_elim_later with "[H£] Hgho") as "Hgho".
    { iApply (lc_weaken with "H£"). rewrite /advance_credits. nia. }
    iModIntro.
    iExists -[((42%positive, 1337%Z), ((γ, new_p, new_s)))].
    iFrame "L Hd".
    iSplitL.
    - iExists _; iSplitR => //=.
      rewrite /ty_own/=!heap_mapsto_fancy_vec_nil !freeable_util.freeable_sz_full.
      repeat iFrame.
      iSplit => //.
      iSplitR => //.
      { by iRight. }
      iNext; iFrame "#".
      iSplit => //.
      by rewrite big_sepM_singleton.
    - iApply (proph_obs_impl with "Obs").
      intros π' (? & ? & Hpost).
      apply Hpost.
  Qed.

  Notation "SP_ValidateWithShr: p1 p2" := (new [ #0])%E (at level 102, p1,p2 at level 1): expr_scope.

  Lemma typed_sp_validate_with_shr `{!Inhabited (~~ℭ)} κ (p1 p2 : path) (tyA : type 𝔄) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
    +[p1 ◁ uniq_bor κ storage_resource_ty; p2 ◁ shr_bor κ storage_resource_ty]
    (SP_ValidateWithShr: p1 p2)
    (λ v, +[v ◁ own_ptr 0 (prod_ty (ghost_ty tyA) (ghost_ty tyC))])
    (λ post '-[(l1, (γ1, p1), _, _, _, _); (l2, (γ2, p2))], λ mask π, γ1 = γ2 ∧ ∀ l q t, vsp_rel (vsp_op (vsp_op p1 p2) q) t π →
      (∀ k s, t !! k = Some s → post -[(l, (q, s))] mask π) ∧
      (t = ∅ → post -[(l, (q, inhabitant))] mask π)).
  Proof.
    move => Alv tid postπ mask iκs vπl.
    fold indep_interp_of_syn_type.
    iIntros "#LFT #TIME #PROPH #UNIQ E L $ TY #Obs" => /=.
    fold indep_interp_of_syn_type.
    destruct vπl as [[[[[[pl1 [γ1 x1]] ?] ?] ?] idx] [[pl2 [ γ2 x2]] []]].
    iDestruct "TY" as "(H1 & H2 & _)".
    iDestruct "H1" as "(%pl1' & %d1 & % & #Hd1 & Huniq & %Hphys1)".
    iDestruct "H2" as "(%pl2' & %d2 & % & #Hd2 & Hshr & %Hphys2)".
    destruct d2 => //.
    iDestruct "Hshr" as "(_ & #Hshr_shr & _)".
    iDestruct (ty_shr_default_to_guard storage_resource_ty with "Hshr_shr") as "#Hshr"; [done|].
    iSimpl in "Hshr".
    iDestruct (Alv with "L E") as "#Alv".
    iDestruct "Huniq" as "[_ [%Hineq [[Bor Credits] Pers]]]".

    iMod (fractional.frac_split_guard_in_half NllftG with "L Alv") as (γ) "[F1 [F2 [#guardHalf #back]]]".
    { solve_ndisj. }
    iMod (llftl_begin with "LFT") as (κ1) "[A1 #Kill1] ". { trivial. }
    iMod (llftl_begin with "LFT") as (κ2) "[A2 #Kill2]". { trivial. }
    iMod (llftl_borrow_shared _ κ1 with "F1") as "[#G1 F1]". { trivial. }
    iMod (llftl_borrow_shared _ κ2 with "F2") as "[#G2 F2]". { trivial. }
    iDestruct (guards_remove_later_rhs with "G1") as "G1'".
    iDestruct (guards_remove_later_rhs with "G2") as "G2'".
    iDestruct (guards_transitive with "G1' guardHalf") as "Incl1".
    iDestruct (guards_transitive with "G2' guardHalf") as "Incl2".

    iMod (proph_ibor_acc with "LFT UNIQ Incl1 Bor A1") as "(Hgho1 & Hclose1)".
    1: trivial.

    iApply wp_fupd.
    wp_lam.
    wp_bind (_ ≤ _)%E.
    iApply (wp_persistent_time_receipt with "TIME Hd2"); [done|].
    iIntros "H£ #Hd2'".
    wp_pure (_ ≤ _)%E.
    iApply (wp_persistent_time_receipt with "TIME Hd2'"); [done|].
    iIntros "H£' Hd2''".
    wp_if.

    rewrite uniq_payload_cell.
    unfold gt_gho.
    iDestruct "Hgho1" as "(H⧖ & Hgho1 & H↦)".
    iDestruct "Hgho1" as "(%Hγ1 & #Hsto1 & Hown1)".

    iMod (proph_obs_sat with "PROPH Obs") as "(%π & <- & _)" => //.
    iDestruct (guards_transitive_right with "Incl2 Hshr") as "Hshr2".
    rewrite bi.sep_assoc.
    iPoseProof (guards_weaken_rhs_sep_r with "Hshr2") as "Hshr3".
    iPoseProof (lguards_weaken_later _ _ _ _ (S (S d2)) with "Hshr3") as "Hshr4"; first lia.
    iMod (sp_validate_with_extra_guard_with_later x1 x2 γ1 _ _ ⊤ (↑NllftG) _
      ltac:(set_solver) ltac:(set_solver) proph_sub_diff_NllftG
      with "PROPH Hsto1 Hshr4 A2 Hown1") as "J".
    replace (advance_credits (S (S d2))) with (S (S d2) + (advance_credits (S (S d2)) - S (S d2))).
    2: { rewrite /advance_credits. nia. }
    iDestruct "H£'" as "(H£' & H£'')".
    iMod (lc_fupd_add_laterN _ _ _ (S (S d2)) with "H£' J") as (q t) "(#Hobs & A2 & Hown1)".

    iMod (cumulative_persistent_time_receipt_get_credits with "TIME Credits Hd2''") as "(#? & Credits)"; [trivial |..].
    iMod (fupd_mask_subseteq (↑Nllft)) as "Hclose".
    { trivial. }
    iMod ("Hclose1" $! (uniq_cell (𝔄:=ghostₛ (positiveₛ * 𝔄)) (γ1, x1) _ _) with "[H↦ H⧖ Hown1]") as "(Htok & A1)".
    { iNext. rewrite uniq_payload_cell.
      iFrame "H⧖ H↦". iFrame "#". iFrame "%". iFrame.
    }
    iDestruct "Credits" as "(Credits1 & Credits2)".
    iDestruct "Credits2" as "(C1 & C2 & C3)".
    iMod ("Hclose") as "_".

    iMod (fupd_mask_subseteq (↑Nllft)) as "Hclose".
    { trivial. }
    iMod ("Kill1" with "A1") as "Hkilled1".
    iMod (lc_fupd_add_later  with "C2 Hkilled1") as "Hkilled1".
    iMod ("Hclose") as "_".
    iMod (fupd_mask_subseteq (↑Nllft)) as "Hclose".
    { trivial. }
    iMod ("Kill2" with "A2") as "Hkilled2".
    replace (advance_credits (S d2)) with (1 + (advance_credits (S d2) - 1)).
    2: { rewrite /advance_credits. nia. }
    iDestruct "H£" as "(H£ & H£')".
    iMod (lc_fupd_add_later  with "H£ Hkilled2") as "Hkilled2".
    iMod ("Hclose") as "_".
    iMod ("F1" with "Hkilled1") as ">Hγ1".
    iMod ("F2" with "Hkilled2") as ">Hγ2".
    iMod (fupd_mask_subseteq (↑NllftG)) as "Hclose".
    { trivial. }
    iMod ("back" with "Hγ1 Hγ2") as "L".
    iMod "Hclose" as "_".
    iModIntro.
    fold indep_interp_of_syn_type in q.
    iCombine "Obs Hobs" as "Obs'".
    destruct (decide (t = ∅)) as [ Hempty | Hnempty ].
    - iExists -[((42%positive, 1337%Z), (q, inhabitant))].
      iFrame "L".
      iSplitL.
      + iSplitL => //=.
        rewrite /tctx_elt_interp.
        iExists _.
        iFrame "Hd2".
        iSplit => //.
      + iApply (proph_obs_impl with "Obs'").
        intros π' [[_ Hpost] Hrel].
        eapply Hpost in Hrel as [? Hpost_empty].
        by apply Hpost_empty.
    - apply map_choose in Hnempty as (k & s & Hlookup).
      iExists -[((42%positive, 1337%Z), (q, s))].
      iFrame "L".
      iSplitL.
      + iSplitL => //=.
        rewrite /tctx_elt_interp.
        iExists _.
        iFrame "Hd2".
        iSplit => //.
      + iApply (proph_obs_impl with "Obs'").
        intros π' [[_ Hpost] Hrel].
        eapply Hpost in Hrel as [Hpost_ne _].
        by eapply Hpost_ne.
  Qed.

  Notation "SP_ExchangeWithShrNonDet: p1 p2 p3 p4" := (new [ #0])%E (at level 102, p1,p2,p3,p4 at level 1): expr_scope.

  Lemma typed_sp_exchange_with_shr_nondeterministic (k : K) κ (p1 p2 p3 p4 : path) n (ty : type (vecₛ (𝔄 * ℭ) n))  E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
    +[p1 ◁ own_ptr 0 storage_resource_ty; p2 ◁ shr_bor κ storage_resource_ty; p3 ◁ own_ptr 0 (tracked_ty tyC); p4 ◁  own_ptr 0 (ghost_ty ty)]
    (SP_ExchangeWithShrNonDet: p1 p2 p3 p4)
    (λ v, +[v ◁ own_ptr 0 (prod_ty storage_resource_ty (tracked_ty tyC))])
    (λ post '-[(_, (γ, p)); (_, (γ', p')); (_, s); (_, new_pss)], λ mask π, γ = γ' ∧
      vsp_exchanges_nondeterministic (vsp_op p p') {[ k := s ]}
        (λ new_p_big new_b, ∃ new_p new_s, new_p_big = vsp_op new_p p' ∧ new_b = {[ k := new_s ]}
          ∧ (new_p, new_s) ∈ vec_to_list new_pss) ∧
      ∀ l, Forall (λ '(new_p, new_s), post -[(l, ((γ, new_p), new_s))] mask π) (vec_to_list new_pss)).
  Proof.
    move => Alv tid mask postπ iκs vπl.
    iIntros "LFT #TIME #PROPH UNIQ E L $ TY #Obs" => /=.
    destruct vπl as [[pl [γ p]] [[pl' [γ' p']] [[pls s] [[pl'' new_pss] []]]]].
    simpl in γ,p,γ',p',s,new_pss.
    iDestruct "TY" as "(Hp & Hp' & Hs & _ & _)".
    iDestruct "Hp" as "(% & %d & % & #Hd & Hown & %Hphys)".
    iDestruct "Hp'" as "(% & %d' & % & #Hd' & Hown' & %Hphys')".
    iDestruct "Hs" as "(% & %d'' & % & #Hd'' & Hown'' & %Hphys'')".
    injection Hphys => ? /=; subst v. injection Hphys' => ? /=; subst v0. injection Hphys'' => ? /=; subst v1.
    destruct d,d',d'' => //.
    iDestruct "Hown" as "(_&_&Hγ&#Hsto&Hown)".
    iDestruct "Hown'" as "(_&#Hshr_shr&_)".
    iDestruct (ty_shr_default_to_guard storage_resource_ty with "Hshr_shr") as "#Hshr"; [done|].
    iSimpl in "Hshr".
    iDestruct "Hown''" as "(_&_&HghoC)".

    iDestruct (Alv with "L E") as "#Alv".
    wp_lam.
    wp_bind (_ ≤ _)%E.
    iApply (wp_persistent_time_receipt with "TIME Hd'"); [done|].
    iIntros "H£ #Hd1".
    wp_pure (_ ≤ _)%E.
    iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME Hd1"); [done|].
    iIntros "H£' #Hd2".
    wp_if.
    iDestruct "Hγ" as "%Hγ".
    iDestruct (guards_transitive_right with "Alv Hshr") as "Hshr1".
    rewrite bi.sep_assoc.
    iPoseProof (guards_weaken_rhs_sep_r with "Hshr1") as "#Hshr2".
    iMod (proph_obs_sat with "PROPH Obs") as "(%π & <- & %exchng & _)" => //.
    assert (vsp_exchanges_nondeterministic (vsp_op p p') {[ k := s ]}
      (λ p2_q b2, ∃ p2, p2_q = vsp_op p2 p' ∧
        (λ new_p new_b, ∃ new_s, new_b = {[ k := new_s ]} ∧ (new_p, new_s) ∈ vec_to_list new_pss)
        p2 b2)) as exchng'.
    { intros q t1 Hsat.
      destruct (exchng q t1 Hsat) as (p2q & b2 & (new_p & new_s & -> & -> & Hin) & Himp).
      exists (vsp_op new_p p'), {[ k := new_s ]}. split; last done.
      exists new_p. split; first done. eauto. }
    iMod (sp_exchange_with_extra_guard_nondeterministic_with_later p p' {[ k := s ]} _
      γ _ _ ⊤ (↑NllftG) _ exchng'
      ltac:(set_solver) ltac:(set_solver) proph_sub_diff_NllftG
      with "PROPH Hsto Hshr2 L Hown [HghoC]") as "Hguard".
    { iNext. by rewrite big_sepM_singleton. }

    rewrite Nat.add_1_r.
    iMod (lc_fupd_add_laterN _ _ _ (S (S d')) with "[H£'] Hguard") as (new_p b2) "(%Hin & L & Hown & Hgho)".
    { iApply (lc_weaken with "H£'"). rewrite /advance_credits. nia. }
    destruct Hin as (new_s & -> & Hin).
    iMod (lc_fupd_elim_later with "[H£] Hgho") as "Hgho".
    { iApply (lc_weaken with "H£"). rewrite /advance_credits. nia. }
    iModIntro.
    iExists -[((42%positive, 1337%Z), ((γ, new_p, new_s)))].
    iFrame "L Hd".
    iSplitL.
    - iExists _; iSplitR => //=.
      rewrite /ty_own/=!heap_mapsto_fancy_vec_nil !freeable_util.freeable_sz_full.
      repeat iFrame.
      iSplit => //.
      iSplitR => //.
      { by iRight. }
      iNext; iFrame "#".
      iSplit => //.
      by rewrite big_sepM_singleton.
    - iApply (proph_obs_impl with "Obs").
      intros π' (? & ? & Hpost).
      specialize (Hpost (42%positive, 1337%Z)).
      rewrite Forall_forall in Hpost.
      by apply (Hpost (new_p, new_s)).
  Qed.
End StorageProtocol.
