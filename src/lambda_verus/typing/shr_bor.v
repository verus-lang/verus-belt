From lrust.typing Require Export type.
From lrust.typing Require Import programs.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
From iris.base_logic.lib Require Import fancy_updates.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section shr_bor.
  Context `{!typeG Σ}.
  
  (** The ownership predicate of [&shr{κ} ty] is persistent and contains the sharing
      predicate of [ty] (without a later). Its sharing predicate is the default one, i.e.
      a guard of the ownership predicate with [g+1] laters: this is structural (it gives
      access to the sharing predicate of [ty]), puts the sharing predicate of [ty] under
      laters (so [&shr] stays contractive). Since the ownership predicate is persistent
      and never lazy, nothing is gained from a structural sharing predicate. *)
  Program Definition shr_bor {𝔄} (κ: lft) (ty: type 𝔄) : type (at_clocₛ 𝔄) := @ty_of_st _ _ ((at_clocₛ 𝔄)) ({|
    st_size := 1;
    st_lfts := κ :: ty.(ty_lfts);
    st_E := ty.(ty_E) ++ ty_outlives_E ty κ;
    
    st_gho x d g tid := [S(d') := d]
      (@[κ] &&{↑NllftG; g+1}&&> ((x.1).1 ↦[^ (x.1).2 ]!∗ ty.(ty_phys) (snd x) tid)) ∗
      ty.(ty_shr) κ (snd x) d' g tid ∗
      ▷^(g+1) (ty.(ty_gho_pers) (snd x) d' g tid)
    ;
      
    st_phys x tid := [FVal (LitV (x.1).1)];
  |}%I : simple_type (at_clocₛ 𝔄)).
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation.
    intros. iIntros "#A". destruct d. { done. } unfold by_succ.
    destruct d'. { lia. }
    iDestruct "A" as "[Phys [Shr #Pers]]". iSplit.
    { leaf_goal laters to (g+1). { lia. } done. }
    iSplit.
    { iApply ty_shr_depth_mono; last by iFrame "Shr". { lia. } { lia. } }
    iApply (bi.laterN_le (g+1) (g'+1)); first by lia. iNext.
    iApply ty_gho_pers_depth_mono; last by iFrame "Pers".
    { lia. } { trivial. }
  Qed.
  Next Obligation.
    intros 𝔄 κ ty κ0 x n d g tid ξ R Hin.
    iIntros "LFT #Incl #Gho".
    destruct d as [|d]; [done|]. rewrite /by_succ.
    iDestruct "Gho" as "[Phys [Shr #InnerPers]]".
    iDestruct (ty_shr_lft_mono ty κ κ0 with "[] Shr") as "#Shr0".
    { iApply (llftl_incl_trans with "Incl []"). iApply llftl_intersect_incl_l. }
    iApply (bi.laterN_le (g + 1 + d * (g + 1))); [lia|].
    rewrite (bi.laterN_add (g + 1) (d * (g + 1))). iNext (g + 1).
    iDestruct (ty_shr_guard_proph ty κ0 (snd x) n d g tid ξ R with "LFT [] InnerPers Shr0")
      as "InnerGuardProph"; [done| |].
    { iApply (llftl_incl_trans with "Incl []"). iApply llftl_intersect_incl_r. }
    iNext. iIntros "#Rk #Rg".
    leaf_goal laters to (n + (d + 1) * (g + 1)). { lia. }
    iApply ("InnerGuardProph" with "Rk").
  Qed.
  Next Obligation. done. Qed.
  
  Global Instance shr_ne {𝔄} κ : NonExpansive (@shr_bor 𝔄 κ).
  Proof. move=> ????. apply ty_of_st_ne. solve_ne_type. Qed.
End shr_bor.

Notation "&shr{ κ }" := (shr_bor κ) (format "&shr{ κ }") : lrust_type_scope.

Section typing.
  Context `{!typeG Σ}.

  Local Lemma shr_bor_gho_dist {𝔄} n κ (ty ty': type 𝔄) x d g tid :
    (∀x tid, ty.(ty_phys) x tid = ty'.(ty_phys) x tid) →
    (∀x d g tid, dist_later n (ty.(ty_gho_pers) x d g tid) (ty'.(ty_gho_pers) x d g tid)) →
    (∀κ x d g tid, ty.(ty_shr) κ x d g tid ≡{n}≡ ty'.(ty_shr) κ x d g tid) →
    (&shr{κ} ty)%T.(ty_gho_own) x d g tid ≡{n}≡ (&shr{κ} ty')%T.(ty_gho_own) x d g tid.
  Proof.
    move=> EqPhys EqPers EqShr /=. f_equiv=> d' /=. f_equiv; [|f_equiv].
    + f_equiv. by rewrite EqPhys.
    + apply EqShr.
    + replace (g + 1) with (S g); last by lia.
      apply later_contractive.
      destruct n; [split; lia|]. apply dist_later_S.
      have H1 := EqPers (x.2) d' g tid.
      rewrite <- dist_later_S in H1. f_equiv. apply H1.
  Qed.

  Global Instance shr_type_contractive {𝔄} κ : TypeContractive (@shr_bor _ _ 𝔄 κ).
  Proof.
    split; [by apply (type_lft_morphism_add_one κ)|done| | | |].
    - move=> n ty ty' ???? EqPers EqPhys EqShr *. by apply shr_bor_gho_dist.
    - move=> n ty ty' ???? EqPers EqPhys EqShr *. by apply shr_bor_gho_dist.
    - done.
    - move=> n ty ty' ???? EqPers EqPhys EqShr *. apply default_shr_contractive=> *.
      split=> m ?. apply shr_bor_gho_dist; [done| |].
      + move=> *. split=> ??. eapply dist_later_lt; [apply EqPers|lia].
      + move=> *. eapply dist_later_lt; [apply EqShr|lia].
  Qed.
  
  Lemma shr_copy {𝔄} κ (ty: type 𝔄) : Copy (&shr{κ} ty).
  Proof.
    split. - typeclasses eauto. - iIntros. iPureIntro. done.
    - intros. by apply copy_shr_default.
  Qed.
  
  Lemma shr_stack_okay {𝔄} κ (ty: type 𝔄) : StackOkay (&shr{κ} ty).
  Proof. done. Qed.

  Global Instance shr_send {𝔄} κ (ty: type 𝔄) : Sync ty → Send (&shr{κ} ty).
  Proof.
    intros Hsync. 
    split.
    - destruct x, x'. intros Ha. inversion Ha. trivial.
    - intros tid tid' x d g. destruct d as [|d]. { iIntros. contradiction. }
      have Ha := (Hsync tid tid' (snd x) d g).
      destruct Ha as [Hphys [Hgho [Hghopers Hshr]]].
      iIntros (G H κs d0 Hineq TG TH) "#LFT #UNIQ #TIME Hg H Gg G A ⧖o". 
      iDestruct "A" as "[#Hphys [#Hshr #Hpers]]". simpl.
      iModIntro. iApply step_fupdN_intro; first by trivial. iModIntro. iModIntro.
      iNext.
      iModIntro. iExists x, 0.
      iSplit; [iSplit; [|iSplit] | ].
      + rewrite Hphys. done.
      + rewrite Hshr. replace (d + 0) with d by lia. done.
      + iNext. rewrite Hghopers. replace (d + 0) with d by lia. done.
      + iFrame "G H". iSplit; last done. replace (d0 + 0) with d0 by lia. done.
  Qed.
  
  Global Instance shr_sync {𝔄} κ (ty: type 𝔄) : Sync ty → Sync (&shr{κ} ty).
  Proof.
    intros Hsync. apply sync_default; [done|]. split.
      - destruct x as [l x]. destruct (Hsync tid tid' x d g) as [phys [gho [pers shr]]]; trivial.
      - destruct x as [l x]. destruct d as [|d]; first by done.
        destruct (Hsync tid tid' x d g) as [phys [gho [pers shr]]]; trivial.
        split; simpl; rewrite shr; rewrite phys; rewrite pers; trivial.
  Qed.

  Global Instance shr_just_loc {𝔄} κ (ty: type 𝔄) : JustLoc (&shr{κ} ty).
  Proof. iIntros (vπ d g tid) "A". by iExists _. Qed.

  Lemma shr_resolve {𝔄} κ (ty: type 𝔄) E L : resolve E L (&shr{κ} ty) (const (const True)).
  Proof. apply resolve_just. Qed.

  Lemma shr_type_incl {𝔄 𝔅} κ κ' (f: 𝔄 →ₛ 𝔅) ty ty' :
    κ' ⊑ κ -∗ type_incl ty ty' f -∗ type_incl (&shr{κ} ty) (&shr{κ'} ty') (at_cloc_mapₛ f).
  Proof.
    iIntros "#Incl".
    iDestruct 1 as "(_ & #Incl2 & #Sub & #SubPers & %Phys & #SubShr)".
    iApply (@type_incl_simple_type Σ _ (at_clocₛ 𝔄) (at_clocₛ 𝔅) _ _).
      - done.
      - unfold ty_lfts, ty_of_st, st_lfts. by iApply lft_intersect_mono.
      - unfold st_gho. iModIntro. iIntros (x d g tid) "A".  destruct x as [l x].
        destruct d as [|d]. { done. }
        unfold by_succ. iDestruct "A" as "[#Hphys [#Hshr #Hpers]]".
        iSplit. { rewrite Phys. iApply (guards_transitive_right with "Incl Hphys"). }
        iSplit. {
            iApply (ty_shr_lft_mono with "Incl").
            iApply "SubShr". iFrame "Hshr".
        }
        { iApply "SubPers". iFrame "Hpers". }
      - simpl. iPureIntro. intros [l x]. done.
  Qed.

  Lemma shr_subtype {𝔄 𝔅} E L κ κ' (f: 𝔄 →ₛ 𝔅) ty ty' :
    lctx_lft_incl E L κ' κ → subtype E L ty ty' f →
    subtype E L (&shr{κ} ty) (&shr{κ'} ty') (at_cloc_mapₛ f).
  Proof.
    move=> In Sub. iIntros "L". iDestruct (In with "L") as "#In".
    iDestruct (Sub with "L") as "#Sub". iIntros "!> #?".
    iApply shr_type_incl; by [iApply "In"|iApply "Sub"].
  Qed.

  Lemma shr_eqtype {𝔄 𝔅} E L κ κ' (f: 𝔄 →ₛ 𝔅) g ty ty' :
    lctx_lft_eq E L κ κ' → eqtype E L ty ty' f g →
    eqtype E L (&shr{κ} ty) (&shr{κ'} ty') (at_cloc_mapₛ f) (at_cloc_mapₛ g).
  Proof. move=> [??] [??]. split; by apply shr_subtype. Qed.
  
  Lemma read_shr {𝔄} (ty: type 𝔄) κ E L :
    Copy ty → lctx_lft_alive E L κ →
    typed_read E L (&shr{κ} ty) ty (&shr{κ} ty) snd (=).
  Proof.
    iIntros (Hcopy Alv ?[|d']????) "#LFT #E #Guard L T H£";
      iDestruct "T" as "[#gho %phys]".
    { done. }
    iDestruct "gho" as "[#A [#Shr #C]]".
    iDestruct (copy_shr with "Shr") as "#B".
    leaf_open "Guard" with "L" as "[InterpL back]". { solve_ndisj. }
    iDestruct (Alv with "InterpL E") as "#Alv".
    iMod ("back" with "InterpL") as "G".
    
    iDestruct (guards_transitive with "Guard Alv") as "G1".
    iDestruct (guards_transitive_right with "G1 A") as "GA".
    iDestruct (guards_transitive_right with "G1 B") as "GB".
    
    leaf_open_laters "GB" with "G" as "T". { solve_ndisj. }
    iMod (lc_fupd_add_laterN with "H£ T") as "[#T Hclose]".
    iMod ("Hclose" with "T") as "G".
    
    iDestruct (copy_concrete with "T") as "%Conc".
    
    iModIntro. iExists (fst x).
    iExists (to_concrete (ty_phys ty (snd x) tid)).
    iExists (ty_phys ty (snd x) tid).
    iExists G.
    inversion phys.
    iSplit. { iPureIntro. done. }
    iSplit. { iPureIntro.  apply length_to_concrete. }
    iFrame "G".
    iSplit. { iFrame "#". rewrite <- heap_mapsto_cells_fancy_fmap_eq.
      rewrite fmap_to_concrete. { iFrame "#". } trivial.
    }
    iSplitR. { iIntros (l₁ c₁) "↦". rewrite <- heap_complete_mapsto_fancy_fmap_eq.
      rewrite fmap_to_concrete. { iModIntro. iFrame. }
      inversion Hcopy; trivial.
    }
    iSplit. { inversion Hcopy. rewrite fmap_to_concrete; done. }
    iSplitR.
    {
      iNext.
      iSplit. { iDestruct (ty_gho_own_depth_mono with "T") as "[S _]"; last by iFrame "S". { lia. } { lia. } }
    { done. }
  }
  iIntros "G". iModIntro. iFrame. iExists x. iSplit; first by done.
  iSplitR. { iFrame "#". } { done. }
  Qed.
End typing.

Global Hint Resolve shr_resolve shr_subtype shr_eqtype read_shr : lrust_typing.
