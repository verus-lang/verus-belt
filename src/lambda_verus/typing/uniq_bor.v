From lrust.typing Require Export type.
From lrust.typing Require Import type_context programs mod_ty uniq_util.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section uniq_bor.
  Context `{!typeG Σ}.

  Program Definition uniq_bor {𝔄} (κ: lft) (ty: type 𝔄) : type (uniq_borₛ 𝔄) := {|
    ty_size := 1;  
    ty_lfts := κ :: ty.(ty_lfts);  
    ty_E := ty.(ty_E) ++ ty_outlives_E ty κ;
    
    ty_gho (x : ~~ (uniq_borₛ 𝔄)) d g tid :=
      κ ⊑ ty_lft ty ∗
      match x with
        (l, x0, ξi, d', g', idx) =>
          ⌜S d' ≤ d ∧ g' ≤ g⌝ ∗ uniq_body ty x0 ξi d' g' idx κ tid l
            ∗ (@[κ] &&{↑NllftG; g+1}&&> l #↦∗_)
            ∗ (basically_dead κ ∨ ▷ ty.(ty_gho_pers) x0 d' g' tid)
      end;
    
    ty_gho_pers (x: ~~ (uniq_borₛ 𝔄)) d g tid :=
      match x with
        (l, x0, ξi, d', g', idx) =>
            ⌜S d' ≤ d ∧ g' ≤ g⌝
              ∗ (basically_dead κ ∨ ▷ ty.(ty_gho_pers) x0 d' g' tid)
              ∗ uniq_body_pers_component ty x0 ξi d' g' idx κ tid l
      end;
      
    ty_phys (x : ~~ (uniq_borₛ 𝔄)) tid :=
      match x with
        (l, x0, ξi, d', g', idx) =>
            [FVal (LitV l.1)]
      end;
    
    (*ty_shr vπ d κ' tid l := [S(d') := d] ∃(l': loc) ξ, ⌜snd ∘ vπ ./ [ξ]⌝ ∗
      &frac{κ'} (λ q, l ↦{q} #l') ∗ &frac{κ'} (λ q, q:[ξ]) ∗
      ▷ ty.(ty_shr) (fst ∘ vπ) d' κ' tid l';*)
  |}%I.
  Next Obligation. intros ? ? ? x. destruct x as [[[[[[l ?] ?] ?] ?] ?] ?]. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. intros ? ? ? x. destruct x as [[[[[[l ?] ?] ?] ?] ?] ?]. done. Qed.
  Next Obligation. intros 𝔄 κ ty d0 g0 d1 g1 x tid Hle Hle2. simpl.
    destruct x as [[[[[l x0] ξi] d'] g'] idx].
    iIntros "[#A [%B [C [#D E]]]]".
    iDestruct (lguards_weaken_later _ _ _ _ (g1+1) with "D") as "D'". { lia. }
    iFrame. iFrame "#".
    iSplit. { iPureIntro. lia. } iIntros "[#A1 [%B1 [C1 [D1 E1]]]]". iFrame. iFrame "#". done.
  Qed.
  Next Obligation. intros 𝔄 κ ty d0 g0 d1 g1 x tid Hle Hle2. simpl.
    destruct x as [[[[[l x0] ξi] d'] g'] idx].
    iIntros "[%B C]". iFrame. iPureIntro. lia.
  Qed.
  Next Obligation.
    intros 𝔄 κ ty κ0 x n d g tid ξ R. simpl. intros Hin.
    destruct x as [[[[[l x0] ξi] d'] g'] idx].
    iIntros "#LFT #Incl1 [[%Dle %Gle] [#InnerPers #IdxBor]]".
    iDestruct "InnerPers" as "[bd|InnerPers]".
    {
      iNext. iDestruct "bd" as (κ') "[#Incl' #†κ']".
      iIntros "#G _". iDestruct (guards_transitive_left with "G Incl1") as "G2".
      iApply (guards_transitive_additive with "G2 []").
      leaf_goal lhs to (@[κ])%I. { iApply llftl_intersect_incl_l. }
      iApply (guards_transitive_right with "Incl'").
      leaf_by_sep. iIntros "Alive". iExFalso. iApply (llftl_not_own_end with "Alive †κ'").
    }
    
    unfold uniq_body_pers_component.
    
    iAssert (κ0 ⊑ κ)%I as "#Hincl0". {
      iApply (guards_transitive with "Incl1 []"). iApply llftl_intersect_incl_l.
    }
    iAssert (κ0 ⊑ foldr meet static (ty_lfts ty))%I as "#Hincl2". {
      iApply (guards_transitive with "Incl1 []"). iApply llftl_intersect_incl_r.
    }
    iAssert (▷ ▷^(d'*(g'+1)) (∀ ξ , ⌜ξ ∈ ξl x0⌝ -∗
          (R &&{↑NllftG; n+1}&&> @[κ0]) -∗
          (R &&{↑NllftG; n+1}&&> ty.(ty_gho) x0 d' g' tid) -∗
          (R &&{↑NllftG; n+1 + d'*(g'+1)}&&> 1:[ξ])
      ))%I as "Hforall".
    { iIntros (ξ') "%Hin2". iDestruct (ty_guard_proph with "LFT [] InnerPers") as "GP".
        { apply Hin2. } { iApply "Hincl2". } iFrame "GP". }
        
    iApply (bi.laterN_le (S (d' * (g' + 1)))). { nia. }
    iNext. iNext.
    iIntros "#Rk #Rg2".
    iAssert (R &&{↑NllftG; n}&&> @[κ])%I as "#RkK".
    { iApply (guards_transitive_left with "Rk Hincl0"). }
    iAssert (R &&{↑NllftG; n}&&> uniq_tok x0 ξi d' g' idx)%I as "#Rtok".
    { iApply (guards_transitive_left with "Rg2 []"). leaf_by_sep.
      iIntros "(A & B & Body & C)". rewrite uniq_body_unfold.
      iDestruct "Body" as "(T & ⧗ & P)". iFrame "T". iIntros "T". iFrame. }
    rewrite elem_of_cons in Hin. destruct Hin as [Hξeq|Hin].
    - subst ξ.
      leaf_goal laters to (n+1). { lia. }
      iApply (uniq_tok_guard_proph_tok with "LFT IdxBor RkK Rtok").
    - iDestruct (uniq_tok_guard_payload with "LFT IdxBor RkK Rtok") as "#G_inst".
      leaf_goal laters to (n + 1 + d' * (g' + 1)). { nia. }
      iApply "Hforall".
        { iPureIntro. apply Hin. }
        { leaf_goal laters to n. { lia. } iFrame "Rk". }
        { iApply (guards_transitive_left with "G_inst []").
          leaf_by_sep. iIntros "[A [B C]]". iFrame "B". iIntros. iFrame.
        }
  Qed.
  Next Obligation.
    destruct x as [[[[[l x0] ξi] d'] g'] idx]. fold indep_interp_of_syn_type. simpl.
    typeclasses eauto.
  Qed.
  Next Obligation.
    destruct x as [[[[[l x0] ξi] d'] g'] idx]. fold indep_interp_of_syn_type. simpl.
    intros d g tid. iIntros "[A [B [C [D E]]]]". iFrame. iApply uniq_body_pers_component_impl.
    iFrame.
  Qed.
  
  Global Instance uniq_bor_ne {𝔄} κ : NonExpansive (@uniq_bor 𝔄 κ).
  Proof. 
    intros n ty ty' Heqv. split.
     - done.
     - simpl. f_equiv. apply Heqv.
     - simpl. f_equiv. { apply Heqv. } 
        unfold ty_outlives_E. f_equiv. apply Heqv.
     - intros x d g tid. destruct x as [[[[[l x0] ξi] d'] g'] idx]. simpl. f_equiv.
        + do 2 f_equiv. apply Heqv.
        + do 2 f_equiv.
          * apply uniq_body_ne; intros; apply Heqv.
          * do 3 f_equiv. apply Heqv.
     - intros x d g tid. destruct x as [[[[[l x0] ξi] d'] g'] idx]. simpl. do 2 f_equiv.
        + do 2 f_equiv. apply Heqv.
        + apply uniq_pers_component_ne; intros; apply Heqv.
     - intros x tid. done.
  Qed.
End uniq_bor.

Notation "&uniq{ κ }" := (uniq_bor κ) (format "&uniq{ κ }") : lrust_type_scope.

Section typing.
  Context `{!typeG Σ}.

  Global Instance uniq_type_contractive {𝔄} κ : TypeContractive (uniq_bor (𝔄:=𝔄) κ).
  Proof.
    split; [by apply (type_lft_morphism_add_one κ)|done| | |].
     - intros n ty ty' Heq Heq1 Heq2 Heq3 Heq4 Heq5 x d g tid.
       destruct x as [[[[[l x0] ξi] d'] g'] idx]. simpl. f_equiv.
        + apply equiv_dist. iDestruct Heq1 as "#[??]".
          iSplit; iIntros "#H"; (iApply llftl_incl_trans; [iApply "H"|done]).
        + do 2 f_equiv.
          * apply uniq_body_contractive; intros; [apply Heq3|apply Heq5].
          * do 2 f_equiv. apply later_contractive. apply Heq4.
     - intros n ty ty' Heq Heq1 Heq2 Heq3 Heq4 Heq5 x d g tid.
       destruct x as [[[[[l x0] ξi] d'] g'] idx]. simpl. do 2 f_equiv.
        + f_equiv. apply later_contractive. apply Heq4.
        + apply uniq_pers_component_contractive; intros; [apply Heq3|apply Heq5].
     - intros x tid. done.
  Qed.
  
  Lemma uniq_stack_okay {𝔄} κ (ty: type 𝔄) : StackOkay (&uniq{κ} ty).
  Proof. intros x tid. destruct x as [[[[[l x0] ξi] d'] g'] idx]. done. Qed.
  
  Global Instance uniq_send_static {𝔄} (ty: type 𝔄) : Send ty → Send (&uniq{static} ty).
  Proof.
    intros Hsend. split. { intros. 
      destruct x as [[[[[[l1 ?] ?] ?] ?] ?] ?].
      destruct x' as [[[[[[l2 ?] ?] ?] ?] ?] ?]. inversion H. subst l2. done.
    }
    destruct x as [[[[[l x0] ξi] d'] g'] idx].
    intros d g G H κs d0 Hineq TG TH.
    iIntros "#LFT #UNIQ #TIME Hg H Gg G (Incl & %Ineqs & UniqBody & Pt & Pers) ⧖o".
    destruct d; first by lia.
    simpl.
    iMod (uniq_body_acc_rebody ty x0 ξi d' g' idx static tid l _ (uniq_payload ty tid' l)
      with "LFT UNIQ [] UniqBody") as "Acc". { set_solver. }
      { iApply llftl_tok_unit. }
    iModIntro. iNext. iMod "Acc" as "((⧖ & Gho & Pt1) & ⧗ & Close)".
    iCombine "⧖o ⧖" as "⧖max".
    iDestruct (send_change_tid tid tid' x0 d' g' G H κs _ _ TG TH with "LFT UNIQ TIME Hg H Gg G Gho ⧖max") as "J". Unshelve. 2: { lia. }
    iModIntro.
    iApply (step_fupdN_le d'). { lia. } { solve_ndisj. }
    iApply (step_fupdN_wand with "J"). iFrame.
    iIntros "gho". iMod "gho" as (x' off) "[gho [#⧖off [%Habstract [G H]]]]".
    iDestruct (ty_gho_pers_impl with "gho") as "#ghopers".
    iMod (fupd_mask_subseteq (↑Nllft)) as "Upd"; first solve_ndisj.
    iMod ("Close" $! (uniq_cell x' (d'+off) g') with "[Pt1 gho] []") as (idx2) "[Bor Alive]".
    { rewrite uniq_payload_later_cell. iNext.
      rewrite (send_change_tid_phys tid tid' x0 x'); [|symmetry; trivial].
      iFrame "gho Pt1". iApply (persistent_time_receipt_mono with "⧖off"). lia. }
    { iNext. iIntros (c2) "[_ static]". iExFalso. iApply (llftl_end_unit with "static"). }
    iMod "Upd" as "_".
    iDestruct (uniq_body_make ty x' x0 with "Bor ⧗") as "UBody".
    iModIntro.
    iExists (l, x', ξi, d'+off, g', idx2), off. iFrame.
    iSplit.
      + iSplit; first by (iPureIntro; lia).
        iFrame "ghopers".
      + iSplit.
        * iApply (persistent_time_receipt_mono with "⧖off"); lia.
        * iPureIntro. rewrite Habstract. trivial.
  Qed.

(*
  Global Instance uniq_send {𝔄} κ (ty: type 𝔄) : Send ty → Send (&uniq{κ} ty).
  Proof.
    intros SendTy tid tid' x d g.
    destruct x as [[[[[l x0] ξi] d'] g'] idx].
    split. { done. }
    iIntros "[#Incl [Hle [UniqBody Pers]]]".
    iDestruct "UniqBody" as "[A B]".
    (*do 10 (f_equiv || move=>?).*)
 *)

  Global Instance uniq_sync {𝔄} κ (ty: type 𝔄) : Sync ty → Sync (&uniq{κ} ty).
  Proof. 
    intros SyncTy tid tid' x d g.
    destruct x as [[[[[l x0] ξi] d'] g'] idx].
    destruct (SyncTy tid tid' x0 d g) as [Hphys [Hgho Hpers]].
    split. { done. }
    have Hg: ∀ x d g, ty.(ty_gho) x d g tid ⊣⊢ ty.(ty_gho) x d g tid'.
    { intros. apply SyncTy. }
    have Hp: ∀ x, ty.(ty_phys) x tid = ty.(ty_phys) x tid'.
    { intros x. apply (SyncTy tid tid' x 0 0). }
    split. { unfold uniq_bor, ty_gho. do 3 f_equiv.
      { by apply uniq_body_proper. }
      f_equiv.
      f_equiv. unfold ty_gho_pers. f_equiv. apply SyncTy.
    }
    unfold uniq_bor, ty_gho_pers. do 2 f_equiv.
      - destruct (SyncTy tid tid' x0 d' g') as [H'phys [H'gho H'pers]].
        setoid_rewrite H'pers. done.
      - by apply uniq_pers_component_proper.
  Qed.

  Global Instance uniq_just_loc {𝔄} κ (ty: type 𝔄) : JustLoc (&uniq{κ} ty).
  Proof. 
    iIntros (x d g tid) "A".
    destruct x as [[[[[l x0] ξi] d'] g'] idx].
    iExists (l.1). done.
  Qed.

  Lemma uniq_resolve {𝔄} E L κ (ty: type 𝔄) :
    lctx_lft_alive E L κ → resolve E L (&uniq{κ} ty) (λ x π, snd (vπ x π) = fst (vπ x π)).
  Proof.
    intros Alive G F x d g tid TimelessRes Hmask.
    iIntros "LFT PROPH UNIQ TIME E #Lguard G [In uniq]".
    destruct x as [[[[[l x0] ξi] d'] g'] idx].
    iDestruct "uniq" as "[Hle [uniq pers]]".
    iMod (resolve_uniq_body with "LFT PROPH UNIQ TIME In E Lguard G uniq") as "[X [G _]]".
      { done. } { set_solver. }
    iModIntro.
    iApply step_fupdN_intro. { set_solver. }
    iModIntro. iModIntro. iFrame "G".
    iApply proph_obs_eq; last by done. intros π. simpl.
    f_equal.
  Qed.

  Lemma uniq_subtype {𝔄} E L κ κ' (ty ty': type 𝔄) :
    lctx_lft_incl E L κ' κ → eqtype E L ty ty' idₛ idₛ →
    subtype E L (&uniq{κ} ty) (&uniq{κ'} ty') idₛ.
  Proof.
    move=> In.
    intros Eqt. rewrite <-eqtype_id_unfold in Eqt. iIntros "L".
    iDestruct (Eqt with "L") as "#Eqt". iDestruct (In with "L") as "#In". iIntros "!> #E".
    iSplit; [done|].
    iDestruct ("Eqt" with "E") as (?) "[[Lfts1 Lfts2][#EqOwn [#EqPers %EqPhys]]]".
    iSpecialize ("In" with "E"). iSplit; [by iApply lft_intersect_mono|].
    iSplit. {
      iModIntro. iIntros (x d g tid) "[#Incl gho]".
      destruct x as [[[[[l x0] ξi] d'] g'] idx].
      iDestruct "gho" as "[#Hineq [UniqBody [#PtBase #Pers]]]".
      iDestruct (uniq_body_pers_component_impl with "UniqBody") as "#Saved".
      iDestruct (incl_uniq_body ty ty' x0 ξi d' g' with "In EqOwn [] UniqBody") as "UniqBody".
      { done. }
      iAssert (basically_dead κ' ∨ ▷ ty_gho_pers ty' x0 d' g' tid)%I as "Pers'". { iDestruct "Pers" as "[Dead|Pers]". { iLeft. iApply (basically_dead_incl with "In Dead"). } iRight. iApply "EqPers". iFrame "Pers". }
      iDestruct (guards_transitive with "In Incl") as "Incl'".
      iDestruct (guards_transitive with "Incl' Lfts1") as "Incl''".
      iFrame "UniqBody Pers' Incl'' Hineq".
      iSplit. { iApply (guards_transitive_right with "In PtBase"). }
      iIntros "[Hincl'' [Hineq'' [UniqBody Pers'']]]".
      iFrame "#".
      rewrite !uniq_body_unfold.
      iDestruct "UniqBody" as "(Tok & ⧗ & _)". iFrame "Tok ⧗ Saved".
    }
    iSplit. {
      iModIntro. iIntros (x d g tid) "#Pers".
      destruct x as [[[[[l x0] ξi] d'] g'] idx].
      iDestruct "Pers" as "[A [Pers C]]".
      iAssert (basically_dead κ' ∨ ▷ ty_gho_pers ty' x0 d' g' tid)%I as "Pers'". { iDestruct "Pers" as "[Dead|Pers]". { iLeft. iApply (basically_dead_incl with "In Dead"). } iRight. iApply "EqPers". iFrame "Pers". }
      iFrame "#".
      iApply (incl_uniq_body_pers_component with "In EqOwn [] C").
      done.
    }
    { done. }
  Qed.
  
  Lemma uniq_eqtype {𝔄} E L κ κ' (ty ty': type 𝔄) :
    lctx_lft_eq E L κ κ' → eqtype E L ty ty' idₛ idₛ →
    eqtype E L (&uniq{κ} ty) (&uniq{κ} ty') idₛ idₛ.
  Proof. move=> [??][??]. by split; apply uniq_subtype. Qed.
  
  Definition uniq_bor_loc {𝔄} (m: ~~ (uniq_borₛ 𝔄)) : cloc :=
      match m with (l, x0, ξi, d', g', idx) => l end.
  
  Definition uniq_bor_current {𝔄} (m: ~~ (uniq_borₛ 𝔄)) : ~~ 𝔄 :=
      match m with (l, x0, ξi, d', g', idx) => x0 end.
      
  Definition uniq_bor_future {𝔄} (m: ~~ (uniq_borₛ 𝔄)) (π : proph_asn) : 𝔄 := (vπ m π).2.
      
  Definition uniq_bor_ξi {𝔄} (m: ~~ (uniq_borₛ 𝔄)) : positive :=
      match m with (l, x0, ξi, d', g', idx) => ξi end.
      
  Definition uniq_bor_update {𝔄} (m: ~~ (uniq_borₛ 𝔄)) (new: ~~ 𝔄) (m': ~~ (uniq_borₛ 𝔄)) :=
      match m, m' with
        (l, x0, ξi, _, _, _), (l', x0', ξi', _, _, _) =>
          l = l' ∧ x0' = new ∧ ξi' = ξi
      end.

  Lemma write_uniq {𝔄} E L κ (ty: type 𝔄):
    lctx_lft_alive E L κ →
    typed_write E L (&uniq{κ} ty) ty (&uniq{κ} ty) ty uniq_bor_current uniq_bor_update.
  Proof.
    move=> Alv. split; [done|].
    intros x d v tid G Htimeless.
    iIntros "#LFT #UNIQ E #GuardsL G [Gho %Phys]".
    destruct x as [[[[[l x0] ξi] d'] g'] idx].
    iDestruct "Gho" as "[#Incl [%Hineq [UniqBody [#PtBase Pers]]]]".
    iMod (lctx_lft_alive_get_guards _ _ _ _ _ Alv with "GuardsL E G") as "[G #GuardsK]".
      { solve_ndisj. }
    iDestruct (guards_transitive with "GuardsL GuardsK") as "#G_Guards_K".
    iMod (fractional.frac_split_guard_in_half with "G G_Guards_K") as (γ2) "[H1 [H2 [#Ghalf #Halfback]]]". { solve_ndisj. }
    iMod (uniq_body_acc with "LFT UNIQ Ghalf UniqBody H1") as "(P & ⧗ & Gback)".
      { solve_ndisj. }
    iDestruct "P" as "(>#⧖ & gho & >pt)".
    destruct d as [|d]. { lia. }
    iModIntro. iExists l. iExists d. iExists (fractional.half γ2).
    assert (v = FVal #(l.1)) as Hvl. { inversion Phys. trivial. }
    subst v.
    iSplit; first by done.
    iSplit; first by done.
    iSplitL "pt gho". {
      iExists (ty_phys ty x0 tid).
      iFrame "pt". simpl. unfold ty_own.
      iSplit; last by done.
      iNext. iDestruct (ty_gho_depth_mono with "gho") as "[gho _]"; last by iFrame "gho".
      { lia. } { lia. }
    }
    iFrame "H2". iSplit. { iApply (guards_transitive_right with "Ghalf PtBase"). }
    iIntros (x1 d1) "pt #⧖1 £new".
    iCombine "⧖ ⧖1" as "⧖max".
    iDestruct "pt" as (lv) "[>pt [gho #>%phys]]". subst lv.
    iDestruct (ty_gho_pers_impl with "gho") as "#ghopers".
    iDestruct ("Gback" $! x1 d1 (S d1) with "[pt gho] ⧗") as "H1".
    { iNext. iFrame.
      iApply (persistent_time_receipt_mono with "⧖max"). lia.
    }
    iMod (fupd_mask_mono with "H1") as "[UniqBody H1]". { set_solver. }
    iIntros "H2". iSpecialize ("Halfback" with "H1 H2"). iMod (fupd_mask_mono with "Halfback") as "G". { solve_ndisj. }
    iModIntro. iFrame "G". 
    unfold ty_own.
    iExists (l, x1, ξi, d1, S d1, idx).
    iSplit. { iPureIntro. done. }
    iSplit; last by done.
    simpl.
    iSplit; first by done.
    iSplit. { iPureIntro. lia. }
    iFrame "ghopers UniqBody".
    leaf_goal laters to _; last by iFrame "PtBase". lia.
  Qed.
  
  Lemma read_uniq {𝔄} E L κ (ty: type 𝔄):
    Copy ty → lctx_lft_alive E L κ →
    typed_read E L (&uniq{κ} ty) ty (&uniq{κ} ty) uniq_bor_current (=).
  Proof.
    move=> Cpy Alv.
    intros x d v tid G Htimeless.
    iIntros "#LFT #E #GuardsL G [Gho %Phys] [£d £1]".
    destruct x as [[[[[l x0] ξi] d'] g'] idx].
    iDestruct "Gho" as "[#Incl [%Hineq [UniqBody [#PtBase Pers]]]]".
    rewrite uniq_body_unfold. iDestruct "UniqBody" as "(Tok & Credits & #Bor)".
    
    iMod (lctx_lft_alive_get_guards _ _ _ _ _ Alv with "GuardsL E G") as "[G #GuardsK]". { solve_ndisj. }
    
    assert (v = FVal #l.1) as Hvl. { inversion Phys. trivial. }
    subst v.
    
    iDestruct (uniq_tok_guard_payload ty x0 ξi d' g' idx κ tid l
      (uniq_tok x0 ξi d' g' idx ∗ G)%I 0 with "LFT Bor [] []") as "BigGuards5".
      { iApply guards_weaken_lhs_sep_r. iApply (guards_transitive with "GuardsL GuardsK"). }
      { iApply guards_weaken_sep_l. }
    
    iMod (guards_extract_persistent_later _ _ (ty_gho ty x0 d' g' tid)
        with "BigGuards5 [Tok G] []") as "J".
      { solve_ndisj. } { iFrame. } { iIntros "(? & ? & ?)". iFrame. }
    iMod (lc_fupd_elim_later with "£1 J") as "J". iMod "J" as "[[Tok G] #InnerGho]".
    iDestruct (guards_transitive with "GuardsL GuardsK") as "GGuardsK".
    iDestruct (guards_transitive_right with "GGuardsK PtBase") as "GGuardsPtBase".
    
    iDestruct (copy_concrete with "InnerGho") as "%Conc".
    
    iModIntro.
    iExists l. iExists (to_concrete (ty_phys ty x0 tid)). iExists (ty_phys ty x0 tid).
    iExists (uniq_tok x0 ξi d' g' idx ∗ G)%I.
    iSplit. { done. }
    iFrame "G". iFrame "Tok".
    iSplit. { iPureIntro. apply length_to_concrete. }
    iSplit. {
      iApply (guard_cloc_combine _ _ _ l with "[] []").
      - leaf_goal lhs to G; last by trivial.
        leaf_by_sep. iIntros "(? & ?)". iFrame. iIntros. done.
      - leaf_goal laters to 1. { lia. }
        iApply (guards_transitive_left with "BigGuards5 []").
        rewrite <- heap_complete_mapsto_fancy_fmap_eq.
        rewrite fmap_to_concrete.
         + leaf_by_sep. { iIntros "(A & B & C)". iFrame. iIntros. iFrame. }
         + inversion Cpy; trivial.
    }
    iSplitR. { iIntros.
        rewrite <- heap_complete_mapsto_fancy_fmap_eq.
        rewrite fmap_to_concrete. { iFrame. done. } inversion Cpy; trivial.
    }
    iSplit. { rewrite fmap_to_concrete; done. }
    iSplit. {
      unfold ty_own. simpl. iSplit; last by done.
      iNext. iDestruct (ty_gho_depth_mono with "InnerGho") as "[InnerGho' _]"; last by iFrame "InnerGho'". { lia. } { lia. }
    }
    iIntros "[Tok G]". iModIntro.
    iExists (l, x0, ξi, d', g', idx).
    iSplit; [done|]. iFrame "G".
    rewrite /ty_own /=. iSplit; [|done]. iFrame "Pers". iFrame "Incl PtBase". iSplit; [done|].
    rewrite uniq_body_unfold. iFrame "∗#".
  Qed.
  
  Lemma tctx_uniq_mod_ty_out {𝔄 𝔅 ℭl} κ (f : 𝔄 →ₛ 𝔅) (fⁱ: 𝔅 →ₛ 𝔄) ty (T: tctx ℭl) p E L
    `{!Isoₛ f fⁱ} : lctx_lft_alive E L κ →
    tctx_incl E L (p ◁ &uniq{κ} (<{f;fⁱ}> ty) +:: T) (p ◁ &uniq{κ} ty +:: T)
      (λ post '(bor -:: cl), λ mask π, ∀ bor' ,
        uniq_bor_loc bor' = uniq_bor_loc bor →
        uniq_bor_current bor' = fⁱ ~~$ₛ (uniq_bor_current bor) →
        uniq_bor_future bor' π = fⁱ $ₛ (uniq_bor_future bor π) →
        post (bor' -:: cl) mask π).
  Proof.
    intros Alv. split.
    { intros ?? Eq  [[??]?] ??. do 2 apply forall_proper=>?. split=>???; apply Eq; auto. }
    iIntros (G tid [x y] mask post Gtimeless) "#LFT #PROPH #UNIQ #E #GguardsL G /=[p T] Obs".
    leaf_open "GguardsL" with "G" as "[L back]". { set_solver. }
    iDestruct (Alv with "L E") as "#LguardsK". iMod ("back" with "L") as "G".
    iDestruct (guards_transitive with "GguardsL LguardsK") as "GguardsK".
    destruct x as [[[[[l x0] ξi] d'] g'] ξidx].
    iDestruct "p" as (v d) "[%Hp [#⧖ [[#Incl [%Hineq [UniqBody #Pers]]] %Hphys]]]".
    iMod (uniq_body_transform (<{f;fⁱ}> ty) ty x0 (fⁱ ~~$ₛ x0) d' g' ξi ξidx κ tid l l _ G f
        (λ d g, (d, g))
        with "LFT PROPH UNIQ [] GguardsK G UniqBody") as (ζi ζidx) "[Obs2 [UniqBody G]]". { set_solver. }
    {
      iIntros "[gho pt]". iModIntro. iFrame "gho". iFrame "pt". iIntros (x2 d2 g2) "(? & ? & ?)".
      simpl. rewrite semi_iso'. iModIntro. iFrame.
    }
    iCombine "Obs Obs2" as "#Obs".
    iModIntro. iExists ((l, (fⁱ ~~$ₛ x0), ζi, d', g', ζidx) -:: y).
    iFrame "G". iFrame "T". iSplit.
      { iExists v, d. iSplit. { done. } iFrame "⧖". iFrame. iFrame "#".
        iSplit; done. }
    iApply (proph_obs_impl with "Obs"). intros π [Ha Hb]. apply Ha; trivial.
    unfold uniq_bor_future. simpl.
    rewrite Hb.
    rewrite semi_iso'. trivial.
  Qed.

  Lemma tctx_uniq_eqtype {𝔄 𝔅 ℭl} κ (f: 𝔄 →ₛ 𝔅) (fⁱ: 𝔅 →ₛ 𝔄) ty ty' (T: tctx ℭl) p E L :
    eqtype E L ty ty' f fⁱ → Isoₛ f fⁱ → lctx_lft_alive E L κ →
    tctx_incl E L (p ◁ &uniq{κ} ty +:: T) (p ◁ &uniq{κ} ty' +:: T)
      (λ post '(bor -:: cl), λ mask π, ∀ bor' ,
          uniq_bor_loc bor' = uniq_bor_loc bor →
          uniq_bor_current bor' = f ~~$ₛ (uniq_bor_current bor) →
          uniq_bor_future bor' π = f $ₛ (uniq_bor_future bor π) →
          post (bor' -:: cl) mask π).
  Proof.
    intros Heqtype Hiso Alv. split.
    { intros ?? Eq  [[??]?] ??. do 2 apply forall_proper=>?. split=>???; apply Eq; auto. }
    iIntros (G tid [x y] mask post Gtimeless) "#LFT #PROPH #UNIQ #E #GguardsL G /=[p T] Obs".
    rewrite <- eqtype_unfold in Heqtype; last by trivial.
    
    leaf_open "GguardsL" with "G" as "[L back]". { set_solver. }
    iDestruct (Heqtype with "L E") as "(%Hsizeeq & #Hlfts & #EqGho & #EqPers & %EqPhys)".
    iDestruct (Alv with "L E") as "#LguardsK".
    iMod ("back" with "L") as "G".
    
    destruct x as [[[[[l x0] ξi] d'] g'] ξidx].
    iDestruct "p" as (v d) "[%Hp [#⧖ [[#Incl [%Hineq [UniqBody [#Pers #Bdead]]]] %Hphys]]]".
    
    iDestruct (guards_transitive with "GguardsL LguardsK") as "GguardsK".
    
    iMod (uniq_body_transform ty ty' x0 (f ~~$ₛ x0) d' g' ξi ξidx κ tid l l _ G fⁱ (λ d g, (d, g))
      with "LFT PROPH UNIQ [] GguardsK G UniqBody") as (ζi ζidx) "[Obs2 [UniqBody G]]". { set_solver. }
    {
      iIntros "[gho pt]". iModIntro.
      iDestruct ("EqGho" with "gho") as "$".
      rewrite EqPhys. iFrame "pt".
      iIntros (x2 d2 g2) "(gho & pt & ⧖')".
      iModIntro. simpl.
        rewrite EqPhys. rewrite semi_iso'. iFrame.
        iApply ("EqGho"). rewrite semi_iso'. iFrame.
    }
    iCombine "Obs Obs2" as "#Obs".
    iModIntro. iExists ((l, (f ~~$ₛ x0), ζi, d', g', ζidx) -:: y).
    iFrame "G". iFrame "T". iSplit.
      { iExists v, d. iSplit. { done. } iFrame "⧖". iFrame.
        iDestruct "Hlfts" as "[H1 H2]".
        iSplit.
          - iSplit. { iApply (guards_transitive with "Incl H1"). }
            iSplit. { done. }
            iFrame "Pers".
            iDestruct "Bdead" as "[$|pers]". iRight. iDestruct ("EqPers" with "pers") as "$".
          - done.
      }
    iApply (proph_obs_impl with "Obs"). intros π [Ha Hb]. apply Ha; trivial.
    unfold uniq_bor_future. simpl.
    rewrite Hb.
    rewrite semi_iso'. trivial.
  Qed.

  Lemma tctx_extract_uniq_eqtype {𝔄 𝔅 ℭl} κ (f: 𝔅 →ₛ 𝔄) (fⁱ: 𝔄 →ₛ 𝔅) ty ty' (T: tctx ℭl) p E L :
    lctx_lft_alive E L κ → eqtype E L ty' ty f fⁱ → Isoₛ f fⁱ →
    tctx_extract_elt E L (p ◁ &uniq{κ} ty) (p ◁ &uniq{κ} ty' +:: T) T
    (λ post '(bor -:: cl), λ mask π, ∀ bor' ,
          uniq_bor_loc bor' = uniq_bor_loc bor →
          uniq_bor_current bor' = f ~~$ₛ (uniq_bor_current bor) →
          uniq_bor_future bor' π = f $ₛ (uniq_bor_future bor π) →
          post (bor' -:: cl) mask π).
  Proof. move=> ???. by eapply tctx_uniq_eqtype. Qed.
End typing.

Global Hint Resolve uniq_resolve uniq_subtype uniq_eqtype
  : lrust_typing.

(* Registering [write_uniq]/[read_uniq] to [Hint Resolve]
  doesnt't help automation in some situations,
  but the following hints let automation work *)
Global Hint Extern 0 (typed_write _ _ (&uniq{_} _) _ _ _ _ _) =>
  simple apply write_uniq : lrust_typing.
Global Hint Extern 0 (typed_read _ _ (&uniq{_} _) _ _ _ _) =>
  simple apply read_uniq : lrust_typing.

(*Global Hint Resolve tctx_extract_uniq_eqtype | 5 : lrust_typing.*)
