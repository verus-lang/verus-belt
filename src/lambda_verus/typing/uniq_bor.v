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
    
    ty_gho_own (x : ~~ (uniq_borₛ 𝔄)) d g tid :=
      κ ⊑ ty_lft ty ∗
      match x with
        (l, x0, ξi, d', g', idx) =>
          ⌜S d' ≤ d ∧ g' ≤ g⌝ ∗ uniq_body ty x0 ξi d' g' idx κ tid l
            ∗ (@[κ] &&{↑NllftG; g+1}&&> l #↦∗_)
      end;
    
    (* The persistent predicate does not contain the persistent predicate of the
       referent: the referent can change while [&uniq] is reborrowed, and the
       persistent predicate of its final value is not available when the reborrow
       ends (see [uniq_body_reborrow]). Where the persistent predicate of the referent
       is needed (in [ty_shr_guard_proph]), it comes from the sharing predicate. *)
    ty_gho_pers (x: ~~ (uniq_borₛ 𝔄)) d g tid :=
      match x with
        (l, x0, ξi, d', g', idx) =>
            ⌜S d' ≤ d ∧ g' ≤ g⌝
              ∗ uniq_body_pers_component ty x0 ξi d' g' idx κ tid l
      end;
      
    ty_phys (x : ~~ (uniq_borₛ 𝔄)) tid :=
      match x with
        (l, x0, ξi, d', g', idx) =>
            [FVal (LitV l.1)]
      end;
    
    (* The sharing predicate is structural: sharing [&uniq{κ} ty] at κ0 gives shared
       access to the referent at [κ0 ⊓ κ]. The guard of the token of the prophecy
       variable is what [ty_shr_guard_proph] needs for it. The guards have [g+1]
       laters and the sharing predicate of the referent is at depth [g] (rather than
       the [g'] of the value), so that lifetime monotonicity can absorb the laters of a
       lifetime inclusion into [g] (see [ty_shr_lft_mono]).
       The sharing predicate also records the persistent predicate of the referent,
       which [ty_shr_guard_proph] of the referent needs. It is under two laters, since
       the sharing predicate of a type constructor may only depend on the persistent
       predicate of its argument two steps later (see [TypeContractive]); this is what
       the budget [d*(g+2)] of laters in [ty_shr_guard_proph] pays for. *)
    ty_shr κ0 (x : ~~ (uniq_borₛ 𝔄)) d g tid :=
      match x with
        (l, x0, ξi, d', g', idx) =>
          ⌜S d' ≤ d ∧ g' ≤ g⌝ ∗
          (@[κ0 ⊓ κ] &&{↑NllftG; g+1}&&> l.1 ↦[^ l.2]!∗ ty.(ty_phys) x0 tid) ∗
          (@[κ0 ⊓ κ] &&{↑NllftG; g+1}&&> 1:[uniq_prvar x0 ξi]) ∗
          ▷ ty.(ty_shr) (κ0 ⊓ κ) x0 d' g tid ∗
          ▷ ▷ ty.(ty_gho_pers) x0 d' g' tid
      end;
  |}%I.
  Next Obligation. intros ? ? ? x. destruct x as [[[[[[l ?] ?] ?] ?] ?] ?]. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. intros ? ? ? x. destruct x as [[[[[[l ?] ?] ?] ?] ?] ?]. done. Qed.
  Next Obligation. intros 𝔄 κ ty d0 g0 d1 g1 x tid Hle Hle2. simpl.
    destruct x as [[[[[l x0] ξi] d'] g'] idx].
    iIntros "[#A [%B [C #D]]]".
    iDestruct (lguards_weaken_later _ _ _ _ (g1+1) with "D") as "D'". { lia. }
    iFrame. iFrame "#".
    iSplit. { iPureIntro. lia. } iIntros "[#A1 [%B1 [C1 D1]]]". iFrame. iFrame "#". done.
  Qed.
  Next Obligation. intros 𝔄 κ ty d0 g0 d1 g1 x tid Hle Hle2. simpl.
    destruct x as [[[[[l x0] ξi] d'] g'] idx].
    iIntros "[%B C]". iFrame. iPureIntro. lia.
  Qed.
  Next Obligation.
    destruct x as [[[[[l x0] ξi] d'] g'] idx]. fold indep_interp_of_syn_type. simpl.
    typeclasses eauto.
  Qed.
  Next Obligation.
    destruct x as [[[[[l x0] ξi] d'] g'] idx]. fold indep_interp_of_syn_type. simpl.
    intros d g tid. iIntros "[A [B [C D]]]". iFrame. iApply uniq_body_pers_component_impl.
    iFrame.
  Qed.
  Next Obligation.
    destruct x as [[[[[l x0] ξi] d'] g'] idx]. fold indep_interp_of_syn_type. simpl.
    typeclasses eauto.
  Qed.
  Next Obligation.
    intros 𝔄 κ ty κ0 κ1 x n d g tid. destruct x as [[[[[l x0] ξi] d'] g'] idx]. simpl.
    iIntros "#Incl ([%Le1 %Le2] & #Pt & #Tok & Shr & #Pers)".
    iAssert (@[κ1 ⊓ κ] &&{↑NllftG; n}&&> @[κ0 ⊓ κ])%I as "#Incl'".
    { iApply guards_llft_glb.
      - leaf_goal laters to (0 + n). { lia. }
        iApply (guards_transitive_additive with "[] Incl"). iApply llftl_intersect_incl_l.
      - leaf_goal laters to 0. { lia. } iApply llftl_intersect_incl_r. }
    iSplit. { iPureIntro. lia. }
    replace (g + n + 1) with (n + (g + 1)) by lia.
    iSplit; [iApply (guards_transitive_additive with "Incl' Pt")|].
    iSplit; [iApply (guards_transitive_additive with "Incl' Tok")|].
    iSplitL; [iNext; iApply (ty_shr_lft_mono with "Incl' Shr")|done].
  Qed.
  Next Obligation.
    intros 𝔄 κ ty κ0 d g d1 g1 x tid ??. destruct x as [[[[[l x0] ξi] d'] g'] idx]. simpl.
    iIntros "(%Le & Pt & Tok & Shr & Pers)". iSplit; [iPureIntro; lia|].
    iSplitL "Pt". { leaf_goal laters to (g+1). { lia. } iFrame "Pt". }
    iSplitL "Tok". { leaf_goal laters to (g+1). { lia. } iFrame "Tok". }
    iFrame "Pers". iNext. iApply (ty_shr_depth_mono with "Shr"); lia.
  Qed.
  Next Obligation.
    intros 𝔄 κ ty E κ0 x d g tid G ??. destruct x as [[[[[l x0] ξi] d'] g'] idx]. simpl.
    iIntros "#LFT #Incl0 #Pers #Gκ0 G Bor".
    iDestruct "Pers" as "([%Le1 %Le2] & #IdxBor)".
    iAssert (κ0 ⊑ κ)%I as "#Hκ0κ".
    { iApply (llftl_incl_trans with "Incl0"). iApply llftl_intersect_incl_l. }
    iAssert (κ0 ⊓ κ ⊑ ty_lft ty)%I as "#Incl'".
    { iApply (llftl_incl_trans with "[]"); [iApply llftl_intersect_incl_l|].
      iApply (llftl_incl_trans with "Incl0"). iApply llftl_intersect_incl_r. }
    iAssert (G &&{↑NllftG}&&> @[κ0 ⊓ κ])%I as "#Gκ".
    { iApply guards_llft_glb; [done|]. iApply (guards_transitive with "Gκ0 Hκ0κ"). }
    (* Unnest the borrow of the payload, at [κ0 ⊓ κ]. *)
    iMod (llftl_sep_split with "LFT Bor") as "[_ Bor]"; [solve_ndisj|].
    iMod (llftl_sep_split with "LFT Bor") as "[_ Bor]"; [solve_ndisj|].
    iMod (llftl_sep_split with "LFT Bor") as "[Body Rest]"; [solve_ndisj|].
    iMod (llftl_bor_guarded_extract _ _ _ _ (@[κ] &&{↑NllftG; g+1}&&> l #↦∗_)
      with "LFT Gκ0 G Rest []") as "(G & _ & #PtBase)"; [solve_ndisj| |].
    { iIntros "!> $". }
    iDestruct (llftl_bor_iff _ _ (uniq_tok x0 ξi d' g' idx ∗
      (⧗1 ∗ uniq_body_pers_component ty x0 ξi d' g' idx κ tid l)) with "[] Body") as "Body".
    { iIntros "!> !>". rewrite uniq_body_unfold. iSplit; iIntros "$". }
    iMod (llftl_sep_split with "LFT Body") as "[Tok _]"; [solve_ndisj|].
    iMod (proph_bor_tok_share with "LFT IdxBor Tok") as "[PBor #TokG]"; [solve_ndisj|].
    iDestruct (llftl_bor_iff _ _ (|={lazyE}=> (⧖(S d' `max` g') ∗
      ty.(ty_gho_own) x0 d' g' tid ∗ l #↦!∗ ty.(ty_phys) x0 tid)) with "[] PBor")
      as "PBor".
    { iIntros "!> !>". rewrite uniq_payload_cell. iSplit; iIntros "$". }
    (* Open the borrow of the lazy contents before the step, run the lazy update after
       the step (which also gives the persistent predicate of the contents), and close
       the borrow with the non-lazy contents. *)
    iMod (llftl_bor_acc_guarded with "LFT PBor Gκ G") as "[Upd Close]"; [solve_ndisj|].
    iModIntro. iApply (step_fupdN_nmono (S d')); [lia|]. simpl.
    iModIntro. iNext.
    iMod (fupd_mask_mono with "Upd") as "(#⧖ & Gho & Pt)"; [rewrite /lazyE; solve_ndisj|].
    iDestruct (ty_gho_pers_impl with "Gho") as "#InnerPers".
    iMod (fupd_mask_subseteq (↑Nllft)) as "Upd"; [solve_ndisj|].
    iMod ("Close" $! (ty.(ty_gho_own) x0 d' g' tid ∗ l #↦!∗ ty.(ty_phys) x0 tid)%I
      with "[Gho Pt]") as "[PBor G]".
    { iSplitR; [|iNext; iFrame]. iIntros "!> GP !> !>". iModIntro. by iFrame "⧖ GP". }
    iMod "Upd" as "_".
    iMod (llftl_sep_split with "LFT PBor") as "[Gho Pt]"; [solve_ndisj|].
    iMod (llftl_bor_guard with "LFT Pt") as "#Pt"; [solve_ndisj|].
    iMod (ty_share with "LFT Incl' InnerPers Gκ G Gho") as "Upd"; [solve_ndisj|].
    iModIntro. iApply (step_fupdN_wand with "Upd"). iIntros ">[$ Shr] !>".
    iSplit; [iPureIntro; lia|].
    iSplitR "Shr"; last first.
    { iSplitR. { leaf_goal laters to 1. { lia. } iFrame "TokG". }
      iSplitL; [iNext; iApply (ty_shr_depth_mono with "Shr"); lia|]. by iFrame "InnerPers". }
    iApply guard_cloc_combine_fancy.
    - iApply (guards_transitive_right with "[] PtBase"). iApply llftl_intersect_incl_r.
    - leaf_goal laters to 1. { lia. } iFrame "Pt".
  Qed.
  Next Obligation.
    intros 𝔄 κ ty κ0 x n d g tid ξ R. destruct x as [[[[[l x0] ξi] d'] g'] idx]. simpl.
    intros Hin.
    iIntros "#LFT #Incl0 _ ([%Le1 %Le2] & _ & #TokG & #Shr & #InnerPers)".
    iAssert (κ0 ⊑ κ)%I as "#Hκ0κ".
    { iApply (llftl_incl_trans with "Incl0"). iApply llftl_intersect_incl_l. }
    iAssert (κ0 ⊓ κ ⊑ ty_lft ty)%I as "#Incl'".
    { iApply (llftl_incl_trans with "[]"); [iApply llftl_intersect_incl_l|].
      iApply (llftl_incl_trans with "Incl0"). iApply llftl_intersect_incl_r. }
    rewrite elem_of_cons in Hin. destruct Hin as [->|Hin].
    - iApply bi.laterN_intro. iIntros "#Rκ".
      leaf_goal laters to (n + (g + 1)). { nia. }
      iApply (guards_transitive_additive with "[] TokG").
      iApply guards_llft_glb; [done|]. iApply (guards_transitive_left with "Rκ Hκ0κ").
    - (* Two laters for the persistent predicate of the referent, then the laters of
         the referent. *)
      iApply (bi.laterN_le (S (S (d' * (g + 2))))). { nia. }
      iNext. iNext.
      iDestruct (ty_gho_pers_depth_mono _ _ _ d' g with "InnerPers") as "#InnerPers'";
        [lia..|].
      iDestruct (ty_shr_guard_proph ty (κ0 ⊓ κ) x0 n d' g tid ξ R Hin
        with "LFT Incl' InnerPers' Shr") as "GP".
      iNext. iIntros "#Rκ". leaf_goal laters to (n + (d'+1)*(g+1)). { nia. }
      iApply "GP". iApply guards_llft_glb; [done|].
      iApply (guards_transitive_left with "Rκ Hκ0κ").
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
        + do 2 f_equiv. apply uniq_body_ne; intros; apply Heqv.
     - intros x d g tid. destruct x as [[[[[l x0] ξi] d'] g'] idx]. simpl. f_equiv.
       apply uniq_pers_component_ne; intros; apply Heqv.
     - intros x tid. done.
     - intros κ0 x d g tid. destruct x as [[[[[l x0] ξi] d'] g'] idx]. simpl.
       destruct Heqv as [_ _ _ _ EqPers EqPhys EqShr]. rewrite EqPhys.
       do 4 f_equiv; [f_equiv; apply EqShr|]. do 2 f_equiv. apply EqPers.
  Qed.
End uniq_bor.

Notation "&uniq{ κ }" := (uniq_bor κ) (format "&uniq{ κ }") : lrust_type_scope.

Section typing.
  Context `{!typeG Σ}.

  Global Instance uniq_type_contractive {𝔄} κ : TypeContractive (uniq_bor (𝔄:=𝔄) κ).
  Proof.
    split; [by apply (type_lft_morphism_add_one κ)|done| | | |].
     - intros n ty ty' Heq Heq1 Heq2 Heq3 Heq4 Heq5 _ x d g tid.
       destruct x as [[[[[l x0] ξi] d'] g'] idx]. simpl. f_equiv.
        + apply equiv_dist. iDestruct Heq1 as "#[??]".
          iSplit; iIntros "#H"; (iApply llftl_incl_trans; [iApply "H"|done]).
        + do 2 f_equiv.
          apply uniq_body_contractive; intros; [apply Heq3|apply Heq4|apply Heq5].
     - intros n ty ty' Heq Heq1 Heq2 Heq3 Heq4 Heq5 _ x d g tid.
       destruct x as [[[[[l x0] ξi] d'] g'] idx]. simpl. f_equiv.
       apply uniq_pers_component_contractive; intros; [apply Heq3|apply Heq4|apply Heq5].
     - intros ???? x tid. by destruct x as [[[[[l x0] ξi] d'] g'] idx].
     - intros n ty ty' _ _ _ _ EqPers EqPhys EqShr κ0 x d g tid.
       destruct x as [[[[[l x0] ξi] d'] g'] idx]. simpl. rewrite EqPhys.
       do 3 f_equiv. f_equiv; [apply later_contractive; apply EqShr|].
       (* The persistent predicate of the referent is only [pred n]-close, hence the
          two laters. *)
       apply later_contractive. destruct n as [|n]; [apply dist_later_0|]. apply dist_later_S.
       apply later_contractive. apply EqPers.
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
    iIntros "#LFT #UNIQ #TIME Hg H Gg G (Incl & %Ineqs & UniqBody & Pt) ⧖o".
    destruct d; first by lia.
    simpl.
    iMod (uniq_body_acc_rebody ty x0 ξi d' g' idx static tid l _ (uniq_payload ty tid' l)
      with "LFT UNIQ [] UniqBody") as "Acc". { set_solver. }
      { iApply llftl_tok_unit. }
    iModIntro. iNext. iMod "Acc" as "(Lazy & ⧗ & Close)".
    iMod (fupd_mask_mono with "Lazy") as "(⧖ & Gho & Pt1)"; [rewrite /lazyE; solve_ndisj|].
    iCombine "⧖o ⧖" as "⧖max".
    iDestruct (send_change_tid tid tid' x0 d' g' G H κs _ _ TG TH with "LFT UNIQ TIME Hg H Gg G Gho ⧖max") as "J". Unshelve. 2: { lia. }
    iModIntro.
    iApply (step_fupdN_le d'). { lia. } { solve_ndisj. }
    iApply (step_fupdN_wand with "J"). iFrame.
    iIntros "gho". iMod "gho" as (x' off) "[gho [#⧖off [%Habstract [G H]]]]".
    iMod (fupd_mask_subseteq (↑Nllft)) as "Upd"; first solve_ndisj.
    iMod ("Close" $! (uniq_cell x' (d'+off) g') with "[Pt1 gho] []") as (idx2) "[Bor Alive]".
    { iApply uniq_payload_intro_later. iNext.
      rewrite (send_change_tid_phys tid tid' x0 x'); [|symmetry; trivial].
      iFrame "gho Pt1". iApply (persistent_time_receipt_mono with "⧖off"). lia. }
    { iNext. iIntros (c2) "[_ static]". iExFalso. iApply (llftl_end_unit with "static"). }
    iMod "Upd" as "_".
    iDestruct (uniq_body_make ty x' x0 with "Bor ⧗") as "UBody".
    iModIntro.
    iExists (l, x', ξi, d'+off, g', idx2), off. iFrame.
    iSplit.
      + iPureIntro; lia.
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
    destruct (SyncTy tid tid' x0 d g) as [Hphys [Hgho [Hpers _]]].
    split. { done. }
    have Hg: ∀ x d g, ty.(ty_gho_own) x d g tid ⊣⊢ ty.(ty_gho_own) x d g tid'.
    { intros. apply SyncTy. }
    have Hps: ∀ x d g, ty.(ty_gho_pers) x d g tid ⊣⊢ ty.(ty_gho_pers) x d g tid'.
    { intros. apply SyncTy. }
    have Hp: ∀ x, ty.(ty_phys) x tid = ty.(ty_phys) x tid'.
    { intros x. apply (SyncTy tid tid' x 0 0). }
    split. { unfold uniq_bor, ty_gho_own. do 3 f_equiv. by apply uniq_body_proper. }
    split. { unfold uniq_bor, ty_gho_pers. f_equiv. by apply uniq_pers_component_proper. }
    intros κ0. simpl. destruct (SyncTy tid tid' x0 d' g) as [H'phys [_ [_ H'shr]]].
    destruct (SyncTy tid tid' x0 d' g') as [_ [_ [H'pers _]]].
    by rewrite H'phys H'shr H'pers.
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
    iIntros "#LFT PROPH UNIQ TIME E #Lguard G [In uniq]".
    destruct x as [[[[[l x0] ξi] d'] g'] idx].
    iDestruct "uniq" as "[%Hle [uniq pers]]".
    (* Settle the borrow first, with a program step, to get the time receipt of its
       contents, which pays for the later credits of the resolution. *)
    leaf_open "Lguard" with "G" as "[L Back]". { solve_ndisj. }
    iDestruct (Alive with "L E") as "#Alv".
    iMod ("Back" with "L") as "G".
    iDestruct (guards_transitive with "Lguard Alv") as "#Gk".
    destruct d as [|d0]; [lia|].
    replace (S d0 * (g + 1)) with (S (d0 * (g + 1) + g)) by lia.
    iModIntro. simpl.
    iMod (uniq_body_settle_step _ _ _ _ _ _ _ _ _ F G with "LFT Gk uniq G") as "Upd";
      [rewrite /lazyE; solve_ndisj|].
    iModIntro. iNext. iMod "Upd" as "(#⧖ & uniq & G)".
    iMod (resolve_uniq_body with "LFT PROPH UNIQ TIME In E Lguard G ⧖ uniq") as "[X [G _]]".
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
    iDestruct ("Eqt" with "E") as (?) "[[Lfts1 Lfts2][#EqOwn [#EqPers [%EqPhys #EqShr]]]]".
    iSpecialize ("In" with "E").
    iSplit; [done|]. iSplit; [by iApply lft_intersect_mono|].
    iSplit. {
      iModIntro. iIntros (x d g tid) "[#Incl gho]".
      destruct x as [[[[[l x0] ξi] d'] g'] idx].
      iDestruct "gho" as "[#Hineq [UniqBody #PtBase]]".
      iDestruct (uniq_body_pers_component_impl with "UniqBody") as "#Saved".
      iDestruct (incl_uniq_body ty ty' x0 ξi d' g' with "In EqOwn EqPers [] UniqBody") as "UniqBody".
      { done. }
      iDestruct (guards_transitive with "In Incl") as "Incl'".
      iDestruct (guards_transitive with "Incl' Lfts1") as "Incl''".
      iFrame "UniqBody Incl'' Hineq".
      iSplit. { iApply (guards_transitive_right with "In PtBase"). }
      iIntros "[Hincl'' [Hineq'' [UniqBody _]]]".
      iFrame "#".
      rewrite !uniq_body_unfold.
      iDestruct "UniqBody" as "(Tok & ⧗ & _)". iFrame "Tok ⧗ Saved".
    }
    iSplit. {
      iModIntro. iIntros (x d g tid) "#Pers".
      destruct x as [[[[[l x0] ξi] d'] g'] idx].
      iDestruct "Pers" as "[A C]".
      iFrame "#".
      iApply (incl_uniq_body_pers_component with "In EqOwn EqPers [] C").
      done.
    }
    iSplit; [done|].
    iIntros "!>" (κ0 x d g tid) "Shr". destruct x as [[[[[l x0] ξi] d'] g'] idx]. simpl.
    iDestruct "Shr" as "($ & Pt & Tok & Shr & #Pers)".
    iAssert (κ0 ⊓ κ' ⊑ κ0 ⊓ κ)%I as "#Incl'".
    { iApply llftl_incl_glb; [iApply llftl_intersect_incl_l|].
      iApply llftl_incl_trans; [iApply llftl_intersect_incl_r|done]. }
    rewrite EqPhys.
    iSplit; [iApply (guards_transitive_right with "Incl' Pt")|].
    iSplit; [iApply (guards_transitive_right with "Incl' Tok")|].
    iSplitL; [iNext; iApply (ty_shr_lft_mono0 with "Incl'"); by iApply "EqShr"|].
    iNext. iNext. by iApply "EqPers".
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
    iDestruct "Gho" as "[#Incl [%Hineq [UniqBody #PtBase]]]".
    iMod (lctx_lft_alive_get_guards _ _ _ _ _ Alv with "GuardsL E G") as "[G #GuardsK]".
      { solve_ndisj. }
    iDestruct (guards_transitive with "GuardsL GuardsK") as "#G_Guards_K".
    iMod (fractional.frac_split_guard_in_half with "G G_Guards_K") as (γ2) "[H1 [H2 [#Ghalf #Halfback]]]". { solve_ndisj. }
    iMod (uniq_body_acc with "LFT UNIQ Ghalf UniqBody H1") as "(P & ⧗ & Gback)".
      { solve_ndisj. }
    iRename "P" into "Lazy".
    destruct d as [|d]. { lia. }
    iModIntro. iExists l. iExists d. iExists (fractional.half γ2).
    assert (v = FVal #(l.1)) as Hvl. { inversion Phys. trivial. }
    subst v.
    iSplit; first by done.
    iSplit; first by done.
    iSplitL "Lazy". {
      iNext. iMod (fupd_mask_mono with "Lazy") as "(_ & gho & pt)"; [rewrite /lazyE; solve_ndisj|].
      iModIntro. iExists (ty_phys ty x0 tid).
      iFrame "pt". simpl. unfold ty_own.
      iSplit; last by done.
      iDestruct (ty_gho_own_depth_mono with "gho") as "[gho _]"; last by iFrame "gho".
      { lia. } { lia. }
    }
    iFrame "H2". iSplit. { iApply (guards_transitive_right with "Ghalf PtBase"). }
    iIntros (x1 d1) "pt #⧖1 £new".
    iRename "⧖1" into "⧖max".
    iDestruct "pt" as (lv) "[>pt [gho #>%phys]]". subst lv.
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
    iFrame "UniqBody".
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
    iDestruct "Gho" as "[#Incl [%Hineq [UniqBody #PtBase]]]".
    iMod (lctx_lft_alive_get_guards _ _ _ _ _ Alv with "GuardsL E G") as "[G #GuardsK]". { solve_ndisj. }
    assert (v = FVal #l.1) as Hvl. { inversion Phys. trivial. }
    subst v.
    iDestruct (guards_transitive with "GuardsL GuardsK") as "#GGuardsK".
    iMod (fractional.frac_split_guard_in_half with "G GGuardsK") as (γ) "[H1 [H2 [#Ghalf #Halfback]]]".
    { solve_ndisj. }
    (* Open the borrow and run the lazy update of the payload; the points-to is put in
       the guarding proposition for the read. *)
    iMod (uniq_body_acc_keep with "LFT Ghalf £1 UniqBody H1") as "(#⧖ & #InnerGho & Pt & Close)".
    { rewrite /lazyE. solve_ndisj. }
    iDestruct (copy_concrete with "InnerGho") as "%Conc".
    iModIntro.
    iExists l. iExists (to_concrete (ty_phys ty x0 tid)). iExists (ty_phys ty x0 tid).
    iExists (fractional.half γ ∗ l #↦!∗ ty_phys ty x0 tid)%I.
    iSplit. { done. }
    iFrame "H2 Pt".
    iSplit. { iPureIntro. apply length_to_concrete. }
    iSplit. {
      iApply (guard_cloc_combine _ _ _ l with "[] []").
      - iApply guards_weaken_lhs_sep_l. iApply (guards_transitive_right with "Ghalf PtBase").
      - leaf_goal laters to 0. { lia. }
        rewrite <- heap_complete_mapsto_fancy_fmap_eq.
        rewrite fmap_to_concrete; [|done]. iApply guards_weaken_sep_r.
    }
    iSplitR. { iIntros.
        rewrite <- heap_complete_mapsto_fancy_fmap_eq.
        rewrite fmap_to_concrete. { iFrame. done. } inversion Cpy; trivial.
    }
    iSplit. { rewrite fmap_to_concrete; done. }
    iSplit. {
      unfold ty_own. simpl. iSplit; last by done.
      iNext. iDestruct (ty_gho_own_depth_mono with "InnerGho") as "[InnerGho' _]"; last by iFrame "InnerGho'". { lia. } { lia. }
    }
    iIntros "[H2 Pt]".
    iDestruct ("Close" with "[Pt]") as "Close". { iNext. iFrame "InnerGho Pt". }
    iMod (fupd_mask_mono with "Close") as "[UniqBody H1]"; [solve_ndisj|].
    iDestruct ("Halfback" with "H1 H2") as "G".
    iMod (fupd_mask_mono with "G") as "G"; [solve_ndisj|].
    iModIntro.
    iExists (l, x0, ξi, d', g', idx).
    iSplit; [done|]. iFrame "G".
    rewrite /ty_own /=. iSplit; [|done]. iFrame "UniqBody". iFrame "Incl PtBase". done.
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
    iMod (uniq_body_transform_lazy (<{f;fⁱ}> ty) ty x0 (fⁱ ~~$ₛ x0) d' g' ξi ξidx κ tid l l _ G f
        with "LFT PROPH UNIQ [] [] GguardsK G UniqBody") as (ζi ζidx) "[Obs2 [UniqBody G]]".
    { set_solver. }
    { by iIntros "[$ $] !>". }
    { iIntros (x2 d2 g2) "[? ?] !>". simpl. rewrite semi_iso'. iFrame. }
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
    iDestruct (Heqtype with "L E") as "#(%Hsizeeq & #Hlfts & #EqGho & #EqPers & %EqPhys & _)".
    iDestruct (Alv with "L E") as "#LguardsK".
    iMod ("back" with "L") as "G".
    
    destruct x as [[[[[l x0] ξi] d'] g'] ξidx].
    iDestruct "p" as (v d) "[%Hp [#⧖ [[#Incl [%Hineq [UniqBody #Pers]]] %Hphys]]]".
    
    iDestruct (guards_transitive with "GguardsL LguardsK") as "GguardsK".
    
    iMod (uniq_body_transform_lazy ty ty' x0 (f ~~$ₛ x0) d' g' ξi ξidx κ tid l l _ G fⁱ
      with "LFT PROPH UNIQ [] [] GguardsK G UniqBody") as (ζi ζidx) "[Obs2 [UniqBody G]]".
    { set_solver. }
    { iIntros "[gho pt] !>". iDestruct ("EqGho" with "gho") as "$".
      rewrite EqPhys. iFrame "pt". }
    { iIntros (x2 d2 g2) "[gho pt] !>". simpl.
      rewrite EqPhys. rewrite semi_iso'. iFrame.
      iApply ("EqGho"). rewrite semi_iso'. iFrame. }
    iCombine "Obs Obs2" as "#Obs".
    iModIntro. iExists ((l, (f ~~$ₛ x0), ζi, d', g', ζidx) -:: y).
    iFrame "G". iFrame "T". iSplit.
      { iExists v, d. iSplit. { done. } iFrame "⧖". iFrame.
        iDestruct "Hlfts" as "[H1 H2]".
        iSplit.
          - iSplit. { iApply (guards_transitive with "Incl H1"). }
            iSplit. { done. }
            iFrame "Pers".
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
