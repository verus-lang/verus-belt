From lrust.typing Require Export type.
From lrust.typing Require Import type_context programs mod_ty uniq_util own.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

(** * Unique borrows of bytes (stage 4 of the MiniRust memory model)

[&uniq{κ} ty] is [&uniq{κ} ty] (of [typing/uniq_bor.v]) with the body of
[typing/uniq_util.v]: the referent owns bytes that represent its value ([cbytes]).
It is the parent type of the referents of the byte place machinery
([typing/bplace/]). *)

Implicit Type 𝔄 𝔅: syn_type.

Section uniq_bytes.
  Context `{!typeG Σ}.

  Program Definition uniq_bytes {𝔄} (κ: lft) (ty: type 𝔄) : type (uniq_borₛ 𝔄) := {|
    ty_size := 1;  
    ty_lfts := κ :: ty.(ty_lfts);  
    ty_E := ty.(ty_E) ++ ty_outlives_E ty κ;
    
    ty_gho_own (x : ~~ (uniq_borₛ 𝔄)) d g tid :=
      κ ⊑ ty_lft ty ∗
      match x with
        (l, x0, ξi, d', g', idx) =>
          ⌜S d' ≤ d ∧ g' ≤ g⌝ ∗ uniq_body ty x0 ξi d' g' idx κ tid l
      end;

    (* The resolved ownership: either the borrow has not been resolved (its body is
       kept: resolving needs κ to be alive, which is not known when an arbitrary value
       is resolved by [resolve_keep_just], e.g. at a dead κ), or the prophecy variable
       has been resolved, and the referent has been shared at κ ([resolve_uniq_body]):
       a guard of its bytes, its sharing predicate and its persistent predicate, i.e.
       the ownership of [&shr{κ} ty] at the current value of the referent (see
       [res_leaf_uniq_to_shr]). *)
    ty_gho_res (x : ~~ (uniq_borₛ 𝔄)) d g tid :=
      κ ⊑ ty_lft ty ∗
      match x with
        (l, x0, ξi, d', g', idx) =>
          ⌜S d' ≤ d ∧ g' ≤ g⌝ ∗
            (uniq_body ty x0 ξi d' g' idx κ tid l ∨
             (@[κ] &&{↑NllftG; 1}&&> cbytes ty x0 l) ∗
             ty.(ty_shr) κ x0 d' g' tid ∗ ty.(ty_gho_pers) x0 d' g' tid)
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
      
    ty_mty := syn_mty _; ty_val := syn_val; ty_mty_eq := eq_refl; ty_val_eq _ := eq_refl;
    ty_fval := syn_fval; ty_fval_eq _ := eq_refl;
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
          (@[κ0 ⊓ κ] &&{↑NllftG; g+1}&&> cbytes ty x0 l) ∗
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
    iIntros "[#A [%B C]]".
    iFrame. iFrame "#".
    iSplit. { iPureIntro. lia. } iIntros "[#A1 [%B1 C1]]". iFrame. iFrame "#". done.
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
    intros d g tid. iIntros "[A [B C]]". iFrame "B".
    iApply (uniq_body_pers_component_impl with "C").
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
    iDestruct "Pers" as "([%Le1 %Le2] & (%κpp & _ & #IdxBor))".
    iAssert (κ0 ⊑ κ)%I as "#Hκ0κ".
    { iApply (llftl_incl_trans with "Incl0"). iApply llftl_intersect_incl_l. }
    iAssert (κ0 ⊓ κ ⊑ ty_lft ty)%I as "#Incl'".
    { iApply (llftl_incl_trans with "[]"); [iApply llftl_intersect_incl_l|].
      iApply (llftl_incl_trans with "Incl0"). iApply llftl_intersect_incl_r. }
    iAssert (G &&{↑NllftG}&&> @[κ0 ⊓ κ])%I as "#Gκ".
    { iApply guards_llft_glb; [done|]. iApply (guards_transitive with "Gκ0 Hκ0κ"). }
    (* Unnest the borrow of the payload, at [κ0 ⊓ κ]. *)
    iMod (llftl_sep_split with "LFT Bor") as "[_ Bor]"; [solve_ndisj|].
    iMod (llftl_sep_split with "LFT Bor") as "[_ Body]"; [solve_ndisj|].
    rewrite uniq_body_unfold.
    iMod (llftl_bor_freeze with "LFT Body") as (κp) "Body"; [solve_ndisj|].
    iMod (llftl_bor_freeze with "LFT Body") as (γ) "Body"; [solve_ndisj|].
    iDestruct (llftl_bor_iff _ _
      ((proph_bor_tok (uniq_prvar x0 ξi) (uniq_cell x0 d' g' γ) idx ∗
        ghost_var γ (1/2) (lstate_triv x0)) ∗
       (uniq_pat_lft κ κp ∗ ⧗1 ∗ uniq_persγ ty x0 ξi idx κ κp tid l)) with "[] Body") as "Body".
    { iIntros "!> !>". rewrite /uniq_tokγ. iSplit.
      - iIntros "($ & [$ $] & $ & $)".
      - iIntros "[[$ $] ($ & $ & $)]". }
    iMod (llftl_sep_split with "LFT Body") as "[Tok _]"; [solve_ndisj|].
    iMod (proph_bor_tok_share_gen _ κ κ0 (uniq_prvar x0 ξi) (uniq_cell x0 d' g' γ) idx
      (uniq_gbody κpp ty tid l) (ghost_var γ (1/2) (lstate_triv x0))
      (ghost_var γ (1/2) (lstate_triv x0) ∗ ghost_var γ (1/2) (lstate_triv x0) ∗
        uniq_payload ty tid l x0 d' g')
      (λ wπ, ⌜∀ π, (wπ π).1 = vπ x0 π⌝)%I
      with "LFT IdxBor [] Tok") as "[PBor #TokG]"; [solve_ndisj| |].
    { iIntros "!> !>" (wπ). rewrite uniq_gbody_triv_iff. iSplit; iIntros "$". }
    iMod (llftl_sep_split with "LFT PBor") as "[_ PBor]"; [solve_ndisj|].
    iMod (llftl_sep_split with "LFT PBor") as "[_ PBor]"; [solve_ndisj|].
    iDestruct (llftl_bor_iff _ _ (guarded_upd lazyE @[ty_lft ty] (⧖(S d' `max` g') ∗
      ty.(ty_gho_own) x0 d' g' tid ∗ cbytes ty x0 l)) with "[] PBor")
      as "PBor".
    { iIntros "!> !>". rewrite uniq_payload_cell. iSplit; iIntros "$". }
    (* Open the borrow of the lazy contents before the step (with half of [G]), run the
       lazy update after the step (with the other half, which also guards the lifetime
       of the type; this also gives the persistent predicate of the contents), and close
       the borrow with the non-lazy contents. *)
    iMod (fractional.frac_split_guard_in_half with "G Gκ") as (γh) "[H1 [H2 [#Gh #Back]]]";
      [solve_ndisj|].
    iMod (llftl_bor_acc_guarded with "LFT PBor Gh H1") as "[Upd Close]"; [solve_ndisj|].
    iModIntro. iApply (step_fupdN_nmono (S d')); [lia|]. simpl.
    iModIntro. iNext.
    iMod (guarded_upd_run with "[] H2 Upd") as "(H2 & #⧖ & Gho & Pt)";
      [rewrite /lazyE; solve_ndisj| |].
    { iApply (guards_transitive with "Gh Incl'"). }
    iDestruct (ty_gho_pers_impl with "Gho") as "#InnerPers".
    iMod (fupd_mask_subseteq (↑Nllft)) as "Upd"; [solve_ndisj|].
    iMod ("Close" $! (ty.(ty_gho_own) x0 d' g' tid ∗ cbytes ty x0 l)%I
      with "[Gho Pt]") as "[PBor H1]".
    { iSplitR; [|iNext; iFrame]. iIntros "!> GP !> !>". iApply guarded_upd_intro.
      iModIntro. by iFrame "⧖ GP". }
    iMod "Upd" as "_".
    iMod (fupd_mask_mono with "(Back H1 H2)") as "G"; [solve_ndisj|].
    iMod (llftl_sep_split with "LFT PBor") as "[Gho Pt]"; [solve_ndisj|].
    iMod (llftl_bor_guard with "LFT Pt") as "#Pt"; [solve_ndisj|].
    iMod (ty_share with "LFT Incl' InnerPers Gκ G Gho") as "Upd"; [solve_ndisj|].
    iModIntro. iApply (step_fupdN_wand with "Upd"). iIntros ">[$ Shr] !>".
    iSplit; [iPureIntro; lia|].
    iSplitR "Shr"; last first.
    { iSplitR. { leaf_goal laters to 1. { lia. } iFrame "TokG". }
      iSplitL; [iNext; iApply (ty_shr_depth_mono with "Shr"); lia|]. by iFrame "InnerPers". }
    leaf_goal laters to 1. { lia. } iFrame "Pt".
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
  Next Obligation.
    intros 𝔄 κ ty x d g tid. destruct x as [[[[[l x0] ξi] d'] g'] idx]. simpl.
    iIntros "($ & $ & Body)". by iLeft.
  Qed.
  
  Global Instance uniq_bor_ne {𝔄} κ : NonExpansive (@uniq_bytes 𝔄 κ).
  Proof. 
    intros n ty ty' Heqv. split.
     - done.
     - simpl. f_equiv. apply Heqv.
     - simpl. f_equiv. { apply Heqv. } 
        unfold ty_outlives_E. f_equiv. apply Heqv.
     - intros x d g tid. destruct x as [[[[[l x0] ξi] d'] g'] idx]. simpl. f_equiv.
        + do 2 f_equiv. apply Heqv.
        + f_equiv. apply uniq_body_ne; [|intros; apply Heqv..].
          rewrite (ty_lfts_ne _ _ _ Heqv). apply lft_equiv_refl.
     - intros x d g tid. destruct x as [[[[[l x0] ξi] d'] g'] idx]. simpl. f_equiv.
       apply uniq_pers_component_ne; [|intros; apply Heqv..].
       rewrite (ty_lfts_ne _ _ _ Heqv). apply lft_equiv_refl.
     - intros x tid. done.
     - intros κ0 x d g tid. destruct x as [[[[[l x0] ξi] d'] g'] idx]. simpl.
       destruct Heqv as [_ _ _ _ EqPers EqPhys EqShr]. rewrite (cbytes_same ty ty').
       do 4 f_equiv; [f_equiv; apply EqShr|]. do 2 f_equiv. apply EqPers.
  Qed.
End uniq_bytes.

Notation "&uniq{ κ }" := (uniq_bytes κ) (format "&uniq{ κ }") : lrust_type_scope.

Section typing.
  Context `{!typeG Σ}.

  Global Instance uniq_type_contractive {𝔄} κ : TypeContractive (uniq_bytes (𝔄:=𝔄) κ).
  Proof.
    split; [by apply (type_lft_morphism_add_one κ)|done| | | |].
     - intros n ty ty' Heq Heq1 Heq2 Heq3 Heq4 Heq5 _ x d g tid.
       destruct x as [[[[[l x0] ξi] d'] g'] idx]. simpl. f_equiv.
        + apply equiv_dist. iDestruct Heq1 as "#[??]".
          iSplit; iIntros "#H"; (iApply llftl_incl_trans; [iApply "H"|done]).
        + f_equiv.
          apply uniq_body_contractive; [done|intros; apply Heq3|intros; apply Heq5].
     - intros n ty ty' Heq Heq1 Heq2 Heq3 Heq4 Heq5 _ x d g tid.
       destruct x as [[[[[l x0] ξi] d'] g'] idx]. simpl. f_equiv.
       apply uniq_pers_component_contractive; [done|intros; apply Heq3|intros; apply Heq5].
     - intros ???? x tid. by destruct x as [[[[[l x0] ξi] d'] g'] idx].
     - intros n ty ty' _ _ _ _ EqPers EqPhys EqShr κ0 x d g tid.
       destruct x as [[[[[l x0] ξi] d'] g'] idx]. simpl. rewrite (cbytes_same ty ty').
       do 3 f_equiv. f_equiv; [apply later_contractive; apply EqShr|].
       (* The persistent predicate of the referent is only [pred n]-close, hence the
          two laters. *)
       apply later_contractive. destruct n as [|n]; [apply dist_later_0|]. apply dist_later_S.
       apply later_contractive. apply EqPers.
  Qed.
  
  Lemma uniq_stack_okay {𝔄} κ (ty: type 𝔄) : StackOkay (&uniq{κ} ty).
  Proof. intros x tid. destruct x as [[[[[l x0] ξi] d'] g'] idx]. done. Qed.
  
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
    split. { unfold uniq_bytes, ty_gho_own. do 2 f_equiv.
      apply uniq_body_proper; [apply lft_equiv_refl|done..]. }
    split. { unfold uniq_bytes, ty_gho_pers. f_equiv.
      apply uniq_pers_component_proper; [apply lft_equiv_refl|done..]. }
    intros κ0. simpl. destruct (SyncTy tid tid' x0 d' g) as [H'phys [_ [_ H'shr]]].
    destruct (SyncTy tid tid' x0 d' g') as [_ [_ [H'pers _]]].
    by rewrite H'shr H'pers.
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
    iIntros "#LFT PROPH UNIQ TIME E #Lguard G [#In uniq]".
    destruct x as [[[[[l x0] ξi] d'] g'] idx].
    iDestruct "uniq" as "[%Hle uniq]".
    (* Settle the borrow first, with a program step, to get the time receipt of its
       contents, which pays for the later credits of the resolution. *)
    leaf_open "Lguard" with "G" as "[L Back]". { solve_ndisj. }
    iDestruct (Alive with "L E") as "#Alv".
    iMod ("Back" with "L") as "G".
    iDestruct (guards_transitive with "Lguard Alv") as "#Gk".
    destruct d as [|d0]; [lia|].
    replace (S d0 * (g + 1)) with (S (d0 * (g + 1) + g)) by lia.
    iModIntro. simpl.
    iMod (uniq_body_settle_step _ _ _ _ _ _ _ _ _ F G with "LFT Gk In uniq G") as "Upd";
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

  (** As [uniq_resolve], keeping the shared view of the referent ([ty_gho_res]). *)
  Lemma uniq_resolve_keep {𝔄} E L κ (ty: type 𝔄) :
    lctx_lft_alive E L κ →
    resolve_keep E L (&uniq{κ} ty) (λ x π, snd (vπ x π) = fst (vπ x π)).
  Proof.
    intros Alive G F x d g tid TimelessRes Hmask.
    iIntros "#LFT PROPH UNIQ TIME E #Lguard G [#In uniq]".
    destruct x as [[[[[l x0] ξi] d'] g'] idx].
    iDestruct "uniq" as "[%Hle uniq]".
    leaf_open "Lguard" with "G" as "[L Back]". { solve_ndisj. }
    iDestruct (Alive with "L E") as "#Alv".
    iMod ("Back" with "L") as "G".
    iDestruct (guards_transitive with "Lguard Alv") as "#Gk".
    destruct d as [|d0]; [lia|].
    replace (S d0 * (g + 1)) with (S (d0 * (g + 1) + g)) by lia.
    iModIntro. simpl.
    iMod (uniq_body_settle_step _ _ _ _ _ _ _ _ _ F G with "LFT Gk In uniq G") as "Upd";
      [rewrite /lazyE; solve_ndisj|].
    iModIntro. iNext. iMod "Upd" as "(#⧖ & uniq & G)".
    iMod (resolve_uniq_body with "LFT PROPH UNIQ TIME In E Lguard G ⧖ uniq")
      as "(X & G & #Shr & #PtG & #Pers)"; [done|set_solver|].
    iModIntro.
    iApply step_fupdN_intro. { set_solver. }
    iModIntro. iModIntro. iFrame "G In". iSplit.
    - iApply proph_obs_eq; last by done. intros π. simpl. f_equal.
    - iSplit; [iPureIntro; lia|]. iRight. by iFrame "Shr PtG Pers".
  Qed.

End typing.
