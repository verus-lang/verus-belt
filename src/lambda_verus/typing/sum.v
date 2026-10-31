From iris.proofmode Require Import proofmode.
From lrust.typing Require Import lft_contexts mod_ty.
From lrust.typing Require Export type.
From guarding Require Import guard tactics guard_later_pers.
From lrust.lifetime Require Import lifetime_full.
Set Default Proof Using "Type".

Implicit Type (𝔄 𝔅: syn_type) (𝔄l 𝔅l: syn_typel).

Section sum.
  Context `{!typeG Σ}.
        
  Lemma lft_intersect_tyl_lfts_lookup_incl {𝔄l} (tyl: typel 𝔄l) i :
    ⊢ lft_intersect_list (tyl_lfts tyl) ⊑ lft_intersect_list (ty_lfts (tyl +!! i)).
  Proof.
    apply lft_intersect_list_submseteq_incl, sublist_submseteq, tyl_lfts_lookup_sublist.
  Qed.

  Program Definition xsum_ty {𝔄l} (tyl: typel 𝔄l) : type (Σ! 𝔄l) := {|
    ty_lfts := tyl_lfts tyl;
    ty_E := tyl_E tyl;
    ty_gho_own x d g tid :=
        match to_xsum (x.1) return iProp Σ with
          xinj i x0 => @ty_gho_own _ _ (𝔄l !!ₗ i) (tyl +!! i) x0 d g tid
        end ;
    ty_gho_res x d g tid :=
        match to_xsum (x.1) return iProp Σ with
          xinj i x0 => @ty_gho_res _ _ (𝔄l !!ₗ i) (tyl +!! i) x0 d g tid
        end ;
    ty_gho_pers x d g tid :=
        match to_xsum (x.1) return iProp Σ with
          xinj i x0 => @ty_gho_pers _ _ (𝔄l !!ₗ i) (tyl +!! i) x0 d g tid
        end ;
    ty_mty := syn_mty _; ty_val := syn_val; ty_mty_eq := eq_refl; ty_val_eq _ := eq_refl;
    ty_fval := syn_fval; ty_fval_eq _ := eq_refl;
    ty_shr κ x d g tid :=
        match to_xsum (x.1) return iProp Σ with
          xinj i x0 => @ty_shr _ _ (𝔄l !!ₗ i) (tyl +!! i) κ x0 d g tid
        end ;
  |}%I.
  Next Obligation.
    intros 𝔄l tyl d g d' g' [x pad] tid H1 H2. simpl.
    refine (match (to_xsum x) with | xinj i x0 => _ end).
    apply ty_gho_own_depth_mono; trivial.
  Qed.
  Next Obligation.
    intros 𝔄l tyl d g d' g' [x pad] tid H1 H2. simpl.
    refine (match (to_xsum x) with | xinj i x0 => _ end).
    apply ty_gho_pers_depth_mono; trivial.
  Qed.
  Next Obligation.
    intros 𝔄l tyl [x pad] d g tid.
    refine (match (to_xsum x) with | xinj i x0 => _ end).
  Qed.
  Next Obligation.
    intros 𝔄l tyl [x pad] d g tid.
    refine (match (to_xsum x) with | xinj i x0 => _ end).
    apply ty_gho_pers_impl.
  Qed.
  Next Obligation.
    intros 𝔄l tyl κ [x pad] d g tid. simpl.
    refine (match (to_xsum x) with | xinj i x0 => _ end).
  Qed.
  Next Obligation.
    intros 𝔄l tyl κ κ' [x pad] d g tid. simpl.
    refine (match (to_xsum x) with | xinj i x0 => _ end).
    apply ty_shr_lft_mono.
  Qed.
  Next Obligation.
    intros 𝔄l tyl κ d g d' g' [x pad] tid ??. simpl.
    refine (match (to_xsum x) with | xinj i x0 => _ end).
    by apply ty_shr_depth_mono.
  Qed.
  Next Obligation.
    intros 𝔄l tyl E κ [x pad] d g tid G ??. simpl.
    refine (match (to_xsum x) with | xinj i x0 => _ end).
    iIntros "#LFT #Incl Pers Gκ G Bor".
    iApply (ty_share with "LFT [] Pers Gκ G Bor"); [done..|].
    iApply (guards_transitive with "Incl []").
    iApply lft_intersect_tyl_lfts_lookup_incl.
  Qed.
  Next Obligation.
    intros 𝔄l tyl κ [x pad] n d g tid ξ R. simpl.
    move=> Hin. replace x with (of_xsum (to_xsum x)) in Hin; last by rewrite semi_iso'. move: Hin.
    refine (match (to_xsum x) with | xinj i x0 => _ end).
    intros Hin. simpl in Hin. rewrite psum_map1_pinj in Hin. rewrite to_xsum_pinj in Hin.
    iIntros "#LFT #Incl #Pers #Shr".
    iApply (ty_shr_guard_proph with "LFT [] Pers Shr"); [done|].
    iApply (guards_transitive with "Incl []").
    iApply lft_intersect_tyl_lfts_lookup_incl.
  Qed.
  Next Obligation.
    intros 𝔄l tyl [x pad] d g tid. simpl.
    refine (match (to_xsum x) with | xinj i x0 => _ end). apply ty_gho_res_of_own.
  Qed.

  Global Instance xsum_ty_ne {𝔄l} : NonExpansive (@xsum_ty 𝔄l).
  Proof.
    move=> n tyl tyl' Eqv.
    split=>/=.
    - rewrite /tyl_lfts. elim: Eqv=>/= [|>Eqv ? ->]; [done|]. f_equiv. apply Eqv.
    - rewrite /tyl_E. elim: Eqv=>/= [|>Eqv ? ->]; [done|]. f_equiv. apply Eqv.
    - intros [x pad] d g tid.
      replace x with (of_xsum (to_xsum x)); last by rewrite semi_iso'.
      refine (match (to_xsum x) with | xinj i x0 => _ end).
      simpl.
      have Eqv': tyl +!! i ≡{n}≡ tyl' +!! i by apply @hlookup_ne.
      unfold ty_gho_own, xsum_ty. rewrite to_xsum_pinj. apply Eqv'.
    - intros [x pad] d g tid.
      replace x with (of_xsum (to_xsum x)); last by rewrite semi_iso'.
      refine (match (to_xsum x) with | xinj i x0 => _ end).
      simpl.
      have Eqv': tyl +!! i ≡{n}≡ tyl' +!! i by apply @hlookup_ne.
      unfold ty_gho_pers, xsum_ty. rewrite to_xsum_pinj. apply Eqv'.
    - intros κ [x pad] d g tid.
      replace x with (of_xsum (to_xsum x)); last by rewrite semi_iso'.
      refine (match (to_xsum x) with | xinj i x0 => _ end).
      simpl.
      have Eqv': tyl +!! i ≡{n}≡ tyl' +!! i by apply @hlookup_ne.
      unfold ty_shr, xsum_ty. rewrite to_xsum_pinj. apply Eqv'.
  Qed.
End sum.

Notation "Σ!" := xsum_ty : lrust_type_scope.
Notation empty_ty := (xsum_ty +[]).

Section typing.
  Context `{!typeG Σ}.

  Lemma xsum_lft_morphism {𝔅 𝔄l} (Tl: hlist (λ 𝔄, type 𝔅 → type 𝔄) 𝔄l) :
    TCHForall (λ 𝔄, TypeLftMorphism) Tl →
    TypeLftMorphism (λ ty: type 𝔅, Σ! (Tl +$ ty))%T.
  Proof.
    move=> All.
    set T := λ ty, Σ!%T (Tl +$ ty).
    have [[?[?[?[??]]]]|[?[?[??]]]]:
      ((∃α βs E, (∀ty, ⊢ ty_lft (T ty) ≡ₗ α ⊓ ty_lft ty) ∧
        (∀ty, elctx_interp (T ty).(ty_E) ⊣⊢
          elctx_interp E ∗ elctx_interp ty.(ty_E) ∗ [∗ list] β ∈ βs, lifetime_full.llft_incl β (ty_lft ty))) ∨
      (∃α E, (∀ty, ⊢ ty_lft (T ty) ≡ₗ α) ∧
        (∀ty, elctx_interp (T ty).(ty_E) ⊣⊢ elctx_interp E))); [|by eleft|by eright].
    induction All as [|???? H ? IH]=>/=.
    { right. exists static, []. split=> ?; by [|apply lft_equiv_refl]. }
    setoid_rewrite lft_intersect_list_app.
    destruct (Xl).
    { inv_hlist xl => ???.
      simpl. destruct H as [α βs E Hα HE | α E Hα HE].
      - left; exists α, βs, E; split.
        + move => ty /=. by rewrite lft_intersect_right_id.
        + move => ty /=; cbn. by rewrite app_nil_r.
      - right; exists α, E; split.
        + move => ty /=. by rewrite lft_intersect_right_id.
        + move => ty /=; cbn. by rewrite app_nil_r.
    }
    case IH=> [[α[βs[E[Hα HE]]]]|[α[E[Hα HE]]]];
    case H=> [α' βs' E' Hα' HE'|α' E' Hα' HE'].
    - left. exists (α' ⊓ α), (βs' ++ βs), (E' ++ E). split=> ?.
      + iApply lft_equiv_trans.
        { iApply lft_intersect_equiv_proper; [iApply Hα'|iApply Hα]. }
        rewrite -!assoc (comm (⊓) _ (α ⊓ _)) -!assoc.
        repeat iApply lft_intersect_equiv_proper; try iApply lft_equiv_refl.
        iApply lft_intersect_equiv_idemp.
      + rewrite !elctx_interp_app HE' HE big_sepL_app -!assoc.
        iSplit; iIntros "#H"; repeat iDestruct "H" as "[?H]"; iFrame "#".
    - left. exists (α' ⊓ α), βs, (E' ++ E). split=> ?.
      + rewrite -assoc. iApply lft_intersect_equiv_proper; [iApply Hα'|iApply Hα].
      + by rewrite !elctx_interp_app HE' HE -!assoc.
    - left. exists (α' ⊓ α), βs', (E' ++ E). split=> ?.
      + rewrite -!assoc (comm (⊓) α _) !assoc.
        iApply lft_intersect_equiv_proper; [iApply Hα'|iApply Hα].
      + rewrite/= !elctx_interp_app HE' HE -!assoc.
        iSplit; iIntros "#H"; repeat iDestruct "H" as "[? H]"; iFrame "#".
    - right. exists (α' ⊓ α), (E' ++ E). split=> ?.
      + iApply lft_intersect_equiv_proper; [iApply Hα'|iApply Hα].
      + by rewrite !elctx_interp_app HE HE'.
  Qed.

  Global Instance xsum_type_ne {𝔄 𝔅l} (T: type 𝔄 → typel 𝔅l) :
    ListTypeNonExpansive T → TypeNonExpansive (Σ! ∘ T)%T.
  Proof.
    move=> [Tl[->All]].
    split=>/=.
    - apply xsum_lft_morphism. eapply TCHForall_impl; [|done]. by move=> >[].
    - move=> ? ty ty' H1 H2 H3 H4 H5 [x pad] d g tid.
      unfold xsum_ty, ty_gho_own. simpl.
      refine (match (to_xsum x) with | xinj i x0 => _ end).
      eapply TCHForall_lookup in All. rewrite !hlookup_apply.
      by apply All.
    - move=> ? ty ty' H1 H2 H3 H4 H5 [x pad] d g tid.
      unfold xsum_ty, ty_gho_pers. simpl.
      refine (match (to_xsum x) with | xinj i x0 => _ end).
      eapply TCHForall_lookup in All. rewrite !hlookup_apply.
      by apply All.
    - move=> ? ty ty' H1 H2 H3 H4 H5 κ [x pad] d g tid.
      unfold xsum_ty, ty_shr. simpl.
      refine (match (to_xsum x) with | xinj i x0 => _ end).
      eapply TCHForall_lookup in All. rewrite !hlookup_apply.
      by apply All.
  Qed.

  Global Instance xsum_type_contractive {𝔄 𝔅l} (T: type 𝔄 → typel 𝔅l) :
    ListTypeContractive T → TypeContractive (Σ! ∘ T)%T.
  Proof.
    move=> [Tl[->All]].
    split=>/=.
    - apply xsum_lft_morphism. eapply TCHForall_impl; [|done]. by move=> >[].
    - move=> ? ty ty' H1 H2 H3 H4 H5 [x pad] d g tid.
      unfold xsum_ty, ty_gho_own. simpl.
      refine (match (to_xsum x) with | xinj i x0 => _ end).
      eapply TCHForall_lookup in All. rewrite !hlookup_apply.
      by apply All.
    - move=> ? ty ty' H1 H2 H3 H4 H5 [x pad] d g tid.
      unfold xsum_ty, ty_gho_pers. simpl.
      refine (match (to_xsum x) with | xinj i x0 => _ end).
      eapply TCHForall_lookup in All. rewrite !hlookup_apply.
      by apply All.
    - move=> ? ty ty' H1 H2 H3 H4 H5 κ [x pad] d g tid.
      unfold xsum_ty, ty_shr. simpl.
      refine (match (to_xsum x) with | xinj i x0 => _ end).
      eapply TCHForall_lookup in All. rewrite !hlookup_apply.
      by apply All.
  Qed.

  Global Instance xsum_copy {𝔄l} (tyl: typel 𝔄l) : ListCopy tyl → Copy (Σ! tyl).
  Proof.
    move=> ?. have Copy: ∀i, Copy (hlookup tyl i).
    { move=> *. by apply TCHForall_lookup. }
    split.
    - intros x d g tid. destruct x as [x pad]. unfold ty_gho_own, xsum_ty.
      refine (match (to_xsum x) with | xinj i x0 => _ end).
    - intros κ [x pad] d g tid. unfold ty_shr, ty_gho_own, xsum_ty.
      refine (match (to_xsum x) with | xinj i x0 => _ end).
      have Cpyi := Copy i. apply copy_shr.
  Qed.

  Global Instance xsum_send {𝔄l} (tyl: typel 𝔄l) : ListSend tyl → Send (Σ! tyl).
  Proof.
    move=> ?. have Send: ∀i, Send (hlookup tyl i).
    { move=> *. by apply TCHForall_lookup. }
    split.
    iIntros (tid tid' x d g G H κs d0 Hineq TG TH) "LFT UNIQ TIME Hg H Gg G Gho ⧖".
      destruct x as [x pad]. replace x with (of_xsum (to_xsum x)).
        2: { apply semi_iso'. typeclasses eauto. }
      refine (match (to_xsum x) with | xinj i x0 => _ end).
      unfold ty_gho_own, xsum_ty. rewrite semi_iso'.
      iDestruct (@send_change_tid _ _ (𝔄l !!ₗ i) (tyl +!! i) (Send i) tid tid' x0 d g G H κs d0 with "LFT UNIQ TIME Hg H Gg G Gho ⧖") as "X". { trivial. }
      iApply (step_fupdN_wand with "X"). iIntros ">X".
      iDestruct "X" as (x0' off) "(gho & ⧖off & %Habs & G & H)".
      iModIntro. iExists (of_xsum (xinj i x0'), pad), off.
      rewrite semi_iso'. iFrame. iPureIntro. 
      simpl. do 2 (rewrite psum_map1_pinj). rewrite Habs. trivial.
  Qed.
  
  Global Instance xsum_sync {𝔄l} (tyl: typel 𝔄l) : ListSync tyl → Sync (Σ! tyl).
  Proof.
    move=> ?. have Sync: ∀i, Sync (hlookup tyl i).
    { move=> *. by apply TCHForall_lookup. }
    intros tid tid' x d g.
    destruct x as [x pad].
    unfold ty_gho_own, ty_gho_pers, ty_shr, xsum_ty.
    refine (match (to_xsum x) with | xinj i x0 => _ end).
    destruct (Sync i tid tid' x0 d g) as [Hb [Hc Hd]].
    split; last split; trivial.
  Qed.

  Lemma xsum_resolve {𝔄l} E L (tyl: typel 𝔄l) Φl :
    resolvel E L tyl Φl →
    resolve E L (Σ! tyl) (λ s, let 'xinj i x := to_xsum (s.1) in (Φl -!! i) x).
  Proof.
    iIntros (Rslv G vπ [x pad] ??? Ti Ma) "#LFT #PROPH #E #L G T".
    unfold ty_gho_own, xsum_ty.
    refine (match (to_xsum x) with | xinj i x0 => _ end).
    eapply HForall_1_lookup in Rslv.
    instantiate (1 := i) in Rslv.
    iApply (Rslv with "[] [] [] [] G T"); trivial.
  Qed.

  Global Instance xsum_res_own {𝔄l} (tyl: typel 𝔄l) :
    TCHForall (λ 𝔄, @ResOwn _ _ 𝔄) tyl → ResOwn (Σ! tyl).
  Proof.
    move=> Hres [x pad] d g tid. rewrite /ty_gho_res /ty_gho_own /=.
    refine (match (to_xsum x) with | xinj i x0 => _ end).
    have ?: ResOwn (tyl +!! i) by apply TCHForall_lookup. by rewrite res_own.
  Qed.

  Lemma xsum_resolve_keep {𝔄l} E L (tyl: typel 𝔄l) Φl :
    HForall_1 (λ _, resolve_keep E L) tyl Φl →
    resolve_keep E L (Σ! tyl) (λ s, let 'xinj i x := to_xsum (s.1) in (Φl -!! i) x).
  Proof.
    iIntros (Rslv G vπ [x pad] ??? Ti Ma) "#LFT #PROPH #E #L G T".
    unfold ty_gho_own, ty_gho_res, xsum_ty.
    refine (match (to_xsum x) with | xinj i x0 => _ end).
    eapply HForall_1_lookup in Rslv.
    instantiate (1 := i) in Rslv.
    iApply (Rslv with "[] [] [] [] G T"); trivial.
  Qed.

  Lemma xsum_resolve_just {𝔄l} E L (tyl: typel 𝔄l) :
    HForall (λ _ ty, resolve E L ty (const (const True))) tyl → resolve E L (Σ! tyl) (const (const True)).
  Proof. move=> ?. apply resolve_just. Qed.

  Lemma psum_map_p2lookup_pinj {𝔄l 𝔅l} {F G}
      (f : ∀ 𝔄 𝔅, F 𝔄 𝔅 → G 𝔄 → G 𝔅)
      (fl : plist2 F 𝔄l 𝔅l)
      (i : fin (length 𝔄l))
      (x0 : G (𝔄l !!ₗ i))
  : 
      psum_map (f -2<$> fl) (pinj i x0) =
        pinj (fin_renew_by_plist2 fl i) (f _ _ (fl -2!! i) x0).
  Proof.
      generalize x0. generalize i. generalize fl. generalize f. generalize 𝔅l.
      clear x0. clear i. clear fl. clear f. clear 𝔅l.
      induction 𝔄l; intros 𝔅l f fl i x0.
      - inversion i.
      - destruct 𝔅l; first by contradiction. destruct fl as [f1 fl1].
        simpl in i. inv_fin i.
        + intros x0. trivial.
        + intros i x0. simpl. rewrite IH𝔄l. trivial.
  Qed.

  Lemma xsum_subtype {𝔄l 𝔅l} E L (tyl: typel 𝔄l) (tyl': typel 𝔅l) fl :
    subtypel E L tyl tyl' fl → subtype E L (Σ! tyl) (Σ! tyl') ((psum_mapₛ fl)).
  Proof. 
    move=> Subs. iIntros "L".
    iAssert (□ (elctx_interp E -∗ tyl_lft tyl' ⊑ tyl_lft tyl))%I as "#InLft".
    { iInduction Subs as [|?????????? Sub Subs] "IH".
      { iIntros "!>_". by iApply lft_incl_refl. }
      iDestruct (Sub with "L") as "#Sub".
      destruct Xl.
      { destruct Yl => //. 
        inv_hlist xl; inv_hlist yl => /= _.
        iIntros "!> E /=". 
        iDestruct ("Sub" with "E") as "#(Hlfts&?)". 
        by rewrite /tyl_lft/tyl_lfts /= !app_nil_r. }
      iDestruct ("IH" with "L") as "#IH'".
      iIntros "!> E /=". iDestruct ("Sub" with "E") as "#[?_]".
      iDestruct ("IH'" with "E") as "#?".
      rewrite /tyl_lft !lft_intersect_list_app. by iApply lft_intersect_mono. }
    move/subtypel_llctx_lookup in Subs. iDestruct (Subs with "L") as "#InTyl".
    iIntros "!> #E".
    iSpecialize ("InLft" with "E"). iSpecialize ("InTyl" with "E").
    (* iSplit; simpl; [iPureIntro; by f_equal|]. iSplit; [done|]. *)
    (* iSplit; first iModIntro; iIntros "*". *)
    (* iDestruct ("InTyl" $! i) as (?) "[#?[#InOwn %Hphys]]". *)
    iSplit; [done|].
    iSplit. { (* gho *)
      iModIntro. iIntros (x d g tid). destruct x as [x pad].
      replace x with (@of_xsum _ (~~) (𝔄l) (to_xsum x)); last by rewrite semi_iso'; trivial.
      refine (match (to_xsum x) with | xinj i x0 => _ end).
    
      iDestruct ("InTyl" $! i) as "(Incl & #Gho & _)".
      iSpecialize ("Gho" $! x0 d g tid). simpl.
      
      rewrite psum_map_p2lookup_pinj.
      (*replace (psum_map (@syn_type_morphism_fn -2<$> fl) (pinj i x0))
         with (pinj (fin_renew_by_plist2 fl i) ((~~!ₛ) (fl -2!! i) x0)).
        2: { symmetry. apply psum_map_p2lookup_pinj. }*)
      unfold ty_gho_own, xsum_ty. rewrite to_xsum_pinj. rewrite to_xsum_pinj. iFrame "Gho".
    } 
    iSplit. { (* gho_pers *)
      iModIntro. iIntros (x d g tid). destruct x as [x pad].
      replace x with (@of_xsum _ (~~) (𝔄l) (to_xsum x)); last by rewrite semi_iso'; trivial.
      refine (match (to_xsum x) with | xinj i x0 => _ end).
      iDestruct ("InTyl" $! i) as "(Incl & _ & #GhoPers & _)".
      iSpecialize ("GhoPers" $! x0 d g tid). simpl.
      rewrite psum_map_p2lookup_pinj.
      unfold ty_gho_pers, xsum_ty. rewrite to_xsum_pinj. rewrite to_xsum_pinj. iFrame "GhoPers".
    }
    { (* shr *)
      iModIntro. iIntros (κ x d g tid). destruct x as [x pad].
      replace x with (@of_xsum _ (~~) (𝔄l) (to_xsum x)); last by rewrite semi_iso'; trivial.
      refine (match (to_xsum x) with | xinj i x0 => _ end).
      iDestruct ("InTyl" $! i) as "(Incl & _ & _ & #Shr)".
      iSpecialize ("Shr" $! κ x0 d g tid). simpl.
      rewrite psum_map_p2lookup_pinj.
      unfold ty_shr, xsum_ty. rewrite to_xsum_pinj. rewrite to_xsum_pinj. iFrame "Shr".
    }
  Qed.

  Lemma xsum_eqtype {𝔄l 𝔅l} E L (tyl: typel 𝔄l) (tyl': typel 𝔅l) fl gl :
    eqtypel E L tyl tyl' fl gl →
    eqtype E L (Σ! tyl) (Σ! tyl') ((psum_mapₛ fl)) ((psum_mapₛ gl)).
  Proof.
    move=> /eqtypel_subtypel[??]. by split; apply xsum_subtype.
  Qed.
  
End typing.

Global Hint Resolve xsum_resolve | 5 : lrust_typing.
Global Hint Resolve xsum_resolve_just xsum_subtype xsum_eqtype
  : lrust_typing.
