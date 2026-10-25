From lrust.lang.lib Require Import memcpy.
From lrust.typing Require Export type tracked own product sum uniq_bor uniq_util shr_bor.
From lrust.typing Require Import uninit type_context programs freeable_util.
From guarding Require Import guard tactics.
From lrust.lifetime Require Import lifetime_full.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section ptr.
  Context `{!typeG Σ}.

  Program Definition ptr_ty : type locₛ := {|
    pt_size := 1;
    pt_gho (l: ~~locₛ) _ := True%I ;
    pt_phys (l: ~~locₛ) _ := [ FVal (LitV (LitLoc l)) ] ;
  |}%I.
  Next Obligation. move=> *. trivial. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. intros. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  
  Global Instance ptr_copy: Copy ptr_ty.
  Proof. split. - typeclasses eauto. - iIntros. iPureIntro. done. Qed.
  
  Lemma ptr_stack_okay : StackOkay ptr_ty.
  Proof. done. Qed.

  Global Instance ptr_send: Send ptr_ty.
  Proof.
    intros. split; trivial.
     - intros. unfold syn_abstract in H. subst x'. trivial.
     - iIntros. iApply step_fupdN_intro; first done. iNext.
       iExists x, 0%nat. iModIntro. iFrame. simpl.
       replace (d0 + 0)%nat with d0 by lia. iFrame "#". done.
  Qed.
  
  Global Instance ptr_sync: Sync ptr_ty.
  Proof. split; trivial. split; iSplit; done. Qed.
  
  Lemma ptr_resolve E L : resolve E L ptr_ty (const (const True)).
  Proof. apply resolve_just. Qed.
End ptr.

Section points_to.
  Context `{!typeG Σ}.

  Program Definition tracked_ty_with_prop {𝔄} (ty: type 𝔄) (P : iProp Σ) : type (trackedₛ 𝔄) := {|
    ty_size := 0;
    ty_lfts := ty.(ty_lfts);
    ty_E := ty.(ty_E);
    ty_gho_own x d g tid := P ∗ (ty.(ty_gho_own) x d g tid) ;
    ty_gho_pers x d g tid := (ty.(ty_gho_pers) x d g tid) ;
    ty_phys x tid := [];
    ty_shr := default_shr (λ x d g tid, P ∗ (ty.(ty_gho_own) x d g tid));
  |}%I.
  Next Obligation. intros; done. Qed.
  Next Obligation. intros; done. Qed.
  Next Obligation. intros; done. Qed.
  Next Obligation.
    intros.
    iIntros "[? gho]".
    iDestruct (ty_gho_own_depth_mono ty with "gho") as "[? wand]" => //. 
    iFrame.
    iIntros "[$ ?]".
    by iApply "wand".
  Qed.
  Next Obligation. intros. apply (ty_gho_pers_depth_mono ty); trivial. Qed.
  Next Obligation.
    intros. iIntros "L Incl gho_pers".
    iPoseProof (ty_guard_proph _ ty with "L Incl gho_pers") as "Hguard" => //.
    iIntros "!> H1 H2".
    iDestruct ("Hguard" with "H1") as "Hguard".
    iDestruct (guards_weaken_rhs_sep_r with "H2") as "H2".
    by iApply ("Hguard" with "H2").
  Qed.
  Next Obligation. iIntros "* [? ?]". iApply (ty_gho_pers_impl 𝔄); trivial. Qed.
  Solve All Obligations with solve_default_shr.

  Definition points_to_ty {𝔄} ty := tracked_ty (@own_ptr _ _ 𝔄 (ty_size ty) ty).

  Global Instance tracked_ty_ne {𝔄} : NonExpansive (@tracked_ty _ _ 𝔄).
  Proof. solve_ne_type. Qed.

  Global Instance points_to_ne {𝔄} : NonExpansive (@points_to_ty 𝔄).
  Proof.
    rewrite /points_to_ty.
    move => m ty1 ty2 Eq.
    apply tracked_ty_ne.
    destruct Eq. rewrite H.
    by rewrite own.own_ne.
  Qed.

  Lemma points_to_stack_okay {𝔄} (ty: type 𝔄) : StackOkay (points_to_ty ty).
  Proof. done. Qed.

  Global Instance points_to_send {𝔄} (ty: type 𝔄) : Send ty → Send (points_to_ty  ty).
  Proof. exact _. Qed.

  Global Instance points_to_sync {𝔄} (ty: type 𝔄) : Sync ty → Sync (points_to_ty ty).
  Proof. exact _. Qed.

  Lemma points_to_resolve {𝔄} E L (ty: type 𝔄) Φ :
    resolve E L ty Φ → resolve E L (points_to_ty ty) (λ '(l, s), Φ s) .
  Proof.
    move => Rslv.
    apply tracked_resolve.
    by eapply own_resolve.
  Qed.

  Lemma points_to_type_incl {𝔄 𝔅} (f: 𝔄 →ₛ 𝔅) ty1 ty2 :
    type_incl ty1 ty2 f -∗ type_incl (points_to_ty ty1) (points_to_ty  ty2) (tracked_mapₛ (at_loc_mapₛ f)).
  Proof.
    iIntros "Hincl".
    iApply tracked_type_incl.
    iDestruct "Hincl" as "(% & ?)".
    rewrite H.
    iApply own_type_incl.
    by iFrame.
  Qed.

  Lemma points_to_subtype {𝔄 𝔅} E L (f: 𝔄 →ₛ 𝔅) ty ty' :
    subtype E L ty ty' f → subtype E L (points_to_ty ty) (points_to_ty ty') (tracked_mapₛ (at_loc_mapₛ f)).
  Proof.
    move=> Sub. iIntros "L". iDestruct (Sub with "L") as "#Incl".
    iIntros "!> #E". iApply points_to_type_incl; by [|iApply "Incl"].
  Qed.

End points_to.

Section typing.

  Context `{!typeG Σ}.

  (* Not sure if this n makes sense to be an argument at the syntax level *)
  (* Notation "PPtr2Own: ptr perm" := (Skip;; ptr)%E (at level 102, ptr, perm at level 1): expr_scope. *)
  Definition PPtr2Own : val :=
    (λ: ["ptr"; "perm"], "ptr")%V.

  Lemma typed_pptr_to_own {𝔄} (perm ptr : path) (ty : type 𝔄) E L I :
    typed_instr E L I +[ptr ◁ ptr_ty; perm ◁ own_ptr 0 (points_to_ty ty)] (PPtr2Own [ptr; perm]) (λ v, +[v ◁ own_ptr (ty_size ty) ty]) (λ post '-[l; (_, (l', x))], λ mask π, l = l' ∧ post -[(l, x)] mask π).
  Proof.
    move => tid postπ mask iκs vπl.
    iIntros "#LFT #TIME #PROPH UNIQ E L $ TY #Obs" => /=.
    destruct vπl as [l [[? [l' x]] []]].
    iDestruct "TY" as "(Hptr & Hperm & _)".
    iDestruct "Hptr" as (pl d Heval) "(#Hd & _ & %Hphys)".
    iDestruct "Hperm" as (pl' d' Heval') "(#Hd' & Hown & %Hphys')".
    simpl in Hphys, Hphys'.
    injection Hphys => ?; subst pl.
    injection Hphys' => ?; subst pl'.
    destruct d' => //=.
    iDestruct "Hown" as "(_ & _ & Hown)".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & _)" => //.
    rewrite /PPtr2Own.
    wp_bind ptr.
    iApply wp_wand.
    iApply wp_eval_path => //.
    iIntros (? ->).
    wp_bind perm.
    iApply wp_wand.
    iApply wp_eval_path => //.
    iIntros (? ->).
    wp_rec.
    iExists -[(l, x)].
    iFrame.
    rewrite /tctx_elt_interp/ty_own/=.
    iSplitL.
    - iSplit => //.
      destruct d' => //=.
      iExists _, (S (S d')).
      do 2 iSplit => //=.
      iDestruct "Hown" as "(? & ? & gho)".
      iSplitL => //.
      iFrame.
      iNext.
      iDestruct (ty.(ty_gho_own_depth_mono) with "gho") as "($ & ?)"; lia.
    - iApply (proph_obs_impl with "Obs").
      intros π' Hpost.
      apply Hpost.
  Qed.

  Definition PPtrFromOwn : val :=
    (λ: ["p"], 
      let: "x" := new [ #1 ] in "x" <- "p";; "x")%V.

  Lemma typed_pptr_from_own {𝔄} (p : path) (ty : type 𝔄) E L I :
    typed_instr E L I +[p ◁ own_ptr (ty_size ty) ty] (PPtrFromOwn [p]) (λ v, +[v ◁ own_ptr 1 (prod_ty ptr_ty (points_to_ty ty))]) (λ post '-[(l, x)], λ mask π, ∀ lc, post -[(lc, (l, (l, x)))] mask π).
  Proof.
    move => tid postπ mask iκs vπl.
    iIntros "#LFT #TIME #PROPH UNIQ E L $ TY #Obs" => /=.
    destruct vπl as [[l x] []].
    iDestruct "TY" as "(TY & _)".
    iDestruct "TY" as (pl d Heval) "(#Hd & Hown & %Hphys)".
    simpl in Hphys.
    injection Hphys => ?; subst pl.
    destruct d => //=.
    iDestruct "Hown" as "(Hl & Hfree & Hgho)".
    wp_bind p.
    iApply wp_wand.
    iApply wp_eval_path => //.
    iIntros (? ->).
    iApply (wp_persistent_time_receipt with "TIME Hd"); [done|].
    iIntros "£ #Hd'".
    wp_rec.
    wp_bind (new _).
    iApply wp_new => //.
    iNext.
    iIntros (l') "[Hfree' Hl']".
    wp_let.
    rewrite heap_mapsto_vec_singleton.
    wp_bind (_ <- _)%E.
    iApply (wp_write_na with "Hl'"); [solve_ndisj|].
    iNext. iIntros "Hl'". wp_seq.
    iExists -[(l', (l, (l, x)))].
    iFrame.
    rewrite /tctx_elt_interp/ty_own/=.
    iSplitL.
    - iSplit => //.
      iExists _, (S (S d)).
      do 2 iSplit => //=.
      iSplitL => //.
      iFrame.
      rewrite -heap_mapsto_vec_singleton.
      rewrite -!(heap_mapsto_fancy_fmap_eq l').
      iFrame.
      rewrite freeable_sz_full.
      iFrame.
      iNext; iNext; iFrame.
      iDestruct (ty.(ty_gho_own_depth_mono) with "Hgho") as "($ & ?)"; lia.
    - iApply (proph_obs_impl with "Obs").
      intros π' Hpost.
      apply Hpost.
  Qed.

  Definition PPtrBorrow : val :=
    (λ: ["ptr"; "perm_ref"], "ptr")%V.

  Lemma typed_pptr_borrow {𝔄} κ (ptr perm_ref : path) (ty : type 𝔄) E L I :
    (* lctx_lft_alive E L κ → *)
    typed_instr E L I +[ptr ◁ ptr_ty; perm_ref ◁ shr_bor κ (points_to_ty ty)] (PPtrBorrow [ptr; perm_ref]) (λ v, +[v ◁ shr_bor κ ty]) (λ post '-[l; (cl, (l', x))], λ mask π, l = l' ∧ post -[((l, repeat [] ty.(ty_size)), x)] mask π).
  Proof.
    move => tid postπ mask iκs vπl.
    iIntros "#LFT #TIME #PROPH #UNIQ #E L $ TY #Obs" => /=.
    destruct vπl as [l [[c [l' x]] []]].
    iDestruct "TY" as "(Hptr & Hperm & _)".
    iDestruct "Hptr" as (pl d Heval) "(#Hd & _ & %Hphys)".
    simpl in Hphys.
    injection Hphys => ?; subst pl.
    iDestruct "Hperm" as (pl' d' Heval') "(#Hd' & Hshr & %Hphys')".
    simpl in Hphys'.
    injection Hphys' => ?; subst pl'.
    (* destruct d' => //=. *)
    rewrite /PPtrBorrow.
    wp_bind ptr.
    iApply wp_wand.
    iApply wp_eval_path => //.
    iIntros (? ->).
    wp_bind perm_ref.
    iApply wp_wand.
    iApply wp_eval_path => //.
    iIntros (? ->).
    iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME Hd'"); [done|].
    destruct d' as [ | [ | d']] => //=; iDestruct "Hshr" as "(_ & #Hshr & #Hpers)".
    { rewrite /advance_credits /=.
      iIntros "(£ & _) #Hd''".
      wp_rec.
      by iMod (lc_fupd_elim_later with "£ Hpers"). }
    iIntros "_ #Hd''".
    wp_rec.
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & _)" => //.
    iModIntro.
    iExists -[((l, repeat [] ty.(ty_size)), x)].
    rewrite /tctx_elt_interp/ty_own/=.
    iFrame.
    iSplitL.
    { rewrite /tctx_elt_interp/ty_own/=.
      iSplit => //; iExists _, (S (S (S d'))).
      iSplit => //.
      iFrame "#" => /=.
      iSplit => //.
      iSplitR; last iSplitL.
      - rewrite heap_mapsto_cells_fancy_empty.
        rewrite (ty.(ty_size_eq) x tid).
        iPoseProof (guards_weaken_rhs_sep_l with "Hshr") as "Hshr2".
        iPoseProof (lguards_weaken_later with "Hshr2") as "Hshr3".
        2: iFrame "#".
        lia.
      - iPoseProof (guards_weaken_rhs_sep_r with "Hshr") as "Hshr2".
        iPoseProof (guards_weaken_rhs_sep_r with "Hshr2") as "Hshr3".
        iPoseProof (guards_later_absorb_1 with "Hshr3") as "Hshr4".
        replace (S (S (d' + 1)) + 1) with (S (S (S (d' + 1)))) by lia.
        iClear "Hshr Hshr2 Hshr3".
        replace (S (S (S (d' + 1)))) with (S (S (S (d' + 1))) + 0) at 2 by lia.
        iApply (guards_transitive_additive with "Hshr4").
        leaf_by_sep.
        iApply ty.(ty_gho_own_depth_mono); lia.
      - repeat iNext.
        iApply (ty.(ty_gho_pers_depth_mono) with "Hpers") => //; lia.
    }
    iApply (proph_obs_impl with "Obs").
    by intros π' [_ Hpost].
  Qed.

  Definition PPtrMutBorrow : val :=
    (λ: ["ptr"; "perm_ref"], "ptr")%V.

  Lemma typed_pptr_borrow_mut {𝔄} κ (ptr perm_ref : path) (ty : type 𝔄) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I +[ptr ◁ ptr_ty; perm_ref ◁ &uniq{κ} (points_to_ty ty)] (PPtrMutBorrow [ptr; perm_ref]) (λ v, +[v ◁ &uniq{κ} ty]) (λ post '-[l; bor], λ mask π, let '(cl, (l', x), ξi, d, g, idx) := bor in l = l' ∧ ∀ bor',
    uniq_bor_current bor' = snd (uniq_bor_current bor) →
    uniq_bor_future bor' π = snd (uniq_bor_future bor π) →
    of_cloc (uniq_bor_loc bor') = fst (uniq_bor_current bor) →
    of_cloc (uniq_bor_loc bor') = fst (uniq_bor_future bor π) →
    post -[bor'] mask π).
  Proof.
    move => Alv tid postπ mask iκs vπl.
    iIntros "#LFT #TIME #PROPH #UNIQ #E L $ TY #Obs" => /=.
    iDestruct (Alv with "L E") as "#Alv".
    destruct vπl as [l [u []]].
    destruct u as [[[[[c [l' x]] ξi] d] g] ξidx].
    iDestruct "TY" as "(Hptr & Hperm & _)".
    iDestruct "Hptr" as (pl d' Heval) "(#Hd & _ & %Hphys)".
    simpl in Hphys.
    injection Hphys => ?; subst pl.
    iDestruct "Hperm" as (pl' d'' Heval') "(#Hd' & Huniq & %Hphys')".
    simpl in Hphys'.
    injection Hphys' => ?; subst pl'.
    iDestruct "Huniq" as "[#Incl [%Hineq [UniqBody [#PtBase #Pers]]]]".
    rewrite /PPtrMutBorrow.
    wp_bind ptr.
    iApply wp_wand.
    iApply wp_eval_path => //.
    iIntros (? ->).
    wp_bind perm_ref.
    iApply wp_wand.
    iApply wp_eval_path => //.
    iIntros (? ->).
    iApply wp_fupd.
    iApply (wp_cumulative_time_receipt2 with "TIME"); [trivial |]; iIntros "⧗".
    destruct d'' as [ | ] => //=; first lia.
    iDestruct "Pers" as "[Dead|Pers]". {
      iDestruct "Dead" as (κ') "[Incl' Dead']".
      iDestruct (guards_transitive with "Alv Incl'") as "G2".
      wp_rec. repeat wp_seq.
      leaf_open "G2" with "L" as "[Alive _]". { solve_ndisj. }
      iExFalso. iApply (llftl_not_own_end with "Alive Dead'").
    }
    iDestruct "UniqBody" as "(ξBor & £saved)".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & _)" => //.
    1: solve_ndisj.

    destruct c as [cl [ | ]] eqn:?.
    2: {
      iMod (uniq_body_acc with "LFT UNIQ Alv [$ξBor $£saved] L") as "[Hown _]"; [solve_ndisj|..].
      wp_rec.
      iDestruct "Hown" as "(_ & _ & Hfalse)".
      iDestruct (heap_cloc_mapsto_fancy_vec_length_eq with "Hfalse") as "%Hfalse".
      by simpl in Hfalse. }

    wp_rec.
    rewrite /tctx_elt_interp/ty_own/=.

    iMod (llctx_interp_make_guarded with "L") as (γ) "[H1 [H2 [#Ghalf #Halfback]]]". { solve_ndisj. }
    iDestruct (guards_transitive with "Ghalf Alv") as "HguardsK".
    destruct d => //=.
    change 2 with (1 + 1).
    iDestruct "⧗" as "(⧗ & ⧗')".
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗ Hd'") as "(Hd'' & £)"; [trivial|..].
    iDestruct "£" as "[£ [£1' £1]]".

    iMod (uniq_body_transform (points_to_ty ty) ty (l, x) x (S d) g ξi ξidx κ tid (l, []) (l, repeat [] ty.(ty_size)) _ _ (pair_with_loc_trackedₛ l) (λ d g, (S d, g)) with "LFT PROPH UNIQ [⧗' £1'] HguardsK H1 [ξBor £saved]") as (ζi ζidx) "[#Obs2 [UniqBody H1]]". { set_solver. }
    { iIntros "[gho pt]".
      iMod (lc_fupd_elim_later with "£1' gho") as "gho".
      iDestruct "gho" as "[phys [free gho]]".
      iModIntro.
      iDestruct (ty_gho_own_depth_mono _ _ _ (S d) g with "gho") as "[gho _]". { lia. } { lia. }
      iFrame "gho".
      simpl.
      rewrite -(ty.(ty_size_eq) x tid).
      rewrite <- heap_cloc_mapsto_fancy_empty.
      iFrame "phys". iIntros (x2 d2 g2) "[gho [pt2 ⧖2]]".
      iMod (cumulative_persistent_time_receipt with "TIME ⧗' ⧖2") as "⧖2'". { solve_ndisj. }
      iModIntro. iFrame "pt". simpl.
      replace (length (ty_phys ty x tid)) with (length (ty_phys ty x2 tid)).
      2: { repeat rewrite ty_size_eq. done. }
      rewrite <- heap_cloc_mapsto_fancy_empty.
      iFrame. iApply (persistent_time_receipt_mono with "⧖2'"). lia.
     }
    { rewrite /uniq_body. iFrame "£saved".
      iApply (proph_ibor_proper with "ξBor"). intros c0.
      rewrite /uniq_payload /=. by rewrite !heap_complete_mapsto_fancy_empty. }
    iDestruct ("Halfback" with "H1 H2") as "X".
    iMod (fupd_mask_mono with "X") as "L". { set_solver. }
    iDestruct "£1" as "(£1 & £1')".
    iMod (lc_fupd_elim_later with "£1 Pers") as "#Pers'".
    iModIntro.
    iExists -[((l, repeat [] (ty.(ty_size))), x, ζi, (S d), g, ζidx)].
    iFrame "L". iFrame "UniqBody". iFrame "Incl".
    iSplit. 
    - iExists _, _.
      iSplit => //.
      iFrame.
      iSplit => //.
      iSplitR; first (iPureIntro; lia).
      iSplitR.
      rewrite <- heap_cloc_mapsto_empty. iApply guards_true. 
      iRight.  iNext.
      iApply (ty_gho_pers_depth_mono  with "Pers'"); lia. 
    - iCombine "Obs Obs2" as "Obs3".
      iApply (proph_obs_impl with "Obs3"). intros π [[_ Ha] Hb].
      apply Ha; intuition.
      + unfold uniq_bor_future. simpl. rewrite Hb. trivial.
      + unfold uniq_bor_future, uniq_bor_loc. simpl. rewrite Hb. trivial.
  Qed.

End typing.

Global Hint Resolve ptr_resolve : lrust_typing.
