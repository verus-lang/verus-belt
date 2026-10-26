From lrust.lang.lib Require Import memcpy new_delete.
From lrust.typing Require Export type.
From lrust.typing Require Import uninit type_context programs freeable_util tracked.
From guarding Require Import guard tactics.
From lrust.lifetime Require Import lifetime_full.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section own.
  Context `{!typeG Σ}.

  (** The sharing predicate of [own_ptr n ty] is structural: a guard of the points-to
      and the sharing predicate of the contents, under one later (to keep [own_ptr]
      contractive). The freeable token is not needed for shared access. *)
  Program Definition own_ptr {𝔄} (n: nat) (ty: type 𝔄) : type (at_locₛ 𝔄) := {|
    ty_size := 1;
    ty_lfts := ty.(ty_lfts);
    ty_E := ty.(ty_E);
    
    ty_gho_own x d g tid := [S(d') := d]
      ((fst x) ↦!∗ ty.(ty_phys) (snd x) tid) ∗
      freeable_sz n ty.(ty_size) (fst x) ∗
      ▷ (ty.(ty_gho_own) (snd x) d' g tid) ;
      
    ty_gho_pers x d g tid := [S(d') := d]
      ▷ (ty.(ty_gho_pers) (snd x) d' g tid) ;
    
    ty_phys x tid := [FVal (LitV (fst x))];
    ty_shr κ x d g tid :=
      ▷ [S(d') := d]
        (@[κ] &&{↑NllftG; g+1}&&> (fst x) ↦!∗ ty.(ty_phys) (snd x) tid) ∗
        ty.(ty_shr) κ (snd x) d' g tid;
  |}%I.
  Next Obligation. move=> ?????* //=. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation.
    move=> 𝔄 n ty [|d] g d' g' vπ tid ??; iIntros "H" => //=.
    iDestruct "H" as "(Hown & Hfree & Hgho)".
    destruct d'; first lia => /=.
    iDestruct (ty.(ty_gho_own_depth_mono) with "Hgho") as "[$ Hwand]" => //; first lia.
    iFrame. iFrame "%" => /=.
    iIntros "($ & $ & Hgho)".
    by iApply "Hwand".
  Qed.
  Next Obligation.
    move=> 𝔄 n ty [|d] g d' g' vπ tid ??; iIntros "H" => //=.
    destruct d'; first lia => /=.
    iDestruct (ty.(ty_gho_pers_depth_mono) with "H") as "$" => //; first lia.
  Qed.
  Next Obligation.
    intros 𝔄 n ty x d g tid. iIntros "A". destruct d as [|d']; first by done.
    iDestruct "A" as "[_ [_ pers]]". iApply ty_gho_pers_impl. iFrame.
  Qed.
  Next Obligation.
    intros 𝔄 n ty κ κ' x m d g tid. iIntros "#Incl Shr".
    iNext. destruct d as [|d']; [done|]. iDestruct "Shr" as "[Pt Shr]". iSplit.
    - replace (g + m + 1) with (m + (g + 1)) by lia.
      iApply (guards_transitive_additive with "Incl Pt").
    - iApply (ty_shr_lft_mono with "Incl Shr").
  Qed.
  Next Obligation.
    intros 𝔄 n ty κ d g d' g' x tid ??. iIntros "Shr".
    iNext. destruct d as [|d0]; [done|]. destruct d' as [|d0']; [lia|].
    iDestruct "Shr" as "[Pt Shr]". iSplit.
    - leaf_goal laters to (g+1). { lia. } iFrame "Pt".
    - iApply (ty_shr_depth_mono with "Shr"); lia.
  Qed.
  Next Obligation.
    intros 𝔄 n ty E κ x d g tid G ??. iIntros "#LFT #Incl #Pers #Gκ G Bor".
    destruct d as [|d']; [done|]. simpl.
    iMod (llftl_sep_split with "LFT Bor") as "[Pt Bor]"; [solve_ndisj|].
    iMod (llftl_sep_split with "LFT Bor") as "[_ Bor]"; [solve_ndisj|].
    iMod (llftl_bor_guard with "LFT Pt") as "#Pt"; [solve_ndisj|].
    iMod (llftl_bor_later_step with "LFT Gκ G Bor") as "Upd"; [first [apply _ | solve_ndisj]..|].
    iModIntro. iModIntro. iNext. iMod "Upd" as "[G Bor]".
    iMod (ty_share with "LFT Incl Pers Gκ G Bor") as "Shr"; [done..|].
    iModIntro. iApply (step_fupdN_wand with "Shr"). iIntros ">[$ Shr] !> !>".
    iFrame "Shr". leaf_goal laters to 1. { lia. } iFrame "Pt".
  Qed.
  Next Obligation.
    intros 𝔄 n ty κ x n0 d g tid ξ R Hin.
    iIntros "#LFT #Incl #Pers #Shr".
    destruct d as [|d']; first by done. simpl.
    iApply (bi.laterN_le (S (d' * (g + 1)))). { lia. }
    iNext. iDestruct "Shr" as "[_ Shr]".
    iDestruct (ty_shr_guard_proph ty κ x.2 n0 d' g tid ξ R Hin with "LFT Incl Pers Shr")
      as "GP".
    iNext. iIntros "#Rκ".
    leaf_goal laters to (n0 + (d'+1)*(g+1)). { lia. } by iApply "GP".
  Qed.
  
  Global Instance own_ne {𝔄} n : NonExpansive (@own_ptr 𝔄 n).
  Proof. solve_ne_type. Qed.

  Global Instance own_type_contractive 𝔄 n : TypeContractive (@own_ptr 𝔄 n).
  Proof.
    split; [by apply type_lft_morphism_id_like|done| | | |].
    - move=>/= > ->*. do 5 (f_contractive || f_equiv) => //; naive_solver.
    - intros. unfold ty_gho_pers, own_ptr. destruct d; first by done. simpl.
      f_contractive. naive_solver.
    - move=>/= > *. do 6 (f_contractive || f_equiv).
    - move=>/= n' ty ty' Sz _ _ EqOwn _ EqPhys EqShr κ x d g tid.
      apply later_contractive. split=> m Hm. destruct d as [|d']; [done|]. simpl.
      f_equiv; [by rewrite EqPhys|]. eapply dist_later_lt; [apply EqShr|lia].
  Qed.
  
  Lemma own_stack_okay {𝔄} n (ty: type 𝔄) : StackOkay (own_ptr n ty).
  Proof. done. Qed.

  Global Instance own_send {𝔄} n (ty: type 𝔄) : Send ty → Send (own_ptr n ty).
  Proof. move=> [Hphys Hgho]. split => //=.
       - intros tid tid' x x' He. inversion He. trivial.
       - intros tid tid' x d g G H κs d0 Hineq TG TH.
         iIntros "LFT UNIQ TIME Hg H Gg G Hgho #⧖o".
         destruct d => //=.
         iDestruct "Hgho" as "(Hown&Hfree&Hgho)".
         iFrame "%". iModIntro. iNext. iModIntro.
         iPoseProof (Hgho with "LFT UNIQ TIME Hg H Gg G Hgho ⧖o") as "X"; first lia.
         iApply (step_fupdN_wand with "X"). iIntros ">X".
         iDestruct "X" as (x' off) "[gho [#⧖off [%Habs [G H]]]]".
         rewrite (Hphys tid tid' (x.2) x'); last by done.
         iExists (x.1, x'), (off). iModIntro. iFrame. iFrame "#". iPureIntro. simpl.
         rewrite Habs. trivial.
  Qed.

  Global Instance own_sync {𝔄} n (ty: type 𝔄) : Sync ty → Sync (own_ptr n ty).
  Proof.
    move=> HSync tid tid' x d g.
    have EqOwn: ∀ d0 g0, (own_ptr n ty).(ty_gho_own) x d0 g0 tid ⊣⊢
        (own_ptr n ty).(ty_gho_own) x d0 g0 tid'.
    { move=> [|d0] g0 //=. destruct (HSync tid tid' x.2 d0 g0) as [-> [Hgho _]].
      by rewrite Hgho. }
    split => //=. split; [apply EqOwn|]. split.
    - destruct d => //=. destruct (HSync tid tid' x.2 d g) as [_ [_ [-> _]]]. done.
    - move=> κ. f_equiv.
      destruct d => //=. destruct (HSync tid tid' x.2 d g) as [-> [_ [_ Hshr]]].
      by rewrite Hshr.
  Qed.

  Global Instance own_just_loc {𝔄} n (ty: type 𝔄) : JustLoc (own_ptr n ty).
  Proof.
    iIntros (vπ [|] g tid) "Hgho" => //=.
    iDestruct "Hgho" as "(Hown&Hfree&Hgho)".
    by iExists _.
  Qed.

  Lemma own_resolve {𝔄} E L n (ty: type 𝔄) Φ :
    resolve E L ty Φ → resolve E L (own_ptr n ty) (λ '(l, v), Φ v).
  Proof.
    iIntros (Rslv G F x d g tid ??) "LFT PROPH UNIQ TIME E L own //".
    iIntros "Hgho".
    destruct d => //=.
    iDestruct "Hgho" as "(Hown&Hfree&Hgho)".
    iModIntro.
    replace (g + 1 + d * (g + 1)) with (S (g + d * (g + 1))) by lia.
    simpl. iModIntro. iNext.
    iDestruct (Rslv G F (snd x) d g tid _ with "[$] [$] [$] [$] [$] [$] [$] Hgho") as "Hrslv".
      { trivial. }
    iMod "Hrslv". iModIntro.
    iDestruct (step_fupdN_nmono with "Hrslv") as "Hrslv"; last first.
     - iApply (step_fupdN_wand with "Hrslv []").
       iIntros "F". iMod "F" as "[Obs G]".
       iModIntro. iFrame "G".
       iApply (proph_obs_impl with "Obs").
       intros π Ha. destruct x. apply Ha.
     - lia.
  Qed.

  Lemma own_type_incl {𝔄 𝔅} n (f: 𝔄 →ₛ 𝔅) ty1 ty2 :
    type_incl ty1 ty2 f -∗ type_incl (own_ptr n ty1) (own_ptr n ty2) (at_loc_mapₛ f).
  Proof.
    iIntros "(%Eq & #Incl & #InOwn & #InOwnPers & %Phys & #InShr)".
    iAssert (□ ∀ x d g tid, (own_ptr n ty1).(ty_gho_own) x d g tid -∗
      (own_ptr n ty2).(ty_gho_own) (at_loc_mapₛ f ~~$ₛ x) d g tid ∗
      ((own_ptr n ty2).(ty_gho_own) (at_loc_mapₛ f ~~$ₛ x) d g tid -∗
        (own_ptr n ty1).(ty_gho_own) x d g tid))%I as "#InOwn'". {
      iModIntro.
      iIntros ([l x0] [ | d] g tid) "Hown //=".
      iDestruct "Hown" as "(Hown&Hfree&Hgho)".
      iPoseProof ("InOwn" with  "Hgho") as "(Hgho & Hwand)".
      iSplitL "Hown Hfree Hgho".
      + rewrite Eq. rewrite Phys. iFrame.
      + iIntros "(Hown & Hfree & Hgho)".
        iFrame "%".
        rewrite Eq. rewrite Phys. iFrame.
        iNext.
        by iApply "Hwand".
    }
    do 3 (iSplit; [done|]).
    iSplit. {
      iModIntro.
      iIntros ([l x0] [ | d] g tid) "Hown //=".
      iApply "InOwnPers". iFrame.
    }
    iSplit. { iPureIntro. move => [l x0] tid. done. }
    iIntros "!>" (κ [l x0] d g tid) "Shr".
    iNext. destruct d as [|d]; [done|]. simpl. iDestruct "Shr" as "[Pt Shr]".
    rewrite -Phys. iFrame "Pt". by iApply "InShr".
  Qed.

  (** Unfolding the sharing predicate of [own_ptr]. (The result is stated with some
      slack in the later count of the guard and in [g].) *)
  Lemma own_shr_unfold {𝔄} n (ty: type 𝔄) E κ x d g tid :
    £ 1 -∗ (own_ptr n ty).(ty_shr) κ x (S d) g tid ={E}=∗
    (@[κ] &&{↑NllftG; g+2}&&> x.1 ↦!∗ ty.(ty_phys) x.2 tid) ∗
    ty.(ty_shr) κ x.2 d (S g) tid.
  Proof.
    iIntros "£ Shr".
    iMod (lc_fupd_elim_later with "£ Shr") as "[Pt Shr]". iModIntro. iSplit.
    - leaf_goal laters to (g+1). { lia. } iFrame "Pt".
    - iApply (ty_shr_depth_mono with "Shr"); lia.
  Qed.

  Lemma own_subtype {𝔄 𝔅} E L n (f: 𝔄 →ₛ 𝔅) ty ty' :
    subtype E L ty ty' f → subtype E L (own_ptr n ty) (own_ptr n ty') (at_loc_mapₛ f).
  Proof.
    move=> Sub. iIntros "L". iDestruct (Sub with "L") as "#Incl".
    iIntros "!> #E". iApply own_type_incl; by [|iApply "Incl"].
  Qed.

  Lemma own_eqtype {𝔄 𝔅} E L n (f: 𝔄 →ₛ 𝔅) g ty ty' :
    eqtype E L ty ty' f g → eqtype E L (own_ptr n ty) (own_ptr n ty') (at_loc_mapₛ f) (at_loc_mapₛ g).
  Proof. move=> [??]. split; by apply own_subtype. Qed.
End own.

Section box.
  Context `{!typeG Σ}.

  Definition box {𝔄} (ty: type 𝔄) : type (at_locₛ 𝔄) := own_ptr ty.(ty_size) ty.
  
  Definition own_tracked {𝔄} (ty: type 𝔄) : type (at_locₛ (trackedₛ 𝔄)) := own_ptr 0 (tracked_ty ty).

  Global Instance box_ne 𝔄 : NonExpansive (@box 𝔄).
  Proof. solve_ne_type. Qed.

  Global Instance box_type_contractive 𝔄 : TypeContractive (@box 𝔄).
  Proof.
    split; [by apply type_lft_morphism_id_like|done| | | |].
    - move=>/= > ->*. do 4 (f_contractive || f_equiv) => //.
      f_contractive; naive_solver.
    - intros. unfold ty_gho_pers, own_ptr. destruct d; first by done. simpl.
      f_contractive. naive_solver.
    - move=>/= *. do 6 (f_contractive || f_equiv).
    - move=>/= n' ty ty' Sz _ _ EqOwn _ EqPhys EqShr κ x d g tid.
      apply later_contractive. split=> m Hm. destruct d as [|d']; [done|]. simpl.
      f_equiv; [by rewrite EqPhys|]. eapply dist_later_lt; [apply EqShr|lia].
  Qed.

  Lemma box_type_incl {𝔄 𝔅} (f: 𝔄 →ₛ 𝔅) ty ty':
    type_incl ty ty' f -∗ type_incl (box ty) (box ty') (at_loc_mapₛ f).
  Proof.
    iIntros "[%Eq ?]". rewrite /box Eq. iApply own_type_incl. by iSplit.
  Qed.

  Lemma box_subtype {𝔄 𝔅} E L (f: 𝔄 →ₛ 𝔅) ty ty' :
    subtype E L ty ty' f → subtype E L (box ty) (box ty') (at_loc_mapₛ f).
  Proof.
    move=> Sub. iIntros "L". iDestruct (Sub with "L") as "#Incl".
    iIntros "!> #?". iApply box_type_incl. by iApply "Incl".
  Qed.

  Lemma box_eqtype {𝔄 𝔅} E L (f: 𝔄 →ₛ 𝔅) g ty ty' :
    eqtype E L ty ty' f g → eqtype E L (box ty) (box ty') (at_loc_mapₛ f) (at_loc_mapₛ g).
  Proof. move=> [??]. split; by apply box_subtype. Qed.
End box.

Section typing.
  Context `{!typeG Σ}.
   Lemma write_own {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) n E L :
    ty.(ty_size) = ty'.(ty_size) →
    typed_write E L (own_ptr n ty) ty (own_ptr n ty') ty' (λ v, v.2) (λ u b' u', u' = (u.1, b')).
  Proof.
    move=> Sz. split; [done|].
    iIntros ([l x0] [|d] v tid G ?) "LFT UNIQ E L G [Hgho %Hphys] //=".
    iDestruct "Hgho" as "(Hown&Hfree&Hgho)".
    rewrite /own_ptr /= in Hphys. move: Hphys; case => <-.
    iExists (l, repeat [] (length (ty_phys ty x0 tid))).
    iModIntro. iExists _. iExists True%I. iSplit => //. iSplit => //.
    iSplitL "Hown Hgho".
    - iNext. iModIntro.
      iExists (ty_phys ty x0 tid). { rewrite <- heap_cloc_mapsto_fancy_empty. by iFrame. }
    - iSplit; first by done.
      iSplit. { rewrite <- heap_cloc_mapsto_empty. iApply guards_true. }
      iIntros (??) "Hown H⧖ H£". rewrite /ty_own /=. rewrite <- Sz.
      iDestruct "Hown" as (vl) "[>Pt [Gho >%Phys]]".
      iIntros. iModIntro. iFrame. iExists (l, y).
      iSplit. { done. }
      iSplitL => //. rewrite <- Phys. iFrame.
      replace (length (ty_phys ty x0 tid)) with (length (ty_phys ty' y tid)).
       + rewrite <- heap_cloc_mapsto_fancy_empty. iFrame.
         iDestruct (ty_gho_own_depth_mono with "Gho") as "[$ _]"; lia.
       + do 2 rewrite ty_size_eq. done.
  Qed.

  Lemma read_own_copy {𝔄} (ty: type 𝔄) n E L :
    Copy ty → typed_read E L (own_ptr n ty) ty (own_ptr n ty) (λ v, snd v) (=).
  Proof.
    iIntros (Cpy [l x0] [ | d] v tid G ?)  "LFT E L G [Hgho %Hphys] Hd //=".
    iDestruct "Hgho" as "(Hown&Hfree&#Hgho)".
    iDestruct (copy_concrete with "Hgho") as ">%Conc".
    rewrite /own_ptr /= in Hphys.
    move:Hphys; case => <-.
    iExists (l, repeat [] (length (ty_phys ty x0 tid))).
    iExists (to_concrete (ty_phys ty x0 tid)).
    iExists (ty_phys ty x0 tid).
    iExists (l ↦!∗ ty_phys ty x0 tid)%I.
    iModIntro.
    iSplitR => //.
    iSplitR. { iPureIntro. apply length_to_concrete. }
    iFrame "Hown".
    iSplitR.
    { rewrite heap_mapsto_cells_fancy_empty. rewrite <- heap_mapsto_cells_fancy_fmap_eq.
      rewrite fmap_to_concrete. { iApply guard.guards_refl. } inversion Cpy; trivial. }
    rewrite /ty_own.
    iSplitR. {
      iIntros. rewrite <- heap_complete_mapsto_fancy_fmap_eq. rewrite fmap_to_concrete.
        { iFrame. done. } { trivial. }
    }
    iSplit. { inversion Cpy. rewrite fmap_to_concrete; done. }
    iSplit. { iNext. iSplitL => //. 
      iPoseProof (ty_gho_own_depth_mono _ d (S d) (S d) (S d) with "Hgho") as "[? _]"; [lia..|done]. }
    iIntros "Hown".
    iModIntro.
    simpl. iExists (l, x0). iFrame. by repeat iSplit.
  Qed.

  Lemma read_own_move {𝔄} (ty: type 𝔄) n E L :
    typed_read E L (own_ptr n ty) ty (own_ptr n (↯ ty.(ty_size))) (λ v, v.2) (λ v z, v.1 = z.1).
  Proof.
    iIntros ([l x] [ | d] v tid G ?)  "LFT E L G [Hgho %Hphys] Hd //=".
    iDestruct "Hgho" as "(Hown & Hfree & Hgho)".
    rewrite /own_ptr /= in Hphys.
    move:Hphys; case => <-.
    iMod (mapsto_vec_untether_emp _ _ _ ∅ with "Hown") as (vl_concrete) "[Hconc [%Hleneq [Retether %ConcreteEq]]]".
    iExists (l, repeat [] (length (ty_phys ty x tid))).
    iExists (vl_concrete).
    iExists (ty_phys ty x tid).
    iExists (l ↦∗ vl_concrete)%I.
    iModIntro.
    iSplitR => //.
    iSplitR. { done. }
    iFrame "Hconc".
    iSplitR. { rewrite heap_mapsto_cells_empty. rewrite Hleneq. iApply guards_refl. }
    iSplitL "Retether". { iIntros. iApply "Retether". done. }
    iSplit. { iPureIntro. intros Hsok. rewrite ConcreteEq; trivial. }
    rewrite /ty_own.
    iSplitL "Hgho".
    { iNext. iSplitL => //. 
      iPoseProof (ty_gho_own_depth_mono _ d (S d) (S d) (S d) with "Hgho") as "[? _]"; [lia..|done]. }
    iIntros "Hown".
    iModIntro.
    replace (ty_size ty) with (length (ty_phys ty x tid)); last by (apply ty_size_eq).
    rewrite <- Hleneq.
    iExists (l, list_to_vec vl_concrete).
    iSplit. { done. }
    simpl.
    iFrame.
    repeat iSplit => //. rewrite vec_to_list_to_vec. rewrite heap_mapsto_fancy_fmap_eq. trivial.
  Qed.

  Lemma type_new_instr n E L I :
    0 ≤ n → let n' := Z.to_nat n in
    typed_instr_ty E L I +[] (new [ #n])%E (own_ptr n' (↯ n'))
        (λ post _ mask π, ∀ l junk, post (l, junk) mask π).
  Proof.
    iIntros (???????) "_ TIME _ _ _ $$ _ Proph". iMod persistent_time_receipt_0 as "⧖".
    iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|].
    iIntros "? #⧖".
    iApply wp_new=>//; [lia|].
    iIntros "!>" (l) "(† & ↦)". iExists -[(l, vrepeat #☠ (Z.to_nat n))].
    iModIntro.
    iSplit.
    { simpl. rewrite /tctx_elt_interp. 
      iSplit => //=.
      rewrite /ty_own /=.
      iExists #l, 1%nat.
      iFrame "⧖".
      rewrite/= freeable_sz_full Z2Nat.id; [|lia].
      iSplit => //.
      iSplit => //.
      rewrite vec_to_list_vrepeat. iFrame.
      rewrite heap_mapsto_fancy_fmap_eq. iFrame. done.
    }
    simpl.
    iApply proph_obs_impl; last by iFrame "Proph".
    done.
  Qed.

  Lemma type_new {𝔄l 𝔅} n x e tr E L (I: invctx) (C: cctx 𝔅) (T: tctx 𝔄l) :
    Closed (x :b: []) e → 0 ≤ n → let n' := Z.to_nat n in
    (∀v: val, typed_body E L I C (v ◁ own_ptr n' (↯ n') +:: T) (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := new [ #n] in e)
      (λ post al mask π, forall l junk, tr post ((l, junk) -:: al) mask π).
  Proof.
    iIntros. 
    iApply type_let. 
    - by apply type_new_instr.
    - solve_typing.
    - instantiate (1 := tr).
      done.
    - done.
  Qed.

  Lemma type_new_subtype {𝔄 𝔅l ℭ} (ty: type 𝔄) n (T: tctx 𝔅l) f e tr x E L I (C: cctx ℭ) :
    Closed (x :b: []) e → 0 ≤ n → let n' := Z.to_nat n in
    subtype E L (↯ n') ty f →
    (∀v: val, typed_body E L I C (v ◁ own_ptr n' ty +:: T) (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := new [ #n] in e) (λ post al mask π, forall l junk, tr post ((l, f ~~$ₛ junk) -:: al) mask π).
  Proof.
    iIntros (??? Sub) "?".
    iApply type_let; [by apply type_new_instr|solve_typing| |]; last first.
    { iIntros (?).
      iApply typed_body_tctx_incl;
        [eapply subtype_tctx_incl, own_subtype, Sub|done]. }
    done.
  Qed.

  Lemma type_delete_instr {𝔄} (ty: type 𝔄) (n: Z) p E L I :
    let n' := ty.(ty_size) in n = Z.of_nat n' →
    typed_instr E L I +[p ◁ own_ptr n' ty] (new_delete.delete [ #n; p])%E (λ _, +[])
      (λ post _, post -[]).
  Proof.
    iIntros (?->? ? ? ? [[l x][]]) "_ _ _ _ _ $$ [p _] #Obs". 
    wp_bind p.
    iApply (wp_hasty with "p"). 
    rewrite /ty_own /=.
    iIntros (?[|?] _) "? [own %]"; [done|].
    iDestruct "own" as "(Hown & Hfree & Hgho)".
    move: H; case => <-.
    pose proof (ty.(ty_size_eq) ) as Sz.
    iMod (mapsto_vec_untether_emp _ _ _ ∅ with "Hown") as (vl_concrete) "[Hconc [%Hleneq _]]".
    iApply (wp_delete vl_concrete n' with "[-] []")=>//.
    {  unfold n'. rewrite Hleneq. by rewrite Sz. }
    { iFrame. rewrite Hleneq. rewrite Sz. by iApply freeable_sz_full. }
    { iNext. iIntros. iExists nil_tt. iSplit => //; iFrame. }
  Qed.

  Lemma type_delete {𝔄 𝔅l ℭl 𝔇} (ty: type 𝔄) n' (n: Z) p e
    E L I (C: cctx 𝔇) (T: tctx 𝔅l) (T': tctx ℭl) trx tr :
    Closed [] e → tctx_extract_ctx E L +[p ◁ own_ptr n' ty] T T' trx →
    n' = ty.(ty_size) → n = n' → typed_body E L I C T' e tr -∗
    typed_body E L I C T (new_delete.delete [ #n; p ];; e) (trx ∘ (λ post '(_ -:: al), tr post al)).
  Proof.
    iIntros (? Extr -> ?) "?". iApply type_seq; [by eapply type_delete_instr|done| |done].
    destruct Extr as [Htrx _]=>?? /=. apply Htrx. by case.
  Qed.
  
  (* T to Tracked<T> *)
  
  Lemma type_delete2_instr {𝔄} (ty: type 𝔄) (n: Z) p E L I :
    let n' := ty.(ty_size) in n = Z.of_nat n' →
    typed_instr E L I
      +[p ◁ own_ptr n' ty]
      (new_delete.delete [ #n; p])%E
      (λ _, +[p ◁ own_tracked ty])
      (λ post π, post π).
  Proof.
    iIntros (?->? ? ? ? [[l x][]]) "? ? ? ? ? $$ [p _] #Obs". 
    wp_bind p.
    iApply (wp_hasty with "p"). 
    rewrite /ty_own /=.
    iIntros (?[|?] Hpath) "#⧖ [own %Hv]"; [done|]. 
    iDestruct "own" as "(Hown & Hfree & Hgho)".
    inversion Hv. subst v.
    pose proof (ty.(ty_size_eq) ) as Sz.
    iMod (mapsto_vec_untether_emp  _ _ _ ∅ with "Hown") as (vl_concrete) "[Hconc [%Hleneq _]]".
    iApply (wp_delete (vl_concrete) n' with "[Hconc Hfree] [Hgho]")=>//.
    {  unfold n'. rewrite Hleneq. by rewrite Sz. }
    { iFrame. rewrite Hleneq. rewrite Sz. by iApply freeable_sz_full. }
    { iNext. iIntros. iExists -[(l, x)]. iSplit => //; iFrame.
      iSplit; last by done. unfold tctx_elt_interp.
      iExists (#l), (S n). iSplit. { iPureIntro. by symmetry. }
      iFrame "⧖". iSplit. { iFrame. simpl. rewrite heap_mapsto_fancy_vec_nil. done. }
      iPureIntro. done.
    }
  Qed.

  Lemma type_letalloc_1 {𝔄 𝔅l ℭl 𝔇} (ty: type 𝔄) (x: string) p e
    (T: tctx 𝔅l) (T': tctx ℭl) (tr : predl_trans' ((at_locₛ 𝔄) :: ℭl) 𝔇) (trx : predl_trans 𝔅l ([𝔄] ++ ℭl)) tr_res E L I (C: cctx 𝔇) :
    Closed [] p → Closed [x] e →
    tctx_extract_ctx E L +[p ◁ ty] T T' trx →
    tr_res ≡ (λ pred_d, trx (λ '(a -:: cl) mask π, ∀ l, tr pred_d ((l, a) -:: cl) mask π) ) →
    ty.(ty_size) = 1%nat →
    (∀v: val, typed_body E L I C (v ◁ box ty +:: T') (subst x v e) tr) -∗
    typed_body E L I C T (letalloc: x <- p in e) tr_res.
  Proof.
    iIntros (???? Sz) "?".
    iApply (typed_body_impl _ (_ ∘ _)).
    { move => post xl mask π Htr_res.
      apply H2 in Htr_res.
      apply Htr_res. }
    iApply typed_body_tctx_incl; [done|].
    set (tr' := (λ post (al : plist ~~ (at_locₛ (uninitₛ (Z.to_nat (Z.of_nat 1))):: 𝔄 :: ℭl)) mask π, let '( (l, junk) -:: a -:: rest) := al in tr post ((l,a) -:: rest) mask π)).
    iApply (@typed_body_impl _ _ (𝔄 :: ℭl) _ _ (λ post al mask π, ∀ l junk, tr' post ((l, junk) -:: al) mask π)); last first.
    - iApply (@type_new (𝔄 :: ℭl) 𝔇 _ _ _ tr'); [|lia|].
      + rewrite /Closed /= !andb_True. split; [done|]. split; [|done].
        split; [apply bool_decide_spec|eapply is_closed_weaken=>//]; set_solver.
      + iIntros (xv) "/=".
        have ->: (subst x xv (x <- p;; e))%E = (xv <- p;; subst x xv e)%E.
        { rewrite /subst /=.
          repeat f_equal;
            [by rewrite bool_decide_true|eapply is_closed_subst=>//; set_solver]. }
        iApply typed_body_impl; last first.
        { iApply (type_assign (own_ptr (Z.to_nat 1%nat) (↯ (Z.to_nat 1%nat))) (↯ (Z.to_nat 1%nat))%T (own_ptr (Z.to_nat 1%nat) ty) ty snd _ _ _ _ _ _ _ _ _ T' id tr _).
          * apply subst_is_closed; [apply is_closed_of_val|done].
          * eapply tctx_extract_ctx_eq.
            eapply tctx_extract_ctx_elt.
            apply tctx_extract_elt_here_exact.
            eapply tctx_extract_ctx_elt.
            apply tctx_extract_elt_here_exact.
            apply tctx_extract_ctx_nil.
            rewrite /id /compose/trans_tail //=.
            fun_ext => a.
            fun_ext => b /=.
            by destruct b as [[? ?] [? ?]].
          * apply (write_own (↯ (Z.to_nat 1%nat)) ty 1%nat ) => /=; lia.
          * rewrite /resolve'.
            instantiate (1:= λ _ _ x, x).
            eapply resolve_impl => //; first apply uninit_resolve.
          * by rewrite /box Sz.
        }
        move=>/= ?[[??][? ?]]????/=?; subst.
        done.
    - move => ?[??]????? //=.
  Qed.

  (* Lemma type_letalloc_n {𝔄 𝔅 𝔅' ℭl 𝔇l 𝔈} (ty: type 𝔄) (tyr: type 𝔅) *)
  (*       (tyr': type 𝔅') gt st (T: tctx ℭl) (T': tctx 𝔇l) trx tr (x: string) *)
  (*       p e E L (C: cctx 𝔈) : *)
  (*   Closed [] p → Closed [x] e → tctx_extract_ctx E L +[p ◁ tyr] T T' trx → *)
  (*   typed_read E L tyr ty tyr' gt st → *)
  (*   (∀v: val, typed_body E L C (v ◁ box ty +:: p ◁ tyr' +:: T') (subst x v e) tr) -∗ *)
  (*   typed_body E L C T (letalloc: x <-{ty.(ty_size)} !p in e) (trx ∘ *)
  (*     (λ post '(b -:: bl), tr post (gt b -:: st b -:: bl))). *)
  (* Proof. *)
  (*   iIntros. iApply typed_body_tctx_incl; [done|]. *)
  (*   iApply typed_body_impl; last first. *)
  (*   { iApply type_new; [|lia|]=>/=. *)
  (*     - rewrite /Closed /=. rewrite !andb_True. *)
  (*       eauto 10 using is_closed_of_val, is_closed_weaken with set_solver. *)
  (*   - iIntros (xv). *)
  (*     have ->: subst x xv (x <-{ty.(ty_size)} !p;; e)%E = *)
  (*              (xv <-{ty.(ty_size)} !p;; subst x xv e)%E. *)
  (*     { rewrite /subst /=. repeat f_equal. *)
  (*       - eapply (is_closed_subst []); [apply is_closed_of_val|set_solver]. *)
  (*       - by rewrite bool_decide_true. *)
  (*       - eapply is_closed_subst; [done|set_solver]. } *)
  (*     rewrite Nat2Z.id. iApply type_memcpy. *)
  (*     + apply subst_is_closed; [apply is_closed_of_val|done]. *)
  (*     + solve_typing. *)
  (*     + by apply (write_own ty (uninit _)). *)
  (*     + solve_typing. *)
  (*     + done. *)
  (*     + done. *)
  (*     + done. } *)
  (*     by move=>/= ?[??]?. *)
  (* Qed. *)

End typing.

Global Hint Resolve own_resolve own_subtype own_eqtype
  box_subtype box_eqtype write_own read_own_copy : lrust_typing.
(* By setting the priority high, we make sure copying is tried before
   moving. *)
Global Hint Resolve read_own_move | 100 : lrust_typing.
