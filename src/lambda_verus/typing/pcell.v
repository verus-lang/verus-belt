From lrust.lang.lib Require Import memcpy.
From lrust.lang Require Import heap.
From lrust.typing Require Export type own product sum shr_bor uniq_bor uniq_util int bool.
From lrust.typing Require Import uninit type_context programs freeable_util.
From guarding Require Import guard tactics.
From lrust.lifetime Require Import lifetime_full.

Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section pcell.
  Context `{!typeG Σ}.

  Program Definition pcell_ty n : type (pcellₛ n) :=
    {| ty_size := n;
      ty_gho_own x _ _ _ := ⌜ length x = n ⌝;
      ty_gho_pers  x _ _ _ := ⌜ length x = n ⌝;
      ty_phys (cell_ids: ~~ (pcellₛ n)) _ := pad (FCell <$> cell_ids) n ;
      ty_lfts := [];
      ty_E := [];
      ty_shr := default_shr (λ (x: ~~(pcellₛ n)) _ _ _, ⌜ length x = n ⌝);
     |}%I.
  Next Obligation. move => n v tid. by rewrite length_pad. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. move => *. iIntros "?". auto. Qed.
  Next Obligation. move => *. iIntros "?". auto. Qed.
  Next Obligation.
      intros n κ x n0 d g tid ξ R Hin. simpl in Hin. set_solver.
  Qed.
  Next Obligation. move => *. by iIntros "?". Qed.
  Solve All Obligations with solve_default_shr.
  
  Global Instance pcell_send n: Send (pcell_ty n).
  Proof.
    intros. split; trivial.
     - intros. unfold syn_abstract in H. simpl in H.
       rewrite H. trivial.
     - iIntros. iApply step_fupdN_intro; first done. iNext.
       iExists x, 0%nat. iModIntro. iFrame. simpl.
       replace (d0 + 0)%nat with d0 by lia. iFrame "#". done.
  Qed.
  
  Global Instance pcell_sync n: Sync (pcell_ty n).
  Proof. apply sync_default; [done|]. split; trivial. split; iSplit; done. Qed.
End pcell.

Section points_to.
  Context `{!typeG Σ}.

  Program Definition cell_points_to_ty {𝔄} (ty: type 𝔄) : type (trackedₛ (pcellₛ (ty.(ty_size)) * 𝔄)) := 
    {| ty_size := 0%nat;
      ty_lfts := ty.(ty_lfts);
      ty_E := ty.(ty_E);
      ty_gho_own x d g tid := 
        [S(d') := d] (cells_points_to_fancy_value_vec x.1 (ty.(ty_phys) x.2 tid))%I ∗ ▷ (ty.(ty_gho_own) x.2 d' g tid) ;
      ty_gho_pers x d g tid := 
        [S(d') := d] ⌜ length x.1 = ty_size ty ⌝ ∗ ▷ (ty.(ty_gho_pers) (snd x) d' g tid) ;
      ty_phys _ _ := [];
      (* Structural, as for [own_ptr] (see there, also for the TEMPORARY alternative). *)
      ty_shr κ x d g tid :=
        (▷ [S(d') := d]
          (@[κ] &&{↑NllftG; g+1}&&> cells_points_to_fancy_value_vec x.1 (ty.(ty_phys) x.2 tid)) ∗
          ty.(ty_shr) κ x.2 d' g tid) ∨
        default_shr (λ (x: ~~(trackedₛ (pcellₛ (ty.(ty_size)) * 𝔄))) d g tid, [S(d') := d] (cells_points_to_fancy_value_vec x.1 (ty.(ty_phys) x.2 tid))%I ∗ ▷ (ty.(ty_gho_own) x.2 d' g tid)) κ x d g tid;
    |}%I.
  Next Obligation. move => 𝔄 tyA v tid //=. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation.
    move => 𝔄 ty d g d' g' v tid ??//=.
    iIntros "H".
    destruct d => //=.
    destruct d' => //=; first lia.
    iDestruct "H" as "[H↦ Hgho]".
    iFrame "H↦".
    iDestruct (ty.(ty_gho_own_depth_mono) with "Hgho") as "[$ Hwand]" => //; first lia.
    iIntros "[$ Hgho] !>".
    by iApply "Hwand".
  Qed.
  Next Obligation.
    move => 𝔄 ty d g d' g' v tid ??//=.
    iIntros "H".
    destruct d => //=.
    destruct d' => //=; first lia.
    iDestruct "H" as "[$ H]".
    iNext.
    iDestruct (ty.(ty_gho_pers_depth_mono) _ _ d' g' with "H") as "?" => //; lia.
  Qed.
  Next Obligation.
    intros 𝔄 ty κ x n0 d g tid ξ R Hin.
    iIntros "#CTX #Incl #GhoPers'".
    destruct d as [|d']; first by done.
    iDestruct "GhoPers'" as "[% GhoPers]".
    simpl in Hin.
    iDestruct (ty_guard_proph _ ty _ _ (n0+1) _ _ _ ξ R Hin with "CTX Incl GhoPers") as "#L".
    iApply (bi.laterN_le (S (d' * (g + 1)))). { lia. }
    iNext. iNext. iIntros "#A #B".
    leaf_goal laters to (n0 + 1 + d' * (g + 1)). { lia. }
    iApply "L".
      - leaf_goal laters to n0. { lia. } iFrame "A".
      - iApply (guards_transitive_additive with "B []"). leaf_by_sep.
        simpl. iIntros "[C D]". iNext. iFrame. iIntros. iFrame.
  Qed.
  Next Obligation.
    intros 𝔄 ty x d g tid. iIntros "A". destruct d as [|d']; first by done.
    iDestruct "A" as "[A1 A2]".
    iDestruct (cells_points_to_fancy_vec_length_eq with "A1") as "%".
    rewrite (ty_size_eq ty) in H.
    iSplit => //.
    iApply ty_gho_pers_impl. iFrame.
  Qed.
  Next Obligation.
    intros 𝔄 ty κ κ' x d g tid. iIntros "#Incl [Shr|Shr]".
    - iLeft. iNext. destruct d as [|d']; [done|]. iDestruct "Shr" as "[Pt Shr]". iSplit.
      + iApply (guards_transitive_right with "Incl Pt").
      + iApply (ty_shr_lft_mono with "Incl Shr").
    - iRight. by iApply (default_shr_lft_mono with "Incl Shr").
  Qed.
  Next Obligation.
    intros 𝔄 ty κ d g d' g' x tid ??. iIntros "[Shr|Shr]".
    - iLeft. iNext. destruct d as [|d0]; [done|]. destruct d' as [|d0']; [lia|].
      iDestruct "Shr" as "[Pt Shr]". iSplit.
      + leaf_goal laters to (g+1). { lia. } iFrame "Pt".
      + iApply (ty_shr_depth_mono with "Shr"); lia.
    - iRight. by iApply (default_shr_depth_mono with "Shr").
  Qed.
  Next Obligation.
    intros 𝔄 ty E κ x k d g tid G ?? Hle. iIntros "#LFT #Incl #Gκ G Bor".
    destruct d as [|d'].
    { iMod (llftl_bor_guarded_pers with "LFT Gκ G Bor") as "[$ #F]"; [solve_ndisj|].
      iAssert (▷^k ▷ False)%I as "#F'". { rewrite -bi.laterN_later. iExact "F". }
      iModIntro. iNext. iLeft. iNext. done. }
    simpl.
    iMod (llftl_bor_laterN_sep_split with "LFT Bor") as "[Pt Bor]"; [solve_ndisj|].
    iMod (llftl_bor_laterN_guard with "LFT Pt") as "#Pt"; [solve_ndisj|].
    iDestruct (llftl_bor_iff _ _ (▷^(S k) ty.(ty_gho_own) x.2 d' g tid) with "[] Bor") as "Bor".
    { iIntros "!> !>". rewrite -bi.laterN_later. iSplit; iIntros "H"; iExact "H". }
    iMod (ty_share ty E κ x.2 (S k) d' g tid G with "LFT Incl Gκ G Bor")
      as "[$ Shr]"; [first [done | lia]..|].
    iAssert (▷^k ▷ ty.(ty_shr) κ x.2 d' g tid)%I with "[Shr]" as "Shr".
    { rewrite -bi.laterN_later. iExact "Shr". }
    iModIntro. iNext. iLeft. iNext. iFrame "Shr".
    leaf_goal laters to (1 + k). { lia. } iFrame "Pt".
  Qed.
  Next Obligation.
    intros 𝔄 ty κ x n0 d g tid ξ R Mono GP Hin.
    iIntros "#LFT #Incl #Pers [#Shr|#Shr]"; last first.
    { by iApply (default_shr_guard_proph with "LFT Incl Pers Shr"). }
    destruct d as [|d']; first by done. simpl.
    iDestruct "Pers" as "[_ Pers]".
    iApply (bi.laterN_le (S (d' * (g + 1)))). { lia. }
    iNext. iDestruct "Shr" as "[_ Shr]".
    iDestruct (ty_shr_guard_proph ty κ x.2 n0 d' g tid ξ R Hin with "LFT Incl Pers Shr")
      as "GP".
    iNext. iIntros "#Rκ".
    leaf_goal laters to (n0 + (d'+1)*(g+1)). { lia. } by iApply "GP".
  Qed.
  Next Obligation.
    intros 𝔄 ty κ x d g tid. iIntros "#G". iRight. by iApply default_shr_from_guard.
  Qed.

  Global Instance cell_points_to_send {𝔄} (ty: type 𝔄) :
      Send ty → Send (cell_points_to_ty ty).
  Proof.
    intros [Hphys Hgho]. split; trivial.
    intros tid tid' x d g G H κs d0 Hineq TG TH.
    iIntros "LFT UNIQ TIME Hg H Gg G Hgho #⧖o".
    destruct d => //=.
    iDestruct "Hgho" as "(Hown&Hgho)".
    iModIntro. iNext. iModIntro.
    iPoseProof (Hgho with "LFT UNIQ TIME Hg H Gg G Hgho ⧖o") as "X"; first lia.
    iApply (step_fupdN_wand with "X"). iIntros ">X".
    iDestruct "X" as (x' off) "[gho [#⧖off [%Habs [G H]]]]".
    rewrite (Hphys tid tid' (x.2) x'); last by done.
    iExists (x.1, x'), (off). iModIntro. iFrame. iFrame "#". iPureIntro. simpl.
    rewrite Habs. trivial.
  Qed.
  
  Global Instance cell_points_to_sync {𝔄} (ty: type 𝔄) :
      Sync ty → Sync (cell_points_to_ty ty).
  Proof.
      move=> HSync tid tid' x d g.
      have EqOwn: ∀ d0 g0, (cell_points_to_ty ty).(ty_gho_own) x d0 g0 tid ⊣⊢
          (cell_points_to_ty ty).(ty_gho_own) x d0 g0 tid'.
      { move=> [|d0] g0 //=. destruct (HSync tid tid' x.2 d0 g0) as [-> [Hgho _]].
        by rewrite Hgho. }
      split => //=. split; [apply EqOwn|]. split.
      - destruct d => //=.
        pose proof (sync_change_tid tid tid' (snd x) d g) as [_ [Hgho [Hghopers _]]].
        rewrite Hghopers. trivial.
      - move=> κ. f_equiv.
        + destruct d => //=. destruct (HSync tid tid' x.2 d g) as [-> [_ [_ Hshr]]].
          by rewrite Hshr.
        + apply default_shr_change_tid=> d0 g0. apply EqOwn.
  Qed.

  (** Unfolding the sharing predicate of [cell_points_to_ty], as [own_shr_unfold]. This
      version takes the sharing predicate with the later of its first alternative
      stripped (as it is after a program step); see [cell_points_to_shr_unfold] for the
      version with a credit. *)
  Lemma cell_points_to_shr_unfold' {𝔄} (ty: type 𝔄) κ x d g tid :
    ([S(d') := d]
        (@[κ] &&{↑NllftG; g+1}&&> cells_points_to_fancy_value_vec x.1 (ty.(ty_phys) x.2 tid)) ∗
        ty.(ty_shr) κ x.2 d' g tid) ∨
    default_shr (cell_points_to_ty ty).(ty_gho_own) κ x d g tid -∗
    (@[κ] &&{↑NllftG; g+2}&&> [S(d') := d]
        cells_points_to_fancy_value_vec x.1 (ty.(ty_phys) x.2 tid)) ∗
    (∀ d', ⌜d = S d'⌝ -∗ ty.(ty_shr) κ x.2 d' (S g) tid).
  Proof.
    iIntros "[Shr|Shr]".
    - destruct d as [|d]; [simpl; by iDestruct "Shr" as %[]|].
      iDestruct "Shr" as "[Pt Shr]". iSplit.
      + leaf_goal laters to (g+1). { lia. } iFrame "Pt".
      + iIntros (? [= <-]). iApply (ty_shr_depth_mono with "Shr"); lia.
    - (* TEMPORARY: uses [ty_shr_from_guard]. *)
      rewrite default_shr_guard; [|exact (ty_gho_own_depth_mono (cell_points_to_ty ty))].
      iDestruct "Shr" as "#G". iSplit.
      + leaf_goal laters to (g+1). { lia. }
        iApply (guards_transitive_left with "G"). leaf_by_sep.
        destruct d as [|d]; simpl; [by iIntros "[]"|]. iIntros "($ & A) P". iFrame.
      + iIntros (d' ->). iApply ty_shr_from_guard. leaf_goal laters to (g + 1 + 1). { lia. }
        iApply (guards_transitive_additive _ _ _ _ (g+1) 1 with "G []").
        leaf_by_sep. simpl. iIntros "(Pt & Gho)". iNext.
        iDestruct (ty_gho_own_depth_mono _ d' g d' (S g) with "Gho") as "[$ Back]"; [lia..|].
        iIntros "Gho". iFrame. by iApply "Back".
  Qed.

  Lemma cell_points_to_shr_unfold {𝔄} (ty: type 𝔄) E κ x d g tid :
    £ 1 -∗ (cell_points_to_ty ty).(ty_shr) κ x d g tid ={E}=∗
    (@[κ] &&{↑NllftG; g+2}&&> [S(d') := d]
        cells_points_to_fancy_value_vec x.1 (ty.(ty_phys) x.2 tid)) ∗
    (∀ d', ⌜d = S d'⌝ -∗ ty.(ty_shr) κ x.2 d' (S g) tid).
  Proof.
    iIntros "£ [Shr|Shr]".
    - iMod (lc_fupd_elim_later with "£ Shr") as "Shr". iModIntro.
      iApply cell_points_to_shr_unfold'. by iLeft.
    - iModIntro. iApply cell_points_to_shr_unfold'. by iRight.
  Qed.
End points_to.

Section typing.

  Context `{!typeG Σ}.

  Definition PCellFromOwn : val :=
    (λ: ["p"], "p")%V.

  Lemma typed_pcell_from_own {𝔄} (p : path) (ty : type 𝔄) E L I :
    typed_instr E L I +[p ◁ own_ptr (ty_size ty) ty] (PCellFromOwn [p]) (λ v, +[v ◁ own_ptr (ty_size ty) (prod_ty (pcell_ty (ty_size ty)) (cell_points_to_ty ty))]) (λ post '-[(l, x)], λ mask π, ∀ (cell_ids : list positive), post -[(l, (cell_ids, (cell_ids, x)))] mask π).
  Proof.
    move => tid postπ mask iκs vπl.
    iIntros "#LFT #TIME #PROPH UNIQ E L $ TY #Obs" => /=.
    destruct vπl as [[l x][]].
    iDestruct "TY" as "(TY & _)".
    iDestruct "TY" as (pl d Heval) "(#Hd & Hown & %Hphys)".
    simpl in Hphys.
    inversion Hphys; subst pl.
    destruct d => //=.
    iDestruct "Hown" as "(Hl & Hfree & Hgho)".
    iApply wp_fupd.
    wp_bind p.
    iApply wp_wand.
    iApply wp_eval_path => //.
    iIntros (? ->).
    iApply (wp_persistent_time_receipt with "TIME Hd"); [done|].
    iIntros "£ #Hd'".
    wp_rec.
    iMod (cell_alloc2 with "Hl") as "[%γs [% H↦]]".
    set cl := ((l, (λ γ, [γ]) <$> γs) : cloc).
    change l with cl.1. change (app [] <$> γs) with cl.2.
    rewrite heap_mapsto_cells_to_complete_mapsto_fancy_vec.
    iDestruct "H↦" as "[Hchain Htail]".
    rewrite heap_complete_mapsto_vec_eq.
    rewrite (ty.(ty_size_eq)) in H.
    iExists -[(l, (γs, (γs, x)))].
    iFrame.
    rewrite /tctx_elt_interp/ty_own/=.
    iSplitL.
    - iModIntro.
      iSplitL => //.
      iExists _, _.
      iFrame "Hd'".
      do 2 iSplit => //=.
      rewrite Nat.add_0_r app_nil_r pad_length'.
      2: by rewrite length_fmap -H.
      iFrame.
      iNext.
      iSplit => //.
      unfold cl.
      rewrite heap_complete_mapsto_fancy_val_vec_eq'.
      iFrame.
      iNext.
      iDestruct (ty.(ty_gho_own_depth_mono) with "Hgho") as "($ & ?)"; lia.
    - iApply (proph_obs_impl with "Obs").
      intros π Hpost.
      apply Hpost.
  Qed.

  Definition PCell2Own : val :=
    (λ: ["pcell"; "perm"], "pcell")%V.

  Lemma typed_pcell_to_own {𝔄} (perm pcell : path) (ty : type 𝔄) E L I :
    typed_instr E L I +[pcell ◁ own_ptr (ty_size ty) (pcell_ty (ty_size ty)); perm ◁ own_ptr 0 (cell_points_to_ty ty)] (PCell2Own [pcell; perm]) (λ v, +[v ◁ own_ptr (ty_size ty) ty]) (λ post '-[(l, γs); (_, (γs', x))], λ mask π, γs = γs' ∧ post -[(l, x)] mask π).
  Proof.
    move => tid postπ mask iκs vπl.
    iIntros "#LFT #TIME #PROPH UNIQ E L $ TY #Obs" => /=.
    destruct vπl as [[l γs] [[l' [γs' x]] []]].
    iDestruct "TY" as "(Hpcell & Hperm & _)".
    iDestruct "Hpcell" as (pl d Heval) "(#Hd & Hown & %Hphys)".
    iDestruct "Hperm" as (pl' d' Heval') "(#Hd' & Hown' & %Hphys')".
    simpl in Hphys, Hphys'.
    inversion Hphys; subst pl.
    inversion Hphys'; subst pl'.
    destruct d => //.
    destruct d' => //=.
    iDestruct "Hown" as "(H↦ & Hfree & >%Hlen)".
    iDestruct "Hown'" as "(_ & _ & Hown)".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & _)" => //.
    rewrite /PCell2Own.
    wp_bind pcell.
    iApply wp_wand.
    iApply wp_eval_path => //.
    iIntros (? ->).
    wp_bind perm.
    iApply wp_wand.
    iApply wp_eval_path => //.
    iIntros (? ->).
    iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME Hd"); [done|].
    iIntros "£ #Hd''".
    wp_rec.
    iDestruct "£" as "[£1 [£2 £3]]".
    destruct d' => /=.
    { by iMod (lc_fupd_elim_later with "£2 Hown"). }
    iClear "£1 £2 £3".
    rewrite pad_length'.
    2: by rewrite length_fmap.
    iDestruct "Hown" as "[H↦' Hgho]".
    rewrite -heap_complete_mapsto_fancy_val_vec_eq'.
    iExists -[(l, x)].
    iFrame.
    rewrite /tctx_elt_interp/ty_own/=.
    iSplitL.
    - iMod (heap_delete_cell with "H↦ H↦'") as "H↦".
      iModIntro.
      iSplit => //.
      iExists _, (S (S d')).
      do 2 iSplit => //=.
      iSplitL => //.
      iFrame.
      iDestruct (ty.(ty_gho_own_depth_mono) with "Hgho") as "($ & ?)"; lia.
    - iApply (proph_obs_impl with "Obs").
      intros π' Hpost.
      apply Hpost.
  Qed.

  Definition PCellBorrow : val :=
    (λ: ["pcell_ref"; "perm_ref"], "pcell_ref")%V.

  Lemma typed_pcell_borrow {𝔄} κ (pcell_ref perm_ref : path) (ty : type 𝔄) E L I :
    (* lctx_lft_alive E L κ → *)
    typed_instr E L I +[pcell_ref ◁ shr_bor κ (pcell_ty (ty_size ty)); perm_ref ◁ shr_bor κ (cell_points_to_ty ty)] (PCellBorrow [pcell_ref; perm_ref]) (λ v, +[v ◁ shr_bor κ ty]) (λ post '-[(l, γs); (_, (γs', x))], λ mask π, γs = γs' ∧ post -[(cloc_flat_insert l γs, x)] mask π).
  Proof.
    move => tid postπ mask iκs vπl.
    iIntros "#LFT #TIME #PROPH #UNIQ #E L $ TY #Obs" => /=.
    destruct vπl as [[l γs] [[l' [γs' x]] []]].
    iDestruct "TY" as "(Hcell & Hperm & _)".
    iDestruct "Hcell" as (pl d Heval) "(#Hd & #Hshr & %Hphys)".
    simpl in Hphys.
    inversion Hphys; subst pl.
    iDestruct "Hperm" as (pl' d' Heval') "(#Hd' & Hshr' & %Hphys')".
    simpl in Hphys'.
    inversion Hphys'; subst pl'.
    (* destruct d' => //=. *)
    rewrite /PCellBorrow.
    wp_bind pcell_ref.
    iApply wp_wand.
    iApply wp_eval_path => //.
    iIntros (? ->).
    wp_bind perm_ref.
    iApply wp_wand.
    iApply wp_eval_path => //.
    iIntros (? ->).
    iApply wp_fupd.
    destruct (decide (d ≤ d')) as [Hd | Hd'].
    - iApply (wp_persistent_time_receipt with "TIME Hd'"); [done|].
      destruct d => //.
      iSimpl in "Hshr".
      destruct d' as [ | [ | d']] => //=.
      { iDestruct "Hshr'" as "(_ & _ & Hfalse)".
        rewrite /advance_credits /=.
        iIntros "(£ & _) #Hd''".
        wp_rec.
        by iMod (lc_fupd_elim_later with "£ Hfalse"). }
      iIntros "H£ #Hd''".
      wp_rec.
      iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & _)" => //.
      iDestruct "Hshr'" as "(_ & #Hshr'0 & (H&Hpers))".
      iDestruct (cell_points_to_shr_unfold' ty κ (γs, x) (S d') (S (S d')) tid with "Hshr'0")
        as "[#Hpt #Hshr']".
      iDestruct ("Hshr'" $! d' with "[//]") as "#Hshr''". iSimpl in "Hpt".
      iExists -[(cloc_flat_insert l γs, x)].
      rewrite /tctx_elt_interp/ty_own/=.
      iFrame.
      iSplitL.
      { iCombine "H Hpers" as "H".
        rewrite !Nat.add_1_r -!bi.later_laterN.
        iMod (lc_fupd_add_laterN _ _ _ (S (S d'))  with "[H£] [H]") as "H".
        { iApply (lc_weaken with "H£"). rewrite /advance_credits. nia. }
        { iIntros "!> !>". iExact "H". }
        iDestruct "H" as "[%Hlen #Hgho]".
        rewrite pad_length'.
        2: by rewrite length_fmap.
        iModIntro.
        iSplit => //.
        - iExists _, (S (S (S d'))).
          iSplit => //.
          iFrame "#" => /=.
          iSplit => //.
          iSplitR; last iSplitL.
          + iDestruct "Hshr" as "(H↦shared1 & _ & _)".
            iDestruct (lguards_weaken_later with "H↦shared1") as "H↦shared1'".
            1: instantiate (1 := S (S d') + 2); lia.
            iDestruct (guard_cloc_combine_fancy' with "H↦shared1' Hpt") as "H↦shared3".
            simpl.
            iApply (lguards_weaken_later with "H↦shared3").
            lia.
          + iApply (ty_shr_depth_mono with "Hshr''"); lia.
          + repeat iNext.
            iApply (ty.(ty_gho_pers_depth_mono) with "Hgho") => //; lia.
      }
      iApply (proph_obs_impl with "Obs").
      intros π [? Hpost].
      apply Hpost.
    - iApply (wp_persistent_time_receipt with "TIME Hd"); [done|].
      destruct d => //.
      iSimpl in "Hshr".
      destruct d' as [ | [ | d']] => //=.
      { iDestruct "Hshr'" as "(_ & _ & Hfalse)".
        rewrite /advance_credits /=.
        iIntros "(£ & _) #Hd''".
        wp_rec.
        by iMod (lc_fupd_elim_later with "£ Hfalse"). }
      iIntros "H£ #Hd''".
      wp_rec.
      iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & _)" => //.
      iDestruct "Hshr'" as "(_ & #Hshr'0 & (H&Hpers))".
      iDestruct (cell_points_to_shr_unfold' ty κ (γs, x) (S d') (S (S d')) tid with "Hshr'0")
        as "[#Hpt #Hshr']".
      iDestruct ("Hshr'" $! d' with "[//]") as "#Hshr''". iSimpl in "Hpt".
      iExists -[(cloc_flat_insert l γs, x)].
      rewrite /tctx_elt_interp/ty_own/=.
      iFrame.
      iSplitL.
      { iCombine "H Hpers" as "H".
        rewrite !Nat.add_1_r -!bi.later_laterN.
        iMod (lc_fupd_add_laterN _ _ _ (S (S d'))  with "[H£] [H]") as "H".
        { iApply (lc_weaken with "H£"). rewrite /advance_credits. nia. }
        { iIntros "!> !>". iExact "H". }
        iDestruct "H" as "[%Hlen #Hgho]".
        rewrite pad_length'.
        2: by rewrite length_fmap.
        iModIntro.
        iSplit => //.
        - iExists _, (S (S d)).
          iSplit => //.
          iFrame "#" => /=.
          iSplit => //.
          iSplitR; last iSplitL.
          + iDestruct "Hshr" as "(H↦shared1 & _ & _)".
            iDestruct (lguards_weaken_later with "Hpt") as "H↦shared2'".
            1: instantiate (1 := S (S d)); lia.
            iDestruct (guard_cloc_combine_fancy' with "H↦shared1 H↦shared2'") as "H↦shared3".
            simpl.
            iApply (lguards_weaken_later with "H↦shared3").
            lia.
          + iApply (ty_shr_depth_mono with "Hshr''"); lia.
          + repeat iNext.
            iApply (ty.(ty_gho_pers_depth_mono) with "Hgho") => //; lia.
      }
      iApply (proph_obs_impl with "Obs").
      intros π [? Hpost].
      apply Hpost.
  Qed.

  Definition PCellMutBorrow : val :=
    (λ: ["pcell_ref"; "perm_mut_ref"], "pcell_ref")%V.

  Lemma typed_pcell_borrow_mut {𝔄} κ (pcell_ref perm_mut_ref : path) (ty : type 𝔄) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I +[pcell_ref ◁ shr_bor κ (pcell_ty (ty_size ty)); perm_mut_ref ◁ &uniq{κ} (cell_points_to_ty ty)] (PCellMutBorrow [pcell_ref; perm_mut_ref]) (λ v, +[v ◁ &uniq{κ} ty]) (λ post '-[(cl, γs); bor], λ mask π, let '(cl', (γs', x), ξi, d, g, idx) := bor in γs = γs' ∧ ∀ bor',
    uniq_bor_current bor' = x →
    uniq_bor_future bor' π = snd (uniq_bor_future bor π) →
    (uniq_bor_future bor π).1 = γs →
    (uniq_bor_loc bor') = cloc_flat_insert cl γs →
    post -[bor'] mask π).
  Proof.
    move => Alv tid postπ mask iκs vπl.
    iIntros "#LFT #TIME #PROPH #UNIQ #E L $ TY #Obs" => /=.
    iDestruct (Alv with "L E") as "#Alv".
    destruct vπl as [[cl γs] [u []]].
    destruct u as [[[[[cl' [γs' x]] ξi] d] g] ξidx].
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & _)" => //.
    iDestruct "TY" as "(Hcell & Hperm & _)".
    iDestruct "Hcell" as (pl d' Heval) "(#Hd & Hcell_shr & %Hphys)".
    destruct d' => //.
    simpl in Hphys.
    inversion Hphys; subst pl.
    iDestruct "Hperm" as (pl' d'' Heval') "(#Hd' & Huniq & %Hphys')".
    simpl in Hphys'.
    inversion Hphys'; subst pl'.
    iDestruct "Huniq" as "[#Incl [%Hineq [UniqBody [#PtBase #Pers]]]]".
    iSimpl in "Hcell_shr".
    iDestruct "Hcell_shr" as "[#Hcell_shr #[_ Hlen]]".
    rewrite /PCellMutBorrow.
    wp_bind pcell_ref.
    iApply wp_wand.
    iApply wp_eval_path => //.
    iIntros (? ->).
    wp_bind perm_mut_ref.
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
    destruct d.
    { by wp_rec. }
    iDestruct "UniqBody" as "(ξBor & £saved)".
    destruct cl' as [l' [ | ]] eqn:?.
    2: {
      iMod (uniq_body_acc with "LFT UNIQ Alv [$ξBor $£saved] L") as "[Hown _]"; [solve_ndisj|..].
      wp_rec.
      iDestruct "Hown" as "(_ & _ & Hfalse)".
      iDestruct (heap_cloc_mapsto_fancy_vec_length_eq with "Hfalse") as "%Hfalse".
      by simpl in Hfalse. }
    wp_rec.

    change 2 with (1 + 1).
    iDestruct "⧗" as "(⧗ & ⧗')".
    iDestruct (guards_transitive_right with "Alv Hcell_shr") as "Hcell_shr'".
    iMod (guards_extract_persistent_later with "Hcell_shr' L []") as "Hlen'".
    3: {
      iIntros "H".
      iDestruct (heap_fancy_mapsto_cells_length with "H") as "H".
      rewrite length_pad.
      iExact "H".
    }
    1: apply _.
    1: done.
    destruct (decide (d' ≤ d'')) as [Hd' | Hd''].
    {

    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗ Hd'") as "(Hd'' & £)"; [solve_ndisj|..].
    iDestruct "£" as "[£ [£1' £1]]".


    rewrite !Nat.add_1_r -!bi.later_laterN.
    iMod (lc_fupd_add_laterN  with "[£] Hlen'") as "[L %Hlen']".
    { iApply (lc_weaken with "£"). nia. }

    iMod (llctx_interp_make_guarded with "L") as (γ) "[H1 [H2 [#Ghalf #Halfback]]]". { solve_ndisj. }
    iDestruct (guards_transitive with "Ghalf Alv") as "HguardsK".

    iMod (uniq_body_transform (cell_points_to_ty ty) ty (γs, x) x (S d) g ξi ξidx κ tid cl' (cloc_flat_insert cl γs) _ _ (pair_with_cell_idsₛ (ty_size ty) γs) (λ d g, (S d, g)) with "LFT PROPH UNIQ [⧗' £1'] HguardsK H1 [ξBor £saved]") as (ζi ζidx) "[#Obs2 [UniqBody H1]]". { set_solver. }
    { iIntros "[gho pt]".
      iMod (lc_fupd_elim_later with "£1' gho") as "gho".
      iDestruct "gho" as "[H↦ gho]".
      iModIntro.
      iSplitL "gho".
      iDestruct (ty_gho_own_depth_mono _ _ _ (S d) g with "gho") as "[gho _]". { lia. } { lia. }
      done.
      simpl.
      rewrite -(ty.(ty_size_eq) x tid).
      iDestruct "Pers" as "[%Hlen Hgho_pers]".
      rewrite pad_length'.
      2: by rewrite length_fmap.


      iDestruct (heap_complete_mapsto_fancy_val_vec_eq'' _ cl with "H↦") as "H↦".
      { rewrite ty.(ty_size_eq) in Hlen. by rewrite Hlen' -Hlen. }
      iFrame.
      iIntros (x2 d2 g2) "[gho [pt2 ⧖2]]".
      iMod (cumulative_persistent_time_receipt with "TIME ⧗' ⧖2") as "⧖2'". { solve_ndisj. }
      iModIntro. simpl.
      replace (length (ty_phys ty x tid)) with (length (ty_phys ty x2 tid)).
      2: { repeat rewrite ty_size_eq. done. }
      simpl.
      rewrite heap_complete_mapsto_fancy_val_vec_eq''.
      iFrame. iApply (persistent_time_receipt_mono with "⧖2'"). lia.
      rewrite ty.(ty_size_eq) in Hlen.
      by rewrite Hlen' - Hlen.
    }
    { rewrite /uniq_body. iFrame "£saved". rewrite Heqc.
      iApply (proph_ibor_proper with "ξBor"). intros c0.
      rewrite /uniq_payload /=. by rewrite !heap_complete_mapsto_fancy_empty. }
    iDestruct ("Halfback" with "H1 H2") as "X".
    iMod (fupd_mask_mono with "X") as "L". { set_solver. }
    iModIntro.
    iExists -[((cloc_flat_insert cl γs), x, ζi, (S d), g, ζidx)].
    iFrame "L". iFrame "UniqBody". iFrame "Incl".
    iSplit. 
    - iExists _, _.
      iSplit => //.
      iFrame.
      iSplit => //.
      iSplitR; first (iPureIntro; lia).
      iDestruct "Pers" as "(%Hlen & #Pers')".
      iSplitR.
      rewrite heap_mapsto_cells_to_complete_mapsto_fancy_vec.
      rewrite pad_length'.
      2: by rewrite length_fmap.
      rewrite heap_complete_mapsto_combine.
      iApply (lguards_weaken_later with "Hcell_shr"); first lia.
      by rewrite Hlen Hlen'.
      iRight.  iNext.
      iApply (ty_gho_pers_depth_mono  with "Pers'"); lia.
    - iCombine "Obs Obs2" as "Obs3".
      iApply (proph_obs_impl with "Obs3"). intros π [[_ Ha] Hb].
      apply Ha; intuition.
      + unfold uniq_bor_future. simpl. rewrite Hb. trivial.
      + unfold uniq_bor_future, uniq_bor_loc. simpl. rewrite Hb. trivial.
    }
    {

    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗ Hd") as "(Hd'' & £)"; [solve_ndisj|..].
    iDestruct "£" as "[£ [£1' £1]]".


    rewrite !Nat.add_1_r -!bi.later_laterN.
    iMod (lc_fupd_add_laterN  with "[£] Hlen'") as "[L %Hlen']".
    { iApply (lc_weaken with "£"). nia. }

    iMod (llctx_interp_make_guarded with "L") as (γ) "[H1 [H2 [#Ghalf #Halfback]]]". { solve_ndisj. }
    iDestruct (guards_transitive with "Ghalf Alv") as "HguardsK".

    iMod (uniq_body_transform (cell_points_to_ty ty) ty (γs, x) x (S d) g ξi ξidx κ tid cl' (cloc_flat_insert cl γs) _ _ (pair_with_cell_idsₛ _ γs) (λ d g, (S d, g)) with "LFT PROPH UNIQ [⧗' £1'] HguardsK H1 [ξBor £saved]") as (ζi ζidx) "[#Obs2 [UniqBody H1]]". { set_solver. }
    { iIntros "[gho pt]".
      iMod (lc_fupd_elim_later with "£1' gho") as "gho".
      iDestruct "gho" as "[H↦ gho]".
      iModIntro.
      iSplitL "gho".
      iDestruct (ty_gho_own_depth_mono _ _ _ (S d) g with "gho") as "[gho _]". { lia. } { lia. }
      done.
      simpl.
      rewrite -(ty.(ty_size_eq) x tid).
      iDestruct "Pers" as "[%Hlen Hgho_pers]".
      rewrite pad_length'.
      2: by rewrite length_fmap.


      iDestruct (heap_complete_mapsto_fancy_val_vec_eq'' _ cl with "H↦") as "H↦".
      { rewrite ty.(ty_size_eq) in Hlen. by rewrite Hlen' -Hlen. }
      iFrame.
      iIntros (x2 d2 g2) "[gho [pt2 ⧖2]]".
      iMod (cumulative_persistent_time_receipt with "TIME ⧗' ⧖2") as "⧖2'". { solve_ndisj. }
      iModIntro. simpl.
      replace (length (ty_phys ty x tid)) with (length (ty_phys ty x2 tid)).
      2: { repeat rewrite ty_size_eq. done. }
      simpl.
      rewrite heap_complete_mapsto_fancy_val_vec_eq''.
      iFrame. iApply (persistent_time_receipt_mono with "⧖2'"). lia.
      rewrite ty.(ty_size_eq) in Hlen.
      by rewrite Hlen' - Hlen.
    }
    { rewrite /uniq_body. iFrame "£saved". rewrite Heqc.
      iApply (proph_ibor_proper with "ξBor"). intros c0.
      rewrite /uniq_payload /=. by rewrite !heap_complete_mapsto_fancy_empty. }
    iDestruct ("Halfback" with "H1 H2") as "X".
    iMod (fupd_mask_mono with "X") as "L". { set_solver. }
    iModIntro.
    iExists -[((cloc_flat_insert cl γs), x, ζi, (S d), g, ζidx)].
    iFrame "L". iFrame "UniqBody". iFrame "Incl".
    iSplit.
    - iExists _, _.
      iSplit => //.
      iFrame.
      iSplit => //.
      iSplitR; first (iPureIntro; lia).
      iDestruct "Pers" as "(%Hlen & #Pers')".
      iSplitR.
      rewrite heap_mapsto_cells_to_complete_mapsto_fancy_vec.
      rewrite pad_length'.
      2: by rewrite length_fmap.
      rewrite heap_complete_mapsto_combine.
      iApply (lguards_weaken_later with "Hcell_shr"); first lia.
      by rewrite Hlen Hlen'.
      iRight.  iNext.
      iApply (ty_gho_pers_depth_mono  with "Pers'"); lia.
    - iCombine "Obs Obs2" as "Obs3".
      iApply (proph_obs_impl with "Obs3"). intros π [[_ Ha] Hb].
      apply Ha; intuition.
      + unfold uniq_bor_future. simpl. rewrite Hb. trivial.
      + unfold uniq_bor_future, uniq_bor_loc. simpl. rewrite Hb. trivial.
    }
  Qed.

End typing.

Section atomics.

  Context `{!typeG Σ}.

  Definition AtomicLoad : val :=
    (λ: ["pcell_ref"; "perm_ref"], !ˢᶜ "pcell_ref")%V.

  Lemma typed_pcell_atomic_load κ (pcell_ref perm_ref : path) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I +[pcell_ref ◁ shr_bor κ (pcell_ty 1); perm_ref ◁ shr_bor κ (cell_points_to_ty int)] (AtomicLoad [pcell_ref; perm_ref]) (λ v, +[v ◁ int]) (λ post '-[(cl, γs); (cl', (γs', n))], λ mask π, γs = γs' ∧ post -[n] mask π).
  Proof.
    move => Alv tid postπ mask iκs vπl.
    iIntros "#LFT #TIME #PROPH #UNIQ #E L $ TY #Obs" => /=.
    iDestruct (Alv with "L E") as "#Alv".
    destruct vπl as [[cl γs] [[cl' [γs' n]] []]].
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & _)" => //.
    iDestruct "TY" as "(Hcell & Hperm & _)".
    iDestruct "Hcell" as (pl d' Heval) "(#Hd & Hcell_shr & %Hphys)".
    destruct d' => //.
    simpl in Hphys.
    inversion Hphys; subst pl.
    iDestruct "Hperm" as (pl' d'' Heval') "(#Hd' & Hint & %Hphys')".
    simpl in Hphys'.
    inversion Hphys'; subst pl'.
    iSimpl in "Hint". 
    destruct d'' => //.
    iSimpl in "Hint". 
    iDestruct "Hint" as "(_ & #H↦_shr & _)".
    iSimpl in "Hcell_shr".
    iDestruct "Hcell_shr" as "[#Hcell_shr #[_ Hlen]]".
    rewrite /AtomicLoad.
    wp_bind pcell_ref.
    iApply wp_wand.
    iApply wp_eval_path => //.
    iIntros (? ->).
    wp_bind perm_ref.
    iApply wp_wand.
    iApply wp_eval_path => //.
    iIntros (? ->).
    destruct (decide (d' ≤ d'')) as [ Hd' | Hd'' ].
    - iApply (wp_persistent_time_receipt with "TIME Hd'"); [trivial | ..].
      iIntros "£ #Hd''".
      iApply wp_fupd.
      destruct d'' => //=.
      { wp_rec.
        iDestruct (cell_points_to_shr_unfold' int κ (γs, n) 0 (S 0) tid with "H↦_shr")
          as "[#H↦ _]".
        iDestruct (guards_transitive_right with "Alv H↦") as "H↦'".
        leaf_open_laters "H↦'" with "L" as "Hfalse"; [trivial | .. ].
        { solve_ndisj. }
        iMod (lc_fupd_add_laterN _ _ _ 3 with "[£] [Hfalse]") as "?".
        { iApply (lc_weaken with "£"). rewrite /advance_credits. nia. }
        { iNext. iDestruct "Hfalse" as "[Hfalse _]". iExact "Hfalse". }
        done. }
      wp_rec.
      iDestruct (cell_points_to_shr_unfold' int κ (γs, n) (S d'') (S (S d'')) tid with "H↦_shr")
        as "[#H↦' _]".
      iDestruct (lguards_weaken_later _ _ _ _ (S (S d'') + 2) with "Hcell_shr") as "Hcell_shr'"; first lia.
      destruct γs as [ | γ [ | ]] eqn:Hγs; cycle 2.
      + iMod (lc_fupd_add_laterN _ _ _ (d' + 1) with "[£] [Hlen]") as "Hlen'".
        { iApply (lc_weaken with "£"). rewrite /advance_credits. nia. }
        { iNext. iModIntro. iExact "Hlen". }
        simpl; by iDestruct "Hlen'" as "%Hfalse".
      + iMod (lc_fupd_add_laterN _ _ _ (d' + 1) with "[£] [Hlen]") as "Hlen'".
        { iApply (lc_weaken with "£"). rewrite /advance_credits. nia. }
        { iNext. iModIntro. iExact "Hlen". }
        simpl; by iDestruct "Hlen'" as "%Hfalse".
      + rewrite pad_length'.
        2: by rewrite length_fmap.
        iDestruct (guard_cloc_combine_fancy' with "Hcell_shr' H↦'") as "Hshr".
        (* rewrite /cloc_flat_insert. *)
        (* rewrite Hcl. *)
        simpl.
        destruct cl.2 as [ | γs1 γs'] eqn:Hcl.
        { rewrite -Hcl.
          rewrite heap_mapsto_cells_to_complete_mapsto_fancy_vec.
          iDestruct (guards_weaken_rhs_sep_r with "Hcell_shr") as "Hfalse".
          iDestruct (guards_transitive_right with "Alv Hfalse") as "Hfalse'".
          iMod (guards_extract_persistent_later _ _ False with "Hfalse' L []") as "Hfalse''".
          { solve_ndisj. }
          iIntros "H".
          iDestruct (heap_cloc_mapsto_fancy_vec_length_eq with "H") as "%Hlen".
          by rewrite Hcl in Hlen.
          rewrite !Nat.add_1_r -!bi.later_laterN.
          iMod (lc_fupd_add_laterN _ _ False (S (S d')) with "[£] [Hfalse'']") as "?".
          { iApply (lc_weaken with "£"). rewrite /advance_credits. nia. }
          { iNext. iMod "Hfalse''". iApply fupd_mask_intro. solve_ndisj.
            iDestruct "Hfalse''" as "[? ?]" => //. }
          done. }
        rewrite (heap_mapsto_singleton _ _ (FVal #n)).
        (* rewrite heap_mapsto_cells_fancy_fmap_eq. *)
        iDestruct (guards_transitive_right with "Alv Hshr") as "Hshr'".
        iApply (wp_read_sc_guarded_cells _ _ (γs1 ++ [γ]) (#n) _ (llctx_interp L) with "[L £]").
        { solve_ndisj. }
        {  iSplitR; first iExact "Hshr'". 
           iFrame.
           iApply (lc_weaken with "£"). rewrite /advance_credits. nia. }
        iIntros "!> L".
        iModIntro.
        iExists -[n].
        iFrame.
        iSplit.
        * iSplit => //.
          iExists _, _.
          repeat iSplit => //.
        * iApply (proph_obs_impl with "Obs").
          intros ? (_ & Hpost).
          apply Hpost.
    - iApply (wp_persistent_time_receipt with "TIME Hd"); [trivial | ..].
      iIntros "£ #Hd''".
      iApply wp_fupd.
      destruct d'' => //=.
      { wp_rec.
        iDestruct (cell_points_to_shr_unfold' int κ (γs, n) 0 (S 0) tid with "H↦_shr")
          as "[#H↦ _]".
        iDestruct (guards_transitive_right with "Alv H↦") as "H↦'".
        leaf_open_laters "H↦'" with "L" as "Hfalse"; [trivial | .. ].
        { solve_ndisj. }
        iMod (lc_fupd_add_laterN _ _ _ 3 with "[£] [Hfalse]") as "?".
        { iApply (lc_weaken with "£"). rewrite /advance_credits. nia. }
        { iNext. iDestruct "Hfalse" as "[Hfalse _]". iExact "Hfalse". }
        done. }
      wp_rec.
      iDestruct (cell_points_to_shr_unfold' int κ (γs, n) (S d'') (S (S d'')) tid with "H↦_shr")
        as "[#H↦ _]".
      iDestruct (lguards_weaken_later _ _ _ _ (S (d' + 1)) with "H↦") as "H↦'"; first lia.
      destruct γs as [ | γ [ | ]] eqn:Hγs; cycle 2.
      + iMod (lc_fupd_add_laterN _ _ _ (d' + 1) with "[£] [Hlen]") as "Hlen'".
        { iApply (lc_weaken with "£"). rewrite /advance_credits. nia. }
        { iNext. iModIntro. iExact "Hlen". }
        simpl; by iDestruct "Hlen'" as "%Hfalse".
      + iMod (lc_fupd_add_laterN _ _ _ (d' + 1) with "[£] [Hlen]") as "Hlen'".
        { iApply (lc_weaken with "£"). rewrite /advance_credits. nia. }
        { iNext. iModIntro. iExact "Hlen". }
        simpl; by iDestruct "Hlen'" as "%Hfalse".
      + rewrite pad_length'.
        2: by rewrite length_fmap.
        iDestruct (guard_cloc_combine_fancy' with "Hcell_shr H↦'") as "Hshr".
        rewrite /cloc_flat_insert.
        (* rewrite Hcl. *)
        simpl.
        destruct cl.2 as [ | γs1 γs'] eqn:Hcl.
        { rewrite -Hcl.
          rewrite heap_mapsto_cells_to_complete_mapsto_fancy_vec.
          iDestruct (guards_weaken_rhs_sep_r with "Hcell_shr") as "Hfalse".
          iDestruct (guards_transitive_right with "Alv Hfalse") as "Hfalse'".
          iMod (guards_extract_persistent_later _ _ False with "Hfalse' L []") as "Hfalse''".
          { solve_ndisj. }
          iIntros "H".
          iDestruct (heap_cloc_mapsto_fancy_vec_length_eq with "H") as "%Hlen".
          by rewrite Hcl in Hlen.
          rewrite !Nat.add_1_r -!bi.later_laterN.
          iMod (lc_fupd_add_laterN _ _ False (S (S d')) with "[£] [Hfalse'']") as "?".
          { iApply (lc_weaken with "£"). rewrite /advance_credits. nia. }
          { iNext. iMod "Hfalse''". iApply fupd_mask_intro. solve_ndisj.
            iDestruct "Hfalse''" as "[? ?]" => //. }
          done. }
        rewrite (heap_mapsto_singleton _ _ (FVal #n)).
        (* rewrite heap_mapsto_cells_fancy_fmap_eq. *)
        iDestruct (guards_transitive_right with "Alv Hshr") as "Hshr'".
        iApply (wp_read_sc_guarded_cells _ _ _ (#n) _ (llctx_interp L) with "[L £]").
        { solve_ndisj. }
        { iSplitR; first iExact "Hshr'". iFrame.
          iApply (lc_weaken with "£"). rewrite /advance_credits. nia. }
        iIntros "!> L".
        iModIntro.
        iExists -[n].
        iFrame.
        iSplit.
        * iSplit => //.
          iExists _, _.
          repeat iSplit => //.
        * iApply (proph_obs_impl with "Obs").
          intros ? (_ & Hpost).
          apply Hpost.
  Qed.

  Definition AtomicStore : val :=
    (λ: ["pcell_ref"; "perm_mut_ref"; "new"], "pcell_ref" <-ˢᶜ "new")%V.

  Lemma typed_pcell_atomic_store κ (pcell_ref perm_mut_ref new : path) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I +[pcell_ref ◁ shr_bor κ (pcell_ty 1); perm_mut_ref ◁ &uniq{κ} (cell_points_to_ty int); new ◁ int] (AtomicStore [pcell_ref; perm_mut_ref; new]) (λ v, +[]) (λ post '-[(cl, γs); bor; n'], λ mask π, let '(cl', (γs', n), ξi, d, g, idx) := bor in γs = γs' ∧
    (uniq_bor_future bor π = (γs', n') → post -[] mask π)).
    (* post -[] mask π). *)
  Proof.
    move => Alv tid postπ mask iκs vπl.
    iIntros "#LFT #TIME #PROPH #UNIQ #E L $ TY #Obs" => /=.
    iDestruct (Alv with "L E") as "#Alv".
    destruct vπl as [[cl γs] [u [n []]]].
    destruct u as [[[[[cl' [γs' x]] ξi] di] gi] ξidx].
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & _)" => //.
    iDestruct "TY" as "(Hcell & Hperm & Hn & _)".
    iDestruct "Hcell" as (pl d Heval) "(#Hd & Hcell_shr & %Hphys)".
    destruct d => //.
    simpl in Hphys.
    inversion Hphys; subst pl.
    iDestruct "Hperm" as (pl' d' Heval') "(#Hd' & Huniq & %Hphys')".
    simpl in Hphys'.
    inversion Hphys'; subst pl'.
    iDestruct "Hn" as (pl'' d'' Heval'') "(#Hd'' & _ & %Hphys'')".
    simpl in Hphys''.
    inversion Hphys''; subst pl''.
    iDestruct "Huniq" as "[#Incl [%Hineq [UniqBody [#PtBase #Pers]]]]".
    iSimpl in "Hcell_shr".
    iDestruct "Hcell_shr" as "[#Hcell_shr #[_ Hlen]]".
    rewrite /AtomicStore.
    wp_bind pcell_ref.
    iApply wp_wand.
    iApply wp_eval_path => //.
    iIntros (? ->).
    wp_bind perm_mut_ref.
    iApply wp_wand.
    iApply wp_eval_path => //.
    iIntros (? ->).
    wp_bind new.
    iApply wp_wand.
    iApply wp_eval_path => //.
    iIntros (? ->).
    iApply wp_fupd.
    iApply (wp_cumulative_time_receipt2 with "TIME"); [trivial |]; iIntros "⧗".
    destruct d' as [ | ] => //=; first lia.
    iDestruct "Pers" as "[Dead|Pers]". {
      iDestruct "Dead" as (κ') "[Incl' Dead']".
      iDestruct (guards_transitive with "Alv Incl'") as "G2".
      wp_rec. repeat wp_seq.
      leaf_open "G2" with "L" as "[Alive _]". { solve_ndisj. }
      iExFalso. iApply (llftl_not_own_end with "Alive Dead'").
    }
    destruct di.
    { by wp_rec. }

    iMod (llctx_interp_make_guarded with "L") as (γ) "[H1 [H2 [#Ghalf #Halfback]]]". { solve_ndisj. }
    iDestruct (guards_transitive with "Ghalf Alv") as "HguardsK".
    iMod (uniq_body_acc with "LFT UNIQ HguardsK UniqBody H1") as "(Bor & £saved & Hclose)".
    1: solve_ndisj.
    wp_rec.
    iDestruct "Pers" as "[%Hlen Hgho_pers]".
    iDestruct "Bor" as "(#H⧖ & H↦ & Hcl')".
    destruct cl' as [l' [ | ]] eqn:?.
    2: {
      iDestruct (heap_cloc_mapsto_fancy_vec_length_eq with "Hcl'") as "%Hfalse".
      by simpl in Hfalse. }
    iSimpl in "H↦".
    iDestruct "H↦" as "[H↦ _]".
    rewrite heap_mapsto_cells_to_complete_mapsto_fancy_vec.
    iDestruct (guards_transitive_right with "HguardsK Hcell_shr") as "Hcell_shr'".
    destruct cl.2 as [ | cell_ids1 [ | ]] eqn:Hcl2; cycle 2.
    { iMod (guards_open_later with "Hcell_shr' H2") as "Hfalse".
      1: solve_ndisj. 
      iMod (cumulative_persistent_time_receipt_get_credits with "TIME £saved Hd") as "(Hd2 & £)"; [solve_ndisj|..].
      rewrite !Nat.add_1_r -!bi.later_laterN.
      iMod (lc_fupd_add_laterN _ _ False (S (S d)) with "[£] [Hfalse]") as "?".
      { iApply (lc_weaken with "£"). rewrite /advance_credits. nia. }
      iNext.
      iMod "Hfalse" as "[[_ Hfalse] _]".
      iDestruct (heap_cloc_mapsto_fancy_vec_length_eq with "Hfalse") as "%Hlen'".
      rewrite length_pad in Hlen'.
      rewrite Hcl2 in Hlen'.
      by simpl in Hlen'.
      done. }
    { iMod (guards_open_later with "Hcell_shr' H2") as "Hfalse".
      1: solve_ndisj. 
      iMod (cumulative_persistent_time_receipt_get_credits with "TIME £saved Hd") as "(Hd2 & £)"; [solve_ndisj|..].
      rewrite !Nat.add_1_r -!bi.later_laterN.
      iMod (lc_fupd_add_laterN _ _ False (S (S d)) with "[£] [Hfalse]") as "?".
      { iApply (lc_weaken with "£"). rewrite /advance_credits. nia. }
      iNext.
      iMod "Hfalse" as "[[_ Hfalse] _]".
      iDestruct (heap_cloc_mapsto_fancy_vec_length_eq with "Hfalse") as "%Hlen'".
      rewrite length_pad in Hlen'.
      rewrite Hcl2 in Hlen'.
      by simpl in Hlen'.
      done. }
    rewrite pad_length'.
    2: by rewrite length_fmap.
    rewrite heap_complete_mapsto_combine.
    rewrite /cloc_flat_insert/=.
    rewrite Hcl2 /=.
    destruct γs as [ | γ1 [ | ]] eqn:Hγs; cycle 2; [by simpl in Hlen.. |].
    subst γs.
    rewrite heap_complete_mapsto_singleton.
    replace ([FVal #x]) with (fmap FVal [LitV $ LitInt $ x]) by done.
    (* broken *)
    iDestruct (cumulative_time_receipt_mono 1 with "⧗") as "⧗"; first lia.
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗ Hd") as "(Hd2 & £)"; [solve_ndisj|..].
    iApply (wp_write_sc_guarded  with "[H2 H↦ £]").
    { solve_ndisj. }
    { replace (S (d + 1)) with (d + 1 + 1) by lia. 
      iFrame "Hcell_shr'".
      rewrite -(Nat.add_1_r d).
      iFrame. 
      (* iFrame "Hd". *)
      rewrite -heap_complete_mapsto_val_singleton.
      rewrite (heap_complete_mapsto_fancy_val_vec_eq'' _ cl).
      rewrite /cloc_flat_insert Hcl2 /=.
      replace [FVal #x] with (FVal <$> [LitV $ LitInt $ x]) by done.
      rewrite heap_complete_mapsto_fancy_fmap_eq.
      iFrame "H↦".
      iApply (lc_weaken with "£").
      rewrite /advance_credits; nia.
      rewrite Hcl2 //=.
    }
    iNext.
    iIntros "[H↦ H2]".

    iMod (fupd_mask_subseteq (↑Nllft)) as "Hback"; [trivial | ..].
    iMod ("Hclose" $! ([γ1], n) (S di) gi with "[H↦] £saved") as "[UB H1]".
    { iNext.
      iFrame "H⧖".
      iSplitL "H↦"; last by rewrite heap_complete_mapsto_fancy_empty.
      rewrite /by_succ. iSplitL; last done.
      rewrite (heap_complete_mapsto_fancy_val_vec_eq'' _ cl).
      rewrite /cloc_flat_insert Hcl2 /=.
      replace [FVal #n] with (FVal <$> [LitV $ LitInt $ n]) by done.
      rewrite heap_complete_mapsto_fancy_fmap_eq.
      rewrite heap_complete_mapsto_val_singleton.
      done.
      rewrite Hcl2 //=.
    }
    iMod "Hback" as "_".
    iMod (fupd_mask_subseteq (↑NllftG)) as "Hback"; [trivial | ..].
    iMod ("Halfback" with "H1 H2") as "L".
    iMod "Hback" as "_".

    iMod (resolve_uniq_body (cell_points_to_ty int) ([γ1], n) with "LFT PROPH UNIQ TIME [Incl] E [] L UB") as "[#Hrslv [L #HBor]]"=> //.
    { iApply guards_refl. }
    
    iModIntro.
    iExists -[].
    iFrame "L".
    iSplit => //.
    iDestruct (proph_obs_and with "Hrslv Obs") as "Obs2".
    iApply (proph_obs_impl with "Obs2").
    intros π .
    intros (Hresolve & _ & Hpost).
    apply Hpost.
    rewrite /uniq_bor_future.
    simpl.

    etrans; [apply (uniq_prvar_app_irrel (𝔄:=trackedₛ (pcellₛ _ * Zₛ)) ([γ1], x) ([γ1], n) ξi π)|].
    by rewrite Hresolve.
    rewrite Hcl2 //=.
  Qed.

  Definition AtomicCAS : val :=
    (λ: ["pcell_ref"; "perm_mut_ref"; "n1"; "n2"], CAS "pcell_ref" "n1" "n2")%V.

  Lemma typed_pcell_atomic_CAS κ (pcell_ref perm_mut_ref p1 p2 : path) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I +[pcell_ref ◁ shr_bor κ (pcell_ty 1); perm_mut_ref ◁ &uniq{κ} (cell_points_to_ty int); p1 ◁ int; p2 ◁ int] (AtomicCAS [pcell_ref; perm_mut_ref; p1; p2]) (λ v, +[v ◁ int]) (λ post '-[(cl, γs); bor; n1; n2], λ mask π, let '(cl', (γs', n), ξi, d, g, idx) := bor in γs = γs' ∧
    (if (decide (n = n1)) then uniq_bor_future bor π = (γs', n2) → post -[1%Z] mask π else uniq_bor_future bor π = (γs', n) → post -[0%Z] mask π)).
    (* post -[] mask π). *)
  Proof.
    move => Alv tid postπ mask iκs vπl.
    iIntros "#LFT #TIME #PROPH #UNIQ #E L $ TY #Obs" => /=.
    iDestruct (Alv with "L E") as "#Alv".
    destruct vπl as [[cl γs] [u [n1 [n2 []]]]].
    destruct u as [[[[[cl' [γs' x]] ξi] di] gi] ξidx].
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & _)" => //.
    iDestruct "TY" as "(Hcell & Hperm & Hn1 & Hn2 & _)".
    iDestruct "Hcell" as (pl d Heval) "(#Hd & Hcell_shr & %Hphys)".
    destruct d => //.
    iDestruct "Hn1" as (v dn1 Hpath1) "(#Hdn1 & _ & %Hphys')".
    simpl in Hphys, Hphys'.
    move: Hphys'; case => ?; subst v.
    iDestruct "Hn2" as (v dn2 Hpath2) "(#Hdn2 & _ & %Hphys')".
    simpl in Hphys, Hphys'.
    move: Hphys'; case => ?; subst v.
    inversion Hphys; subst pl.
    iDestruct "Hperm" as (pl' d' Heval') "(#Hd' & Huniq & %Hphys')".
    simpl in Hphys'.
    inversion Hphys'; subst pl'.
    iDestruct "Huniq" as "[#Incl [%Hineq [UniqBody [#PtBase #Pers]]]]".
    iSimpl in "Hcell_shr".
    iDestruct "Hcell_shr" as "[#Hcell_shr #[_ Hlen]]".
    rewrite /AtomicCAS.
    wp_bind pcell_ref.
    iApply wp_wand.
    iApply wp_eval_path => //.
    iIntros (? ->).
    wp_bind perm_mut_ref.
    iApply wp_wand.
    iApply wp_eval_path => //.
    iIntros (? ->).
    wp_bind p1.
    iApply wp_wand.
    iApply wp_eval_path => //.
    iIntros (? ->).
    wp_bind p2.
    iApply wp_wand.
    iApply wp_eval_path => //.
    iIntros (? ->).
    iApply wp_fupd.
    iApply (wp_cumulative_time_receipt2 with "TIME"); [trivial |]; iIntros "⧗".
    destruct d' as [ | ] => //=; first lia.
    iDestruct "Pers" as "[Dead|Pers]". {
      iDestruct "Dead" as (κ') "[Incl' Dead']".
      iDestruct (guards_transitive with "Alv Incl'") as "G2".
      wp_rec. repeat wp_seq.
      leaf_open "G2" with "L" as "[Alive _]". { solve_ndisj. }
      iExFalso. iApply (llftl_not_own_end with "Alive Dead'").
    }
    destruct di.
    { by wp_rec. }

    iMod (llctx_interp_make_guarded with "L") as (γ) "[H1 [H2 [#Ghalf #Halfback]]]". { solve_ndisj. }
    iDestruct (guards_transitive with "Ghalf Alv") as "HguardsK".
    iMod (uniq_body_acc with "LFT UNIQ HguardsK UniqBody H1") as "(Bor & £saved & Hclose)".
    1: solve_ndisj.
    wp_rec.
    iDestruct "Pers" as "[%Hlen Hgho_pers]".
    iDestruct "Bor" as "(#H⧖ & H↦ & Hcl')".
    destruct cl' as [l' [ | ]] eqn:?.
    2: {
      iDestruct (heap_cloc_mapsto_fancy_vec_length_eq with "Hcl'") as "%Hfalse".
      by simpl in Hfalse. }
    iSimpl in "H↦".
    iDestruct "H↦" as "[H↦ _]".
    rewrite heap_mapsto_cells_to_complete_mapsto_fancy_vec.
    iDestruct (guards_transitive_right with "HguardsK Hcell_shr") as "Hcell_shr'".
    destruct cl.2 as [ | cell_ids1 [ | ]] eqn:Hcl2; cycle 2.
    { iMod (guards_open_later with "Hcell_shr' H2") as "Hfalse".
      1: solve_ndisj. 
      iMod (cumulative_persistent_time_receipt_get_credits with "TIME £saved Hd") as "(Hd2 & £)"; [solve_ndisj|..].
      rewrite !Nat.add_1_r -!bi.later_laterN.
      iMod (lc_fupd_add_laterN _ _ False (S (S d)) with "[£] [Hfalse]") as "?".
      { iApply (lc_weaken with "£"). rewrite /advance_credits. nia. }
      iNext.
      iMod "Hfalse" as "[[_ Hfalse] _]".
      iDestruct (heap_cloc_mapsto_fancy_vec_length_eq with "Hfalse") as "%Hlen'".
      rewrite length_pad in Hlen'.
      rewrite Hcl2 in Hlen'.
      by simpl in Hlen'.
      done. }
    { iMod (guards_open_later with "Hcell_shr' H2") as "Hfalse".
      1: solve_ndisj. 
      iMod (cumulative_persistent_time_receipt_get_credits with "TIME £saved Hd") as "(Hd2 & £)"; [solve_ndisj|..].
      rewrite !Nat.add_1_r -!bi.later_laterN.
      iMod (lc_fupd_add_laterN _ _ False (S (S d)) with "[£] [Hfalse]") as "?".
      { iApply (lc_weaken with "£"). rewrite /advance_credits. nia. }
      iNext.
      iMod "Hfalse" as "[[_ Hfalse] _]".
      iDestruct (heap_cloc_mapsto_fancy_vec_length_eq with "Hfalse") as "%Hlen'".
      rewrite length_pad in Hlen'.
      rewrite Hcl2 in Hlen'.
      by simpl in Hlen'.
      done. }
    rewrite pad_length'.
    2: by rewrite length_fmap.
    rewrite heap_complete_mapsto_combine.
    rewrite /cloc_flat_insert/=.
    rewrite Hcl2 /=.
    destruct γs as [ | γ1 [ | ]] eqn:Hγs; cycle 2; [by simpl in Hlen.. |].
    subst γs.
    rewrite heap_complete_mapsto_singleton.
    replace ([FVal #x]) with (fmap FVal [LitV $ LitInt $ x]) by done.
    2: { rewrite Hcl2 Hlen //=. }
    destruct (decide (n1 = x)) as [ SUC | FAIL].
    - iDestruct (cumulative_time_receipt_mono 1 with "⧗") as "⧗"; first lia.
      iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗ Hd") as "(H⧖' & £)"; [solve_ndisj|..].
      iApply (wp_cas_int_suc_guarded with "[H2 H↦ £]").
      { solve_ndisj. }
      { replace (S (d + 1))%nat with (d + 1 + 1)%nat by lia. 
        iFrame "Hcell_shr'".
        rewrite -(Nat.add_1_r d).
        iFrame.
        rewrite -heap_complete_mapsto_val_singleton.
        rewrite (heap_complete_mapsto_fancy_val_vec_eq'' _ cl).
        rewrite /cloc_flat_insert Hcl2 /=.
        replace [FVal #x] with (FVal <$> [LitV $ LitInt $ x]) by done.
        subst.
        rewrite heap_complete_mapsto_fancy_fmap_eq.
        iFrame.
        iApply (lc_weaken with "£").
        { rewrite /advance_credits. nia. }
        rewrite Hcl2 //=. }
      iNext.
      iIntros "[H2 H↦]".

      iMod (fupd_mask_subseteq (↑Nllft)) as "Hback"; [trivial | ..].
      iMod ("Hclose" $! ([γ1], n2) (S di) gi with "[H↦] £saved") as "[UB H1]".
      { iNext.
        iFrame "H⧖".
        iSplitL "H↦"; last by rewrite heap_complete_mapsto_fancy_empty.
      rewrite /by_succ. iSplitL; last done.
        rewrite (heap_complete_mapsto_fancy_val_vec_eq'' _ cl).
        rewrite /cloc_flat_insert Hcl2 /=.
        replace [FVal #n2] with (FVal <$> [LitV $ LitInt $ n2]) by done.
        rewrite heap_complete_mapsto_fancy_fmap_eq.
        rewrite heap_complete_mapsto_val_singleton.
        done.
        rewrite Hcl2 //=.
      }
      iMod "Hback" as "_".
      iMod (fupd_mask_subseteq (↑NllftG)) as "Hback"; [trivial | ..].
      iMod ("Halfback" with "H1 H2") as "L".
      iMod "Hback" as "_".

      iMod (resolve_uniq_body (cell_points_to_ty int) ([γ1], n2) with "LFT PROPH UNIQ TIME [Incl] E [] L UB") as "[#Hrslv [L #HBor]]"=> //.
      { iApply guards_refl. }
      
      iModIntro.
      iExists -[1%Z].
      iFrame "L".
      iSplit => //.

      + iSplit => //.
        iExists _,_.
        iFrame "#" => //.
      + iDestruct (proph_obs_and with "Hrslv Obs") as "Obs2".
        iApply (proph_obs_impl with "Obs2").
        intros π .
        intros (Hresolve & _ & Hpost).
        case_decide => //.
        apply Hpost.
        rewrite /uniq_bor_future.
        simpl.
        etrans; [apply (uniq_prvar_app_irrel (𝔄:=trackedₛ (pcellₛ _ * Zₛ)) ([γ1], x) ([γ1], n2) ξi π)|].
        by rewrite Hresolve.

    - iDestruct (cumulative_time_receipt_mono 1 with "⧗") as "⧗"; first lia.
      iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗ Hd") as "(H⧖' & £)"; [solve_ndisj|..].
      iApply (wp_cas_int_fail_guarded with "[H2 H↦ £]").
      { solve_ndisj. }
      1: exact FAIL.
      { replace (S (d + 1))%nat with (d + 1 + 1)%nat by lia. 
        iFrame "Hcell_shr'".
        rewrite -(Nat.add_1_r d).
        iFrame. 
        rewrite -heap_complete_mapsto_val_singleton.
        rewrite (heap_complete_mapsto_fancy_val_vec_eq'' _ cl).
        rewrite /cloc_flat_insert Hcl2 /=.
        replace [FVal #x] with (FVal <$> [LitV $ LitInt $ x]) by done.
        subst.
        rewrite heap_complete_mapsto_fancy_fmap_eq.
        iFrame.
        iApply (lc_weaken with "£").
        { rewrite /advance_credits. nia. }
        rewrite Hcl2 //=. }
      iNext.
      iIntros "[H2 H↦]".

      (* iMod (uniq_update (PrVar ((listₛ positiveₛ * Zₛ)%ST ↾ @prval_to_inh (listₛ positiveₛ * Zₛ) (λ _ : proph_asn, ([γ1], x))) ξi) ([γ1], n2) (λ _ : proph_asn, ([γ1], n2)) (S di, gi) with "UNIQ ξVo Pc") as "[ξVo Pc]". { set_solver. } *)

      iMod (fupd_mask_subseteq (↑Nllft)) as "Hback"; [trivial | ..].
      iMod ("Hclose" $! ([γ1], x) (S di) gi with "[H↦] £saved") as "[UB H1]".
      { iNext.
        iFrame "H⧖".
        iSplitL "H↦"; last by rewrite heap_complete_mapsto_fancy_empty.
      rewrite /by_succ. iSplitL; last done.
        rewrite (heap_complete_mapsto_fancy_val_vec_eq'' _ cl).
        rewrite /cloc_flat_insert Hcl2 /=.
        replace [FVal #x] with (FVal <$> [LitV $ LitInt $ x]) by done.
        rewrite heap_complete_mapsto_fancy_fmap_eq.
        rewrite heap_complete_mapsto_val_singleton.
        done.
        rewrite Hcl2 //=.
      }
      iMod "Hback" as "_".
      iMod (fupd_mask_subseteq (↑NllftG)) as "Hback"; [trivial | ..].
      iMod ("Halfback" with "H1 H2") as "L".
      iMod "Hback" as "_".

      iMod (resolve_uniq_body (cell_points_to_ty int) ([γ1], x) with "LFT PROPH UNIQ TIME [Incl] E [] L UB") as "[#Hrslv [L #HBor]]"=> //.
      { iApply guards_refl. }
      
      iModIntro.
      iExists -[0%Z].
      iFrame "L".
      iSplit => //.

      + iSplit => //.
        iExists _,_.
        iFrame "#" => //.
      + iDestruct (proph_obs_and with "Hrslv Obs") as "Obs2".
        iApply (proph_obs_impl with "Obs2").
        intros π .
        intros (Hresolve & _ & Hpost).
        case_decide => //.
        apply Hpost.
        rewrite /uniq_bor_future.
        simpl.
        etrans; [apply (uniq_prvar_app_irrel (𝔄:=trackedₛ (pcellₛ _ * Zₛ)) ([γ1], x) ([γ1], x) ξi π)|].
        by rewrite Hresolve.
  Qed.

End atomics.
