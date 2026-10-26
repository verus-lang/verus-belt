From lrust.typing Require Export uniq_bor shr_bor own uniq_util.
From lrust.typing Require Import lft_contexts type_context programs programs_util.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

(** The rules for borrowing and derferencing borrowed non-Copy pointers are in
  a separate file so make sure that own.v and uniq_bor.v can be compiled
  concurrently. *)

Section borrow.
  Context `{!typeG Σ}.
  
  Lemma type_uniqbor_instr {𝔄} E L I p n (ty: type 𝔄) κ :
    lctx_lft_alive E L κ →
    elctx_sat E L (ty_outlives_E ty κ) →
    typed_instr E L I
        +[p ◁ own_ptr n ty]
        UniqBor
        (const +[p ◁ &uniq{κ} ty; p ◁{κ} blocked_type_ctor _ (own_ptr n ty)])
      (λ post '-[a], λ mask π, ∀ (m: ~~(uniq_borₛ 𝔄)) (b: ~~(blockedₛ (at_locₛ 𝔄))),
        of_cloc (uniq_bor_loc m) = a.1 →
        uniq_bor_current m = a.2 →
        (blockedπ b π).2 = (vπ m π).2 →
        (blockedπ b π).1 = a.1 →
        post -[m; b] mask π).
  Proof.
    intros Alv Out.
    apply typed_instr_of_skip.
    iIntros (x v d tid post mask iκs) "#LFT #TIME #PROPH #UNIQ E L $ #P own #Obs #⧖ ⧗ ⧗' £".
    destruct x as [l x].
    iDestruct (Out with "L E") as "#Out".
    iDestruct (elctx_interp_ty_outlives_E with "Out") as "#?".
    iDestruct "own" as "[gho %phys]". 
    destruct d as [|d']. { done. }
    iDestruct "gho" as "(pt & freeable & gho)".
    iDestruct (ty_gho_pers_impl _ ty with "gho") as "#Pers".
    iDestruct (lc_weaken 1 with "£") as "£"; [rewrite /advance_credits; lia|].
    iMod (alloc_uniq_body _ _ d' (S d') κ _ (l, repeat [] (length (ty_phys ty x tid))) with "LFT PROPH UNIQ [⧖] gho [pt] ⧗") as (ξi ζi idx) "[UniqBody [#Obsξζ Back]]".
      { set_solver. }
      { iApply (persistent_time_receipt_mono with "⧖"). lia. }
      { rewrite <- heap_cloc_mapsto_fancy_empty. iFrame "pt". }
    set ξ := uniq_prvar x ξi.
    set ζ := PrVar (at_locₛ 𝔄 ↾ prval_to_inh (@vπ (at_locₛ 𝔄) (l, x))) ζi.
    iModIntro.
    iExists -[
      ((l, repeat [] (length (ty_phys ty x tid))), x, ξi, d', S d', idx);
      ((l, x), ζi, ζi)
    ].
    iFrame "L".
    unfold tctx_interp, tctx_elt_interp.
    iSplit. {
      iSplitL "UniqBody". {
        iExists v, (S (S d')). iFrame "#". iFrame.
        iSplit; last by done. iSplit; first by iPureIntro; lia.
        rewrite <- heap_cloc_mapsto_empty. iApply guards_true.
      }
      unfold blocked_type_elim. iSplit; [|done].
      iExists v. iFrame "#". iIntros "#†κ".
      iDestruct ("Back" with "†κ") as "Back". iMod (fupd_mask_mono with "Back") as "Back". { set_solver. }
      (* The later credit pays for the later in front of what the lender gets back. The
         pending ownership is the settling of what the lender gets back (unblocking it
         and composing the equalizer of its controller), for the lifetime of the type,
         settled by the unblocking rule with its guard. *)
      iMod (lc_fupd_elim_later with "£ Back") as "Lender".
      iModIntro. iFrame "⧗'".
      iDestruct (uniq_lender_settle with "LFT PROPH †κ Lender") as "Settle".
      rewrite /tctx_pending.
      iApply (guarded_upd_mask_mono lazyE); [set_solver|].
      iApply (guarded_upd_mono with "[freeable] Settle").
      iIntros "(%x'' & %d'' & %g'' & Eqz & ⧖'' & gho & pt) !>".
      iExists (l, x''). iSplitL "Eqz".
      { iNext.
        iApply proph_eqz_modify.
         2: { iApply (proph_eqz_constr (λ t, (l, t)) with "Eqz"). }
        iApply (proph_obs_impl with "Obsξζ"). intros π Ha.
        simpl. simpl in Ha. by rewrite Ha. }
      iExists (S d'' `max` g'').
      destruct (S d'' `max` g'') as [|d1] eqn:Hd1; first by lia.
      iFrame. rewrite /ty_own /=.
      rewrite heap_cloc_mapsto_fancy_empty. repeat rewrite ty_size_eq. iFrame.
      iSplitL. { iDestruct (ty_gho_own_depth_mono with "gho") as "[gho _]"; last by iFrame "gho". { lia. } { lia. } }
      done.
    }
    iCombine "Obs Obsξζ" as "Obs1".
    iApply (proph_obs_impl with "Obs1"). intros π [Hm Hk]. apply Hm; trivial.
     - simpl. rewrite Hk. trivial.
     - simpl. rewrite Hk. trivial.
  Qed.

  (* VerusBelt: we needed to make UniqBor an instruction so we can generate credits. This
     was the old lemma: *)
  (*Lemma tctx_borrow {𝔄} E L p n (ty: type 𝔄) κ:
    elctx_sat E L (ty_outlives_E ty κ) →
    tctx_incl E L +[p ◁ own_ptr n ty] +[p ◁ &uniq{κ} ty; p ◁{κ} blocked_type_ctor _ (own_ptr n ty)]
      (λ post '-[a], λ π, ∀ (m: ~~(uniq_borₛ 𝔄)) (b: ~~(blockedₛ 𝔄)),
        uniq_ref_loc m = a.1 →
        uniq_ref_current m = a.2 →
        vπ b π = (vπ m π).2 →
        post -[m; b] π).
  *)

  (*Lemma tctx_extract_hasty_borrow {𝔄 𝔅 ℭl} E L p n
      (ty : type 𝔄) (ty' : type 𝔅) κ (T : tctx ℭl) f:
    subtype E L ty' ty f →
    elctx_sat E L (ty_outlives_E ty κ) →
    tctx_extract_elt E L (p ◁ &uniq{κ}ty) (p ◁ own_ptr n ty' +:: T)
      (p ◁{κ} blocked_type_ctor _ (own_ptr n ty) +:: T)
      (λ post '(b -:: bs), ∀b': 𝔄, post ((f b, b') -:: b' -:: bs)).
  Proof.
    intros. eapply tctx_incl_impl.
    - eapply tctx_incl_trans; [by eapply subtype_tctx_incl, own_subtype|].
      eapply (tctx_incl_frame_r +[_] +[_; _]). by eapply tctx_borrow.
    - done.
    - intros ??? [??]. by apply forall_proper.
  Qed.*)

  Lemma type_share_instr {𝔄} p κ (ty : type 𝔄) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I +[p ◁ &uniq{κ}ty] Share (const +[p ◁ &shr{κ} ty])
      (λ post '-[m], λ mask π, (vπ m π).1 = (vπ m π).2 -> post -[(uniq_bor_loc m, uniq_bor_current m)] mask π).
  Proof.
    intros Alv.
    apply typed_instr_of_skip.
    intros x v d tid post mask iκs. iIntros "#LFT #TIME #PROPH #UNIQ #E L $ #P Own #Obs ⧖ ⧗ ⧗' £".
    iDestruct (Alv with "L E") as "#Alv".
    iMod (llctx_interp_make_guarded with "L") as (γ) "[H1 [H2 [#Ghalf #Halfback]]]". { solve_ndisj. }
    destruct x as [[[[[l x0] ξi] d'] g'] idx].
    iDestruct "Own" as "[[#Incl [%Ineqs [UniqBody #PtBase]]] #Phys]".
    
    iDestruct (persistent_time_receipt_mono (S d' `max` g') with "⧖") as "#⧖'"; [lia|].
    iMod (resolve_uniq_body ty x0 ξi d' g' idx κ tid l with "LFT PROPH UNIQ TIME Incl E Ghalf H1 ⧖' UniqBody") as "(#Obs2 & H1 & #Shr & #PtGuard & #Pers)". { trivial. } { set_solver. }
    iDestruct ("Halfback" with "H1 H2") as "Halfback'". iMod (fupd_mask_mono with "Halfback'") as "L". { set_solver. }
    iModIntro. iExists -[(l, x0)]. iFrame.
    iSplit. {
      iExists v. iSplit. { done. } iSplit; last by done.
      iSplit. {
        iApply guard_cloc_combine_fancy.
         - leaf_goal laters to (d + 1); first by lia. iFrame "PtBase".
         - leaf_goal laters to 1. { lia. } iFrame "PtGuard".
      }
      iSplit. { iApply (ty_shr_depth_mono with "Shr"); lia. }
      iNext. iApply (ty_gho_pers_depth_mono _ _ _ d (S d)); last by iFrame "Pers".
      { lia. } { lia. }
    }
    iCombine "Obs Obs2" as "Obs3".
    iApply proph_obs_impl; [|done]=>/= π.
    intros [Himpl1 Heq]. apply Himpl1. symmetry. apply Heq.
  Qed.

  Lemma type_share {𝔄 𝔅l ℭl 𝔇} p κ (ty: type 𝔄) (T: tctx 𝔅l) (T' : tctx ℭl)
    trx tr e E L I (C: cctx 𝔇) :
    Closed [] e → tctx_extract_ctx E L +[p ◁ &uniq{κ} ty] T T' trx →
    lctx_lft_alive E L κ →
    typed_body E L I C (p ◁ &shr{κ} ty +:: T') e tr -∗
    typed_body E L I C T (Share;; e) (trx ∘
      (λ post '(m -:: bl), λ mask π, (vπ m π).1 = (vπ m π).2 -> tr post ((uniq_bor_loc m, uniq_bor_current m) -:: bl) mask π)
      )%type.
  Proof.
    iIntros (? Extr ?) "?".
    iApply type_seq; [by eapply type_share_instr|solve_typing| |done].
    destruct Extr as [Htrx _]=>??. apply Htrx. by case.
  Qed.
  
  Lemma tctx_reborrow_uniq {𝔄} E L I p (ty: type 𝔄) κ κ' :
    lctx_lft_incl E L κ' κ →
    typed_instr E L I
        +[p ◁ &uniq{κ} ty]
        ReBor
        (const +[p ◁ &uniq{κ'} ty; p ◁{κ'} blocked_type_ctor _ (&uniq{κ} ty)])
        (λ post '-[bor], λ mask π, ∀ (re_bor: ~~ (uniq_borₛ 𝔄)) (b: ~~(blockedₛ (uniq_borₛ 𝔄))),
            uniq_bor_loc re_bor = uniq_bor_loc bor →
            uniq_bor_current re_bor = uniq_bor_current bor →
            (blockedπ b π) = (uniq_bor_future re_bor π, uniq_bor_future bor π) →
            post -[re_bor; b] mask π).
  Proof.
    intros LftIncl.
    apply typed_instr_of_skip.
    iIntros (x v d tid post mask iκs) "#LFT #TIME #PROPH #UNIQ E L $ #P own Obs #⧖ ⧗ ⧗' £".
    iDestruct (LftIncl with "L E") as "#κ'⊑κ".
    iDestruct "own" as "[gho %phys]". 
    destruct x as [[[[[l x0] ξi] d'] g'] idx].
    iDestruct "gho" as "(#Incl2 & %Hineq & UniqBody & #PtBase)".
    iDestruct (guards_transitive with "κ'⊑κ Incl2") as "Inclκ'".
    iMod (uniq_body_reborrow ty x0 ξi d' g' idx κ κ' tid l with
      "LFT PROPH UNIQ κ'⊑κ ⧗ UniqBody") as (ζi ζidx) "[UniqBody' Inh]".
    { solve_ndisj. }
    iDestruct (lc_weaken (1 + 1) with "£") as "£"; [rewrite /advance_credits; nia|].
    iModIntro. iExists -[(l, x0, ζi, d', g', ζidx);
        ((l, x0, ζi, d', g', idx), ζi, ξi)
    ].
    iFrame "L".
    unfold tctx_interp, tctx_elt_interp.
    iSplit. {
      iSplitL "UniqBody'". {
        iExists v, (S d). iFrame "P". iFrame "⧖". unfold ty_own.
        iSplit. {
          iSplit. { iFrame "Inclκ'". }
          iSplit. { iPureIntro. lia. }
          iFrame "UniqBody'".
          leaf_goal laters to (d + 1); first by lia.
          iApply (guards_transitive_right with "κ'⊑κ PtBase").
        } {
          iPureIntro. apply phys.
        }
      } {
        iSplit; last by done. iExists v. iFrame "P". iIntros "#†κ'".
        iMod (fupd_mask_subseteq (↑Nllft)) as "Upd"; first set_solver.
        iMod ("Inh" with "†κ'") as "Rst".
        iMod "Upd" as "_".
        iModIntro. iFrame "⧗'".
        (* The restored borrow is pending: it is settled (unblocked and closed at the
           trivial state) with a guard for [κ] (from the guard for the lifetime of
           [&uniq{κ} ty]); its value is then known. *)
        rewrite /tctx_pending /guarded_upd. iIntros (G ?) "#Gty G".
        iAssert (G &&{↑NllftG}&&> @[κ])%I as "#Gκ".
        { iApply (guards_transitive with "Gty"). iApply llftl_intersect_incl_l. }
        iDestruct "£" as "[£ £']".
        iMod (uniq_restored_settle with "LFT PROPH UNIQ Gκ Incl2 †κ' £ £' Rst G")
          as (x'' d'' g'' idx'') "(#⧖'' & UB & Eqz & $)"; [rewrite /lazyE; solve_ndisj|].
        iModIntro. iExists (l, x'', ξi, d'', g'', idx'').
        iSplitL "Eqz". {
          iNext.
          iApply (proph_eqz_prod with "[Eqz]").
            - iFrame "Eqz".
            - iApply (proph_eqz_eq with "[]"); [done| |iApply proph_eqz_refl].
              fun_ext=> π /=. apply (uniq_prvar_app_irrel x0 x'' ξi π).
        }
        iExists (d `max` S d'' `max` g'').
        iCombine "⧖'' ⧖" as "⧖max".
        iSplit. { iApply (persistent_time_receipt_mono with "⧖max"). lia. }
        iSplit; last by done. iSplit. { iFrame "Incl2". }
        iSplit. { iPureIntro. nia. }
        iFrame "UB".
        leaf_goal laters to (d + 1); first by lia. iFrame "PtBase".
      }
    }
        
    iApply (proph_obs_impl with "Obs") => /= π.
    intros Ha. apply Ha; done.
  Qed.
    

(* also can't use this one, we need to take a step
  Lemma tctx_reborrow_uniq {𝔄} E L p (ty: type 𝔄) κ κ' :
    lctx_lft_incl E L κ' κ →
    tctx_incl E L +[p ◁ &uniq{κ} ty] +[p ◁ &uniq{κ'} ty; p ◁{κ'} blocked_type_ctor _ (&uniq{κ} ty)]
      (λ post '-[bor], λ π, ∀ (re_bor: ~~ (uniq_borₛ 𝔄)),
          uniq_bor_loc re_bor = uniq_bor_loc bor →
          uniq_bor_current re_bor = uniq_bor_current bor →
          post -[re_bor; (λ π, (uniq_bor_future re_bor π, uniq_bor_future bor π))] π).
  *)

  (*Lemma tctx_extract_hasty_reborrow {𝔄 𝔅l} (ty ty': type 𝔄) κ κ' (T: tctx 𝔅l) E L p :
    lctx_lft_incl E L κ' κ → eqtype E L ty ty' id id →
    tctx_extract_elt E L (p ◁ &uniq{κ'} ty) (p ◁ &uniq{κ} ty' +:: T)
      (p ◁{κ'} &uniq{κ} ty' +:: T) (λ post '((a, a') -:: bl),
        ∀a'': 𝔄, post ((a, a'') -:: (a'', a') -:: bl)).
  Proof.
    move=> ??. eapply tctx_incl_impl.
    - apply (tctx_incl_frame_r +[_] +[_;_]).
      eapply tctx_incl_trans; [by apply tctx_reborrow_uniq|].
      by apply subtype_tctx_incl, uniq_subtype, eqtype_symm.
    - by move=>/= ?[[??]?].
    - intros ??? [[??]?]. by apply forall_proper.
  Qed.*)
  

  Lemma type_deref_uniq_own_instr {𝔄} κ p n (ty: type 𝔄) E L I :
    lctx_lft_alive E L κ →
    typed_instr_ty E L I
        +[p ◁ &uniq{κ} (own_ptr n ty)]
        (!p)
        (&uniq{κ} ty)
        (λ post '-[bor], λ mask π, ∀ bor',
            uniq_bor_current bor' = snd (uniq_bor_current bor) →
            uniq_bor_future bor' π = snd (uniq_bor_future bor π) →
            of_cloc (uniq_bor_loc bor') = fst (uniq_bor_current bor) →
            of_cloc (uniq_bor_loc bor') = fst (uniq_bor_future bor π) →
            post bor' mask π).
  Proof.
    intros Alv.
    apply typed_instr_of_memload_with_cumutime1.
    intros x v d tid post mask.
    destruct x as [[[[[l x0] ξi] d'] g'] ξidx].
    destruct x0 as [l1 x1].
    iIntros "#LFT #TIME #PROPH #UNIQ E L #P own Obs ⧗ #⧖ £".
    iDestruct (Alv with "L E") as "#Alv".
    iDestruct "own" as "[[#Incl [%Hineq [UniqBody #PtBase]]] %Phys]".
    inversion Phys. subst v.
    
    iDestruct (lc_weaken (1 + 1 + 1 + 1) with "£") as "[[[£o £1'] £1] £f]"; [nia|].
    iMod (llctx_interp_make_guarded with "L") as (γ) "[H1 [H2 [#Ghalf #Halfback]]]". { solve_ndisj. }
    iDestruct (guards_transitive with "Ghalf Alv") as "#HguardsK".
    (* Open the borrow and run the lazy update of the payload; the points-to is put in
       the guarding proposition for the read. *)
    iMod (uniq_body_acc_keep with "LFT HguardsK Incl £o UniqBody H1") as "(_ & Gho & Pt & Close)".
    { rewrite /lazyE. solve_ndisj. }
    iModIntro. iExists l, l1,
      (fractional.half γ ∗ l #↦!∗ ty_phys (own_ptr n ty) (l1, x1) tid)%I.
    iSplit; first by done.
    iFrame "H2 Pt".
    iSplit. {
      iApply guard_cloc_combine.
      + iApply guards_weaken_lhs_sep_l. iApply (guards_transitive_right with "HguardsK PtBase").
      + leaf_goal laters to 0. { lia. }
        rewrite <- heap_complete_mapsto_fancy_fmap_eq.
        iApply guards_weaken_sep_r.
    }
    
    iIntros "[H2 Pt]".
    iDestruct ("Close" with "[Gho Pt]") as "Close". { iNext. iFrame. }
    iMod (fupd_mask_mono with "Close") as "[UniqBody H1]"; [solve_ndisj|].
    iMod (uniq_body_transform (own_ptr n ty) ty (l1, x1) x1 d' g' ξi ξidx κ tid l (l1, repeat [] (length (ty_phys ty x1 tid))) _ _ (pair_with_locₛ l1) (λ d g, (S d, g)) with "LFT PROPH UNIQ Incl [] [⧗ £1'] HguardsK H1 £f UniqBody") as (ζi ζidx) "[#Obs2 [UniqBody H1]]". { set_solver. }
     { iApply guards_refl. }
     { iIntros "[gho pt]".  iMod (lc_fupd_elim_later with "£1' gho") as "gho".
       destruct d'. { done. } iDestruct "gho" as "[phys [free gho]]".
       iModIntro. iDestruct (ty_gho_own_depth_mono _ _ _ (S d') g' with "gho") as "[gho _]". { lia. } { lia. }
       iFrame "gho".
       rewrite <- heap_cloc_mapsto_fancy_empty.
       iFrame "phys". iSplitL "⧗".
       { iIntros (d2 g2) "⧖2".
         iMod (cumulative_persistent_time_receipt with "TIME ⧗ ⧖2") as "#⧖2'".
         { rewrite /lazyE. solve_ndisj. }
         iModIntro. iApply (persistent_time_receipt_mono with "⧖2'"). simpl. lia. }
       iIntros (x2 d2 g2) "(gho & pt2)". iModIntro.
       iFrame "pt". simpl.
       replace (length (ty_phys ty x1 tid)) with (length (ty_phys ty x2 tid)).
        2: { repeat rewrite ty_size_eq. done. }
       rewrite <- heap_cloc_mapsto_fancy_empty.
       iFrame.
     }
    iDestruct ("Halfback" with "H1 H2") as "X".
    iMod (fupd_mask_mono with "X") as "L". { set_solver. }
    iModIntro. iExists ((l1, repeat [] (length (ty_phys ty x1 tid))), x1, ζi, d', g', ζidx).
    iFrame "L". iFrame "UniqBody". iFrame "Incl".
    iSplit. {
      iSplit. {
        iSplit. { iPureIntro. lia. }
        rewrite <- heap_cloc_mapsto_empty. iApply guards_true.
      }
      iPureIntro. done.
    }
    iCombine "Obs Obs2" as "Obs3".
    iApply (proph_obs_impl with "Obs3"). intros π [Ha Hb]. apply Ha; intuition.
      - unfold uniq_bor_future. simpl. rewrite Hb. trivial.
      - unfold uniq_bor_future, uniq_bor_loc. simpl. rewrite Hb. trivial.
  Qed.
    
  Lemma type_deref_uniq_own {𝔄 𝔅l ℭl 𝔇} κ x p e n (ty: type 𝔄)
    (T: tctx 𝔅l) (T': tctx ℭl) trx tr E L I (C: cctx 𝔇) :
    Closed (x :b: []) e →
    tctx_extract_ctx E L +[p ◁ &uniq{κ} (own_ptr n ty)] T T' trx →
    lctx_lft_alive E L κ →
    (∀v: val, typed_body E L I C (v ◁ &uniq{κ} ty +:: T') (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := !p in e) (trx ∘
    (λ post '(bor -:: bl), λ mask π, forall bor',
            uniq_bor_current bor' = snd (uniq_bor_current bor) →
            uniq_bor_future bor' π = snd (uniq_bor_future bor π) →
            of_cloc (uniq_bor_loc bor') = fst (uniq_bor_current bor) →
            of_cloc (uniq_bor_loc bor') = fst (uniq_bor_future bor π) →
            tr post (bor' -:: bl) mask π)
    ).
  Proof.
    iIntros (? Extr ?) "?".
    iApply type_let; [by eapply type_deref_uniq_own_instr|solve_typing| |done].
    destruct Extr as [Htrx _]=>??. apply Htrx. by case.
  Qed. 

  Lemma type_deref_shr_own_instr {𝔅} {E L I} κ p n (ty : type 𝔅) :
    lctx_lft_alive E L κ →
    typed_instr_ty E L I
      +[p ◁ &shr{κ} (own_ptr n ty)] (!p) (&shr{κ} ty)
      (λ post '-[(l1, (l2, a))], λ mask π, ∀ l2', of_cloc l2' = l2 → post (l2', a) mask π).
  Proof.
    intros Alv.
    apply typed_instr_of_memload.
    intros x v d tid post mask.
    destruct x as [l1 [l2 x2]].
    iIntros "#LFT #TIME #PROPH #UNIQ E L #P own Obs #⧖ £".
    iDestruct (Alv with "L E") as "#Alv".
    iDestruct "£" as "[£ [£1 £1']]".
    
    iDestruct "own" as "[gho %phys]".
    destruct d as [|d']; first by done.
    iDestruct "gho" as "[#Gp [#Shr #pers]]".
    destruct d' as [|d''].
    { iMod (lc_fupd_elim_later with "£1 pers") as "#pers'".
      iMod (lc_fupd_elim_later with "£1' pers'") as "#pers''".
      by iDestruct "pers''" as "[]". }
    iMod (own_shr_unfold with "£1 Shr") as "[#Gpt #Shr']".
    
    iModIntro. iExists l1, l2, (llctx_interp L).
    inversion phys. subst v.
    iSplit; first by done.
    iFrame "L".
    iSplit. {
      rewrite <- heap_mapsto_cells_fancy_fmap_eq.
      iApply (guards_transitive_right with "Alv Gp").
    }
    iIntros "L".
    iModIntro.
    iExists ((l2, repeat [] (length (ty_phys ty x2 tid))), x2). iFrame "L".
    iDestruct (proph_obs_impl with "Obs") as "$". { intros π Ha. apply Ha. done. }
    iSplit; last by done.
    iSplit. {
       simpl. rewrite <- heap_mapsto_cells_fancy_empty.
       leaf_goal laters to (S (S d'') + 2). { lia. } iFrame "Gpt".
    }
    iSplit. { iApply (ty_shr_depth_mono with "Shr'"); lia. }
    rewrite (bi.laterN_add (S (S (S d'')))). iNext.
    iApply (ty_gho_pers_depth_mono ty with "pers"). { lia. } { lia. }
  Qed.

  Lemma type_deref_shr_own {𝔄 𝔅l ℭl 𝔇} κ x p e n (ty: type 𝔄)
    (T: tctx 𝔅l) (T': tctx ℭl) trx tr E I L (C: cctx 𝔇) :
    Closed (x :b: []) e →
    tctx_extract_ctx E L +[p ◁ &shr{κ} (own_ptr n ty)] T T' trx →
    lctx_lft_alive E L κ →
    (∀v: val, typed_body E L I C (v ◁ &shr{κ} ty +:: T') (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := !p in e) (trx ∘
    (λ post '((l1, (l2, a)) -:: bl), λ mask π, forall l2', of_cloc l2' = l2 → tr post ((l2', a) -:: bl) mask π)
    ).
  Proof.
    iIntros (? Extr ?) "?".
    iApply type_let; [by eapply type_deref_shr_own_instr|solve_typing| |done].
    destruct Extr as [Htrx _]=>??. apply Htrx. by case.
  Qed.
 
  (** Dereferencing a [&uniq{κ} (&uniq{κ'} ty)] gives a [&uniq{κ} ty], by unnesting
      the inner borrow ([proph_ibor_unnest]). When [κ] ends, the closing view shift of
      the unnesting rebuilds the outer payload from the restored inner borrow (at
      [κ']). The outer payload needs the time receipt of the final inner value, which is
      only in the lazy part of the payload of the restored inner borrow. The outer
      payload is a guarded update for the lifetime of [&uniq{κ'} ty], which includes
      [κ']: inside the update, the guard lets us settle the restored inner borrow
      ([uniq_body_settle], with a stored later credit) and read the receipt; a stored
      cumulative time receipt bumps it for the outer depth. *)
  Lemma type_deref_uniq_uniq_instr {𝔄 E L I} κ κ' p (ty : type 𝔄) :
    lctx_lft_alive E L κ →
    typed_instr_ty E L I +[p ◁ &uniq{κ} (&uniq{κ'}ty)] (!p) (&uniq{κ} ty)
      (λ post '-[bor], λ mask π, ∀ bor',
        uniq_bor_loc bor'      = uniq_bor_loc (uniq_bor_current bor) →
        uniq_bor_current bor'  = uniq_bor_current (uniq_bor_current bor) →
        uniq_bor_future bor' π = fst (uniq_bor_future bor π) →
        uniq_bor_future (uniq_bor_current bor) π = snd (uniq_bor_future bor π) →
        post bor' mask π).
  Proof.
    intros Alv. apply typed_instr_of_memload_with_cumutime1.
    intros x v d tid post mask.
    iIntros "#LFT #TIME #PROPH #UNIQ E L #P own Obs ⧗ #⧖ £".
    iDestruct (Alv with "L E") as "#Alv".
    iDestruct "£" as "[£ [£s _]]".
    
    iMod (llctx_interp_make_guarded with "L") as (γ) "[H1 [H2 [#Ghalf #Halfback]]]". { solve_ndisj. }
    iDestruct (guards_transitive with "Ghalf Alv") as "HalfGuardsK".
    
    destruct x as [[[[[l x0] ξi] d0] g0] ξidx].
    destruct x0 as [[[[[l1 x1] ωi] d1] g1] ωidx].
    iDestruct "own" as "[[#Incl [%Ineqs [UniqBody #PtBase]]] %Phys]".
    iDestruct (lc_weaken (1 + 1) with "£") as "[£o £u]"; [nia|].

    iAssert (κ ⊑ κ')%I as "#Hκ⊑κ'". {
      iApply (guards_transitive with "Incl []"). iApply llftl_intersect_incl_l.
    }
    iAssert (κ ⊑ foldr meet static (ty_lfts ty))%I as "#Hκ⊑rest". {
      iApply (guards_transitive with "Incl []"). iApply llftl_intersect_incl_r.
    }
    iAssert (fractional.half γ &&{ ↑NllftG }&&> @[κ'])%I as "#HalfGuardsK'". {
      iApply (guards_transitive with "HalfGuardsK Hκ⊑κ'").
    }

    inversion Phys. subst v.
    set ξ := uniq_prvar (𝔄:=uniq_borₛ 𝔄) (l1, x1, ωi, d1, g1, ωidx) ξi.
    set ω := uniq_prvar x1 ωi.

    (* Open the outer borrow and run the lazy update of its payload; the points-to is
       put in the guarding proposition for the read. *)
    iMod (uniq_body_acc_keep with "LFT HalfGuardsK Incl £o UniqBody H1") as "(_ & Gho & Pt & Close)".
    { rewrite /lazyE. solve_ndisj. }
    iDestruct "Gho" as "(#Incli0 & %Ineqs2 & UBi & #PtBase2)".
    iDestruct (uniq_body_pers_component_impl with "UBi") as "#ωBor".
    iModIntro. iExists l, (l1.1),
      (fractional.half γ ∗ l #↦!∗ ty_phys (&uniq{κ'} ty) (l1, x1, ωi, d1, g1, ωidx) tid)%I.
    iSplit; [done|].
    iFrame "H2 Pt".
    iSplit. {
      iApply guard_cloc_combine.
      + iApply guards_weaken_lhs_sep_l. iApply (guards_transitive_right with "HalfGuardsK PtBase").
      + leaf_goal laters to 0. { lia. }
        rewrite <- heap_cloc_mapsto_fancy_fmap_eq.
        iApply guards_weaken_sep_r.
    }
    
    iIntros "[H2 Pt]".
    iDestruct ("Close" with "[Pt UBi]") as "Close". { iNext. iFrame "∗#%". }
    iMod (fupd_mask_mono with "Close") as "[UniqBody H1]"; [solve_ndisj|].
    iDestruct "UniqBody" as (κpo γo) "(#Inclo & (Gho & ξTok) & ⧗' & #ξBor)".
    rewrite /uniq_persγ proph_idx_bor_gen_unfold proph_bor_tok_unfold.
    iDestruct "ξTok" as "[ξVo ξIdxTok]".
    set xo := (l1, x1, ωi, d1, g1, ωidx).
    (* The new borrow [ζ] (of the inner contents), and a ghost variable [γk] recording
       whether its body has already been put in place (the "phase" of the unnesting). *)
    iMod (ghost_var_alloc (lstate_triv x1)) as (γζ) "[Ghζ Ghζ']".
    iMod (proph_loan_intro (uniq_cell_tyi x1) ⊤ (uniq_cell x1 d1 g1 γζ) with "PROPH UNIQ")
      as (ζi) "Loan"; [solve_ndisj|].
    set ζ := uniq_prvar x1 ζi.
    rewrite proph_loan_unfold. iDestruct "Loan" as "[ζVo ζPc]".
    pose (tinit := lstate_triv x1 : ltype_state).
    pose (tfin := lstate (PatBlocked κ) (inl (PlaceIn x1)) : ltype_state).
    iMod (ghost_var_alloc tinit) as (γk) "[Ghk Ghk']".

    (* Step 1: open the outer borrow, get its contents (the inner borrow), and
       pre-resolve the outer prophecy variable to the pair of the final values of [ζ] and
       of the inner borrow [ω]; the inner token is taken from the inner borrow, opened
       and closed again. *)
    iDestruct (llftl_bor_idx_to_full with "ξBor ξIdxTok") as "ξFull".
    iMod (llftl_bor_acc_guarded with "LFT ξFull HalfGuardsK H1") as "[Body Close1]";
      [solve_ndisj|].
    iMod (bi.later_exist_except_0 with "Body") as (c) "Body".
    iMod (bi.later_exist_except_0 with "Body") as (wξ) "[ξPc Body]".
    iMod (uniq_strip_later with "ξVo ξPc") as "(<- & ξVo & ξPc)".
    iMod (uniq_gbody_triv_open with "Gho Body") as "(_ & Gho1 & Gho2 & Payload)".
    iMod (uniq_payload_force with "[] H2 £u Payload") as "(H2 & #⧖o & GhoO & Pt)";
      [rewrite /lazyE; solve_ndisj| |].
    { iApply (guards_transitive with "HalfGuardsK Incl"). }
    iDestruct "GhoO" as "(#Incli & %Ineqs' & UBi & #PtBasei)".
    iDestruct "UBi" as (κpω γω) "(#Inclω & (Ghω & ωTok) & ⧗i & #ωBor')".
    rewrite /uniq_persγ proph_idx_bor_gen_unfold proph_bor_tok_unfold.
    iDestruct "ωTok" as "[ωVo ωIdxTok]".
    iMod (llftl_bor_idx_acc_guarded with "LFT ωBor' ωIdxTok HalfGuardsK' H2")
      as "[ωBody ωClose]"; [solve_ndisj|].
    iMod (bi.later_exist_except_0 with "ωBody") as (cω) "ωBody".
    iMod (bi.later_exist_except_0 with "ωBody") as (wω) "[ωPc ωBody]".
    iMod (uniq_strip_later with "ωVo ωPc") as "(<- & ωVo & ωPc)".
    iDestruct (uniq_proph_tok with "ωVo ωPc") as "(ωVo & ωtok & ToωPc)".
    iDestruct (uniq_proph_tok with "ζVo ζPc") as "(ζVo & ζtok & ToζPc)".
    pose (uπ := (λ π: proph_asn, ((((π ζ).1, (π ω).1), (1%positive, (1%positive, 1%positive)))
      : uniq_cellₛ (uniq_borₛ 𝔄))) : proph (uniq_cellₛ (uniq_borₛ 𝔄))).
    have Hdep: uπ ./ [ζ; ω].
    { apply (proph_dep_constr2 (λ a b, (((a: uniq_cellₛ 𝔄).1, (b: uniq_cellₛ 𝔄).1),
        (1%positive, (1%positive, 1%positive))) : uniq_cellₛ (uniq_borₛ 𝔄))
        (λ π, π ζ) (λ π, π ω) [ζ] [ω]); apply proph_dep_one. }
    iMod (uniq_preresolve ξ [ζ; ω] uπ 1%Qp with "UNIQ PROPH ξVo ξPc [$ζtok $ωtok]")
      as "(#Obs2 & (ζtok & ωtok & _) & ToξPc)"; [solve_ndisj|done|done|].
    iDestruct ("ToζPc" with "ζtok") as "ζPc".
    iDestruct ("ToωPc" with "ωtok") as "ωPc".
    iMod (fupd_mask_subseteq (↑Nllft)) as "Upd"; [solve_ndisj|].
    iMod ("ωClose" with "[ωPc ωBody]") as "[ωIdxTok H2]".
    { iNext. iExists _, _. iFrame. }
    iMod "Upd" as "_".

    (* The outer borrow keeps (besides the inner token) the observer of [ω] and the outer
       half of its state, with the phase: initially (before [ζ]'s body is in place) also
       the loan of [ζ]; finally, the state of [ω] refines the final value of [ζ]. *)
    pose (A := (∃ cω' p r tag, .VO[ω] cω' ∗ ⌜cell_γ cω' = γω⌝ ∗
      ghost_var γω (1/2) (lstate p r) ∗ pat_ok κ p ∗ ghost_var γk (1/2) tag ∗
      ((⌜tag = tinit ∧ cω' = uniq_cell x1 d1 g1 γω ∧ lstate p r = lstate_triv x1⌝ ∗
          .VO[ζ] (uniq_cell x1 d1 g1 γζ) ∗ ∃ wζ, .PC[ζ] (uniq_cell x1 d1 g1 γζ) wζ) ∨
       ⌜tag = tfin ∧ ∀ π, prfn_den r π = (π ζ).1⌝))%I).
    pose (R := (⧗1 ∗ ⧗1 ∗ £1 ∗ l #↦!∗ ty_phys (&uniq{κ'} ty) xo tid)%I).
    iMod (fupd_mask_subseteq (↑Nllft)) as "Upd"; [solve_ndisj|].
    iMod ("Close1" $! (A ∗ R ∗ idx_bor_tok ωidx)%I
      with "[Gho1 Gho2 ToξPc ωVo Ghω Ghk ζVo ζPc ⧗i ⧗ £s Pt ωIdxTok]") as "[ξB1 H1]".
    { iSplitL "Gho1 Gho2 ToξPc"; last first.
      { iNext. iFrame "⧗i ⧗ £s Pt ωIdxTok".
        iExists _, PatLeaf, (inl (PlaceIn x1)), tinit. iFrame "ωVo Ghω Ghk".
        iSplit; [done|]. iSplit; [iApply pat_ok_leaf|]. iLeft. iFrame "ζVo".
        iSplit; [done|]. iExists _. iFrame "ζPc". }
      (* Rebuilding the outer body, once [κ] has ended: it is blocked at [κ]; once
         unblocked, the inner borrow is settled (unblocked and closed at the trivial
         state). *)
      iNext. iIntros "(A & (⧗i & ⧗ & £s & Pt) & ωIdxTok)".
      pose (sO := lstate (𝔄:=uniq_borₛ 𝔄) (PatBlocked κ) (inl (PlaceProph (xo: ~~ (uniq_borₛ 𝔄)) (λ π, (uπ π).1)))).
      iMod (ghost_var_update_halves sO with "Gho1 Gho2") as "[Gho1 _]".
      iModIntro. iNext. iExists (uniq_cell (𝔄:=uniq_borₛ 𝔄) xo d0 g0 γo), uπ. iSplitL "ToξPc"; [iApply "ToξPc"|].
      rewrite /uniq_gbody cpd_body_cell.
      iExists (PatBlocked κ), (inl (PlaceProph (xo: ~~ (uniq_borₛ 𝔄)) (λ π, (uπ π).1))). iFrame "Gho1".
      iSplit. { iApply pat_ok_blocked. iApply "Inclo". }
      iSplit. { iPureIntro. intros π. by rewrite prfn_den_inl. }
      iApply guarded_upd_intro. iModIntro. iFrame "⧖o".
      rewrite /leaf_owned /blocked_owned. iIntros "#†κ". iModIntro.
      iIntros (G ?) "#Gty G".
      iDestruct "A" as (cω' pa ra tag) "(ωVo & %Hcω & Ghω & #Okω & Ghk & Br)".
      iMod (fractional.frac_split_guard_in_half with "G Gty") as (γh) "[G1 [G2 [#Gh #Back]]]";
        [rewrite /lazyE; solve_ndisj|].
      iAssert (fractional.half γh &&{↑NllftG}&&> @[κ'])%I as "#Ghκ'".
      { iApply (guards_transitive with "Gh"). iApply llftl_intersect_incl_l. }
      iAssert (fractional.half γh &&{↑NllftG}&&> @[ty_lft ty])%I as "#Ghty".
      { iApply (guards_transitive with "Gh"). iApply llftl_intersect_incl_r. }
      iMod (llftl_bor_idx_acc_guarded with "LFT ωBor' ωIdxTok Ghκ' G1") as "[ωB ωClose]";
        [rewrite /lazyE; solve_ndisj|].
      iMod (lc_fupd_elim_later with "£s ωB") as (c' w') "[ωPc ωB]".
      iDestruct (uniq_agree with "ωVo ωPc") as %<-.
      rewrite /uniq_gbody (uniq_cell_surj cω') cpd_body_cell Hcω.
      iDestruct "ωB" as (p' r') "(_ & %Hw' & Ghω' & Upd)".
      iDestruct (ghost_var_agree with "Ghω Ghω'") as %[<- <-]%lstate_inj.
      iMod (guarded_upd_run with "Ghty G2 Upd") as "[G2 [#⧖ω Node]]"; [done|].
      destruct ra as [lr|]; [|done].
      iMod (leaf_owned_unblock with "LFT Ghty Okω †κ G2 ⧖ω Node")
        as "[G2 (%y & %d' & %g' & Rel & #⧖' & Pt' & Gho')]".
      (* The equalizer of [ζ]: in the initial phase, from its controller; in the final
         phase, from the refinement of the inner borrow. *)
      iAssert (▷ ((λ π, (π ζ).1) :== vπ y))%I with "[Br Rel]" as "Eqζ".
      { iDestruct "Br" as "[(_ & ζVo & %wζ & ζPc)|(_ & %Hfin)]".
        - iDestruct (uniq_proph_tok with "ζVo ζPc") as "(_ & ζtok & _)". iNext.
          iDestruct (proph_eqz_token ζ (λ π, (vπ y π, (1%positive, (1%positive, 1%positive))))
            with "PROPH ζtok") as "Eqz".
          by iDestruct (proph_eqz_fst_const with "Eqz") as "Eqz".
        - iDestruct (place_rfn_rel_eqz with "Rel") as "Eqz". iNext.
          iApply (proph_eqz_eq with "Eqz"); [|done]. fun_ext=>π /=.
          by rewrite -Hfin prfn_den_inl. }
      iMod (ghost_var_update_halves (lstate_triv y) with "Ghω Ghω'") as "[Ghω Ghω']".
      iMod (uniq_update ω (uniq_cell y d' g' γω) (vπ (uniq_cell y d' g' γω))
        with "UNIQ ωVo ωPc") as "[ωVo ωPc]"; [rewrite /lazyE; solve_ndisj|].
      iMod (fupd_mask_mono with "(ωClose [Ghω' Pt' Gho' ωPc])") as "[ωIdxTok G1]";
        [rewrite /lazyE; solve_ndisj| |].
      { iNext. iExists _, _. iFrame "ωPc". iApply (uniq_gbody_triv_close' with "Ghω'"); [done|].
        iApply (uniq_payload_intro with "⧖' Gho' Pt'"). }
      iMod (fupd_mask_mono with "(Back G1 G2)") as "$"; [rewrite /lazyE; solve_ndisj|].
      iMod (cumulative_persistent_time_receipt with "TIME ⧗ ⧖'") as "#⧖y";
        [rewrite /lazyE; solve_ndisj|].
      iModIntro. iExists (l1, y, ωi, d', g', ωidx), (S d'), (g0 `max` g').
      iSplitL "Eqζ".
      { rewrite /place_rfn_rel. iNext. iApply (proph_eqz_prod with "[Eqζ] []").
        - iApply (proph_eqz_eq with "Eqζ"); done.
        - iApply (proph_eqz_eq with "[]"); [done| |iApply proph_eqz_refl].
          fun_ext=> π /=. apply (uniq_prvar_app_irrel x1 y ωi π). }
      iSplitR.
      { iCombine "⧖o ⧖y" as "⧖max". iApply (persistent_time_receipt_mono with "⧖max"). lia. }
      rewrite /ofty_owned /=. iFrame "Pt". iFrame "Incli". iSplit; [iPureIntro; lia|].
      iSplitL "Ghω ωVo ωIdxTok ⧗i".
      { iExists κpω, γω. iFrame "Inclω ⧗i". rewrite /uniq_tokγ /uniq_persγ.
        rewrite (uniq_bor_tok_retarget y x1) (uniq_idx_bor_gen_retarget _ y x1).
        rewrite proph_bor_tok_unfold proph_idx_bor_gen_unfold. iFrame "∗#". }
      iApply (lguards_weaken_later with "PtBasei"). lia. }
    iMod "Upd" as "_".

    (* Step 2: unnest the inner borrow. *)
    iMod (llftl_sep_split with "LFT ξB1") as "[ABor RBor]"; [solve_ndisj|].
    iMod (llftl_sep_split with "LFT RBor") as "[_ TokBor]"; [solve_ndisj|].
    iMod (llftl_idx_bor_unnest with "LFT ωBor' TokBor") as "InBor"; [solve_ndisj|].
    iDestruct (llftl_bor_shorten (κ' ⊓ κ) κ with "[] InBor") as "InBor".
    { iApply llftl_incl_glb; [done|iApply guards_refl]. }
    iMod (llftl_sep_join with "LFT ABor InBor") as "Bor"; [solve_ndisj|].

    (* Step 3: open the combination, and close it with the new borrow [ζ], at the
       trivial state; when [κ] ends, the final state of [ζ] is put in the inner borrow,
       blocked at [κ] (its blocked lifetimes are included in [κ]). *)
    iMod (llftl_bor_acc_guarded with "LFT Bor HalfGuardsK H1") as "[[A ωB] Close3]";
      [solve_ndisj|].
    iMod (bi.later_exist_except_0 with "A") as (cω') "A".
    iMod (bi.later_exist_except_0 with "A") as (pa) "A".
    iMod (bi.later_exist_except_0 with "A") as (ra) "A".
    iMod (bi.later_exist_except_0 with "A") as (tag) "(>ωVo & >%Hcω & >Ghω & #Okω & >Ghk & Br)".
    iDestruct (ghost_var_agree with "Ghk Ghk'") as %->.
    iDestruct "Br" as "[(>%Hin & >ζVo & Hζ)|>%Hfin]"; last first.
    { exfalso. destruct Hfin as [Hfin _]. by apply lstate_inj in Hfin as [? _]. }
    destruct Hin as (_ & -> & Hpr). apply lstate_inj in Hpr as [-> ->].
    iMod (bi.later_exist_except_0 with "Hζ") as (wζ) "ζPc".
    iMod (uniq_strip_later with "ζVo ζPc") as "(_ & ζVo & ζPc)".
    iMod (bi.later_exist_except_0 with "ωB") as (c2) "ωB".
    iMod (bi.later_exist_except_0 with "ωB") as (w2) "[ωPc ωB]".
    iMod (uniq_strip_later with "ωVo ωPc") as "(<- & ωVo & ωPc)".
    iMod (uniq_gbody_triv_open with "Ghω ωB") as "(_ & Ghω & Ghω' & Payload)".
    iMod (uniq_update ζ (uniq_cell x1 d1 g1 γζ) (vπ (uniq_cell x1 d1 g1 γζ))
      with "UNIQ ζVo ζPc") as "[ζVo ζPc]"; [solve_ndisj|].
    pose (Qζ := (∃ c w, .PC[ζ] c w ∗ uniq_gbody κ ty tid l1 c w)%I).
    iMod (fupd_mask_subseteq (↑Nllft)) as "Upd"; [solve_ndisj|].
    iMod ("Close3" $! Qζ with "[Ghω Ghω' Ghk Ghk' ωVo ωPc ζPc Payload Ghζ']") as "[ζBor H1]".
    { iSplitR "ζPc Payload Ghζ'"; last first.
      { iNext. iExists _, _. iFrame "ζPc".
        iApply (uniq_gbody_triv_close' with "Ghζ'"); [done|done]. }
      iNext. iIntros "Body".
      iMod (bi.later_exist_except_0 with "Body") as (c3) "Body".
      iMod (bi.later_exist_except_0 with "Body") as (w3) "[ζPc3 Body]".
      rewrite /uniq_gbody {1}/cpd_body.
      iMod (bi.later_exist_except_0 with "Body") as (p3) "Body".
      iMod (bi.later_exist_except_0 with "Body") as (r3) "(#Ok3 & >%Hw3 & _ & Upd3)".
      pose (sω := lstate (PatBlocked κ) (inl (PlaceProph x1 (λ π, (π ζ).1)))).
      iMod (ghost_var_update_halves sω with "Ghω Ghω'") as "[Ghω Ghω']".
      iMod (ghost_var_update_halves tfin with "Ghk Ghk'") as "[Ghk _]".
      pose (cnew := uniq_cell x1 (cell_d c3) (cell_g c3) γω).
      pose (wnew := (λ π: proph_asn, (((π ζ).1, (1%positive, (1%positive, 1%positive))) : uniq_cellₛ 𝔄))
        : proph (uniq_cellₛ 𝔄)).
      iMod (uniq_update ω cnew wnew with "UNIQ ωVo ωPc") as "[ωVo ωPc]".
      { pose proof (nclose_subseteq NllftUsr 0). solve_ndisj. }
      iModIntro. iNext. iSplitL "ωVo Ghω Ghk".
      { iExists cnew, (PatBlocked κ), (inl (PlaceProph x1 (λ π, (π ζ).1))), tfin.
        iFrame "ωVo Ghω Ghk". iSplit; [done|].
        iSplit; [iApply pat_ok_blocked; iApply guards_refl|].
        iRight. iPureIntro. split; [done|]. intros π. by rewrite prfn_den_inl. }
      iExists cnew, wnew. iFrame "ωPc". rewrite cpd_body_cell.
      iExists (PatBlocked κ), (inl (PlaceProph x1 (λ π, (π ζ).1))). iFrame "Ghω'".
      iSplit. { iApply pat_ok_blocked. iApply (llftl_incl_trans with "Hκ⊑κ' Inclω"). }
      iSplit. { iPureIntro. intros π. by rewrite prfn_den_inl. }
      iIntros (G' ?) "#G'ty G'".
      iMod (guarded_upd_run with "G'ty G' Upd3") as "[$ [#⧖3 Node3]]"; [done|].
      iModIntro. iFrame "⧖3".
      destruct r3 as [lr3|]; [|done].
      rewrite /leaf_owned /blocked_owned. iIntros "#†κ". iModIntro.
      iIntros (G'' ?) "#G''ty G''".
      iMod (leaf_owned_unblock with "LFT G''ty Ok3 †κ G'' ⧖3 Node3")
        as "[$ (%y & %d' & %g' & Rel & ⧖' & O)]".
      iModIntro. iExists y, d', g'. iFrame "⧖' O".
      iDestruct (place_rfn_rel_eqz with "Rel") as "Eqz". rewrite /place_rfn_rel. iNext.
      iApply (uniq_ctrl_eqz_fst with "PROPH ζPc3").
      iApply (proph_eqz_eq with "Eqz"); [|done]. fun_ext=> π /=. by rewrite Hw3 prfn_den_inl. }
    iMod "Upd" as "_".
    iDestruct (llftl_bor_idx with "ζBor") as (ζidx) "[#ζBor ζIdxTok]".
    iMod (fupd_mask_subseteq (↑NllftG)) as "Upd"; first solve_ndisj.
    iMod ("Halfback" with "H1 H2") as "L".
    iMod "Upd" as "_".
    iModIntro. iExists (l1, x1, ζi, d1, g1, ζidx).
    iFrame "L".
    iSplitL "Ghζ ζVo ζIdxTok ⧗'".
    - rewrite /ty_own /=. iSplit; [|done].
      iSplit; [iFrame "Hκ⊑rest"|].
      iSplit; [iPureIntro; lia|].
      iSplitL "Ghζ ζVo ζIdxTok ⧗'".
      { iExists κ, γζ. iFrame "⧗'". iSplit; [iApply guards_refl|].
        rewrite /uniq_tokγ /uniq_persγ proph_bor_tok_unfold proph_idx_bor_gen_unfold.
        iFrame "∗#". }
      iApply (guards_transitive_right with "Hκ⊑κ' []").
      iApply (lguards_weaken_later with "PtBase2"). lia.
    - iCombine "Obs Obs2" as "Obs".
      iApply (proph_obs_impl with "Obs"). intros π [Ha Hb].
      apply Ha; trivial.
      + unfold uniq_bor_future. simpl. rewrite Hb. trivial.
      + unfold uniq_bor_future. simpl. rewrite Hb. trivial.
  Qed.

  Lemma type_deref_uniq_uniq {𝔄 𝔅l ℭl 𝔇} κ κ' x p e (ty: type 𝔄)
    (T: tctx 𝔅l) (T': tctx ℭl) trx tr E L I (C: cctx 𝔇) :
    Closed (x :b: []) e →
    tctx_extract_ctx E L +[p ◁ &uniq{κ} (&uniq{κ'} ty)] T T' trx →
    lctx_lft_alive E L κ → lctx_lft_incl E L κ κ' →
    (∀v: val, typed_body E L I C (v ◁ &uniq{κ} ty +:: T') (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := !p in e) (trx ∘
    (λ post '(bor -:: bl), λ mask π, ∀ bor',
        uniq_bor_loc bor'      = uniq_bor_loc (uniq_bor_current bor) →
        uniq_bor_current bor'  = uniq_bor_current (uniq_bor_current bor) →
        uniq_bor_future bor' π = fst (uniq_bor_future bor π) →
        uniq_bor_future (uniq_bor_current bor) π = snd (uniq_bor_future bor π) →
        tr post (bor' -:: bl) mask π))%type.
  Proof.
    iIntros. iApply typed_body_tctx_incl; [done|].
    by iApply type_let; [by eapply type_deref_uniq_uniq_instr|solve_typing| |done].
  Qed.

  Lemma type_deref_shr_uniq_instr {𝔄} {E L I} κ κ' p (ty : type 𝔄) :
    lctx_lft_alive E L κ →
    lctx_lft_incl E L κ κ' →
    typed_instr_ty E L I +[p ◁ &shr{κ} (&uniq{κ'} ty)] (!p) (&shr{κ} ty)
      (λ post '-[(l, bor)], post (uniq_bor_loc bor, uniq_bor_current bor)).
  Proof.
    intros Alv Incl. apply typed_instr_of_memload.
    intros x v d tid post mask.
    iIntros "#LFT #TIME #PROPH #UNIQ E L #P own Obs #⧖ £".
    iDestruct (Alv with "L E") as "#Alv".
    iDestruct (Incl with "L E") as "#Incl".
    iDestruct (guards_transitive with "Alv Incl") as "Alv'".
    destruct x as [l [[[[[l1 x0] ξi] d1] g1] ξidx]].
    iDestruct "own" as "[gho %phys]". inversion phys. subst v.
    destruct d as [|d']; first by done.
    iDestruct "gho" as "[#G↦ [#Shr _]]".
    (* Unfold the (structural) sharing predicate of [&uniq], which also has the
       persistent predicate of the referent. *)
    iDestruct "Shr" as "([%Le1 %Le2] & #Gpt & _ & #InnerShr & #InnerPers)".
    iDestruct (lc_weaken 1 with "£") as "£"; [lia|].
    iMod (lc_fupd_elim_later with "£ InnerShr") as "#InnerShr'".
    iAssert (κ ⊑ κ ⊓ κ')%I as "#Hκ". { iApply llftl_incl_glb; [iApply guards_refl|done]. }
    
    iModIntro. iExists l, l1.1, (llctx_interp L). iSplit; first by done. iFrame "L".
    
    iSplit. {
      rewrite <- heap_mapsto_cells_fancy_fmap_eq.
      iApply (guards_transitive_right with "Alv G↦").
    }
    iIntros "L".
    
    iModIntro. iExists (l1, x0). iFrame.
    iSplit; last by done.
    iSplit. { leaf_goal laters to (S d' + 1). { lia. }
      iApply (guards_transitive_right with "Hκ Gpt"). }
    iSplit. { iApply ty_shr_depth_mono; [| |iApply (ty_shr_lft_mono0 with "Hκ InnerShr'")]; lia. }
    iApply (bi.laterN_le 2); [lia|]. iNext. iNext.
    iApply (ty_gho_pers_depth_mono with "InnerPers"); lia.
  Qed.

  Lemma type_deref_shr_uniq {𝔄 𝔅l ℭl 𝔇} κ κ' x p e (ty: type 𝔄)
    (T: tctx 𝔅l) (T': tctx ℭl) trx tr E L I (C: cctx 𝔇) :
    Closed (x :b: []) e →
    tctx_extract_ctx E L +[p ◁ &shr{κ} (&uniq{κ'} ty)] T T' trx →
    lctx_lft_alive E L κ → lctx_lft_incl E L κ κ' →
    (∀v: val, typed_body E L I C (v ◁ &shr{κ} ty +:: T') (subst' x v e) tr) -∗
    typed_body E L I C T (let: x := !p in e)
      (trx ∘
        (λ post '((l, bor) -:: bl), λ mask π,
            tr post ((uniq_bor_loc bor, uniq_bor_current bor) -:: bl) mask π)
      )%type.
  Proof.
    iIntros. iApply typed_body_tctx_incl; [done|].
    iApply type_let; [by eapply type_deref_shr_uniq_instr|apply tctx_incl_refl| |done].
    by move=>/= ?[[??]?].
  Qed.
End borrow.

(*
Global Hint Resolve tctx_extract_hasty_borrow tctx_extract_hasty_reborrow
  | 10 : lrust_typing.*)
