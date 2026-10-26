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
      iExists v. iFrame "#". iIntros "†κ".
      iDestruct ("Back" with "†κ") as "Back". iMod (fupd_mask_mono with "Back") as "Back". { set_solver. }
      iMod (bi.later_exist_except_0 with "Back") as (x'') "Back".
      iMod (bi.later_exist_except_0 with "Back") as (d'') "Back".
      iMod (bi.later_exist_except_0 with "Back") as (g'') "Back".
      iDestruct "Back" as "(Eqz & >⧖'' & gho & >pt)".
      iModIntro. iExists (l, x''), (S d'' `max` g'').
      destruct (S d'' `max` g'') as [|d1] eqn:Hd1; first by lia.
      iFrame.
      iSplitL "Eqz". {
        iNext.
        iApply proph_eqz_modify.
         2: { iApply (proph_eqz_constr (λ t, (l, t)) with "Eqz"). }
        iApply (proph_obs_impl with "Obsξζ"). intros π Ha.
        simpl. simpl in Ha. rewrite <- Ha.  trivial.
      }
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
    iDestruct "Own" as "[[#Incl [%Ineqs [UniqBody [#PtBase #Pers]]]] #Phys]".
    
    iDestruct "Pers" as "[Dead|Pers]". {
      iDestruct "Dead" as (κ') "[Incl' Dead']".
      iDestruct (guards_transitive with "Ghalf Alv") as "G2".
      iDestruct (guards_transitive with "G2 Incl'") as "G3".
      leaf_open "G3" with "H1" as "[Alive _]". { set_solver. }
      iExFalso. iApply (llftl_not_own_end with "Alive Dead'").
    }
    
    iMod (resolve_uniq_body ty x0 ξi d' g' idx κ tid l with "LFT PROPH UNIQ TIME Incl E Ghalf H1 UniqBody") as "(#Obs2 & H1 & #Shr & #PtGuard)". { trivial. } { set_solver. }
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
    iDestruct "gho" as "(#Incl2 & %Hineq & UniqBody & #PtBase & #InnerPers)".
    iDestruct (guards_transitive with "κ'⊑κ Incl2") as "Inclκ'".
    (* Get the persistent information without a later, or that κ is dead. *)
    iAssert (|={⊤}=> [†κ] ∨ ty_gho_pers ty x0 d' g' tid)%I with "[£]" as ">#InnerPers'".
    { iDestruct "InnerPers" as "[Dead|InnerPers]".
      - iDestruct "Dead" as (κ3) "[#Incl3 Dead3]".
        iMod (llftl_incl_dead_implies_dead with "LFT Incl3 Dead3") as "#†κ". { set_solver. }
        by iLeft.
      - iRight. iApply (lc_fupd_elim_later with "[£] InnerPers").
        iApply (lc_weaken with "£"). rewrite /advance_credits. lia. }
    iMod (uniq_body_reborrow ty x0 ξi d' g' idx κ κ' tid l with
      "LFT PROPH UNIQ κ'⊑κ ⧗ [] InnerPers' UniqBody") as (ζi ζidx) "[UniqBody' Inh]".
    { solve_ndisj. } { iApply (persistent_time_receipt_mono with "⧖"). lia. }
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
          iSplit. {
            leaf_goal laters to (d + 1); first by lia.
            iApply (guards_transitive_right with "κ'⊑κ PtBase").
          }
          iDestruct "InnerPers" as "[Dead|$]". iLeft.
          iApply (basically_dead_incl with "κ'⊑κ Dead").
        } {
          iPureIntro. apply phys.
        }
      } {
        iSplit; last by done. iExists v. iFrame "P". iIntros "#†κ'".
        iMod (fupd_mask_subseteq (↑Nllft)) as "Upd"; first set_solver.
        iMod ("Inh" with "†κ'") as (x'' d'' g'' idx'') "(UB & Eqz & R)".
        iMod "Upd" as "_".
        iDestruct "R" as "[>#⧖'' Pers'']".
        rewrite bi.later_or. iDestruct "Pers''" as "[>#Dead''|#Pers'']".
        - iModIntro. iExists (l, x'', ξi, d'', g'', idx'').
          iExists (d `max` S d'' `max` g'').
          iSplitL "Eqz". {
            iNext.
            iApply (proph_eqz_prod with "[Eqz]").
              - iFrame "Eqz".
              - iApply (proph_eqz_eq with "[]"); [done| |iApply proph_eqz_refl].
                fun_ext=> π /=. apply (uniq_prvar_app_irrel x0 x'' ξi π).
          }
          iCombine "⧖'' ⧖" as "⧖max".
          iSplit. { iApply (persistent_time_receipt_mono with "⧖max"). lia. }
          iFrame "⧗'".
          iSplit; last by done. iSplit. { iFrame "Incl2". }
          iSplit. { iPureIntro. nia. }
          iFrame "UB".
          iSplit. { leaf_goal laters to (d + 1); first by lia. iFrame "PtBase". }
          iLeft. iExists κ. iFrame "Dead''". iApply guards_refl.
        - iModIntro. iExists (l, x'', ξi, d'', g'', idx'').
          iExists (d `max` S d'' `max` g'').
          iSplitL "Eqz". {
            iNext.
            iApply (proph_eqz_prod with "[Eqz]").
              - iFrame "Eqz".
              - iApply (proph_eqz_eq with "[]"); [done| |iApply proph_eqz_refl].
                fun_ext=> π /=. apply (uniq_prvar_app_irrel x0 x'' ξi π).
          }
          iCombine "⧖'' ⧖" as "⧖max".
          iSplit. { iApply (persistent_time_receipt_mono with "⧖max"). lia. }
          iFrame "⧗'".
          iSplit; last by done. iSplit. { iFrame "Incl2". }
          iSplit. { iPureIntro. nia. }
          iFrame "UB".
          iSplit. { leaf_goal laters to (d + 1); first by lia. iFrame "PtBase". }
          iRight. iFrame "Pers''".
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
    iDestruct "own" as "[[#Incl [%Hineq [UniqBody [#PtBase #Pers]]]] %Phys]".
    inversion Phys. subst v.
    
    iDestruct "Pers" as "[Dead|Pers]". {
      iDestruct "Dead" as (κ') "[Incl' Dead']".
      iDestruct (guards_transitive with "Alv Incl'") as "G2".
      leaf_open "G2" with "L" as "[Alive _]". { solve_ndisj. }
      iExFalso. iApply (llftl_not_own_end with "Alive Dead'").
    }
    
    rewrite uniq_body_unfold. iDestruct "UniqBody" as "(ξTok & £saved & #ξBor)".
    iModIntro. iExists l, l1, (llctx_interp L ∗ uniq_tok (𝔄:=at_locₛ 𝔄) (l1, x1) ξi d' g' ξidx)%I.
    iSplit; first by done.
    iFrame "L". iFrame "ξTok".
    iSplit. {
      iDestruct (uniq_tok_guard_payload _ _ _ _ _ _ _ _ _
        (llctx_interp L ∗ uniq_tok (𝔄:=at_locₛ 𝔄) (l1, x1) ξi d' g' ξidx)%I 0 with "LFT ξBor [] []") as "Gexists".
        - iApply (guards_weaken_lhs_sep_l with "Alv").
        - iApply guards_weaken_sep_r.
        - iDestruct (guards_weaken_rhs_sep_r with "Gexists") as "G1".
          iDestruct (guards_weaken_rhs_sep_r with "G1") as "G2".
          iApply guard_cloc_combine.
           + iApply (guards_transitive_right with "[] PtBase").
             iApply (guards_transitive with "[] Alv").
             leaf_by_sep; iIntros "(?&?)"; iFrame; iIntros; done.
           + leaf_goal laters to 1. { lia. }
             rewrite <- heap_complete_mapsto_fancy_fmap_eq.
             iFrame "G2".
    }
    
    iIntros "[L ξTok]".
    
    iMod (llctx_interp_make_guarded with "L") as (γ) "[H1 [H2 [#Ghalf #Halfback]]]". { solve_ndisj. }
    iDestruct (guards_transitive with "Ghalf Alv") as "HguardsK".
    iDestruct "£" as "[£ [£1' £1]]".
    iMod (uniq_body_transform (own_ptr n ty) ty (l1, x1) x1 d' g' ξi ξidx κ tid l (l1, repeat [] (length (ty_phys ty x1 tid))) _ _ (pair_with_locₛ l1) (λ d g, (S d, g)) with "LFT PROPH UNIQ [⧗ £1'] HguardsK H1 [ξTok £saved]") as (ζi ζidx) "[#Obs2 [UniqBody H1]]". { set_solver. }
     { iIntros "[gho pt]".  iMod (lc_fupd_elim_later with "£1' gho") as "gho".
       destruct d'. { done. } iDestruct "gho" as "[phys [free gho]]".
       iModIntro. iDestruct (ty_gho_own_depth_mono _ _ _ (S d') g' with "gho") as "[gho _]". { lia. } { lia. }
       iFrame "gho".
       rewrite <- heap_cloc_mapsto_fancy_empty.
       iFrame "phys". iIntros (x2 d2 g2) "[gho [pt2 ⧖2]]".
       iMod (cumulative_persistent_time_receipt with "TIME ⧗ ⧖2") as "⧖2'". { solve_ndisj. }
       iModIntro. iFrame "pt". simpl.
       replace (length (ty_phys ty x1 tid)) with (length (ty_phys ty x2 tid)).
        2: { repeat rewrite ty_size_eq. done. }
       rewrite <- heap_cloc_mapsto_fancy_empty.
       iFrame. iApply (persistent_time_receipt_mono with "⧖2'"). lia.
       
     }
     { rewrite uniq_body_unfold. iFrame. iFrame "ξBor". }
    iDestruct ("Halfback" with "H1 H2") as "X".
    iMod (fupd_mask_mono with "X") as "L". { set_solver. }
    iMod (lc_fupd_elim_later with "£1 Pers") as "#Pers'".
    iModIntro. iExists ((l1, repeat [] (length (ty_phys ty x1 tid))), x1, ζi, d', g', ζidx).
    iFrame "L". iFrame "UniqBody". iFrame "Incl".
    iSplit. {
      iSplit. {
        iSplit. { iPureIntro. lia. }
        iSplit. { rewrite <- heap_cloc_mapsto_empty. iApply guards_true. }
        iRight. destruct d'; [done|]. iNext.
        iApply (ty_gho_pers_depth_mono _ d' g' with "Pers'"). { lia. } { lia. }
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
    iDestruct "£" as "[£ [£1 £1']]".
    
    iMod (llctx_interp_make_guarded with "L") as (γ) "[H1 [H2 [#Ghalf #Halfback]]]". { solve_ndisj. }
    iDestruct (guards_transitive with "Ghalf Alv") as "HalfGuardsK".
    
    destruct x as [[[[[l x0] ξi] d0] g0] ξidx].
    destruct x0 as [[[[[l1 x1] ωi] d1] g1] ωidx].
    iDestruct "own" as "[[#Incl [%Ineqs [UniqBody [#PtBase #Pers]]]] %Phys]".
    rewrite uniq_body_unfold. iDestruct "UniqBody" as "(ξTok & ⧗' & #ξBor)".
     
    iDestruct "Pers" as "[Dead|Pers]". {
      iDestruct "Dead" as (κ'') "[Incl' Dead']".
      iDestruct (guards_transitive with "HalfGuardsK Incl'") as "G2".
      leaf_open "G2" with "H1" as "[Alive _]". { solve_ndisj. }
      iExFalso. iApply (llftl_not_own_end with "Alive Dead'").
    }
    iMod (lc_fupd_elim_later with "£1 Pers") as "#Pers'".
    iDestruct "Pers'" as "(%Ineqs2 & #Pers2 & #ωBor)".

    iAssert (κ ⊑ κ')%I as "#Hκ⊑κ'". {
      iApply (guards_transitive with "Incl []"). iApply llftl_intersect_incl_l.
    }
    iAssert (κ ⊑ foldr meet static (ty_lfts ty))%I as "#Hκ⊑rest". {
      iApply (guards_transitive with "Incl []"). iApply llftl_intersect_incl_r.
    }
    iAssert (fractional.half γ &&{ ↑NllftG }&&> @[κ'])%I as "#HalfGuardsK'". {
      iApply (guards_transitive with "HalfGuardsK Hκ⊑κ'").
    }
    iDestruct "Pers2" as "[Dead|#Pers2]". {
      iDestruct "Dead" as (κ'') "[Incl' Dead']".
      iDestruct (guards_transitive with "HalfGuardsK' Incl'") as "G2".
      leaf_open "G2" with "H2" as "[Alive _]". { solve_ndisj. }
      iExFalso. iApply (llftl_not_own_end with "Alive Dead'").
    }

    inversion Phys. subst v.
    set ξ := uniq_prvar (𝔄:=uniq_borₛ 𝔄) (l1, x1, ωi, d1, g1, ωidx) ξi.
    set ω := uniq_prvar x1 ωi.

    iDestruct (uniq_tok_guard_payload _ _ _ _ _ _ _ _ _
      (fractional.half γ ∗ uniq_tok (𝔄:=uniq_borₛ 𝔄) (l1, x1, ωi, d1, g1, ωidx) ξi d0 g0 ξidx)%I 0
      with "LFT ξBor [] []") as "#Gexists".
    { iApply (guards_weaken_lhs_sep_l with "HalfGuardsK"). }
    { iApply guards_weaken_sep_r. }
    (* Extract the inner points-to guard *)
    iMod (guards_extract_persistent_later _ _ (@[κ'] &&{↑NllftG; g0+1}&&> l1 #↦∗_)%I
      with "Gexists [H1 ξTok] []") as "J".
    { solve_ndisj. } { iFrame. } { iIntros "(_ & (_ & _ & _ & $ & _) & _)". }
    iMod (lc_fupd_elim_later with "[£] J") as "J".
    { iApply (lc_weaken with "£"). nia. }
    iMod "J" as "[[H1 ξTok] #PtBase2]".
    
    iModIntro. iExists l, (l1.1), (fractional.half γ ∗
      uniq_tok (𝔄:=uniq_borₛ 𝔄) (l1, x1, ωi, d1, g1, ωidx) ξi d0 g0 ξidx)%I.
    iSplit; [done|].
    iFrame "H1". iFrame "ξTok".
    iSplit. {
      iDestruct (guards_weaken_rhs_sep_r with "Gexists") as "G1".
      iDestruct (guards_weaken_rhs_sep_r with "G1") as "G2".
      iApply guard_cloc_combine.
      + iApply (guards_transitive_right with "[] PtBase").
        iApply guards_weaken_lhs_sep_l. done.
      + leaf_goal laters to 1. { lia. }
        rewrite <- heap_cloc_mapsto_fancy_fmap_eq.
        iFrame "G2".
    }
    
    iIntros "[H1 ξTok]".

    (* Allocate the new prophetic borrow, and unnest *)
    iMod (proph_loan_intro (uniq_cell_tyi x1) ⊤ (uniq_cell x1 d1 g1) with "PROPH UNIQ")
      as (ζi) "Loan"; [solve_ndisj|].
    set ζ := uniq_prvar x1 ζi.
    set h := λ (c: ~~ (uniq_cellₛ 𝔄)),
      uniq_cell (𝔄:=uniq_borₛ 𝔄) (l1, c.1, ωi, dec_depth c.2.1, dec_depth c.2.2, ωidx)
        (S (dec_depth c.2.1)) (g0 `max` dec_depth c.2.2).
    set Hπ := λ (a b: (uniq_cellₛ 𝔄)),
      (((a.1, b.1), (enc_depth (S (dec_depth a.2.1)), enc_depth (g0 `max` dec_depth a.2.2)))
        : (uniq_cellₛ (uniq_borₛ 𝔄))).
    set Sm := λ (c: ~~ (uniq_cellₛ 𝔄)),
      (⧖(S (S (dec_depth c.2.1)) `max` dec_depth c.2.2) ∗
        ▷ ty_gho_pers ty c.1 (dec_depth c.2.1) (dec_depth c.2.2) tid)%I.
    have HS: ∀ c, Persistent (Sm c) by intros; apply _.
    have Hinj: Inj (=) (=) h.
    { intros [c1 [p1 p2]] [c2 [p3 p4]] Heq. rewrite /h /uniq_cell /= in Heq.
      injection Heq as -> E1 E2.
      by rewrite -(enc_dec_depth p1) -(enc_dec_depth p2) -(enc_dec_depth p3) -(enc_dec_depth p4) E1 E2. }
    have Hcomm: ∀ c π, vπ (h c) π = Hπ (vπ c π) (π ω).
    { intros [c [p1 p2]] π. rewrite /h /Hπ /=. do 2 f_equal.
      apply (uniq_prvar_app_irrel c x1 ωi π). }
    have Hrefl: ∀ c ζl, (λ π, Hπ (vπ c π) (π ω)) ./ ζl → vπ c ./ ζl.
    { intros [c [p1 p2]] ζl Dep. apply uniq_cell_dep_rev. simpl.
      intros π π' Heq. have := Dep π π' Heq. rewrite /Hπ /=. by intros [=]. }
    have Hdep: (λ π, Hπ (π ζ) (π ω)) ./ [ζ; ω].
    { apply (proph_dep_constr2 Hπ (λ π, π ζ) (λ π, π ω) [ζ] [ω]); apply proph_dep_one. }
    iMod (proph_ibor_unnest ⊤ κ κ' ξ (uniq_cell (𝔄:=uniq_borₛ 𝔄) (l1, x1, ωi, d1, g1, ωidx) d0 g0)
      ξidx (uniq_payload (&uniq{κ'} ty) tid l) ω (uniq_cell x1 d1 g1) ωidx
      (uniq_payload ty tid l1) ζi
      (⧖(S d0 `max` g0) ∗ ⧗1 ∗ l #↦!∗ [FVal #(l1.1)] ∗ κ' ⊑ ty_lft ty ∗
        (@[κ'] &&{↑NllftG; g0+1}&&> l1 #↦∗_))%I Sm h Hπ (fractional.half γ)
      ltac:(apply _) ltac:(solve_ndisj) Hinj HS Hcomm Hrefl Hdep
      with "LFT PROPH UNIQ HalfGuardsK Hκ⊑κ' [ωBor] [] [] [⧗] H1 Loan [ξTok]")
      as "(#Obs2 & ζBor & H1)".
    { by rewrite /uniq_body_pers_component. }
    { (* Split the outer payload *)
      iIntros "Payload". rewrite uniq_payload_cell.
      iDestruct "Payload" as "(>#⧖o & Gho & >Pt)".
      iDestruct "Gho" as "(Incli & _ & UBody & PtBasei & _)".
      rewrite uniq_body_unfold. iDestruct "UBody" as "(>ωTok & >⧗i & _)".
      iModIntro. iSplitL "ωTok"; [by iNext|]. iSplitL "⧗i Pt Incli PtBasei"; [iNext; iFrame "∗#"|].
      iIntros ([x' [p1 p2]]) "ωTok #Sy' (#⧖o' & ⧗i & Pt & #Incli & #PtBasei)".
      rewrite /h uniq_payload_cell. iModIntro. iNext.
      iDestruct "Sy'" as "[#⧖y' #Persy']". simpl.
      iCombine "⧖o' ⧖y'" as "⧖max".
      iSplit. { iApply (persistent_time_receipt_mono with "⧖max"). lia. }
      iFrame "Pt".
      iFrame "Incli".
      iSplit. { iPureIntro. lia. }
      iSplitL "ωTok ⧗i".
      { iApply (uniq_body_from_parts with "[ωTok] ⧗i [ωBor]").
        - rewrite /uniq_tok -(uniq_cell_surj (x', (p1, p2))).
          by rewrite (uniq_bor_tok_retarget x1 x').
        - by rewrite (uniq_pers_component_retarget ty x' x1 ωi _ _ d1 g1). }
      iSplit. { iApply (lguards_weaken_later with "PtBasei"). lia. }
      iRight. iFrame "Persy'". }
    { rewrite /Sm /= !dec_enc_depth. iFrame "Pers2".
      iApply (persistent_time_receipt_mono with "⧖"). lia. }
    { (* Record a persistent summary of the final value *)
      iIntros ([x' [p1 p2]]) "Payload".
      rewrite /uniq_payload /Sm /=.
      iDestruct "Payload" as "(>#⧖y & Gho & Pt)".
      iMod (cumulative_persistent_time_receipt with "TIME ⧗ ⧖y") as "#⧖y'".
      { solve_ndisj. }
      iDestruct (ty_gho_pers_impl with "Gho") as "#GhoPers".
      iModIntro. iSplitL "Gho Pt".
      { iNext. iFrame "∗#". }
      iNext. iSplit.
      - iApply (persistent_time_receipt_mono with "⧖y'"). lia.
      - iFrame "GhoPers". }
    { rewrite proph_ibor_sep. iFrame "ξBor". iApply "ξTok". }
    iDestruct "ζBor" as (ζidx) "ζBor".
    iMod (fupd_mask_subseteq (↑NllftG)) as "Upd"; first solve_ndisj.
    iMod ("Halfback" with "H1 H2") as "L".
    iMod "Upd" as "_".
    iModIntro. iExists (l1, x1, ζi, d1, g1, ζidx).
    iFrame "L".
    iSplitL "ζBor ⧗'".
    - rewrite /ty_own /=. iSplit; [|done].
      iSplit; [iFrame "Hκ⊑rest"|].
      iSplit; [iPureIntro; lia|].
      iSplitL "ζBor ⧗'". { rewrite /uniq_body. iFrame. }
      iSplit. {
        iApply (guards_transitive_right with "Hκ⊑κ' []").
        iApply (lguards_weaken_later with "PtBase2"). lia.
      }
      iRight. iFrame "Pers2".
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
    iDestruct "gho" as "[#G↦ [#Shr #Pers]]".
    (* Unfold the (structural) sharing predicate of [&uniq]. *)
    iDestruct "Shr" as "([%Le1 %Le2] & #Gpt & _ & #InnerShr)".
    iDestruct (lc_weaken ((S d' + 1) + 1) with "£") as "[£p £s]"; [lia|].
    iMod (lc_fupd_elim_laterN with "£p Pers") as "#Pers'".
    iMod (lc_fupd_elim_later with "£s InnerShr") as "#InnerShr'".
    iDestruct "Pers'" as "(_ & #InnerPers & _)".
    iAssert (κ ⊑ κ ⊓ κ')%I as "#Hκ". { iApply llftl_incl_glb; [iApply guards_refl|done]. }
    
    iModIntro. iExists l, l1.1, (llctx_interp L). iSplit; first by done. iFrame "L".
    
    iSplit. {
      rewrite <- heap_mapsto_cells_fancy_fmap_eq.
      iApply (guards_transitive_right with "Alv G↦").
    }
    iIntros "L".
    
    iDestruct "InnerPers" as "[Dead|InnerPers]". {
      iDestruct "Dead" as (κ'') "[Incl' Dead']".
      iDestruct (guards_transitive with "Alv' Incl'") as "G2".
      leaf_open "G2" with "L" as "[Alive _]". { set_solver. }
      iExFalso. iApply (llftl_not_own_end with "Alive Dead'").
    }
    
    iModIntro. iExists (l1, x0). iFrame.
    iSplit; last by done.
    iSplit. { leaf_goal laters to (S d' + 1). { lia. }
      iApply (guards_transitive_right with "Hκ Gpt"). }
    iSplit. { iApply ty_shr_depth_mono; [| |iApply (ty_shr_lft_mono with "Hκ InnerShr'")]; lia. }
    iNext. iApply (ty_gho_pers_depth_mono with "InnerPers"); lia.
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
