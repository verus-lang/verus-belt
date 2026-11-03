From lrust.typing Require Export pcell.
From lrust.typing Require Import programs uniq_util.
From guarding Require Import guard tactics.
From lrust.lifetime Require Import lifetime_full guarded_bor.
Set Default Proof Using "Type".

(** * Borrows of the contents of a [PCell]

[PCell::borrow] gives a shared reference [&shr{κ} ty] to the contents of a cell, given shared
references to the cell and to its permission: the guards of the move right and of the
permission give a guard of the contents ((L2), [gcell_share]), which are the bytes of the
contents at the location of the cell ([bytes_own ty l x]). [PCell::borrow_mut] gives a unique
borrow [&uniq{κ} ty] of the contents, given a shared reference to the cell and a unique
borrow of the permission: the contents are lent ((L3p), [pcell_lend_uniq]); the prophecy of
the permission [(g, x)] is resolved to [(g, x')] with [x'] the prophecy of the new borrow.

The unified place rules then apply below the borrows: field reads and writes, reborrows,
shared reads. When [κ] ends, the cell (whose shared reference was at [κ]) can be moved: the
contents are back in the instance. *)

Implicit Type 𝔄 𝔅: syn_type.

Section cell_borrow.
  Context `{!typeG Σ}.

  Definition PCellBorrow : val := (λ: ["pcell"; "perm"], "pcell")%V.

  Lemma type_pcell_borrow_instr {𝔄} κ (ty: type 𝔄) p q E L I :
    typed_instr E L I
      +[p ◁ᵥ &shr{κ} (pcell_ty (ty_wmty ty)); q ◁ᵥ &shr{κ} (cell_points_to_ty ty)]
      (PCellBorrow [p; q]) (λ v, +[v ◁ᵥ &shr{κ} ty])
      (λ post '-[(l, g); (_, (g', x))], λ mask π, g = g' ∧ post -[(l, x)] mask π).
  Proof.
    iIntros (tid post mask iκs [[l g] [[l' [g' x]] []]]) "_ #TIME #PROPH _ _ $ $ (p & q & _) #Obs".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & _)"; [done|].
    iDestruct (tctx_val_elim with "p") as (vp Hp wp dp [-> Hwp]) "[#⧖p #Own]". simpl in Hwp. simplify_eq.
    iDestruct (tctx_val_elim with "q") as (vq Hq wq dq [-> Hwq]) "[#⧖q #Own']".
    have Hm := ty_mty_wf ty.
    rewrite /PCellBorrow.
    wp_bind p. iApply (wp_wand with "[]"); [by iApply wp_eval_path|]. iIntros (? ->).
    wp_bind q. iApply (wp_wand with "[]"); [by iApply wp_eval_path|]. iIntros (? ->).
    destruct dp as [|dp]; [done|]. destruct dq as [|dq]; [done|].
    set D := dp `max` dq.
    iDestruct "Own" as "(#Gp & _ & _)". iDestruct "Own'" as "(_ & [#Pt #TyShr] & #Pers)".
    iDestruct "Pt" as (γ fv Hfv) "[#Hp #Gb]".
    iAssert (⧖(S D))%I as "#⧖D".
    { rewrite /D Nat.succ_max_distr persistent_time_receipt_sep. by iFrame "⧖p ⧖q". }
    (* (L2): the guards of the move right and of the permission give a guard of the
       contents *)
    iDestruct (guard_pcell_gca _ _ (ty_wmty ty) with "Hp Gp") as "Ga".
    iDestruct (lguards_weaken_later _ _ _ _ (S D + 1) with "Ga") as "GaD"; [lia|].
    iDestruct (lguards_weaken_later _ _ _ _ (S D + 1) with "Gb") as "GbD"; [lia|].
    iDestruct "Hp" as "(_ & #GI & _)".
    iDestruct (gcell_share with "GI GaD GbD") as "Gc"; [solve_ndisj|].
    wp_rec. iExists -[(l, x)]. iSplitR "Obs"; last first.
    { iApply (proph_obs_impl with "Obs"). by intros π [_ ?]. }
    iSplit; [|done]. rewrite tctx_val_val. iExists (S D). iSplit; [done|]. iFrame "⧖D".
    rewrite /= /by_succ. iSplit; [|iSplit].
    - by rewrite /shr_bytes_own (bytes_own_gcont ty l x fv).
    - iApply (ty_shr_depth_mono with "TyShr"); lia.
    - iDestruct "Pers" as "[_ Pers]".
      iApply (bi.laterN_le (S dq + 1) (S (D + 1))); [lia|]. iNext.
      iApply (ty_gho_pers_depth_mono with "Pers"); lia.
  Qed.

  Definition PCellBorrowMut : val := (λ: ["pcell"; "perm"], "pcell")%V.

  Lemma type_pcell_borrow_mut_instr {𝔄} κ (ty: type 𝔄) p q E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
      +[p ◁ᵥ &shr{κ} (pcell_ty (ty_wmty ty)); q ◁ᵥ &uniq{κ} (cell_points_to_ty ty)]
      (PCellBorrowMut [p; q]) (λ v, +[v ◁ᵥ &uniq{κ} ty])
      (λ post '-[(l, g); bor], λ mask π,
        let '(_, (g', x), _, _, _, _) := bor in g = g' ∧
        ∀ bor', uniq_bor_current bor' = x →
          uniq_bor_future bor' π = (uniq_bor_future bor π).2 →
          (uniq_bor_future bor π).1 = g →
          uniq_bor_loc bor' = l →
          post -[bor'] mask π).
  Proof.
    iIntros (Alv tid post mask iκs [[l g] [[[[[[l' [g' x]] ξi] di] gi] ξidx] []]])
      "#LFT #TIME #PROPH #UNIQ #E L $ (p & q & _) #Obs".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & _)"; [done|].
    iDestruct (tctx_val_elim with "p") as (vp Hp wp dp [-> Hwp]) "[#⧖p #Own]". simpl in Hwp. simplify_eq.
    iDestruct (tctx_val_elim with "q") as (vq Hq wq dq [-> Hwq]) "[#⧖q Uniq]".
    iDestruct "Uniq" as "(#Incl & [%Hle1 %Hle2] & Body)".
    have Hm := ty_mty_wf ty.
    rewrite /PCellBorrowMut.
    wp_bind p. iApply (wp_wand with "[]"); [by iApply wp_eval_path|]. iIntros (? ->).
    wp_bind q. iApply (wp_wand with "[]"); [by iApply wp_eval_path|]. iIntros (? ->).
    destruct dp as [|dp]; [done|]. iDestruct "Own" as "(#Gp & _ & #Pers)".
    set D := S dp `max` dq.
    iAssert (⧖D)%I as "#⧖D"; [rewrite persistent_time_receipt_sep; by iFrame "⧖p ⧖q"|].
    iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME ⧖D"); [done|]. iIntros "£ _".
    iDestruct (lc_weaken ((S dp + 1) + (5 + (S dp + 1) + (1 + (S dp + 1)))) with "£")
      as "[£p £l]"; [rewrite /advance_credits; lia|].
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Gh #Back]]]"; [solve_ndisj|].
    iAssert (|={⊤ ∖ ↑advN}=> fractional.half γh ∗ (fractional.half γh &&{↑NllftG}&&> @[κ]))%I
      with "[H1]" as ">[H1 #Gκ]".
    { leaf_open "Gh" with "H1" as "[InterpL back]". { solve_ndisj. }
      iDestruct (Alv with "InterpL E") as "#Alv".
      iMod ("back" with "InterpL") as "$". iModIntro.
      iApply (guards_transitive with "Gh Alv"). }
    iMod (lc_fupd_elim_laterN with "£p Pers") as "Pers'".
    iDestruct "Pers'" as (γ) "#Hp".
    (* (L3p): lend the contents *)
    iMod (pcell_lend_uniq ty κ l g γ (S dp + 1) l' x ξi di gi ξidx tid with
      "LFT PROPH UNIQ Hp Gp Incl Gκ H1 £l Body") as (ζi ζidx) "(#Obsl & Body & H1)";
      [solve_lazyE|].
    iMod (fupd_mask_mono with "(Back H1 H2)") as "$"; [solve_ndisj|].
    wp_rec. iModIntro. iExists -[(l, x, ζi, di, gi, ζidx)].
    iSplitR "Obs"; last first.
    { iCombine "Obsl Obs" as "Obs2". iApply (proph_obs_impl with "Obs2").
      intros π [Hl [_ Hpost]]. apply Hpost; [done| | |done]; by rewrite /uniq_bor_future /= Hl. }
    iSplit; [|done]. rewrite tctx_val_val. iExists D. iSplit; [done|]. iFrame "⧖D".
    iFrame "Incl Body". iPureIntro; lia.
  Qed.
End cell_borrow.
