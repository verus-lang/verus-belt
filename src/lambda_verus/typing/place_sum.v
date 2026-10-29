(** * Sum places

  A leaf [OfTy (Σ! tyl)] of a place rooted at an owned location ([p ◁ₗown{n} lt]) holds a
  sum. Reading its discriminant ([type_case_oplace]) branches on the
  variant [i] of its value and, in branch [i], unfolds the leaf into a _sum place_ at
  variant [i], [SumLty tyl i (OfTy (tyl +!! i))] (whose payload is the leaf of the
  variant; the specification of the branch knows the variant). The payload is reached
  by the context step [PSum tyl i w K] (offset 1, [lpath.v]), so that the general rules
  for unfolding, reborrowing, shared borrows, reading, writing and unblocking leaves,
  and for dropping a place while its leaves are blocked, apply to the payload and its
  subplaces. A sum place is folded back unconditionally ([tctx_fold_oplace_sum]). A leaf
  of an owned place can be assigned a whole new variant with a payload of size 1
  ([type_sum_assign_oplace_instr]) or a unit variant ([type_sum_unit_oplace_instr]). For
  places rooted at a value (e.g. at a unique borrow), below any number of unique borrows,
  see the rules of [place_deep.v]. *)

From iris.proofmode Require Import proofmode.
From lrust.lang Require Import proofmode.
From lrust.typing Require Export type ltype lpath place_own sum.
From lrust.typing Require Import type_context programs programs_util lft_contexts
  uniq_util uniq_bor product own uninit freeable_util type_sum.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section place_sum.
  Context `{!typeG Σ}.

  Lemma pctx_plug_cpd {𝔅 𝔄} (K: pctx 𝔅 𝔄) lt : pctx_nonempty K → lty_is_cpd (pctx_plug K lt).
  Proof. by destruct K. Qed.

  (** A cell of a location without ghost cells is trivially owned. *)
  Lemma guards_empty_cell (G: iProp Σ) E k (l: loc) : ⊢ G &&{E; k}&&> (l, []) #↦_.
  Proof.
    rewrite -heap_complete_mapsto_singleton (_: [[]] = repeat [] 1) //
      -heap_cloc_mapsto_empty.
    iApply guards_true.
  Qed.

  Lemma lty_rfn_sum_in {𝔄l} (tyl: typel 𝔄l) i (lt: lty (𝔄l !!ₗ i)) a pad ζm q :
    lty_rfn (SumLty tyl i lt) (pinj i a, pad) ζm q = prfn_sum i (lty_rfn lt a ζm (false :: q)) pad.
  Proof. by rewrite lty_rfn_sum /= psum_proj_pinj. Qed.

  (** The interpretation of a sum place whose payload is a leaf, at the refinement of a
      value. *)
  Lemma sum_ofty_own_rfn m {𝔄l} (tyl: typel 𝔄l) i (y: ~~ (Σ! 𝔄l)) ζm q d g tid l :
    ltype_own (Owned m) (SumLty tyl i (OfTy (tyl +!! i)))
      (lty_rfn (SumLty tyl i (OfTy (tyl +!! i))) y ζm q) d g tid l ⊢
    ltype_own (Owned m) (OfTy (Σ! tyl)) (inl (PlaceIn y)) d g tid l.
  Proof.
    rewrite lty_rfn_sum. case_match eqn:Ha.
    - apply psum_proj_Some in Ha. destruct y as [s pad]. simpl in Ha. subst s.
      iIntros "H". iApply sum_ofty_unfold_own. iExact "H".
    - rewrite /ltype_own /=. by iIntros "[]".
  Qed.
End place_sum.

Section typing.
  Context `{!typeG Σ}.

  (** * Places rooted at a unique borrow *)

  (** ** Folding a sum place *)

  (** ** Reading the discriminant *)

  Lemma big_sepN_lookup n (Φ: fin n → iProp Σ) i : ([∗ nat] j < n, Φ j) -∗ Φ i.
  Proof.
    iIntros "All". iInduction n as [|n] "IH"; [by inv_fin i|]=>/=.
    iDestruct "All" as "[Φ All]". inv_fin i; [done|]=> i. by iApply ("IH" $! (λ j, Φ (FS j))).
  Qed.

  (** * Places rooted at an owned location *)

  Lemma tctx_fold_oplace_sum {𝔄l 𝔄} E L p n (K: pctx (Σ! 𝔄l) 𝔄) `{!PctxNoUniq K} (tyl: typel 𝔄l) i :
    tctx_incl E L +[p ◁ₗown{n} pctx_plug K (SumLty tyl i (OfTy (tyl +!! i)))]
      +[p ◁ₗown{n} pctx_plug K (OfTy (Σ! tyl))] (λ post '-[x], post -[x]).
  Proof.
    apply (tctx_oplace_change_hole _ _ _ _ K); [by rewrite lty_size_sum_ofty|done|].
    iIntros (y ζm q d g tid l) "H !>". by iApply sum_ofty_own_rfn.
  Qed.

  (** Reading the discriminant of the leaf at the hole of [K] (a sum, at any path): the
      leaf is unfolded into a sum place at the variant [i] of its value, and the program
      continues with branch [i]. *)
  Lemma type_case_oplace {𝔄l 𝔄 𝔅l 𝔇} E L I (C: cctx 𝔇) p n (K: pctx (Σ! 𝔄l) 𝔄) `{!PctxNoUniq K}
      (tyl: typel 𝔄l) (T: tctx 𝔅l) el el' trl :
    IntoPlistc el el' →
    ([∗ nat] i < length 𝔄l, typed_body E L I C
      (p ◁ₗown{n} pctx_plug K (SumLty tyl i (OfTy (tyl +!! i))) +:: T) (el' -!! i) (trl -!! i)) -∗
    typed_body E L I C (p ◁ₗown{n} pctx_plug K (OfTy (Σ! tyl)) +:: T)
      (case: !(pctx_expr K p) of el)
      (λ post '(x -:: cl), let 'xinj i _ := to_xsum (pctx_get K x.1.2).1 in
        (trl -!! i) post (x -:: cl))%type.
  Proof.
    move=> ->. iIntros "el".
    iIntros (tid [x xl] mask post iκs) "#LFT #TIME #PROPH #UNIQ #E L I C /=[Tp T] #Obs".
    destruct x as [[l x₀] ζm].
    rewrite /tctx_elt_interp.
    iDestruct "Tp" as (v Hp D d g) "(#⧖ & ⧗p & -> & %Hle & Fr & Own)".
    have ?: Closed [] (pctx_expr K p).
    { apply pctx_expr_closed. by eapply eval_path_closed. }
    rewrite /ltype_own lty_pat_plug lty_rfn_plug ltype_own_plug.
    iDestruct "Own" as "[L1 Rest]". iSimpl in "L1".
    iDestruct "L1" as (? ->) "[Pt1 Gho1]".
    remember (pctx_get K x₀) as y eqn:Hy. destruct y as [s pad].
    destruct (to_xsum s) as [j a] eqn:Hj.
    have Hs: s = pinj j a. { by rewrite -(semi_iso' to_xsum of_xsum s) Hj. }
    subst s.
    set lr := (l, repeat [] (lty_size (pctx_plug K (OfTy (Σ! tyl))))).
    set lK := pctx_loc K (ty_size (Σ! tyl)) x₀ lr.
    (* The address of the hole. *)
    iMod lc_zero as "£0".
    wp_bind (pctx_expr K p).
    iApply (wp_wand with "[Rest £0]").
    { iApply (wp_pctx_expr K (ty_size (Σ! tyl)) 1 x₀ ζm [] d g tid lr p True True 0
        with "[] £0 [] Rest").
      - rewrite /lr -heap_cloc_mapsto_empty. iApply guards_true.
      - iApply wp_wand; [by iApply wp_eval_path|]. by iIntros (?) "->". }
    iIntros (w) "(-> & _ & _ & Rest)".
    (* Read the discriminant. *)
    iEval (rewrite split_pt_xsum_cells'') in "Pt1". iDestruct "Pt1" as "(Tag & Pay & Pad)".
    iMod lc_zero as "£0".
    wp_bind (!(LitV _))%E.
    iApply (wp_read_na_guarded_cells_singleton _ (cloc_take lK 1).1 (cloc_take lK 1).2
      (cloc_take lK 1 #↦∗ [ #j ]) #j 0 with "[Tag £0]"); [solve_ndisj| |].
    { iFrame "Tag £0". iApply guard_cloc_combine; [|iApply guards_refl].
      iDestruct (oplace_loc_guard K (OfTy (Σ! tyl)) x₀ l (cloc_take lK 1 #↦∗ [ #j ])%I
        (↑NllftG) 0) as "G".
      rewrite (heap_cloc_mapsto_emp_vec_app lK 1).
      iApply (guards_weaken_rhs_sep_l with "G"). }
    iIntros "!> Tag".
    wp_case. { split; [lia|]. by rewrite Nat2Z.id -vlookup_lookup plistc_to_vec_lookup. }
    iDestruct (big_sepN_lookup _ _ j with "el") as "el".
    iApply ("el" $! _ (((l, x₀), ζm) -:: xl)
      with "LFT TIME PROPH UNIQ E L I C [-] []"); last first.
    { iApply proph_obs_impl; [|done]=>/= ?. by rewrite -Hy /= to_xsum_pinj. }
    iFrame "T". iExists #l. iSplit; [done|]. iExists D, d, g. iFrame "⧖".
    rewrite (lty_nrc_plug_eq K (OfTy (Σ! tyl)) (SumLty tyl j (OfTy (tyl +!! j)))) //
      (lty_size_plug_eq K _ (OfTy (Σ! tyl))); [|apply lty_size_sum_ofty].
    iFrame "⧗p Fr". iSplit; [done|]. iSplit; [done|].
    rewrite /ltype_own lty_pat_plug lty_rfn_plug -Hy lty_rfn_sum_in ltype_own_plug
      lty_size_sum_ofty. iFrame "Rest".
    iApply sum_ofty_unfold_own. iExists (pinj j a, pad). iSplit; [done|].
    rewrite /ofty_owned split_pt_xsum_cells''. by iFrame.
  Qed.

  (** ** Assigning a new variant *)

  Lemma xsum_phys_pinj_1 {𝔄l} (tyl: typel 𝔄l) i u vb pad tid :
    ty_phys (tyl +!! i) u tid = [FVal vb] → length pad = (max_ty_size tyl - 1)%nat →
    1 ≤ max_ty_size tyl →
    ty_phys (Σ! tyl) (pinj i u, pad) tid = FVal #i :: FVal vb :: fmap FVal pad.
  Proof.
    intros Hph Hlen ?. rewrite /ty_phys /xsum_ty /= to_xsum_pinj Hph /=.
    apply pad_length'. rewrite /= length_fmap. lia.
  Qed.

  (** Assigning a variant [i] with a payload of size 1 to the leaf at the hole of [K]
      (a sum, at any path), as [type_sum_assign_instr]: the old value is resolved, the
      tag and the payload are written, the padding keeps its (arbitrary) contents. *)
  Lemma type_sum_assign_oplace_instr {𝔄l 𝔄} E L I p q n (K: pctx (Σ! 𝔄l) 𝔄) `{!PctxNoUniq K}
      (tyl: typel 𝔄l) (i: fin (length 𝔄l)) Φ :
    ty_size (tyl +!! i) = 1%nat → resolve E L (Σ! tyl) Φ →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K (OfTy (Σ! tyl)); q ◁ tyl +!! i]
      (pctx_expr K p <-{Σ i} q)
      (λ _, +[p ◁ₗown{n} pctx_plug K (OfTy (Σ! tyl))])
      (λ post '-[x; b], λ mask π, Φ (pctx_get K x.1.2) π → ∀ pad,
        post -[((x.1.1, pctx_set K x.1.2 (pinj i b, pad)), x.2)] mask π).
  Proof.
    iIntros (Hsz Rslv tid post mask iκs [x [b []]])
      "#LFT #TIME #PROPH #UNIQ #E L I (Tp & Tb & _) Obs".
    destruct x as [[l x₀] ζm].
    rewrite /tctx_elt_interp.
    iDestruct "Tp" as (v Hp D d g) "(#⧖ & ⧗p & -> & %Hle & Fr & Own)".
    iDestruct "Tb" as (vb db Hpb) "(#⧖b & Gb & %Phys)".
    have ?: Closed [] (pctx_expr K p).
    { apply pctx_expr_closed. by eapply eval_path_closed. }
    have ?: Closed [] q by eapply eval_path_closed.
    rewrite /ltype_own lty_pat_plug lty_rfn_plug ltype_own_plug.
    iDestruct "Own" as "[L1 Rest]". iSimpl in "L1".
    iDestruct "L1" as (? ->) "[Pt1 Gho1]".
    iDestruct (pctx_own_in with "Rest") as %Hin.
    iDestruct (pctx_own_mode_le with "Rest") as %Hk.
    set k0 := pctx_mode K 0.
    set y := pctx_get K x₀.
    destruct (oplace_loc_empty K (OfTy (Σ! tyl)) x₀ l) as [l' Hl'].
    set lr := (l, repeat [] (lty_size (pctx_plug K (OfTy (Σ! tyl))))).
    set dh := pctx_depth K d.
    have Hdh: dh ≤ d. { rewrite /dh pctx_depth_sub. lia. }
    have HM: 1 ≤ max_ty_size tyl.
    { rewrite -Hsz. apply (max_hlist_with_ge (λ _, ty_size) tyl i). }
    (* The address of the hole. *)
    iMod lc_zero as "£0".
    wp_bind (pctx_expr K p).
    iApply (wp_wand with "[Rest £0]").
    { iApply (wp_pctx_expr K (ty_size (Σ! tyl)) 1 x₀ ζm [] d g tid lr p True True 0
        with "[] £0 [] Rest").
      - rewrite /lr -heap_cloc_mapsto_empty. iApply guards_true.
      - iApply wp_wand; [by iApply wp_eval_path|]. by iIntros (?) "->". }
    iIntros (w) "(-> & _ & _ & Rest)".
    change (lty_size (OfTy (Σ! tyl))) with (ty_size (Σ! tyl)) in Hl'.
    rewrite -/lr in Hl'. rewrite Hl'.
    (* The write steps give cumulative time receipts: for credits, and to raise the
       depth of the place to the depth of the new value below [k0] owned pointers. *)
    wp_bind (_ <- _)%E.
    iCombine "⧖ ⧖b" as "⧖m".
    iApply (wp_cumulative_time_receipt_linear with "TIME ⧖m"); [solve_ndisj|].
    iIntros "⧗". iApply wp_fupd.
    iDestruct (cumulative_time_receipt_mono (1 + S k0) with "⧗") as "⧗"; [lia|].
    iDestruct (cumulative_time_receipt_sep with "⧗") as "[⧗c ⧗k]".
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗c ⧖m") as "[_ £]";
      [solve_ndisj|].
    iMod (cumulative_persistent_time_receipt with "TIME ⧗k ⧖b") as "#⧖k"; [solve_ndisj|].
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iDestruct (lc_weaken (pctx_mode K 1 + (1 + (1 + dh*(g+1))))%nat with "£")
      as "[£k [£r £s]]"; [rewrite /advance_credits pctx_mode_add; nia|].
    iMod (lc_fupd_elim_laterN with "£k Gho1") as "Gho1".
    (* Resolve the old value. *)
    iDestruct (Rslv _ (⊤ ∖ (⊤ ∖ ↑Nllft ∖ ↑prophN ∖ ↑timeN ∖ ↑uniqN))
      with "LFT PROPH UNIQ TIME E Ghalf H2 Gho1") as "ToObs"; [set_solver|].
    iMod (lc_fupd_elim_later with "£r ToObs") as "ToObs".
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iDestruct (lc_step_fupdN_elim_later with "£s ToObs") as "ToObs".
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iMod (fupd_mask_mono with "ToObs") as "[Obs' H2]"; [solve_ndisj|].
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    (* Write the tag. *)
    have Hlen: length (ty_phys (Σ! tyl) y tid) = S (max_ty_size tyl) by rewrite ty_size_eq.
    destruct (ty_phys (Σ! tyl) y tid) as [|fv1 [|fv2 fvs]] eqn:Hph; [done|simpl in Hlen; lia|].
    simpl in Hlen.
    have Hrep: repeat ([]: list cell_id) (max_ty_size tyl) =
      [] :: repeat [] (max_ty_size tyl - 1).
    { destruct (max_ty_size tyl) as [|M]; [lia|]. by rewrite /= Nat.sub_0_r. }
    rewrite Hrep. iEval (rewrite !heap_mapsto_cloc_fancy_vec_cons) in "Pt1".
    iDestruct "Pt1" as "(Pt1 & Pt2 & Pt3)".
    iMod (mapsto_vec_untether_singleton (l', [[]]) fv1 _ ∅ with "[Pt1]")
      as (v₁ l₁ c₁) "[%Hl1 [Pt1 _]]".
    { by rewrite heap_complete_mapsto_fancy_singleton. }
    injection Hl1 as <- <-.
    iMod lc_zero as "£0".
    iApply (wp_write_na_guarded _ l' [] _ #i v₁ 0 True with "[Pt1 £0]"); [solve_ndisj| |].
    { iFrame "Pt1 £0". iApply guards_empty_cell. }
    iIntros "!> [Pt1 _]". iModIntro. wp_seq.
    (* Write the payload. *)
    wp_bind (pctx_expr K p).
    iMod lc_zero as "£0".
    iApply (wp_wand with "[Rest £0]").
    { iApply (wp_pctx_expr K (ty_size (Σ! tyl)) 1 x₀ ζm [] d g tid lr p True True 0
        with "[] £0 [] Rest").
      - rewrite /lr -heap_cloc_mapsto_empty. iApply guards_true.
      - iApply wp_wand; [by iApply wp_eval_path|]. by iIntros (?) "->". }
    iIntros (w) "(-> & _ & _ & Rest)". rewrite Hl'. wp_op.
    wp_bind q. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->".
    iMod (mapsto_vec_untether_singleton (l' +ₗ 1, [[]]) fv2 _ ∅ with "[Pt2]")
      as (v₂ l₂ c₂) "[%Hl2 [Pt2 _]]".
    { by rewrite heap_complete_mapsto_fancy_singleton. }
    injection Hl2 as <- <-.
    iMod lc_zero as "£0".
    iApply wp_fupd.
    iApply (wp_write_na_guarded _ (l' +ₗ 1) [] _ vb v₂ 0 True with "[Pt2 £0]");
      [solve_ndisj| |].
    { iFrame "Pt2 £0". iApply guards_empty_cell. }
    iIntros "!> [Pt2 _]".
    iMod (mapsto_vec_untether _ _ _ ∅ with "Pt3") as (vlc) "[Pt3 [%Hlen3 _]]".
    (* Close the place at the new value. *)
    set d'' := (db + k0) `max` d. set g'' := db `max` g.
    have Hdh'': db ≤ pctx_depth K d''. { rewrite pctx_depth_sub. lia. }
    iDestruct (ty_gho_own_depth_mono _ db db (pctx_depth K d'') g'' with "Gb") as "[Gb _]";
      [lia..|].
    iDestruct (pctx_own_depth_mono _ _ _ _ _ _ _ _ d'' g'' with "Rest") as "Rest"; [lia..|].
    iCombine "⧖ ⧖k" as "⧖D".
    iModIntro. iExists -[((l, pctx_set K x₀ (pinj i b, vlc)), ζm)]. iFrame "L I".
    iSplitR "Obs Obs'"; last first.
    { iCombine "Obs Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=> π [Hπ HΦ].
      by apply Hπ. }
    iSplit; [|done]. rewrite /tctx_elt_interp. iExists #l. iSplit; [done|].
    iExists (D `max` (S k0 + db)), d'', g''. iFrame "⧖D ⧗p Fr".
    iSplit; [done|]. iSplit; [iPureIntro; lia|].
    rewrite /ltype_own lty_pat_plug lty_rfn_plug pctx_get_set pctx_rfn_set // ltype_own_plug.
    rewrite Hl' /= Hrep. iFrame "Rest".
    iExists (pinj i b, vlc). iSplit; [done|]. rewrite /ofty_owned.
    rewrite (xsum_phys_pinj_1 _ _ _ vb); [|done|lia|lia].
    rewrite !heap_mapsto_cloc_fancy_vec_cons. iFrame "Pt1 Pt2 Pt3".
    iNext. rewrite xsum_gho_own_pinj. done.
  Qed.
  Lemma xsum_phys_pinj_0 {𝔄l} (tyl: typel 𝔄l) i u pad tid :
    ty_phys (tyl +!! i) u tid = [] → length pad = max_ty_size tyl →
    ty_phys (Σ! tyl) (pinj i u, pad) tid = FVal #i :: fmap FVal pad.
  Proof.
    intros Hph Hlen. rewrite /ty_phys /xsum_ty /= to_xsum_pinj Hph /=.
    apply pad_length'. by rewrite /= length_fmap Hlen.
  Qed.

  (** Assigning a unit variant [i] (a variant whose type is a subtype of [()], of size 0)
      to the leaf at the hole of [K] (a sum, at any path), as [type_sum_unit_instr]: the
      old value is resolved and the tag is written; the rest of the cells is the padding,
      which keeps its contents. *)
  Lemma type_sum_unit_oplace_instr {𝔄l 𝔄} E L I p n (K: pctx (Σ! 𝔄l) 𝔄) `{!PctxNoUniq K}
      (tyl: typel 𝔄l) (i: fin (length 𝔄l)) f Φ :
    subtype E L () (tyl +!! i) f → resolve E L (Σ! tyl) Φ →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K (OfTy (Σ! tyl))]
      (pctx_expr K p <-{Σ i} ())
      (λ _, +[p ◁ₗown{n} pctx_plug K (OfTy (Σ! tyl))])
      (λ post '-[x], λ mask π, Φ (pctx_get K x.1.2) π → ∀ pad,
        post -[((x.1.1, pctx_set K x.1.2 (pinj i (f ~~$ₛ ()), pad)), x.2)] mask π).
  Proof.
    iIntros (Subtype Rslv tid post mask iκs [x []])
      "#LFT #TIME #PROPH #UNIQ #E L I (Tp & _) Obs".
    iDestruct (Subtype with "L E") as "#(%Ssz & _ & #Sgho & _ & %Sphys & _)".
    destruct x as [[l x₀] ζm].
    rewrite /tctx_elt_interp.
    iDestruct "Tp" as (v Hp D d g) "(#⧖ & ⧗p & -> & %Hle & Fr & Own)".
    have ?: Closed [] (pctx_expr K p).
    { apply pctx_expr_closed. by eapply eval_path_closed. }
    rewrite /ltype_own lty_pat_plug lty_rfn_plug ltype_own_plug.
    iDestruct "Own" as "[L1 Rest]". iSimpl in "L1".
    iDestruct "L1" as (? ->) "[Pt1 Gho1]".
    iDestruct (pctx_own_in with "Rest") as %Hin.
    iDestruct (pctx_own_mode_le with "Rest") as %Hk.
    set y := pctx_get K x₀.
    destruct (oplace_loc_empty K (OfTy (Σ! tyl)) x₀ l) as [l' Hl'].
    set lr := (l, repeat [] (lty_size (pctx_plug K (OfTy (Σ! tyl))))).
    set dh := pctx_depth K d.
    have Hdh: dh ≤ d. { rewrite /dh pctx_depth_sub. lia. }
    (* The address of the hole. *)
    iMod lc_zero as "£0".
    wp_bind (pctx_expr K p).
    iApply (wp_wand with "[Rest £0]").
    { iApply (wp_pctx_expr K (ty_size (Σ! tyl)) 1 x₀ ζm [] d g tid lr p True True 0
        with "[] £0 [] Rest").
      - rewrite /lr -heap_cloc_mapsto_empty. iApply guards_true.
      - iApply wp_wand; [by iApply wp_eval_path|]. by iIntros (?) "->". }
    iIntros (w) "(-> & _ & _ & Rest)".
    change (lty_size (OfTy (Σ! tyl))) with (ty_size (Σ! tyl)) in Hl'.
    rewrite -/lr in Hl'. rewrite Hl'.
    wp_bind (_ <- _)%E.
    iApply wp_fupd. iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj|].
    iIntros "£ _".
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iDestruct (lc_weaken (pctx_mode K 1 + (1 + (1 + dh*(g+1))))%nat with "£")
      as "[£k [£r £s]]"; [rewrite /advance_credits pctx_mode_add; nia|].
    iMod (lc_fupd_elim_laterN with "£k Gho1") as "Gho1".
    (* Resolve the old value. *)
    iDestruct (Rslv _ (⊤ ∖ (⊤ ∖ ↑Nllft ∖ ↑prophN ∖ ↑timeN ∖ ↑uniqN))
      with "LFT PROPH UNIQ TIME E Ghalf H2 Gho1") as "ToObs"; [set_solver|].
    iMod (lc_fupd_elim_later with "£r ToObs") as "ToObs".
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iDestruct (lc_step_fupdN_elim_later with "£s ToObs") as "ToObs".
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iMod (fupd_mask_mono with "ToObs") as "[Obs' H2]"; [solve_ndisj|].
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    (* Write the tag. *)
    have Hlen: length (ty_phys (Σ! tyl) y tid) = S (max_ty_size tyl) by rewrite ty_size_eq.
    destruct (ty_phys (Σ! tyl) y tid) as [|fv1 fvs] eqn:Hph; [done|]. simpl in Hlen.
    rewrite /= heap_mapsto_cloc_fancy_vec_cons. iDestruct "Pt1" as "(Pt1 & Pt2)".
    iMod (mapsto_vec_untether_singleton (l', [[]]) fv1 _ ∅ with "[Pt1]")
      as (v₁ l₁ c₁) "[%Hl1 [Pt1 _]]".
    { by rewrite heap_complete_mapsto_fancy_singleton. }
    injection Hl1 as <- <-.
    iMod lc_zero as "£0".
    iApply (wp_write_na_guarded _ l' [] _ #i v₁ 0 True with "[Pt1 £0]"); [solve_ndisj| |].
    { iFrame "Pt1 £0". iApply guards_empty_cell. }
    iIntros "!> [Pt1 _]". iModIntro. wp_seq. iApply wp_fupd. wp_seq.
    iMod (mapsto_vec_untether _ _ _ ∅ with "Pt2") as (vlc) "[Pt2 [%Hlen2 _]]".
    have Hph0: ty_phys (tyl +!! i) (f ~~$ₛ ()) tid = [].
    { by rewrite -Sphys. }
    iModIntro. iExists -[((l, pctx_set K x₀ (pinj i (f ~~$ₛ ()), vlc)), ζm)]. iFrame "L I".
    iSplitR "Obs Obs'"; last first.
    { iCombine "Obs Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=> π [Hπ HΦ].
      by apply Hπ. }
    iSplit; [|done]. rewrite /tctx_elt_interp. iExists #l. iSplit; [done|].
    iExists D, d, g. iFrame "⧖ ⧗p Fr".
    iSplit; [done|]. iSplit; [done|].
    rewrite /ltype_own lty_pat_plug lty_rfn_plug pctx_get_set pctx_rfn_set // ltype_own_plug.
    rewrite Hl' /=. iFrame "Rest".
    iExists (pinj i (f ~~$ₛ ()), vlc). iSplit; [done|]. rewrite /ofty_owned.
    rewrite (xsum_phys_pinj_0 _ _ _ vlc); [|done|lia].
    rewrite /= heap_mapsto_cloc_fancy_vec_cons. iFrame "Pt1 Pt2".
    iApply bi.laterN_intro. rewrite xsum_gho_own_pinj.
    iDestruct ("Sgho" $! () dh g tid with "[]") as "[$ _]"; done.
  Qed.

End typing.
