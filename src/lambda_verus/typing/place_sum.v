(** * Sum places

  A leaf [OfTy (Σ! tyl)] of a place (rooted at a unique borrow, [p ◁ₗ{κ} lt], or at an
  owned location, [p ◁ₗown{n} lt]) holds a sum. Reading its discriminant
  ([type_case_place], [type_case_place_root], [type_case_oplace]) branches on the
  variant [i] of its value and, in branch [i], unfolds the leaf into a _sum place_ at
  variant [i], [SumLty tyl i (OfTy (tyl +!! i))] (whose payload is the leaf of the
  variant; the specification of the branch knows the variant). The payload is reached
  by the context step [PSum tyl i w K] (offset 1, [lpath.v]), so that the general rules
  for unfolding, reborrowing, shared borrows, reading, writing and unblocking leaves,
  and for dropping a place while its leaves are blocked, apply to the payload and its
  subplaces. A sum place is folded back unconditionally ([tctx_fold_place_sum],
  [tctx_fold_oplace_sum]). A leaf of an owned place can be assigned a whole new variant
  with a payload of size 1 ([type_sum_assign_oplace_instr]) or a unit variant
  ([type_sum_unit_oplace_instr]); so can a leaf of a place rooted at a unique borrow
  ([type_sum_assign_place_instr], keeping the type of the leaf).

  Below the root of a place rooted at a unique borrow, the case analysis switches the
  body of the borrow to the new node ([cpd_rebody]); at the root, it unfolds the borrow
  into a compound place ([cpd_unfold_uniq]). *)

From iris.proofmode Require Import proofmode.
From lrust.lang Require Import proofmode.
From lrust.typing Require Export type ltype lpath place place_own sum.
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

  (** A sum place whose payload is the leaf of its variant is folded back into a leaf
      holding the sum. (The converse is done by reading the discriminant,
      [type_case_place].) *)
  Lemma tctx_fold_place_sum {𝔄l 𝔄} E L p κ (K: pctx (Σ! 𝔄l) 𝔄) (tyl: typel 𝔄l) i :
    lctx_lft_alive E L κ → pctx_simple K →
    tctx_incl E L +[p ◁ₗ{κ} pctx_plug K (SumLty tyl i (OfTy (tyl +!! i)))]
      +[p ◁ₗ{κ} pctx_plug K (OfTy (Σ! tyl))] (λ post '-[x], post -[x]).
  Proof.
    intros Alv HsK. apply tctx_place_change_hole'; [done|done|done| | |done| | | |].
    - by rewrite lty_size_sum_ofty.
    - by rewrite lty_fold_sum_ofty.
    - intros ?; simpl; set_solver.
    - intros ?????. apply prfn_rsv_in.
    - intros y ζm q d g tid l. iIntros "H !>". by iApply sum_ofty_own_rfn.
    - iIntros (κ' ξi' y ζm' d g tid l G ?) "LFT PROPH UNIQ Gκ G Own".
      rewrite -(lty_fold_sum_ofty tyl i).
      iApply (cpd_fold_uniq (SumLty tyl i (OfTy (tyl +!! i))) with "LFT PROPH UNIQ Gκ G Own");
        [done| |solve_ndisj].
      iIntros (d' g') "N". iDestruct (sum_ofty_own_rfn 0 with "N") as "N".
      rewrite lty_fold_sum_ofty /ltype_own /= /ofty_owned. iDestruct "N" as (? ->) "[$ $]".
      done.
  Qed.

  (** ** Reading the discriminant *)

  Lemma big_sepN_lookup n (Φ: fin n → iProp Σ) i : ([∗ nat] j < n, Φ j) -∗ Φ i.
  Proof.
    iIntros "All". iInduction n as [|n] "IH"; [by inv_fin i|]=>/=.
    iDestruct "All" as "[Φ All]". inv_fin i; [done|]=> i. by iApply ("IH" $! (λ j, Φ (FS j))).
  Qed.

  (** Reading the discriminant of the leaf at the hole of [K] (a sum, below the root and
      below no owned pointer): the borrow of the place is opened around the read, and
      closed with the leaf unfolded into a sum place at the variant [i] of its value,
      whose payload is the leaf of the variant (the body of the borrow is switched to
      the new node, [cpd_rebody]); the program continues with branch [i]. At the root of
      a place, the rules for unique borrows of sums apply ([type_case_uniq], after
      [tctx_place_to_uniq]). *)
  Lemma type_case_place {𝔄l 𝔄 𝔅l 𝔇} E L I (C: cctx 𝔇) p κ (K: pctx (Σ! 𝔄l) 𝔄)
      (tyl: typel 𝔄l) (T: tctx 𝔅l) el el' trl :
    IntoPlistc el el' → lctx_lft_alive E L κ → pctx_nonempty K → pctx_noderef K →
    pctx_simple K →
    ([∗ nat] i < length 𝔄l, typed_body E L I C
      (p ◁ₗ{κ} pctx_plug K (SumLty tyl i (OfTy (tyl +!! i))) +:: T) (el' -!! i) (trl -!! i)) -∗
    typed_body E L I C (p ◁ₗ{κ} pctx_plug K (OfTy (Σ! tyl)) +:: T)
      (case: !(p +ₗ #(pctx_off K)) of el)
      (λ post '(x -:: cl),
        let 'xinj i _ := to_xsum (pctx_get K (uniq_bor_current (place_bor x))).1 in
        (trl -!! i) post (x -:: cl))%type.
  Proof.
    move=> -> Alv HK HKd HsK. iIntros "el".
    iIntros (tid [x xl] mask post iκs) "#LFT #TIME #PROPH #UNIQ #E L I C /=[Tp T] #Obs".
    destruct x as [[[[[[l x₀] ξi] d'] g'] idx] ζm].
    rewrite /tctx_elt_interp.
    iDestruct "Tp" as (v Hp) "(%d0 & #⧖0 & ⧗p & -> & %Hle & #Incl & #PtBase & Own)".
    (* The variant of the value of the leaf. *)
    remember (pctx_get K x₀) as y eqn:Hy. destruct y as [s pad].
    destruct (to_xsum s) as [j a] eqn:Hj.
    have Hs: s = pinj j a. { by rewrite -(semi_iso' to_xsum of_xsum s) Hj. }
    subst s.
    wp_bind (p +ₗ #(pctx_off K))%E.
    iApply wp_wand; [iApply (wp_eval_path _ _ #(l.1 +ₗ pctx_off K)); by rewrite /= Hp|].
    iIntros (?) "->".
    wp_bind (!(LitV (l.1 +ₗ pctx_off K)%L))%E.
    iApply (wp_persistent_time_receipt with "TIME ⧖0"); [solve_ndisj|].
    iIntros "£ #⧖S". iApply wp_fupd.
    iDestruct (Alv with "L E") as "#Alv".
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iDestruct (guards_transitive with "Ghalf Alv") as "#Hκ".
    iDestruct (lc_weaken (1 + 3 * (d0 + 1))%nat with "£") as "[£a £r]";
      [rewrite /advance_credits; nia|].
    rewrite /ltype_own ltype_own_cp_uniq_plug //.
    iMod (cpd_rebody with "LFT PROPH UNIQ Hκ H1 Own") as (κp) "(#Inclp & #Ok & Upd & Close)";
      [solve_ndisj|].
    iMod (lc_fupd_elim_later with "£a Upd") as "Upd".
    iMod (guarded_upd_run with "[] H2 Upd") as "(H2 & #⧖' & N)";
      [rewrite /lazyE; solve_ndisj| |].
    { iApply (guards_transitive with "Hκ Incl"). }
    rewrite lty_pat_plug lty_rfn_plug ltype_own_plug pctx_mode_noderef // pctx_depth_noderef //.
    rewrite -Hy.
    iDestruct "N" as "[L1 Rest]". iSimpl in "L1".
    iDestruct "L1" as (? ->) "[Pt1 Gho1]".
    set lK := pctx_loc K (ty_size (Σ! tyl)) x₀ l.
    iEval (rewrite split_pt_xsum_cells'') in "Pt1". iDestruct "Pt1" as "(Tag & Pay & Pad)".
    (* Read the discriminant. *)
    have Hl0: (l.1 +ₗ pctx_off K) = lK.1 by rewrite /lK pctx_loc_fst.
    rewrite Hl0.
    iApply (wp_read_na_guarded_cells_singleton _ (cloc_take lK 1).1 (cloc_take lK 1).2
      (fractional.half γh ∗ cloc_take lK 1 #↦∗ [ #j ]) #j (d0 + 1)
      with "[H2 Tag £r]"); [solve_ndisj| |].
    { iFrame "H2 Tag £r". iApply guard_cloc_combine.
      - iApply guards_weaken_lhs_sep_l. iApply (guards_transitive_right with "Hκ [PtBase]").
        iDestruct (pctx_loc_guard K (ty_size (Σ! tyl)) x₀ with "PtBase") as "G".
        rewrite (heap_cloc_mapsto_emp_vec_app lK 1).
        iApply (guards_weaken_rhs_sep_l with "G").
      - iApply (lguards_weaken_later _ _ _ 0); [lia|iApply guards_weaken_sep_r]. }
    iIntros "!> [H2 Tag]".
    (* Close the borrow with the sum place at the hole. *)
    set lt' := SumLty tyl j (OfTy (tyl +!! j)).
    rewrite (lty_fold_plug_eq' K (OfTy (Σ! tyl)) lt'); [|symmetry; apply lty_fold_sum_ofty].
    iMod ("Close" $! (pctx_pat K (PatSum PatLeaf)) (pctx_rfn K x₀ ζm [] (prfn_sum j (inl (PlaceIn a)) pad))
      d' g' with "[%] [] [] [Tag Pay Pad Gho1 Rest]") as "[Own H1]".
    { intros ζl. apply pctx_rfn_rsv_mono; [done|]. intros _. rewrite prfn_rsv_sum.
      apply prfn_rsv_in. }
    { iIntros "!>" (p2 r2 d2 g2) "Ok2 ⧖ N".
      iApply (ltype_owned_leaf_node with "LFT PROPH UNIQ Ok2 ⧖ N"); [by apply pctx_plug_cpd|by apply lty_simple_plug]. }
    { iNext. iApply (pat_ok_plug with "Ok"). by rewrite /pat_ok. }
    { iNext. iApply guarded_upd_intro. iModIntro. iFrame "⧖'".
      rewrite ltype_own_plug pctx_mode_noderef // pctx_depth_noderef // lty_size_sum_ofty.
      iFrame "Rest". iApply (sum_ofty_unfold_own 0). iExists (pinj j a, pad). iSplit; [done|].
      rewrite /ofty_owned split_pt_xsum_cells''. by iFrame. }
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|]. iModIntro.
    wp_case. { split; [lia|]. by rewrite Nat2Z.id -vlookup_lookup plistc_to_vec_lookup. }
    iDestruct (big_sepN_lookup _ _ j with "el") as "el".
    iApply ("el" $! _ (((l, x₀, ξi, d', g', idx), ζm) -:: xl)
      with "LFT TIME PROPH UNIQ E L I C [-] []"); last first.
    { iApply proph_obs_impl; [|done]=>/= ?. by rewrite ?to_xsum_pinj. }
    iFrame "T". iExists #(l.1). iSplit; [done|]. iExists d0. iFrame "⧖0 Incl PtBase".
    rewrite !lty_nblk_plug /=. iFrame "⧗p". iSplit; [done|]. iSplit; [done|].
    rewrite /ltype_own ltype_own_cp_uniq_plug // lty_pat_plug lty_rfn_plug -Hy lty_rfn_sum_in.
    iExact "Own".
  Qed.

  (** At the root of a place: the body of the borrow is switched to the node of the sum
      place at the variant [i] of the value ([cpd_unfold_uniq]), and opened around the
      read of the discriminant (and closed at the same state). *)
  Lemma type_case_place_root {𝔄l 𝔅l 𝔇} E L I (C: cctx 𝔇) p κ (tyl: typel 𝔄l) (T: tctx 𝔅l)
      el el' trl :
    IntoPlistc el el' → lctx_lft_alive E L κ →
    ([∗ nat] i < length 𝔄l, typed_body E L I C
      (p ◁ₗ{κ} SumLty tyl i (OfTy (tyl +!! i)) +:: T) (el' -!! i) (trl -!! i)) -∗
    typed_body E L I C (p ◁ₗ{κ} OfTy (Σ! tyl) +:: T) (case: !p of el)
      (λ post '(x -:: cl), let 'xinj i _ := to_xsum (uniq_bor_current (place_bor x)).1 in
        (trl -!! i) post (x -:: cl))%type.
  Proof.
    move=> -> Alv. iIntros "el".
    iIntros (tid [x xl] mask post iκs) "#LFT #TIME #PROPH #UNIQ #E L I C /=[Tp T] #Obs".
    destruct x as [[[[[[l [s pad]] ξi] d'] g'] idx] ζm].
    rewrite /tctx_elt_interp.
    iDestruct "Tp" as (v Hp) "(%d0 & #⧖0 & ⧗p & -> & %Hle & #Incl & #PtBase & Own)".
    destruct (to_xsum s) as [j a] eqn:Hj.
    have Hs: s = pinj j a. { by rewrite -(semi_iso' to_xsum of_xsum s) Hj. }
    subst s.
    wp_bind p. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->".
    wp_bind (!(LitV l.1))%E.
    iApply (wp_persistent_time_receipt with "TIME ⧖0"); [solve_ndisj|].
    iIntros "£ #⧖S". iApply wp_fupd.
    iDestruct (Alv with "L E") as "#Alv".
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iDestruct (guards_transitive with "Ghalf Alv") as "#Hκ".
    iDestruct (lc_weaken (1 + 3 * (d0 + 1))%nat with "£") as "[£a £r]";
      [rewrite /advance_credits; nia|].
    (* Switch the body to the node of the sum place. *)
    set lt := SumLty tyl j (OfTy (tyl +!! j)).
    iEval (rewrite -(lty_fold_sum_ofty tyl j)) in "Own".
    iMod (cpd_unfold_uniq lt _ _ _ (prfn_sum j (inl (PlaceIn a)) pad)
      with "LFT PROPH UNIQ Hκ H1 Own") as "[Own H1]"; [done|done|done| | | |solve_ndisj|].
    { rewrite prfn_rsv_sum. apply prfn_rsv_in. }
    { intros π. rewrite prfn_den_sum /= prfn_den_in. by rewrite psum_map1_pinj. }
    { iIntros (d g) "[Gho Pt] !>". rewrite lty_fold_sum_ofty.
      iApply (sum_ofty_unfold_own 0). rewrite /ltype_own /= /ofty_owned.
      iExists _. by iFrame. }
    (* Read the discriminant. *)
    rewrite /ltype_own ltype_own_cp_uniq_cpd //.
    iMod (cpd_acc with "LFT PROPH UNIQ Hκ H1 Own") as (κp) "(#Inclp & #Ok & Upd & Close)";
      [solve_ndisj|].
    iMod (lc_fupd_elim_later with "£a Upd") as "Upd".
    iMod (guarded_upd_run with "[] H2 Upd") as "(H2 & #⧖' & N)";
      [rewrite /lazyE; solve_ndisj| |].
    { iApply (guards_transitive with "Hκ"). by rewrite lty_fold_sum_ofty. }
    iDestruct (sum_ofty_unfold_own 0 with "N") as "N".
    rewrite /ltype_own /=. iDestruct "N" as (? ->) "[Pt1 Gho1]".
    iEval (rewrite split_pt_xsum_cells'') in "Pt1". iDestruct "Pt1" as "(Tag & Pay & Pad)".
    iApply (wp_read_na_guarded_cells_singleton _ (cloc_take l 1).1 (cloc_take l 1).2
      (fractional.half γh ∗ cloc_take l 1 #↦∗ [ #j ]) #j (d0 + 1)
      with "[H2 Tag £r]"); [solve_ndisj| |].
    { iFrame "H2 Tag £r". iApply guard_cloc_combine.
      - iApply guards_weaken_lhs_sep_l. iApply (guards_transitive_right with "Hκ [PtBase]").
        rewrite (heap_cloc_mapsto_emp_vec_app l 1).
        iApply (guards_weaken_rhs_sep_l with "PtBase").
      - iApply (lguards_weaken_later _ _ _ 0); [lia|iApply guards_weaken_sep_r]. }
    iIntros "!> [H2 Tag]".
    iMod ("Close" $! (PatSum PatLeaf) (prfn_sum j (inl (PlaceIn a)) pad) d' g' [] 1%Qp True%I
      with "[] [] [Tag Pay Pad Gho1]") as "(Own & H1 & _)".
    { iPureIntro. intros ζl _. rewrite /prfn_sum /= psum_all_pinj_eq. apply prfn_rsv_in. }
    { done. }
    { iIntros "_". iModIntro. iSplitR; [done|]. iSplitL; [|done].
      iNext. iApply guarded_upd_intro. iModIntro. iFrame "⧖'".
      iApply (sum_ofty_unfold_own 0). iExists (pinj j a, pad). iSplit; [done|].
      rewrite /ofty_owned split_pt_xsum_cells''. by iFrame. }
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|]. iModIntro.
    wp_case. { split; [lia|]. by rewrite Nat2Z.id -vlookup_lookup plistc_to_vec_lookup. }
    iDestruct (big_sepN_lookup _ _ j with "el") as "el".
    iApply ("el" $! _ (((l, (pinj j a, pad), ξi, d', g', idx), ζm) -:: xl)
      with "LFT TIME PROPH UNIQ E L I C [-] []"); last first.
    { iApply proph_obs_impl; [|done]=>/= ?. by rewrite ?to_xsum_pinj. }
    iFrame "T". iExists #(l.1). iSplit; [done|]. iExists d0. iFrame "⧖0 PtBase ⧗p".
    iSplit; [done|]. iSplit; [done|]. iSplit; [by rewrite lty_fold_sum_ofty|].
    rewrite /ltype_own ltype_own_cp_uniq_cpd // lty_rfn_sum_in. iExact "Own".
  Qed.

  (** * Places rooted at an owned location *)

  Lemma tctx_fold_oplace_sum {𝔄l 𝔄} E L p n (K: pctx (Σ! 𝔄l) 𝔄) (tyl: typel 𝔄l) i :
    tctx_incl E L +[p ◁ₗown{n} pctx_plug K (SumLty tyl i (OfTy (tyl +!! i)))]
      +[p ◁ₗown{n} pctx_plug K (OfTy (Σ! tyl))] (λ post '-[x], post -[x]).
  Proof.
    apply tctx_oplace_change_hole; [by rewrite lty_size_sum_ofty|done|].
    iIntros (y ζm q d g tid l) "H !>". by iApply sum_ofty_own_rfn.
  Qed.

  (** Reading the discriminant of the leaf at the hole of [K] (a sum, at any path): the
      leaf is unfolded into a sum place at the variant [i] of its value, and the program
      continues with branch [i]. *)
  Lemma type_case_oplace {𝔄l 𝔄 𝔅l 𝔇} E L I (C: cctx 𝔇) p n (K: pctx (Σ! 𝔄l) 𝔄)
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
    rewrite !lty_nblk_plug /= (lty_size_plug_eq K _ (OfTy (Σ! tyl))); [|apply lty_size_sum_ofty].
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
  Lemma type_sum_assign_oplace_instr {𝔄l 𝔄} E L I p q n (K: pctx (Σ! 𝔄l) 𝔄)
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
  Lemma type_sum_unit_oplace_instr {𝔄l 𝔄} E L I p n (K: pctx (Σ! 𝔄l) 𝔄)
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

  (** Assigning a variant [i] with a payload of size 1 to the leaf at the hole of [K]
      (nonempty, at any path) of a place rooted at a unique borrow; the type of the leaf
      does not change. The borrow of the place is opened ([cpd_acc]) for the whole
      instruction (the address of the leaf is computed twice); the old value is resolved;
      the cells after the payload are the padding, which keeps its contents. *)
  Lemma type_sum_assign_place_instr {𝔄l 𝔄} E L I p q κ (K: pctx (Σ! 𝔄l) 𝔄)
      (tyl: typel 𝔄l) (i: fin (length 𝔄l)) Φ :
    lctx_lft_alive E L κ → pctx_nonempty K → ty_size (tyl +!! i) = 1%nat →
    resolve E L (Σ! tyl) Φ →
    typed_instr E L I +[p ◁ₗ{κ} pctx_plug K (OfTy (Σ! tyl)); q ◁ tyl +!! i]
      (pctx_expr K p <-{Σ i} q)
      (λ _, +[p ◁ₗ{κ} pctx_plug K (OfTy (Σ! tyl))])
      (λ post '-[x; b], λ mask π, Φ (pctx_get K (uniq_bor_current (place_bor x))) π →
        ∀ pad (x': ~~ (placeₛ 𝔄)),
        uniq_bor_loc (place_bor x') = uniq_bor_loc (place_bor x) →
        uniq_bor_current (place_bor x') =
          pctx_set K (uniq_bor_current (place_bor x)) (pinj i b, pad) →
        uniq_bor_future (place_bor x') π = uniq_bor_future (place_bor x) π →
        place_ζis x' = place_ζis x → post -[x'] mask π).
  Proof.
    iIntros (Alv HK Hsz Rslv tid post mask iκs [x [b []]])
      "#LFT #TIME #PROPH #UNIQ #E L I (Tp & Tb & _) Obs".
    destruct x as [[[[[[l x₀] ξi] d'] g'] idx] ζm].
    rewrite /tctx_elt_interp.
    iDestruct "Tp" as (v Hp) "(%d0 & #⧖0 & ⧗p & -> & %Hle & #Incl & #PtBase & Own)".
    iDestruct "Tb" as (vb db Hpb) "(#⧖b & Gb & %Phys)".
    have ?: Closed [] (pctx_expr K p).
    { apply pctx_expr_closed. by eapply eval_path_closed. }
    have ?: Closed [] q by eapply eval_path_closed.
    have HM: 1 ≤ max_ty_size tyl.
    { rewrite -Hsz. apply (max_hlist_with_ge (λ _, ty_size) tyl i). }
    set k := pctx_mode K 0.
    (* The first step gives credits and cumulative time receipts. *)
    iCombine "⧖0 ⧖b" as "⧖m".
    iApply (wp_cumulative_time_receipt_linear with "TIME ⧖m"); [solve_ndisj|].
    iIntros "⧗". iApply wp_fupd.
    set M := d0 `max` db.
    iDestruct (Alv with "L E") as "#Alv".
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iDestruct (guards_transitive with "Ghalf Alv") as "#Hκ".
    rewrite /ltype_own ltype_own_cp_uniq_plug //.
    iMod (cpd_acc with "LFT PROPH UNIQ Hκ H1 Own") as (κp) "(#Inclp & #Ok & Upd & Close)";
      [solve_ndisj|].
    iDestruct (cumulative_time_receipt_sep 1 (S M) with "⧗") as "[⧗c ⧗k]".
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗c ⧖m") as "[#⧖S £]";
      [solve_ndisj|].
    iDestruct (lc_weaken (1 + 3 * (d0 + 1) * M + 3 * (d0 + 1) * M + M + (1 + (1 + M*(M+1))) +
      3 * (d0 + 1) + 3 * (d0 + 1))%nat with "£")
      as "[[[[[[£a £p] £p'] £k] [£r £s]] £w1] £w2]"; [rewrite /advance_credits; nia|].
    iMod (lc_fupd_elim_later with "£a Upd") as "Upd".
    iMod (guarded_upd_run with "[] H2 Upd") as "(H2 & #⧖' & N)";
      [rewrite /lazyE; solve_ndisj| |].
    { iApply (guards_transitive with "Hκ Incl"). }
    rewrite lty_pat_plug lty_rfn_plug ltype_own_plug.
    iDestruct "N" as "[L1 Rest]". iSimpl in "L1".
    iDestruct "L1" as (? ->) "[Pt1 Gho1]".
    iDestruct (pctx_own_mode_le with "Rest") as %Hk.
    iDestruct (pctx_own_in with "Rest") as %Hin.
    set y := pctx_get K x₀. set lK := pctx_loc K (ty_size (Σ! tyl)) x₀ l.
    set dh := pctx_depth K d'.
    have Hdh: dh ≤ d'. { rewrite /dh pctx_depth_sub. lia. }
    have Hk': k ≤ M by rewrite /M /k; lia.
    iAssert (fractional.half γh &&{↑NllftG; d0 + 1}&&> lK #↦∗_)%I as "#GlK".
    { iApply (pctx_loc_guard with "[]"). iApply (guards_transitive_right with "Hκ PtBase"). }
    (* The address of the hole. *)
    wp_bind (pctx_expr K p).
    iApply (wp_wand with "[Rest H2 £p]").
    { iApply (wp_pctx_expr_mask _ K (ty_size (Σ! tyl)) 0 x₀ ζm [] d' g' tid l p
        (fractional.half γh) True (d0 + 1) with "[] [£p] [H2] Rest"); [solve_ndisj| | |].
      - iApply (guards_transitive_right with "Hκ PtBase").
      - iApply (lc_weaken with "£p"). rewrite -/k. nia.
      - iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->". by iFrame. }
    iIntros (w) "(-> & _ & H2 & Rest)".
    (* Resolve the old value. *)
    iMod (lc_fupd_elim_laterN with "[£k] Gho1") as "Gho1".
    { iApply (lc_weaken with "£k"). lia. }
    iDestruct (ty_gho_own_depth_mono _ dh g' M M with "Gho1") as "[Gho1 _]"; [lia..|].
    iDestruct (Rslv _ (⊤ ∖ (⊤ ∖ ↑Nllft ∖ ↑prophN ∖ ↑timeN ∖ ↑uniqN))
      with "LFT PROPH UNIQ TIME E Ghalf H2 Gho1") as "ToObs"; [set_solver|].
    iMod (lc_fupd_elim_later with "£r ToObs") as "ToObs".
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iDestruct (lc_step_fupdN_elim_later with "£s ToObs") as "ToObs".
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iMod (fupd_mask_mono with "ToObs") as "[Obs' H2]"; [solve_ndisj|].
    (* Split the cells: tag, payload, padding. *)
    have Hlen: length (ty_phys (Σ! tyl) y tid) = S (max_ty_size tyl) by rewrite ty_size_eq.
    destruct (ty_phys (Σ! tyl) y tid) as [|fv1 [|fv2 fvs]] eqn:Hph; [done|simpl in Hlen; lia|].
    simpl in Hlen.
    iDestruct (heap_cloc_mapsto_fancy_vec_length_eq with "Pt1") as %HlenK.
    destruct lK as [lK1 [|c1 [|c2 cs]]] eqn:HlK; [done|done|].
    iEval (rewrite !heap_mapsto_cloc_fancy_vec_cons) in "Pt1".
    iDestruct "Pt1" as "(Pt1 & Pt2 & Pt3)".
    iEval (rewrite !heap_mapsto_cloc_emp_cons) in "GlK".
    iMod (mapsto_vec_untether_singleton (lK1, [c1]) fv1 _ ∅ with "[Pt1]")
      as (v₁ l₁ c₁) "[%Hl1 [Pt1 _]]".
    { by rewrite heap_complete_mapsto_fancy_singleton. }
    injection Hl1 as <- <-.
    (* Write the tag. *)
    rewrite -/lK HlK /=. wp_bind (_ <- _)%E.
    iApply (wp_write_na_guarded _ lK1 c1 _ #i v₁ (d0 + 1) (fractional.half γh)
      with "[H2 Pt1 £w1]"); [solve_ndisj| |].
    { iFrame "H2 Pt1 £w1". iApply (guards_weaken_rhs_sep_l with "GlK"). }
    iIntros "!> [Pt1 H2]". wp_seq.
    (* Write the payload. *)
    wp_bind (pctx_expr K p).
    iApply (wp_wand with "[Rest H2 £p']").
    { iApply (wp_pctx_expr_mask _ K (ty_size (Σ! tyl)) 0 x₀ ζm [] d' g' tid l p
        (fractional.half γh) True (d0 + 1) with "[] [£p'] [H2] Rest"); [solve_ndisj| | |].
      - iApply (guards_transitive_right with "Hκ PtBase").
      - iApply (lc_weaken with "£p'"). rewrite -/k. nia.
      - iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->". by iFrame. }
    iIntros (w) "(-> & _ & H2 & Rest)". rewrite -/lK HlK /=. wp_op.
    wp_bind q. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->".
    iMod (mapsto_vec_untether_singleton (lK1 +ₗ 1, [c2]) fv2 _ ∅ with "[Pt2]")
      as (v₂ l₂ c₂) "[%Hl2 [Pt2 _]]".
    { by rewrite heap_complete_mapsto_fancy_singleton. }
    injection Hl2 as <- <-.
    iApply (wp_write_na_guarded _ (lK1 +ₗ 1) c2 _ vb v₂ (d0 + 1) (fractional.half γh)
      with "[H2 Pt2 £w2]"); [solve_ndisj| |].
    { iFrame "H2 Pt2 £w2". iDestruct (guards_weaken_rhs_sep_r with "GlK") as "GlK'".
      iApply (guards_weaken_rhs_sep_l with "GlK'"). }
    iIntros "!> [Pt2 H2]".
    iMod (mapsto_vec_untether _ _ _ ∅ with "Pt3") as (vlc) "[Pt3 [%Hlen3 _]]".
    (* Close the place at the new value. *)
    iDestruct (cumulative_time_receipt_mono (S k) with "⧗k") as "⧗k"; [lia|].
    iMod (cumulative_persistent_time_receipt with "TIME ⧗k ⧖b") as "#⧖k"; [solve_ndisj|].
    set d'' := (db + k) `max` d'. set g'' := db `max` g'.
    have Hdh'': db ≤ pctx_depth K d''. { rewrite pctx_depth_sub. lia. }
    iDestruct (ty_gho_own_depth_mono _ db db (pctx_depth K d'') g'' with "Gb") as "[Gb _]";
      [lia..|].
    iDestruct (pctx_own_depth_mono _ _ _ _ _ _ _ _ d'' g'' with "Rest") as "Rest"; [lia..|].
    iAssert (⧖(S d'' `max` g''))%I as "#⧖''".
    { iCombine "⧖' ⧖k" as "⧖". iApply (persistent_time_receipt_mono with "⧖"). lia. }
    iMod ("Close" $! (pctx_pat K PatLeaf) (pctx_rfn K x₀ ζm [] (inl (PlaceIn (𝔄:=Σ! 𝔄l) (pinj i b, vlc))))
      d'' g'' [] 1%Qp True%I with "[] [] [Pt1 Pt2 Pt3 Gb Rest]") as "(Own & H1 & _)".
    { iPureIntro. intros ζl Hr. eapply pctx_rfn_rsv; [|exact Hr|apply prfn_rsv_in].
      set_solver. }
    { done. }
    { iIntros "_". iModIntro. iSplitR.
      { iNext. iApply (pat_ok_plug with "Ok"). iApply pat_ok_leaf. }
      iSplitL; [|done].
      iNext. iApply guarded_upd_intro. iModIntro. iFrame "⧖''".
      rewrite ltype_own_plug. iFrame "Rest".
      iExists (pinj i b, vlc). iSplit; [done|]. rewrite /ofty_owned.
      rewrite (xsum_phys_pinj_1 _ _ _ vb); [|done|lia|lia].
      rewrite (_: pctx_loc K (lty_size (OfTy (Σ! tyl))) x₀ l = (lK1, c1 :: c2 :: cs));
        [|exact HlK].
      rewrite !heap_mapsto_cloc_fancy_vec_cons. iFrame "Pt1 Pt2 Pt3".
      iApply bi.laterN_intro. by rewrite xsum_gho_own_pinj. }
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "$"; [solve_ndisj|].
    iCombine "⧖0 ⧖''" as "⧖D".
    iModIntro. iExists -[((l, pctx_set K x₀ (pinj i b, vlc), ξi, d'', g'', idx), ζm)].
    iFrame "I". iSplitR "Obs Obs'".
    { iSplit; [|done]. rewrite /tctx_elt_interp. iExists #(l.1). iSplit; [done|].
      iExists (d0 `max` (S d'' `max` g'')). iFrame "⧖D ⧗p Incl".
      iSplit; [done|]. iSplit; [iPureIntro; lia|].
      iSplitR. { iApply (lguards_weaken_later with "PtBase"). lia. }
      rewrite /ltype_own ltype_own_cp_uniq_plug // lty_pat_plug lty_rfn_plug pctx_get_set
        pctx_rfn_set //. }
    iCombine "Obs Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=> π [Hπ HΦ].
    apply (Hπ HΦ vlc); [done|done| |done].
    rewrite !uniq_bor_future_eq. apply (uniq_prvar_app_irrel _ x₀).
  Qed.
End typing.
