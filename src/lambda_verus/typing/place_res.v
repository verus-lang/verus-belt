(** * Resolving owned places to a readable state

  Resolving a place ([p ◁ₗown{n} lt], [place_own.v]) gives up the unique borrows of its
  owned part (the part below no unique borrow: fields, sums, owned pointers) and learns
  the observations of its leaves, but keeps the place readable: the result is a place
  that can be read (and shared) but not written. See [~/verus-belt-phase3-design.md],
  section "Resolve to a readable state".

  ** Resolved place types ([typing/ltype.v])

  - [OfRes ty]: a leaf whose value has been resolved ([resolve_keep] of [type.v]); it
    holds the cells and the resolved ownership [ty_gho_res] of the value. For a type
    without unique borrows ([ResOwn]) this is the ownership, so [OfRes ty] is converted
    back to [OfTy ty]; [OfRes (&uniq{κ} ty)] is re-read as [ShrLty (OfTy ty) κ] (the
    referent shared at [κ], retyping the leaf; an instruction, since a borrow resolved
    by the generic [resolve_keep_just] is only resolved then, with κ alive); owned
    pointers and products are unfolded structurally, sums by case analysis.
  - [ResUniqLty lt κ]: an unfolded unique borrow whose prophecy variable has been
    (pre-)resolved: its referent is a _view_ at [κ] ([lty_view]): the unblocked leaves
    are shared at [κ], the blocked leaves keep their inheritances (in borrows at [κ]) and
    are shared at [κ] once they are unblocked; nested unique borrows at [κ'] are views at
    [κ ⊓ κ'] (they are not resolved: their lenders keep them).

  This file: (a) the conversions of resolved leaves; (b) case analysis on resolved sums
  and folding them back. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From lrust.lang Require Import proofmode.
From lrust.typing Require Export type ltype lpath pctx_acc place_own.
From lrust.typing Require Import type_context programs programs_util lft_contexts
  uniq_util uniq_bor product own shr_bor sum type_sum freeable_util place_shr
  place_resolve place_puniq place_sum place_pshr.
From lrust.util Require Import proph_bor.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

(** * Resolved leaves *)

Section res_leaf.
  Context `{!typeG Σ}.

  (** A resolved leaf whose resolved ownership is its ownership is an unresolved leaf. *)
  Lemma res_leaf_to_ofty m {𝔄} (ty: type 𝔄) `{!ResOwn ty} lr d g tid l :
    ltype_own (Owned m) (OfRes ty) (inl lr) d g tid l ⊢
    ltype_own (Owned m) (OfTy ty) (inl lr) d g tid l.
  Proof.
    rewrite /ltype_own /= /res_leaf /leaf_owned_s /leaf_owned /ofty_owned.
    iIntros "(%x & Rel & Pt & Gho)". iExists x. iFrame "Rel Pt". iNext.
    iDestruct "Gho" as (d' g' [??]) "Gho". rewrite res_own.
    iDestruct (ty_gho_own_depth_mono _ d' g' d g with "Gho") as "[$ _]"; lia.
  Qed.

  (** The resolved ownership of a pair. *)
  Lemma res_leaf_prod_unfold m {𝔄 𝔅} (ty1: type 𝔄) (ty2: type 𝔅) x1 x2 d g tid l :
    ltype_own (Owned m) (OfRes (prod_ty ty1 ty2)) (inl (PlaceIn (𝔄:=𝔄 * 𝔅) (x1, x2))) d g tid l ⊢
    ltype_own (Owned m) (ProdLty (OfRes ty1) (OfRes ty2))
      (inr (inl (PlaceIn x1), inl (PlaceIn x2))) d g tid l.
  Proof.
    rewrite /ltype_own /= /res_leaf /prod_node /=.
    iIntros "(%x & -> & Pt & Gho) /=".
    rewrite heap_cloc_mapsto_fancy_vec_app ty_size_eq. iDestruct "Pt" as "[Pt1 Pt2]".
    iAssert (▷^m (∃ d' g', ⌜d' ≤ d ∧ g' ≤ g⌝ ∗ ty_gho_res ty1 x1 d' g' tid) ∗
      ▷^m (∃ d' g', ⌜d' ≤ d ∧ g' ≤ g⌝ ∗ ty_gho_res ty2 x2 d' g' tid))%I
      with "[Gho]" as "[G1 G2]".
    { rewrite -bi.laterN_sep. iNext. iDestruct "Gho" as (d' g' ?) "[G1 G2]".
      iSplitL "G1"; iExists d', g'; by iFrame. }
    iSplitL "Pt1 G1"; [iExists x1|iExists x2]; iSplit; done || iFrame.
  Qed.

  (** The resolved ownership of an owned pointer below one owned pointer (the root): its
      pointee is a resolved leaf. *)
  Lemma res_leaf_own_unfold1 {𝔄} n (ty: type 𝔄) l' x d g tid l E :
    ltype_own (Owned 1) (OfRes (own_ptr n ty)) (inl (PlaceIn (𝔄:=at_locₛ 𝔄) (l', x))) d g tid l
      ={E}=∗
    ltype_own (Owned 1) (OwnPtrLty n (OfRes ty)) (inr (l', inl (PlaceIn x))) d g tid l.
  Proof.
    rewrite /ltype_own /= /res_leaf /own_node /=.
    iIntros "(%v & -> & Pt & H)". iDestruct "H" as (d' g') "[>[%Hd %Hg] H]".
    destruct d' as [|d']; simpl; [by iMod "H"|].
    iDestruct "H" as "(Pt' & Fr & Gho)".
    iEval (rewrite (heap_cloc_mapsto_fancy_empty l' (ty_phys ty x tid)) ty_size_eq) in "Pt'".
    iMod "Pt'". iModIntro. iFrame "Pt Fr". iSplit; [iPureIntro; lia|]. iExists x.
    iSplit; [done|]. iFrame "Pt'". iNext. iNext. iExists d', g'. iFrame "Gho".
    iPureIntro. lia.
  Qed.

  (** A resolved unique borrow is re-read as a shared reference to its referent, at its
      lifetime: its resolved ownership is either the ownership of [&shr{κ} ty] at the
      current value of the referent, or (when it has been resolved by
      [resolve_keep_just], without knowing that κ is alive) its unresolved body, which
      is resolved now ([resolve_uniq_body], κ alive; the later credits strip the laters
      of the leaf). *)
  Lemma res_leaf_uniq_to_shr m {𝔄} κ (ty: type 𝔄) (y: ~~ (uniq_borₛ 𝔄)) d g D tid l
      E L G :
    Timeless G → lctx_lft_alive E L κ → m ≤ D → d ≤ D → g ≤ D →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ time_ctx -∗ elctx_interp E -∗
    (G &&{↑NllftG}&&> llctx_interp L) -∗ G -∗ ⧖D -∗ £(advance_credits D) -∗
    ltype_own (Owned m) (OfRes (&uniq{κ} ty)) (inl (PlaceIn y)) d g tid l ={⊤}=∗
    G ∗ ltype_own (Owned m) (ShrLty (OfTy ty) κ)
      (inl (PlaceIn (𝔄:=at_clocₛ 𝔄) (uniq_bor_loc y, uniq_bor_current y))) d g tid l.
  Proof.
    iIntros (? Alv Hm Hd Hg) "#LFT #PROPH #UNIQ #TIME #E #GL G #⧖ £".
    rewrite /ltype_own /= /res_leaf /leaf_owned_s /leaf_owned /ofty_owned /=.
    iIntros "(%x & -> & Pt & Gho)". destruct y as [[[[[l0 x0] ξi] d0] g0] idx].
    iDestruct (lc_weaken m with "£") as "£"; [rewrite /advance_credits; nia|].
    iMod (lc_fupd_elim_laterN with "£ Gho") as (d' g' [??]) "(#In & %Hle & #Gc & Gho)".
    iAssert (|={⊤}=> G ∗ (@[κ] &&{↑NllftG; 1}&&> l0 #↦!∗ ty.(ty_phys) x0 tid) ∗
      ty.(ty_shr) κ x0 d0 g0 tid ∗ ty.(ty_gho_pers) x0 d0 g0 tid)%I
      with "[G Gho]" as ">(G & #Gp & #Shr & #Pers)".
    { iDestruct "Gho" as "[Body|$]"; [|done].
      iAssert (⧖(S d0 `max` g0))%I as "#⧖'".
      { iApply (persistent_time_receipt_mono with "⧖"). lia. }
      iMod (resolve_uniq_body ty x0 ξi d0 g0 idx κ tid l0 E L G ⊤
        with "LFT PROPH UNIQ TIME In E GL G ⧖' Body") as "(_ & $ & $ & $ & $)";
        [done|solve_ndisj|]. done. }
    iModIntro. iFrame "G".
    iSplit; [|done]. iExists (l0, x0). iSplit; [done|]. iFrame "Pt".
    iApply bi.laterN_intro. destruct d as [|d]; [lia|]. simpl. iSplit.
    - iApply guard_cloc_combine_fancy.
      + iApply (lguards_weaken_later with "Gc"). lia.
      + iApply (lguards_weaken_later with "Gp"). lia.
    - iSplit; [iApply (ty_shr_depth_mono with "Shr"); lia|].
      iNext. iApply (ty_gho_pers_depth_mono with "Pers"); lia.
  Qed.
End res_leaf.

(** * (a) Conversions of resolved leaves (in the owned part of a place) *)

Section res_conv.
  Context `{!typeG Σ}.

  (** A resolved leaf of a type without unique borrows ([ResOwn]) is an unresolved leaf
      (e.g. [&shr{κ} ty], [own_ptr n int], products of such types). *)
  Lemma tctx_oplace_res_to_ofty {𝔅 𝔄} E L p n (K: pctx 𝔅 𝔄) `{!PctxNoUniq K}
      (ty: type 𝔅) `{!ResOwn ty} :
    tctx_incl E L +[p ◁ₗown{n} pctx_plug K (OfRes ty)] +[p ◁ₗown{n} pctx_plug K (OfTy ty)]
      (λ post '-[x], post -[x]).
  Proof.
    apply (tctx_oplace_change_hole _ _ _ _ K); [done|done|].
    iIntros (y ζm q d g tid l) "H !>". by iApply res_leaf_to_ofty.
  Qed.

  (** A resolved pair is a pair of resolved leaves. *)
  Lemma tctx_unfold_oplace_res_prod {𝔅1 𝔅2 𝔄} E L p n (K: pctx (𝔅1 * 𝔅2) 𝔄) `{!PctxNoUniq K}
      (ty1: type 𝔅1) (ty2: type 𝔅2) :
    tctx_incl E L +[p ◁ₗown{n} pctx_plug K (OfRes (ty1 * ty2))]
      +[p ◁ₗown{n} pctx_plug K (ProdLty (OfRes ty1) (OfRes ty2))] (λ post '-[x], post -[x]).
  Proof.
    apply (tctx_oplace_change_hole _ _ _ _ K); [done|done|].
    iIntros ([y1 y2] ??????) "H !>". by iApply res_leaf_prod_unfold.
  Qed.

  (** A resolved owned pointer (below the root only, as [tctx_unfold_oplace_own]): its
      pointee is resolved. *)
  Lemma tctx_unfold_oplace_res_own {𝔅 𝔄} E L p n' (K: pctx (at_locₛ 𝔅) 𝔄) `{!PctxNoUniq K}
      n (ty: type 𝔅) :
    pctx_mode K 1 = 1%nat →
    tctx_incl E L +[p ◁ₗown{n'} pctx_plug K (OfRes (own_ptr n ty))]
      +[p ◁ₗown{n'} pctx_plug K (OwnPtrLty n (OfRes ty))] (λ post '-[x], post -[x]).
  Proof.
    intros Hm. apply (tctx_oplace_change_hole _ _ _ _ K); [done|done|].
    iIntros ([l' y] ??????) "H". rewrite Hm. by iApply res_leaf_own_unfold1.
  Qed.

  (** A resolved shared reference is a shared reference ([ResOwn]); unfolded. *)
  Lemma tctx_unfold_oplace_res_shr {𝔅 𝔄} E L p n (K: pctx (at_clocₛ 𝔅) 𝔄) `{!PctxNoUniq K}
      κ (ty: type 𝔅) :
    tctx_incl E L +[p ◁ₗown{n} pctx_plug K (OfRes (&shr{κ} ty))]
      +[p ◁ₗown{n} pctx_plug K (ShrLty (OfTy ty) κ)] (λ post '-[x], post -[x]).
  Proof.
    apply (tctx_oplace_change_hole _ _ _ _ K); [done|done|].
    iIntros (y ζm q d g tid l) "H !>". iDestruct (res_leaf_to_ofty with "H") as "H".
    rewrite /ltype_own /=. by iFrame.
  Qed.
End res_conv.

Section res_conv_uniq.
  Context `{!typeG Σ}.

  (** A resolved unique borrow is re-read as a shared reference at its lifetime, whose
      referent is its current referent: [OfRes (&uniq{κ} ty)] becomes [ShrLty (OfTy ty) κ]
      (retyping the leaf, below no sum). This is an instruction (one program step, for
      the credits): if the borrow was resolved without κ alive ([resolve_keep_just]), it
      is resolved now, at the (alive) κ. *)
  Lemma type_oplace_res_uniq_to_shr_instr {𝔅 𝔄} E L I p n (K: pctx (uniq_borₛ 𝔅) 𝔄)
      `{!PctxNoUniq K} κ (ty: type 𝔅) :
    pctx_nosum K → lctx_lft_alive E L κ →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K (OfRes (&uniq{κ} ty))] (place_resolve.skipn 1)
      (const +[p ◁ₗown{n} pctx_plug (pctx_retype K (at_clocₛ 𝔅)) (ShrLty (OfTy ty) κ)])
      (λ post '-[x], post -[((x.1.1, pctx_reset K x.1.2
        ((uniq_bor_loc (pctx_get K x.1.2), uniq_bor_current (pctx_get K x.1.2))
          : ~~ (at_clocₛ 𝔅))), x.2)]).
  Proof.
    iIntros (Hns Alv tid post mask iκs [x []])
      "#LFT #TIME #PROPH #UNIQ #E L I [(%v & %Hp & Own) _] Obs".
    destruct x as [[l x₀] ζm].
    iDestruct "Own" as (D d g) "(#⧖ & ⧗ & -> & %Hle & Fr & Own)".
    rewrite /ltype_own !lty_pat_plug !lty_rfn_plug !ltype_own_plug.
    iDestruct "Own" as "[H Rest]".
    iDestruct (pctx_own_mode_le with "Rest") as %Hk.
    have ?: pctx_depth K d ≤ d by (rewrite pctx_depth_sub; lia).
    have ?: pctx_mode K 1 ≤ D by (rewrite pctx_mode_add; lia).
    iMod (llctx_interp_make_guarded with "L") as (γ) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    set y := pctx_get K x₀.
    set y' := ((uniq_bor_loc y, uniq_bor_current y) : ~~ (at_clocₛ 𝔅)).
    iApply (wp_skipn_ctask 1 (advance_credits D) D with "TIME ⧖ [H H1 H2]"); [done| |].
    { iIntros "!> £".
      iMod (res_leaf_uniq_to_shr with "LFT PROPH UNIQ TIME E Ghalf H1 ⧖ £ H") as "[H1 H]";
        [done|lia..|].
      iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
      iModIntro. iCombine "L H" as "R". iExact "R". }
    iIntros "[L H]".
    iExists -[((l, pctx_reset K x₀ y'), ζm)]. iFrame "L I Obs". iSplit; [|done].
    rewrite /tctx_elt_interp. iExists #l. iSplit; [done|]. iExists D, d, g.
    rewrite (lty_nrc_plug_retype K (OfRes (&uniq{κ} ty)) (ShrLty (OfTy ty) κ)) //.
    rewrite (lty_size_plug_retype K (OfRes (&uniq{κ} ty)) (ShrLty (OfTy ty) κ)); [|done|done].
    iFrame "⧖ ⧗ Fr". iSplit; [done|]. iSplit; [done|].
    rewrite /ltype_own lty_pat_plug lty_rfn_plug pctx_get_reset ltype_own_plug pctx_own_reset //
      pctx_loc_reset // pctx_mode_retype pctx_depth_retype. iFrame "Rest".
    rewrite (_: lty_size (ShrLty (OfTy ty) κ) = lty_size (OfRes (&uniq{κ} ty))); [|done].
    iExact "H".
  Qed.
End res_conv_uniq.

(** * (b) Sums: case analysis on a resolved sum, and folding back *)

Section res_sum.
  Context `{!typeG Σ}.

  Lemma lty_size_sum_ofres {𝔄l} (tyl: typel 𝔄l) i :
    lty_size (SumLty tyl i (OfRes (tyl +!! i))) = ty_size (xsum_ty tyl).
  Proof. rewrite lty_size_fold. exact (f_equal ty_size (lty_fold_sum_ofty tyl i)). Qed.

  Lemma xsum_gho_res_pinj {𝔄l} i (tyl: typel 𝔄l) x0 pad d g tid :
    ty_gho_res (Σ! tyl) (pinj i x0, pad) d g tid ⊣⊢ ty_gho_res (tyl +!! i) x0 d g tid.
  Proof. rewrite [ty_gho_res (Σ! tyl)]/ty_gho_res /xsum_ty /=. by rewrite to_xsum_pinj. Qed.

  (** A resolved sum at a known variant [i] is a sum place whose payload is the resolved
      leaf of the variant, and back. *)
  Lemma sum_res_unfold_own m {𝔄l} (tyl: typel 𝔄l) i (y: ~~ (𝔄l !!ₗ i)) pad d g tid l :
    ltype_own (Owned m) (OfRes (xsum_ty tyl)) (inl (PlaceIn (𝔄:=Σ! 𝔄l) (pinj i y, pad))) d g tid l ⊣⊢
    ltype_own (Owned m) (SumLty tyl i (OfRes (tyl +!! i))) (prfn_sum i (inl (PlaceIn y)) pad)
      d g tid l.
  Proof.
    rewrite /ltype_own /= psum_proj_pinj /= /res_leaf.
    rewrite -{1}(hlist_set_hlookup tyl i) -(max_hlist_with_hlist_set _ tyl i (tyl +!! i))
      hlist_set_hlookup.
    iSplit.
    - iIntros "(%x & -> & Pt & Gho)". rewrite split_pt_xsum_cells''.
      iEval (setoid_rewrite xsum_gho_res_pinj) in "Gho".
      iDestruct "Pt" as "($ & Pt & $)". iExists y. by iFrame.
    - iIntros "(Tag & (%x & -> & Pt & Gho) & Pad)". iExists _. iSplit; [done|].
      iEval (setoid_rewrite xsum_gho_res_pinj).
      rewrite split_pt_xsum_cells''. by iFrame.
  Qed.

  Lemma sum_res_own_rfn m {𝔄l} (tyl: typel 𝔄l) i (y: ~~ (Σ! 𝔄l)) ζm q d g tid l :
    ltype_own (Owned m) (SumLty tyl i (OfRes (tyl +!! i)))
      (lty_rfn (SumLty tyl i (OfRes (tyl +!! i))) y ζm q) d g tid l ⊢
    ltype_own (Owned m) (OfRes (Σ! tyl)) (inl (PlaceIn y)) d g tid l.
  Proof.
    rewrite lty_rfn_sum. case_match eqn:Ha.
    - apply psum_proj_Some in Ha. destruct y as [s pad]. simpl in Ha. subst s.
      iIntros "H". iApply sum_res_unfold_own. iExact "H".
    - rewrite /ltype_own /=. by iIntros "[]".
  Qed.

  (** Folding back a resolved sum place whose payload is a resolved leaf. *)
  Lemma tctx_fold_oplace_res_sum {𝔄l 𝔄} E L p n (K: pctx (Σ! 𝔄l) 𝔄) `{!PctxNoUniq K}
      (tyl: typel 𝔄l) i :
    tctx_incl E L +[p ◁ₗown{n} pctx_plug K (SumLty tyl i (OfRes (tyl +!! i)))]
      +[p ◁ₗown{n} pctx_plug K (OfRes (Σ! tyl))] (λ post '-[x], post -[x]).
  Proof.
    apply (tctx_oplace_change_hole _ _ _ _ K); [by rewrite lty_size_sum_ofres|done|].
    iIntros (y ζm q d g tid l) "H !>". by iApply sum_res_own_rfn.
  Qed.

  (** Case analysis on a resolved sum at the hole of [K] (in the owned part of a place):
      the discriminant is read from the cells of the resolved leaf, which is unfolded into
      a sum place at the variant [i] of its value, with a resolved payload, and the program
      continues with branch [i]. *)
  Lemma type_case_oplace_res {𝔄l 𝔄 𝔅l 𝔇} E L I (C: cctx 𝔇) p n (K: pctx (Σ! 𝔄l) 𝔄)
      `{!PctxNoUniq K} (tyl: typel 𝔄l) (T: tctx 𝔅l) el el' trl :
    IntoPlistc el el' →
    ([∗ nat] i < length 𝔄l, typed_body E L I C
      (p ◁ₗown{n} pctx_plug K (SumLty tyl i (OfRes (tyl +!! i))) +:: T) (el' -!! i) (trl -!! i)) -∗
    typed_body E L I C (p ◁ₗown{n} pctx_plug K (OfRes (Σ! tyl)) +:: T)
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
    iDestruct "Own" as "[L1 Rest]". iSimpl in "L1". rewrite /res_leaf.
    iDestruct "L1" as (? ->) "[Pt1 Gho1]".
    remember (pctx_get K x₀) as y eqn:Hy. destruct y as [s pad].
    destruct (to_xsum s) as [j a] eqn:Hj.
    have Hs: s = pinj j a. { by rewrite -(semi_iso' to_xsum of_xsum s) Hj. }
    subst s.
    set lr := (l, repeat [] (lty_size (pctx_plug K (OfRes (Σ! tyl))))).
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
      iDestruct (oplace_loc_guard K (OfRes (Σ! tyl)) x₀ l (cloc_take lK 1 #↦∗ [ #j ])%I
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
    rewrite (lty_nrc_plug_eq K (OfRes (Σ! tyl)) (SumLty tyl j (OfRes (tyl +!! j)))) //
      (lty_size_plug_eq K _ (OfRes (Σ! tyl))); [|apply lty_size_sum_ofres].
    iFrame "⧗p Fr". iSplit; [done|]. iSplit; [done|].
    rewrite /ltype_own lty_pat_plug lty_rfn_plug -Hy lty_rfn_sum_in ltype_own_plug
      lty_size_sum_ofres. iFrame "Rest".
    iApply sum_res_unfold_own. rewrite /ltype_own /= /res_leaf.
    iExists (pinj j a, pad). iSplit; [done|]. rewrite split_pt_xsum_cells''. by iFrame.
  Qed.
End res_sum.
