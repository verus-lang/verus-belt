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
From lrust.typing Require Import type_context programs lft_contexts uniq_util uniq_bytes_util uniq_bytes own_bytes shr_bytes bytes_layout value_ctx product uninit freeable_util.
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
    apply (tctx_oplace_change_hole _ _ _ _ K); [done|done|].
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
      (case: ToLit (Load Na1Ord (MInt (sum_tag 𝔄l)) (pctx_expr K (ToLit p))) of el)
      (λ post '(x -:: cl), let 'xinj i _ := to_xsum (pctx_get K x.1.2).1 in
        (trl -!! i) post (x -:: cl))%type.
  Proof.
    move=> ->. iIntros "el".
    iIntros (tid [x xl] mask post iκs) "#LFT #TIME #PROPH #UNIQ #E L I C /=[Tp T] #Obs".
    destruct x as [[l x₀] ζm].
    rewrite /tctx_elt_interp.
    iDestruct "Tp" as (v Hp D d g) "(#⧖ & ⧗p & -> & %Hle & Fr & Own)".
    have ?: Closed [] (pctx_expr K (ToLit p)).
    { apply pctx_expr_closed. have ?: Closed [] p by eapply eval_path_closed. apply _. }
    rewrite /ltype_own lty_pat_plug lty_rfn_plug ltype_own_plug.
    iDestruct "Own" as "[L1 Rest]". iSimpl in "L1".
    iDestruct "L1" as (? ->) "[Pt1 Gho1]".
    remember (pctx_get K x₀) as y eqn:Hy. destruct y as [s pad].
    destruct (to_xsum s) as [j a] eqn:Hj.
    have Hs: s = pinj j a. { by rewrite -(semi_iso' to_xsum of_xsum s) Hj. }
    subst s.
    set lr := (l, repeat [] (lty_size (pctx_plug K (OfTy (Σ! tyl))))).
    set lK := pctx_loc K (lty_size (OfTy (Σ! tyl))) x₀ lr.
    (* The address of the hole. *)
    iMod lc_zero as "£0".
    wp_bind (pctx_expr K (ToLit p)).
    iApply (wp_wand with "[Rest £0]").
    { iApply (wp_pctx_expr K (lty_size (OfTy (Σ! tyl))) 1 x₀ ζm [] d g tid lr (ToLit p) True True 0
        with "[] £0 [] Rest").
      - rewrite /lr -heap_cloc_mapsto_empty. iApply guards_true.
      - wp_bind p. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->".
        by wp_pure _. }
    iIntros (w) "(-> & _ & _ & Rest)".
    (* Read the discriminant: a typed [Load] of the tag. *)
    iEval (rewrite (cbytes_sum _ j (tyl +!! j))) in "Pt1". iDestruct "Pt1" as "(Tag & Pay & Pad)".
    iDestruct "Tag" as (bt) "[Bt %Hbt]".
    wp_bind (Load _ _ _).
    iApply (wp_load_na with "Bt"); [exact Hbt|]. iIntros "!> Bt". wp_pure _.
    wp_case. { split; [lia|]. by rewrite Nat2Z.id -vlookup_lookup plistc_to_vec_lookup. }
    iDestruct (big_sepN_lookup _ _ j with "el") as "el".
    iApply ("el" $! _ (((l, x₀), ζm) -:: xl)
      with "LFT TIME PROPH UNIQ E L I C [-] []"); last first.
    { iApply proph_obs_impl; [|done]=>/= ?. by rewrite -Hy /= to_xsum_pinj. }
    iFrame "T". iExists (MLitV (VPtr l)). iSplit; [done|]. iExists D, d, g. iFrame "⧖".
    rewrite (lty_nrc_plug_eq K (OfTy (Σ! tyl)) (SumLty tyl j (OfTy (tyl +!! j)))) //
      (lty_size_plug_eq K _ (OfTy (Σ! tyl))) //.
    iFrame "⧗p Fr". iSplit; [done|]. iSplit; [done|].
    rewrite /ltype_own lty_pat_plug lty_rfn_plug -Hy lty_rfn_sum_in ltype_own_plug.
    iFrame "Rest".
    iApply sum_ofty_unfold_own. iExists (pinj j a, pad). iSplit; [done|].
    rewrite /bofty_owned (cbytes_sum _ j (tyl +!! j)). by iFrame.
  Qed.

  (* Assigning a variant ([type_sum_assign_oplace_instr], [type_sum_unit_oplace_instr] of
     the deleted legacy [place_sum.v]) is not ported: on bytes, a variant is a MiniRust value
     ([type_mk_variant_val_instr]) that is written to the leaf with a typed [Store]
     ([type_write_oplace_instr]). *)
End typing.
