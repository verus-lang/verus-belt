(** * Sum places

  A leaf [OfTy (enum_ty EL tyl)] of a place rooted at an owned location ([p ◁ₗown{n} lt]) holds a
  sum. Reading its discriminant ([type_case_oplace]) branches on the
  variant [i] of its value and, in branch [i], unfolds the leaf into a _sum place_ at
  variant [i], [SumLty EL tyl i (OfTy (tyl +!! i))] (whose payload is the leaf of the
  variant; the specification of the branch knows the variant). The payload is reached
  by the context step [PSum EL tyl i w K] (offset 1, [lpath.v]), so that the general rules
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
From lrust.typing Require Import type_context programs lft_contexts uniq_util uniq_bor own shr_bor bytes_layout value_ctx unit uninit freeable_util.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section place_sum.
  Context `{!typeG Σ}.

  Lemma pctx_plug_cpd {𝔅 𝔄} (K: pctx 𝔅 𝔄) lt : pctx_nonempty K → lty_is_cpd (pctx_plug K lt).
  Proof. by destruct K. Qed.

  Lemma lty_rfn_sum_in {EL 𝔄l} (tyl: typel 𝔄l) i (lt: lty (𝔄l !!ₗ i)) a ζm q :
    lty_rfn (SumLty EL tyl i lt) (pinj i a) ζm q = prfn_sum i (lty_rfn lt a ζm (false :: q)).
  Proof. by rewrite lty_rfn_sum /= psum_proj_pinj. Qed.

  (** The interpretation of a sum place whose payload is a leaf, at the refinement of a
      value. *)
  Lemma sum_ofty_own_rfn m {EL 𝔄l} (tyl: typel 𝔄l) i (y: ~~ (enumₛ EL 𝔄l)) ζm q d g tid l :
    ltype_own (Owned m) (SumLty EL tyl i (OfTy (tyl +!! i)))
      (lty_rfn (SumLty EL tyl i (OfTy (tyl +!! i))) y ζm q) d g tid l ⊢
    ltype_own (Owned m) (OfTy (enum_ty EL tyl)) (inl (PlaceIn y)) d g tid l.
  Proof.
    rewrite lty_rfn_sum. case_match eqn:Ha.
    - apply psum_proj_Some in Ha. simpl in Ha. subst y.
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

  Lemma tctx_fold_oplace_sum {EL 𝔄l 𝔄} E L p n (K: pctx (enumₛ EL 𝔄l) 𝔄) `{!PctxNoUniq K} (tyl: typel 𝔄l) i :
    tctx_incl E L +[p ◁ₗown{n} pctx_plug K (SumLty EL tyl i (OfTy (tyl +!! i)))]
      +[p ◁ₗown{n} pctx_plug K (OfTy (enum_ty EL tyl))] (λ post '-[x], post -[x]).
  Proof.
    apply (tctx_oplace_change_hole _ _ _ _ K); [done|done|].
    iIntros (y ζm q d g tid l) "H !>". by iApply sum_ofty_own_rfn.
  Qed.

  (** Reading the discriminant of the leaf at the hole of [K] (a sum, at any path): the
      leaf is unfolded into a sum place at the variant [i] of its value, and the program
      continues with branch [i]. *)
  Lemma type_case_oplace {EL 𝔄l 𝔄 𝔅l 𝔇} E L I (C: cctx 𝔇) p n (K: pctx (enumₛ EL 𝔄l) 𝔄) `{!PctxNoUniq K}
      (tyl: typel 𝔄l) (T: tctx 𝔅l) el el' trl :
    IntoPlistc el el' →
    ([∗ nat] i < length 𝔄l, typed_body E L I C
      (p ◁ₗown{n} pctx_plug K (SumLty EL tyl i (OfTy (tyl +!! i))) +:: T) (el' -!! i) (trl -!! i)) -∗
    typed_body E L I C (p ◁ₗown{n} pctx_plug K (OfTy (enum_ty EL tyl)) +:: T)
      (case: (GetDiscr (syn_mty (enumₛ EL 𝔄l)) (pctx_expr K p)) of el)
      (λ post '(x -:: cl), let 'xinj i _ := to_xsum (pctx_get K x.1.2) in
        (trl -!! i) post (x -:: cl))%type.
  Proof.
    move=> ->. iIntros "el".
    iIntros (tid [x xl] mask post iκs) "#LFT #TIME #PROPH #UNIQ #E L I C /=[Tp T] #Obs".
    destruct x as [[l x₀] ζm].
    rewrite /tctx_elt_interp.
    iDestruct "Tp" as (v Hp D d g) "(#⧖ & ⧗p & -> & %Hle & Fr & Own)".
    have ?: Closed [] (pctx_expr K p).
    { apply pctx_expr_closed. have ?: Closed [] p by eapply eval_path_closed. apply _. }
    rewrite /ltype_own lty_pat_plug lty_rfn_plug ltype_own_plug.
    iDestruct "Own" as "[L1 Rest]". iSimpl in "L1".
    iDestruct "L1" as (? ->) "[Pt1 Gho1]".
    destruct (to_xsum (pctx_get K x₀)) as [j a] eqn:Hj.
    have Hy: pinj j a = pctx_get K x₀.
    { by rewrite -(semi_iso' to_xsum of_xsum (pctx_get K x₀)) Hj. }
    try rewrite -Hy.
    set lr := l.
    set lK := pctx_loc K (lty_size (OfTy (enum_ty EL tyl))) x₀ lr.
    (* The address of the hole. *)
    wp_bind (pctx_expr K p).
    iApply (wp_wand with "[Rest]").
    { iApply (wp_pctx_expr K (lty_size (OfTy (enum_ty EL tyl))) 1 x₀ ζm [] d g tid lr p True True
        with "[] Rest").
      - wp_bind p. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->".
        iFrame; by iPureIntro. }
    iIntros (w) "(-> & _ & _ & Rest)".
    (* Read the discriminant ([GetDiscr] reads the tag). *)
    iEval (rewrite (cbytes_sum _ j (tyl +!! j))) in "Pt1". iDestruct "Pt1" as "(Rest & Pay)".
    iDestruct "Tag" as (bt) "[Bt %Hbt]".
    wp_bind (GetDiscr _ _).
    iApply (wp_get_discr_sum with "Bt"); [exact Hbt|apply fin_to_nat_lt|]. iIntros "Bt".
    wp_case. { split; [lia|]. by rewrite Nat2Z.id -vlookup_lookup plistc_to_vec_lookup. }
    iDestruct (big_sepN_lookup _ _ j with "el") as "el".
    iApply ("el" $! _ (((l, x₀), ζm) -:: xl)
      with "LFT TIME PROPH UNIQ E L I C [-] []"); last first.
    { iApply proph_obs_impl; [|done]=>/= ?. by rewrite -?Hy to_xsum_pinj. }
    iFrame "T". iExists (MLitV (VPtr l)). iSplit; [done|]. iExists D, d, g. iFrame "⧖".
    rewrite (lty_nrc_plug_eq K (OfTy (enum_ty EL tyl)) (SumLty EL tyl j (OfTy (tyl +!! j)))) //
      (lty_size_plug_eq K _ (OfTy (enum_ty EL tyl))) //.
    iFrame "⧗p Fr". iSplit; [done|]. iSplit; [done|].
    rewrite /ltype_own lty_pat_plug lty_rfn_plug -Hy lty_rfn_sum_in ltype_own_plug.
    iFrame "Rest".
    iApply sum_ofty_unfold_own. iExists (pinj j a). iSplit; [done|].
    rewrite /ofty_owned (cbytes_sum _ j (tyl +!! j)). by iFrame.
  Qed.

  (* Assigning a variant ([type_sum_assign_oplace_instr], [type_sum_unit_oplace_instr] of
     the deleted legacy [place_sum.v]) is not ported: on bytes, a variant is a MiniRust value
     ([type_mk_variant_val_instr]) that is written to the leaf with a typed [Store]
     ([type_write_place_instr]). *)
End typing.
