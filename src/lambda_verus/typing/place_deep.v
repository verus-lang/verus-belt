(** * Values of any size and sums below unique and shared borrows

  The operations of [place_memcpy.v] (memcpy-style copies [e1 <-{n} !e2] of values of any
  size) and of [place_sum.v] (case analysis on a sum, assigning a variant) for owned
  places ([p ◁ₗown{n} …]) whose context contains unique borrows ([PUniq], at any depth,
  interleaved with fields, owned pointers and sums), and copies of any size below shared
  references ([PShr]).

  All rules on a leaf [OfTy ty] at the hole of [K] go through [oplace_leaf_acc]: the
  access of [pctx_acc.v] (opening the enclosing borrows with the credits of the program
  step), and, if the hole is the whole referent of the innermost borrow ([Uniq] mode), the
  opening of its body; in both modes it gives the cells of the leaf (possibly ghost
  cells, guarded by a token), the ownership of its value without laters, and a closer for
  a new value of the leaf (of the same type).

  - [type_memcpy_oplace_deep_instr]: assignment of a value of any size of the type of the
    leaf (as Rust's assignment through [&mut]), the old value resolved;
    [type_memcpy_copy_from_oplace_deep_instr]: copy of a [Copy] leaf into any path that
    can be written; [type_memcpy_copy_from_oplace_pshr_instr]: the same below a shared
    reference. (Moves out of a leaf and assignments that change the type of the leaf are
    only sound below no unique borrow: [type_memcpy_from_oplace_instr],
    [type_memcpy_oplace_instr] of [place_memcpy.v].)
  - [type_case_oplace_deep]: case analysis on a sum leaf, which becomes the sum place
    [SumLty tyl i (OfTy (tyl +!! i))] in branch [i]; [type_fold_oplace_sum_deep_instr]
    folds it back; [type_sum_assign_oplace_deep_instr], [type_sum_unit_oplace_deep_instr],
    [type_sum_memcpy_oplace_deep_instr]: assigning a variant (payload of size 1, unit
    variant, payload of any size).

  See [~/verus-belt-phase3-design.md], section "Any size and sums below PUniq". *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From lrust.lang Require Import proofmode memcpy.
From lrust.typing Require Export type ltype lpath pctx_acc place_own.
From lrust.typing Require Import type_context programs programs_util lft_contexts
  uniq_util uniq_bor product own uninit freeable_util place place_sum place_puniq
  place_pshr sum type_sum.
From lrust.util Require Import proph_bor.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

(** * Access to a leaf below unique borrows *)

Section leaf_acc.
  Context `{!typeG Σ}.

  (** The closer of [oplace_leaf_acc]: a new value [y'] of the leaf, with its cells and
      ownership, at new depths. *)
  Definition oplace_leaf_closer {𝔅 𝔄} (K: pctx 𝔅 𝔄) (ty: type 𝔅) (x₀: ~~𝔄) (ζm: blk_map)
      (d g: nat) (tid: thread_id) (l: loc) (E: coPset) (G G': iProp Σ) : iProp Σ :=
    ∀ y' dh' gh' dn gn, ⌜d ≤ dn ∧ g ≤ gn ∧ dh' + pctx_dlev K ≤ dn ∧ gh' ≤ gn⌝ -∗
      ⧖(S dn `max` gn) -∗ G' -∗
      pctx_ptrs K (ty_size ty) x₀ (l, repeat [] (lty_size (pctx_plug K (OfTy ty)))) -∗
      pctx_loc K (ty_size ty) x₀ (l, repeat [] (lty_size (pctx_plug K (OfTy ty))))
        #↦!∗ ty_phys ty y' tid -∗
      ty_gho_own ty y' dh' gh' tid ={E}=∗
      ltype_own (Owned 1) (pctx_plug K (OfTy ty))
        (lty_rfn (pctx_plug K (OfTy ty)) (pctx_set K x₀ y') ζm []) dn gn tid
        (l, repeat [] (lty_size (pctx_plug K (OfTy ty)))) ∗ G.

  (** The access to the leaf [OfTy ty] at the hole of [K] of an owned place (at the root,
      [Owned 1] mode), below any number of unique borrows, in both modes of the hole. The
      cells of the leaf are guarded by the returned token [G'], which also guards the
      lifetime of the enclosing borrows; the pointer cells on the path are returned to
      compute the address ([wp_pctx_ptrs]). *)
  Lemma oplace_leaf_acc {𝔅 𝔄} (K: pctx 𝔅 𝔄) `{!PctxNoShr K} (ty: type 𝔅) x₀ ζm d g tid
      (l: loc) E (G: iProp Σ) :
    Timeless G → lazyE ⊆ E →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[pctx_ulft K (OfTy ty)]) -∗ G -∗
    £((d + 2) * (d + 3)) -∗
    ltype_own (Owned 1) (pctx_plug K (OfTy ty)) (lty_rfn (pctx_plug K (OfTy ty)) x₀ ζm []) d g
      tid (l, repeat [] (lty_size (pctx_plug K (OfTy ty)))) ={E}=∗
    ∃ (G': iProp Σ) dh gh, ⌜Timeless G'⌝ ∗ G' ∗ ⌜dh + pctx_dlev K ≤ d ∧ gh ≤ g ∧ pctx_in K x₀⌝ ∗
      (G' &&{↑NllftG}&&> @[pctx_ulft K (OfTy ty)]) ∗
      (G' &&{↑NllftG; g + 1}&&>
        pctx_loc K (ty_size ty) x₀ (l, repeat [] (lty_size (pctx_plug K (OfTy ty)))) #↦∗_) ∗
      pctx_loc K (ty_size ty) x₀ (l, repeat [] (lty_size (pctx_plug K (OfTy ty))))
        #↦!∗ ty_phys ty (pctx_get K x₀) tid ∗
      ty_gho_own ty (pctx_get K x₀) dh gh tid ∗
      pctx_ptrs K (ty_size ty) x₀ (l, repeat [] (lty_size (pctx_plug K (OfTy ty)))) ∗
      pctx_pguards K (ty_size ty) (g + 1) G' x₀ (l, repeat [] (lty_size (pctx_plug K (OfTy ty)))) ∗
      oplace_leaf_closer K ty x₀ ζm d g tid l E G G'.
  Proof.
    iIntros (? HE) "#LFT #PROPH #UNIQ #Gu G £ Own".
    have ?: ↑NllftG ⊆ E. { trans lazyE; [apply lazyE_NllftG|done]. }
    have ?: ↑Nllft ⊆ E. { trans lazyE; [rewrite /lazyE; solve_ndisj|done]. }
    set lr := (l, repeat [] (lty_size (pctx_plug K (OfTy ty)))).
    set y := pctx_get K x₀.
    rewrite /ltype_own lty_pat_plug lty_rfn_plug.
    iDestruct (lc_weaken (pctx_acc_cred K 1 d + (d + 2)) with "£") as "[£a £]";
      [have := pctx_acc_cred_le K 1 d; nia|].
    iMod (pctx_acc K (OfTy ty) 1 with "LFT PROPH UNIQ Gu G £a Own")
      as (G' dh gh) "(% & G' & #G'G & %Hdh & H & P & #Gs & #HG & Cl)"; [done|].
    destruct Hdh as (Hdh & Hgh & Hin).
    iAssert (G' &&{↑NllftG}&&> @[pctx_ulft K (OfTy ty)])%I as "#G'u".
    { iApply (guards_transitive with "G'G Gu"). }
    iDestruct (pctx_hguard K (OfTy ty) (ty_size ty) x₀ l G' g with "G'u HG") as "#Gw".
    destruct (pctx_uend K) as [κ|] eqn:Hu.
    - (* The hole is the whole referent of the innermost borrow: open its body. *)
      iEval (rewrite (pctx_kind_uniq K κ) //) in "H".
      iEval (rewrite /pctx_closer (pctx_kind_uniq K κ) //) in "Cl".
      iDestruct "H" as (? idx ->) "Body".
      iMod (fractional.frac_split_guard_in_half NllftG G' G' with "G' []")
        as (γ2) "[A [B [#Gh2 #Back2]]]"; [done|iApply guards_refl|].
      iAssert (fractional.half γ2 &&{↑NllftG}&&> @[κ])%I as "#Aκ".
      { iApply (guards_transitive with "Gh2"). iApply (guards_transitive with "G'u").
        by iApply pctx_ulft_uend. }
      iAssert (fractional.half γ2 &&{↑NllftG}&&> @[ty_lft ty])%I as "#Aty".
      { iApply (guards_transitive with "Gh2"). iApply (guards_transitive with "G'u").
        iApply (pctx_ulft_fold K (OfTy ty)). by eapply pctx_uend_ulfts_ne. }
      iMod (uniq_body_acc with "LFT UNIQ Aκ Body A") as "(Pl & ⧗1 & CloseB)"; [done|].
      iDestruct (lc_weaken 1 with "£") as "£1"; [lia|].
      iMod (lc_fupd_elim_later with "£1 Pl") as "Pl".
      iMod (uniq_payload_run with "Aty B Pl") as "(B & _ & Gho1 & Pt1)"; [done|].
      iModIntro. iExists (fractional.half γ2), dh, gh. iSplit; [iPureIntro; apply _|].
      iFrame "B Gho1 Pt1 P". iSplit; [done|].
      iSplitR. { iApply (guards_transitive with "Gh2 G'u"). }
      iSplitR. { iApply (guards_transitive_right with "Gh2 Gw"). }
      iSplitR. { iApply (pctx_pguards_transfer with "Gh2 Gs"). }
      iIntros (y' dh' gh' dn gn (? & ? & ? & ?)) "#⧖ B P Pt Gho".
      iSpecialize ("CloseB" $! y' dh' gh' with "[Pt Gho] ⧗1").
      { iNext. iFrame "Gho Pt". iApply (persistent_time_receipt_mono with "⧖"). lia. }
      iMod (fupd_mask_mono with "CloseB") as "[Body A]"; [done|].
      iMod (fupd_mask_mono with "(Back2 A B)") as "G'"; [done|].
      iMod ("Cl" $! (OfTy ty) PatLeaf (inl (PlaceIn y')) dh' gh' dn gn [] 1%Qp True%I
        with "[//] [//] [%] [%] [] ⧖ G' P [] [Body]") as "(Own & G & _)".
      { intros ??. apply prfn_rsv_in. }
      { lia. }
      { iApply pat_ok_ulfts_leaf. }
      { done. }
      { iIntros "_ !>". iSplit; [|done]. iExists y', idx. by iFrame. }
      iModIntro. iFrame "G".
      by rewrite /ltype_own lty_pat_plug lty_rfn_plug pctx_get_set pctx_rfn_set //.
    - (* The hole is in [Owned] mode. *)
      iEval (rewrite (pctx_kind_owned K) //) in "H".
      iEval (rewrite /pctx_closer (pctx_kind_owned K) //) in "Cl".
      have Hm := pctx_hmode_le K 1. set mh := pctx_hmode K 1.
      iDestruct "H" as (? ->) "[Pt1 Gho1]".
      iDestruct (lc_weaken mh with "£") as "£"; [lia|].
      iMod (lc_fupd_elim_laterN with "£ Gho1") as "Gho1".
      iModIntro. iExists G', dh, gh. iSplit; [done|]. iFrame "G' Gho1 Pt1 P".
      iSplit; [done|]. iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
      iIntros (y' dh' gh' dn gn (? & ? & ? & ?)) "#⧖ G' P Pt Gho".
      iMod ("Cl" $! (OfTy ty) PatLeaf (inl (PlaceIn y')) dh' gh' dn gn [] 1%Qp True%I
        with "[//] [//] [%] [%] [] ⧖ G' P [] [Pt Gho]") as "(Own & G & _)".
      { intros ??. apply prfn_rsv_in. }
      { lia. }
      { iApply pat_ok_ulfts_leaf. }
      { done. }
      { iIntros "_ !>". iSplit; [|done]. iExists y'. iSplit; [done|]. rewrite /ofty_owned.
        iFrame "Pt". by iApply bi.laterN_intro. }
      iModIntro. iFrame "G".
      by rewrite /ltype_own lty_pat_plug lty_rfn_plug pctx_get_set pctx_rfn_set //.
  Qed.
End leaf_acc.

(** * Values of any size below unique borrows *)

Section memcpy_deep.
  Context `{!typeG Σ}.

  (** Copying a value of any size into the leaf at the hole of [K] (below any number of
      unique borrows, in both modes of the hole), from a path [pr] that can be read,
      keeping the type of the leaf (as Rust's assignment through [&mut]). The old value
      is resolved. The first step gives the credits to open the enclosing borrows and the
      cumulative time receipts to raise the depths of the place. *)
  Lemma type_memcpy_oplace_deep_instr {𝔅 𝔄 ℭ ℭ'} E L I p pr n (K: pctx 𝔅 𝔄) `{!PctxNoShr K}
      (ty: type 𝔅) (tyr: type ℭ) (tyr': type ℭ') gtr str Φ (sz: Z) :
    resolve E L ty Φ → typed_read E L tyr ty tyr' gtr str → sz = ty_size ty →
    lctx_lft_alive E L (pctx_ulft K (OfTy ty)) →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K (OfTy ty); pr ◁ tyr] (pctx_expr K p <-{sz} !pr)
      (λ _, +[p ◁ₗown{n} pctx_plug K (OfTy ty); pr ◁ tyr'])
      (λ post '-[x; b], λ mask π, Φ (pctx_get K x.1.2) π →
        ∀ zr, str b zr → post -[((x.1.1, pctx_set K x.1.2 (gtr b)), x.2); zr] mask π).
  Proof.
    iIntros (Rslv Rd -> Alv tid post mask iκs [x [b []]])
      "#LFT #TIME #PROPH #UNIQ #E L I (Tp & Tr & _) Obs".
    destruct x as [[l x₀] ζm].
    rewrite /tctx_elt_interp.
    iDestruct "Tp" as (v Hp D d g) "(#⧖ & ⧗p & -> & %Hle & Fr & Own)".
    iDestruct "Tr" as (vr dr Hpr) "(#⧖r & Tr)".
    have ?: Closed [] (pctx_expr K p).
    { apply pctx_expr_closed. by eapply eval_path_closed. }
    iDestruct (Alv with "L E") as "#Alv".
    (* The first step gives credits and cumulative time receipts. *)
    iCombine "⧖ ⧖r" as "⧖m".
    iApply (wp_cumulative_time_receipt_linear with "TIME ⧖m"); [solve_ndisj|].
    iIntros "⧗". iApply wp_fupd.
    set M := D `max` dr.
    iDestruct (cumulative_time_receipt_sep 1 (S M) with "⧗") as "[⧗c1 ⧗]".
    iDestruct (cumulative_time_receipt_sep 1 M with "⧗") as "[⧗c2 ⧗k]".
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗c1 ⧖m") as "[#⧖S £]";
      [solve_ndisj|].
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗c2 ⧖m") as "[_ £']";
      [solve_ndisj|].
    iCombine "£ £'" as "£".
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_ulft K (OfTy ty)])%I as "#Hu".
    { iApply (guards_transitive with "Ghalf Alv"). }
    set lr := (l, repeat [] (lty_size (pctx_plug K (OfTy ty)))).
    set y := pctx_get K x₀.
    have HM: S d ≤ M ∧ g ≤ M ∧ dr ≤ M by rewrite /M; lia.
    iDestruct (lc_weaken ((d + 2) * (d + 3) + (3 * (g + 1) * M + ((1 + (1 + M * (g + 1))) +
      ((dr + 1) + (1 + (6 * (M + 1) + (1 + (M + 1)))))))) with "£")
      as "[£a [£w [[£r £s] [£d [£b [£m [£o £o']]]]]]]";
      [rewrite /advance_credits; nia|].
    iMod (oplace_leaf_acc K ty x₀ ζm d g tid l (⊤ ∖ ↑advN) with "LFT PROPH UNIQ Hu H1 £a Own")
      as (G' dh gh) "(% & G' & %Hdh & #G'u & #Gw & Pt1 & Gho1 & P & #Gs & Cl)"; [solve_ndisj|].
    destruct Hdh as (Hdh & Hgh & Hin).
    set lK := pctx_loc K (ty_size ty) x₀ lr.
    (* The address of the hole, and the source. *)
    wp_bind (pctx_expr K p).
    iApply (wp_wand with "[P G' £w]").
    { iApply (wp_pctx_ptrs _ K (ty_size ty) (g + 1) G' x₀ lr p True%I with "[] Gs [£w] [G'] P");
        [solve_ndisj| | |].
      - iEval (rewrite /lr -heap_cloc_mapsto_empty). iApply guards_true.
      - iApply (lc_weaken with "£w"). nia.
      - iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->". by iFrame. }
    iIntros (w) "(-> & _ & G' & P)".
    wp_bind pr. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->".
    (* Resolve the old value. *)
    iDestruct (Rslv _ (⊤ ∖ (⊤ ∖ ↑Nllft ∖ ↑prophN ∖ ↑timeN ∖ ↑uniqN))
      with "LFT PROPH UNIQ TIME E Ghalf H2 Gho1") as "ToObs"; [set_solver|].
    iMod (lc_fupd_elim_later with "£r ToObs") as "ToObs".
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iDestruct (lc_step_fupdN_elim_later with "[£s] ToObs") as "ToObs".
    { iApply (lc_weaken with "£s"). nia. }
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iMod (fupd_mask_mono with "ToObs") as "[Obs' H2]"; [solve_ndisj|].
    (* Read the source. *)
    iMod (Rd with "LFT E Ghalf H2 Tr £d")
      as (lb vlb_c vlb HR Hvr Hlen) "(Hr & #Hrpt & Retether & _ & Own' & Totyr')".
    iDestruct "Own'" as "[Gb #>%Phys]".
    iMod (lc_fupd_elim_later with "£b Gb") as "Gb".
    have Hlenb: length vlb = ty_size ty by rewrite -Phys ty_size_eq.
    iMod (mapsto_vec_untether _ _ _ ∅ with "Pt1") as (vl) "[Pt1 [%Hvl _]]".
    have Hlenl: length vl = ty_size ty by rewrite Hvl ty_size_eq.
    injection Hvr as ->.
    iAssert (G' &&{↑NllftG; M + 1}&&> lK #↦∗_)%I as "#Gw'".
    { iApply (lguards_weaken_later with "Gw"). lia. }
    iApply (wp_memcpy_guarded _ lK lb vl vlb_c G' HR _ (M + 1)
      with "TIME [Pt1 Hr G' £m]"); [solve_ndisj|lia|lia| |].
    { iFrame "Pt1 Hr G' ⧖S £m". iSplit; [iApply "Gw'"|].
      iApply (lguards_weaken_later with "Hrpt"). lia. }
    iIntros "!> (Pt1 & G' & Hr)".
    (* Put the contents (with their ghost cells) into the leaf. *)
    destruct lK as [lK1 cK] eqn:HlK.
    leaf_open_laters "Gw'" with "G'" as "A"; [solve_ndisj|].
    iMod (lc_fupd_elim_later with "£o A") as "A".
    iMod (lc_fupd_elim_laterN with "£o' A") as "A". iMod "A" as "[Pre back]".
    iDestruct ("Retether" $! lK1 cK with "[Pre Pt1]") as "Ret"; [by iFrame|].
    iMod (fupd_mask_mono with "Ret") as "[Pre Pt1]"; [set_solver|].
    iMod ("back" with "Pre") as "G'".
    iMod (fupd_mask_mono with "(Totyr' Hr)") as (zr Hzr) "(H2 & Tr)"; [solve_ndisj|].
    (* Close the place at the new value. *)
    iDestruct (cumulative_time_receipt_mono (S (pctx_dlev K)) with "⧗k") as "⧗k"; [lia|].
    iMod (cumulative_persistent_time_receipt with "TIME ⧗k ⧖r") as "#⧖k"; [solve_ndisj|].
    set dn := (dr + pctx_dlev K) `max` d. set gn := dr `max` g.
    iCombine "⧖ ⧖k" as "⧖D".
    iMod ("Cl" $! (gtr b) dr dr dn gn with "[%] [] G' P [Pt1] Gb") as "[Own H1]".
    { lia. }
    { iApply (persistent_time_receipt_mono with "⧖D"). lia. }
    { rewrite (_: pctx_loc K (ty_size ty) x₀ lr = (lK1, cK)); [|exact HlK].
      rewrite Phys. iFrame "Pt1". }
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iModIntro. iExists -[((l, pctx_set K x₀ (gtr b)), ζm); zr]. iFrame "L I".
    iSplitR "Obs Obs'".
    { iSplitR "Tr"; [|iSplitL; [|done]].
      - rewrite /tctx_elt_interp. iExists #l. iSplit; [done|].
        iExists (D `max` (S (pctx_dlev K) + dr)), dn, gn. iFrame "⧖D ⧗p Fr Own".
        iSplit; [done|]. iPureIntro; lia.
      - iExists #lb.1, dr. iFrame "⧖r Tr". by rewrite Hpr. }
    iCombine "Obs Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=> π [Hπ HΦ].
    by apply Hπ.
  Qed.
  (** Copying a value of any size of a [Copy] type out of the leaf at the hole of [K]
      (below any number of unique borrows, in both modes of the hole), into a path [pw]
      that can be written (whose old value is resolved). The place does not change. *)
  Lemma type_memcpy_copy_from_oplace_deep_instr {𝔅 𝔄 ℭ ℭ' 𝔇} E L I pw p n (K: pctx 𝔅 𝔄)
      `{!PctxNoShr K} (ty: type 𝔅) (tyw: type ℭ) (tyw': type ℭ') (tyb: type 𝔇) gtw stw Φ
      (sz: Z) :
    Copy ty → typed_write E L tyw tyb tyw' ty gtw stw → resolve' E L tyb Φ →
    sz = ty_size ty → lctx_lft_alive E L (pctx_ulft K (OfTy ty)) →
    typed_instr E L I +[pw ◁ tyw; p ◁ₗown{n} pctx_plug K (OfTy ty)] (pw <-{sz} !(pctx_expr K p))
      (λ _, +[pw ◁ tyw'; p ◁ₗown{n} pctx_plug K (OfTy ty)])
      (λ post '-[a; x], λ mask π, Φ (gtw a) π (∀ zw, stw a (pctx_get K x.1.2) zw →
        post -[zw; x] mask π)).
  Proof.
    iIntros (Hcopy [Eq Wrt] Rslv -> Alv tid post mask iκs [a [x []]])
      "#LFT #TIME #PROPH #UNIQ #E L I (Tw & Tp & _) Obs".
    destruct x as [[l x₀] ζm].
    iDestruct (Alv with "L E") as "#Alv".
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iMod (fractional.frac_split_guard_in_half with "H2 Ghalf")
      as (γ2) "[H2 [H3 [#Ghalf2 #Halfback2]]]"; [solve_ndisj|].
    iAssert (fractional.half γ2 &&{↑NllftG}&&> @[pctx_ulft K (OfTy ty)])%I as "#Hu".
    { iApply (guards_transitive with "Ghalf2 Alv"). }
    wp_bind pw. iApply (wp_hasty with "Tw"). iIntros (vw dw Hpw) "#⧖w Tw".
    iMod (Wrt with "LFT UNIQ E Ghalf H1 Tw") as (lw dw' HW Heqv Hdw) "[Old (HW & #Hwpt & Totyw)]".
    injection Heqv as ->.
    rewrite /tctx_elt_interp.
    iDestruct "Tp" as (v Hp D d g) "(#⧖ & ⧗p & -> & %Hle & Fr & Own)".
    have ?: Closed [] (pctx_expr K p).
    { apply pctx_expr_closed. by eapply eval_path_closed. }
    (* The first step gives the credits. *)
    iCombine "⧖ ⧖w" as "⧖m".
    iApply wp_fupd. iApply (wp_cumulative_time_receipt_linear with "TIME ⧖m"); [solve_ndisj|].
    iIntros "⧗".
    set M := D `max` dw.
    iDestruct (cumulative_time_receipt_sep 1 (S M) with "⧗") as "[⧗c1 ⧗]".
    iDestruct (cumulative_time_receipt_sep 1 M with "⧗") as "[⧗c2 _]".
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗c1 ⧖m") as "[#⧖S £]";
      [solve_ndisj|].
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗c2 ⧖m") as "[_ £']";
      [solve_ndisj|].
    iCombine "£ £'" as "£".
    iDestruct (persistent_time_receipt_mono (S M) with "⧖S") as "#⧖S'"; [lia|].
    set lr := (l, repeat [] (lty_size (pctx_plug K (OfTy ty)))).
    set y := pctx_get K x₀.
    have HM: S d ≤ M ∧ g ≤ M ∧ dw ≤ M by rewrite /M; lia.
    iDestruct (lc_weaken ((d + 2) * (d + 3) + (3 * (g + 1) * M + ((1 + (1 + (1 + dw'*(dw+1)))) +
      (6 * S M + (2*M*M + 4*M + 2))))) with "£")
      as "[£a [£w [[£o [£r £s]] [£m £t]]]]"; [rewrite /advance_credits; nia|].
    iMod (oplace_leaf_acc K ty x₀ ζm d g tid l (⊤ ∖ ↑advN) with "LFT PROPH UNIQ Hu H2 £a Own")
      as (G' dh gh) "(% & G' & %Hdh & #G'u & #Gw & Pt1 & Gho1 & P & #Gs & Cl)"; [solve_ndisj|].
    destruct Hdh as (Hdh & Hgh & Hin).
    iDestruct "Gho1" as "#Gho1".
    iDestruct (copy_concrete with "Gho1") as %Hconc.
    set lK := pctx_loc K (ty_size ty) x₀ lr.
    (* The address of the hole. *)
    wp_bind (pctx_expr K p).
    iApply (wp_wand with "[P G' £w]").
    { iApply (wp_pctx_ptrs _ K (ty_size ty) (g + 1) G' x₀ lr p True%I with "[] Gs [£w] [G'] P");
        [solve_ndisj| | |].
      - iEval (rewrite /lr -heap_cloc_mapsto_empty). iApply guards_true.
      - iApply (lc_weaken with "£w"). nia.
      - iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->". by iFrame. }
    iIntros (w) "(-> & _ & G' & P)".
    (* Resolve the old value of the destination. *)
    iMod (lc_fupd_elim_later with "£o Old") as "Old".
    iMod (guarded_upd_run with "Ghalf2 H3 Old") as "[H3 (%vl & Ptw & Gb & %Physb)]";
      [solve_ndisj|].
    have Hlenw: length vl = ty_size ty by rewrite -Physb ty_size_eq Eq.
    iDestruct (Rslv _ (⊤ ∖ (⊤ ∖ ↑Nllft ∖ ↑prophN ∖ ↑timeN ∖ ↑uniqN))
      with "LFT PROPH UNIQ TIME E Ghalf2 H3 Gb") as "ToObs"; [set_solver|].
    iMod (lc_fupd_elim_later with "£r ToObs") as "ToObs".
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iDestruct (lc_step_fupdN_elim_later with "£s ToObs") as "ToObs".
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iMod (fupd_mask_mono with "ToObs") as "[Obs' H3]"; [solve_ndisj|].
    (* Copy. *)
    iMod (mapsto_vec_untether _ _ _ ∅ with "Ptw") as (vlw) "[Ptw [%Hvlw _]]".
    set vlc := to_concrete (ty_phys ty y tid).
    have Hlenc: length vlc = ty_size ty by rewrite /vlc length_to_concrete ty_size_eq.
    iApply (wp_memcpy_guarded _ lw lK vlw vlc HW (G' ∗ lK #↦!∗ ty_phys ty y tid) _ (S M)
      with "TIME [Ptw Pt1 G' HW £m]"); [solve_ndisj|lia|lia| |].
    { iFrame "Ptw Pt1 G' HW ⧖S' £m". iSplit.
      - iApply (lguards_weaken_later with "Hwpt"). lia.
      - iApply (guard_cloc_combine with "[] []").
        + iApply guards_weaken_lhs_sep_l. iApply (lguards_weaken_later with "Gw"). lia.
        + iApply (lguards_weaken_later _ _ _ 0); [lia|].
          rewrite -heap_complete_mapsto_fancy_fmap_eq /vlc fmap_to_concrete //.
          iApply guards_weaken_sep_r. }
    iIntros "!> (Ptw & HW & G' & Pt1)".
    iMod ("Totyw" $! y M with "[Ptw] ⧖S' £t HW") as (zw) "(H1 & %Hzw & Tw)".
    { iNext. iExists (ty_phys ty y tid).
      rewrite -heap_complete_mapsto_fancy_fmap_eq /vlc fmap_to_concrete //. iFrame "Ptw".
      iSplit; [|done].
      iDestruct (ty_gho_own_depth_mono _ dh gh M (S M) with "Gho1") as "[$ _]"; lia. }
    (* Close the place at the same value. *)
    iDestruct ("Cl" $! y dh gh d g with "[%] [] G' P Pt1 Gho1") as "Cl"; [lia| |].
    { iApply (persistent_time_receipt_mono with "⧖"). lia. }
    iMod (fupd_mask_mono with "Cl") as "[Own H2]"; [solve_ndisj|].
    iMod (fupd_mask_mono with "(Halfback2 H2 H3)") as "H2"; [solve_ndisj|].
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iEval (rewrite /y (pctx_set_get K x₀) //) in "Own".
    iModIntro. iExists -[zw; ((l, x₀), ζm)]. iFrame "L I".
    iSplitR "Obs Obs'".
    { iSplitL "Tw"; [|iSplitL; [|done]].
      - iExists #lw.1, (dw `max` S M). iSplit; [by rewrite Hpw|].
        iSplit; [iApply (persistent_time_receipt_mono with "⧖S'"); lia|].
        iDestruct "Tw" as "[Gw' Physw]". iFrame "Physw".
        iDestruct (ty_gho_own_depth_mono with "Gw'") as "[$ _]"; lia.
      - rewrite /tctx_elt_interp. iExists #l. iSplit; [done|].
        iExists D, d, g. by iFrame "⧖ ⧗p Fr Own". }
    iCombine "Obs Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=> π [Hπ HΦ].
    apply HΦ in Hπ. by apply Hπ.
  Qed.
End memcpy_deep.

(** * Values of any size below shared references *)

Section memcpy_pshr.
  Context `{!typeG Σ}.

  (** Copying a value of any size of a [Copy] type out of the hole of [K2], below the
      shared reference at the hole of [K] (both at any path), into a path [pw] that can
      be written (whose old value is resolved). The place does not change. The first
      step ([Skip]) gives the credits for the address ([wp_pshr_addr]), the copy the
      others. *)
  Lemma type_memcpy_copy_from_oplace_pshr_instr {ℭ 𝔅 𝔄 𝔇 𝔈 𝔈'} E L I pw p n
      (K: pctx (at_clocₛ 𝔅) 𝔄) `{!PctxNoShr K} κ (K2: pctx ℭ 𝔅) (lt: lty ℭ)
      (tyw: type 𝔈) (tyw': type 𝔈') (tyb: type 𝔇) gtw stw Φ (sz: Z) :
    Copy (lty_fold lt) → typed_write E L tyw tyb tyw' (lty_fold lt) gtw stw →
    resolve' E L tyb Φ → sz = ty_size (lty_fold lt) →
    lctx_lft_alive E L (pctx_ulft K (ShrLty (pctx_plug K2 lt) κ)) →
    lctx_lft_alive E L (pctx_salv K2 κ) →
    typed_instr E L I +[pw ◁ tyw; p ◁ₗown{n} pctx_plug K (ShrLty (pctx_plug K2 lt) κ)]
      (Seq Skip (pw <-{sz} !(pctx_expr K2 (!(pctx_expr K p)))))%E
      (λ _, +[pw ◁ tyw'; p ◁ₗown{n} pctx_plug K (ShrLty (pctx_plug K2 lt) κ)])
      (λ post '-[a; x], λ mask π, Φ (gtw a) π (∀ zw,
        stw a (pctx_get K2 (pctx_get K x.1.2).2) zw → post -[zw; x] mask π)).
  Proof.
    iIntros (Hcopy [Eq Wrt] Rslv -> Alv1 Alv2 tid post mask iκs [a [x []]])
      "#LFT #TIME #PROPH #UNIQ #E L I (Tw & Tp & _) Obs".
    destruct x as [[l x₀] ζm].
    rewrite /tctx_elt_interp.
    iDestruct "Tp" as (v Hp D d g) "(#⧖ & ⧗p & -> & %Hle & Fr & Own)".
    have ?: Closed [] (pctx_expr K p).
    { apply pctx_expr_closed. by eapply eval_path_closed. }
    have ?: Closed [] (pctx_expr K2 (!(pctx_expr K p))%E).
    { apply pctx_expr_closed. apply _. }
    iDestruct "Tw" as (vw dw Hpw) "(#⧖w & Tw)".
    have ?: Closed [] pw by eapply eval_path_closed.
    iDestruct (Alv1 with "L E") as "#Alv1". iDestruct (Alv2 with "L E") as "#Alv2".
    (* A step, for the credits of the address. *)
    wp_bind Skip. iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [set_solver|].
    iIntros "£ #⧖S". wp_let. iModIntro. wp_let.
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iMod (fractional.frac_split_guard_in_half with "H2 Ghalf")
      as (γ2) "[H2 [H3 [#Ghalf2 #Halfback2]]]"; [solve_ndisj|].
    iAssert (fractional.half γ2 &&{↑NllftG}&&> @[pctx_ulft K (ShrLty (pctx_plug K2 lt) κ)])%I
      as "#Hu". { iApply (guards_transitive with "Ghalf2 Alv1"). }
    iAssert (fractional.half γ2 &&{↑NllftG}&&> @[pctx_salv K2 κ])%I as "#Hs".
    { iApply (guards_transitive with "Ghalf2 Alv2"). }
    iAssert (fractional.half γ2 &&{↑NllftG}&&> @[pctx_slft K2 κ])%I as "#Hsl".
    { iApply (guards_transitive with "Hs"). iApply pctx_salv_slft. }
    iDestruct (lc_weaken (pshr_cred D + (g + 1)) with "£") as "[£a £g]";
      [rewrite /pshr_cred /advance_credits; nia|].
    wp_bind pw. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->".
    iMod (Wrt with "LFT UNIQ E Ghalf H1 Tw") as (lw dw' HW Heqv Hdw) "[Old (HW & #Hwpt & Totyw)]".
    injection Heqv as ->.
    set y := pctx_get K x₀.
    wp_bind (pctx_expr K2 (!(pctx_expr K p))%E).
    iApply (wp_pshr_addr K κ K2 lt (pctx_plug K2 lt) x₀ ζm d g D tid l p (fractional.half γ2)
      with "LFT PROPH UNIQ Hu Hs H2 £a ⧖ [] Own"); [lia|lia|done|done|..].
    { iApply wp_wand; [by iApply wp_eval_path|]. by iIntros (?) "->". }
    iIntros (dh Hdh [Hin1 [Hin2 Hvin]]) "H2 Own #(Pt & Shr & Pers)".
    set z := pctx_get K2 y.2.
    set lK := pctx_loc K2 (lty_size lt) y.2 y.1.
    (* The (persistent) ownership of the value, from the sharing predicate. *)
    iDestruct (copy_shr with "Shr") as "#GGho".
    iDestruct (guards_transitive_right with "Hsl GGho") as "#GGho'".
    iAssert (|={⊤}=> ty_gho_own (lty_fold lt) z dh g tid ∗ fractional.half γ2)%I
      with "[H2 £g]" as ">[#Gho H2]".
    { leaf_open_laters "GGho'" with "H2" as "Gho1"; [solve_ndisj|].
      iMod (lc_fupd_add_laterN with "£g Gho1") as "[#Gho1 Hclose]".
      iMod ("Hclose" with "Gho1") as "$". by iModIntro. }
    iDestruct (copy_concrete with "Gho") as %Hconc.
    (* The copy gives the other credits. *)
    iCombine "⧖ ⧖w" as "⧖m".
    iApply wp_fupd. iApply (wp_persistent_time_receipt with "TIME ⧖m"); [solve_ndisj|].
    iIntros "£ #⧖S'".
    set M := D `max` dw.
    have HM: 1 ≤ M ∧ g ≤ M ∧ dw ≤ M by rewrite /M; lia.
    iDestruct (lc_weaken ((1 + (1 + (1 + dw'*(dw+1)))) + (6 * S M + (2*M*M + 4*M + 2))) with "£")
      as "[[£o [£r £s]] [£m £t]]"; [rewrite /advance_credits; nia|].
    (* Resolve the old value of the destination. *)
    iMod (lc_fupd_elim_later with "£o Old") as "Old".
    iMod (guarded_upd_run with "Ghalf2 H3 Old") as "[H3 (%vl & Ptw & Gb & %Physb)]";
      [solve_ndisj|].
    iDestruct (Rslv _ (⊤ ∖ (⊤ ∖ ↑Nllft ∖ ↑prophN ∖ ↑timeN ∖ ↑uniqN))
      with "LFT PROPH UNIQ TIME E Ghalf2 H3 Gb") as "ToObs"; [set_solver|].
    iMod (lc_fupd_elim_later with "£r ToObs") as "ToObs".
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iDestruct (lc_step_fupdN_elim_later with "£s ToObs") as "ToObs".
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iMod (fupd_mask_mono with "ToObs") as "[Obs' H3]"; [solve_ndisj|].
    (* Copy. *)
    iMod (mapsto_vec_untether _ _ _ ∅ with "Ptw") as (vlw) "[Ptw [%Hvlw _]]".
    set vlc := to_concrete (ty_phys (lty_fold lt) z tid).
    have Hlenw: length vl = ty_size (lty_fold lt) by rewrite -Physb ty_size_eq Eq.
    have Hlenc: length vlc = ty_size (lty_fold lt)
      by rewrite /vlc length_to_concrete ty_size_eq.
    iApply (wp_memcpy_guarded _ lw lK vlw vlc HW (fractional.half γ2) _ (S M)
      with "TIME [Ptw H2 HW £m]"); [solve_ndisj|lia|lia| |].
    { iFrame "Ptw H2 HW ⧖S' £m". iSplit.
      - iApply (lguards_weaken_later with "Hwpt"). lia.
      - iApply (lguards_weaken_later _ _ _ (g + 1)); [lia|].
        iApply (guards_transitive_right with "Hsl").
        rewrite -heap_mapsto_cells_fancy_fmap_eq /vlc fmap_to_concrete //. }
    iIntros "!> (Ptw & HW & H2)".
    iMod ("Totyw" $! z M with "[Ptw] ⧖S' £t HW") as (zw) "(H1 & %Hzw & Tw)".
    { iNext. iExists (ty_phys (lty_fold lt) z tid).
      rewrite -heap_complete_mapsto_fancy_fmap_eq /vlc fmap_to_concrete //. iFrame "Ptw".
      iSplit; [|done].
      iDestruct (ty_gho_own_depth_mono _ dh g M (S M) with "Gho") as "[$ _]"; lia. }
    iMod (fupd_mask_mono with "(Halfback2 H2 H3)") as "H2"; [solve_ndisj|].
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iModIntro. iExists -[zw; ((l, x₀), ζm)]. iFrame "L I".
    iSplitR "Obs Obs'".
    { iSplitL "Tw"; [|iSplitL; [|done]].
      - iExists #lw.1, (dw `max` S M). iSplit; [by rewrite Hpw|].
        iSplit; [iApply (persistent_time_receipt_mono with "⧖S'"); lia|].
        iDestruct "Tw" as "[Gw' Physw]". iFrame "Physw".
        iDestruct (ty_gho_own_depth_mono with "Gw'") as "[$ _]"; lia.
      - rewrite /tctx_elt_interp. iExists #l. iSplit; [done|].
        iExists D, d, g. by iFrame "⧖ ⧗p Fr Own". }
    iCombine "Obs Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=> π [Hπ HΦ].
    apply HΦ in Hπ. by apply Hπ.
  Qed.
End memcpy_pshr.

(** * Sums below unique borrows *)

Section sum_deep.
  Context `{!typeG Σ}.

  (** Reading the discriminant of the leaf at the hole of [K] (a sum, below any number of
      unique borrows, in both modes of the hole): the leaf becomes the sum place at the
      variant [i] of its value (in [Uniq] mode, the body of the innermost borrow is
      switched to the node of the sum place, [cpd_unfold_uniq]), and the program continues
      with branch [i]. The first step (the address) gives the credits. *)
  Lemma type_case_oplace_deep {𝔄l 𝔄 𝔅l 𝔇} E L I (C: cctx 𝔇) p n (K: pctx (Σ! 𝔄l) 𝔄)
      `{!PctxNoShr K} (tyl: typel 𝔄l) (T: tctx 𝔅l) el el' trl :
    IntoPlistc el el' → lctx_lft_alive E L (pctx_ulft K (OfTy (Σ! tyl))) →
    ([∗ nat] i < length 𝔄l, typed_body E L I C
      (p ◁ₗown{n} pctx_plug K (SumLty tyl i (OfTy (tyl +!! i))) +:: T) (el' -!! i) (trl -!! i)) -∗
    typed_body E L I C (p ◁ₗown{n} pctx_plug K (OfTy (Σ! tyl)) +:: T)
      (case: !(pctx_expr K p) of el)
      (λ post '(x -:: cl), let 'xinj i _ := to_xsum (pctx_get K x.1.2).1 in
        (trl -!! i) post (x -:: cl))%type.
  Proof.
    move=> -> Alv. iIntros "el".
    iIntros (tid [x xl] mask post iκs) "#LFT #TIME #PROPH #UNIQ #E L I C /=[Tp T] #Obs".
    destruct x as [[l x₀] ζm].
    rewrite /tctx_elt_interp.
    iDestruct "Tp" as (v Hp D d g) "(#⧖ & ⧗p & -> & %Hle & Fr & Own)".
    have ?: Closed [] (pctx_expr K p).
    { apply pctx_expr_closed. by eapply eval_path_closed. }
    destruct (pctx_get K x₀) as [s pad] eqn:Hy.
    destruct (to_xsum s) as [j a] eqn:Hj.
    have Hs: s = pinj j a. { by rewrite -(semi_iso' to_xsum of_xsum s) Hj. }
    subst s.
    iDestruct (Alv with "L E") as "#Alv".
    wp_bind (!(pctx_expr K p))%E.
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj|].
    iIntros "£ #⧖S". iApply wp_fupd.
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_ulft K (OfTy (Σ! tyl))])%I as "#Hu".
    { iApply (guards_transitive with "Ghalf Alv"). }
    set lr := (l, repeat [] (lty_size (pctx_plug K (OfTy (Σ! tyl))))).
    set lt' := SumLty tyl j (OfTy (tyl +!! j)).
    set r' := (prfn_sum j (inl (PlaceIn a)) pad : prfn (xsumₛ 𝔄l)).
    rewrite /ltype_own lty_pat_plug lty_rfn_plug.
    iDestruct (lc_weaken (pctx_acc_cred K 1 d + (3 * (g + 1) * D + (1 + 3 * (g + 1))))
      with "£") as "[£a [£w [£1 £r]]]";
      [have := pctx_acc_cred_le K 1 d; rewrite /advance_credits; nia|].
    iMod (pctx_acc K (OfTy (Σ! tyl)) 1 with "LFT PROPH UNIQ Hu H1 £a Own")
      as (G' dh gh) "(% & G' & #G'G & %Hdh & H & P & #Gs & #HG & Cl)"; [solve_ndisj|].
    destruct Hdh as (Hdh & Hgh & Hin).
    set lK := pctx_loc K (ty_size (Σ! tyl)) x₀ lr.
    iAssert (G' &&{↑NllftG}&&> @[pctx_ulft K (OfTy (Σ! tyl))])%I as "#G'u".
    { iApply (guards_transitive with "G'G Hu"). }
    iDestruct (pctx_hguard K (OfTy (Σ! tyl)) (ty_size (Σ! tyl)) x₀ l G' g with "G'u HG")
      as "#Gw".
    iAssert (G' &&{↑NllftG; g + 1}&&> cloc_take lK 1 #↦∗_)%I as "#Gt".
    { iEval (rewrite (heap_cloc_mapsto_emp_vec_app lK 1)) in "Gw".
      iApply (guards_weaken_rhs_sep_l with "Gw"). }
    (* The address of the hole. *)
    wp_bind (pctx_expr K p).
    iApply (wp_wand with "[P G' £w]").
    { iApply (wp_pctx_ptrs _ K (ty_size (Σ! tyl)) (g + 1) G' x₀ lr p True%I
        with "[] Gs [£w] [G'] P"); [solve_ndisj| | |].
      - iEval (rewrite /lr -heap_cloc_mapsto_empty). iApply guards_true.
      - iApply (lc_weaken with "£w"). nia.
      - iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->". by iFrame. }
    iIntros (w) "(-> & _ & G' & P)".
    have Hf: lty_fold lt' = lty_fold (OfTy (Σ! tyl)) by apply lty_fold_sum_ofty.
    have Hsz: lty_size lt' = lty_size (OfTy (Σ! tyl)) by apply lty_size_sum_ofty.
    have Hr': ∀ ζl, prfn_rsv (lty_rfn (OfTy (Σ! tyl)) (pctx_get K x₀) ζm (pctx_path K [])) ζl →
      prfn_rsv r' (ζl ++ []).
    { intros ζl _. rewrite /r' prfn_rsv_sum. apply prfn_rsv_in. }
    destruct (pctx_uend K) as [κ|] eqn:Hu.
    - (* The whole referent of the innermost borrow: read the tag in its body, then switch
         the body to the sum place. *)
      iEval (rewrite (pctx_kind_uniq K κ) //) in "H".
      iEval (rewrite /pctx_closer (pctx_kind_uniq K κ) //) in "Cl".
      iDestruct "H" as (? idx ->) "Body". rewrite Hy.
      iMod (fractional.frac_split_guard_in_half NllftG G' G' with "G' []")
        as (γ2) "[A [B [#Gh2 #Back2]]]"; [solve_ndisj|iApply guards_refl|].
      iAssert (G' &&{↑NllftG}&&> @[κ])%I as "#G'κ".
      { iApply (guards_transitive with "G'u"). by iApply pctx_ulft_uend. }
      iAssert (fractional.half γ2 &&{↑NllftG}&&> @[κ])%I as "#Aκ".
      { iApply (guards_transitive with "Gh2 G'κ"). }
      iAssert (fractional.half γ2 &&{↑NllftG}&&> @[ty_lft (Σ! tyl)%T])%I as "#Aty".
      { iApply (guards_transitive with "Gh2"). iApply (guards_transitive with "G'u").
        iApply (pctx_ulft_fold K (OfTy (Σ! tyl))). by eapply pctx_uend_ulfts_ne. }
      iMod (uniq_body_acc with "LFT UNIQ Aκ Body A") as "(Pl & ⧗1 & CloseB)"; [solve_ndisj|].
      iMod (lc_fupd_elim_later with "£1 Pl") as "Pl".
      iMod (uniq_payload_run with "Aty B Pl") as "(B & #⧖' & Gho1 & Pt1)"; [solve_ndisj|].
      iEval (rewrite split_pt_xsum_cells'') in "Pt1". iDestruct "Pt1" as "(Tag & Pay & Pad)".
      iApply (wp_read_na_guarded_cells_singleton _ (cloc_take lK 1).1 (cloc_take lK 1).2
        (fractional.half γ2 ∗ cloc_take lK 1 #↦∗ [ #j ]) #j (g + 1)
        with "[B Tag £r]"); [solve_ndisj| |].
      { iFrame "B Tag £r". iApply guard_cloc_combine.
        - iApply guards_weaken_lhs_sep_l. iApply (guards_transitive_right with "Gh2 Gt").
        - iApply (lguards_weaken_later _ _ _ 0); [lia|iApply guards_weaken_sep_r]. }
      iIntros "!> [B Tag]".
      iSpecialize ("CloseB" $! (pinj j a, pad) dh gh with "[Tag Pay Pad Gho1] ⧗1").
      { iNext. iFrame "⧖' Gho1". rewrite split_pt_xsum_cells''. iFrame. }
      iMod (fupd_mask_mono with "CloseB") as "[Body A]"; [solve_ndisj|].
      iMod (fupd_mask_mono with "(Back2 A B)") as "G'"; [solve_ndisj|].
      iMod (cpd_unfold_uniq lt' κ (pctx_hξi K x₀) (pinj j a, pad) r' dh gh tid lK
        with "LFT PROPH UNIQ G'κ G' [Body]") as "[Own G']"; [done|done|done| | | |solve_ndisj| |].
      { rewrite /r' prfn_rsv_sum. apply prfn_rsv_in. }
      { intros π. rewrite /r' prfn_den_sum /= prfn_den_in. by rewrite psum_map1_pinj. }
      { iIntros (d0 g0) "[Gho Pt] !>". rewrite lty_fold_sum_ofty.
        iApply (sum_ofty_unfold_own 0). rewrite /ltype_own /= /ofty_owned.
        iExists _. by iFrame. }
      { rewrite Hf /ltype_own /=. iExists _, idx. by iFrame. }
      iMod ("Cl" $! lt' (PatSum PatLeaf) r' dh gh d g [] 1%Qp True%I
        with "[//] [//] [%] [%] [] [] G' P [] [Own]") as "(Own & H1 & _)".
      { exact Hr'. }
      { lia. }
      { by iApply big_sepL_pat_ok_nil. }
      { iApply (persistent_time_receipt_mono with "⧖"). lia. }
      { done. }
      { iIntros "_ !>". by iFrame "Own". }
      iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|]. iModIntro.
      wp_case. { split; [lia|]. by rewrite Nat2Z.id -vlookup_lookup plistc_to_vec_lookup. }
      iDestruct (big_sepN_lookup _ _ j with "el") as "el".
      iApply ("el" $! _ (((l, x₀), ζm) -:: xl)
        with "LFT TIME PROPH UNIQ E L I C [-] []"); last first.
      { iApply proph_obs_impl; [|done]=>/= ?. by rewrite ?Hy /= to_xsum_pinj. }
      iFrame "T". iExists #l. iSplit; [done|]. iExists D, d, g. iFrame "⧖".
      rewrite (lty_nrc_plug_eq K (OfTy (Σ! tyl)) lt') // (lty_size_plug_eq K lt' (OfTy (Σ! tyl))) //.
      iFrame "⧗p Fr". iSplit; [done|]. iSplit; [done|].
      rewrite /ltype_own lty_pat_plug lty_rfn_plug Hy lty_rfn_sum_in. iExact "Own".
    - (* [Owned] mode. *)
      iEval (rewrite (pctx_kind_owned K) //) in "H".
      iEval (rewrite /pctx_closer (pctx_kind_owned K) //) in "Cl".
      set mh := pctx_hmode K 1.
      iDestruct "H" as (? ->) "[Pt1 Gho1]". rewrite Hy.
      iEval (rewrite split_pt_xsum_cells'') in "Pt1". iDestruct "Pt1" as "(Tag & Pay & Pad)".
      iApply (wp_read_na_guarded_cells_singleton _ (cloc_take lK 1).1 (cloc_take lK 1).2
        (G' ∗ cloc_take lK 1 #↦∗ [ #j ]) #j (g + 1) with "[G' Tag £r]"); [solve_ndisj| |].
      { iFrame "G' Tag £r". iApply guard_cloc_combine.
        - iApply guards_weaken_lhs_sep_l. iApply "Gt".
        - iApply (lguards_weaken_later _ _ _ 0); [lia|iApply guards_weaken_sep_r]. }
      iIntros "!> [G' Tag]".
      iMod ("Cl" $! lt' (PatSum PatLeaf) r' dh gh d g [] 1%Qp True%I
        with "[//] [//] [%] [%] [] [] G' P [] [Tag Pay Pad Gho1]") as "(Own & H1 & _)".
      { exact Hr'. }
      { lia. }
      { by iApply big_sepL_pat_ok_nil. }
      { iApply (persistent_time_receipt_mono with "⧖"). lia. }
      { done. }
      { iIntros "_ !>". iSplit; [|done]. iApply sum_ofty_unfold_own.
        iExists (pinj j a, pad). iSplit; [done|].
        rewrite /ofty_owned split_pt_xsum_cells''. by iFrame. }
      iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|]. iModIntro.
      wp_case. { split; [lia|]. by rewrite Nat2Z.id -vlookup_lookup plistc_to_vec_lookup. }
      iDestruct (big_sepN_lookup _ _ j with "el") as "el".
      iApply ("el" $! _ (((l, x₀), ζm) -:: xl)
        with "LFT TIME PROPH UNIQ E L I C [-] []"); last first.
      { iApply proph_obs_impl; [|done]=>/= ?. by rewrite ?Hy /= to_xsum_pinj. }
      iFrame "T". iExists #l. iSplit; [done|]. iExists D, d, g. iFrame "⧖".
      rewrite (lty_nrc_plug_eq K (OfTy (Σ! tyl)) lt') // (lty_size_plug_eq K lt' (OfTy (Σ! tyl))) //.
      iFrame "⧗p Fr". iSplit; [done|]. iSplit; [done|].
      rewrite /ltype_own lty_pat_plug lty_rfn_plug Hy lty_rfn_sum_in. iExact "Own".
  Qed.
End sum_deep.
