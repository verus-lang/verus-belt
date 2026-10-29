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
From lrust.typing Require Export type ltype lpath pctx_acc vplace place_own.
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

  (** The closer of [vplace_leaf_acc]: a new value [y'] of the leaf, with its cells and
      ownership, at new depths. *)
  Definition vplace_leaf_closer {𝔅 𝔄} (K: pctx 𝔅 𝔄) (ty: type 𝔅) (x₀: ~~𝔄) (ζm: blk_map)
      (D: nat) (tid: thread_id) (v: val) (E: coPset) (G G': iProp Σ) : iProp Σ :=
    ∀ y' dh' gh' D', ⌜D ≤ D' ∧ dh' + pctx_dlev K ≤ D' ∧ gh' ≤ D'⌝ -∗
      ⧖D' -∗ G' -∗ pctx_vptrs K (ty_size ty) x₀ -∗
      pctx_vloc K (ty_size ty) x₀ #↦!∗ ty_phys ty y' tid -∗
      ty_gho_own ty y' dh' gh' tid ={E}=∗
      vroot_own (pctx_plug K (OfTy ty)) (pctx_vrfn K x₀ ζm (inl (PlaceIn y'))) D' tid v ∗ G.

  (** The access to the leaf [OfTy ty] at the hole of [K] of a place rooted at a value (the
      first step of [K] is the root pointer), below any number of unique borrows, in both
      modes of the hole. The cells of the leaf are guarded by the returned token [G'], which
      also guards the lifetime of the enclosing borrows; the pointer cells on the path are
      returned to compute the address ([wp_pctx_vptrs]). *)
  Lemma vplace_leaf_acc {𝔅 𝔄} (K: pctx 𝔅 𝔄) `{!PctxNoShr K} `{!PctxVRoot K} (ty: type 𝔅)
      x₀ ζm D tid v E (G: iProp Σ) :
    Timeless G → lazyE ⊆ E →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[pctx_ulft K (OfTy ty)]) -∗ G -∗
    £((D + 1) * (D + 2) + 1) -∗
    vroot_own (pctx_plug K (OfTy ty)) (pctx_vrfn K x₀ ζm (inl (PlaceIn (pctx_get K x₀)))) D tid v
      ={E}=∗
    ∃ (G': iProp Σ) dh gh, ⌜Timeless G'⌝ ∗ G' ∗ ⌜v = #(pctx_vrloc K (ty_size ty) x₀).1⌝ ∗
      ⌜dh + pctx_dlev K ≤ D ∧ gh ≤ D ∧ pctx_in K x₀⌝ ∗
      (G' &&{↑NllftG}&&> @[pctx_ulft K (OfTy ty)]) ∗
      (G' &&{↑NllftG; D + 1}&&> pctx_vloc K (ty_size ty) x₀ #↦∗_) ∗
      pctx_vloc K (ty_size ty) x₀ #↦!∗ ty_phys ty (pctx_get K x₀) tid ∗
      ty_gho_own ty (pctx_get K x₀) dh gh tid ∗
      pctx_vptrs K (ty_size ty) x₀ ∗ pctx_vpguards K (ty_size ty) (D + 1) G' x₀ ∗
      vplace_leaf_closer K ty x₀ ζm D tid v E G G'.
  Proof.
    iIntros (? HE) "#LFT #PROPH #UNIQ #Gu G £ Own".
    have Hdl: 1 ≤ pctx_dlev K by apply pctx_vroot_dlev.
    have ?: ↑NllftG ⊆ E. { trans lazyE; [apply lazyE_NllftG|done]. }
    have ?: ↑Nllft ⊆ E. { trans lazyE; [rewrite /lazyE; solve_ndisj|done]. }
    set y := pctx_get K x₀.
    iDestruct (lc_weaken (pctx_vacc_cred K D + (D + 2)) with "£") as "[£a £]";
      [have := pctx_vacc_cred_le K D; nia|].
    iMod (vroot_acc K (OfTy ty) with "LFT PROPH UNIQ Gu G £a Own")
      as (G' dh gh) "(% & G' & #G'G & -> & %Hdh & H & P & #Gs & #HG & Cl)"; [done|].
    destruct Hdh as (Hdh & Hgh & Hin).
    iAssert (G' &&{↑NllftG}&&> @[pctx_ulft K (OfTy ty)])%I as "#G'u".
    { iApply (guards_transitive with "G'G Gu"). }
    iDestruct (pctx_vhguard K (OfTy ty) (ty_size ty) x₀ G' D with "G'u HG") as "#Gw".
    destruct (pctx_uend K) as [κ|] eqn:Hu.
    - (* The hole is the whole referent of the innermost borrow: open its body. *)
      iEval (rewrite (pctx_kind_uniq K κ) //) in "H".
      iEval (rewrite /pctx_vcloser (pctx_kind_uniq K κ) //) in "Cl".
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
      iFrame "B Gho1 Pt1 P". iSplit; [done|]. iSplit; [done|].
      iSplitR. { iApply (guards_transitive with "Gh2 G'u"). }
      iSplitR. { iApply (guards_transitive_right with "Gh2 Gw"). }
      iSplitR. { iApply (pctx_pguards_transfer with "Gh2 Gs"). }
      iIntros (y' dh' gh' D' (? & ? & ?)) "#⧖ B P Pt Gho".
      iSpecialize ("CloseB" $! y' dh' gh' with "[Pt Gho] ⧗1").
      { iNext. iFrame "Gho Pt". iApply (persistent_time_receipt_mono with "⧖"). lia. }
      iMod (fupd_mask_mono with "CloseB") as "[Body A]"; [done|].
      iMod (fupd_mask_mono with "(Back2 A B)") as "G'"; [done|].
      iMod ("Cl" $! (OfTy ty) (inl (PlaceIn y')) dh' gh' D' [] 1%Qp True%I
        with "[//] [//] [//] [%] [%] [] ⧖ G' P [] [Body]") as "(Own & G & _)".
      { intros ??. apply prfn_rsv_in. }
      { lia. }
      { iApply pat_ok_ulfts_leaf. }
      { done. }
      { iIntros "_ !>". iSplit; [|done]. iExists y', idx. by iFrame. }
      by iFrame "G Own".
    - (* The hole is in [Owned] mode. *)
      iEval (rewrite (pctx_kind_owned K) //) in "H".
      iEval (rewrite /pctx_vcloser (pctx_kind_owned K) //) in "Cl".
      have Hm := pctx_hmode_le K 0. set mh := pctx_hmode K 0.
      iDestruct "H" as (? ->) "[Pt1 Gho1]".
      iDestruct (lc_weaken mh with "£") as "£"; [lia|].
      iMod (lc_fupd_elim_laterN with "£ Gho1") as "Gho1".
      iModIntro. iExists G', dh, gh. iSplit; [done|]. iFrame "G' Gho1 Pt1 P".
      iSplit; [done|]. iSplit; [done|]. iSplitR; [done|]. iSplitR; [done|]. iSplitR; [done|].
      iIntros (y' dh' gh' D' (? & ? & ?)) "#⧖ G' P Pt Gho".
      iMod ("Cl" $! (OfTy ty) (inl (PlaceIn y')) dh' gh' D' [] 1%Qp True%I
        with "[//] [//] [//] [%] [%] [] ⧖ G' P [] [Pt Gho]") as "(Own & G & _)".
      { intros ??. apply prfn_rsv_in. }
      { lia. }
      { iApply pat_ok_ulfts_leaf. }
      { done. }
      { iIntros "_ !>". iSplit; [|done]. iExists y'. iSplit; [done|]. rewrite /ofty_owned.
        iFrame "Pt". by iApply bi.laterN_intro. }
      by iFrame "G Own".
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
  Lemma type_memcpy_vplace_deep_instr {𝔅 𝔄 ℭ ℭ'} E L I p pr (K: pctx 𝔅 𝔄) `{!PctxNoShr K} `{!PctxVRoot K}
      (ty: type 𝔅) (tyr: type ℭ) (tyr': type ℭ') gtr str Φ (sz: Z) :
    resolve E L ty Φ → typed_read E L tyr ty tyr' gtr str → sz = ty_size ty →
    lctx_lft_alive E L (pctx_ulft K (OfTy ty)) →
    typed_instr E L I +[p ◁ₗ pctx_plug K (OfTy ty); pr ◁ tyr] (pctx_vexpr K p <-{sz} !pr)
      (λ _, +[p ◁ₗ pctx_plug K (OfTy ty); pr ◁ tyr'])
      (λ post '-[x; b], λ mask π, Φ (pctx_get K x.1) π →
        ∀ zr, str b zr → post -[(pctx_set K x.1 (gtr b), x.2); zr] mask π).
  Proof.
    iIntros (Rslv Rd -> Alv tid post mask iκs [x [b []]])
      "#LFT #TIME #PROPH #UNIQ #E L I (Tp & Tr & _) Obs".
    destruct x as [x₀ ζm].
    rewrite /tctx_elt_interp.
    iDestruct "Tp" as (v Hp) "Tp". iEval (rewrite vplace_own_open) in "Tp".
    iDestruct "Tp" as (D) "(#⧖ & ⧗p & Own)". have Hdl := pctx_vroot_dlev K.
    iDestruct "Tr" as (vr dr Hpr) "(#⧖r & Tr)".
    have ?: Closed [] (pctx_vexpr K p).
    { apply pctx_vexpr_closed. by eapply eval_path_closed. }
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
    set y := pctx_get K x₀.
    have HM: D ≤ M ∧ dr ≤ M by rewrite /M; lia.
    iDestruct (lc_weaken (((D + 1) * (D + 2) + 1) + (3 * (D + 1) * M + ((1 + (1 + M * (D + 1))) +
      ((dr + 1) + (1 + (6 * (M + 1) + (1 + (M + 1)))))))) with "£")
      as "[£a [£w [[£r £s] [£d [£b [£m [£o £o']]]]]]]";
      [rewrite /advance_credits; nia|].
    iMod (vplace_leaf_acc K ty x₀ ζm D tid _ (⊤ ∖ ↑advN) with "LFT PROPH UNIQ Hu H1 £a Own")
      as (G' dh gh) "(% & G' & -> & %Hdh & #G'u & #Gw & Pt1 & Gho1 & P & #Gs & Cl)"; [solve_ndisj|].
    destruct Hdh as (Hdh & Hgh & Hin).
    set lK := pctx_vloc K (ty_size ty) x₀.
    (* The address of the hole, and the source. *)
    wp_bind (pctx_vexpr K p).
    iApply (wp_wand with "[P G' £w]").
    { iApply (wp_pctx_vptrs _ K (ty_size ty) (D + 1) G' x₀ p True%I with "Gs [£w] [G'] P");
        [solve_ndisj| |].
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
    iDestruct (cumulative_time_receipt_mono (pctx_dlev K) with "⧗k") as "⧗k"; [lia|].
    iMod (cumulative_persistent_time_receipt with "TIME ⧗k ⧖r") as "#⧖k"; [solve_ndisj|].
    set Dn := D `max` (pctx_dlev K + dr).
    iCombine "⧖ ⧖k" as "⧖D".
    iMod ("Cl" $! (gtr b) dr dr Dn with "[%] [] G' P [Pt1] Gb") as "[Own H1]".
    { rewrite /Dn. lia. }
    { iApply (persistent_time_receipt_mono with "⧖D"). rewrite /Dn. lia. }
    { rewrite (_: pctx_vloc K (ty_size ty) x₀ = (lK1, cK)); [|exact HlK].
      rewrite Phys. iFrame "Pt1". }
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iModIntro. iExists -[(pctx_set K x₀ (gtr b), ζm); zr]. iFrame "L I".
    iSplitR "Obs Obs'".
    { iSplitR "Tr"; [|iSplitL; [|done]].
      - iExists _. iSplit; [done|].
        iApply (vplace_own_close K _ _ _ Dn with "[] ⧗p");
          [iApply (persistent_time_receipt_mono with "⧖D"); rewrite /Dn; lia|].
        by rewrite pctx_get_set pctx_vrfn_set.
      - iExists #lb.1, dr. iFrame "⧖r Tr". by rewrite Hpr. }
    iCombine "Obs Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=> π [Hπ HΦ].
    by apply Hπ.
  Qed.

  Lemma type_memcpy_oplace_deep_instr {𝔅 𝔄 ℭ ℭ'} E L I p pr n (K: pctx 𝔅 𝔄) `{!PctxNoShr K}
      (ty: type 𝔅) (tyr: type ℭ) (tyr': type ℭ') gtr str Φ (sz: Z) :
    resolve E L ty Φ → typed_read E L tyr ty tyr' gtr str → sz = ty_size ty →
    lctx_lft_alive E L (pctx_ulft K (OfTy ty)) →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K (OfTy ty); pr ◁ tyr] (pctx_expr K p <-{sz} !pr)
      (λ _, +[p ◁ₗown{n} pctx_plug K (OfTy ty); pr ◁ tyr'])
      (λ post '-[x; b], λ mask π, Φ (pctx_get K x.1.2) π →
        ∀ zr, str b zr → post -[((x.1.1, pctx_set K x.1.2 (gtr b)), x.2); zr] mask π).
  Proof. intros. by apply (type_memcpy_vplace_deep_instr _ _ _ _ _ (POwn n K)). Qed.
  (** Copying a value of any size of a [Copy] type out of the leaf at the hole of [K]
      (below any number of unique borrows, in both modes of the hole), into a path [pw]
      that can be written (whose old value is resolved). The place does not change. *)
  Lemma type_memcpy_copy_from_vplace_deep_instr {𝔅 𝔄 ℭ ℭ' 𝔇} E L I pw p (K: pctx 𝔅 𝔄)
      `{!PctxNoShr K} `{!PctxVRoot K} (ty: type 𝔅) (tyw: type ℭ) (tyw': type ℭ') (tyb: type 𝔇) gtw stw Φ
      (sz: Z) :
    Copy ty → typed_write E L tyw tyb tyw' ty gtw stw → resolve' E L tyb Φ →
    sz = ty_size ty → lctx_lft_alive E L (pctx_ulft K (OfTy ty)) →
    typed_instr E L I +[pw ◁ tyw; p ◁ₗ pctx_plug K (OfTy ty)] (pw <-{sz} !(pctx_vexpr K p))
      (λ _, +[pw ◁ tyw'; p ◁ₗ pctx_plug K (OfTy ty)])
      (λ post '-[a; x], λ mask π, Φ (gtw a) π (∀ zw, stw a (pctx_get K x.1) zw →
        post -[zw; x] mask π)).
  Proof.
    iIntros (Hcopy [Eq Wrt] Rslv -> Alv tid post mask iκs [a [x []]])
      "#LFT #TIME #PROPH #UNIQ #E L I (Tw & Tp & _) Obs".
    destruct x as [x₀ ζm].
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
    iDestruct "Tp" as (v Hp) "Tp". iEval (rewrite vplace_own_open) in "Tp".
    iDestruct "Tp" as (D) "(#⧖ & ⧗p & Own)". have Hdl := pctx_vroot_dlev K.
    have ?: Closed [] (pctx_vexpr K p).
    { apply pctx_vexpr_closed. by eapply eval_path_closed. }
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
    set y := pctx_get K x₀.
    have HM: D ≤ M ∧ dw ≤ M by rewrite /M; lia.
    iDestruct (lc_weaken (((D + 1) * (D + 2) + 1) + (3 * (D + 1) * M + ((1 + (1 + (1 + dw'*(dw+1)))) +
      (6 * S M + (2*M*M + 4*M + 2))))) with "£")
      as "[£a [£w [[£o [£r £s]] [£m £t]]]]"; [rewrite /advance_credits; nia|].
    iMod (vplace_leaf_acc K ty x₀ ζm D tid _ (⊤ ∖ ↑advN) with "LFT PROPH UNIQ Hu H2 £a Own")
      as (G' dh gh) "(% & G' & -> & %Hdh & #G'u & #Gw & Pt1 & Gho1 & P & #Gs & Cl)"; [solve_ndisj|].
    destruct Hdh as (Hdh & Hgh & Hin).
    iDestruct "Gho1" as "#Gho1".
    iDestruct (copy_concrete with "Gho1") as %Hconc.
    set lK := pctx_vloc K (ty_size ty) x₀.
    (* The address of the hole. *)
    wp_bind (pctx_vexpr K p).
    iApply (wp_wand with "[P G' £w]").
    { iApply (wp_pctx_vptrs _ K (ty_size ty) (D + 1) G' x₀ p True%I with "Gs [£w] [G'] P");
        [solve_ndisj| |].
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
    iDestruct ("Cl" $! y dh gh D with "[%] ⧖ G' P Pt1 Gho1") as "Cl"; [lia|].
    iMod (fupd_mask_mono with "Cl") as "[Own H2]"; [solve_ndisj|].
    iMod (fupd_mask_mono with "(Halfback2 H2 H3)") as "H2"; [solve_ndisj|].
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iModIntro. iExists -[zw; (x₀, ζm)]. iFrame "L I".
    iSplitR "Obs Obs'".
    { iSplitL "Tw"; [|iSplitL; [|done]].
      - iExists #lw.1, (dw `max` S M). iSplit; [by rewrite Hpw|].
        iSplit; [iApply (persistent_time_receipt_mono with "⧖S'"); lia|].
        iDestruct "Tw" as "[Gw' Physw]". iFrame "Physw".
        iDestruct (ty_gho_own_depth_mono with "Gw'") as "[$ _]"; lia.
      - iExists _. iSplit; [done|].
        iApply (vplace_own_close with "⧖ ⧗p").
        by rewrite ?pctx_get_set ?pctx_vrfn_set. }
    iCombine "Obs Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=> π [Hπ HΦ].
    apply HΦ in Hπ. by apply Hπ.
  Qed.

  Lemma type_memcpy_copy_from_oplace_deep_instr {𝔅 𝔄 ℭ ℭ' 𝔇} E L I pw p n (K: pctx 𝔅 𝔄)
      `{!PctxNoShr K} (ty: type 𝔅) (tyw: type ℭ) (tyw': type ℭ') (tyb: type 𝔇) gtw stw Φ
      (sz: Z) :
    Copy ty → typed_write E L tyw tyb tyw' ty gtw stw → resolve' E L tyb Φ →
    sz = ty_size ty → lctx_lft_alive E L (pctx_ulft K (OfTy ty)) →
    typed_instr E L I +[pw ◁ tyw; p ◁ₗown{n} pctx_plug K (OfTy ty)] (pw <-{sz} !(pctx_expr K p))
      (λ _, +[pw ◁ tyw'; p ◁ₗown{n} pctx_plug K (OfTy ty)])
      (λ post '-[a; x], λ mask π, Φ (gtw a) π (∀ zw, stw a (pctx_get K x.1.2) zw →
        post -[zw; x] mask π)).
  Proof. intros. by eapply (type_memcpy_copy_from_vplace_deep_instr _ _ _ _ _ (POwn n K)). Qed.
End memcpy_deep.

(** * Values of any size below shared references *)

Section memcpy_pshr.
  Context `{!typeG Σ}.

  (** Copying a value of any size of a [Copy] type out of the hole of [K2], below the
      shared reference at the hole of [K] (both at any path), into a path [pw] that can
      be written (whose old value is resolved). The place does not change. The first
      step ([Skip]) gives the credits for the address ([wp_pshr_addr]), the copy the
      others. *)
  Lemma type_memcpy_copy_from_vplace_pshr_instr {ℭ 𝔅 𝔄 𝔇 𝔈 𝔈'} E L I pw p
      (K: pctx (at_clocₛ 𝔅) 𝔄) `{!PctxNoShr K} `{!PctxVRoot K} κ (K2: pctx ℭ 𝔅) (lt: lty ℭ)
      (tyw: type 𝔈) (tyw': type 𝔈') (tyb: type 𝔇) gtw stw Φ (sz: Z) :
    Copy (lty_fold lt) → typed_write E L tyw tyb tyw' (lty_fold lt) gtw stw →
    resolve' E L tyb Φ → sz = ty_size (lty_fold lt) →
    lctx_lft_alive E L (pctx_ulft K (ShrLty (pctx_plug K2 lt) κ)) →
    lctx_lft_alive E L (pctx_salv K2 κ) →
    typed_instr E L I +[pw ◁ tyw; p ◁ₗ pctx_plug K (ShrLty (pctx_plug K2 lt) κ)]
      (Seq Skip (pw <-{sz} !(pctx_expr K2 (!(pctx_vexpr K p)))))%E
      (λ _, +[pw ◁ tyw'; p ◁ₗ pctx_plug K (ShrLty (pctx_plug K2 lt) κ)])
      (λ post '-[a; x], λ mask π, Φ (gtw a) π (∀ zw,
        stw a (pctx_get K2 (pctx_get K x.1).2) zw → post -[zw; x] mask π)).
  Proof.
    iIntros (Hcopy [Eq Wrt] Rslv -> Alv1 Alv2 tid post mask iκs [a [x []]])
      "#LFT #TIME #PROPH #UNIQ #E L I (Tw & Tp & _) Obs".
    destruct x as [x₀ ζm].
    rewrite /tctx_elt_interp.
    iDestruct "Tp" as (v Hp) "Tp". iEval (rewrite vplace_own_open) in "Tp".
    iDestruct "Tp" as (D) "(#⧖ & ⧗p & Own)". have Hdl: 1 ≤ pctx_dlev K by apply pctx_vroot_dlev.
    have ?: Closed [] (pctx_vexpr K p).
    { apply pctx_vexpr_closed. by eapply eval_path_closed. }
    have ?: Closed [] (pctx_expr K2 (!(pctx_vexpr K p))%E).
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
    iDestruct (lc_weaken (pshr_cred D + (D + 1)) with "£") as "[£a £g]";
      [rewrite /pshr_cred /advance_credits; nia|].
    wp_bind pw. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->".
    iMod (Wrt with "LFT UNIQ E Ghalf H1 Tw") as (lw dw' HW Heqv Hdw) "[Old (HW & #Hwpt & Totyw)]".
    injection Heqv as ->.
    set y := pctx_get K x₀.
    wp_bind (pctx_expr K2 (!(pctx_vexpr K p))%E).
    iApply (wp_vpshr_addr K κ K2 lt (pctx_plug K2 lt) x₀ ζm D tid _ p (fractional.half γ2)
      with "LFT PROPH UNIQ Hu Hs H2 £a ⧖ [] Own"); [done|done|..].
    { iApply wp_wand; [by iApply wp_eval_path|]. by iIntros (?) "->". }
    iIntros (dh Hdh [Hin1 [Hin2 Hvin]]) "H2 Own #(Pt & Shr & Pers)".
    set z := pctx_get K2 y.2.
    set lK := pctx_loc K2 (lty_size lt) y.2 y.1.
    (* The (persistent) ownership of the value, from the sharing predicate. *)
    iDestruct (copy_shr with "Shr") as "#GGho".
    iDestruct (guards_transitive_right with "Hsl GGho") as "#GGho'".
    iAssert (|={⊤}=> ty_gho_own (lty_fold lt) z dh D tid ∗ fractional.half γ2)%I
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
    have HM: 1 ≤ M ∧ D ≤ M ∧ dw ≤ M by rewrite /M; lia.
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
      - iApply (lguards_weaken_later _ _ _ (D + 1)); [lia|].
        iApply (guards_transitive_right with "Hsl").
        rewrite -heap_mapsto_cells_fancy_fmap_eq /vlc fmap_to_concrete //. }
    iIntros "!> (Ptw & HW & H2)".
    iMod ("Totyw" $! z M with "[Ptw] ⧖S' £t HW") as (zw) "(H1 & %Hzw & Tw)".
    { iNext. iExists (ty_phys (lty_fold lt) z tid).
      rewrite -heap_complete_mapsto_fancy_fmap_eq /vlc fmap_to_concrete //. iFrame "Ptw".
      iSplit; [|done].
      iDestruct (ty_gho_own_depth_mono _ dh D M (S M) with "Gho") as "[$ _]"; lia. }
    iMod (fupd_mask_mono with "(Halfback2 H2 H3)") as "H2"; [solve_ndisj|].
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iModIntro. iExists -[zw; (x₀, ζm)]. iFrame "L I".
    iSplitR "Obs Obs'".
    { iSplitL "Tw"; [|iSplitL; [|done]].
      - iExists #lw.1, (dw `max` S M). iSplit; [by rewrite Hpw|].
        iSplit; [iApply (persistent_time_receipt_mono with "⧖S'"); lia|].
        iDestruct "Tw" as "[Gw' Physw]". iFrame "Physw".
        iDestruct (ty_gho_own_depth_mono with "Gw'") as "[$ _]"; lia.
      - iExists _. iSplit; [done|].
        by iApply (vplace_own_close with "⧖ ⧗p"). }
    iCombine "Obs Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=> π [Hπ HΦ].
    apply HΦ in Hπ. by apply Hπ.
  Qed.

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
  Proof. intros. by eapply (type_memcpy_copy_from_vplace_pshr_instr _ _ _ _ _ (POwn n K)). Qed.
End memcpy_pshr.

(** * Sums below unique borrows *)

Section sum_deep.
  Context `{!typeG Σ}.

  (** Reading the discriminant of the leaf at the hole of [K] (a sum, below any number of
      unique borrows, in both modes of the hole): the leaf becomes the sum place at the
      variant [i] of its value (in [Uniq] mode, the body of the innermost borrow is
      switched to the node of the sum place, [cpd_unfold_uniq]), and the program continues
      with branch [i]. The first step (the address) gives the credits. *)
  Lemma type_case_vplace_deep {𝔄l 𝔄 𝔅l 𝔇} E L I (C: cctx 𝔇) p (K: pctx (Σ! 𝔄l) 𝔄)
      `{!PctxNoShr K} `{!PctxVRoot K} (tyl: typel 𝔄l) (T: tctx 𝔅l) el el' trl :
    IntoPlistc el el' → lctx_lft_alive E L (pctx_ulft K (OfTy (Σ! tyl))) →
    ([∗ nat] i < length 𝔄l, typed_body E L I C
      (p ◁ₗ pctx_plug K (SumLty tyl i (OfTy (tyl +!! i))) +:: T) (el' -!! i) (trl -!! i)) -∗
    typed_body E L I C (p ◁ₗ pctx_plug K (OfTy (Σ! tyl)) +:: T)
      (case: !(pctx_vexpr K p) of el)
      (λ post '(x -:: cl), let 'xinj i _ := to_xsum (pctx_get K x.1).1 in
        (trl -!! i) post (x -:: cl))%type.
  Proof.
    move=> -> Alv. iIntros "el".
    iIntros (tid [x xl] mask post iκs) "#LFT #TIME #PROPH #UNIQ #E L I C /=[Tp T] #Obs".
    destruct x as [x₀ ζm].
    rewrite /tctx_elt_interp.
    iDestruct "Tp" as (v Hp) "Tp". iEval (rewrite vplace_own_open) in "Tp".
    iDestruct "Tp" as (D) "(#⧖ & ⧗p & Own)". have Hdl := pctx_vroot_dlev K.
    have ?: Closed [] (pctx_vexpr K p).
    { apply pctx_vexpr_closed. by eapply eval_path_closed. }
    destruct (pctx_get K x₀) as [s pad] eqn:Hy.
    destruct (to_xsum s) as [j a] eqn:Hj.
    have Hs: s = pinj j a. { by rewrite -(semi_iso' to_xsum of_xsum s) Hj. }
    subst s.
    iDestruct (Alv with "L E") as "#Alv".
    wp_bind (!(pctx_vexpr K p))%E.
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj|].
    iIntros "£ #⧖S". iApply wp_fupd.
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_ulft K (OfTy (Σ! tyl))])%I as "#Hu".
    { iApply (guards_transitive with "Ghalf Alv"). }
    set lt' := SumLty tyl j (OfTy (tyl +!! j)).
    set r' := (prfn_sum j (inl (PlaceIn a)) pad : prfn (xsumₛ 𝔄l)).
    iDestruct (lc_weaken (pctx_vacc_cred K D + (3 * (D + 1) * D + (1 + 3 * (D + 1))))
      with "£") as "[£a [£w [£1 £r]]]";
      [have := pctx_vacc_cred_le K D; rewrite /advance_credits; nia|].
    iMod (vroot_acc K (OfTy (Σ! tyl)) with "LFT PROPH UNIQ Hu H1 £a Own")
      as (G' dh gh) "(% & G' & #G'G & -> & %Hdh & H & P & #Gs & #HG & Cl)"; [solve_ndisj|].
    destruct Hdh as (Hdh & Hgh & Hin).
    set lK := pctx_vloc K (ty_size (Σ! tyl)) x₀.
    iAssert (G' &&{↑NllftG}&&> @[pctx_ulft K (OfTy (Σ! tyl))])%I as "#G'u".
    { iApply (guards_transitive with "G'G Hu"). }
    iDestruct (pctx_vhguard K (OfTy (Σ! tyl)) (ty_size (Σ! tyl)) x₀ G' D with "G'u HG")
      as "#Gw".
    iAssert (G' &&{↑NllftG; D + 1}&&> cloc_take lK 1 #↦∗_)%I as "#Gt".
    { iEval (rewrite (heap_cloc_mapsto_emp_vec_app lK 1)) in "Gw".
      iApply (guards_weaken_rhs_sep_l with "Gw"). }
    (* The address of the hole. *)
    wp_bind (pctx_vexpr K p).
    iApply (wp_wand with "[P G' £w]").
    { iApply (wp_pctx_vptrs _ K (ty_size (Σ! tyl)) (D + 1) G' x₀ p True%I with "Gs [£w] [G'] P");
        [solve_ndisj| |].
      - iApply (lc_weaken with "£w"). nia.
      - iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->". by iFrame. }
    iIntros (w) "(-> & _ & G' & P)".
    have Hf: lty_fold lt' = lty_fold (OfTy (Σ! tyl)) by apply lty_fold_sum_ofty.
    have Hsz: lty_size lt' = lty_size (OfTy (Σ! tyl)) by apply lty_size_sum_ofty.
    have Hr': ∀ ζl, prfn_rsv (lty_rfn (OfTy (Σ! tyl)) (pctx_get K x₀) ζm (pctx_vpath K)) ζl →
      prfn_rsv r' (ζl ++ []).
    { intros ζl _. rewrite /r' prfn_rsv_sum. apply prfn_rsv_in. }
    destruct (pctx_uend K) as [κ|] eqn:Hu.
    - (* The whole referent of the innermost borrow: read the tag in its body, then switch
         the body to the sum place. *)
      iEval (rewrite (pctx_kind_uniq K κ) //) in "H".
      iEval (rewrite /pctx_vcloser (pctx_kind_uniq K κ) //) in "Cl".
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
        (fractional.half γ2 ∗ cloc_take lK 1 #↦∗ [ #j ]) #j (D + 1)
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
      iMod ("Cl" $! lt' r' dh gh D [] 1%Qp True%I
        with "[//] [//] [//] [%] [%] [] ⧖ G' P [] [Own]") as "(Own & H1 & _)".
      { exact Hr'. }
      { lia. }
      { by iApply big_sepL_pat_ok_nil. }
      { done. }
      { iIntros "_ !>". by iFrame "Own". }
      iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|]. iModIntro.
      wp_case. { split; [lia|]. by rewrite Nat2Z.id -vlookup_lookup plistc_to_vec_lookup. }
      iDestruct (big_sepN_lookup _ _ j with "el") as "el".
      iApply ("el" $! _ ((x₀, ζm) -:: xl)
        with "LFT TIME PROPH UNIQ E L I C [-] []"); last first.
      { iApply proph_obs_impl; [|done]=>/= ?. by rewrite ?Hy /= to_xsum_pinj. }
      iFrame "T". iExists _. iSplit; [done|].
      iApply (vplace_own_close with "⧖ [⧗p]");
        [by rewrite (lty_vnrc_plug_eq K lt' (OfTy (Σ! tyl)))|].
      rewrite Hy lty_rfn_sum_in. iExact "Own".
    - (* [Owned] mode. *)
      iEval (rewrite (pctx_kind_owned K) //) in "H".
      iEval (rewrite /pctx_vcloser (pctx_kind_owned K) //) in "Cl".
      set mh := pctx_hmode K 0.
      iDestruct "H" as (? ->) "[Pt1 Gho1]". rewrite Hy.
      iEval (rewrite split_pt_xsum_cells'') in "Pt1". iDestruct "Pt1" as "(Tag & Pay & Pad)".
      iApply (wp_read_na_guarded_cells_singleton _ (cloc_take lK 1).1 (cloc_take lK 1).2
        (G' ∗ cloc_take lK 1 #↦∗ [ #j ]) #j (D + 1) with "[G' Tag £r]"); [solve_ndisj| |].
      { iFrame "G' Tag £r". iApply guard_cloc_combine.
        - iApply guards_weaken_lhs_sep_l. iApply "Gt".
        - iApply (lguards_weaken_later _ _ _ 0); [lia|iApply guards_weaken_sep_r]. }
      iIntros "!> [G' Tag]".
      iMod ("Cl" $! lt' r' dh gh D [] 1%Qp True%I
        with "[//] [//] [//] [%] [%] [] ⧖ G' P [] [Tag Pay Pad Gho1]") as "(Own & H1 & _)".
      { exact Hr'. }
      { lia. }
      { by iApply big_sepL_pat_ok_nil. }
      { done. }
      { iIntros "_ !>". iSplit; [|done]. iApply sum_ofty_unfold_own.
        iExists (pinj j a, pad). iSplit; [done|].
        rewrite /ofty_owned split_pt_xsum_cells''. by iFrame. }
      iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|]. iModIntro.
      wp_case. { split; [lia|]. by rewrite Nat2Z.id -vlookup_lookup plistc_to_vec_lookup. }
      iDestruct (big_sepN_lookup _ _ j with "el") as "el".
      iApply ("el" $! _ ((x₀, ζm) -:: xl)
        with "LFT TIME PROPH UNIQ E L I C [-] []"); last first.
      { iApply proph_obs_impl; [|done]=>/= ?. by rewrite ?Hy /= to_xsum_pinj. }
      iFrame "T". iExists _. iSplit; [done|].
      iApply (vplace_own_close with "⧖ [⧗p]");
        [by rewrite (lty_vnrc_plug_eq K lt' (OfTy (Σ! tyl)))|].
      rewrite Hy lty_rfn_sum_in. iExact "Own".
  Qed.

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
    iIntros (??) "el".
    iApply (type_case_vplace_deep E L I C p (POwn n K) tyl T el el' trl with "el"); done.
  Qed.
  (** Folding back a sum place whose payload is the leaf of its variant (both modes). *)
  Lemma vplace_conv_sum_fold {𝔄l 𝔄} (K: pctx (Σ! 𝔄l) 𝔄) (tyl: typel 𝔄l) i :
    vplace_conv K (SumLty tyl i (OfTy (tyl +!! i))) (OfTy (Σ! tyl)) (=).
  Proof.
    iIntros (x ζm dh gh D tid lh G E ? HE ??) "#LFT #PROPH #UNIQ _ #Gk G _ _ _ H".
    iModIntro. iExists (pctx_get K x), [], 1%Qp. iSplit; [done|]. iSplit.
    { iPureIntro. intros ??. apply prfn_rsv_in. }
    iSplitR; [done|]. iIntros "_".
    destruct (pctx_uend K) as [κ|] eqn:Hu.
    - rewrite (pctx_kind_uniq K κ) //. rewrite -(lty_fold_sum_ofty tyl i).
      iApply (cpd_fold_uniq (SumLty tyl i (OfTy (tyl +!! i))) with "LFT PROPH UNIQ [] G H");
        [done| |trans lazyE; [rewrite /lazyE; solve_ndisj|set_solver]|].
      + iIntros (d' g') "N". iDestruct (sum_ofty_own_rfn 0 with "N") as "N".
        rewrite lty_fold_sum_ofty /ltype_own /= /ofty_owned. iDestruct "N" as (? ->) "[$ $]".
        done.
      + iApply (guards_transitive with "Gk"). iApply llftl_incl_trans; [iApply llftl_intersect_incl_l|].
        by iApply pctx_ulft_uend.
    - rewrite (pctx_kind_owned K) //. iModIntro. iFrame "G". by iApply sum_ofty_own_rfn.
  Qed.

  Lemma type_fold_vplace_sum_deep_instr {𝔄l 𝔄} E L I p (K: pctx (Σ! 𝔄l) 𝔄) `{!PctxNoShr K} `{!PctxVRoot K}
      (tyl: typel 𝔄l) i :
    lctx_lft_alive E L (pctx_ulft K (SumLty tyl i (OfTy (tyl +!! i))) ⊓ ty_lft (Σ! tyl)%T) →
    typed_instr E L I +[p ◁ₗ pctx_plug K (SumLty tyl i (OfTy (tyl +!! i)))] (Seq Skip Skip)
      (const +[p ◁ₗ pctx_plug K (OfTy (Σ! tyl))])
      (λ post '-[x], post -[x]).
  Proof.
    intros Alv. eapply typed_instr_tr_impl; [|apply (type_change_vplace_instr _ _ _ _ K _ _ (=));
      [by rewrite lty_fold_sum_ofty|by rewrite lty_fold_sum_ofty|by rewrite lty_size_sum_ofty|
       done|done|done|apply vplace_conv_sum_fold]].
    intros post [[x₀ ζm] []] mask π Hπ [x₀' ζm'] Hζ Hin (y' & <- & Hx).
    simpl in *. subst. by rewrite pctx_set_get.
  Qed.

  Lemma type_fold_oplace_sum_deep_instr {𝔄l 𝔄} E L I p n (K: pctx (Σ! 𝔄l) 𝔄) `{!PctxNoShr K}
      (tyl: typel 𝔄l) i :
    lctx_lft_alive E L (pctx_ulft K (SumLty tyl i (OfTy (tyl +!! i))) ⊓ ty_lft (Σ! tyl)%T) →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K (SumLty tyl i (OfTy (tyl +!! i)))] (Seq Skip Skip)
      (const +[p ◁ₗown{n} pctx_plug K (OfTy (Σ! tyl))])
      (λ post '-[x], post -[x]).
  Proof. intros. by apply (type_fold_vplace_sum_deep_instr _ _ _ _ (POwn n K)). Qed.
  (** Assigning a variant [i] with a payload of size 1 to the leaf at the hole of [K] (a
      sum, below any number of unique borrows, in both modes), keeping the type of the
      leaf: the old value is resolved, the tag and the payload are written (the address
      is computed twice), the padding keeps its contents. *)
  Lemma type_sum_assign_vplace_deep_instr {𝔄l 𝔄} E L I p q (K: pctx (Σ! 𝔄l) 𝔄)
      `{!PctxNoShr K} `{!PctxVRoot K} (tyl: typel 𝔄l) (i: fin (length 𝔄l)) Φ :
    ty_size (tyl +!! i) = 1%nat → resolve E L (Σ! tyl) Φ →
    lctx_lft_alive E L (pctx_ulft K (OfTy (Σ! tyl))) →
    typed_instr E L I +[p ◁ₗ pctx_plug K (OfTy (Σ! tyl)); q ◁ tyl +!! i]
      (pctx_vexpr K p <-{Σ i} q)
      (λ _, +[p ◁ₗ pctx_plug K (OfTy (Σ! tyl))])
      (λ post '-[x; b], λ mask π, Φ (pctx_get K x.1) π → ∀ pad,
        post -[(pctx_set K x.1 (pinj i b, pad), x.2)] mask π).
  Proof.
    iIntros (Hsz Rslv Alv tid post mask iκs [x [b []]])
      "#LFT #TIME #PROPH #UNIQ #E L I (Tp & Tb & _) Obs".
    destruct x as [x₀ ζm].
    rewrite /tctx_elt_interp.
    iDestruct "Tp" as (v Hp) "Tp". iEval (rewrite vplace_own_open) in "Tp".
    iDestruct "Tp" as (D) "(#⧖ & ⧗p & Own)". have Hdl := pctx_vroot_dlev K.
    iDestruct "Tb" as (vb db Hpb) "(#⧖b & Gb & %Phys)".
    have ?: Closed [] (pctx_vexpr K p).
    { apply pctx_vexpr_closed. by eapply eval_path_closed. }
    have ?: Closed [] q by eapply eval_path_closed.
    have HM1: 1 ≤ max_ty_size tyl.
    { rewrite -Hsz. apply (max_hlist_with_ge (λ _, ty_size) tyl i). }
    iDestruct (Alv with "L E") as "#Alv".
    (* The first step gives credits and cumulative time receipts. *)
    iCombine "⧖ ⧖b" as "⧖m".
    iApply (wp_cumulative_time_receipt_linear with "TIME ⧖m"); [solve_ndisj|].
    iIntros "⧗". iApply wp_fupd.
    set M := D `max` db.
    iDestruct (cumulative_time_receipt_sep 1 (S M) with "⧗") as "[⧗c1 ⧗]".
    iDestruct (cumulative_time_receipt_sep 1 M with "⧗") as "[⧗c2 ⧗k]".
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗c1 ⧖m") as "[_ £]";
      [solve_ndisj|].
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗c2 ⧖m") as "[_ £']";
      [solve_ndisj|].
    iCombine "£ £'" as "£".
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_ulft K (OfTy (Σ! tyl))])%I as "#Hu".
    { iApply (guards_transitive with "Ghalf Alv"). }
    set y := pctx_get K x₀.
    have HM: D ≤ M ∧ db ≤ M by rewrite /M; lia.
    iDestruct (lc_weaken (((D + 1) * (D + 2) + 1) + (3 * (D + 1) * M + (3 * (D + 1) * M +
      ((1 + (1 + M * (D + 1))) + (3 * (D + 1) + 3 * (D + 1)))))) with "£")
      as "[£a [£w [£w' [[£r £s] [£t1 £t2]]]]]"; [rewrite /advance_credits; nia|].
    iMod (vplace_leaf_acc K (Σ! tyl) x₀ ζm D tid _ (⊤ ∖ ↑advN)
      with "LFT PROPH UNIQ Hu H1 £a Own")
      as (G' dh gh) "(% & G' & -> & %Hdh & #G'u & #Gw & Pt1 & Gho1 & P & #Gs & Cl)"; [solve_ndisj|].
    destruct Hdh as (Hdh & Hgh & Hin).
    (* The address of the hole. *)
    wp_bind (pctx_vexpr K p).
    iApply (wp_wand with "[P G' £w]").
    { iApply (wp_pctx_vptrs _ K (ty_size (Σ! tyl)) (D + 1) G' x₀ p True%I with "Gs [£w] [G'] P");
        [solve_ndisj| |].
      - iApply (lc_weaken with "£w"). nia.
      - iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->". by iFrame. }
    iIntros (w) "(-> & _ & G' & P)".
    (* Resolve the old value. *)
    iDestruct (Rslv _ (⊤ ∖ (⊤ ∖ ↑Nllft ∖ ↑prophN ∖ ↑timeN ∖ ↑uniqN))
      with "LFT PROPH UNIQ TIME E Ghalf H2 Gho1") as "ToObs"; [set_solver|].
    iMod (lc_fupd_elim_later with "£r ToObs") as "ToObs".
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iDestruct (lc_step_fupdN_elim_later with "[£s] ToObs") as "ToObs".
    { iApply (lc_weaken with "£s"). nia. }
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iMod (fupd_mask_mono with "ToObs") as "[Obs' H2]"; [solve_ndisj|].
    (* Split the cells: tag, payload, padding. *)
    set lK := pctx_vloc K (ty_size (Σ! tyl)) x₀.
    have Hlen: length (ty_phys (Σ! tyl) (pctx_get K x₀) tid) = S (max_ty_size tyl) by rewrite ty_size_eq.
    destruct (ty_phys (Σ! tyl) (pctx_get K x₀) tid) as [|fv1 [|fv2 fvs]] eqn:Hph; [done|simpl in Hlen; lia|].
    simpl in Hlen.
    iDestruct (heap_cloc_mapsto_fancy_vec_length_eq with "Pt1") as %HlenK.
    destruct lK as [lK1 [|c1 [|c2 cs]]] eqn:HlK; [done|done|].
    iEval (rewrite !heap_mapsto_cloc_fancy_vec_cons) in "Pt1".
    iDestruct "Pt1" as "(Pt1 & Pt2 & Pt3)".
    iEval (rewrite !heap_mapsto_cloc_emp_cons) in "Gw".
    iMod (mapsto_vec_untether_singleton (lK1, [c1]) fv1 _ ∅ with "[Pt1]")
      as (v₁ l₁ c₁) "[%Hl1 [Pt1 _]]".
    { by rewrite heap_complete_mapsto_fancy_singleton. }
    injection Hl1 as <- <-.
    (* Write the tag. *)
    wp_bind (_ <- _)%E.
    iApply (wp_write_na_guarded _ lK1 c1 _ #i v₁ (D + 1) G' with "[G' Pt1 £t1]");
      [solve_ndisj| |].
    { iFrame "G' Pt1 £t1". iApply (guards_weaken_rhs_sep_l with "Gw"). }
    iIntros "!> [Pt1 G']". wp_seq.
    (* Write the payload. *)
    wp_bind (pctx_vexpr K p).
    iApply (wp_wand with "[P G' £w']").
    { iApply (wp_pctx_vptrs _ K (ty_size (Σ! tyl)) (D + 1) G' x₀ p True%I
        with "Gs [£w'] [G'] P"); [solve_ndisj| |].
      - iApply (lc_weaken with "£w'"). nia.
      - iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->". by iFrame. }
    iIntros (w) "(-> & _ & G' & P)". rewrite -/lK HlK /=. wp_op.
    wp_bind q. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->".
    iMod (mapsto_vec_untether_singleton (lK1 +ₗ 1, [c2]) fv2 _ ∅ with "[Pt2]")
      as (v₂ l₂ c₂) "[%Hl2 [Pt2 _]]".
    { by rewrite heap_complete_mapsto_fancy_singleton. }
    injection Hl2 as <- <-.
    iApply (wp_write_na_guarded _ (lK1 +ₗ 1) c2 _ vb v₂ (D + 1) G'
      with "[G' Pt2 £t2]"); [solve_ndisj| |].
    { iFrame "G' Pt2 £t2". iDestruct (guards_weaken_rhs_sep_r with "Gw") as "Gw2".
      iApply (guards_weaken_rhs_sep_l with "Gw2"). }
    iIntros "!> [Pt2 G']".
    iMod (mapsto_vec_untether _ _ _ ∅ with "Pt3") as (vlc) "[Pt3 [%Hlen3 _]]".
    (* Close the place at the new value. *)
    iDestruct (cumulative_time_receipt_mono (pctx_dlev K) with "⧗k") as "⧗k"; [lia|].
    iMod (cumulative_persistent_time_receipt with "TIME ⧗k ⧖b") as "#⧖k"; [solve_ndisj|].
    set Dn := D `max` (pctx_dlev K + db).
    iCombine "⧖ ⧖k" as "⧖D".
    iMod ("Cl" $! (pinj i b, vlc) db db Dn with "[%] [] G' P [Pt1 Pt2 Pt3] [Gb]")
      as "[Own H1]".
    { rewrite /Dn. lia. }
    { iApply (persistent_time_receipt_mono with "⧖D"). rewrite /Dn. lia. }
    { rewrite (xsum_phys_pinj_1 _ _ _ vb); [|done|lia|lia].
      rewrite (_: pctx_vloc K (ty_size (Σ! tyl)) x₀ = (lK1, c1 :: c2 :: cs)); [|exact HlK].
      rewrite !heap_mapsto_cloc_fancy_vec_cons. iFrame "Pt1 Pt2 Pt3". }
    { by rewrite xsum_gho_own_pinj. }
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iModIntro. iExists -[(pctx_set K x₀ (pinj i b, vlc), ζm)]. iFrame "L I".
    iSplitR "Obs Obs'".
    { iSplit; [|done]. iExists _. iSplit; [done|].
      iApply (vplace_own_close K _ _ _ Dn with "[] ⧗p");
        [iApply (persistent_time_receipt_mono with "⧖D"); rewrite /Dn; lia|].
      by rewrite pctx_get_set pctx_vrfn_set. }
    iCombine "Obs Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=> π [Hπ HΦ].
    by apply Hπ.
  Qed.

  Lemma type_sum_assign_oplace_deep_instr {𝔄l 𝔄} E L I p q n (K: pctx (Σ! 𝔄l) 𝔄)
      `{!PctxNoShr K} (tyl: typel 𝔄l) (i: fin (length 𝔄l)) Φ :
    ty_size (tyl +!! i) = 1%nat → resolve E L (Σ! tyl) Φ →
    lctx_lft_alive E L (pctx_ulft K (OfTy (Σ! tyl))) →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K (OfTy (Σ! tyl)); q ◁ tyl +!! i]
      (pctx_expr K p <-{Σ i} q)
      (λ _, +[p ◁ₗown{n} pctx_plug K (OfTy (Σ! tyl))])
      (λ post '-[x; b], λ mask π, Φ (pctx_get K x.1.2) π → ∀ pad,
        post -[((x.1.1, pctx_set K x.1.2 (pinj i b, pad)), x.2)] mask π).
  Proof. intros. by apply (type_sum_assign_vplace_deep_instr _ _ _ _ _ (POwn n K)). Qed.

  (** Assigning a unit variant [i] (a variant whose type is a subtype of [()]) to the leaf
      at the hole of [K] (a sum, below any number of unique borrows, in both modes): the
      old value is resolved and the tag is written. *)
  Lemma type_sum_unit_vplace_deep_instr {𝔄l 𝔄} E L I p (K: pctx (Σ! 𝔄l) 𝔄) `{!PctxNoShr K} `{!PctxVRoot K}
      (tyl: typel 𝔄l) (i: fin (length 𝔄l)) f Φ :
    subtype E L () (tyl +!! i) f → resolve E L (Σ! tyl) Φ →
    lctx_lft_alive E L (pctx_ulft K (OfTy (Σ! tyl))) →
    typed_instr E L I +[p ◁ₗ pctx_plug K (OfTy (Σ! tyl))]
      (pctx_vexpr K p <-{Σ i} ())
      (λ _, +[p ◁ₗ pctx_plug K (OfTy (Σ! tyl))])
      (λ post '-[x], λ mask π, Φ (pctx_get K x.1) π → ∀ pad,
        post -[(pctx_set K x.1 (pinj i (f ~~$ₛ ()), pad), x.2)] mask π).
  Proof.
    iIntros (Subtype Rslv Alv tid post mask iκs [x []])
      "#LFT #TIME #PROPH #UNIQ #E L I (Tp & _) Obs".
    iDestruct (Subtype with "L E") as "#(%Ssz & _ & #Sgho & _ & %Sphys & _)".
    destruct x as [x₀ ζm].
    rewrite /tctx_elt_interp.
    iDestruct "Tp" as (v Hp) "Tp". iEval (rewrite vplace_own_open) in "Tp".
    iDestruct "Tp" as (D) "(#⧖ & ⧗p & Own)". have Hdl := pctx_vroot_dlev K.
    have ?: Closed [] (pctx_vexpr K p).
    { apply pctx_vexpr_closed. by eapply eval_path_closed. }
    iDestruct (Alv with "L E") as "#Alv".
    iApply wp_fupd. iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj|].
    iIntros "£ _".
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_ulft K (OfTy (Σ! tyl))])%I as "#Hu".
    { iApply (guards_transitive with "Ghalf Alv"). }
    set y := pctx_get K x₀.
    iDestruct (lc_weaken (((D + 1) * (D + 2) + 1) + (3 * (D + 1) * D +
      ((1 + (1 + D * (D + 1))) + 3 * (D + 1)))) with "£")
      as "[£a [£w [[£r £s] £t1]]]"; [rewrite /advance_credits; nia|].
    iMod (vplace_leaf_acc K (Σ! tyl) x₀ ζm D tid _ (⊤ ∖ ↑advN)
      with "LFT PROPH UNIQ Hu H1 £a Own")
      as (G' dh gh) "(% & G' & -> & %Hdh & #G'u & #Gw & Pt1 & Gho1 & P & #Gs & Cl)"; [solve_ndisj|].
    destruct Hdh as (Hdh & Hgh & Hin).
    (* The address of the hole. *)
    wp_bind (pctx_vexpr K p).
    iApply (wp_wand with "[P G' £w]").
    { iApply (wp_pctx_vptrs _ K (ty_size (Σ! tyl)) (D + 1) G' x₀ p True%I with "Gs [£w] [G'] P");
        [solve_ndisj| |].
      - iApply (lc_weaken with "£w"). nia.
      - iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->". by iFrame. }
    iIntros (w) "(-> & _ & G' & P)".
    (* Resolve the old value. *)
    iDestruct (Rslv _ (⊤ ∖ (⊤ ∖ ↑Nllft ∖ ↑prophN ∖ ↑timeN ∖ ↑uniqN))
      with "LFT PROPH UNIQ TIME E Ghalf H2 Gho1") as "ToObs"; [set_solver|].
    iMod (lc_fupd_elim_later with "£r ToObs") as "ToObs".
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iDestruct (lc_step_fupdN_elim_later with "[£s] ToObs") as "ToObs".
    { iApply (lc_weaken with "£s"). nia. }
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iMod (fupd_mask_mono with "ToObs") as "[Obs' H2]"; [solve_ndisj|].
    (* Write the tag. *)
    set lK := pctx_vloc K (ty_size (Σ! tyl)) x₀.
    have Hlen: length (ty_phys (Σ! tyl) (pctx_get K x₀) tid) = S (max_ty_size tyl) by rewrite ty_size_eq.
    destruct (ty_phys (Σ! tyl) (pctx_get K x₀) tid) as [|fv1 fvs] eqn:Hph; [done|]. simpl in Hlen.
    iDestruct (heap_cloc_mapsto_fancy_vec_length_eq with "Pt1") as %HlenK.
    destruct lK as [lK1 [|c1 cs]] eqn:HlK; [done|].
    iEval (rewrite !heap_mapsto_cloc_fancy_vec_cons) in "Pt1".
    iDestruct "Pt1" as "(Pt1 & Pt2)".
    iEval (rewrite !heap_mapsto_cloc_emp_cons) in "Gw".
    iMod (mapsto_vec_untether_singleton (lK1, [c1]) fv1 _ ∅ with "[Pt1]")
      as (v₁ l₁ c₁) "[%Hl1 [Pt1 _]]".
    { by rewrite heap_complete_mapsto_fancy_singleton. }
    injection Hl1 as <- <-.
    wp_bind (_ <- _)%E.
    iApply (wp_write_na_guarded _ lK1 c1 _ #i v₁ (D + 1) G' with "[G' Pt1 £t1]");
      [solve_ndisj| |].
    { iFrame "G' Pt1 £t1". iApply (guards_weaken_rhs_sep_l with "Gw"). }
    iIntros "!> [Pt1 G']". wp_seq.
    iMod (mapsto_vec_untether _ _ _ ∅ with "Pt2") as (vlc) "[Pt2 [%Hlen2 _]]".
    have Hph0: ty_phys (tyl +!! i) (f ~~$ₛ ()) tid = [].
    { by rewrite -Sphys. }
    (* Close the place at the new value. *)
    iMod ("Cl" $! (pinj i (f ~~$ₛ ()), vlc) dh gh D with "[%] ⧖ G' P [Pt1 Pt2] []")
      as "[Own H1]".
    { lia. }
    { rewrite (xsum_phys_pinj_0 _ _ _ vlc); [|done|lia].
      rewrite (_: pctx_vloc K (ty_size (Σ! tyl)) x₀ = (lK1, c1 :: cs)); [|exact HlK].
      rewrite /= heap_mapsto_cloc_fancy_vec_cons. iFrame "Pt1 Pt2". }
    { rewrite xsum_gho_own_pinj. iDestruct ("Sgho" $! () dh gh tid with "[]") as "[$ _]"; done. }
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    wp_seq. iModIntro.
    iExists -[(pctx_set K x₀ (pinj i (f ~~$ₛ ()), vlc), ζm)]. iFrame "L I".
    iSplitR "Obs Obs'".
    { iSplit; [|done]. iExists _. iSplit; [done|].
      iApply (vplace_own_close with "⧖ ⧗p").
      by rewrite pctx_get_set pctx_vrfn_set. }
    iCombine "Obs Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=> π [Hπ HΦ].
    by apply Hπ.
  Qed.

  Lemma type_sum_unit_oplace_deep_instr {𝔄l 𝔄} E L I p n (K: pctx (Σ! 𝔄l) 𝔄) `{!PctxNoShr K}
      (tyl: typel 𝔄l) (i: fin (length 𝔄l)) f Φ :
    subtype E L () (tyl +!! i) f → resolve E L (Σ! tyl) Φ →
    lctx_lft_alive E L (pctx_ulft K (OfTy (Σ! tyl))) →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K (OfTy (Σ! tyl))]
      (pctx_expr K p <-{Σ i} ())
      (λ _, +[p ◁ₗown{n} pctx_plug K (OfTy (Σ! tyl))])
      (λ post '-[x], λ mask π, Φ (pctx_get K x.1.2) π → ∀ pad,
        post -[((x.1.1, pctx_set K x.1.2 (pinj i (f ~~$ₛ ()), pad)), x.2)] mask π).
  Proof. intros. by apply (type_sum_unit_vplace_deep_instr _ _ _ _ (POwn n K)). Qed.
  Lemma xsum_phys_pinj_vec {𝔄l} (tyl: typel 𝔄l) i u pad tid :
    length pad = (max_ty_size tyl - ty_size (tyl +!! i))%nat →
    ty_phys (Σ! tyl) (pinj i u, pad) tid =
      FVal #i :: ty_phys (tyl +!! i) u tid ++ fmap FVal pad.
  Proof.
    intros Hlen. have := max_hlist_with_ge (λ _, ty_size) tyl i. simpl. intros ?.
    rewrite /ty_phys /xsum_ty /= to_xsum_pinj /=. rewrite pad_length'; [done|].
    rewrite /= length_app length_fmap Hlen ty_size_eq. f_equal. rewrite Nat.add_comm Nat.sub_add //.
  Qed.

  (** Assigning a variant [i] with a payload of any size, copied from a path [pr] that can
      be read ([e1 <-{n,Σ i} !e2]), to the leaf at the hole of [K] (a sum, below any number
      of unique borrows, in both modes), keeping the type of the leaf: the old value is
      resolved, the tag is written and the payload copied, the cells after the payload are
      the padding. *)
  Lemma type_sum_memcpy_vplace_deep_instr {𝔄l 𝔄 𝔅 𝔅'} E L I p pr (K: pctx (Σ! 𝔄l) 𝔄)
      `{!PctxNoShr K} `{!PctxVRoot K} (tyl: typel 𝔄l) (i: fin (length 𝔄l)) (tyr: type 𝔅) (tyr': type 𝔅')
      gtr str Φ (sz: Z) :
    resolve E L (Σ! tyl) Φ → typed_read E L tyr (tyl +!! i) tyr' gtr str →
    sz = ty_size (tyl +!! i) → lctx_lft_alive E L (pctx_ulft K (OfTy (Σ! tyl))) →
    typed_instr E L I +[p ◁ₗ pctx_plug K (OfTy (Σ! tyl)); pr ◁ tyr]
      (pctx_vexpr K p <-{sz,Σ i} !pr)
      (λ _, +[p ◁ₗ pctx_plug K (OfTy (Σ! tyl)); pr ◁ tyr'])
      (λ post '-[x; b], λ mask π, Φ (pctx_get K x.1) π → ∀ pad zr, str b zr →
        post -[(pctx_set K x.1 (pinj i (gtr b), pad), x.2); zr] mask π).
  Proof.
    iIntros (Rslv Rd -> Alv tid post mask iκs [x [b []]])
      "#LFT #TIME #PROPH #UNIQ #E L I (Tp & Tr & _) Obs".
    destruct x as [x₀ ζm].
    rewrite /tctx_elt_interp.
    iDestruct "Tp" as (v Hp) "Tp". iEval (rewrite vplace_own_open) in "Tp".
    iDestruct "Tp" as (D) "(#⧖ & ⧗p & Own)". have Hdl := pctx_vroot_dlev K.
    iDestruct "Tr" as (vr dr Hpr) "(#⧖r & Tr)".
    have ?: Closed [] (pctx_vexpr K p).
    { apply pctx_vexpr_closed. by eapply eval_path_closed. }
    have ?: Closed [] pr by eapply eval_path_closed.
    have HMi := max_hlist_with_ge (λ _, ty_size) tyl i. simpl in HMi.
    set sz := ty_size (tyl +!! i).
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
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_ulft K (OfTy (Σ! tyl))])%I as "#Hu".
    { iApply (guards_transitive with "Ghalf Alv"). }
    have HM: D ≤ M ∧ dr ≤ M by rewrite /M; lia.
    iDestruct (lc_weaken (((D + 1) * (D + 2) + 1) + (3 * (D + 1) * M + (3 * (D + 1) * M +
      ((1 + (1 + M * (D + 1))) + (3 * (D + 1) + ((dr + 1) + (1 + (6 * (M + 1) +
      (1 + (M + 1)))))))))) with "£")
      as "[£a [£w [£w' [[£r £s] [£t1 [£d [£b [£m [£o £o']]]]]]]]]";
      [rewrite /advance_credits; nia|].
    iMod (vplace_leaf_acc K (Σ! tyl) x₀ ζm D tid _ (⊤ ∖ ↑advN)
      with "LFT PROPH UNIQ Hu H1 £a Own")
      as (G' dh gh) "(% & G' & -> & %Hdh & #G'u & #Gw & Pt1 & Gho1 & P & #Gs & Cl)"; [solve_ndisj|].
    destruct Hdh as (Hdh & Hgh & Hin).
    (* The address of the hole. *)
    wp_bind (pctx_vexpr K p).
    iApply (wp_wand with "[P G' £w]").
    { iApply (wp_pctx_vptrs _ K (ty_size (Σ! tyl)) (D + 1) G' x₀ p True%I with "Gs [£w] [G'] P");
        [solve_ndisj| |].
      - iApply (lc_weaken with "£w"). nia.
      - iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->". by iFrame. }
    iIntros (w) "(-> & _ & G' & P)".
    (* Resolve the old value. *)
    iDestruct (Rslv _ (⊤ ∖ (⊤ ∖ ↑Nllft ∖ ↑prophN ∖ ↑timeN ∖ ↑uniqN))
      with "LFT PROPH UNIQ TIME E Ghalf H2 Gho1") as "ToObs"; [set_solver|].
    iMod (lc_fupd_elim_later with "£r ToObs") as "ToObs".
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iDestruct (lc_step_fupdN_elim_later with "[£s] ToObs") as "ToObs".
    { iApply (lc_weaken with "£s"). nia. }
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iMod (fupd_mask_mono with "ToObs") as "[Obs' H2]"; [solve_ndisj|].
    (* Split the cells: tag, payload, padding. *)
    set lK := pctx_vloc K (ty_size (Σ! tyl)) x₀.
    have Hlen: length (ty_phys (Σ! tyl) (pctx_get K x₀) tid) = S (max_ty_size tyl)
      by rewrite ty_size_eq.
    destruct (ty_phys (Σ! tyl) (pctx_get K x₀) tid) as [|fv1 fvs] eqn:Hph; [done|].
    simpl in Hlen.
    iDestruct (heap_cloc_mapsto_fancy_vec_length_eq with "Pt1") as %HlenK.
    destruct lK as [lK1 [|c1 cs]] eqn:HlK; [done|].
    iEval (rewrite !heap_mapsto_cloc_fancy_vec_cons) in "Pt1".
    iDestruct "Pt1" as "(Pt1 & Pt2)".
    iEval (rewrite !heap_mapsto_cloc_emp_cons) in "Gw".
    iMod (mapsto_vec_untether_singleton (lK1, [c1]) fv1 _ ∅ with "[Pt1]")
      as (v₁ l₁ c₁) "[%Hl1 [Pt1 _]]".
    { by rewrite heap_complete_mapsto_fancy_singleton. }
    injection Hl1 as <- <-.
    (* Write the tag. *)
    wp_bind (_ <- _)%E.
    iApply (wp_write_na_guarded _ lK1 c1 _ #i v₁ (D + 1) G' with "[G' Pt1 £t1]");
      [solve_ndisj| |].
    { iFrame "G' Pt1 £t1". iApply (guards_weaken_rhs_sep_l with "Gw"). }
    iIntros "!> [Pt1 G']". wp_seq.
    (* The address of the payload. *)
    wp_bind (pctx_vexpr K p).
    iApply (wp_wand with "[P G' £w']").
    { iApply (wp_pctx_vptrs _ K (ty_size (Σ! tyl)) (D + 1) G' x₀ p True%I
        with "Gs [£w'] [G'] P"); [solve_ndisj| |].
      - iApply (lc_weaken with "£w'"). nia.
      - iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->". by iFrame. }
    iIntros (w) "(-> & _ & G' & P)". rewrite -/lK HlK /=. wp_op.
    wp_bind pr. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->".
    (* Read the source. *)
    iMod (Rd with "LFT E Ghalf H2 Tr £d")
      as (lb vlb_c vlb HR Hvr Hlenc) "(Hr & #Hrpt & Retether & _ & Own' & Totyr')".
    iDestruct "Own'" as "[Gb #>%Phys]".
    iMod (lc_fupd_elim_later with "£b Gb") as "Gb".
    have Hlenb: length vlb = sz by rewrite -Phys ty_size_eq.
    injection Hvr as ->.
    (* Split the payload cells from the padding. *)
    have Hfvs: sz ≤ length fvs. { rewrite /sz. etrans; [apply HMi|]. lia. }
    have Htk: length (take sz fvs) = sz by rewrite length_take; lia.
    iAssert (cloc_take (lK1 +ₗ 1, cs) (length (take sz fvs)) #↦!∗ take sz fvs ∗
      cloc_skip (lK1 +ₗ 1, cs) (length (take sz fvs)) #↦!∗ drop sz fvs)%I
      with "[Pt2]" as "[Pt2 Pt3]".
    { rewrite -heap_cloc_mapsto_fancy_vec_app take_drop. iExact "Pt2". }
    rewrite Htk.
    iMod (mapsto_vec_untether _ _ _ ∅ with "Pt2") as (vl2) "[Pt2 [%Hvl2 _]]".
    iMod (mapsto_vec_untether _ _ _ ∅ with "Pt3") as (vl3) "[Pt3 [%Hvl3 _]]".
    iAssert (G' &&{↑NllftG; M + 1}&&> cloc_take (lK1 +ₗ 1, cs) sz #↦∗_)%I as "#Gw2".
    { iApply (lguards_weaken_later _ _ _ (D + 1)); [lia|].
      iDestruct (guards_weaken_rhs_sep_r with "Gw") as "Gw'".
      iEval (rewrite (heap_cloc_mapsto_emp_vec_app _ sz)) in "Gw'".
      iApply (guards_weaken_rhs_sep_l with "Gw'"). }
    iApply (wp_memcpy_guarded _ (cloc_take (lK1 +ₗ 1, cs) sz) lb vl2 vlb_c G' HR _ (M + 1)
      with "TIME [Pt2 Hr G' £m]"); [solve_ndisj| |lia| |].
    { rewrite Hvl2 length_take. lia. }
    { iFrame "Pt2 Hr G' ⧖S £m". iSplit; [iApply "Gw2"|].
      iApply (lguards_weaken_later with "Hrpt"). lia. }
    iIntros "!> (Pt2 & G' & Hr)".
    (* Put the contents (with their ghost cells) into the payload cells. *)
    leaf_open_laters "Gw2" with "G'" as "A"; [solve_ndisj|].
    iMod (lc_fupd_elim_later with "£o A") as "A".
    iMod (lc_fupd_elim_laterN with "£o' A") as "A". iMod "A" as "[Pre back]".
    iDestruct ("Retether" $! (cloc_take (lK1 +ₗ 1, cs) sz).1 (cloc_take (lK1 +ₗ 1, cs) sz).2
      with "[Pre Pt2]") as "Ret"; [by iFrame|].
    iMod (fupd_mask_mono with "Ret") as "[Pre Pt2]"; [set_solver|].
    iMod ("back" with "Pre") as "G'".
    iMod (fupd_mask_mono with "(Totyr' Hr)") as (zr Hzr) "(H2 & Tr)"; [solve_ndisj|].
    (* Close the place at the new value. *)
    iDestruct (cumulative_time_receipt_mono (pctx_dlev K) with "⧗k") as "⧗k"; [lia|].
    iMod (cumulative_persistent_time_receipt with "TIME ⧗k ⧖r") as "#⧖k"; [solve_ndisj|].
    set Dn := D `max` (pctx_dlev K + dr).
    iCombine "⧖ ⧖k" as "⧖D".
    have Hlen3: length vl3 = (max_ty_size tyl - sz)%nat.
    { rewrite Hvl3 length_drop. lia. }
    iMod ("Cl" $! (pinj i (gtr b), vl3) dr dr Dn with "[%] [] G' P [Pt1 Pt2 Pt3] [Gb]")
      as "[Own H1]".
    { rewrite /Dn. lia. }
    { iApply (persistent_time_receipt_mono with "⧖D"). rewrite /Dn. lia. }
    { rewrite (xsum_phys_pinj_vec _ _ _ vl3) //.
      rewrite (_: pctx_vloc K (ty_size (Σ! tyl)) x₀ = (lK1, c1 :: cs)); [|exact HlK].
      rewrite heap_mapsto_cloc_fancy_vec_cons heap_cloc_mapsto_fancy_vec_app Phys Hlenb.
      iFrame "Pt1 Pt2".
      rewrite -heap_complete_mapsto_fancy_fmap_eq. iFrame "Pt3". }
    { by rewrite xsum_gho_own_pinj. }
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iModIntro. iExists -[(pctx_set K x₀ (pinj i (gtr b), vl3), ζm); zr]. iFrame "L I".
    iSplitR "Obs Obs'".
    { iSplitR "Tr"; [|iSplitL; [|done]].
      - iExists _. iSplit; [done|].
        iApply (vplace_own_close K _ _ _ Dn with "[] ⧗p");
          [iApply (persistent_time_receipt_mono with "⧖D"); rewrite /Dn; lia|].
        by rewrite pctx_get_set pctx_vrfn_set.
      - iExists #lb.1, dr. iFrame "⧖r Tr". by rewrite Hpr. }
    iCombine "Obs Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=> π [Hπ HΦ].
    by apply Hπ.
  Qed.

  Lemma type_sum_memcpy_oplace_deep_instr {𝔄l 𝔄 𝔅 𝔅'} E L I p pr n (K: pctx (Σ! 𝔄l) 𝔄)
      `{!PctxNoShr K} (tyl: typel 𝔄l) (i: fin (length 𝔄l)) (tyr: type 𝔅) (tyr': type 𝔅')
      gtr str Φ (sz: Z) :
    resolve E L (Σ! tyl) Φ → typed_read E L tyr (tyl +!! i) tyr' gtr str →
    sz = ty_size (tyl +!! i) → lctx_lft_alive E L (pctx_ulft K (OfTy (Σ! tyl))) →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K (OfTy (Σ! tyl)); pr ◁ tyr]
      (pctx_expr K p <-{sz,Σ i} !pr)
      (λ _, +[p ◁ₗown{n} pctx_plug K (OfTy (Σ! tyl)); pr ◁ tyr'])
      (λ post '-[x; b], λ mask π, Φ (pctx_get K x.1.2) π → ∀ pad zr, str b zr →
        post -[((x.1.1, pctx_set K x.1.2 (pinj i (gtr b), pad)), x.2); zr] mask π).
  Proof. intros. by apply (type_sum_memcpy_vplace_deep_instr _ _ _ _ _ (POwn n K)). Qed.
End sum_deep.
