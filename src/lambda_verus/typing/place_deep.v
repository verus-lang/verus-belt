(** * Byte copies and sums below unique borrows

  The byte versions of the rules of the deleted legacy [place_deep.v] for places rooted at a value
  ([p ◁ₗ …], hence also owned places, [POwn n K]) whose context contains unique borrows
  ([PUniq], at any depth, interleaved with fields, owned pointers and sums).

  All rules on a leaf [OfTy ty] at the hole of [K] go through [vplace_leaf_acc]: the
  access of [pctx_acc.v] (opening the enclosing borrows with the credits of the program
  step), and, if the hole is the whole referent of the innermost borrow, the opening of
  its body; it gives the bytes of the leaf ([cbytes]), the ownership of its value without
  laters, and a closer for a new value of the leaf (of the same type).

  - [type_memcpy_vplace_deep_instr]: assignment of the contents of a box ([own_bytes]) of
    the type of the leaf, a byte-level [MemCopy] (as Rust's assignment through [&mut]):
    the old value is resolved, the box becomes uninitialized ([↯]: it keeps its bytes);
    [type_memcpy_copy_from_vplace_deep_instr]: copy of a [Copy] leaf into a box, again a
    [MemCopy] (no decode/encode). There is no typed memcpy: a round trip through a value
    is a typed [Load] and a typed [Store].
  - [type_case_vplace_deep]: case analysis on a sum leaf, which reads the tag with a typed
    [Load] of the tag [IntType] at offset 0; the leaf becomes the sum place
    [SumLty tyl i (OfTy (tyl +!! i))] in branch [i]; [type_fold_vplace_sum_deep_instr]
    folds it back.

  Not ported: assigning a variant below unique borrows (on bytes it is a typed [Store] of
  a variant value, [type_mk_variant_val_instr], [type_write_vplace_deep_instr]), and the
  copies below shared references ([type_memcpy_copy_from_oplace_pshr_instr]: the shared
  places of [place_pshr.v] are not ported). *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From lrust.lang Require Import proofmode.
From lrust.typing Require Export type ltype lpath pctx_acc vplace place_own.
From lrust.typing Require Import type_context programs lft_contexts uniq_util uniq_bytes_util uniq_bytes own_bytes shr_bytes bytes_layout value_ctx product uninit freeable_util place_sum place_puniq sum.
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
      ⧖D' -∗ G' -∗ pctx_vptrs K (lty_size (OfTy ty)) x₀ -∗
      cbytes ty y' (pctx_vloc K (lty_size (OfTy ty)) x₀) -∗
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
    ∃ (G': iProp Σ) dh gh, ⌜Timeless G'⌝ ∗ G' ∗ ⌜v = MLitV (VPtr (pctx_vrloc K (lty_size (OfTy ty)) x₀).1)⌝ ∗
      ⌜dh + pctx_dlev K ≤ D ∧ gh ≤ D ∧ pctx_in K x₀⌝ ∗
      (G' &&{↑NllftG}&&> @[pctx_ulft K (OfTy ty)]) ∗
      (G' &&{↑NllftG; D + 1}&&> pctx_vloc K (lty_size (OfTy ty)) x₀ #↦∗_) ∗
      cbytes ty (pctx_get K x₀) (pctx_vloc K (lty_size (OfTy ty)) x₀) ∗
      ty_gho_own ty (pctx_get K x₀) dh gh tid ∗
      pctx_vptrs K (lty_size (OfTy ty)) x₀ ∗ pctx_vpguards K (lty_size (OfTy ty)) (D + 1) G' x₀ ∗
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
    iDestruct (pctx_vhguard K (OfTy ty) (lty_size (OfTy ty)) x₀ G' D with "G'u HG") as "#Gw".
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
      { iIntros "_ !>". iSplit; [|done]. iExists y'. iSplit; [done|]. rewrite /bofty_owned.
        iFrame "Pt". by iApply bi.laterN_intro. }
      by iFrame "G Own".
  Qed.
End leaf_acc.

(** * Byte-level copies below unique borrows *)

Section memcpy_deep.
  Context `{!typeG Σ}.

  (** Moving the contents of a box into the leaf at the hole of [K] (below any number of
      unique borrows, in both modes of the hole), keeping the type of the leaf (as Rust's
      assignment through [&mut]): a byte-level [MemCopy] (no decode/encode). The old value
      of the leaf is resolved; the box becomes uninitialized ([↯]: its bytes are kept). *)
  Lemma type_memcpy_vplace_deep_instr {𝔅 𝔄} E L I p pr n (K: pctx 𝔅 𝔄) `{!PctxNoShr K}
      `{!PctxVRoot K} `{!NoCell 𝔅} (ty: type 𝔅) Φ (sz: nat) :
    resolve E L ty Φ → sz = ty_bsize ty →
    lctx_lft_alive E L (pctx_ulft K (OfTy ty)) →
    typed_instr E L I +[p ◁ₗ pctx_plug K (OfTy ty); pr ◁ᵥ own_bytes n ty]
      (MemCopy Na1Ord sz (pctx_vexpr K p) (ToLit pr))
      (λ _, +[p ◁ₗ pctx_plug K (OfTy ty); pr ◁ᵥ own_bytes n (↯ sz)])
      (λ post '-[x; b], λ mask π, Φ (pctx_get K x.1) π →
        ∀ junk, post -[(pctx_set K x.1 b.2, x.2); (b.1, junk)] mask π).
  Proof.
    iIntros (Rslv -> Alv tid post mask iκs [x [[lb y] []]])
      "#LFT #TIME #PROPH #UNIQ #E L I (Tp & Tr & _) Obs".
    destruct x as [x₀ ζm].
    rewrite /tctx_elt_interp.
    iDestruct "Tp" as (v Hp) "Tp". iEval (rewrite vplace_own_open) in "Tp".
    iDestruct "Tp" as (D) "(#⧖ & ⧗p & Own)". have Hdl := pctx_vroot_dlev K.
    iDestruct "Tr" as (vr Hpr wr dr [-> Hwr]) "(#⧖r & Tr)". simpl in Hwr. simplify_eq.
    destruct dr as [|dr]; [done|]. iDestruct "Tr" as "(Bs & Fr & Gb)".
    iDestruct (bytes_own_nocell_bytes with "Bs") as (bs) "[Hbs %Hbs]".
    have ?: Closed [] (pctx_vexpr K p).
    { apply pctx_vexpr_closed. by eapply eval_path_closed. }
    have ?: Closed [] pr by eapply eval_path_closed.
    iDestruct (Alv with "L E") as "#Alv".
    (* The first step gives credits and cumulative time receipts. *)
    iCombine "⧖ ⧖r" as "⧖m".
    iApply (wp_cumulative_time_receipt_linear with "TIME ⧖m"); [solve_ndisj|].
    iIntros "⧗". iApply wp_fupd.
    set M := D `max` (S dr).
    iDestruct (cumulative_time_receipt_sep 1 (S M) with "⧗") as "[⧗c ⧗k]".
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗c ⧖m") as "[#⧖S £]";
      [solve_ndisj|].
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_ulft K (OfTy ty)])%I as "#Hu".
    { iApply (guards_transitive with "Ghalf Alv"). }
    have HM: D ≤ M ∧ S dr ≤ M by rewrite /M; lia.
    iDestruct (lc_weaken (((D + 1) * (D + 2) + 1) + (3 * (D + 1) * M + ((1 + (1 + M * (D + 1))) + 1)))
      with "£") as "[£a [£w [[£r £s] £b]]]"; [rewrite /advance_credits; nia|].
    iMod (vplace_leaf_acc K ty x₀ ζm D tid _ (⊤ ∖ ↑advN) with "LFT PROPH UNIQ Hu H1 £a Own")
      as (G' dh gh) "(% & G' & -> & %Hdh & #G'u & #Gw & Pt1 & Gho1 & P & #Gs & Cl)"; [solve_ndisj|].
    destruct Hdh as (Hdh & Hgh & Hin).
    set lK := pctx_vloc K (lty_size (OfTy ty)) x₀.
    (* The addresses of the hole and of the source. *)
    wp_bind (pctx_vexpr K p).
    iApply (wp_wand with "[P G' £w]").
    { iApply (wp_pctx_vptrs _ K (lty_size (OfTy ty)) (D + 1) G' x₀ p True%I with "Gs [£w] [G'] P");
        [solve_ndisj| |].
      - iApply (lc_weaken with "£w"). nia.
      - iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->". by iFrame. }
    iIntros (w) "(-> & _ & G' & P)".
    wp_bind pr. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->". wp_pure _.
    (* Resolve the old value. *)
    iDestruct (Rslv _ (⊤ ∖ (⊤ ∖ ↑Nllft ∖ ↑prophN ∖ ↑timeN ∖ ↑uniqN))
      with "LFT PROPH UNIQ TIME E Ghalf H2 Gho1") as "ToObs"; [set_solver|].
    iMod (lc_fupd_elim_later with "£r ToObs") as "ToObs".
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iDestruct (lc_step_fupdN_elim_later with "[£s] ToObs") as "ToObs".
    { iApply (lc_weaken with "£s"). nia. }
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iMod (fupd_mask_mono with "ToObs") as "[Obs' H2]"; [solve_ndisj|].
    iMod (lc_fupd_elim_later with "£b Gb") as "Gb".
    (* Copy the bytes. *)
    iDestruct (bytes_own_nocell_bytes with "Pt1") as (bs1) "[Hbs1 %Hbs1]".
    iApply (wp_memcopy with "[$Hbs1 $Hbs]");
      [solve_ndisj|by rewrite (ty_bytes_length _ _ _ Hbs1)|by rewrite (ty_bytes_length _ _ _ Hbs)|].
    iIntros "!> [Hbs1 Hbs]".
    (* Close the place at the new value. *)
    iDestruct (cumulative_time_receipt_mono (pctx_dlev K) with "⧗k") as "⧗k"; [lia|].
    iMod (cumulative_persistent_time_receipt with "TIME ⧗k ⧖r") as "#⧖k"; [solve_ndisj|].
    set Dn := D `max` (pctx_dlev K + S dr).
    iCombine "⧖ ⧖k" as "⧖D".
    iMod ("Cl" $! y dr (S dr) Dn with "[%] [] G' P [Hbs1] Gb") as "[Own H1]".
    { rewrite /Dn. lia. }
    { iApply (persistent_time_receipt_mono with "⧖D"). rewrite /Dn. lia. }
    { by iApply bytes_own_of_bytes. }
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    set junk := vreplicate (ty_bsize ty) (LitV LitPoison).
    iModIntro. iExists -[(pctx_set K x₀ y, ζm); (lb, junk)]. iFrame "L I".
    iSplitR "Obs Obs'".
    { iSplitR "Hbs Fr"; [|iSplitL; [|done]].
      - iExists _. iSplit; [done|].
        iApply (vplace_own_close K _ _ _ Dn with "[] ⧗p");
          [iApply (persistent_time_receipt_mono with "⧖D"); rewrite /Dn; lia|].
        by rewrite pctx_get_set pctx_vrfn_set.
      - iExists _. iSplit; [done|]. iExists (VPtr lb), (S dr). iSplit; [done|]. iFrame "⧖r".
        iSplitL "Hbs".
        + iApply (bytes_own_of_bytes with "Hbs"). exists (VTuple []). split; [done|].
          rewrite -(ty_mty_eq (↯ _)) /= decide_True //. by rewrite (ty_bytes_length _ _ _ Hbs).
        + by iFrame "Fr". }
    iCombine "Obs Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=> π [Hπ HΦ].
    by apply Hπ.
  Qed.

  Lemma type_memcpy_oplace_deep_instr {𝔅 𝔄} E L I p pr n' n (K: pctx 𝔅 𝔄) `{!PctxNoShr K}
      `{!NoCell 𝔅} (ty: type 𝔅) Φ (sz: nat) :
    resolve E L ty Φ → sz = ty_bsize ty →
    lctx_lft_alive E L (pctx_ulft K (OfTy ty)) →
    typed_instr E L I +[p ◁ₗown{n'} pctx_plug K (OfTy ty); pr ◁ᵥ own_bytes n ty]
      (MemCopy Na1Ord sz (pctx_expr K (ToLit p)) (ToLit pr))
      (λ _, +[p ◁ₗown{n'} pctx_plug K (OfTy ty); pr ◁ᵥ own_bytes n (↯ sz)])
      (λ post '-[x; b], λ mask π, Φ (pctx_get K x.1.2) π →
        ∀ junk, post -[((x.1.1, pctx_set K x.1.2 b.2), x.2); (b.1, junk)] mask π).
  Proof. intros. by apply (type_memcpy_vplace_deep_instr _ _ _ _ _ _ (POwn n' K)). Qed.

  (** Copying the value of a [Copy] type out of the leaf at the hole of [K] (below any
      number of unique borrows, in both modes of the hole) into a box: a byte-level
      [MemCopy]. The old contents of the box are resolved; the place does not change. *)
  Lemma type_memcpy_copy_from_vplace_deep_instr {𝔅 𝔄 𝔅'} E L I pw p n (K: pctx 𝔅 𝔄)
      `{!PctxNoShr K} `{!PctxVRoot K} `{!NoCell 𝔅} (ty: type 𝔅) (tyw: type 𝔅') Φ (sz: nat) :
    Copy ty → resolve E L tyw Φ → sz = ty_bsize ty → ty_bsize tyw = sz →
    lctx_lft_alive E L (pctx_ulft K (OfTy ty)) →
    typed_instr E L I +[pw ◁ᵥ own_bytes n tyw; p ◁ₗ pctx_plug K (OfTy ty)]
      (MemCopy Na1Ord sz (ToLit pw) (pctx_vexpr K p))
      (λ _, +[pw ◁ᵥ own_bytes n ty; p ◁ₗ pctx_plug K (OfTy ty)])
      (λ post '-[b; x], λ mask π, Φ b.2 π → post -[(b.1, pctx_get K x.1); x] mask π).
  Proof.
    iIntros (Hcopy Rslv -> Hszw Alv tid post mask iκs [[lw z] [x []]])
      "#LFT #TIME #PROPH #UNIQ #E L I (Tw & Tp & _) Obs".
    destruct x as [x₀ ζm].
    rewrite /tctx_elt_interp.
    iDestruct "Tp" as (v Hp) "Tp". iEval (rewrite vplace_own_open) in "Tp".
    iDestruct "Tp" as (D) "(#⧖ & ⧗p & Own)". have Hdl := pctx_vroot_dlev K.
    iDestruct "Tw" as (vw Hpw ww dw [-> Hww]) "(#⧖w & Tw)". simpl in Hww. simplify_eq.
    destruct dw as [|dw]; [done|]. iDestruct "Tw" as "(Bs & Fr & Gw0)".
    iApply (wp_bytes_own_forget with "Bs"); [solve_ndisj|]. iIntros (bsw) "Hbsw %Hlenw".
    have ?: Closed [] (pctx_vexpr K p).
    { apply pctx_vexpr_closed. by eapply eval_path_closed. }
    have ?: Closed [] pw by eapply eval_path_closed.
    iDestruct (Alv with "L E") as "#Alv".
    iCombine "⧖ ⧖w" as "⧖m".
    iApply (wp_cumulative_time_receipt_linear with "TIME ⧖m"); [solve_ndisj|].
    iIntros "⧗". iApply wp_fupd.
    set M := D `max` (S dw).
    iDestruct (cumulative_time_receipt_sep 1 (S M) with "⧗") as "[⧗c _]".
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗c ⧖m") as "[#⧖S £]";
      [solve_ndisj|].
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_ulft K (OfTy ty)])%I as "#Hu".
    { iApply (guards_transitive with "Ghalf Alv"). }
    have HM: D ≤ M ∧ S dw ≤ M by rewrite /M; lia.
    iDestruct (lc_weaken (((D + 1) * (D + 2) + 1) + (3 * (D + 1) * M + ((1 + (1 + M * (M + 1))) + 1)))
      with "£") as "[£a [£w [[£r £s] £b]]]"; [rewrite /advance_credits; nia|].
    (* The address of the box, then of the hole. *)
    wp_bind pw. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->". wp_pure _.
    iMod (vplace_leaf_acc K ty x₀ ζm D tid _ (⊤ ∖ ↑advN) with "LFT PROPH UNIQ Hu H1 £a Own")
      as (G' dh gh) "(% & G' & -> & %Hdh & #G'u & #Gw & Pt1 & #Gho1 & P & #Gs & Cl)"; [solve_ndisj|].
    destruct Hdh as (Hdh & Hgh & Hin).
    set lK := pctx_vloc K (lty_size (OfTy ty)) x₀.
    wp_bind (pctx_vexpr K p).
    iApply (wp_wand with "[P G' £w]").
    { iApply (wp_pctx_vptrs _ K (lty_size (OfTy ty)) (D + 1) G' x₀ p True%I with "Gs [£w] [G'] P");
        [solve_ndisj| |].
      - iApply (lc_weaken with "£w"). nia.
      - iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->". by iFrame. }
    iIntros (w) "(-> & _ & G' & P)".
    (* Resolve the old contents of the box. *)
    iMod (lc_fupd_elim_later with "£b Gw0") as "Gw0".
    iDestruct (Rslv _ (⊤ ∖ (⊤ ∖ ↑Nllft ∖ ↑prophN ∖ ↑timeN ∖ ↑uniqN))
      with "LFT PROPH UNIQ TIME E Ghalf H2 Gw0") as "ToObs"; [set_solver|].
    iMod (lc_fupd_elim_later with "£r ToObs") as "ToObs".
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iDestruct (lc_step_fupdN_elim_later with "[£s] ToObs") as "ToObs".
    { iApply (lc_weaken with "£s"). nia. }
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iMod (fupd_mask_mono with "ToObs") as "[Obs' H2]"; [solve_ndisj|].
    (* Copy the bytes. *)
    iDestruct (bytes_own_nocell_bytes with "Pt1") as (bs1) "[Hbs1 %Hbs1]".
    iApply (wp_memcopy with "[$Hbsw $Hbs1]");
      [solve_ndisj|by rewrite Hlenw Hszw|by rewrite (ty_bytes_length _ _ _ Hbs1)|].
    iIntros "!> [Hbsw Hbs1]".
    (* Close the place, unchanged. *)
    iMod ("Cl" $! (pctx_get K x₀) dh gh D with "[%] ⧖ G' P [Hbs1] Gho1") as "[Own H1]"; [lia| |].
    { by iApply bytes_own_of_bytes. }
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iModIntro. iExists -[(lw, pctx_get K x₀); (x₀, ζm)]. iFrame "L I".
    iSplitR "Obs Obs'".
    { iSplitL "Hbsw Fr"; [|iSplitL; [|done]].
      - iExists _. iSplit; [done|]. iExists (VPtr lw), (S M). iSplit; [done|].
        iSplit; [iApply (persistent_time_receipt_mono with "⧖S"); lia|].
        iSplitL "Hbsw"; [by iApply bytes_own_of_bytes|]. iSplitL "Fr".
        + by rewrite -Hszw.
        + iNext. iDestruct (ty_gho_own_depth_mono _ dh gh M (S M) with "Gho1") as "[$ _]"; lia.
      - iExists _. iSplit; [done|].
        iApply (vplace_own_close with "⧖ ⧗p").
        by rewrite ?pctx_set_get ?pctx_get_set ?pctx_vrfn_set. }
    iCombine "Obs Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=> π [Hπ HΦ].
    by apply Hπ.
  Qed.
End memcpy_deep.

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
      (case: ToLit (Load Na1Ord (MInt (sum_tag 𝔄l)) (pctx_vexpr K p)) of el)
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
    wp_bind (Load Na1Ord (MInt (sum_tag 𝔄l)) (pctx_vexpr K p))%E.
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
    set lK := pctx_vloc K (lty_size (OfTy (Σ! tyl))) x₀.
    iAssert (G' &&{↑NllftG}&&> @[pctx_ulft K (OfTy (Σ! tyl))])%I as "#G'u".
    { iApply (guards_transitive with "G'G Hu"). }
    iDestruct (pctx_vhguard K (OfTy (Σ! tyl)) (lty_size (OfTy (Σ! tyl))) x₀ G' D with "G'u HG")
      as "#Gw".
    iAssert (G' &&{↑NllftG; D + 1}&&> cloc_take lK 1 #↦∗_)%I as "#Gt".
    { iEval (rewrite (heap_cloc_mapsto_emp_vec_app lK 1)) in "Gw".
      iApply (guards_weaken_rhs_sep_l with "Gw"). }
    (* The address of the hole. *)
    wp_bind (pctx_vexpr K p).
    iApply (wp_wand with "[P G' £w]").
    { iApply (wp_pctx_vptrs _ K (lty_size (OfTy (Σ! tyl))) (D + 1) G' x₀ p True%I with "Gs [£w] [G'] P");
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
      iEval (rewrite (cbytes_sum _ j (tyl +!! j))) in "Pt1". iDestruct "Pt1" as "(Tag & Pay & Pad)".
      iDestruct "Tag" as (bt) "[Bt %Hbt]".
      iApply (wp_load_na with "Bt"); [exact Hbt|]. iIntros "!> Bt".
      iSpecialize ("CloseB" $! (pinj j a, pad) dh gh with "[Bt Pay Pad Gho1] ⧗1").
      { iNext. iFrame "⧖' Gho1". rewrite (cbytes_sum _ j (tyl +!! j)). by iFrame. }
      iMod (fupd_mask_mono with "CloseB") as "[Body A]"; [solve_ndisj|].
      iMod (fupd_mask_mono with "(Back2 A B)") as "G'"; [solve_ndisj|].
      iMod (cpd_unfold_uniq lt' κ (pctx_hξi K x₀) (pinj j a, pad) r' dh gh tid lK
        with "LFT PROPH UNIQ G'κ G' [Body]") as "[Own G']"; [done|done|done| | | |solve_ndisj| |].
      { rewrite /r' prfn_rsv_sum. apply prfn_rsv_in. }
      { intros π. rewrite /r' prfn_den_sum /= prfn_den_in. by rewrite psum_map1_pinj. }
      { iIntros (d0 g0) "[Gho Pt] !>". rewrite lty_fold_sum_ofty.
        iApply (sum_ofty_unfold_own 0). rewrite /ltype_own /= /bofty_owned.
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
      wp_pure _. wp_case. { split; [lia|]. by rewrite Nat2Z.id -vlookup_lookup plistc_to_vec_lookup. }
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
      iEval (rewrite (cbytes_sum _ j (tyl +!! j))) in "Pt1". iDestruct "Pt1" as "(Tag & Pay & Pad)".
      iDestruct "Tag" as (bt) "[Bt %Hbt]".
      iApply (wp_load_na with "Bt"); [exact Hbt|]. iIntros "!> Bt".
      iMod ("Cl" $! lt' r' dh gh D [] 1%Qp True%I
        with "[//] [//] [//] [%] [%] [] ⧖ G' P [] [Bt Pay Pad Gho1]") as "(Own & H1 & _)".
      { exact Hr'. }
      { lia. }
      { by iApply big_sepL_pat_ok_nil. }
      { done. }
      { iIntros "_ !>". iSplit; [|done]. iApply sum_ofty_unfold_own.
        iExists (pinj j a, pad). iSplit; [done|].
        rewrite /bofty_owned (cbytes_sum _ j (tyl +!! j)). by iFrame. }
      iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|]. iModIntro.
      wp_pure _. wp_case. { split; [lia|]. by rewrite Nat2Z.id -vlookup_lookup plistc_to_vec_lookup. }
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
      (case: ToLit (Load Na1Ord (MInt (sum_tag 𝔄l)) (pctx_expr K (ToLit p))) of el)
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
        rewrite lty_fold_sum_ofty /ltype_own /= /bofty_owned. iDestruct "N" as (? ->) "[$ $]".
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
End sum_deep.
