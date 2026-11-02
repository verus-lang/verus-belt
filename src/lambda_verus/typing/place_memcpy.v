(** * Byte copies between places

  A byte copy [pctx_vexpr Kd pd <-ᵇ{n} pctx_vexpr Ks ps] ([memcpy], a [MemCopy] of [n]
  bytes) copies the bytes of the leaf at the hole of the source place
  [ps ◁ₗ pctx_plug Ks …] into the leaf [OfTy tyd] at the hole of the destination place
  [pd ◁ₗ pctx_plug Kd (OfTy tyd)]. It is byte-preserving (no decode/encode); there is no
  typed memcpy (a round trip through a value is a typed [Load] and a typed [Store]). Two
  rules, by the source:

  - [type_memcpy_copy_place_instr]: the source is any place readable as in
    [type_read_place_instr] ([place_read.v]: a [Copy] leaf, [pctx_rleaf], below any mix of
    fields, sums, owned pointers, unique borrows, shared references and resolved unique
    borrows); it does not change; the access to it is [wp_vplace_racc].
  - [type_memcpy_move_place_instr]: the source is any leaf [OfTy ty] of an owned path
    without sums, as in [type_move_place_instr] ([place_own.v]); its value may contain
    cells, which are moved with the bytes; it becomes uninitialized ([↯]). The access to
    it is [wp_vplace_wacc] (a strong update to [↯]).

  The two differ in what happens to the source (a shared or owned read of a [Copy] value,
  which stays, against the transfer of the fancy bytes of any value, with its cells); a
  common statement would need a computed source type and transformer, for no gain.

  The destination is any place writable as in [type_write_place_instr] ([place_write.v]),
  with the new type [ty] of the source ([pctx_wty]: the same type, or, along an owned path
  without sums, any type of the same size: e.g. a box [↯ n] gets the type of the copied
  value); its old value is resolved, and its access is [wp_vplace_wacc].

  The first step (of the address of the destination) gives the credits for the access to
  the destination and the resolution, and the cumulative time receipts to raise its depths;
  the first step of the address of the source those for the access to the source. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From lrust.lang Require Import proofmode.
From lrust.typing Require Export type ltype lpath pctx_acc vplace place_own place_write place_read.
From lrust.typing Require Import type_context programs lft_contexts uniq_util uniq_bor own shr_bor bytes_layout value_ctx product uninit freeable_util place_puniq.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section memcpy.
  Context `{!typeG Σ}.

  (** The address of the hole of a context whose first step is the root pointer is not a
      value: its first program step gives credits and time receipts. *)
  Lemma pctx_expr_to_val {𝔅 𝔄} (K: pctx 𝔅 𝔄) e : to_val e = None → to_val (pctx_expr K e) = None.
  Proof. induction K in e |- *; simpl; [done|auto|intros; by apply IHK..]. Qed.

  Lemma pctx_vexpr_to_val {𝔅 𝔄} (K: pctx 𝔅 𝔄) `{!PctxVRoot K} e : to_val (pctx_vexpr K e) = None.
  Proof.
    rename select (PctxVRoot K) into HR. destruct K; try done; by apply pctx_expr_to_val.
  Qed.

  (** Copying the bytes of a readable [Copy] leaf into a writable leaf. *)
  Lemma type_memcpy_copy_place_instr {𝔅d 𝔄d 𝔅 𝔄 𝔄d'} E L I pd ps (Kd: pctx 𝔅d 𝔄d)
      `{!PctxNoShr Kd} `{!PctxVRoot Kd} (tyd: type 𝔅d) (Kd': pctx 𝔅 𝔄d') fd Φ
      (Ks: pctx 𝔅 𝔄) `{!PctxVRoot Ks} `{!PctxRead Ks} (lt: lty 𝔅) (ty: type 𝔅) κs :
    pctx_wty Kd tyd ty Kd' fd → resolve E L tyd Φ →
    lctx_lft_alive E L (pctx_alv Kd (OfTy tyd)) →
    pctx_rleaf Ks lt ty κs → Copy ty → lctx_lft_alive E L (pctx_alv Ks lt ⊓ κs) →
    typed_instr E L I +[pd ◁ₗ pctx_plug Kd (OfTy tyd); ps ◁ₗ pctx_plug Ks lt]
      (pctx_vexpr Kd pd <-ᵇ{ty_bsize ty} pctx_vexpr Ks ps)
      (λ _, +[pd ◁ₗ pctx_plug Kd' (OfTy ty); ps ◁ₗ pctx_plug Ks lt])
      (λ post '-[xd; xs], λ mask π, Φ (pctx_get Kd xd.1) π →
        post -[(fd xd.1 (pctx_get Ks xs.1), xd.2); xs] mask π).
  Proof.
    intros Hw Rslv Alvd Hl Hcopy0 Alvs. assert (NoCell 𝔅) by exact (copy_nocell ty).
    iIntros (tid post mask iκs [xd [xs []]])
      "#LFT #TIME #PROPH #UNIQ #E L I (Td & Ts & _) Obs".
    destruct xd as [xd₀ ζd]. destruct xs as [xs₀ ζs]. rewrite /memcpy.
    iDestruct "Td" as (vd Hpd) "Td". iEval (rewrite vplace_own_open) in "Td".
    iDestruct "Td" as (Dd) "(#⧖d & ⧗d & Ownd)".
    iDestruct "Ts" as (vs Hps) "Ts". iEval (rewrite vplace_own_open) in "Ts".
    iDestruct "Ts" as (Ds) "(#⧖s & ⧗s & Owns)".
    iDestruct (Alvd with "L E") as "#Alvd". iDestruct (Alvs with "L E") as "#Alvs".
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iMod (fractional.frac_split_guard_in_half NllftG (fractional.half γh)
      (fractional.half γh) with "H1 []") as (γ2) "[A [B [#Gh2 #Back2]]]";
      [solve_ndisj|iApply guards_refl|].
    iAssert (fractional.half γ2 &&{↑NllftG}&&> @[pctx_ulft Kd (OfTy tyd)])%I as "#GAd".
    { iApply (guards_transitive with "Gh2"). iApply (guards_transitive with "Ghalf").
      iApply (guards_transitive with "Alvd"). by iApply pctx_alv_noshr. }
    iAssert (fractional.half γ2 &&{↑NllftG}&&> @[pctx_alv Ks lt ⊓ κs])%I as "#GBs".
    { iApply (guards_transitive with "Gh2"). iApply (guards_transitive with "Ghalf Alvs"). }
    iCombine "⧖d ⧖s" as "⧖m". set M := Dd `max` Ds.
    have HM: Dd ≤ M ∧ Ds ≤ M by rewrite /M; lia.
    (* The first step of the address of the destination: credits and cumulative time
       receipts. *)
    wp_bind (pctx_vexpr Kd pd).
    have ?: TCEq (to_val (pctx_vexpr Kd pd)) None by rewrite pctx_vexpr_to_val; constructor.
    iApply (wp_cumulative_time_receipt_linear with "TIME ⧖m"); [solve_ndisj|].
    iIntros "⧗".
    iDestruct (cumulative_time_receipt_sep 1 (S M) with "⧗") as "[⧗c ⧗k]".
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗c ⧖m") as "[_ £]";
      [solve_ndisj|].
    iDestruct (lc_weaken ((3 * Dd + 5) + (1 + (1 + Dd * (Dd + 1)))) with "£")
      as "[£a [£r £s]]"; [rewrite /advance_credits; nia|].
    iApply (wp_vplace_wacc _ Kd tyd ty Kd' fd with "LFT PROPH UNIQ GAd A £a ⧖d ⧗d Ownd");
      [done|solve_ndisj|done|].
    iIntros (ld dh gh [Hdh Hgh]) "Ptd Ghod Cld".
    (* Resolve the old value of the destination. *)
    iDestruct (Rslv _ (⊤ ∖ (⊤ ∖ ↑Nllft ∖ ↑prophN ∖ ↑timeN ∖ ↑uniqN ∖ ↑gmbN))
      with "LFT PROPH UNIQ TIME E Ghalf H2 Ghod") as "ToObs"; [set_solver|].
    iMod (lc_fupd_elim_later with "£r ToObs") as "ToObs".
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iDestruct (lc_step_fupdN_elim_later with "[£s] ToObs") as "ToObs".
    { iApply (lc_weaken with "£s"). nia. }
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iMod (fupd_mask_mono with "ToObs") as "[Obs' H2]"; [solve_ndisj|].
    (* The first step of the address of the source: credits for its access. *)
    wp_bind (pctx_vexpr Ks ps).
    have ?: TCEq (to_val (pctx_vexpr Ks ps)) None by rewrite pctx_vexpr_to_val; constructor.
    iApply (wp_persistent_time_receipt with "TIME ⧖s"); [solve_ndisj|].
    iIntros "£s _".
    iApply (wp_vplace_racc _ Ks lt ty κs with "LFT PROPH UNIQ GBs B £s ⧖s ⧗s Owns");
      [done|solve_ndisj|done|].
    rewrite /vplace_rcont.
    iIntros (ls G2 dd dhs ghs ([w Hw'] & ? & ?)) "#Guard G2 £dd #Ghos Cls".
    (* Copy the bytes. *)
    iApply wp_fupd.
    iApply (wp_bytes_own_forget with "Ptd"); [solve_ndisj|]. iIntros (bsd) "Hbsd %Hlend".
    iApply (wp_memcopy_guarded_gen _ ld ls bsd (ty_bsize ty) G2 (cbytes ty (pctx_get Ks xs₀) ls)
      (ty_bytes ty (pctx_get Ks xs₀)) dd with "[$Hbsd $G2 $£dd]");
      [solve_ndisj|by rewrite Hlend (pctx_wty_bsize _ _ _ _ _ Hw)|intros ?; apply ty_bytes_length|..].
    { iFrame "Guard". iApply bytes_own_view_nocell. }
    iIntros "!>" (bs2) "(%Hbs2 & Hbsd & G2)".
    iMod (fupd_mask_subseteq (⊤ ∖ ↑advN)) as "Hcl"; [solve_ndisj|].
    iMod ("Cls" with "G2") as "[Ts B]".
    (* Close the destination at the copied value. *)
    iDestruct (cumulative_time_receipt_mono (pctx_dlev Kd) with "⧗k") as "⧗k"; [lia|].
    iMod (cumulative_persistent_time_receipt with "TIME ⧗k ⧖s") as "#⧖k"; [solve_ndisj|].
    set Dn := Dd `max` (pctx_dlev Kd + Ds).
    iCombine "⧖d ⧖k" as "⧖D".
    rewrite /vplace_wcloser.
    iMod ("Cld" $! (pctx_get Ks xs₀) dhs ghs Dn with "[%] [] [Hbsd] Ghos") as "[Td A]".
    { rewrite /Dn. lia. }
    { iApply (persistent_time_receipt_mono with "⧖D"). rewrite /Dn. lia. }
    { by iApply bytes_own_of_bytes. }
    iMod "Hcl" as "_".
    iMod (fupd_mask_mono with "(Back2 A B)") as "H1"; [solve_ndisj|].
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iModIntro. iExists -[(fd xd₀ (pctx_get Ks xs₀), ζd); (xs₀, ζs)]. iFrame "L I".
    iSplitR "Obs Obs'".
    { iSplitL "Td"; [iExists _; by iFrame|]. iSplit; [|done]. iExists _. by iFrame. }
    iCombine "Obs Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=> π [Hπ HΦ].
    by apply Hπ.
  Qed.
  (** Moving the bytes (and the cells) of a leaf of an owned path without sums into a
      writable leaf; the source becomes uninitialized. *)
  Lemma type_memcpy_move_place_instr {𝔅d 𝔄d 𝔅 𝔄 𝔄d'} E L I pd ps (Kd: pctx 𝔅d 𝔄d)
      `{!PctxNoShr Kd} `{!PctxVRoot Kd} (tyd: type 𝔅d) (Kd': pctx 𝔅 𝔄d') fd Φ
      (Ks: pctx 𝔅 𝔄) `{!PctxVRoot Ks} `{!PctxNoUniq Ks} (ty: type 𝔅) :
    pctx_wty Kd tyd ty Kd' fd → resolve E L tyd Φ →
    lctx_lft_alive E L (pctx_alv Kd (OfTy tyd)) → pctx_nosum Ks →
    typed_instr E L I +[pd ◁ₗ pctx_plug Kd (OfTy tyd); ps ◁ₗ pctx_plug Ks (OfTy ty)]
      (pctx_vexpr Kd pd <-ᵇ{ty_bsize ty} pctx_vexpr Ks ps)
      (λ _, +[pd ◁ₗ pctx_plug Kd' (OfTy ty);
        ps ◁ₗ pctx_plug (pctx_retype Ks (uninitₛ (ty_bsize ty))) (OfTy (↯ (ty_bsize ty)))])
      (λ post '-[xd; xs], λ mask π, Φ (pctx_get Kd xd.1) π →
        post -[(fd xd.1 (pctx_get Ks xs.1), xd.2);
          (pctx_reset (𝔅':=uninitₛ (ty_bsize ty)) Ks xs.1 (), xs.2)] mask π).
  Proof.
    intros Hw Rslv Alvd Hns.
    have Hws: pctx_wty Ks ty (↯ (ty_bsize ty)) (pctx_retype Ks (uninitₛ (ty_bsize ty)))
      (pctx_reset Ks) by apply pctx_wty_strong.
    iIntros (tid post mask iκs [xd [xs []]])
      "#LFT #TIME #PROPH #UNIQ #E L I (Td & Ts & _) Obs".
    destruct xd as [xd₀ ζd]. destruct xs as [xs₀ ζs]. rewrite /memcpy.
    iDestruct "Td" as (vd Hpd) "Td". iEval (rewrite vplace_own_open) in "Td".
    iDestruct "Td" as (Dd) "(#⧖d & ⧗d & Ownd)".
    iDestruct "Ts" as (vs Hps) "Ts". iEval (rewrite vplace_own_open) in "Ts".
    iDestruct "Ts" as (Ds) "(#⧖s & ⧗s & Owns)".
    iDestruct (Alvd with "L E") as "#Alvd".
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iMod (fractional.frac_split_guard_in_half NllftG (fractional.half γh)
      (fractional.half γh) with "H1 []") as (γ2) "[A [B [#Gh2 #Back2]]]";
      [solve_ndisj|iApply guards_refl|].
    iAssert (fractional.half γ2 &&{↑NllftG}&&> @[pctx_ulft Kd (OfTy tyd)])%I as "#GAd".
    { iApply (guards_transitive with "Gh2"). iApply (guards_transitive with "Ghalf").
      iApply (guards_transitive with "Alvd"). by iApply pctx_alv_noshr. }
    iAssert (fractional.half γ2 &&{↑NllftG}&&> @[pctx_ulft Ks (OfTy ty)])%I as "#GBs".
    { rewrite pctx_ulft_nouniq -llftl_tok_unit_equiv. iApply guards_true. }
    iCombine "⧖d ⧖s" as "⧖m". set M := Dd `max` Ds.
    have HM: Dd ≤ M ∧ Ds ≤ M by rewrite /M; lia.
    (* The first step of the address of the destination: credits and cumulative time
       receipts. *)
    wp_bind (pctx_vexpr Kd pd).
    have ?: TCEq (to_val (pctx_vexpr Kd pd)) None by rewrite pctx_vexpr_to_val; constructor.
    iApply (wp_cumulative_time_receipt_linear with "TIME ⧖m"); [solve_ndisj|].
    iIntros "⧗".
    iDestruct (cumulative_time_receipt_sep 1 (S M) with "⧗") as "[⧗c ⧗k]".
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗c ⧖m") as "[_ £]";
      [solve_ndisj|].
    iDestruct (lc_weaken ((3 * Dd + 5) + (1 + (1 + Dd * (Dd + 1)))) with "£")
      as "[£a [£r £s]]"; [rewrite /advance_credits; nia|].
    iApply (wp_vplace_wacc _ Kd tyd ty Kd' fd with "LFT PROPH UNIQ GAd A £a ⧖d ⧗d Ownd");
      [done|solve_ndisj|done|].
    iIntros (ld dh gh [Hdh Hgh]) "Ptd Ghod Cld".
    (* Resolve the old value of the destination. *)
    iDestruct (Rslv _ (⊤ ∖ (⊤ ∖ ↑Nllft ∖ ↑prophN ∖ ↑timeN ∖ ↑uniqN ∖ ↑gmbN))
      with "LFT PROPH UNIQ TIME E Ghalf H2 Ghod") as "ToObs"; [set_solver|].
    iMod (lc_fupd_elim_later with "£r ToObs") as "ToObs".
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iDestruct (lc_step_fupdN_elim_later with "[£s] ToObs") as "ToObs".
    { iApply (lc_weaken with "£s"). nia. }
    iMod (fupd_mask_mono with "ToObs") as "ToObs"; [solve_ndisj|].
    iMod (fupd_mask_mono with "ToObs") as "[Obs' H2]"; [solve_ndisj|].
    (* The first step of the address of the source: credits for its access. *)
    wp_bind (pctx_vexpr Ks ps).
    have ?: TCEq (to_val (pctx_vexpr Ks ps)) None by rewrite pctx_vexpr_to_val; constructor.
    iApply (wp_persistent_time_receipt with "TIME ⧖s"); [solve_ndisj|].
    iIntros "£s _".
    iDestruct (lc_weaken (3 * Ds + 5) with "£s") as "£s";
      [rewrite /advance_credits; nia|].
    iApply (wp_vplace_wacc _ Ks ty (↯ (ty_bsize ty)) (pctx_retype Ks (uninitₛ (ty_bsize ty)))
      (pctx_reset Ks) with "LFT PROPH UNIQ GBs B £s ⧖s ⧗s Owns");
      [done|solve_ndisj|done|].
    iIntros (ls dhs ghs [Hdhs Hghs]) "Pts Ghos Cls".
    (* Move the bytes. *)
    iApply wp_fupd.
    iApply (wp_bytes_own_forget with "Ptd"); [solve_ndisj|]. iIntros (bsd) "Hbsd %Hlend".
    iEval (rewrite /cbytes bytes_own_brepr) in "Pts".
    iDestruct "Pts" as (fbs fv) "(Hfbs & [%Hlenf %Hfv] & #Hrep)".
    iApply (wp_fbytes_memcopy with "[$Hbsd $Hfbs]");
      [solve_ndisj|rewrite Hlend; by rewrite -(pctx_wty_bsize _ _ _ _ _ Hw)|done|].
    iIntros "!>" (bs) "(Hfbsd & Hbs & %Hlen)".
    iMod (fupd_mask_subseteq (⊤ ∖ ↑advN)) as "Hcl"; [solve_ndisj|].
    (* Close the source, uninitialized. *)
    rewrite /vplace_wcloser.
    iMod ("Cls" $! () 0 0 Ds with "[%] ⧖s [Hbs] []") as "[Ts B]".
    { lia. }
    { iApply (bytes_own_of_bytes with "Hbs"). exists (VTuple []). split; [done|].
      rewrite -(ty_mty_eq (↯ _)) /= decide_True //. }
    { done. }
    (* Close the destination at the moved value. *)
    iDestruct (cumulative_time_receipt_mono (pctx_dlev Kd) with "⧗k") as "⧗k"; [lia|].
    iMod (cumulative_persistent_time_receipt with "TIME ⧗k ⧖s") as "#⧖k"; [solve_ndisj|].
    set Dn := Dd `max` (pctx_dlev Kd + Ds).
    iCombine "⧖d ⧖k" as "⧖D".
    iMod ("Cld" $! (pctx_get Ks xs₀) dhs ghs Dn with "[%] [] [Hfbsd] Ghos") as "[Td A]".
    { rewrite /Dn. lia. }
    { iApply (persistent_time_receipt_mono with "⧖D"). rewrite /Dn. lia. }
    { rewrite /cbytes bytes_own_brepr. iExists fbs, fv. by iFrame "Hfbsd Hrep". }
    iMod "Hcl" as "_".
    iMod (fupd_mask_mono with "(Back2 A B)") as "H1"; [solve_ndisj|].
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iModIntro.
    iExists -[(fd xd₀ (pctx_get Ks xs₀), ζd); (pctx_reset (𝔅':=uninitₛ (ty_bsize ty)) Ks xs₀ (), ζs)]. iFrame "L I".
    iSplitR "Obs Obs'".
    { iSplitL "Td"; [iExists _; by iFrame|]. iSplit; [|done]. iExists _. by iFrame. }
    iCombine "Obs Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=> π [Hπ HΦ].
    by apply Hπ.
  Qed.
End memcpy.
