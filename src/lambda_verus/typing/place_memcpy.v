(** * Byte copies between places

  A byte copy [pctx_vexpr Kd pd <-ᵇ{n} pctx_vexpr Ks ps] ([memcpy], a [MemCopy] of [n]
  bytes) copies the bytes of the leaf at the hole of the source place
  [ps ◁ₗ pctx_plug Ks …] into the leaf [ltd] at the hole of the destination place
  [pd ◁ₗ pctx_plug Kd ltd]. It is byte-preserving (no decode/encode); there is no
  typed memcpy (a round trip through a value is a typed [Load] and a typed [Store]). Two
  rules, by the source:

  - [type_memcpy_copy_place_instr]: the source is any place readable as in
    [type_read_place_instr] ([place_read.v]: a [Copy] leaf, [pctx_rleaf], below any mix of
    fields, sums, owned pointers, unique borrows, shared references and resolved unique
    borrows); it does not change; the access to it is [wp_vplace_racc].
  - [type_memcpy_move_place_instr]: the source is any leaf [OfTy ty] of an owned path, as
    in [type_move_place_instr] ([place_own.v]); its value may contain cells, which are moved
    with the bytes; it becomes moved-out ([Moved ty]). The access to it is
    [wp_vplace_macc].

  The two differ in what happens to the source (a shared or owned read of a [Copy] value,
  which stays, against the transfer of the fancy bytes of any value, with its cells); a
  common statement would need a computed source type and transformer, for no gain.

  The destination is any leaf writable as in [type_write_place_instr] ([place_write.v]),
  with the new type [ty] of the source ([pctx_wty]: an [OfTy] leaf of the same type, or,
  along an owned path without sums, of any type of the same size, e.g. a box [↯ n] gets
  the type of the copied value; a moved-out leaf [Moved ty], re-initialized); the old value
  of an [OfTy] leaf is resolved ([lty_wres]), and its access is [wp_vplace_wacc].

  The first step (of the address of the destination) gives the credits for the access to
  the destination and the resolution, and the cumulative time receipts to raise its depths;
  the first step of the address of the source those for the access to the source. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From lrust.lang Require Import proofmode.
From lrust.typing Require Export type ltype lpath pctx_acc vplace place_own place_write place_read.
From lrust.typing Require Import type_context programs lft_contexts uniq_util uniq_bor own shr_bor bytes_layout value_ctx unit uninit freeable_util place_puniq gmb_cells.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section memcpy.
  Context `{!typeG Σ}.

  (** Copying the bytes of a readable [Copy] leaf into a writable leaf. *)
  Lemma type_memcpy_copy_place_instr {𝔅d 𝔄d 𝔅 𝔄 𝔄d'} E L I pd ps (Kd: pctx 𝔅d 𝔄d)
      `{!PctxNoShr Kd} `{!PctxVRoot Kd} (ltd: lty 𝔅d) (Kd': pctx 𝔅 𝔄d') fd Φ
      (Ks: pctx 𝔅 𝔄) `{!PctxVRoot Ks} `{!PctxRead Ks} (lt: lty 𝔅) (ty: type 𝔅) κs :
    pctx_wty Kd ltd ty Kd' fd → lty_wres E L ltd Φ →
    lctx_lft_alive E L (pctx_alv Kd ltd) →
    pctx_rleaf Ks lt ty κs → Copy ty → lctx_lft_alive E L (pctx_alv Ks lt ⊓ κs) →
    typed_instr E L I +[pd ◁ₗ pctx_plug Kd ltd; ps ◁ₗ pctx_plug Ks lt]
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
    iAssert (fractional.half γ2 &&{↑NllftG}&&> @[pctx_ulft Kd ltd])%I as "#GAd".
    { iApply (guards_transitive with "Gh2"). iApply (guards_transitive with "Ghalf").
      iApply (guards_transitive with "Alvd"). by iApply pctx_alv_noshr. }
    iAssert (fractional.half γ2 &&{↑NllftG}&&> @[pctx_alv Ks lt ⊓ κs])%I as "#GBs".
    { iApply (guards_transitive with "Gh2"). iApply (guards_transitive with "Ghalf Alvs"). }
    iCombine "⧖d ⧖s" as "⧖m". set M := Dd `max` Ds.
    have HM: Dd ≤ M ∧ Ds ≤ M by rewrite /M; lia.
    (* The first step of the address of the destination: credits and cumulative time
       receipts. *)
    wp_bind (place_addr (pctx_vexpr Kd pd)).
    iApply (wp_cumulative_time_receipt_linear with "TIME ⧖m"); [solve_ndisj|].
    iIntros "⧗".
    iDestruct (cumulative_time_receipt_sep 1 (S M) with "⧗") as "[⧗c ⧗k]".
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗c ⧖m") as "[_ £]";
      [solve_ndisj|].
    iDestruct (lc_weaken ((3 * Dd + 5) + (1 + (1 + Dd * (Dd + 1))) + 1) with "£")
      as "[[£a [£r £s]] £f]"; [rewrite /advance_credits; nia|].
    iDestruct (invctx_interp_gcells with "I") as "[#GC I]".
    wp_bind (pctx_vexpr Kd pd).
    iApply (wp_vplace_wacc _ Kd ltd ty Kd' fd with "LFT PROPH UNIQ GAd A £a ⧖d ⧗d Ownd");
      [done|solve_ndisj|done|].
    iIntros (ld dh gh [Hdh Hgh]) "Oldd Cld". wp_pure _.
    (* Resolve the old value of the destination; its bytes. *)
    iCombine "£r £s £f" as "£r".
    iDestruct (lc_weaken (1 + (1 + Dd * (Dd + 1)) + 1) with "£r") as "£r"; [lia|].
    iMod (lty_wold_resolve E L ltd Φ _ dh gh Dd with "LFT PROPH UNIQ TIME E Ghalf H2 GC £r Oldd")
      as "(Obs' & H2 & %bsd & Hbsd & %Hlend)"; [done|lia|lia|solve_lazyE|].
    (* The first step of the address of the source: credits for its access. *)
    wp_bind (place_addr (pctx_vexpr Ks ps)).
    iApply (wp_persistent_time_receipt with "TIME ⧖s"); [solve_ndisj|].
    iIntros "£s _". wp_bind (pctx_vexpr Ks ps).
    iApply (wp_vplace_racc _ Ks lt ty κs with "LFT PROPH UNIQ GBs B £s ⧖s ⧗s Owns");
      [done|solve_ndisj|done|].
    rewrite /vplace_rcont.
    iIntros (ls G2 dd dhs ghs ([w Hw'] & ? & ?)) "#Guard G2 £dd #Ghos Cls".
    wp_pure _.
    (* Copy the bytes. *)
    iApply wp_fupd.
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
  (** Moving the bytes (and the cells) of a leaf of an owned path into a writable leaf; the
      source becomes moved-out ([Moved ty]). *)
  Lemma type_memcpy_move_place_instr {𝔅d 𝔄d 𝔅 𝔄 𝔄d'} E L I pd ps (Kd: pctx 𝔅d 𝔄d)
      `{!PctxNoShr Kd} `{!PctxVRoot Kd} (ltd: lty 𝔅d) (Kd': pctx 𝔅 𝔄d') fd Φ
      (Ks: pctx 𝔅 𝔄) `{!PctxVRoot Ks} `{!PctxNoUniq Ks} (ty: type 𝔅) :
    pctx_wty Kd ltd ty Kd' fd → lty_wres E L ltd Φ →
    lctx_lft_alive E L (pctx_alv Kd ltd) →
    typed_instr E L I +[pd ◁ₗ pctx_plug Kd ltd; ps ◁ₗ pctx_plug Ks (OfTy ty)]
      (pctx_vexpr Kd pd <-ᵇ{ty_bsize ty} pctx_vexpr Ks ps)
      (λ _, +[pd ◁ₗ pctx_plug Kd' (OfTy ty); ps ◁ₗ pctx_plug Ks (Moved ty)])
      (λ post '-[xd; xs], λ mask π, Φ (pctx_get Kd xd.1) π →
        post -[(fd xd.1 (pctx_get Ks xs.1), xd.2); xs] mask π).
  Proof.
    intros Hw Rslv Alvd.
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
    iAssert (fractional.half γh &&{↑NllftG}&&> @[pctx_ulft Kd ltd])%I as "#GAd".
    { iApply (guards_transitive with "Ghalf").
      iApply (guards_transitive with "Alvd"). by iApply pctx_alv_noshr. }
    iCombine "⧖d ⧖s" as "⧖m". set M := Dd `max` Ds.
    have HM: Dd ≤ M ∧ Ds ≤ M by rewrite /M; lia.
    (* The first step of the address of the destination: credits and cumulative time
       receipts. *)
    wp_bind (place_addr (pctx_vexpr Kd pd)).
    iApply (wp_cumulative_time_receipt_linear with "TIME ⧖m"); [solve_ndisj|].
    iIntros "⧗".
    iDestruct (cumulative_time_receipt_sep 1 (S M) with "⧗") as "[⧗c ⧗k]".
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗c ⧖m") as "[_ £]";
      [solve_ndisj|].
    iDestruct (lc_weaken ((3 * Dd + 5) + (1 + (1 + Dd * (Dd + 1)) + 1)) with "£")
      as "[£a £r]"; [rewrite /advance_credits; nia|].
    iDestruct (invctx_interp_gcells with "I") as "[#GC I]".
    wp_bind (pctx_vexpr Kd pd).
    iApply (wp_vplace_wacc _ Kd ltd ty Kd' fd with "LFT PROPH UNIQ GAd H1 £a ⧖d ⧗d Ownd");
      [done|solve_ndisj|done|].
    iIntros (ld dh gh [Hdh Hgh]) "Oldd Cld". wp_pure _.
    (* Resolve the old value of the destination; its bytes. *)
    iMod (lty_wold_resolve E L ltd Φ _ dh gh Dd with "LFT PROPH UNIQ TIME E Ghalf H2 GC £r Oldd")
      as "(Obs' & H2 & %bsd & Hbsd & %Hlend)"; [done|lia|lia|solve_lazyE|].
    (* The first step of the address of the source: credits for its access. *)
    wp_bind (place_addr (pctx_vexpr Ks ps)).
    iApply (wp_persistent_time_receipt with "TIME ⧖s"); [solve_ndisj|].
    iIntros "£s _". wp_bind (pctx_vexpr Ks ps).
    iDestruct (lc_weaken (Ds + 1 + 1) with "£s") as "[[£s £g] £m]";
      [rewrite /advance_credits; nia|].
    iApply (wp_vplace_macc _ Ks ty xs₀ ζs Ds tid ps vs with "£s ⧖s ⧗s Owns"); [done|].
    iIntros (ls dhs ghs [Hdhs Hghs]) "Pts Ghos Cls". wp_pure _.
    (* Move the bytes. *)
    iApply wp_fupd.
    iDestruct (bytes_own_fval with "Pts") as %[fv Hfv].
    iEval (rewrite /cbytes (bytes_own_gcont _ _ _ fv) //) in "Pts".
    iApply (wp_gcont_memcopy with "[$GC $£m $Pts $Hbsd]");
      [solve_ndisj|apply ty_mty_wf|rewrite Hlend; by rewrite -(pctx_wty_bsize _ _ _ _ _ Hw)|].
    iIntros "!>" (bs) "(Hbs & %Hlen & Cd)".
    iMod (fupd_mask_subseteq (⊤ ∖ ↑advN)) as "Hcl"; [solve_ndisj|].
    (* Close the source, moved-out. *)
    iDestruct ("Cls" with "Hbs [%]") as "Ts".
    { done. }
    (* Close the destination at the moved value. *)
    iDestruct (cumulative_time_receipt_mono (pctx_dlev Kd) with "⧗k") as "⧗k"; [lia|].
    iMod (cumulative_persistent_time_receipt with "TIME ⧗k ⧖s") as "#⧖k"; [solve_ndisj|].
    set Dn := Dd `max` (pctx_dlev Kd + Ds).
    iCombine "⧖d ⧖k" as "⧖D".
    iMod ("Cld" $! (pctx_get Ks xs₀) dhs ghs Dn with "[%] [] [Cd] Ghos") as "[Td H1]".
    { rewrite /Dn. lia. }
    { iApply (persistent_time_receipt_mono with "⧖D"). rewrite /Dn. lia. }
    { by rewrite /cbytes (bytes_own_gcont _ _ _ fv). }
    iMod "Hcl" as "_".
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iModIntro.
    iExists -[(fd xd₀ (pctx_get Ks xs₀), ζd); (xs₀, ζs)]. iFrame "L I".
    iSplitR "Obs Obs'".
    { iSplitL "Td"; [iExists _; by iFrame|]. iSplit; [|done]. iExists _. by iFrame. }
    iCombine "Obs Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=> π [Hπ HΦ].
    by apply Hπ.
  Qed.
End memcpy.
