(** * Places rooted at an owned location

  This file adds the rules for place elements rooted at an _owned_ location, i.e. the pointee of an owned pointer
  [own_bytes n] (a [Box], or a stack slot holding a local variable): [p ◁ₗown{n} lt]
  says that [p] is an owned pointer whose pointee has the place type [lt], in [Owned 1]
  mode (one later for the ghost parts, as in [own_bytes]; so the conversions
  [tctx_own_to_oplace], [tctx_oplace_to_own] are inclusions). Its value is a pair of
  the value of the owned pointer [(l, x₀)] and a blocking map [ζm] ([vplace.v]:
  [p ◁ₗown{n} lt] is [p ◁ₗ OwnPtrLty n lt]):
  the refinement of the place is [lty_rfn lt x₀ ζm []].

  There is no outer borrow: blocking a leaf (a mutable borrow of a subplace at some
  lifetime [α], [type_borrow_place_instr] of [place_puniq.v]) leaves in the place the inheritance of the
  new borrow (pending ownership, [blocked_owned]), which is fired when [α] has ended
  ([unblock_tctx_oplace]). A leaf can be read (copied, [type_read_place_instr] of
  [place_read.v]), moved
  out (leaving it uninitialized, [type_move_place_instr], the unified place move: any
  owned path of fields and owned pointers) and written ([type_write_place_instr] of
  [place_write.v], which also re-initializes an uninitialized leaf). Moving out and
  writing change the type of the leaf, so the place context is retyped ([pctx_retype]). Folding back gives an owned pointer whose type may have
  uninitialized components. An owned pointer below other owned pointers (two or more
  laters deep) is unfolded by an instruction ([type_unfold_oplace_own_instr]). All leaf
  operations are of values of size 1, at any path
  (the address is computed by [pctx_expr], one load per owned pointer above the
  leaf). *)

From iris.proofmode Require Import proofmode.
From lrust.lang Require Import proofmode.
From lrust.typing Require Export type ltype lpath vplace.
From lrust.typing Require Import type_context programs lft_contexts uniq_util uniq_bor own shr_bor bytes_layout value_ctx product uninit freeable_util.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section typing.
  Context `{!typeG Σ}.

  (** * Converting between owned pointers and owned places *)

  Lemma tctx_own_to_oplace {𝔄} E L p n (ty: type 𝔄) :
    tctx_incl E L +[p ◁ᵥ own_bytes n ty] +[p ◁ₗown{n} OfTy ty] (λ post '-[a], post -[(a, [])]).
  Proof.
    split; [by intros ??? [? []]|].
    iIntros (G tid [[l x] []] mask post ?) "_ _ _ _ _ $ [T _] Obs".
    iDestruct (tctx_val_elim with "T") as (v Hp w D [-> Hw]) "(⧖ & Own)". simpl in Hw. simplify_eq.
    destruct D as [|d]; [done|]. iDestruct "Own" as "(Pt & Fr & Gho)".
    iMod cumulative_time_receipt_0 as "⧗".
    iModIntro. iExists -[((l, x), [])]. iFrame "Obs". iSplit; [|done].
    rewrite /tctx_elt_interp. iExists _. iSplit; [done|].
    iExists (S d), d, (S d). rewrite /lty_size -(ty_bsize_eq ty). iFrame "⧖ ⧗ Fr".
    iSplit; [done|]. iSplit; [iPureIntro; lia|].
    rewrite /ltype_own /= /ofty_owned. iExists x. iSplit; [done|]. by iFrame "Gho".
  Qed.

  Lemma tctx_oplace_to_own {𝔄} E L p n (ty: type 𝔄) :
    tctx_incl E L +[p ◁ₗown{n} OfTy ty] +[p ◁ᵥ own_bytes n ty] (λ post '-[x], post -[x.1]).
  Proof.
    split; [by intros ??? [? []]|].
    iIntros (G tid [[[l x] ζm] []] mask post ?) "_ _ _ _ _ $ [T _] Obs".
    iDestruct "T" as (v Hp D d g) "(⧖ & _ & -> & %Hle & Fr & Own)".
    rewrite /ltype_own /= /ofty_owned. iDestruct "Own" as (? ->) "[Pt Gho]".
    iModIntro. iExists -[(l, x)]. iFrame "Obs". iSplit; [|done].
    iExists _. iSplit; [done|]. rewrite -(val_own_intro_sep _ _ _ _ (VPtr l) D); [|done|done]. iFrame "⧖".
    destruct D as [|D]; [lia|]. simpl. rewrite /lty_size -(ty_bsize_eq ty). iFrame "Fr".
    iFrame "Pt". iNext.
    iDestruct (ty_gho_own_depth_mono _ d g D (S D) with "Gho") as "[$ _]"; lia.
  Qed.

  (** * Changing the place type of a subplace *)

  Lemma tctx_oplace_change_hole {𝔅 𝔄} E L p n (K: pctx 𝔅 𝔄) `{!PctxNoUniq K} (lt lt': lty 𝔅) :
    lty_size lt' = lty_size lt → lty_nrc lt' = lty_nrc lt →
    (∀ y ζm q d g tid l, ltype_own (Owned (pctx_mode K 1)) lt (lty_rfn lt y ζm q) d g tid l ={⊤}=∗
       ltype_own (Owned (pctx_mode K 1)) lt' (lty_rfn lt' y ζm q) d g tid l) →
    tctx_incl E L +[p ◁ₗown{n} pctx_plug K lt] +[p ◁ₗown{n} pctx_plug K lt']
      (λ post '-[x], post -[x]).
  Proof.
    intros Hsz Hnb Hown. split; [by intros ??? [? []]|].
    iIntros (G tid [[[l x₀] ζm] []] mask post ?) "_ _ _ _ _ $ [T _] Obs".
    iDestruct "T" as (v Hp D d g) "(⧖ & ⧗ & -> & %Hle & Fr & Own)".
    rewrite /ltype_own !lty_pat_plug !lty_rfn_plug !ltype_own_plug.
    iDestruct "Own" as "[H Rest]".
    iMod (Hown with "H") as "H".
    iModIntro. iExists -[((l, x₀), ζm)]. iFrame "Obs". iSplit; [|done].
    rewrite /tctx_elt_interp. iExists (MLitV (VPtr l)). iSplit; [done|]. iExists D, d, g.
    rewrite (lty_nrc_plug_eq K lt lt' Hnb) (lty_size_plug_eq K lt' lt) //. iFrame "⧖ ⧗ Fr".
    iSplit; [done|]. iSplit; [done|].
    rewrite /ltype_own !lty_pat_plug !lty_rfn_plug !ltype_own_plug Hsz. iFrame.
  Qed.

  (** ** Products *)

  Lemma tctx_unfold_oplace_prod {𝔅1 𝔅2 𝔄} E L p n (K: pctx (𝔅1 * 𝔅2) 𝔄) `{!PctxNoUniq K}
      (ty1: type 𝔅1) (ty2: type 𝔅2) :
    tctx_incl E L +[p ◁ₗown{n} pctx_plug K (OfTy (ty1 * ty2))]
      +[p ◁ₗown{n} pctx_plug K (ProdLty (OfTy ty1) (OfTy ty2))] (λ post '-[x], post -[x]).
  Proof.
    apply (tctx_oplace_change_hole _ _ _ _ K); [done|done|].
    iIntros ([y1 y2] ??????) "H !>". by iApply prod_ofty_unfold_own.
  Qed.

  Lemma tctx_fold_oplace_prod {𝔅1 𝔅2 𝔄} E L p n (K: pctx (𝔅1 * 𝔅2) 𝔄) `{!PctxNoUniq K}
      (ty1: type 𝔅1) (ty2: type 𝔅2) :
    tctx_incl E L +[p ◁ₗown{n} pctx_plug K (ProdLty (OfTy ty1) (OfTy ty2))]
      +[p ◁ₗown{n} pctx_plug K (OfTy (ty1 * ty2))] (λ post '-[x], post -[x]).
  Proof.
    apply (tctx_oplace_change_hole _ _ _ _ K); [done|done|].
    iIntros ([y1 y2] ??????) "H !>". by iApply (prod_ofty_unfold_own with "H").
  Qed.

  (* N-ary products ([tctx_unfold_oplace_xprod], [tctx_fold_oplace_xprod]) are in
     [typing/place_xprod.v]: the layout of [Π! (𝔅 :: 𝔅l)] and of [𝔅 * Π! 𝔅l] differ as
     MiniRust types (they have the same bytes, [syn_iso_bytes]). *)

  (** ** Owned pointers

      An owned pointer at a leaf with one later (i.e. below no other owned pointer than
      the root) is unfolded by stripping the later in front of the points-to of its
      pointee (which is timeless). Folding back works at any number of laters. *)

  Lemma ownptr_ofty_unfold_own1 {𝔄} n (ty: type 𝔄) l' x d g tid l E :
    ltype_own (Owned 1) (OfTy (own_bytes n ty)) (inl (PlaceIn (𝔄:=at_locₛ 𝔄) (l', x))) d g tid l
      ={E}=∗
    ltype_own (Owned 1) (OwnPtrLty n (OfTy ty)) (inr (l', inl (PlaceIn x))) d g tid l.
  Proof.
    rewrite /ltype_own /= /ofty_owned /=.
    iIntros "(%v & -> & Pt & H)". destruct d as [|d]; simpl; [by iMod "H"|].
    iDestruct "H" as "(Pt' & Fr & Gho)".
    iEval (rewrite cbytes_at_loc) in "Pt". rewrite /lty_size -(ty_bsize_eq ty).
    iMod "Pt'". iModIntro. iFrame "Pt Fr". iSplit; [done|]. iExists x. iSplit; [done|].
    iFrame.
  Qed.

  Lemma tctx_unfold_oplace_own {𝔅 𝔄} E L p n' (K: pctx (at_locₛ 𝔅) 𝔄) `{!PctxNoUniq K} n (ty: type 𝔅) :
    pctx_mode K 1 = 1%nat →
    tctx_incl E L +[p ◁ₗown{n'} pctx_plug K (OfTy (own_bytes n ty))]
      +[p ◁ₗown{n'} pctx_plug K (OwnPtrLty n (OfTy ty))] (λ post '-[x], post -[x]).
  Proof.
    intros Hm. apply (tctx_oplace_change_hole _ _ _ _ K); [done|done|].
    iIntros ([l' y] ??????) "H". rewrite Hm. by iApply ownptr_ofty_unfold_own1.
  Qed.

  Lemma tctx_fold_oplace_own {𝔅 𝔄} E L p n' (K: pctx (at_locₛ 𝔅) 𝔄) `{!PctxNoUniq K} n (ty: type 𝔅) :
    tctx_incl E L +[p ◁ₗown{n'} pctx_plug K (OwnPtrLty n (OfTy ty))]
      +[p ◁ₗown{n'} pctx_plug K (OfTy (own_bytes n ty))] (λ post '-[x], post -[x]).
  Proof.
    apply (tctx_oplace_change_hole _ _ _ _ K); [done|done|].
    iIntros ([l' y] ??????) "H !>". by iApply (ownptr_ofty_fold_own with "H").
  Qed.

  (** Unfolding an owned pointer at any depth (e.g. a box inside a box inside the root):
      below [k] laters ([pctx_mode K 1 = k]), the points-to of the pointee is stripped of
      its laters with the later credits of a program step. *)
  Lemma type_unfold_oplace_own_instr {𝔅 𝔄} E L I p n' (K: pctx (at_locₛ 𝔅) 𝔄) `{!PctxNoUniq K} n (ty: type 𝔅) :
    typed_instr E L I +[p ◁ₗown{n'} pctx_plug K (OfTy (own_bytes n ty))] Skip
      (λ _, +[p ◁ₗown{n'} pctx_plug K (OwnPtrLty n (OfTy ty))]) (λ post '-[x], post -[x]).
  Proof.
    iIntros (tid post mask iκs [x []]) "#LFT #TIME #PROPH #UNIQ #E L I [T _] Obs".
    destruct x as [[l x₀] ζm].
    rewrite /tctx_elt_interp.
    iDestruct "T" as (v Hp D d g) "(#⧖ & ⧗p & -> & %Hle & Fr & Own)".
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj|]. iIntros "£ _".
    rewrite /ltype_own !lty_pat_plug !lty_rfn_plug !ltype_own_plug.
    iDestruct "Own" as "[L1 Rest]". iSimpl in "L1".
    iDestruct (pctx_own_mode_le with "Rest") as %Hk.
    iDestruct "L1" as (? ->) "[Pt Gho]".
    destruct (pctx_get K x₀) as [l' y] eqn:Hm. iEval (rewrite cbytes_at_loc) in "Pt".
    iDestruct (lc_weaken (pctx_mode K 1) with "£") as "£";
      [rewrite /advance_credits pctx_mode_add; nia|].
    iMod (lc_fupd_elim_laterN with "£ Gho") as "Gho".
    destruct (pctx_depth K d) as [|dh] eqn:Hdh; [done|].
    iDestruct "Gho" as "(Pt' & Fr' & Gho)".
    wp_seq. iExists -[((l, x₀), ζm)]. iFrame "L I Obs". iSplit; [|done].
    rewrite /tctx_elt_interp. iExists (MLitV (VPtr l)). iSplit; [done|]. iExists D, d, g. iFrame "⧖".
    rewrite (lty_nrc_plug_eq K (OfTy (own_bytes n ty)) (OwnPtrLty n (OfTy ty))) //. iFrame "⧗p".
    rewrite (lty_size_plug_eq K (OwnPtrLty n (OfTy ty)) (OfTy (own_bytes n ty))) //.
    iFrame "Fr". iSplit; [done|]. iSplit; [done|].
    rewrite /ltype_own !lty_pat_plug !lty_rfn_plug !ltype_own_plug Hm Hdh /=.
    iFrame "Rest Pt". iSplit; [done|]. rewrite /lty_size -(ty_bsize_eq ty).
    iSplitL "Fr'"; [by iApply bi.laterN_intro|].
    iExists y. iSplit; [done|]. rewrite /ofty_owned.
    iFrame "Pt'". rewrite Nat.add_1_r /=. iNext. by iApply bi.laterN_intro.
  Qed.

  (** * Unblocking a leaf *)

  (** Once [α] has ended, the leaf at the hole of [K] is unblocked: it gets the final
      contents of its borrow, whose value is the final value of the borrow. The current
      value of the place only changes at the hole. Unblocking pays with the cumulative
      time receipt of the blocked leaf. *)
  Lemma unblock_tctx_oplace {𝔅 𝔄 𝔄l 𝔄l'} p n α (K: pctx 𝔅 𝔄) `{!PctxNoUniq K} (ty: type 𝔅)
      (T: tctx 𝔄l) (T': tctx 𝔄l') E L f :
    lctx_lft_alive E L (ty_lft ty) → unblock_tctx E L α T T' f →
    unblock_tctx E L α (p ◁ₗown{n} pctx_plug K (Blocked ty α) +:: T)
      (p ◁ₗown{n} pctx_plug K (OfTy ty) +:: T')
      (λ π '(x -:: xl), λ '(x' -:: xl'),
        x'.1.1 = x.1.1 ∧ x'.1.2 = pctx_set K x.1.2 (pctx_get K x'.1.2) ∧ x'.2 = x.2 ∧
        vπ (pctx_get K x'.1.2) π = oplace_blk_fin K x π ∧ f π xl xl').
  Proof.
    iIntros (Alv Un G tid [x xl] ?) "#LFT #TIME #PROPH #UNIQ #E #L G #†α /=[(%v & %Hp & Own) T]".
    destruct x as [[l x₀] ζm].
    iDestruct "Own" as (D d g) "(#⧖0 & ⧗ & -> & %Hle & Fr & Own)".
    iDestruct (cumulative_time_receipt_mono (lty_nrc (pctx_plug K (OfTy ty)) 0 0 + 1)
      with "⧗") as "⧗"; [rewrite lty_nrc_plug_blocked; lia|].
    iDestruct (cumulative_time_receipt_sep with "⧗") as "[⧗r ⧗b]".
    leaf_open "L" with "G" as "[L1 back]"; [set_solver|].
    iDestruct (Alv with "L1 E") as "#Lty". iMod ("back" with "L1") as "G".
    (* Half of [G] for the rest of the context, the other half for the place. *)
    iMod (fractional.frac_split_guard_in_half with "G L") as (γ1) "[GT [GP [#GhT #BackT]]]";
      [solve_ndisj|].
    iMod (Un with "LFT TIME PROPH UNIQ E GhT GT †α T") as (dT xl') "[#⧖T ToT']".
    iDestruct (guards_transitive with "GhT Lty") as "#Gty".
    rewrite /ltype_own lty_pat_plug lty_rfn_plug ltype_own_plug.
    iDestruct "Own" as "[L1 Rest]". iSimpl in "L1".
    iDestruct (pctx_own_in with "Rest") as %Hin.
    set y := pctx_get K x₀. set ζi := blk_lookup ζm (pctx_path K []).
    set k0 := pctx_mode K 0.
    (* Unblock the leaf: fire the inheritance of the borrow and settle it. *)
    iDestruct (blocked_owned_fire with "L1 †α") as "Upd1".
    iMod (fupd_mask_mono with "Upd1") as "Upd1"; [rewrite /lazyB; solve_ndisj|].
    iMod (guarded_upd_run with "Gty GP Upd1") as "(GP & %y1 & %d1 & %g1 & Eqz & #⧖1 & O1)";
      [rewrite /lazyE; solve_ndisj|].
    iDestruct "O1" as "[Pt1 Gho1]".
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗b ⧖1") as "[_ £]";
      [solve_ndisj|].
    iDestruct (lc_weaken (pctx_mode K 1 + (1 + (d1 + d1*(g1+2) + (0 + (d1+1)*(g1+1)) + 1 + 1)))
      with "£") as "[£k [£e £]]"; [rewrite /advance_credits; nia|].
    iMod (lc_fupd_elim_laterN with "£k Gho1") as "Gho1".
    iSimpl in "Eqz". iMod (lc_fupd_elim_later with "£e Eqz") as "Eqz".
    iMod (proph_eqz_obs_by_share ty with "LFT Gty GP £ Eqz Gho1") as "(#Obs1 & GP & Gho1)".
    (* Close the place at the unblocked state, at the maximal depths. *)
    set d'' := (d1 + k0) `max` d. set g'' := g1 `max` g.
    have Hdh: d1 ≤ pctx_depth K d''. { rewrite pctx_depth_sub. lia. }
    iDestruct (ty_gho_own_depth_mono _ d1 g1 (pctx_depth K d'') g'' with "Gho1")
      as "[Gho1 _]"; [lia..|].
    iDestruct (pctx_own_depth_mono _ _ _ _ _ _ _ _ d'' g'' with "Rest") as "Rest"; [lia..|].
    iCombine "⧖0 ⧖1" as "⧖D".
    iModIntro. iExists dT, (((l, pctx_set K x₀ y1), ζm) -:: xl').
    iSplitR; [done|].
    iMod "ToT'". iModIntro. iNext. iMod "ToT'". iModIntro.
    iApply (step_fupdN_wand with "ToT'"). iIntros ">(GT & T' & #Obs')".
    iMod (fupd_mask_mono with "(BackT GT GP)") as "$"; [solve_ndisj|].
    iModIntro. iSplitR "Obs'".
    { iFrame "T'". rewrite /tctx_elt_interp. iExists (MLitV (VPtr l)). iSplit; [done|].
      iExists (D `max` ((pctx_mode K 1 + S d1) `max` g1)), d'', g''. iFrame "⧖D ⧗r".
      rewrite (lty_size_plug_eq K (OfTy ty) (Blocked ty α)) //. iFrame "Fr".
      iSplit; [done|]. iSplit; [iPureIntro; rewrite pctx_mode_add; lia|].
      rewrite /ltype_own lty_pat_plug lty_rfn_plug pctx_get_set pctx_rfn_set // ltype_own_plug.
      iFrame "Rest". iExists y1. by iFrame. }
    iCombine "Obs1 Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=> π [Heq Hf].
    split; [done|]. split; [by rewrite /= pctx_get_set|]. split; [done|]. split; [|done].
    rewrite /oplace_blk_fin /= pctx_get_set. symmetry. exact Heq.
  Qed.

  (** * The unified place move

      The access to a leaf [OfTy ty] at the hole of [K] whose path from the root is owned
      ([PctxNoUniq]; its root step, [PctxVRoot], is an owned pointer): a CPS around the
      address of the hole ([pctx_vexpr K p]), which gives the bytes and the ownership of the
      value of the leaf (without laters, with the later credits [£D]), and a closer that
      leaves the leaf moved-out ([Moved ty]) given plain bytes of its size, at the same
      value of the place. *)
  Lemma wp_vplace_macc {𝔅 𝔄} E (K: pctx 𝔅 𝔄) `{!PctxVRoot K} `{!PctxNoUniq K}
      (ty: type 𝔅) x₀ ζm D tid p v Φ :
    eval_path p = Some v →
    £D -∗ ⧖D -∗ ⧗(lty_vnrc (pctx_plug K (OfTy ty))) -∗
    vroot_own (pctx_plug K (OfTy ty))
      (pctx_vrfn K x₀ ζm (lty_rfn (OfTy ty) (pctx_get K x₀) ζm (pctx_vpath K))) D tid v -∗
    (∀ (l: loc) dh gh, ⌜dh ≤ D ∧ gh ≤ D⌝ -∗
      cbytes ty (pctx_get K x₀) l -∗ ty_gho_own ty (pctx_get K x₀) dh gh tid -∗
      (∀ bs, l ↦b bs -∗ ⌜length bs = ty_bsize ty⌝ -∗
        vplace_own (pctx_plug K (Moved ty)) (x₀, ζm) tid v) -∗ Φ #l) -∗
    WP pctx_vexpr K p @ E {{ Φ }}.
  Proof.
    rename select (PctxVRoot K) into HR. rename select (PctxNoUniq K) into HK.
    destruct K as [| | |? 𝔄' n K| | | |]; try done; rewrite /PctxNoUniq /= in HK.
    have ?: PctxNoUniq K by done.
    iIntros (Hp) "£ #⧖ ⧗p Own HΦ".
    destruct x₀ as [l x₀]. rewrite /=.
    iDestruct "Own" as (d g -> Hle) "[Fr Own]".
    rewrite /ltype_own lty_pat_plug ltype_own_plug.
    iDestruct "Own" as "[L1 Rest]". iSimpl in "L1".
    iDestruct "L1" as (? ->) "[Pt1 Gho1]".
    iDestruct (pctx_own_mode_le with "Rest") as %Hk.
    iApply wp_fupd.
    iApply (wp_wand with "[Rest]").
    { iApply (wp_pctx_expr_mask E K (lty_size (OfTy ty)) 1 x₀ ζm [] d g tid l p True True
        with "[] Rest").
      wp_bind p. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->".
      iFrame; by iPureIntro. }
    iIntros (w) "(-> & _ & _ & Rest)".
    iDestruct (lc_weaken (pctx_mode K 1) with "£") as "£"; [rewrite pctx_mode_add; lia|].
    iMod (lc_fupd_elim_laterN with "£ Gho1") as "Gho1". iModIntro.
    iApply ("HΦ" with "[%] Pt1 Gho1"). { rewrite pctx_depth_sub. lia. }
    iIntros (bs) "Hbs %Hlen".
    iExists D. iFrame "⧖".
    rewrite /lty_vnrc /= (lty_nrc_plug_eq K (OfTy ty) (Moved ty)) //. iFrame "⧗p".
    iExists d, g. iSplit; [done|]. iSplit; [done|].
    rewrite (lty_size_plug_eq K (Moved ty) (OfTy ty)) //. iFrame "Fr".
    rewrite /ltype_own lty_pat_plug lty_rfn_plug ltype_own_plug /=.
    iFrame "Rest". rewrite /moved_leaf /pad_cell. iExists bs. by iFrame "Hbs".
  Qed.

  (** Moving the value out of the leaf [OfTy ty] at the hole of [K], in a place rooted at a
      value whose path from the root is owned: [K] is below no unique borrow, shared
      reference or resolved unique borrow ([PctxNoUniq]), so its root step ([PctxVRoot]) is
      an owned pointer ([p ◁ₗ pctx_plug (POwn n K') (OfTy ty)] is
      [p ◁ₗown{n} pctx_plug K' (OfTy ty)]); the path is made of fields, sum payloads and
      owned pointers. The instruction is a typed [Load] ([!ᵐ{ty_mty ty}], [read_move]) at
      the address of the hole; the value may contain cells, which are moved with it
      ([val_cells]). The leaf becomes moved-out ([Moved ty]: its bytes are kept, plain);
      the value of the place does not change (the value of a moved-out leaf is
      irrelevant). *)
  Lemma type_move_place_instr {𝔅 𝔄} E L I p (K: pctx 𝔅 𝔄) `{!PctxVRoot K} `{!PctxNoUniq K}
      (ty: type 𝔅) :
    typed_instr E L I +[p ◁ₗ pctx_plug K (OfTy ty)] (!ᵐ{ty.(ty_mty)} (pctx_vexpr K p))
      (λ v, +[v ◁ᵥ ty; p ◁ₗ pctx_plug K (Moved ty)])
      (λ post '-[x], post -[pctx_get K x.1; x]).
  Proof.
    iIntros (tid post mask iκs [x []]) "#LFT #TIME #PROPH #UNIQ #E L I (Tp & _) Obs".
    destruct x as [x₀ ζm]. rewrite /read_move.
    iDestruct "Tp" as (v Hp) "Tp". iEval (rewrite vplace_own_open) in "Tp".
    iDestruct "Tp" as (D) "(#⧖ & ⧗p & Own)".
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj|].
    iIntros "£ #⧖S".
    iDestruct (lc_weaken (D + 1) with "£") as "[£ £1]"; [rewrite /advance_credits; nia|].
    wp_bind (pctx_vexpr K p).
    iApply (wp_vplace_macc _ K ty x₀ ζm D tid p v with "£ ⧖ ⧗p Own"); [done|].
    iIntros (l dh gh [Hdh Hgh]) "Pt1 Gho1 Cl".
    iApply wp_fupd.
    iDestruct (invctx_interp_gcells with "I") as "[#GC I]".
    iApply (wp_bytes_own_move with "[$GC $£1 $Pt1]"); [solve_ndisj|].
    iIntros "!>" (vw fv bs) "(%Hfv & Hc & Hbs & %Hlen)". iModIntro.
    iExists -[pctx_get K x₀; (x₀, ζm)]. iFrame "L I Obs".
    iSplitR "Hbs Cl".
    { iExists _. iSplit; [by rewrite eval_path_of_val|]. iExists vw, D, fv. iSplit; [done|].
      iFrame "Hc ⧖". iDestruct (ty_gho_own_depth_mono _ dh gh D D with "Gho1") as "[$ _]"; lia. }
    iSplit; [|done]. iExists v. iSplit; [done|]. by iApply ("Cl" with "Hbs").
  Qed.
End typing.
