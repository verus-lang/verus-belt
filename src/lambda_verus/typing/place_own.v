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
  lifetime [α], [type_borrow_oplace_instr]) leaves in the place the inheritance of the
  new borrow (pending ownership, [blocked_owned]), which is fired when [α] has ended
  ([unblock_tctx_oplace]). A leaf can be read (copied, [type_read_place_instr] of
  [place_read.v]), moved
  out (leaving it uninitialized, [type_move_oplace_instr]) and written
  ([type_write_oplace_instr], which also re-initializes an uninitialized leaf). Moving
  out and writing change the type of the leaf, so the place context is retyped
  ([pctx_retype]). Folding back gives an owned pointer whose type may have
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
    rewrite -(tctx_val_intro_sep _ _ _ _ (VPtr l) D); [|done|done]. iFrame "⧖".
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

  (** * Mutable borrow of a leaf *)

  (** A mutable borrow of the leaf at the hole of [K], at a lifetime [α] that the type of
      the leaf outlives. The program computes the address of the leaf ([pctx_expr], a load
      per owned pointer above it). The leaf is blocked until [α] ends, refined by the
      final value of the new borrow (the blocking map gets an entry for the path of the
      hole). *)
  Lemma type_borrow_oplace_instr {𝔅 𝔄} E L I p n α (K: pctx 𝔅 𝔄) `{!PctxNoUniq K} (ty: type 𝔅) :
    elctx_sat E L (ty_outlives_E ty α) →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K (OfTy ty)]
      (Seq (Seq Skip Skip) (OfLit (pctx_expr K (ToLit p))))
      (λ w, +[w ◁ᵥ &uniq{α} ty; p ◁ₗown{n} pctx_plug K (Blocked ty α)])
      (λ post '-[x], λ mask π, ∀ m1: ~~ (uniq_borₛ 𝔅),
        uniq_bor_current m1 = pctx_get K x.1.2 →
        post -[m1; (x.1, (pctx_path K [], uniq_bor_ξi m1) :: x.2)] mask π).
  Proof.
    intros Out tid post mask iκs [x []].
    iIntros "#LFT #TIME #PROPH #UNIQ #E L I [T _] Obs".
    destruct x as [[l x₀] ζm].
    rewrite /tctx_elt_interp.
    iDestruct "T" as (v Hp D d g) "(#⧖ & ⧗p & -> & %Hle & Fr & Own)".
    have ?: Closed [] (pctx_expr K (ToLit p)).
    { apply pctx_expr_closed. have ?: Closed [] p by eapply eval_path_closed. apply _. }
    iDestruct (Out with "L E") as "#Out".
    iDestruct (elctx_interp_ty_outlives_E with "Out") as "#Incl".
    (* Two steps, for credits and cumulative time receipts. *)
    wp_bind (Seq Skip Skip). wp_bind Skip. iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [set_solver|].
    iIntros "£ #⧖S". wp_let. iModIntro. wp_let. iApply wp_fupd.
    iApply (wp_cumulative_time_receipt_linear with "TIME ⧖S"); [set_solver|].
    iIntros "⧗". wp_let. iModIntro. wp_let.
    rewrite /ltype_own lty_pat_plug lty_rfn_plug ltype_own_plug.
    iDestruct "Own" as "[L1 Rest]". iSimpl in "L1".
    iDestruct "L1" as (? ->) "[Pt1 Gho1]".
    iDestruct (pctx_own_mode_le with "Rest") as %Hk.
    set k0 := pctx_mode K 0.
    set y := pctx_get K x₀.
    set lr := l.
    set lK := pctx_loc K (lty_size (OfTy ty)) x₀ lr.
    set dh := pctx_depth K d.
    have Hdh: dh ≤ d. { rewrite /dh pctx_depth_sub. lia. }
    iDestruct (lc_weaken (k0 + 1) with "£") as "[£k £']"; [rewrite /advance_credits; nia|].
    iDestruct (cumulative_time_receipt_mono (1 + (1 + S k0)) with "⧗") as "⧗"; [lia|].
    iDestruct (cumulative_time_receipt_sep with "⧗") as "[⧗a ⧗]".
    iDestruct (cumulative_time_receipt_sep with "⧗") as "[⧗b ⧗k]".
    (* The address of the hole. *)
    iApply wp_fupd. wp_bind (pctx_expr K (ToLit p)).
    iApply (wp_wand with "[Rest]").
    { iApply (wp_pctx_expr K (lty_size (OfTy ty)) 1 x₀ ζm [] d g tid lr (ToLit p) True True
        with "[] Rest").
      - wp_bind p. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->".
        by wp_pure _. }
    iIntros (w) "(-> & _ & _ & Rest)". wp_pure _.
    (* The new borrow. *)
    iEval (rewrite pctx_mode_add bi.laterN_later) in "Gho1".
    iMod (lc_fupd_elim_laterN with "£k Gho1") as "Gho1".
    iMod (alloc_uniq_body ty y dh g α tid lK ⊤ with "LFT PROPH UNIQ [] Gho1 Pt1 ⧗a")
      as (ξi ζi idx) "(Body & _ & Back)"; [solve_ndisj| |].
    { iApply (persistent_time_receipt_mono with "⧖"). lia. }
    iModIntro. iExists -[(lK, y, ξi, dh, g, idx); ((l, x₀), (pctx_path K [], ξi) :: ζm)].
    iFrame "L I". iSplit; last first.
    { iApply (proph_obs_impl with "Obs")=> π Hπ. by apply Hπ. }
    iSplitL "Body".
    { rewrite -(tctx_val_intro_sep _ _ _ _ (VPtr lK) D); [|by rewrite eval_path_of_val|done]. iFrame "⧖". iFrame "Incl Body".
      iPureIntro; lia. }
    iSplit; [|done]. rewrite /tctx_elt_interp. iExists (MLitV (VPtr l)). iSplit; [done|].
    iExists D, d, g. iFrame "⧖".
    rewrite (lty_size_plug_eq K (Blocked ty α) (OfTy ty)) //. iFrame "Fr".
    iSplitL "⧗p ⧗b".
    { iApply (cumulative_time_receipt_mono _ (lty_nrc (pctx_plug K (OfTy ty)) 0 0 + 1)
        with "[⧗p ⧗b]"); [rewrite lty_nrc_plug_blocked; lia|].
      rewrite cumulative_time_receipt_sep. iFrame. }
    iSplit; [done|]. iSplit; [done|].
    rewrite /ltype_own lty_pat_plug lty_rfn_plug ltype_own_plug pctx_own_blk_cons. iFrame "Rest".
    rewrite /= decide_True // /blocked_owned. iIntros "#†α".
    iMod (fupd_mask_mono with "(Back †α)") as "Lender"; [rewrite /lazyE; solve_ndisj|].
    iMod (lc_fupd_elim_later with "£' Lender") as "Lender". iModIntro.
    iApply (guarded_upd_mono with "[⧗k] [Lender]");
      [|iApply (uniq_lender_settle with "LFT PROPH †α Lender")].
    iIntros "(%x & %d1 & %g1 & Eqz & #⧖1 & Gho & Pt)".
    iMod (cumulative_persistent_time_receipt with "TIME ⧗k ⧖1") as "#⧖1'";
      [rewrite /lazyE; solve_ndisj|].
    iModIntro. iExists x, d1, g1. rewrite /ofty_owned /=. iFrame "Eqz Pt Gho".
    iApply (persistent_time_receipt_mono with "⧖1'"). rewrite pctx_mode_add. lia.
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
    iMod (fupd_mask_mono with "(L1 †α)") as "Upd1"; [rewrite /lazyE; solve_ndisj|].
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

  (** * Reading, moving out of and writing a leaf *)

  (** Moving the value out of the leaf at the hole of [K]: a typed [Load]; the leaf becomes
      uninitialized (its type is [↯ (ty_bsize ty)]: its bytes are kept, and represent any
      value of [↯]). *)
  Lemma type_move_oplace_instr {𝔅 𝔄} E L I p n (K: pctx 𝔅 𝔄) `{!PctxNoUniq K}
      (ty: type 𝔅) :
    pctx_nosum K →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K (OfTy ty)]
      (Load Na1Ord ty.(ty_mty) (pctx_expr K (ToLit p)))
      (λ v, +[v ◁ᵥ ty;
        p ◁ₗown{n} pctx_plug (pctx_retype K (uninitₛ (ty_bsize ty))) (OfTy (↯ (ty_bsize ty)))])
      (λ post '-[x], λ mask π, ∀ junk: ~~ (uninitₛ (ty_bsize ty)),
        post -[pctx_get K x.1.2; ((x.1.1, pctx_reset K x.1.2 junk), x.2)] mask π).
  Proof.
    iIntros (Hns tid post mask iκs [x []]) "#LFT #TIME #PROPH #UNIQ #E L I (Tp & _) Obs".
    destruct x as [[l x₀] ζm].
    rewrite /tctx_elt_interp.
    iDestruct "Tp" as (v Hp D d g) "(#⧖ & ⧗p & -> & %Hle & Fr & Own)".
    have ?: Closed [] (pctx_expr K (ToLit p)).
    { apply pctx_expr_closed. have ?: Closed [] p by eapply eval_path_closed. apply _. }
    rewrite /ltype_own lty_pat_plug lty_rfn_plug ltype_own_plug.
    iDestruct "Own" as "[L1 Rest]". iSimpl in "L1".
    iDestruct "L1" as (? ->) "[Pt1 Gho1]".
    iDestruct (pctx_own_mode_le with "Rest") as %Hk.
    set y := pctx_get K x₀.
    set lr := l.
    set lK := pctx_loc K (lty_size (OfTy ty)) x₀ lr.
    set dh := pctx_depth K d.
    have Hdh: dh ≤ d. { rewrite /dh pctx_depth_sub. lia. }
    (* The address of the hole. *)
    wp_bind (pctx_expr K (ToLit p)).
    iApply (wp_wand with "[Rest]").
    { iApply (wp_pctx_expr K (lty_size (OfTy ty)) 1 x₀ ζm [] d g tid lr (ToLit p) True True
        with "[] Rest").
      - wp_bind p. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->".
        by wp_pure _. }
    iIntros (w) "(-> & _ & _ & Rest)".
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj|].
    iIntros "£ #⧖S". iApply wp_fupd.
    iDestruct (lc_weaken (pctx_mode K 1) with "£") as "£";
      [rewrite /advance_credits pctx_mode_add; nia|].
    iMod (lc_fupd_elim_laterN with "£ Gho1") as "Gho1".
    rewrite bytes_own_brepr. iDestruct "Pt1" as (fbs fv) "(Hfbs & [%Hlenf %Hfv] & #Hrep)".
    iApply (wp_fbytes_load with "[$Hfbs $Hrep]"); [solve_ndisj|].
    iIntros "!>" (vw bs) "(Hbs & %Hd & Hus)". iModIntro.
    have Hlen : length bs = ty_bsize ty by rewrite (decode_value_length _ _ _ Hd).
    set junk := (() : ~~ (uninitₛ (ty_bsize ty))).
    iExists -[y; ((l, pctx_reset (𝔅':=uninitₛ (ty_bsize ty)) K x₀ junk), ζm)]. iFrame "L I".
    iSplitR "Obs"; last first.
    { iApply (proph_obs_impl with "Obs")=> π Hπ. by apply Hπ. }
    iSplitR "Hbs Rest ⧗p Fr".
    { iExists _. iSplit; [by rewrite eval_path_of_val|]. iExists vw, D, fv. iSplit; [done|].
      iSplitL "Hus"; [iExists fbs, bs; by iFrame "Hrep Hus"|].
      iFrame "⧖". iDestruct (ty_gho_own_depth_mono _ dh g D D with "Gho1") as "[$ _]"; lia. }
    have Hsz : lty_size (OfTy (↯ (ty_bsize ty))) = lty_size (OfTy ty).
    { rewrite /lty_size. change (syn_bsize (uninitₛ (ty_bsize ty))) with (ty_bsize ty).
      apply ty_bsize_eq. }
    iSplit; [|done]. iExists (MLitV (VPtr l)). iSplit; [done|]. iExists D, d, g. iFrame "⧖".
    rewrite (lty_nrc_plug_retype K (OfTy ty) (OfTy (↯ (ty_bsize ty)))) //.
    rewrite (lty_size_plug_retype K (OfTy ty) (OfTy (↯ (ty_bsize ty)))); [|done|done].
    iFrame "⧗p Fr". iSplit; [done|]. iSplit; [done|].
    rewrite /ltype_own lty_pat_plug lty_rfn_plug pctx_get_reset ltype_own_plug pctx_own_reset //
      pctx_loc_reset // pctx_mode_retype pctx_depth_retype /=.
    rewrite Hsz. iFrame "Rest".
    iExists junk. iSplit; [done|]. rewrite /ofty_owned /=. iSplitL; [|done].
    iApply (bytes_own_of_bytes with "Hbs"). exists (VTuple []). split; [done|].
    rewrite decode_value_tuple decide_True //.
  Qed.

  (** Writing a value into the leaf at the hole of [K] (initialized, or uninitialized
      after a move): a typed [Store] of the MiniRust type of the new value, which has the
      byte size of the leaf. The old value is resolved, and the type of the leaf becomes
      the type of the new value. *)
  Lemma type_write_oplace_instr {𝔅 𝔅' 𝔄} E L I p pb n (K: pctx 𝔅 𝔄) `{!PctxNoUniq K} (ty: type 𝔅)
      (ty': type 𝔅') Φ :
    ty_bsize ty' = ty_bsize ty → resolve E L ty Φ → pctx_nosum K →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K (OfTy ty); pb ◁ᵥ ty']
      (Store Na1Ord ty'.(ty_mty) (pctx_expr K (ToLit p)) pb)
      (λ _, +[p ◁ₗown{n} pctx_plug (pctx_retype K 𝔅') (OfTy ty')])
      (λ post '-[x; b], λ mask π, Φ (pctx_get K x.1.2) π →
        post -[((x.1.1, pctx_reset K x.1.2 b), x.2)] mask π).
  Proof.
    iIntros (Hsz Rslv Hns tid post mask iκs [x [b []]])
      "#LFT #TIME #PROPH #UNIQ #E L I (Tp & Tb & _) Obs".
    destruct x as [[l x₀] ζm].
    rewrite /tctx_elt_interp.
    iDestruct "Tp" as (v Hp D d g) "(#⧖ & ⧗p & -> & %Hle & Fr & Own)".
    iDestruct "Tb" as (vb Hpb wb db fvb [-> Hfvb]) "(Hcb & #⧖b & Gb)".
    have ?: Closed [] (pctx_expr K (ToLit p)).
    { apply pctx_expr_closed. have ?: Closed [] p by eapply eval_path_closed. apply _. }
    rewrite /ltype_own lty_pat_plug lty_rfn_plug ltype_own_plug.
    iDestruct "Own" as "[L1 Rest]". iSimpl in "L1".
    iDestruct "L1" as (? ->) "[Pt1 Gho1]".
    iDestruct (pctx_own_mode_le with "Rest") as %Hk.
    set k0 := pctx_mode K 0.
    set y := pctx_get K x₀.
    set lr := l.
    set lK := pctx_loc K (lty_size (OfTy ty)) x₀ lr.
    set dh := pctx_depth K d.
    have Hdh: dh ≤ d. { rewrite /dh pctx_depth_sub. lia. }
    (* The address of the hole, and the value. *)
    wp_bind (pctx_expr K (ToLit p)).
    iApply (wp_wand with "[Rest]").
    { iApply (wp_pctx_expr K (lty_size (OfTy ty)) 1 x₀ ζm [] d g tid lr (ToLit p) True True
        with "[] Rest").
      - wp_bind p. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->".
        by wp_pure _. }
    iIntros (w) "(-> & _ & _ & Rest)".
    wp_bind pb. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (?) "->".
    (* The write step gives cumulative time receipts: for credits, and to raise the
       depth of the place to the depth of the new value below [k0] owned pointers. *)
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
    (* Write. *)
    iApply (wp_bytes_own_forget with "Pt1"); [solve_ndisj|]. iIntros (bs) "Hbs %Hlen".
    iApply (wp_val_cells_store with "[$Hbs $Hcb]"); [solve_ndisj|done|by rewrite Hlen -Hsz|].
    iIntros "!> Hbs".
    (* Close the place at the new value. *)
    set d'' := (db + k0) `max` d. set g'' := db `max` g.
    have Hdh'': db ≤ pctx_depth K d''. { rewrite pctx_depth_sub. lia. }
    iDestruct (ty_gho_own_depth_mono _ db db (pctx_depth K d'') g'' with "Gb") as "[Gb _]";
      [lia..|].
    iDestruct (pctx_own_depth_mono _ _ _ _ _ _ _ _ d'' g'' with "Rest") as "Rest"; [lia..|].
    iCombine "⧖ ⧖k" as "⧖D".
    have Hsz' : lty_size (OfTy ty') = lty_size (OfTy ty).
    { by rewrite /lty_size -(ty_bsize_eq ty) -(ty_bsize_eq ty'). }
    iModIntro. iExists -[((l, pctx_reset K x₀ b), ζm)]. iFrame "L I".
    iSplitR "Obs Obs'".
    { iSplit; [|done]. rewrite /tctx_elt_interp. iExists (MLitV (VPtr l)). iSplit; [done|].
      iExists (D `max` (S k0 + db)), d'', g''. iFrame "⧖D".
      rewrite (lty_nrc_plug_retype K (OfTy ty) (OfTy ty')) //.
      rewrite (lty_size_plug_retype K (OfTy ty) (OfTy ty')); [|done|done].
      iFrame "⧗p Fr". iSplit; [done|]. iSplit; [iPureIntro; lia|].
      rewrite /ltype_own lty_pat_plug lty_rfn_plug pctx_get_reset ltype_own_plug pctx_own_reset //
        pctx_loc_reset // pctx_mode_retype pctx_depth_retype /=. rewrite Hsz'. iFrame "Rest".
      iExists b. iSplit; [done|]. rewrite /ofty_owned. by iFrame "Gb Hbs". }
    iCombine "Obs Obs'" as "Obs". iApply (proph_obs_impl with "Obs")=> π [Hπ HΦ].
    by apply Hπ.
  Qed.
End typing.
