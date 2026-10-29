(** * Shared borrows of places, and places below shared references

  ** Shared borrows of a place

  A leaf [OfTy ty] of a place rooted at an owned location ([p ◁ₗown{n} lt]) can be
  borrowed shared at a lifetime [α] (as RefinedRust's
  [type_borrow_shr]): its points-to and its ownership predicate are borrowed at [α], the
  borrow of the points-to becomes a guard and the borrow of the ownership predicate is
  shared ([ty_share], whose steps are paid with later credits of the instruction). The
  leaf becomes _shared-blocked_, [ShrBlocked ty α] ([shr_blocked_owned] in [ltype.v]):
  its value does not change, it keeps the (persistent) sharing information, so that it
  can still be read ([type_read_oplace_shr_instr]), and the inheritance of the borrow,
  which gives back the points-to and the ownership predicate once [α] has ended
  ([unblock_tctx_oplace_shr]). For places rooted at a value, below any number of unique
  borrows, see [type_share_vplace_deep_instr], [type_read_vplace_shr_deep_instr] and
  [unblock_tctx_vplace_shr_deep] ([place_puniq.v], [place_pshr.v]).

  ** Places below shared references

  The ownership of [&shr{κ} ty] is persistent, so the place type of the referent of a
  shared reference never changes: there is nothing to block or unblock, and no place
  element (nor a [Shared] borrow kind of [ltype_own]) is needed. A subplace below a
  shared reference is given by a place context [K] (whose siblings are only used for
  their folded types); [tctx_shr_place] gives a shared reference to the subplace at the
  hole of [K] (fields of nested products), from the structural sharing predicate of
  products; reads below a shared reference are reads through such a shared reference
  ([read_shr]). Owned pointers and unique borrows below a shared reference are
  traversed by the existing rules [type_deref_shr_own_instr] and
  [type_deref_shr_uniq_instr] (from their structural sharing predicates). *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From lrust.lang Require Import proofmode.
From lrust.typing Require Export type ltype lpath place_own shr_bor.
From lrust.typing Require Import type_context programs programs_util lft_contexts
  uniq_util uniq_bor product own.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section place_shr.
  Context `{!typeG Σ}.

  (** * Sharing the contents of a leaf *)

  (** The contents of a leaf (its points-to and its ownership predicate) are borrowed
      at [α] and shared; the leaf becomes shared-blocked. [ty_share] takes [d] steps,
      paid with later credits. *)
  Lemma ofty_owned_share {𝔄} m (ty: type 𝔄) α x d g tid (l: cloc) G :
    Timeless G →
    llft_ctx -∗ α ⊑ ty_lft ty -∗ (G &&{↑NllftG}&&> @[α]) -∗ G -∗ £(d + 1) -∗
    l #↦!∗ ty.(ty_phys) x tid -∗ ty.(ty_gho_own) x d g tid ={⊤}=∗
      G ∗ ty.(ty_gho_pers) x d g tid ∗
      leaf_owned_s false m ty (PatShrBlocked α) (inl (PlaceIn x)) d g tid l.
  Proof.
    iIntros (?) "#LFT #Incl #Gα G [£d £1] Pt Gho".
    iDestruct (ty_gho_pers_impl with "Gho") as "#Pers".
    iMod (llftl_borrow _ α (l #↦!∗ ty.(ty_phys) x tid ∗ ty.(ty_gho_own) x d g tid)
      with "LFT [Pt Gho]") as "[Bor Inh]"; [solve_ndisj|by iFrame|].
    iMod (llftl_sep_split with "LFT Bor") as "[BorPt BorGho]"; [solve_ndisj|].
    iMod (llftl_bor_guard with "LFT BorPt") as "#GPt"; [solve_ndisj|].
    iMod (ty_share with "LFT Incl Pers Gα G BorGho") as "Upd"; [done..|].
    iMod (lc_step_fupdN_elim_later with "£d Upd") as ">[$ #Shr]".
    iModIntro. iSplitR; [done|]. rewrite /= /shr_blocked_owned. iExists x.
    iSplitR; [done|]. iSplitR; [iApply (lguards_weaken_later with "GPt"); lia|].
    iFrame "Shr Pers". iIntros "#†α".
    iMod (fupd_mask_mono with "(Inh †α)") as "Pl"; [rewrite /lazyE; solve_ndisj|].
    iMod (lc_fupd_elim_later with "£1 Pl") as "[$ Gho]". iModIntro. by iNext.
  Qed.

  Lemma pat_ok_shr_blocked κ α : α ⊑ κ -∗ pat_ok κ (PatShrBlocked α).
  Proof. rewrite /pat_ok /=. iIntros "$". Qed.

  (** The sharing predicate of [&shr{α} ty] at depth [S d'], from the guard of the
      points-to and the sharing and persistent predicates of [ty] at [d' g'], with
      [d' ≤ d'' ≤ D] and [g' ≤ D]. *)
  Lemma shr_bor_own_intro {𝔄} α (ty: type 𝔄) (l: cloc) x d g D tid :
    d ≤ D → g ≤ S D →
    (@[α] &&{↑NllftG; S D + 1}&&> l.1 ↦[^ l.2]!∗ ty.(ty_phys) x tid) -∗
    ty.(ty_shr) α x d g tid -∗ ty.(ty_gho_pers) x d g tid -∗
    (&shr{α} ty).(ty_gho_own) (l, x) (S D) (S D) tid.
  Proof.
    iIntros (??) "#Pt #Shr #Pers". rewrite /= /by_succ. iFrame "Pt". iSplit.
    - iApply (ty_shr_depth_mono with "Shr"); lia.
    - iNext. iApply (ty_gho_pers_depth_mono with "Pers"); lia.
  Qed.
End place_shr.

Section typing.
  Context `{!typeG Σ}.

  (** * Shared borrow of a leaf of a place rooted at a unique borrow *)

  (** * Reading a shared-blocked leaf of a place rooted at a unique borrow *)

  (** * Unblocking a shared-blocked leaf of a place rooted at a unique borrow *)

  (** * Shared borrow of a leaf of a place rooted at an owned location *)

  (** A shared borrow of the leaf at the hole of [K], at a lifetime [α] that the type of
      the leaf outlives. The leaf is shared-blocked until [α] ends; the value of the
      place does not change. *)
  Lemma type_share_oplace_instr {𝔅 𝔄} E L I p n α (K: pctx 𝔅 𝔄) `{!PctxNoUniq K} (ty: type 𝔅) :
    elctx_sat E L (ty_outlives_E ty α) → lctx_lft_alive E L α →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K (OfTy ty)] (Share;; pctx_expr K p)
      (λ w, +[w ◁ &shr{α} ty; p ◁ₗown{n} pctx_plug K (ShrBlocked ty α)])
      (λ post '-[x], post -[(pctx_loc K (ty_size ty) x.1.2
          (x.1.1, repeat [] (lty_size (pctx_plug K (OfTy ty)))), pctx_get K x.1.2); x]).
  Proof.
    intros Out Alv tid post mask iκs [x []].
    iIntros "#LFT #TIME #PROPH #UNIQ #E L I [T _] Obs".
    destruct x as [[l x₀] ζm].
    rewrite /tctx_elt_interp.
    iDestruct "T" as (v Hp D d g) "(#⧖ & ⧗p & -> & %Hle & Fr & Own)".
    have ?: Closed [] (pctx_expr K p).
    { apply pctx_expr_closed. by eapply eval_path_closed. }
    iDestruct (Out with "L E") as "#Out".
    iDestruct (elctx_interp_ty_outlives_E with "Out") as "#Incl".
    iDestruct (Alv with "L E") as "#Alv".
    (* A step, for credits. *)
    wp_bind (Seq Skip Skip). wp_bind Skip. iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [set_solver|].
    iIntros "£ #⧖S". wp_let. iModIntro. wp_let. wp_let. wp_let.
    rewrite /ltype_own lty_pat_plug lty_rfn_plug ltype_own_plug.
    iDestruct "Own" as "[L1 Rest]". iSimpl in "L1".
    iDestruct "L1" as (? ->) "[Pt1 Gho1]".
    iDestruct (pctx_own_mode_le with "Rest") as %Hk.
    set k0 := pctx_mode K 0.
    set y := pctx_get K x₀.
    set lr := (l, repeat [] (lty_size (pctx_plug K (OfTy ty)))).
    set lK := pctx_loc K (ty_size ty) x₀ lr.
    set dh := pctx_depth K d.
    have Hdh: dh ≤ d. { rewrite /dh pctx_depth_sub. lia. }
    iDestruct (lc_weaken (pctx_mode K 1 + (dh + 1)) with "£") as "[£k £s]";
      [rewrite /advance_credits pctx_mode_add; nia|].
    (* The address of the hole. *)
    iMod lc_zero as "£0".
    iApply wp_fupd.
    iApply (wp_wand with "[Rest £0]").
    { iApply (wp_pctx_expr K (ty_size ty) 1 x₀ ζm [] d g tid lr p True True 0
        with "[] £0 [] Rest").
      - rewrite /lr -heap_cloc_mapsto_empty. iApply guards_true.
      - iApply wp_wand; [by iApply wp_eval_path|]. by iIntros (?) "->". }
    iIntros (w) "(-> & _ & _ & Rest)".
    iMod (lc_fupd_elim_laterN with "£k Gho1") as "Gho1".
    (* Share the contents of the leaf. *)
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iDestruct (guards_transitive with "Ghalf Alv") as "#Hα".
    iMod (ofty_owned_share (pctx_mode K 1) with "LFT Incl Hα H1 £s Pt1 Gho1")
      as "(H1 & #Pers & Leaf)".
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iAssert ((@[α] &&{↑NllftG; g+1}&&> lK #↦!∗ ty.(ty_phys) y tid) ∗
      ty.(ty_shr) α y dh g tid)%I as "#[GPt Shr]".
    { by iDestruct "Leaf" as (? ->) "(#$ & #$ & _)". }
    iModIntro. iExists -[(lK, y); ((l, x₀), ζm)].
    iFrame "L I". iSplit; last first.
    { iApply (proph_obs_impl with "Obs")=> π Hπ. exact Hπ. }
    iSplitR.
    { iExists _, D. iSplit; [by rewrite eval_path_of_val|]. iFrame "⧖". iSplit; [|done].
      destruct D as [|D']; [lia|].
      iApply (shr_bor_own_intro with "[] Shr Pers"); [lia|lia|].
      iApply guard_cloc_combine_fancy.
      - iApply (oplace_loc_guard K (OfTy ty)).
      - iApply (lguards_weaken_later with "GPt"). lia. }
    iSplit; [|done]. rewrite /tctx_elt_interp. iExists #l. iSplit; [done|].
    iExists D, d, g. iFrame "⧖".
    rewrite (lty_size_plug_eq K (ShrBlocked ty α) (OfTy ty)) //
      (lty_nrc_plug_shr_nouniq K ty α).
    iFrame "⧗p Fr". iSplit; [done|]. iSplit; [done|].
    rewrite /ltype_own lty_pat_plug lty_rfn_plug ltype_own_plug /=. iFrame "Rest Leaf".
  Qed.

  (** * Reading a shared-blocked leaf of a place rooted at an owned location *)

  Lemma type_read_oplace_shr_instr {𝔅 𝔄} E L I p n α (K: pctx 𝔅 𝔄) `{!PctxNoUniq K} (ty: type 𝔅) :
    lctx_lft_alive E L α → ty_size ty = 1%nat → Copy ty →
    typed_instr E L I +[p ◁ₗown{n} pctx_plug K (ShrBlocked ty α)] (!(pctx_expr K p))
      (λ v, +[v ◁ ty; p ◁ₗown{n} pctx_plug K (ShrBlocked ty α)])
      (λ post '-[x], post -[pctx_get K x.1.2; x]).
  Proof.
    iIntros (Alv Hsz Hcopy tid post mask iκs [x []]) "#LFT #TIME #PROPH #UNIQ #E L I (Tp & _) Obs".
    destruct x as [[l x₀] ζm].
    rewrite /tctx_elt_interp.
    iDestruct "Tp" as (v Hp D d g) "(#⧖ & ⧗p & -> & %Hle & Fr & Own)".
    have ?: Closed [] (pctx_expr K p).
    { apply pctx_expr_closed. by eapply eval_path_closed. }
    rewrite /ltype_own lty_pat_plug lty_rfn_plug ltype_own_plug.
    iDestruct "Own" as "[L1 Rest]". iSimpl in "L1".
    iDestruct "L1" as (? ->) "(#GPt & #Shr & #PersL & Inh)".
    iDestruct (pctx_own_mode_le with "Rest") as %Hk.
    set y := pctx_get K x₀.
    set lr := (l, repeat [] (lty_size (pctx_plug K (ShrBlocked ty α)))).
    set lK := pctx_loc K (ty_size ty) x₀ lr.
    set dh := pctx_depth K d.
    have Hdh: dh ≤ d. { rewrite /dh pctx_depth_sub. lia. }
    (* The address of the hole. *)
    iMod lc_zero as "£0".
    wp_bind (pctx_expr K p).
    iApply (wp_wand with "[Rest £0]").
    { iApply (wp_pctx_expr K (ty_size ty) 1 x₀ ζm [] d g tid lr p True True 0
        with "[] £0 [] Rest").
      - rewrite /lr -heap_cloc_mapsto_empty. iApply guards_true.
      - iApply wp_wand; [by iApply wp_eval_path|]. by iIntros (?) "->". }
    iIntros (w) "(-> & _ & _ & Rest)".
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [solve_ndisj|].
    iIntros "£ #⧖S". iApply wp_fupd.
    iDestruct (Alv with "L E") as "#Alv".
    iMod (llctx_interp_make_guarded with "L") as (γh) "[H1 [H2 [#Ghalf #Halfback]]]";
      [solve_ndisj|].
    iDestruct (guards_transitive with "Ghalf Alv") as "#Hα".
    iDestruct (lc_weaken ((g + 1) + 3 * (g + 1))%nat with "£") as "[£g £r]";
      [rewrite /advance_credits; nia|].
    (* The (persistent) ownership predicate of the value, from the sharing predicate. *)
    iDestruct (copy_shr with "Shr") as "#GGho".
    iDestruct (guards_transitive_right with "Hα GGho") as "#GGho'".
    iAssert (|={⊤ ∖ ↑advN}=> ty.(ty_gho_own) y dh g tid ∗ fractional.half γh)%I
      with "[H1 £g]" as ">[#Gho1 H1]".
    { leaf_open_laters "GGho'" with "H1" as "Gho1"; [solve_ndisj|].
      iMod (lc_fupd_add_laterN with "£g Gho1") as "[#Gho1 Hclose]".
      iMod ("Hclose" with "Gho1") as "$". by iModIntro. }
    iDestruct (copy_concrete with "Gho1") as %Hconc.
    have Hlen: length (ty_phys ty y tid) = 1%nat by rewrite ty_size_eq.
    destruct (ty_phys ty y tid) as [|fv [|]] eqn:Hphys; [done| |done].
    destruct fv as [w|]; [|by destruct Hconc].
    iApply (wp_read_na_guarded_cells_singleton _ lK.1 lK.2 (fractional.half γh) w (g + 1)
      with "[H1 £r]"); [solve_ndisj| |].
    { iFrame "H1 £r". iApply guard_cloc_combine_fancy.
      - iApply (oplace_loc_guard K (ShrBlocked ty α)).
      - iApply (guards_transitive_right with "Hα GPt"). }
    iIntros "!> H1".
    iMod (fupd_mask_mono with "(Halfback H1 H2)") as "L"; [solve_ndisj|].
    iModIntro. iExists -[y; ((l, x₀), ζm)]. iFrame "L I Obs".
    iSplitR "Inh Rest ⧗p Fr".
    { iExists w, D. iSplit; [by rewrite eval_path_of_val|]. iFrame "⧖".
      iSplit; [|done].
      iDestruct (ty_gho_own_depth_mono _ dh g D D with "Gho1") as "[$ _]"; lia. }
    iSplit; [|done]. iExists #l. iSplit; [done|]. iExists D, d, g. iFrame "⧖ ⧗p Fr".
    iSplit; [done|]. iSplit; [done|].
    rewrite /ltype_own lty_pat_plug lty_rfn_plug ltype_own_plug. iFrame "Rest".
    iExists y. rewrite Hphys. by iFrame "GPt Shr PersL Inh".
  Qed.

  (** * Unblocking a shared-blocked leaf of a place rooted at an owned location *)

  Lemma unblock_tctx_oplace_shr {𝔅 𝔄 𝔄l 𝔄l'} p n α (K: pctx 𝔅 𝔄) `{!PctxNoUniq K} (ty: type 𝔅)
      (T: tctx 𝔄l) (T': tctx 𝔄l') E L f :
    unblock_tctx E L α T T' f →
    unblock_tctx E L α (p ◁ₗown{n} pctx_plug K (ShrBlocked ty α) +:: T)
      (p ◁ₗown{n} pctx_plug K (OfTy ty) +:: T')
      (λ π '(x -:: xl), λ '(x' -:: xl'), x' = x ∧ f π xl xl').
  Proof.
    iIntros (Un G tid [x xl] ?) "#LFT #TIME #PROPH #UNIQ #E #L G #†α /=[(%v & %Hp & Own) T]".
    destruct x as [[l x₀] ζm].
    iDestruct "Own" as (D d g) "(#⧖0 & ⧗ & -> & %Hle & Fr & Own)".
    iMod (Un with "LFT TIME PROPH UNIQ E L G †α T") as (dT xl') "[#⧖T ToT']".
    rewrite /ltype_own lty_pat_plug lty_rfn_plug ltype_own_plug.
    iDestruct "Own" as "[L1 Rest]".
    iDestruct (unblock_shr_blocked_owned (pctx_mode K 1) ty α with "†α L1") as "L1".
    iMod (fupd_mask_mono with "L1") as "L1"; [rewrite /lazyE; solve_ndisj|].
    iModIntro. iExists dT, (((l, x₀), ζm) -:: xl'). iSplitR; [done|].
    iApply (step_fupd_wand with "ToT'"). iIntros "ToT'".
    iApply (step_fupdN_wand with "ToT'"). iIntros ">(G & T' & #Obs')".
    iModIntro. iFrame "G T'". iSplitR "Obs'".
    { rewrite /tctx_elt_interp. iExists #l. iSplit; [done|]. iExists D, d, g.
      iFrame "⧖0". rewrite (lty_size_plug_eq K (OfTy ty) (ShrBlocked ty α)) //
        -(lty_nrc_plug_shr_nouniq K ty α).
      iFrame "⧗ Fr". iSplit; [done|]. iSplit; [done|].
      rewrite /ltype_own lty_pat_plug lty_rfn_plug ltype_own_plug /=. iFrame "Rest L1". }
    iApply (proph_obs_impl with "Obs'")=> π Hf. by split.
  Qed.
End typing.

Section shr_place.
  Context `{!typeG Σ}.

  (** * Places below a shared reference *)

  (** The sharing information of a (folded) place gives the sharing information of the
      subplace at the hole of [K] (fields of nested products), at the location of the
      hole. *)
  Lemma shr_pctx_split {𝔅 𝔄} κ (K: pctx 𝔅 𝔄) (lt: lty 𝔅) x (l: cloc) d g k j tid :
    pctx_fields K →
    (@[κ] &&{↑NllftG; k}&&> l.1 ↦[^ l.2]!∗ ty_phys (lty_fold (pctx_plug K lt)) x tid) -∗
    ty_shr (lty_fold (pctx_plug K lt)) κ x d g tid -∗
    ▷^j ty_gho_pers (lty_fold (pctx_plug K lt)) x d g tid -∗
    let l' := pctx_loc K (lty_size lt) x l in
    (@[κ] &&{↑NllftG; k}&&> l'.1 ↦[^ l'.2]!∗ ty_phys (lty_fold lt) (pctx_get K x) tid) ∗
    ty_shr (lty_fold lt) κ (pctx_get K x) d g tid ∗
    ▷^j ty_gho_pers (lty_fold lt) (pctx_get K x) d g tid.
  Proof.
    induction K as [|𝔅 𝔄1 𝔄2 K IH lt2|𝔅 𝔄1 𝔄2 lt1 K IH| | | |] in lt, x, l |- *; intros HK; simpl.
    - iIntros "$ $ $".
    - iIntros "#Pt [Shr _] Pers". rewrite heap_mapsto_cells_fancy_vec_app.
      iApply (IH with "[] Shr [Pers]"); [done| |by iDestruct "Pers" as "[$ _]"].
      rewrite ty_size_eq -lty_size_fold lty_size_plug.
      by iApply (guards_weaken_rhs_sep_l with "Pt").
    - iIntros "#Pt [_ Shr] Pers". rewrite heap_mapsto_cells_fancy_vec_app.
      iApply (IH with "[] Shr [Pers]"); [done| |by iDestruct "Pers" as "[_ $]"].
      rewrite ty_size_eq -lty_size_fold.
      by iApply (guards_weaken_rhs_sep_r with "Pt").
    - done.
    - done.
    - done.
    - done.
  Qed.

  (** A shared reference to the subplace at the hole of [K] (fields of nested products),
      from a shared reference to the place (which is kept, shared references being
      copyable): [&( *p).f₁…fₙ]. *)
  Lemma tctx_shr_place {𝔅 𝔄} E L p κ (K: pctx 𝔅 𝔄) (ty: type 𝔅) :
    pctx_fields K →
    tctx_incl E L +[p ◁ &shr{κ} (lty_fold (pctx_plug K (OfTy ty)))]
      +[p +ₗ #(pctx_off K) ◁ &shr{κ} ty; p ◁ &shr{κ} (lty_fold (pctx_plug K (OfTy ty)))]
      (λ post '-[x], post -[(pctx_loc K (ty_size ty) x.2 x.1, pctx_get K x.2); x]).
  Proof.
    intros HK. split; [by intros ??? [? []]|].
    iIntros (G tid [[l x] []] mask post ?) "_ _ _ _ _ $ [T _] Obs".
    iDestruct "T" as (v d Hp) "(#⧖ & [#Gho %Phys])".
    destruct d as [|d']; [done|]. iDestruct "Gho" as "(#Pt & #Shr & #Pers)".
    iDestruct (shr_pctx_split with "Pt Shr Pers") as "(Pt' & Shr' & Pers')"; [done|].
    iModIntro. iExists -[(pctx_loc K (ty_size ty) x l, pctx_get K x); (l, x)]. iFrame "Obs".
    iSplit; [|iSplit; [|done]].
    - iExists #((pctx_loc K (ty_size ty) x l).1), (S d'). iFrame "⧖". iSplit.
      { iPureIntro. inversion Phys; subst. rewrite /= Hp pctx_loc_fst //.
        clear -HK. induction K; naive_solver. }
      iSplit; [|done]. iFrame "Pt' Shr' Pers'".
    - iExists v, (S d'). iFrame "⧖ Pt Shr Pers". by iSplit.
  Qed.
End shr_place.
