(** * Places rooted at a value

  A place element [p ◁ₗ lt] says that the value of the path [p] (a value of size 1, not in
  memory) has the place type [lt]. Its value is a pair of the value [x] of the root and a
  blocking map [ζm] (as for the other place elements); its refinement is [lty_vrfn lt x ζm],
  computed from the paths below the root pointer ([lpath.v]).

  It is interpreted as [∃ D, ⧖D ∗ ⧗(lty_vnrc lt) ∗ vroot_own lt (lty_vrfn lt x ζm) D tid v]:
  the receipts of the blocked leaves ([lty_nrc], the root pointer not counting as a level),
  and the root ([vroot_own], [pctx_acc.v]): the [nval] of the root pointer ([lty_vown],
  [ltype.v]: the node of the pointer without its cell) at depths below [D], or a leaf at the
  value. For a root owned pointer, the element is literally the place rooted at the owned
  location [p] ([oplace_own]): [p ◁ₗown{n} lt'] is a notation for [p ◁ₗ OwnPtrLty n lt'].

  Conversions:
  - [tctx_ty_to_vplace], [tctx_vplace_to_ty]: [p ◁ ty] and [p ◁ₗ OfTy ty];
  - [tctx_vplace_unfold_own], [tctx_vplace_fold_own]: [OfTy (own_ptr n ty)] and
    [OwnPtrLty n (OfTy ty)] (so [p ◁ own_ptr n ty] and [p ◁ₗown{n} OfTy ty]);
  - [tctx_vplace_unfold_shr], [tctx_vplace_fold_shr]: [OfTy (&shr{κ} ty)] and
    [ShrLty (OfTy ty) κ];
  - [type_vplace_unfold_uniq_instr] (one [Skip], for the two cumulative time receipts of the
    node of [UniqLty]), [tctx_vplace_fold_uniq]: [OfTy (&uniq{κ} ty)] and
    [UniqLty (OfTy ty) κ]; [type_uniq_to_vplace_instr], [tctx_vplace_to_uniq]: from and to
    [p ◁ &uniq{κ} ty] directly. *)

From iris.proofmode Require Import proofmode.
From lrust.lang Require Import proofmode.
From lrust.typing Require Export type ltype lpath pctx_acc.
From lrust.typing Require Import type_context programs programs_util lft_contexts
  uniq_util uniq_bor product own shr_bor freeable_util.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

(** The value of a place element rooted at a value. *)
Notation vplaceₛ 𝔄 := (𝔄 * blk_mapₛ)%ST.
(** The value of a place element rooted at an owned location. *)
Notation oplaceₛ 𝔄 := (vplaceₛ (at_locₛ 𝔄)).

Section vplace.
  Context `{!typeG Σ}.

  (** A place rooted at an owned location: the pointee of the owned pointer [p], in
      [Owned 1] mode (see [place_own.v]). *)
  Definition oplace_own {𝔄} (n: nat) (lt: lty 𝔄) (x: ~~ (oplaceₛ 𝔄))
      (tid: thread_id) (v: val) : iProp Σ :=
    match x with ((l, x₀), ζm) =>
      ∃ D d g, ⧖D ∗ ⧗(lty_nrc lt 0 0) ∗ ⌜v = #l⌝ ∗ ⌜S d ≤ D ∧ g ≤ D⌝ ∗
        freeable_sz n (lty_size lt) l ∗
        ltype_own (Owned 1) lt (lty_rfn lt x₀ ζm []) d g tid (l, repeat [] (lty_size lt))
    end%I.

  Definition vplace_own {𝔄} (lt: lty 𝔄) : ~~ (vplaceₛ 𝔄) → thread_id → val → iProp Σ :=
    match lt in lty 𝔄 return ~~ (vplaceₛ 𝔄) → thread_id → val → iProp Σ with
    | OwnPtrLty n lt' => oplace_own n lt'
    | lt' => λ x tid v, (∃ D, ⧖D ∗ ⧗(lty_vnrc lt') ∗ vroot_own lt' (lty_vrfn lt' x.1 x.2) D tid v)%I
    end.

  Lemma vplace_own_eq {𝔄} (lt: lty 𝔄) x tid v :
    vplace_own lt x tid v ⊣⊢ ∃ D, ⧖D ∗ ⧗(lty_vnrc lt) ∗ vroot_own lt (lty_vrfn lt x.1 x.2) D tid v.
  Proof.
    destruct lt; try done. destruct x as [[l x₀] ζm]. simpl. iSplit.
    - iIntros "(%D & %d & %g & ⧖ & ⧗ & -> & %Hle & Fr & Own)". iExists D. iFrame "⧖ ⧗".
      iExists d, g. by iFrame.
    - iIntros "(%D & ⧖ & ⧗ & %d & %g & -> & %Hle & Fr & Own)". iExists D, d, g. by iFrame.
  Qed.

  (** The current value of a place. *)
  Definition vplace_cur {𝔄} (lt: lty 𝔄) (x: ~~ (vplaceₛ 𝔄)) : proph 𝔄 :=
    prfn_den (lty_vrfn lt x.1 x.2).

  (** The final value of the borrow of the blocked leaf at the hole of [K]. *)
  Definition vplace_blk_fin {𝔅 𝔄} (K: pctx 𝔅 𝔄) (x: ~~ (vplaceₛ 𝔄)) : proph 𝔅 := λ π,
    (π (uniq_prvar (pctx_get K x.1) (blk_lookup x.2 (pctx_vpath K)))).1.

  (** For a place rooted at an owned location. *)
  Definition oplace_cur {𝔄} (lt: lty 𝔄) (x: ~~ (oplaceₛ 𝔄)) : proph 𝔄 :=
    prfn_den (lty_rfn lt x.1.2 x.2 []).

  Definition oplace_blk_fin {𝔅 𝔄} (K: pctx 𝔅 𝔄) (x: ~~ (oplaceₛ 𝔄)) : proph 𝔅 := λ π,
    (π (uniq_prvar (pctx_get K x.1.2) (blk_lookup x.2 (pctx_path K [])))).1.

  Lemma vplace_own_receipt {𝔄} (lt: lty 𝔄) x tid v : vplace_own lt x tid v -∗ ∃ D, ⧖D.
  Proof. rewrite vplace_own_eq. iIntros "(%D & ⧖ & _)". by iExists D. Qed.

  (** A place [p ◁ₗ pctx_plug K lt] whose root is the first step of [K]. *)
  Lemma vplace_own_open {𝔅 𝔄} (K: pctx 𝔅 𝔄) `{!PctxVRoot K} (lt: lty 𝔅) x ζm tid v :
    vplace_own (pctx_plug K lt) (x, ζm) tid v ⊣⊢ ∃ D, ⧖D ∗ ⧗(lty_vnrc (pctx_plug K lt)) ∗
      vroot_own (pctx_plug K lt) (pctx_vrfn K x ζm (lty_rfn lt (pctx_get K x) ζm (pctx_vpath K)))
        D tid v.
  Proof. by rewrite vplace_own_eq /= lty_vrfn_plug. Qed.

  Lemma vplace_own_close {𝔅 𝔄} (K: pctx 𝔅 𝔄) `{!PctxVRoot K} (lt: lty 𝔅) x ζm D tid v :
    ⧖D -∗ ⧗(lty_vnrc (pctx_plug K lt)) -∗
    vroot_own (pctx_plug K lt) (pctx_vrfn K x ζm (lty_rfn lt (pctx_get K x) ζm (pctx_vpath K)))
      D tid v -∗
    vplace_own (pctx_plug K lt) (x, ζm) tid v.
  Proof. rewrite vplace_own_open. iIntros "⧖ ⧗ R". iExists D. iFrame. Qed.
End vplace.

Notation "p ◁ₗ lt" := (TCtx_sem _ p (vplace_own lt))
  (at level 55, format "p  ◁ₗ  lt").
Notation "p ◁ₗown{ n } lt" := (TCtx_sem _ p (vplace_own (OwnPtrLty n lt)))
  (at level 55, format "p  ◁ₗown{ n }  lt").

Section conv.
  Context `{!typeG Σ}.

  (** * Leaves *)

  Lemma tctx_ty_to_vplace {𝔄} E L p (ty: type 𝔄) :
    tctx_incl E L +[p ◁ ty] +[p ◁ₗ OfTy ty] (λ post '-[a], post -[(a, [])]).
  Proof.
    split; [by intros ??? [? []]|].
    iIntros (G tid [x []] mask post ?) "_ _ _ _ _ $ [T _] Obs".
    iDestruct "T" as (v d Hp) "(⧖ & Gho & %Phys)".
    iMod cumulative_time_receipt_0 as "⧗".
    iModIntro. iExists -[(x, [])]. iFrame "Obs". iSplit; [|done].
    rewrite /tctx_elt_interp. iExists v. iSplit; [done|].
    iExists d. iFrame "⧖ ⧗". iExists d, d. iSplit; [done|]. iExists x. by iFrame.
  Qed.

  Lemma tctx_vplace_to_ty {𝔄} E L p (ty: type 𝔄) :
    tctx_incl E L +[p ◁ₗ OfTy ty] +[p ◁ ty] (λ post '-[x], post -[x.1]).
  Proof.
    split; [by intros ??? [? []]|].
    iIntros (G tid [[x ζm] []] mask post ?) "_ _ _ _ _ $ [T _] Obs".
    iDestruct "T" as (v Hp D) "(⧖ & _ & %d & %g & %Hle & %y & -> & %Phys & Gho)".
    iModIntro. iExists -[x]. iFrame "Obs". iSplit; [|done].
    iExists v, D. iSplit; [done|]. iFrame "⧖". iSplit; [|done].
    iDestruct (ty_gho_own_depth_mono _ d g D D with "Gho") as "[$ _]"; lia.
  Qed.

  (** * Owned pointers *)

  Lemma tctx_vplace_unfold_own {𝔄} E L p n (ty: type 𝔄) :
    tctx_incl E L +[p ◁ₗ OfTy (own_ptr n ty)] +[p ◁ₗown{n} OfTy ty] (λ post '-[x], post -[x]).
  Proof.
    split; [by intros ??? [? []]|].
    iIntros (G tid [[[l x] ζm] []] mask post ?) "_ _ _ _ _ $ [T _] Obs".
    iDestruct "T" as (v Hp D) "(⧖ & ⧗ & %d & %g & %Hle & %y & -> & %Phys & Gho)".
    destruct d as [|d]; [done|]. iDestruct "Gho" as "(Pt & Fr & Gho)".
    iModIntro. iExists -[((l, x), ζm)]. iFrame "Obs". iSplit; [|done].
    rewrite /tctx_elt_interp. iExists v. iSplit; [done|].
    iExists D, d, g. iFrame "⧖ ⧗ Fr". iSplit; [by inversion Phys|].
    iSplit; [iPureIntro; lia|].
    rewrite /ltype_own /= /ofty_owned. iExists x. iSplit; [done|].
    iDestruct (ty_gho_own_depth_mono _ d g d g with "Gho") as "[$ _]"; [lia..|].
    by rewrite -(ty_size_eq ty x tid) -heap_cloc_mapsto_fancy_empty.
  Qed.

  Lemma tctx_vplace_fold_own {𝔄} E L p n (ty: type 𝔄) :
    tctx_incl E L +[p ◁ₗown{n} OfTy ty] +[p ◁ₗ OfTy (own_ptr n ty)] (λ post '-[x], post -[x]).
  Proof.
    split; [by intros ??? [? []]|].
    iIntros (G tid [[[l x] ζm] []] mask post ?) "_ _ _ _ _ $ [T _] Obs".
    iDestruct "T" as (v Hp D d g) "(⧖ & _ & -> & %Hle & Fr & Own)".
    rewrite /ltype_own /= /ofty_owned. iDestruct "Own" as (? ->) "[Pt Gho]".
    iMod cumulative_time_receipt_0 as "⧗".
    iModIntro. iExists -[((l, x), ζm)]. iFrame "Obs". iSplit; [|done].
    rewrite /tctx_elt_interp. iExists #l. iSplit; [done|].
    iExists D. iFrame "⧖ ⧗". iExists (S d), g. iSplit; [iPureIntro; lia|].
    iExists (l, x). iSplit; [done|]. iSplit; [done|]. iFrame "Fr".
    rewrite heap_cloc_mapsto_fancy_empty ty_size_eq. iFrame.
  Qed.

  (** * Shared references *)

  Lemma tctx_vplace_unfold_shr {𝔄} E L p κ (ty: type 𝔄) :
    tctx_incl E L +[p ◁ₗ OfTy (&shr{κ} ty)] +[p ◁ₗ ShrLty (OfTy ty) κ] (λ post '-[x], post -[x]).
  Proof.
    split; [by intros ??? [? []]|].
    iIntros (G tid [[x ζm] []] mask post ?) "_ _ _ _ _ $ [T _] Obs".
    iDestruct "T" as (v Hp D) "(⧖ & ⧗ & %d & %g & %Hle & Leaf)".
    iModIntro. iExists -[(x, ζm)]. iFrame "Obs". iSplit; [|done].
    iExists v. iSplit; [done|]. iExists D. iFrame "⧖ ⧗". iExists d, g. by iFrame.
  Qed.

  Lemma tctx_vplace_fold_shr {𝔄} E L p κ (ty: type 𝔄) :
    tctx_incl E L +[p ◁ₗ ShrLty (OfTy ty) κ] +[p ◁ₗ OfTy (&shr{κ} ty)] (λ post '-[x], post -[x]).
  Proof.
    split; [by intros ??? [? []]|].
    iIntros (G tid [[x ζm] []] mask post ?) "_ _ _ _ _ $ [T _] Obs".
    iDestruct "T" as (v Hp D) "(⧖ & ⧗ & %d & %g & %Hle & Leaf & _)".
    iModIntro. iExists -[(x, ζm)]. iFrame "Obs". iSplit; [|done].
    iExists v. iSplit; [done|]. iExists D. iFrame "⧖ ⧗". iExists d, g. by iFrame.
  Qed.

  (** * Unique borrows

      The node of [UniqLty] holds two cumulative time receipts (as in [uniq_node]), so
      unfolding a [&uniq] value takes a program step. *)

  Lemma type_vplace_unfold_uniq_instr {𝔄} E L I p κ (ty: type 𝔄) :
    typed_instr E L I +[p ◁ₗ OfTy (&uniq{κ} ty)] Skip
      (λ _, +[p ◁ₗ UniqLty (OfTy ty) κ]) (λ post '-[x], post -[x]).
  Proof.
    iIntros (tid post mask iκs [[m ζm] []]) "#LFT #TIME #PROPH #UNIQ #E L I [T _] Obs".
    iDestruct "T" as (v Hp D) "(#⧖ & _ & %d & %g & %Hle & %y & -> & %Phys & Gho)".
    destruct m as [[[[[l' x] ξi] d'] g'] idx].
    iMod cumulative_time_receipt_0 as "⧗0".
    iApply (wp_cumulative_time_receipt_linear with "TIME ⧖"); [solve_ndisj|].
    iIntros "⧗". wp_seq.
    iDestruct "Gho" as "(#Incl & %Hle' & Body & #Gpt)".
    iExists -[((l', x, ξi, d', g', idx), ζm)]. iFrame "L I Obs". iSplit; [|done].
    iExists v. iSplit; [done|]. iExists D. iFrame "⧖ ⧗0". iExists d, g. iSplit; [done|].
    iSplit; [by inversion Phys|]. iSplitL "⧗".
    { iApply (cumulative_time_receipt_mono with "⧗"). lia. }
    iFrame "TIME Incl Gpt". iExists d', g'. iSplit; [done|]. iExists x, idx. by iFrame.
  Qed.

  Lemma tctx_vplace_fold_uniq {𝔄} E L p κ (ty: type 𝔄) :
    tctx_incl E L +[p ◁ₗ UniqLty (OfTy ty) κ] +[p ◁ₗ OfTy (&uniq{κ} ty)]
      (λ post '-[x], λ mask π, ∀ d g idx, post -[(uniq_bor_set_meta x.1 d g idx, x.2)] mask π).
  Proof.
    split.
    { intros ?? Eq [[m ζm] []] ??. do 3 apply forall_proper=> ?. apply Eq. }
    iIntros (G tid [[m ζm] []] mask post ?) "_ _ _ _ _ $ [T _] Obs".
    destruct m as [[[[[l' x] ξi] d0] g0] idx0].
    iDestruct "T" as (v Hp D) "(⧖ & _ & %d & %g & %Hle & -> & _ & _ & #Incl & #Gpt & H)".
    iDestruct "H" as (d' g' Hle') "(%y & %idx & -> & Body)".
    iMod cumulative_time_receipt_0 as "⧗0".
    iModIntro. iExists -[((l', x, ξi, d', g', idx), ζm)].
    iSplitR "Obs"; [|iApply (proph_obs_impl with "Obs")=> π Hπ; apply (Hπ d' g' idx)].
    iSplit; [|done]. iExists _. iSplit; [done|]. iExists D. iFrame "⧖ ⧗0".
    iExists d, g. iSplit; [done|]. iExists _. iSplit; [done|]. iSplit; [done|].
    by iFrame "Incl Gpt Body".
  Qed.

  (** Directly from and to a [&uniq] value. *)
  Lemma type_uniq_to_vplace_instr {𝔄} E L I p κ (ty: type 𝔄) :
    typed_instr E L I +[p ◁ &uniq{κ} ty] Skip
      (λ _, +[p ◁ₗ UniqLty (OfTy ty) κ]) (λ post '-[m], post -[(m, [])]).
  Proof.
    iIntros (tid post mask iκs [m []]) "#LFT #TIME #PROPH #UNIQ #E L I [T _] Obs".
    iDestruct "T" as (v D Hp) "(#⧖ & Gho & %Phys)".
    destruct m as [[[[[l' x] ξi] d'] g'] idx].
    iMod cumulative_time_receipt_0 as "⧗0".
    iApply (wp_cumulative_time_receipt_linear with "TIME ⧖"); [solve_ndisj|].
    iIntros "⧗". wp_seq.
    iDestruct "Gho" as "(#Incl & %Hle' & Body & #Gpt)".
    iExists -[((l', x, ξi, d', g', idx), [])]. iFrame "L I Obs". iSplit; [|done].
    iExists v. iSplit; [done|]. iExists D. iFrame "⧖ ⧗0". iExists D, D. iSplit; [done|].
    iSplit; [by inversion Phys|]. iSplitL "⧗".
    { iApply (cumulative_time_receipt_mono with "⧗"). lia. }
    iFrame "TIME Incl Gpt". iExists d', g'. iSplit; [done|]. iExists x, idx. by iFrame.
  Qed.

  Lemma tctx_vplace_to_uniq {𝔄} E L p κ (ty: type 𝔄) :
    tctx_incl E L +[p ◁ₗ UniqLty (OfTy ty) κ] +[p ◁ &uniq{κ} ty]
      (λ post '-[x], λ mask π, ∀ d g idx, post -[uniq_bor_set_meta x.1 d g idx] mask π).
  Proof.
    eapply tctx_incl_ext; [eapply tctx_incl_trans;
      [apply tctx_vplace_fold_uniq|apply tctx_vplace_to_ty]|].
    by intros ? [? []] ??.
  Qed.
End conv.

(** * Utilities (formerly in [place.v]) *)

Section util.
  Context `{!typeG Σ}.

  Lemma uniq_bor_future_eq {𝔄} l (x₀: ~~𝔄) ξi d g idx π :
    uniq_bor_future (l, x₀, ξi, d, g, idx) π = (π (uniq_prvar x₀ ξi)).1.
  Proof. done. Qed.

  Lemma place_ghost_rsv_elem {𝔄} (x₀: ~~𝔄) ζi ζl :
    uniq_prvar x₀ ζi ∈ ζl → place_rfn_rsv (PlaceGhost x₀ ζi) ζl.
  Proof.
    intros ?. eapply proph_dep_weaken; [|apply place_ghost_rsv]. set_solver.
  Qed.

  (** Turning an equalizer of the value of some contents into an observation, by
      sharing the contents at a fresh lifetime to get guards of their prophecy tokens
      (as in [unblock_tctx_cons_unblock]). *)
  Lemma proph_eqz_obs_by_share {𝔄} (ty: type 𝔄) (xπ: proph 𝔄) x d g tid G :
    Timeless G →
    llft_ctx -∗ (G &&{↑NllftG}&&> @[ty_lft ty]) -∗ G -∗
    £(d + d*(g+2) + (0 + (d+1)*(g+1)) + 1 + 1) -∗
    (xπ :== vπ x) -∗ ty_gho_own ty x d g tid ={⊤}=∗
      ⟨π, xπ π = vπ x π⟩ ∗ G ∗ ty_gho_own ty x d g tid.
  Proof.
    iIntros (?) "#LFT #Gty G £ Eqz gho".
    iDestruct "£" as "[[[[£s £k] £k'] £e] £g]".
    iDestruct (ty_gho_pers_impl with "gho") as "#ghoPers".
    iMod (llftl_begin with "LFT") as (κf) "[κf #κfend]"; [solve_ndisj|].
    set κs := κf ⊓ ty_lft ty.
    iMod (llftl_borrow _ κs (ty_gho_own ty x d g tid) with "LFT [$gho]") as "[Bor Inh]";
      [solve_ndisj|].
    iAssert ((@[κf] ∗ G) &&{↑NllftG}&&> @[κs])%I as "#Wκs".
    { iApply guards_llft_glb; [iApply guards_weaken_sep_l|].
      iApply guards_weaken_lhs_sep_r. iApply "Gty". }
    iAssert (κs ⊑ ty_lft ty)%I as "#Incl". { iApply llftl_intersect_incl_r. }
    iMod (ty_share with "LFT Incl ghoPers Wκs [$κf $G] Bor") as "Upd"; [solve_ndisj|].
    iMod (lc_step_fupdN_elim_later with "£s Upd") as ">[[κf G] #Shr]".
    iAssert (▷^(d*(g+2)) (∀ ζ, ⌜ζ ∈ ξl x⌝ -∗
      ((@[κf] ∗ G) &&{↑NllftG; 0 + (d+1)*(g+1)}&&> 1:[ζ])))%I as "#Hallζlater".
    { iIntros (ζ) "%Hin".
      iDestruct (ty_shr_guard_proph ty κs x 0 d g tid ζ (@[κf] ∗ G)%I Hin
        with "LFT Incl ghoPers Shr") as "A".
      iNext. iApply "A". leaf_goal laters to 0; [lia|]. iFrame "Wκs". }
    iMod (lc_fupd_elim_laterN with "£k Hallζlater") as "#Hallζ".
    iMod (uniq_cmra.proph_eqz_to_obs_with_guard with "£k' Hallζ [κf G] Eqz")
      as "[#Obs [κf G]]"; [set_solver|apply syn_indep|iFrame|].
    iAssert (|={⊤}=> [†κf])%I with "[£e κf]" as ">#†κf".
    { iApply fupd_mask_mono; [|iApply (lc_step_fupd_elim_later with "£e"); by iApply "κfend"].
      solve_ndisj. }
    iAssert (|={⊤}=> ▷ ty_gho_own ty x d g tid)%I with "[Inh]" as ">gho".
    { iApply fupd_mask_mono; [|iApply "Inh"; iApply llftl_end_inter; by iLeft]. solve_ndisj. }
    iMod (lc_fupd_elim_later with "£g gho") as "gho".
    iModIntro. iFrame "∗#".
  Qed.
End util.
