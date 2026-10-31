From lrust.lang Require Import heap_cells.
From lrust.typing Require Export type own value_ctx shr_bor uniq_bor.
From lrust.typing Require Import programs freeable_util uninit uniq_util bool product.
From guarding Require Import guard tactics.
From lrust.lifetime Require Import lifetime_full.
Set Default Proof Using "Type".

(** * [PCell] on bytes (§10 step 5 of [design_docs/pcell-multibyte-cells.md])

A [PCell<T>] on the byte layer is a cell group ([lang/heap_cells.v]): a multi-byte cell
whose content has the MiniRust type [m]. Its two halves are two types:
- [pcell_ty m : type (pcellₛ m)], the cell itself. Its value is the group [g]; its
  ownership is trivial: the location side of the group (the edges from the locations of
  the cell to its byte-cells) is owned by the parent, as the fancy bytes of [g]
  ([bytes_own_pcell]). A [pcell_ty m] has no MiniRust value, so it lives only in memory
  (in a box, behind a reference, as a field).
- [cell_points_to_ty ty : type (trackedₛ (pcellₛ (syn_mty 𝔄) * 𝔄))], the permission
  ([PointsTo<T>] of Verus): a ghost value [(g, x)] that owns the dynamic registry entry of
  [g] ([gdyn g fv]), whose fancy value [fv] is the fancy value of [x] ([ty_fval x]; it may
  contain the groups of nested cells), together with the ownership of [x].

They replaced the legacy word-level [pcell_ty] and [cell_points_to_ty] (deleted in
stage 5). *)

Implicit Type 𝔄 𝔅: syn_type.

Section pcell.
  Context `{!typeG Σ}.

  Program Definition pcell_ty (m: mty) : type (pcellₛ m) :=
    {| ty_size := 0;
      ty_gho_own _ _ _ _ := True;
      ty_gho_res _ _ _ _ := True;
      ty_gho_pers _ _ _ _ := True;
      ty_mty := syn_mty _; ty_val := syn_val; ty_mty_eq := eq_refl; ty_val_eq _ := eq_refl;
      ty_fval := syn_fval; ty_fval_eq _ := eq_refl;
      ty_phys _ _ := [];
      ty_lfts := [];
      ty_E := [];
      ty_shr := default_shr (λ _ _ _ _, True);
     |}%I.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. move => *. iIntros "_". iSplit; auto. Qed.
  Next Obligation. move => *. auto. Qed.
  Next Obligation. move => *. by iIntros "?". Qed.
  Solve All Obligations with solve_default_shr.
  Next Obligation. intros. iIntros "H". iExact "H". Qed.

  Global Instance pcell_res_own m : ResOwn (pcell_ty m).
  Proof. done. Qed.

  Global Instance pcell_send m : Send (pcell_ty m).
  Proof.
    intros. split; trivial.
    iIntros. iApply step_fupdN_intro; first done. iNext.
    iExists x, 0%nat. iModIntro. iFrame. simpl.
    replace (d0 + 0)%nat with d0 by lia. iFrame "#". done.
  Qed.

  Global Instance pcell_sync m : Sync (pcell_ty m).
  Proof. apply sync_default; [done|]. split; trivial. split; iSplit; done. Qed.

  Lemma pcell_ty_mty m : mty_wf m → (pcell_ty m).(ty_mty) = m.
  Proof. intros. by rewrite -ty_mty_eq /= decide_True. Qed.

  Lemma pcell_ty_bsize m : mty_wf m → ty_bsize (pcell_ty m) = mty_size m.
  Proof. intros. by rewrite /ty_bsize pcell_ty_mty. Qed.

  (** The fancy bytes of a cell are the location side of its group. *)
  Lemma bytes_own_pcell_ty m l g :
    mty_wf m →
    bytes_own (pcell_ty m) l g ⊣⊢ ∃ cs, loc_side l g m cs ∗ ⌜length cs = mty_size m⌝.
  Proof. apply bytes_own_pcell. Qed.
End pcell.

Section cell_points_to.
  Context `{!typeG Σ}.

  (** The permission of the group [g] whose content is the value [x] of [ty]: the static
      registry entry of [g] (at the MiniRust type of [ty]) and the dynamic one (at the
      fancy value of [x]). *)
  Definition cell_own {𝔄} (ty: type 𝔄) (g: positive) (x: ~~𝔄) : iProp Σ :=
    ∃ fv cs, ⌜ty.(ty_fval) x = Some fv⌝ ∗ greg g ty.(ty_mty) cs ∗ gdyn g fv.

  Global Instance cell_own_timeless {𝔄} (ty: type 𝔄) g x : Timeless (cell_own ty g x).
  Proof. apply _. Qed.

  Lemma cell_own_same {𝔄} (ty ty': type 𝔄) g x : cell_own ty g x ⊣⊢ cell_own ty' g x.
  Proof. by rewrite /cell_own (ty_mty_same ty ty') (ty_fval_same ty ty'). Qed.

  Lemma cell_own_greg {𝔄} (ty: type 𝔄) g x :
    cell_own ty g x -∗ ∃ fv cs, ⌜ty.(ty_fval) x = Some fv⌝ ∗ greg g ty.(ty_mty) cs.
  Proof. iIntros "(%fv & %cs & % & $ & _)". by iExists fv. Qed.

  Program Definition cell_points_to_ty {𝔄} (ty: type 𝔄) :
      type (trackedₛ (pcellₛ (syn_mty 𝔄) * 𝔄)) :=
    {| ty_size := 0%nat;
      ty_lfts := ty.(ty_lfts);
      ty_E := ty.(ty_E);
      ty_gho_own x d g tid :=
        [S(d') := d] cell_own ty x.1 x.2 ∗ ▷ ty.(ty_gho_own) x.2 d' g tid;
      ty_gho_res x d g tid :=
        [S(d') := d] cell_own ty x.1 x.2 ∗ ▷ ty.(ty_gho_res) x.2 d' g tid;
      ty_gho_pers x d g tid :=
        [S(d') := d] (∃ fv cs, ⌜ty.(ty_fval) x.2 = Some fv⌝ ∗ greg x.1 ty.(ty_mty) cs) ∗
          ▷ ty.(ty_gho_pers) x.2 d' g tid;
      ty_mty := syn_mty _; ty_val := syn_val; ty_mty_eq := eq_refl; ty_val_eq _ := eq_refl;
      ty_fval := syn_fval; ty_fval_eq _ := eq_refl;
      ty_phys _ _ := [];
      (* Structural, as for [own_ptr]. *)
      ty_shr κ x d g tid :=
        ▷ [S(d') := d]
          (@[κ] &&{↑NllftG; g+1}&&> cell_own ty x.1 x.2) ∗ ty.(ty_shr) κ x.2 d' g tid;
    |}%I.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation.
    move => 𝔄 ty d g d' g' x tid ??//=.
    iIntros "H". destruct d => //=. destruct d' => //=; first lia.
    iDestruct "H" as "[Hown Hgho]". iFrame "Hown".
    iDestruct (ty.(ty_gho_own_depth_mono) with "Hgho") as "[$ Hwand]" => //; first lia.
    iIntros "[$ Hgho] !>". by iApply "Hwand".
  Qed.
  Next Obligation.
    move => 𝔄 ty d g d' g' x tid ??//=.
    iIntros "H". destruct d => //=. destruct d' => //=; first lia.
    iDestruct "H" as "[$ H]". iNext.
    iDestruct (ty.(ty_gho_pers_depth_mono) _ _ d' g' with "H") as "?" => //; lia.
  Qed.
  Next Obligation.
    intros 𝔄 ty x d g tid. iIntros "A". destruct d as [|d']; first by done.
    iDestruct "A" as "[A1 A2]". iSplitL "A1"; [by iApply cell_own_greg|].
    iApply ty_gho_pers_impl. iFrame.
  Qed.
  Next Obligation.
    intros 𝔄 ty κ κ' x n d g tid. iIntros "#Incl Shr".
    iNext. destruct d as [|d']; [done|]. iDestruct "Shr" as "[Pt Shr]". iSplit.
    - replace (g + n + 1) with (n + (g + 1)) by lia.
      iApply (guards_transitive_additive with "Incl Pt").
    - iApply (ty_shr_lft_mono with "Incl Shr").
  Qed.
  Next Obligation.
    intros 𝔄 ty κ d g d' g' x tid ??. iIntros "Shr".
    iNext. destruct d as [|d0]; [done|]. destruct d' as [|d0']; [lia|].
    iDestruct "Shr" as "[Pt Shr]". iSplit.
    - leaf_goal laters to (g+1). { lia. } iFrame "Pt".
    - iApply (ty_shr_depth_mono with "Shr"); lia.
  Qed.
  Next Obligation.
    intros 𝔄 ty E κ x d g tid G ??. iIntros "#LFT #Incl #Pers #Gκ G Bor".
    destruct d as [|d']; [done|]. simpl. iDestruct "Pers" as "[_ Pers]".
    iMod (llftl_sep_split with "LFT Bor") as "[Pt Bor]"; [solve_ndisj|].
    iMod (llftl_bor_guard with "LFT Pt") as "#Pt"; [solve_ndisj|].
    iMod (llftl_bor_later_step with "LFT Gκ G Bor") as "Upd"; [first [apply _ | solve_ndisj]..|].
    iModIntro. iModIntro. iNext. iMod "Upd" as "[G Bor]".
    iMod (ty_share with "LFT Incl Pers Gκ G Bor") as "Shr"; [done..|].
    iModIntro. iApply (step_fupdN_wand with "Shr"). iIntros ">[$ Shr] !> !>".
    iFrame "Shr". leaf_goal laters to 1. { lia. } iFrame "Pt".
  Qed.
  Next Obligation.
    intros 𝔄 ty κ x n0 d g tid ξ R Hin.
    iIntros "#LFT #Incl #Pers #Shr".
    destruct d as [|d']; first by done. simpl.
    iDestruct "Pers" as "[_ Pers]".
    iApply (bi.laterN_le (S (d' * (g + 2)))). { lia. }
    iNext. iDestruct "Shr" as "[_ Shr]".
    iDestruct (ty_shr_guard_proph ty κ x.2 n0 d' g tid ξ R Hin with "LFT Incl Pers Shr")
      as "GP".
    iNext. iIntros "#Rκ".
    leaf_goal laters to (n0 + (d'+1)*(g+1)). { lia. } by iApply "GP".
  Qed.
  Next Obligation.
    intros 𝔄 ty x [|d] g tid; [by iIntros|]. iIntros "[$ A]". iNext.
    by iApply ty_gho_res_of_own.
  Qed.

  Global Instance cell_points_to_res_own {𝔄} (ty: type 𝔄) :
    ResOwn ty → ResOwn (cell_points_to_ty ty).
  Proof. move=> ? x [|d] g tid //=. by rewrite res_own. Qed.

  Global Instance cell_points_to_send {𝔄} (ty: type 𝔄) :
      Send ty → Send (cell_points_to_ty ty).
  Proof.
    intros [Hphys Hgho]. split; trivial.
    intros tid tid' x d g G H κs d0 Hineq TG TH.
    iIntros "LFT UNIQ TIME Hg H Gg G Hgho #⧖o".
    destruct d => //=.
    iDestruct "Hgho" as "(Hown&Hgho)".
    iModIntro. iNext. iModIntro.
    iPoseProof (Hgho with "LFT UNIQ TIME Hg H Gg G Hgho ⧖o") as "X"; first lia.
    iApply (step_fupdN_wand with "X"). iIntros ">X".
    iDestruct "X" as (x' off) "[gho [#⧖off [%Habs [G H]]]]".
    iExists (x.1, x'), (off). iModIntro. iFrame. iFrame "#".
    iSplitL "Hown".
    - rewrite /cell_own. by rewrite -!ty_fval_eq (syn_abstract_fval_eq _ _ _ Habs).
    - iPureIntro. simpl. by rewrite Habs.
  Qed.

  Global Instance cell_points_to_sync {𝔄} (ty: type 𝔄) :
      Sync ty → Sync (cell_points_to_ty ty).
  Proof.
      move=> HSync tid tid' x d g.
      have EqOwn: ∀ d0 g0, (cell_points_to_ty ty).(ty_gho_own) x d0 g0 tid ⊣⊢
          (cell_points_to_ty ty).(ty_gho_own) x d0 g0 tid'.
      { move=> [|d0] g0 //=. destruct (HSync tid tid' x.2 d0 g0) as [_ [Hgho _]].
        by rewrite Hgho. }
      split => //=. split; [apply EqOwn|]. split.
      - destruct d => //=.
        pose proof (sync_change_tid tid tid' (snd x) d g) as [_ [Hgho [Hghopers _]]].
        rewrite Hghopers. trivial.
      - move=> κ. f_equiv.
        destruct d => //=. destruct (HSync tid tid' x.2 d g) as [_ [_ [_ Hshr]]].
        by rewrite Hshr.
  Qed.

  (** The permission is a ghost value: its MiniRust value is the empty tuple. *)
  Lemma cell_points_to_val {𝔄} (ty: type 𝔄) x :
    (cell_points_to_ty ty).(ty_val) x = Some (VTuple []).
  Proof. done. Qed.
End cell_points_to.

(** * WP helpers *)
Section pcell_wp.
  Context `{!typeG Σ}.

  (** Fancy bytes that represent a value have the size of its MiniRust type (an update of
      the byte context: the static registry is well formed). *)
  Lemma wp_brepr_length E e m fbs fv Φ :
    TCEq (to_val e) None →
    brepr m fbs fv -∗ (⌜length fbs = mty_size m⌝ -∗ WP e @ E {{ Φ }}) -∗ WP e @ E {{ Φ }}.
  Proof.
    iIntros (Hv) "#Hrep Hwp". iApply wp_bytes_ctx_pre. iIntros (σB) "HB".
    iAssert ⌜length fbs = mty_size m⌝%I as %Hlen.
    { iDestruct "HB" as "(%𝛼 & %M & _ & _ & _ & _ & _ & Cells)".
      iDestruct "Cells" as (R ρ NC NS CW) "(Hreg & _ & _ & _ & _ & [%Hcwf _] & _)".
      iDestruct (brepr_frepr with "Hreg Hrep") as %Hfrep. iPureIntro.
      eapply frepr_length; [apply Hcwf|done]. }
    iModIntro. iFrame "HB". by iApply "Hwp".
  Qed.

  (** [wp_pcell_memcopy], with the size of the bytes left behind. *)
  Lemma wp_pcell_memcopy_len E l l' g m cs bs0 :
    ↑naN ⊆ E → length bs0 = mty_size m →
    {{{ loc_side l g m cs ∗ ▷ l' ↦b bs0 }}}
      MemCopy Na1Ord (mty_size m) (Lit $ LitLoc l') (Lit $ LitLoc l) @ E
    {{{ bs, RET LitV LitPoison; l ↦b bs ∗ ⌜length bs = mty_size m⌝ ∗ loc_side l' g m cs }}}.
  Proof.
    iIntros (? Hlen Φ) "[Hls Hl'] HΦ". iApply wp_bytes_ctx_pre. iIntros (σB) "HB".
    iMod (bytes_ctx_pcell_untether with "HB Hls") as (bs v) "(HB & Hl & %Hd & Hu)"; [done|].
    iModIntro. iFrame "HB".
    iApply (wp_memcopy_post with "Hl' Hl"); [done|done|by eapply decode_value_length|].
    iIntros "!> Hl' Hl" (σB') "HB".
    iMod (bytes_ctx_pcell_retether_eq with "HB Hu Hl'") as "[HB Hls]"; [done|].
    iModIntro. iFrame "HB". iApply "HΦ". iFrame. iPureIntro. by eapply decode_value_length.
  Qed.

  (** Moving a [PCell] by a typed copy, [Store m (Load m)] (as [wp_pcell_move] of
      [lang/pcell_tests.v]), with the size of the bytes left behind. *)
  Lemma wp_pcell_move_len E l l' g m cs bs0 :
    ↑naN ⊆ E → mty_wf m → length bs0 = mty_size m →
    {{{ loc_side l g m cs ∗ ▷ l' ↦b bs0 }}}
      Store Na1Ord m (Lit $ LitLoc l') (Load Na1Ord m (Lit $ LitLoc l)) @ E
    {{{ bs, RET LitV LitPoison; l ↦b bs ∗ ⌜length bs = mty_size m⌝ ∗ loc_side l' g m cs }}}.
  Proof.
    iIntros (? Hm Hlen Φ) "(Hls & Hl') HΦ". iApply wp_bytes_ctx_pre. iIntros (σB) "HB".
    iMod (bytes_ctx_pcell_untether with "HB Hls") as (bs v) "(HB & Hl & %Hd & Hu)"; [done|].
    iModIntro. iFrame "HB".
    wp_bind (Load _ _ _). iApply (wp_load_na with "Hl"); [done|]. iIntros "!> Hl".
    iApply (wp_store_na_post with "Hl'"); [done|by eapply decode_value_wf|done|].
    iIntros "!> Hl'" (σB') "HB".
    iMod (bytes_ctx_pcell_retether_gen with "HB Hu Hl'") as "[HB Hls]"; [done| |].
    { rewrite decode_encode_value; [by rewrite Hd|done|by eapply decode_value_wf]. }
    iModIntro. iFrame "HB". iApply "HΦ". iFrame. iPureIntro. by eapply decode_value_length.
  Qed.
End pcell_wp.

(** * Creating, destroying and moving a [PCell] *)
Section pcell_rules.
  Context `{!typeG Σ}.

  (** [PCell::new]: the contents of a box become a cell. The box now holds the cell, and
      the permission is returned (a ghost value). Groups are not zero-sized. *)
  Definition PCellNew : val := (λ: ["p"], MkTuple [])%V.

  Lemma type_pcell_new_instr {𝔄} n (ty: type 𝔄) p E L I :
    (0 < ty_bsize ty)%nat →
    typed_instr E L I +[p ◁ᵥ own_bytes n ty] (PCellNew [p])
      (λ v, +[p ◁ᵥ own_bytes n (pcell_ty ty.(ty_mty)); v ◁ᵥ cell_points_to_ty ty])
      (λ post '-[(l, x)], λ mask π, ∀ g, post -[(l, g); (g, x)] mask π).
  Proof.
    iIntros (Hsz tid post mask iκs [[l x] []]) "_ _ _ _ _ $ $ [p _] Obs".
    iDestruct "p" as (vp Hp w d [-> Hw]) "[#⧖ Own]". simpl in Hw. simplify_eq.
    rewrite /PCellNew. wp_bind p.
    iApply (wp_wand with "[]"); [by iApply wp_eval_path|]. iIntros (? ->).
    destruct d as [|d]; [done|]. iDestruct "Own" as "(Bytes & Free & Gho)".
    rewrite bytes_own_brepr. iDestruct "Bytes" as (fbs fv) "(Hfbs & [%Hlen %Hfv] & #Hrep)".
    iApply (wp_pcell_create with "Hfbs Hrep"); [solve_ndisj|exact Hsz|apply ty_mty_wf|].
    iIntros (g cs) "Hls Hgd _". iDestruct "Hls" as "[#Hg Hls]".
    iApply (wp_greg_length with "Hg"). iIntros (Hcs).
    wp_rec.
    eapply (tac_wp_pure []); [apply (pure_mk_tuple [])|done|tc_solve|simpl; iApply wp_value].
    iExists -[(l, g); (g, x)]. iSplitR "Obs"; last first.
    { iApply (proph_obs_impl with "Obs"). intros π Hpost. apply Hpost. }
    iSplitL "Free Hls"; [|iSplitL; [|done]].
    - iExists _. iSplit; [done|]. iExists (VPtr l), (S d). iSplit; [done|]. iFrame "⧖".
      iSplitL "Hls"; [|iSplitL; [|done]].
      + rewrite bytes_own_pcell_ty; [|apply ty_mty_wf]. iExists cs. by iFrame "Hg Hls".
      + rewrite pcell_ty_bsize; [|apply ty_mty_wf]. iFrame "Free".
    - rewrite tctx_val_val. iExists (S d). iSplit; [done|]. iFrame "⧖ Gho".
      iExists fv, cs. by iFrame "Hg Hgd".
  Qed.

  (** The form of [PCell::new] of the deleted legacy rule [typed_pcell_from_own]: the box holds the cell and
      the (zero-sized) permission, as a pair. *)
  Definition PCellFromOwn : val := (λ: ["p"], "p")%V.

  Lemma cell_points_to_bytes_own {𝔄} (ty: type 𝔄) l x :
    ⊢ bytes_own (cell_points_to_ty ty) l x.
  Proof. iApply bytes_own_zst_emp; [by rewrite /ty_bsize -ty_mty_eq|done]. Qed.

  Lemma pcell_pair_bsize {𝔄} (ty: type 𝔄) :
    ty_bsize (pcell_ty ty.(ty_mty) * cell_points_to_ty ty)%T = ty_bsize ty.
  Proof.
    rewrite /ty_bsize -ty_mty_eq /= decide_True; [|apply ty_mty_wf].
    rewrite /seq_size /=. lia.
  Qed.

  Lemma type_pcell_from_own_instr {𝔄} n (ty: type 𝔄) p E L I :
    (0 < ty_bsize ty)%nat →
    typed_instr E L I +[p ◁ᵥ own_bytes n ty] (PCellFromOwn [p])
      (λ v, +[v ◁ᵥ own_bytes n (pcell_ty ty.(ty_mty) * cell_points_to_ty ty)%T])
      (λ post '-[(l, x)], λ mask π, ∀ g, post -[(l, (g, (g, x)))] mask π).
  Proof.
    iIntros (Hsz tid post mask iκs [[l x] []]) "_ #TIME _ _ _ $ $ [p _] Obs".
    iDestruct "p" as (vp Hp w d [-> Hw]) "[#⧖ Own]". simpl in Hw. simplify_eq.
    rewrite /PCellFromOwn. wp_bind p.
    iApply (wp_wand with "[]"); [by iApply wp_eval_path|]. iIntros (? ->).
    destruct d as [|d]; [done|]. iDestruct "Own" as "(Bytes & Free & Gho)".
    rewrite bytes_own_brepr. iDestruct "Bytes" as (fbs fv) "(Hfbs & [%Hlen %Hfv] & #Hrep)".
    iApply (wp_pcell_create with "Hfbs Hrep"); [solve_ndisj|exact Hsz|apply ty_mty_wf|].
    iIntros (g cs) "Hls Hgd _". iDestruct "Hls" as "[#Hg Hls]".
    iApply (wp_greg_length with "Hg"). iIntros (Hcs).
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|]. iIntros "_ #⧖S".
    wp_rec.
    iExists -[(l, (g, (g, x)))]. iSplitR "Obs"; last first.
    { iApply (proph_obs_impl with "Obs"). intros π Hpost. apply Hpost. }
    iSplit; [|done]. rewrite tctx_val_val. iExists (S (S d)). iSplit; [done|]. iFrame "⧖S".
    iSplitL "Hls"; [|iSplitL "Free"].
    - rewrite (bytes_own_pair _ (pcell_ty ty.(ty_mty)) (cell_points_to_ty ty)).
      iSplitL; [|iApply cell_points_to_bytes_own].
      rewrite bytes_own_pcell_ty; [|apply ty_mty_wf]. iExists cs. by iFrame "Hg Hls".
    - by rewrite pcell_pair_bsize.
    - iNext. iSplit; [done|]. iSplitL "Hgd"; [iExists fv, cs; by iFrame "Hg Hgd"|].
      iNext. iDestruct (ty_gho_own_depth_mono _ d (S d) d (S (S d)) with "Gho") as "[$ _]"; lia.
  Qed.

  (** [PCell::into_inner]: a box holding a cell and the permission of its group give back
      a box holding the contents. *)
  Definition PCellIntoInner : val := (λ: ["pcell"; "perm"], "pcell")%V.

  Lemma type_pcell_into_inner_instr {𝔄} n (ty: type 𝔄) p q E L I :
    typed_instr E L I +[p ◁ᵥ own_bytes n (pcell_ty ty.(ty_mty)); q ◁ᵥ cell_points_to_ty ty]
      (PCellIntoInner [p; q]) (λ v, +[v ◁ᵥ own_bytes n ty])
      (λ post '-[(l, g); (g', x)], λ mask π, g = g' ∧ post -[(l, x)] mask π).
  Proof.
    iIntros (tid post mask iκs [[l g] [[g' x] []]]) "_ _ #PROPH _ _ $ $ (p & q & _) #Obs".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & _)"; [done|].
    iDestruct "p" as (vp Hp wp dp [-> Hwp]) "[#⧖p Own]". simpl in Hwp. simplify_eq.
    iDestruct "q" as (vq Hq wq dq [-> Hwq]) "[#⧖q Pt]".
    rewrite /PCellIntoInner.
    wp_bind p. iApply (wp_wand with "[]"); [by iApply wp_eval_path|]. iIntros (? ->).
    wp_bind q. iApply (wp_wand with "[]"); [by iApply wp_eval_path|]. iIntros (? ->).
    destruct dp as [|dp]; [done|]. destruct dq as [|dq]; [done|].
    iDestruct "Own" as "(Bytes & Free & _)".
    iDestruct "Pt" as "[(%fv & %cs' & %Hfv & #Hg' & Hgd) Gho]".
    rewrite bytes_own_pcell_ty; [|apply ty_mty_wf]. iDestruct "Bytes" as (cs) "[Hls %Hcs]".
    iApply (wp_pcell_destroy with "Hls Hgd"). iIntros (fbs) "Hfbs #Hrep".
    iApply (wp_brepr_length with "Hrep"). iIntros (Hlen).
    wp_rec. iExists -[(l, x)]. iSplitR "Obs"; last first.
    { iApply (proph_obs_impl with "Obs"). by intros π [_ ?]. }
    iSplit; [|done]. rewrite tctx_val_val. iExists (S dq). iSplit; [done|]. iFrame "⧖q Gho".
    iSplitL "Hfbs".
    - rewrite bytes_own_brepr. iExists fbs, fv. by iFrame "Hfbs Hrep".
    - rewrite pcell_ty_mty; [|apply ty_mty_wf]. done.
  Qed.

  Lemma uninit_bytes_own k l u bs : length bs = k → l ↦b bs -∗ bytes_own (↯ k) l u.
  Proof.
    iIntros (Hlen) "Hbs". iApply (bytes_own_of_bytes with "Hbs"). exists (VTuple []).
    split; [done|]. rewrite -ty_mty_eq /= decide_True //.
  Qed.

  Lemma bytes_own_uninit k l u :
    bytes_own (↯ k) l u -∗ ∃ bs, l ↦b bs ∗ ⌜length bs = k⌝.
  Proof.
    iIntros "Own". iDestruct (bytes_own_nocell_bytes with "Own") as (bs) "[Hbs %Hbs]".
    iExists bs. iFrame. iPureIntro. apply ty_bytes_length in Hbs. by rewrite Hbs.
  Qed.

  (** Moving a [PCell] from a box into a box of uninitialized bytes, by a verbatim copy
      ([MemCopy]). *)
  Lemma type_pcell_memcpy_instr n n' m p q E L I :
    mty_wf m →
    typed_instr E L I +[p ◁ᵥ own_bytes n (↯ (mty_size m)); q ◁ᵥ own_bytes n' (pcell_ty m)]
      (MemCopy Na1Ord (mty_size m) (ToLit p) (ToLit q))
      (λ _, +[p ◁ᵥ own_bytes n (pcell_ty m); q ◁ᵥ own_bytes n' (↯ (mty_size m))])
      (λ post '-[(l, u); (l', g)], post -[(l, g); (l', u)]).
  Proof.
    iIntros (Hm tid post mask iκs [[l u] [[l' g] []]]) "_ _ _ _ _ $ $ (p & q & _) Obs".
    wp_bind p. iApply (wp_val with "p"). iIntros (w d Hp Hw) "#⧖ Own".
    simpl in Hw. simplify_eq. wp_pure _.
    wp_bind q. iApply (wp_val with "q"). iIntros (w' d' Hq Hw') "#⧖' Own'".
    simpl in Hw'. simplify_eq. wp_pure _.
    destruct d as [|d]; [done|]. destruct d' as [|d']; [done|].
    iDestruct "Own" as "(Bytes & Free & _)". iDestruct "Own'" as "(Bytes' & Free' & _)".
    iDestruct (bytes_own_uninit with "Bytes") as (bs0) "[Hbs0 %Hlen0]".
    rewrite bytes_own_pcell_ty //. iDestruct "Bytes'" as (cs) "[Hls %Hcs]".
    iApply (wp_pcell_memcopy_len with "[$Hls $Hbs0]"); [done|done|].
    iIntros "!>" (bs) "(Hbs & %Hlen & Hls)". iExists -[(l, g); (l', u)]. iFrame "Obs".
    iSplitL "Hls Free"; [|iSplitL; [|done]].
    - iExists _. iSplit; [done|]. iExists (VPtr l), (S d). iSplit; [done|]. iFrame "⧖".
      iSplitL "Hls"; [|iSplitL; [|done]].
      + rewrite bytes_own_pcell_ty //. iExists cs. by iFrame.
      + rewrite /ty_bsize pcell_ty_mty //.
    - iExists _. iSplit; [done|]. iExists (VPtr l'), (S d'). iSplit; [done|]. iFrame "⧖'".
      iSplitL "Hbs"; [|iSplitL; [|done]].
      + by iApply (uninit_bytes_own with "Hbs").
      + iEval (rewrite /ty_bsize pcell_ty_mty //) in "Free'". done.
  Qed.

  (** Moving a [PCell] from a box into a box of uninitialized bytes, by a typed copy
      ([Store m (Load m)]): the bytes at the new location are the encoding of the decoded
      contents (padding becomes uninitialized; the contents may embed cells). *)
  Lemma type_pcell_move_instr n n' m p q E L I :
    mty_wf m →
    typed_instr E L I +[p ◁ᵥ own_bytes n (↯ (mty_size m)); q ◁ᵥ own_bytes n' (pcell_ty m)]
      (Store Na1Ord m (ToLit p) (Load Na1Ord m (ToLit q)))
      (λ _, +[p ◁ᵥ own_bytes n (pcell_ty m); q ◁ᵥ own_bytes n' (↯ (mty_size m))])
      (λ post '-[(l, u); (l', g)], post -[(l, g); (l', u)]).
  Proof.
    iIntros (Hm tid post mask iκs [[l u] [[l' g] []]]) "_ _ _ _ _ $ $ (p & q & _) Obs".
    wp_bind p. iApply (wp_val with "p"). iIntros (w d Hp Hw) "#⧖ Own".
    simpl in Hw. simplify_eq. wp_pure _.
    wp_bind q. iApply (wp_val with "q"). iIntros (w' d' Hq Hw') "#⧖' Own'".
    simpl in Hw'. simplify_eq. wp_pure _.
    destruct d as [|d]; [done|]. destruct d' as [|d']; [done|].
    iDestruct "Own" as "(Bytes & Free & _)". iDestruct "Own'" as "(Bytes' & Free' & _)".
    iDestruct (bytes_own_uninit with "Bytes") as (bs0) "[Hbs0 %Hlen0]".
    rewrite bytes_own_pcell_ty //. iDestruct "Bytes'" as (cs) "[Hls %Hcs]".
    iApply (wp_pcell_move_len with "[$Hls $Hbs0]"); [done|done|done|].
    iIntros "!>" (bs) "(Hbs & %Hlen & Hls)". iExists -[(l, g); (l', u)]. iFrame "Obs".
    iSplitL "Hls Free"; [|iSplitL; [|done]].
    - iExists _. iSplit; [done|]. iExists (VPtr l), (S d). iSplit; [done|]. iFrame "⧖".
      iSplitL "Hls"; [|iSplitL; [|done]].
      + rewrite bytes_own_pcell_ty //. iExists cs. by iFrame.
      + rewrite /ty_bsize pcell_ty_mty //.
    - iExists _. iSplit; [done|]. iExists (VPtr l'), (S d'). iSplit; [done|]. iFrame "⧖'".
      iSplitL "Hbs"; [|iSplitL; [|done]].
      + by iApply (uninit_bytes_own with "Hbs").
      + iEval (rewrite /ty_bsize pcell_ty_mty //) in "Free'". done.
  Qed.
End pcell_rules.

(** * Guards of a cell and its permission

A shared reference to a cell guards its location side (its fancy bytes,
[bytes_own_pcell_ty]), and a shared reference to its permission guards [cell_own]. An
access through the cell needs a guard of both; two guards by the same token are combined
into a guard of their conjunction ([guards_and_point]), which is their separating
conjunction ([loc_side_and_gdyn]). *)
Section cell_guards.
  Context `{!typeG Σ}.

  Lemma point_prop_loc_side_gdyn l g m cs fv :
    factoring_props.point_prop (loc_side l g m cs ∗ gdyn g fv).
  Proof. apply factoring_props.point_prop_sep; [apply point_prop_loc_side|apply point_prop_gdyn]. Qed.

  Lemma guard_pcell_loc_side G n m l g cs :
    mty_wf m →
    greg g m cs -∗ (G &&{↑NllftG; n}&&> bytes_own (pcell_ty m) l g) -∗
    (G &&{↑NllftG; n}&&> loc_side l g m cs).
  Proof.
    iIntros (Hm) "#Hg #G1". iDestruct (guards_include_pers with "Hg G1") as "G1g".
    iApply (guards_weaken_rhs_point with "G1g"); [apply point_prop_loc_side|].
    rewrite bytes_own_pcell_ty //.
    iIntros "[(%cs' & [#Hg' Hls] & _) #Hg]". iDestruct (greg_agree with "Hg Hg'") as %[_ <-].
    by iFrame "Hg Hls".
  Qed.

  Lemma guard_cell_own_gdyn {𝔄} (ty: type 𝔄) G n g x fv :
    ty.(ty_fval) x = Some fv →
    (G &&{↑NllftG; n}&&> cell_own ty g x) -∗ (G &&{↑NllftG; n}&&> gdyn g fv).
  Proof.
    iIntros (Hfv) "#G2". iApply (guards_weaken_rhs_point with "G2"); [apply point_prop_gdyn|].
    iIntros "(%fv' & %cs' & %Hfv' & _ & Hgd)". rewrite Hfv in Hfv'. by injection Hfv' as ->.
  Qed.

  Lemma guard_cell_combine {𝔄} (ty: type 𝔄) G n l g cs x fv :
    ty.(ty_fval) x = Some fv →
    greg g ty.(ty_mty) cs -∗
    (G &&{↑NllftG; n}&&> bytes_own (pcell_ty ty.(ty_mty)) l g) -∗
    (G &&{↑NllftG; n}&&> cell_own ty g x) -∗
    (G &&{↑NllftG; n}&&> loc_side l g ty.(ty_mty) cs ∗ gdyn g fv).
  Proof.
    iIntros (Hfv) "#Hg #G1 #G2".
    iDestruct (guard_pcell_loc_side with "Hg G1") as "G1'"; [apply ty_mty_wf|].
    iDestruct (guard_cell_own_gdyn with "G2") as "G2'"; [done|].
    iApply (guards_and_point with "G1' G2'"); [apply point_prop_loc_side_gdyn|].
    apply loc_side_and_gdyn.
  Qed.
End cell_guards.

(** * Atomic accesses through a cell

As the deleted legacy [typed_pcell_atomic_load], [typed_pcell_atomic_store] and
[typed_pcell_atomic_CAS]: at the MiniRust type of the contents (no mixed-size accesses), for
contents without cells ([NoCell]). A load needs shared references to the cell and to its
permission; a store and a compare-and-exchange need a unique borrow of the permission, which
they resolve. *)
Section pcell_atomics.
  Context `{!typeG Σ}.

  Lemma type_pcell_load_sc_instr {𝔄} `{!NoCell 𝔄} κ (ty: type 𝔄) p q E L I :
    Copy ty → lctx_lft_alive E L κ →
    typed_instr E L I
      +[p ◁ᵥ &shr{κ} (pcell_ty ty.(ty_mty)); q ◁ᵥ &shr{κ} (cell_points_to_ty ty)]
      (Load ScOrd ty.(ty_mty) (ToLit p))
      (λ v, +[v ◁ᵥ ty]) (λ post '-[(_, g); (_, (g', x))], λ mask π, g = g' ∧ post -[x] mask π).
  Proof.
    iIntros (? Alv tid post mask iκs [[l g] [[l' [g' x]] []]])
      "#LFT #TIME #PROPH _ #E L $ (p & q & _) #Obs".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & _)"; [done|].
    iDestruct "q" as (vq Hq wq dq [-> Hwq]) "[#⧖q #Own']".
    wp_bind p. iApply (wp_val with "p"). iIntros (w d Hp Hw) "#⧖ #Own".
    simpl in Hw. simplify_eq. wp_pure _.
    destruct d as [|d0]; [done|]. destruct dq as [|dq0]; [done|].
    iDestruct "Own" as "(#Gp & _ & _)". iDestruct "Own'" as "(_ & #Shr & #Pers)".
    iMod (llctx_interp_make_guarded with "L") as (γ) "[H1 [H2 [#Gh #Back]]]"; [solve_ndisj|].
    iAssert (|={⊤}=> fractional.half γ ∗ (fractional.half γ &&{↑NllftG}&&> @[κ]))%I
      with "[H1]" as ">[H1 #Gκ]".
    { leaf_open "Gh" with "H1" as "[InterpL back]". { solve_ndisj. }
      iDestruct (Alv with "InterpL E") as "#Alv".
      iMod ("back" with "InterpL") as "$". iModIntro.
      iApply (guards_transitive with "Gh Alv"). }
    set D := S d0 `max` S dq0.
    iAssert (⧖D)%I as "#⧖D"; [rewrite persistent_time_receipt_sep; by iFrame "⧖ ⧖q"|].
    iApply (wp_persistent_time_receipt with "TIME ⧖D"); [done|]. iIntros "£ #⧖S".
    iDestruct (lc_weaken (1 + (S dq0 + 1) + (S dq0 + 1) + (D + 1)) with "£")
      as "[[[£1 £2] £3] £4]"; [rewrite /advance_credits; lia|].
    iMod (lc_fupd_elim_later with "£1 Shr") as "Shr'".
    destruct dq0 as [|d'']; [done|]. iDestruct "Shr'" as "[#G2 #TyShr]".
    iMod (lc_fupd_elim_laterN with "£2 Pers") as "Pers'".
    iDestruct "Pers'" as "[(%fv & %cs & %Hfv & #Hg) _]".
    iDestruct (copy_shr with "TyShr") as "#GOwn".
    iDestruct (guards_transitive_right with "Gκ GOwn") as "GO".
    iAssert (|={⊤ ∖ ↑advN}=> fractional.half γ ∗ ty.(ty_gho_own) x d'' (S (S d'')) tid)%I
      with "[H1 £3]" as ">[H1 #Gho]".
    { iMod (guards_open_later with "GO H1") as "Open"; [solve_ndisj|].
      iMod (lc_fupd_elim_laterN with "£3 Open") as ">[#Gho Close]".
      iMod ("Close" with "Gho") as "$". by iModIntro. }
    iDestruct (guards_transitive_right with "Gκ Gp") as "G1".
    iDestruct (guards_transitive_right with "Gκ G2") as "G2'".
    iDestruct (lguards_weaken_later _ _ _ _ (D + 1) with "G1") as "G1D"; [lia|].
    iDestruct (lguards_weaken_later _ _ _ _ (D + 1) with "G2'") as "G2D"; [lia|].
    iDestruct (guard_cell_combine with "Hg G1D G2D") as "GP"; [done|].
    have Hc : fv_cells fv = [] by eapply ty_fval_nocell_cells.
    iApply wp_fupd.
    iApply (wp_pcell_load_sc_guarded _ l.1 g ty.(ty_mty) cs fv (fractional.half γ) _ (D + 1)
      with "[H1 £4]"); [solve_ndisj|done| |].
    { iSplitR; [done|]. iSplitR; [iIntros "!> [Hls Hgd]"; iFrame; by iIntros "$ $"|].
      iFrame "Hg H1 £4". }
    iIntros "!>" (v) "[H1 %Hv]".
    iMod (fupd_mask_mono with "(Back H1 H2)") as "$"; [solve_ndisj|].
    rewrite ty_fval_nocell // in Hfv. apply fmap_Some in Hfv as (v' & Hv' & Hfv').
    rewrite Hv in Hfv'. apply fv_lift_inj in Hfv'. subst v'.
    iModIntro. iExists -[x]. iSplitR "Obs"; last first.
    { iApply (proph_obs_impl with "Obs"). by intros π [_ ?]. }
    iSplit; [|done]. rewrite tctx_val_val. iExists D. iSplit; [done|]. iFrame "⧖D".
    iDestruct (ty_gho_own_depth_mono _ d'' (S (S d'')) D D with "Gho") as "[$ _]"; lia.
  Qed.
  (** Opening a unique borrow of the permission of a cell: the borrow is opened with [G1],
      its payload run with [G2], and it can be closed with new contents [y]. *)
  Lemma uniq_cell_open {𝔄} κ (ty: type 𝔄) l' g x ξi di gi ξidx dq tid G1 G2 :
    Timeless G1 → Timeless G2 →
    llft_ctx -∗ uniq_ctx -∗ (G1 &&{↑NllftG}&&> @[κ]) -∗ (G2 &&{↑NllftG}&&> @[κ]) -∗
    (&uniq{κ} (cell_points_to_ty ty)).(ty_gho_own) (l', (g, x), ξi, di, gi, ξidx) dq dq tid -∗
    G1 -∗ G2 -∗ £1 -∗ |={⊤ ∖ ↑advN}=> G2 ∗ ⧗1 ∗
      (κ ⊑ ty_lft (cell_points_to_ty ty)) ∗ ⧖(S di `max` gi) ∗
      (∃ di', ⌜di = S di'⌝ ∗ cell_own ty g x ∗ ▷ ty.(ty_gho_own) x di' gi tid) ∗
      (∀ y d1 g1, ▷ (⧖(S (S d1) `max` g1) ∗ ty.(ty_gho_own) y d1 g1 tid ∗
          cell_own ty g y) -∗ ⧗1 ={↑Nllft}=∗
        uniq_body (cell_points_to_ty ty) (g, y) ξi (S d1) g1 ξidx κ tid l' ∗ G1).
  Proof.
    iIntros (??) "#LFT #UNIQ #Gκ1 #Gκ2 (#Incl & _ & Body) G1 G2 £".
    iMod (uniq_body_acc with "LFT UNIQ Gκ1 Body G1") as "(Pay & ⧗ & Close)"; [solve_ndisj|].
    iMod (uniq_payload_force with "[] G2 £ Pay") as "(G2 & ⧖ & Gho & _)";
      [rewrite /lazyE; solve_ndisj| |].
    { iApply (guards_transitive with "Gκ2 Incl"). }
    destruct di as [|di']; [done|]. iDestruct "Gho" as "[Own Gho]".
    iModIntro. iFrame "G2 ⧗ Incl ⧖". iSplitL "Own Gho"; [iExists di'; by iFrame|].
    iIntros (y d1 g1) "Pay ⧗". iApply ("Close" with "[Pay] ⧗"). iNext.
    iDestruct "Pay" as "($ & Gho & Own)". iFrame "Gho Own".
    rewrite /cbytes bytes_own_unseal. iExists ∅, []. rewrite /greg_map big_sepM_empty.
    iSplit; [by rewrite /heap_mapsto_fbytes|]. iSplit; [|done]. iPureIntro.
    split; [by rewrite /ty_bsize -ty_mty_eq|]. eexists. split; [done|].
    rewrite -ty_mty_eq /=. by apply (frepr_plain _ _ [] (VTuple [])).
  Qed.

  Lemma type_pcell_store_sc_instr {𝔄} `{!NoCell 𝔄} κ (ty: type 𝔄) p q r E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
      +[p ◁ᵥ &shr{κ} (pcell_ty ty.(ty_mty)); q ◁ᵥ &uniq{κ} (cell_points_to_ty ty); r ◁ᵥ ty]
      (Store ScOrd ty.(ty_mty) (ToLit p) r) (λ _, +[])
      (λ post '-[(_, g); bor; y], λ mask π,
        let '(_, (g', _), _, _, _, _) := bor in g = g' ∧
        (uniq_bor_future bor π = (g, vπ y π) → post -[] mask π)).
  Proof.
    iIntros (Alv tid post mask iκs [[l g] [[[[[[l' [g' x]] ξi] di] gi] ξidx] [y []]]])
      "#LFT #TIME #PROPH #UNIQ #E L $ (p & q & r & _) #Obs".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & _)"; [done|].
    iDestruct (Alv with "L E") as "#Alv".
    wp_bind p. iApply (wp_val with "p"). iIntros (w d Hp Hw) "#⧖ #Own".
    simpl in Hw. simplify_eq. wp_pure _.
    wp_bind r. iApply (wp_val with "r"). iIntros (v dy Hr Hv) "#⧖y Gy".
    iDestruct "q" as (vq Hq wq dq [-> Hwq]) "[#⧖q Uniq]".
    destruct d as [|d0]; [done|]. iDestruct "Own" as "(#Gp & _ & _)".
    iApply wp_fupd.
    iApply (wp_cumulative_time_receipt2 with "TIME"); [solve_ndisj|]. iIntros "⧗".
    iDestruct (cumulative_time_receipt_sep 1 1 with "⧗") as "[⧗a ⧗b]".
    set D := S d0 `max` dy.
    iAssert (⧖D)%I as "#⧖D"; [rewrite persistent_time_receipt_sep; by iFrame "⧖ ⧖y"|].
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗a ⧖D") as "[#⧖D1 £]";
      [solve_ndisj|].
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗b ⧖D1") as "[#⧖D2 _]";
      [solve_ndisj|].
    iDestruct (lc_weaken (1 + 2 * (D + 1)) with "£") as "[£1 £2]";
      [rewrite /advance_credits; lia|].
    iMod (llctx_interp_make_guarded with "L") as (γ) "[H1 [H2 [#Gh #Back]]]"; [solve_ndisj|].
    iDestruct (guards_transitive with "Gh Alv") as "#Gκ".
    iMod (uniq_cell_open with "LFT UNIQ Gκ Gκ Uniq H1 H2 £1")
      as "(H2 & ⧗s & #Incl & _ & Own & Close)".
    iDestruct "Own" as (di' ->) "[Own _]". iDestruct "Own" as (fv cs Hfv) "[#Hg Hgd]".
    iDestruct (guards_transitive_right with "Gκ Gp") as "G1".
    iDestruct (lguards_weaken_later _ _ _ _ (D + 1) with "G1") as "G1D"; [lia|].
    iDestruct (guard_pcell_loc_side with "Hg G1D") as "GL"; [apply ty_mty_wf|].
    have Hc : fv_cells fv = [] by eapply ty_fval_nocell_cells.
    iApply (wp_pcell_store_sc_guarded _ l.1 g ty.(ty_mty) cs fv _ v (fractional.half γ) _ (D + 1)
      with "[H2 Hgd £2]"); [solve_ndisj|done|apply ty_mty_wf|by eapply ty_val_wf| |].
    { iSplitR; [done|]. iSplitR; [iIntros "!> $"; by iIntros "$"|]. iFrame "Hg H2 Hgd £2". }
    iIntros "!> [H2 Hgd]".
    iMod (fupd_mask_subseteq (↑Nllft)) as "Hback"; [solve_ndisj|].
    iMod ("Close" $! y D D with "[Gy Hgd] ⧗s") as "[UB H1]".
    { iNext. iSplitR.
      { iApply (persistent_time_receipt_mono with "⧖D2"). lia. }
      iSplitL "Gy"; [by iDestruct (ty_gho_own_depth_mono _ dy dy D D with "Gy") as "[$ _]"; lia|].
      iExists (fv_lift v), cs. iFrame "Hg Hgd". iPureIntro.
      rewrite ty_fval_nocell // Hv //. }
    iMod "Hback" as "_".
    iMod (fupd_mask_mono with "(Back H1 H2)") as "L"; [solve_ndisj|].
    iMod (resolve_uniq_body (cell_points_to_ty ty) (g, y) with
      "LFT PROPH UNIQ TIME Incl E [] L [] UB") as "[#Hrslv [L _]]"; [done|solve_ndisj| | |].
    { iApply guards_refl. }
    { iApply (persistent_time_receipt_mono with "⧖D2"). lia. }
    iModIntro. iExists -[]. iFrame "L". iSplit; [done|].
    iCombine "Hrslv Obs" as "Obs2". iApply (proph_obs_impl with "Obs2").
    intros π (Hres & _ & Hpost). apply Hpost. rewrite /uniq_bor_future /=.
    etrans; [apply (uniq_prvar_app_irrel (𝔄:=trackedₛ (pcellₛ _ * 𝔄)) (g, x) (g, y) ξi π)|].
    by rewrite Hres.
  Qed.

  Lemma type_pcell_mcas_instr {𝔄} `{!NoCell 𝔄} κ (ty: type 𝔄) p q r1 r2 E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
      +[p ◁ᵥ &shr{κ} (pcell_ty ty.(ty_mty)); q ◁ᵥ &uniq{κ} (cell_points_to_ty ty);
        r1 ◁ᵥ ty; r2 ◁ᵥ ty]
      (MCAS ty.(ty_mty) (ToLit p) r1 r2) (λ v, +[v ◁ᵥ bool_ty])
      (λ post '-[(_, g); bor; y1; y2], λ mask π,
        let '(_, (g', x), _, _, _, _) := bor in g = g' ∧
        if bool_decide (ty.(ty_val) x = ty.(ty_val) y1)
        then uniq_bor_future bor π = (g, vπ y2 π) → post -[true] mask π
        else uniq_bor_future bor π = (g, vπ x π) → post -[false] mask π).
  Proof.
    iIntros (Alv tid post mask iκs [[l g] [[[[[[l' [g' x]] ξi] di] gi] ξidx] [y1 [y2 []]]]])
      "#LFT #TIME #PROPH #UNIQ #E L $ (p & q & r1 & r2 & _) #Obs".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & _)"; [done|].
    iDestruct (Alv with "L E") as "#Alv".
    wp_bind p. iApply (wp_val with "p"). iIntros (w d Hp Hw) "#⧖ #Own".
    simpl in Hw. simplify_eq. wp_pure _.
    wp_bind r1. iApply (wp_val with "r1"). iIntros (v1 d1 Hr1 Hv1) "_ _".
    wp_bind r2. iApply (wp_val with "r2"). iIntros (v2 dy Hr2 Hv2) "#⧖y Gy".
    iDestruct "q" as (vq Hq wq dq [-> Hwq]) "[#⧖q Uniq]".
    destruct d as [|d0]; [done|]. iDestruct "Own" as "(#Gp & _ & _)".
    iApply wp_fupd.
    iApply (wp_cumulative_time_receipt2 with "TIME"); [solve_ndisj|]. iIntros "⧗".
    iDestruct (cumulative_time_receipt_sep 1 1 with "⧗") as "[⧗a ⧗b]".
    set D := S d0 `max` dy.
    iAssert (⧖D)%I as "#⧖D"; [rewrite persistent_time_receipt_sep; by iFrame "⧖ ⧖y"|].
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗a ⧖D") as "[#⧖D1 £]";
      [solve_ndisj|].
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗b ⧖D1") as "[#⧖D2 _]";
      [solve_ndisj|].
    iDestruct (lc_weaken (1 + 2 * (D + 1)) with "£") as "[£1 £2]";
      [rewrite /advance_credits; lia|].
    iMod (llctx_interp_make_guarded with "L") as (γ) "[H1 [H2 [#Gh #Back]]]"; [solve_ndisj|].
    iDestruct (guards_transitive with "Gh Alv") as "#Gκ".
    iMod (uniq_cell_open with "LFT UNIQ Gκ Gκ Uniq H1 H2 £1")
      as "(H2 & ⧗s & #Incl & #⧖x & Own & Close)".
    iDestruct "Own" as (di' ->) "[Own Gx]". iDestruct "Own" as (fv cs Hfv) "[#Hg Hgd]".
    iDestruct (guards_transitive_right with "Gκ Gp") as "G1".
    iDestruct (lguards_weaken_later _ _ _ _ (D + 1) with "G1") as "G1D"; [lia|].
    iDestruct (guard_pcell_loc_side with "Hg G1D") as "GL"; [apply ty_mty_wf|].
    have Hfv' := Hfv. rewrite ty_fval_nocell // in Hfv'.
    apply fmap_Some in Hfv' as (vx & Hvx & ->).
    have -> : (Lit $ LitLoc l.1) = (Lit $ LitLoc (l.1 +ₗ (0 + 0)%nat))
      by rewrite /= shift_loc_0_nat.
    iApply (wp_pcell_mcas_sub _ l.1 g ty.(ty_mty) cs g 0 ty.(ty_mty) cs (fv_lift vx) 0
      ty.(ty_mty) vx (fv_lift v2) _ v1 _ v2 (fractional.half γ) _ (D + 1)
      with "[H2 Hgd £2]");
      [solve_ndisj|apply fv_sub_here|apply fv_upd_here|apply ty_mty_wf|by eapply ty_val_wf| |].
    { iSplitR; [done|]. iSplitR; [iIntros "!> $"; by iIntros "$"|].
      iSplitR; [iApply gpath_refl|]. iFrame "Hg H2 Hgd £2". }
    iIntros "!>" (b) "[H2 Hb]".
    iMod (fupd_mask_subseteq (↑Nllft)) as "Hback"; [solve_ndisj|].
    iDestruct "Hb" as "[[[-> %Heq] Hgd]|[[-> %Hne] Hgd]]".
    - subst v1.
      iMod ("Close" $! y2 D D with "[Gy Hgd] ⧗s") as "[UB H1]".
      { iNext. iSplitR.
        { iApply (persistent_time_receipt_mono with "⧖D2"). lia. }
        iSplitL "Gy"; [by iDestruct (ty_gho_own_depth_mono _ dy dy D D with "Gy") as "[$ _]"; lia|].
        iExists (fv_lift v2), cs. iFrame "Hg Hgd". iPureIntro.
        rewrite ty_fval_nocell // Hv2 //. }
      iMod "Hback" as "_".
      iMod (fupd_mask_mono with "(Back H1 H2)") as "L"; [solve_ndisj|].
      iMod (resolve_uniq_body (cell_points_to_ty ty) (g, y2) with
        "LFT PROPH UNIQ TIME Incl E [] L [] UB") as "[#Hrslv [L _]]"; [done|solve_ndisj| | |].
      { iApply guards_refl. }
      { iApply (persistent_time_receipt_mono with "⧖D2"). lia. }
      iModIntro. iExists -[true]. iFrame "L". iSplitR.
      { iSplit; [|done]. rewrite tctx_val_val. iExists D. iSplit; [done|]. by iFrame "⧖D". }
      iCombine "Hrslv Obs" as "Obs2". iApply (proph_obs_impl with "Obs2").
      intros π (Hres & _ & Hpost). rewrite bool_decide_eq_true_2 in Hpost; [|by rewrite Hvx Hv1].
      apply Hpost. rewrite /uniq_bor_future /=.
      etrans; [apply (uniq_prvar_app_irrel (𝔄:=trackedₛ (pcellₛ _ * 𝔄)) (g, x) (g, y2) ξi π)|].
      by rewrite Hres.
    - iMod ("Close" $! x di' gi with "[Gx Hgd] ⧗s") as "[UB H1]".
      { iNext. iFrame "⧖x Gx". iExists (fv_lift vx), cs. by iFrame "Hg Hgd". }
      iMod "Hback" as "_".
      iMod (fupd_mask_mono with "(Back H1 H2)") as "L"; [solve_ndisj|].
      iMod (resolve_uniq_body (cell_points_to_ty ty) (g, x) with
        "LFT PROPH UNIQ TIME Incl E [] L ⧖x UB") as "[#Hrslv [L _]]"; [done|solve_ndisj| |].
      { iApply guards_refl. }
      iModIntro. iExists -[false]. iFrame "L". iSplitR.
      { iSplit; [|done]. rewrite tctx_val_val. iExists D. iSplit; [done|]. by iFrame "⧖D". }
      iCombine "Hrslv Obs" as "Obs2". iApply (proph_obs_impl with "Obs2").
      intros π (Hres & _ & Hpost). rewrite bool_decide_eq_false_2 in Hpost; last first.
      { rewrite Hvx Hv1. congruence. }
      apply Hpost. rewrite /uniq_bor_future /=. by rewrite Hres.
  Qed.
End pcell_atomics.
