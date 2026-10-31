From lrust.lang Require Import heap_cells.
From lrust.typing Require Export type own_bytes value_ctx.
From lrust.typing Require Import programs freeable_util.
From guarding Require Import guard tactics.
From lrust.lifetime Require Import lifetime_full.
Set Default Proof Using "Type".

(** * [PCell] on bytes (§10 step 5 of [design_docs/pcell-multibyte-cells.md])

A [PCell<T>] on the byte layer is a cell group ([lang/heap_cells.v]): a multi-byte cell
whose content has the MiniRust type [m]. Its two halves are two types:
- [pcellb_ty m : type (pcellbₛ m)], the cell itself. Its value is the group [g]; its
  ownership is trivial: the location side of the group (the edges from the locations of
  the cell to its byte-cells) is owned by the parent, as the fancy bytes of [g]
  ([bytes_own_pcellb]). A [pcellb_ty m] has no MiniRust value, so it lives only in memory
  (in a box, behind a reference, as a field).
- [bcell_points_to_ty ty : type (trackedₛ (pcellbₛ (syn_mty 𝔄) * 𝔄))], the permission
  ([PointsTo<T>] of Verus): a ghost value [(g, x)] that owns the dynamic registry entry of
  [g] ([gdyn g fv]), whose fancy value [fv] is the fancy value of [x] ([ty_fval x]; it may
  contain the groups of nested cells), together with the ownership of [x].

These are the byte-layer counterparts of the legacy [pcell_ty] and [cell_points_to_ty] of
[typing/pcell.v]. *)

Implicit Type 𝔄 𝔅: syn_type.

Section pcellb.
  Context `{!typeG Σ}.

  Program Definition pcellb_ty (m: mty) : type (pcellbₛ m) :=
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

  Global Instance pcellb_res_own m : ResOwn (pcellb_ty m).
  Proof. done. Qed.

  Global Instance pcellb_send m : Send (pcellb_ty m).
  Proof.
    intros. split; trivial.
    iIntros. iApply step_fupdN_intro; first done. iNext.
    iExists x, 0%nat. iModIntro. iFrame. simpl.
    replace (d0 + 0)%nat with d0 by lia. iFrame "#". done.
  Qed.

  Global Instance pcellb_sync m : Sync (pcellb_ty m).
  Proof. apply sync_default; [done|]. split; trivial. split; iSplit; done. Qed.

  Lemma pcellb_ty_bsize m : mty_wf m → ty_bsize (pcellb_ty m) = mty_size m.
  Proof. intros. by rewrite /ty_bsize -ty_mty_eq /= decide_True. Qed.

  (** The fancy bytes of a cell are the location side of its group. *)
  Lemma bytes_own_pcellb_ty m l g :
    mty_wf m →
    bytes_own (pcellb_ty m) l g ⊣⊢ ∃ cs, loc_side l g m cs ∗ ⌜length cs = mty_size m⌝.
  Proof. apply bytes_own_pcellb. Qed.
End pcellb.

Section bcell_points_to.
  Context `{!typeG Σ}.

  (** The permission of the group [g] whose content is the value [x] of [ty]: the static
      registry entry of [g] (at the MiniRust type of [ty]) and the dynamic one (at the
      fancy value of [x]). *)
  Definition bcell_own {𝔄} (ty: type 𝔄) (g: positive) (x: ~~𝔄) : iProp Σ :=
    ∃ fv cs, ⌜ty.(ty_fval) x = Some fv⌝ ∗ greg g ty.(ty_mty) cs ∗ gdyn g fv.

  Global Instance bcell_own_timeless {𝔄} (ty: type 𝔄) g x : Timeless (bcell_own ty g x).
  Proof. apply _. Qed.

  Lemma bcell_own_same {𝔄} (ty ty': type 𝔄) g x : bcell_own ty g x ⊣⊢ bcell_own ty' g x.
  Proof. by rewrite /bcell_own (ty_mty_same ty ty') (ty_fval_same ty ty'). Qed.

  Lemma bcell_own_greg {𝔄} (ty: type 𝔄) g x :
    bcell_own ty g x -∗ ∃ cs, greg g ty.(ty_mty) cs.
  Proof. iIntros "(%fv & %cs & _ & $ & _)". Qed.

  Program Definition bcell_points_to_ty {𝔄} (ty: type 𝔄) :
      type (trackedₛ (pcellbₛ (syn_mty 𝔄) * 𝔄)) :=
    {| ty_size := 0%nat;
      ty_lfts := ty.(ty_lfts);
      ty_E := ty.(ty_E);
      ty_gho_own x d g tid :=
        [S(d') := d] bcell_own ty x.1 x.2 ∗ ▷ ty.(ty_gho_own) x.2 d' g tid;
      ty_gho_res x d g tid :=
        [S(d') := d] bcell_own ty x.1 x.2 ∗ ▷ ty.(ty_gho_res) x.2 d' g tid;
      ty_gho_pers x d g tid :=
        [S(d') := d] (∃ cs, greg x.1 ty.(ty_mty) cs) ∗ ▷ ty.(ty_gho_pers) x.2 d' g tid;
      ty_mty := syn_mty _; ty_val := syn_val; ty_mty_eq := eq_refl; ty_val_eq _ := eq_refl;
      ty_fval := syn_fval; ty_fval_eq _ := eq_refl;
      ty_phys _ _ := [];
      (* Structural, as for [own_ptr]. *)
      ty_shr κ x d g tid :=
        ▷ [S(d') := d]
          (@[κ] &&{↑NllftG; g+1}&&> bcell_own ty x.1 x.2) ∗ ty.(ty_shr) κ x.2 d' g tid;
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
    iDestruct "A" as "[A1 A2]". iSplitL "A1"; [by iApply bcell_own_greg|].
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

  Global Instance bcell_points_to_res_own {𝔄} (ty: type 𝔄) :
    ResOwn ty → ResOwn (bcell_points_to_ty ty).
  Proof. move=> ? x [|d] g tid //=. by rewrite res_own. Qed.

  Global Instance bcell_points_to_send {𝔄} (ty: type 𝔄) :
      Send ty → Send (bcell_points_to_ty ty).
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
    - rewrite /bcell_own. by rewrite -!ty_fval_eq (syn_abstract_fval_eq _ _ _ Habs).
    - iPureIntro. simpl. by rewrite Habs.
  Qed.

  Global Instance bcell_points_to_sync {𝔄} (ty: type 𝔄) :
      Sync ty → Sync (bcell_points_to_ty ty).
  Proof.
      move=> HSync tid tid' x d g.
      have EqOwn: ∀ d0 g0, (bcell_points_to_ty ty).(ty_gho_own) x d0 g0 tid ⊣⊢
          (bcell_points_to_ty ty).(ty_gho_own) x d0 g0 tid'.
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
  Lemma bcell_points_to_val {𝔄} (ty: type 𝔄) x :
    (bcell_points_to_ty ty).(ty_val) x = Some (VTuple []).
  Proof. done. Qed.
End bcell_points_to.
