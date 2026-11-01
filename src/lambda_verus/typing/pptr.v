From lrust.typing Require Export type tracked product own shr_bor uniq_bor value_ctx.
From lrust.typing Require Import uniq_util type_context programs ghost.
From guarding Require Import guard tactics.
From lrust.lifetime Require Import lifetime_full.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

(** * Verus-style raw pointers ([PPtr]) and their permissions ([PointsTo])

A [PPtr] is a MiniRust pointer value ([ptr_ty]). Its permission [points_to_ty ty] is a
tracked box of bytes ([tracked_ty (own_bytes (ty_bsize ty) ty)]): a ghost value (the
empty tuple) that owns the bytes of the pointee. The operations take and return
MiniRust values ([◁ᵥ]):
- [typed_pptr_to_own]: a pointer and its permission give a box;
- [typed_pptr_from_own]: a box gives a pointer (the box's pointer value itself) and its
  permission;
- [typed_pptr_borrow], [typed_pptr_borrow_mut]: a pointer and a shared/unique borrow of
  its permission give a shared/unique borrow of the pointee. *)

Section ptr.
  Context `{!typeG Σ}.

  Program Definition ptr_ty : type locₛ := {|
    pt_gho (l: ~~locₛ) _ := True%I ;
  |}%I.
  Next Obligation. move=> *. trivial. Qed.
  Next Obligation. done. Qed.

  Global Instance ptr_copy: Copy ptr_ty.
  Proof.
    split. - apply _. - typeclasses eauto.
    - intros. by apply copy_shr_default.
  Qed.

  Global Instance ptr_send: Send ptr_ty.
  Proof.
    intros. split.
     iIntros. iApply step_fupdN_intro; first done. iNext.
       iExists x, 0%nat. iModIntro. iFrame. simpl.
       replace (d0 + 0)%nat with d0 by lia. iFrame "#". done.
  Qed.

  Lemma ptr_resolve E L : resolve E L ptr_ty (const (const True)).
  Proof. apply resolve_just. Qed.
End ptr.

Section points_to.
  Context `{!typeG Σ}.

  Definition points_to_ty {𝔄} (ty: type 𝔄) := tracked_ty (own_bytes (ty_bsize ty) ty).

  Global Instance points_to_ne {𝔄} : NonExpansive (@points_to_ty 𝔄).
  Proof.
    rewrite /points_to_ty /ty_bsize. move => m ty1 ty2 Eq.
    rewrite (ty_mty_same ty1 ty2). by do 2 f_equiv.
  Qed.

  Global Instance points_to_send {𝔄} (ty: type 𝔄) : Send ty → Send (points_to_ty ty).
  Proof. exact _. Qed.

  Global Instance points_to_sync {𝔄} (ty: type 𝔄) : Sync ty → Sync (points_to_ty ty).
  Proof. exact _. Qed.

  Lemma points_to_resolve {𝔄} E L (ty: type 𝔄) Φ :
    resolve E L ty Φ → resolve E L (points_to_ty ty) (λ '(l, s), Φ s) .
  Proof. move => Rslv. apply tracked_resolve. by eapply own_bytes_resolve. Qed.

  (** A permission is a ghost value: its MiniRust value is the empty tuple. *)
  Lemma points_to_val {𝔄} (ty: type 𝔄) (x: ~~(trackedₛ (at_locₛ 𝔄))) :
    (points_to_ty ty).(ty_val) x = Some (VTuple []).
  Proof. done. Qed.

  Lemma points_to_bsize {𝔄} (ty: type 𝔄) : ty_bsize (points_to_ty ty) = 0.
  Proof. done. Qed.
End points_to.

Section typing.
  Context `{!typeG Σ}.

  Definition PPtr2Own : val := (λ: ["ptr"; "perm"], "ptr")%V.

  Lemma typed_pptr_to_own {𝔄} (perm ptr : path) (ty : type 𝔄) E L I :
    typed_instr E L I +[ptr ◁ᵥ ptr_ty; perm ◁ᵥ points_to_ty ty] (PPtr2Own [ptr; perm])
      (λ v, +[v ◁ᵥ own_bytes (ty_bsize ty) ty])
      (λ post '-[l; (l', x)], λ mask π, l = l' ∧ post -[(l, x)] mask π).
  Proof.
    iIntros (tid postπ mask iκs [l [[l' x] []]]) "#LFT #TIME #PROPH UNIQ E $ $ (Hptr & Hperm & _) #Obs".
    iDestruct "Hptr" as (vp Hp w d [-> Hw]) "[_ _]". simpl in Hw. simplify_eq.
    iDestruct "Hperm" as (vq Hq w' d' [-> _]) "[#Hd' Hown]".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & _)" => //.
    rewrite /PPtr2Own.
    wp_bind ptr. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (? ->).
    wp_bind perm. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (? ->).
    wp_rec.
    iExists -[(l, x)]. iSplitL.
    - iSplit; [|done]. rewrite tctx_val_val. iExists d'. iFrame "Hd' Hown". done.
    - iApply (proph_obs_impl with "Obs"). intros π' Hpost. apply Hpost.
  Qed.

  (** The pointer of the box is the [PPtr]; the operation itself is a no-op that returns
      the (ghost) permission. *)
  Notation PPtrFromOwn := GhostOp (only parsing).

  Lemma typed_pptr_from_own {𝔄} (p : path) (ty : type 𝔄) E L I :
    typed_instr E L I +[p ◁ᵥ own_bytes (ty_bsize ty) ty] PPtrFromOwn
      (λ v, +[p ◁ᵥ ptr_ty; v ◁ᵥ points_to_ty ty])
      (λ post '-[(l, x)], λ mask π, post -[l; (l, x)] mask π).
  Proof.
    iIntros (tid postπ mask iκs [[l x] []]) "#LFT #TIME #PROPH UNIQ E $ $ [Hp _] #Obs".
    iDestruct "Hp" as (vp Hp w d [-> Hw]) "[#Hd Hown]". simpl in Hw. simplify_eq.
    iApply wp_ghost_op. iIntros "!> !>". iExists -[l; (l, x)]. iSplitL.
    - iSplitR; [|iSplitL; [|done]].
      + iExists _. iSplit; [done|]. iExists (VPtr l), d. iSplit; [done|].
        by iFrame "Hd".
      + rewrite tctx_val_val. iExists d. by iFrame "Hd Hown".
    - iApply (proph_obs_impl with "Obs"). intros π' Hpost. apply Hpost.
  Qed.

  Definition PPtrBorrow : val := (λ: ["ptr"; "perm_ref"], "ptr")%V.

  Lemma typed_pptr_borrow {𝔄} κ (ptr perm_ref : path) (ty : type 𝔄) E L I :
    typed_instr E L I +[ptr ◁ᵥ ptr_ty; perm_ref ◁ᵥ &shr{κ} (points_to_ty ty)]
      (PPtrBorrow [ptr; perm_ref]) (λ v, +[v ◁ᵥ &shr{κ} ty])
      (λ post '-[l; (cl, (l', x))], λ mask π, l = l' ∧ post -[(l, x)] mask π).
  Proof.
    iIntros (tid postπ mask iκs [l [[c [l' x]] []]]) "#LFT #TIME #PROPH #UNIQ #E $ $ (Hptr & Hperm & _) #Obs".
    iDestruct "Hptr" as (vp Hp w d [-> Hw]) "[_ _]". simpl in Hw. simplify_eq.
    iDestruct "Hperm" as (vq Hq w' d' [-> _]) "[#Hd' Hshr]".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & _)" => //.
    rewrite /PPtrBorrow.
    wp_bind ptr. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (? ->).
    wp_bind perm_ref. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (? ->).
    iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME Hd'"); [done|].
    iIntros "£ #Hd''".
    destruct d' as [|d']; [done|].
    iDestruct "Hshr" as "(_ & #Hshr0 & #Hpers)". simpl.
    iDestruct (lc_weaken 1 with "£") as "£"; [rewrite /advance_credits; lia|].
    iMod (lc_fupd_elim_later with "£ Hshr0") as "Hshr1".
    destruct d' as [|d'']; [done|].
    iDestruct "Hshr1" as "[#Hpt #Hshr]".
    wp_rec. iModIntro.
    iExists -[(l, x)]. iSplitL.
    - iSplit; [|done]. rewrite tctx_val_val. iExists (S (S (S d''))).
      iSplit; [done|]. iFrame "Hd''". simpl. iSplit; [|iSplit].
      + rewrite /shr_bytes_own. leaf_goal laters to (S (S d'') + 1). { lia. } iFrame "Hpt".
      + iApply (ty_shr_depth_mono with "Hshr"); lia.
      + iApply (bi.laterN_le (S (d'' + 1) + 1) (3 + (d'' + 1))); [lia|].
        rewrite bi.laterN_add. iNext.
        iApply (ty_gho_pers_depth_mono with "Hpers"); lia.
    - iApply (proph_obs_impl with "Obs"). by intros π' [_ Hpost].
  Qed.

  Definition PPtrMutBorrow : val := (λ: ["ptr"; "perm_ref"], "ptr")%V.

  Lemma typed_pptr_borrow_mut {𝔄} κ (ptr perm_ref : path) (ty : type 𝔄) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I +[ptr ◁ᵥ ptr_ty; perm_ref ◁ᵥ &uniq{κ} (points_to_ty ty)]
      (PPtrMutBorrow [ptr; perm_ref]) (λ v, +[v ◁ᵥ &uniq{κ} ty])
      (λ post '-[l; bor], λ mask π, let '(cl, (l', x), ξi, d, g, idx) := bor in l = l' ∧
        ∀ bor',
        uniq_bor_current bor' = snd (uniq_bor_current bor) →
        uniq_bor_future bor' π = snd (uniq_bor_future bor π) →
        (uniq_bor_loc bor') = fst (uniq_bor_current bor) →
        (uniq_bor_loc bor') = fst (uniq_bor_future bor π) →
        post -[bor'] mask π).
  Proof.
    iIntros (Alv tid postπ mask iκs [l [u []]]) "#LFT #TIME #PROPH #UNIQ #E L $ (Hptr & Hperm & _) #Obs".
    iDestruct (Alv with "L E") as "#Alv".
    destruct u as [[[[[c [l' x]] ξi] d] g] ξidx].
    iDestruct "Hptr" as (vp Hp w d0 [-> Hw]) "[_ _]". simpl in Hw. simplify_eq.
    iDestruct "Hperm" as (vq Hq w' d'' [-> _]) "[#Hd' Huniq]".
    iDestruct "Huniq" as "[#Incl [%Hineq UniqBody]]".
    rewrite /PPtrMutBorrow.
    wp_bind ptr. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (? ->).
    wp_bind perm_ref. iApply wp_wand; [by iApply wp_eval_path|]. iIntros (? ->).
    iApply wp_fupd.
    iApply (wp_cumulative_time_receipt2 with "TIME"); [trivial |]; iIntros "⧗".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & _)" => //.
    1: solve_ndisj.
    wp_rec.

    iMod (llctx_interp_make_guarded with "L") as (γ) "[H1 [H2 [#Ghalf #Halfback]]]". { solve_ndisj. }
    iDestruct (guards_transitive with "Ghalf Alv") as "HguardsK".
    change 2 with (1 + 1).
    iDestruct "⧗" as "(⧗ & ⧗')".
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗ Hd'") as "(Hd'' & £)"; [trivial|..].
    iDestruct (lc_weaken (1 + 1) with "£") as "[£1' £f]"; [rewrite /advance_credits; nia|].

    iMod (uniq_body_transform (points_to_ty ty) ty (l, x) x d g ξi ξidx κ tid c l _ _ (pair_with_loc_trackedₛ l) (λ d g, (S d, g)) with "LFT PROPH UNIQ Incl [] [⧗' £1'] HguardsK H1 £f [UniqBody]") as (ζi ζidx) "[#Obs2 [UniqBody H1]]". { set_solver. }
    { iApply guards_refl. }
    { iIntros "[gho _]".
      iMod (lc_fupd_elim_later with "£1' gho") as "gho".
      destruct d as [|d]; [done|].
      iDestruct "gho" as "[pt [free gho]]".
      iModIntro.
      iDestruct (ty_gho_own_depth_mono _ _ _ (S d) g with "gho") as "[gho _]". { lia. } { lia. }
      iFrame "gho". rewrite /cbytes /=. iFrame "pt". iSplitL "⧗'".
      { iIntros (d2 g2) "⧖2".
        iMod (cumulative_persistent_time_receipt with "TIME ⧗' ⧖2") as "#⧖2'".
        { rewrite /lazyE. solve_ndisj. }
        iModIntro. iApply (persistent_time_receipt_mono with "⧖2'"). simpl. lia. }
      iIntros (x2 d2 g2) "(gho & pt2)". iModIntro.
      iFrame "free gho pt2". rewrite /cbytes bytes_own_zst_true //. }
    { iApply (uniq_body_loc with "UniqBody"). intros ?. rewrite /cbytes !bytes_own_zst_true //. }
    iDestruct ("Halfback" with "H1 H2") as "X".
    iMod (fupd_mask_mono with "X") as "L". { set_solver. }
    iModIntro.
    iExists -[(l, x, ζi, d, g, ζidx)].
    iFrame "L". iSplit.
    - iSplit; [|done]. rewrite tctx_val_val. iExists _. iFrame "Hd''".
      iSplit; [done|]. iFrame "Incl UniqBody". iPureIntro; lia.
    - iCombine "Obs Obs2" as "Obs3".
      iApply (proph_obs_impl with "Obs3"). intros π [[_ Ha] Hb].
      apply Ha; intuition.
      + unfold uniq_bor_future. simpl. rewrite Hb. trivial.
      + unfold uniq_bor_future, uniq_bor_loc. simpl. rewrite Hb. trivial.
  Qed.

End typing.

Global Hint Resolve ptr_resolve : lrust_typing.
