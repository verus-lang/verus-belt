From iris.proofmode Require Import proofmode.
From iris.algebra Require Import gmap.
From lrust.typing Require Import lft_contexts.
From lrust.typing Require Import type programs ghost tracked product value_ctx own shr_bor uniq_bor uniq_util.
From lrust.typing Require uniq_util.
From guarding Require Import guard tactics guard_later_pers own_and.
From lrust.typing Require Import ra proph_protocol.
From lrust.lifetime Require Import lifetime_full.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

Section StorageProtocol.

  Context `{!typeG Σ}.
    
  (** The ghost type of storable values, used to put values of a real type [ty] into a
      storage protocol. A value is made storable by sharing it up front, at a fresh
      lifetime [α] (which is part of the storable value), with [ty_share]. The storable
      value holds the token of [α] (to keep the sharing period alive), the resulting
      persistent sharing predicate at [α ⊓ ty_lft ty] (for shared access, see
      [storable_borrow]) and the inheritance of the borrow (to get the ownership
      predicate back after ending [α], see [storable_into_inner]). *)
  Program Definition storable_ty {𝔄} (ty: type 𝔄) : ghost_type (storableₛ 𝔄) := {|
    gt_gho x tid := match x with
        (x0, (d, g), α) =>
          ⌜α ≠ llft_empty⌝ ∗ @[α] ∗ ty.(ty_shr) (α ⊓ ty_lft ty) x0 d g tid ∗
          ([†α] ={↑Nllft}=∗ ▷ ty.(ty_gho_own) x0 d g tid) ∗
          ⧖(S d `max` g) ∗ ty.(ty_gho_pers) x0 d g tid
    end
  |}%I.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.
  Next Obligation. done. Qed.

  Local Lemma storable_ty_gho_change_tid {𝔄} (ty : type 𝔄) tid tid' x :
    Sync ty → (storable_ty ty).(gt_gho) x tid ⊣⊢ (storable_ty ty).(gt_gho) x tid'.
  Proof.
    intros Hsync. destruct x as [[x0 [d0 g0]] α].
    destruct (Hsync tid tid' x0 d0 g0) as [_ [Hgho [Hpers Hshr]]]. simpl.
    by rewrite Hgho Hpers Hshr.
  Qed.

  (* this shouldn't really require Sync, but we would need another layer of step-indexing
    accounting to fix it (similar to how local_inv works). At least in this case,
    it doesn't matter, since the Storage Protocol requires Sync anyway. *)
  Global Instance storable_ty_send {𝔄} (ty : type 𝔄) : Send ty → Sync ty → Send (storable_ty ty).
  Proof. intros Hsend. intros Hsync. split; trivial.
    iIntros (tid tid' x d g G H κs d1 Hineq TG TH) "LFT UNIQ TIME Hg H Gg G gho ⧖".
    iDestruct (storable_ty_gho_change_tid ty tid tid' x with "gho") as "gho".
    iApply step_fupdN_intro; first done. iNext. iModIntro.
    iExists x, 0. iFrame. replace (d1 + 0) with d1 by lia. iFrame.
    done.
  Qed.

  Global Instance storable_ty_sync {𝔄} (ty : type 𝔄) : Sync ty → Sync (storable_ty ty).
  Proof. intros Hsync. apply sync_default; [done|]. split; trivial.
    split; last trivial. by apply storable_ty_gho_change_tid.
  Qed.

  Context {𝔄 ℭ : syn_type}.
  Context {K : Type} `{Countable K}.
  (** The storage protocol, given as a Verus-style [VerusSP] over protocol elements [~~𝔄]
      storing maps from [K] to ghost values [~~ℭ]. *)
  Context `{SP: !VerusSP K (~~ℭ) (~~𝔄)}.
  Context `{G𝔄: !inG Σ (authUR (vra_carUR (vsp_vra K (~~ℭ) (~~𝔄))))}.
  Hypothesis (𝔄_const  : ∀ (x : ~~𝔄) π1 π2 , @vπ 𝔄 x π1 = @vπ 𝔄 x π2).
  Variable (tyC : ghost_type ℭ).

  Set Printing Coercions.
    Program Definition storage_resource_ty : type (ghostₛ (positiveₛ * 𝔄)) :=
    ty_of_gt ({|
          gt_gho v tid :=
            let '(γ, p) := v in
            ⌜ @subseteq coPset _ {[ γ ]} (↑NllftG) ⌝ ∗
            sp_sto γ (λ _ c, tyC.(gt_gho) c tid) ∗ sp_own γ p;
        |}%I : ghost_type (ghostₛ (positiveₛ * 𝔄))).
      Next Obligation.
        move => v.
        unfold indep_interp_of_syn_type in v.
        fold indep_interp_of_syn_type in v.
        destruct v as [γ v].
        move => π1 π2.
        specialize (𝔄_const v π1 π2).
        simpl.
        by f_equal.
      Qed.
      Next Obligation. done. Qed.
      Next Obligation. done. Qed.
      Next Obligation. done. Qed.

  Lemma storage_ty_sync : Send tyC → Sync tyC → Sync storage_resource_ty.
  Proof.
    intros Hsend Hsync. apply sync_default; [done|]. split; first by done. split; last by done.
    simpl. unfold gt_gho. destruct x as [γ p].
    have Hg : ∀ c, tyC.(gt_gho) c tid ⊣⊢ tyC.(gt_gho) c tid'.
    { intros c. destruct (Hsync tid tid' c 0 0) as [H1 [H2 [H3 _]]]. apply H2. }
    rewrite /sp_sto /sp_inv_body. by setoid_rewrite Hg.
  Qed.

  Lemma storage_ty_send : Send tyC → Sync tyC → Send storage_resource_ty.
  Proof.
    intros Hsend. intros Hsync. split; trivial.
    iIntros (tid tid' x d g G H' κs d1 Hineq TG TH) "LFT UNIQ TIME Hg H Gg G gho ⧖".
    have H1 := storage_ty_sync Hsend Hsync.
    destruct (H1 tid tid' x d g) as [H2 [H3 [H4 _]]]. rewrite H3. iIntros.
    iIntros. iApply step_fupdN_intro; first done. iNext. iModIntro.
    iExists x, 0. iFrame. replace (d1 + 0) with d1 by lia. iFrame.
    done.
  Qed.
End StorageProtocol.

(** * Storage protocols on the byte layer

The typing rules of [typing/protocol.v], with the ghost values as MiniRust values ([◁ᵥ],
as in [typing/ra.v]) instead of boxes of size [0], shared references as [&shrb] and
unique borrows as [&uniqb]. The definitions ([storable_ty], [storage_resource_ty]) and the
lemmas of the storage protocol ([typing/proph_protocol.v]) are those of
[typing/protocol.v]. A ghost operation is [GhostOp] (it returns the empty tuple) or
[GhostRet [p]] (it returns the pointer [p], for a result that is a shared reference to a
ghost value: a zero-sized referent is at any location). The operations that return a pair
in [typing/protocol.v] (a box of a pair) here update their first argument and return the
second component. *)

Local Lemma proph_sub_diff' (γ : gname) :
  {[ γ ]} ⊆ (↑NllftG : coPset) → ↑prophN ⊆ (⊤ ∖ {[ γ ]} : coPset).
Proof. intros. assert (↑prophN ## (↑NllftG : coPset)) by solve_ndisj. set_solver. Qed.

Local Lemma proph_sub_diff_NllftG' : ↑prophN ⊆ (⊤ ∖ ↑NllftG : coPset).
Proof. solve_ndisj. Qed.

(** A ghost operation that returns its argument after two steps. *)
Definition GhostRetS : val := (λ: ["p"], Skip ;; "p")%V.

(** A ghost operation that returns a pair of ghost values. *)
Definition GhostOp2 : expr := (Skip ;; MkTuple [MkTuple []; MkTuple []])%E.

Section ghost_vals.
  Context `{!typeG Σ}.

  Lemma wp_ghost_op2 E Φ :
    ▷ ▷ Φ (MLitV (VTuple [VTuple []; VTuple []])) -∗ WP GhostOp2 @ E {{ Φ }}.
  Proof.
    iIntros "HΦ". rewrite /GhostOp2. wp_seq. wp_seq.
    wp_bind (MkTuple []).
    eapply (tac_wp_pure []); [apply (pure_mk_tuple [])|done|tc_solve|simpl; iApply wp_value].
    wp_bind (MkTuple []).
    eapply (tac_wp_pure []); [apply (pure_mk_tuple [])|done|tc_solve|simpl; iApply wp_value].
    eapply (tac_wp_pure []); [apply (pure_mk_tuple [VTuple []; VTuple []])|done|tc_solve|].
    simpl. iApply wp_value. done.
  Qed.

  (** A ghost value (whose MiniRust value is the empty tuple). *)
  Lemma ghost_val_intro {𝔄} tid (ty: type 𝔄) x d :
    ty.(ty_val) x = Some (VTuple []) →
    ⧖d -∗ ty.(ty_gho_own) x d d tid -∗ tctx_elt_interp tid (MLitV (VTuple []) ◁ᵥ ty) x.
  Proof. iIntros (?) "⧖ Gho". rewrite tctx_val_val. iExists d. by iFrame. Qed.

  (** A shared reference to a zero-sized value of a type with the default sharing
      predicate and a trivial persistent predicate, at any location. *)
  Lemma ghost_shr_intro {𝔄} tid κ (ty: type 𝔄) l x d :
    ty_bsize ty = 0 → is_Some (ty.(ty_val) x) → ty_shr_is_default ty →
    (∀ d g, ⊢ ty.(ty_gho_pers) x d g tid) →
    ⧖(S d) -∗ (@[κ] &&{↑NllftG; S d + 1}&&> ty.(ty_gho_own) x d (S d) tid) -∗
    tctx_elt_interp tid (MLitV (VPtr l) ◁ᵥ &shr{κ} ty) (l, x).
  Proof.
    iIntros (Hz Hv Hdef Hpers) "⧖ #G". rewrite tctx_val_val. iExists (S d). iFrame "⧖".
    iSplit; [done|]. rewrite /= /by_succ. iSplit; [by iApply shr_bytes_own_zst|].
    iSplit; [by iApply (ty_shr_default_from_guard ty)|]. iNext. iApply Hpers.
  Qed.

  Lemma ghost_shr_elim {𝔄} tid κ (ty: type 𝔄) l x d :
    ty_shr_is_default ty →
    (&shr{κ} ty).(ty_gho_own) (l, x) (S d) (S d) tid -∗
    (@[κ] &&{↑NllftG; S d + 1}&&> ty.(ty_gho_own) x d (S d) tid).
  Proof.
    iIntros (?) "(_ & #Shr & _)". by iApply (ty_shr_default_to_guard ty with "Shr").
  Qed.
End ghost_vals.

(** ** Storable values *)
Section storable_bytes.
  Context `{!typeG Σ}.

  (** Making a value storable ([storable_new] of [typing/protocol.v]). *)
  Lemma storable_new {𝔄} E L I p (ty : type 𝔄) :
    lctx_lft_alive E L (ty_lft ty) →
    typed_instr E L I +[p ◁ᵥ tracked_ty ty] GhostOp (λ v, +[v ◁ᵥ storable_ty ty])
      (λ post '-[x], λ mask π, ∀ n α, post -[(x, n, α)] mask π).
  Proof.
    iIntros (Alv tid post mask iκs [x1 []]) "#LFT #TIME _ _ #E L $ [p _] Obs".
    iDestruct "p" as (vp Hp w d [-> Hw]) "[#⧖ Gho]".
    iApply wp_fupd. rewrite /GhostOp.
    iApply (wp_cumulative_time_receipt2 with "TIME"); [solve_ndisj|]. iIntros "⧗".
    iDestruct (cumulative_time_receipt_sep 1 1 with "⧗") as "[⧗ _]".
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗ ⧖") as "[#⧖S £]";
      [solve_ndisj|].
    iDestruct (lc_weaken d with "£") as "£"; [unfold advance_credits; nia|].
    iDestruct (Alv with "L E") as "#Alv".
    iDestruct (ty_gho_pers_impl with "Gho") as "#Pers".
    iMod (llftl_begin' with "LFT") as (α) "[α %Hne]"; [solve_ndisj|].
    iMod (llftl_borrow (⊤ ∖ ↑advN) (α ⊓ ty_lft ty) (ty.(ty_gho_own) x1 d d tid)
      with "LFT [Gho]") as "[Bor Inh]"; [solve_ndisj|by iNext|].
    iAssert ((@[α] ∗ llctx_interp L) &&{↑NllftG}&&> @[α ⊓ ty_lft ty])%I as "#Gκ".
    { iApply guards_llft_glb; [iApply guards_weaken_sep_l|].
      iApply (guards_transitive with "[] Alv"). iApply guards_weaken_sep_r. }
    iMod (ty_share with "LFT [] Pers Gκ [$α $L] Bor") as "Upd"; [solve_ndisj| |].
    { iApply llftl_intersect_incl_r. }
    iMod (lc_step_fupdN_elim_later with "£ Upd") as ">[[α $] #Shr]".
    wp_seq. wp_seq.
    eapply (tac_wp_pure []); [apply (pure_mk_tuple [])|done|tc_solve|simpl; iApply wp_value].
    iModIntro. iExists -[(x1, (d, d), α)]. iSplitR "Obs".
    - iSplit; [|done]. iApply (ghost_val_intro _ (storable_ty ty) with "⧖S"); [done|]. simpl.
      iFrame "α Shr Pers". iSplit; [done|]. iSplitL "Inh".
      + iIntros "#Dead". iApply "Inh". rewrite llftl_end_inter. by iLeft.
      + iApply (persistent_time_receipt_mono with "⧖S"). lia.
    - iApply (proph_obs_impl with "Obs"). done.
  Qed.

  (** Getting the value back ([storable_into_inner]). *)
  Lemma storable_into_inner {𝔄} E L I p (ty : type 𝔄) :
    typed_instr E L I +[p ◁ᵥ storable_ty ty] GhostOp (λ v, +[v ◁ᵥ tracked_ty ty])
      (λ post '-[(x, n, α)], λ mask π, post -[x] mask π).
  Proof.
    iIntros (tid post mask iκs [[[x0 [d0 g0]] α] []]) "#LFT #TIME _ _ _ $ $ [p _] Obs".
    iDestruct "p" as (vp Hp w d [-> Hw]) "[_ Gho]".
    iDestruct "Gho" as (Hne) "(α & _ & Inh & #⧖2 & _)".
    iApply wp_fupd. rewrite /GhostOp.
    iApply (wp_cumulative_time_receipt2 with "TIME"); [solve_ndisj|]. iIntros "⧗".
    iDestruct (cumulative_time_receipt_sep 1 1 with "⧗") as "[⧗ _]".
    iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗ ⧖2") as "[#⧖S £]";
      [solve_ndisj|].
    iDestruct (lc_weaken (1 + 1) with "£") as "[£ £']"; [unfold advance_credits; nia|].
    iAssert (|={⊤ ∖ ↑advN}=> ▷ ty.(ty_gho_own) x0 d0 g0 tid)%I with "[α Inh £]" as ">Gho".
    { iMod (fupd_mask_subseteq (↑Nllft)) as "Close"; [solve_ndisj|].
      iMod (llftl_end' with "LFT α") as "End"; [done|].
      iMod (lc_fupd_elim_later with "£ End") as "End".
      iMod "End" as "#Dead".
      iMod ("Inh" with "Dead") as "Gho".
      by iMod "Close" as "_". }
    iMod (lc_fupd_elim_later with "£' Gho") as "Gho".
    wp_seq. wp_seq.
    eapply (tac_wp_pure []); [apply (pure_mk_tuple [])|done|tc_solve|simpl; iApply wp_value].
    iModIntro. iExists -[x0]. iSplitR "Obs".
    - iSplit; [|done]. rewrite tctx_val_val. iExists (S d0 `max` g0 + 1). iSplit; [done|].
      iFrame "⧖S". iDestruct (ty_gho_own_depth_mono with "Gho") as "[$ _]"; lia.
    - iApply (proph_obs_impl with "Obs"). done.
  Qed.
End storable_bytes.

Section storable_borrow.
  Context `{!typeG Σ}.

  (** Shared access to a stored value ([storable_borrow]). *)
  Lemma storable_borrow {𝔄} κ E L I p (ty : type 𝔄) :
    lctx_lft_alive E L κ → lctx_lft_incl E L κ (ty_lft ty) →
    typed_instr E L I +[p ◁ᵥ &shr{κ} (storable_ty ty)] (GhostRetS [p])
      (λ v, +[v ◁ᵥ &shr{κ} (tracked_ty ty)])
      (λ post '-[(l, (x, n, α))], λ mask π, post -[(l, x)] mask π).
  Proof.
    iIntros (Alv Incl tid post mask iκs [[l [[x0 [d0 g0]] α]] []])
      "#LFT #TIME _ _ #E L $ [p _] Obs".
    iDestruct "p" as (vp Hp w d [-> Hw]) "[#⧖ #Own]". simpl in Hw. simplify_eq.
    destruct d as [|d]; [done|].
    iDestruct (ghost_shr_elim _ _ (storable_ty ty) with "Own") as "#gho"; [done|].
    iDestruct (Alv with "L E") as "#Alv".
    iDestruct (Incl with "L E") as "#Incl".
    iDestruct (guards_transitive_right with "Alv gho") as "LG".
    wp_bind p. iApply (wp_wand with "[]"); [by iApply wp_eval_path|]. iIntros (? ->).
    rewrite /GhostRetS. wp_rec. wp_bind Skip. iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|]. iIntros "£ _".
    iDestruct (lc_weaken (S d + 1) with "£") as "£"; [unfold advance_credits; nia|].
    iAssert (|={⊤ ∖ ↑advN}=> llctx_interp L ∗ ty.(ty_shr) (α ⊓ ty_lft ty) x0 d0 g0 tid ∗
      ⧖(S d0 `max` g0) ∗ ty.(ty_gho_pers) x0 d0 g0 tid)%I with "[L £]"
      as ">($ & #Shr & #⧖2 & #Pers)".
    { iMod (guards_open_later with "LG L") as "Opened"; [solve_ndisj|].
      iMod (lc_fupd_elim_laterN with "£ Opened") as ">[Inner back]".
      iDestruct "Inner" as "(%Hne & α & #Shr & Inh & #⧖2 & #Pers)".
      iMod ("back" with "[α Inh]") as "$". { by iFrame "α Shr Inh ⧖2 Pers". }
      by iFrame "Shr ⧖2 Pers". }
    wp_seq. iModIntro.
    iAssert (@[κ] &&{↑NllftG; S d + 1}&&> @[α ⊓ ty_lft ty])%I as "#Gκ".
    { iApply guards_llft_glb.
      - iApply (guards_transitive_left with "gho"). leaf_by_sep.
        iIntros "(% & $ & R)". iIntros "α". by iFrame.
      - leaf_goal laters to 0. { lia. } iFrame "Incl". }
    iDestruct (ty_shr_lft_mono with "Gκ Shr") as "#Shrκ".
    iApply wp_fupd.
    iApply (wp_cumulative_time_receipt_linear with "TIME ⧖2"); [done|]. iIntros "⧗".
    iMod (cumulative_persistent_time_receipt with "TIME ⧗ ⧖") as "#⧖S"; [solve_ndisj|].
    wp_seq. iModIntro. iExists -[(l, x0)]. iFrame "Obs". iSplit; [|done].
    rewrite tctx_val_val. iExists _. iFrame "⧖S". iSplit; [done|].
    replace (S (S (S d0 `max` g0)) + S d) with (S (S (S d0 `max` g0) + S d)) by lia.
    rewrite /= /by_succ. iSplit; [iApply shr_bytes_own_zst; [by rewrite /ty_bsize -ty_mty_eq|done]|].
    iSplit.
    - iApply (ty_shr_depth_mono with "Shrκ"); lia.
    - iApply (bi.laterN_le 0); [lia|]. simpl.
      iApply (ty_gho_pers_depth_mono with "Pers"); lia.
  Qed.
End storable_borrow.

(** ** Storage protocols *)
Section StorageProtocol_bytes.
  Context `{!typeG Σ}.
  Context {𝔄 ℭ : syn_type}.
  Context {K : Type} `{Countable K}.
  Context `{SP: !VerusSP K (~~ℭ) (~~𝔄)}.
  Context `{G𝔄: !inG Σ (authUR (vra_carUR (vsp_vra K (~~ℭ) (~~𝔄))))}.
  Hypothesis (𝔄_const  : ∀ (x : ~~𝔄) π1 π2 , @vπ 𝔄 x π1 = @vπ 𝔄 x π2).
  Variable (tyC : ghost_type ℭ).

  Local Notation srty := (storage_resource_ty 𝔄_const tyC).

  Local Lemma sr_val_intro tid γ a d :
    ⧖d -∗ ⌜{[γ]} ⊆ (↑NllftG : coPset)⌝ -∗ sp_sto γ (λ _ c, tyC.(gt_gho) c tid) -∗ sp_own γ a -∗
    tctx_elt_interp tid (MLitV (VTuple []) ◁ᵥ srty) (γ, a).
  Proof. iIntros "⧖ % Sto Own". iApply (ghost_val_intro _ srty with "⧖"); [done|]. by iFrame. Qed.

  Local Lemma tracked_val_intro tid c d :
    ⧖d -∗ tyC.(gt_gho) c tid -∗ tctx_elt_interp tid (MLitV (VTuple []) ◁ᵥ tracked_ty tyC) c.
  Proof. iIntros "⧖ Gho". iApply (ghost_val_intro _ (tracked_ty tyC) with "⧖ Gho"). done. Qed.

  Local Lemma val_path_intro {𝔅} tid p (ty: type 𝔅) x v d :
    eval_path p = Some (MLitV v) → ty.(ty_val) x = Some v →
    ⧖d -∗ ty.(ty_gho_own) x d d tid -∗ tctx_elt_interp tid (p ◁ᵥ ty) x.
  Proof.
    iIntros (Hp Hv) "⧖ Gho". iExists _. iSplit; [done|]. iExists v, d. by iFrame.
  Qed.

  Notation "SP_Alloc: p s" := GhostOp (at level 102, p,s at level 1): expr_scope.

  Lemma typed_sp_alloc (k : K) (p s : path) (tyA : type 𝔄) E L I :
    typed_instr E L I +[p ◁ᵥ ghost_ty tyA; s ◁ᵥ tracked_ty tyC] (SP_Alloc: p s)
      (λ v, +[v ◁ᵥ srty])
      (λ post '-[a; c], λ mask π, vsp_rel a {[ k := c ]} π ∧ ∀ γ, post -[(γ, a)] mask π).
  Proof.
    iIntros (tid post mask iκs [a [c []]]) "_ _ #PROPH _ _ $ $ (p & s & _) #Obs".
    iDestruct "p" as (vp Hp w d [-> Hw]) "[#⧖ _]".
    iDestruct "s" as (vs Hs w' d' [-> Hw']) "[_ HghoC]".
    iMod (sp_alloc_ns ⊤ NllftG a {[ k := c ]} (λ _ c, tyC.(gt_gho) c tid)
      with "PROPH [] [HghoC]") as "(%γ & %Hγ & Hsto & Htok)"; first solve_ndisj.
    { iApply (proph_obs_impl with "Obs"). by intros π [? _]. }
    { by rewrite big_sepM_singleton. }
    iApply wp_ghost_op. iIntros "!> !>". iExists -[(γ, a)].
    iSplitL; [iSplit; [|done]|iApply (proph_obs_impl with "Obs"); by intros π [_ ?]].
    iApply (sr_val_intro with "⧖ [] Hsto Htok"). iPureIntro. set_solver.
  Qed.

  Notation "SP_Join: a b" := GhostOp (at level 102, a,b at level 1): expr_scope.

  Lemma typed_sp_join (p1 p2 : path) E L I :
    typed_instr E L I +[p1 ◁ᵥ srty; p2 ◁ᵥ srty] (SP_Join: p1 p2) (λ v, +[v ◁ᵥ srty])
      (λ post '-[(γ1, a1); (γ2, a2)], λ mask π,
        γ1 = γ2 ∧ post -[(γ1, vsp_op a1 a2)] mask π).
  Proof.
    iIntros (tid post mask iκs [[γ1 a1] [[γ2 a2] []]]) "_ _ #PROPH _ _ $ $ (p1 & p2 & _) #Obs".
    iMod (proph_obs_sat with "PROPH Obs") as "(%π & <- & _)"; [done|].
    iDestruct "p1" as (vp1 Hp1 w1 d1 [-> Hw1]) "[#⧖ (%Hγ & #Hsto & Hown1)]".
    iDestruct "p2" as (vp2 Hp2 w2 d2 [-> Hw2]) "[_ (_ & _ & Hown2)]".
    iAssert (sp_own γ1 (vsp_op a1 a2)) with "[Hown1 Hown2]" as "Hown".
    { rewrite sp_own_op. iFrame. }
    iApply wp_ghost_op. iIntros "!> !>". iExists -[(γ1, vsp_op a1 a2)].
    iSplitL; [iSplit; [by iApply (sr_val_intro with "⧖ [] Hsto Hown")|done]|].
    iApply (proph_obs_impl with "Obs"). by intros π' [_ ?].
  Qed.

  Notation "SP_Split: p p1 p2" := GhostOp (at level 102, p, p1, p2 at level 1): expr_scope.

  (** Splitting: [self] keeps the first part, the result is the second part. *)
  Lemma typed_sp_split (self p1 p2 : path) (ty : type 𝔄) E L I :
    typed_instr E L I +[self ◁ᵥ srty; p1 ◁ᵥ ghost_ty ty; p2 ◁ᵥ ghost_ty ty]
      (SP_Split: self p1 p2) (λ v, +[self ◁ᵥ srty; v ◁ᵥ srty])
      (λ post '-[(γ, x); x1; x2], λ mask π,
        x = vsp_op x1 x2 ∧ post -[(γ, x1); (γ, x2)] mask π).
  Proof.
    iIntros (tid post mask iκs [[γ x] [x1 [x2 []]]]) "_ _ #PROPH _ _ $ $ (p & _ & _ & _) #Obs".
    iMod (proph_obs_sat with "PROPH Obs") as "(%π & -> & _)"; [done|].
    iDestruct "p" as (vp Hp w d [-> Hw]) "[#⧖ (%Hγ & #Hsto & Hown)]". simpl in Hw. simplify_eq.
    rewrite sp_own_op. iDestruct "Hown" as "[Hown1 Hown2]".
    iApply wp_ghost_op. iIntros "!> !>". iExists -[(γ, x1); (γ, x2)].
    iSplitL; [|iApply (proph_obs_impl with "Obs"); by intros π' [_ ?]].
    iSplitL "Hown1"; [|iSplit; [by iApply (sr_val_intro with "⧖ [] Hsto Hown2")|done]].
    iApply (val_path_intro _ _ srty with "⧖"); [done|done|]. by iFrame "Hsto Hown1".
  Qed.

  Notation "SP_Exchange: p1 p2 p3 p4" := GhostOp (at level 102, p1,p2,p3,p4 at level 1): expr_scope.

  (** Exchanging: [p1] holds the new protocol element, the result is the new stored
      value. *)
  Lemma typed_sp_exchange (k : K) (p1 p2 p3 p4 : path) (tyA : type 𝔄) E L I :
    typed_instr E L I
      +[p1 ◁ᵥ srty; p2 ◁ᵥ tracked_ty tyC; p3 ◁ᵥ ghost_ty tyA; p4 ◁ᵥ ghost_ty tyC]
      (SP_Exchange: p1 p2 p3 p4) (λ v, +[p1 ◁ᵥ srty; v ◁ᵥ tracked_ty tyC])
      (λ post '-[(γ, p); s; new_p; new_s], λ mask π,
        vsp_exchanges p {[ k := s ]} new_p {[ k := new_s ]} π ∧
        post -[(γ, new_p); new_s] mask π).
  Proof.
    iIntros (tid post mask iκs [[γ p] [s [new_p [new_s []]]]])
      "_ _ #PROPH _ _ $ $ (Hp & Hs & _ & _ & _) #Obs".
    iDestruct "Hp" as (vp Hp w d [-> Hw]) "[#⧖ (%Hγ & #Hsto & Hown)]". simpl in Hw. simplify_eq.
    iDestruct "Hs" as (vs Hs w' d' [-> Hw']) "[_ HghoC]".
    iMod (sp_exchange p new_p {[ k := s ]} {[ k := new_s ]} γ _ ⊤ ltac:(set_solver)
      (proph_sub_diff' γ Hγ) with "PROPH Hsto [] Hown [HghoC]") as "(Hown & HghoC)".
    { iApply (proph_obs_impl with "Obs"). by intros π [? _]. }
    { iNext. by rewrite big_sepM_singleton. }
    iApply wp_ghost_op. iIntros "!> !>". rewrite big_sepM_singleton.
    iExists -[(γ, new_p); new_s].
    iSplitL; [|iApply (proph_obs_impl with "Obs"); by intros π' [_ ?]].
    iSplitL "Hown"; [|iSplit; [by iApply (tracked_val_intro with "⧖ HghoC")|done]].
    iApply (val_path_intro _ _ srty with "⧖"); [done|done|]. by iFrame "Hsto Hown".
  Qed.

  Notation "SP_Deposit: p1 p2 p3" := GhostOp (at level 102, p1,p2,p3 at level 1): expr_scope.

  Lemma typed_sp_deposit (k : K) (p1 p2 p3 : path) (tyA : type 𝔄) E L I :
    typed_instr E L I +[p1 ◁ᵥ srty; p2 ◁ᵥ tracked_ty tyC; p3 ◁ᵥ ghost_ty tyA]
      (SP_Deposit: p1 p2 p3) (λ v, +[v ◁ᵥ srty])
      (λ post '-[(γ, p); s; new_p], λ mask π,
        vsp_deposits p {[ k := s ]} new_p π ∧ post -[(γ, new_p)] mask π).
  Proof.
    iIntros (tid post mask iκs [[γ p] [s [new_p []]]])
      "_ _ #PROPH _ _ $ $ (Hp & Hs & _ & _) #Obs".
    iDestruct "Hp" as (vp Hp w d [-> Hw]) "[#⧖ (%Hγ & #Hsto & Hown)]".
    iDestruct "Hs" as (vs Hs w' d' [-> Hw']) "[_ HghoC]".
    iMod (sp_deposit p new_p {[ k := s ]} γ _ ⊤ ltac:(set_solver)
      (proph_sub_diff' γ Hγ) with "PROPH Hsto [] Hown [HghoC]") as "Hown".
    { iApply (proph_obs_impl with "Obs"). by intros π [? _]. }
    { iNext. by rewrite big_sepM_singleton. }
    iApply wp_ghost_op. iIntros "!> !>". iExists -[(γ, new_p)].
    iSplitL; [iSplit; [by iApply (sr_val_intro with "⧖ [] Hsto Hown")|done]|].
    iApply (proph_obs_impl with "Obs"). by intros π' [_ ?].
  Qed.

  Notation "SP_Withdraw: p1 p2 p3" := GhostOp (at level 102, p1,p2,p3 at level 1): expr_scope.

  Lemma typed_sp_withdraw (k : K) (p1 p2 p3 : path) (tyA : type 𝔄) E L I :
    typed_instr E L I +[p1 ◁ᵥ srty; p2 ◁ᵥ ghost_ty tyA; p3 ◁ᵥ ghost_ty tyC]
      (SP_Withdraw: p1 p2 p3) (λ v, +[p1 ◁ᵥ srty; v ◁ᵥ tracked_ty tyC])
      (λ post '-[(γ, p); new_p; new_s], λ mask π,
        vsp_withdraws p new_p {[ k := new_s ]} π ∧ post -[(γ, new_p); new_s] mask π).
  Proof.
    iIntros (tid post mask iκs [[γ p] [new_p [new_s []]]])
      "_ _ #PROPH _ _ $ $ (Hp & _ & _ & _) #Obs".
    iDestruct "Hp" as (vp Hp w d [-> Hw]) "[#⧖ (%Hγ & #Hsto & Hown)]". simpl in Hw. simplify_eq.
    iMod (sp_withdraw p new_p {[ k := new_s ]} γ _ ⊤ ltac:(set_solver)
      (proph_sub_diff' γ Hγ) with "PROPH Hsto [] Hown") as "[Hown HghoC]".
    { iApply (proph_obs_impl with "Obs"). by intros π [? _]. }
    iApply wp_ghost_op. iIntros "!> !>". rewrite big_sepM_singleton.
    iExists -[(γ, new_p); new_s].
    iSplitL; [|iApply (proph_obs_impl with "Obs"); by intros π' [_ ?]].
    iSplitL "Hown"; [|iSplit; [by iApply (tracked_val_intro with "⧖ HghoC")|done]].
    iApply (val_path_intro _ _ srty with "⧖"); [done|done|]. by iFrame "Hsto Hown".
  Qed.

  Notation "SP_Update: p1 p2" := GhostOp (at level 102, p1,p2 at level 1): expr_scope.

  Lemma typed_sp_update (p1 p2 : path) (tyA : type 𝔄) E L I :
    typed_instr E L I +[p1 ◁ᵥ srty; p2 ◁ᵥ ghost_ty tyA] (SP_Update: p1 p2)
      (λ v, +[v ◁ᵥ srty])
      (λ post '-[(γ, p); new_p], λ mask π, vsp_updates p new_p π ∧ post -[(γ, new_p)] mask π).
  Proof.
    iIntros (tid post mask iκs [[γ p] [new_p []]]) "_ _ #PROPH _ _ $ $ (Hp & _ & _) #Obs".
    iDestruct "Hp" as (vp Hp w d [-> Hw]) "[#⧖ (%Hγ & #Hsto & Hown)]".
    iMod (sp_update p new_p γ _ ⊤ ltac:(set_solver)
      (proph_sub_diff' γ Hγ) with "PROPH Hsto [] Hown") as "Hown".
    { iApply (proph_obs_impl with "Obs"). by intros π [? _]. }
    iApply wp_ghost_op. iIntros "!> !>". iExists -[(γ, new_p)].
    iSplitL; [iSplit; [by iApply (sr_val_intro with "⧖ [] Hsto Hown")|done]|].
    iApply (proph_obs_impl with "Obs"). by intros π' [_ ?].
  Qed.

  Notation "SP_ExchangeNonDet: p1 p2 p3" := GhostOp (at level 102, p1,p2,p3 at level 1): expr_scope.

  Lemma typed_sp_exchange_nondeterministic (k : K) (p1 p2 p3 : path) (n : nat)
      (ty : type (vecₛ (𝔄 * ℭ) n)) E L I :
    typed_instr E L I +[p1 ◁ᵥ srty; p2 ◁ᵥ tracked_ty tyC; p3 ◁ᵥ ghost_ty ty]
      (SP_ExchangeNonDet: p1 p2 p3) (λ v, +[p1 ◁ᵥ srty; v ◁ᵥ tracked_ty tyC])
      (λ post '-[(γ, p); s; new_pss], λ mask π,
        vsp_exchanges_nondeterministic p {[ k := s ]}
          (λ new_p new_b, ∃ new_s, new_b = {[ k := new_s ]} ∧ (new_p, new_s) ∈ vec_to_list new_pss) ∧
        Forall (λ '(new_p, new_s), post -[(γ, new_p); new_s] mask π) (vec_to_list new_pss)).
  Proof.
    iIntros (tid post mask iκs [[γ p] [s [new_pss []]]])
      "_ _ #PROPH _ _ $ $ (Hp & Hs & _ & _) #Obs".
    iDestruct "Hp" as (vp Hp w d [-> Hw]) "[#⧖ (%Hγ & #Hsto & Hown)]". simpl in Hw. simplify_eq.
    iDestruct "Hs" as (vs Hs w' d' [-> Hw']) "[_ HghoC]".
    iMod (proph_obs_sat with "PROPH Obs") as "(%π & %exchng & _)"; [done|].
    iMod (sp_exchange_nondeterministic p {[ k := s ]} _ γ _ ⊤ exchng ltac:(set_solver)
      (proph_sub_diff' γ Hγ) with "PROPH Hsto Hown [HghoC]")
      as "(%new_p & %new_b & %Hin & Hown & HghoC)".
    { iNext. by rewrite big_sepM_singleton. }
    destruct Hin as (new_s & -> & Hin).
    iApply wp_ghost_op. iIntros "!> !>". rewrite big_sepM_singleton.
    iExists -[(γ, new_p); new_s].
    iSplitL; last first.
    { iApply (proph_obs_impl with "Obs"). intros π' (_ & Hpost).
      rewrite Forall_forall in Hpost. by apply (Hpost (new_p, new_s)). }
    iSplitL "Hown"; [|iSplit; [by iApply (tracked_val_intro with "⧖ HghoC")|done]].
    iApply (val_path_intro _ _ srty with "⧖"); [done|done|]. by iFrame "Hsto Hown".
  Qed.

  (** The ownership of a shared reference to a storage resource: a guard of its parts. *)
  Local Lemma sr_shr_elim tid κ l γ p d :
    (&shr{κ} srty).(ty_gho_own) (l, (γ, p)) (S d) (S d) tid -∗
    (@[κ] &&{↑NllftG; S d + 1}&&> (⌜{[γ]} ⊆ (↑NllftG : coPset)⌝ ∗
       sp_sto γ (λ _ c, tyC.(gt_gho) c tid)) ∗ sp_own γ p).
  Proof.
    iIntros "Own". iDestruct (ghost_shr_elim _ _ srty with "Own") as "#G"; [done|].
    iSimpl in "G". by rewrite bi.sep_assoc.
  Qed.

  (** The persistent part of a guarded storage resource, with credits. *)
  Local Lemma sr_shr_sto L κ γ p n G tid :
    ↑NllftG ⊆ G →
    llctx_interp L -∗ (llctx_interp L &&{↑NllftG}&&> @[κ]) -∗
    (@[κ] &&{↑NllftG; n}&&> (⌜{[γ]} ⊆ (↑NllftG : coPset)⌝ ∗
       sp_sto γ (λ _ c, tyC.(gt_gho) c tid)) ∗ sp_own γ p) -∗ £n ={G}=∗
    llctx_interp L ∗ ⌜{[γ]} ⊆ (↑NllftG : coPset)⌝ ∗ sp_sto γ (λ _ c, tyC.(gt_gho) c tid).
  Proof.
    iIntros (?) "L #Alv #Shr £". iDestruct (guards_weaken_rhs_sep_l with "Shr") as "Shr1".
    iDestruct (guards_transitive_right with "Alv Shr1") as "G1".
    iMod (guards_extract_persistent_later _ _
      (⌜{[γ]} ⊆ (↑NllftG : coPset)⌝ ∗ sp_sto γ (λ _ c, tyC.(gt_gho) c tid))%I G (↑NllftG) _
      ltac:(apply _) ltac:(done) with "G1 L []") as "Upd"; [iIntros "$"|].
    iMod (lc_fupd_elim_laterN with "£ Upd") as ">[$ [$ $]]". done.
  Qed.

  Local Lemma sr_shr_own_intro tid κ l γ p d :
    ⧖(S d) -∗
    (@[κ] &&{↑NllftG; S d + 1}&&> (⌜{[γ]} ⊆ (↑NllftG : coPset)⌝ ∗
       sp_sto γ (λ _ c, tyC.(gt_gho) c tid)) ∗ sp_own γ p) -∗
    tctx_elt_interp tid (MLitV (VPtr l) ◁ᵥ &shr{κ} srty) (l, (γ, p)).
  Proof.
    iIntros "⧖ #G". iApply (ghost_shr_intro _ _ srty with "⧖");
      [by rewrite /ty_bsize -ty_mty_eq|done|done|done|]. iSimpl. by rewrite -bi.sep_assoc.
  Qed.

  Notation "SP_Guard: p1 p2" := (GhostRet [p1])%E (at level 102, p1,p2 at level 1): expr_scope.

  Lemma typed_sp_guard (k : K) (p1 p2 : path) E L I κ :
    lctx_lft_alive E L κ →
    typed_instr E L I +[p1 ◁ᵥ &shr{κ} srty; p2 ◁ᵥ ghost_ty tyC] (SP_Guard: p1 p2)
      (λ v, +[v ◁ᵥ &shr{κ} (tracked_ty tyC)])
      (λ post '-[(l, (γ, p)); s], λ mask π, vsp_guards p {[ k := s ]} ∧ post -[(l, s)] mask π).
  Proof.
    iIntros (Alv tid post mask iκs [[l [γ p]] [s []]]) "_ #TIME #PROPH _ #E L $ (p1 & _ & _) #Obs".
    iMod (proph_obs_sat with "PROPH Obs") as "(%π & %guard & _)"; [done|].
    iDestruct "p1" as (vp1 Hp1 w1 d [-> Hw1]) "[#⧖ #Own]". simpl in Hw1. simplify_eq.
    destruct d as [|d]; [done|].
    iDestruct (sr_shr_elim with "Own") as "#Hshr".
    iDestruct (Alv with "L E") as "#Alv".
    iApply wp_fupd. wp_bind p1. iApply (wp_wand with "[]"); [by iApply wp_eval_path|].
    iIntros (? ->).
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|]. iIntros "£ #⧖S".
    iDestruct (lc_weaken (S d + 1) with "£") as "£"; [rewrite /advance_credits; nia|].
    wp_rec.
    iMod (sr_shr_sto with "L Alv Hshr £") as "($ & %Hγ & #Hsto)"; [solve_ndisj|].
    iPoseProof (sp_guard _ _ _ {[ γ ]} with "Hsto") as "Hguard'"; [done|set_solver|].
    iPoseProof (guards_later_absorb_1 with "Hguard'") as "#Hguard''".
    iPoseProof (guards_weaken_mask _ (↑NllftG) with "Hguard''") as "Hguard"; [set_solver|].
    iPoseProof (guards_weaken_rhs_sep_r with "Hshr") as "#Hshr'".
    iDestruct (guards_transitive_additive with "Hshr' Hguard") as "Hshr1".
    iModIntro. iExists -[(l, s)]. iSplitL; [iSplit; [|done]|].
    - iApply (ghost_shr_intro _ _ (tracked_ty tyC) with "⧖S");
        [by rewrite /ty_bsize -ty_mty_eq|done|done|done|].
      iApply (lguards_weaken_later with "[Hshr1]"); [|by rewrite big_sepM_singleton]. lia.
    - iApply (proph_obs_impl with "Obs"). by intros π' [_ ?].
  Qed.

  Notation "SP_JoinSharedDet: p1 p2 p3" := (GhostRet [p1])%E
    (at level 102, p1, p2, p3 at level 1): expr_scope.

  Lemma typed_sp_join_shared_to_target κ (p1 p2 p3 : path) (ty : type 𝔄) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
      +[p1 ◁ᵥ &shr{κ} srty; p2 ◁ᵥ &shr{κ} srty; p3 ◁ᵥ ghost_ty ty]
      (SP_JoinSharedDet: p1 p2 p3) (λ v, +[v ◁ᵥ &shr{κ} srty])
      (λ post '-[(l1, (γ1, x1)); (_, (γ2, x2)); y], λ mask π, γ1 = γ2 ∧
        (∀ p, vsp_incl x1 p → vsp_incl x2 p → vsp_incl y p) ∧ post -[(l1, (γ1, y))] mask π).
  Proof.
    iIntros (Alv tid post mask iκs [[l1 [γ1 x1]] [[l2 [γ2 x2]] [y []]]])
      "_ #TIME #PROPH _ #E L $ (p1 & p2 & _ & _) #Obs".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & %Hy & _)"; [done|].
    iDestruct "p1" as (vp1 Hp1 w1 d1 [-> Hw1]) "[#⧖1 #Own1]". simpl in Hw1. simplify_eq.
    iDestruct "p2" as (vp2 Hp2 w2 d2 [-> Hw2]) "[#⧖2 #Own2]".
    destruct d1 as [|d1]; [done|]. destruct d2 as [|d2]; [done|].
    iDestruct (sr_shr_elim with "Own1") as "#Shr1".
    iDestruct (sr_shr_elim with "Own2") as "#Shr2".
    iDestruct (Alv with "L E") as "#Alv".
    set D := d1 `max` d2.
    iAssert (⧖(S D))%I as "#⧖D".
    { rewrite /D Nat.succ_max_distr persistent_time_receipt_sep. by iFrame "⧖1 ⧖2". }
    iApply wp_fupd. wp_bind p1. iApply (wp_wand with "[]"); [by iApply wp_eval_path|].
    iIntros (? ->).
    iApply (wp_persistent_time_receipt with "TIME ⧖D"); [done|]. iIntros "£ _".
    iDestruct (lc_weaken (S D + 1) with "£") as "£"; [rewrite /advance_credits; nia|].
    wp_rec.
    iDestruct (lguards_weaken_later _ _ _ _ (S D + 1) with "Shr1") as "Shr1'"; [lia|].
    iDestruct (lguards_weaken_later _ _ _ _ (S D + 1) with "Shr2") as "Shr2'"; [lia|].
    iMod (sr_shr_sto with "L Alv Shr1' £") as "($ & %Hγ & #Hsto)"; [solve_ndisj|].
    iPoseProof (guards_weaken_rhs_sep_r with "Shr1'") as "#Shr1''".
    iPoseProof (guards_weaken_rhs_sep_r with "Shr2'") as "#Shr2''".
    iPoseProof (guards_and_point _ _ _ (sp_own γ1 y) with "Shr1'' Shr2''") as "Shr3".
    { apply point_prop_p_own. }
    { by iApply sp_own_and_specific. }
    iPoseProof (guards_include_pers (⌜ {[γ1]} ⊆ ↑NllftG ⌝ ∗ (sp_sto _ _)) with "[] Shr3")
      as "Shr4".
    { by iSplit. }
    iModIntro. iExists -[(l1, (γ1, y))]. iSplitL.
    - iSplit; [|done]. iApply (sr_shr_own_intro with "⧖D").
      by rewrite (bi.sep_comm (sp_own γ1 y)).
    - iApply (proph_obs_impl with "Obs"). by intros π' (_ & _ & ?).
  Qed.

  Notation "SP_Weaken: p1 p2" := (GhostRet [p1])%E (at level 102, p1, p2 at level 1): expr_scope.

  Lemma typed_sp_weaken κ (p1 p2 : path) (tyA : type 𝔄) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I +[p1 ◁ᵥ &shr{κ} srty; p2 ◁ᵥ ghost_ty tyA] (SP_Weaken: p1 p2)
      (λ v, +[v ◁ᵥ &shr{κ} srty])
      (λ post '-[(l1, (γ, x1)); x2], λ mask π, vsp_incl x2 x1 ∧ post -[(l1, (γ, x2))] mask π).
  Proof.
    iIntros (Alv tid post mask iκs [[l1 [γ x1]] [x2 []]])
      "_ #TIME #PROPH _ #E L $ (p1 & _ & _) #Obs".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & %Hincl & _)"; [done|].
    iDestruct "p1" as (vp1 Hp1 w1 d [-> Hw1]) "[#⧖ #Own]". simpl in Hw1. simplify_eq.
    destruct d as [|d]; [done|].
    iDestruct (sr_shr_elim with "Own") as "#Shr".
    iDestruct (Alv with "L E") as "#Alv".
    iApply wp_fupd. wp_bind p1. iApply (wp_wand with "[]"); [by iApply wp_eval_path|].
    iIntros (? ->).
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|]. iIntros "£ _".
    iDestruct (lc_weaken (S d + 1) with "£") as "£"; [rewrite /advance_credits; nia|].
    wp_rec.
    iMod (sr_shr_sto with "L Alv Shr £") as "($ & %Hγ & #Hsto)"; [solve_ndisj|].
    iPoseProof (guards_weaken_rhs_sep_r with "Shr") as "#Hsp_own1".
    iPoseProof (guards_weaken_rhs_point with "Hsp_own1") as "Hsp_own2".
    { apply point_prop_p_own. }
    { by apply sp_own_mono. }
    iPoseProof (guards_include_pers (⌜{[γ]} ⊆ ↑NllftG⌝ ∗ sp_sto γ (λ _ c, gt_gho tyC c tid))%I
      with "[] Hsp_own2") as "Shr'".
    { by iSplit. }
    iModIntro. iExists -[(l1, (γ, x2))]. iSplitL.
    - iSplit; [|done]. iApply (sr_shr_own_intro with "⧖").
      by rewrite (bi.sep_comm (sp_own _ _)).
    - iApply (proph_obs_impl with "Obs"). by intros π' [_ ?].
  Qed.

  Local Lemma ghost_pair_val_intro {𝔅 𝔇} tid (tyA: type 𝔅) (tyB: type 𝔇) a b d :
    ⧖d -∗ tctx_elt_interp tid (MLitV (VTuple [VTuple []; VTuple []]) ◁ᵥ (ghost_ty tyA * ghost_ty tyB)%T) (a, b).
  Proof. iIntros "⧖". rewrite tctx_val_val. iExists d. by iFrame. Qed.

  Notation "SP_Validate: p1" := GhostOp2 (at level 102, p1 at level 1): expr_scope.

  (** Validating: the result is a pair of ghost values, a frame [q] and a stored value. *)
  Lemma typed_sp_validate `{!Inhabited (~~ℭ)} κ (p1 : path) (tyA : type 𝔄) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I +[p1 ◁ᵥ &shr{κ} srty] (SP_Validate: p1)
      (λ v, +[v ◁ᵥ (ghost_ty tyA * ghost_ty tyC)%T])
      (λ post '-[(_, (γ, p))], λ mask π, ∀ q t, vsp_rel (vsp_op p q) t π →
        (∀ k s, t !! k = Some s → post -[(q, s)] mask π) ∧
        (t = ∅ → post -[(q, inhabitant)] mask π)).
  Proof.
    iIntros (Alv tid post mask iκs [[l [γ p]] []]) "_ #TIME #PROPH _ #E L $ (p1 & _) #Obs".
    iDestruct "p1" as (vp1 Hp1 w1 d [-> Hw1]) "[#⧖ #Own]".
    destruct d as [|d]; [done|].
    iDestruct (sr_shr_elim with "Own") as "#Shr".
    iDestruct (Alv with "L E") as "#Alv".
    iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|]. iIntros "£ _".
    iDestruct (lc_weaken ((S d + 1) + (S d + 1)) with "£") as "[£1 £2]";
      [rewrite /advance_credits; nia|].
    iApply wp_ghost_op2. iIntros "!> !>".
    iMod (sr_shr_sto with "L Alv Shr £1") as "(L & %Hγ & #Hsto)"; [solve_ndisj|].
    iPoseProof (guards_weaken_rhs_sep_r with "Shr") as "#Shr3".
    iDestruct (guards_transitive_right with "Alv Shr3") as "Shr4".
    iDestruct (sp_own_unit with "Hsto") as "#Hunit".
    iMod (sp_validate_with_extra_guard_with_later vsp_unit p γ _ _ ⊤ (↑NllftG) _
      ltac:(set_solver) ltac:(solve_ndisj) ltac:(solve_ndisj)
      with "PROPH Hsto Shr4 L Hunit") as "J".
    iMod (lc_fupd_elim_laterN with "£2 J") as ">(%q & %t & #Hobs & $ & _)".
    iModIntro. iCombine "Obs Hobs" as "Obs'".
    destruct (decide (t = ∅)) as [Hempty|Hnempty].
    - iExists -[(q, inhabitant)]. iSplitL; [iSplit; [by iApply ghost_pair_val_intro|done]|].
      iApply (proph_obs_impl with "Obs'"). intros π [Hpost Hrel]. rewrite vsp_unit_op in Hrel.
      by apply (Hpost _ _ Hrel).
    - apply map_choose in Hnempty as (k & s & Hlookup).
      iExists -[(q, s)]. iSplitL; [iSplit; [by iApply ghost_pair_val_intro|done]|].
      iApply (proph_obs_impl with "Obs'"). intros π [Hpost Hrel]. rewrite vsp_unit_op in Hrel.
      by eapply (Hpost _ _ Hrel).
  Qed.

  Notation "SP_ExchangeWithShr: p1 p2 p3 p4 p5" := GhostOp
    (at level 102, p1,p2,p3,p4,p5 at level 1): expr_scope.

  Lemma typed_sp_exchange_with_shr (k : K) κ (p1 p2 p3 p4 p5 : path) (tyA : type 𝔄) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
      +[p1 ◁ᵥ srty; p2 ◁ᵥ &shr{κ} srty; p3 ◁ᵥ tracked_ty tyC; p4 ◁ᵥ ghost_ty tyA;
        p5 ◁ᵥ ghost_ty tyC]
      (SP_ExchangeWithShr: p1 p2 p3 p4 p5) (λ v, +[p1 ◁ᵥ srty; v ◁ᵥ tracked_ty tyC])
      (λ post '-[(γ, p); (_, (γ', p')); s; new_p; new_s], λ mask π, γ = γ' ∧
        vsp_exchanges (vsp_op p p') {[ k := s ]} (vsp_op new_p p') {[ k := new_s ]} π ∧
        post -[(γ, new_p); new_s] mask π).
  Proof.
    iIntros (Alv tid post mask iκs [[γ p] [[l' [γ' p']] [s [new_p [new_s []]]]]])
      "_ #TIME #PROPH _ #E L $ (Hp & Hp' & Hs & _ & _ & _) #Obs".
    iMod (proph_obs_sat with "PROPH Obs") as "(%π & <- & _)"; [done|].
    iDestruct "Hp" as (vp Hp w d [-> Hw]) "[#⧖ (%Hγ & #Hsto & Hown)]". simpl in Hw. simplify_eq.
    iDestruct "Hp'" as (vp' Hp' w' d' [-> Hw']) "[#⧖' #Own']".
    iDestruct "Hs" as (vs Hs w'' d'' [-> Hw'']) "[_ HghoC]".
    destruct d' as [|d']; [done|].
    iDestruct (sr_shr_elim with "Own'") as "#Shr".
    iDestruct (Alv with "L E") as "#Alv".
    iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME ⧖'"); [done|]. iIntros "£ _".
    iDestruct (lc_weaken ((S d' + 1) + 1) with "£") as "[£1 £2]";
      [rewrite /advance_credits; nia|].
    iApply wp_ghost_op. iIntros "!> !>".
    iDestruct (guards_transitive_right with "Alv Shr") as "Shr1".
    iPoseProof (guards_weaken_rhs_sep_r with "Shr1") as "#Shr2".
    iMod (sp_exchange_with_extra_guard_with_later p new_p p' {[ k := s ]} {[ k := new_s ]} γ _ _
      ⊤ (↑NllftG) _ ltac:(set_solver) ltac:(solve_ndisj) ltac:(solve_ndisj)
      with "PROPH Hsto Shr2 [] L Hown [HghoC]") as "J".
    { iApply (proph_obs_impl with "Obs"). by intros π' (_ & ? & _). }
    { iNext. by rewrite big_sepM_singleton. }
    iMod (lc_fupd_elim_laterN with "£1 J") as ">($ & Hown & HghoC)".
    iMod (lc_fupd_elim_later with "£2 HghoC") as "HghoC". rewrite big_sepM_singleton.
    iModIntro. iExists -[(γ, new_p); new_s].
    iSplitL; [|iApply (proph_obs_impl with "Obs"); by intros π' (_ & _ & ?)].
    iSplitL "Hown"; [|iSplit; [by iApply (tracked_val_intro with "⧖ HghoC")|done]].
    iApply (val_path_intro _ _ srty with "⧖"); [done|done|]. by iFrame "Hsto Hown".
  Qed.

  Notation "SP_ExchangeWithShrNonDet: p1 p2 p3 p4" := GhostOp
    (at level 102, p1,p2,p3,p4 at level 1): expr_scope.

  Lemma typed_sp_exchange_with_shr_nondeterministic (k : K) κ (p1 p2 p3 p4 : path) n
      (ty : type (vecₛ (𝔄 * ℭ) n)) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
      +[p1 ◁ᵥ srty; p2 ◁ᵥ &shr{κ} srty; p3 ◁ᵥ tracked_ty tyC; p4 ◁ᵥ ghost_ty ty]
      (SP_ExchangeWithShrNonDet: p1 p2 p3 p4) (λ v, +[p1 ◁ᵥ srty; v ◁ᵥ tracked_ty tyC])
      (λ post '-[(γ, p); (_, (γ', p')); s; new_pss], λ mask π, γ = γ' ∧
        vsp_exchanges_nondeterministic (vsp_op p p') {[ k := s ]}
          (λ new_p_big new_b, ∃ new_p new_s, new_p_big = vsp_op new_p p' ∧ new_b = {[ k := new_s ]}
            ∧ (new_p, new_s) ∈ vec_to_list new_pss) ∧
        Forall (λ '(new_p, new_s), post -[(γ, new_p); new_s] mask π) (vec_to_list new_pss)).
  Proof.
    iIntros (Alv tid post mask iκs [[γ p] [[l' [γ' p']] [s [new_pss []]]]])
      "_ #TIME #PROPH _ #E L $ (Hp & Hp' & Hs & _ & _) #Obs".
    iMod (proph_obs_sat with "PROPH Obs") as "(%π & <- & %exchng & _)"; [done|].
    iDestruct "Hp" as (vp Hp w d [-> Hw]) "[#⧖ (%Hγ & #Hsto & Hown)]". simpl in Hw. simplify_eq.
    iDestruct "Hp'" as (vp' Hp' w' d' [-> Hw']) "[#⧖' #Own']".
    iDestruct "Hs" as (vs Hs w'' d'' [-> Hw'']) "[_ HghoC]".
    destruct d' as [|d']; [done|].
    iDestruct (sr_shr_elim with "Own'") as "#Shr".
    iDestruct (Alv with "L E") as "#Alv".
    assert (vsp_exchanges_nondeterministic (vsp_op p p') {[ k := s ]}
      (λ p2_q b2, ∃ p2, p2_q = vsp_op p2 p' ∧
        (λ new_p new_b, ∃ new_s, new_b = {[ k := new_s ]} ∧ (new_p, new_s) ∈ vec_to_list new_pss)
        p2 b2)) as exchng'.
    { intros q t1 Hsat.
      destruct (exchng q t1 Hsat) as (p2q & b2 & (new_p & new_s & -> & -> & Hin) & Himp).
      exists (vsp_op new_p p'), {[ k := new_s ]}. split; last done.
      exists new_p. split; first done. eauto. }
    iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME ⧖'"); [done|]. iIntros "£ _".
    iDestruct (lc_weaken ((S d' + 1) + 1) with "£") as "[£1 £2]";
      [rewrite /advance_credits; nia|].
    iApply wp_ghost_op. iIntros "!> !>".
    iDestruct (guards_transitive_right with "Alv Shr") as "Shr1".
    iPoseProof (guards_weaken_rhs_sep_r with "Shr1") as "#Shr2".
    iMod (sp_exchange_with_extra_guard_nondeterministic_with_later p p' {[ k := s ]} _
      γ _ _ ⊤ (↑NllftG) _ exchng' ltac:(set_solver) ltac:(solve_ndisj) ltac:(solve_ndisj)
      with "PROPH Hsto Shr2 L Hown [HghoC]") as "J".
    { iNext. by rewrite big_sepM_singleton. }
    iMod (lc_fupd_elim_laterN with "£1 J") as ">(%new_p & %b2 & %Hin & $ & Hown & HghoC)".
    destruct Hin as (new_s & -> & Hin).
    iMod (lc_fupd_elim_later with "£2 HghoC") as "HghoC". rewrite big_sepM_singleton.
    iModIntro. iExists -[(γ, new_p); new_s].
    iSplitL; last first.
    { iApply (proph_obs_impl with "Obs"). intros π' (_ & _ & Hpost).
      rewrite Forall_forall in Hpost. by apply (Hpost (new_p, new_s)). }
    iSplitL "Hown"; [|iSplit; [by iApply (tracked_val_intro with "⧖ HghoC")|done]].
    iApply (val_path_intro _ _ srty with "⧖"); [done|done|]. by iFrame "Hsto Hown".
  Qed.

  Notation "SP_ValidateWithShr: p1 p2" := GhostOp2 (at level 102, p1,p2 at level 1): expr_scope.

  (** Validating with a unique borrow and a shared reference (the unique borrow is given
      up). *)
  Lemma typed_sp_validate_with_shr `{!Inhabited (~~ℭ)} κ (p1 p2 : path) (tyA : type 𝔄) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I +[p1 ◁ᵥ &uniq{κ} srty; p2 ◁ᵥ &shr{κ} srty]
      (SP_ValidateWithShr: p1 p2) (λ v, +[v ◁ᵥ (ghost_ty tyA * ghost_ty tyC)%T])
      (λ post '-[(_, (γ1, x1), _, _, _, _); (_, (γ2, x2))], λ mask π, γ1 = γ2 ∧
        ∀ q t, vsp_rel (vsp_op (vsp_op x1 x2) q) t π →
          (∀ k s, t !! k = Some s → post -[(q, s)] mask π) ∧
          (t = ∅ → post -[(q, inhabitant)] mask π)).
  Proof.
    iIntros (Alv tid post mask iκs [[[[[[l1 [γ1 x1]] ξi] di] gi] idx] [[l2 [γ2 x2]] []]])
      "#LFT #TIME #PROPH #UNIQ #E L $ (p1 & p2 & _) #Obs".
    iMod (proph_obs_sat with "PROPH Obs") as "(%π & <- & _)"; [done|].
    iDestruct "p1" as (vp1 Hp1 w1 d1 [-> Hw1]) "[#⧖1 Huniq]".
    iDestruct "p2" as (vp2 Hp2 w2 d2 [-> Hw2]) "[#⧖2 #Own2]".
    destruct d2 as [|d2]; [done|].
    iDestruct (sr_shr_elim with "Own2") as "#Shr".
    iDestruct (Alv with "L E") as "#Alv".
    iDestruct "Huniq" as "(_ & %Hineq & UB)".
    iMod (fractional.frac_split_guard_in_half NllftG with "L Alv")
      as (γ) "[F1 [F2 [#guardHalf #back]]]"; [solve_ndisj|].
    iMod (llftl_begin with "LFT") as (κ1) "[A1 #Kill1]"; [done|].
    iMod (llftl_begin with "LFT") as (κ2) "[A2 #Kill2]"; [done|].
    iMod (llftl_borrow_shared _ κ1 with "F1") as "[#G1 F1]"; [done|].
    iMod (llftl_borrow_shared _ κ2 with "F2") as "[#G2 F2]"; [done|].
    iDestruct (guards_remove_later_rhs with "G1") as "G1'".
    iDestruct (guards_remove_later_rhs with "G2") as "G2'".
    iDestruct (guards_transitive with "G1' guardHalf") as "Incl1".
    iDestruct (guards_transitive with "G2' guardHalf") as "Incl2".
    iMod (uniq_body_acc_drop with "LFT UNIQ Incl1 UB A1") as "(Hgho1 & _ & Hclose1)"; [done|].
    iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME ⧖2"); [done|]. iIntros "£ _".
    iDestruct (lc_weaken ((S d2 + 1) + 1 + 1) with "£") as "[[£1 £2] £3]";
      [rewrite /advance_credits; nia|].
    iApply wp_ghost_op2. iIntros "!> !>".
    iMod (uniq_payload_run _ _ _ _ _ _ _ (@[static]) with "[] [] Hgho1")
      as "(_ & H⧖ & Hgho1 & H↦)"; [rewrite /uniq_util.lazyE; solve_ndisj|iApply guards_refl|
      iApply llftl_tok_unit|].
    iDestruct "Hgho1" as "(%Hγ1 & #Hsto1 & Hown1)".
    iDestruct (guards_transitive_right with "Incl2 Shr") as "Shr2".
    iPoseProof (guards_weaken_rhs_sep_r with "Shr2") as "Shr3".
    iMod (sp_validate_with_extra_guard_with_later x1 x2 γ1 _ _ ⊤ (↑NllftG) _
      ltac:(set_solver) ltac:(solve_ndisj) ltac:(solve_ndisj)
      with "PROPH Hsto1 Shr3 A2 Hown1") as "J".
    iMod (lc_fupd_elim_laterN with "£1 J") as ">(%q & %t & #Hobs & A2 & Hown1)".
    iMod (fupd_mask_subseteq (↑Nllft)) as "Hclose"; [solve_ndisj|].
    iMod ("Hclose1" $! ((γ1, x1) : ~~ (ghostₛ (positiveₛ * 𝔄))) _ _ with "[H↦ H⧖ Hown1]")
      as "A1".
    { iNext. iApply (uniq_payload_intro with "H⧖ [Hown1] H↦"). by iFrame "#%∗". }
    iMod ("Kill1" with "A1") as "Hkilled1".
    iMod (lc_fupd_add_later with "£2 Hkilled1") as "Hkilled1".
    iMod ("Kill2" with "A2") as "Hkilled2".
    iMod (lc_fupd_add_later with "£3 Hkilled2") as "Hkilled2".
    iMod "Hclose" as "_".
    iMod ("F1" with "Hkilled1") as ">Hγ1".
    iMod ("F2" with "Hkilled2") as ">Hγ2".
    iMod (fupd_mask_subseteq (↑NllftG)) as "Hclose"; [solve_ndisj|].
    iMod ("back" with "Hγ1 Hγ2") as "$".
    iMod "Hclose" as "_".
    iModIntro. iCombine "Obs Hobs" as "Obs'".
    destruct (decide (t = ∅)) as [Hempty|Hnempty].
    - iExists -[(q, inhabitant)]. iSplitL; [iSplit; [by iApply ghost_pair_val_intro|done]|].
      iApply (proph_obs_impl with "Obs'"). intros π' [[_ Hpost] Hrel].
      eapply Hpost in Hrel as [? Hpost_empty]. by apply Hpost_empty.
    - apply map_choose in Hnempty as (k & s & Hlookup).
      iExists -[(q, s)]. iSplitL; [iSplit; [by iApply ghost_pair_val_intro|done]|].
      iApply (proph_obs_impl with "Obs'"). intros π' [[_ Hpost] Hrel].
      eapply Hpost in Hrel as [Hpost_ne _]. by eapply Hpost_ne.
  Qed.
End StorageProtocol_bytes.
