From iris.proofmode Require Import proofmode.
From iris.algebra Require Import gmap.
From lrust.typing Require Import lft_contexts.
From lrust.typing Require Export protocol ra_bytes.
From lrust.typing Require Import type programs ghost tracked product value_ctx own_bytes shr_bytes
  uniq_bytes uniq_bytes_util.
From lrust.typing Require uniq_util.
From guarding Require Import guard tactics guard_later_pers own_and.
From lrust.typing Require Import ra proph_protocol.
From lrust.lifetime Require Import lifetime_full.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

(** * Storage protocols on the byte layer

The typing rules of [typing/protocol.v], with the ghost values as MiniRust values ([◁ᵥ],
as in [typing/ra_bytes.v]) instead of boxes of size [0], shared references as [&shrb] and
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
    tctx_elt_interp tid (MLitV (VPtr l.1) ◁ᵥ &shrb{κ} ty) (l, x).
  Proof.
    iIntros (Hz Hv Hdef Hpers) "⧖ #G". rewrite tctx_val_val. iExists (S d). iFrame "⧖".
    iSplit; [done|]. rewrite /= /by_succ. iSplit; [by iApply shr_bytes_own_zst|].
    iSplit; [by iApply (ty_shr_default_from_guard ty)|]. iNext. iApply Hpers.
  Qed.

  Lemma ghost_shr_elim {𝔄} tid κ (ty: type 𝔄) l x d :
    ty_shr_is_default ty →
    (&shrb{κ} ty).(ty_gho_own) (l, x) (S d) (S d) tid -∗
    (@[κ] &&{↑NllftG; S d + 1}&&> ty.(ty_gho_own) x d (S d) tid).
  Proof.
    iIntros (?) "(_ & #Shr & _)". by iApply (ty_shr_default_to_guard ty with "Shr").
  Qed.
End ghost_vals.

(** ** Storable values *)
Section storable_bytes.
  Context `{!typeG Σ}.

  (** Making a value storable ([storable_new] of [typing/protocol.v]). *)
  Lemma storable_new_bytes {𝔄} E L I p (ty : type 𝔄) :
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
  Lemma storable_into_inner_bytes {𝔄} E L I p (ty : type 𝔄) :
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

Section storable_borrow_bytes.
  Context `{!typeG Σ}.

  (** Shared access to a stored value ([storable_borrow]). *)
  Lemma storable_borrow_bytes {𝔄} κ E L I p (ty : type 𝔄) :
    lctx_lft_alive E L κ → lctx_lft_incl E L κ (ty_lft ty) →
    typed_instr E L I +[p ◁ᵥ &shrb{κ} (storable_ty ty)] (GhostRetS [p])
      (λ v, +[v ◁ᵥ &shrb{κ} (tracked_ty ty)])
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
End storable_borrow_bytes.

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

  Notation "SPb_Alloc: p s" := GhostOp (at level 102, p,s at level 1): expr_scope.

  Lemma typed_spb_alloc (k : K) (p s : path) (tyA : type 𝔄) E L I :
    typed_instr E L I +[p ◁ᵥ ghost_ty tyA; s ◁ᵥ tracked_ty tyC] (SPb_Alloc: p s)
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

  Notation "SPb_Join: a b" := GhostOp (at level 102, a,b at level 1): expr_scope.

  Lemma typed_spb_join (p1 p2 : path) E L I :
    typed_instr E L I +[p1 ◁ᵥ srty; p2 ◁ᵥ srty] (SPb_Join: p1 p2) (λ v, +[v ◁ᵥ srty])
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

  Notation "SPb_Split: p p1 p2" := GhostOp (at level 102, p, p1, p2 at level 1): expr_scope.

  (** Splitting: [self] keeps the first part, the result is the second part. *)
  Lemma typed_spb_split (self p1 p2 : path) (ty : type 𝔄) E L I :
    typed_instr E L I +[self ◁ᵥ srty; p1 ◁ᵥ ghost_ty ty; p2 ◁ᵥ ghost_ty ty]
      (SPb_Split: self p1 p2) (λ v, +[self ◁ᵥ srty; v ◁ᵥ srty])
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

  Notation "SPb_Exchange: p1 p2 p3 p4" := GhostOp (at level 102, p1,p2,p3,p4 at level 1): expr_scope.

  (** Exchanging: [p1] holds the new protocol element, the result is the new stored
      value. *)
  Lemma typed_spb_exchange (k : K) (p1 p2 p3 p4 : path) (tyA : type 𝔄) E L I :
    typed_instr E L I
      +[p1 ◁ᵥ srty; p2 ◁ᵥ tracked_ty tyC; p3 ◁ᵥ ghost_ty tyA; p4 ◁ᵥ ghost_ty tyC]
      (SPb_Exchange: p1 p2 p3 p4) (λ v, +[p1 ◁ᵥ srty; v ◁ᵥ tracked_ty tyC])
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

  Notation "SPb_Deposit: p1 p2 p3" := GhostOp (at level 102, p1,p2,p3 at level 1): expr_scope.

  Lemma typed_spb_deposit (k : K) (p1 p2 p3 : path) (tyA : type 𝔄) E L I :
    typed_instr E L I +[p1 ◁ᵥ srty; p2 ◁ᵥ tracked_ty tyC; p3 ◁ᵥ ghost_ty tyA]
      (SPb_Deposit: p1 p2 p3) (λ v, +[v ◁ᵥ srty])
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

  Notation "SPb_Withdraw: p1 p2 p3" := GhostOp (at level 102, p1,p2,p3 at level 1): expr_scope.

  Lemma typed_spb_withdraw (k : K) (p1 p2 p3 : path) (tyA : type 𝔄) E L I :
    typed_instr E L I +[p1 ◁ᵥ srty; p2 ◁ᵥ ghost_ty tyA; p3 ◁ᵥ ghost_ty tyC]
      (SPb_Withdraw: p1 p2 p3) (λ v, +[p1 ◁ᵥ srty; v ◁ᵥ tracked_ty tyC])
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

  Notation "SPb_Update: p1 p2" := GhostOp (at level 102, p1,p2 at level 1): expr_scope.

  Lemma typed_spb_update (p1 p2 : path) (tyA : type 𝔄) E L I :
    typed_instr E L I +[p1 ◁ᵥ srty; p2 ◁ᵥ ghost_ty tyA] (SPb_Update: p1 p2)
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

  Notation "SPb_ExchangeNonDet: p1 p2 p3" := GhostOp (at level 102, p1,p2,p3 at level 1): expr_scope.

  Lemma typed_spb_exchange_nondeterministic (k : K) (p1 p2 p3 : path) (n : nat)
      (ty : type (vecₛ (𝔄 * ℭ) n)) E L I :
    typed_instr E L I +[p1 ◁ᵥ srty; p2 ◁ᵥ tracked_ty tyC; p3 ◁ᵥ ghost_ty ty]
      (SPb_ExchangeNonDet: p1 p2 p3) (λ v, +[p1 ◁ᵥ srty; v ◁ᵥ tracked_ty tyC])
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
    (&shrb{κ} srty).(ty_gho_own) (l, (γ, p)) (S d) (S d) tid -∗
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
    tctx_elt_interp tid (MLitV (VPtr l.1) ◁ᵥ &shrb{κ} srty) (l, (γ, p)).
  Proof.
    iIntros "⧖ #G". iApply (ghost_shr_intro _ _ srty with "⧖");
      [by rewrite /ty_bsize -ty_mty_eq|done|done|done|]. iSimpl. by rewrite -bi.sep_assoc.
  Qed.

  Notation "SPb_Guard: p1 p2" := (GhostRet [p1])%E (at level 102, p1,p2 at level 1): expr_scope.

  Lemma typed_spb_guard (k : K) (p1 p2 : path) E L I κ :
    lctx_lft_alive E L κ →
    typed_instr E L I +[p1 ◁ᵥ &shrb{κ} srty; p2 ◁ᵥ ghost_ty tyC] (SPb_Guard: p1 p2)
      (λ v, +[v ◁ᵥ &shrb{κ} (tracked_ty tyC)])
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

  Notation "SPb_JoinSharedDet: p1 p2 p3" := (GhostRet [p1])%E
    (at level 102, p1, p2, p3 at level 1): expr_scope.

  Lemma typed_spb_join_shared_to_target κ (p1 p2 p3 : path) (ty : type 𝔄) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
      +[p1 ◁ᵥ &shrb{κ} srty; p2 ◁ᵥ &shrb{κ} srty; p3 ◁ᵥ ghost_ty ty]
      (SPb_JoinSharedDet: p1 p2 p3) (λ v, +[v ◁ᵥ &shrb{κ} srty])
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

  Notation "SPb_Weaken: p1 p2" := (GhostRet [p1])%E (at level 102, p1, p2 at level 1): expr_scope.

  Lemma typed_spb_weaken κ (p1 p2 : path) (tyA : type 𝔄) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I +[p1 ◁ᵥ &shrb{κ} srty; p2 ◁ᵥ ghost_ty tyA] (SPb_Weaken: p1 p2)
      (λ v, +[v ◁ᵥ &shrb{κ} srty])
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
End StorageProtocol_bytes.
