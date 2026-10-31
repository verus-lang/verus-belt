From iris.proofmode Require Import proofmode.
From lrust.typing Require Import lft_contexts.
From lrust.typing Require Export ra.
From lrust.typing Require Import type programs ghost value_ctx own_bytes shr_bytes.
From guarding Require Import guard tactics guard_later_pers own_and.
From guarding.internal Require Import auth_frag_util.
From iris.algebra Require Import auth.
From lrust.lifetime Require Import lifetime_full.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

(** * Verus-style resource algebras on the byte layer

The typing rules of [typing/ra.v], with the ghost values as MiniRust values ([◁ᵥ]): a
ghost value ([ra_ty], [ghost_ty]) is zero-sized, and its MiniRust value is the empty tuple,
so it is a value (not a box of size [0], [own_ptr 0], as in [typing/ra.v]). Shared
references are [&shrb]. The resource algebra and its ghost type ([ra_ty], [ra_inv] and
the lemmas [ra_alloc], [ra_validate], [ra_update] etc.) are those of [typing/ra.v]. A
ghost operation is a no-op that returns the empty tuple ([GhostOp]). *)

Definition GhostOp : expr := (Skip ;; MkTuple [])%E.

Notation "RAb_Alloc: p" := GhostOp (at level 102, p at level 150): expr_scope.
Notation "RAb_Join: p1 p2" := GhostOp (at level 102, p1, p2 at level 1): expr_scope.
Notation "RAb_Split: p p1 p2" := GhostOp (at level 102, p, p1, p2 at level 1): expr_scope.
Notation "RAb_Unit:" := GhostOp : expr_scope.
Notation "RAb_Update: self p" := GhostOp (at level 102, self, p at level 1): expr_scope.
Notation "RAb_Validate: self" := GhostOp (at level 102, self at level 1): expr_scope.
Notation "RAb_JoinSharedDet: p1 p2 p" := GhostOp (at level 102, p1, p2, p at level 1): expr_scope.
Notation "RAb_Weaken: p1 p2" := GhostOp (at level 102, p1, p2 at level 1): expr_scope.
Notation "RAb_UpdateWithShr: self other new_value" := GhostOp
  (at level 102, self, other, new_value at level 1): expr_scope.

Section ghost_vals.
  Context `{!typeG Σ}.

  (** A ghost operation takes two steps. *)
  Lemma wp_ghost_op E Φ :
    ▷ ▷ Φ (MLitV (VTuple [])) -∗ WP GhostOp @ E {{ Φ }}.
  Proof.
    iIntros "HΦ". rewrite /GhostOp. wp_seq. wp_seq.
    eapply (tac_wp_pure []); [apply (pure_mk_tuple [])|done|tc_solve|simpl; iApply wp_value].
    done.
  Qed.

End ghost_vals.

Notation "RAb_JoinSharedDet: p1 p2 p" := (Skip ;; p1)%E
  (at level 102, p1, p2, p at level 1, only parsing): expr_scope.

Section RA_bytes.
  Context `{!typeG Σ}.
  Context {𝔄 : syn_type} (VRA : VerusRA (~~𝔄)).
  Context `{G2: !inG Σ (authUR (vra_carUR VRA))}.
  Hypothesis (𝔄_const  : ∀ (x : ~~𝔄) π1 π2 , @vπ 𝔄 x π1 = @vπ 𝔄 x π2).

  Local Notation raty := (ra_ty VRA 𝔄_const).

  Local Lemma ra_val_own tid γ x d :
    ⧖d -∗ own γ (◯ VraCar VRA x) -∗ ra_inv VRA γ -∗
    tctx_elt_interp tid (MLitV (VTuple []) ◁ᵥ raty) (γ, x).
  Proof. iIntros "⧖ Own Inv". rewrite tctx_val_val. iExists d. by iFrame. Qed.

  Local Lemma ra_shr_own tid κ l γ x d :
    ⧖(S d) -∗ (@[κ] &&{↑NllftG; S d + 1}&&> own γ (◯ VraCar VRA x) ∗ ra_inv VRA γ) -∗
    tctx_elt_interp tid (MLitV (VPtr l.1) ◁ᵥ &shrb{κ} raty) (l, (γ, x)).
  Proof.
    iIntros "⧖ #G". rewrite tctx_val_val. iExists (S d). iFrame "⧖". iSplit; [done|].
    rewrite /= /by_succ. iSplit; [iApply shr_bytes_own_zst; [by rewrite /ty_bsize -ty_mty_eq|done]|].
    iSplit; [|done]. by iApply (ty_shr_default_from_guard raty).
  Qed.

  Lemma typed_rab_alloc (p : path) (ty : type 𝔄) E L I :
    typed_instr E L I +[p ◁ᵥ ghost_ty ty] (RAb_Alloc: p) (λ v, +[v ◁ᵥ raty])
      (λ post '-[x], λ mask π, vra_valid VRA x π ∧ ∀ γ, post -[(γ, x)] mask π).
  Proof.
    iIntros (tid post mask iκs [x []]) "_ _ _ _ _ $ $ [p _] #Obs".
    iDestruct "p" as (vp Hp w d [-> Hw]) "[#⧖ _]".
    iMod (ra_alloc VRA ⊤ x with "[]") as (γ) "[Hx #Hinv]".
    { iApply (proph_obs_impl with "Obs"). by intros π [? _]. }
    iApply wp_ghost_op. iIntros "!> !>". iExists -[(γ, x)].
    iSplitL; [iSplit; [by iApply (ra_val_own with "⧖ Hx")|done]|].
    iApply (proph_obs_impl with "Obs"). intros π [_ Hpost]. apply Hpost.
  Qed.

  Lemma typed_rab_join (p1 p2 : path) E L I :
    typed_instr E L I +[p1 ◁ᵥ raty; p2 ◁ᵥ raty] (RAb_Join: p1 p2) (λ v, +[v ◁ᵥ raty])
      (λ post '-[(γ1, x1); (γ2, x2)], λ mask π,
        γ1 = γ2 ∧ post -[(γ1, vra_op VRA x1 x2)] mask π).
  Proof.
    iIntros (tid post mask iκs [[γ1 x1] [[γ2 x2] []]]) "_ _ #PROPH _ _ $ $ (p1 & p2 & _) #Obs".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & _)"; [done|].
    iDestruct "p1" as (vp1 Hp1 w1 d1 [-> Hw1]) "[#⧖1 [Hx1 #Hinv]]".
    iDestruct "p2" as (vp2 Hp2 w2 d2 [-> Hw2]) "[#⧖2 [Hx2 _]]".
    iCombine "Hx1 Hx2" as "Hx". rewrite -auth_frag_op vra_car_op_eq.
    iApply wp_ghost_op. iIntros "!> !>". iExists -[(γ1, vra_op VRA x1 x2)].
    iSplitL; [iSplit; [by iApply (ra_val_own with "⧖1 Hx Hinv")|done]|].
    iApply (proph_obs_impl with "Obs"). by intros π [_ ?].
  Qed.

  (** Splitting: [self] keeps the first part, the result is the second part. (In
      [typing/ra.v], the result is a box of the pair of the two parts.) *)
  Lemma typed_rab_split (self p1 p2 : path) (ty : type 𝔄) E L I :
    typed_instr E L I +[self ◁ᵥ raty; p1 ◁ᵥ ghost_ty ty; p2 ◁ᵥ ghost_ty ty]
      (RAb_Split: self p1 p2) (λ v, +[self ◁ᵥ raty; v ◁ᵥ raty])
      (λ post '-[(γ, x); x1; x2], λ mask π,
        x = vra_op VRA x1 x2 ∧ post -[(γ, x1); (γ, x2)] mask π).
  Proof.
    iIntros (tid post mask iκs [[γ x] [x1 [x2 []]]]) "_ _ #PROPH _ _ $ $ (p & _ & _ & _) #Obs".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & -> & _)"; [done|].
    iDestruct "p" as (vp Hp w d [-> Hw]) "[#⧖ [Hx #Hinv]]".
    rewrite -vra_car_op_eq auth_frag_op. iDestruct "Hx" as "[Hx1 Hx2]".
    iApply wp_ghost_op. iIntros "!> !>". iExists -[(γ, x1); (γ, x2)].
    iSplitL; [|iApply (proph_obs_impl with "Obs"); by intros π [_ ?]].
    iSplitL "Hx1"; [|iSplit; [by iApply (ra_val_own with "⧖ Hx2 Hinv")|done]].
    iExists _. iSplit; [done|]. iExists (VTuple []), d. iSplit; [done|]. by iFrame.
  Qed.

  Lemma typed_rab_unit E L I :
    typed_instr E L I +[] (RAb_Unit:) (λ v, +[v ◁ᵥ raty])
      (λ post '-[], λ mask π, ∀ γ, post -[(γ, vra_unit VRA)] mask π).
  Proof.
    iIntros (tid post mask iκs []) "_ _ _ _ _ $ $ _ #Obs".
    iMod (ra_alloc VRA ⊤ (vra_unit VRA) with "[]") as (γ) "[Hx #Hinv]".
    { iApply proph_obs_true. intros π. apply vra_unit_valid. }
    iMod persistent_time_receipt_0 as "⧖".
    iApply wp_ghost_op. iIntros "!> !>". iExists -[(γ, vra_unit VRA)].
    iSplitL; [iSplit; [by iApply (ra_val_own with "⧖ Hx Hinv")|done]|].
    iApply (proph_obs_impl with "Obs"). done.
  Qed.

  Lemma typed_rab_update (self p : path) (ty : type 𝔄) E L I :
    typed_instr E L I +[self ◁ᵥ raty; p ◁ᵥ ghost_ty ty] (RAb_Update: self p)
      (λ v, +[v ◁ᵥ raty])
      (λ post '-[(γ, x); y], λ mask π,
        vra_frame_preserving_update VRA x y π ∧ post -[(γ, y)] mask π).
  Proof.
    iIntros (tid post mask iκs [[γ x] [y []]]) "_ _ _ _ _ $ $ (p & _ & _) #Obs".
    iDestruct "p" as (vp Hp w d [-> Hw]) "[#⧖ [Hx #Hinv]]".
    iMod (ra_update VRA ⊤ γ x y with "Hinv Hx [Obs]") as "Hy"; [done| |].
    { iApply (proph_obs_impl with "Obs"). by intros π [? _]. }
    iApply wp_ghost_op. iIntros "!> !>". iExists -[(γ, y)].
    iSplitL; [iSplit; [by iApply (ra_val_own with "⧖ Hy Hinv")|done]|].
    iApply (proph_obs_impl with "Obs"). by intros π [_ ?].
  Qed.

  Lemma typed_rab_update_nondeterministic (self p : path) (n : nat) (ty : type (vecₛ 𝔄 n)) E L I :
    typed_instr E L I +[self ◁ᵥ raty; p ◁ᵥ ghost_ty ty] (RAb_Update: self p)
      (λ v, +[v ◁ᵥ raty])
      (λ post '-[(γ, x); ys], λ mask π,
        vra_frame_preserving_update_nondeterministic VRA x (λ y, y ∈ vec_to_list ys) ∧
        Forall (λ y, post -[(γ, y)] mask π) (vec_to_list ys)).
  Proof.
    iIntros (tid post mask iκs [[γ x] [ys []]]) "_ _ #PROPH _ _ $ $ (p & _ & _) #Obs".
    iMod (proph_obs_sat with "PROPH Obs") as "(%π & %Hupd & _)"; [done|].
    iDestruct "p" as (vp Hp w d [-> Hw]) "[#⧖ [Hx #Hinv]]".
    iMod (ra_update_nondeterministic VRA ⊤ γ x _ ltac:(done) Hupd with "Hinv Hx")
      as (y) "[%Hin Hy]".
    iApply wp_ghost_op. iIntros "!> !>". iExists -[(γ, y)].
    iSplitL; [iSplit; [by iApply (ra_val_own with "⧖ Hy Hinv")|done]|].
    iApply (proph_obs_impl with "Obs"). intros π' [_ Hpost].
    rewrite Forall_forall in Hpost. by apply Hpost.
  Qed.

  (** The ownership of a shared reference to an [ra_ty] at [κ]. *)
  Local Lemma ra_shr_guard tid κ l γ x d :
    (&shrb{κ} raty).(ty_gho_own) (l, (γ, x)) (S d) (S d) tid -∗
    (@[κ] &&{↑NllftG; S d + 1}&&> own γ (◯ VraCar VRA x) ∗ ra_inv VRA γ).
  Proof.
    iIntros "(_ & #Shr & _)". iDestruct (ty_shr_default_to_guard raty with "Shr") as "#G";
      [done|].
    iApply (lguards_weaken_later with "G"). lia.
  Qed.

  (** Opening the guard of a shared reference, to get the invariant. *)
  Local Lemma ra_shr_inv E L κ γ x n G :
    ↑NllftG ⊆ G →
    llctx_interp L -∗ (llctx_interp L &&{↑NllftG}&&> @[κ]) -∗
    (@[κ] &&{↑NllftG; n}&&> own γ (◯ VraCar VRA x) ∗ ra_inv VRA γ) -∗ £n ={G}=∗
      llctx_interp L ∗ ra_inv VRA γ.
  Proof.
    iIntros (?) "L #Alv #Shr £". iDestruct (guards_transitive_right with "Alv Shr") as "G1".
    iMod (guards_extract_persistent_later _ _ (ra_inv VRA γ) with "G1 L []") as "Upd";
      [done| |].
    { iIntros "[_ $]". }
    iMod (lc_fupd_elim_laterN with "£ Upd") as ">[$ $]". done.
  Qed.

  Lemma typed_rab_validate κ (self : path) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I +[self ◁ᵥ &shrb{κ} raty] (RAb_Validate: self) (λ _, +[])
      (λ post '-[(_, (γ, x))], λ mask π, (vra_valid VRA x π → post -[] mask π)).
  Proof.
    iIntros (Alv tid post mask iκs [[l [γ x]] []]) "_ #TIME _ _ #E L $ [p _] #Obs".
    iDestruct "p" as (vp Hp w d [-> Hw]) "[#⧖ #Own]".
    destruct d as [|d]; [done|]. iDestruct (ra_shr_guard with "Own") as "#Shr".
    iDestruct (Alv with "L E") as "#Alv".
    iApply wp_fupd. rewrite /GhostOp.
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|]. iIntros "£ _".
    iDestruct (lc_weaken (S d + 1) with "£") as "£"; [rewrite /advance_credits; lia|].
    iDestruct (guards_transitive_right with "Alv Shr") as "G1".
    iMod (guards_open_later with "G1 L") as "Open"; [solve_ndisj|].
    iMod (lc_fupd_elim_laterN with "£ Open") as ">[[Hx #Hinv] Close]".
    iMod (ra_validate with "Hinv Hx") as "[Hx #Hvalid]"; [solve_ndisj|].
    iMod ("Close" with "[$Hx $Hinv]") as "$".
    wp_seq. wp_seq.
    eapply (tac_wp_pure []); [apply (pure_mk_tuple [])|done|tc_solve|simpl; iApply wp_value].
    iModIntro. iExists -[]. iSplit; [done|].
    iCombine "Obs Hvalid" as "Obs'". iApply (proph_obs_impl with "Obs'").
    intros π [Hpost ?]. by apply Hpost.
  Qed.

  Lemma typed_rab_join_shared_to_target κ (p1 p2 p : path) (ty : type 𝔄) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
      +[p1 ◁ᵥ &shrb{κ} raty; p2 ◁ᵥ &shrb{κ} raty; p ◁ᵥ ghost_ty ty]
      (Skip ;; p1) (λ v, +[v ◁ᵥ &shrb{κ} raty])
      (λ post '-[(l1, (γ1, x1)); (_, (γ2, x2)); y], λ mask π,
        γ1 = γ2 ∧ vra_conjunct_shared VRA x1 x2 y ∧ post -[(l1, (γ1, y))] mask π).
  Proof.
    iIntros (Alv tid post mask iκs [[l1 [γ1 x1]] [[l2 [γ2 x2]] [y []]]])
      "_ #TIME #PROPH _ #E L $ (p1 & p2 & _ & _) #Obs".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & %Hy & _)"; [done|].
    iDestruct "p1" as (vp1 Hp1 w1 d1 [-> Hw1]) "[#⧖1 #Own1]". simpl in Hw1. simplify_eq.
    iDestruct "p2" as (vp2 Hp2 w2 d2 [-> Hw2]) "[#⧖2 #Own2]".
    destruct d1 as [|d1]; [done|]. destruct d2 as [|d2]; [done|].
    iDestruct (ra_shr_guard with "Own1") as "#Shr1".
    iDestruct (ra_shr_guard with "Own2") as "#Shr2".
    iDestruct (Alv with "L E") as "#Alv".
    set D := d1 `max` d2.
    iAssert (⧖(S D))%I as "#⧖D".
    { rewrite /D Nat.succ_max_distr persistent_time_receipt_sep. by iFrame "⧖1 ⧖2". }
    iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME ⧖D"); [done|]. iIntros "£ _".
    iDestruct (lc_weaken (S D + 1) with "£") as "£"; [rewrite /advance_credits; lia|].
    iDestruct (lguards_weaken_later _ _ _ _ (S D + 1) with "Shr1") as "Shr1'"; [lia|].
    iDestruct (lguards_weaken_later _ _ _ _ (S D + 1) with "Shr2") as "Shr2'"; [lia|].
    iMod (ra_shr_inv with "L Alv Shr1' £") as "[L #Hinv]"; [solve_ndisj|].
    have Hand : ∀ Q1 Q2 : iProp Σ,
      (own γ1 (◯ VraCar VRA x1) ∗ Q1) ∧ (own γ1 (◯ VraCar VRA x2) ∗ Q2) ⊢
        own γ1 (◯ VraCar VRA y).
    { iIntros (Q1 Q2) "H".
      iApply (and_own_discrete_ucmra_specific with "[H]").
      { by apply vra_auth_frag_conjunct_shared. }
      iSplit; [iDestruct "H" as "[[$ _] _]"|iDestruct "H" as "[_ [$ _]]"]. }
    iPoseProof (@guards_and_own _ _ _ _ _ _ (authUR (vra_carUR VRA)) _ γ1 (◯ VraCar VRA y)
      with "Shr1' Shr2'") as "Shr3"; first apply Hand.
    iPoseProof (guards_include_pers (ra_inv VRA γ1) with "Hinv Shr3") as "Shr4".
    iFrame "L". wp_seq. wp_seq. iApply (wp_wand with "[]"); [by iApply wp_eval_path|].
    iIntros (? ->). iModIntro.
    iExists -[(l1, (γ1, y))]. iSplitL.
    - iSplit; [|done]. iApply (ra_shr_own with "⧖D Shr4").
    - iApply (proph_obs_impl with "Obs"). by intros π (_ & _ & ?).
  Qed.

  Lemma typed_rab_weaken κ (p1 p2 : path) (ty : type 𝔄) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I +[p1 ◁ᵥ &shrb{κ} raty; p2 ◁ᵥ ghost_ty ty]
      (Skip ;; p1) (λ v, +[v ◁ᵥ &shrb{κ} raty])
      (λ post '-[(l, (γ, x)); y], λ mask π, vra_incl VRA y x ∧ post -[(l, (γ, y))] mask π).
  Proof.
    iIntros (Alv tid post mask iκs [[l [γ x]] [y []]])
      "_ #TIME #PROPH _ #E L $ (p1 & _ & _) #Obs".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & %Hincl & _)"; [done|].
    iDestruct "p1" as (vp1 Hp1 w1 d1 [-> Hw1]) "[#⧖1 #Own1]". simpl in Hw1. simplify_eq.
    destruct d1 as [|d1]; [done|].
    iDestruct (ra_shr_guard with "Own1") as "#Shr".
    iDestruct (Alv with "L E") as "#Alv".
    iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME ⧖1"); [done|]. iIntros "£ _".
    iDestruct (lc_weaken (S d1 + 1) with "£") as "£"; [rewrite /advance_credits; lia|].
    iMod (ra_shr_inv with "L Alv Shr £") as "[L #Hinv]"; [solve_ndisj|].
    iPoseProof (@guards_and_own _ _ _ _ _ _ (authUR (vra_carUR VRA)) _ γ (◯ VraCar VRA y)
      with "Shr Shr") as "Shr'".
    { iIntros "[[H _] _]". iApply (own_mono with "H").
      by apply auth_frag_mono, vra_car_included. }
    iPoseProof (guards_include_pers (ra_inv VRA γ) with "Hinv Shr'") as "Shr''".
    iFrame "L". wp_seq. wp_seq. iApply (wp_wand with "[]"); [by iApply wp_eval_path|].
    iIntros (? ->). iModIntro.
    iExists -[(l, (γ, y))]. iSplitL.
    - iSplit; [|done]. iApply (ra_shr_own with "⧖1 Shr''").
    - iApply (proph_obs_impl with "Obs"). by intros π [_ ?].
  Qed.

  Lemma typed_rab_update_with_shr κ (self other new_value : path) (ty : type 𝔄) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
      +[self ◁ᵥ raty; other ◁ᵥ &shrb{κ} raty; new_value ◁ᵥ ghost_ty ty]
      (RAb_UpdateWithShr: self other new_value) (λ out, +[out ◁ᵥ raty])
      (λ post '-[(γ1, x); (_, (γ2, y)); z], λ mask π, γ1 = γ2 ∧
        vra_frame_preserving_update VRA (vra_op VRA x y) (vra_op VRA z y) π ∧
        post -[(γ1, z)] mask π).
  Proof.
    iIntros (Alv tid post mask iκs [[γ1 x] [[l [γ2 y]] [z []]]])
      "_ #TIME #PROPH _ #E L $ (p1 & p2 & _ & _) #Obs".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & _)"; [done|].
    iDestruct "p1" as (vp1 Hp1 w1 d1 [-> Hw1]) "[#⧖1 [Hx _]]".
    iDestruct "p2" as (vp2 Hp2 w2 d2 [-> Hw2]) "[#⧖2 #Own2]".
    destruct d2 as [|d2]; [done|].
    iDestruct (ra_shr_guard with "Own2") as "#Shr".
    iDestruct (Alv with "L E") as "#Alv".
    iApply wp_fupd. rewrite /GhostOp.
    iApply (wp_persistent_time_receipt with "TIME ⧖2"); [done|]. iIntros "£ _".
    iDestruct (lc_weaken (S d2 + 1) with "£") as "£"; [rewrite /advance_credits; lia|].
    iDestruct (guards_transitive_right with "Alv Shr") as "G1".
    iMod (guards_open_later with "G1 L") as "Open"; [solve_ndisj|].
    iMod (lc_fupd_elim_laterN with "£ Open") as ">[[Hy #Hinv] Close]".
    iAssert (own γ1 (◯ VraCar VRA (vra_op VRA x y))) with "[Hx Hy]" as "Hxy".
    { rewrite -vra_car_op_eq auth_frag_op own_op. iFrame. }
    iMod (ra_update VRA _ γ1 (vra_op VRA x y) (vra_op VRA z y) with "Hinv Hxy [Obs]") as "Hxy";
      first solve_ndisj.
    { iApply (proph_obs_impl with "Obs"). by intros π [_ [? _]]. }
    rewrite -vra_car_op_eq auth_frag_op own_op. iDestruct "Hxy" as "[Hz Hy]".
    iMod ("Close" with "[$Hy $Hinv]") as "$".
    wp_seq. wp_seq.
    eapply (tac_wp_pure []); [apply (pure_mk_tuple [])|done|tc_solve|simpl; iApply wp_value].
    iModIntro. iExists -[(γ1, z)]. iSplitL.
    - iSplit; [|done]. by iApply (ra_val_own with "⧖1 Hz Hinv").
    - iApply (proph_obs_impl with "Obs"). by intros π (_ & _ & ?).
  Qed.

  Lemma typed_rab_update_with_shr_non_det κ n (self other new_values : path)
      (ty : type (vecₛ 𝔄 n)) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
      +[self ◁ᵥ raty; other ◁ᵥ &shrb{κ} raty; new_values ◁ᵥ ghost_ty ty]
      (RAb_UpdateWithShr: self other new_values) (λ out, +[out ◁ᵥ raty])
      (λ post '-[(γ1, x); (_, (γ2, y)); zs], λ mask π, γ1 = γ2 ∧
        vra_frame_preserving_update_nondeterministic VRA (vra_op VRA x y)
          (λ w, ∃ z, z ∈ vec_to_list zs ∧ w = vra_op VRA z y) ∧
        Forall (λ z, post -[(γ1, z)] mask π) (vec_to_list zs)).
  Proof.
    iIntros (Alv tid post mask iκs [[γ1 x] [[l [γ2 y]] [zs []]]])
      "_ #TIME #PROPH _ #E L $ (p1 & p2 & _ & _) #Obs".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & %Hupd & _)"; [done|].
    iDestruct "p1" as (vp1 Hp1 w1 d1 [-> Hw1]) "[#⧖1 [Hx _]]".
    iDestruct "p2" as (vp2 Hp2 w2 d2 [-> Hw2]) "[#⧖2 #Own2]".
    destruct d2 as [|d2]; [done|].
    iDestruct (ra_shr_guard with "Own2") as "#Shr".
    iDestruct (Alv with "L E") as "#Alv".
    iApply wp_fupd. rewrite /GhostOp.
    iApply (wp_persistent_time_receipt with "TIME ⧖2"); [done|]. iIntros "£ _".
    iDestruct (lc_weaken (S d2 + 1) with "£") as "£"; [rewrite /advance_credits; lia|].
    iDestruct (guards_transitive_right with "Alv Shr") as "G1".
    iMod (guards_open_later with "G1 L") as "Open"; [solve_ndisj|].
    iMod (lc_fupd_elim_laterN with "£ Open") as ">[[Hy #Hinv] Close]".
    iAssert (own γ1 (◯ VraCar VRA (vra_op VRA x y))) with "[Hx Hy]" as "Hxy".
    { rewrite -vra_car_op_eq auth_frag_op own_op. iFrame. }
    iMod (ra_update_nondeterministic VRA _ γ1 _ _ ltac:(solve_ndisj) Hupd with "Hinv Hxy")
      as (w) "[%Hin Hxy]".
    destruct Hin as (z & Hz & ->).
    rewrite -vra_car_op_eq auth_frag_op own_op. iDestruct "Hxy" as "[Hz Hy]".
    iMod ("Close" with "[$Hy $Hinv]") as "$".
    wp_seq. wp_seq.
    eapply (tac_wp_pure []); [apply (pure_mk_tuple [])|done|tc_solve|simpl; iApply wp_value].
    iModIntro. iExists -[(γ1, z)]. iSplitL.
    - iSplit; [|done]. by iApply (ra_val_own with "⧖1 Hz Hinv").
    - iApply (proph_obs_impl with "Obs"). intros π' (_ & _ & Hpost).
      rewrite Forall_forall in Hpost. by apply Hpost.
  Qed.
End RA_bytes.
