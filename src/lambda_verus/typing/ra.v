From iris.proofmode Require Import proofmode.
From lrust.typing Require Import lft_contexts.
From lrust.typing Require Import type programs ghost value_ctx own shr_bor.
From guarding Require Import guard tactics guard_later_pers own_and.
From guarding.internal Require Import auth_frag_util.
From iris.algebra Require Import auth.
From lrust.lifetime Require Import lifetime_full.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

(** * Verus-style resource algebras *)

(** A [VerusRA] has the capabilities of Verus's [PCM] trait
    (verus/source/vstd/pcm.rs): validity, op, unit, and the laws
    [closed_under_incl], [commutative], [associative], [op_unit], and [unit_valid].
    Unlike in Verus, validity is _prophetic_: it may depend on the prophecy assignment. *)
Record VerusRA (A : Type) := {
  vra_valid : A → proph_asn → Prop;
  vra_op : A → A → A;
  vra_unit : A;
  vra_closed_under_incl a b π : vra_valid (vra_op a b) π → vra_valid a π;
  vra_commutative a b : vra_op a b = vra_op b a;
  vra_associative a b c : vra_op a (vra_op b c) = vra_op (vra_op a b) c;
  vra_op_unit a : vra_op a vra_unit = a;
  vra_unit_valid π : vra_valid vra_unit π;
}.
Global Arguments vra_valid {_} _ _.
Global Arguments vra_op {_} _ _ _.
Global Arguments vra_unit {_} _.
Global Arguments vra_closed_under_incl {_} _ _ _ _.
Global Arguments vra_commutative {_} _ _ _.
Global Arguments vra_associative {_} _ _ _ _.
Global Arguments vra_op_unit {_} _ _.
Global Arguments vra_unit_valid {_} _ _.

Section VerusRADefs.
  Context {A : Type} (P : VerusRA A).

  (** These correspond to [incl], [conjunct_shared], [frame_preserving_update], and
      [frame_preserving_update_nondeterministic] in vstd/pcm.rs, adapted to prophetic
      validity. *)
  Definition vra_incl (a b : A) := ∃ c, vra_op P a c = b.

  (** Since validity is prophetic, it cannot be used to justify combining shared
      resources, so unlike in Verus, there is no validity premise here. *)
  Definition vra_conjunct_shared (a b c : A) :=
    ∀ p, vra_incl a p → vra_incl b p → vra_incl c p.

  (** A frame-preserving update with respect to a given prophecy assignment. *)
  Definition vra_frame_preserving_update (a b : A) (π : proph_asn) :=
    ∀ c, vra_valid P (vra_op P a c) π → vra_valid P (vra_op P b c) π.

  (** For nondeterministic updates, the new value is chosen at the time of the update,
      so it can depend on the frame [c] but not on the prophecy assignment. *)
  Definition vra_frame_preserving_update_nondeterministic (a : A) (bs : A → Prop) :=
    ∀ c, ∃ b, bs b ∧ ∀ π, vra_valid P (vra_op P a c) π → vra_valid P (vra_op P b c) π.
End VerusRADefs.

(** The Ucmra underlying a [VerusRA]. Its validity is trivial; the (prophetic) validity
    of the [VerusRA] is tracked separately, by an invariant holding the authoritative
    element (see [ra_inv]). The carrier is wrapped in a record so that the instances
    below do not interfere with any existing instances on [A]. *)
Record vra_car {A : Type} (P : VerusRA A) := VraCar { vra_val : A }.
Global Arguments VraCar {_} _ _.
Global Arguments vra_val {_ _} _.

Section VerusRACmra.
  Context {A : Type} (P : VerusRA A).
  Implicit Types x y z : vra_car P.

  Global Instance vra_car_op : Op (vra_car P) := λ x y, VraCar P (vra_op P (vra_val x) (vra_val y)).
  Global Instance vra_car_pcore : PCore (vra_car P) := λ _, Some (VraCar P (vra_unit P)).
  Global Instance vra_car_valid : Valid (vra_car P) := λ x, True.
  Global Instance vra_car_unit : Unit (vra_car P) := VraCar P (vra_unit P).

  Canonical Structure vra_carO := leibnizO (vra_car P).

  Local Lemma vra_car_unit_left_id x : ε ⋅ x = x.
  Proof.
    destruct x as [x]. rewrite /op /vra_car_op /=.
    by rewrite vra_commutative vra_op_unit.
  Qed.

  Lemma vra_ra_mixin : RAMixin (vra_car P).
  Proof.
    split.
    - intros x y z ->. done.
    - intros x y cx -> ?. by exists cx.
    - intros x y ->. done.
    - intros [x] [y] [z]. rewrite /op /vra_car_op /= /equiv /ofe_equiv /=.
      by rewrite vra_associative.
    - intros [x] [y]. rewrite /op /vra_car_op /= /equiv /ofe_equiv /=.
      by rewrite vra_commutative.
    - rewrite /pcore /vra_car_pcore. intros x cx [= <-]. apply vra_car_unit_left_id.
    - rewrite /pcore /vra_car_pcore. intros x cx [= <-]. done.
    - rewrite /pcore /vra_car_pcore. intros x y cx _ [= <-].
      eexists. split; first done. exists ε. by rewrite vra_car_unit_left_id.
    - done.
  Qed.
  Canonical Structure vra_carR := discreteR (vra_car P) vra_ra_mixin.

  Global Instance vra_car_cmra_discrete : CmraDiscrete vra_carR.
  Proof. apply discrete_cmra_discrete. Qed.

  Global Instance vra_car_cmra_total : CmraTotal vra_carR.
  Proof. intros x. by eexists. Qed.

  Lemma vra_ucmra_mixin : UcmraMixin (vra_car P).
  Proof.
    split.
    - done.
    - intros x. apply vra_car_unit_left_id.
    - done.
  Qed.
  Canonical Structure vra_carUR := Ucmra (vra_car P) vra_ucmra_mixin.

  Lemma vra_car_op_eq a b : VraCar P a ⋅ VraCar P b = VraCar P (vra_op P a b).
  Proof. done. Qed.

  Lemma vra_car_included a b : VraCar P a ≼ VraCar P b ↔ vra_incl P a b.
  Proof.
    split.
    - intros [[c] Hc]. exists c. by inversion Hc.
    - intros [c Hc]. exists (VraCar P c). by rewrite vra_car_op_eq Hc.
  Qed.

  Lemma vra_car_assoc x y z : x ⋅ (y ⋅ z) = (x ⋅ y) ⋅ z.
  Proof. destruct x, y, z. by rewrite !vra_car_op_eq vra_associative. Qed.

  (** Update the fragment [x] to [y], where [y] may be chosen depending on the frame [c],
      i.e., the rest of the authoritative element. *)
  Lemma vra_auth_frame_updateP (t x : vra_car P) (R : vra_car P → vra_car P → Prop) :
    (∀ c, t = x ⋅ c → ∃ y, R c y) →
    ● t ⋅ ◯ x ~~>: λ r, ∃ c y, t = x ⋅ c ∧ R c y ∧ r = ● (y ⋅ c) ⋅ ◯ y.
  Proof.
    intros HR.
    eapply cmra_updateP_weaken.
    { eapply view_updateP with (Pab := λ a' b', ∃ c y, t = x ⋅ c ∧ R c y ∧ a' = y ⋅ c ∧ b' = y).
      intros n bf [[g Hg] _].
      assert (t = x ⋅ (bf ⋅ g)) as Ht.
      { rewrite vra_car_assoc. exact Hg. }
      destruct (HR _ Ht) as [y Hy].
      exists (y ⋅ (bf ⋅ g)), y. split; first by eauto 10.
      split; last done. exists g. by rewrite vra_car_assoc. }
    intros r (a' & b' & -> & c & y & ? & ? & -> & ->). eauto 10.
  Qed.

  Lemma vra_auth_frag_conjunct_shared (x1 x2 y : A) :
    vra_conjunct_shared P x1 x2 y →
    ∀ w : authUR vra_carUR, ✓ w →
      ◯ VraCar P x1 ≼ w → ◯ VraCar P x2 ≼ w → ◯ VraCar P y ≼ w.
  Proof.
    intros Hy w _ H1 H2.
    destruct (view_frag_included_frag w) as ([b] & Hf & Hle).
    etrans; last exact Hle.
    apply auth_frag_mono, vra_car_included, Hy; apply vra_car_included, Hf; done.
  Qed.
End VerusRACmra.

Definition raN : namespace := nroot .@ "verus_ra".

Section Ra.

  Context `{!typeG Σ}.
  Context {𝔄 : syn_type} (VRA : VerusRA (~~𝔄)).
  Context `{G2: !inG Σ (authUR (vra_carUR VRA))}.

  Hypothesis (𝔄_const  : ∀ (x : ~~𝔄) π1 π2 , @vπ 𝔄 x π1 = @vπ 𝔄 x π2).

  (** The invariant holds the authoritative element, together with an observation
      that it is valid. *)
  Definition ra_inv (γ : gname) : iProp Σ :=
    inv raN (∃ t, own γ (● VraCar VRA t) ∗ ⟨π, vra_valid VRA t π⟩).

  Global Instance ra_inv_persistent γ : Persistent (ra_inv γ) := _.

  Set Printing Coercions.
  Program Definition ra_ty  : type (ghostₛ (positiveₛ * 𝔄)) :=
    ty_of_gt ({|
          gt_gho v tid :=
            let '(γ, m) := v in
            own γ (◯ VraCar VRA m) ∗ ra_inv γ;
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

  (* Definition ra_ty  : type (at_locₛ (positiveₛ* 𝔄)) := own_ptr 0 (ra_inner). *)

  Global Instance ra_send : Send ra_ty.
  Proof.
    intros. split; trivial.
     - iIntros. iApply step_fupdN_intro; first done. iNext.
       iExists x, 0%nat. iModIntro. iFrame. simpl.
       replace (d0 + 0)%nat with d0 by lia. iFrame "#". done.
  Qed.

  Global Instance ra_sync : Sync ra_ty.
  Proof. apply sync_default; [done|]. move => ??[??]??; split => //=. Qed.

  Lemma ra_resolve E L : resolve E L ra_ty (const (const True)).
  Proof. apply resolve_just. Qed.

  Lemma ra_alloc E x :
    ⟨π, vra_valid VRA x π⟩ ={E}=∗ ∃ γ, own γ (◯ VraCar VRA x) ∗ ra_inv γ.
  Proof.
    iIntros "#Obs".
    iMod (own_alloc (● VraCar VRA x ⋅ ◯ VraCar VRA x)) as (γ) "[Hauth Hfrag]".
    { by apply auth_both_valid_discrete. }
    iMod (inv_alloc raN _ (∃ t, own γ (● VraCar VRA t) ∗ ⟨π, vra_valid VRA t π⟩)
      with "[Hauth]") as "#Hinv".
    { iNext. iExists x. iFrame "∗#". }
    iModIntro. iExists γ. iFrame "∗#".
  Qed.

  Lemma ra_validate E γ x :
    ↑raN ⊆ E →
    ra_inv γ -∗ own γ (◯ VraCar VRA x) ={E}=∗
      own γ (◯ VraCar VRA x) ∗ ⟨π, vra_valid VRA x π⟩.
  Proof.
    iIntros (?) "#Hinv Hfrag".
    iInv "Hinv" as ">(%t & Hauth & #Hobs)".
    iDestruct (own_valid_2 with "Hauth Hfrag") as %[Hincl _]%auth_both_valid_discrete.
    apply vra_car_included in Hincl as [c <-].
    iModIntro. iSplitL "Hauth".
    { iNext. iExists _. iFrame "∗#". }
    iFrame. iModIntro.
    iApply (proph_obs_impl with "Hobs").
    intros π. apply vra_closed_under_incl.
  Qed.

  (** Update the fragment [x] to some [y] related to the frame [c]
      (i.e., the rest of the authoritative element) by [R]. *)
  Lemma ra_updateP E γ x (R : ~~𝔄 → ~~𝔄 → Prop) :
    ↑raN ⊆ E →
    (∀ c, ∃ y, R c y) →
    ra_inv γ -∗ own γ (◯ VraCar VRA x) -∗
    ⟨π, ∀ c y, R c y → vra_valid VRA (vra_op VRA x c) π → vra_valid VRA (vra_op VRA y c) π⟩
    ={E}=∗ ∃ c y, ⌜R c y⌝ ∗ own γ (◯ VraCar VRA y).
  Proof.
    iIntros (? HR) "#Hinv Hfrag #Hupd".
    iInv "Hinv" as ">(%t & Hauth & #Hobs)".
    iCombine "Hauth Hfrag" as "Hown".
    assert (● VraCar VRA t ⋅ ◯ VraCar VRA x ~~>: λ r, ∃ c y,
      VraCar VRA t = VraCar VRA x ⋅ c ∧ R (vra_val c) (vra_val y) ∧ r = ● (y ⋅ c) ⋅ ◯ y)
      as Hupd'.
    { apply vra_auth_frame_updateP. intros [c] _. destruct (HR c) as [y Hy].
      by exists (VraCar VRA y). }
    iMod (own_updateP _ _ _ Hupd' with "Hown") as (r) "[%Hr Hown]".
    destruct Hr as ([c] & [y] & Ht & Hy & ->). simpl in Hy.
    rewrite vra_car_op_eq in Ht. injection Ht as ->.
    rewrite own_op. iDestruct "Hown" as "[Hauth Hfrag]".
    iModIntro. iSplitL "Hauth".
    { iNext. iExists (vra_op VRA y c). iFrame "Hauth".
      iDestruct (proph_obs_and with "Hobs Hupd") as "Hobs'".
      iApply (proph_obs_impl with "Hobs'").
      intros π [Hv Hu]. by apply Hu. }
    iModIntro. iExists c, y. by iFrame.
  Qed.

  Lemma ra_update E γ x y :
    ↑raN ⊆ E →
    ra_inv γ -∗ own γ (◯ VraCar VRA x) -∗
    ⟨π, vra_frame_preserving_update VRA x y π⟩ ={E}=∗ own γ (◯ VraCar VRA y).
  Proof.
    iIntros (?) "#Hinv Hfrag #Hupd".
    iMod (ra_updateP E γ x (λ _ y', y' = y) with "Hinv Hfrag [Hupd]") as (c y') "[-> $]".
    - done.
    - eauto.
    - iApply (proph_obs_impl with "Hupd"). intros π Hupd c y' ->. apply Hupd.
    - done.
  Qed.

  Lemma ra_update_nondeterministic E γ x (bs : ~~𝔄 → Prop) :
    ↑raN ⊆ E →
    vra_frame_preserving_update_nondeterministic VRA x bs →
    ra_inv γ -∗ own γ (◯ VraCar VRA x) ={E}=∗ ∃ y, ⌜bs y⌝ ∗ own γ (◯ VraCar VRA y).
  Proof.
    iIntros (? Hupd) "#Hinv Hfrag".
    iMod (ra_updateP E γ x
      (λ c y, bs y ∧ ∀ π, vra_valid VRA (vra_op VRA x c) π → vra_valid VRA (vra_op VRA y c) π)
      with "Hinv Hfrag []") as (c y) "[[%Hy _] Hfrag]".
    - done.
    - done.
    - iApply proph_obs_true. intros π c y [_ Hu]. apply Hu.
    - iModIntro. iExists y. by iFrame.
  Qed.

End Ra.

(** * Verus-style resource algebras on the byte layer

The typing rules of [typing/ra.v], with the ghost values as MiniRust values ([◁ᵥ]): a
ghost value ([ra_ty], [ghost_ty]) is zero-sized, and its MiniRust value is the empty tuple,
so it is a value (not a box of size [0], [own_ptr 0], as in [typing/ra.v]). Shared
references are [&shrb]. The resource algebra and its ghost type ([ra_ty], [ra_inv] and
the lemmas [ra_alloc], [ra_validate], [ra_update] etc.) are those of [typing/ra.v]. A
ghost operation is a no-op that returns the empty tuple ([GhostOp]). *)

Notation "RA_Alloc: p" := GhostOp (at level 102, p at level 150): expr_scope.
Notation "RA_Join: p1 p2" := GhostOp (at level 102, p1, p2 at level 1): expr_scope.
Notation "RA_Split: p p1 p2" := GhostOp (at level 102, p, p1, p2 at level 1): expr_scope.
Notation "RA_Unit:" := GhostOp : expr_scope.
Notation "RA_Update: self p" := GhostOp (at level 102, self, p at level 1): expr_scope.
Notation "RA_Validate: self" := GhostOp (at level 102, self at level 1): expr_scope.
Notation "RA_UpdateWithShr: self other new_value" := GhostOp
  (at level 102, self, other, new_value at level 1): expr_scope.

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
    tctx_elt_interp tid (MLitV (VPtr l) ◁ᵥ &shr{κ} raty) (l, (γ, x)).
  Proof.
    iIntros "⧖ #G". rewrite tctx_val_val. iExists (S d). iFrame "⧖". iSplit; [done|].
    rewrite /= /by_succ. iSplit; [iApply shr_bytes_own_zst; [by rewrite /ty_bsize -ty_mty_eq|done]|].
    iSplit; [|done]. by iApply (ty_shr_default_from_guard raty).
  Qed.

  Lemma typed_ra_alloc (p : path) (ty : type 𝔄) E L I :
    typed_instr E L I +[p ◁ᵥ ghost_ty ty] (RA_Alloc: p) (λ v, +[v ◁ᵥ raty])
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

  Lemma typed_ra_join (p1 p2 : path) E L I :
    typed_instr E L I +[p1 ◁ᵥ raty; p2 ◁ᵥ raty] (RA_Join: p1 p2) (λ v, +[v ◁ᵥ raty])
      (λ post '-[(γ1, x1); (γ2, x2)], λ mask π,
        γ1 = γ2 ∧ post -[(γ1, vra_op VRA x1 x2)] mask π).
  Proof.
    iIntros (tid post mask iκs [[γ1 x1] [[γ2 x2] []]]) "_ _ #PROPH _ _ $ $ (p1 & p2 & _) #Obs".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & _)"; [done|].
    iDestruct "p1" as (vp1 Hp1 w1 d1 [-> Hw1]) "[#⧖1 [Hx1 #Hinv]]".
    iDestruct "p2" as (vp2 Hp2 w2 d2 [-> Hw2]) "[#⧖2 [Hx2 _]]".
    iAssert (own γ1 (◯ VraCar VRA (vra_op VRA x1 x2))) with "[Hx1 Hx2]" as "Hx".
    { rewrite -vra_car_op_eq auth_frag_op own_op. iFrame. }
    iApply wp_ghost_op. iIntros "!> !>". iExists -[(γ1, vra_op VRA x1 x2)].
    iSplitL; [iSplit; [by iApply (ra_val_own with "⧖1 Hx Hinv")|done]|].
    iApply (proph_obs_impl with "Obs"). by intros π [_ ?].
  Qed.

  (** Splitting: [self] keeps the first part, the result is the second part. (In
      [typing/ra.v], the result is a box of the pair of the two parts.) *)
  Lemma typed_ra_split (self p1 p2 : path) (ty : type 𝔄) E L I :
    typed_instr E L I +[self ◁ᵥ raty; p1 ◁ᵥ ghost_ty ty; p2 ◁ᵥ ghost_ty ty]
      (RA_Split: self p1 p2) (λ v, +[self ◁ᵥ raty; v ◁ᵥ raty])
      (λ post '-[(γ, x); x1; x2], λ mask π,
        x = vra_op VRA x1 x2 ∧ post -[(γ, x1); (γ, x2)] mask π).
  Proof.
    iIntros (tid post mask iκs [[γ x] [x1 [x2 []]]]) "_ _ #PROPH _ _ $ $ (p & _ & _ & _) #Obs".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & -> & _)"; [done|].
    iDestruct "p" as (vp Hp w d [-> Hw]) "[#⧖ [Hx #Hinv]]". simpl in Hw. simplify_eq.
    rewrite -vra_car_op_eq auth_frag_op. iDestruct "Hx" as "[Hx1 Hx2]".
    iApply wp_ghost_op. iIntros "!> !>". iExists -[(γ, x1); (γ, x2)].
    iSplitL; [|iApply (proph_obs_impl with "Obs"); by intros π [_ ?]].
    iSplitL "Hx1"; [|iSplit; [by iApply (ra_val_own with "⧖ Hx2 Hinv")|done]].
    rewrite -(tctx_val_intro_sep _ _ _ _ (VTuple []) d); [|done|done]. iFrame "⧖". simpl. by iFrame.
  Qed.

  Lemma typed_ra_unit E L I :
    typed_instr E L I +[] (RA_Unit:) (λ v, +[v ◁ᵥ raty])
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

  Lemma typed_ra_update (self p : path) (ty : type 𝔄) E L I :
    typed_instr E L I +[self ◁ᵥ raty; p ◁ᵥ ghost_ty ty] (RA_Update: self p)
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

  Lemma typed_ra_update_nondeterministic (self p : path) (n : nat) (ty : type (vecₛ 𝔄 n)) E L I :
    typed_instr E L I +[self ◁ᵥ raty; p ◁ᵥ ghost_ty ty] (RA_Update: self p)
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
    (&shr{κ} raty).(ty_gho_own) (l, (γ, x)) (S d) (S d) tid -∗
    (@[κ] &&{↑NllftG; S d + 1}&&> own γ (◯ VraCar VRA x) ∗ ra_inv VRA γ).
  Proof.
    iIntros "(_ & #Shr & _)". iDestruct (ty_shr_default_to_guard raty with "Shr") as "#G";
      [done|].
    iApply (lguards_weaken_later with "G"). lia.
  Qed.

  (** Opening the guard of a shared reference, to get the invariant. *)
  Local Lemma ra_shr_inv L κ γ x n G :
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

  Lemma typed_ra_validate κ (self : path) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I +[self ◁ᵥ &shr{κ} raty] (RA_Validate: self) (λ _, +[])
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
    iAssert (|={⊤ ∖ ↑advN}=> llctx_interp L ∗ ⟨π, vra_valid VRA x π⟩)%I
      with "[L £]" as ">[$ #Hvalid]".
    { iMod (guards_open_later with "G1 L") as "Open"; [solve_ndisj|].
      iMod (lc_fupd_elim_laterN with "£ Open") as ">[[Hx #Hinv] Close]".
      iMod (ra_validate with "Hinv Hx") as "[Hx #Hvalid]"; [solve_ndisj|].
      iMod ("Close" with "[$Hx $Hinv]") as "$". by iModIntro. }
    wp_seq. wp_seq.
    eapply (tac_wp_pure []); [apply (pure_mk_tuple [])|done|tc_solve|simpl; iApply wp_value].
    iModIntro. iExists -[]. iSplit; [done|].
    iCombine "Obs Hvalid" as "Obs'". iApply (proph_obs_impl with "Obs'").
    intros π [Hpost ?]. by apply Hpost.
  Qed.

  Lemma typed_ra_join_shared_to_target κ (p1 p2 p : path) (ty : type 𝔄) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
      +[p1 ◁ᵥ &shr{κ} raty; p2 ◁ᵥ &shr{κ} raty; p ◁ᵥ ghost_ty ty]
      (GhostRet [p1]) (λ v, +[v ◁ᵥ &shr{κ} raty])
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
    iFrame "L". wp_bind p1. iApply (wp_wand with "[]"); [by iApply wp_eval_path|].
    iIntros (? ->). wp_rec. iModIntro.
    iExists -[(l1, (γ1, y))]. iSplitL.
    - iSplit; [|done]. iApply (ra_shr_own with "⧖D Shr4").
    - iApply (proph_obs_impl with "Obs"). by intros π (_ & _ & ?).
  Qed.

  Lemma typed_ra_weaken κ (p1 p2 : path) (ty : type 𝔄) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I +[p1 ◁ᵥ &shr{κ} raty; p2 ◁ᵥ ghost_ty ty]
      (GhostRet [p1]) (λ v, +[v ◁ᵥ &shr{κ} raty])
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
    iFrame "L". wp_bind p1. iApply (wp_wand with "[]"); [by iApply wp_eval_path|].
    iIntros (? ->). wp_rec. iModIntro.
    iExists -[(l, (γ, y))]. iSplitL.
    - iSplit; [|done]. iApply (ra_shr_own with "⧖1 Shr''").
    - iApply (proph_obs_impl with "Obs"). by intros π [_ ?].
  Qed.

  Lemma typed_ra_update_with_shr κ (self other new_value : path) (ty : type 𝔄) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
      +[self ◁ᵥ raty; other ◁ᵥ &shr{κ} raty; new_value ◁ᵥ ghost_ty ty]
      (RA_UpdateWithShr: self other new_value) (λ out, +[out ◁ᵥ raty])
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
    iAssert (|={⊤ ∖ ↑advN}=> llctx_interp L ∗ own γ1 (◯ VraCar VRA z) ∗ ra_inv VRA γ1)%I
      with "[L £ Hx]" as ">($ & Hz & #Hinv)".
    { iMod (guards_open_later with "G1 L") as "Open"; [solve_ndisj|].
      iMod (lc_fupd_elim_laterN with "£ Open") as ">[[Hy #Hinv] Close]".
      iAssert (own γ1 (◯ VraCar VRA (vra_op VRA x y))) with "[Hx Hy]" as "Hxy".
      { rewrite -vra_car_op_eq auth_frag_op own_op. iFrame. }
      iMod (ra_update VRA _ γ1 (vra_op VRA x y) (vra_op VRA z y) with "Hinv Hxy [Obs]") as "Hxy";
        first solve_ndisj.
      { iApply (proph_obs_impl with "Obs"). by intros π [_ [? _]]. }
      rewrite -vra_car_op_eq auth_frag_op own_op. iDestruct "Hxy" as "[Hz Hy]".
      iMod ("Close" with "[$Hy $Hinv]") as "$". by iFrame "Hz Hinv". }
    wp_seq. wp_seq.
    eapply (tac_wp_pure []); [apply (pure_mk_tuple [])|done|tc_solve|simpl; iApply wp_value].
    iModIntro. iExists -[(γ1, z)]. iSplitL.
    - iSplit; [|done]. by iApply (ra_val_own with "⧖1 Hz Hinv").
    - iApply (proph_obs_impl with "Obs"). by intros π (_ & _ & ?).
  Qed.

  Lemma typed_ra_update_with_shr_non_det κ n (self other new_values : path)
      (ty : type (vecₛ 𝔄 n)) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
      +[self ◁ᵥ raty; other ◁ᵥ &shr{κ} raty; new_values ◁ᵥ ghost_ty ty]
      (RA_UpdateWithShr: self other new_values) (λ out, +[out ◁ᵥ raty])
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
    iAssert (|={⊤ ∖ ↑advN}=> llctx_interp L ∗ ∃ z, ⌜z ∈ vec_to_list zs⌝ ∗
        own γ1 (◯ VraCar VRA z) ∗ ra_inv VRA γ1)%I
      with "[L £ Hx]" as ">($ & %z & %Hz & Hz & #Hinv)".
    { iMod (guards_open_later with "G1 L") as "Open"; [solve_ndisj|].
      iMod (lc_fupd_elim_laterN with "£ Open") as ">[[Hy #Hinv] Close]".
      iAssert (own γ1 (◯ VraCar VRA (vra_op VRA x y))) with "[Hx Hy]" as "Hxy".
      { rewrite -vra_car_op_eq auth_frag_op own_op. iFrame. }
      iMod (ra_update_nondeterministic VRA (⊤ ∖ ↑advN ∖ ↑NllftG) γ1 _ _ ltac:(solve_ndisj) Hupd with "Hinv Hxy")
        as (w) "[%Hin Hxy]".
      destruct Hin as (z & Hz & ->).
      rewrite -vra_car_op_eq auth_frag_op own_op. iDestruct "Hxy" as "[Hz Hy]".
      iMod ("Close" with "[$Hy $Hinv]") as "$". iModIntro. iExists z. by iFrame "Hz Hinv". }
    wp_seq. wp_seq.
    eapply (tac_wp_pure []); [apply (pure_mk_tuple [])|done|tc_solve|simpl; iApply wp_value].
    iModIntro. iExists -[(γ1, z)]. iSplitL.
    - iSplit; [|done]. by iApply (ra_val_own with "⧖1 Hz Hinv").
    - iApply (proph_obs_impl with "Obs"). intros π' (_ & _ & Hpost).
      rewrite Forall_forall in Hpost. by apply Hpost.
  Qed.
End RA_bytes.
