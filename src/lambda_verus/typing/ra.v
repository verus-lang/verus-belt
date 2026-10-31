From iris.proofmode Require Import proofmode.
From lrust.typing Require Import lft_contexts.
From lrust.typing Require Import type programs ghost.
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
  Next Obligation. done. Qed.
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
