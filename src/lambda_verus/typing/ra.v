From iris.proofmode Require Import proofmode.
From lrust.typing Require Import lft_contexts.
From lrust.typing Require Import type programs ghost own product tracked shr_bor.
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

Notation "RA_Alloc: p" := (new [ #0])%E (at level 102, p at level 150): expr_scope.
Notation "RA_Join: p1 p2" := (new [ #0])%E (at level 102, p1, p2 at level 1): expr_scope.
Notation "RA_Split: p p1 p2" := (new [ #0])%E (at level 102, p, p1, p2 at level 1): expr_scope.
Notation "RA_Unit:" := (new [ #0])%E : expr_scope.
Notation "RA_Update: self p" := (new [ #0])%E (at level 102, self, p at level 1): expr_scope.
Notation "RA_Validate: self" := (new [ #0])%E (at level 102, self at level 1): expr_scope.

Section RA_type.

  Context `{!typeG Σ}.
  Context {𝔄 : syn_type} (VRA : VerusRA (~~𝔄)).
  Context `{G2: !inG Σ (authUR (vra_carUR VRA))}.
  Hypothesis (𝔄_const  : ∀ (x : ~~𝔄) π1 π2 , @vπ 𝔄 x π1 = @vπ 𝔄 x π2).

  Lemma typed_ra_alloc (p : path) (ty : type 𝔄) E L I :
    typed_instr E L I
    +[p ◁ own_ptr 0 (ghost_ty ty)]
    (RA_Alloc: p)
    (λ v, +[v ◁ own_ptr 0 (ra_ty VRA 𝔄_const)])
    (λ post '-[(_, x)], λ mask π, vra_valid VRA x π ∧ ∀ l γ, post -[(l, (γ, x))] mask π).
  Proof.
    move => tid postπ mask iκs xl.
    iIntros "LFT TIME #PROPH UNIQ E L $ TY #Obs" => /=.
    destruct xl as [[pl m] [ ]].
    iMod (ra_alloc VRA ⊤ m with "[]") as (γ) "[Hm #Hinv]".
    { iApply (proph_obs_impl with "Obs"). by intros π [? _]. }
    iApply wp_new=>//.
    iIntros "!>" (l) "(† & ↦) ".
    iExists -[(l, (γ, m))].
    iFrame "L".
    rewrite /ra_ty/tctx_elt_interp/ty_own/=.
    iDestruct "TY" as "((% & %d & % & Hd & Hgho & %Hphys) & _)".
    destruct d => //.
    iFrame "Hd".
    iSplitL.
    - iExists _; iSplitR => //=.
      repeat rewrite heap_mapsto_fancy_vec_nil.
      by iFrame "∗#".
    - iApply (proph_obs_impl with "Obs").
      intros π' [_ Hpost].
      apply Hpost.
  Qed.

  Lemma typed_ra_join (p1 p2 : path) E L I :
    typed_instr E L I
    +[p1 ◁ own_ptr 0 (ra_ty VRA 𝔄_const); p2 ◁ own_ptr 0 (ra_ty VRA 𝔄_const)]
    (RA_Join: p1 p2)
    (λ v, +[v ◁ own_ptr 0 (ra_ty VRA 𝔄_const)])
    (λ post '-[(_, (γ1, x1)); (_, (γ2, x2))], λ mask π, γ1 = γ2 ∧ ∀ l, post -[(l, (γ1, vra_op VRA x1 x2))] mask π).
  Proof.
    move => tid postπ mask iκs vπl.
    iIntros "LFT TIME #PROPH UNIQ E L $ TY #Obs" => /=.
    destruct vπl as [[pl1 [γ1 x1]] [[pl2 [γ2 x2]] []]].
    iMod (proph_obs_sat with "PROPH Obs") as "(%π & <- & %Hpost)" => //.
    iDestruct "TY" as "(H1 & H2 & _)".
    rewrite /ra_ty/tctx_elt_interp/ty_own/=.
    iDestruct "H1" as "(%l1 & %d1 & % & Hd1 & Hown1 & %Hphys1)".
    iDestruct "H2" as "(%l2 & %d2 & % & Hd2 & Hown2 & %Hphys2)".
    destruct d1,d2 => //.
    iDestruct "Hown1" as "(?&?&Hown1&#Hinv)".
    iDestruct "Hown2" as "(?&?&Hown2&_)".
    iCombine "Hown1 Hown2" as "Hown".
    iApply wp_new=>//.
    iIntros "!>" (l) "(† & ↦) ".
    iExists -[(l, (γ1, (vra_op VRA x1 x2)))].
    iFrame "L".
    iFrame "Hd1".
    iSplitL.
    - iExists _; iSplitR => //=.
      repeat rewrite heap_mapsto_fancy_vec_nil.
      by iFrame "∗#".
    - iApply (proph_obs_impl with "Obs").
      intros π' [_ ].
      apply H1.
  Qed.

  Lemma typed_ra_split (self p1 p2 : path) (ty : type 𝔄) E L I :
    typed_instr E L I
    +[self ◁ own_ptr 0 (ra_ty VRA 𝔄_const); p1 ◁ own_ptr 0 (ghost_ty ty); p2 ◁ own_ptr 0 (ghost_ty ty)] 
    (RA_Split: self p1 p2)
    (λ v, +[v ◁ own_ptr 0 (prod_ty (ra_ty VRA 𝔄_const) (ra_ty VRA 𝔄_const))])
    (λ post '-[(_, (γ, x)); (_, x1); (_, x2)], λ mask π, x = vra_op VRA x1 x2 ∧ ∀ l, post -[(l, ((γ, x1), (γ, x2)))] mask π).
  Proof.
    move => tid postπ mask iκs vπl.
    iIntros "LFT TIME #PROPH UNIQ E L $ TY #Obs" => /=.
    destruct vπl as [[pl [γ x]] [[pl1 x1] [[pl2 x2] []]]].
    simpl in x1, x2.
    iDestruct "TY" as "(H & _ & _ & _)".
    iDestruct "H" as "(%pl' & %d & % & #Hd & Hown & %Hphys)".
    injection Hphys => ? /=; subst pl'.
    destruct d => //.
    iMod (proph_obs_sat with "PROPH Obs") as "(%π & -> & %Hpost)" => //.
    iApply (wp_persistent_time_receipt with "TIME Hd"); [done|].
    iIntros "? #Hd'".
    iApply wp_new=>//.
    iIntros "!>" (l) "(† & ↦)".
    iExists -[(l, ((γ, x1), (γ, x2)))].
    iFrame "L".
    iFrame "Hd'".
    iSplitL.
    - iExists _; iSplitR => //=.
      iDestruct "Hown" as "(?&?&Hown&#Hinv)".
      rewrite -vra_car_op_eq auth_frag_op. iDestruct "Hown" as "[Hown1 Hown2]".
      iFrame "∗#".
      repeat rewrite heap_mapsto_fancy_vec_nil.
      rewrite /ty_own/=!heap_mapsto_vec_nil !freeable_util.freeable_sz_full.
      done.
    - iApply (proph_obs_impl with "Obs").
      intros π' [_ ].
      apply H0.
  Qed.

  Lemma typed_ra_unit E L I :
    typed_instr E L I
    +[]
    (RA_Unit:)
    (λ v, +[v ◁ own_ptr 0 (ra_ty VRA 𝔄_const)])
    (λ post '-[], λ mask π, ∀ l γ, post -[(l, (γ, vra_unit VRA))] mask π).
  Proof.
    move => tid postπ mask iκs vπl.
    iIntros "LFT TIME #PROPH UNIQ E L $ TY #Obs" => /=.
    iMod (ra_alloc VRA ⊤ (vra_unit VRA) with "[]") as (γ) "[Hm #Hinv]".
    { iApply proph_obs_true. intros π. apply vra_unit_valid. }
    iMod persistent_time_receipt_0 as "⧖".
    iApply (wp_persistent_time_receipt with "TIME ⧖"); [done|].
    iIntros "? #⧖".
    iApply wp_new=>//.
    iIntros "!>" (l) "(† & ↦)".
    iExists -[(l, (γ, vra_unit VRA))].
    iFrame "L".
    rewrite /ra_ty/tctx_elt_interp/ty_own/=.
    iFrame "⧖" => /=.
    iSplitL.
    - iExists _; iSplitR => //=.
      repeat rewrite heap_mapsto_fancy_vec_nil.
      by iFrame "∗#".
    - iApply (proph_obs_impl with "Obs").
      by destruct vπl.
  Qed.

  Lemma typed_ra_update (self p : path) (ty : type 𝔄) E L I :
    typed_instr E L I
    +[self ◁ own_ptr 0 (ra_ty VRA 𝔄_const); p ◁ own_ptr 0 (ghost_ty ty)]
    (RA_Update: self p)
    (λ v, +[v ◁ own_ptr 0 (ra_ty VRA 𝔄_const)])
    (λ post '-[(_, (γ, x)); (_, y)], λ mask π, vra_frame_preserving_update VRA x y π ∧ ∀ l, post -[(l, (γ, y))] mask π).
  Proof.
    move => tid postπ mask iκs vπl.
    iIntros "LFT TIME #PROPH UNIQ E L $ TY #Obs" => /=.
    destruct vπl as [[pl [γ x]] [[ply y] []]].
    simpl in y.
    iDestruct "TY" as "(H & ? & _)".
    iDestruct "H" as "(%pl' & %d & % & #Hd & Hown & %Hphys)".
    destruct d => //.
    iDestruct "Hown" as "(? & ? & Hown & #Hinv)".
    iApply wp_fupd.
    iApply wp_new=>//.
    iIntros "!>" (l) "(† & ↦)".
    iMod (ra_update VRA ⊤ γ x y with "Hinv Hown [Obs]") as "Hown"; first done.
    { iApply (proph_obs_impl with "Obs"). by intros π [? _]. }
    iExists -[(l, (γ, y))].
    iFrame "L".
    rewrite /ra_ty/tctx_elt_interp/ty_own/=.
    iFrame "Hd" => /=.
    iSplitL.
    - iExists _; iSplitR => //=.
      iFrame "∗#".
      iModIntro. done.
    - iApply (proph_obs_impl with "Obs").
      intros π' [_ ].
      apply H0.
  Qed.

  Lemma typed_ra_update_nondeterministic (self p : path) (n : nat) (ty : type (vecₛ 𝔄 n)) E L I :
    typed_instr E L I
    +[self ◁ own_ptr 0 (ra_ty VRA 𝔄_const); p ◁ own_ptr 0 (ghost_ty ty)]
    (RA_Update: self p)
    (λ v, +[v ◁ own_ptr 0 (ra_ty VRA 𝔄_const)])
    (λ post '-[(_, (γ, x)); (_, ys)], λ mask π,
        vra_frame_preserving_update_nondeterministic VRA x (λ y, y ∈ vec_to_list ys) ∧
        ∀ l, Forall (λ y, post -[(l, (γ, y))] mask π) (vec_to_list ys)).
  Proof.
    move => tid postπ mask iκs vπl.
    fold indep_interp_of_syn_type.
    iIntros "LFT TIME #PROPH UNIQ E L $ TY #Obs" => /=.
    destruct vπl as [[pl [γ x]] [[plys ys] []]].
    simpl in ys.
    iDestruct "TY" as "(H & _ & _)".
    iDestruct "H" as "(%pl' & %d & % & #Hd & Hown & %Hphys)".
    destruct d => //.
    iMod (proph_obs_sat with "PROPH Obs") as "(%π & %Hupd & _)" => //=.
    iDestruct "Hown" as "(? & ? & Hown & #Hinv)".
    iApply wp_fupd.
    iApply wp_new=>//.
    iIntros "!>" (l) "(† & ↦)".
    iMod (ra_update_nondeterministic VRA ⊤ γ x _ ltac:(done) Hupd with "Hinv Hown")
      as (y) "[%Hin Hown]".
    iExists -[(l, (γ, y))].
    iFrame "L".
    rewrite /ra_ty/tctx_elt_interp/ty_own/=.
    iFrame "Hd" => /=.
    iSplitL.
    - iExists _; iSplitR => //=.
      repeat rewrite heap_mapsto_fancy_vec_nil.
      by iFrame "∗#".
    - iApply (proph_obs_impl with "Obs").
      intros π' [_ Hpost].
      specialize (Hpost l).
      rewrite Forall_forall in Hpost.
      by apply Hpost.
  Qed.

  Lemma typed_ra_validate κ (self : path) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
    +[self ◁ shr_bor κ (ra_ty VRA 𝔄_const)]
    (RA_Validate: self)
    (λ _, +[])
    (λ post '-[(l, (γ, x))], λ mask π, (vra_valid VRA x π → post -[] mask π)).
  Proof.
    move => Alv tid postπ mask iκs vπl.
    iIntros "LFT #TIME #PROPH UNIQ E L $ TY #Obs" => /=.
    destruct vπl as [[pl [γ x]] []].
    iDestruct "TY" as "(H & _)".
    iDestruct "H" as "(%pl' & %d & % & #Hd & Hown & %Hphys)".
    simpl in Hphys.
    injection Hphys => ? /=; subst pl'.
    destruct d => //.
    iDestruct "Hown" as "(? & #Hshr0 & _)".
    iDestruct (ty_shr_default_to_guard (ra_ty VRA 𝔄_const) with "Hshr0") as "#Hshr"; [done|].
    iSimpl in "Hshr".
    (* iMod (proph_obs_sat with "PROPH Obs") as "(%π & %Alv & _)" => //=. *)
    iDestruct (Alv with "L E") as "#Alv".
    iDestruct (guards_transitive_right with "Alv Hshr") as "G1".
    iApply wp_fupd.
    wp_lam.
    wp_bind (_ ≤ _)%E.
    iApply (wp_persistent_time_receipt with "TIME Hd"); [done|].
    iIntros "H£ #Hd'".
    wp_pure (_ ≤ _)%E.
    iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME Hd'"); [done|].
    iIntros "H£' #Hd''".
    wp_if.
    iIntros "!>".
    leaf_open_laters "G1" with "L" as "Hown". { solve_ndisj. }
    rewrite Nat.add_1_r -bi.later_laterN.
    iMod (lc_fupd_add_laterN _ _ _ (S (S d)) with "[H£'] Hown") as "[Hown Hclose]".
    { iApply (lc_weaken with "H£'"). rewrite /advance_credits. nia. }
    iDestruct "Hown" as "[Hown #Hinv]".
    iMod (ra_validate with "Hinv Hown") as "[Hown #Hvalid]"; first solve_ndisj.
    iMod ("Hclose" with "[$Hown $Hinv]") as "L".
    iFrame "L".
    iModIntro.
    iExists -[].
    iSplit => //.
    iCombine "Obs Hvalid" as "Obs'".
    iApply (proph_obs_impl with "Obs'").
    intros π' [Hpost ?].
    by apply Hpost.
  Qed.

  Notation "RA_JoinShared: p1 p2" := (new [ #0])%E (at level 102, p1, p2 at level 1): expr_scope.

(*
  Lemma typed_ra_join_shared κ (p1 p2 : path) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I +[p1 ◁ shr_bor κ (ra_ty VRA 𝔄_const); p2 ◁ shr_bor κ (ra_ty VRA 𝔄_const)] (RA_JoinShared: p1 p2) (λ v, +[v ◁ shr_bor κ (ra_ty VRA 𝔄_const)]) (λ post '-[(l1, (γ1, x1)); (l2, (γ2, x2))], λ mask π, γ1 = γ2 ∧ ∀ y l, x1 ≼ y → x2 ≼ y → post -[(l, (γ1, y))] mask π).
  Proof.
    move => Alv tid postπ mask iκs vπl.
    fold indep_interp_of_syn_type.
    iIntros "LFT #TIME #PROPH UNIQ E L I TY #Obs" => /=.
    destruct vπl as [[pl1 [γ1 x1]] [[pl2 [γ2 x2]] []]].
    iDestruct "TY" as "(H1 & H2 & _)".
    iDestruct "H1" as "(%pl1' & %d1 & % & #Hd1 & Hown1 & %Hphys1)".
    iDestruct "H2" as "(%pl2' & %d2 & % & #Hd2 & Hown2 & %Hphys2)".
    simpl in Hphys1, Hphys2.
    injection Hphys1 => ? /=; subst pl1'.
    injection Hphys2 => ? /=; subst pl2'.
    destruct d1 => //.
    destruct d2 => //.
    iDestruct "Hown1" as "(_ & #Hshr1_shr & _)".
    iDestruct (ty_shr_default_to_guard (ra_ty VRA 𝔄_const) with "Hshr1_shr") as "#Hshr1"; [done|].
    iSimpl in "Hshr1".
    iDestruct "Hown2" as "(_ & #Hshr2_shr & _)".
    iDestruct (ty_shr_default_to_guard (ra_ty VRA 𝔄_const) with "Hshr2_shr") as "#Hshr2"; [done|].
    iSimpl in "Hshr2".
    iDestruct (Alv with "L E") as "#Alv".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & _)" => //.
    destruct (decide (d1 ≤ d2)) as [Hle | Hgt].
    - iDestruct (guards_transitive_right with "Alv Hshr1") as "G1".
      iDestruct (guards_transitive_right with "Alv Hshr2") as "G2".
      iApply wp_fupd.
      wp_lam.
      wp_bind (_ ≤ _)%E.
      iPoseProof (lguards_weaken_later _ _ _ _ (S (d2 + 1)) with "G1") as "G1'"; first lia.
      iApply (wp_persistent_time_receipt with "TIME Hd2"); [done|].
      iIntros "H£ #HdS".
      wp_pure (_ ≤ _)%E.
      iApply wp_fupd.
      iApply (wp_persistent_time_receipt with "TIME HdS"); [done|].
      iIntros "H£' #HdSS".
      wp_if.
      iIntros "!>".
      leaf_open_laters "G1'" with "L" as "Hown". { solve_ndisj. }
      iPoseProof (guards_and_point with "G1' G2") as "G3"; [ | | ..].
      2: {
        iIntros "H". iApply (and_own_discrete_ucmra with "H"). }
  *)

  Notation "RA_JoinSharedDet: p1 p2 p" := (new [ #0])%E (at level 102, p1, p2, p at level 1): expr_scope.
  
  Lemma typed_ra_join_shared_to_target κ (p1 p2 p : path) (ty : type 𝔄) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
    +[p1 ◁ shr_bor κ (ra_ty VRA 𝔄_const); p2 ◁ shr_bor κ (ra_ty VRA 𝔄_const); p ◁ own_ptr 0 (ghost_ty ty)]
    (RA_JoinSharedDet: p1 p2 p)
    (λ v, +[v ◁ shr_bor κ (ra_ty VRA 𝔄_const)])
    (λ post '-[(l1, (γ1, x1)); (l2, (γ2, x2)); (_, y)], λ mask π, γ1 = γ2 ∧ vra_conjunct_shared VRA x1 x2 y ∧ ∀ l, post -[(l, (γ1, y))] mask π).
  Proof.
    move => Alv tid postπ mask iκs vπl.
    fold indep_interp_of_syn_type.
    iIntros "LFT #TIME #PROPH UNIQ E L $ TY #Obs" => /=.
    destruct vπl as [[pl1 [γ1 x1]] [[pl2 [γ2 x2]] [[ply y] []]]].
    simpl in y.
    iDestruct "TY" as "(H1 & H2 & _ & _)".
    iDestruct "H1" as "(%pl1' & %d1 & % & #Hd1 & Hown1 & %Hphys1)".
    iDestruct "H2" as "(%pl2' & %d2 & % & #Hd2 & Hown2 & %Hphys2)".
    simpl in Hphys1, Hphys2.
    injection Hphys1 => ? /=; subst pl1'.
    injection Hphys2 => ? /=; subst pl2'.
    destruct d1 => //.
    destruct d2 => //.
    iDestruct "Hown1" as "(_ & #Hshr1_shr & _)".
    iDestruct (ty_shr_default_to_guard (ra_ty VRA 𝔄_const) with "Hshr1_shr") as "#Hshr1"; [done|].
    iSimpl in "Hshr1".
    iDestruct "Hown2" as "(_ & #Hshr2_shr & _)".
    iDestruct (ty_shr_default_to_guard (ra_ty VRA 𝔄_const) with "Hshr2_shr") as "#Hshr2"; [done|].
    iSimpl in "Hshr2".
    iDestruct (Alv with "L E") as "#Alv".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & %Hy & _)" => //.
    have Hand : ∀ Q1 Q2 : iProp Σ,
      (own γ1 (◯ VraCar VRA x1) ∗ Q1) ∧ (own γ1 (◯ VraCar VRA x2) ∗ Q2) ⊢ own γ1 (◯ VraCar VRA y).
    { iIntros (Q1 Q2) "H".
      iApply (and_own_discrete_ucmra_specific with "[H]").
      { by apply vra_auth_frag_conjunct_shared. }
      iSplit; [iDestruct "H" as "[[$ _] _]"|iDestruct "H" as "[_ [$ _]]"]. }
    (* Extract the (persistent) invariant from the shared borrow. *)
    iApply wp_fupd.
    wp_lam.
    wp_bind (_ ≤ _)%E.
    iApply (wp_persistent_time_receipt with "TIME Hd1"); [done|].
    iIntros "H£ #Hd1'".
    wp_pure (_ ≤ _)%E.
    iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME Hd1'"); [done|].
    iIntros "H£' #Hd1''".
    wp_if.
    iIntros "!>".
    iDestruct (guards_transitive_right with "Alv Hshr1") as "Hshr1a".
    iMod (guards_extract_persistent_later _ _ (ra_inv VRA γ1) ⊤ (↑NllftG) _
      ltac:(apply _) ltac:(set_solver) with "Hshr1a L []") as "H".
    { iIntros "[_ $]". }
    rewrite Nat.add_1_r -bi.later_laterN.
    iMod (lc_fupd_add_laterN _ _ _ (S (S d1)) with "[H£'] H") as "(L & #Hinv)".
    { iApply (lc_weaken with "H£'"). rewrite /advance_credits. nia. }
    iModIntro.
    destruct (decide (d1 ≤ d2)) as [Hle | Hgt].
    - iPoseProof (lguards_weaken_later _ _ _ _ (S (d2 + 1)) with "Hshr1") as "Hshr1'"; first lia.
      iPoseProof (@guards_and_own _ _ _ _ _ _ (authUR (vra_carUR VRA)) _ γ1 (◯ VraCar VRA y)
        with "Hshr1' Hshr2") as "Hshr3"; first apply Hand.
      iPoseProof (guards_include_pers (ra_inv VRA γ1) with "Hinv Hshr3") as "Hshr4".
      iExists -[(((42%positive, 1337%Z), []), (γ1, y))].
      iFrame "L Hd2".
      iSplitL.
      + iExists _; iSplitR => //=.
        rewrite /ty_own/=.
        iSplit; last done.
        iSplitR; first by iApply guards_true.
        iSplit; first by iApply (ty_shr_default_from_guard (ra_ty VRA 𝔄_const)).
        by iNext.
      + iApply (proph_obs_impl with "Obs").
        intros π' (? & ? & Hpost).
        apply Hpost.
    - iPoseProof (lguards_weaken_later _ _ _ _ (S (d1 + 1)) with "Hshr1") as "Hshr1'"; first lia.
      iPoseProof (lguards_weaken_later _ _ _ _ (S (d1 + 1)) with "Hshr2") as "Hshr2'"; first lia.
      iPoseProof (@guards_and_own _ _ _ _ _ _ (authUR (vra_carUR VRA)) _ γ1 (◯ VraCar VRA y)
        with "Hshr1' Hshr2'") as "Hshr3"; first apply Hand.
      iPoseProof (guards_include_pers (ra_inv VRA γ1) with "Hinv Hshr3") as "Hshr4".
      iExists -[(((42%positive, 1337%Z), []), (γ1, y))].
      iFrame "L Hd1".
      iSplitL.
      + iExists _; iSplitR => //=.
        rewrite /ty_own/=.
        iSplit; last done.
        iSplitR; first by iApply guards_true.
        iSplit; first by iApply (ty_shr_default_from_guard (ra_ty VRA 𝔄_const)).
        by iNext.
      + iApply (proph_obs_impl with "Obs").
        intros π' (? & ? & Hpost).
        apply Hpost.
  Qed.

  Notation "RA_Weaken: p1 p2" := (new [ #0])%E (at level 102, p1, p2 at level 1): expr_scope.

  Lemma typed_ra_weaken κ (p1 p2 : path) (ty : type 𝔄) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
    +[p1 ◁ shr_bor κ (ra_ty VRA 𝔄_const); p2 ◁ own_ptr 0 (ghost_ty ty)]
    (RA_Weaken: p1 p2)
    (λ v, +[v ◁ shr_bor κ (ra_ty VRA 𝔄_const)])
    (λ post '-[(l, (γ, x)); (_, y)], λ mask π, vra_incl VRA y x ∧ ∀ l, post -[(l, (γ, y))] mask π).
  Proof.
    move => Alv tid postπ mask iκs vπl.
    fold indep_interp_of_syn_type.
    iIntros "LFT #TIME #PROPH UNIQ E L $ TY #Obs" => /=.
    destruct vπl as [[pl [γ x]]  [[ply y] []] ].
    simpl in y.
    iDestruct "TY" as "(H & _ & _)".
    iDestruct "H" as "(%pl' & %d & % & #Hd & Hown & %Hphys)".
    simpl in Hphys.
    injection Hphys => ? /=; subst pl'.
    destruct d => //.
    iDestruct "Hown" as "(_ & #Hshr_shr & _)".
    iDestruct (ty_shr_default_to_guard (ra_ty VRA 𝔄_const) with "Hshr_shr") as "#Hshr"; [done|].
    iSimpl in "Hshr".
    iDestruct (Alv with "L E") as "#Alv".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & %Hincl & _)" => //.
    (* Extract the (persistent) invariant from the shared borrow. *)
    iApply wp_fupd.
    wp_lam.
    wp_bind (_ ≤ _)%E.
    iApply (wp_persistent_time_receipt with "TIME Hd"); [done|].
    iIntros "H£ #Hd'".
    wp_pure (_ ≤ _)%E.
    iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME Hd'"); [done|].
    iIntros "H£' #Hd''".
    wp_if.
    iIntros "!>".
    iDestruct (guards_transitive_right with "Alv Hshr") as "Hshr1".
    iMod (guards_extract_persistent_later _ _ (ra_inv VRA γ) ⊤ (↑NllftG) _
      ltac:(apply _) ltac:(set_solver) with "Hshr1 L []") as "H".
    { iIntros "[_ $]". }
    rewrite Nat.add_1_r -bi.later_laterN.
    iMod (lc_fupd_add_laterN _ _ _ (S (S d)) with "[H£'] H") as "(L & #Hinv)".
    { iApply (lc_weaken with "H£'"). rewrite /advance_credits. nia. }
    iModIntro.
    iPoseProof (lguards_weaken_later _ _ _ _ (S (d + 1)) with "Hshr") as "Hshr0"; first lia.
    iPoseProof (@guards_and_own _ _ _ _ _ _ (authUR (vra_carUR VRA)) _ γ (◯ VraCar VRA y)
      with "Hshr0 Hshr0") as "Hshr'".
    { iIntros "[[H _] _]". iApply (own_mono with "H").
      by apply auth_frag_mono, vra_car_included. }
    iPoseProof (guards_include_pers (ra_inv VRA γ) with "Hinv Hshr'") as "Hshr''".
    iExists -[(((42%positive, 1337%Z), []), (γ, y))].
    iFrame "L Hd".
    iSplitL.
    + iExists _; iSplitR => //=.
      rewrite /ty_own/=.
      iSplit; last done.
      iSplitR; first by iApply guards_true.
      iSplit; first by iApply (ty_shr_default_from_guard (ra_ty VRA 𝔄_const)).
      by iNext.
    + iApply (proph_obs_impl with "Obs").
      intros π' [_ Hpost].
      apply Hpost.
  Qed.

  Notation "RA_UpdateWithShr: self other new_value" := (new [ #0])%E (at level 102, self,other,new_value at level 1): expr_scope.

  Lemma typed_ra_update_with_shr κ (self other new_value : path) (ty : type 𝔄) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
    +[self ◁ own_ptr 0 (ra_ty VRA 𝔄_const); other ◁ shr_bor κ (ra_ty VRA 𝔄_const); new_value ◁ own_ptr 0 (ghost_ty ty)]
    (RA_UpdateWithShr: self other new_value)
    (λ out, +[out ◁ own_ptr 0 (ra_ty VRA 𝔄_const)])
    (λ post '-[(l1, (γ1, x)); (l2, (γ2, y)); (_, z)], λ mask π, γ1 = γ2 ∧ vra_frame_preserving_update VRA (vra_op VRA x y) (vra_op VRA z y) π ∧ ∀ l, post -[(l, (γ1, z))] mask π).
  Proof.
    move => Alv tid postπ mask iκs vπl.
    iIntros "LFT #TIME #PROPH UNIQ E L $ TY #Obs" => /=.
    destruct vπl as [[pl1 [γ1 x]] [[pl2 [γ2 y]] [[plz z] []]]].
    simpl in z.
    iDestruct "TY" as "(H1 & H2 & _ & _)".
    iDestruct "H1" as "(%pl1' & %d1 & % & #Hd1 & Hown1 & %Hphys1)".
    iDestruct "H2" as "(%pl2' & %d2 & % & #Hd2 & Hown2 & %Hphys2)".
    simpl in Hphys1, Hphys2.
    injection Hphys1 => ? /=; subst pl1'.
    injection Hphys2 => ? /=; subst pl2'.
    destruct d1 => //.
    destruct d2 => //.
    iDestruct "Hown1" as "(_ & _ & Hx & _)".
    iDestruct "Hown2" as "(_ & #Hy_shr & _)".
    iDestruct (ty_shr_default_to_guard (ra_ty VRA 𝔄_const) with "Hy_shr") as "#Hy"; [done|].
    iSimpl in "Hy".
    iDestruct (Alv with "L E") as "#Alv".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & _)" => //.
    iDestruct (guards_transitive_right with "Alv Hy") as "G1".
    iApply wp_fupd.
    wp_lam.
    wp_bind (_ ≤ _)%E.
    iApply (wp_persistent_time_receipt with "TIME Hd2"); [done|].
    iIntros "H£ #Hd2'".
    wp_pure (_ ≤ _)%E.
    iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME Hd2'"); [done|].
    iIntros "H£' #Hd2''".
    wp_if.
    iIntros "!>".
    leaf_open_laters "G1" with "L" as "Hown". { solve_ndisj. }
    rewrite Nat.add_1_r -bi.later_laterN.
    iMod (lc_fupd_add_laterN _ _ _ (S (S d2)) with "[H£'] Hown") as "[Hown Hclose]".
    { iApply (lc_weaken with "H£'"). rewrite /advance_credits. nia. }
    iDestruct "Hown" as "[Hown #Hinv]".
    iAssert (own γ1 (◯ VraCar VRA (vra_op VRA x y))) with "[Hx Hown]" as "Hxy".
    { rewrite -vra_car_op_eq auth_frag_op own_op. iFrame. }
    iMod (ra_update VRA _ γ1 (vra_op VRA x y) (vra_op VRA z y) with "Hinv Hxy [Obs]") as "Hxy";
      first solve_ndisj.
    { iApply (proph_obs_impl with "Obs"). by intros π [_ [? _]]. }
    rewrite -vra_car_op_eq auth_frag_op own_op.
    iDestruct "Hxy" as "[Hx Hown]".
    iMod ("Hclose" with "[$Hown $Hinv]") as "L".
    iFrame "L".
    iModIntro.
    rewrite /tctx_elt_interp/ty_own/=.
    iExists -[(_, (γ1, z))].
    iFrame "Hd1".
    iSplit => //=.
    + iExists _.
      iSplit => //.
      rewrite heap_mapsto_fancy_vec_nil.
      by iFrame "∗#".
    + iApply (proph_obs_impl with "Obs").
      intros π' (_ & _ & Hpost).
      by apply Hpost.
  Qed.

  Notation "RA_UpdateWithShrNonDet: self other new_values" := (new [ #0])%E (at level 102, self,other,new_values at level 1): expr_scope.

  Lemma typed_ra_update_with_shr_non_det κ n (self other new_values : path) (ty : type (vecₛ 𝔄 n)) E L I :
    lctx_lft_alive E L κ →
    typed_instr E L I
    +[self ◁ own_ptr 0 (ra_ty VRA 𝔄_const); other ◁ shr_bor κ (ra_ty VRA 𝔄_const); new_values ◁ own_ptr 0 (ghost_ty ty)]
    (RA_UpdateWithShrNonDet: self other new_values)
    (λ out, +[out ◁ own_ptr 0 (ra_ty VRA 𝔄_const)])
    (λ post '-[(l1, (γ1, x)); (l2, (γ2, y)); (_, zs)], λ mask π, γ1 = γ2 ∧
        vra_frame_preserving_update_nondeterministic VRA (vra_op VRA x y)
          (λ w, ∃ z, z ∈ vec_to_list zs ∧ w = vra_op VRA z y) ∧
        ∀ l, Forall (λ z, post -[(l, (γ1, z))] mask π) (vec_to_list zs)).
  Proof.
    move => Alv tid postπ mask iκs vπl.
    iIntros "LFT #TIME #PROPH UNIQ E L $ TY #Obs" => /=.
    fold indep_interp_of_syn_type.
    destruct vπl as [[pl1 [γ1 x]] [[pl2 [γ2 y]] [[plzs zs] []]]].
    simpl in zs.
    iDestruct "TY" as "(H1 & H2 & _ & _)".
    iDestruct "H1" as "(%pl1' & %d1 & % & #Hd1 & Hown1 & %Hphys1)".
    iDestruct "H2" as "(%pl2' & %d2 & % & #Hd2 & Hown2 & %Hphys2)".
    simpl in Hphys1, Hphys2.
    injection Hphys1 => ? /=; subst pl1'.
    injection Hphys2 => ? /=; subst pl2'.
    destruct d1 => //.
    destruct d2 => //.
    iDestruct "Hown1" as "(_ & _ & Hx & _)".
    iDestruct "Hown2" as "(_ & #Hy_shr & _)".
    iDestruct (ty_shr_default_to_guard (ra_ty VRA 𝔄_const) with "Hy_shr") as "#Hy"; [done|].
    iSimpl in "Hy".
    iDestruct (Alv with "L E") as "#Alv".
    iMod (proph_obs_sat with "PROPH Obs") as "(% & <- & %Hupd & _)" => //.
    iDestruct (guards_transitive_right with "Alv Hy") as "G1".
    iApply wp_fupd.
    wp_lam.
    wp_bind (_ ≤ _)%E.
    iApply (wp_persistent_time_receipt with "TIME Hd2"); [done|].
    iIntros "H£ #Hd2'".
    wp_pure (_ ≤ _)%E.
    iApply wp_fupd.
    iApply (wp_persistent_time_receipt with "TIME Hd2'"); [done|].
    iIntros "H£' #Hd2''".
    wp_if.
    iIntros "!>".
    leaf_open_laters "G1" with "L" as "Hown". { solve_ndisj. }
    rewrite Nat.add_1_r -bi.later_laterN.
    iMod (lc_fupd_add_laterN _ _ _ (S (S d2)) with "[H£'] Hown") as "[Hown Hclose]".
    { iApply (lc_weaken with "H£'"). rewrite /advance_credits. nia. }
    iDestruct "Hown" as "[Hown #Hinv]".
    iAssert (own γ1 (◯ VraCar VRA (vra_op VRA x y))) with "[Hx Hown]" as "Hxy".
    { rewrite -vra_car_op_eq auth_frag_op own_op. iFrame. }
    iMod (ra_update_nondeterministic VRA (⊤ ∖ ↑NllftG) γ1 _ _ ltac:(solve_ndisj) Hupd with "Hinv Hxy")
      as (w) "[%Hin Hxy]".
    destruct Hin as (z & Hz & ->).
    rewrite -vra_car_op_eq auth_frag_op own_op.
    iDestruct "Hxy" as "[Hx Hown]".
    iMod ("Hclose" with "[$Hown $Hinv]") as "L".
    iFrame "L".
    iModIntro.
    rewrite /tctx_elt_interp/ty_own/=.
    iExists -[(_, (γ1, z))].
    iFrame "Hd1".
    iSplit => //=.
    + iExists _.
      iSplit => //.
      rewrite heap_mapsto_fancy_vec_nil.
      by iFrame "∗#".
    + iApply (proph_obs_impl with "Obs").
      intros π' [_ [_ Hpost]].
      specialize (Hpost (42%positive, 1337%Z)).
      rewrite Forall_forall in Hpost.
      by apply Hpost.
  Qed.

End RA_type.
