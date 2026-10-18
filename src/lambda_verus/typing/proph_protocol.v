(** Storage protocols with _prophetic_ validity.

    This is a variant of [guarding/storage_protocol/protocol.v]. The protocol is given by a
    [VerusSP] (corresponding to the [Protocol] trait in verus/source/vstd/storage_protocol.rs),
    whose relation [vsp_rel] may depend on the prophecy assignment. The base (stored)
    resources are maps [gmap K V], as in Verus.

    The authoritative protocol state, the stored map, and the stored resources are kept in
    an invariant, together with a prophecy observation that the relation holds (and the
    pure fact that it is satisfiable for some prophecy assignment). *)

From iris.algebra Require Export cmra updates.
From iris.algebra Require Import proofmode_classes.
From iris.algebra Require Import auth gmap.
From iris.prelude Require Import options.

From iris.base_logic.lib Require Export own iprop.
From iris.proofmode Require Import base.
From iris.proofmode Require Import ltac_tactics.
From iris.proofmode Require Import tactics.
From iris.proofmode Require Import coq_tactics.

From stdpp Require Export namespaces.

Require Import guarding.internal.auth_frag_util.
Require Import guarding.internal.wsat_util.
Require Import guarding.guard.
Require Import guarding.factoring_props.
Require Import guarding.own_and_own_sep.
Require Import guarding.own_and.
From lrust.prophecy Require Import syn_type prophecy.
From lrust.typing Require Import ra.

(** Verus's [Protocol] trait, with a prophetic [rel]. *)
Class VerusSP (K V P : Type) `{Countable K} := {
  vsp_op : P → P → P;
  vsp_rel : P → gmap K V → proph_asn → Prop;
  vsp_unit : P;
  vsp_commutative a b : vsp_op a b = vsp_op b a;
  vsp_associative a b c : vsp_op a (vsp_op b c) = vsp_op (vsp_op a b) c;
  vsp_op_unit a : vsp_op a vsp_unit = a;
}.
Global Arguments vsp_op {_ _ _ _ _ _} _ _.
Global Arguments vsp_rel {_ _ _ _ _ _} _ _ _.
Global Arguments vsp_unit {_ _ _ _ _ _}.

Section VerusSPDefs.
  Context {K V P : Type} `{Countable K} `{!VerusSP K V P}.
  Implicit Types (p q r : P) (t b : gmap K V).

  Lemma vsp_unit_op p : vsp_op vsp_unit p = p.
  Proof. by rewrite vsp_commutative vsp_op_unit. Qed.

  (** These correspond to [incl], [guards], [exchanges], [exchanges_nondeterministic],
      [deposits], [withdraws], and [updates] in vstd/storage_protocol.rs, adapted to the
      prophetic relation. *)
  Definition vsp_incl p1 p2 := ∃ q, vsp_op p1 q = p2.

  (** Guards cannot consult the prophecy assignment, so this must hold for all of them. *)
  Definition vsp_guards p b := ∀ q t π, vsp_rel (vsp_op p q) t π → b ⊆ t.

  Definition vsp_exchanges p1 b1 p2 b2 π :=
    ∀ q t1, vsp_rel (vsp_op p1 q) t1 π → ∃ t2, vsp_rel (vsp_op p2 q) t2 π
      ∧ t1 ##ₘ b1 ∧ t2 ##ₘ b2 ∧ t1 ∪ b1 = t2 ∪ b2.

  (** The new values are chosen at the time of the exchange, so they can depend on the
      frame and the current stored map, but not on the prophecy assignment. *)
  Definition vsp_exchanges_nondeterministic p1 b1 (output_ok : P → gmap K V → Prop) :=
    ∀ q t1, (∃ π, vsp_rel (vsp_op p1 q) t1 π) → ∃ p2 b2, output_ok p2 b2 ∧
      ∀ π, vsp_rel (vsp_op p1 q) t1 π → ∃ t2, vsp_rel (vsp_op p2 q) t2 π
        ∧ t1 ##ₘ b1 ∧ t2 ##ₘ b2 ∧ t1 ∪ b1 = t2 ∪ b2.

  Definition vsp_deposits p1 b1 p2 π :=
    ∀ q t1, vsp_rel (vsp_op p1 q) t1 π → ∃ t2, vsp_rel (vsp_op p2 q) t2 π
      ∧ t1 ##ₘ b1 ∧ t1 ∪ b1 = t2.

  Definition vsp_withdraws p1 p2 b2 π :=
    ∀ q t1, vsp_rel (vsp_op p1 q) t1 π → ∃ t2, vsp_rel (vsp_op p2 q) t2 π
      ∧ t2 ##ₘ b2 ∧ t1 = t2 ∪ b2.

  Definition vsp_updates p1 p2 π :=
    ∀ q t1, vsp_rel (vsp_op p1 q) t1 π → vsp_rel (vsp_op p2 q) t1 π.

  Lemma vsp_deposits_exchanges p1 b1 p2 π :
    vsp_deposits p1 b1 p2 π → vsp_exchanges p1 b1 p2 ∅ π.
  Proof.
    intros Hdep q t1 Hrel. destruct (Hdep q t1 Hrel) as (t2 & ? & ? & <-).
    exists (t1 ∪ b1). split_and!; [done|done|apply map_disjoint_empty_r|].
    by rewrite right_id_L.
  Qed.

  Lemma vsp_withdraws_exchanges p1 p2 b2 π :
    vsp_withdraws p1 p2 b2 π → vsp_exchanges p1 ∅ p2 b2 π.
  Proof.
    intros Hw q t1 Hrel. destruct (Hw q t1 Hrel) as (t2 & ? & ? & ->).
    exists t2. split_and!; [done|apply map_disjoint_empty_r|done|].
    by rewrite right_id_L.
  Qed.

  Lemma vsp_updates_exchanges p1 p2 π :
    vsp_updates p1 p2 π → vsp_exchanges p1 ∅ p2 ∅ π.
  Proof.
    intros Hupd q t1 Hrel. exists t1.
    split_and!; [by apply Hupd|apply map_disjoint_empty_r..|done].
  Qed.

  (** The protocol monoid, as a [VerusRA] with trivial validity. *)
  Definition vsp_vra : VerusRA P := {|
    vra_valid _ _ := True;
    vra_op := vsp_op;
    vra_unit := vsp_unit;
    vra_closed_under_incl _ _ _ _ := I;
    vra_commutative := vsp_commutative;
    vra_associative := vsp_associative;
    vra_op_unit := vsp_op_unit;
    vra_unit_valid _ := I;
  |}.
End VerusSPDefs.
Global Arguments vsp_vra K V P {_ _ _}.

Lemma map_union_disjoint_difference `{Countable K} {V} (t b : gmap K V) :
  t ##ₘ b → (t ∪ b) ∖ b = t.
Proof.
  intros Hdisj. apply map_eq => i. rewrite lookup_difference lookup_union.
  destruct (t !! i) eqn:Ht, (b !! i) eqn:Hb => //=.
  exfalso. by eapply map_disjoint_spec.
Qed.

Section StorageLogic.
  Context {K V P : Type} `{Countable K} `{!VerusSP K V P}.
  Context {Σ: gFunctors}.
  Context `{!invGS Σ, !prophG Σ}.
  Context `{sp_i: !inG Σ (authUR (vra_carUR (vsp_vra K V P)))}.
  Implicit Types (p q r : P) (t b : gmap K V) (g : K → V → iProp Σ).

  Local Notation car := (VraCar (vsp_vra K V P)).

  Definition sp_inv_body (γ: gname) g : iProp Σ :=
    ∃ (state_t: P * gmap K V),
      own γ (● car state_t.1)
      ∗ (⌜ ∃ π, vsp_rel state_t.1 state_t.2 π ⌝ ∗ ⟨π, vsp_rel state_t.1 state_t.2 π⟩)
      ∗ ([∗ map] k ↦ v ∈ state_t.2, g k v).

  Definition sp_sto (γ: gname) g : iProp Σ :=
      own γ (◯ car vsp_unit) ∗ ownI γ (sp_inv_body γ g).

  Definition sp_own (γ: gname) (p: P) : iProp Σ := own γ (◯ car p).

  Global Instance vsp_car_unit_core_id : CoreId (car vsp_unit).
  Proof. rewrite /CoreId. reflexivity. Qed.

  Global Instance pers_sp_own_unit γ : Persistent (sp_own γ vsp_unit).
  Proof. apply _. Qed.

  Global Instance pers_sto γ g : Persistent (sp_sto γ g).
  Proof. apply _. Qed.

  Global Instance timeless_sp_own γ a : Timeless (sp_own γ a).
  Proof. apply _. Qed.

  Lemma apply_timeless_rhs4 (X Y Z W U : iProp Σ) (ti: Timeless Z) (ti2: Timeless W)
      : X ∧ (Y ∗ ▷ (Z ∗ W ∗ U)) -∗ ◇ (X ∧ (Y ∗ Z ∗ W ∗ ▷ (U))).
  Proof.
      iIntros "l".
      rewrite bi.except_0_and. iSplit.
      { iDestruct "l" as "[l _]". iModIntro. iFrame. }
      iDestruct "l" as "[_ [l [lat0 [lat1 lat2]]]]".
      iMod "lat0" as "lat0".
      iMod "lat1" as "lat1".
      iModIntro. iFrame.
  Qed.

  Lemma and_rhs3_entails (X Y Z W U : iProp Σ)
      : (X ∧ (Y ∗ Z ∗ W ∗ U)) ⊢ W.
  Proof.
    iIntros "x". iDestruct "x" as "[_ [_ [_ [w _]]]]". iFrame.
  Qed.

  Lemma auth_frag_conjunct_to_incl (γ: gname) (p state: P) (W: iProp Σ)
      : own γ (◯ car p) ∧ (own γ (● car state) ∗ W) ⊢ ⌜ vsp_incl p state ⌝.
  Proof.
    iIntros "x".
    iAssert ((own γ (● car state) ∧ own γ (◯ car p))%I) with "[x]" as "t".
    { iSplit.
        { iDestruct "x" as "[_ [x _]]". iFrame. }
        { iDestruct "x" as "[x _]". iFrame. }
    }
    iDestruct (auth_frag_conjunct with "t") as "%incll".
    iPureIntro. by apply vra_car_included in incll.
  Qed.

  (* SP-Sep *)

  Lemma sp_own_op (a b : P) γ :
      sp_own γ (vsp_op a b) ⊣⊢ sp_own γ a ∗ sp_own γ b.
  Proof. by rewrite /sp_own -own_op -auth_frag_op. Qed.

  (* SP-Unit *)

  Lemma sp_own_unit γ g : sp_sto γ g ⊢ sp_own γ vsp_unit.
  Proof. iIntros "[$ _]". Qed.

  Lemma sp_own_mono γ a1 a2 : vsp_incl a2 a1 → sp_own γ a1 ⊢ sp_own γ a2.
  Proof.
    intros Hincl. apply own_mono, auth_frag_mono. by apply (vra_car_included (vsp_vra K V P)).
  Qed.

  Lemma sp_own_and_specific x y z γ :
    (∀ w, vsp_incl x w → vsp_incl y w → vsp_incl z w) →
    sp_own γ x ∧ sp_own γ y ⊢ sp_own γ z.
  Proof.
    intros Hw. apply and_own_discrete_ucmra_specific.
    by apply (vra_auth_frag_conjunct_shared (vsp_vra K V P)).
  Qed.

  (* SP-PointProp *)

  Lemma point_prop_p_own (γ: gname) (p: P) : point_prop (sp_own γ p).
  Proof. apply point_prop_own. Qed.

  (* SP-Alloc *)

  Lemma sp_alloc_ns E (N: namespace) (p: P) (t: gmap K V) g :
    ↑prophN ⊆ E →
    proph_ctx -∗ ⟨π, vsp_rel p t π⟩ -∗ ([∗ map] k ↦ v ∈ t, g k v) ={E}=∗
      ∃ γ , ⌜ γ ∈ (↑ N : coPset) ⌝ ∗ sp_sto γ g ∗ sp_own γ p.
  Proof.
    iIntros (?) "#PROPH #Obs f_init".
    iMod (proph_obs_sat with "PROPH Obs") as %Hsat; first done.
    rewrite /sp_own.
    rewrite fancy_updates.uPred_fupd_unseal. unfold fancy_updates.uPred_fupd_def.
    iIntros "[w oe]".
    iMod (ownI_alloc_and_simultaneous_own_alloc_ns
      (λ γ, sp_inv_body γ g)
      (● car p ⋅ (◯ car vsp_unit ⋅ ◯ car p))
      (↑ N)
      with "w") as "w".
    { rewrite coPset_infinite_finite. apply nclose_infinite. }
    { rewrite -auth_frag_op. apply auth_both_valid_discrete. split; last done.
      exists (car vsp_unit). by rewrite !vra_car_op_eq /= vsp_unit_op vsp_op_unit. }
    iDestruct "w" as (γ) "[%in_ns [w [oinv [auth [u frag]]]]]".
    iDestruct ("w" with "[auth f_init]") as "w".
    { iModIntro. iExists (p, t). iFrame "∗#". done. }
    iModIntro. iModIntro.
    iFrame "w oe". iExists γ. iFrame. done.
  Qed.

  (* SP-Guard *)

  Lemma sp_guard (p: P) (b: gmap K V) (γ: gname) (E: coPset) g
    (Hguards: vsp_guards p b)
    (is_in: γ ∈ E)
    : sp_sto γ g ⊢ (sp_own γ p &&{ E }&&> ▷ [∗ map] k ↦ v ∈ b, g k v).
  Proof.
    unfold sp_sto. iIntros "[#ounit #oinv]".
    iDestruct (guards_from_ownI _ _ E with "oinv") as "mg". { set_solver. }
    assert (Inhabited (P * gmap K V)) as IP. { apply populate. apply (vsp_unit, ∅). }
    unfold sp_inv_body.
    rewrite bi.later_exist.
    iDestruct (guards_true E (sp_own γ p)) as "gt".
    iDestruct (guards_transitive _ (sp_own γ p) True%I with "gt mg") as "gg".
    iDestruct (guards_strengthen_exists_with_lhs (P * gmap K V) (sp_own γ p)
      (λ (state_t: P * gmap K V), (▷ (⌜ vsp_incl p state_t.1 ⌝))%I)
      (λ (state_t: P * gmap K V), (▷ (own γ (● car state_t.1)
          ∗ (⌜ ∃ π, vsp_rel state_t.1 state_t.2 π ⌝ ∗ ⟨π, vsp_rel state_t.1 state_t.2 π⟩)
          ∗ [∗ map] k ↦ v ∈ state_t.2, g k v))%I)
      E 0
      with "[gg]") as "ggg".
    {
      iIntros (x) "o". rewrite /sp_own. iNext.
      iDestruct (auth_frag_conjunct_to_incl with "o") as "o"; trivial.
    }
    { unfold guards. iFrame "gg". }
    assert ((∃ x : P * gmap K V, ▷ (own γ (● car x.1)
          ∗ (⌜ ∃ π, vsp_rel x.1 x.2 π ⌝ ∗ ⟨π, vsp_rel x.1 x.2 π⟩)
          ∗ [∗ map] k ↦ v ∈ x.2, g k v) ∗ ▷ ⌜vsp_incl p x.1⌝)
      ⊣⊢ (▷ ([∗ map] k ↦ v ∈ b, g k v) ∗ ▷(([∗ map] k ↦ v ∈ b, g k v) -∗
          ∃ x : P * gmap K V, (own γ (● car x.1)
          ∗ (⌜ ∃ π, vsp_rel x.1 x.2 π ⌝ ∗ ⟨π, vsp_rel x.1 x.2 π⟩)
          ∗ [∗ map] k ↦ v ∈ x.2, g k v) ∗ ⌜vsp_incl p x.1⌝)))
      as Equ.
    { iSplit.
      { iIntros "r".
        rewrite <- bi.later_sep. iNext.
        iDestruct "r" as (state) "[[r [[%Hsat #Hobs] t]] %p_incl_x]".
        destruct p_incl_x as [z Hz]. destruct Hsat as [π Hrel].
        rewrite -Hz in Hrel.
        have Hsub := Hguards z state.2 π Hrel.
        iEval (rewrite -(map_difference_union b state.2) //) in "t".
        rewrite big_sepM_union; last by apply map_disjoint_difference_r.
        iDestruct "t" as "[fb fbz]".
        iFrame "fb".
        iIntros "fb".
        iExists state.
        iFrame "r Hobs".
        iSplitL; last by iPureIntro; exists z.
        iSplit; first by iPureIntro; exists π; rewrite -Hz.
        iEval (rewrite -(map_difference_union b state.2) //).
        rewrite big_sepM_union; last by apply map_disjoint_difference_r.
        iFrame. }
      { iIntros "[a b]".
        iDestruct ("b" with "a") as "b".
        rewrite bi.later_exist.
        iDestruct "b" as (state) "b". iExists state.
        rewrite bi.later_sep. iFrame.
      } }
    setoid_rewrite Equ.
    iApply guards_weaken_rhs_sep_l. iFrame "ggg".
  Qed.

  (* SP-Exchange (general form)

     The new protocol element [p2] and the new stored map [b2] are chosen according to
     [Choice], which may depend on the frame [r] and on the current stored map [t1].
     The prophecy observation guarantees that the relation is preserved. *)

  Lemma sp_exchange_with_extra_guard_general_with_later
      (p1 q: P) (b1: gmap K V) (Choice: P → gmap K V → P → gmap K V → Prop)
      (γ: gname) g (G: iProp Σ) E F n
    (choice_ex: ∀ r t1, (∃ π, vsp_rel (vsp_op (vsp_op p1 q) r) t1 π) →
        ∃ p2 b2, Choice r t1 p2 b2)
    (gname_in_f: γ ∈ F) (f_sub_e: F ⊆ E) (proph_in: ↑prophN ⊆ E ∖ F)
    : proph_ctx -∗ sp_sto γ g -∗ (G &&{ F ; n }&&> sp_own γ q) -∗
      ⟨π, ∀ r t1 p2 b2, Choice r t1 p2 b2 → vsp_rel (vsp_op (vsp_op p1 q) r) t1 π →
        ∃ t2, vsp_rel (vsp_op (vsp_op p2 q) r) t2 π
          ∧ t1 ##ₘ b1 ∧ t2 ##ₘ b2 ∧ t1 ∪ b1 = t2 ∪ b2⟩ -∗
      G -∗ sp_own γ p1 -∗ ▷ ([∗ map] k ↦ v ∈ b1, g k v) ={ E, E ∖ F }=∗
      ▷^n (|={ E ∖ F, E }=> ∃ r t1 p2 b2,
        ⌜ Choice r t1 p2 b2 ⌝ ∗ ⟨π, vsp_rel (vsp_op (vsp_op p1 q) r) t1 π⟩ ∗
        G ∗ sp_own γ p2 ∗ ▷ ([∗ map] k ↦ v ∈ b2, g k v)).
  Proof.
    unfold sp_sto, sp_own.
    iIntros "#PROPH [#ounit #m] #gu #Hupd g p f".
    iDestruct (guards_from_ownI _ _ F with "m") as "mg". { set_solver. }
    iDestruct (guards_true F G) as "gt".
    iDestruct (guards_transitive _ G True%I with "gt mg") as "gg".
    iDestruct (lguards_weaken_later _ _ _ 0 n with "[gg]") as "ggg". { lia. }
    { iFrame "gg". }
    iDestruct (lguards_open_two_simultaneously G _ _ E F n with "ggg gu g") as "opened".
    { set_solver. }
    iMod "opened" as (T) "[t [tinv [town back]]]".
    unfold sp_inv_body.

    iAssert ((▷^n (◇ own γ (◯ car q) ∧ (
          ◇ (▷ (∃ state_t : (P * gmap K V), own γ (● car state_t.1)
            ∗ (⌜ ∃ π, vsp_rel state_t.1 state_t.2 π ⌝ ∗ ⟨π, vsp_rel state_t.1 state_t.2 π⟩)
            ∗ [∗ map] k ↦ v ∈ state_t.2, g k v) -∗ T)
          ∗
          ◇ (∃ state_t : (P * gmap K V), ▷ (own γ (● car state_t.1)
            ∗ (⌜ ∃ π, vsp_rel state_t.1 state_t.2 π ⌝ ∗ ⟨π, vsp_rel state_t.1 state_t.2 π⟩)
            ∗ [∗ map] k ↦ v ∈ state_t.2, g k v))
          )))%I)
          with "[t tinv town]" as "x".
    { iSplit. { iDestruct ("town" with "t") as "town". iNext.
        iDestruct "town" as "[x y]". iFrame "x". }
        iDestruct ("tinv" with "t") as "[tinv back]".
        iFrame "back". iNext. iMod "tinv" as "tinv".
        iMod (bi.later_exist_except_0 with "tinv") as (state0) "tinv".
        iModIntro. iExists state0. iFrame "tinv".
    }

    iModIntro. iNext.

    rewrite <- bi.except_0_sep.
    rewrite <- bi.except_0_and.
    iMod "x" as "x".

    rewrite bi.sep_exist_l.
    rewrite bi.and_exist_l.
    iDestruct "x" as (state0) "x".
    iMod (apply_timeless_rhs4 with "x") as "x".
    iDestruct (and_rhs3_entails with "x") as "#[%Hsat #Hobs]".

    iAssert (own γ (◯ car q) ∧ own γ (● car state0.1) ∗ ((▷ (∃ state_t : P * gmap K V,
          own γ (● car state_t.1)
          ∗ (⌜ ∃ π, vsp_rel state_t.1 state_t.2 π ⌝ ∗ ⟨π, vsp_rel state_t.1 state_t.2 π⟩)
          ∗ [∗ map] k ↦ v ∈ state_t.2, g k v) -∗ T)
        ∗ ▷ ([∗ map] k ↦ v ∈ state0.2, g k v)))%I with "[x]" as "x".
      { iSplit. { iDestruct "x" as "[x _]". iFrame. }
          iDestruct "x" as "[_ [x [y [_ z]]]]". iFrame. }

    iDestruct (andsep_to_sepand_ucmra with "x") as "[x y]".
      { apply auth_frag_disjointness. }

    iDestruct (own_separates_out γ (◯ car q) (own γ (◯ car q) ∧ (▷ (∃ state_t : P * gmap K V,
          own γ (● car state_t.1)
          ∗ (⌜ ∃ π, vsp_rel state_t.1 state_t.2 π ⌝ ∗ ⟨π, vsp_rel state_t.1 state_t.2 π⟩)
          ∗ [∗ map] k ↦ v ∈ state_t.2, g k v) -∗ T)
        ∗ ▷ ([∗ map] k ↦ v ∈ state0.2, g k v)) with "[y]") as "[y z]".
      { iFrame "y". iIntros "[k _]". iFrame. }

    iAssert (own γ (◯ car (vsp_op p1 q))) with "[p y]" as "own_p_q".
    { iApply sp_own_op. iFrame. }
    iCombine "x own_p_q" as "both".
    assert (● car state0.1 ⋅ ◯ car (vsp_op p1 q) ~~>: λ k, ∃ c y,
      car state0.1 = car (vsp_op p1 q) ⋅ c ∧
      (∃ p2 b2, y = car (vsp_op p2 q) ∧ Choice (vra_val c) state0.2 p2 b2) ∧
      k = ● (y ⋅ c) ⋅ ◯ y) as Hupd'.
    { apply vra_auth_frame_updateP. intros [r] Hr.
      rewrite vra_car_op_eq in Hr. injection Hr as Hr.
      destruct (choice_ex r state0.2) as (p2 & b2 & Hc).
      { destruct Hsat as [π Hπ]. exists π. by rewrite -Hr. }
      exists (car (vsp_op p2 q)). eauto. }
    iMod (own_updateP _ _ _ Hupd' with "both") as (k) "[%Hk both]".
    destruct Hk as ([r] & y & Hr & (p2 & b2 & -> & Hc) & ->).
    rewrite vra_car_op_eq in Hr. injection Hr as Hr.
    rewrite !vra_car_op_eq.
    iDestruct "both" as "[x own_p_q]".
    rewrite /= -/(sp_own γ (vsp_op p2 q)) sp_own_op.
    iDestruct "own_p_q" as "[p q]".
    iDestruct ("z" with "q") as "[_ z]".
    iDestruct "z" as "[g fi]".

    iDestruct (proph_obs_and with "Hobs Hupd") as "Hobs'".
    iMod (proph_obs_sat with "PROPH Hobs'") as %(π0 & Hrel0 & Himp0); first done.
    rewrite Hr in Hrel0.
    destruct (Himp0 r state0.2 p2 b2 Hc Hrel0) as (t2 & Hrel2 & Hd1 & Hd2 & Heq).

    iDestruct (bi.later_sep with "[fi f]") as "f_op". { iFrame "fi". iFrame "f". }
    rewrite -big_sepM_union //.
    rewrite Heq.
    rewrite big_sepM_union //.
    iDestruct "f_op" as "[fi fb]".

    iAssert ((▷ ∃ state0_t : P * gmap K V,
          own γ (● car state0_t.1)
          ∗ (⌜ ∃ π, vsp_rel state0_t.1 state0_t.2 π ⌝ ∗ ⟨π, vsp_rel state0_t.1 state0_t.2 π⟩)
          ∗ [∗ map] k ↦ v ∈ state0_t.2, g k v)%I)
          with "[x fi]"
          as "inv_to_return".
    {
      iModIntro.
      iExists (vsp_op (vsp_op p2 q) r, t2). iFrame "x fi".
      iSplit; first by eauto.
      iApply (proph_obs_impl with "Hobs'").
      intros π [Hrel Himp]. rewrite Hr in Hrel.
      destruct (Himp r state0.2 p2 b2 Hc Hrel) as (t2' & Hrel2' & Hd1' & Hd2' & Heq').
      enough (t2' = t2) as -> by done.
      by rewrite -(map_union_disjoint_difference t2' b2) // -Heq' Heq
        map_union_disjoint_difference.
    }
    iDestruct ("g" with "inv_to_return") as "g".
    iMod ("back" with "g") as "g".
    iModIntro. iExists r, state0.2, p2, b2. iFrame "∗%".
    iApply (proph_obs_impl with "Hobs"). intros π. by rewrite Hr.
  Qed.

  Lemma sp_exchange_general
      (p1: P) (b1: gmap K V) (Choice: P → gmap K V → P → gmap K V → Prop)
      (γ: gname) g E
    (choice_ex: ∀ r t1, (∃ π, vsp_rel (vsp_op p1 r) t1 π) → ∃ p2 b2, Choice r t1 p2 b2)
    (gname_in_e: γ ∈ E) (proph_in: ↑prophN ⊆ E ∖ {[ γ ]})
    : proph_ctx -∗ sp_sto γ g -∗
      ⟨π, ∀ r t1 p2 b2, Choice r t1 p2 b2 → vsp_rel (vsp_op p1 r) t1 π →
        ∃ t2, vsp_rel (vsp_op p2 r) t2 π ∧ t1 ##ₘ b1 ∧ t2 ##ₘ b2 ∧ t1 ∪ b1 = t2 ∪ b2⟩ -∗
      sp_own γ p1 -∗ ▷ ([∗ map] k ↦ v ∈ b1, g k v) ={ E }=∗
      ∃ r t1 p2 b2, ⌜ Choice r t1 p2 b2 ⌝ ∗ ⟨π, vsp_rel (vsp_op p1 r) t1 π⟩ ∗
        sp_own γ p2 ∗ ▷ ([∗ map] k ↦ v ∈ b2, g k v).
  Proof.
    iIntros "#PROPH #Hsto #Hupd p f".
    iDestruct (sp_own_unit with "Hsto") as "#u".
    iDestruct (guards_include_pers_simple (sp_own γ vsp_unit) {[ γ ]} 0 with "u") as "gu".
    iMod (sp_exchange_with_extra_guard_general_with_later p1 vsp_unit b1 Choice γ g True%I
      E {[ γ ]} 0 with "PROPH Hsto gu [] [] p f") as "J".
    { intros r t1. rewrite vsp_op_unit. apply choice_ex. }
    { set_solver. } { set_solver. } { done. }
    { iApply (proph_obs_impl with "Hupd"). intros π Himp r t1 p2 b2.
      rewrite !vsp_op_unit. apply Himp. }
    { done. }
    iMod "J" as (r t1 p2 b2) "(% & Hobs & _ & p & f)".
    iModIntro. iExists r, t1, p2, b2. rewrite vsp_op_unit. by iFrame.
  Qed.

  (* SP-Exchange *)

  Lemma sp_exchange
    (p1 p2: P) (b1 b2: gmap K V) (γ: gname) g E
    (gname_in_e: γ ∈ E) (proph_in: ↑prophN ⊆ E ∖ {[ γ ]})
    : proph_ctx -∗ sp_sto γ g -∗ ⟨π, vsp_exchanges p1 b1 p2 b2 π⟩ -∗
        sp_own γ p1 -∗ ▷ ([∗ map] k ↦ v ∈ b1, g k v) ={ E }=∗
        sp_own γ p2 ∗ ▷ ([∗ map] k ↦ v ∈ b2, g k v).
  Proof.
    iIntros "#PROPH #Hsto #Hexch p f".
    iMod (sp_exchange_general p1 b1 (λ _ _ p2' b2', p2' = p2 ∧ b2' = b2) with "PROPH Hsto [] p f")
      as (r t1 p2' b2') "([-> ->] & _ & $ & $)"; [eauto|done|done| |done].
    iApply (proph_obs_impl with "Hexch"). intros π Hexch r t1 p2' b2' [-> ->].
    apply Hexch.
  Qed.

  Lemma sp_exchange_nondeterministic
    (p1: P) (b1: gmap K V) (output_ok: P → gmap K V → Prop) (γ: gname) g E
    (exchng: vsp_exchanges_nondeterministic p1 b1 output_ok)
    (gname_in_e: γ ∈ E) (proph_in: ↑prophN ⊆ E ∖ {[ γ ]})
    : proph_ctx -∗ sp_sto γ g -∗
        sp_own γ p1 -∗ ▷ ([∗ map] k ↦ v ∈ b1, g k v) ={ E }=∗
          ∃ p2 b2 , ⌜ output_ok p2 b2 ⌝ ∗ sp_own γ p2 ∗ ▷ ([∗ map] k ↦ v ∈ b2, g k v).
  Proof.
    iIntros "#PROPH #Hsto p f".
    iMod (sp_exchange_general p1 b1 (λ r t1 p2 b2, output_ok p2 b2 ∧
        ∀ π, vsp_rel (vsp_op p1 r) t1 π → ∃ t2, vsp_rel (vsp_op p2 r) t2 π
          ∧ t1 ##ₘ b1 ∧ t2 ##ₘ b2 ∧ t1 ∪ b1 = t2 ∪ b2) with "PROPH Hsto [] p f")
      as (r t1 p2 b2) "([% _] & _ & p & f)"; [|done|done| |].
    { intros r t1 Hsat. destruct (exchng r t1 Hsat) as (p2 & b2 & ?). eauto. }
    { iApply proph_obs_true. intros π r t1 p2 b2 [_ Himp]. apply Himp. }
    iModIntro. iExists p2, b2. by iFrame.
  Qed.

  (* SP-Deposit *)

  Lemma sp_deposit
      (p1 p2: P) (b1: gmap K V) (γ: gname) g E
      (gname_in_e: γ ∈ E) (proph_in: ↑prophN ⊆ E ∖ {[ γ ]})
      : proph_ctx -∗ sp_sto γ g -∗ ⟨π, vsp_deposits p1 b1 p2 π⟩ -∗
          sp_own γ p1 -∗ ▷ ([∗ map] k ↦ v ∈ b1, g k v) ={ E }=∗ sp_own γ p2.
  Proof.
    iIntros "#PROPH #Hsto #Hdep p f".
    iMod (sp_exchange p1 p2 b1 ∅ γ g E gname_in_e proph_in with "PROPH Hsto [] p f")
      as "[$ _]".
    { iApply (proph_obs_impl with "Hdep"). intros π. apply vsp_deposits_exchanges. }
    done.
  Qed.

  (* SP-Withdraw *)

  Lemma sp_withdraw
      (p1 p2: P) (b2: gmap K V) (γ: gname) g E
      (gname_in_e: γ ∈ E) (proph_in: ↑prophN ⊆ E ∖ {[ γ ]})
      : proph_ctx -∗ sp_sto γ g -∗ ⟨π, vsp_withdraws p1 p2 b2 π⟩ -∗
          sp_own γ p1 ={ E }=∗ sp_own γ p2 ∗ ▷ ([∗ map] k ↦ v ∈ b2, g k v).
  Proof.
    iIntros "#PROPH #Hsto #Hw p".
    iMod (sp_exchange p1 p2 ∅ b2 γ g E gname_in_e proph_in with "PROPH Hsto [] p []") as "$".
    { iApply (proph_obs_impl with "Hw"). intros π. apply vsp_withdraws_exchanges. }
    { by rewrite big_sepM_empty. }
    done.
  Qed.

  (* SP-Update *)

  Lemma sp_update
      (p1 p2: P) (γ: gname) g E
      (gname_in_e: γ ∈ E) (proph_in: ↑prophN ⊆ E ∖ {[ γ ]})
      : proph_ctx -∗ sp_sto γ g -∗ ⟨π, vsp_updates p1 p2 π⟩ -∗
          sp_own γ p1 ={ E }=∗ sp_own γ p2.
  Proof.
    iIntros "#PROPH #Hsto #Hupd p".
    iMod (sp_exchange p1 p2 ∅ ∅ γ g E gname_in_e proph_in with "PROPH Hsto [] p []")
      as "[$ _]".
    { iApply (proph_obs_impl with "Hupd"). intros π. apply vsp_updates_exchanges. }
    { by rewrite big_sepM_empty. }
    done.
  Qed.

  (* SP-Exchange with an extra (shared) element *)

  Lemma sp_exchange_with_extra_guard_with_later
    (p1 p2 q: P) (b1 b2: gmap K V) (γ: gname) g (G: iProp Σ) E F n
    (gname_in_f: γ ∈ F) (f_sub_e: F ⊆ E) (proph_in: ↑prophN ⊆ E ∖ F)
    : proph_ctx -∗ sp_sto γ g -∗ (G &&{ F ; n }&&> sp_own γ q) -∗
      ⟨π, vsp_exchanges (vsp_op p1 q) b1 (vsp_op p2 q) b2 π⟩ -∗
      G -∗ sp_own γ p1 -∗ ▷ ([∗ map] k ↦ v ∈ b1, g k v) ={ E, E ∖ F }=∗
      ▷^n (|={ E ∖ F, E }=> G ∗ sp_own γ p2 ∗ ▷ ([∗ map] k ↦ v ∈ b2, g k v)).
  Proof.
    iIntros "#PROPH #Hsto #Hg #Hexch G p f".
    iMod (sp_exchange_with_extra_guard_general_with_later p1 q b1
      (λ _ _ p2' b2', p2' = p2 ∧ b2' = b2) with "PROPH Hsto Hg [] G p f") as "J";
      [eauto|done|done|done| |].
    { iApply (proph_obs_impl with "Hexch"). intros π Hexch r t1 p2' b2' [-> ->].
      apply Hexch. }
    iModIntro. iNext.
    iMod "J" as (r t1 p2' b2') "([-> ->] & _ & $ & $ & $)". done.
  Qed.

  Lemma sp_exchange_with_extra_guard_nondeterministic_with_later
    (p1 q: P) (b1: gmap K V) (output_ok: P → gmap K V → Prop) (γ: gname) g (G: iProp Σ) E F n
    (exchng: vsp_exchanges_nondeterministic (vsp_op p1 q) b1
        (λ p2_q b2 , ∃ p2 , p2_q = vsp_op p2 q ∧ output_ok p2 b2))
    (gname_in_f: γ ∈ F) (f_sub_e: F ⊆ E) (proph_in: ↑prophN ⊆ E ∖ F)
    : proph_ctx -∗ sp_sto γ g -∗ (G &&{ F ; n }&&> sp_own γ q) -∗
      G -∗ sp_own γ p1 -∗ ▷ ([∗ map] k ↦ v ∈ b1, g k v) ={ E, E ∖ F }=∗
      ▷^n (|={ E ∖ F, E }=> ∃ p2 b2, ⌜ output_ok p2 b2 ⌝ ∗
        G ∗ sp_own γ p2 ∗ ▷ ([∗ map] k ↦ v ∈ b2, g k v)).
  Proof.
    iIntros "#PROPH #Hsto #Hg G p f".
    iMod (sp_exchange_with_extra_guard_general_with_later p1 q b1
      (λ r t1 p2 b2, output_ok p2 b2 ∧
        ∀ π, vsp_rel (vsp_op (vsp_op p1 q) r) t1 π → ∃ t2,
          vsp_rel (vsp_op (vsp_op p2 q) r) t2 π
          ∧ t1 ##ₘ b1 ∧ t2 ##ₘ b2 ∧ t1 ∪ b1 = t2 ∪ b2) with "PROPH Hsto Hg [] G p f") as "J";
      [|done|done|done| |].
    { intros r t1 Hsat. destruct (exchng r t1 Hsat) as (p2q & b2 & (p2 & -> & ?) & Himp).
      exists p2, b2. split; first done. done. }
    { iApply proph_obs_true. intros π r t1 p2 b2 [_ Himp]. apply Himp. }
    iModIntro. iNext.
    iMod "J" as (r t1 p2 b2) "([% _] & _ & G & p & f)".
    iModIntro. iExists p2, b2. by iFrame.
  Qed.

  (* SP-Valid *)

  Lemma sp_validate_with_extra_guard_with_later
    (p1 q: P) (γ: gname) g (G: iProp Σ) E F n
    (gname_in_f: γ ∈ F) (f_sub_e: F ⊆ E) (proph_in: ↑prophN ⊆ E ∖ F)
    : proph_ctx -∗ sp_sto γ g -∗ (G &&{ F ; n }&&> sp_own γ q) -∗
      G -∗ sp_own γ p1 ={ E, E ∖ F }=∗
      ▷^n (|={ E ∖ F, E }=> ∃ r t, ⟨π, vsp_rel (vsp_op (vsp_op p1 q) r) t π⟩ ∗
        G ∗ sp_own γ p1).
  Proof.
    iIntros "#PROPH #Hsto #Hg G p".
    iMod (sp_exchange_with_extra_guard_general_with_later p1 q ∅
      (λ _ _ p2 b2, p2 = p1 ∧ b2 = ∅) with "PROPH Hsto Hg [] G p []") as "J";
      [eauto|done|done|done| | |].
    { iApply proph_obs_true. intros π r t1 p2 b2 [-> ->] Hrel.
      exists t1. split_and!; [done|apply map_disjoint_empty_r..|done]. }
    { by rewrite big_sepM_empty. }
    iModIntro. iNext.
    iMod "J" as (r t1 p2 b2) "([-> ->] & Hobs & G & p & _)".
    iModIntro. iExists r, t1. by iFrame.
  Qed.

  Global Instance proper_sp_own γ : Proper ((=) ==> (⊣⊢)) (sp_own γ).
  Proof. by intros x y ->. Qed.
End StorageLogic.
