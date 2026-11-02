From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth excl agree lib.excl_auth.
From iris.base_logic.lib Require Import invariants.
Require Import guarding.guard.
Require Import guarding.own_and.
From lrust.lifetime Require Import lifetime_full.
From iris.prelude Require Import options.

(** * Guarded mutable borrows (GMB)

An instance [γ] of the GMB library, over a family [c : S → T → iProp Σ] of _contents_
([s : S] is the _placement_, [t : T] the logical contents), provides
- the _move right_ [gmb_a γ s] (exclusive), and
- the _permission_ [gmb_b γ t] (exclusive),
together with a persistent instance invariant [gmb_inv c γ]. The laws (see
[design_docs/guarded-mutable-borrows-plan.md], §1 and "Outcome: phase 1") are:
- (L0) [gmb_create], [gmb_destroy];
- (L1) [gmb_move]: the owner of [gmb_a γ s] takes the contents out, and puts back contents
  at the same [t] but any placement;
- (L2) [gmb_share]: guards of [gmb_a γ s] and [gmb_b γ t] give a guard of [c s t];
- (L3) [gmb_lend], [gmb_lend_guarded]: a guard [@[κ] &&> gmb_a γ s] and a borrow
  [&{κ} (∃ t, gmb_b γ t)] give a borrow [&{κ} (∃ t, c s t)];
- (L4) is automatic: when [κ] ends, the back-map of the lend puts the contents back.

We assume that [c] is timeless. This lets the state invariant be a guard without a later
([True &&{↑NllftUsr2}&&> …]), so that (L2) gives a guard of [c s t] at the step-index of its
inputs, and (L0), (L1), (L3) move [c] in and out of the instance without laters. The
intended instance (fancy bytes at a location, [∃ fbs, l ↦b[^fbs] ∗ ⌜…⌝], with nested cells
owned through their own [gmb_a]) is timeless. *)

(** The [b] side of the state: the contents are [In t], lent out at placement [s] for [κ]
    ([Out s κ]), or the instance is destroyed ([Gone]). *)
Inductive gmb_tstate (S T : Type) :=
  | GmbIn (t : T)
  | GmbOut (s : S) (κ : lft)
  | GmbGone.
Global Arguments GmbIn {S T} t.
Global Arguments GmbOut {S T} s κ.
Global Arguments GmbGone {S T}.

(** The [a] side of the state: the contents are at placement [s] ([Here s]), with a mover
    who has to put back contents at [t] ([Moving t]), or the instance is destroyed. *)
Inductive gmb_sstate (S T : Type) :=
  | GmbHere (s : S)
  | GmbMoving (t : T)
  | GmbDestroyed.
Global Arguments GmbHere {S T} s.
Global Arguments GmbMoving {S T} t.
Global Arguments GmbDestroyed {S T}.

Global Instance gmb_tstate_inhabited S T : Inhabited (gmb_tstate S T) := populate GmbGone.
Global Instance gmb_sstate_inhabited S T : Inhabited (gmb_sstate S T) := populate GmbDestroyed.

Class gmbG Σ (S T : Type) := GmbG {
  gmb_aG :: inG Σ (excl_authR (leibnizO (gmb_sstate S T)));
  gmb_bG :: inG Σ (excl_authR (leibnizO (gmb_tstate S T)));
}.

Definition gmbΣ (S T : Type) : gFunctors := #[
  GFunctor (excl_authR (leibnizO (gmb_sstate S T)));
  GFunctor (excl_authR (leibnizO (gmb_tstate S T)))
].

Global Instance subG_gmbΣ {Σ} S T : subG (gmbΣ S T) Σ → gmbG Σ S T.
Proof. solve_inG. Qed.

(** An instance has two ghost names, one per side, and a _depth_: the largest step-index of
    the guards of [gmb_a] that (L3) accepts, fixed when the instance is created. *)
Record gmb_name := GmbName { gmb_a_name : gname; gmb_b_name : gname; gmb_depth : nat }.

(** ** Exclusive fragments with two half authorities *)

(* begin hide *)
Local Lemma excl_auth_and_eq {X : Type} dq (x y : leibnizO X) (w : excl_authR (leibnizO X)) :
  ✓ w → ●{dq} (Excl' x) ≼ w → ◯ (Excl' y) ≼ w → y = x.
Proof.
  intros Hv [c Hc] Hf. rewrite Hc in Hv Hf. clear Hc w.
  destruct c as [[[dq' ag]|] cf].
  - assert (✓ (to_agree (Excl' x) ⋅ ag)) as Hag.
    { destruct Hv as [_ Hv]. destruct (Hv 0) as (a & Ha & _).
      apply cmra_discrete_valid. rewrite Ha. done. }
    apply agree_op_inv in Hag. rewrite -Hag in Hv Hf.
    assert (●{dq} Excl' x ⋅ View (Some (dq', to_agree (Excl' x))) cf
              ≡ ●{dq ⋅ dq'} (Excl' x) ⋅ ◯ cf) as Heq.
    { split; simpl; [by rewrite -Some_op -pair_op agree_idemp right_id|done]. }
    rewrite Heq in Hv Hf. rewrite auth_frag_included in Hf.
    apply auth_both_dfrac_valid_discrete in Hv as [_ [Hv _]].
    assert (Excl' y ≼ Excl' x) as Hi by by trans cf.
    apply Excl_included in Hi. by inversion Hi.
  - assert (View (Some (dq, to_agree (Excl' x))) ε ⋅ View None cf ≡ ●{dq} (Excl' x) ⋅ ◯ cf)
      as Heq by done.
    rewrite Heq in Hv Hf. rewrite auth_frag_included in Hf.
    apply auth_both_dfrac_valid_discrete in Hv as [_ [Hv _]].
    assert (Excl' y ≼ Excl' x) as Hi by by trans cf.
    apply Excl_included in Hi. by inversion Hi.
Qed.

Section ExclAuthHalves.
  Context {Σ : gFunctors} {X : Type} `{!inG Σ (excl_authR (leibnizO X))}.

  Local Definition xa_half γ (x : X) : iProp Σ := own γ (●{#1/2} (Excl' (x : leibnizO X))).
  Local Definition xa_frag γ (x : X) : iProp Σ := own γ (◯ (Excl' (x : leibnizO X))).

  Local Lemma xa_auth_split (x : X) :
    ●E (x : leibnizO X) ≡ ●{#1/2} (Excl' (x : leibnizO X)) ⋅ ●{#1/2} (Excl' (x : leibnizO X)).
  Proof. by rewrite -auth_auth_dfrac_op dfrac_op_own Qp.half_half. Qed.

  Local Lemma xa_alloc (x : X) : ⊢ |==> ∃ γ, xa_half γ x ∗ xa_half γ x ∗ xa_frag γ x.
  Proof.
    iMod (own_alloc (●E (x : leibnizO X) ⋅ ◯E (x : leibnizO X))) as (γ) "[H F]".
    { apply excl_auth_valid. }
    iModIntro. iExists γ. rewrite /xa_half /xa_frag xa_auth_split.
    iDestruct "H" as "[$ $]". by iFrame.
  Qed.

  Local Lemma xa_half_agree γ x y : xa_half γ x -∗ xa_half γ y -∗ ⌜x = y⌝.
  Proof.
    iIntros "H1 H2". iDestruct (own_valid_2 with "H1 H2") as %Hv.
    apply auth_auth_dfrac_op_inv_L in Hv. by inversion Hv.
  Qed.

  Local Lemma xa_half_frag_agree γ x y : xa_half γ x -∗ xa_frag γ y -∗ ⌜x = y⌝.
  Proof.
    iIntros "H F". iDestruct (own_valid_2 with "H F") as %Hv.
    apply auth_both_dfrac_valid_discrete in Hv as [_ [Hv _]].
    apply Excl_included in Hv. by inversion Hv.
  Qed.

  Local Lemma xa_frag_excl γ x y : xa_frag γ x -∗ xa_frag γ y -∗ False.
  Proof.
    iIntros "F1 F2". iDestruct (own_valid_2 with "F1 F2") as %Hv.
    by apply excl_auth_frag_op_valid in Hv.
  Qed.

  Local Lemma xa_frag_and_half γ x y : xa_frag γ y ∧ xa_half γ x ⊢ ⌜x = y⌝.
  Proof.
    iIntros "H". iDestruct (and_own_discrete_ucmra with "H") as (w) "[W [%Hf %Ha]]".
    iDestruct (own_valid with "W") as %Hv. iPureIntro.
    symmetry. by eapply excl_auth_and_eq.
  Qed.

  Local Lemma xa_update γ x y :
    xa_half γ x -∗ xa_half γ x -∗ xa_frag γ x ==∗ xa_half γ y ∗ xa_half γ y ∗ xa_frag γ y.
  Proof.
    rewrite /xa_half /xa_frag. iIntros "H1 H2 F".
    iAssert (own γ (●E (x : leibnizO X))) with "[H1 H2]" as "H".
    { rewrite xa_auth_split own_op. iFrame. }
    iMod (own_update_2 _ _ _ (●E (y : leibnizO X) ⋅ ◯E (y : leibnizO X)) with "H F") as "[H F]".
    { apply excl_auth_update. }
    rewrite xa_auth_split. iDestruct "H" as "[$ $]". by iFrame.
  Qed.
End ExclAuthHalves.
(* end hide *)

(** ** The library *)

Section GuardedBor.
  Context {Σ : gFunctors}.
  Context `{!llft_logicGS Σ}.
  Context `{!invGS Σ}.
  Context {S T : Type}.
  Context `{!gmbG Σ S T}.
  Context (c : S → T → iProp Σ).
  Context `{c_timeless : !∀ s t, Timeless (c s t)}.

  Implicit Types (γ : gmb_name) (s : S) (t : T) (κ : lft).

  (** The fragments. [gmb_a] and [gmb_b] are exclusive, in disjoint ghost names. *)
  Definition gmb_a γ s : iProp Σ := xa_frag (gmb_a_name γ) (GmbHere (T:=T) s).
  Definition gmb_b γ t : iProp Σ := xa_frag (gmb_b_name γ) (GmbIn (S:=S) t).
  (* the mover's half of (L1), [a_out(t)] *)
  Local Definition gmb_a_out γ t : iProp Σ := xa_frag (gmb_a_name γ) (GmbMoving (S:=S) t).
  (* the back-map's half of (L3), [b_out(s, κ)] *)
  Local Definition gmb_b_out γ s κ : iProp Σ := xa_frag (gmb_b_name γ) (GmbOut (T:=T) s κ).

  (** One authoritative copy of the state; the two invariants each hold one. *)
  Local Definition gmb_auth γ (sa : gmb_sstate S T) (tb : gmb_tstate S T) : iProp Σ :=
    xa_half (gmb_a_name γ) sa ∗ xa_half (gmb_b_name γ) tb.

  (** What the state invariant holds in each state. *)
  Local Definition gmb_state_body (sa : gmb_sstate S T) (tb : gmb_tstate S T) : iProp Σ :=
    match sa, tb with
    | GmbHere s, GmbIn t => c s t          (* idle: the instance holds the contents *)
    | GmbHere s, GmbOut s' _ => ⌜s = s'⌝  (* lent out: the borrow holds them *)
    | GmbMoving t, GmbIn t' => ⌜t = t'⌝   (* moving: the mover holds them *)
    | GmbDestroyed, GmbGone => True
    | _, _ => False
    end.

  Local Definition gmb_state_inv γ : iProp Σ :=
    ∃ st : gmb_sstate S T * gmb_tstate S T, gmb_auth γ st.1 st.2 ∗ gmb_state_body st.1 st.2.

  (** What the other invariant holds: in state [Out s κ], the special token of the lend and
      the guard that refutes an owned [gmb_a γ s] while the token is not returned. *)
  Local Definition gmb_other_body γ (tb : gmb_tstate S T) : iProp Σ :=
    match tb with
    | GmbOut s κ =>
        special_open κ ∗ (special_open κ &&{↑NllftG ∪ ↑NllftO; gmb_depth γ}&&> gmb_a γ s)
    | _ => True
    end.

  Local Definition gmb_other_inv γ : iProp Σ :=
    ∃ sa tb, gmb_auth γ sa tb ∗ gmb_other_body γ tb.

  (** The instance invariant: [guard_inv] and [other_inv] of the plan. *)
  Definition gmb_inv γ : iProp Σ :=
    (True &&{↑NllftUsr2}&&> gmb_state_inv γ) ∗ inv NllftUsr (gmb_other_inv γ).

  Global Instance gmb_inv_persistent γ : Persistent (gmb_inv γ).
  Proof. apply _. Qed.
  Global Instance gmb_a_timeless γ s : Timeless (gmb_a γ s).
  Proof. apply _. Qed.
  Global Instance gmb_b_timeless γ t : Timeless (gmb_b γ t).
  Proof. apply _. Qed.

  Lemma gmb_a_excl γ s s' : gmb_a γ s -∗ gmb_a γ s' -∗ False.
  Proof. apply xa_frag_excl. Qed.
  Lemma gmb_b_excl γ t t' : gmb_b γ t -∗ gmb_b γ t' -∗ False.
  Proof. apply xa_frag_excl. Qed.

  Lemma gmb_a_point γ s : factoring_props.point_prop (gmb_a γ s).
  Proof. apply factoring_props.point_prop_own. Qed.
  Lemma gmb_b_point γ t : factoring_props.point_prop (gmb_b γ t).
  Proof. apply factoring_props.point_prop_own. Qed.

  (* begin hide *)
  Local Instance gmb_state_body_timeless sa tb : Timeless (gmb_state_body sa tb).
  Proof using c_timeless. destruct sa, tb; apply _. Qed.
  Local Instance gmb_state_inv_timeless γ : Timeless (gmb_state_inv γ).
  Proof using c_timeless. rewrite /gmb_state_inv /gmb_auth. apply _. Qed.

  Local Lemma gmb_auth_agree γ sa tb sa' tb' :
    gmb_auth γ sa tb -∗ gmb_auth γ sa' tb' -∗ ⌜sa = sa' ∧ tb = tb'⌝.
  Proof.
    iIntros "[A1 B1] [A2 B2]".
    iDestruct (xa_half_agree with "A1 A2") as %->.
    iDestruct (xa_half_agree with "B1 B2") as %->. done.
  Qed.

  (* Open [guard_inv] (the state invariant) like an invariant. Callers open [other_inv] first:
     it is in [NllftUsr], disjoint from the [NllftG ∪ NllftO] mask of the stored guard. *)
  Local Lemma gmb_state_open E γ :
    ↑NllftUsr2 ⊆ E →
    (True &&{↑NllftUsr2}&&> gmb_state_inv γ) ={E, E ∖ ↑NllftUsr2}=∗
      ∃ sa tb, gmb_auth γ sa tb ∗ gmb_state_body sa tb ∗
        (∀ sa' tb', gmb_auth γ sa' tb' ∗ gmb_state_body sa' tb' ={E ∖ ↑NllftUsr2, E}=∗ True).
  Proof.
    iIntros (Hmask) "#G".
    iMod (guards_open True (gmb_state_inv γ) E (↑NllftUsr2) with "G []") as "[I Hcl]";
      [done|done|].
    iDestruct "I" as ([sa tb]) "[Auth Body]". iModIntro. iExists sa, tb. iFrame.
    iIntros (sa' tb') "[Auth Body]". iApply "Hcl". iExists (sa', tb'). iFrame.
  Qed.
  (* end hide *)

  (** (L0) Create. *)
  Lemma gmb_create E d s t :
    c s t ={E}=∗ ∃ γ, ⌜gmb_depth γ = d⌝ ∗ gmb_inv γ ∗ gmb_a γ s ∗ gmb_b γ t.
  Proof using c_timeless.
    iIntros "C".
    iMod (xa_alloc (GmbHere (T:=T) s)) as (γa) "(A1 & A2 & Fa)".
    iMod (xa_alloc (GmbIn (S:=S) t)) as (γb) "(B1 & B2 & Fb)".
    set (γ := GmbName γa γb d).
    iMod (guards_alloc E NllftUsr2 (gmb_state_inv γ) with "[A1 B1 C]") as "#G".
    { iNext. iExists (GmbHere s, GmbIn t). iFrame. }
    iDestruct (guards_remove_later_rhs with "G") as "#G'".
    iMod (inv_alloc NllftUsr E (gmb_other_inv γ) with "[A2 B2]") as "#I".
    { iNext. iExists (GmbHere s), (GmbIn t). iFrame. }
    iModIntro. iExists γ. iFrame "Fa Fb". iSplit; first done. iSplit; done.
  Qed.

  (** (L0) Destroy. The instance moves to its terminal state. *)
  Lemma gmb_destroy E γ s t :
    ↑Nllft ⊆ E →
    gmb_inv γ -∗ gmb_a γ s -∗ gmb_b γ t ={E}=∗ c s t.
  Proof using c_timeless.
    iIntros (Hmask) "[#G #I] Fa Fb".
    iInv "I" as (sa2 tb2) "[>[A2 B2] _]" "Hcl".
    iMod (gmb_state_open with "G") as (sa tb) "([A1 B1] & Body & Hcl2)"; first solve_ndisj.
    iDestruct (xa_half_frag_agree with "A1 Fa") as %->.
    iDestruct (xa_half_frag_agree with "B1 Fb") as %->.
    iDestruct (xa_half_agree with "A1 A2") as %<-.
    iDestruct (xa_half_agree with "B1 B2") as %<-.
    iMod (xa_update _ _ GmbDestroyed with "A1 A2 Fa") as "(A1 & A2 & _)".
    iMod (xa_update _ _ GmbGone with "B1 B2 Fb") as "(B1 & B2 & _)".
    iMod ("Hcl2" $! GmbDestroyed GmbGone with "[$A1 $B1]") as "_".
    iMod ("Hcl" with "[A2 B2]") as "_".
    { iNext. iExists GmbDestroyed, GmbGone. iFrame. }
    by iModIntro.
  Qed.

  (** (L1) Exchange (move). The mover gets the contents at the current [t], and must put back
      contents at the same [t], at any placement [s']. The credits pay for the later of
      [other_inv] and the step-index of the guard stored there, which refutes the lent-out
      state. *)
  Lemma gmb_move E γ s :
    ↑Nllft ⊆ E →
    gmb_inv γ -∗ £ (1 + gmb_depth γ) -∗ gmb_a γ s ={E}=∗
      ∃ t, c s t ∗ (∀ s', c s' t ={E}=∗ gmb_a γ s').
  Proof using c_timeless.
    iIntros (Hmask) "[#G #I] Lc Fa".
    iInv "I" as (sa2 tb2) "[>[A2 B2] Other]" "Hcl".
    iDestruct (xa_half_frag_agree with "A2 Fa") as %->.
    destruct tb2 as [t|s0 κ|].
    2: { (* lent out: the stored guard gives a second [gmb_a], a contradiction *)
      iDestruct "Lc" as "[Lc1 Lc]".
      iMod (lc_fupd_elim_later with "Lc1 Other") as "[Tok #SG]".
      iMod (guards_open_later (special_open κ) (gmb_a γ s0) (E ∖ ↑NllftUsr) (↑NllftG ∪ ↑NllftO)
              with "SG Tok") as "H"; first solve_ndisj.
      iMod (lc_fupd_add_laterN with "Lc H") as "[Fa' _]".
      iDestruct (gmb_a_excl with "Fa Fa'") as %[]. }
    all: iMod (gmb_state_open with "G") as (sa tb) "([A1 B1] & Body & Hcl2)";
      first solve_ndisj.
    all: iDestruct (gmb_auth_agree with "[$A1 $B1] [$A2 $B2]") as %[-> ->].
    2: { by iDestruct "Body" as %[]. }
    iMod (xa_update _ _ (GmbMoving t) with "A1 A2 Fa") as "(A1 & A2 & Fout)".
    iMod ("Hcl2" $! (GmbMoving t) (GmbIn t) with "[$A1 $B1]") as "_"; first by rewrite /gmb_state_body.
    iMod ("Hcl" with "[A2 B2]") as "_".
    { iNext. iExists (GmbMoving t), (GmbIn t). iFrame. }
    iModIntro. iExists t. iFrame "Body".
    (* the way back *)
    iIntros (s') "C".
    iInv "I" as (sa2 tb2) "[>[A2 B2] _]" "Hcl".
    iDestruct (xa_half_frag_agree with "A2 Fout") as %->.
    iMod (gmb_state_open with "G") as (sa tb) "([A1 B1] & Body & Hcl2)"; first solve_ndisj.
    iDestruct (gmb_auth_agree with "[$A1 $B1] [$A2 $B2]") as %[-> ->].
    destruct tb2 as [t'| |]; [|by iDestruct "Body" as %[]..].
    iDestruct "Body" as %<-.
    iMod (xa_update _ _ (GmbHere s') with "A1 A2 Fout") as "(A1 & A2 & Fa)".
    iMod ("Hcl2" $! (GmbHere s') (GmbIn t) with "[$A1 $B1 $C]") as "_".
    iMod ("Hcl" with "[A2 B2]") as "_".
    { iNext. iExists (GmbHere s'), (GmbIn t). iFrame. }
    by iModIntro.
  Qed.

  (** (L2) Shared. *)
  Lemma gmb_share G F n γ s t :
    ↑NllftUsr2 ⊆ F →
    gmb_inv γ -∗ (G &&{F; n}&&> gmb_a γ s) -∗ (G &&{F; n}&&> gmb_b γ t) -∗
      (G &&{F; n}&&> c s t).
  Proof using c_timeless.
    iIntros (Hmask) "[#GI _] #Ga #Gb".
    iDestruct (guards_weaken_mask _ F with "GI") as "#GI'"; first done.
    iDestruct (guards_transitive_right F G True%I with "[] GI'") as "#GS".
    { iApply guards_true. }
    iDestruct (lguards_weaken_later _ _ _ 0 n with "GS") as "#GS'"; first lia.
    (* the [a] side: the state is [Here s] *)
    iDestruct (guards_strengthen_exists _ G (gmb_a γ s)
                 (λ st, ⌜st.1 = GmbHere s⌝)%I
                 (λ st, gmb_auth γ st.1 st.2 ∗ gmb_state_body st.1 st.2)%I F n
                 with "Ga GS'") as "#G1".
    { intros st. iIntros "H". iApply (xa_frag_and_half (X:=gmb_sstate S T) (gmb_a_name γ)). iSplit.
      - iDestruct "H" as "[$ _]".
      - iDestruct "H" as "[_ [[$ _] _]]". }
    (* the [b] side: the state is [In t] *)
    iDestruct (guards_strengthen_exists _ G (gmb_b γ t)
                 (λ st, ⌜st.2 = GmbIn t⌝)%I
                 (λ st, (gmb_auth γ st.1 st.2 ∗ gmb_state_body st.1 st.2) ∗ ⌜st.1 = GmbHere s⌝)%I
                 F n with "Gb G1") as "#G2".
    { intros st. iIntros "H". iApply (xa_frag_and_half (X:=gmb_tstate S T) (gmb_b_name γ)). iSplit.
      - iDestruct "H" as "[$ _]".
      - iDestruct "H" as "[_ [[[_ $] _] _]]". }
    iApply (guards_transitive_left with "G2").
    iApply guards_weaken. iModIntro.
    iIntros "H". iDestruct "H" as ([sa tb]) "[[[Auth Body] %Ha] %Hb]".
    simpl in Ha, Hb. subst sa tb. iFrame "Body".
    iIntros "C". iExists (GmbHere s, GmbIn t). by iFrame.
  Qed.

  (* begin hide *)
  (* The core of (L3): the state moves from [In t] to [Out s κ], given the token. *)
  Local Lemma gmb_lend_fwd E γ κ s t n :
    ↑Nllft ⊆ E → n ≤ gmb_depth γ →
    llft_ctx -∗ gmb_inv γ -∗ (@[κ] &&{↑NllftG; n}&&> gmb_a γ s) -∗ £ n -∗
    special_open κ -∗ gmb_b γ t ={E}=∗ c s t ∗ gmb_b_out γ s κ.
  Proof using c_timeless.
    iIntros (Hmask Hn) "#LFT [#GI #I] #Ga Lc Tok Fb".
    iDestruct (llftl_special_open_guard κ with "LFT") as "#SG".
    iDestruct (guards_weaken_mask _ (↑NllftG ∪ ↑NllftO) with "Ga") as "#Ga'"; first set_solver.
    iDestruct (guards_transitive_right with "SG Ga'") as "#SA".
    iDestruct (lguards_weaken_later _ _ _ n (gmb_depth γ) with "SA") as "#SA'"; first done.
    iDestruct (guards_weaken_mask _ (↑NllftG ∪ ↑NllftO) with "GI") as "#GI'"; first solve_ndisj.
    iDestruct (guards_transitive (↑NllftG ∪ ↑NllftO) (special_open κ) True%I
                 with "[] GI'") as "#GS".
    { iApply guards_true. }
    iDestruct (lguards_weaken_later _ _ _ 0 n with "GS") as "#GS'"; first lia.
    iDestruct (guards_strengthen_exists _ (special_open κ) (gmb_a γ s)
                 (λ st, ⌜st.1 = GmbHere s⌝)%I
                 (λ st, gmb_auth γ st.1 st.2 ∗ gmb_state_body st.1 st.2)%I _ n
                 with "SA GS'") as "#G1".
    { intros st. iIntros "H". iApply (xa_frag_and_half (X:=gmb_sstate S T) (gmb_a_name γ)). iSplit.
      - iDestruct "H" as "[$ _]".
      - iDestruct "H" as "[_ [[$ _] _]]". }
    iInv "I" as (sa2 tb2) "[>[A2 B2] _]" "Hcl".
    iDestruct (xa_half_frag_agree with "B2 Fb") as %->.
    iMod (guards_open_later with "G1 Tok") as "St"; first solve_ndisj.
    iMod (lc_fupd_add_laterN with "Lc St") as "[St Hcl2]".
    iDestruct "St" as ([sa tb]) "[[[A1 B1] Body] %Hsa]". simpl in Hsa. subst sa.
    iSimpl in "A1 B1 Body".
    iDestruct (gmb_auth_agree with "[$A1 $B1] [$A2 $B2]") as %[<- ->].
    iMod (xa_update _ _ (GmbOut s κ) with "B1 B2 Fb") as "(B1 & B2 & Fout)".
    iMod ("Hcl2" with "[A1 B1]") as "Tok".
    { iExists (GmbHere s, GmbOut s κ). by iFrame. }
    iMod ("Hcl" with "[A2 B2 Tok]") as "_".
    { iNext. iExists (GmbHere s), (GmbOut s κ). iFrame. iFrame "SA'". }
    by iFrame.
  Qed.

  (* The back-map of (L3): the state moves from [Out s κ] back to [In t'], and the token is
     returned. *)
  Local Lemma gmb_lend_back γ κ s t' :
    gmb_inv γ -∗ gmb_b_out γ s κ -∗ c s t' ={↑NllftUsr ∪ ↑NllftUsr2}=∗
      gmb_b γ t' ∗ special_open κ.
  Proof using c_timeless.
    iIntros "[#GI #I] Fout C".
    iInv "I" as (sa2 tb2) "[>[A2 B2] Other]" "Hcl".
    iDestruct (xa_half_frag_agree with "B2 Fout") as %->.
    iDestruct "Other" as "[>Tok _]".
    iMod (gmb_state_open with "GI") as (sa tb) "([A1 B1] & Body & Hcl2)"; first solve_ndisj.
    iDestruct (gmb_auth_agree with "[$A1 $B1] [$A2 $B2]") as %[-> ->].
    destruct sa2 as [s0| |]; [|by iDestruct "Body" as %[]..].
    iDestruct "Body" as %->.
    iMod (xa_update _ _ (GmbIn t') with "B1 B2 Fout") as "(B1 & B2 & Fb)".
    iMod ("Hcl2" $! (GmbHere s) (GmbIn t') with "[$A1 $B1 $C]") as "_".
    iMod ("Hcl" with "[A2 B2]") as "_".
    { iNext. iExists (GmbHere s), (GmbIn t'). iFrame. }
    by iFrame.
  Qed.
  (* end hide *)

  (** (L3) Mutable. The guard of [gmb_a γ s] comes from the owner's share. Its step-index
      [n] must be at most the depth of the instance (it is stored in [other_inv] for (L1));
      the credits pay for it. *)
  Lemma gmb_lend_later E γ κ s n :
    ↑Nllft ⊆ E → n ≤ gmb_depth γ →
    llft_ctx -∗ gmb_inv γ -∗ (@[κ] &&{↑NllftG; n}&&> gmb_a γ s) -∗ £ n -∗
    &{κ} (∃ t, gmb_b γ t) -∗ @[κ] ={E}=∗ &{κ} (∃ t, c s t) ∗ @[κ].
  Proof using c_timeless.
    iIntros (Hmask Hn) "#LFT #GI #Ga Lc Bor Alive".
    iMod (llftl_bor_acc_special with "LFT Bor Alive") as "(Fb & Tok & Close)"; first done.
    iDestruct "Fb" as ">[%t Fb]".
    iMod (gmb_lend_fwd with "LFT GI Ga Lc Tok Fb") as "[C Fout]"; [done..|].
    iApply (fupd_mask_mono (↑Nllft)); first done.
    iApply ("Close" $! (∃ t', c s t')%I with "[Fout C]").
    iSplitR "C"; last by iExists t.
    iNext. iIntros "[C _]". iDestruct "C" as ">[%t' C]".
    iMod (gmb_lend_back with "GI Fout C") as "[Fb Tok]".
    iModIntro. iFrame "Tok". iNext. by iExists t'.
  Qed.

  (** (L3), guarded: the lifetime is held through a guard [G &&> @[κ]]. *)
  Lemma gmb_lend_guarded_later E G γ κ s n :
    Timeless G → ↑Nllft ⊆ E → n ≤ gmb_depth γ →
    llft_ctx -∗ gmb_inv γ -∗ (@[κ] &&{↑NllftG; n}&&> gmb_a γ s) -∗ £ n -∗
    &{κ} (∃ t, gmb_b γ t) -∗ (G &&{↑NllftG}&&> @[κ]) -∗ G ={E}=∗ &{κ} (∃ t, c s t) ∗ G.
  Proof using c_timeless.
    iIntros (HG Hmask Hn) "#LFT #GI #Ga Lc Bor #Gk G".
    iMod (llftl_bor_acc_special_guarded with "LFT Bor Gk G") as "(Fb & Tok & Close)"; first done.
    iDestruct "Fb" as ">[%t Fb]".
    iMod (gmb_lend_fwd with "LFT GI Ga Lc Tok Fb") as "[C Fout]"; [done..|].
    iApply (fupd_mask_mono (↑Nllft)); first done.
    iApply ("Close" $! (∃ t', c s t')%I with "[Fout C]").
    iSplitR "C"; last by iExists t.
    iNext. iIntros "C". iDestruct "C" as ">[%t' C]".
    iMod (gmb_lend_back with "GI Fout C") as "[Fb Tok]".
    iModIntro. iFrame "Tok". iNext. by iExists t'.
  Qed.

  (** (L3) with a guard at step-index 0 (any depth). *)
  Lemma gmb_lend E γ κ s :
    ↑Nllft ⊆ E →
    llft_ctx -∗ gmb_inv γ -∗ (@[κ] &&{↑NllftG}&&> gmb_a γ s) -∗
    &{κ} (∃ t, gmb_b γ t) -∗ @[κ] ={E}=∗ &{κ} (∃ t, c s t) ∗ @[κ].
  Proof using c_timeless.
    iIntros (Hmask) "#LFT #GI #Ga Bor Alive". iMod lc_zero as "Lc".
    iApply (gmb_lend_later with "LFT GI Ga Lc Bor Alive"); [done|lia].
  Qed.

  Lemma gmb_lend_guarded E G γ κ s :
    Timeless G → ↑Nllft ⊆ E →
    llft_ctx -∗ gmb_inv γ -∗ (@[κ] &&{↑NllftG}&&> gmb_a γ s) -∗
    &{κ} (∃ t, gmb_b γ t) -∗ (G &&{↑NllftG}&&> @[κ]) -∗ G ={E}=∗ &{κ} (∃ t, c s t) ∗ G.
  Proof using c_timeless.
    iIntros (HG Hmask) "#LFT #GI #Ga Bor #Gk G". iMod lc_zero as "Lc".
    iApply (gmb_lend_guarded_later with "LFT GI Ga Lc Bor Gk G"); [done|lia].
  Qed.
End GuardedBor.

Global Typeclasses Opaque gmb_a gmb_b gmb_inv.
