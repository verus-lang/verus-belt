From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth excl agree lib.excl_auth.
From iris.base_logic.lib Require Import invariants.
From iris.algebra Require Import excl.
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
- (L3) [gmb_lend], [gmb_lend_guarded] (and [_later] variants for share guards with a
  step-index): a guard [@[κ] &&> gmb_a γ s] and a borrow [&{κ} (∃ t, gmb_b γ t)] give a
  borrow [&{κ} (∃ t, c s t)];
- (L4) is automatic: when [κ] ends, the back-map of the lend puts the contents back.

Lazy lends (phase 2b, see "Outcome: phase 2b" of the plan): the back-map of a lend may
instead store the final contents _lazily_, as a payload with a _settle law_ that forces the
contents with the _bytes mask_ [gmb_bmask γ] of the instance and a dead token for the
lifetime of the lend ([gmb_lend_stop_lazy]); the lender gets a _claim_ [gmb_claim γ R]. The
lend is settled by the first of the mover ([gmb_move] forces the payload) and the lender
([gmb_claim_take]); the settler fixes the final value [t] of the contents, and the lender
gets the permission at [t] with the _residue_ [R t] of the settle law. Settling takes the
_settle lock_ (an exclusive token in the invariant [inv gmbLN], held for the whole
settlement), so that the payload can be forced with the other invariants of the instance
closed; the bytes mask is disjoint from [gmbN]. A permission that may still be a claim is
[gmb_b_uniq] ([gmb_b_uniq_settle] gives the eager permission [gmb_b_shr]).

Model (plan §2.2): the state [(sa, tb)] is kept twice, as two halves of an authority per
ghost name, one in each invariant: the state invariant [guard_inv], a guard
[True &&{↑NllftUsr2}&&> …] holding the contents when idle, and [other_inv], an invariant in
[NllftUsr] holding, while lent out for [κ], the token [special_open κ] and the guard
[special_open κ &&> gmb_a γ s]. In (L1), an owned [gmb_a γ s] together with that guard
refutes the lent-out state; this needs the credits of [gmb_move] (one for the later of
[other_inv], [gmb_depth γ] for the step-index of the stored guard).

We assume that [c] is timeless. This lets the state invariant be a guard without a later
([True &&{↑NllftUsr2}&&> …]), so that (L2) gives a guard of [c s t] at the step-index of its
inputs, and (L0), (L1), (L3) move [c] in and out of the instance without laters. The
intended instance (fancy bytes at a location, [∃ fbs, l ↦b[^fbs] ∗ ⌜…⌝], with nested cells
owned through their own [gmb_a]) is timeless. *)

(** The namespaces of the settle lock and of the claims of lazy lends. The bytes mask of an
    instance (the mask of its settle laws) is disjoint from [gmbN]. *)
Definition gmbN : namespace := nroot .@ "gmb".
Definition gmbLN : namespace := gmbN .@ "lock".
Definition gmbCN : namespace := gmbN .@ "claim".

(** The [b] side of the state: the contents are [In t], lent out at placement [s] for [κ]
    ([Out s κ lz]; [lz] tells whether the back-map may store the contents lazily), pending
    after a lazy lend ([Pend s κ γc γp], with the ghost names of the claim of the lender), or
    the instance is destroyed ([Gone]). *)
Inductive gmb_tstate (S T : Type) :=
  | GmbIn (t : T)
  | GmbOut (s : S) (κ : lft) (lz : bool)
  | GmbPend (s : S) (κ : lft) (γc γp : gname)
  | GmbGone.
Global Arguments GmbIn {S T} t.
Global Arguments GmbOut {S T} s κ lz.
Global Arguments GmbPend {S T} s κ γc γp.
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
  gmb_tokG :: inG Σ (exclR unitO);
}.

Definition gmbΣ (S T : Type) : gFunctors := #[
  GFunctor (excl_authR (leibnizO (gmb_sstate S T)));
  GFunctor (excl_authR (leibnizO (gmb_tstate S T)));
  GFunctor (exclR unitO)
].

Global Instance subG_gmbΣ {Σ} S T : subG (gmbΣ S T) Σ → gmbG Σ S T.
Proof. solve_inG. Qed.

(** An instance has two ghost names, one per side, the ghost name of its settle lock, a
    _depth_ (the largest step-index of the guards of [gmb_a] that (L3) accepts) and a _bytes
    mask_ (the mask of the settle laws of its lazy lends), fixed when it is created. *)
Record gmb_name := GmbName {
  gmb_a_name : gname; gmb_b_name : gname; gmb_k_name : gname;
  gmb_depth : nat; gmb_bmask : coPset }.

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
  (** The mover's half of (L1) ([a_out(t)] of the plan): the token of a move in progress
      ([gmb_move_tok]); it is exclusive with [gmb_a γ s] ([gmb_a_moving_excl]). *)
  Definition gmb_moving γ t : iProp Σ := xa_frag (gmb_a_name γ) (GmbMoving (S:=S) t).
  (** The lender's half of (L3) while the contents are lent out at placement [s] for [κ]
      ([b_out(s, κ)] of the plan): it is held by the back-map of the lend, and given back
      for [gmb_b] by [gmb_lend_stop]; [gmb_lent_lz] is that of a lazy lend, given back for a
      claim by [gmb_lend_stop_lazy]. *)
  Definition gmb_lent γ s κ : iProp Σ := xa_frag (gmb_b_name γ) (GmbOut (T:=T) s κ false).
  Definition gmb_lent_lz γ s κ : iProp Σ := xa_frag (gmb_b_name γ) (GmbOut (T:=T) s κ true).

  (** Exclusive tokens: the settle lock, and the tokens of the claims. *)
  Local Definition gmb_tok (γt : gname) : iProp Σ := own γt (Excl ()).

  (** A dead token for an outer lifetime of a borrow at [κ], as given to the back-maps of
      the guarded special openings ([llftl_bor_acc_special_guarded_dead]). *)
  Definition gmb_bdead κ : iProp Σ := ∃ κ', κ ⊑ κ' ∗ [†κ'].

  (** The payload of a pending lazy lend: the final contents [Q] (under a later), and its
      settle law, which forces the contents with the bytes mask and gives a residue [R t];
      the credits pay for the laters of the payload and of the residue, and for the
      pending state of [other_inv] while the mover settles. *)
  Local Definition gmb_payload_n (n : nat) γ s κ (R : T → iProp Σ) : iProp Σ :=
    ∃ Q : iProp Σ, ▷ Q ∗ (Q -∗ gmb_bdead κ ={gmb_bmask γ}=∗ ∃ t, c s t ∗ R t) ∗
      gmb_bdead κ ∗ £ n.
  Local Definition gmb_payload γ s κ R : iProp Σ := gmb_payload_n 4 γ s κ R.

  (** The claim invariant of a lazy lend, with claim token [γc] and pending token [γp]: the
      lend is pending (with the [b] fragment and the payload), being settled (the payload is
      with the settler, who holds the lock), settled (the permission and the residue are
      deposited for the lender, with a credit), or claimed. *)
  Local Definition gmb_claim_inv γ (γc γp : gname) (R : T → iProp Σ) : iProp Σ :=
    (∃ s κ, xa_frag (gmb_b_name γ) (GmbPend (T:=T) s κ γc γp) ∗ gmb_payload γ s κ R) ∨
    (gmb_tok (gmb_k_name γ)) ∨
    (gmb_tok γp ∗ £ 1 ∗ ∃ t, gmb_b γ t ∗ R t) ∨
    (gmb_tok γp ∗ gmb_tok γc).

  (** The lender's claim on a lazy lend: its residue predicate is [R]. *)
  Definition gmb_claim γ (R : T → iProp Σ) : iProp Σ :=
    ∃ γc γp, gmb_tok γc ∗ inv gmbCN (gmb_claim_inv γ γc γp R).

  (** The permission held by the body of a unique borrow, which may still be a claim
      (L3/L3p take it). *)
  Definition gmb_b_uniq γ (R : T → iProp Σ) : iProp Σ :=
    (∃ t, gmb_b γ t ∗ R t) ∨ gmb_claim γ R.

  (** One authoritative copy of the state; the two invariants each hold one. *)
  Local Definition gmb_auth γ (sa : gmb_sstate S T) (tb : gmb_tstate S T) : iProp Σ :=
    xa_half (gmb_a_name γ) sa ∗ xa_half (gmb_b_name γ) tb.

  (** What the state invariant holds in each state. *)
  Local Definition gmb_state_body (sa : gmb_sstate S T) (tb : gmb_tstate S T) : iProp Σ :=
    match sa, tb with
    | GmbHere s, GmbIn t => c s t          (* idle: the instance holds the contents *)
    | GmbHere s, GmbOut s' _ _ => ⌜s = s'⌝  (* lent out: the borrow holds them *)
    | GmbHere s, GmbPend s' _ _ _ => ⌜s = s'⌝  (* pending: the payload holds them *)
    | GmbMoving t, GmbIn t' => ⌜t = t'⌝   (* moving: the mover holds them *)
    | GmbDestroyed, GmbGone => True
    | _, _ => False
    end.

  Local Definition gmb_state_inv γ : iProp Σ :=
    ∃ st : gmb_sstate S T * gmb_tstate S T, gmb_auth γ st.1 st.2 ∗ gmb_state_body st.1 st.2.

  (** What the other invariant holds: in state [Out s κ lz], the special token of the lend,
      the guard that refutes an owned [gmb_a γ s] while the token is not returned, the
      credits that pay for that refutation (prepaid by the lender, so that (L1) needs no
      credits), and (for a lazy lend) the credits of the payload; in state [Pend], the
      pending token, a credit for the later of the claim invariant, and the claim
      invariant. *)
  Local Definition gmb_other_body γ (tb : gmb_tstate S T) : iProp Σ :=
    match tb with
    | GmbOut s κ lz =>
        special_open κ ∗ (special_open κ &&{↑NllftG ∪ ↑NllftO; gmb_depth γ}&&> gmb_a γ s) ∗
        £ (1 + gmb_depth γ) ∗ (if lz then £ 4 else True)%I
    | GmbPend s κ γc γp => gmb_tok γp ∗ £ 1 ∗ ∃ R, inv gmbCN (gmb_claim_inv γ γc γp R)
    | _ => True
    end%I.

  Local Definition gmb_other_inv γ : iProp Σ :=
    ∃ sa tb, gmb_auth γ sa tb ∗ gmb_other_body γ tb.

  (** The instance invariant: [guard_inv] and [other_inv] of the plan, and the settle lock. *)
  Definition gmb_inv γ : iProp Σ :=
    (True &&{↑NllftUsr2}&&> gmb_state_inv γ) ∗ inv NllftUsr (gmb_other_inv γ) ∗
    inv gmbLN (gmb_tok (gmb_k_name γ)) ∗ ⌜gmb_bmask γ ## ↑gmbN⌝.

  Global Instance gmb_inv_persistent γ : Persistent (gmb_inv γ).
  Proof. apply _. Qed.
  Global Instance gmb_a_timeless γ s : Timeless (gmb_a γ s).
  Proof. apply _. Qed.
  Global Instance gmb_b_timeless γ t : Timeless (gmb_b γ t).
  Proof. apply _. Qed.
  Global Instance gmb_bdead_persistent κ : Persistent (gmb_bdead κ).
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

  Local Lemma gmb_tok_excl γt : gmb_tok γt -∗ gmb_tok γt -∗ False.
  Proof. iIntros "A B". by iDestruct (own_valid_2 with "A B") as %?. Qed.

  Local Lemma gmb_tok_alloc : ⊢ |==> ∃ γt, gmb_tok γt.
  Proof. iApply own_alloc. done. Qed.

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

  (* Forcing the payload of a pending lend, with the bytes mask: the credits strip the
     laters of the payload (one of them is kept for the deposit of the residue). *)
  Local Lemma gmb_payload_force E n γ s κ R :
    gmb_bmask γ ⊆ E →
    ▷ gmb_payload_n (2 + n) γ s κ R ={E}=∗ £ n ∗ ∃ t, c s t ∗ R t.
  Proof.
    iIntros (?) "P".
    iMod (bi.later_exist_except_0 with "P") as (Q) "(Q & Law & Dead & >£)".
    iDestruct (lc_split 1 (1 + n) with "£") as "[£1 £]".
    iDestruct (lc_split 1 n with "£") as "[£2 £3]".
    iCombine "Q Law Dead" as "QL".
    iMod (lc_fupd_elim_later with "£1 QL") as "(Q & Law & Dead)".
    iMod (lc_fupd_elim_later with "£2 Q") as "Q".
    iMod (fupd_mask_mono with "(Law Q Dead)") as "$"; [done|]. by iFrame.
  Qed.

  (* One of the credits of a payload. *)
  Local Lemma gmb_payload_credit E n γ s κ R :
    ▷ gmb_payload_n (1 + n) γ s κ R ={E}=∗ £ 1 ∗ ▷ gmb_payload_n n γ s κ R.
  Proof.
    iIntros "P".
    iMod (bi.later_exist_except_0 with "P") as (Q) "(Q & Law & Dead & >£)".
    iDestruct (lc_split 1 n with "£") as "[$ £]". iModIntro. iNext. iExists Q. iFrame.
  Qed.

  (* The end of a settlement: the state goes from [Pend] to [In t]. The caller holds the [b]
     fragment of the pending state and the forced contents. *)
  Local Lemma gmb_settle_finish E γ s κ γc γp t :
    ↑NllftUsr ∪ ↑NllftUsr2 ⊆ E →
    gmb_inv γ -∗ xa_frag (gmb_b_name γ) (GmbPend (T:=T) s κ γc γp) -∗ c s t ={E}=∗
      gmb_tok γp ∗ gmb_b γ t.
  Proof using c_timeless.
    iIntros (?) "(#GI & #I & _) F C".
    iInv "I" as (sa2 tb2) "[>[A2 B2] Other]" "Hcl".
    iDestruct (xa_half_frag_agree with "B2 F") as %->.
    iDestruct "Other" as "[>Tp _]".
    iMod (gmb_state_open with "GI") as (sa tb) "([A1 B1] & Body & Hcl2)"; first solve_ndisj.
    iDestruct (gmb_auth_agree with "[$A1 $B1] [$A2 $B2]") as %[-> ->].
    destruct sa2 as [s0| |]; [|by iDestruct "Body" as %[]..].
    iDestruct "Body" as %->.
    iMod (xa_update _ _ (GmbIn t) with "B1 B2 F") as "(B1 & B2 & Fb)".
    iMod ("Hcl2" $! (GmbHere s) (GmbIn t) with "[$A1 $B1 $C]") as "_".
    iMod ("Hcl" with "[A2 B2]") as "_".
    { iNext. iExists (GmbHere s), (GmbIn t). iFrame. }
    by iFrame.
  Qed.
  (* end hide *)

  (** (L0) Create, with a bytes mask [EB] for the settle laws of lazy lends. *)
  Lemma gmb_create_mask E d EB s t :
    EB ## ↑gmbN →
    c s t ={E}=∗ ∃ γ, ⌜gmb_depth γ = d ∧ gmb_bmask γ = EB⌝ ∗ gmb_inv γ ∗ gmb_a γ s ∗ gmb_b γ t.
  Proof using c_timeless.
    iIntros (HEB) "C".
    iMod (xa_alloc (GmbHere (T:=T) s)) as (γa) "(A1 & A2 & Fa)".
    iMod (xa_alloc (GmbIn (S:=S) t)) as (γb) "(B1 & B2 & Fb)".
    iMod gmb_tok_alloc as (γk) "K".
    set (γ := GmbName γa γb γk d EB).
    iMod (guards_alloc E NllftUsr2 (gmb_state_inv γ) with "[A1 B1 C]") as "#G".
    { iNext. iExists (GmbHere s, GmbIn t). iFrame. }
    iDestruct (guards_remove_later_rhs with "G") as "#G'".
    iMod (inv_alloc NllftUsr E (gmb_other_inv γ) with "[A2 B2]") as "#I".
    { iNext. iExists (GmbHere s), (GmbIn t). iFrame. }
    iMod (inv_alloc gmbLN E (gmb_tok γk) with "[K]") as "#L"; first by iNext.
    iModIntro. iExists γ. iFrame "Fa Fb". iSplit; first done. iFrame "#". done.
  Qed.

  (** (L0) Create (with the empty bytes mask). *)
  Lemma gmb_create E d s t :
    c s t ={E}=∗ ∃ γ, ⌜gmb_depth γ = d ∧ gmb_bmask γ = ∅⌝ ∗ gmb_inv γ ∗ gmb_a γ s ∗ gmb_b γ t.
  Proof using c_timeless. iApply gmb_create_mask. set_solver. Qed.

  (** (L0) Destroy. The instance moves to its terminal state. *)
  Lemma gmb_destroy E γ s t :
    ↑Nllft ⊆ E →
    gmb_inv γ -∗ gmb_a γ s -∗ gmb_b γ t ={E}=∗ c s t.
  Proof using c_timeless.
    iIntros (Hmask) "(#G & #I & _) Fa Fb".
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

  (* begin hide *)
  (* The move from the idle state [In t]: inside [other_inv] (whose half is [In t]). *)
  Local Lemma gmb_move_in E γ s t :
    ↑NllftUsr2 ⊆ E →
    (True &&{↑NllftUsr2}&&> gmb_state_inv γ) -∗ xa_half (gmb_a_name γ) (GmbHere (T:=T) s) -∗
    xa_half (gmb_b_name γ) (GmbIn (S:=S) t) -∗ gmb_a γ s ={E}=∗
      xa_half (gmb_a_name γ) (GmbMoving (S:=S) t) ∗ xa_half (gmb_b_name γ) (GmbIn (S:=S) t) ∗
      gmb_moving γ t ∗ c s t.
  Proof using c_timeless.
    iIntros (?) "#G A2 B2 Fa".
    iMod (gmb_state_open with "G") as (sa tb) "([A1 B1] & Body & Hcl2)"; first done.
    iDestruct (gmb_auth_agree with "[$A1 $B1] [$A2 $B2]") as %[-> ->].
    iMod (xa_update _ _ (GmbMoving t) with "A1 A2 Fa") as "(A1 & A2 & Fout)".
    iMod ("Hcl2" $! (GmbMoving t) (GmbIn t) with "[$A1 $B1]") as "_"; first by rewrite /gmb_state_body.
    iModIntro. by iFrame.
  Qed.
  (* end hide *)

  (** (L1) Exchange (move), with the token of the move in progress. The mover gets the
      contents at the current [t] and the token [gmb_moving γ t], and must put back contents
      at the same [t], at any placement [s'], with the token. No credits are needed: in the
      lent-out state, the credits for the refutation of the state (the later of [other_inv]
      and the step-index of the guard stored there) were prepaid by the lend. A pending lazy
      lend is settled first: the mover forces its payload (with the bytes mask, holding the
      settle lock), and deposits the permission and the residue for the lender. *)
  Lemma gmb_move_tok E γ s :
    ↑Nllft ∪ ↑gmbN ∪ gmb_bmask γ ⊆ E →
    gmb_inv γ -∗ gmb_a γ s ={E}=∗
      ∃ t, c s t ∗ gmb_moving γ t ∗ (∀ s', gmb_moving γ t -∗ c s' t ={E}=∗ gmb_a γ s').
  Proof using c_timeless.
    iIntros (Hmask) "(#G & #I & #L & %HEB) Fa".
    iAssert (∀ t s', gmb_moving γ t -∗ c s' t ={E}=∗ gmb_a γ s')%I as "Back".
    { iIntros (t s') "Fout C".
      iInv "I" as (sa2 tb2) "[>[A2 B2] Other]" "Hcl".
      iDestruct (xa_half_frag_agree with "A2 Fout") as %->.
      iMod (gmb_state_open with "G") as (sa tb) "([A1 B1] & Body & Hcl2)"; first solve_ndisj.
      iDestruct (gmb_auth_agree with "[$A1 $B1] [$A2 $B2]") as %[-> ->].
      destruct tb2 as [t'| | |]; [|by iDestruct "Body" as %[]..].
      iDestruct "Body" as %<-.
      iMod (xa_update _ _ (GmbHere s') with "A1 A2 Fout") as "(A1 & A2 & Fa)".
      iMod ("Hcl2" $! (GmbHere s') (GmbIn t) with "[$A1 $B1 $C]") as "_".
      iMod ("Hcl" with "[A2 B2 Other]") as "_".
      { iNext. iExists (GmbHere s'), (GmbIn t). iFrame. }
      by iModIntro. }
    iInv "L" as ">K" "HclL".
    iInv "I" as (sa2 tb2) "[>[A2 B2] Other]" "Hcl".
    iDestruct (xa_half_frag_agree with "A2 Fa") as %->.
    destruct tb2 as [t|s0 κ lz|s0 κ γc γp|].
    - (* idle *)
      iMod (gmb_move_in with "G A2 B2 Fa") as "(A2 & B2 & Fout & C)"; first solve_ndisj.
      iMod ("Hcl" with "[A2 B2]") as "_". { iNext. iExists (GmbMoving t), (GmbIn t). iFrame. }
      iMod ("HclL" with "[$K]") as "_".
      iModIntro. iExists t. iFrame "C Fout". iIntros (s'). by iApply "Back".
    - (* lent out: the stored guard gives a second [gmb_a], a contradiction; the stored
         credits pay for it *)
      iDestruct "Other" as "(>Tok & SG & >Lc & _)".
      iDestruct "Lc" as "[Lc1 Lc]".
      iMod (lc_fupd_elim_later with "Lc1 SG") as "#SG".
      iMod (guards_open_later (special_open κ) (gmb_a γ s0) _ (↑NllftG ∪ ↑NllftO)
              with "SG Tok") as "H"; first solve_ndisj.
      iMod (lc_fupd_add_laterN with "Lc H") as "[Fa' _]".
      iDestruct (gmb_a_excl with "Fa Fa'") as %[].
    - (* pending: settle first *)
      iDestruct "Other" as "(>Tp & >Lc1 & CIx)".
      iMod (lc_fupd_elim_later with "Lc1 CIx") as "(%R & #CI)".
      iInv "CI" as "[CIb|[>K'|[(>Tp' & _)|(>Tp' & _)]]]" "HclC".
      2: { iDestruct (gmb_tok_excl with "K K'") as %[]. }
      2,3: iDestruct (gmb_tok_excl with "Tp Tp'") as %[].
      iMod (bi.later_exist_except_0 with "CIb") as (s1) "CIb".
      iMod (bi.later_exist_except_0 with "CIb") as (κ1) "[>F P]".
      iDestruct (xa_half_frag_agree with "B2 F") as %[= <- <-].
      iMod (gmb_payload_credit with "P") as "[Lc1 P]".
      (* close [other_inv] and [CI] (with the lock as a placeholder), and force *)
      iMod ("HclC" with "[K]") as "_". { iNext. iRight. by iLeft. }
      iMod ("Hcl" with "[A2 B2 Tp Lc1]") as "_".
      { iNext. iExists (GmbHere s), (GmbPend s0 κ γc γp). iFrame. iExists R. iFrame "CI". }
      iMod (gmb_payload_force _ 1 with "P") as "(£ & %t & C & Res)".
      { assert (↑gmbLN ⊆@{coPset} ↑gmbN) by solve_ndisj. set_solver. }
      (* the state is now [In t]; then the move *)
      iMod (gmb_settle_finish with "[$G $I $L //] F C") as "[Tp Fb]"; first solve_ndisj.
      iInv "I" as (sa2 tb2) "[>[A2 B2] Other]" "Hcl".
      iDestruct (xa_half_frag_agree with "A2 Fa") as %->.
      iDestruct (xa_half_frag_agree with "B2 Fb") as %->.
      iMod (gmb_move_in with "G A2 B2 Fa") as "(A2 & B2 & Fout & C)"; first solve_ndisj.
      iMod ("Hcl" with "[A2 B2]") as "_". { iNext. iExists (GmbMoving t), (GmbIn t). iFrame. }
      (* deposit the permission and the residue for the lender, and release the lock *)
      iInv "CI" as "[CIb|[>K|[(>Tp' & _)|(>Tp' & _)]]]" "HclC".
      1: { iMod (bi.later_exist_except_0 with "CIb") as (s1) "CIb".
        iMod (bi.later_exist_except_0 with "CIb") as (κ1) "[>F _]".
        iDestruct (xa_frag_excl with "Fb F") as %[]. }
      2,3: iDestruct (gmb_tok_excl with "Tp Tp'") as %[].
      iMod ("HclC" with "[Tp £ Fb Res]") as "_".
      { iNext. iRight. iRight. iLeft. iFrame. }
      iMod ("HclL" with "[$K]") as "_".
      iModIntro. iExists t. iFrame "C Fout". iIntros (s'). by iApply "Back".
    - (* destroyed: impossible with [gmb_a] *)
      iMod (gmb_state_open with "G") as (sa tb) "([A1 B1] & Body & Hcl2)"; first solve_ndisj.
      iDestruct (gmb_auth_agree with "[$A1 $B1] [$A2 $B2]") as %[-> ->].
      by iDestruct "Body" as %[].
  Qed.

  (** (L1) Exchange (move). *)
  Lemma gmb_move E γ s :
    ↑Nllft ∪ ↑gmbN ∪ gmb_bmask γ ⊆ E →
    gmb_inv γ -∗ gmb_a γ s ={E}=∗ ∃ t, c s t ∗ (∀ s', c s' t ={E}=∗ gmb_a γ s').
  Proof using c_timeless.
    iIntros (Hmask) "#GI Fa".
    iMod (gmb_move_tok with "GI Fa") as (t) "(C & Tok & Back)"; first done.
    iModIntro. iExists t. iFrame "C". iIntros (s') "C". iApply ("Back" with "Tok C").
  Qed.

  (** The token of a move in progress excludes the move right. *)
  Lemma gmb_a_moving_excl γ s t : gmb_a γ s -∗ gmb_moving γ t -∗ False.
  Proof. apply xa_frag_excl. Qed.

  Global Instance gmb_moving_timeless γ t : Timeless (gmb_moving γ t).
  Proof. apply _. Qed.

  (** (L2) Shared. *)
  Lemma gmb_share G F n γ s t :
    ↑NllftUsr2 ⊆ F →
    gmb_inv γ -∗ (G &&{F; n}&&> gmb_a γ s) -∗ (G &&{F; n}&&> gmb_b γ t) -∗
      (G &&{F; n}&&> c s t).
  Proof using c_timeless.
    iIntros (Hmask) "(#GI & _) #Ga #Gb".
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

  Global Instance gmb_lent_timeless γ s κ : Timeless (gmb_lent γ s κ).
  Proof. apply _. Qed.

  (** (L3) at the level of special openings: [gmb_lend_start] and [gmb_lend_stop] are the
      two halves of a lend, for any kind of borrow that has a special opening (full borrows
      in [gmb_lend*] below, prophetic borrows in [guarded_bor_proph.v]). The opener of a
      borrow of [gmb_b γ t] at [κ] gets the token [special_open κ]; [gmb_lend_start] takes
      it with the permission and gives the contents. The back-map of the borrow, which runs
      when [κ] ends, uses [gmb_lend_stop] to put back contents at any value and get the
      permission at that value and the token. The lend prepays the credits [£ (1 + gmb_depth
      γ)] that (L1) would need to refute the lent-out state (they are stored in [other_inv]). *)
  Local Lemma gmb_lend_start_gen (lz : bool) E γ κ s t n :
    ↑Nllft ⊆ E → n ≤ gmb_depth γ →
    llft_ctx -∗ gmb_inv γ -∗ (@[κ] &&{↑NllftG; n}&&> gmb_a γ s) -∗ £ n -∗
    £ (1 + gmb_depth γ) -∗ (if lz then £ 4 else True)%I -∗
    special_open κ -∗ gmb_b γ t ={E}=∗ c s t ∗ xa_frag (gmb_b_name γ) (GmbOut (T:=T) s κ lz).
  Proof using c_timeless.
    iIntros (Hmask Hn) "#LFT (#GI & #I & _) #Ga Lc Pre Lz Tok Fb".
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
    iMod (xa_update _ _ (GmbOut s κ lz) with "B1 B2 Fb") as "(B1 & B2 & Fout)".
    iMod ("Hcl2" with "[A1 B1]") as "Tok".
    { iExists (GmbHere s, GmbOut s κ lz). by iFrame. }
    iMod ("Hcl" with "[A2 B2 Tok Pre Lz]") as "_".
    { iNext. iExists (GmbHere s), (GmbOut s κ lz). iFrame. iFrame "SA'". }
    by iFrame.
  Qed.

  Lemma gmb_lend_start E γ κ s t n :
    ↑Nllft ⊆ E → n ≤ gmb_depth γ →
    llft_ctx -∗ gmb_inv γ -∗ (@[κ] &&{↑NllftG; n}&&> gmb_a γ s) -∗ £ n -∗
    £ (1 + gmb_depth γ) -∗ special_open κ -∗ gmb_b γ t ={E}=∗ c s t ∗ gmb_lent γ s κ.
  Proof using c_timeless.
    iIntros (Hmask Hn) "#LFT #GI #Ga Lc Pre Tok Fb".
    iApply (gmb_lend_start_gen false with "LFT GI Ga Lc Pre [//] Tok Fb"); done.
  Qed.

  (** The start of a lazy lend: as [gmb_lend_start], storing four credits for the payload
      (two for its laters, one for the deposit of the residue, one for the pending state
      while the mover settles). *)
  Lemma gmb_lend_start_lazy E γ κ s t n :
    ↑Nllft ⊆ E → n ≤ gmb_depth γ →
    llft_ctx -∗ gmb_inv γ -∗ (@[κ] &&{↑NllftG; n}&&> gmb_a γ s) -∗ £ n -∗
    £ (1 + gmb_depth γ) -∗ £ 4 -∗ special_open κ -∗ gmb_b γ t ={E}=∗ c s t ∗ gmb_lent_lz γ s κ.
  Proof using c_timeless.
    iIntros (Hmask Hn) "#LFT #GI #Ga Lc Pre £ Tok Fb".
    iApply (gmb_lend_start_gen true with "LFT GI Ga Lc Pre £ Tok Fb"); done.
  Qed.

  Lemma gmb_lend_stop γ κ s t' :
    gmb_inv γ -∗ gmb_lent γ s κ -∗ c s t' ={↑NllftUsr ∪ ↑NllftUsr2}=∗
      gmb_b γ t' ∗ special_open κ.
  Proof using c_timeless.
    iIntros "(#GI & #I & _) Fout C".
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

  (** The end of a lazy lend, in the back-map of the borrow: the final contents [Q] are
      stored lazily, with a settle law that forces them with the bytes mask of the instance
      and the dead token, and gives a residue [R t]. The lender gets a claim, the lifetime
      logic its token. No forcing happens here. *)
  Lemma gmb_lend_stop_lazy γ κ s (Q : iProp Σ) (R : T → iProp Σ) :
    gmb_inv γ -∗ gmb_lent_lz γ s κ -∗ ▷ Q -∗ gmb_bdead κ -∗
    (Q -∗ gmb_bdead κ ={gmb_bmask γ}=∗ ∃ t, c s t ∗ R t) ={↑NllftUsr ∪ ↑NllftUsr2}=∗
      gmb_claim γ R ∗ special_open κ.
  Proof using c_timeless.
    iIntros "(#GI & #I & _) Fout Q #Dead Law".
    iMod gmb_tok_alloc as (γc) "Tc". iMod gmb_tok_alloc as (γp) "Tp".
    iInv "I" as (sa2 tb2) "[>[A2 B2] Other]" "Hcl".
    iDestruct (xa_half_frag_agree with "B2 Fout") as %->.
    iDestruct "Other" as "(>Tok & _ & >Pre & >£)".
    iDestruct "Pre" as "[Lc1 _]".
    iMod (gmb_state_open with "GI") as (sa tb) "([A1 B1] & Body & Hcl2)"; first solve_ndisj.
    iDestruct (gmb_auth_agree with "[$A1 $B1] [$A2 $B2]") as %[-> ->].
    destruct sa2 as [s0| |]; [|by iDestruct "Body" as %[]..].
    iDestruct "Body" as %->.
    iMod (xa_update _ _ (GmbPend s κ γc γp) with "B1 B2 Fout") as "(B1 & B2 & F)".
    iMod ("Hcl2" $! (GmbHere s) (GmbPend s κ γc γp) with "[$A1 $B1]") as "_"; first done.
    iMod (inv_alloc gmbCN _ (gmb_claim_inv γ γc γp R) with "[F Q Law £]") as "#CI".
    { iNext. iLeft. iExists s, κ. iFrame "F". iExists Q. iFrame. by iFrame "Dead". }
    iMod ("Hcl" with "[A2 B2 Tp Lc1]") as "_".
    { iNext. iExists (GmbHere s), (GmbPend s κ γc γp). iFrame. iExists R. iFrame "CI". }
    iModIntro. iFrame "Tok". iExists γc, γp. by iFrame.
  Qed.

  (** The lender's claim: it settles the lend if it is still pending (forcing the payload
      with the bytes mask, holding the settle lock), or takes the permission and the residue
      deposited by the settler. *)
  Lemma gmb_claim_take E γ R :
    ↑NllftUsr ∪ ↑NllftUsr2 ∪ ↑gmbN ∪ gmb_bmask γ ⊆ E →
    gmb_inv γ -∗ gmb_claim γ R ={E}=∗ ∃ t, gmb_b γ t ∗ R t.
  Proof using c_timeless.
    iIntros (HE) "(#G & #I & #L & %HEB) (%γc & %γp & Tc & #CI)".
    iInv "L" as ">K" "HclL".
    iInv "CI" as "[CIb|[>K'|[(>Tp & >£ & B)|(>Tp & >Tc')]]]" "HclC".
    - (* pending: settle *)
      iMod (bi.later_exist_except_0 with "CIb") as (s) "CIb".
      iMod (bi.later_exist_except_0 with "CIb") as (κ) "[>F P]".
      iMod ("HclC" with "[K]") as "_". { iNext. iRight. by iLeft. }
      iMod (gmb_payload_force _ 2 with "P") as "(_ & %t & C & Res)".
      { assert (↑gmbLN ⊆@{coPset} ↑gmbN) by solve_ndisj. set_solver. }
      iMod (gmb_settle_finish with "[$G $I $L //] F C") as "[Tp Fb]"; first solve_ndisj.
      iInv "CI" as "[CIb|[>K|[(>Tp' & _)|(>Tp' & _)]]]" "HclC".
      1: { iMod (bi.later_exist_except_0 with "CIb") as (s1) "CIb".
        iMod (bi.later_exist_except_0 with "CIb") as (κ1) "[>F _]".
        iDestruct (xa_frag_excl with "Fb F") as %[]. }
      2,3: iDestruct (gmb_tok_excl with "Tp Tp'") as %[].
      iMod ("HclC" with "[Tp Tc]") as "_". { iNext. iRight. iRight. iRight. iFrame. }
      iMod ("HclL" with "[$K]") as "_". iModIntro. iExists t. iFrame.
    - iDestruct (gmb_tok_excl with "K K'") as %[].
    - (* settled: take the deposit *)
      iMod (lc_fupd_elim_later with "£ B") as (t) "[Fb Res]".
      iMod ("HclC" with "[Tp Tc]") as "_". { iNext. iRight. iRight. iRight. iFrame. }
      iMod ("HclL" with "[$K]") as "_". iModIntro. iExists t. iFrame.
    - iDestruct (gmb_tok_excl with "Tc Tc'") as %[].
  Qed.

  Lemma gmb_b_uniq_intro γ R t : gmb_b γ t -∗ R t -∗ gmb_b_uniq γ R.
  Proof. iIntros "B R". iLeft. iExists t. iFrame. Qed.
  Lemma gmb_b_uniq_claim γ R : gmb_claim γ R -∗ gmb_b_uniq γ R.
  Proof. iIntros "C". by iRight. Qed.

  (** A permission that may still be a claim gives the eager permission. *)
  Lemma gmb_b_uniq_settle E γ R :
    ↑NllftUsr ∪ ↑NllftUsr2 ∪ ↑gmbN ∪ gmb_bmask γ ⊆ E →
    gmb_inv γ -∗ gmb_b_uniq γ R ={E}=∗ ∃ t, gmb_b γ t ∗ R t.
  Proof using c_timeless.
    iIntros (?) "#GI [$|C]"; [done|]. by iApply (gmb_claim_take with "GI C").
  Qed.

  (** (L3) Mutable. The guard of [gmb_a γ s] comes from the owner's share. Its step-index
      [n] must be at most the depth of the instance (it is stored in [other_inv] for (L1));
      the credits [£ n] pay for it, the credits [£ (1 + gmb_depth γ)] are prepaid for
      (L1). *)
  Lemma gmb_lend_later E γ κ s n :
    ↑Nllft ⊆ E → n ≤ gmb_depth γ →
    llft_ctx -∗ gmb_inv γ -∗ (@[κ] &&{↑NllftG; n}&&> gmb_a γ s) -∗ £ n -∗
    £ (1 + gmb_depth γ) -∗
    &{κ} (∃ t, gmb_b γ t) -∗ @[κ] ={E}=∗ &{κ} (∃ t, c s t) ∗ @[κ].
  Proof using c_timeless.
    iIntros (Hmask Hn) "#LFT #GI #Ga Lc Pre Bor Alive".
    iMod (llftl_bor_acc_special with "LFT Bor Alive") as "(Fb & Tok & Close)"; first done.
    iDestruct "Fb" as ">[%t Fb]".
    iMod (gmb_lend_start with "LFT GI Ga Lc Pre Tok Fb") as "[C Fout]"; [done..|].
    iApply (fupd_mask_mono (↑Nllft)); first done.
    iApply ("Close" $! (∃ t', c s t')%I with "[Fout C]").
    iSplitR "C"; last by iExists t.
    iNext. iIntros "[C _]". iDestruct "C" as ">[%t' C]".
    iMod (gmb_lend_stop with "GI Fout C") as "[Fb Tok]".
    iModIntro. iFrame "Tok". iNext. by iExists t'.
  Qed.

  (** (L3), guarded: the lifetime is held through a guard [G &&> @[κ]]. *)
  Lemma gmb_lend_guarded_later E G γ κ s n :
    Timeless G → ↑Nllft ⊆ E → n ≤ gmb_depth γ →
    llft_ctx -∗ gmb_inv γ -∗ (@[κ] &&{↑NllftG; n}&&> gmb_a γ s) -∗ £ n -∗
    £ (1 + gmb_depth γ) -∗
    &{κ} (∃ t, gmb_b γ t) -∗ (G &&{↑NllftG}&&> @[κ]) -∗ G ={E}=∗ &{κ} (∃ t, c s t) ∗ G.
  Proof using c_timeless.
    iIntros (HG Hmask Hn) "#LFT #GI #Ga Lc Pre Bor #Gk G".
    iMod (llftl_bor_acc_special_guarded with "LFT Bor Gk G") as "(Fb & Tok & Close)"; first done.
    iDestruct "Fb" as ">[%t Fb]".
    iMod (gmb_lend_start with "LFT GI Ga Lc Pre Tok Fb") as "[C Fout]"; [done..|].
    iApply (fupd_mask_mono (↑Nllft)); first done.
    iApply ("Close" $! (∃ t', c s t')%I with "[Fout C]").
    iSplitR "C"; last by iExists t.
    iNext. iIntros "C". iDestruct "C" as ">[%t' C]".
    iMod (gmb_lend_stop with "GI Fout C") as "[Fb Tok]".
    iModIntro. iFrame "Tok". iNext. by iExists t'.
  Qed.

  (** Lazy (L3), guarded: the permission may still be a claim (it is settled first), and the
      back-map stores the final contents [Q] lazily, with the settle law [Law]
      ([gmb_lend_stop_lazy]): the lender's inheritance is a claim. *)
  Lemma gmb_lend_guarded_lazy E G γ κ s n (Q : iProp Σ) (R : T → iProp Σ) :
    Timeless G → ↑Nllft ∪ ↑gmbN ∪ gmb_bmask γ ⊆ E → n ≤ gmb_depth γ →
    llft_ctx -∗ gmb_inv γ -∗ (@[κ] &&{↑NllftG; n}&&> gmb_a γ s) -∗ £ n -∗
    £ (1 + gmb_depth γ) -∗ £ 1 -∗ £ 4 -∗
    &{κ} (gmb_b_uniq γ R) -∗ (G &&{↑NllftG}&&> @[κ]) -∗ G -∗
    (∀ t, R t -∗ c s t ={E}=∗ ▷ Q) -∗
    □ (Q -∗ gmb_bdead κ ={gmb_bmask γ}=∗ ∃ t, c s t ∗ R t) ={E}=∗ &{κ} Q ∗ G.
  Proof using c_timeless.
    iIntros (HG Hmask Hn) "#LFT #GI #Ga Lc Pre £1 £3 Bor #Gk G ToQ #Law".
    iMod (llftl_bor_acc_special_guarded_dead with "LFT Bor Gk G") as "(Fb & Tok & Close)";
      first solve_ndisj.
    iMod (lc_fupd_elim_later with "£1 Fb") as "Fb".
    iMod (gmb_b_uniq_settle with "GI Fb") as (t) "[B Res]".
    { assert (↑NllftUsr ∪ ↑NllftUsr2 ⊆@{coPset} ↑Nllft) by solve_ndisj. set_solver. }
    iMod (gmb_lend_start_lazy with "LFT GI Ga Lc Pre £3 Tok B") as "[C Lent]"; [solve_ndisj|done|].
    iMod ("ToQ" with "Res C") as "Q".
    iApply (fupd_mask_mono (↑Nllft)); first solve_ndisj.
    iApply ("Close" $! Q with "[Lent $Q]").
    iNext. iIntros "[Q #Dead]".
    iMod (gmb_lend_stop_lazy with "GI Lent Q Dead [Law]") as "[Cl $]".
    { iIntros "Q D". by iApply ("Law" with "Q D"). }
    iModIntro. iNext. by iRight.
  Qed.

  (** (L3) with a guard at step-index 0 (any depth). *)
  Lemma gmb_lend E γ κ s :
    ↑Nllft ⊆ E →
    llft_ctx -∗ gmb_inv γ -∗ (@[κ] &&{↑NllftG}&&> gmb_a γ s) -∗ £ (1 + gmb_depth γ) -∗
    &{κ} (∃ t, gmb_b γ t) -∗ @[κ] ={E}=∗ &{κ} (∃ t, c s t) ∗ @[κ].
  Proof using c_timeless.
    iIntros (Hmask) "#LFT #GI #Ga Pre Bor Alive". iMod lc_zero as "Lc".
    iApply (gmb_lend_later with "LFT GI Ga Lc Pre Bor Alive"); [done|lia].
  Qed.

  Lemma gmb_lend_guarded E G γ κ s :
    Timeless G → ↑Nllft ⊆ E →
    llft_ctx -∗ gmb_inv γ -∗ (@[κ] &&{↑NllftG}&&> gmb_a γ s) -∗ £ (1 + gmb_depth γ) -∗
    &{κ} (∃ t, gmb_b γ t) -∗ (G &&{↑NllftG}&&> @[κ]) -∗ G ={E}=∗ &{κ} (∃ t, c s t) ∗ G.
  Proof using c_timeless.
    iIntros (HG Hmask) "#LFT #GI #Ga Pre Bor #Gk G". iMod lc_zero as "Lc".
    iApply (gmb_lend_guarded_later with "LFT GI Ga Lc Pre Bor Gk G"); [done|lia].
  Qed.
End GuardedBor.

(** The permission with the contents held eagerly by the instance ((L2) takes it): it is
    [gmb_b] itself; [gmb_b_uniq] may still be a claim. *)
Notation gmb_b_shr := gmb_b (only parsing).

Global Typeclasses Opaque gmb_a gmb_b gmb_lent gmb_lent_lz gmb_inv gmb_claim gmb_b_uniq.
