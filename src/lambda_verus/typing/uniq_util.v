From lrust.typing Require Export type.
From lrust.lifetime Require Import lifetime_full.
From lrust.util Require Export proph_bor.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅: syn_type.

(** * Encoding of depths

  The prophecy variable of a unique borrow ranges over the borrowed value
  together with its depth indices [(d, g)], encoded as positives. *)

Definition enc_depth (d: nat) : positive := Pos.of_succ_nat d.
Definition dec_depth (p: positive) : nat := Nat.pred (Pos.to_nat p).

Lemma dec_enc_depth d : dec_depth (enc_depth d) = d.
Proof. rewrite /dec_depth /enc_depth SuccNat2Pos.id_succ. done. Qed.

Lemma enc_dec_depth p : enc_depth (dec_depth p) = p.
Proof.
  rewrite /dec_depth /enc_depth. have ?:= Pos2Nat.is_pos p.
  apply Pos2Nat.inj. rewrite SuccNat2Pos.id_succ. lia.
Qed.

Global Instance enc_depth_inj : Inj (=) (=) enc_depth.
Proof. intros d d' Heq. by rewrite -(dec_enc_depth d) -(dec_enc_depth d') Heq. Qed.

(** The value of the prophecy variable of a unique borrow: the borrowed value, its
    depths, and the ghost name of the state of the borrow's pinned body (see
    [cpd_body]). *)
Definition uniq_cell {𝔄} (x: ~~𝔄) (d g: nat) (γ: gname) : ~~ (uniq_cellₛ 𝔄) :=
  (x, (enc_depth d, (enc_depth g, γ))).

Definition cell_d {𝔄} (c: ~~ (uniq_cellₛ 𝔄)) : nat := dec_depth c.2.1.
Definition cell_g {𝔄} (c: ~~ (uniq_cellₛ 𝔄)) : nat := dec_depth c.2.2.1.
Definition cell_γ {𝔄} (c: ~~ (uniq_cellₛ 𝔄)) : gname := c.2.2.2.

Lemma uniq_cell_inj {𝔄} (x x': ~~𝔄) d g γ d' g' γ' :
  uniq_cell x d g γ = uniq_cell x' d' g' γ' → x = x' ∧ d = d' ∧ g = g' ∧ γ = γ'.
Proof.
  intros [= -> E1 E2 ->]. split; [done|]. split; [by eapply enc_depth_inj|].
  split; [by eapply enc_depth_inj|done].
Qed.

Lemma uniq_cell_surj {𝔄} (c: ~~ (uniq_cellₛ 𝔄)) :
  c = uniq_cell c.1 (cell_d c) (cell_g c) (cell_γ c).
Proof. destruct c as [x [p1 [p2 γ]]]. by rewrite /uniq_cell /cell_d /cell_g /cell_γ /= !enc_dec_depth. Qed.

Lemma cell_d_uniq_cell {𝔄} (x: ~~𝔄) d g γ : cell_d (uniq_cell x d g γ) = d.
Proof. by rewrite /cell_d /= dec_enc_depth. Qed.
Lemma cell_g_uniq_cell {𝔄} (x: ~~𝔄) d g γ : cell_g (uniq_cell x d g γ) = g.
Proof. by rewrite /cell_g /= dec_enc_depth. Qed.
Lemma cell_γ_uniq_cell {𝔄} (x: ~~𝔄) d g γ : cell_γ (uniq_cell x d g γ) = γ.
Proof. done. Qed.

Lemma vπ_uniq_cell {𝔄} (x: ~~𝔄) d g γ π :
  @vπ (uniq_cellₛ 𝔄) (uniq_cell x d g γ) π = (vπ x π, (enc_depth d, (enc_depth g, γ))).
Proof. done. Qed.

Lemma uniq_cell_dep {𝔄} (x: ~~𝔄) d g γ ζl :
  vπ x ./ ζl → @vπ (uniq_cellₛ 𝔄) (uniq_cell x d g γ) ./ ζl.
Proof. apply (proph_dep_constr (λ a, (a, (enc_depth d, (enc_depth g, γ))))). Qed.

Lemma uniq_cell_dep_rev {𝔄} (c: ~~ (uniq_cellₛ 𝔄)) ζl :
  (λ π, (@vπ 𝔄 c.1 π)) ./ ζl → @vπ (uniq_cellₛ 𝔄) c ./ ζl.
Proof. destruct c as [x [p1 [p2 γ]]]. apply (proph_dep_constr (λ a, (a, (p1, (p2, γ))))). Qed.

Lemma uniq_prvar_app_irrel {𝔄} (x x': ~~𝔄) ξi (π: proph_asn) :
  (π (uniq_prvar x ξi)).1 = (π (uniq_prvar x' ξi)).1.
Proof.
  rewrite /uniq_prvar /uniq_cell_tyi.
  by rewrite (proof_irrel (@to_inh_syn_type (uniq_cellₛ 𝔄) (vπ x inhabitant, (1%positive, (1%positive, 1%positive))))
                         (@to_inh_syn_type (uniq_cellₛ 𝔄) (vπ x' inhabitant, (1%positive, (1%positive, 1%positive))))).
Qed.

Section uniq_util.
  Context `{!typeG Σ}.

  (** * Unique borrows

    A unique borrow [&uniq{κ} ty] at value [(l, x, ξi, d, g, idx)] is a generalized
    prophetic borrow ([proph_idx_bor_gen]) of the prophecy variable [ξ :=
    uniq_prvar x ξi] at lifetime [κ], with a _pinned, state-indexed_ body
    ([cpd_body]): the body is the interpretation of a fixed core ([OfTy ty], the
    leaf node [leaf_node κp ty]) at a state [(p, r)] (a blocking pattern and a
    refinement, see [lstate.v]) held in a Leibniz ghost variable [γ], whose name is
    stored in the value of [ξ] ([uniq_cell]); the controller prophecy of [ξ] is the
    denotation of [r]. The owner of the borrow
    holds the other half of the ghost variable, at the trivial state
    [lstate_triv x] ([PatLeaf], [PlaceIn x]); at that state, the body is exactly the
    (guarded, lazy) payload [uniq_payload] ([uniq_gbody_triv_open],
    [uniq_gbody_triv_close]), so that the operations on unique borrows are as for a
    plain prophetic borrow of the payload. Other states arise when the place behind
    the borrow is unfolded or blocked (see [ltype.v]; a leaf sees a state with a
    structured refinement, written by an unfolded place, as blocked at [κp]); the borrow can then be
    switched to another core (with a fresh ghost variable), and the old body is
    given a state that gives back the new contents once they are unblocked
    ([PatBlocked], with a [PlaceProph] refinement).

    The ghost name [γ] and the lifetime [κp] of the membership condition [pat_ok]
    are existentially quantified in the ownership of the borrow; [κp] is the
    lifetime of the borrow when it was created (or switched), [κ ⊑ κp] (the borrow
    may have been shortened, e.g. by subtyping, which does not change the body).

    When [κ] has ended, the lender gets the controller and the body at some state
    ([uniq_lender]); with a guard for the lifetime of the type it can run the lazy
    update of the body, unblock it ([pat_ok]: all blocked lifetimes are included in
    [κp]) and compose the controller's equalizer with the refinement
    ([uniq_lender_settle], using [proph_ctrl_eqz_compose]).

    ** The payload

    The payload is lazy: the time receipt, the ownership predicate of the contents
    and the points-to are under a guarded update ([guarded_upd]) with the mask
    [lazyE], for the lifetime [ty_lft ty] of the referent type. The update can fire
    inheritances of the lifetime logic ([[†κ] ={↑Nllft}=∗ …]) and open borrows, which
    cannot be done in the closing view shift of a borrow (whose mask is
    [↑NllftUsr ∪ ↑NllftUsr2]). Since [↑NllftG ⊆ ↑Nllft ⊆ lazyE], it can never run
    while a guard is open.

    Running the update needs a guard for [ty_lft ty]. An opener of the borrow (at
    [κ]) has a guard for [κ], and [κ ⊑ ty_lft ty] from the ownership predicate of
    [&uniq]; it opens the borrow with half of the guard and runs the update with the
    other half, paying for the later in front of the contents with a later credit or
    a program step. A lender gets a guard when it unblocks: the blocked entries of
    the type context hold a pending ownership ([tctx_pending]) that is settled with
    a guard for the lifetime of the type. *)
  Definition lazyE : coPset := ↑Nllft ∪ ↑prophN ∪ ↑uniqN.

  Lemma lazyE_NllftUsr : ↑NllftUsr ∪ ↑NllftUsr2 ⊆ lazyE.
  Proof. rewrite /lazyE /NllftUsr /NllftUsr2. solve_ndisj. Qed.

  Lemma lazyE_NllftG : ↑NllftG ⊆ lazyE.
  Proof. rewrite /lazyE /NllftG. solve_ndisj. Qed.

  (** ** Place refinements *)

  (** The relation between a place refinement and a value. *)
  Definition place_rfn_rel {𝔄} (r: place_rfn 𝔄) (x: ~~𝔄) : iProp Σ :=
    match r with
    | PlaceIn x' => ⌜x = x'⌝
    | PlaceProph _ f => ▷ (f :== vπ x)
    end.

  (** The relation gives an equalizer of the denotation (under a later). *)
  Lemma place_rfn_rel_eqz {𝔄} (r: place_rfn 𝔄) x :
    place_rfn_rel r x -∗ ▷ (place_rfn_den r :== vπ x).
  Proof.
    destruct r as [x'|x₀ f]; simpl; [|by iIntros "$"].
    iIntros (->) "!>". iApply proph_eqz_refl.
  Qed.

  (** ** The membership condition

    The pinned body of a borrow with pattern lifetime [κ] only admits patterns whose
    blocked lifetimes are included in [κ], so that they end when [κ] ends. The
    inclusion is semantic: the unblocking always happens in a lazy update (mask
    [lazyE ⊇ ↑NllftG], see [pat_ok_dead]), and a semantic inclusion survives
    shortening the lifetime of the borrow. *)
  Definition pat_ok (κ: lft) (p: lpat) : iProp Σ := [∗ list] α ∈ pat_blk_lfts p, α ⊑ κ.
  Global Instance pat_ok_persistent κ p : Persistent (pat_ok κ p) := _.

  Lemma pat_ok_leaf κ : ⊢ pat_ok κ PatLeaf.
  Proof. by rewrite /pat_ok /=. Qed.

  Lemma pat_ok_blocked κ α : α ⊑ κ -∗ pat_ok κ (PatBlocked α).
  Proof. rewrite /pat_ok /=. iIntros "$". Qed.

  Lemma pat_ok_blocked_inv κ α : pat_ok κ (PatBlocked α) -∗ α ⊑ κ.
  Proof. rewrite /pat_ok /=. iIntros "[$ _]". Qed.

  Lemma pat_ok_mono κ κ' p : κ ⊑ κ' -∗ pat_ok κ p -∗ pat_ok κ' p.
  Proof.
    iIntros "#Incl #Ok". rewrite /pat_ok. iApply (big_sepL_impl with "Ok").
    iIntros "!>" (???) "#H". iApply (llftl_incl_trans with "H Incl").
  Qed.

  Lemma pat_ok_dead κ p E :
    ↑NllftG ⊆ E →
    llft_ctx -∗ pat_ok κ p -∗ [†κ] ={E}=∗ [∗ list] α ∈ pat_blk_lfts p, [†α].
  Proof.
    iIntros (?) "#LFT #Ok #†κ". rewrite /pat_ok.
    iInduction (pat_blk_lfts p) as [|α αl] "IH"; simpl; [done|].
    iDestruct "Ok" as "[Hα Ok]". iMod ("IH" with "Ok") as "$".
    iApply (llftl_incl_dead_implies_dead with "LFT Hα †κ"). done.
  Qed.

  Definition cpd_body {𝔄} (κ α: lft)
      (node: lpat → prfn 𝔄 → nat → nat → thread_id → cloc → iProp Σ)
      (tid: thread_id) (l: cloc)
      (c: ~~ (uniq_cellₛ 𝔄)) (wπ: proph (uniq_cellₛ 𝔄)) : iProp Σ :=
    ∃ (p: lpat) (r: prfn 𝔄), pat_ok κ p ∗ ⌜∀ π, (wπ π).1 = prfn_den r π⌝ ∗
      ghost_var (cell_γ c) (1/2) (lstate p r) ∗
      guarded_upd lazyE @[α] (⧖(S (cell_d c) `max` cell_g c) ∗
        node p r (cell_d c) (cell_g c) tid l).

  Lemma cpd_body_cell {𝔄} κ α (node: lpat → prfn 𝔄 → nat → nat → thread_id → cloc → iProp Σ)
      tid l (x: ~~𝔄) d g γ wπ :
    cpd_body κ α node tid l (uniq_cell x d g γ) wπ ⊣⊢
    ∃ p r, pat_ok κ p ∗ ⌜∀ π, (wπ π).1 = prfn_den r π⌝ ∗
      ghost_var γ (1/2) (lstate p r) ∗
      guarded_upd lazyE @[α] (⧖(S d `max` g) ∗ node p r d g tid l).
  Proof. by rewrite /cpd_body cell_d_uniq_cell cell_g_uniq_cell cell_γ_uniq_cell. Qed.

  Definition uniq_tokγ {𝔄} (x: ~~ 𝔄) (ξi: positive) (d g: nat) (idx: Idx) (γ: gname)
      : iProp Σ :=
    ghost_var γ (1/2) (lstate_triv x) ∗ proph_bor_tok (uniq_prvar x ξi) (uniq_cell x d g γ) idx.

  Definition uniq_pat_lft (κ κp: lft) : iProp Σ := κ ⊑ κp.
  Global Instance uniq_pat_lft_persistent κ κp : Persistent (uniq_pat_lft κ κp) := _.

  Global Instance uniq_tokγ_timeless {𝔄} (x: ~~ 𝔄) ξi d g idx γ :
    Timeless (uniq_tokγ x ξi d g idx γ).
  Proof. apply _. Qed.

  Definition basically_dead (κ: lft) : iProp Σ := ∃ κ' , κ ⊑ κ' ∗ [†κ'].

  Definition basically_dead_incl κ κ' :
    κ' ⊑ κ -∗ basically_dead κ -∗ basically_dead κ'.
  Proof.
    iIntros "#Incl bd". iDestruct "bd" as (κ'') "[#Incl2 #Dead]".
    iExists κ''. iFrame "Dead". iApply (guards_transitive with "Incl Incl2").
  Qed.

  Lemma basically_dead_alive_false κ (G: iProp Σ) E :
    ↑NllftG ⊆ E →
    (G &&{↑NllftG}&&> @[κ]) -∗ basically_dead κ -∗ G ={E}=∗ False.
  Proof.
    iIntros (?) "#Gk Dead G". iDestruct "Dead" as (κ') "[#Incl' #Dead']".
    iDestruct (guards_transitive with "Gk Incl'") as "G2".
    leaf_open "G2" with "G" as "[Alive _]"; [done|].
    iExFalso. iApply (llftl_not_own_end with "Alive Dead'").
  Qed.

  (** ** Resolution *)

End uniq_util.
Global Typeclasses Opaque uniq_pat_lft.

(** The components of the value of a unique borrow. *)
Section uniq_bor_val_parts.
  Definition uniq_bor_loc {𝔄} (m: ~~ (uniq_borₛ 𝔄)) : cloc :=
      match m with (l, x0, ξi, d', g', idx) => l end.
  
  Definition uniq_bor_current {𝔄} (m: ~~ (uniq_borₛ 𝔄)) : ~~ 𝔄 :=
      match m with (l, x0, ξi, d', g', idx) => x0 end.
      
  Definition uniq_bor_future {𝔄} (m: ~~ (uniq_borₛ 𝔄)) (π : proph_asn) : 𝔄 := (vπ m π).2.
      
  Definition uniq_bor_ξi {𝔄} (m: ~~ (uniq_borₛ 𝔄)) : positive :=
      match m with (l, x0, ξi, d', g', idx) => ξi end.
End uniq_bor_val_parts.
