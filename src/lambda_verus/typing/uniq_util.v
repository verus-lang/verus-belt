From lrust.typing Require Export type.
From lrust.lifetime Require Import lifetime_full guarded_bor.
From lrust.util Require Export proph_bor.
From guarding Require Import guard tactics.
From lrust.typing Require Import own bytes_layout.
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

    The payload is lazy: the time receipt and the ownership predicate of the contents
    are under a guarded update ([guarded_upd]) with the mask [lazyE], for the lifetime
    [ty_lft ty] of the referent type. The bytes of the contents are outside the guarded
    update (option 3 of the phase-2b plan of [design_docs/guarded-mutable-borrows-plan.md]):
    in every state of the body, they can be forced with the mask [lazyB] and dead tokens
    only ([leaf_contents_unblock]), without a guard for the lifetime of the type. The update can fire
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
    a guard for the lifetime of the type. The masks [lazyE] and [lazyB] are defined in
    [gcont.v]. *)

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
  Definition uniq_bor_loc {𝔄} (m: ~~ (uniq_borₛ 𝔄)) : loc :=
      match m with (l, x0, ξi, d', g', idx) => l end.
  
  Definition uniq_bor_current {𝔄} (m: ~~ (uniq_borₛ 𝔄)) : ~~ 𝔄 :=
      match m with (l, x0, ξi, d', g', idx) => x0 end.
      
  Definition uniq_bor_future {𝔄} (m: ~~ (uniq_borₛ 𝔄)) (π : proph_asn) : 𝔄 := (vπ m π).2.
      
  Definition uniq_bor_ξi {𝔄} (m: ~~ (uniq_borₛ 𝔄)) : positive :=
      match m with (l, x0, ξi, d', g', idx) => ξi end.
End uniq_bor_val_parts.

(** * Unique borrows of bytes (stage 4 of the MiniRust memory model)

The leaves own bytes: the points-to of a leaf [OfTy ty] at [l] with value [x] is
[cbytes ty x l] (bytes at [l] that represent [x], [bytes_own]: fancy bytes, which may
contain cells). The generic parts above (the encoding of depths, [uniq_cell], [lazyE],
[place_rfn_rel], [pat_ok], [cpd_body], [uniq_tokγ], [uniq_pat_lft], [basically_dead]) are
shared with the legacy word-level version (deleted in stage 5). *)

Section uniq_util_bytes.
  Context `{!typeG Σ}.

  (** The bytes at the location [l] represent [x]. *)
  Definition cbytes {𝔄} (ty: type 𝔄) (x: ~~𝔄) (l: loc) : iProp Σ := bytes_own ty l x.

  Global Instance cbytes_timeless {𝔄} (ty: type 𝔄) x l : Timeless (cbytes ty x l).
  Proof. apply _. Qed.

  Lemma cbytes_same {𝔄} (ty ty': type 𝔄) x l : cbytes ty x l ⊣⊢ cbytes ty' x l.
  Proof. apply bytes_own_same. Qed.

  (** The reduction lemma: for a type without cells, the bytes of a leaf are plain. *)
  Lemma cbytes_nocell {𝔄} `{!NoCell 𝔄} (ty: type 𝔄) x l :
    cbytes ty x l ⊣⊢ ∃ bs, l ↦b bs ∗ ⌜ty_bytes ty x bs⌝.
  Proof. apply bytes_own_nocell. Qed.

  (** The bytes of a pair: those of its components, one after the other. *)
  Lemma cbytes_pair {𝔄 𝔅} (ty: type (𝔄 * 𝔅)) (ty1: type 𝔄) (ty2: type 𝔅) x1 x2 l :
    cbytes ty (x1, x2) l ⊣⊢
    cbytes ty1 x1 l ∗ cbytes ty2 x2 (l +ₗ ty_bsize ty1).
  Proof. rewrite /cbytes /=. apply bytes_own_pair. Qed.

  (** The bytes of a pointer. *)
  Definition ptr_cell (l: loc) (l': loc) : iProp Σ := ∃ bs, l ↦b bs ∗ ⌜ptr_bytes l' bs⌝.

  Global Instance ptr_cell_timeless l l' : Timeless (ptr_cell l l').
  Proof. apply _. Qed.

  Lemma cbytes_at_loc {𝔄} (ty: type (at_locₛ 𝔄)) x l : cbytes ty x l ⊣⊢ ptr_cell l x.1.
  Proof.
    rewrite /cbytes bytes_own_nocell /ptr_cell. by setoid_rewrite ty_bytes_syn;
      setoid_rewrite syn_bytes_at_loc.
  Qed.

  Lemma cbytes_uniq_bor {𝔄} (ty: type (uniq_borₛ 𝔄)) l' x ξi d g idx l :
    cbytes ty (l', x, ξi, d, g, idx) l ⊣⊢ ptr_cell l l'.
  Proof.
    rewrite /cbytes bytes_own_nocell /ptr_cell. by setoid_rewrite ty_bytes_syn;
      setoid_rewrite syn_bytes_uniq_bor.
  Qed.

  (** ** Fancy bytes at a fancy value

    In the bodies of unique borrows, the bytes of the leaves are kept outside the guarded
    update of their ghost ownership (option 3 of the phase-2b plan of
    [design_docs/guarded-mutable-borrows-plan.md]), quantified over the fancy value that
    they represent: [fbytes ty l fv] are the bytes at [l] of some value of [ty] whose fancy
    value is [fv]. The ghost ownership is then that of a value of fancy value [fv]
    ([ofty_gho]). Since the bytes only depend on the fancy value ([cbytes_fval]), the two
    parts can be put back together ([ofty_split]). The bytes can be forced with the mask
    [lazyB] and dead tokens, without a guard for the lifetime of the type
    ([leaf_contents_unblock]). *)
  Definition fbytes {𝔄} (ty: type 𝔄) (l: loc) (fv: FValue) : iProp Σ :=
    ∃ x, ⌜ty.(ty_fval) x = Some fv⌝ ∗ cbytes ty x l.

  Global Instance fbytes_timeless {𝔄} (ty: type 𝔄) l fv : Timeless (fbytes ty l fv).
  Proof. apply _. Qed.

  Lemma cbytes_fval {𝔄} (ty: type 𝔄) x x' l :
    ty.(ty_fval) x = ty.(ty_fval) x' → cbytes ty x l ⊣⊢ cbytes ty x' l.
  Proof. intros Hx. apply bytes_own_iff=> R fbs. by rewrite /ty_fbytes Hx. Qed.

  Lemma cbytes_fval_some {𝔄} (ty: type 𝔄) x l :
    cbytes ty x l -∗ ⌜is_Some (ty.(ty_fval) x)⌝.
  Proof.
    rewrite /cbytes bytes_own_brepr. iIntros "(%fbs & %fv & _ & %Hc & _)". iPureIntro.
    destruct Hc as [_ Hfv]. by eexists.
  Qed.

  Lemma cbytes_fbytes {𝔄} (ty: type 𝔄) x l :
    cbytes ty x l ⊣⊢ ∃ fv, ⌜ty.(ty_fval) x = Some fv⌝ ∗ fbytes ty l fv.
  Proof.
    iSplit.
    - iIntros "B". iDestruct (cbytes_fval_some with "B") as %[fv Hfv].
      iExists fv. iSplit; [done|]. iExists x. by iFrame.
    - iIntros "(%fv & %Hfv & %x0 & %Hx0 & B)". rewrite (cbytes_fval ty x x0) //.
      by rewrite Hfv Hx0.
  Qed.

  Lemma fbytes_cbytes {𝔄} (ty: type 𝔄) x l fv :
    ty.(ty_fval) x = Some fv → fbytes ty l fv -∗ cbytes ty x l.
  Proof. iIntros (Hx) "B". rewrite cbytes_fbytes. iExists fv. by iFrame. Qed.

  Lemma fbytes_same {𝔄} (ty ty': type 𝔄) l fv : fbytes ty l fv ⊣⊢ fbytes ty' l fv.
  Proof. rewrite /fbytes. setoid_rewrite (ty_fval_same ty ty'). by setoid_rewrite (cbytes_same ty ty'). Qed.

  Lemma fbytes_loc {𝔄} (ty: type 𝔄) l l' fv :
    (∀ x, cbytes ty x l ⊣⊢ cbytes ty x l') → fbytes ty l fv ⊣⊢ fbytes ty l' fv.
  Proof. intros Hl. rewrite /fbytes. by setoid_rewrite Hl. Qed.

  (** The refinement [lr] admits the fancy value [fv]: a value [PlaceIn x] must have the
      fancy value [fv]. *)
  Definition lr_fval {𝔄} (ty: type 𝔄) (lr: place_rfn 𝔄) (fv: FValue) : Prop :=
    match lr with PlaceIn x => ty.(ty_fval) x = Some fv | PlaceProph _ _ => True end.

  Lemma lr_fval_rel {𝔄} (ty: type 𝔄) (lr: place_rfn 𝔄) x fv :
    ty.(ty_fval) x = Some fv → place_rfn_rel lr x -∗ ⌜lr_fval ty lr fv⌝.
  Proof. iIntros (Hx) "Rel". destruct lr; [by iDestruct "Rel" as %->|done]. Qed.

  (** ** Leaves in [Owned] mode

    A leaf [OfTy ty] contains a value: its points-to and its ownership predicate
    (under [m] laters, one per enclosing owned pointer). A blocked leaf holds an
    inheritance that gives back pending ownership of the leaf (to be settled with a
    guard for the lifetime of the type, as the blocked entries of the type context);
    the inheritance can be fired with the mask [lazyB] and gives back the bytes at once
    and the ghost ownership in a lazy update.

    The time receipt of the contents given back by a blocked leaf under [m] owned
    pointers is shifted by [m] ([⧖((m + S d') `max` g')]), so that the owned pointers
    above it can be folded back at depths increased by one per pointer (see
    [ltype_owned_unblock_fold] in [typing/ltype.v]). For [m = 0], this is the usual
    receipt [⧖(S d' `max` g')]. *)
  Definition ofty_owned {𝔄} (m: nat) (ty: type 𝔄) (x: ~~𝔄) (d g: nat)
      (tid: thread_id) (l: loc) : iProp Σ :=
    cbytes ty x l ∗ ▷^m ty.(ty_gho_own) x d g tid.

  (** The ghost part of a leaf of fancy value [fv]. *)
  Definition ofty_gho {𝔄} (m: nat) (ty: type 𝔄) (lr: place_rfn 𝔄) (fv: FValue) (d g: nat)
      (tid: thread_id) : iProp Σ :=
    ∃ x, ⌜ty.(ty_fval) x = Some fv⌝ ∗ place_rfn_rel lr x ∗ ▷^m ty.(ty_gho_own) x d g tid.

  Lemma ofty_split {𝔄} m (ty: type 𝔄) lr d g tid l :
    (∃ x, place_rfn_rel lr x ∗ ofty_owned m ty x d g tid l) ⊣⊢
    ∃ fv, (fbytes ty l fv ∗ ⌜lr_fval ty lr fv⌝) ∗ ofty_gho m ty lr fv d g tid.
  Proof.
    iSplit.
    - iIntros "(%x & Rel & B & Gho)". iDestruct (cbytes_fval_some with "B") as %[fv Hfv].
      iDestruct (lr_fval_rel with "Rel") as %Hlr; [done|].
      iExists fv. iSplitL "B"; [iSplit; [iExists x; by iFrame|done]|].
      iExists x. by iFrame.
    - iIntros "(%fv & [B _] & %x & %Hx & Rel & Gho)". iExists x. iFrame "Rel Gho".
      by iApply (fbytes_cbytes with "B").
  Qed.

  Definition blocked_owned {𝔄} (m: nat) (ty: type 𝔄) (α: lft) (lr: place_rfn 𝔄)
      (tid: thread_id) (l: loc) : iProp Σ :=
    [†α] ={lazyB}=∗ ∃ fv, fbytes ty l fv ∗ guarded_upd lazyE @[ty_lft ty]
      (∃ d' g', ⧖((m + S d') `max` g') ∗ ofty_gho m ty lr fv d' g' tid).

  (** Firing the inheritance of a blocked leaf, with the bytes in the lazy update. *)
  Lemma blocked_owned_fire {𝔄} m (ty: type 𝔄) α lr tid l :
    blocked_owned m ty α lr tid l -∗ [†α] ={lazyB}=∗ guarded_upd lazyE @[ty_lft ty]
      (∃ x d' g', place_rfn_rel lr x ∗ ⧖((m + S d') `max` g') ∗ ofty_owned m ty x d' g' tid l).
  Proof.
    iIntros "Inh Dead". iMod ("Inh" with "Dead") as (fv) "[B Upd]". iModIntro.
    iApply (guarded_upd_mono with "[B] Upd").
    iIntros "(%d' & %g' & ⧖ & %x & %Hx & Rel & Gho) !>". iExists x, d', g'. iFrame "Rel ⧖ Gho".
    by iApply (fbytes_cbytes with "B").
  Qed.

  (** A blocked leaf from contents that are already unblocked. *)
  Lemma blocked_owned_intro {𝔄} m (ty: type 𝔄) α lr tid l :
    (∃ fv, fbytes ty l fv ∗ guarded_upd lazyE @[ty_lft ty]
      (∃ d' g', ⧖((m + S d') `max` g') ∗ ofty_gho m ty lr fv d' g' tid)) -∗
    blocked_owned m ty α lr tid l.
  Proof. iIntros "H _". by iModIntro. Qed.

  (** [c] selects the core interpretation, in which blocked leaves are unblocked. *)
  Definition leaf_owned {𝔄} (c: bool) (m: nat) (ty: type 𝔄) (p: lpat) (r: prfn 𝔄)
      (d g: nat) (tid: thread_id) (l: loc) : iProp Σ :=
    match r with
    | inr _ => False
    | inl lr =>
        match p with
        | PatBlocked α =>
            if c then ∃ x, place_rfn_rel lr x ∗ ofty_owned m ty x d g tid l
            else blocked_owned m ty α lr tid l
        | _ => ∃ x, place_rfn_rel lr x ∗ ofty_owned m ty x d g tid l
        end
    end%I.

  Lemma leaf_owned_triv {𝔄} m (ty: type 𝔄) x d g tid l :
    leaf_owned false m ty PatLeaf (inl (PlaceIn x)) d g tid l ⊣⊢ ofty_owned m ty x d g tid l.
  Proof.
    rewrite /leaf_owned /=. iSplit; [iIntros "(%y & -> & $)"|iIntros "H"; iExists x; by iFrame].
  Qed.

  (** The bytes and the ghost part of a (non-core) leaf: a blocked leaf is all bytes (its
      inheritance). *)
  Definition leaf_owned_b {𝔄} (m: nat) (ty: type 𝔄) (p: lpat) (lr: place_rfn 𝔄) (fv: FValue)
      (tid: thread_id) (l: loc) : iProp Σ :=
    match p with
    | PatBlocked α => blocked_owned m ty α lr tid l
    | _ => fbytes ty l fv ∗ ⌜lr_fval ty lr fv⌝
    end%I.

  Definition leaf_owned_g {𝔄} (m: nat) (ty: type 𝔄) (p: lpat) (lr: place_rfn 𝔄) (fv: FValue)
      (d g: nat) (tid: thread_id) : iProp Σ :=
    match p with
    | PatBlocked α => True
    | _ => ofty_gho m ty lr fv d g tid
    end%I.

  Lemma leaf_owned_bg {𝔄} m (ty: type 𝔄) p lr d g tid l :
    leaf_owned false m ty p (inl lr) d g tid l ⊣⊢
    ∃ fv, leaf_owned_b m ty p lr fv tid l ∗ leaf_owned_g m ty p lr fv d g tid.
  Proof.
    destruct p; rewrite /leaf_owned /leaf_owned_b /leaf_owned_g /=; try apply ofty_split.
    iSplit; [iIntros "$"; by iExists inhabitant|iIntros "(%fv & $ & _)"].
  Qed.

  (** Unblocking a leaf, inside a lazy update: the blocked lifetime is included in
      [κ], which has ended. *)
  Lemma leaf_owned_unblock {𝔄} κ m (ty: type 𝔄) p lr d g tid l G :
    Timeless G →
    llft_ctx -∗ (G &&{↑NllftG}&&> @[ty_lft ty]) -∗ pat_ok κ p -∗ [†κ] -∗ G -∗
    ⧖((m + S d) `max` g) -∗ leaf_owned false m ty p (inl lr) d g tid l ={lazyE}=∗
      G ∗ ∃ x d' g', place_rfn_rel lr x ∗ ⧖((m + S d') `max` g') ∗
        ofty_owned m ty x d' g' tid l.
  Proof.
    iIntros (?) "#LFT #Gty #Ok #†κ G #⧖ L".
    destruct p; try (iModIntro; iFrame "G"; iDestruct "L" as (x) "[Rel O]";
      iExists x, d, g; by iFrame "∗#").
    iMod (pat_ok_dead with "LFT Ok †κ") as "[Dead _]"; [apply lazyE_NllftG|].
    iDestruct (blocked_owned_fire with "L Dead") as "Upd".
    iMod (fupd_mask_mono with "Upd") as "Upd"; [apply lazyB_lazyE|].
    by iApply (guarded_upd_run with "Gty G Upd").
  Qed.

  (** The leaf node of the body of a borrow whose membership condition is at [κp]: a
      leaf at a state with a structured refinement (written by an unfolded compound
      place, see [typing/ltype.v]) is blocked at [κp]. *)
  Definition leaf_node {𝔄} (κp: lft) (ty: type 𝔄) (p: lpat) (r: prfn 𝔄)
      (d g: nat) (tid: thread_id) (l: loc) : iProp Σ :=
    leaf_owned false 0 ty (norm_pat κp p r) (inl (prfn_place r)) d g tid l.

  Lemma leaf_node_inl {𝔄} κp (ty: type 𝔄) p lr d g tid l :
    leaf_node κp ty p (inl lr) d g tid l = leaf_owned false 0 ty p (inl lr) d g tid l.
  Proof. done. Qed.

  Lemma pat_ok_norm κ {𝔄} p (r: prfn 𝔄) : pat_ok κ p -∗ pat_ok κ (norm_pat κ p r).
  Proof.
    iIntros "Ok". destruct r; [done|]. iApply pat_ok_blocked. iApply guards_refl.
  Qed.

  Lemma leaf_node_unblock {𝔄} κp (ty: type 𝔄) p r d g tid l G :
    Timeless G →
    llft_ctx -∗ (G &&{↑NllftG}&&> @[ty_lft ty]) -∗ pat_ok κp p -∗ [†κp] -∗ G -∗
    ⧖(S d `max` g) -∗ leaf_node κp ty p r d g tid l ={lazyE}=∗
      G ∗ ∃ x d' g', place_rfn_rel (prfn_place r) x ∗ ⧖(S d' `max` g') ∗
        ofty_owned 0 ty x d' g' tid l.
  Proof.
    iIntros (?) "#LFT #Gty #Ok #†κ G #⧖ L". iDestruct (pat_ok_norm _ _ r with "Ok") as "Ok'".
    iApply (leaf_owned_unblock _ 0 with "LFT Gty Ok' †κ G ⧖ L").
  Qed.

  (** ** The contents of the leaf body

    The contents of the body of a unique borrow of [ty] at a state [(p, r)]: the bytes
    part of the leaf node and, unless the leaf is blocked, its ghost part with the time
    receipt in a lazy update for the lifetime of the type. (A blocked leaf is its
    inheritance, which gives back both parts.) *)
  Definition leaf_owned_lz {𝔄} (ty: type 𝔄) (p: lpat) (lr: place_rfn 𝔄) (fv: FValue)
      (d g: nat) (tid: thread_id) : iProp Σ :=
    match p with
    | PatBlocked _ => True
    | _ => guarded_upd lazyE @[ty_lft ty] (⧖(S d `max` g) ∗ ofty_gho 0 ty lr fv d g tid)
    end%I.

  Definition leaf_contents {𝔄} (κp: lft) (ty: type 𝔄) (p: lpat) (r: prfn 𝔄) (d g: nat)
      (tid: thread_id) (l: loc) : iProp Σ :=
    ∃ fv, leaf_owned_b 0 ty (norm_pat κp p r) (prfn_place r) fv tid l ∗
      leaf_owned_lz ty (norm_pat κp p r) (prfn_place r) fv d g tid.

  (** The time receipt of the contents, which only an unblocked leaf holds. *)
  Definition leaf_rcpt (p: lpat) (d g: nat) : iProp Σ :=
    match p with PatBlocked _ => True | _ => ⧖(S d `max` g) end%I.

  (** The contents as a lazy update of the leaf node. *)
  Lemma leaf_contents_guarded {𝔄} κp (ty: type 𝔄) p r d g tid l :
    leaf_contents κp ty p r d g tid l -∗
    guarded_upd lazyE @[ty_lft ty] (leaf_rcpt (norm_pat κp p r) d g ∗ leaf_node κp ty p r d g tid l).
  Proof.
    iIntros "(%fv & B & Upd)". rewrite /leaf_node leaf_owned_bg /leaf_owned_lz /leaf_rcpt.
    destruct (norm_pat κp p r) eqn:Hn;
      try (iApply (guarded_upd_mono with "[B] Upd"); iIntros "[$ G] !>"; iExists fv; by iFrame).
    iApply guarded_upd_intro. iModIntro. iSplit; [done|]. iExists fv. by iFrame.
  Qed.

  (** Contents from an eager leaf node. *)
  Lemma leaf_contents_intro {𝔄} κp (ty: type 𝔄) p r d g tid l :
    ⧖(S d `max` g) -∗ leaf_node κp ty p r d g tid l -∗ leaf_contents κp ty p r d g tid l.
  Proof.
    iIntros "⧖ L". rewrite /leaf_node leaf_owned_bg. iDestruct "L" as (fv) "[B G]".
    iExists fv. iFrame "B". rewrite /leaf_owned_lz /leaf_owned_g.
    destruct (norm_pat κp p r); try done; iApply guarded_upd_intro; by iFrame.
  Qed.

  (** The contents at a state that only differs by the normalization of the pattern. *)
  Lemma leaf_contents_norm {𝔄} κp κp' (ty: type 𝔄) p r d g tid l :
    leaf_contents κp ty p r d g tid l ⊣⊢
    leaf_contents κp' ty (norm_pat κp p r) (inl (prfn_place r)) d g tid l.
  Proof. done. Qed.

  (** Forcing the bytes of the contents at a state with an unstructured refinement, with
      the mask [lazyB] and the death of a lifetime [κ] that includes all blocked
      lifetimes, without a guard for the lifetime of the type. The ghost part stays in a
      lazy update. *)
  Lemma leaf_contents_unblock_at {𝔄} κ κp (ty: type 𝔄) p lr d g tid l :
    llft_ctx -∗ pat_ok κ p -∗ [†κ] -∗ leaf_contents κp ty p (inl lr) d g tid l ={lazyB}=∗
      ∃ fv, fbytes ty l fv ∗ guarded_upd lazyE @[ty_lft ty]
        (∃ d' g', ⧖(S d' `max` g') ∗ ofty_gho 0 ty lr fv d' g' tid).
  Proof.
    iIntros "#LFT #Ok #†κ (%fv & B & Upd)". rewrite /leaf_owned_b /leaf_owned_lz /=.
    destruct p as [|α| | | | |];
      try (iModIntro; iDestruct "B" as "[B _]"; iExists fv; iFrame "B";
        iApply (guarded_upd_mono with "[] Upd"); iIntros "[⧖ G] !>";
        iExists d, g; by iFrame).
    iMod (pat_ok_dead with "LFT Ok †κ") as "[Dead _]"; [apply lazyB_NllftG|].
    by iMod ("B" with "Dead").
  Qed.

  (** Forcing the bytes of the contents, with the mask [lazyB] and the death of [κp]: all
      blocked lifetimes are included in [κp] ([pat_ok]). *)
  Lemma leaf_contents_unblock {𝔄} κp (ty: type 𝔄) p r d g tid l :
    llft_ctx -∗ pat_ok κp p -∗ [†κp] -∗ leaf_contents κp ty p r d g tid l ={lazyB}=∗
      ∃ fv, fbytes ty l fv ∗ guarded_upd lazyE @[ty_lft ty]
        (∃ d' g', ⧖(S d' `max` g') ∗ ofty_gho 0 ty (prfn_place r) fv d' g' tid).
  Proof.
    iIntros "#LFT #Ok #†κ C". iDestruct (pat_ok_norm _ _ r with "Ok") as "Ok'".
    rewrite (leaf_contents_norm κp κp). iApply (leaf_contents_unblock_at with "LFT Ok' †κ C").
  Qed.

  (** ** The payload

    The bytes of the contents, and their ownership predicate with the time receipt in a
    lazy update ([guarded_upd], with the mask [lazyE], for the lifetime [ty_lft ty] of
    the referent type). *)
  Definition uniq_payload {𝔄} (ty: type 𝔄) (tid: thread_id) (l: loc)
      (x: ~~𝔄) (d g: nat) : iProp Σ :=
    cbytes ty x l ∗ guarded_upd lazyE @[ty_lft ty] (⧖(S d `max` g) ∗ ty.(ty_gho_own) x d g tid).
  Lemma uniq_payload_cell {𝔄} (ty: type 𝔄) tid l x d g :
    uniq_payload ty tid l x d g ⊣⊢
      cbytes ty x l ∗ guarded_upd lazyE @[ty_lft ty] (⧖(S d `max` g) ∗ ty.(ty_gho_own) x d g tid).
  Proof. done. Qed.

  (** A non-lazy payload. *)
  Lemma uniq_payload_intro {𝔄} (ty: type 𝔄) tid l x d g :
    ⧖(S d `max` g) -∗ ty.(ty_gho_own) x d g tid -∗ cbytes ty x l -∗
    uniq_payload ty tid l x d g.
  Proof.
    rewrite uniq_payload_cell. iIntros "⧖ Gho Pt". iFrame "Pt". iApply guarded_upd_intro.
    iModIntro. iFrame.
  Qed.

  Lemma uniq_payload_intro_later {𝔄} (ty: type 𝔄) tid l x d g :
    ▷ (⧖(S d `max` g) ∗ ty.(ty_gho_own) x d g tid ∗ cbytes ty x l) -∗
    ▷ uniq_payload ty tid l x d g.
  Proof. iIntros "(⧖ & Gho & Pt) !>". iApply (uniq_payload_intro with "⧖ Gho Pt"). Qed.

  (** Running the lazy update of a payload, given a guard for the lifetime of the
      type. *)
  Lemma uniq_payload_run {𝔄} (ty: type 𝔄) tid l x d g E G :
    Timeless G → lazyE ⊆ E →
    (G &&{↑NllftG}&&> @[ty_lft ty]) -∗ G -∗ uniq_payload ty tid l x d g ={E}=∗
      G ∗ ⧖(S d `max` g) ∗ ty.(ty_gho_own) x d g tid ∗ cbytes ty x l.
  Proof.
    iIntros (??) "Gk G [Pt P]".
    iMod (guarded_upd_run with "Gk G P") as "($ & $ & $)"; done.
  Qed.

  (** Running the lazy update of a payload that is under a later, with a later
      credit. *)
  Lemma uniq_payload_force {𝔄} (ty: type 𝔄) tid l x d g E G :
    Timeless G → lazyE ⊆ E →
    (G &&{↑NllftG}&&> @[ty_lft ty]) -∗ G -∗
    £1 -∗ ▷ uniq_payload ty tid l x d g ={E}=∗
      G ∗ ⧖(S d `max` g) ∗ ty.(ty_gho_own) x d g tid ∗ cbytes ty x l.
  Proof.
    iIntros (??) "Gk G £ P".
    iMod (lc_fupd_elim_later with "£ P") as "P".
    by iApply (uniq_payload_run with "Gk G P").
  Qed.

  (** Mapping a payload: the bytes eagerly, the ghost part lazily. *)
  Lemma uniq_payload_map {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) tid tid' l l' x x' d g d' g' :
    ty_lft ty' ⊑ ty_lft ty -∗
    (⧖(S d `max` g) -∗ ⧖(S d' `max` g')) -∗
    (cbytes ty x l -∗ cbytes ty' x' l') -∗
    (ty.(ty_gho_own) x d g tid ={lazyE}=∗ ty'.(ty_gho_own) x' d' g' tid') -∗
    uniq_payload ty tid l x d g -∗ uniq_payload ty' tid' l' x' d' g'.
  Proof.
    rewrite !uniq_payload_cell. iIntros "#Incl T WB WG [Pt Upd]".
    iSplitL "WB Pt"; [by iApply "WB"|].
    iApply (guarded_upd_weaken with "Incl").
    iApply (guarded_upd_mono with "[T WG] Upd"). iIntros "(⧖ & Gho)".
    iDestruct ("T" with "⧖") as "$". by iApply "WG".
  Qed.

  (** ** Bodies of unique borrows

    The pinned body of a borrow with the leaf [OfTy ty] as core: the state [(p, r)] (in
    the ghost variable [cell_γ c]), and the contents of the leaf at that state. *)
  Definition uniq_gbody {𝔄} (κp: lft) (ty: type 𝔄) (tid: thread_id) (l: loc)
      (c: ~~ (uniq_cellₛ 𝔄)) (wπ: proph (uniq_cellₛ 𝔄)) : iProp Σ :=
    ∃ (p: lpat) (r: prfn 𝔄), pat_ok κp p ∗ ⌜∀ π, (wπ π).1 = prfn_den r π⌝ ∗
      ghost_var (cell_γ c) (1/2) (lstate p r) ∗
      leaf_contents κp ty p r (cell_d c) (cell_g c) tid l.

  Lemma uniq_gbody_cell {𝔄} κp (ty: type 𝔄) tid l (x: ~~𝔄) d g γ wπ :
    uniq_gbody κp ty tid l (uniq_cell x d g γ) wπ ⊣⊢
    ∃ p r, pat_ok κp p ∗ ⌜∀ π, (wπ π).1 = prfn_den r π⌝ ∗
      ghost_var γ (1/2) (lstate p r) ∗ leaf_contents κp ty p r d g tid l.
  Proof. by rewrite /uniq_gbody cell_d_uniq_cell cell_g_uniq_cell cell_γ_uniq_cell. Qed.

  (** The pinned body of a borrow whose core is a compound place, with the node [node]
      (see [typing/ltype.v]): the contents are both a lazy update of the node, and the
      contents of the leaf [OfTy ty] of the folded type [ty] (at a structured refinement,
      the leaf is blocked at [κp], see [leaf_node]). The second view is the one that the
      closing view shift of the borrow, which goes back to the body of [&uniq], uses
      ([cpd_body_leaf]): it needs no update. *)
  Definition cpd_contents {𝔄} (κp: lft) (ty: type 𝔄)
      (node: lpat → prfn 𝔄 → nat → nat → thread_id → loc → iProp Σ) (p: lpat) (r: prfn 𝔄)
      (d g: nat) (tid: thread_id) (l: loc) : iProp Σ :=
    guarded_upd lazyE @[ty_lft ty] (⧖(S d `max` g) ∗ node p r d g tid l) ∧
    leaf_contents κp ty p r d g tid l.

  Definition cpd_body {𝔄} (κp: lft) (ty: type 𝔄)
      (node: lpat → prfn 𝔄 → nat → nat → thread_id → loc → iProp Σ)
      (tid: thread_id) (l: loc)
      (c: ~~ (uniq_cellₛ 𝔄)) (wπ: proph (uniq_cellₛ 𝔄)) : iProp Σ :=
    ∃ (p: lpat) (r: prfn 𝔄), pat_ok κp p ∗ ⌜∀ π, (wπ π).1 = prfn_den r π⌝ ∗
      ghost_var (cell_γ c) (1/2) (lstate p r) ∗
      cpd_contents κp ty node p r (cell_d c) (cell_g c) tid l.

  Lemma cpd_body_cell {𝔄} κp (ty: type 𝔄) (node: lpat → prfn 𝔄 → nat → nat → thread_id → loc → iProp Σ)
      tid l (x: ~~𝔄) d g γ wπ :
    cpd_body κp ty node tid l (uniq_cell x d g γ) wπ ⊣⊢
    ∃ p r, pat_ok κp p ∗ ⌜∀ π, (wπ π).1 = prfn_den r π⌝ ∗
      ghost_var γ (1/2) (lstate p r) ∗ cpd_contents κp ty node p r d g tid l.
  Proof. by rewrite /cpd_body cell_d_uniq_cell cell_g_uniq_cell cell_γ_uniq_cell. Qed.

  Lemma cpd_body_leaf {𝔄} κp (ty: type 𝔄) node tid l c wπ :
    cpd_body κp ty node tid l c wπ -∗ uniq_gbody κp ty tid l c wπ.
  Proof.
    iIntros "(%p & %r & $ & $ & $ & C)". by iDestruct "C" as "[_ $]".
  Qed.

  Lemma cpd_contents_guarded {𝔄} κp (ty: type 𝔄) node p r d g tid l :
    cpd_contents κp ty node p r d g tid l -∗
    guarded_upd lazyE @[ty_lft ty] (⧖(S d `max` g) ∗ node p r d g tid l).
  Proof. by iIntros "[$ _]". Qed.

  (** Contents of a compound body from the payload of the folded type, at a structured
      refinement [r] of the same denotation, given a conversion of the payload into the
      node. *)
  Lemma cpd_contents_payload {𝔄} κp (ty: type 𝔄) node p (rs: prfn_struct 𝔄) x d g tid l :
    (∀ π, prfn_den (inr rs) π = vπ x π) →
    (∀ d g, ty.(ty_gho_own) x d g tid ∗ cbytes ty x l ⊢ |={lazyE}=> node p (inr rs) d g tid l) →
    uniq_payload ty tid l x d g -∗ cpd_contents κp ty node p (inr rs) d g tid l.
  Proof.
    iIntros (Hden Hconv) "[Pt Upd]". iSplit.
    - iApply (guarded_upd_mono with "[Pt] Upd"). iIntros "[$ Gho]".
      iApply Hconv. iFrame.
    - rewrite cbytes_fbytes. iDestruct "Pt" as (fv Hfv) "B". iExists inhabitant.
      rewrite /leaf_owned_b /leaf_owned_lz /=. iSplitL; [|done].
      iApply blocked_owned_intro. iExists fv. iFrame "B".
      iApply (guarded_upd_mono with "[] Upd"). iIntros "[⧖ Gho] !>". iExists d, g. iFrame "⧖".
      iExists x. iFrame "Gho". iSplit; [done|]. rewrite /place_rfn_rel /=. iNext.
      iApply (proph_eqz_eq with "[]"); [done| |iApply proph_eqz_refl]. fun_ext=> π /=.
      by rewrite Hden.
  Qed.

  (** The persistent part of a unique borrow. *)
  Definition uniq_persγ {𝔄} (ty: type 𝔄) (x: ~~ 𝔄) (ξi: positive) (idx: Idx)
      (κ κp: lft) (tid: thread_id) (l: loc) : iProp Σ :=
    proph_idx_bor_gen κ (uniq_prvar x ξi) idx (uniq_gbody κp ty tid l).

  Definition uniq_bodyγ {𝔄} (ty: type 𝔄) (x: ~~ 𝔄) (ξi: positive) (d g: nat) (idx: Idx)
      (κ κp: lft) (γ: gname) (tid: thread_id) (l: loc) : iProp Σ :=
    uniq_tokγ x ξi d g idx γ ∗ ⧗1 ∗ uniq_persγ ty x ξi idx κ κp tid l.

  Definition uniq_body {𝔄} (ty: type 𝔄) (x: ~~ 𝔄) (ξi: positive) (d: nat) (g: nat) (idx: Idx)
      (κ: lft) (tid: thread_id) (l: loc) : iProp Σ :=
    ∃ κp γ, uniq_pat_lft κ κp ∗ uniq_bodyγ ty x ξi d g idx κ κp γ tid l.

  Definition uniq_body_pers_component {𝔄} (ty: type 𝔄) (x: ~~ 𝔄) (ξi: positive) (d: nat) (g: nat) (idx: Idx)
      (κ: lft) (tid: thread_id) (l: loc) : iProp Σ :=
    ∃ κp, uniq_pat_lft κ κp ∗ uniq_persγ ty x ξi idx κ κp tid l.

  Global Instance uniq_persγ_persistent {𝔄} (ty: type 𝔄) x ξi idx κ κp tid l :
    Persistent (uniq_persγ ty x ξi idx κ κp tid l).
  Proof. rewrite /uniq_persγ. apply proph_idx_bor_gen_persistent. Qed.

  Global Instance uniq_body_pers_component_persistent {𝔄} (ty: type 𝔄) x ξi d g idx κ tid l :
    Persistent (uniq_body_pers_component ty x ξi d g idx κ tid l).
  Proof.
    rewrite /uniq_body_pers_component. apply bi.exist_persistent=> κp.
    apply bi.sep_persistent; [apply _|apply uniq_persγ_persistent].
  Qed.

  Lemma uniq_body_unfold {𝔄} (ty: type 𝔄) x ξi d g idx κ tid l :
    uniq_body ty x ξi d g idx κ tid l ⊣⊢
      ∃ κp γ, uniq_pat_lft κ κp ∗ uniq_tokγ x ξi d g idx γ ∗ ⧗1 ∗ uniq_persγ ty x ξi idx κ κp tid l.
  Proof. done. Qed.

  Lemma uniq_body_from_parts {𝔄} (ty: type 𝔄) x ξi d g idx κ κp γ tid l :
    uniq_pat_lft κ κp -∗ uniq_tokγ x ξi d g idx γ -∗ ⧗1 -∗ uniq_persγ ty x ξi idx κ κp tid l -∗
    uniq_body ty x ξi d g idx κ tid l.
  Proof. iIntros "? ? ? ?". iExists κp, γ. iFrame. Qed.

  Lemma uniq_body_pers_component_impl {𝔄} (ty: type 𝔄) (x: ~~ 𝔄) (ξi: positive) (d: nat) (g: nat) (idx: Idx) (κ: lft) (tid: thread_id) (l: loc)
    : uniq_body ty x ξi d g idx κ tid l -∗ uniq_body_pers_component ty x ξi d g idx κ tid l.
  Proof. iIntros "(%κp & %γ & ? & _ & _ & ?)". iExists κp. iFrame. Qed.

  (** ** Retargeting

    The prophecy variable of a unique borrow only depends on the current value
    through an inhabitedness proof; we can thus change it at will. *)

  Lemma uniq_bor_tok_retarget {𝔄} (x x': ~~ 𝔄) ξi c idx :
    proph_bor_tok (uniq_prvar x ξi) c idx ⊣⊢ proph_bor_tok (uniq_prvar x' ξi) c idx.
  Proof.
    rewrite /uniq_prvar /uniq_cell_tyi.
    by rewrite (proof_irrel (@to_inh_syn_type (uniq_cellₛ 𝔄) (vπ x inhabitant, (1%positive, (1%positive, 1%positive))))
                           (@to_inh_syn_type (uniq_cellₛ 𝔄) (vπ x' inhabitant, (1%positive, (1%positive, 1%positive))))).
  Qed.

  Lemma uniq_idx_bor_gen_retarget {𝔄} κ (x x': ~~ 𝔄) ξi idx
      (P: ~~ (uniq_cellₛ 𝔄) → proph (uniq_cellₛ 𝔄) → iProp Σ) :
    proph_idx_bor_gen κ (uniq_prvar x ξi) idx P ⊣⊢ proph_idx_bor_gen κ (uniq_prvar x' ξi) idx P.
  Proof.
    rewrite /uniq_prvar /uniq_cell_tyi.
    by rewrite (proof_irrel (@to_inh_syn_type (uniq_cellₛ 𝔄) (vπ x inhabitant, (1%positive, (1%positive, 1%positive))))
                           (@to_inh_syn_type (uniq_cellₛ 𝔄) (vπ x' inhabitant, (1%positive, (1%positive, 1%positive))))).
  Qed.

  Lemma uniq_ctrl_retarget {𝔄} (x x': ~~ 𝔄) ξi c (wπ: proph (uniq_cellₛ 𝔄)) :
    .PC[uniq_prvar x ξi] c wπ ⊣⊢ .PC[uniq_prvar x' ξi] c wπ.
  Proof.
    rewrite /uniq_prvar /uniq_cell_tyi.
    by rewrite (proof_irrel (@to_inh_syn_type (uniq_cellₛ 𝔄) (vπ x inhabitant, (1%positive, (1%positive, 1%positive))))
                           (@to_inh_syn_type (uniq_cellₛ 𝔄) (vπ x' inhabitant, (1%positive, (1%positive, 1%positive))))).
  Qed.

  Lemma uniq_tokγ_retarget {𝔄} (x x': ~~ 𝔄) ξi d g idx γ :
    ghost_var γ (1/2) (lstate_triv x) ∗ proph_bor_tok (uniq_prvar x' ξi) (uniq_cell x d g γ) idx ⊣⊢
    uniq_tokγ x ξi d g idx γ.
  Proof. by rewrite /uniq_tokγ (uniq_bor_tok_retarget x x'). Qed.

  Lemma uniq_persγ_retarget {𝔄} (ty: type 𝔄) (x x': ~~ 𝔄) ξi idx κ κp tid l :
    uniq_persγ ty x ξi idx κ κp tid l ⊣⊢ uniq_persγ ty x' ξi idx κ κp tid l.
  Proof. apply uniq_idx_bor_gen_retarget. Qed.

  Lemma uniq_pers_component_retarget {𝔄} (ty: type 𝔄) (x x': ~~ 𝔄) ξi d g d' g' idx κ tid l :
    uniq_body_pers_component ty x ξi d g idx κ tid l ⊣⊢
      uniq_body_pers_component ty x' ξi d' g' idx κ tid l.
  Proof. rewrite /uniq_body_pers_component. by setoid_rewrite (uniq_persγ_retarget ty x x'). Qed.

  Lemma uniq_body_proph_dep {𝔄} (x: ~~𝔄) d g γ :
    @vπ (uniq_cellₛ 𝔄) (uniq_cell x d g γ) ./ ξl x.
  Proof. apply uniq_cell_dep, syn_indep. Qed.

  (** ** Composing the equalizer of the controller of a unique borrow *)

  Lemma uniq_ctrl_eqz_fst {𝔄} (x₀: ~~𝔄) ξi c (wπ: proph (uniq_cellₛ 𝔄)) (uπ: proph 𝔄) :
    proph_ctx -∗ .PC[uniq_prvar x₀ ξi] c wπ -∗ (λ π, (wπ π).1) :== uπ -∗
    (λ π, (π (uniq_prvar x₀ ξi)).1) :== uπ.
  Proof.
    iIntros "#PROPH Pc Eqz".
    iApply (proph_ctrl_eqz_compose (uniq_prvar x₀ ξi) c wπ (λ a: uniq_cellₛ 𝔄, a.1)
      (λ b, (b, (1%positive, (1%positive, 1%positive)))) with "PROPH Pc Eqz"); [done|].
    intros ξl Dep. by apply (proph_dep_constr (λ b: 𝔄, (b, (1%positive, (1%positive, 1%positive))))).
  Qed.

  (** ** Non-expansiveness *)

  (** The payload depends on the lifetime of the type only up to equivalence, which is
      what [TypeNonExpansive] provides. *)
  Lemma uniq_payload_ne {𝔄} n (ty ty': type 𝔄) tid l x d g :
    (⊢ ty_lft ty ≡ₗ ty_lft ty') →
    (∀ x d g, ty.(ty_gho_own) x d g tid ≡{n}≡ ty'.(ty_gho_own) x d g tid) →
    uniq_payload ty tid l x d g ≡{n}≡ uniq_payload ty' tid l x d g.
  Proof.
    intros Hl Hg. rewrite /uniq_payload (guarded_upd_lft_equiv _ _ _ _ Hl) (cbytes_same ty ty' x l).
    do 3 f_equiv. apply Hg.
  Qed.

  Lemma uniq_payload_proper {𝔄} (ty ty': type 𝔄) tid tid' l x d g :
    (⊢ ty_lft ty ≡ₗ ty_lft ty') →
    (∀ x d g, ty.(ty_gho_own) x d g tid ⊣⊢ ty'.(ty_gho_own) x d g tid') →
    uniq_payload ty tid l x d g ⊣⊢ uniq_payload ty' tid' l x d g.
  Proof.
    intros Hl Hg. rewrite /uniq_payload (guarded_upd_lft_equiv _ _ _ _ Hl) (cbytes_same ty ty' x l).
    do 3 f_equiv. apply Hg.
  Qed.

  Lemma ofty_gho_ne {𝔄} n m (ty ty': type 𝔄) lr fv d g tid tid' :
    (∀ x d g, ty.(ty_gho_own) x d g tid ≡{n}≡ ty'.(ty_gho_own) x d g tid') →
    ofty_gho m ty lr fv d g tid ≡{n}≡ ofty_gho m ty' lr fv d g tid'.
  Proof.
    intros Hg. rewrite /ofty_gho. f_equiv=> x. rewrite (ty_fval_same ty ty').
    do 2 f_equiv. f_equiv. apply Hg.
  Qed.

  Lemma leaf_contents_ne {𝔄} n κp (ty ty': type 𝔄) p r d g tid tid' l :
    (⊢ ty_lft ty ≡ₗ ty_lft ty') →
    (∀ x d g, ty.(ty_gho_own) x d g tid ≡{n}≡ ty'.(ty_gho_own) x d g tid') →
    leaf_contents κp ty p r d g tid l ≡{n}≡ leaf_contents κp ty' p r d g tid' l.
  Proof.
    intros Hl Hg. rewrite /leaf_contents. f_equiv=> fv.
    rewrite /leaf_owned_b /leaf_owned_lz. generalize (norm_pat κp p r) (prfn_place r)=> {}p lr.
    have Hl': ∀ fv, lr_fval ty lr fv ↔ lr_fval ty' lr fv.
    { intros. destruct lr; rewrite /lr_fval //. by rewrite (ty_fval_same ty ty'). }
    have Hub: ((fbytes ty l fv ∗ ⌜lr_fval ty lr fv⌝) ∗
      guarded_upd lazyE @[ty_lft ty] (⧖(S d `max` g) ∗ ofty_gho 0 ty lr fv d g tid))%I ≡{n}≡
      ((fbytes ty' l fv ∗ ⌜lr_fval ty' lr fv⌝) ∗
      guarded_upd lazyE @[ty_lft ty'] (⧖(S d `max` g) ∗ ofty_gho 0 ty' lr fv d g tid'))%I.
    { rewrite (fbytes_same ty ty') (guarded_upd_lft_equiv _ _ _ _ Hl).
      f_equiv; [f_equiv; by rewrite Hl'|]. f_equiv. f_equiv. by apply ofty_gho_ne. }
    (* [PatBlocked] separately: [f_equiv] takes long to fail on it. *)
    destruct p as [|α| | | | |]; try exact Hub.
    rewrite /blocked_owned. do 3 f_equiv. f_equiv=> fv'.
    rewrite (fbytes_same ty ty') (guarded_upd_lft_equiv _ _ _ _ Hl). f_equiv.
    f_equiv. do 2 (f_equiv=>?). f_equiv. by apply ofty_gho_ne.
  Qed.

  Lemma uniq_gbody_ne {𝔄} n κp (ty ty': type 𝔄) tid l c wπ :
    (⊢ ty_lft ty ≡ₗ ty_lft ty') →
    (∀ x d g, ty.(ty_gho_own) x d g tid ≡{n}≡ ty'.(ty_gho_own) x d g tid) →
    uniq_gbody κp ty tid l c wπ ≡{n}≡ uniq_gbody κp ty' tid l c wπ.
  Proof.
    intros Hl Hg. rewrite /uniq_gbody. f_equiv=> p. f_equiv=> r.
    do 3 f_equiv. by apply leaf_contents_ne.
  Qed.

  Lemma uniq_gbody_proper {𝔄} κp (ty ty': type 𝔄) tid tid' l c wπ :
    (⊢ ty_lft ty ≡ₗ ty_lft ty') →
    (∀ x d g, ty.(ty_gho_own) x d g tid ⊣⊢ ty'.(ty_gho_own) x d g tid') →
    uniq_gbody κp ty tid l c wπ ⊣⊢ uniq_gbody κp ty' tid' l c wπ.
  Proof.
    intros Hl Hg. apply equiv_dist=> n. rewrite /uniq_gbody. f_equiv=> p. f_equiv=> r.
    do 3 f_equiv. apply leaf_contents_ne; [done|]=> x d g. by rewrite Hg.
  Qed.

  Lemma uniq_gbody_loc {𝔄} κp (ty: type 𝔄) tid l l' c wπ :
    (∀ x, cbytes ty x l ⊣⊢ cbytes ty x l') →
    uniq_gbody κp ty tid l c wπ ⊣⊢ uniq_gbody κp ty tid l' c wπ.
  Proof.
    intros Hl. rewrite /uniq_gbody /leaf_contents. f_equiv=> p. f_equiv=> r.
    do 3 f_equiv. f_equiv=> fv. f_equiv.
    rewrite /leaf_owned_b. generalize (norm_pat κp p r) (prfn_place r)=> {}p lr.
    destruct p as [|α| | | | |]; try by rewrite (fbytes_loc ty l l').
    rewrite /blocked_owned. do 2 f_equiv. f_equiv=> fv'. by rewrite (fbytes_loc ty l l').
  Qed.

  Lemma uniq_body_loc {𝔄} (ty: type 𝔄) x ξi d g idx κ tid l l' :
    (∀ x, cbytes ty x l ⊣⊢ cbytes ty x l') →
    uniq_body ty x ξi d g idx κ tid l ⊣⊢ uniq_body ty x ξi d g idx κ tid l'.
  Proof.
    intros Hl. rewrite /uniq_body /uniq_bodyγ /uniq_persγ. do 2 (f_equiv=>?).
    do 3 f_equiv. apply proph_idx_bor_gen_proper=> c wπ. by apply uniq_gbody_loc.
  Qed.

  Lemma uniq_body_ne {𝔄} n (ty ty': type 𝔄) x ξi d g idx κ tid l :
    (⊢ ty_lft ty ≡ₗ ty_lft ty') →
    (∀ x d g, ty.(ty_gho_own) x d g tid ≡{n}≡ ty'.(ty_gho_own) x d g tid) →
    uniq_body ty x ξi d g idx κ tid l ≡{n}≡ uniq_body ty' x ξi d g idx κ tid l.
  Proof.
    intros Hl Hg. rewrite /uniq_body /uniq_bodyγ /uniq_persγ. do 2 (f_equiv=>?).
    do 3 f_equiv. apply proph_idx_bor_gen_ne=> c wπ. by apply uniq_gbody_ne.
  Qed.

  Lemma uniq_body_contractive {𝔄} n (ty ty': type 𝔄) x ξi d g idx κ tid l :
    (⊢ ty_lft ty ≡ₗ ty_lft ty') →
    (∀ x d g, dist_later n (ty.(ty_gho_own) x d g tid) (ty'.(ty_gho_own) x d g tid)) →
    uniq_body ty x ξi d g idx κ tid l ≡{n}≡ uniq_body ty' x ξi d g idx κ tid l.
  Proof.
    intros Hl Hg. rewrite /uniq_body /uniq_bodyγ /uniq_persγ. do 2 (f_equiv=>?).
    do 3 f_equiv. apply proph_idx_bor_gen_contractive=> c wπ.
    destruct n as [|n]; [split; lia|]. apply dist_later_S.
    apply uniq_gbody_ne; [done|]=> x1 d1 g1.
    have := Hg x1 d1 g1. by rewrite dist_later_S.
  Qed.

  Lemma uniq_body_proper {𝔄} (ty ty': type 𝔄) x ξi d g idx κ tid tid' l :
    (⊢ ty_lft ty ≡ₗ ty_lft ty') →
    (∀ x d g, ty.(ty_gho_own) x d g tid ⊣⊢ ty'.(ty_gho_own) x d g tid') →
    uniq_body ty x ξi d g idx κ tid l ⊣⊢ uniq_body ty' x ξi d g idx κ tid' l.
  Proof.
    intros Hl Hg. rewrite /uniq_body /uniq_bodyγ /uniq_persγ. do 2 (f_equiv=>?).
    do 3 f_equiv. apply proph_idx_bor_gen_proper=> c wπ. by apply uniq_gbody_proper.
  Qed.

  Lemma uniq_pers_component_ne {𝔄} n (ty ty': type 𝔄) x ξi d g idx κ tid l :
    (⊢ ty_lft ty ≡ₗ ty_lft ty') →
    (∀ x d g, ty.(ty_gho_own) x d g tid ≡{n}≡ ty'.(ty_gho_own) x d g tid) →
    uniq_body_pers_component ty x ξi d g idx κ tid l ≡{n}≡
      uniq_body_pers_component ty' x ξi d g idx κ tid l.
  Proof.
    intros Hl Hg. rewrite /uniq_body_pers_component /uniq_persγ. f_equiv=>?.
    f_equiv. apply proph_idx_bor_gen_ne=> c wπ. by apply uniq_gbody_ne.
  Qed.

  Lemma uniq_pers_component_contractive {𝔄} n (ty ty': type 𝔄) x ξi d g idx κ tid l :
    (⊢ ty_lft ty ≡ₗ ty_lft ty') →
    (∀ x d g, dist_later n (ty.(ty_gho_own) x d g tid) (ty'.(ty_gho_own) x d g tid)) →
    uniq_body_pers_component ty x ξi d g idx κ tid l ≡{n}≡
      uniq_body_pers_component ty' x ξi d g idx κ tid l.
  Proof.
    intros Hl Hg. rewrite /uniq_body_pers_component /uniq_persγ. f_equiv=>?.
    f_equiv. apply proph_idx_bor_gen_contractive=> c wπ.
    destruct n as [|n]; [split; lia|]. apply dist_later_S.
    apply uniq_gbody_ne; [done|]=> x1 d1 g1.
    have := Hg x1 d1 g1. by rewrite dist_later_S.
  Qed.

  Lemma uniq_pers_component_proper {𝔄} (ty ty': type 𝔄) x ξi d g idx κ tid tid' l :
    (⊢ ty_lft ty ≡ₗ ty_lft ty') →
    (∀ x d g, ty.(ty_gho_own) x d g tid ⊣⊢ ty'.(ty_gho_own) x d g tid') →
    uniq_body_pers_component ty x ξi d g idx κ tid l ⊣⊢
      uniq_body_pers_component ty' x ξi d g idx κ tid' l.
  Proof.
    intros Hl Hg. rewrite /uniq_body_pers_component /uniq_persγ. f_equiv=>?.
    f_equiv. apply proph_idx_bor_gen_proper=> c wπ. by apply uniq_gbody_proper.
  Qed.

  (** ** The trivial state *)

  (** At the trivial state, the contents are the payload. *)
  Lemma leaf_contents_triv {𝔄} κp (ty: type 𝔄) x d g tid l :
    leaf_contents κp ty PatLeaf (inl (PlaceIn x)) d g tid l ⊣⊢ uniq_payload ty tid l x d g.
  Proof.
    rewrite /leaf_contents /leaf_owned_b /leaf_owned_lz uniq_payload_cell /=. iSplit.
    - iIntros "(%fv & [B %Hx] & Upd)". iSplitL "B"; [by iApply (fbytes_cbytes with "B")|].
      iApply (guarded_upd_mono with "[] Upd").
      iIntros "[$ (%x' & _ & -> & Gho)] !>". done.
    - iIntros "[Pt Upd]". rewrite cbytes_fbytes. iDestruct "Pt" as (fv Hfv) "B".
      iExists fv. iFrame "B". iSplit; [done|]. iApply (guarded_upd_mono with "[] Upd").
      iIntros "[$ Gho] !>". iExists x. by iFrame.
  Qed.

  (** At the trivial state, the body is the payload. *)
  Lemma uniq_gbody_triv_open {𝔄} κp (ty: type 𝔄) γ tid l x d g wπ :
    ghost_var γ (1/2) (lstate_triv x) -∗ ▷ uniq_gbody κp ty tid l (uniq_cell x d g γ) wπ -∗
    ◇ (⌜∀ π, (wπ π).1 = vπ x π⌝ ∗ ghost_var γ (1/2) (lstate_triv x) ∗
       ghost_var γ (1/2) (lstate_triv x) ∗ ▷ uniq_payload ty tid l x d g).
  Proof.
    iIntros "Gh Body". rewrite uniq_gbody_cell.
    iMod (bi.later_exist_except_0 with "Body") as (p) "Body".
    iMod (bi.later_exist_except_0 with "Body") as (r) "(_ & >%Hw & >Gh' & Upd)".
    iDestruct (ghost_var_agree with "Gh Gh'") as %[<- <-]%lstate_inj.
    iModIntro. iFrame "Gh Gh'". iSplit.
    { iPureIntro. intros π. by rewrite Hw prfn_den_in. }
    iNext. by rewrite leaf_contents_triv.
  Qed.

  Lemma uniq_gbody_triv_open' {𝔄} κp (ty: type 𝔄) γ tid l x d g wπ :
    ghost_var γ (1/2) (lstate_triv x) -∗ uniq_gbody κp ty tid l (uniq_cell x d g γ) wπ -∗
    ⌜∀ π, (wπ π).1 = vπ x π⌝ ∗ ghost_var γ (1/2) (lstate_triv x) ∗
       ghost_var γ (1/2) (lstate_triv x) ∗ uniq_payload ty tid l x d g.
  Proof.
    iIntros "Gh Body". rewrite uniq_gbody_cell.
    iDestruct "Body" as (p r) "(_ & %Hw & Gh' & Upd)".
    iDestruct (ghost_var_agree with "Gh Gh'") as %[<- <-]%lstate_inj.
    iFrame "Gh Gh'". iSplit.
    { iPureIntro. intros π. by rewrite Hw prfn_den_in. }
    by rewrite leaf_contents_triv.
  Qed.

  Lemma uniq_gbody_triv_close' {𝔄} κp (ty: type 𝔄) γ tid l x d g wπ :
    (∀ π, (wπ π).1 = vπ x π) →
    ghost_var γ (1/2) (lstate_triv x) -∗ uniq_payload ty tid l x d g -∗
    uniq_gbody κp ty tid l (uniq_cell x d g γ) wπ.
  Proof.
    iIntros (Hw) "Gh P". rewrite uniq_gbody_cell.
    iExists PatLeaf, (inl (PlaceIn x)). iFrame "Gh". iSplit; [iApply pat_ok_leaf|].
    iSplit. { iPureIntro. intros π. by rewrite Hw prfn_den_in. }
    by rewrite leaf_contents_triv.
  Qed.

  Lemma uniq_gbody_triv_close {𝔄} κp (ty: type 𝔄) γ tid l x d g wπ :
    (∀ π, (wπ π).1 = vπ x π) →
    ghost_var γ (1/2) (lstate_triv x) -∗ ▷ uniq_payload ty tid l x d g -∗
    ▷ uniq_gbody κp ty tid l (uniq_cell x d g γ) wπ.
  Proof. iIntros (Hw) "Gh P !>". by iApply (uniq_gbody_triv_close' with "Gh P"). Qed.

  Lemma uniq_gbody_triv_iff {𝔄} κp (ty: type 𝔄) γ tid l x d g wπ :
    ghost_var γ (1/2) (lstate_triv x) ∗ uniq_gbody κp ty tid l (uniq_cell x d g γ) wπ ⊣⊢
    ⌜∀ π, (wπ π).1 = vπ x π⌝ ∗ (ghost_var γ (1/2) (lstate_triv x) ∗
       ghost_var γ (1/2) (lstate_triv x) ∗ uniq_payload ty tid l x d g).
  Proof.
    iSplit.
    - iIntros "[Gh Body]". by iDestruct (uniq_gbody_triv_open' with "Gh Body") as "($ & $ & $ & $)".
    - iIntros "(% & $ & Gh & P)". by iApply (uniq_gbody_triv_close' with "Gh P").
  Qed.

  (** ** Accessors *)

  (** Open a unique borrow, keeping the index; closing may change the value
      and the depth. The payload is lazy, and so is the closing payload. *)
  Lemma uniq_body_acc_lazy {𝔄} (ty: type 𝔄) x ξi d g idx κ tid l E G :
    Timeless G → ↑Nllft ⊆ E →
    llft_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗
    uniq_body ty x ξi d g idx κ tid l -∗ G ={E}=∗
      ▷ uniq_payload ty tid l x d g ∗ ⧗1 ∗
      (∀ x1 d1 g1, ▷ uniq_payload ty tid l x1 d1 g1 -∗ ⧗1
        ={↑Nllft}=∗ uniq_body ty x1 ξi d1 g1 idx κ tid l ∗ G).
  Proof.
    iIntros (??) "#LFT #UNIQ #Gk (%κp & %γ & #Incl & (Gh & Tok) & ⧗ & #Bor) G".
    iMod (proph_idx_bor_gen_acc_idx with "LFT UNIQ Gk Tok Bor G") as (wπ) "[Body Close]";
      [done|].
    iMod (uniq_gbody_triv_open with "Gh Body") as "(_ & Gh & Gh' & P)".
    iModIntro. iFrame "P ⧗". iIntros (x1 d1 g1) "P ⧗".
    iMod (ghost_var_update_halves (lstate_triv x1) with "Gh Gh'") as "[Gh Gh']".
    iMod ("Close" $! (uniq_cell x1 d1 g1 γ) (vπ (uniq_cell x1 d1 g1 γ)) with "[Gh' P]")
      as "[Tok $]".
    { by iApply (uniq_gbody_triv_close with "Gh' P"). }
    iModIntro. iApply (uniq_body_from_parts with "Incl [Gh Tok] ⧗ [Bor]").
    - rewrite -(uniq_tokγ_retarget x1 x). iFrame.
    - by rewrite (uniq_persγ_retarget _ x1 x).
  Qed.

  (** As [uniq_body_acc_lazy], giving up the borrow when closing. *)
  Lemma uniq_body_acc_drop {𝔄} (ty: type 𝔄) x ξi d g idx κ tid l E G :
    Timeless G → ↑Nllft ⊆ E →
    llft_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗
    uniq_body ty x ξi d g idx κ tid l -∗ G ={E}=∗
      ▷ uniq_payload ty tid l x d g ∗ ⧗1 ∗
      (∀ x1 d1 g1, ▷ uniq_payload ty tid l x1 d1 g1 ={↑Nllft}=∗ G).
  Proof.
    iIntros (??) "#LFT #UNIQ #Gk (%κp & %γ & #Incl & (Gh & Tok) & ⧗ & #Bor) G".
    iMod (proph_idx_bor_gen_acc_idx with "LFT UNIQ Gk Tok Bor G") as (wπ) "[Body Close]";
      [done|].
    iMod (uniq_gbody_triv_open with "Gh Body") as "(_ & Gh & Gh' & P)".
    iModIntro. iFrame "P ⧗". iIntros (x1 d1 g1) "P".
    iMod (ghost_var_update_halves (lstate_triv x1) with "Gh Gh'") as "[_ Gh']".
    iMod ("Close" $! (uniq_cell x1 d1 g1 γ) (vπ (uniq_cell x1 d1 g1 γ)) with "[Gh' P]")
      as "[_ $]".
    { by iApply (uniq_gbody_triv_close with "Gh' P"). }
    done.
  Qed.

  (** As [uniq_body_acc_lazy], closing with a non-lazy payload. *)
  Lemma uniq_body_acc {𝔄} (ty: type 𝔄) x ξi d g idx κ tid l E G :
    Timeless G → ↑Nllft ⊆ E →
    llft_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗
    uniq_body ty x ξi d g idx κ tid l -∗ G ={E}=∗
      ▷ uniq_payload ty tid l x d g ∗ ⧗1 ∗
      (∀ x1 d1 g1, ▷ (⧖(S d1 `max` g1) ∗ ty.(ty_gho_own) x1 d1 g1 tid ∗ cbytes ty x1 l) -∗ ⧗1
        ={↑Nllft}=∗ uniq_body ty x1 ξi d1 g1 idx κ tid l ∗ G).
  Proof.
    iIntros (??) "#LFT #UNIQ #Gk Body G".
    iMod (uniq_body_acc_lazy with "LFT UNIQ Gk Body G") as "(P & $ & Close)"; [done..|].
    iModIntro. iFrame "P".
    iIntros (x1 d1 g1) "P ⧗". iApply ("Close" with "[P] ⧗").
    by iApply uniq_payload_intro_later.
  Qed.

  (** Open a unique borrow and run the lazy update of its payload, closing it with the
      same value and depth; this needs no [uniq_ctx]. Half of the guard keeps the borrow
      open, the other half runs the update. *)
  Lemma uniq_body_acc_keep {𝔄} (ty: type 𝔄) x ξi d g idx κ tid l E G :
    Timeless G → lazyE ⊆ E →
    llft_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗ κ ⊑ ty_lft ty -∗ £1 -∗
    uniq_body ty x ξi d g idx κ tid l -∗ G ={E}=∗
      ⧖(S d `max` g) ∗ ty.(ty_gho_own) x d g tid ∗ cbytes ty x l ∗
      (▷ (ty.(ty_gho_own) x d g tid ∗ cbytes ty x l)
        ={↑Nllft}=∗ uniq_body ty x ξi d g idx κ tid l ∗ G).
  Proof.
    iIntros (? HE) "#LFT #Gk #In £ (%κp & %γ & #Incl & (Gh & Tok) & ⧗ & #Bor) G".
    have ?: ↑Nllft ⊆ E. { etrans; [|done]. rewrite /lazyE. set_solver. }
    iMod (fractional.frac_split_guard_in_half with "G Gk") as (γh) "[H1 [H2 [#Gh2 #Back]]]";
      [solve_ndisj|].
    iMod (proph_idx_bor_gen_acc_idx_keep with "LFT Gh2 Tok Bor H1") as (wπ) "[Body Close]";
      [done..|].
    iMod (uniq_gbody_triv_open with "Gh Body") as "(%Hw & Gh & Gh' & P)".
    iMod (uniq_payload_force with "[] H2 £ P") as "(H2 & #⧖ & $ & $)"; [done| |].
    { iApply (guards_transitive with "Gh2 In"). }
    iFrame "⧖". iModIntro. iIntros "P". iMod ("Close" with "[Gh' P]") as "[Tok H1]".
    { iApply (uniq_gbody_triv_close with "Gh'"); [done|].
      iApply uniq_payload_intro_later. iNext. iFrame "∗#". }
    iMod (fupd_mask_mono with "(Back H1 H2)") as "$"; [solve_ndisj|].
    iModIntro. iExists κp, γ. iFrame "∗#".
  Qed.

  Lemma uniq_body_mono_upd {𝔄} (ty: type 𝔄) (x: ~~ 𝔄) (ξi: positive) (d g d' g': nat) (idx: Idx) (κ: lft) (tid: thread_id) (l: loc) E G :
    Timeless G →
    ↑Nllft ∪ ↑uniqN ⊆ E →
    d ≤ d' →
    g ≤ g' →
    llft_ctx -∗
    uniq_ctx -∗
    ⧖(S d' `max` g') -∗
    (G &&{↑NllftG}&&> @[κ]) -∗
    G -∗
    uniq_body ty x ξi d g idx κ tid l ={E}=∗
    G ∗ uniq_body ty x ξi d' g' idx κ tid l.
  Proof.
    iIntros (Gtimeless Hmask Hle1 Hle2) "#LFT #UNIQ #⧖ #guards G UniqBody".
    iMod (uniq_body_acc_lazy with "LFT UNIQ guards UniqBody G") as "(Inner & ⧗ & Back)";
        first by solve_ndisj.
    iMod (fupd_mask_subseteq (↑Nllft)) as "Upd"; [solve_ndisj|].
    iMod ("Back" with "[Inner] ⧗") as "[$ $]"; [|done].
    iNext. iApply (uniq_payload_map with "[] [] [] [] Inner").
    - iApply guards_refl.
    - iIntros "_". iFrame "⧖".
    - by iIntros "$".
    - iIntros "Gho". iModIntro.
      iDestruct (ty_gho_own_depth_mono with "Gho") as "[$ _]"; lia.
  Qed.

  (** Settling a unique borrow: recover the time receipt of its contents, by opening it
      with a guard for [κ] and running the lazy update of its payload (with
      [κ ⊑ ty_lft ty]). *)
  Lemma uniq_body_settle {𝔄} (ty: type 𝔄) x ξi d g idx κ tid l E G :
    Timeless G → lazyE ⊆ E →
    llft_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗ κ ⊑ ty_lft ty -∗ £1 -∗
    uniq_body ty x ξi d g idx κ tid l -∗ G ={E}=∗
      ⧖(S d `max` g) ∗ uniq_body ty x ξi d g idx κ tid l ∗ G.
  Proof.
    iIntros (? HE) "#LFT #Gk #In £ Body G".
    iMod (uniq_body_acc_keep with "LFT Gk In £ Body G") as "(#⧖ & Gho & Pt & Close)";
      [done..|].
    iFrame "⧖". iApply (fupd_mask_mono with "(Close [$Gho $Pt])").
    etrans; [|done]. rewrite /lazyE. set_solver.
  Qed.

  (** As [uniq_body_settle], paying for the later of the payload with a program step
      instead of a later credit. *)
  Lemma uniq_body_settle_step {𝔄} (ty: type 𝔄) x ξi d g idx κ tid l E G :
    Timeless G → lazyE ⊆ E →
    llft_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗ κ ⊑ ty_lft ty -∗
    uniq_body ty x ξi d g idx κ tid l -∗ G -∗ |={E}▷=>
      ⧖(S d `max` g) ∗ uniq_body ty x ξi d g idx κ tid l ∗ G.
  Proof.
    iIntros (? HE) "#LFT #Gk #In (%κp & %γ & #Incl & (Gh & Tok) & ⧗ & #Bor) G".
    have ?: ↑Nllft ⊆ E. { etrans; [|done]. rewrite /lazyE. set_solver. }
    iMod (fractional.frac_split_guard_in_half with "G Gk") as (γh) "[H1 [H2 [#Gh2 #Back]]]";
      [solve_ndisj|].
    iMod (proph_idx_bor_gen_acc_idx_keep with "LFT Gh2 Tok Bor H1") as (wπ) "[Body Close]";
      [done..|].
    iMod (uniq_gbody_triv_open with "Gh Body") as "(%Hw & Gh & Gh' & P)".
    iModIntro. iNext.
    iMod (uniq_payload_run with "[] H2 P") as "(H2 & #⧖ & Gho & Pt)"; [done| |].
    { iApply (guards_transitive with "Gh2 In"). }
    iMod (fupd_mask_mono with "(Close [Gh' Gho Pt])") as "[Tok H1]"; [done| |].
    { iApply (uniq_gbody_triv_close with "Gh'"); [done|].
      iApply uniq_payload_intro_later. iNext. iFrame "∗#". }
    iMod (fupd_mask_mono with "(Back H1 H2)") as "$"; [solve_ndisj|].
    iModIntro. iFrame "⧖". iExists κp, γ. iFrame "∗#".
  Qed.

  (** ** Allocation and the lender *)

  (** What the lender of a unique borrow gets back: the controller and the body, at
      some state. *)
  Definition uniq_lender {𝔄} (κp: lft) (ty: type 𝔄) (x₀: ~~𝔄) (ξi: positive)
      (tid: thread_id) (l: loc) : iProp Σ :=
    ∃ c wπ, .PC[uniq_prvar x₀ ξi] c wπ ∗ uniq_gbody κp ty tid l c wπ.

  (** Once [κp] has ended, the lender can force the bytes of what it got back, with the
      mask [lazyB] and without a guard: the contents are unblocked
      ([leaf_contents_unblock]); the ghost part is in a lazy update, where the equalizer of
      the controller is composed with the refinement. *)
  Lemma uniq_lender_unblock {𝔄} κp (ty: type 𝔄) x₀ ξi tid l :
    llft_ctx -∗ proph_ctx -∗ [†κp] -∗ uniq_lender κp ty x₀ ξi tid l ={lazyB}=∗
    ∃ fv, fbytes ty l fv ∗ guarded_upd lazyE @[ty_lft ty] (∃ x d g,
      ⌜ty.(ty_fval) x = Some fv⌝ ∗ ▷ ((λ π, (π (uniq_prvar x₀ ξi)).1) :== vπ x) ∗
      ⧖(S d `max` g) ∗ ty.(ty_gho_own) x d g tid).
  Proof.
    iIntros "#LFT #PROPH #†κ (%c & %wπ & Pc & Body)".
    rewrite (uniq_cell_surj c) uniq_gbody_cell.
    iDestruct "Body" as (p r) "(#Ok & %Hw & _ & C)".
    iMod (leaf_contents_unblock with "LFT Ok †κ C") as (fv) "[B Upd]".
    iModIntro. iExists fv. iFrame "B". iApply (guarded_upd_mono with "[Pc] Upd").
    iIntros "(%d' & %g' & ⧖ & %x & %Hx & Rel & Gho) !>". iExists x, d', g'.
    iFrame "⧖ Gho". iSplit; [done|].
    iDestruct (place_rfn_rel_eqz with "Rel") as "Eqz". iNext.
    iApply (uniq_ctrl_eqz_fst with "PROPH Pc").
    iApply (proph_eqz_eq with "Eqz"); [|done]. fun_ext=> π /=. by rewrite Hw prfn_place_den.
  Qed.

  (** Once [κp] has ended, the lender can settle what it got back, with a guard for
      the lifetime of the type: the contents are unblocked, and the equalizer of the
      controller is composed with the refinement. *)
  Lemma uniq_lender_settle {𝔄} κp (ty: type 𝔄) x₀ ξi tid l :
    llft_ctx -∗ proph_ctx -∗ [†κp] -∗ uniq_lender κp ty x₀ ξi tid l -∗
    guarded_upd lazyE @[ty_lft ty] (∃ x d g,
      ▷ ((λ π, (π (uniq_prvar x₀ ξi)).1) :== vπ x) ∗ ⧖(S d `max` g) ∗
      ty.(ty_gho_own) x d g tid ∗ cbytes ty x l).
  Proof.
    iIntros "#LFT #PROPH #†κ L" (G ?) "#Gty G".
    iDestruct (uniq_lender_unblock with "LFT PROPH †κ L") as "X".
    iMod (fupd_mask_mono with "X") as (fv) "[B Upd]"; [apply lazyB_lazyE|].
    iMod (guarded_upd_run with "Gty G Upd") as "[$ (%x & %d & %g & %Hx & Eqz & ⧖ & Gho)]";
      [done|].
    iModIntro. iExists x, d, g. iFrame. by iApply (fbytes_cbytes with "B").
  Qed.

  Lemma alloc_uniq_body
      {𝔄} (ty: type 𝔄) (x: ~~ 𝔄) (d: nat) (g: nat)
      (κ: lft) (tid: thread_id) (l: loc) E
   :
    (↑Nllft ∪ ↑prophN ∪ ↑uniqN ∪ ↑gmbN ⊆ E) →
    ⊢ llft_ctx -∗
      proph_ctx -∗
      uniq_ctx -∗ ⧖(S d `max` g) -∗
      (▷ ty.(ty_gho_own) x d g tid) -∗
      cbytes ty x l -∗
      ⧗1
      ={E}=∗
      ∃ ξi ζi idx,
        let ξ := uniq_prvar x ξi in
        let ζ := PrVar (at_locₛ 𝔄 ↾ prval_to_inh (@vπ (at_locₛ 𝔄) (l, x))) ζi in
        uniq_body ty x ξi d g idx κ tid l ∗
        ⟨π, π ζ = (l, (π ξ).1)⟩ ∗
        ([†κ] ={↑Nllft}=∗ ▷ uniq_lender κ ty x ξi tid l).
  Proof.
    intros Hmask. iIntros "#LFT #PROPH #UNIQ #⧖ gho pt ⧗".
    iMod (ghost_var_alloc (lstate_triv x)) as (γ) "[Gh Gh']".
    iMod (proph_loan_intro (uniq_cell_tyi x) E (uniq_cell x d g γ) with "PROPH UNIQ")
      as (ξi) "Loan"; [set_solver|].
    set ξ := uniq_prvar x ξi.
    set ζ𝔄i := (at_locₛ 𝔄 ↾ prval_to_inh (@vπ (at_locₛ 𝔄) (l, x))).
    iMod (proph_intro ζ𝔄i ∅ with "PROPH") as (ζi) "[_ ζtok]"; [set_solver|].
    set ζ := PrVar ζ𝔄i ζi.
    iDestruct (proph_loan_tok with "Loan") as "[ξtok ToLoan]".
    iMod (proph_resolve_toks _ ζ (λ π, (l, (π ξ).1)) [ξ] with "PROPH ζtok [ξtok]")
      as "[ζObs ξtok]".
    { set_solver. }
    { apply (proph_dep_constr (λ a, (l, a.1)) (λ π, π ξ)). apply proph_dep_one. }
    { rewrite big_sepL_singleton. iFrame "ξtok". }
    rewrite big_sepL_singleton.
    iDestruct ("ToLoan" with "ξtok") as "Loan".
    iMod (proph_loan_borrow_gen_pc E κ ξ (uniq_cell x d g γ) (vπ (uniq_cell x d g γ))
      (uniq_gbody κ ty tid l) with "LFT UNIQ Loan [Gh' gho pt]") as (idx) "(Tok & #Bor & Back)";
      [set_solver| |].
    { iApply (uniq_gbody_triv_close with "Gh'"); [done|].
      iApply uniq_payload_intro_later. iNext. iFrame "∗#". }
    iModIntro. iExists ξi, ζi, idx. iFrame "ζObs". iSplitL "Gh Tok ⧗".
    { iExists κ, γ. iFrame "∗#". iApply guards_refl. }
    iIntros "†κ". iMod ("Back" with "†κ") as "Back". iModIntro. iNext.
    iDestruct "Back" as (c wπ) "[Pc Body]". iExists c, wπ. iFrame.
  Qed.

  (** ** Basically dead lifetimes *)

  (** ** Resolution *)

  (** Resolving a unique borrow to its current value: freeze the borrow (at the
      trivial state), share the payload with [ty_share], and get the prophecy tokens
      from the sharing predicate by [ty_shr_guard_proph]. The sharing predicate of the
      payload and a guard of its points-to remain, as well as the persistent predicate.
      The later credits come from the time receipts. *)
  Lemma resolve_uniq_body {𝔄} (ty: type 𝔄) x ξi d g idx κ tid l E L G F :
    Timeless G →
    lctx_lft_alive E L κ → ↑Nllft ∪ ↑prophN ∪ ↑uniqN ∪ ↑gmbN ⊆ F →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ time_ctx -∗ κ ⊑ ty_lft ty -∗ elctx_interp E -∗
    (G &&{↑NllftG}&&> llctx_interp L) -∗
    G -∗ ⧖(S d `max` g) -∗
    uniq_body ty x ξi d g idx κ tid l ={F}=∗
      ⟨π, (π (uniq_prvar x ξi)).1 = (vπ x π)⟩ ∗ G ∗
      ty.(ty_shr) κ x d g tid ∗ (@[κ] &&{↑NllftG; 1}&&> cbytes ty x l) ∗
      ty.(ty_gho_pers) x d g tid.
  Proof.
    intro Ti.
    iIntros (Alv ?) "#LFT #PROPH #UNIQ #TIME #In E #Guard G #⧖".
    iIntros "(%κp & %γ & _ & (Gh & Tok) & ⧗ & #IBor) /=".
    leaf_open "Guard" with "G" as "[L Back]". { solve_ndisj. }
    iDestruct (Alv with "L E") as "#Alv".
    iMod ("Back" with "L") as "G".
    iDestruct (guards_transitive with "Guard Alv") as "#Guard_K".
    iMod (proph_idx_bor_gen_resolve_share F κ (uniq_prvar x ξi) (uniq_cell x d g γ) idx _
      (ghost_var γ (1/2) (lstate_triv x) ∗ uniq_payload ty tid l x d g) (ξl x)
      (ty.(ty_shr) κ x d g tid ∗ (@[κ] &&{↑NllftG; 1}&&> cbytes ty x l) ∗
        ty.(ty_gho_pers) x d g tid)%I G
      (0 + (d+1)*(g+1)) with "LFT PROPH UNIQ Guard_K [Gh] [⧗] G Tok IBor") as "(#Obs & $ & $)".
    { solve_ndisj. } { apply uniq_body_proph_dep. }
    { iIntros (wπ) "Body".
      iMod (uniq_gbody_triv_open with "Gh Body") as "(_ & _ & Gh & P)".
      iModIntro. iSplitL "Gh P"; [iNext; iFrame|].
      iIntros "!> [Gh P]". by iApply (uniq_gbody_triv_close' with "Gh P"). }
    { iIntros (W HW) "#Wκ W Bor".
      iMod (llftl_sep_split with "LFT Bor") as "[_ Bor]"; [solve_ndisj|].
      rewrite uniq_payload_cell.
      iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗ ⧖") as "[_ £]";
        first by solve_ndisj.
      iDestruct (lc_weaken (1 + 1 + d + d*(g+2) + (0 + (d+1)*(g+1))) with "£") as "£".
      { unfold advance_credits. nia. }
      iDestruct "£" as "[[[[£f £1] £d] £k] $]".
      (* Run the lazy update of the payload inside the borrow. *)
      iMod (llftl_sep_split with "LFT Bor") as "[Pt Bor]"; [solve_ndisj|].
      iMod (llftl_bor_guarded_upd with "LFT Wκ In W £f Bor") as "[Bor W]";
        [solve_ndisj|rewrite /lazyE; solve_ndisj|].
      iMod (llftl_sep_split with "LFT Bor") as "[_ Gho]"; [solve_ndisj|].
      iMod (llftl_bor_guard with "LFT Pt") as "$"; [solve_ndisj|].
      (* The persistent predicate of the contents, for [ty_share]. *)
      iMod (llftl_bor_guarded_extract _ _ _ _ (ty.(ty_gho_pers) x d g tid)
        with "LFT Wκ W Gho []") as "(W & Gho & Pers)";
        [solve_ndisj| |].
      { iIntros "!> Gho". iApply (ty_gho_pers_impl with "Gho"). }
      iMod (lc_fupd_elim_later with "£1 Pers") as "#Pers'".
      iMod (ty_share with "LFT In Pers' Wκ W Gho") as "Upd"; [solve_ndisj|].
      iMod (lc_step_fupdN_elim_later with "£d Upd") as ">[$ #Shr]". iFrame "Shr Pers'".
      iAssert (▷^(d*(g+2)) (∀ ζ : proph_var, ⌜ζ ∈ ξl x⌝ -∗
          W &&{ ↑NllftG; 0 + (d+1)*(g+1) }&&> 1:[ζ]))%I as "#Hallζlater".
      { iIntros (ζ) "%HIn".
        iDestruct (ty_shr_guard_proph ty κ x 0 d g tid ζ W HIn with "LFT In Pers' Shr") as "X".
        iNext. iApply "X". by iApply lguards_weaken_later; [|iFrame "Wκ"]; lia. }
      iMod (lc_fupd_elim_laterN with "£k Hallζlater") as "#Hallζ".
      by iModIntro. }
    iModIntro. iApply (proph_obs_impl with "Obs")=> π ->. done.
  Qed.

  (** ** Changing the type and lifetime *)

  Lemma ofty_gho_iff {𝔄} (ty ty': type 𝔄) m lr fv d g tid :
    □ (∀x d g tid, ty.(ty_gho_own) x d g tid ↔ ty'.(ty_gho_own) x d g tid) -∗
    ofty_gho m ty lr fv d g tid -∗ ofty_gho m ty' lr fv d g tid.
  Proof.
    iIntros "#EqOwn (%x & %Hx & Rel & Gho)". iExists x. rewrite (ty_fval_same ty' ty).
    iFrame "Rel". iSplit; [done|]. iNext. by iApply "EqOwn".
  Qed.

  Lemma blocked_owned_iff {𝔄} (ty ty': type 𝔄) m α lr tid l :
    ty_lft ty ≡ₗ ty_lft ty' -∗
    □ (∀x d g tid, ty.(ty_gho_own) x d g tid ↔ ty'.(ty_gho_own) x d g tid) -∗
    blocked_owned m ty α lr tid l -∗ blocked_owned m ty' α lr tid l.
  Proof.
    iIntros "#[_ Incl'] #EqOwn L †α". iMod ("L" with "†α") as (fv) "[B Upd]". iModIntro.
    iExists fv. rewrite (fbytes_same ty ty'). iFrame "B".
    iApply (guarded_upd_weaken with "Incl'"). iApply (guarded_upd_mono with "[] Upd").
    iIntros "(%d' & %g' & ⧖ & O) !>". iExists d', g'. iFrame "⧖".
    by iApply (ofty_gho_iff with "EqOwn O").
  Qed.

  Lemma leaf_owned_iff {𝔄} (ty ty': type 𝔄) m p r d g tid l :
    ty_lft ty ≡ₗ ty_lft ty' -∗
    □ (∀x d g tid, ty.(ty_gho_own) x d g tid ↔ ty'.(ty_gho_own) x d g tid) -∗
    leaf_owned false m ty p r d g tid l -∗ leaf_owned false m ty' p r d g tid l.
  Proof.
    iIntros "#Lfts #EqOwn L".
    iAssert (□ ∀ x d g, ofty_owned m ty x d g tid l -∗ ofty_owned m ty' x d g tid l)%I
      as "#Hofty".
    { iIntros "!>" (x' d' g') "[Pt Gho]". rewrite /ofty_owned (cbytes_same ty ty'). iFrame "Pt".
      iNext. by iApply "EqOwn". }
    destruct r as [lr|]; [|done]. rewrite /leaf_owned.
    destruct p; try (iDestruct "L" as (x') "[Rel O]"; iExists x'; iFrame "Rel";
      by iApply "Hofty").
    iApply (blocked_owned_iff with "Lfts EqOwn L").
  Qed.

  Lemma leaf_contents_iff {𝔄} κp (ty ty': type 𝔄) p r d g tid l :
    ty_lft ty ≡ₗ ty_lft ty' -∗
    □ (∀x d g tid, ty.(ty_gho_own) x d g tid ↔ ty'.(ty_gho_own) x d g tid) -∗
    leaf_contents κp ty p r d g tid l -∗ leaf_contents κp ty' p r d g tid l.
  Proof.
    iIntros "#[Incl Incl'] #EqOwn (%fv & B & Upd)". iExists fv.
    rewrite /leaf_owned_b /leaf_owned_lz.
    destruct (norm_pat κp p r) as [|α| | | | |];
      try (iDestruct "B" as "[B %Hlr]"; rewrite (fbytes_same ty ty'); iFrame "B";
        iSplit; [iPureIntro; destruct (prfn_place r); rewrite /lr_fval //;
          by rewrite (ty_fval_same ty' ty)|];
        iApply (guarded_upd_weaken with "Incl'"); iApply (guarded_upd_mono with "[] Upd");
        iIntros "[$ O] !>"; by iApply (ofty_gho_iff with "EqOwn O")).
    iSplitL; [|done]. iApply (blocked_owned_iff with "[] EqOwn B"). by iSplit.
  Qed.

  Lemma uniq_gbody_iff {𝔄} κp (ty ty': type 𝔄) tid l c wπ :
    ty_lft ty ≡ₗ ty_lft ty' -∗
    □ (∀x d g tid, ty.(ty_gho_own) x d g tid ↔ ty'.(ty_gho_own) x d g tid) -∗
    uniq_gbody κp ty tid l c wπ -∗ uniq_gbody κp ty' tid l c wπ.
  Proof.
    iIntros "#Lfts #EqOwn". rewrite /uniq_gbody.
    iIntros "(%p & %r & $ & $ & $ & C)". iApply (leaf_contents_iff with "Lfts EqOwn C").
  Qed.

  Lemma incl_uniq_persγ {𝔄} (ty ty': type 𝔄) x ξi idx κ κ' κp tid l :
    κ' ⊑ κ -∗ ty_lft ty ≡ₗ ty_lft ty' -∗
    □ (∀x d tid vl, ty.(ty_gho_own) x d tid vl ↔ ty'.(ty_gho_own) x d tid vl) -∗
    uniq_persγ ty x ξi idx κ κp tid l -∗ uniq_persγ ty' x ξi idx κ' κp tid l.
  Proof.
    iIntros "#InLft #Lfts #EqOwn Pc".
    iApply (proph_idx_bor_gen_shorten with "InLft [] Pc").
    iIntros "!> !>" (c wπ). iSplit; iIntros "B".
    - iApply (uniq_gbody_iff with "Lfts EqOwn B").
    - iDestruct "Lfts" as "[L1 L2]".
      iApply (uniq_gbody_iff with "[] [] B"); [by iSplit|].
      iIntros "!>" (????). iSplit; iIntros "H"; by iApply "EqOwn".
  Qed.

  Lemma incl_uniq_body_pers_component {𝔄} (ty ty': type 𝔄) x ξi d g idx κ κ' tid l :
    κ' ⊑ κ -∗ ty_lft ty ≡ₗ ty_lft ty' -∗
    □ (∀x d tid vl, ty.(ty_gho_own) x d tid vl ↔ ty'.(ty_gho_own) x d tid vl) -∗
    uniq_body_pers_component ty x ξi d g idx κ tid l -∗ uniq_body_pers_component ty' x ξi d g idx κ' tid l.
  Proof.
    iIntros "#InLft #Lfts #EqOwn (%κp & #Incl & Pc)".
    iExists κp. iSplit; [iApply (llftl_incl_trans with "InLft Incl")|].
    by iApply (incl_uniq_persγ with "InLft Lfts EqOwn Pc").
  Qed.

  Lemma incl_uniq_body {𝔄} (ty ty': type 𝔄) x ξi d g idx κ κ' tid l :
    κ' ⊑ κ -∗ ty_lft ty ≡ₗ ty_lft ty' -∗
    □ (∀x d tid vl, ty.(ty_gho_own) x d tid vl ↔ ty'.(ty_gho_own) x d tid vl) -∗
    uniq_body ty x ξi d g idx κ tid l -∗ uniq_body ty' x ξi d g idx κ' tid l.
  Proof.
    iIntros "#InLft #Lfts #EqOwn (%κp & %γ & #Incl & Tok & ⧗ & Pc)".
    iExists κp, γ. iFrame "Tok ⧗".
    iSplit; [iApply (llftl_incl_trans with "InLft Incl")|].
    by iApply (incl_uniq_persγ with "InLft Lfts EqOwn Pc").
  Qed.

  (** ** Rebodying at [static], changing the thread id *)

  Lemma uniq_body_acc_static_tid {𝔄} (ty: type 𝔄) x ξi d g idx tid tid' l E :
    ↑Nllft ⊆ E →
    llft_ctx -∗ uniq_ctx -∗
    uniq_body ty x ξi d g idx static tid l ={E}=∗ ▷ ◇ (
      uniq_payload ty tid l x d g ∗ ⧗1 ∗
      (∀ x1 d1 g1, ▷ uniq_payload ty tid' l x1 d1 g1 -∗ ⧗1 ={↑Nllft}=∗
         ∃ idx', uniq_body ty x1 ξi d1 g1 idx' static tid' l)).
  Proof.
    iIntros (?) "#LFT #UNIQ (%κp & %γ & #Incl & (Gh & Tok) & ⧗ & #Bor)".
    iMod (proph_idx_bor_gen_acc_rebody E static (uniq_prvar x ξi) _ idx _ (uniq_gbody κp ty tid' l)
      with "LFT UNIQ [] Tok Bor") as "Acc"; [done|by iApply llftl_tok_unit|].
    iModIntro. iNext. iMod "Acc" as (wπ) "[Body Close]".
    iDestruct (uniq_gbody_triv_open' with "Gh Body") as "(_ & Gh & Gh' & P)".
    iModIntro. iFrame "P ⧗". iIntros (x1 d1 g1) "P ⧗".
    iMod (ghost_var_update_halves (lstate_triv x1) with "Gh Gh'") as "[Gh Gh']".
    iMod ("Close" $! (uniq_cell x1 d1 g1 γ) (vπ (uniq_cell x1 d1 g1 γ)) with "[Gh' P] []")
      as (idx') "(Tok & #Bor' & _)".
    { by iApply (uniq_gbody_triv_close with "Gh' P"). }
    { iIntros "!>" (??) "[_ static]". iExFalso. iApply (llftl_end_unit with "static"). }
    iModIntro. iExists idx'. iApply (uniq_body_from_parts with "Incl [Gh Tok] ⧗ [Bor']").
    - rewrite -(uniq_tokγ_retarget x1 x). iFrame.
    - by rewrite /uniq_persγ (uniq_idx_bor_gen_retarget _ x1 x).
  Qed.

  (** ** Transforming the borrowed contents *)

  Lemma leaf_owned_unblocked {𝔄} c m (ty: type 𝔄) p lr d g tid l :
    (∀ α, p ≠ PatBlocked α) →
    leaf_owned c m ty p (inl lr) d g tid l ⊣⊢ ∃ x, place_rfn_rel lr x ∗ ofty_owned m ty x d g tid l.
  Proof. intros Hp. destruct p; try done. by destruct (Hp α). Qed.

  Lemma lpat_blocked_dec (p: lpat) : {α | p = PatBlocked α} + (∀ α, p ≠ PatBlocked α).
  Proof. destruct p; try (right; by intros ?). left. by eexists. Qed.

  (** The old body of a transformed unique borrow, from the final contents of the new
      borrow [ζ] (with its controller): the old body gets a state that refines [uπ],
      whose value is [f] of the value of [ζ]. The old body is blocked at [κp], the pattern
      lifetime of both borrows: once [κp] is dead, the new contents are unblocked
      ([leaf_contents_unblock]), their bytes are mapped with [BackB] (mask [lazyB], with a
      residue [RB]), and their ghost part, in a lazy update, with [BackG] (the receipt is
      bumped with [Bump]). *)
  Lemma uniq_gbody_map {𝔄 𝔅} E κp (ty: type 𝔄) (ty': type 𝔅) γ
      (fv: ~~𝔅 → ~~𝔄) (fp: 𝔅 → 𝔄)
      (h: nat → nat → nat * nat) (y₀: ~~𝔅) ζi tid l l'
      (y: ~~ (uniq_cellₛ 𝔅)) (wζ: proph (uniq_cellₛ 𝔅)) (uπ: proph (uniq_cellₛ 𝔄)) (s: ltype_state)
      (RB: FValue → FValue → iProp Σ) :
    Inj eq eq fp → (∀ y π, vπ (fv y) π = fp (vπ y π)) →
    (∀ π, (uπ π).1 = fp ((π (uniq_prvar y₀ ζi)).1)) →
    llft_ctx -∗ proph_ctx -∗ ty_lft ty ⊑ ty_lft ty' -∗
    ghost_var γ (1/2) s -∗ ghost_var γ (1/2) s -∗
    (∀ d1 g1, ⧖(S d1 `max` g1) ={lazyE}=∗ ⧖(S (h d1 g1).1 `max` (h d1 g1).2)) -∗
    (∀ w', fbytes ty' l' w' ={lazyB}=∗ ∃ w, fbytes ty l w ∗ RB w' w) -∗
    (∀ y1 d1 g1 w' w, ⌜ty'.(ty_fval) y1 = Some w'⌝ -∗ RB w' w -∗
       ty_gho_own ty' y1 d1 g1 tid ={lazyE}=∗
       ⌜ty.(ty_fval) (fv y1) = Some w⌝ ∗ ty_gho_own ty (fv y1) (h d1 g1).1 (h d1 g1).2 tid) -∗
    ▷ .PC[uniq_prvar y₀ ζi] y wζ -∗ ▷ uniq_gbody κp ty' tid l' y wζ ={E}=∗
    ▷ ∃ c', uniq_gbody κp ty tid l c' uπ.
  Proof.
    iIntros (Hf Hcomm Hu) "#LFT #PROPH #Incl Gh Gh' Bump BackB BackG Pc Body".
    rewrite (uniq_cell_surj y) uniq_gbody_cell.
    iMod (bi.later_exist_except_0 with "Body") as (p) "Body".
    iMod (bi.later_exist_except_0 with "Body") as (r) "(#Ok & >%Hw0 & _ & C)".
    set lrn := prfn_place r.
    have Hw: ∀ π, (wζ π).1 = place_rfn_den lrn π. { intros π. by rewrite Hw0 prfn_place_den. }
    set d1 := cell_d y. set g1 := cell_g y.
    set lr_old : place_rfn 𝔄 := PlaceProph (fv y.1) (λ π, fp ((π (uniq_prvar y₀ ζi)).1)).
    set r_old : prfn 𝔄 := inl lr_old.
    (* The relation of the old refinement, from the relation of the new one. *)
    iAssert (∀ c x, .PC[uniq_prvar y₀ ζi] c wζ -∗ (place_rfn_rel lrn x -∗
      place_rfn_rel lr_old (fv x)))%I as "Rel".
    { iIntros (c x) "Pc Rel". iDestruct (place_rfn_rel_eqz with "Rel") as "Eqz".
      rewrite /place_rfn_rel. iNext.
      iDestruct (uniq_ctrl_eqz_fst with "PROPH Pc [Eqz]") as "Eqz".
      { iApply (proph_eqz_eq with "Eqz"); [|done]. fun_ext=>π /=.
        by rewrite Hw. }
      iDestruct (proph_eqz_constr fp with "Eqz") as "Eqz".
      iApply (proph_eqz_eq with "Eqz"); [done|]. fun_ext=>π /=. by rewrite Hcomm. }
    iMod (ghost_var_update_halves (lstate (PatBlocked κp) r_old) with "Gh Gh'") as "[Gh _]".
    iModIntro. iNext. iExists (uniq_cell (fv y.1) d1 g1 γ). rewrite uniq_gbody_cell.
    iExists (PatBlocked κp), r_old. iFrame "Gh". iSplit; [iApply pat_ok_blocked; iApply guards_refl|].
    iSplit. { iPureIntro. intros π. by rewrite Hu /r_old prfn_den_inl. }
    iExists inhabitant. rewrite /leaf_owned_b /leaf_owned_lz /=. iSplitL; [|done].
    iIntros "#†κ". iMod (leaf_contents_unblock with "LFT Ok †κ C") as (w') "[B Upd]".
    iMod ("BackB" with "B") as (w) "[B RB]". iModIntro. iExists w. iFrame "B".
    iApply (guarded_upd_weaken with "Incl").
    iApply (guarded_upd_mono with "[Bump BackG RB Pc] Upd").
    iIntros "(%d2 & %g2 & ⧖2 & %x & %Hx & R & Gho)".
    iMod ("BackG" with "[//] RB Gho") as "[%Hx' Gho]".
    iMod ("Bump" with "⧖2") as "⧖2".
    iModIntro. iExists (h d2 g2).1, (h d2 g2).2. iFrame "⧖2".
    iExists (fv x). iFrame "Gho". iSplit; [done|]. by iApply ("Rel" with "Pc R").
  Qed.

  (** Replace a unique borrow by a fresh one at another type and location, given a way
      to transform the payload (which is given a guard for [κ]); the transformation
      also provides a way back for the contents (and their receipts): for the bytes (with
      the mask [lazyB], and a residue [RB]) and for the ghost part. The old prophecy
      variable is resolved to [f] of the new one. *)
  Lemma uniq_body_transform_gen {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) x x' d g ξi ξidx κ tid l l' E G
    (fv: ~~𝔅 → ~~𝔄) (fp: 𝔅 → 𝔄) (h: nat → nat → nat * nat) (RB: FValue → FValue → iProp Σ)
    :
      Timeless G →
      Inj eq eq fp → (∀ y π, vπ (fv y) π = fp (vπ y π)) →
      ↑Nllft ∪ ↑prophN ∪ ↑uniqN ∪ ↑gmbN ⊆ E →
      llft_ctx -∗
      proph_ctx -∗
      uniq_ctx -∗
      ty_lft ty ⊑ ty_lft ty' -∗
      (∀ G', ⌜Timeless G'⌝ -∗ (G' &&{↑NllftG}&&> @[κ]) -∗ G' -∗
        ▷ uniq_payload ty tid l x d g ={E}=∗
        G' ∗ ▷ uniq_payload ty' tid l' x' d g ∗
        (∀ d1 g1, ⧖(S d1 `max` g1) ={lazyE}=∗ ⧖(S (h d1 g1).1 `max` (h d1 g1).2)) ∗
        (∀ w', fbytes ty' l' w' ={lazyB}=∗ ∃ w, fbytes ty l w ∗ RB w' w) ∗
        (∀ y1 d1 g1 w' w, ⌜ty'.(ty_fval) y1 = Some w'⌝ -∗ RB w' w -∗
          ty_gho_own ty' y1 d1 g1 tid ={lazyE}=∗
          ⌜ty.(ty_fval) (fv y1) = Some w⌝ ∗
          ty_gho_own ty (fv y1) (h d1 g1).1 (h d1 g1).2 tid)) -∗
      (G &&{↑NllftG}&&> @[κ]) -∗
      G -∗
      uniq_body ty x ξi d g ξidx κ tid l
      ={E}=∗ ∃ ζi ζidx ,
      ⟨π, (π (uniq_prvar x ξi)).1 = fp ((π (uniq_prvar x' ζi)).1)⟩ ∗
      uniq_body ty' x' ζi d g ζidx κ tid l' ∗ G.
  Proof.
    intros Htimeless Hinj Hcomm Hmask.
    iIntros "#LFT #PROPH #UNIQ #Incl wand #GuardsK G (%κp & %γ & #Incl' & (Gh & Tok) & ⧗ & #Bor)".
    iMod (ghost_var_alloc (lstate_triv x')) as (γ') "[Gh2 Gh2']".
    iMod (proph_loan_intro (uniq_cell_tyi x') E (uniq_cell x' d g γ') with "PROPH UNIQ")
      as (ζi) "Loan"; [set_solver|].
    (* Only the first component of the old controller matters. *)
    set fπ := λ (c: (uniq_cellₛ 𝔅)),
      ((fp c.1, (1%positive, (1%positive, 1%positive))) : uniq_cellₛ 𝔄).
    iMod (proph_idx_bor_gen_map E κ (uniq_prvar x ξi) (uniq_cell x d g γ) ξidx
      (uniq_gbody κp ty tid l) (uniq_prvar x' ζi) (uniq_cell x' d g γ')
      (uniq_gbody κp ty' tid l') fπ G
      with "LFT PROPH UNIQ GuardsK [wand Gh Gh2'] G Loan Tok Bor") as "(#Obs & Bor' & G)".
    { solve_ndisj. }
    { iIntros (G' wπ ?) "#G'κ G' Body".
      iMod (uniq_gbody_triv_open with "Gh Body") as "(_ & Gh & Gh' & P)".
      iMod ("wand" with "[//] G'κ G' P") as "($ & P' & Bump & BackB & BackG)".
      iModIntro. iExists (vπ (uniq_cell x' d g γ')).
      iSplitL "Gh2' P'". { by iApply (uniq_gbody_triv_close with "Gh2' P'"). }
      iIntros (y' wζ') "Pc Body".
      iApply (uniq_gbody_map _ _ _ _ _ fv fp with "LFT PROPH Incl Gh Gh' Bump BackB BackG Pc Body");
        [done|by intros π]. }
    iDestruct "Bor'" as (ζidx) "[Tok' #Bor']".
    iModIntro. iExists ζi, ζidx. iFrame "G".
    iSplitR. { iApply (proph_obs_impl with "Obs")=> π ->. done. }
    iExists κp, γ'. iFrame "∗#".
  Qed.

  (** [uniq_body_transform_gen] where the old payload is forced (with the guard for [κ],
      [κ ⊑ ty_lft ty] and a later credit), so that the transformation gets the old
      contents. *)
  Lemma uniq_body_transform {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) x x' d g ξi ξidx κ tid l l' E G
    (f: 𝔅 →ₛ 𝔄) (h: nat → nat → nat * nat) (RB: FValue → FValue → iProp Σ)
    :
      Timeless G →
      Inj eq eq ((!ₛ) f) →
      ↑Nllft ∪ ↑prophN ∪ ↑uniqN ∪ ↑gmbN ⊆ E →
      llft_ctx -∗
      proph_ctx -∗
      uniq_ctx -∗
      κ ⊑ ty_lft ty -∗ ty_lft ty ⊑ ty_lft ty' -∗
      (▷ ty_gho_own ty x d g tid ∗ cbytes ty x l
        ={E}=∗ ▷ ty_gho_own ty' x' d g tid ∗ cbytes ty' x' l' ∗
        (∀ d1 g1, ⧖(S d1 `max` g1) ={lazyE}=∗ ⧖(S (h d1 g1).1 `max` (h d1 g1).2)) ∗
        (∀ w', fbytes ty' l' w' ={lazyB}=∗ ∃ w, fbytes ty l w ∗ RB w' w) ∗
        (∀ x'1 d1 g1 w' w, ⌜ty'.(ty_fval) x'1 = Some w'⌝ -∗ RB w' w -∗
          ty_gho_own ty' x'1 d1 g1 tid ={lazyE}=∗
          ⌜ty.(ty_fval) (f ~~$ₛ x'1) = Some w⌝ ∗
          ty_gho_own ty (f ~~$ₛ x'1) (h d1 g1).1 (h d1 g1).2 tid)
        ) -∗
      (G &&{↑NllftG}&&> @[κ]) -∗
      G -∗
      £1 -∗
      uniq_body ty x ξi d g ξidx κ tid l
      ={E}=∗ ∃ ζi ζidx ,
      ⟨π, (π (uniq_prvar x ξi)).1 = (!ₛ) f ((π (uniq_prvar x' ζi)).1)⟩ ∗
      uniq_body ty' x' ζi d g ζidx κ tid l' ∗ G.
  Proof.
    intros Htimeless Hinj Hmask.
    iIntros "#LFT #PROPH #UNIQ #In #Incl wand #GuardsK G £ Body".
    have Hcomm: ∀ y π, vπ (f ~~$ₛ y) π = (!ₛ) f (vπ y π).
    { intros. by rewrite syn_type_morphism_commutes. }
    iApply (uniq_body_transform_gen ty ty' x x' d g ξi ξidx κ tid l l' E G
      (λ y, f ~~$ₛ y) ((!ₛ) f) h RB Htimeless Hinj Hcomm Hmask
      with "LFT PROPH UNIQ Incl [wand £] GuardsK G Body").
    iIntros (G' ?) "#G'κ G' P".
    iMod (uniq_payload_force with "[] G' £ P") as "($ & #⧖ & Gho & Pt)";
      [rewrite /lazyE; solve_ndisj| |].
    { iApply (guards_transitive with "G'κ In"). }
    iMod ("wand" with "[$Gho $Pt]") as "(Gho' & Pt' & $ & $ & $)".
    iModIntro. iApply uniq_payload_intro_later. iNext. iFrame "∗#".
  Qed.

  (** [uniq_body_transform_gen] where the transformations do not change the depth and
      are run lazily; this needs no later credit. *)
  Lemma uniq_body_transform_lazy {𝔄 𝔅} (ty: type 𝔄) (ty': type 𝔅) x x' d g ξi ξidx κ tid l l' E G
    (f: 𝔅 →ₛ 𝔄) (RB: FValue → FValue → iProp Σ)
    :
      Timeless G →
      Inj eq eq ((!ₛ) f) →
      ↑Nllft ∪ ↑prophN ∪ ↑uniqN ∪ ↑gmbN ⊆ E →
      llft_ctx -∗
      proph_ctx -∗
      uniq_ctx -∗
      ty_lft ty ≡ₗ ty_lft ty' -∗
      (cbytes ty x l -∗ cbytes ty' x' l') -∗
      (ty_gho_own ty x d g tid ={lazyE}=∗ ty_gho_own ty' x' d g tid) -∗
      (∀ w', fbytes ty' l' w' ={lazyB}=∗ ∃ w, fbytes ty l w ∗ RB w' w) -∗
      (∀ x'1 d1 g1 w' w, ⌜ty'.(ty_fval) x'1 = Some w'⌝ -∗ RB w' w -∗
        ty_gho_own ty' x'1 d1 g1 tid ={lazyE}=∗
        ⌜ty.(ty_fval) (f ~~$ₛ x'1) = Some w⌝ ∗ ty_gho_own ty (f ~~$ₛ x'1) d1 g1 tid) -∗
      (G &&{↑NllftG}&&> @[κ]) -∗
      G -∗
      uniq_body ty x ξi d g ξidx κ tid l
      ={E}=∗ ∃ ζi ζidx ,
      ⟨π, (π (uniq_prvar x ξi)).1 = (!ₛ) f ((π (uniq_prvar x' ζi)).1)⟩ ∗
      uniq_body ty' x' ζi d g ζidx κ tid l' ∗ G.
  Proof.
    intros Htimeless Hinj Hmask.
    iIntros "#LFT #PROPH #UNIQ #[Incl Incl'] FwB FwGho BkB BkGho #GuardsK G Body".
    have Hcomm: ∀ y π, vπ (f ~~$ₛ y) π = (!ₛ) f (vπ y π).
    { intros. by rewrite syn_type_morphism_commutes. }
    iApply (uniq_body_transform_gen ty ty' x x' d g ξi ξidx κ tid l l' E G
      (λ y, f ~~$ₛ y) ((!ₛ) f) (λ d g, (d, g)) RB Htimeless Hinj Hcomm Hmask
      with "LFT PROPH UNIQ Incl [FwB FwGho BkB BkGho] GuardsK G Body").
    iIntros (G' ?) "_ $ P". iModIntro. iSplitL "FwB FwGho P".
    { iNext. iApply (uniq_payload_map with "Incl' [] FwB FwGho P"). by iIntros "$". }
    iSplitR; [by iIntros (??) "$"|]. iFrame.
  Qed.

  (** ** Reborrowing *)

  (** What the lender of a reborrow (at [κ']) of a unique borrow (at [κ]) gets back
      once [κ'] has ended: the original borrow (the observer and the persistent part),
      whose body is at the final state of the reborrow (the state of the reborrow is
      copied: its blocked lifetimes are included in [κ'], hence in [κ ⊑ κp]), together
      with the outer half of the ghost variable (at that state) and the reborrow's
      controller. It is settled with [uniq_restored_settle]. *)
  Definition uniq_restored {𝔄} (ty: type 𝔄) (x₀: ~~𝔄) (ξi ζi: positive) (κ κ': lft)
      (tid: thread_id) (l: loc) : iProp Σ :=
    ∃ κp γ γk c wπ idx p (lr: place_rfn 𝔄), κ ⊑ κp ∗
      proph_bor_tok (uniq_prvar x₀ ξi) (uniq_cell c.1 (cell_d c) (cell_g c) γ) idx ∗ ⧗1 ∗
      uniq_persγ ty x₀ ξi idx κ κp tid l ∗
      ▷ (.PC[uniq_prvar x₀ ζi] c wπ ∗ ghost_var γ (1/2) (lstate p (inl lr)) ∗
         ⌜∀ π, (wπ π).1 = place_rfn_den lr π⌝ ∗ pat_ok κ' p ∗
         ghost_var γk (1/2) (lstate p (inl lr))).

  (** Reborrowing records no summary of the final value: the inheritance only gives
      back the restored borrow (see [uniq_restored]). *)
  Lemma uniq_body_reborrow {𝔄} (ty: type 𝔄) x ξi d g idx κ κ' tid l E :
    ↑Nllft ∪ ↑prophN ∪ ↑uniqN ∪ ↑gmbN ⊆ E →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ κ' ⊑ κ -∗ ⧗1 -∗
    uniq_body ty x ξi d g idx κ tid l ={E}=∗ ∃ ζi idx',
      uniq_body ty x ζi d g idx' κ' tid l ∗
      ([†κ'] ={↑Nllft}=∗ uniq_restored ty x ξi ζi κ κ' tid l).
  Proof.
    iIntros (?) "#LFT #PROPH #UNIQ #κ'⊑κ ⧗ (%κp & %γ & #Incl & (Gh & Tok) & ⧗o & #Bor)".
    iMod (ghost_var_alloc (lstate_triv x)) as (γζ) "[Ghζ Ghζ']".
    iMod (proph_loan_intro (uniq_cell_tyi x) E (uniq_cell x d g γζ) with "PROPH UNIQ")
      as (ζi) "Loan"; [set_solver|].
    iMod (ghost_var_alloc (lstate_triv x)) as (γk) "[Ghk Ghk']".
    set R := λ (c: ~~ (uniq_cellₛ 𝔄)) (w: proph (uniq_cellₛ 𝔄)),
      (∃ p (lr: place_rfn 𝔄), ghost_var γ (1/2) (lstate p (inl lr)) ∗
        ⌜∀ π, (w π).1 = place_rfn_den lr π⌝ ∗
        pat_ok κ' p ∗ ghost_var γk (1/2) (lstate p (inl lr)))%I.
    iMod (proph_idx_bor_gen_reborrow E κ κ' (uniq_prvar x ξi) (uniq_cell x d g γ) idx
      (uniq_gbody κp ty tid l) (uniq_gbody κ' ty tid l) R
      (λ c, uniq_cell c.1 (cell_d c) (cell_g c) γ) (uniq_cell x d g γζ) ζi
      with "LFT PROPH UNIQ κ'⊑κ [Ghk' Ghζ'] [Gh Ghk] Loan Tok Bor") as "[Bor' Inh]";
      [solve_ndisj|by rewrite /= cell_d_uniq_cell cell_g_uniq_cell| | |].
    { (* The reborrow starts at the trivial state, which [γk] pins. *)
      iIntros (wπ wζ) "Body R".
      iMod (bi.later_exist_except_0 with "R") as (p) "R".
      iMod (bi.later_exist_except_0 with "R") as (lr) "(>Gh & >%Hw & Ok & >Ghk)".
      iDestruct (ghost_var_agree with "Ghk Ghk'") as %[-> [= ->]]%lstate_inj.
      iMod (uniq_gbody_triv_open with "Gh Body") as "(_ & Gh & Gh' & P)".
      iModIntro. iSplitL "Ghζ' P".
      { iApply (uniq_gbody_triv_close with "Ghζ' P"). intros π. by rewrite Hw. }
      iNext. iIntros (c2 w2) "Body †κ'". rewrite uniq_gbody_cell {1}/uniq_gbody.
      iMod (bi.later_exist_except_0 with "Body") as (p2) "Body".
      iMod (bi.later_exist_except_0 with "Body") as (r2) "(#Ok2 & >%Hw2 & >Ghζ2 & Upd)".
      (* The state is copied, normalized for a leaf (see [leaf_node]). *)
      set p3 := norm_pat κ' p2 r2. set lr3 := prfn_place r2.
      iAssert (▷ pat_ok κ' p3)%I as "#Ok3". { iNext. by iApply pat_ok_norm. }
      have Hw3: ∀ π, (w2 π).1 = place_rfn_den lr3 π.
      { intros π. by rewrite Hw2 prfn_place_den. }
      iMod (ghost_var_update_halves (lstate p3 (inl lr3)) with "Gh Gh'") as "[Gh Gh']".
      iMod (ghost_var_update_halves (lstate p3 (inl lr3)) with "Ghk Ghk'") as "[Ghk Ghk']".
      iModIntro. iSplitL "Gh' Upd".
      - iNext. iExists p3, (inl lr3). rewrite (leaf_contents_norm κ' κp).
        iFrame "Gh' Upd". iSplit; [|by rewrite prfn_den_inl].
        iApply (pat_ok_mono with "[] Ok3"). iApply (llftl_incl_trans with "κ'⊑κ Incl").
      - iNext. iExists p3, lr3. by iFrame "∗#". }
    { iExists PatLeaf, (PlaceIn x). iFrame "Gh Ghk". iSplit; [|iApply pat_ok_leaf].
      iPureIntro. intros π. done. }
    iDestruct "Bor'" as (idx') "[Tok' #Bor']".
    iModIntro. iExists ζi, idx'. iSplitL "Ghζ Tok' ⧗".
    { iExists κ', γζ. iFrame "∗#". iApply guards_refl. }
    iIntros "†κ'". iMod ("Inh" with "†κ'") as (c wπ idx'') "(Tok & #Bor'' & Pc & R)".
    iMod (bi.later_exist_except_0 with "R") as (p) "R".
    iMod (bi.later_exist_except_0 with "R") as (lr) "(Gh & Hw & Ok & Ghk)".
    iModIntro. iExists κp, γ, γk, c, wπ, idx'', p, lr. iFrame "∗#". iExact "Incl".
  Qed.

  (** Settling a restored borrow: open it (with a guard for [κ]), unblock its contents
      (all blocked lifetimes are included in [κ'], which has ended), and close it at the
      trivial state. The reborrow's prophecy variable is equalized with the final
      value. *)
  Lemma uniq_restored_settle {𝔄} (ty: type 𝔄) x₀ ξi ζi κ κ' tid l E G :
    Timeless G → lazyE ⊆ E →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗ κ ⊑ ty_lft ty -∗
    [†κ'] -∗ £1 -∗ £1 -∗ uniq_restored ty x₀ ξi ζi κ κ' tid l -∗ G ={E}=∗
      ∃ x d g idx, ⧖(S d `max` g) ∗ uniq_body ty x ξi d g idx κ tid l ∗
        ▷ ((λ π, (π (uniq_prvar x₀ ζi)).1) :== vπ x) ∗ G.
  Proof.
    iIntros (? HE) "#LFT #PROPH #UNIQ #Gk #In #†κ' £ £' Rst G".
    iDestruct "Rst" as (κp γ γk c wπ idx p lr) "(#Incl & Tok & ⧗ & #Bor & Rst)".
    iMod (lc_fupd_elim_later with "£ Rst") as "(Pc & Gh & %Hw & #Ok & _)".
    have ?: ↑Nllft ⊆ E. { etrans; [|done]. rewrite /lazyE. set_solver. }
    iMod (fractional.frac_split_guard_in_half with "G Gk") as (γh) "[H1 [H2 [#Gh2 #Back]]]";
      [solve_ndisj|].
    iMod (proph_idx_bor_gen_acc_idx with "LFT UNIQ Gh2 Tok Bor H1") as (wπ') "[Body Close]";
      [done|].
    rewrite uniq_gbody_cell.
    iMod (lc_fupd_elim_later with "£' Body") as "Body".
    iDestruct "Body" as (p' r') "(_ & %Hw' & Gh' & C)".
    iDestruct (ghost_var_agree with "Gh Gh'") as %[<- <-]%lstate_inj.
    iDestruct (leaf_contents_unblock_at with "LFT Ok †κ' C") as "Upd".
    iMod (fupd_mask_mono with "Upd") as (fv) "[B Upd]"; [by etrans; [apply lazyB_lazyE|]|].
    iMod (guarded_upd_run with "[] H2 Upd") as "[H2 (%d' & %g' & #⧖' & %y & %Hy & Rel & Gho)]";
      [done| |].
    { iApply (guards_transitive with "Gh2 In"). }
    iDestruct (fbytes_cbytes with "B") as "Pt"; [done|].
    iMod (ghost_var_update_halves (lstate_triv y) with "Gh Gh'") as "[Gh Gh']".
    iSpecialize ("Close" $! (uniq_cell y d' g' γ) (vπ (uniq_cell y d' g' γ))).
    iMod (fupd_mask_mono with "(Close [Gh' Pt Gho])") as "[Tok H1]"; [done| |].
    { iApply (uniq_gbody_triv_close with "Gh'"); [done|].
      iApply uniq_payload_intro_later. iNext. iFrame "∗#". }
    iMod (fupd_mask_mono with "(Back H1 H2)") as "$"; [solve_ndisj|].
    iModIntro. iExists y, d', g', idx. iFrame "⧖'". iSplitL "Gh Tok ⧗".
    { iApply (uniq_body_from_parts with "Incl [Gh Tok] ⧗ [Bor]").
      - rewrite -(uniq_tokγ_retarget y x₀). iFrame.
      - by rewrite (uniq_persγ_retarget _ y x₀). }
    iDestruct (place_rfn_rel_eqz with "Rel") as "Eqz". iNext.
    iApply (uniq_ctrl_eqz_fst with "PROPH Pc").
    iApply (proph_eqz_eq with "Eqz"); [|done]. fun_ext=> π /=. by rewrite Hw.
  Qed.
End uniq_util_bytes.
