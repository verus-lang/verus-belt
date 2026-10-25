(** * Place types (ltypes)

  This file ports the idea of RefinedRust's place types ([ltype]s, see
  [rust_typing/ltypes.v] of the RefinedRust development and §5.2 of the paper)
  to VerusBelt, on top of prophetic borrows ([util/proph_bor.v]). It only
  contains the model (definitions and basic laws); typing rules come later.

  ** Syntax

  [lty 𝔄] is a closed syntax of place types, indexed by the syntactic type
  [𝔄] of the values stored at the place:
  - [OfTy ty]: the place contains a value of type [ty];
  - [Blocked ty κ]: the place is blocked (e.g. reborrowed) until [κ] ends,
    afterwards it contains a value of type [ty];
  - [UniqLty lt κ]: the place contains a unique borrow [&uniq{κ}] whose
    referent has place type [lt];
  - [OwnPtrLty n lt]: the place contains an owned pointer ([own_ptr n]) whose
    pointee has place type [lt];
  - [ProdLty lt1 lt2]: a pair of places.
  [lty_core] replaces [Blocked ty κ] by [OfTy ty] (pointwise otherwise), as
  RefinedRust's [lty_core]. Unlike RefinedRust, there is no separate
  refinement-indexed wrapper: the index [𝔄] of [lty] plays the role of
  RefinedRust's refinement type, and [lty_core] preserves it definitionally.

  ** Place refinements

  A blocked place has no current value of type [~~𝔄] (e.g. [~~Zₛ = Z] cannot
  mention a prophecy). As in RefinedRust, refinements are therefore _place
  refinements_: [PlaceIn x] (a current value) or [PlaceGhost x₀ ζi], denoting
  the final value of the (unique-borrow) prophecy variable [uniq_prvar x₀ ζi]
  (as for blocked type-context entries, cf. [blockedπ]; [x₀] only witnesses
  inhabitation). Compound places additionally have structured refinements
  ([prfn_struct]): the refinement of [UniqLty lt κ] is [(l', r, ξi, γ)] (the
  referent location, the referent's refinement, the borrow's prophecy
  variable id, and the ghost name of its state); [OwnPtrLty] has [(l', r)];
  [ProdLty] has [(r1, r2)]. [prfn 𝔄] depends only on [𝔄], not on the place
  type. The denotation is [prfn_den : prfn 𝔄 → proph 𝔄].

  ** Interpretation

  [ltype_own k lt r d g tid l] (notation [l ◁ₗ[tid, k, d, g] r @ lt]) is
  indexed by depths [d g], exactly as [ty_gho_own]; blocked places ignore the
  depths and give back the contents at some new depth together with a time
  receipt (like [uniq_payload] and the blocked entries of the type context).
  Borrow kinds ([bor_kind]):
  - [Owned m]: the place is owned. For [OfTy ty] this is [ty_own] at the
    location ([l #↦!∗ ty_phys] and [ty_gho_own]); [m] is the number of laters
    guarding the ghost parts (one per enclosing [own_ptr], as for the
    pointee of [own_ptr]; cf. RefinedRust's [Owned wl]). Blocked
    inheritances are never put under a later, so that they can always be
    fired.
    [Blocked ty κ] holds the inheritance [[†κ] ={⊤}=∗ …] (cf. RefinedRust's
    [blocked_lty_own]).
  - [Uniq κ ξi γ]: the place is the referent of a unique borrow at lifetime
    [κ] with prophecy variable id [ξi] and state ghost name [γ].
    - For [OfTy ty] this is the existing [uniq_body] (plus the persistent
      ghost information of the current value, as in [&uniq]), so that
      [UniqLty (OfTy ty) κ] and [OfTy (&uniq{κ} ty)] are equivalent.
    - For [Blocked ty κ'] the borrow itself is blocked (an inheritance giving
      back the [OfTy ty] borrow), as in RefinedRust.
    - For compound place types, the place is held by a _generalized
      prophetic borrow_ ([proph_idx_bor_gen]) pinned to the core via a state
      ghost variable (instead of RefinedRust's saved-proposition pinned
      borrows). Its body is
        [∃ p r', ⌜pat_ok κ p⌝ ∗ ⌜wπ = (prfn_den r', depths)⌝ ∗
           ghost_var γ ½ (p, r') ∗ ⧖ ∗ ⟨Owned interpretation at shape p⟩]
      where the controller's prophecy [wπ] is the denotation of the current
      refinement. The outside holds the other half [ghost_var γ ½ (p, r)]
      next to the observer [.VO] or the reserved observer [.VOR] (the
      latter is allowed, for reservations of blocked components). Switching
      shapes means opening the borrow and updating both halves
      ([cpd_acc]).

  ** Shapes and the pinned core

  Ghost state cannot contain [Σ]-dependent data (an [lty] contains [type]s,
  which contain [iProp Σ]), so the state cannot literally be the place type.
  Instead, a place type [lt] is interpreted as its core [lty_core lt] (a
  [Σ]-dependent parameter of the borrow body) together with a [Σ]-independent
  _blocking pattern_ [lty_pat lt : lpat] recording which subplaces are
  blocked, and at which lifetime. The interpretation [ltype_own_cp] is
  defined by structural recursion on the core, with the pattern as an
  argument. The body of a compound borrow is built from the interpretations
  of the core's children and quantifies over the pattern, which is agreed on
  through the (discrete, timeless) ghost variable. The membership condition
  is purely syntactic: [pat_ok κ p] says that every blocked lifetime of [p]
  is (as a set of atoms) a superset of [κ], i.e. syntactically of the form
  [κ ⊓ α], so that [[†κ]] directly kills it ([lft_dead_incl]) without the
  mask [↑NllftG].

  ** Core interpretation and unblocking

  [ltype_own_core] interprets blocked leaves as [OfTy]. Places in [Uniq] mode
  (i.e. behind a borrow, including the referent of a nested [UniqLty]) have
  their core enforced by the borrow itself (by [uniq_body] resp. the pinned
  body), so [ltype_own_core] there is permissive (any pattern); blocked
  places behind a nested unique borrow belong to that borrow.
  [imp_unblockable κs lt] says that, once all [κs] are dead, the place can be
  shifted to its core without changing the refinement (cf. RefinedRust's
  [imp_unblockable]); the depth may change and no time receipt is guaranteed
  for the new depth (re-establishing a receipt above an [OwnPtrLty] requires
  a program step, as in RustHornBelt). The lender of a pinned body
  ([cpd_create]) gets back the contents at some shape [p] with [pat_ok κ p],
  and can shift them to the core with [cpd_lender_unblock]. No later credits
  are needed in the body: the observer strips the later from the controller
  and the ghost state is timeless.

  ** Unfolding

  At [Owned m], [ProdLty (OfTy ty1) (OfTy ty2)] is [ltype_eq] to
  [OfTy (prod_ty ty1 ty2)] ([prod_ofty_unfold]); [OwnPtrLty n (OfTy ty)] is
  [ltype_eq] to [OfTy (own_ptr n ty)] at [Owned 0] ([ownptr_ofty_unfold]; at
  [Owned m] folding still holds, [ownptr_ofty_fold_own], but unfolding would
  have to take the pointee's points-to out of [m] laters); and
  [UniqLty (OfTy ty) κ] is equivalent to [OfTy (&uniq{κ} ty)]
  ([uniq_ofty_unfold], [uniq_ofty_fold_own]; up to the depth and index
  components of the [&uniq] value, which are not part of the place
  refinement). These are equivalences, not updates. At [Uniq] mode, only
  _folding_ is possible, as an update that opens the borrow with a lifetime
  guard ([cpd_fold] and its instances [prod_ofty_fold_uniq],
  [ownptr_ofty_fold_uniq], [uniq_ofty_fold_uniq]). Unfolding at [Uniq] mode
  (i.e. replacing the pinned core by a more unfolded one) is not possible in
  this model: it would close an existing borrow, whose lender expects the
  non-lazy old contents (e.g. [uniq_payload]) after the lifetime ends, with a
  body that may later contain blocked subplaces; turning those back into the
  old contents would require firing their inheritances inside the closing
  view shift of the lifetime logic, whose mask ([↑NllftUsr ∪ ↑NllftUsr2])
  excludes [↑Nllft]. (RefinedRust avoids this by putting lazy updates
  [|={lftE}=> …] into all borrow contents, including those of [&mut ty];
  here this would require changing [uniq_bor].) Compound [Uniq]-mode places
  are instead created from [Owned] places, already unfolded ([cpd_create]),
  so that their lender can fire inheritances itself. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From lrust.typing Require Export type.
From lrust.typing Require Import uniq_util uniq_bor own product freeable_util.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅 ℭ: syn_type.

(** * Place refinements *)

Inductive place_rfn (𝔄: syn_type) : Type :=
| PlaceIn (x: ~~𝔄)
| PlaceGhost (x₀: ~~𝔄) (ζi: positive).
Global Arguments PlaceIn {_} _.
Global Arguments PlaceGhost {_} _ _.

(** Structured refinements of compound places. *)
Fixpoint prfn_struct (𝔄: syn_type) : Type :=
  match 𝔄 with
  | uniq_borₛ 𝔅 => cloc * (place_rfn 𝔅 + prfn_struct 𝔅) * positive * gname
  | at_locₛ 𝔅 => loc * (place_rfn 𝔅 + prfn_struct 𝔅)
  | prodₛ 𝔅 ℭ => (place_rfn 𝔅 + prfn_struct 𝔅) * (place_rfn ℭ + prfn_struct ℭ)
  | _ => Empty_set
  end%type.

Definition prfn (𝔄: syn_type) : Type := (place_rfn 𝔄 + prfn_struct 𝔄)%type.

Definition place_rfn_wit {𝔄} (r: place_rfn 𝔄) : ~~𝔄 :=
  match r with PlaceIn x => x | PlaceGhost x₀ _ => x₀ end.

Definition place_rfn_den {𝔄} (r: place_rfn 𝔄) : proph 𝔄 :=
  match r with
  | PlaceIn x => vπ x
  | PlaceGhost x₀ ζi => λ π, (π (uniq_prvar x₀ ζi)).1
  end.

Definition idx_dummy : Idx := (1%positive, ∅).

(** A witness value (only used for inhabitation of prophecy variables). *)
Fixpoint prfn_wit {𝔄} : prfn 𝔄 → ~~𝔄 :=
  match 𝔄 return prfn 𝔄 → ~~𝔄 with
  | uniq_borₛ 𝔅 => λ r, match r with
      | inl lr => place_rfn_wit lr
      | inr (l', r', ξi, _) => (l', prfn_wit r', ξi, 0%nat, 0%nat, idx_dummy)
      end
  | at_locₛ 𝔅 => λ r, match r with
      | inl lr => place_rfn_wit lr
      | inr (l', r') => (l', prfn_wit r')
      end
  | prodₛ 𝔅 ℭ => λ r, match r with
      | inl lr => place_rfn_wit lr
      | inr (r1, r2) => (prfn_wit r1, prfn_wit r2)
      end
  | _ => λ r, match r with inl lr => place_rfn_wit lr | inr e => match e with end end
  end.

(** The denotation of a place refinement. *)
Fixpoint prfn_den {𝔄} : prfn 𝔄 → proph 𝔄 :=
  match 𝔄 return prfn 𝔄 → proph 𝔄 with
  | uniq_borₛ 𝔅 => λ r, match r with
      | inl lr => place_rfn_den lr
      | inr (l', r', ξi, _) => λ π, (prfn_den r' π, (π (uniq_prvar (prfn_wit r') ξi)).1)
      end
  | at_locₛ 𝔅 => λ r, match r with
      | inl lr => place_rfn_den lr
      | inr (l', r') => λ π, (l', prfn_den r' π)
      end
  | prodₛ 𝔅 ℭ => λ r, match r with
      | inl lr => place_rfn_den lr
      | inr (r1, r2) => λ π, (prfn_den r1 π, prfn_den r2 π)
      end
  | _ => λ r, match r with inl lr => place_rfn_den lr | inr e => match e with end end
  end.

Lemma prfn_den_in {𝔄} (x: ~~𝔄) : prfn_den (inl (PlaceIn x)) = vπ x.
Proof. by destruct 𝔄. Qed.

Lemma prfn_wit_in {𝔄} (x: ~~𝔄) : prfn_wit (inl (PlaceIn x)) = x.
Proof. by destruct 𝔄. Qed.

(** * Blocking patterns *)

(** The [Σ]-independent part of a place type: which subplaces are blocked,
    and at which lifetime. *)
Inductive lpat :=
| PatLeaf
| PatBlocked (α: lft)
| PatUniq (p: lpat)
| PatOwn (p: lpat)
| PatProd (p1 p2: lpat).

Global Instance lpat_inhabited : Inhabited lpat := populate PatLeaf.

Definition pat_uniq (p: lpat) : lpat := match p with PatUniq p' => p' | _ => PatLeaf end.
Definition pat_own (p: lpat) : lpat := match p with PatOwn p' => p' | _ => PatLeaf end.
Definition pat_l (p: lpat) : lpat := match p with PatProd p1 _ => p1 | _ => PatLeaf end.
Definition pat_r (p: lpat) : lpat := match p with PatProd _ p2 => p2 | _ => PatLeaf end.

(** The blocked lifetimes of a pattern that have to be dead to get back to
    the core in [Owned] mode. Blocked places behind a nested unique borrow
    (also the borrow's referent itself) are not included: those belong to
    the nested borrow (see [ltype_own_core]). *)
Fixpoint pat_blk_lfts (p: lpat) : list lft :=
  match p with
  | PatLeaf | PatUniq _ => []
  | PatBlocked α => [α]
  | PatOwn p' => pat_blk_lfts p'
  | PatProd p1 p2 => pat_blk_lfts p1 ++ pat_blk_lfts p2
  end.

(** Membership condition of the pinned body of a borrow at lifetime [κ]: all
    blocked lifetimes are syntactically of the form [κ ⊓ α]. *)
Definition pat_ok (κ: lft) (p: lpat) : Prop := ∀ α, α ∈ pat_blk_lfts p → κ ⊆ α.

(** The state of the pinned body of a compound unique borrow. *)
Definition ltype_state : Type := (lpat * {𝔄 : syn_type & prfn 𝔄})%type.

Class ltypeG Σ := LtypeG { #[global] ltype_ghost_varG :: ghost_varG Σ ltype_state }.
Definition ltypeΣ : gFunctors := ghost_varΣ ltype_state.
Global Instance subG_ltypeΣ Σ : subG ltypeΣ Σ → ltypeG Σ.
Proof. intros ?. constructor. by apply subG_ghost_varΣ. Qed.

(** * Borrow kinds *)

Inductive bor_kind :=
| Owned (m: nat)
| Uniq (κ: lft) (ξi: positive) (γ: gname).

(** * Syntax of place types *)

Section lty.
  Context `{!typeG Σ}.

  Inductive lty : syn_type → Type :=
  | OfTy {𝔄} (ty: type 𝔄) : lty 𝔄
  | Blocked {𝔄} (ty: type 𝔄) (κ: lft) : lty 𝔄
  | UniqLty {𝔄} (lt: lty 𝔄) (κ: lft) : lty (uniq_borₛ 𝔄)
  | OwnPtrLty {𝔄} (n: nat) (lt: lty 𝔄) : lty (at_locₛ 𝔄)
  | ProdLty {𝔄 𝔅} (lt1: lty 𝔄) (lt2: lty 𝔅) : lty (𝔄 * 𝔅).

  Fixpoint lty_core {𝔄} (lt: lty 𝔄) : lty 𝔄 :=
    match lt in lty 𝔄 return lty 𝔄 with
    | OfTy ty => OfTy ty
    | Blocked ty _ => OfTy ty
    | UniqLty lt κ => UniqLty (lty_core lt) κ
    | OwnPtrLty n lt => OwnPtrLty n (lty_core lt)
    | ProdLty lt1 lt2 => ProdLty (lty_core lt1) (lty_core lt2)
    end.

  Fixpoint lty_pat {𝔄} (lt: lty 𝔄) : lpat :=
    match lt with
    | OfTy _ => PatLeaf
    | Blocked _ κ => PatBlocked κ
    | UniqLty lt _ => PatUniq (lty_pat lt)
    | OwnPtrLty _ lt => PatOwn (lty_pat lt)
    | ProdLty lt1 lt2 => PatProd (lty_pat lt1) (lty_pat lt2)
    end.

  Fixpoint lty_size {𝔄} (lt: lty 𝔄) : nat :=
    match lt with
    | OfTy ty | Blocked ty _ => ty.(ty_size)
    | UniqLty _ _ | OwnPtrLty _ _ => 1
    | ProdLty lt1 lt2 => lty_size lt1 + lty_size lt2
    end.

  Fixpoint lty_lfts {𝔄} (lt: lty 𝔄) : list lft :=
    match lt with
    | OfTy ty | Blocked ty _ => ty.(ty_lfts)
    | UniqLty lt κ => κ :: lty_lfts lt
    | OwnPtrLty _ lt => lty_lfts lt
    | ProdLty lt1 lt2 => lty_lfts lt1 ++ lty_lfts lt2
    end.

  Definition lty_blocked_lfts {𝔄} (lt: lty 𝔄) : list lft := pat_blk_lfts (lty_pat lt).

  Lemma lty_core_idemp {𝔄} (lt: lty 𝔄) : lty_core (lty_core lt) = lty_core lt.
  Proof. induction lt; simpl; rewrite ?IHlt ?IHlt1 ?IHlt2; done. Qed.

  Lemma lty_size_core {𝔄} (lt: lty 𝔄) : lty_size (lty_core lt) = lty_size lt.
  Proof. induction lt; simpl; rewrite ?IHlt ?IHlt1 ?IHlt2; done. Qed.

  Lemma lty_lfts_core {𝔄} (lt: lty 𝔄) : lty_lfts (lty_core lt) = lty_lfts lt.
  Proof. induction lt; simpl; rewrite ?IHlt ?IHlt1 ?IHlt2; done. Qed.
End lty.

(** * Interpretation *)

Section ltype_own.
  Context `{!typeG Σ, !ltypeG Σ}.

  (** ** Leaves *)

  (** A place of type [OfTy ty] containing the value [x]. *)
  Definition ofty_in {𝔄} (k: bor_kind) (ty: type 𝔄) (x: ~~𝔄) (d g: nat)
      (tid: thread_id) (l: cloc) : iProp Σ :=
    match k with
    | Owned m => l #↦!∗ ty.(ty_phys) x tid ∗ ▷^m ty.(ty_gho_own) x d g tid
    | Uniq κ ξi _ => (∃ idx, uniq_body ty x ξi d g idx κ tid l) ∗
        (basically_dead κ ∨ ▷ ty.(ty_gho_pers) x d g tid)
    end.

  (** The relation between a place refinement and a value. *)
  Definition place_rfn_rel {𝔄} (r: place_rfn 𝔄) (x: ~~𝔄) : iProp Σ :=
    match r with
    | PlaceIn x' => ⌜x = x'⌝
    | PlaceGhost x₀ ζi => ▷ ((λ π, (π (uniq_prvar x₀ ζi)).1) :== vπ x)
    end.

  Definition ofty_own {𝔄} (k: bor_kind) (ty: type 𝔄) (r: place_rfn 𝔄) (d g: nat)
      (tid: thread_id) (l: cloc) : iProp Σ :=
    ∃ x, place_rfn_rel r x ∗ ofty_in k ty x d g tid l.

  Definition blocked_own {𝔄} (k: bor_kind) (ty: type 𝔄) (α: lft) (r: place_rfn 𝔄) (d g: nat)
      (tid: thread_id) (l: cloc) : iProp Σ :=
    [†α] ={⊤}=∗ ∃ x d' g', place_rfn_rel r x ∗ ⧖(S d' `max` g') ∗ ofty_in k ty x d' g' tid l.

  (** [c] selects the core interpretation. *)
  Definition leaf_own {𝔄} (c: bool) (k: bor_kind) (ty: type 𝔄) (p: lpat) (r: prfn 𝔄)
      (d g: nat) (tid: thread_id) (l: cloc) : iProp Σ :=
    match r with
    | inr _ => False
    | inl lr =>
        match p with
        | PatBlocked α => if c then ofty_own k ty lr d g tid l else blocked_own k ty α lr d g tid l
        | _ => ofty_own k ty lr d g tid l
        end
    end.

  (** ** Nodes in [Owned] mode, given the interpretations of the children *)

  Definition uniq_node {𝔅} (m: nat) (κ': lft) (lfts: list lft)
      (child: positive → gname → prfn 𝔅 → nat → nat → thread_id → cloc → iProp Σ)
      (r: prfn (uniq_borₛ 𝔅)) (d g: nat) (tid: thread_id) (l: cloc) : iProp Σ :=
    match r with
    | inl _ => False
    | inr (l', r', ξi, γ) =>
        l #↦!∗ [FVal (LitV l'.1)] ∗
        ▷^m (κ' ⊑ lft_intersect_list lfts ∗ (@[κ'] &&{↑NllftG; g+1}&&> l' #↦∗_) ∗
          ∃ d' g', ⌜S d' ≤ d ∧ g' ≤ g⌝ ∗ child ξi γ r' d' g' tid l')
    end.

  Definition own_node {𝔅} (m: nat) (n sz: nat)
      (child: prfn 𝔅 → nat → nat → thread_id → cloc → iProp Σ)
      (r: prfn (at_locₛ 𝔅)) (d g: nat) (tid: thread_id) (l: cloc) : iProp Σ :=
    match r with
    | inl _ => False
    | inr (l', r') =>
        l #↦!∗ [FVal (LitV l')] ∗ ▷^m (⌜d ≠ 0%nat⌝ ∗ freeable_sz n sz l') ∗
        child r' (pred d) g tid (l', repeat [] sz)
    end.

  Definition prod_node {𝔅 ℭ} (sz1: nat)
      (c1: prfn 𝔅 → nat → nat → thread_id → cloc → iProp Σ)
      (c2: prfn ℭ → nat → nat → thread_id → cloc → iProp Σ)
      (r: prfn (𝔅 * ℭ)) (d g: nat) (tid: thread_id) (l: cloc) : iProp Σ :=
    match r with
    | inl _ => False
    | inr (r1, r2) => c1 r1 d g tid (cloc_take l sz1) ∗ c2 r2 d g tid (cloc_skip l sz1)
    end.

  (** ** Compound places in [Uniq] mode *)

  (** The observer: unreserved or reserved. *)
  Definition uniq_obs (ξ: proph_var) (c: pv_val ξ) (idx: Idx) : iProp Σ :=
    proph_bor_tok ξ c idx ∨ ∃ ζl, proph_bor_tok_rsv ξ c idx ζl.

  (** The pinned body. [node] is the [Owned] interpretation of the (fixed)
      core at a given pattern. *)
  (* The prophecy variable [uniq_prvar x₀ ξi] does not depend on the witness
     [x₀] ([uniq_prvar_irrel]); the value stored in the observer is not
     meaningful except for the depths. *)
  Definition cpd_body {𝔄} (κ: lft) (γ: gname)
      (node: lpat → prfn 𝔄 → nat → nat → thread_id → cloc → iProp Σ)
      (tid: thread_id) (l: cloc)
      (c: ~~ (uniq_cellₛ 𝔄)) (wπ: proph (uniq_cellₛ 𝔄)) : iProp Σ :=
    ∃ (p: lpat) (r: prfn 𝔄), ⌜pat_ok κ p⌝ ∗ ⌜wπ = λ π, (prfn_den r π, c.2)⌝ ∗
      ghost_var γ (1/2) ((p, existT 𝔄 r) : ltype_state) ∗
      ⧖(S (dec_depth c.2.1) `max` dec_depth c.2.2) ∗
      node p r (dec_depth c.2.1) (dec_depth c.2.2) tid l.

  Definition cpd_own {𝔄} (κ: lft) (ξi: positive) (γ: gname) (p: lpat)
      (node: lpat → prfn 𝔄 → nat → nat → thread_id → cloc → iProp Σ)
      (r: prfn 𝔄) (d g: nat) (tid: thread_id) (l: cloc) : iProp Σ :=
    ∃ (x₀: ~~𝔄) (idx: Idx),
      uniq_obs (uniq_prvar x₀ ξi) (uniq_cell x₀ d g) idx ∗
      ghost_var γ (1/2) ((p, existT 𝔄 r) : ltype_state) ∗ ⧗1 ∗
      proph_idx_bor_gen κ (uniq_prvar x₀ ξi) idx (cpd_body κ γ node tid l).

  (** ** The interpretation

      By structural recursion on the place type, with the blocking pattern
      as an argument (only the core of the place type matters). *)
  Fixpoint ltype_own_cp (c: bool) {𝔄} (lt: lty 𝔄) {struct lt} :
      bor_kind → lpat → prfn 𝔄 → nat → nat → thread_id → cloc → iProp Σ :=
    match lt in lty 𝔄 return bor_kind → lpat → prfn 𝔄 → nat → nat → thread_id → cloc → iProp Σ with
    | OfTy ty => λ k p, leaf_own c k ty p
    | Blocked ty _ => λ k p, leaf_own c k ty p
    | UniqLty lt' κ' => λ k p,
        match k with
        | Owned m => uniq_node m κ' (lty_lfts lt') (λ ξi γ r' d' g' tid l',
            if c then (∃ p', ltype_own_cp false lt' (Uniq κ' ξi γ) p' r' d' g' tid l')%I
            else ltype_own_cp false lt' (Uniq κ' ξi γ) (pat_uniq p) r' d' g' tid l')
        | Uniq κ ξi γ => cpd_own κ ξi γ p (λ p', uniq_node 0 κ' (lty_lfts lt')
            (λ ξi' γ', ltype_own_cp false lt' (Uniq κ' ξi' γ') (pat_uniq p')))
        end
    | OwnPtrLty n lt' => λ k p,
        match k with
        | Owned m => own_node m n (lty_size lt') (ltype_own_cp c lt' (Owned (m + 1)) (pat_own p))
        | Uniq κ ξi γ => cpd_own κ ξi γ p (λ p', own_node 0 n (lty_size lt')
            (ltype_own_cp false lt' (Owned (0 + 1)) (pat_own p')))
        end
    | ProdLty lt1 lt2 => λ k p,
        match k with
        | Owned m => prod_node (lty_size lt1) (ltype_own_cp c lt1 (Owned m) (pat_l p))
            (ltype_own_cp c lt2 (Owned m) (pat_r p))
        | Uniq κ ξi γ => cpd_own κ ξi γ p (λ p', prod_node (lty_size lt1)
            (ltype_own_cp false lt1 (Owned 0) (pat_l p'))
            (ltype_own_cp false lt2 (Owned 0) (pat_r p')))
        end
    end.

  Definition ltype_own (k: bor_kind) {𝔄} (lt: lty 𝔄) (r: prfn 𝔄) (d g: nat)
      (tid: thread_id) (l: cloc) : iProp Σ :=
    ltype_own_cp false lt k (lty_pat lt) r d g tid l.

  (** The core interpretation. *)
  Definition ltype_own_core (k: bor_kind) {𝔄} (lt: lty 𝔄) (r: prfn 𝔄) (d g: nat)
      (tid: thread_id) (l: cloc) : iProp Σ :=
    match k with
    | Owned _ => ltype_own_cp true lt k (lty_pat lt) r d g tid l
    | Uniq _ _ _ => ∃ p, ltype_own_cp false lt k p r d g tid l
    end.
End ltype_own.

Notation "l ◁ₗ[ tid , k , d , g ] r @ lt" := (ltype_own k lt r d g tid l)
  (at level 70, format "l  ◁ₗ[ tid ,  k ,  d ,  g ]  r  @  lt") : bi_scope.

(** * Laws *)

Section ltype_lemmas.
  Context `{!typeG Σ, !ltypeG Σ}.
  Implicit Type (κ α: lft).

  (** ** Monotonicity of the nodes in their children *)

  Lemma uniq_node_mono {𝔅} m κ' lfts
      (c1 c2: positive → gname → prfn 𝔅 → nat → nat → thread_id → cloc → iProp Σ) r d g tid l :
    (∀ ξi γ r' d' g' tid' l', c1 ξi γ r' d' g' tid' l' ⊢ c2 ξi γ r' d' g' tid' l') →
    uniq_node m κ' lfts c1 r d g tid l ⊢ uniq_node m κ' lfts c2 r d g tid l.
  Proof.
    intros Hc. destruct r as [?|[[[l' r'] ξi] γ]]; [done|]. rewrite /uniq_node.
    iIntros "[$ H]". iNext. iDestruct "H" as "($ & $ & %d' & %g' & ? & C)".
    iExists d', g'. iFrame. by iApply Hc.
  Qed.

  Lemma own_node_mono {𝔅} m n sz (c1 c2: prfn 𝔅 → nat → nat → thread_id → cloc → iProp Σ)
      r d g tid l :
    (∀ r' d' g' tid' l', c1 r' d' g' tid' l' ⊢ c2 r' d' g' tid' l') →
    own_node m n sz c1 r d g tid l ⊢ own_node m n sz c2 r d g tid l.
  Proof.
    intros Hc. destruct r as [?|[l' r']]; [done|]. rewrite /own_node.
    iIntros "($ & $ & C)". by iApply Hc.
  Qed.

  Lemma prod_node_mono {𝔅 ℭ} sz1 (c1 c1': prfn 𝔅 → nat → nat → thread_id → cloc → iProp Σ)
      (c2 c2': prfn ℭ → nat → nat → thread_id → cloc → iProp Σ) r d g tid l :
    (∀ r' d' g' tid' l', c1 r' d' g' tid' l' ⊢ c1' r' d' g' tid' l') →
    (∀ r' d' g' tid' l', c2 r' d' g' tid' l' ⊢ c2' r' d' g' tid' l') →
    prod_node sz1 c1 c2 r d g tid l ⊢ prod_node sz1 c1' c2' r d g tid l.
  Proof.
    intros H1 H2. destruct r as [?|[r1 r2]]; [done|]. rewrite /prod_node.
    iIntros "[A B]". iSplitL "A"; [by iApply H1|by iApply H2].
  Qed.

  (** ** The core *)

  (** Only the core of a place type matters for [ltype_own_cp]. *)
  Lemma ltype_own_cp_core c {𝔄} (lt: lty 𝔄) : ltype_own_cp c (lty_core lt) = ltype_own_cp c lt.
  Proof.
    induction lt as [| |𝔄 lt IH κ|𝔄 n lt IH|𝔄 𝔅 lt1 IH1 lt2 IH2] in c |- *; simpl; [done|done| | |].
    - by rewrite lty_lfts_core !IH.
    - by rewrite lty_size_core !IH.
    - by rewrite lty_size_core !IH1 !IH2.
  Qed.

  (** In [Owned] mode, the core interpretation does not depend on the
      pattern. *)
  Lemma ltype_own_cp_true_owned_pat {𝔄} (lt: lty 𝔄) m p p' r d g tid l :
    ltype_own_cp true lt (Owned m) p r d g tid l ⊢ ltype_own_cp true lt (Owned m) p' r d g tid l.
  Proof.
    induction lt as [𝔄 ty|𝔄 ty α|𝔄 lt IH κ|𝔄 n lt IH|𝔄 𝔅 lt1 IH1 lt2 IH2]
      in m, p, p', r, d, g, tid, l |- *; simpl.
    - destruct r as [lr|]; [|done]. by destruct p, p'.
    - destruct r as [lr|]; [|done]. by destruct p, p'.
    - by apply uniq_node_mono.
    - apply own_node_mono=> *. apply IH.
    - apply prod_node_mono=> *; [apply IH1|apply IH2].
  Qed.

  (** Core idempotence. *)
  Lemma ltype_own_core_idemp k {𝔄} (lt: lty 𝔄) r d g tid l :
    ltype_own_core k (lty_core lt) r d g tid l ⊣⊢ ltype_own_core k lt r d g tid l.
  Proof.
    destruct k as [m|κ ξi γ]; rewrite /ltype_own_core ltype_own_cp_core; [|done].
    iSplit; iApply ltype_own_cp_true_owned_pat.
  Qed.

  (** In [Uniq] mode, the core is enforced by the borrow itself. *)
  Lemma ltype_own_uniq_core {𝔄} κ ξi γ (lt: lty 𝔄) r d g tid l :
    ltype_own (Uniq κ ξi γ) lt r d g tid l ⊢ ltype_own_core (Uniq κ ξi γ) lt r d g tid l.
  Proof. iIntros "H". by iExists (lty_pat lt). Qed.

  (** ** Depth monotonicity in [Owned] mode *)

  Lemma leaf_own_owned_depth_mono c {𝔄} (ty: type 𝔄) m p r d g d' g' tid l :
    d ≤ d' → g ≤ g' →
    leaf_own c (Owned m) ty p r d g tid l ⊢ leaf_own c (Owned m) ty p r d' g' tid l.
  Proof.
    intros ??. destruct r as [lr|]; [|done].
    have Hofty: ofty_own (Owned m) ty lr d g tid l ⊢ ofty_own (Owned m) ty lr d' g' tid l.
    { iIntros "(%x & Rel & Pt & Gho)". iExists x. iFrame. iNext.
      iDestruct (ty_gho_own_depth_mono _ d g d' g' with "Gho") as "[$ _]"; done. }
    destruct p; try apply Hofty. destruct c; [apply Hofty|]. rewrite /leaf_own /blocked_own.
    iIntros "$".
  Qed.

  Lemma ltype_own_cp_owned_depth_mono c {𝔄} (lt: lty 𝔄) m p r d g d' g' tid l :
    d ≤ d' → g ≤ g' →
    ltype_own_cp c lt (Owned m) p r d g tid l ⊢ ltype_own_cp c lt (Owned m) p r d' g' tid l.
  Proof.
    induction lt as [𝔄 ty|𝔄 ty α|𝔄 lt IH κ|𝔄 n lt IH|𝔄 𝔅 lt1 IH1 lt2 IH2]
      in m, p, r, d, g, d', g', tid, l |- *; intros Hd Hg; simpl.
    - by apply leaf_own_owned_depth_mono.
    - by apply leaf_own_owned_depth_mono.
    - destruct r as [?|[[[l' r'] ξi] γ]]; [done|]. rewrite /uniq_node.
      iIntros "[$ H]". iNext. iDestruct "H" as "($ & #G & %d1 & %g1 & %Hle & C)".
      iSplitR. { iApply (lguards_weaken_later with "G"). lia. }
      iExists d1, g1. iFrame. iPureIntro. lia.
    - destruct r as [?|[l' r']]; [done|]. rewrite /own_node.
      iIntros "($ & H & C)". iSplitL "H".
      { iNext. iDestruct "H" as "[% $]". iPureIntro. lia. }
      iApply (IH with "C"); lia.
    - destruct r as [?|[r1 r2]]; [done|]. rewrite /prod_node.
      iIntros "[A B]". iSplitL "A"; [iApply (IH1 with "A")|iApply (IH2 with "B")]; done.
  Qed.

  Lemma ltype_own_core_owned_depth_mono {𝔄} (lt: lty 𝔄) m r d g d' g' tid l :
    d ≤ d' → g ≤ g' →
    ltype_own_core (Owned m) lt r d g tid l ⊢ ltype_own_core (Owned m) lt r d' g' tid l.
  Proof. apply ltype_own_cp_owned_depth_mono. Qed.

  Lemma ltype_own_owned_depth_mono {𝔄} (lt: lty 𝔄) m r d g d' g' tid l :
    d ≤ d' → g ≤ g' →
    ltype_own (Owned m) lt r d g tid l ⊢ ltype_own (Owned m) lt r d' g' tid l.
  Proof. apply ltype_own_cp_owned_depth_mono. Qed.

  (** ** Unblocking *)

  Definition lft_dead_list (κs: list lft) : iProp Σ := [∗ list] κ ∈ κs, [†κ].
  Global Instance lft_dead_list_persistent κs : Persistent (lft_dead_list κs) := _.

  Lemma lft_dead_list_app κs κs' :
    lft_dead_list (κs ++ κs') ⊣⊢ lft_dead_list κs ∗ lft_dead_list κs'.
  Proof. apply big_sepL_app. Qed.

  (** The membership condition [pat_ok] ensures that blocked lifetimes die
      with the borrow (without the mask [↑NllftG]). *)
  Lemma lft_dead_incl κ α : κ ⊆ α → [†κ] ⊢ [†α].
  Proof.
    intros Hsub. have ->: α = κ ⊓ α.
    { unfold meet, llft_intersect. set_solver. }
    rewrite llftl_end_inter. iIntros "$".
  Qed.

  Lemma pat_ok_dead κ p : pat_ok κ p → [†κ] ⊢ lft_dead_list (pat_blk_lfts p).
  Proof.
    iIntros (Hok) "#†κ". rewrite /lft_dead_list. iApply big_sepL_intro.
    iIntros "!>" (i α Hi). iApply (lft_dead_incl with "†κ").
    apply Hok. by eapply elem_of_list_lookup_2.
  Qed.

  (** Implicit unblocking (cf. RefinedRust's [imp_unblockable]): once all
      [κs] are dead, a place can be shifted to its core, without changing
      the refinement. The depth may change. *)
  Definition imp_unblockable (κs: list lft) {𝔄} (lt: lty 𝔄) : iProp Σ :=
    □ ∀ k r d g tid l, lft_dead_list κs -∗ ltype_own k lt r d g tid l ={⊤}=∗
        ∃ d' g', ltype_own_core k lt r d' g' tid l.
  Global Instance imp_unblockable_persistent κs {𝔄} (lt: lty 𝔄) :
    Persistent (imp_unblockable κs lt) := _.

  Lemma imp_unblockable_shorten κs κs' {𝔄} (lt: lty 𝔄) :
    □ (lft_dead_list κs ={⊤}=∗ lft_dead_list κs') -∗
    imp_unblockable κs' lt -∗ imp_unblockable κs lt.
  Proof.
    iIntros "#Hκ #Ub !>" (k r d g tid l) "Dead H".
    iMod ("Hκ" with "Dead") as "Dead'". iApply ("Ub" with "Dead' H").
  Qed.

  Lemma ofty_imp_unblockable κs {𝔄} (ty: type 𝔄) : ⊢ imp_unblockable κs (OfTy ty).
  Proof.
    iIntros "!>" (k r d g tid l) "_ H". iModIntro. iExists d, g.
    destruct k as [m|κ ξi γ]; [|by iApply ltype_own_uniq_core]. done.
  Qed.

  Lemma blocked_imp_unblockable {𝔄} (ty: type 𝔄) α : ⊢ imp_unblockable [α] (Blocked ty α).
  Proof.
    iIntros "!>" (k r d g tid l) "[#Dead _] H".
    destruct k as [m|κ ξi γ]; [|iModIntro; iExists d, g; by iApply ltype_own_uniq_core].
    destruct r as [lr|]; [|done]. rewrite /ltype_own /ltype_own_core /=.
    iMod ("H" with "Dead") as (x d' g') "(Rel & _ & In)". iModIntro.
    iExists d', g', x. iFrame.
  Qed.

  (** Congruence. Unique borrows are trivially unblockable, as blocked
      places behind a nested borrow belong to that borrow. *)
  Lemma uniq_ltype_imp_unblockable κs {𝔄} (lt: lty 𝔄) κ' :
    ⊢ imp_unblockable κs (UniqLty lt κ').
  Proof.
    iIntros "!>" (k r d g tid l) "_ H". iModIntro. iExists d, g.
    destruct k as [m|κ ξi γ]; [|by iApply ltype_own_uniq_core].
    rewrite /ltype_own /ltype_own_core /=. iApply (uniq_node_mono with "H").
    iIntros (ξi γ r' d' g' tid' l') "H". by iExists _.
  Qed.

  Lemma ownptr_ltype_imp_unblockable κs {𝔄} n (lt: lty 𝔄) :
    imp_unblockable κs lt -∗ imp_unblockable κs (OwnPtrLty n lt).
  Proof.
    iIntros "#Ub !>" (k r d g tid l) "#Dead H".
    destruct k as [m|κ ξi γ]; [|iModIntro; iExists d, g; by iApply ltype_own_uniq_core].
    destruct r as [?|[l' r']]; [done|]. rewrite /ltype_own /ltype_own_core /=.
    iDestruct "H" as "(Pt & Fr & C)".
    iMod ("Ub" $! (Owned (m + 1)) with "Dead C") as (d1 g1) "C". iModIntro.
    iExists (S d1), g1. iFrame. iNext. iDestruct "Fr" as "[_ $]". done.
  Qed.

  Lemma prod_ltype_imp_unblockable κs {𝔄 𝔅} (lt1: lty 𝔄) (lt2: lty 𝔅) :
    imp_unblockable κs lt1 -∗ imp_unblockable κs lt2 -∗ imp_unblockable κs (ProdLty lt1 lt2).
  Proof.
    iIntros "#Ub1 #Ub2 !>" (k r d g tid l) "#Dead H".
    destruct k as [m|κ ξi γ]; [|iModIntro; iExists d, g; by iApply ltype_own_uniq_core].
    destruct r as [?|[r1 r2]]; [done|]. rewrite /ltype_own /ltype_own_core /=.
    iDestruct "H" as "[H1 H2]".
    iMod ("Ub1" $! (Owned m) with "Dead H1") as (d1 g1) "H1".
    iMod ("Ub2" $! (Owned m) with "Dead H2") as (d2 g2) "H2".
    iModIntro. iExists (d1 `max` d2), (g1 `max` g2). iSplitL "H1".
    - iApply (ltype_own_core_owned_depth_mono with "H1"); lia.
    - iApply (ltype_own_core_owned_depth_mono with "H2"); lia.
  Qed.

  Lemma imp_unblockable_blocked_dead {𝔄} (lt: lty 𝔄) :
    ⊢ imp_unblockable (lty_blocked_lfts lt) lt.
  Proof.
    induction lt as [𝔄 ty|𝔄 ty α|𝔄 lt IH κ|𝔄 n lt IH|𝔄 𝔅 lt1 IH1 lt2 IH2];
      rewrite /lty_blocked_lfts /=.
    - iApply ofty_imp_unblockable.
    - iApply blocked_imp_unblockable.
    - iApply uniq_ltype_imp_unblockable.
    - iApply ownptr_ltype_imp_unblockable. iApply IH.
    - iApply prod_ltype_imp_unblockable.
      + iApply imp_unblockable_shorten; [|iApply IH1].
        iIntros "!> Dead". rewrite lft_dead_list_app. by iDestruct "Dead" as "[$ _]".
      + iApply imp_unblockable_shorten; [|iApply IH2].
        iIntros "!> Dead". rewrite lft_dead_list_app. by iDestruct "Dead" as "[_ $]".
  Qed.

  (** Explicit unblocking of a blocked place, in both modes. *)
  Lemma unblock_blocked k {𝔄} (ty: type 𝔄) α r d g tid l :
    [†α] -∗ ltype_own k (Blocked ty α) r d g tid l ={⊤}=∗
      ∃ d' g', ⧖(S d' `max` g') ∗ ltype_own k (OfTy ty) r d' g' tid l.
  Proof.
    iIntros "Dead H". destruct r as [lr|]; [|done]. rewrite /ltype_own /=.
    iMod ("H" with "Dead") as (x d' g') "(Rel & ⧖ & In)". iModIntro.
    iExists d', g'. iFrame "⧖". iExists x. iFrame.
  Qed.
End ltype_lemmas.

(** * Inclusion and equality of place types *)

Section ltype_incl.
  Context `{!typeG Σ, !ltypeG Σ}.

  Definition ltype_incl' (k: bor_kind) {𝔄} (r1 r2: prfn 𝔄) (lt1 lt2: lty 𝔄) : iProp Σ :=
    □ ∀ d g tid l,
      match k with
      | Owned _ => ltype_own k lt1 r1 d g tid l ={⊤}=∗ ltype_own k lt2 r2 d g tid l
      | Uniq _ _ _ => ltype_own k lt1 r1 d g tid l -∗ ltype_own k lt2 r2 d g tid l
      end.

  Definition ltype_incl'_core (k: bor_kind) {𝔄} (r1 r2: prfn 𝔄) (lt1 lt2: lty 𝔄) : iProp Σ :=
    □ ∀ d g tid l,
      match k with
      | Owned _ => ltype_own_core k lt1 r1 d g tid l ={⊤}=∗ ltype_own_core k lt2 r2 d g tid l
      | Uniq _ _ _ => ltype_own_core k lt1 r1 d g tid l -∗ ltype_own_core k lt2 r2 d g tid l
      end.

  (** As in RefinedRust, inclusion also requires inclusion of the cores. In
      addition, the denotations of the refinements must agree. *)
  Definition ltype_incl (k: bor_kind) {𝔄} (r1 r2: prfn 𝔄) (lt1 lt2: lty 𝔄) : iProp Σ :=
    ⌜lty_size lt1 = lty_size lt2 ∧ prfn_den r1 = prfn_den r2⌝ ∗
    ltype_incl' k r1 r2 lt1 lt2 ∗ ltype_incl'_core k r1 r2 lt1 lt2.

  Definition ltype_eq (k: bor_kind) {𝔄} (r1 r2: prfn 𝔄) (lt1 lt2: lty 𝔄) : iProp Σ :=
    ltype_incl k r1 r2 lt1 lt2 ∗ ltype_incl k r2 r1 lt2 lt1.

  Global Instance ltype_incl_persistent k {𝔄} (r1 r2: prfn 𝔄) lt1 lt2 :
    Persistent (ltype_incl k r1 r2 lt1 lt2).
  Proof. destruct k; apply _. Qed.
  Global Instance ltype_eq_persistent k {𝔄} (r1 r2: prfn 𝔄) lt1 lt2 :
    Persistent (ltype_eq k r1 r2 lt1 lt2) := _.

  Lemma ltype_incl_refl k {𝔄} (r: prfn 𝔄) (lt: lty 𝔄) : ⊢ ltype_incl k r r lt lt.
  Proof.
    iSplit; [done|]. iSplit; iIntros "!>" (d g tid l); destruct k; by iIntros "$".
  Qed.

  Lemma ltype_eq_refl k {𝔄} (r: prfn 𝔄) (lt: lty 𝔄) : ⊢ ltype_eq k r r lt lt.
  Proof. iSplit; iApply ltype_incl_refl. Qed.

  Lemma ltype_eq_sym k {𝔄} (r1 r2: prfn 𝔄) (lt1 lt2: lty 𝔄) :
    ltype_eq k r1 r2 lt1 lt2 ⊢ ltype_eq k r2 r1 lt2 lt1.
  Proof. iIntros "[$ $]". Qed.
End ltype_incl.

(** * Unfolding equations *)

Section unfold.
  Context `{!typeG Σ, !ltypeG Σ}.

  (** ** Products *)

  Lemma prod_ofty_unfold_own m {𝔄 𝔅} (ty1: type 𝔄) (ty2: type 𝔅) x1 x2 d g tid l :
    ltype_own (Owned m) (ProdLty (OfTy ty1) (OfTy ty2))
      (inr (inl (PlaceIn x1), inl (PlaceIn x2))) d g tid l ⊣⊢
    ltype_own (Owned m) (OfTy (prod_ty ty1 ty2)) (inl (PlaceIn (𝔄:=𝔄 * 𝔅) (x1, x2))) d g tid l.
  Proof.
    rewrite /ltype_own /= /ofty_own /=. iSplit.
    - iIntros "[(%y1 & -> & Pt1 & Gho1) (%y2 & -> & Pt2 & Gho2)]". iExists (x1, x2).
      iSplit; [done|]. rewrite heap_cloc_mapsto_fancy_vec_app ty_size_eq. by iFrame.
    - iIntros "(%y & -> & Pt & Gho)". rewrite heap_cloc_mapsto_fancy_vec_app ty_size_eq.
      iDestruct "Pt" as "[Pt1 Pt2]". iDestruct "Gho" as "[Gho1 Gho2]".
      iSplitL "Pt1 Gho1"; [iExists x1|iExists x2]; by iFrame.
  Qed.

  Lemma prod_ofty_unfold_core m {𝔄 𝔅} (ty1: type 𝔄) (ty2: type 𝔅) x1 x2 d g tid l :
    ltype_own_core (Owned m) (ProdLty (OfTy ty1) (OfTy ty2))
      (inr (inl (PlaceIn x1), inl (PlaceIn x2))) d g tid l ⊣⊢
    ltype_own_core (Owned m) (OfTy (prod_ty ty1 ty2)) (inl (PlaceIn (𝔄:=𝔄 * 𝔅) (x1, x2))) d g tid l.
  Proof. apply (prod_ofty_unfold_own m). Qed.

  Lemma prod_ofty_unfold m {𝔄 𝔅} (ty1: type 𝔄) (ty2: type 𝔅) (x1: ~~𝔄) (x2: ~~𝔅) :
    ⊢ ltype_eq (Owned m) (inr (inl (PlaceIn x1), inl (PlaceIn x2)) : prfn (𝔄 * 𝔅))
        (inl (PlaceIn (𝔄:=𝔄 * 𝔅) (x1, x2)))
        (ProdLty (OfTy ty1) (OfTy ty2)) (OfTy (prod_ty ty1 ty2)).
  Proof.
    iSplit; (iSplit; [iPureIntro; split; [done|by rewrite /= !prfn_den_in]|]);
      iSplit; iIntros "!>" (d g tid l) "H"; iModIntro;
      by [iApply prod_ofty_unfold_own|iApply prod_ofty_unfold_core|
          iApply (prod_ofty_unfold_own with "H")|iApply (prod_ofty_unfold_core with "H")].
  Qed.

  (** ** Owned pointers *)

  Lemma ownptr_ofty_fold_own m {𝔄} n (ty: type 𝔄) l' x d g tid l :
    ltype_own (Owned m) (OwnPtrLty n (OfTy ty)) (inr (l', inl (PlaceIn x))) d g tid l ⊢
    ltype_own (Owned m) (OfTy (own_ptr n ty)) (inl (PlaceIn (𝔄:=at_locₛ 𝔄) (l', x))) d g tid l.
  Proof.
    rewrite /ltype_own /= /ofty_own /=.
    iIntros "(Pt & Fr & %y & -> & Pt' & Gho)". iExists (l', x). iSplit; [done|]. iFrame "Pt".
    iNext. iDestruct "Fr" as "[% Fr]". destruct d as [|d]; [done|]. simpl.
    rewrite (heap_cloc_mapsto_fancy_empty l' (ty_phys ty x tid)) ty_size_eq. iFrame.
  Qed.

  Lemma ownptr_ofty_unfold_own {𝔄} n (ty: type 𝔄) l' x d g tid l :
    ltype_own (Owned 0) (OfTy (own_ptr n ty)) (inl (PlaceIn (𝔄:=at_locₛ 𝔄) (l', x))) d g tid l ⊢
    ltype_own (Owned 0) (OwnPtrLty n (OfTy ty)) (inr (l', inl (PlaceIn x))) d g tid l.
  Proof.
    rewrite /ltype_own /= /ofty_own /=.
    iIntros "(%v & -> & Pt & H)". destruct d as [|d]; [done|]. simpl.
    iDestruct "H" as "(Pt' & Fr & Gho)".
    iEval (rewrite (heap_cloc_mapsto_fancy_empty l' (ty_phys ty x tid)) ty_size_eq) in "Pt'".
    iFrame "Pt Fr". iSplit; [done|]. iExists x. iSplit; [done|]. iFrame.
  Qed.

  Lemma ownptr_ofty_unfold {𝔄} n (ty: type 𝔄) l' (x: ~~𝔄) :
    ⊢ ltype_eq (Owned 0) (inr (l', inl (PlaceIn x)) : prfn (at_locₛ 𝔄))
        (inl (PlaceIn (𝔄:=at_locₛ 𝔄) (l', x))) (OwnPtrLty n (OfTy ty)) (OfTy (own_ptr n ty)).
  Proof.
    iSplit; (iSplit; [iPureIntro; split; [done|by rewrite /= !prfn_den_in]|]);
      iSplit; iIntros "!>" (d g tid l) "H"; iModIntro.
    - by iApply ownptr_ofty_fold_own.
    - by iApply (ownptr_ofty_fold_own with "H").
    - by iApply ownptr_ofty_unfold_own.
    - by iApply (ownptr_ofty_unfold_own with "H").
  Qed.

  (** ** Unique borrows

      [UniqLty (OfTy ty) κ] is equivalent to [OfTy (&uniq{κ} ty)], up to the
      depths and the borrow index stored in the [&uniq] value (which the
      place refinement does not contain, since they change when the borrow
      is reborrowed). The ghost name [γ] is irrelevant here. *)

  Lemma uniq_ofty_den {𝔄} (l': cloc) (x: ~~𝔄) ξi d' g' idx γ :
    prfn_den (inl (PlaceIn (𝔄:=uniq_borₛ 𝔄) (l', x, ξi, d', g', idx)) : prfn (uniq_borₛ 𝔄)) =
    prfn_den (inr (l', inl (PlaceIn x), ξi, γ) : prfn (uniq_borₛ 𝔄)).
  Proof. rewrite /= prfn_den_in prfn_wit_in. done. Qed.

  Lemma uniq_ofty_unfold_own m {𝔄} (ty: type 𝔄) κ l' x ξi d' g' idx γ d g tid l :
    ltype_own (Owned m) (OfTy (&uniq{κ} ty)) (inl (PlaceIn (𝔄:=uniq_borₛ 𝔄) (l', x, ξi, d', g', idx))) d g tid l ⊢
    ltype_own (Owned m) (UniqLty (OfTy ty) κ) (inr (l', inl (PlaceIn x), ξi, γ)) d g tid l.
  Proof.
    rewrite /ltype_own /= /ofty_own /=.
    iIntros "(%v & -> & Pt & Gho)". iFrame "Pt". iNext.
    iDestruct "Gho" as "(#Incl & %Hle & Body & #G & Pers)".
    iSplitR; [done|]. iSplitR; [done|].
    iExists d', g'. iSplit; [done|]. iExists x. iSplit; [done|].
    iSplitL "Body"; [by iExists idx|]. done.
  Qed.

  Lemma uniq_ofty_fold_own m {𝔄} (ty: type 𝔄) κ l' x ξi γ d g tid l :
    ltype_own (Owned m) (UniqLty (OfTy ty) κ) (inr (l', inl (PlaceIn x), ξi, γ)) d g tid l ⊢
    ∃ d' g' idx,
      ltype_own (Owned m) (OfTy (&uniq{κ} ty)) (inl (PlaceIn (𝔄:=uniq_borₛ 𝔄) (l', x, ξi, d', g', idx))) d g tid l.
  Proof.
    rewrite /ltype_own /= /ofty_own /=.
    have ?: Inhabited (~~𝔄) := populate x. have ?: Inhabited Idx := populate idx_dummy.
    iIntros "[Pt H]".
    iDestruct "H" as "(Incl & G & %d' & %g' & Hle & %y & Hy & (%idx & Body) & Pers)".
    iExists d', g', idx, _. iSplit; [done|]. iFrame "Pt". iNext.
    iDestruct "Hy" as %->. iFrame.
  Qed.

  Lemma uniq_ofty_unfold_core m {𝔄} (ty: type 𝔄) κ l' x ξi d' g' idx γ d g tid l :
    ltype_own_core (Owned m) (OfTy (&uniq{κ} ty)) (inl (PlaceIn (𝔄:=uniq_borₛ 𝔄) (l', x, ξi, d', g', idx))) d g tid l ⊢
    ltype_own_core (Owned m) (UniqLty (OfTy ty) κ) (inr (l', inl (PlaceIn x), ξi, γ)) d g tid l.
  Proof.
    iIntros "H". iDestruct (uniq_ofty_unfold_own _ _ _ _ _ _ _ _ _ γ with "H") as "H".
    iApply (uniq_node_mono with "H"). iIntros (?????? l'') "H". by iExists _.
  Qed.

  Lemma uniq_ofty_unfold m {𝔄} (ty: type 𝔄) κ l' (x: ~~𝔄) ξi d' g' idx γ :
    ⊢ ltype_incl (Owned m) (inl (PlaceIn (𝔄:=uniq_borₛ 𝔄) (l', x, ξi, d', g', idx)))
        (inr (l', inl (PlaceIn x), ξi, γ) : prfn (uniq_borₛ 𝔄))
        (OfTy (&uniq{κ} ty)) (UniqLty (OfTy ty) κ).
  Proof.
    iSplit; [iPureIntro; split; [done|apply uniq_ofty_den]|].
    iSplit; iIntros "!>" (d g tid l) "H"; iModIntro;
      [iApply (uniq_ofty_unfold_own with "H")|iApply (uniq_ofty_unfold_core with "H")].
  Qed.
End unfold.

(** * Compound places in [Uniq] mode *)

Section cpd.
  Context `{!typeG Σ, !ltypeG Σ}.

  Lemma cpd_body_cell {𝔄} κ γ (node: lpat → prfn 𝔄 → nat → nat → thread_id → cloc → iProp Σ)
      tid l (x: ~~𝔄) d g wπ :
    cpd_body κ γ node tid l (uniq_cell x d g) wπ ⊣⊢
    ∃ p r, ⌜pat_ok κ p⌝ ∗ ⌜wπ = λ π, (prfn_den r π, (enc_depth d, enc_depth g))⌝ ∗
      ghost_var γ (1/2) ((p, existT 𝔄 r) : ltype_state) ∗ ⧖(S d `max` g) ∗ node p r d g tid l.
  Proof. by rewrite /cpd_body /= !dec_enc_depth. Qed.

  Local Lemma ltype_state_agree {𝔄} (p p': lpat) (r r': prfn 𝔄) :
    ((p, existT 𝔄 r) : ltype_state) = (p', existT 𝔄 r') → p = p' ∧ r = r'.
  Proof.
    intros Heq. split; [exact (f_equal fst Heq)|].
    apply (Eqdep_dec.inj_pair2_eq_dec _ syn_type_beq_dec). exact (f_equal snd Heq).
  Qed.

  (** Switching shapes: open the borrow (with a lifetime guard), and close it
      with any new shape satisfying the membership condition, updating both
      halves of the state. The observer (reserved or not) is kept. *)
  Lemma cpd_acc {𝔄} κ ξi γ p (node: lpat → prfn 𝔄 → nat → nat → thread_id → cloc → iProp Σ)
      (r: prfn 𝔄) d g tid l E G :
    Timeless G → ↑Nllft ⊆ E →
    llft_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗ G -∗
    cpd_own κ ξi γ p node r d g tid l ={E}=∗
      ⌜pat_ok κ p⌝ ∗ ⧖(S d `max` g) ∗ ▷ node p r d g tid l ∗
      (∀ p' (r': prfn 𝔄) d' g', ⌜pat_ok κ p'⌝ -∗ ⧖(S d' `max` g') -∗ ▷ node p' r' d' g' tid l
         ={↑Nllft}=∗ cpd_own κ ξi γ p' node r' d' g' tid l ∗ G).
  Proof.
    iIntros (??) "#LFT #UNIQ #Gk G (%x₀ & %idx & Obs & Gh & ⧗ & #Bor)".
    have ?: Inhabited (prfn 𝔄) := populate r.
    iAssert (∀ wπ, ▷ cpd_body κ γ node tid l (uniq_cell x₀ d g) wπ -∗ ghost_var γ (1/2) ((p, existT 𝔄 r) : ltype_state) ={E}=∗
      ⌜pat_ok κ p⌝ ∗ ⧖(S d `max` g) ∗ ▷ node p r d g tid l ∗ ghost_var γ (1/2) ((p, existT 𝔄 r) : ltype_state) ∗
      ghost_var γ (1/2) ((p, existT 𝔄 r) : ltype_state))%I as "Open".
    { iIntros (wπ) "Body Gh". rewrite cpd_body_cell.
      iDestruct "Body" as (p1 r1) "(>%Hok & >%Hwπ & >Gh' & >#⧖ & Node)".
      iDestruct (ghost_var_agree with "Gh Gh'") as %[<- <-]%ltype_state_agree.
      by iFrame "∗#". }
    iAssert (∀ p' (r': prfn 𝔄) d' g', ⌜pat_ok κ p'⌝ -∗ ⧖(S d' `max` g') -∗ ▷ node p' r' d' g' tid l -∗
      ghost_var γ (1/2) ((p, existT 𝔄 r) : ltype_state) -∗ ghost_var γ (1/2) ((p, existT 𝔄 r) : ltype_state) ==∗
      ghost_var γ (1/2) ((p', existT 𝔄 r') : ltype_state) ∗
      ▷ cpd_body κ γ node tid l (uniq_cell x₀ d' g') (λ π, (prfn_den r' π, (enc_depth d', enc_depth g'))))%I
      as "Shift".
    { iIntros (p' r' d' g' Hok') "#⧖' Node' Gh Gh'".
      iMod (ghost_var_update_halves ((p', existT 𝔄 r') : ltype_state) with "Gh Gh'") as "[$ Gh']".
      iModIntro. rewrite cpd_body_cell. iNext. iExists p', r'. by iFrame "∗#". }
    iDestruct "Obs" as "[Tok|(%ζl & Tok)]".
    - iMod (proph_idx_bor_gen_acc with "LFT UNIQ Gk Tok Bor G") as (wπ) "[Body Close]"; [done|].
      iMod ("Open" with "Body Gh") as "($ & $ & $ & Gh & Gh')". iModIntro.
      iIntros (p' r' d' g') "%Hok' #⧖' Node'".
      iMod ("Shift" with "[//] ⧖' Node' Gh Gh'") as "[Gh Body]".
      iMod ("Close" with "[] Body") as (idx') "(Tok & Bor' & $)".
      { by iIntros "!>" (??) "$". }
      iModIntro. iExists x₀, idx'. iSplitL "Tok"; [by iLeft|]. iFrame.
    - iMod (proph_idx_bor_gen_rsv_acc with "LFT UNIQ Gk Tok Bor G") as (wπ) "[Body Close]"; [done|].
      iMod ("Open" with "Body Gh") as "($ & $ & $ & Gh & Gh')". iModIntro.
      iIntros (p' r' d' g') "%Hok' #⧖' Node'".
      iMod ("Shift" with "[//] ⧖' Node' Gh Gh'") as "[Gh Body]".
      iMod ("Close" with "[] Body") as (idx') "(Tok & Bor' & $)".
      { by iIntros "!>" (??) "$". }
      iModIntro. iExists x₀, idx'. iSplitL "Tok"; [iRight; by iExists ζl|]. iFrame.
  Qed.
End cpd.

(** * Folding in [Uniq] mode *)

Section fold.
  Context `{!typeG Σ, !ltypeG Σ}.

  (** Fold a compound place in [Uniq] mode into an [OfTy ty] place, i.e.
      convert its pinned borrow into a [uniq_body]. This opens the borrow (with
      a lifetime guard) and closes it with the [uniq_payload] body; the
      closing view shift converts the [uniq_payload] back into the pinned
      body, which is possible because the [uniq_payload] corresponds to an
      unblocked shape ([Hback]). A reservation is given up. *)
  Lemma cpd_fold {𝔄} (ty: type 𝔄) (Φ: ~~𝔄 → Prop) κ ξi γ p
      (node: lpat → prfn 𝔄 → nat → nat → thread_id → cloc → iProp Σ) (r: prfn 𝔄) d g tid l E G :
    Timeless G → ↑Nllft ∪ ↑prophN ⊆ E →
    (node p r d g tid l ⊢ ∃ v, ⌜Φ v⌝ ∗ ty.(ty_gho_own) v d g tid ∗ l #↦!∗ ty.(ty_phys) v tid) →
    (∀ x d' g', ty.(ty_gho_own) x d' g' tid ∗ l #↦!∗ ty.(ty_phys) x tid ⊢
       ∃ p' r', ⌜pat_ok κ p' ∧ prfn_den r' = vπ x⌝ ∗ node p' r' d' g' tid l) →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗ G -∗
    cpd_own κ ξi γ p node r d g tid l ={E}=∗
      ∃ v, ⌜Φ v⌝ ∗ ofty_in (Uniq κ ξi γ) ty v d g tid l ∗ G.
  Proof.
    iIntros (?? Hnode Hback) "#LFT #PROPH #UNIQ #Gk G (%x₀ & %idx & Obs & Gh & ⧗ & #Bor)".
    have ?: Inhabited (prfn 𝔄) := populate r.
    have ?: Inhabited (~~𝔄) := populate x₀.
    iAssert (|={E}=> proph_bor_tok (uniq_prvar x₀ ξi) (uniq_cell x₀ d g) idx ∗ G)%I
      with "[Obs G]" as ">[Tok G]".
    { iDestruct "Obs" as "[$|(%ζl & Tok)]"; [done|].
      iApply (proph_idx_bor_gen_unreserve with "LFT PROPH UNIQ Gk G Tok Bor"); solve_ndisj. }
    iMod (proph_idx_bor_gen_acc with "LFT UNIQ Gk Tok Bor G") as (wπ) "[Body Close]";
      [solve_ndisj|].
    rewrite cpd_body_cell.
    iDestruct "Body" as (p1 r1) "(>%Hok & >%Hwπ & >Gh' & >#⧖ & Node)".
    iDestruct (ghost_var_agree with "Gh Gh'") as %[<- <-]%ltype_state_agree.
    iAssert (▷ ∃ v, ⌜Φ v⌝ ∗ ty.(ty_gho_own) v d g tid ∗ l #↦!∗ ty.(ty_phys) v tid)%I
      with "[Node]" as "Node". { iNext. by iApply Hnode. }
    iDestruct "Node" as (v) "(>%Hv & Gho & Pt)".
    iAssert (▷ (ty.(ty_gho_own) v d g tid ∗ ty.(ty_gho_pers) v d g tid))%I
      with "[Gho]" as "[Gho #Pers]".
    { iNext. iDestruct (ty_gho_pers_impl with "Gho") as "#?". by iFrame "∗#". }
    iMod (fupd_mask_subseteq (↑Nllft)) as "Upd"; [solve_ndisj|].
    iMod ("Close" $! (uniq_cell v d g) (vπ (uniq_cell v d g))
      (λ c wπ, ⌜wπ = vπ c⌝ ∗ uniq_payload ty tid l c)%I with "[Gh Gh'] [Gho Pt]")
      as (idx') "(Tok & Bor' & G)".
    { iIntros "!>" (c wπ2) "[>-> Pl]". rewrite /uniq_payload.
      iDestruct "Pl" as "(>#⧖2 & Pl)".
      iAssert (▷ ∃ p'' r'', ⌜pat_ok κ p'' ∧ prfn_den r'' = vπ c.1⌝ ∗
        node p'' r'' (dec_depth c.2.1) (dec_depth c.2.2) tid l)%I with "[Pl]" as "Pl".
      { iNext. by iApply Hback. }
      iDestruct "Pl" as (p'' r'') "(>%Hpr & Node)". destruct Hpr as [Hok'' Hden''].
      iMod (ghost_var_update_halves ((p'', existT 𝔄 r'') : ltype_state) with "Gh Gh'")
        as "[_ Gh]".
      iModIntro. iNext. iExists p'', r''. iFrame "Gh ⧖2 Node". iPureIntro.
      split; [done|]. rewrite Hden''. by destruct c as [? [??]]. }
    { iNext. iSplit; [done|]. rewrite uniq_payload_cell. by iFrame "∗#". }
    iMod "Upd" as "_".
    iAssert (proph_idx_bor κ (uniq_prvar x₀ ξi) idx' (uniq_payload ty tid l)) with "[Bor']"
      as "#Bor2". { by rewrite proph_idx_bor_to_gen. }
    iModIntro. iExists v. iSplit; [done|]. iFrame "G". iSplitL; [|iRight; iFrame "Pers"].
    iExists idx'. iApply (uniq_body_make ty v x₀ with "[Tok Bor2] ⧗").
    rewrite proph_ibor_sep. iFrame "∗#".
  Qed.

  Lemma prod_ofty_fold_uniq {𝔄 𝔅} (ty1: type 𝔄) (ty2: type 𝔅) κ ξi γ x1 x2 d g tid l E G :
    Timeless G → ↑Nllft ∪ ↑prophN ⊆ E →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗ G -∗
    ltype_own (Uniq κ ξi γ) (ProdLty (OfTy ty1) (OfTy ty2))
      (inr (inl (PlaceIn x1), inl (PlaceIn x2))) d g tid l ={E}=∗
    ltype_own (Uniq κ ξi γ) (OfTy (prod_ty ty1 ty2)) (inl (PlaceIn (𝔄:=𝔄 * 𝔅) (x1, x2))) d g tid l ∗ G.
  Proof.
    iIntros (??) "#LFT #PROPH #UNIQ #Gk G H".
    iMod (cpd_fold (prod_ty ty1 ty2) (λ v, v = (x1, x2)) with "LFT PROPH UNIQ Gk G H")
      as (v) "(-> & In & $)"; [done| | |].
    - iIntros "H". iDestruct (prod_ofty_unfold_own 0 with "H") as (y ->) "[Pt Gho]".
      iExists (x1, x2). by iFrame.
    - intros [y1 y2] d' g'. iIntros "[Gho Pt]".
      iExists (PatProd PatLeaf PatLeaf), (inr (inl (PlaceIn y1), inl (PlaceIn y2))).
      iSplit. { iPureIntro. split; [by intros ? ?%elem_of_nil|by rewrite /= !prfn_den_in]. }
      iApply (prod_ofty_unfold_own 0). iExists (y1, y2). by iFrame.
    - iModIntro. iExists (x1, x2). by iFrame.
  Qed.

  Lemma ownptr_ofty_fold_uniq {𝔄} n (ty: type 𝔄) κ ξi γ l' x d g tid l E G :
    Timeless G → ↑Nllft ∪ ↑prophN ⊆ E →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗ G -∗
    ltype_own (Uniq κ ξi γ) (OwnPtrLty n (OfTy ty)) (inr (l', inl (PlaceIn x))) d g tid l ={E}=∗
    ltype_own (Uniq κ ξi γ) (OfTy (own_ptr n ty)) (inl (PlaceIn (𝔄:=at_locₛ 𝔄) (l', x))) d g tid l ∗ G.
  Proof.
    iIntros (??) "#LFT #PROPH #UNIQ #Gk G H".
    iMod (cpd_fold (own_ptr n ty) (λ v, v = (l', x)) with "LFT PROPH UNIQ Gk G H")
      as (v) "(-> & In & $)"; [done| | |].
    - iIntros "H". iDestruct (ownptr_ofty_fold_own 0 with "H") as (y ->) "[Pt Gho]".
      iExists (l', x). by iFrame.
    - intros [l'' y] d' g'. iIntros "[Gho Pt]".
      iExists (PatOwn PatLeaf), (inr (l'', inl (PlaceIn y))).
      iSplit. { iPureIntro. split; [by intros ? ?%elem_of_nil|by rewrite /= !prfn_den_in]. }
      iApply ownptr_ofty_unfold_own. iExists (l'', y). by iFrame.
    - iModIntro. iExists (l', x). by iFrame.
  Qed.

  Lemma uniq_ofty_fold_uniq {𝔄} (ty: type 𝔄) κ' κ ξi γ l' x ξi' γ' d g tid l E G :
    Timeless G → ↑Nllft ∪ ↑prophN ⊆ E →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗ G -∗
    ltype_own (Uniq κ ξi γ) (UniqLty (OfTy ty) κ') (inr (l', inl (PlaceIn x), ξi', γ')) d g tid l
      ={E}=∗ ∃ d' g' idx,
    ltype_own (Uniq κ ξi γ) (OfTy (&uniq{κ'} ty))
      (inl (PlaceIn (𝔄:=uniq_borₛ 𝔄) (l', x, ξi', d', g', idx))) d g tid l ∗ G.
  Proof.
    iIntros (??) "#LFT #PROPH #UNIQ #Gk G H".
    iMod (cpd_fold (&uniq{κ'} ty) (λ v, ∃ d' g' idx, v = (l', x, ξi', d', g', idx))
      with "LFT PROPH UNIQ Gk G H") as (v) "(%Hv & In & $)"; [done| | |].
    - iIntros "H". iDestruct (uniq_ofty_fold_own 0 with "H") as (d' g' idx y ->) "[Pt Gho]".
      iExists (l', x, ξi', d', g', idx). iFrame. iPureIntro. by eexists _, _, _.
    - intros [[[[[l'' y] ξi''] d''] g''] idx''] d' g'. iIntros "[Gho Pt]".
      iExists (PatUniq PatLeaf), (inr (l'', inl (PlaceIn y), ξi'', γ')).
      iSplit. { iPureIntro. split; [by intros ? ?%elem_of_nil|by rewrite -(uniq_ofty_den l'' y ξi'' d'' g'' idx'' γ') prfn_den_in]. }
      iApply uniq_ofty_unfold_own. iExists (l'', y, ξi'', d'', g'', idx''). by iFrame.
    - destruct Hv as (d' & g' & idx & ->). iModIntro. iExists d', g', idx, _. by iFrame.
  Qed.
End fold.

(** * Creating compound places in [Uniq] mode, and their lenders *)

Section create.
  Context `{!typeG Σ, !ltypeG Σ}.

  Definition lty_is_leaf {𝔄} (lt: lty 𝔄) : bool :=
    match lt with OfTy _ | Blocked _ _ => true | _ => false end.

  (** A compound place in [Uniq] mode is a pinned borrow of its [Owned]
      interpretation. *)
  Lemma ltype_own_cp_uniq_cpd {𝔄} (lt: lty 𝔄) κ ξi γ p :
    lty_is_leaf lt = false →
    ltype_own_cp false lt (Uniq κ ξi γ) p =
      cpd_own κ ξi γ p (λ p', ltype_own_cp false lt (Owned 0) p').
  Proof. destruct lt; simpl; intros H; [discriminate|discriminate|reflexivity..]. Qed.

  Local Lemma pat_own_dead p :
    lft_dead_list (pat_blk_lfts p) ⊢ lft_dead_list (pat_blk_lfts (pat_own p)).
  Proof. rewrite /lft_dead_list. destruct p; simpl; iIntros "H"; done. Qed.

  Local Lemma pat_prod_dead p :
    lft_dead_list (pat_blk_lfts p) ⊢
      lft_dead_list (pat_blk_lfts (pat_l p)) ∗ lft_dead_list (pat_blk_lfts (pat_r p)).
  Proof.
    rewrite /lft_dead_list. destruct p; simpl; iIntros "H"; [iSplitL "H"; done..|].
    by iDestruct (big_sepL_app with "H") as "[$ $]".
  Qed.

  (** Unblocking at an arbitrary pattern, in [Owned] mode. *)
  Lemma ltype_own_cp_unblock {𝔄} (lt: lty 𝔄) m p r d g tid l :
    lft_dead_list (pat_blk_lfts p) -∗ ltype_own_cp false lt (Owned m) p r d g tid l ={⊤}=∗
      ∃ d' g', ltype_own_cp true lt (Owned m) p r d' g' tid l.
  Proof.
    induction lt as [𝔄 ty|𝔄 ty α|𝔄 lt IH κ|𝔄 n lt IH|𝔄 𝔅 lt1 IH1 lt2 IH2]
      in m, p, r, d, g, tid, l |- *; simpl.
    1,2: iIntros "#Dead H"; destruct r as [lr|]; [|done]; destruct p; simpl;
        try (iModIntro; iExists d, g; done);
      iEval (rewrite /lft_dead_list big_sepL_singleton) in "Dead";
      iMod ("H" with "Dead") as (x d' g') "(Rel & _ & In)"; iModIntro;
      iExists d', g', x; iFrame.
    - iIntros "_ H". iModIntro. iExists d, g. iApply (uniq_node_mono with "H").
      iIntros (ξi γ r' d' g' tid' l') "H". by iExists _.
    - iIntros "#Dead H". destruct r as [?|[l' r']]; [done|]. rewrite /own_node.
      iDestruct "H" as "(Pt & Fr & C)". iDestruct (pat_own_dead with "Dead") as "Dead'".
      iMod (IH with "Dead' C") as (d1 g1) "C". iModIntro.
      iExists (S d1), g1. iFrame. iNext. iDestruct "Fr" as "[_ $]". done.
    - iIntros "#Dead H". destruct r as [?|[r1 r2]]; [done|]. rewrite /prod_node.
      iDestruct (pat_prod_dead with "Dead") as "[Dead1 Dead2]".
      iDestruct "H" as "[H1 H2]".
      iMod (IH1 with "Dead1 H1") as (d1 g1) "H1".
      iMod (IH2 with "Dead2 H2") as (d2 g2) "H2".
      iModIntro. iExists (d1 `max` d2), (g1 `max` g2). iSplitL "H1".
      + iApply (ltype_own_cp_owned_depth_mono with "H1"); lia.
      + iApply (ltype_own_cp_owned_depth_mono with "H2"); lia.
  Qed.

  (** The lender of a pinned borrow can always shift the contents back to
      the core, once the borrow's lifetime has ended: the membership
      condition guarantees that all blocked lifetimes are dead. *)
  Lemma cpd_lender_unblock {𝔄} κ (lt: lty 𝔄) m p r d g tid l :
    pat_ok κ p →
    [†κ] -∗ ltype_own_cp false lt (Owned m) p r d g tid l ={⊤}=∗
      ∃ d' g', ltype_own_core (Owned m) lt r d' g' tid l.
  Proof.
    iIntros (Hok) "#†κ H". iDestruct (pat_ok_dead with "†κ") as "Dead"; [done|].
    iMod (ltype_own_cp_unblock with "Dead H") as (d' g') "H". iModIntro.
    iExists d', g'. by iApply ltype_own_cp_true_owned_pat.
  Qed.

  (** Create a compound place in [Uniq] mode from an [Owned] place (as for
      borrowing a place). The lender receives, after [κ], the contents at
      some shape satisfying the membership condition, together with an
      equalizer for the final value; with [cpd_lender_unblock] it can then
      shift them back to the core. *)
  Lemma cpd_create {𝔄} κ (lt: lty 𝔄) r d g tid l E :
    lty_is_leaf lt = false → pat_ok κ (lty_pat lt) →
    ↑Nllft ∪ ↑prophN ∪ ↑uniqN ⊆ E →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ ⧖(S d `max` g) -∗ ⧗1 -∗
    ▷ ltype_own (Owned 0) lt r d g tid l ={E}=∗ ∃ ξi γ,
      ltype_own (Uniq κ ξi γ) lt r d g tid l ∗
      ([†κ] ={↑Nllft}=∗ ▷ ∃ p' r' d' g',
        ((λ π, (π (uniq_prvar (prfn_wit r) ξi)).1) :== prfn_den r') ∗ ⌜pat_ok κ p'⌝ ∗
        ⧖(S d' `max` g') ∗ ltype_own_cp false lt (Owned 0) p' r' d' g' tid l).
  Proof.
    iIntros (Hcpd Hok ?) "#LFT #PROPH #UNIQ #⧖ ⧗ H".
    set x₀ := prfn_wit r.
    iMod (proph_loan_intro (uniq_cell_tyi x₀) E (uniq_cell x₀ d g) with "PROPH UNIQ")
      as (ξi) "Loan"; [solve_ndisj|].
    iMod (ghost_var_alloc ((lty_pat lt, existT 𝔄 r) : ltype_state)) as (γ) "[Gh Gh']".
    iMod (proph_loan_borrow_gen E κ (uniq_prvar x₀ ξi) (uniq_cell x₀ d g)
      (λ π, (prfn_den r π, (enc_depth d, enc_depth g)))
      (cpd_body κ γ (λ p', ltype_own_cp false lt (Owned 0) p') tid l)
      with "LFT PROPH UNIQ Loan [Gh' H]") as (idx) "(Tok & #Bor & Back)"; [solve_ndisj| |].
    { rewrite cpd_body_cell. iNext. iExists (lty_pat lt), r. by iFrame "∗#". }
    iModIntro. iExists ξi, γ. iSplitR "Back".
    - rewrite /ltype_own ltype_own_cp_uniq_cpd; [|done].
      iExists x₀, idx. iSplitL "Tok"; [by iLeft|]. iFrame "∗#".
    - iIntros "†κ". iMod ("Back" with "†κ") as "Back". iModIntro. iNext.
      iDestruct "Back" as (c wπ) "[Eqz Body]". rewrite {1}(uniq_cell_surj c) cpd_body_cell.
      iDestruct "Body" as (p' r') "(%Hok' & -> & _ & ⧖' & Node)".
      iExists p', r', (dec_depth c.2.1), (dec_depth c.2.2). iFrame "⧖' Node". iSplit; [|done].
      iApply (proph_eqz_fst_const (λ π, π (uniq_prvar x₀ ξi)) (prfn_den r')
        (enc_depth (dec_depth c.2.1), enc_depth (dec_depth c.2.2))).
      by rewrite !enc_dec_depth.
  Qed.
End create.
