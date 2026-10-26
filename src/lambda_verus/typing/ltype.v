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
  RefinedRust's [lty_core]; [lty_fold] is the type of the place once folded
  ([OfTy]/[Blocked] leaves are their type, the constructors are [&uniq],
  [own_ptr] and [prod_ty]).

  ** Place refinements and states

  Refinements are place refinements ([typing/lstate.v]): [PlaceIn x] (a current
  value) or [PlaceProph x₀ f] (a prophecy, e.g. the final value of a
  reborrow); compound places have structured refinements ([prfn_struct]): the
  refinement of [UniqLty lt κ] is [(l', r, ξi)] (the referent location, the
  referent's refinement and the borrow's prophecy variable id), [OwnPtrLty]
  has [(l', r)], [ProdLty] has [(r1, r2)]. A place type [lt] is interpreted as
  its core (a [Σ]-dependent parameter) together with a [Σ]-independent
  _blocking pattern_ [lty_pat lt : lpat]; the pair of a pattern and a
  refinement is the _state_ of a place.

  ** Interpretation

  [ltype_own k lt r d g tid l] (notation [l ◁ₗ[tid, k, d, g] r @ lt]) is
  indexed by depths [d g], exactly as [ty_gho_own]. Borrow kinds
  ([bor_kind]):
  - [Owned m]: the place is owned. For [OfTy ty] this is [ty_own] at the
    location ([l #↦!∗ ty_phys] and [ty_gho_own]); [m] is the number of laters
    guarding the ghost parts (one per enclosing [own_ptr]). [Blocked ty κ]
    holds an inheritance that gives back _pending_ ownership
    ([blocked_owned]): once [κ] is dead, the contents are obtained by a lazy
    update ([guarded_upd]) for the lifetime of [ty], as the blocked entries of
    the type context ([tctx_pending]). This makes blocking through a unique
    borrow possible, since the contents of a unique borrow are lazy.
  - [Uniq κ ξi]: the place is the referent of a unique borrow at lifetime [κ]
    with prophecy variable id [ξi].
    - For [OfTy ty] this is the existing [uniq_body], so that
      [UniqLty (OfTy ty) κ] and [OfTy (&uniq{κ} ty)] are equivalent.
    - For [Blocked ty κ'] the borrow itself is blocked (an inheritance giving
      back the [OfTy ty] borrow), as in RefinedRust.
    - For compound place types, the place is held by the _same kind_ of borrow
      as [&uniq] ([cpd_own]): a generalized prophetic borrow whose body is a
      pinned, state-indexed body ([cpd_body] of [uniq_util.v]), whose state is
      pinned by the ghost variable whose name is in the value of the borrow's
      prophecy variable ([cell_γ]). The body of [&uniq] is the instance of
      [cpd_body] with the leaf [leaf_node] as node; a compound place uses the
      node of its core instead. Its body ([cpd_gbody]) is the disjunction of the
      compound body and of the body of [&uniq] together with a token [cpd_tok]
      held by the owner of the compound place: once the place is folded back
      ([prod_ofty_fold_uniq]), the token is given up, which allows the closing
      view shift of the folded borrow to convert the [&uniq] body back into the
      compound body.

  ** Unfolding

  At [Owned m], [ProdLty (OfTy ty1) (OfTy ty2)] is [ltype_eq] to
  [OfTy (prod_ty ty1 ty2)] ([prod_ofty_unfold]); [OwnPtrLty n (OfTy ty)] is
  [ltype_eq] to [OfTy (own_ptr n ty)] at [Owned 0] ([ownptr_ofty_unfold]);
  and [UniqLty (OfTy ty) κ] is equivalent to [OfTy (&uniq{κ} ty)]
  ([uniq_ofty_unfold], [uniq_ofty_fold_own]). At [Uniq] mode, a product is
  unfolded _behind an existing unique borrow_ ([prod_ofty_unfold_uniq]): the body
  of the borrow is switched (with a lifetime guard, without a new borrow and
  without changing the prophecy variable) from the leaf [prod_ty ty1 ty2] to the
  node [ProdLty (OfTy ty1) (OfTy ty2)], and back ([prod_ofty_fold_uniq]). The
  closing view shift of the unfolding converts the compound body back into the
  [&uniq] body at the same state: a leaf sees a state with a structured
  refinement as blocked at the pattern lifetime [κp] ([leaf_node]), whose
  inheritance unblocks the components (the membership condition [pat_ok κp]
  makes their blocked lifetimes end before [κp]).

  Unfolding [own_ptr] and [&uniq] behind a unique borrow is not supported: the
  closing view shift would have to rebuild the receipt of an owned pointer
  ([⧖] of one more than the depth of its unblocked pointee, which needs a program
  step), resp. a nested membership condition for the blocked places behind the
  nested borrow. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From lrust.typing Require Export type.
From lrust.typing Require Import uniq_util uniq_bor own product freeable_util.
From lrust.lifetime Require Import lifetime_full.
From guarding Require Import guard tactics.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅 ℭ: syn_type.

(** * Borrow kinds *)

Inductive bor_kind :=
| Owned (m: nat)
| Uniq (κ: lft) (ξi: positive).

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

  (** The type of a place, once folded. *)
  Fixpoint lty_fold {𝔄} (lt: lty 𝔄) : type 𝔄 :=
    match lt in lty 𝔄 return type 𝔄 with
    | OfTy ty => ty
    | Blocked ty _ => ty
    | UniqLty lt κ => uniq_bor κ (lty_fold lt)
    | OwnPtrLty n lt => own_ptr n (lty_fold lt)
    | ProdLty lt1 lt2 => prod_ty (lty_fold lt1) (lty_fold lt2)
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

  Lemma lty_fold_core {𝔄} (lt: lty 𝔄) : lty_fold (lty_core lt) = lty_fold lt.
  Proof. induction lt; simpl; rewrite ?IHlt ?IHlt1 ?IHlt2; done. Qed.

  Lemma lty_size_fold {𝔄} (lt: lty 𝔄) : lty_size lt = ty_size (lty_fold lt).
  Proof. induction lt; simpl; rewrite ?IHlt ?IHlt1 ?IHlt2; done. Qed.

  Lemma lty_lfts_fold {𝔄} (lt: lty 𝔄) : lty_lfts lt = ty_lfts (lty_fold lt).
  Proof. induction lt; simpl; rewrite ?IHlt ?IHlt1 ?IHlt2; done. Qed.
End lty.

(** * Interpretation *)

Section ltype_own.
  Context `{!typeG Σ}.

  (** ** Leaves in [Uniq] mode *)

  Definition ofty_uniq {𝔄} (κ: lft) (ξi: positive) (ty: type 𝔄) (lr: place_rfn 𝔄)
      (d g: nat) (tid: thread_id) (l: cloc) : iProp Σ :=
    ∃ x idx, place_rfn_rel lr x ∗ uniq_body ty x ξi d g idx κ tid l.

  (** A blocked leaf in [Uniq] mode: the borrow itself is blocked; its inheritance
      gives back _pending_ ownership of the borrow, as [blocked_owned]. *)
  Definition blocked_uniq {𝔄} (κ: lft) (ξi: positive) (ty: type 𝔄) (α: lft)
      (lr: place_rfn 𝔄) (tid: thread_id) (l: cloc) : iProp Σ :=
    [†α] ={lazyE}=∗ guarded_upd lazyE @[ty_lft ty]
      (∃ d' g', ⧖(S d' `max` g') ∗ ofty_uniq κ ξi ty lr d' g' tid l).

  Definition leaf_uniq {𝔄} (c: bool) (κ: lft) (ξi: positive) (ty: type 𝔄) (p: lpat)
      (r: prfn 𝔄) (d g: nat) (tid: thread_id) (l: cloc) : iProp Σ :=
    match r with
    | inr _ => False
    | inl lr =>
        match p with
        | PatBlocked α =>
            if c then ofty_uniq κ ξi ty lr d g tid l else blocked_uniq κ ξi ty α lr tid l
        | _ => ofty_uniq κ ξi ty lr d g tid l
        end
    end%I.

  (** ** Leaves, in both modes ([c] selects the core interpretation) *)

  Definition leaf_own {𝔄} (c: bool) (k: bor_kind) (ty: type 𝔄) :
      lpat → prfn 𝔄 → nat → nat → thread_id → cloc → iProp Σ :=
    match k with
    | Owned m => leaf_owned c m ty
    | Uniq κ ξi => leaf_uniq c κ ξi ty
    end.

  (** ** Nodes in [Owned] mode, given the interpretations of the children *)

  Definition uniq_node {𝔅} (m: nat) (κ': lft) (ty: type 𝔅)
      (child: positive → prfn 𝔅 → nat → nat → thread_id → cloc → iProp Σ)
      (r: prfn (uniq_borₛ 𝔅)) (d g: nat) (tid: thread_id) (l: cloc) : iProp Σ :=
    match r with
    | inl _ => False
    | inr (l', r', ξi) =>
        l #↦!∗ [FVal (LitV l'.1)] ∗
        ▷^m (κ' ⊑ ty_lft ty ∗ (@[κ'] &&{↑NllftG; g+1}&&> l' #↦∗_) ∗
          ∃ d' g', ⌜S d' ≤ d ∧ g' ≤ g⌝ ∗ child ξi r' d' g' tid l')
    end%I.

  Definition own_node {𝔅} (m: nat) (n sz: nat)
      (child: prfn 𝔅 → nat → nat → thread_id → cloc → iProp Σ)
      (r: prfn (at_locₛ 𝔅)) (d g: nat) (tid: thread_id) (l: cloc) : iProp Σ :=
    match r with
    | inl _ => False
    | inr (l', r') =>
        l #↦!∗ [FVal (LitV l')] ∗ ▷^m (⌜d ≠ 0%nat⌝ ∗ freeable_sz n sz l') ∗
        child r' (pred d) g tid (l', repeat [] sz)
    end%I.

  Definition prod_node {𝔅 ℭ} (sz1: nat)
      (c1: prfn 𝔅 → nat → nat → thread_id → cloc → iProp Σ)
      (c2: prfn ℭ → nat → nat → thread_id → cloc → iProp Σ)
      (r: prfn (𝔅 * ℭ)) (d g: nat) (tid: thread_id) (l: cloc) : iProp Σ :=
    match r with
    | inl _ => False
    | inr (r1, r2) => c1 r1 d g tid (cloc_take l sz1) ∗ c2 r2 d g tid (cloc_skip l sz1)
    end%I.

  (** ** Compound places in [Uniq] mode *)

  (** The token of the owner of a compound place in [Uniq] mode. *)
  Definition cpd_tok (γf: gname) : iProp Σ := ghost_var γf 1 (lstate_triv (𝔄:=unitₛ) ()).

  Lemma cpd_tok_excl γf : cpd_tok γf -∗ cpd_tok γf -∗ False.
  Proof.
    iIntros "A B". iDestruct (ghost_var_valid_2 with "A B") as %[Hv _].
    by apply Qp.not_add_le_l in Hv.
  Qed.

  (** The body of a compound place in [Uniq] mode: the pinned body with the node
      [node] of the core, or (once folded, without the token) the body of [&uniq]
      at the folded type [ty]. *)
  Definition cpd_gbody {𝔄} (κp: lft) (γf: gname) (ty: type 𝔄)
      (node: lpat → prfn 𝔄 → nat → nat → thread_id → cloc → iProp Σ)
      (tid: thread_id) (l: cloc) (c: ~~ (uniq_cellₛ 𝔄)) (wπ: proph (uniq_cellₛ 𝔄)) : iProp Σ :=
    cpd_body κp (ty_lft ty) node tid l c wπ ∨ (cpd_tok γf ∗ uniq_gbody κp ty tid l c wπ).

  (** As [uniq_body], with the state [lstate p r] instead of the trivial state. The
      observer is reserved, for some [ζl] on which the prophetic leaves of [r] (e.g. the
      final values of the reborrows of blocked leaves) depend ([prfn_rsv]), so that the
      place can be resolved while some of its leaves are blocked. *)
  Definition cpd_own {𝔄} (κ: lft) (ξi: positive) (ty: type 𝔄) (p: lpat)
      (node: lpat → prfn 𝔄 → nat → nat → thread_id → cloc → iProp Σ)
      (r: prfn 𝔄) (d g: nat) (tid: thread_id) (l: cloc) : iProp Σ :=
    ∃ (x₀: ~~𝔄) (κp: lft) (γ γf: gname) (idx: Idx) (ζl: list proph_var),
      uniq_pat_lft κ κp ∗ ⌜prfn_rsv r ζl⌝ ∗
      proph_bor_tok_rsv (uniq_prvar x₀ ξi) (uniq_cell x₀ d g γ) idx ζl ∗
      ghost_var γ (1/2) (lstate p r) ∗ cpd_tok γf ∗ ⧗1 ∗
      proph_idx_bor_gen κ (uniq_prvar x₀ ξi) idx (cpd_gbody κp γf ty node tid l).

  (** ** The interpretation

      By structural recursion on the place type, with the blocking pattern
      as an argument (only the core of the place type matters). *)
  Fixpoint ltype_own_cp (c: bool) {𝔄} (lt: lty 𝔄) {struct lt} :
      bor_kind → lpat → prfn 𝔄 → nat → nat → thread_id → cloc → iProp Σ :=
    match lt in lty 𝔄 return bor_kind → lpat → prfn 𝔄 → nat → nat → thread_id → cloc → iProp Σ with
    | OfTy ty => λ k, leaf_own c k ty
    | Blocked ty _ => λ k, leaf_own c k ty
    | UniqLty lt' κ' => λ k p,
        match k with
        | Owned m => uniq_node m κ' (lty_fold lt') (λ ξi r' d' g' tid l',
            if c then (∃ p', ltype_own_cp false lt' (Uniq κ' ξi) p' r' d' g' tid l')%I
            else ltype_own_cp false lt' (Uniq κ' ξi) (pat_uniq p) r' d' g' tid l')
        | Uniq κ ξi => cpd_own κ ξi (uniq_bor κ' (lty_fold lt')) p
            (λ p', uniq_node 0 κ' (lty_fold lt')
              (λ ξi', ltype_own_cp false lt' (Uniq κ' ξi') (pat_uniq p')))
        end
    | OwnPtrLty n lt' => λ k p,
        match k with
        | Owned m => own_node m n (lty_size lt') (ltype_own_cp c lt' (Owned (m + 1)) (pat_own p))
        | Uniq κ ξi => cpd_own κ ξi (own_ptr n (lty_fold lt')) p
            (λ p', own_node 0 n (lty_size lt')
              (ltype_own_cp false lt' (Owned (0 + 1)) (pat_own p')))
        end
    | ProdLty lt1 lt2 => λ k p,
        match k with
        | Owned m => prod_node (lty_size lt1) (ltype_own_cp c lt1 (Owned m) (pat_l p))
            (ltype_own_cp c lt2 (Owned m) (pat_r p))
        | Uniq κ ξi => cpd_own κ ξi (prod_ty (lty_fold lt1) (lty_fold lt2)) p
            (λ p', prod_node (lty_size lt1)
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
    | Uniq _ _ => ∃ p, ltype_own_cp false lt k p r d g tid l
    end.
End ltype_own.

Notation "l ◁ₗ[ tid , k , d , g ] r @ lt" := (ltype_own k lt r d g tid l)
  (at level 70, format "l  ◁ₗ[ tid ,  k ,  d ,  g ]  r  @  lt") : bi_scope.

(** * Laws *)

Section ltype_lemmas.
  Context `{!typeG Σ}.
  Implicit Type (κ α: lft).

  (** ** Monotonicity of the nodes in their children *)

  Lemma uniq_node_mono {𝔅} m κ' (ty: type 𝔅)
      (c1 c2: positive → prfn 𝔅 → nat → nat → thread_id → cloc → iProp Σ) r d g tid l :
    (∀ ξi r' d' g' tid' l', c1 ξi r' d' g' tid' l' ⊢ c2 ξi r' d' g' tid' l') →
    uniq_node m κ' ty c1 r d g tid l ⊢ uniq_node m κ' ty c2 r d g tid l.
  Proof.
    intros Hc. destruct r as [?|[[l' r'] ξi]]; [done|]. rewrite /uniq_node.
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
    - by rewrite lty_fold_core !IH.
    - by rewrite lty_size_core lty_fold_core !IH.
    - by rewrite lty_size_core !lty_fold_core !IH1 !IH2.
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
    destruct k as [m|κ ξi]; rewrite /ltype_own_core ltype_own_cp_core; [|done].
    iSplit; iApply ltype_own_cp_true_owned_pat.
  Qed.

  (** In [Uniq] mode, the core is enforced by the borrow itself. *)
  Lemma ltype_own_uniq_core {𝔄} κ ξi (lt: lty 𝔄) r d g tid l :
    ltype_own (Uniq κ ξi) lt r d g tid l ⊢ ltype_own_core (Uniq κ ξi) lt r d g tid l.
  Proof. iIntros "H". by iExists (lty_pat lt). Qed.

  (** ** Depth monotonicity in [Owned] mode *)

  Lemma leaf_owned_depth_mono c {𝔄} (ty: type 𝔄) m p r d g d' g' tid l :
    d ≤ d' → g ≤ g' →
    leaf_owned c m ty p r d g tid l ⊢ leaf_owned c m ty p r d' g' tid l.
  Proof.
    intros ??. destruct r as [lr|]; [|done].
    have Hofty: (∃ x, place_rfn_rel lr x ∗ ofty_owned m ty x d g tid l) ⊢
      ∃ x, place_rfn_rel lr x ∗ ofty_owned m ty x d' g' tid l.
    { iIntros "(%x & Rel & Pt & Gho)". iExists x. iFrame. iNext.
      iDestruct (ty_gho_own_depth_mono _ d g d' g' with "Gho") as "[$ _]"; done. }
    destruct p; try apply Hofty. destruct c; [apply Hofty|]. rewrite /leaf_owned.
    iIntros "$".
  Qed.

  Lemma ltype_own_cp_owned_depth_mono c {𝔄} (lt: lty 𝔄) m p r d g d' g' tid l :
    d ≤ d' → g ≤ g' →
    ltype_own_cp c lt (Owned m) p r d g tid l ⊢ ltype_own_cp c lt (Owned m) p r d' g' tid l.
  Proof.
    induction lt as [𝔄 ty|𝔄 ty α|𝔄 lt IH κ|𝔄 n lt IH|𝔄 𝔅 lt1 IH1 lt2 IH2]
      in m, p, r, d, g, d', g', tid, l |- *; intros Hd Hg; simpl.
    - by apply leaf_owned_depth_mono.
    - by apply leaf_owned_depth_mono.
    - destruct r as [?|[[l' r'] ξi]]; [done|]. rewrite /uniq_node.
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

  (** Implicit unblocking (cf. RefinedRust's [imp_unblockable]): once all [κs] are
      dead, a place can be shifted to its core, without changing the refinement,
      given a guard for the lifetime of its folded type (to settle the pending
      ownership of blocked leaves, see [blocked_owned]). The depth may change. *)
  Definition imp_unblockable (κs: list lft) {𝔄} (lt: lty 𝔄) : iProp Σ :=
    □ ∀ k r d g tid l G, ⌜Timeless G⌝ -∗ (G &&{↑NllftG}&&> @[ty_lft (lty_fold lt)]) -∗ G -∗
        lft_dead_list κs -∗ ltype_own k lt r d g tid l ={⊤}=∗
        G ∗ ∃ d' g', ltype_own_core k lt r d' g' tid l.
  Global Instance imp_unblockable_persistent κs {𝔄} (lt: lty 𝔄) :
    Persistent (imp_unblockable κs lt) := _.

  Lemma imp_unblockable_shorten κs κs' {𝔄} (lt: lty 𝔄) :
    □ (lft_dead_list κs ={⊤}=∗ lft_dead_list κs') -∗
    imp_unblockable κs' lt -∗ imp_unblockable κs lt.
  Proof.
    iIntros "#Hκ #Ub !>" (k r d g tid l G ?) "#Gk G Dead H".
    iMod ("Hκ" with "Dead") as "Dead'". iApply ("Ub" with "[//] Gk G Dead' H").
  Qed.

  Lemma ofty_imp_unblockable κs {𝔄} (ty: type 𝔄) : ⊢ imp_unblockable κs (OfTy ty).
  Proof.
    iIntros "!>" (k r d g tid l G ?) "_ $ _ H". iModIntro. iExists d, g.
    destruct k as [m|κ ξi]; [|by iApply ltype_own_uniq_core]. done.
  Qed.

  Lemma blocked_imp_unblockable {𝔄} (ty: type 𝔄) α : ⊢ imp_unblockable [α] (Blocked ty α).
  Proof.
    iIntros "!>" (k r d g tid l G ?) "#Gk G [#Dead _] H".
    destruct k as [m|κ ξi];
      [|iModIntro; iFrame "G"; iExists d, g; by iApply ltype_own_uniq_core].
    destruct r as [lr|]; [|done]. rewrite /ltype_own /ltype_own_core /= /blocked_owned.
    iMod (fupd_mask_mono with "(H Dead)") as "Upd"; [rewrite /lazyE; set_solver|].
    iMod (guarded_upd_run with "Gk G Upd") as "[$ (%x & %d' & %g' & Rel & _ & In)]";
      [rewrite /lazyE; set_solver|].
    iModIntro. iExists d', g', x. iFrame.
  Qed.

  (** Congruence. Unique borrows are trivially unblockable, as blocked
      places behind a nested borrow belong to that borrow. *)
  Lemma uniq_ltype_imp_unblockable κs {𝔄} (lt: lty 𝔄) κ' :
    ⊢ imp_unblockable κs (UniqLty lt κ').
  Proof.
    iIntros "!>" (k r d g tid l G ?) "_ $ _ H". iModIntro. iExists d, g.
    destruct k as [m|κ ξi]; [|by iApply ltype_own_uniq_core].
    rewrite /ltype_own /ltype_own_core /=. iApply (uniq_node_mono with "H").
    iIntros (ξi r' d' g' tid' l') "H". by iExists _.
  Qed.

  Lemma ownptr_ltype_imp_unblockable κs {𝔄} n (lt: lty 𝔄) :
    imp_unblockable κs lt -∗ imp_unblockable κs (OwnPtrLty n lt).
  Proof.
    iIntros "#Ub !>" (k r d g tid l G ?) "#Gk G #Dead H".
    destruct k as [m|κ ξi];
      [|iModIntro; iFrame "G"; iExists d, g; by iApply ltype_own_uniq_core].
    destruct r as [?|[l' r']]; [done|]. rewrite /ltype_own /ltype_own_core /=.
    iDestruct "H" as "(Pt & Fr & C)".
    iMod ("Ub" $! (Owned (m + 1)) with "[//] Gk G Dead C") as "[$ (%d1 & %g1 & C)]".
    iModIntro. iExists (S d1), g1. iFrame. iNext. iDestruct "Fr" as "[_ $]". done.
  Qed.

  Lemma prod_ltype_imp_unblockable κs {𝔄 𝔅} (lt1: lty 𝔄) (lt2: lty 𝔅) :
    imp_unblockable κs lt1 -∗ imp_unblockable κs lt2 -∗ imp_unblockable κs (ProdLty lt1 lt2).
  Proof.
    iIntros "#Ub1 #Ub2 !>" (k r d g tid l G ?) "#Gk G #Dead H".
    destruct k as [m|κ ξi];
      [|iModIntro; iFrame "G"; iExists d, g; by iApply ltype_own_uniq_core].
    destruct r as [?|[r1 r2]]; [done|]. rewrite /ltype_own /ltype_own_core /=.
    iDestruct "H" as "[H1 H2]".
    iAssert (G &&{↑NllftG}&&> @[ty_lft (lty_fold lt1)])%I as "#Gk1".
    { iApply (guards_transitive with "Gk"). simpl. rewrite lft_intersect_list_app.
      iApply llftl_intersect_incl_l. }
    iAssert (G &&{↑NllftG}&&> @[ty_lft (lty_fold lt2)])%I as "#Gk2".
    { iApply (guards_transitive with "Gk"). simpl. rewrite lft_intersect_list_app.
      iApply llftl_intersect_incl_r. }
    iMod ("Ub1" $! (Owned m) with "[//] Gk1 G Dead H1") as "[G (%d1 & %g1 & H1)]".
    iMod ("Ub2" $! (Owned m) with "[//] Gk2 G Dead H2") as "[$ (%d2 & %g2 & H2)]".
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

  (** Explicit unblocking of a blocked place. In [Owned] mode, the pending ownership
      is settled with a guard for the lifetime of the type. *)
  Lemma unblock_blocked_owned m {𝔄} (ty: type 𝔄) α r d g tid l G :
    Timeless G →
    (G &&{↑NllftG}&&> @[ty_lft ty]) -∗ G -∗
    [†α] -∗ ltype_own (Owned m) (Blocked ty α) r d g tid l ={⊤}=∗
      G ∗ ∃ d' g', ⧖(S d' `max` g') ∗ ltype_own (Owned m) (OfTy ty) r d' g' tid l.
  Proof.
    iIntros (?) "#Gk G Dead H". destruct r as [lr|]; [|done].
    rewrite /ltype_own /= /blocked_owned.
    iMod (fupd_mask_mono with "(H Dead)") as "Upd"; [rewrite /lazyE; set_solver|].
    iMod (guarded_upd_run with "Gk G Upd") as "[$ (%x & %d' & %g' & Rel & ⧖ & In)]";
      [rewrite /lazyE; set_solver|].
    iModIntro. iExists d', g'. iFrame "⧖". iExists x. iFrame.
  Qed.

  Lemma unblock_blocked_uniq κ ξi {𝔄} (ty: type 𝔄) α r d g tid l G :
    Timeless G →
    (G &&{↑NllftG}&&> @[ty_lft ty]) -∗ G -∗
    [†α] -∗ ltype_own (Uniq κ ξi) (Blocked ty α) r d g tid l ={⊤}=∗
      G ∗ ∃ d' g', ⧖(S d' `max` g') ∗ ltype_own (Uniq κ ξi) (OfTy ty) r d' g' tid l.
  Proof.
    iIntros (?) "#Gk G Dead H". destruct r as [lr|]; [|done]. rewrite /ltype_own /=.
    iMod (fupd_mask_mono with "(H Dead)") as "Upd"; [rewrite /lazyE; set_solver|].
    iApply (guarded_upd_run with "Gk G Upd"). rewrite /lazyE. set_solver.
  Qed.
End ltype_lemmas.

(** * Inclusion and equality of place types *)

Section ltype_incl.
  Context `{!typeG Σ}.

  Definition ltype_incl' (k: bor_kind) {𝔄} (r1 r2: prfn 𝔄) (lt1 lt2: lty 𝔄) : iProp Σ :=
    □ ∀ d g tid l,
      match k with
      | Owned _ => ltype_own k lt1 r1 d g tid l ={⊤}=∗ ltype_own k lt2 r2 d g tid l
      | Uniq _ _ => ltype_own k lt1 r1 d g tid l -∗ ltype_own k lt2 r2 d g tid l
      end.

  Definition ltype_incl'_core (k: bor_kind) {𝔄} (r1 r2: prfn 𝔄) (lt1 lt2: lty 𝔄) : iProp Σ :=
    □ ∀ d g tid l,
      match k with
      | Owned _ => ltype_own_core k lt1 r1 d g tid l ={⊤}=∗ ltype_own_core k lt2 r2 d g tid l
      | Uniq _ _ => ltype_own_core k lt1 r1 d g tid l -∗ ltype_own_core k lt2 r2 d g tid l
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

(** * Unfolding equations in [Owned] mode *)

Section unfold.
  Context `{!typeG Σ}.

  (** ** Products *)

  Lemma prod_ofty_unfold_own m {𝔄 𝔅} (ty1: type 𝔄) (ty2: type 𝔅) x1 x2 d g tid l :
    ltype_own (Owned m) (ProdLty (OfTy ty1) (OfTy ty2))
      (inr (inl (PlaceIn x1), inl (PlaceIn x2))) d g tid l ⊣⊢
    ltype_own (Owned m) (OfTy (prod_ty ty1 ty2)) (inl (PlaceIn (𝔄:=𝔄 * 𝔅) (x1, x2))) d g tid l.
  Proof.
    rewrite /ltype_own /= /ofty_owned /=. iSplit.
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
    rewrite /ltype_own /= /ofty_owned /=.
    iIntros "(Pt & Fr & %y & -> & Pt' & Gho)". iExists (l', x). iSplit; [done|]. iFrame "Pt".
    iNext. iDestruct "Fr" as "[% Fr]". destruct d as [|d]; [done|]. simpl.
    rewrite (heap_cloc_mapsto_fancy_empty l' (ty_phys ty x tid)) ty_size_eq. iFrame.
  Qed.

  Lemma ownptr_ofty_unfold_own {𝔄} n (ty: type 𝔄) l' x d g tid l :
    ltype_own (Owned 0) (OfTy (own_ptr n ty)) (inl (PlaceIn (𝔄:=at_locₛ 𝔄) (l', x))) d g tid l ⊢
    ltype_own (Owned 0) (OwnPtrLty n (OfTy ty)) (inr (l', inl (PlaceIn x))) d g tid l.
  Proof.
    rewrite /ltype_own /= /ofty_owned /=.
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
      is reborrowed). *)

  Lemma uniq_ofty_den {𝔄} (l': cloc) (x: ~~𝔄) ξi d' g' idx :
    prfn_den (inl (PlaceIn (𝔄:=uniq_borₛ 𝔄) (l', x, ξi, d', g', idx)) : prfn (uniq_borₛ 𝔄)) =
    prfn_den (inr (l', inl (PlaceIn x), ξi) : prfn (uniq_borₛ 𝔄)).
  Proof. rewrite /= prfn_den_in prfn_wit_in. done. Qed.

  Lemma uniq_ofty_unfold_own m {𝔄} (ty: type 𝔄) κ l' x ξi d' g' idx d g tid l :
    ltype_own (Owned m) (OfTy (&uniq{κ} ty)) (inl (PlaceIn (𝔄:=uniq_borₛ 𝔄) (l', x, ξi, d', g', idx))) d g tid l ⊢
    ltype_own (Owned m) (UniqLty (OfTy ty) κ) (inr (l', inl (PlaceIn x), ξi)) d g tid l.
  Proof.
    rewrite /ltype_own /= /ofty_owned /=.
    iIntros "(%v & -> & Pt & Gho)". iFrame "Pt". iNext.
    iDestruct "Gho" as "(#Incl & %Hle & Body & #G)".
    iSplitR; [done|]. iSplitR; [done|].
    iExists d', g'. iSplit; [done|]. iExists x, idx. iSplit; [done|]. done.
  Qed.

  Lemma uniq_ofty_fold_own m {𝔄} (ty: type 𝔄) κ l' x ξi d g tid l :
    ltype_own (Owned m) (UniqLty (OfTy ty) κ) (inr (l', inl (PlaceIn x), ξi)) d g tid l ⊢
    ∃ d' g' idx,
      ltype_own (Owned m) (OfTy (&uniq{κ} ty)) (inl (PlaceIn (𝔄:=uniq_borₛ 𝔄) (l', x, ξi, d', g', idx))) d g tid l.
  Proof.
    rewrite /ltype_own /= /ofty_owned /=.
    have ?: Inhabited (~~𝔄) := populate x. have ?: Inhabited Idx := populate idx_dummy.
    iIntros "[Pt H]".
    iDestruct "H" as "(Incl & G & %d' & %g' & Hle & %y & %idx & Hy & Body)".
    iExists d', g', idx, _. iSplit; [done|]. iFrame "Pt". iNext.
    iDestruct "Hy" as %->. iFrame.
  Qed.

  Lemma uniq_ofty_unfold_core m {𝔄} (ty: type 𝔄) κ l' x ξi d' g' idx d g tid l :
    ltype_own_core (Owned m) (OfTy (&uniq{κ} ty)) (inl (PlaceIn (𝔄:=uniq_borₛ 𝔄) (l', x, ξi, d', g', idx))) d g tid l ⊢
    ltype_own_core (Owned m) (UniqLty (OfTy ty) κ) (inr (l', inl (PlaceIn x), ξi)) d g tid l.
  Proof.
    iIntros "H". iDestruct (uniq_ofty_unfold_own with "H") as "H".
    iApply (uniq_node_mono with "H"). iIntros (????? l'') "H". by iExists _.
  Qed.

  Lemma uniq_ofty_unfold m {𝔄} (ty: type 𝔄) κ l' (x: ~~𝔄) ξi d' g' idx :
    ⊢ ltype_incl (Owned m) (inl (PlaceIn (𝔄:=uniq_borₛ 𝔄) (l', x, ξi, d', g', idx)))
        (inr (l', inl (PlaceIn x), ξi) : prfn (uniq_borₛ 𝔄))
        (OfTy (&uniq{κ} ty)) (UniqLty (OfTy ty) κ).
  Proof.
    iSplit; [iPureIntro; split; [done|apply uniq_ofty_den]|].
    iSplit; iIntros "!>" (d g tid l) "H"; iModIntro;
      [iApply (uniq_ofty_unfold_own with "H")|iApply (uniq_ofty_unfold_core with "H")].
  Qed.
End unfold.

(** * Compound places in [Uniq] mode *)

Section cpd.
  Context `{!typeG Σ}.

  (** Switching states: open the borrow (with a lifetime guard), and close it with
      any new state satisfying the membership condition, updating both halves of
      the ghost variable. The contents are lazy. The reservation may be extended by
      [ζl'] (on which the prophetic leaves of the new refinement may depend, in
      addition to those of the old one): the tokens for [ζl'] are needed when closing;
      they are handed to a view shift that produces the new contents. *)
  Lemma cpd_acc {𝔄} κ ξi (ty: type 𝔄) p (node: lpat → prfn 𝔄 → nat → nat → thread_id → cloc → iProp Σ)
      (r: prfn 𝔄) d g tid l E G :
    Timeless G → ↑Nllft ∪ ↑prophN ⊆ E →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗ G -∗
    cpd_own κ ξi ty p node r d g tid l ={E}=∗ ∃ κp,
      uniq_pat_lft κ κp ∗ ▷ pat_ok κp p ∗
      ▷ guarded_upd lazyE @[ty_lft ty] (⧖(S d `max` g) ∗ node p r d g tid l) ∗
      (∀ p' (r': prfn 𝔄) d' g' ζl' q (R: iProp Σ),
         ⌜∀ ζl, prfn_rsv r ζl → prfn_rsv r' (ζl ++ ζl')⌝ -∗ q:+[ζl'] -∗
         (q:+[ζl'] ={E}=∗ ▷ pat_ok κp p' ∗
           ▷ guarded_upd lazyE @[ty_lft ty] (⧖(S d' `max` g') ∗ node p' r' d' g' tid l) ∗ R)
         ={E}=∗ cpd_own κ ξi ty p' node r' d' g' tid l ∗ G ∗ R).
  Proof.
    iIntros (??) "#LFT #PROPH #UNIQ #Gk G".
    iIntros "(%x₀ & %κp & %γ & %γf & %idx & %ζl & #Incl & %Hr & Tok & Gh & Tf & ⧗ & #Bor)".
    iMod (proph_idx_bor_gen_rsv_acc_ext with "LFT PROPH UNIQ Gk Tok Bor G") as (wπ) "[Body Close]";
      [done..|].
    iDestruct (bi.later_or with "Body") as "[Body|[>Tf' _]]"; last first.
    { iDestruct (cpd_tok_excl with "Tf Tf'") as "[]". }
    rewrite cpd_body_cell.
    iMod (bi.later_exist_except_0 with "Body") as (p1) "Body".
    iMod (bi.later_exist_except_0 with "Body") as (r1) "(#Ok & _ & >Gh' & Upd)".
    iDestruct (ghost_var_agree with "Gh Gh'") as %[<- <-]%lstate_inj.
    iModIntro. iExists κp. iFrame "Incl Ok Upd".
    iIntros (p' r' d' g' ζl' q R Hr') "ζl' VS".
    iMod (ghost_var_update_halves (lstate p' r') with "Gh Gh'") as "[Gh Gh']".
    iMod ("Close" $! (uniq_cell x₀ d' g' γ) (λ π, (prfn_den r' π, (uniq_cell x₀ d' g' γ).2))
      ζl' q R with "ζl' [Gh' VS]") as "(Tok & $ & $)".
    { iIntros "ζl'". iMod ("VS" with "ζl'") as "(Ok' & Upd' & $)". iModIntro.
      iNext. iLeft. rewrite cpd_body_cell. iExists p', r'. by iFrame. }
    iModIntro. iExists x₀, κp, γ, γf, idx, (ζl ++ ζl'). iFrame "∗#". iPureIntro. by apply Hr'.
  Qed.

  (** ** Products *)

  Lemma pat_ok_prod κ p : pat_ok κ p -∗ pat_ok κ (pat_l p) ∗ pat_ok κ (pat_r p).
  Proof.
    iIntros "Ok". destruct p; simpl; try (iSplit; iApply pat_ok_leaf).
    rewrite /pat_ok /= big_sepL_app. done.
  Qed.

  (** The node of [ProdLty (OfTy ty1) (OfTy ty2)] is seen as the leaf
      [prod_ty ty1 ty2] (by the closing view shift of [prod_ofty_unfold_uniq]): at
      a structured refinement, it is blocked at [κp]; once [κp] is dead, the
      components are unblocked. *)
  Lemma prod_node_leaf {𝔄 𝔅} κp (ty1: type 𝔄) (ty2: type 𝔅) p r d g tid l :
    llft_ctx -∗ pat_ok κp p -∗ ⧖(S d `max` g) -∗
    prod_node (ty_size ty1) (leaf_owned false 0 ty1 (pat_l p))
      (leaf_owned false 0 ty2 (pat_r p)) r d g tid l -∗
    leaf_node κp (prod_ty ty1 ty2) p r d g tid l.
  Proof.
    iIntros "#LFT #Ok #⧖ N". destruct r as [lr|[r1 r2]]; [done|].
    iDestruct (pat_ok_prod with "Ok") as "[Ok1 Ok2]".
    destruct r1 as [lr1|]; [|by iDestruct "N" as "[[] _]"].
    destruct r2 as [lr2|]; [|by iDestruct "N" as "[_ []]"].
    iDestruct "N" as "[N1 N2]".
    rewrite /leaf_node /= /blocked_owned. iIntros "#†κ". iModIntro.
    iIntros (G ?) "#Gty G".
    iAssert (G &&{↑NllftG}&&> @[ty_lft ty1])%I as "#Gty1".
    { iApply (guards_transitive with "Gty"). simpl. rewrite lft_intersect_list_app.
      iApply llftl_intersect_incl_l. }
    iAssert (G &&{↑NllftG}&&> @[ty_lft ty2])%I as "#Gty2".
    { iApply (guards_transitive with "Gty"). simpl. rewrite lft_intersect_list_app.
      iApply llftl_intersect_incl_r. }
    iMod (leaf_owned_unblock with "LFT Gty1 Ok1 †κ G ⧖ N1")
      as "[G (%x1 & %d1 & %g1 & Rel1 & #⧖1 & Pt1 & Gho1)]".
    iMod (leaf_owned_unblock with "LFT Gty2 Ok2 †κ G ⧖ N2")
      as "[$ (%x2 & %d2 & %g2 & Rel2 & #⧖2 & Pt2 & Gho2)]".
    iModIntro. iExists (x1, x2), (d1 `max` d2), (g1 `max` g2).
    iDestruct (place_rfn_rel_eqz with "Rel1") as "Eqz1".
    iDestruct (place_rfn_rel_eqz with "Rel2") as "Eqz2".
    iSplitL "Eqz1 Eqz2".
    { rewrite /place_rfn_rel. iNext. iApply (proph_eqz_prod with "[Eqz1] [Eqz2]").
      - iApply (proph_eqz_eq with "Eqz1"); [|done]. fun_ext=> π /=. by rewrite prfn_den_inl.
      - iApply (proph_eqz_eq with "Eqz2"); [|done]. fun_ext=> π /=. by rewrite prfn_den_inl. }
    iCombine "⧖1 ⧖2" as "⧖3".
    iSplit. { iApply (persistent_time_receipt_mono with "⧖3"). lia. }
    rewrite /ofty_owned /= heap_cloc_mapsto_fancy_vec_app ty_size_eq. iFrame "Pt1 Pt2".
    iSplitL "Gho1".
    - iDestruct (ty_gho_own_depth_mono _ _ _ (d1 `max` d2) (g1 `max` g2) with "Gho1")
        as "[$ _]"; lia.
    - iDestruct (ty_gho_own_depth_mono _ _ _ (d1 `max` d2) (g1 `max` g2) with "Gho2")
        as "[$ _]"; lia.
  Qed.

  (** Unfolding a product behind a unique borrow: the body of the borrow is switched
      to the node of [ProdLty (OfTy ty1) (OfTy ty2)], keeping the prophecy variable,
      the value and the depths. *)
  Lemma prod_ofty_unfold_uniq {𝔄 𝔅} (ty1: type 𝔄) (ty2: type 𝔅) κ ξi x1 x2 d g tid l E G :
    Timeless G → ↑Nllft ∪ ↑prophN ⊆ E →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗ G -∗
    ltype_own (Uniq κ ξi) (OfTy (prod_ty ty1 ty2)) (inl (PlaceIn (𝔄:=𝔄 * 𝔅) (x1, x2))) d g tid l
      ={E}=∗
    ltype_own (Uniq κ ξi) (ProdLty (OfTy ty1) (OfTy ty2))
      (inr (inl (PlaceIn x1), inl (PlaceIn x2))) d g tid l ∗ G.
  Proof.
    iIntros (??) "#LFT #PROPH #UNIQ #Gk G H". rewrite /ltype_own /=.
    iDestruct "H" as (x idx ->) "(%κp & %γ & #Incl & (Gh & Tok) & ⧗ & #Bor)".
    iMod (ghost_var_alloc (lstate_triv (𝔄:=unitₛ) ())) as (γf) "Tf".
    set node := (λ p', prod_node (ty_size ty1)
      (leaf_owned false 0 ty1 (pat_l p')) (leaf_owned false 0 ty2 (pat_r p'))).
    set ty := prod_ty ty1 ty2.
    iMod (proph_idx_bor_gen_acc_rebody_guarded E κ (uniq_prvar (𝔄:=𝔄 * 𝔅) (x1, x2) ξi)
      (uniq_cell (𝔄:=𝔄 * 𝔅) (x1, x2) d g γ) idx (uniq_gbody κp ty tid l)
      (cpd_gbody κp γf ty node tid l) with "LFT UNIQ Gk Tok Bor G") as (wπ) "[Body Close]";
      [solve_ndisj|].
    iMod (uniq_gbody_triv_open with "Gh Body") as "(%Hw & Gh & Gh' & Pl)".
    set r : prfn (𝔄 * 𝔅) := inr (inl (PlaceIn x1), inl (PlaceIn x2)).
    iMod (ghost_var_update_halves (lstate (PatProd PatLeaf PatLeaf) r) with "Gh Gh'")
      as "[Gh Gh']".
    iSpecialize ("Close" $! (uniq_cell (𝔄:=𝔄 * 𝔅) (x1, x2) d g γ) wπ).
    iMod (fupd_mask_mono with "(Close [Gh' Pl] [])") as (idx') "(Tok & #Bor' & G)";
      [solve_ndisj| | |].
    { iNext. iLeft. rewrite cpd_body_cell. iExists (PatProd PatLeaf PatLeaf), r.
      iFrame "Gh'". iSplit; [by rewrite /pat_ok|]. iSplit.
      { iPureIntro. intros π. by rewrite Hw /r /= !prfn_den_in. }
      rewrite uniq_payload_cell. iApply (guarded_upd_mono with "[] Pl").
      iIntros "($ & Gho & Pt) !>". rewrite /= heap_cloc_mapsto_fancy_vec_app ty_size_eq.
      iDestruct "Pt" as "[Pt1 Pt2]". iDestruct "Gho" as "[Gho1 Gho2]".
      iSplitL "Pt1 Gho1"; [iExists x1|iExists x2]; by iFrame. }
    { (* Back to the body of [&uniq], at the same state. *)
      iIntros "!>" (c2 w2) "Q". iModIntro. iNext.
      iDestruct "Q" as "[Q|[_ $]]". rewrite /cpd_body /uniq_gbody /cpd_body.
      iDestruct "Q" as (p2 r2) "(#Ok & % & Gh & Upd)". iExists p2, r2. iFrame "Ok Gh".
      iSplit; [done|]. iApply (guarded_upd_mono with "[] Upd").
      iIntros "[#⧖ N] !>". iFrame "⧖". iApply (prod_node_leaf with "LFT Ok ⧖ N"). }
    (* Reserve for no prophecy variable: the leaves are not prophetic. *)
    iMod (proph_idx_bor_gen_reserve E κ _ _ idx' [] 1%Qp with "LFT PROPH UNIQ Gk G [] Tok Bor'")
      as "(Tok & _ & $)"; [solve_ndisj|done|].
    iModIntro. iExists (x1, x2), κp, γ, γf, idx', []. iFrame "∗#". iPureIntro.
    split; apply prfn_rsv_in.
  Qed.

  (** Folding back. *)
  Lemma prod_ofty_fold_uniq {𝔄 𝔅} (ty1: type 𝔄) (ty2: type 𝔅) κ ξi x1 x2 d g tid l E G :
    Timeless G → ↑Nllft ∪ ↑prophN ⊆ E →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗ G -∗
    ltype_own (Uniq κ ξi) (ProdLty (OfTy ty1) (OfTy ty2))
      (inr (inl (PlaceIn x1), inl (PlaceIn x2))) d g tid l ={E}=∗
    ltype_own (Uniq κ ξi) (OfTy (prod_ty ty1 ty2)) (inl (PlaceIn (𝔄:=𝔄 * 𝔅) (x1, x2))) d g tid l ∗ G.
  Proof.
    iIntros (??) "#LFT #PROPH #UNIQ #Gk G H". rewrite /ltype_own /=.
    iDestruct "H" as (x₀ κp γ γf idx ζl) "(#Incl & _ & Tok & Gh & Tf & ⧗ & #Bor)".
    iMod (proph_idx_bor_gen_unreserve with "LFT PROPH UNIQ Gk G Tok Bor") as "[Tok G]";
      [solve_ndisj|].
    set ty := prod_ty ty1 ty2.
    have ?: Inhabited (~~𝔄) := populate x1. have ?: Inhabited (~~𝔅) := populate x2.
    iMod (proph_idx_bor_gen_acc_rebody_guarded E κ (uniq_prvar x₀ ξi) (uniq_cell x₀ d g γ) idx
      _ (uniq_gbody κp ty tid l)
      with "LFT UNIQ Gk Tok Bor G") as (wπ) "[Body Close]"; [solve_ndisj|].
    iDestruct (bi.later_or with "Body") as "[Body|[>Tf' _]]"; last first.
    { iDestruct (cpd_tok_excl with "Tf Tf'") as "[]". }
    rewrite cpd_body_cell.
    iMod (bi.later_exist_except_0 with "Body") as (p) "Body".
    iMod (bi.later_exist_except_0 with "Body") as (r) "(_ & _ & >Gh' & Upd)".
    iDestruct (ghost_var_agree with "Gh Gh'") as %[<- <-]%lstate_inj.
    iMod (ghost_var_update_halves (lstate_triv (𝔄:=𝔄 * 𝔅) (x1, x2)) with "Gh Gh'")
      as "[Gh Gh']".
    iSpecialize ("Close" $! (uniq_cell (𝔄:=𝔄 * 𝔅) (x1, x2) d g γ)
      (vπ (uniq_cell (𝔄:=𝔄 * 𝔅) (x1, x2) d g γ))).
    iMod (fupd_mask_mono with "(Close [Gh' Upd] [Tf])") as (idx') "(Tok & #Bor' & $)";
      [solve_ndisj| | |].
    { iApply (uniq_gbody_triv_close with "Gh'"); [done|]. iNext.
      rewrite uniq_payload_cell. iApply (guarded_upd_mono with "[] Upd").
      iIntros "($ & (%y1 & -> & Pt1 & Gho1) & (%y2 & -> & Pt2 & Gho2)) !>".
      rewrite /= heap_cloc_mapsto_fancy_vec_app ty_size_eq. iFrame. }
    { iIntros "!>" (c2 w2) "P". iModIntro. iNext. iRight. iFrame. }
    iModIntro. iExists (x1, x2), idx'. iSplit; [done|].
    iApply (uniq_body_from_parts with "Incl [Gh Tok] ⧗ [Bor']").
    - rewrite /uniq_tokγ (uniq_bor_tok_retarget _ x₀). iFrame.
    - by rewrite /uniq_persγ (uniq_idx_bor_gen_retarget _ _ x₀).
  Qed.

  (** ** Switching the node of a compound place

      The node of the body of a compound place in [Uniq] mode is the interpretation of
      its core. When a subplace is unfolded (or folded), the core changes, so the body
      is switched to the new node ([node']), keeping the prophecy variable, the
      value, the ghost variable of the state and the reservation. The closing view
      shift of the new body goes back to the body of [&uniq] at the folded type, at
      the same state (as the closing view shift of [prod_ofty_unfold_uniq]), given a
      conversion of the new node into the leaf node; the token of the old body is
      given up for this. *)
  Lemma cpd_rebody {𝔄} κ ξi (ty: type 𝔄) p
      (node node': lpat → prfn 𝔄 → nat → nat → thread_id → cloc → iProp Σ)
      (r: prfn 𝔄) d g tid l E G :
    Timeless G → ↑Nllft ∪ ↑prophN ⊆ E →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗ G -∗
    cpd_own κ ξi ty p node r d g tid l ={E}=∗ ∃ κp,
      uniq_pat_lft κ κp ∗ ▷ pat_ok κp p ∗
      ▷ guarded_upd lazyE @[ty_lft ty] (⧖(S d `max` g) ∗ node p r d g tid l) ∗
      (∀ p' (r': prfn 𝔄) d' g',
         ⌜∀ ζl, prfn_rsv r ζl → prfn_rsv r' ζl⌝ -∗
         □ (∀ p2 r2 d2 g2, pat_ok κp p2 -∗ ⧖(S d2 `max` g2) -∗ node' p2 r2 d2 g2 tid l -∗
              leaf_node κp ty p2 r2 d2 g2 tid l) -∗
         ▷ pat_ok κp p' -∗
         ▷ guarded_upd lazyE @[ty_lft ty] (⧖(S d' `max` g') ∗ node' p' r' d' g' tid l) ={E}=∗
         cpd_own κ ξi ty p' node' r' d' g' tid l ∗ G).
  Proof.
    iIntros (??) "#LFT #PROPH #UNIQ #Gk G".
    iIntros "(%x₀ & %κp & %γ & %γf & %idx & %ζl & #Incl & %Hr & Tok & Gh & Tf & ⧗ & #Bor)".
    iMod (proph_idx_bor_gen_rsv_acc with "LFT UNIQ Gk Tok Bor G") as (wπ) "[Body Close]";
      [solve_ndisj|].
    iDestruct (bi.later_or with "Body") as "[Body|[>Tf' _]]"; last first.
    { iDestruct (cpd_tok_excl with "Tf Tf'") as "[]". }
    rewrite cpd_body_cell.
    iMod (bi.later_exist_except_0 with "Body") as (p1) "Body".
    iMod (bi.later_exist_except_0 with "Body") as (r1) "(#Ok & _ & >Gh' & Upd)".
    iDestruct (ghost_var_agree with "Gh Gh'") as %[<- <-]%lstate_inj.
    iModIntro. iExists κp. iFrame "Incl Ok Upd".
    iIntros (p' r' d' g' Hr') "#Conv Ok' Upd'".
    iMod (ghost_var_update_halves (lstate p' r') with "Gh Gh'") as "[Gh Gh']".
    iMod (ghost_var_alloc (lstate_triv (𝔄:=unitₛ) ())) as (γf') "Tf'".
    iSpecialize ("Close" $! (uniq_cell x₀ d' g' γ)
      (λ π, (prfn_den r' π, (uniq_cell x₀ d' g' γ).2)) (cpd_gbody κp γf' ty node' tid l)).
    iMod (fupd_mask_mono with "(Close [Tf] [Gh' Ok' Upd'])") as (idx') "(Tok & #Bor' & $)";
      [solve_ndisj| | |].
    { (* Back to the body of [&uniq] at the same state, giving up the old token. *)
      iIntros "!>" (c2 w2) "Q". iModIntro. iNext. iRight. iFrame "Tf".
      iDestruct "Q" as "[Q|[_ $]]". rewrite /uniq_gbody /cpd_body.
      iDestruct "Q" as (p2 r2) "(#Ok2 & % & Gh2 & Upd2)". iExists p2, r2. iFrame "Ok2 Gh2".
      iSplit; [done|]. iApply (guarded_upd_mono with "[] Upd2").
      iIntros "[#⧖ N] !>". iFrame "⧖". iApply ("Conv" with "Ok2 ⧖ N"). }
    { iNext. iLeft. rewrite cpd_body_cell. iExists p', r'. iFrame "Ok' Gh' Upd'".
      by iPureIntro. }
    iModIntro. iExists x₀, κp, γ, γf', idx', ζl. iFrame "∗#". iPureIntro. by apply Hr'.
  Qed.

  (** ** Simple place types

      Place types built from leaves and products. In [Owned] mode, such a place can be
      unblocked and folded inside a lazy update, once all its blocked lifetimes are
      dead (via the membership condition). *)
  Fixpoint lty_simple {𝔄} (lt: lty 𝔄) : Prop :=
    match lt with
    | OfTy _ | Blocked _ _ => True
    | ProdLty lt1 lt2 => lty_simple lt1 ∧ lty_simple lt2
    | _ => False
    end.

  Lemma ltype_owned_unblock_fold {𝔄} (lt: lty 𝔄) κ m p r d g tid l G :
    lty_simple lt → Timeless G →
    llft_ctx -∗ (G &&{↑NllftG}&&> @[ty_lft (lty_fold lt)]) -∗ pat_ok κ p -∗ [†κ] -∗ G -∗
    ⧖(S d `max` g) -∗ ltype_own_cp false lt (Owned m) p r d g tid l ={lazyE}=∗
      G ∗ ∃ x d' g', ▷ (prfn_den r :== vπ x) ∗ ⧖(S d' `max` g') ∗
        ofty_owned m (lty_fold lt) x d' g' tid l.
  Proof.
    induction lt as [𝔄 ty|𝔄 ty α|𝔄 lt IH κ'|𝔄 n lt IH|𝔄 𝔅 lt1 IH1 lt2 IH2]
      in p, r, d, g, l, G |- *; intros Hs ?; try done.
    - iIntros "#LFT #Gty #Ok #†κ G #⧖ L". destruct r as [lr|]; [|done].
      iMod (leaf_owned_unblock with "LFT Gty Ok †κ G ⧖ L")
        as "[$ (%x & %d' & %g' & Rel & ⧖' & O)]".
      iModIntro. iExists x, d', g'. iFrame. rewrite prfn_den_inl.
      by iApply place_rfn_rel_eqz.
    - iIntros "#LFT #Gty #Ok #†κ G #⧖ L". destruct r as [lr|]; [|done].
      iMod (leaf_owned_unblock with "LFT Gty Ok †κ G ⧖ L")
        as "[$ (%x & %d' & %g' & Rel & ⧖' & O)]".
      iModIntro. iExists x, d', g'. iFrame. rewrite prfn_den_inl.
      by iApply place_rfn_rel_eqz.
    - destruct Hs as [Hs1 Hs2]. iIntros "#LFT #Gty #Ok #†κ G #⧖ N".
      destruct r as [lr|[r1 r2]]; [done|]. iDestruct "N" as "[N1 N2]".
      iDestruct (pat_ok_prod with "Ok") as "[Ok1 Ok2]".
      iAssert (G &&{↑NllftG}&&> @[ty_lft (lty_fold lt1)])%I as "#Gty1".
      { iApply (guards_transitive with "Gty"). simpl. rewrite lft_intersect_list_app.
        iApply llftl_intersect_incl_l. }
      iAssert (G &&{↑NllftG}&&> @[ty_lft (lty_fold lt2)])%I as "#Gty2".
      { iApply (guards_transitive with "Gty"). simpl. rewrite lft_intersect_list_app.
        iApply llftl_intersect_incl_r. }
      iMod (IH1 with "LFT Gty1 Ok1 †κ G ⧖ N1") as "[G (%x1 & %d1 & %g1 & Eqz1 & #⧖1 & Pt1 & Gho1)]";
        [done|].
      iMod (IH2 with "LFT Gty2 Ok2 †κ G ⧖ N2") as "[$ (%x2 & %d2 & %g2 & Eqz2 & #⧖2 & Pt2 & Gho2)]";
        [done|].
      iModIntro. iExists (x1, x2), (d1 `max` d2), (g1 `max` g2).
      iSplitL "Eqz1 Eqz2". { iNext. iApply (proph_eqz_prod with "[Eqz1] [Eqz2]").
        - iApply (proph_eqz_eq with "Eqz1"); [|done]. by fun_ext=> π /=.
        - iApply (proph_eqz_eq with "Eqz2"); [|done]. by fun_ext=> π /=. }
      iCombine "⧖1 ⧖2" as "⧖3".
      iSplit. { iApply (persistent_time_receipt_mono with "⧖3"). lia. }
      rewrite /ofty_owned /= heap_cloc_mapsto_fancy_vec_app ty_size_eq -!lty_size_fold.
      iFrame "Pt1 Pt2". iNext. iSplitL "Gho1".
      + iDestruct (ty_gho_own_depth_mono _ _ _ (d1 `max` d2) (g1 `max` g2) with "Gho1")
          as "[$ _]"; lia.
      + iDestruct (ty_gho_own_depth_mono _ _ _ (d1 `max` d2) (g1 `max` g2) with "Gho2")
          as "[$ _]"; lia.
  Qed.

  (** The node of a simple place is seen as the leaf of its folded type, as in
      [prod_node_leaf]: at a structured refinement, it is blocked at [κp]. *)
  Lemma ltype_owned_leaf_node {𝔄} (lt: lty 𝔄) κp p r d g tid l :
    lty_simple lt →
    llft_ctx -∗ pat_ok κp p -∗ ⧖(S d `max` g) -∗
    ltype_own_cp false lt (Owned 0) p r d g tid l -∗ leaf_node κp (lty_fold lt) p r d g tid l.
  Proof.
    iIntros (Hs) "#LFT #Ok #⧖ N".
    destruct lt as [𝔄 ty|𝔄 ty α|𝔄 lt κ'|𝔄 n lt|𝔄 𝔅 lt1 lt2]; try done.
    - destruct r as [lr|]; [done|done].
    - destruct r as [lr|]; [done|done].
    - destruct r as [lr|rs]; [done|].
      iEval (rewrite /leaf_node /= /blocked_owned). iIntros "#†κ !>" (G ?) "#Gty G".
      iMod (ltype_owned_unblock_fold (ProdLty lt1 lt2) with "LFT Gty Ok †κ G ⧖ N")
        as "[$ (%x & %d' & %g' & Eqz & ⧖' & O)]"; [done|].
      iModIntro. iExists x, d', g'. iFrame.
  Qed.
End cpd.
