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
  - [ProdLty lt1 lt2]: a pair of places;
  - [ShrBlocked ty κ]: the place is shared until [κ] ends (its value does not change
    and it can still be read), afterwards it contains a value of type [ty] again
    ([shr_blocked_owned]; RefinedRust's [ShrBlockedLtype]);
  - [SumLty tyl i lt]: a sum of the variant [i], whose payload has the place type [lt]
    ([sum_node]: the tag, the payload and the padding; RefinedRust's [EnumLtype]). Its
    folded type is [Σ! tyl] with the type of variant [i] replaced by the folded type of
    [lt] ([hlist_set]), so that folding needs no side condition; its refinement is the
    refinement of the payload and the padding ([prfn_sum]);
  - [ShrLty lt κ]: the place contains a shared reference [&shr{κ}] whose referent is
    viewed as the place type [lt] (a read-only view, the context step [PShr] of
    [typing/lpath.v]): it is the leaf of its folded type [&shr{κ} (lty_fold lt)], together
    with the variants of the sums of [lt] at the (unchanging) referent ([lty_vin]).
  [lty_core] replaces [Blocked ty κ] and [ShrBlocked ty κ] by [OfTy ty] (pointwise
  otherwise), as
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
  and [UniqLty (OfTy ty) κ] is equivalent to [OfTy (&uniq{κ} ty)] together with
  two cumulative time receipts ([uniq_ofty_unfold_own], [uniq_ofty_fold_own]). At [Uniq] mode, a product is
  unfolded _behind an existing unique borrow_ ([prod_ofty_unfold_uniq]): the body
  of the borrow is switched (with a lifetime guard, without a new borrow and
  without changing the prophecy variable) from the leaf [prod_ty ty1 ty2] to the
  node [ProdLty (OfTy ty1) (OfTy ty2)], and back ([prod_ofty_fold_uniq]). The
  closing view shift of the unfolding converts the compound body back into the
  [&uniq] body at the same state: a leaf sees a state with a structured
  refinement as blocked at the pattern lifetime [κp] ([leaf_node]), whose
  inheritance unblocks the components (the membership condition [pat_ok κp]
  makes their blocked lifetimes end before [κp]).

  Owned pointers behind a unique borrow are folded back with shifted receipts (see
  [ltype_owned_unblock_fold]). A unique borrow behind a unique borrow is folded back
  lazily, by folding the nested compound place inside the lazy update of the leaf
  ([uniq_node_unblock_fold]); this relies on the nested membership condition (the
  blocked lifetimes of the nested place are included in the pattern lifetime of the
  outer borrow, see [pat_blk_lfts]) and on the two cumulative time receipts held by
  the node of [UniqLty]. *)

From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import ghost_var.
From lrust.typing Require Export type.
From lrust.typing Require Import uniq_util uniq_bor own product freeable_util sum type_sum shr_bor.
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
  | ProdLty {𝔄 𝔅} (lt1: lty 𝔄) (lt2: lty 𝔅) : lty (𝔄 * 𝔅)
  | ShrBlocked {𝔄} (ty: type 𝔄) (κ: lft) : lty 𝔄
  | SumLty {𝔄l} (tyl: typel 𝔄l) (i: fin (length 𝔄l)) (lt: lty (𝔄l !!ₗ i)) : lty (Σ! 𝔄l)
  | ShrLty {𝔄} (lt: lty 𝔄) (κ: lft) : lty (at_clocₛ 𝔄)
  | OfRes {𝔄} (ty: type 𝔄) : lty 𝔄
  | ResUniqLty {𝔄} (lt: lty 𝔄) (κ: lft) : lty (uniq_borₛ 𝔄).

  Fixpoint lty_core {𝔄} (lt: lty 𝔄) : lty 𝔄 :=
    match lt in lty 𝔄 return lty 𝔄 with
    | OfTy ty => OfTy ty
    | Blocked ty _ => OfTy ty
    | UniqLty lt κ => UniqLty (lty_core lt) κ
    | OwnPtrLty n lt => OwnPtrLty n (lty_core lt)
    | ProdLty lt1 lt2 => ProdLty (lty_core lt1) (lty_core lt2)
    | ShrBlocked ty _ => OfTy ty
    | SumLty tyl i lt => SumLty tyl i (lty_core lt)
    | ShrLty lt κ => ShrLty (lty_core lt) κ
    | OfRes ty => OfRes ty
    | ResUniqLty lt κ => ResUniqLty (lty_core lt) κ
    end.

  Fixpoint lty_pat {𝔄} (lt: lty 𝔄) : lpat :=
    match lt with
    | OfTy _ => PatLeaf
    | Blocked _ κ => PatBlocked κ
    | UniqLty lt _ => PatUniq (lty_pat lt)
    | OwnPtrLty _ lt => PatOwn (lty_pat lt)
    | ProdLty lt1 lt2 => PatProd (lty_pat lt1) (lty_pat lt2)
    | ShrBlocked _ κ => PatShrBlocked κ
    | SumLty _ _ lt => PatSum (lty_pat lt)
    | ShrLty _ _ => PatLeaf
    | OfRes _ => PatLeaf
    | ResUniqLty lt _ => PatUniq (lty_pat lt)
    end.

  (** The type of a place, once folded. *)
  Fixpoint lty_fold {𝔄} (lt: lty 𝔄) : type 𝔄 :=
    match lt in lty 𝔄 return type 𝔄 with
    | OfTy ty => ty
    | Blocked ty _ => ty
    | UniqLty lt κ => uniq_bor κ (lty_fold lt)
    | OwnPtrLty n lt => own_ptr n (lty_fold lt)
    | ProdLty lt1 lt2 => prod_ty (lty_fold lt1) (lty_fold lt2)
    | ShrBlocked ty _ => ty
    | SumLty tyl i lt => xsum_ty (hlist_set tyl i (lty_fold lt))
    | ShrLty lt κ => shr_bor κ (lty_fold lt)
    | OfRes ty => ty
    | ResUniqLty lt κ => uniq_bor κ (lty_fold lt)
    end.

  Fixpoint lty_size {𝔄} (lt: lty 𝔄) : nat :=
    match lt with
    | OfTy ty | Blocked ty _ | ShrBlocked ty _ | OfRes ty => ty.(ty_size)
    | UniqLty _ _ | OwnPtrLty _ _ | ShrLty _ _ | ResUniqLty _ _ => 1
    | ProdLty lt1 lt2 => lty_size lt1 + lty_size lt2
    | SumLty tyl i lt => S (max_hlist_set (λ _, ty_size) tyl i (lty_size lt))
    end.

  Fixpoint lty_lfts {𝔄} (lt: lty 𝔄) : list lft :=
    match lt with
    | OfTy ty | Blocked ty _ | ShrBlocked ty _ | OfRes ty => ty.(ty_lfts)
    | UniqLty lt κ | ResUniqLty lt κ => κ :: lty_lfts lt
    | OwnPtrLty _ lt => lty_lfts lt
    | ProdLty lt1 lt2 => lty_lfts lt1 ++ lty_lfts lt2
    | SumLty tyl i lt => tyl_lfts (hlist_set tyl i (lty_fold lt))
    | ShrLty lt κ => κ :: lty_lfts lt
    end.

  Definition lty_blocked_lfts {𝔄} (lt: lty 𝔄) : list lft := pat_blk_lfts (lty_pat lt).

  (** Leaves (unblocked, blocked or shared-blocked). The view of a nested unique borrow
      whose referent is a leaf keeps what its folding needs ([view_uniq]). *)
  Definition lty_leafb {𝔄} (lt: lty 𝔄) : bool :=
    match lt with OfTy _ | Blocked _ _ | ShrBlocked _ _ => true | _ => false end.

  Lemma lty_core_idemp {𝔄} (lt: lty 𝔄) : lty_core (lty_core lt) = lty_core lt.
  Proof. induction lt; simpl; rewrite ?IHlt ?IHlt1 ?IHlt2; done. Qed.

  Lemma lty_size_core {𝔄} (lt: lty 𝔄) : lty_size (lty_core lt) = lty_size lt.
  Proof. induction lt; simpl; rewrite ?IHlt ?IHlt1 ?IHlt2; done. Qed.

  Lemma lty_fold_core {𝔄} (lt: lty 𝔄) : lty_fold (lty_core lt) = lty_fold lt.
  Proof. induction lt; simpl; rewrite ?IHlt ?IHlt1 ?IHlt2; done. Qed.

  Lemma lty_lfts_core {𝔄} (lt: lty 𝔄) : lty_lfts (lty_core lt) = lty_lfts lt.
  Proof. induction lt; simpl; rewrite ?lty_fold_core ?IHlt ?IHlt1 ?IHlt2; done. Qed.

  Lemma lty_size_fold {𝔄} (lt: lty 𝔄) : lty_size lt = ty_size (lty_fold lt).
  Proof.
    induction lt; simpl; rewrite ?IHlt ?IHlt1 ?IHlt2; try done.
    by rewrite max_hlist_with_hlist_set.
  Qed.

  Lemma lty_lfts_fold {𝔄} (lt: lty 𝔄) : lty_lfts lt = ty_lfts (lty_fold lt).
  Proof. induction lt; simpl; rewrite ?IHlt ?IHlt1 ?IHlt2; done. Qed.

  (** The folded type of a sum place whose payload is the leaf of its variant. *)
  Lemma lty_fold_sum_ofty {𝔄l} (tyl: typel 𝔄l) i :
    lty_fold (SumLty tyl i (OfTy (tyl +!! i))) = xsum_ty tyl.
  Proof. by rewrite /= hlist_set_hlookup. Qed.

  Lemma lty_size_sum_ofty {𝔄l} (tyl: typel 𝔄l) i :
    lty_size (SumLty tyl i (OfTy (tyl +!! i))) = ty_size (xsum_ty tyl).
  Proof. by rewrite lty_size_fold lty_fold_sum_ofty. Qed.

  (** The value [x] is of the variants of the sums of [lt]. This is the information that
      the place type of the referent of a shared reference ([ShrLty]) carries beyond its
      folded type: the referent does not change, so a case analysis below a shared
      reference can record the variant. *)
  Fixpoint lty_vin {𝔄} (lt: lty 𝔄) : ~~𝔄 → Prop :=
    match lt in lty 𝔄 return ~~𝔄 → Prop with
    | OfTy _ | Blocked _ _ | ShrBlocked _ _ | OfRes _ => λ _, True
    | UniqLty lt _ | ResUniqLty lt _ => λ x, lty_vin lt (uniq_bor_current x)
    | OwnPtrLty _ lt => λ x, lty_vin lt x.2
    | ProdLty lt1 lt2 => λ x, lty_vin lt1 x.1 ∧ lty_vin lt2 x.2
    | SumLty _ i lt => λ x,
        match psum_proj i x.1 with Some y => lty_vin lt y | None => False end
    | ShrLty lt _ => λ x, lty_vin lt (snd x)
    end.

  Lemma lty_vin_core {𝔄} (lt: lty 𝔄) : lty_vin (lty_core lt) = lty_vin lt.
  Proof. induction lt; simpl; rewrite ?IHlt ?IHlt1 ?IHlt2; done. Qed.

  (** [lty_vin] at the current value of a refinement (of a leaf). *)
  Definition prfn_vin {𝔄} (P: ~~𝔄 → Prop) (r: prfn 𝔄) : Prop :=
    match r with inl (PlaceIn x) => P x | _ => True end.
End lty.

(** * Interpretation *)

Section ltype_own.
  Context `{!typeG Σ}.

  (** ** Leaves in [Uniq] mode *)

  Definition ofty_uniq {𝔄} (κ: lft) (ξi: positive) (ty: type 𝔄) (lr: place_rfn 𝔄)
      (d g: nat) (tid: thread_id) (l: cloc) : iProp Σ :=
    ∃ x idx, place_rfn_rel lr x ∗ uniq_body ty x ξi d g idx κ tid l.

  (** A blocked leaf in [Uniq] mode: the borrow itself is blocked; its inheritance
      gives back _pending_ ownership of the borrow, as [blocked_owned]. Settling the
      restored borrow needs the borrow lifetime [κ] alive, hence the guard for
      [κ ⊓ ty_lft ty]. *)
  Definition blocked_uniq {𝔄} (κ: lft) (ξi: positive) (ty: type 𝔄) (α: lft)
      (lr: place_rfn 𝔄) (tid: thread_id) (l: cloc) : iProp Σ :=
    [†α] ={lazyE}=∗ guarded_upd lazyE @[κ ⊓ ty_lft ty]
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

  (** ** Shared-blocked leaves in [Owned] mode

      A leaf shared at [α] (by a shared borrow of the place, see [typing/place_shr.v]):
      its value [x] does not change; the points-to and the ownership predicate are
      lent to [α] (a full borrow, which has been turned into a guard of the points-to
      and the sharing predicate of [ty] at [α]), and the inheritance gives them back
      once [α] has ended. The persistent predicate of the value is kept (to get the
      guards of its prophecy tokens from the sharing predicate, [ty_shr_guard_proph],
      when the place is resolved while the leaf is shared). The sharing information is persistent, so the leaf can still
      be read while [α] is alive. As in RefinedRust's [ShrBlockedLtype]. *)
  Definition shr_blocked_owned {𝔄} (m: nat) (ty: type 𝔄) (α: lft) (lr: place_rfn 𝔄)
      (d g: nat) (tid: thread_id) (l: cloc) : iProp Σ :=
    ∃ x, place_rfn_rel lr x ∗
      (@[α] &&{↑NllftG; g+1}&&> l #↦!∗ ty.(ty_phys) x tid) ∗ ty.(ty_shr) α x d g tid ∗
      ty.(ty_gho_pers) x d g tid ∗ ([†α] ={lazyE}=∗ ofty_owned m ty x d g tid l).

  (** The leaves of place types in [Owned] mode: [leaf_owned], and shared-blocked
      leaves. (The leaf bodies of unique borrows, [leaf_node], do not use shared-blocked
      leaves: a shared-blocked leaf is only part of compound places.) *)
  Definition leaf_owned_s {𝔄} (c: bool) (m: nat) (ty: type 𝔄) (p: lpat) (r: prfn 𝔄)
      (d g: nat) (tid: thread_id) (l: cloc) : iProp Σ :=
    match r with
    | inr _ => False
    | inl lr =>
        match p with
        | PatShrBlocked α =>
            if c then ∃ x, place_rfn_rel lr x ∗ ofty_owned m ty x d g tid l
            else shr_blocked_owned m ty α lr d g tid l
        | _ => leaf_owned c m ty p (inl lr) d g tid l
        end
    end%I.

  (** ** Leaves, in both modes ([c] selects the core interpretation) *)

  Definition leaf_own {𝔄} (c: bool) (k: bor_kind) (ty: type 𝔄) :
      lpat → prfn 𝔄 → nat → nat → thread_id → cloc → iProp Σ :=
    match k with
    | Owned m => leaf_owned_s c m ty
    | Uniq κ ξi => leaf_uniq c κ ξi ty
    end.

  (** ** Nodes in [Owned] mode, given the interpretations of the children *)

  Definition uniq_node {𝔅} (m: nat) (κ': lft) (ty: type 𝔅)
      (child: positive → prfn 𝔅 → nat → nat → thread_id → cloc → iProp Σ)
      (r: prfn (uniq_borₛ 𝔅)) (d g: nat) (tid: thread_id) (l: cloc) : iProp Σ :=
    match r with
    | inl _ => False
    | inr (l', r', ξi) =>
        l #↦!∗ [FVal (LitV l'.1)] ∗ ⧗(2 + m) ∗ time_ctx ∗
        ▷^m (κ' ⊑ ty_lft ty ∗ (@[κ'] &&{↑NllftG; g+1}&&> l' #↦∗_) ∗
          ∃ d' g', ⌜S d' ≤ d ∧ g' ≤ g⌝ ∗ child ξi r' d' g' tid l')
    end%I.

  Definition own_node {𝔅} (m: nat) (n sz: nat)
      (child: prfn 𝔅 → nat → nat → thread_id → cloc → iProp Σ)
      (r: prfn (at_locₛ 𝔅)) (d g: nat) (tid: thread_id) (l: cloc) : iProp Σ :=
    match r with
    | inl _ => False
    | inr (l', r') =>
        l #↦!∗ [FVal (LitV l')] ∗ ⌜d ≠ 0%nat⌝ ∗ ▷^m (freeable_sz n sz l') ∗
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

  (** The node of a sum at variant [i] (with a payload of size [sz]): the tag, the
      payload, and the padding (as in [split_pt_xsum_cells'']). The tag and the padding
      have no ghost ownership, so the node does not depend on the mode. *)
  Definition sum_node {𝔅l} (tyl: typel 𝔅l) (i: fin (length 𝔅l)) (sz: nat)
      (child: prfn (𝔅l !!ₗ i) → nat → nat → thread_id → cloc → iProp Σ)
      (r: prfn (Σ! 𝔅l)) (d g: nat) (tid: thread_id) (l: cloc) : iProp Σ :=
    match r with
    | inl _ => False
    | inr (s, pad) =>
        match psum_proj i s with
        | None => False
        | Some r' =>
            cloc_take l 1 #↦∗ [ #i ] ∗ child r' d g tid (cloc_take (cloc_skip l 1) sz) ∗
            cloc_skip (cloc_skip l 1) sz #↦!∗ fmap FVal (vec_to_list
              (padding_to_vec (max_hlist_set (λ _, ty_size) tyl i sz - sz) pad))
        end
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

  (** ** Resolved places in [Owned] mode

      A resolved place ([OfRes], [ResUniqLty]) can be read but not written: it is the
      result of resolving the leaves and the unique borrows of an owned place (see
      [typing/place_res.v]). It is only part of the owned part of a place (below no
      unique borrow, so it is never folded back for a lender, [lty_simple]); in [Uniq]
      mode its interpretation is [False]. *)

  (** A resolved leaf ([OfRes ty]): the cells and the resolved ownership of the value
      ([ty_gho_res], see [resolve_keep]), at some smaller depths. *)
  Definition res_leaf {𝔄} (m: nat) (ty: type 𝔄) (r: prfn 𝔄) (d g: nat) (tid: thread_id)
      (l: cloc) : iProp Σ :=
    match r with
    | inr _ => False
    | inl lr => ∃ x, place_rfn_rel lr x ∗ l #↦!∗ ty.(ty_phys) x tid ∗
        ▷^m (∃ d' g', ⌜d' ≤ d ∧ g' ≤ g⌝ ∗ ty.(ty_gho_res) x d' g' tid)
    end%I.

  (** The view of a leaf of the referent of a resolved unique borrow, at the lifetime [κ]:
      - an unblocked leaf is shared at [κ]: a guard of its cells, its sharing predicate
        at [κ] and its persistent predicate (the ownership predicate of [&shr{κ} ty]
        without its laters, [shr_view] of [typing/place_pshr.v]);
      - a blocked leaf keeps its inheritance, in a borrow at [κ] (it is shared at [κ] once
        it has been unblocked), with a guard of the cells of its location;
      - a shared-blocked leaf (at [α]) is shared at [κ ⊓ α]: its value does not change,
        and it is shared at [α] already (it is readable while [α] is alive); it also keeps
        its inheritance, in a borrow at [κ] (at some smaller depths), with a guard of the
        cells of its location, so that it is shared at [κ] once [α] has ended
        ([unblock_tctx_oplace_res_shr] of [typing/place_res_ops.v]). *)
  Definition view_leaf {𝔄} (κ: lft) (m: nat) (ty: type 𝔄) (p: lpat) (r: prfn 𝔄)
      (d g: nat) (tid: thread_id) (l: cloc) : iProp Σ :=
    match r with
    | inr _ => False
    | inl lr =>
        match p with
        | PatBlocked α =>
            (@[κ] &&{↑NllftG; g+1}&&> l #↦∗_) ∗ &{κ} (blocked_owned m ty α lr tid l)
        | PatShrBlocked α => ∃ x, place_rfn_rel lr x ∗
            (@[κ ⊓ α] &&{↑NllftG; g+1}&&> l.1 ↦[^ l.2]!∗ ty.(ty_phys) x tid) ∗
            ty.(ty_shr) (κ ⊓ α) x d g tid ∗ ty.(ty_gho_pers) x d g tid ∗
            (@[κ] &&{↑NllftG; g+1}&&> l #↦∗_) ∗
            ∃ d' g', ⌜d' ≤ d ∧ g' ≤ g⌝ ∗ &{κ} ([†α] ={lazyE}=∗ ofty_owned m ty x d' g' tid l)
        | _ => ∃ x, place_rfn_rel lr x ∗
            (@[κ] &&{↑NllftG; g+1}&&> l.1 ↦[^ l.2]!∗ ty.(ty_phys) x tid) ∗
            ty.(ty_shr) κ x d g tid ∗ ty.(ty_gho_pers) x d g tid
        end
    end%I.

  (** The view of a nested unique borrow (at [κ'], viewed at [κ]): a guard of its pointer
      cell, and the view of its referent at [κ ⊓ κ'] (the referent itself stays with the
      lender of [κ'], its prophecy variable is not resolved). If its referent is a leaf
      ([b], [lty_leafb]), the view also keeps a guard of the token of its prophecy
      variable at [κ ⊓ κ'] and the persistent component of its body, at some index (both
      from the sharing of [&uniq{κ'} ty] at [κ]), so that it can be folded to the sharing
      of [&uniq{κ'} ty] ([lty_view_fold] of [typing/place_res_ops.v]). (A compound
      referent has a reserved prophecy variable, whose token is not available.) *)
  Definition view_uniq {𝔅} (κ κ': lft) (ty: type 𝔅) (b: bool)
      (child: prfn 𝔅 → nat → nat → thread_id → cloc → iProp Σ)
      (r: prfn (uniq_borₛ 𝔅)) (d g: nat) (tid: thread_id) (l: cloc) : iProp Σ :=
    match r with
    | inl _ => False
    | inr (l', r', ξi) =>
        (@[κ] &&{↑NllftG; g+1}&&> l.1 ↦[^ l.2]∗ [ #l'.1]) ∗ κ' ⊑ ty_lft ty ∗
        ∃ d' g', ⌜S d' ≤ d ∧ g' ≤ g⌝ ∗ child r' d' g' tid l' ∗
          (if b then ∃ (x0: ~~𝔅) idx,
             (@[κ ⊓ κ'] &&{↑NllftG; g+1}&&> 1:[uniq_prvar x0 ξi]) ∗
             uniq_body_pers_component ty x0 ξi d' g' idx κ' tid l'
           else True)
    end%I.

  (** The view of an owned pointer: a guard of its pointer cell, and the view of its
      pointee. *)
  Definition view_own {𝔅} (κ: lft) (sz: nat)
      (child: prfn 𝔅 → nat → nat → thread_id → cloc → iProp Σ)
      (r: prfn (at_locₛ 𝔅)) (d g: nat) (tid: thread_id) (l: cloc) : iProp Σ :=
    match r with
    | inl _ => False
    | inr (l', r') =>
        (@[κ] &&{↑NllftG; g+1}&&> l.1 ↦[^ l.2]∗ [ #l']) ∗ ⌜d ≠ 0%nat⌝ ∗
        child r' (pred d) g tid (l', repeat [] sz)
    end%I.

  (** The view of a sum at variant [i]: guards of its tag and its padding, and the view of
      its payload. *)
  Definition view_sum {𝔅l} (κ: lft) (tyl: typel 𝔅l) (i: fin (length 𝔅l)) (sz: nat)
      (child: prfn (𝔅l !!ₗ i) → nat → nat → thread_id → cloc → iProp Σ)
      (r: prfn (Σ! 𝔅l)) (d g: nat) (tid: thread_id) (l: cloc) : iProp Σ :=
    match r with
    | inl _ => False
    | inr (s, pad) =>
        match psum_proj i s with
        | None => False
        | Some r' =>
            (@[κ] &&{↑NllftG; g+1}&&> (cloc_take l 1).1 ↦[^ (cloc_take l 1).2]∗ [ #i ]) ∗
            child r' d g tid (cloc_take (cloc_skip l 1) sz) ∗
            (@[κ] &&{↑NllftG; g+1}&&> (cloc_skip (cloc_skip l 1) sz).1
              ↦[^ (cloc_skip (cloc_skip l 1) sz).2]!∗ fmap FVal (vec_to_list
              (padding_to_vec (max_hlist_set (λ _, ty_size) tyl i sz - sz) pad)))
        end
    end%I.

  (** The view of the referent [lt] of a resolved unique borrow, at the lifetime [κ] (the
      lifetime of the resolved borrow, intersected with those of the nested unique
      borrows above), with [m] owned pointers above (for the inheritances of the blocked
      leaves). Persistent but for the borrows of the blocked leaves. *)
  Fixpoint lty_view {𝔄} (lt: lty 𝔄) (κ: lft) {struct lt} :
      nat → lpat → prfn 𝔄 → nat → nat → thread_id → cloc → iProp Σ :=
    match lt in lty 𝔄 return nat → lpat → prfn 𝔄 → nat → nat → thread_id → cloc → iProp Σ with
    | OfTy ty | Blocked ty _ | ShrBlocked ty _ => λ m, view_leaf κ m ty
    | UniqLty lt' κ' => λ m p,
        view_uniq κ κ' (lty_fold lt') (lty_leafb lt') (lty_view lt' (κ ⊓ κ') 0 (pat_uniq p))
    | OwnPtrLty n lt' => λ m p,
        view_own κ (lty_size lt') (lty_view lt' κ (m + 1) (pat_own p))
    | ProdLty lt1 lt2 => λ m p,
        prod_node (lty_size lt1) (lty_view lt1 κ m (pat_l p)) (lty_view lt2 κ m (pat_r p))
    | SumLty tyl i lt' => λ m p,
        view_sum κ tyl i (lty_size lt') (lty_view lt' κ m (pat_sum p))
    | ShrLty lt' κ' => λ m p r d g tid l,
        (view_leaf κ m (shr_bor κ' (lty_fold lt')) p r d g tid l ∗
          ⌜prfn_vin (λ x: ~~ (at_clocₛ _), lty_vin lt' x.2) r⌝)%I
    | OfRes _ | ResUniqLty _ _ => λ _ _ _ _ _ _ _, False%I
    end.

  (** A resolved unique borrow ([ResUniqLty lt κ']): its pointer cell, and the view of its
      referent at [κ'] (the referent itself goes back to the lender at the end of [κ']). *)
  Definition res_node {𝔅} (m: nat) (κ': lft) (ty: type 𝔅)
      (child: prfn 𝔅 → nat → nat → thread_id → cloc → iProp Σ)
      (r: prfn (uniq_borₛ 𝔅)) (d g: nat) (tid: thread_id) (l: cloc) : iProp Σ :=
    match r with
    | inl _ => False
    | inr (l', r', ξi) =>
        l #↦!∗ [FVal (LitV l'.1)] ∗
        ▷^m (κ' ⊑ ty_lft ty ∗ ∃ d' g', ⌜S d' ≤ d ∧ g' ≤ g⌝ ∗ child r' d' g' tid l')
    end%I.

  (** ** Pointer nodes without their cells

      The node of a pointer ([own_node], [uniq_node], [res_node]) is the cell of the
      pointer together with the ownership of the pointer _value_, [own_nval], [uniq_nval],
      [res_nval] ([own_node_nval], …). The root of a place rooted at a value (a pointer
      that is not in memory, [typing/vplace.v]) is the [nval] of its root pointer. *)
  Definition uniq_nval {𝔅} (m: nat) (κ': lft) (ty: type 𝔅)
      (child: positive → prfn 𝔅 → nat → nat → thread_id → cloc → iProp Σ)
      (r: prfn (uniq_borₛ 𝔅)) (d g: nat) (tid: thread_id) : iProp Σ :=
    match r with
    | inl _ => False
    | inr (l', r', ξi) =>
        ⧗(2 + m) ∗ time_ctx ∗
        ▷^m (κ' ⊑ ty_lft ty ∗ (@[κ'] &&{↑NllftG; g+1}&&> l' #↦∗_) ∗
          ∃ d' g', ⌜S d' ≤ d ∧ g' ≤ g⌝ ∗ child ξi r' d' g' tid l')
    end%I.

  Definition own_nval {𝔅} (m: nat) (n sz: nat)
      (child: prfn 𝔅 → nat → nat → thread_id → cloc → iProp Σ)
      (r: prfn (at_locₛ 𝔅)) (d g: nat) (tid: thread_id) : iProp Σ :=
    match r with
    | inl _ => False
    | inr (l', r') => ⌜d ≠ 0%nat⌝ ∗ ▷^m (freeable_sz n sz l') ∗ child r' (pred d) g tid (l', repeat [] sz)
    end%I.

  Definition res_nval {𝔅} (m: nat) (κ': lft) (ty: type 𝔅)
      (child: prfn 𝔅 → nat → nat → thread_id → cloc → iProp Σ)
      (r: prfn (uniq_borₛ 𝔅)) (d g: nat) (tid: thread_id) : iProp Σ :=
    match r with
    | inl _ => False
    | inr (l', r', ξi) =>
        ▷^m (κ' ⊑ ty_lft ty ∗ ∃ d' g', ⌜S d' ≤ d ∧ g' ≤ g⌝ ∗ child r' d' g' tid l')
    end%I.

  (** A leaf at a value (of size 1), and a resolved leaf at a value (as [res_leaf]). *)
  Definition vleaf {𝔄} (ty: type 𝔄) (r: prfn 𝔄) (d g: nat) (tid: thread_id) (v: val) : iProp Σ :=
    match r with
    | inr _ => False
    | inl lr => ∃ x, place_rfn_rel lr x ∗ ⌜ty.(ty_phys) x tid = [FVal v]⌝ ∗ ty.(ty_gho_own) x d g tid
    end%I.

  Definition vres_leaf {𝔄} (ty: type 𝔄) (r: prfn 𝔄) (d g: nat) (tid: thread_id) (v: val) : iProp Σ :=
    match r with
    | inr _ => False
    | inl lr => ∃ x, place_rfn_rel lr x ∗ ⌜ty.(ty_phys) x tid = [FVal v]⌝ ∗
        ∃ d' g', ⌜d' ≤ d ∧ g' ≤ g⌝ ∗ ty.(ty_gho_res) x d' g' tid
    end%I.

  (** ** The interpretation

      By structural recursion on the place type, with the blocking pattern
      as an argument (only the core of the place type matters). *)
  Fixpoint ltype_own_cp (c: bool) {𝔄} (lt: lty 𝔄) {struct lt} :
      bor_kind → lpat → prfn 𝔄 → nat → nat → thread_id → cloc → iProp Σ :=
    match lt in lty 𝔄 return bor_kind → lpat → prfn 𝔄 → nat → nat → thread_id → cloc → iProp Σ with
    | OfTy ty => λ k, leaf_own c k ty
    | Blocked ty _ => λ k, leaf_own c k ty
    | ShrBlocked ty _ => λ k, leaf_own c k ty
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
    | SumLty tyl i lt' => λ k p,
        match k with
        | Owned m => sum_node tyl i (lty_size lt') (ltype_own_cp c lt' (Owned m) (pat_sum p))
        | Uniq κ ξi => cpd_own κ ξi (xsum_ty (hlist_set tyl i (lty_fold lt'))) p
            (λ p', sum_node tyl i (lty_size lt') (ltype_own_cp false lt' (Owned 0) (pat_sum p')))
        end
    (* A shared reference whose referent is viewed as [lt']: the leaf of its folded type,
       and the variants of the referent (which does not change). *)
    | ShrLty lt' κ' => λ k p r d g tid l,
        (leaf_own c k (shr_bor κ' (lty_fold lt')) p r d g tid l ∗
          ⌜prfn_vin (λ x: ~~ (at_clocₛ _), lty_vin lt' x.2) r⌝)%I
    (* Resolved places, only in [Owned] mode. *)
    | OfRes ty => λ k p r d g tid l,
        match k with
        | Owned m => res_leaf m ty r d g tid l
        | Uniq _ _ => False%I
        end
    | ResUniqLty lt' κ' => λ k p,
        match k with
        | Owned m => res_node m κ' (lty_fold lt') (λ r' d' g' tid l',
            if c then (∃ p', lty_view lt' κ' 0 p' r' d' g' tid l')%I
            else lty_view lt' κ' 0 (pat_uniq p) r' d' g' tid l')
        | Uniq _ _ => λ _ _ _ _ _, False%I
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

  (** ** The interpretation at a value

      A place type whose root is a pointer ([OwnPtrLty], [UniqLty], [ResUniqLty]) or a leaf
      of size 1 ([OfTy], [OfRes], [ShrLty]), at a value [v] (not in memory): the [nval] of the
      root pointer, in [Owned 0] mode, with the value of the pointer, or the leaf at the
      value. The other place types have no interpretation at a value. *)
  Definition lty_vown {𝔄} (lt: lty 𝔄) : prfn 𝔄 → nat → nat → thread_id → val → iProp Σ :=
    match lt in lty 𝔄 return prfn 𝔄 → nat → nat → thread_id → val → iProp Σ with
    | OfTy ty => vleaf ty
    | UniqLty lt' κ' => λ r d g tid v,
        ((match r with inr (l', _, _) => ⌜v = #(l'.1)⌝ | inl _ => False end) ∗
         uniq_nval 0 κ' (lty_fold lt')
           (λ ξi r' d' g' tid l', ltype_own (Uniq κ' ξi) lt' r' d' g' tid l') r d g tid)%I
    | OwnPtrLty n lt' => λ r d g tid v,
        ((match r with inr (l', _) => ⌜v = #l'⌝ | inl _ => False end) ∗
         own_nval 0 n (lty_size lt') (ltype_own (Owned 1) lt') r d g tid)%I
    | ShrLty lt' κ' => λ r d g tid v,
        (vleaf (shr_bor κ' (lty_fold lt')) r d g tid v ∗
          ⌜prfn_vin (λ x: ~~ (at_clocₛ _), lty_vin lt' x.2) r⌝)%I
    | OfRes ty => vres_leaf ty
    | ResUniqLty lt' κ' => λ r d g tid v,
        ((match r with inr (l', _, _) => ⌜v = #(l'.1)⌝ | inl _ => False end) ∗
         res_nval 0 κ' (lty_fold lt') (lty_view lt' κ' 0 (lty_pat lt')) r d g tid)%I
    | _ => λ _ _ _ _ _, False%I
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
    iIntros "($ & $ & $ & H)". iNext. iDestruct "H" as "($ & $ & %d' & %g' & ? & C)".
    iExists d', g'. iFrame. by iApply Hc.
  Qed.

  Lemma res_node_mono {𝔅} m κ' (ty: type 𝔅)
      (c1 c2: prfn 𝔅 → nat → nat → thread_id → cloc → iProp Σ) r d g tid l :
    (∀ r' d' g' tid' l', c1 r' d' g' tid' l' ⊢ c2 r' d' g' tid' l') →
    res_node m κ' ty c1 r d g tid l ⊢ res_node m κ' ty c2 r d g tid l.
  Proof.
    intros Hc. destruct r as [?|[[l' r'] ξi]]; [done|]. rewrite /res_node.
    iIntros "($ & H)". iNext. iDestruct "H" as "($ & %d' & %g' & ? & C)".
    iExists d', g'. iFrame. by iApply Hc.
  Qed.

  Lemma own_node_mono {𝔅} m n sz (c1 c2: prfn 𝔅 → nat → nat → thread_id → cloc → iProp Σ)
      r d g tid l :
    (∀ r' d' g' tid' l', c1 r' d' g' tid' l' ⊢ c2 r' d' g' tid' l') →
    own_node m n sz c1 r d g tid l ⊢ own_node m n sz c2 r d g tid l.
  Proof.
    intros Hc. destruct r as [?|[l' r']]; [done|]. rewrite /own_node.
    iIntros "($ & $ & $ & C)". by iApply Hc.
  Qed.

  (** ** Pointer nodes are their cells and their [nval]s *)

  Lemma uniq_node_nval {𝔅} m κ' (ty: type 𝔅) child l' r' ξi d g tid l :
    uniq_node m κ' ty child (inr (l', r', ξi)) d g tid l ⊣⊢
      l #↦!∗ [FVal (LitV l'.1)] ∗ uniq_nval m κ' ty child (inr (l', r', ξi)) d g tid.
  Proof. done. Qed.

  Lemma own_node_nval {𝔅} m n sz (child: prfn 𝔅 → nat → nat → thread_id → cloc → iProp Σ)
      l' r' d g tid l :
    own_node m n sz child (inr (l', r')) d g tid l ⊣⊢
      l #↦!∗ [FVal (LitV l')] ∗ own_nval m n sz child (inr (l', r')) d g tid.
  Proof. done. Qed.

  Lemma res_node_nval {𝔅} m κ' (ty: type 𝔅) child l' r' ξi d g tid l :
    res_node m κ' ty child (inr (l', r', ξi)) d g tid l ⊣⊢
      l #↦!∗ [FVal (LitV l'.1)] ∗ res_nval m κ' ty child (inr (l', r', ξi)) d g tid.
  Proof. done. Qed.

  (** A leaf of size 1 is its cell and the leaf at the value of the cell. *)
  Lemma leaf_owned_vleaf {𝔄} (ty: type 𝔄) r d g tid (l: cloc) v :
    l #↦!∗ [FVal v] ∗ vleaf ty r d g tid v ⊢ leaf_owned_s false 0 ty PatLeaf r d g tid l.
  Proof.
    destruct r as [lr|]; [|by iIntros "[_ []]"].
    iIntros "[Pt (%x & Rel & %Hphys & Gho)]". iExists x. iFrame "Rel Gho". by rewrite Hphys.
  Qed.

  Lemma uniq_nval_mono {𝔅} m κ' (ty: type 𝔅)
      (c1 c2: positive → prfn 𝔅 → nat → nat → thread_id → cloc → iProp Σ) r d g tid :
    (∀ ξi r' d' g' tid' l', c1 ξi r' d' g' tid' l' ⊢ c2 ξi r' d' g' tid' l') →
    uniq_nval m κ' ty c1 r d g tid ⊢ uniq_nval m κ' ty c2 r d g tid.
  Proof.
    intros Hc. destruct r as [?|[[l' r'] ξi]]; [done|]. rewrite /uniq_nval.
    iIntros "($ & $ & H)". iNext. iDestruct "H" as "($ & $ & %d' & %g' & ? & C)".
    iExists d', g'. iFrame. by iApply Hc.
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

  Lemma sum_node_mono {𝔅l} (tyl: typel 𝔅l) i sz
      (c1 c2: prfn (𝔅l !!ₗ i) → nat → nat → thread_id → cloc → iProp Σ) r d g d' g' tid l :
    (∀ r' tid' l', c1 r' d g tid' l' ⊢ c2 r' d' g' tid' l') →
    sum_node tyl i sz c1 r d g tid l ⊢ sum_node tyl i sz c2 r d' g' tid l.
  Proof.
    intros Hc. destruct r as [?|[s pad]]; [done|]. rewrite /sum_node.
    case_match; [|by iIntros "[]"]. iIntros "($ & C & $)". by iApply Hc.
  Qed.

  Lemma ltype_own_cp_sum_owned c {𝔅l} (tyl: typel 𝔅l) i (lt: lty (𝔅l !!ₗ i)) m p :
    ltype_own_cp c (SumLty tyl i lt) (Owned m) p =
      sum_node tyl i (lty_size lt) (ltype_own_cp c lt (Owned m) (pat_sum p)).
  Proof. done. Qed.

  (** The node of a sum at the refinement of a payload. *)
  Lemma sum_node_sum {𝔅l} (tyl: typel 𝔅l) i sz
      (c: prfn (𝔅l !!ₗ i) → nat → nat → thread_id → cloc → iProp Σ) r pad d g tid l :
    sum_node tyl i sz c (prfn_sum i r pad) d g tid l ⊣⊢
      cloc_take l 1 #↦∗ [ #i ] ∗ c r d g tid (cloc_take (cloc_skip l 1) sz) ∗
      cloc_skip (cloc_skip l 1) sz #↦!∗ fmap FVal (vec_to_list
        (padding_to_vec (max_hlist_set (λ _, ty_size) tyl i sz - sz) pad)).
  Proof. rewrite /sum_node /prfn_sum. by rewrite psum_proj_pinj. Qed.

  (** A sum node at a structured refinement is at a payload refinement. *)
  Lemma sum_node_inv {𝔅l} (tyl: typel 𝔅l) i sz
      (c: prfn (𝔅l !!ₗ i) → nat → nat → thread_id → cloc → iProp Σ) r d g tid l :
    sum_node tyl i sz c r d g tid l -∗ ∃ r' pad, ⌜r = prfn_sum i r' pad⌝.
  Proof.
    destruct r as [?|[s pad]]; [by iIntros "[]"|]. rewrite /sum_node.
    case_match eqn:Hs; [|by iIntros "[]"]. iIntros "_".
    iExists _, pad. iPureIntro. rewrite /prfn_sum. f_equal. f_equal.
    by apply psum_proj_Some.
  Qed.

  (** ** The core *)

  Lemma lty_leafb_core {𝔄} (lt: lty 𝔄) : lty_leafb (lty_core lt) = lty_leafb lt.
  Proof. by destruct lt. Qed.

  (** Only the core of a place type matters for its view. *)
  Lemma lty_view_core {𝔄} (lt: lty 𝔄) : lty_view (lty_core lt) = lty_view lt.
  Proof.
    induction lt as [| |𝔄 lt IH κ|𝔄 n lt IH|𝔄 𝔅 lt1 IH1 lt2 IH2| |𝔄l tyl i lt IH|𝔄 lt IH κ| |];
      simpl; [done|done| | | |done| | |done|done].
    - by rewrite lty_fold_core lty_leafb_core IH.
    - by rewrite lty_size_core IH.
    - by rewrite lty_size_core IH1 IH2.
    - by rewrite lty_size_core IH.
    - by rewrite lty_fold_core lty_vin_core.
  Qed.

  (** Only the core of a place type matters for [ltype_own_cp]. *)
  Lemma ltype_own_cp_core c {𝔄} (lt: lty 𝔄) : ltype_own_cp c (lty_core lt) = ltype_own_cp c lt.
  Proof.
    induction lt as [| |𝔄 lt IH κ|𝔄 n lt IH|𝔄 𝔅 lt1 IH1 lt2 IH2| |𝔄l tyl i lt IH|𝔄 lt IH κ| |𝔄 lt IH κ]
      in c |- *; simpl; [done|done| | | |done| | |done|].
    - by rewrite lty_fold_core !IH.
    - by rewrite lty_size_core lty_fold_core !IH.
    - by rewrite lty_size_core !lty_fold_core !IH1 !IH2.
    - by rewrite lty_size_core lty_fold_core !IH.
    - by rewrite lty_fold_core lty_vin_core.
    - by rewrite lty_fold_core lty_view_core.
  Qed.

  (** In [Owned] mode, the core interpretation does not depend on the
      pattern. *)
  Lemma ltype_own_cp_true_owned_pat {𝔄} (lt: lty 𝔄) m p p' r d g tid l :
    ltype_own_cp true lt (Owned m) p r d g tid l ⊢ ltype_own_cp true lt (Owned m) p' r d g tid l.
  Proof.
    induction lt as [𝔄 ty|𝔄 ty α|𝔄 lt IH κ|𝔄 n lt IH|𝔄 𝔅 lt1 IH1 lt2 IH2|𝔄 ty α|𝔄l tyl i lt IH|𝔄 lt IH κ|𝔄 ty|𝔄 lt IH κ]
      in m, p, p', r, d, g, tid, l |- *; simpl.
    - destruct r as [lr|]; [|done]. by destruct p, p'.
    - destruct r as [lr|]; [|done]. by destruct p, p'.
    - by apply uniq_node_mono.
    - apply own_node_mono=> *. apply IH.
    - apply prod_node_mono=> *; [apply IH1|apply IH2].
    - destruct r as [lr|]; [|done]. by destruct p, p'.
    - apply sum_node_mono=> *. apply IH.
    - apply bi.sep_mono_l. destruct r as [lr|]; [|done]. by destruct p, p'.
    - done.
    - done.
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
    leaf_owned_s c m ty p r d g tid l ⊢ leaf_owned_s c m ty p r d' g' tid l.
  Proof.
    intros ??. destruct r as [lr|]; [|done].
    have Hofty: (∃ x, place_rfn_rel lr x ∗ ofty_owned m ty x d g tid l) ⊢
      ∃ x, place_rfn_rel lr x ∗ ofty_owned m ty x d' g' tid l.
    { iIntros "(%x & Rel & Pt & Gho)". iExists x. iFrame. iNext.
      iDestruct (ty_gho_own_depth_mono _ d g d' g' with "Gho") as "[$ _]"; done. }
    destruct p; try apply Hofty; destruct c; try apply Hofty.
    - rewrite /= /leaf_owned. iIntros "$".
    - rewrite /= /shr_blocked_owned. iIntros "(%x & Rel & #Pt & #Shr & #Pers & Inh)". iExists x.
      iFrame "Rel". iSplit; [iApply (lguards_weaken_later with "Pt"); lia|].
      iSplit; [iApply (ty_shr_depth_mono with "Shr"); lia|].
      iSplit; [iApply (ty_gho_pers_depth_mono with "Pers"); lia|].
      iIntros "†α". iMod ("Inh" with "†α") as "[Pt' Gho]". iModIntro. iFrame "Pt'".
      iNext. iDestruct (ty_gho_own_depth_mono _ d g d' g' with "Gho") as "[$ _]"; done.
  Qed.

  Lemma ltype_own_cp_owned_depth_mono c {𝔄} (lt: lty 𝔄) m p r d g d' g' tid l :
    d ≤ d' → g ≤ g' →
    ltype_own_cp c lt (Owned m) p r d g tid l ⊢ ltype_own_cp c lt (Owned m) p r d' g' tid l.
  Proof.
    induction lt as [𝔄 ty|𝔄 ty α|𝔄 lt IH κ|𝔄 n lt IH|𝔄 𝔅 lt1 IH1 lt2 IH2|𝔄 ty α|𝔄l tyl i lt IH|𝔄 lt IH κ|𝔄 ty|𝔄 lt IH κ]
      in m, p, r, d, g, d', g', tid, l |- *; intros Hd Hg; simpl;
      first [by apply leaf_owned_depth_mono|by apply bi.sep_mono_l, leaf_owned_depth_mono|idtac].
    4: { apply sum_node_mono=> *. by apply IH. }
    4: { destruct r as [lr|]; [|done]. rewrite /res_leaf.
      iIntros "(%x & $ & $ & H)". iNext. iDestruct "H" as (d1 g1 ?) "H".
      iExists d1, g1. iFrame. iPureIntro. lia. }
    4: { destruct r as [?|[[l' r'] ξi]]; [done|]. rewrite /res_node.
      iIntros "($ & H)". iNext. iDestruct "H" as "($ & %d1 & %g1 & %Hle & C)".
      iExists d1, g1. iFrame. iPureIntro. lia. }
    - destruct r as [?|[[l' r'] ξi]]; [done|]. rewrite /uniq_node.
      iIntros "($ & $ & $ & H)". iNext. iDestruct "H" as "($ & #G & %d1 & %g1 & %Hle & C)".
      iSplitR. { iApply (lguards_weaken_later with "G"). lia. }
      iExists d1, g1. iFrame. iPureIntro. lia.
    - destruct r as [?|[l' r']]; [done|]. rewrite /own_node.
      iIntros "($ & % & $ & C)". iSplit; [iPureIntro; lia|].
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

  (** A shared reference is a leaf (nothing below it is blocked). *)
  Lemma shr_lty_imp_unblockable κs {𝔄} (lt: lty 𝔄) κ : ⊢ imp_unblockable κs (ShrLty lt κ).
  Proof.
    iIntros "!>" (k r d g tid l G ?) "_ $ _ H". iModIntro. iExists d, g.
    destruct k as [m|κ' ξi]; [|by iApply ltype_own_uniq_core]. done.
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

  Lemma shr_blocked_imp_unblockable {𝔄} (ty: type 𝔄) α : ⊢ imp_unblockable [α] (ShrBlocked ty α).
  Proof.
    iIntros "!>" (k r d g tid l G ?) "_ G [#Dead _] H". iFrame "G".
    destruct k as [m|κ ξi]; [|iModIntro; iExists d, g; by iApply ltype_own_uniq_core].
    destruct r as [lr|]; [|done]. rewrite /ltype_own /ltype_own_core /= /shr_blocked_owned.
    iDestruct "H" as (x) "(Rel & _ & _ & _ & Inh)".
    iMod (fupd_mask_mono with "(Inh Dead)") as "O"; [rewrite /lazyE; set_solver|].
    iModIntro. iExists d, g, x. iFrame.
  Qed.

  (** Congruence. Unique borrows are trivially unblockable: implicit unblocking does
      not reach into the nested borrow, whose core interpretation is at any
      pattern. *)
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
    iDestruct "H" as "(Pt & % & Fr & C)".
    iMod ("Ub" $! (Owned (m + 1)) with "[//] Gk G Dead C") as "[$ (%d1 & %g1 & C)]".
    iModIntro. iExists (S d1), g1. by iFrame.
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

  (** The lifetime of (the folded type of) a sum place is included in the lifetime of
      its payload. *)
  Lemma lty_lft_sum {𝔄l} (tyl: typel 𝔄l) i (lt: lty (𝔄l !!ₗ i)) :
    ⊢ ty_lft (lty_fold (SumLty tyl i lt)) ⊑ ty_lft (lty_fold lt).
  Proof.
    iPoseProof (lft_intersect_tyl_lfts_lookup_incl (hlist_set tyl i (lty_fold lt)) i) as "H".
    by rewrite hlookup_hlist_set.
  Qed.

  Lemma sum_ltype_imp_unblockable κs {𝔄l} (tyl: typel 𝔄l) i (lt: lty (𝔄l !!ₗ i)) :
    imp_unblockable κs lt -∗ imp_unblockable κs (SumLty tyl i lt).
  Proof.
    iIntros "#Ub !>" (k r d g tid l G ?) "#Gk G #Dead H".
    destruct k as [m|κ ξi];
      [|iModIntro; iFrame "G"; iExists d, g; by iApply ltype_own_uniq_core].
    rewrite /ltype_own /ltype_own_core /=.
    iDestruct (sum_node_inv with "H") as %(r' & pad & ->).
    rewrite sum_node_sum. iDestruct "H" as "(Tag & C & Pad)".
    iAssert (G &&{↑NllftG}&&> @[ty_lft (lty_fold lt)])%I as "#Gk'".
    { iApply (guards_transitive with "Gk"). iApply lty_lft_sum. }
    iMod ("Ub" $! (Owned m) with "[//] Gk' G Dead C") as "[$ (%d1 & %g1 & C)]".
    iModIntro. iExists d1, g1. rewrite sum_node_sum. by iFrame.
  Qed.

  (** Resolved places are never blocked. *)
  Lemma ofres_imp_unblockable κs {𝔄} (ty: type 𝔄) : ⊢ imp_unblockable κs (OfRes ty).
  Proof.
    iIntros "!>" (k r d g tid l G ?) "_ $ _ H". iModIntro. iExists d, g.
    destruct k as [m|κ ξi]; [done|by iApply ltype_own_uniq_core].
  Qed.

  Lemma res_uniq_imp_unblockable κs {𝔄} (lt: lty 𝔄) κ' :
    ⊢ imp_unblockable κs (ResUniqLty lt κ').
  Proof.
    iIntros "!>" (k r d g tid l G ?) "_ $ _ H". iModIntro. iExists d, g.
    destruct k as [m|κ ξi]; [|by iApply ltype_own_uniq_core].
    rewrite /ltype_own /ltype_own_core /=. iApply (res_node_mono with "H").
    iIntros (r' d' g' tid' l') "H". by iExists _.
  Qed.

  Lemma imp_unblockable_blocked_dead {𝔄} (lt: lty 𝔄) :
    ⊢ imp_unblockable (lty_blocked_lfts lt) lt.
  Proof.
    induction lt as [𝔄 ty|𝔄 ty α|𝔄 lt IH κ|𝔄 n lt IH|𝔄 𝔅 lt1 IH1 lt2 IH2|𝔄 ty α|𝔄l tyl i lt IH|𝔄 lt IH κ|𝔄 ty|𝔄 lt IH κ];
      rewrite /lty_blocked_lfts /=; [| | | | |iApply shr_blocked_imp_unblockable|
        iApply sum_ltype_imp_unblockable; iApply IH|iApply shr_lty_imp_unblockable|
        iApply ofres_imp_unblockable|iApply res_uniq_imp_unblockable].
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
  (** A guard of two lifetimes is a guard of their intersection. *)
  Lemma guards_lft_meet (G: iProp Σ) N κ κ' :
    (G &&{N}&&> @[κ]) -∗ (G &&{N}&&> @[κ']) -∗ (G &&{N}&&> @[κ ⊓ κ']).
  Proof.
    iIntros "A B". iApply (guards_and_point with "A B"); [exact: point_prop_llft_alive|].
    by rewrite llftl_tok_inter_and.
  Qed.

  Lemma unblock_blocked_owned m {𝔄} (ty: type 𝔄) α r d g tid l G :
    Timeless G →
    (G &&{↑NllftG}&&> @[ty_lft ty]) -∗ G -∗
    [†α] -∗ ltype_own (Owned m) (Blocked ty α) r d g tid l ={⊤}=∗
      G ∗ ∃ d' g', ⧖(S d' `max` g') ∗ ltype_own (Owned m) (OfTy ty) r d' g' tid l.
  Proof.
    iIntros (?) "#Gk G Dead H". destruct r as [lr|]; [|done].
    rewrite /ltype_own /= /blocked_owned.
    iMod (fupd_mask_mono with "(H Dead)") as "Upd"; [rewrite /lazyE; set_solver|].
    iMod (guarded_upd_run with "Gk G Upd") as "[$ (%x & %d' & %g' & Rel & #⧖ & In)]";
      [rewrite /lazyE; set_solver|].
    iModIntro. iExists d', g'. iSplit; [iApply (persistent_time_receipt_mono with "⧖"); lia|].
    iExists x. iFrame.
  Qed.

  (** Explicit unblocking of a shared-blocked place in [Owned] mode: the value and the
      depths do not change. *)
  Lemma unblock_shr_blocked_owned m {𝔄} (ty: type 𝔄) α r d g tid l :
    [†α] -∗ ltype_own (Owned m) (ShrBlocked ty α) r d g tid l ={lazyE}=∗
      ltype_own (Owned m) (OfTy ty) r d g tid l.
  Proof.
    iIntros "Dead H". destruct r as [lr|]; [|done].
    rewrite /ltype_own /= /shr_blocked_owned. iDestruct "H" as (x) "(Rel & _ & _ & _ & Inh)".
    iMod ("Inh" with "Dead") as "O". iModIntro. iExists x. iFrame.
  Qed.

  Lemma unblock_blocked_uniq κ ξi {𝔄} (ty: type 𝔄) α r d g tid l G :
    Timeless G →
    (G &&{↑NllftG}&&> @[κ ⊓ ty_lft ty]) -∗ G -∗
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

  (** ** Sums *)

  Lemma xsum_gho_own_pinj {𝔄l} i (tyl: typel 𝔄l) x0 pad d g tid :
    ty_gho_own (Σ! tyl) (pinj i x0, pad) d g tid ⊣⊢ ty_gho_own (tyl +!! i) x0 d g tid.
  Proof. rewrite [ty_gho_own (Σ! tyl)]/ty_gho_own /xsum_ty /=. by rewrite to_xsum_pinj. Qed.

  (** The contents of a sum at variant [i]: the tag, the payload and the padding. *)
  Lemma ofty_owned_xsum m {𝔄l} (tyl: typel 𝔄l) i x pad d g tid l :
    ofty_owned m (xsum_ty tyl) (pinj i x, pad) d g tid l ⊣⊢
      cloc_take l 1 #↦∗ [ #i ] ∗
      ofty_owned m (tyl +!! i) x d g tid (cloc_take (cloc_skip l 1) (ty_size (tyl +!! i))) ∗
      cloc_skip (cloc_skip l 1) (ty_size (tyl +!! i)) #↦!∗ fmap FVal (vec_to_list
        (padding_to_vec (max_hlist_with (λ _, ty_size) tyl - ty_size (tyl +!! i)) pad)).
  Proof.
    rewrite /ofty_owned split_pt_xsum_cells'' xsum_gho_own_pinj.
    iSplit; [iIntros "(($ & $ & $) & $)"|iIntros "($ & ($ & $) & $)"].
  Qed.

  Lemma ofty_owned_xsum_set m {𝔄l} (tyl: typel 𝔄l) i (ty: type (𝔄l !!ₗ i)) x pad d g tid l :
    ofty_owned m (xsum_ty (hlist_set tyl i ty)) (pinj i x, pad) d g tid l ⊣⊢
      cloc_take l 1 #↦∗ [ #i ] ∗
      ofty_owned m ty x d g tid (cloc_take (cloc_skip l 1) (ty_size ty)) ∗
      cloc_skip (cloc_skip l 1) (ty_size ty) #↦!∗ fmap FVal (vec_to_list
        (padding_to_vec (max_hlist_set (λ _, ty_size) tyl i (ty_size ty) - ty_size ty) pad)).
  Proof. by rewrite ofty_owned_xsum hlookup_hlist_set max_hlist_with_hlist_set. Qed.

  (** Unfolding a sum at a known variant [i] into a sum place whose payload is the
      leaf of the variant, and back. *)
  Lemma sum_ofty_unfold_own m {𝔄l} (tyl: typel 𝔄l) i (y: ~~ (𝔄l !!ₗ i)) pad d g tid l :
    ltype_own (Owned m) (OfTy (xsum_ty tyl)) (inl (PlaceIn (𝔄:=Σ! 𝔄l) (pinj i y, pad))) d g tid l ⊣⊢
    ltype_own (Owned m) (SumLty tyl i (OfTy (tyl +!! i))) (prfn_sum i (inl (PlaceIn y)) pad)
      d g tid l.
  Proof.
    rewrite /ltype_own /= psum_proj_pinj /=.
    rewrite -{1}(hlist_set_hlookup tyl i) -(max_hlist_with_hlist_set _ tyl i (tyl +!! i))
      hlist_set_hlookup.
    iSplit.
    - iIntros "(%x & -> & O)". rewrite ofty_owned_xsum.
      iDestruct "O" as "($ & O & $)". iExists y. by iFrame.
    - iIntros "(Tag & (%x & -> & O) & Pad)". iExists _. iSplit; [done|].
      rewrite ofty_owned_xsum. by iFrame.
  Qed.

  (** ** Owned pointers *)

  Lemma ownptr_ofty_fold_own m {𝔄} n (ty: type 𝔄) l' x d g tid l :
    ltype_own (Owned m) (OwnPtrLty n (OfTy ty)) (inr (l', inl (PlaceIn x))) d g tid l ⊢
    ltype_own (Owned m) (OfTy (own_ptr n ty)) (inl (PlaceIn (𝔄:=at_locₛ 𝔄) (l', x))) d g tid l.
  Proof.
    rewrite /ltype_own /= /ofty_owned /=.
    iIntros "(Pt & % & Fr & %y & -> & Pt' & Gho)". iExists (l', x). iSplit; [done|]. iFrame "Pt".
    iNext. destruct d as [|d]; [done|]. simpl.
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

      [UniqLty (OfTy ty) κ] is equivalent to [OfTy (&uniq{κ} ty)] together with [2 + m]
      cumulative time receipts and the time context (held by the node, see
      [ltype_owned_unblock_fold]), up to
      the depths and the borrow index stored in the [&uniq] value (which the place
      refinement does not contain, since they change when the borrow is
      reborrowed). *)

  Lemma uniq_ofty_den {𝔄} (l': cloc) (x: ~~𝔄) ξi d' g' idx :
    prfn_den (inl (PlaceIn (𝔄:=uniq_borₛ 𝔄) (l', x, ξi, d', g', idx)) : prfn (uniq_borₛ 𝔄)) =
    prfn_den (inr (l', inl (PlaceIn x), ξi) : prfn (uniq_borₛ 𝔄)).
  Proof. rewrite /= prfn_den_in prfn_wit_in. done. Qed.

  Lemma uniq_ofty_unfold_own m {𝔄} (ty: type 𝔄) κ l' x ξi d' g' idx d g tid l :
    time_ctx -∗ ⧗(2 + m) -∗
    ltype_own (Owned m) (OfTy (&uniq{κ} ty)) (inl (PlaceIn (𝔄:=uniq_borₛ 𝔄) (l', x, ξi, d', g', idx))) d g tid l -∗
    ltype_own (Owned m) (UniqLty (OfTy ty) κ) (inr (l', inl (PlaceIn x), ξi)) d g tid l.
  Proof.
    rewrite /ltype_own /= /ofty_owned /=.
    iIntros "#TIME ⧗ (%v & -> & Pt & Gho)". iFrame "Pt ⧗ TIME". iNext.
    iDestruct "Gho" as "(#Incl & %Hle & Body & #G)".
    iSplitR; [done|]. iSplitR; [done|].
    iExists d', g'. iSplit; [done|]. iExists x, idx. iSplit; [done|]. done.
  Qed.

  Lemma uniq_ofty_fold_own m {𝔄} (ty: type 𝔄) κ l' x ξi d g tid l :
    ltype_own (Owned m) (UniqLty (OfTy ty) κ) (inr (l', inl (PlaceIn x), ξi)) d g tid l ⊢
    ⧗(2 + m) ∗ ∃ d' g' idx,
      ltype_own (Owned m) (OfTy (&uniq{κ} ty)) (inl (PlaceIn (𝔄:=uniq_borₛ 𝔄) (l', x, ξi, d', g', idx))) d g tid l.
  Proof.
    rewrite /ltype_own /= /ofty_owned /=.
    have ?: Inhabited (~~𝔄) := populate x. have ?: Inhabited Idx := populate idx_dummy.
    iIntros "(Pt & $ & _ & H)".
    iDestruct "H" as "(Incl & G & %d' & %g' & Hle & %y & %idx & Hy & Body)".
    iExists d', g', idx, _. iSplit; [done|]. iFrame "Pt". iNext.
    iDestruct "Hy" as %->. iFrame.
  Qed.

  Lemma uniq_ofty_unfold_core m {𝔄} (ty: type 𝔄) κ l' x ξi d' g' idx d g tid l :
    time_ctx -∗ ⧗(2 + m) -∗
    ltype_own_core (Owned m) (OfTy (&uniq{κ} ty)) (inl (PlaceIn (𝔄:=uniq_borₛ 𝔄) (l', x, ξi, d', g', idx))) d g tid l -∗
    ltype_own_core (Owned m) (UniqLty (OfTy ty) κ) (inr (l', inl (PlaceIn x), ξi)) d g tid l.
  Proof.
    iIntros "#TIME ⧗ H". iDestruct (uniq_ofty_unfold_own with "TIME ⧗ H") as "H".
    iApply (uniq_node_mono with "H"). iIntros (????? l'') "H". by iExists _.
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

  (** Unblocking a leaf in [Owned] mode inside a lazy update, as [leaf_owned_unblock]; a
      shared-blocked leaf is unblocked by its inheritance (its value and depths do not
      change). *)
  Lemma leaf_owned_s_unblock {𝔄} κ m (ty: type 𝔄) p lr d g tid l G :
    Timeless G →
    llft_ctx -∗ (G &&{↑NllftG}&&> @[ty_lft ty]) -∗ pat_ok κ p -∗ [†κ] -∗ G -∗
    ⧖((m + S d) `max` g) -∗ leaf_owned_s false m ty p (inl lr) d g tid l ={lazyE}=∗
      G ∗ ∃ x d' g', place_rfn_rel lr x ∗ ⧖((m + S d') `max` g') ∗
        ofty_owned m ty x d' g' tid l.
  Proof.
    iIntros (?) "#LFT #Gty #Ok #†κ G #⧖ L".
    destruct p as [| | | | |α|]; try by iApply (leaf_owned_unblock with "LFT Gty Ok †κ G ⧖ L").
    iMod (pat_ok_dead with "LFT Ok †κ") as "[†α _]"; [apply lazyE_NllftG|].
    iDestruct "L" as (x) "(Rel & _ & _ & _ & Inh)". iMod ("Inh" with "†α") as "O".
    iModIntro. iFrame "G". iExists x, d, g. iFrame "∗#".
  Qed.

  (** The node of [ProdLty (OfTy ty1) (OfTy ty2)] is seen as the leaf
      [prod_ty ty1 ty2] (by the closing view shift of [prod_ofty_unfold_uniq]): at
      a structured refinement, it is blocked at [κp]; once [κp] is dead, the
      components are unblocked. *)
  Lemma prod_node_leaf {𝔄 𝔅} κp (ty1: type 𝔄) (ty2: type 𝔅) p r d g tid l :
    llft_ctx -∗ pat_ok κp p -∗ ⧖(S d `max` g) -∗
    prod_node (ty_size ty1) (leaf_owned_s false 0 ty1 (pat_l p))
      (leaf_owned_s false 0 ty2 (pat_r p)) r d g tid l -∗
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
    iMod (leaf_owned_s_unblock _ 0 with "LFT Gty1 Ok1 †κ G ⧖ N1")
      as "[G (%x1 & %d1 & %g1 & Rel1 & #⧖1 & Pt1 & Gho1)]".
    iMod (leaf_owned_s_unblock _ 0 with "LFT Gty2 Ok2 †κ G ⧖ N2")
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
      (leaf_owned_s false 0 ty1 (pat_l p')) (leaf_owned_s false 0 ty2 (pat_r p'))).
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

  (** As [cpd_rebody], extending the reservation by [ζl'] (as [cpd_acc]): the tokens for
      [ζl'] are handed to a view shift that produces the new contents. *)
  Lemma cpd_rebody_ext {𝔄} κ ξi (ty: type 𝔄) p
      (node node': lpat → prfn 𝔄 → nat → nat → thread_id → cloc → iProp Σ)
      (r: prfn 𝔄) d g tid l E G :
    Timeless G → ↑Nllft ∪ ↑prophN ⊆ E →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗ G -∗
    cpd_own κ ξi ty p node r d g tid l ={E}=∗ ∃ κp,
      uniq_pat_lft κ κp ∗ ▷ pat_ok κp p ∗
      ▷ guarded_upd lazyE @[ty_lft ty] (⧖(S d `max` g) ∗ node p r d g tid l) ∗
      (∀ p' (r': prfn 𝔄) d' g' ζl' q (R: iProp Σ),
         ⌜∀ ζl, prfn_rsv r ζl → prfn_rsv r' (ζl ++ ζl')⌝ -∗
         □ (∀ p2 r2 d2 g2, pat_ok κp p2 -∗ ⧖(S d2 `max` g2) -∗ node' p2 r2 d2 g2 tid l -∗
              leaf_node κp ty p2 r2 d2 g2 tid l) -∗
         q:+[ζl'] -∗
         (q:+[ζl'] ={E}=∗ ▷ pat_ok κp p' ∗
           ▷ guarded_upd lazyE @[ty_lft ty] (⧖(S d' `max` g') ∗ node' p' r' d' g' tid l) ∗ R)
         ={E}=∗ cpd_own κ ξi ty p' node' r' d' g' tid l ∗ G ∗ R).
  Proof.
    iIntros (??) "#LFT #PROPH #UNIQ #Gk G".
    iIntros "(%x₀ & %κp & %γ & %γf & %idx & %ζl & #Incl & %Hr & Tok & Gh & Tf & ⧗ & #Bor)".
    iMod (proph_idx_bor_gen_rsv_acc_rebody_ext with "LFT PROPH UNIQ Gk Tok Bor G")
      as (wπ) "[Body Close]"; [done..|].
    iDestruct (bi.later_or with "Body") as "[Body|[>Tf' _]]"; last first.
    { iDestruct (cpd_tok_excl with "Tf Tf'") as "[]". }
    rewrite cpd_body_cell.
    iMod (bi.later_exist_except_0 with "Body") as (p1) "Body".
    iMod (bi.later_exist_except_0 with "Body") as (r1) "(#Ok & _ & >Gh' & Upd)".
    iDestruct (ghost_var_agree with "Gh Gh'") as %[<- <-]%lstate_inj.
    iModIntro. iExists κp. iFrame "Incl Ok Upd".
    iIntros (p' r' d' g' ζl' q R Hr') "#Conv ζl' VS".
    iMod (ghost_var_update_halves (lstate p' r') with "Gh Gh'") as "[Gh Gh']".
    iMod (ghost_var_alloc (lstate_triv (𝔄:=unitₛ) ())) as (γf') "Tf'".
    iMod ("Close" $! (uniq_cell x₀ d' g' γ) (λ π, (prfn_den r' π, (uniq_cell x₀ d' g' γ).2))
      ζl' q (cpd_gbody κp γf' ty node' tid l) R with "[Tf] ζl' [Gh' VS]")
      as (idx') "(Tok & #Bor' & $ & $)".
    { (* Back to the body of [&uniq] at the same state, giving up the old token. *)
      iIntros "!>" (c2 w2) "Q". iModIntro. iNext. iRight. iFrame "Tf".
      iDestruct "Q" as "[Q|[_ $]]". rewrite /uniq_gbody /cpd_body.
      iDestruct "Q" as (p2 r2) "(#Ok2 & % & Gh2 & Upd2)". iExists p2, r2. iFrame "Ok2 Gh2".
      iSplit; [done|]. iApply (guarded_upd_mono with "[] Upd2").
      iIntros "[#⧖ N] !>". iFrame "⧖". iApply ("Conv" with "Ok2 ⧖ N"). }
    { iIntros "ζl'". iMod ("VS" with "ζl'") as "(Ok' & Upd' & $)". iModIntro.
      iNext. iLeft. rewrite cpd_body_cell. iExists p', r'. by iFrame. }
    iModIntro. iExists x₀, κp, γ, γf', idx', (ζl ++ ζl'). iFrame "∗#". iPureIntro. by apply Hr'.
  Qed.

  (** ** Simple place types

      Place types built from leaves, products, owned pointers, sums and unique borrows
      (at any depth). In [Owned] mode, such a place can be unblocked and folded inside a
      lazy update, once all its blocked lifetimes are dead (via the membership
      condition). Under [m] owned pointers, the time receipts are shifted by [m] (see
      [blocked_owned]): the owned pointers above a leaf are folded back at depths
      increased by one per pointer, which needs one more receipt per pointer. A unique
      borrow ([UniqLty]) is folded back by folding back the nested place in its own
      borrow ([ltype_uniq_unblock_fold]). *)
  Fixpoint lty_simple {𝔄} (lt: lty 𝔄) : Prop :=
    match lt with
    | OfTy _ | Blocked _ _ | ShrBlocked _ _ | ShrLty _ _ => True
    | OwnPtrLty _ lt => lty_simple lt
    | ProdLty lt1 lt2 => lty_simple lt1 ∧ lty_simple lt2
    | SumLty _ _ lt => lty_simple lt
    | UniqLty lt _ => lty_simple lt
    (* Resolved places are not folded back (they are only in the owned part of a place). *)
    | OfRes _ | ResUniqLty _ _ => False
    end.

  Lemma pat_ok_own κ p : pat_ok κ p -∗ pat_ok κ (pat_own p).
  Proof. iIntros "Ok". destruct p; simpl; try iApply pat_ok_leaf. done. Qed.

  Lemma pat_ok_sum κ p : pat_ok κ p -∗ pat_ok κ (pat_sum p).
  Proof. iIntros "Ok". destruct p; simpl; try iApply pat_ok_leaf. done. Qed.

  Lemma pat_ok_uniq κ p : pat_ok κ p -∗ pat_ok κ (pat_uniq p).
  Proof. iIntros "Ok". destruct p; simpl; try iApply pat_ok_leaf. done. Qed.

  (** The equalizer of a sum value, from the equalizer of its payload. *)
  Lemma proph_eqz_sum {𝔄l} i (r: prfn (𝔄l !!ₗ i)) pad (x: ~~ (𝔄l !!ₗ i)) :
    (prfn_den r :== vπ x) -∗ (prfn_den (prfn_sum i r pad) :== vπ (𝔄:=Σ! 𝔄l) (pinj i x, pad)).
  Proof.
    iIntros "Eqz".
    have ?: Inj (=) (=) (λ a: (𝔄l !!ₗ i), ((pinj i a, pad) : (Σ! 𝔄l)%ST)).
    { intros ?? [=Heq]. by apply pinj_Inj in Heq. }
    iDestruct (proph_eqz_constr (λ a: (𝔄l !!ₗ i), ((pinj i a, pad) : (Σ! 𝔄l)%ST)) with "Eqz")
      as "Eqz".
    iApply (proph_eqz_eq with "Eqz").
    - by rewrite prfn_den_sum.
    - fun_ext=> π /=. by rewrite psum_map1_pinj.
  Qed.

  Definition lty_is_cpd {𝔄} (lt: lty 𝔄) : Prop :=
    match lt with ProdLty _ _ | OwnPtrLty _ _ | UniqLty _ _ | SumLty _ _ _ => True | _ => False end.

  (** In [Uniq] mode, a compound place is a compound place whose node is the
      [Owned 0] interpretation. *)
  Lemma ltype_own_cp_uniq_cpd {𝔄} (lt: lty 𝔄) κ ξi p :
    lty_is_cpd lt →
    ltype_own_cp false lt (Uniq κ ξi) p =
      cpd_own κ ξi (lty_fold lt) p (ltype_own_cp false lt (Owned 0)).
  Proof. by destruct lt. Qed.

  (** The statement of [ltype_owned_unblock_fold] (in [Owned 0] mode), as a hypothesis of
      the fold of nested places. *)
  Definition owned0_unblock_fold {𝔄} (lt: lty 𝔄) (κ: lft) (tid: thread_id) : Prop :=
    ∀ p r d g l G, Timeless G →
    ⊢ llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗
      (G &&{↑NllftG}&&> @[ty_lft (lty_fold lt)]) -∗ pat_ok κ p -∗ [†κ] -∗ G -∗
      ⧖(S d `max` g) -∗ ltype_own_cp false lt (Owned 0) p r d g tid l ={lazyE}=∗
        G ∗ ∃ x d' g', ▷ (prfn_den r :== vπ x) ∗ ⧖(S d' `max` g') ∗
          ofty_owned 0 (lty_fold lt) x d' g' tid l.

  (** ** Unique borrows below a unique borrow

      The node of [UniqLty lt κ'] (with a simple [lt]) is folded back into the leaf
      [&uniq{κ'} (lty_fold lt)] inside a lazy update (with a guard for the lifetime
      of [&uniq{κ'} …], which includes [κ']), once the pattern lifetime [κ] of the
      outer borrow has ended: by the nested membership condition ([pat_ok κ p], see
      [pat_blk_lfts]), the blocked lifetimes of the nested place have ended too. The
      nested compound place is unreserved, its borrow is opened (and switched back to
      the body of [&uniq]), its contents are unblocked and folded
      ([ltype_owned_unblock_fold], recursively), and the borrow is closed at the trivial
      state. The cumulative time receipts of the node ([2 + m] below [m] owned pointers)
      pay for the later credits needed to open the nested borrow (and to strip the [m]
      laters in front of it), and for the receipt of the outer leaf, [m + 1] more than
      the depth of the (unblocked) nested contents. *)

  Lemma leaf_uniq_unblock {𝔄} κ κ' ξi (ty: type 𝔄) p lr d g tid l G :
    Timeless G →
    llft_ctx -∗ (G &&{↑NllftG}&&> @[κ']) -∗ (G &&{↑NllftG}&&> @[ty_lft ty]) -∗
    pat_ok κ p -∗ [†κ] -∗ G -∗
    ⧖(S d `max` g) -∗ leaf_uniq false κ' ξi ty p (inl lr) d g tid l ={lazyE}=∗
      G ∗ ∃ d' g', ⧖(S d' `max` g') ∗ ofty_uniq κ' ξi ty lr d' g' tid l.
  Proof.
    iIntros (?) "#LFT #Gκ' #Gty' #Ok #†κ G #⧖ L".
    iDestruct (guards_lft_meet with "Gκ' Gty'") as "#Gty".
    destruct p; rewrite /leaf_uniq /=;
      try (iModIntro; iFrame "G"; iExists d, g; by iFrame "⧖ L").
    rewrite /blocked_uniq.
    iMod (pat_ok_dead with "LFT Ok †κ") as "[Dead _]"; [apply lazyE_NllftG|].
    iMod ("L" with "Dead") as "Upd".
    by iApply (guarded_upd_run with "Gty G Upd").
  Qed.

  Lemma cpd_own_unblock_fold {𝔄} (lt: lty 𝔄) κ κ' ξi p r d g tid l G :
    owned0_unblock_fold lt κ tid → Timeless G →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗
    (G &&{↑NllftG}&&> @[κ']) -∗ (G &&{↑NllftG}&&> @[ty_lft (lty_fold lt)]) -∗
    pat_ok κ p -∗ [†κ] -∗ G -∗ £1 -∗
    cpd_own κ' ξi (lty_fold lt) p (ltype_own_cp false lt (Owned 0)) r d g tid l ={lazyE}=∗
      G ∗ ∃ x d' g' idx, ▷ (prfn_den r :== vπ x) ∗ ⧖(S d' `max` g') ∗
        uniq_body (lty_fold lt) x ξi d' g' idx κ' tid l.
  Proof.
    iIntros (Hfold ?) "#LFT #PROPH #UNIQ #Gκ' #Gty #Ok #†κ G £ Own".
    iDestruct "Own" as (x₀ κp γ γf idx ζl) "(#Incl & _ & Tok & Gh & Tf & ⧗ & #Bor)".
    iMod (proph_idx_bor_gen_unreserve with "LFT PROPH UNIQ Gκ' G Tok Bor") as "[Tok G]";
      [rewrite /lazyE; solve_ndisj|].
    iMod (fractional.frac_split_guard_in_half NllftG G G with "G []")
      as (γh) "[H1 [H2 [#Ghh #Back]]]";
      [rewrite /lazyE; solve_ndisj|iApply guards_refl|].
    iDestruct (guards_transitive with "Ghh Gκ'") as "#Hκ'".
    iDestruct (guards_transitive with "Ghh Gty") as "#Hty".
    set ty := lty_fold lt.
    have ?: Inhabited (~~𝔄) := populate x₀.
    iMod (proph_idx_bor_gen_acc_rebody_guarded lazyE κ' (uniq_prvar x₀ ξi) (uniq_cell x₀ d g γ)
      idx _ (uniq_gbody κp ty tid l) with "LFT UNIQ Hκ' Tok Bor H1") as (wπ) "[Body Close]";
      [rewrite /lazyE; solve_ndisj|].
    iDestruct (bi.later_or with "Body") as "[Body|[>Tf' _]]"; last first.
    { iDestruct (cpd_tok_excl with "Tf Tf'") as "[]". }
    rewrite cpd_body_cell.
    iMod (lc_fupd_elim_later with "£ Body") as (p1 r1) "(_ & _ & Gh' & Upd)".
    iDestruct (ghost_var_agree with "Gh Gh'") as %[<- <-]%lstate_inj.
    iMod (guarded_upd_run with "Hty H2 Upd") as "(H2 & #⧖1 & N)"; [done|].
    iMod (Hfold with "LFT PROPH UNIQ Hty Ok †κ H2 ⧖1 N")
      as "[H2 (%x & %d2 & %g2 & Eqz & #⧖2 & Pt & Gho)]".
    iMod (ghost_var_update_halves (lstate_triv x) with "Gh Gh'") as "[Gh Gh']".
    iSpecialize ("Close" $! (uniq_cell x d2 g2 γ) (vπ (uniq_cell x d2 g2 γ))).
    iMod (fupd_mask_mono with "(Close [Gh' Pt Gho] [Tf])") as (idx') "(Tok & #Bor' & H1)";
      [rewrite /lazyE; solve_ndisj| | |].
    { iApply (uniq_gbody_triv_close with "Gh'"); [done|]. iNext.
      iApply (uniq_payload_intro with "[] Gho Pt").
      iApply (persistent_time_receipt_mono with "⧖2"). lia. }
    { iIntros "!>" (c2 w2) "P". iModIntro. iNext. iRight. iFrame. }
    iMod (fupd_mask_mono with "(Back H1 H2)") as "$"; [rewrite /lazyE; solve_ndisj|].
    iModIntro. iExists x, d2, g2, idx'. iFrame "Eqz".
    iSplit; [iApply (persistent_time_receipt_mono with "⧖2"); lia|].
    iApply (uniq_body_from_parts with "Incl [Gh Tok] ⧗ [Bor']").
    - rewrite /uniq_tokγ (uniq_bor_tok_retarget _ x₀). iFrame.
    - by rewrite /uniq_persγ (uniq_idx_bor_gen_retarget _ _ x₀).
  Qed.

  (** Folding back a place in [Uniq κ' ξi] mode (the referent of a nested unique
      borrow) into the body of [&uniq{κ'}], given the fold of its node. *)
  Lemma ltype_uniq_unblock_fold {𝔄} (lt: lty 𝔄) κ κ' ξi p r d g tid l G :
    (lty_is_cpd lt → owned0_unblock_fold lt κ tid) → Timeless G →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗
    (G &&{↑NllftG}&&> @[κ']) -∗ (G &&{↑NllftG}&&> @[ty_lft (lty_fold lt)]) -∗
    pat_ok κ p -∗ [†κ] -∗ G -∗ £1 -∗ ⧖(S d `max` g) -∗
    ltype_own_cp false lt (Uniq κ' ξi) p r d g tid l ={lazyE}=∗
      G ∗ ∃ x d' g' idx, ▷ (prfn_den r :== vπ x) ∗ ⧖(S d' `max` g') ∗
        uniq_body (lty_fold lt) x ξi d' g' idx κ' tid l.
  Proof.
    iIntros (Hfold ?) "#LFT #PROPH #UNIQ #Gκ' #Gty #Ok #†κ G £ #⧖ C".
    destruct lt as [𝔅 ty|𝔅 ty α|𝔅 lt κ''|𝔅 n lt|𝔅 ℭ lt1 lt2|𝔅 ty α|𝔅l tyl i lt|𝔅 lt κ''|𝔅 ty|𝔅 lt κ''];
      [..|iDestruct "C" as "[C _]"|by iDestruct "C" as "[]"|by iDestruct "C" as "[]"];
      try (destruct r as [lr|]; [|done];
        iMod (leaf_uniq_unblock with "LFT Gκ' Gty Ok †κ G ⧖ C")
          as "[$ (%d2 & %g2 & #⧖2 & %x & %idx & Rel & Body)]";
        iModIntro; iExists x, d2, g2, idx; iFrame "⧖2 Body"; rewrite prfn_den_inl;
        by iApply place_rfn_rel_eqz);
      iApply (cpd_own_unblock_fold _ _ _ _ _ _ _ _ _ _ _ (Hfold I) with
        "LFT PROPH UNIQ Gκ' Gty Ok †κ G £ C").
  Qed.

  Lemma ltype_owned_unblock_fold {𝔄} (lt: lty 𝔄) κ m p r d g tid l G :
    lty_simple lt → Timeless G →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗
    (G &&{↑NllftG}&&> @[ty_lft (lty_fold lt)]) -∗ pat_ok κ p -∗ [†κ] -∗ G -∗
    ⧖((m + S d) `max` g) -∗ ltype_own_cp false lt (Owned m) p r d g tid l ={lazyE}=∗
      G ∗ ∃ x d' g', ▷ (prfn_den r :== vπ x) ∗ ⧖((m + S d') `max` g') ∗
        ofty_owned m (lty_fold lt) x d' g' tid l.
  Proof.
    induction lt as [𝔄 ty|𝔄 ty α|𝔄 lt IH κ'|𝔄 n lt IH|𝔄 𝔅 lt1 IH1 lt2 IH2|𝔄 ty α|𝔄l tyl i lt IH|𝔄 lt IH κ'|𝔄 ty|𝔄 lt IH κ']
      in m, p, r, d, g, l, G |- *; intros Hs ?; try done; try (exfalso; exact Hs).
    8: { iIntros "#LFT #PROPH #UNIQ #Gty #Ok #†κ G #⧖ [L _]"; destruct r as [lr|]; [|done];
      iMod (leaf_owned_s_unblock with "LFT Gty Ok †κ G ⧖ L")
        as "[$ (%x & %d' & %g' & Rel & ⧖' & O)]";
      iModIntro; iExists x, d', g'; iFrame; rewrite prfn_den_inl;
      by iApply place_rfn_rel_eqz. }
    7: { iIntros "#LFT #PROPH #UNIQ #Gty #Ok #†κ G #⧖ N".
      rewrite ltype_own_cp_sum_owned.
      iDestruct (sum_node_inv with "N") as %(r' & pad & ->).
      rewrite sum_node_sum. iDestruct "N" as "(Tag & N & Pad)".
      iDestruct (pat_ok_sum with "Ok") as "Ok'".
      iAssert (G &&{↑NllftG}&&> @[ty_lft (lty_fold lt)])%I as "#Gty'".
      { iApply (guards_transitive with "Gty"). iApply lty_lft_sum. }
      iMod (IH with "LFT PROPH UNIQ Gty' Ok' †κ G ⧖ N")
        as "[$ (%x & %d' & %g' & Eqz & #⧖1 & O)]"; [done|].
      iModIntro. iExists (pinj i x, pad), d', g'. iFrame "⧖1".
      iSplitL "Eqz"; [iNext; by iApply proph_eqz_sum|].
      rewrite /= ofty_owned_xsum_set -lty_size_fold. iFrame. }
    1,2,6: iIntros "#LFT #PROPH #UNIQ #Gty #Ok #†κ G #⧖ L"; destruct r as [lr|]; [|done];
      iMod (leaf_owned_s_unblock with "LFT Gty Ok †κ G ⧖ L")
        as "[$ (%x & %d' & %g' & Rel & ⧖' & O)]";
      iModIntro; iExists x, d', g'; iFrame; rewrite prfn_den_inl;
      by iApply place_rfn_rel_eqz.
    - (* A nested unique borrow. *)
      iIntros "#LFT #PROPH #UNIQ #Gty #Ok #†κ G #⧖ N".
      destruct r as [?|[[l' r'] ξi]]; [done|].
      iDestruct "N" as "(Pt & ⧗ & #TIME & N)".
      iDestruct (cumulative_time_receipt_sep 1 (S m) with "⧗") as "[⧗a ⧗b]".
      iMod (cumulative_persistent_time_receipt_get_credits with "TIME ⧗a ⧖") as "[_ £]";
        [rewrite /lazyE; solve_ndisj|].
      iDestruct (lc_weaken (m + 1) with "£") as "[£m £]"; [rewrite /advance_credits; nia|].
      iMod (lc_fupd_elim_laterN with "£m N") as "(#Incl' & #Gpt & %d1 & %g1 & %Hle & C)".
      iDestruct (pat_ok_uniq with "Ok") as "#Ok'".
      iAssert (G &&{↑NllftG}&&> @[κ'])%I as "#Gκ'".
      { iApply (guards_transitive with "Gty"). iApply llftl_intersect_incl_l. }
      iAssert (G &&{↑NllftG}&&> @[ty_lft (lty_fold lt)])%I as "#Gty'".
      { iApply (guards_transitive with "Gty"). iApply llftl_intersect_incl_r. }
      iMod (ltype_uniq_unblock_fold lt with "LFT PROPH UNIQ Gκ' Gty' Ok' †κ G £ [] C")
        as "[G (%x & %d1' & %g1' & %idx & Eqz & #⧖1 & Body)]".
      { intros _ p0 r0 d0 g0 l0 G0 ?. by iApply (IH 0 p0 r0 d0 g0 l0 G0). }
      { iApply (persistent_time_receipt_mono with "⧖"). lia. }
      iMod (cumulative_persistent_time_receipt with "TIME ⧗b ⧖1") as "#⧖1'";
        [rewrite /lazyE; solve_ndisj|].
      iModIntro. iFrame "G".
      iExists (l', x, ξi, d1', g1', idx), (S d1' `max` d), (g1' `max` g).
      iSplitL "Eqz".
      { iNext. iApply (proph_eqz_prod with "[Eqz] []").
        - iApply (proph_eqz_eq with "Eqz"); done.
        - iApply (proph_eqz_eq with "[]"); [done| |iApply proph_eqz_refl].
          fun_ext=> π /=. apply (uniq_prvar_app_irrel (prfn_wit r') x ξi π). }
      iSplit. { iCombine "⧖ ⧖1'" as "⧖'". iApply (persistent_time_receipt_mono with "⧖'"). lia. }
      rewrite /ofty_owned /=. iFrame "Pt". iApply bi.laterN_intro.
      iFrame "Incl' Body". iSplit; [iPureIntro; lia|].
      iApply (lguards_weaken_later with "Gpt"). lia.
    - iIntros "#LFT #PROPH #UNIQ #Gty #Ok #†κ G #⧖ N".
      destruct r as [lr|[l' r']]; [done|]. iDestruct "N" as "(Pt & %Hd & Fr & N)".
      iDestruct (pat_ok_own with "Ok") as "Ok'".
      iAssert (⧖((m + 1 + S (pred d)) `max` g))%I as "#⧖'".
      { iApply (persistent_time_receipt_mono with "⧖"). lia. }
      iMod (IH with "LFT PROPH UNIQ Gty Ok' †κ G ⧖' N")
        as "[$ (%x & %d' & %g' & Eqz & #⧖1 & Pt' & Gho)]"; [done|].
      iModIntro. iExists (l', x), (S d'), g'.
      iSplitL "Eqz". { iNext. iApply (proph_eqz_prod with "[] [Eqz]").
        - iApply proph_eqz_refl.
        - iApply (proph_eqz_eq with "Eqz"); [|done]. by fun_ext=> π /=. }
      iSplit. { iApply (persistent_time_receipt_mono with "⧖1"). lia. }
      rewrite /ofty_owned /=. iFrame "Pt".
      rewrite (heap_cloc_mapsto_fancy_empty l' (ty_phys (lty_fold lt) x tid)) ty_size_eq
        -lty_size_fold.
      iNext. iFrame "Pt' Fr". by rewrite (Nat.add_1_r m).
    - destruct Hs as [Hs1 Hs2]. iIntros "#LFT #PROPH #UNIQ #Gty #Ok #†κ G #⧖ N".
      destruct r as [lr|[r1 r2]]; [done|]. iDestruct "N" as "[N1 N2]".
      iDestruct (pat_ok_prod with "Ok") as "[Ok1 Ok2]".
      iAssert (G &&{↑NllftG}&&> @[ty_lft (lty_fold lt1)])%I as "#Gty1".
      { iApply (guards_transitive with "Gty"). simpl. rewrite lft_intersect_list_app.
        iApply llftl_intersect_incl_l. }
      iAssert (G &&{↑NllftG}&&> @[ty_lft (lty_fold lt2)])%I as "#Gty2".
      { iApply (guards_transitive with "Gty"). simpl. rewrite lft_intersect_list_app.
        iApply llftl_intersect_incl_r. }
      iMod (IH1 with "LFT PROPH UNIQ Gty1 Ok1 †κ G ⧖ N1")
        as "[G (%x1 & %d1 & %g1 & Eqz1 & #⧖1 & Pt1 & Gho1)]"; [done|].
      iMod (IH2 with "LFT PROPH UNIQ Gty2 Ok2 †κ G ⧖ N2")
        as "[$ (%x2 & %d2 & %g2 & Eqz2 & #⧖2 & Pt2 & Gho2)]"; [done|].
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

  (** The node of a simple compound place is seen as the leaf of its folded type, as in
      [prod_node_leaf]: at a structured refinement, it is blocked at [κp]. *)
  Lemma ltype_owned_leaf_node {𝔄} (lt: lty 𝔄) κp p r d g tid l :
    lty_is_cpd lt → lty_simple lt →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ pat_ok κp p -∗ ⧖(S d `max` g) -∗
    ltype_own_cp false lt (Owned 0) p r d g tid l -∗ leaf_node κp (lty_fold lt) p r d g tid l.
  Proof.
    iIntros (Hc Hs) "#LFT #PROPH #UNIQ #Ok #⧖ N".
    destruct r as [lr|rs].
    { by destruct lt as [𝔄 ty|𝔄 ty α|𝔄 lt κ'|𝔄 n lt|𝔄 𝔅 lt1 lt2|𝔄 ty α|𝔄l tyl i lt|𝔄 lt κ'|𝔄 ty|𝔄 lt κ']. }
    iEval (rewrite /leaf_node /= /blocked_owned). iIntros "#†κ !>" (G ?) "#Gty G".
    iMod (ltype_owned_unblock_fold lt _ 0 with "LFT PROPH UNIQ Gty Ok †κ G ⧖ N")
      as "[$ (%x & %d' & %g' & Eqz & ⧖' & O)]"; [done|].
    iModIntro. iExists x, d', g'. iFrame.
  Qed.

  (** ** Unfolding and folding the root, generically *)

  (** Unfolding a unique borrow of [lty_fold lt] into the compound place [lt] (with
      no blocked leaves), given a conversion of the payload into the node of [lt]; as
      [prod_ofty_unfold_uniq]. *)
  Lemma cpd_unfold_uniq {𝔄} (lt: lty 𝔄) κ ξi x (r: prfn 𝔄) d g tid l E G :
    lty_is_cpd lt → lty_simple lt → pat_blk_lfts (lty_pat lt) = [] →
    prfn_rsv r [] → (∀ π, prfn_den r π = vπ x π) →
    (∀ d g, ty_gho_own (lty_fold lt) x d g tid ∗ l #↦!∗ ty_phys (lty_fold lt) x tid ⊢
       |={lazyE}=> ltype_own_cp false lt (Owned 0) (lty_pat lt) r d g tid l) →
    Timeless G → ↑Nllft ∪ ↑prophN ⊆ E →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗ G -∗
    ltype_own (Uniq κ ξi) (OfTy (lty_fold lt)) (inl (PlaceIn x)) d g tid l ={E}=∗
    ltype_own (Uniq κ ξi) lt r d g tid l ∗ G.
  Proof.
    iIntros (Hc Hs Hp Hr Hden Hconv ??) "#LFT #PROPH #UNIQ #Gk G H".
    rewrite /ltype_own (ltype_own_cp_uniq_cpd lt) //=.
    iDestruct "H" as (x' idx ->) "(%κp & %γ & #Incl & (Gh & Tok) & ⧗ & #Bor)".
    iMod (ghost_var_alloc (lstate_triv (𝔄:=unitₛ) ())) as (γf) "Tf".
    set node := ltype_own_cp false lt (Owned 0).
    set ty := lty_fold lt.
    iMod (proph_idx_bor_gen_acc_rebody_guarded E κ (uniq_prvar x ξi) (uniq_cell x d g γ) idx
      (uniq_gbody κp ty tid l) (cpd_gbody κp γf ty node tid l) with "LFT UNIQ Gk Tok Bor G")
      as (wπ) "[Body Close]"; [solve_ndisj|].
    iMod (uniq_gbody_triv_open with "Gh Body") as "(%Hw & Gh & Gh' & Pl)".
    iMod (ghost_var_update_halves (lstate (lty_pat lt) r) with "Gh Gh'") as "[Gh Gh']".
    iSpecialize ("Close" $! (uniq_cell x d g γ) wπ).
    iMod (fupd_mask_mono with "(Close [Gh' Pl] [])") as (idx') "(Tok & #Bor' & G)";
      [solve_ndisj| | |].
    { iNext. iLeft. rewrite cpd_body_cell. iExists (lty_pat lt), r.
      iFrame "Gh'". iSplit; [by rewrite /pat_ok Hp|]. iSplit.
      { iPureIntro. intros π. by rewrite Hw Hden. }
      rewrite uniq_payload_cell. iApply (guarded_upd_mono with "[] Pl").
      iIntros "($ & Gho & Pt)". iApply Hconv. iFrame. }
    { iIntros "!>" (c2 w2) "Q". iModIntro. iNext.
      iDestruct "Q" as "[Q|[_ $]]". rewrite /cpd_body /uniq_gbody /cpd_body.
      iDestruct "Q" as (p2 r2) "(#Ok & % & Gh & Upd)". iExists p2, r2. iFrame "Ok Gh".
      iSplit; [done|]. iApply (guarded_upd_mono with "[] Upd").
      iIntros "[#⧖ N] !>". iFrame "⧖".
      by iApply (ltype_owned_leaf_node with "LFT PROPH UNIQ Ok ⧖ N"). }
    iMod (proph_idx_bor_gen_reserve E κ _ _ idx' [] 1%Qp with "LFT PROPH UNIQ Gk G [] Tok Bor'")
      as "(Tok & _ & $)"; [solve_ndisj|done|].
    iModIntro. iExists x, κp, γ, γf, idx', []. by iFrame "∗#".
  Qed.

  (** Folding back, given a conversion of the node into the payload; as
      [prod_ofty_fold_uniq]. *)
  Lemma cpd_fold_uniq {𝔄} (lt: lty 𝔄) κ ξi x (r: prfn 𝔄) d g tid l E G :
    lty_is_cpd lt →
    (∀ d g, ltype_own_cp false lt (Owned 0) (lty_pat lt) r d g tid l ⊢ |={lazyE}=>
       ty_gho_own (lty_fold lt) x d g tid ∗ l #↦!∗ ty_phys (lty_fold lt) x tid) →
    Timeless G → ↑Nllft ∪ ↑prophN ⊆ E →
    llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗ G -∗
    ltype_own (Uniq κ ξi) lt r d g tid l ={E}=∗
    ltype_own (Uniq κ ξi) (OfTy (lty_fold lt)) (inl (PlaceIn x)) d g tid l ∗ G.
  Proof.
    iIntros (Hc Hconv ??) "#LFT #PROPH #UNIQ #Gk G H".
    rewrite /ltype_own (ltype_own_cp_uniq_cpd lt) //=.
    iDestruct "H" as (x₀ κp γ γf idx ζl) "(#Incl & _ & Tok & Gh & Tf & ⧗ & #Bor)".
    iMod (proph_idx_bor_gen_unreserve with "LFT PROPH UNIQ Gk G Tok Bor") as "[Tok G]";
      [solve_ndisj|].
    set ty := lty_fold lt.
    have ?: Inhabited (~~𝔄) := populate x.
    iMod (proph_idx_bor_gen_acc_rebody_guarded E κ (uniq_prvar x₀ ξi) (uniq_cell x₀ d g γ) idx
      _ (uniq_gbody κp ty tid l)
      with "LFT UNIQ Gk Tok Bor G") as (wπ) "[Body Close]"; [solve_ndisj|].
    iDestruct (bi.later_or with "Body") as "[Body|[>Tf' _]]"; last first.
    { iDestruct (cpd_tok_excl with "Tf Tf'") as "[]". }
    rewrite cpd_body_cell.
    iMod (bi.later_exist_except_0 with "Body") as (p) "Body".
    iMod (bi.later_exist_except_0 with "Body") as (r1) "(_ & _ & >Gh' & Upd)".
    iDestruct (ghost_var_agree with "Gh Gh'") as %[<- <-]%lstate_inj.
    iMod (ghost_var_update_halves (lstate_triv x) with "Gh Gh'") as "[Gh Gh']".
    iSpecialize ("Close" $! (uniq_cell x d g γ) (vπ (uniq_cell x d g γ))).
    iMod (fupd_mask_mono with "(Close [Gh' Upd] [Tf])") as (idx') "(Tok & #Bor' & $)";
      [solve_ndisj| | |].
    { iApply (uniq_gbody_triv_close with "Gh'"); [done|]. iNext.
      rewrite uniq_payload_cell. iApply (guarded_upd_mono with "[] Upd").
      iIntros "[$ N]". iMod (Hconv with "N") as "[$ $]". done. }
    { iIntros "!>" (c2 w2) "P". iModIntro. iNext. iRight. iFrame. }
    iModIntro. iExists x, idx'. iSplit; [done|].
    iApply (uniq_body_from_parts with "Incl [Gh Tok] ⧗ [Bor']").
    - rewrite /uniq_tokγ (uniq_bor_tok_retarget _ x₀). iFrame.
    - by rewrite /uniq_persγ (uniq_idx_bor_gen_retarget _ _ x₀).
  Qed.
  (** The fold of the node of [UniqLty lt κ'] at [Owned 0] (an instance of
      [ltype_owned_unblock_fold]). *)
  Lemma uniq_node_unblock_fold {𝔄} (lt: lty 𝔄) κ κ' p r d g tid l G :
    lty_simple lt → Timeless G →
    time_ctx -∗ llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗
    (G &&{↑NllftG}&&> @[ty_lft (lty_fold (UniqLty lt κ'))]) -∗ pat_ok κ p -∗ [†κ] -∗ G -∗
    ⧖(S d `max` g) -∗ ltype_own_cp false (UniqLty lt κ') (Owned 0) p r d g tid l ={lazyE}=∗
      G ∗ ∃ x d' g', ▷ (prfn_den r :== vπ x) ∗ ⧖(S d' `max` g') ∗
        ofty_owned 0 (lty_fold (UniqLty lt κ')) x d' g' tid l.
  Proof. iIntros (??) "_". by iApply (ltype_owned_unblock_fold (UniqLty lt κ') κ 0). Qed.

  (** The node of [UniqLty lt κ'] is seen as the leaf of its folded type, as
      [ltype_owned_leaf_node]. *)
  Lemma ltype_owned_leaf_node_uniq {𝔄} (lt: lty 𝔄) κ' κp p r d g tid l :
    lty_simple lt →
    time_ctx -∗ llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ pat_ok κp p -∗ ⧖(S d `max` g) -∗
    ltype_own_cp false (UniqLty lt κ') (Owned 0) p r d g tid l -∗
    leaf_node κp (lty_fold (UniqLty lt κ')) p r d g tid l.
  Proof. iIntros (?) "_". by iApply (ltype_owned_leaf_node (UniqLty lt κ')). Qed.
End cpd.
