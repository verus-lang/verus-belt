From lrust.typing Require Export type.
From lrust.typing Require Import fixpoint unit struct sum mod_ty own subtype bytes_layout.
From lrust.prophecy Require Import syn_type.
Set Default Proof Using "Type".

Implicit Type 𝔄 𝔅 ℭ: syn_type.

(*
To instantiate a recursive type we need to define the morphism used over the
interpretation sort that is used for folding/unfolding.
We illustrate here for `list`, corresponding to:

```
enum List<T> { Nil, Cons(T, Box<List<T>>) }
```

For list, we (roughly speaking) need an isomorphism between
`listₛ 𝔄` and `(() + Node 𝔄)` (an enum), where the node `Node 𝔄` is a struct of the element
and the (boxed) tail. In practice it's a bit more complicated because of all the padding
and location information.

In general, it should be possible to find an interpretation sort satisfying the recursive
equation as long as it doesn't appear in any negative position.
This corresponds to the check Verus does for the well-formedness of recursive types.

See: _Verus: Verifying Rust Programs using Linear Ghost Types (extended version)_
https://arxiv.org/abs/2303.05491

Note that for the purposes of this check, what matters it the *interpretation sort*,
so "negative positions" may not correspond to what Rust considers "negative".
For example, any type could just have an interpretation sort of (),
which makes the recursive construction trivial.
(In fact, this is the whole reason that `atomic_inv_ty` is parameterized by the 
type ℭ used as the interpretation sort, rather than fixing the interpretation sort as
a boolean predicate 𝔄 → bool, which has 𝔄 in a negative position.
Our more general version thus allows more types to pass this check.)
*)

Definition rlistₛ 𝔄 : syn_type := at_locₛ (listₛ (𝔄 * locₛ)).

(** The layout of a node [Cons(T, Box<List<T>>)]: the element, then the pointer to the
    tail. It depends only on the size [n] of the element, so that the lists of types of the
    same size have the same node layout ([list_subtype]). *)
Definition list_node_layout (n: nat) : struct_layout := SL [0; n] (n + mty_size MPtr) 1.
Notation list_nodeₛ 𝔄 := (structₛ (list_node_layout (syn_bsize 𝔄)) [𝔄; rlistₛ 𝔄])%ST.

(** The layout of [Option<Node<T>>] (a [Nil] or a node): the tagged layout ([tagged_layout]),
    which also depends only on the size of the element. *)
Definition list_enum_layout (n: nat) : enum_layout :=
  tagged_layout [zst_mty; MTuple [] (n + mty_size MPtr) 1].
Notation list_sumₛ 𝔄 := (enumₛ (list_enum_layout (syn_bsize 𝔄)) [unitₛ; list_nodeₛ 𝔄])%ST.

Program Definition list_to_sumₛ {𝔄} : rlistₛ 𝔄 →ₛ at_locₛ (list_sumₛ 𝔄) := {|
  syn_type_morphism_fn := λ l, match l with
      | (loc0, []) => (loc0, inl ())
      | (loc0, (x, loc) :: xl) => (loc0, inr (inl -[x; (loc, xl)]))
  end;
  syn_type_morphism_proph_fn := λ l, match l with
      | (loc0, []) => (loc0, inl ())
      | (loc0, (x, loc) :: xl) => (loc0, inr (inl -[x; (loc, xl)]))
  end;
|}.
Next Obligation. intros 𝔄 [loc0 l] π. destruct l as [|[a c] xl]; done. Qed.
Next Obligation. intros 𝔄 [loc0 l]. destruct l as [|[a c] xl]; first done.
  fold indep_interp_of_syn_type. fold proph_interp_of_syn_type. simpl.
  by rewrite !List.app_nil_r.
Qed.

Program Definition sum_to_listₛ {𝔄} : at_locₛ (list_sumₛ 𝔄) →ₛ rlistₛ 𝔄  := {|
  syn_type_morphism_fn := λ s, match s with
      | (loc0, inl ()) => (loc0, [])
      | (loc0, inr (inl -[x; (loc, xl)])) => (loc0, (x, loc) :: xl)
      | (loc0, inr (inr a)) => absurd a
  end;
  syn_type_morphism_proph_fn := λ s, match s with
      | (loc0, inl ()) => (loc0, [])
      | (loc0, inr (inl -[x; (loc, xl)])) => (loc0, (x, loc) :: xl)
      | (loc0, inr (inr a)) => absurd a
  end;
|}.
Next Obligation. intros 𝔄 [loc0 [[]|[[elem [[loc l] []]]|[]]]] π; done. Qed.
Next Obligation. intros 𝔄 [loc0 [[]|[[elem [[loc l] []]]|[]]]]; first done.
  fold indep_interp_of_syn_type. fold proph_interp_of_syn_type. simpl.
  by rewrite !List.app_nil_r.
Qed.

(** Both are pointers, to the same location: the bytes are the same. *)
Lemma syn_bincl_sum_to_list {𝔄} : syn_bincl (sum_to_listₛ (𝔄:=𝔄)).
Proof. apply syn_bincl_same; [done|]. by intros [l [[]|[[x [[loc xl] []]]|[]]]]. Qed.

Local Instance sum_list_isoₛ {𝔄} : @Isoₛ
    (at_locₛ (list_sumₛ 𝔄))
    (rlistₛ 𝔄)
    sum_to_listₛ
    list_to_sumₛ.
Proof.
  split.
    - split.
      + fun_ext. intros [loc0 [[]|[[elem [[loc l] []]]|[]]]]; trivial.
      + fun_ext. intros [loc0 [|[a c] xl]]; trivial.
    - split.
      + fun_ext. intros [loc0 [[]|[[elem [[loc l] []]]|[]]]]; trivial.
      + fun_ext. intros [loc0 [|[a c] xl]]; trivial.
    - intros x bs. destruct x as [loc0 [[]|[[elem [[loc l] []]]|[]]]]; done.
    - apply syn_bincl_sum_to_list.
Qed.

Definition list_map1 {𝔄 𝔅} (f: 𝔄 →ₛ 𝔅) :
    (list (~~(𝔄 * locₛ))) → (list (~~(𝔅 * locₛ))) :=
    λ l, map (λ '(a, c), (f ~~$ₛ a, c)) l.
Definition list_map2 {𝔄 𝔅} (f: 𝔄 →ₛ 𝔅) :
    (list ((𝔄 * locₛ))) → (list ((𝔅 * locₛ))) :=
    λ l, map (λ '(a, c), (f $ₛ a, c)) l.
Program Definition list_mapₛ {𝔄 𝔅} (f: 𝔄 →ₛ 𝔅) : (rlistₛ 𝔄 →ₛ rlistₛ 𝔅) := {|
  syn_type_morphism_fn := (λ (t: ~~(rlistₛ 𝔄)), match t with (loc0, l) =>
    (loc0, list_map1 f l) end);
  syn_type_morphism_proph_fn := (λ (t: (rlistₛ 𝔄)), match t with (loc0, l) =>
    (loc0, list_map2 f l) end);
|}.
Next Obligation. fold indep_interp_of_syn_type. fold proph_interp_of_syn_type. intros.
  destruct x as [loc l]. simpl. f_equal.
  induction l as [|[a c] xl]; trivial.
  simpl. f_equal. f_equal.
   - rewrite syn_type_morphism_commutes. trivial.
   - apply IHxl.
Qed.
Next Obligation. fold indep_interp_of_syn_type. fold proph_interp_of_syn_type. intros.
  destruct x as [loc l]. simpl. f_equal.
  induction l as [|[a c] xl]; trivial.
  simpl. f_equal. f_equal.
   - rewrite <- syn_type_morphism_ξl. trivial.
   - apply IHxl.
Qed.

(** A list is a pointer to its first node, which [list_mapₛ] keeps: its bytes are
    preserved (whatever [f] does). *)
Lemma syn_bincl_list_map {𝔄 𝔅} (f: 𝔄 →ₛ 𝔅) : syn_bincl (list_mapₛ f).
Proof. apply syn_bincl_same; [done|]. by intros [??]. Qed.

(** The box of a list node owns the bytes of the sum; its size is syntactic. *)
Definition list_node_size 𝔄 : nat := syn_bsize (list_sumₛ 𝔄).

Section list.
  Context `{!typeG Σ}.

  Definition list_map {𝔄} (ty: type 𝔄) (ty': type (rlistₛ 𝔄)) : type (rlistₛ 𝔄) :=
    <{sum_to_listₛ ; list_to_sumₛ}>
      (own_bytes (list_node_size 𝔄)
        (enum_ty (list_enum_layout (syn_bsize 𝔄))
          +[(); struct_ty (list_node_layout (syn_bsize 𝔄)) +[ty; ty']]))%T.
End list.

(* In Rust:
  enum List<T> { Nil, Cons(T, Box<List<T>>) }
  
  This example folds at Box<List<T>> instead of List<T> because it's a bit easier.
  The boxes are boxes of bytes ([own_bytes]).
*)
Notation list_ty ty := (fix_ty (list_map ty)).

Section typing.
  Context `{!typeG Σ}.
    
  (* fold and unfold list *)
  Lemma list_unfold_fold {𝔄} (ty: type 𝔄) E L :
    eqtype E L (list_ty ty)
      (own_bytes (list_node_size 𝔄)
        (enum_ty (list_enum_layout (syn_bsize 𝔄))
          +[(); struct_ty (list_node_layout (syn_bsize 𝔄)) +[ty; list_ty ty]]))%T
        list_to_sumₛ sum_to_listₛ.
  Proof.
    eapply eqtype_eq.
    - eapply eqtype_trans.
      + apply fix_unfold_fold.
      + apply mod_ty_outin.
    - apply extensₛ; trivial.
    - apply extensₛ; trivial.
  Qed.
  
  Lemma list_resolve {𝔄} E L (ty: type 𝔄) Φ :
    resolve E L ty Φ → resolve E L (list_ty ty)
        (λ '(_, l) π, lforall (λ '(x,_), Φ x π) l).
  Proof.
    move=> ?. apply fix_resolve=> ??. eapply resolve_impl; [solve_typing|].
    intros [loc l]. generalize loc. clear loc.
    induction l as [|[x1 loc]]; trivial. by intros ?? [? [? _]].
  Qed.

  Lemma list_resolve_just {𝔄} E L (ty: type 𝔄) :
    resolve E L ty (const (const True)) → resolve E L (list_ty ty) (const (const True)).
  Proof. move=> ?. apply resolve_just. Qed.

  
  (** The size and the layout of a node depend on the element type, so the subtyping of
      the nodes needs [syn_bsize 𝔄 = syn_bsize 𝔅]; it is part of the subtyping of the
      elements ([subtype_bincl_elim]). The nodes are then structs of the same layout
      ([struct_relay_eqtype], [enum_relay_eqtype]). The fixpoint map [list_mapₛ f] preserves the bytes for any
      [f] ([syn_bincl_list_map]). *)
  Lemma list_subtype {𝔄 𝔅} E L (f: 𝔄 →ₛ 𝔅) ty ty' :
    subtype E L ty ty' f → subtype E L (list_ty ty) (list_ty ty') (list_mapₛ f).
  Proof.
    move=> Sub. apply (subtype_bincl_elim _ _ _ _ _ _ _ _ Sub)=> Hb.
    have HL : list_node_layout (syn_bsize 𝔄) = list_node_layout (syn_bsize 𝔅).
    { by rewrite (proj1 Hb). }
    pose g := (struct_relayₛ (𝔄l:=[𝔅; rlistₛ 𝔅])
      (list_node_layout (syn_bsize 𝔄)) (list_node_layout (syn_bsize 𝔅)) ∘ₛ
      struct_mapₛ (𝔄l:=[𝔄; rlistₛ 𝔄]) (𝔅l:=[𝔅; rlistₛ 𝔅])
        (list_node_layout (syn_bsize 𝔄)) -[f; list_mapₛ f]).
    have HEL : list_enum_layout (syn_bsize 𝔄) = list_enum_layout (syn_bsize 𝔅).
    { by rewrite (proj1 Hb). }
    have [Hsz _]: syn_bincl (enum_relayₛ (𝔄l:=[unitₛ; list_nodeₛ 𝔅])
        (list_enum_layout (syn_bsize 𝔄)) (list_enum_layout (syn_bsize 𝔅)) ∘ₛ
      enum_mapₛ (𝔄l:=[unitₛ; list_nodeₛ 𝔄]) (𝔅l:=[unitₛ; list_nodeₛ 𝔅])
        (list_enum_layout (syn_bsize 𝔄)) -[idₛ; g]).
    { apply syn_bincl_compose; [|by apply syn_bincl_enum_relay].
      apply syn_bincl_enum_map. intros i. inv_fin i; [done|]. intros i. inv_fin i.
      - apply syn_bincl_compose; [|by apply syn_bincl_struct_relay].
        apply syn_bincl_struct_map. intros i. inv_fin i; [done|]. intros i. inv_fin i.
        + apply syn_bincl_list_map.
        + intros i. inv_fin i.
      - intros i. inv_fin i. }
    apply fix_subtype.
    - apply syn_bincl_list_map.
    - intros. rewrite <- syn_type_morphism_ξl. trivial.
    - intros ty0 ty0' Sub'. rewrite /list_map /list_node_size Hsz. eapply subtype_eq.
      { apply mod_ty_subtype, own_bytes_subtype.
        eapply (subtype_trans _ (enum_ty (list_enum_layout (syn_bsize 𝔄))
          +[(); struct_ty (list_node_layout (syn_bsize 𝔅)) +[ty'; ty0']]%T));
          [|apply (proj1 (enum_relay_eqtype _ _ _ _ _ HEL))].
        apply enum_subtype.
        apply subtypel_cons; [solve_typing|]. apply subtypel_cons; [|solve_typing].
        eapply (subtype_trans _ (struct_ty (list_node_layout (syn_bsize 𝔄)) +[ty'; ty0']));
          [apply struct_subtype; solve_typing|].
        apply (proj1 (struct_relay_eqtype _ _ _ _ _ HL)). }
      apply extensₛ; fun_ext; intros [loc0 [|[x loc] xl]]; done.
  Qed.

  Lemma list_eqtype {𝔄 𝔅} E L (f: 𝔄 →ₛ 𝔅) (g: 𝔅 →ₛ 𝔄) ty ty' :
    eqtype E L ty ty' f g → eqtype E L (list_ty ty) (list_ty ty') (list_mapₛ f) (list_mapₛ g).
  Proof. move=> [??]. by split; apply list_subtype. Qed.
End typing.

Global Hint Resolve list_resolve | 5 : lrust_typing.
Global Hint Resolve list_resolve_just list_subtype list_eqtype : lrust_typing.
