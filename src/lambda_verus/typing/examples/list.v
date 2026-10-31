From lrust.typing Require Export type.
From lrust.typing Require Import fixpoint product sum mod_ty own_bytes.
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
`listₛ 𝔄` and `(() + (𝔄 * (listₛ 𝔄)))`. In practice it's a bit more complicated
because of all the padding and location information.

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

Definition rlistₛ 𝔄 : syn_type := at_locₛ (listₛ (𝔄 * paddingₛ * locₛ) * paddingₛ).

Program Definition list_to_sumₛ {𝔄} : rlistₛ 𝔄 →ₛ at_locₛ (Σ! [unitₛ ; prodₛ 𝔄 (rlistₛ 𝔄)]) := {|
  syn_type_morphism_fn := λ l, match l with
      | (loc0, ([], nil_padding)) => (loc0, (inl (), nil_padding))
      | (loc0, ((x, padding, loc) :: xl, nil_padding)) => (loc0, (inr (inl (x, (loc, (xl, nil_padding)))), padding))
  end;
  syn_type_morphism_proph_fn := λ l, match l with
      | (loc, ([], nil_padding)) => (loc, (inl (), nil_padding))
      | (loc0, ((x, padding, loc) :: xl, nil_padding)) => (loc0, (inr (inl (x, (loc, (xl, nil_padding)))), padding))
  end;
|}.
Next Obligation. intros 𝔄 [loc0 [l np]] π. destruct l as [|[[a b] c] xl]; done. Qed.
Next Obligation. intros 𝔄 [loc0 [l np]]. destruct l as [|[[a b] c] xl]; first done.
  fold indep_interp_of_syn_type. fold proph_interp_of_syn_type. simpl.
  do 4 (rewrite List.app_nil_r). done.
Qed.
  
Program Definition sum_to_listₛ {𝔄} : at_locₛ (Σ! [unitₛ ; prodₛ 𝔄 (rlistₛ 𝔄)]) →ₛ rlistₛ 𝔄  := {|
  syn_type_morphism_fn := λ s, match s with
      | (loc0, (inl (), padding)) => (loc0, ([], padding))
      | (loc0, (inr (inl (x, (loc, (xl, nil_padding)))), padding)) => (loc0, ((x, padding, loc) :: xl, nil_padding))
      | (loc0, (inr (inr a), _)) => absurd a
  end; 
  syn_type_morphism_proph_fn := λ s, match s with
      | (loc0, (inl (), padding)) => (loc0, ([], padding))
      | (loc0, (inr (inl (x, (loc, (xl, nil_padding)))), padding)) => (loc0, ((x, padding, loc) :: xl, nil_padding))
      | (loc0, (inr (inr a), _)) => absurd a
  end; 
|}.
Next Obligation. intros 𝔄 [loc0 [[[]|[[elem [loc [l np]]]|[]]] p]] π; done. Qed.
Next Obligation. intros 𝔄 [loc0 [[[]|[[elem [loc [l np]]]|[]]] p]]; first done.
  fold indep_interp_of_syn_type. fold proph_interp_of_syn_type. simpl.
  do 4 (rewrite List.app_nil_r). done.
Qed.

Local Instance sum_list_isoₛ {𝔄} : @Isoₛ
    (at_locₛ (Σ! [unitₛ ; prodₛ 𝔄 (rlistₛ 𝔄)]))
    (rlistₛ 𝔄)
    sum_to_listₛ
    list_to_sumₛ.
Proof.
  split.
    - split.
      + fun_ext. intros [loc0 [[[]|[[elem [loc [l np]]]|[]]] p]]; trivial.
      + fun_ext. intros [loc0 [[|[[a b] c] xl] np]]; trivial.
    - split.
      + fun_ext. intros [loc0 [[[]|[[elem [loc [l np]]]|[]]] p]]; trivial.
      + fun_ext. intros [loc0 [[|[[a b] c] xl] np]]; trivial.
    - trivial.
    - destruct x as [loc0 [[[]|[[elem [loc [l np]]]|[]]] p]]; done.
    - done.
    - intros x bs. destruct x as [loc0 [[[]|[[elem [loc [l np]]]|[]]] p]]; done.
Qed.
    
    
Definition list_map1 {𝔄 𝔅} (f: 𝔄 →ₛ 𝔅) :
    (list (~~(𝔄 * paddingₛ * locₛ))) → (list (~~(𝔅 * paddingₛ * locₛ))) :=
    λ l, map (λ '(a, b, c), (f ~~$ₛ a, b, c)) l.
Definition list_map2 {𝔄 𝔅} (f: 𝔄 →ₛ 𝔅) :
    (list ((𝔄 * paddingₛ * locₛ))) → (list ((𝔅 * paddingₛ * locₛ))) :=
    λ l, map (λ '(a, b, c), (f $ₛ a, b, c)) l.
Program Definition list_mapₛ {𝔄 𝔅} (f: 𝔄 →ₛ 𝔅) : (rlistₛ 𝔄 →ₛ rlistₛ 𝔅) := {|
  syn_type_morphism_fn := (λ (t: ~~(rlistₛ 𝔄)), match t with (loc0, (l, nil_pad)) =>
    (loc0, (list_map1 f l, nil_pad)) end);
  syn_type_morphism_proph_fn := (λ (t: (rlistₛ 𝔄)), match t with (loc0, (l, nil_pad)) =>
    (loc0, (list_map2 f l, nil_pad)) end);
|}.
Next Obligation. fold indep_interp_of_syn_type. fold proph_interp_of_syn_type. intros.
  destruct x as [loc [l nil_pad]]. simpl. f_equal. f_equal.
  induction l as [|[[a b] c] xl]; trivial. 
  simpl. f_equal. f_equal.
   - rewrite syn_type_morphism_commutes. trivial.
   - apply IHxl.
Qed.
Next Obligation. fold indep_interp_of_syn_type. fold proph_interp_of_syn_type. intros.
  destruct x as [loc [l nil_pad]]. simpl. f_equal. f_equal.
  induction l as [|[[a b] c] xl]; trivial. 
  simpl. f_equal. f_equal.
   - rewrite <- syn_type_morphism_ξl. trivial.
   - apply IHxl.
Qed.

    
(** The box of a list node owns the bytes of the sum; its size is syntactic. *)
Definition list_node_size 𝔄 : nat := syn_bsize (Σ! [unitₛ ; prodₛ 𝔄 (rlistₛ 𝔄)]).

Section list.
  Context `{!typeG Σ}.

  Definition list_map {𝔄} (ty: type 𝔄) (ty': type (rlistₛ 𝔄)) : type (rlistₛ 𝔄) :=
    <{sum_to_listₛ ; list_to_sumₛ}> (own_bytes (list_node_size 𝔄) (Σ! +[(); ty * ty']))%T.
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
    eqtype E L (list_ty ty) (own_bytes (list_node_size 𝔄) (Σ! +[(); ty * list_ty ty]))%T
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
        (λ '(_, (l, _)) π, lforall (λ '(x,_,_), Φ x π) l).
  Proof.
    move=> ?. apply fix_resolve=> ??. eapply resolve_impl; [solve_typing|].
    intros [loc [l padding]].  generalize loc. clear loc.
    induction l as [|[[x1 pad] loc]]; trivial.
  Qed.

  Lemma list_resolve_just {𝔄} E L (ty: type 𝔄) :
    resolve E L ty (const (const True)) → resolve E L (list_ty ty) (const (const True)).
  Proof. move=> ?. apply resolve_just. Qed.

  
End typing.

Global Hint Resolve list_resolve | 5 : lrust_typing.
Global Hint Resolve list_resolve_just : lrust_typing.
