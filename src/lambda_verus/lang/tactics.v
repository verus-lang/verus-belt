From stdpp Require Import fin_maps.
From lrust.lang Require Export lang.
Set Default Proof Using "Type".

(** We define an alternative representation of expressions in which the
embedding of values and closed expressions is explicit. By reification of
expressions into this type we can implement substitution, closedness
checking, atomic checking, and conversion into values, by computation. *)
Module W.
Inductive expr :=
| Val (v : val) (e : lang.expr) (H : to_val e = Some v)
| ClosedExpr (e : lang.expr) `{!Closed [] e}
| Var (x : string)
| Rec (f : binder) (xl : list binder) (e : expr)
| BinOp (op : bin_op) (e1 e2 : expr)
| NdInt
| App (e : expr) (el : list expr)
| Alloc (e : expr)
| Free (e1 e2 : expr)
| Case (e : expr) (el : list expr)
| Fork (e : expr)
| GlobalLock
| GlobalUnlock
| MLit (v : Value)
| Load (o : order) (m : mty) (e : expr)
| Store (o : order) (m : mty) (e1 e2 : expr)
| MemCopy (o : order) (n : nat) (e1 e2 : expr)
| MkTuple (el : list expr)
| Proj (i : nat) (e : expr)
| MkVariant (t : Z) (e : expr)
| VariantTag (e : expr)
| VariantData (e : expr)
| MCAS (m : mty) (e0 e1 e2 : expr)
.

Fixpoint to_expr (e : expr) : lang.expr :=
  match e with
  | Val v e' _ => e'
  | ClosedExpr e => e
  | Var x => lang.Var x
  | Rec f xl e => lang.Rec f xl (to_expr e)
  | BinOp op e1 e2 => lang.BinOp op (to_expr e1) (to_expr e2)
  | NdInt => lang.NdInt
  | App e el => lang.App (to_expr e) (map to_expr el)
  | Alloc e => lang.Alloc (to_expr e)
  | Free e1 e2 => lang.Free (to_expr e1) (to_expr e2)
  | Case e el => lang.Case (to_expr e) (map to_expr el)
  | Fork e => lang.Fork (to_expr e)
  | GlobalLock => lang.GlobalLock
  | GlobalUnlock => lang.GlobalUnlock
  | MLit v => lang.MLit v
  | Load o m e => lang.Load o m (to_expr e)
  | Store o m e1 e2 => lang.Store o m (to_expr e1) (to_expr e2)
  | MemCopy o n e1 e2 => lang.MemCopy o n (to_expr e1) (to_expr e2)
  | MkTuple el => lang.MkTuple (map to_expr el)
  | Proj i e => lang.Proj i (to_expr e)
  | MkVariant t e => lang.MkVariant t (to_expr e)
  | VariantTag e => lang.VariantTag (to_expr e)
  | VariantData e => lang.VariantData (to_expr e)
  | MCAS m e0 e1 e2 => lang.MCAS m (to_expr e0) (to_expr e1) (to_expr e2)
  end.

Ltac of_expr e :=
  lazymatch e with
  | lang.Var ?x => constr:(Var x)
  | lang.Rec ?f ?xl ?e => let e := of_expr e in constr:(Rec f xl e)
  | lang.BinOp ?op ?e1 ?e2 =>
    let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(BinOp op e1 e2)
  | lang.NdInt => constr:(NdInt)
  | lang.App ?e ?el =>
    let e := of_expr e in let el := of_expr el in constr:(App e el)
  | lang.Alloc ?e => let e := of_expr e in constr:(Alloc e)
  | lang.Free ?e1 ?e2 =>
    let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(Free e1 e2)
  | lang.Case ?e ?el =>
     let e := of_expr e in let el := of_expr el in constr:(Case e el)
  | lang.Fork ?e => let e := of_expr e in constr:(Fork e)
  | @nil lang.expr => constr:(@nil expr)
  | @cons lang.expr ?e ?el =>
    let e := of_expr e in let el := of_expr el in constr:(e::el)
  | to_expr ?e => e
  | of_val ?v => constr:(Val v (of_val v) (to_of_val v))
  | lang.GlobalLock => constr:(GlobalLock)
  | lang.GlobalUnlock => constr:(GlobalUnlock)
  | lang.MLit ?v => constr:(MLit v)
  | lang.Load ?o ?m ?e => let e := of_expr e in constr:(Load o m e)
  | lang.read_copy ?m ?e => let e := of_expr e in constr:(Load Na1Ord m e)
  | lang.read_move ?m ?e => let e := of_expr e in constr:(Load Na1Ord m e)
  | lang.write ?m ?e1 ?e2 =>
    let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(Store Na1Ord m e1 e2)
  | lang.share ?e =>
    let e' := eval unfold lang.share in (lang.share e) in of_expr e'
  | lang.borrow_uniq ?e =>
    let e' := eval unfold lang.borrow_uniq in (lang.borrow_uniq e) in of_expr e'
  | lang.memcpy ?n ?e1 ?e2 =>
    let e' := eval unfold lang.memcpy in (lang.memcpy n e1 e2) in of_expr e'
  | lang.Store ?o ?m ?e1 ?e2 =>
    let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(Store o m e1 e2)
  | lang.MemCopy ?o ?n ?e1 ?e2 =>
    let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(MemCopy o n e1 e2)
  | lang.MkTuple ?el => let el := of_expr el in constr:(MkTuple el)
  | lang.Proj ?i ?e => let e := of_expr e in constr:(Proj i e)
  | lang.MkVariant ?t ?e => let e := of_expr e in constr:(MkVariant t e)
  | lang.VariantTag ?e => let e := of_expr e in constr:(VariantTag e)
  | lang.VariantData ?e => let e := of_expr e in constr:(VariantData e)
  | lang.MCAS ?m ?e0 ?e1 ?e2 =>
     let e0 := of_expr e0 in let e1 := of_expr e1 in let e2 := of_expr e2 in
     constr:(MCAS m e0 e1 e2)
  | _ => match goal with
         | H : to_val e = Some ?v |- _ => constr:(Val v e H)
         | H : Closed [] e |- _ => constr:(@ClosedExpr e H)
         end
  end.

Fixpoint is_closed (X : list string) (e : expr) : bool :=
  match e with
  | Val _ _ _ | ClosedExpr _ => true
  | Var x => bool_decide (x ∈ X)
  | NdInt | GlobalLock | GlobalUnlock | MLit _ => true
  | Rec f xl e => is_closed (f :b: xl +b+ X) e
  | BinOp _ e1 e2 | Free e1 e2 | Store _ _ e1 e2 | MemCopy _ _ e1 e2 =>
    is_closed X e1 && is_closed X e2
  | App e el | Case e el => is_closed X e && forallb (is_closed X) el
  | MkTuple el => forallb (is_closed X) el
  | Alloc e | Fork e | Load _ _ e | Proj _ e | MkVariant _ e
  | VariantTag e | VariantData e => is_closed X e
  | MCAS _ e0 e1 e2 => is_closed X e0 && is_closed X e1 && is_closed X e2
  end.
Lemma is_closed_correct X e : is_closed X e → lang.is_closed X (to_expr e).
Proof.
  revert e X. fix FIX 1; destruct e=>/=;
    try naive_solver eauto using is_closed_to_val, is_closed_weaken_nil.
  - induction el=>/=; naive_solver.
  - induction el=>/=; naive_solver.
  - induction el=>/=; naive_solver.
Qed.

(* We define [to_val (ClosedExpr _)] to be [None] since [ClosedExpr]
constructors are only generated for closed expressions of which we know nothing
about apart from being closed. Notice that the reverse implication of
[to_val_Some] thus does not hold. *)
Definition to_val (e : expr) : option val :=
  match e with
  | Val v _ _ => Some v
  | Rec f xl e =>
    if decide (is_closed (f :b: xl +b+ []) e) is left H
    then Some (@RecV f xl (to_expr e) (is_closed_correct _ _ H)) else None
  | MLit v => Some (MLitV v)
  | _ => None
  end.
Lemma to_val_Some e v :
  to_val e = Some v → of_val v = W.to_expr e.
Proof.
  revert v. induction e; intros; simplify_option_eq; auto using of_to_val.
Qed.
Lemma to_val_is_Some e :
  is_Some (to_val e) → ∃ v, of_val v = to_expr e.
Proof. intros [v ?]; exists v; eauto using to_val_Some. Qed.
Lemma to_val_is_Some' e :
  is_Some (to_val e) → is_Some (lang.to_val (to_expr e)).
Proof. intros [v ?]%to_val_is_Some. exists v. rewrite -to_of_val. by f_equal. Qed.

Fixpoint subst (x : string) (es : expr) (e : expr)  : expr :=
  match e with
  | Val v e H => Val v e H
  | ClosedExpr e => ClosedExpr e
  | Var y => if bool_decide (y = x) then es else Var y
  | Rec f xl e =>
    Rec f xl $ if bool_decide (BNamed x ≠ f ∧ BNamed x ∉ xl) then subst x es e else e
  | BinOp op e1 e2 => BinOp op (subst x es e1) (subst x es e2)
  | NdInt => NdInt
  | App e el => App (subst x es e) (map (subst x es) el)
  | Alloc e => Alloc (subst x es e)
  | Free e1 e2 => Free (subst x es e1) (subst x es e2)
  | Case e el => Case (subst x es e) (map (subst x es) el)
  | Fork e => Fork (subst x es e)
  | GlobalLock => GlobalLock
  | GlobalUnlock => GlobalUnlock
  | MLit v => MLit v
  | Load o m e => Load o m (subst x es e)
  | Store o m e1 e2 => Store o m (subst x es e1) (subst x es e2)
  | MemCopy o n e1 e2 => MemCopy o n (subst x es e1) (subst x es e2)
  | MkTuple el => MkTuple (map (subst x es) el)
  | Proj i e => Proj i (subst x es e)
  | MkVariant t e => MkVariant t (subst x es e)
  | VariantTag e => VariantTag (subst x es e)
  | VariantData e => VariantData (subst x es e)
  | MCAS m e0 e1 e2 => MCAS m (subst x es e0) (subst x es e1) (subst x es e2)
  end.
Lemma to_expr_subst x er e :
  to_expr (subst x er e) = lang.subst x (to_expr er) (to_expr e).
Proof.
  revert e x er. fix FIX 1; destruct e=>/= ? er; repeat case_bool_decide;
    f_equal; eauto using is_closed_nil_subst, is_closed_to_val, eq_sym.
  - induction el=>//=. f_equal; auto.
  - induction el=>//=. f_equal; auto.
  - induction el=>//=. f_equal; auto.
Qed.

Definition is_atomic (e: expr) : bool :=
  match e with
  | Alloc e => bool_decide (is_Some (to_val e))
  | Free e1 e2 =>
    bool_decide (is_Some (to_val e1) ∧ is_Some (to_val e2))
  | MCAS _ e0 e1 e2 =>
    bool_decide (is_Some (to_val e0) ∧ is_Some (to_val e1) ∧ is_Some (to_val e2))
  | Load (ScOrd | Na2Ord) _ e => bool_decide (is_Some (to_val e))
  | Store (ScOrd | Na2Ord) _ e1 e2 | MemCopy (ScOrd | Na2Ord) _ e1 e2 =>
    bool_decide (is_Some (to_val e1) ∧ is_Some (to_val e2))
  | _ => false
  end.
Lemma is_atomic_correct e : is_atomic e → Atomic WeaklyAtomic (to_expr e).
Proof.
  intros He. apply ectx_language_atomic.
  - intros σ e' σ' ef.
    destruct e; simpl; try done; repeat (case_match; try done);
    inversion 1; try (apply val_irreducible; rewrite ?language.to_of_val; naive_solver eauto).
    all: rewrite -[stuck_term](fill_empty); apply stuck_irreducible.
  - apply ectxi_language_sub_redexes_are_values=> /= Ki e' Hfill.
    revert He. destruct e; simpl; try done; repeat (case_match; try done);
    rewrite ?bool_decide_spec;
    destruct Ki; inversion Hfill; subst; clear Hfill;
    try naive_solver eauto using to_val_is_Some'.
Qed.
End W.

Ltac solve_closed :=
  match goal with
  | |- Closed ?X ?e =>
     let e' := W.of_expr e in change (Closed X (W.to_expr e'));
     apply W.is_closed_correct; vm_compute; exact I
  end.
Global Hint Extern 0 (Closed _ _) => solve_closed : typeclass_instances.

Ltac solve_into_val :=
  match goal with
  | |- IntoVal ?e ?v =>
     let e' := W.of_expr e in change (of_val v = W.to_expr e');
     apply W.to_val_Some; simpl; unfold W.to_expr;
     ((unlock; exact eq_refl) || (idtac; exact eq_refl))
  end.
Global Hint Extern 10 (IntoVal _ _) => solve_into_val : typeclass_instances.

Ltac solve_as_val :=
  match goal with
  | |- AsVal ?e =>
     let e' := W.of_expr e in change (∃ v, of_val v = W.to_expr e');
     apply W.to_val_is_Some, (bool_decide_unpack _); vm_compute; exact I
  end.
Global Hint Extern 10 (AsVal _) => solve_as_val : typeclass_instances.

Ltac solve_atomic :=
  match goal with
  | |- Atomic ?s ?e =>
     let e' := W.of_expr e in change (Atomic s (W.to_expr e'));
     apply W.is_atomic_correct; vm_compute; exact I
  end.
Global Hint Extern 0 (Atomic _ _) => solve_atomic : typeclass_instances.

(** Substitution *)
Ltac simpl_subst :=
  unfold subst_v; simpl;
  repeat match goal with
  | |- context [subst ?x ?er ?e] =>
      let er' := W.of_expr er in let e' := W.of_expr e in
      change (subst x er e) with (subst x (W.to_expr er') (W.to_expr e'));
      rewrite <-(W.to_expr_subst x); simpl (* ssr rewrite is slower *)
  end;
  unfold W.to_expr; simpl.
Arguments W.to_expr : simpl never.
Arguments subst : simpl never.

(** The tactic [inv_head_step] performs inversion on hypotheses of the
shape [head_step]. The tactic will discharge head-reductions starting
from values, and simplifies hypothesis related to conversions from and
to values, and finite map operations. This tactic is slightly ad-hoc
and tuned for proving our lifting lemmas. *)
Ltac inv_head_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : MLit _ = of_val ?v |- _ =>
    apply (f_equal (to_val)) in H; rewrite to_of_val in H;
    injection H; clear H; intro
  | H : context [to_val (of_val _)] |- _ => rewrite to_of_val in H
  | H : head_step ?e _ _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
     inversion H; subst; clear H
  end.

(** The tactic [reshape_expr e tac] decomposes the expression [e] into an
evaluation context [K] and a subexpression [e']. It calls the tactic [tac K e']
for each possible decomposition until [tac] succeeds. *)
Ltac reshape_val e tac :=
  let rec go e :=
  match e with
  | of_val ?v => v
  | MLit ?v => constr:(MLitV v)
  | Rec ?f ?xl ?e => constr:(RecV f xl e)
  end in let v := go e in tac v.

Ltac reshape_expr e tac :=
  let rec go_fun K f vs es :=
    match es with
    | ?e :: ?es => reshape_val e ltac:(fun v => go_fun K f (v :: vs) es)
    | ?e :: ?es => go (AppRCtx f (reverse vs) es :: K) e
    end
  with go_tuple K vs es :=
    match es with
    | ?e :: ?es => reshape_val e ltac:(fun v => go_tuple K (v :: vs) es)
    | ?e :: ?es => go (MkTupleCtx (reverse vs) es :: K) e
    end
  with go K e :=
  match e with
  | _ => tac K e
  | BinOp ?op ?e1 ?e2 =>
     reshape_val e1 ltac:(fun v1 => go (BinOpRCtx op v1 :: K) e2)
  | BinOp ?op ?e1 ?e2 => go (BinOpLCtx op e2 :: K) e1
  | App ?e ?el => reshape_val e ltac:(fun f => go_fun K f (@nil val) el)
  | App ?e ?el => go (AppLCtx el :: K) e
  | Alloc ?e => go (AllocCtx :: K) e
  | Free ?e1 ?e2 => reshape_val e1 ltac:(fun v1 => go (FreeRCtx v1 :: K) e2)
  | Free ?e1 ?e2 => go (FreeLCtx e2 :: K) e1
  | Case ?e ?el => go (CaseCtx el :: K) e
  | Load ?o ?m ?e => go (LoadCtx o m :: K) e
  | Store ?o ?m ?e1 ?e2 =>
    reshape_val e1 ltac:(fun v1 => go (StoreRCtx o m v1 :: K) e2)
  | Store ?o ?m ?e1 ?e2 => go (StoreLCtx o m e2 :: K) e1
  | MemCopy ?o ?n ?e1 ?e2 =>
    reshape_val e1 ltac:(fun v1 => go (MemCopyRCtx o n v1 :: K) e2)
  | MemCopy ?o ?n ?e1 ?e2 => go (MemCopyLCtx o n e2 :: K) e1
  | MkTuple ?el => go_tuple K (@nil val) el
  | Proj ?i ?e => go (ProjCtx i :: K) e
  | MkVariant ?t ?e => go (MkVariantCtx t :: K) e
  | VariantTag ?e => go (VariantTagCtx :: K) e
  | VariantData ?e => go (VariantDataCtx :: K) e
  | MCAS ?m ?e0 ?e1 ?e2 => reshape_val e0 ltac:(fun v0 => first
     [ reshape_val e1 ltac:(fun v1 => go (MCasRCtx m v0 v1 :: K) e2)
     | go (MCasMCtx m v0 e2 :: K) e1 ])
  | MCAS ?m ?e0 ?e1 ?e2 => go (MCasLCtx m e1 e2 :: K) e0
  end
  in go (@nil ectx_item) e.
