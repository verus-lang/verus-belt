(** * A MiniRust-style fragment of values, types and abstract bytes

This file defines, following MiniRust
(https://github.com/minirust/minirust, [spec/mem/interface.md],
[spec/lang/values.md], [spec/lang/types.md], [spec/lang/representation.md]):

- [AbstractByte]: the contents of one byte of memory;
- [Value]: the values at the "root" (integers, Booleans, pointers, tuples and
  variants; no unions yet);
- [mty]: a shallow fragment of the MiniRust types ("MiniRust types"), which
  parameterise the representation relation;
- [encode_value] and [decode_value], and their laws: the round trip
  [decode_value m (encode_value m v) = Some v] for well-formed [v], the length law
  [length (encode_value m v) = mty_size m], and monotonicity of [decode_value] with respect
  to the "less defined" order on bytes ([Uninit] is below everything), and well-formedness
  of decoded values ([decode_value_wf]).

Deviations from MiniRust (see [design_docs/minirust-memory-model.md]):
- Locations are abstract (block, offset) pairs, so a pointer is not an integer
  address with provenance. A pointer [l] occupies [PTR_SIZE] bytes
  [PtrFrag l 0], ..., [PtrFrag l (PTR_SIZE-1)].
- [PTR_SIZE] is abstract: it is sealed, and only [PTR_SIZE_pos] is exported.
- Integers of [n] bytes are encoded as [n] little-endian [Init] bytes of the
  two's complement representation.
- [decode_int] fails on an integer out of the range of its type. This only happens for a
  signed type of size 0, which MiniRust does not have; it makes every decoded value
  well-formed.
- An enum has a simple tag (an integer of type [tag]) at offset 0, and the data
  of variant [i] at offset [int_size tag]; there is no discriminator tree.
- The legacy case [Word w] of [AbstractByte] (for the one-word memory operations of
  lambda-Rust) was deleted in stage 6. *)

From stdpp Require Export strings gmap list.
From stdpp Require Import ssreflect.
Set Default Proof Using "Type".

Local Open Scope Z_scope.

(** ** Locations *)
Definition block : Set := positive.
Definition loc : Set := block * Z.

Declare Scope loc_scope.
Bind Scope loc_scope with loc.
Delimit Scope loc_scope with L.

(** ** Sizes *)

(** The size of a pointer, in bytes. It is sealed, so that no proof depends on
    its value; only [PTR_SIZE_pos] is known. *)
Local Definition PTR_SIZE_def : nat := 8.
Local Definition PTR_SIZE_aux : seal (@PTR_SIZE_def). Proof. by eexists. Qed.
Definition PTR_SIZE : nat := PTR_SIZE_aux.(unseal).
Local Definition PTR_SIZE_unseal : PTR_SIZE = PTR_SIZE_def := PTR_SIZE_aux.(seal_eq).

Lemma PTR_SIZE_pos : (0 < PTR_SIZE)%nat.
Proof. rewrite PTR_SIZE_unseal /PTR_SIZE_def. lia. Qed.

(** Integer types: signedness and size in bytes. *)
Record IntType := IntTy { int_signed : bool; int_size : nat }.

Global Instance IntType_eq_dec : EqDecision IntType.
Proof. solve_decision. Defined.

Definition usize : IntType := IntTy false PTR_SIZE.
Definition isize : IntType := IntTy true PTR_SIZE.
Definition i8 : IntType := IntTy true 1.
Definition i16 : IntType := IntTy true 2.
Definition i32 : IntType := IntTy true 4.
Definition i64 : IntType := IntTy true 8.
Definition u8 : IntType := IntTy false 1.
Definition u16 : IntType := IntTy false 2.
Definition u32 : IntType := IntTy false 4.
Definition u64 : IntType := IntTy false 8.

(** [2 ^ (8 * int_size it)] *)
Definition int_modulus (it : IntType) : Z := 256 ^ (Z.of_nat (int_size it)).

Definition int_in_range (it : IntType) (z : Z) : Prop :=
  if int_signed it then - (int_modulus it / 2) ≤ z < int_modulus it / 2
  else 0 ≤ z < int_modulus it.

Global Instance int_in_range_dec it z : Decision (int_in_range it z).
Proof. rewrite /int_in_range. destruct (int_signed it); apply _. Defined.

Lemma int_modulus_pos it : 0 < int_modulus it.
Proof. apply Z.pow_pos_nonneg; lia. Qed.

(** ** Values *)
Inductive Value : Set :=
| VInt (z : Z)
| VBool (b : bool)
| VPtr (l : loc)
| VTuple (vs : list Value)
| VVariant (tag : Z) (data : Value).

Lemma Value_ind' (P : Value → Prop) :
  (∀ z, P (VInt z)) → (∀ b, P (VBool b)) → (∀ l, P (VPtr l)) →
  (∀ vs, Forall P vs → P (VTuple vs)) →
  (∀ t d, P d → P (VVariant t d)) →
  ∀ v, P v.
Proof.
  intros Hi Hb Hp Ht Hv.
  refine (fix FIX v := match v with
    | VInt z => Hi z | VBool b => Hb b | VPtr l => Hp l
    | VTuple vs => Ht vs ((fix go vs := match vs return Forall P vs with
        | [] => @List.Forall_nil _ P | v :: vs => @List.Forall_cons _ P v vs (FIX v) (go vs) end) vs)
    | VVariant t d => Hv t d (FIX d)
    end).
Qed.

Fixpoint Value_beq (v1 v2 : Value) : bool :=
  match v1, v2 with
  | VInt z1, VInt z2 => bool_decide (z1 = z2)
  | VBool b1, VBool b2 => bool_decide (b1 = b2)
  | VPtr l1, VPtr l2 => bool_decide (l1 = l2)
  | VTuple vs1, VTuple vs2 =>
      (fix go vs1 vs2 := match vs1, vs2 with
        | [], [] => true
        | v1 :: vs1, v2 :: vs2 => Value_beq v1 v2 && go vs1 vs2
        | _, _ => false end) vs1 vs2
  | VVariant t1 d1, VVariant t2 d2 => bool_decide (t1 = t2) && Value_beq d1 d2
  | _, _ => false
  end.

Lemma Value_beq_correct v1 v2 : Value_beq v1 v2 ↔ v1 = v2.
Proof.
  revert v2. induction v1 as [| | |vs1 IH|t1 d1 IH] using Value_ind';
    intros [| | |vs2|t2 d2]; simpl;
    rewrite ?andb_True ?bool_decide_spec; try naive_solver.
  revert vs2. induction IH as [|v1 vs1 Hv1 _ IH]; intros [|v2 vs2]; try naive_solver.
Qed.

Global Instance Value_eq_dec : EqDecision Value.
Proof.
  refine (λ v1 v2, cast_if (decide (Value_beq v1 v2))); by rewrite -Value_beq_correct.
Defined.

Global Instance Value_inhabited : Inhabited Value := populate (VTuple []).

(** ** MiniRust types *)

(** A tuple lists its fields with their offsets, and has a total size; the bytes
    not covered by a field are padding. An enum lists the types of the data of
    its variants; it has a tag of type [tag] at offset 0, and the data at offset
    [int_size tag]. *)
Inductive mty : Set :=
| MInt (it : IntType)
| MBool
| MPtr
| MTuple (fields : list (nat * mty)) (size : nat)
| MEnum (variants : list mty) (tag : IntType) (size : nat).

Lemma mty_ind' (P : mty → Prop) :
  (∀ it, P (MInt it)) → P MBool → P MPtr →
  (∀ fs sz, Forall (λ f, P f.2) fs → P (MTuple fs sz)) →
  (∀ vars tag sz, Forall P vars → P (MEnum vars tag sz)) →
  ∀ m, P m.
Proof.
  intros Hi Hb Hp Ht He.
  refine (fix FIX m := match m with
    | MInt it => Hi it | MBool => Hb | MPtr => Hp
    | MTuple fs sz => Ht fs sz ((fix go fs := match fs return Forall (λ f, P f.2) fs with
        | [] => @List.Forall_nil _ _
        | (o, fm) :: fs => @List.Forall_cons _ (λ f, P f.2) (o, fm) fs (FIX fm) (go fs) end) fs)
    | MEnum vars tag sz => He vars tag sz ((fix go vars := match vars return Forall P vars with
        | [] => @List.Forall_nil _ P | vm :: vars => @List.Forall_cons _ P vm vars (FIX vm) (go vars) end) vars)
    end).
Qed.

Fixpoint mty_beq (m1 m2 : mty) : bool :=
  match m1, m2 with
  | MInt it1, MInt it2 => bool_decide (it1 = it2)
  | MBool, MBool | MPtr, MPtr => true
  | MTuple fs1 sz1, MTuple fs2 sz2 =>
      bool_decide (sz1 = sz2) &&
      (fix go fs1 fs2 := match fs1, fs2 with
        | [], [] => true
        | (o1, f1) :: fs1, (o2, f2) :: fs2 =>
            bool_decide (o1 = o2) && mty_beq f1 f2 && go fs1 fs2
        | _, _ => false end) fs1 fs2
  | MEnum vs1 t1 sz1, MEnum vs2 t2 sz2 =>
      bool_decide (t1 = t2) && bool_decide (sz1 = sz2) &&
      (fix go vs1 vs2 := match vs1, vs2 with
        | [], [] => true
        | v1 :: vs1, v2 :: vs2 => mty_beq v1 v2 && go vs1 vs2
        | _, _ => false end) vs1 vs2
  | _, _ => false
  end.

Lemma mty_beq_correct m1 m2 : mty_beq m1 m2 ↔ m1 = m2.
Proof.
  revert m2. induction m1 as [| | |fs1 sz1 IH|vs1 t1 sz1 IH] using mty_ind';
    intros [| | |fs2 sz2|vs2 t2 sz2]; simpl;
    rewrite ?andb_True ?bool_decide_spec; try naive_solver.
  - cut ((fix go (fs1 fs2 : list (nat * mty)) := match fs1, fs2 with
        | [], [] => true
        | (o1, f1) :: fs1, (o2, f2) :: fs2 =>
            bool_decide (o1 = o2) && mty_beq f1 f2 && go fs1 fs2
        | _, _ => false end) fs1 fs2 ↔ fs1 = fs2); [naive_solver|].
    revert fs2. induction IH as [|[o1 f1] fs1 Hf1 _ IH]; intros [|[o2 f2] fs2]; try naive_solver.
  - cut ((fix go (vs1 vs2 : list mty) := match vs1, vs2 with
        | [], [] => true
        | v1 :: vs1, v2 :: vs2 => mty_beq v1 v2 && go vs1 vs2
        | _, _ => false end) vs1 vs2 ↔ vs1 = vs2); [naive_solver|].
    revert vs2. induction IH as [|v1 vs1 Hv1 _ IH]; intros [|v2 vs2]; try naive_solver.
Qed.

Global Instance mty_eq_dec : EqDecision mty.
Proof.
  refine (λ m1 m2, cast_if (decide (mty_beq m1 m2))); by rewrite -mty_beq_correct.
Defined.

Definition mty_size (m : mty) : nat :=
  match m with
  | MInt it => int_size it
  | MBool => 1
  | MPtr => PTR_SIZE
  | MTuple _ sz | MEnum _ _ sz => sz
  end.

(** Layout well-formedness: fields and variant data lie within the type's size,
    and the fields of a tuple do not overlap. *)
Definition fields_disjoint (fs : list (nat * mty)) : Prop :=
  ∀ i j o1 m1 o2 m2, i ≠ j → fs !! i = Some (o1, m1) → fs !! j = Some (o2, m2) →
    (o1 + mty_size m1 ≤ o2 ∨ o2 + mty_size m2 ≤ o1)%nat.

Inductive mty_wf : mty → Prop :=
| MInt_wf it : mty_wf (MInt it)
| MBool_wf : mty_wf MBool
| MPtr_wf : mty_wf MPtr
| MTuple_wf fs sz :
    fields_disjoint fs →
    Forall (λ f, f.1 + mty_size f.2 ≤ sz)%nat fs →
    Forall (λ f, mty_wf f.2) fs →
    mty_wf (MTuple fs sz)
| MEnum_wf vars tag sz :
    Forall (λ vm, int_size tag + mty_size vm ≤ sz ∧ mty_wf vm)%nat vars →
    (int_size tag ≤ sz)%nat →
    mty_wf (MEnum vars tag sz).

Lemma fields_disjoint_cons f fs :
  fields_disjoint (f :: fs) ↔
    Forall (λ f', f.1 + mty_size f.2 ≤ f'.1 ∨ f'.1 + mty_size f'.2 ≤ f.1)%nat fs ∧
    fields_disjoint fs.
Proof.
  destruct f as [o m]. split.
  - intros H. split.
    + apply Forall_lookup=> k [o' m'] Hk. by apply (H 0%nat (S k) o m o' m').
    + intros i j ???? Hij Hi Hj. by apply (H (S i) (S j)); [lia| |].
  - intros [Hf Hfs] [|i] [|j] o1 m1 o2 m2 Hij Hi Hj; simplify_eq/=.
    + by apply (Forall_lookup_1 _ _ _ _ Hf Hj).
    + apply (Forall_lookup_1 _ _ _ _ Hf) in Hi. simpl in Hi. lia.
    + by apply (Hfs i j); [lia| |].
Qed.

Global Instance fields_disjoint_dec fs : Decision (fields_disjoint fs).
Proof.
  induction fs as [|f fs IH].
  - left. intros i ?????? Hi. by rewrite lookup_nil in Hi.
  - refine (cast_if (decide (Forall (λ f', f.1 + mty_size f.2 ≤ f'.1 ∨
      f'.1 + mty_size f'.2 ≤ f.1)%nat fs ∧ fields_disjoint fs)));
      by rewrite fields_disjoint_cons.
Defined.

(** Well-formedness of MiniRust types is decidable ([mty_wfb_correct]). *)
Fixpoint mty_wfb (m : mty) : bool :=
  match m with
  | MInt _ | MBool | MPtr => true
  | MTuple fs sz =>
      bool_decide (fields_disjoint fs) &&
      bool_decide (Forall (λ f, f.1 + mty_size f.2 ≤ sz)%nat fs) &&
      (fix go fs := match fs with [] => true | (_, f) :: fs => mty_wfb f && go fs end) fs
  | MEnum vars tag sz =>
      bool_decide (int_size tag ≤ sz)%nat &&
      (fix go vars := match vars with [] => true | vm :: vars =>
        bool_decide (int_size tag + mty_size vm ≤ sz)%nat && mty_wfb vm && go vars end) vars
  end.

Lemma mty_wfb_correct m : mty_wfb m ↔ mty_wf m.
Proof.
  induction m as [| | |fs sz IH|vars tag sz IH] using mty_ind'; simpl.
  - split; [constructor|done].
  - split; [constructor|done].
  - split; [constructor|done].
  - rewrite !andb_True !bool_decide_spec.
    cut ((fix go (fs : list (nat * mty)) := match fs with [] => true
      | (_, f) :: fs => mty_wfb f && go fs end) fs ↔ Forall (λ f, mty_wf f.2) fs).
    { intros ->. split; [intros [[??]?]; by constructor|by inversion 1]. }
    induction IH as [|[o f] fs Hf _ IH']; simpl; [split; [constructor|done]|].
    rewrite andb_True Hf IH' Forall_cons. done.
  - rewrite !andb_True !bool_decide_spec.
    cut ((fix go (vars : list mty) := match vars with [] => true | vm :: vars =>
        bool_decide (int_size tag + mty_size vm ≤ sz)%nat && mty_wfb vm && go vars end) vars ↔
      Forall (λ vm, int_size tag + mty_size vm ≤ sz ∧ mty_wf vm)%nat vars).
    { intros ->. split; [intros [??]; by constructor|by inversion 1]. }
    induction IH as [|vm vars Hv _ IH']; simpl; [split; [constructor|done]|].
    rewrite !andb_True bool_decide_spec Hv IH' Forall_cons. naive_solver.
Qed.

Global Instance mty_wf_dec m : Decision (mty_wf m).
Proof. refine (cast_if (decide (mty_wfb m))); by rewrite -mty_wfb_correct. Defined.

(** ** Well-formed MiniRust types

[wf_mty] packs a MiniRust type with a proof that it is well formed, as a boolean equality
[mty_wfb m = true]. Two proofs of an equality of booleans are equal without axioms
([eq_pi]), so [wf_mty] has decidable equality, and two [wf_mty]s are equal when their types
are ([wf_mty_eq]). The type of the contents of a cell ([pcellₛ] in [prophecy/syn_type.v]) is
a [wf_mty].

The proofs are kept canonical ([wfb_canon]): a proof built from any proof [H] of
[b = true] computes to [eq_refl] as soon as [b] computes to [true]. So for a concrete [m],
every [wf_mty] built on [m] (with [wfm], [mk_wf_mty] or [mty_to_wf]) is _convertible_ to
[wfm m], and cell types built by the typing rules match the ones written in examples. *)
Definition wf_mty : Type := { m : mty | mty_wfb m = true }.

Definition wfb_canon {b : bool} : b = true → b = true :=
  match b with true => λ _, eq_refl | false => λ H, H end.

Definition mk_wf_mty (m : mty) (H : mty_wfb m = true) : wf_mty := m ↾ wfb_canon H.

(** A [wf_mty] from a proof of [mty_wf m]. *)
Definition mty_to_wf (m : mty) (H : mty_wf m) : wf_mty :=
  mk_wf_mty m (Is_true_true_1 _ (proj2 (mty_wfb_correct m) H)).

(** The [wf_mty] of a concrete MiniRust type: [wfm (MInt i32)] checks [mty_wfb (MInt i32)]
    by computation. *)
Notation wfm m := (exist (λ m', mty_wfb m' = true) m eq_refl).

Global Instance wf_mty_eq_dec : EqDecision wf_mty.
Proof. apply _. Defined.

Lemma wf_mty_wf (m : wf_mty) : mty_wf (`m).
Proof. apply mty_wfb_correct, Is_true_true_2, (proj2_sig m). Qed.

Lemma wf_mty_eq (m m' : wf_mty) : `m = `m' → m = m'.
Proof. apply sig_eq_pi, _. Qed.

(** Well-formed values of a MiniRust type (MiniRust's [check_wf]). *)
Inductive val_wf : mty → Value → Prop :=
| VInt_wf it z : int_in_range it z → val_wf (MInt it) (VInt z)
| VBool_wf b : val_wf MBool (VBool b)
| VPtr_wf l : val_wf MPtr (VPtr l)
| VTuple_wf fs sz vs :
    Forall2 (λ f v, val_wf f.2 v) fs vs → val_wf (MTuple fs sz) (VTuple vs)
| VVariant_wf vars tag sz t vm d :
    0 ≤ t → vars !! Z.to_nat t = Some vm → int_in_range tag t → val_wf vm d →
    val_wf (MEnum vars tag sz) (VVariant t d).

(** ** Abstract bytes *)
Inductive AbstractByte :=
| Uninit
| Init (b : Z)  (* a byte, in [0, 256) *)
| PtrFrag (l : loc) (i : nat).  (* the [i]-th byte of the pointer [l] *)

Global Instance AbstractByte_eq_dec : EqDecision AbstractByte.
Proof. solve_decision. Defined.
Global Instance AbstractByte_inhabited : Inhabited AbstractByte := populate Uninit.

(** The "less defined" order on bytes: [Uninit] is below everything. *)
Definition byte_le (b1 b2 : AbstractByte) : Prop := b1 = Uninit ∨ b1 = b2.
Definition bytes_le : list (AbstractByte) → list (AbstractByte) → Prop :=
  Forall2 byte_le.

(** The slice of [len] elements starting at [off]. *)
Definition list_slice {A} (off len : nat) (l : list A) : list A := take len (drop off l).

Section repr.
  Implicit Types bs : list (AbstractByte).

  (** *** Integers *)
  Fixpoint le_digits (n : nat) (u : Z) : list Z :=
    match n with O => [] | S n => u `mod` 256 :: le_digits n (u `div` 256) end.
  Fixpoint le_value (ds : list Z) : Z :=
    match ds with [] => 0 | d :: ds => d + 256 * le_value ds end.

  Definition byte_of (b : AbstractByte) : option Z :=
    match b with Init z => if bool_decide (0 ≤ z < 256) then Some z else None | _ => None end.

  Definition encode_int (it : IntType) (z : Z) : list (AbstractByte) :=
    Init <$> le_digits (int_size it) (z `mod` int_modulus it).

  Definition decode_int (it : IntType) bs : option Z :=
    if decide (length bs = int_size it) then
      ds ← mapM byte_of bs;
      let u := le_value ds in
      let z := if int_signed it && bool_decide (int_modulus it / 2 ≤ u)
               then u - int_modulus it else u in
      if decide (int_in_range it z) then Some z else None
    else None.

  (** *** Booleans *)
  Definition encode_bool (b : bool) : list (AbstractByte) := [Init (if b then 1 else 0)].
  Definition decode_bool bs : option bool :=
    match bs with
    | [b] => z ← byte_of b;
             if bool_decide (z = 0) then Some false
             else if bool_decide (z = 1) then Some true else None
    | _ => None
    end.

  (** *** Pointers *)
  Definition encode_ptr (l : loc) : list (AbstractByte) := PtrFrag l <$> seq 0 PTR_SIZE.

  Fixpoint ptr_frags_ok (l : loc) (i : nat) bs : bool :=
    match bs with
    | [] => true
    | PtrFrag l' j :: bs => bool_decide (l' = l ∧ j = i) && ptr_frags_ok l (S i) bs
    | _ :: _ => false
    end.

  Definition decode_ptr bs : option loc :=
    match bs with
    | PtrFrag l _ :: _ =>
        if bool_decide (length bs = PTR_SIZE) && ptr_frags_ok l 0 bs then Some l else None
    | _ => None
    end.

  (** *** Encoding and decoding *)

  (** Write the field encodings [ins] (offset, bytes) over [base]. *)
  Definition fill_fields (ins : list (nat * list (AbstractByte))) base :=
    foldr (λ p acc, list_inserts p.1 p.2 acc) base ins.

  Fixpoint encode_value (m : mty) (v : Value) : list (AbstractByte) :=
    match m, v with
    | MInt it, VInt z => encode_int it z
    | MBool, VBool b => encode_bool b
    | MPtr, VPtr l => encode_ptr l
    | MTuple fs sz, VTuple vs =>
        (fix go fs vs := match fs, vs with
          | (off, fm) :: fs, fv :: vs => list_inserts off (encode_value fm fv) (go fs vs)
          | _, _ => replicate sz Uninit end) fs vs
    | MEnum vars tag sz, VVariant t d =>
        (fix pick vars n := match vars, n with
          | [], _ => replicate sz Uninit
          | vm :: _, O =>
              list_inserts 0 (encode_int tag t)
                (list_inserts (int_size tag) (encode_value vm d) (replicate sz Uninit))
          | _ :: vars, S n => pick vars n end) vars (Z.to_nat t)
    | _, _ => replicate (mty_size m) Uninit
    end.

  Fixpoint decode_value (m : mty) bs : option Value :=
    match m with
    | MInt it => VInt <$> decode_int it bs
    | MBool => VBool <$> decode_bool bs
    | MPtr => VPtr <$> decode_ptr bs
    | MTuple fs sz =>
        if decide (length bs = sz) then
          VTuple <$> (fix go fs := match fs with
            | [] => Some []
            | (off, fm) :: fs =>
                v ← decode_value fm (list_slice off (mty_size fm) bs);
                vs ← go fs; Some (v :: vs) end) fs
        else None
    | MEnum vars tag sz =>
        if decide (length bs = sz) then
          t ← decode_int tag (take (int_size tag) bs);
          if decide (0 ≤ t) then
            (fix pick vars n := match vars, n with
              | [], _ => None
              | vm :: _, O =>
                  VVariant t <$> decode_value vm (list_slice (int_size tag) (mty_size vm) bs)
              | _ :: vars, S n => pick vars n end) vars (Z.to_nat t)
          else None
        else None
    end.

  (** *** Unfolding lemmas *)
  Lemma encode_value_tuple fs sz vs :
    encode_value (MTuple fs sz) (VTuple vs) =
    fill_fields (zip_with (λ f v, (f.1, encode_value f.2 v)) fs vs) (replicate sz Uninit).
  Proof.
    simpl. revert vs. induction fs as [|[o f] fs IH]; intros [|v vs]; simpl; try done.
    by rewrite IH.
  Qed.

  Lemma encode_value_enum vars tag sz t d :
    encode_value (MEnum vars tag sz) (VVariant t d) =
    match vars !! Z.to_nat t with
    | Some vm => list_inserts 0 (encode_int tag t)
                   (list_inserts (int_size tag) (encode_value vm d) (replicate sz Uninit))
    | None => replicate sz Uninit
    end.
  Proof.
    simpl. generalize (Z.to_nat t). induction vars as [|vm vars IH]; intros [|n]; simpl; auto.
  Qed.

  Lemma decode_value_tuple fs sz bs :
    decode_value (MTuple fs sz) bs =
    if decide (length bs = sz) then
      VTuple <$> mapM (λ f, decode_value f.2 (list_slice f.1 (mty_size f.2) bs)) fs
    else None.
  Proof.
    simpl. case_decide; [|done]. f_equal.
    induction fs as [|[o f] fs IH]; simpl; [done|]. by rewrite IH.
  Qed.

  Lemma decode_value_enum vars tag sz bs :
    decode_value (MEnum vars tag sz) bs =
    if decide (length bs = sz) then
      t ← decode_int tag (take (int_size tag) bs);
      if decide (0 ≤ t) then
        vm ← vars !! Z.to_nat t;
        VVariant t <$> decode_value vm (list_slice (int_size tag) (mty_size vm) bs)
      else None
    else None.
  Proof.
    simpl. case_decide; [|done]. destruct (decode_int _ _) as [t|]; simpl; [|done].
    case_decide; [|done]. generalize (Z.to_nat t).
    induction vars as [|vm vars IH]; intros [|n]; simpl; auto.
  Qed.

  (** *** The length law *)
  Lemma length_fill_fields ins base : length (fill_fields ins base) = length base.
  Proof. induction ins as [|[o e] ins IH]; simpl; [done|]. by rewrite length_inserts. Qed.

  Lemma length_encode_int it z : length (encode_int it z) = int_size it.
  Proof.
    rewrite /encode_int length_fmap. generalize (z `mod` int_modulus it).
    induction (int_size it); simpl; auto.
  Qed.

  Lemma length_encode_ptr l : length (encode_ptr l) = PTR_SIZE.
  Proof. by rewrite /encode_ptr length_fmap length_seq. Qed.

  Lemma length_encode_value m v : length (encode_value m v) = mty_size m.
  Proof.
    destruct m as [it| | |fs sz|vars tag sz], v as [z|b|l|vs|t d];
      rewrite ?encode_value_tuple ?encode_value_enum /=;
      rewrite ?length_replicate ?length_encode_int ?length_encode_ptr ?length_fill_fields
        ?length_replicate //.
    destruct (vars !! _); by rewrite ?length_inserts length_replicate.
  Qed.

  (** *** Integer round trip *)
  Lemma le_digits_range n u : Forall (λ d, 0 ≤ d < 256) (le_digits n u).
  Proof.
    revert u. induction n as [|n IH]; intros u; simpl; constructor; [|done].
    apply Z.mod_pos_bound. lia.
  Qed.

  Lemma le_value_digits n u : 0 ≤ u < 256 ^ Z.of_nat n → le_value (le_digits n u) = u.
  Proof.
    revert u. induction n as [|n IH]; intros u Hu; simpl.
    - rewrite Z.pow_0_r in Hu. lia.
    - rewrite Nat2Z.inj_succ Z.pow_succ_r in Hu; [|lia].
      rewrite IH.
      + have := Z.div_mod u 256. lia.
      + split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; lia.
  Qed.

  Lemma mapM_byte_of_Init ds :
    Forall (λ d, 0 ≤ d < 256) ds → mapM byte_of (Init <$> ds) = Some ds.
  Proof.
    induction 1 as [|d ds Hd _ IH]; simpl; [done|].
    rewrite bool_decide_true //. by rewrite IH.
  Qed.

  Lemma decode_encode_int it z : int_in_range it z → decode_int it (encode_int it z) = Some z.
  Proof.
    intros Hz. rewrite /decode_int length_encode_int decide_True //.
    rewrite /encode_int mapM_byte_of_Init; [|apply le_digits_range]. simpl.
    have HM := int_modulus_pos it.
    have Hu := Z.mod_pos_bound z (int_modulus it) HM.
    rewrite le_value_digits; [|done].
    assert ((if int_signed it && bool_decide (int_modulus it / 2 ≤ z `mod` int_modulus it)
             then z `mod` int_modulus it - int_modulus it else z `mod` int_modulus it) = z) as ->;
      [|by rewrite /= decide_True].
    have Hdiv := Z.div_mod (int_modulus it) 2.
    have Hmod2 := Z.mod_pos_bound (int_modulus it) 2.
    rewrite /int_in_range in Hz. destruct (int_signed it); simpl.
    - destruct (decide (0 ≤ z)).
      + rewrite Z.mod_small; [|lia]. rewrite bool_decide_false //; lia.
      + rewrite -(Z_mod_plus_full z 1) Z.mod_small; [|lia].
        rewrite bool_decide_true; lia.
    - rewrite Z.mod_small //.
  Qed.

  (** *** Pointer round trip *)
  Lemma ptr_frags_ok_seq l i n : ptr_frags_ok l i (PtrFrag l <$> seq i n) = true.
  Proof.
    revert i. induction n as [|n IH]; intros i; simpl; [done|].
    rewrite bool_decide_true //. apply IH.
  Qed.

  Lemma decode_encode_ptr l : decode_ptr (encode_ptr l) = Some l.
  Proof.
    rewrite /decode_ptr. have := ptr_frags_ok_seq l 0 PTR_SIZE.
    rewrite /encode_ptr. have := PTR_SIZE_pos. destruct PTR_SIZE as [|n]; [lia|].
    simpl. intros _ ->. rewrite length_fmap length_seq bool_decide_true //.
  Qed.

  (** *** Fields *)
  Lemma lookup_fill_fields_out ins base j :
    (∀ k o e, ins !! k = Some (o, e) → (j < o ∨ o + length e ≤ j)%nat) →
    fill_fields ins base !! j = base !! j.
  Proof.
    induction ins as [|[o e] ins IH]; intros Hout; simpl; [done|].
    destruct (Hout 0%nat o e) as [Hj|Hj]; [done| |];
      [rewrite list_lookup_inserts_lt //|rewrite list_lookup_inserts_ge //];
      apply IH; intros k; apply (Hout (S k)).
  Qed.

  Lemma lookup_fill_fields_in ins base k o e j :
    ins !! k = Some (o, e) →
    (∀ k' o' e', k' ≠ k → ins !! k' = Some (o', e') →
       (o' + length e' ≤ o ∨ o + length e ≤ o')%nat) →
    (o ≤ j < o + length e)%nat → (j < length base)%nat →
    fill_fields ins base !! j = e !! (j - o)%nat.
  Proof.
    revert k. induction ins as [|[o0 e0] ins IH]; intros k Hk Hdisj Hj Hlen; [done|].
    simpl. destruct k as [|k].
    - simpl in Hk. simplify_eq. rewrite list_lookup_inserts //.
      rewrite length_fill_fields //.
    - simpl in Hk. destruct (Hdisj 0%nat o0 e0) as [Hd|Hd]; [done|done| |].
      + rewrite list_lookup_inserts_ge; [|lia].
        apply (IH k); [done| |done|done]. intros k' ???. apply (Hdisj (S k')). congruence.
      + rewrite list_lookup_inserts_lt; [|lia].
        apply (IH k); [done| |done|done]. intros k' ???. apply (Hdisj (S k')). congruence.
  Qed.

  Lemma list_slice_eq (l e : list (AbstractByte)) o :
    (o + length e ≤ length l)%nat →
    (∀ j, (o ≤ j < o + length e)%nat → l !! j = e !! (j - o)%nat) →
    list_slice o (length e) l = e.
  Proof.
    intros Hlen Hj. apply list_eq. intros i. rewrite /list_slice.
    destruct (decide (i < length e)%nat).
    - rewrite lookup_take // lookup_drop Hj; [|lia]. f_equal. lia.
    - rewrite lookup_take_ge; [|lia]. rewrite lookup_ge_None_2 //. lia.
  Qed.

  Lemma list_slice_fill_fields ins base k o e :
    ins !! k = Some (o, e) →
    (∀ k' o' e', k' ≠ k → ins !! k' = Some (o', e') →
       (o' + length e' ≤ o ∨ o + length e ≤ o')%nat) →
    (o + length e ≤ length base)%nat →
    list_slice o (length e) (fill_fields ins base) = e.
  Proof.
    intros Hk Hdisj Hlen. apply list_slice_eq; [by rewrite length_fill_fields|].
    intros j Hj. eapply lookup_fill_fields_in; [done..|lia].
  Qed.

  Lemma list_slice_inserts (l e : list (AbstractByte)) o :
    (o + length e ≤ length l)%nat → list_slice o (length e) (list_inserts o e l) = e.
  Proof.
    intros Hlen. apply list_slice_eq; [by rewrite length_inserts|].
    intros j Hj. apply list_lookup_inserts; lia.
  Qed.

  Lemma list_slice_inserts_disjoint (l e : list (AbstractByte)) o o' len :
    (o' + length e ≤ o)%nat → list_slice o len (list_inserts o' e l) = list_slice o len l.
  Proof.
    intros Ho. apply list_eq. intros i. rewrite /list_slice.
    destruct (decide (i < len)%nat).
    - rewrite !lookup_take // !lookup_drop list_lookup_inserts_ge //. lia.
    - rewrite !lookup_take_ge //; lia.
  Qed.

  Lemma take_inserts_0 (l e : list (AbstractByte)) :
    (length e ≤ length l)%nat → take (length e) (list_inserts 0 e l) = e.
  Proof. intros. have := list_slice_inserts l e 0. rewrite /list_slice drop_0. auto. Qed.

  (** *** The round-trip law *)
  Theorem decode_encode_value m v : mty_wf m → val_wf m v → decode_value m (encode_value m v) = Some v.
  Proof.
    revert v. induction m as [it| | |fs sz IH|vars tag sz IH] using mty_ind';
      intros v Hm Hv; inversion Hv as [? z Hz|b|l|? ? vs Hvs|? ? ? t vm d Ht Hvm Htr Hd];
      simplify_eq.
    - by rewrite /= decode_encode_int.
    - by destruct b.
    - by rewrite /= decode_encode_ptr.
    - inversion Hm as [| | |? ? Hdisj Hin Hwf|]; simplify_eq.
      rewrite -/(encode_value (MTuple fs sz) (VTuple vs)) decode_value_tuple encode_value_tuple.
      rewrite length_fill_fields length_replicate decide_True //. apply fmap_Some_2.
      apply mapM_Some, Forall2_lookup. intros k.
      have Hlen := Forall2_length _ _ _ Hvs.
      rewrite Forall2_lookup in Hvs. specialize (Hvs k).
      destruct (fs !! k) as [[o f]|] eqn:Hfk, (vs !! k) as [v|] eqn:Hvk;
        inversion Hvs as [? ? Hvf|]; simplify_eq; constructor. simpl.
      rewrite -(length_encode_value f v) (list_slice_fill_fields _ _ k).
      + apply (Forall_lookup_1 _ _ _ _ IH Hfk); [|done].
        apply (Forall_lookup_1 _ _ _ _ Hwf Hfk).
      + by rewrite lookup_zip_with Hfk Hvk.
      + intros k' o' e' Hk' He'. rewrite lookup_zip_with_Some in He'.
        destruct He' as ([o'' f']&v'&[= -> ->]&Hfk'&Hvk'). simpl.
        rewrite !length_encode_value. by apply (Hdisj k' k o'' f' o f).
      + rewrite length_encode_value length_replicate.
        apply (Forall_lookup_1 _ _ _ _ Hin Hfk).
    - inversion Hm as [| | | |? ? ? Hvars Htag]; simplify_eq.
      rewrite -/(encode_value (MEnum vars tag sz) (VVariant t d)) decode_value_enum encode_value_enum Hvm.
      destruct (Forall_lookup_1 _ _ _ _ Hvars Hvm) as [Hsz Hwf].
      rewrite !length_inserts length_replicate decide_True //.
      rewrite (_ : take (int_size tag) (list_inserts 0 (encode_int tag t) _) = encode_int tag t);
        last first.
      { rewrite -{1}(length_encode_int tag t) take_inserts_0 //.
        by rewrite length_inserts length_replicate length_encode_int. }
      rewrite decode_encode_int //=. rewrite decide_True //= Hvm /=.
      rewrite list_slice_inserts_disjoint; [|by rewrite length_encode_int].
      rewrite -(length_encode_value vm d) list_slice_inserts;
        last by rewrite length_replicate length_encode_value.
      rewrite (Forall_lookup_1 _ _ _ _ IH Hvm) //.
  Qed.

  (** *** Decoding determines the length *)
  Lemma decode_value_length m bs v : decode_value m bs = Some v → length bs = mty_size m.
  Proof.
    destruct m as [it| | |fs sz|vars tag sz]; simpl; intros Hd.
    - rewrite /decode_int in Hd. case_decide; [done|]. by simplify_eq/=.
    - destruct bs as [|? [|]]; by simplify_eq/=.
    - rewrite /decode_ptr in Hd. destruct bs as [|[] bs]; simplify_eq/=.
      case_bool_decide; by simplify_eq/=.
    - case_decide; [done|]. by simplify_eq/=.
    - by case_decide.
  Qed.

  (** *** Monotonicity *)
  Lemma bytes_le_defined bs1 bs2 :
    Forall (λ b, b ≠ Uninit) bs1 → bytes_le bs1 bs2 → bs2 = bs1.
  Proof.
    intros Hdef Hle. induction Hle as [|b1 b2 bs1 bs2 [->| ->] _ IH]; [done| |].
    - by inversion Hdef.
    - inversion Hdef. f_equal. by apply IH.
  Qed.

  Lemma mapM_byte_of_defined bs ds : mapM byte_of bs = Some ds → Forall (λ b, b ≠ Uninit) bs.
  Proof.
    intros Hds%mapM_Some. induction Hds as [|b d bs ds Hb _ IH]; constructor; [|done].
    by destruct b.
  Qed.

  Lemma decode_int_defined it bs z : decode_int it bs = Some z → Forall (λ b, b ≠ Uninit) bs.
  Proof.
    rewrite /decode_int. case_decide; [|done].
    destruct (mapM byte_of bs) eqn:Hds; [|done]. intros _. by eapply mapM_byte_of_defined.
  Qed.

  Lemma ptr_frags_ok_defined l i bs : ptr_frags_ok l i bs → Forall (λ b, b ≠ Uninit) bs.
  Proof.
    revert i. induction bs as [|b bs IH]; intros i; simpl; [done|].
    destruct b; try done. rewrite andb_True. intros [_ ?]. constructor; [done|]. by eapply IH.
  Qed.

  Lemma decode_defined_leaf m bs v :
    (match m with MInt _ | MBool | MPtr => True | _ => False end) →
    decode_value m bs = Some v → Forall (λ b, b ≠ Uninit) bs.
  Proof.
    destruct m as [it| | | |]; simpl; try done; intros _ (w&Hw&_)%fmap_Some_1.
    - by eapply decode_int_defined.
    - destruct bs as [|b [|]]; try done. constructor; [|done]. by destruct b.
    - rewrite /decode_ptr in Hw. destruct bs as [|[] bs]; try done.
      destruct (ptr_frags_ok l 0 _) eqn:Hok; [|by rewrite andb_false_r in Hw].
      apply (ptr_frags_ok_defined l 0). by rewrite Hok.
  Qed.

  Theorem decode_value_mono m bs1 bs2 v :
    bytes_le bs1 bs2 → decode_value m bs1 = Some v → decode_value m bs2 = Some v.
  Proof.
    revert bs1 bs2 v. induction m as [it| | |fs sz IH|vars tag sz IH] using mty_ind';
      intros bs1 bs2 v Hle Hdec.
    1-3: rewrite (bytes_le_defined bs1 bs2) //; [eapply (decode_defined_leaf _ _ v)]; [|exact Hdec]; done.
    - rewrite decode_value_tuple in Hdec. rewrite decode_value_tuple. have Hlen := Forall2_length _ _ _ Hle.
      destruct (decide (length bs1 = sz)); [|done]. rewrite decide_True; [|lia].
      apply fmap_Some_1 in Hdec as (vs&Hvs&->). apply fmap_Some_2.
      revert vs Hvs. induction IH as [|[o f] fs Hf _ IHfs]; intros vs Hvs; [done|].
      simpl in *. destruct (decode_value f _) as [w|] eqn:Hw; [|done]. simpl in Hvs.
      destruct (mapM _ fs) as [ws|] eqn:Hws; [|done]. simpl in Hvs. simplify_eq.
      rewrite (Hf (list_slice o (mty_size f) bs1) _ w) //=.
      + by rewrite (IHfs ws).
      + by apply Forall2_take, Forall2_drop.
    - rewrite decode_value_enum in Hdec. rewrite decode_value_enum. have Hlen := Forall2_length _ _ _ Hle.
      destruct (decide (length bs1 = sz)); [|done]. rewrite decide_True; [|lia].
      destruct (decode_int tag (take _ bs1)) as [t|] eqn:Ht; [|done]. simpl in Hdec.
      rewrite (bytes_le_defined (take (int_size tag) bs1) (take (int_size tag) bs2));
        [|by eapply decode_int_defined|by apply Forall2_take].
      rewrite Ht /=. case_decide; [|done].
      destruct (vars !! Z.to_nat t) as [vm|] eqn:Hvm; [|done]. simpl in *.
      apply fmap_Some_1 in Hdec as (d&Hd&->). apply fmap_Some_2.
      eapply (Forall_lookup_1 _ _ _ _ IH Hvm); [|done].
      by apply Forall2_take, Forall2_drop.
  Qed.

  (** Hence decoding any refinement of an encoding gives back the value. *)
  Corollary decode_encode_value_le m v bs :
    mty_wf m → val_wf m v → bytes_le (encode_value m v) bs → decode_value m bs = Some v.
  Proof. intros. eapply decode_value_mono; [done|]. by apply decode_encode_value. Qed.

  (** *** Decoded values are well-formed *)
  Lemma decode_int_in_range it bs z : decode_int it bs = Some z → int_in_range it z.
  Proof.
    rewrite /decode_int. case_decide; [|done]. destruct (mapM byte_of bs); simpl; [|done].
    case_decide; [|done]. by intros [= <-].
  Qed.

  Theorem decode_value_wf m bs v : mty_wf m → decode_value m bs = Some v → val_wf m v.
  Proof.
    revert bs v. induction m as [it| | |fs sz IH|vars tag sz IH] using mty_ind';
      intros bs v Hm Hd.
    - apply fmap_Some_1 in Hd as (z & Hz & ->). constructor. by eapply decode_int_in_range.
    - apply fmap_Some_1 in Hd as (b & _ & ->). constructor.
    - apply fmap_Some_1 in Hd as (l & _ & ->). constructor.
    - inversion Hm as [| | |? ? _ _ Hwf|]; simplify_eq.
      rewrite decode_value_tuple in Hd. case_decide; [|done].
      apply fmap_Some_1 in Hd as (vs & Hvs & ->). apply mapM_Some in Hvs.
      have Hlen := Forall2_length _ _ _ Hvs.
      constructor. apply Forall2_lookup. intros k.
      destruct (fs !! k) as [f|] eqn:Hf, (vs !! k) as [w|] eqn:Hw; try constructor.
      + eapply (Forall_lookup_1 _ _ _ _ IH Hf); [exact (Forall_lookup_1 _ _ _ _ Hwf Hf)|].
        exact (Forall2_lookup_lr _ _ _ _ _ _ Hvs Hf Hw).
      + exfalso. apply lookup_ge_None in Hw. apply lookup_lt_Some in Hf. lia.
      + exfalso. apply lookup_ge_None in Hf. apply lookup_lt_Some in Hw. lia.
    - inversion Hm as [| | | |? ? ? Hvars Htag]; simplify_eq.
      rewrite decode_value_enum in Hd. case_decide; [|done].
      destruct (decode_int tag (take (int_size tag) bs)) as [t|] eqn:Ht; simpl in Hd; [|done].
      case_decide as Ht0; [|done].
      destruct (vars !! Z.to_nat t) as [vm|] eqn:Hvm; simpl in Hd; [|done].
      apply fmap_Some_1 in Hd as (d & Hd & ->).
      destruct (Forall_lookup_1 _ _ _ _ Hvars Hvm) as [_ Hwfvm].
      econstructor; [done|done|by eapply decode_int_in_range|].
      by eapply (Forall_lookup_1 _ _ _ _ IH Hvm).
  Qed.
End repr.
