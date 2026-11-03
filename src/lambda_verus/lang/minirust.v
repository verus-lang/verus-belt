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
- A variant of an enum is its payload type at an offset, with a tagger (MiniRust's
  [Variant { ty, tagger }], with [ty] the one-field tuple of the payload). The discriminator
  is a decision tree ([discr]) that reads integers only (pointer bytes are UB), and is
  _tag-only_: it never reads a payload byte (no niches yet, see [discr_tag_only]).
- Alignments are part of the layouts ([mty_align]); they are not checked yet.
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

(** The alignment of a pointer. It is sealed too; only [PTR_ALIGN_pos] and
    [PTR_ALIGN_divide] are known. *)
Local Definition PTR_ALIGN_def : nat := 8.
Local Definition PTR_ALIGN_aux : seal (@PTR_ALIGN_def). Proof. by eexists. Qed.
Definition PTR_ALIGN : nat := PTR_ALIGN_aux.(unseal).
Local Definition PTR_ALIGN_unseal : PTR_ALIGN = PTR_ALIGN_def := PTR_ALIGN_aux.(seal_eq).

Lemma PTR_ALIGN_pos : (0 < PTR_ALIGN)%nat.
Proof. rewrite PTR_ALIGN_unseal /PTR_ALIGN_def. lia. Qed.

Lemma PTR_ALIGN_divide : Nat.divide PTR_ALIGN PTR_SIZE.
Proof. rewrite PTR_ALIGN_unseal PTR_SIZE_unseal /PTR_ALIGN_def /PTR_SIZE_def. by exists 1%nat. Qed.

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

(** The alignment of an integer type: its size (at least 1). *)
Definition int_align (it : IntType) : nat := Nat.max 1 (int_size it).

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

(** A discriminator (MiniRust's [Discriminator]): a decision tree that computes the
    discriminant of an enum from its bytes. [DBranch off it fallback children] reads an
    integer of type [it] at offset [off], and goes to the first child whose range [[lo, hi)]
    contains it, or else to [fallback]. *)
Inductive discr : Set :=
| DKnown (t : Z)
| DInvalid
| DBranch (off : nat) (it : IntType) (fallback : discr) (children : list ((Z * Z) * discr)).

Lemma discr_ind' (P : discr → Prop) :
  (∀ t, P (DKnown t)) → P DInvalid →
  (∀ off it fb ch, P fb → Forall (λ c, P c.2) ch → P (DBranch off it fb ch)) →
  ∀ d, P d.
Proof.
  intros Hk Hi Hb.
  refine (fix FIX d := match d with
    | DKnown t => Hk t | DInvalid => Hi
    | DBranch off it fb ch => Hb off it fb ch (FIX fb)
        ((fix go ch := match ch return Forall (λ c, P c.2) ch with
          | [] => @List.Forall_nil _ _
          | (r, c) :: ch => @List.Forall_cons _ (λ c, P c.2) (r, c) ch (FIX c) (go ch) end) ch)
    end).
Qed.

Fixpoint discr_beq (d1 d2 : discr) : bool :=
  match d1, d2 with
  | DKnown t1, DKnown t2 => bool_decide (t1 = t2)
  | DInvalid, DInvalid => true
  | DBranch o1 it1 fb1 ch1, DBranch o2 it2 fb2 ch2 =>
      bool_decide (o1 = o2) && bool_decide (it1 = it2) && discr_beq fb1 fb2 &&
      (fix go ch1 ch2 := match ch1, ch2 with
        | [], [] => true
        | (r1, c1) :: ch1, (r2, c2) :: ch2 => bool_decide (r1 = r2) && discr_beq c1 c2 && go ch1 ch2
        | _, _ => false end) ch1 ch2
  | _, _ => false
  end.

Lemma discr_beq_correct d1 d2 : discr_beq d1 d2 ↔ d1 = d2.
Proof.
  revert d2. induction d1 as [t1| |o1 it1 fb1 ch1 IHfb IH] using discr_ind';
    intros [t2| |o2 it2 fb2 ch2]; simpl; rewrite ?andb_True ?bool_decide_spec; try naive_solver.
  cut ((fix go (ch1 ch2 : list ((Z * Z) * discr)) := match ch1, ch2 with
        | [], [] => true
        | (r1, c1) :: ch1, (r2, c2) :: ch2 => bool_decide (r1 = r2) && discr_beq c1 c2 && go ch1 ch2
        | _, _ => false end) ch1 ch2 ↔ ch1 = ch2).
  { rewrite IHfb. naive_solver. }
  revert ch2. induction IH as [|[r1 c1] ch1 Hc _ IH]; intros [|[r2 c2] ch2]; simpl;
    rewrite ?andb_True ?bool_decide_spec ?Hc ?IH; naive_solver.
Qed.

Global Instance discr_eq_dec : EqDecision discr.
Proof.
  refine (λ d1 d2, cast_if (decide (discr_beq d1 d2))); by rewrite -discr_beq_correct.
Defined.

(** The integers that a tagger writes to mark a variant (MiniRust's [Variant.tagger]):
    offset, type and value. *)
Definition tagger : Set := list (nat * IntType * Z).

(** A tuple lists its fields with their offsets, and has a size and an alignment; the bytes
    not covered by a field are padding. An enum lists its variants: the MiniRust type of the
    payload, the offset of the payload, and the tagger; its discriminator reads the
    discriminant. This is MiniRust's [Variant { ty, tagger }] with [ty] the one-field tuple
    of the payload at its offset. *)
Inductive mty : Set :=
| MInt (it : IntType)
| MBool
| MPtr
| MTuple (fields : list (nat * mty)) (size align : nat)
| MEnum (variants : list (mty * nat * tagger)) (d : discr) (size align : nat).

Lemma mty_ind' (P : mty → Prop) :
  (∀ it, P (MInt it)) → P MBool → P MPtr →
  (∀ fs sz al, Forall (λ f, P f.2) fs → P (MTuple fs sz al)) →
  (∀ vars d sz al, Forall (λ v, P v.1.1) vars → P (MEnum vars d sz al)) →
  ∀ m, P m.
Proof.
  intros Hi Hb Hp Ht He.
  refine (fix FIX m := match m with
    | MInt it => Hi it | MBool => Hb | MPtr => Hp
    | MTuple fs sz al => Ht fs sz al ((fix go fs := match fs return Forall (λ f, P f.2) fs with
        | [] => @List.Forall_nil _ _
        | (o, fm) :: fs => @List.Forall_cons _ (λ f, P f.2) (o, fm) fs (FIX fm) (go fs) end) fs)
    | MEnum vars d sz al => He vars d sz al ((fix go vars := match vars return Forall (λ v, P v.1.1) vars with
        | [] => @List.Forall_nil _ _
        | (vm, o, tg) :: vars => @List.Forall_cons _ (λ v, P v.1.1) (vm, o, tg) vars (FIX vm) (go vars) end) vars)
    end).
Qed.

Fixpoint mty_beq (m1 m2 : mty) : bool :=
  match m1, m2 with
  | MInt it1, MInt it2 => bool_decide (it1 = it2)
  | MBool, MBool | MPtr, MPtr => true
  | MTuple fs1 sz1 al1, MTuple fs2 sz2 al2 =>
      bool_decide (sz1 = sz2) && bool_decide (al1 = al2) &&
      (fix go fs1 fs2 := match fs1, fs2 with
        | [], [] => true
        | (o1, f1) :: fs1, (o2, f2) :: fs2 =>
            bool_decide (o1 = o2) && mty_beq f1 f2 && go fs1 fs2
        | _, _ => false end) fs1 fs2
  | MEnum vs1 d1 sz1 al1, MEnum vs2 d2 sz2 al2 =>
      bool_decide (d1 = d2) && bool_decide (sz1 = sz2) && bool_decide (al1 = al2) &&
      (fix go vs1 vs2 := match vs1, vs2 with
        | [], [] => true
        | (v1, o1, tg1) :: vs1, (v2, o2, tg2) :: vs2 =>
            mty_beq v1 v2 && bool_decide (o1 = o2) && bool_decide (tg1 = tg2) && go vs1 vs2
        | _, _ => false end) vs1 vs2
  | _, _ => false
  end.

Lemma mty_beq_correct m1 m2 : mty_beq m1 m2 ↔ m1 = m2.
Proof.
  revert m2. induction m1 as [| | |fs1 sz1 al1 IH|vs1 d1 sz1 al1 IH] using mty_ind';
    intros [| | |fs2 sz2 al2|vs2 d2 sz2 al2]; simpl;
    rewrite ?andb_True ?bool_decide_spec; try naive_solver.
  - cut ((fix go (fs1 fs2 : list (nat * mty)) := match fs1, fs2 with
        | [], [] => true
        | (o1, f1) :: fs1, (o2, f2) :: fs2 =>
            bool_decide (o1 = o2) && mty_beq f1 f2 && go fs1 fs2
        | _, _ => false end) fs1 fs2 ↔ fs1 = fs2); [naive_solver|].
    revert fs2. induction IH as [|[o1 f1] fs1 Hf1 _ IH]; intros [|[o2 f2] fs2]; try naive_solver.
  - cut ((fix go (vs1 vs2 : list (mty * nat * tagger)) := match vs1, vs2 with
        | [], [] => true
        | (v1, o1, tg1) :: vs1, (v2, o2, tg2) :: vs2 =>
            mty_beq v1 v2 && bool_decide (o1 = o2) && bool_decide (tg1 = tg2) && go vs1 vs2
        | _, _ => false end) vs1 vs2 ↔ vs1 = vs2); [naive_solver|].
    revert vs2. induction IH as [|[[v1 o1] tg1] vs1 Hv1 _ IH]; intros [|[[v2 o2] tg2] vs2];
      simpl; rewrite ?andb_True ?bool_decide_spec; try naive_solver.
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
  | MTuple _ sz _ | MEnum _ _ sz _ => sz
  end.

Definition mty_align (m : mty) : nat :=
  match m with
  | MInt it => int_align it
  | MBool => 1
  | MPtr => PTR_ALIGN
  | MTuple _ _ al | MEnum _ _ _ al => al
  end.

(** *** Discriminators *)

(** Running a discriminator with a reader [rd] of the integers at given offsets. [None]
    (a failing read, or [DInvalid]) is UB. *)
Fixpoint discr_eval (rd : nat → IntType → option Z) (d : discr) : option Z :=
  match d with
  | DKnown t => Some t
  | DInvalid => None
  | DBranch off it fb ch =>
      z ← rd off it;
      (fix go ch := match ch with
        | [] => discr_eval rd fb
        | ((lo, hi), c) :: ch => if decide (lo ≤ z < hi) then discr_eval rd c else go ch
        end) ch
  end.

(** The reads of all the branches of a discriminator (on any path). *)
Fixpoint discr_reads (d : discr) : list (nat * IntType) :=
  match d with
  | DBranch off it fb ch =>
      (off, it) :: discr_reads fb ++
      (fix go ch := match ch with [] => [] | (_, c) :: ch => discr_reads c ++ go ch end) ch
  | _ => []
  end.

(** The length of the longest path. *)
Fixpoint discr_depth (d : discr) : nat :=
  match d with
  | DBranch _ _ fb ch =>
      S (Nat.max (discr_depth fb)
        ((fix go ch : nat := match ch with [] => 0%nat | (_, c) :: ch => Nat.max (discr_depth c) (go ch) end) ch))
  | _ => 0%nat
  end.

Lemma discr_eval_branch rd off it fb ch :
  discr_eval rd (DBranch off it fb ch) =
    z ← rd off it;
    match list_find (λ c, c.1.1 ≤ z < c.1.2) ch with
    | Some (_, (_, c)) => discr_eval rd c | None => discr_eval rd fb end.
Proof.
  simpl. destruct (rd off it) as [z|]; simpl; [|done].
  induction ch as [|[[lo hi] c] ch IH]; simpl; [done|]. case_decide; [done|].
  rewrite IH. by destruct (list_find _ ch) as [[??]|].
Qed.

Lemma elem_of_discr_reads_branch off it fb ch r :
  r ∈ discr_reads (DBranch off it fb ch) ↔
    r = (off, it) ∨ r ∈ discr_reads fb ∨ ∃ c, c ∈ ch ∧ r ∈ discr_reads c.2.
Proof.
  simpl. rewrite elem_of_cons elem_of_app. f_equiv. f_equiv.
  induction ch as [|[rc c] ch IH]; simpl.
  - split; [by intros ?%elem_of_nil|]. intros (? & ?%elem_of_nil & _). done.
  - rewrite elem_of_app IH. split.
    + intros [Hr|(c' & Hc' & Hr)]; [exists (rc, c); split; [left|]; done|].
      exists c'. split; [by right|done].
    + intros (c' & [->|Hc']%elem_of_cons & Hr); [by left|]. right. by exists c'.
Qed.

(** Two readers that agree on the reads of a discriminator give the same result. *)
Lemma discr_eval_agree rd rd' d :
  (∀ off it, (off, it) ∈ discr_reads d → rd off it = rd' off it) →
  discr_eval rd d = discr_eval rd' d.
Proof.
  induction d as [t| |off it fb ch IHfb IH] using discr_ind'; intros Hag; [done|done|].
  rewrite !discr_eval_branch Hag; [|apply elem_of_discr_reads_branch; by left].
  destruct (rd' off it) as [z|]; simpl; [|done].
  destruct (list_find _ ch) as [[k [r c]]|] eqn:Hf.
  - apply list_find_Some in Hf as (Hk & _ & _).
    apply (Forall_lookup_1 _ _ _ _ IH Hk). intros off' it' Hr. apply Hag.
    apply elem_of_discr_reads_branch. right. right. exists (r, c).
    split; [by eapply elem_of_list_lookup_2|done].
  - apply IHfb. intros off' it' Hr. apply Hag, elem_of_discr_reads_branch. by right; left.
Qed.

(** A reader that extends [rd] (on the reads where [rd] succeeds) gives the same result
    when [rd] gives one. *)
Lemma discr_eval_ext rd rd' d t :
  (∀ off it z, rd off it = Some z → rd' off it = Some z) →
  discr_eval rd d = Some t → discr_eval rd' d = Some t.
Proof.
  intros Hext. induction d as [t'| |off it fb ch IHfb IH] using discr_ind'; [done|done|].
  rewrite !discr_eval_branch. destruct (rd off it) as [z|] eqn:Hz; simpl; [|done].
  rewrite (Hext _ _ _ Hz) /=.
  destruct (list_find _ ch) as [[k [r c]]|] eqn:Hf; [|apply IHfb].
  apply list_find_Some in Hf as (Hk & _ & _). apply (Forall_lookup_1 _ _ _ _ IH Hk).
Qed.

(** The reader of the integers written by a tagger. *)
Fixpoint tagger_reader (tg : tagger) (off : nat) (it : IntType) : option Z :=
  match tg with
  | [] => None
  | (o, it', z) :: tg => if decide (o = off ∧ it' = it) then Some z else tagger_reader tg off it
  end.

Lemma tagger_reader_Some tg off it z :
  tagger_reader tg off it = Some z → (off, it, z) ∈ tg.
Proof.
  induction tg as [|[[o it'] z'] tg IH]; simpl; [done|].
  case_decide as Heq; [destruct Heq as [-> ->]; intros [= ->]; by left|].
  intros ?. right. by apply IH.
Qed.

(** ** Layout well-formedness

Fields and variant payloads lie within the type's size, the fields of a tuple do not
overlap, and the tagger entries of a variant lie within the size and outside its payload
and do not overlap. The discriminator of an enum gives each variant from its tagger
([discr_ok], by symbolic evaluation), and is _tag-only_: no branch reads a byte of a payload
([discr_tag_only]), so that writes into a payload never change the discriminant. (Niches
come later; alignment is not checked yet.) *)
Definition fields_disjoint (fs : list (nat * mty)) : Prop :=
  ∀ i j o1 m1 o2 m2, i ≠ j → fs !! i = Some (o1, m1) → fs !! j = Some (o2, m2) →
    (o1 + mty_size m1 ≤ o2 ∨ o2 + mty_size m2 ≤ o1)%nat.

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

(** The ranges [(offset, length)] do not overlap. *)
Definition ranges_disjoint (rs : list (nat * nat)) : Prop :=
  ∀ i j o1 n1 o2 n2, i ≠ j → rs !! i = Some (o1, n1) → rs !! j = Some (o2, n2) →
    (o1 + n1 ≤ o2 ∨ o2 + n2 ≤ o1)%nat.

Lemma ranges_disjoint_cons r rs :
  ranges_disjoint (r :: rs) ↔
    Forall (λ r', r.1 + r.2 ≤ r'.1 ∨ r'.1 + r'.2 ≤ r.1)%nat rs ∧ ranges_disjoint rs.
Proof.
  destruct r as [o n]. split.
  - intros H. split.
    + apply Forall_lookup=> k [o' n'] Hk. by apply (H 0%nat (S k) o n o' n').
    + intros i j ???? Hij Hi Hj. by apply (H (S i) (S j)); [lia| |].
  - intros [Hf Hrs] [|i] [|j] o1 n1 o2 n2 Hij Hi Hj; simplify_eq/=.
    + by apply (Forall_lookup_1 _ _ _ _ Hf Hj).
    + apply (Forall_lookup_1 _ _ _ _ Hf) in Hi. simpl in Hi. lia.
    + by apply (Hrs i j); [lia| |].
Qed.

Global Instance ranges_disjoint_dec rs : Decision (ranges_disjoint rs).
Proof.
  induction rs as [|r rs IH].
  - left. intros i ?????? Hi. by rewrite lookup_nil in Hi.
  - refine (cast_if (decide (Forall (λ r', r.1 + r.2 ≤ r'.1 ∨ r'.1 + r'.2 ≤ r.1)%nat rs ∧
      ranges_disjoint rs))); by rewrite ranges_disjoint_cons.
Defined.

(** The ranges of the entries of a tagger. *)
Definition tagger_ranges (tg : tagger) : list (nat * nat) := (λ e, (e.1.1, int_size e.1.2)) <$> tg.

(** The tagger [tg] of a variant whose payload is at [[o, o + n)], in an enum of size [sz]. *)
Definition tagger_wf (tg : tagger) (o n sz : nat) : Prop :=
  Forall (λ e, e.1.1 + int_size e.1.2 ≤ sz ∧ (e.1.1 + int_size e.1.2 ≤ o ∨ o + n ≤ e.1.1) ∧
    int_in_range e.1.2 e.2)%nat tg ∧
  ranges_disjoint (tagger_ranges tg).

(** The discriminator gives each variant from its tagger. *)
Definition discr_ok (vars : list (mty * nat * tagger)) (d : discr) : Prop :=
  Forall2 (λ i v, discr_eval (tagger_reader v.2) d = Some (Z.of_nat i)) (seq 0 (length vars)) vars.

(** No branch of the discriminator reads a payload byte (or out of bounds). *)
Definition discr_tag_only (vars : list (mty * nat * tagger)) (d : discr) (sz : nat) : Prop :=
  Forall (λ r, r.1 + int_size r.2 ≤ sz ∧
    Forall (λ v, r.1 + int_size r.2 ≤ v.1.2 ∨ v.1.2 + mty_size v.1.1 ≤ r.1) vars)%nat
    (discr_reads d).

(** The layout conditions of an enum (not recursive). *)
Definition enum_layout_ok (vars : list (mty * nat * tagger)) (d : discr) (sz : nat) : Prop :=
  Forall (λ v, v.1.2 + mty_size v.1.1 ≤ sz ∧ tagger_wf v.2 v.1.2 (mty_size v.1.1) sz)%nat vars ∧
  discr_tag_only vars d sz ∧ discr_ok vars d.

Global Instance enum_layout_ok_dec vars d sz : Decision (enum_layout_ok vars d sz).
Proof. rewrite /enum_layout_ok /discr_ok /discr_tag_only /tagger_wf. apply _. Defined.

Inductive mty_wf : mty → Prop :=
| MInt_wf it : mty_wf (MInt it)
| MBool_wf : mty_wf MBool
| MPtr_wf : mty_wf MPtr
| MTuple_wf fs sz al :
    fields_disjoint fs →
    Forall (λ f, f.1 + mty_size f.2 ≤ sz)%nat fs →
    Forall (λ f, mty_wf f.2) fs →
    mty_wf (MTuple fs sz al)
| MEnum_wf vars d sz al :
    enum_layout_ok vars d sz →
    Forall (λ v, mty_wf v.1.1) vars →
    mty_wf (MEnum vars d sz al).

(** Well-formedness of MiniRust types is decidable ([mty_wfb_correct]). *)
Fixpoint mty_wfb (m : mty) : bool :=
  match m with
  | MInt _ | MBool | MPtr => true
  | MTuple fs sz _ =>
      bool_decide (fields_disjoint fs) &&
      bool_decide (Forall (λ f, f.1 + mty_size f.2 ≤ sz)%nat fs) &&
      (fix go fs := match fs with [] => true | (_, f) :: fs => mty_wfb f && go fs end) fs
  | MEnum vars d sz _ =>
      bool_decide (enum_layout_ok vars d sz) &&
      (fix go vars := match vars with [] => true | (vm, _, _) :: vars => mty_wfb vm && go vars end) vars
  end.

Lemma mty_wfb_correct m : mty_wfb m ↔ mty_wf m.
Proof.
  induction m as [| | |fs sz al IH|vars d sz al IH] using mty_ind'; simpl.
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
    cut ((fix go (vars : list (mty * nat * tagger)) := match vars with [] => true
      | (vm, _, _) :: vars => mty_wfb vm && go vars end) vars ↔ Forall (λ v, mty_wf v.1.1) vars).
    { intros ->. split; [intros [??]; by constructor|by inversion 1]. }
    induction IH as [|[[vm o] tg] vars Hv _ IH']; simpl; [split; [constructor|done]|].
    rewrite andb_True Hv IH' Forall_cons. done.
Qed.

Global Instance mty_wf_dec m : Decision (mty_wf m).
Proof. refine (cast_if (decide (mty_wfb m))); by rewrite -mty_wfb_correct. Defined.

Lemma discr_ok_lookup vars d t v :
  discr_ok vars d → vars !! t = Some v → discr_eval (tagger_reader v.2) d = Some (Z.of_nat t).
Proof.
  intros Hok Hv. have Ht : seq 0 (length vars) !! t = Some t.
  { apply lookup_seq. split; [lia|]. by eapply lookup_lt_Some. }
  by apply (Forall2_lookup_lr _ _ _ _ _ _ Hok Ht Hv).
Qed.

Lemma mty_wf_enum_inv vars d sz al :
  mty_wf (MEnum vars d sz al) → enum_layout_ok vars d sz ∧ Forall (λ v, mty_wf v.1.1) vars.
Proof. by inversion 1. Qed.

Lemma mty_wf_tuple_inv fs sz al :
  mty_wf (MTuple fs sz al) → fields_disjoint fs ∧
    Forall (λ f, f.1 + mty_size f.2 ≤ sz)%nat fs ∧ Forall (λ f, mty_wf f.2) fs.
Proof. by inversion 1. Qed.

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
| VTuple_wf fs sz al vs :
    Forall2 (λ f v, val_wf f.2 v) fs vs → val_wf (MTuple fs sz al) (VTuple vs)
| VVariant_wf vars d sz al t vm o tg v :
    0 ≤ t → vars !! Z.to_nat t = Some (vm, o, tg) → val_wf vm v →
    val_wf (MEnum vars d sz al) (VVariant t v).

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

  (** Write the integers of a tagger over [base]. *)
  Definition write_tagger (tg : tagger) base :=
    fill_fields ((λ e, (e.1.1, encode_int e.1.2 e.2)) <$> tg) base.

  (** The reader of the integers of the bytes [bs], and the discriminant that the
      discriminator [d] reads from [bs]. *)
  Definition bytes_reader bs (off : nat) (it : IntType) : option Z :=
    decode_int it (list_slice off (int_size it) bs).
  Definition decode_discr (d : discr) bs : option Z := discr_eval (bytes_reader bs) d.

  Fixpoint encode_value (m : mty) (v : Value) : list (AbstractByte) :=
    match m, v with
    | MInt it, VInt z => encode_int it z
    | MBool, VBool b => encode_bool b
    | MPtr, VPtr l => encode_ptr l
    | MTuple fs sz _, VTuple vs =>
        (fix go fs vs := match fs, vs with
          | (off, fm) :: fs, fv :: vs => list_inserts off (encode_value fm fv) (go fs vs)
          | _, _ => replicate sz Uninit end) fs vs
    | MEnum vars _ sz _, VVariant t d =>
        (fix pick vars n := match vars, n with
          | [], _ => replicate sz Uninit
          | (vm, o, tg) :: _, O =>
              write_tagger tg (list_inserts o (encode_value vm d) (replicate sz Uninit))
          | _ :: vars, S n => pick vars n end) vars (Z.to_nat t)
    | _, _ => replicate (mty_size m) Uninit
    end.

  Fixpoint decode_value (m : mty) bs : option Value :=
    match m with
    | MInt it => VInt <$> decode_int it bs
    | MBool => VBool <$> decode_bool bs
    | MPtr => VPtr <$> decode_ptr bs
    | MTuple fs sz _ =>
        if decide (length bs = sz) then
          VTuple <$> (fix go fs := match fs with
            | [] => Some []
            | (off, fm) :: fs =>
                v ← decode_value fm (list_slice off (mty_size fm) bs);
                vs ← go fs; Some (v :: vs) end) fs
        else None
    | MEnum vars d sz _ =>
        if decide (length bs = sz) then
          t ← decode_discr d bs;
          if decide (0 ≤ t) then
            (fix pick vars n := match vars, n with
              | [], _ => None
              | (vm, o, _) :: _, O =>
                  VVariant t <$> decode_value vm (list_slice o (mty_size vm) bs)
              | _ :: vars, S n => pick vars n end) vars (Z.to_nat t)
          else None
        else None
    end.

  (** *** Unfolding lemmas *)
  Lemma encode_value_tuple fs sz al vs :
    encode_value (MTuple fs sz al) (VTuple vs) =
    fill_fields (zip_with (λ f v, (f.1, encode_value f.2 v)) fs vs) (replicate sz Uninit).
  Proof.
    simpl. revert vs. induction fs as [|[o f] fs IH]; intros [|v vs]; simpl; try done.
    by rewrite IH.
  Qed.

  Lemma encode_value_enum vars d sz al t v :
    encode_value (MEnum vars d sz al) (VVariant t v) =
    match vars !! Z.to_nat t with
    | Some (vm, o, tg) => write_tagger tg (list_inserts o (encode_value vm v) (replicate sz Uninit))
    | None => replicate sz Uninit
    end.
  Proof.
    simpl. generalize (Z.to_nat t). induction vars as [|[[vm o] tg] vars IH]; intros [|n]; simpl; auto.
  Qed.

  Lemma decode_value_tuple fs sz al bs :
    decode_value (MTuple fs sz al) bs =
    if decide (length bs = sz) then
      VTuple <$> mapM (λ f, decode_value f.2 (list_slice f.1 (mty_size f.2) bs)) fs
    else None.
  Proof.
    simpl. case_decide; [|done]. f_equal.
    induction fs as [|[o f] fs IH]; simpl; [done|]. by rewrite IH.
  Qed.

  Lemma decode_value_enum vars d sz al bs :
    decode_value (MEnum vars d sz al) bs =
    if decide (length bs = sz) then
      t ← decode_discr d bs;
      if decide (0 ≤ t) then
        v ← vars !! Z.to_nat t;
        VVariant t <$> decode_value v.1.1 (list_slice v.1.2 (mty_size v.1.1) bs)
      else None
    else None.
  Proof.
    simpl. case_decide; [|done]. destruct (decode_discr d bs) as [t|]; simpl; [|done].
    case_decide; [|done]. generalize (Z.to_nat t).
    induction vars as [|[[vm o] tg] vars IH]; intros [|n]; simpl; auto.
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
    destruct m as [it| | |fs sz al|vars d sz al], v as [z|b|l|vs|t w];
      rewrite ?encode_value_tuple ?encode_value_enum /=;
      rewrite ?length_replicate ?length_encode_int ?length_encode_ptr ?length_fill_fields
        ?length_replicate //.
    destruct (vars !! _) as [[[??]?]|];
      by rewrite /write_tagger ?length_fill_fields ?length_inserts length_replicate.
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

  (** A slice outside all the insertions of [fill_fields]. *)
  Lemma list_slice_fill_fields_out ins base o n :
    (∀ k o' e, ins !! k = Some (o', e) → (o' + length e ≤ o ∨ o + n ≤ o')%nat) →
    list_slice o n (fill_fields ins base) = list_slice o n base.
  Proof.
    intros Hout. apply list_eq. intros i. rewrite /list_slice.
    destruct (decide (i < n)%nat).
    - rewrite !lookup_take // !lookup_drop. apply lookup_fill_fields_out.
      intros k o' e Hk. destruct (Hout k o' e Hk); lia.
    - rewrite !lookup_take_ge //; lia.
  Qed.

  (** The bytes of an entry of a tagger. *)
  Lemma list_slice_write_tagger tg base off it z :
    ranges_disjoint (tagger_ranges tg) →
    Forall (λ e, e.1.1 + int_size e.1.2 ≤ length base)%nat tg →
    (off, it, z) ∈ tg →
    list_slice off (int_size it) (write_tagger tg base) = encode_int it z.
  Proof.
    intros Hdisj Hin (k & Hk)%elem_of_list_lookup.
    rewrite -{1}(length_encode_int it z). apply (list_slice_fill_fields _ _ k).
    - by rewrite list_lookup_fmap Hk.
    - intros k' o' e' Hk' He'. rewrite list_lookup_fmap in He'.
      apply fmap_Some in He' as ([[o'' it'] z'] & Hk'' & [= -> ->]).
      rewrite !length_encode_int.
      apply (Hdisj k' k o'' (int_size it') off (int_size it)); [done| |];
        by rewrite /tagger_ranges list_lookup_fmap ?Hk ?Hk''.
    - rewrite length_encode_int. apply (Forall_lookup_1 _ _ _ _ Hin Hk).
  Qed.

  Lemma list_slice_write_tagger_out tg base o n :
    Forall (λ e, e.1.1 + int_size e.1.2 ≤ o ∨ o + n ≤ e.1.1)%nat tg →
    list_slice o n (write_tagger tg base) = list_slice o n base.
  Proof.
    intros Hout. apply list_slice_fill_fields_out. intros k o' e Hk.
    rewrite list_lookup_fmap in Hk. apply fmap_Some in Hk as ([[o'' it] z] & Hk' & [= -> ->]).
    rewrite length_encode_int.
    apply (Forall_lookup_1 _ _ _ _ Hout Hk').
  Qed.

  (** The discriminator reads the discriminant of a variant from its encoding. *)
  Lemma decode_discr_encode vars d sz al t vm o tg w :
    mty_wf (MEnum vars d sz al) → (0 ≤ t)%Z → vars !! Z.to_nat t = Some (vm, o, tg) →
    length w = sz →
    decode_discr d (write_tagger tg w) = Some t.
  Proof.
    intros Hwf Ht Hvm Hlen. apply mty_wf_enum_inv in Hwf as [(Hvars & _ & Hok) _].
    have Hd := discr_ok_lookup _ _ _ _ Hok Hvm. rewrite Z2Nat.id // in Hd.
    destruct (Forall_lookup_1 _ _ _ _ Hvars Hvm) as [_ [Htg Hdisj]]. simpl in *.
    eapply discr_eval_ext; [|exact Hd]. intros off it z Hz%tagger_reader_Some.
    rewrite /bytes_reader (list_slice_write_tagger _ _ _ _ z) //.
    - apply decode_encode_int. rewrite Forall_forall in Htg. by apply (Htg _ Hz).
    - apply Forall_forall. intros e He. rewrite Hlen. rewrite Forall_forall in Htg. by apply (Htg _ He).
  Qed.

  (** *** The round-trip law *)
  Theorem decode_encode_value m v : mty_wf m → val_wf m v → decode_value m (encode_value m v) = Some v.
  Proof.
    revert v. induction m as [it| | |fs sz al IH|vars d sz al IH] using mty_ind';
      intros v Hm Hv; inversion Hv as [? z Hz|b|l|? ? ? vs Hvs|? ? ? ? t vm o tg w Ht Hvm Hw];
      simplify_eq.
    - by rewrite /= decode_encode_int.
    - by destruct b.
    - by rewrite /= decode_encode_ptr.
    - inversion Hm as [| | |? ? ? Hdisj Hin Hwf|]; simplify_eq.
      rewrite -/(encode_value (MTuple fs sz al) (VTuple vs)) decode_value_tuple encode_value_tuple.
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
    - have Hm' := Hm. apply mty_wf_enum_inv in Hm' as [(Hvars & _ & _) Hwfs].
      rewrite -/(encode_value (MEnum vars d sz al) (VVariant t w)) decode_value_enum
        encode_value_enum Hvm.
      destruct (Forall_lookup_1 _ _ _ _ Hvars Hvm) as [Hsz [Htg _]]. simpl in *.
      have Hwf := Forall_lookup_1 _ _ _ _ Hwfs Hvm.
      rewrite /write_tagger length_fill_fields length_inserts length_replicate decide_True //.
      rewrite (decode_discr_encode vars d sz al t vm o tg); [|done..|];
        last by rewrite length_inserts length_replicate.
      rewrite /= decide_True // Hvm /=. rewrite -/(write_tagger tg _).
      rewrite list_slice_write_tagger_out;
        [|by eapply Forall_impl; [exact Htg|]; intros e (_ & ? & _)].
      rewrite -(length_encode_value vm w) list_slice_inserts;
        last by rewrite length_replicate length_encode_value.
      rewrite (Forall_lookup_1 _ _ _ _ IH Hvm) //.
  Qed.

  (** *** Decoding determines the length *)
  Lemma decode_value_length m bs v : decode_value m bs = Some v → length bs = mty_size m.
  Proof.
    destruct m as [it| | |fs sz al|vars d sz al]; simpl; intros Hd.
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

  Lemma decode_int_mono it bs1 bs2 z :
    bytes_le bs1 bs2 → decode_int it bs1 = Some z → decode_int it bs2 = Some z.
  Proof. intros Hle Hz. rewrite (bytes_le_defined bs1 bs2) //. by eapply decode_int_defined. Qed.

  Lemma decode_discr_mono d bs1 bs2 t :
    bytes_le bs1 bs2 → decode_discr d bs1 = Some t → decode_discr d bs2 = Some t.
  Proof.
    intros Hle. apply discr_eval_ext. intros off it z. rewrite /bytes_reader.
    apply decode_int_mono. by apply Forall2_take, Forall2_drop.
  Qed.

  Theorem decode_value_mono m bs1 bs2 v :
    bytes_le bs1 bs2 → decode_value m bs1 = Some v → decode_value m bs2 = Some v.
  Proof.
    revert bs1 bs2 v. induction m as [it| | |fs sz al IH|vars d sz al IH] using mty_ind';
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
      destruct (decode_discr d bs1) as [t|] eqn:Ht; [|done]. simpl in Hdec.
      rewrite (decode_discr_mono d bs1 bs2 t) //=. case_decide; [|done].
      destruct (vars !! Z.to_nat t) as [vv|] eqn:Hvm; [|done]. simpl in *.
      apply fmap_Some_1 in Hdec as (w&Hw&->). apply fmap_Some_2.
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
    revert bs v. induction m as [it| | |fs sz al IH|vars d sz al IH] using mty_ind';
      intros bs v Hm Hd.
    - apply fmap_Some_1 in Hd as (z & Hz & ->). constructor. by eapply decode_int_in_range.
    - apply fmap_Some_1 in Hd as (b & _ & ->). constructor.
    - apply fmap_Some_1 in Hd as (l & _ & ->). constructor.
    - inversion Hm as [| | |? ? ? _ _ Hwf|]; simplify_eq.
      rewrite decode_value_tuple in Hd. case_decide; [|done].
      apply fmap_Some_1 in Hd as (vs & Hvs & ->). apply mapM_Some in Hvs.
      have Hlen := Forall2_length _ _ _ Hvs.
      constructor. apply Forall2_lookup. intros k.
      destruct (fs !! k) as [f|] eqn:Hf, (vs !! k) as [w|] eqn:Hw; try constructor.
      + eapply (Forall_lookup_1 _ _ _ _ IH Hf); [exact (Forall_lookup_1 _ _ _ _ Hwf Hf)|].
        exact (Forall2_lookup_lr _ _ _ _ _ _ Hvs Hf Hw).
      + exfalso. apply lookup_ge_None in Hw. apply lookup_lt_Some in Hf. lia.
      + exfalso. apply lookup_ge_None in Hf. apply lookup_lt_Some in Hw. lia.
    - apply mty_wf_enum_inv in Hm as [_ Hwfs].
      rewrite decode_value_enum in Hd. case_decide; [|done].
      destruct (decode_discr d bs) as [t|] eqn:Ht; simpl in Hd; [|done].
      case_decide as Ht0; [|done].
      destruct (vars !! Z.to_nat t) as [[[vm o] tg]|] eqn:Hvm; simpl in Hd; [|done].
      apply fmap_Some_1 in Hd as (w & Hw & ->).
      econstructor; [done|done|].
      by eapply (Forall_lookup_1 _ _ _ _ IH Hvm _ _ (Forall_lookup_1 _ _ _ _ Hwfs Hvm)).
  Qed.
End repr.
