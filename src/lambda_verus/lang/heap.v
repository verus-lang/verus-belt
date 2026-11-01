Require Import guarding.internal.na_invariants_fork.
From lrust.util Require Import atomic_lock_counter update.
From lrust.util Require Export cellmap.
From guarding Require Import guard.
From Coq.Arith Require Import PeanoNat.
From stdpp Require Import coPset.
From iris.algebra Require Import big_op gmap frac agree numbers.
From iris.algebra Require Import csum excl auth cmra_big_op.
From iris.algebra.lib Require Import gmap_view.
From iris.bi Require Import fractional.
From iris.base_logic Require Export lib.own.
From iris.proofmode Require Export proofmode.
From iris.base_logic.lib Require Export ghost_map.
From lrust.lang Require Export fvalue.
From lrust.lang Require Export lang.
From iris.prelude Require Import options.
Import uPred.

(** * The heap

Physical memory holds abstract bytes ([state' = gmap loc (lock_state * abyte)]). Its
ghost state is a full-authority cell map ([fcmapR] of [util/cellmap.v]) whose values
([bval]) are a lock state and an abstract byte, which backs the byte points-to
[l ↦b bs]. Each location has a row: a chain of byte-cells (possibly empty) ending in its
value. The physical memory is [𝜙 𝛼] (the values of the location rows), plus the read
counts of the bank of guarded reads ([bytes_ctx]). (The legacy word region, a
non-atomic map of [val]s that backed the word points-to [l ↦ v], was deleted in
stage 6.) *)

(** The namespace of the non-atomic accesses (guarded reads and writes). *)
Definition naN : namespace := nroot .@ "leaf_lifetime_logic" .@ "guarding".

Canonical Structure abyteO := leibnizO abyte.

(** The values of the rows of the byte region: a lock state and a byte. *)
Definition bval : Type := lock_state * abyte.

(** The full maps of the byte region: rows of byte-cells ([positive]) ending in a [bval]. *)
Notation bfull := (full_map loc positive bval).
Notation bphi := (𝜙 loc positive bval).

Definition heap_freeableUR : ucmra :=
  gmapUR block (prodR fracR (gmapR Z (exclR unitO))).

Class heapGS Σ := HeapGS {
  #[global] heap_bmap_inG :: fcmap_logicG loc positive bval Σ;
  #[global] heap_freeable_inG :: inG Σ (authR heap_freeableUR);
  #[global] heap_bbank_inG :: inG Σ (gmap_viewR nat (agreeR (prodO (leibnizO (loc * list abyte))
    (laterO (iPropO Σ)))));
  #[global] heap_greg_inG :: ghost_mapG Σ positive (mty * list positive);
  #[global] heap_gdyn_inG :: ghost_mapG Σ positive FValue;
  #[global] heap_gnc_inG :: ghost_mapG Σ positive ();
  #[global] heap_gnest_inG :: ghost_mapG Σ (positive * positive * nat) ();
  #[global] heap_cw_inG :: inG Σ (gmap_viewR positive (agreeR (prodO
    (leibnizO (loc * nat * nat * FValue)) (laterO (iPropO Σ)))));
  heap_bytes_name : gname;
  heap_bbank_name : gname;
  heap_greg_name : gname;
  heap_gdyn_name : gname;
  heap_gnc_name : gname;
  heap_gnest_name : gname;
  heap_cw_name : gname;
  heap_freeable_name : gname;
  atomic_threadpool: gname;
  atomic_lock_ctr_name: gname;
  (* The edges of the byte region and the dynamic registry of cell groups are different
     ghost cells, so that guards of the location side of a group and of its permission can
     be combined ([loc_side_and_gdyn] in [lang/heap_cells.v]). *)
  heap_bytes_gdyn_ne : heap_bytes_name ≠ heap_gdyn_name
}.

Definition heap_freeable_rel (σ : state) (hF : heap_freeableUR) : Prop :=
  ∀ blk qs, hF !! blk = Some qs →
    qs.2 ≠ ∅ ∧ ∀ i, is_Some (σ.1 !! (blk, i)) ↔ is_Some (qs.2 !! i).

(** * The byte region *)
Section byte_defs.
  Context `{!heapGS Σ}.

  (** The authority of the byte region, its edges and its untethered rows. *)
  Definition bheap (𝛼 : bfull) : iProp Σ := fheap loc positive bval heap_bytes_name 𝛼.
  Definition bpt (lc : loc + positive) (cv : positive + bval) : iProp Σ :=
    fpt loc positive bval heap_bytes_name lc cv.
  Definition bunt (u : untether_id) (c : positive) (v : bval) : iProp Σ :=
    funt loc positive bval heap_bytes_name u c v.

  (** A location without cells, with lock state [st] and byte [b]. *)
  Definition heap_mapsto_st (st : lock_state) (l : loc) (b : abyte) : iProp Σ :=
    bpt (inl l) (inr (st, b)).

  Definition heap_mapsto_st_vec (st : lock_state) (l : loc) (bs : list abyte) : iProp Σ :=
    [∗ list] i ↦ b ∈ bs, heap_mapsto_st st (l +ₗ i) b.

  (** The byte points-to: [l ↦b bs] owns the bytes [bs] at [l], [l +ₗ 1], ..., which are
      not in cells. *)
  Definition heap_mapsto_bytes_def (l : loc) (bs : list abyte) : iProp Σ :=
    heap_mapsto_st_vec (RSt 0) l bs.
  Definition heap_mapsto_bytes_aux : seal (@heap_mapsto_bytes_def). Proof. by eexists. Qed.
  Definition heap_mapsto_bytes := unseal heap_mapsto_bytes_aux.
  Definition heap_mapsto_bytes_eq : @heap_mapsto_bytes = @heap_mapsto_bytes_def :=
    seal_eq heap_mapsto_bytes_aux.
End byte_defs.

Global Instance: Params (@heap_mapsto_bytes) 3 := {}.

Notation "l ↦b bs" := (heap_mapsto_bytes l bs) (at level 20) : bi_scope.

(** ** Cell groups

A _cell group_ [g] is a multi-byte cell: the MiniRust type [m_g] of its contents and one
byte-cell per byte ([cs_g], with [length cs_g = mty_size m_g > 0]). The static registry
[greg g m_g cs_g] is persistent; the dynamic registry holds the current fancy value of each
live group, and its fragment [gdyn g fv] is the permission of the group. Groups whose
fancy value never contains cells are recorded persistently ([gnocell g]).

The byte context owns the _contents_ of the cells of every live group (the edges
[inr c ↦ ...] from its byte-cells) and keeps the decodability invariant D3: the contents
of a group represent its fancy value ([frepr], which depends only on the static
registry). The bytes of the contents of a group only change in the second phase of a
write, together with its fancy value, so D3 needs no exemption for groups with a write in
flight (their contents are marked [WSt], and [fb_strip] ignores lock states).

A non-atomic write through a cell ([bytes_ctx_cell_write_begin]) deposits the permission
of the group, and the guard of its location side, in the bank of cell writes ([CW]) for
the duration of the write. *)

(** A fancy byte of the byte region without its lock state. *)
Definition fb_strip (fb : positive + bval) : positive + abyte :=
  match fb with inl c => inl c | inr (_, b) => inr b end.

(** A fancy byte with lock state [RSt 0]. *)
Definition fb_rst (fb : positive + abyte) : positive + bval :=
  match fb with inl c => inl c | inr b => inr (RSt 0, b) end.

(** The data of a cell write in flight: the location of the group, the offset and the
    length of the written range, and the fancy value of the group before the write. *)
Definition cwkey : Type := loc * nat * nat * FValue.

(** The lock state of the byte [i] of the contents of [g]. *)
Definition cw_ls (CW : gmap positive cwkey) (g : positive) (i : nat) : lock_state :=
  match CW !! g with
  | Some (_, o, n, _) => if decide (o ≤ i < o + n)%nat then WSt else RSt 0
  | None => RSt 0
  end.

(** The nesting of groups: [nest_path NS g0 g o] says that the group [g] sits at the
    offset [o] inside the group [g0], following the nestings [NS]. A nesting
    [(g0, g1, o1) ∈ dom NS] says that the contents of [g0] at [o1] are the byte-cells of
    [g1] (while [g0] is live). *)
Inductive nest_path (NS : gmap (positive * positive * nat) ()) : positive → positive → nat → Prop :=
| nest_path_refl g : nest_path NS g g 0
| nest_path_step g0 g1 o1 g o :
    NS !! (g0, g1, o1) = Some () → nest_path NS g1 g o → nest_path NS g0 g (o1 + o).

(** The row of the location [l] contains the byte-cell [c]. *)
Definition row_has (𝛼 : bfull) (l : loc) (c : positive) : Prop :=
  ∃ cells v, 𝛼 !! inl l = Some (cells, v) ∧ c ∈ cells.

(** The pure invariants of the cell registry. *)
Definition cells_wf (R : gmap positive (mty * list positive)) (ρ : gmap positive FValue)
    (NC : gmap positive ()) (NS : gmap (positive * positive * nat) ())
    (CW : gmap positive cwkey) : Prop :=
  reg_wf R ∧ dom ρ ⊆ dom R ∧
  (∀ g fv, ρ !! g = Some fv → ∀ g', g' ∈ fv_cells fv → (g' < g)%positive ∧ g' ∈ dom ρ) ∧
  (∀ g1 g2 m1 cs1 m2 cs2, g1 ≠ g2 → R !! g1 = Some (m1, cs1) → R !! g2 = Some (m2, cs2) →
     cs1 ## cs2) ∧
  (∀ g m cs, R !! g = Some (m, cs) → (0 < mty_size m)%nat) ∧
  dom NC ⊆ dom R ∧ (∀ g fv, ρ !! g = Some fv → g ∈ dom NC → fv_cells fv = []) ∧
  (∀ g k, CW !! g = Some k → ρ !! g = Some k.2 ∧
     ∃ m cs, R !! g = Some (m, cs) ∧ (k.1.1.2 + k.1.2 ≤ length cs)%nat) ∧
  (∀ g m cs, R !! g = Some (m, cs) → mty_wf m) ∧
  (∀ k, k ∈ dom NS → k.1.1 ∈ dom R).

(** Every byte-cell of the byte region belongs to a live group, and the rows of the
    locations of a group with a write in flight contain its byte-cells. *)
Definition cells_live (𝛼 : bfull) (R : gmap positive (mty * list positive))
    (ρ : gmap positive FValue) (CW : gmap positive cwkey) : Prop :=
  (∀ k cs v c, 𝛼 !! k = Some (cs, v) → c ∈ cs →
     ∃ g m cs', g ∈ dom ρ ∧ R !! g = Some (m, cs') ∧ c ∈ cs') ∧
  (∀ g k m cs, CW !! g = Some k → R !! g = Some (m, cs) →
     ∀ (i : nat) c, cs !! i = Some c → row_has 𝛼 (k.1.1.1 +ₗ i) c).

(** The pure part of the contents [fbs] of a live group [g] (D3): they represent its fancy
    value, their lock states mirror the bank of cell writes, and they contain the byte-cells
    of the groups nested in [g]. *)
Definition gc_pure (R : gmap positive (mty * list positive)) (NS : gmap (positive * positive * nat) ())
    (CW : gmap positive cwkey) (g : positive) (fv : FValue) (m : mty) (cs : list positive)
    (fbs : list (positive + bval)) : Prop :=
  R !! g = Some (m, cs) ∧ frepr R m (fb_strip <$> fbs) fv ∧
  (∀ i ls b, fbs !! i = Some (inr (ls, b)) → ls = cw_ls CW g i) ∧
  (∀ g' o, (g, g', o) ∈ dom NS → ∃ m' cs', R !! g' = Some (m', cs') ∧
     list_slice o (length cs') (fb_strip <$> fbs) = inl <$> cs').

Section cells_defs.
  Context `{!heapGS Σ}.
  Context `{!invGS Σ}.

  (** The static registry: the group [g] has the MiniRust type [m] and the byte-cells [cs]. *)
  Definition greg (g : positive) (m : mty) (cs : list positive) : iProp Σ :=
    g ↪[heap_greg_name]□ (m, cs).
  (** The permission of the group [g]: its current fancy value is [fv]. *)
  Definition gdyn (g : positive) (fv : FValue) : iProp Σ := g ↪[heap_gdyn_name] fv.
  (** The fancy value of the group [g] never contains cells. *)
  Definition gnocell (g : positive) : iProp Σ := g ↪[heap_gnc_name]□ ().
  (** The group [g] is nested at the offset [o] inside the group [g0] (as long as [g0] is
      live). *)
  Definition gnest (g0 g : positive) (o : nat) : iProp Σ := (g0, g, o) ↪[heap_gnest_name]□ ().
  (** The group [g] sits at the offset [o] inside the group [g0], through nestings. *)
  Definition gpath (g0 g : positive) (o : nat) : iProp Σ :=
    ∃ NS, ⌜nest_path NS g0 g o⌝ ∗ [∗ map] k ↦ _ ∈ NS, gnest k.1.1 k.1.2 k.2.

  (** The contents [fbs] of the byte-cells [cs]. *)
  Definition bcells (cs : list positive) (fbs : list (positive + bval)) : iProp Σ :=
    [∗ list] c; fb ∈ cs; fbs, bpt (inr c) fb.

  (** The location side of a cell group, i.e. the [PCell] itself: the locations [l],
      [l +ₗ 1], ... point to the byte-cells of [g]. *)
  Definition loc_side (l : loc) (g : positive) (m : mty) (cs : list positive) : iProp Σ :=
    greg g m cs ∗ [∗ list] i ↦ c ∈ cs, bpt (inl (l +ₗ i)) (inl c).

  (** A cell group in transit (after [bytes_ctx_pcell_untether]): the byte-cells of [g]
      head untethered rows, whose final bytes are [bs]. *)
  Definition untethered (g : positive) (m : mty) (cs : list positive) (bs : list abyte)
      : iProp Σ :=
    greg g m cs ∗ [∗ list] c; b ∈ cs; bs, ∃ u, bunt u c (RSt 0, b).

  (** Fancy bytes in transit (after [bytes_ctx_fbytes_untether]), with the bytes [bs]: each
      byte-cell of [fbs] heads an untethered row whose final byte is the byte of [bs] at its
      position, and the plain bytes of [fbs] are those of [bs]. This is the form of the
      several (sibling) groups of a value with cells in transit: [untethered g m cs bs] is
      [unt_fbytes (inl <$> cs) bs] ([untethered_fbytes]). *)
  Definition unt_fb (fb : positive + abyte) (b : abyte) : iProp Σ :=
    match fb with inl c => ∃ u, bunt u c (RSt 0, b) | inr b' => ⌜b' = b⌝ end.
  Definition unt_fbytes (fbs : list (positive + abyte)) (bs : list abyte) : iProp Σ :=
    [∗ list] fb; b ∈ fbs; bs, unt_fb fb b.

  (** Fancy bytes at locations: [l +ₗ i] points to the byte-cell or the byte [fbs !! i]. *)
  Definition heap_mapsto_fbytes (l : loc) (fbs : list (positive + abyte)) : iProp Σ :=
    [∗ list] i ↦ fb ∈ fbs, bpt (inl (l +ₗ i)) (fb_rst fb).

  (** The fancy bytes [fbs] represent [fv] at [m], with the static registry. *)
  Definition brepr (m : mty) (fbs : list (positive + abyte)) (fv : FValue) : iProp Σ :=
    ∃ R, ⌜frepr R m fbs fv⌝ ∗ [∗ map] g ↦ e ∈ R, greg g e.1 e.2.

  (** The contents of a live group, owned by the byte context, with the invariant D3. *)
  Definition gcontents (R : gmap positive (mty * list positive))
      (NS : gmap (positive * positive * nat) ()) (CW : gmap positive cwkey)
      (g : positive) (fv : FValue) : iProp Σ :=
    ∃ m cs fbs, ⌜gc_pure R NS CW g fv m cs fbs⌝ ∗ bcells cs fbs.

  (** The bank of cell writes. *)
  Definition cw_elt (k : cwkey) (G : iProp Σ) : prodO (leibnizO cwkey) (laterO (iPropO Σ)) :=
    (k, Next G).
  Definition cwbank_auth (CW : gmap positive (cwkey * iProp Σ)) : iProp Σ :=
    own heap_cw_name (gmap_view_auth (DfracOwn 1)
      ((λ e : cwkey * iProp Σ, to_agree (cw_elt e.1 e.2)) <$> CW)).
  Definition cwrite_tok (g : positive) (k : cwkey) (G : iProp Σ) : iProp Σ :=
    own heap_cw_name (gmap_view_frag g (DfracOwn 1) (to_agree (cw_elt k G))).
  (** An entry of the bank of cell writes: the permission of the group, and the guard [G]
      of the location side of the group [g0] in which [g] is nested (possibly [g] itself). *)
  Definition cwentry (g : positive) (e : cwkey * iProp Σ) : iProp Σ :=
    ∃ m cs, greg g m cs ∗ gdyn g e.1.2 ∗ e.2 ∗ ∃ P d, £d ∗ (e.2 &&{↑naN; d}&&> P) ∗
      □ (P -∗ ∃ l0 g0 m0 cs0 (o : nat), ⌜e.1.1.1.1 = l0 +ₗ o ∧ (o + length cs ≤ length cs0)%nat⌝ ∗
           loc_side l0 g0 m0 cs0).

  Definition cells_ctx (𝛼 : bfull) : iProp Σ :=
    ∃ R ρ NC NS (CW : gmap positive (cwkey * iProp Σ)),
      ghost_map_auth heap_greg_name 1 R ∗ ghost_map_auth heap_gdyn_name 1 ρ ∗
      ghost_map_auth heap_gnc_name 1 NC ∗ ghost_map_auth heap_gnest_name 1 NS ∗
      cwbank_auth CW ∗
      ⌜cells_wf R ρ NC NS (fst <$> CW) ∧ cells_live 𝛼 R ρ (fst <$> CW)⌝ ∗
      ([∗ map] g ↦ e ∈ R, greg g e.1 e.2) ∗ ([∗ map] k ↦ _ ∈ NS, gnest k.1.1 k.1.2 k.2) ∗
      ([∗ map] g ↦ e ∈ CW, cwentry g e) ∗
      [∗ map] g ↦ fv ∈ ρ, gcontents R NS (fst <$> CW) g fv.

  (** The read witness of an entry of the bank of guarded reads, of the location edges [cvs]
      of the range at [l]: they all point to bytes, or the range is a plain sub-value at the
      offset [o'] of a group [g] whose permission the reader has, which sits at the offset [o]
      inside the group [g0] whose byte-cells the edges point to. *)
  Definition cells_wit (l : loc) (cvs : list (positive + bval)) : iProp Σ :=
    ⌜Forall (λ cv, ∃ v, cv = inr v) cvs⌝ ∨
    ∃ l0 g0 m0 cs0 g o m cs fv o' m' fvs,
      greg g0 m0 cs0 ∗ gpath g0 g o ∗ greg g m cs ∗ gdyn g fv ∗
      ⌜l = l0 +ₗ (o + o')%nat ∧ cvs = inl <$> list_slice (o + o') (length cvs) cs0 ∧
       fv_sub m fv o' m' fvs ∧ fv_cells fvs = [] ∧ length cvs = mty_size m'⌝.
End cells_defs.

(** ** The bank of guarded reads of the byte region

A non-atomic read of bytes that are only _guarded_ ([G &&{↑naN; d}&&> l ↦b bs], as
in the sharing predicate of a shared reference) cannot keep the points-to across the
two steps of the read. As in the non-atomic map of lambda-Rust (its read bank),
the guard [G] is deposited in a bank for the duration of the read: an entry of the
bank records the range [(l, bs)] of the read, and holds [G] together with its guard
(and the later credits to open it). The physical lock states [σB] of the byte region
are those of the authoritative heap [σA] (the values [𝜙 𝛼] of the location rows) plus
the number of entries of the bank whose range contains the location ([bank_rel]); every
entry is a range that is being read in [σA] ([bank_wf]). A writer (which owns the
points-to of its range) learns that no entry overlaps its range by opening the guards
of the entries ([bbank_disj]): an overlapping entry would give a second edge from one
of its locations. *)

Definition bbankR Σ : cmra :=
  gmap_viewR nat (agreeR (prodO (leibnizO (loc * list abyte)) (laterO (iPropO Σ)))).

(** The range of [n] bytes at [l] contains [l']. *)
Definition in_rng (l : loc) (n : nat) (l' : loc) : Prop := ∃ i : nat, (i < n)%nat ∧ l' = l +ₗ i.
Global Instance in_rng_dec l n l' : Decision (in_rng l n l').
Proof.
  destruct (loc_range_dec l n l') as [[i [??]]|Hn]; [left; by exists i|].
  right. intros (i & ? & ?). by eapply Hn.
Qed.

(** The number of entries of the bank (with ranges [R]) whose range contains [l']. *)
Definition bcnt (R : gmap nat (loc * list abyte)) (l' : loc) : nat :=
  size (filter (λ kv : nat * (loc * list abyte), in_rng kv.2.1 (length kv.2.2) l') R).

Definition adj_ls (c : nat) (ls : lock_state) : lock_state :=
  match ls with RSt n => RSt (n + c) | WSt => WSt end.

(** The physical byte region [σB] is the authoritative one [σA] with the read counts of
    the bank added. *)
Definition bank_rel (R : gmap nat (loc * list abyte)) (σA σB : state') : Prop :=
  ∀ l', σB !! l' = (λ p, (adj_ls (bcnt R l') p.1, p.2)) <$> σA !! l'.

(** The range of each entry is being read, with its bytes. *)
Definition bank_wf (R : gmap nat (loc * list abyte)) (σA : state') : Prop :=
  ∀ i e, R !! i = Some e → mem_range is_reading σA e.1 e.2.

(** No entry overlaps the [n] bytes at [l]. *)
Definition bank_disj (R : gmap nat (loc * list abyte)) (l : loc) (n : nat) : Prop :=
  ∀ i e, R !! i = Some e → ∀ j : nat, (j < n)%nat → ¬ in_rng e.1 (length e.2) (l +ₗ j).

Section bank_defs.
  Context `{!heapGS Σ}.
  Context `{!invGS Σ}.

  Definition bbank_elt (r : loc * list abyte) (G : iProp Σ)
      : prodO (leibnizO (loc * list abyte)) (laterO (iPropO Σ)) := (r, Next G).

  Definition bbank_auth (M : gmap nat ((loc * list abyte) * iProp Σ)) : iProp Σ :=
    own heap_bbank_name (gmap_view_auth (DfracOwn 1)
      ((λ e, to_agree (bbank_elt e.1 e.2)) <$> M)).

  (** An entry holds [G], a guard of some [P] by [G], and the knowledge that [P] contains
      the edges from the locations of the range of the entry. *)
  Definition bbank_entry (e : (loc * list abyte) * iProp Σ) : iProp Σ :=
    e.2 ∗ ∃ P d, £d ∗ (e.2 &&{↑naN; d}&&> P) ∗
      □ (P -∗ ∃ cvs, ⌜length cvs = length e.1.2⌝ ∗
           ([∗ list] i ↦ cv ∈ cvs, bpt (inl (e.1.1 +ₗ i)) cv) ∗ cells_wit e.1.1 cvs).

  (** The ghost state of the byte region, at the physical byte region [σB]. *)
  Definition bytes_ctx (σB : state') : iProp Σ :=
    ∃ (𝛼 : bfull) (M : gmap nat ((loc * list abyte) * iProp Σ)),
      ⌜bank_rel (fst <$> M) (bphi 𝛼) σB⌝ ∗ ⌜bank_wf (fst <$> M) (bphi 𝛼)⌝ ∗
      bheap 𝛼 ∗ bbank_auth M ∗ ([∗ map] e ∈ M, bbank_entry e) ∗ cells_ctx 𝛼.

  (** The token of a guarded read in progress, of the bytes [bs] at [l], whose guard
      [G] is in the bank. *)
  Definition bread_tok (i : nat) (l : loc) (bs : list abyte) (G : iProp Σ) : iProp Σ :=
    own heap_bbank_name (gmap_view_frag i (DfracOwn 1) (to_agree (bbank_elt (l, bs) G))).
End bank_defs.

Section definitions.
  Context `{!heapGS Σ}.
  Context `{!invGS Σ}.
  Context `{!na_invG Σ}.
  Context `{!alc_logicG Σ}.
  
  Fixpoint inter (i0 : Z) (n : nat) : gmapR Z (exclR unitO) :=
    match n with O => ∅ | S n => <[i0 := Excl ()]>(inter (i0+1) n) end.

  Definition heap_freeable_def (l : loc) (q : Qp) (n: nat) : iProp Σ :=
    own heap_freeable_name (◯ {[ l.1 := (q, inter (l.2) n) ]}).
  Definition heap_freeable_aux : seal (@heap_freeable_def). Proof. by eexists. Qed.
  Definition heap_freeable := unseal heap_freeable_aux.
  Definition heap_freeable_eq : @heap_freeable = @heap_freeable_def :=
    seal_eq heap_freeable_aux.
  
  Definition heap_ato_ctx : iProp Σ := 
      na_invariants_fork.na_own atomic_threadpool ⊤ ∗ atomic_lock_ctr atomic_lock_ctr_name 0 ⊤.


  Definition heap_maps_ctx (σ : state') : iProp Σ := bytes_ctx σ.

  Definition heap_ctx (σ:state) : iProp Σ :=
    (∃ hF, heap_maps_ctx σ.1
         ∗ own heap_freeable_name (● hF)
         ∗ ⌜heap_freeable_rel σ hF⌝
         ∗ (match σ.2 with true => True | false => heap_ato_ctx end))%I.
         
End definitions.

Global Typeclasses Opaque heap_freeable.
Global Instance: Params (@heap_freeable) 5 := {}.

Notation "†{ q } l … n" := (heap_freeable l q n)
  (at level 20, q at level 50, format "†{ q } l … n") : bi_scope.
Notation "† l … n" := (heap_freeable l 1 n) (at level 20) : bi_scope.

Section heap.
  Context `{!heapGS Σ}.
  Context `{!invGS Σ}.
  Context `{!na_invG Σ}.
  Context `{!alc_logicG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : state.
  Implicit Types E : coPset.

  Global Instance heap_freeable_timeless q l n : Timeless (†{q}l…n).
  Proof. rewrite heap_freeable_eq /heap_freeable_def. apply _. Qed.

  (*Lemma heap_mapsto_agree l v1 v2 : l ↦ v1 ∗ l ↦ v2 ⊢ ⌜v1 = v2⌝.
  Proof.
    rewrite heap_mapsto_eq -own_op -auth_frag_op own_valid discrete_valid.
    eapply pure_elim; [done|]=> /auth_frag_valid /=.
    rewrite singleton_op -pair_op singleton_valid=> -[? /to_agree_op_inv_L->]; eauto.
  Qed.*)

  Lemma inter_lookup_Some i j (n : nat):
    i ≤ j < i+n → inter i n !! j = Excl' ().
  Proof.
    revert i. induction n as [|n IH]=>/= i; first lia.
    rewrite lookup_insert_Some. destruct (decide (i = j)); naive_solver lia.
  Qed.
  Lemma inter_lookup_None i j (n : nat):
    j < i ∨ i+n ≤ j → inter i n !! j = None.
  Proof.
    revert i. induction n as [|n IH]=>/= i; first by rewrite lookup_empty.
    rewrite lookup_insert_None. naive_solver lia.
  Qed.
  Lemma inter_op i n n' : inter i n ⋅ inter (i+n) n' ≡ inter i (n+n').
  Proof.
    intros j. rewrite lookup_op.
    destruct (decide (i ≤ j < i+n)); last destruct (decide (i+n ≤ j < i+n+n')).
    - by rewrite (inter_lookup_None (i+n) j n') ?inter_lookup_Some; try lia.
    - by rewrite (inter_lookup_None i j n) ?inter_lookup_Some; try lia.
    - by rewrite !inter_lookup_None; try lia.
  Qed.
  Lemma inter_valid i n : ✓ inter i n.
  Proof. revert i. induction n as [|n IH]=>i; first done. by apply insert_valid. Qed.

  Lemma heap_freeable_op_eq l q1 q2 n n' :
    †{q1}l…n ∗ †{q2}l+ₗ n … n' ⊣⊢ †{q1+q2}l…(n+n').
  Proof.
    by rewrite heap_freeable_eq /heap_freeable_def -own_op -auth_frag_op
      singleton_op -pair_op inter_op.
  Qed.

  (** Properties about heap_freeable_rel and heap_freeable *)
  Lemma heap_freeable_rel_None σ l hF :
    (∀ m : Z, σ.1 !! (l +ₗ m) = None) → heap_freeable_rel σ hF →
    hF !! l.1 = None.
  Proof.
    intros FRESH REL. apply eq_None_not_Some. intros [[q s] [Hsne REL']%REL].
    destruct (map_choose s) as [i []%REL'%not_eq_None_Some]; first done.
    move: (FRESH (i - l.2)). by rewrite /shift_loc Zplus_minus.
  Qed.

  Lemma heap_freeable_is_Some σ hF l n i :
    heap_freeable_rel σ hF →
    hF !! l.1 = Some (1%Qp, inter (l.2) n) →
    is_Some (σ.1 !! (l +ₗ i)) ↔ 0 ≤ i ∧ i < n.
  Proof.
    destruct l as [b j]; rewrite /shift_loc /=. intros REL Hl.
    destruct (REL b (1%Qp, inter j n)) as [_ ->]; simpl in *; auto.
    destruct (decide (0 ≤ i ∧ i < n)).
    - rewrite is_Some_alt inter_lookup_Some; lia.
    - rewrite is_Some_alt inter_lookup_None; lia.
  Qed.

  Lemma heap_freeable_rel_init_mem l h n σ:
    n ≠ O →
    (∀ m : Z, σ.1 !! (l +ₗ m) = None) →
    heap_freeable_rel σ h →
    heap_freeable_rel (init_mem l n $σ σ)
                      (<[l.1 := (1%Qp, inter (l.2) n)]> h).
  Proof.
    move=> Hvlnil FRESH REL blk qs /lookup_insert_Some [[<- <-]|[??]].
    - split.
      { destruct n as [|n]; simpl in *; [done|]. apply: insert_non_empty. }
      intros i. destruct (decide (l.2 ≤ i ∧ i < l.2 + n)).
      + rewrite inter_lookup_Some // lookup_init_mem; naive_solver.
      + rewrite inter_lookup_None; last lia. rewrite lookup_init_mem_ne /=; last lia.
        replace (l.1,i) with (l +ₗ (i - l.2)) by (rewrite /shift_loc; f_equal; lia).
        by rewrite FRESH !is_Some_alt.
    - destruct (REL blk qs) as [? Hs]; auto.
      split; [done|]=> i. by rewrite -Hs lookup_init_mem_ne; last auto.
  Qed.

  Lemma heap_freeable_rel_free_mem σ hF n l :
    hF !! l.1 = Some (1%Qp, inter (l.2) n) →
    heap_freeable_rel σ hF →
    heap_freeable_rel (free_mem l n $σ σ) (delete (l.1) hF).
  Proof.
    intros Hl REL b qs; rewrite lookup_delete_Some=> -[NEQ ?].
    destruct (REL b qs) as [? REL']; auto.
    split; [done|]=> i. by rewrite -REL' lookup_free_mem_ne.
  Qed.

  Lemma heap_freeable_rel_stable σ h l p :
    heap_freeable_rel σ h → is_Some (σ.1 !! l) →
    heap_freeable_rel (<[l := p]>σ.1, σ.2) h.
  Proof.
    intros REL Hσ blk qs Hqs. destruct (REL blk qs) as [? REL']; first done.
    split; [done|]=> i. rewrite -REL' lookup_insert_is_Some.
    destruct (decide (l = (blk, i))); naive_solver.
  Qed.
  
  Lemma lookup_init_mem_prev l n σ :
      init_mem (l +ₗ 1) n σ.1 !! l = σ.1 !! l.
  Proof.
      rewrite lookup_init_mem_ne /=; first by done. right. left. lia.
  Qed.

End heap.


Section bytes.
  Context `{!heapGS Σ}.
  Implicit Types σB : gmap loc (lock_state * abyte).
  Implicit Types bs : list abyte.
  Implicit Types 𝛼 : bfull.

  (** ** Structural lemmas *)
  Global Instance heap_mapsto_st_timeless st l b : Timeless (heap_mapsto_st st l b).
  Proof. rewrite /heap_mapsto_st /bpt. apply _. Qed.

  Global Instance heap_mapsto_bytes_timeless l bs : Timeless (l ↦b bs).
  Proof. rewrite heap_mapsto_bytes_eq /heap_mapsto_bytes_def /heap_mapsto_st_vec. apply _. Qed.

  Lemma heap_mapsto_bytes_nil l : l ↦b [] ⊣⊢ True.
  Proof. by rewrite heap_mapsto_bytes_eq. Qed.

  Lemma heap_mapsto_st_vec_app st l bs1 bs2 :
    heap_mapsto_st_vec st l (bs1 ++ bs2) ⊣⊢
    heap_mapsto_st_vec st l bs1 ∗ heap_mapsto_st_vec st (l +ₗ length bs1) bs2.
  Proof.
    rewrite /heap_mapsto_st_vec big_sepL_app.
    do 2 f_equiv. intros k b. by rewrite shift_loc_assoc_nat.
  Qed.

  Lemma heap_mapsto_st_vec_cons st l b bs :
    heap_mapsto_st_vec st l (b :: bs) ⊣⊢
    heap_mapsto_st st l b ∗ heap_mapsto_st_vec st (l +ₗ 1) bs.
  Proof.
    rewrite (heap_mapsto_st_vec_app _ _ [b] bs) /heap_mapsto_st_vec /=.
    by rewrite shift_loc_0 right_id.
  Qed.

  Lemma heap_mapsto_bytes_app l bs1 bs2 :
    l ↦b (bs1 ++ bs2) ⊣⊢ l ↦b bs1 ∗ (l +ₗ length bs1) ↦b bs2.
  Proof. rewrite heap_mapsto_bytes_eq. apply heap_mapsto_st_vec_app. Qed.

  Lemma heap_mapsto_bytes_cons l b bs :
    l ↦b (b :: bs) ⊣⊢ l ↦b [b] ∗ (l +ₗ 1) ↦b bs.
  Proof. by rewrite (heap_mapsto_bytes_app l [b] bs). Qed.

  Lemma heap_mapsto_bytes_st_vec l bs : l ↦b bs ⊣⊢ heap_mapsto_st_vec (RSt 0) l bs.
  Proof. by rewrite heap_mapsto_bytes_eq. Qed.

  Lemma heap_mapsto_st_excl st st' l b b' :
    heap_mapsto_st st l b -∗ heap_mapsto_st st' l b' -∗ False.
  Proof. apply fpt_excl. Qed.

  (** ** Rows of the byte region *)

  (** Two full maps have the same rows with cells. The operations on locations without
      cells (reads, writes, allocation and deallocation) preserve the rows with cells. *)
  Definition rows_cells_eq 𝛼 𝛼' : Prop :=
    ∀ k cs v, cs ≠ [] → 𝛼 !! k = Some (cs, v) ↔ 𝛼' !! k = Some (cs, v).

  Lemma rows_cells_eq_refl 𝛼 : rows_cells_eq 𝛼 𝛼.
  Proof. done. Qed.
  Lemma rows_cells_eq_trans 𝛼1 𝛼2 𝛼3 :
    rows_cells_eq 𝛼1 𝛼2 → rows_cells_eq 𝛼2 𝛼3 → rows_cells_eq 𝛼1 𝛼3.
  Proof. intros H1 H2 k cs v ?. by rewrite H1 // H2. Qed.
  Lemma rows_cells_eq_insert_plain 𝛼 l v :
    (∀ cs v0, 𝛼 !! inl l = Some (cs, v0) → cs = []) →
    rows_cells_eq 𝛼 (<[inl l := ([], v)]> 𝛼).
  Proof.
    intros Hl k cs v' Hcs. destruct (decide (k = inl l)) as [->|].
    - rewrite lookup_insert. split; [intros Hk; by rewrite (Hl _ _ Hk) in Hcs|by intros [= <- _]].
    - by rewrite lookup_insert_ne.
  Qed.
  Lemma rows_cells_eq_delete_plain 𝛼 l :
    (∀ cs v0, 𝛼 !! inl l = Some (cs, v0) → cs = []) →
    rows_cells_eq 𝛼 (delete (inl l) 𝛼).
  Proof.
    intros Hl k cs v' Hcs. destruct (decide (k = inl l)) as [->|].
    - rewrite lookup_delete. split; [intros Hk; by rewrite (Hl _ _ Hk) in Hcs|done].
    - by rewrite lookup_delete_ne.
  Qed.

  (** ** Single locations *)
  Lemma heap_mapsto_st_lookup 𝛼 l ls b :
    bheap 𝛼 -∗ heap_mapsto_st ls l b -∗ ⌜𝛼 !! inl l = Some ([], (ls, b))⌝.
  Proof. iIntros "H● H◯". iApply (fheap_fpt with "H● H◯"). Qed.

  Lemma heap_mapsto_st_lookup_phi 𝛼 l ls b :
    bheap 𝛼 -∗ heap_mapsto_st ls l b -∗ ⌜bphi 𝛼 !! l = Some (ls, b)⌝.
  Proof.
    iIntros "H● H◯". iDestruct (heap_mapsto_st_lookup with "H● H◯") as %Hl.
    iPureIntro. by rewrite phi_lookup Hl.
  Qed.

  Lemma heap_mapsto_st_update 𝛼 l ls b ls' b' :
    bheap 𝛼 -∗ heap_mapsto_st ls l b ==∗
      ⌜𝛼 !! inl l = Some ([], (ls, b))⌝ ∗
      bheap (<[inl l := ([], (ls', b'))]> 𝛼) ∗ heap_mapsto_st ls' l b'.
  Proof.
    iIntros "H● H◯". iDestruct (heap_mapsto_st_lookup with "H● H◯") as %Hl.
    iMod (fcmap_write_loc with "H● H◯") as "[$ $]"; [done|done|]. done.
  Qed.

  Lemma heap_bytes_alloc_vs 𝛼 l b :
    𝛼 !! inl l = None →
    bheap 𝛼 ==∗ bheap (<[inl l := ([], (RSt 0, b))]> 𝛼) ∗ heap_mapsto_st (RSt 0) l b.
  Proof. iIntros (Hl) "H●". by iApply fcmap_alloc. Qed.

  Lemma heap_bytes_dealloc_vs 𝛼 l b :
    bheap 𝛼 -∗ heap_mapsto_st (RSt 0) l b ==∗
    ⌜𝛼 !! inl l = Some ([], (RSt 0, b))⌝ ∗ bheap (delete (inl l) 𝛼).
  Proof. iIntros "H● H◯". by iApply (fcmap_delete with "H● H◯"). Qed.

  Lemma alter_insert_Some {A} (m : gmap loc A) l (f : A → A) x :
    m !! l = Some x → alter f l m = <[l := f x]> m.
  Proof.
    intros Hl. apply map_eq. intros l'. destruct (decide (l = l')) as [<-|].
    - by rewrite lookup_alter lookup_insert Hl.
    - by rewrite lookup_alter_ne // lookup_insert_ne.
  Qed.

  (** ** Ranges *)

  (** Set the lock states of the [bs] at [l] to [st], and their bytes to [bs]. *)
  Fixpoint mem_set (st : lock_state) (l : loc) (bs : list abyte) (σ : state') : state' :=
    match bs with
    | [] => σ
    | b :: bs => <[l:=(st, b)]>(mem_set st (l +ₗ 1) bs σ)
    end.

  Lemma mem_set_write l bs σ : mem_set (RSt 0) l bs σ = mem_write l bs σ.
  Proof. revert l. induction bs as [|b bs IH]; intros l; [done|]. by rewrite /= IH. Qed.

  Lemma lookup_mem_set_out st l bs σ l' :
    (∀ i : nat, (i < length bs)%nat → l' ≠ l +ₗ i) → mem_set st l bs σ !! l' = σ !! l'.
  Proof.
    revert l. induction bs as [|b bs IH]; intros l Hl'; simpl; [done|].
    rewrite lookup_insert_ne; last first.
    { intros ->. apply (Hl' 0%nat); [simpl; lia|]. by rewrite shift_loc_0. }
    apply IH. intros i ?. rewrite -shift_loc_S. apply Hl'. simpl. lia.
  Qed.

  Lemma mem_set_alter f st l bs σ :
    mem_range (.= st) σ l bs → mem_alter f l (length bs) σ = mem_set (f st) l bs σ.
  Proof.
    revert l. induction bs as [|b bs IH]; intros l; [done|]. intros [(ls & Hl & ->) Hr].
    rewrite /= IH // (alter_insert_Some _ _ _ (st, b)) //.
    rewrite lookup_mem_set_out //. intros i Hi. apply shift_loc_ne_S.
  Qed.

  Lemma heap_st_vec_lookup 𝛼 st l bs :
    bheap 𝛼 -∗ heap_mapsto_st_vec st l bs -∗ ⌜mem_range (.= st) (bphi 𝛼) l bs⌝.
  Proof.
    iInduction bs as [|b bs] "IH" forall (l); iIntros "H● Hbs"; [done|].
    rewrite heap_mapsto_st_vec_cons. iDestruct "Hbs" as "[Hb Hbs]".
    iDestruct (heap_mapsto_st_lookup_phi with "H● Hb") as %Hl.
    iDestruct ("IH" with "H● Hbs") as %Hr. iPureIntro. split; [|done]. by eexists.
  Qed.

  Lemma heap_st_vec_set 𝛼 st st' l bs bs' :
    length bs' = length bs →
    bheap 𝛼 -∗ heap_mapsto_st_vec st l bs ==∗ ∃ 𝛼',
      ⌜mem_range (.= st) (bphi 𝛼) l bs ∧ bphi 𝛼' = mem_set st' l bs' (bphi 𝛼) ∧
        rows_cells_eq 𝛼 𝛼'⌝ ∗
      bheap 𝛼' ∗ heap_mapsto_st_vec st' l bs'.
  Proof.
    iInduction bs as [|b bs] "IH" forall (l bs' 𝛼); iIntros (Hlen) "H● Hbs";
      destruct bs' as [|b' bs']; try done.
    { iModIntro. iExists 𝛼. iFrame. rewrite /heap_mapsto_st_vec. iSplit; [iPureIntro; done|done]. }
    rewrite !heap_mapsto_st_vec_cons. iDestruct "Hbs" as "[Hb Hbs]".
    iDestruct (heap_mapsto_st_lookup_phi with "H● Hb") as %Hl0.
    iMod ("IH" $! _ bs' with "[] H● Hbs") as (𝛼1) "([%Hr [%H𝛼1 %Hc1]] & H● & Hbs)";
      [by simplify_eq/=|].
    iMod (heap_mapsto_st_update _ _ _ _ st' b' with "H● Hb") as "(%Hl1 & H● & Hb)".
    iModIntro. iExists _. rewrite (heap_mapsto_st_vec_cons st').
    iFrame "H● Hb Hbs". iPureIntro. split_and!.
    - split; [|done]. by eexists.
    - by rewrite phi_insert_loc H𝛼1.
    - eapply rows_cells_eq_trans; [done|]. apply rows_cells_eq_insert_plain.
      rewrite Hl1. by intros ?? [= <- _].
  Qed.

  (** Allocation and deallocation of single locations, with [bphi]. *)
  Lemma heap_bytes_alloc_vs' 𝛼 l b :
    bphi 𝛼 !! l = None →
    bheap 𝛼 ==∗ ∃ 𝛼', ⌜bphi 𝛼' = <[l:=(RSt 0, b)]> (bphi 𝛼) ∧ rows_cells_eq 𝛼 𝛼'⌝ ∗
      bheap 𝛼' ∗ heap_mapsto_st (RSt 0) l b.
  Proof.
    iIntros (Hl) "H●". rewrite phi_lookup in Hl.
    have Hl' : 𝛼 !! inl l = None by destruct (𝛼 !! inl l) as [[]|].
    iMod (heap_bytes_alloc_vs with "H●") as "[H● $]"; [done|]. iModIntro. iExists _.
    iFrame. iPureIntro. split; [by rewrite phi_insert_loc|].
    apply rows_cells_eq_insert_plain. by rewrite Hl'.
  Qed.

  Lemma heap_bytes_dealloc_vs' 𝛼 l b :
    bheap 𝛼 -∗ heap_mapsto_st (RSt 0) l b ==∗ ∃ 𝛼',
    ⌜bphi 𝛼 !! l = Some (RSt 0, b) ∧ bphi 𝛼' = delete l (bphi 𝛼) ∧ rows_cells_eq 𝛼 𝛼'⌝ ∗
      bheap 𝛼'.
  Proof.
    iIntros "H● H◯". iMod (heap_bytes_dealloc_vs with "H● H◯") as "[%Hl H●]".
    iModIntro. iExists _. iFrame. iPureIntro. split_and!.
    - by rewrite phi_lookup Hl.
    - by rewrite phi_delete_loc.
    - apply rows_cells_eq_delete_plain. rewrite Hl. by intros ?? [= <- _].
  Qed.

  Lemma heap_freeable_rel_dom (σ σ' : state) hF :
    (∀ l, is_Some (σ.1 !! l) ↔ is_Some (σ'.1 !! l)) →
    heap_freeable_rel σ hF → heap_freeable_rel σ' hF.
  Proof.
    intros Hdom REL blk qs Hqs. destruct (REL blk qs Hqs) as [? REL'].
    split; [done|]. intros i. by rewrite -Hdom.
  Qed.

  Lemma is_Some_mem_write' (σ : state') l bs l' :
    (∀ i : nat, (i < length bs)%nat → is_Some (σ !! (l +ₗ i))) →
    is_Some (mem_write l bs σ !! l') ↔ is_Some (σ !! l').
  Proof.
    intros Hbs. destruct (loc_range_dec l (length bs) l') as [[i [Hi ->]]|Hout].
    - destruct (lookup_lt_is_Some_2 bs i) as [b' Hb']; [lia|].
      rewrite (lookup_mem_write_in _ _ _ _ b') //. split; [intros _; by apply Hbs|eauto].
    - by rewrite lookup_mem_write_out.
  Qed.

  Lemma is_Some_mem_write P (σ : state') l bs0 bs l' :
    mem_range P σ l bs0 → length bs = length bs0 →
    is_Some (mem_write l bs σ !! l') ↔ is_Some (σ !! l').
  Proof.
    intros Hbs Hlen. destruct (loc_range_dec l (length bs0) l') as [[i [Hi ->]]|Hout].
    - destruct (mem_range_lookup_1 _ _ _ _ i Hbs Hi) as (ls & b & Hl & _).
      destruct (lookup_lt_is_Some_2 bs i) as [b' Hb']; [lia|].
      rewrite (lookup_mem_write_in _ _ _ _ b') //; rewrite Hl; split; eauto.
    - rewrite lookup_mem_write_out //. by rewrite Hlen.
  Qed.

  Lemma mem_alter_mem_write f l bs σB :
    mem_write l bs (mem_alter f l (length bs) σB) = mem_write l bs σB.
  Proof.
    apply map_eq. intros l'. destruct (loc_range_dec l (length bs) l') as [[i [Hi ->]]|Hout].
    - destruct (lookup_lt_is_Some_2 bs i) as [b Hb]; [lia|].
      by rewrite !(lookup_mem_write_in _ _ _ _ b).
    - by rewrite !lookup_mem_write_out // lookup_mem_alter_out.
  Qed.
End bytes.

(** * The bank of guarded reads *)
Section bank_pure.
  Implicit Types (R : gmap nat (loc * list abyte)) (σA σB : state') (i : nat)
    (e : loc * list abyte) (bs : list abyte).

  Lemma adj_ls_0 ls : adj_ls 0 ls = ls.
  Proof. destruct ls; by rewrite /= ?Nat.add_0_r. Qed.

  Lemma bcnt_insert R i e l' :
    R !! i = None →
    bcnt (<[i:=e]> R) l' = ((if decide (in_rng e.1 (length e.2) l') then 1 else 0) + bcnt R l')%nat.
  Proof.
    intros Hi. rewrite /bcnt map_filter_insert /=. case_decide.
    - rewrite map_size_insert_None //. apply map_lookup_filter_None_2. by left.
    - by rewrite delete_notin.
  Qed.

  Lemma bcnt_delete R i e l' :
    R !! i = Some e →
    bcnt R l' = ((if decide (in_rng e.1 (length e.2) l') then 1 else 0) + bcnt (delete i R) l')%nat.
  Proof.
    intros Hi. rewrite -{1}(insert_delete R i e) //. apply bcnt_insert. apply lookup_delete.
  Qed.

  Lemma bcnt_0 R l' : (∀ i e, R !! i = Some e → ¬ in_rng e.1 (length e.2) l') → bcnt R l' = 0%nat.
  Proof.
    intros H. rewrite /bcnt. apply map_size_empty_iff, map_filter_empty_iff.
    intros i e Hi. by apply (H i e).
  Qed.

  Lemma bank_disj_bcnt R l n (j : nat) : bank_disj R l n → (j < n)%nat → bcnt R (l +ₗ j) = 0%nat.
  Proof. intros H Hj. apply bcnt_0. intros i e Hi. by apply (H i e). Qed.

  Lemma bank_wf_bcnt R σA l : bank_wf R σA → σA !! l = None → bcnt R l = 0%nat.
  Proof.
    intros Hwf Hl. apply bcnt_0. intros i e Hi (j & Hj & ->).
    destruct (mem_range_lookup_1 _ _ _ _ j (Hwf i e Hi) Hj) as (? & ? & Hl' & _).
    by rewrite Hl' in Hl.
  Qed.

  (** ** Ranges of [σB] from ranges of [σA] *)
  Lemma bank_rel_reading R σA σB l bs :
    bank_rel R σA σB → mem_range is_reading σA l bs → mem_range is_reading σB l bs.
  Proof.
    rewrite !mem_range_lookup. intros Hr H i b Hb. destruct (H i b Hb) as (ls & Hl & [n ->]).
    rewrite Hr Hl /=. eexists. split; [done|]. by eexists.
  Qed.

  Lemma bank_rel_reading_S R σA σB l bs :
    bank_rel R σA σB → mem_range is_reading_S σA l bs → mem_range is_reading_S σB l bs.
  Proof.
    rewrite !mem_range_lookup. intros Hr H i b Hb. destruct (H i b Hb) as (ls & Hl & [n ->]).
    rewrite Hr Hl /=. eexists. split; [done|]. by eexists.
  Qed.

  Lemma bank_rel_disj P R σA σB l bs :
    bank_rel R σA σB → bank_disj R l (length bs) →
    mem_range P σA l bs → mem_range P σB l bs.
  Proof.
    rewrite !mem_range_lookup. intros Hr Hd H i b Hb. destruct (H i b Hb) as (ls & Hl & HP).
    rewrite Hr Hl /= (bank_disj_bcnt _ _ _ i Hd); [|by eapply lookup_lt_Some].
    rewrite adj_ls_0. eauto.
  Qed.

  (** ** Updates *)
  Lemma bank_rel_mem_alter Q f R σA σB l bs :
    (∀ c ls, Q ls → f (adj_ls c ls) = adj_ls c (f ls)) →
    bank_rel R σA σB → mem_range Q σA l bs →
    bank_rel R (mem_alter f l (length bs) σA) (mem_alter f l (length bs) σB).
  Proof.
    intros Hf Hr HQ l'. destruct (loc_range_dec l (length bs) l') as [[i [Hi ->]]|Hout].
    - rewrite !lookup_mem_alter_in // Hr.
      destruct (mem_range_lookup_1 _ _ _ _ i HQ Hi) as (ls & b & Hl & HQl & _).
      rewrite Hl /= Hf //.
    - by rewrite !lookup_mem_alter_out.
  Qed.

  Lemma bank_rel_mem_alter_inc R σA σB l n :
    bank_rel R σA σB → bank_rel R (mem_alter ls_inc l n σA) (mem_alter ls_inc l n σB).
  Proof.
    intros Hr l'. destruct (loc_range_dec l n l') as [[i [Hi ->]]|Hout].
    - rewrite !lookup_mem_alter_in // Hr. destruct (σA !! (l +ₗ i)) as [[[]]|]; done.
    - by rewrite !lookup_mem_alter_out.
  Qed.

  Lemma bank_rel_mem_alter_wst R σA σB l n :
    bank_rel R σA σB →
    bank_rel R (mem_alter (λ _, WSt) l n σA) (mem_alter (λ _, WSt) l n σB).
  Proof.
    intros Hr l'. destruct (loc_range_dec l n l') as [[i [Hi ->]]|Hout].
    - rewrite !lookup_mem_alter_in // Hr. destruct (σA !! (l +ₗ i)) as [[[]]|]; done.
    - by rewrite !lookup_mem_alter_out.
  Qed.

  Lemma bank_rel_mem_alter_dec R σA σB l bs :
    bank_rel R σA σB → mem_range is_reading_S σA l bs →
    bank_rel R (mem_alter ls_dec l (length bs) σA) (mem_alter ls_dec l (length bs) σB).
  Proof.
    intros. eapply bank_rel_mem_alter; [|done..]. intros c ls [n ->]. done.
  Qed.

  Lemma bank_rel_mem_write R σA σB l bs bs' :
    length bs' = length bs →
    bank_rel R σA σB → bank_disj R l (length bs) →
    bank_rel R (mem_write l bs' σA) (mem_write l bs' σB).
  Proof.
    intros Hlen Hr Hd l'. destruct (loc_range_dec l (length bs) l') as [[i [Hi ->]]|Hout].
    - destruct (lookup_lt_is_Some_2 bs' i) as [b' Hb']; [lia|].
      rewrite !(lookup_mem_write_in _ _ _ _ b') // (bank_disj_bcnt _ _ _ i Hd) //.
    - rewrite !lookup_mem_write_out ?Hlen //.
  Qed.

  Lemma bank_rel_insert R σA σB l p :
    bank_rel R σA σB → bcnt R l = 0%nat → bank_rel R (<[l:=p]> σA) (<[l:=p]> σB).
  Proof.
    intros Hr H0 l'. destruct (decide (l = l')) as [<-|].
    - rewrite !lookup_insert /= H0 adj_ls_0. by destruct p.
    - rewrite !lookup_insert_ne //.
  Qed.

  Lemma bank_rel_delete R σA σB l :
    bank_rel R σA σB → bank_rel R (delete l σA) (delete l σB).
  Proof.
    intros Hr l'. destruct (decide (l = l')) as [<-|].
    - by rewrite !lookup_delete.
    - rewrite !lookup_delete_ne //.
  Qed.

  Lemma bank_rel_lookup_None R σA σB l : bank_rel R σA σB → σB !! l = None → σA !! l = None.
  Proof. intros Hr. rewrite Hr. by destruct (σA !! l). Qed.

  Lemma bank_rel_add R σA σB i l bs :
    bank_rel R σA σB → R !! i = None → mem_range is_reading σA l bs →
    bank_rel (<[i:=(l, bs)]> R) σA (mem_alter ls_inc l (length bs) σB).
  Proof.
    intros Hr Hi Hrd l'. rewrite (bcnt_insert _ _ _ _ Hi) /=.
    destruct (loc_range_dec l (length bs) l') as [[j [Hj ->]]|Hout].
    - rewrite decide_True; [|by exists j].
      destruct (mem_range_lookup_1 _ _ _ _ j Hrd Hj) as (ls & b & Hl & [n ->] & _).
      rewrite lookup_mem_alter_in // Hr Hl /=. do 3 f_equal. lia.
    - rewrite decide_False; [|intros (j & ? & ?); by eapply Hout].
      by rewrite lookup_mem_alter_out.
  Qed.

  Lemma bank_rel_remove R σA σB i l bs :
    bank_rel R σA σB → R !! i = Some (l, bs) → mem_range is_reading σA l bs →
    bank_rel (delete i R) σA (mem_alter ls_dec l (length bs) σB).
  Proof.
    intros Hr Hi Hrd l'. move: (Hr l'). rewrite (bcnt_delete _ _ _ l' Hi) /=. intros Hrl.
    destruct (loc_range_dec l (length bs) l') as [[j [Hj ->]]|Hout].
    - rewrite decide_True in Hrl; [|by exists j].
      destruct (mem_range_lookup_1 _ _ _ _ j Hrd Hj) as (ls & b & Hl & [n ->] & _).
      rewrite lookup_mem_alter_in // Hrl Hl /=. do 3 f_equal. lia.
    - rewrite decide_False in Hrl; [|intros (j & ? & ?); by eapply Hout].
      by rewrite lookup_mem_alter_out.
  Qed.

  (** ** Well-formedness *)
  Lemma bank_wf_mem_alter f R σA l n :
    (∀ ls, is_reading ls → is_reading (f ls)) →
    bank_wf R σA → bank_wf R (mem_alter f l n σA).
  Proof.
    intros Hf Hwf i e Hi. move: (Hwf i e Hi). rewrite !mem_range_lookup. intros H j b Hb.
    destruct (H j b Hb) as (ls & Hl & Hrd). destruct (loc_range_dec l n (e.1 +ₗ j)) as [[k [Hk Heq]]|Hout].
    - rewrite Heq lookup_mem_alter_in // -Heq Hl /=. eauto.
    - rewrite lookup_mem_alter_out //. eauto.
  Qed.

  Lemma bank_wf_mem_alter_disj f R σA l n :
    bank_disj R l n → bank_wf R σA → bank_wf R (mem_alter f l n σA).
  Proof.
    intros Hd Hwf i e Hi. move: (Hwf i e Hi). rewrite !mem_range_lookup. intros H j b Hb.
    destruct (H j b Hb) as (ls & Hl & Hrd). rewrite lookup_mem_alter_out //.
    - eauto.
    - intros k Hk Heq. apply (Hd i e Hi k Hk). exists j. split; [by eapply lookup_lt_Some|done].
  Qed.

  Lemma bank_wf_mem_write R σA l bs :
    bank_disj R l (length bs) → bank_wf R σA → bank_wf R (mem_write l bs σA).
  Proof.
    intros Hd Hwf i e Hi. move: (Hwf i e Hi). rewrite !mem_range_lookup. intros H j b Hb.
    destruct (H j b Hb) as (ls & Hl & Hrd). rewrite lookup_mem_write_out //.
    - eauto.
    - intros k Hk Heq. apply (Hd i e Hi k Hk). exists j. split; [by eapply lookup_lt_Some|done].
  Qed.

  Lemma bank_wf_insert R σA l p : σA !! l = None → bank_wf R σA → bank_wf R (<[l:=p]> σA).
  Proof.
    intros Hl Hwf i e Hi. move: (Hwf i e Hi). rewrite !mem_range_lookup. intros H j b Hb.
    destruct (H j b Hb) as (ls & Hl' & Hrd). rewrite lookup_insert_ne; [eauto|].
    intros ->. by rewrite Hl in Hl'.
  Qed.

  Lemma bank_wf_delete R σA l :
    bank_disj R l 1 → bank_wf R σA → bank_wf R (delete l σA).
  Proof.
    intros Hd Hwf i e Hi. move: (Hwf i e Hi). rewrite !mem_range_lookup. intros H j b Hb.
    destruct (H j b Hb) as (ls & Hl' & Hrd). rewrite lookup_delete_ne; [eauto|].
    intros Heq. apply (Hd i e Hi 0%nat); [lia|]. rewrite shift_loc_0 Heq.
    exists j. split; [by eapply lookup_lt_Some|done].
  Qed.

  Lemma bank_wf_add R σA i l bs :
    mem_range is_reading σA l bs → bank_wf R σA → bank_wf (<[i:=(l, bs)]> R) σA.
  Proof.
    intros Hrd Hwf i' e. destruct (decide (i = i')) as [<-|].
    - rewrite lookup_insert. by intros [= <-].
    - rewrite lookup_insert_ne //. apply Hwf.
  Qed.

  Lemma bank_wf_remove R σA i : bank_wf R σA → bank_wf (delete i R) σA.
  Proof.
    intros Hwf i' e. destruct (decide (i = i')) as [<-|].
    - by rewrite lookup_delete.
    - rewrite lookup_delete_ne //. apply Hwf.
  Qed.

  Lemma bank_disj_tail R l b bs :
    bank_disj R l (length (b :: bs)) → bank_disj R (l +ₗ 1) (length bs).
  Proof.
    intros H i e Hi j Hj. rewrite -shift_loc_S. apply (H i e Hi (S j)). simpl. lia.
  Qed.

  Lemma bank_disj_head R l b bs : bank_disj R l (length (b :: bs)) → bank_disj R l 1.
  Proof. intros H i e Hi j Hj. apply (H i e Hi j). simpl. lia. Qed.
End bank_pure.

Section cells_rows.
  Context `{!heapGS Σ}.
  Context `{!invGS Σ}.

  Lemma cells_ctx_rows_eq 𝛼 𝛼' : rows_cells_eq 𝛼 𝛼' → cells_ctx 𝛼 -∗ cells_ctx 𝛼'.
  Proof.
    iIntros (Heq) "(%R & %ρ & %NC & %NS & %CW & Hreg & Hdyn & Hnc & Hns & Hcw & [%Hwf [%Hl1 %Hl2]] & HR & HNS & Hcwe & Hρ)".
    iExists R, ρ, NC, NS, CW. iFrame. iPureIntro. split; [done|]. split.
    - intros k cs v c Hk Hc. apply (Hl1 k cs v c); [|done]. apply Heq; [|done].
      intros ->. by apply not_elem_of_nil in Hc.
    - intros g k m cs Hg HR i c Hc. destruct (Hl2 g k m cs Hg HR i c Hc) as (cells & v & Hr & Hcc).
      exists cells, v. split; [|done]. apply Heq; [|done]. intros ->. by apply not_elem_of_nil in Hcc.
  Qed.
End cells_rows.

Section bank.
  Context `{!heapGS Σ}.
  Context `{!invGS Σ}.
  Implicit Types (σA σB : state') (bs : list abyte) (𝛼 : bfull).
  Implicit Types M : gmap nat ((loc * list abyte) * iProp Σ).

  (** An entry of the bank does not overlap the bytes owned by a writer. *)
  Lemma bbank_entry_disj E e st l bs :
    ↑naN ⊆ E →
    bbank_entry e -∗ heap_mapsto_st_vec st l bs ={E}=∗
      ⌜∀ j : nat, (j < length bs)%nat → ¬ in_rng e.1.1 (length e.1.2) (l +ₗ j)⌝ ∗
      bbank_entry e ∗ heap_mapsto_st_vec st l bs.
  Proof.
    iIntros (?) "Entry Hbs".
    destruct (decide (Exists (λ j : nat, in_rng e.1.1 (length e.1.2) (l +ₗ j)) (seq 0 (length bs))))
      as [Hex|Hnex]; last first.
    { iModIntro. iFrame. iPureIntro. intros j Hj Hin. apply Hnex.
      apply Exists_exists. exists j. split; [apply elem_of_seq; lia|done]. }
    apply Exists_exists in Hex as (j & Hj%elem_of_seq & (k & Hk & Heq)).
    iDestruct "Entry" as "(G & %P & %d & £ & #Guard & #HP)".
    iMod (guards_open_later with "Guard G") as "Open"; [done|].
    iMod (lc_fupd_elim_laterN with "£ Open") as ">[P _]".
    iDestruct ("HP" with "P") as (cvs Hlen') "[Pt _]".
    destruct (lookup_lt_is_Some_2 cvs k) as [cv Hcv]; [lia|].
    destruct (lookup_lt_is_Some_2 bs j) as [b Hb]; [lia|].
    iDestruct (big_sepL_lookup with "Pt") as "Pt"; [done|].
    iDestruct (big_sepL_lookup with "Hbs") as "Hbs"; [done|].
    iEval (rewrite -Heq) in "Pt". iDestruct (fpt_excl with "Hbs Pt") as "[]".
  Qed.

  Lemma bbank_disj E M st l bs :
    ↑naN ⊆ E →
    ([∗ map] e ∈ M, bbank_entry e) -∗ heap_mapsto_st_vec st l bs ={E}=∗
      ⌜bank_disj (fst <$> M) l (length bs)⌝ ∗
      ([∗ map] e ∈ M, bbank_entry e) ∗ heap_mapsto_st_vec st l bs.
  Proof.
    iIntros (?). iInduction M as [|i e M Hi] "IH" using map_ind; iIntros "Entries Hbs".
    { iFrame. iPureIntro. intros i e. by rewrite fmap_empty lookup_empty. }
    rewrite big_sepM_insert //. iDestruct "Entries" as "[Entry Entries]".
    iMod (bbank_entry_disj with "Entry Hbs") as "(%H1 & Entry & Hbs)"; [done|].
    iMod ("IH" with "Entries Hbs") as "(%H2 & Entries & $)". iFrame. iPureIntro.
    intros i' e'. rewrite fmap_insert. destruct (decide (i = i')) as [<-|].
    - rewrite lookup_insert. intros [= <-]. apply H1.
    - rewrite lookup_insert_ne //. apply H2.
  Qed.

  (** ** The ghost state of the byte region *)
  Lemma bytes_ctx_empty : bheap ∅ -∗ bbank_auth ∅ -∗
    ghost_map_auth heap_greg_name 1 (∅ : gmap positive (mty * list positive)) -∗
    ghost_map_auth heap_gdyn_name 1 (∅ : gmap positive FValue) -∗
    ghost_map_auth heap_gnc_name 1 (∅ : gmap positive ()) -∗
    ghost_map_auth heap_gnest_name 1 (∅ : gmap (positive * positive * nat) ()) -∗
    cwbank_auth ∅ -∗ bytes_ctx ∅.
  Proof.
    iIntros "H● Hbank Hreg Hdyn Hnc Hns Hcw". iExists ∅, ∅.
    rewrite !big_sepM_empty phi_empty. iFrame "H● Hbank".
    iSplit. { iPureIntro. intros l. by rewrite fmap_empty !lookup_empty. }
    iSplit. { iPureIntro. intros i e. by rewrite fmap_empty lookup_empty. }
    iSplit; [done|]. iExists ∅, ∅, ∅, ∅, ∅. iFrame. rewrite !big_sepM_empty fmap_empty.
    iPureIntro. split_and!; try done; set_solver.
  Qed.

  Lemma bytes_ctx_lookup σB l bs :
    bytes_ctx σB -∗ l ↦b bs -∗ ⌜mem_range is_reading σB l bs⌝.
  Proof.
    iIntros "(%𝛼 & %M & %Hr & %Hwf & H● & Hbank & Entries & Cells) Hbs".
    rewrite heap_mapsto_bytes_st_vec.
    iDestruct (heap_st_vec_lookup with "H● Hbs") as %Hrd. iPureIntro.
    eapply bank_rel_reading; [done|]. eapply mem_range_impl; [|done]. intros ? ->. by eexists.
  Qed.

  Lemma bytes_ctx_lookup_reading σB l bs :
    bytes_ctx σB -∗ heap_mapsto_st_vec (RSt 1) l bs -∗ ⌜mem_range is_reading_S σB l bs⌝.
  Proof.
    iIntros "(%𝛼 & %M & %Hr & %Hwf & H● & Hbank & Entries & Cells) Hbs".
    iDestruct (heap_st_vec_lookup with "H● Hbs") as %Hrd. iPureIntro.
    eapply bank_rel_reading_S; [done|]. eapply mem_range_impl; [|done]. intros ? ->. by eexists.
  Qed.

  Lemma bytes_ctx_lookup_1 E σB st l bs :
    ↑naN ⊆ E →
    bytes_ctx σB -∗ heap_mapsto_st_vec st l bs ={E}=∗
      ⌜mem_range (.= st) σB l bs⌝ ∗ bytes_ctx σB ∗ heap_mapsto_st_vec st l bs.
  Proof.
    iIntros (?) "(%𝛼 & %M & %Hr & %Hwf & H● & Hbank & Entries & Cells) Hbs".
    iDestruct (heap_st_vec_lookup with "H● Hbs") as %Hrd.
    iMod (bbank_disj with "Entries Hbs") as "(%Hd & Entries & $)"; [done|].
    iModIntro. iSplit; [iPureIntro; by eapply bank_rel_disj|]. iExists 𝛼, M. by iFrame.
  Qed.

  Lemma bytes_ctx_read_begin σB l bs :
    bytes_ctx σB -∗ l ↦b bs ==∗
      ⌜mem_range is_reading σB l bs⌝ ∗
      bytes_ctx (mem_alter ls_inc l (length bs) σB) ∗ heap_mapsto_st_vec (RSt 1) l bs.
  Proof.
    iIntros "(%𝛼 & %M & %Hr & %Hwf & H● & Hbank & Entries & Cells) Hbs".
    rewrite heap_mapsto_bytes_st_vec.
    iMod (heap_st_vec_set _ _ (RSt 1) _ _ bs with "H● Hbs") as (𝛼') "([%Hrd [%H𝛼' %Hc]] & H● & $)"; [done|].
    iDestruct (cells_ctx_rows_eq with "Cells") as "Cells"; [done|].
    have Hrd' : mem_range is_reading (bphi 𝛼) l bs.
    { eapply mem_range_impl; [|done]. intros ? ->. by eexists. }
    iModIntro. iSplit; [iPureIntro; by eapply bank_rel_reading|]. iExists _, M. iFrame. iPureIntro.
    rewrite H𝛼' -(mem_set_alter ls_inc (RSt 0)) //. split.
    - by apply bank_rel_mem_alter_inc.
    - apply bank_wf_mem_alter; [|done]. intros ? [n ->]. by eexists.
  Qed.

  Lemma bytes_ctx_read_end σB l bs :
    bytes_ctx σB -∗ heap_mapsto_st_vec (RSt 1) l bs ==∗
      ⌜mem_range is_reading_S σB l bs⌝ ∗
      bytes_ctx (mem_alter ls_dec l (length bs) σB) ∗ l ↦b bs.
  Proof.
    iIntros "(%𝛼 & %M & %Hr & %Hwf & H● & Hbank & Entries & Cells) Hbs".
    rewrite heap_mapsto_bytes_st_vec.
    iMod (heap_st_vec_set _ _ (RSt 0) _ _ bs with "H● Hbs") as (𝛼') "([%Hrd [%H𝛼' %Hc]] & H● & $)"; [done|].
    iDestruct (cells_ctx_rows_eq with "Cells") as "Cells"; [done|].
    have Hrd' : mem_range is_reading_S (bphi 𝛼) l bs.
    { eapply mem_range_impl; [|done]. intros ? ->. by eexists. }
    iModIntro. iSplit; [iPureIntro; by eapply bank_rel_reading_S|]. iExists _, M. iFrame. iPureIntro.
    rewrite H𝛼' -(mem_set_alter ls_dec (RSt 1)) //. split.
    - by apply bank_rel_mem_alter_dec.
    - apply bank_wf_mem_alter; [|done]. intros ? [n ->]. by eexists.
  Qed.

  Lemma bytes_ctx_write_begin E σB l bs :
    ↑naN ⊆ E →
    bytes_ctx σB -∗ l ↦b bs ={E}=∗
      ⌜mem_range (.= RSt 0) σB l bs⌝ ∗
      bytes_ctx (mem_alter (λ _, WSt) l (length bs) σB) ∗ heap_mapsto_st_vec WSt l bs.
  Proof.
    iIntros (?) "(%𝛼 & %M & %Hr & %Hwf & H● & Hbank & Entries & Cells) Hbs".
    iEval (rewrite heap_mapsto_bytes_st_vec) in "Hbs".
    iMod (bbank_disj with "Entries Hbs") as "(%Hd & Entries & Hbs)"; [done|].
    iMod (heap_st_vec_set _ _ WSt _ _ bs with "H● Hbs") as (𝛼') "([%Hrd [%H𝛼' %Hc]] & H● & $)"; [done|].
    iDestruct (cells_ctx_rows_eq with "Cells") as "Cells"; [done|].
    iModIntro. iSplit; [iPureIntro; by eapply bank_rel_disj|]. iExists _, M. iFrame. iPureIntro.
    rewrite H𝛼' -(mem_set_alter (λ _, WSt) (RSt 0)) //. split.
    - by apply bank_rel_mem_alter_wst.
    - by apply bank_wf_mem_alter_disj.
  Qed.

  Lemma bytes_ctx_write_end E σB l bs bs' :
    ↑naN ⊆ E → length bs' = length bs →
    bytes_ctx σB -∗ heap_mapsto_st_vec WSt l bs ={E}=∗
      ⌜mem_range (.= WSt) σB l bs⌝ ∗ bytes_ctx (mem_write l bs' σB) ∗ l ↦b bs'.
  Proof.
    iIntros (? Hlen) "(%𝛼 & %M & %Hr & %Hwf & H● & Hbank & Entries & Cells) Hbs".
    iMod (bbank_disj with "Entries Hbs") as "(%Hd & Entries & Hbs)"; [done|].
    rewrite heap_mapsto_bytes_st_vec.
    iMod (heap_st_vec_set _ _ (RSt 0) _ _ bs' with "H● Hbs") as (𝛼') "([%Hrd [%H𝛼' %Hc]] & H● & $)"; [done|].
    iDestruct (cells_ctx_rows_eq with "Cells") as "Cells"; [done|].
    iModIntro. iSplit; [iPureIntro; by eapply bank_rel_disj|]. iExists _, M. iFrame.
    iPureIntro. rewrite H𝛼' mem_set_write. split.
    - by apply (bank_rel_mem_write _ _ _ _ bs).
    - apply bank_wf_mem_write; [by rewrite Hlen|done].
  Qed.

  Lemma bytes_ctx_write E σB l bs bs' :
    ↑naN ⊆ E → length bs' = length bs →
    bytes_ctx σB -∗ l ↦b bs ={E}=∗
      ⌜mem_range (.= RSt 0) σB l bs⌝ ∗ bytes_ctx (mem_write l bs' σB) ∗ l ↦b bs'.
  Proof.
    iIntros (? Hlen) "(%𝛼 & %M & %Hr & %Hwf & H● & Hbank & Entries & Cells) Hbs".
    iEval (rewrite heap_mapsto_bytes_st_vec) in "Hbs".
    iMod (bbank_disj with "Entries Hbs") as "(%Hd & Entries & Hbs)"; [done|].
    rewrite heap_mapsto_bytes_st_vec.
    iMod (heap_st_vec_set _ _ (RSt 0) _ _ bs' with "H● Hbs") as (𝛼') "([%Hrd [%H𝛼' %Hc]] & H● & $)"; [done|].
    iDestruct (cells_ctx_rows_eq with "Cells") as "Cells"; [done|].
    iModIntro. iSplit; [iPureIntro; by eapply bank_rel_disj|]. iExists _, M. iFrame.
    iPureIntro. rewrite H𝛼' mem_set_write. split.
    - by apply (bank_rel_mem_write _ _ _ _ bs).
    - apply bank_wf_mem_write; [by rewrite Hlen|done].
  Qed.

  Lemma bytes_ctx_alloc σB l b :
    σB !! l = None →
    bytes_ctx σB ==∗ bytes_ctx (<[l:=(RSt 0, b)]> σB) ∗ heap_mapsto_st (RSt 0) l b.
  Proof.
    iIntros (Hl) "(%𝛼 & %M & %Hr & %Hwf & H● & Hbank & Entries & Cells)".
    have HlA := bank_rel_lookup_None _ _ _ _ Hr Hl.
    iMod (heap_bytes_alloc_vs' _ _ b with "H●") as (𝛼') "([%H𝛼' %Hc] & H● & $)"; [done|].
    iDestruct (cells_ctx_rows_eq with "Cells") as "Cells"; [done|].
    iModIntro. iExists _, M. iFrame. iPureIntro. rewrite H𝛼'. split.
    - apply bank_rel_insert; [done|]. by eapply bank_wf_bcnt.
    - by apply bank_wf_insert.
  Qed.

  Lemma bytes_ctx_dealloc E σB l b :
    ↑naN ⊆ E →
    bytes_ctx σB -∗ heap_mapsto_st (RSt 0) l b ={E}=∗
      ⌜σB !! l = Some (RSt 0, b)⌝ ∗ bytes_ctx (delete l σB).
  Proof.
    iIntros (?) "(%𝛼 & %M & %Hr & %Hwf & H● & Hbank & Entries & Cells) Hb".
    iAssert (heap_mapsto_st_vec (RSt 0) l [b]) with "[Hb]" as "Hb".
    { rewrite /heap_mapsto_st_vec /= shift_loc_0. by iFrame. }
    iMod (bbank_disj with "Entries Hb") as "(%Hd & Entries & Hb)"; [done|].
    rewrite /heap_mapsto_st_vec /= shift_loc_0. iDestruct "Hb" as "[Hb _]".
    iMod (heap_bytes_dealloc_vs' with "H● Hb") as (𝛼') "([%HlA [%H𝛼' %Hc]] & H●)".
    iDestruct (cells_ctx_rows_eq with "Cells") as "Cells"; [done|]. iModIntro.
    iSplit.
    { iPureIntro. have H0 := bank_disj_bcnt _ _ _ 0%nat Hd ltac:(simpl; lia).
      rewrite shift_loc_0_nat in H0. by rewrite Hr HlA /= H0. }
    iExists _, M. iFrame. iPureIntro. rewrite H𝛼'. split.
    - by apply bank_rel_delete.
    - by apply bank_wf_delete.
  Qed.

  (** ** Guarded reads *)
  Lemma bytes_ctx_read_begin_guarded E σB l (Φ : list abyte → Prop) n G P d :
    ↑naN ⊆ E → (∀ bs, Φ bs → length bs = n) →
    £(2*d) -∗ (G &&{↑naN; d}&&> P) -∗
    □ (P -∗ ∃ bs, ⌜Φ bs⌝ ∗ l ↦b bs ∗ (l ↦b bs -∗ P)) -∗ G -∗ bytes_ctx σB ={E}=∗
      ∃ i bs, ⌜Φ bs⌝ ∗ ⌜mem_range is_reading σB l bs⌝ ∗
      bytes_ctx (mem_alter ls_inc l n σB) ∗ bread_tok i l bs G.
  Proof.
    iIntros (? HΦ) "[£1 £2] #Guard #HP G (%𝛼 & %M & %Hr & %Hwf & H● & Hbank & Entries & Cells)".
    replace (d + 0)%nat with d by lia.
    iMod (guards_open_later with "Guard G") as "Open"; [done|].
    iMod (lc_fupd_elim_laterN with "£1 Open") as ">[P Back]".
    iDestruct ("HP" with "P") as (bs HΦbs) "[Pt Ret]".
    iEval (rewrite heap_mapsto_bytes_st_vec) in "Pt".
    iDestruct (heap_st_vec_lookup with "H● Pt") as %Hrd0.
    have Hrd : mem_range is_reading (bphi 𝛼) l bs.
    { eapply mem_range_impl; [|done]. intros ? ->. by eexists. }
    iEval (rewrite -heap_mapsto_bytes_st_vec) in "Pt".
    iMod ("Back" with "(Ret Pt)") as "G".
    have Hn := HΦ _ HΦbs. subst n.
    set i := fresh (dom M).
    have Hi : M !! i = None by apply not_elem_of_dom, is_fresh.
    iMod (own_update _ _ (gmap_view_auth (DfracOwn 1)
        ((λ e, to_agree (bbank_elt e.1 e.2)) <$> <[i := ((l, bs), G)]> M) ⋅
      gmap_view_frag i (DfracOwn 1) (to_agree (bbank_elt (l, bs) G))) with "Hbank")
      as "[Hbank Tok]".
    { rewrite fmap_insert. apply gmap_view_alloc; [|done..]. by rewrite lookup_fmap Hi. }
    iModIntro. iExists i, bs. iFrame "Tok". iSplit; [done|].
    iSplit; [iPureIntro; by eapply bank_rel_reading|].
    iExists 𝛼, (<[i := ((l, bs), G)]> M). iFrame "H● Hbank Cells". iSplit.
    { iPureIntro. rewrite fmap_insert. apply bank_rel_add; [done| |done].
      by rewrite lookup_fmap Hi. }
    iSplit. { iPureIntro. rewrite fmap_insert. by apply bank_wf_add. }
    rewrite big_sepM_insert //. iFrame "Entries G". iExists P, d. iFrame "£2 Guard".
    iIntros "!> P". iDestruct ("HP" with "P") as (bs' Hbs') "[Pt _]".
    iExists ((λ b, inr (RSt 0, b)) <$> bs'). iSplit.
    { iPureIntro. by rewrite length_fmap (HΦ _ Hbs'). }
    rewrite heap_mapsto_bytes_eq /heap_mapsto_bytes_def /heap_mapsto_st_vec big_sepL_fmap.
    iFrame "Pt". iLeft. iPureIntro. apply Forall_fmap, Forall_true. eauto.
  Qed.

  Lemma bytes_ctx_read_end_guarded σB i l bs G :
    bytes_ctx σB -∗ bread_tok i l bs G ==∗
      ⌜mem_range is_reading_S σB l bs⌝ ∗
      bytes_ctx (mem_alter ls_dec l (length bs) σB) ∗ ▷ G.
  Proof.
    iIntros "(%𝛼 & %M & %Hr & %Hwf & H● & Hbank & Entries & Cells) Tok".
    iDestruct (own_valid_2 with "Hbank Tok") as "#Hv".
    rewrite gmap_view_both_validI lookup_fmap. iDestruct "Hv" as "(_ & _ & Hv)".
    destruct (M !! i) as [[[l' bs'] G']|] eqn:Hi; last first.
    { rewrite option_equivI. done. }
    rewrite option_equivI /= agree_equivI prod_equivI /=.
    iDestruct "Hv" as "[%Heq Heq]". simplify_eq.
    have Hi' : (fst <$> M) !! i = Some (l, bs) by rewrite lookup_fmap Hi.
    have Hrd := Hwf i _ Hi'.
    iMod (own_update_2 with "Hbank Tok") as "Hbank"; [apply gmap_view_delete|].
    rewrite big_sepM_delete //. iDestruct "Entries" as "[[G _] Entries]".
    iModIntro. iSplit.
    { iPureIntro. rewrite mem_range_lookup. intros j b Hb.
      destruct (mem_range_lookup_1 _ _ _ _ j Hrd) as (ls & b' & Hl & [n ->] & Hb');
        [by eapply lookup_lt_Some|].
      rewrite Hb in Hb'. simplify_eq. rewrite Hr Hl /=.
      rewrite (bcnt_delete _ _ _ _ Hi') /= decide_True; [|exists j; split; [by eapply lookup_lt_Some|done]].
      eexists. split; [done|]. exists (n + bcnt (delete i (fst <$> M)) (l +ₗ j))%nat.
      f_equal. lia. }
    iSplitR "G Heq".
    - iExists 𝛼, (delete i M). rewrite /bbank_auth -fmap_delete. iFrame. iPureIntro. split.
      + rewrite fmap_delete. by eapply bank_rel_remove.
      + rewrite fmap_delete. by apply bank_wf_remove.
    - rewrite later_equivI. iNext. by iRewrite "Heq" in "G".
  Qed.
End bank.

Section bytes_ctx.
  Context `{!heapGS Σ}.
  Context `{!invGS Σ}.
  Context `{!na_invG Σ}.
  Context `{!alc_logicG Σ}.
  Implicit Types bs : list abyte.

  (** ** Allocation and deallocation in the byte region *)
  Lemma heap_alloc_bytes_vs (σ : state') l n :
    (∀ m : Z, σ !! (l +ₗ m) = None) →
    heap_maps_ctx σ ==∗ heap_maps_ctx (init_mem l n σ) ∗ l ↦b (replicate n Uninit).
  Proof.
    revert l. induction n as [|n IH]; iIntros (l Hfresh) "σ".
    { iFrame. by rewrite heap_mapsto_bytes_nil. }
    iMod (IH (l +ₗ 1) with "σ") as "[σ Hl]".
    { intros m. rewrite shift_loc_assoc. apply Hfresh. }
    have Hfr : init_mem (l +ₗ 1) n σ !! l = None.
    { rewrite lookup_init_mem_ne /=; last lia. rewrite -(shift_loc_0 l). apply Hfresh. }
    iMod (bytes_ctx_alloc _ _ Uninit with "σ") as "[σ Hb]"; [done|].
    iModIntro. rewrite /= (heap_mapsto_bytes_cons _ Uninit). iFrame.
    rewrite heap_mapsto_bytes_eq /heap_mapsto_bytes_def /heap_mapsto_st_vec /=.
    rewrite shift_loc_0. by iFrame.
  Qed.

  Lemma heap_alloc_bytes (σ: state) l n :
    0 < n →
    (∀ m, σ.1 !! (l +ₗ m) = None) →
    heap_ctx σ ==∗
      heap_ctx (init_mem l (Z.to_nat n) $σ σ) ∗ †l…(Z.to_nat n) ∗
      l ↦b replicate (Z.to_nat n) Uninit.
  Proof.
    intros ??; iDestruct 1 as (hF) "(Hvalσ & HhF & % & ato)".
    assert (Z.to_nat n ≠ O). { rewrite -(Nat2Z.id 0)=>/Z2Nat.inj. lia. }
    iMod (heap_alloc_bytes_vs _ _ (Z.to_nat n) with "[$Hvalσ]") as "[Hvalσ Hmapsto]"; first done.
    iMod (own_update _ (● hF) with "HhF") as "[HhF Hfreeable]".
    { apply auth_update_alloc,
        (alloc_singleton_local_update _ (l.1) (1%Qp, inter (l.2) (Z.to_nat n))).
      - eauto using heap_freeable_rel_None.
      - split; first done. apply inter_valid. }
    iModIntro. iSplitL "Hvalσ HhF ato".
    { iExists _. iFrame. iPureIntro.
      auto using heap_freeable_rel_init_mem. }
    rewrite heap_freeable_eq /heap_freeable_def //. iFrame.
  Qed.

  Lemma heap_free_bytes_vs (σ : state') l bs E :
    ↑naN ⊆ E →
    heap_maps_ctx σ -∗ l ↦b bs ={E}=∗ heap_maps_ctx (free_mem l (length bs) σ).
  Proof.
    iIntros (?). iInduction bs as [|b bs] "IH" forall (l); iIntros "σ Hbs"; [by iFrame|].
    rewrite heap_mapsto_bytes_cons. iDestruct "Hbs" as "[Hb Hbs]".
    iMod ("IH" with "σ Hbs") as "σ".
    rewrite heap_mapsto_bytes_eq /heap_mapsto_bytes_def /heap_mapsto_st_vec /= shift_loc_0.
    iDestruct "Hb" as "[Hb _]".
    iMod (bytes_ctx_dealloc with "σ Hb") as "[%Hl σ]"; [done|].
    by iFrame.
  Qed.

  Lemma heap_free_bytes σ l bs (n : Z) E :
    ↑naN ⊆ E → n = length bs →
    heap_ctx σ -∗ l ↦b bs -∗ †l…(length bs)
    ={E}=∗ ⌜0 < n⌝ ∗ ⌜∀ m, is_Some (σ.1 !! (l +ₗ m)) ↔ (0 ≤ m < n)⌝ ∗
        heap_ctx (free_mem l (Z.to_nat n) $σ σ).
  Proof.
    iDestruct 1 as (hF) "(Hvalσ & HhF & REL & ato)"; iDestruct "REL" as %REL.
    iIntros "Hmt Hf". rewrite heap_freeable_eq /heap_freeable_def.
    iDestruct (own_valid_2 with "HhF Hf") as % [Hl Hv]%auth_both_valid_discrete.
    move: Hl=> /singleton_included_l [[q qs] [/leibniz_equiv_iff Hl Hq]].
    apply (Some_included_exclusive _ _) in Hq as [=<-<-]%leibniz_equiv; last first.
    { move: (Hv (l.1)). rewrite Hl. by intros [??]. }
    assert (bs ≠ []).
    { intros ->. by destruct (REL (l.1) (1%Qp, ∅)) as [[] ?]. }
    assert (0 < n) by (subst n; by destruct bs).
    iMod (heap_free_bytes_vs with "Hvalσ Hmt") as "Hvalσ"; [done|].
    iMod (own_update_2 with "HhF Hf") as "HhF".
    { apply auth_update_dealloc, (delete_singleton_local_update _ _ _). }
    iModIntro; subst. repeat iSplit;  eauto using heap_freeable_is_Some.
    iExists _. subst. rewrite Nat2Z.id. iFrame.
    eauto using heap_freeable_rel_free_mem.
  Qed.

End bytes_ctx.
