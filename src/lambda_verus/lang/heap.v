Require Import guarding.internal.na_invariants_fork.
From lrust.util Require Import non_atomic_cell_map atomic_lock_counter update.
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

Physical memory holds abstract bytes ([state' = gmap loc (lock_state * abyte)]).
Its ghost state has two regions, with disjoint domains (see [phys_rel]):
- the legacy region, a [non_atomic_map] of [val]s (with cells), which backs the
  legacy points-to [l ↦ v] and all its fancy and cell variants: a location of
  this region holding [v] holds the byte [word_to_byte v] physically;
- the byte region, a full-authority cell map ([fcmapR] of [util/cellmap.v]) whose
  values ([bval]) are a lock state and an abstract byte, which backs the byte points-to
  [l ↦b bs]. Each location of the byte region has a row: a chain of byte-cells
  (possibly empty) ending in its value. The physical byte region is [𝜙 𝛼] (the values of
  the location rows), plus the read counts of the bank of guarded reads.
The legacy layer cannot simply be defined on top of the byte region: its
untethering lemmas (e.g. [mapsto_vec_untether1]) return the contents of a cell
as a [val], so the cell map must hold [val]s; and multi-byte non-atomic reads
through the cell map would need one later per byte. A location moves between the
regions with [heap_word_to_bytes] and [heap_bytes_to_word] (no physical step). *)

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
  #[global] heap_na_logicG :: na_logicG loc val Σ;
  #[global] heap_bbank_inG :: inG Σ (gmap_viewR nat (agreeR (prodO (leibnizO (loc * list abyte))
    (laterO (iPropO Σ)))));
  #[global] heap_greg_inG :: ghost_mapG Σ positive (mty * list positive);
  #[global] heap_gdyn_inG :: ghost_mapG Σ positive FValue;
  #[global] heap_gnc_inG :: ghost_mapG Σ positive ();
  #[global] heap_cw_inG :: inG Σ (gmap_viewR positive (agreeR (prodO
    (leibnizO (loc * nat * nat * FValue)) (laterO (iPropO Σ)))));
  heap_name : gname;
  heap_bytes_name : gname;
  heap_bbank_name : gname;
  heap_greg_name : gname;
  heap_gdyn_name : gname;
  heap_gnc_name : gname;
  heap_cw_name : gname;
  heap_freeable_name : gname;
  atomic_threadpool: gname;
  atomic_lock_ctr_name: gname
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

(** The pure invariants of the cell registry. *)
Definition cells_wf (R : gmap positive (mty * list positive)) (ρ : gmap positive FValue)
    (NC : gmap positive ()) (CW : gmap positive cwkey) : Prop :=
  reg_wf R ∧ dom ρ ⊆ dom R ∧
  (∀ g fv, ρ !! g = Some fv → ∀ g', g' ∈ fv_cells fv → (g' < g)%positive ∧ g' ∈ dom ρ) ∧
  (∀ g1 g2 m1 cs1 m2 cs2, g1 ≠ g2 → R !! g1 = Some (m1, cs1) → R !! g2 = Some (m2, cs2) →
     cs1 ## cs2) ∧
  (∀ g m cs, R !! g = Some (m, cs) → (0 < mty_size m)%nat) ∧
  dom NC ⊆ dom R ∧ (∀ g fv, ρ !! g = Some fv → g ∈ dom NC → fv_cells fv = []) ∧
  (∀ g k, CW !! g = Some k → ρ !! g = Some k.2 ∧
     ∃ m cs, R !! g = Some (m, cs) ∧ (k.1.1.2 + k.1.2 ≤ length cs)%nat).

(** Every byte-cell of the byte region belongs to a live group, and the groups with a write
    in flight sit at the start of the rows of their locations. *)
Definition cells_live (𝛼 : bfull) (R : gmap positive (mty * list positive))
    (ρ : gmap positive FValue) (CW : gmap positive cwkey) : Prop :=
  (∀ k cs v c, 𝛼 !! k = Some (cs, v) → c ∈ cs →
     ∃ g m cs', g ∈ dom ρ ∧ R !! g = Some (m, cs') ∧ c ∈ cs') ∧
  (∀ g k m cs, CW !! g = Some k → R !! g = Some (m, cs) →
     ∀ (i : nat) c, cs !! i = Some c → ∃ rest v, 𝛼 !! inl (k.1.1.1 +ₗ i) = Some (c :: rest, v)).

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

  (** Fancy bytes at locations: [l +ₗ i] points to the byte-cell or the byte [fbs !! i]. *)
  Definition heap_mapsto_fbytes (l : loc) (fbs : list (positive + abyte)) : iProp Σ :=
    [∗ list] i ↦ fb ∈ fbs, bpt (inl (l +ₗ i)) (fb_rst fb).

  (** The fancy bytes [fbs] represent [fv] at [m], with the static registry. *)
  Definition brepr (m : mty) (fbs : list (positive + abyte)) (fv : FValue) : iProp Σ :=
    ∃ R, ⌜frepr R m fbs fv⌝ ∗ [∗ map] g ↦ e ∈ R, greg g e.1 e.2.

  (** The contents of a live group, owned by the byte context, with the invariant D3. *)
  Definition gcontents (R : gmap positive (mty * list positive)) (CW : gmap positive cwkey)
      (g : positive) (fv : FValue) : iProp Σ :=
    ∃ m cs fbs, ⌜R !! g = Some (m, cs) ∧ frepr R m (fb_strip <$> fbs) fv ∧
      ∀ i ls b, fbs !! i = Some (inr (ls, b)) → ls = cw_ls CW g i⌝ ∗ bcells cs fbs.

  (** The bank of cell writes. *)
  Definition cw_elt (k : cwkey) (G : iProp Σ) : prodO (leibnizO cwkey) (laterO (iPropO Σ)) :=
    (k, Next G).
  Definition cwbank_auth (CW : gmap positive (cwkey * iProp Σ)) : iProp Σ :=
    own heap_cw_name (gmap_view_auth (DfracOwn 1)
      ((λ e : cwkey * iProp Σ, to_agree (cw_elt e.1 e.2)) <$> CW)).
  Definition cwrite_tok (g : positive) (k : cwkey) (G : iProp Σ) : iProp Σ :=
    own heap_cw_name (gmap_view_frag g (DfracOwn 1) (to_agree (cw_elt k G))).
  Definition cwentry (g : positive) (e : cwkey * iProp Σ) : iProp Σ :=
    ∃ m cs, greg g m cs ∗ gdyn g e.1.2 ∗ e.2 ∗ ∃ P d, £d ∗ (e.2 &&{↑naN; d}&&> P) ∗
      □ (P -∗ loc_side e.1.1.1.1 g m cs).

  Definition cells_ctx (𝛼 : bfull) : iProp Σ :=
    ∃ R ρ NC (CW : gmap positive (cwkey * iProp Σ)),
      ghost_map_auth heap_greg_name 1 R ∗ ghost_map_auth heap_gdyn_name 1 ρ ∗
      ghost_map_auth heap_gnc_name 1 NC ∗ cwbank_auth CW ∗
      ⌜cells_wf R ρ NC (fst <$> CW) ∧ cells_live 𝛼 R ρ (fst <$> CW)⌝ ∗
      ([∗ map] g ↦ e ∈ R, greg g e.1 e.2) ∗ ([∗ map] g ↦ e ∈ CW, cwentry g e) ∗
      [∗ map] g ↦ fv ∈ ρ, gcontents R (fst <$> CW) g fv.

  (** The read witness of an entry of the bank of guarded reads: the location edges [cvs]
      of the range all point to bytes, or all to byte-cells of one group, whose permission
      the reader has. *)
  Definition cells_wit (cvs : list (positive + bval)) : iProp Σ :=
    ⌜Forall (λ cv, ∃ v, cv = inr v) cvs⌝ ∨
    ∃ g m cs fv, greg g m cs ∗ gdyn g fv ∗ ⌜Forall (λ cv, ∃ c, cv = inl c ∧ c ∈ cs) cvs⌝.
End cells_defs.

(** ** The bank of guarded reads of the byte region

A non-atomic read of bytes that are only _guarded_ ([G &&{↑naN; d}&&> l ↦b bs], as
in the sharing predicate of a shared reference) cannot keep the points-to across the
two steps of the read. As for the legacy region (the read bank of [non_atomic_map]),
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
           ([∗ list] i ↦ cv ∈ cvs, bpt (inl (e.1.1 +ₗ i)) cv) ∗ cells_wit cvs).

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
  
  Definition heap_mapsto'
      (lc: loc + cell_id) (cells: list cell_id) (cv: cell_id + val) : iProp Σ
      := lc @↦[heap_name][^ cells] cv.

  Definition heap_mapsto (l : loc) (v: val) : iProp Σ :=
    (inl l) @↦[heap_name][^ []] (inr v).

  Definition heap_mapsto_vec (l : loc) (vl : list val) : iProp Σ :=
    ([∗ list] i ↦ v ∈ vl, heap_mapsto (l +ₗ i) v)%I.

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


  (** The physical memory [σ] is the union of the legacy region [σL] (whose
      words are stored as [word_to_byte]) and the byte region [σB]. *)
  Definition phys_rel (σ : state') (σL : gmap loc (lock_state * val))
      (σB : gmap loc (lock_state * abyte)) : Prop :=
    ∀ l, match σL !! l, σB !! l with
         | Some (ls, v), None => σ !! l = Some (ls, word_to_byte v)
         | None, Some p => σ !! l = Some p
         | None, None => σ !! l = None
         | Some _, Some _ => False
         end.

  Definition heap_maps_ctx (σ : state') : iProp Σ :=
    ∃ σL σB, ⌜phys_rel σ σL σB⌝ ∗ non_atomic_map heap_name σL
           ∗ bytes_ctx σB.

  Definition heap_ctx (σ:state) : iProp Σ :=
    (∃ hF, heap_maps_ctx σ.1
         ∗ own heap_freeable_name (● hF)
         ∗ ⌜heap_freeable_rel σ hF⌝
         ∗ (match σ.2 with true => True | false => heap_ato_ctx end))%I.
         
  Definition cell_id := positive.
  
  Inductive fancy_val :=
    | FVal (v: val)
    | FCell (c: cell_id).
    
  Definition fv2sum (fv: fancy_val) :=
      match fv with | FVal v => inr v | FCell c => inl c end.
      
  Definition sum2fv (cv: cell_id + val) :=
      match cv with | inl c => FCell c | inr v => FVal v end.
  
  Definition cloc1: Type := loc * list cell_id. 
  Definition cloc: Type := loc * list (list cell_id).
  
  Definition of_cloc (l: cloc) : loc := (l.1).
  
  Definition to_cloc (l: loc) : cloc := (l, []).
     
  Definition heap_mapsto_fancy (l: loc) (fv: fancy_val) : iProp Σ :=
      inl l @↦[heap_name] (fv2sum fv).
  
  Definition heap_mapsto_cells_fancy (l: loc) (cells: list cell_id) (fv: fancy_val) : iProp Σ :=
      inl l @↦[heap_name][^ cells] (fv2sum fv).
      
  Fixpoint heap_mapsto_cells_fancy_vec (l: loc) (cells: list (list cell_id)) (fvs: list fancy_val) : iProp Σ :=
      match cells, fvs with
          | [], [] => True%I
          | cell :: cells', fv :: fvs' => inl l @↦[heap_name][^ cell] (fv2sum fv) ∗ heap_mapsto_cells_fancy_vec (l +ₗ 1) cells' fvs'
          | _, _ => False%I
      end.
  
  Definition heap_mapsto_fancy_vec (l: loc) (fv: list fancy_val) : iProp Σ :=
      heap_mapsto_cells_fancy_vec l (repeat [] (length fv)) fv.
  
  Definition heap_mapsto_cells_val_vec (l: loc) (cells: list (list cell_id)) (v: list val) : iProp Σ :=
      heap_mapsto_cells_fancy_vec l cells (FVal <$> v).
  
  Definition split_at_last {A} (l: list A) : option (list A * A) :=
      match List.rev l with
        | [] => None
        | x :: xs => Some (List.rev xs, x)
      end.
  
  Definition heap_complete_mapsto (l: cloc1) : iProp Σ :=
      match split_at_last (snd l) with
          | Some (cells, last_cell) => inl (fst l) @↦[heap_name][^ cells] (inl last_cell)
          | None => True%I
      end.
      
  Definition heap_complete_mapsto_fancy (l: cloc1) (fv: fancy_val) : iProp Σ :=
      (match split_at_last (snd l) with
          | Some (_, last_cell) => inr last_cell 
          | None => inl (fst l) 
      end) @↦[heap_name] (fv2sum fv).
      
  Fixpoint heap_complete_mapsto_vec' (l: loc) (cs: list (list cell_id)) : iProp Σ :=
      match cs with
        | [] => True%I
        | c :: cells =>
            heap_complete_mapsto (l, c) ∗ heap_complete_mapsto_vec' (l +ₗ 1) cells
      end.
  
  Definition heap_complete_mapsto_vec (l: cloc) : iProp Σ :=
      heap_complete_mapsto_vec' (fst l) (snd l).
      
  Fixpoint heap_complete_mapsto_fancy_vec' (l: loc) (cs: list (list cell_id)) (fvs: list fancy_val) : iProp Σ :=
      match cs, fvs with
        | [], [] => True%I
        | c :: cells, fv :: fvs =>
            heap_complete_mapsto_fancy (l, c) fv ∗ heap_complete_mapsto_fancy_vec' (l +ₗ 1) cells fvs
        | _, _ => False%I
      end.
  
  Definition heap_complete_mapsto_fancy_vec (l: cloc) (fvs: list fancy_val) : iProp Σ :=
      heap_complete_mapsto_fancy_vec' (fst l) (snd l) fvs.
  
  Definition heap_complete_mapsto_val_vec (l: cloc) (v: list val) : iProp Σ :=
      heap_complete_mapsto_fancy_vec l (FVal <$> v).
  
  Definition cell_points_to_value (c : cell_id) (v : val) : iProp Σ :=
      inr c @↦[heap_name] (inr v).

  Definition cell_points_to_fancy_value (c : cell_id) (fv : fancy_val) : iProp Σ :=
      inr c @↦[heap_name] (fv2sum fv).
  
  Fixpoint cells_points_to_fancy_value_vec (cells : list cell_id) (fvs : list fancy_val) : iProp Σ := match cells, fvs with
      | [], [] => True%I
      | cell :: cells, fv :: fvs => (inr cell) @↦[heap_name] (fv2sum fv) ∗ cells_points_to_fancy_value_vec cells fvs
      | _, _ => False%I
      end.
      
  Global Instance heap_complete_mapsto_fancy_vec'_timeless l cs fvs : Timeless (heap_complete_mapsto_fancy_vec' l cs fvs). 
  Proof. generalize l, fvs. clear l. clear fvs. induction cs.
    - simpl. apply _. - intros l fvs. simpl. destruct fvs; first by apply _.
      apply sep_timeless; apply _.
  Qed.

  Global Instance heap_complete_mapsto_fancy_vec_timeless l fv : Timeless (heap_complete_mapsto_fancy_vec l fv). 
  Proof. apply _. Qed.

  Global Instance cell_points_to_value_timeless c v : Timeless (cell_points_to_value c v).
  Proof. apply _. Qed.
  Global Instance cell_points_to_fancy_value_timeless c fv : Timeless (cell_points_to_fancy_value c fv). 
  Proof. apply _. Qed.
  Global Instance cells_points_to_fancy_value_vec_timeless cells fv : Timeless (cells_points_to_fancy_value_vec cells fv).
  Proof.
    induction cells in fv |- *.
    - simpl. apply _.
    - simpl. destruct fv; first by apply _. apply sep_timeless; apply _.
  Qed.

End definitions.

Global Typeclasses Opaque heap_mapsto heap_freeable heap_mapsto_vec.
Global Instance: Params (@heap_mapsto) 4 := {}.
Global Instance: Params (@heap_freeable) 5 := {}.

Notation "l ↦ v" := (heap_mapsto l v) (at level 20) : bi_scope.

Notation "c ^↦ v" := (cell_points_to_value c v) (at level 20) : bi_scope.
Notation "c ^↦! fv" := (cell_points_to_fancy_value c fv) (at level 20) : bi_scope.
Notation "cs ^↦!∗ fl" := (cells_points_to_fancy_value_vec cs fl) (at level 20) : bi_scope.

Notation "l #↦_" := (heap_complete_mapsto l) (at level 20) : bi_scope.
Notation "l #↦! fv" := (heap_complete_mapsto_fancy l fv) (at level 20) : bi_scope.
Notation "l #↦ v" := (heap_complete_mapsto_fancy l (FVal v)) (at level 20) : bi_scope.

Notation "l #↦∗_" := (heap_complete_mapsto_vec l) (at level 20) : bi_scope.
Notation "l #↦!∗ fv" := (heap_complete_mapsto_fancy_vec l fv) (at level 20) : bi_scope.
Notation "l #↦∗ v" := (heap_complete_mapsto_val_vec l v) (at level 20) : bi_scope.

Notation "l ↦[^ c ] v" := (heap_mapsto_cells_fancy l c (FVal v)) (at level 20) : bi_scope.
Notation "l ↦[^ c ]! fv" := (heap_mapsto_cells_fancy l c fv) (at level 20) : bi_scope.
Notation "l ↦! fv" := (heap_mapsto_fancy l fv) (at level 20) : bi_scope.

Notation "l ↦[^ c ]∗ v" := (heap_mapsto_cells_val_vec l c v) (at level 20) : bi_scope.
Notation "l ↦[^ c ]!∗ fv" := (heap_mapsto_cells_fancy_vec l c fv) (at level 20) : bi_scope.

Notation "l ↦!∗ fv" := (heap_mapsto_fancy_vec l fv) (at level 20) : bi_scope.

Notation "l ↦∗ vl" := (heap_mapsto_vec l vl) (at level 20) : bi_scope.

Notation "l ↦∗: P " := (∃ vl, l ↦∗ vl ∗ P vl)%I
  (at level 20, format "l  ↦∗:  P") : bi_scope.
Notation "l #↦!∗: P " := (∃ vl, l #↦!∗ vl ∗ P vl)%I
  (at level 20, format "l  #↦!∗:  P") : bi_scope.

Notation "†{ q } l … n" := (heap_freeable l q n)
  (at level 20, q at level 50, format "†{ q } l … n") : bi_scope.
Notation "† l … n" := (heap_freeable l 1 n) (at level 20) : bi_scope.

Section kmap_lemmas.

  Local Unset Default Proof Using.
  Context `{FinMap nat M1} `{FinMap K2 M2}.
  Context (f : nat → K2) `{!Inj (=) (=) f}.
  (* Local Notation kmap := (kmap (M1:=M1) (M2:=M2)). *)
  Lemma kmap_map_seq_shift {A} (n : nat) (l : list A) :
    @kmap K2 M2 _ _ nat M1 _ A f (@map_seq A (M1 A) _ _ n l) = kmap (λ i, f (n + i)%nat) (map_seq 0 l).
  Proof using All.
    apply map_eq. intros i. apply option_eq; intros y.
    rewrite lookup_kmap_Some.
    setoid_rewrite lookup_kmap_Some => //.
    2: { intros a b Heq%Inj0. lia. }
    split.
    - intros [j [-> [? Hlookup]%lookup_map_seq_Some]].
      exists (j - n)%nat.
      replace (n + (j - n))%nat with j by lia.
      split => //.
      rewrite lookup_map_seq_Some.
      split; first lia.
      by rewrite Nat.sub_0_r.
    - intros [j [-> [? Hlookup]%lookup_map_seq_Some]].
      exists (n + j)%nat.
      split => //.
      rewrite lookup_map_seq_Some.
      split; first lia.
      move: Hlookup.
      by rewrite Nat.add_sub' Nat.sub_0_r.
  Qed.

End kmap_lemmas.


(** ** The physical relation *)
Section phys_rel.
  Implicit Types σ : state'.

  Lemma phys_rel_lookup_L σ σL σB l ls v :
    phys_rel σ σL σB → σL !! l = Some (ls, v) → σ !! l = Some (ls, word_to_byte v).
  Proof. intros Hr Hl. specialize (Hr l). rewrite Hl in Hr. by destruct (σB !! l). Qed.

  Lemma phys_rel_lookup_B σ σL σB l p :
    phys_rel σ σL σB → σB !! l = Some p → σ !! l = Some p.
  Proof.
    intros Hr Hl. specialize (Hr l). rewrite Hl in Hr. by destruct (σL !! l) as [[]|].
  Qed.

  Lemma phys_rel_B_not_L σ σL σB l :
    phys_rel σ σL σB → is_Some (σB !! l) → σL !! l = None.
  Proof.
    intros Hr [p Hl]. specialize (Hr l). rewrite Hl in Hr. by destruct (σL !! l) as [[]|].
  Qed.

  Lemma phys_rel_L_not_B σ σL σB l :
    phys_rel σ σL σB → is_Some (σL !! l) → σB !! l = None.
  Proof.
    intros Hr [[ls v] Hl]. specialize (Hr l). rewrite Hl in Hr. by destruct (σB !! l).
  Qed.

  Lemma phys_rel_None σ σL σB l :
    phys_rel σ σL σB → σ !! l = None → σL !! l = None ∧ σB !! l = None.
  Proof.
    intros Hr Hl. specialize (Hr l).
    destruct (σL !! l) as [[]|], (σB !! l); simplify_eq; done.
  Qed.

  (** An update of the byte region, at locations of the byte region. *)
  Lemma phys_rel_B_update σ σ' σL σB σB' :
    phys_rel σ σL σB →
    (∀ l, (σ' !! l = σ !! l ∧ σB' !! l = σB !! l) ∨
          (is_Some (σB !! l) ∧ is_Some (σB' !! l) ∧ σ' !! l = σB' !! l)) →
    phys_rel σ' σL σB'.
  Proof.
    intros Hr Hupd l. specialize (Hr l). destruct (Hupd l) as [[-> ->]|(HB&[p Hp]&->)]; [done|].
    destruct HB as [p0 Hp0]. rewrite Hp0 in Hr. rewrite Hp.
    destruct (σL !! l) as [[]|]; done.
  Qed.

  Lemma phys_rel_L_insert σ σL σB l ls v :
    phys_rel σ σL σB → σB !! l = None →
    phys_rel (<[l:=(ls, word_to_byte v)]> σ) (<[l:=(ls, v)]> σL) σB.
  Proof.
    intros Hr HB l'. destruct (decide (l = l')) as [<-|].
    - by rewrite !lookup_insert HB.
    - rewrite !lookup_insert_ne //. apply Hr.
  Qed.

  Lemma phys_rel_B_insert σ σL σB l p :
    phys_rel σ σL σB → σL !! l = None →
    phys_rel (<[l:=p]> σ) σL (<[l:=p]> σB).
  Proof.
    intros Hr HL l'. destruct (decide (l = l')) as [<-|].
    - by rewrite !lookup_insert HL.
    - rewrite !lookup_insert_ne //. apply Hr.
  Qed.

  Lemma phys_rel_L_delete σ σL σB l :
    phys_rel σ σL σB → σB !! l = None → phys_rel (delete l σ) (delete l σL) σB.
  Proof.
    intros Hr HB l'. destruct (decide (l = l')) as [<-|].
    - by rewrite !lookup_delete HB.
    - rewrite !lookup_delete_ne //. apply Hr.
  Qed.

  Lemma phys_rel_B_delete σ σL σB l :
    phys_rel σ σL σB → σL !! l = None → phys_rel (delete l σ) σL (delete l σB).
  Proof.
    intros Hr HL l'. destruct (decide (l = l')) as [<-|].
    - by rewrite !lookup_delete HL.
    - rewrite !lookup_delete_ne //. apply Hr.
  Qed.

  Lemma phys_rel_L_to_B σ σL σB l ls v :
    phys_rel σ σL σB → σL !! l = Some (ls, v) →
    phys_rel σ (delete l σL) (<[l:=(ls, word_to_byte v)]> σB).
  Proof.
    intros Hr HL l'. destruct (decide (l = l')) as [<-|].
    - rewrite lookup_delete lookup_insert. by eapply phys_rel_lookup_L.
    - rewrite lookup_delete_ne // lookup_insert_ne //. apply Hr.
  Qed.

  Lemma phys_rel_B_to_L σ σL σB l ls v :
    phys_rel σ σL σB → σB !! l = Some (ls, word_to_byte v) →
    phys_rel σ (<[l:=(ls, v)]> σL) (delete l σB).
  Proof.
    intros Hr HB l'. destruct (decide (l = l')) as [<-|].
    - rewrite lookup_delete lookup_insert. by eapply phys_rel_lookup_B.
    - rewrite lookup_delete_ne // lookup_insert_ne //. apply Hr.
  Qed.

  Lemma phys_rel_empty : phys_rel ∅ ∅ ∅.
  Proof. intros l. by rewrite !lookup_empty. Qed.
End phys_rel.

Section heap.
  Context `{!heapGS Σ}.
  Context `{!invGS Σ}.
  Context `{!na_invG Σ}.
  Context `{!alc_logicG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : state.
  Implicit Types E : coPset.

  (** General properties of mapsto and freeable *)
  Global Instance heap_mapsto_timeless l v : Timeless (l ↦ v).
  Proof. apply points_to_timeless. Qed.

  Global Instance heap_mapsto_vec_timeless l vl : Timeless (l ↦∗ vl).
  Proof. rewrite /heap_mapsto_vec. apply _. Qed.

  Global Instance heap_freeable_timeless q l n : Timeless (†{q}l…n).
  Proof. rewrite heap_freeable_eq /heap_freeable_def. apply _. Qed.

  (*Lemma heap_mapsto_agree l v1 v2 : l ↦ v1 ∗ l ↦ v2 ⊢ ⌜v1 = v2⌝.
  Proof.
    rewrite heap_mapsto_eq -own_op -auth_frag_op own_valid discrete_valid.
    eapply pure_elim; [done|]=> /auth_frag_valid /=.
    rewrite singleton_op -pair_op singleton_valid=> -[? /to_agree_op_inv_L->]; eauto.
  Qed.*)

  Lemma heap_mapsto_vec_nil l : l ↦∗ [] ⊣⊢ True.
  Proof. by rewrite /heap_mapsto_vec. Qed.
  
  Lemma heap_mapsto_fancy_vec_nil l : l ↦!∗ [] ⊣⊢ True.
  Proof. done. Qed.

  Lemma heap_mapsto_vec_app l vl1 vl2 :
    l ↦∗ (vl1 ++ vl2) ⊣⊢ l ↦∗ vl1 ∗ (l +ₗ length vl1) ↦∗ vl2.
  Proof.
    rewrite /heap_mapsto_vec big_sepL_app.
    do 2 f_equiv. intros k v. by rewrite shift_loc_assoc_nat.
  Qed.

  Lemma heap_mapsto_vec_singleton l v : l ↦∗ [v] ⊣⊢ l ↦ v.
  Proof. by rewrite /heap_mapsto_vec /= shift_loc_0 right_id. Qed.

  Lemma heap_mapsto_vec_cons l v vl:
    l ↦∗ (v :: vl) ⊣⊢ l ↦ v ∗ (l +ₗ 1) ↦∗ vl.
  Proof.
    by rewrite (heap_mapsto_vec_app l [v] vl) heap_mapsto_vec_singleton.
  Qed.

(*
  Lemma heap_mapsto_vec_op l vl1 vl2 :
    length vl1 = length vl2 →
    l ↦∗ vl1 ∗ l ↦∗ vl2 ⊣⊢ ⌜vl1 = vl2⌝ ∧ l ↦∗ vl1.
  Proof.
    intros Hlen%Forall2_same_length. apply (anti_symm (⊢)).
    - revert l. induction Hlen as [|v1 v2 vl1 vl2 _ _ IH]=> l.
      { rewrite !heap_mapsto_vec_nil. iIntros "_"; auto. }
      rewrite !heap_mapsto_vec_cons. iIntros "[[Hv1 Hvl1] [Hv2 Hvl2]]".
      iDestruct (IH (l +ₗ 1) with "[$Hvl1 $Hvl2]") as "[% $]"; subst.
      rewrite (inj_iff (.:: vl2)).
      iDestruct (heap_mapsto_agree with "[$Hv1 $Hv2]") as %<-.
      iSplit; first done. iFrame.*)
    (*- by iIntros "[% [$ Hl2]]"; subst.
  Qed.*)

  (*Lemma heap_mapsto_pred_op l q1 q2 n (Φ : list val → iProp Σ) :
    (∀ vl, Φ vl -∗ ⌜length vl = n⌝) →
    l ↦∗{q1}: Φ ∗ l ↦∗{q2}: (λ vl, ⌜length vl = n⌝) ⊣⊢ l ↦∗{q1+q2}: Φ.
  Proof.
    intros Hlen. iSplit.
    - iIntros "[Hmt1 Hmt2]".
      iDestruct "Hmt1" as (vl) "[Hmt1 Hown]". iDestruct "Hmt2" as (vl') "[Hmt2 %]".
      iDestruct (Hlen with "Hown") as %?.
      iCombine "Hmt1" "Hmt2" as "Hmt". rewrite heap_mapsto_vec_op; last congruence.
      iDestruct "Hmt" as "[_ Hmt]". iExists vl. by iFrame.
    - iIntros "Hmt". iDestruct "Hmt" as (vl) "[[Hmt1 Hmt2] Hown]".
      iDestruct (Hlen with "Hown") as %?.
      iSplitL "Hmt1 Hown"; iExists _; by iFrame.
  Qed.*)

  (*Lemma heap_mapsto_pred_wand l q Φ1 Φ2 :
    l ↦∗{q}: Φ1 -∗ (∀ vl, Φ1 vl -∗ Φ2 vl) -∗ l ↦∗{q}: Φ2.
  Proof.
    iIntros "Hm Hwand". iDestruct "Hm" as (vl) "[Hm HΦ]". iExists vl.
    iFrame "Hm". by iApply "Hwand".
  Qed.*)

  (*Lemma heap_mapsto_pred_iff_proper l q Φ1 Φ2 :
    □ (∀ vl, Φ1 vl ↔ Φ2 vl) -∗ □ (l ↦∗{q}: Φ1 ↔ l ↦∗{q}: Φ2).
  Proof.
    iIntros "#HΦ !>". iSplit; iIntros; iApply (heap_mapsto_pred_wand with "[-]"); try done; [|];
    iIntros; by iApply "HΦ".
  Qed.*)

  (*Lemma heap_mapsto_vec_combine l q vl :
    vl ≠ [] →
    l ↦∗{q} vl ⊣⊢ own heap_name (◯ [^op list] i ↦ v ∈ vl,
      {[l +ₗ i := (q, Cinr 0%nat, to_agree v)]}).
  Proof.
    rewrite /heap_mapsto_vec heap_mapsto_eq /heap_mapsto_def /heap_mapsto_st=>?.
    rewrite (big_opL_commute auth_frag) big_opL_commute1 //.
  Qed.*)

  (*Global Instance heap_mapsto_pred_fractional l (P : list val → iProp Σ):
    (∀ vl, Persistent (P vl)) → Fractional (λ q, l ↦∗{q}: P)%I.
  Proof.
    intros p q q'. iSplit.
    - iIntros "H". iDestruct "H" as (vl) "[[Hown1 Hown2] #HP]".
      iSplitL "Hown1"; eauto.
    - iIntros "[H1 H2]". iDestruct "H1" as (vl1) "[Hown1 #HP1]".
      iDestruct "H2" as (vl2) "[Hown2 #HP2]".
      set (ll := min (length vl1) (length vl2)).
      rewrite -[vl1](firstn_skipn ll) -[vl2](firstn_skipn ll) 2!heap_mapsto_vec_app.
      iDestruct "Hown1" as "[Hown1 _]". iDestruct "Hown2" as "[Hown2 _]".
      iCombine "Hown1" "Hown2" as "Hown". rewrite heap_mapsto_vec_op; last first.*)
  (*
      { rewrite !firstn_length. subst ll.
        rewrite -!min_assoc min_idempotent min_comm -min_assoc min_idempotent min_comm. done. }
      iDestruct "Hown" as "[H Hown]". iDestruct "H" as %Hl. iExists (take ll vl1). iFrame.
      destruct (min_spec (length vl1) (length vl2)) as [[Hne Heq]|[Hne Heq]].
      + iClear "HP2". rewrite take_ge; last first.
        { rewrite -Heq /ll. done. }
        rewrite drop_ge; first by rewrite app_nil_r. by rewrite -Heq.
      + iClear "HP1". rewrite Hl take_ge; last first.
        { rewrite -Heq /ll. done. }
        rewrite drop_ge; first by rewrite app_nil_r. by rewrite -Heq.
  Qed. *)
  (*
  Global Instance heap_mapsto_pred_as_fractional l q (P : list val → iProp Σ):
    (∀ vl, Persistent (P vl)) → AsFractional (l ↦∗{q}: P) (λ q, l ↦∗{q}: P)%I q.
  Proof. split; first done. apply _. Qed.*)

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

  (** Weakest precondition *)
  Lemma heap_alloc_vs (σ : state') l n :
    (∀ m : Z, σ !! (l +ₗ m) = None) →
    heap_maps_ctx σ ⊢
    |==> heap_maps_ctx (init_mem l n σ)
       ∗ l ↦∗ (repeat (LitV LitPoison) n).
  Proof.
    generalize l. clear l. induction n.
     - iIntros. iFrame. iModIntro. by rewrite /heap_mapsto_vec.
     - iIntros (l all) "σ". iMod (IHn (l +ₗ 1) with "σ") as "[σ rep]".
        + intros m. rewrite shift_loc_assoc. apply all.
        + iDestruct "σ" as (σL σB) "(%Hr & σ & σB)".
          have Hfresh : init_mem (l +ₗ 1) n σ !! l = None.
          { rewrite lookup_init_mem_ne /=; last lia. rewrite -(shift_loc_0 l). apply all. }
          destruct (phys_rel_None _ _ _ _ Hr Hfresh) as [HL HB].
          iMod (non_atomic_map_insert _ l (LitV LitPoison) with "σ") as "[pt σ]"; first done.
           * iFrame. iSplitR.
             { iPureIntro. by apply (phys_rel_L_insert _ _ _ _ _ (LitV LitPoison)). }
             rewrite /heap_mapsto_vec. simpl. rewrite shift_loc_0.
             rewrite /heap_mapsto. iFrame. setoid_rewrite shift_loc_assoc.
             assert (∀ (i: nat) , (1 + i) = (S i)) as Hi by lia. setoid_rewrite Hi.
             iFrame. done.
  Qed.

  Lemma heap_alloc (σ: state) l n :
    0 < n →
    (∀ m, σ.1 !! (l +ₗ m) = None) →
    heap_ctx σ ==∗
      heap_ctx (init_mem l (Z.to_nat n) $σ σ) ∗ †l…(Z.to_nat n) ∗
      l ↦∗ repeat (LitV LitPoison) (Z.to_nat n).
  Proof.
    intros ??; iDestruct 1 as (hF) "(Hvalσ & HhF & % & ato)".
    assert (Z.to_nat n ≠ O). { rewrite -(Nat2Z.id 0)=>/Z2Nat.inj. lia. }
    iMod (heap_alloc_vs _ _ (Z.to_nat n) with "[$Hvalσ]") as "[Hvalσ Hmapsto]"; first done.
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

  Lemma heap_free_vs (σ : state') l vl E :
    ↑naN ⊆ E →
    heap_maps_ctx σ ∗ l ↦∗ vl
    ⊢ |={E}=> heap_maps_ctx (free_mem l (length vl) σ).
  Proof.
      intros Hmask. generalize l. clear l. induction vl.
     - iIntros (l) "[σ pt]". iFrame. iModIntro. by rewrite /heap_mapsto_vec.
     - rewrite /heap_mapsto_vec. iIntros (l) "[σ [pt ptsep]]".
       iMod (IHvl (l +ₗ 1) with "[σ ptsep]") as "σ".
        { iFrame. rewrite /heap_mapsto_vec.
          assert (∀ (i: nat), (l +ₗ 1 +ₗ i) = (l +ₗ S i)) as Hi.
            { intros i. rewrite shift_loc_assoc. f_equal. lia. }
          setoid_rewrite Hi. iFrame.
        }
       simpl. rewrite shift_loc_0 /heap_mapsto.
       iDestruct "σ" as (σL σB) "(%Hr & σ & σB)".
       iMod (non_atomic_map_delete with "pt σ") as "[%Hst σ]"; first done.
       iModIntro. iFrame. iPureIntro. apply phys_rel_L_delete; [done|].
       by eapply phys_rel_L_not_B.
  Qed.

  Lemma heap_free σ l vl (n : Z) E :
    ↑naN ⊆ E →
    n = length vl →
    heap_ctx σ -∗ l ↦∗ vl -∗ †l…(length vl)
    ={E}=∗ ⌜0 < n⌝ ∗ ⌜∀ m, is_Some (σ.1 !! (l +ₗ m)) ↔ (0 ≤ m < n)⌝ ∗
        heap_ctx (free_mem l (Z.to_nat n) $σ σ).
  Proof.
    iDestruct 1 as (hF) "(Hvalσ & HhF & REL & ato)"; iDestruct "REL" as %REL.
    iIntros "Hmt Hf". rewrite heap_freeable_eq /heap_freeable_def.
    iDestruct (own_valid_2 with "HhF Hf") as % [Hl Hv]%auth_both_valid_discrete.
    move: Hl=> /singleton_included_l [[q qs] [/leibniz_equiv_iff Hl Hq]].
    apply (Some_included_exclusive _ _) in Hq as [=<-<-]%leibniz_equiv; last first.
    { move: (Hv (l.1)). rewrite Hl. by intros [??]. }
    assert (vl ≠ []).
    { intros ->. by destruct (REL (l.1) (1%Qp, ∅)) as [[] ?]. }
    assert (0 < n) by (subst n; by destruct vl).
    iMod (heap_free_vs with "[Hmt Hvalσ]") as "Hvalσ"; first by trivial.
    { iFrame. }
    iMod (own_update_2 with "HhF Hf") as "HhF".
    { apply auth_update_dealloc, (delete_singleton_local_update _ _ _). }
    iModIntro; subst. repeat iSplit;  eauto using heap_freeable_is_Some.
    iExists _. subst. rewrite Nat2Z.id. iFrame.
    eauto using heap_freeable_rel_free_mem.
  Qed.

  (** Legacy operations, through the physical relation *)
  Lemma heap_atomic_read (σ : state') l cells v E G d :
    ↑naN ⊆ E →
    £(d) -∗ (G &&{↑naN;d}&&> (l ↦[^ cells] v)) -∗ G -∗ heap_maps_ctx σ ={E}=∗
      ∃ n, ⌜σ !! l = Some (RSt n, word_to_byte v)⌝ ∗ G ∗ heap_maps_ctx σ.
  Proof.
    iIntros (Hmask) "£ #Gv G (%σL & %σB & %Hr & σ & σB)".
    iMod (atomic_read with "£ [Gv] G σ") as (n) "[%Heq [G σ]]"; [done|by iFrame "Gv"|].
    iModIntro. iExists n. iFrame. iPureIntro. split; [|done]. by eapply phys_rel_lookup_L.
  Qed.

  Lemma heap_na_read_begin (σ : state') l cells v E G d :
    ↑naN ⊆ E →
    £(3*d) -∗ (G &&{↑naN;d}&&> (l ↦[^ cells] v)) -∗ G -∗ heap_maps_ctx σ ={E}=∗
      ∃ n, ⌜σ !! l = Some (RSt n, word_to_byte v)⌝
        ∗ points_to_r_intermediate heap_name l cells v G
        ∗ heap_maps_ctx (<[l := (RSt (n + 1), word_to_byte v)]> σ).
  Proof.
    iIntros (Hmask) "£ #Gv G (%σL & %σB & %Hr & σ & σB)".
    iMod (na_read_begin with "£ [Gv] G σ") as (n) "[%Heq [rim σ]]"; [done|by iFrame "Gv"|].
    iModIntro. iExists n. iFrame. iPureIntro. split; [by eapply phys_rel_lookup_L|].
    apply phys_rel_L_insert; [done|]. by eapply phys_rel_L_not_B.
  Qed.

  Lemma heap_na_read_end (σ : state') l cells v E G :
    ↑naN ⊆ E →
    points_to_r_intermediate heap_name l cells v G -∗ heap_maps_ctx σ -∗ ▷ |={E}=>
      ∃ n, ⌜σ !! l = Some (RSt n, word_to_byte v) ∧ n ≥ 1⌝ ∗ G
        ∗ heap_maps_ctx (<[l := (RSt (n - 1), word_to_byte v)]> σ).
  Proof.
    iIntros (Hmask) "rim (%σL & %σB & %Hr & σ & σB)".
    iDestruct (na_read_end with "rim σ") as "A"; [done|]. iNext.
    iMod "A" as (n) "([%Heq %Hn] & G & σ)". iModIntro. iExists n. iFrame.
    iPureIntro. split; [split; [by eapply phys_rel_lookup_L|done]|].
    apply phys_rel_L_insert; [done|]. by eapply phys_rel_L_not_B.
  Qed.

(*
  Lemma heap_mapsto_lookup σ l ls q v :
    own heap_name (● to_heap σ) -∗
    own heap_name (◯ {[ l := (q, to_lock_stateR ls, to_agree v) ]}) -∗
    ⌜∃ n' : nat,
        σ !! l = Some (match ls with RSt n => RSt (n+n') | WSt => WSt end, v)⌝.
  Proof.
    iIntros "H● H◯".
    iDestruct (own_valid_2 with "H● H◯") as %[Hl?]%auth_both_valid_discrete.
    iPureIntro. move: Hl=> /singleton_included_l [[[q' ls'] dv]].
    rewrite /to_heap lookup_fmap fmap_Some_equiv.
    move=> [[[ls'' v'] [?[[/=??]->]]]]; simplify_eq.
    move=> /Some_pair_included_total_2
      [/Some_pair_included [_ Hincl] /to_agree_included->].
    destruct ls as [|n], ls'' as [|n''],
       Hincl as [[[|n'|]|] [=]%leibniz_equiv]; subst.
    - by exists O.
    - eauto.
    - exists O. by rewrite Nat.add_0_r.
  Qed.

  Lemma heap_mapsto_lookup_1 σ l ls v :
    own heap_name (● to_heap σ) -∗
    own heap_name (◯ {[ l := (1%Qp, to_lock_stateR ls, to_agree v) ]}) -∗
    ⌜σ !! l = Some (ls, v)⌝.
  Proof.
    iIntros "H● H◯".
    iDestruct (own_valid_2 with "H● H◯") as %[Hl?]%auth_both_valid_discrete.
    iPureIntro. move: Hl=> /singleton_included_l [[[q' ls'] dv]].
    rewrite /to_heap lookup_fmap fmap_Some_equiv.
    move=> [[[ls'' v'] [?[[/=??]->]]] Hincl]; simplify_eq.
    apply (Some_included_exclusive _ _) in Hincl as [? Hval]; last by destruct ls''.
    apply (inj to_agree) in Hval. fold_leibniz. subst.
    destruct ls, ls''; rewrite ?Nat.add_0_r; naive_solver.
  Qed.
  *)

  (*Lemma heap_read_vs σ n1 n2 nf l q v:
    σ !! l = Some (RSt (n1 + nf), v) →
    non_atomic_map heap_name σ ⊢ heap_mapsto_st (RSt n1) l q v
    -∗ |==> non_atomic_map heap_name (<[l:=(RSt (n2 + nf), v)]> σ)
        ∗ heap_mapsto_st (RSt n2) l q v.
  Proof.
    intros Hσv. iIntros "H● H◯".
    iMod (own_update_2 _ _ _ (● to_heap (<[l:=(RSt (n2 + nf), b)]> σB) ⋅
      ◯ {[l := (q, to_lock_stateR (RSt n2), to_agree b)]}) with "H● H◯") as "[$ $]"; [|done].
    rewrite to_heap_insert. eapply auth_update, singleton_local_update.
    { by rewrite /to_heap lookup_fmap Hσv. }
    apply prod_local_update_1, prod_local_update_2, csum_local_update_r.
    apply nat_local_update; lia.
  Qed. 
  *)

  Lemma heap_read σ l cells v E :
    ↑naN ⊆ E →
    heap_ctx σ -∗ l ↦[^ cells] v ={E}=∗
    heap_ctx σ ∗ l ↦[^ cells] v ∗ ∃ n, ⌜σ.1 !! l = Some (RSt n, word_to_byte v)⌝.
  Proof.
    iDestruct 1 as (hF) "(Hσ & HhF & REL)". iIntros "Hmt".
    iMod (lc_zero) as "£0".
    iMod (heap_atomic_read with "£0 [] Hmt Hσ") as (n) "[X [Hmt Hσ]]"; first by set_solver.
      { iApply guards_refl. }
    iModIntro. iFrame.
  Qed.

  (*Lemma heap_read_1 σ l cells v E :
    ↑naN ⊆ E →
    heap_ctx σ -∗ l ↦[^ cells] v ={E}=∗
    heap_ctx σ ∗ l ↦[^ cells] v ∗ ⌜σ !! l = Some (RSt 0, v)⌝.
  Proof.
    iDestruct 1 as (hF) "(Hσ & HhF & REL)". iIntros "Hmt".
    iMod (points_to_heap_reading0 with "Hmt Hσ") as "(Hmt & Hσ & Heq0)"; first by trivial.
    iModIntro. iFrame.
  Qed.*)

(*
  Lemma heap_read_na σ l q v :
    heap_ctx σ -∗ l ↦{q} v ==∗ ∃ n,
      ⌜σ !! l = Some (RSt n, v)⌝ ∗
      heap_ctx (<[l:=(RSt (S n), v)]> σ) ∗
      ∀ σ2, heap_ctx σ2 ==∗ ∃ n2, ⌜σ2 !! l = Some (RSt (S n2), v)⌝ ∗
        heap_ctx (<[l:=(RSt n2, v)]> σ2) ∗ l ↦{q} v.
  Proof.
    iDestruct 1 as (hF) "(Hσ & HhF & %)"; iIntros "Hmt".
    rewrite heap_mapsto_eq.
    iDestruct (heap_mapsto_lookup with "Hσ Hmt") as %[n Hσl]; eauto.
    iMod (heap_read_vs _ 0 1 with "Hσ Hmt") as "[Hσ Hmt]"; first done.
    iModIntro. iExists n; iSplit; [done|]. iSplitL "HhF Hσ".
    { iExists hF. iFrame. eauto using heap_freeable_rel_stable. }
    clear dependent n σ hF. iIntros (σ2). iDestruct 1 as (hF) "(Hσ & HhF & %)".
    iDestruct (heap_mapsto_lookup with "Hσ Hmt") as %[n Hσl]; eauto.
    iMod (heap_read_vs _ 1 0 with "Hσ Hmt") as "[Hσ Hmt]"; first done.
    iExists n; iModIntro; iSplit; [done|]. iFrame "Hmt".
    iExists hF. iFrame. eauto using heap_freeable_rel_stable.
  Qed.

  Lemma heap_write_vs σ st1 st2 l v v':
    σ !! l = Some (st1, v) →
    own heap_name (● to_heap σ) ⊢ heap_mapsto_st st1 l 1%Qp v
    ==∗ own heap_name (● to_heap (<[l:=(st2, v')]> σ))
        ∗ heap_mapsto_st st2 l 1%Qp v'.
  Proof.
    intros Hσv. iIntros "H● H◯".
    iMod (own_update_2 _ _ _ (● to_heap (<[l:=(st2, b')]> σB) ⋅
      ◯ {[l := (1%Qp, to_lock_stateR st2, to_agree b')]}) with "H● H◯") as "[$ $]"; [|done].
    rewrite to_heap_insert. eapply auth_update, singleton_local_update.
    { by rewrite /to_heap lookup_fmap Hσv. }
    apply exclusive_local_update. by destruct st2.
  Qed.

  Lemma heap_write σ l v v' :
    heap_ctx σ -∗ l ↦ v ==∗ heap_ctx (<[l:=(RSt 0, v')]> σ) ∗ l ↦ v'.
  Proof.
    iDestruct 1 as (hF) "(Hσ & HhF & %)". iIntros "Hmt".
    rewrite heap_mapsto_eq.
    iDestruct (heap_mapsto_lookup_1 with "Hσ Hmt") as %?; auto.
    iMod (heap_write_vs with "Hσ Hmt") as "[Hσ $]"; first done.
    iModIntro. iExists _. iFrame. eauto using heap_freeable_rel_stable.
  Qed.

  Lemma heap_write_na σ l v v' :
    heap_ctx σ -∗ l ↦ v ==∗
      ⌜σ !! l = Some (RSt 0, v)⌝ ∗
      heap_ctx (<[l:=(WSt, v)]> σ) ∗
      ∀ σ2, heap_ctx σ2 ==∗ ⌜σ2 !! l = Some (WSt, v)⌝ ∗
        heap_ctx (<[l:=(RSt 0, v')]> σ2) ∗ l ↦ v'.
  Proof.
    iDestruct 1 as (hF) "(Hσ & HhF & %)"; iIntros "Hmt".
    rewrite heap_mapsto_eq.
    iDestruct (heap_mapsto_lookup_1 with "Hσ Hmt") as %?; eauto.
    iMod (heap_write_vs with "Hσ Hmt") as "[Hσ Hmt]"; first done.
    iModIntro. iSplit; [done|]. iSplitL "HhF Hσ".
    { iExists hF. iFrame. eauto using heap_freeable_rel_stable. }
    clear dependent σ hF. iIntros (σ2). iDestruct 1 as (hF) "(Hσ & HhF & %)".
    iDestruct (heap_mapsto_lookup with "Hσ Hmt") as %[n Hσl]; eauto.
    iMod (heap_write_vs with "Hσ Hmt") as "[Hσ Hmt]"; first done.
    iModIntro; iSplit; [done|]. iFrame "Hmt".
    iExists hF. iFrame. eauto using heap_freeable_rel_stable.
  Qed.
  *)

    Definition is_concrete (fv: fancy_val) : Prop :=
      match fv with
        | FVal _ => True
        | FCell _ => False
      end.

  Fixpoint all_concrete (l: list fancy_val) : Prop := 
    match l with
      | [] => True
      | v :: l' => is_concrete v ∧ all_concrete l'
    end.
  
  Lemma heap_complete_mapsto_singleton l₀ c₀ :
      ((l₀, [c₀]) #↦∗_) ⊣⊢ ((l₀, c₀) #↦_).
  Proof.
    apply sep_True. apply _.
  Qed.
  
  Lemma heap_complete_mapsto_val_singleton l₀ c₀ v :
      ((l₀, [c₀]) #↦∗ [v]) ⊣⊢ ((l₀, c₀) #↦ v).
  Proof.
    apply sep_True. apply _.
  Qed.
  
  Lemma heap_complete_mapsto_fancy_singleton l₀ c₀ v :
      ((l₀, [c₀]) #↦!∗ [v]) ⊣⊢ ((l₀, c₀) #↦! v).
  Proof.
    apply sep_True. apply _.
  Qed.
  
  Lemma all_concrete_app (l l' : list fancy_val) : all_concrete l ∧ all_concrete l' ↔ all_concrete (l ++ l').
  Proof.
    induction l; simpl; intuition.
  Qed.

  Lemma all_concrete_take l n : all_concrete l → all_concrete (take n l).
  Proof.
    move: l. elim: n=>//= ? IH [|??]//= [??]. split=>//. by apply IH.
  Qed.

  Lemma all_concrete_repeat v n : is_concrete v → all_concrete (repeat v n).
  Proof. move=> ?. by elim: n. Qed.
  
  Definition to_concrete (l: list fancy_val) : list val := (λ fv, match fv with FVal v => v | FCell _ => inhabitant end) <$> l.
  
  Lemma fmap_to_concrete (l: list fancy_val) :
    all_concrete l → fmap FVal (to_concrete l) = l.
  Proof.
    induction l as [|a l]; first done. destruct a.
      - intros [_ Ha]. simpl. unfold fmap in IHl. rewrite IHl; trivial.
      - simpl. intuition.
  Qed.
  
  Lemma length_to_concrete (l: list fancy_val) :
    length (to_concrete l) = length l.
  Proof.
    induction l; first done. simpl. rewrite IHl. trivial.
  Qed.
  
  Lemma heap_mapsto_cells_fancy_fmap_eq l c v
    : l ↦[^ c ]!∗ (fmap FVal v) ⊣⊢ l ↦[^ c ]∗ v.
  Proof. done. Qed.
    
  Lemma heap_complete_mapsto_fancy_fmap_eq l v
    : l #↦!∗ (fmap FVal v) ⊣⊢ l #↦∗ v.
  Proof. done. Qed.

  Lemma all_concrete_fmap_fval vl : all_concrete (FVal <$> vl).
  Proof.
    induction vl; first done. split; first done. apply IHvl.
  Qed.
  
  Lemma heap_mapsto_fancy_vec_cons l fv fvs
    : l ↦!∗ (fv :: fvs) ⊣⊢ l ↦! fv ∗ ((l +ₗ 1) ↦!∗ fvs).
  Proof. done. Qed.
  
  Lemma heap_mapsto_val_vec_cons l fv fvs
    : l ↦∗ (fv :: fvs) ⊣⊢ l ↦ fv ∗ ((l +ₗ 1) ↦∗ fvs).
  Proof. unfold heap_mapsto_vec. rewrite big_sepL_cons.
    rewrite shift_loc_0.
    assert (∀ (i: nat), (l +ₗ 1 +ₗ i) = (l +ₗ S i)) as X. {
      intros i. rewrite shift_loc_assoc. f_equal. lia.
    }
    setoid_rewrite X. done.
  Qed.
  
  Lemma heap_mapsto_cells_fancy_vec_cons l c cs fv fvs
    : l ↦[^ c :: cs ]!∗ (fv :: fvs) ⊣⊢ l ↦[^ c]! fv ∗ ((l +ₗ 1) ↦[^ cs]!∗ fvs).
  Proof. done. Qed.
  
  Lemma heap_mapsto_cells_val_vec_cons l c cs v vs
    : l ↦[^ c :: cs ]∗ (v :: vs) ⊣⊢ l ↦[^ c] v ∗ ((l +ₗ 1) ↦[^ cs]∗ vs).
  Proof. done. Qed.
  
  Lemma heap_mapsto_cloc_fancy_vec_cons l c cs fv fvs
    : (l, c :: cs) #↦!∗ (fv :: fvs) ⊣⊢
        (l, c) #↦! fv ∗ ((l +ₗ 1), cs) #↦!∗ fvs.
  Proof. done. Qed.
  
  Lemma heap_mapsto_cloc_val_vec_cons l c cs v vs
    : (l, c :: cs) #↦∗ (v :: vs) ⊣⊢
        (l, c) #↦ v ∗ ((l +ₗ 1), cs) #↦∗ vs.
  Proof. done. Qed.
  
  Lemma heap_mapsto_cloc_vals_vec_cons l c cs v vs
    : (l, c :: cs) #↦∗ (v :: vs) ⊣⊢
        (l, c) #↦ v ∗ ((l +ₗ 1), cs) #↦∗ vs.
  Proof. done. Qed.
  
  Lemma heap_mapsto_cloc_emp_cons l c cs
    : (l, c :: cs) #↦∗_ ⊣⊢ (l, c) #↦_ ∗ ((l +ₗ 1), cs) #↦∗_.
  Proof. done. Qed.
  
  Lemma heap_cloc_mapsto_fancy_empty l lv :
      l ↦!∗ lv ⊣⊢ (l, repeat [] (length lv)) #↦!∗ lv.
  Proof.
      generalize l. clear l. induction lv; first done. intros l.
      rewrite heap_mapsto_fancy_vec_cons.
      rewrite length_cons.
      replace (repeat [] (S (length lv)) : list (list cell_id)) with (([] :: repeat [] (length lv)) : list (list cell_id)) by done. rewrite heap_mapsto_cloc_fancy_vec_cons.
      rewrite IHlv. done.
  Qed.
  
  Lemma heap_cloc_mapsto_val_empty l lv :
      l ↦∗ lv ⊣⊢ (l, repeat [] (length lv)) #↦∗ lv.
  Proof.
  induction lv in l |- *.
  - rewrite heap_mapsto_vec_nil. 
    rewrite /heap_complete_mapsto_val_vec.
    cbn[fmap list_fmap].
    rewrite -(heap_cloc_mapsto_fancy_empty _ []).
    rewrite heap_mapsto_fancy_vec_nil.
    done.
  - rewrite heap_mapsto_val_vec_cons /=.
    rewrite heap_mapsto_cloc_vals_vec_cons.
    rewrite IHlv.
    rewrite -heap_complete_mapsto_fancy_singleton.
    change [[]] with (@repeat (list cell_id) [] (length [FVal a])).
    rewrite -heap_cloc_mapsto_fancy_empty.
    rewrite heap_mapsto_fancy_vec_cons.
    iSplit => //.
    + iIntros "[Hhead $]". iSplit => //.
    + iIntros "[[? ?] $]" => //.
  Qed.

  Lemma heap_mapsto_cells_fancy_empty l lv :
      l ↦!∗ lv ⊣⊢ l ↦[^ repeat [] (length lv)]!∗ lv.
  Proof. done. Qed.
      
  Lemma heap_mapsto_cells_empty l lv :
      l ↦∗ lv ⊣⊢ l ↦[^ repeat [] (length lv)]∗ lv.
  Proof.
      generalize l. clear l. induction lv; first done. intros l.
      rewrite heap_mapsto_val_vec_cons. rewrite IHlv. done.
  Qed.
  
  Lemma heap_cloc_mapsto_empty l len :
      True ⊣⊢ (l, repeat [] len) #↦∗_.
  Proof.
      generalize l. clear l. induction len; first done.
      intros l. simpl. rewrite heap_mapsto_cloc_emp_cons.
      rewrite <- IHlen. rewrite sep_True. done.
  Qed.
      
  Lemma heap_mapsto_fancy_fmap_eq l v
    : l ↦!∗ (fmap FVal v) ⊣⊢ l ↦∗ v.
  Proof.
      generalize l; clear l; induction v; first done. intros l.
      rewrite heap_mapsto_vec_cons. rewrite <- IHv. done.
  Qed.
  
  Lemma heap_cloc_mapsto_fancy_fmap_eq l v
    : l #↦!∗ (fmap FVal v) ⊣⊢ l #↦∗ v.
  Proof. done. Qed.
    
  Lemma heap_mapsto_cells_fancy_vec_nil l : l ↦[^ []]!∗ [] ⊣⊢ True.
  Proof. done. Qed.

  Definition cloc_take (l: cloc) (n: nat) : cloc := (l.1, take n l.2).
  Definition cloc_skip (l: cloc) (n: nat) : cloc := (l.1 +ₗ n, skipn n l.2).

  Lemma heap_mapsto_fancy_vec_app l vl1 vl2 :
    l ↦!∗ (vl1 ++ vl2) ⊣⊢ l ↦!∗ vl1 ∗ (l +ₗ length vl1) ↦!∗ vl2.
  Proof.
    generalize l. clear l. induction vl1; intros l.
      - simpl. rewrite shift_loc_0. rewrite heap_mapsto_fancy_vec_nil.
        rewrite bi.sep_comm. rewrite bi.sep_True. done.
      - simpl. do 2 rewrite heap_mapsto_fancy_vec_cons.
        rewrite IHvl1. rewrite shift_loc_assoc.
        replace (Z.of_nat (S (length vl1))) with (1 + (length vl1)) by lia.
        iSplit. { iIntros "[a [b c]]". iFrame. } { iIntros "[a b]". iFrame. }
  Qed.
    
  Lemma heap_cloc_mapsto_emp_vec_app (l: cloc) (n: nat) :
    l #↦∗_ ⊣⊢ (cloc_take l n) #↦∗_ ∗ (cloc_skip l n) #↦∗_.
  Proof.
    destruct l as [l cells]. simpl. generalize l, cells. clear l. clear cells. induction n.
       - intros l cells.
         replace (cloc_take (l, cells) 0) with ((l, []) : cloc) by done.
         unfold cloc_skip. rewrite drop_0. rewrite shift_loc_0.
         rewrite bi.sep_comm. rewrite bi.sep_True. done.
       - intros l cells. destruct cells as [|cells].
         { unfold cloc_take, cloc_skip. simpl. iSplit; done. }
         replace (cloc_take (l, cells :: cells0) (S n)) with
                 (l, cells :: take n cells0) by done.
         do 2 rewrite heap_mapsto_cloc_emp_cons.
         replace (cloc_skip (l, cells :: cells0) (S n)) with (cloc_skip (l +ₗ 1, cells0) n).
         2: { simpl. unfold cloc_skip. f_equal. simpl. rewrite shift_loc_assoc. f_equal. lia. }
         rewrite IHn.
         iSplit. { iIntros "[a [b c]]". iFrame. } { iIntros "[a b]". iFrame. }
  Qed.
    
  Lemma heap_cloc_mapsto_fancy_vec_app (l: cloc) vl1 vl2 :
    l #↦!∗ (vl1 ++ vl2) ⊣⊢ (cloc_take l (length vl1)) #↦!∗ vl1 ∗ (cloc_skip l (length vl1)) #↦!∗ vl2.
  Proof.
    destruct l as [l cells]. simpl. generalize l, cells. clear l. clear cells. induction vl1.
       - intros l cells.
         replace (cloc_take (l, cells) 0) with ((l, []) : cloc) by done.
         unfold cloc_skip. rewrite drop_0. rewrite shift_loc_0.
         rewrite bi.sep_comm. rewrite bi.sep_True. done.
       - intros l cells. destruct cells as [|cells].
         { iSplit. { iIntros "a". iExFalso. iFrame. }
           { iIntros "[a b]". iExFalso. iFrame. } }
         replace (cloc_take (l, cells :: cells0) (length (a :: vl1))) with
                 (l, cells :: take (length vl1) cells0) by done.
         rewrite heap_mapsto_cloc_fancy_vec_cons. 
         replace ((a :: vl1) ++ vl2) with (a :: (vl1 ++ vl2)) by done.
         rewrite heap_mapsto_cloc_fancy_vec_cons.
         replace (cloc_skip (l, cells :: cells0) (length (a :: vl1))) with (cloc_skip (l +ₗ 1, cells0) (length vl1)).
         2: { simpl. unfold cloc_skip. f_equal. simpl. rewrite shift_loc_assoc. f_equal. lia. }
         rewrite IHvl1.
         iSplit. { iIntros "[a [b c]]". iFrame. } { iIntros "[a b]". iFrame. }
  Qed.
  
  Lemma heap_mapsto_cells_fancy_vec_app' l vl1 vl2 cells :
    l ↦[^ cells]!∗ (vl1 ++ vl2) ⊣⊢ l ↦[^ take (length vl1) cells]!∗ vl1 ∗ (l +ₗ length vl1) ↦[^ skipn (length vl1) cells]!∗ vl2.
  Proof.
    generalize l. clear l. generalize cells. clear cells. induction vl1; intros cells l.
      - simpl. rewrite shift_loc_0. replace (drop 0 cells) with cells by trivial.
        rewrite bi.sep_comm. rewrite bi.sep_True. done.
      - simpl. destruct cells as [|cells0 cells].
        + simpl. iSplit. { iIntros. done. } { iIntros "[? _]". done. }
        + replace (take (S (length vl1)) (cells0 :: cells)) with (cells0 :: take (length vl1) cells) by trivial.
          do 2 rewrite heap_mapsto_cells_fancy_vec_cons.
          rewrite IHvl1. rewrite shift_loc_assoc.
          replace (Z.of_nat (S (length vl1))) with (Z.add 1 (Z.of_nat (length vl1))) by lia.
          replace ((S (length vl1))) with (1 + (length vl1))%nat by lia.
          replace (drop (1 + length vl1) (cells0 :: cells)) with (drop (length vl1) cells) by trivial.
          iSplit. { iIntros "[a [b c]]". iFrame. } { iIntros "[a b]". iFrame. }
  Qed.
  
  Lemma heap_mapsto_cells_fancy_vec_app l vl1 vl2 :
    l.1 ↦[^ l.2]!∗ (vl1 ++ vl2) ⊣⊢
        (l.1 ↦[^ take (length vl1) l.2]!∗ vl1) ∗ ((l.1 +ₗ length vl1) ↦[^ skipn (length vl1) l.2]!∗ vl2).
  Proof. apply heap_mapsto_cells_fancy_vec_app'. Qed.
  
  Lemma heap_cloc_mapsto_fancy_vec_length_eq l vl :
      l #↦!∗ vl ⊢ ⌜ length l.2 = length vl⌝.
  Proof.
      destruct l as [l c]. simpl. generalize l, c. clear l. clear c. induction vl.
        - intros l c. destruct c.
          + iIntros. iPureIntro. done.
          + iIntros "A". iExFalso. iFrame.
        - intros l c. destruct c.
          + iIntros "A". iExFalso. iFrame.
          + rewrite heap_mapsto_cloc_fancy_vec_cons. iIntros "[A B]".
            iDestruct (IHvl with "B") as "%Hlen".
            iPureIntro. simpl. rewrite Hlen; trivial.
  Qed.

  Lemma cells_points_to_fancy_value_vec_cons γ γs fv fvs
    : (γ :: γs) ^↦!∗ (fv :: fvs) ⊣⊢
        γ ^↦! fv ∗ γs ^↦!∗ fvs.
  Proof. done. Qed.

  Lemma cells_points_to_fancy_vec_length_eq cell_ids vl :
    cell_ids ^↦!∗ vl ⊢ ⌜ length cell_ids = length vl ⌝.
  Proof.
    induction cell_ids as [ | ?? IH ] in vl |- *.
    - destruct vl => //.
      + iIntros. iPureIntro. done.
      + iIntros "A". iExFalso. iFrame.
    - destruct vl.
      + iIntros "A". iExFalso. iFrame.
      + rewrite cells_points_to_fancy_value_vec_cons. iIntros "[A B]".
        iDestruct (IH with "B") as "%Hlen".
        iPureIntro. simpl. rewrite Hlen; trivial.
  Qed.

  Lemma heap_complete_mapsto_val_empty l
    : (l, []) #↦∗ [] ⊣⊢ True. 
  Proof.
    replace [] with (@repeat (list cell_id) [] (@length val [])) by done.
    rewrite -(heap_cloc_mapsto_val_empty).
    rewrite /heap_mapsto_vec.
    rewrite big_sepL_nil.
    done.
  Qed.
  
  Lemma heap_cloc1_mapsto_val l v
    : (l, []) #↦ v ⊣⊢ l ↦ v. 
  Proof. done. Qed.

  Lemma heap_complete_mapsto_fancy_empty l
    : (l, []) #↦!∗ [] ⊣⊢ True. 
  Proof.
    replace [] with (@repeat (list cell_id) [] (@length fancy_val [])) by done.
    rewrite -(heap_cloc_mapsto_fancy_empty).
    done.
  Qed.

  Lemma rev_snoc {A} (a : A) (l : list A) :
    rev (l ++ [a]) = a :: rev l.
  Proof.
    induction l in a |-  *; simpl; first done.
    rewrite IHl.
    done.
  Qed.

  Lemma split_at_last_snoc {A} (a : A) (l : list A) :
    split_at_last (l ++ [a]) = Some (l, a).
  Proof.
    rewrite /split_at_last.
    by rewrite rev_snoc rev_involutive.
  Qed.

  Lemma heap_mapsto_cells_to_complete_mapsto_fancy (l : cloc1) (fv : fancy_val) :
    l.1 ↦[^ l.2 ]! fv ⊣⊢ l #↦_ ∗ l #↦! fv. 
  Proof.
    destruct l as [l cell_ids]. simpl.
    rewrite /heap_mapsto_cells_fancy/heap_complete_mapsto/heap_complete_mapsto_fancy.
    destruct (decide (cell_ids = [])) as [-> | Hnempty].
    (* induction cell_ids as [ | γ cell_ids IH] using rev_ind in l, fv |- *. *)
    - simpl. iSplit. + by iIntros "$". + by iIntros "[_ $]".
    - apply exists_last in Hnempty as (cell_ids' & γ & ->).
      rewrite split_at_last_snoc/=.
      rewrite pt_seq_snoc.
      done.
  Qed.

  Lemma heap_mapsto_cells_to_complete_mapsto_fancy_vec (l : cloc) (fv : list fancy_val) :
    l.1 ↦[^ l.2 ]!∗ fv ⊣⊢ l #↦∗_ ∗ l #↦!∗ fv. 
  Proof.
    destruct l as [l list_cell_ids]. simpl.
    induction list_cell_ids as [| cell_ids list_cell_ids IH] in l, fv |- *.
    - destruct fv => //=.
      + iSplit => //.
      + iSplit => //.
        rewrite /heap_complete_mapsto_fancy_vec/heap_complete_mapsto_fancy_vec'.
        by iIntros "[_ ?]".
    - destruct fv as [| fv fvs]; simpl.
      + iSplit => //.
        * by iIntros.
        * rewrite /heap_complete_mapsto_fancy_vec/heap_complete_mapsto_fancy_vec'.
          by iIntros "[_ ?]".
      + rewrite heap_mapsto_cloc_emp_cons.
        rewrite heap_mapsto_cloc_fancy_vec_cons.
        iSplit.
        * iIntros "[Hfv Hfvs]".
          rewrite IH.
          iDestruct "Hfvs" as "[Hchain Htail]".
          iFrame.
          iPoseProof (heap_mapsto_cells_to_complete_mapsto_fancy (l, cell_ids) fv) as "H".
          iDestruct ("H" with "Hfv") as "[$ $]".
        * iIntros "[[Hchain Hchain'] [Htail Hfvs]]".
          rewrite IH.
          iFrame.
          iPoseProof (heap_mapsto_cells_to_complete_mapsto_fancy (l, cell_ids) fv) as "[_ H]".
          iDestruct ("H" with "[$]") as "?".
          by rewrite /heap_mapsto_cells_fancy/=.
  Qed.

    Lemma cell_alloc2 l fv :
    l ↦!∗ fv ==∗ ∃ γs, ⌜ length γs = length fv ⌝ ∗ l ↦[^ ((λ γ, [γ]) <$> γs) ]!∗ fv.
  Proof.
    induction fv as [ | fv fvs IH] in l |- *.
    - iIntros "? !>"; iExists []; iSplit => //.
    - rewrite heap_mapsto_fancy_vec_cons.
      iIntros "[Hfv Hfvs]".
      iMod (IH with "Hfvs") as "[%γs [%Hlen Hfvs]]".
      rewrite /heap_mapsto_fancy.
      iMod (pt_alloc_cell with "Hfv") as "[%γ Hfv]".
      iModIntro.
      iExists (γ :: γs).
      iSplit.
      1: { iPureIntro. simpl; lia. }
      rewrite fmap_cons heap_mapsto_cells_fancy_vec_cons.
      iFrame.
  Qed.

  Lemma heap_complete_mapsto_vec_eq (l : loc) (γs : list cell_id)  :
    ((l, (λ γ, [γ]) <$> γs) #↦∗_ ⊣⊢ l ↦!∗ (FCell <$> γs))%I . 
  Proof.
    induction γs as [ | γ γs IH] in l |- *; simpl.
    - change (@nil (list cell_id)) with (@repeat (list cell_id) [] 0). 
      rewrite -heap_cloc_mapsto_empty.
      rewrite heap_mapsto_fancy_vec_nil.
      done.
    - rewrite heap_mapsto_cloc_emp_cons heap_mapsto_fancy_vec_cons.
      rewrite IH.
      rewrite /fmap.
      rewrite /heap_complete_mapsto/heap_mapsto_fancy .
      simpl.
      done.
  Qed.

  Lemma heap_complete_mapsto_fancy_val_vec_eq' (l : loc) (γs : list cell_id) (fl : list fancy_val) :
    ((l, (λ γ : cell_id, [γ]) <$> γs) #↦!∗ fl ⊣⊢ γs ^↦!∗ fl).
  Proof.
    induction γs as [ | γ γs IH] in l, fl |- *; simpl.
    - destruct fl as [|fv fvs] => //=.
    - destruct fl as [|fv fvs] => //=.
      rewrite heap_mapsto_cloc_fancy_vec_cons.
      rewrite IH.
      rewrite /heap_complete_mapsto_fancy//=.
  Qed.

  Definition cloc_flat_insert (l : cloc) (γs : list cell_id) :=
    let z := zip_with (λ γ cell_ids, cell_ids ++ [γ]) γs l.2 in
    (l.1, z).

  Lemma heap_complete_mapsto_fancy_val_vec_eq'' γs cl fl :
    length cl.2 = length γs →
    γs ^↦!∗ (fl) ⊣⊢ cloc_flat_insert cl γs #↦!∗ fl.
  Proof.
    move => Hlen.
    destruct cl as [l list_cell_ids].
    induction γs as [ | γ γs IH] in l, list_cell_ids, fl,Hlen |- *; simpl.
    - destruct fl =>//.
    - destruct fl as [ | fv fvs ] => //=.
      + iSplit; first by iIntros.
        destruct list_cell_ids => //.
      + rewrite /cloc_flat_insert/=.
        destruct list_cell_ids as [ | cell_ids list_cell_ids] => //=.
        rewrite heap_mapsto_cloc_fancy_vec_cons.
        replace (_, zip_with _ _ _) with (cloc_flat_insert (l +ₗ 1, list_cell_ids) γs).
        2: by rewrite /cloc_flat_insert.
        rewrite -IH.
        2: naive_solver.
        rewrite /heap_complete_mapsto_fancy/=.
        by rewrite split_at_last_snoc.
  Qed.

  Lemma heap_fancy_mapsto_cells_length l cells fvs :
    l ↦[^ cells ]!∗ fvs ⊢ ⌜ length cells = length fvs ⌝.
  Proof.
    induction cells as [ | cell cells IH] in l, fvs |- * => //=.
    - destruct fvs => //; by iIntros "?".
    - destruct fvs => //; first by iIntros "?".
      iIntros "[head tail]".
      iDestruct (IH with "tail") as "->".
      by iPureIntro.
  Qed.

  Lemma heap_complete_mapsto_combine γs cl :
    length cl.2 = length γs →
    cl #↦∗_ ∗ cl #↦!∗ (FCell <$> γs)  ⊣⊢ cloc_flat_insert cl γs #↦∗_.
  Proof.
    move => Hlen.
    destruct cl as [l list_cell_ids].
    induction γs as [ | γ γs IH] in l, list_cell_ids, Hlen |- *; simpl.
    - destruct list_cell_ids =>//.
      rewrite /heap_complete_mapsto_vec/heap_complete_mapsto_fancy_vec/heap_complete_mapsto_vec//=.
      iSplit => //.
    - destruct list_cell_ids as [ | cell_ids list_cell_ids] => //=.
      rewrite heap_mapsto_cloc_emp_cons heap_mapsto_cloc_fancy_vec_cons.
      rewrite /cloc_flat_insert/=.
      rewrite heap_mapsto_cloc_emp_cons.
      replace (_, zip_with _ _ _) with (cloc_flat_insert (l +ₗ 1, list_cell_ids) γs).
      2: by rewrite /cloc_flat_insert.
      rewrite -IH.
      2: naive_solver.
      iSplit.
      + iIntros "((H1&H2)&H3&H4)".
        iFrame.
        rewrite {2} /heap_complete_mapsto/=. 
        rewrite split_at_last_snoc.
        iDestruct (heap_mapsto_cells_to_complete_mapsto_fancy with "[$H3 $H1]") as "Hfancy". simpl.
        rewrite /heap_mapsto_cells_fancy/=.
        done.
      + iIntros "(H1&H2&H3)".
        iFrame.
        rewrite -heap_mapsto_cells_to_complete_mapsto_fancy.
        rewrite /heap_complete_mapsto/=. 
        rewrite split_at_last_snoc.
        rewrite /heap_mapsto_cells_fancy/=.
        done.
  Qed.

  Lemma heap_mapsto_singleton l cell_ids fv :
    (l ↦[^ [cell_ids]]!∗ [fv]) ⊣⊢ (l ↦[^ cell_ids]! fv).
  Proof.
    iSplit.
    - rewrite heap_mapsto_cells_fancy_vec_cons.
      iIntros "[$ _]".
    - rewrite heap_mapsto_cells_fancy_vec_cons.
      iIntros "$".
  Qed.

  Lemma cell_points_to_fancy_fmap_eq c v
    : c ^↦! (FVal v) ⊣⊢ c ^↦ v. 
  Proof.
    rewrite /cell_points_to_fancy_value/cell_points_to_value//=.
  Qed.
  
  (* conjunction stuff *)
    
  Lemma point_prop_heap_mapsto_cells_fancy_vec l cells vl :
      factoring_props.point_prop (l ↦[^ cells ]!∗ vl).
  Proof using heapGS0 invGS0 Σ.
      generalize l, cells. clear l. clear cells. induction vl.
      - intros. apply factoring_props.point_prop_of_pers. destruct cells; apply _.
      - intros. destruct cells. { apply factoring_props.point_prop_of_pers. apply _. }
        rewrite heap_mapsto_cells_fancy_vec_cons. apply factoring_props.point_prop_sep.
          + apply pt_seq_point_prop. + apply IHvl.
  Qed.
  
  Local Definition loc_cells_fv_map (l: loc) (cells: list (list cell_id)) (fvl: list fancy_val)
      : gmap loc (list cell_id * (cell_id + val)) :=
      kmap (λ (i: nat), l +ₗ i)
        (map_seq 0 (zip_with (λ c fv, (c, fv2sum fv)) cells fvl)).
  
  Local Lemma lookup_loc_cells_fv_map (l: loc) (cells: list (list cell_id)) (fvl: list fancy_val)
      (l0: loc) (cs: list cell_id) (cv: cell_id + val) :
      loc_cells_fv_map l cells fvl !! l0 = Some (cs, cv)
      → ∃ (i: nat), l0 = l +ₗ i ∧ cells !! i = Some cs ∧ fvl !! i = Some (sum2fv cv).
  Proof.
      unfold loc_cells_fv_map. intros Ha.
      rewrite lookup_kmap_Some in Ha. destruct Ha as [i [Hl Ha]]. subst l0.
      rewrite lookup_map_seq_Some in Ha. destruct Ha as [Hi0 Ha].
      replace (i - 0)%nat with i in Ha by lia.
      rewrite lookup_zip_with_Some in Ha. destruct Ha as [cells0 [fv0 [Ha [Hb Hc]]]].
      inversion Ha. subst cs. subst cv. 
      exists i. split; first by trivial. split; first by trivial.
      rewrite Hc. destruct fv0; done.
  Qed.

  
  Local Lemma loc_cells_fv_map_cons l cell cells fv fvl :
      loc_cells_fv_map l (cell :: cells) (fv :: fvl) =
        <[ l := (cell, fv2sum fv) ]> (loc_cells_fv_map (l +ₗ 1) cells fvl).
  Proof.
    rewrite {1} /loc_cells_fv_map.
    simpl.
    rewrite kmap_insert shift_loc_0.
    f_equal.
    rewrite /loc_cells_fv_map.
    rewrite (kmap_map_seq_shift _ 1%nat).
    f_equal.
    apply FunctionalExtensionality.functional_extensionality => i.
    rewrite (shift_loc_assoc).
    f_equal; lia.
    Qed.
  
  Local Lemma loc_cells_fv_map_plus1_not_in l cells fvl :
    loc_cells_fv_map (l +ₗ 1) cells fvl !! l = None.
  Proof.
    unfold loc_cells_fv_map. rewrite lookup_kmap_None. intros i Hl.
    rewrite shift_loc_assoc in Hl.
    assert (l +ₗ 0 = l +ₗ (1 + i)) as Hl2. { rewrite shift_loc_0. trivial. }
    have Hl3 := (shift_loc_inj l _ _ Hl2). lia.
  Qed.
  
  Local Lemma sepM_loc_cells_fv_map_cons l cell cells fv fvl :
      ([∗ map] l0↦'(cells0, cv) ∈ loc_cells_fv_map l (cell :: cells) (fv :: fvl), 
          inl l0 @↦[heap_name][^cells0] cv)
      ⊢ 
      inl l @↦[heap_name][^cell] (fv2sum fv) ∗
      ([∗ map] l0↦'(cells0, cv) ∈ loc_cells_fv_map (l +ₗ 1) (cells) (fvl), 
          inl l0 @↦[heap_name][^cells0] cv).
  Proof using heapGS0 invGS0 Σ.
      rewrite loc_cells_fv_map_cons.
      rewrite big_sepM_insert; first by done.
      apply loc_cells_fv_map_plus1_not_in.
  Qed.
  
  Local Lemma sepM_entails_mapsto_cells_fancy_vec l cells fvl :
      length cells = length fvl →
      ([∗ map] l0 ↦ '(cells, cv) ∈ loc_cells_fv_map l cells fvl, (inl l0) @↦[heap_name][^ cells ] cv)
      ⊢ l ↦[^ cells ]!∗ fvl.
  Proof using heapGS0 invGS0 Σ.
      generalize l, cells. clear l. clear cells. induction fvl.
       - intros l cells Heq. simpl in Heq. rewrite length_zero_iff_nil in Heq. subst cells.
          iIntros. done.
       - intros l cells Heq. destruct cells as [|cell cells]. { simpl in Heq. lia. }
         rewrite heap_mapsto_cells_fancy_vec_cons.
         assert (length cells = length fvl) as Heq'. { simpl in Heq. lia. }
         iIntros "a". iDestruct (sepM_loc_cells_fv_map_cons with "a") as "[a b]".
         iFrame. iDestruct (IHfvl with "b") as "$". trivial.
  Qed.
  
  Lemma cloc_take_app_length l cs1 cs2 :
    cloc_take (l, cs1 ++ cs2) (length cs1) = (l, cs1).
  Proof. by rewrite /cloc_take /= take_app_length. Qed.
  Lemma cloc_skip_app_length l cs1 cs2:
    cloc_skip (l, cs1 ++ cs2) (length cs1) = (l +ₗ length cs1, cs2).
  Proof. by rewrite /cloc_skip /= drop_app_length. Qed.

  Lemma heap_complete_mapsto_fancy_empty_cells l fv :
    (l, []) #↦! fv ⊣⊢ l ↦! fv.
  Proof. by rewrite /heap_complete_mapsto_fancy /heap_mapsto_fancy /=. Qed.

  Local Lemma cloc_get_row_no_cells (l: loc) (cs: list (list cell_id)) (fvl: list fancy_val) (i: nat) (cv: cell_id + val) :
      cs !! i = Some [] →
      fvl !! i = Some (sum2fv cv) →
      (l, cs) #↦!∗ fvl ⊢ inl (l +ₗ i) @↦[heap_name] cv.
  Proof.
    move => Hlookup1 Hlookup2.
    apply elem_of_list_split_length in Hlookup1 as [cs1 [cs2 [-> Hi]]].
    apply elem_of_list_split_length in Hlookup2 as [fvl1 [fvl2 [-> Hi']]].
    rewrite heap_cloc_mapsto_fancy_vec_app.
    rewrite -Hi' Hi cloc_take_app_length cloc_skip_app_length.
    rewrite {1} heap_mapsto_cloc_fancy_vec_cons.
    iIntros "(_ & H & _)".
    rewrite heap_complete_mapsto_fancy_empty_cells/heap_mapsto_fancy/= .
    destruct cv => //.
  Qed.
  

  Local Lemma cloc_get_row_last_cell (l: loc) (cs: list (list cell_id)) (fvl: list fancy_val) (i: nat) (cells: list cell_id) (cell: cell_id) (cv: cell_id + val) :
      cs !! i = Some (cells ++ [cell]) →
      fvl !! i = Some (sum2fv cv) →
      (l, cs) #↦!∗ fvl ⊢ inr cell @↦[heap_name] cv.
  Proof.
    move => Hlookup1 Hlookup2.
    apply elem_of_list_split_length in Hlookup1 as [cs1 [cs2 [-> Hi]]].
    apply elem_of_list_split_length in Hlookup2 as [fvl1 [fvl2 [-> Hi']]].
    rewrite heap_cloc_mapsto_fancy_vec_app.
    rewrite -Hi' Hi cloc_take_app_length cloc_skip_app_length.
    rewrite {1} heap_mapsto_cloc_fancy_vec_cons.
    iIntros "(_ & H & _)".
    rewrite /heap_complete_mapsto_fancy/= .
    rewrite split_at_last_snoc.
    destruct cv => //.
  Qed.

  Local Lemma cloc_get_row_prefix (l: loc) (cs: list (list cell_id)) (i: nat) (cells: list cell_id) (cell: cell_id) :
      cs !! i = Some (cells ++ [cell]) →
      (l, cs) #↦∗_ ⊢ inl (l +ₗ i) @↦[heap_name][^cells] (inl cell).
  Proof.
    move => Hlookup.
    apply elem_of_list_split_length in Hlookup as [cs1 [cs2 [-> Hi]]].
    rewrite (heap_cloc_mapsto_emp_vec_app _ i).
    rewrite Hi cloc_take_app_length cloc_skip_app_length.
    rewrite heap_mapsto_cloc_emp_cons.
    iIntros "(_ & H & _)".
    rewrite /heap_complete_mapsto.
    rewrite split_at_last_snoc //=.
  Qed.
  
  Local Lemma split_at_last_eq_concat_last (c: cell_id) (cells: list cell_id) :
      match split_at_last (c :: cells) with
          | Some (prefix, last_cell) => c :: cells = prefix ++ [last_cell]
          | None => false
      end.
  Proof.
    induction cells as [ | ?? IH ]in c |- * => //=.
    opose proof (@exists_last _ (a :: cells) _) as [a_last [cells' ->]] => //.
    rewrite app_comm_cons split_at_last_snoc //=.
  Qed.
  
  Lemma and_cloc_combine_fancy (l: cloc) (fvl: list fancy_val) :
      l #↦∗_ ∧ l #↦!∗ fvl ⊢ l.1 ↦[^ l.2 ]!∗ fvl.
  Proof using heapGS0 invGS0 Σ.
      iIntros "And".
      iDestruct (heap_cloc_mapsto_fancy_vec_length_eq with "[And]") as "%HLen".
        { iDestruct "And" as "[_ $]". }
      destruct l as [l cs]. simpl.
      iApply sepM_entails_mapsto_cells_fancy_vec; first by trivial.
      iApply pt_seq_andM_sepM. iApply big_andM_intro. iIntros (l0 x) "%IsSome".
      destruct x as [cells cv].
      destruct (lookup_loc_cells_fv_map l cs fvl l0 cells cv IsSome) as [i [Hl [Hc Hv]]].
      subst l0. destruct cells.
       - iApply (cloc_get_row_no_cells _ _ _ _ _ Hc Hv with "[And]").
         iDestruct "And" as "[_ $]".
       - have Hsplit := split_at_last_eq_concat_last c cells.
         destruct (split_at_last (c :: cells)) as [[prefix last_cell]|] eqn:Hsp; last by done.
         rewrite Hsplit. iApply pt_seq_cons_back_and. iSplit.
          + iApply cloc_get_row_prefix. { rewrite <- Hsplit. apply Hc. }
            iDestruct "And" as "[$ _]".
          + iApply (cloc_get_row_last_cell l cs fvl i prefix last_cell).
            { rewrite <- Hsplit. apply Hc. } { apply Hv. }
            iDestruct "And" as "[_ $]".
  Qed.
    
  Lemma and_cloc_combine (l: cloc) (vl: list val) :
      l #↦∗_ ∧ l #↦∗ vl ⊢ l.1 ↦[^ l.2 ]∗ vl.
  Proof using heapGS0 invGS0 Σ.
      apply and_cloc_combine_fancy.
  Qed.
  
  Lemma guard_cloc_combine G E n (l: cloc) (vl: list val) :
      ⊢ (G &&{E;n}&&> l #↦∗_) -∗ (G &&{E;n}&&> l #↦∗ vl) -∗ (G &&{E;n}&&> (l.1 ↦[^ l.2]∗ vl)).
  Proof.
      iApply guards_and_point.
      - apply point_prop_heap_mapsto_cells_fancy_vec. - apply and_cloc_combine.
  Qed.
  
  Lemma guard_cloc_combine_fancy G E n (l: cloc) (vl: list fancy_val) :
      ⊢ (G &&{E;n}&&> l #↦∗_) -∗ (G &&{E;n}&&> l #↦!∗ vl)
          -∗ (G &&{E;n}&&> (l.1 ↦[^ l.2]!∗ vl)).
  Proof.
      iApply guards_and_point.
      - apply point_prop_heap_mapsto_cells_fancy_vec. - apply and_cloc_combine_fancy.
  Qed.

  Lemma heap_mapsto_cells_fancy_vec_length_eq l cells fvl :
      l ↦[^ cells]!∗ fvl ⊢ ⌜length cells = length fvl⌝.
  Proof.
    induction cells as [|c cells IH] in l, fvl |- *; destruct fvl as [|fv fvl];
      simpl; [by iIntros|by iIntros "[]"|by iIntros "[]"|].
    iIntros "[_ H]". by iDestruct (IH with "H") as %->.
  Qed.

  (** A point of a sequence of points. *)
  Lemma heap_mapsto_cells_fancy_vec_lookup l cells fvl (i: nat) cs fv :
      cells !! i = Some cs → fvl !! i = Some fv →
      l ↦[^ cells]!∗ fvl ⊢ inl (l +ₗ i) @↦[heap_name][^ cs] (fv2sum fv).
  Proof.
    induction cells as [|c cells IH] in l, fvl, i |- *; [done|].
    destruct fvl as [|f fvl]; [done|]. destruct i as [|i]; simpl.
    - intros [= ->] [= ->]. rewrite shift_loc_0. iIntros "[$ _]".
    - intros ??. iIntros "[_ H]". iDestruct (IH with "H") as "H"; [done|done|].
      rewrite shift_loc_assoc. by replace (1 + i)%Z with (Z.of_nat (S i)) by lia.
  Qed.

  (** The points of two disjoint consecutive ranges, in a conjunction, are the points of
      their union (as [and_cloc_combine_fancy]; used to combine guards of the two ranges,
      [guard_cells_app_combine_fancy]). *)
  Lemma and_cells_app_combine_fancy l cells (vl1 vl2: list fancy_val) :
      l ↦[^ take (length vl1) cells]!∗ vl1 ∧
        (l +ₗ length vl1) ↦[^ drop (length vl1) cells]!∗ vl2 ⊢
      l ↦[^ cells]!∗ (vl1 ++ vl2).
  Proof using heapGS0 invGS0 Σ.
    iIntros "And".
    iAssert ⌜length (take (length vl1) cells) = length vl1⌝%I as %H1.
    { iDestruct "And" as "[A _]". by iApply heap_mapsto_cells_fancy_vec_length_eq. }
    iAssert ⌜length (drop (length vl1) cells) = length vl2⌝%I as %H2.
    { iDestruct "And" as "[_ A]". by iApply heap_mapsto_cells_fancy_vec_length_eq. }
    rewrite length_take in H1. rewrite length_drop in H2.
    iApply sepM_entails_mapsto_cells_fancy_vec; first by (rewrite length_app; lia).
    iApply pt_seq_andM_sepM. iApply big_andM_intro. iIntros (l0 [cs cv]) "%IsSome".
    destruct (lookup_loc_cells_fv_map l cells (vl1 ++ vl2) l0 cs cv IsSome)
      as [i [-> [Hc Hv]]].
    rewrite (_: cv = fv2sum (sum2fv cv)); [|by destruct cv].
    destruct (decide (i < length vl1)%nat) as [Hi|Hi].
    - iDestruct "And" as "[A _]". iApply (heap_mapsto_cells_fancy_vec_lookup with "A").
      + rewrite lookup_take; [done|lia].
      + rewrite -Hv lookup_app_l; [done|lia].
    - iDestruct "And" as "[_ A]".
      iDestruct (heap_mapsto_cells_fancy_vec_lookup _ _ _ (i - length vl1) cs (sum2fv cv)
        with "A") as "A".
      + rewrite lookup_drop. rewrite -Hc. f_equal. lia.
      + rewrite -Hv lookup_app_r; [done|lia].
      + rewrite shift_loc_assoc. by replace (length vl1 + (i - length vl1)%nat)%Z
          with (Z.of_nat i) by lia.
  Qed.

  Lemma guard_cells_app_combine_fancy G E n l cells (vl1 vl2: list fancy_val) :
      ⊢ (G &&{E;n}&&> l ↦[^ take (length vl1) cells]!∗ vl1) -∗
        (G &&{E;n}&&> (l +ₗ length vl1) ↦[^ drop (length vl1) cells]!∗ vl2) -∗
        (G &&{E;n}&&> l ↦[^ cells]!∗ (vl1 ++ vl2)).
  Proof.
    iApply guards_and_point.
    - apply point_prop_heap_mapsto_cells_fancy_vec. - apply and_cells_app_combine_fancy.
  Qed.

  Lemma cloc_take_app_length' n l cs1 cs2 :
    n = length cs1 →
    cloc_take (l, cs1 ++ cs2) n = (l, cs1).
  Proof. move => ->; by rewrite /cloc_take /= take_app_length. Qed.
  Lemma cloc_skip_app_length' n l cs1 cs2:
    n = length cs1 →
    cloc_skip (l, cs1 ++ cs2) n = (l +ₗ length cs1, cs2).
  Proof. move => ->; by rewrite /cloc_skip /= drop_app_length. Qed.

  Lemma guard_cloc_combine_fancy' G E n (l : cloc) (γs : list cell_id) (vl: list fancy_val) :
      ⊢ (G &&{E;n}&&> l.1 ↦[^ l.2 ]!∗ (FCell <$> γs)) -∗ (G &&{E;n}&&> γs ^↦!∗ vl) -∗ let l' := cloc_flat_insert l γs in (G &&{E;n}&&> (l'.1 ↦[^ l'.2]!∗ vl)).
  Proof.
    iApply guards_and_point.
    - apply point_prop_heap_mapsto_cells_fancy_vec.
    - iIntros "And".
      rewrite -(heap_complete_mapsto_fancy_val_vec_eq' l.1).
      iDestruct (heap_cloc_mapsto_fancy_vec_length_eq with "[And]") as "%HLen".
      { rewrite heap_mapsto_cells_to_complete_mapsto_fancy_vec.
        iDestruct "And" as "[[_ $] _]". }
      iDestruct (heap_cloc_mapsto_fancy_vec_length_eq with "[And]") as "%HLen'".
      { iDestruct "And" as "[_ $]". }
      destruct l as [l cs] => /=; simpl in HLen.
      iApply sepM_entails_mapsto_cells_fancy_vec. 
      { rewrite length_zip_with.
        simpl in HLen'.
        rewrite !length_fmap in HLen, HLen'.
        lia. }
      iApply pt_seq_andM_sepM. 
      iApply big_andM_intro. iIntros (l0 [cells cv]) "%IsSome".
      destruct (lookup_loc_cells_fv_map l _ _ l0 cells cv IsSome) as [i [Hl [Hc Hv]]].
      clear IsSome.
      subst l0. 
      have [γ [Hγs [cells' [Hcs Hcells]]]] : (∃ γ, γs !! i = Some γ ∧ ∃ cells', cs !! i = Some cells' ∧ cells = cells' ++ [γ]).
      { apply lookup_zip_with_Some in Hc.
        destruct Hc as (γ & cells' & ? & ? & ?).
        eexists; split => //.
        eexists; split => //. }
      apply elem_of_list_split_length in Hcs as [cs1 [cs2 [Hcs Hcs1]]].
      apply elem_of_list_split_length in Hγs as [γs1 [γs2 [Hγs Hγs1]]].
      rewrite Hcs Hγs.
      set cl := (l, cs1 ++ cells' :: cs2).
      change l with cl.1.
      change (cs1 ++ cells' :: cs2) with cl.2.
      rewrite fmap_app.
      rewrite heap_mapsto_cells_fancy_vec_app.
      unfold cl; simpl.
      replace (drop (length (FCell <$> γs1)) (cs1 ++ cells' :: cs2)) with (cells' :: cs2).
      2: {
        rewrite drop_app_length' => //.
        rewrite length_fmap; lia.
      }
      replace (take (length (FCell <$> γs1)) (cs1 ++ cells' :: cs2)) with cs1.
      2: {
        rewrite take_app_length' => //.
        rewrite length_fmap; lia.
      }
      rewrite heap_mapsto_cells_fancy_vec_cons.
      iDestruct (and_mono_l with "And") as "And".
      { iIntros "[H1 [H2 H3]]". iExact "H2". }
      apply elem_of_list_split_length in Hv as [vl1 [vl2 [Hvl Hvl1]]].
      rewrite Hvl.
      rewrite heap_cloc_mapsto_fancy_vec_app.
      rewrite -Hvl1 Hγs1.
      rewrite fmap_app.
      rewrite cloc_take_app_length'; first rewrite cloc_skip_app_length'.
      2,3: by rewrite length_fmap.
      rewrite fmap_cons.
      rewrite heap_mapsto_cloc_fancy_vec_cons.
      iDestruct (and_mono_r with "And") as "And".
      { iIntros "[H1 [H2 H3]]". iExact "H2". }
      rewrite Hcells.
      iApply pt_seq_cons_back_and. iSplit.
      + iDestruct "And" as "[H _]".
        rewrite /heap_mapsto_cells_fancy/=.
        by rewrite length_fmap.
      + iDestruct "And" as "[_ H]".
        rewrite /heap_complete_mapsto_fancy.
        simpl.
        destruct cv => //.
  Qed.


  (* untethering *)
  
  Lemma mapsto_vec_untether1 l fv E F :
      l #↦! fv ={E}=∗ ∃ (v: val), l #↦ v
          ∗ (∀ l₁, l₁ #↦_ ∗ l₁ #↦ v ={F}=∗ l₁ #↦_ ∗ l₁ #↦! fv)%I
          ∗ ⌜ match fv with FVal v0 => v0 = v | _ => True end ⌝.
  Proof.
      iIntros "pt". destruct fv.
       - iModIntro. iExists v. iFrame. iSplit. { iIntros. { iModIntro. iFrame. } } done.
       - iMod (pt_untether with "pt") as (v) "[pt back]".
         iModIntro. iExists v. iFrame "pt". iSplit; last by done. iIntros (l₁).
         destruct l₁ as [l0 c0]. iDestruct ("back" $! l0 c0) as "back".
         rewrite <- (heap_mapsto_cells_to_complete_mapsto_fancy (l0, c0) (FVal v)).
         rewrite <- (heap_mapsto_cells_to_complete_mapsto_fancy (l0, c0) (FCell c)).
         iIntros "A". iMod ("back" with "A"). iModIntro. iFrame.
  Qed.
 
  Lemma mapsto_vec_untether' l fv E F :
      l #↦!∗ fv ={E}=∗ ∃ (v: list val), l #↦∗ v ∗ ⌜length v = length fv⌝
          ∗ (∀ l₁, l₁ #↦∗_ ∗ l₁ #↦∗ v ={F}=∗ l₁ #↦∗_ ∗ l₁ #↦!∗ fv)%I
          ∗ ⌜ all_concrete fv → fv = fmap FVal v ⌝.
  Proof.
      destruct l as [l cs]. generalize l, fv. clear l. clear fv. induction cs.
       - intros l fv. iIntros "A". iModIntro. iExists []. 
         rewrite heap_complete_mapsto_val_empty.
         iDestruct (heap_cloc_mapsto_fancy_vec_length_eq with "A") as "%Hlen".
         iSplit; first by done. iSplit; first by iFrame "%".
         simpl in Hlen. symmetry in Hlen. rewrite length_zero_iff_nil in Hlen. subst fv. 
         iSplit; last by done.
         iIntros (l₁). iIntros "[B C]". iModIntro. iFrame. 
       - iIntros (l fv) "pt". destruct fv as [|fv fvs]; first by done.
         rewrite heap_mapsto_cloc_fancy_vec_cons. iDestruct "pt" as "[pt1 pt2]".
         iMod (IHcs with "pt2") as (vs) "[pt2 [%len [back2 %conc2]]]".
         iMod (mapsto_vec_untether1 with "pt1") as (v) "[pt1 [back1 %conc1]]".
         iModIntro. iExists (v :: vs). 
         rewrite heap_mapsto_cloc_vals_vec_cons. iFrame.
         iSplit. { iPureIntro. simpl; rewrite len; trivial. }
         iSplit. {
          iIntros (l₁). destruct l₁ as [l₁ c₁]. iIntros "[prefix pt]".
          destruct c₁ as [|c₁ cs₁]; first by done.
          rewrite heap_mapsto_cloc_emp_cons. rewrite heap_mapsto_cloc_vals_vec_cons.
          iDestruct "prefix" as "[prefix1 prefix2]".
          iDestruct "pt" as "[pt1 pt2]".
          iMod ("back1" with "[pt1 prefix1]") as "[pt1 prefix1]". { iFrame. }
          iMod ("back2" with "[pt2 prefix2]") as "[pt2 prefix2]". { iFrame. }
          iModIntro. iFrame.
         }
         iPureIntro. simpl. intros [conc1' conc2']. rewrite conc2; trivial.
         destruct fv. { subst v. trivial. } simpl in conc1'. contradiction.
  Qed.
  
  Lemma mapsto_vec_untether l fv E F :
      l #↦!∗ fv ={E}=∗ ∃ (v: list val), l #↦∗ v ∗ ⌜length v = length fv⌝
          ∗ (∀ l₁, l₁ #↦∗_ ∗ l₁ #↦∗ v ={F}=∗ l₁ #↦∗_ ∗ l₁ #↦!∗ fv)%I.
  Proof.
      iIntros "pt". iMod (mapsto_vec_untether' _ _ _ F with "pt") as (v) "(A & B & C & D)".
      iExists v. iModIntro. iFrame.
  Qed.
          
  Lemma mapsto_vec_untether_singleton l f E F :
      l #↦!∗ [f] ={E}=∗ ∃ v l₀ c₀, ⌜l = (l₀, [c₀])⌝ ∗ (l₀, c₀) #↦ v
          ∗ (∀ l₁ c₁, (l₁, c₁) #↦_ ∗ (l₁, c₁) #↦ v ={F}=∗ (l₁, c₁) #↦_ ∗ (l₁, [c₁]) #↦!∗ [f]).
  Proof.
    iIntros "pt". iMod (mapsto_vec_untether _ _ _ F with "pt") as (v) "[pt [%Heq Hback]]".
    iModIntro. destruct l as [l cs].
    iDestruct (heap_cloc_mapsto_fancy_vec_length_eq with "pt") as "%Hlen".
    rewrite length_fmap in Hlen. rewrite Heq in Hlen. simpl in Hlen.
    destruct cs as [|c cs]; first by done. destruct cs as [|]; last by done.
    simpl in Heq.
    destruct v as [|v vs]; first by done. destruct vs as [|]; last by done.
    iExists v, l, c. iSplit; first by done. iFrame.
    rewrite heap_complete_mapsto_val_singleton. iFrame.
    iIntros (l₁ c₁). iDestruct ("Hback" $! (l₁, [c₁])) as "Hback".
    rewrite heap_complete_mapsto_val_singleton. 
    rewrite heap_complete_mapsto_singleton. iFrame.
  Qed.
  
  Lemma mapsto_vec_untether_emp l fv E F :
      l ↦!∗ fv ={E}=∗ ∃ (v: list val), l ↦∗ v ∗ ⌜length v = length fv⌝
          ∗ (∀ l₁, l₁ #↦∗_ ∗ l₁ #↦∗ v ={F}=∗ l₁ #↦∗_ ∗ l₁ #↦!∗ fv)
          ∗ ⌜ all_concrete fv → fv = fmap FVal v ⌝.
  Proof. 
      have Ha := (mapsto_vec_untether' (l, repeat [] (length fv)) fv E F).
      rewrite <- heap_cloc_mapsto_fancy_empty in Ha. 
      iIntros "A". iMod (Ha with "A") as (v) "(B & %lens & D & E)".
      rewrite <- lens. rewrite <- heap_cloc_mapsto_val_empty.
      iModIntro. iExists v. iFrame. done.
  Qed.

  Lemma heap_mapsto_fancy_to_heap_complete_mapsto l γ : 
    (l ↦! FCell γ) ⊣⊢ ((l, [γ]) #↦_).
  Proof.
    by rewrite /heap_mapsto_fancy/heap_complete_mapsto/=.
  Qed.
  
  Lemma heap_delete_cell (l : loc) (γs : list cell_id) (fl : list fancy_val) :
    l ↦!∗ (FCell <$> γs) -∗ (l, (λ γ : cell_id, [γ]) <$> γs) #↦!∗ fl ==∗ l ↦!∗ fl.
  Proof.
    induction γs as [ | γ γs IH] in l, fl |- *.
    - simpl. iIntros "_ Hl !>". destruct fl => //.
    - rewrite !fmap_cons.
      destruct fl as [| fv fvs].
      + iIntros "_ H".
        by iDestruct (heap_cloc_mapsto_fancy_vec_length_eq with "H") as "%".
      + iIntros "Hcells Hvals".
        rewrite heap_mapsto_fancy_vec_cons.
        rewrite heap_mapsto_cloc_fancy_vec_cons.
        iDestruct "Hcells" as "(Hγ & Hγs)".
        iDestruct "Hvals" as "(Hfv & Hfvs)".
        rewrite heap_mapsto_fancy_vec_cons.
        iSplitL "Hγ Hfv".
        * rewrite heap_mapsto_fancy_to_heap_complete_mapsto.
          iCombine "Hγ Hfv" as "H".
          rewrite -(heap_mapsto_cells_to_complete_mapsto_fancy).
          rewrite /heap_mapsto_cells_fancy.
          by iMod (pt_delete_cell with "H") as "H".
        * by iMod (IH with "Hγs Hfvs").
  Qed.

  (* writes *)
  Lemma heap_write σ (l: cloc1) v v' E G d :
    ↑naN ⊆ E →
    £(3*d+1) -∗
    heap_ctx σ -∗ (G &&{↑naN;d}&&> l #↦_) -∗ G -∗ l #↦ v ={E}=∗
      ⌜σ.1 !! l.1 = Some (RSt 0, word_to_byte v)⌝ ∗
    heap_ctx (<[l.1 := (RSt 0, word_to_byte v')]> σ.1, σ.2) ∗ G ∗ l #↦ v'.
  Proof.
    iIntros (Hmask) "[£ £1] ctx #guards G pt". iDestruct "ctx" as (hF) "(Hσ & HhF & % & ato)".
    iDestruct "Hσ" as (σL σB) "(%Hr & Hσ & σB)".
    unfold heap_complete_mapsto, heap_complete_mapsto_fancy.
    destruct (split_at_last (snd l)) as [[cells c]|] eqn:Heq.
     - iMod (atomic_write_guarded_cells with "£ guards G pt Hσ") as "A". { apply Hmask. }
       iMod (lc_fupd_elim_later with "£1 A") as "A".
       iMod "A" as "[%res [G [pt Hσ]]]".
       iModIntro. iFrame. iPureIntro.
       have ? := phys_rel_lookup_L _ _ _ _ _ _ Hr res.
       split; [done|]. split; [|eauto using heap_freeable_rel_stable].
       apply phys_rel_L_insert; [done|]. by eapply phys_rel_L_not_B.
     - iMod (atomic_write with "pt Hσ") as "[%res [pt Hσ]]". { trivial. }
       iModIntro. iFrame. iPureIntro.
       have ? := phys_rel_lookup_L _ _ _ _ _ _ Hr res.
       split; [done|]. split; [|eauto using heap_freeable_rel_stable].
       apply phys_rel_L_insert; [done|]. by eapply phys_rel_L_not_B.
  Qed.

  Lemma heap_write_na σ (l: cloc1) v v' E G d :
    ↑naN ⊆ E →
    £(3*d) -∗
    heap_ctx σ -∗ (G &&{↑naN;d}&&> l #↦_) -∗ G -∗ l #↦ v ={E}=∗
      ⌜σ.1 !! l.1 = Some (RSt 0, word_to_byte v)⌝ ∗
      heap_ctx (<[l.1:=(WSt, word_to_byte v)]> σ.1, σ.2) ∗
      ∀ σ', £1 -∗ heap_ctx σ' ={E}=∗ ⌜∃b0, σ'.1 !! l.1 = Some (WSt, b0)⌝ ∗
        heap_ctx (<[l.1:=(RSt 0, word_to_byte v')]> σ'.1, σ'.2) ∗ G ∗ l #↦ v'.
  Proof.
    iIntros (Hmask) "£ ctx #guards G pt". iDestruct "ctx" as (hF) "(Hσ & HhF & % & ato)".
    iDestruct "Hσ" as (σL σB) "(%Hr & Hσ & σB)".
    unfold heap_complete_mapsto, heap_complete_mapsto_fancy.
    destruct (split_at_last (snd l)) as [[cells c]|] eqn:Heq.
     - iMod (na_write_begin_guarded_cells with "£ guards G pt Hσ") as "[%Hres [wim Hσ]]"; first by trivial.
       have ? := phys_rel_lookup_L _ _ _ _ _ _ Hr Hres.
       iModIntro. iFrame "%". iSplitR "wim".
       { iFrame. iPureIntro. split; [|eauto using heap_freeable_rel_stable].
         apply phys_rel_L_insert; [done|]. by eapply phys_rel_L_not_B. }
       iIntros (x) "£1 ctx". iDestruct "ctx" as (hF') "(Hσ & HhF & % & ato)".
       iDestruct "Hσ" as (σL' σB') "(%Hr' & Hσ & σB)".
       iDestruct (na_write_finish_guarded_cells with "wim Hσ") as "A"; first by apply Hmask.
       iMod (lc_fupd_elim_later with "£1 A") as "A".
       iMod "A" as "[%Hres2 [G [pt Hσ]]]".
       destruct Hres2 as [v0 Hres2]. have ? := phys_rel_lookup_L _ _ _ _ _ _ Hr' Hres2.
       iModIntro. iFrame. iPureIntro. split; [by eexists|].
       split; [|eauto using heap_freeable_rel_stable].
       apply phys_rel_L_insert; [done|]. by eapply phys_rel_L_not_B.
     - iMod (na_write_begin with "pt Hσ") as "[%Hres [wim Hσ]]"; first by trivial.
       have ? := phys_rel_lookup_L _ _ _ _ _ _ Hr Hres.
       iModIntro. iFrame "%". iSplitR "G wim".
       { iFrame. iPureIntro. split; [|eauto using heap_freeable_rel_stable].
         apply phys_rel_L_insert; [done|]. by eapply phys_rel_L_not_B. }
       iIntros (x) "£1 ctx". iDestruct "ctx" as (hF') "(Hσ & HhF & % & ato)".
       iDestruct "Hσ" as (σL' σB') "(%Hr' & Hσ & σB)".
       iMod (na_write_finish with "wim Hσ") as "[%Hres2 [pt Hσ]]"; first by trivial.
       destruct Hres2 as [v0 Hres2]. have ? := phys_rel_lookup_L _ _ _ _ _ _ Hr' Hres2.
       iModIntro. iFrame. iPureIntro. split; [by eexists|].
       split; [|eauto using heap_freeable_rel_stable].
       apply phys_rel_L_insert; [done|]. by eapply phys_rel_L_not_B.
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

  (** ** The physical relation for ranges of the byte region *)
  Lemma phys_rel_mem_range P σ σL σB l bs :
    phys_rel σ σL σB → mem_range P σB l bs → mem_range P σ l bs.
  Proof.
    rewrite !mem_range_lookup. intros Hr H i b Hb.
    destruct (H i b Hb) as (ls & Hl & ?). exists ls. split; [|done].
    by eapply phys_rel_lookup_B.
  Qed.

  Lemma phys_rel_mem_alter P f σ σL σB l bs :
    phys_rel σ σL σB → mem_range P σB l bs →
    phys_rel (mem_alter f l (length bs) σ) σL (mem_alter f l (length bs) σB).
  Proof.
    intros Hr Hbs. apply (phys_rel_B_update σ _ σL σB); [done|]. intros l'.
    destruct (loc_range_dec l (length bs) l') as [[i [Hi ->]]|Hout].
    - right. destruct (mem_range_lookup_1 _ _ _ _ i Hbs Hi) as (ls & b & Hl & _).
      rewrite !lookup_mem_alter_in // Hl (phys_rel_lookup_B _ _ _ _ _ Hr Hl). eauto.
    - left. by rewrite !lookup_mem_alter_out.
  Qed.

  Lemma phys_rel_mem_write P σ σL σB l bs bs' :
    phys_rel σ σL σB → mem_range P σB l bs → length bs' = length bs →
    phys_rel (mem_write l bs' σ) σL (mem_write l bs' σB).
  Proof.
    intros Hr Hbs Hlen. apply (phys_rel_B_update σ _ σL σB); [done|]. intros l'.
    destruct (loc_range_dec l (length bs) l') as [[i [Hi ->]]|Hout].
    - right. destruct (mem_range_lookup_1 _ _ _ _ i Hbs Hi) as (ls & b & Hl & _).
      destruct (lookup_lt_is_Some_2 bs' i) as [b' Hb']; [lia|].
      rewrite !(lookup_mem_write_in _ _ _ _ b') //; rewrite Hl; eauto.
    - left. rewrite !lookup_mem_write_out //; by rewrite Hlen.
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
    iIntros (Heq) "(%R & %ρ & %NC & %CW & Hreg & Hdyn & Hnc & Hcw & [%Hwf [%Hl1 %Hl2]] & HR & Hcwe & Hρ)".
    iExists R, ρ, NC, CW. iFrame. iPureIntro. split; [done|]. split.
    - intros k cs v c Hk Hc. apply (Hl1 k cs v c); [|done]. apply Heq; [|done].
      intros ->. by apply not_elem_of_nil in Hc.
    - intros g k m cs Hg HR i c Hc. destruct (Hl2 g k m cs Hg HR i c Hc) as (rest & v & Hr).
      exists rest, v. by apply Heq.
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
    cwbank_auth ∅ -∗ bytes_ctx ∅.
  Proof.
    iIntros "H● Hbank Hreg Hdyn Hnc Hcw". iExists ∅, ∅.
    rewrite !big_sepM_empty phi_empty. iFrame "H● Hbank".
    iSplit. { iPureIntro. intros l. by rewrite fmap_empty !lookup_empty. }
    iSplit. { iPureIntro. intros i e. by rewrite fmap_empty lookup_empty. }
    iSplit; [done|]. iExists ∅, ∅, ∅, ∅. iFrame. rewrite !big_sepM_empty fmap_empty.
    iPureIntro. split_and!; try done.
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

Section cells.
  Context `{!heapGS Σ}.
  Context `{!invGS Σ}.
  Implicit Types 𝛼 : bfull.
  Implicit Types (R : gmap positive (mty * list positive)) (ρ : gmap positive FValue).

  Global Instance greg_persistent g m cs : Persistent (greg g m cs).
  Proof. apply _. Qed.
  Global Instance gnocell_persistent g : Persistent (gnocell g).
  Proof. apply _. Qed.
  Global Instance gdyn_timeless g fv : Timeless (gdyn g fv).
  Proof. apply _. Qed.
  Global Instance bcells_timeless cs fbs : Timeless (bcells cs fbs).
  Proof. apply _. Qed.
  Global Instance loc_side_timeless l g m cs : Timeless (loc_side l g m cs).
  Proof. apply _. Qed.
  Global Instance brepr_persistent m fbs fv : Persistent (brepr m fbs fv).
  Proof. apply _. Qed.
  Global Instance heap_mapsto_fbytes_timeless l fbs : Timeless (heap_mapsto_fbytes l fbs).
  Proof. apply _. Qed.

  Lemma greg_agree g m cs m' cs' : greg g m cs -∗ greg g m' cs' -∗ ⌜m = m' ∧ cs = cs'⌝.
  Proof. iIntros "A B". by iDestruct (ghost_map_elem_agree with "A B") as %[= -> ->]. Qed.

  Lemma gdyn_excl g fv fv' : gdyn g fv -∗ gdyn g fv' -∗ False.
  Proof. iIntros "A B". by iDestruct (ghost_map_elem_ne with "A B") as %?. Qed.

  Lemma greg_lookup R g m cs :
    ghost_map_auth heap_greg_name 1 R -∗ greg g m cs -∗ ⌜R !! g = Some (m, cs)⌝.
  Proof. iIntros "A B". iApply (ghost_map_lookup with "A B"). Qed.
  Lemma gdyn_lookup ρ g fv :
    ghost_map_auth heap_gdyn_name 1 ρ -∗ gdyn g fv -∗ ⌜ρ !! g = Some fv⌝.
  Proof. iIntros "A B". iApply (ghost_map_lookup with "A B"). Qed.
  Lemma gnocell_lookup (NC : gmap positive ()) g :
    ghost_map_auth heap_gnc_name 1 NC -∗ gnocell g -∗ ⌜g ∈ dom NC⌝.
  Proof.
    iIntros "A B". iDestruct (ghost_map_lookup with "A B") as %Hg. iPureIntro.
    by apply elem_of_dom_2 in Hg.
  Qed.

  Lemma brepr_frepr R m fbs fv :
    ghost_map_auth heap_greg_name 1 R -∗ brepr m fbs fv -∗ ⌜frepr R m fbs fv⌝.
  Proof.
    iIntros "A (%R' & %Hrep & #HR')". iAssert ⌜R' ⊆ R⌝%I as %Hsub.
    { iIntros (g). destruct (R' !! g) as [[m' cs']|] eqn:Hg; [|by destruct (R !! g)].
      iDestruct (big_sepM_lookup with "HR'") as "H"; [done|].
      iDestruct (greg_lookup with "A H") as %->. done. }
    iPureIntro. by eapply frepr_mono.
  Qed.

  (** The facts that the authority knows about owned edges. *)
  Lemma bheap_edges 𝛼 (l : loc) (cvs : list (positive + bval)) :
    bheap 𝛼 -∗ ([∗ list] i ↦ cv ∈ cvs, bpt (inl (l +ₗ i)) cv) -∗
    ⌜∀ (i : nat) cv, cvs !! i = Some cv → 𝛼_fine_pair loc positive bval 𝛼 (inl (l +ₗ i)) cv⌝.
  Proof.
    iIntros "H● Hcvs". iApply pure_forall_2. iIntros (i). iApply pure_forall_2.
    iIntros (cv). destruct (cvs !! i) as [cv'|] eqn:Hi; [|by iPureIntro].
    iDestruct (big_sepL_lookup with "Hcvs") as "Hcv"; [done|].
    iDestruct (fheap_fpt with "H● Hcv") as %Hp. iPureIntro. by intros [= <-].
  Qed.

  Lemma bheap_cells 𝛼 cs fbs :
    bheap 𝛼 -∗ bcells cs fbs -∗
    ⌜length cs = length fbs ∧ ∀ (i : nat) c fb, cs !! i = Some c → fbs !! i = Some fb →
       𝛼_fine_pair loc positive bval 𝛼 (inr c) fb⌝.
  Proof.
    iIntros "H● Hcs". iDestruct (big_sepL2_length with "Hcs") as %Hlen.
    iAssert ⌜∀ (i : nat) c fb, cs !! i = Some c → fbs !! i = Some fb →
       𝛼_fine_pair loc positive bval 𝛼 (inr c) fb⌝%I with "[-]" as %H; [|done].
    iApply pure_forall_2. iIntros (i). iApply pure_forall_2. iIntros (c).
    iApply pure_forall_2. iIntros (fb).
    destruct (cs !! i) as [c'|] eqn:Hc, (fbs !! i) as [fb'|] eqn:Hfb; try by iPureIntro.
    iDestruct (big_sepL2_lookup with "Hcs") as "Hc"; [done..|].
    iDestruct (fheap_fpt with "H● Hc") as %Hp. iPureIntro. by intros [= <-] [= <-].
  Qed.

  (** The location side of a group gives the starts of its rows. *)
  Lemma loc_side_rows 𝛼 l g m cs :
    bheap 𝛼 -∗ loc_side l g m cs -∗
    ⌜∀ (i : nat) c, cs !! i = Some c → ∃ rest v, 𝛼 !! inl (l +ₗ i) = Some (c :: rest, v)⌝.
  Proof.
    iIntros "H● [_ Hcs]".
    iDestruct (bheap_edges _ _ (inl <$> cs) with "H● [Hcs]") as %H.
    { by rewrite big_sepL_fmap. }
    iPureIntro. intros i c Hc. move: (H i (inl c)). rewrite list_lookup_fmap Hc /=.
    intros Hp. specialize (Hp eq_refl). rewrite /𝛼_fine_pair in Hp.
    destruct (𝛼 !! inl (l +ₗ i)) as [[[|c' rest] v]|]; try done. subst. eauto.
  Qed.


  (** ** D3 and the compositionality lemma *)

  (** The final byte of a byte-cell: the byte of the value of its row. *)
  Definition cell_final 𝛼 (c : positive) : abyte :=
    match row_of loc positive bval 𝛼 c with Some (_, (_, b)) => b | None => Uninit end.

  (** The contents of cells give their final bytes. *)
  Lemma bcells_final 𝛼 cs fbs :
    bheap 𝛼 -∗ bcells cs fbs -∗
    ⌜cell_final 𝛼 <$> cs = fin_bytes (cell_final 𝛼) (fb_strip <$> fbs)⌝.
  Proof.
    iIntros "H● Hcs". iDestruct (fheap_no_dupes with "H●") as %Hnd.
    iInduction cs as [|c cs] "IH" forall (fbs); destruct fbs as [|fb fbs];
      rewrite /bcells /=; try by iDestruct "Hcs" as "[]".
    { done. }
    iDestruct "Hcs" as "[Hc Hcs]". iDestruct ("IH" with "H● Hcs") as %Hrest.
    iDestruct (fheap_fpt with "H● Hc") as %Hp. iPureIntro. rewrite /fin_bytes /= in Hrest |- *.
    f_equal; [|done]. rewrite /𝛼_fine_pair in Hp. destruct fb as [c2|[ls b]]; simpl.
    - destruct Hp as (k & cs' & v & Hk & Hpair).
      apply list_has_pair_elem_of in Hpair as [Hc Hc2].
      rewrite /cell_final. erewrite row_of_spec; [|done..]. erewrite row_of_spec; [|done..].
      done.
    - destruct Hp as (k & cs' & Hk & Hend). apply list_ends_with_elem_of in Hend.
      rewrite /cell_final. erewrite row_of_spec; [|done..]. done.
  Qed.

  Lemma gcontents_facts 𝛼 R CW ρ :
    bheap 𝛼 -∗ ([∗ map] g ↦ fv ∈ ρ, gcontents R CW g fv) -∗
    ⌜map_Forall (λ g fv, ∃ m cs fbs, R !! g = Some (m, cs) ∧ frepr R m fbs fv ∧
       cell_final 𝛼 <$> cs = fin_bytes (cell_final 𝛼) fbs) ρ⌝.
  Proof.
    iIntros "H● Hρ". iInduction ρ as [|g fv ρ Hg] "IH" using map_ind.
    { iPureIntro. apply map_Forall_empty. }
    rewrite big_sepM_insert //.
    iDestruct "Hρ" as "[(%m & %cs & %fbs & (%HR & %Hrep & _) & Hcs) Hρ]".
    iDestruct (bcells_final with "H● Hcs") as %Hfin.
    iDestruct ("IH" with "H● Hρ") as %Hrest. iPureIntro.
    apply map_Forall_insert; [done|]. split; [|done]. eauto 10.
  Qed.

  (** The compositionality lemma in the byte context: the final bytes of every live group
      decode to the erasure of its fancy value. *)
  Lemma cells_decode 𝛼 R CW ρ NC :
    bheap 𝛼 -∗ ([∗ map] g ↦ fv ∈ ρ, gcontents R CW g fv) -∗ ⌜cells_wf R ρ NC CW⌝ -∗
    ⌜∀ g fv m cs, ρ !! g = Some fv → R !! g = Some (m, cs) →
       ∃ v, fval_erase ρ fv v ∧ decode_value m (cell_final 𝛼 <$> cs) = Some v⌝.
  Proof.
    iIntros "H● Hρ %Hwf". iDestruct (gcontents_facts with "H● Hρ") as %Hf. iPureIntro.
    intros g fv m cs Hg HR. eapply (registry_decode R ρ (cell_final 𝛼) (λ _, True)); [|done..].
    intros g' fv' Hg' _. destruct (Hf g' fv' Hg') as (m' & cs' & fbs & HR' & Hrep & Hfin).
    exists m', cs', fbs. split_and!; [done..|]. intros g'' Hg''.
    destruct Hwf as (_ & _ & Hlt & _). destruct (Hlt g' fv' Hg' g'' Hg''). done.
  Qed.

  (** ** Helpers *)
  Lemma inl_loc_inj {B} (a b : loc) : (inl a : loc + B) = inl b → a = b.
  Proof. intros H. by inversion H. Qed.

  Lemma fb_strip_rst (fbs : list (positive + abyte)) : fb_strip <$> (fb_rst <$> fbs) = fbs.
  Proof. induction fbs as [|fb fbs IH]; [done|]. rewrite !fmap_cons IH. by destruct fb. Qed.

  Lemma gcontents_mono_R R R' CW g fv :
    R ⊆ R' → gcontents R CW g fv -∗ gcontents R' CW g fv.
  Proof.
    iIntros (Hsub) "(%m & %cs & %fbs & (%HR & %Hrep & %Hls) & Hcs)". iExists m, cs, fbs. iFrame.
    iPureIntro. split_and!; [by eapply lookup_weaken|by eapply frepr_mono|done].
  Qed.

  Lemma heap_mapsto_fbytes_bytes l bs : l ↦b bs ⊣⊢ heap_mapsto_fbytes l (inr <$> bs).
  Proof.
    rewrite heap_mapsto_bytes_eq /heap_mapsto_bytes_def /heap_mapsto_st_vec
      /heap_mapsto_fbytes big_sepL_fmap. done.
  Qed.

  Lemma heap_mapsto_fbytes_cons l fb fbs :
    heap_mapsto_fbytes l (fb :: fbs) ⊣⊢
    bpt (inl l) (fb_rst fb) ∗ heap_mapsto_fbytes (l +ₗ 1) fbs.
  Proof.
    rewrite /heap_mapsto_fbytes big_sepL_cons shift_loc_0_nat. f_equiv.
    apply big_sepL_proper. intros i fb' _. by rewrite shift_loc_S.
  Qed.

  (** Fresh group ids, larger than every registered one. *)
  Definition fresh_gid (R : gmap positive (mty * list positive)) : positive :=
    Pos.succ (foldr Pos.max 1%positive (elements (dom R))).

  Lemma fresh_gid_gt R g : g ∈ dom R → (g < fresh_gid R)%positive.
  Proof.
    rewrite /fresh_gid -elem_of_elements. generalize (elements (dom R)). intros gs Hg.
    cut (g ≤ foldr Pos.max 1 gs)%positive; [lia|].
    induction gs as [|g' gs IH]; [by apply not_elem_of_nil in Hg|].
    apply elem_of_cons in Hg as [->|Hg]; simpl; [lia|]. specialize (IH Hg). lia.
  Qed.

  Lemma fresh_gid_fresh R : R !! fresh_gid R = None.
  Proof.
    destruct (R !! fresh_gid R) eqn:Hg; [|done]. exfalso.
    have Hd : fresh_gid R ∈ dom R by apply elem_of_dom; eauto.
    have Hlt := fresh_gid_gt R _ Hd. exact (Pos.lt_irrefl _ Hlt).
  Qed.

  (** All the byte-cells of the registry. *)
  Definition reg_cells (R : gmap positive (mty * list positive)) : list positive :=
    mjoin ((λ kv : positive * (mty * list positive), kv.2.2) <$> map_to_list R).

  Lemma reg_cells_in R g m cs c : R !! g = Some (m, cs) → c ∈ cs → c ∈ reg_cells R.
  Proof.
    intros Hg Hc. rewrite /reg_cells elem_of_list_join. exists cs. split; [done|].
    apply elem_of_list_fmap. exists (g, (m, cs)). split; [done|]. by apply elem_of_map_to_list.
  Qed.

  (** Inserting fresh byte-cells at the front of the rows of [n] locations. *)
  Lemma bheap_insert_fronts 𝛼 l fbs (X : list positive) :
    bheap 𝛼 -∗ heap_mapsto_fbytes l fbs ==∗ ∃ 𝛼' cs,
      ⌜length cs = length fbs ∧ NoDup cs ∧ (∀ c, c ∈ cs → c ∉ X) ∧ bphi 𝛼' = bphi 𝛼 ∧
       (∀ k cs' v c, 𝛼' !! k = Some (cs', v) → c ∈ cs' →
          c ∈ cs ∨ ∃ cs'', 𝛼 !! k = Some (cs'', v) ∧ c ∈ cs'') ∧
       (∀ k, (∀ i : nat, (i < length fbs)%nat → k ≠ inl (l +ₗ i)) → 𝛼' !! k = 𝛼 !! k)⌝ ∗
      bheap 𝛼' ∗ ([∗ list] i ↦ c ∈ cs, bpt (inl (l +ₗ i)) (inl c)) ∗
      bcells cs (fb_rst <$> fbs).
  Proof.
    iInduction fbs as [|fb fbs] "IH" forall (𝛼 l X); iIntros "H● Hfbs".
    { iModIntro. iExists 𝛼, []. iFrame. rewrite /bcells /=. iSplit; [|done]. iPureIntro.
      split_and!; try done.
      - apply NoDup_nil_2.
      - intros c Hc. by apply not_elem_of_nil in Hc.
      - intros k cs' v c Hk Hc. right. eauto. }
    rewrite heap_mapsto_fbytes_cons. iDestruct "Hfbs" as "[Hfb Hfbs]".
    iDestruct (fheap_fpt with "H● Hfb") as %Hp0.
    assert (∃ cs0 v0, 𝛼 !! inl l = Some (cs0, v0)) as (cs0 & v0 & Hl0).
    { rewrite /𝛼_fine_pair in Hp0. destruct (fb_rst fb) as [c|v];
        destruct (𝛼 !! inl l) as [[[|??]?]|]; naive_solver. }
    iMod (fcmap_insert_front loc positive bval _ _ _ _ _ _ X with "H● Hfb") as (c) "([%Hc %HcX] & H● & Hl & Hc)"; [done|].
    iMod ("IH" $! _ _ (c :: X) with "H● Hfbs")
      as (𝛼' cs) "([%Hlen [%Hnd [%HX [%Hphi [%Hrows %Hsame]]]]] & H● & Hls & Hcs)".
    iModIntro. iExists 𝛼', (c :: cs). rewrite /bcells ?fmap_cons big_sepL2_cons.
    iFrame "H● Hc Hcs". iSplit; last first.
    { rewrite big_sepL_cons shift_loc_0_nat. iFrame "Hl".
      iApply (big_sepL_impl with "Hls"). iIntros "!>" (i c' _) "H". by rewrite shift_loc_S. }
    iPureIntro. split_and!.
    - by rewrite /= Hlen.
    - constructor; [|done]. intros Hin. apply (HX c Hin). by left.
    - intros c' [->|Hin]%elem_of_cons; [done|]. intros HX'. apply (HX c' Hin). by right.
    - by rewrite Hphi phi_insert_loc insert_id // phi_lookup Hl0.
    - intros k cs' v c' Hk Hc'. destruct (Hrows k cs' v c' Hk Hc') as [?|(cs'' & Hk' & Hc'')].
      { left. by right. }
      destruct (decide (k = inl l)) as [->|Hne].
      + rewrite lookup_insert in Hk'. simplify_eq.
        apply elem_of_cons in Hc'' as [->|Hc'']; [by left; left|]. right. eauto.
      + rewrite lookup_insert_ne // in Hk'. right. eauto.
    - intros k Hk. rewrite Hsame.
      + rewrite lookup_insert_ne //. intros Heq. apply (Hk 0%nat); [simpl; lia|].
        by rewrite shift_loc_0_nat Heq.
      + intros i Hi. rewrite -shift_loc_S. apply (Hk (S i)). simpl. lia.
  Qed.

  (** An owned edge from a location in the range of a group with a write in flight gives a
      contradiction. *)
  Lemma cwentry_disj E R g e (p : loc) cv :
    ↑naN ⊆ E →
    ghost_map_auth heap_greg_name 1 R -∗ cwentry g e -∗ bpt (inl p) cv ={E}=∗
      ⌜∀ m cs, R !! g = Some (m, cs) → ∀ j : nat, (j < length cs)%nat → p ≠ e.1.1.1.1 +ₗ j⌝ ∗
      ghost_map_auth heap_greg_name 1 R ∗ cwentry g e ∗ bpt (inl p) cv.
  Proof.
    iIntros (?) "Hreg (%m & %cs & #Hg & Hgd & G & %P & %d & £ & #Guard & #HP) Hp".
    iDestruct (greg_lookup with "Hreg Hg") as %HR.
    destruct (decide (in_rng e.1.1.1.1 (length cs) p)) as [(j & Hj & ->)|Hn]; last first.
    { iModIntro. iFrame "Hreg Hp". iSplitR.
      { iPureIntro. intros m' cs' HR' j Hj ->. rewrite HR in HR'. simplify_eq. apply Hn. by exists j. }
      iExists m, cs. iSplitR; [iExact "Hg"|]. iFrame "Hgd G". iExists P, d. iFrame "£ Guard HP". }
    iMod (guards_open_later with "Guard G") as "Open"; [done|].
    iMod (lc_fupd_elim_laterN with "£ Open") as ">[P _]".
    iDestruct ("HP" with "P") as "[_ Hcs]".
    destruct (lookup_lt_is_Some_2 cs j) as [c Hc]; [done|].
    iDestruct (big_sepL_lookup with "Hcs") as "Hc"; [done|].
    iDestruct (fpt_excl with "Hp Hc") as "[]".
  Qed.

  Lemma cwentries_disj E R (CW : gmap positive (cwkey * iProp Σ)) (p : loc) cv :
    ↑naN ⊆ E →
    ghost_map_auth heap_greg_name 1 R -∗ ([∗ map] g ↦ e ∈ CW, cwentry g e) -∗ bpt (inl p) cv ={E}=∗
      ⌜∀ g e m cs, CW !! g = Some e → R !! g = Some (m, cs) →
         ∀ j : nat, (j < length cs)%nat → p ≠ e.1.1.1.1 +ₗ j⌝ ∗
      ghost_map_auth heap_greg_name 1 R ∗ ([∗ map] g ↦ e ∈ CW, cwentry g e) ∗ bpt (inl p) cv.
  Proof.
    iIntros (?) "Hreg HCW Hp". iInduction CW as [|g e CW Hg] "IH" using map_ind.
    { iFrame. iPureIntro. intros ????. by rewrite lookup_empty. }
    rewrite big_sepM_insert //. iDestruct "HCW" as "[He HCW]".
    iMod (cwentry_disj with "Hreg He Hp") as "(%H1 & Hreg & He & Hp)"; [done|].
    iMod ("IH" with "Hreg HCW Hp") as "(%H2 & $ & HCW & $)". iFrame. iPureIntro.
    intros g' e' m cs. destruct (decide (g = g')) as [<-|].
    - rewrite lookup_insert. intros [= <-]. apply H1.
    - rewrite lookup_insert_ne //. apply H2.
  Qed.

  Lemma cwentries_disj_fbytes E R (CW : gmap positive (cwkey * iProp Σ)) l fbs :
    ↑naN ⊆ E →
    ghost_map_auth heap_greg_name 1 R -∗ ([∗ map] g ↦ e ∈ CW, cwentry g e) -∗
    heap_mapsto_fbytes l fbs ={E}=∗
      ⌜∀ g e m cs, CW !! g = Some e → R !! g = Some (m, cs) →
         ∀ i j : nat, (i < length fbs)%nat → (j < length cs)%nat → l +ₗ i ≠ e.1.1.1.1 +ₗ j⌝ ∗
      ghost_map_auth heap_greg_name 1 R ∗ ([∗ map] g ↦ e ∈ CW, cwentry g e) ∗
      heap_mapsto_fbytes l fbs.
  Proof.
    iIntros (?) "Hreg HCW Hfbs". iInduction fbs as [|fb fbs] "IH" forall (l).
    { iFrame. iPureIntro. simpl. lia. }
    rewrite !heap_mapsto_fbytes_cons. iDestruct "Hfbs" as "[Hfb Hfbs]".
    iMod (cwentries_disj with "Hreg HCW Hfb") as "(%H1 & Hreg & HCW & $)"; [done|].
    iMod ("IH" with "Hreg HCW Hfbs") as "(%H2 & $ & $ & $)". iPureIntro.
    intros g e m cs Hg HR [|i] j Hi Hj.
    - rewrite shift_loc_0_nat. by eapply H1.
    - rewrite shift_loc_S. eapply H2; [done..|simpl in Hi; lia|done].
  Qed.

  (** ** Creating a cell group ([PCellFromOwn]) *)
  Lemma bytes_ctx_pcell_create E σB l m fbs fv :
    ↑naN ⊆ E → (0 < mty_size m)%nat →
    bytes_ctx σB -∗ heap_mapsto_fbytes l fbs -∗ brepr m fbs fv ={E}=∗ ∃ g cs,
      bytes_ctx σB ∗ loc_side l g m cs ∗ gdyn g fv ∗
      (if bool_decide (fv_cells fv = []) then gnocell g else True).
  Proof.
    iIntros (? Hsz) "(%𝛼 & %M & %Hr & %Hwf & H● & Hbank & Entries & Cells) Hfbs #Hrep".
    iDestruct "Cells" as (R ρ NC CW) "(Hreg & Hdyn & Hnc & Hcw & [%Hcwf %Hlive] & #HR & Hcwe & Hρ)".
    iDestruct (brepr_frepr with "Hreg Hrep") as %Hfrep.
    have Hlen : length fbs = mty_size m by eapply frepr_length; [apply Hcwf|done].
    iDestruct (fheap_no_dupes with "H●") as %Hnd.
    iDestruct (bheap_edges _ l (fb_rst <$> fbs) with "H● [Hfbs]") as %Hedges.
    { rewrite /heap_mapsto_fbytes big_sepL_fmap. done. }
    iMod (cwentries_disj_fbytes with "Hreg Hcwe Hfbs") as "(%Hcwd & Hreg & Hcwe & Hfbs)"; [done|].
    destruct Hcwf as (HRwf & HdomR & Hrefs & Hdisj & Hpos & HdomNC & HNC & HCW).
    destruct Hlive as [Hlive1 Hlive2].
    (* The groups embedded in [fv] are live. *)
    have Hlive_fv : ∀ g', g' ∈ fv_cells fv → g' ∈ dom ρ.
    { intros g' Hg'. destruct (frepr_cells_in _ _ _ _ _ Hfrep Hg') as (m' & cs' & HR' & Hin).
      have Hpos' := Hpos _ _ _ HR'. have Hlen' := HRwf _ _ _ HR'.
      destruct cs' as [|c cs']; [simpl in Hlen'; lia|].
      destruct (elem_of_list_lookup_1 _ _ (Hin c ltac:(set_solver))) as [i Hi].
      have := Hedges i (inl c). rewrite list_lookup_fmap Hi /=. intros Hp. specialize (Hp eq_refl).
      rewrite /𝛼_fine_pair in Hp. destruct (𝛼 !! inl (l +ₗ i)) as [[[|c0 rest] v]|] eqn:Hrow; try done.
      subst c0. destruct (Hlive1 _ _ _ c Hrow ltac:(set_solver)) as (g'' & m'' & cs'' & Hg'' & HR'' & Hc'').
      destruct (decide (g'' = g')) as [->|Hne]; [done|].
      exfalso. apply (Hdisj _ _ _ _ _ _ Hne HR'' HR' c); [done|set_solver]. }
    iMod (bheap_insert_fronts _ _ _ (reg_cells R) with "H● Hfbs")
      as (𝛼' cs) "([%Hlencs [%Hndcs [%HcsX [%Hphi [%Hrows %Hsame]]]]] & H● & Hls & Hcs)".
    set (g := fresh_gid R).
    have HgR : R !! g = None := fresh_gid_fresh R.
    have Hgρ : ρ !! g = None by apply not_elem_of_dom; intros ?; apply (not_elem_of_dom R g); [done|set_solver].
    have HgNC : NC !! g = None by apply not_elem_of_dom; intros ?; apply (not_elem_of_dom R g); [done|set_solver].
    have HgCW : (fst <$> CW) !! g = None.
    { destruct ((fst <$> CW) !! g) as [k|] eqn:Hk; [|done]. destruct (HCW g k Hk) as [Hρg _].
      by rewrite Hgρ in Hρg. }
    iMod (ghost_map_insert_persist g (m, cs) with "Hreg") as "[Hreg #Hg]"; [done|].
    iMod (ghost_map_insert g fv with "Hdyn") as "[Hdyn Hgd]"; [done|].
    set (NC' := if bool_decide (fv_cells fv = []) then <[g := ()]> NC else NC).
    iAssert (|==> ghost_map_auth heap_gnc_name 1 NC' ∗
      if bool_decide (fv_cells fv = []) then gnocell g else True)%I with "[Hnc]" as ">[Hnc Hgnc]".
    { rewrite /NC'. case_bool_decide; [|by iFrame].
      iMod (ghost_map_insert_persist g () with "Hnc") as "[$ $]"; done. }
    iModIntro. iExists g, cs. iFrame "Hgd Hgnc". iSplitR "Hls"; last by iFrame "Hg".
    iExists 𝛼', M. rewrite Hphi. iFrame "H● Hbank Entries". iSplit; [done|]. iSplit; [done|].
    iExists (<[g := (m, cs)]> R), (<[g := fv]> ρ), NC', CW. iFrame "Hreg Hdyn Hnc Hcw Hcwe".
    have HRsub : R ⊆ <[g := (m, cs)]> R by apply insert_subseteq.
    iSplit; [iPureIntro; split|].
    { (* cells_wf *)
      split_and!.
      - intros g' m' cs' Hg'. destruct (decide (g' = g)) as [->|Hne].
        + rewrite lookup_insert in Hg'. simplify_eq. by rewrite Hlencs.
        + rewrite lookup_insert_ne // in Hg'. by eapply HRwf.
      - rewrite !dom_insert_L. set_solver.
      - intros g' fv' Hg' g'' Hg''. destruct (decide (g' = g)) as [->|Hne].
        + rewrite lookup_insert in Hg'. simplify_eq. have Hd := Hlive_fv g'' Hg''.
          split; [apply fresh_gid_gt; set_solver|]. rewrite dom_insert_L. set_solver.
        + rewrite lookup_insert_ne // in Hg'. destruct (Hrefs g' fv' Hg' g'' Hg'').
          split; [done|]. rewrite dom_insert_L. set_solver.
      - intros g1 g2 m1 cs1 m2 cs2 Hne H1 H2.
        destruct (decide (g1 = g)) as [->|Hne1]; destruct (decide (g2 = g)) as [->|Hne2]; try done.
        + rewrite lookup_insert in H1. rewrite lookup_insert_ne // in H2. simplify_eq.
          intros c Hc1 Hc2. apply (HcsX c Hc1). by eapply reg_cells_in.
        + rewrite lookup_insert in H2. rewrite lookup_insert_ne // in H1. simplify_eq.
          intros c Hc1 Hc2. apply (HcsX c Hc2). by eapply reg_cells_in.
        + rewrite lookup_insert_ne // in H1. rewrite lookup_insert_ne // in H2.
          by apply (Hdisj g1 g2 m1 cs1 m2 cs2).
      - intros g' m' cs' Hg'. destruct (decide (g' = g)) as [->|Hne].
        + rewrite lookup_insert in Hg'. by simplify_eq.
        + rewrite lookup_insert_ne // in Hg'. by eapply Hpos.
      - rewrite /NC' dom_insert_L. case_bool_decide; rewrite ?dom_insert_L; set_solver.
      - intros g' fv' Hg' HNC'. destruct (decide (g' = g)) as [->|Hne].
        + rewrite lookup_insert in Hg'. simplify_eq. rewrite /NC' in HNC'. case_bool_decide; [done|].
          exfalso. by apply (not_elem_of_dom NC g).
        + rewrite lookup_insert_ne // in Hg'. apply (HNC g' fv' Hg').
          rewrite /NC' in HNC'. case_bool_decide; [|done]. rewrite dom_insert_L in HNC'. set_solver.
      - intros g' k Hk. destruct (HCW g' k Hk) as (Hρg & m' & cs' & HR' & Hb).
        have Hne : g' ≠ g by intros ->; rewrite HgCW in Hk.
        rewrite !lookup_insert_ne //. eauto. }
    { (* cells_live *)
      split.
      - intros k cs' v c Hk Hc. destruct (Hrows k cs' v c Hk Hc) as [Hcn|(cs'' & Hk' & Hc'')].
        + exists g, m, cs. rewrite dom_insert_L lookup_insert. split_and!; [set_solver|done|done].
        + destruct (Hlive1 k cs'' v c Hk' Hc'') as (g' & m' & cs0 & Hg' & HR' & Hc0).
          exists g', m', cs0. rewrite dom_insert_L. split_and!; [set_solver| |done].
          by eapply lookup_weaken.
      - intros g' k m' cs' Hk HR' i c Hc.
        have Hne : g' ≠ g by intros ->; rewrite HgCW in Hk.
        rewrite lookup_insert_ne // in HR'.
        destruct (Hlive2 g' k m' cs' Hk HR' i c Hc) as (rest & v & Hrow).
        exists rest, v. rewrite Hsame //. intros j Hj Heq.
        move: Hk. rewrite lookup_fmap. destruct (CW !! g') as [e|] eqn:He; [|done]. intros [= <-].
        apply (Hcwd g' e m' cs' He HR' j i); [lia|by eapply lookup_lt_Some|].
        symmetry. by apply inl_loc_inj in Heq. }
    (* the static registry and the contents *)
    iSplitR "Hcs Hρ". { rewrite big_sepM_insert //. by iFrame "HR Hg". }
    rewrite big_sepM_insert //. iSplitL "Hcs".
    - iExists m, cs, (fb_rst <$> fbs). iFrame "Hcs". iPureIntro. split_and!.
      + apply lookup_insert.
      + rewrite fb_strip_rst. by eapply frepr_mono.
      + intros i ls b. rewrite list_lookup_fmap. destruct (fbs !! i) as [[c|b']|]; simpl; try done.
        intros [= <- <-]. rewrite /cw_ls HgCW. done.
    - iApply (big_sepM_impl with "Hρ"). iIntros "!>" (g' fv' _) "H". by iApply gcontents_mono_R.
  Qed.

  (** The facts that the authority knows about the contents of all live groups. *)
  Lemma gcontents_edges 𝛼 R CW ρ :
    bheap 𝛼 -∗ ([∗ map] g ↦ fv ∈ ρ, gcontents R CW g fv) -∗
    ⌜map_Forall (λ g fv, ∃ m cs fbs, R !! g = Some (m, cs) ∧ frepr R m (fb_strip <$> fbs) fv ∧
       length cs = length fbs ∧
       (∀ (i : nat) c fb, cs !! i = Some c → fbs !! i = Some fb →
          𝛼_fine_pair loc positive bval 𝛼 (inr c) fb) ∧
       (∀ i ls b, fbs !! i = Some (inr (ls, b)) → ls = cw_ls CW g i)) ρ⌝.
  Proof.
    iIntros "H● Hρ". iInduction ρ as [|g fv ρ Hg] "IH" using map_ind.
    { iPureIntro. apply map_Forall_empty. }
    rewrite big_sepM_insert //.
    iDestruct "Hρ" as "[(%m & %cs & %fbs & (%HR & %Hrep & %Hls) & Hcs) Hρ]".
    iDestruct (bheap_cells with "H● Hcs") as %[Hlen Hfp].
    iDestruct ("IH" with "H● Hρ") as %Hrest. iPureIntro.
    apply map_Forall_insert; [done|]. split; [|done]. exists m, cs, fbs. done.
  Qed.

  Lemma has_pair_head_contra (c c' : positive) rest :
    NoDup (c :: rest) → list_has_pair (c :: rest) c' c → False.
  Proof.
    intros Hnd (cs1 & cs2 & Heq)%list_has_pair_destruct.
    destruct cs1 as [|c0 cs1]; simpl in Heq; injection Heq as -> Hrest.
    - subst rest. apply NoDup_cons in Hnd as [Hn _]. apply Hn. set_solver.
    - apply NoDup_cons in Hnd as [Hn _]. apply Hn. rewrite Hrest. set_solver.
  Qed.

  (** Deleting the front cells of rows. *)
  Lemma bheap_delete_fronts 𝛼 l cs fbs :
    bheap 𝛼 -∗ ([∗ list] i ↦ c ∈ cs, bpt (inl (l +ₗ i)) (inl c)) -∗ bcells cs fbs ==∗ ∃ 𝛼',
      ⌜bphi 𝛼' = bphi 𝛼 ∧
       (∀ k cs' v c, 𝛼' !! k = Some (cs', v) → c ∈ cs' →
          c ∉ cs ∧ ∃ cs'', 𝛼 !! k = Some (cs'', v) ∧ c ∈ cs'') ∧
       (∀ k, (∀ i : nat, (i < length cs)%nat → k ≠ inl (l +ₗ i)) → 𝛼' !! k = 𝛼 !! k)⌝ ∗
      bheap 𝛼' ∗ [∗ list] i ↦ fb ∈ fbs, bpt (inl (l +ₗ i)) fb.
  Proof.
    iInduction cs as [|c cs] "IH" forall (𝛼 l fbs); iIntros "H● Hls Hcs";
      destruct fbs as [|fb fbs]; rewrite /bcells /=; try by iDestruct "Hcs" as "[]".
    { iModIntro. iExists 𝛼. iFrame. iPureIntro. split_and!; [done| |done].
      intros k cs' v c Hk Hc. split; [by apply not_elem_of_nil|eauto]. }
    iDestruct "Hcs" as "[Hc Hcs]". iDestruct "Hls" as "[Hl Hls]".
    iEval (rewrite shift_loc_0_nat) in "Hl".
    iDestruct (fheap_no_dupes with "H●") as %Hnd.
    iMod (fcmap_delete_front with "H● Hl Hc") as (cs0 v0) "(%Hk & H● & Hl)".
    have Hnd0 : NoDup (c :: cs0) by eapply row_nodup.
    iMod ("IH" $! _ (l +ₗ 1) fbs with "H● [Hls] Hcs") as (𝛼') "([%Hphi [%Hrows %Hsame]] & H● & Hfbs)".
    { iApply (big_sepL_impl with "Hls"). iIntros "!>" (i c' _) "H". by rewrite shift_loc_S. }
    iModIntro. iExists 𝛼'. iFrame "H●". iSplit; last first.
    { iSplitL "Hl"; [by rewrite shift_loc_0_nat|].
      iApply (big_sepL_impl with "Hfbs"). iIntros "!>" (i fb' _) "H". by rewrite shift_loc_S. }
    iPureIntro. split_and!.
    - by rewrite Hphi phi_insert_loc insert_id // phi_lookup Hk.
    - intros k cs' v c' Hk' Hc'. destruct (Hrows k cs' v c' Hk' Hc') as [Hn (cs'' & Hk'' & Hc'')].
      destruct (decide (k = inl l)) as [->|Hne].
      + rewrite lookup_insert in Hk''. simplify_eq. split.
        * rewrite elem_of_cons. intros [->|?]; [|done]. apply NoDup_cons in Hnd0 as [Hn0 _]. done.
        * exists (c :: cs''). rewrite Hk. split; [done|set_solver].
      + rewrite lookup_insert_ne // in Hk''. split; [|eauto].
        rewrite elem_of_cons. intros [->|?]; [|done].
        eapply rows_disjoint; [exact Hnd|exact Hne|exact Hk''|exact Hk|exact Hc''|set_solver].
    - intros k Hk'. rewrite Hsame.
      + rewrite lookup_insert_ne //. intros Heq. apply (Hk' 0%nat); [simpl; lia|].
        by rewrite shift_loc_0_nat Heq.
      + intros i Hi. rewrite -shift_loc_S. apply (Hk' (S i)). simpl. lia.
  Qed.

  (** ** Destroying a cell group ([PCell2Own]) *)
  Lemma bytes_ctx_pcell_destroy σB l g m cs fv :
    bytes_ctx σB -∗ loc_side l g m cs -∗ gdyn g fv ==∗ ∃ fbs,
      bytes_ctx σB ∗ heap_mapsto_fbytes l fbs ∗ brepr m fbs fv.
  Proof.
    iIntros "(%𝛼 & %M & %Hr & %Hwf & H● & Hbank & Entries & Cells) [#Hg Hls] Hgd".
    iDestruct "Cells" as (R ρ NC CW) "(Hreg & Hdyn & Hnc & Hcw & [%Hcwf %Hlive] & #HR & Hcwe & Hρ)".
    iDestruct (greg_lookup with "Hreg Hg") as %HRg.
    iDestruct (gdyn_lookup with "Hdyn Hgd") as %Hρg.
    iAssert ⌜CW !! g = None⌝%I as %HgCW.
    { destruct (CW !! g) as [e|] eqn:He; [|done].
      iDestruct (big_sepM_lookup with "Hcwe") as "(%m' & %cs' & _ & Hgd' & _)"; [done|].
      iDestruct (gdyn_excl with "Hgd Hgd'") as "[]". }
    have HgCW' : (fst <$> CW) !! g = None by rewrite lookup_fmap HgCW.
    iDestruct (fheap_no_dupes with "H●") as %Hnd.
    iDestruct (loc_side_rows with "H● [$Hg $Hls]") as %Hrows0.
    iDestruct (gcontents_edges with "H● Hρ") as %Hedges.
    iDestruct (big_sepM_delete with "Hρ") as "[(%m' & %cs' & %fbs & (%HR' & %Hrep & %Hls) & Hcs) Hρ]"; [done|].
    rewrite HRg in HR'. injection HR' as <- <-.
    destruct Hcwf as (HRwf & HdomR & Hrefs & Hdisj & Hpos & HdomNC & HNC & HCW).
    destruct Hlive as [Hlive1 Hlive2].
    have Hcs0 : ∃ c0 cs0, cs = c0 :: cs0.
    { have := Hpos _ _ _ HRg. have := HRwf _ _ _ HRg. destruct cs; [simpl; lia|eauto]. }
    destruct Hcs0 as (c0 & cs0 & ->).
    iMod (bheap_delete_fronts with "H● Hls Hcs") as (𝛼') "([%Hphi [%Hrows %Hsame]] & H● & Hfbs)".
    iMod (ghost_map_delete with "Hdyn Hgd") as "Hdyn".
    iModIntro. iExists (fb_strip <$> fbs).
    iSplitR "Hfbs"; last iSplitL "Hfbs".
    2:{ rewrite /heap_mapsto_fbytes big_sepL_fmap. iApply (big_sepL_impl with "Hfbs").
        iIntros "!>" (i fb Hfb) "H". destruct fb as [c|[ls b]]; [done|].
        rewrite (Hls i ls b Hfb) /cw_ls HgCW'. done. }
    2:{ iExists R. iFrame "HR". done. }
    iExists 𝛼', M. rewrite Hphi. iFrame "H● Hbank Entries".
    iSplit; [done|]. iSplit; [done|].
    iExists R, (delete g ρ), NC, CW. iFrame "Hreg Hdyn Hnc Hcw HR Hcwe Hρ".
    iPureIntro. split; [split_and!|split].
    - done.
    - rewrite dom_delete_L. set_solver.
    - intros g' fv' Hg' g'' Hg''. apply lookup_delete_Some in Hg' as [Hne Hg'].
      destruct (Hrefs g' fv' Hg' g'' Hg'') as [Hlt Hdom]. split; [done|].
      rewrite dom_delete_L elem_of_difference. split; [done|]. rewrite elem_of_singleton.
      intros ->. destruct (Hedges g' fv' Hg') as (m'' & cs'' & fbs'' & HR'' & Hrep'' & Hlen'' & Hfp'' & _).
      destruct (frepr_cells_in _ _ _ _ _ Hrep'' Hg'') as (m3 & cs3 & HR3 & Hin3).
      rewrite HRg in HR3. simplify_eq.
      destruct (elem_of_list_lookup_1 _ _ (Hin3 c0 ltac:(set_solver))) as [i Hi].
      rewrite list_lookup_fmap in Hi. destruct (fbs'' !! i) as [fbi|] eqn:Hfbi; [|done].
      destruct fbi as [c2|[??]]; simpl in Hi; simplify_eq.
      destruct (lookup_lt_is_Some_2 cs'' i) as [c'' Hc'']; [rewrite Hlen''; by eapply lookup_lt_Some|].
      have Hp := Hfp'' i c'' (inl c0) Hc'' Hfbi. destruct Hp as (k & csk & vk & Hk & Hpair).
      destruct (Hrows0 0%nat c0 eq_refl) as (rest & v & Hrow). rewrite shift_loc_0_nat in Hrow.
      destruct (decide (k = inl l)) as [->|Hne'].
      + rewrite Hrow in Hk. simplify_eq. eapply has_pair_head_contra; [|done].
        by eapply row_nodup.
      + apply (rows_disjoint loc positive bval 𝛼 k (inl l) csk vk (c0 :: rest) v c0 Hnd Hne' Hk Hrow);
          [|set_solver]. by apply list_has_pair_elem_of in Hpair as [_ ?].
    - done.
    - done.
    - done.
    - intros g' fv' Hg' HNC'. apply lookup_delete_Some in Hg' as [_ Hg']. by eapply HNC.
    - intros g' k Hk. destruct (HCW g' k Hk) as [Hρg' Hrest]. split; [|done].
      rewrite lookup_delete_ne //. intros ->. by rewrite HgCW' in Hk.
    - intros k cs' v c Hk Hc. destruct (Hrows k cs' v c Hk Hc) as (Hnc & cs'' & Hk' & Hc').
      destruct (Hlive1 k cs'' v c Hk' Hc') as (g' & m' & cs3 & Hg' & HR3 & Hc3).
      exists g', m', cs3. split_and!; [|done|done]. rewrite dom_delete_L elem_of_difference.
      split; [done|]. rewrite elem_of_singleton. intros ->. rewrite HRg in HR3. by simplify_eq.
    - intros g' k m' cs' Hk HR' i c Hc. destruct (Hlive2 g' k m' cs' Hk HR' i c Hc) as (rest & v & Hrow).
      exists rest, v. rewrite Hsame //. intros j Hj Heq.
      apply inl_loc_inj in Heq.
      destruct (lookup_lt_is_Some_2 (c0 :: cs0) j) as [cj Hcj]; [done|].
      destruct (Hrows0 j cj Hcj) as (rest' & v' & Hrow'). rewrite -Heq Hrow in Hrow'. simplify_eq.
      have Hne : g' ≠ g by intros ->; rewrite HgCW' in Hk.
      apply (Hdisj g' g m' cs' m (c0 :: cs0) Hne HR' HRg cj); [by eapply elem_of_list_lookup_2|].
      by eapply elem_of_list_lookup_2.
  Qed.

  (** ** Untethering and retethering (moving a [PCell]) *)

  Lemma bheap_untethers 𝛼 l cs :
    bheap 𝛼 -∗ ([∗ list] i ↦ c ∈ cs, bpt (inl (l +ₗ i)) (inl c)) ==∗ ∃ 𝛼' (vs : list bval),
      ⌜length vs = length cs ∧ bphi 𝛼' = bphi 𝛼 ∧
       (∀ (i : nat) c v, cs !! i = Some c → vs !! i = Some v →
          ∃ rest, 𝛼 !! inl (l +ₗ i) = Some (c :: rest, v)) ∧
       (∀ k cs' v c, 𝛼' !! k = Some (cs', v) → c ∈ cs' →
          ∃ k' cs'', 𝛼 !! k' = Some (cs'', v) ∧ c ∈ cs'') ∧
       (∀ l', (∀ i : nat, (i < length cs)%nat → l' ≠ l +ₗ i) → 𝛼' !! inl l' = 𝛼 !! inl l')⌝ ∗
      bheap 𝛼' ∗ ([∗ list] i ↦ v ∈ vs, bpt (inl (l +ₗ i)) (inr v)) ∗
      ([∗ list] c; v ∈ cs; vs, ∃ u, bunt u c v).
  Proof.
    iInduction cs as [|c cs] "IH" forall (𝛼 l); iIntros "H● Hls".
    { iModIntro. iExists 𝛼, []. iFrame "H●". iSplit; [|by iSplit]. iPureIntro.
      split_and!; try done. intros k cs' v c Hk Hc. eauto. }
    iDestruct "Hls" as "[Hl Hls]". iEval (rewrite shift_loc_0_nat) in "Hl".
    iMod (fcmap_untether with "H● Hl") as (k cells1 cells2 v u) "([%Hrow %Hu] & H● & Hl & Hu)".
    destruct (is_row_for_lc_loc _ _ _ _ _ _ _ _ _ _ Hrow) as (-> & -> & Hk).
    iMod ("IH" $! _ (l +ₗ 1) with "H● [Hls]") as (𝛼' vs) "([%Hlen [%Hphi [%Hvs [%Hcells %Hsame]]]] & H● & Hvs & Hus)".
    { iApply (big_sepL_impl with "Hls"). iIntros "!>" (i c' _) "H". by rewrite shift_loc_S. }
    have Hu' : 𝛼 !! inr u = None by done.
    iModIntro. iExists 𝛼', (v :: vs). iFrame "H●". iSplit; last iSplitL "Hl Hvs".
    - iPureIntro. split_and!.
      + by rewrite /= Hlen.
      + rewrite Hphi /𝛼_untether phi_insert_loc phi_insert_unt insert_id // phi_lookup Hk //.
      + intros [|i] c' v' Hc' Hv'; simpl in Hc', Hv'; simplify_eq.
        * rewrite shift_loc_0_nat. eauto.
        * destruct (Hvs i c' v' Hc' Hv') as (rest & Hr). exists rest.
          rewrite /𝛼_untether lookup_insert_ne in Hr; [|intros [= Heq]; by apply (shift_loc_ne_S l i)].
          rewrite lookup_insert_ne // -shift_loc_S in Hr. done.
      + intros k' cs' v' c' Hk' Hc'. destruct (Hcells k' cs' v' c' Hk' Hc') as (k'' & cs'' & Hk'' & Hc'').
        rewrite /𝛼_untether in Hk''. destruct (decide (k'' = inl l)) as [->|Hne].
        { rewrite lookup_insert in Hk''. simplify_eq. by apply not_elem_of_nil in Hc''. }
        rewrite lookup_insert_ne // in Hk''. destruct (decide (k'' = inr u)) as [->|Hne'].
        { rewrite lookup_insert in Hk''. simplify_eq. exists (inl l), (c :: cells2). by split. }
        rewrite lookup_insert_ne // in Hk''. eauto.
      + intros l' Hl'. rewrite Hsame; last first.
        { intros i Hi. rewrite -shift_loc_S. apply (Hl' (S i)). simpl. lia. }
        rewrite /𝛼_untether lookup_insert_ne; last first.
        { intros [= ->]. apply (Hl' 0%nat); [simpl; lia|]. by rewrite shift_loc_0_nat. }
        by rewrite lookup_insert_ne.
    - iSplitL "Hl"; [by rewrite shift_loc_0_nat|].
      iApply (big_sepL_impl with "Hvs"). iIntros "!>" (i v' _) "H". by rewrite shift_loc_S.
    - iFrame "Hus". iExists u. by iFrame "Hu".
  Qed.

  Lemma bheap_retethers 𝛼 l cs (vs : list bval) :
    bheap 𝛼 -∗ ([∗ list] i ↦ v ∈ vs, bpt (inl (l +ₗ i)) (inr v)) -∗
    ([∗ list] c; v ∈ cs; vs, ∃ u, bunt u c v) ==∗ ∃ 𝛼',
      ⌜bphi 𝛼' = bphi 𝛼 ∧
       (∀ k cs' v c, 𝛼' !! k = Some (cs', v) → c ∈ cs' →
          ∃ k' cs'', 𝛼 !! k' = Some (cs'', v) ∧ c ∈ cs'') ∧
       (∀ l', (∀ i : nat, (i < length cs)%nat → l' ≠ l +ₗ i) → 𝛼' !! inl l' = 𝛼 !! inl l')⌝ ∗
      bheap 𝛼' ∗ [∗ list] i ↦ c ∈ cs, bpt (inl (l +ₗ i)) (inl c).
  Proof.
    iInduction cs as [|c cs] "IH" forall (𝛼 l vs); iIntros "H● Hvs Hus";
      destruct vs as [|v vs]; try by iDestruct (big_sepL2_length with "Hus") as %?.
    { iModIntro. iExists 𝛼. iFrame "H●". iSplit; [|done]. iPureIntro.
      split_and!; try done. intros k cs' v c Hk Hc. eauto. }
    iDestruct "Hvs" as "[Hv Hvs]". iEval (rewrite shift_loc_0_nat) in "Hv".
    iDestruct "Hus" as "[[%u Hu] Hus]".
    iMod (fcmap_retether with "H● Hv Hu") as (cs0) "([%Hl %Hu] & H● & Hl)".
    iMod ("IH" $! _ (l +ₗ 1) vs with "H● [Hvs] Hus") as (𝛼') "([%Hphi [%Hcells %Hsame]] & H● & Hls)".
    { iApply (big_sepL_impl with "Hvs"). iIntros "!>" (i v' _) "H". by rewrite shift_loc_S. }
    iModIntro. iExists 𝛼'. iFrame "H●". iSplit; last first.
    { iSplitL "Hl"; [by rewrite shift_loc_0_nat|].
      iApply (big_sepL_impl with "Hls"). iIntros "!>" (i c' _) "H". by rewrite shift_loc_S. }
    iPureIntro. split_and!.
    - rewrite Hphi phi_insert_loc phi_delete_unt insert_id // phi_lookup Hl //.
    - intros k cs' v' c' Hk' Hc'. destruct (Hcells k cs' v' c' Hk' Hc') as (k'' & cs'' & Hk'' & Hc'').
      destruct (decide (k'' = inl l)) as [->|Hne].
      { rewrite lookup_insert in Hk''. simplify_eq. exists (inr u), (c :: cs0). by split. }
      rewrite lookup_insert_ne // in Hk''. destruct (decide (k'' = inr u)) as [->|Hne'].
      { by rewrite lookup_delete in Hk''. }
      rewrite lookup_delete_ne // in Hk''. eauto.
    - intros l' Hl'. rewrite Hsame; last first.
      { intros i Hi. rewrite -shift_loc_S. apply (Hl' (S i)). simpl. lia. }
      rewrite lookup_insert_ne; last first.
      { intros [= ->]. apply (Hl' 0%nat); [simpl; lia|]. by rewrite shift_loc_0_nat. }
      by rewrite lookup_delete_ne.
  Qed.

  (** The final bytes of the rows through a group without a write in flight are not
      being written. *)
  Lemma row_end_rst 𝛼 R ρ NC (CW : gmap positive cwkey) g m cs :
    cells_no_dupes loc positive bval 𝛼 → cells_wf R ρ NC CW → cells_live 𝛼 R ρ CW →
    map_Forall (λ g fv, ∃ m cs fbs, R !! g = Some (m, cs) ∧ frepr R m (fb_strip <$> fbs) fv ∧
       length cs = length fbs ∧
       (∀ (i : nat) c fb, cs !! i = Some c → fbs !! i = Some fb →
          𝛼_fine_pair loc positive bval 𝛼 (inr c) fb) ∧
       (∀ i ls b, fbs !! i = Some (inr (ls, b)) → ls = cw_ls CW g i)) ρ →
    R !! g = Some (m, cs) → CW !! g = None →
    ∀ k c rest v, 𝛼 !! k = Some (c :: rest, v) → c ∈ cs → v.1 = RSt 0.
  Proof.
    intros Hnd Hwf [Hlive1 Hlive2] Hedges HRg HgCW k c rest v Hk Hc.
    destruct Hwf as (HRwf & HdomR & Hrefs & Hdisj & Hpos & HdomNC & HNC & HCW).
    destruct (exists_last (l:=c :: rest)) as (pre & cl & Heq); [done|].
    have Hcl : cl ∈ c :: rest by rewrite Heq; set_solver.
    destruct (Hlive1 k _ v cl Hk Hcl) as (g' & m' & cs' & Hg' & HR' & Hcl').
    apply elem_of_dom in Hg' as [fv' Hfv'].
    destruct (Hedges g' fv' Hfv') as (m'' & cs'' & fbs & HR'' & _ & Hlen & Hfp & Hls).
    rewrite HR' in HR''. injection HR'' as <- <-.
    destruct (elem_of_list_lookup_1 _ _ Hcl') as [j Hj].
    destruct (lookup_lt_is_Some_2 fbs j) as [fb Hfb]; [rewrite -Hlen; by eapply lookup_lt_Some|].
    have Hp := Hfp j cl fb Hj Hfb. have Hk' := Hk. rewrite Heq in Hk'.
    have Hfbv := row_end_pair loc positive bval 𝛼 k pre cl v fb Hnd Hk' Hp. rewrite Hfbv in Hfb.
    destruct v as [ls b]. rewrite (Hls j ls b Hfb) /cw_ls.
    destruct (CW !! g') as [e|] eqn:He; [|done]. exfalso.
    destruct (Hlive2 g' e m' cs' He HR' j cl Hj) as (rest' & v' & Hrow').
    destruct (decide (k = inl (e.1.1.1 +ₗ j))) as [->|Hne].
    - rewrite Hrow' in Hk. assert (cl = c) as -> by congruence.
      destruct (decide (g = g')) as [<-|Hne']; [by rewrite HgCW in He|].
      exact (Hdisj g g' m cs m' cs' Hne' HRg HR' c Hc Hcl').
    - apply (rows_disjoint loc positive bval 𝛼 k (inl (e.1.1.1 +ₗ j)) (pre ++ [cl]) (ls, b)
        (cl :: rest') v' cl Hnd Hne Hk' Hrow'); set_solver.
  Qed.

  Lemma bytes_ctx_pcell_untether E σB l g m cs :
    ↑naN ⊆ E →
    bytes_ctx σB -∗ loc_side l g m cs ={E}=∗ ∃ bs v,
      bytes_ctx σB ∗ l ↦b bs ∗ ⌜decode_value m bs = Some v⌝ ∗ untethered g m cs bs.
  Proof.
    iIntros (?) "(%𝛼 & %M & %Hr & %Hwf & H● & Hbank & Entries & Cells) [#Hg Hls]".
    iDestruct "Cells" as (R ρ NC CW) "(Hreg & Hdyn & Hnc & Hcw & [%Hcwf %Hlive] & #HR & Hcwe & Hρ)".
    iDestruct (greg_lookup with "Hreg Hg") as %HRg.
    iDestruct (fheap_no_dupes with "H●") as %Hnd.
    iDestruct (loc_side_rows with "H● [$Hg $Hls]") as %Hrows0.
    iDestruct (gcontents_edges with "H● Hρ") as %Hedges.
    iDestruct (cells_decode with "H● Hρ []") as %Hdec; [by iPureIntro|].
    iMod (cwentries_disj_fbytes _ _ _ l (inl <$> cs) with "Hreg Hcwe [Hls]")
      as "(%Hcwd & Hreg & Hcwe & Hls)"; [done| |].
    { rewrite /heap_mapsto_fbytes big_sepL_fmap. done. }
    iEval (rewrite /heap_mapsto_fbytes big_sepL_fmap) in "Hls".
    have Hcwf' := Hcwf. have Hlive' := Hlive.
    destruct Hcwf as (HRwf & HdomR & Hrefs & Hdisj & Hpos & HdomNC & HNC & HCW).
    destruct Hlive as [Hlive1 Hlive2].
    have Hcs0 : ∃ c0 cs0, cs = c0 :: cs0.
    { have := Hpos _ _ _ HRg. have := HRwf _ _ _ HRg. destruct cs; [simpl; lia|eauto]. }
    destruct Hcs0 as (c0 & cs0 & Hcs).
    destruct (Hrows0 0%nat c0 ltac:(by rewrite Hcs)) as (rest0 & v0 & Hrow0).
    rewrite shift_loc_0_nat in Hrow0.
    (* The group is live. *)
    have Hgρ : g ∈ dom ρ.
    { destruct (Hlive1 _ _ _ c0 Hrow0 ltac:(set_solver)) as (g' & m' & cs' & Hg' & HR' & Hc').
      destruct (decide (g' = g)) as [->|Hne]; [done|]. exfalso.
      apply (Hdisj _ _ _ _ _ _ Hne HR' HRg c0); [done|rewrite Hcs; set_solver]. }
    apply elem_of_dom in Hgρ as [fv Hfv].
    (* The group has no write in flight. *)
    have HgCW : (fst <$> CW) !! g = None.
    { destruct ((fst <$> CW) !! g) as [k|] eqn:Hk; [|done]. exfalso.
      destruct (Hlive2 g k m cs Hk HRg 0%nat c0 ltac:(by rewrite Hcs)) as (rest' & v' & Hrow').
      rewrite shift_loc_0_nat in Hrow'.
      apply lookup_fmap_Some in Hk as ([k' G] & <- & HkCW). simpl in Hrow'.
      destruct (decide (k'.1.1.1 = l)) as [Heq|Hne].
      - apply (Hcwd g (k', G) m cs HkCW HRg 0%nat 0%nat);
          [rewrite length_fmap Hcs /=; lia|rewrite Hcs /=; lia|].
        by rewrite /= !shift_loc_0_nat Heq.
      - apply (rows_disjoint loc positive bval 𝛼 (inl l) (inl k'.1.1.1) (c0 :: rest0) v0
          (c0 :: rest') v' c0 Hnd); [|done|done|set_solver|set_solver].
        intros Heq%inl_loc_inj. apply Hne. by rewrite Heq. }
    have Hends := row_end_rst 𝛼 R ρ NC (fst <$> CW) g m cs Hnd Hcwf' Hlive' Hedges HRg HgCW.
    iMod (bheap_untethers with "H● Hls")
      as (𝛼' vs) "([%Hlen [%Hphi [%Hvs [%Hcells %Hsame]]]] & H● & Hvs & Hus)".
    have Hvs' : ∀ (i : nat) v, vs !! i = Some v → v.1 = RSt 0.
    { intros i v Hv. destruct (lookup_lt_is_Some_2 cs i) as [c Hc];
        [rewrite -Hlen; by eapply lookup_lt_Some|].
      destruct (Hvs i c v Hc Hv) as [rest Hrow].
      eapply Hends; [done|by eapply elem_of_list_lookup_2]. }
    have Hfin : cell_final 𝛼 <$> cs = snd <$> vs.
    { apply list_eq. intros i. rewrite !list_lookup_fmap.
      destruct (cs !! i) as [c|] eqn:Hc; destruct (vs !! i) as [v|] eqn:Hv; rewrite ?Hv; simpl; try done.
      - destruct (Hvs i c v Hc Hv) as [rest Hrow]. rewrite /cell_final.
        erewrite row_of_spec; [|done|done|set_solver]. by destruct v.
      - apply lookup_lt_Some in Hc. apply lookup_ge_None in Hv. lia.
      - apply lookup_ge_None in Hc. apply lookup_lt_Some in Hv. lia. }
    destruct (Hdec g fv m cs Hfv HRg) as (v & _ & Hd).
    iModIntro. iExists (snd <$> vs), v.
    iSplitR "Hvs Hus"; last iSplitL "Hvs"; [|..|iSplit].
    - iExists 𝛼', M. rewrite Hphi. iFrame "H● Hbank Entries".
      iSplit; [done|]. iSplit; [done|]. iExists R, ρ, NC, CW.
      iFrame "Hreg Hdyn Hnc Hcw HR Hcwe Hρ". iPureIntro. split; [done|split].
      + intros k cs' v' c Hk Hc. destruct (Hcells k cs' v' c Hk Hc) as (k' & cs'' & Hk' & Hc').
        by eapply Hlive1.
      + intros g' k m' cs' Hk HR' i c Hc.
        destruct (Hlive2 g' k m' cs' Hk HR' i c Hc) as (rest & v' & Hrow).
        exists rest, v'. rewrite Hsame //. intros j Hj Heq.
        apply lookup_fmap_Some in Hk as ([k' G] & <- & HkCW).
        apply (Hcwd g' (k', G) m' cs' HkCW HR' j i);
          [by rewrite length_fmap|by eapply lookup_lt_Some|by rewrite Heq].
    - rewrite heap_mapsto_fbytes_bytes /heap_mapsto_fbytes !big_sepL_fmap.
      iApply (big_sepL_impl with "Hvs"). iIntros "!>" (i [ls b] Hv) "H".
      have /= Hls := Hvs' i _ Hv. by subst.
    - by rewrite -Hfin.
    - iFrame "Hg". rewrite big_sepL2_fmap_r. iApply (big_sepL2_impl with "Hus").
      iIntros "!>" (i c [ls b] Hc Hv) "H". have /= Hls := Hvs' i _ Hv. by subst.
  Qed.

  Lemma untethered_rows 𝛼 cs bs :
    bheap 𝛼 -∗ ([∗ list] c; b ∈ cs; bs, ∃ u, bunt u c (RSt 0, b)) -∗
    ⌜∀ (i : nat) c b, cs !! i = Some c → bs !! i = Some b →
       ∃ u rest, 𝛼 !! inr u = Some (c :: rest, (RSt 0, b))⌝.
  Proof.
    iInduction cs as [|c cs] "IH" forall (bs); iIntros "H● Hus";
      destruct bs as [|b bs]; try by iDestruct (big_sepL2_length with "Hus") as %?.
    iDestruct "Hus" as "[[%u Hu] Hus]". iDestruct (fheap_funt with "H● Hu") as %[rest Hrow].
    iDestruct ("IH" with "H● Hus") as %Hrest. iPureIntro.
    intros [|i] c' b' Hc Hb; simpl in Hc, Hb.
    - injection Hc as <-. injection Hb as <-. eauto.
    - eauto.
  Qed.

  (** Writing the bytes of plain untethered rows. *)
  Lemma bheap_write_unts 𝛼 cs (bs bs' : list abyte) fbs :
    length bs' = length cs → (∀ fb, fb ∈ fbs → ∃ x, fb = inr x) →
    bheap 𝛼 -∗ ([∗ list] c; b ∈ cs; bs, ∃ u, bunt u c (RSt 0, b)) -∗ bcells cs fbs ==∗ ∃ 𝛼',
      ⌜(∀ l, 𝛼' !! inl l = 𝛼 !! inl l) ∧
       (∀ k cs' v c, 𝛼' !! k = Some (cs', v) → c ∈ cs' →
          ∃ k' cs'' v', 𝛼 !! k' = Some (cs'', v') ∧ c ∈ cs'')⌝ ∗
      bheap 𝛼' ∗ ([∗ list] c; b ∈ cs; bs', ∃ u, bunt u c (RSt 0, b)) ∗
      bcells cs ((λ b, inr (RSt 0, b)) <$> bs').
  Proof.
    revert 𝛼 bs bs' fbs. induction cs as [|c cs IH]; intros 𝛼 bs bs' fbs Hlen Hpl;
      iIntros "H● Hus Hcs"; destruct bs' as [|b' bs']; simpl in Hlen; try lia;
      destruct bs as [|b bs]; try (by iDestruct (big_sepL2_length with "Hus") as %?);
      destruct fbs as [|fb fbs]; rewrite /bcells /=; try by iDestruct "Hcs" as "[]".
    { iModIntro. iExists 𝛼. iFrame "H●". iSplit; [|by iSplit]. iPureIntro.
      split; [done|]. intros k cs' v c Hk Hc. eauto. }
    iDestruct "Hus" as "[[%u Hu] Hus]". iDestruct "Hcs" as "[Hc Hcs]".
    iDestruct (fheap_no_dupes with "H●") as %Hnd.
    iDestruct (fheap_funt with "H● Hu") as %[rest Hrow].
    destruct (Hpl fb ltac:(set_solver)) as [x ->].
    iDestruct (fheap_fpt with "H● Hc") as %Hp.
    destruct (row_single loc positive bval 𝛼 (inr u) c rest (RSt 0, b) x Hnd Hrow Hp) as [-> <-].
    iMod (fcmap_write_unt loc positive bval _ _ u c [] _ (RSt 0, b') (inr c)
      with "H● Hu Hc") as "(H● & Hu & Hc)"; [done..|].
    iMod (IH _ bs bs' fbs with "H● Hus Hcs") as (𝛼') "([%Hinl %Hcells] & H● & Hus & Hcs)";
      [lia|set_solver|].
    iModIntro. iExists 𝛼'. iFrame "H● Hus Hcs Hc Hu". iPureIntro. split.
    - intros l. rewrite Hinl lookup_insert_ne //.
    - intros k cs' v c' Hk Hc'. destruct (Hcells k cs' v c' Hk Hc') as (k' & cs'' & v' & Hk' & Hc'').
      destruct (decide (k' = inr u)) as [->|Hne].
      + rewrite lookup_insert in Hk'. injection Hk' as <- <-. eauto.
      + rewrite lookup_insert_ne // in Hk'. eauto.
  Qed.

  (** Writing the bytes of an untethered group without cells. *)
  Lemma bytes_ctx_untethered_write σB g m cs bs bs' :
    decode_value m bs' = decode_value m bs →
    bytes_ctx σB -∗ untethered g m cs bs -∗ gnocell g ==∗ bytes_ctx σB ∗ untethered g m cs bs'.
  Proof.
    iIntros (Hdec') "(%𝛼 & %M & %Hr & %Hwf & H● & Hbank & Entries & Cells) [#Hg Hus] #Hnc'".
    iDestruct "Cells" as (R ρ NC CW) "(Hreg & Hdyn & Hnc & Hcw & [%Hcwf %Hlive] & #HR & Hcwe & Hρ)".
    iDestruct (greg_lookup with "Hreg Hg") as %HRg.
    iDestruct (gnocell_lookup with "Hnc Hnc'") as %HgNC.
    iDestruct (fheap_no_dupes with "H●") as %Hnd.
    iDestruct (cells_decode with "H● Hρ []") as %Hdec; [by iPureIntro|].
    iDestruct (big_sepL2_length with "Hus") as %Hlenbs.
    iDestruct (untethered_rows with "H● Hus") as %Hurows.
    destruct Hcwf as (HRwf & HdomR & Hrefs & Hdisj & Hpos & HdomNC & HNC & HCW).
    destruct Hlive as [Hlive1 Hlive2].
    have Hcs0 : ∃ c0 cs0 b0 bs0, cs = c0 :: cs0 ∧ bs = b0 :: bs0.
    { have := Hpos _ _ _ HRg. have := HRwf _ _ _ HRg.
      intros H1 H2. destruct cs as [|c0 cs0], bs as [|b0 bs0]; simpl in *; try lia. by eexists _, _, _, _. }
    destruct Hcs0 as (c0 & cs0 & b0 & bs0 & Hcs & Hbs).
    destruct (Hurows 0%nat c0 b0) as (u0 & rest0 & Hrow0); [by rewrite Hcs|by rewrite Hbs|].
    have Hgρ : g ∈ dom ρ.
    { destruct (Hlive1 _ _ _ c0 Hrow0 ltac:(set_solver)) as (g' & m' & cs' & Hg' & HR' & Hc').
      destruct (decide (g' = g)) as [->|Hne]; [done|]. exfalso.
      apply (Hdisj _ _ _ _ _ _ Hne HR' HRg c0); [done|rewrite Hcs; set_solver]. }
    apply elem_of_dom in Hgρ as [fv Hfv].
    have HgCW : (fst <$> CW) !! g = None.
    { destruct ((fst <$> CW) !! g) as [k|] eqn:Hk; [|done]. exfalso.
      destruct (Hlive2 g k m cs Hk HRg 0%nat c0 ltac:(by rewrite Hcs)) as (rest' & v' & Hrow').
      apply (rows_disjoint loc positive bval 𝛼 (inr u0) (inl (k.1.1.1 +ₗ 0%nat)) (c0 :: rest0)
        (RSt 0, b0) (c0 :: rest') v' c0 Hnd); [done|done|done|set_solver|set_solver]. }
    destruct (Hdec g fv m cs Hfv HRg) as (v & Herase & Hd).
    have Hfin : cell_final 𝛼 <$> cs = bs.
    { apply list_eq. intros i. rewrite !list_lookup_fmap.
      destruct (cs !! i) as [c|] eqn:Hc; destruct (bs !! i) as [b|] eqn:Hb; simpl; try done.
      - destruct (Hurows i c b Hc Hb) as (u & rest & Hrow). rewrite /cell_final.
        erewrite row_of_spec; [|done|done|set_solver]. done.
      - apply lookup_lt_Some in Hc. apply lookup_ge_None in Hb. lia.
      - apply lookup_ge_None in Hc. apply lookup_lt_Some in Hb. lia. }
    rewrite Hfin in Hd. rewrite Hd in Hdec'.
    have Hnocells := HNC g fv Hfv HgNC.
    have Hfv' := fval_erase_nocells _ _ _ Hnocells Herase. subst fv.
    iDestruct (big_sepM_delete with "Hρ") as "[(%m' & %cs' & %fbs & (%HR' & %Hrep & %Hls) & Hcs) Hρ]"; [done|].
    rewrite HRg in HR'. injection HR' as <- <-.
    have Hpl : ∀ fb, fb ∈ fbs → ∃ x, fb = inr x.
    { intros fb Hfb. have Hst : fb_strip fb ∈ fb_strip <$> fbs by apply elem_of_list_fmap_1.
      destruct (frepr_plain_of_nocells _ _ _ _ Hrep Hnocells _ Hst) as [b Hb].
      destruct fb as [c|x]; [done|eauto]. }
    have Hlen' : length bs' = length cs.
    { rewrite (decode_value_length _ _ _ Hdec') Hlenbs. symmetry. by eapply decode_value_length. }
    iMod (bheap_write_unts with "H● Hus Hcs") as (𝛼') "([%Hinl %Hcells] & H● & Hus & Hcs)"; [done..|].
    have Hphi : bphi 𝛼' = bphi 𝛼.
    { apply (map_eq (M:=gmap loc)). intros l. by rewrite !phi_lookup Hinl. }
    iModIntro. iSplitR "Hus"; last by iFrame "Hg".
    iExists 𝛼', M. rewrite Hphi. iFrame "H● Hbank Entries".
    iSplit; [done|]. iSplit; [done|]. iExists R, ρ, NC, CW.
    iFrame "Hreg Hdyn Hnc Hcw HR Hcwe". iSplit.
    { iPureIntro. split; [done|split].
      - intros k cs' v' c Hk Hc. destruct (Hcells k cs' v' c Hk Hc) as (k' & cs'' & v'' & Hk' & Hc').
        by eapply Hlive1.
      - intros g' k m' cs' Hk HR' i c Hc.
        destruct (Hlive2 g' k m' cs' Hk HR' i c Hc) as (rest & v' & Hrow).
        exists rest, v'. by rewrite Hinl. }
    iApply (big_sepM_delete _ _ g with "[Hcs $Hρ]"); [done|].
    iExists m, cs, ((λ b, inr (RSt 0, b)) <$> bs'). iFrame "Hcs". iPureIntro. split_and!.
    - done.
    - have -> : fb_strip <$> ((λ b, inr (RSt 0, b)) <$> bs') = inr <$> bs'.
      { rewrite -list_fmap_compose. apply list_fmap_ext. by intros. }
      by apply frepr_plain.
    - intros i ls b. rewrite list_lookup_fmap. destruct (bs' !! i); simpl; intros Heq;
        simplify_eq. by rewrite /cw_ls HgCW.
  Qed.

  Lemma bytes_ctx_pcell_retether_eq E σB l g m cs bs :
    ↑naN ⊆ E →
    bytes_ctx σB -∗ untethered g m cs bs -∗ l ↦b bs ={E}=∗ bytes_ctx σB ∗ loc_side l g m cs.
  Proof.
    iIntros (?) "(%𝛼 & %M & %Hr & %Hwf & H● & Hbank & Entries & Cells) [#Hg Hus] Hl".
    iDestruct "Cells" as (R ρ NC CW) "(Hreg & Hdyn & Hnc & Hcw & [%Hcwf %Hlive] & #HR & Hcwe & Hρ)".
    iDestruct (big_sepL2_length with "Hus") as %Hlen.
    rewrite heap_mapsto_fbytes_bytes.
    iMod (cwentries_disj_fbytes with "Hreg Hcwe Hl") as "(%Hcwd & Hreg & Hcwe & Hl)"; [done|].
    iMod (bheap_retethers _ l cs ((λ b, (RSt 0, b)) <$> bs) with "H● [Hl] [Hus]")
      as (𝛼') "([%Hphi [%Hcells %Hsame]] & H● & Hls)".
    { rewrite /heap_mapsto_fbytes !big_sepL_fmap. done. }
    { by rewrite big_sepL2_fmap_r. }
    iModIntro. iSplitR "Hls"; last by iFrame "Hg Hls".
    iExists 𝛼', M. rewrite Hphi. iFrame "H● Hbank Entries".
    iSplit; [done|]. iSplit; [done|]. iExists R, ρ, NC, CW.
    iFrame "Hreg Hdyn Hnc Hcw HR Hcwe Hρ". iPureIntro. destruct Hlive as [Hlive1 Hlive2].
    split; [done|split].
    - intros k cs' v c Hk Hc. destruct (Hcells k cs' v c Hk Hc) as (k' & cs'' & Hk' & Hc').
      by eapply Hlive1.
    - intros g' k m' cs' Hk HR' i c Hc.
      destruct (Hlive2 g' k m' cs' Hk HR' i c Hc) as (rest & v' & Hrow).
      exists rest, v'. rewrite Hsame //. intros j Hj Heq.
      apply lookup_fmap_Some in Hk as ([k' G] & <- & HkCW).
      apply (Hcwd g' (k', G) m' cs' HkCW HR' j i);
        [rewrite length_fmap; lia|by eapply lookup_lt_Some|by rewrite Heq].
  Qed.

  (** Retethering a moved group at [l], with bytes [bs'] that decode to the same value. The
      bytes may change only for a group without cells. *)
  Lemma bytes_ctx_pcell_retether E σB l g m cs bs bs' :
    ↑naN ⊆ E → decode_value m bs' = decode_value m bs →
    bytes_ctx σB -∗ untethered g m cs bs -∗ l ↦b bs' -∗ (⌜bs' = bs⌝ ∨ gnocell g) ={E}=∗
      bytes_ctx σB ∗ loc_side l g m cs.
  Proof.
    iIntros (? Hdec) "Hctx Hu Hl [->|#Hnc]".
    - by iApply (bytes_ctx_pcell_retether_eq with "Hctx Hu Hl").
    - iMod (bytes_ctx_untethered_write with "Hctx Hu Hnc") as "[Hctx Hu]"; [done|].
      by iApply (bytes_ctx_pcell_retether_eq with "Hctx Hu Hl").
  Qed.

  (** ** Values of groups, and fancy bytes of plain values and of cells *)
  Lemma brepr_plain m bs v : decode_value m bs = Some v → ⊢ brepr m (inr <$> bs) (fv_lift v).
  Proof.
    iIntros (Hd). iExists ∅. rewrite big_sepM_empty. iSplit; [|done]. iPureIntro.
    by apply frepr_plain.
  Qed.

  Lemma brepr_cell g m cs : greg g m cs -∗ brepr m (inl <$> cs) (FVCell g).
  Proof.
    iIntros "#Hg". iExists {[g := (m, cs)]}. rewrite big_sepM_singleton. iFrame "Hg".
    iPureIntro. apply frepr_cell. by rewrite lookup_singleton.
  Qed.

  Lemma brepr_cell_inv g m m' fbs cs :
    brepr m fbs (FVCell g) -∗ greg g m' cs -∗ ⌜m' = m ∧ fbs = inl <$> cs⌝.
  Proof.
    iIntros "(%R & %Hrep & #HR) #Hg". inversion Hrep as [m0 g0 cs0 Hg0| m0 bs v Hd Hv| |];
      subst.
    - iDestruct (big_sepM_lookup with "HR") as "Hg'"; [done|].
      iDestruct (greg_agree with "Hg Hg'") as %[-> ->]. done.
    - by destruct v.
  Qed.

  Lemma untethered_final 𝛼 cs bs :
    cells_no_dupes loc positive bval 𝛼 → length cs = length bs →
    (∀ (i : nat) c b, cs !! i = Some c → bs !! i = Some b →
       ∃ u rest, 𝛼 !! inr u = Some (c :: rest, (RSt 0, b))) →
    cell_final 𝛼 <$> cs = bs.
  Proof.
    intros Hnd Hlen Hurows. apply list_eq. intros i. rewrite list_lookup_fmap.
    destruct (cs !! i) as [c|] eqn:Hc; destruct (bs !! i) as [b|] eqn:Hb; simpl; try done.
    - destruct (Hurows i c b Hc Hb) as (u & rest & Hrow). rewrite /cell_final.
      erewrite row_of_spec; [|done|done|set_solver]. done.
    - apply lookup_lt_Some in Hc. apply lookup_ge_None in Hb. lia.
    - apply lookup_ge_None in Hc. apply lookup_lt_Some in Hb. lia.
  Qed.

  (** The bytes of a group in transit decode to the erasure of its fancy value. *)
  Lemma bytes_ctx_untethered_val σB g m cs bs fv :
    bytes_ctx σB -∗ untethered g m cs bs -∗ gdyn g fv -∗
    ⌜∃ v, decode_value m bs = Some v ∧ (fv_cells fv = [] → fv = fv_lift v)⌝.
  Proof.
    iIntros "(%𝛼 & %M & %Hr & %Hwf & H● & Hbank & Entries & Cells) [#Hg Hus] Hgd".
    iDestruct "Cells" as (R ρ NC CW) "(Hreg & Hdyn & Hnc & Hcw & [%Hcwf %Hlive] & #HR & Hcwe & Hρ)".
    iDestruct (greg_lookup with "Hreg Hg") as %HRg.
    iDestruct (gdyn_lookup with "Hdyn Hgd") as %Hfv.
    iDestruct (fheap_no_dupes with "H●") as %Hnd.
    iDestruct (cells_decode with "H● Hρ []") as %Hdec; [by iPureIntro|].
    iDestruct (big_sepL2_length with "Hus") as %Hlenbs.
    iDestruct (untethered_rows with "H● Hus") as %Hurows. iPureIntro.
    destruct (Hdec g fv m cs Hfv HRg) as (v & Herase & Hd).
    rewrite (untethered_final 𝛼 cs bs Hnd Hlenbs Hurows) in Hd.
    exists v. split; [done|]. intros Hc. by eapply fval_erase_nocells.
  Qed.

  (** Setting the value of a group without cells in transit. *)
  Lemma bytes_ctx_untethered_set σB g m cs bs bs' fv v' :
    decode_value m bs' = Some v' →
    bytes_ctx σB -∗ untethered g m cs bs -∗ gnocell g -∗ gdyn g fv ==∗
      bytes_ctx σB ∗ untethered g m cs bs' ∗ gdyn g (fv_lift v').
  Proof.
    iIntros (Hdec') "(%𝛼 & %M & %Hr & %Hwf & H● & Hbank & Entries & Cells) [#Hg Hus] #Hnc' Hgd".
    iDestruct "Cells" as (R ρ NC CW) "(Hreg & Hdyn & Hnc & Hcw & [%Hcwf %Hlive] & #HR & Hcwe & Hρ)".
    iDestruct (greg_lookup with "Hreg Hg") as %HRg.
    iDestruct (gnocell_lookup with "Hnc Hnc'") as %HgNC.
    iDestruct (gdyn_lookup with "Hdyn Hgd") as %Hfv.
    iDestruct (fheap_no_dupes with "H●") as %Hnd.
    iDestruct (big_sepL2_length with "Hus") as %Hlenbs.
    iDestruct (untethered_rows with "H● Hus") as %Hurows.
    destruct Hcwf as (HRwf & HdomR & Hrefs & Hdisj & Hpos & HdomNC & HNC & HCW).
    destruct Hlive as [Hlive1 Hlive2].
    have Hcs0 : ∃ c0 cs0 b0 bs0, cs = c0 :: cs0 ∧ bs = b0 :: bs0.
    { have := Hpos _ _ _ HRg. have := HRwf _ _ _ HRg.
      intros H1 H2. destruct cs as [|c0 cs0], bs as [|b0 bs0]; simpl in *; try lia.
      by eexists _, _, _, _. }
    destruct Hcs0 as (c0 & cs0 & b0 & bs0 & Hcs & Hbs).
    destruct (Hurows 0%nat c0 b0) as (u0 & rest0 & Hrow0); [by rewrite Hcs|by rewrite Hbs|].
    have HgCW : (fst <$> CW) !! g = None.
    { destruct ((fst <$> CW) !! g) as [k|] eqn:Hk; [|done]. exfalso.
      destruct (Hlive2 g k m cs Hk HRg 0%nat c0 ltac:(by rewrite Hcs)) as (rest' & v0 & Hrow').
      apply (rows_disjoint loc positive bval 𝛼 (inr u0) (inl (k.1.1.1 +ₗ 0%nat)) (c0 :: rest0)
        (RSt 0, b0) (c0 :: rest') v0 c0 Hnd); [done|done|done|set_solver|set_solver]. }
    have Hnocells := HNC g fv Hfv HgNC.
    iDestruct (big_sepM_delete with "Hρ") as "[(%m' & %cs' & %fbs & (%HR' & %Hrep & %Hls) & Hcs) Hρ]"; [done|].
    rewrite HRg in HR'. injection HR' as <- <-.
    have Hpl : ∀ fb, fb ∈ fbs → ∃ x, fb = inr x.
    { intros fb Hfb. have Hst : fb_strip fb ∈ fb_strip <$> fbs by apply elem_of_list_fmap_1.
      destruct (frepr_plain_of_nocells _ _ _ _ Hrep Hnocells _ Hst) as [b Hb].
      destruct fb as [c|x]; [done|eauto]. }
    have Hlen' : length bs' = length cs.
    { rewrite (decode_value_length _ _ _ Hdec'). symmetry. by eapply HRwf. }
    iMod (bheap_write_unts with "H● Hus Hcs") as (𝛼') "([%Hinl %Hcells] & H● & Hus & Hcs)"; [done..|].
    iMod (ghost_map_update (fv_lift v') with "Hdyn Hgd") as "[Hdyn Hgd]".
    have Hphi : bphi 𝛼' = bphi 𝛼.
    { apply (map_eq (M:=gmap loc)). intros l. by rewrite !phi_lookup Hinl. }
    have Hgdom : g ∈ dom ρ by apply elem_of_dom_2 in Hfv.
    have Hdom' : dom (<[g := fv_lift v']> ρ) = dom ρ.
    { rewrite dom_insert_L. set_solver. }
    iModIntro. iSplitR "Hus Hgd"; last by iFrame "Hg Hgd".
    iExists 𝛼', M. rewrite Hphi. iFrame "H● Hbank Entries".
    iSplit; [done|]. iSplit; [done|]. iExists R, (<[g := fv_lift v']> ρ), NC, CW.
    iFrame "Hreg Hdyn Hnc Hcw HR Hcwe". iSplit.
    { iPureIntro. split; [split_and!|split].
      - done.
      - by rewrite Hdom'.
      - intros g' fv'' Hg' g'' Hg''. destruct (decide (g' = g)) as [->|Hne].
        + rewrite lookup_insert in Hg'. injection Hg' as <-. rewrite fv_cells_lift in Hg''. by apply not_elem_of_nil in Hg''.
        + rewrite lookup_insert_ne // in Hg'. rewrite Hdom'. by eapply Hrefs.
      - done.
      - done.
      - done.
      - intros g' fv'' Hg' HNC'. destruct (decide (g' = g)) as [->|Hne].
        + rewrite lookup_insert in Hg'. injection Hg' as <-. apply fv_cells_lift.
        + rewrite lookup_insert_ne // in Hg'. by eapply HNC.
      - intros g' k Hk. destruct (HCW g' k Hk) as [Hρg' Hrest]. split; [|done].
        rewrite lookup_insert_ne //. intros ->. by rewrite HgCW in Hk.
      - intros k cs' v'' c Hk Hc. destruct (Hcells k cs' v'' c Hk Hc) as (k' & cs'' & v3 & Hk' & Hc').
        rewrite Hdom'. by eapply Hlive1.
      - intros g' k m' cs' Hk HR' i c Hc.
        destruct (Hlive2 g' k m' cs' Hk HR' i c Hc) as (rest & v'' & Hrow).
        exists rest, v''. by rewrite Hinl. }
    iApply big_sepM_insert_delete. iFrame "Hρ".
    iExists m, cs, ((λ b, inr (RSt 0, b)) <$> bs'). iFrame "Hcs". iPureIntro. split_and!.
    - done.
    - have -> : fb_strip <$> ((λ b, inr (RSt 0, b)) <$> bs') = inr <$> bs'.
      { rewrite -list_fmap_compose. apply list_fmap_ext. by intros. }
      by apply frepr_plain.
    - intros i ls b. rewrite list_lookup_fmap. destruct (bs' !! i); simpl; intros Heq;
        simplify_eq. by rewrite /cw_ls HgCW.
  Qed.

  Lemma brepr_plain_inv m fbs v :
    brepr m fbs (fv_lift v) -∗ ⌜∃ bs, fbs = inr <$> bs ∧ decode_value m bs = Some v⌝.
  Proof.
    iIntros "(%R & %Hrep & _)". iPureIntro.
    have Hpl := frepr_plain_of_nocells _ _ _ _ Hrep (fv_cells_lift v).
    destruct (frepr_decode R ∅ (λ _, Uninit) m fbs (fv_lift v) Hrep) as (v' & Her & Hd).
    { intros g m' cs Hg. rewrite fv_cells_lift in Hg. by apply not_elem_of_nil in Hg. }
    have Heq := fval_erase_det _ _ _ _ (fval_erase_lift ∅ v) Her. subst v'.
    exists (fin_bytes (λ _, Uninit) fbs). split; [|done].
    apply list_eq. intros i. rewrite /fin_bytes !list_lookup_fmap.
    destruct (fbs !! i) as [fb|] eqn:Hfb; [|done].
    destruct (Hpl fb ltac:(by eapply elem_of_list_lookup_2)) as [b ->]. done.
  Qed.
End cells.

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
    iDestruct "σ" as (σL σB) "(%Hr & σ & σB)".
    have Hfr : init_mem (l +ₗ 1) n σ !! l = None.
    { rewrite lookup_init_mem_ne /=; last lia. rewrite -(shift_loc_0 l). apply Hfresh. }
    destruct (phys_rel_None _ _ _ _ Hr Hfr) as [HL HB].
    iMod (bytes_ctx_alloc _ _ Uninit with "σB") as "[σB Hb]"; [done|].
    iModIntro. rewrite /= (heap_mapsto_bytes_cons _ Uninit). iFrame.
    iSplitR; [iPureIntro; by apply phys_rel_B_insert|].
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
    iDestruct "σ" as (σL σB) "(%Hr & σ & σB)".
    rewrite heap_mapsto_bytes_eq /heap_mapsto_bytes_def /heap_mapsto_st_vec /= shift_loc_0.
    iDestruct "Hb" as "[Hb _]".
    iMod (bytes_ctx_dealloc with "σB Hb") as "[%Hl σB]"; [done|].
    iModIntro. iFrame. iPureIntro. apply phys_rel_B_delete; [done|].
    eapply phys_rel_B_not_L; [done|]. by eexists.
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

  (** ** Moving locations between the legacy region and the byte region *)
  Lemma heap_word_to_bytes (σ : state') l v E :
    ↑naN ⊆ E →
    heap_maps_ctx σ -∗ l ↦ v ={E}=∗ heap_maps_ctx σ ∗ l ↦b [word_to_byte v].
  Proof.
    iIntros (?) "(%σL & %σB & %Hr & σ & σB) Hl". rewrite /heap_mapsto.
    iMod (non_atomic_map_delete with "Hl σ") as "[%HL σ]"; [done|].
    have HB := phys_rel_L_not_B _ _ _ _ Hr (mk_is_Some _ _ HL).
    iMod (bytes_ctx_alloc _ _ (word_to_byte v) with "σB") as "[σB Hb]"; [done|].
    iModIntro. iFrame. iSplitR; [iPureIntro; by apply phys_rel_L_to_B|].
    rewrite heap_mapsto_bytes_eq /heap_mapsto_bytes_def /heap_mapsto_st_vec /=.
    rewrite shift_loc_0. by iFrame.
  Qed.

  Lemma heap_bytes_to_word (σ : state') l v E :
    ↑naN ⊆ E →
    heap_maps_ctx σ -∗ l ↦b [word_to_byte v] ={E}=∗ heap_maps_ctx σ ∗ l ↦ v.
  Proof.
    iIntros (?) "(%σL & %σB & %Hr & σ & σB) Hb".
    rewrite heap_mapsto_bytes_eq /heap_mapsto_bytes_def /heap_mapsto_st_vec /= shift_loc_0.
    iDestruct "Hb" as "[Hb _]".
    iMod (bytes_ctx_dealloc with "σB Hb") as "[%HB σB]"; [done|].
    have HL := phys_rel_B_not_L _ _ _ _ Hr (mk_is_Some _ _ HB).
    iMod (non_atomic_map_insert _ l v with "σ") as "[Hl σ]"; [done|].
    iModIntro. iFrame. iSplitR; [iPureIntro; by apply phys_rel_B_to_L|]. by rewrite /heap_mapsto.
  Qed.

  Lemma heap_words_to_bytes (σ : state') l vl E :
    ↑naN ⊆ E →
    heap_maps_ctx σ -∗ l ↦∗ vl ={E}=∗ heap_maps_ctx σ ∗ l ↦b (word_to_byte <$> vl).
  Proof.
    iIntros (?). iInduction vl as [|v vl] "IH" forall (l); iIntros "σ Hvl".
    { iFrame. by rewrite heap_mapsto_bytes_nil. }
    rewrite heap_mapsto_vec_cons fmap_cons heap_mapsto_bytes_cons.
    iDestruct "Hvl" as "[Hv Hvl]".
    iMod (heap_word_to_bytes with "σ Hv") as "[σ $]"; [done|].
    iApply ("IH" with "σ Hvl").
  Qed.

  Lemma heap_bytes_to_words (σ : state') l vl E :
    ↑naN ⊆ E →
    heap_maps_ctx σ -∗ l ↦b (word_to_byte <$> vl) ={E}=∗ heap_maps_ctx σ ∗ l ↦∗ vl.
  Proof.
    iIntros (?). iInduction vl as [|v vl] "IH" forall (l); iIntros "σ Hvl".
    { iFrame. by rewrite heap_mapsto_vec_nil. }
    rewrite heap_mapsto_vec_cons fmap_cons heap_mapsto_bytes_cons.
    iDestruct "Hvl" as "[Hv Hvl]".
    iMod (heap_bytes_to_word with "σ Hv") as "[σ $]"; [done|].
    iApply ("IH" with "σ Hvl").
  Qed.
End bytes_ctx.
