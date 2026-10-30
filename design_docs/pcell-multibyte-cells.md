# PCell on the byte memory model: multi-byte cells

Status: design draft (2026-10-30), branch `memory-model`.
Context: `design_docs/minirust-memory-model.md` (stages 1–5). `pcell` is the last user of the
legacy word layer.

## 1. Problem

Moving a `PCell<T>` (≈ `UnsafeCell<T>`) is a *typed* copy: a `Load` at some mty, followed by a
`Store` of the decoded value. This decode-encode round trip may change bytes: padding becomes
`Uninit`, and only the decoded value survives.

The existing untether machinery assumes a byte-for-byte (word-for-word) `memcpy`:

    mapsto_vec_untether : l #↦!∗ fv ={E}=∗ ∃ v, l #↦∗ v ∗ (∀ l₁, l₁ #↦∗_ ∗ l₁ #↦∗ v ={F}=∗ l₁ #↦∗_ ∗ l₁ #↦!∗ fv)

The retether at `l₁` requires the *same* words `v`. It also tells the mover nothing about `v`:
the cell's contents are owned by whoever holds the cell permission, not by the mover.

For a typed move we need three things:
- **Decodability at untether time.** Untethering gives the mover the bytes `bs` together with
  `decode m bs = Some v`, where `m` is the cell's fixed mty. This is the mty to `Load` at.
- **Retether with a value.** Retethering accepts *any* bytes `bs'` with `decode m bs' = Some v`,
  for the same `v`. `encode m v` (from the `Store`) qualifies, and so does a verbatim
  `MemCopy` of `bs`.
- **Multi-byte cells.** One cell spans the `mty_size m` bytes of a value, and holds a
  *fancy MiniRust value*: a MiniRust value that may embed further cells.

## 2. The current machinery

**`util/cellmap.v`, generic in `L` (locations), `C` (cell ids) and `V` (values):**
- The ghost state is a `full_map : gmap (L + untether_id) (list C * V)`. Each location, or
  untethered row `inr u`, has a chain of cells ending in a value.
- The physical heap is `𝜙 α`: a location's value is the end of its chain. Untethered rows are not
  in physical memory.
- Fragments live in a `fine_map : gmap (L + C) (C + V)`: single edges `lc ↦ next`.
- `unt_map` records untethered rows.
- Operations: `alloc`, `delete`, `write` (at the end of a chain), `insert_fresh_cell` (after a
  chain element), `untether`, `retether` and `delete_cell`, each preserving `big_inv`.

**`util/non_atomic_cell_map.v`** layers per-location `lock_state` (`RSt n` / `WSt`) on top:
- a **read bank** holds guards `G &&> inl l @↦[^cells] inr v` while a non-atomic read is in
  flight;
- a **write bank** holds, while a non-atomic write is in flight, the guarded chain *and the
  ownership of the last cell's contents* (`inr cell @↦ inr v`).

**`lang/heap.v` instantiates it with `V = val`** (the legacy region):
- `fancy_val := FVal val | FCell cell_id`;
- `l ↦[^ cells]! fv` and `cloc = loc * list (list cell_id)` (one chain per word);
- `c ^↦! fv`, and the untether lemmas `mapsto_vec_untether(1|')`.

The byte region (`l ↦b bs`) has **no cells**.

**`typing/pcell.v`:**
- `pcell_ty n`, with `ty_phys = FCell <$> cell_ids`;
- `cell_points_to_ty ty`, which owns `cells ^↦!∗ ty_phys x` plus `▷ gho_own`;
- rules: `from_own`, `to_own`, `borrow`, `borrow_mut`, and atomic load, store and CAS.

## 3. Design

### D1. Cells are per byte; a cell group is a multi-byte cell

Instantiate the cell map with `V = abyte`, so cells live in the byte region. Each byte location
keeps its own chain of **byte-cells**, which reuses all of `cellmap.v` unchanged. Add one layer on
top: a **cell group**

    g = (m_g : mty, cs_g : list C)   with   length cs_g = mty_size m_g

The group is registered persistently (an agreement map `g ↦ (m_g, cs_g)`). It is the
"multi-byte cell" `c = (c1, …, cn)`: byte i of the value lives in byte-cell `cs_g !! i`.

*Why per-byte chains plus groups,* rather than making `C` itself n-wide inside `cellmap.v`:
- **Nesting comes for free.** A byte inside a nested `PCell` has the chain
  `l ↦ c_outer_i ↦ c_inner_i ↦ byte`.
- **Partial overlaps stay simple.** Byte-level operations such as `MemCopy` and sub-field stores
  keep acting on single chains.
- **The algebra stays untouched.** `cellmap.v`'s invariants and update lemmas don't change.

The alternative (D1′) is a group-native cell map, with edges `(L + C × idx) → …`. It is cleaner
conceptually, but it means re-proving `cellmap.v`.

### D2. Fancy MiniRust values

    FValue := FVInt Z | FVBool bool | FVPtr loc | FVTuple (list FValue)
            | FVVariant Z FValue | FVCell (g: group_id)

- **Erasure.** `⌊fv⌋_ρ : Value` replaces each `FVCell g` with `ρ g`, the group's current
  (concrete) value.
- **Representation.** `represents m bs fv` is a relation over the group registry: `bs`
  represents `fv` at mty `m` when
  - non-cell parts decode as `decode` does;
  - every `FVCell g'` occupies exactly a sub-range whose sub-mty is `m_{g'}` (alignment
    requirement A below), with those bytes representing `g'`'s value.
- **Compositionality lemma.** `represents m bs fv → decode m bs = Some ⌊fv⌋`.

**Alignment requirement A.** A nested cell may only sit at a position where `m` has a sub-mty
that is the *whole* value: a tuple field, an enum payload, or the whole value. A cell may never
cover part of an int or pointer. That's what makes decoding compositional: `MTuple`/`MEnum`
decode field-wise.

### D3. The decodability invariant

The byte-region context gains an authoritative map `fv_g` (each group's current fancy value) and
this invariant:

    ∀ g, (no byte of g's chains is in WSt) →
         represents m_g (final bytes of cs_g) fv_g

The fragment `g ↦fv fv` is held by the cell permission (`cell_points_to`), together with the
ownership of the group's byte-cell contents.

**Non-atomicity** is handled as in `non_atomic_cell_map`:
- a byte that is in `WSt` (a write in flight; its contents sit in the write bank) exempts its
  group from the invariant;
- since `Store` and `MemCopy` are two-phase over the *whole* range, phase 1 marks the range
  `WSt` and changes no bytes;
- phase 2 writes all bytes at once and leaves `WSt`. At that commit, the writer proves the
  invariant for the new bytes and updates `fv_g`.

So decodability is broken only between the two phases of one write. A finer-grained (per-byte)
write semantics later would need no change to the invariant: the `WSt` exemption covers it.

### D4. Assertions

- **Fancy byte points-to:** `l ↦b[^ chains] fbs` (one chain per byte), generalising `↦b` and
  the legacy `↦[^cells]!`.
- **Byte-cell edges:** `c ^↦b fb`, generalising `c ^↦! fv`.
- **The group permission:** `g ^↦ₘ fv` := `g ↦fv fv` ∗ the contents of `cs_g` ∗ `⌜represents …⌝`.
  It is what `cell_points_to` owns, and it is value-level, so moves (which change bytes) don't
  disturb it.
- **The location side of a PCell:** `l ↦b[^ [g]] _`, the chains `l+i ↦ cs_g !! i`.

### D5. Operations and their lemmas

1. **Create (`PCellFromOwn`).**
   - From `l ↦b bs` with `ty_bytes ty x bs` (so `decode m bs = Some v`), with `m := ty_mty ty`.
   - Insert fresh byte-cells after each location (`insert_fresh_cell`) and register group
     `g = (m, cs)` with `fv_g := lift v` (no nested cells).
   - Gives the location chains (the `PCell`) and `g ^↦ₘ lift v` (the permission).
   - If `x` contains nested cells, `fv_g` contains `FVCell`s instead.
2. **Destroy (`PCell2Own`).** From the location chains and `g ^↦ₘ fv`: delete the byte-cells
   (`delete_cell`), giving `l ↦b bs` with `represents m_g bs fv`.
3. **Read through the cell.** Typed `Load m'` at a sub-position, under a guard of the location
   chain, as in `wp_load_*_guarded_gen`. With the permission, or a guard of it, the decoded value
   is known from `fv_g`.
4. **Write through the cell.** Typed `Store m'` (or `MemCopy`) at a sub-position, using the write
   bank. At commit, require that the new bytes keep `represents` (field-wise, by
   compositionality) and update `fv_g` at that sub-position.
   - Overwriting a nested cell's range requires that cell's permission: it is a write to the
     inner group.
   - `&mut T` borrows into a cell (`borrow_mut`) hand out exactly this "write at a sub-position"
     capability.
5. **Untether, for moving a PCell.**

       pcell_untether : l ↦b[^ [g]] _ ={E}=∗ ∃ bs v,
           l ↦b bs ∗ ⌜decode m_g bs = Some v⌝ ∗ untethered g v ∗
           (∀ l₁ bs', l₁ ↦b bs' -∗ ⌜decode m_g bs' = Some v⌝ -∗ untethered g v ={F}=∗ l₁ ↦b[^ [g]] _)

   - Owning the location chains exclusively means no write is in flight: writers need a guard
     of those chains. So D3 applies and gives `decode m_g bs = Some v`.
   - Neither `bs` nor `v` is otherwise known to the mover.
   - `untethered g v` is the group's chains in untethered rows (`inr u`). It is the *root* form of
     a `PCell` in transit: the result of the `Load m_g`, a `Value v`, typed as "PCell `g` whose
     content decodes to `v`".
   - Retethering after `Store m_g v` at `l₁` uses `decode m_g (encode m_g v) = Some v`
     (`decode_encode_value`). After a verbatim `MemCopy`, it uses `bs' = bs`.
6. **Atomics (load, store, CAS).** Single-phase, so atomic. Same invariant obligations as 3 and 4.

### D6. Types

- **`pcell_ty m`:**
  - `ty_mty = m` (the content's mty);
  - `ty_val = None` (a PCell isn't decodable as a plain `Value` on its own; generic `Load` rules
    don't apply);
  - it gets a **fancy value** `ty_fval x = Some (FVCell g)`.
- **Parents own fancy bytes.** Generalise the parents' byte ownership from
  `∃ bs, l ↦b bs ∗ ⌜decode (ty_mty ty) bs = ty_val x⌝` to
  `∃ fbs, l ↦b[^chains] fbs ∗ ⌜represents (ty_mty ty) fbs (ty_fval x)⌝`. This is the plan's
  "parent keeps fancy abstract bytes". For types without cells, `ty_fval = lift ∘ ty_val` and
  this reduces to today's form.
- **`cell_points_to_ty ty`** owns `g ^↦ₘ fv`, with `⌊fv⌋ = ty_val x` (or the fancy version for
  nested cells), plus `▷ gho_own x`.
- **New place-level rules:**
  - moving a `PCell` place: untether, `Load`, `Store`, retether;
  - `from_own`, `to_own`, `borrow`, `borrow_mut` and the atomics, restated on bytes.

### D7. Payoff

Once `pcell` runs on the byte region, nothing uses the legacy word layer any more. Stage 5 can
then finish:
- delete `ty_phys`, `syn_phys` and the sum padding;
- delete `Word` bytes, the legacy `Read`/`Write`/`CAS`, and `phys_rel`;
- delete the legacy `own_ptr`/`&shr`/`&uniq`/`fn` types and the core rules;
- delete the second ghost region;
- restore the plain names of the `b`-prefixed definitions;
- make `ty_size` the byte size.

## 4. Plan

1. Byte cell map: instantiate `non_atomic_cell_map` at `V = abyte` for the byte region, replacing
   its plain fractional heap. Bring the guarded-read bank of stage 4 into line with the read bank.
2. Groups and fancy values: `FValue`, `represents`, the compositionality lemma, the group
   registry, and the invariant D3 in the byte context.
3. The lemmas of D5, with WP-level tests: create, write, read, untether + `Load`/`Store` +
   retether, destroy, and a nested cell.
4. Types (D6): `ty_fval`, parents on fancy bytes, `pcell_ty`, `cell_points_to_ty`, and the
   ported pcell rules and examples (`pcell_example`, `ra`, `protocol`).
5. Finish stage 5 (D7).

## 5. Open questions

1. **D1 vs D1′:** per-byte chains plus a group registry (recommended), or a group-native cell map?
2. **Alignment requirement A:** may nested cells only sit at whole-sub-value positions (fields,
   enum payloads, the whole value)? Recommended.
3. **Fancy values in parents (D6):** generalise `ty_val` to `ty_fval`, or keep `ty_val` and
   handle cells only in the PCell rules? Recommended: `ty_fval`, so that structs containing
   `PCell` fields work in places.
4. **Root form of a PCell in transit:** `untethered g v` (the content value travels as the
   `Value`, the identity as the ghost group). Confirm.
5. **Sub-position writes through `&mut T` into a cell:** support them from the start, or begin
   with whole-value replacement (`replace`/`put`/`take`) and add `borrow_mut` writes afterwards?
6. **Mixed-size atomics on cells,** e.g. an atomic store at a sub-mty: allow them? With the
   two-phase-free atomic semantics, they're no harder than D5.4.

## 6. Decisions (user, 2026-10-30)

1. **D1:** per-byte chains plus a group registry.
2. **Alignment requirement A** is adopted: nested cells sit only at whole-sub-value positions
   (tuple fields, enum payloads, the whole value), never covering part of an int or pointer.
3. **`ty_val` is generalised to `ty_fval`**, so parents own fancy bytes and structs with `PCell`
   fields work in places.
4. **A PCell in transit** is represented as `untethered g v`: the content value travels as the
   root `Value`, and the identity as the ghost group.
5. **`borrow_mut`**, i.e. sub-position writes through `&mut T` into a cell, is supported from
   the start.
6. **Mixed-size atomics on cells** are ignored for now.

## 7. Refinement: what `represents` depends on

**The registry has two parts:**
- **Static** (persistent, fixed at creation): `g ↦ (m_g, cs_g)`.
- **Dynamic:** `fv_g`, each group's current fancy value.

**`represents_R m bs fv` takes only the static part R.** At an `FVCell g'` position it checks:
- that `m_{g'}` equals the sub-mty at that position (alignment requirement A);
- that `cs_{g'}` are exactly the cells that the enclosing group's chains pass through at those
  bytes.

It says *nothing* about those bytes themselves. They are constrained by `g'`'s own invariant.

**Consequences:**
- **Each group's invariant constrains only its own non-cell bytes.** Nothing is duplicated
  across nesting levels.
- **Writes stay local.** A write into an inner cell updates only `fv_{g'}` and re-proves
  `g'`'s invariant. The `represents` facts of enclosing groups are unaffected.
- **The `WSt` exemption composes.** An inner write in flight marks bytes that also belong to
  every enclosing group, so those groups are exempt as well.

**Compositionality** is therefore a statement about the whole registry:

    (∀ g, at rest g → represents_R m_g (bytes g) fv_g)  →  at rest g  →
    decode m_g (bytes g) = Some ⌊fv_g⌋_ρ

Here `at rest g` means "no byte of `g` is in `WSt`", and `⌊·⌋_ρ` is erasure using the dynamic
values `ρ g := fv_g`. Erasure is defined recursively:

    ⌊FVCell g⌋_ρ = ⌊ρ g⌋_ρ    (well-founded, since nesting is finite)

On all other constructors erasure is structural. In the Coq code it would be a named function
such as `fval_erase`.

## 8. Clarification: the value `v` in `pcell_untether`

`v = ⌊fv_g⌋_ρ`: take `g`'s fancy value from the dynamic registry and replace each nested
`FVCell g'` with `fv_{g'}`, recursively, until the value is concrete.

- **Why the bytes decode to it.** Untethering requires exclusive ownership of the location chains,
  so no write is in flight and `g` is at rest. The compositionality lemma (§7) then gives
  `decode m_g bs = Some ⌊fv_g⌋_ρ`.
- **What the mover knows.** The mover does not hold `g ↦fv fv_g`, so in the lemma `v` is
  existential. The equation `v = ⌊fv_g⌋_ρ` is kept by the invariant, recorded in
  `untethered g v`.
- **Why it stays valid in transit.** Every write to `g`, or to any nested `g'`, needs a guard of a
  chain that starts at a location (`inl l`). While `g` is untethered, its chains (and the nested
  cells reached through them) sit in untethered rows (`inr u`), so nobody can write to them.
  Hence `fv_g` and all nested `fv_{g'}` are frozen, and `⌊fv_g⌋_ρ = v` holds throughout.
- **Retether.** The new bytes `bs'` only need `decode m_g bs' = Some v`; they may differ from `bs`
  (e.g. `encode m_g v` turns padding into `Uninit`). Decoding is field-wise (alignment requirement
  A), so at each nested cell's position the sub-range of `bs'` decodes to `⌊fv_{g'}⌋_ρ`. Every
  group's invariant (§7) therefore holds again for the new bytes.
