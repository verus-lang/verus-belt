# PCell on the byte memory model: multi-byte cells

Status: steps 1–3 implemented (2026-10-30), branch `memory-model`; see §9 Outcome. §10 step 1
done (2026-10-31); see §11. §10 steps 2 and 3 done; see §12 and §13. §10 step 4 done; see §14.
§10 step 5 done; see §15 and §16.
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

## 9. Outcome (2026-10-30)

Plan steps 1–3 are done and merged into `memory-model`. Step 4 was not attempted as designed:
it is a redesign of the byte typing layer, not a port (see "Step 4" below). Step 5 is blocked
on step 4. No `Admitted`; no new axioms (the tests are closed under the global context).

### Step 1: byte cell map

- `util/cellmap.v` gains a full-authority RA, **`fcmap`**. Its authority is the whole full map
  `𝛼`; its fragments are edges (`fpt`) and untethered rows (`funt`). It has update lemmas for
  alloc, delete, write at the end of a row, untether, retether, and insert/delete of a front
  cell, all over the unchanged `big_inv`.
- The byte region is `fcmap` at `V = bval = lock_state * abyte`, with `bheap` / `bpt` / `bunt`.
  `l ↦b bs` lost its fraction (the users in `typing/` were adjusted).
- The guarded-read bank of stage 4 is kept. Its entries now carry a *witness*: the edges of the
  read range, together with `cells_wit` (either all bytes, or all byte-cells of one group
  whose permission the reader has).
- **Deviation.** `non_atomic_cell_map` was not instantiated:
  - its write bank owns cell contents word by word;
  - its points-to are fractional.

  The new RA plus the existing bank was simpler.

### Step 2: groups and fancy values

- **`lang/fvalue.v`:**
  - `FValue`;
  - erasure as an inductive relation `fval_erase ρ fv v`;
  - `represents_R` as the inductive `frepr R m fbs fv`, with alignment requirement A built in;
  - compositionality: `frepr_decode` (one level) and `registry_decode` (whole registry);
  - `fv_upd` / `frepr_upd`, for future sub-position writes.
- **`lang/heap.v`:**
  - static registry `greg g m cs` (persistent);
  - dynamic registry `gdyn g fv` (the permission, exclusive);
  - `gnocell g` (persistent: the group's value never has cells);
  - `gcontents` (D3), and the invariants `cells_wf` / `cells_live`;
  - `cells_decode`: D3 plus compositionality gives `decode m_g (final bytes) = Some ⌊fv_g⌋_ρ`.
- **Deviations:**
  - The byte context owns the contents edges of all live groups, so the permission is only
    `gdyn g fv`.
  - D3 is unconditional: contents bytes change only at a write's commit, and their lock
    states mirror the cell-write bank `CW`. So the `WSt` exemption is not needed.
  - Groups need `0 < mty_size m`.

### Step 3: D5 lemmas and WP-level tests

**Context lemmas (`heap.v`):**
- `bytes_ctx_pcell_create`, `bytes_ctx_pcell_destroy`.
- `bytes_ctx_pcell_untether`, which gives `l ↦b bs`, `decode m bs = Some v` and
  `untethered g m cs bs`.
- `bytes_ctx_pcell_retether`, which takes `bs'` with `decode m bs' = decode m bs`, and
  `bs' = bs ∨ gnocell g`.
- `bytes_ctx_untethered_val`, `bytes_ctx_untethered_set`.
- `bytes_ctx_cell_lookup`, `bytes_ctx_cell_read_begin_guarded`.
- `bytes_ctx_cell_write_begin` / `_end`, the two phases through the bank of cell writes `CW`.

**WP rules (`lifting.v`):**
- `wp_bytes_ctx_pre`, and the `_post` variants of the load, store and memcopy rules (context
  updates after the last step);
- `wp_pcell_create(_plain)`, `wp_pcell_destroy(_plain)`;
- `wp_pcell_load_na/_sc` and `wp_pcell_store_na/_sc`, with the location side owned;
- `wp_pcell_load_na_guarded/_sc_guarded` and `wp_pcell_store_na_guarded/_sc_guarded`, with the
  location side only guarded;
- `wp_pcell_memcopy` (moving a cell).

**Tests (`lang/pcell_tests.v`, all closed under the global context):**
- `test_pcell_read`, `test_pcell_lifecycle` (create, write, move by `MemCopy`, destroy, load);
- `test_pcell_atomic`;
- `test_pcell_read_guarded`, `test_pcell_write_guarded`, `test_pcell_atomic_guarded`;
- `test_pcell_typed_move` (untether, `Load`, `Store`, retether), via `wp_pcell_move`;
- `test_pcell_nested`: create a `PCell<PCell<i32>>` over an existing cell, move it, destroy the
  outer cell, and read through the inner one.

**Deviations and limits:**
- **Untether/retether are context updates, not free-standing fupds.** They are used through
  `wp_bytes_ctx_pre` and the `_post` rules.
- **`untethered g m cs bs` records the bytes, not `v`.** `v` is recovered by decoding.
- **Retether with changed bytes needs `gnocell g`.** When a group embeds cells, the bytes of
  the embedded groups are those groups' own contents and can't be rewritten by the mover. Such
  a group can only be moved verbatim (`MemCopy`), and the nested test does this.
- **Reads and writes through a cell are whole-value, at the group's mty.** Writes also need a
  group without cells: the new fancy value is `fv_lift v`.
  - Sub-position writes (what `borrow_mut` needs for a field of the content) are not done.
  - `CW` keys already carry an offset and length, and `frepr_upd` is proved; the context
    lemma is what's missing.
- **Accesses through an inner cell work only while its byte-cells head their rows**, i.e.
  once the outer cell is destroyed.
- **Reads report the value only for groups without cells:** `fv_cells fv = [] → fv = fv_lift v`.
- **No CAS.** The language has no byte-level CAS construct.
- **Exclusive accesses untether the group for the duration of the access.** Guarded accesses
  use the two banks.
- **`wp_pcell_move` (typed move) takes `∀ bs v, decode m bs = Some v → val_wf m v` as a
  hypothesis.** There is no general lemma saying that decoded values are well-formed.

### Step 4: not done, and why

1. **`pcellₛ n` doesn't know its content type.** Its syntactic mty is an opaque `n`-byte
   `MTuple [] n`, and `~~(pcellₛ n) = list positive` (one legacy cell id per word).
   - D6 needs `ty_mty (pcell_ty) = m`, the content mty, and a fancy value `FVCell g` (one
     group id).
   - So `pcellₛ` must change to carry the content mty, and its semantic type must become a
     group id. That touches `prophecy/syn_type.v` (decidable equality, `syn_mty` / `syn_val`,
     layout lemmas) and every user of `pcellₛ`.
2. **"Parents own fancy bytes" replaces `bytes_own` everywhere.**
   - Today `bytes_own` is `∃ bs, l ↦b bs ∗ ⌜ty_bytes ty x bs⌝`. It would become fancy-byte
     ownership with `frepr` and `ty_fval`.
   - Its users span the byte typing layer: `own_bytes`, `shr_bytes`, `uniq_bytes(_util)`,
     `ltype`, `place_*`, `subtype`, about 5000 lines.
   - `&shrb` / `&uniqb` into a cell's contents need guarded access to cell contents, not to
     location bytes. So their sharing and borrowing constructions change too.
3. **`typing/pcell.v` is stated over the legacy word types.** Its rules (`from_own`, `to_own`,
   `borrow`, `borrow_mut`, atomics) use `own_ptr`, `shr_bor` and `uniq_bor`. Porting means
   re-proving them over `bown` / `&shrb` / `&uniqb` with groups, after 1 and 2.
   `pcell_example`, `ra` and `protocol` follow.

These need design decisions, so step 4 is not a mechanical port and is left for a separate
plan. The open decisions are:
- the representation of `~~pcellₛ` and of the content type;
- how `ty_fval` threads through the sharing and uniq-borrow predicates;
- whether to stage it through a byte-only `pcell_ty` first.

### What remains for step 5

All of it. `pcell.v` and its examples still run on the legacy word layer, so `ty_phys`, `Word`
bytes, the legacy `Read`/`Write`/`CAS`, `phys_rel` and the second ghost region can't be deleted
yet.

## 10. Plan after steps 1–3 (approved 2026-10-31)

**User decision on the syntactic type:** `pcell` is parameterised by its content mty, and the
group id is part of its syntactic type's value. That is, `pcellₛ m` has `~~(pcellₛ m) = group_id`,
`syn_mty = m`, `syn_val = None` and `syn_fval g = FVCell g`. It is added as a new constructor
next to the legacy `pcellₛ n`; the legacy one is deleted in stage 5.

**Order** (each step is a separate merge):
1. **Close the step-3 deviations at the lemma level** (no typing changes):
   - writes through cells at a sub-position (the basis for `borrow_mut`);
   - access to an inner cell without destroying the outer cell;
   - typed moves of groups that contain cells;
   - a general lemma that decoding gives a well-formed value (`decode_value ⇒ val_wf`);
   - a byte-level CAS.
2. **The new syntactic type `pcellₛ m`**, as above.
3. **A `ty_fval` field** in the `type` record, equal to `lift ∘ ty_val` for every type without
   cells.
4. **Parents own fancy bytes.** Generalise `bytes_own` to
   `∃ fbs, l ↦b[^chains] fbs ∗ ⌜represents_R (ty_mty ty) fbs (ty_fval x)⌝`, with a lemma that
   for types without cells this reduces to today's form. This includes shared and unique
   borrows of cell contents.
5. **PCell types and rules on bytes:**
   - the types `pcell_ty m` and `cell_points_to_ty`;
   - the rules `from_own`, `to_own`, `borrow`, `borrow_mut`, the atomics, and the move rule;
   - ports of `pcell_example`, `ra` and `protocol`.
6. **Stage 5:** delete the legacy layer.

## 11. Outcome: §10 step 1 (2026-10-31)

All five items are done at the lemma level, with no typing-layer changes. No `Admitted`; no
new axioms (all tests are closed under the global context). The cell lemmas moved from
`heap.v` to a new file, `lang/heap_cells.v`.

### Changes to the invariants (`heap.v`)

- **Nestings.** A new persistent registry `NS` of nestings `(g0, g, o)`, with fragments
  `gnest g0 g o` ("`g` is a cell at the offset `o` of the fancy value of `g0`") and their
  transitive closure `gpath g0 g o` (with `gpath_refl`, `gpath_nest`). D3 (`gc_pure`) now
  also says that while `g0` is live, its contents at `o` are the byte-cells of `g`. This
  holds forever because writes through `g0` only replace plain sub-values.
- **Rows of writes in flight.** `cells_live` now says that the rows of a group with a write
  in flight *contain* its byte-cells (`row_has`), not that they start with them.
- **The bank of cell writes.** An entry guards the location side of a *root* `g0` in which
  the written group sits (at an offset), not the group's own location side.
- **Read witnesses** (`cells_wit`) are either all plain bytes, or a plain sub-value of a
  group `g` (whose permission the reader has) nested in a root `g0` whose byte-cells the
  edges of the range point to.
- `cells_wf` also records that the mtys of groups are well formed.

### Items

1. **Sub-position writes and reads through cells.** The access target is a plain sub-value
   (`fv_sub m fv o' m' fvs` with `fv_cells fvs = []`) of a group `g`, which may be nested
   (`gpath g0 g o`) in a root `g0` whose location side is guarded. The access is at
   `l0 +ₗ (o + o')`.
   - Context lemmas: `bytes_ctx_cell_write_begin` / `_end` (the end takes any bytes `bs'`
     with `decode_value m' bs' = Some v`, and the new fancy value `fvn` with
     `fv_upd m fv o' m' (fv_lift v) fvn`; it re-proves D3 with `frepr_upd`),
     `cells_ctx_read_sub`, `bytes_ctx_cell_lookup_sub` and
     `bytes_ctx_cell_read_begin_guarded`.
   - WP rules: `wp_pcell_store_na_sub`, `wp_pcell_store_sc_sub`,
     `wp_pcell_memcopy_into_sub`, `wp_pcell_load_na_sub` and `wp_pcell_load_sc_sub`.
   - The whole-value guarded rules (`wp_pcell_load_*_guarded` and `wp_pcell_store_*_guarded`)
     are now corollaries. They need `fv_cells fv = []` instead of `gnocell g`.
2. **Access to an inner cell while the outer one is live.** `bytes_ctx_gnest` (and the WP
   rule `wp_pcell_gnest`) record a nesting from `gdyn g0 fv0` and
   `fv_sub m0 fv0 o m (FVCell g)`. After that the rules of item 1 apply to `g` with root
   `g0`. D3 of the outer group says nothing about the inner bytes, so it is preserved.
3. **Typed moves of groups that embed cells.**
   - `bytes_ctx_untethered_rewrite` rewrites a group in transit with any bytes that decode
     to the same value. It also rewrites the plain bytes of the embedded groups: each byte is
     the final value of an untethered row, and the edge is owned by the contents of the
     innermost group at that position.
   - D3 is re-proved for every group by well-founded induction from the root down
     (`rewrite_pure`, using `frepr_rebytes`).
   - `bytes_ctx_pcell_retether_gen` combines this with retethering; it needs no `gnocell`.
   - `wp_pcell_move` (in `pcell_tests.v`) is the typed move `Store m (Load m)` for any
     group. Nestings stay valid across moves.
4. **`decode_value_wf`** (`minirust.v`, `decode_int` now checks the range of the type).
   `wp_pcell_move` no longer takes a well-formedness hypothesis.
5. **Typed compare-and-exchange `MCAS m l e1 e2`** (`lang.v`, with races in `races.v`;
   `safe_nonracing` and adequacy hold).
   - The class of mtys compared: any `m`. The comparison is equality of the decoded
     `Value`s, so padding is not compared and pointers compare as abstract locations. A
     failure is a sequentially consistent read, and a success an SC write.
   - WP rules: `wp_mcas` on `l ↦b bs`, and `wp_pcell_mcas_sub` through a cell (the
     sub-value's own mty, so no mixed-size accesses). Both report success or failure.

### Tests (`lang/pcell_tests.v`, all closed under the global context)

The earlier tests are ported. New tests:
- `test_pcell_sub_write`: write the first field of a `PCell<(i32, PCell<i32>)>` whose second
  field is a cell, then read it;
- `test_pcell_inner_access`: write and read the inner cell, and read the outer field, with
  the outer cell live;
- `test_pcell_typed_move_nested`: a typed move of `PCell<(i32, PCell<i32>)>`, then a read
  through the inner cell at the new location;
- `test_mcas_int` (a success then a failure on plain bytes) and `test_pcell_mcas`;
- `test_pcell_memcopy_into`.

### Deviations and limits

- **Accesses through cells read or write only plain sub-values.** A guarded read of a
  whole group whose value has cells is no longer offered. It would race with writes to the
  embedded groups, whose permissions the reader does not have. Moves (untether) still handle
  any group.
- **Nestings must be recorded explicitly** (`bytes_ctx_gnest`) before accessing an inner
  cell through its root.
- **The generalised `wp_pcell_move` lives in `pcell_tests.v`** (it uses `wp_bind`), as
  before.

## 12. Outcome: §10 step 2 (2026-10-31)

The syntactic type of byte-level cells is added next to the legacy `pcellₛ n`. No `Admitted`;
no new axioms.

### Definitions (`prophecy/syn_type.v`)

- **The constructor is `pcellbₛ (m: mty)`** (`b` for the byte layer, like `bown` and `&shrb`).
  The legacy `pcellₛ n` stays until stage 5.
- `~~(pcellbₛ m) = positive`, the group id (groups are `positive`s in `lang/fvalue.v` and
  `lang/heap_cells.v`). The prophetic and abstracted interpretations are also `positive`;
  `vπ x π = x` and `ξl x = []`, as for the legacy cell ids.
- `syn_mty (pcellbₛ m) = if decide (mty_wf m) then m else zst_mty`; `syn_val = None`.
- The legacy layout is empty: `size_of (pcellbₛ m) = 0` and `syn_phys x = []`. The new cell
  never lives in the word layer.
- **`syn_fval : ~~𝔄 → option FValue`**, the fancy value:
  - `syn_fval (x: ~~(pcellbₛ m)) = Some (FVCell x)`;
  - structural on `prodₛ`, `xprodₛ` and `xsumₛ`, mirroring `syn_val`
    (`FVTuple [fv₀; fv₁]`, `FVTuple <$> mapM …`, `FVVariant i <$> …`);
  - `fv_lift <$> syn_val x` on every other type.

  It has the shape of `syn_val` (an `option`), so that values without a MiniRust
  representation (out-of-range integers, closures) stay `None`.
- **`syn_nocell : syn_type → bool`**: `false` on `pcellbₛ`, `&&`/`forallb` on products and
  sums, and `true` elsewhere. Cells under other constructors (e.g. `ghostₛ (pcellbₛ m)`) are
  zero-sized and not part of the MiniRust value, so they don't count.

### Lemmas

    Lemma syn_fval_nocell 𝔄 (x: ~~𝔄) : syn_nocell 𝔄 → syn_fval x = fv_lift <$> syn_val x.
    Lemma syn_abstract_fval_eq 𝔄 x x' :
      @syn_abstract 𝔄 x = @syn_abstract 𝔄 x' → @syn_fval 𝔄 x = @syn_fval 𝔄 x'.

(the second is the analogue of `syn_abstract_val_eq`, for the `Send` arguments), plus
`mapM_fmap_fv_lift`. The equality decider, the inhabitedness proofs, `syn_mty_wf`,
`syn_val_wf` and `syn_abstract_val_eq` cover the new constructor.

`lang/minirust.v` gains decidability of `mty_wf`: `fields_disjoint_cons`,
`fields_disjoint_dec`, the checker `mty_wfb` with `mty_wfb_correct`, and the instance
`mty_wf_dec` (all transparent, so `syn_mty (pcellbₛ m)` computes for a concrete `m`).

### Deviation

- **`syn_mty (pcellbₛ m)` is `m` only when `m` is well formed.** `syn_mty_wf` (every
  syntactic type has a well-formed mty, on which `ty_mty_wf` and the encode/decode round trip
  depend) would fail for an ill-formed `m`. The constructor can't carry a proof of
  `mty_wf m` without losing decidable equality, or proof irrelevance (an axiom). So
  ill-formed contents fall back to `zst_mty`. The pcell rules of step 5 will take
  `mty_wf m` as a side condition (decidable, so `by compute`/`done` for concrete `m`), and
  rewrite with `decide_True`.

## 13. Outcome: §10 step 3 (2026-10-31)

The `type` record (`typing/type.v`) gains the fancy value. No `Admitted`; no new axioms;
`bytes_own` is unchanged (that is step 4).

- **Fields:** `ty_fval : ~~𝔄 → option FValue` and `ty_fval_eq x : syn_fval x = ty_fval x`.
  - The shape is that of `ty_val` (`option`): a value with no MiniRust representation
    (a closure, an out-of-range integer) has no fancy value either.
  - Like `ty_mty` and `ty_val`, it is determined by the syntactic type. So `ty_fval` is
    `syn_fval`, and the step-2 lemma carries over.
- **Constructors.** Every type definition already fills the byte-layer fields with the
  one-liner `ty_mty := syn_mty _; ty_val := syn_val; ty_mty_eq := eq_refl;
  ty_val_eq _ := eq_refl;`. Each of the 23 definitions now has one more line,
  `ty_fval := syn_fval; ty_fval_eq _ := eq_refl;`. A smart constructor was not needed: this
  default is the only possible value up to `ty_fval_eq`, and the existing definitions don't
  go through a common builder.
- **Lemmas** (`ty_mty_lemmas`):

      Lemma ty_fval_same {𝔄} (ty ty': type 𝔄) x : ty.(ty_fval) x = ty'.(ty_fval) x.
      Lemma ty_fval_nocell {𝔄} (ty: type 𝔄) x :
        syn_nocell 𝔄 → ty.(ty_fval) x = fv_lift <$> ty.(ty_val) x.
      Lemma ty_fval_nocell_cells {𝔄} (ty: type 𝔄) x fv :
        syn_nocell 𝔄 → ty.(ty_fval) x = Some fv → fv_cells fv = [].

- The OFE structure doesn't change: `ty_fval` is not part of `type_unpack`, just as
  `ty_mty` and `ty_val` aren't.

## 14. Outcome: §10 step 4 (2026-10-31)

Parents own fancy bytes. `bytes_own`, and with it the bodies of `own_bytes`, `&shrb` and the
leaves of `&uniqb` and of the byte places (`cbytes`), now own fancy bytes. Both halves of the
step (boxes, products and sums; the borrows) are in one merge: the borrow bodies are defined
over `bytes_own`, so they needed no separate generalisation. No `Admitted`; no new axioms. No
example needed a change.

### Definitions

- **`ty_fbytes R ty x fbs`** (`typing/type.v`), next to `ty_bytes`:

      length fbs = ty_bsize ty ∧ ∃ fv, ty_fval x = Some fv ∧ frepr R (ty_mty ty) fbs fv

  `fbs : list (positive + abyte)` (byte-cells or bytes), `R` a static registry.
  `syn_fbytes R x fbs` (`typing/bytes_layout.v`) is the same over the syntactic type
  (`ty_fbytes_syn`).
  - **The length is explicit.** `frepr` gives it only for a well-formed registry
    (`frepr_length` needs `reg_wf R`), and an `R` owned as fragments is not known to be well
    formed without the byte context. Combining the fancy bytes of two fields needs the
    lengths.
- **`bytes_own`** (`typing/own_bytes.v`), sealed:

      bytes_own ty l x := ∃ R fbs, heap_mapsto_fbytes l fbs ∗ ⌜ty_fbytes R ty x fbs⌝ ∗ greg_map R
      greg_map R := [∗ map] g ↦ e ∈ R, greg g e.1 e.2

  - **The registry.** Per §7, `frepr` depends only on the static registry, so `bytes_own` owns
    the (persistent) fragments `greg` of the groups that it uses. The existential `R` is
    local to each owner. Two fragments agree where they overlap (`greg_agree`), so their union
    is a fragment containing both (`greg_map_union`); this is what combining needs.
  - **Equivalently** (`bytes_own_brepr`), it is `heap_mapsto_fbytes l fbs` with
    `brepr (ty_mty ty) fbs fv`, the form of the lemmas of `lang/heap_cells.v`
    (`bytes_ctx_pcell_create` etc.).
  - **Why sealed.** Unfolded, the unifier expands it while trying instances. In
    `place_pshr.v`, the `Persistent` search for `guard ∗ ty_shr` tried `pctx_sguards` and
    `shr_view`, and did not finish.
- **`NoCell 𝔄`** (`typing/type.v`): `syn_nocell 𝔄` as a class. It is solved by
  `Hint Extern … exact I` whenever the head constructor of `𝔄` is known, and by
  `prod_nocell` for products of such types.

### The reduction lemmas

    Lemma bytes_own_of_bytes ty l x bs : ty_bytes ty x bs → l ↦b bs -∗ bytes_own ty l x.
    Lemma bytes_own_to_bytes ty l x v :
      ty.(ty_val) x = Some v → bytes_own ty l x -∗ ∃ bs, l ↦b bs ∗ ⌜ty_bytes ty x bs⌝.
    Lemma bytes_own_nocell `{!NoCell 𝔄} ty l x :
      bytes_own ty l x ⊣⊢ ∃ bs, l ↦b bs ∗ ⌜ty_bytes ty x bs⌝.

The first two hold for every type. The second rests on `syn_fval_val`
(`syn_val x = Some v → syn_fval x = Some (fv_lift v)`): a value with a MiniRust value has no
cells. The pure versions are `syn_fbytes_bytes`, `syn_fbytes_val` and `syn_fbytes_nocell`.
Derived forms: `bytes_own_nocell_bytes`, `bytes_own_val` (`is_Some (ty_val x)`),
`bytes_own_view` and `bytes_own_view_nocell` (the `□ (P -∗ ∃ bs, …)` view that
`wp_load_na_guarded_gen` and `wp_memcopy_guarded_gen` take), `cbytes_nocell` and
`shr_bytes_own_nocell`.

**Dropping cells.** Any fancy bytes can be turned into plain bytes by dropping their cells
(dropping a `PCell` is a no-op). This needs the byte context, so it is a WP-level rule:
- `bytes_ctx_fbytes_forget` (`heap_cells.v`) untethers every location edge to a byte-cell
  (`bheap_untether_fbytes`) and leaks the untethered rows. The final bytes are not in a
  write: the edges are owned, so no cell write is in flight there (`cwentries_disj_fbytes`,
  `row_end_rst`).
- `wp_fbytes_forget` (`lifting.v`) and `wp_bytes_own_forget` (`own_bytes.v`) are the WP
  versions, before any non-value expression.

They are used wherever a value of a *generic* type is overwritten or freed: the `Store` rules
(`wp_own_bytes_store`, `type_store_own_bytes_instr`, `type_write_oplace_instr`, the two
`type_write_*place_deep_instr`), the old contents of the target box of the `MemCopy` rules,
and `wp_own_bytes_delete`. `wp_delete_fbytes` (`place_resolve.v`) frees fancy bytes. The
memory of a dropped place (`lty_omem`) is now `mem_cell` (fancy bytes of a given length) at
its leaves, instead of `pad_cell`.

### Splitting along the layout

- **Pairs.** `bytes_own_pair` (generic over the type of the pair, as `cbytes_pair`):

      bytes_own ty l (x1, x2) ⊣⊢ bytes_own ty1 l x1 ∗ bytes_own ty2 (l +ₗ ty_bsize ty1) x2

  from `syn_fbytes_pair` and `frepr_seq_tuple_cons`. A `seq_tuple` has no padding, so its
  representations are those of its fields (`frepr_seq_tuple`). `cbytes_pair` and the field
  projections of `&shrb` (`type_shr_bytes_fst/snd_instr`) are corollaries; the
  `place_shr.v` copy of `bytes_own_pair` is gone.
- **n-ary products.** `syn_fbytes_xprod_cons` gives `cbytes_xprod_cons`.
- **Sums.** `cbytes_sum` keeps its statement: the tag (`tag_cell`) and the padding
  (`pad_cell`) stay plain bytes (`frepr_enum` requires them plain), and only the payload is
  fancy (`syn_fbytes_sum`).
- **Supporting lemmas.** `frepr_tuple_iff`, `frepr_enum_iff`, `frepr_seq_tuple(_nil)`,
  `layout_fields_shift`, `in_field_layout`, `plain_fbytes`.
- **Pointers.** The pointer lemmas (`cbytes_at_loc`, `cbytes_at_cloc`, `cbytes_uniq_bor`) are
  the reduction lemma for pointer types.

### Subtyping

`btype_incl` now requires the equivalence of the fancy representations
(`∀ x R fbs, ty_fbytes R ty x fbs ↔ ty_fbytes R ty' (f x) fbs`). For `f = idₛ` it holds
by `ty_fbytes_same`; for boxes and references it holds by the reduction lemma.
`bytes_own_iff` transports `bytes_own` along such an equivalence.

### Sanity lemma for step 5

    Lemma bytes_own_pcellb {m} (ty: type (pcellbₛ m)) l (g: ~~(pcellbₛ m)) :
      mty_wf m → bytes_own ty l g ⊣⊢ ∃ cs, loc_side l g m cs ∗ ⌜length cs = mty_size m⌝.

For any type of syntactic type `pcellbₛ m`, the byte ownership of the group `g` at `l` is
exactly the location side of `g` (`frepr_cell_inv`). The length is the one that
`bytes_ctx_greg_length` gives. Together with `bytes_own_pair`, the `own` of a tuple with a
cell field splits into the plain bytes of the other fields and the cell's location side.

### Changes to existing rules (deviation)

The rules that `Load` or `MemCopy` the value of a leaf of a *generic* type got an instance
argument `` `{!NoCell 𝔅} `` for the type of the leaf. Before, owning the bytes of a value
implied that it has a MiniRust value; with cells it does not. `Copy` doesn't imply `NoCell`
either: `base`, `simple_type` and `mod_ty` are `Copy` at any syntactic type, including
`pcellbₛ m`. A `Load` of a value with cells is the typed move of step 5 (untether, `Load`,
`Store`, retether), so these rules can't simply be generalised.

The rules are:
- `type_read_oplace_instr`, `type_move_oplace_instr`;
- `type_read_oplace_shr_instr`, `type_read_{v,o}place_deep_instr`,
  `type_read_vplace_pshr_root_instr`, `type_read_{v,o}place_pshr_instr`;
- `type_read_oplace_res(_leaf,_shrblk)_instr`;
- `type_load_own_bytes_copy_instr`, `type_load_shr_bytes_copy_instr`;
- the `MemCopy` rules (`type_memcpy_{v,o}place_deep_instr`,
  `type_memcpy_copy_from_*_instr`);
- the helpers `shr_view_copy` and `wp_load_shr_view`.

Every caller in the examples has a concrete type, so the instance is found automatically
and no example changed. The `Store`, free and drop rules stay fully generic, by dropping the
old cells.

### Size of the change

19 files, about 840 lines added and 175 removed:
- new lemmas: `bytes_layout.v` (+280), `own_bytes.v` (+220), `heap_cells.v` (+100);
- the ports, typically one or two lines per proof: a destruct of plain bytes becomes
  `bytes_own_nocell_bytes` or `wp_bytes_own_forget`, and `iExists bs; iFrame` becomes
  `bytes_own_of_bytes`.

### Limits, for step 5

- **No pcell types or rules** (by the plan).
- **Borrows into cell contents.** `&shrb` and `&uniqb` *of values that contain cells* work:
  their bodies are `bytes_own`/`cbytes`, i.e. fancy bytes at locations. A borrow *of a
  cell's contents* (`PCell::borrow` / `borrow_mut`) points to bytes that are reached through
  the group's chains (`gdyn`, `bytes_ctx_cell_*`), not through location edges. Its body is
  part of the pcell types of step 5.
- **Moves of values with cells.** Generic moves and copies of values with cells (the
  `NoCell` rules above) need the untether/retether machinery, also in step 5.
- **`NoCell` instances.** `NoCell` has instances only for products; `Π!`/`Σ!` of type
  variables would need a `forallb` instance.

## 15. Outcome: §10 step 5 (2026-10-31)

The `PCell` types and rules on bytes, the byte-layer `pcell_example` and the typing rules of
`ra.v` on bytes. No `Admitted`; no new axioms. Files: `typing/pcell_bytes.v` (types, create,
destroy, move, atomics), `typing/pcell_bytes_borrow.v` (borrows of the contents),
`typing/ra_bytes.v`, `typing/examples/pcell_example_bytes.v`. The legacy files are
unchanged.

### Names

| byte layer | legacy |
|---|---|
| `pcellb_ty m : type (pcellbₛ m)` | `pcell_ty n` |
| `bcell_points_to_ty ty : type (trackedₛ (pcellbₛ (syn_mty 𝔄) * 𝔄))` | `cell_points_to_ty ty` |
| `bcell_shr_ty κ ty`, `bcell_uniq_ty κ ty` (borrows of the contents) | `shr_bor κ ty`, `&uniq{κ} ty` at `cloc_flat_insert l γs` |
| `PCellbNew`, `PCellbFromOwn`, `PCellbIntoInner`, `PCellbBorrow`, `PCellbBorrowMut` | `PCellFromOwn`, `PCell2Own`, `PCellBorrow`, `PCellMutBorrow` |
| `type_pcellb_*_instr`, `type_bcell_*_instr` | `typed_pcell_*` |
| `typed_rab_*` (`RAb_*:` notations) | `typed_ra_*` (`RA_*:`) |

### Types

- **`pcellb_ty m`**: value the group `g`; trivial ownership; zero legacy size. Its
  location side is owned by the parent, as its fancy bytes:
  `bytes_own_pcellb_ty : mty_wf m → bytes_own (pcellb_ty m) l g ⊣⊢ ∃ cs, loc_side l g m cs ∗ ⌜length cs = mty_size m⌝`.
  A cell has no MiniRust value, so it lives only in memory (boxes, references, fields).
- **`bcell_points_to_ty ty`**: a ghost value `(g, x)` (its MiniRust value is `VTuple []`),
  owning `bcell_own ty g x := ∃ fv cs, ⌜ty_fval x = Some fv⌝ ∗ greg g (ty_mty ty) cs ∗ gdyn g fv`
  and `▷ ty_gho_own x`. The fancy value may contain the groups of nested cells. The sharing
  predicate is structural (a guard of `bcell_own` and the sharing predicate of `ty`), as the
  legacy one; `Send`/`Sync`/`ResOwn` are inherited.
- The rules use `pcellb_ty ty.(ty_mty)`: the side condition `mty_wf m` of §12 is then
  `ty_mty_wf`.

### Rules (`typing/pcell_bytes.v`)

- `type_pcellb_new_instr` (`0 < ty_bsize ty`): `p ◁ᵥ own_bytes n ty` becomes
  `p ◁ᵥ own_bytes n (pcellb_ty ty.(ty_mty))`, and the result is the permission
  `v ◁ᵥ bcell_points_to_ty ty`; post `∀ g, post -[(l, g); (g, x)]`.
- `type_pcellb_from_own_instr`: the legacy form, the box of the pair
  `own_bytes n (pcellb_ty _ * bcell_points_to_ty ty)` with value `(l, (g, (g, x)))`.
- `type_pcellb_into_inner_instr`: `own_bytes n (pcellb_ty _)` and the permission give
  `own_bytes n ty`; VC `g = g'`.
- Moves: `type_pcellb_memcpy_instr` (`MemCopy` of the cell into a box `own_bytes n (↯ m)`) and
  `type_pcellb_move_instr` (typed move `Store m (Load m)`); the source box becomes `↯`. Any
  contents (with nested cells) can be moved.
- Atomics, at the content's mty, for `NoCell 𝔄`:
  `type_pcellb_load_sc_instr` (`&shrb` of the cell and of the permission, `Copy ty`),
  `type_pcellb_store_sc_instr` and `type_pcellb_mcas_instr` (`&shrb` of the cell, `&uniqb`
  of the permission, which they resolve, as the legacy rules). The MCAS post branches on
  `bool_decide (ty_val x = ty_val y1)` (the MiniRust comparison), and the result is
  `v ◁ᵥ bool_ty`.

### Borrows of the contents (`typing/pcell_bytes_borrow.v`)

The contents of a cell are reached through the byte-cells of its group, not through
location edges, so `&shrb`/`&uniqb` of `ty` (whose bodies are `bytes_own`) cannot be the
result of `borrow`/`borrow_mut`. A borrow of the contents is a borrow **of the permission**,
pinned to the location of the cell:

    pinned_ty ty Φ          (* ownership, persistent and sharing predicates ∗ Φ x g *)
    bcell_loc κ m l g n := ∃ cs, greg g m cs ∗ (@[κ] &&{↑NllftG; n+1}&&> loc_side l g m cs)
    bcell_shr_ty κ ty  := pinned_ty (&shrb{κ} (bcell_points_to_ty ty)) (λ x n, bcell_loc κ _ x.1.1 x.2.1 n)
    bcell_uniq_ty κ ty := pinned_ty (&uniqb{κ} (bcell_points_to_ty ty)) (bcell_uniq_loc κ _)

The pointer of the reference is the location of the cell (the permission is zero-sized, so
its bytes are at any location, `bytes_own_zst_loc`). The values are those of the borrows of
the permission, `(l, (g, x))` and `(l, (g, x), ξ, d, g', idx)`: the prophecy of a
`bcell_uniq_ty` is that of the borrowed permission (resolution: `bcell_uniq_resolve`).

- `type_pcellb_borrow_instr`: `&shrb{κ} (pcellb_ty _)` at `(l, g)` and
  `&shrb{κ} (bcell_points_to_ty ty)` at `(_, (g', x))` give `bcell_shr_ty κ ty` at
  `(l, (g, x))`; VC `g = g'`.
- `type_bcell_shr_load_instr` (`NoCell`, `Copy`): a non-atomic guarded `Load` of the contents.
- `type_pcellb_borrow_mut_instr`: `&shrb{κ} (pcellb_ty _)` and `&uniqb{κ} (bcell_points_to_ty ty)`
  give `bcell_uniq_ty κ ty` at `((l.1, []), (g, x), ξ, …)`; VC `g = g'`.
- `type_bcell_uniq_store_instr` (`NoCell`): a non-atomic `Store` of the whole contents through
  the cell (`wp_pcell_store_na_guarded`, i.e. the sub-position machinery at offset 0); the
  borrow stays, with the new contents.

**Combining guards.** A guarded access needs one guard of `loc_side ∗ gdyn`, but the two
shared references give two guards (by `@[κ]`). Two guards by the same token give a guard of
the conjunction (`guards_and_point`, the target must be a point prop); the conjunction of
`loc_side` (edges of the byte region) and `gdyn` is their separating conjunction because
they live in different ghost cells. For this, `heapGS` has a new field
`heap_bytes_gdyn_ne : heap_bytes_name ≠ heap_gdyn_name` (allocated fresh in `adequacy.v`),
and `lang/heap_cells.v` has `own_and_ne` (`own γ1 a ∧ own γ2 b ⊢ own γ1 a ∗ own γ2 b` for
`γ1 ≠ γ2`, proved in the model), `loc_side_and_gdyn` and the point-prop lemmas.

### Example (`typing/examples/pcell_example_bytes.v`)

`pcell_example_b_type`: allocate a box, store `17`, `PCellbFromOwn`, share the pair at `κ`,
copy the shared reference (`copy_val_tctx_incl`, new in `value_ctx.v`), project the fields
(`type_shr_bytes_fst/snd_instr`), `PCellbBorrow`, load, end `κ`, drop the pair, return the
value; the specification is `post 17`. Instead of calling the legacy `assert` (a legacy
`fn`), the body returns the value. Its axioms are those of the other examples. It takes
about 35 s.

### `ra.v` on bytes (`typing/ra_bytes.v`)

The definitions of `ra.v` (`VerusRA`, `ra_ty`, `ra_inv`, `ra_alloc`, `ra_validate`,
`ra_update…`) are layer-independent and are reused; `proph_protocol.v` depends only on them,
so it needs no port. The typing rules take ghost values as MiniRust values (`◁ᵥ ra_ty`,
`◁ᵥ ghost_ty ty`) instead of boxes of size 0, and shared references as `&shrb{κ} ra_ty`.
A ghost operation is `GhostOp := Skip ;; MkTuple []`; the operations that return a shared
reference are `GhostRet [p1]` (the pointer of the first argument: a zero-sized referent is
at any location, `shr_bytes_own_zst`). Ported: alloc, join, split (deviation: `self` keeps
the first part and the result is the second, instead of a box of the pair), unit, update,
update_nondeterministic, validate, join_shared_to_target, weaken, update_with_shr,
update_with_shr_non_det.

### Changes to existing files

- `lang/heap.v` (`heap_bytes_gdyn_ne`), `lang/adequacy.v`, `lang/heap_cells.v` (above).
- `typing/type.v`: `NoCellL` (lists) with instances for `[]`, `::`, and `NoCell` instances for
  `Π!` and `Σ!` (the §14 left-over).
- `typing/own_bytes.v`: zero-sized bytes (`bytes_own_zst_emp`, `bytes_own_zst_true`,
  `bytes_own_zst_loc`); `typing/shr_bytes.v`: `shr_bytes_own_zst`;
  `typing/value_ctx.v`: `copy_val_tctx_incl`.

### Limits

- **Whole-contents accesses only, for contents without cells** (`NoCell`). Field-wise
  accesses through `bcell_shr_ty`/`bcell_uniq_ty` (the sub-position rules exist at the WP
  level, `wp_pcell_*_sub`) and loads through `bcell_uniq_ty` are not provided; nor are
  places rooted at cell contents (the place machinery is on `bytes_own` leaves).
- **Generic moves and copies of values containing cells** (the `NoCell` rules of §14) are not
  generalised: the move rules above move a `pcellb_ty` box; a generic typed move of a
  value with several groups would need a multi-group untether/retether lemma.
- The atomic store/MCAS consume the unique borrow of the permission (as the legacy rules);
  the non-atomic store through `bcell_uniq_ty` keeps it.

## 16. Outcome: §10 step 5, `protocol.v` on bytes (2026-10-31)

`typing/protocol_bytes.v` has the typing rules of `protocol.v` on the byte layer, as
`ra_bytes.v` for `ra.v`: the definitions (`storable_ty`, `storage_resource_ty`) and the
storage-protocol lemmas (`proph_protocol.v`) are reused; ghost values are `◁ᵥ` values,
shared references `&shrb`, unique borrows `&uniqb`. No `Admitted`; no new axioms.

- Storable values: `storable_new_bytes`, `storable_into_inner_bytes`, `storable_borrow_bytes`
  (the last returns its argument after two steps, `GhostRetS`, to get the cumulative time
  receipt of the stored value, as `typed_instr_of_skip_linear`).
- Owned rules (`GhostOp`): `typed_spb_alloc`, `_join`, `_split`, `_exchange`, `_deposit`,
  `_withdraw`, `_update`, `_exchange_nondeterministic`.
- Shared rules: `typed_spb_guard`, `_join_shared_to_target`, `_weaken` (they return the
  pointer of their first argument, `GhostRet`), `_validate` (`GhostOp2`, a pair of ghost
  values), `_exchange_with_shr`, `_exchange_with_shr_nondeterministic`,
  `_validate_with_shr` (with `&uniqb`, which it gives up, as the legacy rule).
- **Deviation**: the rules whose legacy result is a box of a pair (split, exchange,
  withdraw, the non-deterministic exchanges) keep the first component in their first
  argument (`p1 ◁ᵥ storage_resource_ty`, with the new value) and return the second one.

