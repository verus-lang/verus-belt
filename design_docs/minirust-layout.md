# MiniRust layouts for structs and enums

Status: design only (2026-11-03, branch `memory-model` at `7304f5c`). No Coq changes yet.
Context: `design_docs/minirust-memory-model.md` (decision 8 there: "enums use a simple tag at
offset 0 for now"), `lang/minirust.v`, `lang/fvalue.v`, `prophecy/syn_type.v`,
`typing/bytes_layout.v`, `typing/ltype.v`, `typing/lpath.v`, `typing/own.v`,
`typing/value_ctx.v`, `typing/place_sum.v`, `typing/place_xprod.v`, `typing/product.v`,
`typing/uninit.v`.

There is no local copy of the MiniRust spec. The MiniRust facts below are from
`spec/lang/types.md`, `spec/lang/representation.md` and `spec/lang/operator.md` as
remembered. Check them against the current spec before implementing; the design does not
depend on the details.

## 1. Where we are, and what MiniRust has

### 1.1 Today

- `mty := MInt it | MBool | MPtr | MTuple (fields: list (nat * mty)) size |
  MEnum (variants: list mty) (tag: IntType) size`.
  - Tuples already have explicit field offsets and padding: `fields_disjoint`, fields in
    bounds, and `decode` reads each field from its slice and ignores the other bytes.
  - Enums have a tag of type `tag` at offset 0, and the payload of variant `i` at offset
    `int_size tag`.
- Sizes: `PTR_SIZE` is sealed, and `IntType` carries its size. There is no alignment at all.
- Syntactic layouts (`syn_mty`):
  - `prodₛ` and `Π!` use `seq_tuple`: fields one after the other, no padding, size
    `seq_size` = the sum of the field sizes;
  - `Σ!` uses `seq_enum`: a tag `enum_tag n` at 0, the payload right after it, and size
    `tag + max payload`.
- Many proofs use the sequential shape directly, not just the offset/size laws:
  - plain bytes: `syn_bytes_pair` (`bs = bs1 ++ bs2`), `syn_bytes_sum`
    (`bs = bt ++ bp ++ bq`);
  - fancy bytes: `frepr_seq_tuple_cons`, `syn_fbytes_pair/sum/xprod_cons`;
  - ownership: `gcont_seq_tuple_cons`, `bytes_own_pair`, `cbytes_pair`, `cbytes_sum`;
  - cells: `mcells_seq_tuple_cons`, `mcells_sum`;
  - values with cells: `val_cells_seq_tuple_cons` and the enum `val_cells`;
  - decoding: `decode_prod_cons`, `decode_assoc_l/r`, `decode_prod_unit_l/r`,
    `decode_pad_pair`;
  - sizes: `lty_size_prod` (`size (A*B) = size A + size B`);
  - place contexts: `pctx_off`, `pctx_loc` and `pctx_expr` use `PSnd ↦ +ₗ lty_size lt1`
    and `PSum ↦ +ₗ tag_size 𝔄l`; `prod_node` puts the second child at `l +ₗ sz1`;
    `sum_node`/`view_sum` have the tag at `l`, the payload at `l +ₗ tag_size`, and the
    padding after it;
  - reading a discriminant (`type_case_oplace`, `place_deep`, `place_pshr`) is
    `case: Load Na1Ord (MInt (sum_tag 𝔄l)) (pctx_expr K p)`, a typed load of the tag at
    offset 0;
  - isomorphisms that preserve bytes (`Isoₛ` has `syn_iso_bincl`): `prod_assocₛ`,
    `prod_left/right_idₛ`, `to/of_cons_prodₛ`, `uninit_splitₛ`. `xprod_ty` is defined as
    `mod_ty to_cons_prodₛ of_cons_prodₛ (ty * Π! tyl)`, and `place_xprod.v` unfolds
    `Π! (ty :: tyl)` by the cons iso;
  - examples hard-code offsets and sizes (about 28 `+ₗ #n` and 40 `Alloc #n`/`own_bytes n`
    in `typing/examples`, and `pair_ty_mty : … = MTuple [(0, i32); (4, i32)] 8`).

### 1.2 MiniRust

- `Layout`/`Size`/`Align`. Every type has a size and an alignment (a power of two), and the
  size is a multiple of the alignment.
- `Type::Tuple { fields: List<(Offset, Type)>, size, align }`. The offsets are chosen by
  the compiler (rustc reorders fields for the default repr). The bytes not covered by a
  field are padding: they are ignored by decode, and encode writes them as `Uninit`.
- `Type::Enum { variants: Map<Int, Variant>, discriminant_ty: IntType, discriminator,
  size, align }`, with `Variant { ty: Type, tagger: Map<Offset, (IntType, Int)> }`:
  - `ty` has the size of the whole enum (in practice a tuple whose fields are at
    enum-relative offsets);
  - the tagger lists the integers to write in the padding of `ty` to mark the variant.

  `Discriminator := Known(Int) | Invalid | Branch { offset, value_type: IntType, fallback,
  children: Map<(Int, Int), Discriminator> }` is a decision tree: it reads an integer at
  `offset`, picks the child whose range `[lo, hi)` contains it, and otherwise takes the
  fallback.
  - Decoding: run the discriminator on the bytes. Uninit bytes on its path are UB
    (`None`). Then decode `variants[d].ty` on all the bytes.
  - Encoding: encode the data at `ty`, then write the tagger.
- Niches are just enums whose discriminator reads bytes of the payload. For example,
  `Option<&T>` has size `PTR_SIZE`:
  - `None` has an all-padding `ty` and the tagger `{0 ↦ (usize, 0)}`;
  - `Some` has `ty = Tuple [(0, &T)]` and an empty tagger;
  - the discriminator is `Branch {0, usize, children {[0,1) ↦ Known 0}, fallback Known 1}`.

  Validity of `&T` (non-null, aligned) is what makes this sound.
- `GetDiscriminant` (a value expression on a place) and `SetDiscriminant` (a statement)
  run the discriminator and the tagger on memory.
- Typed loads and stores require the place to be aligned to `ty.align` (UB otherwise).
  `allocate(size, align)`.
- `Type::Union { fields, chunks: List<(Offset, Size)>, size, align }`. Its value is a list
  of chunks of raw bytes, and padding outside the chunks is lost.
- `Type::Array { elem, count }` has stride `elem.size`.

### 1.3 The gaps

| MiniRust | VerusBelt today | Needed for |
|---|---|---|
| field offsets chosen by the compiler (reordering) | `seq_tuple`, fixed order | default `repr(Rust)` structs and tuples |
| `align` in layouts; padding; size rounded up to the alignment | none | any realistic size or offset, `repr(C)` |
| aligned loads and stores (UB if misaligned), `allocate(size, align)` | none | fidelity for raw pointers and unsafe code |
| `Variant { ty, tagger }`, a tag anywhere, payload not necessarily after the tag | tag at 0, payload at `int_size tag` | `repr(Rust)` enums, `repr(u8)` with fields |
| discriminator trees | one tag | multi-byte or split tags, niches |
| niches (`Option<&T>`, `Option<bool>`, `Option<NonZero>`) | none (always a separate tag) | the null-pointer optimisation, FFI-visible sizes |
| `GetDiscriminant`/`SetDiscriminant` | `Load (MInt tag)` at offset 0; a variant is written as a whole value | `match` on niche enums; in-place construction |
| unions (`MaybeUninit`) | `uninitₛ n` is all padding | byte-preserving typed copies, `MaybeUninit<T>` |
| arrays with stride | none (`vecₛ` is zero-sized) | arrays and slices (out of scope here) |

Our own deviation that stays: pointers are `PtrFrag l i` bytes with an abstract `loc`. They
have no integer address, so a discriminator cannot read a pointer as an integer (see D7).

## 2. Generalising the `mty` layer

The aim: make `mty` MiniRust-shaped once, so that every later layout change (the oracle,
alignment, niches) changes only how `syn_mty` *builds* the `mty`, not `mty` itself or its
laws.

### 2.1 The new `mty`

```coq
Inductive discr : Set :=
| DKnown (t : Z)
| DInvalid
| DBranch (off : nat) (it : IntType) (fallback : discr) (children : list ((Z * Z) * discr)).

Inductive mty : Set :=
| MInt (it : IntType) | MBool | MPtr
| MTuple (fields : list (nat * mty)) (size align : nat)
| MEnum (variants : list (mty * nat * list (nat * IntType * Z)))   (* data, data offset, tagger *)
        (d : discr) (size align : nat).

Definition mty_align : mty → nat := (* int_align it | 1 | PTR_ALIGN | align | align *).
```

- **Variants.** A variant is `(vdata, voff, vtagger)`: its data (payload) at offset
  `voff`, and the tagger.
  - This is MiniRust's `Variant { ty, tagger }` with the one-field tuple `ty =
    Tuple [(voff, vdata)]` elided. With `voff = 0` and `vdata` the full-size tuple, it is
    MiniRust exactly.
  - The elision keeps `VVariant t d` with `d` the payload value, so `syn_val`,
    `type_mk_variant_val_instr`, `VariantData` and the examples do not change.
  - MiniRust's `variants: Map<Int, _>` becomes a list indexed by the discriminant, as
    today. `discriminant_ty` is dropped: `Case` takes a `VInt`, so nothing needs it.
- **`align`** is a field of `MTuple`/`MEnum`, not computed from the fields. `repr(align)`,
  `repr(packed)` and the oracle may pick it. `int_align` and `PTR_ALIGN` are sealed, like
  `PTR_SIZE`. Exported laws: they are powers of two, `int_align it ∣ int_size it`, and
  `PTR_ALIGN ∣ PTR_SIZE`.
- **Decoding the discriminator.** `decode_discr d bs : option Z` follows the tree.
  - At a `DBranch`, it reads `slice off (int_size it) bs` with `read_disc_int it`:
    `Some (inl z)` when the bytes decode as an integer, and `Some (inr l)` when they decode
    as a whole pointer.
  - An integer goes to the child whose range contains it, or to the fallback if none does.
  - A pointer goes to the fallback (deviation D7: pointers are non-null and have no
    address).
  - Anything else is `None`: uninit or partially overwritten bytes are UB, as in MiniRust.
- **Encode, decode.**
  - `encode (MEnum vars d sz al) (VVariant t v)`: insert `encode vdata v` at `voff` into
    `replicate sz Uninit`, then write each tagger entry `encode_int it z` at its offset.
  - `decode`: `t ← decode_discr d bs; (vm, o, _) ← vars !! t;
    VVariant t <$> decode vm (slice o (size vm) bs)`.
- **Today's layout as an instance.**
  - Variant `i` is `(m_i, tag_size, [(0, tag, i)])`.
  - The discriminator is `DBranch 0 tag DInvalid [((i, i+1), DKnown i) | i < n]`.
  - Every alignment is 1.

  So `seq_enum` is redefined with the new constructor, and every lemma stated about
  `seq_enum` (`syn_bytes_sum`, `cbytes_sum`, `mcells_seq_enum`, …) keeps its statement.

### 2.2 Well-formedness (still decidable: `wf_mty` and `pcellₛ` need `mty_wfb`)

- **`MTuple`.**
  - `fields_disjoint`, fields in bounds (as today);
  - new: every offset is a multiple of the field's `mty_align`, `align` is a power of two
    and a multiple of each field's align, and `align ∣ size`.

  The new conditions are only needed once alignment is checked (stage L5). Until then
  they can be left out of `mty_wf`, so that `seq_tuple` with `align = 1` stays well
  formed.
- **`MEnum`.** For each variant `(vm, o, tg)`:
  - the payload is in bounds and aligned, and `vm` is well formed;
  - the tagger entries are in bounds, pairwise disjoint, disjoint from the payload range
    `[o, o + size vm)`, and each value is in range of its `IntType`.

  The payload range is the whole `[o, o + size vm)`, not just its fields: a typed `Store`
  of the whole payload writes `Uninit` over the payload's padding.
- **Discriminator correctness `discr_ok vars d`.** This is decidable by *symbolic
  evaluation*: for each variant `t`, run `d` on an abstract byte map that knows the
  tagger bytes of `t` and nothing else.
  - Each `DBranch` on `t`'s path must read exactly one tagger entry, with the same
    `IntType`.
  - The path must end in `DKnown t`.

  This "tag-only" check is enough for stages L1–L3. Stage L4 (niches) lets a branch read
  payload bytes, when the *valid range* of the payload at that position (§2.4) is
  disjoint from every child range, or contained in one.

### 2.3 The laws

All of these stay axiom-free. Only the enum case changes.

- **Length.** Unchanged.
- **Round trip** `decode m (encode m v) = Some v`:
  - the payload part is today's argument;
  - the discriminator part follows from `discr_ok`: along `t`'s path, each read sees the
    tagger bytes that encode wrote, and the payload insertion does not overwrite them,
    since they are disjoint from the payload range.
- **Monotonicity.** When `decode_discr` succeeds, it read only defined (`Init`/`PtrFrag`)
  bytes, so `bytes_le` leaves those bytes unchanged. This is the argument for the tag
  today.
- **`decode_value_wf`.** `val_wf (MEnum …) (VVariant t d) := vars !! t = Some (vm, _, _) ∧
  val_wf vm d`. The `int_in_range tag t` conjunct goes: the discriminant is now just an
  index.
- **`frepr` (fancy bytes).** `frepr_enum` becomes:
  - `length fbs = sz`;
  - `decode_discr d (erase fbs) = Some t`, where `erase` maps a byte-cell `inl _` to
    `Uninit`. If the discriminator succeeds on the erased bytes, it read no cell
    (`Uninit` would have failed), so this also says that the discriminant is in plain
    bytes;
  - `frepr R vm (slice o (size vm) fbs) d`;
  - every byte outside the payload range is plain.

  `frepr_mono`, `frepr_restrict/union` and `fv_sub/fv_upd` (`fvalue.v`) keep their
  statements, with `int_size tag` replaced by `voff`.
- **Cells.** `mcells (MEnum …) (FVVariant t d) = mshift voff (mcells vm d)`.
  `gcells_enum` (`gcont.v`) and the enum `val_cells` (`value_ctx.v`) change the same way.

### 2.4 Valid ranges (stage L4)

`mty_valid_range m off it : option (Z * Z)`: an interval that contains the integer read as
`it` at `[off, off + int_size it)` from the encoding of *any* valid value of `m`.

- `MBool` at 0, read as `u8`: `[0, 2)`.
- An `MPtr` read whole: the pointer marker (it always goes to the fallback, D7).
- The direct tag of a nested `MEnum`: the tag values.
- Inside a field of an `MTuple`: that field's range. Elsewhere: `None` (unknown).

The soundness lemma `val_wf m v → read_disc_int it (slice off _ (encode m v)) ∈ range` is
what `discr_ok` uses for the branches that read the payload. Cells have no niche:
`pcellₛ`'s position yields `None`, so a discriminator can never read cell bytes (this is
rustc's "`UnsafeCell` hides niches"; the `erase` formulation above also enforces it).

### 2.5 A new expression: `GetDiscr m e`

`GetDiscr m e` reads `size m` bytes at `e` (non-atomically), runs `decode_discr` of the
enum `m`, and returns `VInt t`. It is UB (stuck) if the discriminator fails.

- WP rule: `l ↦b{q} bs ∗ ⌜decode_discr d bs = Some t⌝ ⊢ WP GetDiscr m #l {v, ⌜v = #t⌝ ∗
  l ↦b{q} bs}`.
- Races: the same byte-range read as `Load`.

`Case` on a sum becomes `case: GetDiscr (syn_mty (Σ! 𝔄l)) (pctx_expr K p)`. That is
MiniRust's `GetDiscriminant`, and it makes the case rules independent of where the tag is.
`SetDiscriminant` (write the tagger in place) is only needed for building enums in place
(stage L6). Today a variant is a whole `VVariant` value written by a typed `Store`, and
that still works.

## 3. Who decides layouts (the syntactic level)

`syn_mty : syn_type → mty` stays a function: the layout is determined by the syntactic
type, so every semantic type of `𝔄` agrees (`ty_mty_eq`). The question is what
`syn_mty (Π! 𝔄l)` and `syn_mty (Σ! 𝔄l)` are.

### 3.1 A sealed layout oracle (recommended)

These follow the `PTR_SIZE` pattern: a concrete definition, sealed, with only its laws
exported.

```coq
Record mlayout := { ml_size : nat; ml_align : nat; ml_niche : niche_info }.
Definition mty_layout (m : mty) : mlayout.   (* computed; niche_info is trivial until L4 *)

(* sealed *)
Definition struct_layout (ls : list mlayout) : list nat * nat * nat.   (* offsets, size, align *)
Definition enum_layout (ls : list mlayout) : list (nat * list (nat * IntType * Z)) * discr * nat * nat.

Definition struct_mty (ms : list mty) : mty :=
  let '(offs, sz, al) := struct_layout (mty_layout <$> ms) in MTuple (zip offs ms) sz al.
Definition enum_mty (ms : list mty) : mty := (* similarly, with enum_layout *).
```

**Exported laws.** These are what Rust guarantees for `repr(Rust)`, and nothing more:
- `struct_mty ms` and `enum_mty ms` are well formed (offsets aligned, disjoint and in
  bounds; `align ∣ size`; each field align divides `align`; `discr_ok`);
- `struct_layout [] = ([], 0, 1)` (the unit is a ZST);
- `length offs = length ms`.

Today's facts that are *not* laws (Rust does not promise them): field order, the absence
of padding, `size (A*B) = size A + size B`, the tag being at 0, and the payload being
after the tag.

**What the oracle depends on.** Only the field *layouts* (`mlayout`: size, align, niches),
not the field types. That is how rustc works: the layout of a generic struct is a function
of its field layouts. It also tells exactly what a byte-preserving map must preserve:
`syn_bincl f` gets one more conjunct, `mty_layout (syn_mty 𝔄) = mty_layout (syn_mty 𝔅)`
(its size component is the size conjunct it already has). With it, `prod_map`,
`psum_map`, `xprod` maps and `at_loc_map` stay byte-preserving.

**The concrete definition.**
- Stage L2: rustc's algorithm without niches: sort fields by decreasing alignment, then
  lay them out in order.
- Stage L3/L4: a tag after the largest payload, or a niche when there is one.

Which algorithm is chosen does not matter for proofs, which see only the laws. A
`Print Assumptions` stays clean (no axiom: the seal is `Local`).

**Later, a true parameter.** If we ever want the theorem "for every layout function
satisfying the laws", the oracle becomes a `Section` variable or a module functor
parameter, and `syn_mty` takes it. The proofs do not change, since they used only the
laws. This is mechanical, but touches every statement that mentions `syn_mty`, so we
defer it.

### 3.2 Alternatives

- **Explicit layouts in the syntactic type** (`xprodₛ (lay: struct_lay) 𝔄l`).
  - Pros: concrete; examples can match rustc's output byte for byte.
  - Cons: every `syn_type` match and `syn_type_beq` changes. Layouts become data that
    every rule must check for well-formedness (so `Π!` rules get side conditions). Two
    `Π!` types with different layouts are different types, so `xprod_subtype` needs equal
    layouts. And somebody (a frontend) has to supply the layouts.

  This is a good fit for `repr(C)`/`repr(u8)` (computed, not chosen), not for
  `repr(Rust)`.
- **Axioms** (`Parameter struct_layout` + `Axiom`s). Equivalent to the sealed definition,
  but it adds assumptions to every theorem. The seal gives the same abstraction for free.

### 3.3 `repr(C)` vs default

- **Default (`repr(Rust)`)**: the oracle. It is used for `prodₛ`, `Π!` and `Σ!`.
- **`repr(C)`** (later, L6): a *transparent* algorithm (fields in order, each rounded up
  to its alignment, size rounded up to the struct alignment), as a separate syntactic
  constructor or a `repr` flag on `xprodₛ`/`xsumₛ`.
  - Its offsets are still symbolic, since `int_align` and `PTR_ALIGN` are sealed.
  - The laws make the common cases provable. For example, `(i32, i32)` is at offsets 0
    and 4 with size 8, because `int_align i32 ∣ 4`.
  - This is how examples that want concrete numbers get them.

### 3.4 The payloads of enum variants

With `Σ! 𝔄l`, the payload of variant `i` is a value of the *type* `𝔄_i`. It is laid out
as a standalone `𝔄_i` (its own `syn_mty`), contiguously at `voff_i`. A `PSum` hole is
then a place of type `𝔄_i` at `l +ₗ voff_i`, so every leaf rule applies to it unchanged.

- Consequence: the tagger may not live in the payload's padding (a typed `Store` of the
  whole payload clobbers it). So rustc's layout of `enum E { A(u8, u32), B }` (tag at 0,
  `u8` at 1, `u32` at 4, size 8) is *outside* the space our laws allow: ours needs size 12.
- In Rust a variant payload is never a standalone value or a place, so rustc can
  interleave. Matching that would need variant places that go to the *fields* of a variant
  directly (`PSumField tyl i j`), whose offsets are enum-relative: MiniRust's full-size
  `Variant.ty`.
- The `mty` of §2.1 already allows this (`voff = 0`, a full-size tuple). Only the
  syntactic level and the sum places would change, so it is deferred (L6).
- Proofs about programs that do not depend on layout (all safe code) transfer anyway. The
  restriction matters only for claims about exact sizes.

## 4. Impact on the typing layer

### 4.1 Offsets and sizes are centralised

New definitions (in `bytes_layout.v`), each defined from `syn_mty`, so they are
oracle-sealed values:
- `prod_off1 𝔄 𝔅`, `prod_off2 𝔄 𝔅`: the two offsets of a pair;
- `xprod_off 𝔄l j`: the offset of field `j`;
- `sum_off 𝔄l i`: the payload offset of variant `i`;
- `sum_tagger 𝔄l i`: the tagger of variant `i`;
- `pads m`: the padding ranges of a tuple or of a variant, i.e. the complement of the
  payload and tagger ranges.

`lty_size_prod` (an additive size) is replaced by the bounds lemmas `prod_off1 + size 𝔄 ≤
size (𝔄*𝔅)`, the same for `off2`, and the disjointness of the two fields.

**`pctx_off`, `pctx_loc`, `pctx_expr`** (`lpath.v`):
- `PFst` becomes `+ₗ prod_off1` (it is 0 today, and the code relies on that);
- `PSnd` becomes `+ₗ prod_off2` (today `lty_size lt1`);
- `PSum tyl i` becomes `+ₗ sum_off 𝔄l i`, which now depends on `i` (today `tag_size`).

The proofs about `pctx_loc` (`pctx_loc_plug`, `pctx_off` vs `pctx_loc`, `wp_pctx_expr`)
change only in the arithmetic.

### 4.2 Splitting lemmas: one generic lemma per constructor

The real work is replacing the sequential splitting lemmas by *generic* ones over an
arbitrary well-formed `MTuple`/`MEnum`. These can be written and proved **before** any
layout changes (stage L1/L2a), and then the sequential versions become corollaries.

- **Plain bytes.**
  - `syn_bytes_tuple`: the bytes of a tuple are, field by field, the slices at the
    offsets, with any padding.
  - `syn_bytes_pair`: `∃ bs1 bs2, slice off1 bs = bs1 ∧ slice off2 bs = bs2 ∧ length bs =
    size`.
  - `syn_bytes_sum`: the tagger bytes, the payload slice at `voff`, and arbitrary padding.
- **Fancy bytes.** `frepr_tuple_iff` already is the generic form; `frepr_seq_tuple_cons`
  is replaced by it. `frepr_enum_iff` gets the discriminator form of §2.3.
- **Ownership.**
  - `gcont_tuple`: `gcont l (MTuple fs sz al) (FVTuple fvs) ⊣⊢ ([∗ list] (o, m); fv ∈ fs;
    fvs, gcont (l +ₗ o) m fv) ∗ pad_own l (pads fs sz)`, where `pad_own l rs := [∗ list]
    (o, n) ∈ rs, pad_cell (l +ₗ o) n`. It is proved once, from `gfbytes` over disjoint
    ranges. It replaces `gcont_seq_tuple_cons`/`nil`.
  - `bytes_own_pair` and `cbytes_pair`: the two fields at `l +ₗ off1`, `l +ₗ off2`, and
    `pad_own`.
  - `cbytes_sum`: `tagger_own l (sum_tagger 𝔄l i)` (a `tag_cell` per entry) ∗
    `cbytes tyi y (l +ₗ sum_off 𝔄l i)` ∗ `pad_own`. In L1 this is literally today's
    statement.
- **Nodes.**
  - `prod_node` gets the offsets and a padding conjunct: `c1 r1 … (l +ₗ o1) ∗ c2 r2 …
    (l +ₗ o2) ∗ pad_own l pads`.
  - `sum_node` and `view_sum` change the same way.

  The padding has no ghost ownership, so, like the tag and the sum padding today, the nodes
  stay mode-independent.
- **Cells and values.** `mcells_pair`, `mcells_sum`, `val_cells_seq_tuple_cons` and the
  enum `val_cells` are restated with offsets.

### 4.3 Byte-preserving isomorphisms that are lost

With an oracle (or just with alignment), these are **no longer** byte-preserving: they are
`Isoₛ` instances today, and they must be dropped as `Isoₛ` and as subtypings:
- `prod_assocₛ` (`prod_ty_assoc`);
- `prod_left_idₛ`/`right_idₛ` (`prod_ty_left/right_id`);
- `to/of_cons_prodₛ` (`isoₛ_cons_prod`).

They stay available as value-level conversions: load, rebuild with
`MkTuple`/`Proj`, store.

Consequences:
- **`xprod_ty`** must be defined directly as an n-ary product type, like `xsum_ty`
  already is, instead of `mod_ty` of the cons pair. Its ownership is the `[∗]` of the
  field ownerships, and its sharing is at `xprod_off`.
- **`place_xprod.v`**: `tctx_unfold/fold_oplace_xprod` split `Π! (ty :: tyl)` by the cons
  iso, which is now false (the tail `Π! tyl` laid out standalone is not the tail of the
  struct). Structs need **n-ary product places**:
  - a place type `XProdLty (lts : ltyl 𝔄l)`, with a mutual list inductive `ltyl` or an
    `hlist`;
  - a context step `PXField (lts_before) j (lts_after) K`, at `xprod_off 𝔄l j`.

  This is the "ConsLty / 6.5 Products" item of the phase 3 design. It is the largest
  single item here (every `Fixpoint` over `lty`/`pctx` in `ltype.v`, `lpath.v` and
  `pctx_acc.v` gets a case), and it also removes the "`Π!` below unique borrows" gap,
  since the folded type no longer changes.
- **Binary `ProdLty`/`PFst`/`PSnd`** stay for `prodₛ`, with oracle offsets. Once n-ary
  places exist, Rust tuples can be `Π! [A; B]`, and `prodₛ` can be reserved for internal
  pairs.
- **Survivors.**
  - `uninit_splitₛ` is restated as `↯ (syn_bsize (↯n * ↯m)) ≅ ↯n * ↯m`: padding types
    decode from any bytes, so this is byte-preserving for *any* layout. Only the size
    stops being `n + m`.
  - `empty_prod_to_unitₛ` and `uninit0_to_unitₛ` survive (both sides are zero-sized, by
    the `struct_layout []` law).
  - `at_loc_mapₛ` and `psum_map`/`prod_map` of byte-preserving maps survive, with the
    `mty_layout` conjunct of §3.1.

### 4.4 Sums

- **Reading the discriminant.** `type_case_oplace` (and `place_deep`, `place_pshr`) use
  `GetDiscr` (§2.5) on the whole sum leaf. They already own the leaf's bytes (or a
  guarded fraction for `&shr`), and the discriminator's success follows from the
  generalised `cbytes_sum`. The proof shape is unchanged: open the bytes, read, close.
- **Writing a variant.** Writing a whole `VVariant` (`type_mk_variant_val_instr` + typed
  `Store`) is unchanged.
- **Writing into the payload of an unfolded `SumLty`.**
  - Without niches (L1–L3) the tagger is separate, so payload writes are as today.
  - With niches (L4) the discriminant lives in the payload bytes. Folding `SumLty tyl i
    (OfTy ty_i)` back to `OfTy (Σ! tyl)` needs the payload bytes to be *a value of
    `𝔄_i`* (it does today too: `cbytes tyi y`). The valid-range lemma (§2.4) then gives
    the discriminator.
  - A moved-out payload (`↯`) cannot be folded back, exactly as today.
  - Mutable borrows of the payload are fine: the sum cannot be matched while the payload
    is borrowed, as in Rust.
  - Shared borrows of the payload and a discriminant read at the same time need both to
    read the same bytes. That works with fractional or guarded bytes, but `place_pshr`'s
    sum rule has to read the payload's bytes rather than a separate tag cell. This is the
    one L4 item that changes a proof structurally.
- **`tag_cell 𝔄l l i`** becomes `tagger_own l tg` (a list of int cells). For niche
  variants with an empty tagger, it is `True`.

### 4.5 `Moved`, `↯`, `Copy`, `NoCell`, cells

- `Moved`/`↯`: a moved leaf is `↯ (syn_bsize 𝔄)` at the leaf's location. That is
  independent of the layout, given the centralised offsets.
- `Copy`: copies are typed loads, which lose padding (already the case for sum padding);
  `MemCopy` keeps it. Nothing changes, but products now have padding too, and the
  `pad_own` conjuncts carry it.
- `NoCell`: unchanged.
- Cells (`gcont`, `mcells`): the offsets follow the `mty`, so they are layout-generic.
  Alignment requirement A (cells only at whole sub-value positions) is unaffected. Cells
  never carry niches (§2.4).

### 4.6 Examples

- `+ₗ #4` becomes `+ₗ #(prod_off2 i32ₛ i32ₛ)` (a closed literal; the program is
  parametric in the sealed layout, as compiled code is in rustc's choice).
- `Alloc #8`/`own_bytes 8` become `Alloc #(syn_bsize …)`/`own_bytes (syn_bsize …)`.
- `pair_ty_mty` and the hard-coded `MTuple` tests move to `repr(C)` types (L6), or are
  restated with the laws.

The changes are syntactic, and the proofs should not change, apart from
`syn_bsize`-arithmetic side conditions (`lia` after `rewrite` with the bounds lemmas).

### 4.7 Alignment checks (stage L5)

- **Semantics.**
  - `Load`/`Store`/`MemCopy`/`GetDiscr` at `l` with `mty_align m ∤ l.2` are stuck.
  - `Alloc n a` gives offset 0, which is aligned to everything: abstract blocks are
    maximally aligned, a sound abstraction of `allocate(size, align)`.
- **Typing.** `bytes_own ty l x` gets `⌜aligned l (ty_align ty)⌝`. Field offsets are
  multiples of field alignments (an oracle law), so `pctx_loc` of an aligned root is
  aligned (one lemma). The leaf rules thread the fact through.
- **Benefit.** Fidelity for raw pointers, and for pcell/unsafe code later. Well-typed safe
  code never misaligns, so this is a pure cost for the current examples. Defer.

## 5. Decisions for the user

**D1. Who chooses layouts.**
- (a) Explicit layout annotations in `syn_type`.
- (b) A sealed oracle with exported laws (the `PTR_SIZE` pattern).
- (c) A `Section`/functor parameter (truly "for all layouts").
- (d) Axioms.

**Recommendation: (b)** for `repr(Rust)`, stated so that (c) is a mechanical switch later.
Use (a)-style transparent computation only for `repr(C)`.

**D2. The input of the oracle.**
- (a) The field `mty`s.
- (b) The field layout summaries `mlayout` (size, align, niches).

**Recommendation: (b)**: it is rustc-faithful. Add `mty_layout` equality to `syn_bincl`.

**D3. Reordering for default-repr products.**
- (a) Keep the declared order (repr(C)-like) everywhere.
- (b) The oracle may reorder.

**Recommendation: (b)**. The assoc/unit/cons isos are lost either way as soon as there is
alignment, so (a) buys little.

**D4. Alignment.**
- (a) None (align 1, reorder only).
- (b) Alignment in layouts (padding, size rounding) without alignment UB.
- (c) Also UB on misaligned access, with `Alloc` taking an alignment.

**Recommendation: (b)** in L2, and (c) as the optional stage L5.

**D5. The shape of enum variants in `mty`.**
- (a) Keep tag-at-0.
- (b) MiniRust-exact (full-size `ty`, `VVariant t (VTuple [v])`).
- (c) MiniRust with the payload offset (`vdata, voff, tagger`), which contains (b) at
  `voff = 0`.

**Recommendation: (c)**: `syn_val` and the variant instructions do not change.

**D6. Discriminators.**
- (a) One tag (offset, `IntType`).
- (b) MiniRust's decision trees.

**Recommendation: (b)** in the `mty` from L1. It costs little there, and its
well-formedness stays decidable by symbolic evaluation. Only tag-reading branches are
allowed until L4.

**D7. Niches, and pointer bytes.**
- When: now or later. **Recommendation: later (L4)**, with the `mty` of L1 already able to
  express them.
- How a discriminator treats pointer bytes, which we cannot read as integers:
  - (a) they go to the fallback (pointers are non-null);
  - (b) forbid branches that read pointer positions, which loses `Option<&T>`;
  - (c) give pointers integer addresses, a big change to the memory model.

  **Recommendation: (a)**. It is sound for rustc's only pointer niche (0), and it is a
  documented deviation.
- Whether to export the *guaranteed* niche law: `Option<&T>`, `Option<Box<T>>` and
  `Option<NonZero…>` have the size of `T`, with `None` all zeros. **Recommendation: only
  when an example or FFI needs it.**

**D8. How enum payloads are placed.**
- (a) Contiguous standalone payloads (`PSum` stays a place of type `𝔄_i`).
- (b) Interleaved variant fields (variant places go to fields, MiniRust's full-size
  `Variant.ty`).

**Recommendation: (a)** now, and (b) only if exact rustc sizes matter (§3.4).

**D9. `match`.**
- (a) Keep `Load (MInt tag)` at a tag offset.
- (b) A `GetDiscr m e` primitive.

**Recommendation: (b)** in L1: it is MiniRust's `GetDiscriminant`, and it makes later
layout stages invisible to the case rules.

**D10. Field offsets in programs.**
- (a) Literal offsets `#(prod_off2 …)`.
- (b) A `Field m j e` expression.

**Recommendation: (a)**: `pctx_expr` already builds `+ₗ #n`.

**D11. Struct places.**
- (a) Keep binary `ProdLty` and recover `Π!` via cons splitting.
- (b) N-ary `XProdLty`.

(a) is impossible with real layouts. **Recommendation: (b)** (L2b).

**D12. Unions / `MaybeUninit`.** Out of scope. `uninitₛ n` stays all-padding. A
`VUnion (list (list AbstractByte))` value would add byte-preserving typed copies; consider
it with the pcell work.

## 6. Staged plan

Each stage ends with a clean full build and a commit, as before. The key de-risking
device: **seal first, change later**. Each stage first introduces the generic definitions
and laws while the sealed implementation still computes today's layout, ports every
user to the laws, and only then changes the implementation. If all proofs use only the
laws, the last step is free.

**L1 — MiniRust-shaped `mty`, generic splitting lemmas, `GetDiscr`.**
- *Size:* about 12 files, roughly +700/−250 lines. *Risk:* low to medium (all at the
  bottom of the stack; `gmb_cells.v` has 16 `MEnum` uses).
- *Language:*
  - `minirust.v`: `discr`, the new `MEnum` and `MTuple` (with `align`, set to 1
    everywhere), `decode_discr`, `discr_ok` (tag-only, decidable), and the three laws;
  - `fvalue.v`: the `frepr_enum` of §2.3, and `fv_sub`/`fv_upd` with `voff`;
  - `minirust_tests.v`;
  - `lang.v` and `lifting.v`: `GetDiscr` (head step, `wp_get_discr`, races).
- *Syntactic layer:*
  - `seq_enum` is restated in the new form (same layout);
  - `mcells`;
  - `bytes_layout.v`: `frepr_enum_iff`, `syn_bytes_sum`, `syn_fbytes_sum`;
  - the generic `gcont_tuple`/`gcont_enum`, `frepr_tuple`-based pair lemmas and
    `pad_own`, with the `seq_*` lemmas reproved as corollaries;
  - `gcont.v`/`gmb_cells.v`: `gcells_enum`; `value_ctx.v`: the enum `val_cells`.
- *Typing:* `place_sum.v`, `place_deep.v` and `place_pshr.v` switch `Case` to `GetDiscr`.
- *Statements above `bytes_layout.v`:* unchanged.

**L2a — Centralised offsets, products through a sealed struct oracle (still
sequential).**
- *Size:* about 25 files. *Risk:* medium-high: wide but mostly arithmetic. Keep the
  example `Qed` times in view (some `simpl`/`change (syn_mty …)` tricks rely on
  computation through `seq_tuple`).
- *Definitions:*
  - `mlayout`, `int_align`/`PTR_ALIGN` (sealed), `struct_layout` (sealed, computing
    `seq_tuple` with align 1), `struct_mty`;
  - `prod_off1/2`, `xprod_off`, `pads`, and the bounds lemmas.
- *Users switched to the laws:*
  - `pctx_off/loc/expr`, `prod_node`, the views, `bytes_own_pair`/`cbytes_pair`,
    `lty_size_prod` users, `syn_bincl` (+ `mty_layout`);
  - the examples, to symbolic offsets and sizes.
- *Removed:* the assoc/unit/cons `Isoₛ` instances and the `decode_assoc`/`decode_prod_*`
  lemmas.
- *Restated:* `uninit_split`.
- *Temporary:* `xprod_ty` defined directly. `place_xprod.v` is kept by restating it with
  a *sealed sequential-tail law*, or else disabled until L2b. **Open question:** prefer
  disabling, so that no law that is false in general enters.

**L2b — N-ary struct places.**
- *Size:* 8–12 files, large edits in `ltype.v`/`lpath.v`/`pctx_acc.v`. *Risk:* high
  (nested inductive in the place types, many fixpoints).
- *Work:*
  - `XProdLty`/`PXField` with `xprod_off`;
  - the ports of the leaf, unfold, fold and reborrow rules;
  - `place_struct.v` (`set_mid_b_type`) ported;
  - `Π!` below unique borrows comes for free.

**L2c — Real struct layouts.**
- *Size:* 1–2 files. *Risk:* low, if L2a/L2b used only the laws; any failure points at a
  proof that used the implementation.
- *Work:*
  - change the sealed `struct_layout` to sorting by alignment, with size rounding;
  - add the alignment conjuncts to `mty_wf`;
  - prove the laws.

**L3 — Enums through the sealed oracle (no niches).**
- *Size:* about 10 files. *Risk:* medium.
- *Work:*
  - `enum_layout` (sealed, computing today's layout at first);
  - `sum_off 𝔄l i`, `sum_tagger 𝔄l i`;
  - `PSum` offsets, `sum_node`, `view_sum`, `cbytes_sum`, `tagger_own`;
  - then switch the implementation to "tag after the largest payload, aligned".

**L4 — Niches.**
- *Size:* about 8 files. *Risk:* medium-high (the `place_pshr` sum rule; the valid-range
  soundness proof over all `mty`s).
- *Work:*
  - `niche_info` in `mlayout`, `mty_valid_range` and its soundness lemma;
  - `discr_ok` with payload-reading branches;
  - `read_disc_int` and the pointer deviation (D7a);
  - the oracle uses a niche when available; the folding of sum places uses the
    valid-range lemma; the `place_pshr` sum rule reads the payload bytes;
  - optionally, the guaranteed `Option<&T>` law and an example
    (`size_of::<Option<&i32>>() = PTR_SIZE`).

**L5 (optional) — Alignment UB.**
- *Size:* about 15 files, mostly threading one pure fact. *Risk:* medium.
- *Work:* the stuck conditions on misaligned accesses, `Alloc` with an alignment,
  `aligned` in `bytes_own`, and the lemma that `pctx_loc` preserves alignment.

**L6 (later, as needed).**
- `repr(C)`/`repr(uN)` as transparent layouts, with concrete-number examples;
- `SetDiscriminant`;
- interleaved variant layouts (D8b, variant field places);
- unions/`MaybeUninit` (D12);
- the oracle as a true parameter (D1c).

**Order and effort.** L1 is useful on its own: it makes the `mty` faithful and decouples
the case rules. L2a+L2b are the bulk: most of the cost is n-ary struct places, which were
already a known gap. L3/L4 are independent of L2b. A reasonable first milestone is
L1 + L2a + L2c, with `Π!` places disabled or kept on a transitional law, then L2b.

## 7. Revision (user decisions 2026-11-03): explicit layouts

The user replaced D1/D2 (the sealed layout oracle, §3.1) by **explicit layouts as type
parameters**: "operational semantics with typed operations (`mty`); typing rules with
layouts; a well-typed program has these all in agreement". `prod`, `xprod` and `xsum` are
replaced completely by `struct_ty` and `enum_ty`. The other recommendations stand: D4 (b)
alignment in layouts now, misaligned-access UB later (L5, optional); D5 (c); D6 (b); D7
later (L4); D9 (b) `GetDiscr` in L1; D11 (b) n-ary field places; D12 no unions. D8: with
explicit layouts, interleaving can later be written as a variant payload that is itself a
`struct_ty` at offset 0; contiguous payloads are fine for now. §3 (the oracle), §4.1 (the
sealed offsets) and the L2/L3 parts of §6 are superseded by this section.

### 7.1 The `mty` layer (L1)

As §2.1, with these details:

```coq
Inductive discr : Set :=
| DKnown (t : Z) | DInvalid
| DBranch (off : nat) (it : IntType) (fallback : discr) (children : list ((Z * Z) * discr)).
Definition tagger : Set := list (nat * IntType * Z).          (* offset, type, value *)

Inductive mty : Set :=
| MInt (it : IntType) | MBool | MPtr
| MTuple (fields : list (nat * mty)) (size align : nat)
| MEnum (variants : list (mty * nat * tagger))               (* payload, offset, tagger *)
        (d : discr) (size align : nat).
```

- **Alignment.** `mty_align`: `int_align it` (concrete: `max 1 (int_size it)`), `1` for
  `MBool`, `PTR_ALIGN` (sealed like `PTR_SIZE`, with `0 < PTR_ALIGN` and
  `PTR_ALIGN ∣ PTR_SIZE` exported), the `align` field of tuples and enums. In L1 `mty_wf`
  does not check alignment (the sequential layouts have `align = 1`); L2 adds the tuple
  conditions (offsets aligned, field alignments divide `align`, `align ∣ size`) and L3 the
  enum ones, when the sequential layouts are gone.
- **Discriminators** are evaluated by `discr_eval (rd : nat → IntType → option Z) d`: a
  branch reads `rd off it`, goes to the first child whose range `[lo, hi)` contains the
  integer, else to the fallback; `None` is UB. `decode_discr d bs` is `discr_eval` with the
  reader `decode_int it (list_slice off (int_size it) bs)`. Only integers are read: pointer
  bytes are UB for now (D7a, pointers go to the fallback, comes with niches in L4).
- **Well-formedness of an enum** (decidable, `mty_wfb`). For each variant `(vm, o, tg)`:
  `o + size vm ≤ size`, `mty_wf vm`; the tagger entries are in bounds, pairwise disjoint,
  disjoint from `[o, o + size vm)`, and in range of their `IntType`. Then:
  - `discr_ok`: for each variant `t`, `discr_eval (tagger_reader tg_t) d = Some t`
    (symbolic evaluation, §2.2);
  - **tag-only** (new, replaces "each branch reads a tagger entry"): every range read by a
    branch of `d` (static, `discr_reads d`) is in bounds and disjoint from the payload range
    of every variant. Then no path of `d` reads a payload byte, whatever the bytes: a write
    into the payload never changes the discriminant (needed by `frepr_upd`: the actual path
    on arbitrary bytes need not be the symbolic one), and the discriminator never reads the
    byte-cells of a payload. L4 relaxes this for niches.
- **Decode/encode**: `decode`: `t ← decode_discr d bs; (vm, o, _) ← vars !! t;
  VVariant t <$> decode vm (slice o (size vm) bs)`. `encode`: the payload inserted at `o`
  into `replicate size Uninit`, then the tagger entries. `val_wf (MEnum …) (VVariant t v)`
  is `vars !! t = Some (vm, _, _) ∧ val_wf vm v` (no tag range any more).
- **`frepr_enum`**: `length fbs = size`, `decode_discr d (erase fbs) = Some t` (`erase` maps
  a byte-cell to `Uninit`), the payload represented at `slice o (size vm) fbs`, and every
  byte outside the payload range plain. `fv_sub`/`fv_upd`/`mcells`/`gcells` use `o`.
- **`GetDiscr m e`** (MiniRust's `GetDiscriminant`). Deviation from §2.5: it does not read
  `size m` bytes — that would read the byte-cells of a payload (owned by cell borrows, not
  by `↦b`) and race with interior mutability. As in MiniRust, it reads only the bytes of the
  branches on the path: once `e` is a location `l`, a pure head step unfolds it (for
  `m = MEnum _ d _ _`) into `discr_expr d l`: per branch, `let: "z" := Load Na1Ord (MInt it)
  #(l +ₗ off)` and comparisons on `"z"`; `DKnown t` is `#t`; `DInvalid` is stuck. So the
  races and the adequacy are those of `Load` (the new head step is pure).
  - `wp_get_discr`: for chunks `cs : list (nat * list abyte)` with
    `discr_eval (chunks_reader cs) d = Some t`,
    `{{{ [∗ list] c ∈ cs, (l +ₗ c.1) ↦b c.2 }}} GetDiscr m #l {{{ RET #t; same }}}`;
  - `wp_get_discr_guarded`: the chunks guarded by `G`, with `£(2 * d * discr_depth)`.
  - The case rules use `case: GetDiscr (ty_mty (Σ! tyl)) p of …`.

### 7.2 Layouts

```coq
Record struct_layout := SL { sl_offs : list nat; sl_size : nat; sl_align : nat }.
Record enum_layout := EL { el_vars : list (nat * tagger);    (* payload offset, tagger *)
                           el_discr : discr; el_size : nat; el_align : nat }.

Definition sl_mty L ms := MTuple (zip L.(sl_offs) ms) L.(sl_size) L.(sl_align).
Definition sl_wf L ms : Prop := length L.(sl_offs) = length ms ∧ mty_wf (sl_mty L ms).
Definition struct_mty L ms := if decide (sl_wf L ms) then sl_mty L ms else sl_mty (c_layout ms) ms.

Definition el_mty EL ms := MEnum (zip_with (λ m '(o, tg), (m, o, tg)) ms EL.(el_vars))
                                 EL.(el_discr) EL.(el_size) EL.(el_align).
Definition el_wf EL ms : Prop := length EL.(el_vars) = length ms ∧ mty_wf (el_mty EL ms).
Definition enum_mty EL ms := if decide (el_wf EL ms) then el_mty EL ms else el_mty (tagged_layout ms) ms.
```

- **Well-formedness** is decidable (`mty_wfb`), w.r.t. the sizes and alignments of the
  field types. It is checked by computation when the fields have concrete sizes (integers),
  and by a tactic (`lia` after unfolding) when they involve `PTR_SIZE`.
- **Computed layouts are helpers**:
  - `c_layout ms` (`repr(C)`): fields in order, each offset rounded up to the field's
    alignment, `align` the `lcm` of the field alignments (their max, for powers of two; 1
    for no field), `size` the end rounded up to `align`. `sl_wf (c_layout ms) ms` holds
    when the `ms` are well formed.
  - `tagged_layout ms` (`repr(C, u8)`-like): the tag `enum_tag n` at 0, every payload at
    the tag size rounded up to the maximal payload alignment, one `DBranch` on the tag.
- **Ill-formed layouts fall back to the computed layout.** So `syn_mty` stays total and
  always well formed, and `ty_mty_wf` stays unconditional. The typing rules never need
  `sl_wf`: every offset they use is read off the actual `mty`
  (`struct_off L 𝔄l j`, `enum_off EL 𝔄l i`), so they are correct for every `L`; `sl_wf`
  only tells that those numbers are `L`'s (`struct_off_wf : sl_wf L ms → struct_off L 𝔄l j
  = sl_offs L !!! j`). For `c_layout` both branches coincide, so `struct_mty (c_layout ms)
  ms = sl_mty (c_layout ms) ms` without any wf proof (generic code, e.g. `List<T>`).
  (Rejected alternative: `struct_ty` takes a wf proof and `syn_mty_wf` becomes conditional,
  which changes the type record and every use of `ty_mty_wf`.)

### 7.3 Syntactic and semantic types

- New syntactic types `structₛ (L: struct_layout) 𝔄l` (interpreted as `plist`, like `Π!`)
  and `enumₛ (EL: enum_layout) 𝔄l` (interpreted as `psum`, like `Σ!`), with
  `syn_mty (structₛ L 𝔄l) = struct_mty L (syn_mty <$> 𝔄l)`,
  `syn_mty (enumₛ EL 𝔄l) = enum_mty EL (syn_mty <$> 𝔄l)`, and `syn_val`/`syn_fval`
  structural (`VTuple`, `VVariant i`).
- `prodₛ` (`*`), `xprodₛ` (`Π!`) and `xsumₛ` (`Σ!`) stay as **logical** syntactic types
  (they are used for prophecy variables, e.g. `uniq_cellₛ`, for ghost and tracked contents,
  and `Empty_setₛ`), like `sumₛ`, `optionₛ`: zero-sized, with `syn_val = VTuple []`. Their
  memory cases in `syn_mty`/`syn_val`/`syn_fval`/`syn_nocell` are deleted.
- `struct_ty L tyl : type (structₛ L 𝔄l)` and `enum_ty EL tyl : type (enumₛ EL 𝔄l)`: the
  ghost parts are those of `xprod_ty` (the `[∗ hlist]` of the fields, without the cons iso)
  and of `xsum_ty`; the bytes are generic (`syn_mty`). `unit_ty : type unitₛ` is defined
  directly (zero-sized).
- **Deleted**: `prod_ty`, `xprod_ty`, `unit0`, `xsum_ty`, `empty_ty`, `seq_tuple`,
  `seq_enum`, `place_xprod.v`, `prod_assocₛ`, `prod_left/right_idₛ`, `to/of_cons_prodₛ`,
  `cons_prodₛ`, `plist_mapₛ` at `Π!` (moved to `structₛ`), the `decode_prod_*`,
  `decode_assoc_*` lemmas and all `seq_*`/sequential splitting lemmas.
- **Byte-preserving maps**: `syn_bincl` gets the conjunct `mty_align (syn_mty 𝔄) =
  mty_align (syn_mty 𝔅)` (with the size, it determines `sl_wf`), so `struct_map`/`enum_map`
  of byte-preserving maps (same `L`) are byte-preserving. `uninit_split` becomes
  `↯ (n + m) ≅ cstructₛ [↯ n; ↯ m]` (its `c_layout` is `[0; n]`, size `n + m`).
- **Subtyping** `struct_subtype`/`enum_subtype`: same layout, field-wise (as `xprod`/`xsum`).
- **Helpers for examples**: `cstructₛ 𝔄l := structₛ (c_layout (syn_mty <$> 𝔄l)) 𝔄l`,
  `cenumₛ 𝔄l := enumₛ (tagged_layout (syn_mty <$> 𝔄l)) 𝔄l`, and the corresponding types
  (`cstruct_ty tyl`, `cenum_ty tyl`). An explicit layout is written `SL [0; 4] 8 4`.
  Programs use `#(struct_off L 𝔄l j)`, `Alloc #(syn_bsize …)`; for integer fields these
  compute to numbers.

### 7.4 Struct places (L2)

- `StructLty {𝔄l} (L: struct_layout) (lts: hlist lty 𝔄l) : lty (structₛ L 𝔄l)` replaces
  `ProdLty`. This is a nested inductive through `hlist` (Coq accepts it); the `Fixpoint`s
  recurse on `lts` through `hmap`-like functions or an inner `fix`, and the proofs use a
  custom induction principle with an `HForall` hypothesis.
- Refinements: `prfn_struct (structₛ L 𝔄l) := plist (λ 𝔅, prfn 𝔅) 𝔄l` (by a nested
  recursion on the list); patterns: `PatStruct (ps: list lpat)`; paths: `list nat` (field
  `j`; `0` below pointers and sums).
- `struct_node L children r l := ([∗ hlist] child_j r_j (l +ₗ struct_off L 𝔄l j)) ∗
  pad_own l (struct_fields L 𝔄l) (struct_size L 𝔄l)`. Mode-independent, as `prod_node`.
- Context step `PField L (lts: hlist lty 𝔄l) (j: fin (length 𝔄l)) K`, at offset
  `struct_off L 𝔄l j`; `pctx_plug (PField L lts j K) lt = StructLty L (hlist_set lts j
  (pctx_plug K lt))` (the entry `j` of `lts` is ignored, as for `SumLty`).
- Unfolding: `OfTy (struct_ty L tyl)` is `ltype_eq` to `StructLty L (hmap OfTy tyl)`
  (owned), and behind a unique borrow by the compound body (as `prod_ofty_unfold_uniq`).
  `Π!` below unique borrows comes for free.
- Types (L2a): `struct_ty L tyl := struct_of L (fields_ty tyl)`, where `fields_ty tyl :
  type (Π! 𝔄l)` carries the ghost parts of the fields (`Π!` becomes logical) and
  `struct_of L` the bytes of `structₛ L 𝔄l`.
- Rejected alternative: a cons-list of field places inside `lty` at the logical `Π!`
  (`FieldsLty o lt lts`, under a `StructLty L` that owns the padding), which would keep the
  binary `ProdLty` proofs. A chain node owns the bytes of its fields while its folded type
  (at `Π!`) owns none, so the generic folding lemmas (by induction on `lt`, "a place gives the
  leaf of its folded type") would be false on chain nodes.

### 7.5 Enums (L3)

- `SumLty` is restated over `enumₛ EL 𝔄l` (`SumLty EL tyl i lt`, folded type
  `enum_ty EL (hlist_set tyl i (lty_fold lt))`).
- `PSum EL tyl i w K` at `enum_off EL 𝔄l i` (read off the actual `mty`).
- `sum_node`/`view_sum`: the payload at `l +ₗ enum_off`, and `enum_rest l m i`: the bytes
  outside the payload (tagger and padding), whose `decode_discr` (with the payload range
  erased) is `i`. It replaces `tag_cell`/`pad_cell`, and is what `GetDiscr` reads.
- `MkVariant` + typed `Store` of a whole variant are unchanged.

### 7.6 Revised staged plan

- **L1 — MiniRust-shaped `mty`, `GetDiscr`** (§7.1). `seq_tuple`/`seq_enum` (align 1) stay
  as the layouts of `Π!`/`Σ!`/`*`; the typing layer keeps its statements; the case rules
  switch to `GetDiscr`.
- **L2 — Structs.** `struct_layout`, `c_layout`, `structₛ`, `struct_ty`, `StructLty`,
  `PField`, `struct_node`, `pad_own`; the generic tuple splitting lemmas (bytes, fancy
  bytes, cells, values); tuple alignment in `mty_wf`; examples ported to `struct_ty`;
  `prod_ty`, `xprod_ty`, `place_xprod.v`, the product isomorphisms and the sequential
  tuple lemmas deleted; `prodₛ`/`xprodₛ` logical. Possibly in several merges (layouts and
  types; places; deletion).
- **L3 — Enums.** `enum_layout`, `tagged_layout`, `enumₛ`, `enum_ty`, `SumLty` over
  `enumₛ`, `enum_off`, `enum_rest`; enum alignment in `mty_wf`; `xsum_ty`, `seq_enum` and
  the sequential sum lemmas deleted; `xsumₛ` logical; examples ported.
- **L4 — Niches** and **L5 — alignment UB**: as §6.

## Outcome: L1 (branch `proto/layout-l1`)

- **`mty`** (`lang/minirust.v`) as §7.1: `discr` (`DKnown`/`DInvalid`/`DBranch`), `tagger`,
  `MTuple fs size align`, `MEnum (variants: list (mty * nat * tagger)) d size align`,
  `mty_align`, `int_align it = max 1 (int_size it)`, sealed `PTR_ALIGN` (`PTR_ALIGN_pos`,
  `PTR_ALIGN_divide`). `discr_eval rd d` with the laws `discr_eval_agree` (readers that agree
  on `discr_reads d`) and `discr_eval_ext` (an extending reader); `decode_discr d bs`.
- **Well-formedness** (decidable, `mty_wfb_correct`): `enum_layout_ok vars d sz` =
  payloads in bounds, `tagger_wf` (entries in bounds, outside the payload, pairwise
  disjoint, in range), `discr_tag_only` (no branch reads a payload byte), `discr_ok`
  (symbolic evaluation on each tagger). No alignment checks yet. Concrete enums are checked
  by computation (`opt_mty_wf : … := mty_wfb_correct; vm_compute` in `minirust_tests.v`).
- **Laws**: `decode_encode_value` (round trip, via `decode_discr_encode`),
  `decode_value_mono` (via `decode_discr_mono`), `decode_value_wf` (`val_wf` of a variant no
  longer has the tag range), the length laws. `fvalue.v`: `frepr_enum` with
  `decode_discr d (fb_erase <$> fbs) = Some t` and plain bytes outside the payload;
  `fv_sub`/`fv_upd` at the payload offset; `decode_discr_agree_payload` (the
  discriminant does not depend on payload bytes) gives `frepr_upd`. `fb_base` of
  `gmb_cells.v` is now `fb_erase`.
- **Cells**: `mcells`/`gcells` of a variant are shifted by its payload offset;
  `gcont_enum_intro` and `val_cells_enum` (`value_ctx.v`) are generic in the layout (bytes
  before and after the payload, from which the discriminator reads the variant);
  `gopen_rec` (`gmb_cells.v`) likewise.
- **`GetDiscr m e`** (`lang/lang.v`): head step `GetDiscrS` to `discr_expr d l` (pure;
  per branch `let: "z" := Load Na1Ord (MInt it) #(l +ₗ off)` and range tests;
  `DInvalid` is stuck), so no new race or adequacy case (noted in `races.v`). WP rules
  (`lang/proofmode.v`): `wp_get_discr_gen` (a reader and a resource for each load),
  `wp_get_discr` (owned chunks, `chunks_own`/`chunks_reader`), `wp_get_discr_guarded`
  (guarded chunks, `£(2 * d * discr_depth)`); test `test_get_discr` in
  `minirust_tests.v`.
- **Sequential layouts** (`syn_type.v`) restated: `seq_tuple` (align 1), `seq_enum` (tagger
  `[(0, enum_tag n, i)]`, payload at the tag size, `seq_discr n` one branch), with
  `decode_seq_enum`/`decode_discr_seq`/`discr_depth_seq`; `frepr_seq_enum_iff`
  (`bytes_layout.v`) has the former shape, so `syn_bytes_sum`, `syn_fbytes_sum`,
  `cbytes_sum` keep their statements.
- **Case rules** use `case: GetDiscr (syn_mty (Σ! 𝔄l)) p of …` (`place_sum.v`,
  `place_deep.v`, `place_pshr.v`, `place_res.v`), through `wp_get_discr_sum`
  (`bytes_layout.v`) and `wp_get_discr_sum_guarded` / `wp_get_discr_shr_view`
  (`place_pshr.v`); examples `get_some_first.v`, `pcell_parts.v`, `place_pshr.v` updated.

## Outcome: L2a (structs: layouts and types; branch `proto/layout-l2`)

- **Layouts** (`lang/minirust.v`): `struct_layout` (`SL offs size align`), `sl_mty`,
  `sl_wf` (decidable), `c_layout` (`repr(C)`, aligned offsets, `lcm` alignment, size rounded
  up; `c_layout_wf`), `packed_layout` (`repr(packed)`), `struct_lay L ms` (the effective
  layout: `L` if `sl_wf L ms`, else `packed_layout ms`), `struct_mty`. The fallback is the
  packed layout, not `c_layout`: it depends only on the field *sizes*
  (`struct_lay_sizes`), so `syn_bincl` needs no alignment conjunct. Alignment conditions in
  `mty_wf` are left for L5 (with the alignment UB); `c_layout` computes aligned layouts
  for the examples. Tests (`minirust_tests.v`): `c_layout [i32; u8; i32] = SL [0; 4; 8] 12
  4`, and the well-formedness of `c_layout` and of a reordering layout, by computation.
- **Syntactic type** `structₛ L 𝔄l` (`prophecy/syn_type.v`, last constructor): `plist`
  interpretation, `syn_mty = struct_mty L (syn_mty <$> 𝔄l)`, structural `syn_val`/`syn_fval`;
  `struct_consₛ`/`struct_mapₛ`. `bytes_layout.v`: `struct_offs`, `struct_size`,
  `struct_fields`, `syn_fbytes_struct` (plain padding, `fields_fbytes` at the offsets),
  `syn_bincl_struct_map`.
- **Contents** (`own.v`): `pad_own`, `gconts_union`, `gcont_tuple` (the contents of a tuple
  of any layout: its fields at their offsets and the padding; via `frepr_union_l` and
  `gcells_disj_list` of `gcont.v`), `fields_bytes_own`, `bytes_own_struct`.
  `value_ctx.v`: `val_cells_tuple`, `fields_val_own`, `val_own_struct`,
  `type_mk_struct_val_instr`.
- **Types** (`typing/struct.v`): `fields_nil_ty`, `fields_cons_ty`, `fields_ty`
  (`type (Π! 𝔄l)`, ghost parts), `struct_of L`, `struct_ty L tyl := struct_of L (fields_ty
  tyl)`, `cstructₛ`/`cstruct_ty`; `Copy`, `Send`, `SendUpd`, `Sync`, `ResOwn`, resolution,
  `struct_subtype`/`struct_eqtype` (along `struct_mapₛ`), non-expansiveness and
  contractiveness, outlives.
- `prod`/`xprod` are untouched in L2a; L2b replaces them.

## Outcome: L2b (struct places; branch `proto/layout-l2b`)

- **Place types** (`typing/ltype.v`): `StructLty {𝔄l} (L: struct_layout) (lts: hlist lty 𝔄l) :
  lty (structₛ L 𝔄l)` replaces `ProdLty` (a nested inductive through `hlist`; induction
  principle `lty_ind'` with an `HForall` hypothesis). Refinements `prfn_struct (structₛ L 𝔄l) =
  plist prfn 𝔄l` (`prfn_fields_in`), patterns `PatStruct (list lpat)`. The node of a struct
  (`struct_node`, `fields_node`): the fields at the offsets of the effective layout
  (`struct_offs`) and the padding (`pad_own`); its view (`view_struct`) guards the padding.
  Folded type `struct_ty L (hmap lty_fold lts)`.
- **Unfolding**: `struct_ofty_unfold_own`/`_core` (`ltype_eq` of `OfTy (struct_ty L tyl)` and
  `StructLty L (hmap OfTy tyl)`), `struct_ofty_unfold_uniq`/`struct_ofty_fold_uniq` (behind a
  unique borrow, switching the body of the borrow). Rules: `tctx_unfold_oplace_struct`,
  `tctx_fold_oplace_struct` (`place_own.v`), `type_unfold_vplace_struct_instr`,
  `type_fold_vplace_struct_instr` and the `oplace` variants (`place_puniq.v`),
  `tctx_unfold_oplace_res_struct` (`place_res.v`).
- **Contexts** (`typing/lpath.v`): a zipper step `PField {𝔅 𝔄lb 𝔄 𝔄la} L (lb: hlist lty 𝔄lb)
  (K: pctx 𝔅 𝔄) (la: hlist lty 𝔄la) : pctx 𝔅 (structₛ L (𝔄lb ++ 𝔄 :: 𝔄la))`, whose hole is
  field `length 𝔄lb` at offset `struct_off L (𝔄lb ++ 𝔄 :: 𝔄la) (length 𝔄lb)`; the siblings
  `lb`, `la` are kept literally, so `pctx_own` of a field is the ownership of the siblings
  (`fields_own`), of the hole's context and of the padding (`ltype_own_struct_field`). This
  deviates from the `hlist_set`/`fin` form proposed in §7.4: the zipper needs no lookups and
  examples write e.g. `PField L +[OfTy i32t] PHole +[]` for the second of two fields.
  Paths stay `list bool`: field `j` has the selector `fcode j = false :: replicate j true`;
  the selectors are suffix-free (`fcode_suffix_ne`), so the blocking maps of different fields
  are independent. Retyping the hole (strong writes) keeps the layout if the size does not
  change (`pctx_root_bsize`, the layout of a struct depends only on the sizes of its fields).
- The struct versions of the generic place machinery: implicit unblocking, folding back of
  simple places (`ltype_owned_bytes_unblock`), access (`pctx_acc_field`), shared views
  (`shr_pctx_view`, `type_shr_bytes_field_instr`), resolution (`lty_resolve_struct`,
  `lty_rslv_struct`, `lty_res_struct` with `fields_res`), memory of places and
  `drop_boxes` (`fields_omem`, `fields_drop`, at index-based offsets; `mem_bytes_struct`,
  `bytes_fields_pad`), views of resolved borrows (`share_view_struct`).
- `typing/place_xprod.v` is deleted. `PCellFromOwn` gives a struct of the cell and its
  permission (`pcell_pair_ty`, at `pcell_pair_layout`), and `↯ (m + n)` splits into a struct
  (`uninit_plus_struct`).
- **Examples** ported to structs at explicit `c_layout`s (`get_first`, `get_some_first`,
  `place_deep`, `new`, `function`, `place_pshr`, `place_res`, `place_rules`, `place_own`,
  `place_moved`, `pcell_parts`, `pcell_borrows`, `pcell_move`, `place_struct`). Programs
  address fields with `+ₗ #(struct_off L 𝔄l j)` (also field `0`); layouts are written as
  `c_layout [MInt i32; …]` (with literal `mty`s: a layout computed with `syn_mty <$> _`
  leaves a type class evar during `apply`, whose unification hangs). Layouts with pointers
  are symbolic (`PTR_ALIGN` is sealed), so box sizes are written `struct_size L 𝔄l`.
- Known cost: the proof of `pcell_borrows` takes ~11 minutes to check (the kernel check of
  `Qed`; `pcell_example` already took ~1.5 minutes before L2b).
- `prod_ty`, `xprod_ty` and the product isomorphisms are still there (deleted in L2c).
