Our next aim is to make Rust more accurate, using MiniRust as a guideline.
This change will be very invasive, and we'll be more eager to delete old stuff that isn't useful anymore (e.g., most of the old program typing rules from before place types were ready).

# details

In MiniRust:
 - the memory is made of "abstract bytes" (https://github.com/minirust/minirust/blob/master/spec/mem/interface.md)
 - values are defined by an enum which allows literals, pointers, products, and sums (https://github.com/minirust/minirust/blob/master/spec/lang/values.md)


MiniRust values:

```
enum Value<M: Memory> {
    /// A mathematical integer, used for `i*`/`u*` types.
    Int(Int),
    /// A Boolean value, used for `bool`.
    Bool(bool),
    /// A pointer value, used for references and raw pointers.
    Ptr(Pointer<M::Provenance>),
    /// An n-tuple, used for arrays, structs, tuples (including unit).
    Tuple(List<Value<M>>),
    /// A variant of a sum type, used for enums.
    Variant {
        discriminant: Int,
        #[specr::indirection]
        data: Value<M>,
    },
    /// Unions are represented as "lists of chunks", where each chunk is just a raw list of bytes.
    Union(List<List<AbstractByte<M::Provenance>>>),
}
```

Abstract bytes:

```
pub enum AbstractByte<Provenance> {
    /// An uninitialized byte.
    Uninit,
    /// An initialized byte, optionally with some provenance (if it is encoding a pointer).
    Init(u8, Option<ProvenanceFrag<Provenance>>),
}
```

Right now, VerusBelt uses `val` in its memory model; type represenations are sequences of vals and values at the "root" at just the size-1 representations.

Instead, we want to move to using AbstractByte in the memory model, and MiniRust's notion of "Value" at the root. This is going to complicate things, because no longer are we going to be just reading width-1 values from memory, instead we have to read arbitrary-length sequences of abstract bytes and _decode_ them into a Value. Likewise when writing a value to memory, we have to _encode_ the value as bytes. 
MiniRust also defines encoding and decoding (which depends on the "MiniRust type" being read). Our goal is not (yet) to reproduce the encoding and decoding exactly, but to get the machinery in place,
and support pointers that span multiple bytes.

We need to:
 - Add a notion of "typed read" and "typed write" to the language semantics, where type is that of MiniRust's (https://github.com/minirust/minirust/blob/master/spec/lang/types.md). We'll call these "MiniRust types". These are not the same as Rust types, nor the same as VerusBelt semantic types or syntactic types. Notably, they are "shallow" - they do not descend past a pointer indirection. These types serve to parameterize the encoding and decoding relation.
 - Replace VerusBelt's `val` with MiniRust's Value (for "roots") and AbstractByte (for in-memory)
 - In the semantic types, replace the `ty_phys` sequence with an (optional) MiniRust value.
   + It needs to be optional because some types can't be decoded, like `PCell` (this needs a big re-thinking, we'll put this off)
   + Note that it doesn't make sense to change `ty_phys` a sequence of abstract bytes, since when the type is used a root, there's no abstract bytes. That's why we want `ty_phys` to be a MiniRust value.
     Instead, the "parent" (the own, shr bor, or uniq bor) will maintain a sequence of (fancy) abstract bytes with the requirement that those bytes can be decoded to the pointee's value.
     (This means we can remove the padding bytes from the syn representation of `xsum_ty`, for instance, since all the bytes will now just be known by the parent.)

# Fleshed-out plan (decisions 2026-10-29)

## Decisions
1. **Pointer bytes are abstract fragments.** Our `loc`s are abstract (block, offset), so a
   pointer occupies `PTR_SIZE` bytes `PtrFrag(l, i)` (`i < PTR_SIZE`), instead of integer
   addresses with provenance. Sizes are abstract for now.
2. **`PTR_SIZE` is a parameter.** Integer sizes are parametric too, via `IntType`.
3. **Functions stay as they are** (`RecV` closures), as a non-MiniRust case of `Value`.
4. **The expression language starts minimal:** typed `Load mty e`, `Store mty e1 e2`, a byte-level
   `MemCopy`, and tuple/variant construction and projection on `Value`s. There is no split into
   value and place expressions yet.
5. **Compatibility layer.** Legacy one-word operations and the new byte operations coexist so the
   build stays green; the legacy layer is deleted at the end.
6. **Old core typing rules are deleted** once the place rules make them redundant. That includes
   the pre-place rules in `borrow.v`, `product_split.v`, much of `type_sum.v`, the
   `programs_util_own` memcpy rules, and the core `&shr` rules. Examples are ported.
7. **Atomic operations may have any size** (any `mty`).
8. **Enums use a simple tag at offset 0** for now, not MiniRust's discriminator tree.

**`memcpy` copies memory to memory** and preserves the `AbstractByte`s. It does no
decode/encode round trip; a round trip is just a separate `Load` and `Store`, so there is no
typed memcpy.

## Stages (each ends with a clean build and a commit)
1. **Semantics.** Define:
   - `AbstractByte`: `Uninit`, `Init u8`, `PtrFrag loc i`, and a legacy `Word val` for
     compatibility;
   - `Value`;
   - the MiniRust type fragment: `Int(IntType)`, `Bool`, `Ptr`, `Tuple` with field offsets, and
     `Enum` with a tag at 0;
   - `encode`/`decode` with the round-trip and monotonicity laws.

   Then add `Load`, `Store` and `MemCopy` to `lang.v`, with the heap holding bytes. Legacy
   `Read`/`Write`/`CAS` act on `Word` bytes, and `Alloc` gives `Uninit`.
2. **Heap and program logic.**
   - A byte points-to `l ↦b bs`, with the legacy word points-to defined on top of it.
   - WP rules: typed `Load` (`decode mty bs = Some v`), `Store` (writes `encode mty v`), and
     `MemCopy` (byte-preserving).
   - Race detection over byte ranges.
   - Adequacy is preserved.
3. **Type record.**
   - `ty_mty`: a shallow MiniRust type, determined by the syntactic type.
   - `ty_val : ~~𝔄 → option Value` replaces `ty_phys`.
   - Parents (`own_ptr`, `&uniq`, `&shr`) own existential bytes `bs` with
     `decode (ty_mty ty) bs = ty_val x`.
   - Int types get `IntType` sizes.
   - Products and sums get MiniRust layouts, so the sum padding in `~~` goes away.
4. **Places.**
   - A leaf owns a byte range; `pctx` offsets are byte offsets.
   - Leaf read and write are typed `Load`/`Store` of the leaf's `mty`.
   - Copying a place is `MemCopy`.
5. **Delete** the legacy word layer and the redundant core typing rules, and port the examples.
6. **Later:** redesign `pcell` (`ty_val = None`, fancy bytes with cells).

## Outcome: stages 1–2 (merge `3801e8a`)

**Semantics** (`lang/minirust.v`):
- `PTR_SIZE` is sealed (abstract, `0 < PTR_SIZE`); `IntType`.
- `Value := VInt | VBool | VPtr | VTuple | VVariant`.
- The type fragment `mty := MInt | MBool | MPtr | MTuple fields size | MEnum variants tag size`,
  with the tag at offset 0.
- `AbstractByte W := Uninit | Init | PtrFrag l i | Word w`.
- `encode_value`/`decode_value`, with the laws `length_encode_value`, `decode_encode_value` and
  `decode_value_mono`. These are axiom-free.

**`lang.v`:**
- The heap holds `abyte`. Legacy words are `word_to_byte v`, with poison as `Uninit`.
- `val` gains `MLitV Value`.
- New expressions: `Load`, `Store`, `MemCopy` (byte-verbatim), `MkTuple`/`Proj`/`MkVariant`/
  `VariantTag`/`VariantData`, and `ToLit`/`OfLit`.

**Program logic:**
- A byte points-to `l ↦b{q} bs`.
- WP rules: `wp_load_sc/na`, `wp_store_sc/na`, `wp_memcopy`, `wp_alloc_bytes`, `wp_free_bytes`.
- Race detection over byte ranges.

**Deviations:**
- The ghost heap has two regions, legacy words (the cell map, `val`-valued) and bytes, related by
  `phys_rel`. Locations move between them without a step (`wp_words_to_bytes` /
  `wp_bytes_to_words`), because the cell-untethering lemmas need a `val`-valued cell map.
- Closures stay a `val` case.

**Open for later stages:**
- typed CAS;
- guarded (shared-borrow) byte loads;
- proofmode tactics.

## Outcome: stage 3

Stages 3a–3c are done. Stage 3d (deleting `ty_phys`) is not; see below.

**Syntactic MiniRust types and values** (`prophecy/syn_type.v`):
- `Zₛ` is now a notation for `intₛ isize`, where `intₛ (it : IntType)` is a new
  syntactic type with `~~(intₛ it) = Z`.
- `syn_mty : syn_type → mty` maps each syntactic type to its shallow MiniRust type:
  - `intₛ it` to `MInt it`, `boolₛ` to `MBool`;
  - `locₛ`, `at_locₛ`, `at_clocₛ`, `uniq_borₛ` and `exec_funₛ` to `MPtr`;
  - products (`prodₛ`, `Π!`) to `seq_tuple`: an `MTuple` whose fields come one after
    the other, with no padding (sizes are abstract and there is no alignment);
  - `Σ! 𝔄l` to `seq_enum`: an `MEnum` with the tag `enum_tag n` at offset 0 and the
    data right after it. The tag is one byte for up to 256 variants. `Option<i32>`
    comes out as `MEnum [MTuple [] 0; MInt i32] (IntTy false 1) 5`, the same as
    `opt_mty` in `minirust_tests.v`;
  - `uninitₛ n` and `pcellₛ n` to `MTuple [] n` (padding);
  - every other syntactic type to the zero-sized `zst_mty = MTuple [] 0`.
- `syn_val : ~~𝔄 → option Value` gives the MiniRust value. It is `None` for integers
  out of range (`decide (int_in_range it z)`), for closures (`exec_funₛ`) and for
  cells (`pcellₛ`), and for any product or sum that contains one of these. It ignores
  the legacy padding component of `~~(Σ! 𝔄l)`.
- The byte size is `syn_bsize 𝔄 := mty_size (syn_mty 𝔄)`.
- Laws: `syn_mty_wf 𝔄 : mty_wf (syn_mty 𝔄)`;
  `syn_val_wf x v : syn_val x = Some v → val_wf (syn_mty 𝔄) v`;
  `syn_abstract_val_eq` (the counterpart of `syn_abstract_phys_eq`, for `Send`).
- `Isoₛ` has two new fields:
  - `syn_iso_bsize_eq : syn_bsize 𝔄 = syn_bsize 𝔅`;
  - `syn_iso_bytes x bs : decode_value (syn_mty 𝔄) bs = syn_val x ↔
    decode_value (syn_mty 𝔅) bs = syn_val (f x)`.

  An isomorphism has to preserve byte representations, not MiniRust types:
  `() * 𝔄 ≅ 𝔄` and `𝔄 * Π! 𝔅l ≅ Π! (𝔄 :: 𝔅l)` have different `mty`s. The new fields
  are proved for all existing instances: id, compose, cons_prod, unit, left/right id,
  `prod_assoc` (`prod_assoc_bytes`), the uninit split and unit, and the list example.
  The proofs use the helper lemmas `decode_seq_tuple`, `decode_prod_unit_l/r`,
  `decode_prod_cons`, `decode_assoc_l/r` and `decode_pad_pair`.

**Type record** (`typing/type.v`):
- New fields: `ty_mty : mty` and `ty_val : ~~𝔄 → option Value` (`ty_val` takes no
  `tid`).
- New laws: `ty_mty_eq : syn_mty 𝔄 = ty_mty` and
  `ty_val_eq x : syn_val x = ty_val x`. They mirror `ty_size_eq2` and `ty_phys_eq2`.
- Every type definition sets
  `ty_mty := syn_mty _; ty_val := syn_val; ty_mty_eq := eq_refl; ty_val_eq _ := eq_refl`,
  so no `Program` obligation was added and none was renumbered.
- Derived definitions and lemmas:
  - `ty_bsize ty := mty_size ty.(ty_mty)`;
  - `ty_bytes ty x bs := length bs = ty_bsize ty ∧ decode_value ty.(ty_mty) bs = ty.(ty_val) x`;
  - `ty_mty_wf`, `ty_val_wf` (`ty_val x = Some v → val_wf ty_mty v`), `ty_bsize_eq`;
  - `ty_mty_same`, `ty_val_same`, `ty_bytes_same` (types of the same `𝔄` agree);
  - `ty_bytes_decode`, `ty_bytes_encode`, and `ty_bytes_mono` (monotone under
    `bytes_le`).
- `ty_size` still counts legacy words. The law `mty_size ty_mty = ty_size` from the
  plan cannot hold yet: `own_ptr` is 1 word but `PTR_SIZE` bytes, and an `i32` is 1 word
  but 4 bytes. It becomes true when `ty_size` is redefined as the byte size in stage 4.
  Until then, the byte size is `ty_bsize`.

**Integers** (`typing/int.v`):
- `int_ty (it : IntType) : type (intₛ it)`, with the laws `int_ty_mty`, `int_ty_val`
  and `int_ty_copy`.
- `int` is a notation for `int_ty isize`; the legacy arithmetic rules are stated for
  it.
- `minirust.v` defines `i8 … i64` and `u8 … u64`.

**Parents own bytes** (`typing/own_bytes.v`):
- `own_bytes n ty : type (at_locₛ 𝔄)` is the target form of `own_ptr`. Its ownership is
  `bytes_own ty l x := ∃ bs, l ↦b bs ∗ ⌜ty_bytes ty x bs⌝`, plus
  `freeable_sz n (ty_bsize ty) l`, plus `▷ ty_gho_own`. Its sharing predicate is
  structural, like that of `own_ptr`.
- All laws of the type record are proved, and so is `NonExpansive`.
- Rules:
  - `wp_own_bytes_load`: a typed `Load (ty_mty ty)` returns `MLitV v` when
    `ty_val x = Some v`;
  - `wp_own_bytes_store`: a typed `Store` of `ty_val y` turns the box of `x` into a box
    of `y` and gives back `▷ ty_gho_own x`;
  - `wp_own_bytes_new`: `Alloc` followed by `Store`;
  - `wp_own_bytes_delete`;
  - `own_bytes_gho_intro`.

**Why `own_ptr`, `&uniq` and `&shr` are not switched, and how the legacy form is
bridged:**
- The two forms differ physically. A legacy word is the single byte `Word v`. The
  MiniRust encoding is `Init`/`PtrFrag` bytes, and its size is different
  (`ty_bsize`, not `ty_size`).
- So a ghost bridging lemma "words of `ty_phys` ↔ bytes decoding to `ty_val`" is
  impossible. Converting means a real `Store`, and possibly a re-allocation.
- The place machinery (`ltype.v`, `place_*.v`) opens `own_ptr`, `&uniq` and `&shr` to
  get `l ↦!∗ ty_phys x` / `#↦!∗` with cells, and reads and writes leaves with the
  one-word operations. Switching the parents is therefore exactly stage 4.
- The least disruptive path was to add the byte form beside the legacy one:
  - `own_bytes` beside `own_ptr`;
  - `ty_bytes` as the parent relation;
  - `Isoₛ`'s `syn_iso_bytes`, so that `mod_ty` will transport `ty_bytes`.

  The legacy types are unchanged.
- No byte variants of `&shr` and `&uniq` yet:
  - `&shr` needs guarded byte loads, which stage 2 left open;
  - `&uniq` is entangled with the place machinery.

  Subtyping for `own_bytes` is also missing: `type_incl` relates `ty_phys`, and would
  need a `ty_bytes` law. All of this is for stage 4.

**What remains of `ty_phys`, `syn_phys` and the sum padding:**
- `ty_phys`, `syn_phys` and the padding component `list val` of `~~(Σ! 𝔄l)` all stay.
  They are the legacy word representation that the place machinery, `type_incl`,
  `Send` and the fixpoints use.
- They can only be removed together with the word layer: stage 4 for the places,
  stage 5 for the rest. `syn_val` already ignores the padding.

**Tests** (`typing/examples/own_bytes.v`):
- `test_box_pair_swap`: `Box<(i32, i32)>`, with layout
  `MTuple [(0, i32); (4, i32)] 8`. It loads the pair, stores the swapped pair and loads
  it again.
- `test_box_option`: `Box<Option<i32>>`. It does `Box::new(Some(5))`, loads (giving
  `VVariant 1 (VInt 5)`), stores `None`, frees the box and returns the loaded value.
- `Print Assumptions` for both shows only `functional_extensionality_dep`.
- At the syntactic level:
  - `syn_mty_wf` and `prod_assoc_bytes` are closed;
  - `syn_val_wf` and `isoₛ_cons_prod` use `functional_extensionality_dep` (through
    `semi_iso'`/`fun_ext`);
  - `syn_abstract_val_eq` also uses `eq_rect_eq` (through `dependent destruction`, as
    `syn_abstract_phys_eq` already does). It is not used yet.
