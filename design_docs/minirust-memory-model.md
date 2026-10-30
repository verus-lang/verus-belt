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
