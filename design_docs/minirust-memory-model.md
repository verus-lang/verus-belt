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

## Outcome: stage 4

> **Note (stage 5).** The file names in this section are those at the time. The legacy
> place files were deleted later and the `b`-files renamed; see "Outcome: legacy place
> layer deleted" for the mapping.

Stage 4 is done as a parallel byte version of the place machinery. The legacy word
versions stay in the build next to it, unchanged, until stage 5 deletes them. Every byte
example has a `Qed` and `Print Assumptions` shows only `functional_extensionality_dep`.
No new axioms were added; the new heap and adequacy lemmas are closed.

### Decisions

1. **Byte versions next to the legacy files, not a switch in place.** Switching
   `own_ptr`, `&uniq`, `&shr` and the place files in place would break every legacy
   example and every legacy core rule (`borrow.v`, `product_split.v`, `type_sum.v`,
   `programs_util_own`, `function.v`) at once. All of these read and write one-word cells,
   and stage 3 showed that there is no ghost bridge between words and bytes. So each place
   file has a `b`-prefixed copy that was ported mechanically and then fixed by hand:
   - `ltype` → `bltype`, `lpath` → `blpath`, `pctx_acc` → `bpctx_acc`, `vplace` → `bvplace`;
   - `place_own` → `bplace_own`, `place_shr` → `bplace_shr`, `place_resolve` → `bplace_resolve`;
   - `place_puniq` → `bplace_puniq`, `place_sum` → `bplace_sum`, `place_deep` → `bplace_deep`;
   - `uniq_util` → `buniq_util`.

   The byte copies reuse the generic parts of the legacy files: the encoding of depths,
   `uniq_cell`, `place_rfn_rel`, the patterns, the borrow tokens and `pctx` itself.
   - Definitions that changed get a `b` prefix (`bofty_owned`, `buniq_body`, …). This is
     not cosmetic: when two names were the same, typeclass search looped on the legacy
     `Persistent` instances.
   - Lemma names are kept, so the legacy and byte versions are told apart by the import.
   Stage 5 deletes the legacy files and renames the byte ones.

2. **The parents own bytes.** There are three byte types:
   - `own_bytes n ty` (stage 3), the box.
   - `&uniqb{κ} ty` (`buniq_bor.v`). This is `&uniq` with the payload of the body being
     `cbytes ty x l := bytes_own ty l.1 x`, that is, `∃ bs, l ↦b bs ∗ ⌜ty_bytes ty x bs⌝`.
   - `&shrb{κ} ty` (`shr_bytes.v`). Its ownership is `@[κ] &&{↑NllftG; g+1}&&> bytes_own ty l x`,
     together with `ty_shr` and `ty_gho_pers` of `ty`. Because the guard covers
     `bytes_own` (with the `∃ bs` inside it), a shared leaf of a place (`ShrBlocked`) and a
     shared reference have the same shape.

   `ty_bytes ty x bs` now means "`ty_val x = Some v` and `bs` decodes to `v`". This needs a
   MiniRust value, so a type without one (out-of-range integers, closures, cells) has no
   bytes.

3. **Guarded byte loads use a bank of guarded reads** (`lang/heap.v`), which mirrors the
   read bank of the legacy `non_atomic_map`.
   - During a non-atomic read of guarded bytes, the reader puts the guard `G` (with its
     credits) into a bank entry for the range being read.
   - The physical lock states of the byte region are those of the authoritative heap plus
     the number of entries that cover each location (`bank_rel`, `bank_wf`).
   - A writer owns the full points-to of its range. It opens the guards of the entries to
     show that none of them overlaps that range (`bbank_disj`).

   The new rules are in `lang/lifting.v`:
   - `wp_load_sc_guarded`;
   - `wp_load_na_guarded(_gen)`;
   - `wp_memcopy_guarded(_gen)`.

   The general (`_gen`) form takes a guard of any `P` with `□ (P -∗ ∃ q bs, ⌜Ψ bs⌝ ∗ l ↦b{q} bs ∗ (l ↦b{q} bs -∗ P))`.
   This is what `&shrb` and shared leaves need, because their bytes are existential.

   Cost: the byte WP rules that write or free memory now require `↑naN ⊆ E`, and their
   users were adapted.

4. **Root values.** `p ◁ᵥ ty` (`value_ctx.v`) is a `TCtx_sem` element, so no new case is
   needed in the type context. It means that `p` evaluates to `MLitV w` with
   `ty_val x = Some w`, together with `⧖d` and `ty_gho_own x d d`.
   - Pointers are `MLitV (VPtr l)`. Addresses come from `ToLit`, and borrows return
     `OfLit (…)`, so a borrow or reborrow returns a MiniRust pointer value.
   - The value rules are:
     - `type_val_int_instr`, `type_val_unit_instr`, `type_mk_variant_val_instr`;
     - `type_load_own_bytes_copy_instr`, `type_store_own_bytes_instr`,
       `type_load_shr_bytes_copy_instr`;
     - `type_shr_bytes_fst/snd_instr`, field projections of `&shrb` that are a pointer
       offset (in `bplace_shr.v`);
     - `type_resolve_val_instr`.
   - `bvplace.v` turns `◁ᵥ &uniqb` / `◁ᵥ own_bytes` into value-rooted places and back.

5. **Sizes and offsets are in bytes and syntactic.**
   - `lty_size lt := syn_bsize 𝔄`.
   - In `pctx_size`, `PSum` is `tag_size 𝔄l + sum_max 𝔄l`, and `POwn`, `PUniq` and `PShr`
     are `PTR_SIZE`.
   - The `PSnd` offset is the byte size of the first field.
   - The `PSum` payload is at offset `tag_size 𝔄l`, the size of the tag `IntType`.
   - `pctx_expr` loads each pointer on the path with a typed `Load Na1Ord MPtr`.
   - `ty_size` (in words) is unchanged and still used by the legacy layer.

6. **Leaf operations.**
   - **Reading a leaf** is a typed `Load` of `ty_mty ty`. Below shared references it is a
     guarded typed `Load`.
   - **Writing a leaf** is a typed `Store`. The writing rule requires
     `ty_bsize ty' = ty_bsize ty`.
   - **Moving out of a leaf** is a typed `Load`, which leaves `↯ (ty_bsize ty)` with the
     old bytes.
   - **Copying values of any size** below unique borrows is the byte-level `MemCopy` (see
     `bplace_deep.v`); there is no typed memcpy.
   - **Case analysis** reads the tag with
     `case: ToLit (Load Na1Ord (MInt (sum_tag 𝔄l)) (address of the leaf))`.
   - **Assigning a variant** is not a separate rule any more. It is a variant value
     (`MkVariant`) written with a typed `Store`.

### Rule families ported to bytes

- **Model** (`bltype.v`, `blpath.v`, `bpctx_acc.v`, `bvplace.v`):
  - place types and their ownership;
  - fold/unfold;
  - the leaf access below borrows (`vroot_acc`, `wp_pctx_vptrs`);
  - root-value places.
- **Owned places** (`bplace_own.v`):
  - own ↔ oplace;
  - product and box unfold/fold;
  - borrow (`&mut` of a leaf);
  - read, move, write;
  - unblock.
- **Shared leaves** (`bplace_shr.v`):
  - `type_share_oplace_instr`;
  - `type_read_oplace_shr_instr` (guarded load);
  - `unblock_tctx_oplace_shr`;
  - the `&shrb` field projections.
- **Resolve and drop** (`bplace_resolve.v`):
  - `lty_omem` on bytes;
  - `drop_boxes`;
  - `type_resolve_oplace_instr`, `type_drop_oplace_instr`;
  - `tctx_drop_vplace_uniq`, `type_resolve_vplace_uniq_instr`.
- **Below unique borrows** (`bplace_puniq.v`):
  - change of view;
  - product, `&uniqb` and box unfold/fold at any depth;
  - deep borrow, reborrow through a `&uniqb`, read, write, share;
  - unblock at depth;
  - `lty_rslv` and the deep resolve/drop.
- **Sums** (`bplace_sum.v`, `bplace_deep.v`):
  - case analysis on owned and deep places (`type_case_oplace`, `type_case_vplace_deep`,
    `type_case_oplace_deep`);
  - folds.
- **Byte copies below unique borrows** (`bplace_deep.v`):
  - `type_memcpy_vplace_deep_instr` and `type_memcpy_oplace_deep_instr`;
  - `type_memcpy_copy_from_vplace_deep_instr`.

### Still legacy (stage 5)

- `place_res*`: resolution-carrying places. Because of this, `res_pair` is not ported.
- `place_pshr.v`: places below shared references, with shared views and reads through
  `&shr` chains. Its shared views are built on the cell-based structural sharing
  predicates, so they need to be redesigned on byte guards.
  - The byte `get_snd` therefore reads through `&shrb` values and a field projection
    instead.
  - Also still legacy:
    - `shr_pctx_split` and `tctx_shr_place` (`place_shr.v`);
    - the copies of `place_deep.v` below shared references.
- `place_memcpy.v`: the owned-place copies. On bytes they are replaced by typed
  `Load`/`Store` of any size and by `MemCopy`.
- `Π!` products (`tctx_(un)fold_oplace_xprod`). The MiniRust types of `Π! (𝔅 :: 𝔅l)` and
  `𝔅 * Π! 𝔅l` differ, even though their bytes are the same.
- Variant assignment (`type_sum_assign/unit/memcpy_*`). It is replaced by
  `type_mk_variant_val_instr` and a `Store`.

### Examples on bytes

The examples are function bodies (`typed_body`) with a return continuation that takes a
`◁ᵥ` value. They do not use `typed_val`/`fn` types, because `fn` still takes legacy boxes.
The Qed times below are from `coqc -time`.

| Example | Qed time | File |
|---|---|---|
| `set_snd_b_type` | 13 s | `examples/bplace_own.v` |
| `box_pair_b_type` | 16 s | `examples/bplace_own.v` |
| `get_first_b_type` | 6 s | `examples/bget_first.v` |
| `get_some_first_b_type` | 17 s | `examples/bget_some_first.v` |
| `swap_snd_b_type` | 17 s | `examples/bplace_deep.v` |
| `get_snd_b_type` | 6 s | `examples/bget_snd.v` |

Notes on the examples:
- `box_pair_b_type` borrows `&mut *b.0` through the unfolded inner box, because the place
  rules (byte and legacy alike) cannot unfold a box that is the whole referent of a unique
  borrow (`pctx_uend`). The legacy version used a core deref rule instead.
- In `get_some_first_b_type` the tag is read by a typed `Load`, and the result is a
  `MkVariant` value.
- In `swap_snd_b_type` both copies are `MemCopy`, below two `&uniqb`. The result box is
  passed in uninitialized, because there is no byte `new` rule yet.
- `get_snd_b_type` does guarded typed loads through `&shrb`.

### Left for stage 5

- Delete the legacy word layer:
  - `ty_phys`, `syn_phys`, the sum padding, `↦!∗` cells;
  - the legacy place files and the core rules listed in decision 6 of the plan.
  Then rename the `b`-files and redefine `ty_size` as the byte size. That turns
  `cloc` into `loc`, because the cells are always empty for bytes.
- Move function types (`fn`, `type_fn`, `type_call`) to `◁ᵥ` arguments and results.
- Add a byte `new` rule.
- Add subtyping for `own_bytes`, `&uniqb` and `&shrb`. This needs a `ty_bytes` law in
  `type_incl`.
- Add shared places on bytes (`place_pshr`), resolution places (`place_res*`) and `Π!`
  products.
- Redesign cells (`pcell`, ghost cells) as fancy bytes (stage 6 of the plan).

## Outcome: stage 4f

> **Note (stage 5).** The file names in this section are those at the time. The legacy
> place files were deleted later and the `b`-files renamed; see "Outcome: legacy place
> layer deleted" for the mapping.

Stage 4f ports the remaining rule families of the place machinery to bytes, next to the
legacy versions, as in stage 4. `pcell` (with `ra`, `protocol` and the pcell examples)
stays on the legacy layer by decision of the user (2026-10-30).

### 1. Shared places on bytes (`typing/bplace_pshr.v`)

The model (`ShrLty`, `PShr`, `lty_vin`) was already in `bltype.v`/`blpath.v`. The new file
has the shared views and the rules.

- **Shared view on byte guards.** `shr_view κ ty y d g tid l` is the ownership of
  `&shrb{κ} ty` without its laters: a guard of `cbytes ty y l` (the existential bytes), the
  sharing predicate and the persistent predicate. `shr_pctx_view` pushes it through any `K2`:
  - fields split the guard with `cbytes_pair`;
  - a sum at its variant gives the guard of its payload (`cbytes_sum`);
  - `POwn`, `PUniq` and `PShr` step through the structural sharing predicates of
    `own_bytes`, `&uniqb` and `&shrb`.

  The pointers on the path are loaded by `wp_pctx_sexpr`, with guarded typed loads of `MPtr`
  (`wp_load_ptr_guarded`, an instance of `wp_load_na_guarded_gen`) from the guards of their
  bytes (`pctx_sguards`).
- **Two roots.**
  - `p ◁ₗ ShrLty (K2[lt]) κ`: the shared reference itself is a root value (e.g. an
    argument `x: &T`). The address of the hole is `pctx_expr K2 (ToLit p)`
    (`wp_pshr_open_root`).
  - `p ◁ₗ K1[ShrLty (K2[lt]) κ]`, with `PctxNoShr K1` and `PctxVRoot K1`: below a root box
    or unique borrow, at any depth. The address is
    `pctx_expr K2 (ToLit (Load Na1Ord MPtr (pctx_vexpr K1 p)))`. Phase 1 (`wp_pshr_open`) is
    the access of `bpctx_acc.v` to the `ShrLty` leaf, in `Owned` or `Uniq` mode. It loads the
    pointer from the bytes of the leaf (an owned load, after opening the innermost borrow
    in `Uniq` mode), copies the persistent ownership of the `&shrb`, and closes the access
    with the same leaf.
- **No `Skip`.** All credits come from the first program step of the instruction
  (`pshr_cred D + 4(D+1) ≤ advance_credits D`, `pshr_cred_step`). The byte copy below a
  shared reference takes a second batch from the copy step itself.
- **Rules** (each for both roots, with `oplace` instances through `POwn n K`):
  - (a) Change of view.
    - `tctx_change_vplace_shr` at the root, with no step.
    - `type_change_vplace_shr_instr` below `K1`, an instance of `type_change_vplace_instr`.
    - `type_(un)fold_vplace_shr_instr`, which converts between `OfTy (&shrb{κ} ty)` and
      `ShrLty (OfTy ty) κ`.
  - (b) `type_read_vplace_pshr(_root)_instr`: reads a `Copy` leaf of any size with a
    guarded typed `Load (ty_mty)`. The result is `v ◁ᵥ lty_fold lt`, and the place is
    unchanged. The old restriction to size 1 is gone.
  - (c) `type_share_vplace_pshr(_root)_instr`: `OfLit (address)` gives
    `v ◁ᵥ &shrb{pctx_slft K2 κ} (lty_fold lt)`.
  - (d) `type_case_vplace_pshr(_root)`: reads the tag with a guarded typed `Load` of
    `MInt (sum_tag 𝔄l)`. Branch `i` gets the view `K2[SumLty tyl i (OfTy (tyl +!! i))]`.
  - (e) Resolving and dropping.
    - `lty_rslv_shr`: a `ShrLty` is a leaf, for `type_drop_oplace_deep_instr` and
      `resolve_tctx_cons_oplace_deep`.
    - `tctx_drop_vplace_shr`: drops a root shared place.
  - Copies: `type_memcpy_copy_from_vplace_pshr(_root)_instr` (and the `oplace` instance)
    copy a `Copy` leaf below `PShr` into a box with a guarded `MemCopy`
    (`wp_memcopy_guarded_gen`). The old contents of the box are resolved.
- **Field access below shared references.** `shr_pctx_split`/`tctx_shr_place` are not
  ported as separate rules. They are subsumed by `type_share_vplace_pshr_root_instr` with a
  fields-only `K2`, which is an instruction because the address is an offset computation,
  and by `type_shr_bytes_fst/snd_instr` (stage 4).

Examples (`typing/examples/bplace_pshr.v`). Each has a `Qed`, and `Print Assumptions` shows
only `functional_extensionality_dep`. The Qed times are from `coqc -time`.

| Example | Root | Qed |
|---|---|---|
| `get_snd_pb_type` (`( **x).1`, `x: &&(i32,i32)`) | the `&shrb` value | 1.1 s |
| `get_boxed_pb_type` (`*( **b).1`, `b: Box<&(i32, Box<i32>)>`) | box (`K1 = POwn`) | 2.6 s |
| `get_or_zero_pb_type` (`match **b`, `b: Box<&Option<i32>>`) | box | 5.5 s |
| `first_ref_pb_type` (`&( **x).0`, `x: &mut &(i32,i32)`, then resolve `x`) | `&uniqb` value (`K1 = PUniq`) | 6.0 s |

### 2. Resolution places on bytes (`typing/bplace_res*.v`)

The model (`OfRes`, `ResUniqLty`, `res_leaf`, `lty_view`, `view_leaf`) was already in
`bltype.v`. The five legacy files are ported next to the legacy ones:

- `bplace_res.v` (`place_res.v`). It covers the conversions of resolved leaves:
  - `tctx_oplace_res_to_ofty`, for `ResOwn`;
  - `tctx_unfold_oplace_res_prod`, which splits the bytes with `cbytes_pair`;
  - `tctx_unfold_oplace_res_own`, for `own_bytes`;
  - `tctx_unfold_oplace_res_shr`;
  - `type_oplace_res_uniq_to_shr_instr`, which re-reads `OfRes (&uniqb{κ} ty)` as
    `ShrLty (OfTy ty) κ`, through `resolve_uniq_body` on bytes.

  It also covers case analysis on resolved sums (`type_case_oplace_res`, a typed `Load`
  of the tag) and folding them back.
- `bplace_res_view.v`: the laws of views and `lty_share_view`, which shares a place in a
  borrow into its view. On bytes the view of an unblocked leaf is a guard of its bytes
  (`leaf_share_view`), and the view of a pointer is a guard of its pointer bytes
  (`ptr_cell_view`).
- `bplace_res_rslv.v`: `lty_res` and its instances, together with the rule
  `type_resolve_oplace_res_instr` (`skipn k`). The instances are:
  - `lty_res_id`, `lty_res_impl`, `lty_res_ofty`, `lty_res_copy`;
  - `lty_res_prod`, `lty_res_own`, `lty_res_sum`;
  - `lty_res_uniq_leaf`, `lty_res_uniq_cpd`.
- `bplace_res_ops.v`: the operations below `ResUniqLty`. It has the access
  `view_pctx_acc`, and these rules:
  - `type_read_oplace_res_(leaf_|shrblk_)instr`: a guarded typed `Load` of a `Copy` leaf
    of any size, through `wp_load_shr_view`. The address is
    `pctx_expr K2 (ToLit (Load Na1Ord MPtr (pctx_expr K (ToLit p))))`. There is no
    `Skip`: the first step gives the credits.
  - `type_share_oplace_res_instr`.
  - `unblock_tctx_oplace_res` and `unblock_tctx_oplace_res_shr`.
  - `type_drop_oplace_res_instr`.
  - `tctx_fold_oplace_res_uniq_leaf`.
- `bplace_res_copy.v`: `type_memcpy_copy_from_oplace_res_instr`, a guarded `MemCopy`
  of a `Copy` leaf in a view into a box. The old contents of the box are resolved. The
  first step gives the credits for the address and the copy step the rest.
- New in `own_bytes.v`: `own_bytes_res_own`, an instance of `ResOwn`, and
  `own_bytes_resolve_keep`.

**Not ported: folding a resolved borrow with a compound referent.** This covers
`lty_view_fold`, `tctx_fold_oplace_res_uniq` and `type_fold_oplace_res_uniq_meta_instr`.
- The legacy fold combines the guards of the cells of the components into a guard of the
  cells of the whole (`guard_cells_app_combine_fancy`, through `guards_and_point`).
- On bytes the guarded resource is `cbytes ty x l = ∃ bs, l ↦b bs ∗ ⌜ty_bytes ty x bs⌝`.
  The bytes are existential, so it is not a point property (`point_prop`), and two
  guards of adjacent existential byte ranges cannot be combined into a guard of their
  separating conjunction.
- Possible fix: shared views and `&shrb` that guard fixed bytes
  (`∃ bs, ⌜ty_bytes ty x bs⌝ ∗ guard (l ↦b bs)`, chosen when the leaf is shared, with
  `κ` alive). That is a redesign of `shr_bytes_own`, `shr_blocked_owned` and
  `view_leaf`, so it is left for later.
- Leaf referents fold as before. Compound referents stay readable through the view.

Examples (`typing/examples/bplace_res.v`). Each has a `Qed`, and `Print Assumptions` shows
only `functional_extensionality_dep`.

| Example | Qed |
|---|---|
| `res_pair_b_type`: `x: Box<(Box<i32>, &mut (i32,i32))>` is resolved, then `*x.0` and `( *x.1).0` are read; `fin(x.1) = cur(x.1)` | 8.1 s |
| `res_nested_b_type`: `x: Box<&mut &mut (i32,i32)>` is resolved while `( **x).0` is reborrowed; `( **x).1` is read; `*r = 3`; the local lifetime ends and the leaf is unblocked in the view, then read; `fin(x) = ((3, c.2), fin( *x))` | 27.0 s |

### 3. Function types on root values (`typing/bfunction.v`)

`bfn fp spec : type (exec_funₛ ℭ)` is a parallel byte version of `fn`.
- It has the same `fn_params`, now read as the types of the argument values.
- The body is typed with the arguments `w ◁ᵥ ty`, MiniRust values, instead of
  `w ◁ box ty`.
- The return continuation takes `v ◁ᵥ oty`.
- The specification `bfn_spec 𝔄l 𝔅 ℭ := ~~ℭ → predl_trans' 𝔄l 𝔅` is a predicate
  transformer on the values, not on boxes.
- Boxes are still passed when wanted, as values of type `own_bytes n ty`.
- The function value is a closure (`RecV`), so it is still typed by the legacy element
  `f ◁ bfn …`: closures have no MiniRust value (decision 3).

The notations are `bfn<p>(E; ity, …) → oty`, and the rules are:
- `type_bcall_iris'` and `type_bcall`: `call: p ql → k`, with arguments `q ◁ᵥ ty` and the
  result `ret ◁ᵥ oty`;
- `type_bletcall`;
- `type_bfnrec` and `type_bfn`;
- `bfn_resolve`.

The proofs are those of `function.v`, except for `wp_app_hasty_val`, which evaluates
the arguments as values.

Examples (`typing/examples/bfn.v`). `Print Assumptions` shows only
`functional_extensionality_dep` for the first two; `call_get_snd_type` is closed.

| Example | Qed |
|---|---|
| `get_snd_f_type`: `typed_val get_snd_f (bfn<(α, β)>(∅; &shrb{α} (&shrb{β} (i32 * i32))) → i32)` | 1.3 s |
| `first_ref_f_type`: `bfn<(α, β)>(∅; &uniqb{α} (&shrb{β} (i32 * i32))) → &shrb{β} i32` | 6.7 s |
| `call_get_snd_type`: `letcall: "r" := f ["x"]` with `f ◁ bfn …` (`type_bletcall`) | 0.7 s |

### 4. Byte `new` and subtyping (`typing/bsubtype.v`)

**Allocation.** `type_new_bytes_instr`/`type_new_bytes`: `OfLit (Alloc #n)` (for `0 < n`)
gives `v ◁ᵥ own_bytes n (↯ n)`. The uninitialized bytes represent any value of `↯ n`
(`uninit_bytes`). The new box is then initialized by a typed `Store` or a `MemCopy`.

**Subtyping.** `btype_incl ty ty' f` is `type_incl ty ty' f` together with two pure facts:
- `ty_bsize ty = ty_bsize ty'`;
- `∀ x bs, ty_bytes ty x bs ↔ ty_bytes ty' (f x) bs`.

`bsubtype` is the corresponding judgement. The parents own bytes, so a parent can be
retyped only if the bytes of its referent also represent the value at the new type.
- `subtype_bsubtype_id`: every `subtype … idₛ` between types of the same syntactic type is
  a byte subtyping (`ty_bytes_same`). This covers all lifetime subtyping.
- `own_bytes_bsubtype`: covariant, with `at_loc_mapₛ f`.
- `shr_bytes_bsubtype`: the lifetime may shorten, covariant, with `at_cloc_mapₛ f`.
- `uniq_bytes_subtype` and `uniq_bytes_bsubtype`: the lifetime may shorten, and the
  referent is invariant (`eqtype … idₛ idₛ`), as `uniq_subtype`.
- `tctx_bsubtype_val`: `p ◁ᵥ ty ⇒ p ◁ᵥ ty'`, when the MiniRust values agree. The instances
  `tctx_bsubtype_own_bytes`, `tctx_bsubtype_shr_bytes` and `tctx_bsubtype_uniq_bytes` are
  for pointers, whose values always agree.

A general `f` with different MiniRust types (e.g. `mod_ty` isomorphisms) is allowed in
`btype_incl`, which only relates the bytes (`syn_iso_bytes`), but not in
`tctx_bsubtype_val`. No `mod_ty` instance of `btype_incl` is proved yet.

Examples (`typing/examples/bnew.v`):

| Example | Qed | `Print Assumptions` |
|---|---|---|
| `swap_snd_n_type`: `swap_snd` allocating its result, `let: "c" := OfLit (Alloc #8)`, then two `MemCopy`s | 17.3 s | `functional_extensionality_dep` |
| `shorten_b_type`: `&shrb{α} (i32,i32)` returned as `&shrb{β} (i32,i32)` for `β ⊑ α` | 0.3 s | closed |

**Soundness** (`typing/bsoundness.v`). `type_soundness_b` and `type_soundness_b_closed`
are `type_soundness` for a `main` typed with `bmain_type := bfn(∅) → unit_ty`. Their
`Print Assumptions` shows only `functional_extensionality_dep`.

### 5. `Π!` products on bytes (`typing/bplace_xprod.v`)

`Π! (𝔅 :: 𝔅l)` and `𝔅 * Π! 𝔅l` have different MiniRust types: a flat `seq_tuple`, and a
pair whose second field is a tuple. Their bytes are the same, though.
- `syn_bytes_xprod_cons` proves this from `syn_iso_bytes` of `isoₛ_cons_prod` and from
  `syn_val_cons_prod_some`, which shows that one value exists exactly when the other does.
- `cbytes_xprod_cons` splits the bytes of an n-ary product into those of its head and
  those of its tail.
- `xprod_ofty_own` turns a leaf `OfTy (Π! (ty +:: tyl))` into the pair place
  `ProdLty (OfTy ty) (OfTy (Π! tyl))`. Its ownership is that of `mod_ty` of the pair.
- `tctx_unfold_oplace_xprod` and `tctx_fold_oplace_xprod` are the byte versions of the
  legacy rules: `PctxNoUniq K`, `pctx_nosum K`, the hole retyped by `pctx_retype`, and
  the value converted by `of_cons_prodₛ`/`to_cons_prodₛ`.

As in the legacy layer, this is for the owned part of a place only. Below a unique
borrow, the folded type of the referent would change, which the lender fixes.
Supporting that needs a place type for n-ary products (`ConsLty`, see "6.5 Products" of
the phase 3 design), which is not attempted.

Example (`typing/examples/bplace_struct.v`). `set_mid_b_type` takes
`struct S { a, b, c: i32 }` as `Π! +[i32; i32; i32]` in a box of 12 bytes. It unfolds
the product field by field, writes `x.b = 7` with a typed `Store`, reads `x.c` with a
typed `Load`, and drops the box. Qed 7.5 s, and `Print Assumptions` shows only
`functional_extensionality_dep`.

### What still blocks deleting the legacy layer (stage 5)

`pcell` stays on the legacy layer, with `ra`, `protocol` and the pcell examples (user
decision). These use the legacy core:
- `own_ptr`/`box`, `&shr`, `&uniq` and `fn`;
- `borrow.v`, `product_split.v`, `programs_util(_own)` and `type_new`;
- the cell map of the heap (`↦!∗` cells, `phys_rel`, the `Word` bytes, and legacy
  `Read`/`Write`/`CAS`).

So, with `pcell` kept:
- **Can be deleted.**
  - The legacy place machinery: `ltype`, `lpath`, `pctx_acc`, `vplace` and `place_*.v`,
    including `place_pshr`, `place_res*` and `place_memcpy`.
  - Their examples (`examples/place_*.v`, `get_first`, `nested_*`).
  - No byte file and no pcell file imports them. Every place rule family now has a byte
    version.
  - After that, the `b`-files can be renamed.
- **Cannot be deleted yet.**
  - `ty_phys`, `syn_phys`, the padding component of `~~(Σ! 𝔄l)`, `↦!∗` cells and the
    legacy word layer of the heap.
  - The legacy `own_ptr`/`&shr`/`&uniq`/`fn` types and the core rules listed in
    decision 6 of the plan.
  - `ty_size` cannot be redefined as the byte size, because `own_ptr` is one word.

  All of these are needed by `pcell`. They go only with the pcell redesign (stage 6:
  cells as fancy bytes, `ty_val = None`). `type_incl` and `Send` also still relate
  `ty_phys`.
- **Remaining gaps of the byte layer**, besides `pcell`:
  - folding a resolved borrow with a compound referent (see item 2);
  - `Π!` below unique borrows (see item 5);
  - `btype_incl` instances for `mod_ty` isomorphisms;
  - recursive (`fixpoint.v`) types over `own_bytes`, such as a byte `list` example;
  - typed CAS and atomics on bytes;
  - unfolding a box that is the whole referent of a unique borrow (`pctx_uend`), which
    the legacy place rules cannot do either.

## Outcome: legacy place layer deleted

Stage 5, first part. `pcell` stays on the legacy layer (user decision, 2026-10-30), so only
the legacy place machinery is deleted. Every place rule family already has a byte version
(stages 4 and 4f), and no byte file, no `pcell`/`pptr`/`ra`/`protocol` file and no kept
example imported the deleted files.

### Deleted

- Place files (`typing/`): `ltype.v`, `lpath.v`, `pctx_acc.v`, `vplace.v`, `place_own.v`,
  `place_shr.v`, `place_sum.v`, `place_resolve.v`, `place_memcpy.v`, `place_puniq.v`,
  `place_pshr.v`, `place_deep.v`, `place_res.v`, `place_res_view.v`, `place_res_rslv.v`,
  `place_res_ops.v`, `place_res_copy.v`.
- Their examples (`typing/examples/`): `get_first.v`, `place_box.v`, `nested_uniq.v`,
  `nested_deep.v`, `place_own.v`, `place_shr.v`, `place_shr_mid.v`, `place_shr_resolve.v`,
  `place_sum.v`, `place_sum2.v`, `place_resolve.v`, `place_memcpy.v`, `place_deep_box.v`,
  `place_struct.v`, `place_puniq.v`, `place_pshr.v`, `place_deep.v`, `place_deep_sum.v`,
  `place_res_gen.v`, `place_res.v`, `place_res_sum.v`, `place_res_fold.v`,
  `place_res_shr.v`, `place_res_copy.v`, `place_res_shr_end.v`, `place_res_sum_fold.v`,
  `place_res_nested_fold.v`.

### Renamed (with `git mv`)

- The byte place files take the plain names: `bltype` → `ltype`, `blpath` → `lpath`,
  `bpctx_acc` → `pctx_acc`, `bvplace` → `vplace`, and `bplace_X` → `place_X` for `X` in
  `own`, `shr`, `resolve`, `puniq`, `sum`, `deep`, `pshr`, `res`, `res_view`, `res_rslv`,
  `res_ops`, `res_copy`, `xprod`.
- `bsubtype` → `subtype` (there was no legacy `subtype.v`).
- Files whose plain name is a kept legacy file get a `_bytes` name, like `own_bytes.v` and
  `shr_bytes.v`:
  - `buniq_bor` → `uniq_bytes` (`uniq_bor.v` is the legacy `&uniq`, used by `pcell`);
  - `buniq_util` → `uniq_bytes_util` (`uniq_util.v` is used by the legacy `&uniq`, and its
    generic part by the byte files too);
  - `bfunction` → `function_bytes` (`function.v` is the legacy `fn`);
  - `bsoundness` → `soundness_bytes` (`soundness.v` is the adequacy of the legacy `fn`).
- Examples: `bplace_own` → `place_own`, `bget_first` → `get_first`, `bplace_deep` →
  `place_deep`, `bget_some_first` → `get_some_first`, `bget_snd` → `get_snd`,
  `bplace_pshr` → `place_pshr`, `bplace_res` → `place_res`, `bplace_struct` →
  `place_struct`, `bnew` → `new`, `bfn` → `function_bytes`.
- In the examples, the `_b` suffix of the example names is dropped (`get_first_b_type` →
  `get_first_type`, likewise `set_snd`, `box_pair`, `swap_snd`, `get_snd`,
  `get_some_first`, `res_pair`, `res_nested`, `set_mid`, `shorten`). The suffixes `_pb`,
  `_f` and `_n` stay: they tell apart the variants of one example.
- `_CoqProject_using_opam` was stale (it still listed `place.v`/`place_nested.v` and none
  of the byte files); its file list is now that of `_CoqProject`.

**Definitions not renamed.** Every `b`-prefixed definition still has a kept legacy
namesake, so none is renamed back:
- `bofty_owned`, `bleaf_owned`, `bleaf_node`, `bblocked_owned`, `buniq_body(γ)`,
  `buniq_gbody`, `buniq_payload`, `buniq_lender`, `buniq_restored`, `buniq_persγ`,
  `buniq_body_pers_component(_persistent)` (`uniq_bytes_util.v`): the legacy versions in
  `uniq_util.v` are used by `&uniq`, `borrow.v`, `product_split.v` and `type_sum.v`, and
  `uniq_util.v` is imported by the byte files.
- `bfn`, `bfn_spec`, `bfn_resolve`, the rules `type_bcall`, `type_bfn`, … and `bmain_type`,
  `type_soundness_b(_closed)`: the legacy `fn` and `type_soundness` stay.
- `btype_incl`, `bsubtype`: `type_incl` and `subtype` of `type.v` stay.
- The notations `&uniqb` and `&shrb`: `&uniq` and `&shr` stay.

### Still legacy, and why

All of this is needed by `pcell` (with `pptr`, `ra`, `protocol` and `pcell_example`):
- the word layer: `ty_phys`, `syn_phys`, the sum padding, `↦!∗` cells, `phys_rel`, legacy
  `Read`/`Write`/`CAS`, and `ty_size` in words;
- the legacy types `own_ptr`/`box`, `&shr` (`shr_bor.v`), `&uniq` (`uniq_bor.v`,
  `uniq_util.v`), `fn` (`function.v`) and `soundness.v`;
- the core rules `borrow.v`, `product_split.v`, `type_sum.v`, `programs_util(_own)` and
  `type_new`.

These go with the pcell redesign (cells as fancy bytes). The examples `assert.v` and
`list.v` also stay on the legacy layer.

## Outcome: stage 5 / §10 step 6 (legacy typing layer deleted)

Stage 5, second part (§10 step 6 of `pcell-multibyte-cells.md`). With `pcell`, `ra` and
`protocol` on bytes (§§14–16 of that document), the user decision was **port, then
delete**: every legacy feature without a byte counterpart was ported, then the legacy
typing layer was removed. No `Admitted`; no new axioms. The examples print only
`functional_extensionality_dep` under `Print Assumptions`.

### Ported to bytes

Ghost values are MiniRust values (`◁ᵥ`, the empty tuple), as in `ra`/`protocol` (§15).
- **Ghost operations** (`ghost.v`). `GhostOp`, `GhostRet`, `wp_ghost_op` moved here from
  `ra_bytes.v`. New helpers `typed_inv_instr_ghost_op` / `typed_instr_ghost_op`: a ghost
  operation is a ghost update at its value `()`, with two cumulative time receipts.
  `ghost_constant`, `ghost_snapshot`, `ghost_compute` return `v ◁ᵥ ghost_ty ty`; snapshot
  and compute take any type-context element (`tctx_elt`).
- **Atomic invariants** (`atomic_inv.v`, helper `typed_atomic_ghost_op` in
  `programs_util_atomic.v`). `typed_atomic_inv_alloc`
  (`+[p1 ◁ᵥ ghost_ty tyCN; p2 ◁ᵥ tracked_ty ty]` → `v ◁ᵥ atomic_inv_ty ty pred`),
  `_destroy` (→ `v ◁ᵥ tracked_ty ty`), `_open`
  (`p ◁ᵥ &shr{κ} (atomic_inv_ty …)` → `+[v ◁ᵥ tracked_ty ty; v ◁ᵥ atomic_closer_ty κ ty pred]`),
  `_close`. **Deviation:** `open` returns its two ghost values at the *same* value `v = ()`
  (both are zero-sized ghost values), instead of a box of a pair.
- **Local invariants** (`local_inv.v`): the same four rules and the same deviation. `close`
  takes the cumulative time receipts it stores in the invariant from
  `wp_cumulative_time_receipt_linear`.
- **Function types** (`function.v`, formerly `function_bytes.v`): `fn_params`, `subst_plv`,
  `fp_E`, `tr_ret` moved here from the legacy `function.v`; new `fn_send`, `fn_sync` and
  `type_call_iris` (empty lifetime context, as in a new thread).
- **`assert`** (`examples/assert.v`) on `fn` with a `◁ᵥ bool_ty` argument; new
  `type_if_val` (`value_ctx.v`): `if: ToLit p then … else …` on a boolean value.
- **`spawn`** (`spawn.v`): `spawn_type` on `fn`; the argument is a value `◁ᵥ fty`, the
  join handle is returned as a pointer value (`OfLit (spawn …)`), and `join_future` holds a
  MiniRust value (`syn_val x' = Some w`). The language library `lang/lib/spawn.v` (word
  `Read`/`Write`) is unchanged.
- **Soundness** (`soundness.v`): the theorem of `soundness_bytes.v`, now `main_type`,
  `type_soundness`, `type_soundness_closed`.
- **`PPtr`** (`pptr.v`): `ptr_ty` (a pointer value) and
  `points_to_ty ty := tracked_ty (own_bytes (ty_bsize ty) ty)`; `typed_pptr_to_own`,
  `typed_pptr_from_own` (a `GhostOp`: the box's own pointer value becomes the `PPtr`, the
  result is the permission), `typed_pptr_borrow` (→ `&shr{κ} ty`), `typed_pptr_borrow_mut`
  (→ `&uniq{κ} ty`, via `uniq_body_transform`).
- **Boxes** (`own.v`): `own_bytes_send`, `own_bytes_sync`, `own_bytes_resolve` (hint),
  `own_bytes_type_contractive`.
- **Recursive types** (`examples/list.v`): the list type over `own_bytes` boxes
  (`list_node_size 𝔄 := syn_bsize (Σ! [(); 𝔄 * rlistₛ 𝔄])`); `list_unfold_fold`,
  `list_resolve`, `list_resolve_just`. **Not ported:** `list_subtype`/`list_eqtype` (they use
  the legacy `subtype` of boxes; a byte version needs a `bsubtype` for `fix_ty`).
- The accessors `uniq_bor_loc/current/future/ξi` moved to `uniq_util.v`.

### Deleted

- Files (`typing/`): `pcell.v`, `examples/pcell_example.v` (legacy), `own.v`, `shr_bor.v`,
  `uniq_bor.v` (legacy pointer types), `function.v` (legacy `fn`), `borrow.v`,
  `type_sum.v`, `product_split.v` (pre-place core rules: subsumed by the place rules),
  `programs_util.v`, `programs_util_own.v`, `soundness_bytes.v` (merged); `lang/lib/memcpy.v`.
- The legacy rules of `ra.v`/`protocol.v`; `typed_read`, `typed_write`, `type_assign`,
  `type_deref`, `type_memcpy` (`programs.v`); the legacy word-level half of `uniq_util.v`
  (`uniq_body`, `uniq_payload`, … on `↦!∗`); the legacy `typed_atomic_instr*` helpers;
  `letalloc`; `split_mt_ptr`; the syntactic type `pcellₛ n` (with `pair_with_cell_idsₛ`).
- In total about 13 700 lines removed and 3 300 added (from `5601fea`).

### Renamed (no legacy namesake left)

- Files: `own_bytes` → `own`, `shr_bytes` → `shr_bor`, `uniq_bytes` → `uniq_bor`,
  `function_bytes` → `function`, `pcell_bytes` → `pcell`, `pcell_bytes_borrow` →
  `pcell_borrow`, examples `pcell_example_bytes` → `pcell_example`, `own_bytes` → `own`,
  `function_bytes` → `function`. Merged: `uniq_bytes_util` into `uniq_util`, `ra_bytes` into
  `ra`, `protocol_bytes` into `protocol`.
- Definitions/lemmas: `pcellbₛ` → `pcellₛ`; `buniq_*` → `uniq_*`; `bofty_owned`,
  `bleaf_owned`, `bleaf_node`, `bblocked_owned` → without `b`; `bfn*` → `fn*`; `type_bcall`,
  `type_bletcall`, `type_bfnrec`, `type_bfn` → `type_call`, `type_letcall`, `type_fnrec`,
  `type_fn`; `pcellb_*`/`PCellb*`/`bcell_*`/`type_pcellb_*`/`type_bcell_*` → `pcell_*`/
  `PCell*`/`cell_*`/`type_pcell_*`/`type_cell_*`; `typed_rab_*`/`RAb_*` → `typed_ra_*`/`RA_*`;
  `typed_spb_*`/`SPb_*` → `typed_sp_*`/`SP_*`; `storable_*_bytes` → `storable_*`;
  `pcell_example_b_type` → `pcell_example_type`. Notations `&uniqb{κ}`/`&shrb{κ}` →
  `&uniq{κ}`/`&shr{κ}`.
- **Kept:** the type names `own_bytes`, `shr_bytes`, `uniq_bytes` (descriptive; only the
  files and notations were renamed); `btype_incl`, `bsubtype` (the legacy `type_incl`,
  `subtype` of `type.v` are still used by `fixpoint`, `mod_ty`, `tracked`, `uninit`, …).

### Still legacy, and why

- **The word layer of the type record**: `ty_size` (words), `ty_phys`, `syn_phys`,
  `size_of`, the padding component of `~~(Σ! 𝔄l)`, the legacy element `p ◁ ty` (used by
  closures: `f ◁ fn …`), `Send`'s `ty_phys` clause, the legacy `type_incl`/`subtype`.
  Removing them changes the type record and every type definition; not done.
- **`cloc`** in `~~(at_clocₛ 𝔄)` and `~~(uniq_borₛ 𝔄)`, and the guard
  `@[κ] &&{…}&&> l #↦∗_` of `&uniq{κ}` and of the place invariants (`ltype`, `lpath`,
  `pctx_acc`, `place_*`): both run through the whole place machinery (~15 000 lines).
  The cells are always empty for bytes (`heap_cloc_mapsto_empty`).
- **The word heap and the word-level language** (`Read`/`Write`/`CAS`, `↦`, `↦!∗`, the
  cell map of `util/cellmap.v`/`non_atomic_cell_map.v`, `phys_rel`): still used by
  `#↦∗_` above, by `lang/lib/spawn.v` and by the adequacy/race proofs.

**Axioms.** `Print Assumptions` of the examples shows `functional_extensionality_dep`,
and, for the results that use `proph_obs_sat` (`prophecy/prophecy.v`: the rules with a
pure verification condition, e.g. `typed_pptr_*`, `typed_*_inv_*`, `type_pcell_borrow_instr`,
hence `pcell_example_type`, `spawn_type`, `assert_type`), also `Eqdep.Eq_rect_eq.eq_rect_eq`.
The atomic invariants use `Classical_Prop.classic` (case on `Send ty`), as before. None
of these is new.

## Outcome: stage 6 (word layer removal)

Stage 6 removes what stage 5 left word-based ("Still legacy, and why" above), on the branch
`proto/word-delete`, merged into `memory-model` step by step (`--no-ff`, each after a clean
full build). No `Admitted`, no new axioms. In total about 8 600 lines removed and 1 900
added (from `27ddfad`).

### A. `cloc` and the `#↦∗_` guards (merge `ffde693`)

- The guards `@[κ] &&{…}&&> l #↦∗_` are gone from `&uniq` (`uniq_bor.v`, `uniq_util.v`),
  the place types (`ltype.v`: `uniq_node`, `uniq_nval`, `view_leaf`), the paths
  (`lpath.v`: `wp_pctx_expr` has neither the guard nor its credits; `pctx_loc_guard`
  deleted), the accessors (`pctx_acc.v`: `pctx_pguards`, `pctx_vpguards`, `pctx_hlft`
  deleted) and all `place_*` files.
- `cloc` is `loc` everywhere: `at_clocₛ` was merged into `at_locₛ` (`at_cloc_mapₛ`
  deleted), `~~(uniq_borₛ 𝔄)` holds a `loc`, `cloc_take l n`/`cloc_skip l n` became
  `l`/`l +ₗ n`, `loc_dummy` replaces `cloc_dummy`. Deleted: `cbytes_at_cloc`,
  `syn_bytes_at_cloc`, `pctx_loc_empty`, `oplace_loc_empty`, `guards_empty_cell`, the
  `take`/`drop` of `repeat` lemmas.
- **Kept:** the later-credit budgets of the callers (`pshr_cred`, `pctx_vacc_cred`) still
  count the credits the deleted guards consumed; they are now larger than needed. Shrinking
  them only changes arithmetic side conditions, so it was not done.

### B. The word heap and the word-level language (merge `e82b1b1`)

- `lang/lib/spawn.v` is on bytes: `spawn` and `join` are parametrized by the MiniRust
  type `m` of the result (a `Store`/`Load` of `MBool` for the flag at `c`, the data at
  `c +ₗ 1`; `join_spec` assumes `mty_wf m`). `typing/spawn.v` uses
  `spawn (syn_mty 𝔅) call_once` and `join_handle spawnN (syn_mty 𝔄)`.
- Deleted from the language (`lang.v`): `Read`, `Write`, `CAS` with their evaluation
  contexts and head steps, `word_to_byte`; the notations `!`, `<-`, `<-{Σ}`
  (`notation.v`) and their tactics (`tactics.v`, `proofmode.v`).
- `heap.v` (3 161 → about 1 350 lines): the word points-to `↦`/`↦∗`/`↦!∗`, `phys_rel`, the
  word heap and its cell map are deleted; `heap_maps_ctx σ` is `bytes_ctx σ`; `naN` moved
  here. `lifting.v`: the word WP rules are deleted (`wp_eq_loc` is on `l ↦b [b]`);
  `new_delete.v`: `wp_new`, `wp_delete` are on bytes; `races.v`, `adequacy.v` lost their
  word cases. `AbstractByte` lost the `Word` constructor and its parameter.
- Deleted files: `util/non_atomic_cell_map.v`. `util/cellmap.v` keeps `fcmap` (used by
  the cells of `heap_cells.v`); its `cmap` camera and logic are deleted.
  (Superseded: `util/cellmap.v` and `lang/heap_cells.v` were deleted in phase 5 of
  `guarded-mutable-borrows-plan.md`; the byte region of `heap.v` is now a plain ghost map.)

### C1. Closures (merge `c886fd9`)

`tctx_elt` has a single constructor `TCtx_sem`: the legacy word element `p ◁ ty` and the
blocked element `p ◁{κ} ty` (and their lemmas, `typed_instr_ty`, `type_val`,
`type_resolve*`, `type_path_instr`, `type_letpath`, the word rules of `bool`/`int`) are
deleted. **Deviation:** closures are not MiniRust values, so function values are typed by
a new semantic element `p ◁ᶠ ty` (`type_context.v`, `fun_own`: the path evaluates to the
closure `x.1` of the value `x` of `ty : type (exec_funₛ ℭ)`, with its ghost ownership;
lemmas `tctx_fun_val`, `wp_fun`) instead of a value-based `◁ᵥ`. `typed_val`,
`function.v`, `spawn.v`, `soundness.v` and `examples/function.v` use `◁ᶠ`.

### C2. The word fields of the type record (merge `7e01136`)

- `type`: `ty_size`, `ty_phys`, `ty_size_eq`, `ty_size_eq2`, `ty_phys_eq2` and `ty_own`
  are deleted, as are the corresponding fields of `simple_type`, `plain_type`,
  `ghost_type` (`st_concrete`, `pt_concrete`, `gt_size0`, `gt_phys0`, …). `type_equiv'`,
  `type_dist'`, `TypeNonExpansive`, `TypeContractive` lost their size/phys components;
  `Copy` lost `copy_concrete`, `Send` lost `send_change_tid_phys`, `Sync` is
  ownership ∧ persistence ∧ sharing. `JustLoc`, `StackOkay`, `by_just_loc` deleted.
- `syn_type.v`: `size_of`, `syn_phys`, `pad`, `syn_phys_size_eq`,
  `syn_abstract_phys_eq` deleted; `Isoₛ` lost `syn_iso_size_eq` and `syn_iso_phys_eq`.
- `heap.v`: `fancy_val`/`FVal`/`FCell`/`all_concrete` deleted.
- Every type definition lost its size/phys fields and obligations; fixed on the way:
  `int_send`/`int_sync` were stated for the wrong type.

### C4. One subtyping (merge `f6964a6`)

- `type_incl ty ty' f` (`type.v`) now starts with `⌜syn_bincl f⌝`: `f` preserves the size
  and the fancy byte representation (`syn_fbytes`, moved to `type.v`). A parent owns the
  bytes of its referent, so retyping a box, a reference or a borrow needs this; for
  `f = idₛ` it is trivial (`syn_bincl_id`). The byte-only `btype_incl`/`bsubtype` and
  `subtype_bsubtype_id`/`uniq_bytes_bsubtype` are deleted; renamed: `own_bytes_bsubtype`
  → `own_bytes_subtype`, `shr_bytes_bsubtype` → `shr_bytes_subtype`,
  `own_bytes_btype_incl`/`shr_bytes_btype_incl` → `…_type_incl`, `tctx_bsubtype_*` →
  `tctx_subtype_*`, `bytes_own_btype_incl` → `bytes_own_bincl`.
- `syn_bincl` lemmas: `syn_bincl_compose`, `syn_bincl_iso` (`type.v`); `syn_bincl_same`
  (same MiniRust type and fancy value: pointers, zero-sized types),
  `syn_bincl_at_loc_map`, `syn_bincl_prod_map`, `syn_bincl_to_cons_prod`,
  `syn_bincl_of_cons_prod` (`bytes_layout.v`, with the new `syn_fbytes_zst`,
  `syn_fbytes_uninit`, `syn_fbytes_xprod_nil/cons`, `syn_bsize_prod`,
  `syn_bsize_xprod_cons`); `syn_bincl_prod_assoc/left_id/right_id` (`product.v`),
  `syn_bincl_psum_map` (`sum.v`), `syn_bincl_uninit_split` (`uninit.v`),
  `syn_bincl_sum_to_list` (`examples/list.v`).
- New hypotheses: `syn_bincl f` for `mod_ty_in/out/inout/outin/subtype/eqtype` (an `Isoₛ`
  only relates plain bytes), `eqtype_unfold`, `eqtype_unfold_default`,
  `type_incl_default`, the `simple`/`plain`/`ghost` helpers, `base_subtype`/
  `base_eqtype` and `fix_subtype`/`fix_eqtype` (the limit needs it at every step).
- The commented-out `xprod_ty_app_prod` was deleted.

### C3. Sum padding and uninitialized values (merge `293bea2`)

- `~~(Σ! 𝔄l)` is `psum ~~ 𝔄l` (was `psum ~~ 𝔄l * list val`), likewise its prophecy and
  abstracted sorts. `psum_mapₛ`, `syn_val`, `syn_fval`, the place refinements of sums
  (`prfn_struct`, `prfn_sum i r` without the padding argument, `prfn_den_sum`,
  `prfn_wit_sum`, `prfn_rsv_sum`), `sum_node_inv`, `type_mk_variant_val_instr` (the
  transformer no longer quantifies over a padding) and all users were adapted. The bytes
  of the padding of an enum are of course still there (`pad_cell` in `ltype.v`).
- The syntactic type `paddingₛ` is deleted; the list example uses
  `rlistₛ 𝔄 := at_locₛ (listₛ (𝔄 * locₛ))`.
- `~~(uninitₛ n)` is `()` (was `vec val n`); the "junk" values of moved-out leaves are
  `()`.

### Still word-based, and why

- **The expression language.** Expressions are λRust expressions with MiniRust memory
  operations: closures, continuations (`vec val n` arguments), `Alloc`/`Free`/`+ₗ` and the
  case on a tag work on λRust values (`#l`, `#z`, `LitPoison`), converted from MiniRust
  values with `ToLit`/`OfLit`. These are values of the expression language, not of
  memory; replacing them changes the language and the adequacy proof, not the memory
  model.
- **Function values** (`◁ᶠ`, C1) carry a λRust closure for the same reason.

(Superseded by stage 7 below: the λRust literals and `ToLit`/`OfLit` are gone; closures
remain non-MiniRust values of the expression language.)

**Axioms.** See the final report: `Print Assumptions` of the examples is unchanged from
the baseline (`functional_extensionality_dep`, and `Eqdep.Eq_rect_eq.eq_rect_eq` for the
rules with a pure verification condition).

## Outcome: subtyping for fixpoint types

Known gap 11 (branch `proto/fix-subtype`): the `syn_bincl` hypotheses that stage 6 (C4)
added to the subtyping rules were revisited, and `list_subtype`/`list_eqtype` are ported.

- **`Isoₛ` preserves the fancy bytes.** `Isoₛ f g` (`prophecy/syn_type.v`) has the new
  field `syn_iso_bincl : syn_bincl f`; the field `syn_iso_bsize_eq` became a lemma (it is
  the first component of `syn_bincl`), and `syn_iso_bytes` is stated with the new
  `syn_bytes_pres f`. For this, `syn_fbytes`, `syn_cells_pres`, `syn_bincl`,
  `syn_bincl_id/compose/same` and `mcells`/`mshift` (with their lemmas) moved from
  `typing/type.v`, `typing/bytes_layout.v` and `typing/gcont.v` to `prophecy/syn_type.v`.
  `syn_bincl_iso` is now `Isoₛ f g → syn_bincl g` (via the new `syn_bincl_inv`). The
  instances whose fancy bytes need the layout lemmas moved after them:
  `isoₛ_cons_prod`, `Isoₛ_prod_left_id`, `Isoₛ_prod_right_id` (with
  `syn_bincl_prod_left_id/right_id`) are in `typing/bytes_layout.v`; their plain-byte
  parts stayed in `syn_type.v` as `syn_bytes_pres_to_cons_prod`,
  `syn_bytes_pres_prod_left_id/right_id`.
- **Hypotheses removed** (an `Isoₛ` now gives them): `syn_bincl f` (and `syn_bincl g`) of
  `mod_ty_in/out/inout/outin/subtype/eqtype` and of `eqtype_unfold`,
  `eqtype_unfold_default`. Callers updated: `xprod_subtype`, `prod_ty_assoc/left_id/
  right_id`, `uninit_unit`, `uninit_plus_prod`, `list_unfold_fold`, `sum_list_isoₛ`.
- **Hypotheses kept, because they are semantically required:** `syn_bincl f` of
  `fix_subtype` (`syn_bincl f`, `syn_bincl g` of `fix_eqtype_subtype`, `fix_eqtype`),
  `base_subtype`/`base_eqtype`, `type_incl_default` and the `simple`/`plain`/`ghost`
  helpers. These rules have an arbitrary map `f`, and their conclusion implies
  `syn_bincl f` (it is the first component of `type_incl`; with `E = L = []` a subtyping
  proves it outright). For the fixpoint, the step hypothesis cannot provide it: when no
  subtyping along `f` exists it holds vacuously. The hypothesis is syntactic, though, and
  for a fixpoint through a pointer it holds whatever `f` does to the elements
  (`syn_bincl_list_map`, by `syn_bincl_same`).
- **New lemma** `subtype_bincl_elim` (`type.v`): a subtyping may assume the `syn_bincl`
  of another subtyping. `list_subtype` uses it to equate the node sizes
  `list_node_size 𝔄 = list_node_size 𝔅`, which depend on the element type.
- **Ported** (`typing/examples/list.v`, hints restored):
  `list_subtype : subtype E L ty ty' f → subtype E L (list_ty ty) (list_ty ty') (list_mapₛ f)`
  and `list_eqtype`, with no hypothesis beyond the subtyping of the elements.

## Stage 7: MiniRust values in the expression language

Known gap 17: the expression language still has the λRust literals (`base_lit`:
`LitInt`, `LitLoc`, `LitPoison`) next to the MiniRust values `MLit v`, with the conversions
`ToLit`/`OfLit` between them (stage 6, "Still word-based"). Stage 7 removes the λRust
literals; the memory model does not change.

### The values of the expression language

```
Inductive val :=
| MLitV (v : Value)                         (* a MiniRust value *)
| RecV (f : binder) (xl : list binder) (e : expr) `{!Closed (f :b: xl +b+ []) e}.
```

- **MiniRust values.** Every first-order value of a program is a MiniRust `Value`
  (`VInt`, `VBool`, `VPtr`, `VTuple`, `VVariant`). The expression constructor `Lit`,
  `base_lit`, `LitV`, `ToLit`, `OfLit`, `value_to_lit`, `lit_to_value` and the coercion
  `lit_of_bool` are deleted. The notation `#v` is `MLitV v` (in `expr_scope`: `MLit v`),
  with the coercions `VInt : Z >-> Value`, `VPtr : loc >-> Value` and
  `VBool : bool >-> Value` (`notation.v`), so `#4`, `#l`, `#true` keep their syntax and
  mean `VInt 4`, `VPtr l`, `VBool true`.
- **Closures stay non-MiniRust values** (decision 3 of the plan, and C1 of stage 6): `RecV`
  is a value of the expression language, not a `Value`, so it cannot be stored in memory
  (it has no bytes). This is what the typing layer already assumes: function values are
  typed by `p ◁ᶠ ty` (`fun_own`), not by `◁ᵥ`. Function pointers in memory (MiniRust's
  `Ptr` to a function) are a separate extension. Continuations are closures too; their
  arguments are `vec val n` as before (now MiniRust values or closures).
- **`LitPoison` becomes the unit value** `VTuple []` (MiniRust's `()`); the notation `☠`
  is kept for it (`val_scope`), so `#☠` is the result of the instructions without a
  result (`Store`, `MemCopy`, `Free`, `Fork`, `GlobalUnlock`, `delete`) and the operand
  of the ghost instructions (`Newlft`, `Skip`, `Endlft`, …). Poison was "stuck except for
  memory accesses", but nothing relies on that: a stored value is a `Value` already, and
  `#☠` is only ever sequenced away.

### Operations on values

- **Pointer arithmetic** `e1 +ₗ e2` (`BinOp OffsetOp`): `VPtr l`, `VInt z` ↦ `VPtr (l +ₗ z)`.
- **Integer operations** `+`, `-`, `*` on `VInt`; `≤` gives a `VBool`.
- **Equality** `=` (`EqOp`) on two `VInt`s, two `VBool`s or two `VPtr`s gives a `VBool`;
  the comparison of dangling pointers stays nondeterministic (`lit_eq` → `val_eq`, on
  `Value`s). The comparisons of a pointer with the integer `0` (λRust's null) are deleted:
  MiniRust compares pointers with pointers.
- **`Case e el`** takes a `VInt i` (the tag of an enum, as loaded by a typed `Load` of
  `MInt (sum_tag _)` or given by `VariantTag`) and goes to `el !! i`. **`If`** stays the
  derived form `Case e [e2; e1]`, and `Case` also takes a `VBool b` (index
  `Z_of_bool b`), so `if: Load ScOrd MBool "c" then …` needs no conversion.
- **Memory operations** take their addresses as `VPtr l` values: `Load o m #l`,
  `Store o m #l e`, `MemCopy o n #l1 #l2`, `MCAS m #l e1 e2`; `Alloc #n` (a `VInt`)
  returns `#l` (a `VPtr`), `Free #n #l`. So `ToLit p` disappears from every address and
  `OfLit (Alloc #n)` is `Alloc #n`.
- `NdInt` gives a `VInt`; `GlobalLock` gives a `VBool` (whether the lock was held).
- `MkTuple`, `Proj`, `MkVariant`, `VariantTag`, `VariantData` are unchanged (they were
  already on `Value`s).
- `Fork e` gives `#☠`; spawn (`lang/lib/spawn.v`) only loses its `ToLit`.

### Instructions of the typing rules

The typing rules keep their shapes (contexts, transformers, side conditions); their
instruction expressions change syntactically:
- `ToLit p` ↦ `p`, `ToLit (Load Na1Ord MPtr e)` ↦ `Load Na1Ord MPtr e` (`pctx_expr`,
  `pctx_vexpr`, `drop_boxes`, the place rules and the examples), `OfLit (ToLit p +ₗ #n)`
  ↦ `p +ₗ #n` (`place_shr.v`).
- **`&ˢ e` (`share`) keeps one step.** `share e := OfLit e` took a step after the address,
  and the shared-borrow rules use the first step of the instruction for credits and a time
  receipt (`wp_cumulative_time_receipt_linear` needs a non-value), while the address
  `pctx_vexpr K p` may now be a value (for `K = POwn _ PHole`). `share e` becomes
  `place_addr e := let: "_v" := e in "_v"` (a derived form, evaluating `e` and then one β
  step), so the rules keep their step structure and no constructor is added. `&ᵘ e`
  (`borrow_uniq`) has its two `Skip` steps and becomes `Seq (Seq Skip Skip) e`.
- **`e1 <-ᵇ{n} e2` (`memcpy`) takes both addresses with `place_addr`** for the same reason:
  the memcpy rules take the credits and time receipts of the destination and of the source
  from the first step of each address (`pctx_vexpr_to_val`, which no longer holds, is
  deleted). `memcpy n e1 e2 := MemCopy Na1Ord n (place_addr e1) (place_addr e2)`.
- Proofs lose the `wp_pure` steps of `ToLit`/`OfLit`; where a proof used such a step to
  strip a later, a `Skip` or credit of the surrounding instruction is used instead (none is
  expected: the loads give their own later).
- `eval_path` (`type_context.v`) computes `p +ₗ #n` on `VPtr`s.

### Adequacy, races, reification

- `adequacy.v` and `soundness.v` do not depend on the value type (only on `to_of_val`); the
  `exit_cont` returns `#☠`.
- `races.v`: `next_access_head` matches `MLit (VPtr l)`, `MLit (VInt n)` instead of the
  literals; the proof is otherwise unchanged. The stuck term is `App (MLit (VInt 0)) []`.
- `tactics.v` (`W.expr`, `W.of_expr`, `W.to_val`, `W.subst`, `reshape_expr`): the cases
  `Lit`, `ToLit`, `OfLit` are deleted; `lang.share` is unfolded like `lang.borrow_uniq`.

### Migration order and estimate

Each layer below depends on the previous, and the language change breaks every file
downstream, so the stage is one branch (`proto/lang-values`) with a WIP commit per layer,
merged once after a clean full build (a compatibility layer with both kinds of literals
would double the work for no intermediate gain):
1. language: `lang.v`, `notation.v`, `tactics.v`, `proofmode.v`;
2. lifting and adequacy: `lifting.v`, `races.v`, `adequacy.v`, `lang/lib/*`, `minirust_tests.v`;
3. typing core: `type_context.v`, `value_ctx.v`, `programs*.v`, `function.v`, `lpath.v`,
   `pctx_acc.v`, `soundness.v`;
4. place rules: `place_*.v`, `pcell.v`, `gmb_*` tests, `spawn.v`;
5. examples (`typing/examples/*.v`: the programs change syntactically).

Size: about 40 files, mostly mechanical (about 200 `ToLit`, 50 `OfLit`, 150 `LitV`, 70
`LitLoc` occurrences); the deleted language code is about 150 lines. Risk: low to medium.
The proofs that stepped over a `ToLit`/`OfLit` change locally; `share` keeps its step,
so the shared-borrow proofs should not change. No new axioms are expected.

## Outcome: stage 7 (MiniRust values in the expression language)

Branch `proto/lang-values`, merged into `memory-model` after a clean full build. No
`Admitted`, no new axioms (`Print Assumptions` of the examples unchanged).

- **Language** (`lang/lang.v`): `val := RecV … | MLitV (v : Value)`; deleted: the
  expression `Lit`, `base_lit` (`LitPoison`, `LitLoc`, `LitInt`), `LitV`, `ToLit`,
  `OfLit` (with their evaluation contexts and head steps), `value_to_lit`,
  `lit_to_value`, `lit_of_bool` (and its coercion), `lit_eq`/`lit_neq` (now
  `val_eq`/`val_neq` on `Value`s, with booleans; the comparisons of a pointer with the
  integer `0` are deleted), `pure_eq_loc_0_l/r`, `pure_to_lit`, `pure_of_lit`. New:
  `IfS` (`Case` on a `VBool`), `pure_eq_bool`, the notation `unitV` (`VTuple []`, the result
  of `Store`, `MemCopy`, `Free`, `Fork`, `GlobalUnlock`), and `place_addr` (see above).
  `GlobalLock` returns a `VBool`.
- **Notation** (`lang/notation.v`): `#v` is `MLitV v`, with the coercions `VInt`, `VBool`,
  `VPtr`; `☠` is the unit value.
- **Tactics**: `W.expr` lost `Lit`, `ToLit`, `OfLit`; `share` and `memcpy` are unfolded
  by `W.of_expr`. `wp_bind` now also succeeds when the focused expression is the whole
  expression (it used `||`, which needs progress, and the empty context makes none).
- **Typing**: `ToLit p` ↦ `p`, `OfLit (Alloc #n)` ↦ `Alloc #n` everywhere (`pctx_expr`,
  `pctx_vexpr`, `drop_boxes`, `eval_path` on `VPtr`/`VInt`, the place rules, `pcell.v`,
  `shr_bor.v`, `value_ctx.v`, `subtype.v`, `spawn.v`); the proofs lost the `ToLit`/`OfLit`
  steps (where the next goal is no longer a `WP`, `iApply wp_fupd` keeps the update
  modality: `wp_pshr_open`). `type_shr_bytes_fst_instr` is now the identity instruction
  `p`. `wp_global_try_atomic_lock` returns a boolean.
- **Examples**: the programs lost `ToLit`/`OfLit` (e.g. `!ᶜ{MInt i32} ("x" +ₗ #4)`,
  `"c" <-ᵇ{8} …`, `let: "c" := Alloc #8 in`, `case: Load Na1Ord (MInt …) "b" of …`,
  `if: "b" then …`); their proofs are unchanged.


## Outcome: `Send` and `Sync` of the references (branch `proto/ref-send-sync`, 2026-11-03)

- `sync_send : Sync ty → Send ty` (`typing/type.v`). `Sync` here includes the
  thread-independence of `ty_gho_own` (and of `ty_gho_pers`, `ty_shr`), so a `Sync` type is
  sent unchanged, without a step (in RustBelt, `Sync` only constrains the sharing
  predicate; this is a consequence of the definitions here).
- `shr_sync : Sync ty → Sync (&shr{κ} ty)` (by `sync_default`: the guard of the bytes does
  not depend on the thread) and `shr_send : Sync ty → Send (&shr{κ} ty)` (`shr_bor.v`), as
  in RustBelt.
- `uniq_sync : Sync ty → Sync (&uniq{κ} ty)` is kept, and `uniq_send_sync : Sync ty →
  Send (&uniq{κ} ty)` is new (`uniq_bor.v`).
- **Not provable: `uniq_send : Send ty → Send (&uniq{κ} ty)`.** `send_change_tid` is a
  one-way update (with `d` steps, a new value `x'` of the same `syn_abstract` and a new
  depth), not RustBelt's equivalence of the ownership at two threads. The ownership of the
  referent at `tid` is the body of the prophetic borrow at `κ` of `&uniq` (`uniq_persγ`,
  with the lazy payload guarded by `@[ty_lft ty]`; its value and depths are those of the
  token `uniq_tokγ`). So the body cannot be rewritten by `llftl_bor_iff`; a send would have
  to open the borrow (with `κ` alive: the hypotheses of `send_change_tid` only guard the
  thread's lifetimes `κs`), update, and close it with the ownership at `tid'` of the new
  value, which the lender would then get back at the end of `κ` instead of what it lent.
  Needed: `Send` as (or implying) a thread-equivalence of `ty_gho_own` (then the proof is
  that of `uniq_sync`), or the restriction to `κ = static` (borrows never given back; the
  legacy `uniq_send_static`, deleted with the legacy layer, with an access lemma of the
  body at another thread). The reason is also stated in `uniq_bor.v`.
- Tests: `typing/ref_send_sync_tests.v` (instance search for `&shr`/`&uniq` of `int`, of
  boxes, of pairs, nested, and `&shr` of a cell).

## Send as a thread-equivalence (branch `proto/send-equiv`)

Goal: `uniq_send : Send ty → Send (&uniq{κ} ty)`, as in RustBelt. Its proof needs the
thread-independence of the ownership of the referent (`uniq_body_proper`, as in
`uniq_sync`), which the one-way update `send_change_tid` does not give (see the outcome
section above).

### Audit of the update form

The update form of `Send` (`send_change_tid` at `typing/type.v`) takes `d` steps, may
change the value (to an `x'` of the same `syn_abstract`) and the depth (`d + off`), and gets
the thread's `cna_lifetimes` (through a guard at `SendN`) and the guards of its lifetimes.

Instances, and what their proof uses:

- Ownership independent of the thread; sent unchanged, without a step (each is also `Sync`):
  `unit0_send` (`product.v`), `int_send`, `bool_send`, `base_send`, `uninit_send`,
  `ptr_send` (`pptr.v`), `pcell_send`, `ra_send`, `ghost_send`, `join_handle_send`
  (`spawn.v`), `fn_send` (`function.v`), `shr_send : Sync ty → Send (&shr{κ} ty)`,
  `uniq_send_sync : Sync ty → Send (&uniq{κ} ty)`, `atomic_inv_ty_send` (its ownership
  is an invariant of the atomic pool, which holds the contents at `null_tid` when the
  contents are `Send`), `storable_ty_send` and `storage_ty_send` (`protocol.v`; they also
  assume `Sync`, which already gives the equivalence).
- Structural (the update of the components; steps and value changes only come from the
  components): `prod_send`, `xprod_send` (`product.v`), `xsum_send` (`sum.v`),
  `own_bytes_send` (`own.v`: one step for the later of the box, and the bytes follow the
  new value through `syn_abstract_fval_eq`), `mod_ty_send` (needs that `f` respects
  `syn_abstract`), `fix_send` (`fixpoint.v`), `tracked_send`, `points_to_send` (`pptr.v`),
  `cell_points_to_send` (`pcell.v`).
- **Genuinely needs the update:** `local_inv_ty_send : Send ty → Send (local_inv_ty ty
  pred)` (`local_inv.v`). The ownership of a local invariant is a cancellable non-atomic
  invariant in the pool of the thread, `cna_inv γ tid N (…)`, with the contents at `tid`.
  Sending it destroys the invariant (`cna_destroy`, which needs the thread's
  `cna_lifetimes` and the guards of its lifetimes), sends the contents (`d' - d1` more
  steps, paid by the time receipts and credits stored in the invariant), and allocates a
  new invariant at `tid'` (a new name `γ'` and a new depth, so a new value of the same
  `syn_abstract`). No equivalence of `cna_inv γ tid N P` and `cna_inv γ tid' N P` holds.

Uses of `send_change_tid` (consumers of the update form):

- `spawn_type` (`spawn.v`): sends the argument to the new thread and the result back to
  the joining thread (with the `cna_lifetimes` of the threads).
- `atomic_inv.v`: `change_tid_in`/`change_tid_out` move the contents of an atomic invariant
  to and from `null_tid`; `atomic_inv_ty` cases (by excluded middle) on `Send ty`.
- `local_inv_ty_send`, `xsum_send`, `fix_send` (structural uses).

So a `Send` that is a thread-equivalence of `ty_gho_own` keeps every instance except
`local_inv_ty_send`, and the update form is needed for local invariants only.

### Design

Two classes (`typing/type.v`):

- `Send ty := ∀ tid tid' x d g, ty_gho_own x d g tid ⊣⊢ ty_gho_own x d g tid'` (RustBelt's
  `Send`; a definitional class like `Sync`, with the field `send_change_tid`). The
  equivalence is symmetric, so the one-directional `⊢` would be the same.
- `SendUpd ty`: the former `Send` (the update, field `send_upd_change_tid`), unchanged.
  `send_send_upd : Send ty → SendUpd ty` is an instance (priority 100, so that the
  structural instances of `SendUpd` are tried first).

`sync_send : Sync ty → Send ty` stays (now the first component of `Sync`).
`spawn_type` takes `SendUpd fty, SendUpd retty`, and `atomic_inv_ty` cases on
`SendUpd ty`, so both still accept local invariants. Every structural instance has a
`Send` and a `SendUpd` version (`prod`, `xprod`, `xsum`, `own_bytes`, `mod_ty` — only
the `SendUpd` version needs `f` to respect `syn_abstract` —, `fix`, `tracked`,
`points_to`, `cell_points_to`).

### Outcome

- `uniq_send : Send ty → Send (&uniq{κ} ty)` (`uniq_bor.v`), by `uniq_body_proper`, as in
  `uniq_sync`. `uniq_send_sync` is deleted (it is `uniq_send ∘ sync_send`).
- `shr_send : Sync ty → Send (&shr{κ} ty)` and `sync_send` are kept.
- `local_inv_ty_send` is now `local_inv_ty_send_upd : SendUpd ty → SendUpd (local_inv_ty
  ty pred)`: a local invariant is not `Send`, only `SendUpd`. No other instance is lost.
- `atomic_inv_ty_send : SendUpd ty → Send (atomic_inv_ty ty pred)` (the equivalence
  `gho_equiv_of_send`), `atomic_inv_ty_sync : SendUpd ty → Sync …`.
- The `Send` hypotheses that `Sync` already implies are dropped: `storable_ty_send : Sync
  ty → Send (storable_ty ty)`, `storage_ty_sync : Sync tyC → …`, `storage_ty_send : Sync
  tyC → …` (`protocol.v`).
- The instances on thread-independent types (`int`, `bool`, `base`, `uninit`, `ptr`,
  `pcell`, `ra`, `ghost`, `join_handle`, `fn`, `unit0`) are proved by `done`.
- Tests (`typing/ref_send_sync_tests.v`): `Send ty → Send (&uniq{κ} ty)` and nested
  references by instance search, and `SendUpd` of products of boxes of references, from
  `Send` or from `SendUpd` of the components.
