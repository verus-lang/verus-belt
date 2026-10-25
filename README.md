# VerusBelt

This contains the Rocq development validating the contributions of _VerusBelt: A Semantic Foundation for Verus's Proof-Oriented Extensions to the Rust Type System_.

Permanent link to the artifact evaluated with the paper, including docker images: https://zenodo.org/records/19080059

# Installation

First, install Rocq (formerly Coq) 8.20.0.

You need to have [opam](https://opam.ocaml.org/) >= 2.0 installed.

The simplest option is to create a fresh *local* opam switch with everything:

```
opam update
opam switch create -y . ocaml-base-compiler.4.14.2
opam pin coq 8.20.0
eval $(opam env)
```

then run:

```
make -j4
```

If you prefer to use your package manager to install Iris, rather than using the artifact's
local copy, then install Iris 4.3.0 and stdpp 1.11.0:

```
opam repo add rocq-released https://rocq-prover.github.io/opam/released/
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
opam pin coq-iris 4.3.0
```

and run:

```
make all_using_opam -j4
```

# VerusBelt map

## Leaf Lifetime Logic (LeLiLo)

* Paper: Fig. 2
* Rocq:
  * Source: `src/lambda_verus/lifetime/lifetime_full.v`
  * Doc: `doc/lifetime_full.html`

Rules mentioned in the paper:

| Name in paper      | Name in Rocq                     |
|--------------------|----------------------------------|
| LeLiLo-Begin       | `llftl_begin`                    |
| LeLiLo-Not-Own-End | `llftl_not_own_end`              |
| LeLiLo-Tok-Inter   | `llftl_tok_inter_and`            |
| LeLiLo-End-Inter   | `llftl_end_inter`                |
| LeLiLo-Incl-Dead   | `llftl_incl_dead_implies_dead`   |
| LeLiLo-Incl-Guard  | `llft_incl` (by definition)      |
| LeLiLo-Shr-Borrow  | `llftl_borrow_shared`            |
| LeLiLo-Shr-Guard   | by definition                    |
| LeLiLo-Shr-Pers    | `llftl_borrow_shared_persistent` |

Remarks:

 * The `&α shr P` notation in the paper is a paper-only notation which is defined (LeLiLo-Shr-Guard) to be `[α] guards P`. In the Rocq source, this is written: `@[α] &&{↑NllftG}&&> P`.
 * Often the notation appears with an additional `n` parameter: `@[α] &&{↑NllftG; n}&&> P`. The `n` parameter is the number of "laters" (▷) introduced when applying the guard. This detail is not discussed much in the paper (see footnote 3).

## Points-To Cell Logic

* Paper: Fig. 4
* Rocq:
  * Source:
    * `src/lambda_verus/util/non_atomic_cell_map.v`
    * `src/lambda_verus/lang/lifting.v`
  * Doc:
    * `doc/non_atomic_cell_map.html`
    * `doc/lifting.html`

Notations:

There are a number of notations for cell-points-to, for different levels of abstractions
and for all the different ways of specifying lists of cells.
The `l @↦[ι][^cells] v` notation is closest to what's in the paper.

| Rocq notation          | Paper notation                                         |
|------------------------|--------------------------------------------------------|
| `lc @↦[ι] cv`          | `lc ↦ cv`                                              |
| `lc @↦[ι][^ cells] cv` | `lc -[cells]↦ cv`                                      |
| `l ↦ v`                | `l ↦ v`                                                |
| `l ↦! fv`              | `l ↦ fv`                                               |
| `l ↦[^ cells] v`       | `l -[cells]↦ v`                                        |
| `(l,cells) #↦_`        | `l -[cells_0, ..., cells_(k-1)]↦ cells_k`              |
| `(l,cells) #↦ v`       | `cells_k ↦ v` (or `l ↦ v` if `cells` is empty)         |

Rules mentioned in the paper:

| Name in paper  | Name in Rocq                 | File                    |
|----------------|------------------------------|-------------------------|
| Cell-Sep       | `pt_seq_app_sep`             | `non_atomic_cell_map.v` |
| Cell-And       | `pt_seq_app_and`             | `non_atomic_cell_map.v` |
| Cell-Fresh     | `pt_alloc_cell'`             | `non_atomic_cell_map.v` |
| Heap-Read      | `wp_read_na_guarded_cells_0` | `lifting.v`             |
| Heap-Write1    | `wp_write_na`                | `lifting.v`             |
| Heap-Write2    | `wp_write_na_guarded_0`      | `lifting.v`             |
| Heap-Move-Cell | `wp_cell_move_na`            | `lifting.v`             |

## Type-spec soundness theorem

* Paper: Sec. 3
* Rocq:
  * Source:
    * `src/lambda_verus/typing/soundness.v`

An example of instantiating the type-spec soundness theorem for a concrete piece of code
can be found in `src/lambda_verus/typing/examples/pcell_example.v`.
This example file also documents how the checking of a type-spec in VerusBelt corresponds to
the checking done by actual Verus.

## Semantic types

* Paper: Sec. 3.1
* Rocq:
  * Source:
    * `src/lambda_verus/typing/type.v`

The `type` record is used to define a semantic type. Types are parameterized by `𝔄` which
represents the interpreation sort.
This record is instantiated for all the types we care about in VerusBelt

The most important fields of this record are the `ty_gho_own` and `ty_phys` functions, which correspond
to [[T]].own and [[T]].phys from the paper. Also of note are:

  * `ty_size`: the size of the type
  * `ty_lfts`: lifetimes the type is included in (e.g., `&'a T` is included in `'a`)
  * `ty_gho_pers`: the "persistent part of" `ty_gho_own`.
  * `ty_shr`: the sharing predicate, a persistent predicate indexed by a lifetime `κ`
    (see `ty_share` for how it is obtained from a full borrow of `ty_gho_own`).

Finally, there are a bunch of well-formedness conditions.

## Typing rules

Typing rules for standard Rust types largely covers the same feature set as the prior work
(RustHornBelt) but are slightly modified for the following reasons:

 * Predicates require two additional parameters: the `mask` (see Sec. 4)
   and the `π` parameter of type `ProphAsn` (see Sec. 5.1).
 * Interpretation sorts have a little more information in them, e.g., a `box ty` is interpretted as `(l, x)` where `l` is the address of the box.

Below, we detail where to find the most important typing rules.

### Standard Rust types

Key typing rules:

 * `src/lambda_verus/typing/`
   * `programs.v`
     * `type_newlft`: Starting a lifetime
     * `type_endlft`: Ending a lifetime
     * `type_assign`: Assignment from one location to another
   * `int.v`: Int type
   * `bool.v`: Bool type
   * `product.v`: Product types (tuples / structs)
   * `sum.v`: Sum types (enums)
   * `own.v`: Box types
   * `shr_bor.v`: Shared references (`&T`)
   * `uniq_bor.v`: Unique reference (`&mut T`)
   * `borrow.v`:
     * `type_uniqbor_instr`: Create a new borrow
     * `type_share`: Unique borrow -> shared borrow
     * `tcx_reborrow_uniq`: Reborrow
     * `type_deref_uniq_own`: Unique borrow from behind a `Box`
     * `type_deref_shr_own`: Shared borrow from behind a `Box`
     * `type_deref_uniq_uniq`: `&mut &mut T` -> `&mut T`
     * `type_deref_shr_uniq`: `& &mut T` -> `&T`
   * `product_split.v`:
     * `tctx_split_shr_prod`: `&(T, U)` to `&T` and `&U`
     * `type_split_uniq_bor_instr` `&mut (T, U)` to `&mut T` and `&mut U`
   * `type_sum.v`:
     * `type_case_shr_inner`: Match on enum and take shared reference to contents
     * `type_case_uniq_inner`: Match on enum and take unique reference to contents
   * `function.v`
     * `type_call`, `type_letcall`: Calling a function
     * `type_fn`, `type_fnrec`: typing a function value
   * `fixpoint.v` - Fixpoint machinery for recursive types (see `src/lambda_verus/typing/examples/list.v` for an example)

### Verus proof-oriented types

In what follows, we will cover the typing rules for Verus proof-oriented types,
which together compose the primary contribution of the VerusBelt.
Since these types are unusual and not well known, we will also detail the relationship between
the type-spec rules and the Verus source.

Most Verus proof-oriented types are declared in the "Verus standard library", `vstd`, with
individual operations specified as axiomatic functions with a `requires` and `ensures` clause.
The ideal is to have a type-spec theorem in VerusBelt for every axiom in Verus;
in practice, the relationship is more complex due to limitations or simplifications,
which we detail below. (This goes both directions; sometimes the VerusBelt specs are _more_ general.)
VerusBelt focuses on the proof-oriented types; we do not attempt to
verify, e.g., Rust stdlib container types, which are also axiomatized in vstd.

Other notes:

 * In VerusBelt, many variables (e.g., local variables, function arguments) need to be boxed
   where they wouldn't be in Rust source. Following RustBelt, these boxes appear in the "de-sugaring".
   Thus, many VerusBelt specifications may have extra `box` or `own` types.
 * VerusBelt's `tracked_ty` corresponds both to Verus's `Tracked` type
   (e.g., `Tracked<PointsTo>`), and also to Verus's `tracked` variable mode
   (e.g., `let tracked x = ...`).
     * However, if a VerusBelt type is already a zero-sized type, then it doesn't need to be
       wrapped in `tracked_ty`. (The only effect of `tracked_ty` is to make something zero-sized.)
 * The Verus docs don't say whether something is an axiom or not. In the vstd source, axioms are marked either as `axiom fn` or with the attribute `#[verifier::external_body]`.

### PCell

* Paper: Sec. 3.4
* Rocq: `src/lambda_verus/typing/pcell.v`
* Verus:
  * Doc: `./verusdoc/vstd/cell/pcell/struct.PCell.html`
  * Source: `verus/source/vstd/cell/pcell.rs`

| Verus type    | Rocq type              |
|---------------|------------------------|
| `PCell<T>`    | `pcell_ty n`           |
| `PointsTo<T>` | `cell_points_to_ty ty` |

| Verus function | Rocq type-spec           |
|----------------|--------------------------|
| `new`          | `typed_pcell_from_own`   |
| `into_inner`   | `typed_pcell_to_own`     |
| `borrow`       | `typed_pcell_borrow`     |
| -              | `typed_pcell_borrow_mut` |
| `replace`      | -                        |

Remarks:

 * Verus axiomatizes `replace` as the primitive way to modify cell contents;
   we propose `borrow_mut` as a replacement (Sec. 5).
   In fact, `replace` follows immediately from `borrow_mut`.
 * Verus parameterized `PCell` by the type `T` it contains. VerusBelt parameterizes `pcell_ty` by the _size_ of the type.
 * Verus `PointsTo` and VerusBelt `cell_points_to_ty` are both parameterized by the type.
 * Verus represents `CellId` by an arbitrary integer identifier, while VerusBelt represents a cell by a _list_ of identifiers. However, these sets are in bijection.

### PPtr

* Paper: Sec. 3.2
* Rocq: `src/lambda_verus/typing/pptr.v`
* Verus:
  * Doc: `./verusdoc/vstd/simple_pptr/struct.PPtr.html`
  * Source: `verus/source/vstd/simple_pptr.rs`

| Verus type    | Rocq type              |
|---------------|------------------------|
| `PPtr<T>`     | `ptr_ty`               |
| `PointsTo<T>` | `points_to_ty ty`      |

| Verus function | Rocq type-spec          |
|----------------|-------------------------|
| `new`          | `typed_pptr_from_own`   |
| `into_inner`   | `typed_pptr_to_own`     |
| `borrow`       | `typed_pptr_borrow`     |
| -              | `typed_pptr_borrow_mut` |
| `replace`      | -                       |

Remarks:

 * Again, we prove `borrow_mut` in place of `replace`.
 * Our `PPtr` is more closely based on the `PPtr` introduced in [_Verus: Verifying Rust Programs using Linear Ghost Types_](https://dl.acm.org/doi/10.1145/3586037), but the current version of `PPtr` in Verus has evolved since then. (See footnote 1.) VerusBelt's `ptr_ty` most closely resembles Verus's `simple_pptr`, even though `simple_pptr` is not an "axiomatized" library.
 * The Verus `PointsTo` allows data to be optionally uninitialized. VerusBelt's `PointsTo` is always initialized. In VerusBelt, instead, unitialized data is represented by its own _type_ (`↯ n`; see `uninit.v`).

### Resource Algebra / PCM

* Paper: (no dedicated section)
* Rocq: `src/lambda_verus/typing/ra.v`
* Verus:
  * Doc: `./verusdoc/vstd/pcm/struct.Resource.html`
  * Source: `verus/source/vstd/pcm.rs`

| Verus type    | Rocq type |
|---------------|-----------|
| `Resource<P>` | `ra_ty`   |

| Verus function                        | Rocq type spec                     |
|---------------------------------------|------------------------------------|
| `alloc`                               | `typed_ra_alloc`                   |
| `join`                                | `typed_ra_join`                    |
| `split`                               | `typed_ra_split`                   |
| `create_unit`                         | `typed_ra_unit`                    |
| `update`                              | `typed_ra_update`                  |
| `update_nondeterministic`             | `typed_ra_update_nondeterministic` |
| `validate`                            | `typed_ra_validate`                |
| `join_shared`                         | -                                  |
| `join_shared_to_target`               | `typed_ra_join_shared_to_target`   |
| `weaken`                              | `typed_ra_weaken`                  |
| `update_with_shared`                  | `typed_ra_update_with_shr`         |
| `update_nondeterministic_with_shared` | `typed_ra_update_with_shr_non_det` |

Remarks:

 * The `P: PCM` bound is represented in Rocq by the `VerusRA` record, which mirrors the `PCM` trait, except that validity is _prophetic_ (it takes a prophecy assignment `proph_asn`). `ra.v` constructs an Iris camera from it internally: `ra_ty` owns a fragment of an authoritative resource, and an invariant (`ra_inv`) holds the authoritative element together with a prophecy observation that it is valid.
 * Because validity is prophetic, some laws are reformulated: `vra_frame_preserving_update` holds with respect to the (actual) prophecy assignment; for nondeterministic updates, the new element is chosen from the frame alone, so the validity implication must hold for all prophecy assignments; and `vra_conjunct_shared` has no validity premise.
 * `join_shared` doesn't follow from our model; it requires more investigation. We instead prove `join_shared_to_target`, which is slightly weaker (but equivalent for many PCMs).

### Storage Protocols

* Paper: Sec 3.3 ("Example: Storage Protocols")
* Rocq: `src/lambda_verus/typing/protocol.v`
* Verus:
  * Doc: `./verusdoc/vstd/storage_protocol/struct.StorageResource.html`
  * Source: `verus/source/vstd/storage_protocol.rs`

| Verus type                 | Rocq type               |
|----------------------------|-------------------------|
| `StorageResource<K, V, P>` | `storage_resource_ty`   |

| Verus function                          | Rocq type spec                                |
|-----------------------------------------|-----------------------------------------------|
| `alloc`                                 | `typed_sp_alloc`                              |
| `join`                                  | `typed_sp_join`                               |
| `split`                                 | `typed_sp_split`                              |
| `validate`                              | `typed_sp_validate`                           |
| `exchange`                              | `typed_sp_exchange`                           |
| `deposit`                               | `typed_sp_deposit`                            |
| `withdraw`                              | `typed_sp_withdraw`                           |
| `update`                                | `typed_sp_update`                             |
| `exchange_nondeterministic`             | `typed_sp_exchange_nondeterministic`          |
| `guard`                                 | `typed_sp_guard`                              |
| `join_shared`                           | -                                             |
| -                                       | `typed_sp_join_shared_to_target`              |
| `weaken`                                | `typed_sp_weaken`                             |
| `validate_with_shared`                  | `typed_sp_validate_with_shr`                  |
| `exchange_with_shared`                  | `typed_sp_exchange_with_shr`                  |
| `exchange_nondeterministic_with_shared` | `typed_sp_exchange_with_shr_nondeterministic` |

Remarks:
 * The `P: Protocol<K, V>` bound is represented in Rocq by the `VerusSP` class (`src/lambda_verus/typing/proph_protocol.v`), which mirrors the `Protocol` trait, except that `rel` is _prophetic_. The underlying logic is a variant of `src/guarding/storage_protocol/protocol.v` whose invariant additionally holds a prophecy observation that `rel` holds.
 * `guards` must hold for all prophecy assignments (guards cannot consult prophecies). For nondeterministic exchanges, the outcome is chosen from the frame and the current stored map alone. The other relations (`exchanges`, `deposits`, `withdraws`, `updates`) are checked against the actual prophecy assignment.
 * The Verus version deals in collections of ghost objects (via `Map`).
   VerusBelt doesn't have a Map-equivalent type; we prove simplified specs that deal only in singleton
   ghost objects `{[ k := v ]}`, where the key `k` is a parameter of the typing rule.
 * Storage Protocols have the same issue with `join_shared` mentioned above.

### LocalInvariant

* Paper: Sec. 4
* Rocq: `src/lambda_verus/typing/local_inv.v`
* Verus:
  * Doc:
    * `./verusdoc/vstd/invariant/struct.LocalInvariant.html`
    * `./verusdoc/vstd/macro.open_local_invariant.html`
  * Source: `verus/source/vstd/invariant.rs`

| Verus type                      | Rocq type                           |
|---------------------------------|-------------------------------------|
| `LocalInvariant<K, V, Pred>`    | `local_inv_ty {𝔄 ℭ} ty pred`        |
| -                               | `local_closer_ty {𝔄 ℭ} ty pred`     |

| Verus function                  | Rocq type spec            |
|---------------------------------|---------------------------|
| `open_local_invariant!` (start) | `typed_local_inv_open`    |
| `open_local_invariant!` (end)   | `typed_local_inv_close`   |
| `LocalInvariant::new`           | `typed_local_inv_alloc`   |
| `LocalInvariant::into_inner`    | `typed_local_inv_destroy` |

Remarks:

 * The `open_local_invariant!` macro in Verus ties together the open and close operations,
   and also forces all invariant opening to be well-nested. VerusBelt shows this well-nesting
   isn't necessary, instead using the `local_inv_closer_ty` to connect the open and close operations.
   This allows "interleaving" the starts and ends (e.g., `open A; open B; close A; close B`).
 * The verification conditions associated with `open_local_invariant!` (i.e., the specifications
   that modify the mask) are not represented in Verus source as requires/ensures clauses like
   most other specifications. These operations are special-cased in Verus's VC gen.
 * The `typed_local_inv_open` and `typed_local_inv_close` specs modify something called the
   `InvCtx` to keep track of what invariants are open (within the current function).
   This is necessary to fix the soundness hole documented in Sec. 4. ~~This concept does not
   exist in Verus, where the soundness hole remains open.~~
     * This is now fixed, see https://github.com/verus-lang/verus/pull/2476 and https://github.com/verus-lang/verus/pull/2501
 * ~~`LocalInvariant::into_inner` has a precondition on the mask (given by the `opens_invariants` clause). VerusBelt shows this precondition is not necessary (when using the invariant context strategy).~~
     * This precondition was removed in https://github.com/verus-lang/verus/pull/2533 

### AtomicInvariant

* Paper: Sec. 4.1
* Rocq: `src/lambda_verus/typing/atomic_inv.v`
* Verus:
  * Doc:
    * `./verusdoc/vstd/invariant/struct.AtomicInvariant.html`
    * `./verusdoc/vstd/macro.open_atomic_invariant.html`
  * Source: `verus/source/vstd/invariant.rs`

Similar to `LocalInvariant`, though the interaction with the invariant context is different.

| Verus type                      | Rocq type                           |
|---------------------------------|-------------------------------------|
| `AtomicInvariant<K, V, Pred>`   | `atomic_inv_ty {𝔄 ℭ} ty pred`       |
| -                               | `atomic_closer_ty {𝔄 ℭ} ty pred`    |

| Verus function                   | Rocq type spec             |
|----------------------------------|----------------------------|
| `open_atomic_invariant!` (start) | `typed_atomic_inv_open`    |
| `open_atomic_invariant!` (end)   | `typed_atomic_inv_close`   |
| `AtomicInvariant::new`           | `typed_atomic_inv_alloc`   |
| `AtomicInvariant::into_inner`    | `typed_atomic_inv_destroy` |

Remarks:

 * Verus checks that at most 1 executable, atomic instruction takes place in an `open_atomic_invariant!` block. This restriction is not represented in VerusBelt (see the limitation in Sec. 4.1).

### Atomic operations

* Paper: Sec. 4.1
* Rocq: `src/lambda_verus/typing/pcell.v`
* Verus:
  * Doc: `./verusdoc/vstd/atomic/struct.PAtomicU64.html`
  * Source: `verus/source/vstd/atomic.rs`

Though Verus has different types for non-atomic vs. atomic operations (`PCell` vs. `PAtomicU64`, etc.), VerusBelt consolidates both of them into `pcell_ty` (which is more general, as now both kinds of operations can be performed on the same type).  Thus, we use `PCell` again for the atomic operations.

| Verus type       | Rocq type                   |
|------------------|-----------------------------|
| `PAtomicBool`    | `pcell_ty 1`                |
| `PermissionBool` | `cell_points_to_ty bool_ty` |
|------------------|-----------------------------|
| `PAtomicU64`     | `pcell_ty 1`                |
| `PermissionU64`  | `cell_points_to_ty int`     |
|------------------|-----------------------------|
|     ...          |            ...              |

| Verus function            | Rocq type spec             |
|---------------------------|----------------------------|
| `load`                    | `typed_pcell_atomic_load`  |
| `store`                   | `typed_pcell_atomic_store` |
| `compare_exchange_strong` | `typed_pcell_atomic_CAS`   |


Remarks:

 * VerusBelt implements 3 atomic instructions: load, store, and CAS (the last one standing in
   for the large number of possible read-modify-write instructions: `fetch_add`, `fetch_xor`, etc.)
 * VerusBelt's sequentially consistent memory instructions (e.g., `e1 <-ˢᶜ e2`) are special
   in that they are "physically atomic", a property of their evaluation in the operational semantics 
   of our lambda calculus. Likewise, these operations are treated as special by Verus, in that
   they are allowed to occur inside an `open_atomic_invariant!` block. Again, however, recall
   the limitations of our atomicity checks (Sec. 4.1).

# Other artifact information

## Rocq axioms

We use the following standard Rocq axioms:

 * [Dependent functional extensionality](https://docs.rocq-prover.org/master/stdlib/Stdlib.Logic.FunctionalExtensionality.html#functional_extensionality_dep)
 * [Invariance by substitution of reflexive equality proofs](https://docs.rocq-prover.org/master/stdlib/Stdlib.Logic.Eqdep.html#Eq_rect_eq.eq_rect_eq)
 * [Law of Excluded Middle](https://docs.rocq-prover.org/master/stdlib/Stdlib.Logic.Classical_Prop.html#classic)

When following the instructions at the top, you should see the following output from the `Print Assumptions` line at the end:

```
COQC src/lambda_verus/typing/examples/pcell_example.v
Axioms:
functional_extensionality_dep :
  ∀ (A : Type) (B : A → Type) (f g : ∀ x : A, B x),
    (∀ x : A, f x = g x) → f = g
Eqdep.Eq_rect_eq.eq_rect_eq :
  ∀ (U : Type) (p : U) (Q : U → Type) (x : Q p) (h : p = p),
    x = eq_rect p Q x p h
```

Note though, this file only depends on a subset of the total of VerusBelt. The Law of Excluded Middle is only used by `src/lambda_verus/typing/atomic_inv.v`.

## Artifact contents

 * `verus/` - Verus source tree, release 0.2026.03.16.b1c2a95 (b1c2a951686fbc3a71a617fc2889b86fe1b63d45)
 * `verusdoc/` - Documentation for Verus vstd
 * `verusbelt-docker-image.tar` - Docker image for building VerusBelt
 * `verus-impl-docker-image.tar` - Docker image with Verus installed
 * `Dockerfile` - Dockerfile used to produce verusbelt-docker-image.tar
 * `doc/` - html documentation for key Rocq files in VerusBelt
 * `src/` - Rocq source for VerusBelt, including dependencies
   * `guarding/` - Modified version of Leaf
   * `iris/` - Iris source tree (4.3.0)
   * `stdpp/` - Stdpp source tree (1.11.0)
   * `lambda_verus/` - VerusBelt source
     * `lang/`
       * `adequacy.v` - Adequacy theorem
       * `heap.v` - Basic heap laws
       * `lang.v` - Definition of language semantics and evaluation reduction
       * `lifting.v` - Proofs of program logic primitive laws
       * `notation.v` - Defines notation
       * `proofmode.v` - Defines tactics for Iris proof mode
       * `races.v` - Theorems about data race semantics
       * `tactics.v` - Defines more tactics for Iris proof mode
       * `time.v` - Utilities for time credits
       * `lib/`
         * `memcpy.v` - Specs for memcpy
         * `new_delete.v` - Specs for new and delete
         * `spawn.v` - Specs for spawn
     * `lifetime/`
       * `lifetime_full.v` - The Leaf Lifetime Logic public interface (LeLiLo) 
       * `lifetime_internals/` - The model of LeLiLo
     * `prophecy/`
       * `prophecy.v` - Iris propositions for manipulating prophecies in the logic
       * `syn_type.v` - Definitions of syntactic types, non-prophetic interpretations, and prophetic interpretations
     * `typing/`
       * `atomic_inv.v` - Typing rules for `AtomicInvariant`
       * `base.v` - Misc setup
       * `base_type.v` - Define the "base case" for the fixpoint theorem
       * `bool.v` - Typing rules for `bool`
       * `borrow.v` - Borrowing-related typing rules
       * `cont.v` - Typing rules for continuations
       * `cont_context.v` - Continuation contexts
       * `fixpoint.v` - Fixpoint construction for recursive types
       * `freeable_util.v` - Utils about resources used to free memory
       * `function.v` - Typing rules for functions
       * `ghost.v` - Typing rules for `Ghost` type
       * `int.v` - Typing rules for `int` type
       * `inv_context.v` - Invariant contexts
       * `lft_contexts.v` - Lifetime contexts
       * `lifetime.v` - Utils about lifetimes
       * `local_inv.v` - Typing rules for `LocalInvariant`
       * `mod_ty.v` - Typing rules for `mod_ty` (transforming a type by a morphism on interpretation sorts)
       * `own.v` - Boxed types
       * `pcell.v` - Typing rules for `PCell`
       * `pptr.v` - Typing rules for `PPtr`
       * `product.v` - Typing rules for products
       * `product_split.v` - More typing rules for products, including borrowing-related rules
       * `programs.v` - Typing rules for sequencing instructions, starting and ending lifetimes, reading and writing
       * `programs_util.v` - Misc utils about typing programs
       * `programs_util_atomic.v` - Misc utils about typing programs, used for atomic invariants
       * `programs_util_own.v` - Misc utils about typing programs
       * `protocol.v` - Typing rules for storage protocols
       * `ra.v` - Typing rules for resource algebras
       * `shr_bor.v` - Typing rules for shared borrows
       * `soundness.v` - Main type-spec soundness theorem
       * `spawn.v` - Typing rules for spawning a thread
       * `sum.v` - Typing rules for sum types
       * `tracked.v` - Typing rules for the `Tracked` type
       * `type.v` - Definition of a semantic type
       * `type_context.v` - Type contexts
       * `type_sum.v` - More typing rules for sum types, including borrowing-related rules
       * `uninit.v` - Type representing unitialized memory
       * `uniq_bor.v` - Type rules for unique borrows
       * `uniq_cmra.v` - Value-observer / prophecy-controller resources (used only by `util/proph_bor.v`)
       * `uniq_util.v` - Utility lemmas for unique borrows, built on prophetic borrows
     * `util/`
       * `adequacy_util.v` - Fork of Iris adequacy machinery with slight enhancement
       * `atomic_lock_counter.v` - Helper resources for atomic invariants
       * `basic.v` - Misc utils
       * `cancellable.v` - Library of cancellable invariants
       * `cancellable_na_invariants.v` - Additional library of cancellable invariants
       * `cellmap.v` - resources for the Cell Points-To Logic
       * `discrete_fun.v` - utilities for working with discrete functions
       * `fancy_lists.v` - utilities for heterogeneous lists
       * `non_atomic_cell_map.v` - Integrating cell resources with non-atomic read and write operations
       * `proph_bor.v` - Prophetic borrows (`&proph{κ ; ξ ➤ x} P`): full borrows paired with a prophecy variable that is resolved to the borrowed value's final value; the model of unique borrows is defined in terms of these
       * `update.v` - utilities about Iris updates
       * `vector.v` - utilities about vectors
