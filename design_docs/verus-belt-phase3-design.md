# Phase 3: typing rules with place types (design)

Context: `design_docs/verus-belt-place-types-summary.md`. Start: `prophecy-ra` at `3866d11`.

## Goal of the slice

For `p ◁ &uniq{κ} (ty1 * ty2)`:
1. unfold to a place-typed form whose referent is `ProdLty (OfTy ty1) (OfTy ty2)`, and fold back;
2. reborrow field 0 at `α = κ ⊓ α'` (fresh prophecy ζ), blocking field 0;
3. use the new `&uniq{α} ty1` with the existing rules; unblock after `α` ends;
4. drop the outer while field 0 is still blocked, resolving its prophecy ξ through a
   reservation for ζ;
5. an end-to-end example.

## Decisions

### D1. Compound places in Uniq mode hold a reserved observer (3a)

`cpd_own` (ltype.v) holds `proph_bor_tok_rsv ξ c idx ζl` instead of `proph_bor_tok`, with `ζl`
existential and constrained by `⌜prfn_rsv r ζl⌝`. `prfn_rsv r ζl` (lstate.v, Σ-independent)
says that the denotation of every `PlaceProph` leaf of the refinement `r` depends only on `ζl`.

- Unfolding (`prod_ofty_unfold_uniq`) reserves for `[]` (no tokens needed); folding
  (`prod_ofty_fold_uniq`) unreserves. A leaf `OfTy ty` in Uniq mode is still `uniq_body`, with a
  plain observer.
- Switching states (`cpd_acc`) may extend the reservation by `ζl'`, given tokens for `ζl'` that
  are handed to a view shift producing the new contents (so that the tokens can be put back into
  a fresh loan that the new contents borrow).
- The reservation is never shrunk while the place is unfolded; it may over-approximate.

Why always-reserved rather than `tok ∨ rsv`: resolving while blocked must know that the blocked
leaves' denotations depend only on the reserved variables. With an existential reservation and
no constraint this is not known; with the constraint, `tok` is just the case `ζl = []`
(reserving for `[]` is free), so one form suffices.

### D2. `blocked_uniq` in pending form (3a)

`blocked_uniq κ ξi ty α lr := [†α] ={lazyE}=∗ guarded_upd lazyE @[ty_lft ty] (∃ d' g', ⧖ ∗ ofty_uniq …)`,
as `blocked_owned`. `unblock_blocked_uniq` takes a guard for `ty_lft ty`.

### D3. How place types enter the type context (3b)

- A new, *semantic* type-context element `TCtx_sem p Φ` (type_context.v), interpreted as
  `∃ v, ⌜eval_path p = Some v⌝ ∗ Φ x tid v`. This avoids an import cycle (`ltype.v` depends on
  `uniq_bor.v`, which depends on `type_context.v`) and keeps all existing machinery
  (`tctx_incl`, `typed_instr`, extraction, `unblock_tctx`) unchanged: only `tctx_elt_interp`
  matches on elements.
- The place element `p ◁ₗ{κ} lt` (new file `typing/place.v`) is `TCtx_sem p (place_uniq_own κ lt)`
  for `lt : lty 𝔄`, the place type of the *referent* of a `&uniq{κ}`. Its value has syn type
  `uniq_borₛ 𝔄 * listₛ positiveₛ`: the `&uniq` value `(l, x₀, ξi, d', g', idx)` (the index
  `idx` is ignored; `x₀` gives the values of the unblocked leaves and witnesses for the blocked
  ones) and the prophecy ids ζis of the blocked leaves, left to right.
  `lty_rfn lt x₀ ζis` computes the refinement (`PlaceIn` for `OfTy`, `PlaceGhost x ζi` for
  `Blocked`).
- Interpretation: as `&uniq{κ} (lty_fold lt)`'s own at `(d, d)` with `⧖d`, with `uniq_body`
  replaced by `ltype_own (Uniq κ ξi) lt (lty_rfn lt x₀ ζis) d' g'`.
- Specs: the current value of the place is `prfn_den (lty_rfn lt x₀ ζis)` (`place_cur`), the
  final one `uniq_bor_future` of the first component.
- Conversions: `p ◁ &uniq{κ} ty ⇔ p ◁ₗ{κ} OfTy ty` (value `(m, [])`), and the unfold/fold of
  products as `tctx_incl`s.

### D4. Field reborrow (3c.2) is an instruction (`ReBor`)

Opening the outer borrow gives its contents under a later and behind the lazy update; both the
new reborrow's payload and the blocked leaf left in the outer body need parts of them, so the
update has to be run (a later credit and a guard for `ty_lft`), which needs an instruction. The
new reborrow ζ is created as a loan; its token is used to extend the outer reservation by `[ζ]`
and is then put back into the loan, which is borrowed at `α`. Field 0 in the outer body becomes
`blocked_owned … α (PlaceGhost x1 ζi)`, built from the inheritance of the new borrow
(`uniq_lender_settle`, with a later credit stored in the wand).

### D5. Dropping the outer while blocked (3c.4) is an instruction too

The outer borrow is replaced by a fresh `&uniq{κ} ty2` (prophecy η) for the unblocked field, and
ξ is *pre-resolved, reserved*: `uniq_preresolve_reserved` with value
`((π ζ).1, (π η).1)`, which depends on `ζl ++ [η]` (by `prfn_rsv`), with η's (fresh) token only.
The old body is rebuilt, when κ ends, at the state where field 0 is still blocked at α and field
1 is blocked at κ by η (as `type_split_uniq_bor_instr`). The new `&uniq{κ} ty2` can then be
resolved by the existing `uniq_resolve`, which gives `(π η).1 = cur`. So no new sharing argument
is needed for the unblocked parts.

### D6. Unblocking (3c.3) pays with cumulative receipts held by the place

`unblock_tctx` must choose the new value before its steps, but the value of the unblocked field
is only known after opening the outer borrow (a later) and settling the reborrow's lender; and
turning the lender's equalizer `(π ζ).1 :== vπ y` into an observation (by sharing at a fresh
lifetime, `proph_eqz_obs_by_share`) needs credits depending on the depth of `y`. So the place
element holds `⧗(2 * lty_nblk lt)`: one receipt gives credits from the place's `⧖`, the other
from the `⧖` of the unblocked contents. The field reborrow gets its three `⧗1` from
`typed_instr_of_skip_sem` (via `wp_cumulative_time_receipt_linear`). `unblock_tctx` now also gets
`proph_ctx` and `uniq_ctx` (needed to close the outer borrow with a new value).

## Outcome (prophecy-ra, merge `1f10631`)

Commits: `2d5cb27` (3a), `5648c95` (3b, 3c.1, 3c.2, 3c.4), `f307d12` (3c.5, `get_first`),
`32f8622` (3c.3, `set_first`). Full build clean, no `Admitted`.

Still to do: other fields / nested places (only field 0 of a pair of leaves is covered;
`lty_rfn` treats `UniqLty`/`OwnPtrLty` as folded leaves); a general "drop while blocked" for
arbitrary place types (the current one splits off the single unblocked field as a fresh `&uniq`);
reborrowing a field of an already-blocked place; automation hints for the new rules.

## Phase 3, general: paths, place contexts, owned pointers (branch `proto/phase3-general`, `proto/phase3-ownptr`)

### Place contexts and paths (`typing/lpath.v`)

- `pctx 𝔅 𝔄` is a place type of `𝔄` with a hole of type `𝔅`, given from the root:
  `PHole`, `PFst K lt2` (hole in field 0, sibling `lt2`), `PSnd lt1 K`, `POwn n K` (hole in
  the pointee of an `own_ptr n`). `pctx_plug K lt` plugs a place type. The hole has a value
  (`pctx_get`/`pctx_set` on the root value), a path (`pctx_path`, a list of field
  selectors, innermost first), an offset (`pctx_off`, below no owned pointer), a location
  (`pctx_loc`; below an owned pointer it depends on the root value), a mode (`pctx_mode`:
  one later per owned pointer above) and a depth (`pctx_depth`: one less per owned pointer).
- Refinements: `lty_rfn lt x ζm q` (root value `x`, path `q`) with a *blocking map*
  `ζm : list (list bool * positive)` from paths of blocked leaves to the prophecy ids of
  their reborrows (`PlaceGhost`). The map replaces the earlier left-to-right list `ζis`:
  adding an entry for the path of the hole does not change the refinement of the rest
  (`pctx_rfn_blk_cons`, since sibling paths have a different selector at the branching
  point), so the plugged refinement factors as `pctx_rfn K x ζm q (hole refinement)`.
  Stale entries (after unblocking or folding) are harmless.
- Ownership: `ltype_own_plug` splits the `Owned m` interpretation of `pctx_plug K lt` at
  `(pctx_pat K p, pctx_rfn K x ζm q r)` into the hole at
  `(Owned (pctx_mode K m), pctx_depth K d, pctx_loc K (lty_size lt) x l)` and the rest
  `pctx_own K …`, which does not depend on the hole's value (`pctx_own_set`) or on new
  blocking-map entries at the hole (`pctx_own_blk_cons`). In `Uniq` mode a plugged place
  with a nonempty context is a compound place whose node is the `Owned 0` interpretation
  (`ltype_own_cp_uniq_plug`).

### Rules (`typing/place.v`)

- `type_reborrow_place_instr` (`ReBor`, hole below no owned pointer, path output
  `p +ₗ #(pctx_off K)`) and `type_reborrow_place_deref_instr` (any hole; the program
  computes the address `ReBor;; pctx_expr K p`, one load per owned pointer, with the borrow
  of the place open; `wp_pctx_expr`). Both block the leaf at `κ ⊓ α`, add
  `(pctx_path K [], ζi)` to the blocking map and extend the outer reservation by `[ζ]`.
- `unblock_tctx_place`: any hole; the current value changes only at the hole, whose value is
  the final value of the reborrow (`place_blk_fin K x`). The spec does not mention `α` (the
  spec evar of `type_endlft` is created before `α`).
- `tctx_place_change_hole`: generic change of the place type at the hole, by a conversion of
  the `Owned (pctx_mode K 0)` interpretations (below the root; the core changes, so the body
  is switched with `cpd_rebody`, whose closing view shift folds the new node back into the
  leaf of the root type by `ltype_owned_leaf_node`, which needs a simple place) or by a
  conversion in `Uniq` mode at the root. Instances: `tctx_unfold/fold_place_prod`,
  `tctx_unfold/fold_place_own` (unfold only if `pctx_mode K 0 = 0`, i.e. the pointer is not
  itself below an owned pointer, otherwise the pointee's points-to is under laters).
  `tctx_unfold/fold_uniq_prod` are the root corollaries.
- `type_write_place_instr`, `type_read_place_instr`: write (resolving the old value) / copy
  out (`Copy` types) a size-1 `OfTy` leaf below no owned pointer, without reborrowing; the
  borrow of the place is opened around the memory access.
- `tctx_drop_place` (step 2): see below.

### Step 2: dropping a place while blocked

Design choice: *drop = pre-resolve through the reservation, for a fully blocked place*. A
place all of whose leaves are blocked (`lty_blk_all`) has a refinement whose denotation
depends only on the reserved variables (`lty_blk_all_dep`), so ξ is pre-resolved
(`proph_idx_bor_gen_preresolve_rsv`, no tokens) to its current value, i.e. to the final
values of the leaves' reborrows; the body is closed again unchanged at the pre-resolved
controller (the lender gets it when κ ends). An arbitrary blocking pattern is handled by
first reborrowing the unblocked leaves (at `κ ⊓ κ`, with `type_reborrow_place_instr`) and
resolving those reborrows with the existing `uniq_resolve`; this generalizes the former
`type_drop_blocked_field0_instr` (which split off field 1 as a fresh `&uniq`) without a
new sharing argument for the unblocked leaves. Resolving unblocked leaves to their current
values directly would need the tokens (or guards) of the prophecies inside those values.

### Step 3a: owned pointers below a unique borrow

The difficulty (7.4): the closing view shift of the body has to fold an owned pointer back
at a depth one more than its pointee's, and the pointee may come back from a reborrow at an
arbitrary depth `d'` with only `⧖(S d' ⊔ g')`. Solution: *shifted receipts*. A blocked leaf
below `m` owned pointers gives back `⧖((m + S d') ⊔ g')` (`blocked_owned`); the reborrow pays
for the shift with `m` cumulative receipts stored in its inheritance
(`cumulative_persistent_time_receipt`, mask `timeN ⊆ lazyE`), which the reborrow
instruction gets from its step (`⧗(S (S d))` with `m ≤ d`). With this,
`ltype_owned_unblock_fold` (receipt `⧖((m + S d) ⊔ g)` at `Owned m`) folds owned pointers
back in a lazy update, and the node-to-leaf conversion needs no program step. Unblocking
below owned pointers needs no extra receipt (the root depth is raised to `d1 + m`).
`own_node` keeps `d ≠ 0` outside the laters.

### Step 3b: unique borrows below a unique borrow — not implemented

Unfolding `OfTy (&uniq{κ'} ty)` into `UniqLty (OfTy ty) κ'` at `Owned` mode is a pure
equivalence (`uniq_ofty_unfold_own`), but accessing the inner referent needs a context
through `UniqLty` into a nested `Uniq κ'` compound place, and then the closing view shift
of the *outer* body must, at any state, convert the nested `uniq_node` (with an inner
unfolded, possibly blocked place) back into `ofty_owned 0 (&uniq{κ'} ty)`, i.e. into a
`uniq_body` at the trivial state. That needs:
1. a *nested membership condition*: inner blocked lifetimes must be included in the outer
   pattern lifetime `κp` (today `pat_blk_lfts (PatUniq _) = []`); this holds for reborrows
   through the outer borrow (`κ ⊓ α ⊑ κ ⊑ κp`), but `pat_blk_lfts` and the Owned-mode
   unblocking lemmas would change;
2. inside the lazy update of the leaf node (guard for `κ' ⊓ ty_lft ty`, mask `lazyE`, which
   contains `timeN`): open the inner borrow (its contents are under a later; a credit can be
   obtained from the inner place's `⧗1` and a `⧖` with
   `cumulative_persistent_time_receipt_get_credits`), unblock the inner leaves, unreserve the
   inner observer, and write the trivial state, the new value and the new controller into
   the inner borrow; i.e. a nested, lazy version of `cpd_fold_uniq` usable in a closing view
   shift;
3. the outer reservation must also cover the reborrows of inner leaves (the outer
   refinement contains the inner one), so reborrowing an inner leaf extends both
   reservations (the tokens are handed back by `cpd_acc`, so this is possible), and the
   outer drop/unblock rules must traverse `UniqLty`.
None of these is a fundamental obstacle (unlike the receipt problem of 3a before the shifted
receipts), but together they amount to a nested copy of the whole place machinery (contexts
through `UniqLty`, nested `cpd_acc`, nested fold in a view shift); this was not attempted.

### Outcome (prophecy-ra, merges `8b9edfc`, `ee311b8`)

Commits: `f8193e1` (place contexts; general reborrow/unblock/unfold/fold; drop while all
blocked), `0222979` (`get_mid` example), `08e8e7a` (shifted receipts, `POwn`),
`b1091d0` (owned pointers under `&uniq`, deref reborrow, direct read/write; examples
`set_first_direct`, `get_box` in `typing/examples/place_box.v`). Full build clean; the
examples assume only `functional_extensionality_dep`. Note: `get_box_type`'s `Qed` takes
about 3.5 minutes; kernel checking of typing derivations with `own_ptr` inside `&uniq` is
slow already for the existing rules (deref + resolve of `&uniq (own_ptr 1 int * int)`
alone takes ~30 s), so the example is in its own file.

## Nested &uniq (branch `proto/nested-uniq`)

Goal: a `&uniq{κ'} ty` stored inside a Uniq-mode place (`x: &uniq{κ} (… &uniq{κ'} T …)`) can be
unfolded into a nested place, a leaf below it can be reborrowed (blocking it), unblocked after
the reborrow ends, and the outer borrow can be dropped (resolved) while the inner leaf is still
blocked.

### The context step

A nested position is given by a pair of contexts `(K1, K2)`, read as `K1 ∘ PUniq κ' ∘ K2`: an
outer context `K1 : pctx (uniq_borₛ 𝔄') 𝔄` (Owned, below no owned pointer) to a node
`UniqLty lt κ'`, and an inner context `K2 : pctx 𝔅 𝔄'` inside the referent `lt` of the inner
borrow. The place type is `pctx_plug K1 (UniqLty (pctx_plug K2 lt0) κ')`. The step is not a new
`pctx` constructor: across it the mode changes from `Owned 0` (outer node) to `Uniq κ' ξi'`
(the inner place is a compound place `cpd_own` with its *own* prophetic borrow at `κ'`, its own
prophecy variable `ξ'`, pinned body (ghost variable of its state), reservation and `cpd_tok`),
so the ownership of the plugged place does not split as a separating conjunction
(`ltype_own_plug`): reaching the hole means opening the outer borrow and then the inner one
(`cpd_acc` twice). Only one level of nesting is supported (the inner place `lt` is simple,
`lty_simple`, i.e. built from leaves, products and owned pointers), and `K1, K2` are below no
owned pointer for reborrowing/unblocking.

- Paths: the inner place's leaves get paths `pctx_path K2 (false :: pctx_path K1 [])`
  (`UniqLty` behaves like `OwnPtrLty` for paths); the blocking map stays a single map stored in
  the outer place element. Refinement: `lty_rfn (UniqLty lt κ') m ζm q =
  inr (loc m, lty_rfn lt (cur m) ζm (false :: q), ξi m)`; its denotation is
  `(cur of the inner place, fin of ξ')`, as RustHorn's value of a `&mut` in a place.
  `lty_nblk`/`lty_blk_all` look through `UniqLty`.
- The values of a nested borrow inside the place value keep stale depths and index; they are
  not part of the refinement (the node quantifies the inner depths existentially).

### The nested membership condition

`pat_blk_lfts (PatUniq p) := pat_blk_lfts p` (was `[]`). The outer body's `pat_ok κp p_out`
then says that all blocked lifetimes of the inner place are included in the *outer* pattern
lifetime `κp`. The inner state is pinned twice: by the inner ghost variable (agreeing with the
inner body) and by the outer state (`pat_uniq p_out` is the pattern the inner `cpd_own` is
interpreted at), so both agree. A reborrow of an inner leaf is at `β = κ ⊓ α`; then `β ⊑ κ ⊑ κp`
(outer condition) and `β ⊑ κ ⊑ κ' ⊑ κp'` (inner condition, `κ ⊑ κ'` from
`κ ⊑ ty_lft (lty_fold …)`), and `[†β]` follows from `[†α]` syntactically.

### Reservations

- Outer: the outer refinement contains the inner one, and its denotation also contains the
  final value of `ξ'`. `prfn_rsv` of a nested borrow refinement `(l', r', ξi')` requires
  `prfn_rsv r' ζl` *and* that `λ π, (π ξ').1` depends only on `ζl`. So unfolding reserves the
  outer `ξ` for `[ξ']` (the token of `ξ'` is taken from the inner borrow, which is not reserved
  yet, and handed back before the inner place is reserved for `[]`); reborrowing an inner leaf
  (fresh `ζ`) extends *both* reservations by `[ζ]`: the outer `cpd_acc` closer gets `1:[ζ]`,
  passes it to the inner `cpd_acc` closer, whose view shift finally puts it into the loan of
  `ζ` and borrows it at `β`.
- Dropping the outer while all leaves of the inner place are blocked: the outer denotation
  depends only on the reserved variables (`ζ`s and `ξ'`), so `ξ` is pre-resolved to it through
  the reservation (generalized `tctx_drop_place`), giving
  `fin(x) = ((fins of the inner reborrows…), fin(*x))`. The inner reservation is never released
  while unfolded; it is released when the inner place is folded back.

### The lazy nested fold

The closing view shift of the outer body (when the outer borrow is switched to the nested
node), used by the lender of the outer borrow once `κ` (hence `κp`) is dead, must turn the
nested node back into the leaf `&uniq{κ'} (lty_fold lt)` at the trivial state. It does this
lazily, inside the guarded update of `blocked_owned`, which has mask `lazyE ⊇ timeN` and a guard
`G` for `ty_lft (&uniq{κ'} …) = κ' ⊓ …`: unreserve the inner observer, open the inner borrow
(rebody from the compound body to the `&uniq` body, excluding the folded case with `cpd_tok`),
strip the later of its contents with a credit, run its lazy update, unblock and fold the inner
node (`ltype_owned_unblock_fold`; its blocked lifetimes are dead by the nested membership
condition and `[†κp]`), write the trivial state, close the inner borrow, and rebuild the
`&uniq` leaf. The inner contents come back at an arbitrary depth `d2`, while the outer leaf
needs `⧖(S (S d2) ⊔ …)`. So the nested node `uniq_node` stores `⧗2`: one cumulative receipt is
turned (with the outer `⧖`) into the credit for the later, the other bumps the inner receipt by
one; the `⧗1` of the inner `cpd_own` becomes the `⧗1` of the rebuilt `uniq_body`. Unfolding is
therefore an instruction (it needs the `⧗2`, and a credit to run the outer payload); so is
folding back (the new inner index is only known after running the outer node).

### Rules (`typing/place_nested.v`)

- `type_unfold_place_uniq_instr` / `type_fold_place_uniq_instr`: at the root,
  `p ◁ₗ{κ} OfTy (&uniq{κ'} (lty_fold lt))` ⇔ `p ◁ₗ{κ} UniqLty lt κ'` (lt compound, simple,
  unblocked), e.g. `lt = ProdLty (OfTy ty1) (OfTy ty2)`.
- `type_reborrow_place_nested_instr`: reborrow the leaf at `(K1, K2)` at `κ ⊓ α`; the program
  loads the inner pointer (`!(p +ₗ #off1) +ₗ #off2`).
- `unblock_tctx_place_nested`: after `κ ⊓ α` ends.
- `tctx_drop_place_cpd`: drop any compound place all of whose leaves (also through `UniqLty`)
  are blocked.

### Outcome (branch `proto/nested-uniq`)

Implemented as designed. Additional lemmas: `proph_bor.v`: `proph_idx_bor_gen_tok_acc`
(borrow the token of an unreserved borrow's variable), `proph_idx_bor_gen_acc_rebody_rsv`
(rebody and reserve on closing, tokens handed to the closing view shift); `ltype.v`:
`leaf_uniq_unblock`, `cpd_own_unblock_fold` (the lazy fold of the nested compound place),
`uniq_node_unblock_fold`, `ltype_owned_leaf_node_uniq`; `lpath.v`:
`pctx_rfn_blk_cons_below`, `pctx_own_blk_cons_below` (entries for paths below the hole);
`place.v`: `tctx_drop_place_cpd` (old `tctx_drop_place` is a corollary).
Examples (`typing/examples/nested_uniq.v`, ~50 s): `get_inner_first`
(`fn<'a,'b>(&'a mut &'b mut (i32,i32)) -> &'a mut i32`, returns `&mut (**x).0`, drops `x`
while both inner leaves are blocked; spec `fin(x) = ((fin(ret), cur(**x).1), fin(*x))`) and
`set_inner_first` (reborrow `(**x).0` at `'a ⊓ 'γ`, write 5, end `'γ`, unblock, fold back,
resolve; spec `fin(x) = ((5, cur(**x).1), fin(*x))`).

Limitations (not attempted):
- Unfolding/folding a nested borrow only at the root of the outer place (`K1 = PHole`).
  Below the root (`&uniq{κ} (&uniq{κ'} T * U)`), the outer body has to be switched to the
  new node *and* its reservation extended by `[ξ']` in the same opening (the knowledge
  `ξ' ∈ ζl` would be lost when repacking `cpd_own` in between), i.e. a `cpd_rebody` with
  reservation extension, and `tctx_place_change_hole` would need `lty_simple` generalized
  to places containing `UniqLty` (the `UniqLty` case of `ltype_owned_unblock_fold` exists
  only at `Owned 0`, `uniq_node_unblock_fold`). Reborrowing/unblocking are already stated
  for any `K1` below no owned pointer.
- One nesting level (the inner place is `lty_simple`), no nested borrow below an owned
  pointer (its node would be under laters), no `UniqLty` with `K2 = PHole` (reborrowing the
  whole referent `**x` as a place leaf), no further unfolding of the inner place after the
  nested unfold (the nested unfold unfolds `lt` in one go, e.g. a pair of leaves).

## Owned roots and moves (branch `proto/owned-roots`)

Goal (roadmap steps 1 and 2): places rooted at an owned location (the pointee of an
`own_ptr n`, i.e. a `Box` or the stack slot of a local variable), whose leaves can be
borrowed, unblocked, read, written, moved out and re-initialized.

### The owned place element (`typing/place_own.v`)

- `p ◁ₗown{n} lt := TCtx_sem p (oplace_own n lt)`, value `((l, x₀), ζm) : at_locₛ 𝔄 * blk_mapₛ`
  (the value of the owned pointer and a blocking map, as for `p ◁ₗ{κ} lt`), interpreted as
  `∃ D d g, ⧖D ∗ ⧗(lty_nblk lt) ∗ ⌜v = #l⌝ ∗ ⌜S d ≤ D ∧ g ≤ D⌝ ∗ freeable_sz n (lty_size lt) l ∗
   ltype_own (Owned 1) lt (lty_rfn lt x₀ ζm []) d g tid (l, repeat [] (lty_size lt))`.
- **Mode `Owned 1` at the root.** This is exactly the shape of `own_ptr`'s ownership (the
  pointee's points-to now, its ghost ownership under one later), so the conversions
  `tctx_own_to_oplace` / `tctx_oplace_to_own` (`p ◁ own_ptr n ty ⇔ p ◁ₗown{n} OfTy ty`) are
  plain `tctx_incl`s. The price: every leaf is below at least one later
  (`pctx_mode K 1 = 1 + pctx_mode K 0`), so leaf operations strip `▷^k` with credits of their
  step, and the borrow rule pays the shifted receipt of `blocked_owned` with `k` cumulative
  receipts, as `type_reborrow_place_deref_instr`. (With `Owned 0` the conversion
  `own_ptr → place` would need a program step.)
- **No outer borrow.** Blocking a leaf just stores the inheritance of the new borrow (pending
  ownership, `blocked_owned`); there is no reservation, no `cpd_acc`, no pattern lifetime.
  Unblocking fires it after `α` ends, with a guard for `ty_lft ty` from `L`
  (`lctx_lft_alive E L (ty_lft ty)`), and one cumulative receipt per blocked leaf (credits
  for the later of the equalizer, the `▷^k` of the contents and `proph_eqz_obs_by_share`).
- **Unfolding.** Products at any path (`tctx_(un)fold_oplace_prod`, via
  `tctx_oplace_change_hole` and `prod_ofty_unfold_own m`); owned pointers at a path with one
  later (`pctx_mode K 1 = 1`, i.e. not below another box): the later in front of the pointee's
  points-to is stripped by timelessness (`ownptr_ofty_unfold_own1`). Below two laters this is
  impossible without credits (`▷▷P ⊬ ◇P`), so unfolding a box inside a box inside the root
  would need an instruction — not done. Folding back works at any depth.
- **Leaf rules** (all values of size 1, at any path; the address is `pctx_expr K p`, one load
  per owned pointer, evaluated with `wp_pctx_expr` and a trivial guard, since owned locations
  have no ghost cells, `pctx_loc_empty`):
  `type_borrow_oplace_instr` (`(Skip;;Skip);; pctx_expr K p`, needs
  `elctx_sat E L (ty_outlives_E ty α)`, gives `w ◁ &uniq{α} ty` and blocks the leaf at `α`),
  `unblock_tctx_oplace`, `type_read_oplace_instr` (`Copy`), `type_move_oplace_instr`
  (`StackOkay`), `type_write_oplace_instr`.

### Moves (step 2)

- **Moved-out leaves are `OfTy (↯ (ty_size ty))`**, whose value is the old contents of the
  cells (a `vec val`). No new `lty` constructor; folding a place with moved-out leaves gives a
  type with `uninit` components (e.g. `own_ptr n (↯ 1 * int)`), so the existing
  `own_ptr`/`uninit` rules (e.g. `write_own`, which changes the pointee type) still apply after
  folding.
- Moving out and writing change the type of the leaf, hence the syntactic type of the root:
  `pctx_retype K 𝔅' : pctx 𝔅' (pctx_root K 𝔅')` (same siblings and pointers) with
  `pctx_reset K x y` for the value (`lpath.v`). All the context operations commute with it
  (`pctx_own_reset`, `pctx_loc_reset`, `pctx_get_reset`, …). In examples the retyped context
  reduces by `simpl` to the expected place type.
- `type_write_oplace_instr` writes `ty'` over `ty` (same size 1), resolving the old value
  (`resolve E L ty Φ`; for `↯ 1` this is `uninit_resolve`), so it covers both re-initializing a
  moved-out leaf and assigning to an initialized one. The new value may be deeper than the
  old one below `k0` boxes, so the root depth is raised to `db + k0`; the write step gives
  cumulative receipts for this (`wp_cumulative_time_receipt_linear`, with credits from one
  receipt via `cumulative_persistent_time_receipt_get_credits`).
- Moving out of a `&uniq`-rooted place is not added (not allowed in Rust). Assigning to a
  `&uniq`-rooted leaf (`type_write_place_instr`) is still restricted to size 1, the same type,
  and leaves below no owned pointer; any size would need a memcpy-style rule (`p <-{n} !q`)
  opening the borrow around `wp_memcpy`, and a different type would need the retyping of the
  outer core (`cpd_rebody`) — deferred to roadmap step 6.

### Examples (`typing/examples/place_own.v`)

- `set_snd`: `fn set_snd(mut x: (i32, i32)) -> i32 { { let r = &mut x.1; *r = 5; } x.0 = 3; x.1 }`,
  spec `result == 5`: borrow of `x.1` at a fresh lifetime, write through it, end the
  lifetime, unblock, direct write of `x.0`, copy of `x.1`, fold, free.
- `box_pair`: `fn box_pair(mut b: Box<(Box<i32>, i32)>) -> Box<(Box<i32>, i32)> { { let r =
  &mut b.0; **r = 7; } let c = b.0; b.0 = c; b }`, spec `*result == (Box(7), old(b).1)` (same
  inner address): borrow `.0` (an owned pointer), write through it, unblock, move `.0` out
  (leaf `↯ 1`), re-assign, fold.

Not covered: values of size ≠ 1 (memcpy), unfolding a box below two laters, `&uniq` leaves
below owned roots unfolded as nested places (`UniqLty`), shared borrows of owned places,
dropping an owned place with blocked leaves (fold first; a blocked leaf has to be unblocked).

## Shared mode (branch `proto/shared-places`)

Goal (roadmap step 3): shared borrows of a leaf of a place (rooted at a unique borrow or
at an owned location), reads of shared leaves, unblocking after the shared lifetime, and
places below shared references.

### Shared-blocked leaves (`ltype.v`, `lstate.v`)

- New place type `ShrBlocked ty α` (core `OfTy ty`, pattern `PatShrBlocked α`, blocked
  lifetimes `[α]`, refinement `PlaceIn` of its value: the value of a shared leaf does not
  change, so there is no blocking-map entry and no reservation).
- Interpretation in `Owned m` (`shr_blocked_owned`, as RefinedRust's
  `shr_blocked_lty_own`): `∃ x, rel lr x ∗ (@[α] &&{g+1}&&> l #↦!∗ phys x) ∗
  ty_shr α x d g ∗ ([†α] ={lazyE}=∗ ofty_owned m ty x d g l)`. The contents are borrowed
  at `α` (`llftl_borrow`), the borrow of the points-to becomes a guard
  (`llftl_bor_guard`), the borrow of the ownership predicate is shared (`ty_share`, whose
  `d` steps are paid with later credits of the instruction), and the inheritance (with a
  stored later credit) gives the contents back at the same depths.
- The leaves of place types in `Owned` mode are `leaf_owned_s` (`leaf_owned` plus the
  shared-blocked case); the leaf bodies of unique borrows (`leaf_node`, `uniq_gbody`) are
  unchanged, so all of `uniq_util.v`/`uniq_bor.v` is untouched. In `Uniq` mode (a place at
  the root of a unique borrow) `PatShrBlocked` is interpreted as `OfTy` (the rules only
  share below the root, `pctx_nonempty K`). `ltype_owned_leaf_node` now requires a
  compound place (`lty_is_cpd`), its only uses.
- Unblocking in a lazy update (`leaf_owned_s_unblock`, used by the closing view shifts of
  compound bodies and `ltype_owned_unblock_fold`): `pat_ok κp` gives `[†α]` from `[†κp]`,
  and the inheritance is fired; the receipt is unchanged.
- `lty_nblk (ShrBlocked …) = 0`: unblocking needs no receipt, since the value does not
  change and the later in front of the contents of the outer borrow is paid by the step
  of `unblock_tctx` (the outer borrow is opened before the step, the new value is known
  before it).

### Rules (`typing/place_shr.v`)

- `type_share_place_instr` (`Share;; pctx_expr K p`, `K` nonempty, any path, also below
  owned pointers): `p ◁ₗ{κ} K[OfTy ty]` ⇒ `w ◁ &shr{κ ⊓ α} ty; p ◁ₗ{κ} K[ShrBlocked ty (κ ⊓ α)]`,
  needs `lctx_lft_alive E L (κ ⊓ α)`; the value of the place is unchanged, the reference
  is `(pctx_loc K …, pctx_get K x)`.
- `type_read_place_shr_instr` (noderef, size 1, `Copy`): copy out of a shared-blocked
  leaf while `β` is alive (opens the outer borrow for the persistent sharing information,
  closes it at the same state; the gho of the value from `copy_shr`).
- `unblock_tctx_place_shr`: after `κ ⊓ α` ends, `K[ShrBlocked ty (κ ⊓ α)]` ⇒ `K[OfTy ty]`,
  same value.
- Owned roots: `type_share_oplace_instr` (needs `ty_outlives_E ty α` and `α` alive),
  `type_read_oplace_shr_instr`, `unblock_tctx_oplace_shr` (no outer borrow: the
  inheritance is fired directly).
- Places below shared references: no place element and no `Shared` borrow kind. The
  ownership of `&shr{κ} ty` is persistent, so the place type of the referent never changes
  (nothing is blocked). `tctx_shr_place` (any noderef `K`, i.e. nested fields):
  `p ◁ &shr{κ} (lty_fold K[OfTy ty])` ⇒ `p +ₗ #(pctx_off K) ◁ &shr{κ} ty` (keeping `p`),
  from the structural sharing predicate of products (`shr_pctx_split`). Reads are reads
  through such references (`read_shr`); owned pointers and unique borrows below a shared
  reference are traversed by `type_deref_shr_own_instr`/`type_deref_shr_uniq_instr`
  (structural sharing predicates of steps 4–5a).

### Examples and outcome

- `typing/examples/place_shr.v`: `share_first` (`fn<'a>(x: &'a mut (i32,i32)) -> i32`:
  share `x.0` at `'a ⊓ 'b`, read it through the reference and directly while shared, read
  `x.1`, end `'b`, write `x.0 = 5`; spec `result = old(x).0 ∧ fin(x) = (5, old(x).1)`;
  Qed ~43 s), `get_box_shr` (`*( *r).0` for `r: &(Box<i32>, &mut i32)`; ~4 s),
  `share_local` (shared borrow of a field of a local; ~13 s).
- `typing/examples/place_shr_mid.v`: `get_mid_shr` (`( *r).0.1` for
  `r: &((i32,i32),i32)`); its kernel check takes ~14 minutes (cause not identified: the
  derivation is tiny; avoiding `simpl` in the spec proof and stating the offset/type of
  `tctx_shr_place` as equations did not help), hence its own file.
- All assume only `functional_extensionality_dep`.
- Note for automation: a spec that mentions a lifetime created inside the body (e.g. a
  sibling `ShrBlocked ty (α ⊓ β)` in the context `K` of `type_read_place_instr`) cannot
  instantiate the spec evar of `type_let`; `simpl` before `reflexivity` removes it
  (`pctx_get` does not depend on the siblings).
- Not done: a unique borrow below a shared reference in an example (the derivation with
  `type_deref_shr_uniq_instr` goes through, but its `Qed` did not finish in 15 minutes);
  a `pctx`-parametric deref rule below `&shr` (owned pointers in `K`): composing
  `tctx_shr_place` with the existing deref rules covers it; dropping/resolving a `&uniq`
  place while a leaf is shared-blocked (unblock first); shared borrows of the root of a
  place (`K = PHole`); nested (`UniqLty`) places.

## Sums (branch `proto/sum-places`)

Goal (roadmap step 4): places holding sums (`xsum_ty tyl`), with case analysis on a place,
reborrows / borrows / reads / writes / unblocking of (subplaces of) the payload through the
general rules, and assignment of a new variant.

### The sum place type and the context step

- `SumLty tyl i lt : lty (Σ! 𝔄l)` (`ltype.v`): a sum of variant `i` whose payload has place
  type `lt : lty (𝔄l !!ₗ i)` (as RefinedRust's `EnumLtype`). Its folded type is
  `xsum_ty (hlist_set tyl i (lty_fold lt))` (the type of variant `i` replaced by the folded
  payload), and its size `S (max_hlist_set ty_size tyl i (lty_size lt))`; so `lty_size_fold`,
  `lty_fold_core` hold and folding needs no well-formedness side condition.
  `lty_fold (SumLty tyl i (OfTy (tyl +!! i))) = xsum_ty tyl` (`lty_fold_sum_ofty`).
- Refinements (`lstate.v`): `prfn_struct (xsumₛ 𝔄l) := psum prfn 𝔄l * list val` (the payload
  refinement at its variant, and the padding); `prfn_sum i r pad`; `PatSum`.
  `lty_rfn (SumLty tyl i lt) x` is `prfn_sum i (lty_rfn lt y …) x.2` if `x.1 = pinj i y`
  (`psum_proj`), and a constant dummy refinement otherwise (not owned).
- Interpretation: `sum_node` = tag `#i` ∗ payload ∗ padding (as `split_pt_xsum_cells''`), no
  laters (the tag and padding have no ghost state), at any mode; in `Uniq` mode a compound
  place (`cpd_own`) whose node is the `Owned 0` interpretation. Laws: core, depth
  monotonicity, `sum_ltype_imp_unblockable`, the `SumLty` cases of
  `ltype_owned_unblock_fold`/`ltype_owned_leaf_node`/`uniq_node_unblock_fold`,
  `sum_ofty_unfold_own` (`OfTy (Σ! tyl)` at `(pinj i y, pad)` ⊣⊢ `SumLty tyl i (OfTy …)`).
- Context step `PSum tyl i w K` (`lpath.v`): offset 1, no later, path selector `false`.
  `w : ~~(𝔄l !!ₗ i)` is a default payload value, used only by `pctx_get`/`pctx_loc` for
  values of other variants (`~~𝔄` need not be inhabited). Laws that hold only for values of
  the variants of `K` take `pctx_in K x` (`pctx_rfn_set`, `pctx_own_set`, `pctx_set_get`),
  which follows from the ownership of the rest of the place (`pctx_own_in`).
  `pctx_rfn_rsv_hole` became `pctx_rfn_rsv_mono`.
- Limitations of the context step: retyping a hole (moves, writes of another type) is not
  supported through a sum (`pctx_nosum`; `pctx_root` would need the variant list updated
  at `i`, with transports of `fin`/`!!ₗ`); places below shared references are restricted
  to fields of products (`pctx_fields`; sharing a sum gives the sharing predicate of the
  actual variant only).

### Case analysis (`typing/place_sum.v`)

The variant of the current value of a place is known in the proof (the value is part of
the place element), so the case rules unfold the leaf themselves; no specification
precondition (which would need `proph_obs_sat` and hence the axiom `eq_rect_eq`) is used.
Branch `i` is typed in the context with `K[SumLty tyl i (OfTy (tyl +!! i))]` (premises as
`[∗ nat] i < length 𝔄l, …`), with the same value.
- `type_case_place` (`&uniq`-rooted, below the root, `pctx_noderef K`, `pctx_simple K`):
  open with `cpd_rebody`, read the tag (guard of the cells from the place's base guard),
  close with the new node.
- `type_case_place_root` (at the root): `cpd_unfold_uniq` into the sum place, then
  `cpd_acc` around the read.
- `type_case_oplace` (owned places, any path, address `pctx_expr K p`).
- Folding back, unconditionally: `tctx_fold_place_sum` (via `tctx_place_change_hole'`, which
  drops the unused denotation condition of `tctx_place_change_hole`), `tctx_fold_oplace_sum`.
- New variant: `type_sum_assign_oplace_instr` (`pctx_expr K p <-{Σ i} q`, payload of size
  1, owned places): resolves the old value, writes tag and payload, keeps the padding.
  Not done: the unit variant for owned places (`<-{Σ i} ()`), and new variants for
  `&uniq`-rooted places (the size-1 restriction of `type_write_place_instr` applies).

### Examples (`typing/examples/place_sum.v`, ~100 s)

- `get_some_first`: `fn<'a>(x: &'a mut Option<(i32,i32)>) -> Option<&'a mut i32>`, `match x
  { Some(p) => Some(&mut p.0), None => None }`; in `Some`, the payload is unfolded, `p.0`
  and `p.1` are reborrowed (`PSum _ 1 _ (PFst PHole _)`), the second resolved, `x` dropped
  while both leaves are blocked; spec `fin(x) = Some((fin(r), cur.1))`. Qed ~22 s.
- `bump`: a local `Option<i32>`: `None => x = Some(0)` (`type_sum_assign_oplace_instr`),
  `Some(_) => *(&mut x.0) = 7` (borrow of the payload, unblock, fold). Qed ~18 s.
- `set_some`: `fn<'a>(x: &'a mut Option<i32>)`, `if let Some(v) = x { *v = 5 }` with a
  direct write (`type_write_place_instr` at `PSum _ 1 _ PHole`). Qed ~14 s.
- All assume only `functional_extensionality_dep` (`typed_body_vacuous` is avoided: it uses
  `proph_obs_sat`, hence `eq_rect_eq`). The obligations of `xsum_ty` were made axiom-free
  (`induction tyl` instead of `dependent destruction`), since every place type now mentions
  `xsum_ty`.

### Finding on kernel time

`solve_typing` proofs of `lctx_lft_alive E L α` in function contexts whose `fp_E` mentions
sum types take ~40 s of kernel time each at `Qed` (~2 s for `&uniq (int * int)`, 0.06 s for
`&uniq int`); the elaborated proof term is tiny (`lctx_lft_alive_external … (elem_of_list_here
…)`), so the time is spent converting `fp_E …` with the partially reduced list. Proving the
membership after `rewrite /fp_E /=` takes ~1 s. The examples prove `α` alive once (`Alv`)
and reuse it, which brought `get_some_first`'s `Qed` from ~6.5 min to 22 s. The same
pattern may help the other slow examples (not checked; `get_mid_shr` has no sum in its
signature, so its cost has another source).

## Resolve and drop (branch `proto/resolve-drop`)

Goal (roadmap step 5): give up a place element with an arbitrary pattern, in one rule: a
`&uniq`-rooted place is resolved (its prophecy pre-resolved to the current value of the
place), an owned place is resolved and freed.

### Places rooted at a unique borrow (`typing/place_resolve.v`)

`type_resolve_place_instr`: `p ◁ₗ{κ} lt` (compound `lt`, `lty_uniq_rslv lt`) is given up by
the program `skipn (S (lty_nunblk lt))` (one step per unblocked leaf, one to open the
borrow), with the spec `fin(x) = place_cur lt x`: the final values of the reborrows at the
blocked leaves, the current values at the unblocked ones. `lty_uniq_rslv`: leaves `OfTy` or
`Blocked`, also below owned pointers (`OwnPtrLty`) and sums (`SumLty`); nested unique
borrows (`UniqLty`) with blocked leaves only; no `ShrBlocked`. It generalizes
`tctx_drop_place_cpd` (all leaves blocked) and replaces the manual "reborrow every
unblocked leaf at `κ ⊓ κ` and resolve the reborrows".

- **No type condition on the leaves.** The contents of the leaves are not consumed: they go
  back to the lender when `κ` ends, at the same values. What is needed are the prophecy
  tokens of the current values of the unblocked leaves (the pre-resolved value depends on
  them); they are obtained by sharing each leaf at a fresh lifetime
  (`proph_eqz_obs_by_share`), as when unblocking.
- **Fresh variables per unblocked leaf.** The pre-resolution must happen while the borrow
  is open and needs, besides the reservation, tokens for everything the value depends on.
  Instead of collecting the (guarded) tokens of all leaves at once, each unblocked leaf
  gets a fresh prophecy variable `η` (`ltype_owned_rslv`, phase 1, ghost only): the outer
  prophecy is pre-resolved through its reservation to the denotation of the refinement in
  which the unblocked leaves are `PlaceGhost y η` (tokens of the fresh `η`s; new lemma
  `proph_idx_bor_gen_preresolve_rsv_acc`, and `cpd_preresolve` for compound places); then
  (phase 2) each `η` is resolved to the current value of its leaf, independently of the
  others, and the body is closed at the refinement with the `η`s (the relation of a leaf
  to its contents is the equalizer given by the observation). Closing at a refinement
  that differs from the one of the place element is harmless: the lender's view shift
  accepts any refinement.
- **One step per unblocked leaf.** Sharing a leaf costs later credits depending on its
  depth (`rslv_cost`); they cannot be paid by parallel step-updates, because opening the
  token guards keeps `NllftG` open across laters. A single program step gives one batch of
  credits (`advance_credits`), independent of the width of the place, so the instruction
  takes `1 + lty_nunblk lt` steps (`ctask c k R`: `R` given `k` batches of `c` credits;
  `wp_skipn_ctask`).
- **Shared-blocked leaves: unblock first.** The tokens of the value of a shared-blocked
  leaf are guarded by its shared lifetime `α`, which may still be alive (e.g. a returned
  `&shr` of a field) or not; the place does not know. Supporting them would need `α` alive
  from `L` and the guard of `ty_shr_guard_proph` at `α` (the value does not change, so its
  contribution to the final value is its current value). Not done; such leaves have to be
  unblocked (`unblock_tctx_place_shr`) before resolving.
- **Nested `&uniq` with unblocked leaves: fold first.** Their current values are inside
  the inner borrow; resolving them would need to open the inner borrow too (a nested copy
  of the argument). Fold the nested place back (`type_fold_place_uniq_instr`) and keep
  it as an `OfTy (&uniq …)` leaf, which is resolved like any unblocked leaf (sharing a
  `&uniq` gives the token of its prophecy).

### Places rooted at an owned location

- `lty_resolve E L lt Φ` (a semantic judgement, like `resolve`, with instances per
  constructor): the `Owned m` interpretation of `lt` is consumed in `m + d*(g+1)` steps
  (in parallel, `step_fupdN_sep`) to `⟨Φ x⟩`, giving back the memory owned by the place
  (`lty_omem m lt`). Instances: `lty_resolve_ofty` (from `resolve` of the type; moved-out
  leaves `OfTy (↯ n)` by `uninit_resolve`), `lty_resolve_prod`, `lty_resolve_own`,
  `lty_resolve_sum`, and `lty_resolve_just` (any place, `True`: blocked and
  shared-blocked leaves are forgotten).
- `resolve_tctx_cons_oplace` (implicit drop at a jump/return) and
  `type_resolve_oplace_instr` (`Skip`): resolve and leak, for any pattern ("forget without
  free"). A blocked leaf is just forgotten: its lender keeps the `&uniq`, and gets the
  contents back when the lifetime ends (the inheritance is the place's, not the
  lender's).
- `type_drop_oplace_instr`: program `drop_boxes lt p;; delete [#n; p]`: resolves the
  leaves and frees the memory of the place and, recursively, the pointees of its unfolded
  owned pointers (`OwnPtrLty`). Requires `lty_freeb lt` (no `Blocked`/`ShrBlocked` leaf
  in the memory of the place): their memory is lent, it must not be freed while blocked.
  A pointee with a blocked leaf (or whose size is not `n`) is not freed but leaked
  (`own_freeb`); owned pointers in folded leaves (`OfTy (own_ptr …)`) are resolved by
  their type and leaked, as by `type_delete_instr`.
- `lty_omem m lt`: the points-to of the memory of the place, and for each freed pointee,
  its points-to and `▷^m freeable` (as in `own_node`). The rights to free are under laters;
  `drop_boxes` computes the address of a pointee again (from the root, one load per owned
  pointer above, as `pctx_expr`) before freeing it, and these steps strip the laters
  (`wp_drop_boxes`, with an evaluation hypothesis counting `k` steps, `m ≤ k + 1`). Credits
  would not do: their number would grow with the number of boxes.

### Places below shared references

Nothing to do: there is no place element (step 3); `p ◁ &shr{κ} ty` is dropped like any
element (`shr_resolve`, `resolve_just`).

### Examples (`typing/examples/place_resolve.v`, ~50 s)

- `get_last`: `fn<'a>(x: &'a mut (Box<i32>, (Option<i32>, i32))) -> &'a mut i32 { &mut x.1.1 }`,
  the box unfolded below `x`; `x` is resolved while `.1.1` is blocked and `*x.0`, `x.1.0`
  are not; spec `fin(x) = (cur.0, (cur.1.0, fin(ret)))`. Qed 7.5 s.
- `drop_local`: `fn(b: Box<(Box<i32>, Option<i32>)>) -> i32 { let v = *b.0; b.1 = Some(5); v }`:
  move out of the inner box, write a variant, drop `b` (frees the inner box and `b`);
  spec `result = *old(b).0`. Qed 15 s.
- Both assume only `functional_extensionality_dep`.
- Kernel time: `α` alive proved once (`Alv`, as in `place_sum.v`). New finding:
  `solve_typing` for `tctx_extract_ctx` with an unreduced `pctx_plug K lt` / `tyl +!! i`
  in the extracted elements (the output context of `type_sum_assign_oplace_instr` below
  a nonempty context) did not finish in 10 minutes (elaboration, not kernel); `simpl`
  first and it is immediate.

## Step 6: generalizations (branch `proto/generalize`, merge `23f1e16`)

Commits: `d712831` (6.1), `a2a314f` (6.2), `4c47be9` (6.3), `8fb3461` (6.6), `4232b76`
(6.4), `87c66ac` (6.5). Full build clean; all new examples assume only
`functional_extensionality_dep`.

### 6.1 Assign, copy and move of any size (`typing/place_memcpy.v`)

memcpy-style rules (`e1 <-{n} !e2`, `wp_memcpy_guarded`), with the address of the leaf
computed by `pctx_expr K p` (any path, also below owned pointers; one load per pointer),
as `type_memcpy_instr` (`typed_read` for the source, `typed_write` for the destination):
- owned places: `type_memcpy_oplace_instr` (copy into a leaf from a readable path,
  resolving the old value; the leaf's type becomes the new type, `pctx_nosum K`,
  `pctx_retype`), `type_memcpy_oplace_same_instr` (same type, any `K`, also through
  sums; `pctx_set`, new lemma `pctx_loc_set`), `type_memcpy_from_oplace_instr` (move out
  into a writable path; the leaf becomes `OfTy (↯ n)`, `pctx_nosum K`; the ghost cells of
  the contents go to the destination by the source's "retether"),
  `type_memcpy_copy_from_oplace_instr` (copy of a `Copy` value, any `K`);
- places rooted at a unique borrow (same type, any nonempty `K`): `type_memcpy_place_instr`
  (assignment, old value resolved) and `type_memcpy_from_place_instr` (copy of a `Copy`
  value). The borrow of the place is opened (`cpd_acc`) for the whole instruction: the
  address computation (`wp_pctx_expr_mask`, a mask-generic `wp_pctx_expr`, since the
  borrow is opened after the first step, whose credits it needs), the read of the
  source and the copy. The first step's cumulative receipts (`wp_cumulative_time_receipt_linear`)
  give the credits and raise the depth of the place to the new value's depth plus the
  number of owned pointers above the leaf.
- Masks: a rule with a `typed_write` destination must put `wp_fupd` before the step
  lemma (its closing update is at `⊤`), a rule with `cpd_acc`/`typed_read` closings after
  it (at `⊤ ∖ ↑advN`), or use `fupd_mask_mono`.
- Not done: moves and retyping writes through sums (`pctx_root` would need the variant
  list updated); changing the type of a leaf of a `&uniq`-rooted place: the folded type of
  the referent is fixed by the lender of the outer borrow (`cpd_rebody` keeps `ty`, its
  closing view shift must give back the leaf at the old folded type), so a retyping
  assignment could only be temporary (as a move out of `&mut`, which Rust forbids);
  same-type assignment is what Rust allows through `&mut`.

Examples (`typing/examples/place_memcpy.v`, only `functional_extensionality_dep`):
`replace_first` (move a pair out of a field of a local and another pair in),
`set_first_pair` (copy a pair out of a field behind `&mut` and assign it; resolve),
`take_inner` (move a pair out of a box inside a box, drop the place).

### 6.2 Nested unique borrows: any depth, below the root and below boxes

- **Folding back at any depth.** `lty_simple` now includes `UniqLty lt _` (with `lt`
  simple), so places may contain nested borrows at any depth (`&uniq &uniq &uniq …`), also
  below owned pointers. `ltype_owned_unblock_fold` (the lazy fold of a node into the leaf
  of its folded type, used by all closing view shifts of compound bodies) handles
  `UniqLty` at any mode `Owned m`: it strips the `m` laters in front of the inner place
  and opens the inner borrow with credits obtained from one of the node's receipts,
  folds the inner place back recursively (`ltype_uniq_unblock_fold`, `cpd_own_unblock_fold`
  taking the fold of the inner node as a hypothesis `owned0_unblock_fold`), and bumps the
  inner receipt by `m + 1` with the others. Hence the node of `UniqLty` below `m` owned
  pointers holds `⧗(2 + m)` (was `⧗2`) and, new, `time_ctx`: closing view shifts of
  `tctx_incl`s (e.g. `tctx_place_change_hole`) have no `time_ctx`, so the node carries it
  (it is persistent). `ltype_owned_unblock_fold` and `ltype_owned_leaf_node` now take
  `proph_ctx` and `uniq_ctx` (the inner borrow is unreserved and rebodied).
  `uniq_node_unblock_fold`/`ltype_owned_leaf_node_uniq` are corollaries.
- **Unfolding below the root.** `type_unfold_place_uniq_deep_instr` /
  `type_fold_place_uniq_deep_instr` (and `…_prod_…` instances): at the hole of any
  nonempty simple `K1`, also below owned pointers. Unfolding switches the outer body to
  the new node and extends the outer reservation by the inner prophecy variable in the
  same opening: new `proph_idx_bor_gen_rsv_acc_rebody_ext` (`proph_bor.v`) and
  `cpd_rebody_ext` (`ltype.v`); the token of the inner variable is borrowed from the inner
  body, handed to the outer closer and back. The node's `⧗(2 + m)` come from the second
  program step (`Seq Skip Skip`), the credits for the `m` laters from the first. Folding
  uses `cpd_rebody` (the reservation keeps the inner variable; it may over-approximate).
- **Further unfolding of the nested place.** `tctx_place_nested_change_hole` (instances
  `tctx_(un)fold_place_nested_prod`): change a subplace of the nested place (`K2`
  nonempty, `K1` below no owned pointer), as a `tctx_incl`: the outer body is rebodied,
  and the inner one inside the lazy update of the outer contents (`guarded_upd_wand`
  gives the guard needed to open the inner borrow); new `ltype_own_uniq_change_hole_gen`
  (`place.v`: any path, any mask). Below an owned pointer the inner place is under laters
  in the outer node, so a `tctx_incl` (no credits) cannot open it.
- **Not done.**
  - Reborrowing/unblocking a leaf of a nested place below an owned pointer
    (`type_reborrow_place_nested_instr`/`unblock_tctx_place_nested` still need
    `pctx_noderef K1`): it needs the address of the inner referent (a load per pointer, as
    `pctx_expr`) and credits for the laters; unfolding/folding there works.
  - Reborrowing at nesting depth ≥ 2 (a leaf of a place nested inside a nested place): the
    nested context is a pair `(K1, K2)`; deeper paths need a list of contexts with
    `UniqLty` steps between them (`nest_path`/`nest_get`/the double `cpd_acc` generalized to
    a list), and unfolding the root of a nested place (`OfTy (&uniq …)` in `Uniq` mode at
    `K2 = PHole`) needs a reservation extension of every enclosing borrow. The fold
    machinery (closing view shifts) already supports any depth.
  - Shared borrows inside nested places: `type_share_place_instr` would need the same
    double opening as `type_reborrow_place_nested_instr` (and `ShrBlocked` in the inner
    node at `Owned 0`, which is supported by `leaf_owned_s`); not attempted.

Examples (`typing/examples/nested_deep.v`, ~55 s): `get_snd_first`
(`fn<'a,'b>(x: &'a mut (i32, &'b mut (i32, i32))) -> &'a mut i32 { &mut ( *x.1).0 }`: deep
unfold at `PSnd _ PHole`, nested reborrows, `type_resolve_place_instr` with the nested
leaves blocked and `x.0` not; spec `fin(x) = (cur.0, ((fin(r), cur( *x.1).1), fin(x.1)))`)
and `get_inner_mid` (`&mut ( **x).0.1` for `x: &'a mut &'b mut ((i32,i32),i32)`: root nested
unfold, `tctx_unfold_place_nested_prod`, three nested reborrows, drop).

### 6.3 Sums

- **Unit variants of owned places:** `type_sum_unit_oplace_instr` (`pctx_expr K p <-{Σ i} ()`,
  a variant whose type is a subtype of `()`, as `type_sum_unit_instr`): only the tag is
  written, the other cells become the padding (`xsum_phys_pinj_0`).
- **Variants of `&uniq`-rooted places:** `type_sum_assign_place_instr` (payload of size 1,
  any nonempty `K`, the type of the leaf is kept): the borrow is opened for the whole
  instruction, the address is computed twice (`wp_pctx_expr_mask`), the tag and payload
  cells are written with guards obtained from the place's base guard (the cells of the
  leaf may be ghost cells).
- **`&shr` places through sums:** no new rule is needed: `tctx_shr_place` reaches the
  field, the existing `type_case_shr(_inner)` reads the discriminant and gives
  `p +ₗ #1 ◁ &shr{κ} (tyl +!! i)`. A typing derivation for
  `fn get_snd_shr<'a>(r: &'a (i32, Option<i32>)) -> i32 { match r.1 { Some(v) => *v, None => 0 } }`
  goes through, but `type_case_shr`/`type_case_shr_inner` depend on `eq_rect_eq` (through
  `tctx_unwrap_shr_xsum`, which extracts `s = pinj i a` from an observation with
  `proph_obs_sat`), so the example is not included. An axiom-free shared case rule would
  read the tag knowing the (concrete) value of the shared reference, as
  `type_case_oplace` does — not done.
- **Not done: moves and retyping writes through sums.** `pctx_retype` drops the `PSum`
  layer (`pctx_root`); retyping the payload of variant `i` needs the variant list
  `𝔄l` updated at `i` (a `list_set` on syntactic types) with transports of `fin`,
  `!!ₗ` and `psum`/`pinj` along `length (list_set …) = length 𝔄l`, and the type
  `xsum_ty (hlist_set tyl i ty')` at the new index type. Same-type writes, copies and
  borrows through sums are supported (`type_memcpy_oplace_same_instr`,
  `type_memcpy_copy_from_oplace_instr`, the `&uniq` rules).

Examples (`typing/examples/place_sum2.v`, only `functional_extensionality_dep`): `clear`
(`x.0 = None` for a local `(Option<i32>, i32)`) and `set_some_fst`
(`x.0 = Some(v)` for `x: &mut (Option<i32>, i32)`, then resolve).

### 6.6 Boxes two (or more) laters deep

- `type_unfold_oplace_own_instr` (owned places, `Skip`) and `type_unfold_place_own_instr`
  (`&uniq`-rooted places, `Seq Skip Skip`, nonempty simple `K`): unfold an owned pointer
  at any path, also below other owned pointers. The points-to of the pointee is below
  `k` laters (`k = pctx_mode K 1`, resp. `pctx_mode K 0`); it is timeless but
  `▷▷P ⊬ ◇P`, so the laters are stripped with the credits of a program step
  (`k ≤ D`, the root receipt). Below a unique borrow, the body is switched to the new
  node by `cpd_rebody` during the step (the borrow is opened, its lazy contents run with
  a credit, converted, and closed with `guarded_upd_intro`). The other leaf rules already
  work at any depth, so boxes at any depth can now be used.

Examples (`typing/examples/place_deep_box.v`, ~40 s): `deep_read`
(`***b.0` for `b: Box<(Box<Box<i32>>, i32)>`, then drop `b`, freeing the three boxes) and
`deep_get` (`&mut ***x.0` for `x: &'a mut (Box<Box<i32>>, i32)`, then resolve `x`).

### 6.4 Shared mode

- **Resolving/dropping a `&uniq`-rooted place while a leaf is shared-blocked: done**, while
  the shared lifetime is alive (premise `∀ α ∈ lty_shr_lfts lt, lctx_lft_alive E L α` of
  `type_resolve_place_instr`; `lty_uniq_rslv` now accepts `ShrBlocked`, which counts as
  an unblocked leaf in `lty_nunblk`). The value of a shared leaf does not change, so it
  contributes its current value; the prophecy tokens of that value come from its sharing
  predicate (`ty_shr_guard_proph` at `α ⊓ ty_lft ty`, guarded by `α` from `L` and
  `ty_lft ty`), which needs the persistent predicate of the value: `shr_blocked_owned`
  now keeps `ty_gho_pers x d g` (derived when sharing). The case of `ltype_owned_rslv`
  for `ShrBlocked` allocates a fresh variable and resolves it to the current value with
  these guards (`proph_eqz_to_obs_with_guard`), as the unblocked case does with a fresh
  sharing. Owned places already forgot shared leaves when resolving
  (`lty_resolve_just`); freeing them stays forbidden (`lty_freeb`, the memory is lent).
- **Sharing the root of a `&uniq`-rooted place (`K = PHole`): not needed as a new rule.**
  At the root the place is `OfTy ty` in `Uniq` mode, i.e. `p ◁ &uniq{κ} ty`
  (`tctx_place_to_uniq`), and the existing rules apply: reborrow at `κ ⊓ α`
  (`tctx_reborrow_uniq` of `borrow.v`, the original is blocked in the type context and
  unblocked by `type_endlft`) and share the reborrow (`type_share_instr`). A `ShrBlocked`
  root would be interpreted in `Uniq` mode as a blocked borrow (its inheritance giving
  back the `&uniq`), which is what the blocked type-context entry already is. Owned roots
  can already be shared at `K = PHole` (`type_share_oplace_instr` has no nonemptiness
  condition).

Example (`typing/examples/place_shr_resolve.v`): `first_ref`
(`fn<'a>(x: &'a mut (i32, i32)) -> &'a i32 { &x.0 }`: `x` resolved while `x.0` is
shared at `'a ⊓ 'a`; spec `*result = cur(x).0 ∧ fin(x) = cur(x)`).

### 6.5 Products: n-ary products / structs (partial)

- **Owned places: done, through the isomorphism.** `xprod_ty (ty +:: tyl)` is
  `mod_ty to_cons_prodₛ of_cons_prodₛ (prod_ty ty (xprod_ty tyl))`, whose ownership at a
  value `y -:: ys` is the one of the pair at `(y, ys)`. `tctx_unfold_oplace_xprod` /
  `tctx_fold_oplace_xprod` (`place_own.v`) turn a leaf `OfTy (Π! (ty +:: tyl))` into
  `ProdLty (OfTy ty) (OfTy (Π! tyl))` and back; the syntactic type of the hole changes
  (`Π! (𝔅 :: 𝔅l)` vs `𝔅 * Π! 𝔅l`), so the context is retyped (`pctx_retype`,
  `pctx_nosum K`) and the value converted (`of_cons_prodₛ`/`to_cons_prodₛ`). Unfolding
  the tail again gives the fields one by one; all leaf rules then apply.
- **`&uniq`-rooted places: not done.** The same conversion would change the folded type of
  the place (`prod_ty` instead of `xprod_ty`) and the syntactic type of the referent,
  which the lender of the outer borrow fixes (the core of a `Uniq` place is fixed, see
  `cpd_rebody`). A place type for `xprod` is needed: either
  `ConsLty (lt: lty 𝔄) (lts: lty (Π! 𝔄l)) : lty (Π! (𝔄 :: 𝔄l))` with folded type
  `mod_ty to_cons_prodₛ of_cons_prodₛ (prod_ty (lty_fold lt) (lty_fold lts))` (equal to
  `xprod_ty` when `lts` is an `xprod` leaf), a structured refinement for `xprodₛ` in
  `prfn_struct` (a `plist` of refinements, as `psum` for sums; with cases in
  `prfn_wit/den/rsv` and their lemmas), and context steps `PConsHd`/`PConsTl`; or an
  n-ary `XProdLty (hlist lty 𝔄l)`, a nested inductive (all fixpoints and inductions on
  `lty` would need nested recursion). Either way every `ProdLty`/`PFst`/`PSnd` case of
  `lstate.v`, `ltype.v`, `lpath.v` (~50 inductions on contexts) and `place*.v` has to
  be duplicated; this mechanical extension was not attempted. Structs as nested pairs
  (`prod_ty`) are fully supported meanwhile.
- **Elaboration finding.** An instruction applied with `type_seq` must be parenthesized
  in the program exactly as the instruction's expression: with
  `drop_boxes lt p;; delete …;; e` (instead of `(drop_boxes lt p;; delete …);; e`), the
  `eapply` of `type_drop_oplace_instr` tries to unify `drop_boxes lt p ;; delete …` with
  `drop_boxes lt p` by unfolding `delete`, and does not terminate (no error).

Example (`typing/examples/place_struct.v`, ~20 s): `set_mid` (`x.b = 7; x.c` for a local
`struct S { a: i32, b: i32, c: i32 }` as `Π! +[int; int; int]`, unfolded field by
field, then dropped).

## Step 7: performance (branch `proto/perf`)

Scope (user, 2026-10-27): fix the existing slowdowns, no new automation. Times are user CPU
seconds per sentence from `make TIMING=1` (`*.v.timing`), so they do not depend on the
load of the machine; "before" is `prophecy-ra` at `23f1e16`.

### Cause 1: `solve_typing` membership in unreduced lists (cases 1–4)

The slow `Qed`s of `get_mid_shr`, `get_box`, `get_mid`, the liveness proofs with sums and
the dropped `&uniq`-below-`&shr` example have one cause: the `solve_typing` proofs of
`lctx_lft_alive E L α` / `lctx_lft_incl E L α β` with `E = fp_E fp ϝ`. These apply
`lctx_lft_alive_external`, whose premise `ϝ ⊑ₑ α ∈ E` is solved by
`Hint Constructors elem_of_list`. Unifying `elem_of_list_here x ?l : x ∈ x :: ?l` with
`x ∈ fp_E fp ϝ` reduces `fp_E fp ϝ` and instantiates `?l` with a partially reduced tail
(inlined `app`/`fmap` fixpoints applied to `ty_lfts ty`, `ty_E ty`, …). At `Qed`, the
kernel has to convert `fp_E fp ϝ` with `x :: ?l`; it reduces `fp_E` lazily into a
differently shaped term (fixpoints stuck on `ty_lfts` of the types of the signature),
compares the two stuck terms, fails deep inside, unfolds and retries: exponential in the
depth of the types of the signature. Measured on the liveness lemma alone
(`lctx_lft_alive (fp_E (FP ∅ +[ty] oty AtomicClosed) ϝ) [ϝ ⊑ₗ []] α`):

| signature | before | after |
|---|---|---|
| `&uniq{α} (Σ! +[(); int * int])` | ~40 s (not finished in 20 min under load) | 0.005 s |
| `&uniq{α} (own_ptr 1 int * int)` | 30 s | 0.001 s |
| `&shr{α} ((int * int) * int)` | > 10 min | 0.001 s |

The elaborated proof term is tiny; the equation `fp_E … = [ϝ ⊑ₑ α; …]` itself is proved and
checked in no time; and `rewrite /fp_E /=` before `left` (the earlier workaround) still
took 1.2 s, `lazy` before `left` 0.04 s. So the cost is the conversion of two
differently half-reduced lists, and it disappears when one side is in normal form.

**Fix** (`typing/base.v`, commit `3c43dc1`): before the membership search, the spine of a
list that is not syntactically `cons`/`nil` is normalized (`list_spine_norm`: `hnf`,
element by element; tails that do not reduce to `cons`/`nil` are kept as they are), and the
goal is `change`d to the normalized list:
`Hint Extern 0 (@elem_of _ (list _) _ ?x ?l)` and, the same for both sides,
`Hint Extern 0 (?l1 ⊆+ ?l2)` (used by `elctx_sat_submseteq`). The kernel then converts
`fp_E fp ϝ` with a list in normal form, which is linear. The hint fails (and the old
search runs) when the list is already a `cons`/`nil` or does not reduce to one, so it
does not change what `solve_typing` proves, only the shape of the instantiated tails.
The `Alv` workaround in `place_sum.v`, `place_sum2.v`, `place_resolve.v` is no longer
needed (kept; comments updated).

| `Qed` | before | after |
|---|---|---|
| `get_mid_shr` (`place_shr_mid.v`) | 857 s | 3.7 s |
| `get_mid` (`get_first.v`) | 454 s | 12.8 s |
| `get_box` (`place_box.v`) | 209 s | 8.5 s |
| `share_first` (`place_shr.v`) | 47 s | 23 s |
| `set_first` / `get_first` / `set_first_direct` (`get_first.v`) | 24 / 21 / 13 s | 9.0 / 7.3 / 4.3 s |
| the `&uniq`-below-`&shr` read, re-created as `get_uniq_shr` (`place_shr.v`) | did not finish in 25 min | 4.6 s |

The ~30 s of "deref + delete + resolve + return on `&uniq (own_ptr 1 int * int)`" noted
for `get_box` was exactly the 30 s liveness proof above. `get_uniq_shr`
(`fn get_uniq_shr<'a,'b>(r: &'a (Box<i32>, &'b mut i32)) -> i32 { *( *r).1 }`, through
`type_deref_shr_uniq_instr`, which needs `α` alive and `α ⊑ β` from `fp_E`) is now in
`typing/examples/place_shr.v` (commit `c2115b5`); it assumes only
`functional_extensionality_dep`.

### Case 5: `tctx_extract_ctx` with unreduced `pctx_plug K lt` / `tyl +!! i`

Not reproducible at `23f1e16`: without the `simpl`, `solve_typing` on the output context
of `type_sum_assign_oplace_instr` in `drop_local` (`place_resolve.v`) succeeds at once
(the trace shows `tctx_extract_elt_further` twice, `here_exact` for the place element,
which unifies `pctx_plug …` with `ProdLty …` by conversion, and `here_copy` for
`v5 ◁ +[(); int] +!! 1` against `v5 ◁ int`), and the `Qed` time is unchanged (15.8 s).
Synthetic variants (a non-`Copy` payload `+[(); box int] +!! 1`, other orders of the
context, the place element alone) are also immediate. The earlier hang probably had
another cause, e.g. the `type_seq` parenthesization loop found in step 6 ("an
instruction used with `type_seq` must be parenthesized …"). The `simpl` was removed.

### Cause 2: two slow tactic calls in the libraries

Found by the timing of the full build (not in the list above):
- `place.v`, `tctx_unfold_place_own`: `rewrite /ltype_own ltype_own_cp_uniq_plug // …`
  took 82 s, also with explicit arguments for the lemma: a `rewrite` in a proof-mode goal
  rewrites the whole `envs_entails Δ P`, and matching the pattern against the
  `ltype_own_cp …` hypotheses in `Δ` is expensive. `iEval (rewrite …)` (conclusion only):
  0.02 s; the `Qed` is unchanged (1.4 s).
- `uniq_util.v`, `uniq_gbody_ne`/`_proper`/`_loc`: `destruct p; try (f_equiv=>?; f_equiv;
  apply Hofty)` took 26 s and 66 s: in the `PatBlocked` case, `f_equiv=>?` takes about 25 s
  to fail. That case is now handled first (`destruct p; [|…|..]`): ~0 s.
Commit `5fb911e`.

### Remaining slow `Qed`s (after the fixes)

| sentence | time |
|---|---|
| `pcell_example_type` `Qed` (`pcell_example.v`) | 96 s |
| `Print Assumptions pcell_example_type` | 24 s |
| `get_some_first` `Qed` (`place_sum.v`) | 24 s |
| `share_first` `Qed` (`place_shr.v`) | 23 s |
| `box_pair` `Qed` (`place_own.v`) | 19 s |
| `bump` `Qed` (`place_sum.v`) | 19 s |
| `drop_local` `Qed` (`place_resolve.v`) | 16 s |
| `set_snd` `Qed` (`place_own.v`) | 16 s |
| `get_inner_mid` `Qed` (`nested_deep.v`) | 15.5 s |
| `Print Assumptions share_first_type` | 15 s |
| `set_some` `Qed` (`place_sum.v`) | 15 s |
| `type_deref_uniq_uniq_instr` `Qed` (`borrow.v`) | 14 s |

`pcell_example_type` was bisected (rest of the derivation closed by a local axiom, time
of `Qed` of the prefix): the cost is spread over the steps (3–16 s per typing step, e.g.
`type_int_eq` with its `solve_typing` 6.5 s, each `type_endlft` ~15 s), while the
side-condition proofs of these steps, stated alone with the same contexts, take
0.03–0.06 s at `Qed`. So the time goes into the kernel check of the derivation itself
(the rules applied to the long context and the composed predicate transformer), not
into a `solve_typing` proof; the precise conversion was not identified. Note that the type
indices of the contexts contain unreduced appends
(`Zₛ :: [Zₛ; at_clocₛ Zₛ] ++ […]`, from `T2 v h++ T1'` of `type_let` instantiated after
`simpl_subst`), a possible lead. `Print Assumptions` takes 13–25 s in several examples (it
traverses all dependencies); it is kept, as required.

### Full build

Clean `make -j8` of the whole development (8 cores): 1789 s (30 min) before → 859 s (14 min) after,
both on a quiet machine; total CPU time over all sentences 4825 s → 3014 s. Before, the
critical path was `place_shr_mid.v` (~14.5 min for one file) and `get_first.v`
(~8.5 min); after, the slowest file is `pcell_example.v` (~2 min).

## PUniq: nested unique borrows as context steps (branch `proto/puniq`)

Goal (user, 2026-10-28): arbitrarily nested places, all rooted at an owned location; a
`&uniq`-rooted place becomes `own (uniq …)`. This step makes the referent of a nested
unique borrow an ordinary step of a place context, so that the operations on owned places
(`p ◁ₗown{n} …`) work below any number of unique borrows, interleaved with fields, boxes
and sums. The uniq-rooted rules are kept (removal later, once redundant).

### The constructor

`PUniq {𝔅 𝔄'} (κ: lft) (K: pctx 𝔅 𝔄') : pctx 𝔅 (uniq_borₛ 𝔄')`: the hole is in the
referent of a unique borrow at `κ` whose referent has the place type `pctx_plug K _`:

- `pctx_plug (PUniq κ K) lt = UniqLty (pctx_plug K lt) κ`;
- values: `pctx_get (PUniq κ K) x = pctx_get K (uniq_bor_current x)`, `pctx_set` sets the
  current value of the borrow (`uniq_bor_set_current`, moved from `place_nested.v`); the
  location, prophecy id, depths and index of the borrow value are kept;
- `pctx_path (PUniq κ K) q = pctx_path K (false :: q)` (as `UniqLty` in `lty_rfn`, so the
  blocking map is one map for the whole place, as in `place_nested.v`);
- `pctx_rfn (PUniq κ K) x ζm q r = inr (uniq_bor_loc x, pctx_rfn K (uniq_bor_current x) ζm
  (false :: q) r, uniq_bor_ξi x)`, so `lty_rfn_plug` holds for all contexts;
- `pctx_pat (PUniq κ K) p = PatUniq (pctx_pat K p)`, `pctx_size = 1`, `pctx_core`,
  `pctx_nblk`, `pctx_retype`/`pctx_root`/`pctx_reset` pointwise;
- `pctx_off (PUniq κ K) = 0` and `pctx_noderef (PUniq κ K) = False` (as `POwn`: the
  location of the referent comes from the value); `pctx_loc (PUniq κ K) n x _ =
  pctx_loc K n (uniq_bor_current x) (uniq_bor_loc x)` (the referent's location is a `cloc`,
  possibly with ghost cells, unlike the pointee of an owned pointer);
- `pctx_expr (PUniq κ K) e = pctx_expr K (!e)` (one load, as `POwn`);
- `pctx_simple (PUniq κ K) = pctx_simple K`, `pctx_fields (PUniq κ K) = False`.

### Ownership across the step

The ownership of `UniqLty lt κ` in `Owned m` mode is `uniq_node`: the pointer cell, `⧗(2+m)`,
and, under `▷^m`, the inclusion `κ ⊑ ty_lft …`, a guard of the referent's cells, and the
referent in mode `Uniq κ ξi` at some depth `S d' ≤ d` (for a compound referent, `cpd_own`:
a pinned prophetic borrow with its own state ghost variable, reservation and `cpd_tok`; for a
leaf, `uniq_body`). So the ownership of a plugged place does not split as a separating
conjunction across `PUniq` (`ltype_own_plug` cannot hold): reaching the hole means opening
borrows. Hence:

- **Legacy split, restricted.** `ltype_own_plug`, `pctx_loc_guard`, `pctx_loc_empty` keep
  their statements under a type-class premise `PctxNoUniq K` (no `PUniq` step; instances for
  all other constructors and for `pctx_retype`/`pctx_core`), so the existing rules (which
  take it as an instance-implicit argument) and their uses in examples are unchanged. All
  other context lemmas (`lty_rfn_plug`, `pctx_rfn_blk_cons(_below)`, `pctx_get_set`, …) hold
  for every context. `pctx_own (PUniq κ K) := False` and `pctx_mode`/`pctx_depth` get
  values that keep `pctx_mode_add`/`pctx_depth_sub` true; they are only meaningful for
  `PctxNoUniq` contexts.
- **Kind of the hole.** `pctx_kind K k x : bor_kind` (starting from the kind `k` of the root,
  `x` the root value): `Owned (m + #boxes in the last segment)` if the hole is below no
  `PUniq` or below a nonempty segment after the last `PUniq`; `Uniq κ (uniq_bor_ξi y)` if the
  context ends with `PUniq κ PHole` (the hole is the whole referent of the innermost borrow,
  e.g. `**x` for `x: &mut &mut i32`). Inside a borrow the node is in `Owned 0` mode, so the
  number of laters restarts at 0 after each `PUniq`.
- **Access (the generalized split).** `ltype_own_pctx_acc` (new file `typing/pctx_acc.v`), by
  induction on `K`, from `Owned m` at the root: given a timeless token `G` guarding
  `@[pctx_ulft K lt]` (the lifetime of the folded type at the outermost `PUniq`, which
  includes every enclosing borrow lifetime `κ1 … κk` and the lifetimes of the referents) and
  `£(pctx_acc_cost K m)` (one credit per later of each `uniq_node`, plus one per opened
  `cpd_own` body), it opens the enclosing borrows one after the other (`cpd_rebody_ext`
  for compound referents; for each level a fresh half of the token, `frac_split_guard_in_half`),
  runs their lazy contents, and gives
  - the hole, `ltype_own_cp false lt (pctx_kind K (Owned m) x) p r dh gh tid (pctx_loc K n x l)`
    at some depth with `dh + pctx_dlev K ≤ d`, `gh ≤ g`, where `pctx_dlev` counts boxes and
    borrows on the path;
  - the pointer cells of the path (`pctx_ptrs`, the points-to of each `POwn`/`PUniq` cell
    and the guards of the referents' cells), from which `wp_pctx_ptrs` computes the address
    `pctx_expr K e` while the borrows are open;
  - a token `G'` guarding the same lifetime (for the rule's own guarded updates);
  - a closer: for a new hole `lt'` (same folded type and size), pattern `p'` and refinement
    `r'`, given
    * `⌜∀ ζl, prfn_rsv r ζl → prfn_rsv r' (ζl ++ ζl')⌝` (reservation extension),
    * `[∗ list] κ ∈ pctx_ulfts K, pat_ok κ p'` (the new blocked lifetimes are below every
      enclosing borrow lifetime, hence below every enclosing pattern lifetime `κp_i ⊒ κ_i`;
      this is the nested membership condition at all levels),
    * a receipt `⧖(S d' ⊔ g')` for the new root depth (`d' ≥ d`, `d' ≥ dh' + pctx_dlev K`),
    * the pointer cells and `G'` back, and tokens `q:+[ζl']` with a view shift that turns
      them into the new hole (and a frame `R`): the tokens are passed through the closers of
      all enclosing borrows (each extends its reservation by `ζl'`), from the outermost to
      the innermost, and handed to the view shift, which puts them into the loan of the new
      borrow (as in `type_reborrow_place_nested_instr`, for two levels);
    it closes all borrows (each body switched to its new node by `cpd_rebody_ext`; the
    closing view shifts fold back with `ltype_owned_leaf_node`, which handles nested
    `UniqLty` at any depth) and gives back the root at `(d', g')` and `G`.
  Without `PUniq` the access is the old split (no borrow, no credits, no tokens).

### Blocking and reservations through several borrows

A reborrow of a leaf below `k` enclosing borrows `κ1 … κk` (outermost first) of an owned
place, at a fresh lifetime `α`, is at `pctx_blft K α = κ1 ⊓ (… ⊓ (κk ⊓ α))` (syntactic, as
`κ ⊓ α` of the uniq-rooted rules; `= α` below no borrow): `pctx_blft K α ⊑ κi ⊑ κp_i` gives
`pat_ok` at every level, and `[†α] ⊢ [†pctx_blft K α]` without masks. The fresh prophecy
variable `ζ` of the reborrow extends the reservations of all `k` enclosing borrows (their
refinements contain the hole's). Unfolding `OfTy (&uniq{κ'} ty)` into `UniqLty (OfTy ty) κ'`
below `k ≥ 1` borrows extends all `k` reservations by the inner prophecy variable `ξ'`
(the token of `ξ'` is borrowed from the inner body and returned, as in
`type_unfold_place_uniq_deep_instr`). A blocked leaf of an owned place keeps its inheritance
in the place (no reservation at the root); unblocking fires it (after `α` has ended) through
the same access.

### What this subsumes

The nested position `(K1, K2)` of `place_nested.v` is the context `K1 ∘ PUniq κ' K2`; deeper
nestings are further `PUniq` steps, so `nest_get/nest_set/nest_path/nest_loc` are
`pctx_get/pctx_set/pctx_path/pctx_loc` of the composed context and the double `cpd_acc` is the
access lemma at depth 2. A `&uniq`-rooted place `p ◁ₗ{κ} lt` corresponds to the owned place
`own (UniqLty lt κ)` with the context prefix `PUniq κ`; the uniq-rooted rules become
instances of the own-rooted rules once the root conversion (a `&uniq` value stored in an owned
slot, i.e. a local) is used.

### Rules ported (own-rooted, `typing/place_puniq.v`)

Priority order (user): (a) unfold/fold `OfTy (&uniq{κ'} ty)` ↔ `UniqLty (OfTy ty) κ'` at
any position; (b) reborrow of a leaf below `PUniq` and unblock; (c) read/copy and same-type
assignment of a leaf below `PUniq`; (d) resolve/drop of an owned place containing unfolded
`UniqLty`s; (e) shared borrow below `PUniq`. Leaves at a hole of kind `Uniq` (the whole
referent of the innermost borrow) are written through the `&uniq` itself
(`uniq_body_acc`).

### Outcome (branch `proto/puniq`)

Implemented as designed, with these refinements:

- **Legacy split.** `ltype_own_plug`, `pctx_loc_guard`, `pctx_loc_empty` take an
  instance-implicit `PctxNoUniq K`; the existing rules that use them got the binder (added
  mechanically); examples are unchanged (the instance is solved when `K` is given). Proofs
  that `apply` such a rule without giving `K` now pass `K` explicitly (`apply` makes a
  non-dependent instance premise a goal).
- **Access** (`typing/pctx_acc.v`, `pctx_acc`): from `Owned m` at depth `d`, with
  `£(pctx_acc_cred K m d)` (0 below no `PUniq`, `(d+1)(m+d+2)` otherwise: the number of
  laters to strip is not syntactic, it is bounded by the depth, which decreases at each
  level). The result also gives `pctx_in K x` and a guard of the cells of the hole by
  `@[pctx_hlft K b]` (the lifetime of the innermost enclosing borrow), used by writes and by
  the guard of a new borrow. The closer may change the core (the bodies are switched with
  `cpd_rebody_gen`, a variant of `cpd_rebody_ext` choosing the new node when closing).
- **Receipts of owned places** (`lty_nrc`, replaces `lty_nblk` in `oplace_own`): unblocking a
  leaf below `k` borrows has to open them (one batch of credits, from a receipt with the root
  receipt `⧖D`) and to raise the depths of every level above the leaf, while the receipt
  given back by its inheritance is only shifted by the owned pointers after the last borrow.
  So a blocked leaf holds `1 + e` receipts, `e` the number of levels above it outside its
  last segment (`= 0` below no borrow: the old count); a shared-blocked leaf below a borrow
  holds one (credits for opening). Reborrow/share rules take them from their second step.
- **`blocked_uniq`** (never produced before) runs its lazy update with a guard for
  `κ ⊓ ty_lft ty` (settling a restored borrow needs `κ` alive); it is produced by reborrowing
  the whole referent of the innermost borrow (`uniq_body_reborrow`, inheritance settled by
  `uniq_restored_settle'`, credits stored in the inheritance).
- **Resolve.** `lty_rslv` generalizes `lty_resolve` with the blocking map and the path (the
  denotation of a blocked leaf is in the blocking map); `lty_rslv_uniq_blk` pre-resolves a
  nested borrow whose referent has only blocked leaves through its reservation.

Rules (`typing/place_puniq.v`), for an owned place `p ◁ₗown{n} pctx_plug K lt` with any `K`
(`pctx_uend K = None`: hole in `Owned` mode; `= Some κ`: the whole referent of the innermost
borrow, in `Uniq κ` mode):
- (a) `type_change_oplace_instr` (generic, `Seq Skip Skip`, conversion `oplace_conv` at the
  mode of the hole), instances `type_(un)fold_oplace_uniq_instr` (both modes),
  `type_(un)fold_oplace_prod_instr` (both modes), `type_(un)fold_oplace_own_deep_instr`
  (`Owned` mode);
- (b) `type_borrow_oplace_deep_instr` (`Owned` mode) and `type_borrow_oplace_uniq_instr`
  (`Uniq` mode), at `pctx_blft K α`; `unblock_tctx_oplace_deep`, `unblock_tctx_oplace_uniq`;
- (c) `type_write_oplace_deep_instr` (`ReBor;; pctx_expr K p <- pb`, size 1, same type, both
  modes), `type_read_oplace_deep_instr` (`Skip;; !(pctx_expr K p)`, `Copy`, size 1, both
  modes);
- (d) `lty_rslv` with `lty_rslv_of/prod/own/uniq_blk`; `type_resolve_oplace_deep_instr`,
  `resolve_tctx_cons_oplace_deep`, `type_drop_oplace_deep_instr`;
- (e) `type_share_oplace_deep_instr` (`Owned` mode, at `pctx_blft K α`),
  `unblock_tctx_oplace_shr_deep`.

Examples (`typing/examples/place_puniq.v`, only `functional_extensionality_dep`): 
`get_inner_first_own` (`&mut (**x).0` for `x: &'a mut &'b mut (i32,i32)`, the argument slot as
`own (uniq (uniq …))`; `x` dropped while both leaves are blocked), `write_deep`
(`***x = 5` for `&mut &mut &mut i32`, folded back and resolved), `assign_two`
(`(**x).0 = v`), `box_uniq` (`&mut **b` and `**b = 7` for `b: Box<&mut i32>`).

Not done:
- assignment/copy of any size (memcpy) below `PUniq` (only size 1);
- sums below `PUniq` (case analysis, variant assignment);
- resolving a nested borrow whose referent has unblocked leaves (fold it back first, or
  reborrow and resolve the leaves);
- step-free (`tctx_incl`) versions of the conversions below `PUniq`: the access always
  strips the laters of the opened bodies with credits, so every change below a borrow is an
  instruction (the uniq-rooted `tctx_place_change_hole` maps the lazy contents under the
  later instead);
- reading a shared leaf below `PUniq`; unfolding an owned pointer in `Uniq` mode.

### Which uniq-rooted rules are now redundant

None is a formal corollary: a uniq-rooted element `p ◁ₗ{κ} lt` holds a `&uniq` value that is
in no memory slot, while the own-rooted rules need the slot (the place `own (UniqLty lt κ)`
of the local or argument holding the reference). In programs, a `&mut` argument or local is
in a slot, so the own-rooted rules replace the uniq-rooted ones (as the ported examples
show: `get_inner_first_own` vs `get_inner_first` of `nested_uniq.v`). With that reading:
- **Redundant** (own-rooted version at any `K`, any nesting depth, also below boxes):
  `place_nested.v` entirely (nested unfold/fold at the root and below it, nested change of
  the hole, nested reborrow and unblock); in `place.v`: `type_unfold_place_own_instr`,
  `type_reborrow_place(_deref)_instr`, `unblock_tctx_place`, `type_write_place_instr`,
  `type_read_place_instr`, `tctx_drop_place(_cpd)`; in `place_shr.v`:
  `type_share_place_instr`, `unblock_tctx_place_shr`.
- **Redundant up to a program step**: `tctx_place_change_hole(')`,
  `tctx_(un)fold_place_prod/own`, `tctx_(un)fold_uniq_prod` are `tctx_incl`s; the own-rooted
  versions below a borrow are instructions (`Seq Skip Skip`), because the access strips the
  later in front of the contents of each opened body with credits (the uniq-rooted rules map
  the contents under the later). A step-free variant of the access (closing with the
  contents transformed under the later) would remove this difference.
- **Not yet redundant**: `place_memcpy.v` (`type_memcpy_place_instr`,
  `type_memcpy_from_place_instr`: any size; the own-rooted write/copy below `PUniq` are of
  size 1), `place_sum.v` (`type_case_place(_root)`, `tctx_fold_place_sum`,
  `type_sum_assign_place_instr`: no sum rules below `PUniq`), `place_resolve.v`
  (`type_resolve_place_instr`: resolving with unblocked or shared leaves; below `PUniq` only
  nested places with all leaves blocked, otherwise fold back first), `place_shr.v`
  (`type_read_place_shr_instr`: reading a shared leaf), and the conversions
  `tctx_uniq_to_place`/`tctx_place_to_uniq` (no slot).

## PShr: nested shared borrows as context steps (branch `proto/pshr`)

Goal (user, 2026-10-28): as `PUniq`, a context step `PShr κ K` into the referent of a
`&shr{κ}` leaf of an own-rooted place, at any position, interleaved with the other steps
(`own (uniq (shr …))`, `&mut &T`, `Box<&T>`, `&&T`). No interior mutability: below a shared
reference nothing changes, so the places below `PShr` are a read-only *view*.

### The place type and the constructor

- New place type `ShrLty lt κ : lty (at_clocₛ 𝔄)` (an unfolded shared reference whose
  referent has the place type `lt`): `lty_fold = &shr{κ} (lty_fold lt)`, size 1,
  `lty_lfts = κ :: lty_lfts lt`, pattern `PatLeaf`, refinement `inl (PlaceIn x)` (the
  value never changes; no blocking map entry below it), core pointwise.
- Interpretation, in both modes (`Owned m` and `Uniq κ' ξi`): the *leaf* of the folded type,
  `leaf_own c k (&shr{κ} (lty_fold lt)) p r`, together with the pure fact `prfn_vin lt r`:
  the referent value is of the variants of the sums of `lt` (`lty_vin`, through all
  constructors). This is the only information the referent place type carries beyond its
  folded type (the variant of a sum, recorded by a case analysis below `PShr`). There is no
  `Shared` borrow kind: nothing below `PShr` is owned, the sharing predicates are
  persistent and structural (steps 4–5a), so the referent is only ever *viewed* through
  `ty_shr` of the folded type.
- `PShr κ K : pctx 𝔅 (at_clocₛ 𝔄')`, `pctx_plug (PShr κ K) lt = ShrLty (pctx_plug K lt) κ`;
  `pctx_get = pctx_get K x.2`, `pctx_set` pointwise on `x.2` (only for the laws; no rule
  writes below `PShr`); `pctx_path K (false :: q)`; `pctx_size = 1`; `pctx_off = 0`,
  `pctx_noderef = False`, `pctx_fields = False`, `pctx_nouniq = False` (so every legacy rule,
  `PctxNoUniq K`, excludes it); `pctx_loc (PShr κ K) n x _ = pctx_loc K n x.2 x.1`;
  `pctx_expr (PShr κ K) e = pctx_expr K (!e)` (one load); `pctx_in = pctx_in K x.2`;
  `pctx_rfn (PShr κ K) x _ _ _ = inl (PlaceIn x)` (so `lty_rfn_plug` holds for all
  contexts, but `pctx_rfn_set` needs no `PShr` step, `PctxNoShr K`); `pctx_nblk`/`pctx_nrc`
  pass through (and so do `lty_nblk`/`lty_nrc` of `ShrLty`, so that the plug laws hold;
  no blocked leaf is ever created below `PShr`); `pctx_own (PShr κ K) := False` (no split).
- `PctxNoShr K` (type class, as `PctxNoUniq`): the access `pctx_acc` and every rule built on
  it (`place_puniq.v`) get it as an instance-implicit premise: the hole of the access is
  owned (a `bor_kind`), and the referent of a shared reference is not.

### Rules: a context with `PShr` is `K1[ShrLty (K2[lt]) κ]`

A context whose first `PShr` step is `PShr κ K2` is written `K1 ∘ PShr κ K2` with
`PctxNoShr K1`; the rules are stated on `pctx_plug K1 (ShrLty (pctx_plug K2 lt) κ)` (no
composition operator needed; `pctx_expr K2 (!(pctx_expr K1 p))` is the address). `K2` is
arbitrary (fields, sums, `POwn`, `PUniq`, further `PShr`).

- *Phase 1 (owned part):* the access `pctx_acc K1` to the `ShrLty` leaf (in `Owned` or
  `Uniq` mode, opening the enclosing unique borrows with the credits of the step), load the
  `&shr` pointer, and take a copy of its (persistent) ownership predicate; the access is
  closed again with the same leaf. The `&shr` leaf need not be blocked or shared-blocked to
  read through it: its ownership is persistent, so copying it out leaves the place unchanged
  (as `*x: &'b T` is copied out of `x: &'a mut &'b T` in Rust). The lifetimes `K1` needs
  (`pctx_ulft K1`) need only be alive during the instruction.
- *Phase 2 (shared part):* a persistent *shared view* `shr_view κ ty y d g l` = guard of the
  cells at `κ` ∗ `ty_shr κ y d g` ∗ `ty_gho_pers y d g` (the `&shr` ownership predicate
  without its laters) is pushed through `K2` (`shr_pctx_acc`): fields split the guard and the
  structural sharing predicates; a sum at its variant (known from `lty_vin`) gives its
  payload; `POwn` strips the later of `own_ptr`'s sharing predicate; `PUniq κ'` goes to
  `κ ⊓ κ'` (`&uniq`'s sharing predicate); `PShr κ'` opens the default sharing predicate of
  the inner `&shr` (guard with `g+1` laters, opened with a token of the outer lifetime) and
  continues at `κ'` (Rust: `&'a &'b T` gives `&'b T`). The lifetime of the hole is
  `pctx_slft K2 κ`; all lifetimes on the path must be alive for the loads,
  `pctx_salv K2 κ` (their intersection). The laters are paid with credits (bounded by the
  depth: each deref decreases it), the loads of the pointers are guarded by the views
  (`pctx_sguards`, `wp_pctx_sexpr`).
- No closer is needed for phase 2; nothing is blocked, written or unblocked below `PShr`.

Planned rules (`typing/place_pshr.v`), in priority order:
(a) unfold/fold `OfTy (&shr{κ} ty)` ↔ `ShrLty (OfTy ty) κ` at the hole of any `K`
    (`PctxNoShr K`), and changing the referent place type of a `ShrLty` to one with the same
    folded type (pairs, boxes, `&uniq`, inner `&shr` below `PShr`, any depth), instances of
    `type_change_oplace_instr` (`oplace_conv`, both modes);
(b) `type_read_oplace_pshr_instr`: `Skip;; !(pctx_expr K2 (!(pctx_expr K1 p)))` copies a
    `Copy` leaf of size 1 below `PShr` (as `read_shr`, from `copy_shr`);
(c) `type_share_oplace_pshr_instr`: `Skip;; pctx_expr K2 (!(pctx_expr K1 p))` gives
    `&shr{pctx_slft K2 κ} (lty_fold lt)` to the sub-place (place unchanged);
(d) case analysis on a sum below `PShr` (reading the tag through the view), recording the
    variant in the place type (`SumLty tyl i (OfTy (tyl +!! i))` below `ShrLty`);
(e) resolve/drop: `ShrLty` is a leaf of type `&shr …` (resolution trivial, nothing freed
    below it).

### Outcome (branch `proto/pshr`)

Implemented as designed (`typing/ltype.v`, `typing/lpath.v`, `typing/pctx_acc.v`, new
`typing/place_pshr.v`, examples `typing/examples/place_pshr.v`), with these details:

- **Accounting functions.** In `pctx_acc.v` (`pctx_kind`, `pctx_hmode`, `pctx_ne`/`pctx_nmm`,
  `pctx_dlev`, …) a `PShr` step behaves as `POwn` (only meaningful under `PctxNoShr`, but then
  all laws proved by induction for all contexts keep holding); `lty_nrc (ShrLty lt _) e mm =
  lty_nrc lt e (S mm)`. `pctx_nonempty (PShr _ _) = False` (the plugged place is a leaf, so
  `ltype_own_cp_uniq_plug` keeps its statement). `pctx_rfn_set`, `pat_ok_plug_hole`,
  `pctx_acc`, `lty_is_cpd_plug` (`place_nested.v`) take `PctxNoShr`; so do all the rules of
  `place_puniq.v` (instance-implicit; the examples are unchanged). `lty_uniq_rslv (ShrLty) =
  False` (uniq-rooted resolution of an unfolded shared reference: fold it first);
  `lty_freeb`/`lty_omem`/`drop_boxes` treat `ShrLty` as a leaf of size 1.
- **Shared view** (`shr_view`, persistent): the ownership predicate of `&shr{κ} ty` without
  its laters (`shr_bor_gho_view`/`shr_bor_gho_of_view`). Its persistent part is the whole
  ownership predicate of an inner `&shr` (`ty_gho_pers = st_gho` for simple types), so
  stepping through a nested shared reference needs no lifetime token, only `g+1` credits.
  `shr_pctx_view` takes `£(d * (g+3))` for a view at depth `d` (the number of derefs below
  `PShr` is only known from the depths, after the access).
- **Phase 1** (`wp_pshr_addr`): the address of the hole of `K2` below the shared reference at
  the hole of `K1`, from `£(pshr_cred D)` (`5D²+13D+3 ≤ advance_credits D`); the access may be
  closed with another view `lt''` of the referent of the same folded type whose variant
  constraints hold at the (unchanging) referent (used by the case analysis).
- **Lifetimes.** `pctx_slft K2 κ`: `PUniq κ'` gives `κ ⊓ κ'`, `PShr κ'` gives `κ'`;
  `pctx_salv K2 κ` (the intersection of all lifetimes on the path) must be alive, and the
  lifetimes of `K1` (`pctx_ulft K1`) during the instruction only.

Rules (`typing/place_pshr.v`), for `K: pctx (at_clocₛ 𝔅) 𝔄` with `PctxNoShr K`, `K2` any:
- (a) `type_unfold_oplace_shr_instr`/`type_fold_oplace_shr_instr`
  (`K[OfTy (&shr{κ} ty)]` ↔ `K[ShrLty (OfTy ty) κ]`, both modes; `Seq Skip Skip`);
  `type_change_oplace_shr_instr` (`K[ShrLty (K2[lt]) κ]` → `K[ShrLty (K2[lt']) κ]` for
  `lty_fold lt' = lty_fold lt`, `lty_nrc lt' = lty_nrc lt`, `lty_vin lt ⊆ lty_vin lt'`:
  unfolding pairs, boxes, `&uniq`, nested `&shr` below `PShr`, folding back a sum view);
  all instances of `type_change_oplace_instr` (`oplace_conv_shr(_unfold/_fold)`);
- (b) `type_read_oplace_pshr_instr`: `Skip;; !(pctx_expr K2 (!(pctx_expr K p)))` gives
  `v ◁ lty_fold lt` (size 1, `Copy`), value `pctx_get K2 (pctx_get K x).2`;
- (c) `type_share_oplace_pshr_instr`: `Skip;; pctx_expr K2 (!(pctx_expr K p))` gives
  `v ◁ &shr{pctx_slft K2 κ} (lty_fold lt)` (value `(pctx_loc K2 … , pctx_get K2 …)`);
- (d) `type_case_oplace_pshr`: `case: (Skip;; !(pctx_expr K2 (!(pctx_expr K p)))) of el`,
  branch `i` with the view `K2[SumLty tyl i (OfTy (tyl +!! i))]` (no `eq_rect_eq`);
- (e) `lty_rslv_shr` (`lty_resolve_just`): with `type_drop_oplace_deep_instr` and
  `resolve_tctx_cons_oplace_deep`;
- gap of PUniq: `type_read_oplace_shr_deep_instr` (reading the shared-blocked leaf
  `ShrBlocked ty (pctx_blft K α)` produced by `type_share_oplace_deep_instr`, below any
  number of unique borrows, `Owned` mode; the closer needs `pat_ok` of the pattern at every
  enclosing borrow, hence the lifetime of the form `pctx_blft K α`).

Examples (`typing/examples/place_pshr.v`, only `functional_extensionality_dep`; Qed times):
`get_snd` (`( **x).1` for `x: &'a &'b (i32, i32)`, 4.6 s), `first_ref` (`&( **x).0 : &'b i32`
for `x: &'a mut &'b (i32, i32)`, then `x` resolved, `fin(x) = cur(x)`, 10.3 s), `get_boxed`
(`*( **b).1` for `b: Box<&(i32, Box<i32>)>`, 6.4 s), `get_or_zero` (`match **b` for
`b: Box<&Option<i32>>`, 13.2 s). Finding: after the case rule, the first `reflexivity` on the
predicate transformer of a branch needs `simpl` first (the branch index `-!! i`).

Not done: copies of any size below `PShr` (only `!`, size 1); step-free (`tctx_incl`)
versions (every rule is an instruction with a `Skip` for the credits, also for `PctxNoUniq`
contexts); uniq-rooted places containing `ShrLty` (resolution, legacy rules: `PctxNoUniq`
excludes `PShr`); an example for `type_read_oplace_shr_deep_instr`.

### Which rules are now redundant (PShr)

As for PUniq, none is a formal corollary: the `&shr`-specific rules act on a shared reference
*value* in the type context (`p ◁ &shr{κ} ty`, e.g. a `let`-bound reference or the result of a
shared borrow), while the own-rooted rules need it in a slot (`own (shr …)`). With that reading:
- **Redundant** (for references in slots, at any depth, below boxes, unique borrows and further
  shared references): `tctx_shr_place` (`place_shr.v`; fields only, and step-free; the
  own-rooted `type_share_oplace_pshr_instr` is an instruction), its lemma `shr_pctx_split`
  (subsumed by `shr_pctx_view`); `type_deref_shr_own_instr`, `type_deref_shr_uniq_instr`
  (`borrow.v`, derefs below `&shr`) and `read_shr` used for places (a read of `( **x).f` is
  one instruction); `type_case_shr` (`type_sum.v`, case on a shared sum; the own-rooted
  version also avoids `eq_rect_eq`); in `place_shr.v`, `type_read_place_shr_instr` (the
  gap of PUniq, now `type_read_oplace_shr_deep_instr`) and, up to a program step,
  `type_read_oplace_shr_instr` (the deep version with `pctx_blft K α = α` for `PctxNoUniq K`).
- **Not redundant**: the rules on `&shr` values outside slots (`read_shr`, `type_deref_shr_*`,
  `tctx_shr_place`, `type_case_shr` for `let`-bound references); `type_share_instr`
  (`borrow.v`) and the uniq-rooted sharing rules of `place_shr.v` (`type_share_place_instr`,
  `unblock_tctx_place_shr`) are about creating shared borrows, already listed for PUniq.

## Any size and sums below PUniq (branch `proto/size-sums`)

Goal (user, 2026-10-28): the memcpy rules of 6.1 and the sum rules of step 4 for own-rooted
places whose context contains `PUniq` (and `POwn`/`PFst`/`PSnd`/`PSum`) at any depth, in
both modes of the hole (`pctx_kind`), and copies of any size below `PShr`. New file
`typing/place_deep.v`; examples `typing/examples/place_deep.v`, `place_deep_sum.v`.

### Leaf access

All leaf rules go through one lemma, `oplace_leaf_acc` (for `K[OfTy ty]`, `PctxNoShr K`,
`£((d+2)(d+3))`, a token guarding `@[pctx_ulft K (OfTy ty)]`): `pctx_acc`, then, if the hole
is the whole referent of the innermost borrow (`pctx_uend K = Some κ`, `Uniq` mode), the
body of that borrow is opened (`uniq_body_acc`, `uniq_payload_run`); in `Owned` mode the
laters of the hole are stripped. In both modes it gives
- a timeless token `G'` guarding the enclosing lifetime and the cells of the leaf
  (`G' &&{↑NllftG; g+1}&&> lK #↦∗_`, `lK = pctx_loc K …`; the cells may be ghost cells,
  so every write and every retether goes through this guard, as in the uniq-rooted
  memcpy rules);
- the points-to `lK #↦!∗ ty_phys ty y` and the ownership `ty_gho_own ty y dh gh` (no
  later), the pointer cells and their guards (for `wp_pctx_ptrs`);
- a closer `oplace_leaf_closer` for a new value `y'` of the same type, at new depths
  `(dh', gh')` with a receipt `⧖(S dn ⊔ gn)` for the new root depths
  (`dh' + pctx_dlev K ≤ dn`); it gives back the root `K[OfTy ty]` at `pctx_set K x y'`.

The rules apply the step lemma to the instruction itself (`wp_cumulative_time_receipt_linear`
before the first step, so the whole WP is at `⊤ ∖ ↑advN`); the `⧗(S (S M))` receipts pay
two batches of credits (`advance_credits M` each; one batch is not enough for small `M`)
and the `S (pctx_dlev K)` receipts that raise the root depth. So the programs are the
same as for `PctxNoUniq` contexts (`pctx_expr K p <-{n} !pr`, `case: !(pctx_expr K p) of …`,
`pctx_expr K p <-{Σ i} q`, …), without `Skip` prefixes. Only the copy below `PShr` keeps a
`Skip` (`wp_pshr_addr` is stated at mask `⊤`).

### Rules (`typing/place_deep.v`)

For `K` with `PctxNoShr K` and `lctx_lft_alive E L (pctx_ulft K (OfTy ty))` (trivial for
`PctxNoUniq K`: `pctx_ulft = static`):
- `type_memcpy_oplace_deep_instr`: `pctx_expr K p <-{ty_size ty} !pr` with
  `typed_read E L tyr ty tyr' gtr str` and `resolve E L ty Φ`; the leaf keeps its type,
  its value becomes `gtr b`, the old value is resolved.
- `type_memcpy_copy_from_oplace_deep_instr`: `pw <-{ty_size ty} !(pctx_expr K p)` for
  `Copy ty`, with `typed_write` of the destination (old value resolved by `resolve'`);
  the place does not change.
- `type_memcpy_copy_from_oplace_pshr_instr`: `Skip;; pw <-{n} !(pctx_expr K2 (!(pctx_expr K p)))`
  for `K[ShrLty (K2[lt]) κ]`, `Copy (lty_fold lt)` (any size), from the shared view of
  `wp_pshr_addr` (guard of the cells at `pctx_slft K2 κ`, concrete values by `copy_shr`).
- `type_case_oplace_deep` (`typed_body`): `case: !(pctx_expr K p) of el`, branch `i` with
  `K[SumLty tyl i (OfTy (tyl +!! i))]`; in `Uniq` mode the tag is read inside the body of
  the innermost borrow, which is then switched to the node of the sum place
  (`cpd_unfold_uniq`).
- `type_fold_oplace_sum_deep_instr` (`Seq Skip Skip`, instance of `type_change_oplace_instr`
  with `oplace_conv_sum_fold`: `sum_ofty_own_rfn` / `cpd_fold_uniq`).
- `type_sum_assign_oplace_deep_instr` (payload of size 1, `pctx_expr K p <-{Σ i} q`),
  `type_sum_unit_oplace_deep_instr` (`<-{Σ i} ()`), `type_sum_memcpy_oplace_deep_instr`
  (payload of any size copied from a readable path, `<-{n,Σ i} !pr`; the cells after the
  payload become the padding, `xsum_phys_pinj_vec`).
- Reborrow, unblock, read, write and share of payload leaves below `PUniq` need nothing new:
  the `PUniq` rules only require `PctxNoShr K` and `pctx_acc` handles `PSum` steps
  (no `pctx_nosum`/`pctx_simple`/`pctx_noderef` side condition); checked by the example
  `set_some_first` (reborrow and unblock of `p.0` at `PUniq α (PUniq β (PSum _ 1 _ (PFst PHole _)))`).

Not done (and why):
- Moves out of a leaf below `PUniq` and assignments that change the type of a leaf below
  `PUniq`: unsound/impossible as designed (the folded type of each referent is fixed by the
  lender of its borrow; Rust forbids moving out of `&mut`); below no `PUniq` the existing
  `type_memcpy_from_oplace_instr`/`type_memcpy_oplace_instr` (`PctxNoUniq`, `pctx_nosum`) apply.
- Step-free (`tctx_incl`) versions below `PUniq` (as before: the access needs credits).

Examples (only `functional_extensionality_dep`; `Qed` times, `make TIMING=1`):
`swap_snd` (`let c = ( **x).1; ( **x).1 = y` for `x: &mut &mut (i32,(i32,i32))`,
`y: (i32,i32)`; 17.8 s), `get_pair` (`**x` of size 2 for `x: & &(i32,i32)`; 3.3 s)
in `place_deep.v`; `set_some_first` (`if let Some(p) = &mut **x { p.0 = 1 }` for
`x: &mut &mut Option<(i32,i32)>`, with a reborrow of `p.0`; 55.9 s) and `reset`
(`**x = None; **x = Some(y)`, two-cell payload; 20.3 s) in `place_deep_sum.v`.
Slow `Qed` of `set_some_first`: bisected with the rest of a branch closed by a local axiom,
the `Some` branch costs about 44 s of the 60 s of the lemma, spread over its steps
(`type_endlft` with the unblock about 9 s, the five fold/drop steps about 26 s, the reborrow
and write about 9 s), as for `pcell_example_type` (no single slow conversion found).

### Which rules are now redundant

As before, "redundant" reads the uniq-rooted rules as applying to references in slots:
- **Redundant** (same program, `PctxNoUniq K ⊆ PctxNoShr K`, the liveness premise is about
  `static`): `type_memcpy_oplace_same_instr` (by `type_memcpy_oplace_deep_instr`),
  `type_memcpy_copy_from_oplace_instr` (by `type_memcpy_copy_from_oplace_deep_instr`),
  `type_case_oplace` (by `type_case_oplace_deep`), `type_sum_assign_oplace_instr`,
  `type_sum_unit_oplace_instr` (by the deep versions); for references in slots:
  `type_memcpy_place_instr`, `type_memcpy_from_place_instr` (`place_memcpy.v`),
  `type_case_place`, `type_case_place_root`, `type_sum_assign_place_instr` (`place_sum.v`).
- **Redundant up to a program step**: `tctx_fold_oplace_sum`, `tctx_fold_place_sum`
  (`tctx_incl`) by `type_fold_oplace_sum_deep_instr` (`Seq Skip Skip`).
- **Not redundant**: `type_write_oplace_deep_instr`, `type_read_oplace_deep_instr` (size 1
  from/to a value, not a path), `type_read_oplace_pshr_instr` (likewise),
  `type_memcpy_oplace_instr`, `type_memcpy_from_oplace_instr` (retyping/moves, below no
  `PUniq` only).

## Resolve to a readable state (plan approved 2026-10-28)

**Goal.** A fully general resolve rule for own-rooted places that:
- is purely skips (drop is a separate step);
- leaves the place readable but not writable;
- requires no new lifetime and no new borrow. Existing `&uniq`s become shared at their own
  lifetime κ, as in `type_share_instr`.

**Owned part of the place** (from the root, through `POwn`, products and sums): mapping `R`.
- `OfTy ty` ↦ `OfRes ty`. Here we learn `Φ x` from the generic `resolve E L ty Φ` (`type.v`).
- `ProdLty`, `OwnPtrLty`, `SumLty`: structural.
- `UniqLty lt κ` ↦ `ResUniqLty (S_κ lt) κ`. ξ is pre-resolved to the denotation of `S_κ lt`: blocked
  leaves via the reservation, the others by their current values. The referent is then shared at κ.
- `ShrLty`: unchanged.
- Owned `Blocked`/`ShrBlocked`: unchanged, or mapped to `OfRes` when they unblock.

**Referent of a resolved `&uniq{κ}`:** mapping `S_κ`.
- `OfTy` ↦ a shared leaf (`ty_shr κ`).
- `Blocked ty β` ↦ blocked; shared at κ once β ends.
- `ShrBlocked β` ↦ shared at κ.
- `UniqLty lt' κ'` ↦ `S_{κ⊓κ'} lt'`. It is a view only, not resolved: the lender of κ' keeps it.
- Products, boxes, sums: structural.
- `ShrLty`: unchanged.

**Folding.** `ResUniqLty lt κ` with no blocked leaves folds to `ShrLty (OfTy (lty_fold lt)) κ`. This
retypes `&uniq` to `&shr`, which is allowed in the owned part.

**Unfolding `OfRes`:**
- `OfRes (&uniq{κ} ty)` ⇒ `ShrLty (OfTy ty) κ`;
- `OfRes (&shr{κ} ty)` ⇒ `ShrLty (OfTy ty) κ`;
- `OfRes (own_ptr n ty)` ⇒ `OwnPtrLty n (OfRes ty)`;
- products structurally;
- case analysis on sums.

Copy reads and shared reborrows work on `OfRes` leaves; there are no write or move rules.

**The rules.**
- Resolve: `p ◁ₗown{n} lt` ⇒ `p ◁ₗown{n} R(lt)`, as `skipn k`.
- Unblock inside `ResUniqLty`.
- A separate drop.

### Outcome (branch `proto/resolve-readable`)

**Item 1: `ty_gho_res`.** A new field `ty_gho_res : ~~𝔄 → nat → nat → thread_id → iProp Σ` of
`type` (`type.v`), with no laws and not part of the OFE, so it is not ≡-proper. A cheaper
option was to retype resolved leaves to existing "resolved" types with no new field. It is
sound but rejected for two reasons. It cannot resolve inside sums, because the `SumLty`
payload type is fixed. And `resolve_just` cannot be stated generically. `resolve` itself is
unchanged: `resolve_just` would need `gho_res` from `gho_own`, which `&uniq` at a dead κ
cannot give. Instead:
- `resolve_keep E L ty Φ` is `resolve`, but it ends with `⟨π, Φ x π⟩ ∗ G ∗ ty_gho_res x d g tid`.
- `Class ResOwn ty := ty_gho_res ⊣⊢ ty_gho_own`. This is a class, not a `Copy` law, because
  `Copy` is ≡-proper and `gho_res` is not in the OFE.
- `&uniq{κ} ty` has `gho_res := κ ⊑ ty_lft ty ∗` (for the current value `x0`, depths `d' g'`):
  a guarded `↦∗_` at `g+1`, the guarded `↦!∗ phys x0`, `ty_shr κ x0 d' g'`, and
  `ty_gho_pers x0 d' g'`.
- `own_ptr`, products, sums, `mod_ty`, `tracked*`, and `cell_points_to` are structural. All
  other types have `gho_res := gho_own`, with a `ResOwn` instance.
- `resolve_keep` instances: `uniq`, `own`, `prod`, `xsum`, `mod_ty`, `tracked`. There are also
  `resolve_keep_just` (from `ResOwn`) and `resolve_keep_copy` (`Copy`, `ResOwn`, and `resolve`).

**Place types (`ltype.v`).** Two new constructors:
- `OfRes ty` is a resolved leaf: `ty_gho_res` under `▷^…`, next to the cells.
- `ResUniqLty lt κ` is a resolved unique borrow. It holds its cells, `κ ⊑ lfts`, and the view
  `lty_view lt κ …` (the mapping `S_κ`):
  - `OfTy` becomes a shared leaf: guarded cells, `ty_shr`, and `ty_gho_pers`.
  - `Blocked ty β` stays blocked, with the observer and token. It is unblocked to a shared
    leaf.
  - Products, boxes, and sums are structural.
  - `UniqLty lt' κ'` becomes the view of `lt'` at `κ ⊓ κ'`.
  - `ShrLty` is unchanged.

Both constructors are `Owned` only. `lty_simple` is false for both, so `pctx_noshr (PUniq …)`
now also requires `pctx_simple`. As a result, `pctx_acc` closers and
`type_change_oplace_instr` take a `lty_simple lt'` premise.

**Item 2: conversions (`typing/place_res.v`).**
- `tctx_oplace_res_to_ofty`: `OfRes ty ⇒ OfTy ty`, given `ResOwn`.
- `tctx_unfold_oplace_res_prod`: `OfRes (ty1 * ty2) ⇒ ProdLty (OfRes ty1) (OfRes ty2)`.
- `tctx_unfold_oplace_res_own`: `OfRes (own_ptr n ty) ⇒ OwnPtrLty n (OfRes ty)`, at mode 1
  only.
- `tctx_oplace_res_uniq_to_shr`: `OfRes (&uniq{κ} ty) ⇒ ShrLty (OfTy ty) κ`, retyping, with
  `pctx_nosum K`.
- `tctx_unfold_oplace_res_shr`: `OfRes (&shr{κ} ty) ⇒ ShrLty (OfTy ty) κ`.

Leaves converted back to `OfTy`/`ShrLty` are read with the existing rules.

**Items 3 and 4: the resolution judgement (`typing/place_res_rslv.v`).**
`lty_res E L lt lt' k Φ` means that the `Owned m` interpretation of `lt` becomes that of `lt'`
at the same refinement and blocking map. It spends `k` credit batches (`ctask`) and learns
`⟨π, Φ x ζm q π⟩`. The instances are:
- `lty_res_id` (k = 0) and `lty_res_impl`;
- `lty_res_ofty` (from `resolve_keep`, `OfTy ↦ OfRes`, k = 1);
- `lty_res_prod` (`k1 + k2`), `lty_res_own`, and `lty_res_sum`;
- `lty_res_uniq_leaf` (κ alive);
- `lty_res_uniq_cpd` (κ alive, `lty_is_cpd lt`, `lty_vok lt`). Here ξ is resolved to
  `prfn_den (lty_rfn lt cur ζm (false::q))` through the reservation
  (`proph_idx_bor_gen_resolve_share_rsv`). The unblocked leaves are shared at κ
  (`lty_share_view`, `place_res_view.v`), and their tokens are guarded by that sharing.

The rule is:

    type_resolve_oplace_res_instr : lty_res E L lt lt' k Φ →
      typed_instr E L I +[p ◁ₗown{n} lt] (place_resolve.skipn k) (const +[p ◁ₗown{n} lt'])
        (λ post '-[x], λ mask π, Φ x.1.2 x.2 [] π → post -[x] mask π)

**Item 5: operations below `ResUniqLty` (`typing/place_res_ops.v`).** For `K` with
`PctxNoUniq` and `K2` with `PctxNoShr`, the hole is reached through `view_pctx_acc` at
`pctx_slft K2 κ`. The rules are:
- `type_read_oplace_res_instr`: reads a `Copy` leaf of size 1. The place is unchanged.
- `type_share_oplace_res_instr`: gives `&shr{pctx_slft K2 κ} ty` to a leaf.
- `unblock_tctx_oplace_res`: `Blocked ty (pctx_blft (PUniq κ K2) α)` becomes `OfTy ty` in the
  view. The new leaf's value is the final value of the reborrow, as for
  `unblock_tctx_oplace_deep`.
- `tctx_fold_oplace_res_uniq_leaf`: folds `ResUniqLty (OfTy ty) κ` to `ShrLty (OfTy ty) κ`,
  with `pctx_nosum K`.
- `type_drop_oplace_res_instr` (`lty_freeb lt`): `drop_boxes lt p;; delete`. It is a wrapper
  of `type_drop_oplace_deep_instr`.

**Item 6: examples.** All use only `functional_extensionality_dep`.
- `examples/place_res_gen.v` `res_gen`: a generic `T: Copy + ResOwn` of size 1 with
  `∀ E L, resolve E L T ΦT`. It is resolved, read, and dropped. Qed 4.3 s.
- `examples/place_res.v` `res_pair`: `(Box<i32>, &mut (i32,i32))` is resolved (two steps),
  then `*x.0` and `( *x.1).0` are read and the slot is dropped. It learns
  `fin(x.1) = cur(x.1)`. Qed 11.0 s.
- `examples/place_res.v` `res_nested`: `&mut &mut (i32,i32)` with `( **x).0` reborrowed at a
  local lifetime. It is resolved with that leaf blocked, `( **x).1` is read, and the lifetime
  ends, which unblocks the leaf in the view. The leaf is then read and the slot is dropped.
  The spec is `fin(x) = ((3, c.2), fin( *x))`. Qed 27.8 s. The transformers are stated
  without the local lifetime (`lty_res_impl`, `typed_instr_tr_impl`).

**Not done, and why** (as of `proto/resolve-readable`; see "Gaps filled" below for what
was done since).
- Folding a `ResUniqLty` with a compound referent to `ShrLty (OfTy (lty_fold lt)) κ` needs to
  combine the guards of disjoint heap ranges into one guard of their sep. There is no lemma
  "∧ of disjoint ranges ⊢ ∗" for guarded cells (it would follow `and_cloc_combine_fancy` in
  `lang/heap.v`). Only the leaf fold is done. Compound referents stay readable through the
  view.
- Case analysis on `OfRes (Σ tyl)`. Unfolding `OfRes (own_ptr)` below other boxes (mode > 1).
- `ShrBlocked` leaves in a resolved view are excluded by `lty_vok`. `UniqLty` inside the
  referent is allowed only when the referent below it is not blocked.
- Copies of size > 1 below `ResUniqLty`.

**Gaps filled (branch `proto/resolve-gaps`, 2026-10-29).**
1. *Fully generic resolution.* New record law `ty_gho_res_of_own : ty_gho_own ⊢ ty_gho_res`
   (last field of `type`; proved for every type). `&uniq{κ} ty` has
   `gho_res := κ ⊑ lft ∗ ⌜…⌝ ∗ guard ∗ (uniq_body … ∨ shared view)`: the left disjunct is
   the unresolved body (resolving needs κ alive, unknown for an arbitrary value).
   `resolve_keep_just : resolve_keep E L ty (const (const True))` now holds for every type.
   `OfRes (&uniq{κ} ty) ⇒ ShrLty (OfTy ty) κ` became an instruction
   (`type_oplace_res_uniq_to_shr_instr`, `skipn 1`, κ alive; the left disjunct is resolved
   then, by `resolve_uniq_body`). `lty_res_copy`: a `Copy` leaf is resolved from a copy of
   its ownership and stays `OfTy` (readable without `ResOwn`). For an abstract `T`: resolve
   (to `OfRes T`, nothing learnt) and drop are possible; reading `OfRes T` is not (it needs
   `ResOwn T`); a `Copy` `T` is read after `lty_res_copy`.
2. *Sums.* `type_case_oplace_res` (`case: !(pctx_expr K p)` on `OfRes (Σ! tyl)`, branch `i`
   with `SumLty tyl i (OfRes (tyl +!! i))`, `PctxNoUniq K`), `tctx_fold_oplace_res_sum`
   (back), via `sum_res_unfold_own`.
3. *Compound fold.* Heap lemma `and_cells_app_combine_fancy` (`lang/heap.v`: the
   conjunction of the points-to of two consecutive disjoint ranges entails the points-to
   of their union; through `pt_seq_andM_sepM`) and `guard_cells_app_combine_fancy`.
   `lty_view_fold` and `tctx_fold_oplace_res_uniq`: `ResUniqLty lt κ ⇒
   ShrLty (OfTy (lty_fold lt)) κ` for `lty_rfold lt` (leaves, pairs, boxes, `ShrLty` with
   no receipts; not sums: their folded type is `Σ! (hlist_set …)`, and not nested
   `UniqLty`: its view has no guard of the inner prophecy token, which `&uniq`'s sharing
   predicate needs; both done since, see "Open points filled" below).
4. *Shared-blocked leaves in views.* `view_leaf` of `PatShrBlocked α` = the leaf shared at
   `κ ⊓ α` (taken out of `shr_blocked_owned` at resolution, `share_view_shrblk`; the
   inheritance stays in the borrow). `lty_vok` allows them. The prophecy tokens of their
   values are guarded through `ty_shr (κ ⊓ α)`, so `lty_view_guard_proph` is now at
   `κ ⊓ lty_sbl lt` and `lty_res_uniq_cpd` needs `lty_sbl lt` (the intersection of the
   shared-blocking lifetimes) alive; `proph_idx_bor_gen_resolve_share_rsv` takes the extra
   lifetime. Reading: `type_read_oplace_res_leaf_instr` (leaf `OfTy` or `ShrBlocked`,
   `view_rleaf`), instances `type_read_oplace_res_instr`,
   `type_read_oplace_res_shrblk_instr` (`pctx_salv K2 κ ⊓ β` alive). Unblocking after β
   ends: see "Open points filled" below.
5. *Copies of any size.* `type_memcpy_copy_from_oplace_res_instr` (`place_res_copy.v`):
   `Skip;; pw <-{n} !(pctx_expr K2 (!(pctx_expr K p)))` for a `Copy` leaf (`view_rleaf`) of
   any size. Below `OfRes` no new rule: convert first (`tctx_oplace_res_to_ofty` for
   `ResOwn`, `type_oplace_res_uniq_to_shr_instr`) and use `place_deep.v`.

Examples (only `functional_extensionality_dep`; Qed): `res_gen` (arbitrary `T`, resolve +
drop, 1.5 s), `res_gen_copy` (`Copy` `T`, read, 3.7 s), `res_pair` 12.3 s, `res_nested`
28.9 s, `place_res_sum.v` `res_opt` (`Option<(i32,&mut i32)>` resolved as a whole, case,
`p.0` read, 10.2 s), `place_res_fold.v` `res_fold` (`&mut (i32,i32)` resolved, folded to
`&(i32,i32)` and returned, 8.4 s), `place_res_shr.v` `res_shr` (`&mut (i32,i32)` resolved
while `( *x).0` is shared at a local lifetime; both leaves and `*r` read, 28.7 s),
`place_res_copy.v` `res_copy` (pair copied out of a resolved `&mut &mut ((i32,i32),i32)`,
6.2 s).

Newly redundant: `tctx_fold_oplace_res_uniq_leaf` (instance of `tctx_fold_oplace_res_uniq`
with `lt = OfTy ty`). Removed: `tctx_oplace_res_uniq_to_shr` (unsound with the new
`gho_res`; replaced by the instruction). `resolve_keep_copy` is now subsumed for reading by
`lty_res_copy` (kept).

**Open points filled (branch `proto/res-open-points`, 2026-10-29, commit `ea35ca7`).**
1. *Shared-blocked leaves become shared at κ once their lifetime ends.* `view_leaf` of
   `PatShrBlocked α` keeps, besides the sharing at `κ ⊓ α`, a guard
   `@[κ] &&{g+1}&&> l #↦∗_` of the cells and `∃ d' g' ≤ d g, &{κ} ([†α] ={lazyE}=∗
   ofty_owned m ty x d' g' tid l)`: at resolution (`share_view_shrblk`) the borrow of
   `shr_blocked_owned` is split into its persistent part and its inheritance (the depths
   are outside the borrow, so the view stays depth-monotone). The view of a shared-blocked
   leaf is no longer persistent (`view_rleaf_shared`, `view_leaf_shrblk_tguards` frame it
   back). New rule `unblock_tctx_oplace_res_shr` (`place_res_ops.v`, like
   `unblock_tctx_oplace_res`): `ShrBlocked ty (pctx_blft (PUniq κ K2) α)` at the hole of `K2`
   in `pctx_plug K (ResUniqLty (pctx_plug K2 _) κ)` becomes `OfTy ty` when `α` ends, given
   `pctx_salv K2 κ` alive and `pctx_slft K2 κ ⊑ ty_lft ty`; the inheritance is fired
   inside its borrow, which is closed at the restored contents and shared at
   `pctx_slft K2 κ` (`leaf_share_view`), paid by the credits of the leaf's receipt. The
   value is unchanged (`x' = x`).
2. *Sums in the fold.* `lty_rfold` accepts `SumLty tyl i lt` with `lty_rfold lt`; the
   folded type stays `Σ! (hlist_set tyl i (lty_fold lt))` (no change to `lty_fold`). In the
   view the guards of the tag, the payload and the padding are combined
   (`guard_cells_app_combine_fancy` twice, `xsum_phys_pinj`, `xsum_shr_pinj`). The folded
   type is `Σ! tyl` when `lty_fold lt = tyl +!! i` (`lty_fold_sum_eq`; by conversion for a
   concrete `tyl`, as after a case analysis). Chosen over changing `SumLty`'s folded type:
   no change to the place-type definitions, and the equality is a plain rewrite.
3. *Nested `&uniq` in the fold.* `view_uniq` takes a flag `b` (`lty_leafb lt'`: the
   referent is a leaf); when it is set the view also keeps `∃ x0 idx,
   (@[κ ⊓ κ'] &&{g+1}&&> 1:[uniq_prvar x0 ξi]) ∗ uniq_body_pers_component …`, both from
   the sharing of `&uniq{κ'} ty` at κ in `share_view_uniq_leaf`. `view_pctx_acc`'s closer
   takes `lty_leafb lt' = lty_leafb lt`. `lty_rfoldu` (as `lty_rfold`, plus
   `UniqLty (OfTy _) _`) and `lty_view_fold_meta`: the view folds to the shared leaf at a
   value `y` with `lty_meq lt x y` (equal up to the depths and index of the nested
   borrows, which `lty_rfn` forgets; the view supplies them). As the witness is below the
   `▷^m` of `res_node`, the fold is an instruction: `type_fold_oplace_res_uniq_meta_instr`
   (`skipn 1`, transformer `∀ y, lty_meq lt (cur) y → post …`). `lty_view_fold` and
   `tctx_fold_oplace_res_uniq` (no nested borrows, no step) are kept, derived through
   `lty_rfold_meq`.
   *Not done:* a nested `&uniq` whose referent is compound (`UniqLty (ProdLty …) κ'` in a
   resolved referent). Its prophecy variable is reserved (`proph_bor_tok_rsv`: the token
   is in `proph_reserved`), and unreserving it in the borrow would not give back the
   reserved form that the lender's `cpd_own` needs. Fold the inner borrow
   (`type_fold_oplace_uniq_instr`) before resolving instead.

Examples (only `functional_extensionality_dep`; Qed): `place_res_shr_end.v` `res_shr_end`
(`&mut (i32,i32)` resolved while `( *x).0` is shared at a local lifetime; `*r` read; the
lifetime ends, the leaf is unblocked in the view and read with the ordinary rule; dropped;
25.3 s), `place_res_sum_fold.v` `res_opt_fold` (`&mut Option<(i32,i32)>`, case on `*x`,
resolved and folded to `&Option<(i32,i32)>` in both branches, returned; 26.1 s),
`place_res_nested_fold.v` `res_nested_fold` (`&mut &mut (i32,i32)` with `**x` unfolded,
resolved, folded by the instruction to `& &mut (i32,i32)`, returned; 8.9 s).

Newly redundant: none. `tctx_fold_oplace_res_uniq` is not subsumed by the instruction (it
needs no step), and `type_read_oplace_res_shrblk_instr` is still needed while the lifetime
is alive.

**Redundancy.** No rule is formally redundant. `resolve_tctx` and
`type_resolve_oplace_deep_instr` are still needed, because they resolve to nothing, at a
dead κ, and with no `ResOwn`. `lty_simple_true` was removed: it is now false, and the uses
take premises instead.

## Value-rooted places (approved 2026-10-29)

**Element.** `p ◁ₗ lt`, where `lt : lty 𝔄` is the place type of the *value* `p`. It is interpreted
as `∃ D, ⧖D ∗ ⧗(lty_nrc lt …) ∗ node_val lt v`, where `node_val` is the root pointer's node
without its cell. The pointer nodes `own_node`, `uniq_node` and the `ShrLty` node are split into
`cell ∗ node_val`, so that `ltype_own` at a location is unchanged.

**Instances.** The existing notations are kept and become instances:
- `p ◁ₗown{n} lt' := p ◁ₗ OwnPtrLty n lt'`;
- `p ◁ₗ{κ} lt' := p ◁ₗ UniqLty lt' κ`;
- a `&shr` value used as a place is `p ◁ₗ ShrLty (OfTy ty) κ`.

**What stays.** `p ◁ ty` stays as it is, with conversion rules to and from `p ◁ₗ OfTy ty`. The old
core `&shr` rules stay for now: `type_deref_shr_*`, `read_shr`, `type_case_shr`.

**Receipts.** There is one layout: `lty_nrc` plus the receipts stored in nodes (`⧗2` in
`uniq_node`), with existential depths. Converting a bare `&uniq` value, or an old uniq-rooted
place with shared-blocked leaves, into the element is therefore an instruction with one `Skip`.
Reverse conversions, and everything for `OwnPtrLty` roots, are pure inclusions.

**Plan.**
1. Split the nodes into `cell ∗ node_val`.
2. Define `p ◁ₗ lt` and prove the conversions.
3. Make `pctx_acc` root-generic: a context `K` whose first step is `POwn`, `PUniq` or `PShr` is
   the root pointer, whose address is `p` itself (`pctx_vexpr`, no load).
4. Restate the deep rules once over `p ◁ₗ pctx_plug K lt`: `place_deep`, `place_puniq`,
   `place_pshr`, `place_res*`.
5. Delete the parallel place-specific rule sets once they are redundant: `place.v`,
   `place_nested.v`, and the uniq-rooted parts of `place_shr`, `place_sum`, `place_memcpy` and
   `place_resolve`. Port the examples.

### Outcome (branch `proto/value-roots`, merge `0954081`)

Steps 1–5 done; full clean build 20:56 (`make -j8 TIMING=1`), only
`functional_extensionality_dep` in every `Print Assumptions`.

**Step 1 (`ltype.v`).** `own_nval`, `uniq_nval`, `res_nval` (the node without its cell),
`vleaf`/`vres_leaf` (a leaf at a value), lemmas `own_node_nval`, `uniq_node_nval`,
`res_node_nval` (`node (inr …) l ⊣⊢ cell ∗ nval`, by conversion; the node definitions and
`ltype_own` are unchanged). `lty_vown lt r d g tid v`: the interpretation at a value
(`OfTy`, `ShrLty`, `OfRes`: leaves; `OwnPtrLty`, `UniqLty`, `ResUniqLty`: `⌜v = ptr⌝ ∗ nval`
in `Owned 0`; `False` otherwise).

**Step 2 (`vplace.v`).** `p ◁ₗ lt := TCtx_sem _ p (vplace_own lt)`, value `(x, ζm)`:
`vplace_own lt (x, ζm) ⊣⊢ ∃ D, ⧖D ∗ ⧗(lty_vnrc lt) ∗ vroot_own lt (lty_vrfn lt x ζm) D tid v`
(`vplace_own_eq`). `vroot_own`: `∃ d g ≤ D, lty_vown lt …`, except for a root owned
pointer, kept in the old form (pointee at `S d ≤ D`). `vplace_own (OwnPtrLty n lt')` is by
definition `oplace_own n lt'`, so `p ◁ₗown{n} lt'` is literally a notation for
`p ◁ₗ OwnPtrLty n lt'` and all old own-rooted proofs went through unchanged; likewise
`p ◁ₗ{κ} lt'` is now a notation for `p ◁ₗ UniqLty lt' κ`. The refinement `lty_vrfn` starts
the paths below the root pointer (so the blocking maps of `p ◁ₗown{n} lt'` are those of the
old own-rooted element), and `lty_vnrc (OwnPtrLty _ lt') = lty_nrc lt' 0 0` (the root
pointer is not a level). `vplace_own` is `simpl never` (otherwise contexts get unfolded).
Conversions: `tctx_ty_to_vplace`/`tctx_vplace_to_ty` (`p ◁ ty ↔ p ◁ₗ OfTy ty`),
`tctx_vplace_unfold_own`/`fold_own`, `tctx_vplace_unfold_shr`/`fold_shr` (pure);
`type_vplace_unfold_uniq_instr` and `type_uniq_to_vplace_instr` (one `Skip`, for the `⧗2`
of the node), `tctx_vplace_fold_uniq`/`tctx_vplace_to_uniq` (`∀ d g idx`, the depths and
index of the value become those of the node). No separate lemma relates the deleted
`place_uniq_own` to the new element: its rules were ported instead (the new uniq root has
existential depths, `⧗(lty_nrc lt 1 0)` plus the node's `⧗2` instead of `⧗(2·nblk)`).

**Step 3 (`lpath.v`, `pctx_acc.v`).** `PctxVRoot K` (first step `POwn` or `PUniq`),
`pctx_vpath`, `pctx_vrfn` (`lty_vrfn_plug`), `pctx_vnrc/vne/vnmm` (`lty_vnrc_plug`),
`pctx_vexpr` (the first step without a load), `pctx_vrloc`, `pctx_vloc`, `pctx_vptrs`,
`pctx_vpguards`, `wp_pctx_vptrs` (`£(3k·pred dlev)`). `vroot_acc`: for `POwn n K'` it is
`pctx_acc K'` at `Owned 1`; for `PUniq κ K'` it is `pctx_acc_uniq_hole/cpd` without the
cell; credits `pctx_vacc_cred K D = (D+1)²` below a borrow; the closer takes the new root
depth `D'` (`D ≤ D'`, `dh' + dlev K ≤ D'`, `gh' ≤ D'`) and `⧖D'`; guards at `D + 1`.

**Step 4.** Generic rules over `p ◁ₗ pctx_plug K lt` (`PctxNoShr K`, `PctxVRoot K`), the
old own-rooted names kept as corollaries at `K := POwn n K'` (same statements):
- `place_puniq.v`: `vplace_conv`, `type_change_vplace_instr`,
  `type_(un)fold_vplace_{prod,uniq,own_deep}_instr`, `type_borrow_vplace_{deep,uniq}_instr`,
  `unblock_tctx_vplace_{deep,uniq,shr_deep}`, `type_write/read_vplace_deep_instr`,
  `type_share_vplace_deep_instr`; `unblock_tctx_impl`.
- `place_pshr.v`: `wp_vpshr_addr`, `type_(un)fold_vplace_shr_instr`,
  `type_change_vplace_shr_instr`, `type_read/share_vplace_pshr_instr`,
  `type_case_vplace_pshr`, `type_read_vplace_shr_deep_instr`.
- `place_deep.v`: `vplace_leaf_acc`, `type_memcpy_vplace_deep_instr`,
  `type_memcpy_copy_from_vplace_{deep,pshr}_instr`, `type_case_vplace_deep`,
  `type_fold_vplace_sum_deep_instr`, `type_sum_{assign,unit,memcpy}_vplace_deep_instr`.
- `place_resolve.v`: `tctx_drop_vplace_uniq`, `type_resolve_vplace_uniq_instr` (the
  uniq-root resolutions, ported from `place.v`/`place_resolve.v`).
Not generalized: the `PctxNoUniq` rules (`place_own`, `place_sum`, `place_memcpy`,
`place_shr`, `place_resolve`, `place_res*`) stay own-rooted (`PctxNoUniq K` excludes a root
`&uniq`, so for value roots they only have the own-rooted instance); the
resolution-to-a-readable-state rules (`lty_res`, view operations) stay own-rooted (a value
root `ResUniqLty` is not reachable); the pshr rules need `PctxVRoot K1` (a root `&shr` value
uses the core `&shr` rules after `tctx_vplace_fold_shr`).

**Step 5.** Deleted: `place.v` (all of it: `place_uniq_own`, `place_rfn/cur/blk_fin`,
`tctx_uniq_to_place`, `tctx_place_to_uniq`, `tctx_place_change_hole(')`,
`tctx_(un)fold_place_{prod,own}`, `type_unfold_place_own_instr`, `tctx_(un)fold_uniq_prod`,
`type_reborrow_place(_deref)_instr`, `type_write/read_place_instr`, `unblock_tctx_place`,
`tctx_drop_place(_cpd)`, …; `uniq_bor_future_eq`, `place_ghost_rsv_elem`,
`proph_eqz_obs_by_share` moved to `vplace.v`), `place_nested.v` (all of it), in
`place_shr.v` `type_share_place_instr`, `type_read_place_shr_instr`,
`unblock_tctx_place_shr`, in `place_sum.v` `tctx_fold_place_sum`, `type_case_place`,
`type_case_place_root`, `type_sum_assign_place_instr`, in `place_memcpy.v`
`type_memcpy_place_instr`, `type_memcpy_from_place_instr`, in `place_resolve.v`
`type_resolve_place_instr`. Kept: the core `&shr` rules, `tctx_shr_place`.
Ported examples (specs unchanged; programs get a `Skip` for the conversion of the `&uniq`,
`ReBor`s for unfolds/folds below the borrow, and reborrows become `let: "r" := ReBor;; addr`;
Qed): `get_first.v` (10.7, 18.4, 15.6, 6.8 s), `nested_deep.v` (14.6, 21.8),
`nested_uniq.v` (12.6, 20.5), `place_box.v` (12.4), `place_deep_box.v` (8.2),
`place_memcpy.v` (`set_first_pair` 11.2), `place_resolve.v` (`get_last` 15.0),
`place_shr.v` (`share_first` 28.9), `place_shr_resolve.v` (7.1), `place_sum.v`
(`get_some_first` 34.6, `set_some` 13.6), `place_sum2.v` (`set_some_fst` 18.5).
Finding: side conditions with `pctx_ulft` need `simpl` before `solve_typing` (it hangs).
