# Place types in VerusBelt: summary of the plan so far

Status as of 2026-10-26. Branch `place-types` (formerly `prophecy-ra`) of `~/verus-belt`. Nothing has been pushed.
Detailed rearchitecture plan: `design_docs/verus-belt-rearch.md`.

## Goal

Bring RefinedRust-style **place types** (`ltype`s) into VerusBelt. In particular, a mutable
reference should still be usable, and resolvable, while some of its contents are blocked by a
reborrow.

## Background: what RefinedRust does

Sources are in `~/refinedrust-artifact/`; see `pinned_borrows.v` and `ltypes.v`.

- **Pinned borrows** `&pin{κ}[Q] P`. The contents `P` can change any number of times, as long as
  `P ∗ [†κ] ⇒ ▷Q` holds. Each new contents only has to convert back to the fixed lender target `Q`,
  never to the previous contents. This removes the "chaining" problem of `bor_acc_strong`.
- **Place types.**
  - A closed inductive `lty`, with three borrow kinds: `Owned`, `Uniq κ γ` and `Shared κ`.
  - Uniq-mode ownership is `&pin{κ}[core interp](current interp)`.
  - Weak updates under Uniq require the core to stay the same and the new place type to be
    unblockable after `κ`.
- **Value tracking.** A ghost-variable observer/auth pair (`gvar_obs`/`gvar_auth`) does this. It is
  the non-prophetic analogue of VerusBelt's VO/PC.
- **Why unfolding behind `&mut` works there.** Every borrow's contents carry a lazy inner
  `|={lftE}=>`. Blocked parts can therefore be converted back inside that update rather than inside
  the lifetime logic's closing view shift.

## Decisions taken

1. **`proph_bor` alone does not replace pinned borrows.**
   - VO/PC only pins the *value*; it does not pin the lender's target.
   - Instead, pin the shape with a state-indexed body: a Leibniz ghost variable holds the current
     state.
   - Each state persistently carries a proof that it can be unblocked back to the fixed core.
   - The prophecy value cannot hold the state, so the state needs its own ghost variable.
2. **Blocked lifetimes are syntactic intersections `κ ⊓ α`.** Then `[†κ]` gives `[†α]` with no
   mask requirement. (`llftl_incl_dead_implies_dead` needs `↑NllftG`, which closing view shifts do
   not have.)
3. **Resolving a `&mut` whose contents are blocked uses resolution reservations, not pre-resolution
   at borrow time.**
   - `1:[ξ]` together with tokens for `ζl` is exchanged for `proph_reserved ξ ζl`.
   - Later, ξ can be resolved to a value that depends on `ζl` without holding their tokens. Tokens
     are only needed for the extra dependencies `ηl`.
   - A reservation can be released (unreserved) at any time.
   - It is sound because the reservation sits in the prophecy log at the moment it was made, and no
     token for ξ exists afterwards.
4. **Closed syntax for place types**, with a ghost-state pattern. The ghost variable cannot hold an
   `lty` itself: `lty` contains `type`s, which contain `iProp Σ`, so Σ would depend on itself.
5. **Rearchitect sharing before making `&uniq` lazy.** With a lazy body `&{κ}(|={…}=> P)`, a guard
   can only reach `|={…}=> P`, which breaks guard-based sharing. So:
   - split `ty_gho` into `ty_gho_own` (ownership, may be lazy) and a persistent `ty_shr κ`, plus a
     law `ty_share`;
   - `ty_shr` must be **indexed by κ**, because sharing `&uniq{κ'}` at κ only gives `κ ⊓ κ'`;
   - the lazy update must be a **fancy** update with mask `↑Nllft ∪ ↑prophN ∪ ↑uniqN`, so that
     inheritances can be fired, which means `ty_share` takes a guard for κ;
   - by default, `ty_shr κ := @[κ] &&> ty_gho_own`.

## Done (commits on `place-types` (formerly `prophecy-ra`))

| Commit | Content |
|---|---|
| `115a618` | `prophecy.v`: resolution reservations (`proph_reserve`/`unreserve`/`reserve_extend`/`resolve_reserved(_gen)`). The model is a reserved log entry that is resolved in place. Existing statements are unchanged. |
| `4dc97fb` | `uniq_cmra.v`: reserved observer `.VOR[ξ;ζl]` with reserve/unreserve/extend/resolve/preresolve lemmas. `proph_bor.v`: reserved prophetic borrows `&iproph_rsv`, plus a generalized body `proph_idx_bor_gen` whose controller prophecy is independent of the value. `ltype.v` (new): the place-type model, described below. |
| `db4cb0a` | `lifetime_full.v`: `llftl_bor_guard` (`&{κ}P ⇒ @[κ] &&{;1}&&> P`) and `llftl_bor_fupd_guarded` (run a fancy update inside a borrow, given a κ guard and `£1`). |
| `122e629` | `type.v`: `ty_gho` renamed to `ty_gho_own`. New fields `ty_shr`, `ty_shr_persistent`, `ty_shr_lft_mono`, `ty_shr_depth_mono`, `ty_share`. Every type uses `default_shr` (a guard of `gho_own` with one later, closed downward in depth). Behaviour is unchanged. |

### The `ltype.v` model (Phase 2)

- **Constructors and borrow kinds.**
  - `lty` has `OfTy`, `Blocked`, `UniqLty`, `OwnPtrLty` and `ProdLty`.
  - Place refinements are `PlaceIn x | PlaceGhost x₀ ζi`; a ghost refinement denotes the
    reborrow's prophecy.
  - Borrow kinds are `Owned m | Uniq κ ξi γ`.
- **Uniq mode.** A compound place is a generalized prophetic borrow pinned to a fixed core, with the
  pattern and refinement held in a ghost variable.
- **Proved laws.**
  - unblockability, `unblock_blocked`, and core idempotence;
  - unfolding equivalences at Owned for `prod_ty`, `own_ptr` and `&uniq`;
  - folding at Uniq, as an update under a guard;
  - switching shapes (`cpd_acc`);
  - shifting back to the core on the lender side (`cpd_create`, `cpd_lender_unblock`).
- **Known gap.** You cannot unfold behind an *existing* `&uniq`, because its lender expects the
  non-lazy `uniq_payload`. This is what motivates the rearchitecture.

### Step 3: consumers use `ty_shr` (commit `2332892`)

- **`default_shr` now has `g+1` laters**, to match `&shr`.
- **`ty_shr` is in the OFE.** `TypeNonExpansive`/`TypeContractive` follow RustBelt's step-index
  convention: the shr clause is compared one step later than the own/pers clauses.
- **`fixpoint.v`** builds a chain of (own, pers, shr) triples.
- **`type_incl`** has a new shr clause.
- **`Copy` gains `copy_shr`; `Sync` gains tid-independence of shr.**
- **`ty_shr_guard_proph`** is a lemma; the underlying field `ty_shr_guard_proph'` has TEMPORARY
  hypotheses.
- **`&shr`'s `st_gho`** is now
  `(@[κ] &&{;g+1}&&> pointsto) ∗ ty.shr κ x d' g ∗ ▷^(g+1) pers`.

**TEMPORARY laws.** Both hold only while every type uses the default shr, and step 5 must remove
them. Each use is commented in the code.

- `ty_shr_from_guard` (guard of `gho_own` ⇒ shr), used by:
  - `borrow.v`: `type_share_instr`, `type_deref_shr_own_instr`, `type_deref_shr_uniq_instr`
  - `product_split.v`: `tctx_split_shr_prod`
  - `type_sum.v`: `tctx_unwrap_shr_xsum`
  - `pcell.v`: `typed_pcell_borrow`
  - `pptr.v`: `typed_pptr_borrow`
  - `protocol.v`: `storable_borrow`, `typed_sp_guard`
- `ty_shr_to_default` (shr ⇒ default shr), used by:
  - `mod_ty.v`: `mod_ty_in`/`out`/`id`
  - `product.v`: `prod_ty_left_id`/`right_id`

**Constraint for step 4.** To stay contractive, a type's structural `ty_shr` must put the inner
`ty_shr` under `▷`. This applies to box, `&uniq` and `&shr`.

### Step 4: structural `ty_shr` (commit `6ec2d46`)

**`ty_share` no longer takes credits.** A credit cost that depends only on `(d, g)` cannot pay
for products, because the cost grows with the width of the type. The new statement is

    k + d ≤ g → … &{κ}(▷^k ty_gho_own x d g tid) ={E}=∗ G ∗ ▷^k ty_shr κ x d g tid

`ty_share0` is the case `k = 0`. `own_ptr` recurses at `k+1`.

**Which types are structural:**
- structural: `prod`, `unit0` (`True`), `xsum`, `mod_ty`, `tracked`, `tracked_ty_with_prop`,
  `fix_ty` (the limit of the chain);
- `own_ptr` and `cell_points_to` are `▷[S d'] (guard pointsto ∗ ty.shr) ∨ default_shr`, where the
  `∨ default_shr` part is TEMPORARY and goes away together with `ty_shr_from_guard`;
- `&shr` deliberately keeps `default_shr`. It is contractive that way, and a structural version
  would mean rebuilding it without `ty_of_st` for no gain.

**Consumers and temporary laws:**
- `ty_shr_to_default` is deleted.
- `ty_shr_from_guard` is still used in four places:
  - `borrow.v`: `type_share_instr` and `type_deref_shr_uniq_instr`, both on `&uniq` payloads;
  - `protocol.v`: `storable_borrow` and `typed_sp_guard`;
  - the alternative branch of `own_shr_unfold` (`own.v`);
  - the alternative branch of `cell_points_to_shr_unfold'` (`pcell.v`).

**Notes for step 5:**
- `ty_share0` needs `d ≤ g`, so `&uniq` must maintain `d' ≤ g'` for its payload.
- Running the lazy update costs credits per `&uniq` node, plus laters under `own_ptr`. These
  credits have the same width problem, so `ty_share` probably needs a step-update form (as in
  RustBelt, `|={E}▷=>^n`) rather than credits.

### Step 5a: step-update `ty_share`, structural `&uniq` shr (commit `dc4e42c`)

- **`ty_share` is now a step-update:**
  `… ty_gho_pers x d g tid -∗ (G guards @[κ]) -∗ G -∗ &{κ}(ty_gho_own …) ={E}=∗ |={E}▷=>^d |={E}=> G ∗ ty_shr κ …`.
  - `own_ptr`, `cell_points_to` and `&uniq` each take one step.
  - Products share their components in parallel, each with half of `G` (`share_par`), so the step
    count is `d` and does not grow with width.
  - The `▷^k` parameter is gone.
- **`&uniq`'s `ty_shr` at κ0:**
  `(@[κ0⊓κ] guards the full points-to) ∗ (@[κ0⊓κ] &&{;1}&&> 1:[ξ]) ∗ ▷ ty.shr (κ0⊓κ) x0 d' g'`.
  It is produced by `proph_bor_tok_share`, which unnests, pins the value by VO agreement, and also
  yields the token guard.
- **Resolution** goes freeze → share → `ty_shr_guard_proph`, through the new
  `proph_ibor_resolve_share`. `resolve_uniq_body` now returns `ty_shr`.
- **Temporary items removed:** `ty_shr_from_guard`, the `∨ default_shr` disjuncts, the temporary
  hypotheses on `ty_shr_guard_proph`, and the old `ty_guard_proph`. One TEMPORARY item remains:
  `storable_borrow` in `protocol.v`, which assumes `ty_shr_is_default ty` and has no users. It is
  deferred to step 6.

### Step 5b: lazy `&uniq` payload (commit `3dad48f`)

- **The payload is now partly lazy.** With `lazyE := ↑Nllft ∪ ↑prophN ∪ ↑uniqN`:
  `uniq_payload := ⧖ ∗ ty_gho_pers x0 ∗ |={lazyE}=> (ty_gho_own x0 ∗ l #↦!∗ phys)`.
  `⧖` and `pers` stay outside the update, because the summaries in `proph_ibor_reborrow` and
  `proph_ibor_unnest` need them at a mask where the update cannot run.
- **Read paths now open the borrow, run the update, and close.** This covers `read_uniq`, the
  `&uniq` deref rules and `type_case_uniq_outer`. `uniq_tok_guard_payload` is deleted.
- **Changes to interfaces:**
  - `typed_write` hands out the old contents lazily.
  - `tctx_unwrap_uniq_xsum` became `typed_body_unwrap_uniq_xsum`, which needs a credit.
  - The mask of `Send` gains `↑prophN`.
  - `type_uniqbor_instr` stores a `£1` in the blocked entry.
- **`ltype.v`:** `cpd_body`'s node became lazy so that `cpd_fold` stays provable. `cpd_fold`
  now needs `£1`.

### Step 7 prerequisites (design: `design_docs/verus-belt-step7-design.md`)

**Step 7.1** (commits `36b5142`, `c03e344` on `place-types` (formerly `prophecy-ra`)):
- `&uniq`'s own and pers no longer contain the referent's pers.
- `&uniq`'s shr carries it under `▷▷`.
- The budget of `ty_shr_guard_proph` grew from `d*(g+1)` to `d*(g+2)`.
- `uniq_payload = ⧖ ∗ |={lazyE}=> (own ∗ pt)`.
- The summaries now contain only `⧖`.

**Step 7.2 prototype** (branch `proto/settle-at-unblock`, commit `ca9024e`, not merged):
- The receipt moved inside the lazy update.
- Blocked type-context entries hand out `tctx_pending_own`: settle given a guard for `ty_lft ty`.
- Reborrow, UniqBor, share and unblock all go through. No dead-κ disjunct is needed: unblocking
  already requires `ty_lft ty` alive, which guards κ.
- **Fails:** the `&uniq &uniq` deref (`proph_ibor_unnest`). Rebuilding the outer payload needs the
  inner final value's receipt, which is behind the inner borrow at κ', and there is no guard for
  κ' there. The deref rule is commented out on the prototype branch.

**Step 7.3: guarded lazy payload** (commit `dc1448d`, merged into `place-types` (formerly `prophecy-ra`) as `1ef9328`):
- New combinator in `type.v`: `guarded_upd E P Q := ∀ G, ⌜Timeless G⌝ -∗ (G guards P) -∗ G ={E}=∗ G ∗ Q`.
- `uniq_payload := guarded_upd lazyE @[ty_lft ty] (⧖ ∗ own ∗ pt)`.
- Openers split their guard: one half opens the borrow, the other runs the payload, via
  `κ ⊑ ty_lft ty`.
- The summaries `R`/`S` are removed from `proph_ibor_reborrow` and `proph_ibor_unnest`. Their
  transformation wands now receive their own guard.
- The `&uniq &uniq` deref is restored: inside the guarded update, κ' opens and settles the inner
  borrow.
- `typed_write` hands out the old contents as `guarded_upd … (llctx_interp L) …`.
- `tctx_pending_own` is now simply a guarded update.
- No per-type `ty_settle` law was needed.
- `ltype.v`: `cpd_body` and `cpd_own` are guarded by `α = lft_intersect_list (lty_lfts lt)`.
  `Blocked`'s `blocked_own` (Owned mode) has not been converted to the pending form yet; it will
  need it once typing rules block places through `&uniq`.

**Step 7.4: `&uniq` on the pinned, state-indexed body.** Commits `95d2f7b`, `9cbaafd`,
`e02ed72`, merged into `place-types` (formerly `prophecy-ra`) as `3866d11`.

- **Where γ lives.** The state ghost name γ is part of the uniq cell value:
  `uniq_cell x d g γ := (x, (enc d, (enc g, γ)))`.
- **The new body.**
  - `uniq_body := ∃ κp γ, uniq_pat_lft κ κp ∗ ghost_var γ ½ (lstate_triv x) ∗ proph_bor_tok … ∗ ⧗1 ∗ proph_idx_bor_gen κ … (uniq_gbody κp ty)`.
  - `uniq_gbody = cpd_body κp (ty_lft ty) (leaf_node κp ty)`.
  - At the trivial state this is exactly the old guarded payload.
  - The lender settles with `uniq_lender_settle`.
- **Unfolding behind an existing `&uniq`.** `prod_ofty_unfold_uniq` and `prod_ofty_fold_uniq`
  switch the shape of the same borrow, keeping the prophecy variable, value and depths. They rely
  on `proph_idx_bor_gen_acc_rebody_guarded` and on the exclusive token `cpd_tok`.
- **`blocked_owned` is now in pending form:**
  `[†α] ={lazyE}=∗ guarded_upd lazyE @[ty_lft ty] (…)`. `imp_unblockable` takes a guard.
- **Other changes.**
  - `prophecy.v` and `syn_type.v`: the cell type gains γ.
  - `uniq_cmra.v`: a resolved controller now records an observation, not just an equaliser
    (`proph_ctrl_eqz_compose`).
  - `bor_kind Uniq` no longer carries a ghost name.
- **Dropped or still to do:**
  - own_ptr and `&uniq` unfolding under Uniq;
  - `cpd_create`/`cpd_lender_unblock`;
  - **the reserved observer `uniq_obs` (tok ∨ rsv) in compound places**, which Phase 3 needs again;
  - Uniq-mode `blocked_uniq` in pending form.

### Phase 3: typing rules (commit `2d5cb27`, merge `1f10631`; design in `design_docs/verus-belt-phase3-design.md`)

- **3a (prerequisites).**
  - Compound Uniq places hold `.VOR` for some ζl. Unfolding reserves for `[]`; `cpd_acc` can
    extend the reservation.
  - `blocked_uniq` is in pending form.
- **Integration.**
  - A new semantic element `TCtx_sem` in `type_context.v`.
  - In the new file `place.v`: `p ◁ₗ{κ} lt`. Its value is the `&uniq` value plus `ζis`, the
    prophecy ids of the blocked leaves.
- **Rules.**
  - `tctx_uniq_to_place` / `tctx_place_to_uniq`.
  - `tctx_unfold_uniq_prod` / `tctx_fold_uniq_prod`.
  - `type_reborrow_field0_instr`: blocks field 0 at `κ ⊓ α`, and extends the outer reservation by
    `[ζ]`.
  - `type_drop_blocked_field0_instr`: drops the outer while field 0 is blocked. It pre-resolves
    ξ to `(fin ζ, fin η)` using the reservation, so only η's token is needed.
  - `unblock_tctx_place_field0`.
- **Examples** (`typing/examples/get_first.v`). Only `functional_extensionality_dep` is assumed.
  - `get_first`: `fn<α>(&uniq{α}(int*int)) → &uniq{α} int`, with the spec
    `fin(x) = (fin(ret), cur(x).1)`. The outer borrow is dropped while field 0 is still blocked.
  - `set_first`: reborrow, write 5, end the lifetime, unblock, fold back. The spec is
    `fin(x) = (5, cur(x).1)`.
- **Not covered yet.**
  - Only field 0 of pairs of `OfTy` leaves: no field 1, no nested places.
  - No unfolding under Uniq for `&uniq` or `own_ptr`.
  - Drop-while-blocked only in its pair-specific form.
  - No automation; the examples apply rules by hand.

### Phase 3, general rules (merges `8b9edfc`, `ee311b8`)

- **Place contexts** (`lpath.v`).
  - `pctx 𝔅 𝔄 ::= PHole | PFst K lt2 | PSnd lt1 K | POwn n K`, with operations for plugging,
    get/set, path, offset, location, mode/depth, and the address expression.
  - The blocked leaves are now a map from paths to ζ.
- **Rules parametric in the path** (`place.v`):
  - `tctx_place_change_hole`, the generic one, with unfold/fold for prod and `own_ptr`;
  - `type_reborrow_place(_deref)_instr`;
  - `unblock_tctx_place`;
  - `type_read/write_place_instr`;
  - `tctx_drop_place`, which drops while all leaves are blocked via the reservation. Other
    patterns first reborrow and resolve their unblocked leaves.
- **`own_ptr` under `&uniq` works.** Receipts are shifted by the number of pointers above, so
  folding back needs no program step.
- **Nested `&uniq`** (branch `proto/nested-uniq`, design in `design_docs/verus-belt-phase3-design.md`,
  section "Nested &uniq"): `x: &uniq{κ} &uniq{κ'} T` is unfolded (at the root) into
  `UniqLty lt κ'`; leaves of the nested place are reborrowed at `κ ⊓ α`, unblocked, and the
  outer borrow can be dropped while they are blocked. Nested membership condition
  (`pat_blk_lfts` looks through `PatUniq`), outer reservation includes the inner prophecy,
  lazy nested fold paid by `⧗2` in the `UniqLty` node. Examples in
  `typing/examples/nested_uniq.v`.
- **Examples:** `get_first`, `set_first`, `get_mid` (`.0.1`), `set_first_direct`, and `get_box` in
  `place_box.v`. They assume only `functional_extensionality_dep`. `get_box`'s `Qed` takes about
  3.5 minutes.

## Open design questions (next)

- **Step 6, storage protocols: done** (design in `design_docs/verus-belt-step6-design.md`).
  - Commit `e6822bd`: `ty_shr_lft_mono` now accepts inclusions with laters, absorbed into `g`:
    `(@[κ'] &&{n}&&> @[κ]) -∗ ty_shr κ x d g -∗ ty_shr κ' x d (g+n)`. The old statement is the
    lemma `ty_shr_lft_mono0`. Only `&uniq` needed re-indexing: its token guard now has `g+1`
    laters, and its inner shr sits at the outer `g`.
  - Commit `2bdc9e1`: storable values share up front.
    - The storable value is `~~𝔄 * (nat*nat) * lft`.
    - `gt_gho := ⌜α≠∅⌝ ∗ @[α] ∗ ty.shr (α⊓ty_lft) ∗ ([†α] ⇒ ▷ gho_own) ∗ ⧖ ∗ pers`.
    - New premises: `storable_new` needs `ty_lft` alive; `storable_borrow` needs `κ ⊑ ty_lft`.
    - The `Copy` instance is gone.
    - New `typed_instr_of_skip_linear` in `programs_util.v`, for summing time receipts.
  - No TEMPORARY items remain.
- **Step 7, rebasing `&uniq` onto the pinned body: unblocked.** Step 7.1 removed the non-lazy
  `pers`, and step 7.3 removed the non-lazy `⧖`. What remains is the rebase itself (plan step 4),
  plus giving `Blocked`'s `blocked_own` the pending form.

## Remaining plan

4. **Structural `ty_shr` with recursive `ty_share`** for `own_ptr`/`box`, `prod`/`xprod`, `sum`,
   `tracked`, `mod_ty`, `fixpoint`, the typed `pcell`/`pptr`, and `shr_bor`.
5. **`&uniq`.**
   - `shr κ := (@[κ⊓κ'] &&> pointsto) ∗ ty.shr (κ⊓κ') ∗ (guard for ξ's token)`.
   - Prove `ty_share` by unnesting, opening at `κ⊓κ'`, running the lazy update, closing non-lazily,
     and recursing.
   - Make `uniq_payload` lazy (`|={Mlazy}=> …`).
   - Restructure `resolve_uniq_body`/`proph_ibor_resolve` as: freeze, then share, then guard the
     prophecy tokens.
   - Fix `borrow.v`, `product_split.v`, `type_sum.v`, `pptr.v`, `pcell.v`.
   - Retire `ty_shr_from_guard` and the old `ty_guard_proph`.
6. **Storage protocols.**
   - deposit: create `&{κs}(gho_own)` and store it together with `@[κs]`;
   - shared access: `ty_share` on the stored borrow;
   - withdraw: end `κs` and use the inheritance.

   Needs a design pass first.
7. **`ltype.v`.**
   - Rebase `&uniq`'s body on the pinned, state-indexed body, with `OfTy` as the trivial pattern.
   - Support unfolding under Uniq.
   - Then Phase 3: typing rules for place access, field reborrow below `&uniq`, writes,
     unblocking, and dropping or resolving a `&uniq` while blocked using `.VOR` reservations. Add
     an end-to-end example.

Out of scope so far: `Shared` mode for place types, `Opened`/`Coreable`/`Shadowed` place types,
arrays and enums.

## Working conventions

- Commit locally after each major change once the full build is clean (`make -j8` with the opam
  switch `verusbelt`). Don't push without asking.
- No `Admitted` and no new axioms.
- Use sub-agents for the large implementation steps.

## Roadmap to full place support (agreed 2026-10-27, executed in order)

**Goal.** Places of all kinds, arbitrarily nested: box, `&shr`, `&uniq`, products and sums.
General rules for mutable borrow, shared borrow, assign, copy, move, resolve and drop of a place.

1. Owned roots: places rooted at a local or `own_ptr`.
2. Moves: a moved-out (`uninit`) place type, move from a place, re-assign.
3. Shared mode: a `Shared` borrow kind, a shared-blocked place type, shared borrow of a place,
   and `&shr` places.
4. Sums: an enum/sum place type with a fixed variant, and case analysis on places.
5. General resolve and drop, for arbitrary patterns and for owned places.
6. Generalizations:
   - nested `&uniq` at any depth and below `Box`;
   - assign and copy for any size, and below `Box`;
   - n-ary products.
7. Automation, and reducing the cost of kernel checking.

**Progress.**
- Steps 1–2 are done (merge `7ac1530`; `typing/place_own.v`, examples in
  `typing/examples/place_own.v`).
  - Owned roots: `p ◁ₗown{n} lt`, whose root is in `Owned 1` mode.
  - Moved-out leaves are `OfTy (↯ 1)`.
  - Rules: conversions, unfold/fold, `type_borrow_oplace_instr`, `unblock_tctx_oplace`, and
    read/move/write for size 1.
  - Limits: no unfolding of a box two laters deep; assignment of any size to `&uniq` leaves is
    deferred to step 6.

- Step 3 is done (merge `256cd59`; `typing/place_shr.v`, examples in
  `typing/examples/place_shr.v`, `place_shr_mid.v`; design in
  `design_docs/verus-belt-phase3-design.md`, section "Shared mode").
  - Shared-blocked leaves `ShrBlocked ty α` (value unchanged, persistent sharing info,
    inheritance of the contents); shared borrow of a leaf of `&uniq`-rooted (at `κ ⊓ α`)
    and owned places, reads while shared, unblocking.
  - Places below `&shr`: no `Shared` borrow kind (the referent never changes);
    `tctx_shr_place` (nested fields, parametric in `pctx`) plus the existing deref rules.

Agents follow `~/verus-belt-tools/AGENT-WORKFLOW.md` (`coq-goals`, the LSP tool, targeted and
`vos` builds).
- Step 4 is done (merge `e911635`; `typing/place_sum.v`, examples in
  `typing/examples/place_sum.v`).
  - Place type `SumLty tyl i lt`, with context step `PSum`.
  - Rules: case analysis on places (`type_case_place(_root)`, `type_case_oplace`), fold back, and
    assigning a new variant to an owned place (payload of size 1).
  - Limits: no moves or retyping writes through a sum (`pctx_nosum`); `&shr` places restricted
    to product fields; no unit variant or `&uniq` variant assignment.
  - Slow-`Qed` finding: `solve_typing` proofs of `lctx_lft_alive (fp_E …) L α` take about 42 s
    of kernel time each when the signature contains sums. Proving `α` alive once and reusing it
    avoids this.
- Step 5 is done (commit `f1730e1`, merge `deec53d`; `typing/place_resolve.v`, examples in
  `typing/examples/place_resolve.v`; design in `design_docs/verus-belt-phase3-design.md`, section
  "Resolve and drop"). `type_resolve_place_instr` gives up a `&uniq`-rooted place with any
  mix of unblocked and blocked leaves (also below boxes and sums; nested `UniqLty` with
  blocked leaves only), pre-resolving its prophecy to the current value of the place, in
  `1 + lty_nunblk lt` program steps: each unblocked leaf gets a fresh prophecy variable
  (the outer prophecy is pre-resolved through its reservation to the refinement with
  these variables), which is then resolved by sharing the leaf at a fresh lifetime; no
  type condition on the leaves (their contents go back to the lender). Shared-blocked
  leaves must be unblocked first, nested places with unblocked leaves folded first.
  Owned places: the judgement `lty_resolve E L lt Φ` (instances per constructor, from
  `resolve` of the leaf types; blocked/shared-blocked leaves forgotten);
  `resolve_tctx_cons_oplace`/`type_resolve_oplace_instr` resolve and leak;
  `type_drop_oplace_instr` (`drop_boxes lt p;; delete`) resolves and frees the place and,
  recursively, the pointees of its unfolded boxes; it needs no blocked or shared leaf in
  the memory of the place (that memory is lent). `&shr` places need nothing. Examples:
  `get_last` (Qed 7.5 s) and `drop_local` (Qed 15 s), only `functional_extensionality_dep`.
  Finding: `solve_typing` on `tctx_extract_ctx` with an unreduced `pctx_plug K lt` /
  `tyl +!! i` in the extracted context did not finish in 10 minutes; `simpl` first.
- Step 6 is done in part (merge `23f1e16` of branch `proto/generalize`; commits `d712831`,
  `a2a314f`, `4c47be9`, `8fb3461`, `4232b76`, `87c66ac`; design in `design_docs/verus-belt-phase3-design.md`,
  section "Step 6: generalizations", which also says precisely what is not done and why).
  - 6.1 assign/copy/move of any size (`typing/place_memcpy.v`): memcpy rules at any path,
    also below boxes, for owned places (copy/move in with retyping, same-type through
    sums, move/copy out) and `&uniq` places (same-type assignment, copy out); retyping
    through sums and retyping `&uniq` leaves not done (core fixed by the lender).
  - 6.2 nested `&uniq`: the lazy fold handles `UniqLty` at any depth and below boxes
    (`lty_simple` includes `UniqLty`; the node holds `⧗(2 + m)` and `time_ctx`); unfolding
    below the root (`type_(un)fold_place_uniq_deep_instr`, new `cpd_rebody_ext`); further
    unfolding inside a nested place (`tctx_place_nested_change_hole`). Not done: reborrows
    at nesting depth ≥ 2 or below boxes, shares inside nested places.
  - 6.3 sums: unit variants of owned places (`type_sum_unit_oplace_instr`), variants of
    `&uniq` places (`type_sum_assign_place_instr`); `&shr` through sums by composition
    (but `type_case_shr` uses `eq_rect_eq`); retyping through sums not done.
  - 6.4 shared mode: resolving a `&uniq` place while a leaf is shared
    (`type_resolve_place_instr`, shared lifetime alive; `shr_blocked_owned` keeps the
    persistent predicate); sharing the root is the existing `&uniq` reborrow + share.
  - 6.5 n-ary products: owned places only (`tctx_(un)fold_oplace_xprod`, via the `mod_ty`
    iso and `pctx_retype`); `&uniq` places need a new `ConsLty` place type (not done).
  - 6.6 boxes at any depth (`type_unfold_oplace_own_instr`, `type_unfold_place_own_instr`).
  - Examples (new files, only `functional_extensionality_dep`; Qed times measured 6 files
    in parallel): `place_memcpy.v` (`replace_first` 7.3 s, `set_first_pair` 8.4 s,
    `take_inner` 5.9 s), `nested_deep.v` (`get_snd_first` 9.8 s, `get_inner_mid` 15.4 s),
    `place_sum2.v` (`clear` 2.6 s, `set_some_fst` 12.9 s), `place_deep_box.v`
    (`deep_read` 7.7 s, `deep_get` 6.1 s), `place_shr_resolve.v` (`first_ref` 18.8 s),
    `place_struct.v` (`set_mid` 11.4 s).
  - Findings: an instruction used with `type_seq` must be parenthesized as its own
    expression (`(drop_boxes …;; delete …);; e`), otherwise `eapply` loops in unification;
    `rewrite -(lty_fold_plug_eq' …) //` left no goal for the following `iApply` (use
    `; [|done]` for the side condition); `rewrite` in a proof-mode goal also rewrites the
    hypotheses of the environment, so give explicit instances; rules that open
    a `&uniq` place for several steps need the mask-generic `wp_pctx_expr_mask`.
- **Step 7 refocused** (user, 2026-10-27): fix the existing slowdowns, with no new automation.
  - Known slow cases: `get_box` (about 3.5 min), `get_mid_shr` (about 14 min), the dropped
    `&uniq`-below-`&shr` example, `solve_typing` on liveness with sums in the signature, and
    `tctx_extract_ctx` on unreduced `pctx_plug`.
  - After step 7, stop and review the state of the project with the user.
- Step 7 is done (branch `proto/perf`; commits `3c43dc1`, `5fb911e`, `c2115b5`; design in
  `design_docs/verus-belt-phase3-design.md`, section "Step 7: performance").
  - One cause for cases 1–4: `solve_typing` proofs of `ϝ ⊑ₑ α ∈ fp_E …` (liveness and
    inclusion from the function's lifetime context). Unification instantiated the tail of
    `elem_of_list_here` with a half-reduced list, and the kernel's conversion of it with
    `fp_E …` is exponential in the depth of the signature's types. Fix in
    `typing/base.v`: hints that normalize the spine of such lists (`list_spine_norm`)
    before membership/`⊆+` search. `Qed`s: `get_mid_shr` 857 s → 3.7 s, `get_mid`
    454 s → 13 s, `get_box` 209 s → 8.5 s, `share_first` 47 s → 23 s; liveness alone
    30 s / > 10 min → ~0 s. The `&uniq`-below-`&shr` read is now an example
    (`get_uniq_shr` in `place_shr.v`, 4.6 s; before: not finished in 25 min).
  - Case 5 (`tctx_extract_ctx` on unreduced `pctx_plug`/`+!!`) does not reproduce; the
    `simpl` in `place_resolve.v` was removed.
  - Also fixed: an 82 s `rewrite` in `place.v` (now `iEval`, the rewrite also tried
    the proof-mode hypotheses) and a 25 s failing `f_equiv` in three `uniq_util.v`
    lemmas.
  - Full clean build `make -j8`: 1789 s → 859 s (total CPU 4825 s → 3014 s).
    Slowest left: `pcell_example_type` `Qed` 96 s (cost spread over the typing steps,
    not identified), then `Qed`s of 14–24 s and some `Print Assumptions` (13–25 s).

- **PUniq** is done (branch `proto/puniq`, merges `7aec4e2`, `59d7865`, `0ff3867`; main
  commits `b53d379`/`fdc556d` (PUniq, access), `a37347e` (receipts), `fcaf81d` (a), `5c050e2`
  (b), `64b6ccb` (c), `b9d210a` (d), `2036711` (Uniq-mode reborrow, e), `6009ee0`, `2523b01`, examples
  `4f23b51`, `5ff186c`, `bd4f79d`, `0007d87`; design in `design_docs/verus-belt-phase3-design.md`, section
  "PUniq").
  - `pctx` has a constructor `PUniq κ K` (the referent of a nested `&uniq`); the legacy split
    `ltype_own_plug` needs `PctxNoUniq K` (instance-implicit in the existing rules, solved
    automatically in the examples).
  - `typing/pctx_acc.v`: the access to the hole of any context from `Owned m`, opening the
    enclosing borrows one after the other (credits bounded by the depth, none without
    `PUniq`); the closer extends the reservations of all enclosing borrows by the new
    prophecy variables (tokens passed from the outermost to the innermost) and may change
    the core. The hole is in `Owned` mode, or in `Uniq κ` mode if it is the whole referent
    of the innermost borrow.
  - Owned places now hold `lty_nrc` receipts (a blocked leaf below borrows holds one more
    per level above it outside its last segment); `blocked_uniq` is guarded by `κ ⊓ ty_lft`.
  - `typing/place_puniq.v`: own-rooted rules at any `K`: unfold/fold of `&uniq` (both
    modes), pairs (both modes), boxes; reborrow (at `κ1 ⊓ … ⊓ κk ⊓ α`) and unblock (both
    modes); write/copy of size 1 (both modes); resolve/drop with nested borrows whose
    leaves are all blocked (`lty_rslv`); shared borrow and unblock (`Owned` mode).
  - Examples `typing/examples/place_puniq.v` (only `functional_extensionality_dep`, Qed
    10–14 s; clean full build 16 min): `get_inner_first_own`, `write_deep` (`&mut &mut &mut i32`), `assign_two`,
    `box_uniq` (`Box<&mut i32>`).
  - Not done: memcpy of any size and sums below `PUniq`, resolving nested places with
    unblocked leaves, step-free (`tctx_incl`) conversions below `PUniq`, reading shared
    leaves below `PUniq`. The uniq-rooted rules are kept; see the report for which are
    redundant.

- **PShr** is done (branch `proto/pshr`, merge `eaecb29`; commits `6456f8c` (ShrLty, PShr,
  PctxNoShr), `234c7b3` (shared views, address below PShr), `2358d70` (a, b), `c338833`
  (c, d), `6384416` (e, example), `daeec61` (gap of PUniq), examples `71bf975`, `1bb36c3`,
  `c27f2d1`; design in `design_docs/verus-belt-phase3-design.md`, section "PShr").
  - Place type `ShrLty lt κ` (an unfolded `&shr{κ}`: the leaf of `&shr{κ} (lty_fold lt)` and
    the variants of the sums of `lt` at the unchanging referent, `lty_vin`; both modes) and
    the context step `PShr κ K`; the referent is a read-only view (no `Shared` borrow kind).
    `PctxNoShr K` (implied by `PctxNoUniq K`) for `pctx_acc` and the rules of
    `place_puniq.v` (instance-implicit, examples unchanged).
  - `typing/place_pshr.v`, for `K[ShrLty (K2[lt]) κ]` (`PctxNoShr K`, `K2` any: fields,
    sums, boxes, `&uniq`, further `&shr`): phase 1 opens `K` (`pctx_acc`), loads the shared
    reference and copies its persistent ownership; phase 2 pushes a persistent shared view
    through `K2` (`shr_pctx_view`, lifetime `pctx_slft K2 κ`: `κ ⊓ κ'` below `&uniq{κ'}`,
    `κ'` below `&shr{κ'}`). Rules: (a) unfold/fold `&shr` at any position and view changes
    below it; (b) read of size 1; (c) shared borrow of a sub-place at `pctx_slft K2 κ`;
    (d) case analysis recording the variant (no `eq_rect_eq`); (e) `lty_rslv_shr`; and the
    gap of PUniq: reading a shared-blocked leaf below unique borrows.
  - Examples `typing/examples/place_pshr.v` (only `functional_extensionality_dep`):
    `get_snd` (`( **x).1`, `&&(i32,i32)`, Qed 4.6 s), `first_ref` (`&( **x).0 : &'b i32` from
    `&'a mut &'b (i32,i32)`, 10.3 s), `get_boxed` (`*( **b).1`, `Box<&(i32, Box<i32>)>`,
    6.4 s), `get_or_zero` (`match **b`, `Box<&Option<i32>>`, 13.2 s). Clean full build 16:40.
  - Not done: copies of any size below `PShr`; step-free versions; uniq-rooted places
    containing `ShrLty`. Redundancy (design doc): the `&shr` rules on references in slots
    (`tctx_shr_place`, `type_deref_shr_own/uniq_instr`, `type_case_shr`,
    `type_read_place_shr_instr`, up to a step `type_read_oplace_shr_instr`); not for
    `&shr` values outside slots.

- **Any size and sums below PUniq** is done (branch `proto/size-sums`, merge `ee896c6`;
  commits `0c9e144`, `86f9033`, `50d8980` (rules), `f3436d4`, `79a8939`, `65d15ea`,
  `1dbd263` (examples); design in `design_docs/verus-belt-phase3-design.md`, section "Any size and sums
  below PUniq").
  - New file `typing/place_deep.v`. One leaf access, `oplace_leaf_acc` (`pctx_acc`, plus
    the body of the innermost borrow in `Uniq` mode), gives the cells (guarded by a token),
    the value's ownership without laters and a closer for a new value; the rules take
    their credits and receipts from the instruction's own first step, so the programs are
    those of the `PctxNoUniq` rules.
  - Rules (any `K` with `PctxNoShr`, both modes): `type_memcpy_oplace_deep_instr` (same-type
    assignment of any size, old value resolved), `type_memcpy_copy_from_oplace_deep_instr`
    (copy of a `Copy` leaf), `type_memcpy_copy_from_oplace_pshr_instr` (copy of any size
    below `PShr`), `type_case_oplace_deep`, `type_fold_oplace_sum_deep_instr`,
    `type_sum_assign_oplace_deep_instr` (payload of size 1), `type_sum_unit_oplace_deep_instr`,
    `type_sum_memcpy_oplace_deep_instr` (payload of any size). Reborrow/unblock/read/write/share
    of payload leaves below `PUniq` work with the existing `PUniq` rules (no side condition
    on `PSum`). Moves and retyping assignments stay restricted to `PctxNoUniq` (sound only
    there).
  - Examples (only `functional_extensionality_dep`): `typing/examples/place_deep.v`:
    `swap_snd` (copy and assign `( **x).1`, two cells, `&mut &mut (i32,(i32,i32))`, Qed 17.8 s),
    `get_pair` (`**x` of `& &(i32,i32)`, 3.3 s); `place_deep_sum.v`: `set_some_first`
    (`if let Some(p) = &mut **x { p.0 = 1 }`, with a reborrow of `p.0`, 55.9 s), `reset`
    (`**x = None; **x = Some(y)`, 20.3 s). The cost of `set_some_first` is spread over the
    steps of its `Some` branch (no single slow conversion).
  - Newly redundant (design doc): `type_memcpy_oplace_same_instr`,
    `type_memcpy_copy_from_oplace_instr`, `type_case_oplace`, `type_sum_assign_oplace_instr`,
    `type_sum_unit_oplace_instr`; for references in slots `type_memcpy_place_instr`,
    `type_memcpy_from_place_instr`, `type_case_place(_root)`, `type_sum_assign_place_instr`;
    up to a step `tctx_fold_oplace_sum`, `tctx_fold_place_sum`. None removed.

- **Resolve to a readable state** is done (branch `proto/resolve-readable`; commits `c3baea7`
  (`ty_gho_res`, `resolve_keep`, `ResOwn`), `60c9495` (`OfRes`, `ResUniqLty`, conversions),
  `bce3c21` (views, share-to-view, `lty_res`, rule), `2321597` (read, unblock), `8558329`
  (drop, `res_gen`), `5227b82` (`res_pair`), `1f96f25` (`res_nested`), `15e7d45` (share,
  leaf fold); design in `design_docs/verus-belt-phase3-design.md`, section "Resolve to a readable
  state", "Outcome").
  - New field `ty_gho_res` (no laws). `resolve` is unchanged; a new `resolve_keep` keeps the
    resolved ownership. For `&uniq{κ}`, `gho_res` is the sharing of the current value at κ.
  - New place types `OfRes ty` and `ResUniqLty lt κ` (Owned only). The view `lty_view` is
    the mapping `S_κ`. `lty_simple` is false for both, so the `pctx_acc` closers take
    `lty_simple lt'`.
  - The judgement `lty_res E L lt lt' k Φ` is structural, with `uniq_leaf`/`uniq_cpd` cases.
    The rule `type_resolve_oplace_res_instr` is `skipn k` and learns `Φ`.
  - Below `ResUniqLty`: read (Copy, size 1), shared borrow of a leaf, unblock, and a fold of
    a leaf referent. Conversions of `OfRes` for `ResOwn`, products, boxes (mode 1), `&uniq`,
    and `&shr`. A separate drop.
  - Examples (only `functional_extensionality_dep`): `res_gen` (generic `T`, Qed 4.3 s),
    `res_pair` (`(Box<i32>, &mut (i32,i32))`, 11.0 s), `res_nested` (`&mut &mut (i32,i32)`
    with a blocked leaf, unblocked after the resolve, 27.8 s).
  - Not done: folding compound resolved referents (needs a heap lemma combining guarded
    disjoint ranges), case analysis on `OfRes` sums, `ShrBlocked` in views, and copies of
    size > 1 below `ResUniqLty`. No rule is newly redundant; `lty_simple_true` was removed.

- **Resolve gaps** (branch `proto/resolve-gaps`; commits `239d81b` (generic resolution:
  `ty_gho_res_of_own`, `resolve_keep_just` for every type, `&uniq`'s `gho_res` with an
  unresolved disjunct, `OfRes` sums), `5830402` (`res_opt`), `da990d3` (compound fold,
  heap lemma `and_cells_app_combine_fancy`), `0ed7fe0` (shared-blocked leaves in views),
  `addad0a` (copies of any size below `ResUniqLty`); design in
  `design_docs/verus-belt-phase3-design.md`, "Resolve to a readable state", "Gaps filled").
  - An arbitrary `T` is resolved and dropped (not read: no `ResOwn`); a `Copy` `T` is
    resolved keeping `OfTy` (`lty_res_copy`). `OfRes (&uniq)` → `ShrLty` is an instruction.
  - Case analysis on `OfRes (Σ! tyl)`, fold back; fold of compound views (pairs, boxes) to
    `ShrLty (OfTy (lty_fold lt)) κ`; shared-blocked leaves viewed at `κ ⊓ α` (resolution
    needs their lifetimes alive); memcpy of `Copy` leaves of any size from views.
  - Examples (only `functional_extensionality_dep`): `res_gen` 1.5 s, `res_gen_copy` 3.7 s,
    `res_opt` 10.2 s, `res_fold` 8.4 s, `res_shr` 28.7 s, `res_copy` 6.2 s.
  - Not done: sums and nested `UniqLty` in the compound fold; unblocking shared-blocked
    leaves of a view. Newly redundant: `tctx_fold_oplace_res_uniq_leaf`.

- **Resolve open points** (branch `proto/res-open-points`, commit `ea35ca7`; design in
  `design_docs/verus-belt-phase3-design.md`, "Resolve to a readable state", "Open points filled").
  - Shared-blocked leaves of a view keep their inheritance in a borrow at the view's
    lifetime; `unblock_tctx_oplace_res_shr` makes them ordinary shared leaves once their
    lifetime ends.
  - The compound fold accepts sums (`lty_rfold`, `lty_fold_sum_eq`) and nested `&uniq`s
    with a leaf referent (`view_uniq` keeps the inner token guard;
    `type_fold_oplace_res_uniq_meta_instr`, value up to `lty_meq`).
  - Examples (only `functional_extensionality_dep`): `res_shr_end` 25.3 s, `res_opt_fold`
    26.1 s, `res_nested_fold` 8.9 s.
  - Not done: folding a nested `&uniq` with a compound referent (its prophecy variable is
    reserved, so there is no token guard; fold the inner borrow before resolving). Newly
    redundant: none.

## Decisions (user, 2026-10-28)
- The branch is renamed `prophecy-ra` → `place-types` (local only).
- Standard axioms such as `eq_rect_eq` are acceptable.
- End state: all places are own-rooted with arbitrary nesting, so `(own (uniq _))` replaces
  rooting a place at a `&uniq`. Remove the uniq-rooted rules once they are redundant, but not
  before.
- **Queued after PUniq** (user, 2026-10-28): the same for `PShr`, a place-context step into the
  referent of a `&shr`. It should support nested shared borrows in own-rooted places, at any
  position, mixed with the other steps.

- **Value-rooted places** (branch `proto/value-roots`, merge `0954081`; commits `722bf84`,
  `4bc943c`, `cea58f1`, `5f08649`, `2641353`, `632d3f4`; design in
  `design_docs/verus-belt-phase3-design.md`, "Value-rooted places", "Outcome").
  - `p ◁ₗ lt` (`vplace.v`): `∃ D, ⧖D ∗ ⧗(lty_vnrc lt) ∗ vroot_own lt …`, the root being the
    node value of the root pointer (`own_nval`/`uniq_nval`, `ltype.v`). `p ◁ₗown{n} lt'` and
    `p ◁ₗ{κ} lt'` are notations for `p ◁ₗ OwnPtrLty n lt'` and `p ◁ₗ UniqLty lt' κ`.
  - Root access `vroot_acc` (`pctx_acc.v`) for contexts whose first step is the root
    pointer (`PctxVRoot`); the deep rules of `place_puniq`, `place_pshr`, `place_deep` are
    stated once over `p ◁ₗ pctx_plug K lt`, the own-rooted ones are corollaries.
  - `place.v`, `place_nested.v` and the uniq-rooted rules of `place_shr`, `place_sum`,
    `place_memcpy`, `place_resolve` deleted; 11 example files ported (only
    `functional_extensionality_dep`). Clean build 20:56.
  - Not generalized: `PctxNoUniq` (own-rooted) rules and `place_res*`; a root `&shr` value
    for the pshr rules.
