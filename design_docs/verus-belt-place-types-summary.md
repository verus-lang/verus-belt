# Place types in VerusBelt: summary of the plan so far

> **Note (stage 5 of the MiniRust memory model, 2026-10-30).** The legacy word-level place
> files and examples named in this document (`ltype.v`, `lpath.v`, `pctx_acc.v`,
> `vplace.v`, `place_*.v`, `examples/place_*.v`, `get_first.v`, `nested_*.v`, …) were
> deleted. The byte versions now carry the same file names (e.g. `bltype.v` became
> `ltype.v`), so a file name below may now refer to its byte version. See
> `design_docs/minirust-memory-model.md`, "Outcome: legacy place layer deleted".

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

## Unified place read (branch `proto/read-unify`, 2026-11-01)

One rule reads from any non-blocked place, whatever mix of owned pointers, unique borrows,
shared references and resolved unique borrows is above the leaf: `type_read_place_instr`
(`typing/place_read.v`). Two merges: stage 1 (everything but resolved places), stage 2 (the
context step `PResUniq` for resolved unique borrows, and resolved leaves).

```coq
Lemma type_read_place_instr {𝔅 𝔄} E L I p (K: pctx 𝔅 𝔄) `{!PctxVRoot K} `{!PctxRead K}
    (lt: lty 𝔅) (ty: type 𝔅) κs :
  pctx_rleaf K lt ty κs → Copy ty → lctx_lft_alive E L (pctx_alv K lt ⊓ κs) →
  typed_instr E L I +[p ◁ₗ pctx_plug K lt] (!ᶜ{ty.(ty_mty)} (pctx_vexpr K p))
    (λ v, +[v ◁ᵥ ty; p ◁ₗ pctx_plug K lt])
    (λ post '-[x], post -[pctx_get K x.1; x]).
```

- **Instruction.** `read_copy m e := Load Na1Ord m e` (`lang/lang.v`), notation `!ᶜ{m} e`
  (`lang/notation.v`, `expr_scope`, level 9). `W.of_expr` (`lang/tactics.v`) reifies it as a
  `Load`, so `simpl_subst` turns it into `Load Na1Ord m e`. No `Skip`: as in the old
  `PctxNoUniq` and `PShr` reads, `wp_persistent_time_receipt` gives the credits of the first
  program step before the access (the whole instruction is at `⊤ ∖ ↑advN`).
- **Contexts.** Any `K` whose root step is `POwn`, `PUniq`, `PShr` or `PResUniq`
  (`PctxVRoot`, extended to `PShr` and `PResUniq`, so the root may also be a shared reference
  value `p ◁ₗ ShrLty …` or a resolved unique borrow value `p ◁ₗ ResUniqLty …`). Owned places
  are the root `POwn n`: `p ◁ₗown{n} K[lt]` is `p ◁ₗ (POwn n K)[lt]`. `PctxRead K` (a type
  class, solved by the structure of `K`): the siblings below a unique borrow are simple, down
  to the first shared reference (needed by the access `vroot_acc` above it); since
  `pctx_simple (PResUniq _ _) = False`, a resolved unique borrow is below no unique borrow
  (where `ResUniqLty` has no interpretation anyway).
- **`PResUniq κ K`** (`lpath.v`): a new `pctx` constructor, the referent of a resolved unique
  borrow (`pctx_plug` gives `ResUniqLty`). It behaves like `PUniq` in the functions on values,
  paths, refinements and receipts, has `pctx_nonempty`, `pctx_simple`, `pctx_noshr`,
  `pctx_nouniq` false (it is never accessed by `pctx_acc` and not split by `ltype_own_plug`),
  and is like `PUniq` in the shared-view functions of `place_pshr.v` (`lty_fold (ResUniqLty lt
  κ) = uniq_bytes κ (lty_fold lt)`). All functions and lemmas on `pctx` were extended
  (mechanically, in `lpath.v`, `pctx_acc.v`, `place_puniq.v`, `place_pshr.v`,
  `place_res_ops.v`); `pctx_hmode_ne` and `pctx_vhmode_ne_le/ge` now take `PctxNoShr`.
- **Readable leaves** `pctx_rleaf K lt ty κs := pctx_rleafb K true lt ty κs`: at the hole,
  `lty_rleaf b lt ty κs` (`place_res_ops.v`, replacing `view_rleaf`): `OfTy ty` with
  `κs = static`, `ShrBlocked ty β` with `κs = β`, and, if `b` (no `PUniq`/`PResUniq` above),
  `OfRes ty` for `ResOwn ty` with `κs = static`; below a shared reference, any `lt` with
  `ty = lty_fold lt` and `κs = static`. `Blocked` is not readable.
- **Lifetimes** `pctx_alv K lt` (was `pctx_ralv`; since `proto/place-polish` the one notion
  of all place rules, in `pctx_acc.v`): `ty_lft (lty_fold (UniqLty K'[lt] κ)) ⊓ …` at each
  `PUniq κ K'` above the first shared reference or resolved borrow (the old `pctx_ulft`
  condition), and `pctx_salv K2 κ` at the first `PShr κ K2` or `PResUniq κ K2` (the old
  shared/view condition).
- **Proof.** `pctx_read_split` splits `K` at its first `PShr` or `PResUniq` with the new
  context composition `pctx_app` (`lpath.v`, with `pctx_plug/get/expr/vexpr/pat/path/loc/rfn_app`).
  Above it, `type_read_vplace_noshr` (the old deep read, generalised to shared-blocked
  leaves, in both modes) and `type_read_vplace_ores` (a resolved leaf, through
  `ltype_own_plug`); below a `PShr`, `type_read_vplace_pshr(_root)` (the old `place_pshr`
  reads); below a `PResUniq`, `type_read_vplace_res(_root)`, through `wp_view_read`, which
  accesses the view (`view_pctx_acc`) down to the hole (shared at `pctx_slft K2 κ ⊓ κs`) or to
  the next `PShr`, whose shared view is pushed through the rest (`shr_pctx_view`), so shared
  references inside views are read too (the old rule needed `PctxNoShr K2`).
- **`Copy` implies `NoCell`.** `Copy` has a new first field `copy_nocell : NoCell 𝔄`
  (`typing/type.v`, with `Hint Extern`s that find `NoCell`/`NoCellL` from `Copy`/`ListCopy`
  hypotheses). No rule that takes `Copy` takes `NoCell` any more (the read rule,
  `type_load_own_bytes_copy_instr`, `type_load_shr_bytes_copy_instr`,
  `type_cell_shr_load_instr`, `type_pcell_load_sc_instr`, `shr_view_copy`, `wp_load_shr_view`,
  the memcpy-copy rules). `simple_type_copy`, `base_copy`, `mod_ty_copy` and `fix_copy` now
  take a `NoCell` hypothesis (solved by computation at concrete syntactic types).
- **Deleted:** `type_read_oplace_instr` (`place_own.v`), `type_read_oplace_shr_instr`
  (`place_shr.v`), `type_read_vplace_deep_instr`, `type_read_oplace_deep_instr`
  (`place_puniq.v`), `type_read_vplace_pshr_root_instr`, `type_read_vplace_pshr_instr`,
  `type_read_oplace_pshr_instr` (`place_pshr.v`), `type_read_oplace_res_leaf_instr`,
  `type_read_oplace_res_instr`, `type_read_oplace_res_shrblk_instr` (`place_res_ops.v`), and
  `view_rleaf` (now `lty_rleaf false`). Examples ported: `place_own`, `place_struct`,
  `place_pshr`, `function`, `place_res`; their programs read with `!ᶜ{MInt i32} …` and the
  proofs apply `type_read_place_instr` with the whole context (e.g.
  `POwn PTR_SIZE (PResUniq α (PUniq β (PFst PHole (OfTy i32t))))`), side conditions
  `[by constructor|apply _|solve_typing]` (`[by split|…]` below a shared reference).
- **Other changes.** `pctx_simple (PShr _ _) = True` (a shared reference is simple whatever its
  referent); the closers of `pctx_acc`/`vroot_acc` accept the old pattern of the hole instead of
  the inclusion of its blocked lifetimes in the enclosing borrow lifetimes
  (`⌜p' = p⌝ ∨ [∗ list] κ ∈ pctx_ulfts K, pat_ok κ p'`), so that a shared-blocked leaf below a
  unique borrow can be closed again unchanged; `pctx_vroot_nonempty` (unused) deleted.
- **Deviations from the requested statement.** The extra class `PctxRead K` (above); no
  `Skip`; `pctx_rleaf` is a notation for `pctx_rleafb K true` (the flag tracks whether
  resolved leaves are readable).

## Unified place move (branch `proto/move-unify`, 2026-11-01)

One rule moves the value out of a leaf of any owned path: `type_move_place_instr`
(`typing/place_own.v`).

```coq
Lemma type_move_place_instr {𝔅 𝔄} E L I p (K: pctx 𝔅 𝔄) `{!PctxVRoot K} `{!PctxNoUniq K}
    (ty: type 𝔅) :
  pctx_nosum K →
  typed_instr E L I +[p ◁ₗ pctx_plug K (OfTy ty)] (!ᵐ{ty.(ty_mty)} (pctx_vexpr K p))
    (λ v, +[v ◁ᵥ ty;
      p ◁ₗ pctx_plug (pctx_retype K (uninitₛ (ty_bsize ty))) (OfTy (↯ (ty_bsize ty)))])
    (λ post '-[x], post -[pctx_get K x.1;
      (pctx_reset (𝔅':=uninitₛ (ty_bsize ty)) K x.1 (), x.2)]).
```

- **Instruction.** `read_move m e := Load Na1Ord m e` (`lang/lang.v`), notation `!ᵐ{m} e`
  (`lang/notation.v`, as `!ᶜ`); `W.of_expr` reifies it as a `Load`. No `Skip`.
- **Contexts.** Rust moves only out of owned paths: `PctxNoUniq K` (no `PUniq`, `PShr`,
  `PResUniq`), so the root step (`PctxVRoot`) is `POwn n`: `p ◁ₗ pctx_plug (POwn n K') lt` is
  `p ◁ₗown{n} pctx_plug K' lt`. The value may contain cells (they are moved with it,
  `val_cells`).
- **Sums (deviation: `pctx_nosum` kept).** The payload of a sum place `SumLty tyl i lt` has
  the type of variant `i` (`lt: lty (𝔄l !!ₗ i)`), so a payload left uninitialized (of type
  `uninitₛ n`) under the same variant is not expressible without a new place-type
  constructor (or a retyped `typel`, for which there is no type of the retyped payload);
  `pctx_retype` drops the sum layer, which is only sound without sums. Moving the whole sum
  (and then matching on the value) is allowed.
- **Deleted:** `type_move_oplace_instr` (`place_own.v`). Examples ported: `place_own`
  (`box_pair`: `!ᵐ{MPtr} (ToLit "b")`, context `POwn (PTR_SIZE + 4) (PFst PHole _)`),
  `pcell_move` (three moves).

## Unified place write (branch `proto/write-unify`, 2026-11-01)

One rule writes a value into a leaf of any writable place: `type_write_place_instr`
(`typing/place_write.v`).

```coq
Inductive pctx_wty {𝔅 𝔄} (K: pctx 𝔅 𝔄) (ty: type 𝔅) :
    ∀ {𝔅' 𝔄'}, type 𝔅' → pctx 𝔅' 𝔄' → (~~𝔄 → ~~𝔅' → ~~𝔄') → Prop :=
| pctx_wty_same : pctx_wty K ty ty K (pctx_set K)
| pctx_wty_strong {𝔅'} (ty': type 𝔅') :
    pctx_nouniq K → pctx_nosum K → ty_bsize ty' = ty_bsize ty →
    pctx_wty K ty ty' (pctx_retype K 𝔅') (pctx_reset K).

Lemma type_write_place_instr {𝔅 𝔄 𝔅' 𝔄'} E L I p pb (K: pctx 𝔅 𝔄) `{!PctxNoShr K}
    `{!PctxVRoot K} (ty: type 𝔅) (ty': type 𝔅') (K': pctx 𝔅' 𝔄') f Φ :
  pctx_wty K ty ty' K' f → resolve E L ty Φ → lctx_lft_alive E L (pctx_alv K (OfTy ty)) →
  typed_instr E L I +[p ◁ₗ pctx_plug K (OfTy ty); pb ◁ᵥ ty']
    (pctx_vexpr K p <-{ty'.(ty_mty)} pb)
    (λ _, +[p ◁ₗ pctx_plug K' (OfTy ty')])
    (λ post '-[x; b], λ mask π, Φ (pctx_get K x.1) π → post -[(f x.1 b, x.2)] mask π).
```

- **Instruction.** `write m e1 e2 := Store Na1Ord m e1 e2` (`lang/lang.v`), notation
  `e1 <-{m} e2` (`lang/notation.v`, level 80); `W.of_expr` reifies it as a `Store`. No
  `Skip` (the old deep writes had `Seq (Seq Skip Skip)`, `ReBor;;` in the programs): the
  first step (`wp_cumulative_time_receipt_linear` on the whole instruction) gives the
  credits (to open the enclosing borrows and to resolve the old value) and the cumulative
  time receipts (to raise the depth of the place to `pctx_dlev K` plus the depth of the new
  value).
- **Contexts.** Any `K` with `PctxNoShr` (no `PShr`, no `PResUniq` on the path; the siblings
  below a `PUniq` are simple, as for the deep writes) and `PctxVRoot` (root `POwn` or `PUniq`;
  `p ◁ₗown{n} K'[lt]` is `p ◁ₗ (POwn n K')[lt]`). Sums are allowed (same type).
- **Leaves.** Only `OfTy ty` (in particular `OfTy (↯ n)`, an uninitialized leaf). Blocked and
  shared-blocked leaves are not writable (Rust forbids writing a borrowed place), resolved
  leaves are not needed. No other blocked-free condition: the siblings are untouched.
- **Strong vs. weak update: `pctx_wty K ty ty' K' f`**, an inductive side condition (like
  `lty_rleaf`), solved by `apply pctx_wty_same` or `by apply pctx_wty_strong`. It is
  relational, not a function of `K` (deviation): the result of the same-type write keeps the
  sum layers of `K`, which `pctx_retype` drops (a sum payload has the type of its variant),
  so no single retyping function covers both. `pctx_wty_strong` needs an owned path
  (`pctx_nouniq`, so the root is `POwn`) without sums; `pctx_wty_bsize` gives the size.
- **Lifetime.** One condition, `pctx_alv K (OfTy ty)` (was `pctx_ulft K (OfTy ty)`, the
  folded type at the outermost unique borrow; `static` without one: `solve_typing`).
- **Access.** `wp_vplace_wacc` (CPS around the address `pctx_vexpr K p`): the bytes and the
  ownership of the old value (without laters), and a closer `vplace_wcloser` for a new value
  of type `ty'` at new depths, giving `p ◁ₗ pctx_plug K' (OfTy ty')` at `f x b`. Same type:
  `vplace_leaf_acc` (`place_deep.v`); strong: `ltype_own_plug` and `pctx_retype`.
- **Deleted:** `type_write_oplace_instr` (`place_own.v`), `type_write_vplace_deep_instr`,
  `type_write_oplace_deep_instr` (`place_puniq.v`), and `type_store_own_bytes_instr`
  (`value_ctx.v`): it is the instance `K = POwn n PHole`, `pctx_wty_same`, after
  `tctx_own_to_oplace` (with `resolve_just`, then `tctx_oplace_to_own`); it was unused.
  Examples ported: `place_own`, `place_struct`, `pcell_example`, `pcell_move`, `place_res`
  (programs `ToLit "r" <-{MInt i32} "five"` without `ReBor;;`; proofs
  `eapply (type_write_place_instr _ _ _ vr v5 (PUniq β PHole) i32t i32t);
  [apply pctx_wty_same|apply resolve_just|solve_typing]`).

## Unified place memcpy (branch `proto/memcpy-unify`, 2026-11-01)

A byte copy between places, `pctx_vexpr Kd pd <-ᵇ{n} pctx_vexpr Ks ps` (`memcpy n e1 e2 :=
MemCopy Na1Ord n e1 e2`, `lang/lang.v`; notation `e1 <-ᵇ{n} e2`, level 80; reified as a
`MemCopy`), is byte-preserving (no typed memcpy). Two rules (`typing/place_memcpy.v`), by the
source:

```coq
Lemma type_memcpy_copy_place_instr {𝔅d 𝔄d 𝔅 𝔄 𝔄d'} E L I pd ps (Kd: pctx 𝔅d 𝔄d)
    `{!PctxNoShr Kd} `{!PctxVRoot Kd} (tyd: type 𝔅d) (Kd': pctx 𝔅 𝔄d') fd Φ
    (Ks: pctx 𝔅 𝔄) `{!PctxVRoot Ks} `{!PctxRead Ks} (lt: lty 𝔅) (ty: type 𝔅) κs :
  pctx_wty Kd tyd ty Kd' fd → resolve E L tyd Φ →
  lctx_lft_alive E L (pctx_alv Kd (OfTy tyd)) →
  pctx_rleaf Ks lt ty κs → Copy ty → lctx_lft_alive E L (pctx_alv Ks lt ⊓ κs) →
  typed_instr E L I +[pd ◁ₗ pctx_plug Kd (OfTy tyd); ps ◁ₗ pctx_plug Ks lt]
    (pctx_vexpr Kd pd <-ᵇ{ty_bsize ty} pctx_vexpr Ks ps)
    (λ _, +[pd ◁ₗ pctx_plug Kd' (OfTy ty); ps ◁ₗ pctx_plug Ks lt])
    (λ post '-[xd; xs], λ mask π, Φ (pctx_get Kd xd.1) π →
      post -[(fd xd.1 (pctx_get Ks xs.1), xd.2); xs] mask π).

Lemma type_memcpy_move_place_instr {𝔅d 𝔄d 𝔅 𝔄 𝔄d'} E L I pd ps (Kd: pctx 𝔅d 𝔄d)
    `{!PctxNoShr Kd} `{!PctxVRoot Kd} (tyd: type 𝔅d) (Kd': pctx 𝔅 𝔄d') fd Φ
    (Ks: pctx 𝔅 𝔄) `{!PctxVRoot Ks} `{!PctxNoUniq Ks} (ty: type 𝔅) :
  pctx_wty Kd tyd ty Kd' fd → resolve E L tyd Φ →
  lctx_lft_alive E L (pctx_alv Kd (OfTy tyd)) → pctx_nosum Ks →
  typed_instr E L I +[pd ◁ₗ pctx_plug Kd (OfTy tyd); ps ◁ₗ pctx_plug Ks (OfTy ty)]
    (pctx_vexpr Kd pd <-ᵇ{ty_bsize ty} pctx_vexpr Ks ps)
    (λ _, +[pd ◁ₗ pctx_plug Kd' (OfTy ty);
      ps ◁ₗ pctx_plug (pctx_retype Ks (uninitₛ (ty_bsize ty))) (OfTy (↯ (ty_bsize ty)))])
    (λ post '-[xd; xs], λ mask π, Φ (pctx_get Kd xd.1) π →
      post -[(fd xd.1 (pctx_get Ks xs.1), xd.2);
        (pctx_reset (𝔅':=uninitₛ (ty_bsize ty)) Ks xs.1 (), xs.2)] mask π).
```

- **Two rules (justified deviation from "one").** The source side differs in kind: a copy
  source is a `Copy` leaf of any readable place (also below shared references and resolved
  unique borrows, where it is only guarded: `wp_memcopy_guarded_gen`), which stays; a move
  source is any leaf of an owned path without sums (as for `type_move_place_instr`), whose
  fancy bytes (with their cells) are transferred (`wp_fbytes_memcopy`; superseded: since
  phase 4/5 of `guarded-mutable-borrows-plan.md` this is `wp_gcont_memcopy`, and the cell WP
  rules are deleted) and which becomes `↯`. One statement would need a computed source result (unchanged place vs retyped
  place, and two transformers) and a disjunction of the two side conditions, for no gain.
- **Destination.** Any writable place as in `type_write_place_instr`, with the new type
  given by `pctx_wty Kd tyd ty Kd' fd` (same type, or strong update along an owned path
  without sums); the old value is resolved. The old "memcpy into a `↯` box changing its type"
  is the strong instance with `Kd = POwn n PHole`, `tyd = ↯ n` (`by apply pctx_wty_strong`),
  after `tctx_own_to_oplace`.
- **Sizes.** The instruction copies `ty_bsize ty` bytes; `pctx_wty` gives
  `ty_bsize ty = ty_bsize tyd` (`pctx_wty_bsize`).
- **Steps.** The first step of the destination address (`wp_cumulative_time_receipt_linear`,
  bound with `pctx_vexpr_to_val`) gives the credits for the destination access and the
  resolution and the time receipts to raise the depth of the destination; the first step of
  the source address (`wp_persistent_time_receipt`) the credits for the source access. No
  `Skip`.
- **Read access.** `wp_vplace_racc` (`place_read.v`) is the read rule's case analysis on the
  shape of the context, factored as an access (a CPS around the address, `vplace_rcont`): the
  address of the leaf, a guard of its bytes by a token `G2` with `dd` laters (the bytes
  themselves, `guards_refl`, for an owned leaf; the shared view's guard for a shared one), the
  persistent ownership of the value, and a closer. `type_read_place_instr` is now this access
  plus `wp_load_na_guarded_gen`; the per-shape read lemmas (`type_read_vplace_noshr`,
  `_pshr`, `_pshr_root`, `_ores`, `_res`, `_res_root`) and `wp_view_read` were replaced by
  the per-shape accesses (`wp_vplace_racc_noshr`, … , `wp_view_racc`), and
  `wp_load_shr_view` (`place_pshr.v`, only used by them) was deleted.
- **Deleted:** `type_memcpy_vplace_deep_instr`, `type_memcpy_oplace_deep_instr`,
  `type_memcpy_copy_from_vplace_deep_instr` (`place_deep.v`),
  `type_memcpy_copy_from_vplace_pshr_instr`, `type_memcpy_copy_from_oplace_pshr_instr`,
  `type_memcpy_copy_from_vplace_pshr_root_instr` (`place_pshr.v`),
  `type_memcpy_copy_from_oplace_res_instr` (and the file `place_res_copy.v`). Examples
  ported: `place_deep` (`swap_snd`) and `new` (`swap_snd_n`): programs
  `ToLit "c" <-ᵇ{8} (… +ₗ #4)` and `(… +ₗ #4) <-ᵇ{8} ToLit "y"`; the boxes `c` and `y` are
  viewed as owned places (`tctx_own_to_oplace`) for the copies.

## Unified place share (branch `proto/share-unify`, 2026-11-01)

One rule borrows shared the leaf at the hole of any readable place: `type_share_place_instr`
(new file `typing/place_share.v`).

```coq
Lemma type_share_place_instr {𝔅 𝔄} E L I p (K: pctx 𝔅 𝔄) `{!PctxVRoot K} `{!PctxRead K}
    α (lt: lty 𝔅) (ty: type 𝔅) (lt': lty 𝔅) :
  pctx_sleaf E L K α lt ty lt' → lctx_lft_incl E L α (pctx_blft K) →
  lctx_lft_alive E L (pctx_alv K lt) →
  typed_instr E L I +[p ◁ₗ pctx_plug K lt] (&ˢ (pctx_vexpr K p))
    (λ v, +[v ◁ᵥ &shr{α} ty; p ◁ₗ pctx_plug K lt'])
    (λ post '-[x], post -[(pctx_vloc K (lty_size lt) x.1, pctx_get K x.1); x]).
```

- **Instruction.** `share e := OfLit e` (`lang/lang.v`; since stage 7 of
  `minirust-memory-model.md`, `share e := place_addr e`, one β step), notation `&ˢ e` (`lang/notation.v`,
  level 9); `W.of_expr` reifies it as an `OfLit`. No `Skip` (the old rules had `Share;;` =
  `Seq Skip Skip` for the owned/unique cases): the first step of the instruction
  (`wp_cumulative_time_receipt_linear` below no shared reference, `wp_persistent_time_receipt`
  otherwise) gives the credits and, for a shared-blocked leaf below a unique borrow, its
  receipt.
- **Contexts.** Those of the read rule: `PctxVRoot K` (root `POwn`, `PUniq`, `PShr` or
  `PResUniq`) and `PctxRead K` (simple siblings below a unique borrow, down to the first shared
  reference).
- **(Superseded by `proto/place-polish`, below: `α` is the lifetime of the result.)**
  **Computed result.** `pctx_shlft K α`: `pctx_blft K α` below no shared reference and no
  resolved unique borrow (`pctx_vlft K = None`), else `pctx_slft K2 κ`, the lifetime of the view
  at the first `PShr κ K2`/`PResUniq κ K2`. `pctx_sleaf E L K β lt ty lt'` (a `Fixpoint`, solved
  by `simpl; split_and!` or `by split`): below no shared reference, `lt = OfTy ty`,
  `lt' = ShrBlocked ty β` and `elctx_sat E L (ty_outlives_E ty β)`, and the hole is not the whole
  referent of a unique borrow (`PUniq κ PHole` gives `False`: in `Uniq` mode a shared-blocked leaf
  has no interpretation of its own); below a shared reference, any `lt`, `ty = lty_fold lt`,
  `lt' = lt`; below a resolved unique borrow, `pctx_vsleaf K2 lt ty` (an unblocked leaf of the
  view, or any leaf below a shared reference in the view) and `lt' = lt`.
- **Lifetimes.** (Superseded, see below.) One condition, `pctx_ralv K lt ⊓ α` (the read rule's lifetimes, and `α`; below
  a shared reference or resolved unique borrow `α` is not used, take `static`).
- **Proof.** Split of `K` as in the read access (`pctx_read_split`): `type_share_vplace_noshr`
  (the old deep share: `vroot_acc` and `ofty_owned_share`, now mask-generic),
  `type_share_vplace_pshr(_root)` (`wp_pshr_open(_root)`), `type_share_vplace_res(_root)`
  through the new view access `wp_view_sacc` (as `wp_view_racc`, returning the shared view of
  the hole; shared references inside the view are now supported, the old rule needed
  `PctxNoShr K2`, and a resolved unique borrow at the root is new).
- **Deleted:** `type_share_oplace_instr` (`place_shr.v`), `type_share_vplace_deep_instr`,
  `type_share_oplace_deep_instr` (`place_puniq.v`), `type_share_vplace_pshr_root_instr`,
  `type_share_vplace_pshr_instr`, `type_share_oplace_pshr_instr` (`place_pshr.v`),
  `type_share_oplace_res_instr` (`place_res_ops.v`). Examples ported: `pcell_example`
  (`&ˢ (ToLit "pair")`, `K = POwn 4 PHole`), `place_pshr` and `function` (`first_ref`:
  `&ˢ (ToLit (Load Na1Ord MPtr (ToLit "x")))`, `K = PUniq α (PShr β (PFst PHole (OfTy i32t)))`,
  `α := static`).
- **Deviations.** Re-sharing a shared-blocked leaf and shared-blocked leaves in views are not
  covered (copy the existing shared reference instead); the outlives condition is part of
  `pctx_sleaf` (it is only needed for an owned leaf); `α` is a dummy below a shared reference
  or a resolved unique borrow.

## Unified place borrow (branch `proto/uniq-unify`, 2026-11-01)

One rule borrows mutably the leaf at the hole of any place on an owned/unique path:
`type_borrow_place_instr` (`typing/place_puniq.v`).

```coq
Lemma type_borrow_place_instr {𝔅 𝔄} E L I p (K: pctx 𝔅 𝔄) `{!PctxNoShr K} `{!PctxVRoot K}
    α (ty: type 𝔅) :
  elctx_sat E L (ty_outlives_E ty α) → lctx_lft_incl E L α (pctx_blft K) →
  lctx_lft_alive E L (pctx_alv K (OfTy ty) ⊓ pctx_balv K α) →
  typed_instr E L I +[p ◁ₗ pctx_plug K (OfTy ty)] (&ᵘ (pctx_vexpr K p))
    (λ w, +[w ◁ᵥ &uniq{α} ty; p ◁ₗ pctx_plug K (Blocked ty α)])
    (λ post '-[x], λ mask π, ∀ m1: ~~ (uniq_borₛ 𝔅),
      uniq_bor_current m1 = pctx_get K x.1 →
      post -[m1; (x.1, (pctx_vpath K, uniq_bor_ξi m1) :: x.2)] mask π).
```

- **Instruction.** `borrow_uniq e := Seq (Seq Skip Skip) (OfLit e)` (`lang/lang.v`), notation
  `&ᵘ e` (`lang/notation.v`, level 9); `W.of_expr` unfolds it. The two `Skip`s stay (the old
  `ReBor;; OfLit …`): the first gives the credits (`wp_persistent_time_receipt`), the second
  the cumulative time receipts at depth `S D` (`wp_cumulative_time_receipt_linear`) for the new
  borrow, the blocked leaf's inheritance (`pctx_hmode K 0` levels) and its receipts
  (`S (pctx_vne K)`). One step at depth `D` gives `⧗(S (S D))`, one short when the leaf has
  depth 0 and `pctx_dlev K = D` (so a single-step `OfLit e` does not suffice).
- **Contexts.** `PctxNoShr K` (no `PShr`, no `PResUniq`: Rust does not borrow mutably below a
  shared reference, and a resolved place is read-only) and `PctxVRoot K` (root `POwn n`, i.e.
  `p ◁ₗown{n} …`, or `PUniq κ`). Sums allowed.
- **Uniform statement.** By the mode of the hole: `pctx_uend K = None` (Owned mode, the old
  deep borrow, now `type_borrow_vplace_owned`) or `Some κ` (the whole referent of the innermost
  unique borrow, a reborrow, now `type_borrow_vplace_uniq`); both had the same conclusion.
  (Since `proto/place-polish`: `α` is the lifetime of the new borrow, `α ⊑ pctx_blft K`, and `α`
  must be alive only for a reborrow, `pctx_balv K α`; see below.)
- **Deleted:** `type_borrow_oplace_instr` (`place_own.v`: the instance `K = POwn n K'` with
  `PctxNoUniq K'`, `pctx_blft K α = α`; its separate proof via `alloc_uniq_body` is gone),
  `type_borrow_vplace_deep_instr`, `type_borrow_oplace_deep_instr`,
  `type_borrow_vplace_uniq_instr`, `type_borrow_oplace_uniq_instr` (`place_puniq.v`; the two
  vplace ones are the per-mode lemmas). Examples ported: `place_own` (`&ᵘ (ToLit "x" +ₗ #4)`,
  `K = POwn _ (PSnd (OfTy i32t) PHole)`), `get_first`, `get_some_first`, `place_res` (programs
  `&ᵘ …` instead of `ReBor;; OfLit …`; proofs `apply (type_borrow_place_instr _ _ _ vb K α i32t);
  [solve_typing|simpl; solve_typing]`).
- **Deviations.** Two `Skip`s inside the instruction (above); the leaf is `OfTy ty` only (Rust
  forbids borrowing a borrowed or moved-out place; a shared-blocked leaf is not mutably
  borrowable).

## Unified place resolve (branch `proto/resolve-unify`, 2026-11-01)

One rule resolves a place to a readable state, at the hole of any context whose path is
owned, the root unique borrow included: `type_resolve_place_instr`
(`typing/place_res_rslv.v`).

```coq
Inductive pctx_res (E: elctx) (L: llctx) :
    ∀ {𝔅 𝔄}, pctx 𝔅 𝔄 → lty 𝔅 → lty 𝔅 → nat →
      (~~𝔅 → blk_map → lpath → proph_asn → Prop) → Prop :=
| pctx_res_root {𝔅} (lt lt': lty 𝔅) k Φ :
    vroot_res E L lt lt' k Φ → pctx_res E L PHole lt lt' k (λ x ζm _, Φ x ζm)
| pctx_res_own {𝔅 𝔄'} n (K: pctx 𝔅 𝔄') (lt lt': lty 𝔅) k Φ :
    lty_res E L lt lt' k Φ → pctx_res E L (POwn n K) lt lt' k Φ.

Lemma type_resolve_place_instr {𝔅 𝔄} E L I p (K: pctx 𝔅 𝔄) `{!PctxNoUniq K}
    (lt lt': lty 𝔅) k Φ e :
  pctx_res E L K lt lt' k Φ → place_resolve.skipn k = e →
  typed_instr E L I +[p ◁ₗ pctx_plug K lt] e
    (const +[p ◁ₗ pctx_plug K lt'])
    (λ post '-[x], λ mask π, Φ (pctx_get K x.1) x.2 (pctx_vpath K) π → post -[x] mask π).
```

- **Purely ghost.** The program is `skipn k` (`k` steps, one batch of credits per step for
  the `ctask` of the judgement); no memory access, no new lifetime or borrow. The place stays,
  at the same value; its hole becomes readable but not mutable (`OfRes`, `ResUniqLty`, or
  unchanged), and `Φ` is learnt. The resolution is the generic one: `lty_res` (leaves by
  `resolve_keep`, any type by `resolve_keep_just`, `Copy` leaves by `resolve`; structural;
  unfolded unique borrows by `lty_res_uniq_leaf`/`_cpd`).
- **Contexts.** `PctxNoUniq K`: the hole is in the owned part of the place, below the root
  owned pointer (`K = POwn n K'`, `lty_res` at the hole, through `ltype_own_plug`), or it is the
  root of a place rooted at a value (`K = PHole`). Below a unique borrow, a shared reference or
  a resolved unique borrow there is nothing to resolve (resolved places have no
  interpretation in `Uniq` mode; the nested borrows are resolved from outside, by
  `lty_res_uniq_*` on the `UniqLty` above them).
- **Root.** New judgement `vroot_res E L lt lt' k Φ` (as `lty_res`, on `vroot_own`), with
  `vroot_res_uniq_leaf` and `vroot_res_uniq_cpd`: a unique borrow value `p ◁ₗ UniqLty lt κ`
  becomes `p ◁ₗ ResUniqLty lt κ`, its prophecy pre-resolved to the current value. For this,
  the proofs of `lty_res_uniq_leaf`/`_cpd` were factored through new lemmas on the `nval`s
  (`uniq_nval_res_leaf`, `uniq_nval_res_cpd`: the node minus its pointer cell), used by both.
- **Deleted:** `type_resolve_oplace_res_instr` (`place_res_rslv.v`; the instance
  `K = POwn n PHole`), `type_resolve_vplace_uniq_instr` (`place_resolve.v`; now the root
  instance `vroot_res_uniq_cpd`, which also needs `lty_vok lt` and `lty_sbl lt` alive instead
  of `lty_uniq_rslv lt` and the shared lifetimes alive, and covers a leaf referent too, then
  `tctx_incl_resolve_head` to forget the place) with its proof machinery (`ltype_owned_rslv`,
  `proph_idx_bor_gen_preresolve_rsv_acc`, `cpd_preresolve`, `lty_uniq_rslv`, `lty_shr_lfts`,
  `lty_nunblk`, `rslv_cost`, `lctx_lft_alive_list`), `type_resolve_oplace_instr`
  (`place_resolve.v`) and `type_resolve_oplace_deep_instr` (`place_puniq.v`): resolving and
  forgetting an owned place is the new rule followed by forgetting (their judgements
  `lty_resolve`/`lty_rslv` stay, for `resolve_tctx_cons_oplace(_deep)` and the drops).
  Examples ported: `place_res` (`res_pair`, `res_nested`: `K = POwn n PHole`, `cbn [pctx_res]`
  before the `lty_res` instances). New example `place_res_root` (`downgrade`:
  `fn downgrade<'a>(x: &'a mut (i32, i32)) -> &'a (i32, i32) { &*x }`, the root of `x` is
  resolved and its referent shared below the resolved borrow, `K = PResUniq α PHole`).
- **Kept (different operations).** `type_resolve_val_instr` (`value_ctx.v`): resolving a
  value `p ◁ᵥ ty` (not a place) and forgetting it, used throughout the examples for borrow
  values; `tctx_incl_resolve_head`/`_lower` (`type_context.v`): forgetting context elements
  (no resolution, no step); `tctx_drop_vplace_uniq`: giving up a root unique borrow with only
  blocked leaves without a program step (a `tctx_incl`); `resolve_tctx_cons_oplace(_deep)`:
  resolution of the context at a jump; the drops.
- **Deviations.** The judgement is per shape of `K` (`pctx_res`: `vroot_res` at the root,
  `lty_res` at a hole below an owned pointer), since `lty_res` is stated on memory nodes and a
  root has no pointer cell; the resolved place is kept (forget it to give it up).

## Place rules polish (branch `proto/place-polish`, 2026-11-01)

Follow-ups on the eight unified rules (statements above are updated).

- **Move without `∀ junk`.** `~~(uninitₛ n) = ()`, so `type_move_place_instr` and
  `type_memcpy_move_place_instr` give `pctx_reset (𝔅':=uninitₛ (ty_bsize ty)) K x.1 ()`.
- **One lifetime notion.** `pctx_alv K lt` (`pctx_acc.v`, the former `pctx_ralv`, with
  `pctx_slft`/`pctx_salv` moved there from `place_pshr.v`): the lifetime of the folded type at
  each unique borrow above the first shared reference or resolved unique borrow, and
  `pctx_salv K' κ` there; `static` for owned paths. Read, write, memcpy (both sides), share and
  borrow require `lctx_lft_alive E L (pctx_alv K lt)` (read and the copy source `⊓ κs`); for
  `PctxNoShr K`, `pctx_alv_noshr` gives the old `pctx_ulft` guard. (The fold/unfold, sum and
  unblock rules of `place_puniq.v`/`place_deep.v`/`place_pshr.v` still state `pctx_ulft`.)
- **Borrow lifetime as input.** `pctx_blft K : lft` (no `α`): below the first shared
  reference or resolved unique borrow, the lifetime of the view (`pctx_vlft`; the unique
  borrows above do not matter: `&**x : &'b T` for `x: &'a mut &'b T`); otherwise the
  intersection of the enclosing unique borrow lifetimes (`static` at the end).
  - Borrow: `&uniq{α} ty`, leaf `Blocked ty α`; side conditions `ty_outlives_E ty α`,
    `lctx_lft_incl E L α (pctx_blft K)`, and `lctx_lft_alive E L (pctx_alv K (OfTy ty) ⊓
    pctx_balv K α)` where `pctx_balv K α` is `α` for a reborrow of the whole referent of the
    innermost unique borrow (`pctx_uend K = Some _`: the token of the new prophecy variable
    is taken under `α`) and `static` otherwise (an Owned-mode borrow does not need `α` alive,
    as before consolidation).
  - Share: `&shr{α} ty`; `pctx_sleaf E L K α lt ty lt'`, `lctx_lft_incl E L α (pctx_blft K)`,
    `lctx_lft_alive E L (pctx_alv K lt)`. Leaf cases `lty_sleaf E L α b lt ty lt'`
    (inductive): `lty_sleaf_ofty` (owned part: becomes `ShrBlocked ty α`, needs the outlives
    condition and `α` alive), `lty_sleaf_view` (an unblocked leaf of a view, unchanged),
    `lty_sleaf_shrblk` (a shared-blocked leaf at `β` with `lctx_lft_incl E L α β`, unchanged,
    in the owned part or in a view). Below a shared reference: any leaf, at its folded type.
  - The intersections are gone: the blocked lifetime is `α` itself, so the unblock rules
    (`unblock_tctx_vplace_deep`, `_uniq`, `_shr_deep`, `unblock_tctx_oplace_res(_shr)` and
    their `oplace` corollaries) take `Blocked ty α`/`ShrBlocked ty α` and get `[†α]`
    directly. The inclusions in the enclosing borrow lifetimes needed by the closers
    (`pat_ok`) and by `uniq_body_reborrow` are persistent consequences of
    `lctx_lft_incl` (`pat_ok_blft`, `pctx_blft_incl`). Examples now return `&uniq{α}`
    instead of `&uniq{α ⊓ α}` (`get_first`, `get_some_first`); `res_nested` borrows at a
    local `γ ⊑ₗ [α; β]`.
- **Sharing completeness.** Re-sharing a `ShrBlocked ty β` leaf at `α ⊑ β`
  (`type_share_vplace_noshr_shrblk`, from its sharing, `shr_view_lft_mono`), and sharing
  `ShrBlocked` leaves in views (`wp_view_sacc` returns the shared view at
  `pctx_vslft K κ lt`, the view lifetime intersected with `β`; `pctx_vslft_incl`).
- **Credits.** The word-layer budgets are gone: `pctx_acc_cred K m d = m + 2d + 2` (was
  `(d+1)(m+d+2)`), `pctx_vacc_cred K D = 2D + 3` (was `(D+1)²`), `pshr_cred D = 3D² + 9D + 5`
  (was `7D² + 12D + 3`), the write access takes `£(3D + 5)` (was `(D+1)(D+2)+1`), and the
  unused `£w` credits for word loads of pointers (`3(D+1)` per pointer) were removed from the
  borrow, sum and `wp_pshr_open` proofs.
- **`pctx_res` usability.** The hang came from unification unfolding `lty_res` (a big
  definition) when the step counts did not match syntactically (`?k1 + ?k2` vs `2` after
  `apply lty_res_prod`), and from inferring `k` from the program (`skipn ?k` vs `Skip;; …`).
  Now `lty_res` and `vroot_res` are records (`LtyRes`, `VrootRes`), `pctx_res` is an inductive
  (`pctx_res_root`, `pctx_res_own`), and the rule takes any instruction `e` with the premise
  `skipn k = e` (after the `pctx_res` premise, so `k` comes from the derivation; then `done`).
  Examples: `eapply (type_resolve_place_instr _ _ _ vx K lt); [apply pctx_res_own; apply
  lty_res_prod; …|done]`; no `cbn [pctx_res]`.
- **Tests** (`examples/place_rules.v`, instruction-level, fast): reading an `OfRes` leaf,
  reading through a shared reference in the view of a resolved borrow, sharing in a view below
  an owned pointer, re-sharing a `ShrBlocked` leaf (owned, below a unique borrow, in a view),
  resolving a compound root (`vroot_res_uniq_cpd`).

