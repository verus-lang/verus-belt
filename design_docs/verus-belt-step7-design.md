# Step 7 prerequisites: summaries of the final value when a `&uniq` reborrow ends

Context: `design_docs/verus-belt-place-types-summary.md`, `design_docs/verus-belt-rearch.md`.
State at the start: HEAD `2bdc9e1`.

## Problem

When a reborrow of a `&uniq` ends, the restored outer `&uniq` needs two persistent facts about
its final contents `x'`:
- the receipt `⧖(S d' ⊔ g')`, for the depth constraint in `&uniq`'s own;
- `[†κ] ∨ ▷ ty_gho_pers x'`.

`proph_ibor_reborrow` (summary `R`) and `proph_ibor_unnest` (summary `S`) read these facts inside
a closing view shift of the lifetime logic, whose mask is `↑NllftUsr ∪ ↑NllftUsr2`. They are used
by `uniq_body_reborrow` and by the `&uniq &uniq` deref in `borrow.v`. This works today only
because `uniq_payload` keeps `⧖` and `pers` outside the lazy update.

Once `&uniq`'s body becomes the pinned, state-indexed body, a blocked state has those facts only
behind the blocked sub-places' inheritances. Firing those needs `↑Nllft`, which the closing view
shift does not have.

The problem also nests: `&uniq`'s `pers` contains the referent's `pers`.

## Plan

### 1. Simplify `&uniq` (option (b))

- Drop the referent's `ty_gho_pers` from `&uniq`'s own and its `ty_gho_pers`; at present it
  appears as `basically_dead κ ∨ ▷ ty_gho_pers x0` in own, and in the pers component.
- `ty_shr_guard_proph` then has to get the inner pers through `&uniq`'s shr. That needs
  `ty_shr ⊢ ▷^? pers` per type, or an equivalent. To keep the later budget sufficient at `g' = 0`,
  either bump the budget (e.g. `d*(g+2)`) or require `g' ≥ 1` for `&uniq`.
- With this, the summary `R`/`S` reduces to `⧖` only.

### 2. Sanity check (prototype, not merged unless it works out)

Restate `uniq_body_reborrow` so that its inheritance no longer returns the summary. Then:
- make `&uniq`'s depth constraint tolerate a dead `κ`:
  `basically_dead κ ∨ ⌜S d' ≤ d ∧ g' ≤ g⌝ (∗ the receipt)`;
- recover `⧖` at unblock time by opening the restored borrow with a guard for `κ`, running the
  lazy update and reading the receipt;
- push this through the rules in `borrow.v` that use it.

The aim is to find out whether settling at unblock time and the dead-`κ` disjunct work in
practice.

### 3. Main fix (only if step 2 succeeds)

- Drop the summaries from `proph_ibor_reborrow` and `proph_ibor_unnest`.
- Add a per-type pending ownership `pending_own` (equal to `ty_gho_own` unless the type contains
  `&uniq`) and a law
  `ty_settle : (G guards @[ty_lft ty]) -∗ G -∗ pending_own x' ={E}=∗ |={E}▷=>^d |={E}=> G ∗ ∃d, ⧖d ∗ ty_own x' d d`.
- Blocked type-context entries and `Blocked` in `ltype.v` hand out pending ownership. The
  unblocking rule pays for settling it.

### 4. Then the step-7 rebase

Rebase `&uniq`'s body onto the pinned, state-indexed body, and support unfolding under Uniq.

## Outcome of step 2 and revised step 3

**The prototype** (branch `proto/settle-at-unblock`, commit `ca9024e`):
- Settling at unblock time works for reborrow, UniqBor, share and unblock.
- No dead-κ disjunct is needed.
- The `&uniq &uniq` deref fails: in the closing view shift of `proph_ibor_unnest` there is no
  guard for κ'.

**Revised step 3: a guarded lazy payload.** This replaces the per-type `ty_settle`:

    uniq_payload ty := ∀ G, ⌜Timeless G⌝ -∗ (G &&{↑NllftG}&&> @[ty_lft ty]) -∗ G ={lazyE}=∗ G ∗ (⧖ ∗ ty_gho_own … ∗ pt)

Every consumer has such a guard:
- an opener has a guard for κ, and κ ⊑ `ty_lft ty`;
- a lender gets one at unblock.

The closing view shift of the unnest can therefore produce this form. Opening and settling the
inner borrow at κ' then happens inside the guarded update.
