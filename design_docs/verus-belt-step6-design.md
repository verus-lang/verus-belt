# Step 6 design: storage protocols after the own/shr split

Context: `design_docs/verus-belt-rearch.md` (plan §3E) and `design_docs/verus-belt-place-types-summary.md`.
State: HEAD `3dad48f` (lazy `&uniq` payload).

## 1. Where the problem actually is

- **The protocol itself is fine.** It is parametric over a ghost type `tyC`, and it stores
  `tyC.gt_gho c` (`storage_resource_ty`, `typed_sp_*` in `typing/protocol.v`; the algebra is in
  `proph_protocol.v`). For ghost types, sharing is the default guard of `gt_gho`, which the
  protocol's guard rules (`typed_sp_guard`, `…_with_shr`) produce directly. None of these rules
  needs to change.
- **The only bridge from real types into protocols is `storable_ty ty`.** It is a ghost type with
  `gt_gho (x0,(d,g)) := ty.gho_own x0 d g ∗ ⧖(S d ⊔ g)`, used only in `protocol.v`:
  - `storable_new`: `own (tracked ty) → own (storable ty)`;
  - `storable_into_inner`: the reverse;
  - `storable_borrow`: `&shr κ (storable ty) → &shr κ (tracked ty)`;
  - the `Send`/`Sync`/`Copy` instances.
- **Only `storable_borrow` is unsound in general** (it is currently TEMPORARY, restricted to
  `ty_shr_is_default`). `&shr κ (storable ty)` only provides `@[κ] &&> ty.gho_own …`. Turning that
  into `ty.shr κ` is false once `gho_own` is lazy (`&uniq` inside `ty`).

## 2. Options rejected

1. **Store a borrow and run `ty_share` when accessing shared.** `ty_share` consumes the borrow, and
   a guard only gives temporary access to it, so the borrow cannot be shared from under the
   protocol's guard.
2. **Make `storable_ty` a full type with a structural `shr`.** This does not help.
   `typed_sp_guard` produces a shared reference to a stored value from a guard of the stored
   `gt_gho`, so the conversion from guard to `ty.shr` is still needed somewhere.
3. **Keep the restriction to default-shr types.** That excludes storing anything that contains
   `&uniq`.

## 3. Chosen design: share up front, when a value becomes storable

The doc's idea of borrowing before deposit, refined: also run `ty_share` once, eagerly, and store
the persistent result.

**Value.** Add the sharing lifetime to the value, so that a guarded existential can be pinned:
- `~~(storableₛ 𝔄) := ~~𝔄 * (nat * nat) * lft`, where `lft = gset nat`, countable;
- update the `storableₛ` cases in `syn_type.v` (5 arms): `vπ` is the identity, and phys, `ξl` and
  the size are unchanged.

**Ghost predicate.** For `x = (x0, (d, g), α)` and `κs := α ⊓ ty_lft ty`:

```
gt_gho x tid :=
    @[α]                                              (* keeps the sharing period alive *)
  ∗ ty.(ty_shr) κs x0 d g tid                         (* persistent, computed once      *)
  ∗ ([†α] ={↑Nllft}=∗ ▷ ty.(ty_gho_own) x0 d g tid)   (* the borrow's inheritance       *)
  ∗ ⧖(S d `max` g) ∗ ty.(ty_gho_pers) x0 d g tid
```

`[†α] ⊢ [†κs]` holds by `[† κ ⊓ κ'] ⊣⊢ [†κ] ∨ [†κ']`, so the inheritance from `llftl_borrow` at
`κs` can be restated with `[†α]`.

**Rules:**

- **`storable_new`** (adds a premise `lctx_lft_alive E L (ty_lft ty)`):
  1. Begin a fresh `α` with `llftl_begin`.
  2. Create `&{κs}(ty.gho_own x0 d g)` and its inheritance with `llftl_borrow`.
  3. Run `ty_share` with the guard `G := @[α] ∗ (guard of L)`, combined for `α ⊓ ty_lft` via
     `guards_llft_glb`. Its premise `κs ⊑ ty_lft` holds by `llftl_intersect_incl_r`.
  4. Discharge the resulting `|={E}▷=>^d` with `d` credits from the instruction's time receipts,
     as `resolve_uniq_body` does. This needs a `typed_instr_of_skip` variant that provides `£`, as
     `storable_borrow` already uses.
  5. Return `@[α]` and the L tokens.
- **`storable_into_inner`:**
  1. End `α`. The ender from `llftl_begin` takes one step: `={↑Nllft}[∅]▷=∗ [†α]`.
  2. Fire the inheritance to get `▷ ty.gho_own`, and strip the later with the instruction's second
     step or a credit.

  Already-forced lazy contents need no update. Contents are lazy only inside nested `&uniq`, which
  `gho_own` carries as is.
- **`storable_borrow`** (adds a premise `lctx_lft_incl E L κ (ty_lft ty)`, or the corresponding
  `elctx_sat (ty_outlives_E ty κ)`, because `storable_ty` has `lfts = []`):
  1. From `@[κ] &&> gt_gho x`, guard transitivity gives `@[κ] &&> @[α]`, i.e. `κ ⊑ α`.
  2. Open the guard once (κ is alive via L) to extract the persistent `ty.shr κs x0 d g`. Strip
     the guard's later with credits (the rule already has `£`).
  3. `κ ⊑ α ⊓ ty_lft` by `llftl_incl_glb`, so `ty_shr_lft_mono` gives `ty.shr κ`, which is
     `(tracked ty).shr κ`.
  4. Build `&shr κ (tracked ty)`. The TEMPORARY hypothesis goes away.

  Because `α` is part of the value, the existential problem does not arise.
- **Instances:**
  - `Sync (storable ty)` follows from `Sync ty`, which includes tid-independence of `ty_shr` and of
    `gho_own` (the latter inside the inheritance).
  - `Send` is unchanged (`Send ty → Sync ty →`). Tokens and inheritances are tid-independent
    modulo `Sync`.
  - **`Copy (storable ty)` is dropped.** `gt_gho` now holds the token `@[α]`, so it is not
    persistent. The instance has no users.

## 4. What does not change

- the `typed_sp_*` rules, `storage_resource_ty`, `proph_protocol.v` and `ra.v`;
- prophecies: `ξl` of `storableₛ` is `[]` and `vπ` is the identity, so stored values are
  prophecy-independent; `ty_shr_guard_proph` is trivial for `storable_ty`.

## 5. Costs and risks

- **Changing the value of `storableₛ`** touches `syn_type.v` and every destructuring of storable
  values (only in `protocol.v`). It is mechanical.
- **`storable_new` now needs `ty_lft ty` alive**, and `d` credits or steps. Credits are available
  from time receipts.
- **A leaked storable value** (never turned back into the inner type) leaks the token of its
  lifetime `α`. This is harmless: the value is simply never returned.
- **`gt_gho` grows** by an `@[α]` and a persistent `ty_shr`. The protocol's deposit, withdraw and
  exchange rules move the whole `gt_gho` around and are agnostic to it.

## 6. Implementation steps (one commit)

1. Change the value of `storableₛ` in `syn_type.v` and fix fallout.
2. Redefine `storable_ty` and update `Send`/`Sync`; delete `Copy`.
3. Reprove `storable_new`, `storable_into_inner` and `storable_borrow`, with the new premises.
4. Remove the TEMPORARY comments. Full build, then commit.

## 7. Revision after the first implementation attempt (approved: option (c))

**What failed.** `κ ⊑ α` is a guard with zero laters. A guard that reaches the stored `@[α]`
through the protocol has `n ≥ 1` laters, because stored items sit under `▷` and `typed_sp_guard`
adds one. A guard with laters does not imply the zero-later guard, even for a timeless token, so
`ty_shr_lft_mono` cannot be applied.

**Fix: let inclusion monotonicity accept laters.** Generalize the field to

    ty_shr_lft_mono : (@[κ'] &&{↑NllftG; n}&&> @[κ]) -∗ ty_shr κ x d g tid -∗ ty_shr κ' x d (g+n) tid

The old law is the case `n = 0`. The extra laters are absorbed into the depth index `g`.

How each type proves it:
- **default shr:** by guard composition;
- **structural types:** by recursion;
- **`&uniq`:** re-index its token guard `&&{;1}&&> 1:[ξ]` to `&&{;g+1}&&>`.

**Effect on `storable_borrow`.** It proceeds as in §3 with three changes:
- use `κ ⊑ₙ α ⊓ ty_lft`, built from the guard with `n` laters and the static `κ ⊑ ty_lft`;
- produce `ty.shr κ` at depth `g + n`;
- strip the guard's laters with credits when extracting the persistent `ty.shr`.
