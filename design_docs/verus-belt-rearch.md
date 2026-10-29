It sounds like we need to go the lazy route, but there's a big problem. VerusBelt completely rearchitected the way shared borrows work. Instead of RustBelt's `own` and `shr` predicates, VerusBelt uses a single `ty_gho` predicate, with shared borrows defined uniformly via the "guard" operator: `@[k] &&{E}&&> ty_gho`. There's also a law for how guard interacts with full borrows that lets you guard the contents of a full borrow (`llftl_idx_bor_guard`). The problem is if mutable borrows are lazy, we have `&{κ} |==> P` and then we can only guard `|==> P` which is no good. We need to make a big detour to fix this architectural problem before we can make mutable borrows lazy.

We need to synthesize the RustBelt `shr`/`own` approach a bit with VerusBelt. Instead of just `gho` we should have `gho_own` and `gho_shr`, and shared borrows being defined as a guard of `gho_shr`.
Every type needs a law that a mutable borrow can be turned into a shared borrow
(to be included in the definition of `type` in `type.v`):

```
ty_shr_bor_begin: (&{κ} ty.(ty_gho)) |={E}=∗ (@[κ] &&{E}&&> ty.(ty_gho_shr))
```

By reintroducing this dichotomy between `own` and `shr`, we can have mutable be lazy when uniquely owned, and non-lazy when shared. (This should be fine because we can't take a mutable borrow from a place that's behind a shared reference anyway, so we never have to deal with a blocked place behind a shared reference.)

Specifically, we can have:
 * `gho_own` for mutable borrow `&uniq{κ} ty` can be lazy: `&{κ} |==> (ty.(gho_own) ... ∗ ...)`
 * `gho_shr` for mutable borrow `&uniq{κ} ty` can be non-lazy: just `ty.(gho_shr) ...`
(Probably with some laters and other details...)

If we have ownership of the mutable borrow `&{κ} (|==> P)` and need to turn it into a shared borrow, this is OK,  we can discharge the `|==>` and freeze and get a guard on `P`. 
Thus we can go from `&{κ} |==> (ty.(gho_own) ... ∗ ...)` to `(@[κ] &&{E}&&> (ty.(gho_shr) ...))`.

If we have `&{κ} (|==> &{κ} (|==> P))` we discharge the first `|==>`, unnest, and then recursively apply the law.

(Fixing storage protocols will be a little tricky. To deposit a `P`, we will probably need to borrow it first, then deposit it along with its lifetime token; then end the borrow after withdraw.)

Please flesh out the plan for this rearchitecture (all the changes we need to make for the definition of `type` and how that impacts all the downstream type definitions).

---

# Fleshed-out plan

## 1. Two corrections to the sketch above

### 1a. `gho_shr` must be indexed by the sharing lifetime: `ty_shr κ x d g tid`

Sharing `&κ &uniq{κ'} T` only gives access to the referent at `κ ⊓ κ'`. The proof of the
share law also only produces a borrow at `κ ⊓ κ'` (it unnests with
`llftl_idx_bor_unnest : &{κ',i}P -∗ &{κ}(idx_bor_tok i) ={E}=∗ &{κ ⊓ κ'} P`).

An unindexed `gho_shr(&uniq{κ'} ty)` would have to be `@[κ'] &&> (…)`, and that is unsound:
- guards are persistent, so anyone holding `@[κ] &&> gho_shr` can open it while κ is alive;
- that yields a persistent guard at `κ'`;
- that guard outlives the sharing, but after κ ends the `&uniq` is mutable again.

Hiding `κ0 = κ ⊓ κ'` existentially doesn't help either, because then `κ ⊑ κ0` can no longer be shown.

So, as in RustBelt:
- `ty_gho_own` is ownership (renamed from `ty_gho`) and may be lazy;
- `ty_shr κ x d g tid` is persistent, monotone in κ, and takes no location (`gho` is location-free);
- the default for types with no borrow inside is `ty_shr κ x := @[κ] &&{↑NllftG}&&> ty_gho_own x`,
  which keeps the guard style wherever it already works.

### 1b. The lazy update must be a fancy update, so the share law takes a guard for κ

Laziness exists so that the lender can turn blocked contents back into the core by firing
inheritances. Those are `[†κ] ={↑Nllft}=∗ …`, which a basic update `|==>` cannot run. So the lazy
update has to be `|={Mlazy}=>` with `Mlazy := ↑Nllft ∪ ↑prophN ∪ ↑uniqN`.

A fancy update cannot run under `llftl_bor_acc_atomic`, whose mask is `∅`. The share law must
therefore open borrows non-atomically, using a guard for κ. This costs nothing in practice:
- sharing only happens while κ is alive;
- the recursive call at `κ ⊓ κ'` is covered too: since `κ ⊑ ty_lft`, the guard for κ also guards
  `κ ⊓ κ'`.

Also note: `↑NllftG ⊆ ↑Nllft`, so a lazy update can never run while a guard is open (`leaf_open`).

## 2. Changes to `type` (`typing/type.v`)

- **`ty_gho`** is renamed to `ty_gho_own`.
- **New `ty_shr κ x d g tid`**, with laws `ty_shr_persistent`, `ty_shr_lft_mono`
  (`κ' ⊑ κ -∗ shr κ … -∗ shr κ' …`) and depth monotonicity.
- **New `ty_share`:**
  `llft_ctx -∗ κ ⊑ ty_lft ty -∗ (G &&{↑NllftG}&&> @[κ]) -∗ G -∗ £(share_cost d g) -∗ &{κ}(ty_gho_own x d g tid) ={E}=∗ G ∗ ty_shr κ x d g tid`,
  with `Mlazy ⊆ E`. The credits come from time receipts, as in `resolve_uniq_body`.
- **`ty_gho_pers`:** keep `gho_own ⊢ gho_pers`, and add `ty_shr κ … ⊢ ▷^? gho_pers`.
- **`ty_guard_proph`:** restate it on `ty_shr`:
  `ξ ∈ ξl x → ty_shr κ x d g tid -∗ ▷^…((R &&{…;n}&&> @[κ]) -∗ R &&{…}&&> 1:[ξ])`.
- **`Copy`:** add `ty_shr κ x … -∗ (@[κ] &&> ty_gho_own x …)`, or require the default `shr`.
- **`Sync`:** tid-independence of `ty_shr` rather than `ty_gho`.
- **`Send`:** stays on `gho_own`. `send_change_tid` already runs at a mask containing `↑Nllft`.
- **`type_incl` / `subtype`:** add `□ ∀κ x d g tid, ty_shr κ x … -∗ ty'.shr κ (f x) …`.
- **`TypeNonExpansive` / `TypeContractive`:** add `shr` clauses. The `fixpoint.v` chain must keep
  `ty_share`, just as it keeps `ty_guard_proph` today.
- **`simple_type` / `plain_type` / `ghost_type`:** default `shr`, with a generic `ty_share`.

One generic lifetime-logic lemma covers every default instance:
`&{κ}P ={E}=∗ @[κ] &&{↑NllftG;1}&&> ▷P`. It goes through `llftl_bor_idx`, then
`llftl_borrow_shared` on the index token, then `llftl_idx_bor_guard'`.

## 3. Downstream type definitions

- **A. Default instance** (`shr κ := @[κ] &&> gho_own`, `ty_share` from the generic lemma):
  `int`, `bool`, `uninit`, `base_type`, `ghost`, plain `pptr`, the base `pcell`, `spawn`,
  `function`, `ra`, `atomic_inv`, `local_inv`. The invariant types store the inner `gho_own`
  inside an invariant, which is fine: opening the invariant yields owned contents.
- **B. Structural** (`shr` built from the inner `shr`; `ty_share` splits the borrow and recurses):
  - `own_ptr`/`box`: `(@[κ]&&>pointsto) ∗ (@[κ]&&>freeable) ∗ ▷ ty.shr κ`;
  - `prod`/`xprod`: `shr₁ ∗ shr₂`;
  - `sum`: by the fixed variant;
  - `tracked`, `mod_ty`, `fixpoint`: pass-through;
  - the typed points-to of `pcell`, and `pptr`'s `P ∗ ty.gho`.
- **C. `shr_bor`:** `gho_own` is today's `st_gho` with `ty.gho` replaced by `ty.shr κ'`. It is
  persistent, so `shr κ` is the same predicate.
- **D. `uniq_bor`:**
  - `gho_own` becomes lazy: `uniq_payload := |={Mlazy}=> (⧖ ∗ ty.gho_own … ∗ l #↦!∗ phys)`.
  - Later, rebase the body on the pinned, state-indexed body from `ltype.v` (with `OfTy` as the
    trivial pattern). This closes the Phase-2 gap of not being able to unfold behind an existing
    `&uniq`.
  - `shr κ x := (@[κ⊓κ'] &&> pointsto) ∗ ty.shr (κ⊓κ') x0 ∗ (guard for ξ's token)`. The token
    guard is needed because `ξ ∈ ξl x`.
  - `ty_share` proof:
    1. open the outer borrow with the κ guard;
    2. unnest to `&{κ⊓κ'}(∃x'. PC ∗ |={Mlazy}=> payload x')`;
    3. open that with the `κ⊓κ'` guard, fix `x'` by VO agreement, and run the lazy update;
    4. close it non-lazily (the closing obligation is trivial);
    5. split off `PC` and recurse on `ty.gho_own` at `κ⊓κ'`.
- **E. Storage protocols** (`protocol.v`, `proph_protocol.v`):
  - deposit: create `&{κs}(gho_own)` and store it together with `@[κs]`;
  - shared access: `ty_share` on the stored borrow, then guard `ty.shr κs`;
  - withdraw: end κs (`llftl_end'`) and take the inheritance.

  This needs its own design pass before coding.
- **`ltype.v`:** update the leaves and rename `ty_gho` to `ty_gho_own`.

## 4. Typing-rule consumers

- **`borrow.v`:**
  - `type_share(_instr)`: use `ty_share`. Prophecy resolution still uses `proph_ibor_resolve`,
    but `Deps` now comes from `ty_guard_proph` on `shr`.
  - The deref-shr rules: unfold `own.shr` / `uniq.shr`.
  - The `&uniq` reborrow and deref rules: run the lazy update after opening.
- **`proph_bor.v`:** `proph_ibor_resolve` (and its reserved variant) takes a sharing law for the
  payload and derives `Deps` from it.
- **`uniq_util.v`:**
  - `resolve_uniq_body`: freeze, then `ty_share`, then `ty_guard_proph`;
  - `alloc`/`reborrow`: wrap the payload in the update.
- **`product_split.v`:** the shr split uses `prod.shr`; the uniq split threads the update through.
- **Elsewhere** (`type_sum.v`, `pptr.v`, `pcell.v`, `programs_util_*.v`, `type_context.v`,
  `soundness.v`): mostly the rename, plus `ty_shr` where a proof reads through a shared reference.

## 5. Migration order (commit after each step once the full build is clean)

1. Lifetime-logic lemmas: the generic `&{κ}P ⇒ guard` lemma, and a guarded open/run-update/close
   helper.
2. Add `ty_shr` and `ty_share` to `type` with every type using the default instance (sound for all
   types, since nothing is lazy yet). Rename `ty_gho` → `ty_gho_own`.
3. Switch the consumers to `ty_shr`: `shr_bor`, `ty_guard_proph`, `Copy`/`Sync`, `type_incl`,
   contractiveness, `fixpoint`, and the deref and share rules.
4. Give the structural types (§3B) and `shr_bor` (§3C) a structural `shr` with a recursive
   `ty_share`.
5. `&uniq`: a structural `shr` at `κ⊓κ'` with its `ty_share`, then make the payload lazy, and fix
   up its consumers.
6. Storage protocols: deposit via borrow plus token.
7. `ltype.v`: rebase `&uniq`'s body on the pinned body and support unfolding under Uniq; then
   Phase 3 (typing rules with reservations).
