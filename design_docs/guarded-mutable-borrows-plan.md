# Guarded mutable borrows, and a decodability layer built on them (plan)

Status: plan (2026-11-01). It follows the user's proposal
`proposed-abstraction-guarded-mutable-borrows.md` and route C of §20 of
`pcell-multibyte-cells.md`: keep Rust's semantics, where a typed move re-encodes the
contents of a cell. Goal: `PCell::borrow`/`borrow_mut` return `&shr{κ} ty`/`&uniq{κ} ty`,
which hold the exact abstract bytes of the contents while the borrow is live.

## 1. The abstraction

Fix a family `c(s, t)` (`t`: the logical contents; `s`: the *placement*, see below). An
instance `γ` provides three propositions:
- `a γ s` — the *move right* (owned by the `pcell` value);
- `b γ t` — the *permission* (owned by `cell_points_to`);
- `c(s, t)` — the *contents*, which hold the exact resources (bytes).

Laws (all up to `▷`/credits and masks; masks of the lazy back-maps of borrows,
`↑NllftUsr`, must reach the instance's state, cf. O4 of §20):

- **(L0) Create/destroy.** `c(s,t) ={E}=∗ ∃ γ, a γ s ∗ b γ t`, and
  `a γ s ∗ b γ t ={E}=∗ c(s,t)`.
- **(L1) Exchange (move).** `a γ s ={E}=∗ ∃ t, c(s,t) ∗ (∀ s', c(s',t) ={E}=∗ a γ s')`.
  The mover does not learn `t` from `b`. It must give back contents at the *same* `t`,
  but it may change the placement and the exact resources. For a re-encoding move that
  means bytes that decode to the same value.
- **(L2) Shared.** `G &&{E}&&> a γ s` and `G &&{E}&&> b γ t` give `G &&{E}&&> c(s,t)`.
- **(L3) Mutable.** `@[κ] &&{E}&&> a γ s` and `&{κ} (∃ t, b γ t)` give
  `&{κ} (∃ t, c(s,t))`.
- **(L3p) Prophetic mutable.** The same law for the prophetic borrows of the `&uniq`
  bodies (`proph_bor`/`uniq_body`, `cpd_body`). It maps the prophecy of `t` to the
  prophecy of the contents.
- **(L4) Restoration.** After `κ` ends, each side gets its part back on its own:
  - the lender of `&{κ}(∃t, b γ t)` gets `b γ t'` for the final `t'`;
  - the owner of `a γ s` can use (L1) again without the lender's cooperation.

  This is what Rust needs: after `borrow_mut`'s lifetime ends, the owner may move the
  cell even if the permission is never touched again.

The proposal stated (L1) as an equivalence `a ⊣⊢ ∃t, c(t)`. It cannot literally be one:
- a guard of `a` would then be a guard of `∃t, c(t)`, which allows reading the contents
  without the permission;
- (L3) takes `c` out of `a` for the duration of `κ`.

So (L1) is an update that only the *owner* of `a` can perform, and while a lend is
outstanding `a` is never owned. The owner gets `a` back only after the lifetime of its
own sharing has ended.

The placement `s` is a generalisation of the proposal; see §3 for why it is needed.

## 2. Model (user proposal `gmb_model_proposal.md`, as refined 2026-11-02)

### 2.1 Lifetime-logic extension: special openings

```
Lemma llftl_bor_acc_special E P κ :
  ↑Nllft ⊆ E →
  llft_ctx -∗ &{κ} P -∗ @[κ] ={E}=∗ ▷ P ∗ special_open κ ∗
    (∀ Q, ▷ (▷ Q ∗ [†κ] ={↑NllftUsr ∪ ↑NllftUsr2}=∗ ▷ P ∗ special_open κ) ∗ ▷ Q
          ={↑Nllft}=∗ &{κ} Q ∗ @[κ]).
special_open κ &&{↑NllftG ∪ ↑NllftO}&&> @[κ]      (persistent law)
```

- **Back-maps already run eagerly** at lifetime end (step 2 of `llftl_end`,
  `outer_kill_lt_step2` in `lifetime_internals/expire_lt.v`). So `special_open κ` comes back
  to the model through the back-map before the end completes.
- **The dead token in the back-map is fine.** `[†κ]` is created in step 1, before the
  tokens are collected. The two invariants of the model may be out of sync during the end,
  and the `NllftO` invariant (`lifetime_full.v:86`) is open during step 2: back-maps run
  with `↑Nbox ∪ ↑NllftUsr ∪ ↑NllftUsr2`, which excludes `↑NllftO`.
- **The certificate.** Put ghost state into the `NllftO` invariant certifying that the
  registry of `special_open` tokens is in sync with the alive/dead registry. The guard law
  is then stated with mask `↑NllftG ∪ ↑NllftO`.
  - So a back-map holding `[†κ]` cannot use it to reach `@[κ]`, and no contradiction can be
    derived inside it.
  - Outside the end procedure, the guard is available.
- **The registry** is keyed so that ending an atomic lifetime collects the tokens of every
  intersection containing it.
- **Variants needed:**
  - a guarded version, taking `G &&{↑NllftG}&&> @[κ]` like `llftl_bor_acc_guarded`;
  - an indexed-borrow version;
  - a version for prophetic borrows (`proph_bor`, the `&uniq` bodies), for L3p.
- **Reopening.** A borrow that is later reopened, reborrowed, split, joined or unnested
  keeps its back-map chain. Check that step 2 runs the composed chain.

### 2.2 GMB ghost state and invariants

- **Ghost state.** Two copies of an authoritative state, `Auth`/`Auth2(opt_s, opt_t)`,
  with `opt_s : option S` and `opt_t : In t | Out κ`. Fragments:
  - `a(s)`: `opt_s = Some s`; exclusive.
  - `a_out(t)`: `opt_s = None`, `opt_t = In t`.
  - `b(t)`: `opt_t = In t`; exclusive.
  - `b_out(s, κ)`: `opt_s = Some s`, `opt_t = Out κ`.

  `a` and `b` live in disjoint ghost names, so their guards combine (`guards_and_point`).
- **`guard_inv`** := `True &&{↑NllftUsr2}&&> ∃ opt_s opt_t, Auth(opt_s, opt_t) ∗ …`, with
  one case per state:

  | State | Holds |
  |---|---|
  | `(Some s, In t)` | `c(s, t)` |
  | `(Some s, Out κ)` | `True` (contents lent) |
  | `(None, In t)` | `True` (contents with the mover) |
  | `(None, Out κ)` | `False` |
  | destroyed | `True` (terminal state, for L0) |

- **`other_inv`** := `inv NllftUsr (∃ opt_s opt_t, Auth2(opt_s, opt_t) ∗ …)`. In state
  `Out κ` (with `opt_s = Some s`) it holds the token `special_open κ` and the guard
  `special_open κ &&{↑NllftG ∪ ↑NllftO}&&> a(s)`; otherwise `True`.

### 2.3 Laws

- **(L1) forward.**
  - In state `Out κ`: take the token and the guard from `other_inv`, and combine them with
    the owned, exclusive `a(s)` (`guards_and_pers_with_excl`, `T := a(s)`). This gives
    `False`. It needs mask `↑NllftG ∪ ↑NllftO` and a step or credit for the guard's later.
  - In state `In t`: move to `(None, In t)` and take `c(s, t)`.
- **(L1) back.** From `(None, In t)` to `(Some s', In t)`, depositing `c(s', t)`.
- **(L2).**
  - Combine the guards of `a(s)` and `b(t)`.
  - `guards_strengthen_exists` against `guard_inv` gives the persistent fact that the
    state is `(Some s, In t)`.
  - `guards_weaken` projects out `c(s, t)`. This works although `c` is not a point prop.
- **(L3).** Inputs: `@[κ] &&> a(s)` and `&{κ}(∃ t, b(t))`.
  1. Open the borrow with the special accessor.
  2. Move `b(t)` to `b_out(s, κ)`, and the state to `(Some s, Out κ)`.
  3. Take `c(s, t)` out of `guard_inv`.
  4. Store the token and the guard `special_open κ &&> @[κ] &&> a(s)` in `other_inv`. The
     second guard comes from the owner's share at `α` and `κ ⊑ α`.
  5. Close with `Q := ∃ t', c(s, t')` and the back-map `c(s, t') ⇛ b(t') ∗ special_open κ`.
     The back-map moves the state to `(Some s, In t')`, deposits `c`, and returns the token
     from `other_inv`.

  `s` cannot change during the lend, because `a(s)` is only guarded.
- **(L4)** is automatic. When `κ` ends, step 2 runs the back-map, so the state is back to
  `In` before anyone can own `a(s)` again.
- **(L0).** Allocate the ghost state and both invariants; destroy into the terminal state.
- **No typing-rule changes:** `pcell_ty` owns plain `a(s)`, and the share and unblock rules
  are untouched.

## 3. Instantiation: the decodability layer

- **Contents.** Take `t = fv` (the fancy value of the contents) and `s = l` (the location
  of the cell):
  `c_g(l, fv) := ∃ fbs, l ↦b[^fbs] ∗ ⌜frepr m_g fbs fv⌝`. These are exact fancy bytes
  at `l`: ordinary bytes, with the positions of nested cells owned through their own
  move rights `a γ' (l + o)`.
- **Decodability (D3)** is no longer a global heap invariant. It is a property of `c`,
  held by whoever has the contents:
  - the instance, when idle;
  - the mover, during (L1);
  - the borrow, during (L3).
- **The three types:**
  - `pcell_ty m` at `l` owns `a γ_g l`;
  - `cell_points_to ty` owns `b γ_g (ty_fval x)`;
  - a borrow of the contents is a borrow of `c_g(l, ty_fval x)`, which is exactly the body
    of `&shr{κ} ty`/`&uniq{κ} ty` at `l` (`bytes_own ty l x`, with
    `ty_mty ty = m_g`).
- **Why the placement is the location.**
  - If `c` were over the group's contents only (`g ↦ bytes`, as in the proposal), an
    access at `l` would still need the location side, which is the pin of O3. That means
    threading it through about 300 uses in the borrow bodies and the place files.
  - With `c` at the location, the contents *are* ordinary memory at `l`. O3 disappears,
    and the borrow bodies are the existing ones.
  - The mover changes the placement (L1 with `s' = l'`). This is the same in-transit
    pattern as today's `unt_fbytes`: the closer `∀ l', c_g(l', fv) ={E}=∗ a γ_g l'`
    travels with the moved value.
- **How the §20 obstacles are resolved:**
  - **O1:** the body is typed by `ty`, whose layout splits along `ty_mty ty = m_g`. Each
    field write is checked at its own type, and decodability at `m_g` follows by
    compositionality of `frepr` (it is already a consequence of `ty_fbytes`). No per-byte
    roles are needed.
  - **O2:** no tethering ids. While `c` is held the bytes are exact, and a move cannot
    happen during `κ`, since `a` is only guarded.
  - **O3:** gone, as above.
  - **O4:** the back-maps reach the instance invariant, which lives in `↑NllftUsr`.
- **Consequence for the heap.** The physical heap no longer needs cell machinery: the
  byte chains, `fcmap`, `gdyn`, the write and read banks, D3, `gnest` and the
  sub-position WP rules all become unnecessary. Cells become purely logical, in the way
  Verus's `PCell` is. The plan deletes them in phase 5, once everything has been ported.
  `FValue`/`FVCell` stay, for fancy values in `val_own`/`ty_fval`.

## 4. Phases (each a merge, with a clean full build)

0. **Lifetime-logic extension (§2.1).**
   - Special openings: plain, guarded and indexed, with the guard law
     `special_open κ &&{↑NllftG ∪ ↑NllftO}&&> @[κ]`.
   - A registry of special tokens, kept in sync with the alive/dead registry, with its
     certificate in the `NllftO` invariant.
   - Collection of the tokens in step 2 of `llftl_end`, including intersections and
     composed back-map chains.
   - Tests: open specially, close, end the lifetime; reopen the borrow normally and
     reborrow it, then end.
1. **GMB library (non-prophetic).**
   - New file `lifetime/guarded_bor.v` (or `typing/`, if it needs `typeG`).
   - Contents: the laws (L0)–(L4) over §2.2–§2.3.
   - Tests: a toy instance, `c(s,t) := s ↦ t`, exercising every law, including a move after
     a lend.
2. **Prophetic GMB (L3p)** on `proph_bor` / `uniq_body` / `cpd_body` (`uniq_util.v`),
   with the value map from `t` to the borrow's value, and resolution at the end.
3. **Decodability layer.** The instance `c_g(l, fv)` over fancy bytes, with nested cells
   through `a`, and lemmas:
   - create and destroy (`new`, `into_inner`);
   - move: (L1), then a typed `Load`/`Store` or `MemCopy`, then close at `l'`, for any
     number of sibling and nested cells;
   - shared and mutable access;
   - atomics (load, store, `MCAS`) through (L2) guards.

   It lives next to the old `heap_cells.v` until phase 5.
4. **Typing.**
   - `pcell_ty` and `cell_points_to` are redefined.
   - `type_pcell_borrow_instr` returns `&shr{κ} ty` (L2), and
     `type_pcell_borrow_mut_instr` returns `&uniq{κ} ty` (L3p), with the prophecy mapping
     `((g,x),(g',x'))` to `(x,x')`.
   - The unified place rules then apply below them: field reads and writes, reborrows,
     loads through the unique borrow.
   - `val_own` in transit uses the (L1) closers instead of `unt_fbytes`.
   - Deleted: `cell_shr_ty`, `cell_uniq_ty`, `pinned_ty`, `cell_loc`, and the two bespoke
     access rules.
   - Examples: through `borrow_mut`, write one field of a pair inside a cell and read it
     back through `borrow`; a reborrow below a cell borrow; moving the cell after the
     borrow ends.
5. **Delete the cell heap.**
   - The cell machinery goes from `lang/heap_cells.v` and `lang/heap.v`: chains,
     `fcmap`, banks, D3, `gnest`, the sub-position and cell WP rules.
   - Port `pcell_tests`, `pcell_example`, `pcell_move`, `ra` and `protocol`.
6. **Docs.** Outcome sections in this file and in `pcell-multibyte-cells.md`.

## 5. Decisions

1. The placement is the location (§3).
2. P1 is solved by the special openings of §2.1, which extend the lifetime logic. No
   typing-rule changes are needed.
3. Whether to delete the physical cell heap in phase 5 (recommended), or keep it as a
   second model: still open.
