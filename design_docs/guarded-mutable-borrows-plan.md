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

## 2. Model (phase 1 has to settle it)

Candidate M1:
- **Instance state.** An Iris invariant (namespace inside `↑NllftUsr`) holds the
  authoritative ghost state: placement `●s`, contents `●E t`. Its state is one of:
  - `idle`: holds `c(s,t)`;
  - `out`: `c` taken by (L1), or by a shared opening;
  - `lent κ' inh`: during (L3).
- **The two sides.** `a γ s := ◯s ∗ tokA`; `b γ t := ◯E t ∗ tokB`. They live in disjoint
  ghost cells, so guards of the two combine (`guards_and_point`, as was done for
  `loc_side`/`gdyn`).
- **(L2):** combine the guards of `a` and `b`. The invariant is guarded by `True`. Inside
  the combined guard, agreement shows the state is `idle` at `(s,t)`.
- **(L3):**
  - Open the `b`-borrow guarded by `@[κ]` (`llftl_bor_acc_guarded`).
  - Move `b` into the invariant.
  - Create a **fresh** borrow of `∃t, c(s,t) ∗ wtok γ t` with `llftl_borrow`. Its
    inheritance `inh` is stored in the invariant (state `lent κ inh`), not given to either
    side.
  - The `b`-borrow's content becomes `True`. Its back-map takes `b γ t'` (the current
    value) out of the invariant, which can be done without the dead token, because the
    writer updates `●E`/`◯E` there.
  - The result is the fresh borrow.
- **(L4) for the `a` side.** Running `inh` needs `[†κ]`.
  - **Open problem P1:** the owner of `a` gets it back through generic inheritance (the
    place machinery unblocking `pcell`), and the owned `a` does not record that `κ` is
    dead.
  - Candidate fixes:
    1. **GMB-aware sharing.** The `pcell` type's sharing goes through a GMB operation
       `a γ s ={E}=∗ sh γ s κ ∗ ([†κ] ={E}=∗ a γ s)`, whose inheritance normalises
       outstanding lends at any `κ' ⊑ κ`, using `[†κ] → [†κ']`. (L3) takes `sh γ s κ`
       and `κ' ⊑ κ` instead of a bare guard.
       - To check: whether `ty_share`, which receives `&{κ}(ty_own)` and not the owned
         `a`, can install such a normaliser. If not, the generic inheritance has to run a
         type-specific hook.
    2. **`a` records the sharing lifetime,** and (L1) succeeds whenever the recorded lend
       lifetime `κ' ⊑ κ_sh` is dead; an owned `a` then proves `[†κ_sh]` through a
       persistent witness deposited at inheritance.
    3. **A new primitive in the lifetime logic:** a borrow with a *shared* inheritance
       that anyone holding `[†κ]` can run once.
- **Checkpoint:** phase 1 reports which fix works before anything is built on it.

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

1. **GMB library (non-prophetic).**
   - New file `lifetime/guarded_bor.v` (or `typing/`, if it needs `typeG`).
   - Contents: the statement of (L0)–(L4) with the placement, model M1, and the
     resolution of P1.
   - Tests: a toy instance, `c(s,t) := s ↦ t`, exercising every law, including move after
     lend and restoration of both sides.
   - **Checkpoint with the user:** the model, P1's resolution, and any extension of the
     lifetime logic.
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

## 5. Decisions for the user

1. The placement parameter `s`, instantiated with the location (recommended), versus `c`
   over the group's contents with the pin threaded everywhere.
2. Whether extending the lifetime logic is acceptable if P1 needs it (fix 3).
3. Whether to delete the physical cell heap in phase 5 (recommended), or to keep it as a
   second model.
