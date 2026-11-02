# Guarded mutable borrows, and a decodability layer built on them (plan)

Status: plan (2026-11-01; all decisions made 2026-11-02). It follows the user's proposal
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
3. The physical cell heap is deleted in phase 5 (user decision, 2026-11-02).

## Outcome: phase 0

Implemented in `lifetime/lifetime_full.v`; tests in `lifetime/lifetime_special_tests.v`.
The internals (`lifetime_internals/*.v`) are unchanged, and so are the statements of all
existing public lemmas.

### Lemmas

```
special_open κ                       (* timeless, not persistent *)
Lemma llftl_special_open_guard κ :
  llft_ctx -∗ special_open κ &&{↑NllftG ∪ ↑NllftO}&&> @[κ].
Lemma llftl_bor_acc_special E P κ :
  ↑Nllft ⊆ E →
  llft_ctx -∗ &{κ} P -∗ @[κ] ={E}=∗ ▷ P ∗ special_open κ ∗
    (∀ Q, ▷ (▷ Q ∗ [†κ] ={↑NllftUsr ∪ ↑NllftUsr2}=∗ ▷ P ∗ special_open κ) ∗ ▷ Q
          ={↑Nllft}=∗ &{κ} Q ∗ @[κ]).
Lemma llftl_bor_acc_special_guarded E G κ P :
  Timeless G → ↑Nllft ⊆ E →
  llft_ctx -∗ &{κ} P -∗ (G &&{↑NllftG}&&> @[κ]) -∗ G ={E}=∗ ▷ P ∗ special_open κ ∗
    (∀ Q, ▷ (▷ Q ={↑NllftUsr ∪ ↑NllftUsr2}=∗ ▷ P ∗ special_open κ) ∗ ▷ Q
          ={↑Nllft}=∗ &{κ} Q ∗ G).
Lemma llftl_bor_idx_acc_special E P κ idx :          (* closer as llftl_bor_acc_special *)
  ↑Nllft ⊆ E → llft_ctx -∗ &{κ, idx} P -∗ idx_bor_tok idx -∗ @[κ] ={E}=∗ …
Lemma llftl_bor_idx_acc_special_guarded E G κ idx P : (* closer as the guarded one *)
  Timeless G → ↑Nllft ⊆ E →
  llft_ctx -∗ &{κ, idx} P -∗ idx_bor_tok idx -∗ (G &&{↑NllftG}&&> @[κ]) -∗ G ={E}=∗ …
```

`NllftO` is now exported by `lifetime_full.v` (same value as the internal one).

### Model

- **Ghost state.** `special_open κ := own sp_name (◯ {[+ κ +]})`, a fragment of an
  authoritative multiset of the lifetimes of all tokens in circulation (new `inG` for
  `authR (gmultisetUR lft)` in `llft_logicGpreS`, new ghost names `sp_name`, `lk_name`).
- **Registry** (`spec_inv sa`, a new conjunct of the `Nmain` invariant, next to `sa`): the
  `● T`, and one entry `(κ, sn)` per token, where `sn` is a reverse borrow `Borrow ∅ κ` whose
  contents is a token `special_open κ`; `T` is the multiset of the entries' lifetimes.
- **Minting** (`llftl_special_register`): mint a token, put it in a fresh borrow
  `&{κ} (special_open κ)` (`outer_borrow_create`), and record its reverse borrow. The special
  accessor joins this borrow with the user's borrow and opens the join normally, handing the
  token out; its closer is the normal closer, with the back-map `▷ Q ∗ [†κ] ={…}=∗ ▷ P ∗
  special_open κ` used as it is.
- **The token comes back by the model's own invariant.** When the first atom of `κ` dies, the
  reverse borrow at `κ` becomes valid, so the box invariant guarantees that it is full: the
  back-map chain has returned a token into it. Nothing depends on the shape of the chain.
- **Certificate.** Either every registered `κ` is alive (`set_map κ ⊆ sa`), and both halves of
  a lock `Delayed lk_name None` are in the registry; or an end of `k` is in progress: the
  registry holds one half of the lock at `Some (k, alive')` and the `NllftO` half of
  `Delayed d_name (Some (k, alive'))`, and every registered `κ` is included in
  `alive' ∪ {[k]}`.
- **End procedure** (`llftl_end_maybe_swell'`). Step 1 (with `NllftO` open): kill `k`, put the
  registry in the locked state, keeping the other half of the lock. Step 2: unlock (the
  half we hold pins `k` and `alive'`), run the back-maps (`outer_kill_lt_step2`, unchanged),
  then collect: for each entry whose lifetime contains `k`, take the token out of its
  reverse borrow (`outer_unborrow_start`, as in `llftl_borrow_rev`) and deallocate it from
  `● T` (`spec_collect`); re-establish the certificate for the other entries; close `Nmain`
  and `NllftO`. Entries only contain swell atoms, so ending a temporary (non-swell) lifetime
  collects nothing and needs no later.
- **Guard law.** `llft_ctx` now also contains a guard view of `NllftO`,
  `True &&{↑NllftO}&&> ▷ (…)` (the invariant is allocated with `guards_alloc_with_inv`).
  The guard opens it and `Nmain`: `◯ {[+κ+]} ∧ ● T` gives `κ ∈ T`; the closed `NllftO` holds
  `Delayed None`, which refutes the locked state; so `κ ⊆ sa`, and the guard returns the copy
  of `@[κ]` kept in `sa`. With `NllftO` in the mask, back-maps (run while the end procedure
  holds `NllftO`) cannot use the guard.

### Supported operations after a special opening

All of them. The closed borrow `&{κ} Q` is an ordinary full borrow, and the collection only
uses the reverse borrow of the registry, whose fullness the model guarantees whatever
happened to the closed borrow: normal, special, atomic or guarded reopening, reborrowing,
splitting and joining, unnesting, conversion to and from indexed borrows, freezing, faking.
The tests exercise reopening, reborrowing and split/join.

### Deviations

- The proposal's stray `∃ κ', @[κ']` is dropped, as requested.
- The guarded accessor's back-map has no `[†κ]`, like `llftl_bor_acc_guarded`.
- The indexed versions close to a full borrow `&{κ} Q`. A closer at the same index
  (returning `idx_bor_tok idx`, like `llftl_bor_idx_acc`) is not provided: the token's borrow
  is joined with the opened borrow, so the opened borrow cannot keep its index.
- The prophetic version (for L3p) is not part of phase 0; it should follow the same pattern
  (join the token borrow into the prophetic borrow's underlying full borrow).

## Outcome: phase 1

Implemented in `lifetime/guarded_bor.v`; tests in `lifetime/guarded_bor_tests.v`. Nothing
else changed. No axioms (`Print Assumptions`: closed under the global context).

### Interface

Generic over `S` (placement), `T` (contents) and `c : S → T → iProp Σ`, with one
assumption: **`∀ s t, Timeless (c s t)`**. It lets the state invariant be a guard without a
later, so that (L2) keeps the step-index of its inputs, and (L0), (L1), (L3) move `c` in and
out of the instance without laters. The phase-3 instance (`l ↦b[^fbs]`, pure facts, nested
`gmb_a`) is timeless.

- Ghost state: `gmbG Σ S T` (two `excl_authR (leibnizO _)`), `gmbΣ S T`.
- An instance name `γ : gmb_name` has two ghost names and a **depth** `gmb_depth γ : nat`,
  fixed at creation: the largest step-index of the share guards that (L3) accepts.
- `gmb_a γ s`, `gmb_b γ t`: exclusive (`gmb_a_excl`, `gmb_b_excl`), timeless point props
  (`gmb_a_point`, `gmb_b_point`), in disjoint ghost names.
- `gmb_inv c γ`: persistent instance invariant (`guard_inv` and `other_inv`).

### Laws

```
Lemma gmb_create E d s t :                                                     (* L0 *)
  c s t ={E}=∗ ∃ γ, ⌜gmb_depth γ = d⌝ ∗ gmb_inv γ ∗ gmb_a γ s ∗ gmb_b γ t.
Lemma gmb_destroy E γ s t :                                                    (* L0 *)
  ↑Nllft ⊆ E →
  gmb_inv γ -∗ gmb_a γ s -∗ gmb_b γ t ={E}=∗ c s t.
Lemma gmb_move E γ s :                                                         (* L1 *)
  ↑Nllft ⊆ E →
  gmb_inv γ -∗ £ (1 + gmb_depth γ) -∗ gmb_a γ s ={E}=∗
    ∃ t, c s t ∗ (∀ s', c s' t ={E}=∗ gmb_a γ s').
Lemma gmb_share G F n γ s t :                                                  (* L2 *)
  ↑NllftUsr2 ⊆ F →
  gmb_inv γ -∗ (G &&{F; n}&&> gmb_a γ s) -∗ (G &&{F; n}&&> gmb_b γ t) -∗
    (G &&{F; n}&&> c s t).
Lemma gmb_lend_later E γ κ s n :                                               (* L3 *)
  ↑Nllft ⊆ E → n ≤ gmb_depth γ →
  llft_ctx -∗ gmb_inv γ -∗ (@[κ] &&{↑NllftG; n}&&> gmb_a γ s) -∗ £ n -∗
  &{κ} (∃ t, gmb_b γ t) -∗ @[κ] ={E}=∗ &{κ} (∃ t, c s t) ∗ @[κ].
Lemma gmb_lend_guarded_later E G γ κ s n :                                     (* L3 *)
  Timeless G → ↑Nllft ⊆ E → n ≤ gmb_depth γ →
  llft_ctx -∗ gmb_inv γ -∗ (@[κ] &&{↑NllftG; n}&&> gmb_a γ s) -∗ £ n -∗
  &{κ} (∃ t, gmb_b γ t) -∗ (G &&{↑NllftG}&&> @[κ]) -∗ G ={E}=∗ &{κ} (∃ t, c s t) ∗ G.
Lemma gmb_lend E γ κ s :                                         (* L3, n = 0, any depth *)
  ↑Nllft ⊆ E →
  llft_ctx -∗ gmb_inv γ -∗ (@[κ] &&{↑NllftG}&&> gmb_a γ s) -∗
  &{κ} (∃ t, gmb_b γ t) -∗ @[κ] ={E}=∗ &{κ} (∃ t, c s t) ∗ @[κ].
Lemma gmb_lend_guarded E G γ κ s :                               (* L3, n = 0, any depth *)
  Timeless G → ↑Nllft ⊆ E →
  llft_ctx -∗ gmb_inv γ -∗ (@[κ] &&{↑NllftG}&&> gmb_a γ s) -∗
  &{κ} (∃ t, gmb_b γ t) -∗ (G &&{↑NllftG}&&> @[κ]) -∗ G ={E}=∗ &{κ} (∃ t, c s t) ∗ G.
```

(L4) is not a lemma: after `[†κ]`, the lender's inheritance of `&{κ}(∃ t, gmb_b γ t)` gives
`gmb_b γ t'` at the final value, and the owner's `gmb_a γ s` works with `gmb_move` on its
own (tests below).

### Model

As §2.2, with these refinements:
- **Ghost state.** Per side, an `excl_auth` with the authority split in two halves
  (`●{#1/2}`), one in each invariant (`Auth`, `Auth2`), and the exclusive fragment `◯`. The
  `a` side is `Here s | Moving t | Destroyed` (`a(s)`, `a_out(t)`), the `b` side is
  `In t | Out s κ | Gone` (`b(t)`, `b_out(s, κ)`). `a_out` remembers `t` (the mover's way
  back must deposit at the state's `t`), and `Out` remembers `s` (the back-map must deposit
  at the state's `s`); the proposal's `b_out(s, κ)` is one fragment of the `b` name.
- **`guard_inv`** := `True &&{↑NllftUsr2}&&> ∃ st, Auth st ∗ body st`, with body
  `(Here s, In t) ↦ c s t`, `(Here s, Out s' _) ↦ ⌜s = s'⌝`, `(Moving t, In t') ↦ ⌜t = t'⌝`,
  `(Destroyed, Gone) ↦ True`, and `False` otherwise. It is allocated with `guards_alloc` and
  its later removed by timelessness. It is opened like an invariant (`guards_open`, putting
  back another witness).
- **`other_inv`** := `inv NllftUsr (∃ sa tb, Auth2 sa tb ∗ …)`, holding in state `Out s κ`
  the token `special_open κ` and the guard
  `special_open κ &&{↑NllftG ∪ ↑NllftO; gmb_depth γ}&&> gmb_a γ s`.
- **(L1)** opens `other_inv` first (`NllftUsr`). In state `Out s κ` it spends one credit on
  the invariant's later and `gmb_depth γ` credits on the stored guard, opens it with the
  token (mask `↑NllftG ∪ ↑NllftO`, still available) and gets a second `gmb_a`: `False`.
  Otherwise it opens `guard_inv` (`NllftUsr2`).
- **(L2)**: `guards_strengthen_exists` twice against `G &&> True &&> guard_inv`, with
  `a ∧ Auth ⊢ ⌜…⌝` (`and_own_discrete_ucmra` and a lemma on `excl_auth` with fractional
  authority), then `guards_weaken` projects out `c s t`.
- **(L3)** opens the borrow with `llftl_bor_acc_special(_guarded)`. With the token it opens
  the guard `special_open κ &&> guard_inv` strengthened by the owner's share (so the state
  is `Here s`; this is what refutes `Moving`, and costs the `£ n`), moves the `b` side to
  `Out s κ`, takes `c s t`, and stores the token and the guard in `other_inv`. The back-map
  (`={↑NllftUsr ∪ ↑NllftUsr2}=∗`, no `[†κ]` needed) moves the `b` side back to `In t'`,
  deposits `c s t'`, and returns the token from `other_inv`.

### Tests (`guarded_bor_tests.v`)

Toy instance: `c s t := s ↪[γm] t` (a ghost map `nat → nat`; the tests hold its authority
to observe values).
- `test_create_destroy` (L0).
- `test_move` (L1 with a change of placement: delete `s`, insert `s'`, close at `s'`; destroy).
- `test_share_read` (L2: shares of `gmb_a` and `gmb_b` at `κ`; read the contents).
- `test_lend_write_end_move` (L3, L4): share `gmb_a` at `κ`, lend `gmb_b` at `κ`, write `t'`
  through the borrow, end `κ`; the lender's inheritance is `gmb_b γ t'` (shown with (L2)
  from the owned `gmb_a ∗ gmb_b`), then the owner moves.
- `test_lend_abandoned` (L4, owner's side alone): the lender drops its borrow and its
  inheritance; after `[†κ]` the owner moves.
- `test_lend_later`: depth 1, the owner's share is a frozen full borrow
  (`llftl_bor_guard`, step-index 1); lend with `£ 1`, move with `£ 2`.
- `test_relend_sub_lifetime`: the typing-layer shape. The owner shares at `α`; two
  successive lends at `α ⊓ β1`, `α ⊓ β2` through the guarded accessor
  (`G := @[α] ∗ @[βi]`), each ended by its `βi`; then `α` ends and the owner moves. The
  owner gets `gmb_a` back only from the inheritance of its share, i.e. after `[†α]`, when
  every lend lifetime has ended and its back-map has run: the lent-out case of (L1) (refuted
  in `gmb_move`) is unreachable for well-behaved clients.

### Deviations from §2

- `gmb_a`, `gmb_b` are plain fragments, and the persistent `gmb_inv c γ` is a separate
  argument of the laws (created by `gmb_create`). Folding it into `a`/`b` does not work: the
  guard stored in `other_inv` would mention `other_inv`, and (L2) needs the invariant
  outside the guards.
- (L1) needs `£ (1 + gmb_depth γ)`, not a fixed `▷`: the stored guard is under the later of
  `other_inv`, and has the step-index of the owner's share.
- Share guards with a step-index `n` are supported up to the depth of the instance, chosen
  at creation; (L3) then needs `£ n`. Unbounded step-indices are not supported: (L1) would
  not know how many credits to spend. The typing layer must fix a bound per cell (or share
  `gmb_a` at index 0).
- The (L2) mask must contain `↑NllftUsr2` (it does if it contains `↑NllftG`).
- Not provided: an indexed-borrow version of (L3) (phase 0 closes indexed special openings
  to full borrows anyway), and the prophetic (L3p) (phase 2).
