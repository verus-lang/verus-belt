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

## Outcome: phase 2

Implemented in `lifetime/guarded_bor.v` (lends at the level of special openings),
`util/proph_bor.v` (special openings of prophetic borrows) and the new
`lifetime/guarded_bor_proph.v` (L3p); tests in `lifetime/guarded_bor_proph_tests.v`. No
axioms (`Print Assumptions` of the lemmas and tests: closed under the global context).
Nothing else changed; the statements of the phase-1 laws are unchanged.

**Result.** (L3p) holds for prophetic borrows whose payload gives back the contents
*eagerly* (in the back-map). It does **not** hold, with the model of §2, for the bodies of
`&uniq{κ} ty` (`uniq_body`, `uniq_gbody`/`cpd_body`), whose contents are lazy. So the
lemma that phase 4 wanted ("uniq body of the permission type at `κ` + share guard of `a` ⇒
uniq body of `ty` at `κ`") is not provided. Why, and the proposed extension (phase 2b), are
below.

### Lemmas

(L3) split at a special opening (`guarded_bor.v`; the phase-1 `gmb_lend*` are now proved
with them):
```
Definition gmb_lent γ s κ : iProp Σ.        (* b_out(s, κ); timeless *)
Lemma gmb_lend_start E γ κ s t n :
  ↑Nllft ⊆ E → n ≤ gmb_depth γ →
  llft_ctx -∗ gmb_inv γ -∗ (@[κ] &&{↑NllftG; n}&&> gmb_a γ s) -∗ £ n -∗
  special_open κ -∗ gmb_b γ t ={E}=∗ c s t ∗ gmb_lent γ s κ.
Lemma gmb_lend_stop γ κ s t' :
  gmb_inv γ -∗ gmb_lent γ s κ -∗ c s t' ={↑NllftUsr ∪ ↑NllftUsr2}=∗
    gmb_b γ t' ∗ special_open κ.
```

Special openings of generalized prophetic borrows (`proph_bor.v`; phase 0's join pattern,
through `llftl_bor_idx_acc_special_guarded`):
```
Lemma proph_idx_bor_gen_acc_rebody_special_guarded E κ ξ x idx (P Q: pv_val ξ → pv_proph ξ → iProp Σ) G :
  Timeless G → ↑Nllft ⊆ E →
  llft_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗
  proph_bor_tok ξ x idx -∗ proph_idx_bor_gen κ ξ idx P -∗ G ={E}=∗ ∃ wπ,
    ▷ P x wπ ∗ special_open κ ∗
    (∀ x1 wπ1, ▷ Q x1 wπ1 -∗
       ▷ (∀ x2 wπ2, ▷ Q x2 wπ2 ={↑NllftUsr ∪ ↑NllftUsr2}=∗ ▷ P x2 wπ2 ∗ special_open κ)
       ={↑Nllft}=∗ ∃ idx', proph_bor_tok ξ x1 idx' ∗ proph_idx_bor_gen κ ξ idx' Q ∗ G).
Lemma proph_idx_bor_gen_map_special E κ ξ x idx (P: pv_val ξ → pv_proph ξ → iProp Σ)
    ζ y (Q: pv_val ζ → pv_proph ζ → iProp Σ) (fπ: proj1_sig (pv_ty ζ) → proj1_sig (pv_ty ξ)) G :
  Timeless G → ↑Nllft ∪ ↑prophN ⊆ E →
  llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ (G &&{↑NllftG}&&> @[κ]) -∗
  (∀ G' wπ, ⌜Timeless G'⌝ -∗ (G' &&{↑NllftG}&&> @[κ]) -∗ G' -∗
     special_open κ -∗ ▷ P x wπ ={E}=∗
     G' ∗ ∃ wζ, ▷ Q y wζ ∗
     (∀ y' wζ', ▷ .PC[ζ] y' wζ' -∗ ▷ Q y' wζ' ={↑NllftUsr ∪ ↑NllftUsr2}=∗
        (▷ ∃ x', P x' (λ π, fπ (π ζ))) ∗ special_open κ)) -∗
  G -∗ proph_loan ζ y -∗ proph_bor_tok ξ x idx -∗ proph_idx_bor_gen κ ξ idx P ={E}=∗
    ⟨π, π ξ = fπ (π ζ)⟩ ∗ (∃ idx', proph_bor_tok ζ y idx' ∗ proph_idx_bor_gen κ ζ idx' Q) ∗ G.
```
They are `proph_idx_bor_gen_acc_rebody_guarded` and `proph_idx_bor_gen_map` (the accessor
under `uniq_body_transform_gen`) with the token added.

(L3p) (`guarded_bor_proph.v`, over the phase-1 section variables `c`, `Timeless (c s t)`):
```
Lemma gmb_lend_proph E κ ξ x idx (P Q: pv_val ξ → pv_proph ξ → iProp Σ) G γ s n :
  Timeless G → ↑Nllft ⊆ E → n ≤ gmb_depth γ →
  llft_ctx -∗ uniq_ctx -∗ gmb_inv c γ -∗
  (@[κ] &&{↑NllftG; n}&&> gmb_a γ s) -∗ £ n -∗ (G &&{↑NllftG}&&> @[κ]) -∗
  (∀ wπ, ▷ P x wπ ={E}=∗ ∃ t, gmb_b γ t ∗ (c s t ={E}=∗ ▷ Q x wπ ∗
     (∀ x2 wπ2, ▷ Q x2 wπ2 ={↑NllftUsr ∪ ↑NllftUsr2}=∗
        ∃ t', ▷ c s t' ∗ (gmb_b γ t' -∗ ▷ P x2 wπ2)))) -∗
  G -∗ proph_bor_tok ξ x idx -∗ proph_idx_bor_gen κ ξ idx P ={E}=∗
    ∃ idx', proph_bor_tok ξ x idx' ∗ proph_idx_bor_gen κ ξ idx' Q ∗ G.
Lemma gmb_lend_proph_map E κ ξ x idx (P: pv_val ξ → pv_proph ξ → iProp Σ)
    ζ y (Q: pv_val ζ → pv_proph ζ → iProp Σ) (fπ: proj1_sig (pv_ty ζ) → proj1_sig (pv_ty ξ)) G γ s n :
  Timeless G → ↑Nllft ∪ ↑prophN ⊆ E → n ≤ gmb_depth γ →
  llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ gmb_inv c γ -∗
  (@[κ] &&{↑NllftG; n}&&> gmb_a γ s) -∗ £ n -∗ (G &&{↑NllftG}&&> @[κ]) -∗
  (∀ G' wπ, ⌜Timeless G'⌝ -∗ (G' &&{↑NllftG}&&> @[κ]) -∗ G' -∗ ▷ P x wπ ={E}=∗
     G' ∗ ∃ t, gmb_b γ t ∗ (c s t ={E}=∗ ∃ wζ, ▷ Q y wζ ∗
       (∀ y' wζ', ▷ .PC[ζ] y' wζ' -∗ ▷ Q y' wζ' ={↑NllftUsr ∪ ↑NllftUsr2}=∗
          ∃ t', ▷ c s t' ∗ (gmb_b γ t' -∗ ▷ ∃ x', P x' (λ π, fπ (π ζ)))))) -∗
  G -∗ proph_loan ζ y -∗ proph_bor_tok ξ x idx -∗ proph_idx_bor_gen κ ξ idx P ={E}=∗
    ⟨π, π ξ = fπ (π ζ)⟩ ∗ (∃ idx', proph_bor_tok ζ y idx' ∗ proph_idx_bor_gen κ ζ idx' Q) ∗ G.
```
- `gmb_lend_proph` keeps the prophecy variable, its value and its controller: resolving the
  new borrow resolves `ξ` itself.
- `gmb_lend_proph_map` is the value-map version: the old variable is pre-resolved to `fπ` of
  the fresh one (e.g. `fπ y := (g, y)` for the permission's value `(g, x)` and the contents'
  `x`), so resolving the new borrow resolves the old one consistently, and the old borrow's
  body is restored at the controller `fπ ζ` when `κ` ends.
- The caller splits the permission off the old payload and builds the new payload from the
  contents. The way back, from the final new payload, runs in the back-map and must give
  back the contents there (`∃ t', ▷ c s t' ∗ …`).

### Tests (`guarded_bor_proph_tests.v`)

The toy instance of phase 1, with contents in `positive` (a type of prophecy values). The
lender holds a generalized prophetic borrow of the permission
(`proph_loan_borrow_gen`).
- `test_proph_map_write_resolve_end_move`: the `borrow_mut` shape. The permission's
  variable `ξ` ranges over pairs `(g0, t)`, the contents' variable `ζ` over `t`. Lend with
  `gmb_lend_proph_map` (`fπ y := (g0, y)`); write `t'` through the new borrow
  (`proph_idx_bor_gen_acc_idx`); resolve it (`proph_idx_bor_gen_resolve_share`); end `κ`.
  The test concludes `⟨π, π ξ = (g0, t')⟩`, and that the lender's inheritance gives
  `gmb_b γ t'` (observed with (L2)); the owner then moves.
- `test_proph_inplace_write_resolve_end_move`: the same with `gmb_lend_proph` (one
  variable, `⟨π, π ξ = t'⟩`).
- `test_proph_lend_abandoned`: after the lend, the lender drops its new borrow, the
  observation and its inheritance; after `[†κ]` the owner moves.

### Why (L3p) fails for `&uniq` bodies

1. **The back-map must give back the contents.** (L4) lets the owner move after `κ`
   without the lender. So when `κ` ends, the contents must be back in the instance before
   anyone can own `gmb_a γ s`. The only code that runs at the end of `κ` is the back-map of
   the special opening (step 2 of `llftl_end`). It runs at mask `↑NllftUsr ∪ ↑NllftUsr2`, and
   phase 0 requires it to also return `special_open κ`, which is how `gmb_move` refutes the
   lent-out state. That is the back-map `c(s, t') ⇛ b(t') ∗ special_open κ` of §2.3.
2. **The `&uniq` body does not have the contents at that point.** In
   `uniq_gbody κp ty tid l c wπ`, the bytes `cbytes ty x l` (which phase 3 identifies with
   `c_g(l, ty_fval x)`) are inside `guarded_upd lazyE @[ty_lft ty] (⧖ ∗ leaf_node …)`. For a
   pattern `PatBlocked α`, they are behind a further `[†α] ={lazyE}=∗ guarded_upd …`
   (`blocked_owned`). The rules that act on the borrow during `κ` create such states:
   - writes through unfolded places (`norm_pat` blocks at `κp`);
   - reborrows (`PatBlocked κ'`);
   - transformations (`uniq_gbody_map` maps lazily).
3. **The back-map cannot force the body.** Forcing needs:
   - the mask `lazyE ⊇ ↑Nllft`, which is open during step 2;
   - a guard of `@[ty_lft ty]`;
   - for blocked parts, `[†α]`. The guarded special accessor gives the back-map no dead
     token (the opening is at a temporary lifetime).

   So no back-map can produce `c s t'` from the final new body.
4. **Deferring the settlement does not work either.** Suppose the back-map only returned the
   token and stored the lazy body in `other_inv` ("pending"). Then:
   - (L2) and (L3) need the contents in `guard_inv`;
   - (L1) needs the owner to force the body. `gmb_move` has neither `[†κ]` nor a guard for
     the payload's lifetime. The owner does not even know `κ`: the same `gmb_a` share can
     serve many lends.

   The lender could settle: its old body can be closed at `PatBlocked κ`, which receives
   `[†κ]`. But (L4) must not depend on the lender.

### Proposed extension (phase 2b): pending lends, settled by either side

All of the following stays within the current lifetime logic.

1. **Registered shares.** Before sharing at `α`, the owner turns `gmb_a γ s` into
   `gmb_a_sh γ s α`, an a-state `Shared s α`, equivalent to `Here s` for `guard_inv`. The
   lazy (L3p) takes `@[κ] &&{↑NllftG; n}&&> gmb_a_sh γ s α` and `κ ⊑ α`.
   - The owner unshares with
     `gmb_a_sh γ s α ∗ [†α] ∗ (G &&{↑NllftG}&&> @[β]) ∗ G ={lazyE ∪ ↑gmbN}=∗ gmb_a γ s ∗ G`.
     This settles a pending lend: `[†κ]` follows from `κ ⊑ α`.
   - `β` is the payload's lifetime (`ty_lft ty`), fixed when the instance is created, like
     the depth.
2. **Pending state.** The back-map moves the b-side from `Out s κ` to `Pending s κ`. It
   stores the final new payload (under `▷`) and the b fragment in `other_inv`, and returns
   the token.
   - The payload comes with a settle law, fixed at the lend:
     `▷ Q ∗ [†κ] ∗ guard of β ={lazyE}=∗ ∃ t', c s t' ∗ R t'`. For `&uniq`, this is forcing
     `uniq_gbody κ ty` with `leaf_node_unblock`, and splitting `ofty_owned` into the bytes
     and the rest.
3. **A settle lock.** Use an invariant `inv gmbN K`, with an exclusive token `K` and
   `gmbN` disjoint from `lazyE`. A settler:
   - takes `K` and puts it into `other_inv` with the state `Taken`;
   - closes `other_inv` and forces the payload (`gmbN` stays open);
   - reopens `other_inv`, deposits `c s t'` (b-state `In t'`), and leaves `R t'` for the
     lender (state `Settled t'`);
   - gives back `K`.

   Anyone who meets `Taken` while holding `K` has a contradiction. The back-map holds its
   own b fragment, so it never meets `Taken`.
4. **The lender's claim.** `gmb_claim γ κ ∗ [†κ] ∗ guard of β ={lazyE ∪ ↑gmbN}=∗
   ∃ t', gmb_b γ t' ∗ R t'` either settles the lend or takes the residue. It runs in the
   lazy update of the old body. `gmb_lend_proph_map`'s way back would build that old body
   at `PatBlocked κ` (with `pat_ok` from `κ ⊑ κp`), so that its `blocked_owned` gets `[†κ]`.
5. **At the `&uniq` level.** A special `uniq_body_transform_gen`, through
   `proph_idx_bor_gen_map_special`, with `κp := κ` for the new borrow, gives
   `uniq_body (permission type) at κ ⇒ uniq_body ty at κ`. Its way back is items 2 and 4.
6. **Typing (phase 4).**
   - The share predicate of `pcell ty` at `α'` carries the registered root:
     `∃ α, α' ⊑ α ∗ (@[α'] &&> gmb_a_sh γ s α)`. `ty_share` registers the share, by
     opening the borrow it gets.
   - The ownership is `gmb_a γ s ∨ ∃ α, gmb_a_sh γ s α ∗ [†α]`. The move unshares first;
     typing has `lazyE` and a guard of `ty_lft ty` at that point.

### How phase 4 uses phase 2 as it stands

- `gmb_lend_start`/`gmb_lend_stop` and `proph_idx_bor_gen_map_special` are the building
  blocks of item 5.
- `gmb_lend_proph_map` is (L3p) when the new payload gives back the contents in the
  back-map. This holds for payloads that keep the bytes outside any lazy update, but not
  for `&uniq{κ} ty`.
- Phase 3 does not depend on phase 2. It can proceed with (L0)–(L3) and the toy-tested
  laws; `type_pcell_borrow_mut_instr` returning `&uniq{κ} ty` waits for phase 2b.

### Deviations

- No lemma at the level of `uniq_body`/`cpd_body` (see above). The value map is a
  prophecy map `fπ`, as in `proph_idx_bor_gen_map`, rather than a `syn_type` morphism.
- The lend lemmas take the payload split as a client view shift, rather than fixing the
  payload to `gmb_b`/`c`.

## Phase 2b audit (2026-11-02)

Read-only audit of the approved phase 2b: **lazy c** (the b-side state `In` may hold the
contents lazily; `gmb_b_shr` requires them eager, `gmb_b_uniq` allows lazy), and **option 3**
(in the `&uniq` body model, the top-level bytes `cbytes ty x l` live outside the lifetime
guard `guarded_upd lazyE @[ty_lft ty]`; blocked leaves keep an inheritance layer
`[†α] ={…}=∗ cbytes … ∗ guarded_upd … (ghost…)`). The goal is that the mover can force the
stored contents with mask `lazyE` and dead tokens only, without any lifetime guard. Line
numbers refer to HEAD 1483f90.

**Verdict: go, with changes.** No site in the typing layer needs the guard to produce or
transform top-level bytes. Every site is either pure or eager (class a), or can be
restructured (class b). There are two required changes outside option 3 itself:
1. A small change to the lifetime-logic internals gives the guarded special back-map a
   dead token (Q3). It has been checked in an experiment.
2. On the GMB side, forcing has to happen with the GMB invariants closed. This needs a
   settle lock, and a mask `lazyB` for the bytes layer that excludes the lock's namespace
   (Q5).

### Q1. Where bytes are produced or transformed under a guarded lazy update

Classes: **(a)** pure or eager, no change beyond restating; **(b)** needs restructuring
(how is given); **(c)** blocker. No site is in class (c).

| Site | What happens to the bytes | Class |
|---|---|---|
| `uniq_payload` (uniq_util.v:396) and its API: `_intro(_later)`, `_run`, `_force` (404–438) | The payload becomes `cbytes ty x l ∗ guarded_upd(⧖ ∗ gho)`. The statements of `_run` and `_force` are unchanged. | a |
| `uniq_payload_map` (442) | Its premise `gho ∗ cbytes ={lazyE}=∗ gho' ∗ cbytes'` splits into an eager bytes map and a lazy ghost map. Its only users are `uniq_body_mono_upd` (bytes unchanged) and `uniq_body_transform_lazy` (no users outside the file). | b, trivial |
| `cpd_body` (166) and `uniq_gbody` (459) | The node parameter splits into a bytes part and a ghost part: `∃ v, nbytes p r v l ∗ guarded_upd(⧖ ∗ ngho p r v d g tid l)`. See "Shape" below. | b, central |
| `ofty_owned` (343) | Unchanged. It is already `cbytes ∗ ▷^m gho`, with no later on the bytes. | a |
| `blocked_owned` (346) and `leaf_owned`/`leaf_node` (351, 389) | The inheritance becomes `[†α] ={lazyB}=∗ ∃ x, cbytes ty x l ∗ guarded_upd lazyE @[ty_lft ty] (rel ∗ ⧖ ∗ ▷^m gho)`. Producers: (1) `place_puniq.v:681–697`: `Back1 †α` (at `↑Nllft`), the stored `£c`, and `uniq_lender_settle`, which now fires the lender body's bytes layer with `pat_ok α` and `[†α]`, no guard; (2) `uniq_gbody_map`, blocked case; (3) the leaf views of structured refinements (Conv, below). | b |
| `shr_blocked_owned` (ltype.v:313), created by `ofty_owned_share` (place_shr.v:48) | Today the bytes and the ghost are borrowed together at `α`. Instead, borrow them separately (two `llftl_borrow`), so that there are two inheritances: `[†α] ={lazyB}=∗ cbytes`, which is timeless and needs no credit, and the ghost one. `PatShrBlocked α` is in `pat_blk_lfts` (lstate.v:355), so `pat_ok` covers it. | b, small |
| `blocked_uniq` (ltype.v:286) | Not part of any `cpd` body: the children of a `cpd` node are always `Owned 0` (ltype.v:623–676). A Uniq-mode blocked leaf is a whole borrow, not top-level bytes. | a |
| Conv in back-maps: `prod_node_leaf` (ltype.v:1479), `ltype_owned_leaf_node` (1983), `_uniq` (2097); used by the closing view shifts of `prod_ofty_unfold_uniq` (1559), `cpd_rebody` (1650), `cpd_rebody_ext` (1697), `cpd_rebody_gen` (pctx_acc.v:496) and `cpd_unfold_uniq` (2036) | At a structured refinement the leaf is blocked at `κp` (`norm_pat`). Today it is applied inside `guarded_upd_mono`. Under option 3 it packages the children's bytes parts into the `[†κp] ={lazyB}=∗` layer. This happens at the closing mask (`↑NllftUsr ∪ ↑NllftUsr2`), with no forcing. When it fires: unblock the children's bytes through `pat_ok_dead`, then combine them with pure layout lemmas (`cbytes_pair`, `cbytes_sum`, `cbytes_at_loc`, `cbytes_uniq_bor`). | b |
| `ltype_owned_unblock_fold` (ltype.v:1876), `cpd_own_unblock_fold` (1806), `ltype_uniq_unblock_fold` (1855), `leaf_owned(_s)_unblock` (uniq_util.v:367, ltype.v:1461) | Split each into a bytes unblock (`lazyB` and dead tokens, no guard) and a ghost fold (`lazyE` and the guard). In the `UniqLty` case, the cumulative receipts and credits open the nested borrow. That is ghost: the top-level bytes are only `ptr_cell l l'`. In the `OwnPtrLty` case the pointee, bytes included, stays in the ghost part, because only the top-level bytes leave the guard. | b, largest proof |
| `cpd_unfold_uniq` / `cpd_fold_uniq` (2002, 2045), `prod_ofty_unfold/fold_uniq` (1522, 1568) | Today the hypothesis `Hconv` (`gho ∗ cbytes ⊢ |={lazyE}=> node`, and the converse) is applied under the guard. Under option 3 it splits into a bytes part and a lazy ghost part. The bytes part is pure in every instance (the layout lemmas above), and for pointer nodes `l'` comes from the `PlaceIn` value. | b |
| `cpd_acc`, `cpd_rebody`, `_ext` (ltype.v:1417, 1617, 1664) and `cpd_rebody_gen` (pctx_acc.v:463) | These statements expose `guarded_upd(⧖ ∗ node …)`. They are restated with the split node. Their callers (pctx_acc.v:662, 889) force at a program step and close eagerly (`guarded_upd_intro`). They now need the split lemma for an eager `Owned 0` interpretation. | b |
| `uniq_gbody_map` (uniq_util.v:1175) | Unblocked case: the old body is built in the back-map of `proph_idx_bor_gen_map`, so the bytes part of `Back` must be pure, or at most `↑NllftUsr`. Blocked case: `Back` runs in the inheritance at `lazyB`. If a client's bytes map needs `lazyE`, block the old body at `κp` instead (`pat_ok κp (PatBlocked κp)` is trivial). This is the same trick as `norm_pat`. | b |
| `uniq_body_transform_gen`, `_transform`, `_transform_lazy` (1249, 1303, 1345) | The forward direction is eager at a program step. The way back goes through `uniq_gbody_map`. Its only user outside the file, pptr.v:191 (`points_to_ty ty` ↔ `ty`), maps bytes purely: `points_to_ty`'s own bytes are zero-size, and the pointee bytes go into its ghost. | a / b |
| `uniq_body_reborrow` (1397) and `uniq_restored(_settle)` (1386, 1455; place_puniq.v:882) | The reborrow's final body is copied wholesale, bytes part included. Settling is eager. | a |
| `proph_idx_bor_gen_map(_special)` (proph_bor.v:1345) and `gmb_lend_proph(_map)` (guarded_bor_proph.v) | Generic in the payload. The phase-2 statements are restated for lazy c (the back-map stores a settle law). | b (GMB side) |
| `resolve_uniq_body` (uniq_util.v:1007), the share of `&uniq` (uniq_bor.v:150–190), `uniq_body_acc*` / `settle*` (771–920) and `alloc_uniq_body` (952) | All eager: they force at program steps or with credits. Under option 3 they get simpler: the bytes are available without running `llftl_bor_guarded_upd`. | a |
| Eager unblock rules: place_own.v:222, place_puniq.v:801 and 1119, place_res_ops.v:278, place_res_view.v:269/681 (`&{κ}(blocked_owned …)` in `view_leaf`), place_res_rslv.v:326 | They run the inheritance or update at a step. The outputs change shape (bytes outside). | a, mechanical |
| own.v, shr_bor.v, subtype.v, place_read/write/deep/pshr/memcpy/xprod/sum.v, pcell.v, pcell_borrow.v | Eager, or pure retyping (`cbytes_same`, `bytes_own_iff`). `uniq_body_acc` together with `uniq_payload_run` keeps its statement. | a |

**Shape.** Quantify the bytes part over the fancy value, as phase 3's `c_g` does: bytes
`∃ fv, l ↦b[^fbs] ∗ ⌜frepr (ty_mty ty) fbs fv⌝ (∗ greg_map)`, and ghost
`∃ x, ⌜ty_fval x = Some fv⌝ ∗ rel lr x ∗ ⧖ ∗ gho x`. Quantifying over `x` itself instead
fails for pointer leaves whose value is only known inside the guard, e.g. a nested `&uniq`
folded lazily in the `UniqLty` case of `ltype_owned_unblock_fold`: its bytes (`ptr_cell l l'`)
depend only on `l'`, but `x = (l', x0, ξi, d, g, idx)` is chosen inside the guard. The `fv`
form also makes the mover's `t' = fv` immediate. The fancy value of a pointer depends only
on the pointer (`syn_fval`, prophecy/syn_type.v:594). The split needs a new pair of fixpoints
(bytes and ghost) that mirrors `ltype_own_cp … (Owned m)`, with the lemma
`ltype_own_cp false lt (Owned m) p r … ⊣⊢ ∃ fv, bytes ∗ ghost`. Locals in Owned mode see
only the changed `blocked_owned`/`shr_blocked_owned`.

### Q2. Are bytes ever obtained from ghost ownership?

**Top-level bytes: never, in any lazy context.** Every lazy producer gets them from bytes by
pure layout lemmas.

Bytes do come from ghost ownership in these places, and none of them forces bytes under the
guard:
- **Owned pointers.** The pointee's bytes are in `ty_gho_own (own_bytes …)`
  (`ownptr_ofty_unfold_own`, ltype.v:1335, and the `OwnPtrLty` cases of the unfold/fold
  lemmas). They are not top-level for the `&uniq` place that contains the pointer, so they
  stay in the ghost part.
- **Nested `&uniq`.** The referent's bytes are in the nested body, which is ghost.
- **`points_to_ty` (pptr.v).** Its bytes are zero-size, and the pointee goes into its ghost.
- **`ty_share`.** It only shares the ghost part. It runs eagerly, with steps.
- **The current cell model.** `cell_points_to`'s ghost owns the heap-cell contents. The
  permission is zero-size, so this is not top-level bytes.
- **`greg_map` fragments in `bytes_own_def` (own.v:65).** They are persistent and timeless:
  no guard.

**Phase 3 caveat.** `c_g`'s fancy bytes include `gmb_a γ' (l+o)` for nested cells. That is
exclusive ghost, but timeless and owned, so it needs no guard. While a nested cell is shared
(say for its own `borrow_mut`), the enclosing leaf is `ShrBlocked α` with `α ⊑ κp`, and its
bytes come back through the split shr inheritance.

### Q3. A dead token in the guarded special back-map

**How the opening works.** `llftl_bor_acc_special_guarded` (lifetime_full.v:2225):
1. It creates a temporary non-swell lifetime `κ'` (`llftl_guarded_tok_to_tmp`, 1944).
2. It registers the token borrow at exactly `κ`, joins it with the user's borrow, and opens
   the join with `llftl_bor_acc_maybe_swell'` (1233), with `κ'` as the opener.
3. The closer is `llftl_idx_acc_back_vs` (1170), then `outer_unborrow_end` (unborrow.v:813)
   with `bl = κ'` and `al = κ''`, the borrow's internal lifetime (`κ ⊑ κ''`, from
   `full_bor`).
4. The stored back-map receives only `∃ k ∈ bl, Dead k`, i.e. `[†κ']`. The wrapper discards
   it (`"[Q _]"`, 1243).

**What `[†κ']` is worth.** Nothing: `κ'` is killed when the accessor closes, and `κ' ⊑ κ`
points the wrong way.

**When the back-map runs.** In the `k ∈ al` branch of `llft_vs_for_unborrow_end`
(unborrow.v:208, at 254–262), the atom `k` that is being killed is in `al`, and its dead
token `#Dead` (a `ModuloDeadPers`) is in context. So a variant can also pass
`∃ k ∈ al, Dead k`, i.e. `[†κ'']`.

**Experiment.** I changed `llft_vs_for_unborrow_end`'s back-map hypothesis to
`▷ Q ∗ (∃k∈bl, Dead k) ∗ (∃k∈al, Dead k) ={…}=∗ ▷ P`, in a /tmp copy, adding
`iExists k; modulo_dead_pers_implies_dead`. It checks, `Qed` included. The other branches
only pass the hypothesis to the IH.

**Composed chains.** Later reopenings rebuild `future_vs` from the old one. The old
back-map still runs only in its own `k ∈ al` branch, and `al` is preserved by close, split
and join. So composed chains are fine.

**Lemmas to change** (old statements derivable by weakening):
- `llft_vs_for_unborrow_end` and `_atomic` (unborrow.v:384);
- `inner_unborrow_end` and `outer_unborrow_end`;
- `llftl_idx_acc_back_vs` and `llftl_bor_acc_maybe_swell'`;
- new `llftl_bor(_idx)_acc_special_guarded_dead` variants, whose back-map gets
  `basically_dead κ := ∃κ'', κ ⊑ κ'' ∗ [†κ'']` (built from `κ ⊑ κ''`, which is in scope);
- the two special lemmas of proph_bor.v (1309, 1345).

About 8 lemmas. The phase-0 note "internals unchanged" no longer holds.

**Is `basically_dead` enough?** Yes. The back-map stores it, persistent, in the pending
state. The mover, with mask `lazyE ⊇ ↑NllftG`, then gets:
- `[†κ]`, by `llftl_incl_dead_implies_dead`;
- `[†α]` for every blocked `α`, by `pat_ok_dead` (uniq_util.v:145).

This assumes that the new borrow of the contents has pattern lifetime `κp := κ`, as item 5
of the phase-2b proposal says. `uniq_body_transform_gen` keeps the *old* `κp`, so the GMB
lend must build its body fresh. Then the old (permission) body is closed at `PatBlocked κ`,
with `κ ⊑ κp_old`.

### Q4. Size

| Area | Files | Lemmas touched | Kind |
|---|---|---|---|
| Lifetime internals | unborrow.v, lifetime_full.v, proph_bor.v | about 8 | small |
| `&uniq` body | uniq_util.v | 4 definitions, about 35 lemmas | mostly mechanical; `uniq_gbody_map`, `uniq_lender_settle` and `alloc` are real work |
| Place types | ltype.v | about 25 lemmas, plus the new bytes/ghost fixpoints and the split lemma | the Uniq-mode section (1406–2101) is mostly rewritten |
| Place accessors | pctx_acc.v; place_puniq.v; place_shr.v, place_own.v, place_res_ops.v, place_res_view.v, place_res_rslv.v; uniq_bor.v, pptr.v | `cpd_rebody_gen` and 2 `PUniq` cases; about 6; 1–3 each | |
| GMB | guarded_bor.v, guarded_bor_proph.v (and tests) | | lazy-In state, settle lock, restated (L3p) |

In total, about 12 files, about 90 lemmas of which about 15 are substantial, roughly
2–2.5k lines touched. No typing-rule statement changes.

**Riskiest spots:**
1. `ltype_owned_unblock_fold` split, `UniqLty` case: values only known inside the guard,
   hence the `fv` form.
2. The new fixpoints and the split lemma: blocked and shr-blocked leaves, sums, and the
   existential `fv` threaded through products.
3. The unblocked case of `uniq_gbody_map`, whose bytes map runs at the back-map mask.
4. pctx_acc's nested closers.
5. Qed times of the large conversions.

### Q5. Other blockers for the combined design

1. **Forcing cannot happen with the GMB invariants open.** `lazyE ⊇ ↑NllftUsr ∪ ↑NllftUsr2`
   (`lazyE_NllftUsr`, uniq_util.v:118), and lifetime inheritances need `↑Nllft`, so the
   mover cannot force while `other_inv` or `guard_inv` is open. The pending payload must be
   taken out, the invariants closed, the payload forced, the invariants reopened and the
   result deposited.
2. **The take-out needs a lock.** Both the mover (L1) and the lender's claim (the old body's
   ghost) may settle, and so may `cell_points_to`'s `ty_share` (which needs `b_shr` eager).
   An intermediate state must be ruled out for the others. Use the settle lock of the
   phase-2b proposal (item 3): an exclusive token in `inv gmbN K`, held for the whole
   settlement.
3. **The lock needs a second mask.** It works only if:
   - (a) the bytes layer is forced with a mask that excludes `gmbN`; and
   - (b) the lender's claim and `ty_share` (whose law assumes only
     `↑Nllft ∪ ↑prophN ∪ ↑uniqN ⊆ E`, type.v:453) can open `gmbN`.

   Proposal:
   - `lazyB := ↑Nllft ∪ ↑prophN ∪ ↑uniqN` (today's `lazyE`) is the mask of every
     bytes-layer inheritance (blocked and shr-blocked leaves, the Conv packaging);
   - `lazyE := lazyB ∪ ↑gmbN`, with `gmbN ## lazyB`, for the guarded ghost updates and for
     `ty_share`.

   No bytes-layer inheritance needs `gmbN`: the permission's bytes are zero-size, so the
   claim lives in the ghost part, and nested cells' bytes are owned `gmb_a`. Changing the
   definition of `lazyE` is mechanical (`solve_ndisj`), but it touches every file that
   unfolds it.
4. **`t'` is not known in the back-map.** The value of the final contents is only fixed when
   the contents are forced (blocked leaves, and pointer leaves via `fv`). So the lazy b-state
   cannot carry `t`: `gmb_b_uniq` is `∃ t` until settled. Whoever settles first fixes `t'`
   and leaves `R t'` for the lender. This is consistent with (L1), where `t` is
   existential.
5. **Credits.** The back-map stores `▷ Q`, and `Q`'s bytes layer contains wands, so it is
   not timeless. Forcing therefore costs one credit, on top of the one for `other_inv`'s
   later. Have the lend (a program step) store `£2` in `other_inv`: credits are timeless, so
   settlement then needs no step. This matters for `ty_share`, which may have `d = 0`.
   - No time receipt `⧖` is needed to force the bytes: the receipts are only used by the
     ghost folds.
   - The nested inheritances carry their own credits (e.g. `£c` in place_puniq.v:691;
     place_shr.v:69).
6. **Masks at the mover's step.** At a typed move the mover has `⊤ ⊇ lazyE ∪ ↑gmbN`.
   `gmb_move`'s side condition becomes `lazyE ⊆ E`. The back-map itself only stores, at
   `↑NllftUsr ∪ ↑NllftUsr2`, and never meets the locked state: it holds its own b fragment
   (state `Out`).

## Outcome: phase 2b (steps 1–4)

Implemented as specified by the audit, with the deviations listed per step. No typing-rule
statement changed (the examples build unchanged). `Print Assumptions` of the new lemmas and
tests: closed under the global context (lifetime and GMB layer), or only
`functional_extensionality_dep` (typing layer, as before).

### Step 1: dead token for the guarded back-maps (merge 1d63c9f)

- Internals (`unborrow.v`): the back-map hypothesis of `llft_vs_for_unborrow_end`,
  `inner_unborrow_end` and `outer_unborrow_end` also receives `∃ k ∈ al, Dead k` (the atom
  being killed, in the `k ∈ al` branch). `llftl_idx_acc_back_vs` (local) passes
  `llft_dead_def' κ ∗ llft_dead_def' (set_map LtAtomSwell idx.2)`.
- New public lemmas (`lifetime_full.v`), old statements unchanged:
  ```
  Lemma llftl_bor_acc_maybe_swell'_dead E P κ' κ : ↑Nllft ⊆ E →
    llft_ctx -∗ (llft_alive_def' κ' &&{↑NllftG}&&> @[κ]) -∗ &{κ} P -∗ llft_alive_def' κ' -∗
    |={E}=> ▷ P ∗ (∀ Q, ▷ (▷ Q ∗ (∃ κ'', κ ⊑ κ'' ∗ [†κ'']) ={↑NllftUsr ∪ ↑NllftUsr2}=∗ ▷ P) ∗ ▷ Q
                    ={↑Nllft}=∗ &{κ} Q ∗ llft_alive_def' κ').
  Lemma llftl_bor_acc_guarded_dead E G κ P : Timeless G → ↑Nllft ⊆ E →
    llft_ctx -∗ &{κ} P -∗ (G &&{↑NllftG}&&> @[κ]) -∗ G ={E}=∗
      ▷ P ∗ (∀ Q, ▷ (▷ Q ∗ (∃ κ'', κ ⊑ κ'' ∗ [†κ'']) ={↑NllftUsr ∪ ↑NllftUsr2}=∗ ▷ P) ∗ ▷ Q
                  ={↑Nllft}=∗ &{κ} Q ∗ G).
  Lemma llftl_bor_acc_special_guarded_dead E G κ P :     (* closer as above, with the token *)
  Lemma llftl_bor_idx_acc_special_guarded_dead E G κ idx P :
  ```
  `∃ κ'', κ ⊑ κ'' ∗ [†κ'']` is `basically_dead κ` (uniq_util.v) and `gmb_bdead κ`.
- `proph_bor.v`: `proph_idx_bor_gen_acc_rebody_special_guarded_dead` and
  `proph_idx_bor_gen_map_special_dead` (the way back gets the dead token); the phase-2
  statements are derived from them.
- Deviation: the atomic accessor is not changed: it already gives `[†κ]`.

### Step 2: bytes outside the lifetime guard in `&uniq` bodies (merge f06ed8a)

The bytes of the leaves of `&uniq` bodies are quantified over the fancy value and kept
outside the guarded update of the ghost part (`uniq_util.v`):
```
Definition fbytes ty l fv := ∃ x, ⌜ty_fval x = Some fv⌝ ∗ cbytes ty x l.
Lemma cbytes_fbytes ty x l : cbytes ty x l ⊣⊢ ∃ fv, ⌜ty_fval x = Some fv⌝ ∗ fbytes ty l fv.
Definition ofty_gho m ty lr fv d g tid := ∃ x, ⌜ty_fval x = Some fv⌝ ∗ place_rfn_rel lr x ∗ ▷^m ty_gho_own x d g tid.
Definition blocked_owned m ty α lr tid l :=
  [†α] ={lazyB}=∗ ∃ fv, fbytes ty l fv ∗ guarded_upd lazyE @[ty_lft ty]
    (∃ d' g', ⧖((m + S d') `max` g') ∗ ofty_gho m ty lr fv d' g' tid).
Definition leaf_contents κp ty p r d g tid l :=        (* p' := norm_pat κp p r, lr := prfn_place r *)
  ∃ fv, leaf_owned_b 0 ty p' lr fv tid l ∗ leaf_owned_lz ty p' lr fv d g tid.
  (* unblocked: fbytes ty l fv ∗ ⌜lr_fval ty lr fv⌝ and guarded_upd lazyE @[ty_lft ty] (⧖ ∗ ofty_gho 0 …);
     blocked: blocked_owned and True *)
Definition uniq_payload ty tid l x d g := cbytes ty x l ∗ guarded_upd lazyE @[ty_lft ty] (⧖(S d `max` g) ∗ ty_gho_own x d g tid).
Definition uniq_gbody κp ty tid l c wπ := ∃ p r, pat_ok κp p ∗ ⌜…⌝ ∗ ghost_var (cell_γ c) ½ (lstate p r) ∗
  leaf_contents κp ty p r (cell_d c) (cell_g c) tid l.
Definition cpd_contents κp ty node p r d g tid l :=
  guarded_upd lazyE @[ty_lft ty] (⧖(S d `max` g) ∗ node p r d g tid l) ∧ leaf_contents κp ty p r d g tid l.
Definition cpd_body κp ty node tid l c wπ := … ∗ cpd_contents κp ty node p r (cell_d c) (cell_g c) tid l.
Lemma leaf_contents_unblock κp ty p r d g tid l :
  llft_ctx -∗ pat_ok κp p -∗ [†κp] -∗ leaf_contents κp ty p r d g tid l ={lazyB}=∗
    ∃ fv, fbytes ty l fv ∗ guarded_upd lazyE @[ty_lft ty] (∃ d' g', ⧖(S d' `max` g') ∗ ofty_gho 0 ty (prfn_place r) fv d' g' tid).
```
`lazyB := ↑Nllft ∪ ↑prophN ∪ ↑uniqN`. In `ltype.v`:
```
Lemma ltype_owned_bytes_unblock lt κ tid : lty_simple lt → owned_bytes_unblock lt κ tid.
  (* ltype_own_cp false lt (Owned m) p r d g tid l, with pat_ok κ p, [†κ], ⧖ ={lazyB}=∗
     ∃ fv, fbytes (lty_fold lt) l fv ∗ guarded_upd lazyE @[ty_lft (lty_fold lt)]
       (∃ x d' g', ⌜ty_fval x = Some fv⌝ ∗ ▷ (prfn_den r :== vπ x) ∗ ⧖((m + S d') `max` g') ∗ ▷^m ty_gho_own x d' g' tid) *)
Lemma cpd_contents_eager lt κp p r d g tid l : lty_is_cpd lt → lty_simple lt →
  llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ pat_ok κp p -∗ ⧖(S d `max` g) -∗
  ltype_own_cp false lt (Owned 0) p r d g tid l -∗ cpd_contents κp (lty_fold lt) (ltype_own_cp false lt (Owned 0)) p r d g tid l.
```
`ltype_owned_unblock_fold` keeps its statement (derived from `ltype_owned_bytes_unblock`).

Deviations from the audit's "Shape":
- No new bytes/ghost fixpoints mirroring `ltype_own_cp`: the compound body holds *both* views
  of the same resources (`cpd_contents`, a conjunction): the lazy node (for the openers) and
  the leaf contents of the folded type (for the closing view shift). The producers build both
  (eagerly: `cpd_contents_eager`; from a payload: `cpd_contents_payload`). So the `Conv`
  parameter of `cpd_rebody`/`_ext`/`cpd_rebody_gen` is gone (the closers take `cpd_contents`),
  `prod_node_leaf` is removed, and the back-maps are `cpd_body_leaf` (no update).
- `fbytes` is stated with a witness value (equivalent to the fancy-bytes form of
  `bytes_own_brepr` whenever some value has that fancy value); all layout reasoning stays at the
  value level.
- Blocked leaves have no lazy part (their inheritance gives both parts); `leaf_rcpt` gives the
  receipt only for unblocked states.
- The folds of compound bodies back to the leaf at the trivial state force the contents:
  `prod_ofty_fold_uniq` and `cpd_fold_uniq` take a guard for the lifetime of the folded type
  and `£1` (their callers, `vplace_conv` instances, have them). `cpd_unfold_uniq` requires a
  structured refinement.
- `shr_blocked_owned` keeps one inheritance (its mask becomes `lazyB`; it already fires at
  `↑Nllft` with a stored credit), and so does the view of shared-blocked leaves.
- `uniq_gbody_map` always blocks the old body at `κp` and takes a split way back
  (`BackB` on `fbytes` at `lazyB`, with a residue `RB`, and `BackG` on the ghost part); so do
  `uniq_body_transform(_gen, _lazy)` (pptr.v instantiates `RB`).
- Resolution and sharing inside borrows use `llftl_bor_cpd_contents(_step)` (`ltype.v`).

### Step 3: lazy GMB lends, claims, settle lock, `b_uniq`/`b_shr` (merge 2977149)

`lifetime/guarded_bor.v`. New namespaces `gmbN`, `gmbLN := gmbN.@"lock"`,
`gmbCN := gmbN.@"claim"`. An instance has a _bytes mask_ `gmb_bmask γ` (disjoint from
`gmbN`, recorded in `gmb_inv`). The b-side gains `GmbOut s κ lz` (lazy-capable lend, storing
`£3`) and `GmbPend s κ γc γp` (pending lazy lend). A pending lend lives in a claim invariant
(`inv gmbCN`) holding the b fragment and the payload (`▷ Q`, its settle law at the bytes mask,
the dead token, `£3`); while it is settled the settler holds the lock token (from
`inv gmbLN`) and leaves it in the claim invariant; the settled permission and residue are
deposited there (with a credit) for the lender.
```
Lemma gmb_create E d s t : c s t ={E}=∗ ∃ γ, ⌜gmb_depth γ = d ∧ gmb_bmask γ = ∅⌝ ∗ gmb_inv γ ∗ gmb_a γ s ∗ gmb_b γ t.
Lemma gmb_create_mask E d EB s t : EB ## ↑gmbN →
  c s t ={E}=∗ ∃ γ, ⌜gmb_depth γ = d ∧ gmb_bmask γ = EB⌝ ∗ gmb_inv γ ∗ gmb_a γ s ∗ gmb_b γ t.
Lemma gmb_move E γ s : ↑Nllft ∪ ↑gmbN ∪ gmb_bmask γ ⊆ E →
  gmb_inv γ -∗ £ (1 + gmb_depth γ) -∗ gmb_a γ s ={E}=∗ ∃ t, c s t ∗ (∀ s', c s' t ={E}=∗ gmb_a γ s').
  (* a pending lend is settled first: the mover forces the payload *)
Lemma gmb_lend_start_lazy E γ κ s t n : ↑Nllft ⊆ E → n ≤ gmb_depth γ →
  llft_ctx -∗ gmb_inv γ -∗ (@[κ] &&{↑NllftG; n}&&> gmb_a γ s) -∗ £ n -∗ £ 3 -∗
  special_open κ -∗ gmb_b γ t ={E}=∗ c s t ∗ gmb_lent_lz γ s κ.
Lemma gmb_lend_stop_lazy γ κ s (Q : iProp Σ) (R : T → iProp Σ) :
  gmb_inv γ -∗ gmb_lent_lz γ s κ -∗ ▷ Q -∗ gmb_bdead κ -∗
  (Q -∗ gmb_bdead κ ={gmb_bmask γ}=∗ ∃ t, c s t ∗ R t) ={↑NllftUsr ∪ ↑NllftUsr2}=∗ gmb_claim γ R ∗ special_open κ.
Lemma gmb_claim_take E γ R : ↑NllftUsr ∪ ↑NllftUsr2 ∪ ↑gmbN ∪ gmb_bmask γ ⊆ E →
  gmb_inv γ -∗ gmb_claim γ R ={E}=∗ ∃ t, gmb_b γ t ∗ R t.
Definition gmb_b_uniq γ R := (∃ t, gmb_b γ t ∗ R t) ∨ gmb_claim γ R.     Notation gmb_b_shr := gmb_b.
Lemma gmb_b_uniq_settle E γ R : (mask as gmb_claim_take) → gmb_inv γ -∗ gmb_b_uniq γ R ={E}=∗ ∃ t, gmb_b_shr γ t ∗ R t.
Lemma gmb_lend_guarded_lazy E G γ κ s n Q R : Timeless G → ↑Nllft ∪ ↑gmbN ∪ gmb_bmask γ ⊆ E → n ≤ gmb_depth γ →
  llft_ctx -∗ gmb_inv γ -∗ (@[κ] &&{↑NllftG; n}&&> gmb_a γ s) -∗ £ n -∗ £ 1 -∗ £ 3 -∗
  &{κ} (gmb_b_uniq γ R) -∗ (G &&{↑NllftG}&&> @[κ]) -∗ G -∗ (∀ t, R t -∗ c s t ={E}=∗ ▷ Q) -∗
  □ (Q -∗ gmb_bdead κ ={gmb_bmask γ}=∗ ∃ t, c s t ∗ R t) ={E}=∗ &{κ} Q ∗ G.
```
`guarded_bor_proph.v`: `gmb_lend_proph_map_lazy` (as `gmb_lend_proph_map`, with `£ 3`; the
way back gets `gmb_bdead κ` and returns `∃ QS R, ▷ QS ∗ (QS -∗ gmb_bdead κ ={gmb_bmask γ}=∗
∃ t', c s t' ∗ R t') ∗ (gmb_claim c γ R -∗ ▷ ∃ x', P x' (λ π, fπ (π ζ)))`). The eager (L3)/(L3p)
statements are unchanged. Tests: `test_lazy_lend_claim`, `test_lazy_lend_abandoned` (the owner
forces and moves), `test_proph_lazy_lend_abandoned`; the old tests use masks with `↑gmbN`.

In the typing layer: `lazyE := ↑Nllft ∪ ↑prophN ∪ ↑uniqN ∪ ↑gmbN` (so the ghost layer can take
the lock; `lazyB ## ↑gmbN`). The masks of `ty_share` (type record) and of the resolution
interfaces (`↑Nllft ∪ ↑prophN ∪ ↑timeN ∪ ↑uniqN ⊆ F`, in type.v, type_context.v,
place_resolve.v, place_puniq.v, uniq_util.v) become `↑Nllft ∪ ↑prophN ∪ ↑uniqN ∪ ↑gmbN`
(`timeN ⊆ Nllft`; the 5-fold union is beyond `solve_ndisj`'s depth). The explicit resolution
masks of place_write.v and place_memcpy.v exclude `gmbN` too.

Deviations:
- The settle lock is `inv gmbLN` (a token), but the pending payload is in a per-lend claim
  invariant in `gmbCN` (not in `other_inv`): the lender's claim is that invariant, so it needs
  no agreement on its residue `R`. The lock token is the placeholder of the payload while it
  is being forced.
- `£3` (not `£2`) are stored: two for the laters of the payload, one for the deposited residue.
- `gmb_b_uniq` is indexed by the residue `R` (a claim cannot carry `t`, audit Q5.4);
  `gmb_b_shr` is `gmb_b`.
- `gmb_create` also states `gmb_bmask γ = ∅`; `gmb_move` needs `↑gmbN ∪ gmb_bmask γ` in its mask.

### Step 4: (L3p) for `&uniq` bodies

`typing/gmb_uniq.v` (abstract `c : loc → FValue → iProp`, abstract permission and contents
types):
```
Lemma gmb_lend_uniq {𝔄p 𝔄} (pty: type 𝔄p) (ty: type 𝔄) (fv: ~~𝔄 → ~~𝔄p) (fp: 𝔄 → 𝔄p)
    (fvp: FValue) γ (l lp: loc) (y: ~~𝔄) ξi d g idx κ tid E G :
  Timeless G → Inj eq eq fp → (∀ y π, vπ (fv y) π = fp (vπ y π)) →
  lazyE ⊆ E → gmb_bmask γ = lazyB →
  (∀ x fv0, ty.(ty_fval) x = Some fv0 → c l fv0 ⊢ cbytes ty x l) →
  (∀ fv0, fbytes ty l fv0 ⊢ c l fv0) →
  (∀ v, pty.(ty_fval) v = Some fvp) → (∀ v, cbytes pty v lp ⊣⊢ True) →
  (∀ y' d' g', ty_gho_own pty (fv y') d' g' tid ⊢ |={lazyE}=>
     ∃ fv0, ⌜ty.(ty_fval) y' = Some fv0⌝ ∗ gmb_b γ fv0 ∗ ty_gho_own ty y' d' g' tid) →
  (∀ y' d' g' fv0, ty.(ty_fval) y' = Some fv0 →
     gmb_b γ fv0 ∗ ty_gho_own ty y' d' g' tid ⊢ ty_gho_own pty (fv y') d' g' tid) →
  llft_ctx -∗ proph_ctx -∗ uniq_ctx -∗ gmb_inv c γ -∗
  (@[κ] &&{↑NllftG}&&> gmb_a γ l) -∗ κ ⊑ ty_lft pty -∗ ty_lft pty ⊑ ty_lft ty -∗
  (G &&{↑NllftG}&&> @[κ]) -∗ G -∗ £ 4 -∗
  uniq_body pty (fv y) ξi d g idx κ tid lp ={E}=∗ ∃ ζi ζidx,
    ⟨π, (π (uniq_prvar (fv y) ξi)).1 = fp ((π (uniq_prvar y ζi)).1)⟩ ∗
    uniq_body ty y ζi d g ζidx κ tid l ∗ G.
```
The new body is fresh with pattern lifetime `κ`. Its final body is stored lazily (settle law:
`leaf_contents_unblock` with `[†κ]` from the dead token, then `fbytes ⊢ c`); the old body is
given back blocked at `κ` (`κ ⊑ κp_old`), and its lazy ghost update takes the claim and
rebuilds the permission's ownership from the residue. (The permission's ownership may hold a
`gmb_b_uniq`: the forward hypothesis is a `lazyE` update, which can settle it.)
Test (`typing/gmb_uniq_tests.v`, toy instance `c l fv := fbytes ty l fv`):
`test_gmb_uniq_abandoned` — a permission borrow from `alloc_uniq_body`, the lend, the new
borrow dropped, `κ` ended; the owner moves (`gmb_move` forces the stored bytes).

Deviations: the value map is a function `fv` with its prophecy `fp` (as
`uniq_body_transform_gen`); the share guard is at step-index 0.

### For phase 3/4

- The typing instance of phase 4 has to discharge the interface of `gmb_lend_uniq`: `c` vs.
  `fbytes`, the zero-size permission (`cell_points_to`), and its ownership predicate as
  `gmb_b γ (ty_fval x) ∗ ty_gho_own ty x` (or a `gmb_b_uniq`). Instances used with `&uniq`
  must be created with bytes mask `lazyB` (`gmb_create_mask`).
- Typed moves of `pcell` need `↑gmbN` (they have `⊤`).
