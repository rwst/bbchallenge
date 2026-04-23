# ShiftOv6 — Progress log

TM: `1RB0LC_1LC0RD_1LF1LA_1LB1RE_1RB1LE_---0LE`

Aim: find and (eventually) prove macro rules.  Halt/nonhalt is **not**
the target.

## Transition table

|   | 0   | 1   |
|---|-----|-----|
| A | 1RB | 0LC |
| B | 1LC | 0RD |
| C | 1LF | 1LA |
| D | 1LB | 1RE |
| E | 1RB | 1LE |
| F | --- | 0LE |

Halt condition: `F,0 → ---`.  F reachable only from `C,0 → 1LF`, so
halting requires `C` to fire on a `0` and the cell to its left to
also be `0`.

## 2026-04-23

### Simulator (`sim.py`, `explore.py`, `patterns.py`)

- `sim.py`: direct-execution simulator with tape array; supports
  `trace`, `evt`, `blocks`, `scan` commands.
- `explore.py`: left/right blank-boundary event traces.
- `patterns.py`: state-run-length and local-triple frequency summary.

### Observed dynamics

Dominant 3-step cycle `E → B → D → E` (≈ 16 737 fires per 100 k
steps).  E-runs of length 3 are the modal run, corresponding to the
"E sweeps left over exactly two 1s then fires" pattern.

**E-right-blank events** (blocks read L-to-R, rightmost is always 1):

```
step     6 dt=    6  blocks=[1, 1]
step    26 dt=   20  blocks=[2, 2, 1]
step    76 dt=   50  blocks=[6, 2, 1]
step   190 dt=  114  blocks=[2, 10, 2, 1]
step   752 dt=  562  blocks=[2, 25, 2, 1]
step 18240 dt=17488  blocks=[2, 124, 4, 2, 1]
```

These events are rare; between consecutive events the machine performs
a non-trivial restructure that also grows the active region.  Rate of
growth is super-linear, consistent with a "shift-overflow counter"
character.

### The local 5-step bump (empirically identified, steps 48–76)

With tape shape `… 0 1^K 0 1^L [E] 0 1^M 0 blank∞` and head on the
**2nd** cell of the middle block (state E, head symbol 1), the machine
performs a cycle:

```
[K, L, M]  →(5 steps)→  [K+1, L-1, M]
```

Iterated `L-1` times, the middle block is reduced to size 1 with head
now on the 0-separator between blocks 2 and 3.  A 3-step "finish"
(E,0→B,1→D,1→E) at that point, when `M = 2`, rearranges to blocks
`[K+L-1, 2, 1]` with E at the right blank.

Total cycle: `5(L-1) + 3 = 5L − 2` steps.  For the observed
[K, L, M] = [1, 6, 2] at step 48, predicted `28` = observed `76 − 48
= 28`. ✓

This family covers `M = 2`; the finish is different at other `M`.

### Lean file `machine.lean`

- TM definition via `tm!` macro: ✓
- Per-transition simp lemmas `tr_A0` … `tr_F1`: ✓
- **Proven**: `E_sweep` (inductive shift-lemma, E-left-sweep over `ones k`).
- **Proven**: `BDE_cycle3` (local 3-step rewrite `[E,0] 1 1 X` →
  `1 0 1 [E,X]`).
- **Proven**: `init_to_Init_Config_6` (by `decide`, blank → step 6
  Config-level) and stream lift `init_to_SInit_6`.
- **Proven**: `bump5` — inner 5-step cycle
  `M_Config L K (j+1) M → M_Config L (K+1) j M`.  Direct simp.
- **Proven**: `bump5_term` — terminal 5-step cycle at block 2 size 2
  `M_Config L K 0 M → S_Config L (K+1) M`.  Direct simp.
- **Proven**: `bump5_iter` — iterate the inner bump `n` times,
  transferring `n` ones from block 2 to block 1 in `5n` steps.
- **Proven**: `bump5_iter_term` — iterate all the way + terminal:
  `M_Config L K n M → S_Config L (K+n+1) M` in `5(n+1)` steps.
- Placeholder existence theorem `finish3_M2`.

Build: `lake build ShiftOv6` succeeds with **no sorries**.

### The clean parameterization

Three configs cover the `M = 2` family fully:

* `M_Config L K j M`: state E, head = 1 on the 2nd cell from left of
  block 2.  Block 2 has size `j + 2`.  Tape reads
  `L' 0 1^K 0 1 [E]1^(j+1) 0 1^M 0 blank∞`.

* `S_Config L K M`: state E, head = 0 on the 0-separator between
  a size-1 block 2 and block 3.  Tape reads
  `L' 0 1^K 0 1 [E]1^M 0 blank∞`.

* `R_Config L K`: state E, head = 0 at the right blank with blocks
  `[K, 2, 1]`.  Tape reads `L' 0 1^K 0 1 1 0 1 [E=0] blank∞`.

### Full proven macro chain (no sorries)

```
         5n steps             5 steps             3 steps
M_Config ────────→ M_Config ────────→ S_Config ────────→ R_Config
L K (j+n) M        L (K+n) j M       L (K+n+1) M        L (K+n+1)
   │                                                        │
   └─────────── macro_to_R: 5(n+1) + 3 steps ───────────────┘
                (parameters: K, n; requires M = 2)
```

And the entry bridge:

```
              48 steps                       28 steps
sinitConfig ───────────→ M_Config blank∞ 1 4 2 ──────────→ R_Config blank∞ 6
(blank tape)             (step 48, blocks [1, 6, 2])    (step 76, blocks [6, 2, 1])
    │                                                       │
    └─────────── init_to_R_Config_6: 76 steps ──────────────┘
```

### 2026-04-23 session 2

- Refactored `M_Config` — earlier version had a buggy `head` field at
  `L_blk = 1`.  New design uses separate `M_Config`/`S_Config` keyed
  to "head in block" vs "head on separator".
- Proved `bump5` (inner 5-step cycle) and `bump5_term` (terminal
  5-step cycle) as direct `simp` lemmas.
- Proved `bump5_iter` by induction on `n`, `bump5_iter_term` by
  composition.
- Added `R_Config` (right-blank E-turnaround).  Proved `finish3_M2`
  (3-step S → R transition) by direct simp.
- Proved `macro_to_R` composing the full macro: `M_Config L K n 2` →
  `R_Config L (K+n+1)` in `5(n+1)+3` steps.
- Identified step 48 as `M_Config blank∞ 1 4 2` by direct simulation.
  Proved `init_to_M_Config` (blank → step 48 M_Config) by `decide` +
  stream lift.
- Proved `init_to_R_Config_6` (blank → step 76 `R_Config blank∞ 6` =
  blocks `[6, 2, 1]`) by composition.
- Verifies the observed dt=28 between step 48 and step 76: matches
  `5(4+1)+3 = 28`.  ✓

### 2026-04-23 session 3

Extended the concrete chain by two more E-turnarounds via `decide`:

- `R4_Config L K` — 4-block right-blank E-turnaround (blocks
  `[2, K, 2, 1]`).  Tape `L' 0 1^2 0 1^K 0 1^2 0 1 [E=0] blank∞`.
- `init_to_R4_Config_10` — blank → step 190 (blocks `[2, 10, 2, 1]`)
  by `decide` with `maxRecDepth 3000`.
- `R_Config_6_to_R4_Config_10` — step 76 → step 190 in 114 steps;
  specific to `L = blank∞` (head enters L territory by 5 cells).
- `init_to_R4_Config_25` — blank → step 752 (blocks `[2, 25, 2, 1]`)
  by `decide` with `maxRecDepth 8000`.
- `R4_Config_10_to_R4_Config_25` — step 190 → step 752 in 562 steps;
  specific to `L = blank∞`.

### Complete chain (all proven, no sorries)

```
  0 ──48──→ M_Config blank∞ 1 4 2   (step 48, blocks [1, 6, 2])
           │
           │ macro_to_R at (K=1, n=4): 5·5+3 = 28 steps
           ↓
 76 ────── R_Config  blank∞ 6         (step 76, blocks [6, 2, 1])
           │
           │ restructure: 114 steps (via decide, L = blank∞ only)
           ↓
190 ────── R4_Config blank∞ 10        (step 190, blocks [2, 10, 2, 1])
           │
           │ restructure: 562 steps (via decide, L = blank∞ only)
           ↓
752 ────── R4_Config blank∞ 25        (step 752, blocks [2, 25, 2, 1])
```

Beyond step 752 the next E-turnaround is at step 18240 (dt 17488,
blocks `[2, 124, 4, 2, 1]` — 5 blocks).  562-step `decide` works at
`maxRecDepth 8000`; 17488 steps will not scale via `decide`.

### 2026-04-23 session 4 (TODO 3: search for local carry rules)

Empirically hunted for `carry_22_5`-style local macro rules using
`carry_search.py`:

- `scanK` sweeps over `R4_Config blank∞ K` for `K = 2..34`, measuring
  the step count and block structure to the next E-right-blank event.
  Observed dt sequence: `72, 114, 72, 114, 196, 322, 196, 322, 562,
  962, 562, 962, 1628, 2660, …` — grows super-linearly, no simple
  closed form.  Outputs alternate between 3-block `[?, 2, 1]` and
  4/5-block `[?, ?, 2, 1]` / `[?, ?, 4, 2, 1]` depending on `K mod 4`
  (or similar parity).

- `locality` tests the same K-config with **different left prefixes**
  (blank, mixed, ones-only, zebra).  Results across three cases
  (`K = 2`, `K = 4`, `K = 10`, and the cleaner `[2, 4, 2, 1]`
  context): every non-trivial transformation is **L-dependent** —
  both the step count and the output blocks change drastically with
  `L`.  Notably, `ones-only` L's *halt* quickly, confirming the head
  reaches deep into `L` and reads its contents.

- **Weak right-locality observation**: when the machine doesn't halt,
  the rightmost 3 blocks of the input are preserved as the rightmost
  3 of the output (e.g. `[…, 4, 2, 1]` → `[…, 4, 2, 1]`).  The "…"
  portion transforms unpredictably.  This is a weaker property than
  full locality and not obviously useful as a Lean theorem — the
  step count `dt` still depends on "…".

**Conclusion on TODO 3**: no Chaotic6-style `carry_*` local rules
exist for this TM beyond the `bump5` family already proven.  The
dynamics are genuinely non-local past the R_Config regime.

Scripts: `carry_search.py` (`scanK`, `locality`, `inter` commands).

## TODOs

1. **Generalize the 114-step restructure to abstract `L`** — the head
   excursion is ≤ 16 cells; if we can characterise the prefix it
   reads (≤ 5 cells into `L`), we could state a local rule `R_Config
   (prefix *> L) 6 → R4_Config L' 10` for any tail `L`.  Worth
   investigating whether those 5 cells are always read as blank (i.e.
   whether the restructure truly only depends on the existence of
   enough blank left-padding).

2. **Classify the super-linear restructure family.**  Empirical dt
   after `R4_Config ... 10`: `562, 17488, …` — not obviously
   polynomial.  Likely a chaotic regime needing schema-based analysis.

3. **`R_Config` at arbitrary `M ≠ 2`**: analogue of Chaotic6's
   `carry_22`, `swap_25`, etc. Local simp lemmas if they exist.

4. **A more abstract version of `macro_to_R`** with `M ≠ 2` would
   subsume most of the current concrete-only theorems.
