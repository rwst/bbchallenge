# Era-discovery simulator: detailed implementation plans

Five strategies for accelerating era-boundary discovery, ordered from
lowest effort / lowest payoff to highest. Each section contains a goal,
prerequisites, concrete implementation steps, validation criteria, risk
mitigations, and a time estimate.

Companion to `invariant_strategy.md`. Baseline: current `macro_sim.py`
reaches era ~221 in ~1 B raw steps (~minute on a single core).

## Plan 1 — PyPy drop-in

### Goal
Run the existing `macro_sim.py` unchanged under PyPy3's tracing JIT.
Expected speedup: 10–30×. Reach: era ~10⁴ in 1 hour CPU.

### Prerequisites
- PyPy 3.10+ installed (`pypy3 --version`).
- The codebase already runs in pure Python with no compiled extensions
  except `dataclasses` (PyPy-supported).

### Steps
1. **Install PyPy** (e.g., `apt install pypy3 pypy3-dev` on Debian, or
   `brew install pypy3` on macOS, or via portable archive).
2. **Smoke test**: `pypy3 macro_sim.py -n 10000`. Expect identical JSON
   output to CPython.
3. **Benchmark** (`time` wrapper):
   - `time python3 macro_sim.py -n 100000`
   - `time pypy3 macro_sim.py -n 100000`
   Record wall-clock and confirm speedup ≥ 10×.
4. **Hot-path inspection**: PyPy's `--jit` flag with `pypylog` to
   verify `macro_step` is being JIT'd. Common warm-up cliffs are loops
   that take only a few iterations; here we have ≥10⁵ iterations so
   warmup is not an issue.
5. **Tune (if speedup < 10×)**:
   - Inline `Macro` dataclass field accesses (PyPy specializes these
     after warmup but if we see overhead, replace `@dataclass` with a
     plain `class` and `__slots__`).
   - Replace `Counter` with plain `dict` if hot.
   - Confirm no `eval`/`exec`/`getattr`-by-string in hot path.
6. **Reach test**: `pypy3 macro_sim.py -n 5000000` should run in
   minutes and reach era ~500–800.

### Validation
Bit-exact JSON output for `-n 10000`, `-n 100000`, `-n 1000000` between
CPython and PyPy. `diff <(python3 …) <(pypy3 …)` should be empty.

### Risks
- **None to soundness** — same Python source.
- **Speedup miss**: occasionally PyPy doesn't JIT due to highly variable
  control flow. If observed, pivot to Plan 2.

### Time estimate
2–4 hours including benchmarking, with most time in step 5 if needed.

### Done when
PyPy reaches era 1000 in < 10 minutes wall-clock with identical output
to CPython.

---

## Plan 2 — Cython compilation of the hot loop

### Goal
Compile `macro_step` and the dispatch loop into a C extension. Expected
speedup: 50–200× over CPython. Reach: era ~10⁵ in 1 hour.

### Prerequisites
- Cython 3.x (`pip install cython`).
- A C compiler (`gcc` or `clang`).
- Plan 1 done (so we have a benchmarking baseline).

### Steps
1. **Profile** with cProfile under CPython to confirm `macro_step` and
   the per-step overhead dominate (expected: ≥ 70 % of runtime).
2. **Extract the hot core** into `macro_core.pyx`:
   - `cdef class Macro`: replace `@dataclass` with `cdef public int kind`
     (`0`=M, `1`=M0), `cdef public long long c`, and `cdef public list L, R`.
     (Lists stay Python lists initially; revisit in step 7 if hot.)
   - `cpdef tuple macro_step(Macro m)` returning `(result, steps, rule)`,
     where `result` is `Macro` or sentinel int.
3. **Sentinel encoding**: replace string sentinels (`'__AXIOM_R1__'`,
   `'__HALT__'`) with small integer codes (`-1`, `-2`, `-3`, `-4`) so
   the dispatch returns a typed `(int code, long long steps, str rule)`.
4. **Compile**: `cythonize -i macro_core.pyx`. Verify the `.so` builds.
5. **Wire into macro_sim.py**: replace the in-file `macro_step` import
   with `from macro_core import macro_step`. Keep the outer
   loop / I/O in pure Python.
6. **Benchmark**: target ≥ 50× over CPython for `-n 100000`.
7. **Optional further tuning** (if < 50×):
   - Replace `m.L` and `m.R` with `cdef vector[long long]` (requires
     `# distutils: language = c++` directive).
   - Annotate loop variables with `cdef int i, j` etc.
   - Use `boundscheck(False)` and `wraparound(False)` decorators.
8. **Bigint guard**: at each `macro_step` exit point, assert
   `m.L[0] < (1 << 62)` (and same for `m.R[0]`). Empirically values
   stay small for ~10⁵ eras, but we want a tripwire if reached.

### Validation
Diff JSON output against PyPy (Plan 1) for `-n 100000` and `-n 1000000`.
The bigint guard should not fire under either run.

### Risks
- **`long long` overflow** at deep eras (~10⁵+). Mitigation: bigint
  guard catches it before silent corruption; pivot to Plan 3 or 4.
- **Cython API drift**: pin `cython>=3.0,<4`.
- **Build issues**: keep a `Makefile` target that rebuilds the `.pyx`
  from scratch.

### Time estimate
1–2 days, mostly in steps 2–5.

### Done when
Cython simulator runs `-n 1000000` in < 1 minute wall-clock, identical
output to PyPy / CPython on all checked sample sizes.

---

## Plan 3 — Native Rust port

### Goal
Standalone Rust binary `era-sim` reproducing `macro_sim.py`'s logic with
fixed-size `u64` fields. Expected speedup: 200–1000×. Reach: era ~5×10⁵
in 1 hour.

### Prerequisites
- Rust 1.75+ via `rustup`.
- Plan 2 done (Cython gives us a ground truth fast enough to cross-check
  Rust against millions of macro steps).

### Steps
1. **Bootstrap**:
   - `cargo new era-sim --bin`
   - In `Cargo.toml`: depend on `smallvec`, `serde_json`, `clap`.

2. **Define types** in `src/macro_state.rs`:
   ```rust
   #[derive(Clone, Debug, PartialEq)]
   pub enum Kind { M, M0 }

   #[derive(Clone, Debug, PartialEq)]
   pub struct Macro {
       pub kind: Kind,
       pub c: u64,
       pub l: SmallVec<[u64; 16]>,
       pub r: SmallVec<[u64; 16]>,
   }
   ```
   `SmallVec<[_; 16]>` is inline up to 16 elements (covers ~all
   observed L/R lengths through era 10⁶), spills to heap beyond.

3. **Port `macro_step`** to `src/dispatch.rs`. Use a `match` over
   `(kind, c, l.first(), r.first(), …)` patterns. Return enum:
   ```rust
   pub enum StepResult {
       Macro { next: Macro, steps: u64, rule: &'static str },
       Axiom(AxiomKind),
       Halt,
       Stuck,
   }
   ```

4. **Port `bridge_axiom`** to `src/bridge.rs`. Use a flat byte array
   for the tape (size 4 KB sliding window, with the head re-centered
   when within 1 KB of either end). Verified: max bridge length seen
   is ~7 K raw steps, so 4 KB window suffices with margin.

5. **Port `classify_axiom`** as a pure function on `&Macro`.

6. **Main loop** in `src/main.rs`: matches `macro_sim.py`'s CLI
   (`-n`, `-l`, `--verbose-period`). Outputs the same JSON summary.

7. **Logging**: per-axiom occurrence dumped to stdout/JSONL.

8. **Cross-validation** (most important step):
   - Build a Python wrapper that reads era-sim's JSONL output and
     compares macro-step-by-macro-step against `macro_sim.py` for
     the first 100 000 macro steps.
   - Each macro step's `(rule, steps, output Macro)` must match
     exactly.
   - Run this test in CI (a `tests/cross_validate.sh` script).

9. **Benchmark**:
   - `cargo build --release && time ./target/release/era-sim -n 1000000`
   - Target: ≥ 200× over CPython baseline.

10. **Overflow guard**: every place where we compute `a + 1`, `c + 4`,
    etc., use `checked_add` and panic on overflow. This is the
    tripwire for u64 capacity (~era 10⁶+).

### Validation
- Cross-validation against Cython (Plan 2) for first 10⁵ macro steps,
  then against PyPy (Plan 1) for the next 10⁶ macro steps (slower
  ground truth but still reachable).
- Property test: `proptest` crate generating random `MacroInvariant`-
  satisfying configs and verifying `macro_step` matches Python on
  ≥ 10⁴ samples.

### Risks
- **Logic discrepancy**: subtle differences in axiom-classification
  edge cases. Mitigation: extensive cross-validation (step 8) catches
  any divergence within 100 macro steps.
- **u64 overflow**: pinned by `checked_add`. When it fires, switch to
  Plan 4's GMP integration.
- **Rust learning curve** (if implementer is new to Rust): allocate
  extra time in step 3.

### Time estimate
1–2 weeks. Steps 2–6 are 3–4 days; step 8 is 2 days; debugging via
cross-validation typically 2–3 days.

### Done when
- `era-sim -n 10000000` completes in ~2 minutes.
- Cross-validation passes for 10⁶ macro steps.
- `checked_add` doesn't fire through era 10⁵.

---

## Plan 4 — Closed-form era step + GMP big integers

### Goal
Skip individual macro steps; iterate at era granularity. Each invocation
of the era function `T` advances the orbit by one full era using
algebraic shortcuts. Combined with arbitrary-precision integers for L/R
values that can outgrow u64. Expected speedup: 10⁴–10⁶× over Python.
Reach: era ~10⁷ in 1 hour.

### Prerequisites
- Plan 3 done (we need the Rust port as ground truth for correctness).
- Hand-derived case analysis of within-era macro dispatch sequences
  (this is the math content; see step 1).

### Steps
1. **Derive within-era closed forms** (the hardest step; fully manual):

   For each era-start shape, trace the macro dispatch through to the
   next era boundary (the next `era_and_sweep` or `era_and_sweep_solo`
   firing). Express the resulting state as a closed-form function of
   the era-start parameters.

   Reference the trace pattern from era 0 (verified):
   - Start: `M[1] 4 [1]` (cursor 4, L=[1], R=[1]).
   - sweep: `M[1] 4 [1] → M[2] 2 [2]` (15 raw steps).
   - sweep_to_zero: `M[2] 2 [2] → M0[3] [3]` (11 raw steps).
   - zero_bounce_to_zero: `M0[3] [3] → M0[7] [1]` (12 raw steps).
   - era_and_sweep_solo: `M0[7] [1] → M[1] 10 [1]` (39 raw steps).
   - Total: 77 raw, 4 macro steps.

   Generalize for shape `M[a] c [b]` with `c ≥ 4`, `a, b ≥ 1`:
   - `(c−2)/2` sweeps to reach `M[a + (c−2)/2] 2 [b + (c−2)/2]`.
   - sweep_to_zero: `→ M0[a + (c−2)/2 + 1] [b + (c−2)/2 + 1]`.
   - Then case-split on `b + (c−2)/2 + 1 mod something` for the
     zero_bounce variants.
   - Eventually `era_and_sweep` or `era_and_sweep_solo` ends the era.

   Repeat for shapes with longer L or R; each case yields a closed-form
   `T_shape : EraStart → EraEnd`.

   **Document each case in `era_step_derivation.md`** with the trace
   and resulting formula.

2. **Implement `T` in Rust** as `src/era_step.rs`:
   ```rust
   pub fn era_step(start: &Macro) -> EraResult { … }
   ```
   Internally a `match` over the era-start shape, dispatching to one
   of the closed-form cases derived in step 1.

3. **Bigint integration**:
   - Add `num-bigint = "0.4"` to `Cargo.toml`.
   - Replace `u64` with `BigUint` for L/R element type, behind a
     trait `RunLength`. Use `u64` in tests and `BigUint` in deep
     era runs.
   - Or: stay u64 but use `u128` for arithmetic, falling back to
     `BigUint` when intermediate computations exceed u128. (Simpler
     but capped at ~era 10⁷.)

4. **Within-era axiom handling**:
   - R2 / R3-narrow are already proved as bridges of constant raw-
     step count. The era function must still advance the macro state
     correctly when these fire. Handle them as additional cases in
     `T`.

5. **Cross-validation against Plan 3**:
   - Run plan 3's `era-sim` for 10⁵ eras. Snapshot every era-end
     state.
   - Run plan 4's `era-step` for the same 10⁵ eras. Compare snapshots.
   - All must match exactly.

6. **Benchmark**:
   - Run plan 4 for 10⁷ eras. Measure wall-clock.
   - Target: ≥ 10⁴× over Python `macro_sim.py` measured at common
     era count.

7. **Output format**: JSONL with one record per era end:
   `{ "era": n, "raw_steps": k, "macro": "M[…] c […]" }`.

### Validation
- Cross-validation against `era-sim` for 10⁵ eras (must be exact).
- Sanity: era 0 end = `M[1] 10 [1]`; era 1 end = `M[10] 3 [1]`.
- Spot-check at era 100, era 1000 via Plan 3 (run plan 3 to that era,
  compare).

### Risks
- **Case-analysis incompleteness**: a within-era pattern not covered
  by step 1's derivation. Mitigation: when `T` encounters an unknown
  shape, fall back to plan 3's `era-sim` (single-era macro-step
  iteration). Log every fallback for later derivation.
- **Multi-bounce cascade complexity**: deep multi-bounces within an
  era can produce many sub-cases. Mitigation: derive iteratively,
  starting from simple shapes and adding cases as the simulator hits
  fallback paths.
- **Bigint overhead**: `BigUint` is ~10× slower than `u64`. The
  closed-form era step still wins because it skips so many steps,
  but factor this into the speedup estimate.

### Time estimate
2–4 weeks. Most time (1.5–3 weeks) is step 1's derivation. The Rust
implementation is 3–5 days; cross-validation 2–3 days.

### Done when
- `era-step -n 1000000` completes in < 10 minutes.
- Cross-validation matches `era-sim` for 10⁵ eras.
- `era_step_derivation.md` documents every within-era shape.

---

## Plan 5 — Mathematical recurrence (no simulation at all)

### Goal
Discover an arithmetic recurrence `cfg_{n+1} = R(cfg_n)` for some
embedding of `EraConfig` into ℕᵏ (or ℤ₂ᵏ, or a polynomial ring). Once
known, era *N* is a few microseconds of arithmetic regardless of *N*.
Reach: era 10⁹–10¹².

### Prerequisites
- Plan 4 done. Need ≥ 10⁶ era-end snapshots to fit and verify.
- Background reading: Mxdys/ValidS work on Antihydra; LucysMoonlight
  invariant; Pillai TM analysis. These are recurrence-based.

### Steps
1. **Generate data**: run Plan 4 to era 10⁶, save full sequence of
   `(era_count, |L|, sum L, head L, last L, |R|, …)` records.

2. **Inspect for low-order recurrence** (numerical experiments):
   a. Plot `head L_n`, `sum L_n`, `|L_n|` vs n. Look for power
      laws / linear / log behavior.
   b. Try `head L_{n+1} = a · head L_n + b` for small a, b.
   c. Try `L_{n+1}[k] = f(L_n[k], L_n[k−1])` for each position k.
   d. Try `sum L_n mod 2^k` for various k.

3. **Try 2-adic embedding**:
   a. Encode L = `[a_1, a_2, …, a_k]` as a 2-adic integer
      `x = Σ_i a_i · 2^{s_i}` for some position scheme s_i.
   b. Check whether the era map preserves a 2-adic congruence
      `x_{n+1} ≡ φ(x_n) mod 2^k` for various k.
   c. If yes, hypothesize the full 2-adic recurrence.

4. **Try Collatz-like reduction**:
   a. The TM may simulate `f(x) = x/2 if even, (3x+1)/2 if odd` or a
      variant. Test by encoding L as a binary string and checking
      whether era step matches.

5. **Try linear recurrence over ℤ**:
   a. Construct matrix `M` such that `L_{n+1} = M · L_n + b` (treating
      L as a vector). Check via least-squares fit on the data.

6. **If a recurrence is found**:
   - Verify on ≥ 10⁶ data points (zero discrepancies).
   - Implement as `recurrence-iter.rs`: 50–100 lines of pure
     arithmetic.
   - Run to era 10⁹ and beyond.
   - Submit findings to `invariant_strategy.md` (this should provide
     the Option-2 invariant).

7. **If no recurrence is found**:
   - Documentation: write up the negative findings (which classes were
     ruled out, by which experiments).
   - Pivot back to Plan 4 + cascade approach for R1.

### Validation
- Recurrence must reproduce all ≥ 10⁶ data points exactly. Even one
  discrepancy means it's wrong.
- Once verified empirically, attempt to prove the recurrence
  preservation through a Lean theorem (this is the Option-2 closure
  for R1).

### Risks
- **Recurrence may not exist** in any tractable form. The TM is in
  the busy-beaver regime, and not every Mealy-Moore-decomposable TM
  has a clean recurrence.
- **Recurrence may exist but with period > 10⁶**: not detectable from
  10⁶ data points. Mitigation: extend Plan 4 to era 10⁷ if Plan 5's
  initial searches fail.
- **Discovery requires mathematical insight**: this is the only
  step in the plan that is not mechanical. Reserve time for
  exploration and accept that it might fail.

### Time estimate
- If recurrence is "obvious" once we have data: 1–2 weeks for
  discovery + verification.
- If recurrence is structural / 2-adic: 1–3 months including
  literature review.
- If no recurrence exists: 2–4 weeks before declaring failure and
  pivoting.

### Done when
Either:
- A recurrence verified on ≥ 10⁶ era-end states, with implementation
  reaching era 10⁹ in < 1 hour. Findings submitted as PR to
  `invariant_strategy.md` and (ideally) formalized in Lean to close
  R1.
- Or, a documented impossibility report ruling out a list of
  recurrence families, with the analysis preserved for future
  attempts.

---

## Recommended execution order

| Step | Build on | Yields |
|------|----------|--------|
| Plan 1 (PyPy) | nothing | era 10⁴ data + cheap baseline |
| Plan 2 (Cython) | Plan 1 baseline | era 10⁵ data |
| Plan 3 (Rust port) | Plan 2 ground truth | era 5×10⁵ data + bug-resistant simulator |
| Plan 4 (closed-form era) | Plan 3 ground truth + within-era derivation | era 10⁷ data + foundation for #5 |
| Plan 5 (recurrence) | Plan 4 data | closure of Option 2 / R1 closure / negative result |

Plans 1–3 are pure engineering and largely mechanical. Plan 4 is
mostly engineering with a math derivation step at the front. Plan 5 is
mostly math. The progression takes you from "drop-in interpreter" to
"hand the problem to the algebraists with millions of data points."

## What this gets us toward Option 2

Option 2 from `TACTIC_PLAN.md` (closing R1 via a 2-adic / algebraic
invariant) requires:
1. **Empirical evidence**: data from many eras to fit and verify a
   candidate invariant. Plans 1–4 provide this.
2. **Discovery**: identify the candidate invariant. Plan 5's analytical
   sub-steps.
3. **Verification**: prove it preserves under era steps. Once known,
   formalization in Lean uses the existing `OrbitReachable` framework.

Each plan in the chain enables the next; the bottleneck for closing
R1 via Option 2 is data, then insight, then formalization — in that
order.
