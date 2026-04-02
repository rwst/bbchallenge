# Macro Rules for TM 1RB---0RB0LA2RA_2LB2LA3RA4LB0LB

## Transition Table (2-state, 5-symbol)

       0     1     2     3     4
  A   1RB   ---   0RB   0LA   2RA
  B   2LB   2LA   3RA   4LB   0LB

Transition A,1 is undefined (halt).

## Tape Structure

After initialization, the tape has the form (physical L to R):

    0^inf  1 3  [binary cells in {2,3}]  [HEAD]  [ternary pairs]  2+  0^inf
           ~~~                                                     ~~
       terminator                                              padding

- **Terminator**: cells 1, 3 at the physical left edge of nonzero tape.
- **Binary region**: cells in {2,3} between the terminator and the head.
  Encoding: 2 = bit 0, 3 = bit 1. LSB is closest to the head.
- **Head**: at the boundary between binary and ternary regions.
- **Ternary region**: consecutive pairs of cells, each pair encoding one ternary digit.
  Encoding: pair (2,2) = digit 0, pair (0,2) = digit 1, pair (4,2) = digit 2.
  LSB pair is closest to the head.
- **Padding**: one or more cells of value 2 at the right edge (extends during RInc bounce).

In mxdys's reversed notation: `.22 (42|02|22)* (<A|B>) (2|3)* 31.`

## Canonical Configs

**CycleStart(bin, tern, pad)**:
State A, head reading symbol 2, at boundary between binary and ternary.

    left  = bin ++ [3, 1]          (binary cells LSB-first, then reversed terminator)
    head  = 2
    right = tern ++ replicate pad 2 (ternary pairs, then padding 2s)

where every cell in `bin` is 2 or 3, and `tern` is a concatenation of pairs
from {(2,2), (0,2), (4,2)}.

Observed at steps: 117, 155, 169, 173, 800, ...

## RInc (Right Increment)

Starts from CycleStart. The head sweeps right, alternating A,2->0RB and B,2->3RA,
converting ternary pairs 22->03. When it reaches the right padding/blank edge,
it bounces (B,0->2LB extending tape) and sweeps back left, converting 03->42
via B,3->4LB and B,0->2LB.

During the leftward sweep, the head crosses back into the binary region and
propagates a carry: B,3->4LB continues the carry through 1-bits, B,2->3RA
stops the carry by flipping a 0-bit to 1.

**Normal carry (binary has a 0-bit):**
Binary value increments by 1. No change to binary digit count.
After cleanup (A,4->2RA chain), returns to CycleStart with binary+1.

**Full carry (all binary bits are 1):**
Carry propagates through all binary bits and into the terminator.
B,3->4LB hits terminator cell 3, B,1->2LA hits terminator cell 1.
A,0->1RB at blank re-creates terminator one position left.
B,2->3RA and A,4->2RA cleanup.
Result: binary resets to all 0s with one additional digit, terminator shifts left.

After RInc, the ternary region is all (4,2) pairs (digit 2 = max value),
and one additional pair may have been created from the padding.

## LInc (Left Decrement of Ternary)

Immediately follows RInc (the machine is at CycleStart after RInc).
The head enters the ternary region: A,2->0RB then B reads the first ternary pair.

**Decrement of first (LSB) ternary digit:**
- If digit = 2 (pair 42): B,4->0LB, then bounce → converts to (0,2) = digit 1.
  (The LInc borrow doesn't propagate.)
- If digit = 1 (pair 02): B,0->2LB, B,2->3RA, eventually → converts to (2,2) = digit 0.
  (Simple decrement.)
- If digit = 0 (pair 22): borrow propagation, analogous to binary carry in RInc.

**Borrow propagation**: trailing 0-digits (22 pairs) get set to digit 2 (42 pairs),
and the first non-zero digit is decremented.

After LInc, returns to CycleStart with ternary value decremented by 1.

## Normal Cycle

One complete cycle = RInc + LInc:
- Binary counter increments by 1
- Ternary counter decrements by 1
- Step count is proportional to tape length (which grows slowly)
- Returns to CycleStart

This repeats until the ternary counter reaches 0 (all pairs are (2,2)).

## Overflow (Ternary = 0)

When the ternary counter is 0 and the next decrement would underflow,
a complex reset sequence occurs. In mxdys's terminology:

1. **LOv**: Adds a new zero-digit to the ternary counter.
2. **RRstS**: Consumes binary 1-bits, creating new ternary counter segments.
3. **RRst0**: Initializes the new ternary counter to all-2s (max).
4. **LRst**: Merges ternary counter segments.

Net effect of overflow:
- Ternary digit count increases (by 2 in even overflows, by 1 in odd overflows —
  based on observed pattern of alternating "immediate" and "extended" overflows).
- Binary counter is modified (may reset lower bits, grow digit count).
- Ternary counter is re-initialized near max value for the new digit count.

### Observed overflow data

    T_digits  B_value    step  delta_B
    --------  -------  ------  -------
           2        0      93
           3        1     117        1  (immediate)
           4       10     764        9  = 3^2
           5       11     800        1  (immediate)
           6      129    6635      118
           7      130    6685        1  (immediate)
           8     1425   59170     1295
           9     1426   59228        1  (immediate)

Pattern: overflows come in pairs. Odd-to-even T_digits transitions are "immediate"
(delta_B = 1). Even-to-odd transitions take many cycles (delta_B grows ~exponentially).

## Overflow Details

### Even overflow (pad=0 → pad=1)

When ternary is all-zero at pad=0, the overflow_cycle theorem applies:
- Input: `CycleStart bin (rep s2 (2*d)) 0` (d ternary digit pairs, all zero)
- Output: `CycleStart bin' (repPair s4 s2 d) 1` (d pairs of digit 2 = max)
- Steps: `6*d + 4`
- Binary is incremented by 1 (via carry_stop or overflow_carry)
- Ternary is re-initialized to all-max (3^d - 1)

The binary increment may be:
- **carry_stop**: flips lowest s2→s3, standard +1
- **overflow_carry**: all bits are s3 (value 2^d-1), wraps to rep s2 (d+1) (value 0),
  carry absorbed by terminator which shifts left. Binary grows by 1 digit.

### Odd overflow (pad=1 → pad=0)

When ternary is all-zero at pad=1, the head enters ternary, bounces, and
cascades left into the binary region. Two cases depending on the leading
binary bit:

**Case k=0** (bin starts with s2, i.e., binary value is even):
- The overflow_odd theorem applies
- Input: `CycleStart (s2 :: bin_rest) (rep s2 (2*d)) 1`
- Output: `CycleStart bin_rest (rep s2 (2*(d+2))) 0`
- The leading s2 is consumed (absorbed into new ternary)
- Ternary grows by 2 digit pairs (d → d+2), re-initialized to all-zero
- Binary shrinks by 1 cell
- Steps: `6*d + 9`

**Case k=1** (bin = s3 :: s2 :: bin_rest, exactly one leading s3):
- The overflow_odd_k1 theorem applies (PROVED)
- Input: `CycleStart (s3 :: s2 :: bin_rest) (rep s2 (2*d)) 1`
- Output: `CycleStart bin_rest (s0 :: s2 :: rep s2 (2*(d+1))) 1`
- The leading s3 and s2 are consumed, creating ternary digit 1 (pair s0,s2)
- Ternary grows by 2 pairs (d → d+2 total), first digit = 1, rest = 0
- pad stays at 1 (another odd overflow follows with the new nonzero ternary)
- Steps: `6*d + 10`
- Note: output has pad=1, so IsCanonical requires bin_rest.length ≥ 2

**Case k≥2** (bin = rep s3 (k+1) ++ s2 :: bin_rest, multiple leading s3s):
- After odd_overflow_cascade + k+1 A,s3→0LA steps, creates k+1 consecutive
  s0 cells on the right: rep s0 (k+1) ++ rep s2 (2*(d+2))
- For k≥2 this is NOT valid ternary (pairs would be (s0,s0) etc.)
- The machine continues with complex behavior (A,s2→0RB into the s0 region...)
- Needs separate analysis; not yet proved

### Parity of binary at odd overflow

The leading bit of binary at odd overflow is NOT fixed — both k=0 and k=1
occur in practice:

    T_dig  B_val  binOdd  case
        3      1    true   k≥1 (s3 leading)
        5     11    true   k≥1 (s3 leading)
        7    130   false   k=0 (s2 leading)
        9   1425    true   k≥1 (s3 leading)

This means the proof cannot assume a fixed parity invariant relating binOdd
to ternOdd. Both cases must be handled.

### Safety: binary never all-s3 at odd overflow

If all binary bits were s3 at odd overflow (k=1 case), the cascade would
propagate through the entire binary into the terminator, reaching state A
at symbol 1 → HALT. The nonhalting proof requires showing this never happens.

Argument: at odd overflow, binary has just been incremented (from the preceding
even overflow era). An all-s3 binary would mean value = 2^d - 1, but the even
overflow either did carry_stop (leaving at least one s2) or overflow_carry
(resetting to all s2). In both cases, the result has at least one s2 bit.
More precisely: overflow_carry produces `rep s2 (d+1)` (all zeros), and
carry_stop flips one s2→s3 leaving others as s2. So binary always has ≥1
s2 bit after even overflow, and the subsequent cycle_nonzero steps preserve
the property that binary is not all-s3 (each increment either stops at a s2
or wraps to all-s2).

### Multi-phase overflow structure

The simulation data reveals that overflows are more complex than simple
single-step transitions. The delta_B values between consecutive T_dig
transitions are:

    T_dig transition  delta_B
    2 → 3             1 (immediate)
    3 → 4             9 = 3^2
    4 → 5             1 (immediate)
    5 → 6             118
    6 → 7             1 (immediate)
    7 → 8             1295

The non-immediate delta_B values (9, 118, 1295) are NOT simple powers of 3.
This suggests that what the proof models as "one overflow + one era of
cycle_nonzero" may actually involve nested canonical states at intermediate
ternary sizes. The proof's overflow_cycle theorem captures one phase of a
multi-phase process, producing intermediate CycleStart states with smaller
ternary counters than expected.

However, this does not affect correctness of the nonhalting argument — each
intermediate CycleStart is still a valid canonical form, and the proof only
needs to show that every canonical form leads to another canonical form
(progress), not that eras have a specific structure.

## Nonhalting Argument

The machine never halts because:
1. The normal cycle always terminates (finite sweep + carry, bounded by tape size).
2. When ternary overflows, the reset always terminates and produces a valid
   new CycleStart with more ternary digits.
3. The process repeats forever: each era has finitely many cycles, each overflow
   leads to a new era.
4. The undefined transition A,1 is never reached: symbol 1 only exists at the
   terminator, which is only approached by state B (via carry propagation).
   B,1->2LA erases it and retreats, preventing state A from ever reaching it.

### Proof status

The Lean proof in `machine.lean` establishes nonhalt modulo 4 sorries in
`canonical_progress`. Parity conditions have been removed from IsCanonical.

**Completed:**
- ✅ Remove parity conditions from IsCanonical
- ✅ `reaches_canonical`: proved by native_decide (117 steps)
- ✅ `cycle_nonzero` case: fully proved (no parity needed)
- ✅ Even overflow overflow_carry subcase: proved
- ✅ Odd overflow k=0 case: proved via `overflow_odd`
- ✅ `overflow_odd_k1` theorem: proved (k=1 cascade, 6d+10 steps)
- ✅ Case split on bin_decompose at odd overflow

**IsCanonical fields** (after parity removal):
1. `c = CycleStart bin_cells tern_cells pad`
2. `∀ s ∈ bin_cells, s = s2 ∨ s = s3`
3. `ValidTern tern_cells`
4. `pad ≤ 1`
5. `tern_cells.length ≥ 2`
6. `bin_cells ≠ []`
7. `pad = 1 → bin_cells.length ≥ 2`

**Remaining sorries (4):**

1. **Even overflow carry_stop** (line ~985): `bin'.length ≥ 2` for pad=1 output.
   - Issue: overflow_cycle guarantees `binOdd bin = true → bin'.length ≥ 2`,
     but without parity we don't know binOdd. For carry_stop with k=0
     (bin = s2::rest), bin' has same length as bin — need bin.length ≥ 2.
   - Root cause: bin.length at pad=0 could theoretically be 1 (from odd
     overflow k=0 shrinking bin). In practice always ≥ 2 per simulation.

2. **Odd overflow k=1 integration** (line ~1030): overflow_odd_k1 proved but
   output bin_rest might be too small for IsCanonical (need length ≥ 2 since
   output has pad=1). bin = s3::s2::bin_rest has length ≥ 2 trivially from
   hlen_bin, giving bin_rest.length ≥ 0 — not enough.

3. **Odd overflow k≥2** (line ~1034): Multiple leading s3 bits create invalid
   intermediate ternary (consecutive s0 cells). Needs separate theorem tracing
   the complex cascade behavior.

4. **Odd overflow all-s3 binary** (line ~1036): Must prove this config is
   unreachable. If all binary bits are s3, the cascade propagates into the
   terminator → A,s1 → HALT. Need to show binary always has ≥1 s2 bit at
   pad=1 odd overflow.

**Root issue:** All 4 sorries stem from insufficient `bin.length` tracking.
The invariant `pad=1 → bin.length ≥ 2` is too weak because:
- Even overflow output has pad=1, needs bin'.length ≥ 2 (sorry 1)
- Odd overflow k=1 output has pad=1, needs bin_rest.length ≥ 2 (sorry 2)
- Odd overflow k≥2 and all-s3 need bin to have specific structure (sorries 3-4)

**Proposed fix: strengthen bin.length tracking.**

From simulation data, bin.length at pad=1 (after even overflow) is always
much larger than 2. The growth comes from overflow_carry expanding binary.
Specifically:
- overflow_carry: bin grows by 1 (rep s3 d → rep s2 (d+1))
- carry_stop: bin stays same length
- cycle_nonzero: bin.length ≥ bin.length (never shrinks)
- odd overflow k=0: bin shrinks by 1
- odd overflow k=1: bin shrinks by 2

So net growth per even+odd overflow pair: binary grows via overflow_carry or
stays same via carry_stop, then shrinks by 1 or 2 at odd overflow. Over many
eras, binary grows because overflow_carry happens periodically.

**NOTE:** k≥2 IS reachable (B_val=11 at T_dig=5 has binary [s3,s3,s2,s3], k=2).
Any approach must handle arbitrary k, not assume k≤1.

Approaches rated by difficulty:

A. **Track bin.length explicitly** (HARD): Add invariant like `bin.length ≥ f(tern.length)`
   to IsCanonical. Requires cross-era reasoning about binary growth rate.
   Would resolve all 4 sorries if successful.

B. **Weaken IsCanonical** (MEDIUM setup + HARD core): Allow bin=[] or small bin,
   generalize cycle_nonzero for bin=[]. Moderate refactoring. But still requires
   proving all-s3 unreachable (see below).

C. **General k overflow theorem** (MEDIUM): Prove by induction on k that the
   odd overflow cascade + k A,s3→0LA steps + ⌊k/2⌋ mini-cycles reaches a valid
   CycleStart. Each mini-cycle processes one (s0,s0) pair via 3 steps + carry.
   Similar structure to existing inductive proofs.

**Irreducible core difficulty: all-s3 unreachable (HARD, required by ALL approaches)**

If binary is all-s3 at odd overflow, the A,s3→0LA cascade propagates through
the entire binary into the terminator: A reads s3 (terminator) → 0LA, then
reads s1 → HALT. So any correct nonhalting proof MUST show this never happens.

After even overflow, binary always has ≥1 s2 bit (carry_stop leaves s2 bits,
overflow_carry produces all s2). But cycle_nonzero can make binary all-s3
temporarily (carry_stop with k=0 on bin = s2::rep s3 m gives rep s3 (m+1)).
The next cycle immediately fixes this via overflow_carry. The question is:
can ternary reach 0 at the exact cycle when binary is all-s3?

This is a number-theoretic condition: binary value V + ternary value T = V₀ + T₀
(conserved during normal cycles, modulo wrapping). Binary is all-s3 when
V = 2^n - 1. So need: V₀ + T₀ ≢ 2^n - 1 (mod 2^n) for all reachable parameters.

Possible argument: 3^d - 1 is always even (since 3^d is odd). So the number of
normal cycles per half-era is even. Binary parity is preserved over an even
number of increments. If binary parity at even overflow output rules out all-s3
at odd overflow... but this requires tracking parity, which we removed.

**Recommended path forward:**
1. Prove general k overflow theorem (approach C, MEDIUM) — handles sorries 2-3
2. Prove all-s3 unreachable (HARD) — handles sorry 4
3. Sorry 1 (even overflow length) may resolve as a consequence of 1-2, or may
   need a separate bin.length argument
