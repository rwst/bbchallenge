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
- Binary is incremented by 1 (via carry_stop or overflow_carry)
- Ternary is re-initialized to all-max (value 3^d - 1)

The binary increment may be:
- **carry_stop**: flips lowest s2→s3, standard +1. Binary length unchanged.
- **overflow_carry**: all bits are s3 (value 2^n-1), wraps to rep s2 (n+1) (value 0),
  carry absorbed by terminator which shifts left. Binary grows by 1 digit.

### Odd overflow (pad=1 → pad=0)

When ternary is all-zero at pad=1, the head enters ternary, bounces, and
cascades left into the binary region. Cases depend on the leading binary bits:

**Case k=0** (bin starts with s2, i.e., binary value is even):
- The overflow_odd theorem applies
- Input: `CycleStart (s2 :: bin_rest) (rep s2 (2*d)) 1`
- Output: `CycleStart bin_rest (rep s2 (2*(d+2))) 0`
- The leading s2 is consumed (absorbed into new ternary)
- Ternary grows by 2 digit pairs (d → d+2), re-initialized to all-zero
- Binary shrinks by 1 cell
- Steps: `6*d + 9`

**Case k=1** (bin = s3 :: s2 :: bin_rest, exactly one leading s3):
- The overflow_odd_k1 theorem applies
- Input: `CycleStart (s3 :: s2 :: bin_rest) (rep s2 (2*d)) 1`
- Output: `CycleStart bin_rest (s0 :: s2 :: rep s2 (2*(d+1))) 1`
- The leading s3 and s2 are consumed, creating ternary digit 1 (pair s0,s2)
- Ternary grows by 2 pairs (d → d+2 total), first digit = 1, rest = 0
- pad stays at 1 (another odd overflow follows with the new nonzero ternary)
- Steps: `6*d + 10`

**Case k≥2** (bin = rep s3 (k+1) ++ s2 :: bin_rest, multiple leading s3s):
- Not yet proved. The cascade creates k+1 consecutive s0 cells in the ternary
  region, which is not valid ternary for k≥2 (pairs would be (s0,s0) etc.)
- Needs separate analysis

**Case all-s3** (bin = rep s3 dd):
- Carry propagates through all binary cells into the terminator
- Verified by simulation: this ALWAYS leads to A reading s1 → HALT
- Must prove this configuration is unreachable

### Parity of binary at odd overflow

The leading bit of binary at odd overflow is NOT fixed — both k=0 and k≥1
occur in practice:

    T_dig  B_val  binOdd  case
        3      1    true   k≥1 (s3 leading)
        5     11    true   k≥1 (s3 leading)
        7    130   false   k=0 (s2 leading)
        9   1425    true   k≥1 (s3 leading)

### Binary value trajectory

Tracing binary value (V) at even overflow entries and the parity of bin_rest
at odd overflow outputs (the value that becomes the next even overflow input):

    Era  V_entry  binOdd  d   V_after_era  bin_rest_val  binOdd(rest)
      0        1    true  4            22            11         true
      1       11    true  6           260           130        FALSE
      2      130   false  8          2851          1425         true
      3     1425    true 10         29754         14877         true
      4    14877    true 12         38414         19207         true
      5    19207    true 14        870016        435008        FALSE

The pattern of binOdd(bin_rest) is: T, F, T, T, T, F, F, F, ...
This is NOT periodic and NOT constant.

**CRITICAL FINDING:** No simple mod-based parity invariant can determine
binOdd at even overflow entries. The unconditional invariant
`binOdd bin = (ternOdd tern == (pad == 1))` was proved preserved by
cycle_nonzero (both flip) and overflow_cycle, but is FALSE at the output
of overflow_odd: `binOdd bin_rest = true` fails at era 1 (bin_rest value
130 is even).

The binary value at era end depends on the wrap history during cycle_nonzero:
binary wraps (overflow_carry) multiple times per era since 3^d >> 2^(bin.length).
The value after wraps is V₀ + T - Σ(2^nᵢ) where nᵢ are binary lengths at
each wrap. This makes the mod-4 (and higher) behavior of V_end depend on
the exact wrap schedule, which varies per era.

### Safety: binary never all-s3 at odd overflow

All-s3 at odd overflow (binary = rep s3 dd) leads to HALT (confirmed by
simulation for all tested dd and d values). The nonhalting proof MUST show
this never occurs.

**What doesn't work:**
- Parity invariant: binOdd at even overflow is not always true (era 2 has
  V=130, binOdd=false). So we cannot prove binOdd=false at odd overflow.
- binValue conservation V+T=const: FALSE because overflow_carry resets
  binary value to 0, not +1. The sum changes at every wrap.
- Any simple mod-k invariant: the binary value mod 4 at overflow points
  depends on wrap history, which has no periodic pattern.

**What might work:**
- General overflow theorem for arbitrary k: prove that for any k leading s3s
  followed by s2::bin_rest, the overflow produces a valid CycleStart.
  Combined with proving all-s3 is unreachable, this would close all cases.
- Binary length growth argument: show 2^(bin.length) grows faster than 3^d,
  so that the gap (2^n - 1 - binValue) is always positive at odd overflow.
  But 2^(bin.length) < 3^d in practice (wraps always happen), so this
  argument cannot work directly.
- Computational verification: verify the first N eras by computation,
  then show a structural property (e.g., binary length ≥ d + C) holds
  from era N onward, making all-s3 impossible.
- The all-s3 case requires binValue = 2^n - 1, which means exactly
  T - Σ(2^nᵢ) + V₀ = 2^n_final - 1. This is a precise Diophantine
  condition that may be provable to never hold.

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
4. The undefined transition A,1 is never reached because binary is never all-s3
   at odd overflow (preventing the carry cascade from reaching the terminator).

Point 4 is the crux — it requires showing all-s3 is unreachable. See the
"Safety" section above for the current state of this argument.

### Proof status

The Lean proof in `machine.lean` establishes nonhalt modulo **1 sorry** in
`canonical_progress`. The proof uses an unconditional parity invariant as
IsCanonical field 8, but this invariant is FALSE for some reachable states.

**IsCanonical fields** (current, 8 fields — field 8 is WRONG):
1. `c = CycleStart bin_cells tern_cells pad`
2. `∀ s ∈ bin_cells, s = s2 ∨ s = s3`
3. `ValidTern tern_cells`
4. `pad ≤ 1`
5. `tern_cells.length ≥ 2`
6. `bin_cells ≠ []`
7. `pad = 1 → bin_cells.length ≥ 2`
8. `binOdd bin_cells = (ternOdd tern_cells == (pad == 1))` ← **FALSE at era 2**

Field 8 is preserved by cycle_nonzero (both binOdd and ternOdd flip each step)
and by overflow_cycle (binOdd flips, ternOdd stays false). But it is NOT
preserved by overflow_odd: the output requires `binOdd bin_rest = true`,
which is false when bin_rest has even value (occurs at era 1: bin_rest=130).

**Proved theorems:**
- `reaches_canonical`: native_decide (117 steps)
- `cycle_nonzero`: fully proved, preserves all 8 fields
- `overflow_cycle` (even overflow): fully proved
- `overflow_odd` (odd overflow k=0): proved (6d+9 steps)
- `overflow_odd_k1` (odd overflow k=1): proved (6d+10 steps)
- At even overflow: parity invariant gives binOdd=true → hlen2 → bin'.length ≥ 2
- At odd overflow: parity invariant gives binOdd=false → k=0 only → all other
  cases eliminated by contradiction

**Remaining sorry (1):**
`binOdd bin_rest = true` at k=0 odd overflow output — **unprovable (false)**.

**Consequence:** The proof structure with the parity invariant as field 8
cannot work. Either:
1. Remove field 8 and handle all odd overflow cases (k=0, k=1, k≥2, all-s3)
   individually — reverting to the original 4-sorry structure
2. Find a correct invariant that rules out all-s3

### Binary length changes

- overflow_carry: bin grows by 1 (rep s3 d → rep s2 (d+1))
- carry_stop: bin stays same length
- cycle_nonzero: bin.length ≥ bin.length (never shrinks)
- odd overflow k=0: bin shrinks by 1
- odd overflow k=1: bin shrinks by 2
- odd overflow k≥2: bin shrinks by k+1

During each era, binary wraps multiple times (3^d >> 2^bin.length), growing
by ~3-5 cells per era from wraps. Ternary grows by 2 pairs per era.
Binary length at even overflow entries: 2, 5, 8, 11, 14, 18, 21, 24, ...

**NOTE:** k≥2 IS reachable (B_val=11 at T_dig=5 has binary [s3,s3,s2,s3], k=2).
Any approach must handle arbitrary k, not assume k≤1.
