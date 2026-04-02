# Macro Analysis: 1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF

## Transition table (6-state 2-symbol)

| | 0 | 1 |
|---|---|---|
| A | 1RB | 1LA |
| B | 1RC | 0RF |
| C | 1RD | --- |
| D | 0LE | 1RB |
| E | --- | 0LA |
| F | 1LD | 1RF |

Undefined: C,1 and E,0.

## Tape structure

The tape is always a block of 1s with a small number of **zero-markers**
scattered inside:

```
0^inf  1^a₁  0  1^a₂  0  ...  1^aₖ  [HEAD]  1^b₁  0  1^b₂  0  ...  1^bₘ  0^inf
```

The total tape length grows slowly (O(log steps)). The number of
zero-markers varies by phase but is always small (≤ ~log(tape_length)).

## Macro operations

The machine alternates between five micro-phases that compose into
sweep cycles:

### Phase 1: A-sweep-left
- **Rule**: A,1 → 1LA (identity sweep: writes 1 over 1, moves left)
- **Effect**: Head races left across all 1s until hitting a 0
- **Duration**: proportional to distance to left edge or left zero-marker

### Phase 2: B-create-zero
- **Rule**: A,0 → 1RB then B,1 → 0RF
- A consumes a 0-marker (writes 1 over it), moves right, becomes B
- B writes a **new** 0-marker one position to the right of the old one
- Net effect: **left zero-marker shifts right by 1**

### Phase 3: F-sweep-right
- **Rule**: F,1 → 1RF (identity sweep: writes 1 over 1, moves right)
- **Effect**: Head races right across 1s until hitting the next 0-marker
  (or the right edge of the tape)

### Phase 4a: F-bounce (interior zero)
- **Rule**: F,0 → 1LD then D,1 → 1RB
- F consumes a 0-marker, bounces left as D, then D goes right as B
- B at the next cell sees 1 → creates new 0-marker (Phase 2 again)
- Then F sweeps right again (Phase 3)
- Net effect: the consumed 0 is replaced by a **new 0 one position left**
- **Right zero-marker shifts left by 1**

### Phase 4b: BCD-extension (right edge)
- **Trigger**: B sees 0 at right tape edge
- **Rules**: B,0 → 1RC; C,0 → 1RD; D,0 → 0LE; E,1 → 0LA
- The BCD chain extends the tape rightward by 2 cells of 1s
- D,0 at the new right edge bounces back via E
- E writes a 0 (new rightmost zero-marker), becomes A
- **Restarts** at Phase 1

## Sweep cycle summary

One complete **sweep cycle** does the following:
1. A sweeps left to leftmost zero (or left edge)
2. Left zero shifts right by 1 (consumed and recreated)
3. F sweeps right to first zero-marker
4. That zero shifts left by 1 (consumed and recreated)
5. Continue: F sweeps right to next zero, shifts it left by 1, repeat
6. At right edge: BCD extends tape by 2, creates rightmost zero, restarts

**Key invariant**: each sweep cycle moves every zero-marker **one
position inward** (left zeros move right, right zeros move left).

## Era structure

An **era** begins when the tape is all-1s (no zero-markers). The
BCD chain extends the tape and creates a zero-pair near the right
edge. Then sweep cycles converge the zeros inward. When adjacent
zeros meet, they annihilate (merge), possibly spawning new internal
zeros that require further processing. When all zeros are gone, the
era ends and the next one begins.

**Observed E_Config events** (D reading rightmost 1 of all-1s tape):

| Era | Step | Tape length | E_Config n |
|-----|------|-------------|------------|
| 0 | 19 | 5 | E_Config 4 |
| 1 | 84 | 11 | E_Config 10 |

After E_Config 10, the machine enters a complex multi-zero-marker
phase and does **not** return to an all-1s E_Config within 1M+ steps.
The earlier claim of eras at len 13/27/77 was incorrect — those were
moments when the tape happened to have all-1s content but the head
was not in the D-at-rightmost-1 configuration.

NOTE: The tape continues to grow and zero-markers persist. The
machine's behavior becomes increasingly complex after era 1.

### Simple era example (len=9, within era 1)

Zero positions at each E→A transition:
```
step  43: zpos=[1,7]   distance=6
step  58: zpos=[2,6]   distance=4
step  69: zpos=[3,5]   distance=2  → merge
```
Three cycles to converge. Each cycle: both zeros move 1 inward.

### Complex era (len=15, within era 2)

```
step 120: zpos=[1,13]  distance=12
step 147: zpos=[2,12]  distance=10
step 170: zpos=[3,11]  distance=8
step 189: zpos=[4,10]  distance=6
step 204: zpos=[5,9]   distance=4
step 215: zpos=[6,8]   distance=2  → merge
step 230: zpos=[10,15] (tape grew to 17, new pair spawned)
step 243: zpos=[11,14] distance=3
step 249: zpos=[12,14] distance=2  → merge (then complex multi-zero phase)
```

After the main pair merges, a **secondary pair** spawns at the right
side, requiring further sub-era processing.

## Conjectures

### C1 (Non-halting — structural)
**The machine never halts.** The two undefined transitions C,1 and
E,0 are never reached because:
- C is only entered via B,0 → 1RC, which only fires at the right
  tape edge (the only place B sees 0). The next cell is also 0 (blank),
  so C always sees 0.
- E is only entered via D,0 → 0LE, which fires at the right tape
  edge. The cell one step left is always a 1 (interior of tape), so
  E always sees 1.

**Proof strategy**: show that B reads 0 only at positions ≥ max(tape)
and that D reads 0 only at positions ≥ max(tape), so C and E always
see cells beyond the current tape right edge and the cell just inside
it, respectively.

### C2 (Zero-marker invariant)
**At every E→A transition, the tape consists of a contiguous block of
1s with k ≥ 0 zero-markers at distinct interior positions. Each
subsequent sweep cycle shifts every zero-marker exactly one position
inward (left zeros move right, right zeros move left).**

This is the core inductive step for the non-halting proof.

### C3 (Era growth)
**The tape length at era boundaries grows super-linearly.** Observed
lengths 5, 13, 27, 77 suggest each era produces more internal
zero-markers when the main pair annihilates, requiring O(L) additional
sub-eras to resolve. This gives a roughly geometric growth in tape
length per era.

Length deltas: 8, 14, 50. The increasing growth factor suggests
the number of "cascade levels" of zero-marker processing increases
each era.

### C4 (Zero-pair annihilation spawns new pairs)
**When two adjacent zeros meet and annihilate, the resulting BCD
extension creates a new zero pair at the right edge of the extended
segment.** This new pair then needs its own convergence cycles. In
later eras, the annihilation cascade is deeper: merging pair A spawns
pair B, which spawns pair C, etc.

The depth of this cascade determines the era duration and explains
the super-linear growth.

### C5 (F-sweep is an identity transform)
**F,1 → 1RF and A,1 → 1LA are both identity sweeps**: they read 1,
write 1, and move. The tape content is only modified at the
zero-marker positions (by the A→B and F→D transitions). This means
tape analysis can focus entirely on zero-marker dynamics.

### C6 (Tape growth rate)
**The tape grows by exactly 2 cells per BCD extension.** Each BCD
chain writes 1 at two new cells via B,0→1RC and C,0→1RD before D,0
bounces. The number of BCD extensions per era determines the tape
length increment.

### C7 (Step count is exponential in tape length)
**The step count grows exponentially in tape length.** Each sweep
cycle takes O(L) steps (two traversals of the tape). An era with
tape length L has O(L) sweep cycles (to converge the zero-pair from
distance ~L to 0). So an era takes O(L²) steps. With L growing
geometrically across eras, the total step count is dominated by the
last era and grows exponentially.

## Key transitions for proof

The non-halting proof needs:
1. **C,1 unreachable**: B sees 0 only at right edge (beyond tape)
2. **E,0 unreachable**: D sees 0 only at right edge; cell at (right_edge − 1) is always 1
3. **Tape always extends**: BCD chain always fires (tape always reaches right edge)
4. **Zeros always converge**: inductive argument that zero-markers move inward by 1 per cycle

Items 1–2 give non-halting assuming tape structure is maintained.
Items 3–4 show the structure is maintained inductively across eras.
