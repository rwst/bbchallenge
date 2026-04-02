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
