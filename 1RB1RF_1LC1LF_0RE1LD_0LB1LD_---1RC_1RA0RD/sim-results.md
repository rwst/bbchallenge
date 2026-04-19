# Simulator-derived decomposition of the DBL macro cycle

**Machine**: `1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD`
**Macro config**: `C(z, m) = 0^∞ [C] (01)^z 1^m 0^∞`
**DBL rule**: `C(z, m) → C(2z, m+2−2z)` in exactly `6·z²` micro-steps.

**Empirical coverage**: simulator run up to 5·10⁶ steps; DBL cycles
observed for `z ∈ {2, 4, 6, 8, 10, 12, 14, 16, 18, 20, 24, 26, 28, 30,
32, 34, 36, 40, 42, 44, 48, 52, 56, 60, 64, 76, 112}` (always even).
Every observed cycle decomposes *exactly* into the structure below.

## Phase decomposition (proved in Lean where marked ✓)

```
tm_DBL(z, m) = phase1 ; phase2 ; phase3 ; phase4+5 ; final
```

| Phase | Steps | Proved? | Lemma |
|---|---|---|---|
| phase1 (CE-sweep)    | `2z`    | ✓ | `tm_DBL_phase1` |
| phase2 (boundary)    | `4`     | ✓ | `tm_DBL_phase2` |
| phase3 (FA-sweep)    | `5`     | ✓ | `tm_DBL_phase3` |
| phase 4+5            | `6z²−2z−9` | partial | (see below) |
| final (3-step ext.)  | `3`     | ✓ | `tm_DBL_final` |

## Structure of phase 4+5 (the recursive engine)

For every observed `z ≥ 2`, phase 4+5 consists of **exactly** `z−1`
"round groups" interleaved with **exactly** `z−2` "break cycles",
closed by one final extension:

```
phase 4+5 = round_group(1) ;
            [ break_cycle(1) ; round_group(2) ;
              break_cycle(2) ; round_group(3) ;
              …
              break_cycle(z-2) ; round_group(z-1) ; ]
            final_ext
```

where:
- `round_group(k)` = `2k` consecutive 4-step rounds = `8k` steps.
  Each round consumes `[0, 1, 1]` from the left prefix and prepends
  `[0, 1]` to the right. So `round_group(k)` consumes `ones(2·2k) = ones(4k)` ...
  **actually no**: `round_group(k)` consumes `ones(2·(2k)) = ones(4k)`
  off the left when applied to the `ones-block prefix` of that length.

  Checked: `round_group(1)` consumes the `ones 4` prefix from
  `false :: ones 4 ++ …` left at the end of phase 3; `round_group(k)`
  at index `k` consumes a larger ones-block built up by the prior
  break.

- `break_cycle(i)` = `4i + 8` steps, split as:
    - 4 steps (break round: D,D,B,F where F reads 0)
    - `4i + 2` steps (mini-FA sweep through `zebra(2i+1)` of `4i+2` cells)
    - 2 steps (trigger: A,1→F, F,1→D)

- `final_ext` = `3` steps (D,1→D,0→B,0→C — extends tape by 2 zeros).

## Step-count verification

Summing:
```
Σ_{k=1}^{z-1} 8k          (round groups)
 + Σ_{i=1}^{z-2} (4i+8)   (break cycles)
 + 3                       (final)
= 8·(z−1)z/2 + [4·(z-2)(z-1)/2 + 8(z-2)] + 3
= 4z(z-1) + 2(z-2)(z-1) + 8(z-2) + 3
= 4z² − 4z + 2z² − 6z + 4 + 8z − 16 + 3
= 6z² − 2z − 9
```

Matches `6·z² − (2z+9)` = the expected phase-4+5 count. ✓

## Concrete cases

```
z   round groups              break cycles                   phase 4+5   total
---------------------------------------------------------------------------
2   (2)                       —                               11          24
4   (2)(4)(6)                 (12)(16)                        79          96
6   (2)(4)(6)(8)(10)          (12)(16)(20)(24)              195         216
8   (2)(4)(6)(8)(10)(12)(14)  (12)(16)(20)(24)(28)(32)      359         384
10  (2)(4)(…)(18)             (12)(16)(…)(40)               571         600
12  …                         …                             831         864
…   …                         …                             …            …
112 (2)(4)…(222)              (12)(16)…(448)             75031       75264
```

(Round-group values in the table are **round counts**, each contributing
`4×` steps.)

## Left-tape shape invariant across phase 4+5

Let `L_k` = left tape at the **start** of `round_group(k)` (k = 1, …, z−1).

**Invariant** (verified by concrete trace for z=2, 4):
```
L_k = [false] ++ ones(4k) ++ (zebra (z-1-k)).reverse
```

(That is: a single `0`, then `4k` ones, then the remaining tail of
the phase-2 reverse-zebra.)

- `L_1 = [false] ++ ones 4 ++ (zebra (z-2)).reverse` — matches the
  end of `tm_DBL_phase123` ✓
- `L_{z-1} = [false] ++ ones(4(z-1)) ++ (zebra 0).reverse
           = [false] ++ ones(4z-4)` — just the single 0 plus a large
           ones block, no reverse-zebra tail.

`round_group(k)` consumes `ones(4k)` in `2k` rounds (`8k` steps),
transforming `L_k` into

```
M_k = [false] ++ (zebra (z-1-k)).reverse
```

`break_cycle(i)` then takes `M_i` and produces `L_{i+1}`:
```
Input (M_i):    [false] ++ (zebra (z-1-i)).reverse                  (length 2(z-i)−1)
Output (L_{i+1}): [false] ++ ones(4(i+1)) ++ (zebra (z-2-i)).reverse  (length 4i+4 + 2(z-2-i) + 1 = 2z+2i-3)
```

Net length change: `(2z+2i-3) − (2(z-i)-1) = 4i - 2`. ✓

For z=4 concrete trace:
- `L_1 = [0, 1, 1, 1, 1, 1, 0, 1, 0]` = `[0] ++ ones 4 ++ [1,0,1,0]` ✓
- `M_1 = [0, 1, 0, 1, 0]` = `[0] ++ [1,0,1,0]` ✓ (after round_group 1)
- `L_2 = [0, 1^8, 1, 0] = [0, 1^9, 0]` = `[0] ++ ones 8 ++ [1,0]` ✓ (after break 1)
- `M_2 = [0, 1, 0]` = `[0] ++ [1,0]` ✓ (after round_group 2)
- `L_3 = [0, 1^12]` = `[0] ++ ones 12 ++ []` ✓ (after break 2)
- `M_3 = [0]` = `[0] ++ []` ✓ (after round_group 3)
- Then final_ext extends to `C_Config 8 (m-6) p`.

## Right-tape shape

At the end of phase 3, right = `ones(m-2) ++ zeros p`.

After `round_group(k)` right gains `zebra(2k)` prepended (as rounds
prepend `[0,1]` each, and `round_group(k)` has `2k` rounds).

After `break_cycle(i)` right loses:
- `zebra(2i+1)` consumed by the mini-FA (but right has gained
  `zebra(2i+1)` first from the break-round's 3 prepends + 1 R-pop).
- Plus 2 cells lost to the trigger (step 11 and step 12 pop).

Net: right gets shorter by 2 cells (absorbing 2 ones off the ones-buffer).

After the full sequence of `z-1` round groups and `z-2` break cycles,
right has lost `2(z-2) = 2z - 4` ones from the initial `ones(m-2)`
buffer, giving `ones(m-2z+2)` remaining. After `final_ext`, the tape
gets a leading zebra pattern, landing us at
`C_Config (2z) (m - 2z + 2) p`. ✓ matches the DBL output formula.

## Significance for the Lean proof plan

The decomposition is **exactly** the recurrence:
```
P_4+5(z) = round_group(z-1) steps
         + Σ_{i=1}^{z-2} [break_cycle(i) + round_group(i+1)]
         + final_ext
```

Not the `phase_4+5(z) = phase_4+5(z-1) + constants` relation I guessed
earlier — rather a direct enumeration with closed-form step sums for
each piece.

This means the Lean proof of `tm_DBL` can proceed by:

1. Prove `round_group(k)` lemma — `2k` applications of `tm_DBL_round`.
   Already have `tm_DBL_rounds k` for `k` rounds; need `tm_DBL_rounds (2k)`.
2. Prove `break_cycle(i)` lemma — 4 steps (break round) + `FA_shift (2i)`
   (mini-FA through `zebra(2i+1)`) + 2 trigger steps.
3. Compose in a single outer induction on `z` (actually on the index `i`
   from 1 to `z-1`, with the step counts and tape shapes
   precisely tracked at each step).

With the exact structure now known, the tm_DBL proof is now just
mechanical assembly of the known primitives (`tm_DBL_round`,
`FA_shift`, concrete boundary steps). No additional structural
insights are needed — only careful bookkeeping.

## Odd-z observation

The simulator never produces an odd-z DBL cycle. The DBL rule sends
`z → 2z`, preserving parity of z. The initial C-macro after the TM
bootstrap is `C(2, 1)`, then `C(0, 2)`; both have even z. So
**z is always even** in every reachable C-macro state.

Consequence: the Lean statement of `tm_DBL` can safely assume `z ≥ 2`
with `z` even (or just `z ≥ 2`, since odd-z hypotheses are vacuously
unused). The `z = 1` edge case is unreachable and can be ignored.

## Generator for this file

See `sim6.py` and `sim7.py` — `sim7.py` output is the source of the
`round group / break cycle` counts above. To regenerate:

```
$ python3 sim7.py 5000000
```

and copy the per-z structure into this file. (The simulator emits
this as a structured tree; the output was manually formatted here.)
