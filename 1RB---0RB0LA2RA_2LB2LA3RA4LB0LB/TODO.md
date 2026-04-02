# TM5 Nonhalt Proof — Remaining Sorries

The file `machine.lean` proves `nonhalt` (the 2-state 5-symbol TM does not halt)
modulo **1 sorry** in `canonical_progress` (line ~991). The rest compiles cleanly.

## Architecture

```
nonhalt
  ├── reaches_canonical        ✓  (native_decide, 117 steps)
  └── canonical_progress       1 sorry (odd overflow parity)
        ├── cycle_nonzero case     ✓  (parity flip via binOdd/ternOdd)
        ├── even overflow case     ✓  (binOdd flip + length ≥ 2)
        └── odd overflow case      1 sorry (parity of output)
```

## Completed

- **A1 + B1:** `bin' ≠ []` added to cycle_nonzero and overflow_cycle outputs
- **A2 + A3:** Parity preserved through cycle_nonzero via binOdd/ternOdd flip lemmas
- **B2:** binOdd flip through overflow_cycle, deriving `binOdd bin' = false`
- **C1:** `bin_rest ≠ []` derived from `pad = 1 → bin.length ≥ 2` in IsCanonical,
  proved via `bin'.length ≥ 2` from overflow_cycle when `binOdd = true`

### Helper lemmas added
- `ternOdd_rep_s2_append` — ternOdd ignores leading s2 pairs
- `ternOdd_repPair_s4_s2_append` — ternOdd ignores leading (s4,s2) pairs
- `binOdd_carry_flip_stop` — binOdd flips under carry_stop
- `binOdd_overflow_carry_flip` — binOdd flips under overflow_carry (d ≥ 1)

### IsCanonical fields
1. `c = CycleStart bin_cells tern_cells pad`
2. `∀ s ∈ bin_cells, s = s2 ∨ s = s3`
3. `ValidTern tern_cells`
4. `pad ≤ 1`
5. `tern_cells.length ≥ 2`
6. `bin_cells ≠ []`
7. `pad = 1 → binOdd bin_cells = ternOdd tern_cells`
8. `pad = 0 → binOdd bin_cells = !ternOdd tern_cells`
9. `pad = 1 → bin_cells.length ≥ 2`

## Remaining sorry: odd overflow parity (line ~991)

**Goal:** `binOdd bin_rest = true` where `bin = s2 :: bin_rest` at odd overflow (pad=1).

Currently the odd overflow case uses `overflow_odd` which handles only k=0 (bin starts
with s2, meaning binary is even). The output `CycleStart bin_rest (rep s2 (2*(d+2))) 0`
needs `binOdd bin_rest = !ternOdd (rep s2 ...) = true`. This requires the second-lowest
bit of binary to be s3 (value ≡ 2 mod 4).

### Chosen approach: k=1 overflow cascade (avoids mod-4 tracking)

Instead of requiring `binOdd bin_rest = true`, restructure the odd overflow proof to
handle both possible cases of `bin_rest`:

**Case k=0:** `bin_rest = s2 :: rest2` (second bit is 0, value ≡ 0 mod 4).
  Output: `CycleStart rest2 (rep s2 (2*(d+2))) 0`
  — uses existing `overflow_odd`

**Case k=1:** `bin_rest = s3 :: rest2` (second bit is 1, value ≡ 2 mod 4).
  Output: `CycleStart rest2 tern' 1` with specific ternary from cascade
  — needs new theorem `overflow_odd_k1`

**Case bin_rest = []:** impossible (already proved via `hlen_bin`)

The odd overflow cascade with k=1:
1. Forward sweep: 2*(d+1) steps through d+1 pairs → (s0,s3) pairs
2. Bounce: 3 steps (A,0→1RB, B,0→2LB, B,1→2LA)
3. Leftward cascade: 4*(d+1) steps → (s2,s2) pairs
4. At binary s3: A,3→0LA, creates s0. Now head reads next binary cell.
5. Result: `CycleStart rest2 (s0 :: s2 :: rep s2 (2*(d+1))) 1`
   i.e., first ternary pair is (s0,s2) = digit 1, rest is zero, pad=1

Steps for k=1 = 6d + 10.

### Implementation plan

1. Prove `overflow_odd_k1 (bin_rest : List Sym) (d : Nat)`:
   ```
   run tm (CycleStart (s3 :: bin_rest) (rep s2 (2*d)) 1) (6*d+10) =
     CycleStart bin_rest (s0 :: s2 :: rep s2 (2*(d+1))) 0
   ```
   Similar to `overflow_odd` but with one extra cascade step through the s3 bit.

2. In `canonical_progress` odd overflow case, replace current proof with:
   ```
   cases bin_rest with
   | nil => exact absurd rfl hne_br
   | cons b rest2 =>
     have hb := hbr b (by simp)
     rcases hb with rfl | rfl
     · -- b = s2 (k=0): use overflow_odd
       ...existing proof, binOdd rest2 needs to be shown...
     · -- b = s3 (k=1): use overflow_odd_k1
       ...new proof with different output ternary...
   ```

   Wait — this still has the same problem. After removing the s2 (k=0) or s3 (k=1)
   bit, we get `rest2` and need `binOdd rest2 = true` (for k=0 output pad=0) or
   `binOdd rest2 = ternOdd (s0 :: s2 :: ...)` (for k=1 output pad=0).

   For k=1 output: `ternOdd (s0 :: s2 :: rep s2 (2*(d+1)))` = `!ternOdd (rep s2 (2*(d+1)))` = `!false` = `true`. So need `binOdd rest2 = !true = false`... wait, pad=0 means `binOdd = !ternOdd`.

   Let me recalculate. k=1 output is `CycleStart rest2 (s0 :: s2 :: rep s2 (2*(d+1))) 0`.
   Parity condition pad=0: `binOdd rest2 = !ternOdd (s0 :: s2 :: rep s2 (2*(d+1)))`.
   `ternOdd (s0 :: s2 :: rep s2 ...) = !ternOdd (rep s2 ...) = !false = true`.
   So need: `binOdd rest2 = !true = false`.

   For k=0 output: `CycleStart rest2 (rep s2 (2*(d+2))) 0`.
   Parity condition pad=0: `binOdd rest2 = !ternOdd (rep s2 ...) = !false = true`.

   So k=0 needs `binOdd rest2 = true` and k=1 needs `binOdd rest2 = false`.
   Since `bin_rest = s2 :: rest2` (k=0) or `bin_rest = s3 :: rest2` (k=1),
   and `binOdd (s2 :: rest2) = false`, `binOdd (s3 :: rest2) = true`...

   Wait. The parity condition says: at odd overflow, `binOdd bin = false` (bin = s2 :: bin_rest). We DON'T have a parity condition on bin_rest. We need one for the output.

   Key insight: `binOdd bin_rest` = second-lowest bit of bin. We know `binOdd bin = false` (LSB is s2). The output parity depends on whether we used k=0 or k=1.

   For k=0 (bin_rest starts with s2): `binOdd rest2 = ?`  — we don't know!
   For k=1 (bin_rest starts with s3): `binOdd rest2 = ?`  — we don't know!

   **The parity of rest2 is the THIRD bit.** We've just pushed the problem one level deeper.

   HOWEVER: both k=0 and k=1 produce valid outputs IF the parity condition holds.
   The question is whether the parity condition ALWAYS holds for the actual execution.

### Real solution: the parity condition IS automatically satisfied

Actually, let me reconsider. The output of odd overflow with k=0 is:
  `CycleStart bin_rest (rep s2 (2*(d+2))) 0`

We need IsCanonical, which requires `binOdd bin_rest = !ternOdd (rep s2 (2*(d+2))) = true`.

But `binOdd bin_rest = binOdd (s2 :: rest2) = false` if bin_rest starts with s2.
That gives `false = true` — CONTRADICTION.

So k=0 with bin_rest starting with s2 is IMPOSSIBLE in the actual execution? No wait,
k=0 means bin starts with s2 (which it does from parity), and overflow_odd removes
the leading s2. So bin_rest is what remains. And we need binOdd bin_rest = true.

This is exactly the original C2 sorry. The k=0/k=1 split doesn't help because we
still need to know the second bit to determine which case we're in, and whichever
case we're in, we need to know the third bit for the output parity.

### Correct approach: both cases have DIFFERENT output structures

The key realization: k=0 and k=1 produce different (pad, ternary) pairs:
- k=0: pad=0, tern = rep s2 (all zero)
- k=1: pad=1, tern = s0 :: s2 :: rep s2 ... (first pair nonzero)

Wait, I wrote k=1 output as pad=0 above. Let me recheck from memory:

From project_odd_overflow.md:
- k=0: bin' = bin_rest (s2 consumed), tern' = rep s2 (2*(d+2)), pad' = 0
- k=1: bin' = bin_rest (s3 and s2 consumed), tern' has first pair (s0,s2), rest zeros, pad' = 1

So k=1 output has pad=1! Let me redo:

k=1 output: `CycleStart bin_rest' (s0 :: s2 :: rep s2 (2*d')) 1` for appropriate d'.
Actually from memory: "tern' has first pair = (s0,s2) = digit 1, rest = (s2,s2) = digit 0. d+2 pairs total."

So tern' = s0 :: s2 :: rep s2 (2*(d+1)), total pairs = 1 + (d+1) = d+2. And pad=1.

For pad=1 parity: `binOdd bin_rest' = ternOdd tern'`.
`ternOdd (s0 :: s2 :: rep s2 (2*(d+1))) = !ternOdd (rep s2 (2*(d+1))) = !false = true`.
So need: `binOdd bin_rest' = true`.

And bin_rest' is bin_rest with s3 removed (since k=1 means bin_rest = s3 :: bin_rest').
`binOdd bin_rest'` — we don't know this either!

So both cases require knowing `binOdd` of deeper parts of the binary. The k=1 approach
does NOT avoid the mod-4 problem; it just shifts it.

### True solution

The fundamental issue is that odd overflow removes bits from binary, and we need to
maintain parity of the remaining bits. This requires tracking more than just the LSB
parity.

**Option A: Track value mod 4** — add `bin_value mod 4` condition to IsCanonical.
At pad=0 (era start): value ≡ 1 (mod 4). After cycle_nonzero: value increments,
mod 4 cycles 1→2→3→0→1... After 3^d steps: value ≡ 1 + 3^d (mod 4).

**Option B: Track second-bit parity** — add a condition on bin[1] to IsCanonical.
Similar complexity to Option A.

**Option C: Strengthen the whole approach** — define binary value as a natural number,
track it explicitly, and derive bit-level properties as needed.

**Recommended: Option A** (track value mod 4). Add to IsCanonical:
- `pad = 0 → bin_value bin ≡ 1 [MOD 4]`  (era start: value is 1 mod 4)
- `pad = 1 → bin_value bin ≡ 0 [MOD 2]`  (mid-era: value is even)

Then at odd overflow:
- `bin_value bin ≡ 0 [MOD 2]` → bin = s2 :: bin_rest (LSB = 0)
- Need `bin_value bin ≡ 2 [MOD 4]` for bin_rest to start with s3
- This requires `pad = 1 → bin_value bin ≡ 2 [MOD 4]`

Proving this invariant through cycle_nonzero: value increments by 1, so mod 4 cycles.
After even overflow (pad 0→1): value was V ≡ 1 + 3^d (mod 4), overflow_cycle adds 1,
so value ≡ 2 + 3^d (mod 4). Then cycle_nonzero runs 3^d - 1 more times:
value at odd overflow ≡ 2 + 3^d + (3^d - 1) = 1 + 2·3^d (mod 4).

For d=1: 2·3 = 6 ≡ 2 (mod 4), so value ≡ 3 (mod 4)... that's not ≡ 2.
Hmm, this doesn't seem to give a clean invariant.

**Actually**, maybe the invariant should just be `pad = 1 → bin_value ≡ 2 [MOD 4]`
and verify this is preserved by cycle_nonzero (which adds 1, so 2→3→0→1→2...,
preserving mod-4 only after 4 steps, not after each step).

This doesn't work directly. cycle_nonzero changes value by 1, so mod 4 changes each step.

**The real invariant must account for the ternary value too.** Let V = binary value,
T = ternary value. The pair (V, T) evolves as: cycle_nonzero does V→V+1, T→T-1.
So V+T is constant during an era. V+T at era start = V0 + 3^d - 1 (T starts at 3^d - 1).
At overflow: T = 0, so V = V0 + 3^d - 1.

At even overflow (pad=0→1): V_even = V0 + 3^d - 1, after carry: V_even' = V0 + 3^d.
Then T resets to 3^{d'} - 1 for new d'. cycle_nonzero runs until T=0 again:
V_odd = V_even' + 3^{d'} - 1.

Hmm, this is getting complex. Let me just leave the 1 sorry with a clear comment
and the analysis above.
