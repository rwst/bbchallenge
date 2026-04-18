# TODO: rule_R3_general / rule_R4_general by induction

## Goal

Prove:
```
rule_R3_general (n m : Nat) (middle : List Nat) (hmid : AllPosEven middle) (L : List Sym) :
    run tm { B, s1, L, rep s4 (2n+1) ++ [s1, s2] ++ middlePrefix middle ++ rep s4 (2m+2) }
        (4n + 4m + 16 + Σ (2yᵢ + 8) for yᵢ ∈ middle) =
      { B, s1, L, rep s4 (2n) ++ [s1, s2] ++ middlePrefix middle ++ rep s4 (2m+2) ++ [s1, s2] }
```

Where:
- `middlePrefix : List Nat → List Sym` recursively: `[] → []`, `y :: ys → rep s4 y ++ [s1, s2] ++ middlePrefix ys`
- `middle_cost middle = Σᵢ (2yᵢ + 8)` — per-digit cost is `2y + 8` (forward `y+4` + backward `y+4`)

## Prerequisites (DONE)

- [x] `sweep_s2_carry_L` (left-generalized)
- [x] `finalize_tail_L` (left-generalized)
- [x] `sweep_s2_to_s3` (already L-generalized via listHd/listTl)
- [x] `AllPosEven` predicate
- [x] `cross_even_digit_forward`, `cross_even_digit_backward`

## Step 1: Define helpers

- [ ] `def middlePrefix : List Nat → List Sym`
- [ ] `def middle_cost : List Nat → Nat := fun ys => 2 * ys.sum + 8 * ys.length`
- [ ] `def stack_L : List Nat → List Sym → List Sym` — accumulated left from forward pass
- [ ] Simp lemmas: `middlePrefix_nil`, `middlePrefix_cons`, `stack_L_nil`, `stack_L_cons`

## Step 2: Left-generalize rule_R3_nil

- [ ] `rule_R3_nil_L (n m : Nat) (L : List Sym)`:
  - Same as rule_R3_nil but with `L` flowing through all helpers.
  - Use `finalize_tail_L` at the end.
  - All other helpers already handle arbitrary left context (they push onto left).
  - Key change: replace `[s1]` with `s1 :: L` in initial sweep_s4_odd_A call.

## Step 3: Left-generalize rule_R4_nil

- [ ] `rule_R4_nil_L (n m : Nat) (L : List Sym)`:
  - Parallel to rule_R3_nil_L but with R4 backward phase.
  - For m=0 case: 5 direct steps handle left specially — need to check L threads correctly.
  - For m≥1: sweep_s2_to_s3 + finalize_tail_L.

## Step 4: Forward pass helper

- [ ] `forward_pass (middle : List Nat) (hmid : AllPosEven middle) (L Rtail : List Sym)`:
  ```
  run tm { B, s1, L, s2 :: (middlePrefix middle ++ Rtail) } 
      (Σᵢ (yᵢ + 4)) =
    { B, s1, stack_L middle L, s2 :: Rtail }
  ```
  - Induction on middle.
  - Base: run tm config 0 = config (trivial).
  - Step: peel cross_even_digit_forward, apply IH.

## Step 5: Backward pass helper

- [ ] `backward_pass (middle : List Nat) (hmid : AllPosEven middle) (L : List Sym) (Rprefix : List Sym)`:
  ```
  -- Starts from state A head s2 with stack_L middle L on left + extra shape.
  -- Consumes middle digits in reverse, rebuilding them on right.
  ```
  The backward state shape is tricky. After sweep_s2_to_s3 + first backward_carry, we're at:
  - state A head s2
  - left = rep s2 (y_j - 1) ++ s3 :: s1 :: stack_L (middle-last) L
  - right = s2 :: rep s4 (2m+2) ++ [s1, s2]
  
  Then cross_even_digit_backward + backward_carry iterates, peeling each digit.
  Final state: state A head s2, left = rep s2 (2n) ++ s1 :: L.
  
  This is complex — the "state after j iterations" involves both left shape and accumulated right-side tail.

## Step 6: Compose rule_R3_general

- [ ] Combine rule_R3_nil_L + forward_pass + sweep_s4_from_B_even + bounce + sweep_s2_to_s3 + backward_pass + finalize_tail_L.
- [ ] Arithmetic: step count = 2n+2m+10 + forward_cost + 2 + (2m+2) + 3 + backward_cost + (2n+1) = 4n+4m+16 + middle_cost middle.

## Step 7: Compose rule_R4_general

- [ ] Same structure but backward phase uses sweep_s2_to_s3 (2m-1) for m≥1 case (m=0 case needs special handling).
- [ ] Step count = 4n+4m+18 + middle_cost middle.

## Step 8: Wire into rule_R3 / rule_R4

- [ ] Replace the cons-cons sorry in rule_R3 with rule_R3_general.
- [ ] Replace the cons-cons sorry in rule_R4 with rule_R4_general.

## Challenges & risks

1. **Backward pass state shape**: The intermediate state after j backward iterations has a mixed left shape (partial stack) and right shape (partial rebuild). Precise formulation is tricky.

2. **AllPosEven destructuring**: Each induction step needs `∃ k, y = 2*k+2` from AllPosEven, which gives the concrete form needed for `cross_even_digit_forward k`.

3. **Arithmetic**: Step count formula involves Σ over middle. Need to be careful with Nat sum manipulation.

4. **Simp normalization**: After applying forward_pass, the right tape has structural differences (`middlePrefix ys ++ rep s4 (2m+2)` vs `macroRight (ys ++ [2m+2])`). Need simp lemmas to unify.

## Estimated scope

- Helpers (steps 1-3): ~150 lines
- Forward pass (step 4): ~50 lines (simpler induction)
- Backward pass (step 5): ~100 lines (more intricate)
- Composition (steps 6-7): ~200 lines each
- Total: ~700 lines new code

## Incremental checkpoints

If full implementation is too large, do in this order:
1. Step 1 (definitions only): 30 lines, no proofs.
2. Step 2 (rule_R3_nil_L): 80 lines, unlocks cleaner rule_R3_nil.
3. Step 4 (forward_pass): 50 lines, standalone useful.
4. Step 6 (rule_R3_general) for middle of length ≤ 2: test composition.
5. Generalize Step 6 to arbitrary middle.

Each checkpoint should compile cleanly before proceeding.
