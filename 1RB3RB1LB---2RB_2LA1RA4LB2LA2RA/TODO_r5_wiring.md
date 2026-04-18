# TODO: rule_R5 wiring (COMPLETED)

Resolved via:
- `R5_tail : List Nat → List Sym` — helper defining trailing tape for rest.
- `macroRight_R5_unfold` — unified unfolding lemma (induction on middle generalizing a).
- `rule_R5` now directly applies `rule_R5_core_with_middle` after the unfolding.

No further action needed.
