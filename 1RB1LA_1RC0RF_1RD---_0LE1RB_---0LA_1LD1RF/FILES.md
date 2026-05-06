# File tree — Sweeper TM `1RB1LA_1RC0RF_1RD---_0LE1RB_---0LA_1LD1RF`

Project root for the 6-state 2-symbol "sweeper" TM nonhalting proof. The
Lean development uses `BusyLean` and depends on `machine.lean` for the
foundation; downstream files extend it. Three reachability axioms (R1,
R2, R3) were originally posited; R2 and R3-narrow were closed
(2026-04-29), only R1 (`reach_M_nil_3`) remains.

```
.
├── Lean sources
│   ├── machine.lean              1791 L  Foundation: TM transitions, OrbitReachable, OrbitProg, macro rules
│   ├── progress.lean              996 L  macro_progress dispatch + sweeper_never_halts (depends on machine + forward_dynamics)
│   ├── phase2.lean               1364 L  Backward-analysis closure of R1/R2/R3 axioms via OrbitReachable
│   ├── forward_dynamics.lean      590 L  Forward-dynamics proofs (R2, R3-narrow); now also exposes Φ-jump from R3
│   ├── era.lean                   655 L  Era-graded structures (EraStartConfig, IntraEra, IntraEraOf); intra-era sweep non-shrinking lemma; Stage D gap doc
│   ├── era_orbit.lean             513 L  Stages A1+A2+B + Φ-pruning + BadShape framework (Option A landed); 4 sorries (3 step_R1 + 1 residual base case)
│   ├── era_orbit_gamma.lean       333 L  Option γ scaffolding: D2 predecessor characterisation + γFuel measure + bounded forward simulator gammaSim. Axiom-clean, 0 sorries. Foundation for cascade closure.
│   ├── scout_parity.lean          125 L  Parity-argument scouting probe (Path 1 fast check, 2026-05-06): cursor stays odd along M→M predecessors of M([], 3, R) but M0→M (D11) breaks pure parity. 4 lemmas, 0 sorries.
│   ├── conjectures.lean            77 L  Empirical conjectures from era-sim (stated as `theorem … := sorry`)
│   └── c1inv_abandoned.lean        98 L  Abandoned step-level C1Inv/SafeRight invariant approach (kept for reference)
│
├── Planning & status (markdown)
│   ├── LOG.md                    1634 L  Master changelog; current state, axiom hygiene, layer status, Φ pipeline (2026-05-05)
│   ├── plan-era-graded-not_R1.md  765 L  Plan for closing R1 via era-graded forward analysis; Sub-plan E (D2-spine bound, post-γ) is the active path
│   ├── plan-badshape.md            336 L  Plan for closing residual base R sorry (Option A + γ scaffolding landed; cascade closure remains)
│   ├── plan-r1.md                 645 L  Plan for closing R1 via "reachable ∧ c=3 → L≠[]" (form A.3) [superseded]
│   ├── plan-sim-era.md            447 L  Five strategies for accelerating era-boundary discovery
│   ├── era_findings.md            184 L  Findings from era-sim datasets (era_*.jsonl)
│   ├── invariant_strategy.md      173 L  Taxonomy of strengthened-invariant strategies
│   ├── TACTIC_PLAN.md             164 L  Plan for closing the 3 reachability axioms
│   ├── mersenne.md                144 L  Mersenne preservation conditions in machine_base.lean
│   ├── macro_step_analysis.md      85 L  Verified macro-step mapping (200K steps, 0 mismatches)
│   ├── gap_rules_status.md         80 L  Gap rules discovery; unified sweep-rule pattern
│   └── timeout.md                 142 L  Resolved whnf-timeout fix via @[irreducible] toConfig
│
├── Notes / wikitext
│   ├── macro.txt                  Plain-text macro rule listing
│   ├── macro.wiki                 Wikitext version with transition table
│   └── wiki.txt                   Status snippet (2026-04-29)
│
├── Python simulators
│   ├── sim.py                     331 L  Raw 6-state 2-symbol TM simulator
│   ├── macro_sim.py               643 L  F1+F2 macro-step simulator with axiom logging (mirrors machine.lean dispatch)
│   ├── macro_audit.py              97 L  Audits config patterns for axiom-producer detection
│   └── __pycache__/               Compiled Python (macro_sim, sim)
│
├── era-sim/                       Native Rust port of macro_sim.py
│   ├── Cargo.toml                 Edition 2024, opt-level 3 + thin LTO
│   ├── Cargo.lock
│   ├── src/main.rs                1:1 port of macro_step dispatch; emits JSONL of era boundaries
│   └── target/release/era-sim     Built binary
│
├── Data
│   ├── ax_100b.json               Axiom firings log (100 G macro steps; mostly R3)
│   ├── era_100b.jsonl    7.4 MB   Era-boundary dataset, 100 G macro steps
│   └── era_full.jsonl   14.6 MB   Full era-boundary dataset (largest run)
│
├── .claude/
│   └── settings.local.json        lean-lsp MCP enabled
│
└── FILES.md                       This index
```

## Build & verification

- `lake build Sweeper` succeeds with no `sorry`s.
- `#print axioms Sweeper.sweeper_never_halts` →
  `{propext, Classical.choice, Quot.sound, reach_M_nil_3, reach_multi_bounce_last_2_long, reach_multi_bounce_last_2_mid_1}`
  (post-2026-04-29: only the first three plus **R1** remain after R2 + R3-narrow closure).

## Dependency graph (Lean)

```
            BusyLean + Mathlib
                   │
              machine.lean
              ┌────┴────┐
              ▼         ▼
   forward_dynamics  (era.lean ↑ progress)
              │         ▲
              └─────►progress.lean
                        ▲
                        │
                    phase2.lean
                        ▲
                        │
                  conjectures.lean (sorries)
```

`c1inv_abandoned.lean` imports only `BusyLean` and is not part of the
build chain.
