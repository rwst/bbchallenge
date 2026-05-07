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
│   ├── scout_2adic.lean           199 L  2-adic measure scout (Path 1′ check, 2026-05-06): defines macroMr := P_R(2) + 3; D2 forward doubles macroMr, D3 forward +1; lex(phi, macroMr) strictly decreases backward across D2/D3/D11. 0 sorries, key forward identities axiom-clean.
│   ├── era_orbit_2adic.lean       235 L  Sub-plan E.3' foundations (2026-05-06): macroStep_lex_strict_increase (12-case forward monotonicity, axiom-clean), D2_backward_phi_eq + D2_backward_mr_double + D2_backward_lex_strict (cascade-backward analysis), cascade_unreachable structural skeleton. Delegates base case to era.lean's existing sorry.
│   ├── era_orbit_macros.lean      275 L  Cascade tactic library (2026-05-07, expanded): `mc_dcase_close`, `mc_rule_close`, `mc_phi_lt_six`, `mc_R1_self`, `mc_R1_callback`, `mc_R3_extract`, `mc_AllGe1_a_ge1`, `mc_noconf`, `mc_inj_omega/simp` — automate boilerplate (M-vs-M0 noConfusion, M.injEq + cons.injEq + omega ladders, phi_lt_six, step_R1/R3 unpackers, AllGe1 ⊥ closer, length-mismatch via simp fallback). 602 invocations across cascade*.lean.
│   ├── era_orbit_cascade.lean     1172 L  Cascade redesign base (2026-05-07 macro pass): InCascade predicate (4 constructors), 7 base shape-exclusion helpers + 3 starts-with helpers (callback variants for cascade IH); refactored with macros (57 invocations). 0 sorries.
│   ├── era_orbit_cascade_chains.lean  1815 L  21 chain helpers (D11/mb2as/R2_succ chains, axiom-clean), refactored with macros (381 invocations). 0 sorries.
│   ├── era_orbit_cascade_main.lean  451 L  cascade_strong_aux + cascade_strong + corollary `not_M_empty_3_via_cascade`. Imports d2 to use chain helpers. 6 sorries inside cascade_strong_aux (mk_M_1_2spine_5 D2/D12 + mk_M_empty_7 D12/mb2ds/R2zero/R3).
│   ├── era_orbit_cascade_d2.lean   1663 L  D2/D3 sub-case work file (Sessions 8-12): refactored with macros (164 invocations); 25 sorries cover bridging `not_M_6_3_dR_via_ih` (D3, step_R3); helpers `not_M_2_6_3_dR_via_ih` (D2/D3 forward-ref to later helpers, multi_bounce_general/last_2_general, step_R3); `not_M_1_6_5_R_via_ih` (D2/D8/D12, step_multi_bounce_general/3run_last_2/last_2_general, step_R3); parametric `not_M_kspine_6_3_R_via_ih` (whole body — needs mathlib API rewrite for `List.length_replicate`/`nsmul_eq_mul`/`List.getElem?`).
│   ├── conjectures.lean            77 L  Empirical conjectures from era-sim (stated as `theorem … := sorry`)
│   └── c1inv_abandoned.lean        98 L  Abandoned step-level C1Inv/SafeRight invariant approach (kept for reference)
│
├── Planning & status (markdown)
│   ├── LOG.md                    1634 L  Master changelog; current state, axiom hygiene, layer status, Φ pipeline (2026-05-05)
│   ├── plan-era-graded-not_R1.md  765 L  Plan for closing R1 via era-graded forward analysis; (Sub-plan E superseded — see plan-era-graded_D2-spine bound.md)
│   ├── plan-era-graded_D2-spine bound.md  695 L  Detailed Sub-plan E plan (2026-05-06); SUPERSEDED in §9 by 2-adic Path 1′ via lex(phi, macroMr) measure (math-on-paper check failed Φ-only bound; scout_2adic validates lex measure)
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

       era_orbit_2adic.lean
               ▲
               │
        era_orbit_cascade.lean (base)
               ▲
               │
        era_orbit_cascade_chains.lean (21 chain helpers, 3 sorries)
               ▲   ▲
               │   │
               │   └─── era_orbit_cascade_d2.lean (D2 sub-case work, 3 sorries)
               │
        era_orbit_cascade_main.lean (cascade_strong_aux, 6 sorries)
```

`c1inv_abandoned.lean` imports only `BusyLean` and is not part of the
build chain.
