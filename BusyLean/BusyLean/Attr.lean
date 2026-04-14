/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Lean.Meta.Tactic.Simp.Attr

/-! # BusyLean: simp attribute registrations

A dedicated file for simp attribute declarations. Lean 4 forbids declaring
and using an attribute in the same file, so we keep the `initialize` here
and tag its lemmas in `TapeNorm.lean`.
-/

open Lean Meta

/-- The `tape_norm` simp set used by the `es` tactic for tape normalization. -/
initialize tapeNormExt : SimpExtension ←
  registerSimpAttr `tape_norm "simp set for BusyLean tape normalization"

/-- The `tape_split` simp set used by `es`'s Stage 3 fallback to **split** an
    atom like `ones (2 + k)` into `ones 2 ++ ones k`. Goes the *opposite*
    direction of `tape_norm` (which merges) — the two sets are intentionally
    not used together because they would loop. -/
initialize tapeSplitExt : SimpExtension ←
  registerSimpAttr `tape_split "simp set for BusyLean tape splitting (Stage 3 fallback)"
