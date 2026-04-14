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
