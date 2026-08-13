/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).

UNTRUSTED (checked by comparator / by `#print axioms`): the challenge statements, proved by delegating to
the `Superperm7` library (`Superperm7.verified_upper_bound`, `Superperm7.lower_bound_5897`,
`Superperm7.lower_bound`).  `ChallengeDeps.IsSuperpermutation` and `Superperm7.IsSuperpermutation` are
syntactically identical definitions over Mathlib, so the bridge is definitional unfolding (`Iff.rfl`).
-/
import ChallengeDeps
import Superperm7.Main
import Superperm7.Bound5897
open ChallengeDeps

theorem isSuperpermutation_iff (w : Word) :
    ChallengeDeps.IsSuperpermutation w ↔ Superperm7.IsSuperpermutation w := Iff.rfl

theorem superperm7_upper_5906 : ∃ w : Word, IsSuperpermutation w ∧ w.length = 5906 :=
  Superperm7.verified_upper_bound

theorem superperm7_lower_5897 : ∀ w : Word, IsSuperpermutation w → 5897 ≤ w.length :=
  fun w h => Superperm7.lower_bound_5897 w ((isSuperpermutation_iff w).1 h)

theorem superperm7_lower_5898 : ∀ w : Word, IsSuperpermutation w → 5898 ≤ w.length :=
  fun w h => Superperm7.lower_bound w ((isSuperpermutation_iff w).1 h)
