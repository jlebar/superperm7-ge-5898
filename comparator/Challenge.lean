/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).

TRUSTED FILE (read it).  The statements, with placeholder proofs.  `Solution.lean` proves exactly
these; comparator checks statement equality and the axioms used.
-/
import ChallengeDeps

open ChallengeDeps

/-- Some superpermutation on seven symbols has length 5906 (the Egan–Houston word of 2019; not new). -/
theorem superperm7_upper_5906 : ∃ w : Word, IsSuperpermutation w ∧ w.length = 5906 := by
  sorry

/-- Every superpermutation on seven symbols has length at least 5897. -/
theorem superperm7_lower_5897 : ∀ w : Word, IsSuperpermutation w → 5897 ≤ w.length := by
  sorry

/-- Every superpermutation on seven symbols has length at least 5898. -/
theorem superperm7_lower_5898 : ∀ w : Word, IsSuperpermutation w → 5898 ≤ w.length := by
  sorry
