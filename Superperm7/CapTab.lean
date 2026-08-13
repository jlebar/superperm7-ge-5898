/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.SearchSound

namespace Superperm7

/-- The single-trail capacity table for `g = 0 … 36` at `n = 7`: `capTab[g]` bounds from above the
number of rows of a model marked trail with total charge `≤ g` (certified in `CapCheck/*` /
`CapTable.lean` by failed searches for `capTab[g] + 1` rows).  The entries are in fact the exact maxima
found by search, but only the upper bound is proved or used. -/
def capTab : Array Nat :=
  #[5, 5, 9, 9, 13, 13, 16, 16, 20, 20, 24, 24, 27, 27, 31, 31, 34, 34, 36, 38, 40, 41, 43, 44, 46, 47, 50, 51, 52, 54, 56, 57, 59, 60, 63, 64, 66]

theorem capTab_size : capTab.size = 37 := rfl

end Superperm7
