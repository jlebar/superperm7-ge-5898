/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.Main
import Superperm7.Bound5897

/-! Print the axioms the headline theorems depend on.  Expected: `propext`, `Classical.choice`,
`Quot.sound`, and `native_decide` evaluation certificates (`*._native.native_decide.*`); no `sorryAx`. -/

#print axioms Superperm7.main_theorem        -- 5898 ≤ s(7) ≤ 5906
#print axioms Superperm7.lower_bound         -- ∀ w, IsSuperpermutation w → 5898 ≤ w.length
#print axioms Superperm7.lower_bound_5897    -- the cheaper independent bound (Bound5897.lean)
