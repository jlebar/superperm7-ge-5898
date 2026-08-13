/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.EqChecks.J3636
import Superperm7.EqChecks.J161634
import Superperm7.EqChecks.J142626
import Superperm7.EqChecks.J141636
import Superperm7.EqChecks.J14141616

/-! # The five template-join impossibility facts (evaluated in separate modules) -/

namespace Superperm7

theorem joins_checked :
    joinImpossible 36 [36] = true ∧ joinImpossible 16 [16, 34] = true ∧
    joinImpossible 14 [26, 26] = true ∧ joinImpossible 14 [16, 36] = true ∧
    joinImpossible 14 [14, 16, 16] = true :=
  ⟨EqChecks.j3636, EqChecks.j161634, EqChecks.j142626, EqChecks.j141636, EqChecks.j14141616⟩

end Superperm7
