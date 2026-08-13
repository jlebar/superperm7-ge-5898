/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CapTab

namespace Superperm7.CapCheck

/-- No model marked trail of charge `≤ 11` has `25` rows (search certificate). -/
theorem chk11 : search capTab 11 25 true 25 = false := by native_decide

end Superperm7.CapCheck
