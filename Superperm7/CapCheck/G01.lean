/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CapTab

namespace Superperm7.CapCheck

/-- No model marked trail of charge `≤ 1` has `6` rows (search certificate). -/
theorem chk01 : search capTab 1 6 true 6 = false := by native_decide

end Superperm7.CapCheck
