/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CapTab

namespace Superperm7.CapCheck

/-- No model marked trail of charge `≤ 0` has `6` rows (search certificate). -/
theorem chk00 : search capTab 0 6 true 6 = false := by native_decide

end Superperm7.CapCheck
