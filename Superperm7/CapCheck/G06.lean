/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CapTab

namespace Superperm7.CapCheck

/-- No model marked trail of charge `≤ 6` has `17` rows (search certificate). -/
theorem chk06 : search capTab 6 17 true 17 = false := by native_decide

end Superperm7.CapCheck
