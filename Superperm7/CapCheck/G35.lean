/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CapTab

namespace Superperm7.CapCheck

/-- No model marked trail of charge `≤ 35` has `65` rows (search certificate). -/
theorem chk35 : search capTab 35 65 true 65 = false := by native_decide

end Superperm7.CapCheck
