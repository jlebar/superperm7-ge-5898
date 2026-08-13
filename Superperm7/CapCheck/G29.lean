/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CapTab

namespace Superperm7.CapCheck

/-- No model marked trail of charge `≤ 29` has `55` rows (search certificate). -/
theorem chk29 : search capTab 29 55 true 55 = false := by native_decide

end Superperm7.CapCheck
