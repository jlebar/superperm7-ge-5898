/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CapTab

namespace Superperm7.CapCheck

/-- No model marked trail of charge `≤ 19` has `39` rows (search certificate). -/
theorem chk19 : search capTab 19 39 true 39 = false := by native_decide

end Superperm7.CapCheck
