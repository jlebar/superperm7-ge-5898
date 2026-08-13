/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CapTab

namespace Superperm7.CapCheck

/-- No model marked trail of charge `≤ 22` has `44` rows (search certificate). -/
theorem chk22 : search capTab 22 44 true 44 = false := by native_decide

end Superperm7.CapCheck
