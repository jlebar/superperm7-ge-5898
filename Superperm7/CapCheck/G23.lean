/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CapTab

namespace Superperm7.CapCheck

/-- No model marked trail of charge `≤ 23` has `45` rows (search certificate). -/
theorem chk23 : search capTab 23 45 true 45 = false := by native_decide

end Superperm7.CapCheck
