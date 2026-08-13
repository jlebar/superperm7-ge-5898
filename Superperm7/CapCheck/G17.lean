/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CapTab

namespace Superperm7.CapCheck

/-- No model marked trail of charge `≤ 17` has `35` rows (search certificate). -/
theorem chk17 : search capTab 17 35 true 35 = false := by native_decide

end Superperm7.CapCheck
