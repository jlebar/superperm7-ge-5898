/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CapTab

namespace Superperm7.CapCheck

/-- No model marked trail of charge `≤ 32` has `60` rows (search certificate). -/
theorem chk32 : search capTab 32 60 true 60 = false := by native_decide

end Superperm7.CapCheck
