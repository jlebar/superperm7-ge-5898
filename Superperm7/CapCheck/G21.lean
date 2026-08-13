/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CapTab

namespace Superperm7.CapCheck

/-- No model marked trail of charge `≤ 21` has `42` rows (search certificate). -/
theorem chk21 : search capTab 21 42 true 42 = false := by native_decide

end Superperm7.CapCheck
