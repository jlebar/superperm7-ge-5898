/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CapTab

namespace Superperm7.CapCheck

/-- No model marked trail of charge `≤ 36` has `67` rows (search certificate). -/
theorem chk36 : search capTab 36 67 true 67 = false := by native_decide

end Superperm7.CapCheck
