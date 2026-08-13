/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CapTab

namespace Superperm7.CapCheck

/-- No model marked trail of charge `≤ 26` has `51` rows (search certificate). -/
theorem chk26 : search capTab 26 51 true 51 = false := by native_decide

end Superperm7.CapCheck
