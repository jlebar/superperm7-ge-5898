/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CapTab

namespace Superperm7.CapCheck

/-- No model marked trail of charge `≤ 24` has `47` rows (search certificate). -/
theorem chk24 : search capTab 24 47 true 47 = false := by native_decide

end Superperm7.CapCheck
