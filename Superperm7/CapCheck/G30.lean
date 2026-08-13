/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CapTab

namespace Superperm7.CapCheck

/-- No model marked trail of charge `≤ 30` has `57` rows (search certificate). -/
theorem chk30 : search capTab 30 57 true 57 = false := by native_decide

end Superperm7.CapCheck
