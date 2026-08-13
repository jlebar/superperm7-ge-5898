/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CapTab

namespace Superperm7.CapCheck

/-- No model marked trail of charge `≤ 18` has `37` rows (search certificate). -/
theorem chk18 : search capTab 18 37 true 37 = false := by native_decide

end Superperm7.CapCheck
