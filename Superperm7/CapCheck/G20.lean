/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CapTab

namespace Superperm7.CapCheck

/-- No model marked trail of charge `≤ 20` has `41` rows (search certificate). -/
theorem chk20 : search capTab 20 41 true 41 = false := by native_decide

end Superperm7.CapCheck
