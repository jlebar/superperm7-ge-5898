/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CapTab

namespace Superperm7.CapCheck

/-- No model marked trail of charge `≤ 15` has `32` rows (search certificate). -/
theorem chk15 : search capTab 15 32 true 32 = false := by native_decide

end Superperm7.CapCheck
