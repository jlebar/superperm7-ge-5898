/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CapTab

namespace Superperm7.CapCheck

/-- No model marked trail of charge `≤ 13` has `28` rows (search certificate). -/
theorem chk13 : search capTab 13 28 true 28 = false := by native_decide

end Superperm7.CapCheck
