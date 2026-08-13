/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CapTab

namespace Superperm7.CapCheck

/-- No model marked trail of charge `≤ 28` has `53` rows (search certificate). -/
theorem chk28 : search capTab 28 53 true 53 = false := by native_decide

end Superperm7.CapCheck
