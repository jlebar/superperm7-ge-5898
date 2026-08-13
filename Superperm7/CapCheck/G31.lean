/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CapTab

namespace Superperm7.CapCheck

/-- No model marked trail of charge `≤ 31` has `58` rows (search certificate). -/
theorem chk31 : search capTab 31 58 true 58 = false := by native_decide

end Superperm7.CapCheck
