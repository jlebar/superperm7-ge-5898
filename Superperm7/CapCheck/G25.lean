/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CapTab

namespace Superperm7.CapCheck

/-- No model marked trail of charge `≤ 25` has `48` rows (search certificate). -/
theorem chk25 : search capTab 25 48 true 48 = false := by native_decide

end Superperm7.CapCheck
