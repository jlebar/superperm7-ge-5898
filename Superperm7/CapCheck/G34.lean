/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CapTab

namespace Superperm7.CapCheck

/-- No model marked trail of charge `≤ 34` has `64` rows (search certificate). -/
theorem chk34 : search capTab 34 64 true 64 = false := by native_decide

end Superperm7.CapCheck
