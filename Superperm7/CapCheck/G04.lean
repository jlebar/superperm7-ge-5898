/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CapTab

namespace Superperm7.CapCheck

/-- No model marked trail of charge `≤ 4` has `14` rows (search certificate). -/
theorem chk04 : search capTab 4 14 true 14 = false := by native_decide

end Superperm7.CapCheck
