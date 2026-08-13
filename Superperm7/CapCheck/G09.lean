/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CapTab

namespace Superperm7.CapCheck

/-- No model marked trail of charge `≤ 9` has `21` rows (search certificate). -/
theorem chk09 : search capTab 9 21 true 21 = false := by native_decide

end Superperm7.CapCheck
