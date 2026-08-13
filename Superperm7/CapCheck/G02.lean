/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CapTab

namespace Superperm7.CapCheck

/-- No model marked trail of charge `≤ 2` has `10` rows (search certificate). -/
theorem chk02 : search capTab 2 10 true 10 = false := by native_decide

end Superperm7.CapCheck
