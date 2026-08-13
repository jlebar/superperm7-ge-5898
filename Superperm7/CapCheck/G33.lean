/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CapTab

namespace Superperm7.CapCheck

/-- No model marked trail of charge `≤ 33` has `61` rows (search certificate). -/
theorem chk33 : search capTab 33 61 true 61 = false := by native_decide

end Superperm7.CapCheck
