/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CapTab

namespace Superperm7.CapCheck

/-- No model marked trail of charge `≤ 27` has `52` rows (search certificate). -/
theorem chk27 : search capTab 27 52 true 52 = false := by native_decide

end Superperm7.CapCheck
