/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CapTabs

namespace Superperm7.Cert.M1

/-- shard 13/35 of level 52 (mu = 1): frontier depth 16, states [7865, 8470) -/
theorem sh52_13 : Fast.shardOK capTab1 52 89 1 16 73 (605 * 13) 605 = true := by
  native_decide

end Superperm7.Cert.M1
