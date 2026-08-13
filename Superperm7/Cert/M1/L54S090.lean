/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CapTabs

namespace Superperm7.Cert.M1

/-- shard 90/120 of level 54 (mu = 1): frontier depth 16, states [15570, 15743) -/
theorem sh54_90 : Fast.shardOK capTab1 54 92 1 16 76 (173 * 90) 173 = true := by
  native_decide

end Superperm7.Cert.M1
