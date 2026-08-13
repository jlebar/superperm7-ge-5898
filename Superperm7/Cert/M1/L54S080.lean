/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CapTabs

namespace Superperm7.Cert.M1

/-- shard 80/120 of level 54 (mu = 1): frontier depth 16, states [13840, 14013) -/
theorem sh54_80 : Fast.shardOK capTab1 54 92 1 16 76 (173 * 80) 173 = true := by
  native_decide

end Superperm7.Cert.M1
