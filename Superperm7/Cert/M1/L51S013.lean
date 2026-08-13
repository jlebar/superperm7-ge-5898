/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CapTabs

namespace Superperm7.Cert.M1

/-- shard 13/15 of level 51 (mu = 1): frontier depth 16, states [38545, 41510) -/
theorem sh51_13 : Fast.shardOK capTab1 51 87 1 16 71 (2965 * 13) 2965 = true := by
  native_decide

end Superperm7.Cert.M1
