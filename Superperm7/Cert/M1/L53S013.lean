/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CapTabs

namespace Superperm7.Cert.M1

/-- shard 13/30 of level 53 (mu = 1): frontier depth 16, states [18473, 19894) -/
theorem sh53_13 : Fast.shardOK capTab1 53 90 1 16 74 (1421 * 13) 1421 = true := by
  native_decide

end Superperm7.Cert.M1
