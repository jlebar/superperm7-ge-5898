/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CapTabs

namespace Superperm7.Cert.M1

theorem lvl47 : Fast.fsearch capTab1 47 (capTab1.getD 47 0 + 1) 1 (capTab1.getD 47 0 + 1) = false := by
  native_decide

end Superperm7.Cert.M1
