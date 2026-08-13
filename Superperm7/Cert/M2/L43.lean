/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.Cert.M2.L43S000
import Superperm7.Cert.M2.L43S001
import Superperm7.Cert.M2.L43S002
import Superperm7.Cert.M2.L43S003

namespace Superperm7.Cert.M2

theorem cover43 : (Fast.frontier capTab2 43 76 2 14).length ≤ 5561 * 4 := by native_decide

theorem lvl43_lit : Fast.fsearch capTab2 43 76 2 (62 + 14) = false := by
  apply Fast.fsearch_false_of_shards capTab2 43 76 2 14 62 5561 4 (by norm_num) (by norm_num) cover43
  intro i hi
  interval_cases i
  · exact sh43_0
  · exact sh43_1
  · exact sh43_2
  · exact sh43_3

theorem lvl43 : Fast.fsearch capTab2 43 (capTab2.getD 43 0 + 1) 2 (capTab2.getD 43 0 + 1) = false := by
  have h : capTab2.getD 43 0 + 1 = 76 := by decide
  rw [h]
  exact lvl43_lit

end Superperm7.Cert.M2
