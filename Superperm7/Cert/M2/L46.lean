/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.Cert.M2.L46S000
import Superperm7.Cert.M2.L46S001
import Superperm7.Cert.M2.L46S002
import Superperm7.Cert.M2.L46S003

namespace Superperm7.Cert.M2

theorem cover46 : (Fast.frontier capTab2 46 81 2 14).length ≤ 2707 * 4 := by native_decide

theorem lvl46_lit : Fast.fsearch capTab2 46 81 2 (67 + 14) = false := by
  apply Fast.fsearch_false_of_shards capTab2 46 81 2 14 67 2707 4 (by norm_num) (by norm_num) cover46
  intro i hi
  interval_cases i
  · exact sh46_0
  · exact sh46_1
  · exact sh46_2
  · exact sh46_3

theorem lvl46 : Fast.fsearch capTab2 46 (capTab2.getD 46 0 + 1) 2 (capTab2.getD 46 0 + 1) = false := by
  have h : capTab2.getD 46 0 + 1 = 81 := by decide
  rw [h]
  exact lvl46_lit

end Superperm7.Cert.M2
