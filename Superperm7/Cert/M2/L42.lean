/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.Cert.M2.L42S000
import Superperm7.Cert.M2.L42S001
import Superperm7.Cert.M2.L42S002
import Superperm7.Cert.M2.L42S003
import Superperm7.Cert.M2.L42S004
import Superperm7.Cert.M2.L42S005
import Superperm7.Cert.M2.L42S006
import Superperm7.Cert.M2.L42S007

namespace Superperm7.Cert.M2

theorem cover42 : (Fast.frontier capTab2 42 75 2 14).length ≤ 1255 * 8 := by native_decide

theorem lvl42_lit : Fast.fsearch capTab2 42 75 2 (61 + 14) = false := by
  apply Fast.fsearch_false_of_shards capTab2 42 75 2 14 61 1255 8 (by norm_num) (by norm_num) cover42
  intro i hi
  interval_cases i
  · exact sh42_0
  · exact sh42_1
  · exact sh42_2
  · exact sh42_3
  · exact sh42_4
  · exact sh42_5
  · exact sh42_6
  · exact sh42_7

theorem lvl42 : Fast.fsearch capTab2 42 (capTab2.getD 42 0 + 1) 2 (capTab2.getD 42 0 + 1) = false := by
  have h : capTab2.getD 42 0 + 1 = 75 := by decide
  rw [h]
  exact lvl42_lit

end Superperm7.Cert.M2
