/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.Cert.M2.L45S000
import Superperm7.Cert.M2.L45S001
import Superperm7.Cert.M2.L45S002
import Superperm7.Cert.M2.L45S003
import Superperm7.Cert.M2.L45S004
import Superperm7.Cert.M2.L45S005

namespace Superperm7.Cert.M2

theorem cover45 : (Fast.frontier capTab2 45 80 2 14).length ≤ 528 * 6 := by native_decide

theorem lvl45_lit : Fast.fsearch capTab2 45 80 2 (66 + 14) = false := by
  apply Fast.fsearch_false_of_shards capTab2 45 80 2 14 66 528 6 (by norm_num) (by norm_num) cover45
  intro i hi
  interval_cases i
  · exact sh45_0
  · exact sh45_1
  · exact sh45_2
  · exact sh45_3
  · exact sh45_4
  · exact sh45_5

theorem lvl45 : Fast.fsearch capTab2 45 (capTab2.getD 45 0 + 1) 2 (capTab2.getD 45 0 + 1) = false := by
  have h : capTab2.getD 45 0 + 1 = 80 := by decide
  rw [h]
  exact lvl45_lit

end Superperm7.Cert.M2
