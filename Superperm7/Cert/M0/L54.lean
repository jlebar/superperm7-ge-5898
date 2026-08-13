/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.Cert.M0.L54S000
import Superperm7.Cert.M0.L54S001
import Superperm7.Cert.M0.L54S002
import Superperm7.Cert.M0.L54S003

namespace Superperm7.Cert.M0

theorem cover54 : (Fast.frontier capTab0 54 92 0 14).length ≤ 359 * 4 := by native_decide

theorem lvl54_lit : Fast.fsearch capTab0 54 92 0 (78 + 14) = false := by
  apply Fast.fsearch_false_of_shards capTab0 54 92 0 14 78 359 4 (by norm_num) (by norm_num) cover54
  intro i hi
  interval_cases i
  · exact sh54_0
  · exact sh54_1
  · exact sh54_2
  · exact sh54_3

theorem lvl54 : Fast.fsearch capTab0 54 (capTab0.getD 54 0 + 1) 0 (capTab0.getD 54 0 + 1) = false := by
  have h : capTab0.getD 54 0 + 1 = 92 := by decide
  rw [h]
  exact lvl54_lit

end Superperm7.Cert.M0
