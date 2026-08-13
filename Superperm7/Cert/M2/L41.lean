/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.Cert.M2.L41S000
import Superperm7.Cert.M2.L41S001
import Superperm7.Cert.M2.L41S002

namespace Superperm7.Cert.M2

theorem cover41 : (Fast.frontier capTab2 41 73 2 14).length ≤ 5431 * 3 := by native_decide

theorem lvl41_lit : Fast.fsearch capTab2 41 73 2 (59 + 14) = false := by
  apply Fast.fsearch_false_of_shards capTab2 41 73 2 14 59 5431 3 (by norm_num) (by norm_num) cover41
  intro i hi
  interval_cases i
  · exact sh41_0
  · exact sh41_1
  · exact sh41_2

theorem lvl41 : Fast.fsearch capTab2 41 (capTab2.getD 41 0 + 1) 2 (capTab2.getD 41 0 + 1) = false := by
  have h : capTab2.getD 41 0 + 1 = 73 := by decide
  rw [h]
  exact lvl41_lit

end Superperm7.Cert.M2
