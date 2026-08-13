/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.Cert.M1.L50S000
import Superperm7.Cert.M1.L50S001
import Superperm7.Cert.M1.L50S002
import Superperm7.Cert.M1.L50S003

namespace Superperm7.Cert.M1

theorem cover50 : (Fast.frontier capTab1 50 86 1 14).length ≤ 3264 * 4 := by native_decide

theorem lvl50_lit : Fast.fsearch capTab1 50 86 1 (72 + 14) = false := by
  apply Fast.fsearch_false_of_shards capTab1 50 86 1 14 72 3264 4 (by norm_num) (by norm_num) cover50
  intro i hi
  interval_cases i
  · exact sh50_0
  · exact sh50_1
  · exact sh50_2
  · exact sh50_3

theorem lvl50 : Fast.fsearch capTab1 50 (capTab1.getD 50 0 + 1) 1 (capTab1.getD 50 0 + 1) = false := by
  have h : capTab1.getD 50 0 + 1 = 86 := by decide
  rw [h]
  exact lvl50_lit

end Superperm7.Cert.M1
