/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.Cert.M0.L56S000
import Superperm7.Cert.M0.L56S001
import Superperm7.Cert.M0.L56S002
import Superperm7.Cert.M0.L56S003
import Superperm7.Cert.M0.L56S004
import Superperm7.Cert.M0.L56S005
import Superperm7.Cert.M0.L56S006
import Superperm7.Cert.M0.L56S007

namespace Superperm7.Cert.M0

theorem cover56 : (Fast.frontier capTab0 56 94 0 14).length ≤ 955 * 8 := by native_decide

theorem lvl56_lit : Fast.fsearch capTab0 56 94 0 (80 + 14) = false := by
  apply Fast.fsearch_false_of_shards capTab0 56 94 0 14 80 955 8 (by norm_num) (by norm_num) cover56
  intro i hi
  interval_cases i
  · exact sh56_0
  · exact sh56_1
  · exact sh56_2
  · exact sh56_3
  · exact sh56_4
  · exact sh56_5
  · exact sh56_6
  · exact sh56_7

theorem lvl56 : Fast.fsearch capTab0 56 (capTab0.getD 56 0 + 1) 0 (capTab0.getD 56 0 + 1) = false := by
  have h : capTab0.getD 56 0 + 1 = 94 := by decide
  rw [h]
  exact lvl56_lit

end Superperm7.Cert.M0
