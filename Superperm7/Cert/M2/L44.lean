/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.Cert.M2.L44S000
import Superperm7.Cert.M2.L44S001
import Superperm7.Cert.M2.L44S002
import Superperm7.Cert.M2.L44S003
import Superperm7.Cert.M2.L44S004
import Superperm7.Cert.M2.L44S005
import Superperm7.Cert.M2.L44S006

namespace Superperm7.Cert.M2

theorem cover44 : (Fast.frontier capTab2 44 78 2 14).length ≤ 3122 * 7 := by native_decide

theorem lvl44_lit : Fast.fsearch capTab2 44 78 2 (64 + 14) = false := by
  apply Fast.fsearch_false_of_shards capTab2 44 78 2 14 64 3122 7 (by norm_num) (by norm_num) cover44
  intro i hi
  interval_cases i
  · exact sh44_0
  · exact sh44_1
  · exact sh44_2
  · exact sh44_3
  · exact sh44_4
  · exact sh44_5
  · exact sh44_6

theorem lvl44 : Fast.fsearch capTab2 44 (capTab2.getD 44 0 + 1) 2 (capTab2.getD 44 0 + 1) = false := by
  have h : capTab2.getD 44 0 + 1 = 78 := by decide
  rw [h]
  exact lvl44_lit

end Superperm7.Cert.M2
