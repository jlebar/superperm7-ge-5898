/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.Cert.M1.L51S000
import Superperm7.Cert.M1.L51S001
import Superperm7.Cert.M1.L51S002
import Superperm7.Cert.M1.L51S003
import Superperm7.Cert.M1.L51S004
import Superperm7.Cert.M1.L51S005
import Superperm7.Cert.M1.L51S006
import Superperm7.Cert.M1.L51S007
import Superperm7.Cert.M1.L51S008
import Superperm7.Cert.M1.L51S009
import Superperm7.Cert.M1.L51S010
import Superperm7.Cert.M1.L51S011
import Superperm7.Cert.M1.L51S012
import Superperm7.Cert.M1.L51S013
import Superperm7.Cert.M1.L51S014

namespace Superperm7.Cert.M1

theorem cover51 : (Fast.frontier capTab1 51 87 1 16).length ≤ 2965 * 15 := by native_decide

theorem lvl51_lit : Fast.fsearch capTab1 51 87 1 (71 + 16) = false := by
  apply Fast.fsearch_false_of_shards capTab1 51 87 1 16 71 2965 15 (by norm_num) (by norm_num) cover51
  intro i hi
  interval_cases i
  · exact sh51_0
  · exact sh51_1
  · exact sh51_2
  · exact sh51_3
  · exact sh51_4
  · exact sh51_5
  · exact sh51_6
  · exact sh51_7
  · exact sh51_8
  · exact sh51_9
  · exact sh51_10
  · exact sh51_11
  · exact sh51_12
  · exact sh51_13
  · exact sh51_14

theorem lvl51 : Fast.fsearch capTab1 51 (capTab1.getD 51 0 + 1) 1 (capTab1.getD 51 0 + 1) = false := by
  have h : capTab1.getD 51 0 + 1 = 87 := by decide
  rw [h]
  exact lvl51_lit

end Superperm7.Cert.M1
