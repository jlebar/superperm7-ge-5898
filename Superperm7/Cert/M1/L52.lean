/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.Cert.M1.L52S000
import Superperm7.Cert.M1.L52S001
import Superperm7.Cert.M1.L52S002
import Superperm7.Cert.M1.L52S003
import Superperm7.Cert.M1.L52S004
import Superperm7.Cert.M1.L52S005
import Superperm7.Cert.M1.L52S006
import Superperm7.Cert.M1.L52S007
import Superperm7.Cert.M1.L52S008
import Superperm7.Cert.M1.L52S009
import Superperm7.Cert.M1.L52S010
import Superperm7.Cert.M1.L52S011
import Superperm7.Cert.M1.L52S012
import Superperm7.Cert.M1.L52S013
import Superperm7.Cert.M1.L52S014
import Superperm7.Cert.M1.L52S015
import Superperm7.Cert.M1.L52S016
import Superperm7.Cert.M1.L52S017
import Superperm7.Cert.M1.L52S018
import Superperm7.Cert.M1.L52S019
import Superperm7.Cert.M1.L52S020
import Superperm7.Cert.M1.L52S021
import Superperm7.Cert.M1.L52S022
import Superperm7.Cert.M1.L52S023
import Superperm7.Cert.M1.L52S024
import Superperm7.Cert.M1.L52S025
import Superperm7.Cert.M1.L52S026
import Superperm7.Cert.M1.L52S027
import Superperm7.Cert.M1.L52S028
import Superperm7.Cert.M1.L52S029
import Superperm7.Cert.M1.L52S030
import Superperm7.Cert.M1.L52S031
import Superperm7.Cert.M1.L52S032
import Superperm7.Cert.M1.L52S033
import Superperm7.Cert.M1.L52S034

namespace Superperm7.Cert.M1

theorem cover52 : (Fast.frontier capTab1 52 89 1 16).length ≤ 605 * 35 := by native_decide

theorem lvl52_lit : Fast.fsearch capTab1 52 89 1 (73 + 16) = false := by
  apply Fast.fsearch_false_of_shards capTab1 52 89 1 16 73 605 35 (by norm_num) (by norm_num) cover52
  intro i hi
  interval_cases i
  · exact sh52_0
  · exact sh52_1
  · exact sh52_2
  · exact sh52_3
  · exact sh52_4
  · exact sh52_5
  · exact sh52_6
  · exact sh52_7
  · exact sh52_8
  · exact sh52_9
  · exact sh52_10
  · exact sh52_11
  · exact sh52_12
  · exact sh52_13
  · exact sh52_14
  · exact sh52_15
  · exact sh52_16
  · exact sh52_17
  · exact sh52_18
  · exact sh52_19
  · exact sh52_20
  · exact sh52_21
  · exact sh52_22
  · exact sh52_23
  · exact sh52_24
  · exact sh52_25
  · exact sh52_26
  · exact sh52_27
  · exact sh52_28
  · exact sh52_29
  · exact sh52_30
  · exact sh52_31
  · exact sh52_32
  · exact sh52_33
  · exact sh52_34

theorem lvl52 : Fast.fsearch capTab1 52 (capTab1.getD 52 0 + 1) 1 (capTab1.getD 52 0 + 1) = false := by
  have h : capTab1.getD 52 0 + 1 = 89 := by decide
  rw [h]
  exact lvl52_lit

end Superperm7.Cert.M1
