/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.Cert.M1.L53S000
import Superperm7.Cert.M1.L53S001
import Superperm7.Cert.M1.L53S002
import Superperm7.Cert.M1.L53S003
import Superperm7.Cert.M1.L53S004
import Superperm7.Cert.M1.L53S005
import Superperm7.Cert.M1.L53S006
import Superperm7.Cert.M1.L53S007
import Superperm7.Cert.M1.L53S008
import Superperm7.Cert.M1.L53S009
import Superperm7.Cert.M1.L53S010
import Superperm7.Cert.M1.L53S011
import Superperm7.Cert.M1.L53S012
import Superperm7.Cert.M1.L53S013
import Superperm7.Cert.M1.L53S014
import Superperm7.Cert.M1.L53S015
import Superperm7.Cert.M1.L53S016
import Superperm7.Cert.M1.L53S017
import Superperm7.Cert.M1.L53S018
import Superperm7.Cert.M1.L53S019
import Superperm7.Cert.M1.L53S020
import Superperm7.Cert.M1.L53S021
import Superperm7.Cert.M1.L53S022
import Superperm7.Cert.M1.L53S023
import Superperm7.Cert.M1.L53S024
import Superperm7.Cert.M1.L53S025
import Superperm7.Cert.M1.L53S026
import Superperm7.Cert.M1.L53S027
import Superperm7.Cert.M1.L53S028
import Superperm7.Cert.M1.L53S029

namespace Superperm7.Cert.M1

theorem cover53 : (Fast.frontier capTab1 53 90 1 16).length ≤ 1421 * 30 := by native_decide

theorem lvl53_lit : Fast.fsearch capTab1 53 90 1 (74 + 16) = false := by
  apply Fast.fsearch_false_of_shards capTab1 53 90 1 16 74 1421 30 (by norm_num) (by norm_num) cover53
  intro i hi
  interval_cases i
  · exact sh53_0
  · exact sh53_1
  · exact sh53_2
  · exact sh53_3
  · exact sh53_4
  · exact sh53_5
  · exact sh53_6
  · exact sh53_7
  · exact sh53_8
  · exact sh53_9
  · exact sh53_10
  · exact sh53_11
  · exact sh53_12
  · exact sh53_13
  · exact sh53_14
  · exact sh53_15
  · exact sh53_16
  · exact sh53_17
  · exact sh53_18
  · exact sh53_19
  · exact sh53_20
  · exact sh53_21
  · exact sh53_22
  · exact sh53_23
  · exact sh53_24
  · exact sh53_25
  · exact sh53_26
  · exact sh53_27
  · exact sh53_28
  · exact sh53_29

theorem lvl53 : Fast.fsearch capTab1 53 (capTab1.getD 53 0 + 1) 1 (capTab1.getD 53 0 + 1) = false := by
  have h : capTab1.getD 53 0 + 1 = 90 := by decide
  rw [h]
  exact lvl53_lit

end Superperm7.Cert.M1
