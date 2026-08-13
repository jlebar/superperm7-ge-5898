/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CapCheck.G00
import Superperm7.CapCheck.G01
import Superperm7.CapCheck.G02
import Superperm7.CapCheck.G03
import Superperm7.CapCheck.G04
import Superperm7.CapCheck.G05
import Superperm7.CapCheck.G06
import Superperm7.CapCheck.G07
import Superperm7.CapCheck.G08
import Superperm7.CapCheck.G09
import Superperm7.CapCheck.G10
import Superperm7.CapCheck.G11
import Superperm7.CapCheck.G12
import Superperm7.CapCheck.G13
import Superperm7.CapCheck.G14
import Superperm7.CapCheck.G15
import Superperm7.CapCheck.G16
import Superperm7.CapCheck.G17
import Superperm7.CapCheck.G18
import Superperm7.CapCheck.G19
import Superperm7.CapCheck.G20
import Superperm7.CapCheck.G21
import Superperm7.CapCheck.G22
import Superperm7.CapCheck.G23
import Superperm7.CapCheck.G24
import Superperm7.CapCheck.G25
import Superperm7.CapCheck.G26
import Superperm7.CapCheck.G27
import Superperm7.CapCheck.G28
import Superperm7.CapCheck.G29
import Superperm7.CapCheck.G30
import Superperm7.CapCheck.G31
import Superperm7.CapCheck.G32
import Superperm7.CapCheck.G33
import Superperm7.CapCheck.G34
import Superperm7.CapCheck.G35
import Superperm7.CapCheck.G36

/-!
# The certified capacity table through charge 36

Each `CapCheck.chkNN` is a `native_decide` evaluation of the reflected search;
together with the completeness theorem they give: every model marked trail of
charge `≤ g ≤ 36` has at most `capTab[g]` rows.
-/

namespace Superperm7

theorem capTab_checked : capsChecked capTab 36 = true := by
  unfold capsChecked
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq]
  intro g hg
  interval_cases g
  · exact CapCheck.chk00
  · exact CapCheck.chk01
  · exact CapCheck.chk02
  · exact CapCheck.chk03
  · exact CapCheck.chk04
  · exact CapCheck.chk05
  · exact CapCheck.chk06
  · exact CapCheck.chk07
  · exact CapCheck.chk08
  · exact CapCheck.chk09
  · exact CapCheck.chk10
  · exact CapCheck.chk11
  · exact CapCheck.chk12
  · exact CapCheck.chk13
  · exact CapCheck.chk14
  · exact CapCheck.chk15
  · exact CapCheck.chk16
  · exact CapCheck.chk17
  · exact CapCheck.chk18
  · exact CapCheck.chk19
  · exact CapCheck.chk20
  · exact CapCheck.chk21
  · exact CapCheck.chk22
  · exact CapCheck.chk23
  · exact CapCheck.chk24
  · exact CapCheck.chk25
  · exact CapCheck.chk26
  · exact CapCheck.chk27
  · exact CapCheck.chk28
  · exact CapCheck.chk29
  · exact CapCheck.chk30
  · exact CapCheck.chk31
  · exact CapCheck.chk32
  · exact CapCheck.chk33
  · exact CapCheck.chk34
  · exact CapCheck.chk35
  · exact CapCheck.chk36

/-- Every model marked trail of charge `≤ g` (`g ≤ 36`) has at most `capTab[g]` rows. -/
theorem modelTrail_length_le_capTab (g : ℕ) (hg : g ≤ 36) (rows : List MarkedRow)
    (hmodel : ModelTrail rows) (hcharge : chargeSum rows ≤ g) :
    rows.length ≤ capTab.getD g 0 :=
  capsValid_of_checked capTab 36 capTab_checked g hg rows hmodel hcharge

end Superperm7
