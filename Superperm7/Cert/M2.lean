/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.Cert.M2.B00_37
import Superperm7.Cert.M2.B38_40
import Superperm7.Cert.M2.L41
import Superperm7.Cert.M2.L42
import Superperm7.Cert.M2.L43
import Superperm7.Cert.M2.L44
import Superperm7.Cert.M2.L45
import Superperm7.Cert.M2.L46

/-!
# Certified capacity table `capTab2` (at most 2 marked rows), charges `0 … 46`
-/

namespace Superperm7.Cert.M2

theorem valid_le (g : ℕ) (hg : g ≤ 46) : CapValidMuAt 2 capTab2 g := by
  induction g using Nat.strong_induction_on with
  | _ g ih =>
      have hbelow : CapsValidMuBelow 2 capTab2 g := fun g' hg' => ih g' hg' (by omega)
      apply capValidMu_step capTab2 2 g hbelow
      interval_cases g
      · exact lvl_of_batch_0_37 0 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_37 1 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_37 2 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_37 3 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_37 4 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_37 5 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_37 6 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_37 7 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_37 8 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_37 9 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_37 10 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_37 11 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_37 12 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_37 13 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_37 14 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_37 15 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_37 16 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_37 17 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_37 18 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_37 19 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_37 20 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_37 21 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_37 22 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_37 23 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_37 24 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_37 25 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_37 26 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_37 27 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_37 28 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_37 29 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_37 30 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_37 31 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_37 32 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_37 33 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_37 34 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_37 35 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_37 36 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_37 37 (by norm_num) (by norm_num)
      · exact lvl_of_batch_38_40 38 (by norm_num) (by norm_num)
      · exact lvl_of_batch_38_40 39 (by norm_num) (by norm_num)
      · exact lvl_of_batch_38_40 40 (by norm_num) (by norm_num)
      · exact lvl41
      · exact lvl42
      · exact lvl43
      · exact lvl44
      · exact lvl45
      · exact lvl46

end Superperm7.Cert.M2

namespace Superperm7

/-- Every model trail with at most `2` marked rows and charge `≤ g ≤ 46` has at most `capTab2[g]` rows. -/
theorem capTab2_valid (g : ℕ) (hg : g ≤ 46) : CapValidMuAt 2 capTab2 g := Cert.M2.valid_le g hg

end Superperm7
