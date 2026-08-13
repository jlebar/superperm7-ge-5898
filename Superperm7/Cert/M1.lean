/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.Cert.M1.B00_40
import Superperm7.Cert.M1.B41_44
import Superperm7.Cert.M1.L45
import Superperm7.Cert.M1.L46
import Superperm7.Cert.M1.L47
import Superperm7.Cert.M1.L48
import Superperm7.Cert.M1.L49
import Superperm7.Cert.M1.L50
import Superperm7.Cert.M1.L51
import Superperm7.Cert.M1.L52
import Superperm7.Cert.M1.L53
import Superperm7.Cert.M1.L54

/-!
# Certified capacity table `capTab1` (at most 1 marked row), charges `0 … 54`
-/

namespace Superperm7.Cert.M1

theorem valid_le (g : ℕ) (hg : g ≤ 54) : CapValidMuAt 1 capTab1 g := by
  induction g using Nat.strong_induction_on with
  | _ g ih =>
      have hbelow : CapsValidMuBelow 1 capTab1 g := fun g' hg' => ih g' hg' (by omega)
      apply capValidMu_step capTab1 1 g hbelow
      interval_cases g
      · exact lvl_of_batch_0_40 0 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_40 1 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_40 2 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_40 3 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_40 4 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_40 5 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_40 6 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_40 7 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_40 8 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_40 9 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_40 10 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_40 11 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_40 12 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_40 13 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_40 14 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_40 15 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_40 16 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_40 17 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_40 18 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_40 19 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_40 20 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_40 21 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_40 22 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_40 23 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_40 24 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_40 25 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_40 26 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_40 27 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_40 28 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_40 29 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_40 30 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_40 31 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_40 32 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_40 33 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_40 34 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_40 35 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_40 36 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_40 37 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_40 38 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_40 39 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_40 40 (by norm_num) (by norm_num)
      · exact lvl_of_batch_41_44 41 (by norm_num) (by norm_num)
      · exact lvl_of_batch_41_44 42 (by norm_num) (by norm_num)
      · exact lvl_of_batch_41_44 43 (by norm_num) (by norm_num)
      · exact lvl_of_batch_41_44 44 (by norm_num) (by norm_num)
      · exact lvl45
      · exact lvl46
      · exact lvl47
      · exact lvl48
      · exact lvl49
      · exact lvl50
      · exact lvl51
      · exact lvl52
      · exact lvl53
      · exact lvl54

end Superperm7.Cert.M1

namespace Superperm7

/-- Every model trail with at most `1` marked rows and charge `≤ g ≤ 54` has at most `capTab1[g]` rows. -/
theorem capTab1_valid (g : ℕ) (hg : g ≤ 54) : CapValidMuAt 1 capTab1 g := Cert.M1.valid_le g hg

end Superperm7
