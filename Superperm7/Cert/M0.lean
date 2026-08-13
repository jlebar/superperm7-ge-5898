/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.Cert.M0.B00_49
import Superperm7.Cert.M0.L50
import Superperm7.Cert.M0.L51
import Superperm7.Cert.M0.L52
import Superperm7.Cert.M0.L53
import Superperm7.Cert.M0.L54
import Superperm7.Cert.M0.L55
import Superperm7.Cert.M0.L56

/-!
# Certified capacity table `capTab0` (at most 0 marked rows), charges `0 … 56`
-/

namespace Superperm7.Cert.M0

theorem valid_le (g : ℕ) (hg : g ≤ 56) : CapValidMuAt 0 capTab0 g := by
  induction g using Nat.strong_induction_on with
  | _ g ih =>
      have hbelow : CapsValidMuBelow 0 capTab0 g := fun g' hg' => ih g' hg' (by omega)
      apply capValidMu_step capTab0 0 g hbelow
      interval_cases g
      · exact lvl_of_batch_0_49 0 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 1 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 2 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 3 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 4 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 5 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 6 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 7 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 8 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 9 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 10 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 11 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 12 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 13 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 14 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 15 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 16 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 17 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 18 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 19 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 20 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 21 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 22 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 23 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 24 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 25 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 26 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 27 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 28 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 29 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 30 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 31 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 32 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 33 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 34 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 35 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 36 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 37 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 38 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 39 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 40 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 41 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 42 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 43 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 44 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 45 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 46 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 47 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 48 (by norm_num) (by norm_num)
      · exact lvl_of_batch_0_49 49 (by norm_num) (by norm_num)
      · exact lvl50
      · exact lvl51
      · exact lvl52
      · exact lvl53
      · exact lvl54
      · exact lvl55
      · exact lvl56

end Superperm7.Cert.M0

namespace Superperm7

/-- Every model trail with at most `0` marked rows and charge `≤ g ≤ 56` has at most `capTab0[g]` rows. -/
theorem capTab0_valid (g : ℕ) (hg : g ≤ 56) : CapValidMuAt 0 capTab0 g := Cert.M0.valid_le g hg

end Superperm7
