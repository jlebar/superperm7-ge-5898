/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.Cube

/-!
# Capacity tables to be certified with the fast kernel

`capTab0` : upper bounds on the number of rows of a trail with charge `≤ g`, `g ≤ 56`, no marked row;
`capTab1` : the same values, `g ≤ 54`, certified for trails with at most one marked row;
`capTab2` : the same values, `g ≤ 46`, certified for trails with at most two marked rows.
Each entry is certified (in `Cert/M0`, `Cert/M1`, `Cert/M2`) by a failed search for one more row; the
values are the exact maxima found by search, but only the upper bound is proved or used.  (That the
marked tables coincide with the unmarked one is an outcome of the computation, not an assumption.)
-/

namespace Superperm7

def capTab0 : Array Nat := #[5, 5, 9, 9, 13, 13, 16, 16, 20, 20, 24, 24, 27, 27, 31, 31, 34, 34, 36, 38, 40, 41, 43, 44, 46, 47, 50, 51, 52, 54, 56, 57, 59, 60, 63, 64, 66, 66, 68, 69, 71, 72, 74, 75, 77, 79, 80, 82, 83, 85, 85, 86, 88, 89, 91, 92, 93]
def capTab1 : Array Nat := #[5, 5, 9, 9, 13, 13, 16, 16, 20, 20, 24, 24, 27, 27, 31, 31, 34, 34, 36, 38, 40, 41, 43, 44, 46, 47, 50, 51, 52, 54, 56, 57, 59, 60, 63, 64, 66, 66, 68, 69, 71, 72, 74, 75, 77, 79, 80, 82, 83, 85, 85, 86, 88, 89, 91]
def capTab2 : Array Nat := #[5, 5, 9, 9, 13, 13, 16, 16, 20, 20, 24, 24, 27, 27, 31, 31, 34, 34, 36, 38, 40, 41, 43, 44, 46, 47, 50, 51, 52, 54, 56, 57, 59, 60, 63, 64, 66, 66, 68, 69, 71, 72, 74, 75, 77, 79, 80]

theorem capTab0_size : capTab0.size = 57 := rfl
theorem capTab1_size : capTab1.size = 55 := rfl
theorem capTab2_size : capTab2.size = 47 := rfl

end Superperm7
