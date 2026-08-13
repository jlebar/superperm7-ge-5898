/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).

TRUSTED FILE (read it).  The definitions the headline statements depend on, from Mathlib alone.
They are verbatim copies of the ones in `Superperm7/Basic.lean`; `Solution.lean` bridges the two by
definitional unfolding, and comparator checks that the proved statements are exactly the ones in
`Challenge.lean`, which mention only the constants defined here.
-/
import Mathlib

namespace ChallengeDeps

/-- The seven symbols. -/
abbrev Symbol := Fin 7
/-- Permutations of the seven symbols. -/
abbrev Perm7 := Equiv.Perm Symbol
/-- Words over the seven symbols. -/
abbrev Word := List Symbol

/-- The seven-letter word listing the values of a permutation. -/
def permWord (p : Perm7) : Word := List.ofFn p

/-- `p` occurs in `w` as a contiguous factor. -/
def Occurs (w : Word) (p : Perm7) : Prop := permWord p <:+: w

/-- `w` contains every one of the 5040 permutations as a contiguous factor. -/
def IsSuperpermutation (w : Word) : Prop := ∀ p : Perm7, Occurs w p

end ChallengeDeps
