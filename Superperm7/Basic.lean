/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE); this file is
additionally subject to the upstream MIT notice below.

Adapted from https://github.com/BGray-wrl/superperm6
  file:   formal-verification/Superperm6/Basic.lean
  commit: d8a932d8f61d80b0bcfc737bd0e235a8300449c4
  upstream copyright: Copyright (c) 2026 Benjamin Grayzel — MIT License (reproduced in NOTICE).
Local modifications (port from six to seven symbols; see docs/PORT_LOG.md): six symbols replaced by seven throughout (Fin 7, 5040 permutations, overlap facts for words of length 7); additional single-quantifier lemmas appended.
-/
import Mathlib

/-!
# Basic definitions and the exact overlap metric

This file formalizes the non-computational definitions in Sections 1--2 of
the manuscript.  The overlap cost is defined as the least shift at which a
suffix of the first word agrees with a prefix of the second word.  The proof
that it is a directed metric is generic for equal-length lists.
-/

namespace Superperm7

abbrev Symbol := Fin 7
abbrev Perm7 := Equiv.Perm Symbol
abbrev Word := List Symbol

/-- The seven-letter word associated with a permutation. -/
def permWord (p : Perm7) : Word := List.ofFn p

@[simp] theorem permWord_length (p : Perm7) : (permWord p).length = 7 := by
  simp [permWord]

theorem permWord_nodup (p : Perm7) : (permWord p).Nodup := by
  change (List.ofFn p).Nodup
  exact List.nodup_ofFn.mpr p.injective

theorem permWord_injective : Function.Injective permWord := by
  intro p q h
  apply Equiv.ext
  intro i
  exact congrFun (List.ofFn_injective h) i

theorem card_perm7 : Fintype.card Perm7 = 5040 := by
  norm_num [Fintype.card_perm]

/-- A permutation occurs as a contiguous seven-symbol factor of `w`. -/
def Occurs (w : Word) (p : Perm7) : Prop := permWord p <:+: w

instance (w : Word) (p : Perm7) : Decidable (Occurs w p) :=
  List.decidableInfix (permWord p) w

/-- A word containing all `7!` permutations. -/
def IsSuperpermutation (w : Word) : Prop := ∀ p : Perm7, Occurs w p

instance (w : Word) : Decidable (IsSuperpermutation w) :=
  Fintype.decidableForallFintype

/-- A formulation of `s(7) = n` that does not hide existence in `Nat.find`. -/
def IsMinimumLength (n : ℕ) : Prop :=
  (∃ w : Word, IsSuperpermutation w ∧ w.length = n) ∧
  (∀ w : Word, IsSuperpermutation w → n ≤ w.length)

section Overlap

variable {α : Type*} [DecidableEq α]

/-- A shift `k` is compatible when the suffix remaining after dropping `k`
symbols from `x` is the corresponding prefix of `y`. -/
def OverlapCompatible (x y : List α) (k : ℕ) : Prop :=
  x.drop k = y.take (x.length - k)

instance (x y : List α) (k : ℕ) : Decidable (OverlapCompatible x y k) :=
  inferInstanceAs (Decidable (x.drop k = y.take (x.length - k)))

omit [DecidableEq α] in
private theorem overlap_exists (x y : List α) :
    ∃ k, OverlapCompatible x y k := by
  refine ⟨x.length, ?_⟩
  simp [OverlapCompatible]

/-- Least number of symbols which must be appended to an equal-length word
`x` in order for the result to end in `y`. -/
def overlapCost (x y : List α) : ℕ := Nat.find (overlap_exists x y)

theorem overlapCost_spec (x y : List α) :
    OverlapCompatible x y (overlapCost x y) :=
  Nat.find_spec (overlap_exists x y)

theorem overlapCost_le_length (x y : List α) : overlapCost x y ≤ x.length :=
  Nat.find_min' (overlap_exists x y)
    (show OverlapCompatible x y x.length by simp [OverlapCompatible])

theorem overlapCost_le_of_compatible {x y : List α} {k : ℕ}
    (h : OverlapCompatible x y k) : overlapCost x y ≤ k :=
  Nat.find_min' (overlap_exists x y) h

omit [DecidableEq α] in
theorem suffix_of_compatible {x y : List α} {k : ℕ}
    (h : OverlapCompatible x y k) :
    y <:+ x ++ y.drop (x.length - k) := by
  refine ⟨x.take k, ?_⟩
  calc
    x.take k ++ y =
        x.take k ++ (y.take (x.length - k) ++ y.drop (x.length - k)) := by
          rw [List.take_append_drop]
    _ = (x.take k ++ x.drop k) ++ y.drop (x.length - k) := by
          rw [h]
          simp only [List.append_assoc]
    _ = x ++ y.drop (x.length - k) := by rw [List.take_append_drop]

omit [DecidableEq α] in
theorem compatible_of_suffix {x y t : List α} {k : ℕ}
    (hlen : y.length = x.length) (ht : t.length = k) (hk : k ≤ x.length)
    (h : y <:+ x ++ t) : OverlapCompatible x y k := by
  rcases h with ⟨pre, hpre⟩
  have hprelen : pre.length = k := by
    have hlen := congrArg List.length hpre
    simp only [List.length_append] at hlen
    omega
  have hy : y = x.drop k ++ t := by
    calc
      y = (pre ++ y).drop k := by simp [hprelen]
      _ = (x ++ t).drop k := by rw [hpre]
      _ = x.drop k ++ t := List.drop_append_of_le_length hk
  have hdrop : (x.drop k).length = x.length - k := by simp
  calc
    x.drop k = (x.drop k ++ t).take (x.length - k) := by simp [hdrop]
    _ = y.take (x.length - k) := by rw [hy]

/-- `overlapCost` is minimal among *all* appended words, not merely among
the canonical suffixes of `y`. -/
theorem overlapCost_min {x y t : List α} {k : ℕ}
    (hlen : y.length = x.length) (ht : t.length = k)
    (h : y <:+ x ++ t) : overlapCost x y ≤ k := by
  by_cases hk : x.length ≤ k
  · exact (overlapCost_le_length x y).trans hk
  · exact Nat.find_min' (overlap_exists x y)
      (compatible_of_suffix hlen ht (Nat.le_of_lt (Nat.lt_of_not_ge hk)) h)

/-- The canonical symbols appended by an optimal overlap. -/
def optimalAppend (x y : List α) : List α :=
  y.drop (x.length - overlapCost x y)

theorem optimalAppend_length {x y : List α} (hlen : y.length = x.length) :
    (optimalAppend x y).length = overlapCost x y := by
  simp only [optimalAppend, List.length_drop, hlen]
  have hle := overlapCost_le_length x y
  omega

theorem optimalAppend_suffix {x y : List α} :
    y <:+ x ++ optimalAppend x y := by
  exact suffix_of_compatible (overlapCost_spec x y)

theorem overlapCost_self (x : List α) : overlapCost x x = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact Nat.find_min' (overlap_exists x x)
    (show OverlapCompatible x x 0 by simp [OverlapCompatible])

theorem overlapCost_triangle {x y z : List α}
    (hxy : y.length = x.length) (hyz : z.length = y.length) :
    overlapCost x z ≤ overlapCost x y + overlapCost y z := by
  let u := optimalAppend x y
  let v := optimalAppend y z
  have hyS : y <:+ x ++ u := optimalAppend_suffix
  have hzS : z <:+ y ++ v := optimalAppend_suffix
  rcases hyS with ⟨a, ha⟩
  rcases hzS with ⟨b, hb⟩
  have hzFinal : z <:+ x ++ (u ++ v) := by
    refine ⟨a ++ b, ?_⟩
    calc
      (a ++ b) ++ z = a ++ (b ++ z) := by simp [List.append_assoc]
      _ = a ++ (y ++ v) := by rw [hb]
      _ = (a ++ y) ++ v := by simp [List.append_assoc]
      _ = (x ++ u) ++ v := by rw [ha]
      _ = x ++ (u ++ v) := by simp [List.append_assoc]
  apply overlapCost_min (hyz.trans hxy)
    (show (u ++ v).length = overlapCost x y + overlapCost y z by
      simp [u, v, optimalAppend_length hxy, optimalAppend_length hyz])
    hzFinal

theorem overlapCost_pos_of_ne {x y : List α} (hlen : y.length = x.length)
    (hne : x ≠ y) : 0 < overlapCost x y := by
  apply Nat.pos_of_ne_zero
  intro hzero
  have h := overlapCost_spec x y
  rw [hzero] at h
  have hxy : x = y := by simpa [OverlapCompatible, ← hlen] using h
  exact hne hxy

end Overlap

/-- Directed append cost on seven-symbol permutations. -/
def d (p q : Perm7) : ℕ := overlapCost (permWord p) (permWord q)

@[simp] theorem d_self (p : Perm7) : d p p = 0 := overlapCost_self _

theorem d_le_seven (p q : Perm7) : d p q ≤ 7 := by
  simpa [d] using overlapCost_le_length (permWord p) (permWord q)

theorem d_pos_of_ne {p q : Perm7} (h : p ≠ q) : 0 < d p q := by
  apply overlapCost_pos_of_ne (by simp)
  exact fun hpq => h (permWord_injective hpq)

theorem d_triangle (p q r : Perm7) : d p r ≤ d p q + d q r := by
  exact overlapCost_triangle (by simp) (by simp)


/-! ## The rotation and insertion maps (n = 7) -/

private def rotIndexFn : Symbol → Symbol
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 3
  | ⟨3, _⟩ => 4
  | ⟨4, _⟩ => 5
  | ⟨5, _⟩ => 6
  | ⟨_, _⟩ => 0

private def rotIndexInvFn : Symbol → Symbol
  | ⟨0, _⟩ => 6
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 2
  | ⟨4, _⟩ => 3
  | ⟨5, _⟩ => 4
  | ⟨_, _⟩ => 5

private def insertIndexFn : Symbol → Symbol
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 3
  | ⟨3, _⟩ => 4
  | ⟨4, _⟩ => 5
  | ⟨5, _⟩ => 0
  | ⟨_, _⟩ => 6

private def insertIndexInvFn : Symbol → Symbol
  | ⟨0, _⟩ => 5
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 2
  | ⟨4, _⟩ => 3
  | ⟨5, _⟩ => 4
  | ⟨_, _⟩ => 6

private def nondecompTwoIndexFn : Symbol → Symbol
  | ⟨0, _⟩ => 2
  | ⟨1, _⟩ => 3
  | ⟨2, _⟩ => 4
  | ⟨3, _⟩ => 5
  | ⟨4, _⟩ => 6
  | ⟨5, _⟩ => 1
  | ⟨_, _⟩ => 0

private def nondecompTwoIndexInvFn : Symbol → Symbol
  | ⟨0, _⟩ => 6
  | ⟨1, _⟩ => 5
  | ⟨2, _⟩ => 0
  | ⟨3, _⟩ => 1
  | ⟨4, _⟩ => 2
  | ⟨5, _⟩ => 3
  | ⟨_, _⟩ => 4

def rotIndex : Equiv.Perm Symbol where
  toFun := rotIndexFn
  invFun := rotIndexInvFn
  left_inv := by decide
  right_inv := by decide

def insertIndex : Equiv.Perm Symbol where
  toFun := insertIndexFn
  invFun := insertIndexInvFn
  left_inv := by decide
  right_inv := by decide

def nondecompTwoIndex : Equiv.Perm Symbol where
  toFun := nondecompTwoIndexFn
  invFun := nondecompTwoIndexInvFn
  left_inv := by decide
  right_inv := by decide

/-- `R(abcdefg) = bcdefga`. -/
def R (p : Perm7) : Perm7 := rotIndex.trans p

/-- `F(abcdefg) = bcdefag`: rotate the first six symbols, fix the last. -/
def F (p : Perm7) : Perm7 := insertIndex.trans p

/-- The nondecomposable (proper) cost-two successor `abcdefg ↦ cdefgba`. -/
def N₂ (p : Perm7) : Perm7 := nondecompTwoIndex.trans p

def finiteOrbit [Fintype α] [DecidableEq α] (f : α → α) (n : ℕ) (x : α) : Finset α :=
  (Finset.range n).image fun i => (f^[i]) x

def rClass (p : Perm7) : Finset Perm7 := finiteOrbit R 7 p
def fBlock (p : Perm7) : Finset Perm7 := finiteOrbit F 6 p

def allRClasses : Finset (Finset Perm7) := Finset.univ.image rClass
def allFBlocks : Finset (Finset Perm7) := Finset.univ.image fBlock

theorem R_order_seven : ∀ p : Perm7, (R^[7]) p = p := by native_decide
theorem F_order_six : ∀ p : Perm7, (F^[6]) p = p := by native_decide

theorem rClass_card (p : Perm7) : (rClass p).card = 7 := by native_decide +revert
theorem fBlock_card (p : Perm7) : (fBlock p).card = 6 := by native_decide +revert
theorem number_of_rClasses : allRClasses.card = 720 := by native_decide
theorem number_of_fBlocks : allFBlocks.card = 840 := by native_decide

/-! ## Overlap costs between permutations are determined by a single shift

For permutations (all symbols distinct) at most one shift `k < 7` is
compatible, because compatibility at shift `k` forces `q 0 = p k`.  Hence
`d p q = k ↔ OverlapCompatible (permWord p) (permWord q) k`, and the cost-one,
cost-two and cost-three successor lemmas become statements with a single
quantifier. -/

theorem permWord_getElem? (p : Perm7) (i : ℕ) (hi : i < 7) :
    (permWord p)[i]? = some (p ⟨i, hi⟩) := by
  rw [permWord, List.getElem?_ofFn]
  simp [hi]

/-- Compatibility at shift `k` pins the first `7-k` values of `q`. -/
theorem agree_of_compatible {p q : Perm7} {k : ℕ} (hk : k < 7)
    (h : OverlapCompatible (permWord p) (permWord q) k)
    (i : Fin 7) (hi : i.val + k < 7) : q i = p ⟨i.val + k, hi⟩ := by
  unfold OverlapCompatible at h
  have := congrArg (fun l => l[i.val]?) h
  simp only [List.getElem?_drop, List.getElem?_take, permWord_length] at this
  rw [if_pos (by omega), permWord_getElem? p (k + i.val) (by omega),
    permWord_getElem? q i.val i.isLt] at this
  simp only [Option.some.injEq] at this
  rw [← this]
  congr 1; ext; simp; omega

theorem overlapCompatible_perm_unique {p q : Perm7} {j k : ℕ} (hj : j < 7) (hk : k < 7)
    (h1 : OverlapCompatible (permWord p) (permWord q) j)
    (h2 : OverlapCompatible (permWord p) (permWord q) k) : j = k := by
  have a := agree_of_compatible hj h1 ⟨0, by omega⟩ (by simp; omega)
  have b := agree_of_compatible hk h2 ⟨0, by omega⟩ (by simp; omega)
  rw [a] at b
  have := congrArg Fin.val (p.injective b)
  simpa using this

theorem d_eq_iff_compatible {p q : Perm7} {k : ℕ} (hk : k < 7) :
    d p q = k ↔ OverlapCompatible (permWord p) (permWord q) k := by
  constructor
  · intro h
    have := overlapCost_spec (permWord p) (permWord q)
    unfold d at h
    rwa [h] at this
  · intro h
    have hle : d p q ≤ k := overlapCost_le_of_compatible h
    have hspec := overlapCost_spec (permWord p) (permWord q)
    exact overlapCompatible_perm_unique (lt_of_le_of_lt hle hk) hk hspec h

/-- Two permutations of `Fin 7` that agree on the first six positions are equal. -/
theorem perm_eq_of_agree_six {q q' : Perm7} (h : ∀ i : Fin 7, i.val < 6 → q i = q' i) :
    q = q' := by
  apply Equiv.ext
  intro i
  by_cases hi : i.val < 6
  · exact h i hi
  · obtain ⟨j, hj⟩ := q'.surjective (q i)
    by_cases hj6 : j.val < 6
    · have e := h j hj6
      rw [hj] at e
      have := congrArg Fin.val (q.injective e.symm)
      simp at this; omega
    · have : j = i := Fin.ext (by omega)
      rw [this] at hj; exact hj.symm

/-- Positions swap `5 ↔ 6`. -/
def swapLastTwo : Equiv.Perm Symbol := Equiv.swap ⟨5, by omega⟩ ⟨6, by omega⟩

/-- Two permutations agreeing on the first five positions are equal or differ
by the transposition of the last two positions. -/
theorem perm_eq_or_swap_of_agree_five {q q' : Perm7}
    (h : ∀ i : Fin 7, i.val < 5 → q i = q' i) :
    q = q' ∨ q = swapLastTwo.trans q' := by
  by_cases h5 : q ⟨5, by omega⟩ = q' ⟨5, by omega⟩
  · left
    apply perm_eq_of_agree_six
    intro i hi
    by_cases hi5 : i.val < 5
    · exact h i hi5
    · have : i = ⟨5, by omega⟩ := Fin.ext (by simp; omega)
      rw [this]; exact h5
  · right
    obtain ⟨j, hj⟩ := q'.surjective (q ⟨5, by omega⟩)
    have hj6 : j.val = 6 := by
      by_contra hne
      by_cases hj5 : j.val < 5
      · have e := h j hj5
        rw [hj] at e
        have := congrArg Fin.val (q.injective e.symm); simp at this; omega
      · have : j = ⟨5, by omega⟩ := Fin.ext (by simp; omega)
        rw [this] at hj; exact h5 hj.symm
    apply perm_eq_of_agree_six
    intro i hi
    simp only [Equiv.trans_apply, swapLastTwo]
    by_cases hi5 : i.val < 5
    · rw [Equiv.swap_apply_of_ne_of_ne]
      · exact h i hi5
      · intro he; have := congrArg Fin.val he; simp at this; omega
      · intro he; have := congrArg Fin.val he; simp at this; omega
    · have hi' : i = ⟨5, by omega⟩ := Fin.ext (by simp; omega)
      have hj' : j = ⟨6, by omega⟩ := Fin.ext hj6
      rw [hi', Equiv.swap_apply_left, ← hj', hj]

theorem permWord_R_compat : ∀ p : Perm7, OverlapCompatible (permWord p) (permWord (R p)) 1 := by
  unfold OverlapCompatible
  native_decide

theorem permWord_RR_compat : ∀ p : Perm7,
    OverlapCompatible (permWord p) (permWord (R (R p))) 2 := by
  unfold OverlapCompatible
  native_decide

theorem permWord_N₂_compat : ∀ p : Perm7,
    OverlapCompatible (permWord p) (permWord (N₂ p)) 2 := by
  unfold OverlapCompatible
  native_decide

theorem N₂_eq_swap_RR (p : Perm7) : N₂ p = swapLastTwo.trans (R (R p)) := by
  apply Equiv.ext; intro i; fin_cases i <;> rfl

theorem cost_one_successor (p q : Perm7) : d p q = 1 ↔ q = R p := by
  rw [d_eq_iff_compatible (by omega)]
  constructor
  · intro h
    apply perm_eq_of_agree_six
    intro i hi
    rw [agree_of_compatible (by omega) h i (by omega),
      agree_of_compatible (by omega) (permWord_R_compat p) i (by omega)]
  · rintro rfl; exact permWord_R_compat p

theorem cost_two_successors (p q : Perm7) :
    d p q = 2 ↔ q = R (R p) ∨ q = N₂ p := by
  rw [d_eq_iff_compatible (by omega)]
  constructor
  · intro h
    have : ∀ i : Fin 7, i.val < 5 → q i = (R (R p)) i := by
      intro i hi
      rw [agree_of_compatible (by omega) h i (by omega),
        agree_of_compatible (by omega) (permWord_RR_compat p) i (by omega)]
    rcases perm_eq_or_swap_of_agree_five this with h | h
    · exact Or.inl h
    · right; rw [N₂_eq_swap_RR]; exact h
  · rintro (rfl | rfl)
    · exact permWord_RR_compat p
    · exact permWord_N₂_compat p

theorem cost_two_R_R (p : Perm7) : d p (R (R p)) = 2 := (cost_two_successors p _).mpr (Or.inl rfl)
theorem cost_two_N₂ (p : Perm7) : d p (N₂ p) = 2 := (cost_two_successors p _).mpr (Or.inr rfl)
theorem cost_one_R (p : Perm7) : d p (R p) = 1 := (cost_one_successor p _).mpr rfl

end Superperm7
