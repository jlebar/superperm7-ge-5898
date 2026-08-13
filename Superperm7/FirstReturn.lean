/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE); this file is
additionally subject to the upstream MIT notice below.

Adapted from https://github.com/BGray-wrl/superperm6
  file:   formal-verification/Superperm6/FirstReturn.lean
  commit: d8a932d8f61d80b0bcfc737bd0e235a8300449c4
  upstream copyright: Copyright (c) 2026 Benjamin Grayzel — MIT License (reproduced in NOTICE).
Local modifications (port from six to seven symbols; see docs/PORT_LOG.md): return time <= 7; single-quantifier restatements.
-/
import Superperm7.Orbit
import Superperm7.Euler

/-!
# First return around a rotation class

The permutation `A` in Sections 3--4 is the first-return map of `R` on the
run starts.  This file constructs that permutation abstractly from an actual
Hamilton route.
-/

namespace Superperm7

/-- `R`, packaged as a permutation of the 5040 states. -/
def rotationPerm7 : Equiv.Perm Perm7 where
  toFun := R
  invFun := fun p => rotIndex.symm.trans p
  left_inv := by native_decide
  right_inv := by native_decide

theorem rotationPerm7_pow_seven (p : Perm7) :
    (rotationPerm7 ^ 7) p = p := by
  native_decide +revert

theorem rotationPerm7_pow_apply (n : ℕ) (p : Perm7) :
    (rotationPerm7 ^ n) p = (R^[n]) p := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, Function.iterate_succ_apply', ih]
      rfl

def IsRunReturn (route : List Perm7) (s : RunStart route) (n : ℕ) : Prop :=
  0 < n ∧ (rotationPerm7 ^ n) s.1 ∈ runStartSet route

instance (route : List Perm7) (s : RunStart route) (n : ℕ) :
    Decidable (IsRunReturn route s n) := by
  unfold IsRunReturn
  infer_instance

theorem runReturn_exists (route : List Perm7) (s : RunStart route) :
    ∃ n, IsRunReturn route s n := by
  refine ⟨7, by norm_num, ?_⟩
  rw [rotationPerm7_pow_seven]
  exact s.2

noncomputable def runReturnTime (route : List Perm7) (s : RunStart route) : ℕ :=
  Nat.find (runReturn_exists route s)

theorem runReturnTime_spec (route : List Perm7) (s : RunStart route) :
    IsRunReturn route s (runReturnTime route s) :=
  Nat.find_spec (runReturn_exists route s)

theorem runReturnTime_min (route : List Perm7) (s : RunStart route) {n : ℕ}
    (hn : n < runReturnTime route s) : ¬ IsRunReturn route s n :=
  Nat.find_min (runReturn_exists route s) hn

theorem runReturnTime_le_seven (route : List Perm7) (s : RunStart route) :
    runReturnTime route s ≤ 7 :=
  Nat.find_min' (runReturn_exists route s)
    ⟨by norm_num, by rw [rotationPerm7_pow_seven]; exact s.2⟩

/-- Before the first return to the selected run starts, rotation advances
one position at a time along an actual cost-one run in the linear route. -/
theorem idxOf_rotationPerm7_pow_before_return {route : List Perm7}
    (hroute : IsHamiltonianRoute route) (s : RunStart route) :
    ∀ n : ℕ, n < runReturnTime route s →
      route.idxOf ((rotationPerm7 ^ n) s.1) = route.idxOf s.1 + n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      intro hn
      have hn' : n < runReturnTime route s := by omega
      let y := (rotationPerm7 ^ (n + 1)) s.1
      have hyNotStart : y ∉ runStartSet route := by
        intro hyStart
        exact runReturnTime_min route s hn
          ⟨by omega, by simpa [y, Nat.succ_eq_add_one] using hyStart⟩
      have hyDest : y ∈ costOneDestinations route := by
        simpa [runStartSet] using hyNotStart
      obtain ⟨a, haEdge, haCost⟩ :=
        mem_costOneDestinations_gives_edge hyDest
      have hyR : y = R a := (cost_one_successor a y).mp haCost
      have hpowR : y = R ((rotationPerm7 ^ n) s.1) := by
        dsimp [y]
        rw [pow_succ', Equiv.Perm.mul_apply]
        rfl
      have ha : a = (rotationPerm7 ^ n) s.1 := by
        exact R_injective (hyR.symm.trans hpowR)
      have hidx := idxOf_succ_of_pair_infix hroute.1 (hroute.2 a)
        (hroute.2 y) haEdge
      rw [ha, ih hn'] at hidx
      exact hidx

/-- The next selected start encountered while moving cyclically by `R`. -/
noncomputable def nextRunStart (route : List Perm7) (s : RunStart route) :
    RunStart route :=
  ⟨(rotationPerm7 ^ runReturnTime route s) s.1,
    (runReturnTime_spec route s).2⟩

private theorem return_power_cancel_right {route : List Perm7}
    (s t : RunStart route)
    (hnext : (nextRunStart route s).1 = (nextRunStart route t).1)
    (hmn : runReturnTime route s ≤ runReturnTime route t) :
    s = t := by
  let m := runReturnTime route s
  let n := runReturnTime route t
  let d := n - m
  have hnmd : n = m + d := by
    dsimp [d]
    omega
  have hpow : s.1 = (rotationPerm7 ^ d) t.1 := by
    apply (rotationPerm7 ^ m).injective
    calc
      (rotationPerm7 ^ m) s.1 = (rotationPerm7 ^ n) t.1 := by
        simpa [nextRunStart, m, n] using hnext
      _ = (rotationPerm7 ^ (m + d)) t.1 := by rw [hnmd]
      _ = (rotationPerm7 ^ m) ((rotationPerm7 ^ d) t.1) := by
        rw [pow_add, Equiv.Perm.mul_apply]
  have hnm : n ≤ m := by
    by_contra hnot
    have hmdpos : 0 < d := by
      dsimp [d]
      omega
    have hdn : d < n := by
      have hmpos := (runReturnTime_spec route s).1
      dsimp [m, n] at *
      omega
    have hdReturn : IsRunReturn route t d := by
      refine ⟨hmdpos, ?_⟩
      rw [← hpow]
      exact s.2
    exact runReturnTime_min route t hdn hdReturn
  have hmnEq : m = n := by omega
  apply Subtype.ext
  dsimp [d] at hpow
  rw [hmnEq] at hpow
  simpa using hpow

theorem nextRunStart_injective (route : List Perm7) :
    Function.Injective (nextRunStart route) := by
  intro s t hnext
  by_cases hmn : runReturnTime route s ≤ runReturnTime route t
  · exact return_power_cancel_right s t (congrArg Subtype.val hnext) hmn
  · exact (return_power_cancel_right t s
      (congrArg Subtype.val hnext.symm) (Nat.le_of_not_ge hmn)).symm

/-- The first-return map is a permutation because the set of run starts is
finite. -/
noncomputable def runStartPerm (route : List Perm7) :
    Equiv.Perm (RunStart route) :=
  Equiv.ofBijective (nextRunStart route)
    ⟨nextRunStart_injective route,
      Finite.injective_iff_surjective.mp (nextRunStart_injective route)⟩

@[simp] theorem runStartPerm_apply (route : List Perm7) (s : RunStart route) :
    runStartPerm route s = nextRunStart route s := rfl

theorem rotationPerm7_pow_mem_rClass (n : ℕ) (p : Perm7) :
    (rotationPerm7 ^ n) p ∈ rClass p := by
  induction n with
  | zero =>
      simpa using self_mem_rClass p
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      change R ((rotationPerm7 ^ n) p) ∈ rClass p
      exact R_mem_rClass_of_mem p _ ih

theorem nextRunStart_same_rClass (route : List Perm7) (s : RunStart route) :
    rClass (nextRunStart route s).1 = rClass s.1 := by
  apply rClass_eq_of_mem
  exact rotationPerm7_pow_mem_rClass _ _

private theorem runStartPerm_sameCycle_of_rotation_power (route : List Perm7) :
    ∀ j : ℕ, ∀ s t : RunStart route,
      t.1 = (rotationPerm7 ^ j) s.1 →
      (runStartPerm route).SameCycle s t := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
      intro s t hj
      by_cases hj0 : j = 0
      · subst j
        simp only [pow_zero, Equiv.Perm.one_apply] at hj
        apply Eq.sameCycle
        exact Subtype.ext hj.symm
      · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
        let m := runReturnTime route s
        have hmj : m ≤ j := by
          apply Nat.find_min' (runReturn_exists route s)
          refine ⟨hjpos, ?_⟩
          rw [← hj]
          exact t.2
        by_cases hmEq : m = j
        · have hnext : nextRunStart route s = t := by
            apply Subtype.ext
            simpa [nextRunStart, m, hmEq] using hj.symm
          subst t
          refine ⟨1, ?_⟩
          simp
        · have hmLt : m < j := lt_of_le_of_ne hmj hmEq
          let u := nextRunStart route s
          let d := j - m
          have hdj : d < j := by
            have hmpos := (runReturnTime_spec route s).1
            dsimp [d, m] at *
            omega
          have htPower : t.1 = (rotationPerm7 ^ d) u.1 := by
            change t.1 = (rotationPerm7 ^ d) ((rotationPerm7 ^ m) s.1)
            calc
              t.1 = (rotationPerm7 ^ j) s.1 := hj
              _ = (rotationPerm7 ^ (d + m)) s.1 := by
                congr 2
                dsimp [d]
                omega
              _ = (rotationPerm7 ^ d) ((rotationPerm7 ^ m) s.1) := by
                rw [pow_add, Equiv.Perm.mul_apply]
          have hst : (runStartPerm route).SameCycle s u := by
            refine ⟨1, ?_⟩
            simp [u]
          exact hst.trans (ih d hdj u t htPower)

theorem runStartPerm_sameCycle_of_same_rClass (route : List Perm7)
    (s t : RunStart route) (hst : rClass s.1 = rClass t.1) :
    (runStartPerm route).SameCycle s t := by
  have htMem : t.1 ∈ rClass s.1 := by
    rw [hst]
    exact self_mem_rClass t.1
  rcases Finset.mem_image.mp htMem with ⟨j, hj, hjpow⟩
  exact runStartPerm_sameCycle_of_rotation_power route j s t
    (by simpa [rotationPerm7_pow_apply] using hjpow.symm)

theorem rotationClassOf_baseRunStart (route : List Perm7)
    (hroute : IsHamiltonianRoute route) (C : RotationClass) :
    rotationClassOf (baseRunStart route hroute C).1 = C := by
  apply Subtype.ext
  have hsC := baseRunStart_mem_class route hroute C
  rcases Finset.mem_image.mp C.2 with ⟨p, _hp, hpC⟩
  rw [← hpC] at hsC ⊢
  exact rClass_eq_of_mem p _ hsC

theorem card_rotationClass : Fintype.card RotationClass = 720 := by
  calc
    Fintype.card RotationClass = allRClasses.card := Fintype.card_coe _
    _ = 720 := number_of_rClasses

/-- Fixed vectors of the first-return permutation are exactly choices of
one scalar per rotation class. -/
noncomputable def rotationClassFunctionsEquivRunStartFixed
    (route : List Perm7) (hroute : IsHamiltonianRoute route) :
    (RotationClass → ℝ) ≃ₗ[ℝ] permFixedSubmodule (runStartPerm route) where
  toFun f := ⟨fun s => f (rotationClassOf s.1), by
    intro s
    change f (rotationClassOf (runStartPerm route s).1) =
      f (rotationClassOf s.1)
    rw [runStartPerm_apply]
    congr 1
    apply Subtype.ext
    exact nextRunStart_same_rClass route s⟩
  invFun v := fun C => v.1 (baseRunStart route hroute C)
  left_inv f := by
    funext C
    exact congrArg f (rotationClassOf_baseRunStart route hroute C)
  right_inv v := by
    apply Subtype.ext
    funext s
    apply permFixed_eq_of_sameCycle (runStartPerm route) v
    apply runStartPerm_sameCycle_of_same_rClass
    have hbase := rotationClassOf_baseRunStart route hroute
      (rotationClassOf s.1)
    exact congrArg Subtype.val hbase
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem runStartPerm_cycleCount (route : List Perm7)
    (hroute : IsHamiltonianRoute route) :
    permCycleCount (runStartPerm route) = 720 := by
  calc
    permCycleCount (runStartPerm route) =
        Module.finrank ℝ (permFixedSubmodule (runStartPerm route)) :=
      (finrank_permFixedSubmodule (runStartPerm route)).symm
    _ = Module.finrank ℝ (RotationClass → ℝ) :=
      (rotationClassFunctionsEquivRunStartFixed route hroute).finrank_eq.symm
    _ = Fintype.card RotationClass := Module.finrank_pi ℝ
    _ = 720 := card_rotationClass

end Superperm7
