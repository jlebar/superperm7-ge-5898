/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE); this file is
additionally subject to the upstream MIT notice below.

Adapted from https://github.com/BGray-wrl/superperm6
  file:   formal-verification/Superperm6/Section5Core.lean
  commit: d8a932d8f61d80b0bcfc737bd0e235a8300449c4
  upstream copyright: Copyright (c) 2026 Benjamin Grayzel — MIT License (reproduced in NOTICE).
Local modifications (port from six to seven symbols; see docs/PORT_LOG.md): constants for seven symbols.
-/
import Superperm7.Section4
import Superperm7.Rows

/-!
# Verified core facts for the Section 5 bridge

This file proves the definition-level parts of the distinguished-row and
safe-surgery arguments.  It does not itself carry the full cover-to-certificate
bridge: the global choice and accounting of retained rows, represented gaps,
and concealed payload are proved separately, in `CoarsenBridge` and
`CoarsenAccounting`.
-/

namespace Superperm7

/-! ## Hole runs stay in one insertion block -/

theorem touchedTPerm_pow_eq_touchedFPerm_pow_of_holes
    (route : List Perm7) (p : TouchedState route) (n : ℕ)
    (hholes : ∀ j < n,
      ¬ IsSelectedTouched route ((touchedTPerm route ^ j) p)) :
    (touchedTPerm route ^ n) p = (touchedFPerm route ^ n) p := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', Equiv.Perm.mul_apply,
        touchedTPerm_eq_touchedF_of_not_selected route
          ((touchedTPerm route ^ n) p) (hholes n (by omega)),
        ih (fun j hj => hholes j (by omega))]

theorem touchedStateBlock_apply_touchedF_pow (route : List Perm7)
    (p : TouchedState route) (n : ℕ) :
    touchedStateBlock route ((touchedFPerm route ^ n) p) =
      touchedStateBlock route p := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      calc
        touchedStateBlock route
            (touchedFPerm route ((touchedFPerm route ^ n) p)) =
            touchedStateBlock route ((touchedFPerm route ^ n) p) := by
          apply Subtype.ext
          exact fBlock_F _
        _ = touchedStateBlock route p := ih

/-- Formal version of distinguished-row Lemma (i): every finite consecutive
run of holes on a `T`-orbit is contained in one `F`-block. -/
theorem hole_run_stays_in_one_block (route : List Perm7)
    (p : TouchedState route) (n : ℕ)
    (hholes : ∀ j < n,
      ¬ IsSelectedTouched route ((touchedTPerm route ^ j) p))
    {j : ℕ} (hj : j ≤ n) :
    touchedStateBlock route ((touchedTPerm route ^ j) p) =
      touchedStateBlock route p := by
  rw [touchedTPerm_pow_eq_touchedFPerm_pow_of_holes route p j
    (fun i hi => hholes i (hi.trans_le hj))]
  exact touchedStateBlock_apply_touchedF_pow route p j

/-! ## The visible row complementary to a boundary gap -/

/-- A gap of `d ≤ 5` holes beginning at `x` leaves the cyclic interval
`F^d x,...,F^5 x` visible. -/
def gapComplementRow (x : Perm7) (holes : Fin 6) : Row where
  start := (F^[holes.val]) x
  lengthCode := ⟨5 - holes.val, by omega⟩

theorem gapComplementRow_length (x : Perm7) (holes : Fin 6) :
    (gapComplementRow x holes).length = 6 - holes.val := by
  simp [gapComplementRow, Row.length]
  omega

theorem gapComplementRow_lastState : ∀ (x : Perm7) (holes : Fin 6),
    (gapComplementRow x holes).lastState = (F^[5]) x := by
  native_decide

theorem gapComplementRow_block : ∀ (x : Perm7) (holes : Fin 6),
    (gapComplementRow x holes).block = fBlock x := by
  native_decide

/-- Single-quantifier form of the exit-tuple identity: the complementary
row after `F a` exits through the tail of `R⁻¹ a`. -/
theorem gapComplementRow_beta_F : ∀ (a : Perm7) (holes : Fin 6),
    (gapComplementRow (F a) holes).beta = (permWord (Rinv a)).drop 3 := by
  native_decide

/-- The exit triple of the complementary row depends only on the state just
before the gap under `T`, not on the gap length. -/
theorem gapComplementRow_beta_of_F_eq : ∀ (a x : Perm7) (holes : Fin 6),
    F a = x →
      (gapComplementRow x holes).beta =
        (permWord (Rinv a)).drop 3 := by
  intro a x holes hx
  subst hx
  exact gapComplementRow_beta_F a holes

noncomputable def runMacroBeta (route : List Perm7) (s : RunStart route) : Triple :=
  (permWord (Rinv (runStartPerm route s).1)).drop 3

/-- Formal endpoint calculation in distinguished-row Lemma (ii).  If the
`T`-edge out of selected start `s` enters the first hole `x`, every possible
visible complementary row has exactly the exit triple of the run from `s`. -/
theorem gapComplementRow_beta_of_touchedT_predecessor
    (route : List Perm7) (s : RunStart route) (x : Perm7)
    (holes : Fin 6)
    (hT : (touchedTPerm route (runStartTouchedState route s)).1 = x) :
    (gapComplementRow x holes).beta = runMacroBeta route s := by
  apply gapComplementRow_beta_of_F_eq
  exact (touchedTPerm_runStartTouchedState_val route s).symm.trans hT

theorem gapComplementRow_alpha (x : Perm7) (holes : Fin 6) :
    alpha (gapComplementRow x holes).start =
      alpha ((F^[holes.val]) x) := rfl

/-! ## Safe cyclic surgery -/

/-- An abstract placement of distinct cyclic intervals into linear trails.
`position` is required to be injective within each trail. -/
def TrailPlacementIsFaithful {I T : Type*}
    (trail : I → T) (position : I → ℕ) : Prop :=
  ∀ i j, trail i = trail j → position i = position j → i = j

/-- Among cyclic successor pairs, one pair is either on different trails or
occurs in forward order on a common trail.  This is the load-bearing
existence assertion in the safe cyclic surgery lemma. -/
theorem exists_safe_cyclic_pair
    {I T : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (next : Equiv.Perm I) (hnext : ∀ i, next i ≠ i)
    (trail : I → T) (position : I → ℕ)
    (hfaithful : TrailPlacementIsFaithful trail position) :
    ∃ i : I, trail i ≠ trail (next i) ∨
      position i < position (next i) := by
  obtain ⟨i, _hi, hmin⟩ := Finset.exists_min_image
    (Finset.univ : Finset I) position Finset.univ_nonempty
  refine ⟨i, ?_⟩
  by_cases htrail : trail i = trail (next i)
  · right
    have hle := hmin (next i) (Finset.mem_univ _)
    have hne : position i ≠ position (next i) := by
      intro heq
      exact hnext i (hfaithful i (next i) htrail heq).symm
    omega
  · exact Or.inl htrail

/-! ## Distinct quotient components have disjoint visible classes -/

theorem selected_rotation_classes_disjoint_of_component_ne
    {route : List Perm7} (hroute : IsHamiltonianRoute route)
    (s t : RunStart route)
    (hne : (rotationGraph route hroute).connectedComponentMk (startBlock s) ≠
      (rotationGraph route hroute).connectedComponentMk (startBlock t)) :
    Disjoint (rClass s.1) (rClass t.1) := by
  rw [Finset.disjoint_left]
  intro x hxs hxt
  apply hne
  apply SimpleGraph.ConnectedComponent.sound
  apply startBlocks_reachable_of_same_rClass hroute
  exact (rClass_eq_of_mem s.1 x hxs).symm.trans
    (rClass_eq_of_mem t.1 x hxt)

theorem selected_blocks_ne_of_component_ne
    {route : List Perm7} (hroute : IsHamiltonianRoute route)
    (s t : RunStart route)
    (hne : (rotationGraph route hroute).connectedComponentMk (startBlock s) ≠
      (rotationGraph route hroute).connectedComponentMk (startBlock t)) :
    startBlock s ≠ startBlock t := by
  intro hst
  exact hne (congrArg
    ((rotationGraph route hroute).connectedComponentMk) hst)

end Superperm7
