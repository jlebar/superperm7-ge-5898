/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE); this file is
additionally subject to the upstream MIT notice below.

Adapted from https://github.com/BGray-wrl/superperm6
  file:   formal-verification/Superperm6/Euler.lean
  commit: d8a932d8f61d80b0bcfc737bd0e235a8300449c4
  upstream copyright: Copyright (c) 2026 Benjamin Grayzel — MIT License (reproduced in NOTICE).
Local modifications (port from six to seven symbols; see docs/PORT_LOG.md): namespace and permutation type only.
-/
import Superperm7.GraphRank
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The permutation-map Euler formula

This file proves the generic finite-permutation statement used in Section 4.
Cycles include fixed points.  The proof uses the bipartite incidence graph
of the cycles of the two permutations for the Euler inequality and the sign
homomorphism for parity.
-/

namespace Superperm7

open SimpleGraph

section PermCycles

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Nontrivial cycle factors together with fixed points: exactly the cycles
of a permutation, including one-cycles. -/
abbrev PermCycle (σ : Equiv.Perm α) :=
  σ.cycleFactorsFinset ⊕ Function.fixedPoints σ

def permCycleOf (σ : Equiv.Perm α) (x : α) : PermCycle σ :=
  if hx : σ x = x then
    Sum.inr ⟨x, Function.mem_fixedPoints_iff.mpr hx⟩
  else
    Sum.inl ⟨σ.cycleOf x,
      Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr
        (Equiv.Perm.mem_support.mpr hx)⟩

theorem permCycleOf_surjective (σ : Equiv.Perm α) :
    Function.Surjective (permCycleOf σ) := by
  intro C
  cases C with
  | inr x =>
      refine ⟨x.1, ?_⟩
      simp [permCycleOf, Function.mem_fixedPoints_iff.mp x.2]
  | inl c =>
      have hcCycle := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.2).1
      obtain ⟨x, hxSupport⟩ := hcCycle.nonempty_support
      have hxMove : σ x ≠ x := by
        apply Equiv.Perm.mem_support.mp
        have hcAgree := (Equiv.Perm.mem_cycleFactorsFinset_iff.mp c.2).2
        have hcx : c.1 x ≠ x := Equiv.Perm.mem_support.mp hxSupport
        simpa [hcAgree x hxSupport] using hcx
      refine ⟨x, ?_⟩
      simp only [permCycleOf, dif_neg hxMove, Sum.inl.injEq]
      apply Subtype.ext
      exact (Equiv.Perm.eq_cycleOf_of_mem_cycleFactorsFinset_iff
        σ c.1 c.2 x).mpr hxSupport |>.symm

theorem permCycleOf_apply (σ : Equiv.Perm α) (x : α) :
    permCycleOf σ (σ x) = permCycleOf σ x := by
  by_cases hx : σ x = x
  · simp [permCycleOf, hx]
  · have hfx : σ (σ x) ≠ σ x := by
      intro h
      exact hx (σ.injective h)
    simp only [permCycleOf, dif_neg hx, dif_neg hfx, Sum.inl.injEq,
      Subtype.mk.injEq]
    exact Equiv.Perm.cycleOf_self_apply σ x

theorem sameCycle_of_permCycleOf_eq (σ : Equiv.Perm α) {x y : α}
    (hxy : permCycleOf σ x = permCycleOf σ y) : σ.SameCycle x y := by
  by_cases hx : σ x = x
  · by_cases hy : σ y = y
    · simp only [permCycleOf, dif_pos hx, dif_pos hy, Sum.inr.injEq,
        Subtype.mk.injEq] at hxy
      subst y
      exact Equiv.Perm.SameCycle.rfl
    · simp [permCycleOf, hx, hy] at hxy
  · by_cases hy : σ y = y
    · simp [permCycleOf, hx, hy] at hxy
    · simp only [permCycleOf, dif_neg hx, dif_neg hy, Sum.inl.injEq,
        Subtype.mk.injEq] at hxy
      exact (Equiv.Perm.sameCycle_iff_cycleOf_eq_of_mem_support
        (Equiv.Perm.mem_support.mpr hx) (Equiv.Perm.mem_support.mpr hy)).mpr hxy

theorem permCycleOf_eq_of_sameCycle (σ : Equiv.Perm α) {x y : α}
    (hxy : σ.SameCycle x y) : permCycleOf σ x = permCycleOf σ y := by
  by_cases hx : σ x = x
  · have hEq : x = y := hxy.eq_of_left hx
    subst y
    rfl
  · have hy : σ y ≠ y := by
      intro hy
      exact hx (hxy.apply_eq_self_iff.mpr hy)
    simp only [permCycleOf, dif_neg hx, dif_neg hy, Sum.inl.injEq,
      Subtype.mk.injEq]
    exact (Equiv.Perm.sameCycle_iff_cycleOf_eq_of_mem_support
      (Equiv.Perm.mem_support.mpr hx) (Equiv.Perm.mem_support.mpr hy)).mp hxy

/-- Total number of cycles, including fixed points. -/
def permCycleCount (σ : Equiv.Perm α) : ℕ := Fintype.card (PermCycle σ)

theorem permCycleCount_eq (σ : Equiv.Perm α) :
    permCycleCount σ = σ.cycleType.card +
      (Fintype.card α - σ.cycleType.sum) := by
  rw [permCycleCount, Fintype.card_sum, Equiv.Perm.card_fixedPoints]
  congr 1
  rw [Equiv.Perm.cycleType_def, Multiset.card_map]
  exact Fintype.card_coe σ.cycleFactorsFinset

/-- The sign parity expressed using the total cycle count. -/
theorem sign_eq_one_iff_even_card_add_cycleCount (σ : Equiv.Perm α) :
    Equiv.Perm.sign σ = 1 ↔ Even (Fintype.card α + permCycleCount σ) := by
  let n := Fintype.card α
  let a := σ.cycleType.sum
  let b := σ.cycleType.card
  have han : a ≤ n := σ.sum_cycleType_le
  have hcount : permCycleCount σ = b + (n - a) := by
    simpa [n, a, b] using permCycleCount_eq σ
  have hparity : Even (a + b) ↔ Even (n + permCycleCount σ) := by
    constructor
    · rintro ⟨k, hk⟩
      refine ⟨k + (n - a), ?_⟩
      omega
    · rintro ⟨k, hk⟩
      have hkn : n - a ≤ k := by omega
      refine ⟨k - (n - a), ?_⟩
      omega
  rw [Equiv.Perm.sign_of_cycleType,
    neg_one_pow_eq_one_iff_even (by decide), hparity]

theorem cycleTypeExponent_even_iff_card_add_cycleCount
    (σ : Equiv.Perm α) :
    Even (σ.cycleType.sum + σ.cycleType.card) ↔
      Even (Fintype.card α + permCycleCount σ) := by
  let n := Fintype.card α
  let a := σ.cycleType.sum
  let b := σ.cycleType.card
  have han : a ≤ n := σ.sum_cycleType_le
  have hcount : permCycleCount σ = b + (n - a) := by
    simpa [n, a, b] using permCycleCount_eq σ
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k + (n - a), ?_⟩
    omega
  · rintro ⟨k, hk⟩
    have hkn : n - a ≤ k := by omega
    refine ⟨k - (n - a), ?_⟩
    omega

end PermCycles

section Incidence

variable {α : Type*} [Fintype α] [DecidableEq α]

abbrev IncidenceVertex (P Q : Equiv.Perm α) := PermCycle P ⊕ PermCycle Q

noncomputable local instance incidenceVertexDecidableEq (P Q : Equiv.Perm α) :
    DecidableEq (IncidenceVertex P Q) := Classical.decEq _

def pCycleVertex (P Q : Equiv.Perm α) (x : α) : IncidenceVertex P Q :=
  Sum.inl (permCycleOf P x)

def qCycleVertex (P Q : Equiv.Perm α) (x : α) : IncidenceVertex P Q :=
  Sum.inr (permCycleOf Q x)

noncomputable def incidenceEdgeCandidates (P Q : Equiv.Perm α) :
    Finset (Sym2 (IncidenceVertex P Q)) :=
  Finset.univ.image fun x => s(pCycleVertex P Q x, qCycleVertex P Q x)

noncomputable def incidenceGraph (P Q : Equiv.Perm α) :
    SimpleGraph (IncidenceVertex P Q) :=
  SimpleGraph.fromEdgeSet (incidenceEdgeCandidates P Q :
    Set (Sym2 (IncidenceVertex P Q)))

noncomputable def incidenceComponentCount (P Q : Equiv.Perm α) : ℕ :=
  Fintype.card (incidenceGraph P Q).ConnectedComponent

theorem incidenceEdgeCandidates_card_le (P Q : Equiv.Perm α) :
    (incidenceEdgeCandidates P Q).card ≤ Fintype.card α := by
  exact Finset.card_image_le.trans_eq Finset.card_univ

theorem incidence_adj (P Q : Equiv.Perm α) (x : α) :
    (incidenceGraph P Q).Adj (pCycleVertex P Q x) (qCycleVertex P Q x) := by
  rw [incidenceGraph, SimpleGraph.fromEdgeSet_adj]
  constructor
  · have hmem : s(pCycleVertex P Q x, qCycleVertex P Q x) ∈
        incidenceEdgeCandidates P Q := by
      apply Finset.mem_image.mpr
      exact ⟨x, Finset.mem_univ _, rfl⟩
    simpa using hmem
  · simp [pCycleVertex, qCycleVertex]

noncomputable def incidenceComponent (P Q : Equiv.Perm α) (x : α) :
    (incidenceGraph P Q).ConnectedComponent :=
  (incidenceGraph P Q).connectedComponentMk (pCycleVertex P Q x)

theorem incidenceComponent_surjective (P Q : Equiv.Perm α) :
    Function.Surjective (incidenceComponent P Q) := by
  intro C
  obtain ⟨v, hvC⟩ := C.nonempty_supp
  have hvEq : (incidenceGraph P Q).connectedComponentMk v = C :=
    (C.mem_supp_iff v).mp hvC
  cases v with
  | inl pC =>
      obtain ⟨x, hx⟩ := permCycleOf_surjective P pC
      refine ⟨x, ?_⟩
      dsimp [incidenceComponent, pCycleVertex]
      rw [hx]
      exact hvEq
  | inr qC =>
      obtain ⟨x, hx⟩ := permCycleOf_surjective Q qC
      refine ⟨x, ?_⟩
      have hadj := incidence_adj P Q x
      have hcomp := ConnectedComponent.sound hadj.reachable
      dsimp [qCycleVertex] at hcomp
      rw [hx] at hcomp
      exact hcomp.trans hvEq

theorem incidenceGraph_edgeFinset_card_le (P Q : Equiv.Perm α) :
    (incidenceGraph P Q).edgeFinset.card ≤ Fintype.card α := by
  have hsubset : (incidenceGraph P Q).edgeFinset ⊆
      incidenceEdgeCandidates P Q := by
    intro e he
    have heSet : e ∈ (incidenceGraph P Q).edgeSet :=
      SimpleGraph.mem_edgeFinset.mp he
    rw [incidenceGraph, SimpleGraph.edgeSet_fromEdgeSet] at heSet
    exact heSet.1
  exact (Finset.card_le_card hsubset).trans (incidenceEdgeCandidates_card_le P Q)

/-- The bipartite cycle-incidence inequality
`c(P)+c(Q) ≤ |E|+components`. -/
theorem two_cycle_counts_le_card_add_components (P Q : Equiv.Perm α) :
    permCycleCount P + permCycleCount Q ≤
      Fintype.card α + incidenceComponentCount P Q := by
  have hrank := card_vertices_le_card_edges_add_components (incidenceGraph P Q)
  have hedge := incidenceGraph_edgeFinset_card_le P Q
  simpa [IncidenceVertex, permCycleCount, incidenceComponentCount,
    Fintype.card_sum] using (hrank.trans (Nat.add_le_add_right hedge _))

theorem incidenceComponent_apply_P (P Q : Equiv.Perm α) (x : α) :
    incidenceComponent P Q (P x) = incidenceComponent P Q x := by
  dsimp [incidenceComponent, pCycleVertex]
  rw [permCycleOf_apply]

theorem incidenceComponent_apply_Q (P Q : Equiv.Perm α) (x : α) :
    incidenceComponent P Q (Q x) = incidenceComponent P Q x := by
  have hx := ConnectedComponent.sound (incidence_adj P Q x).reachable
  have hQx := ConnectedComponent.sound (incidence_adj P Q (Q x)).reachable
  have hqclass : qCycleVertex P Q (Q x) = qCycleVertex P Q x := by
    simp only [qCycleVertex, permCycleOf_apply]
  rw [hqclass] at hQx
  exact hQx.trans hx.symm

theorem incidenceComponent_apply_mul (P Q : Equiv.Perm α) (x : α) :
    incidenceComponent P Q ((P * Q) x) = incidenceComponent P Q x := by
  rw [Equiv.Perm.mul_apply, incidenceComponent_apply_P,
    incidenceComponent_apply_Q]

theorem incidenceComponent_apply_mul_pow (P Q : Equiv.Perm α)
    (n : ℕ) (x : α) :
    incidenceComponent P Q (((P * Q) ^ n) x) = incidenceComponent P Q x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Equiv.Perm.mul_apply]
      exact (ih ((P * Q) x)).trans (incidenceComponent_apply_mul P Q x)

theorem incidenceComponent_eq_of_product_sameCycle (P Q : Equiv.Perm α)
    {x y : α} (hxy : (P * Q).SameCycle x y) :
    incidenceComponent P Q x = incidenceComponent P Q y := by
  obtain ⟨n, _hnpos, _hnbound, hnxy⟩ := hxy.exists_pow_eq (P * Q)
  have hpow := incidenceComponent_apply_mul_pow P Q n x
  rw [hnxy] at hpow
  exact hpow.symm

noncomputable def permCycleRepresentative (σ : Equiv.Perm α)
    (C : PermCycle σ) : α :=
  Classical.choose (permCycleOf_surjective σ C)

theorem permCycleRepresentative_spec (σ : Equiv.Perm α)
    (C : PermCycle σ) :
    permCycleOf σ (permCycleRepresentative σ C) = C :=
  Classical.choose_spec (permCycleOf_surjective σ C)

noncomputable def productCycleToIncidenceComponent (P Q : Equiv.Perm α)
    (C : PermCycle (P * Q)) : (incidenceGraph P Q).ConnectedComponent :=
  incidenceComponent P Q (permCycleRepresentative (P * Q) C)

theorem productCycleToIncidenceComponent_surjective (P Q : Equiv.Perm α) :
    Function.Surjective (productCycleToIncidenceComponent P Q) := by
  intro K
  obtain ⟨x, hxK⟩ := incidenceComponent_surjective P Q K
  let C := permCycleOf (P * Q) x
  refine ⟨C, ?_⟩
  have hsame : (P * Q).SameCycle
      (permCycleRepresentative (P * Q) C) x := by
    apply sameCycle_of_permCycleOf_eq
    rw [permCycleRepresentative_spec]
  have hcomp := incidenceComponent_eq_of_product_sameCycle P Q hsame
  exact hcomp.trans hxK

/-- Every incidence component contains at least one cycle of `P*Q`. -/
theorem incidence_components_le_product_cycles (P Q : Equiv.Perm α) :
    incidenceComponentCount P Q ≤ permCycleCount (P * Q) := by
  exact Fintype.card_le_of_surjective
    (productCycleToIncidenceComponent P Q)
    (productCycleToIncidenceComponent_surjective P Q)

/-! ## Parity and the exact Euler reduction -/

/-- The parity half of the permutation-map Euler formula. -/
theorem permutationMap_cycle_sum_parity (P Q : Equiv.Perm α) :
    Even (Fintype.card α + permCycleCount P + permCycleCount Q +
      permCycleCount (P * Q)) := by
  let eP := P.cycleType.sum + P.cycleType.card
  let eQ := Q.cycleType.sum + Q.cycleType.card
  let eR := (P * Q).cycleType.sum + (P * Q).cycleType.card
  have hpow : (-1 : ℤˣ) ^ (eP + eQ + eR) = 1 := by
    change (-1 : ℤˣ) ^ ((eP + eQ) + eR) = 1
    calc
      (-1 : ℤˣ) ^ ((eP + eQ) + eR) =
          (-1 : ℤˣ) ^ (eP + eQ) * (-1 : ℤˣ) ^ eR :=
        pow_add _ _ _
      _ = (((-1 : ℤˣ) ^ eP * (-1 : ℤˣ) ^ eQ) *
          (-1 : ℤˣ) ^ eR) := by
        exact congrArg (fun z : ℤˣ => z * (-1 : ℤˣ) ^ eR)
          (pow_add (-1 : ℤˣ) eP eQ)
      _ = 1 := by
        have hp : (-1 : ℤˣ) ^ eP = Equiv.Perm.sign P := by
          dsimp [eP]
          exact (Equiv.Perm.sign_of_cycleType P).symm
        have hq : (-1 : ℤˣ) ^ eQ = Equiv.Perm.sign Q := by
          dsimp [eQ]
          exact (Equiv.Perm.sign_of_cycleType Q).symm
        have hr : (-1 : ℤˣ) ^ eR = Equiv.Perm.sign (P * Q) := by
          dsimp [eR]
          exact (Equiv.Perm.sign_of_cycleType (P * Q)).symm
        calc
          ((-1 : ℤˣ) ^ eP * (-1 : ℤˣ) ^ eQ) *
              (-1 : ℤˣ) ^ eR =
              (Equiv.Perm.sign P * Equiv.Perm.sign Q) *
                Equiv.Perm.sign (P * Q) :=
            congrArg₂ (fun x y : ℤˣ => x * y)
              (congrArg₂ (fun x y : ℤˣ => x * y) hp hq) hr
          _ = Equiv.Perm.sign (P * Q) * Equiv.Perm.sign (P * Q) := by
            rw [Equiv.Perm.sign_mul]
          _ = 1 := by
            simpa [pow_two] using Int.units_sq (Equiv.Perm.sign (P * Q))
  have he : Even (eP + eQ + eR) :=
    (neg_one_pow_eq_one_iff_even (R := ℤˣ) (by decide)).mp hpow
  have hP := cycleTypeExponent_even_iff_card_add_cycleCount P
  have hQ := cycleTypeExponent_even_iff_card_add_cycleCount Q
  have hR := cycleTypeExponent_even_iff_card_add_cycleCount (P * Q)
  dsimp [eP, eQ, eR] at he
  have hlarge : Even ((Fintype.card α + permCycleCount P) +
      (Fintype.card α + permCycleCount Q) +
      (Fintype.card α + permCycleCount (P * Q))) := by
    simpa only [Nat.even_add, hP, hQ, hR] using he
  rcases hlarge with ⟨z, hz⟩
  refine ⟨z - Fintype.card α, ?_⟩
  omega

/-- Once the face inequality is known, parity makes its deficit twice a
natural number.  This is the exact algebraic form of the Euler formula. -/
theorem permutationMapEulerFormula_of_face_bound (P Q : Equiv.Perm α)
    (k : ℕ)
    (hface : permCycleCount P + permCycleCount Q + permCycleCount (P * Q) ≤
      Fintype.card α + 2 * k) :
    ∃ g : ℕ,
      permCycleCount P + permCycleCount Q + permCycleCount (P * Q) + 2 * g =
        Fintype.card α + 2 * k := by
  let lhs := permCycleCount P + permCycleCount Q + permCycleCount (P * Q)
  let rhs := Fintype.card α + 2 * k
  have hpar := permutationMap_cycle_sum_parity P Q
  have hEvenDeficit : Even (rhs - lhs) := by
    rcases hpar with ⟨z, hz⟩
    have hzle : z ≤ Fintype.card α + k := by
      dsimp [lhs, rhs] at *
      omega
    refine ⟨Fintype.card α + k - z, ?_⟩
    dsimp [lhs, rhs] at *
    omega
  rcases hEvenDeficit with ⟨g, hg⟩
  refine ⟨g, ?_⟩
  dsimp [lhs, rhs] at *
  omega

/-! ## A linear-algebra proof of the face inequality -/

/-- The real vector space fixed by a permutation. -/
def permFixedSubmodule (P : Equiv.Perm α) : Submodule ℝ (α → ℝ) where
  carrier := {v | ∀ x, v (P x) = v x}
  zero_mem' := by simp
  add_mem' := by
    intro u v hu hv x
    simp only [Pi.add_apply, hu x, hv x]
  smul_mem' := by
    intro c v hv x
    simp only [Pi.smul_apply, hv x]

theorem permFixed_apply_pow (P : Equiv.Perm α)
    (v : permFixedSubmodule P) (n : ℕ) (x : α) :
    v.1 ((P ^ n) x) = v.1 x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ, Equiv.Perm.mul_apply, ih, v.2]

theorem permFixed_eq_of_sameCycle (P : Equiv.Perm α)
    (v : permFixedSubmodule P) {x y : α} (hxy : P.SameCycle x y) :
    v.1 x = v.1 y := by
  obtain ⟨n, _hnpos, _hnbound, hnxy⟩ := hxy.exists_pow_eq P
  have hpow := permFixed_apply_pow P v n x
  rw [hnxy] at hpow
  exact hpow.symm

/-- A fixed vector is exactly a choice of one scalar per permutation cycle. -/
noncomputable def cycleFunctionsEquivFixed (P : Equiv.Perm α) :
    (PermCycle P → ℝ) ≃ₗ[ℝ] permFixedSubmodule P where
  toFun f := ⟨fun x => f (permCycleOf P x), by
    intro x
    change f (permCycleOf P (P x)) = f (permCycleOf P x)
    rw [permCycleOf_apply]⟩
  invFun v := fun C => v.1 (permCycleRepresentative P C)
  left_inv f := by
    funext C
    exact congrArg f (permCycleRepresentative_spec P C)
  right_inv v := by
    apply Subtype.ext
    funext x
    apply permFixed_eq_of_sameCycle P v
    apply sameCycle_of_permCycleOf_eq
    exact permCycleRepresentative_spec P (permCycleOf P x)
  map_add' f g := rfl
  map_smul' c f := rfl

theorem finrank_permFixedSubmodule (P : Equiv.Perm α) :
    Module.finrank ℝ (permFixedSubmodule P) = permCycleCount P := by
  rw [← (cycleFunctionsEquivFixed P).finrank_eq, Module.finrank_pi]
  rfl

/-- The standard dot product, regarded purely as a bilinear form. -/
noncomputable abbrev permutationDot : LinearMap.BilinForm ℝ (α → ℝ) :=
  dotProductBilin ℝ ℝ

theorem permutationDot_apply (u v : α → ℝ) :
    permutationDot u v = ∑ x, u x * v x := rfl

theorem permutationDot_isSymm :
    (permutationDot (α := α)).IsSymm := by
  refine ⟨?_⟩
  intro u v
  exact dotProduct_comm u v

theorem permutationDot_nondegenerate :
    (permutationDot (α := α)).Nondegenerate := by
  constructor
  · intro v hv
    funext x
    change v x = 0
    have hx := hv (Pi.single x 1)
    change v ⬝ᵥ Pi.single x 1 = 0 at hx
    rw [dotProduct_single_one] at hx
    exact hx
  · intro v hv
    funext x
    change v x = 0
    have hx := hv (Pi.single x 1)
    change Pi.single x 1 ⬝ᵥ v = 0 at hx
    rw [single_one_dotProduct] at hx
    exact hx

/-- On vectors fixed by `P*Q`, compare a vector with its `Q⁻¹`-translate. -/
def cycleDelta (P Q : Equiv.Perm α) :
    permFixedSubmodule (P * Q) →ₗ[ℝ] (α → ℝ) where
  toFun z := fun x => z.1 (Q.symm x) - z.1 x
  map_add' z w := by
    funext x
    simp only [Submodule.coe_add, Pi.add_apply]
    ring
  map_smul' c z := by
    funext x
    simp only [Submodule.coe_smul_of_tower, Pi.smul_apply, RingHom.id_apply]
    ring

theorem cycleDelta_ker_fixed_Q (P Q : Equiv.Perm α)
    (z : LinearMap.ker (cycleDelta P Q)) :
    ∀ x, z.1.1 (Q x) = z.1.1 x := by
  intro x
  have hz := congrFun (show cycleDelta P Q z.1 = 0 from z.2) (Q x)
  change z.1.1 (Q.symm (Q x)) - z.1.1 (Q x) = 0 at hz
  rw [Q.symm_apply_apply] at hz
  linarith

theorem cycleDelta_ker_fixed_P (P Q : Equiv.Perm α)
    (z : LinearMap.ker (cycleDelta P Q)) :
    ∀ x, z.1.1 (P x) = z.1.1 x := by
  intro x
  have hPQ := z.1.2 (Q.symm x)
  change z.1.1 (P (Q (Q.symm x))) = z.1.1 (Q.symm x) at hPQ
  rw [Q.apply_symm_apply] at hPQ
  have hz := congrFun (show cycleDelta P Q z.1 = 0 from z.2) x
  change z.1.1 (Q.symm x) - z.1.1 x = 0 at hz
  linarith

/-- The kernel of `cycleDelta` injects into the common fixed space. -/
def commonFixedSubmodule (P Q : Equiv.Perm α) : Submodule ℝ (α → ℝ) :=
  permFixedSubmodule P ⊓ permFixedSubmodule Q

def fixedSupSubmodule (P Q : Equiv.Perm α) : Submodule ℝ (α → ℝ) :=
  permFixedSubmodule P ⊔ permFixedSubmodule Q

def cycleDeltaKerToInf (P Q : Equiv.Perm α) :
    LinearMap.ker (cycleDelta P Q) →ₗ[ℝ]
      commonFixedSubmodule P Q where
  toFun z := ⟨z.1.1, cycleDelta_ker_fixed_P P Q z,
    cycleDelta_ker_fixed_Q P Q z⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem cycleDeltaKerToInf_injective (P Q : Equiv.Perm α) :
    Function.Injective (cycleDeltaKerToInf P Q) := by
  intro z w hzw
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun t : commonFixedSubmodule P Q => t.1) hzw

theorem cycleDelta_ker_finrank_le_inf (P Q : Equiv.Perm α) :
    Module.finrank ℝ (LinearMap.ker (cycleDelta P Q)) ≤
      Module.finrank ℝ (commonFixedSubmodule P Q) := by
  exact (cycleDeltaKerToInf P Q).finrank_le_finrank_of_injective
    (cycleDeltaKerToInf_injective P Q)

theorem permFixed_apply_symm (P : Equiv.Perm α)
    (v : permFixedSubmodule P) (x : α) :
    v.1 (P.symm x) = v.1 x := by
  have h := v.2 (P.symm x)
  rw [P.apply_symm_apply] at h
  exact h.symm

theorem cycleDelta_eq_P_sub (P Q : Equiv.Perm α)
    (z : permFixedSubmodule (P * Q)) (x : α) :
    cycleDelta P Q z x = z.1 (P x) - z.1 x := by
  have h := z.2 (Q.symm x)
  change z.1 (P (Q (Q.symm x))) = z.1 (Q.symm x) at h
  rw [Q.apply_symm_apply] at h
  change z.1 (Q.symm x) - z.1 x = z.1 (P x) - z.1 x
  rw [← h]

theorem cycleDelta_orthogonal_fixed_Q (P Q : Equiv.Perm α)
    (z : permFixedSubmodule (P * Q)) (u : permFixedSubmodule Q) :
    permutationDot u.1 (cycleDelta P Q z) = 0 := by
  rw [permutationDot_apply]
  change (∑ x, u.1 x * (z.1 (Q.symm x) - z.1 x)) = 0
  simp_rw [mul_sub, Finset.sum_sub_distrib, sub_eq_zero]
  calc
    (∑ x, u.1 x * z.1 (Q.symm x)) =
        ∑ x, u.1 (Q x) * z.1 x := by
      simpa using Q.symm.sum_comp (fun x => u.1 (Q x) * z.1 x)
    _ = ∑ x, u.1 x * z.1 x := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [u.2]

theorem cycleDelta_orthogonal_fixed_P (P Q : Equiv.Perm α)
    (z : permFixedSubmodule (P * Q)) (u : permFixedSubmodule P) :
    permutationDot u.1 (cycleDelta P Q z) = 0 := by
  rw [permutationDot_apply]
  have hpoint : ∀ x, cycleDelta P Q z x = z.1 (P x) - z.1 x :=
    cycleDelta_eq_P_sub P Q z
  simp_rw [hpoint, mul_sub, Finset.sum_sub_distrib, sub_eq_zero]
  calc
    (∑ x, u.1 x * z.1 (P x)) =
        ∑ x, u.1 (P.symm x) * z.1 x := by
      simpa using (show α ≃ α from P).sum_comp
        (fun x => u.1 (P.symm x) * z.1 x)
    _ = ∑ x, u.1 x * z.1 x := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [permFixed_apply_symm P u]

theorem cycleDelta_mem_orthogonal_sup (P Q : Equiv.Perm α)
    (z : permFixedSubmodule (P * Q)) :
    cycleDelta P Q z ∈
      (permutationDot (α := α)).orthogonal
        (permFixedSubmodule P ⊔ permFixedSubmodule Q) := by
  intro u hu
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hu
  change permutationDot (p + q) (cycleDelta P Q z) = 0
  rw [map_add]
  have hp0 := cycleDelta_orthogonal_fixed_P P Q z ⟨p, hp⟩
  have hq0 := cycleDelta_orthogonal_fixed_Q P Q z ⟨q, hq⟩
  change permutationDot p (cycleDelta P Q z) +
      permutationDot q (cycleDelta P Q z) = 0
  rw [hp0, hq0, add_zero]

theorem cycleDelta_range_le_orthogonal_sup (P Q : Equiv.Perm α) :
    LinearMap.range (cycleDelta P Q) ≤
      (permutationDot (α := α)).orthogonal
        (fixedSupSubmodule P Q) := by
  rintro _ ⟨z, rfl⟩
  exact cycleDelta_mem_orthogonal_sup P Q z

/-- The dimension inequality underlying the permutation-map Euler bound. -/
theorem permutation_fixed_space_inequality (P Q : Equiv.Perm α) :
    Module.finrank ℝ (permFixedSubmodule P) +
        Module.finrank ℝ (permFixedSubmodule Q) +
        Module.finrank ℝ (permFixedSubmodule (P * Q)) ≤
      Fintype.card α + 2 * Module.finrank ℝ (commonFixedSubmodule P Q) := by
  let pDim := Module.finrank ℝ (permFixedSubmodule P)
  let qDim := Module.finrank ℝ (permFixedSubmodule Q)
  let zDim := Module.finrank ℝ (permFixedSubmodule (P * Q))
  let iDim := Module.finrank ℝ (commonFixedSubmodule P Q)
  let sDim := Module.finrank ℝ (fixedSupSubmodule P Q)
  let rDim := Module.finrank ℝ (LinearMap.range (cycleDelta P Q))
  let kDim := Module.finrank ℝ (LinearMap.ker (cycleDelta P Q))
  let oDim := Module.finrank ℝ
    ((permutationDot (α := α)).orthogonal (fixedSupSubmodule P Q))
  have hSupInf : sDim + iDim = pDim + qDim := by
    dsimp [sDim, iDim, pDim, qDim, fixedSupSubmodule, commonFixedSubmodule]
    exact Submodule.finrank_sup_add_finrank_inf_eq
      (permFixedSubmodule P) (permFixedSubmodule Q)
  have hRankNullity : rDim + kDim = zDim := by
    dsimp [rDim, kDim, zDim]
    exact LinearMap.finrank_range_add_finrank_ker (cycleDelta P Q)
  have hKer : kDim ≤ iDim := by
    dsimp [kDim, iDim]
    exact cycleDelta_ker_finrank_le_inf P Q
  have hRange : rDim ≤ oDim := by
    dsimp [rDim, oDim]
    exact Submodule.finrank_mono (cycleDelta_range_le_orthogonal_sup P Q)
  have hAmbient : Module.finrank ℝ (α → ℝ) = Fintype.card α :=
    Module.finrank_pi ℝ
  have hOrth : oDim = Fintype.card α - sDim := by
    dsimp [oDim, sDim]
    rw [LinearMap.BilinForm.finrank_orthogonal
      (permutationDot_nondegenerate (α := α)), hAmbient]
  have hSupLe : sDim ≤ Fintype.card α := by
    dsimp [sDim]
    rw [← hAmbient]
    exact Submodule.finrank_le _
  omega

/-! The common fixed space has one degree of freedom per incidence component. -/

noncomputable def incidenceVertexValue (P Q : Equiv.Perm α)
    (v : commonFixedSubmodule P Q) : IncidenceVertex P Q → ℝ
  | Sum.inl C => v.1 (permCycleRepresentative P C)
  | Sum.inr C => v.1 (permCycleRepresentative Q C)

theorem incidenceVertexValue_pCycleVertex (P Q : Equiv.Perm α)
    (v : commonFixedSubmodule P Q) (x : α) :
    incidenceVertexValue P Q v (pCycleVertex P Q x) = v.1 x := by
  apply permFixed_eq_of_sameCycle P ⟨v.1, v.2.1⟩
  apply sameCycle_of_permCycleOf_eq
  exact permCycleRepresentative_spec P (permCycleOf P x)

theorem incidenceVertexValue_qCycleVertex (P Q : Equiv.Perm α)
    (v : commonFixedSubmodule P Q) (x : α) :
    incidenceVertexValue P Q v (qCycleVertex P Q x) = v.1 x := by
  apply permFixed_eq_of_sameCycle Q ⟨v.1, v.2.2⟩
  apply sameCycle_of_permCycleOf_eq
  exact permCycleRepresentative_spec Q (permCycleOf Q x)

theorem incidenceVertexValue_eq_of_adj (P Q : Equiv.Perm α)
    (v : commonFixedSubmodule P Q) {a b : IncidenceVertex P Q}
    (hab : (incidenceGraph P Q).Adj a b) :
    incidenceVertexValue P Q v a = incidenceVertexValue P Q v b := by
  have hab' := hab
  rw [incidenceGraph, SimpleGraph.fromEdgeSet_adj] at hab'
  have hmem : s(a, b) ∈ incidenceEdgeCandidates P Q := by
    simpa using hab'.1
  obtain ⟨x, _hx, hxedge⟩ := Finset.mem_image.mp hmem
  rw [Sym2.eq_iff] at hxedge
  rcases hxedge with hxedge | hxedge
  · rcases hxedge with ⟨rfl, rfl⟩
    rw [incidenceVertexValue_pCycleVertex,
      incidenceVertexValue_qCycleVertex]
  · rcases hxedge with ⟨rfl, rfl⟩
    rw [incidenceVertexValue_qCycleVertex,
      incidenceVertexValue_pCycleVertex]

theorem incidenceVertexValue_eq_of_walk (P Q : Equiv.Perm α)
    (v : commonFixedSubmodule P Q) {a b : IncidenceVertex P Q}
    (w : (incidenceGraph P Q).Walk a b) :
    incidenceVertexValue P Q v a = incidenceVertexValue P Q v b := by
  induction w with
  | nil => rfl
  | cons h w ih =>
      exact (incidenceVertexValue_eq_of_adj P Q v h).trans ih

theorem commonFixed_eq_of_incidenceComponent_eq (P Q : Equiv.Perm α)
    (v : commonFixedSubmodule P Q) {x y : α}
    (hxy : incidenceComponent P Q x = incidenceComponent P Q y) :
    v.1 x = v.1 y := by
  have hreach : (incidenceGraph P Q).Reachable
      (pCycleVertex P Q x) (pCycleVertex P Q y) := by
    exact ConnectedComponent.exact hxy
  apply hreach.elim
  intro w
  rw [← incidenceVertexValue_pCycleVertex P Q v x,
    ← incidenceVertexValue_pCycleVertex P Q v y]
  exact incidenceVertexValue_eq_of_walk P Q v w

noncomputable def incidencePointRepresentative (P Q : Equiv.Perm α)
    (K : (incidenceGraph P Q).ConnectedComponent) : α :=
  Classical.choose (incidenceComponent_surjective P Q K)

theorem incidencePointRepresentative_spec (P Q : Equiv.Perm α)
    (K : (incidenceGraph P Q).ConnectedComponent) :
    incidenceComponent P Q (incidencePointRepresentative P Q K) = K :=
  Classical.choose_spec (incidenceComponent_surjective P Q K)

noncomputable def commonFixedToComponentValues (P Q : Equiv.Perm α) :
    commonFixedSubmodule P Q →ₗ[ℝ]
      ((incidenceGraph P Q).ConnectedComponent → ℝ) where
  toFun v := fun K => v.1 (incidencePointRepresentative P Q K)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem commonFixedToComponentValues_injective (P Q : Equiv.Perm α) :
    Function.Injective (commonFixedToComponentValues P Q) := by
  intro v w hvw
  apply Subtype.ext
  funext x
  let K := incidenceComponent P Q x
  have hrep : incidenceComponent P Q (incidencePointRepresentative P Q K) =
      incidenceComponent P Q x := by
    exact incidencePointRepresentative_spec P Q K
  have hvrep := commonFixed_eq_of_incidenceComponent_eq P Q v hrep
  have hwrep := commonFixed_eq_of_incidenceComponent_eq P Q w hrep
  have hat := congrFun hvw K
  change v.1 (incidencePointRepresentative P Q K) =
      w.1 (incidencePointRepresentative P Q K) at hat
  exact hvrep.symm.trans (hat.trans hwrep)

/-- Common fixed vectors are exactly scalar functions on the components of
the cycle-incidence graph. -/
noncomputable def componentFunctionsEquivCommonFixed (P Q : Equiv.Perm α) :
    ((incidenceGraph P Q).ConnectedComponent → ℝ) ≃ₗ[ℝ]
      commonFixedSubmodule P Q where
  toFun f := ⟨fun x => f (incidenceComponent P Q x),
    by
      constructor
      · intro x
        change f (incidenceComponent P Q (P x)) =
          f (incidenceComponent P Q x)
        rw [incidenceComponent_apply_P]
      · intro x
        change f (incidenceComponent P Q (Q x)) =
          f (incidenceComponent P Q x)
        rw [incidenceComponent_apply_Q]⟩
  invFun := commonFixedToComponentValues P Q
  left_inv f := by
    funext K
    change f (incidenceComponent P Q
      (incidencePointRepresentative P Q K)) = f K
    rw [incidencePointRepresentative_spec]
  right_inv v := by
    apply Subtype.ext
    funext x
    apply commonFixed_eq_of_incidenceComponent_eq P Q v
    exact incidencePointRepresentative_spec P Q (incidenceComponent P Q x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem commonFixed_finrank_eq_incidenceComponentCount (P Q : Equiv.Perm α) :
    Module.finrank ℝ (commonFixedSubmodule P Q) =
      incidenceComponentCount P Q := by
  rw [← (componentFunctionsEquivCommonFixed P Q).finrank_eq,
    Module.finrank_pi]
  rfl

theorem commonFixed_finrank_le_incidenceComponentCount (P Q : Equiv.Perm α) :
    Module.finrank ℝ (commonFixedSubmodule P Q) ≤
      incidenceComponentCount P Q := by
  exact (commonFixed_finrank_eq_incidenceComponentCount P Q).le

/-- The full face inequality for two finite permutations. -/
theorem permutationMap_face_bound (P Q : Equiv.Perm α) :
    permCycleCount P + permCycleCount Q + permCycleCount (P * Q) ≤
      Fintype.card α + 2 * incidenceComponentCount P Q := by
  calc
    permCycleCount P + permCycleCount Q + permCycleCount (P * Q) =
        Module.finrank ℝ (permFixedSubmodule P) +
          Module.finrank ℝ (permFixedSubmodule Q) +
          Module.finrank ℝ (permFixedSubmodule (P * Q)) := by
      rw [finrank_permFixedSubmodule, finrank_permFixedSubmodule,
        finrank_permFixedSubmodule]
    _ ≤ Fintype.card α +
        2 * Module.finrank ℝ (commonFixedSubmodule P Q) :=
      permutation_fixed_space_inequality P Q
    _ ≤ Fintype.card α + 2 * incidenceComponentCount P Q := by
      exact Nat.add_le_add_left
        (Nat.mul_le_mul_left 2 (commonFixed_finrank_le_incidenceComponentCount P Q)) _

/-- Euler's formula for the permutation map generated by `P` and `Q`.
The natural number `g` is the (possibly disconnected) total genus. -/
theorem permutationMapEulerFormula (P Q : Equiv.Perm α) :
    ∃ g : ℕ,
      permCycleCount P + permCycleCount Q + permCycleCount (P * Q) + 2 * g =
        Fintype.card α + 2 * incidenceComponentCount P Q := by
  exact permutationMapEulerFormula_of_face_bound P Q
    (incidenceComponentCount P Q) (permutationMap_face_bound P Q)

end Incidence

end Superperm7
