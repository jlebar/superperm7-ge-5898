/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE); this file is
additionally subject to the upstream MIT notice below.

Adapted from https://github.com/BGray-wrl/superperm6
  file:   formal-verification/Superperm6/Structural.lean
  commit: d8a932d8f61d80b0bcfc737bd0e235a8300449c4
  upstream copyright: Copyright (c) 2026 Benjamin Grayzel — MIT License (reproduced in NOTICE).
Local modifications (port from six to seven symbols; see docs/PORT_LOG.md): structural counts with budget r + q + p <= 134 and defect <= 13 in place of the n = 6 frontier equality; k = 120 + m - r + a.
-/
import Superperm7.Orbit
import Superperm7.Euler
import Superperm7.Registry

/-!
# Route-to-registry structural counts (n = 7)

This file carries a normalized light Hamilton route through the
quotient-graph rank calculation.  Unlike the `n = 6` development there is
no frontier lift: `p` is the route's actual path count `highCostCount + 1`
and the defect is only bounded, `m + a + b + η ≤ 13`.  The exact relation
`5877 + (m + a + b + η) ≤ routeWeight route` is also exposed
(`RouteStructuralCounts.defect_add_le_weight`), so a sharper weight bound
gives a sharper defect bound (weight `≤ 5889` gives `D ≤ 12`).
-/

namespace Superperm7

/-- The numerical structural data obtained before invoking the
permutation-map face calculation. -/
structure RouteStructuralCounts (route : List Perm7)
    (hroute : IsHamiltonianRoute route) where
  r : ℕ
  q : ℕ
  p : ℕ
  M : ℕ
  k : ℕ
  m : ℕ
  a : ℕ
  b : ℕ
  eta : ℕ
  runStart_card : (runStartSet route).card = 720 + r
  chainStart_card : (chainStartSet route).card = q
  p_route : p = highCostCount route + 1
  M_route : M = (touchedBlocks route).card
  k_route : k = rotationComponentCount route hroute
  budget : r + q + p ≤ 134
  p_pos : 1 ≤ p
  p_le_q : p ≤ q
  M_eq : M = 120 + m
  k_eq : k = 120 + m - r + a
  q_eq : q = k + b
  p_eq : p = eta + 1
  defect_le : m + a + b + eta ≤ 13
  a_le_r : a ≤ r
  r_le_six_m : r ≤ 6 * m
  k_le_M : k ≤ M
  k_le_q : k ≤ q

namespace RouteStructuralCounts

variable {route : List Perm7} {hroute : IsHamiltonianRoute route}

/-- The capped weight identity `7 + cappedRouteWeight = 5763 + r + q + p`
holds for the structural `r, q, p` (they are the route's actual counts). -/
theorem capped_weight_eq (z : RouteStructuralCounts route hroute) :
    7 + cappedRouteWeight route = 5763 + z.r + z.q + z.p := by
  have hs := z.runStart_card
  have hc := z.chainStart_card
  have hp := z.p_route
  rw [runStartSet_card hroute] at hs
  rw [chainStartSet_card hroute] at hc
  have hpart := route_edge_count_partition hroute.1
  have hlen := hamiltonian_route_length hroute
  have hx1 := costOneCount_le_4320 hroute
  rw [cappedRouteWeight_eq_counts hroute.1]
  omega

/-- `r + q + p = 121 + D`. -/
theorem budget_eq_defect (z : RouteStructuralCounts route hroute) :
    z.r + z.q + z.p = 121 + (z.m + z.a + z.b + z.eta) := by
  have hM := z.M_eq
  have hk := z.k_eq
  have hq := z.q_eq
  have hp := z.p_eq
  have hkM := z.k_le_M
  have hrm := z.r_le_six_m
  have hD := z.defect_le
  omega

/-- The exact weight/defect relation: `5877 + D ≤ routeWeight route`.  In
particular weight `≤ 5889` forces `D ≤ 12` and weight `≤ 5890` forces
`D ≤ 13`. -/
theorem defect_add_le_weight (z : RouteStructuralCounts route hroute) :
    5877 + (z.m + z.a + z.b + z.eta) ≤ routeWeight route := by
  have hcap := z.capped_weight_eq
  have hD := z.budget_eq_defect
  have hle := cappedRouteWeight_le route
  omega

theorem defect_le_of_weight_le (z : RouteStructuralCounts route hroute) {W : ℕ}
    (hweight : routeWeight route ≤ W) :
    z.m + z.a + z.b + z.eta + 5877 ≤ W := by
  have h := z.defect_add_le_weight
  omega

theorem defect_le_twelve_of_weight_le_5889 (z : RouteStructuralCounts route hroute)
    (hweight : routeWeight route ≤ 5889) :
    z.m + z.a + z.b + z.eta ≤ 12 := by
  have h := z.defect_add_le_weight
  omega

end RouteStructuralCounts

/-- Every normalized Hamilton route of weight at most 5890 supplies all of
the Section 4 counts through `D ≤ 13`, before the face-fragmentation
identity. -/
theorem routeStructuralCounts_of_weight_at_most_5890 {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (hweight : routeWeight route ≤ 5890) :
    Nonempty (RouteStructuralCounts route hroute) := by
  obtain ⟨x, hadm, hloss, hx1, hx2, _hx3, hx4, _hcap⟩ :=
    cheap_cover_profile_of_weight_at_most_5890 hroute hweight
  have horbit := route_profile_orbit_inequality hroute hnormal x hadm hx1 hx2
  have hadm' := hadm
  rcases hadm' with ⟨hr600, hp0pos, hp0q, hqbound⟩
  have hloss' : x.r + x.q + x.p ≤ 134 := by
    dsimp [CheapCoverProfile.loss] at hloss
    omega
  have hpRoute : x.p = highCostCount route + 1 := by omega
  let M := (touchedBlocks route).card
  let k := rotationComponentCount route hroute
  have hsCard0 := runStartSet_card hroute
  have hcCard0 := chainStartSet_card hroute
  have hpart := route_edge_count_partition hroute.1
  have hlen := hamiltonian_route_length hroute
  have hsCard : (runStartSet route).card = 720 + x.r := by
    dsimp [CheapCoverProfile.admissible] at hadm
    omega
  have hcCard : (chainStartSet route).card = x.q := by
    dsimp [CheapCoverProfile.admissible] at hadm
    omega
  have hfit0 := runStartSet_card_le_six_mul_touchedBlocks route
  have hfit : 720 + x.r ≤ 6 * M := by
    dsimp [M]
    omega
  have hKQ0 := rotationComponentCount_le_chains hroute hnormal
  have hKQ : k ≤ x.q := by
    dsimp [k]
    omega
  have hKM0 := rotationComponentCount_le_touchedBlocks hroute
  have hKM : k ≤ M := by
    dsimp [k, M]
    exact hKM0
  have hMRank0 := touchedBlocks_card_le_run_excess_add_components hroute
  have hMRank : M ≤ x.r + k := by
    dsimp [M, k]
    omega
  have hM120 : 120 ≤ M := by omega
  let m := M - 120
  let a := x.r - (M - k)
  let b := x.q - k
  let eta := x.p - 1
  have hMkR : M - k ≤ x.r := by omega
  have hMeq : M = 120 + m := by
    dsimp [m]
    omega
  have hrm : x.r ≤ 6 * m := by
    dsimp [m]
    omega
  have hkeq : k = 120 + m - x.r + a := by
    dsimp [m, a]
    omega
  have hqeq : x.q = k + b := by
    dsimp [b]
    omega
  have hpeq : x.p = eta + 1 := by
    dsimp [eta]
    omega
  have hdefect : m + a + b + eta ≤ 13 := by
    exact defect_bound_identity hkeq hqeq hpeq hloss' (by omega)
  have haR : a ≤ x.r := by
    dsimp [a]
    omega
  let z : RouteStructuralCounts route hroute :=
    { r := x.r
      q := x.q
      p := x.p
      M := M
      k := k
      m := m
      a := a
      b := b
      eta := eta
      runStart_card := hsCard
      chainStart_card := hcCard
      p_route := hpRoute
      M_route := rfl
      k_route := rfl
      budget := hloss'
      p_pos := hp0pos
      p_le_q := hp0q
      M_eq := hMeq
      k_eq := hkeq
      q_eq := hqeq
      p_eq := hpeq
      defect_le := hdefect
      a_le_r := haR
      r_le_six_m := hrm
      k_le_M := hKM
      k_le_q := hKQ }
  exact ⟨z⟩

/-- The remaining mathematical content of (4.6)--(4.8), stated on the
already extracted route counts. -/
def RouteStructuralCounts.HasFaceFragmentation
    {route : List Perm7} {hroute : IsHamiltonianRoute route}
    (z : RouteStructuralCounts route hroute) : Prop :=
  ∃ g h : ℕ, 2 * g ≤ z.a ∧ z.b + 2 * g = z.a + h

/-- The exact interface needed from the route-specific construction of
`F`, `A`, and `T=F*A`.  The generic Euler theorem itself is already proved
in `Euler.lean`; the only cover-specific condition here is that every
product cycle contributes at least one cost-one/two chain. -/
theorem hasFaceFragmentation_of_permutationMap
    {route : List Perm7} {hroute : IsHamiltonianRoute route}
    (z : RouteStructuralCounts route hroute)
    {E : Type*} [Fintype E] [DecidableEq E]
    (P Q : Equiv.Perm E)
    (hcard : Fintype.card E = 6 * z.M)
    (hP : permCycleCount P = z.M)
    (hQ : permCycleCount Q = 720 + (6 * z.m - z.r))
    (hcomponents : incidenceComponentCount P Q = z.k)
    (hproductChains : permCycleCount (P * Q) ≤ z.q) :
    z.HasFaceFragmentation := by
  obtain ⟨g, hEuler⟩ := permutationMapEulerFormula P Q
  have hkProduct := incidence_components_le_product_cycles P Q
  have hD := z.defect_le
  have hMeq := z.M_eq
  have hkeq := z.k_eq
  have hqeq := z.q_eq
  have hrm := z.r_le_six_m
  let cT := permCycleCount (P * Q)
  have hface : cT + 2 * g = z.k + z.a := by
    dsimp [cT]
    rw [hP, hQ, hcard, hcomponents] at hEuler
    omega
  have hga : 2 * g ≤ z.a := by
    dsimp [cT] at hface
    rw [hcomponents] at hkProduct
    omega
  let h := z.q - cT
  refine ⟨g, h, hga, ?_⟩
  have hcq : cT ≤ z.q := hproductChains
  dsimp [h]
  omega

/-- The structural counts land in one of the finite registry cases. -/
theorem registryCandidate_of_structuralCounts
    {route : List Perm7} {hroute : IsHamiltonianRoute route}
    (z : RouteStructuralCounts route hroute) :
    ∃ c : RegistryCandidate, c.valid ∧
      c.m = z.m ∧
      c.a = z.a ∧
      c.b = z.b ∧
      c.eta = z.eta ∧
      c.r = z.r := by
  have hD := z.defect_le
  have haR := z.a_le_r
  have hrm := z.r_le_six_m
  let c : RegistryCandidate := ⟨z.m, z.a, z.b, z.eta, z.r⟩
  have hcvalid : c.valid := by
    dsimp [RegistryCandidate.valid, c]
    refine ⟨hD, haR, hrm, ?_⟩
    intro hm0
    omega
  exact ⟨c, hcvalid, rfl, rfl, rfl, rfl, rfl⟩

end Superperm7
