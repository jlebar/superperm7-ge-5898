/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE); this file is
additionally subject to the upstream MIT notice below.

Adapted from https://github.com/BGray-wrl/superperm6
  file:   formal-verification/Superperm6/Section4.lean
  commit: d8a932d8f61d80b0bcfc737bd0e235a8300449c4
  upstream copyright: Copyright (c) 2026 Benjamin Grayzel — MIT License (reproduced in NOTICE).
Local modifications (port from six to seven symbols; see docs/PORT_LOG.md): realization predicate for the parametric registry; weight bound 5890.
-/
import Superperm7.PermutationMap
import Superperm7.Structural

/-!
# Complete route-to-registry reduction through Section 4 (n = 7)

This file supplies the route-specific hypotheses of the generic Euler
calculation using the concrete permutations constructed in
`PermutationMap.lean`, and packages the interface predicate
`RouteRealizesRegistryCandidate` consumed by the bridge and the finite
elimination.
-/

namespace Superperm7

theorem routeStructuralCounts_hasFaceFragmentation
    {route : List Perm7} (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (z : RouteStructuralCounts route hroute) :
    z.HasFaceFragmentation := by
  apply hasFaceFragmentation_of_permutationMap z
    (touchedFPerm route) (touchedAPerm route)
  · calc
      Fintype.card (TouchedState route) =
          6 * (touchedBlocks route).card := touchedState_card route
      _ = 6 * z.M := by rw [z.M_route]
  · calc
      permCycleCount (touchedFPerm route) =
          (touchedBlocks route).card := touchedFPerm_cycleCount route
      _ = z.M := z.M_route.symm
  · have hhole := touchedHole_card route
    rw [touchedState_card, ← z.M_route, z.runStart_card] at hhole
    have hhole' : Fintype.card (TouchedHole route) = 6 * z.m - z.r := by
      have hM := z.M_eq
      have hr := z.r_le_six_m
      omega
    rw [touchedAPerm_cycleCount route hroute, hhole']
  · calc
      incidenceComponentCount (touchedFPerm route) (touchedAPerm route) =
          rotationComponentCount route hroute :=
        touchedFA_incidenceComponentCount route hroute
      _ = z.k := z.k_route.symm
  · have hT := touchedTPerm_cycleCount_le_chainStartSet_card hroute hnormal
    rw [z.chainStart_card] at hT
    simpa [touchedTPerm] using hT

/-- Every normalized light Hamilton route lands in one of the registry
cases. -/
theorem normalized_light_route_gives_registryCandidate
    {route : List Perm7} (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route) (hweight : routeWeight route ≤ 5890) :
    ∃ c : RegistryCandidate, c.valid := by
  obtain ⟨z⟩ := routeStructuralCounts_of_weight_at_most_5890
    hroute hnormal hweight
  obtain ⟨c, hc, _hm, _ha, _hb, _heta, _hr⟩ :=
    registryCandidate_of_structuralCounts z
  exact ⟨c, hc⟩

/-- Exact route-level meaning of a registry case.  Keeping the route and its
structural counts in this predicate prevents the later finite eliminations
from being confused with the much weaker assertion that the arithmetic case
itself is valid. -/
def RouteRealizesRegistryCandidate (route : List Perm7)
    (hroute : IsHamiltonianRoute route) (c : RegistryCandidate) : Prop :=
  c.valid ∧ ∃ _hnormal : IsNormalizedRoute route,
    routeWeight route ≤ 5890 ∧
    ∃ z : RouteStructuralCounts route hroute,
      c.m = z.m ∧
      c.a = z.a ∧
      c.b = z.b ∧
      c.eta = z.eta ∧
      c.r = z.r

/-- A normalized light route realizes an exact, arithmetically valid
registry candidate, with all five displayed parameters identified. -/
theorem normalized_light_route_realizes_registryCandidate
    {route : List Perm7} (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route) (hweight : routeWeight route ≤ 5890) :
    ∃ c : RegistryCandidate, RouteRealizesRegistryCandidate route hroute c := by
  obtain ⟨z⟩ := routeStructuralCounts_of_weight_at_most_5890
    hroute hnormal hweight
  obtain ⟨c, hc, hm, ha, hb, heta, hr⟩ :=
    registryCandidate_of_structuralCounts z
  exact ⟨c, hc, hnormal, hweight, z, hm, ha, hb, heta, hr⟩

/-- The Euler face-fragmentation constraint also holds for every realized
candidate (documentary; the capacity elimination does not use it). -/
theorem realized_candidate_hasFaceFragmentation
    {route : List Perm7} {hroute : IsHamiltonianRoute route}
    {c : RegistryCandidate} (h : RouteRealizesRegistryCandidate route hroute c) :
    ∃ g h : ℕ, 2 * g ≤ c.a ∧ c.b + 2 * g = c.a + h := by
  obtain ⟨_hc, hnormal, _hw, z, hm, ha, hb, heta, hr⟩ := h
  obtain ⟨g, h', hg, hh⟩ := routeStructuralCounts_hasFaceFragmentation hroute hnormal z
  refine ⟨g, h', ?_, ?_⟩
  · rw [ha]; exact hg
  · rw [ha, hb]; exact hh

/-- The same reduction starting from an arbitrary (not initially
normalized) light Hamilton route. -/
theorem light_route_gives_registryCandidate
    {route : List Perm7} (hroute : IsHamiltonianRoute route)
    (hweight : routeWeight route ≤ 5890) :
    ∃ normalized : List Perm7,
      IsHamiltonianRoute normalized ∧ IsNormalizedRoute normalized ∧
      routeWeight normalized ≤ 5890 ∧
      ∃ c : RegistryCandidate, c.valid := by
  obtain ⟨normalized, hnormalized, hnormal, hnormalizedWeight⟩ :=
    normalized_route_of_weight_at_most hroute hweight
  exact ⟨normalized, hnormalized, hnormal, hnormalizedWeight,
    normalized_light_route_gives_registryCandidate
      hnormalized hnormal hnormalizedWeight⟩

end Superperm7
