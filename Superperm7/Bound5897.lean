/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CoarsenBridge
import Superperm7.ElimD12

/-!
# A cheaper, independent bound: `s(7) ≥ 5897`

This file is **not** used by `Main.lean`.  It assembles the weaker bound `s(7) ≥ 5897` from the
same reduction layer but a different and much smaller elimination back-end: the all-marks
capacity table to charge 36 (`CapTab`, `CapCheck/*`), its superadditive closure (`Closure`) and
the defect-`≤ 12` sweep (`ElimD12`).  It builds in well under one CPU-hour and is kept as an
independent corroboration of the `D ≤ 12` range and as a quick end-to-end smoke test of the
reduction: a superpermutation of length `≤ 5896` would give a normalized Hamiltonian route of
weight `≤ 5889`, hence a realized registry candidate whose defect the exact weight/defect relation
pins to at most twelve, hence a coarsened certificate that the closure of the table excludes.
(The reduction layer itself is stated for weight `≤ 5890` / defect `≤ 13`; this file only uses
the `D ≤ 12` sub-range.)
-/

namespace Superperm7

/-- No realized registry candidate of defect at most twelve survives the
capacity elimination. -/
theorem no_realized_registry_candidate_le12 :
    ¬ ∃ (route : List Perm7) (hroute : IsHamiltonianRoute route) (c : RegistryCandidate),
      RouteRealizesRegistryCandidate route hroute c ∧ c.m + c.a + c.b + c.eta ≤ 12 := by
  rintro ⟨route, hroute, c, hreal, hdefect⟩
  have hvalid : c.valid := hreal.1
  obtain ⟨u', hu', ⟨inst⟩⟩ := coarsen_bridge hreal
  rcases hvalid with ⟨_, har, hr, _⟩
  exact no_coarsened_instance c.m c.a c.b c.eta c.r u' hdefect har hr hu' inst

theorem no_normalized_hamiltonian_route_of_weight_at_most_5889 :
    ¬ ∃ route : List Perm7,
      IsHamiltonianRoute route ∧ IsNormalizedRoute route ∧ routeWeight route ≤ 5889 := by
  rintro ⟨route, hroute, hnormal, hweight⟩
  obtain ⟨c, hc⟩ :=
    normalized_light_route_realizes_registryCandidate hroute hnormal (by omega)
  obtain ⟨_hnormal', _hw, z, hm, ha, hb, heta, _hr⟩ := hc.2
  have hD := z.defect_le_twelve_of_weight_le_5889 hweight
  exact no_realized_registry_candidate_le12 ⟨route, hroute, c, hc, by omega⟩

theorem no_hamiltonian_route_of_weight_at_most_5889 :
    ¬ ∃ route : List Perm7, IsHamiltonianRoute route ∧ routeWeight route ≤ 5889 := by
  rintro ⟨route, hroute, hweight⟩
  obtain ⟨route', hroute', hnormal', hweight'⟩ := normalized_route_of_weight_at_most hroute hweight
  exact no_normalized_hamiltonian_route_of_weight_at_most_5889 ⟨route', hroute', hnormal', hweight'⟩

/-- Every superpermutation on seven symbols has length at least `5897` (superseded by
`Superperm7.lower_bound`; independent proof). -/
theorem lower_bound_5897 : ∀ w : Word, IsSuperpermutation w → 5897 ≤ w.length := by
  intro w hw
  by_contra hshort
  have hlength : w.length ≤ 7 + 5889 := by omega
  exact no_hamiltonian_route_of_weight_at_most_5889
    ((exact_path_formulation 5889).mp ⟨w, hw, hlength⟩)

end Superperm7
