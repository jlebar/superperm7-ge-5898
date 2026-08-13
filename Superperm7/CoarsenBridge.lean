/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE); this file is
additionally subject to the upstream MIT notice below.

Adapted from https://github.com/BGray-wrl/superperm6
  file:   formal-verification/Superperm6/CoarsenBridge.lean
  commit: d8a932d8f61d80b0bcfc737bd0e235a8300449c4
  upstream copyright: Copyright (c) 2026 Benjamin Grayzel — MIT License (reproduced in NOTICE).
Local modifications (port from six to seven symbols; see docs/PORT_LOG.md): bridge stated for the parametric registry: coarsen_bridge_cases / coarsen_bridge / coarsen_bridge_forest with u' <= 6m - r.
-/
import Superperm7.CoarsenAccounting

/-!
# The general Section 5 coarsening bridge

Safe cyclic surgery first contracts every materialized `T`-face.  We then
retain one contracted face in each quotient component and delete all other
face arcs, replacing deletions by trail breaks.  The retained arcs carry the
marked complementary rows from `CoarsenAux.lean`.
-/

namespace Superperm7

open List

set_option maxHeartbeats 4000000

/-- Surgery followed by one-face-per-component deletion.  This is the
route-side content of Steps 1--3 of the coarsening construction. -/
theorem retained_arc_system_of_structural_counts
    {route : List Perm7} (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (hweight : routeWeight route ≤ 5890)
    (z : RouteStructuralCounts route hroute) :
    Nonempty
      (RetainedArcSystem route hroute z.k (z.eta + 1 + z.b)) := by
  classical
  let σ : Equiv.Perm (ChainStart route) := chainFaceNext route
  let faces : List (List (ChainStart route)) := permCycleLists σ
  let trails₀ : List (List (List (ChainStart route))) :=
    (routeChainTrails route).map (List.map fun chain => [chain])

  have hfacesNonempty : ∀ face ∈ faces, face ≠ [] := by
    intro face hface
    exact permCycleLists_nonempty σ hface
  have hfacesNodup : faces.flatten.Nodup :=
    permCycleLists_nodup σ
  have hfacesFlattenLength : faces.flatten.length = z.q := by
    calc
      faces.flatten.length = Fintype.card (ChainStart route) := by
        exact permCycleLists_flatten_length σ
      _ = z.q := chains_card hroute z

  have hchainsPerm :
      List.Perm (routeChainTrails route).flatten faces.flatten := by
    have hleft : (routeChainTrails route).flatten.Nodup := by
      rw [routeChainTrails_flatten]
      exact routeChainStarts_nodup hroute
    apply (List.perm_ext_iff_of_nodup hleft hfacesNodup).2
    intro chain
    constructor
    · intro _hchain
      exact permCycleLists_complete σ chain
    · intro _hface
      rw [routeChainTrails_flatten]
      exact routeChainStarts_complete hroute chain
  have htrailsPerm :
      List.Perm trails₀.flatten
        (faces.flatten.map (fun chain => [chain])) := by
    simpa [trails₀] using hchainsPerm.map (fun chain => [chain])
  have htrailsCompat :
      ∀ trail ∈ trails₀,
        trail.IsChain
          (ArcCompatible (chainAlpha route) (chainBeta route)) := by
    intro singletonTrail hsingletonTrail
    rcases List.mem_map.mp hsingletonTrail with
      ⟨trail, htrail, rfl⟩
    rw [List.isChain_map]
    exact (chainTrails_compat hroute hnormal htrail).imp
      fun x y hxy => by
        simpa [ArcCompatible, arcStart, arcEnd] using hxy

  obtain ⟨trails', finalArcs, hfinalCompat, hfinalBudget,
      hfinalCount, hfinalPerm, hfinalFaces⟩ :=
    surgery_final (chainAlpha route) (chainBeta route)
      faces trails₀ hfacesNonempty hfacesNodup htrailsPerm htrailsCompat

  have hfinalFlattenPerm :
      List.Perm finalArcs.flatten faces.flatten := by
    apply flatten_perm_of_forall₂_perm
    exact hfinalFaces.imp fun _arc _face h => h.2.perm
  have hfinalFlattenNodup : finalArcs.flatten.Nodup :=
    hfinalFlattenPerm.nodup_iff.mpr hfacesNodup
  have hfinalArcSpec :
      ∀ {arc}, arc ∈ finalArcs →
        ∃ face, face ∈ faces ∧ arc ≠ [] ∧ arc ~r face := by
    intro arc harc
    obtain ⟨face, hface, hspec⟩ :=
      exists_right_of_forall₂_of_mem hfinalFaces harc
    exact ⟨face, hface, hspec.1, hspec.2⟩
  have hfinalArcNe : ∀ {arc}, arc ∈ finalArcs → arc ≠ [] := by
    intro arc harc
    obtain ⟨_face, _hface, harcNe, _hrot⟩ :=
      hfinalArcSpec harc
    exact harcNe
  have hfinalArcsNodup : finalArcs.Nodup :=
    nodup_of_nodup_flatten_of_ne_nil hfinalFlattenNodup
      (fun arc harc => hfinalArcNe harc)
  have htrailsFlattenNodup : trails'.flatten.Nodup :=
    hfinalPerm.nodup_iff.mpr hfinalArcsNodup

  have hfinalArcWrap :
      ∀ {arc}, arc ∈ finalArcs →
        chainFaceNext route (arcLast route hroute arc) =
          arcHead route hroute arc := by
    intro arc harc
    obtain ⟨face, hface, harcNe, hrot⟩ := hfinalArcSpec harc
    have hwrap := permCycleLists_rotated_wrap σ hface hrot harcNe
    rw [arcLast_eq_getLast hroute harcNe,
      arcHead_eq_head hroute harcNe]
    simpa [σ] using hwrap

  let FinalArc := {arc : List (ChainStart route) // arc ∈ finalArcs}
  letI : Fintype (rotationGraph route hroute).ConnectedComponent :=
    SetLike.instFintype
  let arcComponent : FinalArc →
      (rotationGraph route hroute).ConnectedComponent :=
    fun arc =>
      chainStartComponent hroute (arcHead route hroute arc.1)

  have harcComponentSurjective :
      Function.Surjective arcComponent := by
    intro K
    obtain ⟨c, hcK⟩ :=
      chainStartComponent_surjective hroute hnormal K
    have hcFlatten : c ∈ faces.flatten :=
      permCycleLists_complete σ c
    rcases List.mem_flatten.mp hcFlatten with ⟨face, hface, hcFace⟩
    obtain ⟨arc, harc, hspec⟩ :=
      exists_left_of_forall₂_of_mem hfinalFaces hface
    have harcNe : arc ≠ [] := hspec.1
    have hheadArc : arcHead route hroute arc ∈ arc := by
      rw [arcHead_eq_head hroute harcNe]
      exact List.head_mem harcNe
    have hheadFace : arcHead route hroute arc ∈ face :=
      hspec.2.mem_iff.mp hheadArc
    let a : FinalArc := ⟨arc, harc⟩
    refine ⟨a, ?_⟩
    change chainStartComponent hroute (arcHead route hroute arc) = K
    exact
      (face_members_same_component hface hheadFace hcFace hroute).trans hcK

  let representative :
      (rotationGraph route hroute).ConnectedComponent → FinalArc :=
    fun K => Classical.choose (harcComponentSurjective K)
  have hrepresentativeSpec :
      ∀ K, arcComponent (representative K) = K :=
    fun K => Classical.choose_spec (harcComponentSurjective K)
  have hrepresentativeInjective :
      Function.Injective representative := by
    intro K L hKL
    rw [← hrepresentativeSpec K, ← hrepresentativeSpec L, hKL]
  have hrepresentativeValInjective :
      Function.Injective (fun K => (representative K).1) := by
    intro K L hKL
    apply hrepresentativeInjective
    apply Subtype.ext
    exact hKL

  let retained : Finset (List (ChainStart route)) :=
    Finset.univ.image fun K :
      (rotationGraph route hroute).ConnectedComponent =>
        (representative K).1
  have hretainedMemFinal :
      ∀ {arc}, arc ∈ retained → arc ∈ finalArcs := by
    intro arc harc
    rcases Finset.mem_image.mp harc with ⟨K, _hK, hKarc⟩
    rw [← hKarc]
    exact (representative K).2
  have hretainedSubset :
      retained ⊆ finalArcs.toFinset := by
    intro arc harc
    simpa using hretainedMemFinal harc
  have hretainedCard : retained.card = z.k := by
    calc
      retained.card =
          (Finset.univ : Finset
            (rotationGraph route hroute).ConnectedComponent).card := by
        exact Finset.card_image_of_injective _
          hrepresentativeValInjective
      _ = Fintype.card
          (rotationGraph route hroute).ConnectedComponent :=
        Finset.card_univ
      _ = z.k := by
        simpa only [rotationComponentCount] using z.k_route.symm
  have hretainedComponents :
      ∀ {arc₁ arc₂},
        arc₁ ∈ retained → arc₂ ∈ retained → arc₁ ≠ arc₂ →
        chainStartComponent hroute (arcHead route hroute arc₁) ≠
          chainStartComponent hroute (arcHead route hroute arc₂) := by
    intro arc₁ arc₂ harc₁ harc₂ hne hcomponents
    rcases Finset.mem_image.mp harc₁ with ⟨K, _hK, hK⟩
    rcases Finset.mem_image.mp harc₂ with ⟨L, _hL, hL⟩
    have hKL : K = L := by
      calc
        K = arcComponent (representative K) :=
          (hrepresentativeSpec K).symm
        _ = chainStartComponent hroute
              (arcHead route hroute arc₁) := by rw [← hK]
        _ = chainStartComponent hroute
              (arcHead route hroute arc₂) := hcomponents
        _ = arcComponent (representative L) := by rw [← hL]
        _ = L := hrepresentativeSpec L
    apply hne
    rw [← hK, ← hL, hKL]

  let dead : List (ChainStart route) → Prop :=
    fun arc => arc ∉ retained
  obtain ⟨reducedTrails, hreducedCompat, hreducedFlatten,
      hreducedBudget⟩ :=
    trail_deletion
      (ArcCompatible (chainAlpha route) (chainBeta route))
      trails' hfinalCompat dead

  have hreducedMemRetained :
      ∀ {arc}, arc ∈ reducedTrails.flatten → arc ∈ retained := by
    intro arc harc
    rw [hreducedFlatten] at harc
    have hkeep := (List.mem_filter.mp harc).2
    simpa [dead] using hkeep
  have hretainedMemReduced :
      ∀ {arc}, arc ∈ retained → arc ∈ reducedTrails.flatten := by
    intro arc harc
    rw [hreducedFlatten]
    apply List.mem_filter.mpr
    constructor
    · exact hfinalPerm.mem_iff.mpr (hretainedMemFinal harc)
    · simp [dead, harc]
  have hreducedToFinset :
      reducedTrails.flatten.toFinset = retained := by
    ext arc
    simp only [List.mem_toFinset]
    exact ⟨hreducedMemRetained, hretainedMemReduced⟩
  have hreducedNodup : reducedTrails.flatten.Nodup := by
    rw [hreducedFlatten]
    exact htrailsFlattenNodup.filter _
  have hreducedLength : reducedTrails.flatten.length = z.k := by
    calc
      reducedTrails.flatten.length =
          reducedTrails.flatten.toFinset.card :=
        (List.toFinset_card_of_nodup hreducedNodup).symm
      _ = retained.card := congrArg Finset.card hreducedToFinset
      _ = z.k := hretainedCard

  have hkeepFlatten :
      reducedTrails.flatten =
        trails'.flatten.filter (fun arc => decide (arc ∈ retained)) := by
    simpa [dead] using hreducedFlatten
  have hkeepLength :
      (trails'.flatten.filter
        (fun arc => decide (arc ∈ retained))).length = z.k := by
    rw [← hkeepFlatten]
    exact hreducedLength
  have hpartition :=
    List.length_eq_length_filter_add
      (l := trails'.flatten) (fun arc => decide (arc ∈ retained))
  have hdeadLength :
      (trails'.flatten.filter
        (fun arc => decide (arc ∉ retained))).length =
          faces.length - z.k := by
    have htotal : trails'.flatten.length = faces.length := hfinalCount
    have hpartition' :
        trails'.flatten.length =
          (trails'.flatten.filter
            (fun arc => decide (arc ∈ retained))).length +
          (trails'.flatten.filter
            (fun arc => decide (arc ∉ retained))).length := by
      simpa using hpartition
    omega
  have hdeadCount :
      trails'.flatten.countP (fun arc => decide (dead arc)) =
        faces.length - z.k := by
    rw [List.countP_eq_length_filter]
    simpa [dead] using hdeadLength

  have hcLower : z.k ≤ faces.length := by
    calc
      z.k = retained.card := hretainedCard.symm
      _ ≤ finalArcs.toFinset.card :=
        Finset.card_le_card hretainedSubset
      _ = finalArcs.length :=
        List.toFinset_card_of_nodup hfinalArcsNodup
      _ = faces.length := hfinalFaces.length_eq
  have hcUpper : faces.length ≤ z.q := by
    rw [← hfacesFlattenLength]
    exact length_le_flatten_length_of_ne_nil hfacesNonempty

  obtain ⟨x, hxr, hxq, hxp, htrails₀Le⟩ :=
    cheap_profile_for_bridge hroute hnormal hweight z
  have hprofileBound :
      trails₀.length ≤ z.p := by
    have htrails₀Le' : trails₀.length ≤ x.p := by
      simpa [trails₀] using htrails₀Le
    rw [← hxp]
    exact htrails₀Le'
  have hcombinedBudget :
      reducedTrails.length ≤
        trails₀.length + (z.q - faces.length) +
          (faces.length - z.k) := by
    have hsurgery := hfinalBudget
    rw [hfacesFlattenLength] at hsurgery
    rw [hdeadCount] at hreducedBudget
    omega
  have htrailCount :
      reducedTrails.length ≤ z.eta + 1 + z.b :=
    coarsened_trail_budget_arithmetic z hcLower hcUpper
      hprofileBound hcombinedBudget

  have hreducedNonempty :
      ∀ arc ∈ reducedTrails.flatten, arc ≠ [] := by
    intro arc harc
    exact hfinalArcNe (hretainedMemFinal (hreducedMemRetained harc))
  have hreducedWrap :
      ∀ arc ∈ reducedTrails.flatten,
        chainFaceNext route (arcLast route hroute arc) =
          arcHead route hroute arc := by
    intro arc harc
    exact hfinalArcWrap
      (hretainedMemFinal (hreducedMemRetained harc))
  have hreducedComponents :
      reducedTrails.flatten.Pairwise fun arc₁ arc₂ =>
        chainStartComponent hroute (arcHead route hroute arc₁) ≠
          chainStartComponent hroute (arcHead route hroute arc₂) := by
    apply hreducedNodup.imp_of_mem
    intro arc₁ arc₂ harc₁ harc₂ hne
    exact hretainedComponents
      (hreducedMemRetained harc₁)
      (hreducedMemRetained harc₂) hne

  exact ⟨
    { trails := reducedTrails
      trail_count := htrailCount
      arc_count := hreducedLength
      compat := hreducedCompat
      nonempty := hreducedNonempty
      wrap := hreducedWrap
      component_disjoint := hreducedComponents }⟩

/-- The marked rows obtained after surgery, deletion, and endpoint
transport.  It contains all structural fields of a `CoarsenedInstance`;
only the global charge/run trichotomy remains. -/
theorem prepared_coarsening_of_structural_counts
    {route : List Perm7} (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (hweight : routeWeight route ≤ 5890)
    (z : RouteStructuralCounts route hroute) :
    Nonempty (PreparedCoarsening z.k (z.eta + 1 + z.b)) := by
  obtain ⟨arcs⟩ :=
    retained_arc_system_of_structural_counts
      hroute hnormal hweight z
  exact ⟨arcs.toPrepared hnormal⟩

/-! ## Hole accounting and the three exact outcomes -/

/-- Global accounting for the retained rows.

The preceding construction proves all local row properties and every
cardinality used here:

* `structural_touchedHole_card` gives `6m-r` total holes;
* `structural_hidden_chain_count` gives `q-k=b` hidden gaps;
* `structural_payload_block_count` gives `M-k=r-a` payload blocks.

What remains is the global injection from omission runs to hidden gaps and
the associated hidden-gap trichotomy. -/
theorem retained_arc_accounting_outcome
    {route : List Perm7} (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (z : RouteStructuralCounts route hroute)
    (sys :
      RetainedArcSystem route hroute z.k (z.eta + 1 + z.b)) :
    (sys.toPrepared hnormal).AccountingOutcome
      (6 * z.m - z.r) z.b (z.r - z.a) := by
  have hcharge :=
    retained_arc_totalCharge_le hroute hnormal z sys
  have hruns :=
    retained_arc_totalRuns_le hroute hnormal z sys
  have hpayload :=
    retained_arc_forestPayload hroute hnormal z sys
  by_cases hrunsPos :
      0 < (sys.toPrepared hnormal).totalRuns
  · exact Or.inl ⟨hcharge, hruns, hrunsPos⟩
  · have hrunsZero :
        (sys.toPrepared hnormal).totalRuns = 0 := by omega
    have hunmarked :=
      (sys.toPrepared hnormal).unmarked_of_totalRuns_eq_zero
        hrunsZero
    by_cases hchargeEq :
        (sys.toPrepared hnormal).totalCharge =
          6 * z.m - z.r
    · exact Or.inr (Or.inr
        ⟨hchargeEq, hunmarked, hpayload⟩)
    · have hbPos : 0 < z.b := by
        by_contra hbNot
        have hbZero : z.b = 0 := by omega
        apply hchargeEq
        exact retained_arc_totalCharge_eq_of_b_eq_zero
          hroute hnormal z sys hbZero
      exact Or.inr (Or.inl
        ⟨hbPos, by omega, hruns⟩)

theorem coarsen_cases_of_structural_counts
    {route : List Perm7} (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (hweight : routeWeight route ≤ 5890)
    (z : RouteStructuralCounts route hroute) :
    (∃ inst : CoarsenedInstance z.k (z.eta + 1 + z.b)
        (6 * z.m - z.r) z.b,
        1 ≤ (inst.trails.flatten.map
          MarkedRow.omissionRuns).sum) ∨
    (0 < z.b ∧
      Nonempty
        (CoarsenedInstance z.k (z.eta + 1 + z.b)
          (6 * z.m - z.r - 1) z.b)) ∨
    Nonempty
      (ForestInstance z.k (z.eta + 1 + z.b)
        (6 * z.m - z.r) (z.r - z.a)) := by
  obtain ⟨sys⟩ :=
    retained_arc_system_of_structural_counts
      hroute hnormal hweight z
  exact (sys.toPrepared hnormal).toCases
    (retained_arc_accounting_outcome hroute hnormal z sys)

/-- The exact Section-5 bridge contract: a represented omission run, a
genuine off-block hole (hence charge budget `u-1`), or the unmarked exact
forest instance with its `r-a` payload blocks. -/
theorem coarsen_bridge_cases
    {route : List Perm7} {hroute : IsHamiltonianRoute route}
    {c : RegistryCandidate} :
    RouteRealizesRegistryCandidate route hroute c →
    (∃ inst : CoarsenedInstance c.k c.tau c.u c.b,
        1 ≤ (inst.trails.flatten.map
          MarkedRow.omissionRuns).sum) ∨
    (0 < c.b ∧ Nonempty (CoarsenedInstance c.k c.tau (c.u - 1) c.b)) ∨
    Nonempty (ForestInstance c.k c.tau c.u (c.r - c.a)) := by
  rintro ⟨_hcvalid, hnormal, hweight, z,
    hcm, hca, hcb, hceta, hcr⟩
  have hcases :=
    coarsen_cases_of_structural_counts
      hroute hnormal hweight z
  have hk : z.k = c.k := by
    rw [RegistryCandidate.k, z.k_eq, hcm, hca, hcr]
  have hτ : z.eta + 1 + z.b = c.tau := by
    rw [RegistryCandidate.tau, hceta, hcb]
  have hu : 6 * z.m - z.r = c.u := by
    rw [RegistryCandidate.u, hcm, hcr]
  have hb : z.b = c.b := hcb.symm
  have hextra : z.r - z.a = c.r - c.a := by rw [hcr, hca]
  rw [hk, hτ, hu, hb, hextra] at hcases
  exact hcases

/-- The disjunction-free corollary consumed by the capacity elimination:
every realized candidate yields a coarsened instance with row count `k`,
trail budget `τ`, run budget `b`, and some charge budget `u' ≤ u`. -/
theorem coarsen_bridge
    {route : List Perm7} {hroute : IsHamiltonianRoute route}
    {c : RegistryCandidate} (h : RouteRealizesRegistryCandidate route hroute c) :
    ∃ u' : ℕ, u' ≤ c.u ∧ Nonempty (CoarsenedInstance c.k c.tau u' c.b) := by
  rcases coarsen_bridge_cases h with
    hmarked | hoffblock | hforest
  · obtain ⟨inst, _hpositive⟩ := hmarked
    exact ⟨c.u, le_rfl, ⟨inst⟩⟩
  · obtain ⟨_hbpos, ⟨inst⟩⟩ := hoffblock
    exact ⟨c.u - 1, Nat.sub_le _ _, ⟨inst⟩⟩
  · obtain ⟨forest⟩ := hforest
    exact ⟨c.u, le_rfl,
      ⟨forest.toCoarsenedInstance.mono le_rfl le_rfl (Nat.zero_le _)⟩⟩

/-- With no hidden-gap budget, the first two alternatives collapse and the
exact unmarked forest payload is forced. -/
theorem coarsen_bridge_forest
    {route : List Perm7} {hroute : IsHamiltonianRoute route}
    {c : RegistryCandidate}
    (hrealized : RouteRealizesRegistryCandidate route hroute c)
    (hb : c.b = 0) :
    Nonempty (ForestInstance c.k c.tau c.u (c.r - c.a)) := by
  rcases coarsen_bridge_cases hrealized with
    hmarked | hoffblock | hforest
  · obtain ⟨inst, hpositive⟩ := hmarked
    have hruns := inst.runs_le
    omega
  · have hbpos := hoffblock.1
    omega
  · exact hforest

end Superperm7
