/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE); this file is
additionally subject to the upstream MIT notice below.

Adapted from https://github.com/BGray-wrl/superperm6
  file:   formal-verification/Superperm6/CheapCover.lean
  commit: d8a932d8f61d80b0bcfc737bd0e235a8300449c4
  upstream copyright: Copyright (c) 2026 Benjamin Grayzel — MIT License (reproduced in NOTICE).
Local modifications (port from six to seven symbols; see docs/PORT_LOG.md): profile arithmetic for seven symbols: x1 = 4320 - r, x2 = 720 + r - q, weight budget 5890, loss bound; admissibility ranges.
-/
import Superperm7.Normalization

/-!
# Extracting the cheap-cover parameters from a route

This file formalizes the route-counting part of equations (2.3)--(2.5).
In particular, the bound of 4320 cost-one edges is proved from the 720
rotation classes; it is not supplied as a numerical hypothesis.
-/

namespace Superperm7

/-- Number of cost-two edges in a route. -/
def costTwoCount : List Perm7 → ℕ
  | p :: q :: rest => (if d p q = 2 then 1 else 0) + costTwoCount (q :: rest)
  | _ => 0

/-- Number of cost-three edges in a route. -/
def costThreeCount : List Perm7 → ℕ
  | p :: q :: rest => (if d p q = 3 then 1 else 0) + costThreeCount (q :: rest)
  | _ => 0

/-- Number of edges of cost at least four in a route. -/
def highCostCount : List Perm7 → ℕ
  | p :: q :: rest => (if 4 ≤ d p q then 1 else 0) + highCostCount (q :: rest)
  | _ => 0

/-- The route weight after replacing every edge cost above four by four. -/
def cappedRouteWeight : List Perm7 → ℕ
  | p :: q :: rest => min (d p q) 4 + cappedRouteWeight (q :: rest)
  | _ => 0

/-- The sources of the cost-one edges, in route order. -/
def costOneSources : List Perm7 → List Perm7
  | p :: q :: rest =>
      if d p q = 1 then p :: costOneSources (q :: rest)
      else costOneSources (q :: rest)
  | _ => []

/-- Destinations of the selected cost-one edges. -/
def costOneDestinations : List Perm7 → List Perm7
  | p :: q :: rest =>
      if d p q = 1 then q :: costOneDestinations (q :: rest)
      else costOneDestinations (q :: rest)
  | _ => []

/-- Destinations of all selected edges of cost at most two. -/
def cheapTwoDestinations : List Perm7 → List Perm7
  | p :: q :: rest =>
      if d p q ≤ 2 then q :: cheapTwoDestinations (q :: rest)
      else cheapTwoDestinations (q :: rest)
  | _ => []

@[simp] theorem costOneSources_length (route : List Perm7) :
    (costOneSources route).length = costOneCount route := by
  induction route with
  | nil => simp [costOneSources, costOneCount]
  | cons p tail ih =>
      cases tail with
      | nil => simp [costOneSources, costOneCount]
      | cons q rest =>
          simp only [costOneSources, costOneCount]
          split <;> simp_all <;> omega

theorem costOneSources_sublist (route : List Perm7) :
    List.Sublist (costOneSources route) route := by
  induction route with
  | nil => simp [costOneSources]
  | cons p tail ih =>
      cases tail with
      | nil => simp [costOneSources]
      | cons q rest =>
          simp only [costOneSources]
          split
          · exact ih.cons₂ p
          · exact ih.cons p

theorem costOneSources_nodup {route : List Perm7} (h : route.Nodup) :
    (costOneSources route).Nodup :=
  (costOneSources_sublist route).nodup h

@[simp] theorem costOneDestinations_length (route : List Perm7) :
    (costOneDestinations route).length = costOneCount route := by
  induction route with
  | nil => simp [costOneDestinations, costOneCount]
  | cons p tail ih =>
      cases tail with
      | nil => simp [costOneDestinations, costOneCount]
      | cons q rest =>
          simp only [costOneDestinations, costOneCount]
          split <;> simp_all <;> omega

theorem costOneDestinations_sublist_tail (route : List Perm7) :
    List.Sublist (costOneDestinations route) route.tail := by
  induction route with
  | nil => simp [costOneDestinations]
  | cons p tail ih =>
      cases tail with
      | nil => simp [costOneDestinations]
      | cons q rest =>
          simp only [costOneDestinations]
          split
          · exact ih.cons_cons q
          · exact ih.cons q

theorem costOneDestinations_sublist (route : List Perm7) :
    List.Sublist (costOneDestinations route) route :=
  (costOneDestinations_sublist_tail route).trans (List.tail_sublist route)

theorem costOneDestinations_nodup {route : List Perm7} (h : route.Nodup) :
    (costOneDestinations route).Nodup :=
  (costOneDestinations_sublist route).nodup h

theorem cheapTwoDestinations_sublist_tail (route : List Perm7) :
    List.Sublist (cheapTwoDestinations route) route.tail := by
  induction route with
  | nil => simp [cheapTwoDestinations]
  | cons p tail ih =>
      cases tail with
      | nil => simp [cheapTwoDestinations]
      | cons q rest =>
          simp only [cheapTwoDestinations]
          split
          · exact ih.cons_cons q
          · exact ih.cons q

theorem cheapTwoDestinations_sublist (route : List Perm7) :
    List.Sublist (cheapTwoDestinations route) route :=
  (cheapTwoDestinations_sublist_tail route).trans (List.tail_sublist route)

theorem cheapTwoDestinations_nodup {route : List Perm7} (h : route.Nodup) :
    (cheapTwoDestinations route).Nodup :=
  (cheapTwoDestinations_sublist route).nodup h

theorem cheapTwoDestinations_length {route : List Perm7}
    (hnodup : route.Nodup) :
    (cheapTwoDestinations route).length =
      costOneCount route + costTwoCount route := by
  induction route with
  | nil => simp [cheapTwoDestinations, costOneCount, costTwoCount]
  | cons p tail ih =>
      cases tail with
      | nil => simp [cheapTwoDestinations, costOneCount, costTwoCount]
      | cons q rest =>
          have hpq : p ≠ q := by
            intro hpq
            subst q
            simp at hnodup
          have hpos := d_pos_of_ne hpq
          have hi := ih hnodup.tail
          simp only [cheapTwoDestinations, costOneCount, costTwoCount]
          by_cases hle : d p q ≤ 2 <;>
            by_cases h1 : d p q = 1 <;>
            by_cases h2 : d p q = 2 <;>
            simp [hle, h1, h2, hi] <;> omega

theorem mem_costOneDestinations_gives_edge {route : List Perm7} {u : Perm7}
    (hu : u ∈ costOneDestinations route) :
    ∃ p : Perm7, [p, u] <:+: route ∧ d p u = 1 := by
  induction route with
  | nil => simp [costOneDestinations] at hu
  | cons p tail ih =>
      cases tail with
      | nil => simp [costOneDestinations] at hu
      | cons q rest =>
          simp only [costOneDestinations] at hu
          by_cases hpq : d p q = 1
          · rw [if_pos hpq] at hu
            rcases List.mem_cons.mp hu with hqu | hu
            · subst u
              exact ⟨p, List.infix_append_left, hpq⟩
            · obtain ⟨a, ha, hd⟩ := ih hu
              exact ⟨a, List.infix_cons ha, hd⟩
          · rw [if_neg hpq] at hu
            obtain ⟨a, ha, hd⟩ := ih hu
            exact ⟨a, List.infix_cons ha, hd⟩

theorem mem_cheapTwoDestinations_gives_edge {route : List Perm7} {u : Perm7}
    (hu : u ∈ cheapTwoDestinations route) :
    ∃ p : Perm7, [p, u] <:+: route ∧ d p u ≤ 2 := by
  induction route with
  | nil => simp [cheapTwoDestinations] at hu
  | cons p tail ih =>
      cases tail with
      | nil => simp [cheapTwoDestinations] at hu
      | cons q rest =>
          simp only [cheapTwoDestinations] at hu
          by_cases hpq : d p q ≤ 2
          · rw [if_pos hpq] at hu
            rcases List.mem_cons.mp hu with hqu | hu
            · subst u
              exact ⟨p, List.infix_append_left, hpq⟩
            · obtain ⟨a, ha, hd⟩ := ih hu
              exact ⟨a, List.infix_cons ha, hd⟩
          · rw [if_neg hpq] at hu
            obtain ⟨a, ha, hd⟩ := ih hu
            exact ⟨a, List.infix_cons ha, hd⟩

private theorem mem_costOneDestinations_cons (a : Perm7)
    {route : List Perm7} {q : Perm7}
    (hq : q ∈ costOneDestinations route) :
    q ∈ costOneDestinations (a :: route) := by
  cases route with
  | nil => simp [costOneDestinations] at hq
  | cons b rest =>
      cases rest with
      | nil => simp [costOneDestinations] at hq
      | cons c tail =>
          simp only [costOneDestinations]
          split
          · exact List.mem_cons_of_mem _ hq
          · exact hq

private theorem mem_costOneDestinations_append_pair (pre post : List Perm7)
    (p q : Perm7) (hcost : d p q = 1) :
    q ∈ costOneDestinations (pre ++ p :: q :: post) := by
  induction pre with
  | nil => simp [costOneDestinations, hcost]
  | cons a pre ih =>
      simpa only [List.cons_append] using mem_costOneDestinations_cons a ih

theorem pair_infix_mem_costOneDestinations {route : List Perm7} {p q : Perm7}
    (hpair : [p, q] <:+: route) (hcost : d p q = 1) :
    q ∈ costOneDestinations route := by
  rcases hpair with ⟨pre, post, hroute⟩
  rw [← hroute]
  simpa [List.append_assoc] using
    mem_costOneDestinations_append_pair pre post p q hcost

private theorem mem_cheapTwoDestinations_cons (a : Perm7)
    {route : List Perm7} {q : Perm7}
    (hq : q ∈ cheapTwoDestinations route) :
    q ∈ cheapTwoDestinations (a :: route) := by
  cases route with
  | nil => simp [cheapTwoDestinations] at hq
  | cons b rest =>
      cases rest with
      | nil => simp [cheapTwoDestinations] at hq
      | cons c tail =>
          simp only [cheapTwoDestinations]
          split
          · exact List.mem_cons_of_mem _ hq
          · exact hq

private theorem mem_cheapTwoDestinations_append_pair (pre post : List Perm7)
    (p q : Perm7) (hcost : d p q ≤ 2) :
    q ∈ cheapTwoDestinations (pre ++ p :: q :: post) := by
  induction pre with
  | nil => simp [cheapTwoDestinations, hcost]
  | cons a pre ih =>
      simpa only [List.cons_append] using mem_cheapTwoDestinations_cons a ih

theorem pair_infix_mem_cheapTwoDestinations {route : List Perm7} {p q : Perm7}
    (hpair : [p, q] <:+: route) (hcost : d p q ≤ 2) :
    q ∈ cheapTwoDestinations route := by
  rcases hpair with ⟨pre, post, hroute⟩
  rw [← hroute]
  simpa [List.append_assoc] using
    mem_cheapTwoDestinations_append_pair pre post p q hcost

/-- Starts of the maximal cost-one runs, represented as the vertices which
are not destinations of a selected cost-one edge. -/
def runStartSet (route : List Perm7) : Finset Perm7 :=
  Finset.univ \ (costOneDestinations route).toFinset

/-- Starts of the maximal chains using costs one and two. -/
def chainStartSet (route : List Perm7) : Finset Perm7 :=
  Finset.univ \ (cheapTwoDestinations route).toFinset

theorem runStartSet_card {route : List Perm7}
    (hroute : IsHamiltonianRoute route) :
    (runStartSet route).card = 5040 - costOneCount route := by
  rw [runStartSet, Finset.card_sdiff]
  simp only [Finset.inter_univ, Finset.card_univ, card_perm7]
  rw [List.toFinset_card_of_nodup (costOneDestinations_nodup hroute.1)]
  have hlen := costOneDestinations_length route
  omega

theorem chainStartSet_card {route : List Perm7}
    (hroute : IsHamiltonianRoute route) :
    (chainStartSet route).card =
      5040 - (costOneCount route + costTwoCount route) := by
  rw [chainStartSet, Finset.card_sdiff]
  simp only [Finset.inter_univ, Finset.card_univ, card_perm7]
  rw [List.toFinset_card_of_nodup (cheapTwoDestinations_nodup hroute.1)]
  have hlen := cheapTwoDestinations_length hroute.1
  omega

theorem mem_costOneSources_gives_edge {route : List Perm7} {u : Perm7}
    (hu : u ∈ costOneSources route) : [u, R u] <:+: route := by
  induction route with
  | nil => simp [costOneSources] at hu
  | cons p tail ih =>
      cases tail with
      | nil => simp [costOneSources] at hu
      | cons q rest =>
          simp only [costOneSources] at hu
          by_cases hpq : d p q = 1
          · rw [if_pos hpq] at hu
            rcases List.mem_cons.mp hu with hpu | hu
            · subst u
              have hq : q = R p := (cost_one_successor p q).mp hpq
              subst q
              exact List.infix_append_left
            · exact List.infix_cons (ih hu)
          · rw [if_neg hpq] at hu
            exact List.infix_cons (ih hu)

theorem hamiltonian_route_length {route : List Perm7}
    (hroute : IsHamiltonianRoute route) : route.length = 5040 := by
  have huniv : route.toFinset = (Finset.univ : Finset Perm7) := by
    ext p
    simp [hroute.2 p]
  calc
    route.length = route.toFinset.card :=
      (List.toFinset_card_of_nodup hroute.1).symm
    _ = (Finset.univ : Finset Perm7).card := by rw [huniv]
    _ = 5040 := by simp [card_perm7]

/-- Every route edge has exactly one of the four capped costs. -/
theorem route_edge_count_partition {route : List Perm7}
    (hnodup : route.Nodup) :
    costOneCount route + costTwoCount route + costThreeCount route +
        highCostCount route = route.length - 1 := by
  induction route with
  | nil => simp [costOneCount, costTwoCount, costThreeCount, highCostCount]
  | cons p tail ih =>
      cases tail with
      | nil => simp [costOneCount, costTwoCount, costThreeCount, highCostCount]
      | cons q rest =>
          have hpq : p ≠ q := by
            intro hpq
            subst q
            simp at hnodup
          have hpos := d_pos_of_ne hpq
          have htail : (q :: rest).Nodup := hnodup.tail
          have hi := ih htail
          have hi' :
              costOneCount (q :: rest) + costTwoCount (q :: rest) +
                  costThreeCount (q :: rest) + highCostCount (q :: rest) =
                rest.length := by
            simpa using hi
          simp only [costOneCount, costTwoCount, costThreeCount, highCostCount,
            List.length_cons]
          by_cases h1 : d p q = 1 <;>
            by_cases h2 : d p q = 2 <;>
            by_cases h3 : d p q = 3 <;>
            by_cases h4 : 4 ≤ d p q <;>
            simp [h1, h2, h3, h4, hi'] <;> omega

theorem cappedRouteWeight_le (route : List Perm7) :
    cappedRouteWeight route ≤ routeWeight route := by
  induction route with
  | nil => simp [cappedRouteWeight, routeWeight]
  | cons p tail ih =>
      cases tail with
      | nil => simp [cappedRouteWeight, routeWeight]
      | cons q rest =>
          simp only [cappedRouteWeight, routeWeight]
          have hmin : min (d p q) 4 ≤ d p q := min_le_left _ _
          omega

/-- Capped weight expressed by its edge counts. -/
theorem cappedRouteWeight_eq_counts {route : List Perm7}
    (hnodup : route.Nodup) :
    cappedRouteWeight route =
      costOneCount route + 2 * costTwoCount route +
        3 * costThreeCount route + 4 * highCostCount route := by
  induction route with
  | nil => simp [cappedRouteWeight, costOneCount, costTwoCount,
      costThreeCount, highCostCount]
  | cons p tail ih =>
      cases tail with
      | nil => simp [cappedRouteWeight, costOneCount, costTwoCount,
          costThreeCount, highCostCount]
      | cons q rest =>
          have hpq : p ≠ q := by
            intro hpq
            subst q
            simp at hnodup
          have hpos := d_pos_of_ne hpq
          have hi := ih hnodup.tail
          simp only [cappedRouteWeight, costOneCount, costTwoCount,
            costThreeCount, highCostCount]
          by_cases h1 : d p q = 1 <;>
            by_cases h2 : d p q = 2 <;>
            by_cases h3 : d p q = 3 <;>
            by_cases h4 : 4 ≤ d p q <;>
            simp [h1, h2, h3, h4, hi] <;> omega

/-- In a normalized route, every retained cost-two edge is the
nondecomposable successor `N₂`. -/
theorem normalized_cost_two_successor {route : List Perm7}
    (hnormal : IsNormalizedRoute route) :
    route.IsChain fun p q => d p q = 2 → q = N₂ p := by
  exact hnormal.imp fun {p q} hnot hcost =>
    (cost_two_successors p q).mp hcost |>.resolve_left hnot

/-! ## The 720 missed rotation edges -/

theorem mem_rClass_iff (p q : Perm7) :
    q ∈ rClass p ↔ ∃ i : Fin 7, q = (R^[i.val]) p := by
  simp only [rClass, finiteOrbit, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.val, i.isLt, rfl⟩

theorem rClass_R_iterate : ∀ p : Perm7, ∀ i : Fin 7,
    rClass ((R^[i.val]) p) = rClass p := by
  native_decide

theorem R_R_iterate_mem_rClass : ∀ p : Perm7, ∀ i : Fin 7,
    R ((R^[i.val]) p) ∈ rClass p := by
  native_decide

/-- Rotation classes really form a partition: membership determines the
class.  This is a small finite fact about the explicit rotation map. -/
theorem rClass_eq_of_mem : ∀ p q : Perm7,
    q ∈ rClass p → rClass q = rClass p := by
  intro p q hq
  obtain ⟨i, rfl⟩ := (mem_rClass_iff p q).mp hq
  exact rClass_R_iterate p i

theorem R_mem_rClass_of_mem : ∀ p q : Perm7,
    q ∈ rClass p → R q ∈ rClass p := by
  intro p q hq
  obtain ⟨i, rfl⟩ := (mem_rClass_iff p q).mp hq
  exact R_R_iterate_mem_rClass p i

abbrev RotationClass := ↥allRClasses

private theorem rotationClass_nonempty (C : RotationClass) : C.1.Nonempty := by
  rcases Finset.mem_image.mp C.2 with ⟨p, _hp, hC⟩
  rw [← hC]
  apply Finset.card_pos.mp
  rw [rClass_card]
  omega

/-- The member of a rotation class occurring last in a Hamilton route. -/
noncomputable def lastInRotationClass (route : List Perm7)
    (C : RotationClass) : Perm7 :=
  Classical.choose (Finset.exists_max_image C.1 (fun p => route.idxOf p)
    (rotationClass_nonempty C))

theorem lastInRotationClass_mem (route : List Perm7)
    (C : RotationClass) : lastInRotationClass route C ∈ C.1 :=
  (Classical.choose_spec (Finset.exists_max_image C.1 (fun p => route.idxOf p)
    (rotationClass_nonempty C))).1

theorem idxOf_le_lastInRotationClass (route : List Perm7)
    (C : RotationClass) {p : Perm7} (hp : p ∈ C.1) :
    route.idxOf p ≤ route.idxOf (lastInRotationClass route C) :=
  (Classical.choose_spec (Finset.exists_max_image C.1 (fun p => route.idxOf p)
    (rotationClass_nonempty C))).2 p hp

theorem idxOf_succ_of_pair_infix {route : List Perm7} {x y : Perm7}
    (hnodup : route.Nodup) (hx : x ∈ route) (hy : y ∈ route)
    (hxy : [x, y] <:+: route) :
    route.idxOf y = route.idxOf x + 1 := by
  rw [List.infix_iff_getElem?] at hxy
  obtain ⟨i, hi, hpair⟩ := hxy
  have hix := hpair 0 (by simp)
  have hiy := hpair 1 (by simp)
  simp at hix hiy
  obtain ⟨hibound, hix'⟩ := List.getElem?_eq_some_iff.mp hix
  obtain ⟨hisbound, hiy'⟩ := List.getElem?_eq_some_iff.mp hiy
  have hxbound : route.idxOf x < route.length :=
    List.idxOf_lt_length_iff.mpr hx
  have hybound : route.idxOf y < route.length :=
    List.idxOf_lt_length_iff.mpr hy
  have hxget := List.getElem_idxOf hxbound
  have hyget := List.getElem_idxOf hybound
  have hxi : route.idxOf x = i :=
    hnodup.getElem_inj_iff.mp (hxget.trans hix'.symm)
  have hyi : route.idxOf y = i + 1 :=
    hnodup.getElem_inj_iff.mp (hyget.trans (by simpa [Nat.add_comm] using hiy'.symm))
  omega

theorem last_rotation_edge_absent {route : List Perm7}
    (hroute : IsHamiltonianRoute route) (C : RotationClass) :
    lastInRotationClass route C ∉ costOneSources route := by
  intro hsource
  let u := lastInRotationClass route C
  have huC : u ∈ C.1 := lastInRotationClass_mem route C
  have hRuC : R u ∈ C.1 := by
    rcases Finset.mem_image.mp C.2 with ⟨p, _hp, hpC⟩
    rw [← hpC] at huC ⊢
    exact R_mem_rClass_of_mem p u huC
  have hpair : [u, R u] <:+: route := mem_costOneSources_gives_edge hsource
  have hsucc := idxOf_succ_of_pair_infix hroute.1 (hroute.2 u)
    (hroute.2 (R u)) hpair
  have hmax := idxOf_le_lastInRotationClass route C hRuC
  dsimp [u] at hsucc hmax
  omega

private theorem lastInRotationClass_injective (route : List Perm7) :
    Function.Injective (lastInRotationClass route) := by
  intro C D hCD
  apply Subtype.ext
  have huC := lastInRotationClass_mem route C
  have huD := lastInRotationClass_mem route D
  rcases Finset.mem_image.mp C.2 with ⟨p, _hp, hpC⟩
  rcases Finset.mem_image.mp D.2 with ⟨q, _hq, hqD⟩
  have huCp : lastInRotationClass route C ∈ rClass p := by
    rwa [hpC]
  have huDq : lastInRotationClass route D ∈ rClass q := by
    rwa [hqD]
  have hclassC : rClass (lastInRotationClass route C) = C.1 :=
    (rClass_eq_of_mem p _ huCp).trans hpC
  have hclassD : rClass (lastInRotationClass route D) = D.1 :=
    (rClass_eq_of_mem q _ huDq).trans hqD
  calc
    C.1 = rClass (lastInRotationClass route C) := hclassC.symm
    _ = rClass (lastInRotationClass route D) := congrArg rClass hCD
    _ = D.1 := hclassD

/-- A Hamilton route uses at most six cost-one edges from each of the 720
directed rotation cycles, hence at most 4320 in total. -/
theorem costOneCount_le_4320 {route : List Perm7}
    (hroute : IsHamiltonianRoute route) : costOneCount route ≤ 4320 := by
  let missed : Finset Perm7 :=
    Finset.univ.image (lastInRotationClass route)
  let selected : Finset Perm7 := (costOneSources route).toFinset
  have hmissedCard : missed.card = 720 := by
    calc
      missed.card = (Finset.univ : Finset RotationClass).card := by
        exact Finset.card_image_of_injective _
          (lastInRotationClass_injective route)
      _ = Fintype.card RotationClass := Finset.card_univ
      _ = allRClasses.card := Fintype.card_coe allRClasses
      _ = 720 := number_of_rClasses
  have hselectedCard : selected.card = costOneCount route := by
    simpa [selected] using List.toFinset_card_of_nodup
      (costOneSources_nodup hroute.1)
  have hdisjoint : Disjoint selected missed := by
    rw [Finset.disjoint_left]
    intro u huSelected huMissed
    simp only [selected, List.mem_toFinset] at huSelected
    simp only [missed, Finset.mem_image, Finset.mem_univ, true_and] at huMissed
    obtain ⟨C, hCu⟩ := huMissed
    rw [← hCu] at huSelected
    exact last_rotation_edge_absent hroute C huSelected
  have hunion : selected ∪ missed ⊆ (Finset.univ : Finset Perm7) := by simp
  have hcard := Finset.card_le_card hunion
  rw [Finset.card_union_of_disjoint hdisjoint, hselectedCard, hmissedCard] at hcard
  simp [card_perm7] at hcard
  omega

/-! ## Exact cheap-cover parameters -/

/-- The numerical data extracted from deleting all route edges of cost at
least four and then successively regarding cost-one, cost-two, and
cost-three edges as joins. -/
structure CheapCoverProfile where
  r : ℕ
  q : ℕ
  p : ℕ
  deriving DecidableEq

def CheapCoverProfile.loss (x : CheapCoverProfile) : ℕ :=
  720 + x.r + x.q + x.p

def CheapCoverProfile.admissible (x : CheapCoverProfile) : Prop :=
  x.r ≤ 4320 ∧ 1 ≤ x.p ∧ x.p ≤ x.q ∧ x.q ≤ 720 + x.r

/-- Equation (2.3), the capped-length identity (2.4), and all subtraction
side conditions, derived from an actual Hamilton route. -/
theorem cheap_cover_profile_of_hamiltonian_route {route : List Perm7}
    (hroute : IsHamiltonianRoute route) :
    ∃ x : CheapCoverProfile,
      x.admissible ∧
      costOneCount route = 4320 - x.r ∧
      costTwoCount route = 720 + x.r - x.q ∧
      costThreeCount route = x.q - x.p ∧
      highCostCount route = x.p - 1 ∧
      7 + cappedRouteWeight route = 5763 + x.r + x.q + x.p := by
  let x₁ := costOneCount route
  let x₂ := costTwoCount route
  let x₃ := costThreeCount route
  let x₄ := highCostCount route
  let r := 4320 - x₁
  let p := x₄ + 1
  let q := x₃ + p
  let x : CheapCoverProfile := ⟨r, q, p⟩
  have hlen : route.length = 5040 := hamiltonian_route_length hroute
  have hpart := route_edge_count_partition hroute.1
  have hx₁ : x₁ ≤ 4320 := costOneCount_le_4320 hroute
  have hcount : x₁ + x₂ + x₃ + x₄ = 5039 := by
    simpa [x₁, x₂, x₃, x₄, hlen] using hpart
  have hr : r ≤ 4320 := by simp [r]
  have hp1 : 1 ≤ p := by simp [p]
  have hpq : p ≤ q := by simp [q]
  have hqr : q ≤ 720 + r := by
    dsimp [q, p, r, x₁, x₂, x₃, x₄] at *
    omega
  have hx1eq : x₁ = 4320 - r := by
    dsimp [r]
    omega
  have hx2eq : x₂ = 720 + r - q := by
    dsimp [q, p, r] at *
    omega
  have hx3eq : x₃ = q - p := by
    simp [q]
  have hx4eq : x₄ = p - 1 := by
    simp [p]
  have hcap := cappedRouteWeight_eq_counts hroute.1
  refine ⟨x, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨hr, hp1, hpq, hqr⟩
  · simpa [x, x₁] using hx1eq
  · simpa [x, x₂] using hx2eq
  · simpa [x, x₃] using hx3eq
  · simpa [x, x₄] using hx4eq
  · dsimp [x]
    rw [hcap]
    dsimp [x₁, x₂, x₃, x₄] at hx1eq hx2eq hx3eq hx4eq ⊢
    omega

/-- A route of weight at most 5890 yields a genuine admissible profile of
loss at most 854.  This is the formal route-to-arithmetic boundary used by
the later frontier argument. -/
theorem cheap_cover_profile_of_weight_at_most_5890 {route : List Perm7}
    (hroute : IsHamiltonianRoute route) (hweight : routeWeight route ≤ 5890) :
    ∃ x : CheapCoverProfile,
      x.admissible ∧ x.loss ≤ 854 ∧
      costOneCount route = 4320 - x.r ∧
      costTwoCount route = 720 + x.r - x.q ∧
      costThreeCount route = x.q - x.p ∧
      highCostCount route = x.p - 1 ∧
      7 + cappedRouteWeight route = 5763 + x.r + x.q + x.p := by
  obtain ⟨x, hadm, hx1, hx2, hx3, hx4, hcap⟩ :=
    cheap_cover_profile_of_hamiltonian_route hroute
  have hcapLe := cappedRouteWeight_le route
  have hloss : x.loss ≤ 854 := by
    have hcapLe' : 7 + cappedRouteWeight route ≤ 7 + routeWeight route :=
      Nat.add_le_add_left hcapLe 7
    rw [hcap] at hcapLe'
    dsimp [CheapCoverProfile.loss]
    omega
  exact ⟨x, hadm, hloss, hx1, hx2, hx3, hx4, hcap⟩

end Superperm7
