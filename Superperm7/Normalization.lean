/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE); this file is
additionally subject to the upstream MIT notice below.

Adapted from https://github.com/BGray-wrl/superperm6
  file:   formal-verification/Superperm6/Normalization.lean
  commit: d8a932d8f61d80b0bcfc737bd0e235a8300449c4
  upstream copyright: Copyright (c) 2026 Benjamin Grayzel — MIT License (reproduced in NOTICE).
Local modifications (port from six to seven symbols; see docs/PORT_LOG.md): constants for seven symbols.
-/
import Superperm7.Path

/-!
# Normalizing a Hamilton route

This file formalizes Lemma 2.2 of the manuscript.  A decomposable cost-two
edge `x → R (R x)` can be replaced by the two cost-one edges through `R x`.
Removing `R x` from its old position never raises the weight, and none of its
old incident edges has cost one.  Repeating the exchange terminates because
the number of cost-one edges strictly increases.
-/

namespace Superperm7

/-- Number of cost-one edges in a route. -/
def costOneCount : List Perm7 → ℕ
  | p :: q :: rest => (if d p q = 1 then 1 else 0) + costOneCount (q :: rest)
  | _ => 0

/-- A normalized route contains no decomposable cost-two edge. -/
def IsNormalizedRoute (route : List Perm7) : Prop :=
  route.IsChain fun p q => q ≠ R (R p)

instance (route : List Perm7) : Decidable (IsNormalizedRoute route) :=
  inferInstanceAs (Decidable (route.IsChain fun p q => q ≠ R (R p)))

theorem R_injective : Function.Injective R := by
  intro p q hpq
  apply Equiv.ext
  intro i
  have hi := Equiv.congr_fun hpq (rotIndex.symm i)
  simpa [R] using hi

private theorem infix_pair_right_unique {route : List Perm7} {x y z : Perm7}
    (hnodup : route.Nodup)
    (hxy : [x, y] <:+: route) (hxz : [x, z] <:+: route) : y = z := by
  rw [List.infix_iff_getElem?] at hxy hxz
  obtain ⟨i, hi, hixy⟩ := hxy
  obtain ⟨j, hj, hjxz⟩ := hxz
  have hix := hixy 0 (by simp)
  have hjx := hjxz 0 (by simp)
  have hiy := hixy 1 (by simp)
  have hjz := hjxz 1 (by simp)
  simp at hix hiy hjx hjz
  obtain ⟨hii, hix'⟩ := List.getElem?_eq_some_iff.mp hix
  obtain ⟨hjj, hjx'⟩ := List.getElem?_eq_some_iff.mp hjx
  have hij : i = j := hnodup.getElem_inj_iff.mp (hix'.trans hjx'.symm)
  subst j
  exact Option.some.inj (hiy.symm.trans hjz)

private theorem infix_pair_left_unique {route : List Perm7} {x y z : Perm7}
    (hnodup : route.Nodup)
    (hxy : [x, z] <:+: route) (hzy : [y, z] <:+: route) : x = y := by
  rw [List.infix_iff_getElem?] at hxy hzy
  obtain ⟨i, hi, hixz⟩ := hxy
  obtain ⟨j, hj, hjyz⟩ := hzy
  have hix := hixz 0 (by simp)
  have hjy := hjyz 0 (by simp)
  have hiz := hixz 1 (by simp)
  have hjz := hjyz 1 (by simp)
  simp at hix hjy hiz hjz
  obtain ⟨hii, hiz'⟩ := List.getElem?_eq_some_iff.mp hiz
  obtain ⟨hjj, hjz'⟩ := List.getElem?_eq_some_iff.mp hjz
  have heq : route[i + 1] = route[j + 1] := by
    simpa [Nat.add_comm] using hiz'.trans hjz'.symm
  have hij : i + 1 = j + 1 := hnodup.getElem_inj_iff.mp heq
  have : i = j := by omega
  subst j
  exact Option.some.inj (hix.symm.trans hjy)

/-- Removing a vertex from a route does not increase its weight.  Endpoint
deletions are included; an interior deletion uses the directed triangle
inequality. -/
theorem routeWeight_erase_le (u : Perm7) : ∀ route : List Perm7,
    routeWeight (route.erase u) ≤ routeWeight route
  | [] => by simp [routeWeight]
  | [a] => by
      by_cases h : a = u <;> simp [h, routeWeight]
  | a :: b :: rest => by
      by_cases hau : a = u
      · subst a
        simp [routeWeight]
      · by_cases hbu : b = u
        · subst b
          cases rest with
          | nil => simp [routeWeight, hau]
          | cons c cs =>
              have htri := d_triangle a u c
              rw [List.erase_cons_tail (not_beq_of_ne hau), List.erase_cons_head]
              simp only [routeWeight]
              omega
        · have ih := routeWeight_erase_le u (b :: rest)
          have ih' : routeWeight (b :: rest.erase u) ≤ routeWeight (b :: rest) := by
            simpa only [List.erase_cons_tail (not_beq_of_ne hbu)] using ih
          rw [List.erase_cons_tail (not_beq_of_ne hau),
            List.erase_cons_tail (not_beq_of_ne hbu)]
          simp only [routeWeight]
          omega

/-- Every edge incident with `u` is known not to have cost one. -/
def NoCostOneIncident (route : List Perm7) (u : Perm7) : Prop :=
  route.IsChain fun a b => (a = u ∨ b = u) → d a b ≠ 1

/-- Under the incident-edge hypothesis, deleting `u` cannot remove a
cost-one edge.  The shortcut may create one. -/
theorem costOneCount_le_erase {u : Perm7} : ∀ {route : List Perm7},
    NoCostOneIncident route u →
    costOneCount route ≤ costOneCount (route.erase u)
  | [], _ => by simp [costOneCount]
  | [a], _ => by simp [costOneCount]
  | a :: b :: rest, hno => by
      have hab := hno.rel_head
      have htail : NoCostOneIncident (b :: rest) u := hno.tail
      by_cases hau : a = u
      · subst a
        have hnot : d u b ≠ 1 := hab (Or.inl rfl)
        simp [costOneCount, hnot]
      · by_cases hbu : b = u
        · subst b
          have hau' : d a u ≠ 1 := hab (Or.inr rfl)
          cases rest with
          | nil => simp [costOneCount, hau, hau']
          | cons c cs =>
              have huc := htail.rel_head (Or.inl rfl)
              rw [List.erase_cons_tail (not_beq_of_ne hau), List.erase_cons_head]
              simp [costOneCount, hau', huc]
        · have ih := costOneCount_le_erase htail
          have ih' : costOneCount (b :: rest) ≤ costOneCount (b :: rest.erase u) := by
            simpa only [List.erase_cons_tail (not_beq_of_ne hbu)] using ih
          rw [List.erase_cons_tail (not_beq_of_ne hau),
            List.erase_cons_tail (not_beq_of_ne hbu)]
          simp only [costOneCount]
          omega

theorem costOneCount_le_length : ∀ route : List Perm7,
    costOneCount route ≤ route.length
  | [] => by simp [costOneCount]
  | [p] => by simp [costOneCount]
  | p :: q :: rest => by
      have ih := costOneCount_le_length (q :: rest)
      simp only [List.length_cons] at ih
      simp only [costOneCount, List.length_cons]
      split <;> omega

private theorem bad_edge_vertices (x : Perm7) :
    let u := R x
    let y := R u
    x ≠ u ∧ u ≠ y ∧ d x u = 1 ∧ d u y = 1 ∧ d x y = 2 := by
  dsimp
  have hxuCost : d x (R x) = 1 := (cost_one_successor x (R x)).2 rfl
  have huyCost : d (R x) (R (R x)) = 1 :=
    (cost_one_successor (R x) (R (R x))).2 rfl
  have hxyCost : d x (R (R x)) = 2 :=
    (cost_two_successors x (R (R x))).2 (Or.inl rfl)
  have hxu : x ≠ R x := by
    intro h
    rw [← h] at hxuCost
    simp at hxuCost
  have huy : R x ≠ R (R x) := fun h => hxu (R_injective h)
  exact ⟨hxu, huy, hxuCost, huyCost, hxyCost⟩

private theorem noCostOneIncident_of_badEdge {route : List Perm7} {x : Perm7}
    (hnodup : route.Nodup) (hbad : [x, R (R x)] <:+: route) :
    NoCostOneIncident route (R x) := by
  rw [NoCostOneIncident, List.isChain_iff_forall_rel_of_append_cons_cons]
  intro a b pre post hedge hab hcost
  have habEdge : [a, b] <:+: route := by
    refine ⟨pre, post, ?_⟩
    simpa [List.append_assoc] using hedge.symm
  rcases hab with hau | hbu
  · subst a
    have hb : b = R (R x) := (cost_one_successor (R x) b).mp hcost
    subst b
    have := infix_pair_left_unique hnodup hbad habEdge
    exact (bad_edge_vertices x).1 this
  · subst b
    have hu : R x = R a := (cost_one_successor a (R x)).mp hcost
    have ha : a = x := R_injective hu.symm
    subst a
    have := infix_pair_right_unique hnodup hbad habEdge
    exact (bad_edge_vertices x).2.1 this.symm

private theorem infix_pair_erase {route : List Perm7} {x y u : Perm7}
    (hux : u ≠ x) (huy : u ≠ y) (hxy : [x, y] <:+: route) :
    [x, y] <:+: route.erase u := by
  rcases hxy with ⟨pre, post, hroute⟩
  rw [← hroute]
  by_cases hu : u ∈ pre
  · rw [List.append_assoc, List.erase_append_left _ hu]
    refine ⟨pre.erase u, post, ?_⟩
    simp [List.append_assoc]
  · have hnot : u ∉ pre ++ [x, y] := by simpa [hux, huy, hu]
    rw [List.erase_append_right post hnot]
    exact ⟨pre, post.erase u, rfl⟩

private theorem routeWeight_insert_between (pre post : List Perm7)
    (x u y : Perm7) (hweight : d x y = d x u + d u y) :
    routeWeight (pre ++ x :: u :: y :: post) =
      routeWeight (pre ++ x :: y :: post) := by
  induction pre with
  | nil => simp [routeWeight]; omega
  | cons a pre ih =>
      cases pre with
      | nil => simp [routeWeight]; omega
      | cons b rest =>
          simpa only [List.cons_append, routeWeight] using
            congrArg (fun n => d a b + n) ih

private theorem costOneCount_insert_between (pre post : List Perm7)
    (x u y : Perm7) (hxu : d x u = 1) (huy : d u y = 1)
    (hxy : d x y ≠ 1) :
    costOneCount (pre ++ x :: u :: y :: post) =
      costOneCount (pre ++ x :: y :: post) + 2 := by
  induction pre with
  | nil => simp [costOneCount, hxu, huy, hxy]; omega
  | cons a pre ih =>
      cases pre with
      | nil => simp [costOneCount, hxu, huy, hxy]; omega
      | cons b rest =>
          simpa only [List.cons_append, costOneCount] using
            congrArg (fun n => (if d a b = 1 then 1 else 0) + n) ih

/-- One normalization exchange. -/
theorem improve_decomposable_edge {route : List Perm7} {x : Perm7}
    (hroute : IsHamiltonianRoute route)
    (hbad : [x, R (R x)] <:+: route) :
    ∃ route' : List Perm7,
      IsHamiltonianRoute route' ∧
      routeWeight route' ≤ routeWeight route ∧
      costOneCount route < costOneCount route' ∧
      route'.length = route.length := by
  let u := R x
  let y := R u
  have hverts := bad_edge_vertices x
  have hxu : x ≠ u := hverts.1
  have huy : u ≠ y := hverts.2.1
  have hdxu : d x u = 1 := hverts.2.2.1
  have hduy : d u y = 1 := hverts.2.2.2.1
  have hdxy : d x y = 2 := hverts.2.2.2.2
  have hbad' : [x, y] <:+: route := by simpa [u, y] using hbad
  have huRoute : u ∈ route := hroute.2 u
  have huBase : u ∉ route.erase u := by
    exact List.Nodup.not_mem_erase hroute.1
  have hbaseEdge : [x, y] <:+: route.erase u :=
    infix_pair_erase hxu.symm huy hbad'
  rcases hbaseEdge with ⟨pre, post, hbase⟩
  have hbase' : pre ++ x :: y :: post = route.erase u := by
    simpa [List.append_assoc] using hbase
  let route' := pre ++ x :: u :: y :: post
  refine ⟨route', ?_, ?_, ?_, ?_⟩
  · have hpermOld : route.Perm (u :: route.erase u) := List.perm_cons_erase huRoute
    have hpermNew : route'.Perm (u :: route.erase u) := by
      have hm := @List.perm_middle Perm7 u (pre ++ [x]) (y :: post)
      rw [← hbase']
      simpa [route', List.append_assoc] using hm
    have hperm : route'.Perm route := hpermNew.trans hpermOld.symm
    exact ⟨hperm.nodup_iff.mpr hroute.1, fun p => hperm.mem_iff.mpr (hroute.2 p)⟩
  · have hdelete := routeWeight_erase_le u route
    have hinsert := routeWeight_insert_between pre post x u y (by omega)
    rw [← hbase'] at hdelete
    simpa [route'] using hinsert.le.trans hdelete
  · have hno := noCostOneIncident_of_badEdge hroute.1 hbad'
    have hdelete := costOneCount_le_erase hno
    have hinsert := costOneCount_insert_between pre post x u y hdxu hduy (by omega)
    rw [← hbase'] at hdelete
    rw [hinsert]
    simpa [route'] using (show costOneCount route <
        costOneCount (pre ++ x :: y :: post) + 2 by omega)
  · have hpermOld : route.Perm (u :: route.erase u) := List.perm_cons_erase huRoute
    have hpermNew : route'.Perm (u :: route.erase u) := by
      have hm := @List.perm_middle Perm7 u (pre ++ [x]) (y :: post)
      rw [← hbase']
      simpa [route', List.append_assoc] using hm
    exact (hpermNew.trans hpermOld.symm).length_eq

theorem not_normalized_iff_bad_edge {route : List Perm7} :
    ¬ IsNormalizedRoute route ↔ ∃ x : Perm7, [x, R (R x)] <:+: route := by
  constructor
  · intro h
    rw [IsNormalizedRoute, List.isChain_iff_forall_rel_of_append_cons_cons] at h
    push Not at h
    obtain ⟨x, y, pre, post, hroute, hy⟩ := h
    subst y
    refine ⟨x, ⟨pre, post, ?_⟩⟩
    simpa [List.append_assoc] using hroute.symm
  · rintro ⟨x, hx⟩ hnorm
    rw [IsNormalizedRoute, List.isChain_iff_forall_rel_of_append_cons_cons] at hnorm
    rcases hx with ⟨pre, post, hroute⟩
    apply hnorm
    · simpa [List.append_assoc] using hroute.symm
    · rfl

private theorem normalize_aux (n : ℕ) : ∀ route : List Perm7,
    IsHamiltonianRoute route →
    route.length - costOneCount route ≤ n →
    ∃ route' : List Perm7,
      IsHamiltonianRoute route' ∧ IsNormalizedRoute route' ∧
      routeWeight route' ≤ routeWeight route := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro route hroute hbound
      by_cases hnorm : IsNormalizedRoute route
      · exact ⟨route, hroute, hnorm, le_rfl⟩
      · obtain ⟨x, hbad⟩ := not_normalized_iff_bad_edge.mp hnorm
        obtain ⟨next, hnext, hweight, hcount, hlength⟩ :=
          improve_decomposable_edge hroute hbad
        have hcount_le := costOneCount_le_length next
        have hmeasure : next.length - costOneCount next < n := by
          omega
        obtain ⟨final, hfinal, hfinalNorm, hfinalWeight⟩ :=
          ih _ hmeasure next hnext le_rfl
        exact ⟨final, hfinal, hfinalNorm, hfinalWeight.trans hweight⟩

/-- Every Hamilton route can be normalized without increasing its weight. -/
theorem exists_normalized_route {route : List Perm7}
    (hroute : IsHamiltonianRoute route) :
    ∃ route' : List Perm7,
      IsHamiltonianRoute route' ∧ IsNormalizedRoute route' ∧
      routeWeight route' ≤ routeWeight route := by
  exact normalize_aux (route.length - costOneCount route) route hroute le_rfl

/-- A light route has a normalized light representative. -/
theorem normalized_route_of_weight_at_most {route : List Perm7} {budget : ℕ}
    (hroute : IsHamiltonianRoute route) (hweight : routeWeight route ≤ budget) :
    ∃ route' : List Perm7,
      IsHamiltonianRoute route' ∧ IsNormalizedRoute route' ∧
      routeWeight route' ≤ budget := by
  obtain ⟨route', hroute', hnorm, hle⟩ := exists_normalized_route hroute
  exact ⟨route', hroute', hnorm, hle.trans hweight⟩

end Superperm7
