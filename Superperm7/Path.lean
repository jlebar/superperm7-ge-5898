/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE); this file is
additionally subject to the upstream MIT notice below.

Adapted from https://github.com/BGray-wrl/superperm6
  file:   formal-verification/Superperm6/Path.lean
  commit: d8a932d8f61d80b0bcfc737bd0e235a8300449c4
  upstream copyright: Copyright (c) 2026 Benjamin Grayzel — MIT License (reproduced in NOTICE).
Local modifications (port from six to seven symbols; see docs/PORT_LOG.md): constants for seven symbols (word length 7, 5040 vertices).
-/
import Superperm7.Basic

/-!
# Exact Hamilton-path formulation

This file proves both directions of Lemma 2.1.  In particular, it does not
assume that a superpermutation contains each permutation only once: one
occurrence of each factor is chosen, the chosen starts are sorted, and the
overlap costs telescope.
-/

namespace Superperm7

def appendedSymbols (p q : Perm7) : Word :=
  optimalAppend (permWord p) (permWord q)

@[simp] theorem appendedSymbols_length (p q : Perm7) :
    (appendedSymbols p q).length = d p q := by
  exact optimalAppend_length (by simp)

theorem overlap_join (p q : Perm7) :
    permWord p ++ appendedSymbols p q =
      (permWord p).take (d p q) ++ permWord q := by
  have h := overlapCost_spec (permWord p) (permWord q)
  have hd : (permWord p).drop (d p q) = (permWord q).take (7 - d p q) := by
    simpa [d, OverlapCompatible] using h
  calc
    permWord p ++ appendedSymbols p q =
        ((permWord p).take (d p q) ++ (permWord p).drop (d p q)) ++
          (permWord q).drop (7 - d p q) := by
            simp only [appendedSymbols, optimalAppend, d, permWord_length]
            rw [List.take_append_drop]
    _ = (permWord p).take (d p q) ++
        ((permWord q).take (7 - d p q) ++ (permWord q).drop (7 - d p q)) := by
          simp only [List.append_assoc]
          rw [hd]
    _ = (permWord p).take (d p q) ++ permWord q := by
          rw [List.take_append_drop]

def routeTail : Perm7 → List Perm7 → Word
  | _, [] => []
  | p, q :: qs => appendedSymbols p q ++ routeTail q qs

def routeWord : List Perm7 → Word
  | [] => []
  | p :: ps => permWord p ++ routeTail p ps

def routeWeight : List Perm7 → ℕ
  | [] => 0
  | [_] => 0
  | p :: q :: qs => d p q + routeWeight (q :: qs)

theorem routeTail_length (p : Perm7) (ps : List Perm7) :
    (routeTail p ps).length = routeWeight (p :: ps) := by
  induction ps generalizing p with
  | nil => simp [routeTail, routeWeight]
  | cons q qs ih => simp [routeTail, routeWeight, ih]

theorem routeWord_length (p : Perm7) (ps : List Perm7) :
    (routeWord (p :: ps)).length = 7 + routeWeight (p :: ps) := by
  simp [routeWord, routeTail_length]

theorem routeWord_step_suffix (p q : Perm7) (qs : List Perm7) :
    routeWord (q :: qs) <:+ routeWord (p :: q :: qs) := by
  refine ⟨(permWord p).take (d p q), ?_⟩
  simp only [routeWord, routeTail]
  rw [← List.append_assoc, ← overlap_join]
  simp only [List.append_assoc]

theorem routeWord_contains {p : Perm7} {route : List Perm7} (hp : p ∈ route) :
    Occurs (routeWord route) p := by
  induction route with
  | nil => simp at hp
  | cons x xs ih =>
      rcases eq_or_ne xs [] with rfl | hxs
      · simp only [List.mem_singleton] at hp
        subst p
        simp [Occurs, routeWord, routeTail]
      · obtain ⟨y, ys, rfl⟩ := List.exists_cons_of_ne_nil hxs
        simp only [List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact List.infix_append_left
        · exact (ih (by simpa using hp)).trans (routeWord_step_suffix x y ys).isInfix

def IsHamiltonianRoute (route : List Perm7) : Prop :=
  route.Nodup ∧ ∀ p : Perm7, p ∈ route

theorem routeWord_isSuperpermutation {route : List Perm7}
    (hroute : IsHamiltonianRoute route) : IsSuperpermutation (routeWord route) := by
  intro p
  exact routeWord_contains (hroute.2 p)

theorem hamiltonian_route_nonempty {route : List Perm7}
    (hroute : IsHamiltonianRoute route) : route ≠ [] := by
  intro hnil
  have := hroute.2 (Equiv.refl Symbol)
  simp [hnil] at this

theorem word_of_hamiltonian_route {route : List Perm7}
    (hroute : IsHamiltonianRoute route) :
    ∃ w : Word, IsSuperpermutation w ∧ w.length = 7 + routeWeight route := by
  refine ⟨routeWord route, routeWord_isSuperpermutation hroute, ?_⟩
  obtain ⟨p, ps, rfl⟩ := List.exists_cons_of_ne_nil (hamiltonian_route_nonempty hroute)
  exact routeWord_length p ps

/-! ## Extracting a path from an arbitrary word -/

def OccursAt (w : Word) (p : Perm7) (i : ℕ) : Prop :=
  (w.drop i).take 7 = permWord p ∧ i + 7 ≤ w.length

theorem exists_occursAt_of_occurs {w : Word} {p : Perm7} (h : Occurs w p) :
    ∃ i, OccursAt w p i := by
  rcases h with ⟨pre, post, hword⟩
  refine ⟨pre.length, ?_, ?_⟩
  · rw [← hword]
    simp [permWord_length]
  · have hlen := congrArg List.length hword
    simp only [List.length_append, permWord_length] at hlen
    omega

theorem d_le_start_gap {w : Word} {p q : Perm7} {i j : ℕ}
    (hp : OccursAt w p i) (hq : OccursAt w q j) (hij : i ≤ j) :
    d p q ≤ j - i := by
  by_cases hlarge : 7 ≤ j - i
  · exact (d_le_seven p q).trans hlarge
  · apply overlapCost_le_of_compatible
    unfold OverlapCompatible
    simp only [permWord_length]
    rw [← hp.1, ← hq.1]
    calc
      ((w.drop i).take 7).drop (j - i) =
          ((w.drop i).drop (j - i)).take (7 - (j - i)) := List.drop_take
      _ = (w.drop j).take (7 - (j - i)) := by
          rw [List.drop_drop]
          congr 2
          omega
      _ = ((w.drop j).take 7).take (7 - (j - i)) := by
          rw [List.take_take]
          congr 2
          omega

noncomputable def chosenStart (w : Word) (h : IsSuperpermutation w) (p : Perm7) : ℕ :=
  Classical.choose (exists_occursAt_of_occurs (h p))

theorem chosenStart_spec (w : Word) (h : IsSuperpermutation w) (p : Perm7) :
    OccursAt w p (chosenStart w h p) :=
  Classical.choose_spec (exists_occursAt_of_occurs (h p))

theorem chosenStart_injective (w : Word) (h : IsSuperpermutation w) :
    Function.Injective (chosenStart w h) := by
  intro p q hpq
  apply permWord_injective
  calc
    permWord p = (w.drop (chosenStart w h p)).take 7 := (chosenStart_spec w h p).1.symm
    _ = (w.drop (chosenStart w h q)).take 7 := by rw [hpq]
    _ = permWord q := (chosenStart_spec w h q).1

theorem routeWeight_add_start_le {start : Perm7 → ℕ} {limit : ℕ}
    (edge : ∀ p q, start p ≤ start q → d p q ≤ start q - start p)
    (ends : ∀ p, start p + 7 ≤ limit)
    (p : Perm7) (ps : List Perm7)
    (hsorted : (p :: ps).Pairwise fun x y => start x ≤ start y) :
    routeWeight (p :: ps) + start p + 7 ≤ limit := by
  induction ps generalizing p with
  | nil => simpa [routeWeight] using ends p
  | cons q qs ih =>
      rw [List.pairwise_cons] at hsorted
      have hpq : start p ≤ start q := hsorted.1 q (by simp)
      have htail := ih q hsorted.2
      have hedge := edge p q hpq
      simp only [routeWeight]
      omega

theorem route_of_superpermutation (w : Word) (h : IsSuperpermutation w) :
    ∃ route : List Perm7,
      IsHamiltonianRoute route ∧ routeWeight route ≤ w.length - 7 := by
  let start := chosenStart w h
  have hstart : Function.Injective start := chosenStart_injective w h
  letI : LinearOrder Perm7 := LinearOrder.lift' start hstart
  let route := (Finset.univ : Finset Perm7).sort
  have hnodup : route.Nodup := by
    exact Finset.sort_nodup _ _
  have hall : ∀ p : Perm7, p ∈ route := by
    intro p
    simp [route]
  have hsortedOrder : route.Pairwise (fun p q => p ≤ q) := by
    exact Finset.pairwise_sort _ _
  have hsorted : route.Pairwise (fun p q => start p ≤ start q) := by
    simpa [LinearOrder.lift'] using hsortedOrder
  refine ⟨route, ⟨hnodup, hall⟩, ?_⟩
  have hrouteNonempty : route ≠ [] := by
    intro hempty
    have hmem := hall (Equiv.refl Symbol)
    rw [hempty] at hmem
    simp at hmem
  obtain ⟨p, ps, hr⟩ := List.exists_cons_of_ne_nil hrouteNonempty
  have hsorted' : (p :: ps).Pairwise (fun x y => start x ≤ start y) := by
    rw [← hr]
    exact hsorted
  have hbound := routeWeight_add_start_le
    (start := start) (limit := w.length)
    (fun x y hxy => d_le_start_gap
      (chosenStart_spec w h x) (chosenStart_spec w h y) hxy)
    (fun x => (chosenStart_spec w h x).2) p ps hsorted'
  rw [hr]
  omega

/-- A bound-by-bound form of equation (2.1).  Equality of the two minima is
an immediate corollary, while this statement avoids introducing a separate
minimum operator. -/
theorem exact_path_formulation (budget : ℕ) :
    (∃ w : Word, IsSuperpermutation w ∧ w.length ≤ 7 + budget) ↔
    (∃ route : List Perm7,
      IsHamiltonianRoute route ∧ routeWeight route ≤ budget) := by
  constructor
  · rintro ⟨w, hw, hlen⟩
    obtain ⟨route, hroute, hweight⟩ := route_of_superpermutation w hw
    exact ⟨route, hroute, by omega⟩
  · rintro ⟨route, hroute, hweight⟩
    obtain ⟨w, hw, hlen⟩ := word_of_hamiltonian_route hroute
    exact ⟨w, hw, by omega⟩

end Superperm7
