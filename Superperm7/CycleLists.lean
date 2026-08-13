/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE); this file is
additionally subject to the upstream MIT notice below.

Adapted from https://github.com/BGray-wrl/superperm6
  file:   formal-verification/Superperm6/CycleLists.lean
  commit: d8a932d8f61d80b0bcfc737bd0e235a8300449c4
  upstream copyright: Copyright (c) 2026 Benjamin Grayzel — MIT License (reproduced in NOTICE).
Local modifications (port from six to seven symbols; see docs/PORT_LOG.md): namespace and permutation type only.
-/
import Superperm7.Euler
import Mathlib.GroupTheory.Perm.Cycle.Concrete

/-!
# Concrete cycle lists for a finite permutation

This file turns the cycle type used by `permCycleCount` into an actual list
of cyclically ordered lists.  Fixed points are represented by singleton
lists; nontrivial cycles use `Equiv.Perm.toList`.
-/

namespace Superperm7

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The cyclically ordered list belonging to one cycle of `σ`. -/
noncomputable def permCycleList (σ : Equiv.Perm α)
    (C : PermCycle σ) : List α :=
  let x := permCycleRepresentative σ C
  if x ∈ σ.support then σ.toList x else [x]

theorem mem_permCycleList_iff (σ : Equiv.Perm α)
    (C : PermCycle σ) (x : α) :
    x ∈ permCycleList σ C ↔ permCycleOf σ x = C := by
  classical
  let r := permCycleRepresentative σ C
  have hrC : permCycleOf σ r = C :=
    permCycleRepresentative_spec σ C
  change x ∈ (if r ∈ σ.support then σ.toList r else [r]) ↔
    permCycleOf σ x = C
  by_cases hr : r ∈ σ.support
  · rw [if_pos hr, Equiv.Perm.mem_toList_iff]
    constructor
    · rintro ⟨hrx, _⟩
      exact (permCycleOf_eq_of_sameCycle σ hrx).symm.trans hrC
    · intro hx
      refine ⟨sameCycle_of_permCycleOf_eq σ (hrC.trans hx.symm), hr⟩
  · rw [if_neg hr, List.mem_singleton]
    constructor
    · rintro rfl
      exact hrC
    · intro hx
      have hrx : σ.SameCycle r x :=
        sameCycle_of_permCycleOf_eq σ (hrC.trans hx.symm)
      have hrfix : σ r = r := by
        simpa [Equiv.Perm.mem_support] using hr
      exact (hrx.eq_of_left hrfix).symm

theorem permCycleList_ne_nil (σ : Equiv.Perm α)
    (C : PermCycle σ) :
    permCycleList σ C ≠ [] := by
  intro hnil
  have hmem : permCycleRepresentative σ C ∈ permCycleList σ C :=
    (mem_permCycleList_iff σ C _).2
      (permCycleRepresentative_spec σ C)
  rw [hnil] at hmem
  simp at hmem

theorem permCycleList_nodup (σ : Equiv.Perm α)
    (C : PermCycle σ) :
    (permCycleList σ C).Nodup := by
  classical
  let r := permCycleRepresentative σ C
  by_cases hr : r ∈ σ.support
  · simpa [permCycleList, r, hr] using Equiv.Perm.nodup_toList σ r
  · simp [permCycleList, r, hr]

/-- Consecutive entries in a concrete cycle list are permutation steps. -/
theorem permCycleList_isChain (σ : Equiv.Perm α)
    (C : PermCycle σ) :
    (permCycleList σ C).IsChain fun x y => σ x = y := by
  classical
  let r := permCycleRepresentative σ C
  by_cases hr : r ∈ σ.support
  · simp only [permCycleList, r, hr, if_pos]
    rw [List.isChain_iff_getElem]
    intro i hi
    rw [Equiv.Perm.getElem_toList, Equiv.Perm.getElem_toList]
    rw [pow_succ', Equiv.Perm.mul_apply]
  · simp [permCycleList, r, hr]

/-- The last entry of a concrete cycle list steps back to its head. -/
theorem permCycleList_wrap (σ : Equiv.Perm α)
    (C : PermCycle σ) (hne : permCycleList σ C ≠ []) :
    σ ((permCycleList σ C).getLast hne) =
      (permCycleList σ C).head hne := by
  classical
  let r := permCycleRepresentative σ C
  by_cases hr : r ∈ σ.support
  · let l := σ.toList r
    have hl : l ≠ [] :=
      List.ne_nil_of_length_pos
        (Equiv.Perm.length_toList_pos_of_mem_support σ r hr)
    have hnext :=
      Equiv.Perm.next_toList_eq_apply σ r
        (l.getLast hl) (List.getLast_mem hl)
    have hwrap :=
      List.next_getLast_eq_head l hl (Equiv.Perm.nodup_toList σ r)
    have hresult : σ (l.getLast hl) = l.head hl :=
      hnext.symm.trans hwrap
    simpa [permCycleList, r, hr] using hresult
  · have hrfix : σ r = r := by
      simpa [Equiv.Perm.mem_support] using hr
    simpa [permCycleList, r, hr] using hrfix

/-- The cyclic successor operation on a concrete cycle list is `σ`. -/
theorem permCycleList_next_eq (σ : Equiv.Perm α)
    (C : PermCycle σ) (x : α) (hx : x ∈ permCycleList σ C) :
    (permCycleList σ C).next x hx = σ x := by
  classical
  let r := permCycleRepresentative σ C
  by_cases hr : r ∈ σ.support
  · simpa [permCycleList, r, hr] using
      Equiv.Perm.next_toList_eq_apply σ r x (by
        simpa [permCycleList, r, hr] using hx)
  · have hrfix : σ r = r := by
      simpa [Equiv.Perm.mem_support] using hr
    have hxEq : x = r := by
      simpa [permCycleList, r, hr] using hx
    subst x
    simpa [permCycleList, r, hr] using hrfix.symm

/-- One concrete list for every cycle of `σ`, including fixed points. -/
noncomputable def permCycleLists (σ : Equiv.Perm α) : List (List α) :=
  (Finset.univ : Finset (PermCycle σ)).toList.map (permCycleList σ)

theorem permCycleLists_nonempty (σ : Equiv.Perm α)
    {face : List α} (hface : face ∈ permCycleLists σ) :
    face ≠ [] := by
  rcases List.mem_map.mp hface with ⟨C, _hC, rfl⟩
  exact permCycleList_ne_nil σ C

theorem permCycleLists_complete (σ : Equiv.Perm α) (x : α) :
    x ∈ (permCycleLists σ).flatten := by
  classical
  simp only [List.mem_flatten]
  refine ⟨permCycleList σ (permCycleOf σ x), ?_,
    (mem_permCycleList_iff σ (permCycleOf σ x) x).2 rfl⟩
  simp [permCycleLists]

theorem permCycleLists_nodup (σ : Equiv.Perm α) :
    (permCycleLists σ).flatten.Nodup := by
  classical
  rw [List.nodup_flatten]
  constructor
  · intro face hface
    rcases List.mem_map.mp hface with ⟨C, _hC, rfl⟩
    exact permCycleList_nodup σ C
  · change
      (((Finset.univ : Finset (PermCycle σ)).toList.map
        (permCycleList σ)).Pairwise List.Disjoint)
    rw [List.pairwise_map]
    apply (Finset.nodup_toList
      (Finset.univ : Finset (PermCycle σ))).imp
    intro C D hCD
    rw [List.disjoint_left]
    intro x hxC hxD
    apply hCD
    exact ((mem_permCycleList_iff σ C x).1 hxC).symm.trans
      ((mem_permCycleList_iff σ D x).1 hxD)

theorem permCycleLists_partition (σ : Equiv.Perm α) (x : α) :
    (permCycleLists σ).flatten.count x = 1 :=
  List.count_eq_one_of_mem (permCycleLists_nodup σ)
    (permCycleLists_complete σ x)

theorem permCycleLists_length_eq_cycleCount (σ : Equiv.Perm α) :
    (permCycleLists σ).length = permCycleCount σ := by
  classical
  simp [permCycleLists, permCycleCount]

theorem permCycleLists_flatten_length (σ : Equiv.Perm α) :
    (permCycleLists σ).flatten.length = Fintype.card α := by
  classical
  have hset : (permCycleLists σ).flatten.toFinset =
      (Finset.univ : Finset α) := by
    ext x
    simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
    exact permCycleLists_complete σ x
  calc
    (permCycleLists σ).flatten.length =
        (permCycleLists σ).flatten.toFinset.card :=
      (List.toFinset_card_of_nodup (permCycleLists_nodup σ)).symm
    _ = (Finset.univ : Finset α).card := congrArg Finset.card hset
    _ = Fintype.card α := Finset.card_univ

theorem permCycleLists_step (σ : Equiv.Perm α)
    {face : List α} (hface : face ∈ permCycleLists σ) :
    face.IsChain fun x y => σ x = y := by
  rcases List.mem_map.mp hface with ⟨C, _hC, rfl⟩
  exact permCycleList_isChain σ C

theorem permCycleLists_wrap (σ : Equiv.Perm α)
    {face : List α} (hface : face ∈ permCycleLists σ)
    (hne : face ≠ []) :
    σ (face.getLast hne) = face.head hne := by
  rcases List.mem_map.mp hface with ⟨C, _hC, rfl⟩
  exact permCycleList_wrap σ C hne

theorem permCycleLists_next_eq (σ : Equiv.Perm α)
    {face : List α} (hface : face ∈ permCycleLists σ)
    (x : α) (hx : x ∈ face) :
    face.next x hx = σ x := by
  rcases List.mem_map.mp hface with ⟨C, _hC, rfl⟩
  exact permCycleList_next_eq σ C x hx

/-- Every rotation of a represented cycle list has the same wraparound
successor. -/
theorem permCycleLists_rotated_wrap (σ : Equiv.Perm α)
    {face arc : List α} (hface : face ∈ permCycleLists σ)
    (hrot : arc ~r face) (hne : arc ≠ []) :
    σ (arc.getLast hne) = arc.head hne := by
  let x := arc.getLast hne
  have hxArc : x ∈ arc := List.getLast_mem hne
  have hxFace : x ∈ face := hrot.mem_iff.mp hxArc
  have hArcNodup : arc.Nodup :=
    hrot.nodup_iff.mpr
      ((permCycleLists_nodup σ).sublist
        (List.infix_of_mem_flatten hface).sublist)
  calc
    σ x = face.next x hxFace :=
      (permCycleLists_next_eq σ hface x hxFace).symm
    _ = arc.next x hxArc :=
      (List.isRotated_next_eq hrot hArcNodup hxArc).symm
    _ = arc.head hne :=
      List.next_getLast_eq_head arc hne hArcNodup

/-- A represented cycle list contains every point in the same cycle as any
one of its entries. -/
theorem mem_of_mem_permCycleLists_of_sameCycle (σ : Equiv.Perm α)
    {face : List α} (hface : face ∈ permCycleLists σ)
    {x y : α} (hx : x ∈ face) (hxy : σ.SameCycle x y) :
    y ∈ face := by
  rcases List.mem_map.mp hface with ⟨C, _hC, rfl⟩
  apply (mem_permCycleList_iff σ C y).2
  exact (permCycleOf_eq_of_sameCycle σ hxy).symm.trans
    ((mem_permCycleList_iff σ C x).1 hx)

/-- Two represented cycle lists containing same-cycle elements are equal. -/
theorem permCycleLists_eq_of_sameCycle (σ : Equiv.Perm α)
    {face₁ face₂ : List α}
    (hface₁ : face₁ ∈ permCycleLists σ)
    (hface₂ : face₂ ∈ permCycleLists σ)
    {x y : α} (hx : x ∈ face₁) (hy : y ∈ face₂)
    (hxy : σ.SameCycle x y) :
    face₁ = face₂ := by
  rcases List.mem_map.mp hface₁ with ⟨C, _hC, rfl⟩
  rcases List.mem_map.mp hface₂ with ⟨D, _hD, rfl⟩
  have hxC := (mem_permCycleList_iff σ C x).1 hx
  have hyD := (mem_permCycleList_iff σ D y).1 hy
  have hCD : C = D := hxC.symm.trans
    ((permCycleOf_eq_of_sameCycle σ hxy).trans hyD)
  exact congrArg (permCycleList σ) hCD

end Superperm7
