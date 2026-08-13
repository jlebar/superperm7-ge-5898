/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE); this file is
additionally subject to the upstream MIT notice below.

Adapted from https://github.com/BGray-wrl/superperm6
  file:   formal-verification/Superperm6/Coarsen.lean
  commit: d8a932d8f61d80b0bcfc737bd0e235a8300449c4
  upstream copyright: Copyright (c) 2026 Benjamin Grayzel — MIT License (reproduced in NOTICE).
Local modifications (port from six to seven symbols; see docs/PORT_LOG.md): marked rows with omitted ⊆ Fin 6, charge = (6 - length) + |omitted|; omissionRuns_le_two replaces the n = 6 run pattern lemma.
-/
import Superperm7.Rows
import Superperm7.RowModel

/-!
# The coarsened finite instance produced by the Section 5 bridge

This file defines the exact finite object that the route-side bridge
constructs for every positive-`m` registry case and that the finite
searches refute.  A `MarkedRow` is a visible row together with a set of
omitted (concealed-hole) positions; omissions are strictly interior and
form at most two contiguous runs.  A `CoarsenedInstance` is a trail system of marked rows
with global block/visible-class disjointness and the hole/gap budgets of
the manuscript's Proposition 5.5.
-/

namespace Superperm7


/-- A row with a set of omitted positions (0-indexed within the row). -/
structure MarkedRow where
  row : Row
  omitted : Finset (Fin 6)
  deriving DecidableEq

namespace MarkedRow

/-- Omitted positions must exist and be strictly interior. -/
def OmissionsInterior (x : MarkedRow) : Prop :=
  ∀ i ∈ x.omitted, 0 < i.val ∧ i.val + 1 < x.row.length

instance (x : MarkedRow) : Decidable (OmissionsInterior x) := by
  unfold OmissionsInterior; infer_instance

/-- Number of contiguous runs of omitted positions. -/
def omissionRuns (x : MarkedRow) : ℕ :=
  (x.omitted.filter fun i => ¬ ∃ j ∈ x.omitted, j.val + 1 = i.val).card

/-- The visible class mask: rotation classes of non-omitted positions. -/
def visibleMask (x : MarkedRow) : Finset (Finset Perm7) :=
  ((Finset.range x.row.length).filter
    (fun i => ∀ j ∈ x.omitted, j.val ≠ i)).image
      fun i => rClass ((F^[i]) x.row.start)

/-- Exact hole charge: retained-gap holes plus omitted positions. -/
def charge (x : MarkedRow) : ℕ := (6 - x.row.length) + x.omitted.card

/-- An ordinary (unmarked) row. -/
def ofRow (r : Row) : MarkedRow := ⟨r, ∅⟩

@[simp] theorem ofRow_visibleMask (r : Row) :
    (ofRow r).visibleMask = r.classMask := by
  simp [visibleMask, ofRow, Row.classMask]

@[simp] theorem ofRow_charge (r : Row) : (ofRow r).charge = 6 - r.length := by
  simp [charge, ofRow]

@[simp] theorem ofRow_omissionRuns (r : Row) : (ofRow r).omissionRuns = 0 := by
  simp [omissionRuns, ofRow]

theorem visibleMask_subset_classMask (x : MarkedRow) :
    x.visibleMask ⊆ x.row.classMask := by
  intro c hc
  rcases Finset.mem_image.mp hc with ⟨i, hi, rfl⟩
  exact Finset.mem_image.mpr
    ⟨i, (Finset.mem_filter.mp hi).1, rfl⟩

/-- Interior omissions in a row of length `L ≤ 6` form at most two runs
(the interior has at most four positions).  Finite check over all subsets. -/
theorem omissionRuns_le_two : ∀ (x : MarkedRow),
    x.OmissionsInterior → omissionRuns x ≤ 2 := by
  intro x
  have : ∀ s : Finset (Fin 6), ∀ L : Fin 6,
      (∀ i ∈ s, 0 < i.val ∧ i.val + 1 < L.val + 1) →
      (s.filter fun i => ¬ ∃ j ∈ s, j.val + 1 = i.val).card ≤ 2 := by
    decide
  intro hint
  have h := this x.omitted x.row.lengthCode
    (by
      intro i hi
      have := hint i hi
      simpa [Row.length] using this)
  simpa [omissionRuns, Row.length] using h

end MarkedRow

/-- Marked rows on one trail: endpoint chain on the underlying rows. -/
def MarkedCompatible (x y : MarkedRow) : Prop :=
  RowCompatible x.row y.row

instance (x y : MarkedRow) : Decidable (MarkedCompatible x y) := by
  unfold MarkedCompatible; infer_instance

/-- Global disjointness for distinct component rows: distinct distinguished
blocks and disjoint *visible* class masks. -/
def MarkedDisjoint (x y : MarkedRow) : Prop :=
  x.row.block ≠ y.row.block ∧ Disjoint x.visibleMask y.visibleMask

instance (x y : MarkedRow) : Decidable (MarkedDisjoint x y) := by
  unfold MarkedDisjoint; infer_instance

/-- The coarsened image of a cheap cover: `k` component rows on at most
`τ` compatible trails, visible charge at most `u`, at most `b` represented
omission runs.  This is the exact object refuted by the finite searches;
the bridge theorem constructs it from any realized positive-`m` registry
candidate. -/
structure CoarsenedInstance (k τ u b : ℕ) where
  trails : List (List MarkedRow)
  trail_count : trails.length ≤ τ
  row_count : trails.flatten.length = k
  compat : ∀ t ∈ trails, t.IsChain MarkedCompatible
  disjoint : trails.flatten.Pairwise MarkedDisjoint
  interior : ∀ x ∈ trails.flatten, x.OmissionsInterior
  charge_le : (trails.flatten.map MarkedRow.charge).sum ≤ u
  runs_le : (trails.flatten.map MarkedRow.omissionRuns).sum ≤ b

/-- The stronger data available when no hole is concealed off-block and no
gap is represented: exact charge and the relaxed payload condition.  Used
by the forest slices (`a = 0`): the `extra` blocks are the touched blocks
not distinguished by any row, and every rotation class invisible in the
rows meets one of them. -/
structure ForestInstance (k τ u extra : ℕ) extends
    CoarsenedInstance k τ u 0 where
  charge_eq : (trails.flatten.map MarkedRow.charge).sum = u
  unmarked : ∀ x ∈ trails.flatten, x.omitted = ∅
  payloadBlocks : Finset (Finset Perm7)
  payload_card : payloadBlocks.card = extra
  payload_blocks : payloadBlocks ⊆ allFBlocks
  payload_fresh : ∀ x ∈ trails.flatten, x.row.block ∉ payloadBlocks
  payload_cover : ∀ C ∈ allRClasses,
    (∀ x ∈ trails.flatten, C ∉ x.visibleMask) →
      ∃ B ∈ payloadBlocks, ∃ p ∈ B, rClass p = C

/-! ## Loop erasure

A loop row (length five) has equal outer tuples, so deleting it from a
compatible trail splices the trail without breaking the endpoint chain.
This is the model-level step used by the weighted-capacity compositions. -/

theorem loop_beta_eq_alpha (p : Perm7) :
    (rowOfLength p 4).beta = alpha p := length_five_row_is_loop p

/-- Filtering a chain preserves the chain condition when every dropped
element bridges its neighbours. -/
private theorem isChain_cons_filter_of_bridge {α : Type*}
    {R : α → α → Prop} {keep : α → Bool}
    (hbridge : ∀ x y z, keep y = false → R x y → R y z → R x z) :
    ∀ (l : List α) (x : α), List.IsChain R (x :: l) →
      List.IsChain R (x :: l.filter keep)
  | [], _x, _ => by simp
  | y :: l', x, h => by
      match h with
      | .cons_cons hxy hyl =>
        by_cases hy : keep y
        · rw [List.filter_cons_of_pos hy]
          exact .cons_cons hxy (isChain_cons_filter_of_bridge hbridge l' y hyl)
        · rw [List.filter_cons_of_neg (by simpa using hy)]
          match l', hyl with
          | [], _ => simp
          | z :: l'', .cons_cons hyz hzl =>
            exact isChain_cons_filter_of_bridge hbridge (z :: l'') x
              (.cons_cons (hbridge x y z (by simpa using hy) hxy hyz) hzl)

theorem isChain_filter_of_bridge {α : Type*}
    {R : α → α → Prop} {keep : α → Bool}
    (hbridge : ∀ x y z, keep y = false → R x y → R y z → R x z) :
    ∀ {l : List α}, List.IsChain R l → List.IsChain R (l.filter keep)
  | [], _ => by simp
  | x :: l, h => by
      by_cases hx : keep x
      · rw [List.filter_cons_of_pos hx]
        exact isChain_cons_filter_of_bridge hbridge l x h
      · rw [List.filter_cons_of_neg (by simpa using hx)]
        exact isChain_filter_of_bridge hbridge h.tail

/-- Removing loop rows from a marked trail preserves the endpoint chain
(no split), because a loop's entry and exit triples agree. -/
theorem chain_erase_loops (t : List MarkedRow)
    (hchain : t.IsChain MarkedCompatible) :
    (t.filter fun x => x.row.lengthCode ≠ 4).IsChain MarkedCompatible := by
  apply isChain_filter_of_bridge (hbridge := ?_) hchain
  intro x y z hy hxy hyz
  have hy3 : y.row.lengthCode = 4 := by
    by_contra hne
    simp [hne] at hy
  have hyloop : y.row.beta = alpha y.row.start := by
    have hrow : y.row = rowOfLength y.row.start 4 := by
      cases hr : y.row with
      | mk s c =>
          simp only [rowOfLength]
          congr 1
          simpa [hr] using hy3
    rw [hrow]
    exact loop_beta_eq_alpha y.row.start
  unfold MarkedCompatible RowCompatible at *
  rw [hxy, ← hyloop]
  exact hyz

end Superperm7
