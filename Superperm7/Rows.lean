/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE); this file is
additionally subject to the upstream MIT notice below.

Adapted from https://github.com/BGray-wrl/superperm6
  file:   formal-verification/Superperm6/Rows.lean
  commit: d8a932d8f61d80b0bcfc737bd0e235a8300449c4
  upstream copyright: Copyright (c) 2026 Benjamin Grayzel — MIT License (reproduced in NOTICE).
Local modifications (port from six to seven symbols; see docs/PORT_LOG.md): rows of insertion blocks of length 6 (was 5): length codes Fin 6, alpha = take 4, the full-block successor G of order 5, no six pairwise-disjoint full rows.
-/
import Superperm7.Basic

/-!
# Cyclic rows and the full-block successor (n = 7)

The definition-level finite row model.  A row is a cyclic interval of an
insertion block, given by its oriented start and its length `1 … 6`.  Its
head `alpha` is the first four symbols of the start; its tail `beta` is the
last four symbols of `R⁻¹` of its last state.  The full-block successor map
`G` rotates the first five symbols and fixes the last two; it has order five,
and it is the unique class-disjoint compatible continuation of a full row.
-/

namespace Superperm7

/-- Head/tail tuples (four symbols at `n = 7`).  The name is kept from the
`n = 6` development, whose generic surgery layer refers to it. -/
abbrev Triple := List Symbol

def alpha (p : Perm7) : Triple := (permWord p).take 4

/-- Inverse rotation, using `R^6` because `R` has order seven. -/
def Rinv (p : Perm7) : Perm7 := (R^[6]) p

structure Row where
  start : Perm7
  /-- Stored as `0`--`5`; the mathematical row length is `lengthCode + 1`. -/
  lengthCode : Fin 6
  deriving DecidableEq, Fintype

def Row.length (row : Row) : ℕ := row.lengthCode.val + 1

def Row.lastState (row : Row) : Perm7 :=
  (F^[row.lengthCode.val]) row.start

def Row.beta (row : Row) : Triple :=
  (permWord (Rinv row.lastState)).drop 3

def Row.block (row : Row) : Finset Perm7 := fBlock row.start

def Row.classMask (row : Row) : Finset (Finset Perm7) :=
  ((Finset.range row.length).image fun i => rClass ((F^[i]) row.start))

theorem oriented_row_count : Fintype.card Row = 30240 := by
  native_decide

def rowOfLength (p : Perm7) (length : Fin 6) : Row := ⟨p, length⟩

def quadAt (p : Perm7) (i j k l : Fin 7) : Triple := [p i, p j, p k, p l]

/-- The complete endpoint table.  Codes `0`--`5` represent lengths `1`--`6`:
`abcd → cdef, defa, efab, fabc, abcd, bcde`. -/
theorem row_endpoint_table : ∀ p : Perm7,
    (rowOfLength p 0).beta = quadAt p 2 3 4 5 ∧
    (rowOfLength p 1).beta = quadAt p 3 4 5 0 ∧
    (rowOfLength p 2).beta = quadAt p 4 5 0 1 ∧
    (rowOfLength p 3).beta = quadAt p 5 0 1 2 ∧
    (rowOfLength p 4).beta = quadAt p 0 1 2 3 ∧
    (rowOfLength p 5).beta = quadAt p 1 2 3 4 := by
  native_decide

theorem length_five_row_is_loop : ∀ p : Perm7,
    (rowOfLength p 4).beta = alpha p := by
  native_decide

def fullRow (p : Perm7) : Row := rowOfLength p 5

def fullClassMask (p : Perm7) : Finset (Finset Perm7) :=
  (fBlock p).image rClass

def FullCompatibleDisjoint (p q : Perm7) : Prop :=
  (fullRow p).beta = alpha q ∧ Disjoint (fullClassMask p) (fullClassMask q)

instance (p q : Perm7) : Decidable (FullCompatibleDisjoint p q) :=
  inferInstanceAs (Decidable
    ((fullRow p).beta = alpha q ∧ Disjoint (fullClassMask p) (fullClassMask q)))

private def gIndexFn : Symbol → Symbol
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 2
  | ⟨2, _⟩ => 3
  | ⟨3, _⟩ => 4
  | ⟨4, _⟩ => 0
  | ⟨5, _⟩ => 5
  | ⟨_, _⟩ => 6

private def gIndexInvFn : Symbol → Symbol
  | ⟨0, _⟩ => 4
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 2
  | ⟨4, _⟩ => 3
  | ⟨5, _⟩ => 5
  | ⟨_, _⟩ => 6

def gIndex : Equiv.Perm Symbol where
  toFun := gIndexFn
  invFun := gIndexInvFn
  left_inv := by decide
  right_inv := by decide

/-- `G(a,b,c,d,e,y,z) = (b,c,d,e,a,y,z)`. -/
def G (p : Perm7) : Perm7 := gIndex.trans p

theorem fullRow_beta_eq_alpha_G : ∀ p : Perm7, (fullRow p).beta = alpha (G p) := by
  native_decide

theorem fullCompatibleDisjoint_G : ∀ p : Perm7, FullCompatibleDisjoint p (G p) := by
  native_decide

/-- Position permutations fixing the first four positions. -/
def tailStabilizer : Finset (Equiv.Perm Symbol) :=
  Finset.univ.filter fun σ => ∀ i : Symbol, i.val < 4 → σ i = i

theorem tailStabilizer_card : tailStabilizer.card = 6 := by native_decide

/-- Among the six starts sharing the head of `G p`, only `G p` itself is
class-disjoint from the block of `p`. -/
theorem fullDisjoint_tail_unique : ∀ p : Perm7, ∀ σ ∈ tailStabilizer,
    Disjoint (fullClassMask p) (fullClassMask (σ.trans (G p))) → σ = 1 := by
  native_decide

theorem alpha_eq_iff_agree_four (q q' : Perm7) :
    alpha q = alpha q' ↔ ∀ i : Fin 7, i.val < 4 → q i = q' i := by
  constructor
  · intro h i hi
    have := congrArg (fun l => l[i.val]?) h
    simp only [alpha, List.getElem?_take, if_pos hi, permWord_getElem? q i.val i.isLt,
      permWord_getElem? q' i.val i.isLt, Option.some.injEq] at this
    exact this
  · intro h
    apply List.ext_getElem?
    intro i
    simp only [alpha, List.getElem?_take]
    by_cases hi : i < 4
    · rw [if_pos hi, if_pos hi, permWord_getElem? q i (by omega), permWord_getElem? q' i (by omega),
        h ⟨i, by omega⟩ hi]
    · rw [if_neg hi, if_neg hi]

/-- The full-block successor lemma, including uniqueness among all 5040
possible next starts. -/
theorem full_block_successor (p q : Perm7) :
    FullCompatibleDisjoint p q ↔ q = G p := by
  constructor
  · rintro ⟨hcompat, hdisj⟩
    rw [fullRow_beta_eq_alpha_G] at hcompat
    have hagree := (alpha_eq_iff_agree_four (G p) q).mp hcompat
    let σ : Equiv.Perm Symbol := q.trans (G p).symm
    have hq : q = σ.trans (G p) := by
      apply Equiv.ext; intro i; simp [σ]
    have hσ : σ ∈ tailStabilizer := by
      simp only [tailStabilizer, Finset.mem_filter, Finset.mem_univ, true_and]
      intro i hi
      simp only [σ, Equiv.trans_apply]
      rw [← hagree i hi]
      simp
    rw [hq] at hdisj
    have := fullDisjoint_tail_unique p σ hσ hdisj
    rw [hq, this]
    rfl
  · rintro rfl
    exact fullCompatibleDisjoint_G p

theorem G_order_five : ∀ p : Perm7, (G^[5]) p = p := by
  native_decide

theorem first_five_G_images_distinct (p : Perm7) :
    ((Finset.range 5).image fun i => (G^[i]) p).card = 5 := by
  native_decide +revert

theorem fullClassMask_nonempty (p : Perm7) : (fullClassMask p).Nonempty := by
  refine ⟨rClass p, ?_⟩
  simp only [fullClassMask, Finset.mem_image]
  refine ⟨p, ?_, rfl⟩
  simp only [fBlock, finiteOrbit, Finset.mem_image, Finset.mem_range]
  exact ⟨0, by omega, rfl⟩

/-- A class-disjoint compatible segment cannot contain six full rows.  This
is the analytic pruning rule (P1), derived from the successor theorem and
`G^5 = id`. -/
theorem no_six_pairwise_disjoint_full_rows
    (p0 p1 p2 p3 p4 p5 : Perm7)
    (h01 : FullCompatibleDisjoint p0 p1)
    (h12 : FullCompatibleDisjoint p1 p2)
    (h23 : FullCompatibleDisjoint p2 p3)
    (h34 : FullCompatibleDisjoint p3 p4)
    (h45 : FullCompatibleDisjoint p4 p5)
    (h05 : Disjoint (fullClassMask p0) (fullClassMask p5)) : False := by
  have e01 : p1 = G p0 := (full_block_successor p0 p1).mp h01
  have e12 : p2 = G p1 := (full_block_successor p1 p2).mp h12
  have e23 : p3 = G p2 := (full_block_successor p2 p3).mp h23
  have e34 : p4 = G p3 := (full_block_successor p3 p4).mp h34
  have e45 : p5 = G p4 := (full_block_successor p4 p5).mp h45
  have ep5 : p5 = p0 := by
    rw [e45, e34, e23, e12, e01]
    simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using
      (G_order_five p0)
  rw [ep5] at h05
  obtain ⟨c, hc⟩ := fullClassMask_nonempty p0
  exact (Finset.disjoint_left.mp h05) hc hc

end Superperm7
