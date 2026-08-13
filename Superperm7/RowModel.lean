/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE); this file is
additionally subject to the upstream MIT notice below.

Adapted from https://github.com/BGray-wrl/superperm6
  file:   formal-verification/Section57Closure/ResetPhase.lean
  commit: d8a932d8f61d80b0bcfc737bd0e235a8300449c4
  upstream copyright: Copyright (c) 2026 Benjamin Grayzel — MIT License (reproduced in NOTICE).
Local modifications (port from six to seven symbols; see docs/PORT_LOG.md): only the generic half (RowCompatible / RowDisjoint / CompatibleTrail, relabelling) was kept, at seven symbols.
-/
import Superperm7.Rows

/-!
# The finite row model: compatibility, disjointness, trails, relabelling

Endpoint compatibility of consecutive rows, block/class disjointness of
distinct rows, and the simultaneous symbol relabelling under which every
model predicate is invariant.  (Generic part of the `n = 6` file
`Section57Closure/ResetPhase.lean`; the `n = 6` pruning rule P2 is dropped.)
-/

namespace Superperm7

open Superperm7

set_option maxHeartbeats 1000000

/-- Exact endpoint compatibility for two directed rows. -/
def RowCompatible (x y : Row) : Prop := x.beta = alpha y.start

instance (x y : Row) : Decidable (RowCompatible x y) := by
  unfold RowCompatible
  infer_instance

/-- The constraints shared by distinct component rows in one finite trail. -/
def RowDisjoint (x y : Row) : Prop :=
  x.block ≠ y.block ∧ Disjoint x.classMask y.classMask

instance (x y : Row) : Decidable (RowDisjoint x y) := by
  unfold RowDisjoint
  infer_instance

/-- A finite row trail has matching outer triples and globally distinct
distinguished blocks and visible rotation classes. -/
def CompatibleTrail (rows : List Row) : Prop :=
  rows.IsChain RowCompatible ∧ rows.Pairwise RowDisjoint

instance (rows : List Row) : Decidable (CompatibleTrail rows) := by
  unfold CompatibleTrail
  infer_instance

/-- Codes `0,1,2,3` are precisely the ordinary reset lengths `1,2,3,4`. -/
def resetRow (p : Perm7) (lengthCode : Fin 4) : Row :=
  rowOfLength p ⟨lengthCode.val, by omega⟩

/-! ## Simultaneous symbol relabeling -/

/-- Relabel permutation values by `σ`.  Position operations such as `F`, `R`,
and `G` commute with this action. -/
def relabelPerm (σ : Perm7) : Perm7 ≃ Perm7 where
  toFun p := p.trans σ
  invFun p := p.trans σ.symm
  left_inv p := by
    apply Equiv.ext
    intro i
    simp
  right_inv p := by
    apply Equiv.ext
    intro i
    simp

def relabelRow (σ : Perm7) (row : Row) : Row where
  start := relabelPerm σ row.start
  lengthCode := row.lengthCode

@[simp] theorem relabelPerm_apply (σ p : Perm7) (i : Symbol) :
    relabelPerm σ p i = σ (p i) := rfl

@[simp] theorem relabelPerm_F (σ p : Perm7) :
    relabelPerm σ (F p) = F (relabelPerm σ p) := by
  apply Equiv.ext
  intro i
  rfl

@[simp] theorem relabelPerm_R (σ p : Perm7) :
    relabelPerm σ (R p) = R (relabelPerm σ p) := by
  apply Equiv.ext
  intro i
  rfl

@[simp] theorem relabelPerm_G (σ p : Perm7) :
    relabelPerm σ (G p) = G (relabelPerm σ p) := by
  apply Equiv.ext
  intro i
  rfl

theorem relabelPerm_F_iterate (σ p : Perm7) : ∀ n : ℕ,
    relabelPerm σ ((F^[n]) p) = (F^[n]) (relabelPerm σ p) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        relabelPerm_F, ih]

theorem relabelPerm_R_iterate (σ p : Perm7) : ∀ n : ℕ,
    relabelPerm σ ((R^[n]) p) = (R^[n]) (relabelPerm σ p) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        relabelPerm_R, ih]

@[simp] theorem relabelPerm_self_symm (p : Perm7) :
    relabelPerm p.symm p = 1 := by
  apply Equiv.ext
  intro i
  simp

theorem permWord_relabel (σ p : Perm7) :
    permWord (relabelPerm σ p) = (permWord p).map σ := by
  apply List.ext_get
  · simp
  · intro n hn hn'
    simp [permWord]

theorem relabelPerm_Rinv (σ p : Perm7) :
    relabelPerm σ (Rinv p) = Rinv (relabelPerm σ p) := by
  exact relabelPerm_R_iterate σ p 6

@[simp] theorem relabelRow_length (σ : Perm7) (row : Row) :
    (relabelRow σ row).length = row.length := rfl

theorem relabelRow_lastState (σ : Perm7) (row : Row) :
    (relabelRow σ row).lastState = relabelPerm σ row.lastState := by
  symm
  exact relabelPerm_F_iterate σ row.start row.lengthCode.val

theorem alpha_relabel (σ p : Perm7) :
    alpha (relabelPerm σ p) = (alpha p).map σ := by
  simp [alpha, permWord_relabel]

theorem beta_relabel (σ : Perm7) (row : Row) :
    (relabelRow σ row).beta = row.beta.map σ := by
  simp only [Row.beta, relabelRow_lastState]
  rw [← relabelPerm_Rinv, permWord_relabel]
  simp

theorem RowCompatible_relabel_iff (σ : Perm7) (x y : Row) :
    RowCompatible (relabelRow σ x) (relabelRow σ y) ↔ RowCompatible x y := by
  rw [RowCompatible, beta_relabel]
  change x.beta.map σ = (alpha y.start).map σ ↔ _
  exact List.map_inj_right σ.injective

theorem fBlock_relabel (σ p : Perm7) :
    (fBlock p).map (relabelPerm σ).toEmbedding =
      fBlock (relabelPerm σ p) := by
  ext q
  simp only [Finset.mem_map, Equiv.coe_toEmbedding, fBlock, finiteOrbit,
    Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨x, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨i, hi, (relabelPerm_F_iterate σ p i).symm⟩
  · rintro ⟨i, hi, hq⟩
    refine ⟨(F^[i]) p, ⟨i, hi, rfl⟩, ?_⟩
    exact (relabelPerm_F_iterate σ p i).trans hq

theorem rClass_relabel (σ p : Perm7) :
    (rClass p).map (relabelPerm σ).toEmbedding =
      rClass (relabelPerm σ p) := by
  ext q
  simp only [Finset.mem_map, Equiv.coe_toEmbedding, rClass, finiteOrbit,
    Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨x, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨i, hi, (relabelPerm_R_iterate σ p i).symm⟩
  · rintro ⟨i, hi, hq⟩
    refine ⟨(R^[i]) p, ⟨i, hi, rfl⟩, ?_⟩
    exact (relabelPerm_R_iterate σ p i).trans hq

theorem rowBlock_relabel (σ : Perm7) (row : Row) :
    row.block.map (relabelPerm σ).toEmbedding = (relabelRow σ row).block := by
  exact fBlock_relabel σ row.start

theorem rowClassMask_relabel (σ : Perm7) (row : Row) :
    row.classMask.map
        (Finset.mapEmbedding (relabelPerm σ).toEmbedding).toEmbedding =
      (relabelRow σ row).classMask := by
  ext C
  simp only [Finset.mem_map, RelEmbedding.coe_toEmbedding,
    Finset.mapEmbedding_apply, Row.classMask, Finset.mem_image,
    Finset.mem_range]
  constructor
  · rintro ⟨D, ⟨i, hi, rfl⟩, rfl⟩
    refine ⟨i, by simpa using hi, ?_⟩
    change rClass ((F^[i]) (relabelPerm σ row.start)) =
      (rClass ((F^[i]) row.start)).map (relabelPerm σ).toEmbedding
    rw [← relabelPerm_F_iterate, ← rClass_relabel]
  · rintro ⟨i, hi, hC⟩
    refine ⟨rClass ((F^[i]) row.start), ⟨i, by simpa using hi, rfl⟩, ?_⟩
    rw [rClass_relabel, relabelPerm_F_iterate]
    exact hC

theorem RowDisjoint_relabel_iff (σ : Perm7) (x y : Row) :
    RowDisjoint (relabelRow σ x) (relabelRow σ y) ↔ RowDisjoint x y := by
  unfold RowDisjoint
  rw [← rowBlock_relabel σ x, ← rowBlock_relabel σ y,
    ← rowClassMask_relabel σ x, ← rowClassMask_relabel σ y,
    (Finset.map_injective (relabelPerm σ).toEmbedding).ne_iff,
    Finset.disjoint_map]

@[simp] theorem relabelRow_fullRow (σ p : Perm7) :
    relabelRow σ (fullRow p) = fullRow (relabelPerm σ p) := rfl

@[simp] theorem relabelRow_resetRow (σ p : Perm7) (l : Fin 4) :
    relabelRow σ (resetRow p l) = resetRow (relabelPerm σ p) l := rfl

theorem compatibleTrail_map_relabel_iff (σ : Perm7) (rows : List Row) :
    CompatibleTrail (rows.map (relabelRow σ)) ↔ CompatibleTrail rows := by
  unfold CompatibleTrail
  constructor
  · rintro ⟨hchain, hpair⟩
    refine ⟨(List.isChain_map (relabelRow σ)).mp hchain |>.imp ?_,
      (List.pairwise_map.mp hpair).imp ?_⟩
    · intro x y hxy
      exact (RowCompatible_relabel_iff σ x y).mp hxy
    · intro x y hxy
      exact (RowDisjoint_relabel_iff σ x y).mp hxy
  · rintro ⟨hchain, hpair⟩
    refine ⟨(List.isChain_map (relabelRow σ)).mpr (hchain.imp ?_),
      List.pairwise_map.mpr (hpair.imp ?_)⟩
    · intro x y hxy
      exact (RowCompatible_relabel_iff σ x y).mpr hxy
    · intro x y hxy
      exact (RowDisjoint_relabel_iff σ x y).mpr hxy

/-- The two equivalent full-row mask definitions used by `Row` and by the
pre-existing full-successor theorem agree. -/
theorem fullRow_classMask_eq_fullClassMask (p : Perm7) :
    (fullRow p).classMask = fullClassMask p := by
  native_decide +revert

theorem full_pair_of_compatibleTrail_cons
    (p q : Perm7) (tail : List Row)
    (h : CompatibleTrail (fullRow p :: fullRow q :: tail)) :
    FullCompatibleDisjoint p q := by
  rcases h with ⟨hchain, hpair⟩
  have hcompat : RowCompatible (fullRow p) (fullRow q) := by
    exact (List.isChain_cons_cons.mp hchain).1
  have hhead := (List.pairwise_cons.mp hpair).1
  have hdisjoint : RowDisjoint (fullRow p) (fullRow q) :=
    hhead (fullRow q) (by simp)
  unfold FullCompatibleDisjoint
  constructor
  · exact hcompat
  · rw [← fullRow_classMask_eq_fullClassMask,
      ← fullRow_classMask_eq_fullClassMask]
    exact hdisjoint.2

end Superperm7
