/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE); this file is
additionally subject to the upstream MIT notice below.

Adapted from https://github.com/BGray-wrl/superperm6
  file:   formal-verification/Superperm6/PermutationMap.lean
  commit: d8a932d8f61d80b0bcfc737bd0e235a8300449c4
  upstream copyright: Copyright (c) 2026 Benjamin Grayzel — MIT License (reproduced in NOTICE).
Local modifications (port from six to seven symbols; see docs/PORT_LOG.md): block length 6, run-start counting with factor 6, iterate lemmas F^[5]; single-quantifier restatements.
-/
import Superperm7.FirstReturn

/-!
# The route-specific permutation map

This file constructs the touched state space, the insertion permutation
`F`, and the first-return permutation `A` used in Section 4.
-/

namespace Superperm7

theorem mem_fBlock_iff (p q : Perm7) :
    q ∈ fBlock p ↔ ∃ i : Fin 6, q = (F^[i.val]) p := by
  simp only [fBlock, finiteOrbit, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨i.val, i.isLt, rfl⟩

theorem fBlock_F_iterate_fin : ∀ p : Perm7, ∀ i : Fin 6,
    fBlock ((F^[i.val]) p) = fBlock p := by
  native_decide

theorem fBlock_eq_of_mem : ∀ p q : Perm7,
    q ∈ fBlock p → fBlock q = fBlock p := by
  intro p q hq
  obtain ⟨i, rfl⟩ := (mem_fBlock_iff p q).mp hq
  exact fBlock_F_iterate_fin p i

def IsTouched (route : List Perm7) (p : Perm7) : Prop :=
  fBlock p ∈ touchedBlocks route

instance (route : List Perm7) (p : Perm7) : Decidable (IsTouched route p) :=
  by
    unfold IsTouched
    infer_instance

abbrev TouchedState (route : List Perm7) := {p : Perm7 // IsTouched route p}

theorem fBlock_eq_touchedBlock_of_mem {route : List Perm7}
    (B : TouchedBlock route) {p : Perm7} (hp : p ∈ B.1) :
    fBlock p = B.1 := by
  rcases Finset.mem_image.mp B.2 with ⟨s, _hs, hsB⟩
  rw [← hsB] at hp ⊢
  exact fBlock_eq_of_mem s p hp

noncomputable def blockStateEquivTouched (route : List Perm7) :
    (Σ B : TouchedBlock route, ↑B.1) ≃ TouchedState route where
  toFun x := ⟨x.2.1, by
    change fBlock x.2.1 ∈ touchedBlocks route
    rw [fBlock_eq_touchedBlock_of_mem x.1 x.2.2]
    exact x.1.2⟩
  invFun x := ⟨⟨fBlock x.1, x.2⟩, ⟨x.1, self_mem_fBlock x.1⟩⟩
  left_inv x := by
    have hB : (⟨fBlock x.2.1, by
        rw [fBlock_eq_touchedBlock_of_mem x.1 x.2.2]
        exact x.1.2⟩ : TouchedBlock route) = x.1 := by
      apply Subtype.ext
      exact fBlock_eq_touchedBlock_of_mem x.1 x.2.2
    apply Sigma.ext hB
    have hBval : fBlock x.2.1 = x.1.1 := by
      exact congrArg Subtype.val hB
    have hpred : ∀ p : Perm7,
        p ∈ fBlock x.2.1 ↔ p ∈ x.1.1 := by
      intro p
      rw [hBval]
    exact (Subtype.heq_iff_coe_eq hpred).2 rfl
  right_inv x := by
    apply Subtype.ext
    rfl

theorem touchedState_card (route : List Perm7) :
    Fintype.card (TouchedState route) = 6 * (touchedBlocks route).card := by
  have hfiber : ∀ B : TouchedBlock route, Fintype.card ↑B.1 = 6 := by
    intro B
    rw [Fintype.card_coe]
    rcases Finset.mem_image.mp B.2 with ⟨s, _hs, hsB⟩
    rw [← hsB, fBlock_card]
  calc
    Fintype.card (TouchedState route) =
        Fintype.card (Σ B : TouchedBlock route, ↑B.1) :=
      Fintype.card_congr (blockStateEquivTouched route).symm
    _ = ∑ B : TouchedBlock route, Fintype.card ↑B.1 := Fintype.card_sigma
    _ = ∑ _B : TouchedBlock route, 6 := by
      apply Finset.sum_congr rfl
      intro B _hB
      exact hfiber B
    _ = 6 * (touchedBlocks route).card := by
      simp [Nat.mul_comm]

/-- `F`, packaged as a permutation of all states. -/
def insertionPerm7 : Equiv.Perm Perm7 where
  toFun := F
  invFun := fun p => insertIndex.symm.trans p
  left_inv := by native_decide
  right_inv := by native_decide

/-- Restriction of `F` to the union of touched blocks. -/
def touchedFPerm (route : List Perm7) : Equiv.Perm (TouchedState route) :=
  insertionPerm7.subtypePerm fun p => by
    change fBlock (F p) ∈ touchedBlocks route ↔
      fBlock p ∈ touchedBlocks route
    rw [fBlock_F]

@[simp] theorem touchedFPerm_apply_val (route : List Perm7)
    (p : TouchedState route) :
    (touchedFPerm route p).1 = F p.1 := rfl

theorem touchedFPerm_pow_apply_val (route : List Perm7) (n : ℕ)
    (p : TouchedState route) :
    ((touchedFPerm route ^ n) p).1 = (F^[n]) p.1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, Function.iterate_succ_apply']
      change F ((touchedFPerm route ^ n) p).1 = F ((F^[n]) p.1)
      rw [ih]

noncomputable def touchedBlockRepresentative (route : List Perm7)
    (B : TouchedBlock route) : Perm7 :=
  Classical.choose (Finset.mem_image.mp B.2)

theorem touchedBlockRepresentative_start (route : List Perm7)
    (B : TouchedBlock route) :
    touchedBlockRepresentative route B ∈ runStartSet route :=
  (Classical.choose_spec (Finset.mem_image.mp B.2)).1

theorem touchedBlockRepresentative_block (route : List Perm7)
    (B : TouchedBlock route) :
    fBlock (touchedBlockRepresentative route B) = B.1 :=
  (Classical.choose_spec (Finset.mem_image.mp B.2)).2

noncomputable def touchedBlockRepresentativeState (route : List Perm7)
    (B : TouchedBlock route) : TouchedState route :=
  ⟨touchedBlockRepresentative route B, by
    change fBlock (touchedBlockRepresentative route B) ∈ touchedBlocks route
    rw [touchedBlockRepresentative_block]
    exact B.2⟩

/-- Fixed vectors of the touched `F` permutation are choices of one scalar
per touched block. -/
noncomputable def touchedBlockFunctionsEquivFFixed (route : List Perm7) :
    (TouchedBlock route → ℝ) ≃ₗ[ℝ] permFixedSubmodule (touchedFPerm route) where
  toFun f := ⟨fun p => f ⟨fBlock p.1, p.2⟩, by
    intro p
    change f ⟨fBlock (F p.1), (touchedFPerm route p).2⟩ =
      f ⟨fBlock p.1, p.2⟩
    congr 1
    apply Subtype.ext
    exact fBlock_F p.1⟩
  invFun v := fun B => v.1 (touchedBlockRepresentativeState route B)
  left_inv f := by
    funext B
    exact congrArg f (Subtype.ext (touchedBlockRepresentative_block route B))
  right_inv v := by
    apply Subtype.ext
    funext p
    let B : TouchedBlock route := ⟨fBlock p.1, p.2⟩
    have hpMem : p.1 ∈ fBlock (touchedBlockRepresentative route B) := by
      rw [touchedBlockRepresentative_block]
      exact self_mem_fBlock p.1
    rcases Finset.mem_image.mp hpMem with ⟨i, hi, hipow⟩
    have hpow : (touchedFPerm route ^ i)
        (touchedBlockRepresentativeState route B) = p := by
      apply Subtype.ext
      rw [touchedFPerm_pow_apply_val]
      exact hipow
    have hvpow := permFixed_apply_pow (touchedFPerm route) v i
      (touchedBlockRepresentativeState route B)
    rw [hpow] at hvpow
    exact hvpow.symm
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem touchedFPerm_cycleCount (route : List Perm7) :
    permCycleCount (touchedFPerm route) = (touchedBlocks route).card := by
  calc
    permCycleCount (touchedFPerm route) =
        Module.finrank ℝ (permFixedSubmodule (touchedFPerm route)) :=
      (finrank_permFixedSubmodule (touchedFPerm route)).symm
    _ = Module.finrank ℝ (TouchedBlock route → ℝ) :=
      (touchedBlockFunctionsEquivFFixed route).finrank_eq.symm
    _ = Fintype.card (TouchedBlock route) := Module.finrank_pi ℝ
    _ = (touchedBlocks route).card := Fintype.card_coe _

/-! ## Fixed spaces under transport and a subtype split -/

/-- Conjugating a permutation along an equivalence does not change its
fixed-vector space. -/
noncomputable def permCongrFixedEquiv {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (e : X ≃ Y) (P : Equiv.Perm X) :
    permFixedSubmodule (e.permCongr P) ≃ₗ[ℝ] permFixedSubmodule P where
  toFun v := ⟨fun x => v.1 (e x), by
    intro x
    have h := v.2 (e x)
    simpa using h⟩
  invFun v := ⟨fun y => v.1 (e.symm y), by
    intro y
    have h := v.2 (e.symm y)
    simpa using h⟩
  left_inv v := by
    apply Subtype.ext
    funext y
    simp
  right_inv v := by
    apply Subtype.ext
    funext x
    simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem permCycleCount_permCongr {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (e : X ≃ Y) (P : Equiv.Perm X) :
    permCycleCount (e.permCongr P) = permCycleCount P := by
  rw [← finrank_permFixedSubmodule (e.permCongr P),
    ← finrank_permFixedSubmodule P]
  exact (permCongrFixedEquiv e P).finrank_eq

/-- A permutation assembled from invariant complementary subtypes has the
product of their two fixed-vector spaces. -/
noncomputable def subtypeCongrFixedEquiv {X : Type*}
    [Fintype X] [DecidableEq X] (p : X → Prop) [DecidablePred p]
    (P : Equiv.Perm {x // p x}) (Q : Equiv.Perm {x // ¬ p x}) :
    permFixedSubmodule (P.subtypeCongr Q) ≃ₗ[ℝ]
      permFixedSubmodule P × permFixedSubmodule Q where
  toFun v :=
    (⟨fun x => v.1 x.1, by
      intro x
      have h := v.2 x.1
      simpa using h⟩,
     ⟨fun x => v.1 x.1, by
      intro x
      have h := v.2 x.1
      simpa using h⟩)
  invFun v := ⟨fun x => if hx : p x then v.1.1 ⟨x, hx⟩
      else v.2.1 ⟨x, hx⟩, by
    intro x
    by_cases hx : p x
    · rw [Equiv.Perm.subtypeCongr.left_apply P Q hx]
      simp only [dif_pos hx, dif_pos (P ⟨x, hx⟩).2]
      exact v.1.2 ⟨x, hx⟩
    · rw [Equiv.Perm.subtypeCongr.right_apply P Q hx]
      simp only [dif_neg hx, dif_neg (Q ⟨x, hx⟩).2]
      exact v.2.2 ⟨x, hx⟩⟩
  left_inv v := by
    apply Subtype.ext
    funext x
    by_cases hx : p x <;> simp [hx]
  right_inv v := by
    apply Prod.ext
    · apply Subtype.ext
      funext x
      simp [x.2]
    · apply Subtype.ext
      funext x
      simp [x.2]
  map_add' v w := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl
  map_smul' c v := by
    apply Prod.ext <;> apply Subtype.ext <;> rfl

theorem permCycleCount_subtypeCongr {X : Type*}
    [Fintype X] [DecidableEq X] (p : X → Prop) [DecidablePred p]
    (P : Equiv.Perm {x // p x}) (Q : Equiv.Perm {x // ¬ p x}) :
    permCycleCount (P.subtypeCongr Q) =
      permCycleCount P + permCycleCount Q := by
  rw [← finrank_permFixedSubmodule (P.subtypeCongr Q),
    ← finrank_permFixedSubmodule P, ← finrank_permFixedSubmodule Q,
    ← Module.finrank_prod]
  exact (subtypeCongrFixedEquiv p P Q).finrank_eq

theorem permCycleCount_one {X : Type*} [Fintype X] [DecidableEq X] :
    permCycleCount (1 : Equiv.Perm X) = Fintype.card X := by
  simp [permCycleCount_eq, Equiv.Perm.cycleType_one]

def IsSelectedTouched (route : List Perm7) (p : TouchedState route) : Prop :=
  p.1 ∈ runStartSet route

instance (route : List Perm7) (p : TouchedState route) :
    Decidable (IsSelectedTouched route p) := by
  unfold IsSelectedTouched
  infer_instance

noncomputable def runStartEquivSelectedTouched (route : List Perm7) :
    RunStart route ≃ {p : TouchedState route // IsSelectedTouched route p} where
  toFun s := ⟨⟨s.1, by
    change fBlock s.1 ∈ touchedBlocks route
    exact Finset.mem_image.mpr ⟨s.1, s.2, rfl⟩⟩, s.2⟩
  invFun p := ⟨p.1.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def selectedTouchedAPerm (route : List Perm7) :
    Equiv.Perm {p : TouchedState route // IsSelectedTouched route p} :=
  (runStartEquivSelectedTouched route).permCongr (runStartPerm route)

/-- `A` cycles the selected starts in each rotation class and fixes holes. -/
noncomputable def touchedAPerm (route : List Perm7) :
    Equiv.Perm (TouchedState route) :=
  (selectedTouchedAPerm route).subtypeCongr 1

abbrev TouchedHole (route : List Perm7) :=
  {p : TouchedState route // ¬ IsSelectedTouched route p}

theorem touchedHole_card (route : List Perm7) :
    Fintype.card (TouchedHole route) =
      Fintype.card (TouchedState route) - (runStartSet route).card := by
  rw [Fintype.card_subtype_compl]
  congr 1
  calc
    Fintype.card {p : TouchedState route // IsSelectedTouched route p} =
        Fintype.card (RunStart route) :=
      Fintype.card_congr (runStartEquivSelectedTouched route).symm
    _ = (runStartSet route).card := Fintype.card_coe _

theorem touchedAPerm_cycleCount (route : List Perm7)
    (hroute : IsHamiltonianRoute route) :
    permCycleCount (touchedAPerm route) =
      720 + Fintype.card (TouchedHole route) := by
  rw [touchedAPerm, permCycleCount_subtypeCongr,
    selectedTouchedAPerm,
    permCycleCount_permCongr (runStartEquivSelectedTouched route),
    runStartPerm_cycleCount route hroute, permCycleCount_one]

def runStartTouchedState (route : List Perm7) (s : RunStart route) :
    TouchedState route :=
  ⟨s.1, Finset.mem_image.mpr ⟨s.1, s.2, rfl⟩⟩

theorem runStartTouchedState_selected (route : List Perm7)
    (s : RunStart route) :
    IsSelectedTouched route (runStartTouchedState route s) := s.2

@[simp] theorem touchedAPerm_runStartTouchedState (route : List Perm7)
    (s : RunStart route) :
    touchedAPerm route (runStartTouchedState route s) =
      runStartTouchedState route (runStartPerm route s) := by
  apply Subtype.ext
  rw [touchedAPerm, Equiv.Perm.subtypeCongr.left_apply
    (selectedTouchedAPerm route) 1 (runStartTouchedState_selected route s)]
  change ((selectedTouchedAPerm route
    ((runStartEquivSelectedTouched route) s)).1).1 =
      (runStartPerm route s).1
  rw [selectedTouchedAPerm, Equiv.permCongr_apply]
  rfl

theorem touchedAPerm_pow_runStartTouchedState (route : List Perm7)
    (n : ℕ) (s : RunStart route) :
    (touchedAPerm route ^ n) (runStartTouchedState route s) =
      runStartTouchedState route ((runStartPerm route ^ n) s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', Equiv.Perm.mul_apply,
        ih, touchedAPerm_runStartTouchedState]

def touchedStateBlock (route : List Perm7) (p : TouchedState route) :
    TouchedBlock route := ⟨fBlock p.1, p.2⟩

@[simp] theorem touchedStateBlock_runStartTouchedState
    (route : List Perm7) (s : RunStart route) :
    touchedStateBlock route (runStartTouchedState route s) = startBlock s := rfl

noncomputable def touchedRotationComponent (route : List Perm7)
    (hroute : IsHamiltonianRoute route) (p : TouchedState route) :
    (rotationGraph route hroute).ConnectedComponent :=
  (rotationGraph route hroute).connectedComponentMk (touchedStateBlock route p)

theorem touchedRotationComponent_apply_F (route : List Perm7)
    (hroute : IsHamiltonianRoute route) (p : TouchedState route) :
    touchedRotationComponent route hroute (touchedFPerm route p) =
      touchedRotationComponent route hroute p := by
  apply congrArg ((rotationGraph route hroute).connectedComponentMk)
  apply Subtype.ext
  exact fBlock_F p.1

theorem touchedRotationComponent_apply_A (route : List Perm7)
    (hroute : IsHamiltonianRoute route) (p : TouchedState route) :
    touchedRotationComponent route hroute (touchedAPerm route p) =
      touchedRotationComponent route hroute p := by
  by_cases hp : IsSelectedTouched route p
  · let s : RunStart route := ⟨p.1, hp⟩
    have hps : p = runStartTouchedState route s := by
      apply Subtype.ext
      rfl
    rw [hps, touchedAPerm_runStartTouchedState]
    apply SimpleGraph.ConnectedComponent.sound
    exact startBlocks_reachable_of_same_rClass hroute
      (runStartPerm route s) s (by
        rw [runStartPerm_apply]
        exact nextRunStart_same_rClass route s)
  · have hfix : touchedAPerm route p = p := by
      rw [touchedAPerm,
        Equiv.Perm.subtypeCongr.right_apply (selectedTouchedAPerm route) 1 hp]
      rfl
    rw [hfix]

theorem touchedF_fixed_eq_of_block_eq (route : List Perm7)
    (v : permFixedSubmodule (touchedFPerm route))
    (p q : TouchedState route)
    (hpq : touchedStateBlock route p = touchedStateBlock route q) :
    v.1 p = v.1 q := by
  have hblocks : fBlock p.1 = fBlock q.1 := congrArg Subtype.val hpq
  have hqmem : q.1 ∈ fBlock p.1 := by
    rw [hblocks]
    exact self_mem_fBlock q.1
  rcases Finset.mem_image.mp hqmem with ⟨i, hi, hipow⟩
  have hstate : (touchedFPerm route ^ i) p = q := by
    apply Subtype.ext
    rw [touchedFPerm_pow_apply_val]
    exact hipow
  have hv := permFixed_apply_pow (touchedFPerm route) v i p
  rw [hstate] at hv
  exact hv.symm

theorem touchedA_fixed_eq_of_same_rClass (route : List Perm7)
    (v : permFixedSubmodule (touchedAPerm route))
    (s t : RunStart route) (hst : rClass s.1 = rClass t.1) :
    v.1 (runStartTouchedState route s) =
      v.1 (runStartTouchedState route t) := by
  have hcycle := runStartPerm_sameCycle_of_same_rClass route s t hst
  obtain ⟨n, _hnpos, _hnbound, hn⟩ := hcycle.exists_pow_eq (runStartPerm route)
  have hstate : (touchedAPerm route ^ n)
      (runStartTouchedState route s) = runStartTouchedState route t := by
    rw [touchedAPerm_pow_runStartTouchedState, hn]
  have hv := permFixed_apply_pow (touchedAPerm route) v n
    (runStartTouchedState route s)
  rw [hstate] at hv
  exact hv.symm

noncomputable def rotationVertexValue (route : List Perm7)
    (hroute : IsHamiltonianRoute route)
    (v : commonFixedSubmodule (touchedFPerm route) (touchedAPerm route))
    (B : TouchedBlock route) : ℝ :=
  v.1 (touchedBlockRepresentativeState route B)

theorem touchedStateBlock_representative (route : List Perm7)
    (B : TouchedBlock route) :
    touchedStateBlock route (touchedBlockRepresentativeState route B) = B := by
  apply Subtype.ext
  exact touchedBlockRepresentative_block route B

theorem rotationVertexValue_eq_state_of_block (route : List Perm7)
    (hroute : IsHamiltonianRoute route)
    (v : commonFixedSubmodule (touchedFPerm route) (touchedAPerm route))
    (B : TouchedBlock route) (p : TouchedState route)
    (hp : touchedStateBlock route p = B) :
    rotationVertexValue route hroute v B = v.1 p := by
  apply touchedF_fixed_eq_of_block_eq route ⟨v.1, v.2.1⟩
  exact (touchedStateBlock_representative route B).trans hp.symm

theorem rotationVertexValue_startBlock (route : List Perm7)
    (hroute : IsHamiltonianRoute route)
    (v : commonFixedSubmodule (touchedFPerm route) (touchedAPerm route))
    (s : RunStart route) :
    rotationVertexValue route hroute v (startBlock s) =
      v.1 (runStartTouchedState route s) := by
  apply rotationVertexValue_eq_state_of_block route hroute v
  rfl

theorem rotationVertexValue_eq_of_adj (route : List Perm7)
    (hroute : IsHamiltonianRoute route)
    (v : commonFixedSubmodule (touchedFPerm route) (touchedAPerm route))
    {B D : TouchedBlock route} (hBD : (rotationGraph route hroute).Adj B D) :
    rotationVertexValue route hroute v B =
      rotationVertexValue route hroute v D := by
  have hBD' := hBD
  rw [rotationGraph, SimpleGraph.fromEdgeSet_adj] at hBD'
  have hmem : s(B, D) ∈ rotationEdgeCandidates route hroute := by
    simpa using hBD'.1
  obtain ⟨s, _hs, hsedge⟩ := Finset.mem_image.mp hmem
  let b := baseRunStart route hroute (rotationClassOf s.1)
  have hclass : rClass s.1 = rClass b.1 := by
    have hb := rotationClassOf_baseRunStart route hroute
      (rotationClassOf s.1)
    exact (congrArg Subtype.val hb).symm
  have hvalues : rotationVertexValue route hroute v (startBlock s) =
      rotationVertexValue route hroute v (startBlock b) := by
    rw [rotationVertexValue_startBlock, rotationVertexValue_startBlock]
    exact touchedA_fixed_eq_of_same_rClass route ⟨v.1, v.2.2⟩ s b hclass
  change s(startBlock s, startBlock b) = s(B, D) at hsedge
  rw [Sym2.eq_iff] at hsedge
  rcases hsedge with hsedge | hsedge
  · rcases hsedge with ⟨rfl, rfl⟩
    exact hvalues
  · rcases hsedge with ⟨rfl, rfl⟩
    exact hvalues.symm

theorem rotationVertexValue_eq_of_walk (route : List Perm7)
    (hroute : IsHamiltonianRoute route)
    (v : commonFixedSubmodule (touchedFPerm route) (touchedAPerm route))
    {B D : TouchedBlock route} (w : (rotationGraph route hroute).Walk B D) :
    rotationVertexValue route hroute v B =
      rotationVertexValue route hroute v D := by
  induction w with
  | nil => rfl
  | cons h w ih =>
      exact (rotationVertexValue_eq_of_adj route hroute v h).trans ih

theorem commonFixed_eq_of_touchedRotationComponent_eq (route : List Perm7)
    (hroute : IsHamiltonianRoute route)
    (v : commonFixedSubmodule (touchedFPerm route) (touchedAPerm route))
    {p q : TouchedState route}
    (hpq : touchedRotationComponent route hroute p =
      touchedRotationComponent route hroute q) :
    v.1 p = v.1 q := by
  have hreach : (rotationGraph route hroute).Reachable
      (touchedStateBlock route p) (touchedStateBlock route q) :=
    SimpleGraph.ConnectedComponent.exact hpq
  apply hreach.elim
  intro w
  rw [← rotationVertexValue_eq_state_of_block route hroute v
      (touchedStateBlock route p) p rfl,
    ← rotationVertexValue_eq_state_of_block route hroute v
      (touchedStateBlock route q) q rfl]
  exact rotationVertexValue_eq_of_walk route hroute v w

noncomputable def rotationComponentBlockRepresentative (route : List Perm7)
    (hroute : IsHamiltonianRoute route)
    (K : (rotationGraph route hroute).ConnectedComponent) :
    TouchedBlock route :=
  Classical.choose K.nonempty_supp

theorem rotationComponentBlockRepresentative_spec (route : List Perm7)
    (hroute : IsHamiltonianRoute route)
    (K : (rotationGraph route hroute).ConnectedComponent) :
    (rotationGraph route hroute).connectedComponentMk
      (rotationComponentBlockRepresentative route hroute K) = K :=
  (K.mem_supp_iff _).mp (Classical.choose_spec K.nonempty_supp)

noncomputable def rotationComponentStateRepresentative (route : List Perm7)
    (hroute : IsHamiltonianRoute route)
    (K : (rotationGraph route hroute).ConnectedComponent) :
    TouchedState route :=
  touchedBlockRepresentativeState route
    (rotationComponentBlockRepresentative route hroute K)

theorem rotationComponentStateRepresentative_spec (route : List Perm7)
    (hroute : IsHamiltonianRoute route)
    (K : (rotationGraph route hroute).ConnectedComponent) :
    touchedRotationComponent route hroute
      (rotationComponentStateRepresentative route hroute K) = K := by
  rw [touchedRotationComponent, rotationComponentStateRepresentative,
    touchedStateBlock_representative,
    rotationComponentBlockRepresentative_spec]

/-- The common fixed space of the actual route permutations `F` and `A`
has one degree of freedom per component of the route's rotation quotient. -/
noncomputable def rotationComponentFunctionsEquivCommonFixed
    (route : List Perm7) (hroute : IsHamiltonianRoute route) :
    ((rotationGraph route hroute).ConnectedComponent → ℝ) ≃ₗ[ℝ]
      commonFixedSubmodule (touchedFPerm route) (touchedAPerm route) where
  toFun f := ⟨fun p => f (touchedRotationComponent route hroute p), by
    constructor
    · intro p
      change f (touchedRotationComponent route hroute (touchedFPerm route p)) =
        f (touchedRotationComponent route hroute p)
      rw [touchedRotationComponent_apply_F]
    · intro p
      change f (touchedRotationComponent route hroute (touchedAPerm route p)) =
        f (touchedRotationComponent route hroute p)
      rw [touchedRotationComponent_apply_A]⟩
  invFun v := fun K => v.1 (rotationComponentStateRepresentative route hroute K)
  left_inv f := by
    funext K
    change f (touchedRotationComponent route hroute
      (rotationComponentStateRepresentative route hroute K)) = f K
    rw [rotationComponentStateRepresentative_spec]
  right_inv v := by
    apply Subtype.ext
    funext p
    apply commonFixed_eq_of_touchedRotationComponent_eq route hroute v
    exact rotationComponentStateRepresentative_spec route hroute
      (touchedRotationComponent route hroute p)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem touchedFA_incidenceComponentCount (route : List Perm7)
    (hroute : IsHamiltonianRoute route) :
    incidenceComponentCount (touchedFPerm route) (touchedAPerm route) =
      rotationComponentCount route hroute := by
  rw [← commonFixed_finrank_eq_incidenceComponentCount,
    ← (rotationComponentFunctionsEquivCommonFixed route hroute).finrank_eq,
    Module.finrank_pi]
  rfl

/-! ## Product cycles and actual cost-one/two chains -/

/-- The face permutation `T = F*A`; products act right-to-left. -/
noncomputable def touchedTPerm (route : List Perm7) :
    Equiv.Perm (TouchedState route) :=
  touchedFPerm route * touchedAPerm route

@[simp] theorem touchedTPerm_runStartTouchedState_val
    (route : List Perm7) (s : RunStart route) :
    (touchedTPerm route (runStartTouchedState route s)).1 =
      F (runStartPerm route s).1 := by
  rw [touchedTPerm, Equiv.Perm.mul_apply,
    touchedAPerm_runStartTouchedState, touchedFPerm_apply_val]
  rfl

theorem touchedAPerm_eq_self_of_not_selected (route : List Perm7)
    (p : TouchedState route) (hp : ¬ IsSelectedTouched route p) :
    touchedAPerm route p = p := by
  rw [touchedAPerm,
    Equiv.Perm.subtypeCongr.right_apply (selectedTouchedAPerm route) 1 hp]
  rfl

theorem touchedTPerm_eq_touchedF_of_not_selected (route : List Perm7)
    (p : TouchedState route) (hp : ¬ IsSelectedTouched route p) :
    touchedTPerm route p = touchedFPerm route p := by
  rw [touchedTPerm, Equiv.Perm.mul_apply,
    touchedAPerm_eq_self_of_not_selected route p hp]

/-- If a selected start is the destination of an actual cheap edge, its
predecessor under `T` is the preceding cost-one run start, and occurs
strictly earlier in the linear Hamilton route. -/
theorem touchedT_predecessor_earlier_of_mem_cheapTwoDestinations
    {route : List Perm7} (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route) (s : RunStart route)
    (hsCheap : s.1 ∈ cheapTwoDestinations route) :
    ∃ u : RunStart route,
      touchedTPerm route (runStartTouchedState route u) =
        runStartTouchedState route s ∧
      route.idxOf u.1 < route.idxOf s.1 := by
  obtain ⟨x, hxEdge, hxCheap⟩ :=
    mem_cheapTwoDestinations_gives_edge hsCheap
  have hsNotOne : s.1 ∉ costOneDestinations route := by
    have hsMem := Finset.mem_sdiff.mp s.2
    intro hsOne
    exact hsMem.2 (by simpa using hsOne)
  have hxNotOne : d x s.1 ≠ 1 := by
    intro hxOne
    exact hsNotOne (pair_infix_mem_costOneDestinations hxEdge hxOne)
  have hidxEdge := idxOf_succ_of_pair_infix hroute.1 (hroute.2 x)
    (hroute.2 s.1) hxEdge
  have hxs : x ≠ s.1 := by
    intro hxs
    subst x
    simp at hidxEdge
  have hxPos := d_pos_of_ne hxs
  have hxTwo : d x s.1 = 2 := by omega
  let rx : RunStart route :=
    ⟨R x, rotation_successor_runStart_of_cost_two hroute hxEdge hxTwo⟩
  let u : RunStart route := (runStartPerm route).symm rx
  have hperm : runStartPerm route u = rx := by
    exact (runStartPerm route).apply_symm_apply rx
  have hnext : nextRunStart route u = rx := by
    rw [← runStartPerm_apply]
    exact hperm
  let m := runReturnTime route u
  have hmPos : 0 < m := by
    exact (runReturnTime_spec route u).1
  let j := m - 1
  have hmj : m = j + 1 := by
    dsimp [j]
    omega
  have hpowRx : (rotationPerm7 ^ m) u.1 = rx.1 := by
    exact congrArg Subtype.val hnext
  have hxPow : x = (rotationPerm7 ^ j) u.1 := by
    apply R_injective
    calc
      R x = rx.1 := rfl
      _ = (rotationPerm7 ^ m) u.1 := hpowRx.symm
      _ = R ((rotationPerm7 ^ j) u.1) := by
        rw [hmj, pow_succ', Equiv.Perm.mul_apply]
        rfl
  have hjm : j < m := by
    dsimp [j]
    omega
  have hidxRun := idxOf_rotationPerm7_pow_before_return hroute u j hjm
  have hidxEarlier : route.idxOf u.1 < route.idxOf s.1 := by
    rw [← hxPow] at hidxRun
    omega
  have hsNorm : s.1 = N₂ x := normalized_cost_two_edge hnormal hxEdge hxTwo
  have hsF : s.1 = F rx.1 := by
    dsimp [rx]
    rw [hsNorm, N₂_eq_F_R]
  refine ⟨u, ?_, hidxEarlier⟩
  apply Subtype.ext
  rw [touchedTPerm_runStartTouchedState_val, hperm]
  exact hsF.symm

/-- No `T`-cycle can consist only of holes: on holes `T=F`, while every
touched `F`-block contains a selected run start. -/
theorem touchedTPerm_cycle_meets_runStart (route : List Perm7)
    (p : TouchedState route) :
    ∃ s : RunStart route,
      (touchedTPerm route).SameCycle p (runStartTouchedState route s) := by
  classical
  by_contra hnone
  push Not at hnone
  have hnotSelected : ∀ n : ℕ,
      ¬ IsSelectedTouched route ((touchedTPerm route ^ n) p) := by
    intro n hnSelected
    let s : RunStart route :=
      ⟨((touchedTPerm route ^ n) p).1, hnSelected⟩
    apply hnone s
    have hsEq : runStartTouchedState route s =
        (touchedTPerm route ^ n) p := by
      apply Subtype.ext
      rfl
    rw [hsEq]
    refine ⟨(n : ℤ), ?_⟩
    simp
  have hiter : ∀ n : ℕ,
      (touchedTPerm route ^ n) p = (touchedFPerm route ^ n) p := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        rw [pow_succ', Equiv.Perm.mul_apply, pow_succ', Equiv.Perm.mul_apply,
          touchedTPerm_eq_touchedF_of_not_selected route
            ((touchedTPerm route ^ n) p) (hnotSelected n), ih]
  rcases Finset.mem_image.mp p.2 with ⟨s, hsStart, hsBlock⟩
  let rs : RunStart route := ⟨s, hsStart⟩
  have hsMem : s ∈ fBlock p.1 := by
    rw [← hsBlock]
    exact self_mem_fBlock s
  rcases Finset.mem_image.mp hsMem with ⟨i, hi, hipow⟩
  have hfinal : (touchedTPerm route ^ i) p =
      runStartTouchedState route rs := by
    rw [hiter]
    apply Subtype.ext
    rw [touchedFPerm_pow_apply_val]
    exact hipow
  apply hnone rs
  rw [← hfinal]
  refine ⟨(i : ℤ), ?_⟩
  simp

/-- Following missing cheap predecessors strictly backwards must terminate
at a genuine cost-one/two chain start, without leaving the same `T`-cycle. -/
theorem runStart_same_touchedTCycle_as_chainStart
    {route : List Perm7} (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route) (s : RunStart route) :
    ∃ c : ChainStart route,
      (touchedTPerm route).SameCycle (runStartTouchedState route s)
        (runStartTouchedState route (chainAsRunStart c)) := by
  by_cases hsChain : s.1 ∈ chainStartSet route
  · let c : ChainStart route := ⟨s.1, hsChain⟩
    refine ⟨c, ?_⟩
    apply Eq.sameCycle
    apply Subtype.ext
    rfl
  · have hsCheap : s.1 ∈ cheapTwoDestinations route := by
      simpa [chainStartSet] using hsChain
    obtain ⟨u, hTu, huEarlier⟩ :=
      touchedT_predecessor_earlier_of_mem_cheapTwoDestinations
        hroute hnormal s hsCheap
    obtain ⟨c, huc⟩ :=
      runStart_same_touchedTCycle_as_chainStart hroute hnormal u
    refine ⟨c, ?_⟩
    have hus : (touchedTPerm route).SameCycle
        (runStartTouchedState route u) (runStartTouchedState route s) := by
      refine ⟨1, ?_⟩
      simpa using hTu
    exact hus.symm.trans huc
termination_by route.idxOf s.1
decreasing_by exact huEarlier

theorem touchedTPerm_cycle_meets_chainStart
    {route : List Perm7} (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route) (p : TouchedState route) :
    ∃ c : ChainStart route,
      (touchedTPerm route).SameCycle p
        (runStartTouchedState route (chainAsRunStart c)) := by
  obtain ⟨s, hps⟩ := touchedTPerm_cycle_meets_runStart route p
  obtain ⟨c, hsc⟩ :=
    runStart_same_touchedTCycle_as_chainStart hroute hnormal s
  exact ⟨c, hps.trans hsc⟩

noncomputable def chainStartToTouchedTCycle (route : List Perm7)
    (c : ChainStart route) : PermCycle (touchedTPerm route) :=
  permCycleOf (touchedTPerm route)
    (runStartTouchedState route (chainAsRunStart c))

theorem chainStartToTouchedTCycle_surjective
    {route : List Perm7} (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route) :
    Function.Surjective (chainStartToTouchedTCycle route) := by
  intro C
  let p := permCycleRepresentative (touchedTPerm route) C
  obtain ⟨c, hpc⟩ :=
    touchedTPerm_cycle_meets_chainStart hroute hnormal p
  refine ⟨c, ?_⟩
  change permCycleOf (touchedTPerm route)
      (runStartTouchedState route (chainAsRunStart c)) = C
  calc
    permCycleOf (touchedTPerm route)
        (runStartTouchedState route (chainAsRunStart c)) =
        permCycleOf (touchedTPerm route) p :=
      permCycleOf_eq_of_sameCycle (touchedTPerm route) hpc.symm
    _ = C := permCycleRepresentative_spec (touchedTPerm route) C

/-- This discharges the manuscript's last route-specific hypothesis in the
Section 4 Euler calculation. -/
theorem touchedTPerm_cycleCount_le_chainStartSet_card
    {route : List Perm7} (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route) :
    permCycleCount (touchedTPerm route) ≤ (chainStartSet route).card := by
  have hcard := Fintype.card_le_of_surjective
    (chainStartToTouchedTCycle route)
    (chainStartToTouchedTCycle_surjective hroute hnormal)
  simpa [permCycleCount, Fintype.card_coe] using hcard

end Superperm7
