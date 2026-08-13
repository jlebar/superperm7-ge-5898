/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE); this file is
additionally subject to the upstream MIT notice below.

Adapted from https://github.com/BGray-wrl/superperm6
  file:   formal-verification/Superperm6/CoarsenAccounting.lean
  commit: d8a932d8f61d80b0bcfc737bd0e235a8300449c4
  upstream copyright: Copyright (c) 2026 Benjamin Grayzel — MIT License (reproduced in NOTICE).
Local modifications (port from six to seven symbols; see docs/PORT_LOG.md): seven-symbol constants; trail-budget arithmetic takes p0 <= z.p.
-/
import Superperm7.CoarsenAux

/-!
# Global accounting for retained coarsening rows

This file supplies the orbit and finite-block bookkeeping used by the final
accounting theorem in `CoarsenBridge.lean`.
-/

namespace Superperm7

open List

set_option maxHeartbeats 4000000

/-! ## The first-return partition and the total gap count -/

/-- A state position before the next return of a chain start under `T`. -/
abbrev ChainReturnSlot (route : List Perm7) :=
  Σ c : ChainStart route, Fin (chainReturnTime route c)

noncomputable def chainReturnSlotState (route : List Perm7) :
    ChainReturnSlot route → TouchedState route
  | ⟨c, i⟩ =>
      (touchedTPerm route ^ i.val) (chainTouchedState route c)

private theorem chainReturnSlot_eq_of_le
    (route : List Perm7)
    (x y : ChainReturnSlot route)
    (hxy : chainReturnSlotState route x =
      chainReturnSlotState route y)
    (hle : x.2.val ≤ y.2.val) :
    x = y := by
  rcases x with ⟨c, i⟩
  rcases y with ⟨d, j⟩
  change i.val ≤ j.val at hle
  let delta := j.val - i.val
  have hj : j.val = i.val + delta := by
    dsimp [delta]
    omega
  have hcancel :
      chainTouchedState route c =
        (touchedTPerm route ^ delta) (chainTouchedState route d) := by
    apply (touchedTPerm route ^ i.val).injective
    calc
      (touchedTPerm route ^ i.val) (chainTouchedState route c) =
          (touchedTPerm route ^ j.val)
            (chainTouchedState route d) := hxy
      _ = (touchedTPerm route ^ (i.val + delta))
            (chainTouchedState route d) := by rw [hj]
      _ = (touchedTPerm route ^ i.val)
            ((touchedTPerm route ^ delta)
              (chainTouchedState route d)) := by
          rw [pow_add, Equiv.Perm.mul_apply]
  have hdelta : delta = 0 := by
    by_contra hne
    have hpos : 0 < delta := Nat.pos_of_ne_zero hne
    have hlt : delta < chainReturnTime route d := by
      have hjlt := j.isLt
      dsimp [delta]
      omega
    apply chainReturnTime_min route d hlt
    refine ⟨hpos, ?_⟩
    rw [← hcancel]
    exact c.2
  have hij : i.val = j.val := by
    dsimp [delta] at hdelta
    omega
  have hcd : c = d := by
    have hstate : chainTouchedState route c =
        chainTouchedState route d := by
      simpa [hdelta] using hcancel
    apply Subtype.ext
    exact congrArg (fun p : TouchedState route => p.1) hstate
  subst d
  have hij' : i = j := Fin.ext hij
  subst j
  rfl

theorem chainReturnSlotState_injective (route : List Perm7) :
    Function.Injective (chainReturnSlotState route) := by
  intro x y hxy
  by_cases hle : x.2.val ≤ y.2.val
  · exact chainReturnSlot_eq_of_le route x y hxy hle
  · exact (chainReturnSlot_eq_of_le route y x hxy.symm
      (Nat.le_of_not_ge hle)).symm

private theorem chainReturnSlotState_surjective_power
    {route : List Perm7} :
    ∀ n : ℕ, ∀ c : ChainStart route,
      ∃ x : ChainReturnSlot route,
        chainReturnSlotState route x =
          (touchedTPerm route ^ n) (chainTouchedState route c) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro c
      by_cases hn : n < chainReturnTime route c
      · exact ⟨⟨c, ⟨n, hn⟩⟩, rfl⟩
      · let delta := n - chainReturnTime route c
        have hreturnPos : 0 < chainReturnTime route c :=
          (chainReturnTime_spec route c).1
        have hdeltaLt : delta < n := by
          dsimp [delta]
          omega
        obtain ⟨x, hx⟩ :=
          ih delta hdeltaLt (chainFaceNext route c)
        refine ⟨x, hx.trans ?_⟩
        calc
          (touchedTPerm route ^ delta)
              (chainTouchedState route (chainFaceNext route c)) =
            (touchedTPerm route ^ delta)
              ((touchedTPerm route ^ chainReturnTime route c)
                (chainTouchedState route c)) := by
              rw [chainFaceNext_apply,
                chainTouchedState_nextFace]
          _ = (touchedTPerm route ^
                (delta + chainReturnTime route c))
              (chainTouchedState route c) := by
              rw [pow_add, Equiv.Perm.mul_apply]
          _ = (touchedTPerm route ^ n)
              (chainTouchedState route c) := by
              congr 2
              dsimp [delta]
              omega

theorem chainReturnSlotState_surjective
    {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route) :
    Function.Surjective (chainReturnSlotState route) := by
  intro p
  obtain ⟨c, hcycle⟩ :=
    touchedTPerm_cycle_meets_chainStart hroute hnormal p
  obtain ⟨n, _hnpos, _hnbound, hn⟩ :=
    hcycle.symm.exists_pow_eq (touchedTPerm route)
  obtain ⟨x, hx⟩ :=
    chainReturnSlotState_surjective_power n c
  refine ⟨x, hx.trans ?_⟩
  simpa [chainTouchedState] using hn

theorem sum_chainReturnTime_eq_touchedState_card
    {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route) :
    (∑ c : ChainStart route, chainReturnTime route c) =
      Fintype.card (TouchedState route) := by
  calc
    (∑ c : ChainStart route, chainReturnTime route c) =
        Fintype.card (ChainReturnSlot route) := by
      simp [ChainReturnSlot]
    _ = Fintype.card (TouchedState route) :=
      Fintype.card_congr
        (Equiv.ofBijective (chainReturnSlotState route)
          ⟨chainReturnSlotState_injective route,
            chainReturnSlotState_surjective hroute hnormal⟩)

/-- A position in one of the materialized selected-state chains. -/
abbrev ChainRunSlot (route : List Perm7) :=
  Σ c : ChainStart route, Fin (chainRunStarts route c).length

noncomputable def chainRunSlotStart (route : List Perm7) :
    ChainRunSlot route → RunStart route
  | ⟨c, i⟩ => (chainRunStarts route c)[i.val]

theorem chainRunStarts_nodup
    {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (c : ChainStart route) :
    (chainRunStarts route c).Nodup := by
  have hchain :
      (chainRunStarts route c).IsChain fun s t =>
        route.idxOf s.1 < route.idxOf t.1 :=
    (chainRunStarts_isChain route c).imp fun s t hst =>
      hst.idxOf_lt hroute hnormal
  apply hchain.pairwise.imp
  intro s t hlt hst
  subst t
  exact (Nat.lt_irrefl _ hlt)

theorem chainRunSlotStart_injective
    {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route) :
    Function.Injective (chainRunSlotStart route) := by
  rintro ⟨c, i⟩ ⟨d, j⟩ hij
  change (chainRunStarts route c)[i.val] =
    (chainRunStarts route d)[j.val] at hij
  have hiMem : (chainRunStarts route c)[i.val] ∈
      chainRunStarts route c := List.getElem_mem ..
  have hjMem : (chainRunStarts route d)[j.val] ∈
      chainRunStarts route d := List.getElem_mem ..
  have hiMemD : (chainRunStarts route c)[i.val] ∈
      chainRunStarts route d := by
    rw [hij]
    exact hjMem
  have hcd : c = d :=
    runStart_chain_unique hroute hnormal
      (chainRunStarts route c)[i.val] c d hiMem hiMemD
  subst d
  have hindex : i.val = j.val :=
    (chainRunStarts_nodup hroute hnormal c).getElem_inj_iff.mp hij
  have hindex' : i = j := Fin.ext hindex
  subst j
  rfl

theorem chainRunSlotStart_surjective
    {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route) :
    Function.Surjective (chainRunSlotStart route) := by
  intro s
  obtain ⟨c, hc, _hunique⟩ :=
    chains_partition_runStarts hroute hnormal s
  obtain ⟨i, hi, his⟩ := List.getElem_of_mem hc
  exact ⟨⟨c, ⟨i, hi⟩⟩, his⟩

theorem sum_chainRunStarts_length_eq_runStart_card
    {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route) :
    (∑ c : ChainStart route, (chainRunStarts route c).length) =
      (runStartSet route).card := by
  calc
    (∑ c : ChainStart route, (chainRunStarts route c).length) =
        Fintype.card (ChainRunSlot route) := by
      simp [ChainRunSlot]
    _ = Fintype.card (RunStart route) :=
      Fintype.card_congr
        (Equiv.ofBijective (chainRunSlotStart route)
          ⟨chainRunSlotStart_injective hroute hnormal,
            chainRunSlotStart_surjective hroute hnormal⟩)
    _ = (runStartSet route).card := Fintype.card_coe _

/-- The chain gaps partition all touched holes, expressed in the cardinal
form used by the accounting proof. -/
theorem sum_gapLen_eq_structural_holes
    {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (z : RouteStructuralCounts route hroute) :
    (∑ c : ChainStart route, gapLen route c) =
      6 * z.m - z.r := by
  have hreturns :=
    sum_chainReturnTime_eq_touchedState_card hroute hnormal
  have hruns :=
    sum_chainRunStarts_length_eq_runStart_card hroute hnormal
  have hsplit :
      (∑ c : ChainStart route, chainReturnTime route c) =
        (∑ c : ChainStart route, (chainRunStarts route c).length) +
          ∑ c : ChainStart route, gapLen route c := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro c _hc
    exact chainReturnTime_eq_length_add_gapLen hroute hnormal c
  rw [touchedState_card, ← z.M_route] at hreturns
  rw [z.runStart_card] at hruns
  have hM := z.M_eq
  have hrm := z.r_le_six_m
  omega

/-! ## Counted holes and the charge injection -/

theorem F_iterates_fin_six_injective (p : Perm7) :
    Function.Injective (fun i : Fin 6 => (F^[i.val]) p) := by
  native_decide +revert

theorem fin_six_filter_lt_card (g : Fin 6) :
    ((Finset.univ : Finset (Fin 6)).filter
      fun i => i.val < g.val).card = g.val := by
  native_decide +revert

theorem F_cut_interval_disjoint
    (p : Perm7) (g i j : Fin 6)
    (hi : i.val < g.val) (hj : j.val < 6 - g.val) :
    (F^[i.val]) p ≠ (F^[j.val]) ((F^[g.val]) p) := by
  native_decide +revert

noncomputable def chainCutIndices (route : List Perm7)
    (c : ChainStart route) : Finset (Fin 6) :=
  Finset.univ.filter fun i => i.val < gapLen route c

noncomputable def chainCutHoles (route : List Perm7)
    (c : ChainStart route) : Finset Perm7 :=
  (chainCutIndices route c).image fun i =>
    (F^[i.val]) (gapFirstHole route c)

noncomputable def chainOmittedHoles (route : List Perm7)
    (c : ChainStart route) : Finset Perm7 :=
  (chainMarkedRow route c).omitted.image fun i =>
    (F^[i.val]) (chainGapRow route c).start

noncomputable def chainCountedHoles (route : List Perm7)
    (c : ChainStart route) : Finset Perm7 :=
  chainCutHoles route c ∪ chainOmittedHoles route c

theorem chainCutIndices_card (route : List Perm7)
    (c : ChainStart route) :
    (chainCutIndices route c).card = gapLen route c := by
  change ((Finset.univ : Finset (Fin 6)).filter
    fun i => i.val < (gapLenFin route c).val).card =
      (gapLenFin route c).val
  exact fin_six_filter_lt_card (gapLenFin route c)

theorem chainCutHoles_card (route : List Perm7)
    (c : ChainStart route) :
    (chainCutHoles route c).card = gapLen route c := by
  rw [chainCutHoles,
    Finset.card_image_of_injective _
      (F_iterates_fin_six_injective (gapFirstHole route c)),
    chainCutIndices_card]

theorem chainOmittedHoles_card (route : List Perm7)
    (c : ChainStart route) :
    (chainOmittedHoles route c).card =
      (chainMarkedRow route c).omitted.card := by
  exact Finset.card_image_of_injective _
    (F_iterates_fin_six_injective (chainGapRow route c).start)

theorem chainCutHoles_disjoint_chainOmittedHoles
    (route : List Perm7) (c : ChainStart route) :
    Disjoint (chainCutHoles route c) (chainOmittedHoles route c) := by
  rw [Finset.disjoint_left]
  intro p hpCut hpOmitted
  rcases Finset.mem_image.mp hpCut with ⟨i, hi, hip⟩
  rcases Finset.mem_image.mp hpOmitted with ⟨j, hj, hjp⟩
  have hiLt : i.val < (gapLenFin route c).val := by
    simpa [chainCutIndices] using hi
  have hjLen : j.val <
      6 - (gapLenFin route c).val := by
    have hj' := (mem_chainMarkedRow_omitted_iff route c j).1 hj
    simpa [chainGapRow, gapComplementRow_length] using hj'.1
  apply F_cut_interval_disjoint
    (gapFirstHole route c) (gapLenFin route c) i j hiLt hjLen
  calc
    (F^[i.val]) (gapFirstHole route c) = p := hip
    _ = (F^[j.val]) (chainGapRow route c).start := hjp.symm
    _ = (F^[j.val])
        ((F^[(gapLenFin route c).val])
          (gapFirstHole route c)) := rfl

theorem chainMarkedRow_charge_eq
    (route : List Perm7) (c : ChainStart route) :
    (chainMarkedRow route c).charge =
      gapLen route c + (chainMarkedRow route c).omitted.card := by
  unfold MarkedRow.charge
  rw [chainMarkedRow_row]
  change 6 -
      (gapComplementRow
        (gapFirstHole route c) (gapLenFin route c)).length +
        (chainMarkedRow route c).omitted.card =
    gapLen route c + (chainMarkedRow route c).omitted.card
  rw [gapComplementRow_length]
  have hgap := gapLen_le_five route c
  change 6 - (6 - gapLen route c) +
      (chainMarkedRow route c).omitted.card =
    gapLen route c + (chainMarkedRow route c).omitted.card
  omega

theorem chainCountedHoles_card (route : List Perm7)
    (c : ChainStart route) :
    (chainCountedHoles route c).card =
      (chainMarkedRow route c).charge := by
  rw [chainCountedHoles,
    Finset.card_union_of_disjoint
      (chainCutHoles_disjoint_chainOmittedHoles route c),
    chainCutHoles_card, chainOmittedHoles_card,
    chainMarkedRow_charge_eq]

theorem gap_F_iterate_not_selected
    (route : List Perm7) (c : ChainStart route)
    {j : ℕ} (hj : j < gapLen route c) :
    (F^[j]) (gapFirstHole route c) ∉ runStartSet route := by
  have hholes : ∀ i < j,
      ¬ IsSelectedTouched route
        ((touchedTPerm route ^ i) (chainGapSource route c)) := by
    intro i hi
    exact gapLen_min route c (hi.trans hj)
  have hTF :=
    touchedTPerm_pow_eq_touchedFPerm_pow_of_holes
      route (chainGapSource route c) j hholes
  have hnot := gapLen_min route c hj
  change ((touchedTPerm route ^ j)
    (chainGapSource route c)).1 ∉ runStartSet route at hnot
  rw [hTF, touchedFPerm_pow_apply_val] at hnot
  exact hnot

noncomputable def touchedHoleStates (route : List Perm7) :
    Finset Perm7 :=
  (Finset.univ : Finset (TouchedHole route)).image fun h => h.1.1

theorem mem_touchedHoleStates_iff
    (route : List Perm7) (p : Perm7) :
    p ∈ touchedHoleStates route ↔
      IsTouched route p ∧ p ∉ runStartSet route := by
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨h, _hh, rfl⟩
    exact ⟨h.1.2, h.2⟩
  · rintro ⟨hpTouched, hpHole⟩
    let h : TouchedHole route := ⟨⟨p, hpTouched⟩, hpHole⟩
    exact Finset.mem_image.mpr ⟨h, Finset.mem_univ h, rfl⟩

theorem touchedHoleStates_card (route : List Perm7) :
    (touchedHoleStates route).card =
      Fintype.card (TouchedHole route) := by
  rw [touchedHoleStates,
    Finset.card_image_of_injective]
  · exact Finset.card_univ
  · intro h h' heq
    apply Subtype.ext
    apply Subtype.ext
    exact heq

theorem chainCountedHoles_subset_touchedHoleStates
    {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (c : ChainStart route) :
    chainCountedHoles route c ⊆ touchedHoleStates route := by
  intro p hp
  rw [chainCountedHoles, Finset.mem_union] at hp
  apply (mem_touchedHoleStates_iff route p).2
  rcases hp with hpCut | hpOmitted
  · rcases Finset.mem_image.mp hpCut with ⟨i, hi, rfl⟩
    have hiLt : i.val < gapLen route c := by
      simpa [chainCutIndices] using hi
    constructor
    · change fBlock
          ((F^[i.val]) (gapFirstHole route c)) ∈
          touchedBlocks route
      rw [fBlock_F_iterate]
      exact (chainGapSource route c).2
    · exact gap_F_iterate_not_selected route c hiLt
  · rcases Finset.mem_image.mp hpOmitted with ⟨i, hi, rfl⟩
    have hi' := (mem_chainMarkedRow_omitted_iff route c i).1 hi
    constructor
    · change fBlock
          ((F^[i.val]) (chainGapRow route c).start) ∈
          touchedBlocks route
      rw [fBlock_F_iterate]
      exact Finset.mem_image.mpr
        ⟨(chainGapRow route c).start,
          chainGapRow_start_selected hroute hnormal c, rfl⟩
    · exact hi'.2

theorem mem_chainCountedHoles_block
    (route : List Perm7) (c : ChainStart route)
    {p : Perm7} (hp : p ∈ chainCountedHoles route c) :
    fBlock p = (chainMarkedRow route c).row.block := by
  rw [chainCountedHoles, Finset.mem_union] at hp
  rcases hp with hpCut | hpOmitted
  · rcases Finset.mem_image.mp hpCut with ⟨i, _hi, rfl⟩
    rw [fBlock_F_iterate, chainMarkedRow_row]
    exact (gapComplementRow_block
      (gapFirstHole route c) (gapLenFin route c)).symm
  · rcases Finset.mem_image.mp hpOmitted with ⟨i, _hi, rfl⟩
    rw [fBlock_F_iterate]
    rfl

@[simp] theorem RetainedArcSystem.toPrepared_flatten
    {route : List Perm7} {hroute : IsHamiltonianRoute route}
    {k τ : ℕ} (hnormal : IsNormalizedRoute route)
    (sys : RetainedArcSystem route hroute k τ) :
    (sys.toPrepared hnormal).trails.flatten =
      sys.trails.flatten.map (markedRowOfArc route hroute) := by
  simp [RetainedArcSystem.toPrepared]

theorem retained_arc_rows_pairwise_block_ne
    {route : List Perm7} {hroute : IsHamiltonianRoute route}
    {k τ : ℕ} (hnormal : IsNormalizedRoute route)
    (sys : RetainedArcSystem route hroute k τ) :
    sys.trails.flatten.Pairwise fun arc₁ arc₂ =>
      (markedRowOfArc route hroute arc₁).row.block ≠
        (markedRowOfArc route hroute arc₂).row.block := by
  have hdisjoint := (sys.toPrepared hnormal).disjoint
  rw [RetainedArcSystem.toPrepared_flatten,
    List.pairwise_map] at hdisjoint
  apply hdisjoint.imp
  intro _arc₁ _arc₂ h
  exact h.1

theorem retained_arcs_nodup
    {route : List Perm7} {hroute : IsHamiltonianRoute route}
    {k τ : ℕ} (hnormal : IsNormalizedRoute route)
    (sys : RetainedArcSystem route hroute k τ) :
    sys.trails.flatten.Nodup := by
  apply (retained_arc_rows_pairwise_block_ne hnormal sys).imp
  intro arc₁ arc₂ hblocks harcs
  subst arc₂
  exact hblocks rfl

private theorem pairwise_symmetric_rel_of_mem
    {α : Type*} {R : α → α → Prop} {l : List α}
    (hsymm : Symmetric R) (hpair : l.Pairwise R)
    {a b : α} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    R a b := by
  obtain ⟨i, hi, hia⟩ := List.getElem_of_mem ha
  obtain ⟨j, hj, hjb⟩ := List.getElem_of_mem hb
  by_cases hij : i < j
  · simpa [hia, hjb] using
      (List.pairwise_iff_getElem.mp hpair i j hi hj hij)
  · have hji : j < i := by
      have hne : i ≠ j := by
        intro heq
        subst j
        apply hab
        exact hia.symm.trans hjb
      omega
    apply hsymm
    simpa [hia, hjb] using
      (List.pairwise_iff_getElem.mp hpair j i hj hi hji)

theorem retained_counted_holes_pairwise_disjoint
    {route : List Perm7} {hroute : IsHamiltonianRoute route}
    {k τ : ℕ} (hnormal : IsNormalizedRoute route)
    (sys : RetainedArcSystem route hroute k τ) :
    Set.PairwiseDisjoint
      ((sys.trails.flatten.toFinset : Finset
        (List (ChainStart route))) : Set (List (ChainStart route)))
      (fun arc =>
        chainCountedHoles route (arcLast route hroute arc)) := by
  intro arc₁ harc₁ arc₂ harc₂ hne
  have hblockNe :=
    pairwise_symmetric_rel_of_mem (R := fun a b =>
      (markedRowOfArc route hroute a).row.block ≠
        (markedRowOfArc route hroute b).row.block)
      (fun _ _ h => Ne.symm h)
      (retained_arc_rows_pairwise_block_ne hnormal sys)
      (by simpa using harc₁) (by simpa using harc₂) hne
  change Disjoint
    (chainCountedHoles route (arcLast route hroute arc₁))
    (chainCountedHoles route (arcLast route hroute arc₂))
  rw [Finset.disjoint_left]
  intro p hp₁ hp₂
  apply hblockNe
  exact
    (mem_chainCountedHoles_block route
      (arcLast route hroute arc₁) hp₁).symm.trans
      (mem_chainCountedHoles_block route
        (arcLast route hroute arc₂) hp₂)

theorem retained_arc_totalCharge_le
    {route : List Perm7} (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (z : RouteStructuralCounts route hroute)
    {τ : ℕ}
    (sys : RetainedArcSystem route hroute z.k τ) :
    (sys.toPrepared hnormal).totalCharge ≤ 6 * z.m - z.r := by
  let arcs := sys.trails.flatten
  let counted : List (ChainStart route) → Finset Perm7 :=
    fun arc => chainCountedHoles route (arcLast route hroute arc)
  have hpair :
      Set.PairwiseDisjoint
        ((arcs.toFinset : Finset (List (ChainStart route))) :
          Set (List (ChainStart route))) counted := by
    exact retained_counted_holes_pairwise_disjoint hnormal sys
  have hsubset :
      arcs.toFinset.biUnion counted ⊆ touchedHoleStates route := by
    intro p hp
    rcases Finset.mem_biUnion.mp hp with ⟨arc, harc, hpArc⟩
    exact chainCountedHoles_subset_touchedHoleStates
      hroute hnormal (arcLast route hroute arc) hpArc
  have hcardLe :=
    Finset.card_le_card hsubset
  calc
    (sys.toPrepared hnormal).totalCharge =
        (arcs.map fun arc =>
          (chainMarkedRow route
            (arcLast route hroute arc)).charge).sum := by
      rw [PreparedCoarsening.totalCharge,
        RetainedArcSystem.toPrepared_flatten,
        List.map_map]
      rfl
    _ = (arcs.map fun arc => (counted arc).card).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro arc _harc
      exact (chainCountedHoles_card route
        (arcLast route hroute arc)).symm
    _ = ∑ arc ∈ arcs.toFinset, (counted arc).card := by
      exact (List.sum_toFinset
        (fun arc => (counted arc).card)
        (retained_arcs_nodup hnormal sys)).symm
    _ = (arcs.toFinset.biUnion counted).card := by
      exact (Finset.card_biUnion hpair).symm
    _ ≤ (touchedHoleStates route).card := hcardLe
    _ = Fintype.card (TouchedHole route) :=
      touchedHoleStates_card route
    _ = 6 * z.m - z.r := structural_touchedHole_card z

/-! ## Omission-run ownership and the hidden-chain bound -/

theorem F_apply_iterate_five (p : Perm7) :
    F ((F^[5]) p) = p := by
  native_decide +revert

theorem F_iterate_five_iterate_of_pos
    (p : Perm7) (i : Fin 6) (hi : 0 < i.val) :
    (F^[5]) ((F^[i.val]) p) = (F^[i.val - 1]) p := by
  native_decide +revert

/-- A cyclic run of holes is identified by its first hole: that state is
unselected and its `F`-predecessor is selected. -/
abbrev HoleRunStart (route : List Perm7) :=
  {p : Perm7 //
    p ∉ runStartSet route ∧ (F^[5]) p ∈ runStartSet route}

def holeRunPredecessor (route : List Perm7)
    (h : HoleRunStart route) : RunStart route :=
  ⟨(F^[5]) h.1, h.2.2⟩

noncomputable def holeRunSource (route : List Perm7)
    (h : HoleRunStart route) : RunStart route :=
  (runStartPerm route).symm (holeRunPredecessor route h)

noncomputable def holeOwnerChain
    {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (h : HoleRunStart route) : ChainStart route :=
  Classical.choose
    (chains_partition_runStarts hroute hnormal
      (holeRunSource route h))

theorem holeRunSource_mem_owner
    {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (h : HoleRunStart route) :
    holeRunSource route h ∈
      chainRunStarts route (holeOwnerChain hroute hnormal h) :=
  (Classical.choose_spec
    (chains_partition_runStarts hroute hnormal
      (holeRunSource route h))).1

theorem touchedTPerm_holeRunSource_val
    (route : List Perm7) (h : HoleRunStart route) :
    (touchedTPerm route
      (runStartTouchedState route (holeRunSource route h))).1 = h.1 := by
  rw [touchedTPerm_runStartTouchedState_val]
  change F
      (runStartPerm route
        ((runStartPerm route).symm (holeRunPredecessor route h))).1 =
    h.1
  rw [(runStartPerm route).apply_symm_apply]
  exact F_apply_iterate_five h.1

private theorem eq_getLast_of_mem_of_no_successor
    {α : Type*} {R : α → α → Prop}
    {l : List α} (hne : l ≠ []) (hchain : l.IsChain R)
    {s : α} (hs : s ∈ l) (hterminal : ∀ t, ¬ R s t) :
    s = l.getLast hne := by
  obtain ⟨i, hi, his⟩ := List.getElem_of_mem hs
  have hiLast : i = l.length - 1 := by
    by_contra hneLast
    have hiSucc : i + 1 < l.length := by omega
    have hrel :=
      List.isChain_iff_getElem.mp hchain i hiSucc
    apply hterminal l[i + 1]
    simpa [his] using hrel
  calc
    s = l[i] := his.symm
    _ = l[l.length - 1] := by
      congr 1
    _ = l.getLast hne := (List.getLast_eq_getElem hne).symm

theorem holeRunSource_eq_chainLast
    {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (h : HoleRunStart route) :
    holeRunSource route h =
      chainLast route (holeOwnerChain hroute hnormal h) := by
  apply eq_getLast_of_mem_of_no_successor
    (chainRunStarts_ne_nil route (holeOwnerChain hroute hnormal h))
    (chainRunStarts_isChain route (holeOwnerChain hroute hnormal h))
    (holeRunSource_mem_owner hroute hnormal h)
  intro t hstep
  apply h.2.1
  have hval := congrArg (fun p : TouchedState route => p.1) hstep.1
  change (touchedTPerm route
      (runStartTouchedState route (holeRunSource route h))).1 =
    t.1 at hval
  rw [touchedTPerm_holeRunSource_val] at hval
  rw [hval]
  exact t.2

theorem holeOwnerChain_gapFirstHole
    {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (h : HoleRunStart route) :
    gapFirstHole route (holeOwnerChain hroute hnormal h) = h.1 := by
  rw [gapFirstHole_eq_F_A,
    ← holeRunSource_eq_chainLast hroute hnormal h]
  simpa only [touchedTPerm_runStartTouchedState_val] using
    touchedTPerm_holeRunSource_val route h

theorem holeOwnerChain_gapLen_pos
    {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (h : HoleRunStart route) :
    0 < gapLen route (holeOwnerChain hroute hnormal h) := by
  by_contra hnot
  have hzero :
      gapLen route (holeOwnerChain hroute hnormal h) = 0 := by omega
  have hselected :=
    gapLen_spec route (holeOwnerChain hroute hnormal h)
  rw [hzero] at hselected
  change gapFirstHole route
      (holeOwnerChain hroute hnormal h) ∈ runStartSet route at hselected
  rw [holeOwnerChain_gapFirstHole hroute hnormal h] at hselected
  exact h.2.1 hselected

theorem holeOwnerChain_injective
    {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route) :
    Function.Injective (holeOwnerChain hroute hnormal) := by
  intro h h' howner
  apply Subtype.ext
  calc
    h.1 = gapFirstHole route
        (holeOwnerChain hroute hnormal h) :=
      (holeOwnerChain_gapFirstHole hroute hnormal h).symm
    _ = gapFirstHole route
        (holeOwnerChain hroute hnormal h') := by rw [howner]
    _ = h'.1 := holeOwnerChain_gapFirstHole hroute hnormal h'

noncomputable def chainOmissionStartIndices
    (route : List Perm7) (c : ChainStart route) : Finset (Fin 6) :=
  (chainMarkedRow route c).omitted.filter fun i =>
    ¬ ∃ j ∈ (chainMarkedRow route c).omitted,
      j.val + 1 = i.val

theorem chainOmissionStartIndices_card
    (route : List Perm7) (c : ChainStart route) :
    (chainOmissionStartIndices route c).card =
      (chainMarkedRow route c).omissionRuns := by
  rfl

theorem omission_start_index_pos
    {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (c : ChainStart route) {i : Fin 6}
    (hi : i ∈ chainOmissionStartIndices route c) :
    0 < i.val := by
  have hiOmitted := (Finset.mem_filter.mp hi).1
  exact (chainMarkedRow_interior hroute hnormal c i hiOmitted).1

theorem omission_start_predecessor_selected
    {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (c : ChainStart route) {i : Fin 6}
    (hi : i ∈ chainOmissionStartIndices route c) :
    (F^[i.val - 1]) (chainGapRow route c).start ∈
      runStartSet route := by
  have hiOmitted := (Finset.mem_filter.mp hi).1
  have hiFirst := (Finset.mem_filter.mp hi).2
  have hiData :=
    (mem_chainMarkedRow_omitted_iff route c i).1 hiOmitted
  have hiPos :=
    (chainMarkedRow_interior hroute hnormal c i hiOmitted).1
  have hpredFive : i.val - 1 < 6 := by omega
  let j : Fin 6 := ⟨i.val - 1, hpredFive⟩
  have hjLen : j.val < (chainGapRow route c).length := by
    dsimp [j]
    omega
  by_contra hjNotSelected
  have hjOmitted : j ∈ (chainMarkedRow route c).omitted := by
    exact (mem_chainMarkedRow_omitted_iff route c j).2
      ⟨hjLen, hjNotSelected⟩
  apply hiFirst
  exact ⟨j, hjOmitted, by
    dsimp [j]
    omega⟩

noncomputable def omissionHoleRunStart
    {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (c : ChainStart route)
    (i : {i : Fin 6 // i ∈ chainOmissionStartIndices route c}) :
    HoleRunStart route :=
  ⟨(F^[i.1.val]) (chainGapRow route c).start,
    (mem_chainMarkedRow_omitted_iff route c i.1).1
      (Finset.mem_filter.mp i.2).1 |>.2,
    by
      rw [F_iterate_five_iterate_of_pos
        (chainGapRow route c).start i.1
          (omission_start_index_pos hroute hnormal c i.2)]
      exact omission_start_predecessor_selected
        hroute hnormal c i.2⟩

theorem omissionHoleRunStart_injective
    {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (c : ChainStart route) :
    Function.Injective (omissionHoleRunStart hroute hnormal c) := by
  intro i j hij
  have hval := congrArg
    (fun h : HoleRunStart route => h.1) hij
  change (F^[i.1.val]) (chainGapRow route c).start =
    (F^[j.1.val]) (chainGapRow route c).start at hval
  have hindex :
      i.1 = j.1 :=
    F_iterates_fin_six_injective
      (chainGapRow route c).start hval
  exact Subtype.ext hindex

noncomputable def chainOmissionRunStarts
    {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (c : ChainStart route) : Finset (HoleRunStart route) :=
  (Finset.univ :
    Finset {i : Fin 6 // i ∈ chainOmissionStartIndices route c}).image
      (omissionHoleRunStart hroute hnormal c)

theorem chainOmissionRunStarts_card
    {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (c : ChainStart route) :
    (chainOmissionRunStarts hroute hnormal c).card =
      (chainMarkedRow route c).omissionRuns := by
  rw [chainOmissionRunStarts,
    Finset.card_image_of_injective _
      (omissionHoleRunStart_injective hroute hnormal c),
    Finset.card_univ, Fintype.card_coe,
    chainOmissionStartIndices_card]

theorem mem_chainOmissionRunStarts_val_mem_omitted
    {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (c : ChainStart route) {h : HoleRunStart route}
    (hh : h ∈ chainOmissionRunStarts hroute hnormal c) :
    h.1 ∈ chainOmittedHoles route c := by
  rcases Finset.mem_image.mp hh with ⟨i, _hi, rfl⟩
  apply Finset.mem_image.mpr
  exact ⟨i.1, (Finset.mem_filter.mp i.2).1, rfl⟩

theorem mem_chainOmissionRunStarts_block
    {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (c : ChainStart route) {h : HoleRunStart route}
    (hh : h ∈ chainOmissionRunStarts hroute hnormal c) :
    fBlock h.1 = (chainMarkedRow route c).row.block := by
  have hmem :=
    mem_chainOmissionRunStarts_val_mem_omitted
      hroute hnormal c hh
  rcases Finset.mem_image.mp hmem with ⟨i, _hi, hip⟩
  rw [← hip, fBlock_F_iterate]
  rfl

theorem holeOwner_ne_of_mem_chainOmissionRunStarts
    {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (c : ChainStart route) {h : HoleRunStart route}
    (hh : h ∈ chainOmissionRunStarts hroute hnormal c) :
    holeOwnerChain hroute hnormal h ≠ c := by
  intro howner
  have hpos := holeOwnerChain_gapLen_pos hroute hnormal h
  have hzeroIndex :
      (0 : Fin 6) ∈
        chainCutIndices route (holeOwnerChain hroute hnormal h) := by
    simp [chainCutIndices, hpos]
  have hhCut :
      h.1 ∈ chainCutHoles route
        (holeOwnerChain hroute hnormal h) := by
    apply Finset.mem_image.mpr
    exact ⟨0, hzeroIndex,
      by simpa using
        (holeOwnerChain_gapFirstHole hroute hnormal h)⟩
  rw [howner] at hhCut
  have hhOmitted :=
    mem_chainOmissionRunStarts_val_mem_omitted
      hroute hnormal c hh
  exact (Finset.disjoint_left.mp
    (chainCutHoles_disjoint_chainOmittedHoles route c))
      hhCut hhOmitted

noncomputable def retainedCutChains
    {route : List Perm7} {hroute : IsHamiltonianRoute route}
    {k τ : ℕ} (sys : RetainedArcSystem route hroute k τ) :
    Finset (ChainStart route) :=
  sys.trails.flatten.toFinset.image (arcLast route hroute)

theorem retained_arcLast_injective_on
    {route : List Perm7} {hroute : IsHamiltonianRoute route}
    {k τ : ℕ} (hnormal : IsNormalizedRoute route)
    (sys : RetainedArcSystem route hroute k τ)
    {arc₁ arc₂ : List (ChainStart route)}
    (harc₁ : arc₁ ∈ sys.trails.flatten)
    (harc₂ : arc₂ ∈ sys.trails.flatten)
    (hlast :
      arcLast route hroute arc₁ = arcLast route hroute arc₂) :
    arc₁ = arc₂ := by
  by_contra hne
  have hblockNe :=
    pairwise_symmetric_rel_of_mem (R := fun a b =>
      (markedRowOfArc route hroute a).row.block ≠
        (markedRowOfArc route hroute b).row.block)
      (fun _ _ h => Ne.symm h)
      (retained_arc_rows_pairwise_block_ne hnormal sys)
      harc₁ harc₂ hne
  apply hblockNe
  simp [markedRowOfArc, hlast]

theorem retainedCutChains_card
    {route : List Perm7} {hroute : IsHamiltonianRoute route}
    {k τ : ℕ} (hnormal : IsNormalizedRoute route)
    (sys : RetainedArcSystem route hroute k τ) :
    (retainedCutChains sys).card = k := by
  rw [retainedCutChains, Finset.card_image_iff.mpr]
  · rw [List.toFinset_card_of_nodup
      (retained_arcs_nodup hnormal sys),
      sys.arc_count]
  · intro arc₁ harc₁ arc₂ harc₂ hlast
    apply retained_arcLast_injective_on hnormal sys
    · simpa using harc₁
    · simpa using harc₂
    · exact hlast

noncomputable def hiddenChains
    {route : List Perm7} {hroute : IsHamiltonianRoute route}
    {k τ : ℕ} (sys : RetainedArcSystem route hroute k τ) :
    Finset (ChainStart route) :=
  Finset.univ \ retainedCutChains sys

theorem hiddenChains_card
    {route : List Perm7} {hroute : IsHamiltonianRoute route}
    {τ : ℕ} (hnormal : IsNormalizedRoute route)
    (z : RouteStructuralCounts route hroute)
    (sys : RetainedArcSystem route hroute z.k τ) :
    (hiddenChains sys).card = z.b := by
  rw [hiddenChains, Finset.card_sdiff]
  simp only [Finset.inter_univ, Finset.card_univ]
  rw [retainedCutChains_card hnormal sys,
    structural_hidden_chain_count z]

noncomputable def chainRepresentedGaps
    {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (c : ChainStart route) : Finset (ChainStart route) :=
  (chainOmissionRunStarts hroute hnormal c).image
    (holeOwnerChain hroute hnormal)

theorem chainRepresentedGaps_card
    {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (c : ChainStart route) :
    (chainRepresentedGaps hroute hnormal c).card =
      (chainMarkedRow route c).omissionRuns := by
  rw [chainRepresentedGaps,
    Finset.card_image_of_injective _
      (holeOwnerChain_injective hroute hnormal),
    chainOmissionRunStarts_card]

theorem retained_represented_gaps_pairwise_disjoint
    {route : List Perm7} {hroute : IsHamiltonianRoute route}
    {k τ : ℕ} (hnormal : IsNormalizedRoute route)
    (sys : RetainedArcSystem route hroute k τ) :
    Set.PairwiseDisjoint
      ((sys.trails.flatten.toFinset : Finset
        (List (ChainStart route))) : Set (List (ChainStart route)))
      (fun arc => chainRepresentedGaps hroute hnormal
        (arcLast route hroute arc)) := by
  intro arc₁ harc₁ arc₂ harc₂ hne
  have hblockNe :=
    pairwise_symmetric_rel_of_mem (R := fun a b =>
      (markedRowOfArc route hroute a).row.block ≠
        (markedRowOfArc route hroute b).row.block)
      (fun _ _ h => Ne.symm h)
      (retained_arc_rows_pairwise_block_ne hnormal sys)
      (by simpa using harc₁) (by simpa using harc₂) hne
  change Disjoint
    (chainRepresentedGaps hroute hnormal
      (arcLast route hroute arc₁))
    (chainRepresentedGaps hroute hnormal
      (arcLast route hroute arc₂))
  rw [Finset.disjoint_left]
  intro c hc₁ hc₂
  rcases Finset.mem_image.mp hc₁ with ⟨g₁, hg₁, hg₁c⟩
  rcases Finset.mem_image.mp hc₂ with ⟨g₂, hg₂, hg₂c⟩
  have hg : g₁ = g₂ := by
    apply holeOwnerChain_injective hroute hnormal
    exact hg₁c.trans hg₂c.symm
  subst g₂
  apply hblockNe
  exact
    (mem_chainOmissionRunStarts_block hroute hnormal
      (arcLast route hroute arc₁) hg₁).symm.trans
      (mem_chainOmissionRunStarts_block hroute hnormal
        (arcLast route hroute arc₂) hg₂)

theorem chainMarkedRow_block_eq_gapFirstHole
    (route : List Perm7) (c : ChainStart route) :
    (chainMarkedRow route c).row.block =
      fBlock (gapFirstHole route c) := by
  rw [chainMarkedRow_row]
  exact gapComplementRow_block
    (gapFirstHole route c) (gapLenFin route c)

theorem retained_represented_gaps_subset_hidden
    {route : List Perm7} {hroute : IsHamiltonianRoute route}
    {k τ : ℕ} (hnormal : IsNormalizedRoute route)
    (sys : RetainedArcSystem route hroute k τ)
    {arc : List (ChainStart route)}
    (harc : arc ∈ sys.trails.flatten) :
    chainRepresentedGaps hroute hnormal
        (arcLast route hroute arc) ⊆ hiddenChains sys := by
  intro c hc
  rw [hiddenChains, Finset.mem_sdiff]
  constructor
  · exact Finset.mem_univ c
  · intro hcCut
    rcases Finset.mem_image.mp hc with ⟨g, hg, hgc⟩
    rcases Finset.mem_image.mp hcCut with
      ⟨arc', harc', harc'c⟩
    have harc'Mem : arc' ∈ sys.trails.flatten := by
      simpa using harc'
    have hblocks :
        (markedRowOfArc route hroute arc).row.block =
          (markedRowOfArc route hroute arc').row.block := by
      calc
        (markedRowOfArc route hroute arc).row.block =
            fBlock g.1 :=
          (mem_chainOmissionRunStarts_block hroute hnormal
            (arcLast route hroute arc) hg).symm
        _ = fBlock (gapFirstHole route
              (holeOwnerChain hroute hnormal g)) := by
            rw [holeOwnerChain_gapFirstHole hroute hnormal g]
        _ = fBlock (gapFirstHole route
              (arcLast route hroute arc')) := by
            rw [hgc, harc'c]
        _ = (markedRowOfArc route hroute arc').row.block := by
          exact (chainMarkedRow_block_eq_gapFirstHole route
            (arcLast route hroute arc')).symm
    have harcs : arc = arc' := by
      by_contra hne
      have hblockNe :=
        pairwise_symmetric_rel_of_mem (R := fun a b =>
          (markedRowOfArc route hroute a).row.block ≠
            (markedRowOfArc route hroute b).row.block)
          (fun _ _ h => Ne.symm h)
          (retained_arc_rows_pairwise_block_ne hnormal sys)
          harc harc'Mem hne
      exact hblockNe hblocks
    subst arc'
    apply holeOwner_ne_of_mem_chainOmissionRunStarts
      hroute hnormal (arcLast route hroute arc) hg
    exact hgc.trans harc'c.symm

theorem retained_arc_totalRuns_le
    {route : List Perm7} (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (z : RouteStructuralCounts route hroute)
    {τ : ℕ}
    (sys : RetainedArcSystem route hroute z.k τ) :
    (sys.toPrepared hnormal).totalRuns ≤ z.b := by
  let arcs := sys.trails.flatten
  let represented : List (ChainStart route) →
      Finset (ChainStart route) :=
    fun arc => chainRepresentedGaps hroute hnormal
      (arcLast route hroute arc)
  have hpair :
      Set.PairwiseDisjoint
        ((arcs.toFinset : Finset (List (ChainStart route))) :
          Set (List (ChainStart route))) represented := by
    exact retained_represented_gaps_pairwise_disjoint hnormal sys
  have hsubset :
      arcs.toFinset.biUnion represented ⊆ hiddenChains sys := by
    intro c hc
    rcases Finset.mem_biUnion.mp hc with ⟨arc, harc, hcArc⟩
    have harcArcs : arc ∈ arcs := by
      simpa only [List.mem_toFinset] using harc
    have harcMem : arc ∈ sys.trails.flatten := by
      exact harcArcs
    exact retained_represented_gaps_subset_hidden hnormal sys
      harcMem hcArc
  have hcardLe := Finset.card_le_card hsubset
  calc
    (sys.toPrepared hnormal).totalRuns =
        (arcs.map fun arc =>
          (chainMarkedRow route
            (arcLast route hroute arc)).omissionRuns).sum := by
      rw [PreparedCoarsening.totalRuns,
        RetainedArcSystem.toPrepared_flatten,
        List.map_map]
      rfl
    _ = (arcs.map fun arc => (represented arc).card).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro arc _harc
      exact (chainRepresentedGaps_card hroute hnormal
        (arcLast route hroute arc)).symm
    _ = ∑ arc ∈ arcs.toFinset, (represented arc).card := by
      exact (List.sum_toFinset
        (fun arc => (represented arc).card)
        (retained_arcs_nodup hnormal sys)).symm
    _ = (arcs.toFinset.biUnion represented).card := by
      exact (Finset.card_biUnion hpair).symm
    _ ≤ (hiddenChains sys).card := hcardLe
    _ = z.b := hiddenChains_card hnormal z sys

/-! ## The payload blocks and visibility cover -/

noncomputable def retainedRowBlocks
    {route : List Perm7} {hroute : IsHamiltonianRoute route}
    {k τ : ℕ} (sys : RetainedArcSystem route hroute k τ) :
    Finset (Finset Perm7) :=
  sys.trails.flatten.toFinset.image fun arc =>
    (markedRowOfArc route hroute arc).row.block

theorem retained_rowBlock_injective_on
    {route : List Perm7} {hroute : IsHamiltonianRoute route}
    {k τ : ℕ} (hnormal : IsNormalizedRoute route)
    (sys : RetainedArcSystem route hroute k τ)
    {arc₁ arc₂ : List (ChainStart route)}
    (harc₁ : arc₁ ∈ sys.trails.flatten)
    (harc₂ : arc₂ ∈ sys.trails.flatten)
    (hblocks :
      (markedRowOfArc route hroute arc₁).row.block =
        (markedRowOfArc route hroute arc₂).row.block) :
    arc₁ = arc₂ := by
  by_contra hne
  exact
    (pairwise_symmetric_rel_of_mem (R := fun a b =>
      (markedRowOfArc route hroute a).row.block ≠
        (markedRowOfArc route hroute b).row.block)
      (fun _ _ h => Ne.symm h)
      (retained_arc_rows_pairwise_block_ne hnormal sys)
      harc₁ harc₂ hne) hblocks

theorem retainedRowBlocks_card
    {route : List Perm7} {hroute : IsHamiltonianRoute route}
    {k τ : ℕ} (hnormal : IsNormalizedRoute route)
    (sys : RetainedArcSystem route hroute k τ) :
    (retainedRowBlocks sys).card = k := by
  rw [retainedRowBlocks, Finset.card_image_iff.mpr]
  · rw [List.toFinset_card_of_nodup
      (retained_arcs_nodup hnormal sys),
      sys.arc_count]
  · intro arc₁ harc₁ arc₂ harc₂ hblocks
    apply retained_rowBlock_injective_on hnormal sys
    · simpa using harc₁
    · simpa using harc₂
    · exact hblocks

theorem markedRowOfArc_block_mem_touchedBlocks
    {route : List Perm7} {hroute : IsHamiltonianRoute route}
    {k τ : ℕ} (hnormal : IsNormalizedRoute route)
    (sys : RetainedArcSystem route hroute k τ)
    {arc : List (ChainStart route)}
    (_harc : arc ∈ sys.trails.flatten) :
    (markedRowOfArc route hroute arc).row.block ∈
      touchedBlocks route := by
  apply Finset.mem_image.mpr
  refine ⟨(chainGapRow route
    (arcLast route hroute arc)).start, ?_, ?_⟩
  · exact chainGapRow_start_selected hroute hnormal _
  · rfl

theorem retainedRowBlocks_subset_touchedBlocks
    {route : List Perm7} {hroute : IsHamiltonianRoute route}
    {k τ : ℕ} (hnormal : IsNormalizedRoute route)
    (sys : RetainedArcSystem route hroute k τ) :
    retainedRowBlocks sys ⊆ touchedBlocks route := by
  intro B hB
  rcases Finset.mem_image.mp hB with ⟨arc, harc, rfl⟩
  exact markedRowOfArc_block_mem_touchedBlocks hnormal sys
    (by simpa using harc)

noncomputable def retainedPayloadBlocks
    {route : List Perm7} {hroute : IsHamiltonianRoute route}
    {k τ : ℕ} (sys : RetainedArcSystem route hroute k τ) :
    Finset (Finset Perm7) :=
  touchedBlocks route \ retainedRowBlocks sys

theorem retainedPayloadBlocks_card
    {route : List Perm7} {hroute : IsHamiltonianRoute route}
    {τ : ℕ} (hnormal : IsNormalizedRoute route)
    (z : RouteStructuralCounts route hroute)
    (sys : RetainedArcSystem route hroute z.k τ) :
    (retainedPayloadBlocks sys).card = z.r - z.a := by
  rw [retainedPayloadBlocks, Finset.card_sdiff]
  have hsubset :=
    retainedRowBlocks_subset_touchedBlocks hnormal sys
  rw [Finset.inter_eq_left.mpr hsubset,
    retainedRowBlocks_card hnormal sys,
    structural_payload_block_count z]

theorem selected_mem_chainGapRow_range
    {route : List Perm7}
    (c : ChainStart route) {p : Perm7}
    (hpSelected : p ∈ runStartSet route)
    (hpBlock :
      fBlock p = (chainMarkedRow route c).row.block) :
    ∃ i < (chainGapRow route c).length,
      (F^[i]) (chainGapRow route c).start = p := by
  have hpMem : p ∈ fBlock (gapFirstHole route c) := by
    rw [← chainMarkedRow_block_eq_gapFirstHole route c,
      ← hpBlock]
    exact self_mem_fBlock p
  rcases Finset.mem_image.mp hpMem with ⟨n, hnFive, hnp⟩
  have hnLt : n < 6 := by simpa [fBlock, finiteOrbit] using hnFive
  have hgapLe : gapLen route c ≤ n := by
    by_contra hnot
    have hnGap : n < gapLen route c := Nat.lt_of_not_ge hnot
    exact (gap_F_iterate_not_selected route c hnGap)
      (hnp ▸ hpSelected)
  let i := n - gapLen route c
  have hiLen : i < (chainGapRow route c).length := by
    rw [chainGapRow, gapComplementRow_length]
    change i < 6 - gapLen route c
    dsimp [i]
    omega
  refine ⟨i, hiLen, ?_⟩
  calc
    (F^[i]) (chainGapRow route c).start =
        (F^[i]) ((F^[gapLen route c])
          (gapFirstHole route c)) := rfl
    _ = (F^[i + gapLen route c])
          (gapFirstHole route c) := by
      rw [Function.iterate_add_apply]
    _ = (F^[n]) (gapFirstHole route c) := by
      congr 2
      dsimp [i]
      omega
    _ = p := hnp

theorem selected_class_mem_chainMarkedRow_visibleMask
    {route : List Perm7}
    (c : ChainStart route) {p : Perm7}
    (hpSelected : p ∈ runStartSet route)
    (hpBlock :
      fBlock p = (chainMarkedRow route c).row.block) :
    rClass p ∈ (chainMarkedRow route c).visibleMask := by
  obtain ⟨i, hiLen, hip⟩ :=
    selected_mem_chainGapRow_range c hpSelected hpBlock
  apply Finset.mem_image.mpr
  refine ⟨i, Finset.mem_filter.mpr ⟨
    Finset.mem_range.mpr hiLen, ?_⟩, ?_⟩
  · intro j hj hji
    have hjHole :=
      (mem_chainMarkedRow_omitted_iff route c j).1 hj |>.2
    apply hjHole
    rw [hji, hip]
    exact hpSelected
  · change rClass
      ((F^[i]) (chainGapRow route c).start) = rClass p
    rw [hip]

theorem retained_arc_forestPayload
    {route : List Perm7} (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (z : RouteStructuralCounts route hroute)
    {τ : ℕ}
    (sys : RetainedArcSystem route hroute z.k τ) :
    (sys.toPrepared hnormal).ForestPayload (z.r - z.a) := by
  refine ⟨retainedPayloadBlocks sys,
    retainedPayloadBlocks_card hnormal z sys, ?_, ?_, ?_⟩
  · intro B hB
    have hTouched : B ∈ touchedBlocks route := by
      exact (Finset.mem_sdiff.mp hB).1
    rcases Finset.mem_image.mp hTouched with ⟨p, _hp, rfl⟩
    exact Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩
  · intro x hx
    rw [RetainedArcSystem.toPrepared_flatten] at hx
    rcases List.mem_map.mp hx with ⟨arc, harc, rfl⟩
    rw [retainedPayloadBlocks, Finset.mem_sdiff]
    push Not
    intro _hTouched
    apply Finset.mem_image.mpr
    exact ⟨arc, by simpa using harc, rfl⟩
  · intro C hC hinvisible
    rcases Finset.mem_image.mp hC with ⟨q, _hq, rfl⟩
    let RC : RotationClass :=
      ⟨rClass q, Finset.mem_image.mpr
        ⟨q, Finset.mem_univ q, rfl⟩⟩
    obtain ⟨p, hpSelected, hpClass⟩ :=
      rotationClass_meets_runStartSet hroute RC
    have hpTouched : fBlock p ∈ touchedBlocks route :=
      Finset.mem_image.mpr ⟨p, hpSelected, rfl⟩
    have hpRClass : rClass p = rClass q :=
      rClass_eq_of_mem q p hpClass
    by_cases hpRetained : fBlock p ∈ retainedRowBlocks sys
    · rcases Finset.mem_image.mp hpRetained with
        ⟨arc, harc, hblock⟩
      have harcMem : arc ∈ sys.trails.flatten := by
        simpa using harc
      let row := markedRowOfArc route hroute arc
      have hrowMem :
          row ∈ (sys.toPrepared hnormal).trails.flatten := by
        rw [RetainedArcSystem.toPrepared_flatten]
        exact List.mem_map.mpr ⟨arc, harcMem, rfl⟩
      exfalso
      apply (hinvisible row hrowMem)
      change rClass q ∈
        (chainMarkedRow route (arcLast route hroute arc)).visibleMask
      rw [← hpRClass]
      apply selected_class_mem_chainMarkedRow_visibleMask
        (arcLast route hroute arc) hpSelected
      exact hblock.symm
    · refine ⟨fBlock p, ?_, p, self_mem_fBlock p, hpRClass⟩
      exact Finset.mem_sdiff.mpr ⟨hpTouched, hpRetained⟩

/-! ## The zero-hidden-chain equality and final trichotomy -/

/-- A nonempty omission set has at least one run: its least element starts
one. -/
theorem MarkedRow.omissionRuns_pos_of_nonempty
    (x : MarkedRow) (_hinterior : x.OmissionsInterior)
    (hne : x.omitted.Nonempty) :
    0 < x.omissionRuns := by
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image x.omitted (fun i => i.val) hne
  unfold MarkedRow.omissionRuns
  apply Finset.card_pos.mpr
  refine ⟨i, Finset.mem_filter.mpr ⟨hi, ?_⟩⟩
  rintro ⟨j, hj, hji⟩
  have := hmin j hj
  omega

theorem PreparedCoarsening.unmarked_of_totalRuns_eq_zero
    {k τ : ℕ} (prep : PreparedCoarsening k τ)
    (hzero : prep.totalRuns = 0) :
    ∀ x ∈ prep.trails.flatten, x.omitted = ∅ := by
  intro x hx
  have hxRun : x.omissionRuns = 0 := by
    apply (List.sum_eq_zero_iff.mp hzero)
    exact List.mem_map.mpr ⟨x, hx, rfl⟩
  by_contra hne
  have hnonempty : x.omitted.Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hne
  have hpos :=
    MarkedRow.omissionRuns_pos_of_nonempty x
      (prep.interior x hx) hnonempty
  omega

theorem retainedCutChains_eq_univ_of_b_eq_zero
    {route : List Perm7} {hroute : IsHamiltonianRoute route}
    {τ : ℕ} (hnormal : IsNormalizedRoute route)
    (z : RouteStructuralCounts route hroute)
    (sys : RetainedArcSystem route hroute z.k τ)
    (hb : z.b = 0) :
    retainedCutChains sys = Finset.univ := by
  have hhiddenCard := hiddenChains_card hnormal z sys
  rw [hb] at hhiddenCard
  have hhiddenEmpty : hiddenChains sys = ∅ :=
    Finset.card_eq_zero.mp hhiddenCard
  have hdiffEmpty :
      (Finset.univ : Finset (ChainStart route)) \
        retainedCutChains sys = ∅ := by
    simpa [hiddenChains] using hhiddenEmpty
  have hunivSubset :
      (Finset.univ : Finset (ChainStart route)) ⊆
        retainedCutChains sys :=
    Finset.sdiff_eq_empty_iff_subset.mp hdiffEmpty
  exact Finset.eq_univ_iff_forall.mpr fun c =>
    hunivSubset (Finset.mem_univ c)

theorem retained_arcLast_list_nodup
    {route : List Perm7} {hroute : IsHamiltonianRoute route}
    {k τ : ℕ} (hnormal : IsNormalizedRoute route)
    (sys : RetainedArcSystem route hroute k τ) :
    (sys.trails.flatten.map (arcLast route hroute)).Nodup := by
  have harcsNodup := retained_arcs_nodup hnormal sys
  rw [List.nodup_map_iff_inj_on harcsNodup]
  intro arc₁ harc₁ arc₂ harc₂ hlast
  exact retained_arcLast_injective_on hnormal sys
    harc₁ harc₂ hlast

theorem retained_arc_totalCharge_eq_of_b_eq_zero
    {route : List Perm7} (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (z : RouteStructuralCounts route hroute)
    {τ : ℕ}
    (sys : RetainedArcSystem route hroute z.k τ)
    (hb : z.b = 0) :
    (sys.toPrepared hnormal).totalCharge = 6 * z.m - z.r := by
  let arcs := sys.trails.flatten
  have hrunsLe := retained_arc_totalRuns_le hroute hnormal z sys
  have hrunsZero :
      (sys.toPrepared hnormal).totalRuns = 0 := by omega
  have hunmarked :=
    (sys.toPrepared hnormal).unmarked_of_totalRuns_eq_zero hrunsZero
  have harcUnmarked :
      ∀ arc ∈ arcs,
        (chainMarkedRow route
          (arcLast route hroute arc)).omitted = ∅ := by
    intro arc harc
    apply hunmarked
    rw [RetainedArcSystem.toPrepared_flatten]
    exact List.mem_map.mpr ⟨arc, harc, rfl⟩
  have hcutToFinset :
      (arcs.map (arcLast route hroute)).toFinset =
        retainedCutChains sys := by
    apply Finset.ext
    intro c
    constructor
    · intro hc
      rcases List.mem_map.mp (List.mem_toFinset.mp hc) with
        ⟨arc, harc, harcC⟩
      apply Finset.mem_image.mpr
      exact ⟨arc, List.mem_toFinset.mpr harc, harcC⟩
    · intro hc
      rcases Finset.mem_image.mp hc with ⟨arc, harc, harcC⟩
      apply List.mem_toFinset.mpr
      exact List.mem_map.mpr
        ⟨arc, List.mem_toFinset.mp harc, harcC⟩
  have hcutUniv :=
    retainedCutChains_eq_univ_of_b_eq_zero
      hnormal z sys hb
  calc
    (sys.toPrepared hnormal).totalCharge =
        (arcs.map fun arc =>
          (chainMarkedRow route
            (arcLast route hroute arc)).charge).sum := by
      rw [PreparedCoarsening.totalCharge,
        RetainedArcSystem.toPrepared_flatten,
        List.map_map]
      rfl
    _ = (arcs.map fun arc =>
          gapLen route (arcLast route hroute arc)).sum := by
      apply congrArg List.sum
      apply List.map_congr_left
      intro arc harc
      rw [chainMarkedRow_charge_eq,
        harcUnmarked arc harc]
      simp
    _ = ((arcs.map (arcLast route hroute)).map
          (gapLen route)).sum := by
      rw [List.map_map]
      rfl
    _ = ∑ c ∈ (arcs.map
          (arcLast route hroute)).toFinset, gapLen route c := by
      exact (List.sum_toFinset (gapLen route)
        (retained_arcLast_list_nodup hnormal sys)).symm
    _ = ∑ c : ChainStart route, gapLen route c := by
      rw [hcutToFinset, hcutUniv]
    _ = 6 * z.m - z.r :=
      sum_gapLen_eq_structural_holes hroute hnormal z

end Superperm7
