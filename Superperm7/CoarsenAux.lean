/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE); this file is
additionally subject to the upstream MIT notice below.

Adapted from https://github.com/BGray-wrl/superperm6
  file:   formal-verification/Superperm6/CoarsenAux.lean
  commit: d8a932d8f61d80b0bcfc737bd0e235a8300449c4
  upstream copyright: Copyright (c) 2026 Benjamin Grayzel — MIT License (reproduced in NOTICE).
Local modifications (port from six to seven symbols; see docs/PORT_LOG.md): seven-symbol constants; weight bound 5890.
-/
import Superperm7.Coarsen
import Superperm7.Surgery
import Superperm7.CycleLists
import Superperm7.ChainTrails
import Superperm7.Section5Core
import Superperm7.Structural

/-!
# Auxiliary lemmas for the general coarsening bridge

This file contains the route-independent list bookkeeping and the
route-side component/row facts used by `CoarsenBridge.lean`.
-/

namespace Superperm7

open List

set_option maxHeartbeats 2000000

theorem flatten_perm_of_forall₂_perm
    {α : Type*} {parts parts' : List (List α)}
    (h : List.Forall₂ List.Perm parts parts') :
    List.Perm parts.flatten parts'.flatten := by
  induction h with
  | nil => exact List.Perm.refl []
  | cons hhead _htail ih =>
      simpa using hhead.append ih

theorem exists_right_of_forall₂_of_mem
    {α β : Type*} {R : α → β → Prop}
    {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {x : α} (hx : x ∈ xs) :
    ∃ y ∈ ys, R x y := by
  induction h with
  | nil => simp at hx
  | @cons a b as bs hab _htail ih =>
      rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨b, by simp, hab⟩
      · obtain ⟨y, hy, hxy⟩ := ih hx
        exact ⟨y, by simp [hy], hxy⟩

theorem exists_left_of_forall₂_of_mem
    {α β : Type*} {R : α → β → Prop}
    {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {y : β} (hy : y ∈ ys) :
    ∃ x ∈ xs, R x y := by
  induction h with
  | nil => simp at hy
  | @cons a b as bs hab _htail ih =>
      rcases List.mem_cons.mp hy with rfl | hy
      · exact ⟨a, by simp, hab⟩
      · obtain ⟨x, hx, hxy⟩ := ih hy
        exact ⟨x, by simp [hx], hxy⟩

theorem lengths_map_map
    {α β : Type*} (f : α → β) (parts : List (List α)) :
    (parts.map (List.map f)).map List.length =
      parts.map List.length := by
  induction parts with
  | nil => rfl
  | cons part parts ih =>
      simp [ih]

theorem length_le_flatten_length_of_ne_nil
    {α : Type*} {parts : List (List α)}
    (hne : ∀ part ∈ parts, part ≠ []) :
    parts.length ≤ parts.flatten.length := by
  induction parts with
  | nil => simp
  | cons part parts ih =>
      have hpartPos : 0 < part.length :=
        List.length_pos_iff.mpr (hne part (by simp))
      have htail :
          parts.length ≤ parts.flatten.length :=
        ih (fun p hp => hne p (by simp [hp]))
      simp only [List.length_cons, List.flatten_cons, List.length_append]
      omega

/-! ## Quotient components along faces -/

theorem touchedRotationComponent_apply_T
    {route : List Perm7} (hroute : IsHamiltonianRoute route)
    (p : TouchedState route) :
    touchedRotationComponent route hroute (touchedTPerm route p) =
      touchedRotationComponent route hroute p := by
  rw [touchedTPerm, Equiv.Perm.mul_apply,
    touchedRotationComponent_apply_F,
    touchedRotationComponent_apply_A]

theorem touchedRotationComponent_apply_T_pow
    {route : List Perm7} (hroute : IsHamiltonianRoute route)
    (n : ℕ) (p : TouchedState route) :
    touchedRotationComponent route hroute
        ((touchedTPerm route ^ n) p) =
      touchedRotationComponent route hroute p := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply,
        touchedRotationComponent_apply_T, ih]

theorem chainStartComponent_apply_face
    {route : List Perm7} (hroute : IsHamiltonianRoute route)
    (c : ChainStart route) :
    chainStartComponent hroute (chainFaceNext route c) =
      chainStartComponent hroute c := by
  change touchedRotationComponent route hroute
      (chainTouchedState route (chainFaceNext route c)) =
    touchedRotationComponent route hroute (chainTouchedState route c)
  rw [chainFaceNext_apply, chainTouchedState_nextFace]
  exact touchedRotationComponent_apply_T_pow hroute _ _

theorem chainStartComponent_apply_face_pow
    {route : List Perm7} (hroute : IsHamiltonianRoute route)
    (n : ℕ) (c : ChainStart route) :
    chainStartComponent hroute ((chainFaceNext route ^ n) c) =
      chainStartComponent hroute c := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply,
        chainStartComponent_apply_face, ih]

theorem chainStartComponent_eq_of_face_sameCycle
    {route : List Perm7} (hroute : IsHamiltonianRoute route)
    {c d : ChainStart route}
    (hcd : (chainFaceNext route).SameCycle c d) :
    chainStartComponent hroute c = chainStartComponent hroute d := by
  obtain ⟨n, _hnpos, _hnbound, hn⟩ :=
    hcd.exists_pow_eq (chainFaceNext route)
  have hcomp := chainStartComponent_apply_face_pow hroute n c
  rw [hn] at hcomp
  exact hcomp.symm

theorem face_members_same_component
    {route : List Perm7}
    {face : List (ChainStart route)}
    (hface : face ∈ permCycleLists (chainFaceNext route))
    {c d : ChainStart route} (hc : c ∈ face) (hd : d ∈ face)
    (hroute : IsHamiltonianRoute route) :
    chainStartComponent hroute c = chainStartComponent hroute d := by
  rcases List.mem_map.mp hface with ⟨C, _hC, rfl⟩
  apply chainStartComponent_eq_of_face_sameCycle hroute
  apply sameCycle_of_permCycleOf_eq
  exact
    ((mem_permCycleList_iff (chainFaceNext route) C c).1 hc).trans
      ((mem_permCycleList_iff (chainFaceNext route) C d).1 hd).symm

/-! ## Complement-row endpoint and selection facts -/

theorem F_iterate_five_apply_F (p : Perm7) :
    (F^[5]) (F p) = p := by
  native_decide +revert

theorem gapComplementRow_lastState_selected
    (route : List Perm7) (c : ChainStart route) :
    (gapComplementRow
      (gapFirstHole route c) (gapLenFin route c)).lastState ∈
        runStartSet route := by
  rw [gapComplementRow_lastState, gapFirstHole_eq_F_A,
    F_iterate_five_apply_F]
  exact (runStartPerm route (chainLast route c)).2

theorem gapComplementRow_start_selected
    {route : List Perm7} (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route) (c : ChainStart route) :
    (gapComplementRow
      (gapFirstHole route c) (gapLenFin route c)).start ∈
        runStartSet route := by
  rw [gapComplementRow_start_eq_faceNext hroute hnormal c]
  exact chainStartSet_subset_runStartSet route
    (chainFaceNext route c).2

/-! ## The marked row attached to a retained face arc -/

noncomputable def chainGapRow (route : List Perm7)
    (c : ChainStart route) : Row :=
  gapComplementRow (gapFirstHole route c) (gapLenFin route c)

noncomputable def chainMarkedRow (route : List Perm7)
    (c : ChainStart route) : MarkedRow :=
  let row := chainGapRow route c
  { row := row
    omitted := Finset.univ.filter fun i : Fin 6 =>
      i.val < row.length ∧
        (F^[i.val]) row.start ∉ runStartSet route }

@[simp] theorem chainMarkedRow_row (route : List Perm7)
    (c : ChainStart route) :
    (chainMarkedRow route c).row = chainGapRow route c := by
  rfl

theorem mem_chainMarkedRow_omitted_iff
    (route : List Perm7) (c : ChainStart route) (i : Fin 6) :
    i ∈ (chainMarkedRow route c).omitted ↔
      i.val < (chainGapRow route c).length ∧
        (F^[i.val]) (chainGapRow route c).start ∉
          runStartSet route := by
  simp [chainMarkedRow]

theorem Row.length_le_six (row : Row) : row.length ≤ 6 := by
  have := row.lengthCode.isLt
  simp only [Row.length]
  omega

theorem chainGapRow_start_selected
    {route : List Perm7} (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route) (c : ChainStart route) :
    (chainGapRow route c).start ∈ runStartSet route :=
  gapComplementRow_start_selected hroute hnormal c

theorem chainGapRow_start_eq_faceNext
    {route : List Perm7} (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route) (c : ChainStart route) :
    (chainGapRow route c).start = (chainFaceNext route c).1 :=
  gapComplementRow_start_eq_faceNext hroute hnormal c

theorem chainGapRow_lastState_selected
    (route : List Perm7) (c : ChainStart route) :
    (chainGapRow route c).lastState ∈ runStartSet route :=
  gapComplementRow_lastState_selected route c

theorem chainMarkedRow_interior
    {route : List Perm7} (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route) (c : ChainStart route) :
    (chainMarkedRow route c).OmissionsInterior := by
  intro i hi
  change 0 < i.val ∧ i.val + 1 < (chainGapRow route c).length
  have hi' := (mem_chainMarkedRow_omitted_iff route c i).1 hi
  constructor
  · by_contra hnot
    have hiz : i.val = 0 := by omega
    apply hi'.2
    simpa [hiz] using chainGapRow_start_selected hroute hnormal c
  · by_contra hnot
    have hlenLe := (chainGapRow route c).length_le_six
    have hilast : i.val + 1 = (chainGapRow route c).length := by
      omega
    have hicode :
        i.val = (chainGapRow route c).lengthCode.val := by
      simp [Row.length] at hilast
      omega
    apply hi'.2
    have hstate :
        (F^[i.val]) (chainGapRow route c).start =
          (chainGapRow route c).lastState := by
      simp [Row.lastState, hicode]
    rw [hstate]
    exact chainGapRow_lastState_selected route c

theorem chainGapRow_alpha_eq_chainAlpha
    {route : List Perm7} (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route) (c : ChainStart route) :
    alpha (chainGapRow route c).start =
      chainAlpha route (chainFaceNext route c) :=
  gapComplementRow_alpha_eq_chainAlpha hroute hnormal c

theorem chainGapRow_beta_eq_chainBeta
    (route : List Perm7) (c : ChainStart route) :
    (chainGapRow route c).beta = chainBeta route c :=
  gapComplementRow_beta_eq_chainBeta route c

theorem chainMarkedRow_compatible_of_arcCompatible
    {route : List Perm7} (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    {arc₁ arc₂ : List (ChainStart route)}
    (harc₁ : arc₁ ≠ []) (harc₂ : arc₂ ≠ [])
    (hwrap₂ :
      chainFaceNext route (arc₂.getLast harc₂) = arc₂.head harc₂)
    (hcompat :
      ArcCompatible (chainAlpha route) (chainBeta route) arc₁ arc₂) :
    MarkedCompatible
      (chainMarkedRow route (arc₁.getLast harc₁))
      (chainMarkedRow route (arc₂.getLast harc₂)) := by
  have hendpoints :
      chainBeta route (arc₁.getLast harc₁) =
        chainAlpha route (arc₂.head harc₂) :=
    (arcCompatible_iff_getLast_head
      (chainAlpha route) (chainBeta route) harc₁ harc₂).mp hcompat
  unfold MarkedCompatible RowCompatible
  rw [chainMarkedRow_row, chainMarkedRow_row,
    chainGapRow_beta_eq_chainBeta,
    chainGapRow_alpha_eq_chainAlpha hroute hnormal, hwrap₂]
  exact hendpoints

/-! ## Visible states and global component disjointness -/

theorem fBlock_F_iterate (n : ℕ) (p : Perm7) :
    fBlock ((F^[n]) p) = fBlock p := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', fBlock_F, ih]

theorem chainMarkedRow_visible_position_selected
    (route : List Perm7) (c : ChainStart route) (i : ℕ)
    (hi : i < (chainGapRow route c).length)
    (hvisible :
      ∀ j ∈ (chainMarkedRow route c).omitted, j.val ≠ i) :
    (F^[i]) (chainGapRow route c).start ∈ runStartSet route := by
  by_contra hnot
  have hiFive : i < 6 :=
    hi.trans_le (chainGapRow route c).length_le_six
  let j : Fin 6 := ⟨i, hiFive⟩
  have hj : j ∈ (chainMarkedRow route c).omitted := by
    apply (mem_chainMarkedRow_omitted_iff route c j).2
    exact ⟨hi, hnot⟩
  exact hvisible j hj rfl

theorem chainMarkedRow_visibleMask_witness
    {route : List Perm7} (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route) (c : ChainStart route)
    {C : Finset Perm7}
    (hC : C ∈ (chainMarkedRow route c).visibleMask) :
    ∃ s : RunStart route,
      C = rClass s.1 ∧
      (rotationGraph route hroute).connectedComponentMk (startBlock s) =
        chainStartComponent hroute c := by
  rcases Finset.mem_image.mp hC with ⟨i, hi, rfl⟩
  have hiRange := (Finset.mem_filter.mp hi).1
  have hvisible := (Finset.mem_filter.mp hi).2
  have hiLen : i < (chainGapRow route c).length := by
    simpa using hiRange
  have hpSelected :
      (F^[i]) (chainGapRow route c).start ∈ runStartSet route :=
    chainMarkedRow_visible_position_selected route c i hiLen hvisible
  let s : RunStart route :=
    ⟨(F^[i]) (chainGapRow route c).start, hpSelected⟩
  refine ⟨s, rfl, ?_⟩
  have hblock :
      startBlock s =
        startBlock (chainAsRunStart (chainFaceNext route c)) := by
    apply Subtype.ext
    change
      fBlock ((F^[i]) (chainGapRow route c).start) =
        fBlock (chainFaceNext route c).1
    rw [fBlock_F_iterate,
      chainGapRow_start_eq_faceNext hroute hnormal c]
  calc
    (rotationGraph route hroute).connectedComponentMk (startBlock s) =
        (rotationGraph route hroute).connectedComponentMk
          (startBlock (chainAsRunStart (chainFaceNext route c))) := by
      rw [hblock]
    _ = chainStartComponent hroute (chainFaceNext route c) := rfl
    _ = chainStartComponent hroute c :=
      chainStartComponent_apply_face hroute c

theorem chainMarkedRow_block_eq_faceNext_startBlock
    {route : List Perm7} (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route) (c : ChainStart route) :
    (chainMarkedRow route c).row.block =
      (startBlock (chainAsRunStart (chainFaceNext route c))).1 := by
  change fBlock (chainGapRow route c).start =
    fBlock (chainFaceNext route c).1
  rw [chainGapRow_start_eq_faceNext hroute hnormal c]

theorem chainMarkedRows_disjoint_of_component_ne
    {route : List Perm7} (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route) {c d : ChainStart route}
    (hne :
      chainStartComponent hroute c ≠ chainStartComponent hroute d) :
    MarkedDisjoint (chainMarkedRow route c) (chainMarkedRow route d) := by
  have hfaceNe :
      (rotationGraph route hroute).connectedComponentMk
          (startBlock (chainAsRunStart (chainFaceNext route c))) ≠
        (rotationGraph route hroute).connectedComponentMk
          (startBlock (chainAsRunStart (chainFaceNext route d))) := by
    change
      chainStartComponent hroute (chainFaceNext route c) ≠
        chainStartComponent hroute (chainFaceNext route d)
    intro heq
    apply hne
    rw [← chainStartComponent_apply_face hroute c,
      ← chainStartComponent_apply_face hroute d]
    exact heq
  constructor
  · rw [chainMarkedRow_block_eq_faceNext_startBlock hroute hnormal,
      chainMarkedRow_block_eq_faceNext_startBlock hroute hnormal]
    intro heq
    apply selected_blocks_ne_of_component_ne hroute _ _ hfaceNe
    apply Subtype.ext
    exact heq
  · rw [Finset.disjoint_left]
    intro C hCc hCd
    obtain ⟨s, hsC, hsComp⟩ :=
      chainMarkedRow_visibleMask_witness hroute hnormal c hCc
    obtain ⟨t, htC, htComp⟩ :=
      chainMarkedRow_visibleMask_witness hroute hnormal d hCd
    have hstComp :
        (rotationGraph route hroute).connectedComponentMk (startBlock s) ≠
          (rotationGraph route hroute).connectedComponentMk (startBlock t) := by
      rw [hsComp, htComp]
      exact hne
    have hclasses :=
      selected_rotation_classes_disjoint_of_component_ne
        hroute s t hstComp
    have hsMem : s.1 ∈ rClass s.1 := self_mem_rClass s.1
    have htMem : s.1 ∈ rClass t.1 := by
      rw [← htC, hsC]
      exact hsMem
    exact (Finset.disjoint_left.mp hclasses) hsMem htMem

/-! ## Cheap-profile identification and the final trail arithmetic -/

/-- At `n = 7` the structural `p` is the route's actual path count, so the
number of initial chain trails is at most `z.p` with no frontier slack. -/
theorem cheap_profile_for_bridge
    {route : List Perm7} (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (_hweight : routeWeight route ≤ 5890)
    (z : RouteStructuralCounts route hroute) :
    ∃ x : CheapCoverProfile,
      x.r = z.r ∧ x.q = z.q ∧ x.p = z.p ∧
      (routeChainTrails route).length ≤ x.p := by
  have htrail := chainTrails_count hroute hnormal
  refine ⟨⟨z.r, z.q, z.p⟩, rfl, rfl, rfl, ?_⟩
  change (routeChainTrails route).length ≤ z.p
  rw [z.p_route]
  exact htrail

theorem coarsened_trail_budget_arithmetic
    {route : List Perm7} {hroute : IsHamiltonianRoute route}
    (z : RouteStructuralCounts route hroute)
    {p₀ pFinal cT : ℕ}
    (hcLower : z.k ≤ cT) (hcUpper : cT ≤ z.q)
    (hp₀ : p₀ ≤ z.p)
    (hfinal :
      pFinal ≤ p₀ + (z.q - cT) + (cT - z.k)) :
    pFinal ≤ z.eta + 1 + z.b := by
  have hkeq := z.k_eq
  have hqeq := z.q_eq
  have hpeq := z.p_eq
  omega

theorem structural_touchedHole_card
    {route : List Perm7} {hroute : IsHamiltonianRoute route}
    (z : RouteStructuralCounts route hroute) :
    Fintype.card (TouchedHole route) = 6 * z.m - z.r := by
  have hhole := touchedHole_card route
  rw [touchedState_card, ← z.M_route, z.runStart_card] at hhole
  have hM := z.M_eq
  have hr := z.r_le_six_m
  omega

theorem structural_hidden_chain_count
    {route : List Perm7} {hroute : IsHamiltonianRoute route}
    (z : RouteStructuralCounts route hroute) :
    Fintype.card (ChainStart route) - z.k = z.b := by
  rw [chains_card hroute z, z.q_eq]
  omega

theorem structural_payload_block_count
    {route : List Perm7} {hroute : IsHamiltonianRoute route}
    (z : RouteStructuralCounts route hroute) :
    (touchedBlocks route).card - z.k = z.r - z.a := by
  rw [← z.M_route]
  have hM := z.M_eq
  have hk := z.k_eq
  have ha := z.a_le_r
  have hkM := z.k_le_M
  have hrm := z.r_le_six_m
  have hdefect := z.defect_le
  omega

/-! ## Prepared arc and row systems -/

noncomputable def arcHead (route : List Perm7)
    (hroute : IsHamiltonianRoute route)
    (arc : List (ChainStart route)) : ChainStart route :=
  arc.headD (baseChainStart route hroute)

noncomputable def arcLast (route : List Perm7)
    (hroute : IsHamiltonianRoute route)
    (arc : List (ChainStart route)) : ChainStart route :=
  arc.getLastD (baseChainStart route hroute)

theorem arcHead_eq_head
    {route : List Perm7} (hroute : IsHamiltonianRoute route)
    {arc : List (ChainStart route)} (hne : arc ≠ []) :
    arcHead route hroute arc = arc.head hne := by
  obtain ⟨a, tail, rfl⟩ := List.exists_cons_of_ne_nil hne
  rfl

theorem arcLast_eq_getLast
    {route : List Perm7} (hroute : IsHamiltonianRoute route)
    {arc : List (ChainStart route)} (hne : arc ≠ []) :
    arcLast route hroute arc = arc.getLast hne := by
  obtain ⟨a, tail, rfl⟩ := List.exists_cons_of_ne_nil hne
  unfold arcLast
  rw [List.getLastD_cons, List.getLast_eq_getLastD]

structure RetainedArcSystem
    (route : List Perm7) (hroute : IsHamiltonianRoute route)
    (k τ : ℕ) where
  trails : List (List (List (ChainStart route)))
  trail_count : trails.length ≤ τ
  arc_count : trails.flatten.length = k
  compat :
    ∀ trail ∈ trails,
      trail.IsChain (ArcCompatible (chainAlpha route) (chainBeta route))
  nonempty : ∀ arc ∈ trails.flatten, arc ≠ []
  wrap : ∀ arc ∈ trails.flatten,
    chainFaceNext route (arcLast route hroute arc) =
      arcHead route hroute arc
  component_disjoint :
    trails.flatten.Pairwise fun arc₁ arc₂ =>
      chainStartComponent hroute (arcHead route hroute arc₁) ≠
        chainStartComponent hroute (arcHead route hroute arc₂)

structure PreparedCoarsening (k τ : ℕ) where
  trails : List (List MarkedRow)
  trail_count : trails.length ≤ τ
  row_count : trails.flatten.length = k
  compat : ∀ trail ∈ trails, trail.IsChain MarkedCompatible
  disjoint : trails.flatten.Pairwise MarkedDisjoint
  interior : ∀ row ∈ trails.flatten, row.OmissionsInterior

noncomputable def markedRowOfArc
    (route : List Perm7) (hroute : IsHamiltonianRoute route)
    (arc : List (ChainStart route)) : MarkedRow :=
  chainMarkedRow route (arcLast route hroute arc)

noncomputable def RetainedArcSystem.toPrepared
    {route : List Perm7} {hroute : IsHamiltonianRoute route}
    {k τ : ℕ} (hnormal : IsNormalizedRoute route)
    (sys : RetainedArcSystem route hroute k τ) :
    PreparedCoarsening k τ := by
  let markedTrails :=
    sys.trails.map (List.map (markedRowOfArc route hroute))
  have hflat :
      markedTrails.flatten =
        sys.trails.flatten.map (markedRowOfArc route hroute) := by
    simp [markedTrails]
  refine
    { trails := markedTrails
      trail_count := by simpa [markedTrails] using sys.trail_count
      row_count := by
        rw [hflat, List.length_map]
        exact sys.arc_count
      compat := ?_
      disjoint := ?_
      interior := ?_ }
  · intro rowTrail hrowTrail
    rcases List.mem_map.mp hrowTrail with
      ⟨arcTrail, harcTrail, rfl⟩
    rw [List.isChain_map]
    apply (sys.compat arcTrail harcTrail).imp_of_mem_imp
    intro arc₁ arc₂ harc₁ harc₂ hcompat
    have harc₁Flat : arc₁ ∈ sys.trails.flatten :=
      List.mem_flatten.mpr ⟨arcTrail, harcTrail, harc₁⟩
    have harc₂Flat : arc₂ ∈ sys.trails.flatten :=
      List.mem_flatten.mpr ⟨arcTrail, harcTrail, harc₂⟩
    have hne₁ := sys.nonempty arc₁ harc₁Flat
    have hne₂ := sys.nonempty arc₂ harc₂Flat
    have hwrap₂ := sys.wrap arc₂ harc₂Flat
    rw [arcLast_eq_getLast hroute hne₂,
      arcHead_eq_head hroute hne₂] at hwrap₂
    change MarkedCompatible
      (chainMarkedRow route (arcLast route hroute arc₁))
      (chainMarkedRow route (arcLast route hroute arc₂))
    rw [arcLast_eq_getLast hroute hne₁,
      arcLast_eq_getLast hroute hne₂]
    exact chainMarkedRow_compatible_of_arcCompatible
      hroute hnormal hne₁ hne₂ hwrap₂ hcompat
  · rw [hflat, List.pairwise_map]
    apply sys.component_disjoint.imp_of_mem
    intro arc₁ arc₂ harc₁ harc₂ hcompNe
    apply chainMarkedRows_disjoint_of_component_ne hroute hnormal
    intro hlastEq
    apply hcompNe
    calc
      chainStartComponent hroute (arcHead route hroute arc₁) =
          chainStartComponent hroute
            (chainFaceNext route (arcLast route hroute arc₁)) := by
        rw [sys.wrap arc₁ harc₁]
      _ = chainStartComponent hroute (arcLast route hroute arc₁) :=
        chainStartComponent_apply_face hroute _
      _ = chainStartComponent hroute (arcLast route hroute arc₂) :=
        hlastEq
      _ = chainStartComponent hroute
            (chainFaceNext route (arcLast route hroute arc₂)) := by
        rw [chainStartComponent_apply_face hroute]
      _ = chainStartComponent hroute (arcHead route hroute arc₂) := by
        rw [sys.wrap arc₂ harc₂]
  · intro row hrow
    rw [hflat] at hrow
    rcases List.mem_map.mp hrow with ⟨arc, _harc, rfl⟩
    exact chainMarkedRow_interior hroute hnormal _

/-! ## Accounting interface and model packaging -/

def PreparedCoarsening.totalCharge
    {k τ : ℕ} (prep : PreparedCoarsening k τ) : ℕ :=
  (prep.trails.flatten.map MarkedRow.charge).sum

def PreparedCoarsening.totalRuns
    {k τ : ℕ} (prep : PreparedCoarsening k τ) : ℕ :=
  (prep.trails.flatten.map MarkedRow.omissionRuns).sum

def PreparedCoarsening.ForestPayload
    {k τ : ℕ} (prep : PreparedCoarsening k τ) (extra : ℕ) : Prop :=
  ∃ payloadBlocks : Finset (Finset Perm7),
    payloadBlocks.card = extra ∧
    payloadBlocks ⊆ allFBlocks ∧
    (∀ x ∈ prep.trails.flatten,
      x.row.block ∉ payloadBlocks) ∧
    (∀ C ∈ allRClasses,
      (∀ x ∈ prep.trails.flatten, C ∉ x.visibleMask) →
        ∃ B ∈ payloadBlocks, ∃ p ∈ B, rClass p = C)

/-- The exact bookkeeping alternatives left after the marked rows have
been prepared.  The second branch records that a genuine hidden gap exists,
so in particular the hidden-gap budget is positive. -/
def PreparedCoarsening.AccountingOutcome
    {k τ : ℕ} (prep : PreparedCoarsening k τ)
    (u b extra : ℕ) : Prop :=
  (prep.totalCharge ≤ u ∧ prep.totalRuns ≤ b ∧
      1 ≤ prep.totalRuns) ∨
  (0 < b ∧ prep.totalCharge ≤ u - 1 ∧ prep.totalRuns ≤ b) ∨
  (prep.totalCharge = u ∧
      (∀ x ∈ prep.trails.flatten, x.omitted = ∅) ∧
      prep.ForestPayload extra)

theorem sum_omissionRuns_eq_zero_of_unmarked
    {rows : List MarkedRow}
    (h : ∀ x ∈ rows, x.omitted = ∅) :
    (rows.map MarkedRow.omissionRuns).sum = 0 := by
  induction rows with
  | nil => simp
  | cons x rows ih =>
      have hx := h x (by simp)
      have htail : ∀ y ∈ rows, y.omitted = ∅ :=
        fun y hy => h y (by simp [hy])
      simp [MarkedRow.omissionRuns, hx, ih htail]

def PreparedCoarsening.toCoarsenedInstance
    {k τ u b : ℕ} (prep : PreparedCoarsening k τ)
    (hcharge : prep.totalCharge ≤ u)
    (hruns : prep.totalRuns ≤ b) :
    CoarsenedInstance k τ u b where
  trails := prep.trails
  trail_count := prep.trail_count
  row_count := prep.row_count
  compat := prep.compat
  disjoint := prep.disjoint
  interior := prep.interior
  charge_le := hcharge
  runs_le := hruns

def CoarsenedInstance.mono
    {k τ u b τ' u' b' : ℕ}
    (inst : CoarsenedInstance k τ u b)
    (hτ : τ ≤ τ') (hu : u ≤ u') (hb : b ≤ b') :
    CoarsenedInstance k τ' u' b' where
  trails := inst.trails
  trail_count := inst.trail_count.trans hτ
  row_count := inst.row_count
  compat := inst.compat
  disjoint := inst.disjoint
  interior := inst.interior
  charge_le := inst.charge_le.trans hu
  runs_le := inst.runs_le.trans hb

def CoarsenedInstance.castRowCount
    {k k' τ u b : ℕ} (h : k = k')
    (inst : CoarsenedInstance k τ u b) :
    CoarsenedInstance k' τ u b :=
  h ▸ inst

@[simp] theorem CoarsenedInstance.castRowCount_trails
    {k k' τ u b : ℕ} (h : k = k')
    (inst : CoarsenedInstance k τ u b) :
    (inst.castRowCount h).trails = inst.trails := by
  subst k'
  rfl

/-- Package the purely numerical accounting trichotomy as the exact three
finite-model cases consumed by the elimination layer. -/
theorem PreparedCoarsening.toCases
    {k τ u b extra : ℕ} (prep : PreparedCoarsening k τ)
    (hout : prep.AccountingOutcome u b extra) :
    (∃ inst : CoarsenedInstance k τ u b,
        1 ≤ (inst.trails.flatten.map
          MarkedRow.omissionRuns).sum) ∨
    (0 < b ∧ Nonempty (CoarsenedInstance k τ (u - 1) b)) ∨
    Nonempty (ForestInstance k τ u extra) := by
  rcases hout with hmarked | hoffblock | hforest
  · left
    let inst :=
      prep.toCoarsenedInstance hmarked.1 hmarked.2.1
    exact ⟨inst, hmarked.2.2⟩
  · right
    left
    exact ⟨hoffblock.1,
      ⟨prep.toCoarsenedInstance hoffblock.2.1 hoffblock.2.2⟩⟩
  · right
    right
    rcases hforest.2.2 with
      ⟨payloadBlocks, hpayloadCard, hpayloadBlocks,
        hpayloadFresh, hpayloadCover⟩
    have hrunsZero :
        (prep.trails.flatten.map MarkedRow.omissionRuns).sum = 0 :=
      sum_omissionRuns_eq_zero_of_unmarked hforest.2.1
    let base : CoarsenedInstance k τ u 0 :=
      prep.toCoarsenedInstance
        (by rw [hforest.1])
        (by
          simpa [PreparedCoarsening.totalRuns] using hrunsZero.le)
    exact ⟨
      { toCoarsenedInstance := base
        charge_eq := hforest.1
        unmarked := hforest.2.1
        payloadBlocks := payloadBlocks
        payload_card := hpayloadCard
        payload_blocks := hpayloadBlocks
        payload_fresh := hpayloadFresh
        payload_cover := hpayloadCover }⟩

end Superperm7
