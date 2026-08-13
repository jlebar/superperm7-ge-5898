/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE); this file is
additionally subject to the upstream MIT notice below.

Adapted from https://github.com/BGray-wrl/superperm6
  file:   formal-verification/Superperm6/Orbit.lean
  commit: d8a932d8f61d80b0bcfc737bd0e235a8300449c4
  upstream copyright: Copyright (c) 2026 Benjamin Grayzel — MIT License (reproduced in NOTICE).
Local modifications (port from six to seven symbols; see docs/PORT_LOG.md): rotation of order 7, orbit inequality 120 + ceil(r/6) <= r + q; pairwise native_decide lemmas restated with a single permutation quantifier.
-/
import Superperm7.CheapCover
import Superperm7.Frontier
import Superperm7.GraphRank
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# The orbit graph of the cost-one runs

This file constructs the quotient graph used in Section 3 directly from a
Hamilton route.  Its vertices are the touched insertion blocks.  One star
per rotation class supplies at most `r` edges.
-/

namespace Superperm7

theorem self_mem_rClass (p : Perm7) : p ∈ rClass p := by
  apply Finset.mem_image.mpr
  exact ⟨0, by simp, by simp⟩

theorem rClass_R (p : Perm7) : rClass (R p) = rClass p :=
  rClass_eq_of_mem p (R p) (R_mem_rClass_of_mem p p (self_mem_rClass p))

/-- The insertion successor stays in the same insertion block. -/
theorem fBlock_F : ∀ p : Perm7, fBlock (F p) = fBlock p := by
  native_decide

/-- The explicit identity behind equation (3.4). -/
theorem N₂_eq_F_R : ∀ p : Perm7, N₂ p = F (R p) := by
  native_decide

def rotationClassOf (p : Perm7) : RotationClass :=
  ⟨rClass p, Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩⟩

private theorem rotationClass_eq_rClass_of_mem (C : RotationClass)
    {p : Perm7} (hp : p ∈ C.1) : C.1 = rClass p := by
  rcases Finset.mem_image.mp C.2 with ⟨q, _hq, hqC⟩
  rw [← hqC] at hp ⊢
  exact (rClass_eq_of_mem q p hp).symm

/-- Each rotation class contains a run start.  The proof uses the member of
the class that occurs last in the linear route. -/
theorem rotationClass_meets_runStartSet {route : List Perm7}
    (hroute : IsHamiltonianRoute route) (C : RotationClass) :
    ∃ p ∈ runStartSet route, p ∈ C.1 := by
  let u := lastInRotationClass route C
  have huC : u ∈ C.1 := lastInRotationClass_mem route C
  have hRuC : R u ∈ C.1 := by
    rcases Finset.mem_image.mp C.2 with ⟨p, _hp, hpC⟩
    rw [← hpC] at huC ⊢
    exact R_mem_rClass_of_mem p u huC
  have hnotDest : R u ∉ costOneDestinations route := by
    intro hdest
    obtain ⟨a, haEdge, haCost⟩ :=
      mem_costOneDestinations_gives_edge hdest
    have hRa : R u = R a := (cost_one_successor a (R u)).mp haCost
    have hau : a = u := R_injective hRa.symm
    subst a
    have hsucc := idxOf_succ_of_pair_infix hroute.1 (hroute.2 u)
      (hroute.2 (R u)) haEdge
    have hmax := idxOf_le_lastInRotationClass route C hRuC
    dsimp [u] at hsucc hmax
    omega
  refine ⟨R u, ?_, hRuC⟩
  simp [runStartSet, hnotDest]

abbrev RunStart (route : List Perm7) := ↥(runStartSet route)

/-- The insertion blocks touched by run starts. -/
def touchedBlocks (route : List Perm7) : Finset (Finset Perm7) :=
  (runStartSet route).image fBlock

abbrev TouchedBlock (route : List Perm7) := ↥(touchedBlocks route)

def startBlock {route : List Perm7} (s : RunStart route) :
    TouchedBlock route :=
  ⟨fBlock s.1, Finset.mem_image.mpr ⟨s.1, s.2, rfl⟩⟩

/-- A chosen run start in each rotation class. -/
noncomputable def baseRunStart (route : List Perm7)
    (hroute : IsHamiltonianRoute route) (C : RotationClass) : RunStart route :=
  ⟨Classical.choose (rotationClass_meets_runStartSet hroute C),
    (Classical.choose_spec (rotationClass_meets_runStartSet hroute C)).1⟩

theorem baseRunStart_mem_class (route : List Perm7)
    (hroute : IsHamiltonianRoute route) (C : RotationClass) :
    (baseRunStart route hroute C).1 ∈ C.1 :=
  (Classical.choose_spec (rotationClass_meets_runStartSet hroute C)).2

theorem baseRunStart_injective (route : List Perm7)
    (hroute : IsHamiltonianRoute route) :
    Function.Injective (baseRunStart route hroute) := by
  intro C D hCD
  apply Subtype.ext
  have hC := baseRunStart_mem_class route hroute C
  have hD := baseRunStart_mem_class route hroute D
  rw [← congrArg Subtype.val hCD] at hD
  calc
    C.1 = rClass (baseRunStart route hroute C).1 :=
      rotationClass_eq_rClass_of_mem C hC
    _ = D.1 := (rotationClass_eq_rClass_of_mem D hD).symm

noncomputable def baseRunStartSet (route : List Perm7)
    (hroute : IsHamiltonianRoute route) : Finset (RunStart route) :=
  Finset.univ.image (baseRunStart route hroute)

theorem baseRunStartSet_card (route : List Perm7)
    (hroute : IsHamiltonianRoute route) :
    (baseRunStartSet route hroute).card = 720 := by
  calc
    (baseRunStartSet route hroute).card =
        (Finset.univ : Finset RotationClass).card := by
      exact Finset.card_image_of_injective _ (baseRunStart_injective route hroute)
    _ = Fintype.card RotationClass := Finset.card_univ
    _ = allRClasses.card := Fintype.card_coe allRClasses
    _ = 720 := number_of_rClasses

noncomputable def nonBaseRunStarts (route : List Perm7)
    (hroute : IsHamiltonianRoute route) : Finset (RunStart route) :=
  Finset.univ \ baseRunStartSet route hroute

theorem nonBaseRunStarts_card (route : List Perm7)
    (hroute : IsHamiltonianRoute route) :
    (nonBaseRunStarts route hroute).card =
      (runStartSet route).card - 720 := by
  rw [nonBaseRunStarts, Finset.card_sdiff]
  simp only [Finset.inter_univ, Fintype.card_coe, Finset.card_univ]
  rw [baseRunStartSet_card]

private theorem runStart_eq_own_base_of_mem_baseSet {route : List Perm7}
    (hroute : IsHamiltonianRoute route) (s : RunStart route)
    (hs : s ∈ baseRunStartSet route hroute) :
    s = baseRunStart route hroute (rotationClassOf s.1) := by
  rcases Finset.mem_image.mp hs with ⟨C, _hC, hsC⟩
  have hsMemC : s.1 ∈ C.1 := by
    rw [← hsC]
    exact baseRunStart_mem_class route hroute C
  have hclass : C = rotationClassOf s.1 := by
    apply Subtype.ext
    exact rotationClass_eq_rClass_of_mem C hsMemC
  simpa [hclass] using hsC.symm

/-- Candidate quotient edges: every non-base run start is joined to the
chosen start in its rotation class, after projecting both to insertion
blocks.  Diagonal candidates are harmless and are discarded by
`SimpleGraph.fromEdgeSet`. -/
noncomputable def rotationEdgeCandidates (route : List Perm7)
    (hroute : IsHamiltonianRoute route) : Finset (Sym2 (TouchedBlock route)) :=
  (nonBaseRunStarts route hroute).image fun s =>
    s(startBlock s,
      startBlock (baseRunStart route hroute (rotationClassOf s.1)))

noncomputable def rotationGraph (route : List Perm7)
    (hroute : IsHamiltonianRoute route) : SimpleGraph (TouchedBlock route) :=
  SimpleGraph.fromEdgeSet (rotationEdgeCandidates route hroute :
    Set (Sym2 (TouchedBlock route)))

theorem rotationEdgeCandidates_card_le (route : List Perm7)
    (hroute : IsHamiltonianRoute route) :
    (rotationEdgeCandidates route hroute).card ≤
      (runStartSet route).card - 720 := by
  exact Finset.card_image_le.trans_eq (nonBaseRunStarts_card route hroute)

/-- Every run start is connected in the quotient graph to the chosen start
of its rotation class. -/
theorem startBlock_reachable_own_base {route : List Perm7}
    (hroute : IsHamiltonianRoute route) (s : RunStart route) :
    (rotationGraph route hroute).Reachable (startBlock s)
      (startBlock (baseRunStart route hroute (rotationClassOf s.1))) := by
  let b := baseRunStart route hroute (rotationClassOf s.1)
  change (rotationGraph route hroute).Reachable (startBlock s) (startBlock b)
  by_cases hsb : s = b
  · exact hsb ▸ SimpleGraph.Reachable.refl _
  have hsNonBase : s ∈ nonBaseRunStarts route hroute := by
    simp only [nonBaseRunStarts, Finset.mem_sdiff, Finset.mem_univ, true_and]
    intro hsBase
    exact hsb (runStart_eq_own_base_of_mem_baseSet hroute s hsBase)
  have hedge : s(startBlock s, startBlock b) ∈
      rotationEdgeCandidates route hroute := by
    apply Finset.mem_image.mpr
    exact ⟨s, hsNonBase, rfl⟩
  by_cases hblocks : startBlock s = startBlock b
  · exact hblocks ▸ SimpleGraph.Reachable.refl _
  apply SimpleGraph.Adj.reachable
  rw [rotationGraph, SimpleGraph.fromEdgeSet_adj]
  exact ⟨by simpa using hedge, hblocks⟩

/-- Starts in the same rotation class project into the same connected
component of the quotient graph. -/
theorem startBlocks_reachable_of_same_rClass {route : List Perm7}
    (hroute : IsHamiltonianRoute route) (s t : RunStart route)
    (hst : rClass s.1 = rClass t.1) :
    (rotationGraph route hroute).Reachable (startBlock s) (startBlock t) := by
  have hclass : rotationClassOf s.1 = rotationClassOf t.1 := by
    apply Subtype.ext
    exact hst
  have hs := startBlock_reachable_own_base hroute s
  have ht := startBlock_reachable_own_base hroute t
  rw [hclass] at hs
  exact hs.trans ht.symm

/-! ## Cost-two chains meet the quotient components -/

private theorem pair_relation_of_isChain {α : Type*} {R : α → α → Prop}
    {route : List α} {x y : α} (hchain : route.IsChain R)
    (hpair : [x, y] <:+: route) : R x y := by
  rcases hpair with ⟨pre, post, hroute⟩
  exact (List.isChain_iff_forall_rel_of_append_cons_cons.mp hchain)
    (a := x) (b := y) (l₁ := pre) (l₂ := post)
    (by simpa [List.append_assoc] using hroute.symm)

private theorem pair_right_unique {route : List Perm7} {x y z : Perm7}
    (hroute : IsHamiltonianRoute route)
    (hxy : [x, y] <:+: route) (hxz : [x, z] <:+: route) : y = z := by
  have hiy := idxOf_succ_of_pair_infix hroute.1 (hroute.2 x) (hroute.2 y) hxy
  have hiz := idxOf_succ_of_pair_infix hroute.1 (hroute.2 x) (hroute.2 z) hxz
  exact (List.idxOf_inj (hroute.2 y)).mp (by omega)

private theorem pair_left_unique {route : List Perm7} {x y z : Perm7}
    (hroute : IsHamiltonianRoute route)
    (hxz : [x, z] <:+: route) (hyz : [y, z] <:+: route) : x = y := by
  have hix := idxOf_succ_of_pair_infix hroute.1 (hroute.2 x) (hroute.2 z) hxz
  have hiy := idxOf_succ_of_pair_infix hroute.1 (hroute.2 y) (hroute.2 z) hyz
  exact (List.idxOf_inj (hroute.2 x)).mp (by omega)

/-- The earliest route vertex in a rotation class. -/
noncomputable def firstInRotationClass (route : List Perm7)
    (C : RotationClass) : Perm7 :=
  Classical.choose (Finset.exists_min_image C.1 (fun p => route.idxOf p)
    (by
      rcases Finset.mem_image.mp C.2 with ⟨p, _hp, hpC⟩
      rw [← hpC]
      apply Finset.card_pos.mp
      rw [rClass_card]
      omega))

theorem firstInRotationClass_mem (route : List Perm7) (C : RotationClass) :
    firstInRotationClass route C ∈ C.1 :=
  (Classical.choose_spec (Finset.exists_min_image C.1 (fun p => route.idxOf p)
    (by
      rcases Finset.mem_image.mp C.2 with ⟨p, _hp, hpC⟩
      rw [← hpC]
      apply Finset.card_pos.mp
      rw [rClass_card]
      omega))).1

theorem firstInRotationClass_idx_le (route : List Perm7) (C : RotationClass)
    {p : Perm7} (hp : p ∈ C.1) :
    route.idxOf (firstInRotationClass route C) ≤ route.idxOf p :=
  (Classical.choose_spec (Finset.exists_min_image C.1 (fun p => route.idxOf p)
    (by
      rcases Finset.mem_image.mp C.2 with ⟨q, _hq, hqC⟩
      rw [← hqC]
      apply Finset.card_pos.mp
      rw [rClass_card]
      omega))).2 p hp

/-- The earliest vertex of every rotation class is necessarily a run
start. -/
theorem firstInRotationClass_is_runStart {route : List Perm7}
    (hroute : IsHamiltonianRoute route) (C : RotationClass) :
    firstInRotationClass route C ∈ runStartSet route := by
  let u := firstInRotationClass route C
  have huC : u ∈ C.1 := firstInRotationClass_mem route C
  have hnotDest : u ∉ costOneDestinations route := by
    intro huDest
    obtain ⟨a, haEdge, haCost⟩ := mem_costOneDestinations_gives_edge huDest
    have hua : u = R a := (cost_one_successor a u).mp haCost
    have haC : a ∈ C.1 := by
      have hclass : C.1 = rClass u := rotationClass_eq_rClass_of_mem C huC
      rw [hclass, hua, rClass_R]
      exact self_mem_rClass a
    have hmin := firstInRotationClass_idx_le route C haC
    have hsucc := idxOf_succ_of_pair_infix hroute.1 (hroute.2 a) (hroute.2 u) haEdge
    dsimp [u] at hmin hsucc
    omega
  dsimp [u] at hnotDest ⊢
  simp [runStartSet, hnotDest]

noncomputable def firstRunStartInClass {route : List Perm7}
    (hroute : IsHamiltonianRoute route) (C : RotationClass) : RunStart route :=
  ⟨firstInRotationClass route C, firstInRotationClass_is_runStart hroute C⟩

/-- The destination of an actual non-cost-one route edge is a run start. -/
theorem target_runStart_of_cost_ne_one {route : List Perm7} {x y : Perm7}
    (hroute : IsHamiltonianRoute route) (hpair : [x, y] <:+: route)
    (hcost : d x y ≠ 1) : y ∈ runStartSet route := by
  have hnotDest : y ∉ costOneDestinations route := by
    intro hyDest
    obtain ⟨a, haEdge, haCost⟩ := mem_costOneDestinations_gives_edge hyDest
    have hax : a = x := pair_left_unique hroute haEdge hpair
    subst a
    exact hcost haCost
  simp [runStartSet, hnotDest]

/-- If `x → y` is a cost-two edge, the unused cost-one successor `R x` is
also a run start. -/
theorem rotation_successor_runStart_of_cost_two {route : List Perm7}
    {x y : Perm7} (hroute : IsHamiltonianRoute route)
    (hpair : [x, y] <:+: route) (hcost : d x y = 2) :
    R x ∈ runStartSet route := by
  have hnotDest : R x ∉ costOneDestinations route := by
    intro hDest
    obtain ⟨a, haEdge, haCost⟩ := mem_costOneDestinations_gives_edge hDest
    have hRa : R x = R a := (cost_one_successor a (R x)).mp haCost
    have hax : a = x := R_injective hRa.symm
    subst a
    have htarget : R x = y := pair_right_unique hroute haEdge hpair
    have hOne : d x (R x) = 1 := (cost_one_successor x (R x)).2 rfl
    rw [htarget] at hOne
    omega
  simp [runStartSet, hnotDest]

theorem normalized_cost_two_edge {route : List Perm7} {x y : Perm7}
    (hnormal : IsNormalizedRoute route) (hpair : [x, y] <:+: route)
    (hcost : d x y = 2) : y = N₂ x := by
  exact pair_relation_of_isChain (normalized_cost_two_successor hnormal) hpair hcost

/-- Moving backwards across a cost-two edge reaches an earlier run start in
the same quotient component. -/
theorem earlier_runStart_reachable_of_cost_two {route : List Perm7}
    {x y : Perm7} (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route) (hpair : [x, y] <:+: route)
    (hcost : d x y = 2) :
    let ys : RunStart route :=
      ⟨y, target_runStart_of_cost_ne_one hroute hpair (by omega)⟩
    ∃ t : RunStart route,
      route.idxOf t.1 < route.idxOf y ∧
      (rotationGraph route hroute).Reachable (startBlock t) (startBlock ys) := by
  dsimp
  let C := rotationClassOf x
  let t : RunStart route := firstRunStartInClass hroute C
  let rx : RunStart route :=
    ⟨R x, rotation_successor_runStart_of_cost_two hroute hpair hcost⟩
  let ys : RunStart route :=
    ⟨y, target_runStart_of_cost_ne_one hroute hpair (by omega)⟩
  have hxC : x ∈ C.1 := by
    dsimp [C, rotationClassOf]
    exact self_mem_rClass x
  have hidxT : route.idxOf t.1 ≤ route.idxOf x := by
    exact firstInRotationClass_idx_le route C hxC
  have hidxY := idxOf_succ_of_pair_infix hroute.1 (hroute.2 x) (hroute.2 y) hpair
  have hclasses : rClass t.1 = rClass rx.1 := by
    dsimp [t, firstRunStartInClass, rx, C]
    have htC := firstInRotationClass_mem route (rotationClassOf x)
    have htClass := rotationClass_eq_rClass_of_mem (rotationClassOf x) htC
    simpa [rotationClassOf, rClass_R] using htClass.symm
  have hreach : (rotationGraph route hroute).Reachable
      (startBlock t) (startBlock rx) :=
    startBlocks_reachable_of_same_rClass hroute t rx hclasses
  have hy : y = F (R x) := by
    rw [normalized_cost_two_edge hnormal hpair hcost, N₂_eq_F_R]
  have hblocks : startBlock rx = startBlock ys := by
    apply Subtype.ext
    change fBlock (R x) = fBlock y
    calc
      fBlock (R x) = fBlock (F (R x)) := (fBlock_F (R x)).symm
      _ = fBlock y := congrArg fBlock hy.symm
  have hlt : route.idxOf t.1 < route.idxOf y := by omega
  refine ⟨t, hlt, ?_⟩
  exact hblocks ▸ hreach

/-- Every run start is joined, through cost-two transitions inside the
rotation quotient, to an earlier start of a cost-one/two chain. -/
theorem runStart_reachable_chainStart {route : List Perm7}
    (hroute : IsHamiltonianRoute route) (hnormal : IsNormalizedRoute route)
    (s : RunStart route) :
    ∃ c : RunStart route,
      c.1 ∈ chainStartSet route ∧
      (rotationGraph route hroute).Reachable (startBlock c) (startBlock s) := by
  by_cases hsChain : s.1 ∈ chainStartSet route
  · exact ⟨s, hsChain, SimpleGraph.Reachable.refl _⟩
  have hsCheapDest : s.1 ∈ cheapTwoDestinations route := by
    by_contra hnot
    apply hsChain
    simp [chainStartSet, hnot]
  obtain ⟨x, hxEdge, hxCheap⟩ :=
    mem_cheapTwoDestinations_gives_edge hsCheapDest
  have hsNotOneDest : s.1 ∉ costOneDestinations route := by
    have hsMem : s.1 ∈ (Finset.univ : Finset Perm7) \
        (costOneDestinations route).toFinset := s.2
    intro hsList
    exact (Finset.mem_sdiff.mp hsMem).2 (by simpa using hsList)
  have hxNotOne : d x s.1 ≠ 1 := by
    intro hxOne
    exact hsNotOneDest (pair_infix_mem_costOneDestinations hxEdge hxOne)
  have hidx := idxOf_succ_of_pair_infix hroute.1 (hroute.2 x)
    (hroute.2 s.1) hxEdge
  have hne : x ≠ s.1 := by
    intro hxs
    subst x
    simp at hidx
  have hpos := d_pos_of_ne hne
  have hxTwo : d x s.1 = 2 := by omega
  obtain ⟨t, htEarlier, htReach⟩ :=
    earlier_runStart_reachable_of_cost_two hroute hnormal hxEdge hxTwo
  obtain ⟨c, hcChain, hcReach⟩ :=
    runStart_reachable_chainStart hroute hnormal t
  refine ⟨c, hcChain, hcReach.trans ?_⟩
  simpa only using htReach
termination_by route.idxOf s.1
decreasing_by exact htEarlier

/-- A chain start cannot be the destination of a cost-one edge, so it is
also a run start. -/
theorem chainStartSet_subset_runStartSet (route : List Perm7) :
    chainStartSet route ⊆ runStartSet route := by
  intro p hp
  have hpNotCheap : p ∉ cheapTwoDestinations route := by
    simpa [chainStartSet] using hp
  have hpNotOne : p ∉ costOneDestinations route := by
    intro hpOne
    obtain ⟨x, hxEdge, hxOne⟩ := mem_costOneDestinations_gives_edge hpOne
    exact hpNotCheap (pair_infix_mem_cheapTwoDestinations hxEdge (by omega))
  simp [runStartSet, hpNotOne]

abbrev ChainStart (route : List Perm7) := ↥(chainStartSet route)

def chainAsRunStart {route : List Perm7} (c : ChainStart route) :
    RunStart route :=
  ⟨c.1, chainStartSet_subset_runStartSet route c.2⟩

theorem chainStartSet_nonempty {route : List Perm7}
    (hroute : IsHamiltonianRoute route) : (chainStartSet route).Nonempty := by
  obtain ⟨p, rest, hrouteEq⟩ :=
    List.exists_cons_of_ne_nil (hamiltonian_route_nonempty hroute)
  have hpNotDest : p ∉ cheapTwoDestinations route := by
    intro hpDest
    have hsub := cheapTwoDestinations_sublist_tail route
    have hpTail : p ∈ route.tail := hsub.mem hpDest
    rw [hrouteEq] at hpTail
    have hnodup : (p :: rest).Nodup := by simpa [hrouteEq] using hroute.1
    exact (List.nodup_cons.mp hnodup).1 hpTail
  refine ⟨p, ?_⟩
  simp [chainStartSet, hpNotDest]

/-- A fixed anchor among the chain starts. -/
noncomputable def baseChainStart (route : List Perm7)
    (hroute : IsHamiltonianRoute route) : ChainStart route :=
  ⟨Classical.choose (chainStartSet_nonempty hroute),
    Classical.choose_spec (chainStartSet_nonempty hroute)⟩

noncomputable def nonBaseChainStarts (route : List Perm7)
    (hroute : IsHamiltonianRoute route) : Finset (ChainStart route) :=
  Finset.univ.erase (baseChainStart route hroute)

theorem nonBaseChainStarts_card (route : List Perm7)
    (hroute : IsHamiltonianRoute route) :
    (nonBaseChainStarts route hroute).card =
      (chainStartSet route).card - 1 := by
  change ((Finset.univ : Finset (ChainStart route)).erase
      (baseChainStart route hroute)).card = _
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_coe]

noncomputable def chainAnchorEdgeCandidates (route : List Perm7)
    (hroute : IsHamiltonianRoute route) : Finset (Sym2 (TouchedBlock route)) :=
  (nonBaseChainStarts route hroute).image fun c =>
    s(startBlock (chainAsRunStart c),
      startBlock (chainAsRunStart (baseChainStart route hroute)))

theorem chainAnchorEdgeCandidates_card_le (route : List Perm7)
    (hroute : IsHamiltonianRoute route) :
    (chainAnchorEdgeCandidates route hroute).card ≤
      (chainStartSet route).card - 1 := by
  exact Finset.card_image_le.trans_eq (nonBaseChainStarts_card route hroute)

noncomputable def orbitEdgeCandidates (route : List Perm7)
    (hroute : IsHamiltonianRoute route) : Finset (Sym2 (TouchedBlock route)) :=
  rotationEdgeCandidates route hroute ∪ chainAnchorEdgeCandidates route hroute

noncomputable def orbitGraph (route : List Perm7)
    (hroute : IsHamiltonianRoute route) : SimpleGraph (TouchedBlock route) :=
  SimpleGraph.fromEdgeSet (orbitEdgeCandidates route hroute :
    Set (Sym2 (TouchedBlock route)))

theorem rotationGraph_le_orbitGraph (route : List Perm7)
    (hroute : IsHamiltonianRoute route) :
    rotationGraph route hroute ≤ orbitGraph route hroute := by
  unfold rotationGraph orbitGraph orbitEdgeCandidates
  apply SimpleGraph.fromEdgeSet_mono
  intro e he
  exact Finset.mem_union_left _ he

/-- Every chain anchor is connected to the fixed anchor by its one added
edge. -/
theorem chainStart_reachable_baseAnchor {route : List Perm7}
    (hroute : IsHamiltonianRoute route) (c : ChainStart route) :
    (orbitGraph route hroute).Reachable (startBlock (chainAsRunStart c))
      (startBlock (chainAsRunStart (baseChainStart route hroute))) := by
  let b := baseChainStart route hroute
  change (orbitGraph route hroute).Reachable (startBlock (chainAsRunStart c))
    (startBlock (chainAsRunStart b))
  by_cases hcb : c = b
  · exact hcb ▸ SimpleGraph.Reachable.refl _
  have hcb' : c ≠ baseChainStart route hroute := by
    simpa [b] using hcb
  have hcNonBase : c ∈ nonBaseChainStarts route hroute := by
    simp [nonBaseChainStarts, hcb']
  have hedge : s(startBlock (chainAsRunStart c),
      startBlock (chainAsRunStart b)) ∈
      chainAnchorEdgeCandidates route hroute := by
    apply Finset.mem_image.mpr
    exact ⟨c, hcNonBase, rfl⟩
  by_cases hblocks : startBlock (chainAsRunStart c) =
      startBlock (chainAsRunStart b)
  · exact hblocks ▸ SimpleGraph.Reachable.refl _
  apply SimpleGraph.Adj.reachable
  rw [orbitGraph, SimpleGraph.fromEdgeSet_adj]
  refine ⟨?_, hblocks⟩
  apply Finset.mem_union_right
  simpa using hedge

/-- After adding the chain-anchor edges, the touched-block graph is
connected. -/
theorem orbitGraph_connected {route : List Perm7}
    (hroute : IsHamiltonianRoute route) (hnormal : IsNormalizedRoute route) :
    (orbitGraph route hroute).Connected := by
  let anyClass := rotationClassOf (Equiv.refl Symbol)
  let anyStart := baseRunStart route hroute anyClass
  letI : Nonempty (TouchedBlock route) := ⟨startBlock anyStart⟩
  apply SimpleGraph.Connected.mk
  intro B D
  rcases Finset.mem_image.mp B.2 with ⟨s, hsStart, hsBlock⟩
  rcases Finset.mem_image.mp D.2 with ⟨t, htStart, htBlock⟩
  let rs : RunStart route := ⟨s, hsStart⟩
  let rt : RunStart route := ⟨t, htStart⟩
  have hB : startBlock rs = B := by
    apply Subtype.ext
    exact hsBlock
  have hD : startBlock rt = D := by
    apply Subtype.ext
    exact htBlock
  obtain ⟨cs, hcsChain, hcsReach⟩ :=
    runStart_reachable_chainStart hroute hnormal rs
  obtain ⟨ct, hctChain, hctReach⟩ :=
    runStart_reachable_chainStart hroute hnormal rt
  let ccs : ChainStart route := ⟨cs.1, hcsChain⟩
  let cct : ChainStart route := ⟨ct.1, hctChain⟩
  have hcsEq : chainAsRunStart ccs = cs := by apply Subtype.ext; rfl
  have hctEq : chainAsRunStart cct = ct := by apply Subtype.ext; rfl
  have hrotLe := rotationGraph_le_orbitGraph route hroute
  have hcsFinal := hcsReach.mono hrotLe
  have hctFinal := hctReach.mono hrotLe
  have hcsAnchor := chainStart_reachable_baseAnchor hroute ccs
  have hctAnchor := chainStart_reachable_baseAnchor hroute cct
  rw [hcsEq] at hcsAnchor
  rw [hctEq] at hctAnchor
  have hBD : (orbitGraph route hroute).Reachable (startBlock rs) (startBlock rt) :=
    hcsFinal.symm.trans (hcsAnchor.trans (hctAnchor.symm.trans hctFinal))
  simpa [hB, hD] using hBD

theorem orbitGraph_edgeFinset_card_le (route : List Perm7)
    (hroute : IsHamiltonianRoute route) :
    (orbitGraph route hroute).edgeFinset.card ≤
      ((runStartSet route).card - 720) +
        ((chainStartSet route).card - 1) := by
  have hsubset : (orbitGraph route hroute).edgeFinset ⊆
      orbitEdgeCandidates route hroute := by
    intro e he
    have heSet : e ∈ (orbitGraph route hroute).edgeSet :=
      SimpleGraph.mem_edgeFinset.mp he
    rw [orbitGraph, SimpleGraph.edgeSet_fromEdgeSet] at heSet
    exact heSet.1
  calc
    (orbitGraph route hroute).edgeFinset.card ≤
        (orbitEdgeCandidates route hroute).card := Finset.card_le_card hsubset
    _ ≤ (rotationEdgeCandidates route hroute).card +
        (chainAnchorEdgeCandidates route hroute).card := by
          exact Finset.card_union_le _ _
    _ ≤ ((runStartSet route).card - 720) +
        ((chainStartSet route).card - 1) :=
          Nat.add_le_add (rotationEdgeCandidates_card_le route hroute)
            (chainAnchorEdgeCandidates_card_le route hroute)

/-- The concrete quotient-rank/chain inequality `M ≤ r+q`, stated before
substituting the profile variables. -/
theorem touchedBlocks_card_le_run_excess_add_chains {route : List Perm7}
    (hroute : IsHamiltonianRoute route) (hnormal : IsNormalizedRoute route) :
    (touchedBlocks route).card ≤
      ((runStartSet route).card - 720) + (chainStartSet route).card := by
  have hconn := orbitGraph_connected hroute hnormal
  have hvertices := hconn.card_vert_le_card_edgeSet_add_one
  have hedges := orbitGraph_edgeFinset_card_le route hroute
  have hchainPos : 1 ≤ (chainStartSet route).card :=
    Finset.card_pos.mpr (chainStartSet_nonempty hroute)
  have hvertices' := hvertices
  rw [Nat.card_eq_fintype_card, Fintype.card_coe] at hvertices'
  have hedgeNat : Nat.card (orbitGraph route hroute).edgeSet =
      (orbitGraph route hroute).edgeFinset.card := by
    rw [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card]
  rw [hedgeNat] at hvertices'
  omega

theorem self_mem_fBlock (p : Perm7) : p ∈ fBlock p := by
  apply Finset.mem_image.mpr
  exact ⟨0, by simp, by simp⟩

/-- Six states per insertion block gives `|S| ≤ 6M`. -/
theorem runStartSet_card_le_six_mul_touchedBlocks (route : List Perm7) :
    (runStartSet route).card ≤ 6 * (touchedBlocks route).card := by
  apply Finset.card_le_mul_card_image
  intro B hB
  rcases Finset.mem_image.mp hB with ⟨p, hp, hpB⟩
  subst B
  apply (Finset.card_le_card ?_).trans_eq (fBlock_card p)
  intro q hq
  simp only [Finset.mem_filter] at hq
  rw [← hq.2]
  exact self_mem_fBlock q

/-! ## The unaugmented quotient component count -/

noncomputable def rotationComponentCount (route : List Perm7)
    (hroute : IsHamiltonianRoute route) : ℕ :=
  Fintype.card (rotationGraph route hroute).ConnectedComponent

noncomputable def chainStartComponent {route : List Perm7}
    (hroute : IsHamiltonianRoute route) (c : ChainStart route) :
    (rotationGraph route hroute).ConnectedComponent :=
  (rotationGraph route hroute).connectedComponentMk
    (startBlock (chainAsRunStart c))

theorem chainStartComponent_surjective {route : List Perm7}
    (hroute : IsHamiltonianRoute route) (hnormal : IsNormalizedRoute route) :
    Function.Surjective (chainStartComponent hroute) := by
  intro K
  obtain ⟨B, hBK⟩ := K.nonempty_supp
  have hcomp : (rotationGraph route hroute).connectedComponentMk B = K :=
    (K.mem_supp_iff B).mp hBK
  rcases Finset.mem_image.mp B.2 with ⟨s, hsStart, hsBlock⟩
  let rs : RunStart route := ⟨s, hsStart⟩
  obtain ⟨c, hcChain, hcReach⟩ :=
    runStart_reachable_chainStart hroute hnormal rs
  let cc : ChainStart route := ⟨c.1, hcChain⟩
  refine ⟨cc, ?_⟩
  have hcc : chainAsRunStart cc = c := by
    apply Subtype.ext
    rfl
  have hB : startBlock rs = B := by
    apply Subtype.ext
    exact hsBlock
  have hreach : (rotationGraph route hroute).Reachable
      (startBlock (chainAsRunStart cc)) B := by
    simpa [hcc, hB] using hcReach
  exact (SimpleGraph.ConnectedComponent.sound hreach).trans hcomp

theorem rotationComponentCount_le_chains {route : List Perm7}
    (hroute : IsHamiltonianRoute route) (hnormal : IsNormalizedRoute route) :
    rotationComponentCount route hroute ≤ (chainStartSet route).card := by
  have hcard := Fintype.card_le_of_surjective (chainStartComponent hroute)
    (chainStartComponent_surjective hroute hnormal)
  simpa [rotationComponentCount, Fintype.card_coe] using hcard

theorem rotationComponentCount_le_touchedBlocks {route : List Perm7}
    (hroute : IsHamiltonianRoute route) :
    rotationComponentCount route hroute ≤ (touchedBlocks route).card := by
  have hcard := Fintype.card_le_of_surjective
    ((rotationGraph route hroute).connectedComponentMk)
    Quot.mk_surjective
  simpa [rotationComponentCount, Fintype.card_coe] using hcard

theorem rotationGraph_edgeFinset_card_le (route : List Perm7)
    (hroute : IsHamiltonianRoute route) :
    (rotationGraph route hroute).edgeFinset.card ≤
      (runStartSet route).card - 720 := by
  have hsubset : (rotationGraph route hroute).edgeFinset ⊆
      rotationEdgeCandidates route hroute := by
    intro e he
    have heSet : e ∈ (rotationGraph route hroute).edgeSet :=
      SimpleGraph.mem_edgeFinset.mp he
    rw [rotationGraph, SimpleGraph.edgeSet_fromEdgeSet] at heSet
    exact heSet.1
  exact (Finset.card_le_card hsubset).trans
    (rotationEdgeCandidates_card_le route hroute)

theorem touchedBlocks_card_le_run_excess_add_components {route : List Perm7}
    (hroute : IsHamiltonianRoute route) :
    (touchedBlocks route).card ≤
      ((runStartSet route).card - 720) +
        rotationComponentCount route hroute := by
  have hrank := card_vertices_le_card_edges_add_components
    (rotationGraph route hroute)
  have hedge := rotationGraph_edgeFinset_card_le route hroute
  have hbound := hrank.trans (Nat.add_le_add_right hedge _)
  simpa [rotationComponentCount, Fintype.card_coe] using hbound

/-- The manuscript's orbit inequality, now derived from an actual
normalized Hamilton route and its extracted profile rather than from three
abstract counting premises. -/
theorem route_profile_orbit_inequality {route : List Perm7}
    (hroute : IsHamiltonianRoute route) (hnormal : IsNormalizedRoute route)
    (x : CheapCoverProfile) (hadm : x.admissible)
    (hx1 : costOneCount route = 4320 - x.r)
    (hx2 : costTwoCount route = 720 + x.r - x.q) :
    120 + ceilDivSix x.r ≤ x.r + x.q := by
  have hsCard0 := runStartSet_card hroute
  have hcCard0 := chainStartSet_card hroute
  have hpart := route_edge_count_partition hroute.1
  have hrouteLen := hamiltonian_route_length hroute
  have hsCard : (runStartSet route).card = 720 + x.r := by
    dsimp [CheapCoverProfile.admissible] at hadm
    omega
  have hcCard : (chainStartSet route).card = x.q := by
    dsimp [CheapCoverProfile.admissible] at hadm
    omega
  have hfit0 := runStartSet_card_le_six_mul_touchedBlocks route
  have hrank0 := touchedBlocks_card_le_run_excess_add_chains hroute hnormal
  have hfit : 720 + x.r ≤ 6 * (touchedBlocks route).card := by omega
  have hrank : (touchedBlocks route).card ≤ x.r + x.q := by omega
  exact orbit_inequality_of_counts hfit hrank (Nat.le_refl x.q)

end Superperm7
