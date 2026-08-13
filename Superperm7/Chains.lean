/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE); this file is
additionally subject to the upstream MIT notice below.

Adapted from https://github.com/BGray-wrl/superperm6
  file:   formal-verification/Superperm6/Chains.lean
  commit: d8a932d8f61d80b0bcfc737bd0e235a8300449c4
  upstream copyright: Copyright (c) 2026 Benjamin Grayzel — MIT License (reproduced in NOTICE).
Local modifications (port from six to seven symbols; see docs/PORT_LOG.md): block length 6, gap lengths <= 5; single-quantifier restatements.
-/
import Superperm7.Section5Core

/-!
# Route-side chains, trails, and faces

This file materializes the maximal cost-one/two chains of a normalized
Hamilton route.  A chain is represented by its successive cost-one run
starts.  Its internal successor relation is the route-specific permutation
`T = F * A`; an internal step is retained precisely when its destination is
an actual cheap destination of the route.
-/

namespace Superperm7

/-! ## Cost-one runs and their endpoints -/

/-- The last state of the cost-one run starting at `s`. -/
noncomputable def runEnd (route : List Perm7) (s : RunStart route) : Perm7 :=
  Rinv (runStartPerm route s).1

/-- The states of the cost-one run, in route order. -/
noncomputable def runSegment (route : List Perm7) (s : RunStart route) :
    List Perm7 :=
  (List.range (runReturnTime route s)).map fun n =>
    (rotationPerm7 ^ n) s.1

theorem R_runEnd_eq (route : List Perm7) (s : RunStart route) :
    R (runEnd route s) = (runStartPerm route s).1 := by
  rw [runEnd, runStartPerm_apply]
  change R ((R^[6]) ((rotationPerm7 ^ runReturnTime route s) s.1)) =
    (rotationPerm7 ^ runReturnTime route s) s.1
  have hR6 := R_order_seven
      ((rotationPerm7 ^ runReturnTime route s) s.1)
  simpa [Function.iterate_succ_apply'] using hR6

theorem runEnd_eq_iterate (route : List Perm7) (s : RunStart route) :
    runEnd route s =
      (R^[runReturnTime route s - 1]) s.1 := by
  have htpos := (runReturnTime_spec route s).1
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (by omega :
    runReturnTime route s ≠ 0)
  rw [hn]
  simp only [Nat.succ_sub_one]
  apply R_injective
  rw [R_runEnd_eq, runStartPerm_apply]
  simp only [nextRunStart]
  rw [hn]
  change (rotationPerm7 ^ (n + 1)) s.1 = R ((R^[n]) s.1)
  rw [pow_succ', Equiv.Perm.mul_apply, rotationPerm7_pow_apply]
  rfl

@[simp] theorem runSegment_length (route : List Perm7)
    (s : RunStart route) :
    (runSegment route s).length = runReturnTime route s := by
  simp [runSegment]

theorem runSegment_ne_nil (route : List Perm7) (s : RunStart route) :
    runSegment route s ≠ [] := by
  intro hnil
  have hlen := congrArg List.length hnil
  simp [runSegment] at hlen
  exact (Nat.ne_of_gt (runReturnTime_spec route s).1) hlen

@[simp] theorem runSegment_head (route : List Perm7) (s : RunStart route) :
    (runSegment route s).head (runSegment_ne_nil route s) = s.1 := by
  simp [runSegment, (runReturnTime_spec route s).1]

theorem runSegment_getLast (route : List Perm7) (s : RunStart route) :
    (runSegment route s).getLast (runSegment_ne_nil route s) =
      runEnd route s := by
  rw [runEnd_eq_iterate]
  simp [runSegment, List.getLast_map]
  rw [rotationPerm7_pow_apply]

theorem runEnd_idxOf {route : List Perm7}
    (hroute : IsHamiltonianRoute route) (s : RunStart route) :
    route.idxOf (runEnd route s) =
      route.idxOf s.1 + (runReturnTime route s - 1) := by
  rw [runEnd_eq_iterate, ← rotationPerm7_pow_apply]
  apply idxOf_rotationPerm7_pow_before_return hroute
  have htpos := (runReturnTime_spec route s).1
  omega

/-- Every adjacent pair within a run is a genuine cost-one route edge. -/
theorem runSegment_isChain_cost_one {route : List Perm7}
    (hroute : IsHamiltonianRoute route) (s : RunStart route) :
    (runSegment route s).IsChain fun x y =>
      [x, y] <:+: route ∧ d x y = 1 := by
  rw [List.isChain_iff_getElem]
  intro i hi
  simp only [runSegment_length] at hi
  simp only [runSegment, List.getElem_map, List.getElem_range]
  constructor
  · rw [List.infix_iff_getElem?]
    let k := route.idxOf s.1 + i
    refine ⟨k, ?_, ?_⟩
    · simp only [List.length_cons, List.length_nil]
      have hidxNext :=
        idxOf_rotationPerm7_pow_before_return hroute s (i + 1) (by omega)
      have hmem := hroute.2 ((rotationPerm7 ^ (i + 1)) s.1)
      have hbound := List.idxOf_lt_length_iff.mpr hmem
      omega
    · intro j hj
      simp only [List.length_cons, List.length_nil] at hj
      interval_cases j
      · simp only [List.getElem_cons_zero]
        have hidx :=
          idxOf_rotationPerm7_pow_before_return hroute s i (by omega)
        have hbound := List.idxOf_lt_length_iff.mpr
          (hroute.2 ((rotationPerm7 ^ i) s.1))
        have hget := List.getElem?_eq_getElem hbound
        rw [List.getElem_idxOf hbound] at hget
        simpa [k, hidx, Nat.add_comm] using hget
      · simp only [List.getElem_cons_succ, List.getElem_cons_zero]
        have hidx :=
          idxOf_rotationPerm7_pow_before_return hroute s (i + 1) (by omega)
        have hbound := List.idxOf_lt_length_iff.mpr
          (hroute.2 ((rotationPerm7 ^ (i + 1)) s.1))
        have hget := List.getElem?_eq_getElem hbound
        rw [List.getElem_idxOf hbound] at hget
        simpa [k, hidx, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using hget
  · rw [pow_succ', Equiv.Perm.mul_apply]
    exact (cost_one_successor _ _).2 rfl

/-- A cost-one run is a literal contiguous segment of the Hamilton route. -/
theorem run_is_route_segment {route : List Perm7}
    (hroute : IsHamiltonianRoute route) (s : RunStart route) :
    runSegment route s <:+: route := by
  rw [List.infix_iff_getElem?]
  refine ⟨route.idxOf s.1, ?_, ?_⟩
  · have htpos := (runReturnTime_spec route s).1
    have hlast := runEnd_idxOf hroute s
    have hmem := hroute.2 (runEnd route s)
    have hbound := List.idxOf_lt_length_iff.mpr hmem
    simp only [runSegment_length]
    omega
  · intro i hi
    simp only [runSegment_length] at hi
    have hidx := idxOf_rotationPerm7_pow_before_return hroute s i hi
    have hmem := hroute.2 ((rotationPerm7 ^ i) s.1)
    have hbound := List.idxOf_lt_length_iff.mpr hmem
    have hget := List.getElem?_eq_getElem hbound
    rw [List.getElem_idxOf hbound] at hget
    simp only [runSegment, List.getElem_map, List.getElem_range]
    simpa [hidx, Nat.add_comm] using hget

theorem runEnd_exit_cost_ne_one {route : List Perm7}
    (hroute : IsHamiltonianRoute route) (s : RunStart route) {y : Perm7}
    (hedge : [runEnd route s, y] <:+: route) :
    d (runEnd route s) y ≠ 1 := by
  intro hone
  have hyDest :=
    pair_infix_mem_costOneDestinations hedge hone
  have hy : y = (runStartPerm route s).1 := by
    rw [(cost_one_successor _ _).mp hone, R_runEnd_eq]
  rw [hy] at hyDest
  exact (Finset.mem_sdiff.mp (runStartPerm route s).2).2 (by
    simpa using hyDest)

/-! ## The deterministic cost-two successor relation -/

/-- `s ⟶ t` means that `t` is the selected `T`-successor of `s` and is
the destination of an actual cost-at-most-two route edge. -/
noncomputable def IsChainStep (route : List Perm7)
    (s t : RunStart route) : Prop :=
  touchedTPerm route (runStartTouchedState route s) =
      runStartTouchedState route t ∧
    t.1 ∈ cheapTwoDestinations route

noncomputable instance (route : List Perm7) (s t : RunStart route) :
    Decidable (IsChainStep route s t) := by
  unfold IsChainStep
  infer_instance

theorem IsChainStep.right_unique {route : List Perm7}
    {s t u : RunStart route}
    (hst : IsChainStep route s t) (hsu : IsChainStep route s u) :
    t = u := by
  apply Subtype.ext
  exact congrArg (fun p : TouchedState route => p.1)
    (hst.1.symm.trans hsu.1)

theorem IsChainStep.left_unique {route : List Perm7}
    {s t u : RunStart route}
    (hsu : IsChainStep route s u) (htu : IsChainStep route t u) :
    s = t := by
  apply Subtype.ext
  have h := (touchedTPerm route).injective (hsu.1.trans htu.1.symm)
  exact congrArg (fun p : TouchedState route => p.1) h

/-- The optional deterministic successor inside a chain. -/
noncomputable def chainSucc? (route : List Perm7)
    (s : RunStart route) : Option (RunStart route) :=
  if h : ∃ t, IsChainStep route s t then
    some (Classical.choose h)
  else none

theorem chainSucc?_eq_some_iff (route : List Perm7)
    (s t : RunStart route) :
    chainSucc? route s = some t ↔ IsChainStep route s t := by
  classical
  constructor
  · intro h
    simp only [chainSucc?] at h
    split at h
    next hex =>
      have hc := Classical.choose_spec hex
      have heq : Classical.choose hex = t := Option.some.inj h
      simpa [heq] using hc
    next hnone => simp at h
  · intro hst
    simp only [chainSucc?]
    split
    next hex =>
      congr 1
      exact IsChainStep.right_unique (Classical.choose_spec hex) hst
    next hnone => exact False.elim (hnone ⟨t, hst⟩)

theorem chainSucc?_eq_none_iff (route : List Perm7)
    (s : RunStart route) :
    chainSucc? route s = none ↔ ¬ ∃ t, IsChainStep route s t := by
  classical
  simp [chainSucc?]

theorem IsChainStep.idxOf_lt {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    {s t : RunStart route} (hst : IsChainStep route s t) :
    route.idxOf s.1 < route.idxOf t.1 := by
  obtain ⟨u, huT, huEarlier⟩ :=
    touchedT_predecessor_earlier_of_mem_cheapTwoDestinations
      hroute hnormal t hst.2
  have hus : u = s := by
    apply Subtype.ext
    have hstate : runStartTouchedState route u =
        runStartTouchedState route s := by
      apply (touchedTPerm route).injective
      exact huT.trans hst.1.symm
    exact congrArg (fun p : TouchedState route => p.1) hstate
  simpa [hus] using huEarlier

private theorem F_injective : Function.Injective F :=
  insertionPerm7.injective

/-- Conversely, every retained `T`-step is the actual cost-two edge leaving
the source run. -/
theorem IsChainStep.route_edge {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    {s t : RunStart route} (hst : IsChainStep route s t) :
    [runEnd route s, t.1] <:+: route ∧
      d (runEnd route s) t.1 = 2 := by
  obtain ⟨x, hxEdge, hxCheap⟩ :=
    mem_cheapTwoDestinations_gives_edge hst.2
  have htNotOne : d x t.1 ≠ 1 := by
    intro hone
    have htDest := pair_infix_mem_costOneDestinations hxEdge hone
    exact (Finset.mem_sdiff.mp t.2).2 (by simpa using htDest)
  have hidx := idxOf_succ_of_pair_infix hroute.1
    (hroute.2 x) (hroute.2 t.1) hxEdge
  have hxt : x ≠ t.1 := by
    intro h
    subst x
    simp at hidx
  have hpos := d_pos_of_ne hxt
  have htwo : d x t.1 = 2 := by omega
  have htN : t.1 = N₂ x :=
    normalized_cost_two_edge hnormal hxEdge htwo
  have htFR : t.1 = F (R x) := by
    rw [htN, N₂_eq_F_R]
  have htFA : t.1 = F (runStartPerm route s).1 := by
    have hval := congrArg (fun p : TouchedState route => p.1) hst.1
    simpa using
      ((touchedTPerm_runStartTouchedState_val route s).symm.trans hval).symm
  have hAR : (runStartPerm route s).1 = R x := by
    apply F_injective
    exact htFA.symm.trans htFR
  have hxEnd : x = runEnd route s := by
    apply R_injective
    exact hAR.symm.trans (R_runEnd_eq route s).symm
  subst x
  exact ⟨hxEdge, htwo⟩

theorem cost_two_step_is_T {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (s : RunStart route) {y : Perm7}
    (hedge : [runEnd route s, y] <:+: route)
    (hcost : d (runEnd route s) y = 2) :
    let t : RunStart route :=
      ⟨y, target_runStart_of_cost_ne_one hroute hedge (by omega)⟩
    y = N₂ (runEnd route s) ∧
      y = F (runStartPerm route s).1 ∧
      touchedTPerm route (runStartTouchedState route s) =
        runStartTouchedState route t ∧
      IsChainStep route s t := by
  dsimp
  let t : RunStart route :=
    ⟨y, target_runStart_of_cost_ne_one hroute hedge (by omega)⟩
  have hyN : y = N₂ (runEnd route s) :=
    normalized_cost_two_edge hnormal hedge hcost
  have hyF : y = F (runStartPerm route s).1 := by
    rw [hyN, N₂_eq_F_R, R_runEnd_eq]
  have hT : touchedTPerm route (runStartTouchedState route s) =
      runStartTouchedState route t := by
    apply Subtype.ext
    rw [touchedTPerm_runStartTouchedState_val]
    exact hyF.symm
  have hcheap : y ∈ cheapTwoDestinations route :=
    pair_infix_mem_cheapTwoDestinations hedge (by omega)
  exact ⟨hyN, hyF, hT, hT, hcheap⟩

/-! ## Materialized chain lists -/

private noncomputable def chainRunAux (route : List Perm7) :
    ℕ → RunStart route → List (RunStart route)
  | 0, s => [s]
  | fuel + 1, s =>
      s :: match chainSucc? route s with
        | none => []
        | some t => chainRunAux route fuel t

/-- The maximal deterministic `T`-walk beginning at a chain start. -/
noncomputable def chainRunStarts (route : List Perm7)
    (c : ChainStart route) : List (RunStart route) :=
  chainRunAux route (route.length - route.idxOf c.1) (chainAsRunStart c)

private theorem chainRunAux_ne_nil (route : List Perm7)
    (fuel : ℕ) (s : RunStart route) :
    chainRunAux route fuel s ≠ [] := by
  cases fuel <;> simp [chainRunAux]

private theorem chainRunAux_head (route : List Perm7)
    (fuel : ℕ) (s : RunStart route) :
    (chainRunAux route fuel s).head
      (chainRunAux_ne_nil route fuel s) = s := by
  cases fuel <;> simp [chainRunAux]

private theorem chainRunAux_head?_eq (route : List Perm7)
    (fuel : ℕ) (s : RunStart route) :
    (chainRunAux route fuel s).head? = some s := by
  cases fuel <;> simp [chainRunAux]

private theorem getLast?_cons_of_ne_nil {α : Type*}
    (a : α) {l : List α} (h : l ≠ []) :
    (a :: l).getLast? = l.getLast? := by
  rw [List.getLast?_eq_getLast (by simp),
    List.getLast?_eq_getLast h, List.getLast_cons h]

theorem chainRunStarts_ne_nil (route : List Perm7)
    (c : ChainStart route) :
    chainRunStarts route c ≠ [] :=
  chainRunAux_ne_nil route _ _

@[simp] theorem chainRunStarts_head (route : List Perm7)
    (c : ChainStart route) :
    (chainRunStarts route c).head (chainRunStarts_ne_nil route c) =
      chainAsRunStart c := by
  exact chainRunAux_head route _ _

@[simp] theorem chainRunStarts_head?_eq (route : List Perm7)
    (c : ChainStart route) :
    (chainRunStarts route c).head? = some (chainAsRunStart c) :=
  chainRunAux_head?_eq route _ _

private theorem chainRunAux_isChain (route : List Perm7)
    (fuel : ℕ) (s : RunStart route) :
    (chainRunAux route fuel s).IsChain (IsChainStep route) := by
  induction fuel generalizing s with
  | zero => simp [chainRunAux]
  | succ fuel ih =>
      simp only [chainRunAux]
      cases hsucc : chainSucc? route s with
      | none => simp
      | some t =>
          simp only
          rw [List.isChain_cons]
          constructor
          · intro y hy
            rw [chainRunAux_head?_eq] at hy
            have hyt : y = t := Option.some.inj hy.symm
            subst y
            exact (chainSucc?_eq_some_iff route s t).mp hsucc
          · exact ih t

theorem chainRunStarts_isChain (route : List Perm7)
    (c : ChainStart route) :
    (chainRunStarts route c).IsChain (IsChainStep route) :=
  chainRunAux_isChain route _ _

private theorem chainRunAux_last_terminal {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (fuel : ℕ) (s : RunStart route)
    (hbudget : route.length ≤ route.idxOf s.1 + fuel)
    (last : RunStart route)
    (hlast : (chainRunAux route fuel s).getLast? = some last) :
    chainSucc? route last = none := by
  induction fuel generalizing s with
  | zero =>
      have hlt := List.idxOf_lt_length_iff.mpr (hroute.2 s.1)
      omega
  | succ fuel ih =>
      cases hsucc : chainSucc? route s with
      | none =>
          have hls : last = s := by
            simpa [chainRunAux, hsucc] using (Option.some.inj hlast).symm
          simpa [hls] using hsucc
      | some t =>
          have hlast' : (chainRunAux route fuel t).getLast? = some last := by
            rw [show chainRunAux route (fuel + 1) s =
                s :: chainRunAux route fuel t by
              simp [chainRunAux, hsucc]] at hlast
            rw [getLast?_cons_of_ne_nil s
              (chainRunAux_ne_nil route fuel t)] at hlast
            exact hlast
          apply ih t
          have hstep := (chainSucc?_eq_some_iff route s t).mp hsucc
          have hlt := hstep.idxOf_lt hroute hnormal
          omega
          exact hlast'

/-- The final run start in a materialized chain. -/
noncomputable def chainLast (route : List Perm7)
    (c : ChainStart route) : RunStart route :=
  (chainRunStarts route c).getLast (chainRunStarts_ne_nil route c)

theorem chainLast_mem (route : List Perm7) (c : ChainStart route) :
    chainLast route c ∈ chainRunStarts route c :=
  List.getLast_mem _

theorem chainLast_terminal {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (c : ChainStart route) :
    chainSucc? route (chainLast route c) = none := by
  unfold chainLast chainRunStarts
  refine chainRunAux_last_terminal hroute hnormal
    (route.length - route.idxOf c.1) (chainAsRunStart c) ?_ _ ?_
  · change route.length ≤ route.idxOf c.1 +
      (route.length - route.idxOf c.1)
    have hcMem := hroute.2 c.1
    have hcBound := List.idxOf_lt_length_iff.mpr hcMem
    omega
  · exact List.getLast?_eq_getLast _

/-- The last run of a chain cannot leave by a cost-two route edge. -/
theorem chainLast_exit_cost_ne_two {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (c : ChainStart route) {y : Perm7}
    (hedge : [runEnd route (chainLast route c), y] <:+: route) :
    d (runEnd route (chainLast route c)) y ≠ 2 := by
  intro htwo
  let t : RunStart route :=
    ⟨y, target_runStart_of_cost_ne_one hroute hedge (by omega)⟩
  have hstep : IsChainStep route (chainLast route c) t :=
    (cost_two_step_is_T hroute hnormal (chainLast route c) hedge htwo).2.2.2
  have hsome := (chainSucc?_eq_some_iff route (chainLast route c) t).2 hstep
  rw [chainLast_terminal hroute hnormal c] at hsome
  simp at hsome

/-! ## The chain partition -/

private theorem chainRunAux_closed {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (fuel : ℕ) (start : RunStart route)
    (hbudget : route.length ≤ route.idxOf start.1 + fuel)
    {s t : RunStart route}
    (hs : s ∈ chainRunAux route fuel start)
    (hst : IsChainStep route s t) :
    t ∈ chainRunAux route fuel start := by
  induction fuel generalizing start with
  | zero =>
      have hlt := List.idxOf_lt_length_iff.mpr (hroute.2 start.1)
      omega
  | succ fuel ih =>
      cases hsucc : chainSucc? route start with
      | none =>
          have hsEq : s = start := by
            simpa [chainRunAux, hsucc] using hs
          subst s
          have hsome :=
            (chainSucc?_eq_some_iff route start t).2 hst
          rw [hsucc] at hsome
          simp at hsome
      | some next =>
          have hstep :=
            (chainSucc?_eq_some_iff route start next).mp hsucc
          have hshape : chainRunAux route (fuel + 1) start =
              start :: chainRunAux route fuel next := by
            simp [chainRunAux, hsucc]
          rw [hshape] at hs ⊢
          rcases List.mem_cons.mp hs with hsEq | hsTail
          · subst s
            have htn : t = next :=
              IsChainStep.right_unique hst hstep
            subst t
            apply List.mem_cons_of_mem
            have hm := List.head_mem
              (chainRunAux_ne_nil route fuel next)
            simpa only [chainRunAux_head] using hm
          · exact List.mem_cons_of_mem _ (ih next (by
                have hidx := hstep.idxOf_lt hroute hnormal
                omega) hsTail)

theorem chainRunStarts_closed {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (c : ChainStart route) {s t : RunStart route}
    (hs : s ∈ chainRunStarts route c)
    (hst : IsChainStep route s t) :
    t ∈ chainRunStarts route c := by
  apply chainRunAux_closed hroute hnormal
  · change route.length ≤ route.idxOf c.1 +
      (route.length - route.idxOf c.1)
    have hlt := List.idxOf_lt_length_iff.mpr (hroute.2 c.1)
    omega
  · exact hs
  · exact hst

private theorem exists_rel_predecessor_of_mem_cons
    {α : Type*} {Rel : α → α → Prop} {a s : α} :
    ∀ {tail : List α},
      (a :: tail).IsChain Rel →
      s ∈ a :: tail →
      s ≠ a →
      ∃ u, u ∈ a :: tail ∧ Rel u s
  | [], _hchain, hmem, hne => by
      simp only [List.mem_singleton] at hmem
      exact False.elim (hne hmem)
  | b :: tail, hchain, hmem, hne => by
      have hab : Rel a b := hchain.rel_head
      have htail : (b :: tail).IsChain Rel := hchain.tail
      rcases List.mem_cons.mp hmem with hsa | hmemTail
      · exact False.elim (hne hsa)
      · by_cases hsb : s = b
        · subst s
          exact ⟨a, by simp, hab⟩
        · obtain ⟨u, hu, hus⟩ :=
            exists_rel_predecessor_of_mem_cons htail hmemTail hsb
          exact ⟨u, List.mem_cons_of_mem _ hu, hus⟩

private theorem chainRunStarts_predecessor {route : List Perm7}
    (c : ChainStart route) (s : RunStart route)
    (hmem : s ∈ chainRunStarts route c)
    (hne : s ≠ chainAsRunStart c) :
    ∃ u, u ∈ chainRunStarts route c ∧ IsChainStep route u s := by
  obtain ⟨a, tail, hshape⟩ :=
    List.exists_cons_of_ne_nil (chainRunStarts_ne_nil route c)
  have ha : a = chainAsRunStart c := by
    have hhead := chainRunStarts_head?_eq route c
    rw [hshape] at hhead
    simpa using hhead
  subst a
  rw [hshape] at hmem ⊢
  exact exists_rel_predecessor_of_mem_cons
    (by simpa [hshape] using chainRunStarts_isChain route c)
    hmem hne

theorem chainStart_not_mem_cheapTwoDestinations
    {route : List Perm7} (c : ChainStart route) :
    c.1 ∉ cheapTwoDestinations route := by
  have hnot := (Finset.mem_sdiff.mp c.2).2
  intro hc
  exact hnot (by simpa using hc)

theorem chainStart_mem_chainRunStarts_iff
    (route : List Perm7) (c d : ChainStart route) :
    chainAsRunStart c ∈ chainRunStarts route d ↔ c = d := by
  constructor
  · intro hmem
    by_cases heq : chainAsRunStart c = chainAsRunStart d
    · exact Subtype.ext
        (congrArg (fun s : RunStart route => s.1) heq)
    · obtain ⟨u, _hu, hstep⟩ :=
        chainRunStarts_predecessor d (chainAsRunStart c) hmem heq
      exact False.elim
        (chainStart_not_mem_cheapTwoDestinations c hstep.2)
  · intro hcd
    subst d
    have hmem := List.head_mem (chainRunStarts_ne_nil route c)
    simpa only [chainRunStarts_head] using hmem

theorem runStart_mem_some_chain {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (s : RunStart route) :
    ∃ c : ChainStart route, s ∈ chainRunStarts route c := by
  by_cases hsChain : s.1 ∈ chainStartSet route
  · let c : ChainStart route := ⟨s.1, hsChain⟩
    have hsc : s = chainAsRunStart c := Subtype.ext rfl
    refine ⟨c, ?_⟩
    rw [hsc]
    exact (chainStart_mem_chainRunStarts_iff route c c).2 rfl
  · have hsCheap : s.1 ∈ cheapTwoDestinations route := by
      simpa [chainStartSet] using hsChain
    obtain ⟨u, huT, huEarlier⟩ :=
      touchedT_predecessor_earlier_of_mem_cheapTwoDestinations
        hroute hnormal s hsCheap
    obtain ⟨c, huc⟩ := runStart_mem_some_chain hroute hnormal u
    have hstep : IsChainStep route u s := ⟨huT, hsCheap⟩
    exact ⟨c, chainRunStarts_closed hroute hnormal c huc hstep⟩
termination_by route.idxOf s.1
decreasing_by exact huEarlier

theorem runStart_chain_unique {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (s : RunStart route) (c d : ChainStart route)
    (hc : s ∈ chainRunStarts route c)
    (hd : s ∈ chainRunStarts route d) :
    c = d := by
  by_cases hsChain : s.1 ∈ chainStartSet route
  · let e : ChainStart route := ⟨s.1, hsChain⟩
    have hse : s = chainAsRunStart e := Subtype.ext rfl
    have hec : e = c :=
      (chainStart_mem_chainRunStarts_iff route e c).1 (hse ▸ hc)
    have hed : e = d :=
      (chainStart_mem_chainRunStarts_iff route e d).1 (hse ▸ hd)
    exact hec.symm.trans hed
  · have hsc : s ≠ chainAsRunStart c := by
      intro h
      apply hsChain
      rw [congrArg Subtype.val h]
      exact c.2
    have hsd : s ≠ chainAsRunStart d := by
      intro h
      apply hsChain
      rw [congrArg Subtype.val h]
      exact d.2
    obtain ⟨u, huc, hus⟩ :=
      chainRunStarts_predecessor c s hc hsc
    obtain ⟨v, hvd, hvs⟩ :=
      chainRunStarts_predecessor d s hd hsd
    have huv : u = v := IsChainStep.left_unique hus hvs
    subst v
    exact runStart_chain_unique hroute hnormal u c d huc hvd
termination_by route.idxOf s.1
decreasing_by exact hus.idxOf_lt hroute hnormal

/-- Every run start occurs in one and only one materialized chain. -/
theorem chains_partition_runStarts {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (s : RunStart route) :
    ∃! c : ChainStart route, s ∈ chainRunStarts route c := by
  obtain ⟨c, hc⟩ := runStart_mem_some_chain hroute hnormal s
  exact ⟨c, hc, fun d hd => runStart_chain_unique
    hroute hnormal s d c hd hc⟩

/-! ## Route order on the chains -/

theorem runEnd_idxOf_lt_of_runStart_idxOf_lt {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (s t : RunStart route)
    (hst : route.idxOf s.1 < route.idxOf t.1) :
    route.idxOf (runEnd route s) < route.idxOf t.1 := by
  by_contra hnot
  have hle : route.idxOf t.1 ≤ route.idxOf (runEnd route s) :=
    Nat.le_of_not_gt hnot
  let j := route.idxOf t.1 - route.idxOf s.1
  have hjpos : 0 < j := by
    dsimp [j]
    omega
  have hend := runEnd_idxOf hroute s
  have hjlt : j < runReturnTime route s := by
    dsimp [j]
    omega
  have hidx :=
    idxOf_rotationPerm7_pow_before_return hroute s j hjlt
  have hidxEq :
      route.idxOf ((rotationPerm7 ^ j) s.1) = route.idxOf t.1 := by
    dsimp [j] at hidx ⊢
    omega
  have hstate : (rotationPerm7 ^ j) s.1 = t.1 :=
    ((List.idxOf_inj (hroute.2 t.1)).mp hidxEq.symm).symm
  exact runReturnTime_min route s hjlt
    ⟨hjpos, by rw [hstate]; exact t.2⟩

private theorem forall_mem_of_isChain_from_head
    {α : Type*} {Rel : α → α → Prop} {P : α → Prop}
    (hstep : ∀ {a b}, Rel a b → P a → P b) :
    ∀ {a : α} {tail : List α},
      (a :: tail).IsChain Rel →
      P a →
      ∀ x ∈ a :: tail, P x
  | a, [], _hchain, ha, x, hx => by
      have hxa : x = a := by simpa only [List.mem_singleton] using hx
      subst x
      exact ha
  | a, b :: tail, hchain, ha, x, hx => by
      rcases List.mem_cons.mp hx with hxa | hxTail
      · simpa [hxa] using ha
      · exact forall_mem_of_isChain_from_head
          (Rel := Rel) (P := P) hstep hchain.tail
          (hstep hchain.rel_head ha) x hxTail

theorem chainRunStart_head_idxOf_le {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (c : ChainStart route) {s : RunStart route}
    (hs : s ∈ chainRunStarts route c) :
    route.idxOf c.1 ≤ route.idxOf s.1 := by
  obtain ⟨a, tail, hshape⟩ :=
    List.exists_cons_of_ne_nil (chainRunStarts_ne_nil route c)
  have ha : a = chainAsRunStart c := by
    have hh := chainRunStarts_head?_eq route c
    rw [hshape] at hh
    simpa using hh
  subst a
  apply forall_mem_of_isChain_from_head
      (Rel := IsChainStep route)
      (P := fun u => route.idxOf c.1 ≤ route.idxOf u.1)
      (fun hab ha => ha.trans (hab.idxOf_lt hroute hnormal).le)
      (by simpa [hshape] using chainRunStarts_isChain route c)
      (by
        change route.idxOf c.1 ≤ route.idxOf c.1
        exact le_rfl)
      s
  simpa [hshape] using hs

theorem IsChainStep.idxOf_lt_chainStart_of_lt {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    {s t : RunStart route} (hst : IsChainStep route s t)
    (c : ChainStart route)
    (hsc : route.idxOf s.1 < route.idxOf c.1) :
    route.idxOf t.1 < route.idxOf c.1 := by
  have hend :=
    runEnd_idxOf_lt_of_runStart_idxOf_lt hroute s (chainAsRunStart c) hsc
  change route.idxOf (runEnd route s) < route.idxOf c.1 at hend
  have hedge := hst.route_edge hroute hnormal
  have hidx := idxOf_succ_of_pair_infix hroute.1
    (hroute.2 (runEnd route s)) (hroute.2 t.1) hedge.1
  have hle : route.idxOf t.1 ≤ route.idxOf c.1 := by omega
  have hne : route.idxOf t.1 ≠ route.idxOf c.1 := by
    intro heq
    have htc : t.1 = c.1 :=
      ((List.idxOf_inj (hroute.2 c.1)).mp heq.symm).symm
    exact chainStart_not_mem_cheapTwoDestinations c (by
      rw [← htc]
      exact hst.2)
  omega

theorem chainRunStart_idxOf_lt_of_head_lt {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (c d : ChainStart route)
    (hcd : route.idxOf c.1 < route.idxOf d.1)
    {s : RunStart route} (hs : s ∈ chainRunStarts route c) :
    route.idxOf s.1 < route.idxOf d.1 := by
  obtain ⟨a, tail, hshape⟩ :=
    List.exists_cons_of_ne_nil (chainRunStarts_ne_nil route c)
  have ha : a = chainAsRunStart c := by
    have hh := chainRunStarts_head?_eq route c
    rw [hshape] at hh
    simpa using hh
  subst a
  apply forall_mem_of_isChain_from_head
      (Rel := IsChainStep route)
      (P := fun u => route.idxOf u.1 < route.idxOf d.1)
      (fun hab hu => hab.idxOf_lt_chainStart_of_lt hroute hnormal d hu)
      (by simpa [hshape] using chainRunStarts_isChain route c)
      (by simpa using hcd)
      s
  simpa [hshape] using hs

private def finsetSubtypeList {α : Type*} [DecidableEq α]
    (S : Finset α) (l : List α) : List S :=
  l.filterMap fun x => if hx : x ∈ S then some ⟨x, hx⟩ else none

private theorem mem_finsetSubtypeList {α : Type*} [DecidableEq α]
    (S : Finset α) (l : List α) (x : S) :
    x ∈ finsetSubtypeList S l ↔ x.1 ∈ l := by
  simp [finsetSubtypeList]

private theorem map_finsetSubtypeList {α : Type*} [DecidableEq α]
    (S : Finset α) (l : List α) :
    (finsetSubtypeList S l).map Subtype.val =
      l.filter (· ∈ S) := by
  induction l with
  | nil => simp [finsetSubtypeList]
  | cons a l ih =>
      simp only [finsetSubtypeList, List.filterMap_cons, List.filter_cons]
      split <;> simp_all [finsetSubtypeList]

/-- All chain starts, in their linear route order. -/
def routeChainStarts (route : List Perm7) : List (ChainStart route) :=
  finsetSubtypeList (chainStartSet route) route

@[simp] theorem mem_routeChainStarts (route : List Perm7)
    (c : ChainStart route) :
    c ∈ routeChainStarts route ↔ c.1 ∈ route :=
  mem_finsetSubtypeList _ _ _

theorem routeChainStarts_complete {route : List Perm7}
    (hroute : IsHamiltonianRoute route) (c : ChainStart route) :
    c ∈ routeChainStarts route :=
  (mem_routeChainStarts route c).2 (hroute.2 c.1)

theorem routeChainStarts_nodup {route : List Perm7}
    (hroute : IsHamiltonianRoute route) :
    (routeChainStarts route).Nodup := by
  have hn : (route.filter (· ∈ chainStartSet route)).Nodup :=
    (List.filter_sublist).nodup hroute.1
  rw [← map_finsetSubtypeList] at hn
  exact hn.of_map Subtype.val

private theorem route_pairwise_idxOf {route : List Perm7}
    (hnodup : route.Nodup) :
    route.Pairwise fun x y => route.idxOf x < route.idxOf y := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have himem : route[i] ∈ route := List.getElem_mem ..
  have hjmem : route[j] ∈ route := List.getElem_mem ..
  have hibound := List.idxOf_lt_length_iff.mpr himem
  have hjbound := List.idxOf_lt_length_iff.mpr hjmem
  have hiEq : route.idxOf route[i] = i :=
    hnodup.getElem_inj_iff.mp (List.getElem_idxOf hibound)
  have hjEq : route.idxOf route[j] = j :=
    hnodup.getElem_inj_iff.mp (List.getElem_idxOf hjbound)
  omega

theorem routeChainStarts_pairwise_idxOf {route : List Perm7}
    (hroute : IsHamiltonianRoute route) :
    (routeChainStarts route).Pairwise fun c d =>
      route.idxOf c.1 < route.idxOf d.1 := by
  have hp := (route_pairwise_idxOf hroute.1).sublist
    (List.filter_sublist :
      (route.filter (· ∈ chainStartSet route)).Sublist route)
  rw [← map_finsetSubtypeList] at hp
  exact (List.pairwise_map
    (f := fun c : ChainStart route => c.1)
    (R := fun x y : Perm7 => route.idxOf x < route.idxOf y)).mp hp

private theorem relation_of_pair_infix_isChain
    {α : Type*} {Rel : α → α → Prop}
    {l : List α} {a b : α}
    (hchain : l.IsChain Rel) (hpair : [a, b] <:+: l) :
    Rel a b := by
  rcases hpair with ⟨pre, post, hshape⟩
  exact (List.isChain_iff_forall_rel_of_append_cons_cons.mp hchain)
    (a := a) (b := b) (l₁ := pre) (l₂ := post)
    (by simpa [List.append_assoc] using hshape.symm)

theorem routeChainStarts_pair_idxOf_lt {route : List Perm7}
    (hroute : IsHamiltonianRoute route) {c d : ChainStart route}
    (hpair : [c, d] <:+: routeChainStarts route) :
    route.idxOf c.1 < route.idxOf d.1 := by
  apply relation_of_pair_infix_isChain
    (List.isChain_iff_pairwise.mpr
      (routeChainStarts_pairwise_idxOf hroute))
    hpair

private theorem routeChainStarts_no_between {route : List Perm7}
    (hroute : IsHamiltonianRoute route) {c d e : ChainStart route}
    (hpair : [c, d] <:+: routeChainStarts route)
    (hce : route.idxOf c.1 < route.idxOf e.1)
    (hed : route.idxOf e.1 ≤ route.idxOf d.1) :
    e = d := by
  rcases hpair with ⟨pre, post, hshape⟩
  have hpwShape :
      (pre ++ [c, d] ++ post).Pairwise (fun x y : ChainStart route =>
        route.idxOf x.1 < route.idxOf y.1) := by
    rw [hshape]
    exact routeChainStarts_pairwise_idxOf hroute
  have hpwCanon :
      (pre ++ c :: d :: post).Pairwise (fun x y : ChainStart route =>
        route.idxOf x.1 < route.idxOf y.1) := by
    simpa [List.append_assoc] using hpwShape
  have heMem : e ∈ pre ++ c :: d :: post := by
    have heAll := routeChainStarts_complete hroute e
    rw [← hshape] at heAll
    simpa [List.append_assoc] using heAll
  have hsplit := List.pairwise_append.mp hpwCanon
  rcases List.mem_append.mp heMem with hePre | heTail
  · have hec := hsplit.2.2 e hePre c (by simp)
    omega
  · rcases List.mem_cons.mp heTail with hec | heTail
    · subst e
      omega
    · rcases List.mem_cons.mp heTail with hedEq | hePost
      · exact hedEq
      · have htailPw := hsplit.2.1
        have hdPost := (List.pairwise_cons.mp
          (List.pairwise_cons.mp htailPw).2).1 e hePost
        omega

/-! ## Macroedge endpoints -/

def chainAlpha (route : List Perm7) (c : ChainStart route) : Triple :=
  alpha c.1

noncomputable def chainBeta (route : List Perm7)
    (c : ChainStart route) : Triple :=
  runMacroBeta route (chainLast route c)

theorem chainAlpha_eq_head (route : List Perm7) (c : ChainStart route) :
    chainAlpha route c =
      alpha ((chainRunStarts route c).head
        (chainRunStarts_ne_nil route c)).1 := by
  rw [chainRunStarts_head]
  rfl

theorem chainBeta_eq_last3 (route : List Perm7) (c : ChainStart route) :
    chainBeta route c =
      (permWord (runEnd route (chainLast route c))).drop 3 := rfl

/-! ## Consecutive chains and cost-three compatibility -/

private theorem pair_infix_succ_getElem {route : List Perm7}
    {x : Perm7} (hx : x ∈ route)
    (hnext : route.idxOf x + 1 < route.length) :
    [x, route[route.idxOf x + 1]] <:+: route := by
  rw [List.infix_iff_getElem?]
  refine ⟨route.idxOf x, ?_, ?_⟩
  · simp only [List.length_cons, List.length_nil]
    omega
  · intro i hi
    simp only [List.length_cons, List.length_nil] at hi
    interval_cases i
    · simp only [List.getElem_cons_zero]
      have hbound := List.idxOf_lt_length_iff.mpr hx
      have hget := List.getElem?_eq_getElem hbound
      rw [List.getElem_idxOf hbound] at hget
      simpa using hget
    · simp only [List.getElem_cons_succ, List.getElem_cons_zero]
      simpa [Nat.add_comm] using List.getElem?_eq_getElem hnext

private theorem route_pair_left_unique {route : List Perm7}
    (hroute : IsHamiltonianRoute route) {x y z : Perm7}
    (hxy : [x, y] <:+: route) (hzy : [z, y] <:+: route) :
    x = z := by
  have hix := idxOf_succ_of_pair_infix hroute.1
    (hroute.2 x) (hroute.2 y) hxy
  have hiz := idxOf_succ_of_pair_infix hroute.1
    (hroute.2 z) (hroute.2 y) hzy
  apply (List.idxOf_inj (hroute.2 x)).mp
  omega

/-- Consecutive chain starts in route order are joined by the unique route
edge leaving the last run of the first chain.  Its cost is three or high. -/
theorem consecutive_chains_route_edge {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    {c d : ChainStart route}
    (hpair : [c, d] <:+: routeChainStarts route) :
    [runEnd route (chainLast route c), d.1] <:+: route ∧
      (Superperm7.d (runEnd route (chainLast route c)) d.1 = 3 ∨
        4 ≤ Superperm7.d (runEnd route (chainLast route c)) d.1) := by
  have hcd := routeChainStarts_pair_idxOf_lt hroute hpair
  have hlastLt : route.idxOf (chainLast route c).1 < route.idxOf d.1 :=
    chainRunStart_idxOf_lt_of_head_lt hroute hnormal c d hcd
      (chainLast_mem route c)
  have hendLt :=
    runEnd_idxOf_lt_of_runStart_idxOf_lt hroute
      (chainLast route c) (chainAsRunStart d) hlastLt
  change route.idxOf (runEnd route (chainLast route c)) <
    route.idxOf d.1 at hendLt
  have hdBound := List.idxOf_lt_length_iff.mpr (hroute.2 d.1)
  have hnext :
      route.idxOf (runEnd route (chainLast route c)) + 1 <
        route.length := by
    omega
  let y :=
    route[route.idxOf (runEnd route (chainLast route c)) + 1]
  have hedge : [runEnd route (chainLast route c), y] <:+: route :=
    pair_infix_succ_getElem (hroute.2 _) hnext
  have hidxY := idxOf_succ_of_pair_infix hroute.1
    (hroute.2 (runEnd route (chainLast route c))) (hroute.2 y) hedge
  have hnotOne :=
    runEnd_exit_cost_ne_one hroute (chainLast route c) hedge
  have hnotTwo :=
    chainLast_exit_cost_ne_two hroute hnormal c hedge
  have hyNotCheap : y ∉ cheapTwoDestinations route := by
    intro hyCheap
    obtain ⟨x, hxEdge, hxCost⟩ :=
      mem_cheapTwoDestinations_gives_edge hyCheap
    have hx : x = runEnd route (chainLast route c) :=
      route_pair_left_unique hroute hxEdge hedge
    subst x
    have hne : runEnd route (chainLast route c) ≠ y := by
      intro heq
      have hidxY' := hidxY
      rw [← heq] at hidxY'
      omega
    have hpos := d_pos_of_ne hne
    omega
  have hyChain : y ∈ chainStartSet route := by
    simp [chainStartSet, hyNotCheap]
  let e : ChainStart route := ⟨y, hyChain⟩
  have hcLast :=
    chainRunStart_head_idxOf_le hroute hnormal c
      (chainLast_mem route c)
  have hendIdx := runEnd_idxOf hroute (chainLast route c)
  have hce : route.idxOf c.1 < route.idxOf e.1 := by
    dsimp [e]
    omega
  have hed : route.idxOf e.1 ≤ route.idxOf d.1 := by
    dsimp [e]
    omega
  have heq : e = d :=
    routeChainStarts_no_between hroute hpair hce hed
  have hyEq : y = d.1 :=
    congrArg (fun z : ChainStart route => z.1) heq
  rw [hyEq] at hedge hnotOne hnotTwo hidxY
  refine ⟨hedge, ?_⟩
  have hne : runEnd route (chainLast route c) ≠ d.1 := by
    intro h
    have hidxY' := hidxY
    rw [← h] at hidxY'
    omega
  have hpos := d_pos_of_ne hne
  omega

/-- `d p q = 3` says exactly that the last four symbols of `p` are the
first four of `q`.  Via `d_eq_iff_compatible` this is definitional, with no
search over pairs. -/
theorem cost_three_iff_endpoint_compatible : ∀ p q : Perm7,
    d p q = 3 ↔ (permWord p).drop 3 = alpha q := by
  intro p q
  rw [d_eq_iff_compatible (by omega)]
  unfold OverlapCompatible alpha
  simp only [permWord_length]

theorem consecutive_chains_compatible {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    {c d : ChainStart route}
    (hpair : [c, d] <:+: routeChainStarts route)
    (hthree : Superperm7.d
      (runEnd route (chainLast route c)) d.1 = 3) :
    chainBeta route c = chainAlpha route d := by
  rw [chainBeta_eq_last3]
  exact (cost_three_iff_endpoint_compatible _ _).mp hthree

end Superperm7
