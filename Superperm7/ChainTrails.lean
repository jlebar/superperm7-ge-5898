/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE); this file is
additionally subject to the upstream MIT notice below.

Adapted from https://github.com/BGray-wrl/superperm6
  file:   formal-verification/Superperm6/ChainTrails.lean
  commit: d8a932d8f61d80b0bcfc737bd0e235a8300449c4
  upstream copyright: Copyright (c) 2026 Benjamin Grayzel — MIT License (reproduced in NOTICE).
Local modifications (port from six to seven symbols; see docs/PORT_LOG.md): block length 6; single-quantifier restatements.
-/
import Superperm7.Chains

/-!
# Trails and face structure of route-side chains

This continuation of `Chains.lean` groups the route-ordered chains at
cost-three joins and constructs the first-return face permutation on chain
starts, including its bounded hole-gap data.
-/

namespace Superperm7

/-! ## A generic consecutive split -/

private def splitTrails {α : Type*} (good : α → α → Prop)
    [DecidableRel good] : List α → List (List α)
  | [] => []
  | [a] => [[a]]
  | a :: b :: rest =>
      if good a b then
        match splitTrails good (b :: rest) with
        | [] => [[a]]
        | trail :: trails => (a :: trail) :: trails
      else
        [a] :: splitTrails good (b :: rest)
termination_by l => l.length

private def breakDestinations {α : Type*} (good : α → α → Prop)
    [DecidableRel good] : List α → List α
  | a :: b :: rest =>
      if good a b then breakDestinations good (b :: rest)
      else b :: breakDestinations good (b :: rest)
  | _ => []

private theorem splitTrails_ne_nil_of_ne_nil
    {α : Type*} (good : α → α → Prop) [DecidableRel good]
    {l : List α} (hl : l ≠ []) :
    splitTrails good l ≠ [] := by
  cases l with
  | nil => exact False.elim (hl rfl)
  | cons a tail =>
      cases tail with
      | nil => simp [splitTrails]
      | cons b rest =>
          simp only [splitTrails]
          split
          · cases splitTrails good (b :: rest) <;> simp
          · simp

private theorem splitTrails_first
    {α : Type*} (good : α → α → Prop) [DecidableRel good]
    (a : α) (tail : List α) :
    ∃ trail trails,
      splitTrails good (a :: tail) = trail :: trails ∧
      trail.head? = some a := by
  induction tail generalizing a with
  | nil => exact ⟨[a], [], by simp [splitTrails]⟩
  | cons b rest ih =>
      by_cases hab : good a b
      · obtain ⟨trail, trails, hsplit, hhead⟩ := ih b
        refine ⟨a :: trail, trails, ?_, by simp⟩
        simp [splitTrails, hab, hsplit]
      · exact ⟨[a], splitTrails good (b :: rest), by
          simp [splitTrails, hab]⟩

private theorem splitTrails_flatten
    {α : Type*} (good : α → α → Prop) [DecidableRel good] :
    ∀ l : List α, (splitTrails good l).flatten = l := by
  intro l
  induction l with
  | nil => simp [splitTrails]
  | cons a tail ih =>
      cases tail with
      | nil => simp [splitTrails]
      | cons b rest =>
          by_cases hab : good a b
          · obtain ⟨trail, trails, hsplit, _hhead⟩ :=
              splitTrails_first good b rest
            have ih' : trail ++ trails.flatten = b :: rest := by
              simpa [hsplit] using ih
            simp [splitTrails, hab, hsplit, ih']
          · simp [splitTrails, hab, ih]

private theorem splitTrails_isChain
    {α : Type*} (good : α → α → Prop) [DecidableRel good] :
    ∀ l : List α, ∀ trail ∈ splitTrails good l,
      trail.IsChain good := by
  intro l
  induction l with
  | nil => simp [splitTrails]
  | cons a tail ih =>
      cases tail with
      | nil => simp [splitTrails]
      | cons b rest =>
          by_cases hab : good a b
          · obtain ⟨first, trails, hsplit, hhead⟩ :=
              splitTrails_first good b rest
            intro trail htrail
            simp only [splitTrails, hab, ↓reduceIte, hsplit] at htrail
            rcases List.mem_cons.mp htrail with hfirst | hrest
            · subst trail
              rw [List.isChain_cons]
              constructor
              · intro x hx
                rw [hhead] at hx
                simpa using Option.some.inj hx.symm ▸ hab
              · exact ih first (by rw [hsplit]; simp)
            · exact ih trail (by rw [hsplit]; exact List.mem_cons_of_mem _ hrest)
          · intro trail htrail
            simp only [splitTrails, hab, ↓reduceIte] at htrail
            rcases List.mem_cons.mp htrail with hsingle | hrest
            · subst trail
              simp
            · exact ih trail hrest

private theorem breakDestinations_sublist_tail
    {α : Type*} (good : α → α → Prop) [DecidableRel good] :
    ∀ l : List α, (breakDestinations good l).Sublist l.tail := by
  intro l
  induction l with
  | nil => simp [breakDestinations]
  | cons a tail ih =>
      cases tail with
      | nil => simp [breakDestinations]
      | cons b rest =>
          by_cases hab : good a b
          · simp only [breakDestinations, hab, ↓reduceIte, List.tail_cons]
            exact ih.cons b
          · simp only [breakDestinations, hab, ↓reduceIte, List.tail_cons]
            exact ih.cons_cons b

private theorem mem_breakDestinations
    {α : Type*} (good : α → α → Prop) [DecidableRel good]
    {l : List α} {b : α}
    (hb : b ∈ breakDestinations good l) :
    ∃ a, [a, b] <:+: l ∧ ¬ good a b := by
  induction l with
  | nil => simp [breakDestinations] at hb
  | cons a tail ih =>
      cases tail with
      | nil => simp [breakDestinations] at hb
      | cons c rest =>
          by_cases hac : good a c
          · simp only [breakDestinations, hac, ↓reduceIte] at hb
            obtain ⟨x, hx, hbad⟩ := ih hb
            exact ⟨x, List.infix_cons hx, hbad⟩
          · simp only [breakDestinations, hac, ↓reduceIte,
              List.mem_cons] at hb
            rcases hb with hbc | hb
            · subst b
              exact ⟨a, List.infix_append_left, hac⟩
            · obtain ⟨x, hx, hbad⟩ := ih hb
              exact ⟨x, List.infix_cons hx, hbad⟩

private theorem splitTrails_length_eq_breaks_add_one
    {α : Type*} (good : α → α → Prop) [DecidableRel good]
    {l : List α} (hl : l ≠ []) :
    (splitTrails good l).length =
      (breakDestinations good l).length + 1 := by
  induction l with
  | nil => exact False.elim (hl rfl)
  | cons a tail ih =>
      cases tail with
      | nil => simp [splitTrails, breakDestinations]
      | cons b rest =>
          have ih' := ih (by simp)
          by_cases hab : good a b
          · obtain ⟨trail, trails, hsplit, _hhead⟩ :=
              splitTrails_first good b rest
            simpa [splitTrails, breakDestinations, hab, hsplit] using ih'
          · simp [splitTrails, breakDestinations, hab, ih']

/-! ## The route's cost-three trails -/

def ChainsCompatible (route : List Perm7)
    (c next : ChainStart route) : Prop :=
  d (runEnd route (chainLast route c)) next.1 = 3

noncomputable instance (route : List Perm7) :
    DecidableRel (ChainsCompatible route) := by
  unfold ChainsCompatible
  infer_instance

/-- Split the route-ordered chain sequence exactly at non-cost-three joins. -/
noncomputable def routeChainTrails (route : List Perm7) :
    List (List (ChainStart route)) :=
  splitTrails (ChainsCompatible route) (routeChainStarts route)

theorem routeChainTrails_flatten (route : List Perm7) :
    (routeChainTrails route).flatten = routeChainStarts route :=
  splitTrails_flatten _ _

/-- Every chain start occurs exactly once in the flattened trails. -/
theorem chainTrails_partition {route : List Perm7}
    (hroute : IsHamiltonianRoute route) (c : ChainStart route) :
    (routeChainTrails route).flatten.count c = 1 := by
  rw [routeChainTrails_flatten,
    (routeChainStarts_nodup hroute).count]
  simp [routeChainStarts_complete hroute c]

/-- Consecutive chains within every trail have matching macroedge triples. -/
theorem chainTrails_compat {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    {trail : List (ChainStart route)}
    (htrail : trail ∈ routeChainTrails route) :
    trail.IsChain fun c next =>
      chainBeta route c = chainAlpha route next := by
  have hgood : trail.IsChain (ChainsCompatible route) :=
    splitTrails_isChain _ _ trail htrail
  apply hgood.imp
  intro c next hthree
  rw [chainBeta_eq_last3]
  exact (cost_three_iff_endpoint_compatible _ _).mp hthree

/-! ## Counting the trail breaks -/

/-- Destinations of route edges of cost at least four, in route order. -/
def highCostDestinations : List Perm7 → List Perm7
  | p :: q :: rest =>
      if 4 ≤ d p q then q :: highCostDestinations (q :: rest)
      else highCostDestinations (q :: rest)
  | _ => []

@[simp] theorem highCostDestinations_length (route : List Perm7) :
    (highCostDestinations route).length = highCostCount route := by
  induction route with
  | nil => simp [highCostDestinations, highCostCount]
  | cons p tail ih =>
      cases tail with
      | nil => simp [highCostDestinations, highCostCount]
      | cons q rest =>
          simp only [highCostDestinations, highCostCount]
          split <;> simp_all <;> omega

theorem highCostDestinations_sublist_tail (route : List Perm7) :
    (highCostDestinations route).Sublist route.tail := by
  induction route with
  | nil => simp [highCostDestinations]
  | cons p tail ih =>
      cases tail with
      | nil => simp [highCostDestinations]
      | cons q rest =>
          simp only [highCostDestinations]
          split
          · exact ih.cons_cons q
          · exact ih.cons q

theorem highCostDestinations_nodup {route : List Perm7}
    (hnodup : route.Nodup) :
    (highCostDestinations route).Nodup :=
  (highCostDestinations_sublist_tail route).nodup hnodup.tail

private theorem mem_highCostDestinations_cons (a : Perm7)
    {route : List Perm7} {q : Perm7}
    (hq : q ∈ highCostDestinations route) :
    q ∈ highCostDestinations (a :: route) := by
  cases route with
  | nil => simp [highCostDestinations] at hq
  | cons b rest =>
      simp only [highCostDestinations]
      split
      · exact List.mem_cons_of_mem _ hq
      · exact hq

private theorem mem_highCostDestinations_append_pair
    (pre post : List Perm7) (p q : Perm7)
    (hcost : 4 ≤ d p q) :
    q ∈ highCostDestinations (pre ++ p :: q :: post) := by
  induction pre with
  | nil => simp [highCostDestinations, hcost]
  | cons a pre ih =>
      simpa only [List.cons_append] using
        mem_highCostDestinations_cons a ih

theorem pair_infix_mem_highCostDestinations
    {route : List Perm7} {p q : Perm7}
    (hpair : [p, q] <:+: route) (hcost : 4 ≤ d p q) :
    q ∈ highCostDestinations route := by
  rcases hpair with ⟨pre, post, hroute⟩
  rw [← hroute]
  simpa [List.append_assoc] using
    mem_highCostDestinations_append_pair pre post p q hcost

private theorem routeChainStarts_ne_nil {route : List Perm7}
    (hroute : IsHamiltonianRoute route) :
    routeChainStarts route ≠ [] := by
  obtain ⟨p, hp⟩ := chainStartSet_nonempty hroute
  let c : ChainStart route := ⟨p, hp⟩
  intro hnil
  have hc := routeChainStarts_complete hroute c
  rw [hnil] at hc
  simp at hc

private theorem chainBreakCount_le_highCostCount
    {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route) :
    (breakDestinations (ChainsCompatible route)
      (routeChainStarts route)).length ≤ highCostCount route := by
  let breaks :=
    breakDestinations (ChainsCompatible route) (routeChainStarts route)
  have hbreakNodup : breaks.Nodup := by
    exact (breakDestinations_sublist_tail
      (ChainsCompatible route) (routeChainStarts route)).nodup
        (routeChainStarts_nodup hroute).tail
  have hmapNodup : (breaks.map Subtype.val).Nodup :=
    hbreakNodup.map Subtype.val_injective
  have hhighNodup : (highCostDestinations route).Nodup :=
    highCostDestinations_nodup hroute.1
  have hsubset :
      (breaks.map Subtype.val).toFinset ⊆
        (highCostDestinations route).toFinset := by
    intro y hy
    simp only [List.mem_toFinset, List.mem_map] at hy ⊢
    obtain ⟨next, hnext, rfl⟩ := hy
    obtain ⟨c, hpair, hbad⟩ :=
      mem_breakDestinations (ChainsCompatible route) hnext
    have hrouteEdge :=
      consecutive_chains_route_edge hroute hnormal hpair
    have hhigh :
        4 ≤ d (runEnd route (chainLast route c)) next.1 := by
      rcases hrouteEdge.2 with hthree | hhigh
      · exact False.elim (hbad hthree)
      · exact hhigh
    exact pair_infix_mem_highCostDestinations hrouteEdge.1 hhigh
  have hcard := Finset.card_le_card hsubset
  rw [List.toFinset_card_of_nodup hmapNodup,
    List.toFinset_card_of_nodup hhighNodup,
    List.length_map, highCostDestinations_length] at hcard
  exact hcard

/-- Every new trail after the first is forced by a cost-at-least-four route
edge. -/
theorem chainTrails_count {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route) :
    (routeChainTrails route).length ≤ highCostCount route + 1 := by
  have hsplit :=
    splitTrails_length_eq_breaks_add_one
      (ChainsCompatible route) (routeChainStarts_ne_nil hroute)
  have hbreak := chainBreakCount_le_highCostCount hroute hnormal
  change (splitTrails (ChainsCompatible route)
    (routeChainStarts route)).length ≤ highCostCount route + 1
  rw [hsplit]
  exact Nat.add_le_add_right hbreak 1

/-! ## First return of `T` to chain starts -/

def chainTouchedState (route : List Perm7)
    (c : ChainStart route) : TouchedState route :=
  runStartTouchedState route (chainAsRunStart c)

def IsChainReturn (route : List Perm7)
    (c : ChainStart route) (n : ℕ) : Prop :=
  0 < n ∧
    ((touchedTPerm route ^ n) (chainTouchedState route c)).1 ∈
      chainStartSet route

noncomputable instance (route : List Perm7)
    (c : ChainStart route) (n : ℕ) :
    Decidable (IsChainReturn route c n) := by
  unfold IsChainReturn
  infer_instance

theorem chainReturn_exists (route : List Perm7)
    (c : ChainStart route) :
    ∃ n, IsChainReturn route c n := by
  let T := touchedTPerm route
  refine ⟨orderOf T, (isOfFinOrder_of_finite T).orderOf_pos, ?_⟩
  change ((T ^ orderOf T) (chainTouchedState route c)).1 ∈
    chainStartSet route
  rw [pow_orderOf_eq_one]
  exact c.2

noncomputable def chainReturnTime (route : List Perm7)
    (c : ChainStart route) : ℕ :=
  Nat.find (chainReturn_exists route c)

theorem chainReturnTime_spec (route : List Perm7)
    (c : ChainStart route) :
    IsChainReturn route c (chainReturnTime route c) :=
  Nat.find_spec (chainReturn_exists route c)

theorem chainReturnTime_min (route : List Perm7)
    (c : ChainStart route) {n : ℕ}
    (hn : n < chainReturnTime route c) :
    ¬ IsChainReturn route c n :=
  Nat.find_min (chainReturn_exists route c) hn

noncomputable def nextFaceChainStart (route : List Perm7)
    (c : ChainStart route) : ChainStart route :=
  ⟨((touchedTPerm route ^ chainReturnTime route c)
      (chainTouchedState route c)).1,
    (chainReturnTime_spec route c).2⟩

theorem chainTouchedState_nextFace (route : List Perm7)
    (c : ChainStart route) :
    chainTouchedState route (nextFaceChainStart route c) =
      (touchedTPerm route ^ chainReturnTime route c)
        (chainTouchedState route c) := by
  apply Subtype.ext
  rfl

private theorem chainReturn_cancel_right {route : List Perm7}
    (c d : ChainStart route)
    (hnext : (nextFaceChainStart route c).1 =
      (nextFaceChainStart route d).1)
    (hmn : chainReturnTime route c ≤ chainReturnTime route d) :
    c = d := by
  let T := touchedTPerm route
  let m := chainReturnTime route c
  let n := chainReturnTime route d
  let delta := n - m
  have hnmd : n = m + delta := by
    dsimp [delta]
    omega
  have hnextEq :
      nextFaceChainStart route c = nextFaceChainStart route d :=
    Subtype.ext hnext
  have hnextState :
      (T ^ m) (chainTouchedState route c) =
        (T ^ n) (chainTouchedState route d) := by
    rw [← chainTouchedState_nextFace,
      ← chainTouchedState_nextFace, hnextEq]
  have hpow : chainTouchedState route c =
      (T ^ delta) (chainTouchedState route d) := by
    apply (T ^ m).injective
    calc
      (T ^ m) (chainTouchedState route c) =
          (T ^ n) (chainTouchedState route d) := hnextState
      _ = (T ^ (m + delta)) (chainTouchedState route d) := by rw [hnmd]
      _ = (T ^ m) ((T ^ delta) (chainTouchedState route d)) := by
        rw [pow_add, Equiv.Perm.mul_apply]
  have hnm : n ≤ m := by
    by_contra hnot
    have hdeltaPos : 0 < delta := by
      dsimp [delta]
      omega
    have hdeltaLt : delta < n := by
      have hmpos := (chainReturnTime_spec route c).1
      dsimp [m, n, delta] at *
      omega
    have hdeltaReturn : IsChainReturn route d delta := by
      refine ⟨hdeltaPos, ?_⟩
      rw [← hpow]
      exact c.2
    exact chainReturnTime_min route d hdeltaLt hdeltaReturn
  have hmnEq : m = n := by omega
  apply Subtype.ext
  change c.1 = d.1
  dsimp [delta] at hpow
  rw [hmnEq] at hpow
  simp at hpow
  have hval := congrArg (fun p : TouchedState route => p.1) hpow
  change c.1 = d.1 at hval
  exact hval

theorem nextFaceChainStart_injective (route : List Perm7) :
    Function.Injective (nextFaceChainStart route) := by
  intro c d hnext
  by_cases hmn : chainReturnTime route c ≤ chainReturnTime route d
  · exact chainReturn_cancel_right c d
      (congrArg Subtype.val hnext) hmn
  · exact (chainReturn_cancel_right d c
      (congrArg Subtype.val hnext.symm)
      (Nat.le_of_not_ge hmn)).symm

/-- The successor chain on a face is the first return of `T` to the set of
chain starts. -/
noncomputable def chainFaceNext (route : List Perm7) :
    Equiv.Perm (ChainStart route) :=
  Equiv.ofBijective (nextFaceChainStart route)
    ⟨nextFaceChainStart_injective route,
      Finite.injective_iff_surjective.mp
        (nextFaceChainStart_injective route)⟩

@[simp] theorem chainFaceNext_apply (route : List Perm7)
    (c : ChainStart route) :
    chainFaceNext route c = nextFaceChainStart route c := rfl

private theorem chainFaceNext_sameCycle_of_touched_power
    (route : List Perm7) :
    ∀ j : ℕ, ∀ c d : ChainStart route,
      chainTouchedState route d =
        (touchedTPerm route ^ j) (chainTouchedState route c) →
      (chainFaceNext route).SameCycle c d := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
      intro c d hj
      by_cases hj0 : j = 0
      · subst j
        simp only [pow_zero, Equiv.Perm.one_apply] at hj
        apply Eq.sameCycle
        apply Subtype.ext
        have hval :=
          congrArg (fun p : TouchedState route => p.1) hj
        change d.1 = c.1 at hval
        exact hval.symm
      · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
        let m := chainReturnTime route c
        have hmj : m ≤ j := by
          apply Nat.find_min' (chainReturn_exists route c)
          refine ⟨hjpos, ?_⟩
          rw [← hj]
          exact d.2
        by_cases hmEq : m = j
        · have hnext : nextFaceChainStart route c = d := by
            apply Subtype.ext
            have hval :=
              congrArg (fun p : TouchedState route => p.1) hj
            change d.1 =
              ((touchedTPerm route ^ j)
                (chainTouchedState route c)).1 at hval
            simpa [nextFaceChainStart, m, hmEq] using hval.symm
          subst d
          refine ⟨1, ?_⟩
          simp
        · have hmLt : m < j := lt_of_le_of_ne hmj hmEq
          let u := nextFaceChainStart route c
          let delta := j - m
          have hdeltaLt : delta < j := by
            have hmpos := (chainReturnTime_spec route c).1
            dsimp [delta, m] at *
            omega
          have hdPower : chainTouchedState route d =
              (touchedTPerm route ^ delta)
                (chainTouchedState route u) := by
            rw [chainTouchedState_nextFace]
            calc
              chainTouchedState route d =
                  (touchedTPerm route ^ j)
                    (chainTouchedState route c) := hj
              _ = (touchedTPerm route ^ (delta + m))
                    (chainTouchedState route c) := by
                    congr 2
                    dsimp [delta]
                    omega
              _ = (touchedTPerm route ^ delta)
                    ((touchedTPerm route ^ m)
                      (chainTouchedState route c)) := by
                    rw [pow_add, Equiv.Perm.mul_apply]
          have hcu : (chainFaceNext route).SameCycle c u := by
            refine ⟨1, ?_⟩
            simp [u]
          exact hcu.trans (ih delta hdeltaLt u d hdPower)

theorem chainFaceNext_sameCycle_of_touchedSameCycle
    (route : List Perm7) (c d : ChainStart route)
    (hcd : (touchedTPerm route).SameCycle
      (chainTouchedState route c) (chainTouchedState route d)) :
    (chainFaceNext route).SameCycle c d := by
  obtain ⟨n, _hnpos, _hnbound, hn⟩ :=
    hcd.exists_pow_eq (touchedTPerm route)
  exact chainFaceNext_sameCycle_of_touched_power route n c d hn.symm

private theorem permCycleOf_apply_pow
    {α : Type*} [Fintype α] [DecidableEq α]
    (P : Equiv.Perm α) (n : ℕ) (x : α) :
    permCycleOf P ((P ^ n) x) = permCycleOf P x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, permCycleOf_apply, ih]

theorem chainStartToTouchedTCycle_apply_face
    (route : List Perm7) (c : ChainStart route) :
    chainStartToTouchedTCycle route (chainFaceNext route c) =
      chainStartToTouchedTCycle route c := by
  change permCycleOf (touchedTPerm route)
      (chainTouchedState route (chainFaceNext route c)) =
    permCycleOf (touchedTPerm route) (chainTouchedState route c)
  rw [chainFaceNext_apply, chainTouchedState_nextFace]
  exact permCycleOf_apply_pow _ _ _

theorem chainStartToTouchedTCycle_apply_face_pow
    (route : List Perm7) (n : ℕ) (c : ChainStart route) :
    chainStartToTouchedTCycle route ((chainFaceNext route ^ n) c) =
      chainStartToTouchedTCycle route c := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply,
        chainStartToTouchedTCycle_apply_face, ih]

theorem chainFaceSameCycle_touchedCycle_eq
    (route : List Perm7) {c d : ChainStart route}
    (hcd : (chainFaceNext route).SameCycle c d) :
    chainStartToTouchedTCycle route c =
      chainStartToTouchedTCycle route d := by
  obtain ⟨n, _hnpos, _hnbound, hn⟩ :=
    hcd.exists_pow_eq (chainFaceNext route)
  have hpow := chainStartToTouchedTCycle_apply_face_pow route n c
  rw [hn] at hpow
  exact hpow.symm

noncomputable def chainFaceCycleToTouchedCycle (route : List Perm7) :
    PermCycle (chainFaceNext route) →
      PermCycle (touchedTPerm route) :=
  fun C => chainStartToTouchedTCycle route
    (permCycleRepresentative (chainFaceNext route) C)

theorem chainFaceCycleToTouchedCycle_injective (route : List Perm7) :
    Function.Injective (chainFaceCycleToTouchedCycle route) := by
  intro C D hCD
  let c := permCycleRepresentative (chainFaceNext route) C
  let d := permCycleRepresentative (chainFaceNext route) D
  have hTouchedSame : (touchedTPerm route).SameCycle
      (chainTouchedState route c) (chainTouchedState route d) := by
    apply sameCycle_of_permCycleOf_eq
    exact hCD
  have hFaceSame :=
    chainFaceNext_sameCycle_of_touchedSameCycle route c d hTouchedSame
  calc
    C = permCycleOf (chainFaceNext route) c :=
      (permCycleRepresentative_spec (chainFaceNext route) C).symm
    _ = permCycleOf (chainFaceNext route) d :=
      permCycleOf_eq_of_sameCycle (chainFaceNext route) hFaceSame
    _ = D := permCycleRepresentative_spec (chainFaceNext route) D

theorem chainFaceCycleToTouchedCycle_surjective
    {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route) :
    Function.Surjective (chainFaceCycleToTouchedCycle route) := by
  intro D
  obtain ⟨c, hc⟩ :=
    chainStartToTouchedTCycle_surjective hroute hnormal D
  let C := permCycleOf (chainFaceNext route) c
  refine ⟨C, ?_⟩
  let r := permCycleRepresentative (chainFaceNext route) C
  have hrCycle :
      permCycleOf (chainFaceNext route) r =
        permCycleOf (chainFaceNext route) c := by
    exact (permCycleRepresentative_spec (chainFaceNext route) C).trans rfl
  have hrc : (chainFaceNext route).SameCycle r c :=
    sameCycle_of_permCycleOf_eq (chainFaceNext route) hrCycle
  exact (chainFaceSameCycle_touchedCycle_eq route hrc).trans hc

noncomputable def chainFaceCyclesEquivTouchedCycles
    {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route) :
    PermCycle (chainFaceNext route) ≃
      PermCycle (touchedTPerm route) :=
  Equiv.ofBijective (chainFaceCycleToTouchedCycle route)
    ⟨chainFaceCycleToTouchedCycle_injective route,
      chainFaceCycleToTouchedCycle_surjective hroute hnormal⟩

/-- Faces of materialized chains are exactly the `T`-cycles. -/
theorem faces_eq_T_cycles {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route) :
    permCycleCount (chainFaceNext route) =
      permCycleCount (touchedTPerm route) := by
  exact Fintype.card_congr
    (chainFaceCyclesEquivTouchedCycles hroute hnormal)

theorem chains_card {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (z : RouteStructuralCounts route hroute) :
    Fintype.card (ChainStart route) = z.q := by
  rw [Fintype.card_coe, z.chainStart_card]

/-! ## The bounded hole gap after a chain -/

noncomputable def chainGapSource (route : List Perm7)
    (c : ChainStart route) : TouchedState route :=
  touchedTPerm route
    (runStartTouchedState route (chainLast route c))

def IsGapReturn (route : List Perm7)
    (c : ChainStart route) (n : ℕ) : Prop :=
  IsSelectedTouched route
    ((touchedTPerm route ^ n) (chainGapSource route c))

noncomputable instance (route : List Perm7)
    (c : ChainStart route) (n : ℕ) :
    Decidable (IsGapReturn route c n) := by
  unfold IsGapReturn
  infer_instance

theorem gapReturn_exists (route : List Perm7)
    (c : ChainStart route) :
    ∃ n, IsGapReturn route c n := by
  obtain ⟨s, hsame⟩ :=
    touchedTPerm_cycle_meets_runStart route (chainGapSource route c)
  obtain ⟨n, _hnpos, _hnbound, hn⟩ :=
    hsame.exists_pow_eq (touchedTPerm route)
  refine ⟨n, ?_⟩
  change IsSelectedTouched route
    ((touchedTPerm route ^ n) (chainGapSource route c))
  rw [hn]
  exact runStartTouchedState_selected route s

/-- Number of consecutive holes after the last run of a chain. -/
noncomputable def gapLen (route : List Perm7)
    (c : ChainStart route) : ℕ :=
  Nat.find (gapReturn_exists route c)

theorem gapLen_spec (route : List Perm7)
    (c : ChainStart route) :
    IsGapReturn route c (gapLen route c) :=
  Nat.find_spec (gapReturn_exists route c)

theorem gapLen_min (route : List Perm7)
    (c : ChainStart route) {n : ℕ}
    (hn : n < gapLen route c) :
    ¬ IsGapReturn route c n :=
  Nat.find_min (gapReturn_exists route c) hn

/-- A touched insertion block has six states, so at most five consecutive
states can be holes. -/
theorem gapLen_le_five (route : List Perm7)
    (c : ChainStart route) :
    gapLen route c ≤ 5 := by
  by_contra hnot
  have hlong : 5 < gapLen route c := Nat.lt_of_not_ge hnot
  let p := chainGapSource route c
  have hpTouched : fBlock p.1 ∈ touchedBlocks route := p.2
  rcases Finset.mem_image.mp hpTouched with ⟨s, hsStart, hsBlock⟩
  let rs : RunStart route := ⟨s, hsStart⟩
  have hsMem : s ∈ fBlock p.1 := by
    rw [← hsBlock]
    exact self_mem_fBlock s
  rcases Finset.mem_image.mp hsMem with ⟨i, hi, hiF⟩
  have hiFive : i < 6 := by simpa using hi
  have hiGap : i < gapLen route c := by omega
  have hholes : ∀ j < i,
      ¬ IsSelectedTouched route ((touchedTPerm route ^ j) p) := by
    intro j hj
    exact gapLen_min route c (hj.trans hiGap)
  have hTF :=
    touchedTPerm_pow_eq_touchedFPerm_pow_of_holes
      route p i hholes
  have hstate :
      (touchedTPerm route ^ i) p =
        runStartTouchedState route rs := by
    apply Subtype.ext
    rw [hTF, touchedFPerm_pow_apply_val]
    exact hiF
  apply gapLen_min route c hiGap
  change IsSelectedTouched route
    ((touchedTPerm route ^ i) p)
  rw [hstate]
  exact rs.2

noncomputable def gapLenFin (route : List Perm7)
    (c : ChainStart route) : Fin 6 :=
  ⟨gapLen route c, by
    have := gapLen_le_five route c
    omega⟩

noncomputable def gapRunStart (route : List Perm7)
    (c : ChainStart route) : RunStart route :=
  ⟨((touchedTPerm route ^ gapLen route c)
      (chainGapSource route c)).1,
    gapLen_spec route c⟩

theorem gapRunStart_state (route : List Perm7)
    (c : ChainStart route) :
    runStartTouchedState route (gapRunStart route c) =
      (touchedTPerm route ^ gapLen route c)
        (chainGapSource route c) := by
  apply Subtype.ext
  rfl

theorem gapRunStart_not_cheap {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (c : ChainStart route) :
    (gapRunStart route c).1 ∉ cheapTwoDestinations route := by
  intro hcheap
  obtain ⟨u, huT, _huEarlier⟩ :=
    touchedT_predecessor_earlier_of_mem_cheapTwoDestinations
      hroute hnormal (gapRunStart route c) hcheap
  cases hgap : gapLen route c with
  | zero =>
      have huLastState :
          runStartTouchedState route u =
            runStartTouchedState route (chainLast route c) := by
        apply (touchedTPerm route).injective
        calc
          touchedTPerm route (runStartTouchedState route u) =
              runStartTouchedState route (gapRunStart route c) := huT
          _ = (touchedTPerm route ^ gapLen route c)
                (chainGapSource route c) :=
              gapRunStart_state route c
          _ = chainGapSource route c := by rw [hgap]; simp
          _ = touchedTPerm route
                (runStartTouchedState route (chainLast route c)) := rfl
      have huLast : u = chainLast route c := by
        apply Subtype.ext
        exact congrArg (fun p : TouchedState route => p.1) huLastState
      have hstep : IsChainStep route
          (chainLast route c) (gapRunStart route c) := by
        refine ⟨?_, hcheap⟩
        rw [← huLast]
        exact huT
      have hsome :=
        (chainSucc?_eq_some_iff route
          (chainLast route c) (gapRunStart route c)).2 hstep
      rw [chainLast_terminal hroute hnormal c] at hsome
      simp at hsome
  | succ n =>
      have hnGap : n < gapLen route c := by omega
      have hnHole : ¬ IsSelectedTouched route
          ((touchedTPerm route ^ n) (chainGapSource route c)) :=
        gapLen_min route c hnGap
      have huPred :
          runStartTouchedState route u =
            (touchedTPerm route ^ n) (chainGapSource route c) := by
        apply (touchedTPerm route).injective
        calc
          touchedTPerm route (runStartTouchedState route u) =
              runStartTouchedState route (gapRunStart route c) := huT
          _ = (touchedTPerm route ^ gapLen route c)
                (chainGapSource route c) :=
              gapRunStart_state route c
          _ = touchedTPerm route
                ((touchedTPerm route ^ n)
                  (chainGapSource route c)) := by
              rw [hgap, pow_succ', Equiv.Perm.mul_apply]
      apply hnHole
      rw [← huPred]
      exact u.2

noncomputable def gapChainStart {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (c : ChainStart route) : ChainStart route :=
  ⟨(gapRunStart route c).1, by
    simp [chainStartSet, gapRunStart_not_cheap hroute hnormal c]⟩

/-- The first state after the chain; when `gapLen > 0` this is the first
hole. -/
noncomputable def gapFirstHole (route : List Perm7)
    (c : ChainStart route) : Perm7 :=
  (chainGapSource route c).1

theorem gapFirstHole_eq_F_A (route : List Perm7)
    (c : ChainStart route) :
    gapFirstHole route c =
      F (runStartPerm route (chainLast route c)).1 := by
  exact touchedTPerm_runStartTouchedState_val
    route (chainLast route c)

theorem gapFirstHole_is_hole_of_pos (route : List Perm7)
    (c : ChainStart route) (hpos : 0 < gapLen route c) :
    ¬ IsSelectedTouched route (chainGapSource route c) := by
  simpa [IsGapReturn] using gapLen_min route c hpos

theorem gap_holes_stay_in_one_block (route : List Perm7)
    (c : ChainStart route) {j : ℕ} (hj : j ≤ gapLen route c) :
    touchedStateBlock route
        ((touchedTPerm route ^ j) (chainGapSource route c)) =
      touchedStateBlock route (chainGapSource route c) := by
  apply hole_run_stays_in_one_block
  · intro i hi
    exact gapLen_min route c hi
  · exact hj

theorem gap_F_iterate_eq_gapRunStart (route : List Perm7)
    (c : ChainStart route) :
    (F^[gapLen route c]) (gapFirstHole route c) =
      (gapRunStart route c).1 := by
  have hholes : ∀ j < gapLen route c,
      ¬ IsSelectedTouched route
        ((touchedTPerm route ^ j) (chainGapSource route c)) := by
    intro j hj
    exact gapLen_min route c hj
  have hTF :=
    touchedTPerm_pow_eq_touchedFPerm_pow_of_holes
      route (chainGapSource route c) (gapLen route c) hholes
  have hstate := gapRunStart_state route c
  have hval := congrArg (fun p : TouchedState route => p.1)
    (hstate.trans hTF)
  simpa [gapFirstHole, touchedFPerm_pow_apply_val] using hval.symm

/-! ## Identifying the concrete gap with the face successor -/

theorem chainRunStarts_getElem_state
    (route : List Perm7) (c : ChainStart route)
    (i : ℕ) (hi : i < (chainRunStarts route c).length) :
    runStartTouchedState route (chainRunStarts route c)[i] =
      (touchedTPerm route ^ i) (chainTouchedState route c) := by
  induction i with
  | zero =>
      rw [List.getElem_zero, chainRunStarts_head]
      simp [chainTouchedState]
  | succ i ih =>
      have hi' : i < (chainRunStarts route c).length := by omega
      have hstep : IsChainStep route
          (chainRunStarts route c)[i]
          (chainRunStarts route c)[i + 1] :=
        (List.isChain_iff_getElem.mp
          (chainRunStarts_isChain route c)) i (by omega)
      calc
        runStartTouchedState route
              (chainRunStarts route c)[i + 1] =
            touchedTPerm route
              (runStartTouchedState route
                (chainRunStarts route c)[i]) := hstep.1.symm
        _ = touchedTPerm route
              ((touchedTPerm route ^ i)
                (chainTouchedState route c)) := by rw [ih hi']
        _ = (touchedTPerm route ^ (i + 1))
              (chainTouchedState route c) := by
            rw [pow_succ', Equiv.Perm.mul_apply]

theorem chainLast_state (route : List Perm7) (c : ChainStart route) :
    runStartTouchedState route (chainLast route c) =
      (touchedTPerm route ^
          ((chainRunStarts route c).length - 1))
        (chainTouchedState route c) := by
  rw [chainLast, List.getLast_eq_getElem]
  exact chainRunStarts_getElem_state route c _ (by
    have hne := chainRunStarts_ne_nil route c
    have hpos : 0 < (chainRunStarts route c).length :=
      List.length_pos_iff.mpr hne
    omega)

private theorem chainRunStarts_getElem_not_chainStart
    (route : List Perm7) (c : ChainStart route)
    (i : ℕ) (hiPos : 0 < i)
    (hi : i < (chainRunStarts route c).length) :
    (chainRunStarts route c)[i].1 ∉ chainStartSet route := by
  cases i with
  | zero => omega
  | succ i =>
      have hstep : IsChainStep route
          (chainRunStarts route c)[i]
          (chainRunStarts route c)[i + 1] :=
        (List.isChain_iff_getElem.mp
          (chainRunStarts_isChain route c)) i (by omega)
      intro hstart
      exact (Finset.mem_sdiff.mp hstart).2 (by simpa using hstep.2)

theorem chainGapSource_eq_power_length
    (route : List Perm7) (c : ChainStart route) :
    chainGapSource route c =
      (touchedTPerm route ^ (chainRunStarts route c).length)
        (chainTouchedState route c) := by
  have hpos : 0 < (chainRunStarts route c).length :=
    List.length_pos_iff.mpr (chainRunStarts_ne_nil route c)
  calc
    chainGapSource route c =
        touchedTPerm route
          (runStartTouchedState route (chainLast route c)) := rfl
    _ = touchedTPerm route
          ((touchedTPerm route ^
              ((chainRunStarts route c).length - 1))
            (chainTouchedState route c)) := by
          rw [chainLast_state]
    _ = (touchedTPerm route ^
            (((chainRunStarts route c).length - 1) + 1))
          (chainTouchedState route c) := by
          rw [pow_succ', Equiv.Perm.mul_apply]
    _ = (touchedTPerm route ^ (chainRunStarts route c).length)
          (chainTouchedState route c) := by
          congr 2
          omega

theorem chainGap_end_state
    (route : List Perm7) (c : ChainStart route) :
    (touchedTPerm route ^
        ((chainRunStarts route c).length + gapLen route c))
        (chainTouchedState route c) =
      runStartTouchedState route (gapRunStart route c) := by
  calc
    (touchedTPerm route ^
        ((chainRunStarts route c).length + gapLen route c))
        (chainTouchedState route c) =
      (touchedTPerm route ^
        (gapLen route c + (chainRunStarts route c).length))
        (chainTouchedState route c) := by
          congr 2
          omega
    _ = (touchedTPerm route ^ gapLen route c)
          ((touchedTPerm route ^ (chainRunStarts route c).length)
            (chainTouchedState route c)) := by
          rw [pow_add, Equiv.Perm.mul_apply]
    _ = (touchedTPerm route ^ gapLen route c)
          (chainGapSource route c) := by
          rw [chainGapSource_eq_power_length]
    _ = runStartTouchedState route (gapRunStart route c) :=
      (gapRunStart_state route c).symm

theorem chainGap_is_return
    {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (c : ChainStart route) :
    IsChainReturn route c
      ((chainRunStarts route c).length + gapLen route c) := by
  constructor
  · have hpos : 0 < (chainRunStarts route c).length :=
      List.length_pos_iff.mpr (chainRunStarts_ne_nil route c)
    omega
  · rw [chainGap_end_state]
    exact (gapChainStart hroute hnormal c).2

private theorem no_chain_return_before_gap_end
    {route : List Perm7}
    (c : ChainStart route) {j : ℕ}
    (hjPos : 0 < j)
    (hjLt :
      j < (chainRunStarts route c).length + gapLen route c) :
    ¬ IsChainReturn route c j := by
  intro hjReturn
  by_cases hjChain : j < (chainRunStarts route c).length
  · have hstate :=
      chainRunStarts_getElem_state route c j hjChain
    have hval := congrArg (fun p : TouchedState route => p.1) hstate
    change (chainRunStarts route c)[j].1 =
      ((touchedTPerm route ^ j) (chainTouchedState route c)).1 at hval
    have hstart :
        (chainRunStarts route c)[j].1 ∈ chainStartSet route := by
      rw [hval]
      exact hjReturn.2
    exact
      (chainRunStarts_getElem_not_chainStart
        route c j hjPos hjChain) hstart
  · have hlenLe : (chainRunStarts route c).length ≤ j :=
      Nat.le_of_not_gt hjChain
    let r := j - (chainRunStarts route c).length
    have hrLt : r < gapLen route c := by
      dsimp [r]
      omega
    have hpower :
        (touchedTPerm route ^ j) (chainTouchedState route c) =
          (touchedTPerm route ^ r) (chainGapSource route c) := by
      calc
        (touchedTPerm route ^ j) (chainTouchedState route c) =
            (touchedTPerm route ^
              (r + (chainRunStarts route c).length))
              (chainTouchedState route c) := by
                congr 2
                dsimp [r]
                omega
        _ = (touchedTPerm route ^ r)
              ((touchedTPerm route ^
                  (chainRunStarts route c).length)
                (chainTouchedState route c)) := by
              rw [pow_add, Equiv.Perm.mul_apply]
        _ = (touchedTPerm route ^ r)
              (chainGapSource route c) := by
              rw [chainGapSource_eq_power_length]
    apply gapLen_min route c hrLt
    change ((touchedTPerm route ^ r)
        (chainGapSource route c)).1 ∈ runStartSet route
    rw [← hpower]
    exact chainStartSet_subset_runStartSet route hjReturn.2

theorem chainReturnTime_eq_length_add_gapLen
    {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (c : ChainStart route) :
    chainReturnTime route c =
      (chainRunStarts route c).length + gapLen route c := by
  let n := (chainRunStarts route c).length + gapLen route c
  have hnReturn : IsChainReturn route c n :=
    chainGap_is_return hroute hnormal c
  have htimeLe : chainReturnTime route c ≤ n :=
    Nat.find_min' (chainReturn_exists route c) hnReturn
  have hnLe : n ≤ chainReturnTime route c := by
    by_contra hnot
    have htimeLt : chainReturnTime route c < n :=
      Nat.lt_of_not_ge hnot
    exact no_chain_return_before_gap_end c
      (chainReturnTime_spec route c).1 htimeLt
      (chainReturnTime_spec route c)
  exact Nat.le_antisymm htimeLe hnLe

/-- The concrete successor reached after the final chain run and its short
hole gap is exactly the first-return successor defining the face. -/
theorem gapChainStart_eq_chainFaceNext
    {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (c : ChainStart route) :
    gapChainStart hroute hnormal c = chainFaceNext route c := by
  rw [chainFaceNext_apply]
  apply Subtype.ext
  change (gapRunStart route c).1 =
    ((touchedTPerm route ^ chainReturnTime route c)
      (chainTouchedState route c)).1
  rw [chainReturnTime_eq_length_add_gapLen hroute hnormal,
    chainGap_end_state]
  rfl

theorem gap_F_iterate_eq_faceNext
    {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (c : ChainStart route) :
    (F^[gapLen route c]) (gapFirstHole route c) =
      (chainFaceNext route c).1 := by
  calc
    (F^[gapLen route c]) (gapFirstHole route c) =
        (gapRunStart route c).1 :=
      gap_F_iterate_eq_gapRunStart route c
    _ = (gapChainStart hroute hnormal c).1 := rfl
    _ = (chainFaceNext route c).1 := by
      rw [gapChainStart_eq_chainFaceNext hroute hnormal c]

theorem gap_zero_faceNext_eq_touchedT_last
    {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (c : ChainStart route)
    (hzero : gapLen route c = 0) :
    (chainFaceNext route c).1 =
      (touchedTPerm route
        (runStartTouchedState route (chainLast route c))).1 := by
  have hface :=
    gap_F_iterate_eq_faceNext hroute hnormal c
  rw [hzero] at hface
  simpa [gapFirstHole, chainGapSource] using hface.symm

theorem gapComplementRow_start_eq_faceNext
    {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (c : ChainStart route) :
    (gapComplementRow
      (gapFirstHole route c) (gapLenFin route c)).start =
        (chainFaceNext route c).1 := by
  exact gap_F_iterate_eq_faceNext hroute hnormal c

theorem gapComplementRow_alpha_eq_chainAlpha
    {route : List Perm7}
    (hroute : IsHamiltonianRoute route)
    (hnormal : IsNormalizedRoute route)
    (c : ChainStart route) :
    alpha (gapComplementRow
      (gapFirstHole route c) (gapLenFin route c)).start =
        chainAlpha route (chainFaceNext route c) := by
  rw [gapComplementRow_start_eq_faceNext hroute hnormal c]
  rfl

theorem gapComplementRow_beta_eq_chainBeta
    (route : List Perm7) (c : ChainStart route) :
    (gapComplementRow
      (gapFirstHole route c) (gapLenFin route c)).beta =
        chainBeta route c := by
  exact gapComplementRow_beta_of_touchedT_predecessor
    route (chainLast route c) (gapFirstHole route c)
      (gapLenFin route c) rfl

end Superperm7
