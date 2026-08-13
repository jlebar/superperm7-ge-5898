/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.Equality

/-!
# From a coarsened certificate in an equality cell to a template family

A trail `t` is *template-typed* when `(chargeSum t, markCount t) = (c, m)` has
`percapVal c m = optLen c` with `c ∈ {14,16,26,34,36}` **and** `t.length = percapVal c m`.
A DP `convLoose τ u b` bounds the total rows of `≤ τ` trails (charge `≤ u`, marks `≤ b`)
under the extra constraint that *some* trail is not template-typed (its length is then
`≤ percapVal c m − 1`, or its `(c, m)` is not a template pair).  Checking
`convLoose τ u b < k` for the three equality parameter sets shows every trail of an
instance is template-typed; the charges then form one of the template multisets, and
`joinImpossible` refutes the family.
-/

namespace Superperm7

/-- template charge of a template length -/
def chargeOfLen (n : ℕ) : Option ℕ :=
  if n = 31 then some 14 else if n = 34 then some 16 else if n = 50 then some 26
  else if n = 63 then some 34 else if n = 66 then some 36 else none

/-- A trail with `(chargeSum, markCount) = (c, m)` that is NOT template-typed
(template-typed := its length `ℓ` has `chargeOfLen ℓ = some g` with `c ≤ g`)
has length at most `looseCap c m`: if the cap value itself is a template length whose
charge is `≥ c`, a non-typed trail must be strictly shorter. -/
def looseCap (c m : ℕ) : ℕ :=
  match chargeOfLen (percapVal c m) with
  | some g => if c ≤ g then percapVal c m - 1 else percapVal c m
  | none => percapVal c m

/-! ## Tables (small ranges: τ ≤ 4, u ≤ 72, b ≤ 3) -/

def pcT (c m : ℕ) : ℕ := percapVal c m

/-- exact-profile DP over trails: `tightTab[τ][u][b]` = max Σ percapVal over EXACTLY τ trails…
we use "at most τ" with zero-row trails allowed implicitly by percapVal 0 m ≥ 0. -/
def stepAll (prev : Array (Array ℕ)) (cap : ℕ → ℕ → ℕ) : Array (Array ℕ) :=
  (Array.range 73).map fun u => (Array.range 4).map fun b =>
    ((List.range (u + 1)).flatMap fun c => (List.range (b + 1)).map fun m =>
      cap c m + (prev.getD (u - c) #[]).getD (b - m) 0).foldl max 0

def zeroTab : Array (Array ℕ) := (Array.range 73).map fun _ => Array.replicate 4 0

/-- `convAllTab[τ]` : all trails unconstrained (like convF13 but on the small range) -/
def convAllTab : Array (Array (Array ℕ)) := Id.run do
  let mut t := #[zeroTab]
  for _ in [0:4] do
    t := t.push (stepAll t[t.size - 1]! pcT)
  return t

def convAll (τ u b : ℕ) : ℕ := ((convAllTab.getD τ #[]).getD u #[]).getD b 0

/-- `convLooseTab[τ]` : at least one trail loose.  Recurrence:
loose(τ+1,u,b) = max over (c,m) of max( looseCap c m + all(τ,u-c,b-m), pcT c m + loose(τ,u-c,b-m) ),
with loose(0,·,·) = −∞ (encoded by a separate validity: we use 0 and track τ ≥ 1 carefully by
initializing loose(1,u,b) = max looseCap). -/
def convLooseTab : Array (Array (Array ℕ)) := Id.run do
  -- τ = 0: no trails, cannot have a loose trail: use 0 but it is never a valid witness;
  -- to stay sound we define loose(τ+1) from all(τ) and loose(τ) and only ever *upper bound*.
  let mut t : Array (Array (Array ℕ)) := #[zeroTab]
  for τ in [0:4] do
    let prevAll := convAllTab.getD τ #[]
    let prevLoose := t[t.size - 1]!
    let next := (Array.range 73).map fun u => (Array.range 4).map fun b =>
      ((List.range (u + 1)).flatMap fun c => (List.range (b + 1)).flatMap fun m =>
        (looseCap c m + (prevAll.getD (u - c) #[]).getD (b - m) 0) ::
        (if τ = 0 then [] else [pcT c m + (prevLoose.getD (u - c) #[]).getD (b - m) 0])).foldl max 0
    t := t.push next
  return t

def convLoose (τ u b : ℕ) : ℕ := ((convLooseTab.getD τ #[]).getD u #[]).getD b 0

/-- the recurrences, checked on the range -/
def eqTabsChecked : Bool :=
  (List.range 4).all fun τ => (List.range 73).all fun u => (List.range 4).all fun b =>
    (List.range (u + 1)).all fun c => (List.range (b + 1)).all fun m =>
      decide (pcT c m + convAll τ (u - c) (b - m) ≤ convAll (τ + 1) u b) &&
      decide (looseCap c m + convAll τ (u - c) (b - m) ≤ convLoose (τ + 1) u b) &&
      (decide (τ = 0) || decide (pcT c m + convLoose τ (u - c) (b - m) ≤ convLoose (τ + 1) u b))

/-- the three equality parameter sets are strict for loose families -/
def eqCellsChecked : Bool :=
  decide (convLoose 4 60 3 < 130) && decide (convLoose 3 66 2 < 131) && decide (convLoose 2 72 1 < 132)

end Superperm7

namespace Superperm7

/-! ## Soundness of the loose DP -/

theorem eqTabsChecked_true : eqTabsChecked = true := by native_decide
theorem eqCellsChecked_true : eqCellsChecked = true := by native_decide

/-- template-typed trail: its length is a template length `ℓ` with charge budget respected -/
def Typed (t : List MarkedRow) : Prop :=
  ∃ g, chargeOfLen t.length = some g ∧ chargeSum t ≤ g

theorem optLen_values : optLen 14 = 31 ∧ optLen 16 = 34 ∧ optLen 26 = 50 ∧ optLen 34 = 63 ∧ optLen 36 = 66 := by
  native_decide

theorem chargeOfLen_optLen {n g : ℕ} (h : chargeOfLen n = some g) : optLen g = n ∧ 0 < optLen g := by
  obtain ⟨e14, e16, e26, e34, e36⟩ := optLen_values
  unfold chargeOfLen at h
  split_ifs at h with h1 h2 h3 h4 h5 <;> simp only [Option.some.injEq] at h <;> subst h
  · subst h1; rw [e14]; exact ⟨rfl, by omega⟩
  · subst h2; rw [e16]; exact ⟨rfl, by omega⟩
  · subst h3; rw [e26]; exact ⟨rfl, by omega⟩
  · subst h4; rw [e34]; exact ⟨rfl, by omega⟩
  · subst h5; rw [e36]; exact ⟨rfl, by omega⟩

/-- monotonicity in the mark budget at the three cells -/
theorem convLoose_mono_cells :
    (∀ b ≤ 3, convLoose 4 60 b ≤ convLoose 4 60 3) ∧ (∀ b ≤ 2, convLoose 3 66 b ≤ convLoose 3 66 2) ∧
    (∀ b ≤ 1, convLoose 2 72 b ≤ convLoose 2 72 1) := by
  native_decide

section
variable (h0 : ∀ g ≤ 56, CapValidMuAt 0 capTab0 g)
  (h1 : ∀ g ≤ 54, CapValidMuAt 1 capTab1 g)
  (h2 : ∀ g ≤ 46, CapValidMuAt 2 capTab2 g)
include h0 h1 h2

/-- a non-typed trail obeys the loose cap -/
theorem length_le_looseCap (t : List MarkedRow) (ht : ModelTrail t) (hnt : ¬ Typed t) :
    t.length ≤ looseCap (chargeSum t) (markCount t) := by
  have hle := length_le_percapVal h0 h1 h2 t ht (chargeSum t) (markCount t) le_rfl le_rfl
  unfold looseCap
  split
  · rename_i g hg
    split
    · rename_i hcg
      -- if t.length = percapVal then t would be typed
      by_contra hlt
      have heq : t.length = percapVal (chargeSum t) (markCount t) := by omega
      exact hnt ⟨g, by rw [heq]; exact hg, hcg⟩
    · exact hle
  · exact hle

omit h0 h1 h2 in
theorem lookups_eq (τ u b : ℕ) (hτ : τ < 4) (hu : u < 73) (hb : b < 4) (c m : ℕ) (hc : c ≤ u) (hm : m ≤ b) :
    pcT c m + convAll τ (u - c) (b - m) ≤ convAll (τ + 1) u b ∧
    looseCap c m + convAll τ (u - c) (b - m) ≤ convLoose (τ + 1) u b ∧
    (τ = 0 ∨ pcT c m + convLoose τ (u - c) (b - m) ≤ convLoose (τ + 1) u b) := by
  have h := eqTabsChecked_true
  unfold eqTabsChecked at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    Bool.or_eq_true] at h
  obtain ⟨⟨a1, a2⟩, a3⟩ := h τ hτ u hu b hb c (by omega) m (by omega)
  exact ⟨a1, a2, a3⟩

/-- all-trails bound on the small range -/
theorem trails_le_convAll : ∀ (trails : List (List MarkedRow)) (τ u b : ℕ),
    τ ≤ 4 → u ≤ 72 → b ≤ 3 → trails.length ≤ τ → (∀ t ∈ trails, ModelTrail t) →
    (trails.map chargeSum).sum ≤ u → (trails.map markCount).sum ≤ b →
    (trails.map List.length).sum ≤ convAll τ u b := by
  intro trails
  induction trails with
  | nil => intro τ u b _ _ _ _ _ _ _; simp
  | cons t ts ih =>
      intro τ u b hτ hu hb hlen hmodel hcharge hmarks
      cases τ with
      | zero => simp at hlen
      | succ τ =>
          simp only [List.map_cons, List.sum_cons, List.length_cons] at hcharge hmarks hlen ⊢
          have ht := hmodel t (by simp)
          have e1 := length_le_percapVal h0 h1 h2 t ht (chargeSum t) (markCount t) le_rfl le_rfl
          have e2 := ih τ (u - chargeSum t) (b - markCount t) (by omega) (by omega) (by omega) (by omega)
            (fun s hs => hmodel s (by simp [hs])) (by omega) (by omega)
          have e3 := (lookups_eq τ u b (by omega) (by omega) (by omega) (chargeSum t) (markCount t)
            (by omega) (by omega)).1
          unfold pcT at e3
          omega

/-- loose-family bound: if some trail is not typed -/
theorem trails_le_convLoose : ∀ (trails : List (List MarkedRow)) (τ u b : ℕ),
    τ ≤ 4 → u ≤ 72 → b ≤ 3 → trails.length ≤ τ → (∀ t ∈ trails, ModelTrail t) →
    (trails.map chargeSum).sum ≤ u → (trails.map markCount).sum ≤ b →
    (∃ t ∈ trails, ¬ Typed t) →
    (trails.map List.length).sum ≤ convLoose τ u b := by
  intro trails
  induction trails with
  | nil => intro τ u b _ _ _ _ _ _ _ hex; simp at hex
  | cons t ts ih =>
      intro τ u b hτ hu hb hlen hmodel hcharge hmarks hex
      cases τ with
      | zero => simp at hlen
      | succ τ =>
          simp only [List.map_cons, List.sum_cons, List.length_cons] at hcharge hmarks hlen ⊢
          have ht := hmodel t (by simp)
          have hlk := lookups_eq τ u b (by omega) (by omega) (by omega) (chargeSum t) (markCount t)
            (by omega) (by omega)
          by_cases htt : Typed t
          · -- the loose trail is among ts (so ts ≠ [] and τ ≥ 1)
            obtain ⟨s, hs, hns⟩ := hex
            have hs' : s ∈ ts := by
              rcases List.mem_cons.mp hs with rfl | h
              · exact absurd htt hns
              · exact h
            have hτpos : τ ≠ 0 := by
              intro h0'; subst h0'
              have : ts = [] := List.eq_nil_of_length_eq_zero (by omega)
              rw [this] at hs'; simp at hs'
            have e1 := length_le_percapVal h0 h1 h2 t ht (chargeSum t) (markCount t) le_rfl le_rfl
            have e2 := ih τ (u - chargeSum t) (b - markCount t) (by omega) (by omega) (by omega) (by omega)
              (fun s hs => hmodel s (by simp [hs])) (by omega) (by omega) ⟨s, hs', hns⟩
            rcases hlk.2.2 with h | h
            · exact absurd h hτpos
            · unfold pcT at h; omega
          · have e1 := length_le_looseCap h0 h1 h2 t ht htt
            have e2 := trails_le_convAll h0 h1 h2 ts τ (u - chargeSum t) (b - markCount t) (by omega)
              (by omega) (by omega) (by omega) (fun s hs => hmodel s (by simp [hs])) (by omega) (by omega)
            have := hlk.2.1
            omega

/-- In the three equality parameter sets, every trail of an instance is typed. -/
theorem all_typed {k τ u u' b : ℕ} (inst : CoarsenedInstance k τ u' b) (hu' : u' ≤ u)
    (hcell : (k = 130 ∧ τ = 4 ∧ u = 60 ∧ b ≤ 3) ∨ (k = 131 ∧ τ = 3 ∧ u = 66 ∧ b ≤ 2) ∨
      (k = 132 ∧ τ = 2 ∧ u = 72 ∧ b ≤ 1)) :
    ∀ t ∈ inst.trails, Typed t := by
  by_contra hnot
  push Not at hnot
  have hmodel : ∀ t ∈ inst.trails, ModelTrail t := by
    intro t ht
    refine ⟨?_, inst.compat t ht, pairwise_of_flatten_pairwise ht inst.disjoint⟩
    intro x hx
    exact inst.interior x (List.mem_flatten.mpr ⟨t, ht, hx⟩)
  have hcharge : (inst.trails.map chargeSum).sum ≤ u := by
    have : (inst.trails.map chargeSum).sum = (inst.trails.flatten.map MarkedRow.charge).sum := by
      unfold chargeSum
      rw [List.map_flatten, List.sum_flatten, List.map_map]
      rfl
    rw [this]; exact le_trans inst.charge_le hu'
  have hmarks : (inst.trails.map markCount).sum ≤ b := by
    have : (inst.trails.map markCount).sum = markCount inst.trails.flatten := by
      unfold markCount
      rw [List.countP_flatten]
    rw [this]
    exact le_trans (markCount_le_runs _) inst.runs_le
  have hrows : (inst.trails.map List.length).sum = k := by
    rw [← List.length_flatten]; exact inst.row_count
  have hchk := eqCellsChecked_true
  unfold eqCellsChecked at hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
  rcases hcell with ⟨rfl, rfl, rfl, hb⟩ | ⟨rfl, rfl, rfl, hb⟩ | ⟨rfl, rfl, rfl, hb⟩
  · have := trails_le_convLoose h0 h1 h2 inst.trails 4 60 b (by omega) (by omega) hb inst.trail_count
      hmodel hcharge hmarks hnot
    have hbm : convLoose 4 60 b ≤ convLoose 4 60 3 := convLoose_mono_cells.1 b hb
    omega
  · have := trails_le_convLoose h0 h1 h2 inst.trails 3 66 b (by omega) (by omega) (by omega) inst.trail_count
      hmodel hcharge hmarks hnot
    have hbm : convLoose 3 66 b ≤ convLoose 3 66 2 := convLoose_mono_cells.2.1 b hb
    omega
  · have := trails_le_convLoose h0 h1 h2 inst.trails 2 72 b (by omega) (by omega) (by omega) inst.trail_count
      hmodel hcharge hmarks hnot
    have hbm : convLoose 2 72 b ≤ convLoose 2 72 1 := convLoose_mono_cells.2.2 b hb
    omega

end

end Superperm7
