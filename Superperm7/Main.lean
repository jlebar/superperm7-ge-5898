/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.EqualityCells
import Superperm7.EqualityChecks
import Superperm7.Cert.M0
import Superperm7.Cert.M1
import Superperm7.Cert.M2
import Superperm7.CoarsenBridge
import Superperm7.Witness

/-!
# Main theorem: `5898 ≤ s(7) ≤ 5906`

Assembly of the lower bound.  A superpermutation of length `≤ 5897` gives (path formulation,
normalization) a normalized Hamiltonian route of weight `≤ 5890`, hence (cheap cover, orbit
inequality, permutation-map counts) a realized registry candidate with defect `m+a+b+η ≤ 13`,
hence (surgery bridge) a coarsened certificate `CoarsenedInstance (120+m−r+a) (η+1+b) u' b` with
`u' ≤ 6m−r`.  Cells other than the nine equality cells are excluded by the capacity sweep over
the certified tables `capTab0/1/2` with mark-splitting closure and direct queries
(`ElimD13.lean`, `no_coarsened_instance13`); the equality cells reduce, via the tightness
computation and the optimal-trail enumeration, to five template families, which the relabelled
join checks exclude (`EqualityCells.lean`, `EqChecks/*`).

`Bound5897.lean` contains an independent, much cheaper elimination (defect `≤ 12` only, from the
all-marks table to charge 36) giving `s(7) ≥ 5897`; nothing here depends on it.
-/

namespace Superperm7

/-! ## The certified tables discharge the hypotheses -/

theorem H0 : ∀ g ≤ 56, CapValidMuAt 0 capTab0 g := capTab0_valid
theorem H1 : ∀ g ≤ 54, CapValidMuAt 1 capTab1 g := capTab1_valid
theorem H2 : ∀ g ≤ 46, CapValidMuAt 2 capTab2 g := capTab2_valid

/-! ## Equality cells: typed trails form a template family -/

/-- the multiset (as a sorted list) of template charges of a typed family -/
theorem typed_ofType (t : List MarkedRow) (ht : ModelTrail t) (hm : markCount t ≤ 3) (htt : Typed t) :
    ∃ g, chargeOfLen t.length = some g ∧ OfType g t := by
  obtain ⟨g, hg, hc⟩ := htt
  obtain ⟨hopt, _⟩ := chargeOfLen_optLen hg
  exact ⟨g, hg, ht, hm, hc, hopt.symm⟩

/-- Boolean: every list of `τ` template lengths (each in {31,34,50,63,66}) summing to `k`
has its charge list (via `chargeOfLen`), after moving some member to the front, equal to one of
the five join-checked shapes `(g₁, gs)` up to the order of `gs` handled by `placeable`'s
symmetry — we simply require: some rotation `(g₁ :: gs)` of the charge list has
`joinImpossible g₁ gs = true` among the five checked, as literal lists after sorting `gs`. -/
def lenChoices : List ℕ := [31, 34, 50, 63, 66]

def chargeOfLen! (n : ℕ) : ℕ := (chargeOfLen n).getD 0

/-- all length lists of exactly `τ` template lengths summing to `k` -/
def lenLists : ℕ → ℕ → List (List ℕ)
  | 0, k => if k = 0 then [[]] else []
  | τ + 1, k => lenChoices.flatMap fun ℓ => if ℓ ≤ k then (lenLists τ (k - ℓ)).map (ℓ :: ·) else []

/-- the five checked shapes, as (first charge, remaining charges) with the remaining list in the
exact order used in `joins_checked` -/
def checkedShapes : List (ℕ × List ℕ) :=
  [(36, [36]), (16, [16, 34]), (14, [26, 26]), (14, [16, 36]), (14, [14, 16, 16])]

/-- every length list for the three cells, read as charges, is a permutation of a checked shape -/
def shapesCovered : Bool :=
  ([(4, 130), (3, 131), (2, 132)] : List (ℕ × ℕ)).all fun (τ, k) =>
    (List.range (τ + 1)).all fun n => (lenLists n k).all fun ls =>
      let cs := ls.map chargeOfLen!
      checkedShapes.any fun (g1, gs) => decide ((g1 :: gs).Perm cs)

theorem shapesCovered_true : shapesCovered = true := by decide

theorem mem_lenLists : ∀ (τ k : ℕ) (ls : List ℕ), ls.length = τ → (∀ ℓ ∈ ls, ℓ ∈ lenChoices) →
    ls.sum = k → ls ∈ lenLists τ k := by
  intro τ
  induction τ with
  | zero =>
      intro k ls hlen _ hsum
      have : ls = [] := List.eq_nil_of_length_eq_zero hlen
      subst this
      simp at hsum
      subst hsum
      simp [lenLists]
  | succ τ ih =>
      intro k ls hlen hmem hsum
      cases ls with
      | nil => simp at hlen
      | cons ℓ rest =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
          simp only [List.sum_cons] at hsum
          unfold lenLists
          rw [List.mem_flatMap]
          refine ⟨ℓ, hmem ℓ (by simp), ?_⟩
          rw [if_pos (by omega), List.mem_map]
          exact ⟨rest, ih (k - ℓ) rest hlen (fun x hx => hmem x (by simp [hx])) (by omega), rfl⟩

theorem chargeOfLen_mem_lenChoices {n g : ℕ} (h : chargeOfLen n = some g) : n ∈ lenChoices := by
  unfold chargeOfLen at h
  unfold lenChoices
  split_ifs at h <;> subst_vars <;> simp

theorem crossDisjointFamily_of_flatten : ∀ (ts : List (List MarkedRow)),
    ts.flatten.Pairwise MarkedDisjoint → CrossDisjointFamily ts := by
  intro ts
  induction ts with
  | nil => intro _; exact List.Pairwise.nil
  | cons t ts ih =>
      intro hp
      simp only [List.flatten_cons] at hp
      rw [List.pairwise_append] at hp
      refine List.Pairwise.cons ?_ (ih hp.2.1)
      intro s hs x hx y hy
      exact hp.2.2 x hx y (List.mem_flatten.mpr ⟨s, hs, hy⟩)

/-- No coarsened certificate exists in an equality cell. -/
theorem no_equality_instance {k τ u u' b : ℕ} (inst : CoarsenedInstance k τ u' b) (hu' : u' ≤ u)
    (hcell : (k = 130 ∧ τ = 4 ∧ u = 60 ∧ b ≤ 3) ∨ (k = 131 ∧ τ = 3 ∧ u = 66 ∧ b ≤ 2) ∨
      (k = 132 ∧ τ = 2 ∧ u = 72 ∧ b ≤ 1)) : False := by
  have htyped := all_typed H0 H1 H2 inst hu' hcell
  have hmodel : ∀ t ∈ inst.trails, ModelTrail t := by
    intro t ht
    refine ⟨?_, inst.compat t ht, pairwise_of_flatten_pairwise ht inst.disjoint⟩
    intro x hx
    exact inst.interior x (List.mem_flatten.mpr ⟨t, ht, hx⟩)
  have hmarks3 : ∀ t ∈ inst.trails, markCount t ≤ 3 := by
    intro t ht
    have hsum : (inst.trails.map markCount).sum ≤ b := by
      have : (inst.trails.map markCount).sum = markCount inst.trails.flatten := by
        unfold markCount; rw [List.countP_flatten]
      rw [this]; exact le_trans (markCount_le_runs _) inst.runs_le
    have hle : markCount t ≤ (inst.trails.map markCount).sum :=
      List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map_of_mem ht)
    rcases hcell with ⟨_, _, _, hb⟩ | ⟨_, _, _, hb⟩ | ⟨_, _, _, hb⟩ <;> omega
  -- the family is cross-disjoint (from the flattened pairwise disjointness)
  have hfam : CrossDisjointFamily inst.trails := crossDisjointFamily_of_flatten _ inst.disjoint
  -- lengths: each a template length; they sum to k; there are exactly τ trails (τ ≤ trails ≤ τ
  -- since each typed trail has ≥ 31 rows and k < 31·(τ+1))
  have hlens : ∀ t ∈ inst.trails, t.length ∈ lenChoices := by
    intro t ht
    obtain ⟨g, hg, _⟩ := htyped t ht
    exact chargeOfLen_mem_lenChoices hg
  have hsum : (inst.trails.map List.length).sum = k := by
    rw [← List.length_flatten]; exact inst.row_count
  -- the length list is in lenLists τ k, so its charge list is a permutation of a checked shape
  have hll := mem_lenLists inst.trails.length k (inst.trails.map List.length) (by simp)
    (fun ℓ hℓ => by obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hℓ; exact hlens t ht) hsum
  have hsc := shapesCovered_true
  unfold shapesCovered at hsc
  rw [List.all_eq_true] at hsc
  have hτk : (τ, k) ∈ ([(4, 130), (3, 131), (2, 132)] : List (ℕ × ℕ)) := by
    rcases hcell with ⟨rfl, rfl, _, _⟩ | ⟨rfl, rfl, _, _⟩ | ⟨rfl, rfl, _, _⟩ <;> simp
  have := hsc (τ, k) hτk
  rw [List.all_eq_true] at this
  have := this inst.trails.length (by simp; have := inst.trail_count; omega)
  rw [List.all_eq_true] at this
  have := this _ hll
  rw [List.any_eq_true] at this
  obtain ⟨⟨g1, gs⟩, hshape, hperm⟩ := this
  simp only [decide_eq_true_eq] at hperm
  -- charges list cs := trails.map (chargeOfLen! ∘ length); build the Forall₂ OfType (cs) (trails)
  have hOf : List.Forall₂ OfType (inst.trails.map fun t => chargeOfLen! t.length) inst.trails := by
    have : ∀ (l : List (List MarkedRow)), (∀ t ∈ l, ModelTrail t) → (∀ t ∈ l, markCount t ≤ 3) →
        (∀ t ∈ l, Typed t) → List.Forall₂ OfType (l.map fun t => chargeOfLen! t.length) l := by
      intro l
      induction l with
      | nil => intro _ _ _; exact List.Forall₂.nil
      | cons t ts ih =>
          intro hm hk ht
          refine List.Forall₂.cons ?_ (ih (fun s hs => hm s (by simp [hs])) (fun s hs => hk s (by simp [hs]))
            (fun s hs => ht s (by simp [hs])))
          obtain ⟨g, hg, hot⟩ := typed_ofType t (hm t (by simp)) (hk t (by simp)) (ht t (by simp))
          have : chargeOfLen! t.length = g := by unfold chargeOfLen!; rw [hg]; rfl
          show OfType (chargeOfLen! t.length) t
          rw [this]; exact hot
    exact this _ hmodel hmarks3 htyped
  -- reorder the family along the permutation (g1 :: gs) ~ cs
  have hcs : (inst.trails.map List.length).map chargeOfLen! = inst.trails.map (fun t => chargeOfLen! t.length) := by
    rw [List.map_map]; rfl
  rw [hcs] at hperm
  -- obtain a permutation of trails matching (g1 :: gs)
  obtain ⟨ts', hts'perm, hts'⟩ : ∃ ts' : List (List MarkedRow), ts'.Perm inst.trails ∧
      List.Forall₂ OfType (g1 :: gs) ts' := by
    have key : ∀ (cs : List ℕ) (ts : List (List MarkedRow)), List.Forall₂ OfType cs ts →
        ∀ (cs' : List ℕ), cs'.Perm cs → ∃ ts', ts'.Perm ts ∧ List.Forall₂ OfType cs' ts' := by
      intro cs ts h cs' hp
      induction hp generalizing ts with
      | nil => cases h; exact ⟨[], List.Perm.refl _, List.Forall₂.nil⟩
      | cons x _ ih =>
          cases h with
          | cons hx hrest =>
              obtain ⟨ts', hp', hf'⟩ := ih _ hrest
              exact ⟨_ :: ts', hp'.cons _, List.Forall₂.cons hx hf'⟩
      | swap x y l =>
          cases h with
          | cons hy hrest =>
              cases hrest with
              | cons hx hrest' => exact ⟨_ :: _ :: _, List.Perm.swap _ _ _, List.Forall₂.cons hx (List.Forall₂.cons hy hrest')⟩
      | trans _ _ ih1 ih2 =>
          obtain ⟨ts1, hp1, hf1⟩ := ih2 _ h
          obtain ⟨ts2, hp2, hf2⟩ := ih1 _ hf1
          exact ⟨ts2, hp2.trans hp1, hf2⟩
    exact key _ _ hOf _ hperm
  cases hts' with
  | cons ht1 hrest =>
      rename_i t1 rest
      have hfam' : CrossDisjointFamily (t1 :: rest) := by
        unfold CrossDisjointFamily at hfam ⊢
        exact hfam.perm hts'perm.symm (fun hst => cross_symm hst)
      -- positivity of optLen for the shape charges
      have hposAll : ∀ g ∈ (g1 :: gs), 0 < optLen g := by
        intro g hg
        simp only [checkedShapes, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hshape
        obtain ⟨e14, e16, e26, e34, e36⟩ := optLen_values
        rcases hshape with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hg <;>
          rcases hg with rfl | rfl | rfl | rfl <;> omega
      have hj : joinImpossible g1 gs = true := by
        obtain ⟨j1, j2, j3, j4, j5⟩ := joins_checked
        simp only [checkedShapes, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hshape
        rcases hshape with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact j1
        · exact j2
        · exact j3
        · exact j4
        · exact j5
      exact no_family_of_joinImpossible H0 H1 H2 g1 gs hj (hposAll g1 (by simp))
        (fun g hg => hposAll g (by simp [hg])) t1 rest ht1 hrest hfam'

/-! ## All cells with defect ≤ 13 -/

theorem no_coarsened_instance_le13 (m a b eta r u' : ℕ)
    (hdefect : m + a + b + eta ≤ 13) (har : a ≤ r) (hr : r ≤ 6 * m) (hu' : u' ≤ 6 * m - r)
    (inst : CoarsenedInstance (120 + m - r + a) (eta + 1 + b) u' b) : False := by
  by_cases heq : isEqualityCell m a b eta r = true
  · unfold isEqualityCell at heq
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at heq
    obtain ⟨⟨ha0, hr0⟩, hcases⟩ := heq
    subst ha0; subst hr0
    rcases hcases with (⟨hm, hbe⟩ | ⟨hm, hbe⟩) | ⟨hm, hbe⟩ <;> subst hm
    · have hk : 120 + 10 - 0 + 0 = 130 := by norm_num
      have hτ : eta + 1 + b = 4 := by omega
      rw [hk, hτ] at inst
      exact no_equality_instance (u := 60) inst (by simpa using hu') (Or.inl ⟨rfl, rfl, rfl, by omega⟩)
    · have hk : 120 + 11 - 0 + 0 = 131 := by norm_num
      have hτ : eta + 1 + b = 3 := by omega
      rw [hk, hτ] at inst
      exact no_equality_instance (u := 66) inst (by simpa using hu') (Or.inr (Or.inl ⟨rfl, rfl, rfl, by omega⟩))
    · have hk : 120 + 12 - 0 + 0 = 132 := by norm_num
      have hτ : eta + 1 + b = 2 := by omega
      rw [hk, hτ] at inst
      exact no_equality_instance (u := 72) inst (by simpa using hu') (Or.inr (Or.inr ⟨rfl, rfl, rfl, by omega⟩))
  · exact no_coarsened_instance13 H0 H1 H2 m a b eta r u' hdefect har hr hu' (by simpa using heq) inst

/-! ## Assembly -/

theorem no_realized_registry_candidate :
    ¬ ∃ (route : List Perm7) (hroute : IsHamiltonianRoute route) (c : RegistryCandidate),
      RouteRealizesRegistryCandidate route hroute c := by
  rintro ⟨route, hroute, c, hreal⟩
  have hvalid : c.valid := hreal.1
  obtain ⟨u', hu', ⟨inst⟩⟩ := coarsen_bridge hreal
  rcases hvalid with ⟨hdefect, har, hr, _⟩
  exact no_coarsened_instance_le13 c.m c.a c.b c.eta c.r u' hdefect har hr hu' inst

theorem no_hamiltonian_route_of_weight_at_most_5890 :
    ¬ ∃ route : List Perm7, IsHamiltonianRoute route ∧ routeWeight route ≤ 5890 := by
  rintro ⟨route, hroute, hweight⟩
  obtain ⟨route', hroute', hnormal', hweight'⟩ := normalized_route_of_weight_at_most hroute hweight
  obtain ⟨c, hc⟩ := normalized_light_route_realizes_registryCandidate hroute' hnormal' hweight'
  exact no_realized_registry_candidate ⟨route', hroute', c, hc⟩

/-- **Lower bound.** Every superpermutation on seven symbols has length at least `5898`. -/
theorem lower_bound : ∀ w : Word, IsSuperpermutation w → 5898 ≤ w.length := by
  intro w hw
  by_contra hshort
  have hlength : w.length ≤ 7 + 5890 := by omega
  exact no_hamiltonian_route_of_weight_at_most_5890
    ((exact_path_formulation 5890).mp ⟨w, hw, hlength⟩)

/-- **Main theorem.** `5898 ≤ s(7) ≤ 5906`: some superpermutation on seven symbols has length
`5906` (the Egan–Houston word of 2019), and every superpermutation on seven symbols has length at least `5898`. -/
theorem main_theorem :
    (∃ w : Word, IsSuperpermutation w ∧ w.length = 5906) ∧
    (∀ w : Word, IsSuperpermutation w → 5898 ≤ w.length) :=
  ⟨verified_upper_bound, lower_bound⟩

end Superperm7
