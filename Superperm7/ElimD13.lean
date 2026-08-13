/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.ElimD13Data
import Superperm7.ElimD12
/-!
# Elimination of every non-equality certificate with defect at most thirteen

With the certified tables (`capTab0/1/2`, taken as hypotheses `h0 h1 h2`),
their mark-splitting closure `capMu`, the all-marks cap `capW`, and the direct
queries of `Directs`, the per-trail cap `percapVal c m` bounds every model trail of
charge `≤ c` with at most `m` marked rows.  Its convolution over at most `τ`
trails with total charge `≤ u` and at most `b` marked rows in all bounds the
row count of any `CoarsenedInstance k τ u b`; the sweep `sweep13Checked` shows
this bound is `< k` for every cell with `m+a+b+η ≤ 13` other than the nine
equality cells.
-/

namespace Superperm7

/-! ## Marked rows and omission runs -/

theorem one_le_omissionRuns_of_marked (x : MarkedRow) (hx : isMarked x = true) :
    1 ≤ x.omissionRuns := by
  unfold isMarked at hx
  unfold MarkedRow.omissionRuns
  have key : ∀ s : Finset (Fin 6), s ≠ ∅ →
      1 ≤ (s.filter fun i => ¬ ∃ j ∈ s, j.val + 1 = i.val).card := by decide
  exact key x.omitted (by simpa using hx)

theorem markCount_le_runs (rows : List MarkedRow) :
    markCount rows ≤ (rows.map MarkedRow.omissionRuns).sum := by
  induction rows with
  | nil => simp [markCount]
  | cons x xs ih =>
      rw [markCount_cons]
      simp only [List.map_cons, List.sum_cons]
      by_cases hx : isMarked x = true
      · have := one_le_omissionRuns_of_marked x hx
        rw [if_pos hx]; omega
      · rw [if_neg hx]; omega

/-! ## Table lookups -/

theorem percapT_spec : ∀ c < 79, ∀ m < 14, percapT c m = percapVal c m := by
  intro c hc m hm
  simp [percapT, percapTab, Array.getD, hc, hm]

theorem conv13Checked_true : conv13Checked = true := by native_decide

theorem le_convF13_succ : ∀ τ < 14, ∀ u < 79, ∀ b < 14, ∀ c ≤ u, ∀ m ≤ b,
    percapVal c m + convF13 τ (u - c) (b - m) ≤ convF13 (τ + 1) u b := by
  intro τ hτ u hu b hb c hc m hm
  have h := conv13Checked_true
  unfold conv13Checked at h
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  rw [← percapT_spec c (by omega) m (by omega)]
  exact h τ hτ u hu b hb c (by omega) m (by omega)

theorem sweep13Checked_true : sweep13Checked = true := by native_decide

theorem sweep13 (m a b eta r : ℕ) (hm : m ≤ 13) (ha : a ≤ 13) (hb : b ≤ 13) (heta : eta ≤ 13)
    (hr : r ≤ 78) (h1 : m + a + b + eta ≤ 13) (h2 : a ≤ r) (h3 : r ≤ 6 * m)
    (hne : isEqualityCell m a b eta r = false) : cellDead13 m a b eta r = true := by
  have h := sweep13Checked_true
  unfold sweep13Checked at h
  simp only [List.all_eq_true, List.mem_range] at h
  have := h m (by omega) a (by omega) b (by omega) eta (by omega) r (by omega)
  simp only [h1, h2, h3, decide_true, Bool.and_self, Bool.not_true, Bool.false_or, hne] at this
  exact this

/-! ## Validity of the per-trail cap and the convolution -/

section
variable (h0 : ∀ g ≤ 56, CapValidMuAt 0 capTab0 g)
  (h1 : ∀ g ≤ 54, CapValidMuAt 1 capTab1 g)
  (h2 : ∀ g ≤ 46, CapValidMuAt 2 capTab2 g)
include h0 h1 h2

theorem length_le_percapVal (t : List MarkedRow) (ht : ModelTrail t) (c m : ℕ)
    (hc : chargeSum t ≤ c) (hm : markCount t ≤ m) : t.length ≤ percapVal c m := by
  unfold percapVal
  exact le_min (length_le_baseCap h0 h1 h2 t ht c m hc hm) (length_le_directCap h0 h1 h2 t ht c m hc hm)

/-- Trails with total charge `≤ u ≤ 78`, at most `b ≤ 13` marked rows in all,
and at most `τ ≤ 14` in number carry at most `convF13 τ u b` rows. -/
theorem trails_rows_le_convF13 : ∀ (trails : List (List MarkedRow)) (τ u b : ℕ),
    τ ≤ 14 → u ≤ 78 → b ≤ 13 →
    trails.length ≤ τ →
    (∀ t ∈ trails, ModelTrail t) →
    (trails.map chargeSum).sum ≤ u →
    (trails.map markCount).sum ≤ b →
    (trails.map List.length).sum ≤ convF13 τ u b := by
  intro trails
  induction trails with
  | nil => intro τ u b _ _ _ _ _ _ _; simp
  | cons t ts ih =>
      intro τ u b hτ hu hb hlen hmodel hcharge hmarks
      cases τ with
      | zero => simp at hlen
      | succ τ =>
          simp only [List.map_cons, List.sum_cons, List.length_cons] at hcharge hmarks hlen ⊢
          have ht : ModelTrail t := hmodel t (by simp)
          have e1 := length_le_percapVal h0 h1 h2 t ht (chargeSum t) (markCount t) le_rfl le_rfl
          have e2 := ih τ (u - chargeSum t) (b - markCount t) (by omega) (by omega) (by omega) (by omega)
            (fun s hs => hmodel s (by simp [hs])) (by omega) (by omega)
          have e3 := le_convF13_succ τ (by omega) u (by omega) b (by omega) (chargeSum t) (by omega)
            (markCount t) (by omega)
          omega

theorem coarsened_rows_le_convF13 {k τ u b : ℕ} (inst : CoarsenedInstance k τ u b)
    (hτ : τ ≤ 14) (hu : u ≤ 78) (hb : b ≤ 13) : k ≤ convF13 τ u b := by
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
    rw [this]; exact inst.charge_le
  have hmarks : (inst.trails.map markCount).sum ≤ b := by
    have : (inst.trails.map markCount).sum = markCount inst.trails.flatten := by
      unfold markCount
      rw [List.countP_flatten]
    rw [this]
    exact le_trans (markCount_le_runs _) inst.runs_le
  have hrows : (inst.trails.map List.length).sum = k := by
    rw [← List.length_flatten]; exact inst.row_count
  rw [← hrows]
  exact trails_rows_le_convF13 h0 h1 h2 inst.trails τ u b hτ hu hb inst.trail_count hmodel hcharge hmarks

/-- **No coarsened certificate exists for a non-equality cell of defect at most thirteen.** -/
theorem no_coarsened_instance13 (m a b eta r u' : ℕ)
    (hdefect : m + a + b + eta ≤ 13) (har : a ≤ r) (hr : r ≤ 6 * m) (hu' : u' ≤ 6 * m - r)
    (hne : isEqualityCell m a b eta r = false)
    (inst : CoarsenedInstance (120 + m - r + a) (eta + 1 + b) u' b) : False := by
  have hle := coarsened_rows_le_convF13 h0 h1 h2 (inst.relaxCharge hu') (by omega) (by omega) (by omega)
  have hdead := sweep13 m a b eta r (by omega) (by omega) (by omega) (by omega) (by omega)
    hdefect har hr hne
  unfold cellDead13 at hdead
  simp only [decide_eq_true_eq] at hdead
  omega

end

end Superperm7
