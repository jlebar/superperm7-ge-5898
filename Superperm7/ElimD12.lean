/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.ElimD12Data
/-!
# Elimination of every coarsened certificate with defect at most twelve

A `CoarsenedInstance k τ u b` consists of at most `τ` model trails carrying
`k` rows in total with total charge at most `u`.  Each trail of charge `c`
has at most `capW c` rows, so `k ≤ F τ u` where `F` is the `τ`-fold max-plus
convolution of `capW`.  A finite arithmetic sweep shows `F τ u < k` for every
registry cell `(m, a, b, η, r)` with `m + a + b + η ≤ 12`, where
`k = 120 + m − r + a`, `τ = η + 1 + b`, `u = 6m − r`.
-/

namespace Superperm7

/-! ## Max-plus convolution of the single-trail cap (tabulated, `τ ≤ 13`, `u ≤ 72`) -/

theorem capWTab_spec : ∀ u < 73, capWTab.getD u 0 = capW u := by
  intro u hu
  simp [capWTab, Array.getD, hu]

theorem convF_zero : ∀ u < 73, convF 0 u = 0 := by native_decide

theorem convChecked_true : convChecked = true := by native_decide

theorem le_convF_succ : ∀ τ < 13, ∀ u < 73, ∀ u1 ≤ u,
    capW u1 + convF τ (u - u1) ≤ convF (τ + 1) u := by
  intro τ hτ u hu u1 hu1
  have h := convChecked_true
  unfold convChecked at h
  simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  rw [← capWTab_spec u1 (by omega)]
  exact h τ hτ u hu u1 (by omega)

/-- A list of at most `τ ≤ 13` model trails with total charge `≤ u ≤ 72`
carries at most `convF τ u` rows. -/
theorem trails_rows_le_convF : ∀ (trails : List (List MarkedRow)) (τ u : ℕ),
    τ ≤ 13 → u ≤ 72 →
    trails.length ≤ τ →
    (∀ t ∈ trails, ModelTrail t) →
    (trails.map chargeSum).sum ≤ u →
    (trails.map List.length).sum ≤ convF τ u := by
  intro trails
  induction trails with
  | nil => intro τ u _ _ _ _ _; simp
  | cons t ts ih =>
      intro τ u hτ hu hlen hmodel hcharge
      cases τ with
      | zero => simp at hlen
      | succ τ =>
          simp only [List.map_cons, List.sum_cons, List.length_cons] at hcharge hlen ⊢
          have ht : ModelTrail t := hmodel t (by simp)
          have h1 : t.length ≤ capW (chargeSum t) := modelTrail_length_le_capW t ht _ le_rfl
          have h2 := ih τ (u - chargeSum t) (by omega) (by omega) (by omega)
            (fun s hs => hmodel s (by simp [hs])) (by omega)
          have h3 := le_convF_succ τ (by omega) u (by omega) (chargeSum t) (by omega)
          omega

/-! ## From a coarsened certificate to the convolution bound -/

theorem pairwise_of_flatten_pairwise {t : List MarkedRow} {trails : List (List MarkedRow)}
    (ht : t ∈ trails) (hpair : trails.flatten.Pairwise MarkedDisjoint) :
    t.Pairwise MarkedDisjoint :=
  hpair.sublist (List.sublist_flatten_of_mem ht)

theorem coarsened_rows_le_convF {k τ u b : ℕ} (inst : CoarsenedInstance k τ u b)
    (hτ : τ ≤ 13) (hu : u ≤ 72) : k ≤ convF τ u := by
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
  have hrows : (inst.trails.map List.length).sum = k := by
    rw [← List.length_flatten]; exact inst.row_count
  rw [← hrows]
  exact trails_rows_le_convF inst.trails τ u hτ hu inst.trail_count hmodel hcharge

/-! ## The registry sweep -/

theorem sweepChecked_true : sweepChecked = true := by native_decide

/-- Every registry cell with defect at most twelve fails the capacity test. -/
theorem sweep : ∀ m ≤ 12, ∀ a ≤ 12, ∀ b ≤ 12, ∀ eta ≤ 12, ∀ r ≤ 72,
    m + a + b + eta ≤ 12 → a ≤ r → r ≤ 6 * m → cellDead m a b eta r = true := by
  intro m hm a ha b hb eta heta r hr h1 h2 h3
  have h := sweepChecked_true
  unfold sweepChecked at h
  simp only [List.all_eq_true, List.mem_range] at h
  have := h m (by omega) a (by omega) b (by omega) eta (by omega) r (by omega)
  simp only [h1, h2, h3, decide_true, Bool.and_self, Bool.not_true, Bool.false_or] at this
  exact this

/-- Enlarging the charge budget of a certificate. -/
def CoarsenedInstance.relaxCharge {k τ u u' b : ℕ} (inst : CoarsenedInstance k τ u' b)
    (h : u' ≤ u) : CoarsenedInstance k τ u b :=
  { trails := inst.trails, trail_count := inst.trail_count, row_count := inst.row_count,
    compat := inst.compat, disjoint := inst.disjoint, interior := inst.interior,
    charge_le := le_trans inst.charge_le h, runs_le := inst.runs_le }

/-- **No coarsened certificate exists for a registry cell of defect at most
twelve.**  This is the finite heart of `s(7) ≥ 5897`. -/
theorem no_coarsened_instance (m a b eta r u' : ℕ)
    (hdefect : m + a + b + eta ≤ 12) (har : a ≤ r) (hr : r ≤ 6 * m) (hu' : u' ≤ 6 * m - r)
    (inst : CoarsenedInstance (120 + m - r + a) (eta + 1 + b) u' b) : False := by
  have hle := coarsened_rows_le_convF (inst.relaxCharge hu') (by omega) (by omega)
  have hdead := sweep m (by omega) a (by omega) b (by omega) eta (by omega) r (by omega)
    hdefect har hr
  unfold cellDead at hdead
  simp only [decide_eq_true_eq] at hdead
  omega

end Superperm7
