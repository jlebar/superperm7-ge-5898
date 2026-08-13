/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.ClosureMu

/-!
# Direct high-target queries

A few single failed searches with targets well above the true capacity,
pruned by already-valid caps.  They sharpen the per-trail cap exactly where
the mark-splitting closures are loose (one heavy trail carrying marked rows),
at negligible cost.  Each gives: every model trail with at most `μ` marked
rows and charge `≤ g` has fewer than `T` rows.
-/

namespace Superperm7

/-- base per-trail cap from the closures: valid for trails with at most `m` marks
(`capW` is valid for every trail; `capMu m` for `m ≤ 2`) -/
def baseCap (c m : ℕ) : ℕ := if m ≤ 2 then min (capW c) (capMu m c) else capW c

/-- pruning caps for a direct query at mark budget `m`: `baseCap` below `g` -/
def dcaps (m g : ℕ) : Array ℕ := (Array.range g).map fun c => baseCap c m

theorem dcaps_getD (m g c : ℕ) (hc : c < g) : (dcaps m g).getD c 0 = baseCap c m := by
  simp [dcaps, Array.getD, hc]

/-- The list of direct queries `(μ, g, T)`. -/
def directQueries : List (ℕ × ℕ × ℕ) :=
  [(0, 78, 130),
   (1, 58, 101), (1, 60, 105), (1, 62, 108), (1, 64, 112), (1, 66, 116), (1, 68, 119), (1, 70, 123),
   (2, 52, 94), (2, 58, 105),
   (3, 42, 80), (3, 48, 91)]

def directChecked : Bool :=
  directQueries.all fun (μ, g, T) => Fast.fsearch (dcaps μ g) g T μ T == false

theorem directChecked_true : directChecked = true := by native_decide

/-- the sharpest direct target applying to `(c, m)`: min over queries `(μ, g, T)` with
`m ≤ μ` and `c ≤ g` of `T - 1` (or a large number) -/
def directCap (c m : ℕ) : ℕ :=
  (directQueries.filter fun (μ, g, _) => decide (m ≤ μ) && decide (c ≤ g)).foldl
    (fun acc (_, _, T) => min acc (T - 1)) 100000

section
variable (h0 : ∀ g ≤ 56, CapValidMuAt 0 capTab0 g)
  (h1 : ∀ g ≤ 54, CapValidMuAt 1 capTab1 g)
  (h2 : ∀ g ≤ 46, CapValidMuAt 2 capTab2 g)
include h0 h1 h2

theorem length_le_baseCap (t : List MarkedRow) (ht : ModelTrail t) (c m : ℕ)
    (hc : chargeSum t ≤ c) (hm : markCount t ≤ m) : t.length ≤ baseCap c m := by
  have hW := modelTrail_length_le_capW t ht c hc
  unfold baseCap
  split
  · rename_i hm2
    exact le_min hW (modelTrail_length_le_capMu h0 h1 h2 m hm2 t ht hm c hc)
  · exact hW

theorem dcaps_validBelow (m g : ℕ) : CapsValidMuBelow m (dcaps m g) g := by
  intro c hc rows hmodel hm hcharge
  rw [dcaps_getD m g c hc]
  exact length_le_baseCap h0 h1 h2 rows hmodel c m hcharge hm

/-- Each listed direct query is a valid strict row bound. -/
theorem direct_of_mem (μ g T : ℕ) (hmem : (μ, g, T) ∈ directQueries)
    (rows : List MarkedRow) (hmodel : ModelTrail rows) (hm : markCount rows ≤ μ)
    (hcharge : chargeSum rows ≤ g) : rows.length < T := by
  have hall := directChecked_true
  unfold directChecked at hall
  rw [List.all_eq_true] at hall
  have h := hall (μ, g, T) hmem
  simp only [beq_iff_eq] at h
  have hT : 0 < T := by
    simp only [directQueries, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
    omega
  exact length_lt_of_fsearch_false (dcaps μ g) g T μ T (dcaps_validBelow h0 h1 h2 μ g) hT (by omega) h
    rows hmodel hm hcharge

/-- The combined direct cap is valid. -/
theorem length_le_directCap (rows : List MarkedRow) (hmodel : ModelTrail rows) (c m : ℕ)
    (hcharge : chargeSum rows ≤ c) (hm : markCount rows ≤ m) : rows.length ≤ directCap c m := by
  unfold directCap
  -- fold over the filtered list: every step keeps an upper bound
  have key : ∀ (l : List (ℕ × ℕ × ℕ)), (∀ q ∈ l, q ∈ directQueries ∧ m ≤ q.1 ∧ c ≤ q.2.1) →
      ∀ acc, rows.length ≤ acc →
        rows.length ≤ l.foldl (fun acc (q : ℕ × ℕ × ℕ) => min acc (q.2.2 - 1)) acc := by
    intro l
    induction l with
    | nil => intro _ acc hacc; simpa
    | cons q qs ih =>
        intro hl acc hacc
        simp only [List.foldl_cons]
        apply ih (fun q' hq' => hl q' (by simp [hq']))
        obtain ⟨hq, hμ, hg⟩ := hl q (by simp)
        rcases q with ⟨μ, g, T⟩
        have := direct_of_mem h0 h1 h2 μ g T hq rows hmodel (by simp at hμ; omega) (by simp at hg; omega)
        simp only
        omega
  apply key
  · intro q hq
    rw [List.mem_filter] at hq
    rcases q with ⟨μ, g, T⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hq
    exact ⟨hq.1, hq.2.1, hq.2.2⟩
  · have := modelTrail_length_le_720 rows hmodel; omega

end

end Superperm7
