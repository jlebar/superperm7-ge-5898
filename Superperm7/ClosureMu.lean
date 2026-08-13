/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CapTabs
import Superperm7.Closure

/-!
# Mark-indexed superadditive closure

Three certified tables — `capTab0` (no marked row, charges ≤ 56), `capTab1`
(≤ 1 marked row, ≤ 54), `capTab2` (≤ 2 marked rows, ≤ 46) — are extended to
row caps `capMu μ u` for every charge budget `u`, by superadditivity with mark
splitting: cutting a trail with at most `μ` marked rows gives two trails whose
mark counts add up to at most `μ` and whose charges add.

The validity of the three tables is taken as a hypothesis here (it is proved
by the sharded certificates `Cert.M0/M1/M2`), so this file compiles
independently of them.
-/

namespace Superperm7

/-! ## Base bounds from the three tables -/

def muG : ℕ → ℕ
  | 0 => 56
  | 1 => 54
  | _ => 46

def muTab : ℕ → Array ℕ
  | 0 => capTab0
  | 1 => capTab1
  | _ => capTab2

/-- least certified charge for `L` rows with at most `μ` marks, or `G_μ + 1` -/
def rhoBaseMu (μ L : ℕ) : ℕ :=
  match (List.range (muG μ + 1)).find? (fun g => decide (L ≤ (muTab μ).getD g 0)) with
  | some g => g
  | none => muG μ + 1

/-- the closure tables `rho μ L`, `μ ≤ 2`, `L < 722`, computed by the DP with mark splitting;
`rhoMuTab[μ][L]` -/
def rhoMuTab : Array (Array ℕ) := Id.run do
  let mut t : Array (Array ℕ) := #[Array.replicate 722 0, Array.replicate 722 0, Array.replicate 722 0]
  for L in [1:722] do
    -- compute for μ = 2, 1, 0 (so that monotonicity in μ can be folded in)
    for μr in [0:3] do
      let μ := 2 - μr
      let mut best := rhoBaseMu μ L
      -- monotone in μ: a bound for more marks is a bound for fewer
      if μ < 2 then best := max best ((t[μ + 1]!)[L]!)
      for k in [1:L] do
        -- min over μ1 + μ2 = μ
        let mut m := 100000
        for μ1 in [0:μ+1] do
          m := min m ((t[μ1]!)[k]! + (t[μ - μ1]!)[L - k]!)
        best := max best m
      t := t.set! μ ((t[μ]!).set! L best)
  return t

def rhoMu (μ L : ℕ) : ℕ := (rhoMuTab.getD μ #[]).getD L 0

/-- Each entry is justified by the base bound, by monotonicity in `μ`, or by a split. -/
def rhoMuJustified : Bool :=
  (List.range 3).all fun μ => (List.range 722).all fun L =>
    decide (rhoMu μ L ≤ rhoBaseMu μ L) ||
    (decide (μ < 2) && decide (rhoMu μ L ≤ rhoMu (μ + 1) L)) ||
    (List.range L).any fun k => decide (1 ≤ k) &&
      (List.range (μ + 1)).all fun μ1 => decide (rhoMu μ L ≤ rhoMu μ1 k + rhoMu (μ - μ1) (L - k))

theorem rhoMuJustified_true : rhoMuJustified = true := by native_decide

theorem rhoMu_justified (μ : ℕ) (hμ : μ ≤ 2) (L : ℕ) (hL : L < 722) :
    rhoMu μ L ≤ rhoBaseMu μ L ∨
    (μ < 2 ∧ rhoMu μ L ≤ rhoMu (μ + 1) L) ∨
    ∃ k, 1 ≤ k ∧ k < L ∧ ∀ μ1 ≤ μ, rhoMu μ L ≤ rhoMu μ1 k + rhoMu (μ - μ1) (L - k) := by
  have h := rhoMuJustified_true
  unfold rhoMuJustified at h
  simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, decide_eq_true_eq,
    Bool.and_eq_true, List.any_eq_true] at h
  rcases h μ (by omega) L hL with (h1 | ⟨h2, h3⟩) | ⟨k, hk, hk1, hall⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl ⟨h2, h3⟩)
  · exact Or.inr (Or.inr ⟨k, hk1, hk, fun μ1 hμ1 => hall μ1 (by omega)⟩)

theorem rhoBaseMu_le : ∀ μ ≤ 2, ∀ L < 722, rhoBaseMu μ L ≤ muG μ + 1 := by native_decide

theorem rhoBaseMu_le_of_tab : ∀ μ ≤ 2, ∀ c ≤ 56, c ≤ muG μ → ∀ L ≤ 100,
    L ≤ (muTab μ).getD c 0 → rhoBaseMu μ L ≤ c := by
  native_decide

theorem muTab_le_100 : ∀ μ ≤ 2, ∀ c ≤ 56, (muTab μ).getD c 0 ≤ 100 := by native_decide

/-- `capMu μ u` = the largest `L ≤ 720` with `rhoMu μ L ≤ u`. -/
def capMu (μ u : ℕ) : ℕ :=
  ((List.range 721).filter fun L => decide (rhoMu μ L ≤ u)).foldl max 0

theorem markCount_append (xs ys : List MarkedRow) :
    markCount (xs ++ ys) = markCount xs + markCount ys := by
  unfold markCount; rw [List.countP_append]

/-! ## Validity -/

section
variable (h0 : ∀ g ≤ 56, CapValidMuAt 0 capTab0 g)
  (h1 : ∀ g ≤ 54, CapValidMuAt 1 capTab1 g)
  (h2 : ∀ g ≤ 46, CapValidMuAt 2 capTab2 g)
include h0 h1 h2

theorem muTab_valid (μ : ℕ) (hμ : μ ≤ 2) (g : ℕ) (hg : g ≤ muG μ) : CapValidMuAt μ (muTab μ) g := by
  interval_cases μ
  · exact h0 g hg
  · exact h1 g hg
  · exact h2 g hg

theorem rhoBaseMu_le_chargeSum (μ : ℕ) (hμ : μ ≤ 2) (rows : List MarkedRow) (h : ModelTrail rows)
    (hm : markCount rows ≤ μ) : rhoBaseMu μ rows.length ≤ chargeSum rows := by
  have hL : rows.length < 722 := by have := modelTrail_length_le_720 rows h; omega
  by_cases hc : chargeSum rows ≤ muG μ
  · have hG : muG μ ≤ 56 := by interval_cases μ <;> decide
    have hlen := muTab_valid h0 h1 h2 μ hμ (chargeSum rows) hc rows h hm le_rfl
    have h100 := muTab_le_100 μ hμ (chargeSum rows) (by omega)
    exact rhoBaseMu_le_of_tab μ hμ (chargeSum rows) (by omega) hc rows.length (by omega) hlen
  · have := rhoBaseMu_le μ hμ rows.length hL
    omega

/-- Superadditivity with mark splitting: every model trail with at most `μ ≤ 2`
marked rows and `L` rows has charge at least `rhoMu μ L`. -/
theorem rhoMu_le_chargeSum : ∀ (L μ : ℕ), μ ≤ 2 → ∀ (rows : List MarkedRow), rows.length = L →
    ModelTrail rows → markCount rows ≤ μ → rhoMu μ L ≤ chargeSum rows := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
      intro μ
      -- inner downward induction on μ for the monotonicity case: handle μ = 2, 1, 0 via a measure
      induction hk : (2 - μ) generalizing μ with
      | zero =>
          intro hμ rows hlen hmodel hm
          have hμ2 : μ = 2 := by omega
          subst hμ2
          have hL : L < 722 := by have := modelTrail_length_le_720 rows hmodel; omega
          rcases rhoMu_justified 2 le_rfl L hL with hbase | ⟨hlt, _⟩ | ⟨k, hk1, hkL, hsplit⟩
          · exact le_trans hbase (hlen ▸ rhoBaseMu_le_chargeSum h0 h1 h2 2 le_rfl rows hmodel hm)
          · omega
          · have hm1 : markCount (rows.take k) ≤ 2 := le_trans (markCount_take_le rows k) hm
            have hsp := hsplit (markCount (rows.take k)) hm1
            have e1 := ih k hkL (markCount (rows.take k)) hm1 (rows.take k) (by rw [List.length_take]; omega)
              (modelTrail_take rows hmodel k) le_rfl
            have hsum : markCount (rows.take k) + markCount (rows.drop k) = markCount rows := by
              rw [← markCount_append, List.take_append_drop]
            have e2 := ih (L - k) (by omega) (2 - markCount (rows.take k)) (by omega) (rows.drop k)
              (by simp [hlen]) (modelTrail_drop rows hmodel k) (by omega)
            have hcs : chargeSum (rows.take k) + chargeSum (rows.drop k) = chargeSum rows := by
              rw [← chargeSum_append, List.take_append_drop]
            omega
      | succ n ihμ =>
          intro hμ rows hlen hmodel hm
          have hL : L < 722 := by have := modelTrail_length_le_720 rows hmodel; omega
          rcases rhoMu_justified μ hμ L hL with hbase | ⟨hlt, hmono⟩ | ⟨k, hk1, hkL, hsplit⟩
          · exact le_trans hbase (hlen ▸ rhoBaseMu_le_chargeSum h0 h1 h2 μ hμ rows hmodel hm)
          · have := ihμ (μ + 1) (by omega) (by omega) rows hlen hmodel (by omega)
            omega
          · have hm1 : markCount (rows.take k) ≤ μ := le_trans (markCount_take_le rows k) hm
            have hsp := hsplit (markCount (rows.take k)) hm1
            have e1 := ih k hkL (markCount (rows.take k)) (by omega) (rows.take k) (by rw [List.length_take]; omega)
              (modelTrail_take rows hmodel k) le_rfl
            have hsum : markCount (rows.take k) + markCount (rows.drop k) = markCount rows := by
              rw [← markCount_append, List.take_append_drop]
            have e2 := ih (L - k) (by omega) (μ - markCount (rows.take k)) (by omega) (rows.drop k)
              (by simp [hlen]) (modelTrail_drop rows hmodel k) (by omega)
            have hcs : chargeSum (rows.take k) + chargeSum (rows.drop k) = chargeSum rows := by
              rw [← chargeSum_append, List.take_append_drop]
            omega

/-! ## The extended caps -/

theorem modelTrail_length_le_capMu (μ : ℕ) (hμ : μ ≤ 2) (rows : List MarkedRow) (h : ModelTrail rows)
    (hm : markCount rows ≤ μ) (u : ℕ) (hu : chargeSum rows ≤ u) : rows.length ≤ capMu μ u := by
  have hrho := rhoMu_le_chargeSum h0 h1 h2 rows.length μ hμ rows rfl h hm
  have hlen := modelTrail_length_le_720 rows h
  apply le_foldl_max_of_mem
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨by omega, by omega⟩

end

end Superperm7
