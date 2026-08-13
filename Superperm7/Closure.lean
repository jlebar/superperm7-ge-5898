/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CapTable

/-!
# Superadditive closure of the capacity table

Cutting a model trail into a prefix and a suffix gives two model trails whose
charges add.  Hence the least charge `ρ(L)` needed for `L` rows is
superadditive in `L`, and the certified table `capTab` (charges `≤ 36`)
propagates to a valid row cap `capW u` for every charge budget `u`.

Everything here is elementary: the closure table `rhoTab` is computed once and
its defining inequalities are checked by `decide`; validity is a strong
induction on the length of the trail.
-/

namespace Superperm7

/-! ## A priori length bound -/

theorem visibleMask_subset_allRClasses (x : MarkedRow) : x.visibleMask ⊆ allRClasses := by
  intro C hC
  rcases Finset.mem_image.mp hC with ⟨i, _, rfl⟩
  exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩

theorem visibleMask_nonempty (x : MarkedRow) (hx : Admissible x) : x.visibleMask.Nonempty := by
  refine ⟨rClass ((F^[0]) x.row.start), Finset.mem_image.mpr ⟨0, ?_, rfl⟩⟩
  refine Finset.mem_filter.mpr ⟨?_, ?_⟩
  · simp [Row.length]
  · intro j hj hj0
    have := hx j hj
    omega

def visibleUnion : List MarkedRow → Finset (Finset Perm7)
  | [] => ∅
  | x :: xs => x.visibleMask ∪ visibleUnion xs

theorem mem_visibleUnion {C : Finset Perm7} {xs : List MarkedRow} :
    C ∈ visibleUnion xs ↔ ∃ x ∈ xs, C ∈ x.visibleMask := by
  induction xs with
  | nil => simp [visibleUnion]
  | cons x xs ih => simp [visibleUnion, ih]

theorem visibleUnion_subset (xs : List MarkedRow) : visibleUnion xs ⊆ allRClasses := by
  intro C hC
  rcases mem_visibleUnion.mp hC with ⟨x, _, hx⟩
  exact visibleMask_subset_allRClasses x hx

theorem length_le_card_visibleUnion (xs : List MarkedRow) (hadm : ∀ x ∈ xs, Admissible x)
    (hpair : xs.Pairwise MarkedDisjoint) : xs.length ≤ (visibleUnion xs).card := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.pairwise_cons] at hpair
      have hdisj : Disjoint x.visibleMask (visibleUnion xs) := by
        rw [Finset.disjoint_left]
        intro C hCx hCu
        rcases mem_visibleUnion.mp hCu with ⟨y, hy, hCy⟩
        exact Finset.disjoint_left.mp (hpair.1 y hy).2 hCx hCy
      simp only [visibleUnion, List.length_cons]
      rw [Finset.card_union_of_disjoint hdisj]
      have h1 := (visibleMask_nonempty x (hadm x (by simp))).card_pos
      have h2 := ih (fun y hy => hadm y (by simp [hy])) hpair.2
      omega

/-- A model trail has at most 720 rows (its visible class masks are nonempty,
pairwise disjoint, and drawn from the 720 rotation classes). -/
theorem modelTrail_length_le_720 (rows : List MarkedRow) (h : ModelTrail rows) :
    rows.length ≤ 720 := by
  have := length_le_card_visibleUnion rows h.1 h.2.2
  have hcard := Finset.card_le_card (visibleUnion_subset rows)
  rw [number_of_rClasses] at hcard
  omega

/-! ## The closure table -/

/-- least certified charge for `L` rows: the least `g ≤ 36` with `capTab[g] ≥ L`,
or `37` if none. -/
def rhoBase (L : ℕ) : ℕ :=
  match (List.range 37).find? (fun g => decide (L ≤ capTab.getD g 0)) with
  | some g => g
  | none => 37

/-- superadditive closure, tabulated for `L < 722` -/
def rhoTab : Array ℕ := Id.run do
  let mut t : Array ℕ := Array.replicate 722 0
  for L in [1:722] do
    let mut best := rhoBase L
    for k in [1:L] do
      best := max best (t[k]! + t[L - k]!)
    t := t.set! L best
  return t

def rho (L : ℕ) : ℕ := rhoTab.getD L 0

/-- The two facts about the table that the validity proof consumes:
each entry is justified by the base bound or by a split. -/
theorem rho_justified : ∀ L < 722,
    rho L ≤ rhoBase L ∨ ∃ k < L, 1 ≤ k ∧ rho L ≤ rho k + rho (L - k) := by
  native_decide

theorem rhoBase_le_37 : ∀ L < 722, rhoBase L ≤ 37 := by native_decide

theorem rhoBase_le_of_capTab : ∀ c ≤ 36, ∀ L ≤ 66, L ≤ capTab.getD c 0 → rhoBase L ≤ c := by
  native_decide

theorem capTab_le_66 : ∀ c ≤ 36, capTab.getD c 0 ≤ 66 := by native_decide

theorem rho_zero : rho 0 = 0 := by native_decide

/-! ## Validity -/

theorem chargeSum_append (xs ys : List MarkedRow) :
    chargeSum (xs ++ ys) = chargeSum xs + chargeSum ys := by
  simp [chargeSum, List.sum_append]

theorem modelTrail_drop (rows : List MarkedRow) (h : ModelTrail rows) (n : ℕ) :
    ModelTrail (rows.drop n) :=
  ⟨fun y hy => h.1 y (List.mem_of_mem_drop hy),
   h.2.1.suffix (List.drop_suffix n rows),
   h.2.2.sublist (List.drop_sublist n rows)⟩

theorem rhoBase_le_chargeSum (rows : List MarkedRow) (h : ModelTrail rows) :
    rhoBase rows.length ≤ chargeSum rows := by
  have hL : rows.length < 722 := by have := modelTrail_length_le_720 rows h; omega
  by_cases hc : chargeSum rows ≤ 36
  · have hlen := modelTrail_length_le_capTab (chargeSum rows) hc rows h le_rfl
    have h66 := capTab_le_66 (chargeSum rows) hc
    exact rhoBase_le_of_capTab (chargeSum rows) hc rows.length (by omega) hlen
  · have := rhoBase_le_37 rows.length hL
    omega

/-- Superadditivity: every model trail of `L` rows has charge at least `rho L`. -/
theorem rho_le_chargeSum : ∀ (rows : List MarkedRow), ModelTrail rows →
    rho rows.length ≤ chargeSum rows := by
  suffices h : ∀ L, ∀ rows : List MarkedRow, rows.length = L → ModelTrail rows →
      rho L ≤ chargeSum rows by
    intro rows hm; exact h _ rows rfl hm
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
      intro rows hlen hmodel
      have hL : L < 722 := by have := modelTrail_length_le_720 rows hmodel; omega
      rcases rho_justified L hL with hbase | ⟨k, hkL, hk1, hsplit⟩
      · exact le_trans hbase (hlen ▸ rhoBase_le_chargeSum rows hmodel)
      · have h1 := ih k hkL (rows.take k) (by simp [hlen]; omega) (modelTrail_take rows hmodel k)
        have h2 := ih (L - k) (by omega) (rows.drop k) (by simp [hlen]) (modelTrail_drop rows hmodel k)
        have hsum : chargeSum (rows.take k) + chargeSum (rows.drop k) = chargeSum rows := by
          rw [← chargeSum_append, List.take_append_drop]
        omega

/-! ## The extended cap -/

/-- `capW u` = the largest `L ≤ 720` with `rho L ≤ u`. -/
def capW (u : ℕ) : ℕ :=
  ((List.range 721).filter fun L => decide (rho L ≤ u)).foldl max 0

theorem le_foldl_max_of_mem {l : List ℕ} {a : ℕ} (h : a ∈ l) (init : ℕ) :
    a ≤ l.foldl max init := by
  induction l generalizing init with
  | nil => simp at h
  | cons b t ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp h with rfl | h
      · have : ∀ (t : List ℕ) (i : ℕ), i ≤ t.foldl max i := by
          intro t; induction t with
          | nil => simp
          | cons c t ih' => intro i; simp only [List.foldl_cons]; exact le_trans (le_max_left _ _) (ih' _)
        exact le_trans (le_max_right _ _) (this t _)
      · exact ih h _

/-- Every model marked trail of charge `≤ u` has at most `capW u` rows. -/
theorem modelTrail_length_le_capW (rows : List MarkedRow) (h : ModelTrail rows) (u : ℕ)
    (hu : chargeSum rows ≤ u) : rows.length ≤ capW u := by
  have hrho := rho_le_chargeSum rows h
  have hlen := modelTrail_length_le_720 rows h
  apply le_foldl_max_of_mem
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨by omega, by omega⟩

theorem capW_mono {u v : ℕ} (huv : u ≤ v) : capW u ≤ capW v := by
  -- capW u is attained by some L in the filter for u, which is also in the filter for v
  unfold capW
  have : ∀ (l : List ℕ) (init : ℕ), (l.filter fun L => decide (rho L ≤ u)).foldl max init ≤
      (l.filter fun L => decide (rho L ≤ v)).foldl max init := by
    intro l
    induction l with
    | nil => simp
    | cons a t ih =>
        intro init
        by_cases ha : rho a ≤ u
        · have hb : rho a ≤ v := le_trans ha huv
          simp only [List.filter_cons, ha, hb, decide_true, List.foldl_cons]
          exact ih _
        · simp only [List.filter_cons, ha, decide_false]
          by_cases hb : rho a ≤ v
          · simp only [hb, decide_true, List.foldl_cons]
            refine le_trans (ih init) ?_
            -- foldl max is monotone in init
            have mono : ∀ (s : List ℕ) (i j : ℕ), i ≤ j → s.foldl max i ≤ s.foldl max j := by
              intro s; induction s with
              | nil => intro i j hij; simpa
              | cons c s ih' => intro i j hij; simp only [List.foldl_cons]; exact ih' _ _ (max_le_max hij le_rfl)
            exact mono _ _ _ (le_max_left _ _)
          · simp only [hb, decide_false]
            exact ih _
  exact this _ 0

end Superperm7
