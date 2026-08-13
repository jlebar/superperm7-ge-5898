/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.Templates
import Superperm7.ElimD13
/-!
# The nine equality cells

In the cells `(m,a,r) = (10,0,0), (11,0,0), (12,0,0)` (with `b + η = 13 − m`)
the convolution bound is attained: `130 = 31+31+34+34`, `131 = 31+34+66 =
31+50+50 = 34+34+63`, `132 = 66+66`.  Any coarsened certificate must then
consist of trails of exactly optimal length at charges `(14,14,16,16)`,
`(14,16,36) / (14,26,26) / (16,16,34)`, `(36,36)`; each trail, normalized, is
one of the enumerated `templates`; and an exhaustive check over relabellings
shows that no such family of templates is pairwise visibly class-disjoint.
-/

namespace Superperm7

open Mirror

/-! ## Computable cross-disjointness test on concrete rows -/

/-- do two concrete marked rows share a visible rotation class? (by class ids) -/
def sharesClass (x y : MarkedRow) : Bool :=
  (visibleIdList x).any fun c => (visibleIdList y).any fun d => c == d

/-- some row of `s` shares a visible class with some row of `t` -/
def clash (s t : List MarkedRow) : Bool :=
  s.any fun x => t.any fun y => sharesClass x y

theorem not_markedDisjoint_of_sharesClass {x y : MarkedRow} (h : sharesClass x y = true) :
    ¬ MarkedDisjoint x y := by
  intro hd
  unfold sharesClass at h
  simp only [List.any_eq_true, beq_iff_eq] at h
  obtain ⟨c, hc, d, hd', rfl⟩ := h
  exact List.disjoint_left.mp (visibleIdList_disjoint_of hd.2) hc hd'

/-- If `clash s t`, the rows of `s` and `t` are not all pairwise disjoint. -/
theorem not_cross_of_clash {s t : List MarkedRow} (h : clash s t = true) :
    ¬ (∀ x ∈ s, ∀ y ∈ t, MarkedDisjoint x y) := by
  intro hall
  unfold clash at h
  simp only [List.any_eq_true] at h
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  exact not_markedDisjoint_of_sharesClass hxy (hall x hx y hy)

def relabelTrail (ρ : Perm7) (t : List MarkedRow) : List MarkedRow := t.map (relabelMarkedRow ρ)

/-! ## The join checks (with cached class-id lists) -/

/-- all visible class ids of a trail -/
def trailIds (t : List MarkedRow) : List Nat := t.flatMap visibleIdList

/-- id-level clash: the two id lists intersect -/
def idsClash (a b : List Nat) : Bool := a.any fun c => b.any fun d => c == d

theorem idsClash_iff (a b : List Nat) : idsClash a b = true ↔ ∃ c, c ∈ a ∧ c ∈ b := by
  unfold idsClash
  simp only [List.any_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨c, hc, d, hd, rfl⟩; exact ⟨c, hc, hd⟩
  · rintro ⟨c, hc, hd⟩; exact ⟨c, hc, c, hd, rfl⟩

theorem clash_iff (s t : List MarkedRow) :
    clash s t = true ↔ ∃ x ∈ s, ∃ y ∈ t, ∃ c, c ∈ visibleIdList x ∧ c ∈ visibleIdList y := by
  unfold clash sharesClass
  simp only [List.any_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨x, hx, y, hy, c, hc, d, hd, rfl⟩; exact ⟨x, hx, y, hy, c, hc, hd⟩
  · rintro ⟨x, hx, y, hy, c, hc, hd⟩; exact ⟨x, hx, y, hy, c, hc, c, hd, rfl⟩

theorem clash_eq_idsClash (s t : List MarkedRow) : clash s t = idsClash (trailIds s) (trailIds t) := by
  apply Bool.eq_iff_iff.mpr
  rw [clash_iff, idsClash_iff]
  unfold trailIds
  simp only [List.mem_flatMap]
  constructor
  · rintro ⟨x, hx, y, hy, c, hc, hd⟩; exact ⟨c, ⟨x, hx, hc⟩, ⟨y, hy, hd⟩⟩
  · rintro ⟨c, ⟨x, hx, hc⟩, ⟨y, hy, hd⟩⟩; exact ⟨x, hx, y, hy, c, hc, hd⟩

/-- the visible position words of a trail -/
def visWords (t : List MarkedRow) : List W :=
  t.flatMap fun x => ((List.range x.row.length).filter (fun i => ∀ j ∈ x.omitted, j.val ≠ i)).map
    fun i => permWord ((F^[i]) x.row.start)

theorem trailIds_eq_visWords (t : List MarkedRow) : trailIds t = (visWords t).map classId := by
  unfold trailIds visWords visibleIdList
  rw [List.map_flatMap]
  congr 1
  funext x
  rw [List.map_map]
  rfl

/-- apply a relabelling given as a word (`r[a] = ρ a`) to a word -/
def applyW (r : W) (w : W) : W := w.map fun a => r.getD a.val a

/-- ids of `ρ·B` computed at word level from `visWords B` and `r = permWord ρ` -/
def relabelIds (r : W) (ws : List W) : List Nat := ws.map fun w => classId (applyW r w)

theorem applyW_permWord (ρ : Perm7) (w : W) : applyW (permWord ρ) w = w.map ρ := by
  unfold applyW
  apply List.map_congr_left
  intro a _
  rw [List.getD_eq_getElem?_getD, permWord_getElem? ρ a.val a.isLt]
  simp

theorem visWords_relabel (ρ : Perm7) (t : List MarkedRow) :
    visWords (relabelTrail ρ t) = (visWords t).map (fun w => w.map ρ) := by
  unfold visWords relabelTrail
  rw [List.flatMap_map, List.map_flatMap]
  congr 1
  funext x
  rw [List.map_map]
  simp only [relabelMarkedRow_row, relabelRow_length, relabelMarkedRow_omitted]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, relabelRow]
  rw [← relabelPerm_F_iterate, permWord_relabel]

theorem trailIds_relabel (ρ : Perm7) (B : List MarkedRow) :
    trailIds (relabelTrail ρ B) = relabelIds (permWord ρ) (visWords B) := by
  rw [trailIds_eq_visWords, visWords_relabel, List.map_map]
  unfold relabelIds
  apply List.map_congr_left
  intro w _
  simp only [Function.comp_apply]
  rw [applyW_permWord]

/-- relabelling words (all 5040) under which `ρ·B` does not clash with any placed id list;
returns the id lists of the placed `ρ·B` -/
def compatibleRelabels (fixed : List (List Nat)) (Bws : List W) : List (List Nat) :=
  allWords.filterMap fun r =>
    let ids := relabelIds r Bws
    if fixed.all fun A => !(idsClash A ids) then some ids else none

/-- template data for the join: visible words per template (cached per charge) -/
def templateWordsOf (g : ℕ) : List (List W) := (templates g).map visWords
def tw14 : List (List W) := templateWordsOf 14
def tw16 : List (List W) := templateWordsOf 16
def tw26 : List (List W) := templateWordsOf 26
def tw34 : List (List W) := templateWordsOf 34
def tw36 : List (List W) := templateWordsOf 36
def templateWords (g : ℕ) : List (List W) :=
  if g = 14 then tw14 else if g = 16 then tw16 else if g = 26 then tw26 else if g = 34 then tw34
  else if g = 36 then tw36 else templateWordsOf g

theorem templateWords_eq (g : ℕ) : templateWords g = (templates g).map visWords := by
  unfold templateWords tw14 tw16 tw26 tw34 tw36 templateWordsOf
  split_ifs <;> subst_vars <;> rfl

/-- Is there a way to place templates of charges `gs` (relabelled arbitrarily) pairwise
non-clashing with each other and with `fixed`?  Nested search with pruning. -/
def placeable (fixed : List (List Nat)) : List ℕ → Bool
  | [] => true
  | g :: gs => (templateWords g).any fun Bws =>
      (compatibleRelabels fixed Bws).any fun ids => placeable (ids :: fixed) gs

/-- The join check for a charge multiset `g₁ :: gs`: the first trail is a template as is
(normalized), the others are relabelled templates. -/
def joinImpossible (g1 : ℕ) (gs : List ℕ) : Bool :=
  (templateWords g1).all fun Aws => !(placeable [Aws.map classId] gs)

-- (the finite join checks are evaluated in `EqualityChecks.lean`)

/-! ## Soundness of the join -/

theorem permWord_mem_allWords : ∀ ρ : Perm7, permWord ρ ∈ allWords := by native_decide

theorem relabelTrail_comp (ρ σ : Perm7) (t : List MarkedRow) :
    relabelTrail ρ (relabelTrail σ t) = relabelTrail (σ.trans ρ) t := by
  unfold relabelTrail
  rw [List.map_map]
  apply List.map_congr_left
  intro x _
  rcases x with ⟨⟨p, L⟩, s⟩
  simp only [Function.comp_apply, relabelMarkedRow, relabelRow]
  congr 1

theorem relabelTrail_one (t : List MarkedRow) : relabelTrail 1 t = t := by
  unfold relabelTrail
  conv_rhs => rw [← List.map_id t]
  apply List.map_congr_left
  intro x _
  rcases x with ⟨⟨p, L⟩, s⟩
  simp only [relabelMarkedRow, relabelRow, id]
  congr 1

/-- cross-disjointness is invariant under a common relabelling -/
theorem cross_relabel_iff (ρ : Perm7) (s t : List MarkedRow) :
    (∀ x ∈ relabelTrail ρ s, ∀ y ∈ relabelTrail ρ t, MarkedDisjoint x y) ↔
    (∀ x ∈ s, ∀ y ∈ t, MarkedDisjoint x y) := by
  unfold relabelTrail
  constructor
  · intro h x hx y hy
    exact (MarkedDisjoint_relabel_iff ρ x y).mp
      (h _ (List.mem_map_of_mem hx) _ (List.mem_map_of_mem hy))
  · intro h x hx y hy
    obtain ⟨x0, hx0, rfl⟩ := List.mem_map.mp hx
    obtain ⟨y0, hy0, rfl⟩ := List.mem_map.mp hy
    exact (MarkedDisjoint_relabel_iff ρ x0 y0).mpr (h x0 hx0 y0 hy0)

/-- A family of trails, pairwise cross-disjoint. -/
def CrossDisjointFamily (ts : List (List MarkedRow)) : Prop :=
  ts.Pairwise fun s t => ∀ x ∈ s, ∀ y ∈ t, MarkedDisjoint x y

theorem markedDisjoint_symm {x y : MarkedRow} (h : MarkedDisjoint x y) : MarkedDisjoint y x :=
  ⟨fun e => h.1 e.symm, h.2.symm⟩

theorem cross_symm {s t : List MarkedRow} (h : ∀ x ∈ s, ∀ y ∈ t, MarkedDisjoint x y) :
    ∀ y ∈ t, ∀ x ∈ s, MarkedDisjoint y x :=
  fun y hy x hx => markedDisjoint_symm (h x hx y hy)

theorem crossDisjointFamily_relabel (ρ : Perm7) (ts : List (List MarkedRow))
    (h : CrossDisjointFamily ts) : CrossDisjointFamily (ts.map (relabelTrail ρ)) := by
  unfold CrossDisjointFamily at *
  rw [List.pairwise_map]
  exact h.imp fun {s t} hst => (cross_relabel_iff ρ s t).mpr hst

section
variable (h0 : ∀ g ≤ 56, CapValidMuAt 0 capTab0 g)
  (h1 : ∀ g ≤ 54, CapValidMuAt 1 capTab1 g)
  (h2 : ∀ g ≤ 46, CapValidMuAt 2 capTab2 g)
include h0 h1 h2

/-- A trail "of type `g`": model, ≤ 3 marks, charge ≤ g, exactly `optLen g` rows. -/
def OfType (g : ℕ) (t : List MarkedRow) : Prop :=
  ModelTrail t ∧ markCount t ≤ 3 ∧ chargeSum t ≤ g ∧ t.length = optLen g

omit h0 h1 h2 in
theorem ofType_relabel (ρ : Perm7) {g : ℕ} {t : List MarkedRow} (h : OfType g t) :
    OfType g (relabelTrail ρ t) := by
  refine ⟨modelTrail_map_relabel ρ t h.1, ?_, ?_, ?_⟩
  · have : markCount (relabelTrail ρ t) = markCount t := by
      unfold markCount relabelTrail; rw [List.countP_map]; rfl
    rw [this]; exact h.2.1
  · unfold relabelTrail; rw [chargeSum_map_relabel]; exact h.2.2.1
  · unfold relabelTrail; rw [List.length_map]; exact h.2.2.2

omit h0 h1 h2 in
theorem forall₂_ofType_map (ρ : Perm7) {gs : List ℕ} {ts : List (List MarkedRow)}
    (h : List.Forall₂ OfType gs ts) : List.Forall₂ OfType gs (ts.map (relabelTrail ρ)) := by
  induction h with
  | nil => exact List.Forall₂.nil
  | cons h _ ih => exact List.Forall₂.cons (ofType_relabel ρ h) ih

/-- Every trail of type `g` is a relabelled template. -/
theorem exists_template (g : ℕ) (hg : 0 < optLen g) (t : List MarkedRow) (ht : OfType g t) :
    ∃ B ∈ templates g, ∃ ρ : Perm7, t = relabelTrail ρ B := by
  cases hne : t with
  | nil => rw [hne] at ht; have := ht.2.2.2; simp at this; omega
  | cons x xs =>
      let σ := x.row.start.symm
      have hnorm : OfType g (relabelTrail σ t) := ofType_relabel σ ht
      have hfirst : ∀ y, (relabelTrail σ t).head? = some y → y.row.start = 1 := by
        intro y hy
        rw [hne] at hy
        simp only [relabelTrail, List.map_cons, List.head?_cons, Option.some.injEq] at hy
        rw [← hy]
        exact relabelPerm_self_symm x.row.start
      have hmem := mem_templates h0 h1 h2 g hg (relabelTrail σ t) hnorm.1 hnorm.2.1 hfirst hnorm.2.2.1 hnorm.2.2.2
      refine ⟨relabelTrail σ t, hmem, x.row.start, ?_⟩
      rw [relabelTrail_comp, ← hne]
      have : (σ.trans x.row.start) = 1 := by ext i; simp [σ]
      rw [this, relabelTrail_one]

/-- Soundness of `placeable`: a cross-disjoint family `placed ++ ts` with `ts` of types `gs`
makes `placeable (placed.map trailIds) gs` true. -/
theorem placeable_of_family : ∀ (gs : List ℕ) (placed ts : List (List MarkedRow)),
    (∀ g ∈ gs, 0 < optLen g) →
    List.Forall₂ OfType gs ts →
    CrossDisjointFamily (placed ++ ts) →
    placeable (placed.map trailIds) gs = true := by
  intro gs
  induction gs with
  | nil => intro placed ts _ hts _; cases hts; rfl
  | cons g gs ih =>
      intro placed ts hpos hts hfam
      cases hts with
      | cons ht hrest =>
          rename_i t ts'
          obtain ⟨B, hB, ρ, rfl⟩ := exists_template h0 h1 h2 g (hpos g (by simp)) _ ht
          unfold placeable
          rw [List.any_eq_true]
          refine ⟨visWords B, by rw [templateWords_eq]; exact List.mem_map_of_mem hB, ?_⟩
          rw [List.any_eq_true]
          refine ⟨trailIds (relabelTrail ρ B), ?_, ?_⟩
          · unfold compatibleRelabels
            rw [List.mem_filterMap]
            refine ⟨permWord ρ, permWord_mem_allWords ρ, ?_⟩
            rw [← trailIds_relabel]
            have hall : (placed.map trailIds).all (fun A => !(idsClash A (trailIds (relabelTrail ρ B)))) = true := by
              rw [List.all_eq_true]
              intro A hA
              obtain ⟨P, hP, rfl⟩ := List.mem_map.mp hA
              have hcross : ∀ x ∈ P, ∀ y ∈ relabelTrail ρ B, MarkedDisjoint x y := by
                unfold CrossDisjointFamily at hfam
                exact (List.pairwise_append.mp hfam).2.2 P hP _ (by simp)
              rw [← clash_eq_idsClash]
              cases hc : clash P (relabelTrail ρ B) with
              | false => rfl
              | true => exact absurd hcross (not_cross_of_clash hc)
            simp [hall]
          · have := ih (relabelTrail ρ B :: placed) ts' (fun g' hg' => hpos g' (by simp [hg'])) hrest
            simp only [List.map_cons] at this
            apply this
            unfold CrossDisjointFamily at hfam ⊢
            have hperm : (placed ++ relabelTrail ρ B :: ts').Perm ((relabelTrail ρ B :: placed) ++ ts') := by
              simp only [List.cons_append]
              exact List.perm_middle
            exact hfam.perm hperm (fun hst => cross_symm hst)

/-- Soundness of `joinImpossible`. -/
theorem no_family_of_joinImpossible (g1 : ℕ) (gs : List ℕ) (hj : joinImpossible g1 gs = true)
    (hpos1 : 0 < optLen g1) (hpos : ∀ g ∈ gs, 0 < optLen g)
    (t : List MarkedRow) (ts : List (List MarkedRow))
    (ht : OfType g1 t) (hts : List.Forall₂ OfType gs ts) (hfam : CrossDisjointFamily (t :: ts)) : False := by
  -- normalize by the first trail's relabelling
  obtain ⟨A, hA, ρ, rfl⟩ := exists_template h0 h1 h2 g1 hpos1 t ht
  let σ := ρ.symm
  have hfam' : CrossDisjointFamily ((relabelTrail ρ A :: ts).map (relabelTrail σ)) :=
    crossDisjointFamily_relabel σ _ hfam
  simp only [List.map_cons, relabelTrail_comp] at hfam'
  have hρσ : ρ.trans σ = 1 := by ext i; simp [σ]
  rw [hρσ, relabelTrail_one] at hfam'
  have hts' : List.Forall₂ OfType gs (ts.map (relabelTrail σ)) := forall₂_ofType_map σ hts
  have hpl := placeable_of_family h0 h1 h2 gs [A] (ts.map (relabelTrail σ)) hpos hts' (by simpa using hfam')
  simp only [List.map_cons, List.map_nil, trailIds_eq_visWords] at hpl
  unfold joinImpossible at hj
  rw [List.all_eq_true] at hj
  have := hj (visWords A) (by rw [templateWords_eq]; exact List.mem_map_of_mem hA)
  rw [hpl] at this
  simp at this

end

end Superperm7
