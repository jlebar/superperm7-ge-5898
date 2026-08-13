/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.Search
import Superperm7.RowModel

/-!
# Completeness of the reflected capacity search

`search caps g target marks fuel = false` refutes every model marked trail of
charge `≤ g` and length `≥ target` (with first start normalized to `1`, then
for arbitrary first start by relabelling), provided `caps[g']` is a valid
length cap for model trails of charge `≤ g'` for every `g' < g`.
-/

namespace Superperm7

open Mirror

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false

/-! ## Model trails -/

/-- Admissible marked rows: omissions strictly interior. -/
def Admissible (x : MarkedRow) : Prop := x.OmissionsInterior

instance (x : MarkedRow) : Decidable (Admissible x) := by
  unfold Admissible; infer_instance

/-- A model trail: admissible rows, consecutive rows compatible, all rows
pairwise block-distinct and visibly class-disjoint. -/
def ModelTrail (rows : List MarkedRow) : Prop :=
  (∀ x ∈ rows, Admissible x) ∧ rows.IsChain MarkedCompatible ∧ rows.Pairwise MarkedDisjoint

def chargeSum (rows : List MarkedRow) : ℕ := (rows.map MarkedRow.charge).sum

@[simp] theorem chargeSum_nil : chargeSum [] = 0 := rfl
@[simp] theorem chargeSum_cons (x : MarkedRow) (xs : List MarkedRow) :
    chargeSum (x :: xs) = x.charge + chargeSum xs := by
  simp [chargeSum]

theorem modelTrail_tail {x : MarkedRow} {xs : List MarkedRow}
    (h : ModelTrail (x :: xs)) : ModelTrail xs :=
  ⟨fun y hy => h.1 y (by simp [hy]), h.2.1.tail, (List.pairwise_cons.mp h.2.2).2⟩

theorem modelTrail_take (rows : List MarkedRow) (h : ModelTrail rows) (n : ℕ) :
    ModelTrail (rows.take n) :=
  ⟨fun y hy => h.1 y (List.mem_of_mem_take hy),
   h.2.1.prefix (List.take_prefix n rows),
   h.2.2.sublist (List.take_sublist n rows)⟩

theorem chargeSum_take_le (rows : List MarkedRow) (n : ℕ) :
    chargeSum (rows.take n) ≤ chargeSum rows := by
  unfold chargeSum
  have := List.take_prefix n rows
  exact List.Sublist.sum_le_sum (by simpa using (this.sublist).map MarkedRow.charge)
    (fun _ _ => Nat.zero_le _)

/-- `caps` is a valid single-trail cap at budget `g'`. -/
def CapValidAt (caps : Array Nat) (g' : ℕ) : Prop :=
  ∀ rows : List MarkedRow, ModelTrail rows → chargeSum rows ≤ g' → rows.length ≤ caps.getD g' 0

def CapsValidBelow (caps : Array Nat) (g : ℕ) : Prop := ∀ g' < g, CapValidAt caps g'

/-! ## Bitmask lemmas -/

@[simp] theorem testBit_one' (i : Nat) :
    Nat.testBit 1 i = decide (i = 0) := by
  cases i with
  | zero => simp
  | succ i =>
      have hlt : 1 < 2 ^ (i + 1) := one_lt_pow₀ one_lt_two (by omega)
      simpa using Nat.testBit_eq_false_of_lt hlt

@[simp] theorem testBit_one_shift (x i : Nat) :
    (1 <<< x).testBit i = decide (i = x) := by
  by_cases hix : i = x
  · subst i; simp
  · by_cases hle : x ≤ i
    · have hsub : i - x ≠ 0 := by omega
      simp [hle, hsub, hix, testBit_one']
    · simp [hle, hix]

@[simp] theorem testBit_bitMask (xs : List Nat) (i : Nat) :
    (bitMask xs).testBit i = decide (i ∈ xs) := by
  induction xs with
  | nil => simp [bitMask]
  | cons x xs ih =>
      rw [bitMask, Nat.testBit_lor, testBit_one_shift, ih]
      by_cases hix : i = x
      · subst i; simp
      · by_cases him : i ∈ xs <;> simp [hix, him]

theorem bitMask_land_eq_zero_iff (xs ys : List Nat) :
    bitMask xs &&& bitMask ys = 0 ↔ List.Disjoint xs ys := by
  constructor
  · intro h
    rw [List.disjoint_left]
    intro i hix hiy
    have ht := congrArg (fun n => n.testBit i) h
    simp [Nat.testBit_land, hix, hiy] at ht
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_land, testBit_bitMask, testBit_bitMask, Nat.zero_testBit]
    rw [List.disjoint_left] at h
    by_cases hix : i ∈ xs
    · have hiy : i ∉ ys := fun hiy => h hix hiy
      simp [hix, hiy]
    · simp [hix]

theorem lor_land_right (a b c : Nat) :
    (a ||| b) &&& c = (a &&& c) ||| (b &&& c) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_land, Nat.testBit_lor]
  cases a.testBit i <;> cases b.testBit i <;> cases c.testBit i <;> decide

/-! ## Codes and ids are faithful -/

theorem wcode_eq_foldl (w : W) : wcode w = w.foldl (fun acc a => acc * 8 + a.val) 0 := rfl

private theorem foldl_code_append (w : W) (init : Nat) :
    w.foldl (fun acc (a : Fin 7) => acc * 8 + a.val) init =
      init * 8 ^ w.length + w.foldl (fun acc (a : Fin 7) => acc * 8 + a.val) 0 := by
  induction w generalizing init with
  | nil => simp
  | cons a t ih =>
      simp only [List.foldl_cons, List.length_cons, Nat.zero_mul, Nat.zero_add]
      rw [ih (init * 8 + a.val), ih a.val]
      ring

private theorem wcode_lt (w : W) : wcode w < 8 ^ w.length := by
  induction w with
  | nil => simp [wcode]
  | cons a t ih =>
      unfold wcode
      simp only [List.foldl_cons, List.length_cons, Nat.zero_mul, Nat.zero_add]
      rw [foldl_code_append]
      have ha : a.val ≤ 7 := by omega
      have := ih
      unfold wcode at this
      calc a.val * 8 ^ t.length + List.foldl (fun acc (a : Fin 7) => acc * 8 + a.val) 0 t
          < a.val * 8 ^ t.length + 8 ^ t.length := by omega
        _ = (a.val + 1) * 8 ^ t.length := by ring
        _ ≤ 8 * 8 ^ t.length := Nat.mul_le_mul_right _ (by omega)
        _ = 8 ^ (t.length + 1) := by ring

theorem wcode_injective_of_length {v w : W} (hlen : v.length = w.length)
    (h : wcode v = wcode w) : v = w := by
  induction v generalizing w with
  | nil => cases w with
    | nil => rfl
    | cons _ _ => simp at hlen
  | cons a t ih =>
      cases w with
      | nil => simp at hlen
      | cons b u =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
          unfold wcode at h
          simp only [List.foldl_cons, Nat.zero_mul, Nat.zero_add] at h
          rw [foldl_code_append t, foldl_code_append u, hlen] at h
          have ht := wcode_lt t; have hu := wcode_lt u
          unfold wcode at ht hu
          rw [hlen] at ht
          have hab : a.val = b.val := by
            have := congrArg (fun x => x / 8 ^ u.length) h
            simp only at this
            rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by positivity),
              Nat.add_comm (b.val * _), Nat.add_mul_div_right _ _ (by positivity),
              Nat.div_eq_of_lt ht, Nat.div_eq_of_lt hu] at this
            simpa using this
          have htu : List.foldl (fun acc (a : Fin 7) => acc * 8 + a.val) 0 t =
              List.foldl (fun acc (a : Fin 7) => acc * 8 + a.val) 0 u := by
            rw [hab] at h; omega
          rw [Fin.ext hab, ih hlen htu]

/-- The class code is attained by some rotation. -/
theorem classCode_attained : ∀ p : Perm7,
    (List.range 7).any (fun i => wcode (permWord ((R^[i]) p)) == classCode (permWord p))
      = true := by
  native_decide

theorem classCode_R : ∀ p : Perm7, classCode (permWord (R p)) = classCode (permWord p) := by
  native_decide

theorem classCode_R_iterate (p : Perm7) : ∀ i : ℕ,
    classCode (permWord ((R^[i]) p)) = classCode (permWord p)
  | 0 => rfl
  | i + 1 => by rw [Function.iterate_succ_apply', classCode_R, classCode_R_iterate p i]

theorem classId_faithful : ∀ p : Perm7,
    classReps[classInv[classCode (permWord p)]!]? = some (classCode (permWord p)) := by
  native_decide

theorem Mirror.mem_rClass_iff (p q : Perm7) : q ∈ rClass p ↔ ∃ i < 7, (R^[i]) p = q := by
  simp [rClass, finiteOrbit]

theorem rClass_eq_of_iterate (p : Perm7) : ∀ i : ℕ, rClass ((R^[i]) p) = rClass p := by
  suffices h : ∀ p : Perm7, rClass (R p) = rClass p by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [Function.iterate_succ_apply', h, ih]
  intro p
  ext q
  simp only [Mirror.mem_rClass_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    by_cases h6 : i < 6
    · exact ⟨i + 1, by omega, by rw [Function.iterate_succ_apply]⟩
    · refine ⟨0, by omega, ?_⟩
      have : i = 6 := by omega
      subst this
      have := R_order_seven p
      rw [show (7 : ℕ) = 6 + 1 from rfl, Function.iterate_add_apply] at this
      simpa using this.symm
  · rintro ⟨i, hi, rfl⟩
    by_cases h0 : i = 0
    · subst h0
      refine ⟨6, by omega, ?_⟩
      have := R_order_seven p
      rw [show (7 : ℕ) = 6 + 1 from rfl, Function.iterate_succ_apply] at this
      simpa using this
    · refine ⟨i - 1, by omega, ?_⟩
      rw [← Function.iterate_succ_apply, Nat.succ_eq_add_one, show i - 1 + 1 = i by omega]

theorem classCode_eq_imp_rClass_eq {p q : Perm7}
    (h : classCode (permWord p) = classCode (permWord q)) : rClass p = rClass q := by
  have hp := classCode_attained p
  have hq := classCode_attained q
  rw [List.any_eq_true] at hp hq
  obtain ⟨i, hi, hpi⟩ := hp
  obtain ⟨j, hj, hqj⟩ := hq
  simp only [beq_iff_eq] at hpi hqj
  have hcodes : wcode (permWord ((R^[i]) p)) = wcode (permWord ((R^[j]) q)) := by
    rw [hpi, hqj, h]
  have hw := wcode_injective_of_length (by simp) hcodes
  have hperm : (R^[i]) p = (R^[j]) q := permWord_injective hw
  rw [← rClass_eq_of_iterate p i, ← rClass_eq_of_iterate q j, hperm]

theorem classId_eq_imp_rClass_eq {p q : Perm7}
    (h : classId (permWord p) = classId (permWord q)) : rClass p = rClass q := by
  apply classCode_eq_imp_rClass_eq
  have hp := classId_faithful p
  have hq := classId_faithful q
  unfold classId at h
  rw [h] at hp
  rw [hp] at hq
  simpa using hq

/-- The block code is attained by some `F`-iterate. -/
theorem blockCode_attained : ∀ p : Perm7,
    (List.range 6).any (fun i => wcode (permWord ((F^[i]) p)) == blockCode (permWord p))
      = true := by
  native_decide

theorem blockCode_F : ∀ p : Perm7, blockCode (permWord (F p)) = blockCode (permWord p) := by
  native_decide

theorem blockId_faithful : ∀ p : Perm7,
    blockReps[blockInv[blockCode (permWord p)]!]? = some (blockCode (permWord p)) := by
  native_decide

theorem Mirror.mem_fBlock_iff (p q : Perm7) : q ∈ fBlock p ↔ ∃ i < 6, (F^[i]) p = q := by
  simp [fBlock, finiteOrbit]

theorem fBlock_eq_of_iterate (p : Perm7) : ∀ i : ℕ, fBlock ((F^[i]) p) = fBlock p := by
  suffices h : ∀ p : Perm7, fBlock (F p) = fBlock p by
    intro i
    induction i with
    | zero => rfl
    | succ i ih => rw [Function.iterate_succ_apply', h, ih]
  intro p
  ext q
  simp only [Mirror.mem_fBlock_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    by_cases h5 : i < 5
    · exact ⟨i + 1, by omega, by rw [Function.iterate_succ_apply]⟩
    · refine ⟨0, by omega, ?_⟩
      have : i = 5 := by omega
      subst this
      have := F_order_six p
      rw [show (6 : ℕ) = 5 + 1 from rfl, Function.iterate_add_apply] at this
      simpa using this.symm
  · rintro ⟨i, hi, rfl⟩
    by_cases h0 : i = 0
    · subst h0
      refine ⟨5, by omega, ?_⟩
      have := F_order_six p
      rw [show (6 : ℕ) = 5 + 1 from rfl, Function.iterate_succ_apply] at this
      simpa using this
    · refine ⟨i - 1, by omega, ?_⟩
      rw [← Function.iterate_succ_apply, Nat.succ_eq_add_one, show i - 1 + 1 = i by omega]

theorem blockCode_eq_imp_fBlock_eq {p q : Perm7}
    (h : blockCode (permWord p) = blockCode (permWord q)) : fBlock p = fBlock q := by
  have hp := blockCode_attained p
  have hq := blockCode_attained q
  rw [List.any_eq_true] at hp hq
  obtain ⟨i, hi, hpi⟩ := hp
  obtain ⟨j, hj, hqj⟩ := hq
  simp only [beq_iff_eq] at hpi hqj
  have hcodes : wcode (permWord ((F^[i]) p)) = wcode (permWord ((F^[j]) q)) := by
    rw [hpi, hqj, h]
  have hw := wcode_injective_of_length (by simp) hcodes
  have hperm : (F^[i]) p = (F^[j]) q := permWord_injective hw
  rw [← fBlock_eq_of_iterate p i, ← fBlock_eq_of_iterate q j, hperm]

theorem blockId_eq_imp_fBlock_eq {p q : Perm7}
    (h : blockId (permWord p) = blockId (permWord q)) : fBlock p = fBlock q := by
  apply blockCode_eq_imp_fBlock_eq
  have hp := blockId_faithful p
  have hq := blockId_faithful q
  unfold blockId at h
  rw [h] at hp
  rw [hp] at hq
  simpa using hq

/-! ## Fields of the encoding -/

def visibleIdList (x : MarkedRow) : List Nat :=
  ((List.range x.row.length).filter (fun i => ∀ j ∈ x.omitted, j.val ≠ i)).map
    fun i => classId (permWord ((F^[i]) x.row.start))

theorem omittedBits_testBit (s : Finset (Fin 6)) (j : Fin 6) :
    (omittedBits s).testBit j.val = decide (j ∈ s) := by
  revert s j; decide

theorem omittedBits_testBit_ge (s : Finset (Fin 6)) (j : ℕ) (hj : 6 ≤ j) :
    (omittedBits s).testBit j = false := by
  apply Nat.testBit_eq_false_of_lt
  calc omittedBits s ≤ ∑ i : Fin 6, 2 ^ i.val := Finset.sum_le_sum_of_subset (Finset.subset_univ s)
    _ = 63 := by decide
    _ < 2 ^ j := lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by omega) hj)

theorem encode_block (x : MarkedRow) : (encode x).block = blockId (permWord x.row.start) := rfl

theorem encode_beta (x : MarkedRow) : (encode x).beta = headIdOfTuple x.row.beta := by
  rcases x with ⟨⟨p, L⟩, s⟩; rfl

theorem encode_visible (x : MarkedRow) : (encode x).visible = bitMask (visibleIdList x) := by
  rcases x with ⟨⟨p, L⟩, s⟩
  simp only [encode, mkMirror, visibleIdList, Row.length]
  congr 1
  congr 1
  apply List.filter_congr
  intro i hi
  simp only [List.mem_range] at hi
  have hi6 : i < 6 := by omega
  have := omittedBits_testBit s ⟨i, hi6⟩
  simp only at this
  rw [this]
  by_cases hmem : (⟨i, hi6⟩ : Fin 6) ∈ s
  · simp only [hmem, decide_true, Bool.not_true, false_eq_decide_iff, not_forall, not_not]
    exact ⟨⟨i, hi6⟩, hmem, rfl⟩
  · simp only [hmem, decide_false, Bool.not_false, true_eq_decide_iff]
    intro j hj hji
    apply hmem
    have : j = ⟨i, hi6⟩ := Fin.ext hji
    rwa [this] at hj

theorem encode_charge (x : MarkedRow) : (encode x).charge = x.charge := by
  rcases x with ⟨⟨p, L⟩, s⟩
  simp only [encode, mkMirror, MarkedRow.charge, Row.length]
  congr 1
  have : ∀ s : Finset (Fin 6),
      ((List.range 6).filter fun j => (omittedBits s).testBit j).length = s.card := by
    decide
  exact this s

/-! ## Mirror disjointness -/

def mirrorDisjoint (r s : MRow) : Prop := r.block ≠ s.block ∧ (r.visible &&& s.visible) = 0

theorem visibleIdList_disjoint_of {x y : MarkedRow}
    (h : Disjoint x.visibleMask y.visibleMask) :
    List.Disjoint (visibleIdList x) (visibleIdList y) := by
  rw [List.disjoint_left]
  intro c hcx hcy
  rcases List.mem_map.mp hcx with ⟨i, hi, rfl⟩
  rcases List.mem_map.mp hcy with ⟨j, hj, hji⟩
  have hclass := classId_eq_imp_rClass_eq hji
  rw [Finset.disjoint_left] at h
  have hi0 := List.mem_filter.mp hi
  have hj0 := List.mem_filter.mp hj
  apply h (a := rClass ((F^[i]) x.row.start))
  · exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨by simpa using hi0.1, by simpa using hi0.2⟩, rfl⟩
  · exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨by simpa using hj0.1, by simpa using hj0.2⟩, hclass⟩

theorem mirrorDisjoint_encode_of {x y : MarkedRow} (h : MarkedDisjoint x y) :
    mirrorDisjoint (encode x) (encode y) := by
  refine ⟨?_, ?_⟩
  · intro hb
    exact h.1 (blockId_eq_imp_fBlock_eq hb)
  · rw [encode_visible, encode_visible, bitMask_land_eq_zero_iff]
    exact visibleIdList_disjoint_of h.2

/-! ## Bucket membership -/

theorem allowedOmissionBits_of_interior : ∀ (s : Finset (Fin 6)) (L : Fin 6),
    (∀ i ∈ s, 0 < i.val ∧ i.val + 1 < L.val + 1) → omittedBits s ∈ allowedOmissionBits L := by
  decide

theorem omittedBits_of_admissible (x : MarkedRow) (hx : Admissible x) :
    omittedBits x.omitted ∈ allowedOmissionBits x.row.lengthCode := by
  apply allowedOmissionBits_of_interior
  intro i hi
  have := hx i hi
  simpa [Row.length] using this

theorem omittedBits_ne_zero_iff (s : Finset (Fin 6)) : (omittedBits s != 0) = decide (s ≠ ∅) := by
  revert s; decide

/-- Every generated mirror row lies in the bucket of its start's head id. -/
theorem mkMirror_mem_bucket : ∀ (p : Perm7) (L : Fin 6), ∀ om ∈ allowedOmissionBits L,
    (mkMirror p L om, om != 0) ∈ buckets.getD (headId p) [] := by
  native_decide

theorem encode_mem_bucket (x : MarkedRow) (hx : Admissible x) :
    (encode x, decide (x.omitted ≠ ∅)) ∈ buckets.getD (headId x.row.start) [] := by
  have := mkMirror_mem_bucket x.row.start x.row.lengthCode (omittedBits x.omitted)
    (omittedBits_of_admissible x hx)
  rw [omittedBits_ne_zero_iff] at this
  exact this

theorem encode_mem_startRows (x : MarkedRow) (hx : Admissible x) (hstart : x.row.start = 1) :
    (encode x, decide (x.omitted ≠ ∅)) ∈ startRows := by
  unfold startRows
  simp only [List.mem_flatMap, List.mem_finRange, List.mem_map, true_and]
  refine ⟨x.row.lengthCode, omittedBits x.omitted, omittedBits_of_admissible x hx, ?_⟩
  rw [omittedBits_ne_zero_iff]
  rcases x with ⟨⟨p, L⟩, s⟩
  simp only at hstart
  subst hstart
  rfl

/-- Compatibility means the successor lies in the bucket named by the mirror `beta`. -/
theorem headId_eq_beta_of_compatible {x y : MarkedRow} (h : MarkedCompatible x y) :
    headId y.row.start = (encode x).beta := by
  rw [encode_beta]
  unfold headId
  unfold MarkedCompatible RowCompatible at h
  rw [h]

/-! ## Freshness along a mirror trail -/

def Fresh : Nat → Nat → List MRow → Prop
  | _, _, [] => True
  | usedBlocks, usedClasses, r :: rs =>
      (usedBlocks &&& blockBit r) = 0 ∧ (usedClasses &&& r.visible) = 0 ∧
      Fresh (usedBlocks ||| blockBit r) (usedClasses ||| r.visible) rs

theorem blockBit_land_eq_zero_iff (r s : MRow) :
    blockBit r &&& blockBit s = 0 ↔ r.block ≠ s.block := by
  constructor
  · intro hzero heq
    have ht := congrArg (fun n => n.testBit r.block) hzero
    simp [blockBit, heq] at ht
  · intro hne
    apply Nat.eq_of_testBit_eq
    intro i
    simp only [Nat.testBit_land, blockBit, testBit_one_shift, Nat.zero_testBit]
    by_cases hir : i = r.block
    · simp [hir, hne]
    · simp [hir]

private theorem fresh_add {usedBlocks usedClasses : Nat} {r : MRow} {rs : List MRow}
    (hfresh : Fresh usedBlocks usedClasses rs) (hdis : ∀ s ∈ rs, mirrorDisjoint r s) :
    Fresh (usedBlocks ||| blockBit r) (usedClasses ||| r.visible) rs := by
  induction rs generalizing usedBlocks usedClasses with
  | nil => simp [Fresh]
  | cons s ss ih =>
      rcases hfresh with ⟨hblock, hvisible, htail⟩
      have hrs := hdis s (by simp)
      have hblock' : (usedBlocks ||| blockBit r) &&& blockBit s = 0 := by
        rw [lor_land_right, hblock, (blockBit_land_eq_zero_iff r s).mpr hrs.1]; rfl
      have hvisible' : (usedClasses ||| r.visible) &&& s.visible = 0 := by
        rw [lor_land_right, hvisible, hrs.2]; rfl
      refine ⟨hblock', hvisible', ?_⟩
      have hi := ih htail (fun z hz => hdis z (by simp [hz]))
      convert hi using 1 <;> ac_rfl

theorem fresh_zero_of_pairwise (xs : List MRow) (hpair : xs.Pairwise mirrorDisjoint) :
    Fresh 0 0 xs := by
  induction xs with
  | nil => simp [Fresh]
  | cons r rs ih =>
      rw [List.pairwise_cons] at hpair
      refine ⟨by simp [blockBit], by simp, ?_⟩
      exact fresh_add (ih hpair.2) hpair.1

theorem pairwise_mirrorDisjoint_of_model (rows : List MarkedRow)
    (h : rows.Pairwise MarkedDisjoint) : (rows.map encode).Pairwise mirrorDisjoint :=
  List.pairwise_map.mpr (h.imp fun hab => mirrorDisjoint_encode_of hab)

/-! ## Completeness of `found` -/

theorem le_getD_of_le_getD_zero {caps : Array Nat} {rem n d : Nat}
    (h : n ≤ caps.getD rem 0) : n ≤ caps.getD rem d := by
  unfold Array.getD at h ⊢
  split
  · rename_i hlt; simp [hlt] at h; exact h
  · rename_i hlt; simp [hlt] at h; omega

theorem admit_isSome {caps : Array Nat} {g target rows holes : Nat} {r : MRow} {rest : ℕ}
    (hbudget : holes + r.charge ≤ g)
    (hreach : target ≤ rows + 1 + rest)
    (hcap : ∀ rem, rem = g - (holes + r.charge) → rem < g → rest ≤ caps.getD rem target) :
    admit caps g target rows holes r = some (holes + r.charge) := by
  unfold admit
  simp only
  rw [if_neg (by omega)]
  by_cases hrem : g - (holes + r.charge) < g
  · simp only [hrem, ↓reduceIte]
    have := hcap _ rfl hrem
    rw [if_neg (by omega)]
  · simp only [hrem, ↓reduceIte]
    rw [if_neg (by omega)]

/-- Main completeness lemma: if the remaining model rows `xs` continue the
mirror state and reach `target`, the search reports `true`. -/
theorem found_complete (caps : Array Nat) (g target : Nat) (allowMarks : Bool)
    (hcaps : CapsValidBelow caps g) :
    ∀ (xs : List MarkedRow) (fuel head usedBlocks usedClasses rows holes : Nat),
      ModelTrail xs →
      (allowMarks = false → ∀ x ∈ xs, x.omitted = ∅) →
      (∀ x, xs.head? = some x → headId x.row.start = head) →
      Fresh usedBlocks usedClasses (xs.map encode) →
      holes + chargeSum xs ≤ g →
      target ≤ rows + xs.length →
      xs.length ≤ fuel →
      found caps g target allowMarks fuel head usedBlocks usedClasses rows holes = true := by
  intro xs
  induction xs with
  | nil =>
      intro fuel head usedBlocks usedClasses rows holes _ _ _ _ _ htarget _
      simp only [List.length_nil, Nat.add_zero] at htarget
      cases fuel <;> simp [found, htarget]
  | cons x rest ih =>
      intro fuel head usedBlocks usedClasses rows holes hmodel hmarks hhead hfresh hcharge htarget hlen
      cases fuel with
      | zero => simp at hlen
      | succ fuel =>
          by_cases hdone : target ≤ rows
          · simp [found, hdone]
          have hx : Admissible x := hmodel.1 x (by simp)
          have hbucket := encode_mem_bucket x hx
          rw [hhead x rfl] at hbucket
          simp only [List.map_cons] at hfresh
          rcases hfresh with ⟨hblock, hvisible, hfreshTail⟩
          simp only [chargeSum_cons] at hcharge
          simp only [List.length_cons] at htarget hlen
          have hrestModel : ModelTrail rest := modelTrail_tail hmodel
          -- the admit step
          have hadmit : admit caps g target rows holes (encode x) = some (holes + (encode x).charge) := by
            apply admit_isSome (rest := rest.length)
            · rw [encode_charge]; omega
            · omega
            · intro rem hrem hlt
              have hvalid := hcaps rem hlt rest hrestModel (by rw [encode_charge] at hrem; omega)
              exact le_getD_of_le_getD_zero hvalid
          have hrec := ih fuel (encode x).beta (usedBlocks ||| blockBit (encode x))
            (usedClasses ||| (encode x).visible) (rows + 1) (holes + (encode x).charge)
            hrestModel
            (fun hm y hy => hmarks hm y (by simp [hy]))
            (by
              intro y hy
              cases rest with
              | nil => simp at hy
              | cons y' rest' =>
                  simp only [List.head?_cons, Option.some.injEq] at hy
                  subst hy
                  exact headId_eq_beta_of_compatible (List.isChain_cons_cons.mp hmodel.2.1).1)
            hfreshTail
            (by rw [encode_charge]; omega)
            (by omega)
            (by omega)
          -- assemble
          simp only [found, hdone, ↓reduceIte, List.any_eq_true, Bool.and_eq_true]
          refine ⟨(encode x, decide (x.omitted ≠ ∅)), hbucket, ?_⟩
          refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
          · cases hm : allowMarks
            · simp [hmarks hm x (by simp)]
            · simp
          · simpa using hblock
          · simpa using hvisible
          · rw [hadmit]; exact hrec

/-- Completeness of `search` for normalized model trails. -/
theorem search_complete (caps : Array Nat) (g target : Nat) (allowMarks : Bool) (fuel : Nat)
    (hcaps : CapsValidBelow caps g)
    (rows : List MarkedRow) (hmodel : ModelTrail rows)
    (hmarks : allowMarks = false → ∀ x ∈ rows, x.omitted = ∅)
    (hfirst : ∀ x, rows.head? = some x → x.row.start = 1)
    (hcharge : chargeSum rows ≤ g)
    (htarget : target ≤ rows.length) (hpos : 0 < target)
    (hlen : rows.length ≤ fuel + 1) :
    search caps g target allowMarks fuel = true := by
  cases rows with
  | nil => simp at htarget; omega
  | cons x rest =>
      have hx : Admissible x := hmodel.1 x (by simp)
      have hstart : x.row.start = 1 := hfirst x rfl
      have hmem := encode_mem_startRows x hx hstart
      have hfreshAll : Fresh 0 0 ((x :: rest).map encode) :=
        fresh_zero_of_pairwise _ (pairwise_mirrorDisjoint_of_model _ hmodel.2.2)
      simp only [List.map_cons] at hfreshAll
      rcases hfreshAll with ⟨_, _, hfreshTail⟩
      simp only [chargeSum_cons] at hcharge
      simp only [List.length_cons] at htarget hlen
      have hrestModel : ModelTrail rest := modelTrail_tail hmodel
      have hadmit : admit caps g target 0 0 (encode x) = some (0 + (encode x).charge) := by
        apply admit_isSome (rest := rest.length)
        · rw [encode_charge]; omega
        · omega
        · intro rem hrem hlt
          have hvalid := hcaps rem hlt rest hrestModel (by rw [encode_charge] at hrem; omega)
          exact le_getD_of_le_getD_zero hvalid
      have hrec := found_complete caps g target allowMarks hcaps rest fuel (encode x).beta
        (blockBit (encode x)) (encode x).visible 1 (0 + (encode x).charge)
        hrestModel
        (fun hm y hy => hmarks hm y (by simp [hy]))
        (by
          intro y hy
          cases rest with
          | nil => simp at hy
          | cons y' rest' =>
              simp only [List.head?_cons, Option.some.injEq] at hy
              subst hy
              exact headId_eq_beta_of_compatible (List.isChain_cons_cons.mp hmodel.2.1).1)
        (by simpa using hfreshTail)
        (by rw [encode_charge]; omega)
        (by omega)
        (by omega)
      simp only [search, List.any_eq_true, Bool.and_eq_true]
      refine ⟨(encode x, decide (x.omitted ≠ ∅)), hmem, ?_, ?_⟩
      · cases hm : allowMarks
        · simp [hmarks hm x (by simp)]
        · simp
      · rw [hadmit]; exact hrec

/-! ## Relabelling closure -/

def relabelMarkedRow (σ : Perm7) (x : MarkedRow) : MarkedRow where
  row := relabelRow σ x.row
  omitted := x.omitted

@[simp] theorem relabelMarkedRow_row (σ : Perm7) (x : MarkedRow) :
    (relabelMarkedRow σ x).row = relabelRow σ x.row := rfl

@[simp] theorem relabelMarkedRow_omitted (σ : Perm7) (x : MarkedRow) :
    (relabelMarkedRow σ x).omitted = x.omitted := rfl

@[simp] theorem relabelMarkedRow_charge (σ : Perm7) (x : MarkedRow) :
    (relabelMarkedRow σ x).charge = x.charge := rfl

theorem admissible_relabel_iff (σ : Perm7) (x : MarkedRow) :
    Admissible (relabelMarkedRow σ x) ↔ Admissible x := by
  rcases x with ⟨⟨p, L⟩, s⟩; rfl

theorem markedVisibleMask_relabel (σ : Perm7) (x : MarkedRow) :
    x.visibleMask.map (Finset.mapEmbedding (relabelPerm σ).toEmbedding).toEmbedding =
      (relabelMarkedRow σ x).visibleMask := by
  ext C
  simp only [Finset.mem_map, RelEmbedding.coe_toEmbedding, Finset.mapEmbedding_apply,
    MarkedRow.visibleMask, Finset.mem_image, Finset.mem_filter, Finset.mem_range,
    relabelMarkedRow_row, relabelRow_length, relabelMarkedRow_omitted]
  constructor
  · rintro ⟨D, ⟨i, ⟨hi, homit⟩, rfl⟩, rfl⟩
    refine ⟨i, ⟨by simpa using hi, homit⟩, ?_⟩
    change rClass ((F^[i]) (relabelPerm σ x.row.start)) =
      (rClass ((F^[i]) x.row.start)).map (relabelPerm σ).toEmbedding
    rw [← relabelPerm_F_iterate, ← rClass_relabel]
  · rintro ⟨i, ⟨hi, homit⟩, hC⟩
    refine ⟨rClass ((F^[i]) x.row.start), ⟨i, ⟨by simpa using hi, homit⟩, rfl⟩, ?_⟩
    rw [rClass_relabel, relabelPerm_F_iterate]
    exact hC

theorem MarkedCompatible_relabel_iff (σ : Perm7) (x y : MarkedRow) :
    MarkedCompatible (relabelMarkedRow σ x) (relabelMarkedRow σ y) ↔ MarkedCompatible x y :=
  RowCompatible_relabel_iff σ x.row y.row

theorem MarkedDisjoint_relabel_iff (σ : Perm7) (x y : MarkedRow) :
    MarkedDisjoint (relabelMarkedRow σ x) (relabelMarkedRow σ y) ↔ MarkedDisjoint x y := by
  unfold MarkedDisjoint
  change (relabelRow σ x.row).block ≠ (relabelRow σ y.row).block ∧
      Disjoint (relabelMarkedRow σ x).visibleMask (relabelMarkedRow σ y).visibleMask ↔
    x.row.block ≠ y.row.block ∧ Disjoint x.visibleMask y.visibleMask
  rw [← rowBlock_relabel σ x.row, ← rowBlock_relabel σ y.row,
    ← markedVisibleMask_relabel σ x, ← markedVisibleMask_relabel σ y,
    (Finset.map_injective (relabelPerm σ).toEmbedding).ne_iff, Finset.disjoint_map]

theorem modelTrail_map_relabel (σ : Perm7) (rows : List MarkedRow) (h : ModelTrail rows) :
    ModelTrail (rows.map (relabelMarkedRow σ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro y hy
    rcases List.mem_map.mp hy with ⟨z, hz, rfl⟩
    exact (admissible_relabel_iff σ z).mpr (h.1 z hz)
  · exact (List.isChain_map (relabelMarkedRow σ)).mpr
      (h.2.1.imp fun _ _ hxy => (MarkedCompatible_relabel_iff σ _ _).mpr hxy)
  · exact List.pairwise_map.mpr
      (h.2.2.imp fun {a b} hxy => (MarkedDisjoint_relabel_iff σ a b).mpr hxy)

theorem chargeSum_map_relabel (σ : Perm7) (rows : List MarkedRow) :
    chargeSum (rows.map (relabelMarkedRow σ)) = chargeSum rows := by
  unfold chargeSum
  simp [List.map_map, Function.comp_def]

/-- If `search caps g target true fuel = false` and caps are valid below `g`,
then every model trail of charge `≤ g` and length `≤ fuel + 1` is shorter
than `target`. -/
theorem length_lt_of_search_false (caps : Array Nat) (g target fuel : Nat)
    (hcaps : CapsValidBelow caps g) (hpos : 0 < target) (hfuel : target ≤ fuel + 1)
    (hsearch : search caps g target true fuel = false)
    (rows : List MarkedRow) (hmodel : ModelTrail rows) (hcharge : chargeSum rows ≤ g) :
    rows.length < target := by
  by_contra hge
  push_neg at hge
  -- truncate to exactly `target` rows and normalize the first start
  let cut := rows.take target
  have hcutModel : ModelTrail cut := modelTrail_take rows hmodel target
  have hcutLen : cut.length = target := by simp [cut]; omega
  have hcutCharge : chargeSum cut ≤ g := le_trans (chargeSum_take_le rows target) hcharge
  cases hc : cut with
  | nil => rw [hc] at hcutLen; simp at hcutLen; omega
  | cons x xs =>
      let σ := x.row.start.symm
      let norm := (x :: xs).map (relabelMarkedRow σ)
      have hnormModel : ModelTrail norm := modelTrail_map_relabel σ _ (hc ▸ hcutModel)
      have hnormCharge : chargeSum norm ≤ g := by
        rw [chargeSum_map_relabel]; rw [hc] at hcutCharge; exact hcutCharge
      have hnormLen : norm.length = target := by simp [norm]; rw [hc] at hcutLen; simpa using hcutLen
      have hfirst : ∀ y, norm.head? = some y → y.row.start = 1 := by
        intro y hy
        simp only [norm, List.map_cons, List.head?_cons, Option.some.injEq] at hy
        subst hy
        change relabelPerm x.row.start.symm x.row.start = 1
        exact relabelPerm_self_symm x.row.start
      have := search_complete caps g target true fuel hcaps norm hnormModel (by simp) hfirst
        hnormCharge (by omega) hpos (by omega)
      rw [hsearch] at this
      exact Bool.false_ne_true this

/-! ## Certified cap tables -/

/-- Boolean certificate: for every `g ≤ G`, the search for one more row than
`caps[g]` fails (with marks allowed, fuel `caps[g] + 1`). -/
def capsChecked (caps : Array Nat) (G : Nat) : Bool :=
  (List.range (G + 1)).all fun g =>
    search caps g (caps.getD g 0 + 1) true (caps.getD g 0 + 1) == false

theorem capsValid_of_checked (caps : Array Nat) (G : Nat) (h : capsChecked caps G = true) :
    ∀ g ≤ G, CapValidAt caps g := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
      intro hg rows hmodel hcharge
      have hbelow : CapsValidBelow caps g := fun g' hg' => ih g' hg' (by omega)
      have hall := List.all_eq_true.mp h g (by simp; omega)
      simp only [beq_iff_eq] at hall
      have := length_lt_of_search_false caps g (caps.getD g 0 + 1) (caps.getD g 0 + 1) hbelow
        (by omega) (by omega) hall rows hmodel hcharge
      omega

end Superperm7
