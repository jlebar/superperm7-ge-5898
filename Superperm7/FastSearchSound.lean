/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.FastSearch
import Superperm7.SearchSound

/-!
# Completeness of the fast search kernel

`Fast.fsearch caps g target mu fuel = false` refutes every model marked trail
with at most `mu` marked rows, charge `≤ g` and `≥ target` rows, provided
`caps` is valid below `g` (for trails with at most `mu` marked rows).
-/

namespace Superperm7

open Mirror

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false

/-! ## Marked-row counts and `mu`-restricted validity -/

def isMarked (x : MarkedRow) : Bool := decide (x.omitted ≠ ∅)

def markCount (rows : List MarkedRow) : ℕ := rows.countP fun x => isMarked x

@[simp] theorem markCount_nil : markCount [] = 0 := rfl
theorem markCount_cons (x : MarkedRow) (xs : List MarkedRow) :
    markCount (x :: xs) = (if isMarked x then 1 else 0) + markCount xs := by
  unfold markCount; rw [List.countP_cons]; split <;> omega

theorem markCount_take_le (rows : List MarkedRow) (n : ℕ) :
    markCount (rows.take n) ≤ markCount rows :=
  (List.take_sublist n rows).countP_le

theorem markCount_drop_le (rows : List MarkedRow) (n : ℕ) :
    markCount (rows.drop n) ≤ markCount rows :=
  (List.drop_sublist n rows).countP_le

/-- `caps` is a valid cap at budget `g'` for model trails with at most `mu` marked rows. -/
def CapValidMuAt (mu : ℕ) (caps : Array Nat) (g' : ℕ) : Prop :=
  ∀ rows : List MarkedRow, ModelTrail rows → markCount rows ≤ mu → chargeSum rows ≤ g' →
    rows.length ≤ caps.getD g' 0

def CapsValidMuBelow (mu : ℕ) (caps : Array Nat) (g : ℕ) : Prop :=
  ∀ g' < g, CapValidMuAt mu caps g'

/-! ## `packIds` / `Cand.cls` round trip -/

theorem cls_packIds (ids : List Nat) (hids : ∀ c ∈ ids, c < 1024) :
    ∀ j < ids.length, ((packIds ids) >>> (10 * j)) &&& 1023 = ids[j]! := by
  induction ids with
  | nil => intro j hj; simp at hj
  | cons c cs ih =>
      intro j hj
      have hc : c < 1024 := hids c (by simp)
      have hcs : ∀ d ∈ cs, d < 1024 := fun d hd => hids d (by simp [hd])
      have h1023 : (1023 : ℕ) = 2 ^ 10 - 1 := by norm_num
      cases j with
      | zero =>
          simp only [packIds, Nat.mul_zero, Nat.shiftRight_zero, List.getElem!_cons_zero]
          rw [h1023, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq, Nat.add_mul_mod_self_right]
          exact Nat.mod_eq_of_lt hc
      | succ j =>
          simp only [List.length_cons, Nat.add_lt_add_iff_right] at hj
          simp only [packIds, List.getElem!_cons_succ]
          have hshift : (c + packIds cs <<< 10) >>> (10 * (j + 1)) = packIds cs >>> (10 * j) := by
            rw [Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
              show 10 * (j + 1) = 10 + 10 * j by ring, Nat.pow_add, ← Nat.div_div_eq_div_mul,
              Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hc, Nat.zero_add]
          rw [hshift]
          exact ih hcs j hj

/-! ## Agreement of `mkCand` with the model -/

def fencode (x : MarkedRow) : Cand := mkCand x.row.start x.row.lengthCode (omittedBits x.omitted)

theorem allowedOmissionBitsN_eq (L : Fin 6) : allowedOmissionBitsN L.val = allowedOmissionBits L := by
  fin_cases L <;> rfl

theorem iter_rotF_permWord : ∀ (p : Perm7) (j : Fin 6),
    iter rotF j.val (permWord p) = permWord ((F^[j.val]) p) := by
  native_decide

theorem tailTupleW_permWord : ∀ (p : Perm7) (L : Fin 6),
    tailTupleW (permWord p) L.val = (rowOfLength p L).beta := by
  native_decide

theorem classId_lt : ∀ p : Perm7, classId (permWord p) < 720 := by native_decide
theorem blockId_lt : ∀ p : Perm7, blockId (permWord p) < 840 := by native_decide
theorem headId_lt : ∀ p : Perm7, headId p < 840 := by native_decide

/-- The visible class-id list of the encoding is the model's `visibleIdList`. -/
theorem fencode_ids (x : MarkedRow) :
    ((List.range (x.row.lengthCode.val + 1)).filter fun j => !((omittedBits x.omitted).testBit j)).map
        (fun j => classId (iter rotF j (permWord x.row.start))) = visibleIdList x := by
  rcases x with ⟨⟨p, L⟩, s⟩
  simp only [visibleIdList, Row.length]
  have hf : ((List.range (L.val + 1)).filter fun j => !((omittedBits s).testBit j)) =
      ((List.range (L.val + 1)).filter fun i => ∀ j ∈ s, j.val ≠ i) := by
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
  rw [hf]
  apply List.map_congr_left
  intro j hj
  simp only [List.mem_filter, List.mem_range] at hj
  have hj6 : j < 6 := by omega
  have := iter_rotF_permWord p ⟨j, hj6⟩
  simp only at this
  rw [this]

theorem visibleIdList_lt (x : MarkedRow) : ∀ c ∈ visibleIdList x, c < 1024 := by
  intro c hc
  rcases List.mem_map.mp hc with ⟨i, _, rfl⟩
  have := classId_lt ((F^[i]) x.row.start)
  omega

theorem visibleIdList_length_le (x : MarkedRow) : (visibleIdList x).length ≤ 6 := by
  unfold visibleIdList
  rw [List.length_map]
  refine le_trans (List.length_filter_le _ _) ?_
  simp [Row.length]

theorem fencode_cnt (x : MarkedRow) : (fencode x).cnt = (visibleIdList x).length := by
  unfold fencode mkCand mkCandW
  simp only
  rw [← fencode_ids x]

theorem fencode_clsList (x : MarkedRow) : (fencode x).clsList = visibleIdList x := by
  unfold Cand.clsList
  rw [fencode_cnt]
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp only [List.getElem_map, List.getElem_range]
    unfold Cand.cls fencode mkCand mkCandW
    simp only
    rw [fencode_ids x, cls_packIds _ (visibleIdList_lt x) j (by simpa using h1)]
    exact (List.getElem!_eq_getElem?_getD ..).trans (by simp [List.getElem?_eq_getElem h2])

theorem fencode_block (x : MarkedRow) : (fencode x).block = blockId (permWord x.row.start) := rfl

theorem fencode_beta (x : MarkedRow) : (fencode x).beta = headIdOfTuple x.row.beta := by
  rcases x with ⟨⟨p, L⟩, s⟩
  unfold fencode mkCand mkCandW
  simp only
  rw [tailTupleW_permWord p L]
  rfl

theorem fencode_marked (x : MarkedRow) : (fencode x).marked = isMarked x := by
  unfold fencode mkCand mkCandW isMarked
  simp only
  exact omittedBits_ne_zero_iff x.omitted

theorem fencode_charge (x : MarkedRow) (hx : Admissible x) : (fencode x).charge = x.charge := by
  have h1 : (fencode x).charge = 6 - (visibleIdList x).length := by
    unfold fencode mkCand mkCandW; simp only; rw [← fencode_ids x]
  rw [h1]
  -- visible + charge = 6 for admissible rows
  rcases x with ⟨⟨p, L⟩, s⟩
  simp only [visibleIdList, MarkedRow.charge, Row.length, List.length_map]
  have key : ∀ (s : Finset (Fin 6)) (L : Fin 6), (∀ i ∈ s, 0 < i.val ∧ i.val + 1 < L.val + 1) →
      6 - ((List.range (L.val + 1)).filter fun i => ∀ j ∈ s, j.val ≠ i).length =
        (6 - (L.val + 1)) + s.card := by
    decide
  exact key s L (fun i hi => by simpa [Row.length] using hx i hi)

/-! ## Bucket membership -/

theorem mkCandW_mem_cands : ∀ (p : Perm7) (L : Fin 6), ∀ om ∈ allowedOmissionBits L,
    mkCandW (permWord p) L.val om ∈ cands.getD (headId p) #[] := by
  native_decide

theorem fencode_mem_cands (x : MarkedRow) (hx : Admissible x) :
    fencode x ∈ cands.getD (headId x.row.start) #[] :=
  mkCandW_mem_cands x.row.start x.row.lengthCode (omittedBits x.omitted) (omittedBits_of_admissible x hx)

theorem mkCandW_mem_startCands : ∀ (L : Fin 6), ∀ om ∈ allowedOmissionBits L,
    mkCandW (permWord 1) L.val om ∈ startCands := by
  native_decide

theorem fencode_mem_startCands (x : MarkedRow) (hx : Admissible x) (hstart : x.row.start = 1) :
    fencode x ∈ startCands := by
  have := mkCandW_mem_startCands x.row.lengthCode (omittedBits x.omitted) (omittedBits_of_admissible x hx)
  unfold fencode mkCand
  rw [hstart]
  exact this

theorem headId_eq_fbeta_of_compatible {x y : MarkedRow} (h : MarkedCompatible x y) :
    headId y.row.start = (fencode x).beta := by
  rw [fencode_beta]
  unfold headId
  unfold MarkedCompatible RowCompatible at h
  rw [h]

/-! ## Bitset semantics -/

namespace BitSet

def size (s : BitSet) : Nat := s.data.size

theorem size_insert (s : BitSet) (i : Nat) : (s.insert i).size = s.size := by
  rcases s with ⟨⟨bs⟩⟩
  show (bs.set! _ _).size = bs.size
  simp

theorem uint8_bit_or (b : UInt8) (k k' : Nat) (hk : k < 8) (hk' : k' < 8) :
    ((b ||| ((1 : UInt8) <<< k.toUInt8)) &&& ((1 : UInt8) <<< k'.toUInt8) != 0) =
      (decide (k' = k) || (b &&& ((1 : UInt8) <<< k'.toUInt8) != 0)) := by
  have : ∀ (b : UInt8) (k k' : Fin 8),
      ((b ||| ((1 : UInt8) <<< k.val.toUInt8)) &&& ((1 : UInt8) <<< k'.val.toUInt8) != 0) =
        (decide (k'.val = k.val) || (b &&& ((1 : UInt8) <<< k'.val.toUInt8) != 0)) := by
    native_decide
  exact this b ⟨k, hk⟩ ⟨k', hk'⟩

theorem uint8_zero_bit (k : Nat) (hk : k < 8) :
    ((0 : UInt8) &&& ((1 : UInt8) <<< k.toUInt8) != 0) = false := by
  have : ∀ k : Fin 8, ((0 : UInt8) &&& ((1 : UInt8) <<< k.val.toUInt8) != 0) = false := by native_decide
  exact this ⟨k, hk⟩

private theorem default_zero_bit (k : Nat) (hk : k < 8) :
    ((default : UInt8) &&& ((1 : UInt8) <<< k.toUInt8) != 0) = false := uint8_zero_bit k hk

theorem and7_lt (i : Nat) : i &&& 7 < 8 := by
  have : i &&& 7 = i % 8 := Nat.and_two_pow_sub_one_eq_mod i 3
  omega

theorem contains_empty (n i : Nat) : (BitSet.empty n).contains i = false := by
  unfold BitSet.empty BitSet.contains
  show ((Array.replicate n (0 : UInt8))[i >>> 3]! &&& _ != 0) = false
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
  by_cases h : i >>> 3 < n
  · rw [Array.getElem?_replicate, if_pos h]; exact uint8_zero_bit _ (and7_lt i)
  · rw [Array.getElem?_replicate, if_neg h]; exact uint8_zero_bit _ (and7_lt i)

theorem getElem!_set! (bs : Array UInt8) (a b : Nat) (v : UInt8) (ha : a < bs.size) :
    (bs.set! a v)[b]! = if a = b then v else bs[b]! := by
  rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds]
  split
  · subst_vars; simp [ha]
  · rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]

theorem contains_insert (s : BitSet) (i j : Nat) (hi : i < 8 * s.size) (hj : j < 8 * s.size) :
    (s.insert i).contains j = (decide (j = i) || s.contains j) := by
  rcases s with ⟨⟨bs⟩⟩
  unfold BitSet.insert BitSet.contains
  simp only [BitSet.size, ByteArray.size] at hi hj
  show ((bs.set! (i >>> 3) (bs[i >>> 3]! ||| _))[j >>> 3]! &&& _ != 0) = (decide (j = i) || (bs[j >>> 3]! &&& _ != 0))
  have hi3 : i >>> 3 = i / 8 := Nat.shiftRight_eq_div_pow i 3
  have hj3 : j >>> 3 = j / 8 := Nat.shiftRight_eq_div_pow j 3
  have hik : i >>> 3 < bs.size := by rw [hi3]; omega
  have hi7 : i &&& 7 = i % 8 := Nat.and_two_pow_sub_one_eq_mod i 3
  have hj7 : j &&& 7 = j % 8 := Nat.and_two_pow_sub_one_eq_mod j 3
  rw [getElem!_set! _ _ _ _ hik]
  by_cases hblk : i >>> 3 = j >>> 3
  · rw [if_pos hblk, hblk, uint8_bit_or _ _ _ (and7_lt i) (and7_lt j)]
    congr 1
    apply Bool.decide_congr
    omega
  · rw [if_neg hblk]
    have hne : ¬ j = i := fun h => hblk (by rw [h])
    simp [hne]

end BitSet

/-! ## Class/block ids are in range -/

theorem clsList_lt_720 (x : MarkedRow) : ∀ c ∈ (fencode x).clsList, c < 720 := by
  rw [fencode_clsList]
  intro c hc
  rcases List.mem_map.mp hc with ⟨i, _, rfl⟩
  exact classId_lt _

theorem fblock_lt_840 (x : MarkedRow) : (fencode x).block < 840 := blockId_lt _

/-! ## The represented sets -/

/-- `cs`/`bs` represent exactly the visible classes / blocks of the rows `done`. -/
structure Represents (cs bs : BitSet) (done : List MarkedRow) : Prop where
  csize : cs.size = 90
  bsize : bs.size = 105
  cls : ∀ i < 720, cs.contains i = decide (∃ x ∈ done, i ∈ (fencode x).clsList)
  blk : ∀ i < 840, bs.contains i = decide (∃ x ∈ done, i = (fencode x).block)

theorem represents_empty : Represents Fast.emptyClasses Fast.emptyBlocks [] where
  csize := by rfl
  bsize := by rfl
  cls := by intro i _; rw [Fast.emptyClasses, BitSet.contains_empty]; simp
  blk := by intro i _; rw [Fast.emptyBlocks, BitSet.contains_empty]; simp

theorem insertAux_size (cs : BitSet) (c : Cand) : ∀ n, (Fast.insertAux cs c n).size = cs.size
  | 0 => rfl
  | n + 1 => by rw [Fast.insertAux, BitSet.size_insert, insertAux_size cs c n]

theorem contains_insertAux (cs : BitSet) (c : Cand) (hcs : cs.size = 90)
    (hc : ∀ j < c.cnt, c.cls j < 720) :
    ∀ n ≤ c.cnt, ∀ i < 720, (Fast.insertAux cs c n).contains i =
      (decide (∃ j < n, i = c.cls j) || cs.contains i)
  | 0, _, i, _ => by simp [Fast.insertAux]
  | n + 1, hn, i, hi => by
      rw [Fast.insertAux, BitSet.contains_insert _ _ _ (by rw [insertAux_size, hcs]; have := hc n (by omega); omega)
        (by rw [insertAux_size, hcs]; omega), contains_insertAux cs c hcs hc n (by omega) i hi]
      by_cases h1 : i = c.cls n
      · simp only [h1, decide_true, Bool.true_or, Bool.true_eq, Bool.or_eq_true, decide_eq_true_eq]
        exact Or.inl ⟨n, by omega, rfl⟩
      · simp only [h1, decide_false, Bool.false_or]
        congr 1
        apply Bool.decide_congr
        constructor
        · rintro ⟨j, hj, rfl⟩; exact ⟨j, by omega, rfl⟩
        · rintro ⟨j, hj, rfl⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
          · exact ⟨j, hj, rfl⟩
          · exact absurd (by rw [hj]) h1

theorem mem_clsList_iff (c : Cand) (i : Nat) : i ∈ c.clsList ↔ ∃ j < c.cnt, i = c.cls j := by
  unfold Cand.clsList
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩

theorem represents_step {cs bs : BitSet} {done : List MarkedRow} (h : Represents cs bs done)
    (x : MarkedRow) :
    Represents (Fast.insertAll cs (fencode x)) (bs.insert (fencode x).block) (done ++ [x]) where
  csize := by rw [Fast.insertAll, insertAux_size, h.csize]
  bsize := by rw [BitSet.size_insert, h.bsize]
  cls := by
    intro i hi
    have hc : ∀ j < (fencode x).cnt, (fencode x).cls j < 720 := by
      intro j hj
      exact clsList_lt_720 x _ ((mem_clsList_iff _ _).mpr ⟨j, hj, rfl⟩)
    rw [Fast.insertAll, contains_insertAux cs (fencode x) h.csize hc _ le_rfl i hi, h.cls i hi]
    rw [← Bool.decide_or]
    apply Bool.decide_congr
    simp only [List.mem_append, List.mem_singleton, mem_clsList_iff]
    constructor
    · rintro (⟨j, hj, rfl⟩ | ⟨y, hy, hyi⟩)
      · exact ⟨x, Or.inr rfl, j, hj, rfl⟩
      · exact ⟨y, Or.inl hy, hyi⟩
    · rintro ⟨y, hy | rfl, hyi⟩
      · exact Or.inr ⟨y, hy, hyi⟩
      · exact Or.inl hyi
  blk := by
    intro i hi
    rw [BitSet.contains_insert _ _ _ (by rw [h.bsize]; have := fblock_lt_840 x; omega) (by rw [h.bsize]; omega),
      h.blk i hi]
    rw [← Bool.decide_or]
    apply Bool.decide_congr
    simp only [List.mem_append, List.mem_singleton]
    constructor
    · rintro (rfl | ⟨y, hy, rfl⟩)
      · exact ⟨x, Or.inr rfl, rfl⟩
      · exact ⟨y, Or.inl hy, rfl⟩
    · rintro ⟨y, hy | rfl, rfl⟩
      · exact Or.inr ⟨y, hy, rfl⟩
      · exact Or.inl rfl

/-- With disjointness from everything done, the candidate is fresh. -/
theorem free_of_disjoint {cs bs : BitSet} {done : List MarkedRow} (h : Represents cs bs done)
    (x : MarkedRow) (hdis : ∀ y ∈ done, MarkedDisjoint y x) :
    bs.contains (fencode x).block = false ∧ Fast.free cs (fencode x) = true := by
  constructor
  · rw [h.blk _ (fblock_lt_840 x)]
    simp only [decide_eq_false_iff_not, not_exists, not_and]
    intro y hy heq
    exact (hdis y hy).1 (blockId_eq_imp_fBlock_eq heq.symm)
  · have hfree : ∀ n ≤ (fencode x).cnt, Fast.freeAux cs (fencode x) n = true := by
      intro n
      induction n with
      | zero => intro; rfl
      | succ n ih =>
          intro hn
          rw [Fast.freeAux, ih (by omega), Bool.and_true, Bool.not_eq_true']
          have hlt : (fencode x).cls n < 720 :=
            clsList_lt_720 x _ ((mem_clsList_iff _ _).mpr ⟨n, by omega, rfl⟩)
          rw [h.cls _ hlt]
          simp only [decide_eq_false_iff_not, not_exists, not_and]
          intro y hy hmem
          have hxmem : (fencode x).cls n ∈ (fencode x).clsList :=
            (mem_clsList_iff _ _).mpr ⟨n, by omega, rfl⟩
          rw [fencode_clsList] at hmem hxmem
          exact List.disjoint_left.mp (visibleIdList_disjoint_of (hdis y hy).2) hmem hxmem
    exact hfree _ le_rfl

/-! ## Completeness -/

theorem admit_isSome' {caps : Array Nat} {g target rows holes ch : Nat} {rest : ℕ}
    (hbudget : holes + ch ≤ g)
    (hreach : target ≤ rows + 1 + rest)
    (hcap : ∀ rem, rem = g - (holes + ch) → rem < g → rest ≤ caps.getD rem target) :
    Fast.admit caps g target rows holes ch = some (holes + ch) := by
  unfold Fast.admit
  simp only
  rw [if_neg (by omega)]
  by_cases hrem : g - (holes + ch) < g
  · simp only [hrem, ↓reduceIte]
    have := hcap _ rfl hrem
    rw [if_neg (by omega)]
  · simp only [hrem, ↓reduceIte]
    rw [if_neg (by omega)]

theorem pairwise_snoc {done : List MarkedRow} {x : MarkedRow} {rest : List MarkedRow}
    (h : (done ++ x :: rest).Pairwise MarkedDisjoint) : ∀ y ∈ done, MarkedDisjoint y x := by
  intro y hy
  rw [List.pairwise_append] at h
  exact h.2.2 y hy x (by simp)

/-- Main completeness lemma for `ffound`. -/
theorem ffound_complete (caps : Array Nat) (g target mu : Nat) (hcaps : CapsValidMuBelow mu caps g) :
    ∀ (xs done : List MarkedRow) (fuel head : Nat) (cs bs : BitSet) (holes marks : Nat),
      ModelTrail (done ++ xs) →
      Represents cs bs done →
      (∀ x, xs.head? = some x → headId x.row.start = head) →
      holes + chargeSum xs ≤ g →
      marks + markCount xs ≤ mu →
      target ≤ done.length + xs.length →
      xs.length ≤ fuel →
      Fast.ffound caps g target mu fuel head cs bs done.length holes marks = true := by
  intro xs
  induction xs with
  | nil =>
      intro done fuel head cs bs holes marks _ _ _ _ _ htarget _
      simp only [List.length_nil, Nat.add_zero] at htarget
      cases fuel <;> simp [Fast.ffound, htarget]
  | cons x rest ih =>
      intro done fuel head cs bs holes marks hmodel hrep hhead hcharge hmarks htarget hlen
      cases fuel with
      | zero => simp at hlen
      | succ fuel =>
          by_cases hdone : target ≤ done.length
          · simp [Fast.ffound, hdone]
          have hx : Admissible x := hmodel.1 x (by simp)
          have hcand := fencode_mem_cands x hx
          rw [hhead x rfl] at hcand
          simp only [chargeSum_cons] at hcharge
          rw [markCount_cons] at hmarks
          simp only [List.length_cons] at htarget hlen
          have hdis := pairwise_snoc hmodel.2.2
          obtain ⟨hblk, hfree⟩ := free_of_disjoint hrep x hdis
          have hrestModel : ModelTrail rest := by
            have hsuf : ModelTrail (x :: rest) :=
              ⟨fun y hy => hmodel.1 y (by simp [hy]),
               hmodel.2.1.suffix (List.suffix_append done (x :: rest)),
               hmodel.2.2.sublist (List.sublist_append_right done (x :: rest))⟩
            exact modelTrail_tail hsuf
          have hadmit : Fast.admit caps g target done.length holes (fencode x).charge =
              some (holes + (fencode x).charge) := by
            apply admit_isSome' (rest := rest.length)
            · rw [fencode_charge x hx]; omega
            · omega
            · intro rem hrem hlt
              have hvalid := hcaps rem hlt rest hrestModel (by omega) (by rw [fencode_charge x hx] at hrem; omega)
              exact le_getD_of_le_getD_zero hvalid
          have htry : Fast.tryCand caps g target mu cs bs done.length holes marks (fencode x) =
              some (holes + (fencode x).charge) := by
            unfold Fast.tryCand
            rw [fencode_marked]
            have hm : ¬ (isMarked x && decide (mu ≤ marks)) = true := by
              cases hxm : isMarked x
              · simp
              · simp only [hxm, ↓reduceIte] at hmarks; simp; omega
            rw [if_neg hm, hblk, if_neg (by simp), hfree, if_neg (by simp), hadmit]
          have hrec := ih (done ++ [x]) fuel (fencode x).beta (Fast.insertAll cs (fencode x))
            (bs.insert (fencode x).block) (holes + (fencode x).charge)
            (if (fencode x).marked then marks + 1 else marks)
            (by simpa using hmodel)
            (represents_step hrep x)
            (by
              intro y hy
              cases rest with
              | nil => simp at hy
              | cons y' rest' =>
                  simp only [List.head?_cons, Option.some.injEq] at hy
                  rw [← hy]
                  have hchain := hmodel.2.1
                  have : (x :: y' :: rest').IsChain MarkedCompatible :=
                    (hchain.suffix (List.suffix_append done (x :: y' :: rest')))
                  exact headId_eq_fbeta_of_compatible (List.isChain_cons_cons.mp this).1)
            (by rw [fencode_charge x hx]; omega)
            (by rw [fencode_marked]; split <;> simp_all <;> omega)
            (by simp; omega)
            (by omega)
          simp only [List.length_append, List.length_singleton] at hrec
          simp only [Fast.ffound, hdone, ↓reduceIte, Array.any_eq_true]
          obtain ⟨i, hi, hci⟩ := Array.getElem_of_mem hcand
          refine ⟨i, hi, ?_⟩
          rw [hci, htry]
          exact hrec

/-- Completeness of `fsearch` for normalized model trails with at most `mu` marks. -/
theorem fsearch_complete (caps : Array Nat) (g target mu fuel : Nat)
    (hcaps : CapsValidMuBelow mu caps g)
    (rows : List MarkedRow) (hmodel : ModelTrail rows) (hmarks : markCount rows ≤ mu)
    (hfirst : ∀ x, rows.head? = some x → x.row.start = 1)
    (hcharge : chargeSum rows ≤ g)
    (htarget : target ≤ rows.length) (hpos : 0 < target)
    (hlen : rows.length ≤ fuel + 1) :
    Fast.fsearch caps g target mu fuel = true := by
  cases rows with
  | nil => simp at htarget; omega
  | cons x rest =>
      have hx : Admissible x := hmodel.1 x (by simp)
      have hstart : x.row.start = 1 := hfirst x rfl
      have hmem := fencode_mem_startCands x hx hstart
      obtain ⟨hblk, hfree⟩ := free_of_disjoint represents_empty x (by simp)
      simp only [chargeSum_cons] at hcharge
      rw [markCount_cons] at hmarks
      simp only [List.length_cons] at htarget hlen
      have hrestModel : ModelTrail rest := modelTrail_tail hmodel
      have hadmit : Fast.admit caps g target 0 0 (fencode x).charge = some (0 + (fencode x).charge) := by
        apply admit_isSome' (rest := rest.length)
        · rw [fencode_charge x hx]; omega
        · omega
        · intro rem hrem hlt
          have hvalid := hcaps rem hlt rest hrestModel (by omega) (by rw [fencode_charge x hx] at hrem; omega)
          exact le_getD_of_le_getD_zero hvalid
      have htry : Fast.tryCand caps g target mu Fast.emptyClasses Fast.emptyBlocks 0 0 0 (fencode x) =
          some (0 + (fencode x).charge) := by
        unfold Fast.tryCand
        rw [fencode_marked]
        have hm : ¬ (isMarked x && decide (mu ≤ 0)) = true := by
          cases hxm : isMarked x
          · simp
          · simp only [hxm, ↓reduceIte] at hmarks; simp; omega
        rw [if_neg hm, hblk, if_neg (by simp), hfree, if_neg (by simp), hadmit]
      have hrec := ffound_complete caps g target mu hcaps rest [x] fuel (fencode x).beta
        (Fast.insertAll Fast.emptyClasses (fencode x)) (Fast.emptyBlocks.insert (fencode x).block)
        (0 + (fencode x).charge) (if (fencode x).marked then 1 else 0)
        (by simpa using hmodel)
        (by simpa using represents_step represents_empty x)
        (by
          intro y hy
          cases rest with
          | nil => simp at hy
          | cons y' rest' =>
              simp only [List.head?_cons, Option.some.injEq] at hy
              rw [← hy]
              exact headId_eq_fbeta_of_compatible (List.isChain_cons_cons.mp hmodel.2.1).1)
        (by rw [fencode_charge x hx]; omega)
        (by rw [fencode_marked]; split <;> simp_all <;> omega)
        (by simp; omega)
        (by omega)
      simp only [List.length_singleton] at hrec
      simp only [Fast.fsearch, Array.any_eq_true]
      obtain ⟨i, hi, hci⟩ := Array.getElem_of_mem hmem
      refine ⟨i, hi, ?_⟩
      rw [hci, htry]
      exact hrec

/-- If `fsearch caps g target mu fuel = false` and caps are valid below `g` for
`mu`-marked trails, every model trail with at most `mu` marks and charge `≤ g`
(and `target ≤ fuel + 1`) has fewer than `target` rows. -/
theorem length_lt_of_fsearch_false (caps : Array Nat) (g target mu fuel : Nat)
    (hcaps : CapsValidMuBelow mu caps g) (hpos : 0 < target) (hfuel : target ≤ fuel + 1)
    (hsearch : Fast.fsearch caps g target mu fuel = false)
    (rows : List MarkedRow) (hmodel : ModelTrail rows) (hmarks : markCount rows ≤ mu)
    (hcharge : chargeSum rows ≤ g) :
    rows.length < target := by
  by_contra hge
  push Not at hge
  let cut := rows.take target
  have hcutModel : ModelTrail cut := modelTrail_take rows hmodel target
  have hcutLen : cut.length = target := by simp [cut]; omega
  have hcutCharge : chargeSum cut ≤ g := le_trans (chargeSum_take_le rows target) hcharge
  have hcutMarks : markCount cut ≤ mu := le_trans (markCount_take_le rows target) hmarks
  cases hc : cut with
  | nil => rw [hc] at hcutLen; simp at hcutLen; omega
  | cons x xs =>
      let σ := x.row.start.symm
      let norm := (x :: xs).map (relabelMarkedRow σ)
      have hnormModel : ModelTrail norm := modelTrail_map_relabel σ _ (hc ▸ hcutModel)
      have hnormCharge : chargeSum norm ≤ g := by
        rw [chargeSum_map_relabel]; rw [hc] at hcutCharge; exact hcutCharge
      have hnormMarks : markCount norm ≤ mu := by
        have : markCount norm = markCount (x :: xs) := by
          unfold markCount norm
          rw [List.countP_map]
          rfl
        rw [this]; rw [hc] at hcutMarks; exact hcutMarks
      have hnormLen : norm.length = target := by simp [norm]; rw [hc] at hcutLen; simpa using hcutLen
      have hfirst : ∀ y, norm.head? = some y → y.row.start = 1 := by
        intro y hy
        simp only [norm, List.map_cons, List.head?_cons, Option.some.injEq] at hy
        subst hy
        change relabelPerm x.row.start.symm x.row.start = 1
        exact relabelPerm_self_symm x.row.start
      have := fsearch_complete caps g target mu fuel hcaps norm hnormModel hnormMarks hfirst
        hnormCharge (by omega) hpos (by omega)
      rw [hsearch] at this
      exact Bool.false_ne_true this

/-! ## Certified tables, `mu`-indexed -/

/-- for every `g ≤ G`, the fast search for one more row than `caps[g]` fails -/
def fcapsChecked (caps : Array Nat) (mu G : Nat) : Bool :=
  (List.range (G + 1)).all fun g =>
    Fast.fsearch caps g (caps.getD g 0 + 1) mu (caps.getD g 0 + 1) == false

theorem capsValidMu_of_checked (caps : Array Nat) (mu G : Nat) (h : fcapsChecked caps mu G = true) :
    ∀ g ≤ G, CapValidMuAt mu caps g := by
  intro g
  induction g using Nat.strong_induction_on with
  | _ g ih =>
      intro hg rows hmodel hmarks hcharge
      have hbelow : CapsValidMuBelow mu caps g := fun g' hg' => ih g' hg' (by omega)
      have hall := List.all_eq_true.mp h g (by simp; omega)
      simp only [beq_iff_eq] at hall
      have := length_lt_of_fsearch_false caps g (caps.getD g 0 + 1) mu (caps.getD g 0 + 1) hbelow
        (by omega) (by omega) hall rows hmodel hmarks hcharge
      omega

/-- Level-by-level form: validity below `g` plus the failed search at `g` gives validity at `g`. -/
theorem capValidMu_step (caps : Array Nat) (mu g : Nat) (hbelow : CapsValidMuBelow mu caps g)
    (h : Fast.fsearch caps g (caps.getD g 0 + 1) mu (caps.getD g 0 + 1) = false) :
    CapValidMuAt mu caps g := by
  intro rows hmodel hmarks hcharge
  have := length_lt_of_fsearch_false caps g (caps.getD g 0 + 1) mu (caps.getD g 0 + 1) hbelow
    (by omega) (by omega) h rows hmodel hmarks hcharge
  omega

end Superperm7
