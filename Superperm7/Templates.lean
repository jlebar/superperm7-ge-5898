/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.FastEnum
import Superperm7.ElimD13Data
/-!
# Templates: the optimal trails at the five tight charges, and their decoding

For `g ∈ {14, 16, 26, 34, 36}` the optimal row count `M(g) ∈ {31, 34, 50, 63, 66}`
is attained by very few normalized model trails (3, 3, 2, 2, 4 respectively,
none of them marked, although up to three marked rows are allowed in the
enumeration).  They are enumerated by `Fast.fenum` (complete by
`fenum_complete`) and decoded back to `List MarkedRow`.
-/

namespace Superperm7

open Mirror

/-! ## Decoding provenance -/

/-- the word with a given base-8 code, if it is one of the 5040 permutation words -/
def wordOfCode (c : Nat) : W :=
  match allWords.find? (fun w => wcode w == c) with
  | some w => w
  | none => idWord

def bitsFinset (m : Nat) : Finset (Fin 6) := Finset.univ.filter fun i => m.testBit i.val

def decodeProv (p : Prov) : MarkedRow :=
  { row := { start := wordToPerm (wordOfCode p.wc), lengthCode := ⟨p.lc % 6, Nat.mod_lt _ (by omega)⟩ }
    omitted := bitsFinset p.om }

theorem wordToPerm_permWord : ∀ p : Perm7, wordToPerm (permWord p) = p := by native_decide

theorem wordOfCode_wcode : ∀ p : Perm7, wordOfCode (wcode (permWord p)) = permWord p := by native_decide

theorem bitsFinset_omittedBits (s : Finset (Fin 6)) : bitsFinset (omittedBits s) = s := by
  revert s; decide

theorem decodeProv_prov (x : MarkedRow) : decodeProv (prov x) = x := by
  rcases x with ⟨⟨p, L⟩, s⟩
  unfold decodeProv prov
  simp only
  congr
  · rw [wordOfCode_wcode, wordToPerm_permWord]
  · exact Nat.mod_eq_of_lt L.isLt
  · exact bitsFinset_omittedBits s

theorem decode_map_prov (rows : List MarkedRow) : (rows.map prov).map decodeProv = rows := by
  rw [List.map_map]
  conv_rhs => rw [← List.map_id rows]
  apply List.map_congr_left
  intro x _
  exact decodeProv_prov x

/-! ## The template lists -/

/-- pruning caps for enumeration at charge `g` with up to three marks -/
def ecaps (g : ℕ) : Array ℕ := (Array.range g).map fun c => percapVal c 3

/-- optimal length at the template charges -/
def optLen (g : ℕ) : ℕ := percapVal g 0

/-- the enumerated templates (provenance lists), decoded -/
def templates (g : ℕ) : List (List MarkedRow) :=
  (Fast.fenum (ecaps g) g (optLen g) 3 (optLen g)).map fun t => t.map decodeProv

set_option maxRecDepth 4000 in
theorem templates_count :
    (templates 14).length = 3 ∧ (templates 16).length = 3 ∧ (templates 26).length = 2 ∧
    (templates 34).length = 2 ∧ (templates 36).length = 4 := by
  native_decide

section
variable (h0 : ∀ g ≤ 56, CapValidMuAt 0 capTab0 g)
  (h1 : ∀ g ≤ 54, CapValidMuAt 1 capTab1 g)
  (h2 : ∀ g ≤ 46, CapValidMuAt 2 capTab2 g)
include h0 h1 h2

omit h0 h1 h2 in
theorem ecaps_getD (g c : ℕ) (hc : c < g) : (ecaps g).getD c 0 = percapVal c 3 := by
  simp [ecaps, Array.getD, hc]

theorem ecaps_validBelow (g : ℕ) : CapsValidMuBelow 3 (ecaps g) g := by
  intro c hc rows hmodel hm hcharge
  rw [ecaps_getD g c hc]
  unfold percapVal
  exact le_min (length_le_baseCap h0 h1 h2 rows hmodel c 3 hcharge hm)
    (length_le_directCap h0 h1 h2 rows hmodel c 3 hcharge hm)

/-- **Template completeness.** A normalized model trail with at most three
marked rows, charge `≤ g`, and exactly `optLen g` rows is one of `templates g`. -/
theorem mem_templates (g : ℕ) (hg : 0 < optLen g) (rows : List MarkedRow) (hmodel : ModelTrail rows)
    (hmarks : markCount rows ≤ 3) (hfirst : ∀ x, rows.head? = some x → x.row.start = 1)
    (hcharge : chargeSum rows ≤ g) (hlen : rows.length = optLen g) :
    rows ∈ templates g := by
  have hmem := fenum_complete (ecaps g) g (optLen g) 3 (optLen g) (ecaps_validBelow h0 h1 h2 g)
    rows hmodel hmarks hfirst hcharge hlen.symm hg (by omega)
  unfold templates
  rw [List.mem_map]
  exact ⟨rows.map prov, hmem, decode_map_prov rows⟩

end

end Superperm7
