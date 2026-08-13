/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.Coarsen

/-!
# Reflected single-trail search with capacity pruning

A `MarkedRow` is reflected into a numeric mirror record carrying its
insertion-block id, the bitmask of rotation-class ids of its visible positions,
the head id of its tail tuple, and its charge.  All mirror rows (honest and
marked, all starts, all lengths) are precomputed into buckets indexed by the
head id of the start.  The search `found` is a depth-first enumeration of
mirror trails from a state (current head id, used blocks, used classes, rows,
charge) with the *suffix bound* pruning

  rows(prefix) + 1 + caps[g - charge] < target   ⇒   prune,

which is sound whenever `caps[g']` bounds the length of every model trail of
charge `≤ g'` for `g' < g`.  Completeness (`found = false` refutes every model
trail) is proved in `SearchSound.lean`; this file is data and programs only.
-/

namespace Superperm7

/-! ## Word codes and id tables -/

namespace Mirror

abbrev W := List (Fin 7)

def wcode (w : W) : Nat := w.foldl (fun acc a => acc * 8 + a.val) 0

def allWords : List W := (List.finRange 7).permutations

def rotL7 : W → W
  | a :: t => t ++ [a]
  | [] => []

def rotF : W → W
  | [a, b, c, d, e, f, z] => [b, c, d, e, f, a, z]
  | w => w

def iter (f : W → W) : Nat → W → W
  | 0, w => w
  | k + 1, w => iter f k (f w)

def classCode (w : W) : Nat :=
  ((List.range 7).map fun k => wcode (iter rotL7 k w)).foldl min (8 ^ 7)

def blockCode (w : W) : Nat :=
  ((List.range 6).map fun k => wcode (iter rotF k w)).foldl min (8 ^ 7)

/-- sorted distinct codes; the id of a code is its index -/
def classReps : Array Nat := ((allWords.map classCode).dedup.mergeSort).toArray
def blockReps : Array Nat := ((allWords.map blockCode).dedup.mergeSort).toArray
def headReps : Array Nat := ((allWords.map fun w => wcode (w.take 4)).dedup.mergeSort).toArray

def invTab (reps : Array Nat) : Array Nat := Id.run do
  let mut t : Array Nat := Array.replicate (8 ^ 7) 0
  for i in [0:reps.size] do
    t := t.set! reps[i]! i
  return t

def classInv : Array Nat := invTab classReps
def blockInv : Array Nat := invTab blockReps
def headInv : Array Nat := invTab headReps

def classId (w : W) : Nat := classInv[classCode w]!
def blockId (w : W) : Nat := blockInv[blockCode w]!
def headIdOfTuple (t : W) : Nat := headInv[wcode t]!

end Mirror

open Mirror

/-! ## Mirror rows -/

/-- Numeric mirror of a marked row. -/
structure MRow where
  block : Nat
  visible : Nat     -- bitmask over class ids (< 720)
  beta : Nat        -- head id of the tail tuple
  charge : Nat
  deriving DecidableEq, Repr

/-- bitmask of the omitted positions -/
def omittedBits (s : Finset (Fin 6)) : Nat :=
  s.sum fun i => 2 ^ i.val

def bitMask : List Nat → Nat
  | [] => 0
  | c :: cs => (1 <<< c) ||| bitMask cs

/-- the mirror of the marked row with start `p`, length code `L`, omission bits `om` -/
def mkMirror (p : Perm7) (L : Fin 6) (om : Nat) : MRow :=
  let w := permWord p
  let len := L.val + 1
  let visIds := ((List.range len).filter fun j => !(om.testBit j)).map
    fun j => classId (permWord ((F^[j]) p))
  { block := blockId w
    visible := bitMask visIds
    beta := headIdOfTuple ((rowOfLength p L).beta)
    charge := (6 - len) + ((List.range 6).filter fun j => om.testBit j).length }

def encode (x : MarkedRow) : MRow := mkMirror x.row.start x.row.lengthCode (omittedBits x.omitted)

def headId (p : Perm7) : Nat := headIdOfTuple (alpha p)

/-- omission bitmasks allowed for a row of length code `L`: subsets of the
strictly interior positions `1 … L-1` (length `L+1`, last position `L`). -/
def allowedOmissionBits (L : Fin 6) : List Nat :=
  (List.range (2 ^ 6)).filter fun om =>
    (List.range 6).all fun j => !(om.testBit j) || (0 < j ∧ j + 1 < L.val + 1)

/-! ## Buckets -/

/-- Decode a word to a permutation (identity on non-permutation words). -/
def wordToPerm (w : W) : Perm7 :=
  if h : w.Perm (List.finRange 7) then
    let hlen : w.length = 7 := by simpa using h.length_eq
    let hnd : w.Nodup := h.nodup_iff.mpr (List.nodup_finRange 7)
    let hall : ∀ x : Fin 7, x ∈ w := by
      intro x
      exact h.mem_iff.mpr (by simp)
    (finCongr hlen).symm.trans (hnd.getEquivOfForallMemList w hall)
  else
    1

def allPermsList : List Perm7 := allWords.map wordToPerm

/-- `buckets[h]` = all mirror rows (honest and marked) whose start has head id `h`,
each paired with a flag `marked`. -/
def buckets : Array (List (MRow × Bool)) := Id.run do
  let mut t : Array (List (MRow × Bool)) := Array.replicate 840 []
  for p in allPermsList do
    let h := headId p
    for L in List.finRange 6 do
      for om in allowedOmissionBits L do
        let r := mkMirror p L om
        t := t.set! h ((r, om != 0) :: t[h]!)
  return t

/-- rows starting at the identity permutation -/
def startRows : List (MRow × Bool) :=
  (List.finRange 6).flatMap fun L =>
    (allowedOmissionBits L).map fun om => (mkMirror 1 L om, om != 0)

/-! ## The search -/

def blockBit (r : MRow) : Nat := 1 <<< r.block

/-- Try to append mirror row `r` to a prefix with `rows` rows and charge
`holes`; returns the new charge if it passes the budget and the suffix-cap
pruning against `target`. -/
def admit (caps : Array Nat) (g target rows holes : Nat) (r : MRow) : Option Nat :=
  let holes' := holes + r.charge
  if g < holes' then none
  else
    let rem := g - holes'
    let sfx := if rem < g then caps.getD rem target else target
    if rows + 1 + sfx < target then none else some holes'

/-- Depth-first search: is there a mirror-trail continuation reaching `target` rows? -/
def found (caps : Array Nat) (g target : Nat) (allowMarks : Bool) :
    Nat → Nat → Nat → Nat → Nat → Nat → Bool
  | 0, _, _, _, _, _ => true
  | fuel + 1, head, usedBlocks, usedClasses, rows, holes =>
    if target ≤ rows then true
    else
      (buckets.getD head []).any fun (r, marked) =>
        (allowMarks || !marked) &&
        ((usedBlocks &&& blockBit r) == 0) &&
        ((usedClasses &&& r.visible) == 0) &&
        match admit caps g target rows holes r with
        | none => false
        | some holes' =>
          found caps g target allowMarks fuel r.beta
            (usedBlocks ||| blockBit r) (usedClasses ||| r.visible) (rows + 1) holes'

/-- Search over trails whose first row starts at the identity permutation. -/
def search (caps : Array Nat) (g target : Nat) (allowMarks : Bool) (fuel : Nat) : Bool :=
  startRows.any fun (r, marked) =>
    (allowMarks || !marked) &&
    match admit caps g target 0 0 r with
    | none => false
    | some holes' => found caps g target allowMarks fuel r.beta (blockBit r) r.visible 1 holes'

end Superperm7
