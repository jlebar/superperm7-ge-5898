/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.Search

/-!
# A faster reflected search kernel (byte-array bitsets, packed candidates, mark budget)

Same search as `Search.lean` — depth-first over model marked trails from a
normalized first row, with suffix-cap pruning — but engineered for throughput:
used classes / used blocks are `ByteArray` bitsets, each candidate row carries
its (at most six) visible class ids packed in one machine word, and a budget
`mu` bounds the number of marked rows on the trail.
Completeness is proved in `FastSearchSound.lean`.
-/

namespace Superperm7

open Mirror

/-! ## Persistent bitsets over `ByteArray` -/

structure BitSet where
  data : ByteArray

namespace BitSet

def empty (nbytes : Nat) : BitSet := ⟨⟨Array.replicate nbytes 0⟩⟩

@[inline] def contains (s : BitSet) (i : Nat) : Bool :=
  (s.data.get! (i >>> 3) &&& ((1 : UInt8) <<< (i &&& 7).toUInt8)) != 0

@[inline] def insert (s : BitSet) (i : Nat) : BitSet :=
  let k := i >>> 3
  ⟨s.data.set! k (s.data.get! k ||| ((1 : UInt8) <<< (i &&& 7).toUInt8))⟩

end BitSet

/-! ## Candidate rows -/

/-- A candidate row: block id, packed visible class ids (`cnt` ids, 10 bits
each), head id of the tail, charge, and whether it is marked. -/
structure Cand where
  block : Nat
  packed : Nat
  cnt : Nat
  beta : Nat
  charge : Nat
  marked : Bool
  deriving DecidableEq, Repr

namespace Cand

/-- the `j`-th visible class id -/
@[inline] def cls (c : Cand) (j : Nat) : Nat := (c.packed >>> (10 * j)) &&& 1023

/-- the list of visible class ids (specification-level) -/
def clsList (c : Cand) : List Nat := (List.range c.cnt).map c.cls

end Cand

def packIds : List Nat → Nat
  | [] => 0
  | c :: cs => c + (packIds cs <<< 10)

/-- word-level tail tuple of the row of length `L+1` at `w`: symbols 2..5 of `F^L w` -/
def tailTupleW (w : W) (L : Nat) : W := ((iter rotF L w).drop 2).take 4

/-- the candidate for start word `w`, length code `L`, omission bits `om`
(pure word arithmetic; agreement with the model is proved in `FastSearchSound`) -/
def mkCandW (w : W) (L : Nat) (om : Nat) : Cand :=
  let len := L + 1
  let ids := ((List.range len).filter fun j => !(om.testBit j)).map
    fun j => classId (iter rotF j w)
  { block := blockId w
    packed := packIds ids
    cnt := ids.length
    beta := headIdOfTuple (tailTupleW w L)
    charge := 6 - ids.length
    marked := om != 0 }

/-- the same, phrased on a permutation (used only in statements/proofs) -/
def mkCand (p : Perm7) (L : Fin 6) (om : Nat) : Cand := mkCandW (permWord p) L.val om

def headIdW (w : W) : Nat := headIdOfTuple (w.take 4)

/-- omission bit patterns allowed for length code `L` (as in `Search.lean`, on `Nat`) -/
def allowedOmissionBitsN (L : Nat) : List Nat :=
  (List.range (2 ^ 6)).filter fun om =>
    (List.range 6).all fun j => !(om.testBit j) || (0 < j ∧ j + 1 < L + 1)

/-- `cands[h]` = all candidates whose start has head id `h` -/
def cands : Array (Array Cand) := Id.run do
  let mut t : Array (Array Cand) := Array.replicate 840 #[]
  for w in allWords do
    let h := headIdW w
    for L in [0:6] do
      for om in allowedOmissionBitsN L do
        t := t.set! h (t[h]!.push (mkCandW w L om))
  return t

def idWord : W := List.finRange 7

/-- candidates starting at the identity word -/
def startCands : Array Cand :=
  ((List.range 6).flatMap fun L => (allowedOmissionBitsN L).map fun om => mkCandW idWord L om).toArray

/-! ## The search -/

namespace Fast

/-- are all visible classes of `c` free? -/
def freeAux (cs : BitSet) (c : Cand) : Nat → Bool
  | 0 => true
  | j + 1 => !(cs.contains (c.cls j)) && freeAux cs c j

@[inline] def free (cs : BitSet) (c : Cand) : Bool := freeAux cs c c.cnt

def insertAux (cs : BitSet) (c : Cand) : Nat → BitSet
  | 0 => cs
  | j + 1 => (insertAux cs c j).insert (c.cls j)

@[inline] def insertAll (cs : BitSet) (c : Cand) : BitSet := insertAux cs c c.cnt

/-- suffix-cap admission test; returns the new charge -/
@[inline] def admit (caps : Array Nat) (g target rows holes ch : Nat) : Option Nat :=
  let holes' := holes + ch
  if g < holes' then none
  else
    let rem := g - holes'
    let sfx := if rem < g then caps.getD rem target else target
    if rows + 1 + sfx < target then none else some holes'

/-- can candidate `c` be appended to the state? if so, the new charge -/
@[inline] def tryCand (caps : Array Nat) (g target mu : Nat) (cs bs : BitSet)
    (rows holes marks : Nat) (c : Cand) : Option Nat :=
  if c.marked && mu ≤ marks then none
  else if bs.contains c.block then none
  else if !(free cs c) then none
  else admit caps g target rows holes c.charge

/-- depth-first search from a state -/
def ffound (caps : Array Nat) (g target mu : Nat) :
    Nat → Nat → BitSet → BitSet → Nat → Nat → Nat → Bool
  | 0, _, _, _, _, _, _ => true
  | fuel + 1, head, cs, bs, rows, holes, marks =>
      if target ≤ rows then true
      else
        (cands.getD head #[]).any fun c =>
          match tryCand caps g target mu cs bs rows holes marks c with
          | none => false
          | some holes' =>
              ffound caps g target mu fuel c.beta (insertAll cs c) (bs.insert c.block)
                (rows + 1) holes' (if c.marked then marks + 1 else marks)

def emptyClasses : BitSet := BitSet.empty 90
def emptyBlocks : BitSet := BitSet.empty 105

/-- search over trails whose first row starts at the identity permutation -/
def fsearch (caps : Array Nat) (g target mu fuel : Nat) : Bool :=
  startCands.any fun c =>
    match tryCand caps g target mu emptyClasses emptyBlocks 0 0 0 c with
    | none => false
    | some holes' =>
        ffound caps g target mu fuel c.beta (insertAll emptyClasses c) (emptyBlocks.insert c.block)
          1 holes' (if c.marked then 1 else 0)

end Fast

end Superperm7
