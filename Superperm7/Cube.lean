/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.FastSearchSound

/-!
# Cube and conquer for the fast search

The failed-search certificates for the expensive charge budgets are split into
independent shards.  `frontier caps g target mu d` is the list of search
states reached after `d` rows (from the normalized first row); if every state
of the frontier fails `ffound`, so does `fsearch`.  Shards are contiguous
ranges of the frontier, each discharged by its own `native_decide`.
-/

namespace Superperm7

namespace Fast

/-- A search state (as passed to `ffound`). -/
structure SState where
  head : Nat
  cs : BitSet
  bs : BitSet
  rows : Nat
  holes : Nat
  marks : Nat

/-- the successors examined by `ffound` at a state -/
def expand (caps : Array Nat) (g target mu : Nat) (s : SState) : List SState :=
  (cands.getD s.head #[]).toList.filterMap fun c =>
    match tryCand caps g target mu s.cs s.bs s.rows s.holes s.marks c with
    | none => none
    | some holes' =>
        some { head := c.beta, cs := insertAll s.cs c, bs := s.bs.insert c.block,
               rows := s.rows + 1, holes := holes', marks := if c.marked then s.marks + 1 else s.marks }

/-- the root states: after the first (identity-start) row -/
def roots (caps : Array Nat) (g target mu : Nat) : List SState :=
  startCands.toList.filterMap fun c =>
    match tryCand caps g target mu emptyClasses emptyBlocks 0 0 0 c with
    | none => none
    | some holes' =>
        some { head := c.beta, cs := insertAll emptyClasses c, bs := emptyBlocks.insert c.block,
               rows := 1, holes := holes', marks := if c.marked then 1 else 0 }

/-- states after `d + 1` rows -/
def frontier (caps : Array Nat) (g target mu : Nat) : Nat → List SState
  | 0 => roots caps g target mu
  | d + 1 => (frontier caps g target mu d).flatMap (expand caps g target mu)

def runState (caps : Array Nat) (g target mu fuel : Nat) (s : SState) : Bool :=
  ffound caps g target mu fuel s.head s.cs s.bs s.rows s.holes s.marks

theorem ffound_succ_of_lt (caps : Array Nat) (g target mu fuel : Nat) (s : SState)
    (hlt : s.rows < target) :
    runState caps g target mu (fuel + 1) s = true →
      ∃ s' ∈ expand caps g target mu s, runState caps g target mu fuel s' = true := by
  intro h
  unfold runState ffound at h
  rw [if_neg (by omega)] at h
  rw [Array.any_eq_true] at h
  obtain ⟨i, hi, hci⟩ := h
  set c := (cands.getD s.head #[])[i] with hc
  cases htc : tryCand caps g target mu s.cs s.bs s.rows s.holes s.marks c with
  | none => rw [htc] at hci; exact absurd hci (by simp)
  | some holes' =>
      rw [htc] at hci
      refine ⟨{ head := c.beta, cs := insertAll s.cs c, bs := s.bs.insert c.block,
                rows := s.rows + 1, holes := holes',
                marks := if c.marked then s.marks + 1 else s.marks }, ?_, ?_⟩
      · unfold expand
        rw [List.mem_filterMap]
        refine ⟨c, ?_, by rw [htc]⟩
        rw [Array.mem_toList_iff]; exact Array.getElem_mem hi
      · simpa [runState] using hci

theorem roots_rows (caps : Array Nat) (g target mu : Nat) :
    ∀ s ∈ roots caps g target mu, s.rows = 1 := by
  intro s hs
  unfold roots at hs
  rw [List.mem_filterMap] at hs
  obtain ⟨c, _, hc⟩ := hs
  split at hc
  · simp at hc
  · simp only [Option.some.injEq] at hc; rw [← hc]

theorem expand_rows (caps : Array Nat) (g target mu : Nat) (s : SState) :
    ∀ s' ∈ expand caps g target mu s, s'.rows = s.rows + 1 := by
  intro s' hs'
  unfold expand at hs'
  rw [List.mem_filterMap] at hs'
  obtain ⟨c, _, hc⟩ := hs'
  split at hc
  · simp at hc
  · simp only [Option.some.injEq] at hc; rw [← hc]

theorem frontier_rows (caps : Array Nat) (g target mu : Nat) :
    ∀ d, ∀ s ∈ frontier caps g target mu d, s.rows = d + 1
  | 0 => roots_rows caps g target mu
  | d + 1 => by
      intro s hs
      unfold frontier at hs
      rw [List.mem_flatMap] at hs
      obtain ⟨s0, hs0, hs⟩ := hs
      rw [expand_rows caps g target mu s0 s hs, frontier_rows caps g target mu d s0 hs0]

/-- If the search succeeds with fuel `fuel + d`, some frontier state at depth
`d` succeeds with fuel `fuel` (provided the target is beyond depth `d`). -/
theorem frontier_complete (caps : Array Nat) (g target mu fuel : Nat) :
    ∀ d, d + 1 < target →
      fsearch caps g target mu (fuel + d) = true →
        ∃ s ∈ frontier caps g target mu d, runState caps g target mu fuel s = true
  | 0 => by
      intro _ h
      unfold fsearch at h
      rw [Array.any_eq_true] at h
      obtain ⟨i, hi, hci⟩ := h
      set c := startCands[i] with hc
      cases htc : tryCand caps g target mu emptyClasses emptyBlocks 0 0 0 c with
      | none => rw [htc] at hci; exact absurd hci (by simp)
      | some holes' =>
          rw [htc] at hci
          refine ⟨{ head := c.beta, cs := insertAll emptyClasses c, bs := emptyBlocks.insert c.block,
                    rows := 1, holes := holes', marks := if c.marked then 1 else 0 }, ?_, ?_⟩
          · unfold frontier roots
            rw [List.mem_filterMap]
            refine ⟨c, ?_, by rw [htc]⟩
            rw [Array.mem_toList_iff]; exact Array.getElem_mem hi
          · simpa [runState] using hci
  | d + 1 => by
      intro hd h
      rw [show fuel + (d + 1) = (fuel + 1) + d by omega] at h
      obtain ⟨s, hs, hrun⟩ := frontier_complete caps g target mu (fuel + 1) d (by omega) h
      have hrows := frontier_rows caps g target mu d s hs
      obtain ⟨s', hs', hrun'⟩ := ffound_succ_of_lt caps g target mu fuel s (by omega) hrun
      refine ⟨s', ?_, hrun'⟩
      unfold frontier
      rw [List.mem_flatMap]
      exact ⟨s, hs, hs'⟩

/-- Boolean shard check: states `a … a+n-1` of the depth-`d` frontier all fail with fuel `fuel`. -/
def shardOK (caps : Array Nat) (g target mu d fuel a n : Nat) : Bool :=
  (((frontier caps g target mu d).drop a).take n).all fun s => !(runState caps g target mu fuel s)

/-- covering by consecutive shards of length `n` starting at `0` -/
theorem all_of_shards {α : Type} (l : List α) (p : α → Bool) (n k : ℕ) (hn : 0 < n)
    (hcover : l.length ≤ n * k)
    (h : ∀ i < k, ((l.drop (n * i)).take n).all p = true) : l.all p = true := by
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have hi : j / n < k := by
    apply Nat.div_lt_of_lt_mul
    calc j < l.length := hj
      _ ≤ n * k := hcover
  have := h (j / n) hi
  rw [List.all_eq_true] at this
  apply this
  rw [List.mem_take_iff_getElem]
  refine ⟨j % n, ?_, ?_⟩
  · simp only [List.length_drop]
    have := Nat.mod_lt j hn
    have : n * (j / n) + j % n = j := Nat.div_add_mod j n
    omega
  · rw [List.getElem_drop]
    congr 1
    exact Nat.div_add_mod j n

/-- The sharded certificate: if the depth-`d` frontier is covered by `k`
shards of length `n`, each failing with fuel `fuel`, then the search with fuel
`fuel + d` fails. -/
theorem fsearch_false_of_shards (caps : Array Nat) (g target mu d fuel n k : Nat)
    (hd : d + 1 < target) (hn : 0 < n)
    (hcover : (frontier caps g target mu d).length ≤ n * k)
    (h : ∀ i < k, shardOK caps g target mu d fuel (n * i) n = true) :
    fsearch caps g target mu (fuel + d) = false := by
  by_contra hne
  rw [Bool.not_eq_false] at hne
  obtain ⟨s, hs, hrun⟩ := frontier_complete caps g target mu fuel d hd hne
  have hall := all_of_shards (frontier caps g target mu d) (fun s => !(runState caps g target mu fuel s))
    n k hn hcover h
  rw [List.all_eq_true] at hall
  have := hall s hs
  rw [hrun] at this
  exact Bool.false_ne_true (by simpa using this)

end Fast

end Superperm7
