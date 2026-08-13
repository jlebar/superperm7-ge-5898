/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.Closure

/-! # Tabulated data for the elimination sweep (kept in its own precompiled module) -/

namespace Superperm7

def capWTab : Array ℕ := (Array.range 73).map capW

/-- next row of the convolution table from the previous row -/
def convStep (prev : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 73) fun u =>
    ((List.range (u.val + 1)).map fun u1 => capWTab.getD u1 0 + prev.getD (u.val - u1) 0).foldl max 0

/-- `convTab[τ][u] = F τ u` for `τ ≤ 25`, `u ≤ 72` -/
def convTab : Array (Array ℕ) := Id.run do
  let mut t : Array (Array ℕ) := #[Array.replicate 73 0]
  for _ in [0:25] do
    t := t.push (convStep t[t.size - 1]!)
  return t

def convF (τ u : ℕ) : ℕ := (convTab.getD τ #[]).getD u 0

/-- Boolean check of the defining inequality of the convolution on the range used. -/
def convChecked : Bool :=
  (List.range 13).all fun τ => (List.range 73).all fun u => (List.range (u + 1)).all fun u1 =>
    decide (capWTab.getD u1 0 + convF τ (u - u1) ≤ convF (τ + 1) u)

/-- The cell test: `F τ u < k` for the cell `(m, a, b, η, r)`. -/
def cellDead (m a b eta r : ℕ) : Bool :=
  convF (eta + 1 + b) (6 * m - r) < 120 + m - r + a

/-- Boolean sweep over all registry cells with defect at most twelve. -/
def sweepChecked : Bool :=
  (List.range 13).all fun m => (List.range 13).all fun a => (List.range 13).all fun b =>
    (List.range 13).all fun eta => (List.range 73).all fun r =>
      !(decide (m + a + b + eta ≤ 12) && decide (a ≤ r) && decide (r ≤ 6 * m)) || cellDead m a b eta r

end Superperm7
