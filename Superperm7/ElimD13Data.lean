/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.Directs

/-! # Tabulated data for the defect-13 sweep (own precompiled module) -/

namespace Superperm7

/-- per-trail row cap for a trail of charge `≤ c` with at most `m` marked rows -/
def percapVal (c m : ℕ) : ℕ := min (baseCap c m) (directCap c m)

def percapTab : Array (Array ℕ) :=
  (Array.range 79).map fun c => (Array.range 14).map fun m => percapVal c m

def percapT (c m : ℕ) : ℕ := (percapTab.getD c #[]).getD m 0

/-- next layer of the convolution table `conv[u][b]` from the previous layer -/
def conv13Step (prev : Array (Array ℕ)) : Array (Array ℕ) :=
  (Array.range 79).map fun u => (Array.range 14).map fun b =>
    ((List.range (u + 1)).flatMap fun c => (List.range (b + 1)).map fun m =>
      percapT c m + (prev.getD (u - c) #[]).getD (b - m) 0).foldl max 0

/-- `conv13Tab[τ][u][b]` for `τ ≤ 14`, `u ≤ 78`, `b ≤ 13` -/
def conv13Tab : Array (Array (Array ℕ)) := Id.run do
  let zero : Array (Array ℕ) := (Array.range 79).map fun _ => Array.replicate 14 0
  let mut t : Array (Array (Array ℕ)) := #[zero]
  for _ in [0:14] do
    t := t.push (conv13Step t[t.size - 1]!)
  return t

def convF13 (τ u b : ℕ) : ℕ := ((conv13Tab.getD τ #[]).getD u #[]).getD b 0

def conv13Checked : Bool :=
  (List.range 14).all fun τ => (List.range 79).all fun u => (List.range 14).all fun b =>
    (List.range (u + 1)).all fun c => (List.range (b + 1)).all fun m =>
      decide (percapT c m + convF13 τ (u - c) (b - m) ≤ convF13 (τ + 1) u b)

/-- the nine equality cells `(m, b, η)` with `a = r = 0`, handled by template enumeration -/
def isEqualityCell (m a b eta r : ℕ) : Bool :=
  a == 0 && r == 0 && ((m == 10 && b + eta == 3) || (m == 11 && b + eta == 2) || (m == 12 && b + eta == 1))

def cellDead13 (m a b eta r : ℕ) : Bool :=
  convF13 (eta + 1 + b) (6 * m - r) b < 120 + m - r + a

def sweep13Checked : Bool :=
  (List.range 14).all fun m => (List.range 14).all fun a => (List.range 14).all fun b =>
    (List.range 14).all fun eta => (List.range 79).all fun r =>
      !(decide (m + a + b + eta ≤ 13) && decide (a ≤ r) && decide (r ≤ 6 * m)) ||
      isEqualityCell m a b eta r || cellDead13 m a b eta r

end Superperm7
