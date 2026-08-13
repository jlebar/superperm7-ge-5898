/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE); this file is
additionally subject to the upstream MIT notice below.

Adapted from https://github.com/BGray-wrl/superperm6
  file:   formal-verification/Superperm6/Frontier.lean
  commit: d8a932d8f61d80b0bcfc737bd0e235a8300449c4
  upstream copyright: Copyright (c) 2026 Benjamin Grayzel — MIT License (reproduced in NOTICE).
Local modifications (port from six to seven symbols; see docs/PORT_LOG.md): the frontier lift and profile counts were dropped; only the loss/defect arithmetic used downstream is kept, with seven-symbol constants.
-/
import Superperm7.Basic

/-!
# Cheap-cover and orbit arithmetic (n = 7)

The numerical parts of Sections 2--4 that the reduction consumes.  At
`n = 7` there is no frontier lift: the defect is bounded (`≤ 13`) rather
than pinned, so only the orbit inequality and the capped-length identity
survive from the `n = 6` file; the documentary profile counts are dropped.
-/

namespace Superperm7

/-- `ceil (r / 6)` for a natural number `r`. -/
def ceilDivSix (r : ℕ) : ℕ := (r + 5) / 6

/-- The arithmetic core of the orbit inequality (3.2). -/
theorem orbit_inequality_of_counts {r q M k : ℕ}
    (selected_fit : 720 + r ≤ 6 * M)
    (quotient_rank : M ≤ r + k)
    (components_le_chains : k ≤ q) :
    120 + ceilDivSix r ≤ r + q := by
  simp only [ceilDivSix]
  omega

/-- Equations (2.3)--(2.4), with every natural subtraction guarded by the
corresponding combinatorial inequality. -/
theorem capped_length_identity {r q p : ℕ}
    (hr : r ≤ 4320) (hq : q ≤ 720 + r) (hp : p ≤ q) (hp1 : 1 ≤ p) :
    7 + (4320 - r) + 2 * (720 + r - q) + 3 * (q - p) + 4 * (p - 1) =
      5763 + r + q + p := by
  omega

theorem capped_at_most_5897_iff_loss {r q p : ℕ} :
    5763 + r + q + p ≤ 5897 ↔ 720 + r + q + p ≤ 854 := by
  omega

theorem loss_at_most_854_iff {r q p : ℕ} :
    720 + r + q + p ≤ 854 ↔ r + q + p ≤ 134 := by
  omega

/-- Algebra behind the defect: `r + q + p = 121 + D` once `r ≤ 120 + m`. -/
theorem defect_identity {r q p m a b eta k : ℕ}
    (hk : k = 120 + m - r + a)
    (hq : q = k + b)
    (hp : p = eta + 1)
    (hr : r ≤ 120 + m) :
    r + q + p = 121 + (m + a + b + eta) := by
  omega

/-- Algebra behind the defect bound `D ≤ 13`. -/
theorem defect_bound_identity {r q p m a b eta k : ℕ}
    (hk : k = 120 + m - r + a)
    (hq : q = k + b)
    (hp : p = eta + 1)
    (hbudget : r + q + p ≤ 134)
    (hr : r ≤ 120 + m) :
    m + a + b + eta ≤ 13 := by
  omega

/-- Algebraic consequence of the Euler face count and the definition of
`h`; this is equation (4.8), conditional on those two structural inputs. -/
theorem face_fragmentation_identity {q k a b g h cT : ℕ}
    (hq : q = k + b)
    (hfaces : cT = k + a - 2 * g)
    (hgenus : 2 * g ≤ k + a)
    (hga : 2 * g ≤ a)
    (hh : h = q - cT)
    (hc : cT ≤ q) : b = a - 2 * g + h := by
  omega

end Superperm7
