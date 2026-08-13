/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE); this file is
additionally subject to the upstream MIT notice below.

Adapted from https://github.com/BGray-wrl/superperm6
  file:   formal-verification/Superperm6/Registry.lean
  commit: d8a932d8f61d80b0bcfc737bd0e235a8300449c4
  upstream copyright: Copyright (c) 2026 Benjamin Grayzel — MIT License (reproduced in NOTICE).
Local modifications (port from six to seven symbols; see docs/PORT_LOG.md): the published n = 6 family list is replaced by the parametric RegistryCandidate (m, a, b, eta, r) with defect budget 13.
-/
import Superperm7.Frontier

/-!
# The bounded-defect structural registry (n = 7)

At `n = 7` a light route (`routeWeight ≤ 5890`, i.e. words of length at most
`5897`) has defect `D = m + a + b + η ≤ 13`.  There is no frontier lift, so
the registry is the set of all `(m, a, b, η, r)` with `D ≤ 13`, `a ≤ r ≤ 6m`
and `r = 0` when `m = 0`.  The Euler face-fragmentation data `(g, h)` of the
`n = 6` registry is not recorded in the candidate (it is still proved, in
`Section4.lean`, but the capacity elimination does not use it).
-/

namespace Superperm7

/-- The registry parameters realized by a light normalized route. -/
structure RegistryCandidate where
  m : ℕ
  a : ℕ
  b : ℕ
  eta : ℕ
  r : ℕ
  deriving DecidableEq, Repr

namespace RegistryCandidate

def valid (c : RegistryCandidate) : Prop :=
  c.m + c.a + c.b + c.eta ≤ 13 ∧ c.a ≤ c.r ∧ c.r ≤ 6 * c.m ∧ (c.m = 0 → c.r = 0)

instance (c : RegistryCandidate) : Decidable c.valid := by
  unfold valid
  infer_instance

/-- Number of component rows `k = 120 + m - r + a`. -/
def k (c : RegistryCandidate) : ℕ := 120 + c.m - c.r + c.a

/-- Trail budget `τ = η + 1 + b`. -/
def tau (c : RegistryCandidate) : ℕ := c.eta + 1 + c.b

/-- Hole budget `u = 6m - r`. -/
def u (c : RegistryCandidate) : ℕ := 6 * c.m - c.r

theorem r_le_of_valid {c : RegistryCandidate} (hc : c.valid) : c.r ≤ 120 + c.m := by
  rcases hc with ⟨hD, _, hr, _⟩
  omega

end RegistryCandidate

/-- Hole, component, chain, and path formulas (4.2), checked purely as
integer algebra under the definitions of `m,a,b,eta`. -/
theorem registry_parameter_formulas {M r k q p m a b eta : ℕ}
    (hM : M = 120 + m)
    (ha : r = M - k + a)
    (hrank : k ≤ M)
    (hrM : r ≤ M)
    (hq : q = k + b)
    (hp : p = eta + 1) :
    6 * M - (720 + r) = 6 * m - r ∧
    k = 120 + m - r + a ∧
    q = (120 + m - r + a) + b ∧
    p = eta + 1 := by
  omega

end Superperm7
