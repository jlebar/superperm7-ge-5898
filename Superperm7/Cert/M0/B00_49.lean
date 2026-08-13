/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CapTabs

namespace Superperm7.Cert.M0

/-- levels 0..49: each failed search, checked in one batch -/
theorem chk_0_49 : ((List.range (49 + 1)).drop 0).all (fun g =>
    Fast.fsearch capTab0 g (capTab0.getD g 0 + 1) 0 (capTab0.getD g 0 + 1) == false) = true := by
  native_decide

theorem lvl_of_batch_0_49 (g : ℕ) (ha : 0 ≤ g) (hb : g ≤ 49) :
    Fast.fsearch capTab0 g (capTab0.getD g 0 + 1) 0 (capTab0.getD g 0 + 1) = false := by
  have h := chk_0_49
  rw [List.all_eq_true] at h
  have := h g (by rw [List.mem_iff_getElem]; refine ⟨g - 0, by simp; omega, ?_⟩; simp [List.getElem_drop]; try omega)
  simpa using this

end Superperm7.Cert.M0
