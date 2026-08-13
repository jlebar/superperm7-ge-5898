/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.CapTabs

namespace Superperm7.Cert.M2

/-- levels 38..40: each failed search, checked in one batch -/
theorem chk_38_40 : ((List.range (40 + 1)).drop 38).all (fun g =>
    Fast.fsearch capTab2 g (capTab2.getD g 0 + 1) 2 (capTab2.getD g 0 + 1) == false) = true := by
  native_decide

theorem lvl_of_batch_38_40 (g : ℕ) (ha : 38 ≤ g) (hb : g ≤ 40) :
    Fast.fsearch capTab2 g (capTab2.getD g 0 + 1) 2 (capTab2.getD g 0 + 1) = false := by
  have h := chk_38_40
  rw [List.all_eq_true] at h
  have := h g (by rw [List.mem_iff_getElem]; refine ⟨g - 38, by simp; omega, ?_⟩; simp [List.getElem_drop]; try omega)
  simpa using this

end Superperm7.Cert.M2
