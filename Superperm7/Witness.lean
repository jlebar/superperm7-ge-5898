/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE); this file is
additionally subject to the upstream MIT notice below.

Adapted from https://github.com/BGray-wrl/superperm6
  file:   formal-verification/Superperm6/Witness.lean
  commit: d8a932d8f61d80b0bcfc737bd0e235a8300449c4
  upstream copyright: Copyright (c) 2026 Benjamin Grayzel — MIT License (reproduced in NOTICE).
Local modifications (port from six to seven symbols; see docs/PORT_LOG.md): reads and checks the 5906-symbol seven-symbol word instead of the 872-symbol six-symbol word.
-/
import Superperm7.Basic

/-!
# An explicit length-5906 superpermutation on seven symbols

The witness — one of the length-5906 words found by Greg Egan and Robin Houston in February 2019,
as published on Egan's superpermutations page and in the public Superpermutators corpus
(`7_5906_nsk666646664466646666_2SYMM_FS.txt`) — is read at elaboration time from
`data/superperm7_5906.txt` and checked with Lean's native evaluator.  It gives the upper bound
`s(7) ≤ 5906`; it is not new and is included only so that the final statement is two-sided.
-/

namespace Superperm7

def witnessText : String :=
  include_str ".." / "data" / "superperm7_5906.txt"

def digit? : Char → Option Symbol
  | '1' => some 0
  | '2' => some 1
  | '3' => some 2
  | '4' => some 3
  | '5' => some 4
  | '6' => some 5
  | '7' => some 6
  | _ => none

def witness : Word := witnessText.toList.filterMap digit?

theorem witness_length : witness.length = 5906 := by native_decide

set_option maxHeartbeats 0 in
theorem witness_isSuperpermutation : IsSuperpermutation witness := by
  native_decide

theorem verified_upper_bound :
    ∃ w : Word, IsSuperpermutation w ∧ w.length = 5906 :=
  ⟨witness, witness_isSuperpermutation, witness_length⟩

end Superperm7
