import Solution

/-! Axiom audit of the three challenge statements as proved in `Solution.lean`.
Expected: `propext`, `Classical.choice`, `Quot.sound`, and `native_decide` evaluation certificates
(`Superperm7.…._native.native_decide.ax_…`, plus `Lean.ofReduceBool`/`Lean.trustCompiler` on toolchains
that report them); no `sorryAx`. -/

#print axioms superperm7_upper_5906
#print axioms superperm7_lower_5897
#print axioms superperm7_lower_5898
