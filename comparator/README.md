# Statement layer / independent checking with `leanprover/comparator`

This directory isolates *what* is proved from *how*.  It follows the layout expected by
[comparator](https://github.com/leanprover/comparator), the Lean FRO's trusted-verification tool, which
builds a trusted challenge module and an untrusted solution module in a sandbox, checks that the solution
proves **exactly** the challenge statements, checks which axioms the proofs use, and replays the proofs
through the Lean kernel.

| file | role | trusted? |
|---|---|---|
| `ChallengeDeps.lean` | `Symbol := Fin 7`, `Perm7`, `Word`, `permWord`, `Occurs`, `IsSuperpermutation` — a 29-line file, Mathlib only | yes — read it |
| `Challenge.lean` | the three statements (`∃ w, IsSuperpermutation w ∧ w.length = 5906`; `∀ w, IsSuperpermutation w → 5897 ≤ w.length`; the same with `5898`), proofs `sorry` | yes — read it |
| `Solution.lean` | the same statements proved by delegating to `Superperm7.verified_upper_bound`, `Superperm7.lower_bound_5897`, `Superperm7.lower_bound` | no (checked) |
| `PrintAxioms.lean` | `#print axioms` of the three solution theorems — the quick check | — |
| `config.json` | comparator configuration (the three theorem names; permitted axioms = the standard ones) | yes |
| `native_decide_certificates.txt` | the 382 evaluation-certificate names the solution additionally depends on (documentation; see below) | — |

What a skeptical reader has to trust to know *what* is claimed: Mathlib's `Equiv.Perm`, `List.ofFn`,
`List.IsInfix` (`<:+:`) and `List.length`; the two trusted files; the Lean kernel.  Nothing under
`Superperm7/` needs to be read for that.

## Quick check

```sh
lake build Solution
lake env lean comparator/PrintAxioms.lean
```

Each of the three lines printed must list `propext`, `Classical.choice`, `Quot.sound` and otherwise only
names of the form `Superperm7.<decl>._native.native_decide.ax_<i>_<j>` (the evaluation certificates,
listed in `native_decide_certificates.txt`), and in particular no `sorryAx`.  `../AUDIT.md` records the output at this commit.

## About `native_decide`, and what a comparator run can and cannot do here

Unlike a purely deductive development, this proof discharges its finite computations (capacity tables,
optimal-trail enumerations, join checks, the witness check) with `native_decide`: Lean compiles the
decision procedure, runs it, and admits the outcome as an evaluation certificate — on this toolchain one
named axiom `Superperm7.<declaration>._native.native_decide.ax_<i>_<j>` per use, 382 in all
(`native_decide_certificates.txt`).  Neither the Lean kernel nor comparator (nor `lean4checker`, nor
`nanoda`) re-executes native code, so no external checker can turn these into kernel facts; that is the
trust base stated in the top-level README.

What comparator *does* establish for this repository is statement fidelity: run with `config.json` (which
permits only the standard axioms), it builds the trusted `Challenge` and the untrusted `Solution`, exports
both, and checks that `superperm7_upper_5906`, `superperm7_lower_5897`, `superperm7_lower_5898` and every
constant their statements mention are *identical* between the two — i.e. that the library proves exactly
the isolated statements.  That comparison passes (it was run during pre-publication review at comparator
commit `71b52ec`, re-pinned to Lean v4.30.0).  The run then stops, as it must, at the axiom stage with
`Illegal axiom detected: 'Superperm7.Cert.M2.chk_0_37._native.native_decide.ax_1_1'`: at that comparator version the
permitted-axiom list can only name constants that also exist in the trusted environment, so
per-declaration `native_decide` certificates cannot be whitelisted and a fully "okay" run is not
available for a proof of this kind.  We therefore do not claim one.  Independent corroboration of the
evaluations themselves is a separate, conventional exercise (re-computing the tables stated in
`Superperm7/CapTab*.lean`, `Templates.lean`, `EqualityCells.lean` with any program).

## Full comparator run

Prerequisites as in the comparator README (`elan`, `landrun`, `lean4export` for the toolchain in
`../lean-toolchain`, the `comparator` binary).  From the repository root:

```sh
lake exe cache get
lake env /path/to/comparator comparator/config.json
```

Expected outcome, as explained above: the statement comparison passes and the run then reports the first
evaluation certificate as an illegal axiom.  Do not pre-build `Challenge`/`Solution` before a run you want to
rely on; let comparator build them.  The three `[[lean_lib]]` stanzas with `srcDir = "comparator"` at the end
of `../lakefile.toml` make the modules `ChallengeDeps`, `Challenge`, `Solution` resolvable by those bare names.
