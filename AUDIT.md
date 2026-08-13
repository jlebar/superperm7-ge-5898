# Audit record

This file records the checks that were run on exactly the sources in this repository and how to
reproduce them.  Nothing here is part of the trusted base: a reader can re-run everything below.

Toolchain: Lean `leanprover/lean4:v4.30.0`; mathlib `v4.30.0` (commit `c5ea00351c28e24afc9f0f84379aa41082b1188f`, pinned in `lake-manifest.json`).
Library name: `Superperm7`.  Repository: <https://github.com/jlebar/superperm7-ge-5898>.  Option `precompileModules = true`: the certificate shards call the search kernel as compiled code
(shared libraries) during elaboration rather than through the interpreter — it changes which evaluator is
trusted for the `native_decide` certificates, not what is proved.

## How to reproduce

```sh
lake exe cache get                       # optional: prebuilt mathlib
lake build                               # the Superperm7 library (default target = Main + Bound5897)
lake env lean AxiomAudit.lean            # axioms of Superperm7.main_theorem, lower_bound, lower_bound_5897
lake build Solution                      # the isolated statements, proved by delegation
lake env lean comparator/PrintAxioms.lean
lake build Challenge                     # the trusted statement file; expect exactly three 'sorry' warnings
```

## Recorded results at this commit (x86-64 Linux, 96 cores shared with other work)

* `lake build` (default target: `Superperm7.Main` and `Superperm7.Bound5897`) from a clean `.lake/build`:
  **completed successfully, 18,083 jobs** (mathlib taken from the cache), no errors, no `sorry` warnings.
  Total CPU time 11.0 hours (39,447 s user); wall time 77 minutes on this machine; an independent
  rebuild from a clean clone during pre-publication review measured 11.1 CPU-hours and 55 minutes wall on
  96 hardware threads, with both `#print axioms` outputs byte-identical to the files in `docs/`.  Of this,
  `lake build Superperm7.Bound5897` alone (the independent, cheaper `s(7) ≥ 5897`) is about 1–1.5
  CPU-hours plus a one-time ≈ 1 CPU-hour compile of Mathlib's C files to object code (forced by
  `precompileModules`; the Mathlib cache ships `.c`, not `.o`); `Superperm7.Main` (the 5898 theorem)
  accounts for the rest.  Peak memory: ~7 GB for the largest single Lean process, ~130 GB across the
  machine at full parallelism.
* `lake build Superperm7 Challenge Solution`: completed successfully, **18,090 jobs** in total; the only
  warnings are the three deliberate `declaration uses 'sorry'` in `comparator/Challenge.lean`.
* `sorry` tokens outside comments in the whole repository: **3**, all in `comparator/Challenge.lean` (the
  trusted statement file, by design).  None under `Superperm7/`, none in `comparator/Solution.lean`.
* `axiom` declarations anywhere in the repository: **0**.  Occurrences of `implemented_by` or
  `@[extern` under `Superperm7/`: **0**.
* Axiom audit.  Every headline theorem depends on `propext`, `Classical.choice`, `Quot.sound` and
  otherwise **only** on `native_decide` evaluation certificates, i.e. names of the form
  `Superperm7.<declaration>._native.native_decide.ax_<i>_<j>`; no `sorryAx`, no other axiom:

| theorem | file | axioms in total | of which evaluation certificates | the rest |
|---|---|---|---|---|
| `Superperm7.main_theorem` (5898 ≤ s(7) ≤ 5906) | `Superperm7/Main.lean` | 383 | 380 | propext, Classical.choice, Quot.sound |
| `Superperm7.lower_bound` (∀ w, … → 5898 ≤ w.length) | `Superperm7/Main.lean` | 381 | 378 | propext, Classical.choice, Quot.sound |
| `Superperm7.lower_bound_5897` (independent, cheaper) | `Superperm7/Bound5897.lean` | 78 | 75 | propext, Classical.choice, Quot.sound |
| `superperm7_upper_5906` | `comparator/Solution.lean` | 5 | 2 (`witness_isSuperpermutation`, `witness_length`) | propext, Classical.choice, Quot.sound |
| `superperm7_lower_5897` | `comparator/Solution.lean` | 78 | 75 | propext, Classical.choice, Quot.sound |
| `superperm7_lower_5898` | `comparator/Solution.lean` | 381 | 378 | propext, Classical.choice, Quot.sound |

  The complete verbatim output of the two audit commands is in `docs/axiom-audit-library.txt` 
  and `docs/axiom-audit-statements.txt`; the union of the certificate names (382) is also the permitted-axiom
  list in `comparator/config.json`.

## What the evaluation certificates are

Each certificate is the record of one `native_decide` call: a closed decidable proposition (a failed
capacity search on one shard, an equality of a computed table with a literal, an enumeration returning a
stated list, a join check returning `false`, or the witness check) was compiled by Lean, executed, and
its Boolean result admitted.  The propositions are all stated in the source next to the call
(`Superperm7/CapCheck/*`, `Cert/*`, `CapTabs.lean`, `Directs.lean`, `Templates.lean`, `EqChecks/*`,
`EqualityCells.lean`, `Witness.lean`, and the small table facts in `Basic`/`Rows`).  Trusting them
means trusting Lean's compiler and runtime on these programs, in addition to the kernel.  They can be
corroborated independently of Lean by recomputing the same finite objects with any program; the
mathematical reduction that makes these finitely many facts sufficient is checked by the kernel in the
ordinary way.

## Kernel replay (extra check)

`LEAN_NUM_THREADS=8 lake env leanchecker Superperm7 Solution ChallengeDeps Challenge` — the `lean4checker`
shipped with the toolchain, which re-typechecks every declaration of the named modules (module names are
prefixes, so all 368 `Superperm7.*` modules are covered) through the kernel from the `.olean` files —
exited 0 with no diagnostics in 5 min 14 s wall at this commit (run on a build directory containing only
this commit's modules).  This shows that every kernel-checkable proof replays outside the elaborator; it
does not re-execute the 382 evaluation certificates, which are axioms to the kernel.  Without the thread cap
the replay runs all modules in parallel and needs several hundred GB of memory.

## Comparator

`comparator/` contains trusted statement files and a configuration for
[leanprover/comparator](https://github.com/leanprover/comparator).  As `comparator/README.md` explains, for a
proof that uses `native_decide` comparator can certify statement fidelity but not the computations: its
Challenge-vs-Solution statement comparison passes for the three statements (run during pre-publication
review at comparator `71b52ec` / Lean v4.30.0), after which the axiom stage necessarily rejects the first
evaluation certificate.  We ran the quick check (`PrintAxioms.lean`) recorded above ourselves.
