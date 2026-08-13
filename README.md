# 5898 ≤ s(7) ≤ 5906: a Lean-verified lower bound for superpermutations on seven symbols

*Human-written content:* Everything outside of this section was generated using
an unreleased version of Claude.  My contribution, such as it is, consisted of
pointing the model at this problem, so Claude should be credited as the author
here.  Nonetheless I take responsibility for the contents of this repo.

This is not an official Anthropic product or publication.

This proof builds on the work of many humans.  I hope that other humans will be
able to build upon this one.

--------

> Research artifact.  Not maintained and not accepting contributions.
> A Lean 4 development released as a static record of the result; see `AUDIT.md` for exactly what was
> checked at this commit and `comparator/` for the isolated statements.

Repository: <https://github.com/jlebar/superperm7-ge-5898>.

A *superpermutation* on seven symbols is a word over `{1,…,7}` that contains every one of the
5040 permutations as a contiguous factor; `s(7)` denotes the least possible length of such a word.
The best construction, found by Greg Egan and Robin Houston in 2019, has length 5906.  This repository contains a
Lean 4 / mathlib proof that **no superpermutation on seven symbols has length less than 5898**:

```lean
-- Superperm7/Main.lean
theorem Superperm7.main_theorem :
    (∃ w : Word, IsSuperpermutation w ∧ w.length = 5906) ∧
    (∀ w : Word, IsSuperpermutation w → 5898 ≤ w.length)
```

Here `Word := List (Fin 7)` and `IsSuperpermutation w := ∀ p : Equiv.Perm (Fin 7), List.ofFn p <:+: w`
(mathlib notions only; the definitions are isolated in `comparator/ChallengeDeps.lean`, 29 lines, and
repeated at the top of `Superperm7/Basic.lean`).  The first conjunct merely re-checks
the published Egan–Houston word; the content is the second (also available on its own as
`Superperm7.lower_bound`).  This leaves `s(7) ∈ {5898, …, 5906}`.  The file
`Superperm7/Bound5897.lean` proves the weaker `s(7) ≥ 5897` (`Superperm7.lower_bound_5897`) by an
independent and roughly ten times cheaper elimination; the main theorem does not use it, and it is
kept only as corroboration and as a quick end-to-end check of the reduction.

The development has no `sorry` (apart from the three deliberate placeholders in the trusted statement
file `comparator/Challenge.lean`), declares no axioms, and uses no `implemented_by`/`extern`.
`#print axioms` (`AxiomAudit.lean`; output recorded verbatim in `AUDIT.md`) lists `propext`,
`Classical.choice`, `Quot.sound`, and the evaluation certificates that `native_decide` emits for
the finite computations — 380 of them for the main theorem (75 for the cheaper 5897 bound).  So, beyond the Lean kernel, the
trust base includes Lean's compiler and native evaluator; this is the same footing as the `s(6) = 872`
formalization cited below, and it is spelled out, together with what an external checker such as
`comparator` can and cannot add for a proof of this kind, in `comparator/README.md`.  The statements
themselves are isolated in `comparator/ChallengeDeps.lean` + `comparator/Challenge.lean` (about 50 lines
over Mathlib, headers included), which is all one has to read to know exactly what is claimed.

## Context and prior work

Everything here stands on a decade of work by the superpermutation community, most of it done in the
open in the [Superpermutators](https://groups.google.com/g/superpermutators) group and its
[shared repository](https://github.com/superpermutators/superperm).

**The problem.**  Ashlock and Tillotson (1993) conjectured `s(n) = 1! + 2! + ⋯ + n!`.  Nathaniel Johnston
(2013) drew attention to the question and to the non-uniqueness of minimal words
([OEIS A180632](https://oeis.org/A180632)).  Robin Houston (2014,
[arXiv:1408.5108](https://arxiv.org/abs/1408.5108)) disproved the conjecture for `n = 6` by finding a
word of length 872, one less than predicted, using TSP solvers.

**Classical lower bounds.**  An anonymous 4chan poster (2011) proved `s(n) ≥ n! + (n−1)! + (n−2)! + n − 3`;
the argument was verified, completed and written up by Houston, Jay Pantone and Vince Vatter (2018).  For
seven symbols it gives **5884**.  Houston (late 2018) and, independently, Erik Tadewaldt (2019) observed
that the bound can be raised by one for `n ≥ 5` (**5885**); see also Michael Engen and Vince Vatter,
*Containing all permutations*, Amer. Math. Monthly 128 (2021).

**Upper bounds for n = 7.**

* October 2018 — Greg Egan, adapting a 2013 construction of Aaron Williams, gives words of length
  `n! + (n−1)! + (n−2)! + (n−3)! + n − 3` for every `n`: **5908** at `n = 7`.
* 1 February 2019 — Bogdan Coanda ("Charlie Vane") finds a word of length **5907**, and soon several more.
* 27 February 2019 — Houston and Egan reach **5906**: Houston proposed "non-standard kernels" and generated
  candidates, and Egan's search program completed one of them — a palindromic kernel, with the twofold
  symmetry imposed on the whole solution — with 2-cycles
  ([Egan's write-up](https://www.gregegan.net/SCIENCE/Superpermutations/Superpermutations.html); the
  programs live in the shared repository).  5906 is still the record; many further 5906-words have since
  been derived by the group.

**Lower bounds for n = 7 in 2026** (as of 12 August 2026; machine-checked bounds first, strongest first within each group).

| bound | by | date | status |
|---|---|---|---|
| **5892** | Xiaolong Liu — preimage-chain refinement `hunterBound(k) + Γ_k` of the Hunter–Raudvere bound ([repo](https://github.com/Haruhiyuki/superpermutations-preimage-chain-lower-bounds)) | 10 Aug | Lean, kernel-only (no `native_decide`) |
| **5889** | にか (nika0220) — the equality case of the Hunter–Raudvere bound excluded by integer Farkas certificates ([repo](https://github.com/nika0220/superperm5889), [announcement](https://groups.google.com/g/superpermutators/c/PWo62q0ULNo)) | 11 Aug | Lean, with `native_decide` |
| **5888** | Zach Hunter and Uku Raudvere — `s(k) ≥ k! + (k−1)! + (k−2)! + ⌈((k−2)! − (k−2))/(k² − 3k + 1)⌉ + k − 3`, from Hunter's 2019 draft, completed and formalized ([repo](https://github.com/urdvr/superpermutations-hunter)) | 28 Jul | Lean |
| **5886** | Uku Raudvere — an additive sharpening of the 2018 bound ([repo](https://github.com/urdvr/superperm-coeff2)) | Jul | Lean |
| **5896** | Vlad Gheorghe, with GPT-5.6 and Claude — the `n = 7` run (paper §10.3, `a7/` bundle) of their computer-assisted proof package for `s(6) = 872` ([a6-872](https://github.com/vlad-ds/a6-872)), whose reduction is proved on paper and whose cases are closed by recorded searches; the authors label the `n = 7` result a "theorem candidate", "conditional on the theorem layer of \[the `s(6)`\] paper" and "quarantined pending an independent rerun of its replay bundle" | 28–29 Jul | conditional, not machine-checked |
| **5893** | Marin Kisic — a general bound drafted by GPT-5.6, which he described as one he had not been able to verify ([announcement](https://groups.google.com/g/superpermutators/c/gB_XTrvE0KY)); Raudvere replied that he has an unpublished independent proof of it based on an idea of Hunter's | 7–8 Aug | informal, unverified |

Meanwhile the six-symbol value was settled formally: Benjamin Grayzel, Claude Fable 5 and GPT Sol 5.6 Pro
gave a complete Lean 4 proof of **`s(6) = 872`** ([superperm6](https://github.com/BGray-wrl/superperm6),
29 July 2026); Cole Fritsch had announced the equality in 2021 with an argument that remained incomplete.

**What this repository adds** is `s(7) ≥ 5898`, verified end-to-end in Lean: six more than the best
previously machine-checked bound we are aware of (Liu's 5892), and above the unverified or conditional
claims of 5893 and 5896.  Methodologically it is a descendant of two of the works above.  The *reduction
layer* — from a hypothetical short word to a small family of combinatorial "coarsened certificates" — is
a port from six to seven symbols of the Grayzel–Fable–Sol `superperm6` development, whose files we adapted
under its MIT licence (details in `docs/PORT_LOG.md`).  The *elimination layer* follows the capacity idea
behind Gheorghe et al.'s conditional 5896, but certifies the single-trail capacity bounds inside Lean by
complete searches (rather than bounding them on paper), carries marked rows, superadditive closure and
the final "equality-cell" join inside the proof assistant, and thereby gains two symbols while removing
the conditionality.

## The argument in outline

Write a hypothetical word's length as `5884 + D`.  The reduction views the word as a Hamiltonian
route in the overlap digraph on the 5040 permutations, normalizes it, and extracts a *coarsened
certificate*: at most `τ = η + 1 + b` trails of cyclic rows of insertion blocks (some positions
possibly "marked", i.e. concealed), pairwise block-distinct and visibly rotation-class-disjoint,
carrying `k = 120 + m − r + a` rows with total charge (holes) at most `u = 6m − r`, where the
*defect* `D = m + a + b + η` is bounded by the length budget.  Proving `s(7) ≥ 5884 + K` therefore
means showing that no parameter cell with `D ≤ K − 1` admits such a certificate.

* **Single-trail capacity.**  Let `M_μ(g)` be the maximum number of rows of one trail with charge
  `≤ g` and at most `μ` marked rows.  A depth-first search with *suffix-cap pruning* (a suffix of a
  trail is, after relabelling, again a trail, so already-established caps bound every subtree)
  determines `M_μ`; its completeness is proved once as a theorem about the search function, after which
  each table entry `c` is certified as an upper bound (`M_μ(g) ≤ c`) by a failed search for `c + 1`
  rows, evaluated by `native_decide`.  Only these upper bounds are proved or needed; that the tabulated
  values are the exact maxima is what the searches found, not something the proof uses.  Certified
  here: all mark counts for `g ≤ 36`; `μ = 0` for `g ≤ 56`; `μ = 1` for `g ≤ 54`; `μ = 2` for `g ≤ 46` —
  the deep levels by cube-and-conquer over some 250 shards, each its own Lean file.  All these tables
  coincide with the unmarked one:
  `5,5,9,9,13,13,16,16,20,20,24,24,27,27,31,31,34,34,36,38,40,41,43,44,46,47,50,51,52,54,56,57,59,
  60,63,64,66,66,68,69,71,72,74,75,77,79,80,82,83,85,85,86,88,89,91,92,93`.
* **Closure and sweep.**  The least charge needed for `L` rows is superadditive in `L` (with marks
  split between the parts), which extends the certified tables to valid caps for every budget; a
  dozen cheap *direct* high-target searches sharpen the cap where the marked closures are loose.
  A max-plus convolution over the `≤ τ` trails then kills every cell with `D ≤ 12` and every
  cell with `D = 13` except nine *equality cells*,
  `(m, a, r) ∈ {(10,0,0), (11,0,0), (12,0,0)}`, in which the convolution bound is attained exactly.
* **Equality cells.**  Tightness forces every trail in such a cell to be an *optimal* trail at one
  of the charges `14, 16, 26, 34, 36` (lengths `31, 34, 50, 63, 66`).  A collecting variant of the
  search, again with a proved completeness theorem, enumerates all optimal trails up to
  relabelling — there are just `3, 3, 2, 2, 4` of them, none marked — and an exhaustive check over
  the 5040 relabellings shows that no family with charge multiset `(14,14,16,16)`, `(14,16,36)`,
  `(14,26,26)`, `(16,16,34)` or `(36,36)` is pairwise class-disjoint.  Hence no cell with `D ≤ 13`
  survives, which is `s(7) ≥ 5898`.

`docs/PORT_LOG.md` records exactly which statements of the six-symbol reduction changed in the port
(constants `720→5040`, `120→720`, `144→840`, block length `5→6`, the defect budget, and the removal
of every `native_decide` that quantified over *pairs* of permutations, which would not have been
feasible at 5040² cases).

## Repository layout

| path | contents |
|---|---|
| `Superperm7/Basic, Rows, RowModel, Coarsen` | permutations of `Fin 7`, overlap cost, the maps `R`, `F`, `N₂`, rotation classes (720), insertion blocks (840), cyclic rows, marked rows, coarsened certificates |
| `Superperm7/Path … CoarsenBridge` (20 files) | the reduction, ported from `superperm6`: word ↔ Hamiltonian route, normalization, cheap cover, orbit inequality, permutation-map counts, the exact relation between defect and route weight, and the surgery bridge producing a `CoarsenedInstance` |
| `Superperm7/Search, SearchSound` | reference search with suffix-cap pruning and its completeness theorem |
| `Superperm7/CapTab, CapCheck/*, CapTable, Closure` | the all-marks table to charge 36 (37 certificate files) and its superadditive closure — used by both theorems |
| `Superperm7/ElimD12Data, ElimD12, Bound5897` | the `D ≤ 12` sweep and the independent cheaper bound `s(7) ≥ 5897`; not used by `Main` |
| `Superperm7/FastSearch, FastSearchSound, Cube` | the fast search kernel (byte-array bitsets, packed candidates, mark budget), its completeness theorem, and the sharding lemma |
| `Superperm7/CapTabs, Cert/M0, Cert/M1, Cert/M2` | the certified tables `μ = 0 (g ≤ 56)`, `μ = 1 (g ≤ 54)`, `μ = 2 (g ≤ 46)` — 248 shard files plus per-level and per-table aggregators (279 files) |
| `Superperm7/ClosureMu, Directs, ElimD13Data, ElimD13` | mark-splitting closure, direct queries, the `D ≤ 13` sweep outside the equality cells |
| `Superperm7/FastEnum, Templates, Equality, EqualityCells, EqChecks/*, EqualityChecks` | optimal-trail enumeration with completeness, decoding, the relabelled-join soundness theorem, the tightness computation, and the five join-impossibility facts |
| `Superperm7/Witness`, `data/superperm7_5906.txt` | the Egan–Houston 5906-word, read at elaboration time and checked by evaluation |
| `Superperm7/Main` | assembly of the main theorem `5898 ≤ s(7) ≤ 5906` |
| `comparator/` | the isolated statements (`ChallengeDeps.lean`, `Challenge.lean`: trusted, Mathlib only), the delegating `Solution.lean`, `PrintAxioms.lean`, and a configuration for `leanprover/comparator` — start here |
| `AxiomAudit.lean`, `AUDIT.md` | the axiom audit of the library theorems and the record of every check run at this commit |
| `docs/PORT_BRIEF.md`, `docs/PORT_LOG.md` | the specification given for the port and the log of what was changed |
| `tools/gen_cert.py`, `tools/frontier_sizes.json` | the (untrusted) script that laid out the certificate shards; not needed to check the proof |

## Checking the proof

Requires [`elan`](https://github.com/leanprover/elan); the pinned Lean and mathlib versions are picked up
automatically.  The full build is about 11 CPU-hours and parallelizes well (measurements, memory
footprint and an optional kernel replay are recorded in `AUDIT.md`).

```sh
lake exe cache get                                                  # prebuilt mathlib
lake build                                                          # the main theorem
lake env lean AxiomAudit.lean                                       # axioms of the library theorems
lake build Solution && lake env lean comparator/PrintAxioms.lean    # axioms of the isolated statements
```

`lake build Superperm7.Bound5897` builds only the cheaper independent bound `s(7) ≥ 5897`, in roughly a
tenth of the time.

What a careful reader should inspect by hand is small: the definitions and statements in `comparator/`
(or equivalently the top of `Superperm7/Basic.lean` and `Superperm7/Main.lean`).  Everything else is checked by Lean.  What Lean does *not* protect
against is a bug in its own compiler or native evaluator affecting one of the `native_decide`
certificates; readers who want independent corroboration of the finite facts (the capacity tables,
the five optimal-trail lists, the join checks) can regenerate them with any straightforward
program — they are stated explicitly in `CapTab*.lean`, `Templates.lean` and `EqualityCells.lean`.

## Provenance, credit, licence

The mathematics specific to this bound, the search design, and all Lean engineering were carried
out by Claude (Anthropic) working as an autonomous coding agent, in a session directed by Justin
Lebar (Anthropic), August 2026.  The reduction layer is adapted from
[`superperm6`](https://github.com/BGray-wrl/superperm6) by Benjamin Grayzel, Claude Fable 5 and
GPT Sol 5.6 Pro (MIT licence; notice retained in `NOTICE` and in each derived file's header).  The capacity method builds
on the framework of Gheorghe et al.'s [`a6-872`](https://github.com/vlad-ds/a6-872).  The 5906-word
is Egan and Houston's, taken from Egan's page / the Superpermutators corpus.  We are grateful to all of
them, and to Robin Houston, Bogdan Coanda, Jay Pantone, Vince Vatter, Nathaniel Johnston, Zach Hunter, Uku Raudvere and the
other members of the Superpermutators group, on whose definitions, data, programs and patient
public discussion this work relies throughout.

Released under the Apache License, Version 2.0 — see `LICENSE` and `NOTICE`; the files adapted from
`superperm6` additionally carry, and remain subject to, its MIT notice (reproduced in `NOTICE`).

## How to cite

If you build on this result, please cite it as

> Claude (Anthropic), *A Lean-verified lower bound s(7) ≥ 5898 for superpermutations on seven
> symbols*, 2026.  https://github.com/jlebar/superperm7-ge-5898

```bibtex
@misc{superperm7-ge-5898,
  author       = {{Claude (Anthropic)}},
  title        = {A {Lean}-verified lower bound $s(7) \ge 5898$ for superpermutations on seven symbols},
  year         = {2026},
  howpublished = {\url{https://github.com/jlebar/superperm7-ge-5898}},
  note         = {Lean 4 / mathlib formalization, version 1.0.0}
}
```

(`CITATION.cff` carries the same data in machine-readable form.)  Please also cite the works this one
rests on — in particular Grayzel, Claude Fable 5 and GPT Sol 5.6 Pro's `superperm6` for the reduction
layer, and Egan and Houston for the 5906-symbol word — as detailed under *Context and prior work* above.

## Not in this repository

The same session also searched, without success, for a word of length 5905, by generalizing
Egan's kernel-completion program to arbitrary kernels and exhaustively refuting some 8×10⁷
kernel designs (all two- and three-component kernels in the natural parameter ranges, and all
single kernels of score 15 up to 35 rows, apart from a small explicitly listed residue).  That
computation is evidence, not proof, and is being written up separately; nothing in the verified
result depends on it.
