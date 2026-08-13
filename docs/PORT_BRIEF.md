> Historical note (release): this is the brief that was handed to the sub-task that ported the
> six-symbol reduction layer, reproduced unedited except that a local path has been removed.  It was
> written for the first milestone (defect `D ≤ 12`, route weight `≤ 5889`, i.e. `s(7) ≥ 5897`); the bound
> was afterwards raised to `D ≤ 13` / weight `≤ 5890` for the main theorem (see `PORT_LOG.md`, "Defect
> bound bump").  It refers to development files that are not part of this repository (`orig6/` = the
> upstream `superperm6` sources, `../work/LEAN_MAP.md`, `Compute.lean`, `Test.lean`, `MTable.lean`), and to
> `Main.lean` in its old role (now `Bound5897.lean`).

# Port brief: n = 6 → n = 7 reduction layer

Goal: in `the development directory ` (Lean 4.30.0 + mathlib v4.30.0,
`lake build` works, `precompileModules = true`), port the *n-uniform reduction* of the verified
`s(6)=872` development (original files in `orig6/`, technical map in
`../work/LEAN_MAP.md` — READ §0, §1.2–1.13, §1.15, §1.20–1.25, §B, §C FIRST) so that it proves,
for seven symbols and defect budget `D ≤ 12`, the bridge theorem consumed by the new
capacity elimination.

Already done and building (DO NOT change statements in these; you may append lemmas at the
end of a file if downstream needs them, and say so in PORT_LOG.md):
`Superperm7/Basic.lean` (Fin 7, Perm7, d, R, F, N₂, rClass (orbit of R, size 7), fBlock (orbit
of F, size 6), 5040/720/840 counts, `cost_one_successor`, `cost_two_successors`,
`d_eq_iff_compatible`, `agree_of_compatible`, `perm_eq_of_agree_six`, …),
`Superperm7/Rows.lean` (Row with `lengthCode : Fin 6`, alpha = take 4, beta = drop 3 of R⁻¹ of
last state, `row_endpoint_table`, `length_five_row_is_loop`, `G` (rotate first five, order 5),
`full_block_successor`, `no_six_pairwise_disjoint_full_rows`),
`Superperm7/RowModel.lean` (RowCompatible/RowDisjoint/CompatibleTrail, relabelling; this is the
generic half of `orig6/ResetPhase.lean`; import it wherever the old code imported
`Section57Closure.ResetPhase`), `Superperm7/Coarsen.lean` (MarkedRow with `omitted : Finset (Fin 6)`,
`charge = (6 - length) + |omitted|`, `CoarsenedInstance k τ u b`, `ForestInstance`,
`omissionRuns_le_two` replaces the n=6 `two_runs_unique_pattern`),
`Superperm7/Compute.lean` (mine; unrelated to you).

Seeded copies with only the namespace/`Perm6→Perm7` renamed (they do NOT build yet) are in
`Superperm7/`: Path, Normalization, CheapCover, Frontier, GraphRank, Euler, CycleLists, Orbit,
FirstReturn, PermutationMap, Registry, Structural, Section4, Section5Core, Surgery, Chains,
ChainTrails, CoarsenAux, CoarsenAccounting, CoarsenBridge.

## Target statements

Parameters at n = 7 (put them as they arise; a small `Params` section at the top of
CheapCover is fine):
* words of length ≤ 5896  ⇔  Hamiltonian routes of weight ≤ **5889** (= 5896 − 7);
* `x1 = 4320 − r`, `x2 = 720 + r − q`, `x3 = q − p`, `7 + cappedRouteWeight = 5763 + r + q + p`,
  so weight ≤ 5889 gives `r + q + p ≤ 133`;  `CheapCoverProfile.loss := 720 + r + q + p ≤ 853`;
  admissible: `r ≤ 4320 ∧ 1 ≤ p ∧ p ≤ q ∧ q ≤ 720 + r`;
* orbit inequality: `120 + ceilDivSix r ≤ r + q` with `ceilDivSix r := (r+5)/6`
  (from `720 + r ≤ 6M`, `M ≤ r + k`, `k ≤ q`);
* **no frontier lift**: keep the actual `p` (= highCostCount + 1).  `RouteStructuralCounts` gets
  `budget : r + q + p ≤ 133` instead of `frontier : r + q + p = 29`, `M_eq : M = 120 + m`,
  `k_eq : k = 120 + m - r + a`, `q_eq : q = k + b`, `p_eq : p = eta + 1`,
  `defect_le : m + a + b + eta ≤ 12` (instead of `defect_four`), `a_le_r`, `r_le_six_m : r ≤ 6*m`,
  `k_le_M`, `k_le_q`.  (Since `k = 120+m-r+a` uses ℕ subtraction you need `r ≤ 120 + m`, which
  follows from `r ≤ 6m`… careful: only for `m ≤ 24`; use `M ≤ r + k` i.e. derive `k` as
  `M + a - r` with the guard `r ≤ M + a`… mirror whatever guard structure the n=6 file uses —
  see LEAN_MAP §C.10 and the "Natural subtraction guards" remark; at n=6 they had `r ≤ 24+m`.
  Here `r ≤ 6m` and `m ≤ 12` give `r ≤ 72 ≤ 120 + m`, fine.)
* Registry: replace the n=6 `StructuralFamily`/`RegistryCandidate` (Fin 5 fields, D = 4, 152 cases)
  by
  ```lean
  structure RegistryCandidate where
    m : ℕ; a : ℕ; b : ℕ; eta : ℕ; r : ℕ
  def RegistryCandidate.valid (c) : Prop :=
    c.m + c.a + c.b + c.eta ≤ 12 ∧ c.a ≤ c.r ∧ c.r ≤ 6 * c.m ∧ (c.m = 0 → c.r = 0)
  def RegistryCandidate.k (c) : ℕ := 120 + c.m - c.r + c.a
  def RegistryCandidate.tau (c) : ℕ := c.eta + 1 + c.b
  def RegistryCandidate.u (c) : ℕ := 6 * c.m - c.r
  ```
  The face-fragmentation/genus data (`g`, `h`, `b = a − 2g + h`) is NOT needed by the new
  elimination.  Keep the Euler files (they are generic and free) but you may drop
  `hasFaceFragmentation` from the candidate: `RouteRealizesRegistryCandidate route hroute c` :=
  `c.valid ∧ ∃ _ : IsNormalizedRoute route, routeWeight route ≤ 5889 ∧ ∃ z : RouteStructuralCounts
  route hroute, c.m = z.m ∧ c.a = z.a ∧ c.b = z.b ∧ c.eta = z.eta ∧ c.r = z.r`.
  If keeping the Euler-derived constraint is *easier* than removing it (because Structural/
  Section4 are written around it), keep it — extra valid-ness conjuncts are harmless as long as
  `valid` still implies the four conjuncts above.
* The two theorems the elimination consumes (names fixed, put them in CoarsenBridge.lean):
  ```lean
  theorem normalized_light_route_realizes_registryCandidate {route : List Perm7}
      (hroute : IsHamiltonianRoute route) (hnormal : IsNormalizedRoute route)
      (hweight : routeWeight route ≤ 5889) :
      ∃ c : RegistryCandidate, RouteRealizesRegistryCandidate route hroute c
  theorem coarsen_bridge {route : List Perm7} {hroute : IsHamiltonianRoute route}
      {c : RegistryCandidate} (h : RouteRealizesRegistryCandidate route hroute c) :
      ∃ u' : ℕ, u' ≤ c.u ∧ Nonempty (CoarsenedInstance c.k c.tau u' c.b)
  ```
  (`coarsen_bridge` is the disjunction-free corollary of the n=6 `coarsen_bridge_cases`:
  case 1 gives `u' = u`; case 2 gives `u' = u−1`; the forest case gives a
  `ForestInstance k τ u extra`, whose `toCoarsenedInstance` has `b := 0` — use
  `CoarsenedInstance.mono`/a cast to weaken `0 ≤ c.b`.  If porting the full trichotomy is no
  harder, port it and derive `coarsen_bridge` from it.)
  Also keep `exact_path_formulation`, `exists_normalized_route`/`normalized_route_of_weight_at_most`
  with their n=6 signatures (7 in place of 6).

## What to drop
`Witness.lean`, `Consequences.lean`, everything under `Section57Closure` except the generic half of
ResetPhase (already ported as RowModel), the whole `M0*`/`BoundaryReduction` path (the bridge has
no `m ≠ 0` hypothesis — LEAN_MAP §B.3), `Frontier`'s lift and profile counts (keep only
`orbit_inequality_of_counts`-style arithmetic you actually use; you may inline it and delete
Frontier.lean), `Registry`'s published family list and counts.

## Mechanical substitutions (LEAN_MAP §B.2)
720→5040 (perms), 120→720 (classes), 144→840 (blocks), 600→4320, word length / R order 6→7,
block size / F order 5→6, `Fin 5`→`Fin 6` (row positions, gap lengths), `F^[4]`→`F^[5]`,
`R^[5]`→`R^[6]`, `4 − holes`→`5 − holes`, charge `5 −`→`6 −`, `5 * M`→`6 * M`, `5 * m`→`6 * m`,
24→120 (the `(n−2)!`), 842→5763, 865→5889, 29→133 (as `≤`), `take 3`→`take 4` (alpha),
`drop 3` stays (beta), `Triple` stays as a name.  `R_order_six`→`R_order_seven`,
`F_order_five`→`F_order_six`, `card_perm6`→`card_perm7`, `d_le_six`→`d_le_seven`,
`length_four_row_is_loop`→`length_five_row_is_loop`, `G_order_four`→`G_order_five`,
`no_five_pairwise_disjoint_full_rows`→`no_six_pairwise_disjoint_full_rows`.

## Performance rules (important)
Any `native_decide` quantifying over **pairs** of permutations (5040² = 25 M) is forbidden — it
will not finish.  The n=6 code has ~10 of these (LEAN_MAP §E: `rClass_eq_of_mem`,
`R_mem_rClass_of_mem`, `fBlock_eq_of_mem`, `cost_three_iff_endpoint_compatible`,
`gapComplementRow_beta_of_F_eq`, …).  Restate each with a single permutation quantifier plus a
small explicit inner range, or prove it structurally.  Patterns that work:
* `q ∈ rClass p → …` : `rClass p = (range 7).image (R^[i] p)`, so obtain `i < 7` with
  `q = (R^[i]) p` (`Finset.mem_image`) and prove `∀ p, ∀ i : Fin 7, P p ((R^[i]) p)` by
  `native_decide` (5040·7).  Same for `fBlock` with 6.
* `d p q = 3 ↔ (permWord p).drop 3 = alpha q`: use `d_eq_iff_compatible` (Basic) — `d p q = k`
  iff `OverlapCompatible (permWord p) (permWord q) k` for `k < 7`, and `OverlapCompatible … 3`
  unfolds to `drop 3 (permWord p) = take 4 (permWord q) = alpha q`.  No search at all.
* `F a = x → P a x` over all pairs: substitute, prove `∀ a, P a (F a)` (5040).
Single-quantifier `native_decide` over `Perm7` (5040 cases) is fine; over `Row` (30240) is fine
if the body is cheap.  Use `native_decide +revert` when the goal has a free `p : Perm7`.
Build one file at a time: `lake build Superperm7.<File>` (from the project root).  A file that
takes > 15 min to build almost certainly has a pairwise `native_decide` left in it.

## Process
Work strictly in dependency order (LEAN_MAP §0): Path, Normalization, CheapCover, (Frontier),
GraphRank, Euler, CycleLists, Orbit, FirstReturn, PermutationMap, Registry, Structural, Section4,
Section5Core, Surgery, Chains, ChainTrails, CoarsenAux, CoarsenAccounting, CoarsenBridge.
GraphRank/Euler/CycleLists/Surgery should build unchanged (they are generic) — do them early to
confirm.  After each file builds with **no `sorry`**, append a line to `PORT_LOG.md`
(file, status, what changed beyond substitution, build time).  If you get stuck on a lemma for
more than ~30 minutes, leave a clearly marked `sorry` with a `-- PORT-TODO:` comment explaining
exactly what remains, log it, and move on; list all such at the top of PORT_LOG.md.
Do not modify `Compute.lean`, `Test.lean`, `MTable.lean`, or any file whose name starts with
`Cap`, `Search`, `Elim`, `Closure`, `Main` (those are being written concurrently).  Do not touch
`lakefile.toml`.  Never run `lake clean`.  Never run `lake build` without a target (build only
your file).  Keep the mathematical content and proof structure of the original; this is a port,
not a redesign.
