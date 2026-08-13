> Note (release): this log was written during development.  File names have since changed:
> the development's `Main.lean` (5897) is now `Bound5897.lean`, `Main98.lean` (5898) is now `Main.lean`,
> `Elim{,Data}.lean` are `ElimD12{,Data}.lean` and `Elim98{,Data}.lean` are `ElimD13{,Data}.lean`.

# PORT_LOG: n=6 → n=7 reduction layer

## Defect bound bump 12 → 13

The reduction layer now runs at weight budget `5890` (words of length ≤ 5897)
and defect bound `D = m+a+b+η ≤ 13`.  `lake build Superperm7.CoarsenBridge`
and `lake build Superperm7.Main` both succeed, no `sorry` anywhere; a scratch
`rfl` check confirms the exported definitions unfold to the new constants.

Statements changed (same names unless noted):
- `Registry.lean`: `RegistryCandidate.valid c := c.m + c.a + c.b + c.eta ≤ 13 ∧ …` (was `≤ 12`).
- `Frontier.lean`: `defect_bound_identity` now takes `r+q+p ≤ 134` and concludes `≤ 13`;
  `capped_at_most_5896_iff_loss` → `capped_at_most_5897_iff_loss` (`… ≤ 5897 ↔ 720+r+q+p ≤ 854`);
  `loss_at_most_853_iff` → `loss_at_most_854_iff` (`… ≤ 854 ↔ r+q+p ≤ 134`);
  new `defect_identity : … → r ≤ 120+m → r+q+p = 121 + (m+a+b+eta)`.
- `CheapCover.lean`: `cheap_cover_profile_of_weight_at_most_5889` →
  `cheap_cover_profile_of_weight_at_most_5890` (hyp `routeWeight ≤ 5890`, gives `x.loss ≤ 854`).
- `Structural.lean`: `RouteStructuralCounts.budget : r+q+p ≤ 134` (was 133),
  `RouteStructuralCounts.defect_le : m+a+b+eta ≤ 13` (was 12);
  `routeStructuralCounts_of_weight_at_most_5889` → `…_5890` (hyp `≤ 5890`).
  New lemmas in `namespace RouteStructuralCounts` exposing the exact weight/defect relation:
  `capped_weight_eq : 7 + cappedRouteWeight route = 5763 + z.r + z.q + z.p`,
  `budget_eq_defect : z.r + z.q + z.p = 121 + (z.m+z.a+z.b+z.eta)`,
  `defect_add_le_weight : 5877 + (z.m+z.a+z.b+z.eta) ≤ routeWeight route`,
  `defect_le_of_weight_le : routeWeight route ≤ W → D + 5877 ≤ W`,
  `defect_le_twelve_of_weight_le_5889 : routeWeight route ≤ 5889 → D ≤ 12`.
- `Section4.lean`: `RouteRealizesRegistryCandidate … := c.valid ∧ ∃ _, routeWeight route ≤ 5890 ∧ …`;
  `normalized_light_route_realizes_registryCandidate`, `normalized_light_route_gives_registryCandidate`,
  `light_route_gives_registryCandidate` take/produce `routeWeight ≤ 5890`.
- `CoarsenAux.lean` (`cheap_profile_for_bridge`), `CoarsenBridge.lean`
  (`retained_arc_system_of_structural_counts`, `prepared_coarsening_of_structural_counts`,
  `coarsen_cases_of_structural_counts`): hypothesis `≤ 5889` → `≤ 5890`.
  `coarsen_bridge`, `coarsen_bridge_cases`, `coarsen_bridge_forest` statements unchanged.
- `Path.lean`/`Normalization.lean` untouched (budget-generic).
- No `72`/`73`/`Fin`-sized constants in the reduction layer depended on the defect bound
  (the only `≤ 72`/`< 73` tables are in the off-limits `Elim.lean`), so nothing else moved.

`Main.lean` (the 5897 theorem, which uses `Elim.no_coarsened_instance` with `D ≤ 12`):
`no_realized_registry_candidate` now carries the extra conjunct `c.m+c.a+c.b+c.eta ≤ 12`,
and `no_normalized_hamiltonian_route_of_weight_at_most_5889` feeds weight `≤ 5889 ≤ 5890`
into the pipeline and recovers `D ≤ 12` from `z.defect_le_twelve_of_weight_le_5889`.
`no_hamiltonian_route_of_weight_at_most_5889`, `lower_bound`, `main_theorem` are unchanged.
No off-limits file was modified; `Main98.lean` (already written against `≤ 13`/`5890`) was not touched.

## Final summary

**Status: complete.**  All 20 files in the brief's list build clean with
`lake build Superperm7.<File>`, with **no `sorry`** and no PORT-TODO anywhere:
Path, Normalization, CheapCover, Frontier, GraphRank, Euler, CycleLists, Orbit,
FirstReturn, PermutationMap, Registry, Structural, Section4, Section5Core,
Surgery, Chains, ChainTrails, CoarsenAux, CoarsenAccounting, CoarsenBridge.

`#print axioms` on `coarsen_bridge` and `normalized_light_route_realizes_registryCandidate`
lists only `propext`, `Classical.choice`, `Quot.sound` and `native_decide`
certificates (all single-quantifier over `Perm7`, or `Perm7 × Fin 6/7`, or
`Perm7 × Fin 6³`; nothing pairwise).

**Remaining sorries: none.**

**Total build time** (this machine, mathlib cached): each file 5–70 s; a cold
rebuild of the whole ported chain Path → CoarsenBridge is ≈ 12 min wall; the
sub-chain PermutationMap → CoarsenBridge rebuilt in 4 min 37 s.  No file exceeds
~75 s.  All ten pairwise `native_decide`s of the n=6 code were restated
(see per-file notes) so nothing quantifies over pairs of permutations.

**Exported interface (as specified in the brief):**
```lean
-- Registry.lean
structure RegistryCandidate where m : ℕ; a : ℕ; b : ℕ; eta : ℕ; r : ℕ
def RegistryCandidate.valid c := c.m + c.a + c.b + c.eta ≤ 13 ∧ c.a ≤ c.r ∧ c.r ≤ 6 * c.m ∧ (c.m = 0 → c.r = 0)
def RegistryCandidate.k c := 120 + c.m - c.r + c.a
def RegistryCandidate.tau c := c.eta + 1 + c.b
def RegistryCandidate.u c := 6 * c.m - c.r
-- Section4.lean
def RouteRealizesRegistryCandidate route hroute c :=
  c.valid ∧ ∃ _ : IsNormalizedRoute route, routeWeight route ≤ 5890 ∧
    ∃ z : RouteStructuralCounts route hroute, c.m = z.m ∧ c.a = z.a ∧ c.b = z.b ∧ c.eta = z.eta ∧ c.r = z.r
theorem normalized_light_route_realizes_registryCandidate {route} (hroute) (hnormal)
    (hweight : routeWeight route ≤ 5890) : ∃ c, RouteRealizesRegistryCandidate route hroute c
-- CoarsenBridge.lean
theorem coarsen_bridge_cases : RouteRealizesRegistryCandidate route hroute c →
    (∃ inst : CoarsenedInstance c.k c.tau c.u c.b, 1 ≤ Σ omissionRuns) ∨
    (0 < c.b ∧ Nonempty (CoarsenedInstance c.k c.tau (c.u - 1) c.b)) ∨
    Nonempty (ForestInstance c.k c.tau c.u (c.r - c.a))
theorem coarsen_bridge (h : RouteRealizesRegistryCandidate route hroute c) :
    ∃ u' : ℕ, u' ≤ c.u ∧ Nonempty (CoarsenedInstance c.k c.tau u' c.b)
theorem coarsen_bridge_forest (h) (hb : c.b = 0) : Nonempty (ForestInstance c.k c.tau c.u (c.r - c.a))
-- Path.lean / Normalization.lean (n=6 signatures with 7 for 6)
theorem exact_path_formulation (budget) : (∃ w, IsSuperpermutation w ∧ w.length ≤ 7 + budget) ↔ (∃ route, IsHamiltonianRoute route ∧ routeWeight route ≤ budget)
theorem exists_normalized_route / normalized_route_of_weight_at_most  -- unchanged
```

**Statement deviations from the brief (all equivalent / placement only):**
1. `normalized_light_route_realizes_registryCandidate` is *defined* in
   `Section4.lean` (its natural home, as at n=6) rather than textually in
   `CoarsenBridge.lean`; `CoarsenBridge` imports `Section4`, so
   `import Superperm7.CoarsenBridge` exposes both target theorems with exactly
   the brief's signatures (verified by a scratch check file).
2. `RouteStructuralCounts` has one field beyond the brief's list:
   `p_route : p = highCostCount route + 1`.  With no frontier lift the bridge's
   trail-budget arithmetic needs `#chainTrails ≤ z.p = η+1` directly (at n=6 it
   got this from `r+q+p₀ ≤ 29` and `D = 4`, which does not work with `D ≤ 12`),
   so `z.p` is tied to the route.  Correspondingly `cheap_profile_for_bridge` now
   returns `x.p = z.p` and `coarsened_trail_budget_arithmetic` takes `p₀ ≤ z.p`
   instead of `r+q+p₀ ≤ 29`.
3. Full trichotomy `coarsen_bridge_cases` was ported (it was no harder) and
   `coarsen_bridge` is derived from it; `coarsen_bridge_forest` also kept.
4. The face-fragmentation data (g, h) is dropped from `RegistryCandidate` as
   allowed; the Euler-derived fact is still proved
   (`routeStructuralCounts_hasFaceFragmentation`, and
   `realized_candidate_hasFaceFragmentation : … → ∃ g h, 2g ≤ c.a ∧ c.b + 2g = c.a + h`).
5. Renamed n-numbered lemmas beyond the brief's substitution list:
   `costOneCount_le_six_hundred → costOneCount_le_4320`,
   `cheap_cover_profile_of_weight_at_most_865 → …_5889` (now `…_5890`),
   `routeStructuralCounts_of_weight_at_most_865 → …_5889` (now `…_5890`),
   `runStartSet_card_le_five_mul_touchedBlocks → …_six_mul_…`,
   `rotationPerm7_pow_six → rotationPerm7_pow_seven`, `runReturnTime_le_six → …_le_seven`,
   `gapLen_le_four → gapLen_le_five`, `Row.length_le_five → Row.length_le_six`,
   `F_iterate_four_apply_F → F_iterate_five_apply_F`, `F_apply_iterate_four → …_five`,
   `F_iterate_four_iterate_of_pos → …_five_…`, `F_iterates_fin_five_injective → …_fin_six_…`,
   `fin_five_filter_lt_card → fin_six_filter_lt_card`,
   `registryCandidate_of_faceFragmentation → registryCandidate_of_structuralCounts`.
6. No changes were made to Basic/Rows/RowModel/Coarsen/Compute or any off-limits file;
   nothing was appended to the already-done files.

## Per-file log

| file | status | notes | build time |
|---|---|---|---|
| Path | OK, no sorry | 6→7 only | 42 s |
| Normalization | OK, no sorry | unchanged | 36 s |
| CheapCover | OK, no sorry | constants; `rClass_eq_of_mem`/`R_mem_rClass_of_mem` now via `mem_rClass_iff` + `∀ p, ∀ i : Fin 7` native_decide (5040·7); renamed `costOneCount_le_six_hundred`→`costOneCount_le_4320`, `cheap_cover_profile_of_weight_at_most_865`→`…_5890` (loss ≤ 854, after the 12→13 bump) | 41 s |
| Frontier | OK, no sorry | rewritten/trimmed: `ceilDivSix`, `orbit_inequality_of_counts` (720+r ≤ 6M ⇒ 120+⌈r/6⌉ ≤ r+q), `capped_length_identity`, `defect_bound_identity` (≤ 13 after the bump), `defect_identity`, `face_fragmentation_identity`; lift and profile counts dropped | 5 s |
| GraphRank | OK, no sorry | unchanged | 4 s |
| Euler | OK, no sorry | unchanged | ~60 s |
| CycleLists | OK, no sorry | unchanged | ~10 s |
| Surgery | OK, no sorry | unchanged | ~35 s |
| Orbit | OK, no sorry | constants; `runStartSet_card_le_five_mul_touchedBlocks`→`…_six_mul_…`; orbit inequality now `120 + ceilDivSix r ≤ r + q` | 45 s |
| FirstReturn | OK, no sorry | constants; `rotationPerm7_pow_seven`, `runReturnTime_le_seven`, cycle count 720 | 45 s |
| PermutationMap | OK, no sorry | `fBlock_eq_of_mem` via `mem_fBlock_iff` + `∀ p, ∀ i : Fin 6` native_decide; `touchedState_card = 6*M`; `touchedAPerm_cycleCount = 720 + holes` | 50 s |
| Registry | OK, no sorry | rewritten per brief: `RegistryCandidate {m a b eta r : ℕ}`, `valid`, `k`, `tau`, `u`, `r_le_of_valid`; published family list / counts dropped | 5 s |
| Structural | OK, no sorry | `RouteStructuralCounts`: `runStart_card = 720 + r`, new field `p_route : p = highCostCount route + 1`, `budget : r+q+p ≤ 134` (replaces `frontier`; 133 before the bump), `M_eq : M = 120 + m`, `k_eq : k = 120+m-r+a`, `defect_le : … ≤ 13` (replaces `defect_four`; 12 before the bump), `r_le_six_m`; no frontier lift (z.p is the actual p); `routeStructuralCounts_of_weight_at_most_5890`; `defect_add_le_weight` (5877 + D ≤ weight); `hasFaceFragmentation_of_permutationMap` kept (6*M, 720+…); `registryCandidate_of_faceFragmentation` → `registryCandidate_of_structuralCounts` (no face hypothesis) | 70 s |
| Section4 | OK, no sorry | `RouteRealizesRegistryCandidate` exactly as in brief (c.m = z.m ∧ …); `normalized_light_route_realizes_registryCandidate` with the brief's signature lives here (CoarsenBridge imports it); added documentary `realized_candidate_hasFaceFragmentation` | 35 s |
| Section5Core | OK, no sorry | `gapComplementRow (holes : Fin 6)`, lengthCode `5 - holes`, lastState `F^[5]`; `gapComplementRow_beta_of_F_eq` now proved from single-quantifier `gapComplementRow_beta_F : ∀ a holes, (gapComplementRow (F a) holes).beta = …` (5040·6) | 45 s |
| Chains | OK, no sorry | `R^[6]`/`R_order_seven`; `cost_three_iff_endpoint_compatible` proved structurally via `d_eq_iff_compatible` (no native_decide) | 45 s |
| ChainTrails | OK, no sorry | `gapLen_le_four`→`gapLen_le_five`, `gapLenFin : Fin 6` | 35 s |
| CoarsenAux | OK, no sorry | dropped `open Section57Closure`; `F_iterate_five_apply_F`; omitted positions `Fin 6`; `Row.length_le_six`; `cheap_profile_for_bridge` now gives `x.p = z.p` via `p_route`; `coarsened_trail_budget_arithmetic` takes `p₀ ≤ z.p`; holes `6*z.m - z.r` | 35 s |
| CoarsenAccounting | OK, no sorry | `Fin 6`, `F^[5]`, `6 -`, `6*z.m`; the five small native_decides renamed (`…fin_six…`, `F_apply_iterate_five`, `F_iterate_five_iterate_of_pos`, `F_cut_interval_disjoint` over 5040·6³); `MarkedRow.omissionRuns_pos_of_nonempty` reproved structurally (least omitted index starts a run) instead of via the n=6 `two_runs_unique_pattern` | 40 s |
| CoarsenBridge | OK, no sorry | weight 5890 (was 5889); trail budget via `trails₀.length ≤ z.p`; `coarsen_bridge_cases`/`coarsen_bridge`/`coarsen_bridge_forest` restated over `c.k c.tau c.u c.b` (and `c.r - c.a`); `coarsen_bridge` is the brief's `∃ u' ≤ c.u, Nonempty (CoarsenedInstance c.k c.tau u' c.b)` | 45 s |
