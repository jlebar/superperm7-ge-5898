#!/usr/bin/env python3
"""HISTORICAL / UNTRUSTED helper, kept for transparency; not needed to check the proof and not runnable
from this repository as-is (it drove a `fasttable` executable and read a table file that live in the
development tree, not here).

Generate the sharded certificate Lean files for capTab0 (mu=0, g<=56), capTab1 (mu=1, g<=54),
capTab2 (mu=2, g<=46)."""
import subprocess, math, re, os, json
ROOT = os.path.dirname(os.path.abspath(__file__))
EXE = os.path.join(ROOT, ".lake/build/bin/fasttable")
tab = [int(re.match(r"M\((\d+)\) = (\d+)", l).group(2)) for l in open(os.path.join(ROOT, "../work/M7_exact.log")) if re.match(r"M\((\d+)\)", l)]

# plan: mu -> (G, batch_upto, {level: k_shards})
PLAN = {
    0: dict(G=56, batches=[(0, 49)], shards={54: 4, 56: 8}),
    1: dict(G=54, batches=[(0, 40), (41, 44)], shards={50: 4, 51: 15, 52: 35, 53: 30, 54: 120}),
    2: dict(G=46, batches=[(0, 37), (38, 40)], shards={41: 3, 42: 8, 43: 4, 44: 7, 45: 6, 46: 4}),
}
CACHE = os.path.join(ROOT, "frontier_sizes.json")
sizes = json.load(open(CACHE)) if os.path.exists(CACHE) else {}

def frontier_size(mu, g, d):
    key = f"{mu},{g},{d}"
    if key not in sizes:
        out = subprocess.run([EXE, "frontier", str(mu), str(g), str(d)], capture_output=True, text=True).stdout
        m = re.search(r"\|frontier\| = (\d+)", out)
        sizes[key] = int(m.group(1))
        json.dump(sizes, open(CACHE, "w"))
    return sizes[key]

def w(path, s):
    os.makedirs(os.path.dirname(path), exist_ok=True)
    open(path, "w").write(s)

for mu, plan in PLAN.items():
    G = plan["G"]; cap = f"capTab{mu}"
    ns = f"Superperm7.Cert.M{mu}"
    d_imports = []
    level_thm = {}   # g -> fully qualified theorem name proving fsearch cap g (cap.getD g 0 + 1) mu (cap.getD g 0 + 1) = false
    # batches
    for (a, b) in plan["batches"]:
        name = f"B{a:02d}_{b:02d}"
        w(f"{ROOT}/Superperm7/Cert/M{mu}/{name}.lean", f'''import Superperm7.CapTabs

namespace {ns}

/-- levels {a}..{b}: each failed search, checked in one batch -/
theorem chk_{a}_{b} : ((List.range ({b} + 1)).drop {a}).all (fun g =>
    Fast.fsearch {cap} g ({cap}.getD g 0 + 1) {mu} ({cap}.getD g 0 + 1) == false) = true := by
  native_decide

theorem lvl_of_batch_{a}_{b} (g : ℕ) (ha : {a} ≤ g) (hb : g ≤ {b}) :
    Fast.fsearch {cap} g ({cap}.getD g 0 + 1) {mu} ({cap}.getD g 0 + 1) = false := by
  have h := chk_{a}_{b}
  rw [List.all_eq_true] at h
  have := h g (by rw [List.mem_iff_getElem]; refine ⟨g - {a}, by simp; omega, ?_⟩; simp [List.getElem_drop]; try omega)
  simpa using this

end {ns}
''')
        d_imports.append(f"Superperm7.Cert.M{mu}.{name}")
        for g in range(a, b + 1):
            level_thm[g] = (f"lvl_of_batch_{a}_{b} {g} (by norm_num) (by norm_num)")
    # single and sharded levels
    covered = set(g for (a, b) in plan["batches"] for g in range(a, b + 1))
    for g in range(0, G + 1):
        if g in covered: continue
        T = tab[g] + 1
        if g not in plan["shards"]:
            name = f"L{g:02d}"
            w(f"{ROOT}/Superperm7/Cert/M{mu}/{name}.lean", f'''import Superperm7.CapTabs

namespace {ns}

theorem lvl{g} : Fast.fsearch {cap} {g} ({cap}.getD {g} 0 + 1) {mu} ({cap}.getD {g} 0 + 1) = false := by
  native_decide

end {ns}
''')
            d_imports.append(f"Superperm7.Cert.M{mu}.{name}")
            level_thm[g] = f"lvl{g}"
        else:
            k = plan["shards"][g]
            d = 14 if k <= 10 else 16
            L = frontier_size(mu, g, d)
            n = math.ceil(L / k)
            k = math.ceil(L / n)
            fuel = T - d
            assert fuel > 0 and d + 1 < T
            shard_names = []
            for i in range(k):
                sname = f"L{g:02d}S{i:03d}"
                w(f"{ROOT}/Superperm7/Cert/M{mu}/{sname}.lean", f'''import Superperm7.CapTabs

namespace {ns}

/-- shard {i}/{k} of level {g} (mu = {mu}): frontier depth {d}, states [{n*i}, {n*i+n}) -/
theorem sh{g}_{i} : Fast.shardOK {cap} {g} {T} {mu} {d} {fuel} ({n} * {i}) {n} = true := by
  native_decide

end {ns}
''')
                shard_names.append(sname)
            imports = "\n".join(f"import Superperm7.Cert.M{mu}.{s}" for s in shard_names)
            cases = "\n".join(f"  · exact sh{g}_{i}" for i in range(k))
            w(f"{ROOT}/Superperm7/Cert/M{mu}/L{g:02d}.lean", f'''{imports}

namespace {ns}

theorem cover{g} : (Fast.frontier {cap} {g} {T} {mu} {d}).length ≤ {n} * {k} := by native_decide

theorem lvl{g}_lit : Fast.fsearch {cap} {g} {T} {mu} ({fuel} + {d}) = false := by
  apply Fast.fsearch_false_of_shards {cap} {g} {T} {mu} {d} {fuel} {n} {k} (by norm_num) (by norm_num) cover{g}
  intro i hi
  interval_cases i
{cases}

theorem lvl{g} : Fast.fsearch {cap} {g} ({cap}.getD {g} 0 + 1) {mu} ({cap}.getD {g} 0 + 1) = false := by
  have h : {cap}.getD {g} 0 + 1 = {T} := by decide
  rw [h]
  exact lvl{g}_lit

end {ns}
''')
            d_imports.append(f"Superperm7.Cert.M{mu}.L{g:02d}")
            level_thm[g] = f"lvl{g}"
            print(f"mu={mu} g={g}: T={T} d={d} |frontier|={L} n={n} k={k}")
    # assembly
    steps = []
    steps.append(f'''theorem valid_le (g : ℕ) (hg : g ≤ {G}) : CapValidMuAt {mu} {cap} g := by
  induction g using Nat.strong_induction_on with
  | _ g ih =>
      have hbelow : CapsValidMuBelow {mu} {cap} g := fun g' hg' => ih g' hg' (by omega)
      apply capValidMu_step {cap} {mu} g hbelow
      interval_cases g''')
    for g in range(0, G + 1):
        steps.append(f"      · exact {level_thm[g]}")
    imports = "\n".join(f"import {m}" for m in d_imports)
    w(f"{ROOT}/Superperm7/Cert/M{mu}.lean", f'''{imports}

/-!
# Certified capacity table `{cap}` (at most {mu} marked row{"s" if mu != 1 else ""}), charges `0 … {G}`
-/

namespace {ns}

{chr(10).join(steps)}

end {ns}

namespace Superperm7

/-- Every model trail with at most `{mu}` marked rows and charge `≤ g ≤ {G}` has at most `{cap}[g]` rows. -/
theorem {cap}_valid (g : ℕ) (hg : g ≤ {G}) : CapValidMuAt {mu} {cap} g := Cert.M{mu}.valid_le g hg

end Superperm7
''')
print("done; sizes:", sizes)
