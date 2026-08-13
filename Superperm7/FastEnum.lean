/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE).
Authors: Claude (Anthropic).
-/
import Superperm7.FastSearchSound

/-!
# Enumerating all optimal trails (with provenance)

A variant of the fast kernel that, instead of stopping at the first trail
reaching `target` rows, *collects* every such trail as the list of its rows'
provenance records `(start word code, length code, omission bits)`.  The
completeness theorem says: every model trail with at most `mu` marked rows,
charge `≤ g`, exactly `target` rows and first start `1` has its provenance
list in the output.  (Pruning uses valid caps exactly as in `fsearch`.)
-/

namespace Superperm7

open Mirror

/-- provenance of a row: base-8 code of the start word, length code, omission bits -/
structure Prov where
  wc : Nat
  lc : Nat
  om : Nat
  deriving DecidableEq, Repr, Hashable

/-- candidate together with its provenance -/
structure PCand where
  c : Cand
  p : Prov
  deriving DecidableEq, Repr

def mkPCandW (w : W) (L om : Nat) : PCand := ⟨mkCandW w L om, ⟨wcode w, L, om⟩⟩

def pcands : Array (Array PCand) := Id.run do
  let mut t : Array (Array PCand) := Array.replicate 840 #[]
  for w in allWords do
    let h := headIdW w
    for L in [0:6] do
      for om in allowedOmissionBitsN L do
        t := t.set! h (t[h]!.push (mkPCandW w L om))
  return t

def startPCands : Array PCand :=
  ((List.range 6).flatMap fun L => (allowedOmissionBitsN L).map fun om => mkPCandW idWord L om).toArray

namespace Fast

/-- collect all continuations reaching `target`; `acc` is the reversed provenance prefix -/
def fenumFrom (caps : Array Nat) (g target mu : Nat) :
    Nat → Nat → BitSet → BitSet → Nat → Nat → Nat → List Prov → List (List Prov)
  | 0, _, _, _, _, _, _, _ => []
  | fuel + 1, head, cs, bs, rows, holes, marks, acc =>
      if target ≤ rows then [acc.reverse]
      else
        (pcands.getD head #[]).toList.flatMap fun pc =>
          match tryCand caps g target mu cs bs rows holes marks pc.c with
          | none => []
          | some holes' =>
              fenumFrom caps g target mu fuel pc.c.beta (insertAll cs pc.c) (bs.insert pc.c.block)
                (rows + 1) holes' (if pc.c.marked then marks + 1 else marks) (pc.p :: acc)

/-- all normalized (first start = identity) trails with `≤ mu` marks, charge `≤ g`,
reaching `target` rows (as provenance lists of length `target`) -/
def fenum (caps : Array Nat) (g target mu fuel : Nat) : List (List Prov) :=
  startPCands.toList.flatMap fun pc =>
    match tryCand caps g target mu emptyClasses emptyBlocks 0 0 0 pc.c with
    | none => []
    | some holes' =>
        fenumFrom caps g target mu fuel pc.c.beta (insertAll emptyClasses pc.c) (emptyBlocks.insert pc.c.block)
          1 holes' (if pc.c.marked then 1 else 0) [pc.p]

end Fast

/-! ## Completeness -/

def prov (x : MarkedRow) : Prov :=
  ⟨wcode (permWord x.row.start), x.row.lengthCode.val, omittedBits x.omitted⟩

def pencode (x : MarkedRow) : PCand := ⟨fencode x, prov x⟩

theorem mkPCandW_mem_pcands : ∀ (p : Perm7) (L : Fin 6), ∀ om ∈ allowedOmissionBits L,
    mkPCandW (permWord p) L.val om ∈ pcands.getD (headId p) #[] := by
  native_decide

theorem pencode_mem_pcands (x : MarkedRow) (hx : Admissible x) :
    pencode x ∈ pcands.getD (headId x.row.start) #[] :=
  mkPCandW_mem_pcands x.row.start x.row.lengthCode (omittedBits x.omitted) (omittedBits_of_admissible x hx)

theorem mkPCandW_mem_startPCands : ∀ (L : Fin 6), ∀ om ∈ allowedOmissionBits L,
    mkPCandW (permWord 1) L.val om ∈ startPCands := by
  native_decide

theorem pencode_mem_startPCands (x : MarkedRow) (hx : Admissible x) (hstart : x.row.start = 1) :
    pencode x ∈ startPCands := by
  have := mkPCandW_mem_startPCands x.row.lengthCode (omittedBits x.omitted) (omittedBits_of_admissible x hx)
  unfold pencode fencode mkCand prov
  rw [hstart]
  exact this

theorem pencode_c (x : MarkedRow) : (pencode x).c = fencode x := rfl
theorem pencode_p (x : MarkedRow) : (pencode x).p = prov x := rfl

/-- Completeness of `fenumFrom`: the provenance list of any model continuation
reaching exactly `target` rows appears in the output. -/
theorem fenumFrom_complete (caps : Array Nat) (g target mu : Nat) (hcaps : CapsValidMuBelow mu caps g) :
    ∀ (xs done : List MarkedRow) (fuel head : Nat) (cs bs : BitSet) (holes marks : Nat) (acc : List Prov),
      ModelTrail (done ++ xs) →
      Represents cs bs done →
      (∀ x, xs.head? = some x → headId x.row.start = head) →
      holes + chargeSum xs ≤ g →
      marks + markCount xs ≤ mu →
      target = done.length + xs.length →
      xs.length + 1 ≤ fuel →
      acc.reverse ++ xs.map prov ∈
        Fast.fenumFrom caps g target mu fuel head cs bs done.length holes marks acc := by
  intro xs
  induction xs with
  | nil =>
      intro done fuel head cs bs holes marks acc _ _ _ _ _ htarget hlen
      cases fuel with
      | zero => simp at hlen
      | succ fuel =>
          simp only [List.length_nil, Nat.add_zero] at htarget
          simp [Fast.fenumFrom, htarget]
  | cons x rest ih =>
      intro done fuel head cs bs holes marks acc hmodel hrep hhead hcharge hmarks htarget hlen
      cases fuel with
      | zero => simp at hlen
      | succ fuel =>
          have hnot : ¬ target ≤ done.length := by simp at htarget; omega
          have hx : Admissible x := hmodel.1 x (by simp)
          have hcand := pencode_mem_pcands x hx
          rw [hhead x rfl] at hcand
          simp only [chargeSum_cons] at hcharge
          rw [markCount_cons] at hmarks
          simp only [List.length_cons] at htarget hlen
          have hdis := pairwise_snoc hmodel.2.2
          obtain ⟨hblk, hfree⟩ := free_of_disjoint hrep x hdis
          have hrestModel : ModelTrail rest := by
            have hsuf : ModelTrail (x :: rest) :=
              ⟨fun y hy => hmodel.1 y (by simp [hy]),
               hmodel.2.1.suffix (List.suffix_append done (x :: rest)),
               hmodel.2.2.sublist (List.sublist_append_right done (x :: rest))⟩
            exact modelTrail_tail hsuf
          have hadmit : Fast.admit caps g target done.length holes (fencode x).charge =
              some (holes + (fencode x).charge) := by
            apply admit_isSome' (rest := rest.length)
            · rw [fencode_charge x hx]; omega
            · omega
            · intro rem hrem hlt
              have hvalid := hcaps rem hlt rest hrestModel (by omega) (by rw [fencode_charge x hx] at hrem; omega)
              exact le_getD_of_le_getD_zero hvalid
          have htry : Fast.tryCand caps g target mu cs bs done.length holes marks (fencode x) =
              some (holes + (fencode x).charge) := by
            unfold Fast.tryCand
            rw [fencode_marked]
            have hm : ¬ (isMarked x && decide (mu ≤ marks)) = true := by
              cases hxm : isMarked x
              · simp
              · simp only [hxm, ↓reduceIte] at hmarks; simp; omega
            rw [if_neg hm, hblk, if_neg (by simp), hfree, if_neg (by simp), hadmit]
          have hrec := ih (done ++ [x]) fuel (fencode x).beta (Fast.insertAll cs (fencode x))
            (bs.insert (fencode x).block) (holes + (fencode x).charge)
            (if (fencode x).marked then marks + 1 else marks) (prov x :: acc)
            (by simpa using hmodel)
            (represents_step hrep x)
            (by
              intro y hy
              cases rest with
              | nil => simp at hy
              | cons y' rest' =>
                  simp only [List.head?_cons, Option.some.injEq] at hy
                  rw [← hy]
                  have hchain := hmodel.2.1
                  have : (x :: y' :: rest').IsChain MarkedCompatible :=
                    (hchain.suffix (List.suffix_append done (x :: y' :: rest')))
                  exact headId_eq_fbeta_of_compatible (List.isChain_cons_cons.mp this).1)
            (by rw [fencode_charge x hx]; omega)
            (by rw [fencode_marked]; split <;> simp_all <;> omega)
            (by simp; omega)
            (by omega)
          simp only [List.length_append, List.length_singleton, List.reverse_cons, List.append_assoc,
            List.singleton_append] at hrec
          simp only [Fast.fenumFrom, hnot, ↓reduceIte, List.mem_flatMap, List.map_cons]
          refine ⟨pencode x, ?_, ?_⟩
          · rw [Array.mem_toList_iff]; exact hcand
          · rw [pencode_c, htry]
            simpa using hrec

theorem fenum_complete (caps : Array Nat) (g target mu fuel : Nat)
    (hcaps : CapsValidMuBelow mu caps g)
    (rows : List MarkedRow) (hmodel : ModelTrail rows) (hmarks : markCount rows ≤ mu)
    (hfirst : ∀ x, rows.head? = some x → x.row.start = 1)
    (hcharge : chargeSum rows ≤ g)
    (htarget : target = rows.length) (hpos : 0 < target)
    (hlen : rows.length ≤ fuel) :
    rows.map prov ∈ Fast.fenum caps g target mu fuel := by
  cases rows with
  | nil => simp at htarget; omega
  | cons x rest =>
      have hx : Admissible x := hmodel.1 x (by simp)
      have hstart : x.row.start = 1 := hfirst x rfl
      have hmem := pencode_mem_startPCands x hx hstart
      obtain ⟨hblk, hfree⟩ := free_of_disjoint represents_empty x (by simp)
      simp only [chargeSum_cons] at hcharge
      rw [markCount_cons] at hmarks
      simp only [List.length_cons] at htarget hlen
      have hrestModel : ModelTrail rest := modelTrail_tail hmodel
      have hadmit : Fast.admit caps g target 0 0 (fencode x).charge = some (0 + (fencode x).charge) := by
        apply admit_isSome' (rest := rest.length)
        · rw [fencode_charge x hx]; omega
        · omega
        · intro rem hrem hlt
          have hvalid := hcaps rem hlt rest hrestModel (by omega) (by rw [fencode_charge x hx] at hrem; omega)
          exact le_getD_of_le_getD_zero hvalid
      have htry : Fast.tryCand caps g target mu Fast.emptyClasses Fast.emptyBlocks 0 0 0 (fencode x) =
          some (0 + (fencode x).charge) := by
        unfold Fast.tryCand
        rw [fencode_marked]
        have hm : ¬ (isMarked x && decide (mu ≤ 0)) = true := by
          cases hxm : isMarked x
          · simp
          · simp only [hxm, ↓reduceIte] at hmarks; simp; omega
        rw [if_neg hm, hblk, if_neg (by simp), hfree, if_neg (by simp), hadmit]
      have hrec := fenumFrom_complete caps g target mu hcaps rest [x] fuel (fencode x).beta
        (Fast.insertAll Fast.emptyClasses (fencode x)) (Fast.emptyBlocks.insert (fencode x).block)
        (0 + (fencode x).charge) (if (fencode x).marked then 1 else 0) [prov x]
        (by simpa using hmodel)
        (by simpa using represents_step represents_empty x)
        (by
          intro y hy
          cases rest with
          | nil => simp at hy
          | cons y' rest' =>
              simp only [List.head?_cons, Option.some.injEq] at hy
              rw [← hy]
              exact headId_eq_fbeta_of_compatible (List.isChain_cons_cons.mp hmodel.2.1).1)
        (by rw [fencode_charge x hx]; omega)
        (by rw [fencode_marked]; split <;> simp_all <;> omega)
        (by simp; omega)
        (by omega)
      simp only [List.length_singleton, List.reverse_singleton, List.singleton_append] at hrec
      simp only [Fast.fenum, List.mem_flatMap, List.map_cons]
      refine ⟨pencode x, ?_, ?_⟩
      · rw [Array.mem_toList_iff]; exact hmem
      · rw [pencode_c, htry]
        simpa using hrec

end Superperm7
