/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE); this file is
additionally subject to the upstream MIT notice below.

Adapted from https://github.com/BGray-wrl/superperm6
  file:   formal-verification/Superperm6/Surgery.lean
  commit: d8a932d8f61d80b0bcfc737bd0e235a8300449c4
  upstream copyright: Copyright (c) 2026 Benjamin Grayzel — MIT License (reproduced in NOTICE).
Local modifications (port from six to seven symbols; see docs/PORT_LOG.md): namespace and permutation type only.
-/
import Superperm7.Rows

/-!
# Abstract safe cyclic surgery

This file contains the list-combinatorial surgery argument used by the
Section 5--7 bridge.  A trail system is encoded temporarily as a list of
optional arcs.  The value `none` is a trail break.  With this encoding the
safe merge

```
P, x, W, y, R  ↦  W, break, P, x ++ y, R
```

preserves every old adjacency that is still exposed and adds exactly one
trail break.
-/

namespace Superperm7

open List

section TrailEncoding

variable {γ : Type*}

/-- Lift a relation to a list with explicit breaks.  A relation is required
only when both neighboring tokens are genuine items. -/
def BrokenRel (r : γ → γ → Prop) : Option γ → Option γ → Prop
  | some x, some y => r x y
  | _, _ => True

/-- Encode every trail with a trailing `none` delimiter. -/
def delimit : List (List γ) → List (Option γ)
  | [] => []
  | trail :: trails => trail.map some ++ none :: delimit trails

/-- Read a delimited token list back into trails. -/
def undelimit : List (Option γ) → List (List γ)
  | [] => []
  | none :: tokens => [] :: undelimit tokens
  | some x :: tokens =>
      match undelimit tokens with
      | [] => [[x]]
      | trail :: trails => (x :: trail) :: trails

/-- The genuine items in a broken token list. -/
def tokenItems (tokens : List (Option γ)) : List γ :=
  tokens.filterMap id

/-- The number of explicit trail breaks. -/
def breakCount (tokens : List (Option γ)) : ℕ :=
  tokens.countP Option.isNone

@[simp] theorem tokenItems_nil : tokenItems ([] : List (Option γ)) = [] := rfl

@[simp] theorem tokenItems_cons_none (tokens : List (Option γ)) :
    tokenItems (none :: tokens) = tokenItems tokens := rfl

@[simp] theorem tokenItems_cons_some (x : γ) (tokens : List (Option γ)) :
    tokenItems (some x :: tokens) = x :: tokenItems tokens := rfl

@[simp] theorem tokenItems_append (u v : List (Option γ)) :
    tokenItems (u ++ v) = tokenItems u ++ tokenItems v := by
  simp [tokenItems]

@[simp] theorem mem_tokenItems_iff {x : γ} {tokens : List (Option γ)} :
    x ∈ tokenItems tokens ↔ some x ∈ tokens := by
  induction tokens with
  | nil => simp
  | cons token tokens ih =>
      cases token <;> simp [ih]

@[simp] theorem tokenItems_map_some (items : List γ) :
    tokenItems (items.map some) = items := by
  induction items <;> simp [tokenItems, *]

@[simp] theorem breakCount_nil : breakCount ([] : List (Option γ)) = 0 := rfl

@[simp] theorem breakCount_cons_none (tokens : List (Option γ)) :
    breakCount (none :: tokens) = breakCount tokens + 1 := by
  simp [breakCount]

@[simp] theorem breakCount_cons_some (x : γ) (tokens : List (Option γ)) :
    breakCount (some x :: tokens) = breakCount tokens := by
  simp [breakCount]

@[simp] theorem breakCount_append (u v : List (Option γ)) :
    breakCount (u ++ v) = breakCount u + breakCount v := by
  simp [breakCount, List.countP_append]

@[simp] theorem breakCount_map_some (items : List γ) :
    breakCount (items.map some) = 0 := by
  induction items <;> simp [breakCount, *]

@[simp] theorem tokenItems_delimit (trails : List (List γ)) :
    tokenItems (delimit trails) = trails.flatten := by
  induction trails with
  | nil => rfl
  | cons trail trails ih =>
      simp [delimit, ih]

@[simp] theorem breakCount_delimit (trails : List (List γ)) :
    breakCount (delimit trails) = trails.length := by
  induction trails with
  | nil => rfl
  | cons trail trails ih =>
      simp [delimit, ih]

theorem delimit_ends_in_none {trails : List (List γ)} (htrails : trails ≠ []) :
    (delimit trails).getLast? = some none := by
  induction trails with
  | nil => exact (htrails rfl).elim
  | cons trail trails ih =>
      cases trails with
      | nil => simp [delimit]
      | cons next rest =>
          change (trail.map some ++ none :: delimit (next :: rest)).getLast? =
            some none
          rw [List.getLast?_append_of_ne_nil _ (by simp)]
          rw [List.getLast?_cons_of_ne_nil (by simp [delimit])]
          exact ih (by simp)

theorem isChain_delimit {r : γ → γ → Prop} {trails : List (List γ)}
    (hchains : ∀ trail ∈ trails, trail.IsChain r) :
    (delimit trails).IsChain (BrokenRel r) := by
  induction trails with
  | nil => exact .nil
  | cons trail trails ih =>
      have htrail : (trail.map some).IsChain (BrokenRel r) := by
        rw [List.isChain_map]
        exact (hchains trail (by simp)).imp fun _ _ h => h
      have hleft : (trail.map some ++ [none]).IsChain (BrokenRel r) := by
        apply htrail.append (.singleton none)
        simp [BrokenRel]
      have hright : (none :: delimit trails).IsChain (BrokenRel r) := by
        apply (ih fun t ht => hchains t (by simp [ht])).cons
        simp [BrokenRel]
      change (trail.map some ++ none :: delimit trails).IsChain (BrokenRel r)
      exact List.isChain_split.mpr ⟨hleft, hright⟩

@[simp] theorem tokenItems_undelimit (tokens : List (Option γ)) :
    (undelimit tokens).flatten = tokenItems tokens := by
  induction tokens with
  | nil => rfl
  | cons token tokens ih =>
      cases token with
      | none => simp [undelimit, ih]
      | some x =>
          simp only [undelimit, tokenItems_cons_some]
          cases h : undelimit tokens with
          | nil =>
              simp only [flatten_cons, flatten_nil, append_nil]
              simpa [h] using congrArg (fun xs => x :: xs) ih
          | cons trail trails =>
              simp only [h, flatten_cons] at ih ⊢
              simp [ih]

theorem undelimit_ne_nil_of_ends_in_none {tokens : List (Option γ)}
    (hend : tokens.getLast? = some none) :
    undelimit tokens ≠ [] := by
  intro h
  cases tokens with
  | nil => simp at hend
  | cons token tokens =>
      cases token with
      | none => simp [undelimit] at h
      | some x =>
          cases hdecode : undelimit tokens <;> simp [undelimit, hdecode] at h

theorem length_undelimit_of_ends_in_none {tokens : List (Option γ)}
    (hend : tokens.getLast? = some none) :
    (undelimit tokens).length = breakCount tokens := by
  induction tokens with
  | nil => simp at hend
  | cons token tokens ih =>
      cases token with
      | none =>
          by_cases hnil : tokens = []
          · subst tokens
            rfl
          · have htail : tokens.getLast? = some none := by
              simpa [List.getLast?_cons_of_ne_nil hnil] using hend
            simp [undelimit, breakCount, ih htail]
      | some x =>
          have hnil : tokens ≠ [] := by
            intro h
            subst tokens
            simp at hend
          have htail : tokens.getLast? = some none := by
            simpa [List.getLast?_cons_of_ne_nil hnil] using hend
          obtain ⟨trail, trails, hdecode⟩ :=
            List.exists_cons_of_ne_nil (undelimit_ne_nil_of_ends_in_none htail)
          have hlen := ih htail
          rw [hdecode] at hlen
          simpa [undelimit, hdecode, breakCount] using hlen

theorem chains_undelimit {r : γ → γ → Prop} {tokens : List (Option γ)}
    (hchain : tokens.IsChain (BrokenRel r)) :
    ∀ trail ∈ undelimit tokens, trail.IsChain r := by
  induction hchain with
  | nil => simp [undelimit]
  | singleton token =>
      cases token <;> simp [undelimit]
  | @cons_cons x y tokens hxy htail ih =>
      cases x with
      | none => simpa [undelimit] using ih
      | some x =>
          cases y with
          | none =>
              simp only [undelimit]
              simp only [undelimit] at ih
              simpa using ih
          | some y =>
              simp only [BrokenRel] at hxy
              simp only [undelimit] at ih ⊢
              cases hdecode : undelimit tokens with
              | nil =>
                  simp only [hdecode] at ih ⊢
                  simp [hxy]
              | cons trail trails =>
                  simp only [hdecode] at ih ⊢
                  intro t ht
                  rw [mem_cons] at ht
                  rcases ht with rfl | ht
                  · exact (ih _ (by simp)).cons_cons hxy
                  · exact ih t (by simp [ht])

end TrailEncoding

section ArcEndpoints

variable {α : Type*}

/-- The exposed first endpoint of a possibly empty arc. -/
def arcStart (A : α → Triple) (arc : List α) : Option Triple :=
  arc.head?.map A

/-- The exposed last endpoint of a possibly empty arc. -/
def arcEnd (B : α → Triple) (arc : List α) : Option Triple :=
  arc.getLast?.map B

/-- Endpoint compatibility for two arcs.  All arcs used by surgery are
nonempty, so this is precisely `B(last x) = A(head y)`. -/
def ArcCompatible (A B : α → Triple) (x y : List α) : Prop :=
  arcEnd B x = arcStart A y

theorem arcCompatible_iff_getLast_head (A B : α → Triple)
    {x y : List α} (hx : x ≠ []) (hy : y ≠ []) :
    ArcCompatible A B x y ↔
      B (x.getLast hx) = A (y.head hy) := by
  unfold ArcCompatible arcEnd arcStart
  rw [List.getLast?_eq_getLast_of_ne_nil hx,
    List.head?_eq_some_head hy]
  simp

theorem arcCompatible_iff_getLast!_head! [Inhabited α]
    (A B : α → Triple) {x y : List α}
    (hx : x ≠ []) (hy : y ≠ []) :
    ArcCompatible A B x y ↔ B x.getLast! = A y.head! := by
  rw [arcCompatible_iff_getLast_head A B hx hy]
  have hxLast : x.getLast! = x.getLast hx :=
    List.getLast!_of_getLast?
      (List.getLast?_eq_getLast_of_ne_nil hx)
  have hyHead : y.head! = y.head hy :=
    List.head!_of_head? (List.head?_eq_some_head hy)
  rw [hxLast, hyHead]

theorem arcStart_append_of_ne_nil (A : α → Triple) {x y : List α}
    (hx : x ≠ []) :
    arcStart A (x ++ y) = arcStart A x := by
  cases x with
  | nil => exact (hx rfl).elim
  | cons a x => simp [arcStart]

theorem arcEnd_append_of_ne_nil (B : α → Triple) (x : List α) {y : List α}
    (hy : y ≠ []) :
    arcEnd B (x ++ y) = arcEnd B y := by
  simp [arcEnd, List.getLast?_append_of_ne_nil x hy]

theorem ArcCompatible.merge_left (A B : α → Triple)
    {q x y : List α} (hx : x ≠ [])
    (h : ArcCompatible A B q x) :
    ArcCompatible A B q (x ++ y) := by
  rw [ArcCompatible, arcStart_append_of_ne_nil A hx]
  exact h

theorem ArcCompatible.merge_right (A B : α → Triple)
    {x y q : List α} (hy : y ≠ [])
    (h : ArcCompatible A B y q) :
    ArcCompatible A B (x ++ y) q := by
  rw [ArcCompatible, arcEnd_append_of_ne_nil B x hy]
  exact h

end ArcEndpoints

section SafeSplice

variable {γ : Type*} {r : γ → γ → Prop}

/-- The token-level safe splice.  It is valid whenever the new item has the
same incoming behavior as `x` and the same outgoing behavior as `y`. -/
theorem brokenRel_safe_splice
    {P W R : List (Option γ)} {x y z : γ}
    (hchain :
      (P ++ (some x :: (W ++ (some y :: R)))).IsChain (BrokenRel r))
    (hin : ∀ q, r q x → r q z)
    (hout : ∀ q, r y q → r z q) :
    (W ++ (none :: (P ++ (some z :: R)))).IsChain (BrokenRel r) := by
  have hsplitX :=
    (List.isChain_split (R := BrokenRel r) (l₁ := P) (c := some x)
      (l₂ := W ++ some y :: R)).mp hchain
  have hsplitY :=
    (List.isChain_cons_split (R := BrokenRel r) (a := some x)
      (c := some y) (l₁ := W) (l₂ := R)).mp hsplitX.2
  have hW : W.IsChain (BrokenRel r) := by
    simpa using hsplitY.1.tail.dropLast
  have hP : P.IsChain (BrokenRel r) :=
    hsplitX.1.left_of_append
  have hPz : (P ++ [some z]).IsChain (BrokenRel r) := by
    apply hP.append (.singleton (some z))
    intro q hq _ hz
    simp at hz
    subst hz
    have hold := (List.isChain_append.mp hsplitX.1).2.2 q hq (some x) (by simp)
    cases q with
    | none => trivial
    | some q => exact hin q hold
  have hyR : (some y :: R).IsChain (BrokenRel r) := hsplitY.2
  have hzR : (some z :: R).IsChain (BrokenRel r) := by
    apply hyR.tail.cons
    intro q hq
    have hold := hyR.rel_head? hq
    cases q with
    | none => trivial
    | some q => exact hout q hold
  have hmain : (P ++ some z :: R).IsChain (BrokenRel r) :=
    List.isChain_split.mpr ⟨hPz, hzR⟩
  have hleft : (W ++ [none]).IsChain (BrokenRel r) := by
    apply hW.append (.singleton none)
    simp [BrokenRel]
  have hright : (none :: P ++ some z :: R).IsChain (BrokenRel r) := by
    apply hmain.cons
    simp [BrokenRel]
  exact (List.isChain_split (R := BrokenRel r) (l₁ := W)
    (c := none) (l₂ := P ++ (some z :: R))).mpr ⟨hleft, hright⟩

theorem arc_safe_splice {α : Type*} (A B : α → Triple)
    {P W R : List (Option (List α))} {x y : List α}
    (hx : x ≠ []) (hy : y ≠ [])
    (hchain :
      (P ++ (some x :: (W ++ (some y :: R)))).IsChain
        (BrokenRel (ArcCompatible A B))) :
    (W ++ (none :: (P ++ (some (x ++ y) :: R)))).IsChain
      (BrokenRel (ArcCompatible A B)) := by
  apply brokenRel_safe_splice hchain
  · intro q h
    exact h.merge_left A B hx
  · intro q h
    exact h.merge_right A B hy

end SafeSplice

section SafePair

variable {γ : Type*} [DecidableEq γ]

omit [DecidableEq γ] in
theorem nodup_of_nodup_flatten_of_ne_nil
    {parts : List (List γ)}
    (hflat : parts.flatten.Nodup)
    (hne : ∀ part ∈ parts, part ≠ []) :
    parts.Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  have hdisjoint := (List.nodup_flatten.mp hflat).2
  exact hdisjoint.imp_of_mem fun {x y} hx hy hxy => by
    intro e
    subst y
    cases x with
    | nil => exact hne [] hx rfl
    | cons a x =>
        exact (List.disjoint_left.mp hxy) (a := a) (by simp) (by simp)

/-- A list-level form of the safe cyclic-pair lemma.  The chosen adjacent
cyclic pair occurs in forward order in the broken token list. -/
theorem exists_safe_rotated_pair
    (parts : List γ) (tokens : List (Option γ))
    (htwo : 2 ≤ parts.length)
    (hnodup : parts.Nodup)
    (hmem : ∀ x ∈ parts, some x ∈ tokens) :
    ∃ x y rest P W R,
      parts ~r (x :: y :: rest) ∧
      tokens = P ++ some x :: W ++ some y :: R := by
  have hparts : parts.toFinset.Nonempty := by
    cases parts with
    | nil => simp at htwo
    | cons x xs => exact ⟨x, by simp⟩
  obtain ⟨x, hxfin, hmin⟩ :=
    Finset.exists_min_image parts.toFinset
      (fun a => tokens.idxOf (some a)) hparts
  have hxparts : x ∈ parts := by simpa using hxfin
  obtain ⟨left, right, hpartsEq, _hxleft⟩ :=
    List.eq_append_cons_of_mem hxparts
  have htail : right ++ left ≠ [] := by
    intro h
    have hr : right = [] := (List.append_eq_nil_iff.mp h).1
    have hl : left = [] := (List.append_eq_nil_iff.mp h).2
    subst right
    subst left
    simp at hpartsEq
    subst parts
    simp at htwo
  obtain ⟨y, rest, htailEq⟩ := List.exists_cons_of_ne_nil htail
  have hrot : parts ~r (x :: y :: rest) := by
    rw [hpartsEq]
    simpa [htailEq, List.append_assoc] using
      (List.isRotated_append (l := left) (l' := x :: right))
  have hyparts : y ∈ parts :=
    hrot.mem_iff.mpr (by simp)
  have hxy : x ≠ y := by
    have hrotNodup : (x :: y :: rest).Nodup :=
      hrot.nodup_iff.mp hnodup
    have hxnot : x ∉ y :: rest := (List.nodup_cons.mp hrotNodup).1
    intro e
    exact hxnot (by simp [e])
  have hxmem : some x ∈ tokens := hmem x hxparts
  have hymem : some y ∈ tokens := hmem y hyparts
  have hle : tokens.idxOf (some x) ≤ tokens.idxOf (some y) :=
    hmin y (by simpa using hyparts)
  have hlt : tokens.idxOf (some x) < tokens.idxOf (some y) := by
    have hne : tokens.idxOf (some x) ≠ tokens.idxOf (some y) := by
      intro heq
      have : some x = some y := (List.idxOf_inj hxmem).mp heq
      exact hxy (Option.some.inj this)
    omega
  obtain ⟨P, tail, htokens, hxP⟩ :=
    List.eq_append_cons_of_mem hxmem
  have hxidx : tokens.idxOf (some x) = P.length := by
    rw [htokens, List.idxOf_append_of_notMem hxP]
    simp
  have hyTail : some y ∈ tail := by
    rw [htokens] at hymem
    simp only [mem_append, mem_cons] at hymem
    rcases hymem with hyP | hyx | hyTail
    · have hyidx : tokens.idxOf (some y) = P.idxOf (some y) := by
        rw [htokens, List.idxOf_append_of_mem hyP]
      have := List.idxOf_lt_length_of_mem hyP
      omega
    · exact (hxy (Option.some.inj hyx.symm)).elim
    · exact hyTail
  obtain ⟨W, R, htailTokens⟩ := List.append_of_mem hyTail
  refine ⟨x, y, rest, P, W, R, hrot, ?_⟩
  simp [htokens, htailTokens, List.append_assoc]

end SafePair

theorem List.IsRotated.flatten {α : Type*}
    {parts parts' : List (List α)} (h : parts ~r parts') :
    parts.flatten ~r parts'.flatten := by
  obtain ⟨n, rfl⟩ := h
  let k := n % parts.length
  calc
    parts.flatten =
        (parts.take k).flatten ++ (parts.drop k).flatten := by
      rw [← List.flatten_append, List.take_append_drop]
    _ ~r (parts.drop k).flatten ++ (parts.take k).flatten :=
      List.isRotated_append
    _ = (parts.rotate n).flatten := by
      rw [List.rotate_eq_drop_append_take_mod]
      simp [k]

section SpliceBookkeeping

variable {γ : Type*}

theorem perm_extract_two (P W R : List γ) (x y : γ) :
    P ++ (x :: (W ++ (y :: R))) ~ x :: y :: (P ++ W ++ R) := by
  calc
    P ++ (x :: (W ++ (y :: R))) ~
        x :: (P ++ (W ++ (y :: R))) :=
      List.perm_middle
    _ = x :: ((P ++ W) ++ (y :: R)) := by
      simp [List.append_assoc]
    _ ~ x :: y :: ((P ++ W) ++ R) :=
      (List.perm_middle.cons x)
    _ = x :: y :: (P ++ W ++ R) := by
      simp [List.append_assoc]

theorem perm_insert_merge (P W R : List γ) (z : γ) :
    W ++ P ++ (z :: R) ~ z :: (P ++ W ++ R) := by
  calc
    W ++ P ++ (z :: R) ~ z :: ((W ++ P) ++ R) :=
      List.perm_middle
    _ ~ z :: ((P ++ W) ++ R) :=
      ((List.perm_append_comm (l₁ := W) (l₂ := P)).append_right R).cons z
    _ = z :: (P ++ W ++ R) := by
      simp [List.append_assoc]

theorem tokenItems_splice_perm
    {P W R : List (Option γ)} {x y z : γ}
    {parts outside : List γ}
    (hparts : parts ~r (x :: y :: []))
    (hperm :
      tokenItems (P ++ (some x :: (W ++ (some y :: R)))) ~
        parts ++ outside) :
    tokenItems (W ++ (none :: (P ++ (some z :: R)))) ~
      z :: outside := by
  have hold :
      tokenItems (P ++ (some x :: (W ++ (some y :: R)))) ~
        x :: y :: (tokenItems P ++ tokenItems W ++ tokenItems R) := by
    simpa using
      perm_extract_two (tokenItems P) (tokenItems W) (tokenItems R) x y
  have htarget :
      parts ++ outside ~ x :: y :: outside := by
    simpa using hparts.perm.append_right outside
  have hrest :
      tokenItems P ++ tokenItems W ++ tokenItems R ~ outside := by
    exact (hold.symm.trans (hperm.trans htarget)).cons_inv.cons_inv
  have hnew :
      tokenItems (W ++ (none :: (P ++ (some z :: R)))) ~
        z :: (tokenItems P ++ tokenItems W ++ tokenItems R) := by
    simpa using
      perm_insert_merge (tokenItems P) (tokenItems W) (tokenItems R) z
  exact hnew.trans (hrest.cons z)

theorem tokenItems_splice_perm_general
    {P W R : List (Option γ)} {x y z : γ}
    {parts rest outside : List γ}
    (hparts : parts ~r (x :: y :: rest))
    (hperm :
      tokenItems (P ++ (some x :: (W ++ (some y :: R)))) ~
        parts ++ outside) :
    tokenItems (W ++ (none :: (P ++ (some z :: R)))) ~
      (z :: rest) ++ outside := by
  have hold :
      tokenItems (P ++ (some x :: (W ++ (some y :: R)))) ~
        x :: y :: (tokenItems P ++ tokenItems W ++ tokenItems R) := by
    simpa using
      perm_extract_two (tokenItems P) (tokenItems W) (tokenItems R) x y
  have htarget :
      parts ++ outside ~ x :: y :: (rest ++ outside) := by
    simpa [List.append_assoc] using hparts.perm.append_right outside
  have hrest :
      tokenItems P ++ tokenItems W ++ tokenItems R ~ rest ++ outside := by
    exact (hold.symm.trans (hperm.trans htarget)).cons_inv.cons_inv
  have hnew :
      tokenItems (W ++ (none :: (P ++ (some z :: R)))) ~
        z :: (tokenItems P ++ tokenItems W ++ tokenItems R) := by
    simpa using
      perm_insert_merge (tokenItems P) (tokenItems W) (tokenItems R) z
  simpa [List.append_assoc] using hnew.trans (hrest.cons z)

theorem breakCount_safe_splice
    (P W R : List (Option γ)) (x y z : γ) :
    breakCount (W ++ (none :: (P ++ (some z :: R)))) =
      breakCount (P ++ (some x :: (W ++ (some y :: R)))) + 1 := by
  simp only [breakCount_append, breakCount_cons_none, breakCount_cons_some]
  omega

theorem safe_splice_ends_in_none
    {P W R : List (Option γ)} {x y z : γ}
    (hend :
      (P ++ (some x :: (W ++ (some y :: R)))).getLast? = some none) :
    (W ++ (none :: (P ++ (some z :: R)))).getLast? = some none := by
  cases R with
  | nil =>
      have hlast :
          (P ++ (some x :: (W ++ [some y]))).getLast? = some (some y) := by
        simpa [List.append_assoc] using
          (List.getLast?_append_cons (P ++ (some x :: W)) (some y) [])
      rw [hlast] at hend
      simp at hend
  | cons token R =>
      have htail : (token :: R).getLast? = some none := by
        rw [show P ++ (some x :: (W ++ (some y :: token :: R))) =
          (P ++ (some x :: W ++ [some y])) ++ (token :: R) by
            simp [List.append_assoc]] at hend
        rwa [List.getLast?_append_of_ne_nil _ (by simp)] at hend
      rw [show W ++ (none :: (P ++ (some z :: token :: R))) =
        (W ++ (none :: P ++ [some z])) ++ (token :: R) by
          simp [List.append_assoc]]
      rwa [List.getLast?_append_of_ne_nil _ (by simp)]

end SpliceBookkeeping

section CollapseFace

variable {α : Type*} [DecidableEq α]

/-- A current cyclic list of nonempty arcs represents a fixed face. -/
def RepresentsFace (parts : List (List α)) (face : List α) : Prop :=
  (∀ part ∈ parts, part ≠ []) ∧
  parts.flatten ~r face ∧
  face.Nodup ∧
  face ≠ []

/-- Collapse all arcs of one face.  `outside` records every arc belonging to
other faces and is left unchanged as a multiset. -/
theorem collapse_face
    (A B : α → Triple) (face : List α)
    (parts outside : List (List α))
    (tokens : List (Option (List α)))
    (hrep : RepresentsFace parts face)
    (hperm : tokenItems tokens ~ parts ++ outside)
    (hchain : tokens.IsChain (BrokenRel (ArcCompatible A B)))
    (hend : tokens.getLast? = some none) :
    ∃ arc tokens',
      arc ≠ [] ∧
      arc ~r face ∧
      tokenItems tokens' ~ arc :: outside ∧
      tokens'.IsChain (BrokenRel (ArcCompatible A B)) ∧
      tokens'.getLast? = some none ∧
      breakCount tokens' ≤ breakCount tokens + (parts.length - 1) := by
  induction hn : parts.length using Nat.strong_induction_on
      generalizing parts tokens with
  | h n ih =>
      rcases hrep with ⟨hne, hface, hfaceNodup, hfaceNe⟩
      cases parts with
      | nil =>
          simp only [List.flatten_nil] at hface
          exact (hfaceNe (List.isRotated_nil_iff'.mp hface).symm).elim
      | cons first tail =>
          cases tail with
          | nil =>
              refine ⟨first, tokens, ?_, ?_, ?_, hchain, hend, ?_⟩
              · exact hne first (by simp)
              · simpa using hface
              · simpa using hperm
              · simp
          | cons second rest =>
              have htwo :
                  2 ≤ (first :: second :: rest).length := by simp
              have hflatNodup :
                  (first :: second :: rest).flatten.Nodup :=
                hface.nodup_iff.mpr hfaceNodup
              have hpartsNodup :
                  (first :: second :: rest).Nodup :=
                nodup_of_nodup_flatten_of_ne_nil hflatNodup hne
              have hmem :
                  ∀ part ∈ (first :: second :: rest), some part ∈ tokens := by
                intro part hpart
                rw [← mem_tokenItems_iff]
                exact hperm.mem_iff.mpr
                  (List.mem_append_left outside hpart)
              obtain ⟨x, y, arcRest, P, W, R, hrot, htokens⟩ :=
                exists_safe_rotated_pair (first :: second :: rest) tokens
                  htwo hpartsNodup hmem
              have hxmem : x ∈ first :: second :: rest :=
                hrot.mem_iff.mpr (by simp)
              have hymem : y ∈ first :: second :: rest :=
                hrot.mem_iff.mpr (by simp)
              have hx : x ≠ [] := hne x hxmem
              have hy : y ≠ [] := hne y hymem
              have htokensNorm :
                  tokens = P ++ (some x :: (W ++ (some y :: R))) := by
                simpa [List.append_assoc] using htokens
              have hrotLen : arcRest.length = rest.length := by
                have hlenEq := hrot.perm.length_eq
                simp only [length_cons, Nat.succ_inj] at hlenEq
                exact hlenEq.symm
              let merged : List α := x ++ y
              let newParts : List (List α) := merged :: arcRest
              let newTokens : List (Option (List α)) :=
                W ++ (none :: (P ++ (some merged :: R)))
              have hnewNe : ∀ part ∈ newParts, part ≠ [] := by
                intro part hpart
                simp only [newParts, mem_cons] at hpart
                rcases hpart with rfl | hpart
                · exact List.append_ne_nil_of_left_ne_nil hx y
                · exact hne part
                    (hrot.mem_iff.mpr (by simp [hpart]))
              have hnewFace : newParts.flatten ~r face := by
                have hback :
                    (x :: y :: arcRest).flatten ~r
                      (first :: second :: rest).flatten :=
                  (List.IsRotated.flatten hrot).symm
                have htrans := hback.trans hface
                simpa [newParts, merged, List.append_assoc] using htrans
              have hnewPerm :
                  tokenItems newTokens ~ newParts ++ outside := by
                rw [htokensNorm] at hperm
                have hs := tokenItems_splice_perm_general
                  (z := merged) hrot hperm
                simpa [newTokens, newParts] using hs
              have hnewChain :
                  newTokens.IsChain (BrokenRel (ArcCompatible A B)) := by
                rw [htokensNorm] at hchain
                simpa [newTokens, merged] using
                  arc_safe_splice A B hx hy hchain
              have hnewEnd : newTokens.getLast? = some none := by
                rw [htokensNorm] at hend
                simpa [newTokens, merged] using
                  (safe_splice_ends_in_none (z := merged) hend)
              have hnewCount :
                  breakCount newTokens = breakCount tokens + 1 := by
                have hc := breakCount_safe_splice P W R x y merged
                rw [htokensNorm]
                simpa [newTokens] using hc
              have hlen :
                  newParts.length < n := by
                simp only [newParts, length_cons]
                simp only [length_cons] at hn
                omega
              have hnewRep : RepresentsFace newParts face :=
                ⟨hnewNe, hnewFace, hfaceNodup, hfaceNe⟩
              obtain ⟨arc, finalTokens, harcNe, harcFace, hfinalPerm,
                  hfinalChain, hfinalEnd, hfinalCount⟩ :=
                ih newParts.length hlen newParts newTokens hnewRep hnewPerm
                  hnewChain hnewEnd rfl
              refine ⟨arc, finalTokens, harcNe, harcFace, hfinalPerm,
                hfinalChain, hfinalEnd, ?_⟩
              have hnewLen : newParts.length + 1 =
                  (first :: second :: rest).length := by
                simp [newParts, hrotLen]
              rw [hnewCount] at hfinalCount
              simp only [length_cons] at hn
              omega

end CollapseFace

section CollapseFaces

variable {α : Type*} [DecidableEq α]

/-- Total number of pairwise merges still required by a list of faces. -/
def mergeBudget (parts : List (List (List α))) : ℕ :=
  (parts.map fun faceParts => faceParts.length - 1).sum

/-- Collapse every represented face, leaving `outside` arcs untouched. -/
theorem collapse_faces
    (A B : α → Triple)
    (parts : List (List (List α))) (faces : List (List α))
    (outside : List (List α))
    (tokens : List (Option (List α)))
    (hreps : List.Forall₂ RepresentsFace parts faces)
    (hperm : tokenItems tokens ~ parts.flatten ++ outside)
    (hchain : tokens.IsChain (BrokenRel (ArcCompatible A B)))
    (hend : tokens.getLast? = some none) :
    ∃ finalArcs tokens',
      List.Forall₂
        (fun arc face => arc ≠ [] ∧ arc ~r face) finalArcs faces ∧
      tokenItems tokens' ~ finalArcs ++ outside ∧
      tokens'.IsChain (BrokenRel (ArcCompatible A B)) ∧
      tokens'.getLast? = some none ∧
      breakCount tokens' ≤ breakCount tokens + mergeBudget parts := by
  induction hreps generalizing outside tokens with
  | nil =>
      exact ⟨[], tokens, .nil, by simpa using hperm, hchain, hend, by simp⟩
  | @cons faceParts face parts faces hrep _hreps ih =>
      have htailPerm :
          tokenItems tokens ~ parts.flatten ++ (faceParts ++ outside) := by
        have hreorder :
            faceParts ++ parts.flatten ++ outside ~
              parts.flatten ++ (faceParts ++ outside) := by
          simpa [List.append_assoc] using
            (List.perm_append_comm (l₁ := faceParts)
              (l₂ := parts.flatten)).append_right outside
        exact hperm.trans hreorder
      obtain ⟨tailArcs, tailTokens, htailFaces, htailItems,
          htailChain, htailEnd, htailCount⟩ :=
        ih (faceParts ++ outside) tokens htailPerm hchain hend
      have hheadPerm :
          tokenItems tailTokens ~ faceParts ++ (tailArcs ++ outside) := by
        have hreorder :
            tailArcs ++ (faceParts ++ outside) ~
              faceParts ++ (tailArcs ++ outside) := by
          simpa [List.append_assoc] using
            (List.perm_append_comm (l₁ := tailArcs)
              (l₂ := faceParts)).append_right outside
        exact htailItems.trans hreorder
      obtain ⟨arc, finalTokens, harcNe, harcFace, hfinalItems,
          hfinalChain, hfinalEnd, hheadCount⟩ :=
        collapse_face A B face faceParts (tailArcs ++ outside)
          tailTokens hrep hheadPerm htailChain htailEnd
      refine ⟨arc :: tailArcs, finalTokens,
        .cons ⟨harcNe, harcFace⟩ htailFaces, ?_, hfinalChain,
        hfinalEnd, ?_⟩
      · simpa [List.append_assoc] using hfinalItems
      · simp only [mergeBudget, List.map_cons, List.sum_cons] at htailCount ⊢
        omega

/-- Initial per-face parts: every item is its own singleton arc. -/
def singletonParts (faces : List (List α)) : List (List (List α)) :=
  faces.map fun face => face.map fun item => [item]

omit [DecidableEq α] in
@[simp] theorem flatten_map_singleton (items : List α) :
    (items.map fun item => [item]).flatten = items := by
  induction items <;> simp_all

omit [DecidableEq α] in
@[simp] theorem singletonParts_flatten (faces : List (List α)) :
    (singletonParts faces).flatten =
      faces.flatten.map (fun item => [item]) := by
  induction faces with
  | nil => rfl
  | cons face faces ih =>
      simp [singletonParts]

omit [DecidableEq α] in
theorem singletonParts_represent
    {faces : List (List α)}
    (hne : ∀ face ∈ faces, face ≠ [])
    (hnodup : faces.flatten.Nodup) :
    List.Forall₂ RepresentsFace (singletonParts faces) faces := by
  induction faces with
  | nil => exact .nil
  | cons face faces ih =>
      have hnodup' : (face ++ faces.flatten).Nodup := by
        simpa only [List.flatten_cons] using hnodup
      have hfaceNodup : face.Nodup :=
        (List.nodup_append.mp hnodup').1
      have htailNodup : faces.flatten.Nodup :=
        (List.nodup_append.mp hnodup').2.1
      apply List.Forall₂.cons
      · refine ⟨?_, ?_, hfaceNodup, hne face (by simp)⟩
        · intro part hpart
          simp only [mem_map] at hpart
          obtain ⟨item, _hitem, rfl⟩ := hpart
          simp
        · simpa using List.IsRotated.refl face
      · apply ih
        · intro f hf
          exact hne f (by simp [hf])
        · exact htailNodup

omit [DecidableEq α] in
theorem mergeBudget_singletonParts_add_length
    {faces : List (List α)}
    (hne : ∀ face ∈ faces, face ≠ []) :
    mergeBudget (singletonParts faces) + faces.length =
      faces.flatten.length := by
  induction faces with
  | nil => rfl
  | cons face faces ih =>
      have hpos : 0 < face.length :=
        List.length_pos_iff.mpr (hne face (by simp))
      have iht := ih fun f hf => hne f (by simp [hf])
      simp only [mergeBudget, singletonParts, List.map_cons, List.sum_cons,
        List.length_cons, List.flatten_cons, List.length_append,
        List.length_map]
      simp only [mergeBudget, singletonParts] at iht
      omega

end CollapseFaces

/-- Final safe cyclic surgery.  There is one nonempty rotated arc per input
face; those arcs form compatible trails, and each merge costs at most one
additional trail. -/
theorem surgery_final
    {α : Type*} [DecidableEq α]
    (A B : α → Triple)
    (faces : List (List α))
    (trails₀ : List (List (List α)))
    (hfaces : ∀ face ∈ faces, face ≠ [])
    (hnodup : faces.flatten.Nodup)
    (hperm :
      trails₀.flatten ~ faces.flatten.map (fun item => [item]))
    (hcompat :
      ∀ trail ∈ trails₀, trail.IsChain (ArcCompatible A B)) :
    ∃ trails' : List (List (List α)), ∃ finalArcs : List (List α),
      (∀ trail ∈ trails', trail.IsChain (ArcCompatible A B)) ∧
      trails'.length ≤
        trails₀.length + (faces.flatten.length - faces.length) ∧
      trails'.flatten.length = faces.length ∧
      trails'.flatten ~ finalArcs ∧
      List.Forall₂
        (fun arc face => arc ≠ [] ∧ arc ~r face) finalArcs faces := by
  cases faces with
  | nil =>
      have hflat : trails₀.flatten = [] := by
        simpa using hperm
      refine ⟨trails₀, [], hcompat, by simp, ?_, ?_, .nil⟩
      · simp [hflat]
      · simp [hflat]
  | cons face faces =>
      let allFaces := face :: faces
      let parts := singletonParts allFaces
      let tokens := delimit trails₀
      have htrailsNe : trails₀ ≠ [] := by
        intro hnil
        subst trails₀
        have hlen := hperm.length_eq
        have hfacePos : 0 < face.length :=
          List.length_pos_iff.mpr (hfaces face (by simp))
        simp only [List.flatten_nil, List.length_nil, List.length_map,
          List.flatten_cons, List.length_append] at hlen
        omega
      have hreps : List.Forall₂ RepresentsFace parts allFaces := by
        apply singletonParts_represent hfaces hnodup
      have htokenPerm : tokenItems tokens ~ parts.flatten ++ [] := by
        simpa [tokens, parts, allFaces] using hperm
      have htokenChain :
          tokens.IsChain (BrokenRel (ArcCompatible A B)) :=
        isChain_delimit hcompat
      have htokenEnd : tokens.getLast? = some none :=
        delimit_ends_in_none htrailsNe
      obtain ⟨finalArcs, finalTokens, hfinalFaces, hfinalItems,
          hfinalChain, hfinalEnd, hfinalCount⟩ :=
        collapse_faces A B parts allFaces [] tokens hreps htokenPerm
          htokenChain htokenEnd
      let trails' := undelimit finalTokens
      have htrailChains :
          ∀ trail ∈ trails', trail.IsChain (ArcCompatible A B) :=
        chains_undelimit hfinalChain
      have htrailLength :
          trails'.length = breakCount finalTokens :=
        length_undelimit_of_ends_in_none hfinalEnd
      have hflatPerm : trails'.flatten ~ finalArcs := by
        rw [show trails'.flatten = tokenItems finalTokens by
          exact tokenItems_undelimit finalTokens]
        simpa using hfinalItems
      have hfinalArcsLength :
          finalArcs.length = allFaces.length :=
        hfinalFaces.length_eq
      have hflatLength : trails'.flatten.length = allFaces.length :=
        hflatPerm.length_eq.trans hfinalArcsLength
      have hinitialBreaks : breakCount tokens = trails₀.length := by
        simp [tokens]
      have hbudgetAdd :
          mergeBudget parts + allFaces.length =
            allFaces.flatten.length := by
        exact mergeBudget_singletonParts_add_length hfaces
      have hbudget :
          mergeBudget parts =
            allFaces.flatten.length - allFaces.length := by
        omega
      refine ⟨trails', finalArcs, htrailChains, ?_, ?_, hflatPerm,
        hfinalFaces⟩
      · rw [htrailLength]
        rw [hinitialBreaks, hbudget] at hfinalCount
        simpa [allFaces] using hfinalCount
      · simpa [allFaces] using hflatLength

section Deletion

variable {β : Type*}

/-- Replace a dead item by a trail break. -/
def deletionToken (dead : β → Prop) [DecidablePred dead] :
    Option β → Option β
  | none => none
  | some x => if dead x then none else some x

theorem tokenItems_map_deletionToken
    (dead : β → Prop) [DecidablePred dead]
    (tokens : List (Option β)) :
    tokenItems (tokens.map (deletionToken dead)) =
      (tokenItems tokens).filter (fun x => !decide (dead x)) := by
  induction tokens with
  | nil => rfl
  | cons token tokens ih =>
      cases token with
      | none => simpa [deletionToken] using ih
      | some x =>
          by_cases hx : dead x
          · simp [deletionToken, hx, ih]
          · simp [deletionToken, hx, ih]

theorem breakCount_map_deletionToken
    (dead : β → Prop) [DecidablePred dead]
    (tokens : List (Option β)) :
    breakCount (tokens.map (deletionToken dead)) =
      breakCount tokens +
        (tokenItems tokens).countP (fun x => decide (dead x)) := by
  induction tokens with
  | nil => rfl
  | cons token tokens ih =>
      cases token with
      | none =>
          simp [deletionToken, ih, Nat.add_assoc, Nat.add_comm]
      | some x =>
          by_cases hx : dead x
          · simp [deletionToken, hx, ih, Nat.add_assoc]
          · simp [deletionToken, hx, ih]

theorem isChain_map_deletionToken
    {r : β → β → Prop} (dead : β → Prop) [DecidablePred dead]
    {tokens : List (Option β)}
    (hchain : tokens.IsChain (BrokenRel r)) :
    (tokens.map (deletionToken dead)).IsChain (BrokenRel r) := by
  rw [List.isChain_map]
  apply hchain.imp
  intro x y hxy
  cases x with
  | none => simp [deletionToken, BrokenRel]
  | some x =>
      cases y with
      | none => simp [deletionToken, BrokenRel]
      | some y =>
          by_cases hx : dead x <;> by_cases hy : dead y
          · simp [deletionToken, BrokenRel, hx, hy]
          · simp [deletionToken, BrokenRel, hx, hy]
          · simp [deletionToken, BrokenRel, hx, hy]
          · simpa [deletionToken, BrokenRel, hx, hy] using hxy

theorem deletionToken_ends_in_none
    (dead : β → Prop) [DecidablePred dead]
    {tokens : List (Option β)}
    (hend : tokens.getLast? = some none) :
    (tokens.map (deletionToken dead)).getLast? = some none := by
  rw [List.getLast?_map, hend]
  rfl

/-- Delete an arbitrary predicate of items from compatible trails.  Each
deleted occurrence is replaced by a break, so deletion adds at most one
trail per deleted item. -/
theorem trail_deletion
    (r : β → β → Prop)
    (trails : List (List β))
    (compat : ∀ trail ∈ trails, trail.IsChain r)
    (dead : β → Prop) [DecidablePred dead] :
    ∃ trails' : List (List β),
      (∀ trail ∈ trails', trail.IsChain r) ∧
      trails'.flatten =
        trails.flatten.filter (fun x => !decide (dead x)) ∧
      trails'.length ≤ trails.length +
        trails.flatten.countP (fun x => decide (dead x)) := by
  classical
  cases trails with
  | nil => exact ⟨[], by simp⟩
  | cons trail trails =>
      let original := delimit (trail :: trails)
      let reduced := original.map (deletionToken dead)
      let trails' := undelimit reduced
      have horiginalChain : original.IsChain (BrokenRel r) :=
        isChain_delimit compat
      have hreducedChain : reduced.IsChain (BrokenRel r) :=
        isChain_map_deletionToken dead horiginalChain
      have horiginalEnd : original.getLast? = some none :=
        delimit_ends_in_none (by simp)
      have hreducedEnd : reduced.getLast? = some none :=
        deletionToken_ends_in_none dead horiginalEnd
      have hchains : ∀ t ∈ trails', t.IsChain r :=
        chains_undelimit hreducedChain
      have hitems :
          trails'.flatten =
            (trail :: trails).flatten.filter
              (fun x => !decide (dead x)) := by
        rw [show trails'.flatten = tokenItems reduced by
          exact tokenItems_undelimit reduced]
        rw [show tokenItems reduced =
            (tokenItems original).filter (fun x => !decide (dead x)) by
          exact tokenItems_map_deletionToken dead original]
        simp [original]
      have hlength :
          trails'.length =
            (trail :: trails).length +
              (trail :: trails).flatten.countP
                (fun x => decide (dead x)) := by
        rw [show trails'.length = breakCount reduced by
          exact length_undelimit_of_ends_in_none hreducedEnd]
        rw [show breakCount reduced =
            breakCount original +
              (tokenItems original).countP
                (fun x => decide (dead x)) by
          exact breakCount_map_deletionToken dead original]
        simp [original]
      exact ⟨trails', hchains, hitems, hlength.le⟩

end Deletion

end Superperm7
