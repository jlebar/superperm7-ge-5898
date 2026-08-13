/-
Copyright (c) 2026 Anthropic, PBC. Released under the Apache License 2.0 (see LICENSE); this file is
additionally subject to the upstream MIT notice below.

Adapted from https://github.com/BGray-wrl/superperm6
  file:   formal-verification/Superperm6/GraphRank.lean
  commit: d8a932d8f61d80b0bcfc737bd0e235a8300449c4
  upstream copyright: Copyright (c) 2026 Benjamin Grayzel — MIT License (reproduced in NOTICE).
Local modifications (port from six to seven symbols; see docs/PORT_LOG.md): namespace and permutation type only.
-/
import Mathlib

/-!
# A finite graph rank inequality

For a finite graph, the number of vertices is at most the number of edges
plus the number of connected components.  Mathlib provides the connected
case; the proof below joins one representative from each component to a
fixed representative and reduces to that theorem.
-/

namespace Superperm7

open SimpleGraph

section

variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable local instance connectedComponentDecidableEq (G : SimpleGraph V) :
    DecidableEq G.ConnectedComponent := Classical.decEq _

noncomputable def componentRepresentative (G : SimpleGraph V)
    (C : G.ConnectedComponent) : V :=
  Classical.choose C.nonempty_supp

theorem componentRepresentative_mem (G : SimpleGraph V)
    (C : G.ConnectedComponent) : componentRepresentative G C ∈ C.supp :=
  Classical.choose_spec C.nonempty_supp

noncomputable def baseComponent (G : SimpleGraph V) [Nonempty V] :
    G.ConnectedComponent :=
  G.connectedComponentMk (Classical.choice ‹Nonempty V›)

noncomputable def componentAnchorCandidates (G : SimpleGraph V)
    [Nonempty V] : Finset (Sym2 V) :=
  ((Finset.univ : Finset G.ConnectedComponent).erase (baseComponent G)).image
    fun C => s(componentRepresentative G C,
      componentRepresentative G (baseComponent G))

theorem componentAnchorCandidates_card_le (G : SimpleGraph V)
    [Nonempty V] :
    (componentAnchorCandidates G).card ≤
      Fintype.card G.ConnectedComponent - 1 := by
  calc
    (componentAnchorCandidates G).card ≤
        ((Finset.univ : Finset G.ConnectedComponent).erase
          (baseComponent G)).card := Finset.card_image_le
    _ = Fintype.card G.ConnectedComponent - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]

noncomputable def componentConnectedAugmentation (G : SimpleGraph V)
    [Nonempty V] : SimpleGraph V :=
  SimpleGraph.fromEdgeSet
    ((G.edgeFinset ∪ componentAnchorCandidates G : Finset (Sym2 V)) : Set (Sym2 V))

theorem graph_le_componentConnectedAugmentation (G : SimpleGraph V)
    [Nonempty V] : G ≤ componentConnectedAugmentation G := by
  apply (SimpleGraph.le_fromEdgeSet_iff G _).mpr
  intro e he
  apply Finset.mem_union_left
  exact SimpleGraph.mem_edgeFinset.mpr he

theorem component_representative_reachable (G : SimpleGraph V)
    (v : V) :
    G.Reachable v
      (componentRepresentative G (G.connectedComponentMk v)) := by
  exact ConnectedComponent.reachable_of_mem_supp (G.connectedComponentMk v)
    ConnectedComponent.connectedComponentMk_mem
    (componentRepresentative_mem G _)

theorem component_anchor_reachable_base (G : SimpleGraph V) [Nonempty V]
    (C : G.ConnectedComponent) :
    (componentConnectedAugmentation G).Reachable
      (componentRepresentative G C)
      (componentRepresentative G (baseComponent G)) := by
  by_cases hC : C = baseComponent G
  · exact hC ▸ Reachable.refl _
  have hmem : C ∈ (Finset.univ : Finset G.ConnectedComponent).erase
      (baseComponent G) := by simp [hC]
  have hedge : s(componentRepresentative G C,
      componentRepresentative G (baseComponent G)) ∈
      componentAnchorCandidates G := by
    apply Finset.mem_image.mpr
    exact ⟨C, hmem, rfl⟩
  by_cases hrep : componentRepresentative G C =
      componentRepresentative G (baseComponent G)
  · exact hrep ▸ Reachable.refl _
  apply Adj.reachable
  unfold componentConnectedAugmentation
  rw [SimpleGraph.fromEdgeSet_adj]
  refine ⟨?_, hrep⟩
  apply Finset.mem_union_right
  simpa using hedge

theorem componentConnectedAugmentation_connected (G : SimpleGraph V)
    [Nonempty V] : (componentConnectedAugmentation G).Connected := by
  apply Connected.mk
  intro u v
  have hu := (component_representative_reachable G u).mono
    (graph_le_componentConnectedAugmentation G)
  have hv := (component_representative_reachable G v).mono
    (graph_le_componentConnectedAugmentation G)
  have huBase := component_anchor_reachable_base G (G.connectedComponentMk u)
  have hvBase := component_anchor_reachable_base G (G.connectedComponentMk v)
  exact hu.trans (huBase.trans (hvBase.symm.trans hv.symm))

/-- Finite graph rank inequality: `|V| ≤ |E| + components`. -/
theorem card_vertices_le_card_edges_add_components (G : SimpleGraph V) :
    Fintype.card V ≤ G.edgeFinset.card + Fintype.card G.ConnectedComponent := by
  cases isEmpty_or_nonempty V with
  | inl hempty => simp
  | inr hnonempty =>
      letI : Nonempty V := hnonempty
      let H := componentConnectedAugmentation G
      have hconn := componentConnectedAugmentation_connected G
      have hconnected := hconn.card_vert_le_card_edgeSet_add_one
      have hconnected' : Fintype.card V ≤ H.edgeFinset.card + 1 := by
        have hedgeNat : Nat.card H.edgeSet = H.edgeFinset.card := by
          rw [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card]
        rw [Nat.card_eq_fintype_card, hedgeNat] at hconnected
        exact hconnected
      have hanchor := componentAnchorCandidates_card_le G
      have hedgeBound : H.edgeFinset.card ≤
          G.edgeFinset.card + (componentAnchorCandidates G).card := by
        have hsubset : H.edgeFinset ⊆
            G.edgeFinset ∪ componentAnchorCandidates G := by
          intro e he
          have heSet : e ∈ H.edgeSet := SimpleGraph.mem_edgeFinset.mp he
          dsimp [H, componentConnectedAugmentation] at heSet
          rw [SimpleGraph.edgeSet_fromEdgeSet] at heSet
          exact heSet.1
        exact (Finset.card_le_card hsubset).trans (Finset.card_union_le _ _)
      have hkpos : 1 ≤ Fintype.card G.ConnectedComponent :=
        Fintype.card_pos_iff.mpr inferInstance
      omega

end

end Superperm7
