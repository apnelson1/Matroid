import Matroid.Graph.Connected.Basic
import Matroid.Graph.Independent
import Matroid.Graph.Tree
import Matroid.ForMathlib.Minimal
import Matroid.ForMathlib.Tactic.ENatToNat

import Matroid.Exercises.HamiltonianCycle.Degree
import Matroid.Exercises.HamiltonianCycle.Walk

open Set

namespace Graph

variable {α β ι : Type*} {x y z u v : α} {e f : β} {G H K H₁ H₂ : Graph α β}
variable {S A : Set α}

-- COMPONENTS
lemma finite_components_of_finite [G.Finite] : G.Components.Finite :=
  G.vertexSet_finite.finite_of_encard_le G.components_encard_le

lemma ge_two_components_of_not_connected (hNeBot : V(G).Nonempty) (h : ¬ G.Connected) :
    2 ≤ G.Components.encard := by
  -- This is very easy by `components_subsingleton_iff`.
  by_contra! hcon
  replace hcon : G.Components.Subsingleton := by
    rw [← encard_le_one_iff_subsingleton]
    enat_to_nat!
    omega
  rw [components_subsingleton_iff_connected] at hcon
  rw [← ne_bot_iff] at hNeBot
  tauto

lemma components_encard_eq_one_iff : G.Components.encard = 1 ↔ G.Connected := by
  rw [encard_eq_one]
  exact components_eq_singleton_iff

lemma not_connected_of_nontrivial_components (h : G.Components.Nontrivial) : ¬ G.Connected := by
  rw [← components_encard_eq_one_iff]
  rw [← one_lt_encard_iff_nontrivial] at h
  exact h.ne'

lemma not_connected_of_components_encard_ge_two (h : 2 ≤ G.Components.encard) : ¬ G.Connected := by
  rw [two_le_encard_iff_nontrivial] at h
  exact not_connected_of_nontrivial_components h

lemma components_nontrivial_of_not_connected (hNeBot : V(G).Nonempty) (h : ¬ G.Connected)
    : G.Components.Nontrivial := by
  rw [← two_le_encard_iff_nontrivial]
  exact ge_two_components_of_not_connected hNeBot h

protected lemma Connected.components_eq_singleton_self (h : G.Connected) : G.Components = {G} := by
  have h_subsingleton := components_subsingleton_iff_connected.mpr (Or.inr h)
  exact h_subsingleton.eq_singleton_of_mem h

lemma components_eq_singleton_self (h : G.Connected) : G.Components = {G} :=
  h.components_eq_singleton_self

lemma components_eq_singleton_self_iff : H.Components = {H} ↔ H.Connected :=
  ⟨fun h ↦ components_eq_singleton_iff.mp ⟨_, h⟩, fun h ↦ h.connected.components_eq_singleton_self⟩

-- ISSEPSET

lemma empty_isSep (h : ¬ G.Connected) : G.IsSep ∅ where
  subset_vx := empty_subset _
  not_connected := by simpa

lemma IsSep.not_connected_of_empty (h : G.IsSep ∅) : ¬ G.Connected := by
  have := h.not_connected
  simp_all only [vertexDelete_empty, not_false_eq_true]

@[simp]
lemma IsMinSep.eq_empty_iff (hS : G.IsMinSep S) : S = ∅ ↔ ¬ G.Connected := by
  refine ⟨fun h ↦ (h ▸ hS).toIsSep.not_connected_of_empty, ?_⟩
  by_contra! hcon
  obtain ⟨hG, hSne⟩ := hcon
  obtain rfl := by simpa using hS.minimal ∅ <| empty_isSep hG
  simp at hSne

@[simp]
lemma empty_isMinSep_iff : G.IsMinSep ∅ ↔ ¬ G.Connected :=
  ⟨fun h ↦ h.toIsSep.not_connected_of_empty, fun h ↦ ⟨empty_isSep h, by simp⟩⟩

lemma IsMinSep.connected_iff (hS : G.IsMinSep S) : G.Connected ↔ S.Nonempty := by
  simpa [nonempty_iff_ne_empty] using hS.eq_empty_iff.not.symm

-- lemma IsMinSep.encard_pos_iff (hS : G.IsMinSep S) : 0 < S.encard ↔ G.Connected := by
--   rw [Set.encard_pos, ←not_iff_not, Set.not_nonempty_iff_eq_empty, ←Set.encard_eq_zero]
--   exact hS.encard_eq_zero_iff

-- lemma IsMinSep.encard_ne_zero_iff (hS : G.IsMinSep S) : S.encard ≠ 0 ↔ G.Connected := by
--   rw [encard_ne_zero, ←not_iff_not, Set.not_nonempty_iff_eq_empty, ←Set.encard_eq_zero]
--   exact hS.encard_eq_zero_iff

-- any two MinSepSets have the same encard
lemma IsMinSep.encard_eq_encard_of_isMinSep (hS : G.IsMinSep S) (hA : G.IsMinSep A) :
    S.encard = A.encard := by
  have h₁ := hS.minimal _ hA.toIsSep
  have h₂ := hA.minimal _ hS.toIsSep
  exact h₁.antisymm h₂

lemma isSep_empty_iff_not_connected : G.IsSep ∅ ↔ ¬ G.Connected := by
  refine ⟨fun h ↦ h.not_connected_of_empty, ?_⟩
  intro hyp
  refine ⟨by simp only [empty_subset], by simpa only [vertexDelete_empty]⟩

lemma isSep_empty_iff_isMinSep_empty : G.IsSep ∅ ↔ G.IsMinSep ∅ := by
  refine ⟨?_, fun h ↦ h.toIsSep⟩
  intro hyp
  refine ⟨hyp, ?_⟩
  intro A hA
  simp only [encard_empty, zero_le]

lemma isMinSep_empty_iff_not_connected : G.IsMinSep ∅ ↔ ¬ G.Connected := by
  rw [← isSep_empty_iff_isMinSep_empty]
  exact isSep_empty_iff_not_connected

lemma eq_iff_components_eq_components : G = H ↔ G.Components = H.Components := by
  refine ⟨by rintro rfl; rfl, ?_⟩
  intro hyp
  rw [G.eq_sUnion_components, H.eq_sUnion_components]
  simp_all only

lemma IsCompOf.eq_of_connected (hH : H.IsCompOf G) (hG : G.Connected) : H = G := by
  obtain ⟨x, hx⟩ := hH.nonempty
  exact hH.eq_of_mem_mem hG.connected hx (hH.subset hx)

lemma IsClosedSubgraph.vertexDelete_components_eq (hH : H ≤c G) :
    (G - V(H)).Components = G.Components \ H.Components := by
  ext C
  refine ⟨?_, ?_⟩ <;> intro hC
  · simp only [mem_diff, mem_components_iff_isCompOf]
    refine ⟨hC.of_isClosedSubgraph hH.compl, ?_⟩
    suffices ¬ V(C) ≤ V(H) by exact fun h ↦ this h.subset
    have solver := hC.le
    rw [le_vertexDelete_iff] at solver
    intro bad
    replace solver := solver.2.eq_bot_of_le bad
    have := hC.nonempty
    simp only [bot_eq_empty] at solver
    rw [solver] at this
    exact not_nonempty_empty this
  simp only [mem_components_iff_isCompOf]
  obtain (h|h) := hH.isCompOf_of_isCompOf_compl hC.1
  · exfalso
    simp only [mem_diff, mem_components_iff_isCompOf] at hC
    exact hC.2 h
  assumption

lemma IsClosedSubgraph.isCompOf_of_isCompOf (hH : H ≤c G) (hK : K.IsCompOf H) : K.IsCompOf G :=
  hK.of_isClosedSubgraph hH

lemma IsClosedSubgraph.components_subset (hH : H ≤c G) : H.Components ⊆ G.Components :=
  fun _ hC ↦  hC.of_isClosedSubgraph hH

lemma IsClosedSubgraph.vertexDelete_components_encard_eq (hH : H ≤c G) :
    (G - V(H)).Components.encard + H.Components.encard = G.Components.encard := by
  rw [hH.vertexDelete_components_eq, encard_diff_add_encard, union_eq_left.mpr hH.components_subset]

lemma IsCompOf.vertexDelete_components_eq (hH : H.IsCompOf G) :
    (G - V(H)).Components = G.Components \ {H} := by
  rw [hH.isClosedSubgraph.vertexDelete_components_eq]
  suffices H.Components = {H} by rw [this]
  exact hH.connected.components_eq_singleton_self

lemma IsCompOf.vertexDelete_components_encard_eq (hH : H.IsCompOf G) :
    (G - V(H)).Components.encard + 1 = G.Components.encard := by
  rw [← encard_singleton H, ← hH.connected.components_eq_singleton_self]
  exact hH.isClosedSubgraph.vertexDelete_components_encard_eq

lemma IsCompOf.isSepSet_of_three_le_components_encard
    (hH : H.IsCompOf G) (hG : 3 ≤ G.Components.encard) : G.IsSep V(H) := by
  refine ⟨hH.subset, ?_⟩
  refine not_connected_of_components_encard_ge_two ?_
  suffices : 3 ≤ 1 + (G - V(H)).Components.encard
  · exact ENat.one_add_le_one_add_iff.mp this
  rwa [add_comm, hH.vertexDelete_components_encard_eq]

lemma IsCompOf.isCompOf_compl_of_disjoint
    (hH : H.IsCompOf G) (hdisj : Disjoint V(H) S) : H.IsCompOf (G - S) := by
  have hle : H ≤ G - S := by
    rw [le_vertexDelete_iff]
    refine ⟨hH.le, hdisj⟩
  have hle_closed : H ≤c G - S := by
    refine ⟨hle, ?_⟩
    intro e x hex hxH
    have hex' : G.Inc e x := hex.of_le vertexDelete_le
    exact hH.isClosedSubgraph.closed hex' hxH
  rw [IsCompOf_iff_isClosedSubgraph_connected]
  refine ⟨hle_closed, hH.connected⟩

lemma IsCompOf.isSepSet_of_not_connected_of_ssubset
    (hH : H.IsCompOf G) (hG : ¬ G.Connected) (hssub : S ⊂ V(H)) : G.IsSep S := by
  refine ⟨hssub.le.trans hH.subset, ?_⟩
  rw [ssubset_iff_exists] at hssub
  obtain ⟨hSH, x, hxH, hxnS⟩ := hssub
  have hxHS : x ∈ V(H - S) := by
    simp only [vertexDelete_vertexSet, mem_diff]
    exact ⟨hxH, hxnS⟩
  have hle : H - S ≤ G - S := vertexDelete_mono_left hH.le _
  obtain ⟨Cx, hCx_ge, hCx_isCompOf⟩ :=
    (Graph.walkable_connected hxHS).exists_isCompOf_ge
      (Graph.walkable_isClosedSubgraph.le.trans hle)
  have hxCx : x ∈ V(Cx) := by
    refine Graph.vertexSet_mono hCx_ge ?_
    exact mem_walkable_self_iff.mpr hxHS
  replace hG : G.Components.Nontrivial := components_nontrivial_of_not_connected
    (hH.nonempty.mono hH.subset) hG
  obtain ⟨K, K_isCompOf_G, hne⟩ := hG.exists_ne H
  have K_isCompOf_GS : K.IsCompOf (G - S) := by
    refine K_isCompOf_G.isCompOf_compl_of_disjoint ?_
    by_contra! hcon
    refine hne ?_
    rw [not_disjoint_iff] at hcon
    obtain ⟨y, hyK, hyS⟩ := hcon
    exact (K_isCompOf_G : K.IsCompOf G).eq_of_mem_mem hH hyK (hSH hyS)
  refine not_connected_of_nontrivial_components ?_
  refine ⟨K, K_isCompOf_GS, Cx, hCx_isCompOf, ?_⟩
  contrapose hne
  refine K_isCompOf_G.eq_of_mem_mem hH (x := x) ?_ ?_
  · rwa [hne]
  simp at hxHS
  exact hxHS.1

/-
lemma vertexDelete_not_isolated_components_encard (hx : ¬ G.Isolated x) :
    G.Components.encard ≤ (G - {x}).Components.encard := by


-- deleting one vertex can only lower Components.encard by at most 1
lemma vertexDelete_components_encard_ge (x : α) :
    G.Components.encard - 1 ≤ (G - {x}).Components.encard := by
  -- Cases:
  -- 1: x ∉ V(G), in which case G - {x} = G, and the statement is trivial
  -- 2: {x} is a component of G, in which case the # of components is lowered by 1
  -- 3: {x} is not a component of G, in which case the # either stays the same or increases
  sorry

lemma exists_isSepSet_with_encard_lt_components_encard
    (hG : 3 ≤ V(G).encard) (hConn : ¬ G.Connected) {n} (hn : n < G.Components.encard) :
    ∃ S, G.IsSep S ∧ S.encard = n := by
  obtain (rfl | h) := em (n = ⊤)
  · simp at hn
  enat_to_nat; clear h
  induction n generalizing G with
  | zero =>
      refine ⟨∅, ⟨?_, ?_⟩, ?_⟩ <;> simp_all
  | succ n IH => sorry
-/

lemma exists_isSepSet_size_one_of_not_connected (hG : 3 ≤ V(G).encard) (h : ¬ G.Connected) :
    ∃ S, G.IsSep S ∧ S.encard = 1 := by
  -- This is actually a little subtle.
  -- I'm guessing there's probably machinery to better deal with this.

  have hNeBot : V(G).Nonempty := by
    rw [← encard_pos]
    suffices aux : (0 : ℕ∞) < 3 by exact aux.trans_le hG
    enat_to_nat; omega
  -- Casework on whether every component is a singleton or not.
  -- If every component is a singleton, then there are at least 3 components, and we can simply
  --   delete any component.
  -- Otherwise, there is at least one nontrivial component, in which case we can delete any vertex
  --   of that component.
  obtain (h_subsingleton | h_nontrivial) := em (∀ H ∈ G.Components, V(H).encard ≤ 1)
  · replace h_subsingleton : ∀ H : G.Components, V(H.1).encard = 1 := by
      intro ⟨H, hH⟩
      refine (h_subsingleton _ hH).antisymm ?_
      rw [one_le_encard_iff_nonempty]
      exact hH.nonempty
    have heq : G.Components.encard = V(G).encard := by
      conv => rhs; rw [G.eq_sUnion_components]; simp only [sUnion_vertexSet]
      rw [← ENat.tsum_encard_eq_encard_biUnion
            (fun _ hx _ hy hne ↦ (G.components_pairwise_stronglyDisjoint hx hy hne).vertex)]
      simp [tsum_congr h_subsingleton]
    rw [←heq] at hG
    have ⟨H, hH⟩ : G.Components.Nonempty := by
      rw [← encard_pos]
      suffices (0 : ℕ∞) < 3 by exact this.trans_le hG
      enat_to_nat; omega
    refine ⟨V(H), hH.isSepSet_of_three_le_components_encard hG, h_subsingleton ⟨_, hH⟩⟩
  -- Else, there is at least one nontrivial component.
  simp [one_lt_encard_iff_nontrivial] at h_nontrivial
  obtain ⟨H, hH, H_nontrivial⟩ := h_nontrivial
  obtain ⟨x, hx⟩ := hH.nonempty
  refine ⟨{x}, ?_, by simp⟩
  refine hH.isSepSet_of_not_connected_of_ssubset h ⟨by simpa, H_nontrivial.not_subset_singleton⟩
