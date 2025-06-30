import Matroid.Graph.Walk.Cycle
import Matroid.Graph.Constructions.Basic
import Matroid.Graph.Lattice
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Set.Card

variable {α β : Type*} {G H T F : Graph α β} {u v x y z : α} {e e' f g : β} {X : Set α}
{P C Q : WList α β}

open Set

lemma finite_list_nodup (α : Type*) [Finite α] : {L : List α | L.Nodup}.Finite := by
  classical
  haveI := Fintype.ofFinite
  refine (List.finite_length_le α (Fintype.card α)).subset fun L hL ↦ ?_
  simp [List.Nodup.length_le_card hL]

@[simp]
theorem List.nodup_attachWith {α : Type*} {l : List α} (P : α → Prop) (hP : ∀ x ∈ l, P x) :
    (l.attachWith P hP).Nodup ↔ l.Nodup := by
  induction l with simp_all

namespace Graph

/-! ### Finiteness -/

/-- A graph is finite if it has finitely many vertices and edges -/
@[mk_iff]
protected class Finite (G : Graph α β) : Prop where
  vertexSet_finite : V(G).Finite
  edgeSet_finite : E(G).Finite

lemma Finite.mono (hG : G.Finite) (hHG : H ≤ G) : H.Finite where
  vertexSet_finite := hG.vertexSet_finite.subset <| vertexSet_mono hHG
  edgeSet_finite := hG.edgeSet_finite.subset <| edgeSet_mono hHG

lemma finite_of_le [G.Finite] (hHG : H ≤ G) : H.Finite :=
  ‹G.Finite›.mono hHG

instance [G.Finite] (X : Set α) : (G - X).Finite :=
  ‹G.Finite›.mono vertexDelete_le

instance [G.Finite] (F : Set β) : (G ↾ F).Finite :=
  ‹G.Finite›.mono edgeRestrict_le

instance [G.Finite] (F : Set β) : (G ＼ F).Finite :=
  ‹G.Finite›.mono edgeDelete_le

lemma Finite.induce (hG : G.Finite) (hX : X ⊆ V(G)) : G[X].Finite where
  vertexSet_finite := hG.vertexSet_finite.subset hX
  edgeSet_finite := hG.edgeSet_finite.subset (by simp)

@[simp]
lemma vertexSet_finite [G.Finite] : G.vertexSet.Finite :=
  Finite.vertexSet_finite

@[simp]
lemma edgeSet_finite [G.Finite] : G.edgeSet.Finite :=
  Finite.edgeSet_finite

lemma isTrail_finite (G : Graph α β) [G.Finite] : {P | G.IsTrail P}.Finite := by
  have hVfin := G.vertexSet_finite.to_subtype
  have hEfin := G.edgeSet_finite.to_subtype
  have : Finite {L : List E(G) // L.Nodup} := finite_list_nodup E(G)
  let f (P : {P // G.IsTrail P}) : V(G) × {L : List E(G) // L.Nodup} :=
    ⟨⟨P.1.first, P.2.isWalk.vertex_mem_of_mem (by simp)⟩,
    ⟨P.1.edge.attachWith _ (fun _ ↦ P.2.isWalk.edge_mem_of_mem), by simp [P.2.edge_nodup]⟩⟩
  change Finite {P // G.IsTrail P}
  refine Finite.of_injective f fun ⟨P, hP⟩ ⟨P', hP'⟩ hPP' ↦ ?_
  simp only [Prod.mk.injEq, Subtype.mk.injEq, f] at hPP'
  simp only [Subtype.mk.injEq, f]
  apply hP.isWalk.eq_of_edge_eq_first_eq hP'.isWalk hPP'.1
  convert congr_arg (fun L ↦ L.map Subtype.val) hPP'.2 <;> simp

lemma isPath_finite (G : Graph α β) [G.Finite] : {P | G.IsPath P}.Finite :=
  G.isTrail_finite.subset fun _ ↦ IsPath.isTrail

lemma isCycle_finite (G : Graph α β) [G.Finite] : {C | G.IsCycle C}.Finite :=
  G.isTrail_finite.subset fun _ ↦ IsCycle.isTrail

/-- A finite graph has finitely many subgraphs. -/
lemma finite_setOf_le (G : Graph α β) [G.Finite] : {H | H ≤ G}.Finite := by
  refine Finite.of_finite_image (f := fun H ↦ (⟨V(H), E(H)⟩ : Set α × Set β)) ?_
    fun H₁ h₁ H₂ h₂ h_eq ↦ ?_
  · refine (G.vertexSet_finite.finite_subsets.prod G.edgeSet_finite.finite_subsets).subset ?_
    rintro _ ⟨H, hle : H ≤ G, rfl⟩
    simp [vertexSet_mono hle, edgeSet_mono hle]
  simp only [Prod.mk.injEq] at h_eq
  exact G.ext_of_le_le h₁ h₂ h_eq.1 h_eq.2

instance (G : Graph α β) [G.Finite] : Finite G.Subgraph := finite_setOf_le G

instance (G : Graph α β) [G.Finite] : Finite G.ClosedSubgraph :=
  G.finite_setOf_le.subset fun _ hH ↦ hH.le

instance [G.Finite] [H.Finite] : (G ∪ H).Finite where
  vertexSet_finite := G.vertexSet_finite.union H.vertexSet_finite
  edgeSet_finite := G.edgeSet_finite.union H.edgeSet_finite

instance : (Graph.singleEdge x y e).Finite where
  vertexSet_finite := by simp
  edgeSet_finite := by simp

instance (W : WList α β) : W.toGraph.Finite where
  vertexSet_finite := by simp
  edgeSet_finite := by simp

/-- Used for well-founded induction on finite graphs by number of vertices -/
lemma encard_delete_vertex_lt {G : Graph α β} [G.Finite] (hx : x ∈ V(G)) :
    V(G - {x}).encard < V(G).encard := by
  rw [vertexDelete_vertexSet]
  exact (G.vertexSet_finite.subset diff_subset).encard_lt_encard (by simpa)

/-- Used for well-founded induction on finite graphs by number of edges -/
lemma encard_delete_edge_lt {G : Graph α β} [G.Finite] (he : e ∈ E(G)) :
    E(G ＼ {e}).encard < E(G).encard := by
  rw [edgeDelete_edgeSet]
  exact (G.edgeSet_finite.subset diff_subset).encard_lt_encard (by simpa)

-- instance [G.Finite] : WellFoundedLT G.Subgraph := inferInstance

-- instance [G.Finite] : WellFoundedLT G.ClosedSubgraph := inferInstance

/-! ### Local Finiteness -/

/-- A graph is `LocallyFinite` if each of its vertices is incident with finitely many edges. -/
protected class LocallyFinite (G : Graph α β) where
  finite : ∀ x, {e | G.Inc e x}.Finite

lemma finite_setOf_inc (G : Graph α β) [G.LocallyFinite] : {e | G.Inc e x}.Finite :=
  LocallyFinite.finite x

lemma finite_setOf_adj (G : Graph α β) [G.LocallyFinite] : {y | G.Adj x y}.Finite := by
  change Finite {y // G.Adj x y}
  have : Finite {e // G.Inc e x} := G.finite_setOf_inc
  refine Finite.of_injective (β := {e // G.Inc e x})
    (fun y ↦ ⟨y.2.choose, y.2.choose_spec.inc_left⟩) fun ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩ ↦ ?_
  simp only [Subtype.mk.injEq]
  generalize_proofs h₁ h₂
  refine fun h ↦  h₁.choose_spec.right_unique ?_
  rw [h]
  exact h₂.choose_spec

lemma finite_setOf_isNonloopAt (G : Graph α β) [G.LocallyFinite] :
  {e | G.IsNonloopAt e x}.Finite := G.finite_setOf_inc.subset fun _ he ↦ he.inc

lemma finite_setOf_isLoopAt (G : Graph α β) [G.LocallyFinite] :
  {e | G.IsLoopAt e x}.Finite := G.finite_setOf_inc.subset fun _ he ↦ he.inc

instance [Finite β] (G : Graph α β) : G.LocallyFinite where
  finite _ := toFinite ..

lemma LocallyFinite.mono (hG : G.LocallyFinite) (hle : H ≤ G) : H.LocallyFinite where
  finite _ := G.finite_setOf_inc.subset fun _ he ↦ he.of_le hle

instance [G.LocallyFinite] (X : Set α) : G[X].LocallyFinite where
  finite _ := G.finite_setOf_inc.subset fun _ ⟨_, he⟩ ↦ (induce_isLink_iff.1 he).1.inc_left

instance [G.LocallyFinite] (X : Set α) : (G - X).LocallyFinite :=
  ‹G.LocallyFinite›.mono vertexDelete_le

instance [G.LocallyFinite] (F : Set β) : (G ↾ F).LocallyFinite :=
  ‹G.LocallyFinite›.mono edgeRestrict_le

instance [G.LocallyFinite] (F : Set β) : (G ＼ F).LocallyFinite :=
  ‹G.LocallyFinite›.mono edgeDelete_le

instance [G.Finite] : G.LocallyFinite where
  finite _ := G.edgeSet_finite.subset fun _ ↦ Inc.edge_mem

instance [G.LocallyFinite] [H.LocallyFinite] : (G ∪ H).LocallyFinite where
  finite x := by
    refine ((G.finite_setOf_inc (x := x)).union (H.finite_setOf_inc (x := x))).subset ?_
    simp_rw [union_inc_iff, subset_def]
    aesop

instance (V : Set α) : (Graph.noEdge V β).LocallyFinite where
  finite := by simp

@[simp]
lemma vertexSet_finite_iff [G.LocallyFinite] : V(G).Finite ↔ G.Finite := by
  refine ⟨fun h ↦ ⟨h, ?_⟩, fun h ↦ Finite.vertexSet_finite⟩
  refine (h.biUnion (t := fun v ↦ {e | G.Inc e v}) (fun i a ↦ LocallyFinite.finite i )).subset ?_
  simp only [subset_def, mem_iUnion, mem_setOf_eq, exists_prop]
  intro e he
  obtain ⟨x, y, hx⟩ := exists_isLink_of_mem_edgeSet he
  exact ⟨_, hx.left_mem, hx.inc_left⟩

end Graph

-- lemma IsForest.exists_isLeaf [G.Finite] (hG : )
