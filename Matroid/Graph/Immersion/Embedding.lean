module

public import Matroid.Graph.Hom.Image
public import Matroid.Graph.Immersion.Basic

/-!
# Embeddings as immersions

A graph embedding gives a topological immersion whose routes each contain one edge.
An isomorphism gives a surjective topological immersion.
-/

@[expose] public noncomputable section

open Set Function WList
open scoped Sym2

variable {V E V' E' : Type*} {G : Graph V E} {H : Graph V' E'}

namespace Graph.Emb

/-- Replace every edge of a graph embedding by the corresponding one-edge route. -/
def toImmersion (F : Emb G H) : Immersion G H := by
  let route (e : E(G)) : WList V' E' :=
    let h := H.exists_isLink_of_mem_edgeSet (F.edgeMap e).2
    cons h.choose (F.edgeMap e).1 (nil h.choose_spec.choose)
  refine
    { vertex := F.vertEmbedding
      route := route
      route_isTrail := fun e ↦ ?_
      route_nonempty := fun e ↦ by simp [route]
      route_ends := fun e ↦ ?_
      route_edge_disjoint := fun e f hef ↦ ?_ }
  · let h := H.exists_isLink_of_mem_edgeSet (F.edgeMap e).2
    simp [route, h.choose_spec.choose_spec, h.choose_spec.choose_spec.right_mem]
  · obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet e.2
    let h := H.exists_isLink_of_mem_edgeSet (F.edgeMap e).2
    have hmap := F.map_isLink (e := e)
      (x := ⟨x, hxy.left_mem⟩) (y := ⟨y, hxy.right_mem⟩) hxy
    rw [hxy.ends_eq, Sym2.map_mk]
    exact congrArg (Sym2.map Subtype.val)
      (hmap.ends_eq.symm.trans h.choose_spec.choose_spec.ends_eq)
  · apply disjoint_left.mpr
    intro f' he hf
    have he' : f' = (F.edgeMap e).1 := by simpa [route] using he
    have hf' : f' = (F.edgeMap f).1 := by simpa [route] using hf
    exact hef (F.edgeMap_injective (Subtype.ext (he'.symm.trans hf')))

@[simp]
lemma toImmersion_vertex (F : Emb G H) : F.toImmersion.vertex = F.vertEmbedding := rfl

@[simp]
lemma toImmersion_route_length (F : Emb G H) (e : E(G)) :
    (F.toImmersion.route e).length = 1 := rfl

@[simp]
lemma toImmersion_route_edgeSet (F : Emb G H) (e : E(G)) :
    E(F.toImmersion.route e) = {(F.edgeMap e).1} := by
  simp [toImmersion]

@[simp]
lemma toImmersion_route_internalVertexSet (F : Emb G H) (e : E(G)) :
    (F.toImmersion.route e).internalVertexSet = ∅ := by
  simp [toImmersion, internalVertexSet]

@[simp]
lemma toImmersion_topological (F : Emb G H) : F.toImmersion.Topological := by
  refine ⟨fun e ↦ by simp, fun e ↦ ?_, fun e f hef ↦ by simp⟩
  obtain ⟨x, f, y, hroute⟩ := (F.toImmersion.route e).length_eq_one_iff.mp
    (F.toImmersion_route_length e)
  have hlink := (F.toImmersion.route_isWalk e)
  rw [hroute] at hlink ⊢
  have hxy : H.IsLink f x y := (cons_isWalk_iff.mp hlink).1
  obtain rfl | hne := eq_or_ne x y
  · exact Or.inr ((nil_isPath hxy.left_mem).cons_isCyclicWalk hxy (by simp))
  · exact Or.inl (by simp [hxy, hxy.right_mem, hne])

lemma toImmersion_strong (F : Emb G H) : F.toImmersion.Strong := F.toImmersion_topological.1

@[simp]
lemma toImmersion_image_vertexSet (F : Emb G H) :
    V(F.toImmersion.Image) = range (Subtype.val ∘ F.vertMap) := by
  rw [Immersion.image_vertexSet_eq_union_internal]
  simp only [toImmersion_vertex, toImmersion_route_internalVertexSet, iUnion_empty, union_empty]
  rfl

@[simp]
lemma toImmersion_image_edgeSet (F : Emb G H) :
    E(F.toImmersion.Image) = range (Subtype.val ∘ F.edgeMap) := by
  rw [Immersion.image_edgeSet]
  simp only [toImmersion_route_edgeSet, iUnion_singleton_eq_range]
  rfl

/-- The one-edge routes occupy exactly the image of the embedding. -/
@[simp]
lemma toImmersion_image (F : Emb G H) : F.toImmersion.Image = F.Image := by
  apply ext_of_le_le F.toImmersion.image_le F.image_le
  · rw [F.toImmersion_image_vertexSet, F.image_vertexSet]
    rfl
  · rw [F.toImmersion_image_edgeSet, F.image_edgeSet]
    rfl

/-- Passing from an embedding to its one-edge immersion preserves surjectivity. -/
lemma toImmersion_surjective_iff (F : Emb G H) :
    F.toImmersion.Surjective ↔ F.Surjective := by
  rw [Immersion.Surjective, Hom.Surjective, F.toImmersion_image]

end Graph.Emb

namespace Graph.Iso

/-- An isomorphism occupies the entire host when regarded as an immersion. -/
lemma toImmersion_surjective (F : Iso G H) : F.toEmb.toImmersion.Surjective := by
  exact F.toEmb.toImmersion_surjective_iff.mpr F.surjective

end Graph.Iso
