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

section

variable (F : Emb G H)
include F

/-- Replace every edge of a graph embedding by the corresponding one-edge route. -/
@[simps (attr := grind =)]
def toImmersion : Immersion G H where
  vertex := F.vertEmbedding
  route e := H.exists_isLink_of_mem_edgeSet (F.edgeMap e).prop |>.choose_spec.choose_spec.walk
  route_isTrail e := by simp
  route_nonempty e := by simp
  route_ends e := by
    obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet e.prop
    rw [hxy.ends_eq, Sym2.map_mk]
    exact congrArg (Sym2.map Subtype.val)
      ((F.map_isLink hxy).ends_eq.symm.trans <| H.exists_isLink_of_mem_edgeSet (F.edgeMap e).2
      |>.choose_spec.choose_spec.ends_eq)
  route_edge_disjoint e f hef := disjoint_left.mpr fun f' he hf ↦ hef <| by
    simp only [IsLink.walk_edgeSet, mem_singleton_iff] at he hf
    exact F.edgeMap_injective <| Subtype.val_injective <| he ▸ hf

@[simp, grind .]
lemma toImmersion_topological : F.toImmersion.Topological := by
  refine ⟨fun e ↦ by simp, fun e ↦ ?_, fun e f hef ↦ by simp⟩
  obtain ⟨x, f, y, hroute⟩ :=
    (F.toImmersion.route e).length_eq_one_iff.mp (show (F.toImmersion.route e).length = 1 by simp)
  have hlink := F.toImmersion.route_isWalk e
  rw [hroute] at hlink ⊢
  replace hlink : H.IsLink f x y := (cons_isWalk_iff.mp hlink).left
  refine (eq_or_ne x y).symm.imp (fun hne ↦ ?_) ?_
  · simp [hlink, hlink.right_mem, hne]
  rintro rfl
  exact (nil_isPath hlink.left_mem).cons_isCyclicWalk hlink <| by simp

@[simp, grind .]
lemma toImmersion_strong : F.toImmersion.Strong := F.toImmersion_topological.1

/-- The one-edge routes occupy exactly the image of the embedding. -/
@[simp, grind =]
lemma toImmersion_image : F.toImmersion.Image = F.Image := by
  refine ext_of_le_le F.toImmersion.image_le F.image_le ?_ ?_
  · simp_rw [Immersion.image_vertexSet_eq_union_internal, toImmersion_vertex, toImmersion_route,
    IsLink.walk_internalVertexSet, iUnion_empty, union_empty]
    rfl
  simp_rw [Immersion.image_edgeSet, toImmersion_route, IsLink.walk_edgeSet, Hom.image_edgeSet,
    iUnion_singleton_eq_range]
  rfl

/-- Passing from an embedding to its one-edge immersion preserves surjectivity. -/
@[simp, grind =]
lemma toImmersion_surjective_iff : F.toImmersion.Surjective ↔ F.Surjective := by
  rw [Immersion.Surjective, Hom.Surjective, F.toImmersion_image]

end

end Graph.Emb

namespace Graph.Iso

/-- An isomorphism occupies the entire host when regarded as an immersion. -/
lemma toImmersion_surjective (F : Iso G H) : F.toEmb.toImmersion.Surjective :=
  F.toEmb.toImmersion_surjective_iff.mpr F.surjective

end Graph.Iso
