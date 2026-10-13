module

public import Matroid.Graph.Walk.Cycle
public import Matroid.Graph.WList.TakeDrop.Index

/-!
# Graph immersions

An immersion replaces edges by nonempty, pairwise edge-disjoint trails. The predicates
`Immersion.Strong` and `Immersion.Topological` impose additional vertex restrictions.
`Immersion.Image` retains the vertices and edges used by the chosen routes, including repeated
visits to vertices. `Immersion.Surjective` asserts that this image is the whole host.

This file develops the route and image API, restriction to the image, and normalization to
path or cycle routes. Normalization keeps the branch vertices but may shrink the image.
-/

@[expose] public section

namespace Graph

open Set Function Graph WList
open scoped Sym2

/-! ## Definitions -/

section Definitions

variable {V E V' E' : Type*} {H : Graph V E} {G : Graph V' E'}

/-- An immersion with specified nonempty, pairwise edge-disjoint trail routes. -/
structure Immersion (H : Graph V E) (G : Graph V' E') where
  vertex : V(H) ↪ V(G)
  route : E(H) → WList V' E'
  route_isTrail : ∀ e, G.IsTrail (route e)
  route_nonempty : ∀ e, (route e).Nonempty
  route_ends : ∀ e, Sym2.map (Subtype.val ∘ vertex) (H.ends e) = s((route e).first, (route e).last)
  route_edge_disjoint : Pairwise (Disjoint on fun e ↦ (route e).edgeSet)

@[ext]
lemma Immersion.ext {M N : Immersion H G}
    (hvertex : ∀ v, M.vertex v = N.vertex v) (hroute : ∀ e, M.route e = N.route e) : M = N := by
  cases M
  cases N
  congr
  · exact Embedding.ext hvertex
  · exact funext hroute

/-- The subgraph occupied by the branch vertices and routes. -/
def Immersion.Image (M : Immersion H G) : Graph V' E' :=
  G[range (Subtype.val ∘ M.vertex) ∪ ⋃ e : E(H), (M.route e).vertexSet]
    ↾ ⋃ e : E(H), (M.route e).edgeSet

/-- The chosen immersion occupies its entire host. -/
def Immersion.Surjective (M : Immersion H G) : Prop := M.Image = G

/-- Route interiors avoid the branch vertices. -/
def Immersion.Strong (M : Immersion H G) : Prop :=
  ∀ e, Disjoint (M.route e).internalVertexSet (range (Subtype.val ∘ M.vertex))

/-- A strong immersion with path or cycle routes and pairwise disjoint route interiors. -/
def Immersion.Topological (M : Immersion H G) : Prop :=
  M.Strong ∧ (∀ e, G.IsPath (M.route e) ∨ G.IsCyclicWalk (M.route e)) ∧
    Pairwise (Disjoint on fun e ↦ (M.route e).internalVertexSet)

/-- There is an immersion of `H` in `G`. -/
def IsImmersion (H : Graph V E) (G : Graph V' E') : Prop := Nonempty (Immersion H G)

/-- There is a strong immersion of `H` in `G`. -/
def IsStrongImmersion (H : Graph V E) (G : Graph V' E') : Prop :=
  ∃ M : Immersion H G, M.Strong

/-- There is a topological immersion of `H` in `G`. -/
def IsTopologicalMinor' (H : Graph V E) (G : Graph V' E') : Prop :=
  ∃ M : Immersion H G, M.Topological

end Definitions

/-! ## Routes -/

section Routes

variable {α β γ δ : Type*} {G : Graph α β} {J : Graph γ δ}

namespace Immersion

variable (M : Immersion J G)

lemma vertex_range_subset : range (Subtype.val ∘ M.vertex) ⊆ V(G) := by
  rintro _ ⟨x, rfl⟩
  exact (M.vertex x).prop

lemma route_isWalk (e : E(J)) : G.IsWalk (M.route e) :=
  (M.route_isTrail e).isWalk

lemma route_vertexSet_subset (e : E(J)) : V(M.route e) ⊆ V(G) :=
  (M.route_isTrail e).vertexSet_subset

lemma route_edgeSet_subset (e : E(J)) : E(M.route e) ⊆ E(G) :=
  (M.route_isTrail e).edgeSet_subset

lemma mem_vertexSet_of_mem_route {e : E(J)} {x : α} (hx : x ∈ M.route e) : x ∈ V(G) :=
  M.route_vertexSet_subset e hx

lemma mem_edgeSet_of_mem_route {e : E(J)} {f : β} (hf : f ∈ E(M.route e)) : f ∈ E(G) :=
  M.route_edgeSet_subset e hf

/-- The ends of a route, expressed using a link of its source graph. -/
lemma route_ends_eq {e : E(J)} {u v : γ} (huv : J.IsLink e.1 u v) :
    s(((M.vertex ⟨u, huv.left_mem⟩ : V(G)) : α),
      ((M.vertex ⟨v, huv.right_mem⟩ : V(G)) : α)) =
      s((M.route e).first, (M.route e).last) := by
  rw [← M.route_ends e, huv.ends_eq, Sym2.map_mk]
  rfl

lemma ends_mem_vertex_range (e : E(J)) :
    (M.route e).first ∈ range (Subtype.val ∘ M.vertex) ∧
      (M.route e).last ∈ range (Subtype.val ∘ M.vertex) := by
  obtain ⟨u, v, huv⟩ := exists_isLink_of_mem_edgeSet e.prop
  obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := Sym2.eq_iff.mp (M.route_ends_eq huv)
  · exact ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
  · exact ⟨⟨_, h2⟩, ⟨_, h1⟩⟩

/-- A host edge belongs to at most one route. -/
lemma eq_of_mem_route_edgeSet {e f : E(J)} {g : β}
    (hge : g ∈ E(M.route e)) (hgf : g ∈ E(M.route f)) : e = f := by
  by_contra hne
  exact (M.route_edge_disjoint hne).notMem_of_mem_left hge hgf

variable {M}

lemma Strong.notMem_vertex_range_of_mem_internalVertexSet (hM : M.Strong) {e : E(J)} {x : α}
    (hx : x ∈ (M.route e).internalVertexSet) : x ∉ range (Subtype.val ∘ M.vertex) :=
  (hM e).notMem_of_mem_left hx

lemma Strong.notMem_internalVertexSet_of_mem_vertex_range (hM : M.Strong) {e : E(J)} {x : α}
    (hx : x ∈ range (Subtype.val ∘ M.vertex)) : x ∉ (M.route e).internalVertexSet :=
  (hM e).notMem_of_mem_right hx

/-- If a strong-immersion route meets a branch vertex, it is one of the route ends. -/
lemma Strong.mem_ends_of_mem_route_of_mem_vertex_range (hM : M.Strong) {e : E(J)} {x : α}
    (hxW : x ∈ M.route e) (hxB : x ∈ range (Subtype.val ∘ M.vertex)) :
    x = (M.route e).first ∨ x = (M.route e).last := by
  obtain rfl | hx | rfl := mem_iff_eq_first_or_mem_internalVertexSet_or_eq_last.mp hxW
  · exact Or.inl rfl
  · exact (hM.notMem_vertex_range_of_mem_internalVertexSet hx hxB).elim
  · exact Or.inr rfl

lemma Strong.mem_vertex_range_iff_mem_ends (hM : M.Strong) {e : E(J)} {x : α}
    (hxW : x ∈ M.route e) :
    x ∈ range (Subtype.val ∘ M.vertex) ↔ x = (M.route e).first ∨ x = (M.route e).last := by
  refine ⟨hM.mem_ends_of_mem_route_of_mem_vertex_range hxW, ?_⟩
  rintro (rfl | rfl)
  · exact (M.ends_mem_vertex_range e).1
  · exact (M.ends_mem_vertex_range e).2

/-- A strong-immersion route meets the branch vertices exactly at its two ends. -/
lemma Strong.route_inter_vertex_range (hM : M.Strong) (e : E(J)) :
    V(M.route e) ∩ range (Subtype.val ∘ M.vertex) =
      {(M.route e).first, (M.route e).last} := by
  refine subset_antisymm ?_ fun x hx ↦ ?_
  · rintro x ⟨hxW, hxB⟩
    simpa using hM.mem_ends_of_mem_route_of_mem_vertex_range hxW hxB
  obtain rfl | rfl := hx
  · exact ⟨first_mem, (M.ends_mem_vertex_range e).1⟩
  · exact ⟨last_mem, (M.ends_mem_vertex_range e).2⟩

end Immersion

end Routes

/-! ## Image -/

section Image

variable {α β γ δ : Type*} {G : Graph α β} {J : Graph γ δ}

namespace Immersion

variable (M : Immersion J G)

lemma image_le : M.Image ≤ G :=
  restrict_le.trans <| induce_le <|
    union_subset M.vertex_range_subset <| iUnion_subset M.route_vertexSet_subset

@[simp]
lemma image_vertexSet : V(M.Image) = range (Subtype.val ∘ M.vertex) ∪ ⋃ e : E(J), V(M.route e) := by
  simp [Image]

@[simp]
lemma image_edgeSet : E(M.Image) = ⋃ e : E(J), E(M.route e) := by
  rw [Image, edgeSet_restrict]
  refine subset_antisymm inter_subset_right fun e he ↦ ?_
  obtain ⟨r, her⟩ := mem_iUnion.mp he
  have hle : G[V(M.route r)] ≤ G[range (Subtype.val ∘ M.vertex) ∪ ⋃ e : E(J), V(M.route e)] :=
    G.induce_mono_right (fun _ hx ↦ mem_union_right _ (mem_iUnion.mpr ⟨r, hx⟩))
  exact ⟨hle.edgeSet_mono ((M.route_isWalk r).edgeSet_subset_edgeSet_induce her),
    mem_iUnion.mpr ⟨r, her⟩⟩

lemma route_vertexSet_subset_image (e : E(J)) : V(M.route e) ⊆ V(M.Image) := by
  rw [M.image_vertexSet]
  exact fun _ hx ↦ mem_union_right _ (mem_iUnion.mpr ⟨e, hx⟩)

lemma route_edgeSet_subset_image (e : E(J)) : E(M.route e) ⊆ E(M.Image) := by
  rw [M.image_edgeSet]
  exact fun _ hx ↦ mem_iUnion.mpr ⟨e, hx⟩

lemma route_isTrail_image (e : E(J)) : M.Image.IsTrail (M.route e) :=
  (M.route_isTrail e).isTrail_le_of_nonempty M.image_le
    (M.route_edgeSet_subset_image e) (M.route_nonempty e)

/-- Restricting to the image preserves and reflects whether a route is a path. -/
@[simp]
lemma route_isPath_image_iff (e : E(J)) : M.Image.IsPath (M.route e) ↔ G.IsPath (M.route e) :=
  ⟨fun h ↦ h.of_le M.image_le, fun h ↦ h.isPath_le_of_nonempty M.image_le
    (M.route_edgeSet_subset_image e) (M.route_nonempty e)⟩

/-- Restricting to the image preserves and reflects whether a route is a cyclic walk. -/
@[simp]
lemma route_isCyclicWalk_image_iff (e : E(J)) :
    M.Image.IsCyclicWalk (M.route e) ↔ G.IsCyclicWalk (M.route e) :=
  ⟨fun h ↦ h.of_le M.image_le, fun h ↦ h.isCycle_of_le M.image_le
    (M.route_edgeSet_subset_image e)⟩

lemma vertex_range_subset_image : range (Subtype.val ∘ M.vertex) ⊆ V(M.Image) := by
  rw [M.image_vertexSet]
  exact subset_union_left

lemma vertex_mem_image (x : V(J)) : (M.vertex x).1 ∈ V(M.Image) :=
  M.vertex_range_subset_image ⟨x, rfl⟩

/-- Route endpoints contribute no vertices beyond the branch vertices. -/
lemma image_vertexSet_eq_union_internal :
    V(M.Image) = range (Subtype.val ∘ M.vertex) ∪ ⋃ e : E(J), (M.route e).internalVertexSet := by
  rw [M.image_vertexSet]
  ext x
  simp only [mem_union, mem_iUnion]
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩ <;> obtain (hxbranch | ⟨e, hi⟩) := hx
  · exact Or.inl hxbranch
  · obtain rfl | hi | rfl := mem_iff_eq_first_or_mem_internalVertexSet_or_eq_last.mp hi
    · exact Or.inl (M.ends_mem_vertex_range e).1
    · exact Or.inr ⟨e, hi⟩
    · exact Or.inl (M.ends_mem_vertex_range e).2
  · exact Or.inl hxbranch
  exact Or.inr ⟨e, mem_iff_eq_first_or_mem_internalVertexSet_or_eq_last.mpr (Or.inr (Or.inl hi))⟩

variable {M}

lemma Surjective.vertexSet_eq (h : M.Surjective) :
    range (Subtype.val ∘ M.vertex) ∪ ⋃ e : E(J), V(M.route e) = V(G) := by
  simpa using congrArg Graph.vertexSet h

lemma Surjective.edgeSet_eq (h : M.Surjective) : ⋃ e : E(J), E(M.route e) = E(G) := by
  simpa using congrArg Graph.edgeSet h

/-- Surjectivity is equivalent to covering both the host vertices and its edges. -/
theorem surjective_iff_covers :
    M.Surjective ↔
      V(G) ⊆ range (Subtype.val ∘ M.vertex) ∪ ⋃ e : E(J), (M.route e).internalVertexSet ∧
      E(G) ⊆ ⋃ e : E(J), E(M.route e) := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨hV, hE⟩ ↦ ext_of_le_le M.image_le le_rfl ?_ ?_⟩
  · rw [← M.image_vertexSet_eq_union_internal, h]
  · rw [h.edgeSet_eq]
  · rw [← M.image_vertexSet_eq_union_internal] at hV
    exact M.image_le.vertexSet_mono.antisymm hV
  · rw [M.image_edgeSet]
    exact (iUnion_subset M.route_edgeSet_subset).antisymm hE

variable (M)

/-- Restrict an immersion to its image without changing any route. -/
def toImage : Immersion J M.Image where
  vertex :=
    { toFun x := ⟨(M.vertex x).1, M.vertex_mem_image x⟩
      inj' _ _ h:= M.vertex.injective (Subtype.ext (congrArg (fun z : V(M.Image) ↦ z.1) h)) }
  route := M.route
  route_isTrail := M.route_isTrail_image
  route_nonempty := M.route_nonempty
  route_ends := M.route_ends
  route_edge_disjoint := M.route_edge_disjoint

@[simp]
lemma toImage_vertex_val (x : V(J)) : (M.toImage.vertex x).1 = (M.vertex x).1 := rfl

@[simp]
lemma toImage_route (e : E(J)) : M.toImage.route e = M.route e := rfl

@[simp]
lemma toImage_image : M.toImage.Image = M.Image := by
  apply ext_of_le_le M.toImage.image_le le_rfl
  · rw [M.toImage.image_vertexSet]
    exact M.image_vertexSet.symm
  · rw [M.toImage.image_edgeSet, M.image_edgeSet]
    rfl

lemma toImage_surjective : M.toImage.Surjective := M.toImage_image

@[simp]
lemma strong_toImage_iff : M.toImage.Strong ↔ M.Strong := Iff.rfl

@[simp]
lemma topological_toImage_iff : M.toImage.Topological ↔ M.Topological := by
  simp only [Topological, strong_toImage_iff, toImage_route,
    route_isPath_image_iff, route_isCyclicWalk_image_iff]

variable {M}

lemma Strong.toImage (hM : M.Strong) : M.toImage.Strong := hM

lemma Topological.toImage (hM : M.Topological) : M.toImage.Topological :=
  M.topological_toImage_iff.mpr hM

end Immersion

end Image

/-! ## Normalization -/

section Normalization

variable {α β γ δ : Type*} {G : Graph α β} {H : Graph γ δ}

namespace Immersion

open Classical

/-- Apply `WList.cycleBypass` to every route, retaining the branch embedding and a sublist
of each route. -/
@[simps]
noncomputable def normalize (M : Immersion H G) : Immersion H G where
  vertex := M.vertex
  route := fun e ↦ (M.route e).cycleBypass
  route_isTrail := fun e ↦ (M.route_isTrail e).sublist (M.route e).cycleBypass_isSublist
  route_nonempty := fun e ↦ cycleBypass_nonempty (M.route_nonempty e)
  route_ends := fun e ↦ by simpa using M.route_ends e
  route_edge_disjoint := fun e f hef ↦ (M.route_edge_disjoint hef).mono
    (M.route e).cycleBypass_isSublist.edge_subset (M.route f).cycleBypass_isSublist.edge_subset

lemma normalize_route_isSublist (M : Immersion H G) (e : E(H)) :
    (M.normalize.route e).IsSublist (M.route e) := (M.route e).cycleBypass_isSublist

lemma normalize_route_isSimple (M : Immersion H G) (e : E(H)) :
    G.IsPath (M.normalize.route e) ∨ G.IsCyclicWalk (M.normalize.route e) :=
  (M.route_isTrail e).cycleBypass_isSimple

lemma Strong.normalize {M : Immersion H G} (hM : M.Strong) : M.normalize.Strong := by
  intro e
  exact (hM e).mono_left (M.normalize_route_isSublist e).internalVertexSet_subset_internalVertexSet

lemma normalize_image_le (M : Immersion H G) : M.normalize.Image ≤ M.Image := by
  apply (Compatible.of_le_le M.normalize.image_le M.image_le).le_iff.mpr
  constructor
  · rw [M.normalize.image_vertexSet, M.image_vertexSet, normalize_vertex]
    exact union_subset_union_right _ <| iUnion_mono fun e ↦ (M.normalize_route_isSublist e).subset
  · rw [M.normalize.image_edgeSet, M.image_edgeSet]
    exact iUnion_mono fun e ↦ (M.normalize_route_isSublist e).edge_subset

/-- The fixed points of normalization are exactly the immersions with simple routes. -/
lemma normalize_eq_self_iff (M : Immersion H G) : M.normalize = M ↔
    ∀ e, G.IsPath (M.route e) ∨ G.IsCyclicWalk (M.route e) := by
  classical
  refine ⟨fun h e ↦ ?_, fun h ↦ Immersion.ext (fun _ ↦ rfl) (fun e ↦ ?_)⟩
  · simpa only [h] using M.normalize_route_isSimple e
  · exact (M.route_isTrail e).cycleBypass_eq_self_iff.mpr (h e)

@[simp]
lemma normalize_normalize (M : Immersion H G) : M.normalize.normalize = M.normalize :=
  M.normalize.normalize_eq_self_iff.mpr M.normalize_route_isSimple

end Immersion

theorem isImmersion_iff_exists_simple_routes : IsImmersion H G ↔
    ∃ M : Immersion H G, ∀ e, G.IsPath (M.route e) ∨ G.IsCyclicWalk (M.route e) :=
  ⟨fun ⟨M⟩ ↦ ⟨M.normalize, M.normalize_route_isSimple⟩, fun ⟨M, _⟩ ↦ ⟨M⟩⟩

theorem isStrongImmersion_iff_exists_simple_routes : IsStrongImmersion H G ↔
    ∃ M : Immersion H G, M.Strong ∧
      ∀ e, G.IsPath (M.route e) ∨ G.IsCyclicWalk (M.route e) :=
  ⟨fun ⟨M, hM⟩ ↦ ⟨M.normalize, hM.normalize, M.normalize_route_isSimple⟩,
    fun ⟨M, hM, _⟩ ↦ ⟨M, hM⟩⟩

end Normalization

end Graph
