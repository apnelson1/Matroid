module

public import Matroid.Graph.Relabel
public import Matroid.Graph.Map
public import Matroid.Graph.Simple
public import Matroid.Graph.WList.TakeDrop.Index

/-!
# Topological minors

This file contains the intrinsic theory of topological-minor witnesses.  It deliberately does not
import graph minors or contraction theory; those live downstream in `Graph/Minor/Topological`.
Subdivision/exhaustiveness is also kept in a separate module.

There are two witness structures.

* `Graph.TopologicalMinor H G` is the label-coherent version: `H` and `G` use the same ambient
  vertex and edge types, every vertex of `H` is literally a vertex of `G`, and the label of each
  edge `e` of `H` occurs on its own route.
* `Graph.IsoTopologicalMinor H G` is the isomorphism-invariant version.  The pattern may live on
  unrelated carrier types and is placed in `G` through an embedding of its active vertex set.

The route geometry is intentionally aligned between the two structures.  Internal route vertices
avoid branch vertices, distinct routes have disjoint interiors, and in the heterogeneous structure
edge-disjointness is recorded explicitly.  In the label-coherent structure route edge-disjointness
is derived from the distinguished edge labels.

## Construction interfaces

The fully general heterogeneous route model is the structure itself.  Two convenience constructors
are supplied for the common path-only cases:

* `IsoTopologicalMinor.ofPathRoutes`: loopless patterns; route edge-disjointness is supplied.
* `IsoTopologicalMinor.ofPathRoutes_of_simple`: simple patterns; route edge-disjointness follows
  from the other hypotheses.

`SubgraphReplacement` is the complementary host-first construction interface.  It is useful in
particular for multigraphs: one specifies disjoint subgraphs of the host and collapses each to a
single distinguished edge.

## Support and normalization

Every witness has a `usedSubgraph`, the part of the host occupied by its branch vertices and
routes.  Heterogeneous witnesses can be normalized by relabelling the pattern onto the host's
carrier types, choosing one representative host edge from each route.
-/

@[expose] public section

variable {α β γ δ ι : Type*} {G H K : Graph α β} {J L : Graph γ δ} {u v x y z : α} {e f g : β}
  {W : WList α β}

open Set WList Function
open scoped Sym2

namespace Graph

/-! ## Core witness structures -/

/-- A label-coherent topological-minor model of `H` in `G`.

The pattern and host use the same ambient vertex and edge types.  Every pattern edge `e` occurs on
its own route, which is the extra coherence unavailable in `IsoTopologicalMinor`.
-/
structure TopologicalMinor (H G : Graph α β) where
  /-- Pattern vertices are literally vertices of the host. -/
  vertex_subset : V(H) ⊆ V(G)
  /-- The route replacing each pattern edge. -/
  route : E(H) → WList α β
  /-- The label of a pattern edge occurs on its own route. -/
  route_edge_mem : ∀ e, e.val ∈ E(route e)
  /-- A route is either a path, or a cyclic walk for a loop edge. -/
  route_isSimple : ∀ e, G.IsPath (route e) ∨ G.IsCyclicWalk (route e)
  /-- The ends of a pattern edge are exactly the ends of its route, after forgetting subtypes. -/
  route_ends : ∀ e,
    Sym2.map (fun x : V(H) ↦ (x : α)) (H.ends e) =
      s((route e).first, (route e).last)
  /-- Internal route vertices are not branch vertices. -/
  route_internal_disjoint_branchVertices : ∀ e,
    Disjoint (route e).internalVertexSet V(H)
  /-- Distinct routes have disjoint interiors. -/
  route_internal_disjoint : ∀ e f, e ≠ f →
    Disjoint (route e).internalVertexSet (route f).internalVertexSet

/-- The proposition that `H` is a label-coherent topological minor of `G`. -/
def IsTopologicalMinor (H G : Graph α β) : Prop :=
  Nonempty (H.TopologicalMinor G)

/-- An isomorphism-invariant topological-minor model of `J` in `G`.

The pattern and host may use unrelated carrier types.  Branch vertices are embedded directly in the
ambient vertex type of the host; membership in the active host vertex set is recorded separately.
This makes relabelling and composition with graph isomorphisms straightforward.
-/
structure IsoTopologicalMinor (J : Graph γ δ) (G : Graph α β) where
  /-- Placement of the pattern vertices in the ambient host carrier. -/
  branchVertex : V(J) ↪ α
  /-- Every branch vertex is active in the host. -/
  branchVertex_mem : ∀ x, branchVertex x ∈ V(G)
  /-- The route replacing each pattern edge. -/
  route : E(J) → WList α β
  /-- A route is either a path, or a cyclic walk for a loop edge. -/
  route_isSimple : ∀ e, G.IsPath (route e) ∨ G.IsCyclicWalk (route e)
  /-- Every pattern edge has a nontrivial route. -/
  route_nonempty : ∀ e, (route e).Nonempty
  /-- Pattern ends are sent to the ends of the corresponding route. -/
  route_ends : ∀ e,
    Sym2.map branchVertex (J.ends e) = s((route e).first, (route e).last)
  /-- Internal route vertices are not branch vertices. -/
  route_internal_disjoint_branchVertices : ∀ e,
    Disjoint (route e).internalVertexSet (range branchVertex)
  /-- Distinct routes have disjoint interiors. -/
  route_internal_disjoint : ∀ e f, e ≠ f →
    Disjoint (route e).internalVertexSet (route f).internalVertexSet
  /-- Distinct routes use disjoint host edges. -/
  route_edge_disjoint : ∀ e f, e ≠ f → Disjoint E(route e) E(route f)

/-- The proposition that `J` is an isomorphism-invariant topological minor of `G`. -/
def IsIsoTopologicalMinor (J : Graph γ δ) (G : Graph α β) : Prop :=
  Nonempty (J.IsoTopologicalMinor G)

/-! ## Label-coherent topological minors -/

namespace TopologicalMinor

variable (M : H.TopologicalMinor G)

lemma vertexSet_mono (M : H.TopologicalMinor G) : V(H) ⊆ V(G) := M.vertex_subset

lemma route_isTrail (e : E(H)) : G.IsTrail (M.route e) :=
  (M.route_isSimple e).elim IsPath.isTrail IsCyclicWalk.isTrail

lemma route_nonempty (e : E(H)) : (M.route e).Nonempty := by
  exact nonempty_iff_exists_edge.mpr ⟨e.val, M.route_edge_mem e⟩

/-- The pattern edge really links the two ends of its route. -/
lemma route_isLink (e : E(H)) : H.IsLink e.val (M.route e).first (M.route e).last := by
  obtain ⟨u, v, huv⟩ := exists_isLink_of_mem_edgeSet e.prop
  have hends :
      s(u, v) = s((M.route e).first, (M.route e).last) := by
    rw [← M.route_ends e, huv.ends_eq, Sym2.map_mk]
  obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := Sym2.eq_iff.mp hends
  · simpa [h1, h2] using huv
  · simpa [h1, h2] using huv.symm

lemma edgeSet_mono (M : H.TopologicalMinor G) : E(H) ⊆ E(G) := by
  intro e he
  exact M.route_isTrail ⟨e, he⟩ |>.edgeSet_subset (M.route_edge_mem ⟨e, he⟩)

lemma route_ends_mem_vertexSet (e : E(H)) :
    (M.route e).first ∈ V(H) ∧ (M.route e).last ∈ V(H) :=
  ⟨(M.route_isLink e).left_mem, (M.route_isLink e).right_mem⟩

/-- If two distinct routes meet at a vertex, that vertex is an end of the first route. -/
lemma eq_end_of_mem_of_mem_route {e f : E(H)} {x : α} (hef : e ≠ f)
    (hxe : x ∈ M.route e) (hxf : x ∈ M.route f) :
    x = (M.route e).first ∨ x = (M.route e).last := by
  by_contra hx
  simp only [not_or] at hx
  have hxi := mem_internalVertexSet_of_mem_ne_ends hxe hx
  obtain h1 | h1 | h1 := mem_iff_eq_first_or_mem_internalVertexSet_or_eq_last.mp hxf
  · exact (M.route_internal_disjoint_branchVertices e).notMem_of_mem_left hxi
      (h1 ▸ (M.route_isLink f).left_mem)
  · exact (M.route_internal_disjoint e f hef).notMem_of_mem_left hxi h1
  exact (M.route_internal_disjoint_branchVertices e).notMem_of_mem_left hxi
    (h1 ▸ (M.route_isLink f).right_mem)

/-- If a host edge lies on the routes of two distinct pattern edges, then on the first route it
must be the distinguished pattern-edge label. -/
lemma eq_of_mem_edgeSet_route {e f : E(H)} {g : β} (hef : e ≠ f)
    (hge : g ∈ E(M.route e)) (hgf : g ∈ E(M.route f)) : e.val = g := by
  obtain ⟨a, b, hab⟩ := exists_dInc_of_mem_edge hge
  obtain ⟨c, d, hcd⟩ := exists_dInc_of_mem_edge hgf
  have hmem : a ∈ M.route f ∧ b ∈ M.route f := by
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := ((M.route_isTrail e).isWalk.isLink_of_dInc hab)
      |>.eq_and_eq_or_eq_and_eq ((M.route_isTrail f).isWalk.isLink_of_dInc hcd)
    · exact ⟨hcd.left_mem, hcd.right_mem⟩
    exact ⟨hcd.right_mem, hcd.left_mem⟩
  have ha := M.eq_end_of_mem_of_mem_route hef hab.left_mem hmem.1
  have hb := M.eq_end_of_mem_of_mem_route hef hab.right_mem hmem.2
  obtain hp | hc := M.route_isSimple e
  · have hlen := Nat.succ_le_of_lt (M.route_nonempty e).length_pos |>.eq_of_not_lt'
      <| one_lt_length_iff.not.mpr <| hp.not_nontrivial_of_dInc rfl rfl hab ha hb
    obtain ⟨u, g', v, heq⟩ := (M.route e).length_eq_one_iff.mp hlen
    obtain rfl : g = g' := by simpa [heq] using hge
    simpa [heq] using M.route_edge_mem e
  · obtain rfl : b = a := by
      grind [hc.isClosed, hc.isClosed.symm]
    simpa [hc.eq_loop_of_isLink_self (isLink_iff_dInc.mpr (Or.inl hab))] using
      M.route_edge_mem e

/-- Distinct routes are edge-disjoint.  In the label-coherent structure this is derived rather than
stored: each route contains its own distinguished pattern-edge label. -/
lemma route_edge_disjoint {e f : E(H)} (hef : e ≠ f) :
    Disjoint E(M.route e) E(M.route f) :=
  disjoint_left.mpr fun _ hge hgf ↦ hef <| Subtype.ext <|
    (M.eq_of_mem_edgeSet_route hef hge hgf).trans
      (M.eq_of_mem_edgeSet_route hef.symm hgf hge).symm

/-- A route meets the pattern vertex set exactly at its two ends. -/
lemma route_inter_vertexSet (e : E(H)) :
    V(M.route e) ∩ V(H) = {(M.route e).first, (M.route e).last} := by
  refine subset_antisymm ?_ ?_
  · rintro x ⟨hxW, hxH⟩
    obtain rfl | hx | rfl := mem_iff_eq_first_or_mem_internalVertexSet_or_eq_last.mp hxW
    · simp
    · exact (M.route_internal_disjoint_branchVertices e).notMem_of_mem_left hx hxH |>.elim
    · simp
  · intro x hx
    simp only [mem_insert_iff, mem_singleton_iff] at hx
    obtain rfl | rfl := hx
    · exact ⟨first_mem, (M.route_isLink e).left_mem⟩
    exact ⟨last_mem, (M.route_isLink e).right_mem⟩

/-- A route meets the pattern edge set exactly in its distinguished edge label. -/
lemma route_inter_edgeSet (e : E(H)) : E(M.route e) ∩ E(H) = {e.val} := by
  refine subset_antisymm ?_ (singleton_subset_iff.mpr ⟨M.route_edge_mem e, e.prop⟩)
  rintro f ⟨hfroute, hfH⟩
  rw [mem_singleton_iff]
  by_contra hfe
  let f' : E(H) := ⟨f, hfH⟩
  have hef : e ≠ f' := by
    intro h
    exact hfe (congrArg Subtype.val h).symm
  exact (M.route_edge_disjoint hef).notMem_of_mem_left hfroute (M.route_edge_mem f')

/-- Enlarge the host of a topological-minor witness. -/
noncomputable def mono_right {K : Graph α β} (hGK : G ≤ K) : H.TopologicalMinor K where
  vertex_subset := M.vertex_subset.trans hGK.vertexSet_mono
  route := M.route
  route_edge_mem := M.route_edge_mem
  route_isSimple e := (M.route_isSimple e).imp (·.of_le hGK) (·.of_le hGK)
  route_ends := M.route_ends
  route_internal_disjoint_branchVertices := M.route_internal_disjoint_branchVertices
  route_internal_disjoint := M.route_internal_disjoint

/-- Every graph is a topological minor of any supergraph, using one-edge routes. -/
noncomputable def of_le (hHG : H ≤ G) : H.TopologicalMinor G where
  vertex_subset := hHG.vertexSet_mono
  route e :=
    let h := exists_isLink_of_mem_edgeSet e.prop
    cons h.choose e.val (nil h.choose_spec.choose)
  route_edge_mem e := by simp
  route_isSimple e := by
    let h := exists_isLink_of_mem_edgeSet e.prop
    obtain hxy | hxy := eq_or_ne h.choose h.choose_spec.choose
    · right
      have hlink := h.choose_spec.choose_spec.of_le hHG
      change G.IsCyclicWalk (cons h.choose e.val (nil h.choose_spec.choose))
      rw [← hxy] at hlink ⊢
      exact (nil_isPath hlink.left_mem).cons_isCyclicWalk hlink (by simp)
    · left
      simp [isPath_iff, h.choose_spec.choose_spec.of_le hHG,
        (h.choose_spec.choose_spec.of_le hHG).right_mem, hxy]
  route_ends e := by
    let h := exists_isLink_of_mem_edgeSet e.prop
    rw [h.choose_spec.choose_spec.ends_eq, Sym2.map_mk]
    rfl
  route_internal_disjoint_branchVertices e := by
    let h := exists_isLink_of_mem_edgeSet e.prop
    simp [WList.internalVertexSet]
  route_internal_disjoint e f hef := by
    let he := exists_isLink_of_mem_edgeSet e.prop
    simp [WList.internalVertexSet]

/-- Regard a label-coherent witness as an isomorphism-invariant witness. -/
noncomputable def toIsoTopologicalMinor : H.IsoTopologicalMinor G where
  branchVertex := Function.Embedding.subtype _
  branchVertex_mem x := M.vertex_subset x.prop
  route := M.route
  route_isSimple := M.route_isSimple
  route_nonempty := M.route_nonempty
  route_ends := M.route_ends
  route_internal_disjoint_branchVertices e := by
    simpa using M.route_internal_disjoint_branchVertices e
  route_internal_disjoint := M.route_internal_disjoint
  route_edge_disjoint := fun e f hef ↦ M.route_edge_disjoint hef

end TopologicalMinor

@[simp]
lemma IsTopologicalMinor.refl (H : Graph α β) : H.IsTopologicalMinor H :=
  ⟨TopologicalMinor.of_le le_rfl⟩

lemma IsTopologicalMinor.mono_right {H G K : Graph α β} (hHG : H.IsTopologicalMinor G)
    (hGK : G ≤ K) : H.IsTopologicalMinor K :=
  ⟨hHG.some.mono_right hGK⟩

lemma IsTopologicalMinor.isIsoTopologicalMinor {H G : Graph α β}
    (hHG : H.IsTopologicalMinor G) : H.IsIsoTopologicalMinor G :=
  ⟨hHG.some.toIsoTopologicalMinor⟩

@[simp]
lemma IsIsoTopologicalMinor.refl (G : Graph α β) : G.IsIsoTopologicalMinor G :=
  (IsTopologicalMinor.refl G).isIsoTopologicalMinor

/-! ## Isomorphism-invariant topological minors -/

namespace IsoTopologicalMinor

variable (M : J.IsoTopologicalMinor G)

/-- The branch-vertex embedding with codomain restricted to the active host vertex set. -/
def branchVertexEmbedding : V(J) ↪ V(G) where
  toFun x := ⟨M.branchVertex x, M.branchVertex_mem x⟩
  inj' _ _ hxy := M.branchVertex.injective (congrArg Subtype.val hxy)

lemma branchVertex_injective : Injective M.branchVertex := M.branchVertex.injective

lemma route_isTrail (e : E(J)) : G.IsTrail (M.route e) :=
  (M.route_isSimple e).elim IsPath.isTrail IsCyclicWalk.isTrail

lemma route_ends_eq {e : E(J)} {u v : γ} (huv : J.IsLink e.val u v) :
    s(M.branchVertex ⟨u, huv.left_mem⟩, M.branchVertex ⟨v, huv.right_mem⟩) =
      s((M.route e).first, (M.route e).last) := by
  have hends : J.ends e = s(⟨u, huv.left_mem⟩, ⟨v, huv.right_mem⟩) := huv.ends_eq
  rw [← M.route_ends e, hends, Sym2.map_mk]

lemma ends_mem_range_branchVertex (e : E(J)) :
    (M.route e).first ∈ range M.branchVertex ∧
      (M.route e).last ∈ range M.branchVertex := by
  obtain ⟨u, v, huv⟩ := exists_isLink_of_mem_edgeSet e.prop
  obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := Sym2.eq_iff.mp (M.route_ends_eq huv)
  · exact ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
  exact ⟨⟨_, h2⟩, ⟨_, h1⟩⟩

/-- If two distinct routes meet at a vertex, that vertex is an end of the first route. -/
lemma eq_end_of_mem_of_mem_route {e f : E(J)} {x : α} (hef : e ≠ f)
    (hxe : x ∈ M.route e) (hxf : x ∈ M.route f) :
    x = (M.route e).first ∨ x = (M.route e).last := by
  by_contra hx
  simp only [not_or] at hx
  have hxi := mem_internalVertexSet_of_mem_ne_ends hxe hx
  obtain h1 | h1 | h1 := mem_iff_eq_first_or_mem_internalVertexSet_or_eq_last.mp hxf
  · exact (M.route_internal_disjoint_branchVertices e).notMem_of_mem_left hxi
      (h1 ▸ (M.ends_mem_range_branchVertex f).1)
  · exact (M.route_internal_disjoint e f hef).notMem_of_mem_left hxi h1
  exact (M.route_internal_disjoint_branchVertices e).notMem_of_mem_left hxi
    (h1 ▸ (M.ends_mem_range_branchVertex f).2)

/-- Enlarge the host of an isomorphism-invariant topological-minor witness. -/
noncomputable def mono_right {K : Graph α β} (hGK : G ≤ K) : J.IsoTopologicalMinor K where
  branchVertex := M.branchVertex
  branchVertex_mem x := hGK.vertexSet_mono (M.branchVertex_mem x)
  route := M.route
  route_isSimple e := (M.route_isSimple e).imp (·.of_le hGK) (·.of_le hGK)
  route_nonempty := M.route_nonempty
  route_ends := M.route_ends
  route_internal_disjoint_branchVertices := M.route_internal_disjoint_branchVertices
  route_internal_disjoint := M.route_internal_disjoint
  route_edge_disjoint := M.route_edge_disjoint

/-! ### Path-route constructors -/

/-- A path with the prescribed distinct branch-vertex ends is nonempty. -/
lemma pathRoute_nonempty_of_loopless {J : Graph γ δ} {G : Graph α β} [J.Loopless]
    (branch : V(J) ↪ α) (route : E(J) → WList α β)
    (route_isPath : ∀ e, G.IsPath (route e))
    (route_ends : ∀ e,
      Sym2.map branch (J.ends e) = s((route e).first, (route e).last))
    (e : E(J)) : (route e).Nonempty := by
  obtain ⟨u, v, huv⟩ := exists_isLink_of_mem_edgeSet e.prop
  have hend :
      s(branch ⟨u, huv.left_mem⟩, branch ⟨v, huv.right_mem⟩) =
        s((route e).first, (route e).last) := by
    rw [← route_ends e, huv.ends_eq, Sym2.map_mk]
  refine (first_ne_last_iff (route_isPath e).nodup).mp fun h ↦ huv.ne ?_
  apply Subtype.mk_eq_mk.mp
  apply branch.injective
  obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := Sym2.eq_iff.mp hend
  · exact h1.trans (h.trans h2.symm)
  exact h1.trans (h.symm.trans h2.symm)

/-- Construct a topological-minor witness for a loopless multigraph from path routes.

Parallel edges are allowed, so edge-disjointness of distinct routes is supplied explicitly.
-/
noncomputable def ofPathRoutes {J : Graph γ δ} {G : Graph α β} [J.Loopless]
    (branch : V(J) → α) (branch_mem : ∀ x, branch x ∈ V(G)) (branch_injective : Injective branch)
    (route : E(J) → WList α β) (route_isPath : ∀ e, G.IsPath (route e))
    (route_ends : ∀ e, Sym2.map branch (J.ends e) = s((route e).first, (route e).last))
    (route_internal_disjoint_branch : ∀ e, Disjoint (route e).internalVertexSet (range branch))
    (route_internal_disjoint : ∀ e f, e ≠ f →
      Disjoint (route e).internalVertexSet (route f).internalVertexSet)
    (route_edge_disjoint : ∀ e f, e ≠ f → Disjoint E(route e) E(route f)) :
    J.IsoTopologicalMinor G where
  branchVertex := ⟨branch, branch_injective⟩
  branchVertex_mem := branch_mem
  route := route
  route_isSimple e := Or.inl (route_isPath e)
  route_nonempty :=
    pathRoute_nonempty_of_loopless ⟨branch, branch_injective⟩ route route_isPath route_ends
  route_ends := route_ends
  route_internal_disjoint_branchVertices := route_internal_disjoint_branch
  route_internal_disjoint := route_internal_disjoint
  route_edge_disjoint := route_edge_disjoint

/-- In a simple pattern, the path-route hypotheses force distinct routes to be edge-disjoint. -/
lemma pathRoutes_edge_disjoint_of_simple {J : Graph γ δ} {G : Graph α β} [J.Simple]
    (branch : V(J) → α) (branch_injective : Injective branch)
    (route : E(J) → WList α β) (route_isPath : ∀ e, G.IsPath (route e))
    (route_ends : ∀ e, Sym2.map branch (J.ends e) = s((route e).first, (route e).last))
    (route_internal_disjoint_branch : ∀ e, Disjoint (route e).internalVertexSet (range branch))
    (route_internal_disjoint : ∀ e f, e ≠ f →
      Disjoint (route e).internalVertexSet (route f).internalVertexSet) :
    ∀ e f, e ≠ f → Disjoint E(route e) E(route f) := by
  let branchEmbedding : V(J) ↪ α := ⟨branch, branch_injective⟩
  have hends : ∀ e : E(J), ∃ u v : V(J), u ≠ v ∧
      s(branch u, branch v) = s((route e).first, (route e).last) := by
    rintro e
    obtain ⟨u, v, huv⟩ := exists_isLink_of_mem_edgeSet e.prop
    have h : J.ends e = s(⟨u, huv.left_mem⟩, ⟨v, huv.right_mem⟩) := huv.ends_eq
    refine ⟨⟨u, huv.left_mem⟩, ⟨v, huv.right_mem⟩,
      fun hne ↦ huv.ne (congrArg Subtype.val hne), ?_⟩
    rw [← route_ends e, h, Sym2.map_mk]
  have hmem_range : ∀ (e : E(J)) {x : α},
      x = (route e).first ∨ x = (route e).last → x ∈ range branch := by
    rintro e x hx
    obtain ⟨u, v, -, hend⟩ := hends e
    obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := Sym2.eq_iff.mp hend <;> obtain rfl | rfl := hx
    · exact ⟨u, h1⟩
    · exact ⟨v, h2⟩
    · exact ⟨v, h2⟩
    exact ⟨u, h1⟩
  have route_nonempty : ∀ e, (route e).Nonempty := by
    intro e
    exact pathRoute_nonempty_of_loopless branchEmbedding route route_isPath route_ends e
  have hinter : ∀ (e f : E(J)), e ≠ f → ∀ x ∈ route e, x ∈ route f →
      x = (route e).first ∨ x = (route e).last := by
    rintro e f hef x hxe hxf
    by_contra hx
    simp only [not_or] at hx
    have hxi := mem_internalVertexSet_of_mem_ne_ends hxe hx
    obtain h1 | h1 | h1 := mem_iff_eq_first_or_mem_internalVertexSet_or_eq_last.mp hxf
    · exact (route_internal_disjoint_branch e).notMem_of_mem_left hxi
        (hmem_range f (Or.inl h1))
    · exact (route_internal_disjoint e f hef).notMem_of_mem_left hxi h1
    exact (route_internal_disjoint_branch e).notMem_of_mem_left hxi
      (hmem_range f (Or.inr h1))
  have key : ∀ (g : β) (p q : E(J)), p ≠ q → g ∈ E(route p) → g ∈ E(route q) →
      G.IsLink g (route p).first (route p).last := by
    rintro g p q hpq hgp hgq
    obtain ⟨a, b, hab⟩ := exists_dInc_of_mem_edge hgp
    obtain ⟨c, d, hcd⟩ := exists_dInc_of_mem_edge hgq
    have hmem : a ∈ route q ∧ b ∈ route q := by
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := ((route_isPath p).isWalk.isLink_of_dInc hab)
        |>.eq_and_eq_or_eq_and_eq ((route_isPath q).isWalk.isLink_of_dInc hcd)
      · exact ⟨hcd.left_mem, hcd.right_mem⟩
      exact ⟨hcd.right_mem, hcd.left_mem⟩
    have hlen := Nat.succ_le_of_lt (route_nonempty p).length_pos |>.eq_of_not_lt'
      <| one_lt_length_iff.not.mpr <| (route_isPath p).not_nontrivial_of_dInc rfl rfl hab
        (hinter p q hpq a hab.left_mem hmem.1) (hinter p q hpq b hab.right_mem hmem.2)
    obtain ⟨u, g', v, heq⟩ := (route p).length_eq_one_iff.mp hlen
    obtain rfl : g = g' := by simpa [heq] using hgp
    have hw := (route_isPath p).isWalk
    rw [heq] at hw ⊢
    exact (cons_isWalk_iff.mp hw).1
  rintro e f hef
  refine disjoint_left.mpr fun g hge hgf ↦ hef (ends_injective J
    (Sym2.map.injective branch_injective ?_))
  rw [route_ends e, route_ends f]
  obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := (key g e f hef hge hgf).eq_and_eq_or_eq_and_eq
    (key g f e hef.symm hgf hge)
  · rw [h1, h2]
  rw [h1, h2, Sym2.eq_swap]

/-- Convenient path-route constructor for a simple pattern.

Simplicity is used only to derive edge-disjointness of distinct routes. -/
noncomputable def ofPathRoutes_of_simple {J : Graph γ δ} {G : Graph α β} [J.Simple]
    (branch : V(J) → α) (branch_mem : ∀ x, branch x ∈ V(G)) (branch_injective : Injective branch)
    (route : E(J) → WList α β) (route_isPath : ∀ e, G.IsPath (route e))
    (route_ends : ∀ e, Sym2.map branch (J.ends e) = s((route e).first, (route e).last))
    (route_internal_disjoint_branch : ∀ e, Disjoint (route e).internalVertexSet (range branch))
    (route_internal_disjoint : ∀ e f, e ≠ f →
      Disjoint (route e).internalVertexSet (route f).internalVertexSet) :
    J.IsoTopologicalMinor G :=
  ofPathRoutes branch branch_mem branch_injective route route_isPath route_ends
    route_internal_disjoint_branch route_internal_disjoint
    (pathRoutes_edge_disjoint_of_simple branch branch_injective route route_isPath route_ends
      route_internal_disjoint_branch route_internal_disjoint)

/-! ### Transport along pattern isomorphisms -/

/-- Transport a topological-minor witness along an isomorphism of the pattern graph. -/
noncomputable def ofIso {γ' δ' : Type*} {J : Graph γ δ} {K : Graph γ' δ'} {G : Graph α β}
    (F : Iso J K) (M : K.IsoTopologicalMinor G) : J.IsoTopologicalMinor G where
  branchVertex := F.vertMapEmbedding.trans M.branchVertex
  branchVertex_mem x := M.branchVertex_mem (F.vertMapEmbedding x)
  route e := M.route (F.edgeMapEmbedding e)
  route_isSimple e := M.route_isSimple _
  route_nonempty e := M.route_nonempty _
  route_ends e := by
    obtain ⟨u, v, huv⟩ := exists_isLink_of_mem_edgeSet e.prop
    let uJ : V(J) := ⟨u, huv.left_mem⟩
    let vJ : V(J) := ⟨v, huv.right_mem⟩
    have hK : K.IsLink (F.edgeMapEmbedding e) (F.vertMapEmbedding uJ) (F.vertMapEmbedding vJ) :=
      F.map_isLink huv
        (by simpa [F.edgeEquiv_apply] using F.mem_edgeMap_edgeEquiv e)
        (by simpa [F.vertexEquiv_apply] using F.mem_vertMap_vertexEquiv uJ)
        (by simpa [F.vertexEquiv_apply] using F.mem_vertMap_vertexEquiv vJ)
    rw [huv.ends_eq, Sym2.map_mk, ← M.route_ends (F.edgeMapEmbedding e), hK.ends_eq,
      Sym2.map_mk]
    rfl
  route_internal_disjoint_branchVertices e := by
    refine (M.route_internal_disjoint_branchVertices (F.edgeMapEmbedding e)).mono_right ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨F.vertMapEmbedding x, rfl⟩
  route_internal_disjoint e f hef :=
    M.route_internal_disjoint _ _ fun h ↦ hef (F.edgeMapEmbedding.injective h)
  route_edge_disjoint e f hef :=
    M.route_edge_disjoint _ _ fun h ↦ hef (F.edgeMapEmbedding.injective h)

/-! ### Normalization by relabelling -/

/-- A representative host edge chosen from each route. -/
noncomputable def repEdge (e : E(J)) : β :=
  (M.route_nonempty e).exists_edge.choose

lemma repEdge_mem (e : E(J)) : M.repEdge e ∈ E(M.route e) :=
  (M.route_nonempty e).exists_edge.choose_spec

lemma repEdge_injective : Injective M.repEdge :=
  fun e f hef ↦ by_contra fun hne ↦ (M.route_edge_disjoint e f hne).notMem_of_mem_left
    (M.repEdge_mem e) (hef ▸ M.repEdge_mem f)

/-- The embedding of pattern edges into representative host-edge labels. -/
noncomputable def repEdgeEmbedding : E(J) ↪ β :=
  ⟨M.repEdge, M.repEdge_injective⟩

/-- Same-carrier copy of the pattern using the model's branch vertices and representative edges. -/
noncomputable def normalized : Graph α β :=
  J.relabel M.branchVertex M.repEdgeEmbedding

@[simp]
lemma vertexSet_normalized : V(M.normalized) = range M.branchVertex := by
  simp [normalized]

@[simp]
lemma edgeSet_normalized : E(M.normalized) = range M.repEdge := by
  simp [normalized, repEdgeEmbedding]

/-- The canonical isomorphism from the abstract pattern to its normalized same-carrier copy. -/
noncomputable def isoNormalized : Iso J M.normalized :=
  J.relabelIso M.branchVertex M.repEdgeEmbedding

/-- The source pattern edge corresponding to an edge of the normalized copy. -/
noncomputable def source (e : E(M.normalized)) : E(J) :=
  (Equiv.ofInjective M.repEdge M.repEdge_injective).symm ⟨e.val, by
    simpa [edgeSet_normalized] using e.prop⟩

lemma repEdge_source (e : E(M.normalized)) : M.repEdge (M.source e) = e.val :=
  congrArg Subtype.val <|
    (Equiv.ofInjective M.repEdge M.repEdge_injective).apply_symm_apply ⟨e.val, by
      simpa [edgeSet_normalized] using e.prop⟩

lemma source_repEdge (e : E(J)) :
    M.source ⟨M.repEdge e, by simp [edgeSet_normalized]⟩ = e :=
  M.repEdge_injective <| (M.repEdge_source _).trans rfl

/-- The normalized copy is a label-coherent topological minor of the host. -/
noncomputable def toTopologicalMinor : M.normalized.TopologicalMinor G where
  vertex_subset x hx := by
    rw [vertexSet_normalized] at hx
    obtain ⟨v, rfl⟩ := hx
    exact M.branchVertex_mem v
  route e := M.route (M.source e)
  route_edge_mem e := by
    simpa [← M.repEdge_source e] using M.repEdge_mem (M.source e)
  route_isSimple e := M.route_isSimple (M.source e)
  route_ends e := by
    obtain ⟨u, v, huv⟩ := exists_isLink_of_mem_edgeSet (M.source e).prop
    let uJ : V(J) := ⟨u, huv.left_mem⟩
    let vJ : V(J) := ⟨v, huv.right_mem⟩
    have hnorm : M.normalized.IsLink e.val (M.branchVertex uJ) (M.branchVertex vJ) := by
      have h := (J.relabel_isLink M.branchVertex M.repEdgeEmbedding (M.source e) uJ vJ).2 huv
      simpa [normalized, repEdgeEmbedding, M.repEdge_source e] using h
    rw [hnorm.ends_eq, Sym2.map_mk]
    simpa [uJ, vJ] using M.route_ends_eq huv
  route_internal_disjoint_branchVertices e := by
    rw [vertexSet_normalized]
    exact M.route_internal_disjoint_branchVertices (M.source e)
  route_internal_disjoint e f hef := by
    have hsource : M.source e ≠ M.source f := fun h ↦ hef <| Subtype.ext <|
      (M.repEdge_source e).symm.trans ((congrArg M.repEdge h).trans (M.repEdge_source f))
    exact M.route_internal_disjoint _ _ hsource

/-- Normalize an abstract topological-minor model to a same-carrier copy of the pattern. -/
theorem exists_iso_topologicalMinor (M : J.IsoTopologicalMinor G) :
    ∃ K : Graph α β, Nonempty (Iso J K) ∧ Nonempty (K.TopologicalMinor G) :=
  ⟨M.normalized, ⟨M.isoNormalized⟩, ⟨M.toTopologicalMinor⟩⟩

end IsoTopologicalMinor

lemma IsIsoTopologicalMinor.mono_right {J : Graph γ δ} {G K : Graph α β}
    (hJG : J.IsIsoTopologicalMinor G) (hGK : G ≤ K) : J.IsIsoTopologicalMinor K :=
  ⟨hJG.some.mono_right hGK⟩

lemma IsIsoTopologicalMinor.ofIso {γ' δ' : Type*} {J : Graph γ δ} {K : Graph γ' δ'}
    {G : Graph α β} (F : Iso J K) (hKG : K.IsIsoTopologicalMinor G) :
    J.IsIsoTopologicalMinor G :=
  ⟨IsoTopologicalMinor.ofIso F hKG.some⟩

/-- The heterogeneous definition is equivalent to an isomorphic same-carrier copy equipped with a
label-coherent topological-minor witness. -/
theorem isIsoTopologicalMinor_iff_exists_iso_topologicalMinor {J : Graph γ δ}
    {G : Graph α β} :
    J.IsIsoTopologicalMinor G ↔
      ∃ K : Graph α β, Nonempty (Iso J K) ∧ Nonempty (K.TopologicalMinor G) :=
  ⟨fun ⟨M⟩ ↦ M.exists_iso_topologicalMinor,
    fun ⟨_, ⟨F⟩, ⟨M⟩⟩ ↦ ⟨IsoTopologicalMinor.ofIso F M.toIsoTopologicalMinor⟩⟩

/-! ## Host-first construction: subgraph replacement -/

/-- An indexed family of subgraphs of `G`, each intended to collapse to one edge between two
specified vertices.

The components provide a convenient sufficient condition for route separation.  This interface is
particularly useful for loops and parallel edges, where a simple-graph path constructor is not
adequate.
-/
structure SubgraphReplacement (G : Graph α β) (ι : Type*) where
  component : ι → Graph α β
  left : ι → α
  right : ι → α
  edge : ι → β
  component_le : ∀ i, component i ≤ G
  realization : ∀ i, ∃ W,
    ((component i).IsPath W ∨ (component i).IsCyclicWalk W) ∧
      edge i ∈ E(W) ∧ W.first = left i ∧ W.last = right i
  interior_disjoint : ∀ ⦃i j⦄, i ≠ j →
    Disjoint (V(component i) \ {left i, right i}) V(component j)
  edge_injective : Injective edge

namespace SubgraphReplacement

variable (R : G.SubgraphReplacement ι)

/-- A selected simple route realizing component `i`. -/
noncomputable def route (i : ι) : WList α β := (R.realization i).choose

lemma route_isSimple (i : ι) :
    (R.component i).IsPath (R.route i) ∨ (R.component i).IsCyclicWalk (R.route i) :=
  (R.realization i).choose_spec.1

lemma route_isTrail (i : ι) : (R.component i).IsTrail (R.route i) :=
  (R.route_isSimple i).elim (·.isTrail) (·.isTrail)

lemma edge_mem_route (i : ι) : R.edge i ∈ E(R.route i) :=
  (R.realization i).choose_spec.2.1

@[simp]
lemma route_first (i : ι) : (R.route i).first = R.left i :=
  (R.realization i).choose_spec.2.2.1

@[simp]
lemma route_last (i : ι) : (R.route i).last = R.right i :=
  (R.realization i).choose_spec.2.2.2

@[simp]
lemma route_nonempty (i : ι) : (R.route i).Nonempty :=
  nonempty_iff_exists_edge.mpr ⟨R.edge i, R.edge_mem_route i⟩

/-- The graph obtained by replacing each component by its distinguished edge. -/
@[simps]
def replacementGraph : Graph α β where
  vertexSet := ⋃ i, {R.left i, R.right i}
  edgeSet := range R.edge
  IsLink e x y := ∃ i, e = R.edge i ∧
    ((x = R.left i ∧ y = R.right i) ∨ (x = R.right i ∧ y = R.left i))
  isLink_symm e _ := ⟨by
    rintro x y ⟨i, rfl, hxy | hxy⟩
    · exact ⟨i, rfl, Or.inr ⟨hxy.2, hxy.1⟩⟩
    · exact ⟨i, rfl, Or.inl ⟨hxy.2, hxy.1⟩⟩⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro e x y v w ⟨i, rfl, hxy⟩ ⟨j, hj, hvw⟩
    obtain rfl := R.edge_injective hj
    grind
  left_mem_of_isLink := by
    rintro e x y ⟨i, rfl, hxy | hxy⟩ <;> exact mem_iUnion.2 ⟨i, by simp [hxy]⟩
  edge_mem_iff_exists_isLink e :=
    ⟨fun ⟨i, hi⟩ ↦ hi ▸ ⟨R.left i, R.right i, ⟨i, rfl, Or.inl ⟨rfl, rfl⟩⟩⟩,
      fun ⟨x, y, i, hei, _⟩ ↦ ⟨i, hei.symm⟩⟩

lemma replacementGraph_isLink_left_right (i : ι) :
    R.replacementGraph.IsLink (R.edge i) (R.left i) (R.right i) :=
  ⟨i, rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- The source component of an edge in the replacement graph. -/
noncomputable def source (e : E(R.replacementGraph)) : ι :=
  (congrArg (e.val ∈ ·) R.edgeSet_replacementGraph) ▸ e.prop |>.choose

lemma edge_source (e : E(R.replacementGraph)) : R.edge (R.source e) = e.val :=
  (congrArg (e.val ∈ ·) R.edgeSet_replacementGraph) ▸ e.prop |>.choose_spec

lemma source_eq_of_edge_eq {i : ι} {e : E(R.replacementGraph)} (hi : R.edge i = e.val) :
    R.source e = i :=
  R.edge_injective ((R.edge_source e).trans hi.symm)

/-- Internal vertices of the selected route in component `i`. -/
def internal (i : ι) : Set α := (R.route i).internalVertexSet

lemma internal_subset_component (i : ι) : R.internal i ⊆ V(R.component i) := by
  rintro x hx
  exact R.route_isTrail i |>.vertexSet_subset <|
    List.mem_of_mem_tail (List.mem_of_mem_dropLast hx)

lemma route_tail_getLast (i : ι) (htail_ne : (R.route i).vertex.tail ≠ []) :
    (R.route i).vertex.tail.getLast htail_ne = (R.route i).last := by
  rw [List.getLast_tail, vertex_getLast]

lemma vertex_tail_nodup {i : ι} : (R.route i).vertex.tail.Nodup := by
  obtain hP | hC := R.route_isSimple i
  · exact hP.nodup.tail
  simpa [(R.route_nonempty i).vertex_tail] using hC.nodup

lemma internal_disjoint_ends (i : ι) : Disjoint (R.internal i) {R.left i, R.right i} := by
  refine disjoint_left.mpr fun x hxI hxEnds ↦ ?_
  change x ∈ (R.route i).vertex.tail.dropLast at hxI
  rw [← R.route_first i, ← R.route_last i] at hxEnds
  have hx_tail : x ∈ (R.route i).vertex.tail := List.mem_of_mem_dropLast hxI
  have htail_ne : (R.route i).vertex.tail ≠ [] := List.ne_nil_of_mem hx_tail
  have hnd_tail := R.vertex_tail_nodup (i := i)
  obtain hP | hC := R.route_isSimple i
  · have hx_mem_tail : x ∈ (R.route i).tail := by
      change x ∈ (R.route i).tail.vertex
      rwa [(R.route_nonempty i).vertex_tail]
    have hne_first : x ≠ (R.route i).first :=
      fun h ↦ first_notMem_tail_of_nodup hP.nodup (R.route_nonempty i) (h ▸ hx_mem_tail)
    obtain rfl | rfl := hxEnds
    · exact hne_first rfl
    exact hnd_tail.getLast_not_mem_dropLast htail_ne <| (R.route_tail_getLast i htail_ne).symm ▸ hxI
  obtain rfl | rfl := hxEnds
  · exact hnd_tail.getLast_not_mem_dropLast htail_ne <|
      (R.route_tail_getLast i htail_ne).trans hC.isClosed.symm ▸ hxI
  exact hnd_tail.getLast_not_mem_dropLast htail_ne <| (R.route_tail_getLast i htail_ne).symm ▸ hxI

lemma internal_disjoint_component_of_ne {i j : ι} (hij : i ≠ j) :
    Disjoint (R.internal i) V(R.component j) :=
  (R.interior_disjoint hij).mono_left
    <| subset_sdiff.mpr ⟨R.internal_subset_component i, R.internal_disjoint_ends i⟩

lemma ends_mem_component (i : ι) : R.left i ∈ V(R.component i) ∧ R.right i ∈ V(R.component i) :=
  ⟨R.route_first i ▸ (R.route_isTrail i |>.vertexSet_subset first_mem),
    R.route_last i ▸ (R.route_isTrail i |>.vertexSet_subset last_mem)⟩

lemma internal_disjoint_replacement_vertices (i : ι) :
    Disjoint (R.internal i) V(R.replacementGraph) := by
  simp only [vertexSet_replacementGraph, disjoint_iUnion_right]
  rintro j
  obtain rfl | hij := eq_or_ne i j
  · exact R.internal_disjoint_ends i
  refine (R.internal_disjoint_component_of_ne hij).mono_right ?_
  grind [R.ends_mem_component j]

lemma internal_disjoint_of_ne {i j : ι} (hij : i ≠ j) : Disjoint (R.internal i) (R.internal j) :=
  (R.internal_disjoint_component_of_ne hij).mono_right (R.internal_subset_component j)

/-- The replacement graph is a label-coherent topological minor of the ambient graph. -/
noncomputable def topologicalMinor : R.replacementGraph.TopologicalMinor G where
  vertex_subset x hx := by
    simp only [vertexSet_replacementGraph, mem_iUnion, mem_insert_iff, mem_singleton_iff] at hx
    obtain ⟨i, rfl | rfl⟩ := hx
    · exact (R.component_le i).vertexSet_mono (R.ends_mem_component i).1
    exact (R.component_le i).vertexSet_mono (R.ends_mem_component i).2
  route e := R.route (R.source e)
  route_edge_mem e := by
    simpa [← R.edge_source e] using R.edge_mem_route (R.source e)
  route_isSimple e :=
    (R.route_isSimple (R.source e)).imp (·.of_le (R.component_le _)) (·.of_le (R.component_le _))
  route_ends e := by
    have hlink : R.replacementGraph.IsLink e.val
        (R.left (R.source e)) (R.right (R.source e)) := by
      rw [← R.edge_source e]
      exact R.replacementGraph_isLink_left_right (R.source e)
    rw [hlink.ends_eq, Sym2.map_mk, R.route_first, R.route_last]
  route_internal_disjoint_branchVertices e := R.internal_disjoint_replacement_vertices (R.source e)
  route_internal_disjoint e f hef := by
    have hsf : R.source e ≠ R.source f := fun h ↦ hef <| Subtype.ext <|
      (R.edge_source e).symm.trans ((congrArg R.edge h).trans (R.edge_source f))
    exact R.internal_disjoint_of_ne hsf

/-- The replacement graph is a topological minor of the ambient graph. -/
theorem isTopologicalMinor : R.replacementGraph.IsTopologicalMinor G :=
  ⟨R.topologicalMinor⟩

end SubgraphReplacement

/-! ## Used subgraphs -/

namespace TopologicalMinor

variable (M : H.TopologicalMinor G)

/-- Vertices used by a label-coherent topological-minor witness, including isolated pattern
vertices. -/
def usedVertexSet : Set α :=
  V(H) ∪ ⋃ e : E(H), V(M.route e)

/-- Edges used by a label-coherent topological-minor witness. -/
def usedEdgeSet : Set β :=
  ⋃ e : E(H), E(M.route e)

/-- The subgraph of the host occupied by the witness. -/
def usedSubgraph : Graph α β :=
  G[M.usedVertexSet] ↾ M.usedEdgeSet

lemma usedVertexSet_subset : M.usedVertexSet ⊆ V(G) :=
  union_subset M.vertex_subset <| iUnion_subset fun e ↦ (M.route_isTrail e).vertexSet_subset

lemma usedSubgraph_le : M.usedSubgraph ≤ G :=
  restrict_le.trans (induce_le M.usedVertexSet_subset)

lemma route_vertexSet_subset_usedVertexSet (e : E(H)) : V(M.route e) ⊆ M.usedVertexSet :=
  fun _ hx ↦ mem_union_right _ (mem_iUnion.mpr ⟨e, hx⟩)

lemma route_edgeSet_subset_usedEdgeSet (e : E(H)) : E(M.route e) ⊆ M.usedEdgeSet :=
  fun _ hx ↦ mem_iUnion.mpr ⟨e, hx⟩

lemma route_isSimple_usedSubgraph (e : E(H)) :
    M.usedSubgraph.IsPath (M.route e) ∨ M.usedSubgraph.IsCyclicWalk (M.route e) := by
  refine (M.route_isSimple e).imp ?_ ?_
  · exact fun hP ↦ isPath_restrict_iff.mpr
      ⟨(isPath_induce_iff M.usedVertexSet_subset).mpr
        ⟨hP, M.route_vertexSet_subset_usedVertexSet e⟩,
        M.route_edgeSet_subset_usedEdgeSet e⟩
  exact fun hC ↦ (restrict_isCyclicWalk_iff _ _).mpr ⟨(induce_isCyclicWalk_iff _ _).mpr
    ⟨hC, M.route_vertexSet_subset_usedVertexSet e⟩, M.route_edgeSet_subset_usedEdgeSet e⟩

lemma vertexSet_subset_usedSubgraph : V(H) ⊆ V(M.usedSubgraph) := by
  simp +contextual [usedSubgraph, usedVertexSet]

lemma edgeSet_subset_usedSubgraph : E(H) ⊆ E(M.usedSubgraph) := by
  intro e he
  let eH : E(H) := ⟨e, he⟩
  have htrail : M.usedSubgraph.IsTrail (M.route eH) :=
    (M.route_isSimple_usedSubgraph eH).elim (·.isTrail) (·.isTrail)
  exact htrail.edgeSet_subset (M.route_edge_mem eH)

end TopologicalMinor

namespace IsoTopologicalMinor

variable (M : J.IsoTopologicalMinor G)

/-- Vertices used by a heterogeneous witness, including isolated branch vertices. -/
def usedVertexSet : Set α := range M.branchVertex ∪ ⋃ e : E(J), V(M.route e)

/-- Edges used by a heterogeneous witness. -/
def usedEdgeSet : Set β := ⋃ e : E(J), E(M.route e)

/-- The subgraph of the host occupied by the heterogeneous witness. -/
def usedSubgraph : Graph α β := G[M.usedVertexSet] ↾ M.usedEdgeSet

lemma usedVertexSet_subset : M.usedVertexSet ⊆ V(G) :=
  union_subset (range_subset_iff.mpr M.branchVertex_mem) <|
    iUnion_subset fun e ↦ (M.route_isTrail e).vertexSet_subset

lemma usedSubgraph_le : M.usedSubgraph ≤ G := restrict_le.trans (induce_le M.usedVertexSet_subset)

lemma route_vertexSet_subset_usedVertexSet (e : E(J)) : V(M.route e) ⊆ M.usedVertexSet :=
  fun _ hx ↦ mem_union_right _ (mem_iUnion.mpr ⟨e, hx⟩)

lemma route_edgeSet_subset_usedEdgeSet (e : E(J)) : E(M.route e) ⊆ M.usedEdgeSet :=
  fun _ hx ↦ mem_iUnion.mpr ⟨e, hx⟩

lemma route_isSimple_usedSubgraph (e : E(J)) :
    M.usedSubgraph.IsPath (M.route e) ∨ M.usedSubgraph.IsCyclicWalk (M.route e) := by
  refine (M.route_isSimple e).imp ?_ ?_
  · exact fun hP ↦ isPath_restrict_iff.mpr ⟨(isPath_induce_iff M.usedVertexSet_subset).mpr
      ⟨hP, M.route_vertexSet_subset_usedVertexSet e⟩, M.route_edgeSet_subset_usedEdgeSet e⟩
  exact fun hC ↦ (restrict_isCyclicWalk_iff ..).mpr ⟨(induce_isCyclicWalk_iff ..).mpr
    ⟨hC, M.route_vertexSet_subset_usedVertexSet e⟩, M.route_edgeSet_subset_usedEdgeSet e⟩

end IsoTopologicalMinor

end Graph
