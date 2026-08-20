module

public import Matroid.Graph.Planarity.TopologicalMinor

@[expose] public section

/-!
# Inserting an edge or a subdivided edge into a drawing

These constructions work in an arbitrary topological space. `addEdge` is the primitive cell
attachment. `addPath` first adds a fresh edge and then transports that drawing across the
subdivision which replaces the fresh edge by the prescribed path.

## Main definitions

- `Graph.Drawing.IsFreeArc`: an arc injective on `Ioo 0 1` whose relative interior misses the
  support. This is what both geometric inputs of §13.1 deliver, and the only thing either
  combinator asks of the plane.
- `Graph.Drawing.addEdge`: extend a drawing by one edge drawn along a free arc between two of its
  vertices. `u = v` is allowed and is the loop case.
- `Graph.addFreshEdge`: add an edge with label `Sum.inr ()`, after relabelling old edges by
  `Sum.inl`.
- `Graph.Drawing.addPathSubdivision`, `Graph.Drawing.addPath`: replace that fresh edge by a path.

## Main statements

- `Graph.Drawing.support_addEdge`, `Graph.Drawing.support_addPath`: exact image formulas.
- `Graph.Drawing.addPath_extends`: the subdivided-edge insertion leaves the original drawing
  unchanged.

Plane-specific existence and polygonality results are in `Insertion.Plane`. Generic drawing union
is independent and lives in `Drawing.Union`.
-/

open Function Set Topology
open scoped unitInterval

universe u

variable {X : Type u} [TopologicalSpace X]

/-! ### Reorienting an arc

`Graph.source` and `Graph.target` pick the orientation of an edge from `ArbRel`, one linear order
per *type*, so a caller who supplies an arc from `D.vertex u` to `D.vertex v` cannot know which of
its ends the new edge calls its source. `Path.reorient` absorbs the swap, and the two lemmas after
it say the swap is invisible to `range` and to `Path.Interior` — which are the only two things
`ofVertexAndEdgePaths` looks at.

These declarations only reorient paths and identify the resulting range and interior. -/

namespace unitInterval

lemma closure_Ioo_zero_one : closure (Ioo (0 : I) 1) = univ := by
  rw [closure_Ioo (zero_ne_one (α := I))]
  simp [Set.eq_univ_iff_forall, unitInterval.le_one']

lemma symm_mem_Ioo {t : I} (ht : t ∈ Ioo (0 : I) 1) : σ t ∈ Ioo (0 : I) 1 :=
  ⟨unitInterval.pos_iff_ne_zero.mpr <| by
      simp [unitInterval.symm_eq_zero, unitInterval.lt_one_iff_ne_one.mp ht.2],
    unitInterval.lt_one_iff_ne_one.mpr <| by
      simp [unitInterval.symm_eq_one, unitInterval.pos_iff_ne_zero.mp ht.1]⟩

end unitInterval

namespace Path

open Classical in
/-- Reorient `γ` so that its ends are the prescribed pair, given that the two pairs agree as
unordered pairs. -/
noncomputable def reorient {a b x y : X} (γ : Path a b) (h : s(x, y) = s(a, b)) : Path x y :=
  if hx : x = a ∧ y = b then γ.cast hx.1 hx.2
  else
    have h' : x = b ∧ y = a := (Sym2.eq_iff.mp h).resolve_left hx
    γ.symm.cast h'.1 h'.2

@[simp]
lemma range_reorient {a b x y : X} (γ : Path a b) (h : s(x, y) = s(a, b)) :
    range (γ.reorient h) = range γ := by
  rw [reorient]
  split_ifs <;> simp

@[simp]
lemma reorient_interior {a b x y : X} (γ : Path a b) (h : s(x, y) = s(a, b)) :
    (γ.reorient h).Interior = γ.Interior := by
  rw [reorient]
  split_ifs
  · rfl
  refine subset_antisymm ?_ ?_ <;> rintro _ ⟨t, ht, rfl⟩
  · exact ⟨σ t, unitInterval.symm_mem_Ioo ht, rfl⟩
  · exact ⟨σ t, unitInterval.symm_mem_Ioo ht, by simp⟩

lemma injOn_reorient {a b x y : X} (γ : Path a b) (h : s(x, y) = s(a, b))
    (hγ : InjOn γ (Ioo (0 : I) 1)) : InjOn (γ.reorient h) (Ioo (0 : I) 1) := by
  rw [reorient]
  split_ifs
  · exact hγ
  intro s hs t ht hst
  have := hγ (unitInterval.symm_mem_Ioo hs) (unitInterval.symm_mem_Ioo ht) hst
  simpa using congrArg σ this

end Path

namespace Graph

public noncomputable section

variable {α β : Type*} {G : Graph α β} {u v : α} {f : β}

namespace Drawing

/-! ### Free arcs -/

/-- An arc of `X` that a drawing can absorb as a new edge: injectively parametrized on the open
interval, with relative interior missing the support of `D` altogether.

The geometric constructions below produce this condition from a face or from a sector at a vertex.
-/
structure IsFreeArc (D : Drawing G X) {x y : X} (γ : Path x y) : Prop where
  injOn : InjOn γ (Ioo (0 : I) 1)
  disjoint_support : Disjoint γ.Interior D.support

variable {D : Drawing G X} {x y : X} {γ : Path x y}

lemma IsFreeArc.disjoint_range_vertex (hγ : D.IsFreeArc γ) :
    Disjoint γ.Interior (range D.vertex) :=
  hγ.disjoint_support.mono_right fun _ ⟨w, hw⟩ ↦ hw ▸ D.vertex_mem_support w

lemma IsFreeArc.disjoint_range_edgePath (hγ : D.IsFreeArc γ) (e : E(G)) :
    Disjoint γ.Interior (range (D.edgePath e)) :=
  hγ.disjoint_support.mono_right (D.edgePath_range_subset_support e)

lemma IsFreeArc.reorient {x' y' : X} (hγ : D.IsFreeArc γ) (h : s(x', y') = s(x, y)) :
    D.IsFreeArc (γ.reorient h) where
  injOn := γ.injOn_reorient h hγ.injOn
  disjoint_support := by rw [Path.reorient_interior]; exact hγ.disjoint_support

/-! ### Adding one edge

`Graph.addEdge f u v` is `Graph.singleEdge u v f ∪ G`, so a shared edge would be resolved in favour
of the new one; `hf : f ∉ E(G)` rules that out and is what makes `G ≤ G.addEdge f u v`. The vertex
set does not grow, which is the whole reason this case is cheaper than a general union: the vertex
map is `D.vertex` transported along `V(G.addEdge f u v) = V(G)`, with no `dite` and no `Agree`. -/

section AddEdge

variable (hu : u ∈ V(G)) (hv : v ∈ V(G))

lemma vertexSet_addEdge_eq (hu : u ∈ V(G)) (hv : v ∈ V(G)) (f : β) : V(G.addEdge f u v) = V(G) := by
  simp [vertexSet_addEdge, insert_subset_iff, hu, hv]

include hu hv in
lemma mem_vertexSet_of_mem_vertexSet_addEdge {w : α} (hw : w ∈ V(G.addEdge f u v)) : w ∈ V(G) :=
  vertexSet_addEdge_eq hu hv f ▸ hw

lemma eq_of_notMem_edgeSet {ed : E(G.addEdge f u v)} (hed : ed.1 ∉ E(G)) : ed.1 = f := by grind

/-- The vertex placement of `D.addEdge`: the new edge brings no new vertex, so this is `D.vertex`
transported along `vertexSet_addEdge_eq`. -/
def addEdgeVertex (D : Drawing G X) (hu : u ∈ V(G)) (hv : v ∈ V(G)) (f : β)
    (w : V(G.addEdge f u v)) : X :=
  D.vertex ⟨w.1, mem_vertexSet_of_mem_vertexSet_addEdge hu hv w.2⟩

include hu hv in
lemma addEdgeVertex_injective (D : Drawing G X) : Injective (D.addEdgeVertex hu hv f) :=
  fun _ _ h ↦ Subtype.ext congr(($(D.vertex_injective h) : α))

include hu hv in
@[simp]
lemma range_addEdgeVertex (D : Drawing G X) : range (D.addEdgeVertex hu hv f) = range D.vertex := by
  refine subset_antisymm (by rintro _ ⟨w, rfl⟩; exact ⟨_, rfl⟩) ?_
  rintro _ ⟨w, rfl⟩
  exact ⟨⟨w.1, by simp [vertexSet_addEdge, w.2]⟩, rfl⟩

/-! The two transport lemmas for an old edge. They are the analogues of
`Drawing.restrict_vertex_edgeSource` and `Drawing.restrict_vertex_edgeTarget`, and hold for the
same reason: `IsSubgraph.source` and `IsSubgraph.target` are available for `G ≤ G.addEdge f u v`.
They exist to make `addEdgeEdge` typecheck. -/

include hu hv in
lemma addEdgeVertex_edgeSource_of_mem (D : Drawing G X) (hf : f ∉ E(G)) {ed : E(G.addEdge f u v)}
    (hed : ed.1 ∈ E(G)) :
    D.addEdgeVertex hu hv f (edgeSource ed) = D.vertex (edgeSource ⟨ed.1, hed⟩) :=
  congrArg D.vertex (Subtype.ext ((le_addEdge (x := u) (y := v) hf).source hed))

include hu hv in
lemma addEdgeVertex_edgeTarget_of_mem (D : Drawing G X) (hf : f ∉ E(G))
    {ed : E(G.addEdge f u v)} (hed : ed.1 ∈ E(G)) :
    D.addEdgeVertex hu hv f (edgeTarget ed) = D.vertex (edgeTarget ⟨ed.1, hed⟩) :=
  congrArg D.vertex (Subtype.ext ((le_addEdge (x := u) (y := v) hf).target hed))

lemma sym2_ends_of_eq {ed : E(G.addEdge f u v)} (hed : ed.1 = f) :
    s(((edgeSource ed : V(G.addEdge f u v)) : α), ((edgeTarget ed : V(G.addEdge f u v)) : α))
      = s(u, v) := by
  have h := isLink_edgeSource_edgeTarget ed
  rw [hed] at h
  exact h.isLink_iff_sym2_eq.mp (G.addEdge_isLink f u v)

include hu hv in
/-- The ends of the new edge are the two prescribed points, in an order chosen by `ArbRel`. This
is the hypothesis `Path.reorient` consumes. -/
lemma sym2_addEdgeVertex_of_eq (D : Drawing G X) {ed : E(G.addEdge f u v)} (hed : ed.1 = f) :
    s(D.addEdgeVertex hu hv f (edgeSource ed), D.addEdgeVertex hu hv f (edgeTarget ed))
      = s(D.vertex ⟨u, hu⟩, D.vertex ⟨v, hv⟩) := by
  obtain ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ := Sym2.eq_iff.mp (sym2_ends_of_eq hed)
  · exact Sym2.eq_iff.mpr <| .inl ⟨congrArg D.vertex (Subtype.ext h₁),
      congrArg D.vertex (Subtype.ext h₂)⟩
  exact Sym2.eq_iff.mpr <| .inr ⟨congrArg D.vertex (Subtype.ext h₁),
    congrArg D.vertex (Subtype.ext h₂)⟩

open Classical in
/-- The edge placement of `D.addEdge`: the old edges keep their arcs, and `f` gets `γ`, reoriented
if `ArbRel` disagrees with the order the caller wrote. -/
noncomputable def addEdgeEdge (D : Drawing G X) (hu : u ∈ V(G)) (hv : v ∈ V(G)) (hf : f ∉ E(G))
    (γ : Path (D.vertex ⟨u, hu⟩) (D.vertex ⟨v, hv⟩)) (ed : E(G.addEdge f u v)) :
    Path (D.addEdgeVertex hu hv f (edgeSource ed)) (D.addEdgeVertex hu hv f (edgeTarget ed)) :=
  if hed : ed.1 ∈ E(G) then
    (D.edgePath ⟨ed.1, hed⟩).cast (D.addEdgeVertex_edgeSource_of_mem hu hv hf hed)
      (D.addEdgeVertex_edgeTarget_of_mem hu hv hf hed)
  else
    γ.reorient (D.sym2_addEdgeVertex_of_eq hu hv (eq_of_notMem_edgeSet hed))

/-! The computation lemmas for `addEdgeEdge`, at the level of `range` and `Path.Interior`. They
are never stated as equations between paths: `addEdgeEdge … ed` and `D.edgePath ⟨ed.1, hed⟩` have
different types, so such an equation is ill-typed and forces `HEq`. `Path.cast` and
`Path.reorient` keep `toFun` up to the swap, and both sets see through that. -/

variable (hf : f ∉ E(G)) (γ : Path (D.vertex ⟨u, hu⟩) (D.vertex ⟨v, hv⟩))

@[simp]
lemma range_addEdgeEdge_of_mem {ed : E(G.addEdge f u v)} (hed : ed.1 ∈ E(G)) :
    range (D.addEdgeEdge hu hv hf γ ed) = range (D.edgePath ⟨ed.1, hed⟩) := by
  rw [addEdgeEdge, dite_eq_left hed]
  rfl

@[simp]
lemma range_addEdgeEdge_of_notMem {ed : E(G.addEdge f u v)} (hed : ed.1 ∉ E(G)) :
    range (D.addEdgeEdge hu hv hf γ ed) = range γ := by
  rw [addEdgeEdge, dite_eq_right hed, Path.range_reorient]

@[simp]
lemma addEdgeEdge_interior_of_mem {ed : E(G.addEdge f u v)} (hed : ed.1 ∈ E(G)) :
    (D.addEdgeEdge hu hv hf γ ed).Interior = (D.edgePath ⟨ed.1, hed⟩).Interior := by
  rw [addEdgeEdge, dite_eq_left hed]
  rfl

@[simp]
lemma addEdgeEdge_interior_of_notMem {ed : E(G.addEdge f u v)} (hed : ed.1 ∉ E(G)) :
    (D.addEdgeEdge hu hv hf γ ed).Interior = γ.Interior := by
  rw [addEdgeEdge, dite_eq_right hed, Path.reorient_interior]

/-! ### The four obligations of `ofVertexAndEdgePaths`

Each splits on `ed.1 ∈ E(G)`. The old case is the corresponding fact for `D`, transported along a
computation lemma; the new case is `IsFreeArc`; and in the last obligation the two new edges must
be equal, because both carry the label `f`. -/

include hu hv in
lemma addEdgeEdge_injOn (hγ : D.IsFreeArc γ) (ed : E(G.addEdge f u v)) :
    InjOn (D.addEdgeEdge hu hv hf γ ed) (Ioo (0 : I) 1) := by
  rw [addEdgeEdge]
  split_ifs with hed
  · exact D.edgePath_injOn_Ioo ⟨ed.1, hed⟩
  exact γ.injOn_reorient _ hγ.injOn

include hu hv in
lemma addEdgeEdge_interior_disjoint_vertex (hγ : D.IsFreeArc γ) (ed : E(G.addEdge f u v)) :
    Disjoint (D.addEdgeEdge hu hv hf γ ed).Interior (range (D.addEdgeVertex hu hv f)) := by
  rw [range_addEdgeVertex hu hv]
  by_cases hed : ed.1 ∈ E(G)
  · rw [addEdgeEdge_interior_of_mem hu hv hf γ hed]
    exact D.pathInterior_edgePath_disjoint_vertex _
  rw [addEdgeEdge_interior_of_notMem hu hv hf γ hed]
  exact hγ.disjoint_range_vertex

include hu hv in
lemma addEdgeEdge_interior_disjoint (hγ : D.IsFreeArc γ) {ed₁ ed₂ : E(G.addEdge f u v)}
    (hne : ed₁ ≠ ed₂) :
    Disjoint (D.addEdgeEdge hu hv hf γ ed₁).Interior (D.addEdgeEdge hu hv hf γ ed₂).Interior := by
  by_cases hed₁ : ed₁.1 ∈ E(G) <;> by_cases hed₂ : ed₂.1 ∈ E(G)
  · rw [addEdgeEdge_interior_of_mem hu hv hf γ hed₁, addEdgeEdge_interior_of_mem hu hv hf γ hed₂]
    exact D.pathInterior_edgePath_disjoint fun h ↦ hne (Subtype.ext congr(($h : β)))
  · rw [addEdgeEdge_interior_of_mem hu hv hf γ hed₁,
      addEdgeEdge_interior_of_notMem hu hv hf γ hed₂]
    exact ((hγ.disjoint_range_edgePath _).mono_right
      (Path.interior_subset_range _)).symm
  · rw [addEdgeEdge_interior_of_notMem hu hv hf γ hed₁,
      addEdgeEdge_interior_of_mem hu hv hf γ hed₂]
    exact (hγ.disjoint_range_edgePath _).mono_right (Path.interior_subset_range _)
  · exact absurd (Subtype.ext ((eq_of_notMem_edgeSet hed₁).trans
      (eq_of_notMem_edgeSet hed₂).symm)) hne

/-- **Insertion of one edge.** A drawing of `G` and a free arc between the images of `u` and `v`
assemble into a drawing of `G` with one more edge `f` joining `u` and `v`.

`u = v` is allowed and is the loop case: `Drawing.ofVertexAndEdgePaths` asks for injectivity only
on the open interval. -/
noncomputable def addEdge (D : Drawing G X) (hu : u ∈ V(G)) (hv : v ∈ V(G)) (hf : f ∉ E(G))
    (γ : Path (D.vertex ⟨u, hu⟩) (D.vertex ⟨v, hv⟩)) (hγ : D.IsFreeArc γ) :
    Drawing (G.addEdge f u v) X :=
  ofVertexAndEdgePaths (D.addEdgeVertex hu hv f) (D.addEdgeVertex_injective hu hv)
    (D.addEdgeEdge hu hv hf γ) (addEdgeEdge_injOn hu hv hf γ hγ)
    (addEdgeEdge_interior_disjoint_vertex hu hv hf γ hγ)
    fun _ _ ↦ addEdgeEdge_interior_disjoint hu hv hf γ hγ

@[simp]
lemma addEdge_vertex (hγ : D.IsFreeArc γ) (w : V(G.addEdge f u v)) :
    (D.addEdge hu hv hf γ hγ).vertex w = D.addEdgeVertex hu hv f w := rfl

@[simp]
lemma range_edgePath_addEdge (hγ : D.IsFreeArc γ) (ed : E(G.addEdge f u v)) :
    range ((D.addEdge hu hv hf γ hγ).edgePath ed) = range (D.addEdgeEdge hu hv hf γ ed) := rfl

include hu hv in
/-- The support of the extended drawing. This is what lets a caller insert edges one at a time:
`IsFreeArc` for the next arc is a statement about `D.support ∪ range γ`. -/
lemma support_addEdge (hγ : D.IsFreeArc γ) :
    (D.addEdge hu hv hf γ hγ).support = D.support ∪ range γ := by
  have h : (D.addEdge hu hv hf γ hγ).support
      = range (D.addEdgeVertex hu hv f) ∪ ⋃ ed, range (D.addEdgeEdge hu hv hf γ ed) :=
    (D.addEdge hu hv hf γ hγ).support_eq
  rw [h, range_addEdgeVertex hu hv, D.support_eq, union_assoc]
  congr 1
  ext z
  simp only [mem_iUnion, mem_union]
  refine ⟨?_, ?_⟩
  · rintro ⟨ed, hz⟩
    by_cases hed : ed.1 ∈ E(G)
    · rw [range_addEdgeEdge_of_mem hu hv hf γ hed] at hz
      exact .inl ⟨_, hz⟩
    · rw [range_addEdgeEdge_of_notMem hu hv hf γ hed] at hz
      exact .inr hz
  · rintro (⟨e, hz⟩ | hz)
    · exact ⟨⟨e.1, by simp [edgeSet_addEdge, e.2]⟩,
        by rwa [range_addEdgeEdge_of_mem hu hv hf γ e.2]⟩
    · exact ⟨⟨f, by simp [edgeSet_addEdge]⟩,
        by rwa [range_addEdgeEdge_of_notMem hu hv hf γ hf]⟩

end AddEdge

end Drawing

/-! ### A genuinely fresh auxiliary edge -/

/-- Relabel every old edge by `Sum.inl` and add the new edge `Sum.inr ()`. This avoids any
assumption that the original edge type contains a fresh label. -/
def addFreshEdge (G : Graph α β) (u v : α) : Graph α (β ⊕ Unit) :=
  (G.edgeMap Sum.inl).addEdge (Sum.inr ()) u v

namespace Drawing

/-- Add a genuinely fresh edge along a free arc. This is `addEdge` after transporting the old
drawing across the `Sum.inl` relabelling. -/
noncomputable def addFreshEdge (D : Drawing G X) (hu : u ∈ V(G)) (hv : v ∈ V(G))
    (γ : Path (D.vertex ⟨u, hu⟩) (D.vertex ⟨v, hv⟩)) (hγ : D.IsFreeArc γ) :
    Drawing (G.addFreshEdge u v) X := by
  sorry

/-- Adding the fresh auxiliary edge changes the image only by adjoining the supplied arc. -/
@[simp]
theorem support_addFreshEdge (D : Drawing G X) (hu : u ∈ V(G)) (hv : v ∈ V(G))
    (γ : Path (D.vertex ⟨u, hu⟩) (D.vertex ⟨v, hv⟩)) (hγ : D.IsFreeArc γ) :
    (D.addFreshEdge hu hv γ hγ).support = D.support ∪ range γ := by
  sorry

/-! ### Inserting a path by subdivision -/

/-- The combinatorial certificate that replacing the fresh auxiliary edge by `P` gives
`G ∪ P.toGraph`. Old edges are represented by one-edge routes and the fresh edge is represented
by `P`. -/
noncomputable def addPathSubdivision {P : WList α β} (hP : P.toGraph.IsPath P)
    (hu : u ∈ V(G)) (hv : v ∈ V(G)) (hends : P.first = u ∧ P.last = v)
    (hint : V(G) ∩ V(P.toGraph) = {P.first, P.last})
    (hE : Disjoint E(G) E(P.toGraph)) :
    (G.addFreshEdge u v).IsoSubdivision (G ∪ P.toGraph) := by
  sorry

/-- On every original vertex, the subdivision certificate uses the corresponding vertex of the
union graph. -/
theorem addPathSubdivision_branchVertex {P : WList α β} (hP : P.toGraph.IsPath P)
    (hu : u ∈ V(G)) (hv : v ∈ V(G)) (hends : P.first = u ∧ P.last = v)
    (hint : V(G) ∩ V(P.toGraph) = {P.first, P.last})
    (hE : Disjoint E(G) E(P.toGraph)) (x : V(G.addFreshEdge u v)) :
    ((addPathSubdivision hP hu hv hends hint hE).branchVertex x).1 = x.1 := by
  sorry

/-- Insert `P` along a free arc by adding one fresh edge and subdividing that edge. -/
noncomputable def addPath (D : Drawing G X) {P : WList α β} (hP : P.toGraph.IsPath P)
    (hu : u ∈ V(G)) (hv : v ∈ V(G)) (hends : P.first = u ∧ P.last = v)
    (hint : V(G) ∩ V(P.toGraph) = {P.first, P.last})
    (hE : Disjoint E(G) E(P.toGraph))
    (γ : Path (D.vertex ⟨u, hu⟩) (D.vertex ⟨v, hv⟩)) (hγ : D.IsFreeArc γ) :
    Drawing (G ∪ P.toGraph) X :=
  (D.addFreshEdge hu hv γ hγ).subdivide (addPathSubdivision hP hu hv hends hint hE)

/-- Original vertices retain their positions after path insertion. -/
theorem addPath_vertex_of_mem_left (D : Drawing G X) {P : WList α β}
    (hP : P.toGraph.IsPath P) (hu : u ∈ V(G)) (hv : v ∈ V(G))
    (hends : P.first = u ∧ P.last = v)
    (hint : V(G) ∩ V(P.toGraph) = {P.first, P.last})
    (hE : Disjoint E(G) E(P.toGraph))
    (γ : Path (D.vertex ⟨u, hu⟩) (D.vertex ⟨v, hv⟩)) (hγ : D.IsFreeArc γ)
    {w : V(G ∪ P.toGraph)} (hw : w.1 ∈ V(G)) :
    (D.addPath hP hu hv hends hint hE γ hγ).vertex w = D.vertex ⟨w.1, hw⟩ := by
  sorry

/-- Original edges retain exactly their old closed-cell images after path insertion. -/
theorem range_edgePath_addPath_of_mem_left (D : Drawing G X) {P : WList α β}
    (hP : P.toGraph.IsPath P) (hu : u ∈ V(G)) (hv : v ∈ V(G))
    (hends : P.first = u ∧ P.last = v)
    (hint : V(G) ∩ V(P.toGraph) = {P.first, P.last})
    (hE : Disjoint E(G) E(P.toGraph))
    (γ : Path (D.vertex ⟨u, hu⟩) (D.vertex ⟨v, hv⟩)) (hγ : D.IsFreeArc γ)
    {e : E(G ∪ P.toGraph)} (he : e.1 ∈ E(G)) :
    range ((D.addPath hP hu hv hends hint hE γ hγ).edgePath e) =
      range (D.edgePath ⟨e.1, he⟩) := by
  sorry

/-- Every new path edge is drawn along a subarc of the supplied free arc. -/
theorem range_edgePath_addPath_of_mem_right_subset (D : Drawing G X) {P : WList α β}
    (hP : P.toGraph.IsPath P) (hu : u ∈ V(G)) (hv : v ∈ V(G))
    (hends : P.first = u ∧ P.last = v)
    (hint : V(G) ∩ V(P.toGraph) = {P.first, P.last})
    (hE : Disjoint E(G) E(P.toGraph))
    (γ : Path (D.vertex ⟨u, hu⟩) (D.vertex ⟨v, hv⟩)) (hγ : D.IsFreeArc γ)
    {e : E(G ∪ P.toGraph)} (he : e.1 ∈ E(P.toGraph)) :
    range ((D.addPath hP hu hv hends hint hE γ hγ).edgePath e) ⊆ range γ := by
  sorry

/-- Path insertion leaves the original drawing unchanged. -/
theorem addPath_extends (D : Drawing G X) {P : WList α β} (hP : P.toGraph.IsPath P)
    (hu : u ∈ V(G)) (hv : v ∈ V(G)) (hends : P.first = u ∧ P.last = v)
    (hint : V(G) ∩ V(P.toGraph) = {P.first, P.last})
    (hE : Disjoint E(G) E(P.toGraph))
    (γ : Path (D.vertex ⟨u, hu⟩) (D.vertex ⟨v, hv⟩)) (hγ : D.IsFreeArc γ) :
    (D.addPath hP hu hv hends hint hE γ hγ).Extends D (Graph.left_le_union G P.toGraph) := by
  sorry

/-- Inserting a path along `γ` adjoins exactly the image of `γ` to the old drawing. -/
@[simp]
theorem support_addPath (D : Drawing G X) {P : WList α β} (hP : P.toGraph.IsPath P)
    (hu : u ∈ V(G)) (hv : v ∈ V(G)) (hends : P.first = u ∧ P.last = v)
    (hint : V(G) ∩ V(P.toGraph) = {P.first, P.last})
    (hE : Disjoint E(G) E(P.toGraph))
    (γ : Path (D.vertex ⟨u, hu⟩) (D.vertex ⟨v, hv⟩)) (hγ : D.IsFreeArc γ) :
    (D.addPath hP hu hv hends hint hE γ hγ).support = D.support ∪ range γ := by
  sorry

end Drawing


end


end Graph
