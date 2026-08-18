module

public import Matroid.Graph.Planarity.StarLemma

@[expose] public section

/-!
# Inserting an edge or a path into a drawing

Given a drawing of `G` and an arc whose interior misses the drawing, this file extends the drawing
by one edge or by a path. The combinators are specialized to those two cases: `addEdge` adds one
edge, while `addPath` adds a path whose interior vertices are new and whose two ends attach to the
original drawing. The geometric lemmas later in the file produce the free arcs used by these
constructions.

## Main definitions

- `Graph.Drawing.IsFreeArc`: an arc injective on `Ioo 0 1` whose relative interior misses the
  support. This is what both geometric inputs of §13.1 deliver, and the only thing either
  combinator asks of the plane.
- `Graph.Drawing.addEdge`: extend a drawing by one edge drawn along a free arc between two of its
  vertices. `u = v` is allowed and is the loop case.
- `Graph.Drawing.IsFreeAttachment`, `Graph.Drawing.addPath`: glue a drawing of a path graph onto a
  drawing that it meets only at the path's two ends.

- `Graph.Drawing.IsFreePolygonalArc`: the polygonal form of the same thing, which is what §13.1's
  geometry produces and what keeps the extended drawing polygonal.

## Main statements

- `Graph.Drawing.support_addEdge`, `Graph.Drawing.support_addPath`: the support of the extended
  drawing, which is what lets a caller insert edges one at a time.
- `Graph.PLPlanar.addEdge_of_isLink`, `Graph.PLPlanar.addLoop`: insert an edge or loop in a
  polygonal drawing.
- `Graph.Planar.addPath_of_isFreeAttachment`, `Graph.Planar.addPath_of_isFreeArc`: the path forms.
- The remaining geometric statements are `exists_face_frontier_superset_edgePath_interior`,
  `exists_freePolygonalArc_in_faceSet`, `exists_isFreePolygonalArc_loop`, `isPL_addEdge`, and
  `exists_isFreeAttachment_of_isFreeArc`.
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

noncomputable section

variable {α β : Type*} {G : Graph α β} {u v : α} {f : β}

namespace Drawing

/-! ### Free arcs -/

/-- An arc of `X` that a drawing can absorb as a new edge: injectively parametrized on the open
interval, with relative interior missing the support of `D` altogether.

The geometric constructions below produce this condition from a face or from a sector at a vertex. -/
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

lemma vertexSet_addEdge_eq (hu : u ∈ V(G)) (hv : v ∈ V(G)) (f : β) :
    V(G.addEdge f u v) = V(G) := by
  simp [vertexSet_addEdge, insert_subset_iff, hu, hv]

include hu hv in
lemma mem_vertexSet_of_mem_vertexSet_addEdge {w : α} (hw : w ∈ V(G.addEdge f u v)) : w ∈ V(G) :=
  vertexSet_addEdge_eq hu hv f ▸ hw

lemma eq_of_notMem_edgeSet {ed : E(G.addEdge f u v)} (hed : ed.1 ∉ E(G)) : ed.1 = f := by
  have := ed.2
  simp only [edgeSet_addEdge] at this
  grind

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
lemma range_addEdgeVertex (D : Drawing G X) :
    range (D.addEdgeVertex hu hv f) = range D.vertex := by
  refine subset_antisymm (by rintro _ ⟨w, rfl⟩; exact ⟨_, rfl⟩) ?_
  rintro _ ⟨w, rfl⟩
  exact ⟨⟨w.1, by simp [vertexSet_addEdge, w.2]⟩, rfl⟩

/-! The two transport lemmas for an old edge. They are the analogues of
`Drawing.restrict_vertex_edgeSource` and `Drawing.restrict_vertex_edgeTarget`, and hold for the
same reason: `IsSubgraph.source` and `IsSubgraph.target` are available for `G ≤ G.addEdge f u v`.
They exist to make `addEdgeEdge` typecheck. -/

include hu hv in
lemma addEdgeVertex_edgeSource_of_mem (D : Drawing G X) (hf : f ∉ E(G))
    {ed : E(G.addEdge f u v)} (hed : ed.1 ∈ E(G)) :
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
  · exact Sym2.eq_iff.mpr <| .inr ⟨congrArg D.vertex (Subtype.ext h₁),
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
  · exact γ.injOn_reorient _ hγ.injOn

include hu hv in
lemma addEdgeEdge_interior_disjoint_vertex (hγ : D.IsFreeArc γ) (ed : E(G.addEdge f u v)) :
    Disjoint (D.addEdgeEdge hu hv hf γ ed).Interior (range (D.addEdgeVertex hu hv f)) := by
  rw [range_addEdgeVertex hu hv]
  by_cases hed : ed.1 ∈ E(G)
  · rw [addEdgeEdge_interior_of_mem hu hv hf γ hed]
    exact D.pathInterior_edgePath_disjoint_vertex _
  · rw [addEdgeEdge_interior_of_notMem hu hv hf γ hed]
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

/-! ### Adding a path

The path case adds the interior vertices of `P`, so its vertex map distinguishes the two graphs.
The attachment hypotheses identify the overlap with `{P.first, P.last}` and align the two drawings
there. -/

section AddPath

variable {P : WList α β} {D : Drawing G X} {DP : Drawing P.toGraph X}

/-- What it takes to glue a drawing of the path graph `P.toGraph` onto a drawing of `G`: the two
graphs share no edge, they share exactly the two ends of `P` as vertices, the two drawings place
those two vertices at the same point of `X`, and the two supports meet nowhere else.

`agree` is a **typing** obligation, not a proof obligation: without it `addPathEdge` does not
elaborate, because an edge of `P.toGraph` whose source is a shared vertex must be assigned a path
*starting at* `addPathVertex … (edgeSource _)`, which computes to `D.vertex …`, whereas
`DP.edgePath` starts at `DP.vertex …`. Under `vertexSet_inter` it says exactly that `D` and `DP`
agree at `P.first` and at `P.last`.

`support_inter` is stated with `⊆` rather than `=` on purpose: given `agree` the reverse inclusion
is automatic, so an equality would only make every call site harder. -/
structure IsFreeAttachment (D : Drawing G X) (DP : Drawing P.toGraph X) : Prop where
  edgeSet_disjoint : Disjoint E(G) E(P.toGraph)
  vertexSet_inter : V(G) ∩ V(P.toGraph) = {P.first, P.last}
  agree : ∀ (x : α) (hG : x ∈ V(G)) (hP : x ∈ V(P.toGraph)), D.vertex ⟨x, hG⟩ = DP.vertex ⟨x, hP⟩
  support_inter : D.support ∩ DP.support ⊆ D.vertex '' {w : V(G) | w.1 ∈ V(P.toGraph)}

namespace IsFreeAttachment

lemma compatible (h : D.IsFreeAttachment DP) : G.Compatible P.toGraph :=
  Compatible.of_disjoint_edgeSet h.edgeSet_disjoint

/-- **The workhorse of the cross case.** A point common to the two supports is not merely *some*
point of `D`: it is a vertex image on *both* sides. That upgrade is what rules out a shared point
lying in the interior of an edge, and it discharges the mixed case of all four obligations. -/
lemma mem_range_vertex_of_mem_support_inter (h : D.IsFreeAttachment DP) {z : X}
    (hz₁ : z ∈ D.support) (hz₂ : z ∈ DP.support) :
    z ∈ range D.vertex ∧ z ∈ range DP.vertex := by
  obtain ⟨w, hw, rfl⟩ := h.support_inter ⟨hz₁, hz₂⟩
  exact ⟨⟨w, rfl⟩, ⟨⟨w.1, hw⟩, (h.agree w.1 w.2 hw).symm⟩⟩

/-- No interior point of an edge of `G` lies on the drawing of the path. -/
lemma notMem_support_right_of_mem_interior (h : D.IsFreeAttachment DP) (e : E(G)) {z : X}
    (hz : z ∈ (D.edgePath e).Interior) : z ∉ DP.support := fun hz₂ ↦
  (D.pathInterior_edgePath_disjoint_vertex e).notMem_of_mem_left hz
    (h.mem_range_vertex_of_mem_support_inter
      (D.edgePath_range_subset_support e (Path.interior_subset_range _ hz)) hz₂).1

/-- No interior point of an edge of the path lies on the drawing of `G`. -/
lemma notMem_support_left_of_mem_interior (h : D.IsFreeAttachment DP) (e : E(P.toGraph)) {z : X}
    (hz : z ∈ (DP.edgePath e).Interior) : z ∉ D.support := fun hz₁ ↦
  (DP.pathInterior_edgePath_disjoint_vertex e).notMem_of_mem_left hz
    (h.mem_range_vertex_of_mem_support_inter hz₁
      (DP.edgePath_range_subset_support e (Path.interior_subset_range _ hz))).2

lemma disjoint_interior_range_vertex_right (h : D.IsFreeAttachment DP) (e : E(G)) :
    Disjoint (D.edgePath e).Interior (range DP.vertex) :=
  disjoint_left.mpr fun _ hz ⟨w, hw⟩ ↦
    h.notMem_support_right_of_mem_interior e hz (hw ▸ DP.vertex_mem_support w)

lemma disjoint_interior_range_vertex_left (h : D.IsFreeAttachment DP) (e : E(P.toGraph)) :
    Disjoint (DP.edgePath e).Interior (range D.vertex) :=
  disjoint_left.mpr fun _ hz ⟨w, hw⟩ ↦
    h.notMem_support_left_of_mem_interior e hz (hw ▸ D.vertex_mem_support w)

lemma disjoint_interior_cross (h : D.IsFreeAttachment DP) (e : E(G)) (e' : E(P.toGraph)) :
    Disjoint (D.edgePath e).Interior (DP.edgePath e').Interior :=
  disjoint_left.mpr fun _ hz hz' ↦ h.notMem_support_right_of_mem_interior e hz
    (DP.edgePath_range_subset_support e' (Path.interior_subset_range _ hz'))

end IsFreeAttachment

open Classical in
/-- The vertex placement of `D.addPath`: use `D` where it is defined, `DP` otherwise. -/
noncomputable def addPathVertex (D : Drawing G X) (DP : Drawing P.toGraph X)
    (w : V(G ∪ P.toGraph)) : X :=
  if hw : w.1 ∈ V(G) then D.vertex ⟨w.1, hw⟩
  else DP.vertex ⟨w.1, Or.resolve_left (show w.1 ∈ V(G) ∨ w.1 ∈ V(P.toGraph) from w.2) hw⟩

@[simp]
lemma addPathVertex_of_mem_left (D : Drawing G X) (DP : Drawing P.toGraph X)
    {w : V(G ∪ P.toGraph)} (hw : w.1 ∈ V(G)) : addPathVertex D DP w = D.vertex ⟨w.1, hw⟩ :=
  dite_eq_left hw

/-- The right-hand computation rule. Unlike the left one it needs `agree`, because a vertex of the
path may also be a vertex of `G`, in which case `addPathVertex` took the `D` branch. -/
lemma addPathVertex_of_mem_right (h : D.IsFreeAttachment DP) {w : V(G ∪ P.toGraph)}
    (hw : w.1 ∈ V(P.toGraph)) : addPathVertex D DP w = DP.vertex ⟨w.1, hw⟩ := by
  by_cases hw₁ : w.1 ∈ V(G)
  · rw [addPathVertex_of_mem_left D DP hw₁]
    exact h.agree w.1 hw₁ hw
  · rw [addPathVertex, dite_eq_right hw₁]

lemma range_addPathVertex (h : D.IsFreeAttachment DP) :
    range (addPathVertex D DP) = range D.vertex ∪ range DP.vertex := by
  refine subset_antisymm (range_subset_iff.mpr fun w ↦ ?_) (union_subset ?_ ?_)
  · by_cases hw : w.1 ∈ V(G)
    · exact .inl ⟨_, (addPathVertex_of_mem_left D DP hw).symm⟩
    · exact .inr ⟨_, (addPathVertex_of_mem_right h
        (Or.resolve_left (show w.1 ∈ V(G) ∨ w.1 ∈ V(P.toGraph) from w.2) hw)).symm⟩
  · rintro _ ⟨w, rfl⟩
    exact ⟨⟨w.1, .inl w.2⟩, addPathVertex_of_mem_left D DP w.2⟩
  · rintro _ ⟨w, rfl⟩
    exact ⟨⟨w.1, .inr w.2⟩, addPathVertex_of_mem_right h w.2⟩

/-! The four `edgeSource`/`edgeTarget` transport lemmas. They are the exact analogues of
`Drawing.restrict_vertex_edgeSource` and `Drawing.restrict_vertex_edgeTarget`, and hold for the
same reason: `ArbRel` fixes one linear order per *type*, so `IsSubgraph.source` and
`IsSubgraph.target` are available for `G ≤ G ∪ P.toGraph` and for `P.toGraph ≤ G ∪ P.toGraph`.
They exist to make `addPathEdge` typecheck. -/

lemma addPathVertex_edgeSource_left (D : Drawing G X) (DP : Drawing P.toGraph X)
    {ed : E(G ∪ P.toGraph)} (hed : ed.1 ∈ E(G)) :
    addPathVertex D DP (edgeSource ed) = D.vertex (edgeSource ⟨ed.1, hed⟩) := by
  have hsrc : (edgeSource ed : V(G ∪ P.toGraph)).1 = (edgeSource (⟨ed.1, hed⟩ : E(G))).1 :=
    (Graph.left_le_union G P.toGraph).source hed
  rw [addPathVertex_of_mem_left D DP (hsrc ▸ (edgeSource (⟨ed.1, hed⟩ : E(G))).2)]
  exact congrArg D.vertex (Subtype.ext hsrc)

lemma addPathVertex_edgeTarget_left (D : Drawing G X) (DP : Drawing P.toGraph X)
    {ed : E(G ∪ P.toGraph)} (hed : ed.1 ∈ E(G)) :
    addPathVertex D DP (edgeTarget ed) = D.vertex (edgeTarget ⟨ed.1, hed⟩) := by
  have htgt : (edgeTarget ed : V(G ∪ P.toGraph)).1 = (edgeTarget (⟨ed.1, hed⟩ : E(G))).1 :=
    (Graph.left_le_union G P.toGraph).target hed
  rw [addPathVertex_of_mem_left D DP (htgt ▸ (edgeTarget (⟨ed.1, hed⟩ : E(G))).2)]
  exact congrArg D.vertex (Subtype.ext htgt)

lemma addPathVertex_edgeSource_right (h : D.IsFreeAttachment DP) {ed : E(G ∪ P.toGraph)}
    (hed : ed.1 ∈ E(P.toGraph)) :
    addPathVertex D DP (edgeSource ed) = DP.vertex (edgeSource ⟨ed.1, hed⟩) := by
  have hsrc : (edgeSource ed : V(G ∪ P.toGraph)).1 =
      (edgeSource (⟨ed.1, hed⟩ : E(P.toGraph))).1 := h.compatible.right_le_union.source hed
  rw [addPathVertex_of_mem_right h (hsrc ▸ (edgeSource (⟨ed.1, hed⟩ : E(P.toGraph))).2)]
  exact congrArg DP.vertex (Subtype.ext hsrc)

lemma addPathVertex_edgeTarget_right (h : D.IsFreeAttachment DP) {ed : E(G ∪ P.toGraph)}
    (hed : ed.1 ∈ E(P.toGraph)) :
    addPathVertex D DP (edgeTarget ed) = DP.vertex (edgeTarget ⟨ed.1, hed⟩) := by
  have htgt : (edgeTarget ed : V(G ∪ P.toGraph)).1 =
      (edgeTarget (⟨ed.1, hed⟩ : E(P.toGraph))).1 := h.compatible.right_le_union.target hed
  rw [addPathVertex_of_mem_right h (htgt ▸ (edgeTarget (⟨ed.1, hed⟩ : E(P.toGraph))).2)]
  exact congrArg DP.vertex (Subtype.ext htgt)

open Classical in
/-- The edge placement of `D.addPath`. There is no shared edge to arbitrate, by
`IsFreeAttachment.edgeSet_disjoint`. -/
noncomputable def addPathEdge (h : D.IsFreeAttachment DP) (ed : E(G ∪ P.toGraph)) :
    Path (addPathVertex D DP (edgeSource ed)) (addPathVertex D DP (edgeTarget ed)) :=
  if hed : ed.1 ∈ E(G) then
    (D.edgePath ⟨ed.1, hed⟩).cast (addPathVertex_edgeSource_left D DP hed)
      (addPathVertex_edgeTarget_left D DP hed)
  else
    have hed' : ed.1 ∈ E(P.toGraph) :=
      Or.resolve_left (show ed.1 ∈ E(G) ∨ ed.1 ∈ E(P.toGraph) from ed.2) hed
    (DP.edgePath ⟨ed.1, hed'⟩).cast (addPathVertex_edgeSource_right h hed')
      (addPathVertex_edgeTarget_right h hed')

/-! The computation lemmas for `addPathEdge`, at the level of `range` and `Path.Interior`, for the
same typing reason as in the single-edge case. -/

@[simp]
lemma range_addPathEdge_of_mem_left (h : D.IsFreeAttachment DP) {ed : E(G ∪ P.toGraph)}
    (hed : ed.1 ∈ E(G)) : range (addPathEdge h ed) = range (D.edgePath ⟨ed.1, hed⟩) := by
  rw [addPathEdge, dite_eq_left hed]
  rfl

@[simp]
lemma range_addPathEdge_of_notMem_left (h : D.IsFreeAttachment DP) {ed : E(G ∪ P.toGraph)}
    (hed : ed.1 ∉ E(G)) (hed' : ed.1 ∈ E(P.toGraph)) :
    range (addPathEdge h ed) = range (DP.edgePath ⟨ed.1, hed'⟩) := by
  rw [addPathEdge, dite_eq_right hed]
  rfl

@[simp]
lemma addPathEdge_interior_of_mem_left (h : D.IsFreeAttachment DP) {ed : E(G ∪ P.toGraph)}
    (hed : ed.1 ∈ E(G)) : (addPathEdge h ed).Interior = (D.edgePath ⟨ed.1, hed⟩).Interior := by
  rw [addPathEdge, dite_eq_left hed]
  rfl

@[simp]
lemma addPathEdge_interior_of_notMem_left (h : D.IsFreeAttachment DP) {ed : E(G ∪ P.toGraph)}
    (hed : ed.1 ∉ E(G)) (hed' : ed.1 ∈ E(P.toGraph)) :
    (addPathEdge h ed).Interior = (DP.edgePath ⟨ed.1, hed'⟩).Interior := by
  rw [addPathEdge, dite_eq_right hed]
  rfl

lemma mem_edgeSet_right_of_notMem_left {ed : E(G ∪ P.toGraph)} (hed : ed.1 ∉ E(G)) :
    ed.1 ∈ E(P.toGraph) :=
  Or.resolve_left (show ed.1 ∈ E(G) ∨ ed.1 ∈ E(P.toGraph) from ed.2) hed

/-! ### The four obligations of `ofVertexAndEdgePaths`

Each splits on membership in `E(G)`/`V(G)` into a `D` case, a `DP` case and a cross case. The
first two are the corresponding fact for `D` or for `DP`, transported along a computation lemma;
the cross case is one of the three `IsFreeAttachment` lemmas above. -/

lemma addPathVertex_injective (h : D.IsFreeAttachment DP) : Injective (addPathVertex D DP) := by
  intro w₁ w₂ hw
  refine Subtype.ext ?_
  by_cases h₁ : w₁.1 ∈ V(G) <;> by_cases h₂ : w₂.1 ∈ V(G)
  · rw [addPathVertex_of_mem_left D DP h₁, addPathVertex_of_mem_left D DP h₂] at hw
    exact congr(($(D.vertex_injective hw) : α))
  · have h₂' := Or.resolve_left (show w₂.1 ∈ V(G) ∨ w₂.1 ∈ V(P.toGraph) from w₂.2) h₂
    rw [addPathVertex_of_mem_left D DP h₁, addPathVertex_of_mem_right h h₂'] at hw
    obtain ⟨w, hwP, hwz⟩ := h.support_inter
      ⟨D.vertex_mem_support _, hw ▸ DP.vertex_mem_support _⟩
    obtain rfl : w = ⟨w₁.1, h₁⟩ := D.vertex_injective hwz
    exact congr(($(DP.vertex_injective ((h.agree w₁.1 h₁ hwP).symm.trans hw)) : α))
  · have h₁' := Or.resolve_left (show w₁.1 ∈ V(G) ∨ w₁.1 ∈ V(P.toGraph) from w₁.2) h₁
    rw [addPathVertex_of_mem_right h h₁', addPathVertex_of_mem_left D DP h₂] at hw
    obtain ⟨w, hwP, hwz⟩ := h.support_inter
      ⟨D.vertex_mem_support _, hw ▸ DP.vertex_mem_support _⟩
    obtain rfl : w = ⟨w₂.1, h₂⟩ := D.vertex_injective hwz
    exact congr(($(DP.vertex_injective (hw.trans (h.agree w₂.1 h₂ hwP))) : α))
  · have h₁' := Or.resolve_left (show w₁.1 ∈ V(G) ∨ w₁.1 ∈ V(P.toGraph) from w₁.2) h₁
    have h₂' := Or.resolve_left (show w₂.1 ∈ V(G) ∨ w₂.1 ∈ V(P.toGraph) from w₂.2) h₂
    rw [addPathVertex_of_mem_right h h₁', addPathVertex_of_mem_right h h₂'] at hw
    exact congr(($(DP.vertex_injective hw) : α))

lemma addPathEdge_injOn (h : D.IsFreeAttachment DP) (ed : E(G ∪ P.toGraph)) :
    InjOn (addPathEdge h ed) (Ioo (0 : I) 1) := by
  rw [addPathEdge]
  split_ifs with hed
  · exact D.edgePath_injOn_Ioo _
  · exact DP.edgePath_injOn_Ioo _

lemma addPathEdge_interior_disjoint_vertex (h : D.IsFreeAttachment DP) (ed : E(G ∪ P.toGraph)) :
    Disjoint (addPathEdge h ed).Interior (range (addPathVertex D DP)) := by
  rw [range_addPathVertex h, disjoint_union_right]
  by_cases hed : ed.1 ∈ E(G)
  · rw [addPathEdge_interior_of_mem_left h hed]
    exact ⟨D.pathInterior_edgePath_disjoint_vertex _, h.disjoint_interior_range_vertex_right _⟩
  · rw [addPathEdge_interior_of_notMem_left h hed (mem_edgeSet_right_of_notMem_left hed)]
    exact ⟨h.disjoint_interior_range_vertex_left _, DP.pathInterior_edgePath_disjoint_vertex _⟩

lemma addPathEdge_interior_disjoint (h : D.IsFreeAttachment DP) {ed₁ ed₂ : E(G ∪ P.toGraph)}
    (hne : ed₁ ≠ ed₂) :
    Disjoint (addPathEdge h ed₁).Interior (addPathEdge h ed₂).Interior := by
  by_cases hed₁ : ed₁.1 ∈ E(G) <;> by_cases hed₂ : ed₂.1 ∈ E(G)
  · rw [addPathEdge_interior_of_mem_left h hed₁, addPathEdge_interior_of_mem_left h hed₂]
    exact D.pathInterior_edgePath_disjoint fun heq ↦ hne (Subtype.ext congr(($heq : β)))
  · rw [addPathEdge_interior_of_mem_left h hed₁,
      addPathEdge_interior_of_notMem_left h hed₂ (mem_edgeSet_right_of_notMem_left hed₂)]
    exact h.disjoint_interior_cross _ _
  · rw [addPathEdge_interior_of_notMem_left h hed₁ (mem_edgeSet_right_of_notMem_left hed₁),
      addPathEdge_interior_of_mem_left h hed₂]
    exact (h.disjoint_interior_cross _ _).symm
  · rw [addPathEdge_interior_of_notMem_left h hed₁ (mem_edgeSet_right_of_notMem_left hed₁),
      addPathEdge_interior_of_notMem_left h hed₂ (mem_edgeSet_right_of_notMem_left hed₂)]
    exact DP.pathInterior_edgePath_disjoint fun heq ↦ hne (Subtype.ext congr(($heq : β)))

/-- **Insertion of a path.** A drawing of `G` and a drawing of a path that meets it only at the
path's two ends assemble into a drawing of `G ∪ P.toGraph`. -/
noncomputable def addPath (D : Drawing G X) (DP : Drawing P.toGraph X)
    (h : D.IsFreeAttachment DP) : Drawing (G ∪ P.toGraph) X :=
  ofVertexAndEdgePaths (addPathVertex D DP) (addPathVertex_injective h) (addPathEdge h)
    (addPathEdge_injOn h) (addPathEdge_interior_disjoint_vertex h)
    fun _ _ ↦ addPathEdge_interior_disjoint h

@[simp]
lemma addPath_vertex (h : D.IsFreeAttachment DP) (w : V(G ∪ P.toGraph)) :
    (D.addPath DP h).vertex w = addPathVertex D DP w := rfl

@[simp]
lemma range_edgePath_addPath (h : D.IsFreeAttachment DP) (ed : E(G ∪ P.toGraph)) :
    range ((D.addPath DP h).edgePath ed) = range (addPathEdge h ed) := rfl

/-- The support of a glued drawing is the union of the two supports. This is what lets a caller
iterate `addPath`, and what turns a hypothesis about `D.support ∪ DP.support` into one about the
glued drawing. -/
lemma support_addPath (h : D.IsFreeAttachment DP) :
    (D.addPath DP h).support = D.support ∪ DP.support := by
  have hsupp : (D.addPath DP h).support
      = range (addPathVertex D DP) ∪ ⋃ ed, range (addPathEdge h ed) := (D.addPath DP h).support_eq
  rw [hsupp, range_addPathVertex h, D.support_eq, DP.support_eq]
  ext z
  simp only [mem_union, mem_iUnion]
  refine ⟨?_, ?_⟩
  · rintro ((hz | hz) | ⟨ed, hz⟩)
    · exact .inl (.inl hz)
    · exact .inr (.inl hz)
    by_cases hed : ed.1 ∈ E(G)
    · rw [range_addPathEdge_of_mem_left h hed] at hz
      exact .inl (.inr ⟨_, hz⟩)
    · rw [range_addPathEdge_of_notMem_left h hed (mem_edgeSet_right_of_notMem_left hed)] at hz
      exact .inr (.inr ⟨_, hz⟩)
  · rintro ((hz | ⟨e, hz⟩) | (hz | ⟨e, hz⟩))
    · exact .inl (.inl hz)
    · exact .inr ⟨⟨e.1, .inl e.2⟩, by rwa [range_addPathEdge_of_mem_left h e.2]⟩
    · exact .inl (.inr hz)
    · refine .inr ⟨⟨e.1, .inr e.2⟩, ?_⟩
      have hed : (⟨e.1, .inr e.2⟩ : E(G ∪ P.toGraph)).1 ∉ E(G) := fun hmem ↦
        h.edgeSet_disjoint.notMem_of_mem_left hmem e.2
      rwa [range_addPathEdge_of_notMem_left h hed e.2]

end AddPath

/-! ### The geometry

The combinators above are proved for arbitrary ambient spaces. The geometric inputs below are
polygonal: they choose a face incident with an edge or a sector at a vertex, then produce a free
polygonal arc. `IsFreePolygonalArc.isFreeArc` forgets the polygonal structure when calling
`Drawing.addEdge`; `isPL_addEdge` preserves it for later insertions.

The chain for a parallel edge is

`exists_face_frontier_superset_edgePath_interior` (a face incident with the open cell)
→ `vertex_mem_of_edgePath_interior_subset` (its ends lie on that frontier; proved)
→ `exists_freePolygonalArc_in_faceSet` (the routing primitive)
→ `IsFreePolygonalArc.isFreeArc` (proved)
→ `exists_isFreePolygonalArc_of_isLink` and `exists_isFreeArc_of_isLink` (proved)
→ `Planar.addEdge_of_isLink`.

For a loop the first three steps are replaced by `exists_isFreePolygonalArc_loop`, a triangle
inside one sector of the star at the vertex, and the rest is the same. `isPL_addEdge` is what makes
the result polygonal again, hence what lets Corollary 13.3 iterate 13.2; it is the reason the
geometry hands back a `PolygonalPath` and not just a `Path`. -/

section Geometry

/-- The polygonal form of `IsFreeArc`: an embedded polygonal arc — or an embedded circle, when its
two ends coincide, which is the loop case — meeting the drawing only at its ends.

This is what §13.1's geometry actually produces. `IsFreePolygonalArc.isFreeArc` forgets the
segments and hands `Drawing.addEdge` what it needs; `isPL_addEdge` keeps them. -/
structure IsFreePolygonalArc (D : Drawing G Plane) {z w : Plane}
    (Q : PolygonalPath z w) : Prop where
  isSimpleArcOrLoop : Q.IsSimpleArcOrLoop
  disjoint_support : Disjoint (Q.toSet \ {z, w}) D.support

/-- The bridge out of the polygonal category: `Path.interior_toPath` identifies the relative
interior of the parametrized arc with `toSet` minus the two ends, which is exactly the set
`IsFreePolygonalArc` controls. -/
lemma IsFreePolygonalArc.isFreeArc {D : Drawing G Plane} {z w : Plane} {Q : PolygonalPath z w}
    (hQ : D.IsFreePolygonalArc Q) : D.IsFreeArc Q.toPath where
  injOn := hQ.isSimpleArcOrLoop.injOn_toPath_Ioo
  disjoint_support := Path.interior_toPath_range hQ.isSimpleArcOrLoop hQ.disjoint_support

/-- An arc whose relative interior lies inside a face is free, because a face misses the support.
This is how the routing primitive's conclusion becomes an `IsFreePolygonalArc`. -/
lemma isFreePolygonalArc_of_subset_faceSet (D : Drawing G Plane) {z w : Plane}
    {Q : PolygonalPath z w} (F : D.Face) (hQ : Q.IsSimpleArcOrLoop)
    (hsub : Q.toSet \ {z, w} ⊆ D.faceSet F) : D.IsFreePolygonalArc Q where
  isSimpleArcOrLoop := hQ
  disjoint_support := (D.faceSet_disjoint_support F).mono_left hsub

/-- The relative interior of an edge lies on the frontier of a face.

*Open.* `StarLemma.lean` proves the corresponding statement for faces of `D.onePoint`. The missing
step is the correspondence between faces of `D` and `D.onePoint`. -/
theorem exists_face_frontier_superset_edgePath_interior [G.Finite] (D : PLDrawing G Plane)
    (e : E(G)) : ∃ F : D.Face, (D.edgePath e).Interior ⊆ frontier (D.faceSet F) := by
  sorry

/-- The ends of an edge are limits of interior points of its arc, so any closed set containing the
relative interior contains both ends. With `S := frontier (D.faceSet F)` this is the sentence
"`p u, p v ∈ frontier W`, since they lie in `closure Γ̊_e`" of Lemma 13.2(1). Nothing polygonal, and
nothing two-dimensional. -/
lemma vertex_mem_of_edgePath_interior_subset (D : Drawing G X) (e : E(G)) {S : Set X}
    (hS : IsClosed S) (hsub : (D.edgePath e).Interior ⊆ S) :
    D.vertex (edgeSource e) ∈ S ∧ D.vertex (edgeTarget e) ∈ S := by
  have hmem : ∀ t : I, D.edgePath e t ∈ S := by
    intro t
    refine hS.closure_subset (closure_mono hsub (image_closure_subset_closure_image
      (D.edgePath e).continuous ⟨t, ?_, rfl⟩))
    rw [unitInterval.closure_Ioo_zero_one]
    trivial
  exact ⟨by simpa using hmem 0, by simpa using hmem 1⟩

/-- Two points on the frontier of a face are joined by a polygonal arc whose relative interior lies
inside the face.

*Open, and the genuinely two-dimensional input here.* This is the routing lemma used by the edge
insertion construction. -/
theorem exists_freePolygonalArc_in_faceSet [G.Finite] (D : PLDrawing G Plane)
    (F : D.toDrawing.Face) {z w : Plane} (hz : z ∈ frontier (D.toDrawing.faceSet F))
    (hw : w ∈ frontier (D.toDrawing.faceSet F)) :
    ∃ Q : PolygonalPath z w, Q.IsSimpleArcOrLoop ∧ Q.toSet \ {z, w} ⊆ D.toDrawing.faceSet F := by
  sorry

/-- **Lemma 13.2(1), parallel edge.** If `e` joins `u` and `v`, a polygonal drawing admits a free
polygonal arc between the images of `u` and `v`: route it through a face incident with `e`.

This is the assembly of the three lemmas above, and it is proved. -/
theorem exists_isFreePolygonalArc_of_isLink [G.Finite] (D : PLDrawing G Plane) {e : β}
    (he : G.IsLink e u v) :
    ∃ Q : PolygonalPath (D.vertex ⟨u, he.left_mem⟩) (D.vertex ⟨v, he.right_mem⟩),
      D.toDrawing.IsFreePolygonalArc Q := by
  obtain ⟨F, hF⟩ := exists_face_frontier_superset_edgePath_interior D ⟨e, he.edge_mem⟩
  obtain ⟨hs, ht⟩ := vertex_mem_of_edgePath_interior_subset D.toDrawing ⟨e, he.edge_mem⟩
    isClosed_frontier hF
  have hends := (isLink_edgeSource_edgeTarget (⟨e, he.edge_mem⟩ : E(G))).isLink_iff_sym2_eq.mp he
  have huv : D.vertex ⟨u, he.left_mem⟩ ∈ frontier (D.toDrawing.faceSet F) ∧
      D.vertex ⟨v, he.right_mem⟩ ∈ frontier (D.toDrawing.faceSet F) := by
    obtain ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ := Sym2.eq_iff.mp hends
    · have e₁ : (⟨u, he.left_mem⟩ : V(G)) = edgeSource (⟨e, he.edge_mem⟩ : E(G)) :=
        Subtype.ext h₁.symm
      have e₂ : (⟨v, he.right_mem⟩ : V(G)) = edgeTarget (⟨e, he.edge_mem⟩ : E(G)) :=
        Subtype.ext h₂.symm
      exact ⟨by rw [e₁]; exact hs, by rw [e₂]; exact ht⟩
    · have e₁ : (⟨u, he.left_mem⟩ : V(G)) = edgeTarget (⟨e, he.edge_mem⟩ : E(G)) :=
        Subtype.ext h₂.symm
      have e₂ : (⟨v, he.right_mem⟩ : V(G)) = edgeSource (⟨e, he.edge_mem⟩ : E(G)) :=
        Subtype.ext h₁.symm
      exact ⟨by rw [e₁]; exact ht, by rw [e₂]; exact hs⟩
  obtain ⟨Q, hQ, hsub⟩ := exists_freePolygonalArc_in_faceSet D F huv.1 huv.2
  exact ⟨Q, isFreePolygonalArc_of_subset_faceSet D.toDrawing F hQ hsub⟩

/-- **Lemma 13.2(2), loop.** A polygonal drawing of a finite graph admits a free polygonal loop at
every vertex.

*Open.* Route, verbatim from Status.md: take `ρ := ρ_{p v}` from the star lemma 3.6; by 3.5,
`ball (p v) ρ ∖ supp D` is a union of open sectors (the whole punctured ball if `deg v = 0`). Fix
one, with angular interval `(θᵢ, θᵢ₊₁)`, choose `θᵢ < θ' < θ'' < θᵢ₊₁` with `θ'' − θ' < π` and
`0 < r < ρ`, and take the boundary of the triangle with vertices `p v`, `p v + r·e^{iθ'}`,
`p v + r·e^{iθ''}`. Every point of that triangle has argument in `[θ', θ'']` and radius `≤ r`, so it
lies in the closed sector and meets `supp D` only at `p v`. That triangle is a `PolygonalPath` with
equal ends, so `IsSimpleArcOrLoop` is its circle case — which is why `IsFreeArc` was never allowed
to demand `u ≠ v`. -/
theorem exists_isFreePolygonalArc_loop [G.Finite] (D : PLDrawing G Plane) (hu : u ∈ V(G)) :
    ∃ Q : PolygonalPath (D.vertex ⟨u, hu⟩) (D.vertex ⟨u, hu⟩),
      D.toDrawing.IsFreePolygonalArc Q := by
  sorry

/-- Lemma 13.2(1) in the form `Drawing.addEdge` consumes. -/
theorem exists_isFreeArc_of_isLink [G.Finite] (D : PLDrawing G Plane) {e : β}
    (he : G.IsLink e u v) :
    ∃ γ : Path (D.vertex ⟨u, he.left_mem⟩) (D.vertex ⟨v, he.right_mem⟩),
      D.toDrawing.IsFreeArc γ := by
  obtain ⟨Q, hQ⟩ := exists_isFreePolygonalArc_of_isLink D he
  exact ⟨Q.toPath, hQ.isFreeArc⟩

/-- Lemma 13.2(2) in the form `Drawing.addEdge` consumes. -/
theorem exists_isFreeArc_loop [G.Finite] (D : PLDrawing G Plane) (hu : u ∈ V(G)) :
    ∃ γ : Path (D.vertex ⟨u, hu⟩) (D.vertex ⟨u, hu⟩), D.toDrawing.IsFreeArc γ := by
  obtain ⟨Q, hQ⟩ := exists_isFreePolygonalArc_loop D hu
  exact ⟨Q.toPath, hQ.isFreeArc⟩

/-- Inserting an edge along a *polygonal* free arc keeps the drawing polygonal. This is what lets
Corollary 13.3 apply Lemma 13.2 again to the drawing it just produced, and it is the reason the two
existence lemmas above hand back a `PolygonalPath`.

*Open.* Route: `PLDrawing.ofCells` with `addEdgeVertex` for the vertices, the old cells transported
by `PolygonalPath.cast` exactly as in `PLDrawing.restrictCell`, and `Q` — reversed if `ArbRel`
disagrees, the polygonal analogue of `Path.reorient` — as the cell of `f`. Its four obligations are
the `toSet`-level forms of `addEdgeEdge_injOn`, `addEdgeEdge_interior_disjoint_vertex` and
`addEdgeEdge_interior_disjoint`, already discharged above at the `Path.Interior` level; the
translation between the two levels is `Path.interior_toPath`. -/
theorem isPL_addEdge [G.Finite] (D : PLDrawing G Plane) (hu : u ∈ V(G)) (hv : v ∈ V(G))
    (hf : f ∉ E(G)) {Q : PolygonalPath (D.vertex ⟨u, hu⟩) (D.vertex ⟨v, hv⟩)}
    (hQ : D.toDrawing.IsFreePolygonalArc Q) :
    (D.toDrawing.addEdge hu hv hf Q.toPath hQ.isFreeArc).IsPL := by
  sorry

/-- A free arc carries a drawing of any path graph with the same two ends: cut `[0,1]` at the
interior vertices of `P` and give each edge of `P` the corresponding subpath. Together with
`addPath` this inserts a *subdivided* edge, which is what a topological-minor argument needs.

*Open.* Route: induct on `P`, splitting `γ` with `Path.trans`/`Subpath` (`Mathlib.Topology.Subpath`,
which this file does not yet import). `IsFreeAttachment.agree` and `vertexSet_inter` are the
hypotheses `hint` and `hends` unchanged; `support_inter` is `hγ`, since the only points of
`range γ` on `D.support` are its two ends. Nothing here is two-dimensional — it is stated for an
arbitrary ambient space on purpose. -/
theorem exists_isFreeAttachment_of_isFreeArc (D : Drawing G X) {P : WList α β}
    (hP : P.toGraph.IsPath P) (hu : u ∈ V(G)) (hv : v ∈ V(G))
    (hends : P.first = u ∧ P.last = v) (hint : V(G) ∩ V(P.toGraph) = {P.first, P.last})
    (hE : Disjoint E(G) E(P.toGraph)) (γ : Path (D.vertex ⟨u, hu⟩) (D.vertex ⟨v, hv⟩))
    (hγ : D.IsFreeArc γ) :
    ∃ DP : Drawing P.toGraph X, D.IsFreeAttachment DP ∧ DP.support = range γ := by
  sorry

end Geometry

end Drawing

/-! ### Planarity

These corollaries choose a drawing, obtain a free arc, and apply the insertion combinator. The
edge and loop results start from `PLPlanar` because their geometric inputs are polygonal; path
insertion accepts an ordinary plane drawing.
-/

namespace PLPlanar

variable {e : β}

/-- Adding an edge parallel to an existing one keeps a finite graph planar. -/
theorem addEdge_of_isLink [G.Finite] (hG : G.PLPlanar) (he : G.IsLink e u v) (hf : f ∉ E(G)) :
    (G.addEdge f u v).Planar := by
  obtain ⟨D⟩ := hG
  obtain ⟨γ, hγ⟩ := Drawing.exists_isFreeArc_of_isLink D he
  exact ⟨D.toDrawing.addEdge he.left_mem he.right_mem hf γ hγ⟩

/-- Adding a loop keeps a finite graph planar. -/
theorem addLoop [G.Finite] (hG : G.PLPlanar) (hu : u ∈ V(G)) (hf : f ∉ E(G)) :
    (G.addEdge f u u).Planar := by
  obtain ⟨D⟩ := hG
  obtain ⟨γ, hγ⟩ := Drawing.exists_isFreeArc_loop D hu
  exact ⟨D.toDrawing.addEdge hu hu hf γ hγ⟩

end PLPlanar

namespace Planar

variable {e : β}

/-- Gluing a drawn path onto a drawing keeps the union planar. This is `Drawing.addPath` with the
drawings existentially quantified away. -/
theorem addPath_of_isFreeAttachment {P : WList α β} (D : Drawing G Plane)
    (DP : Drawing P.toGraph Plane) (h : D.IsFreeAttachment DP) : (G ∪ P.toGraph).Planar :=
  ⟨D.addPath DP h⟩

/-- Inserting a subdivided edge along a free arc of a plane drawing. -/
theorem addPath_of_isFreeArc {P : WList α β} (D : Drawing G Plane) (hP : P.toGraph.IsPath P)
    (hu : u ∈ V(G)) (hv : v ∈ V(G)) (hends : P.first = u ∧ P.last = v)
    (hint : V(G) ∩ V(P.toGraph) = {P.first, P.last}) (hE : Disjoint E(G) E(P.toGraph))
    (γ : Path (D.vertex ⟨u, hu⟩) (D.vertex ⟨v, hv⟩)) (hγ : D.IsFreeArc γ) :
    (G ∪ P.toGraph).Planar := by
  obtain ⟨DP, hattach, -⟩ :=
    Drawing.exists_isFreeAttachment_of_isFreeArc D hP hu hv hends hint hE γ hγ
  exact ⟨D.addPath DP hattach⟩

end Planar

end

end Graph
