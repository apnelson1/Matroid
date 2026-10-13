module

public import Matroid.Graph.Immersion.Basic
public import Matroid.Graph.Subdivision

/-!
# Topological immersions, topological minors, and subdivisions

`Immersion.Topological` and `Graph.IsoTopologicalMinor` impose the same conditions on the same
branch vertices and routes. The conversions below preserve those data, including their image.
The relation `Graph.IsTopologicalMinor` therefore agrees with `Graph.IsIsoTopologicalMinor`.
Adding `Immersion.Surjective` gives exactly the existing `Graph.IsoSubdivision` witnesses.
-/

@[expose] public section

namespace Graph

open Function Set WList Graph

variable {α β γ δ : Type*} {G : Graph α β} {J : Graph γ δ}

/-! ## Topological minors -/

namespace IsoTopologicalMinor

/-- Regard a topological-minor witness as an immersion with the same vertices and routes. -/
def toImmersion (M : J.IsoTopologicalMinor G) : Immersion J G where
  vertex :=
    { toFun := fun v ↦ ⟨M.branchVertex v, M.branchVertex_mem v⟩
      inj' := fun _ _ huv ↦ M.branchVertex.injective (congrArg Subtype.val huv) }
  route := M.route
  route_isTrail e := (M.route_isSimple e).elim IsPath.isTrail IsCyclicWalk.isTrail
  route_nonempty := M.route_nonempty
  route_ends := M.route_ends
  route_edge_disjoint := M.route_edge_disjoint

@[simp]
lemma toImmersion_vertex (M : J.IsoTopologicalMinor G) (v : V(J)) :
    (M.toImmersion.vertex v).1 = M.branchVertex v := rfl

@[simp]
lemma toImmersion_route (M : J.IsoTopologicalMinor G) (e : E(J)) :
    M.toImmersion.route e = M.route e := rfl

@[simp]
lemma toImmersion_topological (M : J.IsoTopologicalMinor G) : M.toImmersion.Topological :=
  ⟨M.route_internal_disjoint_branchVertices, M.route_isSimple, M.route_internal_disjoint⟩

@[simp]
lemma toImmersion_Image (M : J.IsoTopologicalMinor G) :
    M.toImmersion.Image = M.usedSubgraph := rfl

end IsoTopologicalMinor

namespace Immersion

/-- Package a topological immersion as a topological-minor witness without changing its routes. -/
def toIsoTopologicalMinor (M : Immersion J G) (hM : M.Topological) :
    J.IsoTopologicalMinor G where
  branchVertex :=
    { toFun := Subtype.val ∘ M.vertex
      inj' := fun _ _ huv ↦ M.vertex.injective (Subtype.ext huv) }
  branchVertex_mem v := (M.vertex v).prop
  route := M.route
  route_isSimple := hM.2.1
  route_nonempty := M.route_nonempty
  route_ends := M.route_ends
  route_internal_disjoint_branchVertices := hM.1
  route_internal_disjoint := hM.2.2
  route_edge_disjoint := M.route_edge_disjoint

@[simp]
lemma toIsoTopologicalMinor_branchVertex (M : Immersion J G) (hM : M.Topological) (v : V(J)) :
    (M.toIsoTopologicalMinor hM).branchVertex v = (M.vertex v).1 := rfl

@[simp]
lemma toIsoTopologicalMinor_route (M : Immersion J G) (hM : M.Topological) (e : E(J)) :
    (M.toIsoTopologicalMinor hM).route e = M.route e := rfl

@[simp]
lemma toIsoTopologicalMinor_toImmersion (M : Immersion J G) (hM : M.Topological) :
    (M.toIsoTopologicalMinor hM).toImmersion = M := rfl

@[simp]
lemma usedSubgraph_toIsoTopologicalMinor (M : Immersion J G) (hM : M.Topological) :
    (M.toIsoTopologicalMinor hM).usedSubgraph = M.Image := rfl

end Immersion

@[simp]
lemma IsoTopologicalMinor.toImmersion_toIsoTopologicalMinor
    (M : J.IsoTopologicalMinor G) :
    M.toImmersion.toIsoTopologicalMinor M.toImmersion_topological = M := rfl

/-- The trail-based topological-minor relation agrees with the existing heterogeneous relation. -/
theorem isIsoTopologicalMinor_iff_isTopologicalMinor :
    J.IsIsoTopologicalMinor G ↔ J.IsTopologicalMinor' G := by
  constructor
  · rintro ⟨M⟩
    exact ⟨M.toImmersion, M.toImmersion_topological⟩
  · rintro ⟨M, hM⟩
    exact ⟨M.toIsoTopologicalMinor hM⟩

/-! ## Subdivisions -/

namespace IsoSubdivision

/-- Regard a subdivision as an immersion with the same vertices and routes. -/
def toImmersion (S : J.IsoSubdivision G) : Immersion J G :=
  S.toIsoTopologicalMinor.toImmersion

@[simp]
lemma toImmersion_vertex (S : J.IsoSubdivision G) (v : V(J)) :
    (S.toImmersion.vertex v).1 = S.branchVertex v := rfl

@[simp]
lemma toImmersion_route (S : J.IsoSubdivision G) (e : E(J)) :
    S.toImmersion.route e = S.route e := rfl

@[simp]
lemma toImmersion_topological (S : J.IsoSubdivision G) : S.toImmersion.Topological :=
  S.toIsoTopologicalMinor.toImmersion_topological

@[simp]
lemma toImmersion_surjective (S : J.IsoSubdivision G) : S.toImmersion.Surjective :=
  S.toIsoTopologicalMinor.isExhaustive_iff_usedSubgraph_eq.mp S.exhaustive

end IsoSubdivision

namespace Immersion

/-- A surjective topological immersion gives a subdivision with the same vertices and routes. -/
def toIsoSubdivision (M : Immersion J G) (hM : M.Topological) (hSurj : M.Surjective) :
    J.IsoSubdivision G where
  toIsoTopologicalMinor := M.toIsoTopologicalMinor hM
  exhaustive := (M.toIsoTopologicalMinor hM).isExhaustive_iff_usedSubgraph_eq.mpr hSurj

@[simp]
lemma toIsoSubdivision_branchVertex (M : Immersion J G) (hM : M.Topological)
    (hSurj : M.Surjective) (v : V(J)) :
    (M.toIsoSubdivision hM hSurj).branchVertex v = (M.vertex v).1 := rfl

@[simp]
lemma toIsoSubdivision_route (M : Immersion J G) (hM : M.Topological)
    (hSurj : M.Surjective) (e : E(J)) :
    (M.toIsoSubdivision hM hSurj).route e = M.route e := rfl

@[simp]
lemma toIsoSubdivision_toImmersion (M : Immersion J G) (hM : M.Topological)
    (hSurj : M.Surjective) : (M.toIsoSubdivision hM hSurj).toImmersion = M := rfl

end Immersion

@[simp]
lemma IsoSubdivision.toImmersion_toIsoSubdivision (S : J.IsoSubdivision G) :
    S.toImmersion.toIsoSubdivision S.toImmersion_topological S.toImmersion_surjective = S := rfl

/-- Subdivisions are exactly surjective topological immersions. -/
theorem isIsoSubdivision_iff_exists_immersion : J.IsIsoSubdivision G ↔
    ∃ M : Immersion J G, M.Topological ∧ M.Surjective := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.toImmersion, S.toImmersion_topological, S.toImmersion_surjective⟩
  · rintro ⟨M, hM, hSurj⟩
    exact ⟨M.toIsoSubdivision hM hSurj⟩

end Graph
