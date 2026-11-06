module

public import Matroid.GraphTheory.Graph.Immersion.Basic
public import Matroid.GraphTheory.Graph.Subdivision

/-!
# Topological immersions, topological minors, and subdivisions

`Immersion.Topological` and `Graph.TopologicalMinor` impose the same conditions on the same
branch vertices and routes. The conversions below preserve those data, including their image.
The relation `Graph.IsTopologicalMinor` therefore agrees with `Graph.IsTopologicalMinor`.
Adding `Immersion.Surjective` gives exactly the existing `Graph.Subdivision` witnesses.
-/

@[expose] public section

namespace Graph

open Function Set WList Graph

variable {α β γ δ : Type*} {G : Graph α β} {J : Graph γ δ}

/-! ## Topological minors -/

namespace TopologicalMinor

/-- Regard a topological-minor witness as an immersion with the same vertices and routes. -/
def toImmersion (M : J.TopologicalMinor G) : Immersion J G where
  vertex :=
    { toFun := fun v ↦ ⟨M.branchVertex v, M.branchVertex_mem v⟩
      inj' := fun _ _ huv ↦ M.branchVertex.injective (congrArg Subtype.val huv) }
  route := M.route
  route_isTrail e := (M.route_isSimple e).elim IsPath.isTrail IsCyclicWalk.isTrail
  route_nonempty := M.route_nonempty
  route_ends := M.route_ends
  route_edge_disjoint := M.route_edge_disjoint

@[simp]
lemma toImmersion_vertex (M : J.TopologicalMinor G) (v : V(J)) :
    (M.toImmersion.vertex v).1 = M.branchVertex v := rfl

@[simp]
lemma toImmersion_route (M : J.TopologicalMinor G) (e : E(J)) :
    M.toImmersion.route e = M.route e := rfl

@[simp]
lemma toImmersion_topological (M : J.TopologicalMinor G) : M.toImmersion.Topological :=
  ⟨M.route_internal_disjoint_branchVertices, M.route_isSimple, M.route_internal_disjoint⟩

@[simp]
lemma toImmersion_Image (M : J.TopologicalMinor G) :
    M.toImmersion.Image = M.usedSubgraph := rfl

end TopologicalMinor

namespace Immersion

/-- Package a topological immersion as a topological-minor witness without changing its routes. -/
def toTopologicalMinor (M : Immersion J G) (hM : M.Topological) :
    J.TopologicalMinor G where
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
lemma toTopologicalMinor_branchVertex (M : Immersion J G) (hM : M.Topological) (v : V(J)) :
    (M.toTopologicalMinor hM).branchVertex v = (M.vertex v).1 := rfl

@[simp]
lemma toTopologicalMinor_route (M : Immersion J G) (hM : M.Topological) (e : E(J)) :
    (M.toTopologicalMinor hM).route e = M.route e := rfl

@[simp]
lemma toTopologicalMinor_toImmersion (M : Immersion J G) (hM : M.Topological) :
    (M.toTopologicalMinor hM).toImmersion = M := rfl

@[simp]
lemma usedSubgraph_toTopologicalMinor (M : Immersion J G) (hM : M.Topological) :
    (M.toTopologicalMinor hM).usedSubgraph = M.Image := rfl

end Immersion

@[simp]
lemma TopologicalMinor.toImmersion_toTopologicalMinor
    (M : J.TopologicalMinor G) :
    M.toImmersion.toTopologicalMinor M.toImmersion_topological = M := rfl

/-- The trail-based topological-minor relation agrees with the existing heterogeneous relation. -/
theorem isTopologicalMinor_iff_isTopologicalMinor :
    J.IsTopologicalMinor G ↔ J.IsTopologicalMinor' G := by
  constructor
  · rintro ⟨M⟩
    exact ⟨M.toImmersion, M.toImmersion_topological⟩
  · rintro ⟨M, hM⟩
    exact ⟨M.toTopologicalMinor hM⟩

/-! ## Subdivisions -/

namespace Subdivision

/-- Regard a subdivision as an immersion with the same vertices and routes. -/
def toImmersion (S : J.Subdivision G) : Immersion J G :=
  S.toTopologicalMinor.toImmersion

@[simp]
lemma toImmersion_vertex (S : J.Subdivision G) (v : V(J)) :
    (S.toImmersion.vertex v).1 = S.branchVertex v := rfl

@[simp]
lemma toImmersion_route (S : J.Subdivision G) (e : E(J)) :
    S.toImmersion.route e = S.route e := rfl

@[simp]
lemma toImmersion_topological (S : J.Subdivision G) : S.toImmersion.Topological :=
  S.toTopologicalMinor.toImmersion_topological

@[simp]
lemma toImmersion_surjective (S : J.Subdivision G) : S.toImmersion.Surjective :=
  S.toTopologicalMinor.isExhaustive_iff_usedSubgraph_eq.mp S.exhaustive

end Subdivision

namespace Immersion

/-- A surjective topological immersion gives a subdivision with the same vertices and routes. -/
def toSubdivision (M : Immersion J G) (hM : M.Topological) (hSurj : M.Surjective) :
    J.Subdivision G where
  toTopologicalMinor := M.toTopologicalMinor hM
  exhaustive := (M.toTopologicalMinor hM).isExhaustive_iff_usedSubgraph_eq.mpr hSurj

@[simp]
lemma toSubdivision_branchVertex (M : Immersion J G) (hM : M.Topological)
    (hSurj : M.Surjective) (v : V(J)) :
    (M.toSubdivision hM hSurj).branchVertex v = (M.vertex v).1 := rfl

@[simp]
lemma toSubdivision_route (M : Immersion J G) (hM : M.Topological)
    (hSurj : M.Surjective) (e : E(J)) :
    (M.toSubdivision hM hSurj).route e = M.route e := rfl

@[simp]
lemma toSubdivision_toImmersion (M : Immersion J G) (hM : M.Topological)
    (hSurj : M.Surjective) : (M.toSubdivision hM hSurj).toImmersion = M := rfl

end Immersion

@[simp]
lemma Subdivision.toImmersion_toSubdivision (S : J.Subdivision G) :
    S.toImmersion.toSubdivision S.toImmersion_topological S.toImmersion_surjective = S := rfl

/-- Subdivisions are exactly surjective topological immersions. -/
theorem isSubdivision_iff_exists_immersion : J.IsSubdivision G ↔
    ∃ M : Immersion J G, M.Topological ∧ M.Surjective := by
  constructor
  · rintro ⟨S⟩
    exact ⟨S.toImmersion, S.toImmersion_topological, S.toImmersion_surjective⟩
  · rintro ⟨M, hM, hSurj⟩
    exact ⟨M.toSubdivision hM hSurj⟩

end Graph
