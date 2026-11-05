module

public import Matroid.GraphTheory.GraphTopology.Map
public import Matroid.GraphTheory.GraphTopology.StraightLine

/-! # Affine transport of straight-line and polygonal graph-like spaces -/

@[expose] public section

open Set Function Topology

namespace GraphLike

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
  {G : GraphLike X}

/-- An affine map embedding the carrier preserves straight-line edges. -/
theorem map_isStraightLine (hG : G.IsStraightLine) (f : X →ᵃ[ℝ] Y)
    (hf : IsEmbedding (fun x : G.carrier ↦ f x.1)) : (G.map f hf).IsStraightLine := by
  intro e he x y hb
  rw [G.map_edgeSet f hf] at he
  obtain ⟨d, hd, rfl⟩ := he
  obtain ⟨a, _, b, _, hab, _⟩ := G.boundary_isPair hd
  rw [G.mapEdge_boundary f hf hd, hab, image_pair] at hb
  rw [hG hd hab, image_segment]
  rcases pair_eq_pair_iff.mp hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact segment_symm ℝ _ _

private def affinePath (f : X →ᵃ[ℝ] Y) :
    ∀ {x y : X}, PolygonalPath x y → PolygonalPath (f x) (f y)
  | _, _, .nil x => .nil (f x)
  | _, _, .cons x y P => .cons (f x) (f y) (affinePath f P)

variable [ContinuousAdd X] [ContinuousSMul ℝ X]
  [ContinuousAdd Y] [ContinuousSMul ℝ Y]

private theorem affinePath_apply (f : X →ᵃ[ℝ] Y) {x y : X} (P : PolygonalPath x y)
    (t : unitInterval) : (affinePath f P).toPath t = f (P.toPath t) := by
  induction P generalizing t with
  | nil x => rfl
  | cons x y P ih =>
    cases P with
    | nil => exact (f.apply_lineMap x y t).symm
    | cons y z P =>
      simp only [affinePath, PolygonalPath.toPath, Path.trans_apply]
      split_ifs
      · exact (f.apply_lineMap x y _).symm
      · exact ih _

private theorem affinePath_toSet (f : X →ᵃ[ℝ] Y) {x y : X} (P : PolygonalPath x y) :
    (affinePath f P).toSet = f '' P.toSet := by
  rw [PolygonalPath.toSet_eq_range_toPath, PolygonalPath.toSet_eq_range_toPath,
    ← range_comp]
  congr 1
  funext t
  exact affinePath_apply f P t

/-- Affine carrier embeddings preserve polygonal representatives, including loops. -/
theorem map_isPolygonal (hG : G.IsPolygonal) (f : X →ᵃ[ℝ] Y)
    (hf : IsEmbedding (fun x : G.carrier ↦ f x.1)) : (G.map f hf).IsPolygonal := by
  intro e he x y hb
  rw [G.map_edgeSet f hf] at he
  obtain ⟨d, hd, rfl⟩ := he
  obtain ⟨a, _, b, _, hab, _⟩ := G.boundary_isPair hd
  obtain ⟨P, hP, hrange⟩ := hG hd hab
  have hp : (affinePath f P).toPath.IsPrimitive := by
    intro s t hst
    rw [affinePath_apply, affinePath_apply] at hst
    apply hP
    apply G.map_injOn f hf _ _ hst <;>
      apply G.edge_subset hd <;> rw [← hrange, PolygonalPath.toSet_eq_range_toPath] <;>
      exact mem_range_self _
  have hr : (affinePath f P).toSet = f '' d := by
    rw [affinePath_toSet, hrange]
  rw [G.mapEdge_boundary f hf hd, hab, image_pair] at hb
  rcases pair_eq_pair_iff.mp hb with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨affinePath f P, hp, hr⟩
  · exact ⟨(affinePath f P).reverse, PolygonalPath.isPrimitive_reverse_iff.mpr hp,
      (PolygonalPath.toSet_reverse _).trans hr⟩

end GraphLike
