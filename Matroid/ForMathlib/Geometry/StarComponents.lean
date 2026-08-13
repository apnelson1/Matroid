module

public import Matroid.ForMathlib.Geometry.DiskMinusRadii
public import Matroid.ForMathlib.Geometry.SegmentFigure
public import Matroid.ForMathlib.Topology.OnePoint

@[expose] public section

/-!
# Sectors of a star and components of the complement

If a set `S` meets a small closed ball at `p` in a star of straight radii, then the sectors of the
punctured disk are the local picture of the complement of `S`. This file relates them to the
*global* components of that complement on the sphere `OnePoint ℝ²`.

## Why this is here and not in `Planarity/`

The one statement below was `Graph.PLDrawing.exists_sector_subset_faceSet`, a private lemma about a
polygonal drawing. It never used the drawing: the star arrived as a set-level hypothesis, and the
conclusion was about `Drawing.faceSet`, which is by definition a connected component of the
complement of the support. Replacing the support by an arbitrary `S` and the face by
`connectedComponentIn` loses nothing and makes it available to callers with no graph — Status.md
3.9, whose θ-curve is three arcs and no drawing. See Kuratowski `Decisions.md` D14 and D16.

## Main statements

* `exists_sector_subset_connectedComponentIn` : a component whose frontier reaches inside the ball
  contains a whole sector.
-/

open Set Metric Topology Filter

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

variable {S : Set ℝ²} {p q : ℝ²} {ρ : ℝ} {Y : Finset ℝ²}

/-- **Sector extraction.** If the closed ball at `p` meets `S` in a star, then any connected
component of the complement of `S` on the sphere whose frontier reaches a point `q` of the open ball
contains the image of a whole sector of the punctured disk.

Stated for a general `q ∈ ball p ρ` rather than for `p` itself: two of the three call sites want
`q = p` and the third does not, and the argument never looks at which.

`hYne` is needed: with `Y = ∅` the "star" is the single point `p`, `diskMinusRadii p ρ ∅` is the
punctured disk, and the argument that `p` itself is not in the component breaks. -/
theorem exists_sector_subset_connectedComponentIn (hYne : Y.Nonempty)
    (hstar : closedBall p ρ ∩ S = {p} ∪ ⋃ y ∈ Y, segment ℝ p y)
    (hqball : q ∈ ball p ρ) {w : OnePoint ℝ²}
    (hq : (q : OnePoint ℝ²) ∈ frontier (connectedComponentIn ((↑) '' S)ᶜ w)) :
    ∃ C ∈ sectors p ρ Y, (↑) '' C ⊆ connectedComponentIn ((↑) '' S)ᶜ w := by
  set K : Set (OnePoint ℝ²) := connectedComponentIn ((↑) '' S)ᶜ w with hK
  have hKsub : K ⊆ ((↑) '' S)ᶜ := connectedComponentIn_subset _ _
  have hnhds : (↑) '' (ball p ρ) ∈ 𝓝 (q : OnePoint ℝ²) := by
    rw [OnePoint.nhds_coe_eq]
    exact Filter.image_mem_map (isOpen_ball.mem_nhds hqball)
  obtain ⟨z', ⟨hzU, hzF⟩⟩ :=
    mem_closure_iff_nhds.mp (frontier_subset_closure hq) ((↑) '' ball p ρ) hnhds
  obtain ⟨z, hzball, rfl⟩ := hzU
  have hzS : z ∉ S := fun hz ↦ hKsub hzF ⟨z, hz, rfl⟩
  have hzD : z ∈ diskMinusRadii p ρ Y := by
    refine ⟨hzball, fun hzrad ↦ hzS ?_⟩
    have hzsup : z ∈ closedBall p ρ ∩ S := by
      rw [hstar]
      exact Or.inr (by simpa [mem_iUnion] using hzrad)
    exact hzsup.2
  refine ⟨connectedComponentIn (diskMinusRadii p ρ Y) z, ⟨z, hzD, rfl⟩, ?_⟩
  have hCsub := connectedComponentIn_subset (diskMinusRadii p ρ Y) z
  have hconn : IsConnected
      ((↑) '' connectedComponentIn (diskMinusRadii p ρ Y) z : Set (OnePoint ℝ²)) :=
    (isConnected_connectedComponentIn_iff.mpr hzD).image _ OnePoint.continuous_coe.continuousOn
  have himg : ((↑) '' connectedComponentIn (diskMinusRadii p ρ Y) z : Set (OnePoint ℝ²)) ⊆
      ((↑) '' S : Set (OnePoint ℝ²))ᶜ := by
    rintro _ ⟨w0, hw0, rfl⟩
    have hw0D := hCsub hw0
    have hw0S : w0 ∉ S := by
      intro hwS
      have hw0mem : w0 ∈ closedBall p ρ ∩ S := ⟨ball_subset_closedBall hw0D.1, hwS⟩
      rw [hstar] at hw0mem
      obtain rfl | hwY := hw0mem
      · exact hw0D.2 (by
          obtain ⟨y, hy⟩ := hYne
          exact mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨hy, left_mem_segment _ _ _⟩⟩)
      exact hw0D.2 (by simpa [mem_iUnion] using hwY)
    exact fun ⟨w1, hw1, heq⟩ ↦ hw0S (OnePoint.coe_injective heq ▸ hw1)
  have hz_mem : (z : OnePoint ℝ²) ∈ (↑) '' connectedComponentIn (diskMinusRadii p ρ Y) z :=
    ⟨z, mem_connectedComponentIn hzD, rfl⟩
  rw [hK, connectedComponentIn_eq hzF]
  exact hconn.isPreconnected.subset_connectedComponentIn hz_mem himg

end
