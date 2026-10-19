module

public import Matroid.ForMathlib.Analysis.Convex.Segment

/-!
# Segment figures

A segment figure is a finite union of closed real segments. Degenerate segments include
isolated points, and the empty family represents the empty set. The predicate records the
underlying set, without choosing a presentation. No topology on the ambient space is required.

The basic operations are finite unions, intersections, and affine images. `induction_on`
allows arguments by adjoining one segment, without repeatedly unpacking a presentation.
-/

@[expose] public section

open Set

variable {V W ι : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W] {S T : Set V}
  {Sι : ι → Set V}

/-- A finite union of closed real segments, allowing degenerate segments. -/
def IsSegmentFigure (S : Set V) : Prop :=
  ∃ E : Set (V × V), E.Finite ∧ S = ⋃ e ∈ E, segment ℝ e.1 e.2

@[simp, grind .]
theorem isSegmentFigure_empty : IsSegmentFigure (∅ : Set V) :=
  ⟨∅, finite_empty, by simp⟩

@[grind .]
theorem isSegmentFigure_segment (a b : V) : IsSegmentFigure (segment ℝ a b) :=
  ⟨{(a, b)}, finite_singleton _, by simp⟩

@[simp, grind .]
theorem isSegmentFigure_singleton (a : V) : IsSegmentFigure ({a} : Set V) := by
  simpa using isSegmentFigure_segment a a

namespace IsSegmentFigure

@[grind .]
theorem union (hS : IsSegmentFigure S) (hT : IsSegmentFigure T) : IsSegmentFigure (S ∪ T) := by
  obtain ⟨E, hE, rfl⟩ := hS
  obtain ⟨F, hF, rfl⟩ := hT
  exact ⟨E ∪ F, hE.union hF, by rw [biUnion_union]⟩

/-- Induction by adjoining a closed segment to a segment figure. -/
@[elab_as_elim]
theorem induction_on {P : Set V → Prop} (empty : P ∅) (hS : IsSegmentFigure S)
    (adjoin : ∀ a b T, IsSegmentFigure T → P T → P (segment ℝ a b ∪ T)) : P S := by
  obtain ⟨E, hE, rfl⟩ := hS
  induction E, hE using Set.Finite.induction_on with
  | empty => simpa using empty
  | @insert e E he hE ih =>
    simpa only [biUnion_insert] using adjoin e.1 e.2 _ ⟨E, hE, rfl⟩ ih

@[grind .]
theorem iUnion [Finite ι] (hS : ∀ i, IsSegmentFigure (Sι i)) : IsSegmentFigure (⋃ i, Sι i) := by
  choose E hE he using hS
  refine ⟨⋃ i, E i, finite_iUnion hE, ?_⟩
  simp_rw [he, biUnion_iUnion]

theorem biUnion {I : Set ι} (hI : I.Finite) (hS : ∀ i ∈ I, IsSegmentFigure (Sι i)) :
    IsSegmentFigure (⋃ i ∈ I, Sι i) := by
  have := hI.to_subtype
  simpa only [iUnion_subtype] using iUnion (fun i : I ↦ hS i i.2)

@[grind .]
theorem of_finite (hS : S.Finite) : IsSegmentFigure S := by
  simpa using biUnion hS (fun a _ ↦ isSegmentFigure_singleton a)

theorem insert (hS : IsSegmentFigure S) (a : V) : IsSegmentFigure (insert a S) := by
  simpa using (isSegmentFigure_singleton a).union hS

/-- Intersections are reduced to intersections of the finitely many generating segments. -/
@[grind .]
theorem inter (hS : IsSegmentFigure S) (hT : IsSegmentFigure T) : IsSegmentFigure (S ∩ T) := by
  refine hS.induction_on (by simp) fun a b S _ ih ↦ ?_
  rw [union_inter_distrib_right]
  refine union (hT.induction_on (by simp) fun c d T _ ih ↦ ?_) ih
  rw [inter_union_distrib_left]
  refine union ?_ ih
  obtain h | h := (segment ℝ a b ∩ segment ℝ c d).eq_empty_or_nonempty
  · exact h ▸ isSegmentFigure_empty
  obtain ⟨p, q, hpq⟩ := segment_inter_segment_eq_segment_of_nonempty h
  exact hpq ▸ isSegmentFigure_segment p q

/-- Intersecting finitely many figures inside another figure also allows an empty index set. -/
theorem inter_biInter (hS : IsSegmentFigure S) {I : Set ι} (hI : I.Finite)
    (hSι : ∀ i ∈ I, IsSegmentFigure (Sι i)) : IsSegmentFigure (S ∩ ⋂ i ∈ I, Sι i) := by
  induction I, hI using Set.Finite.induction_on with
  | empty => simpa using hS
  | @insert i I hi hI ih =>
    rw [biInter_insert, inter_left_comm]
    exact (hSι i (by simp)).inter (ih fun j hj ↦ hSι j (by simp [hj]))

theorem iInter [Finite ι] [Nonempty ι] (hSι : ∀ i, IsSegmentFigure (Sι i)) :
    IsSegmentFigure (⋂ i, Sι i) := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  simpa only [biInter_univ, inter_eq_right.mpr (iInter_subset Sι i)] using
    (hSι i).inter_biInter (finite_univ : (univ : Set ι).Finite) (fun j _ ↦ hSι j)

/-- No continuity or injectivity is required of an affine image. -/
theorem image (hS : IsSegmentFigure S) (f : V →ᵃ[ℝ] W) : IsSegmentFigure (f '' S) := by
  refine hS.induction_on (by simp) fun a b S _ ih ↦ ?_
  rw [image_union, image_segment]
  exact (isSegmentFigure_segment _ _).union ih

/-- A figure has a finite subset with exactly the same convex hull. -/
theorem exists_finite_convexHull_eq (hS : IsSegmentFigure S) :
    ∃ F : Set V, F.Finite ∧ F ⊆ S ∧ convexHull ℝ F = convexHull ℝ S := by
  refine hS.induction_on ⟨∅, finite_empty, Subset.rfl, rfl⟩ fun a b S _ ⟨F, hF, hFS, hFh⟩ ↦ ?_
  use {a, b} ∪ F, ((finite_singleton b).insert a).union hF, union_subset_union ?_ hFS, ?_
  · simp [insert_subset_iff, left_mem_segment, right_mem_segment]
  refine (convexHull_mono <| union_subset_union ?_ hFS).antisymm ?_
  · simp [insert_subset_iff, left_mem_segment, right_mem_segment]
  refine convexHull_min ?_ (convex_convexHull ..)
  refine union_subset ?_ <| (subset_convexHull ℝ S).trans (hFh ▸ convexHull_mono subset_union_right)
  exact (convex_convexHull ℝ _).segment_subset
    (subset_convexHull ℝ _ (Or.inl (Or.inl rfl))) (subset_convexHull ℝ _ (Or.inl (Or.inr rfl)))

end IsSegmentFigure

end
