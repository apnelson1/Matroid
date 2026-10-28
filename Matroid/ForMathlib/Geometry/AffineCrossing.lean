module

public import Matroid.ForMathlib.Analysis.Convex.Segment
public import Matroid.ForMathlib.Topology.Crossing

/-! # Crossings of affine half-spaces

Open segments crossing an affine level supply boundary crossings. Finite segment covers
with relatively closed nonconstant generators have finitely many crossings at every level.
-/

@[expose] public section

open Set AffineMap

namespace AffineMap

section OrderedRing

variable {K V : Type*} [Ring K] [LinearOrder K] [IsStrictOrderedRing K]
  [DenselyOrdered K] [TopologicalSpace K] [OrderTopology K]
  [AddCommGroup V] [Module K V] [TopologicalSpace V]
  [ContinuousConstVAdd V V] [ContinuousSMul K V] {S : Set V}

/-- An interior point of a transverse open segment is a crossing of its affine level. -/
theorem mem_boundaryCrossings_preimage_Ioi_of_mem_openSegment
    (f : V →ᵃ[K] K) (hf : Continuous f) {a b p : V}
    (hseg : openSegment K a b ⊆ S) (hp : p ∈ openSegment K a b)
    (hab : f a ≠ f b) : p ∈ boundaryCrossings S (f ⁻¹' Ioi (f p)) := by
  have hpa : openSegment K p a ⊆ S := by
    rw [openSegment_symm] at hseg hp
    exact (openSegment_subset_openSegment_right_of_mem hp).trans hseg
  have hpb : openSegment K p b ⊆ S := (openSegment_subset_openSegment_right_of_mem hp).trans hseg
  have hfp : f p ∈ openSegment K (f a) (f b) := by
    rw [← image_openSegment K f]
    exact mem_image_of_mem f hp
  have hneg (q : V) (hq : openSegment K p q ⊆ S) (hqp : f q < f p) :
      p ∈ closure {r | r ∈ S ∧ f r < f p} := by
    have h := mem_closure_lt_of_openSegment_subset (-f) hq (neg_lt_neg hqp)
    change p ∈ closure {r | r ∈ S ∧ -f p < -f r} at h
    simpa only [neg_lt_neg_iff] using h
  have hsides : p ∈ closure (S ∩ f ⁻¹' Ioi (f p)) ∧
      p ∈ closure (S ∩ f ⁻¹' Iio (f p)) := by
    rcases lt_or_gt_of_ne hab with hab | hab
    · have hbetween := openSegment_subset_Ioo hab hfp
      exact ⟨mem_closure_lt_of_openSegment_subset f hpb hbetween.2, hneg a hpa hbetween.1⟩
    · rw [openSegment_symm] at hfp
      have hbetween := openSegment_subset_Ioo hab hfp
      exact ⟨mem_closure_lt_of_openSegment_subset f hpa hbetween.2, hneg b hpb hbetween.1⟩
  exact hf.mem_boundaryCrossings_preimage_Ioi_of_mem_closure (hseg hp) hsides.1 hsides.2

/-- A fibre covered locally by transverse open segments consists exactly of crossings. -/
theorem boundaryCrossings_eq_fiber_of_local_segments (f : V →ᵃ[K] K) (hf : Continuous f) {c : K}
    (hcover : ∀ p ∈ S, f p = c →
      ∃ a b, openSegment K a b ⊆ S ∧ p ∈ openSegment K a b ∧ f a ≠ f b) :
    boundaryCrossings S (f ⁻¹' Ioi c) = S ∩ f ⁻¹' {c} := by
  apply Subset.antisymm
  · intro p hp
    exact ⟨hp.1.1, (frontier_lt_subset_eq continuous_const hf hp.1.2).symm⟩
  rintro p ⟨hp, hpc⟩
  obtain ⟨a, b, hseg, hmid, hab⟩ := hcover p hp hpc
  simpa only [show f p = c from hpc] using
    f.mem_boundaryCrossings_preimage_Ioi_of_mem_openSegment hf hseg hmid hab

/-- A level avoiding all generator endpoint values consists exactly of crossings. -/
theorem boundaryCrossings_eq_fiber_of_regular_level (f : V →ᵃ[K] K) (hf : Continuous f)
    {E : Set (V × V)} (hpres : S = ⋃ e ∈ E, segment K e.1 e.2) {c : K}
    (hc : ∀ e ∈ E, f e.1 ≠ c ∧ f e.2 ≠ c) :
    boundaryCrossings S (f ⁻¹' Ioi c) = S ∩ f ⁻¹' {c} := by
  apply boundaryCrossings_eq_fiber_of_local_segments f hf
  intro p hpS hpc
  obtain ⟨e, he, hp⟩ := mem_iUnion₂.mp (hpres ▸ hpS)
  have hpa : p ≠ e.1 := fun h ↦ (hc e he).1 ((congrArg f h).symm.trans hpc)
  have hpb : p ≠ e.2 := fun h ↦ (hc e he).2 ((congrArg f h).symm.trans hpc)
  have hab : f e.1 ≠ f e.2 := by
    intro h
    have hfp := mem_image_of_mem f hp
    rw [image_segment K f, ← h, segment_same] at hfp
    exact (hc e he).1 (hfp.symm.trans hpc)
  refine ⟨e.1, e.2, ?_, mem_openSegment_of_ne_left_right hpa.symm hpb.symm hp, hab⟩
  intro q hq
  exact hpres ▸ mem_iUnion₂.mpr ⟨e, he, openSegment_subset_segment K _ _ hq⟩

end OrderedRing

/-- Every crossing lies on a nonconstant generator when these generators are relatively closed. -/
theorem boundaryCrossings_subset_nonconstant_generators {K V : Type*}
    [Ring K] [LinearOrder K] [IsStrictOrderedRing K] [TopologicalSpace K] [OrderTopology K]
    [AddCommGroup V] [Module K V] [TopologicalSpace V] {S : Set V} {E : Set (V × V)}
    (hE : E.Finite) (hcover : S ⊆ ⋃ e ∈ E, segment K e.1 e.2)
    (f : V →ᵃ[K] K) (hf : Continuous f)
    (hclosed : ∀ e ∈ E, f e.1 ≠ f e.2 →
      IsClosed ((↑) ⁻¹' segment K e.1 e.2 : Set S)) (c : K) :
    boundaryCrossings S (f ⁻¹' Ioi c) ⊆
      ⋃ e ∈ {e ∈ E | f e.1 ≠ f e.2}, segment K e.1 e.2 ∩ f ⁻¹' {c} := by
  intro q hq
  have hqc : f q = c := (frontier_lt_subset_eq continuous_const hf hq.1.2).symm
  have hcl : q ∈ closure (S ∩ f ⁻¹' Ioi c) := by
    simpa only [(isOpen_Ioi.preimage hf).interior_eq] using hq.2.1
  have hcl' : q ∈ closure (⋃ e ∈ E,
      (S ∩ segment K e.1 e.2) ∩ f ⁻¹' Ioi c) := by
    apply closure_mono _ hcl
    intro r hr
    obtain ⟨e, he, hre⟩ := mem_iUnion₂.mp (hcover hr.1)
    exact mem_iUnion₂.mpr ⟨e, he, ⟨hr.1, hre⟩, hr.2⟩
  rw [hE.closure_biUnion] at hcl'
  obtain ⟨e, he, hqe⟩ := mem_iUnion₂.mp hcl'
  have hab : f e.1 ≠ f e.2 := by
    intro hab
    have hconst : ∀ r ∈ segment K e.1 e.2, f r = f e.1 := by
      intro r hr
      have hr' := mem_image_of_mem f hr
      rw [image_segment K f, ← hab, segment_same] at hr'
      exact hr'
    have hqconst : f q = f e.1 :=
      (isClosed_singleton.preimage hf).closure_subset
        (closure_mono (show (S ∩ segment K e.1 e.2) ∩ f ⁻¹' Ioi c ⊆
          f ⁻¹' {f e.1} from fun r hr ↦ hconst r hr.1.2) hqe)
    have hempty : (S ∩ segment K e.1 e.2) ∩ f ⁻¹' Ioi c = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro r hr
      have hrc : f r = c := (hconst r hr.1.2).trans (hqconst.symm.trans hqc)
      exact lt_irrefl c (hrc ▸ hr.2)
    simp [hempty] at hqe
  have hseg : q ∈ segment K e.1 e.2 :=
    isClosed_preimage_val.mp (hclosed e he hab) ⟨hq.1.1,
      closure_mono inter_subset_left hqe⟩
  exact mem_iUnion₂.mpr ⟨e, ⟨he, hab⟩, hseg, hqc⟩

/-- Finite segment covers with relatively closed nonconstant generators have finite crossings. -/
theorem finite_boundaryCrossings_of_cover {K V : Type*}
    [Ring K] [LinearOrder K] [IsStrictOrderedRing K] [TopologicalSpace K] [OrderTopology K]
    [AddCommGroup V] [Module K V] [TopologicalSpace V] {S : Set V} {E : Set (V × V)}
    (hE : E.Finite) (hcover : S ⊆ ⋃ e ∈ E, segment K e.1 e.2)
    (f : V →ᵃ[K] K) (hf : Continuous f)
    (hclosed : ∀ e ∈ E, f e.1 ≠ f e.2 →
      IsClosed ((↑) ⁻¹' segment K e.1 e.2 : Set S)) (c : K) :
    (boundaryCrossings S (f ⁻¹' Ioi c)).Finite := by
  have hfinite : (⋃ e ∈ {e ∈ E | f e.1 ≠ f e.2},
      segment K e.1 e.2 ∩ f ⁻¹' {c}).Finite := by
    apply (hE.sep fun e ↦ f e.1 ≠ f e.2).biUnion
    intro e he
    exact (f.subsingleton_segment_fiber he.2 c).finite
  exact hfinite.subset (boundaryCrossings_subset_nonconstant_generators hE hcover f hf hclosed c)

end AffineMap
