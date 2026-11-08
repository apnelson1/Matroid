module

public import Matroid.ForMathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.Analysis.Convex.Between
public import Mathlib.Order.Interval.Set.Infinite

/-! # Affine fibres of segments and finite segment covers

The sufficient segment criteria need only a partial order on the scalar domain.
Endpoint membership is needed for the exact segment criteria. Over an ordered field,
nondegenerate segments are infinite and determine the exceptional fibre values of a
finite segment presentation.
-/

@[expose] public section

open Set AffineSubspace

namespace AffineMap

section OrderedRing

variable {K V W Q : Type*} [Ring K] [IsDomain K] [PartialOrder K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [Module.IsTorsionFree K W] [AddTorsor W Q]

omit [IsDomain K] in
private theorem exists_lineMap_of_mem_segment {a b p : V} (hp : p ∈ segment K a b) :
    ∃ t : K, AffineMap.lineMap a b t = p := by
  obtain ⟨s, t, -, -, hst, rfl⟩ := hp
  exact ⟨t, by rw [AffineMap.lineMap_apply_module, ← hst, add_sub_cancel_right]⟩

theorem injOn_segment (f : V →ᵃ[K] Q) {a b : V}
    (h : a = b ∨ f a ≠ f b) : InjOn f (segment K a b) := by
  apply ((f.injOn_affineSpan_pair_iff a b).mpr h).mono
  intro x hx
  exact mem_affineSpan_pair_iff_exists_lineMap_eq.mpr (exists_lineMap_of_mem_segment hx)

theorem subsingleton_segment_fiber (f : V →ᵃ[K] Q) {a b : V}
    (hab : f a ≠ f b) (c : Q) :
    (segment K a b ∩ f ⁻¹' {c}).Subsingleton := by
  intro p hp q hq
  exact f.injOn_segment (Or.inr hab) hp.1 hq.1 (hp.2.trans hq.2.symm)

theorem finite_fiber_of_cover {S : Set V} {E : Set (V × V)} (hE : E.Finite)
    (hcover : S ⊆ ⋃ e ∈ E, segment K e.1 e.2) (f : V →ᵃ[K] Q) (c : Q)
    (hf : ∀ e ∈ E, e.1 ≠ e.2 → f e.1 = c → f e.2 ≠ c) :
    (S ∩ f ⁻¹' {c}).Finite := by
  apply Set.Finite.subset (s := (⋃ e ∈ E, segment K e.1 e.2) ∩ f ⁻¹' {c})
  · rw [iUnion₂_inter]
    refine hE.biUnion fun e he ↦ ?_
    by_cases hab : e.1 = e.2
    · apply (finite_singleton e.2).subset
      rintro p ⟨⟨s, t, -, -, hst, rfl⟩, -⟩
      simp only [hab, ← add_smul, hst, one_smul, mem_singleton_iff]
    by_cases hsep : f e.1 ≠ f e.2
    · exact (subsingleton_segment_fiber f hsep c).finite
    have heq : f e.1 = f e.2 := not_ne_iff.mp hsep
    have hempty : segment K e.1 e.2 ∩ f ⁻¹' {c} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨t, ht⟩ := exists_lineMap_of_mem_segment hp.1
      have hfp : f p = f e.1 := by
        rw [← ht, f.apply_lineMap, ← heq, AffineMap.lineMap_same_apply]
      have hleft : f e.1 = c := hfp.symm.trans hp.2
      exact hf e he hab hleft (heq ▸ hleft)
    simp [hempty]
  · exact inter_subset_inter_left _ hcover

theorem infinite_fiber_iff_infinite_generator {S : Set V} {E : Set (V × V)}
    (hE : E.Finite) (hpres : S = ⋃ e ∈ E, segment K e.1 e.2)
    (f : V →ᵃ[K] Q) (c : Q) :
    (S ∩ f ⁻¹' {c}).Infinite ↔
      ∃ e ∈ E, (segment K e.1 e.2).Infinite ∧ f e.1 = c ∧ f e.2 = c := by
  constructor
  · intro hinf
    by_contra h
    push Not at h
    apply hinf
    rw [hpres, iUnion₂_inter]
    refine hE.biUnion fun e he ↦ ?_
    by_cases hseg : (segment K e.1 e.2).Finite
    · exact hseg.subset inter_subset_left
    apply finite_fiber_of_cover (E := {e}) (finite_singleton _) (by simp) f c
    rintro q rfl _ ha hb
    exact h q he hseg ha hb
  rintro ⟨e, he, hinf, ha, hb⟩ hfin
  apply hinf (hfin.subset ?_)
  intro p hp
  refine ⟨hpres ▸ mem_iUnion₂.mpr ⟨e, he, hp⟩, ?_⟩
  obtain ⟨t, rfl⟩ := exists_lineMap_of_mem_segment hp
  simp only [mem_preimage, mem_singleton_iff, f.apply_lineMap, ha, hb,
    AffineMap.lineMap_same_apply]

end OrderedRing

section Segments

variable {R V W P Q : Type*} [Ring R] [IsDomain R] [PartialOrder R] [ZeroLEOneClass R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  [Module.IsTorsionFree R W] [AddTorsor V P] [AddTorsor W Q]

theorem injOn_affineSegment_iff (f : P →ᵃ[R] Q) (a b : P) :
    InjOn f (affineSegment R a b) ↔ a = b ∨ f a ≠ f b := by
  constructor
  · intro h
    exact or_iff_not_imp_right.mpr fun hn ↦ h
      ⟨0, ⟨le_rfl, zero_le_one⟩, lineMap_apply_zero _ _⟩
      ⟨1, ⟨zero_le_one, le_rfl⟩, lineMap_apply_one _ _⟩ (not_not.mp hn)
  · intro h
    exact ((injOn_affineSpan_pair_iff f a b).mpr h).mono (affineSegment_subset_affineSpan R a b)

theorem injOn_segment_iff (f : V →ᵃ[R] Q) (a b : V) :
    InjOn f (segment R a b) ↔ a = b ∨ f a ≠ f b := by
  constructor
  · intro h
    exact or_iff_not_imp_right.mpr fun hn ↦
      h (left_mem_segment R a b) (right_mem_segment R a b) (not_not.mp hn)
  · exact f.injOn_segment

theorem subsingleton_segment_fiber_iff (f : V →ᵃ[R] Q) (a b : V) (c : Q) :
    (segment R a b ∩ f ⁻¹' {c}).Subsingleton ↔
      a = b ∨ f a ≠ f b ∨ f a ≠ c := by
  constructor
  · intro h
    by_cases hab : f a = f b
    · by_cases hac : f a = c
      · exact Or.inl (h ⟨left_mem_segment R a b, hac⟩
          ⟨right_mem_segment R a b, hab.symm.trans hac⟩)
      · exact Or.inr (Or.inr hac)
    · exact Or.inr (Or.inl hab)
  · intro h
    apply ((subsingleton_affineSpan_pair_fiber_iff f a b c).mpr h).anti
    apply inter_subset_inter_left
    intro x hx
    exact mem_affineSpan_pair_iff_exists_lineMap_eq.mpr (exists_lineMap_of_mem_segment hx)

end Segments

end AffineMap

section OrderedField

variable {K V W Q : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W] [AddTorsor W Q]

@[simp]
theorem finite_segment_iff {a b : V} : (segment K a b).Finite ↔ a = b := by
  constructor
  · intro h
    by_contra hab
    have hi := (Set.Icc_infinite (zero_lt_one : (0 : K) < 1)).image
      (AffineMap.lineMap_injective K hab).injOn
    rw [← segment_eq_image_lineMap] at hi
    exact hi h
  rintro rfl
  simp

namespace AffineMap

theorem infinite_fiber_iff_generator {S : Set V} {E : Set (V × V)} (hE : E.Finite)
    (hpres : S = ⋃ e ∈ E, segment K e.1 e.2) (f : V →ᵃ[K] Q) (c : Q) :
    (S ∩ f ⁻¹' {c}).Infinite ↔
      ∃ e ∈ E, e.1 ≠ e.2 ∧ f e.1 = c ∧ f e.2 = c := by
  rw [infinite_fiber_iff_infinite_generator hE hpres f c]
  simp only [Set.Infinite, finite_segment_iff]

theorem infinite_fiber_values_eq {S : Set V} {E : Set (V × V)} (hE : E.Finite)
    (hpres : S = ⋃ e ∈ E, segment K e.1 e.2) (f : V →ᵃ[K] Q) :
    {c | (S ∩ f ⁻¹' {c}).Infinite} =
      (fun e : V × V ↦ f e.1) '' {e ∈ E | e.1 ≠ e.2 ∧ f e.1 = f e.2} := by
  ext c
  rw [mem_ofPred, infinite_fiber_iff_generator hE hpres f]
  constructor
  · rintro ⟨e, he, hab, ha, hb⟩
    exact ⟨e, ⟨he, hab, ha.trans hb.symm⟩, ha⟩
  rintro ⟨e, ⟨he, hab, heq⟩, ha⟩
  exact ⟨e, he, hab, ha, heq ▸ ha⟩

end AffineMap

end OrderedField
