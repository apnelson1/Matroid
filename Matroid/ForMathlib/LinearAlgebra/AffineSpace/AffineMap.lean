module

public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # Affine maps on lines and escape along affine functionals -/

@[expose] public section

open Set AffineSubspace

namespace AffineMap

section Lines

variable {R V W P Q : Type*} [Ring R] [IsDomain R]
  [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  [Module.IsTorsionFree R W] [AddTorsor V P] [AddTorsor W Q]

private theorem injOn_line (f : P →ᵃ[R] Q) {a b : P} (hab : f a ≠ f b) :
    InjOn f (affineSpan R {a, b} : Set P) := by
  rintro x hx y hy hxy
  obtain ⟨s, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hx
  obtain ⟨t, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hy
  refine congrArg _ <| lineMap_injective R hab ?_
  rwa [← f.apply_lineMap, ← f.apply_lineMap]

theorem injOn_affineSpan_pair_iff (f : P →ᵃ[R] Q) (a b : P) :
    InjOn f (affineSpan R {a, b} : Set P) ↔ a = b ∨ f a ≠ f b := by
  constructor
  · intro h
    exact or_iff_not_imp_right.mpr fun hn ↦
      h (left_mem_affineSpan_pair R a b) (right_mem_affineSpan_pair R a b) (not_not.mp hn)
  · rintro (rfl | hab)
    · simp
    · exact injOn_line f hab

theorem subsingleton_affineSpan_pair_fiber_iff (f : P →ᵃ[R] Q) (a b : P) (c : Q) :
    ((affineSpan R {a, b} : Set P) ∩ f ⁻¹' {c}).Subsingleton ↔
      a = b ∨ f a ≠ f b ∨ f a ≠ c := by
  constructor
  · intro h
    by_cases hab : f a = f b
    · by_cases hac : f a = c
      · exact Or.inl (h ⟨left_mem_affineSpan_pair R a b, hac⟩
          ⟨right_mem_affineSpan_pair R a b, hab.symm.trans hac⟩)
      · exact Or.inr (Or.inr hac)
    · exact Or.inr (Or.inl hab)
  · rintro (rfl | hab | hac)
    · simpa using (subsingleton_singleton (a := a)).anti
        (inter_subset_left : ({a} : Set P) ∩ f ⁻¹' {c} ⊆ {a})
    · exact fun _ hx _ hy ↦ injOn_line f hab hx.1 hy.1 (hx.2.trans hy.2.symm)
    · by_cases hab : f a = f b
      · intro x hx
        obtain ⟨s, rfl⟩ := mem_affineSpan_pair_iff_exists_lineMap_eq.mp hx.1
        have hxc := hx.2
        simp only [mem_preimage, Set.mem_singleton_iff, f.apply_lineMap, ← hab,
          lineMap_same_apply] at hxc
        exact (hac hxc).elim
      · exact fun _ hx _ hy ↦ injOn_line f hab hx.1 hy.1 (hx.2.trans hy.2.symm)

end Lines

section Affine

variable {𝕜 V P : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [AddTorsor V P]

theorem exists_ray_avoiding_of_bddAbove (f : P →ᵃ[𝕜] 𝕜) {S : Set P} {v : V}
    (hf : f.linear ≠ 0) (hv : 0 ≤ f.linear v) (hS : BddAbove (f '' S)) :
    ∃ z ∉ S, ∀ t : 𝕜, 0 ≤ t → t • v +ᵥ z ∉ S := by
  obtain ⟨B, hB⟩ := hS
  have hw : ∃ w, f.linear w ≠ 0 := by
    by_contra! h
    apply hf
    ext w
    exact h w
  obtain ⟨w, hw⟩ := hw
  obtain ⟨p⟩ := (inferInstance : Nonempty P)
  let z := ((B + 1 - f p) / f.linear w) • w +ᵥ p
  have hz : f z = B + 1 := by
    simp only [z, f.map_vadd, map_smul, smul_eq_mul, vadd_eq_add]
    rw [div_mul_cancel₀ _ hw]
    ring
  have htail : ∀ t : 𝕜, 0 ≤ t → t • v +ᵥ z ∉ S := by
    intro t ht hmem
    have hbound := hB (mem_image_of_mem f hmem)
    rw [f.map_vadd, map_smul, smul_eq_mul, vadd_eq_add, hz] at hbound
    have := mul_nonneg ht hv
    linarith
  exact ⟨z, by simpa using htail 0 le_rfl, htail⟩

theorem bddAbove_preimage_line_of_pos (f : P →ᵃ[𝕜] 𝕜) {S : Set P} {v : V}
    (hv : 0 < f.linear v) (hS : BddAbove (f '' S)) (z : P) :
    BddAbove ((fun t : 𝕜 ↦ t • v +ᵥ z) ⁻¹' S) := by
  obtain ⟨B, hB⟩ := hS
  refine ⟨(B - f z) / f.linear v, fun t ht ↦ ?_⟩
  have hbound := hB (mem_image_of_mem f ht)
  rw [f.map_vadd, map_smul, smul_eq_mul, vadd_eq_add] at hbound
  rw [le_div_iff₀ hv]
  linarith

end Affine

end AffineMap
