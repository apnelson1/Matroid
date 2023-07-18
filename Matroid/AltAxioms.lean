import Matroid.Basic
import Mathlib.Data.Set.Pairwise.Basic

open Set 

namespace Matroid

example (ι : Type _) (Xs : ι → Set α) (h : Pairwise (Disjoint on Xs)) (i j : ι) (hne : i ≠ j) : 
    i = j := by
  have : Disjoint (Xs i) (Xs j) := h hne 
  sorry

def matroid_of_indep_of_forall_subset_base (E : Set α) (Indep : Set α → Prop)
  (h_exists_maximal_indep_subset : ∀ X, X ⊆ E → ∃ I, I ∈ maximals (· ⊆ ·) {I | Indep I ∧ I ⊆ X})
  (h_subset : ∀ ⦃I J⦄, Indep J → I ⊆ J → Indep I)
  (h_basis : ∀ ⦃I I'⦄, Indep I → I' ∈ maximals (· ⊆ ·) {I | Indep I} →
    ∃ B, B ∈ maximals (· ⊆ ·) {I | Indep I} ∧ I ⊆ B ∧ B ⊆ I ∪ I')
  (h_support : ∀ I, Indep I → I ⊆ E) : Matroid α :=
  matroid_of_indep E Indep
  (by {
    obtain ⟨I, ⟨hI, -⟩⟩ := h_exists_maximal_indep_subset ∅ (empty_subset _)
    rw [←subset_empty_iff.mp hI.2]
    exact hI.1
  })
  (fun I J hI hIJ ↦ h_subset hI hIJ)
  (by {
    rintro I B hI h'I hB
    obtain ⟨B', hB'⟩ := h_basis hI hB
    obtain ⟨x, hx⟩ : ∃ x, x ∈ B' \ I := by {
      simp_rw [mem_diff]
      by_contra' h
      rw [←subset_def] at h
      have : I = B' := subset_antisymm (hB'.2.1) (h)
      subst this
      exact h'I hB'.1
    }
    have hxB : x ∈ B := by
      have := hB'.2.2 hx.1 
      rw [mem_union] at this
      rcases this with g | g
      . { exfalso
          exact hx.2 g }
      . { exact g }
    have : insert x I ⊆ B' := by
      rw [insert_eq, union_subset_iff, singleton_subset_iff]
      exact ⟨hx.1, hB'.2.1⟩
    exact ⟨x, ⟨hxB, hx.2⟩, h_subset hB'.1.1 this⟩
  })
  -- (h_maximal : ∀ X, X ⊆ E → ExistsMaximalSubsetProperty Indep X) 
  (by {
    let Base   : Set α → Prop := maximals (· ⊆ ·) { I | Indep I } 
    let Base'  : Set α → Prop := { B | Base (E \ B) }
    let Indep' : Set α → Prop := { I' | ∃ B', Base' B' ∧ I' ⊆ B' }

    have aux1 : ∀ I I', Indep' I ∧ (I' ∈ maximals (· ⊆ ·) { I' | Indep' I' }) →
                  ∃ B, B ∈ maximals (· ⊆ ·) {I' | Indep' I'} ∧ I ⊆ B ∧ B ⊆ I ∪ I' := by sorry

    have aux2 : ∀ X B, X ⊆ E → Base B →
      (B ∩ X ∈ maximals (· ⊆ ·) {I | Indep I ∧ I ⊆ X} ↔
       (E \ B) ∩ (E \ X) ∈ maximals (· ⊆ ·) {I' | Indep' I' ∧ I' ⊆ (E \ X)}) := by sorry


    -- (I3') holds for `Indep ∩ 2^X`
    have aux3 : ∀ X, X ⊆ E →
        (∀ I I', I ∈ {I | Indep I ∧ I ⊆ X } ∧ I' ∈ maximals (· ⊆ ·) {I | Indep I ∧ I ⊆ X } →
        ∃ B, B ∈ maximals (· ⊆ ·) {I | Indep I ∧ I ⊆ X } ∧ I ⊆ B ∧ B ⊆ I ∪ I') := by
      rintro X hX I I' ⟨hI, hI'⟩

      obtain ⟨Bh, hBh⟩ := h_exists_maximal_indep_subset E (by rfl)

      have : ∀ I, Indep I ∧ I ⊆ E ↔ Indep I := sorry
      simp_rw [this] at hBh
      obtain ⟨B', hB'⟩ := h_basis hI'.1.1 hBh

      have I'eq : I' = B' ∩ X := sorry
      rw [I'eq] at hI'
      have hB'c := (aux2 X B' hX hB'.1).mp hI'

      obtain ⟨B, hB⟩ := h_basis hI.1 hB'.1
      
      have h₁ : B ∩ (E \ X) ⊆ B' ∩ (E \ X) := sorry
      -- from `I ⊆ X`
      have h₂ : (E \ B') ∩ (E \ X) ⊆ (E \ B) ∩ (E \ X) := sorry
      -- from previous
      have h₃ : E \ B ∩ (E \ X) ∈ {I' | Indep' I' ∧ I' ⊆ E \ X} := sorry
      have hBc := hB'c
      rw [subset_antisymm h₂ (hB'c.2 h₃ h₂), ←aux2 X B hX hB.1] at hBc
      refine' ⟨B ∩ X, hBc, subset_inter_iff.mpr ⟨hB.2.1, hI.2⟩, _⟩
      . calc
          B ∩ X ⊆ (I ∪ B') ∩ X    := inter_subset_inter_left X hB.2.2
          _ = (I ∩ X) ∪ (B' ∩ X)  := inter_distrib_right _ _ _
          _ = I ∪ (B' ∩ X)        := by rw [inter_eq_self_of_subset_left hI.2]
          _ = I ∪ I'              := by rw [←I'eq]

    simp_rw [ExistsMaximalSubsetProperty]
    rintro X hX I hI hIX
    obtain ⟨I', hI'⟩ := h_exists_maximal_indep_subset X hX
    obtain ⟨B, hB⟩ := aux3 X hX I I' ⟨⟨hI, hIX⟩, hI'⟩
    exact ⟨B, ⟨hB.1.1.1, hB.2.1, hB.1.1.2⟩, fun Y hY hBY ↦ hB.1.2 ⟨hY.1, hY.2.2⟩ hBY⟩
  })
  h_support

-- -- -- Oxley's axiomatization (Axioms for infinite matroids, Theorem 5.2)
-- def oxley_indep (E : Set α) (Indep : Set α → Prop) :=
--   (∀ X, X ⊆ E → ∃ Y, Y ⊆ X ∧ Y ∈ maximals (· ⊆ ·) ({I | Indep I ∧ I ⊆ X})) ∧
--   (∀ I J, Indep J → I ⊆ J → Indep I) ∧
--   (∀ I I', Indep I → 
--       I' ∈ (maximals (· ⊆ ·) {I | Indep I}) 
--     → ∃ B, B ∈ maximals (· ⊆ ·) {I | Indep I} ∧ I ⊆ B ∧ B ⊆ I ∪ I') ∧
--   (∀ I, Indep I → I ⊆ E)

-- def matroid_of_indep_of_forall_subset_base (E : Set α) (Indep : Set α → Prop) (hcI : oxley_indep E Indep) : 
--   Matroid α :=
--   matroid_of_indep E Indep
--   (by {
--     obtain ⟨Y, ⟨hY, h⟩⟩ := hcI.1 ∅ (empty_subset _)
--     rw [subset_empty_iff] at hY
--     subst hY
--     exact h.1.1
--   })
--   (fun I J hI hIJ ↦ hcI.2.1 I J hI hIJ)
--   (by {
--     rintro I B hI h'I hB
--     obtain ⟨B', hB'⟩ := hcI.2.2.1 I B hI hB
--     have : ∃ x, x ∈ B' \ I := by {
--       simp_rw [mem_diff]
--       by_contra' h
--       rw [←subset_def] at h
--       have : I = B' := subset_antisymm (hB'.2.1) (h)
--       subst this
--       exact h'I hB'.1
--     }
--     obtain ⟨x, hx⟩ := this
--     use x
--     have : x ∈ B := by
--       have := hB'.2.2 hx.1 
--       rw [mem_union] at this
--       rcases this with g | g
--       . { exfalso
--           exact hx.2 g }
--       . { exact g }
--     use ⟨this, hx.2⟩
--     have : insert x I ⊆ B' := by
--       rw [insert_eq, union_subset_iff, singleton_subset_iff]
--       exact ⟨hx.1, hB'.2.1⟩
--     exact hcI.2.1 (insert x I) B' hB'.1.1 this 
--   })
--   (by {
--     rintro X hX
--     -- rw [ExistsMaximalSubsetProperty]
--     -- rintro I hI hIX
--     obtain ⟨Y, hY⟩ := hcI.1 X hX
--     have := hcI.2.2
    
--     rw [ExistsMaximalSubsetProperty]
--     sorry
--   })
--   (hcI.2.2.2)
  
-- def matroid_of_direct_sum' {ι : Type _} (Ms : ι → Matroid α)
--   -- (hEs : Pairwise (fun i ↦ (Ms i).E) i j => Disjoint i j) :
--   (hEs : ∀ i j, i ≠ j → Disjoint (Ms i).E (Ms j).E) :=
--   matroid_of_oxley
--   (⋃ i, (Ms i).E)
--   (fun I ↦ I ⊆ (⋃ i, (Ms i).E) ∧ ∀ i, (Ms i).Indep (I ∩ (Ms i).E))
--   (by {
--     sorry
--   })


end from_axioms

end Matroid 


/- Restrict a matroid to a set containing a known basis. This is a special case of restriction
  and only has auxiliary use -/
-- def bRestr (M : Matroid α) {B₀ R : Set α} (hB₀ : M.Base B₀) (hB₀R : B₀ ⊆ R) (hR : R ⊆ M.E) : 
--     Matroid α where
--   ground := R
--   Base B := M.Base B ∧ B ⊆ R
--   exists_base' := ⟨B₀, ⟨hB₀, hB₀R⟩⟩ 
--   base_exchange' := by
--     rintro B B' ⟨hB, hBR⟩ ⟨hB', hB'R⟩ e he
--     obtain ⟨f, hf⟩ := hB.exchange hB' he
--     refine' ⟨f, hf.1, hf.2, insert_subset (hB'R hf.1.1) ((diff_subset _ _).trans hBR)⟩    
--   maximality' := by
--     rintro X hXR Y ⟨B, ⟨hB, -⟩, hYB⟩ hYX
--     obtain ⟨J, ⟨⟨BJ, hBJ, hJBJ⟩, hJ⟩, hJmax⟩ := M.maximality' X (hXR.trans hR) Y ⟨B, hB, hYB⟩ hYX 
--     simp only [mem_setOf_eq, and_imp, forall_exists_index] at hJmax 
--     obtain ⟨BJ', hBJ', hJBJ'⟩ :=
--       (hBJ.indep.subset hJBJ).subset_basis_of_subset (subset_union_left _ B₀) 
--         (union_subset (hJ.2.trans (hXR.trans hR)) (hB₀R.trans hR))
--     have' hBJ'b := hB₀.base_of_basis_supset (subset_union_right _ _) hBJ'
--     refine' ⟨J, ⟨⟨BJ', ⟨hBJ'b, hBJ'.subset.trans (union_subset (hJ.2.trans hXR) hB₀R)⟩, hJBJ'⟩,hJ⟩, 
--       fun K ⟨⟨BK, ⟨hBK, _⟩, hKBK⟩, hYK, hKX⟩ hKJ ↦ hJmax BK hBK hKBK hYK hKX hKJ⟩
--   subset_ground' := by tauto

