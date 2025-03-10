import Mathlib.Data.Matrix.Rank

open Set
variable {X Y F : Type*} [Field F] [Fintype X] [Fintype Y]

lemma Matrix.exists_submatrix_span_rows (A : Matrix X Y F) : ∃ r : Fin A.rank → X, 
    Submodule.span F (range (A.submatrix r id)) = Submodule.span F (range A) := by 
  classical
  set t := LinearIndepOn.extend (K := F) (s := ∅) (t := range A) (by simp) (by simp) with ht
  have htA : t ⊆ range A := LinearIndepOn.extend_subset ..
  obtain ⟨s', hs't⟩ := subset_range_iff_exists_image_eq.1 htA
  obtain ⟨s, hs, hinj⟩ := exists_image_eq_and_injOn (s := s') (f := A)
  -- rw [hs't, ht] at hs
  have hsp : Submodule.span F (A '' s) = Submodule.span F (range A) := by
    rw [hs, hs't, ht]
    apply LinearIndepOn.span_extend_eq_span
  rw [← hsp]
  apply_fun Module.finrank F at hsp
  have hli : LinearIndepOn F A s := by
    sorry
  
  have hb := Basis.span hli.linearIndependent
  
  have hcard := Module.finrank_eq_card_basis (R := F) hb
  -- rw [← toFinset_card] at hcard
  have foo : Module.finrank F ↥(Submodule.span F (A '' s)) = s.toFinset.card := by
    rw [hsp, toFinset_card, ← hcard]
    congr
    · ext
      convert Iff.rfl
      simp 

    
     
  simp at hcard 

  rw [← Matrix.rank_eq_finrank_span_row] at hcard
  -- rw [← Matrix.rank_eq_finrank_span_row, finrank_span_set_eq_card, toFinset_image,
  --   Finset.card_image_of_injOn (by simpa)] at hsp


lemma Matrix.exists_submatrix_rank (A : Matrix X Y F) :
    ∃ r : Fin A.rank → X, (A.submatrix r id).rank = A.rank := by
  classical
  -- simp only [Matrix.rank_eq_finrank_span_row]
  set t := LinearIndepOn.extend (K := F) (s := ∅) (t := range A) (by simp) (by simp) with ht
  have htA : t ⊆ range A := LinearIndepOn.extend_subset ..
  obtain ⟨s', hs't⟩ := subset_range_iff_exists_image_eq.1 htA
  obtain ⟨s, hs, hinj⟩ := exists_image_eq_and_injOn (s := s') (f := A)
  -- rw [hs't, ht] at hs
  have hsp : Submodule.span F (A '' s) = Submodule.span F (range A) := by
    rw [hs, hs't, ht]
    apply LinearIndepOn.span_extend_eq_span
  apply_fun Module.finrank F at hsp

  -- have hrank := congr_arg (Module.finrank F ·) hsp
  rw [← Matrix.rank_eq_finrank_span_row, finrank_span_set_eq_card, toFinset_image,
    Finset.card_image_of_injOn (by simpa)] at hsp
  -- rw [← hsp]
  -- have hrank : A.rank =
  have hli : LinearIndepOn F A (s.toFinset) := by
    sorry
  have hb := Basis.span hli.linearIndependent
  have hcard := Module.finrank_eq_card_finset_basis (R := F) hb
  rw [← Matrix.rank_eq_finrank_span_row] at hcard


  -- have hcard : s.toFinset.card = Module.finrank F (Submodule.span F (range A)) := by
  --   have := LinearIndependent.ca
  set φ := Finset.eq  uivFinOfCardEq hsp
  use fun x ↦ (φ.symm x).1
  convert hcard





  sorry
