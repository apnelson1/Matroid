import Matroid.Dual 

/-!
# Duality
-/

open Set

namespace Matroid

variable {α : Type _} {M : Matroid α}
section restrict

/-- Change the ground set of a matroid to some `R : Set α`. The independent sets of the restriction 
  are the independent subsets of the new ground set. Most commonly used when `R ⊆ M.E`   -/
def Restrict (M : Matroid α) (X : Set α) : Matroid α :=
  matroid_of_indep X (fun I ↦ M.Indep I ∧ I ⊆ X) ⟨M.empty_indep, empty_subset _⟩
    ( fun I J h hIJ ↦ ⟨h.1.subset hIJ, hIJ.trans h.2⟩ )
    ( by
        rintro I I' ⟨hI, hIY⟩ (hIn : ¬ M.Basis' I X) (hI' : M.Basis' I' X)
        rw [basis'_iff_basis_inter_ground] at hIn hI'
        obtain ⟨B', hB', rfl⟩ := hI'.exists_base
        obtain ⟨B, hB, hIB, hBIB'⟩ := hI.exists_base_subset_union_base hB'
        rw [hB'.inter_basis_iff_compl_inter_basis_dual, diff_inter_diff] at hI'

        have hss : M.E \ (B' ∪ (X ∩ M.E)) ⊆ M.E \ (B ∪ (X ∩ M.E))
        · apply diff_subset_diff_right
          rw [union_subset_iff, and_iff_left (subset_union_right _ _), union_comm]
          exact hBIB'.trans (union_subset_union_left _ (subset_inter hIY hI.subset_ground))

        have hi : M﹡.Indep (M.E \ (B ∪ (X ∩ M.E)))
        · rw [dual_indep_iff_exists]
          exact ⟨B, hB, disjoint_of_subset_right (subset_union_left _ _) disjoint_sdiff_left⟩

        have h_eq := hI'.eq_of_subset_indep hi hss 
          (diff_subset_diff_right (subset_union_right _ _))
        rw [h_eq, ←diff_inter_diff, ←hB.inter_basis_iff_compl_inter_basis_dual] at hI'

    
        obtain ⟨J, hJ, hIJ⟩ := hI.subset_basis_of_subset 
          (subset_inter hIB (subset_inter hIY hI.subset_ground))
        
        obtain rfl := hI'.indep.eq_of_basis hJ

        have hIJ' : I ⊂ B ∩ (X ∩ M.E) := hIJ.ssubset_of_ne (fun he ↦ hIn (by rwa [he]))

        obtain ⟨e, he⟩ := exists_of_ssubset hIJ'
        exact ⟨e, ⟨⟨(hBIB' he.1.1).elim (fun h ↦ (he.2 h).elim) id,he.1.2⟩, he.2⟩, 
          hI'.indep.subset (insert_subset he.1 hIJ), insert_subset he.1.2.1 hIY⟩ ) 
    ( by
        rintro A hAX I ⟨hI, _⟩ hIA
        obtain ⟨J, hJ, hIJ⟩ := hI.subset_basis'_of_subset hIA; use J
        rw [mem_maximals_setOf_iff, and_iff_left hJ.subset, and_iff_left hIJ, 
          and_iff_right ⟨hJ.indep, hJ.subset.trans hAX⟩]
        exact fun K ⟨⟨hK, _⟩, _, hKA⟩ hJK ↦ hJ.eq_of_subset_indep hK hJK hKA )
    ( by tauto )
    
variable {R R₁ R₂ : Set α}

class MRestrict (α β : Type _) := (restrict : α → β → α)

infixl:65  " ↾ " => MRestrict.restrict

instance {α : Type _} : MRestrict (Matroid α) (Set α) := ⟨fun M X ↦ M.Restrict X⟩  

@[simp] theorem restrict_indep_iff : (M ↾ R).Indep I ↔ M.Indep I ∧ I ⊆ R := by
  change (M.Restrict R).Indep I ↔ _; simp [Restrict]
  
theorem Indep.indep_restrict_of_subset (h : M.Indep I) (hIR : I ⊆ R) : (M ↾ R).Indep I := 
  restrict_indep_iff.mpr ⟨h,hIR⟩

@[simp] theorem restrict_ground_eq : (M ↾ R).E = R := rfl 

theorem restrict_finite {R : Set α} (hR : R.Finite) : (M ↾ R).Finite := 
  ⟨hR⟩  

@[simp] theorem restrict_dep_iff : (M ↾ R).Dep X ↔ ¬ M.Indep X ∧ X ⊆ R := by
  rw [Dep, restrict_indep_iff, restrict_ground_eq]; tauto

@[simp] theorem restrict_ground_eq_self (M : Matroid α) : (M ↾ M.E) = M := by
  refine' eq_of_indep_iff_indep_forall rfl _; aesop
  
theorem restrict_restrict_eq (M : Matroid α) (hR : R₂ ⊆ R₁) : (M ↾ R₁) ↾ R₂ = M ↾ R₂ := by
  refine' eq_of_indep_iff_indep_forall rfl _
  simp only [restrict_ground_eq, restrict_indep_iff, and_congr_left_iff, and_iff_left_iff_imp]
  exact fun _ h _ _ ↦ h.trans hR
  
theorem Indep.of_restrict (h : (M ↾ R).Indep I) : M.Indep I :=
  (restrict_indep_iff.mp h).1

@[simp] theorem base_restrict_iff (hX : X ⊆ M.E := by aesop_mat) :
    (M ↾ X).Base I ↔ M.Basis I X := by
  simp_rw [base_iff_maximal_indep, basis_iff', restrict_indep_iff, and_iff_left hX, and_assoc]
  aesop

theorem base_restrict_iff' : (M ↾ X).Base I ↔ M.Basis' I X := by
  simp_rw [Basis', base_iff_maximal_indep, mem_maximals_setOf_iff, restrict_indep_iff]

theorem Basis.restrict_base (h : M.Basis I X) : (M ↾ X).Base I := by
  rw [basis_iff'] at h
  simp_rw [base_iff_maximal_indep, restrict_indep_iff, and_imp, and_assoc, and_iff_right h.1.1, 
    and_iff_right h.1.2.1] 
  exact fun J hJ hJX hIJ ↦ h.1.2.2 _ hJ hIJ hJX
 
instance restrict_finiteRk [M.FiniteRk] : (M ↾ R).FiniteRk := 
  let ⟨_, hB⟩ := (M ↾ R).exists_base
  hB.finiteRk_of_finite (hB.indep.of_restrict.finite)

instance restrict_finitary [Finitary M] (R : Set α) : Finitary (M ↾ R) := by 
  refine ⟨fun I hI ↦ ?_⟩ 
  simp only [restrict_indep_iff] at *
  rw [indep_iff_forall_finite_subset_indep]
  exact ⟨fun J hJ hJfin ↦ (hI J hJ hJfin).1, 
    fun e heI ↦ singleton_subset_iff.1 (hI _ (by simpa) (toFinite _)).2⟩ 

@[simp] theorem Basis.base_restrict (h : M.Basis I X) : (M ↾ X).Base I := 
  (base_restrict_iff h.subset_ground).mpr h

theorem Basis.basis_restrict_of_subset (hI : M.Basis I X) (hXY : X ⊆ Y) : (M ↾ Y).Basis I X := by
  rwa [←base_restrict_iff, M.restrict_restrict_eq hXY, base_restrict_iff]

theorem basis'_restrict_iff : (M ↾ R).Basis' I X ↔ M.Basis' I (X ∩ R) ∧ I ⊆ R := by 
  simp_rw [Basis', mem_maximals_setOf_iff, restrict_indep_iff, subset_inter_iff, and_imp]; tauto

theorem basis_restrict_iff' : (M ↾ R).Basis I X ↔ M.Basis I (X ∩ M.E) ∧ X ⊆ R := by 
  rw [basis_iff_basis'_subset_ground, basis'_restrict_iff, restrict_ground_eq, and_congr_left_iff, 
    ← basis'_iff_basis_inter_ground]
  intro hXR
  rw [inter_eq_self_of_subset_left hXR, and_iff_left_iff_imp]
  exact fun h ↦ h.subset.trans hXR
  
theorem basis_restrict_iff (hR : R ⊆ M.E := by aesop_mat) :
    (M ↾ R).Basis I X ↔ M.Basis I X ∧ X ⊆ R := by
  rw [basis_restrict_iff', and_congr_left_iff]
  intro hXR
  rw [←basis'_iff_basis_inter_ground, basis'_iff_basis]  

theorem restrict_eq_restrict_iff (M M' : Matroid α) (X : Set α) : 
    M ↾ X = M' ↾ X ↔ ∀ I, I ⊆ X → (M.Indep I ↔ M'.Indep I) := by 
  refine' ⟨fun h I hIX ↦ _, fun h ↦ eq_of_indep_iff_indep_forall rfl fun I (hI : I ⊆ X) ↦ _⟩
  · rw [←and_iff_left (a := (M.Indep I)) hIX, ←and_iff_left (a := (M'.Indep I)) hIX, 
      ←restrict_indep_iff, h, restrict_indep_iff]
  rw [restrict_indep_iff, and_iff_left hI, restrict_indep_iff, and_iff_left hI, h _ hI]

@[simp] theorem restrict_eq_self_iff : M ↾ R = M ↔ R = M.E :=
  ⟨fun h ↦ by rw [←h]; rfl, fun h ↦ by simp [h]⟩
  
def Restriction (N M : Matroid α) : Prop := M ↾ N.E = N ∧ N.E ⊆ M.E

def StrictRestriction (N M : Matroid α) : Prop := M ↾ N.E = N ∧ N.E ⊂ M.E

infix:20  " ≤r " => Restriction
infix:20  " <r " => StrictRestriction

theorem Restriction.eq_restrict (h : N ≤r M) : M ↾ N.E = N :=
  h.1

theorem Restriction.subset (h : N ≤r M) : N.E ⊆ M.E := 
  h.2

theorem Restriction.exists_eq_restrict (h : N ≤r M) : ∃ R, R ⊆ M.E ∧ N = M ↾ R := by
  rw [←h.eq_restrict]; exact ⟨N.E, h.subset, rfl⟩ 

theorem StrictRestriction.restriction (h : N <r M) : N ≤r M :=
  ⟨h.1, h.2.subset⟩ 

theorem StrictRestriction.ssubset (h : N <r M) : N.E ⊂ M.E := 
  h.2

theorem StrictRestriction.ne (h : N <r M) : N ≠ M := by 
  rintro rfl; exact h.ssubset.ne rfl

theorem StrictRestriction.eq_restrict (h : N <r M) : M ↾ N.E = N := 
  h.restriction.eq_restrict

theorem StrictRestriction.exists_eq_restrict (h : N <r M) : ∃ R, R ⊂ M.E ∧ N = M ↾ R :=
  ⟨N.E, h.ssubset, by rw [h.eq_restrict]⟩ 
  
theorem restrict_restriction (M : Matroid α) (R : Set α) (hR : R ⊆ M.E := by aesop_mat) : 
    M ↾ R ≤r M := by
  rw [Restriction, restrict_ground_eq, and_iff_left hR]

theorem restriction_iff_exists : (N ≤r M) ↔ ∃ R, R ⊆ M.E ∧ N = M ↾ R := by
  use Restriction.exists_eq_restrict; rintro ⟨R, hR, rfl⟩; exact restrict_restriction M R hR 

theorem StrictRestriction.Ne (h : N <r M) : N ≠ M := by
  rintro rfl; exact h.2.ne rfl

theorem Restriction.strictRestriction_of_ne (h : N ≤r M) (hne : N ≠ M) : N <r M := by
  obtain ⟨R, hR, rfl⟩ := h.exists_eq_restrict
  exact ⟨h.eq_restrict, hR.ssubset_of_ne (fun h ↦ hne (by rw [h, restrict_ground_eq_self]))⟩

instance Restriction.trans : IsTrans (Matroid α) (· ≤r ·) := 
  ⟨fun M₁ M₂ M₃ h₁ h₂ ↦ by 
  { rw [restriction_iff_exists] at *
    obtain ⟨R₁, hR₁, rfl⟩ := h₁ 
    obtain ⟨R₂, hR₂, rfl⟩ := h₂ 
    exact ⟨R₁, hR₁.trans hR₂, restrict_restrict_eq _ hR₁⟩ } ⟩ 

instance Restriction.refl : IsRefl (Matroid α) (· ≤r ·) := 
  ⟨fun M ↦ ⟨M.restrict_ground_eq_self, rfl.subset⟩⟩   

instance Restriction.antisymm : IsAntisymm (Matroid α) (· ≤r ·) :=
  ⟨fun M M' ⟨h₁,h₂⟩ ⟨_,h₂'⟩ ↦ by rw [←h₁, h₂.antisymm h₂', restrict_ground_eq_self]⟩ 

instance : IsNonstrictStrictOrder (Matroid α) (· ≤r ·) (· <r ·) where
  right_iff_left_not_left := fun M M' ↦ 
    ⟨fun h ↦ ⟨h.restriction, fun h' ↦ h.ne (antisymm h.restriction h')⟩, 
     fun h ↦ h.1.strictRestriction_of_ne (by rintro rfl; exact h.2 (refl M))⟩  

end restrict


section Basis

-- These lemmas are awkward positioned here, because they look like they belong in `Basic`, but
-- their proofs depend on the definition of restriction (and hence duality. Maybe refactoring 
-- the proofs isn't too bad. 

theorem Basis.transfer (hIX : M.Basis I X) (hJX : M.Basis J X) (hXY : X ⊆ Y) (hJY : M.Basis J Y) :
    M.Basis I Y := by
  rw [←base_restrict_iff]; rw [← base_restrict_iff] at hJY
  exact hJY.base_of_basis_superset hJX.subset (hIX.basis_restrict_of_subset hXY)

theorem Basis.basis_of_basis_of_subset_of_subset (hI : M.Basis I X) (hJ : M.Basis J Y) (hJX : J ⊆ X) 
    (hIY : I ⊆ Y) : M.Basis I Y := by
  have hI' := hI.basis_subset (subset_inter hI.subset hIY) (inter_subset_left _ _)
  have hJ' := hJ.basis_subset (subset_inter hJX hJ.subset) (inter_subset_right _ _)
  exact hI'.transfer hJ' (inter_subset_right _ _) hJ
  
  
  -- exact hI'.transfer hJ' (inter_subset_right _ _) hJ

-- theorem Basis.transfer'' (hI : M.Basis I X) (hJ : M.Basis J Y) (hJX : J ⊆ X) :
--     M.Basis I (I ∪ Y) := by
--   obtain ⟨J', hJ', hJJ'⟩ := hJ.indep.subset_basis_of_subset hJX
--   have hJ'Y := (hJ.basis_union_of_subset hJ'.indep hJJ').basis_union hJ'
--   refine' (hI.transfer' hJ'Y hJ'.subset _).basis_subset _ _
--   · exact subset_union_of_subset_right hI.subset _
--   · exact subset_union_left _ _
--   refine' union_subset (subset_union_of_subset_right hI.subset _) _
--   rw [union_right_comm]
--   exact subset_union_right _ _

theorem Indep.exists_basis_subset_union_basis (hI : M.Indep I) (hIX : I ⊆ X) (hJ : M.Basis J X) :
    ∃ I', M.Basis I' X ∧ I ⊆ I' ∧ I' ⊆ I ∪ J := by
  obtain ⟨I', hI', hII', hI'IJ⟩ :=
    (hI.indep_restrict_of_subset hIX).exists_base_subset_union_base (Basis.base_restrict hJ)
  rw [base_restrict_iff] at hI'
  exact ⟨I', hI', hII', hI'IJ⟩

theorem Indep.exists_insert_of_not_basis (hI : M.Indep I) (hIX : I ⊆ X) (hI' : ¬M.Basis I X)
    (hJ : M.Basis J X) : ∃ e ∈ J \ I, M.Indep (insert e I) := by
  rw [← base_restrict_iff] at hI' ; rw [← base_restrict_iff] at hJ 
  obtain ⟨e, he, hi⟩ := (hI.indep_restrict_of_subset hIX).exists_insert_of_not_base hI' hJ
  exact ⟨e, he, (restrict_indep_iff.mp hi).1⟩

theorem Basis.base_of_base_subset (hIX : M.Basis I X) (hB : M.Base B) (hBX : B ⊆ X) : M.Base I :=
  hB.base_of_basis_superset hBX hIX

theorem Basis.exchange (hIX : M.Basis I X) (hJX : M.Basis J X) (he : e ∈ I \ J) :
    ∃ f ∈ J \ I, M.Basis (insert f (I \ {e})) X := by
  obtain ⟨y,hy, h⟩ := hIX.restrict_base.exchange hJX.restrict_base he
  exact ⟨y, hy, by rwa [base_restrict_iff] at h⟩ 
  
theorem Basis.eq_exchange_of_diff_eq_singleton (hI : M.Basis I X) (hJ : M.Basis J X)
    (hIJ : I \ J = {e}) : ∃ f ∈ J \ I, J = insert f I \ {e} := by
  rw [← base_restrict_iff] at hI hJ ; exact hI.eq_exchange_of_diff_eq_singleton hJ hIJ

theorem Basis'.card_eq_card (hI : M.Basis' I X) (hJ : M.Basis' J X) : I.encard = J.encard := by
  rw [←base_restrict_iff'] at hI hJ; exact hI.encard_eq_encard_of_base hJ
  
theorem Basis.card_eq_card (hI : M.Basis I X) (hJ : M.Basis J X) : I.encard = J.encard :=
  hI.basis'.card_eq_card hJ.basis'

theorem Indep.augment (hI : M.Indep I) (hJ : M.Indep J) (hIJ : I.encard < J.encard) : 
    ∃ e ∈ J \ I, M.Indep (insert e I) := by
  by_contra' he
  have hb : M.Basis I (I ∪ J)
  · simp_rw [hI.basis_iff_forall_insert_dep (subset_union_left _ _), union_diff_left, mem_diff, 
      and_imp, dep_iff, insert_subset_iff, and_iff_left hI.subset_ground]
    exact fun e heJ heI ↦ ⟨he e ⟨heJ, heI⟩, hJ.subset_ground heJ⟩ 
  obtain ⟨J', hJ', hJJ'⟩ := hJ.subset_basis_of_subset (subset_union_right I J)
  rw [←hJ'.card_eq_card hb] at hIJ
  exact hIJ.not_le (encard_mono hJJ')


end Basis

end Matroid