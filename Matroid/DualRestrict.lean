import Matroid.Basic 

open Set

namespace Matroid

variable {α : Type _} {M : Matroid α}

section dual 

def dual (M : Matroid α) : Matroid α := 
  matroid_of_indep M.E (fun I ↦ I ⊆ M.E ∧ ∃ B, M.Base B ∧ Disjoint I B) 
⟨empty_subset M.E, M.exists_base.imp (fun B hB ↦ ⟨hB, empty_disjoint _⟩)⟩ 
( by { 
    rintro I J ⟨hJE, B, hB, hJB⟩ hIJ
    exact ⟨hIJ.trans hJE, ⟨B, hB, disjoint_of_subset_left hIJ hJB⟩⟩ } )
( by { 
    rintro I X ⟨hIE, B, hB, hIB⟩ hI_not_max hX_max
    have hXE := hX_max.1.1
    have hB' := (base_compl_iff_mem_maximals_disjoint_base hXE).mpr hX_max
    
    set B' := M.E \ X with hX
    have hI := (not_iff_not.mpr (base_compl_iff_mem_maximals_disjoint_base)).mpr hI_not_max
    obtain ⟨B'', hB'', hB''₁, hB''₂⟩ := (hB'.indep.diff I).exists_base_subset_union_base hB 
    rw [←compl_subset_compl, ←hIB.sdiff_eq_right, ←union_diff_distrib, diff_eq, compl_inter, 
      compl_compl, union_subset_iff, compl_subset_compl] at hB''₂ 
    
    have hssu := (subset_inter (hB''₂.2) hIE).ssubset_of_ne 
      (by { rintro rfl; apply hI; convert hB''; simp [hB''.subset_ground] })
  
    obtain ⟨e, ⟨(heB'' : e ∉ _), heE⟩, heI⟩ := exists_of_ssubset hssu
    use e
    simp_rw [mem_diff, insert_subset_iff, and_iff_left heI, and_iff_right heE, and_iff_right hIE]
    refine' ⟨by_contra (fun heX ↦ heB'' (hB''₁ ⟨_, heI⟩)), ⟨B'', hB'', _⟩⟩ 
    · rw [hX]; exact ⟨heE, heX⟩
    rw [←union_singleton, disjoint_union_left, disjoint_singleton_left, and_iff_left heB'']
    exact disjoint_of_subset_left hB''₂.2 disjoint_compl_left } ) 
( by {
    rintro X - I'⟨hI'E, B, hB, hI'B⟩ hI'X
    obtain ⟨I, hI⟩ :=  M.exists_basis (M.E \ X)
    obtain ⟨B', hB', hIB', hB'IB⟩ := hI.indep.exists_base_subset_union_base hB
    refine' ⟨(X \ B') ∩ M.E, 
      ⟨_,subset_inter (subset_diff.mpr _) hI'E, (inter_subset_left _ _).trans (diff_subset _ _)⟩, _⟩ 
    · simp only [inter_subset_right, true_and]
      exact ⟨B', hB', disjoint_of_subset_left (inter_subset_left _ _) disjoint_sdiff_left⟩
    · rw [and_iff_right hI'X]
      refine' disjoint_of_subset_right hB'IB _ 
      rw [disjoint_union_right, and_iff_left hI'B]
      exact disjoint_of_subset hI'X hI.subset disjoint_sdiff_right
    simp only [mem_setOf_eq, subset_inter_iff, and_imp, forall_exists_index]
    intros J hJE B'' hB'' hdj _ hJX hssJ
    rw [and_iff_left hJE]
    rw [diff_eq, inter_right_comm, ←diff_eq, diff_subset_iff] at hssJ
  
    have hI' : (B'' ∩ X) ∪ (B' \ X) ⊆ B'
    · rw [union_subset_iff, and_iff_left (diff_subset _ _),
      ←inter_eq_self_of_subset_left hB''.subset_ground, inter_right_comm, inter_assoc]
      
      calc _ ⊆ _ := inter_subset_inter_right _ hssJ 
           _ ⊆ _ := by rw [inter_distrib_left, hdj.symm.inter_eq, union_empty] 
           _ ⊆ _ := inter_subset_right _ _
    
    obtain ⟨B₁,hB₁,hI'B₁,hB₁I⟩ := (hB'.indep.subset hI').exists_base_subset_union_base hB''
    rw [union_comm, ←union_assoc, union_eq_self_of_subset_right (inter_subset_left _ _)] at hB₁I
    
    have : B₁ = B'
    · refine' hB₁.eq_of_subset_indep hB'.indep (fun e he ↦ _)
      refine' (hB₁I he).elim (fun heB'' ↦ _) (fun h ↦ h.1)
      refine' (em (e ∈ X)).elim (fun heX ↦ hI' (Or.inl ⟨heB'', heX⟩)) (fun heX ↦ hIB' _)
      refine' hI.mem_of_insert_indep ⟨hB₁.subset_ground he, heX⟩ 
        (hB₁.indep.subset (insert_subset he _))
      refine' (subset_union_of_subset_right (subset_diff.mpr ⟨hIB',_⟩) _).trans hI'B₁
      refine' disjoint_of_subset_left hI.subset disjoint_sdiff_left 

    subst this 

    refine' subset_diff.mpr ⟨hJX, by_contra (fun hne ↦ _)⟩
    obtain ⟨e, heJ, heB'⟩ := not_disjoint_iff.mp hne
    obtain (heB'' | ⟨-,heX⟩ ) := hB₁I heB'
    · exact hdj.ne_of_mem heJ heB'' rfl
    exact heX (hJX heJ) } ) 
( by tauto )  

/-- A notation typeclass for matroid duality, denoted by the `﹡` symbol. (This is distinct from the 
  usual `*` symbol for multiplication, due to precedence issues. )-/
class Mdual (β : Type _) := (dual : β → β)

postfix:max "﹡" => Mdual.dual

instance Matroid_Mdual {α : Type _} : Mdual (Matroid α) := ⟨Matroid.dual⟩ 

theorem dual_indep_iff_exists' : (M﹡.Indep I) ↔ I ⊆ M.E ∧ (∃ B, M.Base B ∧ Disjoint I B) := 
  by simp [Mdual.dual, dual]

@[simp] theorem dual_ground : M﹡.E = M.E := rfl 

@[aesop unsafe 10% (rule_sets [Matroid])]
theorem subset_dual_ground_of_subset_ground (hX : X ⊆ M.E) : X ⊆ M﹡.E :=
  hX 

@[aesop unsafe 10% (rule_sets [Matroid])]
theorem subset_ground_of_subset_dual_ground (hX : X ⊆ M﹡.E) : X ⊆ M.E :=
  hX 

@[simp] theorem dual_indep_iff_exists (hI : I ⊆ M.E := by aesop_mat) : 
  (M﹡.Indep I) ↔ (∃ B, M.Base B ∧ Disjoint I B) := 
by rw [dual_indep_iff_exists', and_iff_right hI]

theorem dual_dep_iff_forall : (M﹡.Dep I) ↔ (∀ B, M.Base B → (I ∩ B).Nonempty) ∧ I ⊆ M.E := 
  by simp_rw [dep_iff, dual_indep_iff_exists', dual_ground, and_congr_left_iff, not_and, 
    not_exists, not_and, not_disjoint_iff_nonempty_inter, imp_iff_right_iff, iff_true_intro Or.inl]
  
instance dual_finite [M.Finite] : M﹡.Finite := 
  ⟨M.ground_finite⟩  

theorem subset_ground_dual (hX : X ⊆ M.E := by aesop_mat) : X ⊆ M﹡.E := 
  hX 

@[simp] theorem dual_base_iff (hB : B ⊆ M.E := by aesop_mat) : M﹡.Base B ↔ M.Base (M.E \ B) := by
  rw [base_compl_iff_mem_maximals_disjoint_base, base_iff_maximal_indep, dual_indep_iff_exists', 
    mem_maximals_setOf_iff]
  simp [dual_indep_iff_exists']

theorem dual_base_iff' : M﹡.Base B ↔ M.Base (M.E \ B) ∧ B ⊆ M.E :=
  (em (B ⊆ M.E)).elim (fun h ↦ by rw [dual_base_iff, and_iff_left h]) 
    (fun h ↦ iff_of_false (h ∘ (fun h' ↦ h'.subset_ground)) (h ∘ And.right))

theorem setOf_dual_base_eq : setOf M﹡.Base = (fun X ↦ M.E \ X) '' setOf M.Base := by
  ext B
  simp only [mem_setOf_eq, mem_image, dual_base_iff']
  refine' ⟨fun h ↦ ⟨_, h.1, diff_diff_cancel_left h.2⟩, 
    fun ⟨B', hB', h⟩ ↦ ⟨_,h.symm.trans_subset (diff_subset _ _)⟩⟩
  rwa [←h, diff_diff_cancel_left hB'.subset_ground]

@[simp] theorem dual_dual (M : Matroid α) : M﹡﹡ = M :=  
  eq_of_base_iff_base_forall rfl (fun B (h : B ⊆ M.E) ↦ 
    by rw [dual_base_iff, dual_base_iff, dual_ground, diff_diff_cancel_left h])

theorem Base.compl_base_of_dual (h : M﹡.Base B) : M.Base (M.E \ B) := 
  (dual_base_iff'.1 h).1

theorem Base.compl_base_dual (h : M.Base B) : M﹡.Base (M.E \ B) := by
  rwa [dual_base_iff, diff_diff_cancel_left h.subset_ground] 

theorem Base.compl_inter_basis_of_inter_basis (hB : M.Base B) (hBX : M.Basis (B ∩ X) X) :
    M﹡.Basis ((M.E \ B) ∩ (M.E \ X)) (M.E \ X) := by
  refine' Indep.basis_of_forall_insert _ (inter_subset_right _ _) (fun e he ↦ _)
  · rw [dual_indep_iff_exists]
    exact ⟨B, hB, disjoint_of_subset_left (inter_subset_left _ _) disjoint_sdiff_left⟩
  simp only [diff_inter_self_eq_diff, mem_diff, not_and, not_not, imp_iff_right he.1.1] at he 
  simp_rw [dual_dep_iff_forall, insert_subset_iff, and_iff_right he.1.1, 
    and_iff_left ((inter_subset_left _ _).trans (diff_subset _ _))]
  refine' fun B' hB' ↦ by_contra (fun hem ↦ _)
  simp_rw [nonempty_iff_ne_empty, not_ne_iff, ←union_singleton, inter_distrib_right, 
    union_empty_iff, singleton_inter_eq_empty, diff_eq, inter_comm _ M.E, 
    ←inter_inter_distrib_left, ← inter_assoc, inter_right_comm, 
    inter_eq_self_of_subset_right hB'.subset_ground, ←diff_eq, diff_eq_empty] at hem
  obtain ⟨f, hfb, hBf⟩ := hB.exchange hB' ⟨he.2, hem.2⟩ 
  
  have hi : M.Indep (insert f (B ∩ X))
  · refine' hBf.indep.subset (insert_subset_insert _)
    simp_rw [subset_diff, and_iff_right (inter_subset_left _ _), disjoint_singleton_right, 
      mem_inter_iff, iff_false_intro he.1.2, and_false]
  exact hfb.2 (hBX.mem_of_insert_indep (hem.1 hfb) hi).1 

theorem Base.inter_basis_iff_compl_inter_basis_dual (hB : M.Base B) (hX : X ⊆ M.E := by aesop_mat): 
    M.Basis (B ∩ X) X ↔ M﹡.Basis ((M.E \ B) ∩ (M.E \ X)) (M.E \ X) := by
  refine' ⟨hB.compl_inter_basis_of_inter_basis, fun h ↦ _⟩
  simpa [inter_eq_self_of_subset_right hX, inter_eq_self_of_subset_right hB.subset_ground] using
    hB.compl_base_dual.compl_inter_basis_of_inter_basis h
    
theorem dual_inj {M₁ M₂ : Matroid α} (h : M₁﹡ = M₂﹡) : M₁ = M₂ :=
by rw [←dual_dual M₁, h, dual_dual]

@[simp] theorem dual_inj_iff {M₁ M₂ : Matroid α} : M₁﹡ = M₂﹡ ↔ M₁ = M₂ := ⟨dual_inj, congr_arg _⟩

theorem eq_dual_comm {M₁ M₂ : Matroid α} : M₁ = M₂﹡ ↔ M₂ = M₁﹡ := 
by rw [←dual_inj_iff, dual_dual, eq_comm]

theorem dual_eq_comm {M₁ M₂ : Matroid α} : M₁﹡ = M₂ ↔ M₂﹡ = M₁ := 
by rw [←dual_inj_iff, dual_dual, eq_comm]

theorem base_iff_dual_base_compl (hB : B ⊆ M.E := by aesop_mat) :
    M.Base B ↔ M﹡.Base (M.E \ B) := by 
  rw [dual_base_iff, diff_diff_cancel_left hB]

/-- A Coindependent set is a subset of `M.E` that is disjoint from some Base -/
def Coindep (M : Matroid α) (I : Set α) : Prop := (∃ B, M.Base B ∧ Disjoint I B) ∧ I ⊆ M.E
pp_extended_field_notation Coindep

@[aesop unsafe 10% (rule_sets [Matroid])]
theorem Coindep.subset_ground (hX : M.Coindep X) : X ⊆ M.E :=
  hX.2

theorem coindep_iff_exists (hX : X ⊆ M.E := by aesop_mat) : 
    M.Coindep X ↔ ∃ B, M.Base B ∧ B ⊆ M.E \ X := by
  simp_rw [Coindep, and_iff_left hX, subset_diff]
  exact ⟨fun ⟨B, hB⟩ ↦ ⟨B, hB.1, hB.1.subset_ground, hB.2.symm⟩, 
    fun ⟨B, hB⟩ ↦ ⟨B, hB.1, hB.2.2.symm⟩⟩

theorem Coindep.exists_base_subset_compl (h : M.Coindep X) : ∃ B, M.Base B ∧ B ⊆ M.E \ X := 
  (coindep_iff_exists h.subset_ground).mp h

@[simp] theorem dual_indep_iff_Coindep : M﹡.Indep X ↔ M.Coindep X := by 
  rw [dual_indep_iff_exists', and_comm]; rfl

end dual 

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

instance restrict_finite {R : Set α} (hR : R.Finite) : (M ↾ R).Finite := 
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

@[simp] theorem restrict_base_iff (hX : X ⊆ M.E := by aesop_mat) :
    (M ↾ X).Base I ↔ M.Basis I X := by
  simp_rw [base_iff_maximal_indep, basis_iff', restrict_indep_iff, and_iff_left hX, and_assoc]
  aesop

theorem restrict_base_iff' : (M ↾ X).Base I ↔ M.Basis' I X := by
  simp_rw [Basis', base_iff_maximal_indep, mem_maximals_setOf_iff, restrict_indep_iff]

theorem Basis.restrict_base (h : M.Basis I X) : (M ↾ X).Base I := by
  rw [basis_iff'] at h
  simp_rw [base_iff_maximal_indep, restrict_indep_iff, and_imp, and_assoc, and_iff_right h.1.1, 
    and_iff_right h.1.2.1] 
  exact fun J hJ hJX hIJ ↦ h.1.2.2 _ hJ hIJ hJX
 
instance restrict_finiteRk [M.FiniteRk] : (M ↾ R).FiniteRk := 
  let ⟨_, hB⟩ := (M ↾ R).exists_base
  hB.finiteRk_of_finite (hB.indep.of_restrict.finite)

@[simp] theorem Basis.base_restrict (h : M.Basis I X) : (M ↾ X).Base I := 
  (restrict_base_iff h.subset_ground).mpr h

theorem Basis.basis_restrict_of_subset (hI : M.Basis I X) (hXY : X ⊆ Y) : (M ↾ Y).Basis I X := by
  rwa [←restrict_base_iff, M.restrict_restrict_eq hXY, restrict_base_iff]

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

-- These lemmas are awkard positioned here, because they look like they belong in `Basic`, but
-- their proofs depend on the definition of restriction (and hence duality. ) Maybe refactoring 
-- the proofs isn't too bad. 

theorem Basis.transfer (hIX : M.Basis I X) (hJX : M.Basis J X) (hXY : X ⊆ Y) (hJY : M.Basis J Y) :
    M.Basis I Y := by
  rw [←restrict_base_iff]; rw [← restrict_base_iff] at hJY
  exact hJY.base_of_basis_supset hJX.subset (hIX.basis_restrict_of_subset hXY)

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
  rw [restrict_base_iff] at hI'
  exact ⟨I', hI', hII', hI'IJ⟩

theorem Indep.exists_insert_of_not_basis (hI : M.Indep I) (hIX : I ⊆ X) (hI' : ¬M.Basis I X)
    (hJ : M.Basis J X) : ∃ e ∈ J \ I, M.Indep (insert e I) := by
  rw [← restrict_base_iff] at hI' ; rw [← restrict_base_iff] at hJ 
  obtain ⟨e, he, hi⟩ := (hI.indep_restrict_of_subset hIX).exists_insert_of_not_base hI' hJ
  exact ⟨e, he, (restrict_indep_iff.mp hi).1⟩

theorem Basis.base_of_base_subset (hIX : M.Basis I X) (hB : M.Base B) (hBX : B ⊆ X) : M.Base I :=
  hB.base_of_basis_supset hBX hIX

theorem Basis.exchange (hIX : M.Basis I X) (hJX : M.Basis J X) (he : e ∈ I \ J) :
    ∃ f ∈ J \ I, M.Basis (insert f (I \ {e})) X := by
  obtain ⟨y,hy, h⟩ := hIX.restrict_base.exchange hJX.restrict_base he
  exact ⟨y, hy, by rwa [restrict_base_iff] at h⟩ 
  
theorem Basis.eq_exchange_of_diff_eq_singleton (hI : M.Basis I X) (hJ : M.Basis J X)
    (hIJ : I \ J = {e}) : ∃ f ∈ J \ I, J = insert f I \ {e} := by
  rw [← restrict_base_iff] at hI hJ ; exact hI.eq_exchange_of_diff_eq_singleton hJ hIJ

end Basis

end Matroid