import Matroid.Flat

variable {α : Type _} {M : Matroid α} {E : Set α}

namespace Matroid 

open Set 

section EmptyOn

/-- The `Matroid α` with empty ground set-/
def empty_on (α : Type _) : Matroid α := 
  matroid_of_base_of_finite finite_empty (· = ∅) ⟨_,rfl⟩ (by rintro _ _ rfl; simp) (by simp)

@[simp] theorem empty_on_ground : (empty_on α).E = ∅ := rfl

@[simp] theorem empty_on_base_iff : (empty_on α).Base B ↔ B = ∅ := by 
  simp [empty_on]

@[simp] theorem empty_on_indep_iff : (empty_on α).Indep B ↔ B = ∅ := by 
  simp [indep_iff_subset_base, subset_empty_iff]  

@[simp] theorem ground_eq_empty_iff : (M.E = ∅) ↔ M = empty_on α := by 
  refine' ⟨fun h ↦ eq_of_base_iff_base_forall (by simp [h]) _, fun h ↦ by simp [h]⟩
  simp only [h, subset_empty_iff, empty_on_base_iff, forall_eq, iff_true]
  obtain ⟨B', hB'⟩ := M.exists_base
  rwa [←eq_empty_of_subset_empty (hB'.subset_ground.trans_eq h)]

@[simp] theorem empty_on_dual_eq : (empty_on α)﹡ = empty_on α := by
  rw [← ground_eq_empty_iff]; rfl 
  
/-- Any two empty matroids are isomorphic -/
noncomputable def Iso.of_empty (α β : Type _) [_root_.Nonempty α] [_root_.Nonempty β] : 
    Iso (empty_on α) (empty_on β) where
  toLocalEquiv := InjOn.toLocalEquiv _ _ (injOn_empty (Classical.arbitrary (α → β)))
  source_eq' := by simp
  target_eq' := by simp
  setOf_base_eq' := by ext B; simp [eq_comm (a := ∅)]

@[simp] theorem delete_ground_self (M : Matroid α) : M ⟍ M.E = empty_on α := by
  simp [←ground_eq_empty_iff]

@[simp] theorem contract_ground_self (M : Matroid α) : M ⟋ M.E = empty_on α := by
  simp [←ground_eq_empty_iff]

@[simp] theorem restrict_to_empty (M : Matroid α) : M ↾ (∅ : Set α) = empty_on α := by 
  simp [←ground_eq_empty_iff]

@[simp] theorem empty_minor (M : Matroid α) : (empty_on α) ≤m M :=
  ⟨M.E, ∅, by simp [rfl.subset]⟩ 
  
@[simp] theorem minor_empty_iff : M ≤m empty_on α ↔ M = empty_on α :=
  ⟨fun h ↦ ground_eq_empty_iff.1 (eq_empty_of_subset_empty h.subset), 
    by rintro rfl; apply empty_minor⟩



theorem eq_empty_on_or_nonempty (M : Matroid α) : M = empty_on α ∨ Nonempty M := by 
  rw [←ground_eq_empty_iff]
  exact M.E.eq_empty_or_nonempty.elim Or.inl (fun h ↦ Or.inr ⟨h⟩)


end EmptyOn

section LoopyOn

/-- The `Matroid α` with ground set `E` whose only base is `∅` -/
def loopy_on (E : Set α) : Matroid α := (empty_on α ↾ E) 

@[simp] theorem loopy_on_ground (E : Set α) : (loopy_on E).E = E := rfl 

@[simp] theorem loopy_on_indep_iff : (loopy_on E).Indep I ↔ I = ∅ := by
  simp only [loopy_on, restrict_indep_iff, empty_on_indep_iff, and_iff_left_iff_imp]
  rintro rfl; apply empty_subset

@[simp] theorem loopy_on_base_iff : (loopy_on E).Base B ↔ B = ∅ := by
  simp only [base_iff_maximal_indep, loopy_on_indep_iff, forall_eq, and_iff_left_iff_imp]
  exact fun h _ ↦ h
  
@[simp] theorem loopy_on_er_eq (E X : Set α) : (loopy_on E).er X = 0 := by 
  obtain ⟨I, hI⟩ := (loopy_on E).exists_basis' X 
  rw [hI.er_eq_encard, loopy_on_indep_iff.1 hI.indep, encard_empty]

@[simp] theorem loopy_on_erk_eq (E : Set α) : (loopy_on E).erk = 0 := by 
  rw [erk_eq_er_ground, loopy_on_er_eq]

@[simp] theorem loopy_on_r_eq (E X : Set α) : (loopy_on E).r X = 0 := by 
  rw [←er_toNat_eq_r, loopy_on_er_eq]; rfl 

@[simp] theorem loopy_on_basis_iff : (loopy_on E).Basis I X ↔ I = ∅ ∧ X ⊆ E :=
  ⟨fun h ↦⟨loopy_on_indep_iff.mp h.indep, h.subset_ground⟩, 
    by rintro ⟨rfl, hX⟩; rw [basis_iff]; simp⟩ 

@[simp] theorem loopy_on_cl_eq (E X : Set α) : (loopy_on E).cl X = E := 
  (cl_subset_ground _ _).antisymm 
    (subset_trans (by rw [(loopy_on_base_iff.2 rfl).cl_eq]) (cl_subset_cl _ (empty_subset _)))

@[simp] theorem cl_empty_eq_ground_iff : M.cl ∅ = M.E ↔ M = loopy_on M.E := by 
  refine ⟨fun h ↦ eq_of_cl_eq_cl_forall ?_, fun h ↦ by rw [h, loopy_on_cl_eq, loopy_on_ground]⟩
  refine fun X ↦ subset_antisymm (by simp [cl_subset_ground]) ?_ 
  rw [loopy_on_cl_eq, ←h]
  exact M.cl_mono (empty_subset _)
   
@[simp] theorem erk_eq_zero_iff : M.erk = 0 ↔ M = loopy_on M.E := by 
  refine ⟨fun h ↦ cl_empty_eq_ground_iff.1 ?_, fun h ↦ by rw [h, loopy_on_erk_eq]⟩
  obtain ⟨B, hB⟩ := M.exists_base
  rw [←hB.encard, encard_eq_zero] at h 
  rw [←h, hB.cl_eq]

@[simp] theorem empty_base_iff : M.Base ∅ ↔ M = loopy_on M.E :=
  ⟨fun h ↦ by rw [←cl_empty_eq_ground_iff, h.cl_eq], fun h ↦ by rw [h, loopy_on_base_iff]⟩
  
theorem eq_loopy_on_iff_cl : M = loopy_on E ↔ M.cl ∅ = E ∧ M.E = E :=
  ⟨fun h ↦ by rw [h]; simp, fun ⟨h,h'⟩ ↦ by rw [←h', ←cl_empty_eq_ground_iff, h, h']⟩
  
theorem eq_loopy_on_iff_erk : M = loopy_on E ↔ M.erk = 0 ∧ M.E = E := 
  ⟨fun h ↦ by rw [h]; simp, fun ⟨h,h'⟩ ↦ by rw [←h', ←erk_eq_zero_iff, h]⟩



instance : FiniteRk (loopy_on E) := 
  ⟨⟨∅, loopy_on_base_iff.2 rfl, finite_empty⟩⟩ 

theorem Finite.loopy_on_finite (hE : E.Finite) : Finite (loopy_on E) := 
  ⟨hE⟩ 

@[simp] theorem loopy_on_restrict (E R : Set α) : (loopy_on E) ↾ R = loopy_on R := by
  have h0 : ((loopy_on E) ↾ R).erk = 0 
  · rw [erk_eq_er_ground, restrict_er_eq', loopy_on_er_eq]
  rwa [erk_eq_zero_iff, restrict_ground_eq] at h0

@[simp] theorem loopy_on_delete (E X : Set α) : (loopy_on E) ⟍ X = loopy_on (E \ X) := by
  rw [←restrict_compl, loopy_on_restrict, loopy_on_ground]

@[simp] theorem loopy_on_contract (E X : Set α) : (loopy_on E) ⟋ X = loopy_on (E \ X) := by 
  simp_rw [eq_loopy_on_iff_cl, contract_cl_eq, empty_union, loopy_on_cl_eq, contract_ground, 
    loopy_on_ground]
  
@[simp] theorem loopy_on_minor : M ≤m loopy_on E ↔ M = loopy_on M.E ∧ M.E ⊆ E := by 
  refine ⟨fun h ↦ ⟨by obtain ⟨C, D, _, _, _, rfl⟩ := h; simp, h.subset⟩, fun ⟨h, hss⟩ ↦ ?_⟩
  
  convert (loopy_on E).restrict_minor hss using 1
  rw [h, loopy_on_ground, loopy_on_restrict]

theorem contract_eq_loopy_on_of_spanning (h : M.Spanning C) : M ⟋ C = loopy_on (M.E \ C) := by 
  rw [eq_loopy_on_iff_cl, contract_ground, and_iff_left rfl, contract_cl_eq, empty_union, h.cl_eq]
  
theorem eq_loopy_on_or_rkPos (M : Matroid α) : M = loopy_on M.E ∨ RkPos M := by 
  rw [←empty_base_iff, rkPos_iff_empty_not_base]; apply em
  
end LoopyOn

section FreeOn

/-- The `Matroid α` with ground set `E` whose only base is `E`. -/
def free_on (E : Set α) : Matroid α := (loopy_on E)﹡  

@[simp] theorem free_on_ground : (free_on E).E = E := rfl 

@[simp] theorem free_on_dual_eq : (free_on E)﹡ = loopy_on E := by 
  rw [free_on, dual_dual]
  
@[simp] theorem loopy_on_dual_eq : (loopy_on E)﹡ = free_on E := rfl 

@[simp] theorem free_on_base_iff : (free_on E).Base B ↔ B = E := by
  simp only [free_on, loopy_on_ground, dual_base_iff', loopy_on_base_iff, diff_eq_empty, 
    ←subset_antisymm_iff, eq_comm (a := E)]

@[simp] theorem free_on_indep_iff : (free_on E).Indep I ↔ I ⊆ E := by
  simp [indep_iff_subset_base]

theorem free_on_indep (hIE : I ⊆ E) : (free_on E).Indep I := 
  free_on_indep_iff.2 hIE

@[simp] theorem free_on_erk_eq (E : Set α) : (free_on E).erk = E.encard := by
  rw [erk_eq_er_ground, free_on_ground, (free_on_indep_iff.2 rfl.subset).er]

@[simp] theorem free_on_basis_iff : (free_on E).Basis I X ↔ I = X ∧ X ⊆ E := by 
  use fun h ↦ ⟨(free_on_indep h.subset_ground).eq_of_basis h ,h.subset_ground⟩
  rintro ⟨rfl, hIE⟩ 
  exact (free_on_indep hIE).basis_self
  
@[simp] theorem free_on_basis'_iff : (free_on E).Basis' I X ↔ I = X ∩ E := by 
  rw [basis'_iff_basis_inter_ground, free_on_basis_iff, free_on_ground, 
    and_iff_left (inter_subset_right _ _)]

theorem free_on_er_eq (hXE : X ⊆ E) : (free_on E).er X = X.encard := by
  obtain ⟨I, hI⟩ := (free_on E).exists_basis X
  rw [hI.er_eq_encard, (free_on_indep hXE).eq_of_basis hI]

theorem free_on_r_eq (hXE : X ⊆ E) : (free_on E).r X = X.ncard := by 
  rw [←er_toNat_eq_r, free_on_er_eq hXE, ncard_def]

@[simp] theorem ground_indep_iff_eq_free_on : M.Indep M.E ↔ M = free_on M.E := 
  ⟨fun h ↦ eq_of_indep_iff_indep_forall rfl fun I hI ↦ by simp [hI, h.subset hI], 
    fun h ↦ by rw [h]; simp [rfl.subset]⟩
  
@[simp] theorem girth_eq_top_iff_free_on [Finitary M] : M.girth = ⊤ ↔ M = free_on M.E := by
  rw [←ground_indep_iff_eq_free_on, girth_eq_top_iff, indep_iff_forall_subset_not_circuit]
  exact ⟨fun h C _ hC ↦ h C hC hC.finite, fun h C hC _ ↦ h C hC.subset_ground hC⟩
  
@[simp] theorem free_on_delete (E X : Set α) : (free_on E) ⟍ X = free_on (E \ X) := by
  rw [←loopy_on_dual_eq, ←contract_dual_eq_dual_delete, loopy_on_contract, loopy_on_dual_eq]

theorem free_on_restrict (h : R ⊆ E) : (free_on E) ↾ R = free_on R := by 
  rw [←delete_compl, free_on_delete, free_on_ground, diff_diff_cancel_left h]

@[simp] theorem free_on_contract (E X : Set α) : (free_on E) ⟋ X = free_on (E \ X) := by
  rw [←loopy_on_dual_eq, ←delete_dual_eq_dual_contract, loopy_on_delete, loopy_on_dual_eq]

end FreeOn

section TrivialOn

/-- The matroid on `E` whose unique base is the subset `I` of `E`.  (If `I` is not a subset of `E`, 
  the base is `I ∩ E` )-/
def trivial_on (I E : Set α) : Matroid α := (free_on I) ↾ E 

@[simp] theorem trivial_on_ground : (trivial_on I E).E = E := 
  rfl 

theorem trivial_on_base_iff (hIE : I ⊆ E) : (trivial_on I E).Base B ↔ B = I := by
  rw [trivial_on, base_restrict_iff', free_on_basis'_iff, inter_eq_self_of_subset_right hIE]

theorem trivial_on_inter_ground_eq (I E : Set α) :
    trivial_on (I ∩ E) E = trivial_on I E := by
  simp only [trivial_on, restrict_eq_restrict_iff, free_on_indep_iff, subset_inter_iff, 
    iff_self_and]
  tauto

@[simp] theorem trivial_on_indep_iff' : (trivial_on I E).Indep J ↔ J ⊆ I ∩ E := by
  rw [trivial_on, restrict_indep_iff, free_on_indep_iff, subset_inter_iff]

theorem trivial_on_indep_iff (hIE : I ⊆ E) : (trivial_on I E).Indep J ↔ J ⊆ I := by
  rw [trivial_on, restrict_indep_iff, free_on_indep_iff, and_iff_left_iff_imp]
  exact fun h ↦ h.trans hIE

theorem trivial_on_basis_iff (hI : I ⊆ E) (hX : X ⊆ E) :
    (trivial_on I E).Basis J X ↔ J = X ∩ I := by
  rw [basis_iff_mem_maximals]
  simp_rw [trivial_on_indep_iff', ←subset_inter_iff, ←le_eq_subset, Iic_def, maximals_Iic, 
    mem_singleton_iff, inter_eq_self_of_subset_left hI, inter_comm I]

theorem trivial_on_inter_basis (hI : I ⊆ E) (hX : X ⊆ E) : (trivial_on I E).Basis (X ∩ I) X := by
  rw [trivial_on_basis_iff hI hX]
  
@[simp] theorem trivial_on_dual_eq (I E : Set α) : (trivial_on I E)﹡ = trivial_on (E \ I) E := by
  rw [←trivial_on_inter_ground_eq]
  refine eq_of_base_iff_base_forall rfl (fun B (hB : B ⊆ E) ↦ ?_)
  rw [dual_base_iff, trivial_on_base_iff (inter_subset_right _ _), 
    trivial_on_base_iff (diff_subset _ _), trivial_on_ground]
  refine' ⟨fun h ↦ _, fun h ↦ _⟩
  · rw [←diff_diff_cancel_left hB, h, diff_inter_self_eq_diff]
  rw [h, inter_comm I]; simp 

@[simp] theorem trivial_on_cl_eq (I E X : Set α) : 
    (trivial_on I E).cl X = (X ∩ I ∩ E) ∪ (E \ I) := by
  have hb := (trivial_on_basis_iff (inter_subset_right I E) (inter_subset_right X E)).mpr rfl
  ext e
  
  rw [←trivial_on_inter_ground_eq I E, cl_eq_cl_inter_ground _ X, trivial_on_ground, 
    ←hb.cl_eq_cl, hb.indep.mem_cl_iff, dep_iff, trivial_on_indep_iff', insert_subset_iff, 
    trivial_on_ground, inter_assoc, inter_self,  and_iff_left (inter_subset_right _ _), 
    ←inter_inter_distrib_right, inter_assoc, union_distrib_right, inter_comm I, inter_union_diff, 
    insert_subset_iff, inter_comm X, inter_assoc, and_iff_left (inter_subset_left _ _), 
    mem_inter_iff]
  simp only [not_and, mem_inter_iff, mem_union, mem_diff]
  tauto
   
theorem eq_trivial_on_of_loops_union_coloops (hE : M.E = M.cl ∅ ∪ M﹡.cl ∅) :
    M = trivial_on (M﹡.cl ∅) M.E := by
  refine eq_of_base_iff_base_forall rfl (fun B hBE ↦ ?_) 
  rw [trivial_on_base_iff (show M﹡.cl ∅ ⊆ M.E from M﹡.cl_subset_ground _)]
  rw [hE, ←diff_subset_iff] at hBE
  use fun h ↦ h.coloops_subset.antisymm' (by rwa [sdiff_eq_left.mpr h.indep.disjoint_loops] at hBE)
  rintro rfl
  obtain ⟨B, hB⟩ := M.exists_base
  rwa [hB.coloops_subset.antisymm ]
  refine subset_trans ?_ (diff_subset_iff.2 hE.subset)
  rw [subset_diff, and_iff_right hB.subset_ground]
  exact hB.indep.disjoint_loops

theorem trivial_on_loops_eq (I E : Set α) : (trivial_on I E).cl ∅ = E \ I := by 
  simp
  
@[simp] theorem trivial_on_coloops_eq' (I E : Set α) : (trivial_on I E)﹡.cl ∅ = I ∩ E := by 
  simp [inter_comm I]
  
theorem trivial_on_coloops_eq (h : I ⊆ E) : (trivial_on I E)﹡.cl ∅ = I := by 
  simp [h]

@[simp] theorem trivial_on_self (I : Set α) : (trivial_on I I) = free_on I := by 
  rw [trivial_on, free_on_restrict rfl.subset]

@[simp] theorem trivial_on_empty (I : Set α) : (trivial_on ∅ I) = loopy_on I := by 
  rw [←dual_inj_iff, trivial_on_dual_eq, diff_empty, trivial_on_self, loopy_on_dual_eq]
  
@[simp] theorem trivial_on_restrict' (I E R : Set α) :
    (trivial_on I E) ↾ R = trivial_on (I ∩ R ∩ E) R := by
  simp_rw [eq_iff_indep_iff_indep_forall, restrict_ground_eq, trivial_on_ground, true_and, 
    restrict_indep_iff, trivial_on_indep_iff', subset_inter_iff]
  tauto

theorem trivial_on_restrict (h : I ⊆ E) (R : Set α) : 
    (trivial_on I E) ↾ R = trivial_on (I ∩ R) R := by
  rw [trivial_on_restrict', inter_right_comm, inter_eq_self_of_subset_left h]

@[simp] theorem trivial_on_delete (I E D : Set α) : 
    (trivial_on I E) ⟍ D = trivial_on (I \ D) (E \ D) := by 
  rw [←restrict_compl, trivial_on_restrict', trivial_on_ground, inter_assoc, 
    inter_eq_self_of_subset_left (diff_subset _ _), eq_comm, ←trivial_on_inter_ground_eq, 
    diff_inter_diff_right, inter_diff_assoc]
  
@[simp] theorem trivial_on_contract (I E C : Set α) : 
    (trivial_on I E) ⟋ C = trivial_on (I \ C) (E \ C) := by 
  rw [←dual_inj_iff, contract_dual_eq_dual_delete, trivial_on_dual_eq, trivial_on_delete, 
    diff_diff_comm, ←trivial_on_dual_eq, dual_inj_iff, ←trivial_on_inter_ground_eq, eq_comm, 
    ←trivial_on_inter_ground_eq, diff_inter_diff_right, inter_diff_assoc]
  
theorem trivial_on_of_minor (h : M ≤m trivial_on I E) : ∃ I₀, M = trivial_on I₀ M.E := by 
  obtain ⟨C, D, -, -, -, rfl⟩ := h
  simp only [trivial_on_contract, trivial_on_delete, trivial_on_ground]
  exact ⟨_, rfl⟩ 

end TrivialOn