import Matroid.Minor

variable {α : Type _} {M : Matroid α} {E : Set α}

namespace Matroid 

open Set 

section EmptyOn

/-- The `Matroid α` with empty ground set-/
def empty_on (α : Type) : Matroid α := 
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
noncomputable def Iso.of_empty (α β : Type _) [Nonempty α] [Nonempty β] : 
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
  simp_rw [trivial_on, restrict_eq_restrict_iff, free_on_indep_iff, subset_inter_iff, iff_self_and]
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
  simp_rw [←trivial_on_inter_ground_eq I E, cl_eq_cl_inter_ground _ X, trivial_on_ground, 
    ←hb.cl_eq_cl, hb.indep.mem_cl_iff, dep_iff, trivial_on_indep_iff', insert_subset_iff, 
    trivial_on_ground, inter_comm E, inter_assoc, inter_self, inter_comm E, inter_assoc, inter_self,
    and_iff_left (inter_subset_right _ _),
    and_iff_left ((inter_subset_right _ _).trans (inter_subset_right _ _))]
  simp only [mem_inter_iff, and_true, not_and, mem_union, mem_diff]
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

section Truncate

/-- The truncation of a matroid to finite rank `k`. The independent sets of the truncation
  are the independent sets of the matroid of size at most `k`. -/
def truncate (M : Matroid α) (k : ℕ∞) : Matroid α := 
  Option.casesOn k M 
  fun k ↦ matroid_of_indep_of_bdd_augment M.E (fun I ↦ M.Indep I ∧ I.encard ≤ k) 
  ( by simp )
  ( fun I J ⟨hI, hIc⟩ hIJ ↦ ⟨hI.subset hIJ, (encard_mono hIJ).trans hIc⟩ )
  ( by
      rintro I J ⟨hI, _⟩ ⟨hJ, hJc⟩ hIJ
      obtain ⟨e, he, hi⟩ := hI.augment hJ hIJ
      exact ⟨e, he.1, he.2, hi,
        (encard_insert_of_not_mem he.2).trans_le ((ENat.add_one_le_of_lt hIJ).trans hJc)⟩ )
  ⟨ k, fun I ⟨_, hIJ⟩ ↦ hIJ ⟩ 
  ( fun I h ↦ h.1.subset_ground )

@[simp] theorem truncate_top (M : Matroid α) : M.truncate ⊤ = M := rfl 

@[simp] theorem truncate_indep_iff : (M.truncate k).Indep I ↔ (M.Indep I ∧ I.encard ≤ k) := by 
  cases k <;> simp [truncate, WithTop.none_eq_top, WithTop.some_eq_coe, le_top]

@[simp] theorem truncate_ground_eq : (M.truncate k).E = M.E := by
  cases k <;> rfl

@[simp] theorem truncate_zero (M : Matroid α) : M.truncate 0 = loopy_on M.E := by 
  refine' eq_of_indep_iff_indep_forall rfl _
  simp only [truncate_ground_eq, truncate_indep_iff, nonpos_iff_eq_zero, encard_eq_zero, 
    loopy_on_indep_iff, and_iff_right_iff_imp]
  rintro I - rfl; apply empty_indep

theorem truncate_eq_self_of_rk_le (h_rk : M.erk ≤ k) : M.truncate k = M := by 
  refine eq_of_indep_iff_indep_forall truncate_ground_eq (fun I _ ↦ ?_)
  rw [truncate_indep_iff, and_iff_left_iff_imp]
  exact fun hi ↦ hi.encard_le_erk.trans h_rk
  
theorem truncate_base_iff {k : ℕ} (h_rk : k ≤ M.erk) :
    (M.truncate k).Base B ↔ M.Indep B ∧ B.encard = k := by
  simp_rw [base_iff_maximal_indep, truncate_indep_iff, and_imp]
  refine ⟨fun ⟨⟨hB, hBk⟩, h⟩ ↦ ⟨hB, hBk.antisymm (le_of_not_lt fun hlt ↦ ?_)⟩, 
    fun ⟨hB, hBk⟩ ↦ ⟨⟨ hB, hBk.le⟩, 
      fun I _ hIk hBI ↦ ?_⟩ ⟩
  · obtain ⟨B', hB', hJB'⟩ := hB.exists_base_supset
    obtain ⟨J, hBJ, hJB', h'⟩ := 
      exists_supset_subset_encard_eq hJB' hBk (h_rk.trans_eq hB'.encard.symm)
    rw [h _ (hB'.indep.subset hJB') h'.le hBJ] at hlt
    exact hlt.ne h' 
  exact (finite_of_encard_eq_coe hBk).eq_of_subset_of_encard_le' hBI (hIk.trans_eq hBk.symm)

theorem truncate_base_iff_of_finiteRk [FiniteRk M] (h_rk : k ≤ M.erk) : 
    (M.truncate k).Base B ↔ M.Indep B ∧ B.encard = k := by
  lift k to ℕ using (h_rk.trans_lt M.erk_lt_top).ne; rwa [truncate_base_iff]
  
instance truncate.finite [Finite M] : Finite (M.truncate k) := 
⟨ by simp [ground_finite M] ⟩

instance truncate.finiteRk {k : ℕ} : FiniteRk (M.truncate k) := by
  obtain ⟨B, hB⟩ := (M.truncate k).exists_base
  refine ⟨B, hB, (le_or_lt M.erk k).elim (fun h ↦ ?_) (fun h ↦ ?_)⟩
  · rw [truncate_eq_self_of_rk_le h] at hB
    rw [←encard_lt_top_iff, hB.encard]
    exact h.trans_lt (WithTop.coe_lt_top _)
  rw [truncate_base_iff h.le] at hB
  rw [←encard_lt_top_iff, hB.2]
  apply WithTop.coe_lt_top
   
theorem Indep.of_truncate (h : (M.truncate k).Indep I) : M.Indep I := by 
  rw [truncate_indep_iff] at h; exact h.1

theorem Indep.encard_le_of_truncate (h : (M.truncate k).Indep I) : I.encard ≤ k := 
  (truncate_indep_iff.mp h).2

theorem truncate_er_eq (M : Matroid α) (k : ℕ∞) (X : Set α) : 
    (M.truncate k).er X = min (M.er X) k := by
  simp_rw [le_antisymm_iff, le_er_iff, er_le_iff, truncate_indep_iff]
  obtain ⟨I, hI⟩ := M.exists_basis' X
  refine ⟨fun J hJX hJi ↦ le_min (hJi.1.encard_le_er_of_subset hJX) hJi.2, ?_⟩
  obtain ⟨I₀, hI₀, hI₀ss⟩ := exists_subset_encard_eq (min_le_of_left_le (b := k) hI.encard.symm.le)
  exact ⟨_, hI₀.trans hI.subset, ⟨hI.indep.subset hI₀, hI₀ss.trans_le (min_le_right _ _)⟩, hI₀ss⟩   
  
end Truncate

section Uniform

/-- A uniform matroid with a given rank `k` and ground set `E`. If `k = ⊤`, then every set is
  independent. ` -/
def unif_on (E : Set α) (k : ℕ∞) : Matroid α := (free_on E).truncate k 

@[simp] theorem unif_on_ground_eq (E : Set α) : (unif_on E k).E = E := by
  cases k <;> rfl

@[simp] theorem unif_on_indep_iff : (unif_on E k).Indep I ↔ I.encard ≤ k ∧ I ⊆ E := by
  simp [unif_on, and_comm]

@[simp] theorem unif_on_top (E : Set α) : unif_on E ⊤ = free_on E := by 
  rw [unif_on, truncate_top]

@[simp] theorem unif_on_zero (E : Set α) : unif_on E 0 = loopy_on E := by 
  simp [unif_on]
 
theorem unif_on_eq_unif_on_min (E : Set α) (k : ℕ∞) : unif_on E k = unif_on E (min k E.encard) := by
  simp only [ge_iff_le, eq_iff_indep_iff_indep_forall, unif_on_ground_eq, unif_on_indep_iff, 
    le_min_iff, and_congr_left_iff, iff_self_and, true_and]
  exact fun I hI _ _ ↦ encard_mono hI

@[simp] theorem unif_on_encard : unif_on E E.encard = free_on E := by 
  rw [unif_on, truncate_eq_self_of_rk_le (free_on_erk_eq _).le]

theorem unif_on_eq_of_le (h : E.encard ≤ k) : unif_on E k = free_on E := by 
  rw [unif_on, truncate_eq_self_of_rk_le (by rwa [free_on_erk_eq])]

theorem unif_on_base_iff {k : ℕ} (hk : k ≤ E.encard) (hBE : B ⊆ E) : 
    (unif_on E k).Base B ↔ B.encard = k := by
  rw [unif_on, truncate_base_iff, free_on_indep_iff, and_iff_right hBE]; rwa [free_on_erk_eq]

theorem unif_on_base_iff' (hktop : k ≠ ⊤) (hk : k ≤ E.encard) (hBE : B ⊆ E) : 
    (unif_on E k).Base B ↔ B.encard = k := by
  lift k to ℕ using hktop; rw [unif_on_base_iff hk hBE]
  
theorem unif_on_er_eq (E : Set α) (k : ℕ∞) (hX : X ⊆ E) : (unif_on E k).er X = min X.encard k := by
  rw [unif_on, truncate_er_eq, free_on_er_eq hX]

theorem unif_on_er_eq' (E : Set α) (k : ℕ∞) : (unif_on E k).er X = min (X ∩ E).encard k := by
  rw [←er_inter_ground_eq, unif_on_er_eq _ _ (by rw [unif_on_ground_eq]; apply inter_subset_right), 
    unif_on_ground_eq]

instance {k : ℕ} {E : Set α} : FiniteRk (unif_on E k) := by
  rw [←rFin_ground_iff_finiteRk, rFin, unif_on_er_eq _ _ (by simp [rfl.subset])]
  exact (min_le_right _ _).trans_lt (WithTop.coe_lt_top _)
  
@[simp] theorem unif_on_spanning_iff' {k : ℕ∞} (hk : k ≠ ⊤) :
    (unif_on E k).Spanning X ↔ (k ≤ X.encard ∧ X ⊆ E) ∨ X = E  := by 
  lift k to ℕ using hk 
  rw [spanning_iff_er', erk_eq_er_ground, unif_on_ground_eq, unif_on_er_eq', unif_on_er_eq', 
    le_min_iff, min_le_iff, min_le_iff, iff_true_intro (le_refl _), or_true, and_true, inter_self]
  refine' ⟨fun ⟨h, hXE⟩ ↦ h.elim (fun h ↦ _) (fun h ↦ Or.inl ⟨_,hXE⟩), 
    fun h ↦ h.elim (fun ⟨hle, hXE⟩ ↦ ⟨Or.inr (by rwa [inter_eq_self_of_subset_left hXE]), hXE⟩ ) _⟩
  · refine' X.finite_or_infinite.elim (fun hfin ↦ Or.inr _) (fun hinf ↦ Or.inl ⟨_, hXE⟩) 
    · rw [←(hfin.inter_of_left E).eq_of_subset_of_encard_le' (inter_subset_right _ _) h, 
        inter_eq_self_of_subset_left hXE]
    rw [hinf.encard_eq]
    apply le_top
  · exact h.trans (encard_mono (inter_subset_left _ _))
  rintro rfl
  rw [inter_self]
  exact ⟨Or.inl rfl.le, Subset.rfl⟩ 

theorem unif_on_spanning_iff {k : ℕ} (hk : k ≤ E.encard) (hX : X ⊆ E) : 
    (unif_on E k).Spanning X ↔ k ≤ X.encard := by
  rw [← ENat.some_eq_coe, unif_on_spanning_iff' (WithTop.coe_lt_top k).ne, and_iff_left hX, 
    or_iff_left_iff_imp]
  rintro rfl
  assumption
  
theorem eq_unif_on_iff : M = unif_on E k ↔ M.E = E ∧ ∀ I, M.Indep I ↔ I.encard ≤ k ∧ I ⊆ E :=
  ⟨by rintro rfl; simp, 
    fun ⟨hE, h⟩ ↦ eq_of_indep_iff_indep_forall (by simpa) fun I _↦ by simpa using h I⟩
  
theorem unif_on_dual_eq (hE : E.Finite) : (unif_on E k)﹡ = unif_on E (E.encard - k) := by
  obtain (rfl | hk) := eq_or_ne k ⊤; simp
  lift k to ℕ using hk 
  obtain (hle | hlt) := le_or_lt E.encard k
  · rw [unif_on_eq_of_le hle, free_on_dual_eq, tsub_eq_zero_of_le hle, unif_on_zero]
  refine eq_of_base_iff_base_forall (by simp) (fun B hBE ↦ ?_)
  simp only [dual_ground, unif_on_ground_eq] at hBE 
  rw [dual_base_iff', unif_on_base_iff' ((tsub_le_self.trans_lt hE.encard_lt_top).ne) (by simp) hBE, 
    unif_on_ground_eq, and_iff_left hBE, unif_on_base_iff hlt.le (diff_subset _ _), 
    ←WithTop.add_right_cancel_iff (hE.subset hBE).encard_lt_top.ne, 
    encard_diff_add_encard_of_subset hBE, Iff.comm, eq_comm, add_comm, 
    ←WithTop.add_right_cancel_iff (hlt.trans_le le_top).ne, tsub_add_cancel_of_le hlt.le]
  
@[simp] theorem unif_on_delete_eq (E D : Set α) (k : ℕ∞) :
    (unif_on E k) ⟍ D = unif_on (E \ D) k := by
  simp_rw [eq_unif_on_iff, delete_ground, unif_on_ground_eq, true_and, delete_indep_iff, 
    unif_on_indep_iff, subset_diff, and_assoc, imp_true_iff]

-- @[simp] theorem unif_on_contract_eq'' (E C : Set α) {k1 k2 : ℕ∞} (h1 : (E ∩ C).encard ): 
--     (unif_on E k) ⟋ C = unif_on (E \ C) (k - (E ∩ C).encard) := by 

@[simp] theorem unif_on_contract_eq' (E C : Set α) {k : ℕ∞} (hk : k ≠ ⊤): 
    (unif_on E k) ⟋ C = unif_on (E \ C) (k - (E ∩ C).encard) := by 
  lift k to ℕ using hk
  rw [←contract_inter_ground_eq, unif_on_eq_unif_on_min, unif_on_ground_eq, inter_comm]
  refine' eq_of_spanning_iff_spanning_forall (by simp) (fun S hS ↦ _)
  rw [contract_spanning_iff, unif_on_spanning_iff', unif_on_spanning_iff']
  · simp only [ge_iff_le, contract_ground, unif_on_ground_eq, diff_self_inter, subset_diff] at hS  
    simp only [ge_iff_le, min_le_iff, union_subset_iff, inter_subset_left, and_true, 
      tsub_le_iff_right, subset_diff, subset_antisymm_iff (a := S), diff_subset_iff, 
      and_iff_right hS, iff_true_intro hS.1, true_and, iff_true_intro hS.2]
    
    refine' ⟨fun ⟨h,hdj⟩ ↦ h.elim (fun h ↦ _) (fun h ↦ _), fun h ↦ _⟩
    · sorry
    · right; rw [← h, union_comm]; apply union_subset_union_left _ (inter_subset_right _ _)

      

      
      
      
      
      

  
  
--   lift k to ℕ using hk
--   obtain (hle | hlt) := le_or_lt E.encard k
--   · have hle' := (encard_mono (inter_subset_left E C)).trans hle
--     rw [unif_on_eq_of_le hle, free_on_contract, unif_on_eq_of_le ]
--     rwa [←WithTop.add_le_add_iff_right (hle'.trans_lt (WithTop.coe_lt_top _)).ne, 
--       encard_diff_add_encard_inter, tsub_add_cancel_of_le hle']
--   obtain (hle' | hlt') := le_or_lt (k : ℕ∞) (E ∩ C).encard
--   · rw [tsub_eq_zero_of_le hle', unif_on_zero, ←contract_inter_ground_eq, 
--       contract_eq_loopy_on_of_spanning, unif_on_ground_eq, diff_inter_self_eq_diff]
--     rwa [unif_on_ground_eq, unif_on_spanning_iff hlt.le (inter_subset_right _ _), inter_comm]
--   obtain (hfin | hinf) := E.finite_or_infinite
--   · rw [← dual_inj_iff, contract_dual_eq_dual_delete, unif_on_dual_eq hfin, 
--       unif_on_dual_eq (hfin.diff C), unif_on_delete_eq]
--     convert rfl using 2
--     rw [←WithTop.add_right_cancel_iff (a := (k : ℕ∞) - encard (E ∩ C)), tsub_add_cancel_of_le]
    
    

    

    
    
    
    
  -- rw [tsub_eq_zero_of_le hle, max_eq_left (zero_le _), unif_on_encard, unif_on_eq_of_le hle, 
  --   free_on_contract]
  
    

  -- lift k to ℕ using (hlt.trans_le le_top).ne 
  -- obtain (hinf | hfin) := E.finite_or_infinite.symm
  -- · rw [hinf.encard_eq, ENat.top_sub_coe, max_eq_right le_top, unif_on_top]
  -- rw [←dual_inj_iff, contract_dual_eq_dual_delete, unif_on_dual_eq]

      
  -- obtain (hlt | hle) := le_or_lt (encard (E ∩ C)) k
  -- · obtain (hfin | hinf) := E.finite_or_infinite
  --   · rw [←dual_inj_iff, contract_dual_eq_dual_delete, unif_on_dual_eq hfin, unif_on_delete_eq, 
  --       unif_on_dual_eq (hfin.diff _), ←encard_diff_add_encard_inter E C]
  --     sorry
  --   sorry
  -- rw [tsub_eq_zero_of_le hle.le, unif_on_zero, ←contract_inter_ground_eq, unif_on_ground_eq, 
  --   contract_eq_loopy_on_of_spanning (Base.spanning _), unif_on_ground_eq, diff_inter_self_eq_diff]
  
  -- rw [unif_on_base_iff (hle.le.trans (encard_mono (inter_subset_left _ _))) (inter_subset_right _ _)]

  -- simp_rw [eq_unif_on_iff, contract_ground, unif_on_ground_eq, true_and]
  -- refine' fun⟨fun h ↦ _, fun h ↦ _⟩

/-- A canonical uniform matroid, with rank `a` and ground type `Fin b`. -/
def unif (a b : ℕ) := unif_on (univ : Set (Fin b)) a 

@[simp] theorem unif_ground_eq (a b : ℕ) : (unif a b).E = univ := rfl 

@[simp] theorem unif_indep_iff (I) : (unif a b).Indep I ↔ I.encard ≤ a := by 
  rw [unif, unif_on_indep_iff, and_iff_left (subset_univ _)]

@[simp] theorem unif_er_eq (X) : (unif a b).er X = min X.encard a := by 
  rw [unif, unif_on_er_eq _ _ (subset_univ _)]
  
theorem unif_base_iff (hab : a ≤ b) : (unif a b).Base B ↔ B.encard = a := by
  rw [unif, unif_on, truncate_base_iff, free_on_indep_iff, and_iff_right (subset_univ _)]
  rwa [free_on_erk_eq, encard_univ, PartENat.card_eq_coe_fintype_card, Fintype.card_fin, 
    PartENat.withTopEquiv_natCast, Nat.cast_le]
  
@[simp] theorem unif_base_iff' : (unif a (a + b)).Base B ↔ B.encard = a := by 
  rw [unif_base_iff (Nat.le_add_right _ _)]
  
@[simp] theorem unif_dual' (h : a + b = n) : (unif a n)﹡ = unif b n := by
  subst h
  refine eq_of_base_iff_base_forall rfl (fun B _ ↦ ?_)
  rw [dual_base_iff, unif_ground_eq, unif_base_iff (Nat.le_add_right _ _), 
    unif_base_iff (Nat.le_add_left _ _), 
    ←WithTop.add_right_cancel_iff (encard_ne_top_iff.2 B.toFinite), 
    encard_diff_add_encard_of_subset (subset_univ _), Iff.comm, 
    ←WithTop.add_left_cancel_iff (WithTop.coe_ne_top (a := a)), eq_comm]
  convert Iff.rfl 
  rw [encard_univ, PartENat.card_eq_coe_fintype_card, Fintype.card_fin, 
    PartENat.withTopEquiv_natCast, ENat.some_eq_coe, eq_comm, Nat.cast_add]
  
theorem unif_dual (hab : a ≤ b) : (unif a b)﹡ = unif (b - a) b := 
  unif_dual' (Nat.add_sub_of_le hab)

@[simp] theorem unif_self_dual (a : ℕ) : (unif a (2*a))﹡ = unif a (2*a) := 
  unif_dual' (two_mul a).symm 

theorem isIso_unif_iff {a b : ℕ} (hb0 : b ≠ 0) {M : Matroid α} : 
    M ≃ (unif a b) ↔ (M = unif_on M.E a ∧ M.E.encard = (b : ℕ∞)) := by 
  rw [eq_unif_on_iff, and_iff_right rfl]
  refine ⟨fun ⟨e⟩ ↦ ⟨fun I ↦ ⟨fun hI ↦ ⟨?_,hI.subset_ground⟩,fun ⟨hle, hIE⟩ ↦ ?_⟩,?_⟩, 
    fun ⟨hI, hb⟩ ↦ ?_⟩ 
  · have hi := e.on_indep hI
    rwa [unif_indep_iff, encard_image_of_injOn (e.injOn_ground.mono hI.subset_ground)] at hi
  · apply e.on_indep_symm 
    rwa [unif_indep_iff, encard_image_of_injOn (e.injOn_ground.mono hIE)]
  · rw [←encard_image_of_injOn (e.injOn_ground), e.image_ground, unif_ground_eq, encard_univ]
    simp
  have hne : Nonempty (Fin b) := ⟨⟨0, Nat.pos_of_ne_zero hb0⟩⟩ 
  have hne' : Nonempty α := 
    ⟨(nonempty_of_encard_ne_zero (hb.trans_ne (Nat.cast_ne_zero.2 hb0))).some⟩ 
  have hfin := finite_of_encard_eq_coe hb
  rw [← (show (univ : Set (Fin b)).encard = b by simp [encard_univ])] at hb
  obtain ⟨f, hf⟩ := hfin.exists_bijOn_of_encard_eq hb
  refine ⟨iso_of_forall_indep' hf.toLocalEquiv rfl rfl fun I hIE ↦ ?_⟩ 
  simp only [BijOn.toLocalEquiv_apply, unif_indep_iff]
  rw [encard_image_of_injOn (hf.injOn.mono hIE), hI, and_iff_left hIE]
  


-- /-- Horrible proof. Should be improved using `simple` api -/
-- theorem iso_line_iff {k : ℕ} (hk : 2 ≤ k) : 
--   nonempty (M ≃i (unif 2 k)) ↔ 
--     (∀ e f ∈ M.E, M.indep {e,f}) ∧ M.rk = 2 ∧ M.E.finite ∧ M.E.ncard = k :=
-- begin
--   simp_rw [iso_unif_iff, encard_eq_coe_iff, ← and_assoc, and.congr_left_iff, 
--     set.eq_unif_on_iff, and_iff_right rfl, nat.cast_bit0, enat.coe_one], 
--   rintro rfl hfin, 
--   have lem : ∀ x y, ({x,y} : Set α).encard ≤ 2, 
--   { intros x y, 
--     rw [(({x,y} : Set α).to_finite.encard_eq), ←nat.cast_two, nat.cast_le],   
--     exact (ncard_insert_le _ _).trans (by simp) },
--   haveI : M.finite := ⟨hfin⟩, 
--   refine ⟨λ h, ⟨λ e he f hf, (h _).mpr ⟨lem _ _,_⟩,_⟩, λ h I, _⟩,
  
--   { rintro x ((rfl : x = e)| (rfl : x = f)); assumption  },
--   { rw [rk],
--     rw [←one_add_one_eq_two, nat.add_one_le_iff, one_lt_ncard_iff hfin] at hk, 
--     obtain ⟨a, b, ha, hb, hne⟩ := hk, 
--     have hss : {a,b} ⊆ M.E, by {rintro x ((rfl : x = a) | (rfl : x = b)); assumption}, 
--     have hlb := M.r_mono hss, 
--     rw [indep.r ((h _).mpr ⟨_, hss⟩), ncard_pair hne] at hlb, 
--     { refine hlb.antisymm' _, 
--       obtain ⟨B, hB⟩ := M.exists_base, 
--       rw [←rk, ←hB.card],
--       have h' := ((h B).mp hB.indep).1,
--       rw [←nat.cast_two, encard_le_coe_iff] at h', 
--       exact h'.2 },
--     apply lem },
--   rw [←nat.cast_two, encard_le_coe_iff], 
--   refine ⟨λ h', ⟨⟨h'.finite, _⟩, h'.subset_ground⟩, _⟩,
--   { rw [←h'.r, ←h.2], exact r_le_rk _ _ },
--   rintro ⟨⟨hfin, hcard⟩, hss⟩,  
--   rw [le_iff_eq_or_lt, nat.lt_iff_add_one_le, ncard_eq_two, ←one_add_one_eq_two, 
--     nat.add_le_add_iff_right, ncard_le_one_iff_eq hfin] at hcard, 
--   obtain (⟨x,y,-, rfl⟩ | rfl | ⟨e, rfl⟩ ) := hcard, 
--   { exact h.1 _ (hss (by simp)) _ (hss (by simp)) }, 
--   { simp }, 
--   convert h.1 e (hss (by simp)) e (hss (by simp)), 
--   simp, 
-- end 

-- section relax

-- -- def relax_set (M : Matroid α) (Hs : Set (set α)) := 
-- -- matroid_of_base M.E (λ B, M.base B ∨ (B ∈ Hs ∧ M.circuit B ∧ M.cocircuit (M.E \ B))) 
-- -- (M.exists_base.imp (λ _, or.inl)) 
-- -- (begin
-- --   intros B B' hB hB' e he, 
-- --   have hBE : B ⊆ M.E := hB.elim base.subset_ground (λ h', h'.2.1.subset_ground), 
-- --   by_cases hel : M.coloop e, sorry,
-- --   have h1 : M.indep (B \ {e}), sorry, 
-- --   obtain ⟨B₁, hB₁⟩ := h1.subset_basis_of_subset (diff_subset_diff_left hBE) (diff_subset _ _), 
-- --   have h2 : ¬M.base (B \ {e}), sorry, 
-- --   rw coloop_iff_forall_mem_base at hel, push_neg at hel, 
-- --   obtain ⟨B₁, hB₁, heB₁⟩ := hel, 
  

-- --   -- have h2 : ∃ B₂, M.base B₂ ∧ B \ {e} ⊆ B₂ ∧ B₂ ⊆ (B \ {e}) ∪ B', sorry, 
-- --   -- obtain ⟨B₂, hB₂, hssB₂, hB₂ss⟩ := h2, 
-- --   -- obtain ⟨B₃, hB₃, hB₃ss⟩ := h1.exists_base_supset, 
-- --   -- have := hB₃.exchange hB₂,  
-- --   -- have := hB₁.exchange hB₂, 
-- --   -- have h2 : ∃ x ∈ B' \ (B \ {e}), M.base (insert x (B \ {e})), 
-- --   -- {   },

-- --   -- obtain ⟨B1, hB1, hBeB1⟩ := h1.exists_base_supset,  
-- --   -- { have := hB1.exchange, },

  
-- --   -- obtain ⟨x, hx, hxB⟩ := h₁,  
-- --   -- have h' : ∃ B₁ ⊆ (B \ {e}) ∪ B', B \ {e} ⊆ B₁ ∧ M.base B₁, sorry, 

-- --   -- have heB : M.indep (B \ {e}), sorry, 
-- --   -- rintro B B' (hB | ⟨hB, hBc, hBk⟩) (hB' | ⟨hB', hBc', hBk'⟩) e ⟨heB, heB'⟩, 
  
-- --   -- { exact (hB.exchange hB' ⟨heB, heB'⟩).imp (λ f, Exists.imp (λ hf, or.inl)) },
-- --   -- { have h' : ∃ B₁ ⊆ (B \ {e}) ∪ B', M.base B₁, sorry, 
-- --   -- obtain ⟨B₁, hB₁ss, hB₁⟩ := h',  
-- --   -- obtain ⟨B₂, hB₂, hBB₂⟩ := heB.exists_base_supset, 
-- --   -- have := hB₂.exchange hB₁, 
-- --   -- have := hB₂.exchange hB₁ ⟨, 
-- --   --
-- --   --  have := hB.exchange hB₁, 
-- --   -- obtain ⟨f, hf, hBf⟩  := 
-- --   --   hB.exchange hB₁ ⟨heB, λ heB₁, (hB₁ss heB₁).elim (not_mem_diff_singleton _ _) _⟩, 
-- --   --   exact ⟨f, ⟨(hB₁ss hf.1).elim (λ h', (hf.2 h'.1).elim) id, hf.2⟩, or.inl hBf⟩ },
  
-- -- end) sorry sorry 

-- end relax

end Uniform

end Matroid 