import Matroid.Flat

variable {α : Type _} {M : Matroid α} {E : Set α}

namespace Matroid

open Set

section EmptyOn

/-- The `Matroid α` with empty ground set-/
def emptyOn (α : Type _) : Matroid α :=
  matroid_of_base_of_finite finite_empty (· = ∅) ⟨_,rfl⟩ (by rintro _ _ rfl; simp) (by simp)

@[simp] theorem emptyOn_ground : (emptyOn α).E = ∅ := rfl

@[simp] theorem emptyOn_base_iff : (emptyOn α).Base B ↔ B = ∅ := by
  simp [emptyOn]

@[simp] theorem emptyOn_indep_iff : (emptyOn α).Indep B ↔ B = ∅ := by
  simp [indep_iff_subset_base, subset_empty_iff]

@[simp] theorem ground_eq_empty_iff : (M.E = ∅) ↔ M = emptyOn α := by
  refine' ⟨fun h ↦ eq_of_base_iff_base_forall (by simp [h]) _, fun h ↦ by simp [h]⟩
  simp only [h, subset_empty_iff, emptyOn_base_iff, forall_eq, iff_true]
  obtain ⟨B', hB'⟩ := M.exists_base
  rwa [←eq_empty_of_subset_empty (hB'.subset_ground.trans_eq h)]

@[simp] theorem emptyOn_dual_eq : (emptyOn α)﹡ = emptyOn α := by
  rw [← ground_eq_empty_iff]; rfl

/-- Any two empty matroids are isomorphic -/
noncomputable def Iso.of_empty (α β : Type _) [_root_.Nonempty α] [_root_.Nonempty β] :
    Iso (emptyOn α) (emptyOn β) where
  toLocalEquiv := InjOn.toLocalEquiv _ _ (injOn_empty (Classical.arbitrary (α → β)))
  source_eq' := by simp
  target_eq' := by simp
  setOf_base_eq' := by ext B; simp [eq_comm (a := ∅)]

@[simp] theorem delete_ground_self (M : Matroid α) : M ⟍ M.E = emptyOn α := by
  simp [←ground_eq_empty_iff]

@[simp] theorem contract_ground_self (M : Matroid α) : M ⟋ M.E = emptyOn α := by
  simp [←ground_eq_empty_iff]

@[simp] theorem restrict_to_empty (M : Matroid α) : M ↾ (∅ : Set α) = emptyOn α := by
  simp [←ground_eq_empty_iff]

@[simp] theorem empty_minor (M : Matroid α) : (emptyOn α) ≤m M :=
  ⟨M.E, ∅, by simp [rfl.subset]⟩

@[simp] theorem minor_empty_iff : M ≤m emptyOn α ↔ M = emptyOn α :=
  ⟨fun h ↦ ground_eq_empty_iff.1 (eq_empty_of_subset_empty h.subset),
    by rintro rfl; apply empty_minor⟩

theorem eq_emptyOn_or_nonempty (M : Matroid α) : M = emptyOn α ∨ Matroid.Nonempty M := by
  rw [←ground_eq_empty_iff]
  exact M.E.eq_empty_or_nonempty.elim Or.inl (fun h ↦ Or.inr ⟨h⟩)

end EmptyOn

section LoopyOn

/-- The `Matroid α` with ground set `E` whose only base is `∅` -/
def loopyOn (E : Set α) : Matroid α := (emptyOn α ↾ E)

@[simp] theorem loopyOn_ground (E : Set α) : (loopyOn E).E = E := rfl

@[simp] theorem loopyOn_indep_iff : (loopyOn E).Indep I ↔ I = ∅ := by
  simp only [loopyOn, restrict_indep_iff, emptyOn_indep_iff, and_iff_left_iff_imp]
  rintro rfl; apply empty_subset

@[simp] theorem loopyOn_base_iff : (loopyOn E).Base B ↔ B = ∅ := by
  simp only [base_iff_maximal_indep, loopyOn_indep_iff, forall_eq, and_iff_left_iff_imp]
  exact fun h _ ↦ h

@[simp] theorem loopyOn_er_eq (E X : Set α) : (loopyOn E).er X = 0 := by
  obtain ⟨I, hI⟩ := (loopyOn E).exists_basis' X
  rw [hI.er_eq_encard, loopyOn_indep_iff.1 hI.indep, encard_empty]

@[simp] theorem loopyOn_erk_eq (E : Set α) : (loopyOn E).erk = 0 := by
  rw [erk_eq_er_ground, loopyOn_er_eq]

@[simp] theorem loopyOn_r_eq (E X : Set α) : (loopyOn E).r X = 0 := by
  rw [←er_toNat_eq_r, loopyOn_er_eq]; rfl

@[simp] theorem loopyOn_basis_iff : (loopyOn E).Basis I X ↔ I = ∅ ∧ X ⊆ E :=
  ⟨fun h ↦⟨loopyOn_indep_iff.mp h.indep, h.subset_ground⟩,
    by rintro ⟨rfl, hX⟩; rw [basis_iff]; simp⟩

@[simp] theorem loopyOn_cl_eq (E X : Set α) : (loopyOn E).cl X = E :=
  (cl_subset_ground _ _).antisymm
    (subset_trans (by rw [(loopyOn_base_iff.2 rfl).cl_eq]) (cl_subset_cl _ (empty_subset _)))

@[simp] theorem cl_empty_eq_ground_iff : M.cl ∅ = M.E ↔ M = loopyOn M.E := by
  refine ⟨fun h ↦ eq_of_cl_eq_cl_forall ?_, fun h ↦ by rw [h, loopyOn_cl_eq, loopyOn_ground]⟩
  refine fun X ↦ subset_antisymm (by simp [cl_subset_ground]) ?_
  rw [loopyOn_cl_eq, ←h]
  exact M.cl_mono (empty_subset _)

@[simp] theorem erk_eq_zero_iff : M.erk = 0 ↔ M = loopyOn M.E := by
  refine ⟨fun h ↦ cl_empty_eq_ground_iff.1 ?_, fun h ↦ by rw [h, loopyOn_erk_eq]⟩
  obtain ⟨B, hB⟩ := M.exists_base
  rw [←hB.encard, encard_eq_zero] at h
  rw [←h, hB.cl_eq]

@[simp] theorem empty_base_iff : M.Base ∅ ↔ M = loopyOn M.E :=
  ⟨fun h ↦ by rw [←cl_empty_eq_ground_iff, h.cl_eq], fun h ↦ by rw [h, loopyOn_base_iff]⟩

theorem eq_loopyOn_iff_cl : M = loopyOn E ↔ M.cl ∅ = E ∧ M.E = E :=
  ⟨fun h ↦ by rw [h]; simp, fun ⟨h,h'⟩ ↦ by rw [←h', ←cl_empty_eq_ground_iff, h, h']⟩

theorem eq_loopyOn_iff_erk : M = loopyOn E ↔ M.erk = 0 ∧ M.E = E :=
  ⟨fun h ↦ by rw [h]; simp, fun ⟨h,h'⟩ ↦ by rw [←h', ←erk_eq_zero_iff, h]⟩

instance : FiniteRk (loopyOn E) :=
  ⟨⟨∅, loopyOn_base_iff.2 rfl, finite_empty⟩⟩

theorem Finite.loopyOn_finite (hE : E.Finite) : Matroid.Finite (loopyOn E) :=
  ⟨hE⟩

@[simp] theorem loopyOn_restrict (E R : Set α) : (loopyOn E) ↾ R = loopyOn R := by
  have h0 : ((loopyOn E) ↾ R).erk = 0
  · rw [erk_eq_er_ground, restrict_er_eq', loopyOn_er_eq]
  rwa [erk_eq_zero_iff, restrict_ground_eq] at h0

@[simp] theorem loopyOn_delete (E X : Set α) : (loopyOn E) ⟍ X = loopyOn (E \ X) := by
  rw [←restrict_compl, loopyOn_restrict, loopyOn_ground]

@[simp] theorem loopyOn_contract (E X : Set α) : (loopyOn E) ⟋ X = loopyOn (E \ X) := by
  simp_rw [eq_loopyOn_iff_cl, contract_cl_eq, empty_union, loopyOn_cl_eq, contract_ground,
    loopyOn_ground]

@[simp] theorem loopyOn_minor : M ≤m loopyOn E ↔ M = loopyOn M.E ∧ M.E ⊆ E := by
  refine ⟨fun h ↦ ⟨by obtain ⟨C, D, _, _, _, rfl⟩ := h; simp, h.subset⟩, fun ⟨h, hss⟩ ↦ ?_⟩

  convert (loopyOn E).restrict_minor hss using 1
  rw [h, loopyOn_ground, loopyOn_restrict]

theorem contract_eq_loopyOn_of_spanning (h : M.Spanning C) : M ⟋ C = loopyOn (M.E \ C) := by
  rw [eq_loopyOn_iff_cl, contract_ground, and_iff_left rfl, contract_cl_eq, empty_union, h.cl_eq]

theorem eq_loopyOn_or_rkPos (M : Matroid α) : M = loopyOn M.E ∨ RkPos M := by
  rw [←empty_base_iff, rkPos_iff_empty_not_base]; apply em

theorem not_rkPos_iff : ¬RkPos M ↔ M = loopyOn M.E := by
  rw [rkPos_iff_empty_not_base, not_iff_comm, empty_base_iff]

end LoopyOn

section FreeOn

/-- The `Matroid α` with ground set `E` whose only base is `E`. -/
def freeOn (E : Set α) : Matroid α := (loopyOn E)﹡

@[simp] theorem freeOn_ground : (freeOn E).E = E := rfl

@[simp] theorem freeOn_dual_eq : (freeOn E)﹡ = loopyOn E := by
  rw [freeOn, dual_dual]

@[simp] theorem loopyOn_dual_eq : (loopyOn E)﹡ = freeOn E := rfl

@[simp] theorem freeOn_base_iff : (freeOn E).Base B ↔ B = E := by
  simp only [freeOn, loopyOn_ground, dual_base_iff', loopyOn_base_iff, diff_eq_empty,
    ←subset_antisymm_iff, eq_comm (a := E)]

@[simp] theorem freeOn_indep_iff : (freeOn E).Indep I ↔ I ⊆ E := by
  simp [indep_iff_subset_base]

theorem freeOn_indep (hIE : I ⊆ E) : (freeOn E).Indep I :=
  freeOn_indep_iff.2 hIE

@[simp] theorem freeOn_erk_eq (E : Set α) : (freeOn E).erk = E.encard := by
  rw [erk_eq_er_ground, freeOn_ground, (freeOn_indep_iff.2 rfl.subset).er]

@[simp] theorem freeOn_basis_iff : (freeOn E).Basis I X ↔ I = X ∧ X ⊆ E := by
  use fun h ↦ ⟨(freeOn_indep h.subset_ground).eq_of_basis h ,h.subset_ground⟩
  rintro ⟨rfl, hIE⟩
  exact (freeOn_indep hIE).basis_self

@[simp] theorem freeOn_basis'_iff : (freeOn E).Basis' I X ↔ I = X ∩ E := by
  rw [basis'_iff_basis_inter_ground, freeOn_basis_iff, freeOn_ground,
    and_iff_left (inter_subset_right _ _)]

theorem freeOn_er_eq (hXE : X ⊆ E) : (freeOn E).er X = X.encard := by
  obtain ⟨I, hI⟩ := (freeOn E).exists_basis X
  rw [hI.er_eq_encard, (freeOn_indep hXE).eq_of_basis hI]

theorem freeOn_r_eq (hXE : X ⊆ E) : (freeOn E).r X = X.ncard := by
  rw [←er_toNat_eq_r, freeOn_er_eq hXE, ncard_def]

@[simp] theorem ground_indep_iff_eq_freeOn : M.Indep M.E ↔ M = freeOn M.E :=
  ⟨fun h ↦ eq_of_indep_iff_indep_forall rfl fun I hI ↦ by simp [hI, h.subset hI],
    fun h ↦ by rw [h]; simp [rfl.subset]⟩

@[simp] theorem girth_eq_top_iff_freeOn [Finitary M] : M.girth = ⊤ ↔ M = freeOn M.E := by
  rw [←ground_indep_iff_eq_freeOn, girth_eq_top_iff, indep_iff_forall_subset_not_circuit]
  exact ⟨fun h C _ hC ↦ h C hC hC.finite, fun h C hC _ ↦ h C hC.subset_ground hC⟩

@[simp] theorem freeOn_delete (E X : Set α) : (freeOn E) ⟍ X = freeOn (E \ X) := by
  rw [←loopyOn_dual_eq, ←contract_dual_eq_dual_delete, loopyOn_contract, loopyOn_dual_eq]

theorem freeOn_restrict (h : R ⊆ E) : (freeOn E) ↾ R = freeOn R := by
  rw [←delete_compl, freeOn_delete, freeOn_ground, diff_diff_cancel_left h]

@[simp] theorem freeOn_contract (E X : Set α) : (freeOn E) ⟋ X = freeOn (E \ X) := by
  rw [←loopyOn_dual_eq, ←delete_dual_eq_dual_contract, loopyOn_delete, loopyOn_dual_eq]

end FreeOn

section TrivialOn

/-- The matroid on `E` whose unique base is the subset `I` of `E`.  (If `I` is not a subset of `E`,
  the base is `I ∩ E` )-/
def trivialOn (I E : Set α) : Matroid α := (freeOn I) ↾ E

@[simp] theorem trivialOn_ground : (trivialOn I E).E = E :=
  rfl

theorem trivialOn_base_iff (hIE : I ⊆ E) : (trivialOn I E).Base B ↔ B = I := by
  rw [trivialOn, base_restrict_iff', freeOn_basis'_iff, inter_eq_self_of_subset_right hIE]

theorem trivialOn_inter_ground_eq (I E : Set α) :
    trivialOn (I ∩ E) E = trivialOn I E := by
  simp only [trivialOn, restrict_eq_restrict_iff, freeOn_indep_iff, subset_inter_iff,
    iff_self_and]
  tauto

@[simp] theorem trivialOn_indep_iff' : (trivialOn I E).Indep J ↔ J ⊆ I ∩ E := by
  rw [trivialOn, restrict_indep_iff, freeOn_indep_iff, subset_inter_iff]

theorem trivialOn_indep_iff (hIE : I ⊆ E) : (trivialOn I E).Indep J ↔ J ⊆ I := by
  rw [trivialOn, restrict_indep_iff, freeOn_indep_iff, and_iff_left_iff_imp]
  exact fun h ↦ h.trans hIE

theorem trivialOn_basis_iff (hI : I ⊆ E) (hX : X ⊆ E) :
    (trivialOn I E).Basis J X ↔ J = X ∩ I := by
  rw [basis_iff_mem_maximals]
  simp_rw [trivialOn_indep_iff', ←subset_inter_iff, ←le_eq_subset, Iic_def, maximals_Iic,
    mem_singleton_iff, inter_eq_self_of_subset_left hI, inter_comm I]

theorem trivialOn_inter_basis (hI : I ⊆ E) (hX : X ⊆ E) : (trivialOn I E).Basis (X ∩ I) X := by
  rw [trivialOn_basis_iff hI hX]

@[simp] theorem trivialOn_dual_eq (I E : Set α) : (trivialOn I E)﹡ = trivialOn (E \ I) E := by
  rw [←trivialOn_inter_ground_eq]
  refine eq_of_base_iff_base_forall rfl (fun B (hB : B ⊆ E) ↦ ?_)
  rw [dual_base_iff, trivialOn_base_iff (inter_subset_right _ _),
    trivialOn_base_iff (diff_subset _ _), trivialOn_ground]
  refine' ⟨fun h ↦ _, fun h ↦ _⟩
  · rw [←diff_diff_cancel_left hB, h, diff_inter_self_eq_diff]
  rw [h, inter_comm I]; simp

@[simp] theorem trivialOn_cl_eq (I E X : Set α) :
    (trivialOn I E).cl X = (X ∩ I ∩ E) ∪ (E \ I) := by
  have hb := (trivialOn_basis_iff (inter_subset_right I E) (inter_subset_right X E)).mpr rfl
  ext e

  rw [←trivialOn_inter_ground_eq I E, cl_eq_cl_inter_ground _ X, trivialOn_ground,
    ←hb.cl_eq_cl, hb.indep.mem_cl_iff, dep_iff, trivialOn_indep_iff', insert_subset_iff,
    trivialOn_ground, inter_assoc, inter_self,  and_iff_left (inter_subset_right _ _),
    ←inter_inter_distrib_right, inter_assoc, union_distrib_right, inter_comm I, inter_union_diff,
    insert_subset_iff, inter_comm X, inter_assoc, and_iff_left (inter_subset_left _ _),
    mem_inter_iff]
  simp only [not_and, mem_inter_iff, mem_union, mem_diff]
  tauto

theorem eq_trivialOn_of_loops_union_coloops (hE : M.E = M.cl ∅ ∪ M﹡.cl ∅) :
    M = trivialOn (M﹡.cl ∅) M.E := by
  refine eq_of_base_iff_base_forall rfl (fun B hBE ↦ ?_)
  rw [trivialOn_base_iff (show M﹡.cl ∅ ⊆ M.E from M﹡.cl_subset_ground _)]
  rw [hE, ←diff_subset_iff] at hBE
  use fun h ↦ h.coloops_subset.antisymm' (by rwa [sdiff_eq_left.mpr h.indep.disjoint_loops] at hBE)
  rintro rfl
  obtain ⟨B, hB⟩ := M.exists_base
  rwa [hB.coloops_subset.antisymm ]
  refine subset_trans ?_ (diff_subset_iff.2 hE.subset)
  rw [subset_diff, and_iff_right hB.subset_ground]
  exact hB.indep.disjoint_loops

theorem trivialOn_loops_eq (I E : Set α) : (trivialOn I E).cl ∅ = E \ I := by
  simp

@[simp] theorem trivialOn_coloops_eq' (I E : Set α) : (trivialOn I E)﹡.cl ∅ = I ∩ E := by
  simp [inter_comm I]

theorem trivialOn_coloops_eq (h : I ⊆ E) : (trivialOn I E)﹡.cl ∅ = I := by
  simp [h]

@[simp] theorem trivialOn_self (I : Set α) : (trivialOn I I) = freeOn I := by
  rw [trivialOn, freeOn_restrict rfl.subset]

@[simp] theorem trivialOn_empty (I : Set α) : (trivialOn ∅ I) = loopyOn I := by
  rw [←dual_inj_iff, trivialOn_dual_eq, diff_empty, trivialOn_self, loopyOn_dual_eq]

@[simp] theorem trivialOn_restrict' (I E R : Set α) :
    (trivialOn I E) ↾ R = trivialOn (I ∩ R ∩ E) R := by
  simp_rw [eq_iff_indep_iff_indep_forall, restrict_ground_eq, trivialOn_ground, true_and,
    restrict_indep_iff, trivialOn_indep_iff', subset_inter_iff]
  tauto

theorem trivialOn_restrict (h : I ⊆ E) (R : Set α) :
    (trivialOn I E) ↾ R = trivialOn (I ∩ R) R := by
  rw [trivialOn_restrict', inter_right_comm, inter_eq_self_of_subset_left h]

@[simp] theorem trivialOn_delete (I E D : Set α) :
    (trivialOn I E) ⟍ D = trivialOn (I \ D) (E \ D) := by
  rw [←restrict_compl, trivialOn_restrict', trivialOn_ground, inter_assoc,
    inter_eq_self_of_subset_left (diff_subset _ _), eq_comm, ←trivialOn_inter_ground_eq,
    diff_inter_diff_right, inter_diff_assoc]

@[simp] theorem trivialOn_contract (I E C : Set α) :
    (trivialOn I E) ⟋ C = trivialOn (I \ C) (E \ C) := by
  rw [←dual_inj_iff, contract_dual_eq_dual_delete, trivialOn_dual_eq, trivialOn_delete,
    diff_diff_comm, ←trivialOn_dual_eq, dual_inj_iff, ←trivialOn_inter_ground_eq, eq_comm,
    ←trivialOn_inter_ground_eq, diff_inter_diff_right, inter_diff_assoc]

theorem trivialOn_of_minor (h : M ≤m trivialOn I E) : ∃ I₀, M = trivialOn I₀ M.E := by
  obtain ⟨C, D, -, -, -, rfl⟩ := h
  simp only [trivialOn_contract, trivialOn_delete, trivialOn_ground]
  exact ⟨_, rfl⟩

@[simp] theorem trivialOn_eq_freeOn : trivialOn E E = freeOn E := by
  rw [trivialOn, restrict_eq_self_iff, freeOn_ground]

@[simp] theorem trivialOn_eq_loopyOn : trivialOn ∅ E = loopyOn E := by
  simp [eq_iff_indep_iff_indep_forall]

end TrivialOn
