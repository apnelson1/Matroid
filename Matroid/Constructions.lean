import Matroid.Rank

variable {α : Type _} {M : Matroid α} {E : Set α}

namespace Matroid 

open Set 

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

@[simp] theorem loopy_on_r_eq (E X : Set α) : (loopy_on E).r X = 0 := by 
  rw [←er_toNat_eq_r, loopy_on_er_eq]; rfl 

@[simp] theorem loopy_on_basis_iff : (loopy_on E).Basis I X ↔ I = ∅ ∧ X ⊆ E :=
  ⟨fun h ↦⟨loopy_on_indep_iff.mp h.indep, h.subset_ground⟩, 
    by rintro ⟨rfl, hX⟩; rw [basis_iff]; simp⟩ 

@[simp] theorem loopy_on_cl_eq (E X : Set α) : (loopy_on E).cl X = E := 
  (cl_subset_ground _ _).antisymm 
    (subset_trans (by rw [(loopy_on_base_iff.2 rfl).cl_eq]) (cl_subset_cl _ (empty_subset _)))

@[simp] theorem eq_loopy_on_iff_cl_empty_eq_ground : M = loopy_on E ↔ M.E = E ∧ M.cl ∅ = E := by
  refine' ⟨fun h ↦ by simp [h], fun h ↦ eq_of_cl_eq_cl_forall (fun X ↦ _)⟩
  rw [←h.1, loopy_on_cl_eq, subset_antisymm_iff, and_iff_right (M.cl_subset_ground _), 
    h.1, ←h.2]
  exact M.cl_mono (empty_subset _)


instance : FiniteRk (loopy_on E) := 
  ⟨⟨∅, loopy_on_base_iff.2 rfl, finite_empty⟩⟩ 

theorem Finite.loopy_on_finite (hE : E.Finite) : Finite (loopy_on E) := 
  ⟨hE⟩ 

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
  
/-- The matroid on `E` whose unique base is the subset `I` of `E`.  (If `I` is not a subset of `E`, 
  the base is `I ∩ E` )-/
def trivial_on (I E : Set α) : Matroid α := (free_on I) ↾ E 

@[simp] theorem trivial_on_ground : (trivial_on I E).E = E := 
  rfl 

theorem trivial_on_base_iff (hIE : I ⊆ E) : (trivial_on I E).Base B ↔ B = I := by
  rw [trivial_on, restrict_base_iff', free_on_basis'_iff, inter_eq_self_of_subset_right hIE]

theorem trivial_on_eq_trivial_on_inter_ground (I E : Set α) :
    trivial_on I E = trivial_on (I ∩ E) E := by
  simp_rw [trivial_on, restrict_eq_restrict_iff, free_on_indep_iff, subset_inter_iff, iff_self_and]
  tauto

theorem trivial_on_indep_iff' : (trivial_on I E).Indep J ↔ J ⊆ I ∩ E := by
  rw [trivial_on, restrict_indep_iff, free_on_indep_iff, subset_inter_iff]

theorem trivial_on_indep_iff (hIE : I ⊆ E) : (trivial_on I E).Indep J ↔ J ⊆ I := by
  rw [trivial_on, restrict_indep_iff, free_on_indep_iff, and_iff_left_iff_imp]
  exact fun h ↦ h.trans hIE
  
theorem trivial_on_basis_iff (hI : I ⊆ E) (hX : X ⊆ E) : (trivial_on I E).Basis J X ↔ J = X ∩ I := by
  rw [basis_iff_mem_maximals]
  simp_rw [trivial_on_indep_iff', ←subset_inter_iff, ←le_eq_subset, Iic_def, maximals_Iic, 
    mem_singleton_iff, inter_eq_self_of_subset_left hI, inter_comm I]

theorem trivial_on_inter_basis (hI : I ⊆ E) (hX : X ⊆ E) : (trivial_on I E).Basis (X ∩ I) X := by
  rw [trivial_on_basis_iff hI hX]
  
@[simp] theorem trivial_on_dual_eq (I E : Set α) : (trivial_on I E)﹡ = trivial_on (E \ I) E := by
  rw [trivial_on_eq_trivial_on_inter_ground]
  refine eq_of_base_iff_base_forall rfl (fun B (hB : B ⊆ E) ↦ ?_)
  rw [dual_base_iff, trivial_on_base_iff (inter_subset_right _ _), 
    trivial_on_base_iff (diff_subset _ _), trivial_on_ground]
  refine' ⟨fun h ↦ _, fun h ↦ _⟩
  · rw [←diff_diff_cancel_left hB, h, diff_inter_self_eq_diff]
  rw [h, inter_comm I]; simp 
  

-- @[simp] theorem girth_eq_zero_iff_free_on [finitary M] : M.girth = 0 ↔ M = free_on M.E :=
-- begin
--   rw [←ground_indep_iff_eq_free_on, girth_eq_zero_iff, indep_iff_forall_subset_not_circuit], 
--   exact ⟨λ h C hCE hC, h C hC hC.finite, λ h C hC hi, h C hC.subset_ground hC⟩,
-- end 

-- /-- The matroid on `α` with empty ground Set -/
-- def empty (α : Type*) : Matroid α := Matroid.loopy_on ∅ 

-- theorem ground_eq_empty_iff_eq_empty : M.E = ∅ ↔ M = empty α := 
-- begin
--   simp_rw [eq_iff_indep_iff_indep_forall, empty, loopy_on_ground, loopy_on_indep_iff, iff_self_and], 
--   rintro he I hI, 
--   rw [he, subset_empty_iff] at hI, 
--   simp [hI], 
-- end 

-- @[simp] theorem empty_ground : (empty α).E = ∅ := rfl  

-- @[simp] theorem empty_base_iff : (empty α).base B ↔ B = ∅ := 
-- by simp [empty]

-- /-- Any two empty matroids are isomorphic -/
-- def iso.of_empty (α β : Type*) : (empty α) ≃i (empty β) :=
-- { to_equiv := by {convert equiv.equiv_of_is_empty (∅ : Set α) (∅ : Set β)},
--   on_base' := by simp }

-- @[simp] theorem restrict_empty (M : Matroid α) : M ‖ (∅ : Set α) = empty α :=
-- by simp [←ground_eq_empty_iff_eq_empty]

-- @[simp] theorem dual_empty : (empty α)﹡ = empty α := 
-- by simp [←ground_eq_empty_iff_eq_empty]

-- @[simp] theorem delete_ground_eq_empty (M : Matroid α) : M ⟍ M.E = empty α :=
-- by simp [←ground_eq_empty_iff_eq_empty]

-- @[simp] theorem contract_ground_eq_empty (M : Matroid α) : M ⟋ M.E = empty α :=
-- by simp [←ground_eq_empty_iff_eq_empty]

-- end trivial 

-- /-- The truncation of a matroid to finite rank `k`. The independent sets of the truncation
--   are the independent sets of the matroid of size at most `k`. -/
-- def truncate (M : Matroid α) (k : ℕ) : Matroid α := 
-- matroid_of_indep_of_bdd' M.E (λ I, M.indep I ∧ I.finite ∧ I.ncard ≤ k) 
-- (by simp)
-- (λ I J h hIJ, ⟨h.1.subset hIJ, h.2.1.subset hIJ, (ncard_le_of_subset hIJ h.2.1).trans h.2.2⟩ )
-- (begin
--   rintro I J ⟨hI, hIfin, hIc⟩ ⟨hJ, hJfin, hJc⟩ hIJ, 
--   obtain ⟨e, heJ, heI, hi⟩ := hI.augment_of_finite hJ hIfin hIJ, 
--   refine ⟨e, heJ, heI, hi, hIfin.insert e, (ncard_insert_le _ _).trans _⟩, 
--   rw [nat.add_one_le_iff], 
--   exact hIJ.trans_le hJc, 
-- end) 
-- (⟨k, λ I, and.right⟩)
-- (λ I hI, hI.1.subset_ground)

-- @[simp] theorem truncate_indep_iff : (M.truncate k).indep I ↔ (M.indep I ∧ I.finite ∧ I.ncard ≤ k) := 
-- by simp [truncate]

-- @[simp] theorem truncate_ground_eq : (M.truncate k).E = M.E := rfl 

-- theorem truncate_base_iff [finite_rk M] (h : k ≤ M.rk) :
--   (M.truncate k).base B ↔ M.indep B ∧ B.ncard = k :=
-- begin
--   simp_rw [base_iff_maximal_indep, truncate_indep_iff, and_imp], 
--   split, 
--   { rintro ⟨⟨hBi, hBin, hBc⟩, hBmax⟩, 
--     refine ⟨hBi, hBc.antisymm _⟩, 
--     obtain ⟨B', hB', hBB'⟩ := hBi.exists_base_supset, 
--     rw ←hB'.card at h, 
--     obtain ⟨J, hBJ, hJB', rfl⟩ := exists_intermediate_set' hBc h hBB', 
--     rw hBmax J (hB'.indep.subset hJB') (hB'.finite.subset hJB') rfl.le hBJ },
--   rintro ⟨hB, rfl⟩, 
--   exact ⟨⟨hB, hB.finite, rfl.le⟩, λ I hI hIfin hIc hBI, eq_of_subset_of_ncard_le hBI hIc hIfin⟩, 
-- end 

-- theorem truncate_base_iff_of_infinite_rk [infinite_rk M] :
--   (M.truncate k).base B ↔ M.indep B ∧ B.finite ∧ B.ncard = k :=
-- begin
--   simp_rw [base_iff_maximal_indep, truncate_indep_iff, and_imp], 
--   split, 
--   { rintro ⟨⟨hBi, hBfin, hBc⟩, hBmax⟩, 
--     refine ⟨hBi, hBfin, hBc.antisymm _⟩, 
--     obtain ⟨B', hB', hBB'⟩ := hBi.exists_base_supset, 
--     obtain ⟨J, hBJ, hJB', hJfin, rfl⟩ := hB'.infinite.exists_supset_ncard_eq' hBB' hBfin hBc, 
--     rw hBmax J (hB'.indep.subset hJB') hJfin rfl.le hBJ, },
--   rintro ⟨hB, hBfin, rfl⟩, 
--   exact ⟨⟨hB, hBfin, rfl.le⟩, λ I hI hIfin hIc hBI, eq_of_subset_of_ncard_le hBI hIc hIfin⟩, 
-- end 

-- instance truncate.finite [finite M] : finite (M.truncate k) := 
-- ⟨ by simp [ground_finite M] ⟩ 

-- instance truncate.finite_rk : finite_rk (M.truncate k) := 
-- ⟨ let ⟨B, hB⟩ := (M.truncate k).exists_base in ⟨B, hB, (truncate_indep_iff.mp hB.indep).2.1⟩ ⟩ 

-- theorem indep.of_truncate (h : (M.truncate k).indep I) : M.indep I := 
-- by { rw [truncate_indep_iff] at h, exact h.1 }

-- theorem indep.ncard_le_of_truncate (h : (M.truncate k).indep I) : I.ncard ≤ k := 
-- (truncate_indep_iff.mp h).2.2

-- theorem r_fin.truncate_r_eq (hX : M.r_fin X) (k : ℕ) : (M.truncate k).r X = min (M.r X) k := 
-- begin
--   rw [r_eq_r_inter_ground, truncate_ground_eq, M.r_eq_r_inter_ground], 
--   have hX' := hX.inter_right M.E, 
--   obtain ⟨I, hI⟩ := (M.truncate k).exists_basis (X ∩ M.E),
--   have hi := truncate_indep_iff.mp hI.indep, 
--   obtain ⟨J, hJ, hIJ⟩ := hi.1.subset_basis_of_subset hI.subset, 
--   rw [←hI.card, le_antisymm_iff, le_min_iff, and_iff_left hi.2.2, min_le_iff, ←hi.1.r, 
--     and_iff_right (hX'.r_mono (hIJ.trans hJ.subset)), ←hJ.card, hi.1.r], 
--   by_contra' h, 
--   obtain ⟨e, heJ, heI⟩ := exists_mem_not_mem_of_ncard_lt_ncard h.1 hI.indep.finite, 
--   rw hI.eq_of_subset_indep _ (subset_insert e I) (insert_subset.mpr ⟨hJ.subset heJ,hI.subset⟩) 
--     at heI, 
--   { exact heI (mem_insert _ _) },
--   rw truncate_indep_iff, 
--   refine ⟨hJ.indep.subset (insert_subset.mpr ⟨heJ, hIJ⟩), hI.finite.insert e, _⟩, 
--   exact (ncard_insert_le _ _).trans (nat.add_one_le_iff.mpr h.2), 
-- end 

-- theorem truncate_r_eq [finite_rk M] (k : ℕ) (X : Set α) : (M.truncate k).r X = min (M.r X) k := 
-- begin
--   rw [r_eq_r_inter_ground, M.r_eq_r_inter_ground, truncate_ground_eq], 
--   exact (M.to_r_fin (X ∩ M.E)).truncate_r_eq _, 
-- end 

-- -- theorem truncate_r_eq_of_not_r_fin (hX : ¬M.r_fin X) (k : ℕ) (hXE : X ⊆ M.E . ssE) :
-- --   (M.truncate k).r X = k :=
-- -- begin
-- --   obtain ⟨I, hI⟩ := M.exists_basis X, 
-- --   obtain ⟨J, hJI, hJfin, rfl⟩ := (hI.infinite_of_not_r_fin hX).exists_subset_ncard_eq k, 
-- --   have hJfin' := M.r_fin_of_finite hJfin (hJI.trans hI.subset_ground_left), 
-- --   have hJi : (M.truncate J.ncard).indep J, by simp [hI.indep.subset hJI, hJfin],
-- --   obtain ⟨J', hJJ', hJ'⟩ := hJi.subset_basis_of_subset (hJI.trans hI.subset), 
-- --   rw [←hJJ'.card, eq_of_subset_of_ncard_le hJ' _ hJJ'.indep.finite], 
-- --   exact hJJ'.indep.ncard_le_of_truncate, 
-- -- end 

-- /-- A uniform matroid with a given rank and ground Set -/
-- def set.unif_on (E : Set α) (k : ℕ) := (free_on E).truncate k 

-- @[simp] theorem set.unif_on_ground_eq : (E.unif_on k).E = E := rfl 

-- @[simp] theorem set.unif_on_indep_iff : (E.unif_on k).indep I ↔ I.finite ∧ I.ncard ≤ k ∧ I ⊆ E :=
-- by simp [set.unif_on, and_comm (I ⊆ E), and_assoc]

-- theorem set.unif_on_indep_iff' : (E.unif_on k).indep I ↔ I.encard ≤ k ∧ I ⊆ E := 
-- by rw [encard_le_coe_iff, set.unif_on_indep_iff, and_assoc]

-- theorem set.unif_on_base_iff_of_finite (hE : E.finite) (hk : k ≤ E.ncard) (hBE : B ⊆ E) : 
--   (E.unif_on k).base B ↔ B.ncard = k :=
-- by { haveI := free_on_finite hE, rw [set.unif_on, truncate_base_iff], simp [hBE], simpa }

-- theorem set.unif_on_r_eq_of_finite (E : Set α) (k : ℕ) {X : Set α} (hX : X ⊆ E) (hXfin : X.finite) : 
--   (E.unif_on k).r X = min X.ncard k := 
-- begin
--   rw [set.unif_on, r_fin.truncate_r_eq, free_on_r_eq hX], 
--   exact (free_on E).r_fin_of_finite hXfin
-- end 

-- theorem set.eq_unif_on_iff : M = E.unif_on a ↔ M.E = E ∧ ∀ I, M.indep I ↔ I.encard ≤ a ∧ I ⊆ E := 
-- begin
--   simp_rw [eq_iff_indep_iff_indep_forall, set.unif_on_ground_eq, set.unif_on_indep_iff', 
--     and.congr_right_iff],  
--   rintro rfl, 
--   exact ⟨λ h I, ⟨λ hI, (h I hI.subset_ground).mp hI, λ hI, (h I hI.2).mpr hI⟩, 
--     λ h I hIE, h I⟩,
-- end 

-- -- theorem set.unif_on_r_eq_of_infinite (E : Set α) (k : ℕ) (hXinf : X.infinite) (hXE : X ⊆ E):
-- --   (E.unif_on k).r X = k :=
-- -- begin
-- --   rw [set.unif_on, truncate_r_eq_of_not_r_fin], 
-- --   simp_rw [r_fin, not_exists, not_and, free_on_basis_iff hXE], 
-- --   simpa, 
-- -- end 

-- /-- A uniform matroid of a given rank whose ground Set is the universe of a type -/
-- def unif_on (α : Type*) (k : ℕ) := (univ : Set α).unif_on k 

-- @[simp] theorem unif_on_ground_eq : (unif_on α k).E = (univ : Set α) := rfl 

-- @[simp] theorem unif_on_indep_iff [_root_.finite α] : (unif_on α k).indep I ↔ I.ncard ≤ k := 
-- by simp only [unif_on, set.unif_on_indep_iff, subset_univ, and_true, and_iff_right_iff_imp, 
--     iff_true_intro (to_finite I), imp_true_iff]
  
-- /-- A canonical uniform matroid, with rank `a` and ground type `fin b`. -/
-- def unif (a b : ℕ) := unif_on (fin b) a 

-- @[simp] theorem unif_ground_eq (a b : ℕ) : (unif a b).E = univ := rfl 

-- @[simp] theorem unif_indep_iff (I : Set (fin b)) : (unif a b).indep I ↔ I.ncard ≤ a :=
-- by rw [unif, unif_on_indep_iff]

-- @[simp] theorem unif_indep_iff' (I : Set (fin b)) : (unif a b).indep I ↔ I.encard ≤ a :=
-- by rw [unif_indep_iff, encard_le_coe_iff, and_iff_right (to_finite I)]

-- @[simp] theorem unif_r_eq (X : Set (fin b)) : (unif a b).r X = min X.ncard a := 
-- by { rw [unif, unif_on, set.unif_on_r_eq_of_finite _ _ (subset_univ _)], exact to_finite X } 

-- @[simp] theorem unif_base_iff (hab : a ≤ b) {B : Set (fin b)} : 
--   (unif a b).base B ↔ B.ncard = a := 
-- begin
--   simp only [unif, unif_on, set.unif_on], 
--   rw [truncate_base_iff, free_on_indep_iff, and_iff_right (subset_univ _)], 
--   rwa [free_on_rk_eq, ncard_eq_to_finset_card, finite.to_finset_univ, finset.card_fin], 
-- end 

-- theorem unif_dual' (h : a + b = c) : (unif a c)﹡ = unif b c := 
-- begin
--   subst h, 
--   refine eq_of_base_iff_base_forall rfl (λ B hB, _), 
--   rw [unif_base_iff le_add_self, dual_base_iff, unif_base_iff le_self_add, unif_ground_eq, 
--     ←compl_eq_univ_diff], 
--   have hc := ncard_add_ncard_compl B, 
--   rw [nat.card_eq_fintype_card, fintype.card_fin] at hc,
--   exact ⟨λ h, by rwa [h, add_comm, add_right_inj] at hc, 
--     λ h, by rwa [h, add_comm, add_left_inj] at hc⟩ 
-- end 

-- theorem unif_dual (hab : a ≤ b) : (unif a b)﹡ = unif (b - a) b := 
-- unif_dual' (nat.add_sub_of_le hab)

-- theorem unif_self_dual (a : ℕ) : (unif a (2*a))﹡ = unif a (2*a) := 
-- unif_dual' (two_mul a).symm 

-- theorem iso_unif_iff {a b : ℕ} {M : Matroid α} : 
--   nonempty (M ≃i (unif a b)) ↔ (M = M.E.unif_on a ∧ M.E.encard = (b : ℕ∞)) := 
-- begin
--   refine ⟨λ h, _, λ h, _⟩,
--   { obtain ⟨i⟩ := h,
--     Set e := i.to_equiv, 
--     rw [encard, part_enat.card_congr e, unif_ground_eq, part_enat.card_eq_coe_fintype_card, 
--       part_enat.with_top_equiv_coe, nat.cast_inj, ←set.to_finset_card, to_finset_univ, 
--       finset.card_fin, eq_self_iff_true, and_true, eq_iff_indep_iff_indep_forall, 
--       set.unif_on_ground_eq, and_iff_right rfl], 
--     intros I hI, 
--     rw [set.unif_on_indep_iff, and_iff_left hI, ←encard_le_coe_iff, i.on_indep hI, unif_indep_iff', 
--       iso.image, encard_image_of_injective _ (subtype.coe_injective), 
--       encard_image_of_injective _ (equiv_like.injective i), 
--       encard_preimage_of_injective_subset_range subtype.coe_injective], 
--     rwa subtype.range_coe },
--   rw [encard_eq_coe_iff, ncard] at h, 
--   obtain ⟨h1, hfin, h'⟩ := h, 
--   haveI := finite_coe_iff.mpr hfin, 
--   Set e := (finite.equiv_fin_of_card_eq h').trans (equiv.set.univ (fin b)).symm, 
--   refine ⟨@iso_of_indep _ _ M (unif a b) e (λ I, _)⟩,  
--   apply_fun indep at h1, 
--   rw [h1, set.unif_on_indep_iff'],  
--   simp only [image_subset_iff, subtype.coe_preimage_self, subset_univ, and_true, equiv.coe_trans, 
--     function.comp_app, equiv.set.univ_symm_apply, unif_indep_iff', 
--     encard_image_of_injective _ subtype.coe_injective],
--   rw [encard_image_of_injective], 
--   intros x y, 
--   simp,  
-- end 

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

end Matroid 