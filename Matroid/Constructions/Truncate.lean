import Matroid.Rank

variable {α : Type*} {M : Matroid α} {E : Set α}

namespace Matroid

open Set

section Truncate

/-- The `IndepMatroid` whose independent sets are the `M`-independent sets of size at most `k`. -/
def truncate_indepMatroid (M : Matroid α) (k : ℕ) : IndepMatroid α := IndepMatroid.ofBddAugment
  (E := M.E)
  (Indep := fun I ↦ M.Indep I ∧ I.encard ≤ k)
  (indep_empty := by simp)
  (indep_subset := fun I J hI hIJ ↦ ⟨hI.1.subset hIJ, (encard_mono hIJ).trans hI.2⟩)
  (indep_aug := by
    rintro I J ⟨hI, _⟩ ⟨hJ, hJc⟩ hIJ
    obtain ⟨e, he, hi⟩ := hI.augment hJ hIJ
    exact ⟨e, he.1, he.2, hi,
      (encard_insert_of_not_mem he.2).trans_le ((ENat.add_one_le_of_lt hIJ).trans hJc)⟩)
  (indep_bdd := ⟨k, fun _ ↦ And.right⟩)
  (subset_ground := fun _ h ↦ h.1.subset_ground)

/-- The truncation of a matroid to rank `k`. The independent sets of the truncation
  are the independent sets of the matroid of size at most `k`.  -/
def truncate (M : Matroid α) (k : ℕ∞) : Matroid α :=
  Option.casesOn k M <| fun k ↦ (M.truncate_indepMatroid k).matroid

@[simp] theorem truncate_top (M : Matroid α) : M.truncate ⊤ = M := rfl

@[simp] theorem truncate_indep_iff : (M.truncate k).Indep I ↔ (M.Indep I ∧ I.encard ≤ k) := by
  cases k <;> simp [truncate, truncate_indepMatroid, WithTop.none_eq_top,
    WithTop.some_eq_coe, le_top]

@[simp] theorem truncate_ground_eq : (M.truncate k).E = M.E := by
  cases k <;> rfl

@[simp] theorem truncate_zero (M : Matroid α) : M.truncate 0 = loopyOn M.E := by
  refine' eq_of_indep_iff_indep_forall rfl _
  simp only [truncate_ground_eq, truncate_indep_iff, nonpos_iff_eq_zero, encard_eq_zero,
    loopyOn_indep_iff, and_iff_right_iff_imp]
  rintro I - rfl; apply empty_indep

@[simp] theorem truncate_emptyOn (α : Type*) (k : ℕ∞) : (emptyOn α).truncate k = emptyOn α := by
  rw [← ground_eq_empty_iff, truncate_ground_eq, emptyOn_ground]

@[simp] theorem truncate_loopyOn (E : Set α) (k : ℕ∞) : (loopyOn E).truncate k = loopyOn E := by
  apply eq_of_indep_iff_indep_forall (by simp)
  simp only [truncate_ground_eq, loopyOn_ground, truncate_indep_iff, loopyOn_indep_iff,
    and_iff_left_iff_imp]
  rintro _ _ rfl
  simp

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
  · obtain ⟨B', hB', hJB'⟩ := hB.exists_base_superset
    obtain ⟨J, hBJ, hJB', h'⟩ :=
      exists_superset_subset_encard_eq hJB' hBk (h_rk.trans_eq hB'.encard.symm)
    rw [h _ (hB'.indep.subset hJB') h'.le hBJ] at hlt
    exact hlt.ne h'
  exact (finite_of_encard_eq_coe hBk).eq_of_subset_of_encard_le' hBI (hIk.trans_eq hBk.symm)

theorem truncate_base_iff_of_finiteRk [FiniteRk M] (h_rk : k ≤ M.erk) :
    (M.truncate k).Base B ↔ M.Indep B ∧ B.encard = k := by
  lift k to ℕ using (h_rk.trans_lt M.erk_lt_top).ne; rwa [truncate_base_iff]

instance truncate.finite [Matroid.Finite M] : Matroid.Finite (M.truncate k) :=
⟨ by simp [ground_finite M] ⟩

instance truncate.finiteRk {k : ℕ} : FiniteRk (M.truncate k) := by
  obtain ⟨B, hB⟩ := (M.truncate k).exists_base
  refine ⟨B, hB, (le_or_lt M.erk k).elim (fun h ↦ ?_) (fun h ↦ ?_)⟩
  · rw [truncate_eq_self_of_rk_le h] at hB
    rw [← encard_lt_top_iff, hB.encard]
    exact h.trans_lt (WithTop.coe_lt_top _)
  rw [truncate_base_iff h.le] at hB
  rw [← encard_lt_top_iff, hB.2]
  apply WithTop.coe_lt_top

theorem Indep.of_truncate (h : (M.truncate k).Indep I) : M.Indep I := by
  rw [truncate_indep_iff] at h; exact h.1

theorem Indep.encard_le_of_truncate (h : (M.truncate k).Indep I) : I.encard ≤ k :=
  (truncate_indep_iff.mp h).2

theorem truncate_er_eq (M : Matroid α) (k : ℕ∞) (X : Set α) :
    (M.truncate k).er X = min (M.er X) k := by
  simp_rw [le_antisymm_iff, le_er_iff, er_le_iff, truncate_indep_iff]
  obtain ⟨I, hI⟩ := M.exists_basis' X
  refine ⟨?_, ?_⟩
  · intro J hJX hJi
    exact le_min (hJi.1.encard_le_er_of_subset hJX) hJi.2
  obtain ⟨I₀, hI₀, hI₀ss⟩ := exists_subset_encard_eq (min_le_of_left_le (b := k) hI.encard.symm.le)
  exact ⟨_, hI₀.trans hI.subset, ⟨hI.indep.subset hI₀, hI₀ss.trans_le (min_le_right _ _)⟩, hI₀ss⟩

end Truncate
