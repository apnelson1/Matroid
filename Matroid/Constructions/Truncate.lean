import Matroid.Extension

variable {α : Type*} {M : Matroid α} {E I B : Set α} {k : ℕ∞}

namespace Matroid

open Set

section truncateTo

/-- The `IndepMatroid` whose independent sets are the `M`-independent sets of size at most `k`. -/
def truncateToNat (M : Matroid α) (k : ℕ) : Matroid α :=
  IndepMatroid.matroid <| IndepMatroid.ofBddAugment
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
@[simps!] def truncateTo (M : Matroid α) (k : ℕ∞) : Matroid α :=
  Matroid.ofExistsMatroid
    (E := M.E)
    (Indep := fun I ↦ M.Indep I ∧ I.encard ≤ k)
    (hM :=  k.recTopCoe ⟨M, rfl, by simp⟩
      (fun k ↦ ⟨M.truncateToNat k, rfl, fun _ ↦ by simp [truncateToNat]⟩))

@[simp] theorem truncateTo_top (M : Matroid α) : M.truncateTo ⊤ = M :=
  eq_of_indep_iff_indep_forall rfl (by simp [truncateTo])

@[simp] theorem truncateTo_indep_iff : (M.truncateTo k).Indep I ↔ (M.Indep I ∧ I.encard ≤ k) :=
    Iff.rfl

@[simp] theorem truncateTo_ground_eq : (M.truncateTo k).E = M.E := rfl

@[simp] theorem truncateTo_zero (M : Matroid α) : M.truncateTo 0 = loopyOn M.E := by
  refine eq_of_indep_iff_indep_forall rfl ?_
  suffices ∀ I ⊆ M.E, I = ∅ → M.Indep I by simpa
  rintro I - rfl; exact M.empty_indep

@[simp] theorem truncateTo_emptyOn (α : Type*) (k : ℕ∞) : (emptyOn α).truncateTo k = emptyOn α := by
  rw [← ground_eq_empty_iff, truncateTo_ground_eq, emptyOn_ground]

@[simp] theorem truncate_loopyOn (E : Set α) (k : ℕ∞) : (loopyOn E).truncateTo k = loopyOn E := by
  apply eq_of_indep_iff_indep_forall (by simp)
  suffices ∀ I ⊆ E, I = ∅ → encard I ≤ k by simpa
  rintro _ - rfl; simp

theorem truncate_eq_self_of_rk_le (h_rk : M.erk ≤ k) : M.truncateTo k = M := by
  refine eq_of_indep_iff_indep_forall truncateTo_ground_eq (fun I _ ↦ ?_)
  rw [truncateTo_indep_iff, and_iff_left_iff_imp]
  exact fun hi ↦ hi.encard_le_erk.trans h_rk

theorem truncateTo_base_iff {k : ℕ} (h_rk : k ≤ M.erk) :
    (M.truncateTo k).Base B ↔ M.Indep B ∧ B.encard = k := by
  simp_rw [base_iff_maximal_indep, truncateTo_indep_iff, and_imp]
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
    (M.truncateTo k).Base B ↔ M.Indep B ∧ B.encard = k := by
  lift k to ℕ using (h_rk.trans_lt M.erk_lt_top).ne; rwa [truncateTo_base_iff]

instance truncateTo.finite [Matroid.Finite M] : Matroid.Finite (M.truncateTo k) :=
⟨ by simp [ground_finite M] ⟩

instance truncateTo.finiteRk {k : ℕ} : FiniteRk (M.truncateTo k) := by
  obtain ⟨B, hB⟩ := (M.truncateTo k).exists_base
  refine ⟨B, hB, (le_or_lt M.erk k).elim (fun h ↦ ?_) (fun h ↦ ?_)⟩
  · rw [truncate_eq_self_of_rk_le h] at hB
    rw [← encard_lt_top_iff, hB.encard]
    exact h.trans_lt (WithTop.coe_lt_top _)
  rw [truncateTo_base_iff h.le] at hB
  rw [← encard_lt_top_iff, hB.2]
  apply WithTop.coe_lt_top

theorem Indep.of_truncateTo (h : (M.truncateTo k).Indep I) : M.Indep I := by
  rw [truncateTo_indep_iff] at h; exact h.1

theorem Indep.encard_le_of_truncateTo (h : (M.truncateTo k).Indep I) : I.encard ≤ k :=
  (truncateTo_indep_iff.mp h).2

theorem truncateTo_er_eq (M : Matroid α) (k : ℕ∞) (X : Set α) :
    (M.truncateTo k).er X = min (M.er X) k := by
  simp_rw [le_antisymm_iff, le_er_iff, er_le_iff, truncateTo_indep_iff]
  obtain ⟨I, hI⟩ := M.exists_basis' X
  refine ⟨?_, ?_⟩
  · intro J hJX hJi
    exact le_min (hJi.1.encard_le_er_of_subset hJX) hJi.2
  obtain ⟨I₀, hI₀, hI₀ss⟩ := exists_subset_encard_eq (min_le_of_left_le (b := k) hI.encard.symm.le)
  exact ⟨_, hI₀.trans hI.subset, ⟨hI.indep.subset hI₀, hI₀ss.trans_le (min_le_right _ _)⟩, hI₀ss⟩

end truncateTo

section truncate

/-- The matroid on `M.E` whose independent sets are the independent nonbases of `M`. -/
def truncate (M : Matroid α) := Matroid.ofExistsMatroid
  (E := M.E)
  (Indep := fun I ↦ M.Indep I ∧ (M.Base I → I = ∅))
  (hM := by
    refine ⟨M.projectBy (ModularCut.principal M M.E), rfl, fun I ↦ ?_⟩
    obtain (hM | hM) := M.eq_loopyOn_or_rkPos
    · rw [hM]; simp [ModularCut.eq_top_iff, Subset.rfl]
    suffices M.Indep I → (¬M.E ⊆ M.cl I ↔ M.Base I → I = ∅) by simpa [M.principal_ground_ne_top]
    refine fun hI ↦ ⟨fun h hIb ↦ by simp [hIb.cl_eq, Subset.rfl] at h, fun h hss ↦ ?_⟩
    have hIb := hI.base_of_ground_subset_cl hss
    exact hIb.nonempty.ne_empty (h hIb))

@[simp] lemma truncate_ground_eq : M.truncate.E = M.E := rfl

lemma truncate_indep_iff' : M.truncate.Indep I ↔ M.Indep I ∧ (M.Base I → I = ∅) := Iff.rfl

@[simp] lemma truncate_indep_iff [M.RkPos] : M.truncate.Indep I ↔ M.Indep I ∧ ¬ M.Base I := by
  simp only [truncate_indep_iff', and_congr_right_iff]
  exact fun _ ↦ ⟨fun h hB ↦ hB.nonempty.ne_empty (h hB), fun h hB ↦ by contradiction⟩

@[simp] lemma truncate_loopyOn_eq {E : Set α} : (loopyOn E).truncate = loopyOn E := by
  simp (config := {contextual := true}) [truncate, ModularCut.principal, eq_loopyOn_iff]

lemma truncate_base_iff [M.RkPos] : M.truncate.Base B ↔ ∃ e ∉ B, M.Base (insert e B) := by
  refine ⟨fun h ↦ ?_, fun ⟨e, he, hBe⟩ ↦ ?_⟩
  · obtain ⟨hB, hBb⟩ := truncate_indep_iff.1 h.indep
    obtain ⟨B', hB', hBB'⟩ := hB.exists_base_superset
    obtain ⟨e, heB', heB⟩ := exists_of_ssubset (hBB'.ssubset_of_ne (by rintro rfl; contradiction))
    refine ⟨e, heB, ?_⟩
    rwa [h.eq_of_subset_indep ?_ (subset_diff_singleton hBB' heB), insert_diff_singleton,
      insert_eq_of_mem heB']
    rw [truncate_indep_iff]
    exact ⟨hB'.indep.subset diff_subset, hB'.not_base_of_ssubset <| diff_singleton_sSubset.mpr heB'⟩
  refine Indep.base_of_forall_insert ?_ ?_
  · rw [truncate_indep_iff]
    exact ⟨hBe.indep.subset (subset_insert _ _), hBe.not_base_of_ssubset (ssubset_insert he)⟩
  simp only [truncate_ground_eq, mem_diff, truncate_indep_iff, not_and, not_not, and_imp]
  exact fun f _ hfB hfBi ↦ insert_base_of_insert_indep he hfB hBe hfBi

end truncate

section circuitOn

variable {C : Set α}

/-- The matroid on `E` whose ground set is a circuit. Empty if `E = ∅`. -/
def circuitOn (C : Set α) := (freeOn C).truncate

@[simp] lemma circuitOn_ground : (circuitOn C).E = C := rfl

lemma circuitOn_indep_iff (hC : C.Nonempty) : (circuitOn C).Indep I ↔ I ⊂ C := by
  have := freeOn_rkPos hC
  simp [circuitOn, truncate_indep_iff, ssubset_iff_subset_ne]

lemma circuitOn_dep_iff (hC : C.Nonempty) {D : Set α} : (circuitOn C).Dep D ↔ D = C := by
  simp only [Dep, circuitOn_indep_iff hC, ssubset_iff_subset_ne, ne_eq, not_and, not_not,
    circuitOn_ground]
  exact ⟨fun h ↦ h.1 h.2, by rintro rfl; simp [Subset.rfl]⟩

lemma circuitOn_base_iff (hC : C.Nonempty) : (circuitOn C).Base B ↔ ∃ e ∉ B, insert e B = C := by
  have _ := freeOn_rkPos hC; simp [circuitOn, truncate_base_iff]

lemma circuitOn_ground_circuit (hC : C.Nonempty) : (circuitOn C).Circuit C := by
  simp [circuit_iff_forall_ssubset, circuitOn_dep_iff hC, circuitOn_indep_iff hC]

lemma circuitOn_circuit_iff (hC : C.Nonempty) {C' : Set α} : (circuitOn C).Circuit C' ↔ C' = C := by
  refine ⟨fun h ↦ h.eq_of_subset_circuit (circuitOn_ground_circuit hC) h.subset_ground, ?_⟩
  rintro rfl
  exact circuitOn_ground_circuit hC

lemma ground_circuit_iff [M.Nonempty] : M.Circuit M.E ↔ M = circuitOn M.E := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine eq_of_circuit_iff_circuit_forall rfl <| fun C hC ↦ ?_
    rw [circuitOn_circuit_iff h.nonempty]
    exact ⟨fun h' ↦ h'.eq_of_subset_circuit h hC, by rintro rfl; assumption⟩
  rw [h]
  exact circuitOn_ground_circuit M.ground_nonempty

lemma circuit_iff_restr_eq_circuitOn (hCne : C.Nonempty) (hC : C ⊆ M.E := by aesop_mat) :
    M.Circuit C ↔ M ↾ C = circuitOn C := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine eq_of_circuit_iff_circuit_forall rfl fun C' hC' ↦ ?_
    rw [restrict_circuit_iff h.subset_ground, circuitOn_circuit_iff h.nonempty,
      and_iff_left (show C' ⊆ C from hC')]
    exact ⟨fun h' ↦ h'.eq_of_subset_circuit h hC', fun h' ↦ by rwa [h']⟩
  have h' := restrict_circuit_iff hC (C := C)
  rwa [and_iff_left Subset.rfl, h, iff_true_intro (circuitOn_ground_circuit hCne), true_iff] at h'

end circuitOn
--


-- def tr (M : Matroid α) : Matroid α where
--   E := M.E
--   Base B := ∃ e ∉ B, M.Base (insert e B)
--   Indep I := M.Indep I ∧ ¬ M.Base I
--   indep_iff' I := by
--     refine ⟨fun ⟨hI, hIb⟩ ↦ ?_, fun ⟨B, ⟨e, heB, heB'⟩, hIB⟩ ↦ ?_⟩
--     · obtain ⟨B, hB, hIB⟩ := hI.exists_base_superset
--       obtain ⟨e, heB, heI⟩ := exists_of_ssubset (hIB.ssubset_of_ne (by rintro rfl; contradiction))
--       exact ⟨B \ {e}, ⟨e, by simp, by simpa [heB]⟩, subset_diff_singleton hIB heI⟩
--     have hIBe : I ⊆ insert e B := hIB.trans (subset_insert _ _)
--     refine ⟨heB'.indep.subset hIBe, fun hI ↦ heB (hIB ?_)⟩
--     simp [hI.eq_of_subset_base heB' hIBe]
--   exists_base := _
--   base_exchange := _
--   maximality := _
--   subset_ground := _
