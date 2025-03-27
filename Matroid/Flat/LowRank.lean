import Matroid.Flat.Lattice

variable {α : Type*} {M : Matroid α} {I F X Y F' F₀ F₁ F₂ P L H H₁ H₂ H' B C K : Set α} {e f : α}

open Set
namespace Matroid

@[reducible] def IsPoint (M : Matroid α) (P : Set α) := M.IsFlat P ∧ M.eRk P = 1

lemma IsPoint.isFlat (hP : M.IsPoint P) : M.IsFlat P :=
  hP.1

lemma IsPoint.eRk (hP : M.IsPoint P) : M.eRk P = 1 :=
  hP.2

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma IsPoint.subset_ground (hP : M.IsPoint P) : P ⊆ M.E :=
  hP.1.subset_ground

lemma IsPoint.isRkFinite (hP : M.IsPoint P) : M.IsRkFinite P := by
  simp [← eRk_ne_top_iff, hP.eRk]

lemma IsNonloop.closure_isPoint (he : M.IsNonloop e) : M.IsPoint (M.closure {e}) :=
  ⟨M.closure_isFlat {e}, by rw [eRk_closure_eq, he.indep.eRk_eq_encard, encard_singleton]⟩

lemma loops_covBy_iff : M.loops ⋖[M] P ↔ M.IsPoint P := by
  simp only [covBy_iff_eRelRk_eq_one, closure_isFlat, eRelRk_closure_left, eRelRk_empty_left,
    true_and, and_congr_right_iff, and_iff_right_iff_imp, loops]
  exact fun h _ ↦ h.closure_subset_of_subset (empty_subset _)

lemma IsPoint.covBy (hP : M.IsPoint P) : M.loops ⋖[M] P := loops_covBy_iff.2 hP

lemma IsPoint.exists_eq_closure_isNonloop (hP : M.IsPoint P) :
    ∃ e, M.IsNonloop e ∧ P = M.closure {e} := by
  obtain ⟨I, hI⟩ := M.exists_isBasis P
  obtain ⟨e, rfl⟩ := encard_eq_one.1 <| hI.encard_eq_eRk.trans hP.eRk
  obtain rfl := hP.isFlat.eq_closure_of_isBasis hI
  exact ⟨e, indep_singleton.1 hI.indep, rfl⟩

lemma IsPoint.eq_closure_of_mem (hP : M.IsPoint P) (he : M.IsNonloop e) (heP : e ∈ P) :
    P = M.closure {e} := by
  rw [← indep_singleton] at he
  exact hP.isFlat.eq_closure_of_isBasis <| he.isBasis_of_subset_of_eRk_le_of_finite
    (singleton_subset_iff.2 heP) (by rw [hP.eRk, he.eRk_eq_encard, encard_singleton])
    (finite_singleton e)

lemma isPoint_iff_exists_eq_closure_isNonloop :
    M.IsPoint P ↔ ∃ e, M.IsNonloop e ∧ P = M.closure {e} :=
  ⟨IsPoint.exists_eq_closure_isNonloop, by rintro ⟨e, he, rfl⟩; exact he.closure_isPoint⟩

lemma IsPoint.isNonloop (hP : M.IsPoint {e}) : M.IsNonloop e := by
  simpa using hP.eRk

lemma IsPoint.insert_indep (h : M.IsPoint {e}) (f : α) (hf : f ∈ M.E := by aesop_mat) :
    M.Indep {e, f} := by
  obtain rfl | hne := eq_or_ne e f
  · simp [h.isNonloop]
  simpa [pair_comm] using h.isFlat.insert_indep_of_isBasis (h.isNonloop.indep.isBasis_self)
    ⟨hf, hne.symm⟩

lemma isPoint_singleton_iff [M.Nonempty] : M.IsPoint {e} ↔ ∀ f ∈ M.E, M.Indep {e,f} := by
  refine ⟨fun h f hf ↦ h.insert_indep f hf, fun h ↦ ?_⟩
  obtain ⟨x, hx⟩ := M.ground_nonempty
  have he : M.IsNonloop e := (h x hx).isNonloop_of_mem (mem_insert _ _)
  have hF : M.IsFlat {e}
  · simp only [isFlat_iff, he.indep.isBasis_iff_eq, singleton_subset_iff, he.mem_ground, and_true]
    rintro _ X rfl he f hXf
    rw [he.eq_of_subset_indep (h f (he.subset_ground hXf)) (by simp)
      (by simpa [pair_subset_iff, hXf] using he.subset)]
    simp
  rw [← hF.closure]
  exact he.closure_isPoint

lemma IsPoint.loopless_of_singleton (h : M.IsPoint {e}) : M.Loopless := by
  rw [loopless_iff_loops, ← subset_empty_iff, loops]
  nth_rw 2 [← diff_eq_empty.2 h.isFlat.closure.subset]
  rw [subset_diff_singleton_iff]
  exact ⟨M.closure_subset_closure (empty_subset _), h.isNonloop.not_isLoop⟩

lemma isPoint_contract_iff (hC : C ⊆ M.E := by aesop_mat) :
    (M ／ C).IsPoint P ↔ (M.closure C ⋖[M] (C ∪ P)) ∧ Disjoint P C := by
  rw [IsPoint, isFlat_contract_iff, covBy_iff_eRelRk_eq_one, eRelRk_closure_left,
    union_comm C, ← eRelRk_eq_eRelRk_union, and_iff_right (closure_isFlat _ _),
    ← eRelRk_eq_eRk_contract, and_assoc, and_assoc, and_congr_right_iff, and_comm,
    and_congr_left_iff, iff_and_self]
  rintro h - -
  rw [← h.closure]
  exact M.closure_subset_closure subset_union_right

/-- IsPoints of `M ／ C` are equivalent to flats covering `M.closure C`. -/
@[simps] def isPointContractCovByEquiv (M : Matroid α) (C : Set α) :
    {P // (M ／ C).IsPoint P} ≃ {F // M.closure C ⋖[M] F} where
  toFun P := ⟨P ∪ M.closure C, by
    obtain ⟨P, hP⟩ := P
    rw [← contract_inter_ground_eq, isPoint_contract_iff, closure_inter_ground] at hP
    convert hP.1 using 1
    rw [subset_antisymm_iff, union_subset_iff, and_iff_right subset_union_right,
      union_subset_iff, and_iff_left subset_union_left, ← hP.1.isFlat_right.closure,
      ← closure_inter_ground]
    exact ⟨M.closure_subset_closure subset_union_left,
      (M.subset_closure _).trans subset_union_right⟩⟩
  invFun P := ⟨P \ C, by
    obtain ⟨P, hP⟩ := P
    rw [← closure_inter_ground] at hP
    rwa [diff_eq_diff_inter_of_subset hP.subset_ground_right, ← contract_inter_ground_eq,
      isPoint_contract_iff, and_iff_left disjoint_sdiff_left, union_diff_self,
      union_eq_self_of_subset_left, closure_inter_ground]
    exact (M.subset_closure _).trans hP.subset ⟩
  left_inv := by
    rintro ⟨P,hP⟩
    simp only [Subtype.mk.injEq]
    rw [← contract_inter_ground_eq, isPoint_contract_iff] at hP
    rw [← closure_inter_ground, diff_eq_diff_inter_of_subset
      (union_subset _ (M.closure_subset_ground _)),
      subset_antisymm_iff, diff_subset_iff, union_subset_iff, subset_diff,
      and_iff_right subset_union_right, and_iff_right hP.1.subset, and_iff_left hP.2]
    · exact subset_union_left
    exact subset_union_right.trans hP.1.subset_ground_right
  right_inv := by
    rintro ⟨P, hP⟩
    simp only [Subtype.mk.injEq]
    rw [diff_eq_diff_inter_of_subset hP.subset_ground_right, ← closure_inter_ground,
      diff_union_eq_union_of_subset P (M.subset_closure (C ∩ M.E)),
      union_eq_left, closure_inter_ground]
    exact hP.subset

lemma IsPoint.eq_or_eq_of_isFlat_of_subset (hP : M.IsPoint P) (hF : M.IsFlat F) (h : F ⊆ P) :
    F = M.loops ∨ F = P :=
  hP.covBy.eq_or_eq hF hF.loops_subset h

lemma IsPoint.subset_or_inter_eq_loops_of_isFlat (hP : M.IsPoint P) (hF : M.IsFlat F) :
    P ⊆ F ∨ P ∩ F = M.loops := by
  obtain (h | h) := hP.eq_or_eq_of_isFlat_of_subset (hP.isFlat.inter hF) inter_subset_left
  · exact Or.inr h
  exact Or.inl (inter_eq_left.1 h)

-- /-- Each flat `F` induces a partition of the set of points not contained in `F`. -/
-- def IsFlat.covByIsPointPartition {F : Set α} (hF : M.IsFlat F) :
--     Partition {P | M.IsPoint P ∧ ¬ (P ⊆ F)} := Partition.ofPairwiseDisjoint'
--   (parts := (fun F' ↦ {P | P ⊆ F' ∧ ¬ (P ⊆ F)}) '' hF.covByPartition)
--   (pairwiseDisjoint := by
--     rintro Ps ⟨_, h, rfl⟩
--     simp

--     )
--   (forall_nonempty := sorry)
--   (eq_sUnion := sorry)





abbrev IsLine (M : Matroid α) (L : Set α) := M.IsFlat L ∧ M.eRk L = 2

lemma IsLine.isFlat (hL : M.IsLine L) : M.IsFlat L :=
  hL.1

lemma IsLine.eRk (hL : M.IsLine L) : M.eRk L = 2 :=
  hL.2

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma IsLine.subset_ground (hL : M.IsLine L) : L ⊆ M.E :=
  hL.1.subset_ground

lemma IsLine.isRkFinite (hL : M.IsLine L) : M.IsRkFinite L := by
  simp [← eRk_ne_top_iff, hL.eRk]

lemma IsLine.mem_iff_covBy (hL : M.IsLine L) (he : M.IsNonloop e) :
    e ∈ L ↔ M.closure {e} ⋖[M] L := by
  rw [(M.closure_isFlat {e}).covBy_iff_eRelRk_eq_one hL.isFlat, hL.isFlat.closure_subset_iff_subset,
    singleton_subset_iff, iff_self_and, eRelRk_closure_left]
  intro heL
  rw [isRkFinite_singleton.eRelRk_eq_sub (by simpa), he.eRk_eq, hL.eRk]
  rfl

lemma IsNonloop.closure_covBy_iff (he : M.IsNonloop e) :
    M.closure {e} ⋖[M] L ↔ M.IsLine L ∧ e ∈ L := by
  refine ⟨fun h ↦ ⟨⟨h.isFlat_right, ?_⟩,h.subset <| M.mem_closure_self e⟩,
    fun ⟨hL, heL⟩ ↦ by rwa [← hL.mem_iff_covBy he]⟩
  rw [h.eRk_eq, eRk_closure_eq, he.eRk_eq]
  rfl

def IsNonloop.LineContractElemPointEquiv (he : M.IsNonloop e) :
    {P // (M ／ {e}).IsPoint P} ≃ {L // M.IsLine L ∧ e ∈ L} :=
  (M.isPointContractCovByEquiv {e}).trans (Equiv.subtypeEquivRight (fun _ ↦ he.closure_covBy_iff))

abbrev IsPlane (M : Matroid α) (P : Set α) := M.IsFlat P ∧ M.eRk P = 3

lemma IsPlane.isFlat (hP : M.IsPlane P) : M.IsFlat P :=
  hP.1

lemma IsPlane.eRk (hP : M.IsPlane P) : M.eRk P = 3 :=
  hP.2
