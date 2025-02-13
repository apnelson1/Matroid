import Matroid.Flat.Lattice

variable {α : Type*} {M : Matroid α} {I F X Y F' F₀ F₁ F₂ P L H H₁ H₂ H' B C K : Set α} {e f : α}

open Set
namespace Matroid

@[reducible] def Point (M : Matroid α) (P : Set α) := M.Flat P ∧ M.eRk P = 1

lemma Point.flat (hP : M.Point P) : M.Flat P :=
  hP.1

lemma Point.eRk (hP : M.Point P) : M.eRk P = 1 :=
  hP.2

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma Point.subset_ground (hP : M.Point P) : P ⊆ M.E :=
  hP.1.subset_ground

lemma Point.isRkFinite (hP : M.Point P) : M.IsRkFinite P := by
  simp [← eRk_ne_top_iff, hP.eRk]

lemma Nonloop.closure_point (he : M.Nonloop e) : M.Point (M.closure {e}) :=
  ⟨M.closure_flat {e}, by rw [eRk_closure_eq, he.indep.eRk_eq_encard, encard_singleton]⟩

lemma loops_covBy_iff : M.closure ∅ ⋖[M] P ↔ M.Point P := by
  simp only [covBy_iff_eRelRk_eq_one, closure_flat, eRelRk_closure_left, eRelRk_empty_left,
    true_and, and_congr_right_iff, and_iff_right_iff_imp]
  exact fun h _ ↦ h.closure_subset_of_subset (empty_subset _)

lemma Point.covBy (hP : M.Point P) : M.closure ∅ ⋖[M] P := loops_covBy_iff.2 hP

lemma Point.exists_eq_closure_nonloop (hP : M.Point P) : ∃ e, M.Nonloop e ∧ P = M.closure {e} := by
  obtain ⟨I, hI⟩ := M.exists_basis P
  obtain ⟨e, rfl⟩ := encard_eq_one.1 <| hI.encard_eq_eRk.trans hP.eRk
  obtain rfl := hP.flat.eq_closure_of_basis hI
  exact ⟨e, indep_singleton.1 hI.indep, rfl⟩

lemma Point.eq_closure_of_mem (hP : M.Point P) (he : M.Nonloop e) (heP : e ∈ P) :
    P = M.closure {e} := by
  rw [← indep_singleton] at he
  exact hP.flat.eq_closure_of_basis <| he.basis_of_subset_of_eRk_le_of_finite
    (singleton_subset_iff.2 heP) (by rw [hP.eRk, he.eRk_eq_encard, encard_singleton])
    (finite_singleton e)

lemma point_iff_exists_eq_closure_nonloop : M.Point P ↔ ∃ e, M.Nonloop e ∧ P = M.closure {e} :=
  ⟨Point.exists_eq_closure_nonloop, by rintro ⟨e, he, rfl⟩; exact he.closure_point⟩

lemma Point.nonloop (hP : M.Point {e}) : M.Nonloop e := by
  simpa using hP.eRk

lemma Point.insert_indep (h : M.Point {e}) (f : α) (hf : f ∈ M.E := by aesop_mat) :
    M.Indep {e, f} := by
  obtain rfl | hne := eq_or_ne e f
  · simp [h.nonloop]
  simpa [pair_comm] using h.flat.insert_indep_of_basis (h.nonloop.indep.basis_self) ⟨hf, hne.symm⟩

lemma point_singleton_iff [M.Nonempty] : M.Point {e} ↔ ∀ f ∈ M.E, M.Indep {e,f} := by
  refine ⟨fun h f hf ↦ h.insert_indep f hf, fun h ↦ ?_⟩
  obtain ⟨x, hx⟩ := M.ground_nonempty
  have he : M.Nonloop e := (h x hx).nonloop_of_mem (mem_insert _ _)
  have hF : M.Flat {e}
  · simp only [flat_iff, he.indep.basis_iff_eq, singleton_subset_iff, he.mem_ground, and_true]
    rintro _ X rfl he f hXf
    rw [he.eq_of_subset_indep (h f (he.subset_ground hXf)) (by simp)
      (by simpa [pair_subset_iff, hXf] using he.subset)]
    simp
  rw [← hF.closure]
  exact he.closure_point

lemma Point.loopless_of_singleton (h : M.Point {e}) : M.Loopless := by
  rw [loopless_iff_closure_empty, ← subset_empty_iff]
  nth_rw 2 [← diff_eq_empty.2 h.flat.closure.subset]
  rw [subset_diff_singleton_iff]
  exact ⟨M.closure_subset_closure (empty_subset _), h.nonloop.not_loop⟩

lemma point_contract_iff (hC : C ⊆ M.E := by aesop_mat) :
    (M ／ C).Point P ↔ (M.closure C ⋖[M] (C ∪ P)) ∧ Disjoint P C := by
  rw [Point, flat_contract_iff, covBy_iff_eRelRk_eq_one, eRelRk_closure_left,
    union_comm C, ← eRelRk_eq_eRelRk_union, and_iff_right (closure_flat _ _),
    ← eRelRk_eq_eRk_contract, and_assoc, and_assoc, and_congr_right_iff, and_comm,
    and_congr_left_iff, iff_and_self]
  rintro h - -
  rw [← h.closure]
  exact M.closure_subset_closure subset_union_right

/-- Points of `M ／ C` are equivalent to flats covering `M.closure C`. -/
@[simps] def pointContractCovByEquiv (M : Matroid α) (C : Set α) :
    {P // (M ／ C).Point P} ≃ {F // M.closure C ⋖[M] F} where
  toFun P := ⟨P ∪ M.closure C, by
    obtain ⟨P, hP⟩ := P
    rw [← contract_inter_ground_eq, point_contract_iff, closure_inter_ground] at hP
    convert hP.1 using 1
    rw [subset_antisymm_iff, union_subset_iff, and_iff_right subset_union_right,
      union_subset_iff, and_iff_left subset_union_left, ← hP.1.flat_right.closure,
      ← closure_inter_ground]
    exact ⟨M.closure_subset_closure subset_union_left,
      (M.subset_closure _).trans subset_union_right⟩⟩
  invFun P := ⟨P \ C, by
    obtain ⟨P, hP⟩ := P
    rw [← closure_inter_ground] at hP
    rwa [diff_eq_diff_inter_of_subset hP.subset_ground_right, ← contract_inter_ground_eq,
      point_contract_iff, and_iff_left disjoint_sdiff_left, union_diff_self,
      union_eq_self_of_subset_left, closure_inter_ground]
    exact (M.subset_closure _).trans hP.subset ⟩
  left_inv := by
    rintro ⟨P,hP⟩
    simp only [Subtype.mk.injEq]
    rw [← contract_inter_ground_eq, point_contract_iff] at hP
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

lemma Point.eq_or_eq_of_flat_of_subset (hP : M.Point P) (hF : M.Flat F) (h : F ⊆ P) :
    F = M.closure ∅ ∨ F = P :=
  hP.covBy.eq_or_eq hF hF.loops_subset h

lemma Point.subset_or_inter_eq_loops_of_flat (hP : M.Point P) (hF : M.Flat F) :
    P ⊆ F ∨ P ∩ F = M.closure ∅ := by
  obtain (h | h) := hP.eq_or_eq_of_flat_of_subset (hP.flat.inter hF) inter_subset_left
  · exact Or.inr h
  exact Or.inl (inter_eq_left.1 h)

-- /-- Each flat `F` induces a partition of the set of points not contained in `F`. -/
-- def Flat.covByPointPartition {F : Set α} (hF : M.Flat F) :
--     Partition {P | M.Point P ∧ ¬ (P ⊆ F)} := Partition.ofPairwiseDisjoint'
--   (parts := (fun F' ↦ {P | P ⊆ F' ∧ ¬ (P ⊆ F)}) '' hF.covByPartition)
--   (pairwiseDisjoint := by
--     rintro Ps ⟨_, h, rfl⟩
--     simp

--     )
--   (forall_nonempty := sorry)
--   (eq_sUnion := sorry)





abbrev Line (M : Matroid α) (L : Set α) := M.Flat L ∧ M.eRk L = 2

lemma Line.flat (hL : M.Line L) : M.Flat L :=
  hL.1

lemma Line.eRk (hL : M.Line L) : M.eRk L = 2 :=
  hL.2

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma Line.subset_ground (hL : M.Line L) : L ⊆ M.E :=
  hL.1.subset_ground

lemma Line.isRkFinite (hL : M.Line L) : M.IsRkFinite L := by
  simp [← eRk_ne_top_iff, hL.eRk]

lemma Line.mem_iff_covBy (hL : M.Line L) (he : M.Nonloop e) : e ∈ L ↔ M.closure {e} ⋖[M] L := by
  rw [(M.closure_flat {e}).covBy_iff_eRelRk_eq_one hL.flat, hL.flat.closure_subset_iff_subset,
    singleton_subset_iff, iff_self_and, eRelRk_closure_left]
  intro heL
  rw [isRkFinite_singleton.eRelRk_eq_sub (by simpa), he.eRk_eq, hL.eRk]
  rfl

lemma Nonloop.closure_covBy_iff (he : M.Nonloop e) : M.closure {e} ⋖[M] L ↔ M.Line L ∧ e ∈ L := by
  refine ⟨fun h ↦ ⟨⟨h.flat_right, ?_⟩,h.subset <| M.mem_closure_self e⟩,
    fun ⟨hL, heL⟩ ↦ by rwa [← hL.mem_iff_covBy he]⟩
  rw [h.eRk_eq, eRk_closure_eq, he.eRk_eq]
  rfl

def Nonloop.lineContractPointEquiv (he : M.Nonloop e) :
    {P // (M ／ e).Point P} ≃ {L // M.Line L ∧ e ∈ L} :=
  (M.pointContractCovByEquiv {e}).trans (Equiv.subtypeEquivRight (fun _ ↦ he.closure_covBy_iff))

abbrev Plane (M : Matroid α) (P : Set α) := M.Flat P ∧ M.eRk P = 3

lemma Plane.flat (hP : M.Plane P) : M.Flat P :=
  hP.1

lemma Plane.eRk (hP : M.Plane P) : M.eRk P = 3 :=
  hP.2
