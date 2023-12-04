import Matroid.Flat
import Matroid.Simple

open Set BigOperators

namespace Matroid

variable {ι α : Type*} {M : Matroid α} {B : Set α} {Xs Ys Js Is : ι → Set α} {i j : ι}

section ModularBase

/-- A base `B` is a modular base for an indexed set family if its intersection with every set
  in the family is a basis for that set. -/
@[pp_dot] def ModularBase (M : Matroid α) (B : Set α) (Xs : ι → Set α) :=
  M.Base B ∧ ∀ i, M.Basis ((Xs i) ∩ B) (Xs i)

theorem ModularBase.base (h : M.ModularBase B Xs) : M.Base B :=
  h.1

theorem ModularBase.indep (h : M.ModularBase B Xs) : M.Indep B :=
  h.base.indep

theorem ModularBase.basis_inter (h : M.ModularBase B Xs) (i : ι) : M.Basis ((Xs i) ∩ B) (Xs i) :=
  h.2 i

theorem ModularBase.subset_cl_inter (h : M.ModularBase B Xs) (i : ι) : Xs i ⊆ M.cl ((Xs i) ∩ B) :=
  (h.basis_inter i).subset_cl

theorem ModularBase.cl_inter_eq (h : M.ModularBase B Xs) (i : ι) : M.cl (Xs i ∩ B) = M.cl (Xs i) :=
  (h.basis_inter i).cl_eq_cl

@[aesop unsafe 5% (rule_sets [Matroid])]
theorem ModularBase.subset_ground (h : M.ModularBase B Xs) (i : ι) : Xs i ⊆ M.E :=
  (h.basis_inter i).subset_ground

theorem ModularBase.subtype (h : M.ModularBase B Xs) (A : Set ι) :
    M.ModularBase B (fun i : A ↦ Xs i) :=
  ⟨h.1, fun ⟨i,_⟩ ↦ h.2 i⟩

@[simp] theorem modularBase_pair_iff {B X Y : Set α} :
    M.ModularBase B (fun i : ({X,Y} : Set (Set α)) ↦ i) ↔
      M.Base B ∧ M.Basis (X ∩ B) X ∧ M.Basis (Y ∩ B) Y := by
  simp [ModularBase]

theorem ModularBase.basis_iInter [Nonempty ι] (h : M.ModularBase B Xs) :
    M.Basis ((⋂ i, Xs i) ∩ B) (⋂ i, Xs i) :=
  h.1.indep.interBasis_iInter (fun _ ↦ h.2 _)

theorem ModularBase.basis_biInter (h : M.ModularBase B Xs) {A : Set ι} (hA : A.Nonempty)  :
    M.Basis ((⋂ i ∈ A, Xs i) ∩ B) (⋂ i ∈ A, Xs i) :=
  h.1.indep.interBasis_biInter hA (fun _ _ ↦ h.2 _)

@[aesop unsafe 5% (rule_sets [Matroid])]
theorem ModularBase.iInter_subset_ground [Nonempty ι] (h : M.ModularBase B Xs) :
    ⋂ i, Xs i ⊆ M.E :=
  h.basis_iInter.subset_ground

theorem ModularBase.biInter_subset_ground (h : M.ModularBase B Xs) {A : Set ι} (hA : A.Nonempty) :
    ⋂ i ∈ A, Xs i ⊆ M.E :=
  (h.basis_biInter hA).subset_ground

theorem ModularBase.basis_iUnion (h : M.ModularBase B Xs) :
    M.Basis ((⋃ i, Xs i) ∩ B) (⋃ i, Xs i) := by
  simp_rw [h.1.indep.inter_basis_cl_iff_subset_cl_inter, iUnion_subset_iff]
  exact fun i ↦ (h.subset_cl_inter i).trans
    (M.cl_subset_cl (inter_subset_inter_left _ (subset_iUnion _ i)))

theorem ModularBase.basis_biUnion (h : M.ModularBase B Xs) (A : Set ι) :
    M.Basis ((⋃ i ∈ A, Xs i) ∩ B) (⋃ i ∈ A, Xs i) := by
  convert (h.subtype A).basis_iUnion <;> simp

theorem exists_modularBase_of_iUnion_indep (h : M.Indep (⋃ i, Xs i)) :
    ∃ B, M.ModularBase B Xs := by
  obtain ⟨B, hB, hIB⟩ := h.exists_base_superset
  refine ⟨B, hB, fun i ↦ ?_⟩
  rw [inter_eq_self_of_subset_left <| iUnion_subset_iff.1 hIB i]
  exact (h.subset (subset_iUnion _ i)).basis_self

theorem Base.modularBase_of_forall_subset_cl (hB : M.Base B) (h : ∀ i, Xs i ⊆ M.cl ((Xs i) ∩ B)) :
    M.ModularBase B Xs := by
  exact ⟨hB, fun i ↦ hB.indep.inter_basis_cl_iff_subset_cl_inter.2 (h i)⟩

theorem ModularBase.modularBase_of_forall_subset_subset_cl (hB : M.ModularBase B Xs)
    (hXY : ∀ i, Xs i ⊆ Ys i) (hYX : ∀ i, Ys i ⊆ M.cl (Xs i)) : M.ModularBase B Ys := by
  refine ⟨hB.base, fun i ↦ hB.indep.inter_basis_cl_iff_subset_cl_inter.2 ?_⟩
  refine (hYX i).trans (M.cl_subset_cl_of_subset_cl ?_)
  exact (hB.2 i).subset_cl.trans (M.cl_subset_cl (inter_subset_inter_left B (hXY i)))

theorem ModularBase.modularBase_cls (hB : M.ModularBase B Xs) :
    M.ModularBase B (fun i ↦ M.cl (Xs i)) :=
  hB.modularBase_of_forall_subset_subset_cl (fun i ↦ M.subset_cl (Xs i)) (fun i ↦ Subset.rfl)

theorem ModularBase.iInter_cl_eq_cl_iInter [Nonempty ι] (hB : M.ModularBase B Xs) :
    (⋂ i : ι, M.cl (Xs i)) = M.cl (⋂ i : ι, Xs i) := by
  simp_rw [subset_antisymm_iff, subset_iInter_iff, ← hB.cl_inter_eq]
  rw [← cl_iInter_eq_biInter_cl_of_iUnion_indep, ← iInter_inter B Xs]
  · refine ⟨M.cl_subset_cl (inter_subset_left _ _), fun i ↦ ?_⟩
    rw [hB.cl_inter_eq]
    exact M.cl_subset_cl (iInter_subset _ i)
  exact hB.base.indep.subset (iUnion_subset (fun _ ↦ inter_subset_right _ _))

end ModularBase
section ModularFamily

def ModularFamily (M : Matroid α) (Xs : ι → Set α) := ∃ B, M.ModularBase B Xs

theorem Indep.modularFamily (hI : M.Indep I) (hXs : ∀ i, M.Basis ((Xs i) ∩ I) (Xs i)) :
    M.ModularFamily Xs := by
  simp_rw [hI.inter_basis_cl_iff_subset_cl_inter] at hXs
  obtain ⟨B, hB, hIB⟩ := hI
  refine ⟨B, hB, ?_⟩
  simp_rw [hB.indep.inter_basis_cl_iff_subset_cl_inter]
  exact fun i ↦ (hXs i).trans (M.cl_subset_cl (inter_subset_inter_right _ hIB))

theorem ModularFamily.subset_ground_of_mem (h : M.ModularFamily Xs) (i : ι) : Xs i ⊆ M.E :=
  let ⟨_, h⟩ := h
  h.subset_ground i

theorem ModularFamily.iInter_cl_eq_cl_iInter [Nonempty ι] (hXs : M.ModularFamily Xs) :
    (⋂ i : ι, M.cl (Xs i)) = M.cl (⋂ i : ι, Xs i) :=
  let ⟨_, h⟩ := hXs
  h.iInter_cl_eq_cl_iInter

theorem Indep.modularFamily_of_subsets (hI : M.Indep I) (hJs : ⋃ i, Js i ⊆ I) :
    M.ModularFamily Js := by
  refine hI.modularFamily (fun i ↦ ?_)
  have hJI : Js i ⊆ I := (subset_iUnion _ i).trans hJs
  rw [inter_eq_self_of_subset_left hJI]
  exact (hI.subset hJI).basis_self

theorem ModularFamily.modularFamily_of_forall_subset_cl (h : M.ModularFamily Xs)
    (hXY : ∀ i, Xs i ⊆ Ys i) (hYX : ∀ i, Ys i ⊆ M.cl (Xs i)) : M.ModularFamily Ys :=
  let ⟨B, hB⟩ := h
  ⟨B, hB.modularBase_of_forall_subset_subset_cl hXY hYX⟩

theorem ModularFamily.cls_modularFamily (h : M.ModularFamily Xs) :
    M.ModularFamily (fun i ↦ M.cl (Xs i)) :=
  let ⟨B, hB⟩ := h
  ⟨B, hB.modularBase_cls⟩

/-- Sets `X,Y` are a modular pair if they form a modular family as a type. -/
def ModularPair (M : Matroid α) (X Y : Set α) :=
    M.ModularFamily (fun i : Bool ↦ bif i then X else Y)

theorem ModularPair.symm (h : M.ModularPair X Y) : M.ModularPair Y X := by
   obtain ⟨B, hB⟩ := h
   exact ⟨B, hB.base, fun i ↦ by simpa using hB.2 !i⟩

theorem ModularPair.comm : M.ModularPair X Y ↔ M.ModularPair Y X :=
  ⟨ModularPair.symm, ModularPair.symm⟩

@[aesop unsafe 5% (rule_sets [Matroid])]
theorem ModularPair.subset_ground_left (h : M.ModularPair X Y) : X ⊆ M.E :=
  h.subset_ground_of_mem true

@[aesop unsafe 5% (rule_sets [Matroid])]
theorem ModularPair.subset_ground_right (h : M.ModularPair X Y) : Y ⊆ M.E :=
  h.subset_ground_of_mem false

@[simp] theorem modularPair_iff {M : Matroid α} {X Y : Set α} :
    M.ModularPair X Y ↔ ∃ I, M.Indep I ∧ M.Basis (X ∩ I) X ∧ M.Basis (Y ∩ I) Y := by
  simp only [ModularPair, ModularFamily, mem_singleton_iff, modularBase_pair_iff]
  refine ⟨fun ⟨B, hB, hB'⟩ ↦ ⟨B, hB.indep, ?_⟩,
    fun ⟨I, ⟨B, hB, hIB⟩, hIX, hIY⟩ ↦ ⟨B, hB, ?_⟩ ⟩
  · exact ⟨by simpa using hB' true, by simpa using hB' false⟩
  simp only [Bool.forall_bool, cond_false, cond_true]
  rw [← hIX.eq_of_subset_indep (hB.indep.inter_left X) (inter_subset_inter_right _ hIB)
    (inter_subset_left _ _), ← hIY.eq_of_subset_indep (hB.indep.inter_left Y)
    (inter_subset_inter_right _ hIB) (inter_subset_left _ _)]
  exact ⟨hIY,hIX⟩

theorem ModularFamily.modularPair (h : M.ModularFamily Xs) (i j : ι) :
    M.ModularPair (Xs i) (Xs j) := by
  obtain ⟨B, hB⟩ := h
  exact modularPair_iff.2 ⟨B, hB.indep, hB.basis_inter i, hB.basis_inter j⟩

theorem modularPair_iff_exists_subsets_cl_inter :
    M.ModularPair X Y ↔ ∃ I, M.Indep I ∧ X ⊆ M.cl (X ∩ I) ∧ Y ⊆ M.cl (Y ∩ I)  := by
  rw [modularPair_iff]
  refine ⟨fun ⟨I,hI,h⟩ ↦ ⟨I,hI,?_⟩, fun ⟨I,hI,h⟩ ↦ ⟨I,hI,?_⟩⟩
  · rwa [← hI.inter_basis_cl_iff_subset_cl_inter, ← hI.inter_basis_cl_iff_subset_cl_inter]
  rwa [hI.inter_basis_cl_iff_subset_cl_inter, hI.inter_basis_cl_iff_subset_cl_inter]

theorem ModularPair.exists_subsets_cl_inter (h : M.ModularPair X Y) :
    ∃ I, M.Indep I ∧ X ⊆ M.cl (X ∩ I) ∧ Y ⊆ M.cl (Y ∩ I) :=
  modularPair_iff_exists_subsets_cl_inter.1 h

theorem modularPair_iff_exists_basis_basis :
    M.ModularPair X Y ↔ ∃ I J, M.Basis I X ∧ M.Basis J Y ∧ M.Indep (I ∪ J) := by
  rw [modularPair_iff]
  refine ⟨fun ⟨I,hI,hIX,hIY⟩ ↦ ⟨_, _, hIX, hIY, hI.subset (by simp)⟩,
    fun ⟨I,J,hI,hJ,hi⟩ ↦ ⟨_,hi, ?_⟩⟩
  simp_rw [hi.inter_basis_cl_iff_subset_cl_inter]
  use hI.subset_cl.trans (M.cl_subset_cl (subset_inter hI.subset (subset_union_left _ _)))
  exact hJ.subset_cl.trans (M.cl_subset_cl (subset_inter hJ.subset (subset_union_right _ _)))

theorem ModularPair.exists_common_basis (h : M.ModularPair X Y) : ∃ I,
    M.Basis I (X ∪ Y) ∧ M.Basis (I ∩ X) X ∧ M.Basis (I ∩ Y) Y ∧ M.Basis (I ∩ X ∩ Y) (X ∩ Y) := by
  obtain ⟨B, hB⟩ := h
  refine ⟨(X ∪ Y) ∩ B, ?_⟩
  rw [inter_right_comm, inter_eq_self_of_subset_right (subset_union_left _ _),
    inter_right_comm, inter_eq_self_of_subset_right (subset_union_right _ _), inter_right_comm]
  refine ⟨?_, by simpa using hB.basis_inter true, by simpa using hB.basis_inter false, ?_⟩
  · have hu := hB.basis_iUnion
    rwa [← union_eq_iUnion] at hu
  have hi := hB.basis_iInter
  rwa [← inter_eq_iInter] at hi

theorem ModularPair.inter_cl_eq (h : M.ModularPair X Y) : M.cl (X ∩ Y) = M.cl X ∩ M.cl Y := by
  convert (ModularFamily.iInter_cl_eq_cl_iInter h).symm
  · rw [inter_eq_iInter]
  simp_rw [Bool.cond_eq_ite, apply_ite, ← Bool.cond_eq_ite, inter_eq_iInter]

theorem modularPair_of_subset (hXY : X ⊆ Y) (hY : Y ⊆ M.E) : M.ModularPair X Y := by
  obtain ⟨I,J, hI, hJ, hIJ⟩ := M.exists_basis_subset_basis hXY
  refine modularPair_iff.2 ⟨J, hJ.indep, ?_, by rwa [inter_eq_self_of_subset_right hJ.subset]⟩
  rwa [← hI.eq_of_subset_indep (hJ.indep.inter_left X) (subset_inter hI.subset hIJ)
    (inter_subset_left _ _)]

theorem Indep.modularPair_of_union (hi : M.Indep (I ∪ J)) : M.ModularPair I J := by
  simpa only [iUnion_subset_iff, Bool.forall_bool, cond_false, subset_union_right, cond_true,
    subset_union_left, and_self, forall_true_left] using
    hi.modularFamily_of_subsets (Js := fun i ↦ bif i then I else J)

theorem ModularPair.of_subset_cl_subset_cl (h : M.ModularPair X Y) (hXX' : X ⊆ X')
    (hX' : X' ⊆ M.cl X) (hYY' : Y ⊆ Y') (hY' : Y' ⊆ M.cl Y) : M.ModularPair X' Y' := by
  apply ModularFamily.modularFamily_of_forall_subset_cl h
  · simp [hYY', hXX']
  simp [hY', hX']

theorem ModularPair.of_subset_cl_left (h : M.ModularPair X Y) (hXX' : X ⊆ X') (hX' : X' ⊆ M.cl X) :
    M.ModularPair X' Y :=
  h.of_subset_cl_subset_cl hXX' hX' Subset.rfl (M.subset_cl Y)

theorem ModularPair.of_subset_cl_right (h : M.ModularPair X Y) (hYY' : Y ⊆ Y') (hY' : Y' ⊆ M.cl Y) :
    M.ModularPair X Y' :=
  (h.symm.of_subset_cl_left hYY' hY').symm

theorem ModularPair.of_basis_left (h : M.ModularPair I Y) (hIX : M.Basis I X) :
    M.ModularPair X Y :=
  h.of_subset_cl_left hIX.subset hIX.subset_cl

theorem ModularPair.of_basis_right (h : M.ModularPair X J) (hJY : M.Basis J Y) :
    M.ModularPair X Y :=
  h.of_subset_cl_right hJY.subset hJY.subset_cl

theorem ModularPair.of_basis_of_basis (h : M.ModularPair I J) (hIX : M.Basis I X)
    (hJY : M.Basis J Y) : M.ModularPair X Y :=
  (h.of_basis_left hIX).of_basis_right hJY

theorem ModularPair.cl_left (h : M.ModularPair X Y) : M.ModularPair (M.cl X) Y :=
  h.of_subset_cl_left (M.subset_cl X) Subset.rfl

theorem ModularPair.cl_right (h : M.ModularPair X Y) : M.ModularPair X (M.cl Y) :=
  h.symm.cl_left.symm

theorem ModularPair.cl_cl (h : M.ModularPair X Y) : M.ModularPair (M.cl X) (M.cl Y) :=
  h.cl_left.cl_right

theorem modularPair_singleton (he : e ∈ M.E) (hX : X ⊆ M.E) (heX : e ∉ M.cl X) :
    M.ModularPair {e} X := by
  obtain ⟨I, hI⟩ := M.exists_basis X
  have hi : M.Indep (insert e I)
  · rw [hI.indep.insert_indep_iff, hI.cl_eq_cl]
    exact Or.inl ⟨he, heX⟩
  have hI' := hI.insert_basis_insert hi
  rw [← singleton_union] at hI'
  exact hI'.indep.modularPair_of_union.of_basis_right hI

theorem ModularPair.er_add_er (h : M.ModularPair X Y) :
    M.er X + M.er Y = M.er (X ∩ Y) + M.er (X ∪ Y) := by
  obtain ⟨I, hIu, hIX, hIY, hIi⟩ := h.exists_common_basis
  rw [hIi.er_eq_encard, hIu.er_eq_encard, hIX.er_eq_encard, hIY.er_eq_encard,
    ← encard_union_add_encard_inter, ← inter_distrib_left, ← inter_inter_distrib_left,
    ← inter_assoc, inter_eq_self_of_subset_left hIu.subset, add_comm]

theorem rFin.modularPair_iff (hXfin : M.rFin X) (hYfin : M.rFin Y) (hXE : X ⊆ M.E := by aesop_mat)
    (hYE : Y ⊆ M.E := by aesop_mat) :
    M.ModularPair X Y ↔ M.er X + M.er Y = M.er (X ∩ Y) + M.er (X ∪ Y) := by
  refine ⟨fun h ↦ h.er_add_er, fun hr ↦ modularPair_iff_exists_basis_basis.2 ?_ ⟩
  obtain ⟨Ii, hIi⟩ := M.exists_basis (X ∩ Y)
  have hifin : Ii.encard ≠ ⊤
  · simpa using (hXfin.inter_right Y).finite_of_basis hIi
  obtain ⟨IX, hIX, hX⟩ := hIi.indep.subset_basis_of_subset
    (hIi.subset.trans (inter_subset_left _ _))
  obtain ⟨IY, hIY, hY⟩ := hIi.indep.subset_basis_of_subset
    (hIi.subset.trans (inter_subset_right _ _))
  refine ⟨IX, IY, hIX, hIY, ?_⟩
  rw [hIi.er_eq_encard, hIX.er_eq_encard, ← encard_diff_add_encard_of_subset hX,
    add_comm (encard _), add_assoc, WithTop.add_left_cancel_iff hifin, hIY.er_eq_encard,
    ← encard_union_add_encard_inter, ← union_eq_self_of_subset_left hY, ← union_assoc,
    diff_union_self, union_eq_self_of_subset_right hX] at hr
  refine Basis.indep <| (hXfin.union hYfin).basis_of_subset_cl_of_subset_of_encard_le ?_
    (union_subset_union hIX.subset hIY.subset) (le_of_add_le_left hr.le)
  rw [← M.cl_union_cl_left_eq, ← M.cl_union_cl_right_eq]
  exact (M.subset_cl _).trans (M.cl_subset_cl (union_subset_union hIX.subset_cl hIY.subset_cl))

theorem modularPair_iff_r [FiniteRk M] (hXE : X ⊆ M.E := by aesop_mat)
    (hYE : Y ⊆ M.E := by aesop_mat) :
    M.ModularPair X Y ↔ M.r X + M.r Y = M.r (X ∩ Y) + M.r (X ∪ Y) := by
  simp_rw [(M.to_rFin X).modularPair_iff (M.to_rFin Y), ← coe_r_eq, ← Nat.cast_add, Nat.cast_inj]

theorem ModularFamily.modularPair_compl (h : M.ModularFamily Xs) (A : Set ι) :
    M.ModularPair (⋃ i ∈ A, Xs i) (⋃ i ∈ Aᶜ, Xs i) := by
  rw [modularPair_iff]
  obtain ⟨B, hB⟩ := h
  exact ⟨B, hB.indep, hB.basis_biUnion A, hB.basis_biUnion Aᶜ⟩

theorem ModularFamily.modularPair_singleton_compl (h : M.ModularFamily Xs) (i₀ : ι) :
    M.ModularPair (Xs i₀) (⋃ i ∈ ({i₀} : Set ι)ᶜ, Xs i) := by
  convert h.modularPair_compl {i₀}; simp

end ModularFamily

section ModularSet

/-- A `ModularSet` is a set that is a modular pair with every flat. -/
def ModularSet (M : Matroid α) (X : Set α) := ∀ ⦃F⦄, M.Flat F → M.ModularPair X F

@[simp] theorem modularSet_def {M : Matroid α} {X : Set α} :
    M.ModularSet X ↔ ∀ ⦃F⦄, M.Flat F → M.ModularPair X F := Iff.rfl

@[aesop unsafe 5% (rule_sets [Matroid])]
theorem ModularSet.subset_ground (h : M.ModularSet X) : X ⊆ M.E :=
  (h (M.cl_flat ∅)).subset_ground_left

@[simp] theorem modularSet_iff {M : Matroid α} {X : Set α} :
    M.ModularSet X ↔ ∀ ⦃F⦄, M.Flat F → ∃ I, M.Indep I ∧ M.Basis (X ∩ I) X ∧ M.Basis (F ∩ I) F := by
  simp [ModularSet, modularPair_iff]

theorem modularSet_iff_cl {M : Matroid α} {X : Set α} :
    M.ModularSet X ↔ ∀ ⦃F⦄, M.Flat F → ∃ I, M.Indep I ∧ X ⊆ M.cl (X ∩ I) ∧ F ⊆ M.cl (F ∩ I) := by
  rw [modularSet_iff]
  refine ⟨fun h F hF ↦ ?_, fun h F hF ↦ ?_⟩
  · obtain ⟨I, hI, hI'⟩ := h hF
    refine ⟨I, hI, ?_⟩
    rwa [← hI.inter_basis_cl_iff_subset_cl_inter, ← hI.inter_basis_cl_iff_subset_cl_inter]
  obtain ⟨I, hI, hI'⟩ := h hF
  refine ⟨I, hI, ?_⟩
  rwa [hI.inter_basis_cl_iff_subset_cl_inter, hI.inter_basis_cl_iff_subset_cl_inter]

theorem modularSet_ground (M : Matroid α) : M.ModularSet M.E :=
  modularSet_def.2 (fun _ hF ↦ (modularPair_of_subset hF.subset_ground Subset.rfl).symm)

theorem modularSet_empty (M : Matroid α) : M.ModularSet ∅ :=
  modularSet_def.2 (fun _ hF ↦ (modularPair_of_subset (empty_subset _) hF.subset_ground))

theorem modularSet.cl (h : M.ModularSet X) : M.ModularSet (M.cl X) :=
  fun _ hF ↦ (h hF).cl_left

theorem modularSet_singleton (M : Matroid α) (he : e ∈ M.E) : M.ModularSet {e} := by
  refine modularSet_def.2 fun F hF ↦ ?_
  by_cases heF : {e} ⊆ F
  · apply modularPair_of_subset heF hF.subset_ground
  rw [singleton_subset_iff, ← hF.cl] at heF
  exact modularPair_singleton he hF.subset_ground heF

/-- Every modular set in a simple matroid is a flat. -/
theorem ModularSet.Flat [Simple M] (hF : M.ModularSet F) : M.Flat F := by
  by_contra h
  obtain ⟨e, heF, he⟩ := exists_mem_cl_not_mem_of_not_flat h
  rw [modularSet_iff] at hF
  obtain ⟨I, hI, hIF, hIe⟩ := hF (M.cl_flat {e})
  have heM := M.cl_subset_ground F heF
  have heI : e ∈ I
  · rw [hI.inter_basis_cl_iff_subset_cl_inter, cl_singleton_eq,
      cl_eq_self_of_subset_singleton heM (inter_subset_left _ _)] at hIe
    simpa using hIe
  apply hI.not_mem_cl_diff_of_mem heI
  apply mem_of_mem_of_subset <| M.cl_subset_cl_of_subset_cl hIF.subset_cl heF
  apply M.cl_subset_cl
  rw [subset_diff, and_iff_right (inter_subset_right _ _), disjoint_singleton_right]
  exact fun he' ↦ he <| (inter_subset_left _ _) he'

end ModularSet

section Skew

def SkewFamily (M : Matroid α) (Xs : ι → Set α) :=
  M.ModularFamily Xs ∧ ∀ ⦃i j⦄, i ≠ j → Xs i ∩ Xs j ⊆ M.cl ∅

theorem SkewFamily.modularFamily (h : M.SkewFamily Xs) : M.ModularFamily Xs :=
  h.1

@[aesop unsafe 5% (rule_sets [Matroid])]
theorem SkewFamily.subset_ground_of_mem (h : M.SkewFamily Xs) (i : ι) : Xs i ⊆ M.E :=
  h.modularFamily.subset_ground_of_mem i

theorem SkewFamily.loop_of_mem_inter (h : M.SkewFamily Xs) (hij : i ≠ j)
    (he : e ∈ Xs i ∩ Xs j) : M.Loop e :=
  h.2 hij he

theorem SkewFamily.subset_loops_of_ne (h : M.SkewFamily Xs) (hij : i ≠ j) : Xs i ∩ Xs j ⊆ M.cl ∅ :=
  h.2 hij

theorem SkewFamily.disjoint_inter_indep (h : M.SkewFamily Xs) (hI : M.Indep I) (hij : i ≠ j) :
    Disjoint (Xs i ∩ I) (Xs j) := by
  rw [disjoint_iff_forall_ne]
  rintro e ⟨hei, heI⟩ _ hej rfl
  exact (hI.nonloop_of_mem heI).not_loop <| h.loop_of_mem_inter hij ⟨hei,hej⟩

theorem SkewFamily.pairwiseDisjoint_inter_of_indep (h : M.SkewFamily Xs) (hI : M.Indep I) :
    (univ : Set ι).PairwiseDisjoint (fun i ↦ Xs i ∩ I) :=
  fun _ _ _ _ hij ↦ (h.disjoint_inter_indep hI hij).mono_right (inter_subset_left _ _)

theorem SkewFamily.disjoint_of_indep_subsets (h : M.SkewFamily Xs) (hIX : ∀ i, Is i ⊆ Xs i)
    (hIs : ∀ i, M.Indep (Is i)) : univ.PairwiseDisjoint Is :=
  fun i _ j _ hij ↦ disjoint_iff_inter_eq_empty.2 <|
    ((hIs i).inter_right (Is j)).eq_empty_of_subset_loops
    ((inter_subset_inter (hIX i) (hIX j)).trans (h.2 hij).subset)

theorem SkewFamily.cls_skewFamily (h : M.SkewFamily Xs) : M.SkewFamily (fun i ↦ M.cl (Xs i)) := by
  refine ⟨h.modularFamily.cls_modularFamily, fun i j hij ↦ ?_⟩
  have := M.cl_subset_cl_of_subset_cl <| h.subset_loops_of_ne hij
  rwa [← (h.modularFamily.modularPair i j).inter_cl_eq]

theorem skewFamily_iff_exist_bases : M.SkewFamily Xs ↔
    ∃ (Is : ι → Set α), univ.PairwiseDisjoint Is ∧ M.Basis (⋃ i : ι, Is i) (⋃ i : ι, Xs i) ∧
      ∀ i, M.Basis (Is i) (Xs i) := by
  refine ⟨fun h ↦ ?_,
    fun ⟨Is, hdj, hIs, hb⟩ ↦ ⟨hIs.indep.modularFamily fun i ↦ ?_, fun i j hij ↦ ?_⟩⟩
  · obtain ⟨B, hB⟩ := h.modularFamily
    refine ⟨_, ?_, ?_, hB.basis_inter⟩
    · exact h.disjoint_of_indep_subsets (fun i ↦ inter_subset_left _ _)
        (fun i ↦ hB.indep.inter_left _)
    rw [← iUnion_inter]
    exact hB.basis_iUnion
  · rw [hIs.indep.inter_basis_cl_iff_subset_cl_inter]
    exact (hb i).subset_cl.trans (M.cl_subset_cl (subset_inter (hb i).subset (subset_iUnion _ _)))
  refine (inter_subset_inter (M.subset_cl _ (hb i).subset_ground)
    (M.subset_cl _ (hb j).subset_ground)).trans ?_
  rw [← (hb i).cl_eq_cl, ← (hb j).cl_eq_cl, ← (hIs.indep.subset _).cl_inter_eq_inter_cl,
    Disjoint.inter_eq <| hdj (mem_univ i) (mem_univ j) hij]
  exact union_subset (subset_iUnion _ _) (subset_iUnion _ _)

theorem SkewFamily.iUnion_indep_subset_indep (h : M.SkewFamily Xs) (hIX : ∀ i, Is i ⊆ Xs i)
    (hIs : ∀ i, M.Indep (Is i)) : M.Indep (⋃ i, Is i) := by
  choose Js hJs using fun i ↦ (hIs i).subset_basis_of_subset (hIX i)
  refine Indep.subset ?_ <| iUnion_mono (fun i ↦ (hJs i).2)

  obtain ⟨J, hJ⟩ := M.exists_basis (⋃ i, Js i) sorry

  by_contra hcon
  have ex_i : ∃ i e, e ∈ (Js i) \ J
  · sorry

  obtain ⟨i₀, e, hei₀, heJ⟩ := ex_i

  obtain ⟨Ks, hdj, hKs, huKs⟩ := skewFamily_iff_exist_bases.1 h

  have hssE : Js i₀ ∪ (⋃ i ∈ ({i₀}ᶜ : Set ι), Ks i) ⊆ M.E
  · sorry

  obtain ⟨K', hK', hss⟩ := (hJs i₀).1.indep.subset_basis_of_subset sorry hssE

  have hK'' : ∀ i, i ≠ i₀ → Ks i ⊆ K'
  · intro i hne f hf

    by_contra hfK'
    refine hfK' <| hK'.mem_of_insert_indep (Or.inr <| mem_biUnion hne hf) ?_
    rw [hK'.indep.insert_indep_iff_of_not_mem hfK', mem_diff,
      and_iff_right ((huKs i).indep.subset_ground hf)]
    refine not_mem_subset ?_ <| hKs.indep.not_mem_cl_diff_of_mem (mem_iUnion.2 ⟨i,hf⟩)

    rw [hK'.cl_eq_cl, M.cl_subset_cl_iff_subset_cl]



    simp only [mem_compl_iff, mem_singleton_iff, mem_iUnion, not_exists, union_subset_iff,
      iUnion_subset_iff]
    refine ⟨?_, fun j hjne ↦ ?_⟩
    · refine (hJs i₀).1.subset.trans ((huKs i₀).subset_cl.trans (M.cl_subset_cl ?_))
      refine subset_diff_singleton (subset_iUnion Ks i₀) (fun hKsi₀ ↦ ?_)
      exact (hdj (mem_univ i) (mem_univ i₀) hne).ne_of_mem hf hKsi₀ rfl


    sorry
    -- refine hK'.cl_subset_c.trans ?_


  have he' : e ∈ M.cl (K' \ {e})
  · refine mem_of_mem_of_subset (hJ.subset_cl (mem_iUnion_of_mem _ hei₀)) ?_
    rw [cl_subset_cl_iff_subset_cl]
    rintro f hf
    obtain ⟨i, hfi⟩ := mem_iUnion.1 (hJ.subset hf)
    obtain (rfl | hi) := eq_or_ne i₀ i
    · apply M.subset_cl (K' \ {e}) ((diff_subset _ _).trans hK'.indep.subset_ground)
      exact ⟨hss hfi, fun (h : f = e) ↦ heJ <| h ▸ hf⟩
    refine mem_of_mem_of_subset ((hJs i).1.subset.trans (huKs i).subset_cl hfi) (M.cl_subset_cl ?_)
    refine subset_diff_singleton (hK'' i hi.symm) (fun heK ↦ ?_)
    apply Loop.not_nonloop <| h.loop_of_mem_inter hi ⟨(hJs i₀).1.subset hei₀, (huKs i).subset heK⟩
    exact (hK'.indep.subset hss).nonloop_of_mem hei₀

--   exact hK'.indep.not_mem_cl_diff_of_mem (hss hei₀) he'
      -- refine mem_of_mem_of_subset ?_ (M.subset_cl ?_ ((diff_subset _ _).trans hK'.subset_ground)))

    -- rw [hJ.cl_eq_cl, cl_subset_cl_iff_subset_cl hJ.subset_ground, iUnion_subset_iff]
    -- intro i
    -- obtain (rfl | hi) := eq_or_ne i₀ i
    -- · refine subset_trans ?_ (hJ.subset_cl.trans ?_)

  -- have hJ₀K' : e ∈ M.cl
  -- ·


  -- have ex_i : ∃ i, I ∩ (Is i) ⊂ Is i
  -- · by_contra' h
  --   refine hcon (hI.indep.subset (iUnion_subset fun i ↦ ?_))
  --   exact (inter_subset_right I (Is i)).eq_or_ssubset.elim inter_eq_right.1 (fun h' ↦ (h i h').elim)
  -- obtain ⟨i₀, hi₀ss⟩ := ex_i





  --

  -- obtain ⟨J₀, hJ₀, hssJ₀⟩ := (hI.indep.inter_right (Is i₀)).subset_basis_of_subset
  --   (subset_union_left _ (Ks i₀)) (union_subset
  --     ((inter_subset_left _ _).trans hI.indep.subset_ground) (huKs i₀).indep.subset_ground)

  -- -- This is a good test for `aesop_mat`.
  -- have hssE : J₀ ∪ (⋃ i ∈ ({i₀}ᶜ : Set ι), Ks i) ⊆ M.E
  -- · refine union_subset hJ₀.indep.subset_ground ?_
  --   simp only [mem_compl_iff, mem_singleton_iff, iUnion_subset_iff]
  --   exact fun i _ ↦ (huKs i).indep.subset_ground

  -- obtain ⟨K',hK',hss⟩ := hJ₀.indep.subset_basis_of_subset (subset_union_left _ _) hssE


  -- have hK'' : M.Basis K'




  -- have hKd := biUnion_subset_biUnion_left (subset_univ ({i₀}ᶜ : Set ι)) (t := Ks)
  -- rw [biUnion_univ] at hKd
  -- obtain ⟨K', hK', hss⟩ :=
  --   (hKs.indep.subset hKd).subset_basis_of_subset (subset_union_left _ J₀)
  --     (union_subset (hKd.trans hKs.indep.subset_ground) hJ₀.indep.subset_ground)






    -- rw [← inter_eq_right, subset_antisymm_iff, and_iff_right (inter_subset_right _ _),
    --   subset_iff_ssubset_or_eq]
  -- choose Js hJs using fun i ↦ (hIs i).subset_basis_of_subset (hIX i)
  -- refine Indep.subset ?_ <| iUnion_mono (fun i ↦ (hJs i).2)
  -- obtain ⟨Ks, hdj, hKs, huKs⟩ := skewFamily_iff_exist_bases.1 h
  -- obtain ⟨J, hJ⟩ := M.exists_basis (⋃ i, Js i)
  --   (iUnion_subset (fun i ↦ (hJs i).1.indep.subset_ground))
  -- obtain (rfl | hss) := hJ.subset.eq_or_ssubset
  -- · exact hJ.indep
  -- obtain ⟨e, ⟨_,⟨i₀,rfl⟩, (hi₀ : e ∈ Js i₀)⟩, heJs⟩ := exists_of_ssubset hss
  -- obtain ⟨J', hJ', hss⟩  := (hJ.indep.inter_left (Xs i₀)).subset_basis_of_subset
  --   (subset_union_left _ (⋃ i ∈ ({i₀}ᶜ : Set ι), Ks i)) sorry
  -- have hJ'b : M.Basis J' (⋃ i, Xs i) := sorry





  -- have


  -- have hJX : M.Basis J (⋃ i, Xs i)
  -- · refine hJ.basis_of_cl_eq_cl (hJ.subset.trans (iUnion_mono (fun i ↦ (hJs i).1.subset))) ?_
  --   simp_rw [← M.cl_iUnion_cl_eq_cl_iUnion Js,
  --     fun i ↦ (hJs i).1.cl_eq_cl, M.cl_iUnion_cl_eq_cl_iUnion]




  -- replace hJ := hJ.basis_cl_right
  -- rw []

  -- rw [← hJ.subset.antisymm]
  -- · exact hJ.indep
  -- rintro e ⟨_, ⟨i₀,_, rfl⟩, (hei₀ : e ∈ Js i₀)⟩





--   -- obtain ⟨I₀, hI₀⟩ := (hC.diff_singleton_indep heC).subset_basis_of_subset (subset_union_left _ (Js i₀))



-- theorem SkewFamily.mono (h : M.SkewFamily Xs) (hYX : ∀ i, Ys i ⊆ Xs i) : M.SkewFamily Ys := by

--   have hYE : ∀ i, Ys i ⊆ M.E := fun i ↦ (hYX i).trans (h.subset_ground_of_mem i)
--   -- rw [skewFamily_iff_exist_bases] at h ⊢

--   choose Js hJs using (fun i ↦ M.exists_basis (Ys i))

--   have : h.modularFamily






-- theorem SkewFamily.mono (h : M.SkewFamily Xs) (hYX : ∀ i, Ys i ⊆ Xs i) : M.SkewFamily Ys := by
--   _

def Skew (M : Matroid α) (X Y : Set α) := M.SkewFamily (fun i ↦ bif i then X else Y)

theorem Skew.modularPair (h : M.Skew X Y) : M.ModularPair X Y :=
  h.modularFamily

-- theorem skew_iff_of_subset (hXY : X ⊆ Y) (hY : Y ⊆ M.E := by aesop_mat) :
--     M.Skew X Y ↔ X ⊆ M.cl ∅ := by
--   _

theorem skew_iff_exists_bases (X Y : Set α) :
    M.Skew X Y ↔ ∃ I J, M.Indep (I ∪ J) ∧ Disjoint I J ∧ M.Basis I X ∧ M.Basis J Y := by
  change (M.ModularPair X Y ∧ _) ↔ _
  rw [modularPair_iff_exists_basis_basis]
  simp only [exists_and_left, ne_eq, Bool.forall_bool, Bool.not_eq_false, cond_false,
    Bool.not_eq_true, cond_true, inter_self, IsEmpty.forall_iff, forall_true_left, true_and,
    and_true]
  refine ⟨fun ⟨⟨I, hI, J, hJ, hIJ⟩, h, _⟩ ↦ ⟨I, J, hIJ, ?_, hI, hJ⟩,
    fun ⟨I, J, hu, hdj, hI, hJ⟩ ↦ ⟨⟨I,hI,J,hJ,hu⟩  , ?_⟩ ⟩
  · rw [disjoint_iff_forall_ne]
    rintro e heI _ heJ rfl
    exact (hI.indep.nonloop_of_mem heI).not_loop (h ⟨hJ.subset heJ, hI.subset heI⟩)
  rw [inter_comm, and_self]
  refine (inter_subset_inter hI.subset_cl hJ.subset_cl).trans ?_
  rw [← hu.cl_inter_eq_inter_cl, hdj.inter_eq]

-- theorem skewFamily.sum_er_eq_er_biUniµon (h : M.SkewFamily Xs) (A : Finset ι) :
--     ∑ i in A, M.er (Xs i) = M.er (⋃ i ∈ A, Xs i) := by
--   classical
--   apply A.induction_on (p := fun A ↦ ∑ i in A, M.er (Xs i) = M.er (⋃ i ∈ (A : Set ι), Xs i))
--   · simp
--   intro a s has hs
--   simp only [Finset.mem_coe, Finset.coe_insert, mem_insert_iff, iUnion_iUnion_eq_or_left]
  -- have := ∑ i in A, M.er (Xs i) = M.er (⋃ i ∈ (A : Set ι), Xs i)

-- theorem skewFamily_iff_exists_base : M.SkewFamily Xs ↔ ∃ B, M.Base B ∧
--     univ.PairwiseDisjoint (fun i ↦ Xs i ∩ B) ∧ ∀ i, M.Basis (Xs i ∩ B) (Xs i) := by

--   refine ⟨fun h ↦ ?_, fun ⟨B, hB, hdj, hbs⟩ ↦ ?_⟩








end Skew


end Matroid
