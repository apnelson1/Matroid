import Matroid.Flat
import Matroid.Simple
import Matroid.ForMathlib.Card
import Mathlib.Order.ModularLattice

open Set BigOperators

namespace Matroid

variable {ι α : Type*} {M : Matroid α} {B I J X X' Y Y' F : Set α} {Xs Ys Js Is : ι → Set α}
  {i j : ι} {e f : α}

section ModularBase

/-- A base `B` is a modular base for an indexed set family if it contains bases for all the sets
  in the family. -/
def ModularBase (M : Matroid α) (B : Set α) (Xs : ι → Set α) :=
  M.Base B ∧ ∀ i, M.Basis ((Xs i) ∩ B) (Xs i)

lemma ModularBase.base (h : M.ModularBase B Xs) : M.Base B :=
  h.1

lemma ModularBase.indep (h : M.ModularBase B Xs) : M.Indep B :=
  h.base.indep

lemma ModularBase.basis_inter (h : M.ModularBase B Xs) (i : ι) : M.Basis ((Xs i) ∩ B) (Xs i) :=
  h.2 i

lemma ModularBase.subset_cl_inter (h : M.ModularBase B Xs) (i : ι) : Xs i ⊆ M.cl ((Xs i) ∩ B) :=
  (h.basis_inter i).subset_cl

lemma ModularBase.cl_inter_eq (h : M.ModularBase B Xs) (i : ι) : M.cl (Xs i ∩ B) = M.cl (Xs i) :=
  (h.basis_inter i).cl_eq_cl

@[aesop unsafe 5% (rule_sets := [Matroid])]
lemma ModularBase.subset_ground (h : M.ModularBase B Xs) (i : ι) : Xs i ⊆ M.E :=
  (h.basis_inter i).subset_ground

lemma ModularBase.subtype (h : M.ModularBase B Xs) (A : Set ι) :
    M.ModularBase B (fun i : A ↦ Xs i) :=
  ⟨h.1, fun ⟨i,_⟩ ↦ h.2 i⟩

@[simp] lemma modularBase_pair_iff {B X Y : Set α} :
    M.ModularBase B (fun i : ({X,Y} : Set (Set α)) ↦ i) ↔
      M.Base B ∧ M.Basis (X ∩ B) X ∧ M.Basis (Y ∩ B) Y := by
  simp [ModularBase]

lemma ModularBase.basis_iInter [Nonempty ι] (h : M.ModularBase B Xs) :
    M.Basis ((⋂ i, Xs i) ∩ B) (⋂ i, Xs i) :=
  h.1.indep.interBasis_iInter (fun _ ↦ h.2 _)

lemma ModularBase.basis_biInter (h : M.ModularBase B Xs) {A : Set ι} (hA : A.Nonempty)  :
    M.Basis ((⋂ i ∈ A, Xs i) ∩ B) (⋂ i ∈ A, Xs i) :=
  h.1.indep.interBasis_biInter hA (fun _ _ ↦ h.2 _)

@[aesop unsafe 5% (rule_sets := [Matroid])]
lemma ModularBase.iInter_subset_ground [Nonempty ι] (h : M.ModularBase B Xs) :
    ⋂ i, Xs i ⊆ M.E :=
  h.basis_iInter.subset_ground

lemma ModularBase.biInter_subset_ground (h : M.ModularBase B Xs) {A : Set ι} (hA : A.Nonempty) :
    ⋂ i ∈ A, Xs i ⊆ M.E :=
  (h.basis_biInter hA).subset_ground

lemma ModularBase.basis_iUnion (h : M.ModularBase B Xs) :
    M.Basis ((⋃ i, Xs i) ∩ B) (⋃ i, Xs i) := by
  simp_rw [h.1.indep.inter_basis_cl_iff_subset_cl_inter, iUnion_subset_iff]
  exact fun i ↦ (h.subset_cl_inter i).trans
    (M.cl_subset_cl (inter_subset_inter_left _ (subset_iUnion _ i)))

lemma ModularBase.basis_biUnion (h : M.ModularBase B Xs) (A : Set ι) :
    M.Basis ((⋃ i ∈ A, Xs i) ∩ B) (⋃ i ∈ A, Xs i) := by
  convert (h.subtype A).basis_iUnion <;> simp

lemma exists_modularBase_of_iUnion_indep (h : M.Indep (⋃ i, Xs i)) :
    ∃ B, M.ModularBase B Xs := by
  obtain ⟨B, hB, hIB⟩ := h.exists_base_superset
  refine ⟨B, hB, fun i ↦ ?_⟩
  rw [inter_eq_self_of_subset_left <| iUnion_subset_iff.1 hIB i]
  exact (h.subset (subset_iUnion _ i)).basis_self

lemma Base.modularBase_of_forall_subset_cl (hB : M.Base B) (h : ∀ i, Xs i ⊆ M.cl ((Xs i) ∩ B)) :
    M.ModularBase B Xs := by
  exact ⟨hB, fun i ↦ hB.indep.inter_basis_cl_iff_subset_cl_inter.2 (h i)⟩

lemma ModularBase.modularBase_of_forall_subset_subset_cl (hB : M.ModularBase B Xs)
    (hXY : ∀ i, Xs i ⊆ Ys i) (hYX : ∀ i, Ys i ⊆ M.cl (Xs i)) : M.ModularBase B Ys := by
  refine ⟨hB.base, fun i ↦ hB.indep.inter_basis_cl_iff_subset_cl_inter.2 ?_⟩
  refine (hYX i).trans (M.cl_subset_cl_of_subset_cl ?_)
  exact (hB.2 i).subset_cl.trans (M.cl_subset_cl (inter_subset_inter_left B (hXY i)))

lemma ModularBase.modularBase_cls (hB : M.ModularBase B Xs) :
    M.ModularBase B (fun i ↦ M.cl (Xs i)) :=
  hB.modularBase_of_forall_subset_subset_cl (fun i ↦ M.subset_cl (Xs i)) (fun i ↦ Subset.rfl)

lemma ModularBase.iInter_cl_eq_cl_iInter [Nonempty ι] (hB : M.ModularBase B Xs) :
    (⋂ i : ι, M.cl (Xs i)) = M.cl (⋂ i : ι, Xs i) := by
  simp_rw [subset_antisymm_iff, subset_iInter_iff, ← hB.cl_inter_eq]
  rw [← cl_iInter_eq_iInter_cl_of_iUnion_indep, ← iInter_inter B Xs]
  · refine ⟨M.cl_subset_cl (inter_subset_left _ _), fun i ↦ ?_⟩
    rw [hB.cl_inter_eq]
    exact M.cl_subset_cl (iInter_subset _ i)
  exact hB.base.indep.subset (iUnion_subset (fun _ ↦ inter_subset_right _ _))

end ModularBase
section ModularFamily

/-- A set family is a `ModularFamily` if it has a modular base. -/
def ModularFamily (M : Matroid α) (Xs : ι → Set α) := ∃ B, M.ModularBase B Xs

lemma Indep.modularFamily (hI : M.Indep I) (hXs : ∀ i, M.Basis ((Xs i) ∩ I) (Xs i)) :
    M.ModularFamily Xs := by
  simp_rw [hI.inter_basis_cl_iff_subset_cl_inter] at hXs
  obtain ⟨B, hB, hIB⟩ := hI.exists_base_superset
  refine ⟨B, hB, ?_⟩
  simp_rw [hB.indep.inter_basis_cl_iff_subset_cl_inter]
  exact fun i ↦ (hXs i).trans (M.cl_subset_cl (inter_subset_inter_right _ hIB))

lemma ModularFamily.subset_ground_of_mem (h : M.ModularFamily Xs) (i : ι) : Xs i ⊆ M.E :=
  let ⟨_, h⟩ := h
  h.subset_ground i

lemma ModularFamily.iInter_cl_eq_cl_iInter [Nonempty ι] (hXs : M.ModularFamily Xs) :
    (⋂ i : ι, M.cl (Xs i)) = M.cl (⋂ i : ι, Xs i) :=
  let ⟨_, h⟩ := hXs
  h.iInter_cl_eq_cl_iInter

lemma Indep.modularFamily_of_subsets (hI : M.Indep I) (hJs : ⋃ i, Js i ⊆ I) :
    M.ModularFamily Js := by
  refine hI.modularFamily (fun i ↦ ?_)
  have hJI : Js i ⊆ I := (subset_iUnion _ i).trans hJs
  rw [inter_eq_self_of_subset_left hJI]
  exact (hI.subset hJI).basis_self

lemma ModularFamily.modularFamily_of_forall_subset_cl (h : M.ModularFamily Xs)
    (hXY : ∀ i, Xs i ⊆ Ys i) (hYX : ∀ i, Ys i ⊆ M.cl (Xs i)) : M.ModularFamily Ys :=
  let ⟨B, hB⟩ := h
  ⟨B, hB.modularBase_of_forall_subset_subset_cl hXY hYX⟩

lemma ModularFamily.cls_modularFamily (h : M.ModularFamily Xs) :
    M.ModularFamily (fun i ↦ M.cl (Xs i)) :=
  let ⟨B, hB⟩ := h
  ⟨B, hB.modularBase_cls⟩

@[simp] lemma modularFamily_of_isEmpty [IsEmpty ι] : M.ModularFamily Xs :=
  M.empty_indep.modularFamily_of_subsets (by simp)

@[simp] lemma modularFamily_iff_of_subsingleton [Subsingleton ι] :
    M.ModularFamily Xs ↔ ∀ i, Xs i ⊆ M.E := by
  obtain (h | ⟨⟨i⟩⟩) := isEmpty_or_nonempty ι; simp
  refine ⟨fun h ↦ h.subset_ground_of_mem, fun h ↦ ?_⟩
  obtain ⟨I, hI⟩ := M.exists_basis (Xs i)
  obtain ⟨B, hB, hIB⟩ := hI.indep.exists_base_superset
  refine ⟨B, hB, fun j ↦ ?_⟩
  rwa [Subsingleton.elim j i, inter_comm, hI.inter_eq_of_subset_indep hIB hB.indep]

lemma ModularFamily_of_loopEquiv (h : M.ModularFamily Xs) (he : ∀ i, M.LoopEquiv (Xs i) (Ys i)) :
    M.ModularFamily Ys := by
  obtain ⟨B, hB⟩ := h
  refine ⟨B, hB.base, fun i ↦ ?_⟩
  rw [← (he i).basis_iff, ← (he i).inter_eq_of_indep hB.indep]
  exact hB.basis_inter i

lemma ModularFamily.ofRestrict' {R : Set α}
    (h : (M ↾ R).ModularFamily Xs) : M.ModularFamily (fun i ↦ (Xs i) ∩ M.E) := by
  obtain ⟨B, hBb, hB⟩ := h
  obtain ⟨B', hB'⟩ := hBb.indep.of_restrict.exists_base_superset
  refine' ⟨B', hB'.1, fun i ↦ _⟩
  obtain Basis := hB i
  have R_B'_inter_eq : R ∩ B' = B := by
    rw [ext_iff]
    refine' fun x ↦ ⟨fun x_mem ↦ _, fun x_mem ↦ ⟨hBb.subset_ground x_mem, hB'.2 x_mem⟩⟩
    by_contra x_nB
    apply (hB'.1.indep.subset (insert_subset x_mem.2 hB'.2)).not_dep
    rw [Dep, and_iff_left ((insert_subset x_mem.2 hB'.2).trans hB'.1.subset_ground)]
    exact (restrict_dep_iff.1 (hBb.insert_dep ⟨x_mem.1, x_nB⟩)).1
  simp only
  rw [basis_restrict_iff'] at Basis
  rw [ ← inter_eq_self_of_subset_left Basis.2, inter_right_comm _ R, inter_assoc, R_B'_inter_eq,
    inter_assoc, inter_eq_self_of_subset_right (hB'.2.trans hB'.1.subset_ground),
    inter_right_comm, inter_eq_self_of_subset_left Basis.2]
  exact Basis.1

lemma ModularFamily.ofRestrict {M : Matroid α} {R : Set α} (hR : R ⊆ M.E)
    (h : (M ↾ R).ModularFamily Xs) : M.ModularFamily Xs := by
  convert h.ofRestrict' with i
  rw [inter_eq_self_of_subset_left <| (h.subset_ground_of_mem i).trans hR]

/-- A subfamily of a modular family is a modular family. -/
lemma ModularFamily.comp {η : Type*} (h : M.ModularFamily Xs) (t : η → ι) :
    M.ModularFamily (Xs ∘ t) := by
  obtain ⟨B, hB, hBXs⟩ := h
  exact ⟨B, hB, fun i ↦ (by simpa using hBXs (t i))⟩

lemma ModularFamily.set_biInter_comp {η : Type*} (h : M.ModularFamily Xs) (t : η → Set ι)
    (ht : ∀ j, (t j).Nonempty) : M.ModularFamily (fun j ↦ ⋂ i ∈ t j, (Xs i)) := by
  obtain ⟨B, hB⟩ := h; exact ⟨B, hB.base, fun j ↦ hB.basis_biInter (ht j)⟩

/-- Sets `X,Y` are a modular pair if some independent set contains bases for both. -/
def ModularPair (M : Matroid α) (X Y : Set α) :=
    M.ModularFamily (fun i : Bool ↦ bif i then X else Y)

lemma ModularPair.symm (h : M.ModularPair X Y) : M.ModularPair Y X := by
   obtain ⟨B, hB⟩ := h
   exact ⟨B, hB.base, fun i ↦ by simpa using hB.2 !i⟩

lemma ModularPair.comm : M.ModularPair X Y ↔ M.ModularPair Y X :=
  ⟨ModularPair.symm, ModularPair.symm⟩

@[aesop unsafe 5% (rule_sets := [Matroid])]
lemma ModularPair.subset_ground_left (h : M.ModularPair X Y) : X ⊆ M.E :=
  h.subset_ground_of_mem true

@[aesop unsafe 5% (rule_sets := [Matroid])]
lemma ModularPair.subset_ground_right (h : M.ModularPair X Y) : Y ⊆ M.E :=
  h.subset_ground_of_mem false

@[simp] lemma modularPair_iff {M : Matroid α} {X Y : Set α} :
    M.ModularPair X Y ↔ ∃ I, M.Indep I ∧ M.Basis (X ∩ I) X ∧ M.Basis (Y ∩ I) Y := by
  simp only [ModularPair, ModularFamily, mem_singleton_iff, modularBase_pair_iff, indep_iff]
  refine ⟨fun ⟨B, hB, hB'⟩ ↦ ⟨B, indep_iff.1 hB.indep, ?_⟩,
    fun ⟨I, ⟨B, hB, hIB⟩, hIX, hIY⟩ ↦ ⟨B, hB, ?_⟩ ⟩
  · exact ⟨by simpa using hB' true, by simpa using hB' false⟩
  simp only [Bool.forall_bool, cond_false, cond_true]
  rw [← hIX.eq_of_subset_indep (hB.indep.inter_left X) (inter_subset_inter_right _ hIB)
    (inter_subset_left _ _), ← hIY.eq_of_subset_indep (hB.indep.inter_left Y)
    (inter_subset_inter_right _ hIB) (inter_subset_left _ _)]
  exact ⟨hIY,hIX⟩

lemma ModularFamily.modularPair (h : M.ModularFamily Xs) (i j : ι) :
    M.ModularPair (Xs i) (Xs j) := by
  obtain ⟨B, hB⟩ := h
  exact modularPair_iff.2 ⟨B, hB.indep, hB.basis_inter i, hB.basis_inter j⟩

lemma modularPair_iff_exists_subsets_cl_inter :
    M.ModularPair X Y ↔ ∃ I, M.Indep I ∧ X ⊆ M.cl (X ∩ I) ∧ Y ⊆ M.cl (Y ∩ I)  := by
  rw [modularPair_iff]
  refine ⟨fun ⟨I,hI,h⟩ ↦ ⟨I,hI,?_⟩, fun ⟨I,hI,h⟩ ↦ ⟨I,hI,?_⟩⟩
  · rwa [← hI.inter_basis_cl_iff_subset_cl_inter, ← hI.inter_basis_cl_iff_subset_cl_inter]
  rwa [hI.inter_basis_cl_iff_subset_cl_inter, hI.inter_basis_cl_iff_subset_cl_inter]

lemma ModularPair.exists_subsets_cl_inter (h : M.ModularPair X Y) :
    ∃ I, M.Indep I ∧ X ⊆ M.cl (X ∩ I) ∧ Y ⊆ M.cl (Y ∩ I) :=
  modularPair_iff_exists_subsets_cl_inter.1 h

lemma modularPair_iff_exists_basis_basis :
    M.ModularPair X Y ↔ ∃ I J, M.Basis I X ∧ M.Basis J Y ∧ M.Indep (I ∪ J) := by
  rw [modularPair_iff]
  refine ⟨fun ⟨I,hI,hIX,hIY⟩ ↦ ⟨_, _, hIX, hIY, hI.subset (by simp)⟩,
    fun ⟨I,J,hI,hJ,hi⟩ ↦ ⟨_,hi, ?_⟩⟩
  simp_rw [hi.inter_basis_cl_iff_subset_cl_inter]
  use hI.subset_cl.trans (M.cl_subset_cl (subset_inter hI.subset (subset_union_left _ _)))
  exact hJ.subset_cl.trans (M.cl_subset_cl (subset_inter hJ.subset (subset_union_right _ _)))

lemma ModularPair.exists_common_basis (h : M.ModularPair X Y) : ∃ I,
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

lemma ModularPair.inter_cl_eq (h : M.ModularPair X Y) : M.cl (X ∩ Y) = M.cl X ∩ M.cl Y := by
  convert (ModularFamily.iInter_cl_eq_cl_iInter h).symm
  · rw [inter_eq_iInter]
  simp_rw [Bool.cond_eq_ite, apply_ite, ← Bool.cond_eq_ite, inter_eq_iInter]

lemma modularPair_of_subset (hXY : X ⊆ Y) (hY : Y ⊆ M.E) : M.ModularPair X Y := by
  obtain ⟨I,J, hI, hJ, hIJ⟩ := M.exists_basis_subset_basis hXY
  refine modularPair_iff.2 ⟨J, hJ.indep, ?_, by rwa [inter_eq_self_of_subset_right hJ.subset]⟩
  rwa [← hI.eq_of_subset_indep (hJ.indep.inter_left X) (subset_inter hI.subset hIJ)
    (inter_subset_left _ _)]

lemma Indep.modularPair_of_union (hi : M.Indep (I ∪ J)) : M.ModularPair I J := by
  simpa only [iUnion_subset_iff, Bool.forall_bool, cond_false, subset_union_right, cond_true,
    subset_union_left, and_self, forall_true_left] using
    hi.modularFamily_of_subsets (Js := fun i ↦ bif i then I else J)

lemma ModularPair.of_subset_cl_subset_cl (h : M.ModularPair X Y) (hXX' : X ⊆ X')
    (hX' : X' ⊆ M.cl X) (hYY' : Y ⊆ Y') (hY' : Y' ⊆ M.cl Y) : M.ModularPair X' Y' := by
  apply ModularFamily.modularFamily_of_forall_subset_cl h
  · simp [hYY', hXX']
  simp [hY', hX']

lemma ModularPair.of_subset_cl_left (h : M.ModularPair X Y) (hXX' : X ⊆ X') (hX' : X' ⊆ M.cl X) :
    M.ModularPair X' Y :=
  h.of_subset_cl_subset_cl hXX' hX' Subset.rfl (M.subset_cl Y)

lemma ModularPair.of_subset_cl_right (h : M.ModularPair X Y) (hYY' : Y ⊆ Y') (hY' : Y' ⊆ M.cl Y) :
    M.ModularPair X Y' :=
  (h.symm.of_subset_cl_left hYY' hY').symm

lemma ModularPair.of_basis_left (h : M.ModularPair I Y) (hIX : M.Basis I X) :
    M.ModularPair X Y :=
  h.of_subset_cl_left hIX.subset hIX.subset_cl

lemma ModularPair.of_basis_right (h : M.ModularPair X J) (hJY : M.Basis J Y) :
    M.ModularPair X Y :=
  h.of_subset_cl_right hJY.subset hJY.subset_cl

lemma ModularPair.of_basis_of_basis (h : M.ModularPair I J) (hIX : M.Basis I X)
    (hJY : M.Basis J Y) : M.ModularPair X Y :=
  (h.of_basis_left hIX).of_basis_right hJY

lemma ModularPair.cl_left (h : M.ModularPair X Y) : M.ModularPair (M.cl X) Y :=
  h.of_subset_cl_left (M.subset_cl X) Subset.rfl

lemma ModularPair.cl_right (h : M.ModularPair X Y) : M.ModularPair X (M.cl Y) :=
  h.symm.cl_left.symm

lemma ModularPair.cl_cl (h : M.ModularPair X Y) : M.ModularPair (M.cl X) (M.cl Y) :=
  h.cl_left.cl_right

lemma modularPair_singleton (he : e ∈ M.E) (hX : X ⊆ M.E) (heX : e ∉ M.cl X) :
    M.ModularPair {e} X := by
  obtain ⟨I, hI⟩ := M.exists_basis X
  have hi : M.Indep (insert e I) := by
    rw [hI.indep.insert_indep_iff, hI.cl_eq_cl]
    exact Or.inl ⟨he, heX⟩
  have hI' := hI.insert_basis_insert hi
  rw [← singleton_union] at hI'
  exact hI'.indep.modularPair_of_union.of_basis_right hI

lemma ModularPair.er_add_er (h : M.ModularPair X Y) :
    M.er X + M.er Y = M.er (X ∩ Y) + M.er (X ∪ Y) := by
  obtain ⟨I, hIu, hIX, hIY, hIi⟩ := h.exists_common_basis
  rw [hIi.er_eq_encard, hIu.er_eq_encard, hIX.er_eq_encard, hIY.er_eq_encard,
    ← encard_union_add_encard_inter, ← inter_union_distrib_left, ← inter_inter_distrib_left,
    ← inter_assoc, inter_eq_self_of_subset_left hIu.subset, add_comm]

lemma rFin.modularPair_iff (hXfin : M.rFin X) (hYfin : M.rFin Y) (hXE : X ⊆ M.E := by aesop_mat)
    (hYE : Y ⊆ M.E := by aesop_mat) :
    M.ModularPair X Y ↔ M.er X + M.er Y = M.er (X ∩ Y) + M.er (X ∪ Y) := by
  refine ⟨fun h ↦ h.er_add_er, fun hr ↦ modularPair_iff_exists_basis_basis.2 ?_ ⟩
  obtain ⟨Ii, hIi⟩ := M.exists_basis (X ∩ Y)
  have hifin : Ii.encard ≠ ⊤ := by
    simpa using (hXfin.inter_right Y).finite_of_basis hIi
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

lemma modularPair_iff_r [FiniteRk M] (hXE : X ⊆ M.E := by aesop_mat)
    (hYE : Y ⊆ M.E := by aesop_mat) :
    M.ModularPair X Y ↔ M.r X + M.r Y = M.r (X ∩ Y) + M.r (X ∪ Y) := by
  simp_rw [(M.to_rFin X).modularPair_iff (M.to_rFin Y), ← coe_r_eq, ← Nat.cast_add, Nat.cast_inj]

lemma ModularFamily.modularPair_compl_biUnion (h : M.ModularFamily Xs) (A : Set ι) :
    M.ModularPair (⋃ i ∈ A, Xs i) (⋃ i ∈ Aᶜ, Xs i) := by
  rw [modularPair_iff]
  obtain ⟨B, hB⟩ := h
  exact ⟨B, hB.indep, hB.basis_biUnion A, hB.basis_biUnion Aᶜ⟩

lemma ModularFamily.modularPair_compl_biInter (h : M.ModularFamily Xs) (A : Set ι)
    (hA : A.Nonempty) (hA' : A ≠ univ) : M.ModularPair (⋂ i ∈ A, Xs i) (⋂ i ∈ Aᶜ, Xs i) := by
  rw [modularPair_iff]
  obtain ⟨B, hB⟩ := h
  exact ⟨B, hB.indep, hB.basis_biInter hA, hB.basis_biInter (by rwa [nonempty_compl])⟩

lemma ModularFamily.modularPair_singleton_compl_biUnion (h : M.ModularFamily Xs) (i₀ : ι) :
    M.ModularPair (Xs i₀) (⋃ i ∈ ({i₀} : Set ι)ᶜ, Xs i) := by
  convert h.modularPair_compl_biUnion {i₀}; simp

lemma ModularFamily.modularPair_singleton_compl_biInter [Nontrivial ι] (h : M.ModularFamily Xs)
    (i₀ : ι) : M.ModularPair (Xs i₀) (⋂ i ∈ ({i₀} : Set ι)ᶜ, Xs i) := by
  convert h.modularPair_compl_biInter {i₀} (by simp)
    (by simpa [ne_univ_iff_exists_not_mem, mem_singleton_iff] using exists_ne i₀); simp

lemma modularPair_insert_cl (M : Matroid α) (X : Set α) (e f : α) :
    M.ModularPair (M.cl (insert e X)) (M.cl (insert f X)) := by
  obtain ⟨I, hI⟩ := M.exists_basis' X

  rw [← cl_insert_cl_eq_cl_insert, ← cl_insert_cl_eq_cl_insert (e := f), ← hI.cl_eq_cl]
  obtain (he | he) := em' (e ∈ M.E)
  · rw [← cl_inter_ground, insert_inter_of_not_mem he, cl_inter_ground]
    exact modularPair_of_subset (M.cl_subset_cl (subset_insert _ _)) (M.cl_subset_ground _)
  obtain (hf | hf) := em' (f ∈ M.E)
  · rw [ModularPair.comm, ← cl_inter_ground, insert_inter_of_not_mem hf, cl_inter_ground]
    exact modularPair_of_subset (M.cl_subset_cl (subset_insert _ _)) (M.cl_subset_ground _)

  obtain (hfI | hfI) := em (f ∈ M.cl I)
  · rw [ModularPair.comm, insert_eq_of_mem hfI]
    exact modularPair_of_subset (M.cl_subset_cl (subset_insert _ _)) (M.cl_subset_ground _)
  rw [cl_insert_cl_eq_cl_insert, cl_insert_cl_eq_cl_insert]
  obtain (hef | hef) := em (e ∈ M.cl (insert f I))
  · refine modularPair_of_subset (M.cl_subset_cl_of_subset_cl ?_) (M.cl_subset_ground _)
    exact insert_subset hef (M.subset_cl_of_subset (subset_insert _ _)
      (insert_subset hf hI.indep.subset_ground))

  refine ModularPair.cl_cl ?_
  apply Indep.modularPair_of_union
  rw [union_insert, union_eq_self_of_subset_right (subset_insert _ _), insert_comm,
    Indep.insert_indep_iff]
  · exact .inl ⟨he, hef⟩
  rw [hI.indep.insert_indep_iff]
  exact .inl ⟨hf, hfI⟩

end ModularFamily

section ModularSet

/-- A `ModularSet` is a set that is a modular pair with every flat. -/
def ModularSet (M : Matroid α) (X : Set α) := ∀ ⦃F⦄, M.Flat F → M.ModularPair X F

@[simp] lemma modularSet_def {M : Matroid α} {X : Set α} :
    M.ModularSet X ↔ ∀ ⦃F⦄, M.Flat F → M.ModularPair X F := Iff.rfl

@[aesop unsafe 5% (rule_sets := [Matroid])]
lemma ModularSet.subset_ground (h : M.ModularSet X) : X ⊆ M.E :=
  (h (M.cl_flat ∅)).subset_ground_left

@[simp] lemma modularSet_iff {M : Matroid α} {X : Set α} :
    M.ModularSet X ↔ ∀ ⦃F⦄, M.Flat F → ∃ I, M.Indep I ∧ M.Basis (X ∩ I) X ∧ M.Basis (F ∩ I) F := by
  simp [ModularSet, modularPair_iff]

lemma modularSet_iff_cl {M : Matroid α} {X : Set α} :
    M.ModularSet X ↔ ∀ ⦃F⦄, M.Flat F → ∃ I, M.Indep I ∧ X ⊆ M.cl (X ∩ I) ∧ F ⊆ M.cl (F ∩ I) := by
  rw [modularSet_iff]
  refine ⟨fun h F hF ↦ ?_, fun h F hF ↦ ?_⟩
  · obtain ⟨I, hI, hI'⟩ := h hF
    refine ⟨I, hI, ?_⟩
    rwa [← hI.inter_basis_cl_iff_subset_cl_inter, ← hI.inter_basis_cl_iff_subset_cl_inter]
  obtain ⟨I, hI, hI'⟩ := h hF
  refine ⟨I, hI, ?_⟩
  rwa [hI.inter_basis_cl_iff_subset_cl_inter, hI.inter_basis_cl_iff_subset_cl_inter]

lemma modularSet_ground (M : Matroid α) : M.ModularSet M.E :=
  modularSet_def.2 (fun _ hF ↦ (modularPair_of_subset hF.subset_ground Subset.rfl).symm)

lemma modularSet_empty (M : Matroid α) : M.ModularSet ∅ :=
  modularSet_def.2 (fun _ hF ↦ (modularPair_of_subset (empty_subset _) hF.subset_ground))

lemma modularSet.cl (h : M.ModularSet X) : M.ModularSet (M.cl X) :=
  fun _ hF ↦ (h hF).cl_left

lemma modularSet_singleton (M : Matroid α) (he : e ∈ M.E) : M.ModularSet {e} := by
  refine modularSet_def.2 fun F hF ↦ ?_
  by_cases heF : {e} ⊆ F
  · apply modularPair_of_subset heF hF.subset_ground
  rw [singleton_subset_iff, ← hF.cl] at heF
  exact modularPair_singleton he hF.subset_ground heF

/-- Every modular set in a simple matroid is a flat. -/
lemma ModularSet.Flat [Simple M] (hF : M.ModularSet F) : M.Flat F := by
  by_contra h
  obtain ⟨e, heF, he⟩ := exists_mem_cl_not_mem_of_not_flat h
  rw [modularSet_iff] at hF
  obtain ⟨I, hI, hIF, hIe⟩ := hF (M.cl_flat {e})
  have heM := M.cl_subset_ground F heF
  have heI : e ∈ I := by
    rw [hI.inter_basis_cl_iff_subset_cl_inter, cl_singleton_eq,
      cl_eq_self_of_subset_singleton heM (inter_subset_left _ _)] at hIe
    simpa using hIe
  apply hI.not_mem_cl_diff_of_mem heI
  apply mem_of_mem_of_subset <| M.cl_subset_cl_of_subset_cl hIF.subset_cl heF
  apply M.cl_subset_cl
  rw [subset_diff, and_iff_right (inter_subset_right _ _), disjoint_singleton_right]
  exact fun he' ↦ he <| (inter_subset_left _ _) he'

end ModularSet

section Skew

/-- A `SkewFamily` is a collection of sets having pairwise disjoint bases whose union is
  independent. -/
def SkewFamily (M : Matroid α) (Xs : ι → Set α) :=
  M.ModularFamily Xs ∧ ∀ ⦃i j⦄, i ≠ j → Xs i ∩ Xs j ⊆ M.cl ∅

lemma SkewFamily.modularFamily (h : M.SkewFamily Xs) : M.ModularFamily Xs :=
  h.1

@[aesop unsafe 5% (rule_sets := [Matroid])]
lemma SkewFamily.subset_ground_of_mem (h : M.SkewFamily Xs) (i : ι) : Xs i ⊆ M.E :=
  h.modularFamily.subset_ground_of_mem i

lemma SkewFamily.loop_of_mem_inter (h : M.SkewFamily Xs) (hij : i ≠ j)
    (he : e ∈ Xs i ∩ Xs j) : M.Loop e :=
  h.2 hij he

lemma SkewFamily.subset_loops_of_ne (h : M.SkewFamily Xs) (hij : i ≠ j) : Xs i ∩ Xs j ⊆ M.cl ∅ :=
  h.2 hij

lemma SkewFamily.disjoint_inter_indep (h : M.SkewFamily Xs) (hI : M.Indep I) (hij : i ≠ j) :
    Disjoint (Xs i ∩ I) (Xs j) := by
  rw [disjoint_iff_forall_ne]
  rintro e ⟨hei, heI⟩ _ hej rfl
  exact (hI.nonloop_of_mem heI).not_loop <| h.loop_of_mem_inter hij ⟨hei,hej⟩

lemma SkewFamily.disjoint_of_indep_subset (h : M.SkewFamily Xs) (hI : M.Indep I) (hIX : I ⊆ Xs i)
    (hij : i ≠ j) : Disjoint I (Xs j) := by
  have hdj := h.disjoint_inter_indep hI hij
  rwa [inter_eq_self_of_subset_right hIX] at hdj

lemma SkewFamily.pairwiseDisjoint_inter_of_indep (h : M.SkewFamily Xs) (hI : M.Indep I) :
    (univ : Set ι).PairwiseDisjoint (fun i ↦ Xs i ∩ I) :=
  fun _ _ _ _ hij ↦ (h.disjoint_inter_indep hI hij).mono_right (inter_subset_left _ _)

lemma SkewFamily.pairwiseDisjoint_of_indep_subsets (h : M.SkewFamily Xs) (hIX : ∀ i, Is i ⊆ Xs i)
    (hIs : ∀ i, M.Indep (Is i)) : univ.PairwiseDisjoint Is :=
  fun i _ j _ hij ↦ disjoint_iff_inter_eq_empty.2 <|
    ((hIs i).inter_right (Is j)).eq_empty_of_subset_loops
    ((inter_subset_inter (hIX i) (hIX j)).trans (h.2 hij).subset)

lemma SkewFamily.pairwiseDisjoint_of_bases (h : M.SkewFamily Xs)
    (hIX : ∀ i, M.Basis (Is i) (Xs i)) : univ.PairwiseDisjoint Is :=
  h.pairwiseDisjoint_of_indep_subsets (fun i ↦ (hIX i).subset) (fun i ↦ (hIX i).indep)

lemma SkewFamily.cls_skewFamily (h : M.SkewFamily Xs) : M.SkewFamily (fun i ↦ M.cl (Xs i)) := by
  refine ⟨h.modularFamily.cls_modularFamily, fun i j hij ↦ ?_⟩
  have := M.cl_subset_cl_of_subset_cl <| h.subset_loops_of_ne hij
  rwa [← (h.modularFamily.modularPair i j).inter_cl_eq]

lemma Indep.skewFamily_of_disjoint_bases (hI : M.Indep (⋃ i, Is i))
    (hdj : univ.PairwiseDisjoint Is) (hIs : ∀ i, M.Basis (Is i) (Xs i)) : M.SkewFamily Xs := by
  refine ⟨hI.modularFamily fun i ↦ ?_, fun i j hij ↦ ?_⟩
  · rw [hI.inter_basis_cl_iff_subset_cl_inter]
    exact (hIs i).subset_cl.trans (M.cl_subset_cl (subset_inter (hIs i).subset (subset_iUnion _ i)))
  refine (inter_subset_inter (M.subset_cl _ (hIs i).subset_ground)
    (M.subset_cl _ (hIs j).subset_ground)).trans ?_
  rw [← (hIs i).cl_eq_cl, ← (hIs j).cl_eq_cl, ← (hI.subset _).cl_inter_eq_inter_cl,
    Disjoint.inter_eq <| hdj (mem_univ i) (mem_univ j) hij]
  exact union_subset (subset_iUnion _ _) (subset_iUnion _ _)

lemma skewFamily_iff_exist_bases : M.SkewFamily Xs ↔
    ∃ (Is : ι → Set α), univ.PairwiseDisjoint Is ∧ M.Basis (⋃ i : ι, Is i) (⋃ i : ι, Xs i) ∧
      ∀ i, M.Basis (Is i) (Xs i) := by
  refine ⟨fun h ↦ ?_, fun ⟨Is, hdj, hIs, hb⟩ ↦ hIs.indep.skewFamily_of_disjoint_bases hdj hb⟩
  obtain ⟨B, hB⟩ := h.modularFamily
  refine ⟨_, ?_, ?_, hB.basis_inter⟩
  · exact h.pairwiseDisjoint_of_indep_subsets (fun i ↦ inter_subset_left _ _)
      (fun i ↦ hB.indep.inter_left _)
  rw [← iUnion_inter]
  exact hB.basis_iUnion

lemma Indep.skewFamily_iff_pairwiseDisjoint (hI : M.Indep (⋃ i : ι, Is i)) :
    M.SkewFamily Is ↔ univ.PairwiseDisjoint Is := by
  refine ⟨fun h ↦ h.pairwiseDisjoint_of_indep_subsets
    (fun _ ↦ Subset.rfl) (fun i ↦ hI.subset (subset_iUnion _ _)),
    fun h ↦ hI.skewFamily_of_disjoint_bases ?_ (fun i ↦ (hI.subset (subset_iUnion _ _)).basis_self)⟩
  exact h

/--
  For a skew family `Xs`, the union of some independent subsets of the `Xs` is independent.
  Quite a nasty proof. Probably the right proof involves relating modularity to the
  lattice of Flats. -/
lemma SkewFamily.iUnion_indep_subset_indep (h : M.SkewFamily Xs) (hIX : ∀ i, Is i ⊆ Xs i)
    (hIs : ∀ i, M.Indep (Is i)) : M.Indep (⋃ i, Is i) := by
  choose Js hJs using fun i ↦ (hIs i).subset_basis_of_subset (hIX i)
  refine Indep.subset ?_ <| iUnion_mono (fun i ↦ (hJs i).2)

  obtain ⟨J, hJ⟩ := M.exists_basis _ (iUnion_subset (fun i ↦ (hJs i).1.indep.subset_ground))

  by_contra hcon
  have ex_i : ∃ i e, e ∈ (Js i) \ J := by
    by_contra! h'
    rw [← hJ.subset.antisymm (iUnion_subset fun i e he ↦ by_contra fun heJ ↦ h' i e ⟨he, heJ⟩)]
      at hcon
    exact hcon hJ.indep

  obtain ⟨i₀, e, hei₀, heJ⟩ := ex_i

  obtain ⟨Ks, hdj, hKs, huKs⟩ := skewFamily_iff_exist_bases.1 h

  have hssE : Js i₀ ∪ (⋃ i ∈ ({i₀}ᶜ : Set ι), Ks i) ⊆ M.E := by
    refine union_subset (hJs i₀).1.indep.subset_ground ?_
    simp only [mem_compl_iff, mem_singleton_iff, iUnion_subset_iff]
    exact fun i _ ↦ (huKs i).indep.subset_ground

  obtain ⟨K', hK', hss⟩ := (hJs i₀).1.indep.subset_basis_of_subset (subset_union_left _ _) hssE

  have hK'' : ∀ i, i ≠ i₀ → Ks i ⊆ K' := by
    intro i hne f hf
    by_contra hfK'
    apply hKs.indep.not_mem_cl_diff_of_mem (mem_iUnion.2 ⟨i,hf⟩)
    have hcl : f ∈ M.cl K' := by
      exact hK'.subset_cl (Or.inr <| mem_biUnion hne hf)

    refine mem_of_mem_of_subset
      (M.cl_subset_cl (subset_diff_singleton hK'.subset hfK') hcl) (M.cl_subset_cl_of_subset_cl ?_)
    simp only [mem_compl_iff, mem_singleton_iff, mem_union, mem_iUnion, exists_prop, not_exists,
      diff_singleton_subset_iff, union_subset_iff, iUnion_subset_iff]
    refine ⟨(hJs i₀).1.subset.trans ?_, fun i _ ↦ ?_⟩
    · refine (huKs i₀).subset_cl.trans (subset_trans (M.cl_subset_cl ?_) (subset_insert _ _))
      refine subset_diff_singleton (subset_iUnion Ks i₀) (fun hf' ↦ ?_)
      exact (hdj (mem_univ i) (mem_univ i₀) hne).ne_of_mem hf hf' rfl

    refine subset_trans ?_ <|
      insert_subset_insert (M.subset_cl _ ((diff_subset _ _).trans hKs.indep.subset_ground))
    rw [insert_diff_singleton]
    exact (subset_iUnion Ks i).trans (subset_insert _ _)

  have he' : e ∈ M.cl (K' \ {e}) := by
    refine mem_of_mem_of_subset (hJ.subset_cl (mem_iUnion_of_mem _ hei₀)) ?_
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

  exact hK'.indep.not_mem_cl_diff_of_mem (hss hei₀) he'

lemma SkewFamily.mono (h : M.SkewFamily Xs) (hYX : ∀ i, Ys i ⊆ Xs i) : M.SkewFamily Ys := by
  choose Is hIs using fun i ↦ M.exists_basis (Ys i) ((hYX i).trans (h.subset_ground_of_mem i))
  refine Indep.skewFamily_of_disjoint_bases ?_ ?_ hIs
  · exact h.iUnion_indep_subset_indep (fun i ↦ (hIs i).subset.trans (hYX i)) (fun i ↦ (hIs i).indep)
  exact h.pairwiseDisjoint_of_indep_subsets
    (fun i ↦ (hIs i).subset.trans (hYX i)) (fun i ↦ (hIs i).indep)

lemma SkewFamily.iUnion_basis_iUnion (h : M.SkewFamily Xs) (hIs : ∀ i, M.Basis (Is i) (Xs i)) :
    M.Basis (⋃ i, Is i) (⋃ i, Xs i) := by
  have hi := h.iUnion_indep_subset_indep (fun i ↦ (hIs i).subset) (fun i ↦ (hIs i).indep)
  exact hi.basis_of_subset_of_subset_cl (iUnion_mono (fun i ↦ (hIs i).subset)) <|
    iUnion_subset (fun i ↦ (hIs i).subset_cl.trans (M.cl_subset_cl (subset_iUnion _ _)))

lemma SkewFamily.sum_er_eq_er_iUnion [Fintype ι] (h : M.SkewFamily Xs) :
    ∑ i, M.er (Xs i) = M.er (⋃ i, Xs i) := by
  choose Is hIs using fun i ↦ M.exists_basis (Xs i) (h.subset_ground_of_mem i)
  rw [(h.iUnion_basis_iUnion hIs).er_eq_encard,
    encard_iUnion _ (h.pairwiseDisjoint_of_bases hIs)]
  simp_rw [(hIs _).er_eq_encard]

lemma rFin.skewFamily_iff_sum_er_eq_er_iUnion [Fintype ι] (hXs : ∀ i, M.rFin (Xs i))
    (hXE : ∀ i, Xs i ⊆ M.E) : M.SkewFamily Xs ↔ ∑ i, M.er (Xs i) = M.er (⋃ i, Xs i) := by
  refine ⟨SkewFamily.sum_er_eq_er_iUnion, fun hsum ↦ ?_⟩
  choose Is hIs using fun i ↦ M.exists_basis (Xs i) (hXE i)
  rw [← er_cl_eq , ← M.cl_iUnion_cl_eq_cl_iUnion] at hsum
  simp_rw [← (fun i ↦ M.er_cl_eq (Xs i)), ← (fun i ↦ (hIs i).cl_eq_cl), M.cl_iUnion_cl_eq_cl_iUnion,
    er_cl_eq, (fun i ↦ (hIs i).indep.er)] at hsum

  apply Indep.skewFamily_of_disjoint_bases ?_ ?_ hIs
  · exact rFin.indep_of_encard_le_er
      ((rFin.iUnion hXs).subset (iUnion_mono (fun i ↦ (hIs i).subset)))
      ((encard_iUnion_le _).trans hsum.le)
  exact pairwiseDisjoint_of_encard_sum_le_encard_iUnion
    (fun i ↦ (hXs i).finite_of_basis (hIs i)) (hsum.le.trans <| M.er_le_encard _)

lemma skewFamily_iff_sum_er_eq_er_iUnion [Fintype ι] [FiniteRk M] (hXs : ∀ i, Xs i ⊆ M.E) :
     M.SkewFamily Xs ↔ ∑ i, M.r (Xs i) = M.r (⋃ i, Xs i) := by
  simp_rw [rFin.skewFamily_iff_sum_er_eq_er_iUnion (fun i ↦ M.to_rFin (Xs i)) hXs,
    ← M.coe_r_eq, ← Nat.cast_sum, Nat.cast_inj]

/-- Two sets are skew if they have disjoint bases with independent union. -/
def Skew (M : Matroid α) (X Y : Set α) := M.SkewFamily (fun i ↦ bif i then X else Y)

@[aesop unsafe 5% (rule_sets := [Matroid])]
lemma Skew.subset_ground_left (h : M.Skew X Y) : X ⊆ M.E :=
  h.subset_ground_of_mem true

@[aesop unsafe 5% (rule_sets := [Matroid])]
lemma Skew.subset_ground_right (h : M.Skew X Y) : Y ⊆ M.E :=
  h.subset_ground_of_mem false

lemma Skew.modularPair (h : M.Skew X Y) : M.ModularPair X Y :=
  h.modularFamily

lemma skew_iff_modularPair_inter_subset_loops :
    M.Skew X Y ↔ M.ModularPair X Y ∧ X ∩ Y ⊆ M.cl ∅ := by
  rw [Skew, SkewFamily, ModularPair, and_congr_right_iff]
  simp [inter_comm X Y]

lemma Skew.inter_subset_loops (h : M.Skew X Y) : X ∩ Y ⊆ M.cl ∅ :=
  (skew_iff_modularPair_inter_subset_loops.1 h).2

lemma Skew.disjoint [Loopless M] (h : M.Skew X Y) : Disjoint X Y := by
  rw [disjoint_iff_inter_eq_empty, ← subset_empty_iff]
  simpa using h.inter_subset_loops

lemma Skew.symm (h : M.Skew X Y) : M.Skew Y X := by
  rw [skew_iff_modularPair_inter_subset_loops] at h ⊢
  rwa [inter_comm, ModularPair.comm]

lemma Skew.comm : M.Skew X Y ↔ M.Skew Y X :=
  ⟨Skew.symm, Skew.symm⟩

lemma skew_iff_exist_bases {X Y : Set α} :
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

lemma Skew.disjoint_of_indep_subset_left (h : M.Skew X Y) (hI : M.Indep I) (hIX : I ⊆ X) :
    Disjoint I Y :=
  SkewFamily.disjoint_of_indep_subset (i := true) (j := false) h hI hIX (by simp)

lemma Skew.disjoint_of_indep_subset_right (h : M.Skew X Y) (hJ : M.Indep J) (hJY : J ⊆ Y) :
    Disjoint X J :=
  (SkewFamily.disjoint_of_indep_subset (j := true) (i := false) h hJ hJY (by simp)).symm

lemma Skew.disjoint_of_basis_of_subset (h : M.Skew X Y) (hI : M.Basis I X) (hJ : J ⊆ Y) :
    Disjoint I J :=
  (h.disjoint_of_indep_subset_left hI.indep hI.subset).mono_right hJ

lemma Skew.diff_loops_disjoint_left (h : M.Skew X Y) : Disjoint (X \ M.cl ∅) Y := by
  rw [disjoint_iff_inter_eq_empty, ← inter_diff_right_comm, diff_eq_empty]
  exact h.inter_subset_loops

lemma Skew.mono (h : M.Skew X Y) (hX : X' ⊆ X) (hY : Y' ⊆ Y) : M.Skew X' Y' :=
  SkewFamily.mono h (Ys := fun i ↦ bif i then X' else Y') (Bool.rec (by simpa) (by simpa))

lemma Skew.mono_left (h : M.Skew X Y) (hX : X' ⊆ X) : M.Skew X' Y :=
  h.mono hX Subset.rfl

lemma Skew.mono_right (h : M.Skew X Y) (hY : Y' ⊆ Y) : M.Skew X Y' :=
  h.mono Subset.rfl hY

lemma Skew.cl_skew (h : M.Skew X Y) : M.Skew (M.cl X) (M.cl Y) := by
  have h' := SkewFamily.cls_skewFamily h
  simp_rw [Bool.cond_eq_ite, apply_ite, ← Bool.cond_eq_ite] at h'
  exact h'

lemma skew_iff_cl_skew (hX : X ⊆ M.E := by aesop_mat) (hY : Y ⊆ M.E := by aesop_mat) :
    M.Skew X Y ↔ M.Skew (M.cl X) (M.cl Y) :=
  ⟨Skew.cl_skew, fun h ↦ h.mono (M.subset_cl X) (M.subset_cl Y)⟩

lemma skew_iff_of_loopEquiv (hX : M.LoopEquiv X X') (hY : M.LoopEquiv Y Y') :
    M.Skew X Y ↔ M.Skew X' Y' := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rwa [skew_iff_cl_skew hX.subset_ground hY.subset_ground, ← hX.cl_eq_cl, ← hY.cl_eq_cl,
      ← skew_iff_cl_skew]
  rwa [skew_iff_cl_skew hX.symm.subset_ground hY.symm.subset_ground, hX.cl_eq_cl, hY.cl_eq_cl,
      ← skew_iff_cl_skew]

lemma skew_iff_diff_loops_skew : M.Skew X Y ↔ M.Skew (X \ M.cl ∅) (Y \ M.cl ∅) :=
  skew_iff_of_loopEquiv (M.loopEquiv_diff_loops X) (M.loopEquiv_diff_loops Y)

lemma skew_iff_diff_loops_skew_left : M.Skew X Y ↔ M.Skew (X \ M.cl ∅) Y :=
  skew_iff_of_loopEquiv (M.loopEquiv_diff_loops X) rfl

lemma skew_iff_bases_skew (hI : M.Basis I X) (hJ : M.Basis J Y) : M.Skew I J ↔ M.Skew X Y :=
  ⟨fun h ↦ h.cl_skew.mono hI.subset_cl hJ.subset_cl, fun h ↦ h.mono hI.subset hJ.subset⟩

lemma Skew.union_indep_of_indep_subsets (h : M.Skew X Y) (hI : M.Indep I) (hIX : I ⊆ X)
    (hJ : M.Indep J) (hJY : J ⊆ Y) : M.Indep (I ∪ J) := by
  rw [union_eq_iUnion]
  exact SkewFamily.iUnion_indep_subset_indep h (Is := fun i ↦ bif i then I else J)
    (Bool.rec (by simpa) (by simpa)) (Bool.rec (by simpa) (by simpa))

lemma Skew.union_basis_union (h : M.Skew X Y) (hI : M.Basis I X) (hJ : M.Basis J Y) :
    M.Basis (I ∪ J) (X ∪ Y) := by
  rw [union_eq_iUnion, union_eq_iUnion]
  exact SkewFamily.iUnion_basis_iUnion h (Bool.rec (by simpa) (by simpa))

lemma Indep.skew_iff_disjoint (h : M.Indep (I ∪ J)) : M.Skew I J ↔ Disjoint I J := by
  rw [union_eq_iUnion] at h
  convert h.skewFamily_iff_pairwiseDisjoint
  convert pairwise_disjoint_on_bool.symm
  simp [PairwiseDisjoint, Set.Pairwise, Pairwise]

lemma skew_iff_contract_restrict_eq_restrict (hX : X ⊆ M.E := by aesop_mat)
    (hY : Y ⊆ M.E := by aesop_mat) : M.Skew X Y ↔ (M ／ X) ↾ Y = M ↾ Y := by
  obtain ⟨I, hI⟩ := M.exists_basis X
  refine ⟨fun h ↦ ?_, fun h ↦ skew_iff_exist_bases.2 ?_⟩
  · refine eq_of_indep_iff_indep_forall rfl fun J (hJ : J ⊆ Y) ↦ ?_
    simp_rw [restrict_indep_iff, hI.contract_indep_iff, and_iff_left hJ]
    refine ⟨fun h ↦ h.1.subset (subset_union_left _ _),
      fun hJi ↦ ⟨?_, h.disjoint_of_indep_subset_right hJi hJ⟩⟩
    exact h.symm.union_indep_of_indep_subsets hJi hJ hI.indep hI.subset
  obtain ⟨J, hJ⟩ := M.exists_basis Y
  have hi : (M ↾ Y).Indep J := by
    exact restrict_indep_iff.2 ⟨hJ.indep, hJ.subset⟩
  refine ⟨I, J, ?_, ?_, hI, hJ⟩
  · rw [← h, restrict_indep_iff, hI.contract_eq_contract_delete, delete_indep_iff,
      hI.indep.contract_indep_iff, union_comm] at hi
    exact hi.1.1.2
  rw [← h, restrict_indep_iff, hI.contract_indep_iff] at hi
  exact hi.1.2.mono_left hI.subset

lemma SkewFamily.skew_compl (h : M.SkewFamily Xs) (A : Set ι) :
    M.Skew (⋃ i ∈ A, Xs i) (⋃ i ∈ Aᶜ, Xs i) := by
  rw [skew_iff_modularPair_inter_subset_loops]
  refine ⟨h.modularFamily.modularPair_compl_biUnion A, ?_⟩
  rintro e ⟨⟨_,⟨i,hi,rfl⟩,hi'⟩ ,⟨_,⟨j,hj,rfl⟩,hj'⟩⟩
  simp only [mem_iUnion, exists_prop] at hi' hj'
  exact h.loop_of_mem_inter (show i ≠ j from fun hij ↦ hj'.1 <| hij ▸ hi'.1) ⟨hi'.2, hj'.2⟩

lemma SkewFamily.skew_compl_singleton (h : M.SkewFamily Xs) (i : ι) :
    M.Skew (Xs i) (⋃ j ∈ ({i} : Set ι)ᶜ, Xs j) := by
  convert h.skew_compl {i}; simp

end Skew

-- section Flat

-- variable {F₁ F₂ : Set α}

-- lemma foo (hF₁ : M.Flat F₁) (hF₂ : M.Flat F₂) : M.ModularPair F₁ F₂ ↔
--     IsModularLattice ↑(Icc (hF₁.toFlats ⊓ hF₂.toFlats) (hF₁.toFlats ⊔ hF₂.toFlats)) := by
--   refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
--   · constructor
--     ·

-- end Flat

end Matroid
