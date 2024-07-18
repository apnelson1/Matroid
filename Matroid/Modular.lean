import Matroid.Flat
import Matroid.Simple
import Matroid.ForMathlib.Card
import Mathlib.Order.ModularLattice

open Set BigOperators Set.Notation

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

lemma ModularBase.subset_closure_inter (h : M.ModularBase B Xs) (i : ι) :
    Xs i ⊆ M.closure ((Xs i) ∩ B) :=
  (h.basis_inter i).subset_closure

lemma ModularBase.closure_inter_eq (h : M.ModularBase B Xs) (i : ι) :
    M.closure (Xs i ∩ B) = M.closure (Xs i) :=
  (h.basis_inter i).closure_eq_closure.symm

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
  simp_rw [h.1.indep.inter_basis_closure_iff_subset_closure_inter, iUnion_subset_iff]
  exact fun i ↦ (h.subset_closure_inter i).trans
    (M.closure_subset_closure (inter_subset_inter_left _ (subset_iUnion _ i)))

lemma ModularBase.basis_biUnion (h : M.ModularBase B Xs) (A : Set ι) :
    M.Basis ((⋃ i ∈ A, Xs i) ∩ B) (⋃ i ∈ A, Xs i) := by
  convert (h.subtype A).basis_iUnion <;> simp

lemma exists_modularBase_of_iUnion_indep (h : M.Indep (⋃ i, Xs i)) :
    ∃ B, M.ModularBase B Xs := by
  obtain ⟨B, hB, hIB⟩ := h.exists_base_superset
  refine ⟨B, hB, fun i ↦ ?_⟩
  rw [inter_eq_self_of_subset_left <| iUnion_subset_iff.1 hIB i]
  exact (h.subset (subset_iUnion _ i)).basis_self

lemma Base.modularBase_of_forall_subset_closure (hB : M.Base B)
    (h : ∀ i, Xs i ⊆ M.closure ((Xs i) ∩ B)) : M.ModularBase B Xs := by
  exact ⟨hB, fun i ↦ hB.indep.inter_basis_closure_iff_subset_closure_inter.2 (h i)⟩

lemma ModularBase.modularBase_of_forall_subset_subset_closure (hB : M.ModularBase B Xs)
    (hXY : ∀ i, Xs i ⊆ Ys i) (hYX : ∀ i, Ys i ⊆ M.closure (Xs i)) : M.ModularBase B Ys := by
  refine ⟨hB.base, fun i ↦ hB.indep.inter_basis_closure_iff_subset_closure_inter.2 ?_⟩
  refine (hYX i).trans (M.closure_subset_closure_of_subset_closure ?_)
  exact (hB.2 i).subset_closure.trans (M.closure_subset_closure (inter_subset_inter_left B (hXY i)))

lemma ModularBase.modularBase_closures (hB : M.ModularBase B Xs) :
    M.ModularBase B (fun i ↦ M.closure (Xs i)) :=
  hB.modularBase_of_forall_subset_subset_closure
    (fun i ↦ M.subset_closure (Xs i)) (fun _ ↦ Subset.rfl)

lemma ModularBase.iInter_closure_eq_closure_iInter [Nonempty ι] (hB : M.ModularBase B Xs) :
    (⋂ i : ι, M.closure (Xs i)) = M.closure (⋂ i : ι, Xs i) := by
  simp_rw [subset_antisymm_iff, subset_iInter_iff, ← hB.closure_inter_eq]
  rw [← closure_iInter_eq_iInter_closure_of_iUnion_indep, ← iInter_inter B Xs]
  · refine ⟨M.closure_subset_closure inter_subset_left, fun i ↦ ?_⟩
    rw [hB.closure_inter_eq]
    exact M.closure_subset_closure (iInter_subset _ i)
  exact hB.base.indep.subset (iUnion_subset (fun _ ↦ inter_subset_right))

end ModularBase
section ModularFamily

/-- A set family is a `ModularFamily` if it has a modular base. -/
def ModularFamily (M : Matroid α) (Xs : ι → Set α) := ∃ B, M.ModularBase B Xs

lemma Indep.modularFamily (hI : M.Indep I) (hXs : ∀ i, M.Basis ((Xs i) ∩ I) (Xs i)) :
    M.ModularFamily Xs := by
  simp_rw [hI.inter_basis_closure_iff_subset_closure_inter] at hXs
  obtain ⟨B, hB, hIB⟩ := hI.exists_base_superset
  refine ⟨B, hB, ?_⟩
  simp_rw [hB.indep.inter_basis_closure_iff_subset_closure_inter]
  exact fun i ↦ (hXs i).trans (M.closure_subset_closure (inter_subset_inter_right _ hIB))

lemma ModularFamily.subset_ground_of_mem (h : M.ModularFamily Xs) (i : ι) : Xs i ⊆ M.E :=
  let ⟨_, h⟩ := h
  h.subset_ground i

lemma ModularFamily.iInter_closure_eq_closure_iInter [Nonempty ι] (hXs : M.ModularFamily Xs) :
    (⋂ i : ι, M.closure (Xs i)) = M.closure (⋂ i : ι, Xs i) :=
  let ⟨_, h⟩ := hXs
  h.iInter_closure_eq_closure_iInter

lemma Indep.modularFamily_of_subsets (hI : M.Indep I) (hJs : ⋃ i, Js i ⊆ I) :
    M.ModularFamily Js := by
  refine hI.modularFamily (fun i ↦ ?_)
  have hJI : Js i ⊆ I := (subset_iUnion _ i).trans hJs
  rw [inter_eq_self_of_subset_left hJI]
  exact (hI.subset hJI).basis_self

lemma ModularFamily.modularFamily_of_forall_subset_closure (h : M.ModularFamily Xs)
    (hXY : ∀ i, Xs i ⊆ Ys i) (hYX : ∀ i, Ys i ⊆ M.closure (Xs i)) : M.ModularFamily Ys :=
  let ⟨B, hB⟩ := h
  ⟨B, hB.modularBase_of_forall_subset_subset_closure hXY hYX⟩

lemma ModularFamily.closures_modularFamily (h : M.ModularFamily Xs) :
    M.ModularFamily (fun i ↦ M.closure (Xs i)) :=
  let ⟨B, hB⟩ := h
  ⟨B, hB.modularBase_closures⟩

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

lemma ModularFamily.map {β : Type*} (f : α → β) (hf : InjOn f M.E) (h : M.ModularFamily Xs) :
    (M.map f hf).ModularFamily (fun i ↦ f '' (Xs i)) := by
  obtain ⟨B, hB, hBX⟩ := h
  refine ⟨f '' B, hB.map hf, fun i ↦ ?_⟩
  convert (hBX i).map hf
  rw [hf.image_inter (hBX i).subset_ground hB.subset_ground]

lemma modularFamily_map_iff {β : Type*} (f : α → β) (hf : InjOn f M.E) {Xs : ι → Set β} :
    (M.map f hf).ModularFamily Xs ↔ ∃ Ys, M.ModularFamily Ys ∧ ∀ i, Xs i = f '' (Ys i) := by
  refine ⟨fun h ↦ ?_, fun ⟨Ys, hYs, h_eq⟩ ↦ ?_⟩
  · obtain ⟨B, hB, h⟩ := h
    simp_rw [map_basis_iff'] at h
    rw [map_base_iff] at hB
    obtain ⟨B, hB, rfl⟩ := hB
    choose Is hIs using h
    choose Ys hYs using hIs
    refine ⟨Ys, ⟨B, hB, fun i ↦ ?_⟩, fun i ↦ (hYs i).2.2⟩
    convert (hYs i).1
    rw [← hf.image_eq_image_iff (inter_subset_right.trans hB.subset_ground)
      (hYs i).1.indep.subset_ground, ← (hYs i).2.1, (hYs i).2.2, hf.image_inter]
    · exact (hYs i).1.subset_ground
    exact hB.subset_ground

  convert hYs.map f hf with i
  apply h_eq

lemma ModularFamily.mapEmbedding {β : Type*} (f : α ↪ β) (h : M.ModularFamily Xs) :
    (M.mapEmbedding f).ModularFamily (fun i ↦ f '' (Xs i)) := by
  obtain ⟨B, hB, hBX⟩ := h
  refine ⟨f '' B, hB.mapEmbedding f, fun i ↦ ?_⟩
  convert (hBX i).mapEmbedding f
  rw [image_inter f.injective]

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
    inter_subset_left, ← hIY.eq_of_subset_indep (hB.indep.inter_left Y)
    (inter_subset_inter_right _ hIB) inter_subset_left]
  exact ⟨hIY,hIX⟩

lemma ModularFamily.modularPair (h : M.ModularFamily Xs) (i j : ι) :
    M.ModularPair (Xs i) (Xs j) := by
  obtain ⟨B, hB⟩ := h
  exact modularPair_iff.2 ⟨B, hB.indep, hB.basis_inter i, hB.basis_inter j⟩

lemma modularPair_iff_exists_subsets_closure_inter :
    M.ModularPair X Y ↔ ∃ I, M.Indep I ∧ X ⊆ M.closure (X ∩ I) ∧ Y ⊆ M.closure (Y ∩ I)  := by
  rw [modularPair_iff]
  refine ⟨fun ⟨I,hI,h⟩ ↦ ⟨I,hI,?_⟩, fun ⟨I,hI,h⟩ ↦ ⟨I,hI,?_⟩⟩
  · rwa [← hI.inter_basis_closure_iff_subset_closure_inter,
      ← hI.inter_basis_closure_iff_subset_closure_inter]
  rwa [hI.inter_basis_closure_iff_subset_closure_inter,
    hI.inter_basis_closure_iff_subset_closure_inter]

lemma ModularPair.exists_subsets_closure_inter (h : M.ModularPair X Y) :
    ∃ I, M.Indep I ∧ X ⊆ M.closure (X ∩ I) ∧ Y ⊆ M.closure (Y ∩ I) :=
  modularPair_iff_exists_subsets_closure_inter.1 h

lemma modularPair_iff_exists_basis_basis :
    M.ModularPair X Y ↔ ∃ I J, M.Basis I X ∧ M.Basis J Y ∧ M.Indep (I ∪ J) := by
  rw [modularPair_iff]
  refine ⟨fun ⟨I,hI,hIX,hIY⟩ ↦ ⟨_, _, hIX, hIY, hI.subset (by simp)⟩,
    fun ⟨I,J,hI,hJ,hi⟩ ↦ ⟨_,hi, ?_⟩⟩
  simp_rw [hi.inter_basis_closure_iff_subset_closure_inter]
  use hI.subset_closure.trans (M.closure_subset_closure (subset_inter hI.subset subset_union_left))
  exact hJ.subset_closure.trans
    (M.closure_subset_closure (subset_inter hJ.subset subset_union_right))

lemma ModularPair.exists_common_basis (h : M.ModularPair X Y) : ∃ I,
    M.Basis I (X ∪ Y) ∧ M.Basis (I ∩ X) X ∧ M.Basis (I ∩ Y) Y ∧ M.Basis (I ∩ X ∩ Y) (X ∩ Y) := by
  obtain ⟨B, hB⟩ := h
  refine ⟨(X ∪ Y) ∩ B, ?_⟩
  rw [inter_right_comm, inter_eq_self_of_subset_right subset_union_left,
    inter_right_comm, inter_eq_self_of_subset_right subset_union_right, inter_right_comm]
  refine ⟨?_, by simpa using hB.basis_inter true, by simpa using hB.basis_inter false, ?_⟩
  · have hu := hB.basis_iUnion
    rwa [← union_eq_iUnion] at hu
  have hi := hB.basis_iInter
  rwa [← inter_eq_iInter] at hi

lemma ModularPair.inter_closure_eq (h : M.ModularPair X Y) :
    M.closure (X ∩ Y) = M.closure X ∩ M.closure Y := by
  convert (ModularFamily.iInter_closure_eq_closure_iInter h).symm
  · rw [inter_eq_iInter]
  simp_rw [Bool.cond_eq_ite, apply_ite, ← Bool.cond_eq_ite, inter_eq_iInter]

lemma modularPair_of_subset (hXY : X ⊆ Y) (hY : Y ⊆ M.E) : M.ModularPair X Y := by
  obtain ⟨I,J, hI, hJ, hIJ⟩ := M.exists_basis_subset_basis hXY
  refine modularPair_iff.2 ⟨J, hJ.indep, ?_, by rwa [inter_eq_self_of_subset_right hJ.subset]⟩
  rwa [← hI.eq_of_subset_indep (hJ.indep.inter_left X) (subset_inter hI.subset hIJ)
    inter_subset_left]

lemma Indep.modularPair_of_union (hi : M.Indep (I ∪ J)) : M.ModularPair I J := by
  simpa only [iUnion_subset_iff, Bool.forall_bool, cond_false, subset_union_right, cond_true,
    subset_union_left, and_self, forall_true_left] using
    hi.modularFamily_of_subsets (Js := fun i ↦ bif i then I else J)

lemma ModularPair.of_subset_closure_subset_closure (h : M.ModularPair X Y) (hXX' : X ⊆ X')
    (hX' : X' ⊆ M.closure X) (hYY' : Y ⊆ Y') (hY' : Y' ⊆ M.closure Y) : M.ModularPair X' Y' := by
  apply ModularFamily.modularFamily_of_forall_subset_closure h
  · simp [hYY', hXX']
  simp [hY', hX']

lemma ModularPair.of_subset_closure_left (h : M.ModularPair X Y) (hXX' : X ⊆ X')
    (hX' : X' ⊆ M.closure X) : M.ModularPair X' Y :=
  h.of_subset_closure_subset_closure hXX' hX' Subset.rfl (M.subset_closure Y)

lemma ModularPair.of_subset_closure_right (h : M.ModularPair X Y) (hYY' : Y ⊆ Y')
    (hY' : Y' ⊆ M.closure Y) : M.ModularPair X Y' :=
  (h.symm.of_subset_closure_left hYY' hY').symm

lemma ModularPair.of_basis_left (h : M.ModularPair I Y) (hIX : M.Basis I X) :
    M.ModularPair X Y :=
  h.of_subset_closure_left hIX.subset hIX.subset_closure

lemma ModularPair.of_basis_right (h : M.ModularPair X J) (hJY : M.Basis J Y) :
    M.ModularPair X Y :=
  h.of_subset_closure_right hJY.subset hJY.subset_closure

lemma ModularPair.of_basis_of_basis (h : M.ModularPair I J) (hIX : M.Basis I X)
    (hJY : M.Basis J Y) : M.ModularPair X Y :=
  (h.of_basis_left hIX).of_basis_right hJY

lemma ModularPair.closure_left (h : M.ModularPair X Y) : M.ModularPair (M.closure X) Y :=
  h.of_subset_closure_left (M.subset_closure X) Subset.rfl

lemma ModularPair.closure_right (h : M.ModularPair X Y) : M.ModularPair X (M.closure Y) :=
  h.symm.closure_left.symm

lemma ModularPair.closure_closure (h : M.ModularPair X Y) :
    M.ModularPair (M.closure X) (M.closure Y) :=
  h.closure_left.closure_right

lemma modularPair_singleton (he : e ∈ M.E) (hX : X ⊆ M.E) (heX : e ∉ M.closure X) :
    M.ModularPair {e} X := by
  obtain ⟨I, hI⟩ := M.exists_basis X
  have hi : M.Indep (insert e I) := by
    rw [hI.indep.insert_indep_iff, ← hI.closure_eq_closure]
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

lemma FinRank.modularPair_iff (hXfin : M.FinRank X) (hYfin : M.FinRank Y)
    (hXE : X ⊆ M.E := by aesop_mat) (hYE : Y ⊆ M.E := by aesop_mat) :
    M.ModularPair X Y ↔ M.er X + M.er Y = M.er (X ∩ Y) + M.er (X ∪ Y) := by
  refine ⟨fun h ↦ h.er_add_er, fun hr ↦ modularPair_iff_exists_basis_basis.2 ?_ ⟩
  obtain ⟨Ii, hIi⟩ := M.exists_basis (X ∩ Y)
  have hifin : Ii.encard ≠ ⊤ := by
    simpa using (hXfin.inter_right Y).finite_of_basis hIi
  obtain ⟨IX, hIX, hX⟩ := hIi.indep.subset_basis_of_subset
    (hIi.subset.trans inter_subset_left)
  obtain ⟨IY, hIY, hY⟩ := hIi.indep.subset_basis_of_subset
    (hIi.subset.trans inter_subset_right)
  refine ⟨IX, IY, hIX, hIY, ?_⟩
  rw [hIi.er_eq_encard, hIX.er_eq_encard, ← encard_diff_add_encard_of_subset hX,
    add_comm (encard _), add_assoc, WithTop.add_left_cancel_iff hifin, hIY.er_eq_encard,
    ← encard_union_add_encard_inter, ← union_eq_self_of_subset_left hY, ← union_assoc,
    diff_union_self, union_eq_self_of_subset_right hX] at hr
  refine Basis.indep <| (hXfin.union hYfin).basis_of_subset_of_subset_closure_of_encard_le
    (union_subset_union hIX.subset hIY.subset) ?_ (le_of_add_le_left hr.le) (by aesop_mat)
  rw [← M.closure_union_closure_left_eq, ← M.closure_union_closure_right_eq]
  exact (M.subset_closure _).trans
    (M.closure_subset_closure (union_subset_union hIX.subset_closure hIY.subset_closure))

lemma modularPair_iff_r [FiniteRk M] (hXE : X ⊆ M.E := by aesop_mat)
    (hYE : Y ⊆ M.E := by aesop_mat) :
    M.ModularPair X Y ↔ M.r X + M.r Y = M.r (X ∩ Y) + M.r (X ∪ Y) := by
  simp_rw [(M.to_finRank X).modularPair_iff (M.to_finRank Y), ← coe_r_eq, ← Nat.cast_add,
    Nat.cast_inj]

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

lemma modularPair_insert_insert (M : Matroid α) {X : Set α} {e f : α}
    (he : e ∉ M.closure (insert f X))  (hX : X ⊆ M.E := by aesop_mat)
    (heE : e ∈ M.E := by aesop_mat) (hfE : f ∈ M.E := by aesop_mat) :
    M.ModularPair (insert e X) (insert f X) := by
  obtain ⟨I, hI⟩ := M.exists_basis X

  have heb : M.Basis (insert e I) (insert e X) := by
    refine hI.insert_basis_insert ?_
    rw [hI.indep.insert_indep_iff, mem_diff, ← hI.closure_eq_closure, and_iff_right heE]
    exact .inl (not_mem_subset (M.closure_subset_closure <| subset_insert ..) he)

  by_cases hf : f ∈ M.closure (insert e X)
  · have hmod : M.ModularPair (insert e I) I := ModularPair.symm <| modularPair_of_subset
      (subset_insert _ _) (insert_subset heE hI.indep.subset_ground)
    refine hmod.of_subset_closure_subset_closure (insert_subset_insert hI.subset)
      heb.subset_closure (hI.subset.trans (subset_insert _ _)) (insert_subset ?_ hI.subset_closure)
    rw [← hI.closure_eq_closure]
    contrapose! he
    exact mem_closure_insert he hf

  have hfb : M.Basis (insert f I) (insert f X) := by
    refine hI.insert_basis_insert ?_
    rw [hI.indep.insert_indep_iff, mem_diff, ← hI.closure_eq_closure, and_iff_right hfE]
    exact .inl (not_mem_subset (M.closure_subset_closure <| subset_insert ..) hf)

  have hmod : M.ModularPair (insert e I) (insert f I) := by
    refine Indep.modularPair_of_union ?_
    rw [← singleton_union, union_assoc, union_eq_self_of_subset_left (subset_insert _ _),
      singleton_union, hfb.indep.insert_indep_iff, ← hfb.closure_eq_closure]
    exact .inl ⟨heE, he⟩

  exact hmod.of_subset_closure_subset_closure (insert_subset_insert hI.subset)
    heb.subset_closure (insert_subset_insert hI.subset) hfb.subset_closure

lemma modularPair_insert_closure (M : Matroid α) (X : Set α) (e f : α)
    (hX : X ⊆ M.E := by aesop_mat) (he : e ∈ M.E := by aesop_mat) (hf : f ∈ M.E := by aesop_mat) :
    M.ModularPair (M.closure (insert e X)) (M.closure (insert f X)) := by

  by_cases he' : e ∈ M.closure (insert f X)
  · exact modularPair_of_subset
      (M.closure_subset_closure_of_subset_closure
        (insert_subset he' (M.subset_closure_of_subset (subset_insert _ _))))
      (M.closure_subset_ground _ (insert_subset hf hX))

  exact (M.modularPair_insert_insert he').closure_closure




end ModularFamily

section ModularSet

/-- A `ModularSet` is a set that is a modular pair with every flat. -/
def ModularSet (M : Matroid α) (X : Set α) := ∀ ⦃F⦄, M.Flat F → M.ModularPair X F

@[simp] lemma modularSet_def {M : Matroid α} {X : Set α} :
    M.ModularSet X ↔ ∀ ⦃F⦄, M.Flat F → M.ModularPair X F := Iff.rfl

@[aesop unsafe 5% (rule_sets := [Matroid])]
lemma ModularSet.subset_ground (h : M.ModularSet X) : X ⊆ M.E :=
  (h (M.closure_flat ∅)).subset_ground_left

@[simp] lemma modularSet_iff {M : Matroid α} {X : Set α} :
    M.ModularSet X ↔ ∀ ⦃F⦄, M.Flat F → ∃ I, M.Indep I ∧ M.Basis (X ∩ I) X ∧ M.Basis (F ∩ I) F := by
  simp [ModularSet, modularPair_iff]

lemma modularSet_iff_closure {M : Matroid α} {X : Set α} :
    M.ModularSet X ↔ ∀ ⦃F⦄, M.Flat F → ∃ I, M.Indep I ∧ X ⊆ M.closure (X ∩ I) ∧ F ⊆ M.closure (F ∩ I) := by
  rw [modularSet_iff]
  refine ⟨fun h F hF ↦ ?_, fun h F hF ↦ ?_⟩
  · obtain ⟨I, hI, hI'⟩ := h hF
    refine ⟨I, hI, ?_⟩
    rwa [← hI.inter_basis_closure_iff_subset_closure_inter, ← hI.inter_basis_closure_iff_subset_closure_inter]
  obtain ⟨I, hI, hI'⟩ := h hF
  refine ⟨I, hI, ?_⟩
  rwa [hI.inter_basis_closure_iff_subset_closure_inter, hI.inter_basis_closure_iff_subset_closure_inter]

lemma modularSet_ground (M : Matroid α) : M.ModularSet M.E :=
  modularSet_def.2 (fun _ hF ↦ (modularPair_of_subset hF.subset_ground Subset.rfl).symm)

lemma modularSet_empty (M : Matroid α) : M.ModularSet ∅ :=
  modularSet_def.2 (fun _ hF ↦ (modularPair_of_subset (empty_subset _) hF.subset_ground))

lemma modularSet.closure (h : M.ModularSet X) : M.ModularSet (M.closure X) :=
  fun _ hF ↦ (h hF).closure_left

lemma modularSet_singleton (M : Matroid α) (he : e ∈ M.E) : M.ModularSet {e} := by
  refine modularSet_def.2 fun F hF ↦ ?_
  by_cases heF : {e} ⊆ F
  · apply modularPair_of_subset heF hF.subset_ground
  rw [singleton_subset_iff, ← hF.closure] at heF
  exact modularPair_singleton he hF.subset_ground heF

/-- Every modular set in a simple matroid is a flat. -/
lemma ModularSet.Flat [Simple M] (hF : M.ModularSet F) : M.Flat F := by
  by_contra h
  obtain ⟨e, heE, heF, he⟩ := exists_mem_closure_not_mem_of_not_flat h
  rw [modularSet_iff] at hF
  obtain ⟨I, hI, hIF, hIe⟩ := hF (M.closure_flat {e})
  have heM := M.closure_subset_ground F hIF.subset_ground heF
  have heI : e ∈ I := by
    rw [hI.inter_basis_closure_iff_subset_closure_inter, closure_singleton_eq,
      closure_eq_self_of_subset_singleton heM inter_subset_left] at hIe
    simpa using hIe
  apply hI.not_mem_closure_diff_of_mem heI
  apply mem_of_mem_of_subset <| M.closure_subset_closure_of_subset_closure hIF.subset_closure heF
  apply M.closure_subset_closure
  rw [subset_diff, and_iff_right inter_subset_right, disjoint_singleton_right]
  exact fun he' ↦ he <| inter_subset_left he'

end ModularSet

section Skew

/-- A `SkewFamily` is a collection of sets having pairwise disjoint bases whose union is
  independent. -/
def SkewFamily (M : Matroid α) (Xs : ι → Set α) :=
  M.ModularFamily Xs ∧ ∀ ⦃i j⦄, i ≠ j → Xs i ∩ Xs j ⊆ M.closure ∅

lemma SkewFamily.modularFamily (h : M.SkewFamily Xs) : M.ModularFamily Xs :=
  h.1

@[aesop unsafe 5% (rule_sets := [Matroid])]
lemma SkewFamily.subset_ground_of_mem (h : M.SkewFamily Xs) (i : ι) : Xs i ⊆ M.E :=
  h.modularFamily.subset_ground_of_mem i

lemma SkewFamily.loop_of_mem_inter (h : M.SkewFamily Xs) (hij : i ≠ j)
    (he : e ∈ Xs i ∩ Xs j) : M.Loop e :=
  h.2 hij he

lemma SkewFamily.subset_loops_of_ne (h : M.SkewFamily Xs) (hij : i ≠ j) : Xs i ∩ Xs j ⊆ M.closure ∅ :=
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

lemma SkewFamily.pairwise_disjoint_inter_of_indep (h : M.SkewFamily Xs) (hI : M.Indep I) :
    Pairwise (Disjoint on fun i ↦ Xs i ∩ I) :=
  fun _ _ hij ↦ (h.disjoint_inter_indep hI hij).mono_right inter_subset_left

lemma SkewFamily.pairwise_disjoint_of_indep_subsets (h : M.SkewFamily Xs) (hIX : ∀ i, Is i ⊆ Xs i)
    (hIs : ∀ i, M.Indep (Is i)) : Pairwise (Disjoint on Is) :=
  fun i j hij ↦ disjoint_iff_inter_eq_empty.2 <|
    ((hIs i).inter_right (Is j)).eq_empty_of_subset_loops
    ((inter_subset_inter (hIX i) (hIX j)).trans (h.2 hij).subset)

lemma SkewFamily.pairwise_disjoint_of_bases (h : M.SkewFamily Xs)
    (hIX : ∀ i, M.Basis (Is i) (Xs i)) : Pairwise (Disjoint on Is) :=
  h.pairwise_disjoint_of_indep_subsets (fun i ↦ (hIX i).subset) (fun i ↦ (hIX i).indep)

lemma SkewFamily.closures_skewFamily (h : M.SkewFamily Xs) : M.SkewFamily (fun i ↦ M.closure (Xs i)) := by
  refine ⟨h.modularFamily.closures_modularFamily, fun i j hij ↦ ?_⟩
  have := M.closure_subset_closure_of_subset_closure <| h.subset_loops_of_ne hij
  rwa [← (h.modularFamily.modularPair i j).inter_closure_eq]

lemma Indep.skewFamily_of_disjoint_bases (hI : M.Indep (⋃ i, Is i))
    (hdj : Pairwise (Disjoint on Is)) (hIs : ∀ i, M.Basis (Is i) (Xs i)) : M.SkewFamily Xs := by
  refine ⟨hI.modularFamily fun i ↦ ?_, fun i j hij ↦ ?_⟩
  · rw [hI.inter_basis_closure_iff_subset_closure_inter]
    exact (hIs i).subset_closure.trans (M.closure_subset_closure (subset_inter (hIs i).subset (subset_iUnion _ i)))
  refine (inter_subset_inter (M.subset_closure _) (M.subset_closure _)).trans ?_
  rw [(hIs i).closure_eq_closure, (hIs j).closure_eq_closure,
    ← (hI.subset _).closure_inter_eq_inter_closure, Disjoint.inter_eq <| hdj hij]
  exact union_subset (subset_iUnion _ _) (subset_iUnion _ _)

lemma skewFamily_iff_exist_bases : M.SkewFamily Xs ↔
    ∃ (Is : ι → Set α), Pairwise (Disjoint on Is) ∧ M.Basis (⋃ i : ι, Is i) (⋃ i : ι, Xs i) ∧
      ∀ i, M.Basis (Is i) (Xs i) := by
  refine ⟨fun h ↦ ?_, fun ⟨Is, hdj, hIs, hb⟩ ↦ hIs.indep.skewFamily_of_disjoint_bases hdj hb⟩
  obtain ⟨B, hB⟩ := h.modularFamily
  refine ⟨_, ?_, ?_, hB.basis_inter⟩
  · exact h.pairwise_disjoint_of_indep_subsets (fun i ↦ inter_subset_left)
      (fun i ↦ hB.indep.inter_left _)
  rw [← iUnion_inter]
  exact hB.basis_iUnion

lemma Indep.skewFamily_iff_pairwise_disjoint (hI : M.Indep (⋃ i : ι, Is i)) :
    M.SkewFamily Is ↔ Pairwise (Disjoint on Is) := by
  refine ⟨fun h ↦ h.pairwise_disjoint_of_indep_subsets
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

  obtain ⟨K', hK', hss⟩ := (hJs i₀).1.indep.subset_basis_of_subset subset_union_left hssE

  have hK'' : ∀ i, i ≠ i₀ → Ks i ⊆ K' := by
    intro i hne f hf
    by_contra hfK'
    apply hKs.indep.not_mem_closure_diff_of_mem (mem_iUnion.2 ⟨i,hf⟩)
    have hcl : f ∈ M.closure K' := by
      exact hK'.subset_closure (Or.inr <| mem_biUnion hne hf)

    refine mem_of_mem_of_subset
      (M.closure_subset_closure (subset_diff_singleton hK'.subset hfK') hcl)
      (M.closure_subset_closure_of_subset_closure ?_)
    simp only [mem_compl_iff, mem_singleton_iff, mem_union, mem_iUnion, exists_prop, not_exists,
      diff_singleton_subset_iff, union_subset_iff, iUnion_subset_iff]
    refine ⟨(hJs i₀).1.subset.trans ?_, fun i _ ↦ ?_⟩
    · refine (huKs i₀).subset_closure.trans (subset_trans (M.closure_subset_closure ?_) (subset_insert _ _))
      refine subset_diff_singleton (subset_iUnion Ks i₀) (fun hf' ↦ ?_)
      exact (hdj hne).ne_of_mem hf hf' rfl

    refine subset_trans ?_ <| insert_subset_insert (M.subset_closure _)
    rw [insert_diff_singleton]
    exact (subset_iUnion Ks i).trans (subset_insert _ _)

  have he' : e ∈ M.closure (K' \ {e}) := by
    refine mem_of_mem_of_subset (hJ.subset_closure (mem_iUnion_of_mem _ hei₀)) ?_
    rw [closure_subset_closure_iff_subset_closure]
    rintro f hf
    obtain ⟨i, hfi⟩ := mem_iUnion.1 (hJ.subset hf)
    obtain (rfl | hi) := eq_or_ne i₀ i
    · apply M.subset_closure (K' \ {e})
      exact ⟨hss hfi, fun (h : f = e) ↦ heJ <| h ▸ hf⟩
    refine mem_of_mem_of_subset ((hJs i).1.subset.trans (huKs i).subset_closure hfi) (M.closure_subset_closure ?_)
    refine subset_diff_singleton (hK'' i hi.symm) (fun heK ↦ ?_)
    apply Loop.not_nonloop <| h.loop_of_mem_inter hi ⟨(hJs i₀).1.subset hei₀, (huKs i).subset heK⟩
    exact (hK'.indep.subset hss).nonloop_of_mem hei₀

  exact hK'.indep.not_mem_closure_diff_of_mem (hss hei₀) he'

lemma SkewFamily.mono (h : M.SkewFamily Xs) (hYX : ∀ i, Ys i ⊆ Xs i) : M.SkewFamily Ys := by
  choose Is hIs using fun i ↦ M.exists_basis (Ys i) ((hYX i).trans (h.subset_ground_of_mem i))
  refine Indep.skewFamily_of_disjoint_bases ?_ ?_ hIs
  · exact h.iUnion_indep_subset_indep (fun i ↦ (hIs i).subset.trans (hYX i)) (fun i ↦ (hIs i).indep)
  exact h.pairwise_disjoint_of_indep_subsets
    (fun i ↦ (hIs i).subset.trans (hYX i)) (fun i ↦ (hIs i).indep)

lemma SkewFamily.iUnion_basis_iUnion (h : M.SkewFamily Xs) (hIs : ∀ i, M.Basis (Is i) (Xs i)) :
    M.Basis (⋃ i, Is i) (⋃ i, Xs i) := by
  have hi := h.iUnion_indep_subset_indep (fun i ↦ (hIs i).subset) (fun i ↦ (hIs i).indep)
  exact hi.basis_of_subset_of_subset_closure (iUnion_mono (fun i ↦ (hIs i).subset)) <|
    iUnion_subset (fun i ↦ (hIs i).subset_closure.trans (M.closure_subset_closure (subset_iUnion _ _)))

lemma SkewFamily.sum_er_eq_er_iUnion [Fintype ι] (h : M.SkewFamily Xs) :
    ∑ i, M.er (Xs i) = M.er (⋃ i, Xs i) := by
  choose Is hIs using fun i ↦ M.exists_basis (Xs i) (h.subset_ground_of_mem i)
  have hdj := (h.pairwise_disjoint_of_bases hIs)
  rw [← pairwise_univ] at hdj
  rw [(h.iUnion_basis_iUnion hIs).er_eq_encard, encard_iUnion _ hdj]
  simp_rw [(hIs _).er_eq_encard]

lemma FinRank.skewFamily_iff_sum_er_eq_er_iUnion [Fintype ι] (hXs : ∀ i, M.FinRank (Xs i))
    (hXE : ∀ i, Xs i ⊆ M.E) : M.SkewFamily Xs ↔ ∑ i, M.er (Xs i) = M.er (⋃ i, Xs i) := by
  refine ⟨SkewFamily.sum_er_eq_er_iUnion, fun hsum ↦ ?_⟩
  choose Is hIs using fun i ↦ M.exists_basis (Xs i) (hXE i)
  rw [← er_closure_eq , ← M.closure_iUnion_closure_eq_closure_iUnion] at hsum
  simp_rw [← (fun i ↦ M.er_closure_eq (Xs i)), (fun i ↦ (hIs i).closure_eq_closure),
    M.closure_iUnion_closure_eq_closure_iUnion, er_closure_eq, (fun i ↦ (hIs i).indep.er)] at hsum

  apply Indep.skewFamily_of_disjoint_bases ?_ ?_ hIs
  · exact FinRank.indep_of_encard_le_er
      ((FinRank.iUnion hXs).subset (iUnion_mono (fun i ↦ (hIs i).subset)))
      ((encard_iUnion_le _).trans hsum.le)
  rw [← pairwise_univ]
  exact pairwiseDisjoint_of_encard_sum_le_encard_iUnion
    (fun i ↦ (hXs i).finite_of_basis (hIs i)) (hsum.le.trans <| M.er_le_encard _)

lemma skewFamily_iff_sum_er_eq_er_iUnion [Fintype ι] [FiniteRk M] (hXs : ∀ i, Xs i ⊆ M.E) :
     M.SkewFamily Xs ↔ ∑ i, M.r (Xs i) = M.r (⋃ i, Xs i) := by
  simp_rw [FinRank.skewFamily_iff_sum_er_eq_er_iUnion (fun i ↦ M.to_finRank (Xs i)) hXs,
    ← M.coe_r_eq, ← Nat.cast_sum, Nat.cast_inj]

lemma skewFamily_iff_forall_circuit (hXs : ∀ i, Xs i ⊆ M.E) (hdj : Pairwise (Disjoint on Xs)) :
    M.SkewFamily Xs ↔ ∀ C, M.Circuit C → C ⊆ ⋃ i, Xs i → ∃ i, C ⊆ Xs i := by
  refine ⟨fun h C hC hCU ↦ ?_, fun h ↦ ?_⟩
  · have h : ∃ i, ¬ M.Indep (C ∩ Xs i) := by
      by_contra! hcon
      refine hC.dep.not_indep ?_
      refine (h.iUnion_indep_subset_indep (fun i ↦ inter_subset_right) hcon).subset ?_
      simp [← inter_iUnion, hCU, Subset.rfl]
    obtain ⟨i, hi⟩ := h
    rw [← hC.eq_of_not_indep_subset hi inter_subset_left]
    exact ⟨i, inter_subset_right⟩
  choose Is hIs using fun i ↦ M.exists_basis _ (hXs i)
  have hss := iUnion_mono (fun i ↦ (hIs i).subset)
  have hIe : ⋃ i, Is i ⊆ M.E := by simp [fun i ↦ (hIs i).subset.trans (hXs i)]
  have h_inter : ∀ i, Xs i ∩ ⋃ j, Is j = Is i := by
    intro i
    simp only [inter_iUnion, subset_antisymm_iff, iUnion_subset_iff]
    refine ⟨fun j ↦ ?_, subset_iUnion_of_subset i (subset_inter (hIs i).subset Subset.rfl)⟩
    obtain (rfl | hne) := eq_or_ne i j
    · apply inter_subset_right
    simp [((hdj hne).mono_right (hIs j).subset).inter_eq]
  refine Indep.skewFamily_of_disjoint_bases ?_ ?_ hIs
  · rw [indep_iff_forall_subset_not_circuit hIe]
    intro C hCss hC
    obtain ⟨i, hI⟩ := h C hC (hCss.trans hss)
    have hC' := subset_inter hI hCss
    rw [h_inter] at hC'
    exact hC.dep.not_indep ((hIs i).indep.subset hC')
  exact fun i j hne ↦ (hdj hne).mono ((hIs i).subset) ((hIs j).subset)

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
    M.Skew X Y ↔ M.ModularPair X Y ∧ X ∩ Y ⊆ M.closure ∅ := by
  rw [Skew, SkewFamily, ModularPair, and_congr_right_iff]
  simp [inter_comm X Y]

lemma Skew.inter_subset_loops (h : M.Skew X Y) : X ∩ Y ⊆ M.closure ∅ :=
  (skew_iff_modularPair_inter_subset_loops.1 h).2

lemma Skew.disjoint [Loopless M] (h : M.Skew X Y) : Disjoint X Y := by
  rw [disjoint_iff_inter_eq_empty, ← subset_empty_iff]
  simpa using h.inter_subset_loops

lemma Skew.symm (h : M.Skew X Y) : M.Skew Y X := by
  rw [skew_iff_modularPair_inter_subset_loops] at h ⊢
  rwa [inter_comm, ModularPair.comm]

lemma skew_comm : M.Skew X Y ↔ M.Skew Y X :=
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
  refine (inter_subset_inter hI.subset_closure hJ.subset_closure).trans ?_
  rw [← hu.closure_inter_eq_inter_closure, hdj.inter_eq]

lemma Skew.disjoint_of_indep_subset_left (h : M.Skew X Y) (hI : M.Indep I) (hIX : I ⊆ X) :
    Disjoint I Y :=
  SkewFamily.disjoint_of_indep_subset (i := true) (j := false) h hI hIX (by simp)

lemma Skew.disjoint_of_indep_subset_right (h : M.Skew X Y) (hJ : M.Indep J) (hJY : J ⊆ Y) :
    Disjoint X J :=
  (SkewFamily.disjoint_of_indep_subset (j := true) (i := false) h hJ hJY (by simp)).symm

lemma Skew.disjoint_of_basis_of_subset (h : M.Skew X Y) (hI : M.Basis I X) (hJ : J ⊆ Y) :
    Disjoint I J :=
  (h.disjoint_of_indep_subset_left hI.indep hI.subset).mono_right hJ

lemma Skew.disjoint_of_indep_left (h : M.Skew I X) (hI : M.Indep I) : Disjoint I X :=
  h.disjoint_of_indep_subset_left hI Subset.rfl

lemma Skew.disjoint_of_indep_right (h : M.Skew X I) (hI : M.Indep I) : Disjoint X I :=
  h.disjoint_of_indep_subset_right hI Subset.rfl

lemma Skew.diff_loops_disjoint_left (h : M.Skew X Y) : Disjoint (X \ M.closure ∅) Y := by
  rw [disjoint_iff_inter_eq_empty, ← inter_diff_right_comm, diff_eq_empty]
  exact h.inter_subset_loops

lemma Skew.mono (h : M.Skew X Y) (hX : X' ⊆ X) (hY : Y' ⊆ Y) : M.Skew X' Y' :=
  SkewFamily.mono h (Ys := fun i ↦ bif i then X' else Y') (Bool.rec (by simpa) (by simpa))

lemma Skew.mono_left (h : M.Skew X Y) (hX : X' ⊆ X) : M.Skew X' Y :=
  h.mono hX Subset.rfl

lemma Skew.mono_right (h : M.Skew X Y) (hY : Y' ⊆ Y) : M.Skew X Y' :=
  h.mono Subset.rfl hY

lemma Skew.closure_skew (h : M.Skew X Y) : M.Skew (M.closure X) (M.closure Y) := by
  have h' := SkewFamily.closures_skewFamily h
  simp_rw [Bool.cond_eq_ite, apply_ite, ← Bool.cond_eq_ite] at h'
  exact h'

lemma skew_iff_closure_skew : M.Skew X Y ↔ M.Skew (M.closure X) (M.closure Y) :=
  ⟨Skew.closure_skew, fun h ↦ h.mono (M.subset_closure X) (M.subset_closure Y)⟩

lemma skew_iff_closure_skew_left : M.Skew X Y ↔ M.Skew (M.closure X) Y := by
  by_cases hY : Y ⊆ M.E
  · rw [skew_iff_closure_skew, iff_comm, skew_iff_closure_skew, closure_closure]
  exact iff_of_false (fun h ↦ hY <| h.subset_ground_right) (fun h ↦ hY <| h.subset_ground_right)

lemma skew_iff_closure_skew_right : M.Skew X Y ↔ M.Skew X (M.closure Y) := by
  rw [skew_comm, skew_iff_closure_skew_left, skew_comm]

lemma skew_iff_of_loopEquiv (hX : M.LoopEquiv X X') (hY : M.LoopEquiv Y Y') :
    M.Skew X Y ↔ M.Skew X' Y' := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rwa [skew_iff_closure_skew, ← hX.closure_eq_closure, ← hY.closure_eq_closure,
      ← skew_iff_closure_skew]
  rwa [skew_iff_closure_skew, hX.closure_eq_closure, hY.closure_eq_closure, ← skew_iff_closure_skew]

lemma skew_iff_diff_loops_skew : M.Skew X Y ↔ M.Skew (X \ M.closure ∅) (Y \ M.closure ∅) :=
  skew_iff_of_loopEquiv (M.loopEquiv_diff_loops X) (M.loopEquiv_diff_loops Y)

lemma skew_iff_diff_loops_skew_left : M.Skew X Y ↔ M.Skew (X \ M.closure ∅) Y :=
  skew_iff_of_loopEquiv (M.loopEquiv_diff_loops X) rfl

lemma skew_iff_bases_skew (hI : M.Basis I X) (hJ : M.Basis J Y) : M.Skew I J ↔ M.Skew X Y :=
  ⟨fun h ↦ h.closure_skew.mono hI.subset_closure hJ.subset_closure, fun h ↦ h.mono hI.subset hJ.subset⟩

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
  rw [← pairwise_disjoint_on_bool, Skew, Indep.skewFamily_iff_pairwise_disjoint]
  rwa [union_eq_iUnion] at h

lemma Indep.skew_iff_disjoint_union_indep (hI : M.Indep I) (hJ : M.Indep J) :
    M.Skew I J ↔ Disjoint I J ∧ M.Indep (I ∪ J) := by
  refine ⟨fun h ↦ ⟨h.disjoint_of_indep_left hI, ?_⟩, fun h ↦ h.2.skew_iff_disjoint.2 h.1⟩
  exact h.union_indep_of_indep_subsets hI Subset.rfl hJ Subset.rfl

lemma Indep.subset_skew_diff (h : M.Indep I) (hJI : J ⊆ I) : M.Skew J (I \ J) := by
  rw [Indep.skew_iff_disjoint]
  · exact disjoint_sdiff_right
  exact h.subset (union_subset hJI diff_subset)

lemma skew_iff_contract_restrict_eq_restrict (hX : X ⊆ M.E := by aesop_mat)
    (hY : Y ⊆ M.E := by aesop_mat) : M.Skew X Y ↔ (M ／ X) ↾ Y = M ↾ Y := by
  obtain ⟨I, hI⟩ := M.exists_basis X
  refine ⟨fun h ↦ ?_, fun h ↦ skew_iff_exist_bases.2 ?_⟩
  · refine eq_of_indep_iff_indep_forall rfl fun J (hJ : J ⊆ Y) ↦ ?_
    simp_rw [restrict_indep_iff, hI.contract_indep_iff, and_iff_left hJ]
    refine ⟨fun h ↦ h.1.subset subset_union_left,
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

-- lemma Circuit.something {C : Set α} (hC : M.Circuit C) (hXnt : X.Nontrivial) (hXC : X ⊆ C)
--     (hJ : M.Skew X J) : ∃ C', (M ／ J).Circuit C' ∧ X ⊆ C' := by



lemma empty_skew (hX : X ⊆ M.E) : M.Skew ∅ X := by
  rw [skew_iff_contract_restrict_eq_restrict, contract_empty]

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

lemma skew_iff_forall_circuit (hdj : Disjoint X Y) (hX : X ⊆ M.E := by aesop_mat)
    (hY : Y ⊆ M.E := by aesop_mat) : M.Skew X Y ↔ ∀ C, M.Circuit C → C ⊆ X ∪ Y → C ⊆ X ∨ C ⊆ Y := by
  rw [Skew, skewFamily_iff_forall_circuit]
  · simp [← union_eq_iUnion, or_comm]
  · simp [hX, hY]
  rwa [pairwise_disjoint_on_bool]

lemma skew_of_subset_loops {L : Set α} (hL : L ⊆ M.closure ∅) (hX : X ⊆ M.E) : M.Skew L X := by
  rw [skew_iff_diff_loops_skew_left, diff_eq_empty.2 hL]
  apply empty_skew hX

lemma Loop.skew (he : M.Loop e) (hX : X ⊆ M.E) : M.Skew {e} X :=
  skew_of_subset_loops (by simpa) hX

lemma skew_of_subset_coloops {K : Set α} (hK : K ⊆ M✶.closure ∅) (hdj : Disjoint K X)
    (hX : X ⊆ M.E := by aesop_mat) :
    M.Skew K X := by
  have hKE : K ⊆ M.E := hK.trans (M✶.closure_subset_ground ∅)
  rw [skew_iff_contract_restrict_eq_restrict hKE, contract_eq_delete_of_subset_coloops hK,
    delete_eq_restrict, restrict_restrict_eq]
  rwa [subset_diff, and_iff_left hdj.symm]

lemma Coloop.skew (he : M.Coloop e) (heX : e ∉ X) (hX : X ⊆ M.E := by aesop_mat) : M.Skew {e} X :=
  skew_of_subset_coloops (by simpa) (by simpa)

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
