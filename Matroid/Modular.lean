import Matroid.Flat
import Matroid.Simple
import Matroid.ForMathlib.Card
import Mathlib.Order.ModularLattice

open Set BigOperators Set.Notation

namespace Matroid

variable {α : Type*} {ι : Sort*} {η : Type*} {A : Set η} {M : Matroid α} {B I J X X' Y Y' F : Set α}
    {e : α} {i j : ι} {Xs Ys Is Js : ι → Set α}

section ModularBase

/-- A base `B` is a modular base for an indexed set family if it contains a basis for each set
in the family. -/
@[mk_iff]
structure ModularBase (M : Matroid α) (B : Set α) (Xs : ι → Set α) : Prop :=
  base : M.Base B
  forall_basis : ∀ i, M.Basis ((Xs i) ∩ B) (Xs i)

lemma ModularBase.indep (h : M.ModularBase B Xs) : M.Indep B :=
  h.base.indep

lemma ModularBase.basis_inter (h : M.ModularBase B Xs) (i : ι) : M.Basis ((Xs i) ∩ B) (Xs i) :=
  h.2 i

lemma ModularBase.subset_closure_inter (h : M.ModularBase B Xs) (i : ι) :
    Xs i ⊆ M.closure ((Xs i) ∩ B) :=
  (h.basis_inter i).subset_closure

lemma ModularBase.closure_inter_eq (h : M.ModularBase B Xs) (i : ι) :
    M.closure (Xs i ∩ B) = M.closure (Xs i) :=
  (h.basis_inter i).closure_eq_closure

@[aesop unsafe 5% (rule_sets := [Matroid])]
lemma ModularBase.subset_ground (h : M.ModularBase B Xs) (i : ι) : Xs i ⊆ M.E :=
  (h.basis_inter i).subset_ground

lemma ModularBase.subtype {Xs : η → Set α} (h : M.ModularBase B Xs) (A : Set η) :
    M.ModularBase B (fun i : A ↦ Xs i) :=
  ⟨h.1, fun ⟨i,_⟩ ↦ h.2 i⟩

@[simp] lemma modularBase_pair_iff {B X Y : Set α} :
    M.ModularBase B (fun i : ({X,Y} : Set (Set α)) ↦ i) ↔
      M.Base B ∧ M.Basis (X ∩ B) X ∧ M.Basis (Y ∩ B) Y := by
  simp [modularBase_iff]

lemma ModularBase.basis_iInter [Nonempty ι] (h : M.ModularBase B Xs) :
    M.Basis ((⋂ i, Xs i) ∩ B) (⋂ i, Xs i) :=
  h.1.indep.interBasis_iInter (fun _ ↦ h.2 _)

lemma ModularBase.basis_iUnion (h : M.ModularBase B Xs) :
    M.Basis ((⋃ i, Xs i) ∩ B) (⋃ i, Xs i) := by
  simp_rw [h.1.indep.inter_basis_closure_iff_subset_closure_inter, iUnion_subset_iff]
  exact fun i ↦ (h.subset_closure_inter i).trans
    (M.closure_subset_closure (inter_subset_inter_left _ (subset_iUnion _ i)))

lemma exists_modularBase_of_iUnion_indep (h : M.Indep (⋃ i, Xs i)) : ∃ B, M.ModularBase B Xs := by
  obtain ⟨B, hB, hIB⟩ := h.exists_base_superset
  refine ⟨B, hB, fun i ↦ ?_⟩
  rw [inter_eq_self_of_subset_left <| iUnion_subset_iff.1 hIB i]
  exact (h.subset (subset_iUnion _ i)).basis_self

lemma Base.modularBase_of_forall_subset_closure (hB : M.Base B)
    (h : ∀ i, Xs i ⊆ M.closure ((Xs i) ∩ B)) : M.ModularBase B Xs := by
  exact ⟨hB, fun i ↦ hB.indep.inter_basis_closure_iff_subset_closure_inter.2 (h i)⟩

lemma ModularBase.basis_biInter {Xs : η → Set α} (h : M.ModularBase B Xs) (hA : A.Nonempty) :
    M.Basis ((⋂ i ∈ A, Xs i) ∩ B) (⋂ i ∈ A, Xs i) :=
  h.1.indep.interBasis_biInter hA (fun _ _ ↦ h.2 _)

@[aesop unsafe 5% (rule_sets := [Matroid])]
lemma ModularBase.iInter_subset_ground [Nonempty ι] (h : M.ModularBase B Xs) : ⋂ i, Xs i ⊆ M.E :=
  h.basis_iInter.subset_ground

lemma ModularBase.biInter_subset_ground {Xs : η → Set α} (h : M.ModularBase B Xs)
    (hA : A.Nonempty) : ⋂ i ∈ A, Xs i ⊆ M.E :=
  (h.basis_biInter hA).subset_ground

lemma ModularBase.basis_biUnion {Xs : η → Set α} (h : M.ModularBase B Xs) (A : Set η) :
    M.Basis ((⋃ i ∈ A, Xs i) ∩ B) (⋃ i ∈ A, Xs i) := by
  convert (h.subtype A).basis_iUnion <;> simp

lemma ModularBase.modularBase_of_forall_subset_subset_closure (hB : M.ModularBase B Xs)
    (hXY : ∀ i, Xs i ⊆ Ys i) (hYX : ∀ i, Ys i ⊆ M.closure (Xs i)) : M.ModularBase B Ys := by
  refine ⟨hB.base, fun i ↦ hB.indep.inter_basis_closure_iff_subset_closure_inter.2 ?_⟩
  refine (hYX i).trans (M.closure_subset_closure_of_subset_closure ?_)
  exact (hB.2 i).subset_closure.trans
    (M.closure_subset_closure (inter_subset_inter_left B (hXY i)))

lemma ModularBase.modularBase_cls (hB : M.ModularBase B Xs) :
    M.ModularBase B (fun i ↦ M.closure (Xs i)) :=
  hB.modularBase_of_forall_subset_subset_closure (fun i ↦ M.subset_closure (Xs i))
    (fun _ ↦ Subset.rfl)

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

lemma ModularFamily.cls_modularFamily (h : M.ModularFamily Xs) :
    M.ModularFamily (fun i ↦ M.closure (Xs i)) :=
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
  refine ⟨B', hB'.1, fun i ↦ ?_⟩
  obtain Basis := hB i
  have R_B'_inter_eq : R ∩ B' = B := by
    refine Set.ext <| fun x ↦ ⟨fun x_mem ↦ ?_, fun x_mem ↦ ⟨hBb.subset_ground x_mem, hB'.2 x_mem⟩⟩
    by_contra x_nB
    apply (hB'.1.indep.subset (insert_subset x_mem.2 hB'.2)).not_dep
    rw [Dep, and_iff_left ((insert_subset x_mem.2 hB'.2).trans hB'.1.subset_ground)]
    exact (restrict_dep_iff.1 (hBb.insert_dep ⟨x_mem.1, x_nB⟩)).1
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
lemma ModularFamily.comp {ζ : Sort*} (h : M.ModularFamily Xs) (t : ζ → ι) :
    M.ModularFamily (Xs ∘ t) := by
  obtain ⟨B, hB, hBXs⟩ := h
  exact ⟨B, hB, fun i ↦ (by simpa using hBXs (t i))⟩

lemma ModularFamily.set_biInter_comp {Xs : η → Set α} (h : M.ModularFamily Xs) (t : ι → Set η)
    (ht : ∀ j, (t j).Nonempty) : M.ModularFamily (fun j ↦ ⋂ i ∈ t j, (Xs i)) := by
  obtain ⟨B, hB⟩ := h
  exact ⟨B, hB.base, fun j ↦ hB.basis_biInter (ht j)⟩

lemma ModularFamily.map {β : Type*} (f : α → β) (hf : InjOn f M.E) (h : M.ModularFamily Xs) :
    (M.map f hf).ModularFamily (fun i ↦ f '' (Xs i)) := by
  obtain ⟨B, hB, hBX⟩ := h
  refine ⟨f '' B, hB.map hf, fun i ↦ ?_⟩
  convert (hBX i).map hf
  rw [hf.image_inter (hBX i).subset_ground hB.subset_ground]

lemma modularFamily_map_iff (f : α → η) (hf : InjOn f M.E) {Xs : ι → Set η} :
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
    rw [hI.indep.insert_indep_iff, hI.closure_eq_closure]
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
    (hIi.subset.trans inter_subset_left)
  obtain ⟨IY, hIY, hY⟩ := hIi.indep.subset_basis_of_subset
    (hIi.subset.trans inter_subset_right)
  refine ⟨IX, IY, hIX, hIY, ?_⟩
  rw [hIi.er_eq_encard, hIX.er_eq_encard, ← encard_diff_add_encard_of_subset hX,
    add_comm (encard _), add_assoc, WithTop.add_left_cancel_iff hifin, hIY.er_eq_encard,
    ← encard_union_add_encard_inter, ← union_eq_self_of_subset_left hY, ← union_assoc,
    diff_union_self, union_eq_self_of_subset_right hX] at hr
  refine Basis.indep <| (hXfin.union hYfin).basis_of_subset_closure_of_subset_of_encard_le ?_
    (union_subset_union hIX.subset hIY.subset) (le_of_add_le_left hr.le)
  rw [← M.closure_union_closure_left_eq, ← M.closure_union_closure_right_eq]
  exact (M.subset_closure _).trans
    (M.closure_subset_closure (union_subset_union hIX.subset_closure hIY.subset_closure))

lemma modularPair_iff_r [FiniteRk M] (hXE : X ⊆ M.E := by aesop_mat)
    (hYE : Y ⊆ M.E := by aesop_mat) :
    M.ModularPair X Y ↔ M.r X + M.r Y = M.r (X ∩ Y) + M.r (X ∪ Y) := by
  simp_rw [(M.to_rFin X).modularPair_iff (M.to_rFin Y), ← cast_r_eq, ← Nat.cast_add, Nat.cast_inj]

lemma ModularFamily.modularPair_compl_biUnion {Xs : η → Set α} (h : M.ModularFamily Xs)
    (A : Set η) : M.ModularPair (⋃ i ∈ A, Xs i) (⋃ i ∈ Aᶜ, Xs i) := by
  rw [modularPair_iff]
  obtain ⟨B, hB⟩ := h
  exact ⟨B, hB.indep, hB.basis_biUnion A, hB.basis_biUnion Aᶜ⟩

lemma ModularFamily.modularPair_compl_biInter {Xs : η → Set α} (h : M.ModularFamily Xs) (A : Set η)
    (hA : A.Nonempty) (hA' : A ≠ univ) : M.ModularPair (⋂ i ∈ A, Xs i) (⋂ i ∈ Aᶜ, Xs i) := by
  rw [modularPair_iff]
  obtain ⟨B, hB⟩ := h
  exact ⟨B, hB.indep, hB.basis_biInter hA, hB.basis_biInter (by rwa [nonempty_compl])⟩

lemma ModularFamily.modularPair_singleton_compl_biUnion {Xs : η → Set α} (h : M.ModularFamily Xs)
    (i₀ : η) : M.ModularPair (Xs i₀) (⋃ i ∈ ({i₀} : Set η)ᶜ, Xs i) := by
  convert h.modularPair_compl_biUnion {i₀}; simp

lemma ModularFamily.modularPair_singleton_compl_biInter [Nontrivial η] {Xs : η → Set α}
    (h : M.ModularFamily Xs) (i₀ : η) : M.ModularPair (Xs i₀) (⋂ i ∈ ({i₀} : Set η)ᶜ, Xs i) := by
  convert h.modularPair_compl_biInter {i₀} (by simp)
    (by simpa [ne_univ_iff_exists_not_mem, mem_singleton_iff] using exists_ne i₀); simp

lemma modularPair_insert_closure (M : Matroid α) (X : Set α) (e f : α) :
    M.ModularPair (M.closure (insert e X)) (M.closure (insert f X)) := by
  obtain ⟨I, hI⟩ := M.exists_basis' X

  rw [← closure_insert_closure_eq_closure_insert,
    ← closure_insert_closure_eq_closure_insert (e := f), ← hI.closure_eq_closure]
  obtain (he | he) := em' (e ∈ M.E)
  · rw [← closure_inter_ground, insert_inter_of_not_mem he, closure_inter_ground]
    exact modularPair_of_subset (M.closure_subset_closure (subset_insert _ _))
      (M.closure_subset_ground _)
  obtain (hf | hf) := em' (f ∈ M.E)
  · rw [ModularPair.comm, ← closure_inter_ground, insert_inter_of_not_mem hf, closure_inter_ground]
    exact modularPair_of_subset (M.closure_subset_closure (subset_insert _ _))
      (M.closure_subset_ground _)

  obtain (hfI | hfI) := em (f ∈ M.closure I)
  · rw [ModularPair.comm, insert_eq_of_mem hfI]
    exact modularPair_of_subset (M.closure_subset_closure (subset_insert _ _))
      (M.closure_subset_ground _)
  rw [closure_insert_closure_eq_closure_insert, closure_insert_closure_eq_closure_insert]
  obtain (hef | hef) := em (e ∈ M.closure (insert f I))
  · refine modularPair_of_subset (M.closure_subset_closure_of_subset_closure ?_)
      (M.closure_subset_ground _)
    exact insert_subset hef (M.subset_closure_of_subset (subset_insert _ _)
      (insert_subset hf hI.indep.subset_ground))

  refine ModularPair.closure_closure ?_
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
  (h (M.closure_flat ∅)).subset_ground_left

@[simp] lemma modularSet_iff {M : Matroid α} {X : Set α} :
    M.ModularSet X ↔ ∀ ⦃F⦄, M.Flat F → ∃ I, M.Indep I ∧ M.Basis (X ∩ I) X ∧ M.Basis (F ∩ I) F := by
  simp [ModularSet, modularPair_iff]

lemma modularSet_iff_closure {M : Matroid α} {X : Set α} :
    M.ModularSet X ↔
      ∀ ⦃F⦄, M.Flat F → ∃ I, M.Indep I ∧ X ⊆ M.closure (X ∩ I) ∧ F ⊆ M.closure (F ∩ I) := by
  rw [modularSet_iff]
  refine ⟨fun h F hF ↦ ?_, fun h F hF ↦ ?_⟩
  · obtain ⟨I, hI, hI'⟩ := h hF
    refine ⟨I, hI, ?_⟩
    rwa [← hI.inter_basis_closure_iff_subset_closure_inter,
      ← hI.inter_basis_closure_iff_subset_closure_inter]
  obtain ⟨I, hI, hI'⟩ := h hF
  refine ⟨I, hI, ?_⟩
  rwa [hI.inter_basis_closure_iff_subset_closure_inter,
    hI.inter_basis_closure_iff_subset_closure_inter]

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
  obtain ⟨e, heF, he⟩ := exists_mem_closure_not_mem_of_not_flat h
  rw [modularSet_iff] at hF
  obtain ⟨I, hI, hIF, hIe⟩ := hF (M.closure_flat {e})
  have heM := M.closure_subset_ground F heF
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


-- section Flat

-- variable {F₁ F₂ : Set α}

-- lemma foo (hF₁ : M.Flat F₁) (hF₂ : M.Flat F₂) : M.ModularPair F₁ F₂ ↔
--     IsModularLattice ↑(Icc (hF₁.toFlats ⊓ hF₂.toFlats) (hF₁.toFlats ⊔ hF₂.toFlats)) := by
--   refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
--   · constructor
--     ·

-- end Flat

end Matroid
