import Matroid.Flat.Lattice
import Matroid.Simple
import Matroid.ForMathlib.Card
import Matroid.ForMathlib.Matroid.Basic
import Mathlib.Order.ModularLattice
import Mathlib.Order.Zorn

open Set BigOperators Set.Notation

namespace Matroid

variable {α : Type*} {ι : Sort*} {η : Type*} {A : Set η} {M : Matroid α} {B I J X X' Y Y' F : Set α}
    {e : α} {i j : ι} {Xs Ys Is Js : ι → Set α}

section IsModularBase

/-- A base `B` is a modular base for an indexed set family if it contains a basis for each set
in the family. -/
@[mk_iff]
structure IsModularBase (M : Matroid α) (B : Set α) (Xs : ι → Set α) : Prop where
  isBase : M.IsBase B
  forall_isBasis : ∀ i, M.IsBasis ((Xs i) ∩ B) (Xs i)

lemma IsModularBase.indep (h : M.IsModularBase B Xs) : M.Indep B :=
  h.isBase.indep

lemma IsModularBase.isBasis_inter (h : M.IsModularBase B Xs) (i : ι) :
    M.IsBasis ((Xs i) ∩ B) (Xs i) :=
  h.2 i

lemma IsModularBase.subset_closure_inter (h : M.IsModularBase B Xs) (i : ι) :
    Xs i ⊆ M.closure ((Xs i) ∩ B) :=
  (h.isBasis_inter i).subset_closure

lemma IsModularBase.closure_inter_eq (h : M.IsModularBase B Xs) (i : ι) :
    M.closure (Xs i ∩ B) = M.closure (Xs i) :=
  (h.isBasis_inter i).closure_eq_closure

@[aesop unsafe 5% (rule_sets := [Matroid])]
lemma IsModularBase.subset_ground (h : M.IsModularBase B Xs) (i : ι) : Xs i ⊆ M.E :=
  (h.isBasis_inter i).subset_ground

lemma IsModularBase.subtype {Xs : η → Set α} (h : M.IsModularBase B Xs) (A : Set η) :
    M.IsModularBase B (fun i : A ↦ Xs i) :=
  ⟨h.1, fun ⟨i,_⟩ ↦ h.2 i⟩

@[simp] lemma isModularBase_pair_iff {B X Y : Set α} :
    M.IsModularBase B (fun i : ({X,Y} : Set (Set α)) ↦ i) ↔
      M.IsBase B ∧ M.IsBasis (X ∩ B) X ∧ M.IsBasis (Y ∩ B) Y := by
  simp [isModularBase_iff]

lemma IsModularBase.isBasis_iInter [Nonempty ι] (h : M.IsModularBase B Xs) :
    M.IsBasis ((⋂ i, Xs i) ∩ B) (⋂ i, Xs i) :=
  h.1.indep.inter_IsBasis_iInter (fun _ ↦ h.2 _)

lemma IsModularBase.isBasis_iUnion (h : M.IsModularBase B Xs) :
    M.IsBasis ((⋃ i, Xs i) ∩ B) (⋃ i, Xs i) := by
  simp_rw [h.1.indep.inter_isBasis_closure_iff_subset_closure_inter, iUnion_subset_iff]
  exact fun i ↦ (h.subset_closure_inter i).trans
    (M.closure_subset_closure (inter_subset_inter_left _ (subset_iUnion _ i)))

lemma exists_isModularBase_of_iUnion_indep (h : M.Indep (⋃ i, Xs i)) :
    ∃ B, M.IsModularBase B Xs := by
  obtain ⟨B, hB, hIB⟩ := h.exists_isBase_superset
  refine ⟨B, hB, fun i ↦ ?_⟩
  rw [inter_eq_self_of_subset_left <| iUnion_subset_iff.1 hIB i]
  exact (h.subset (subset_iUnion _ i)).isBasis_self

lemma IsBase.isModularBase_of_forall_subset_closure (hB : M.IsBase B)
    (h : ∀ i, Xs i ⊆ M.closure ((Xs i) ∩ B)) : M.IsModularBase B Xs := by
  exact ⟨hB, fun i ↦ hB.indep.inter_isBasis_closure_iff_subset_closure_inter.2 (h i)⟩

lemma IsModularBase.isBasis_biInter {Xs : η → Set α} (h : M.IsModularBase B Xs) (hA : A.Nonempty) :
    M.IsBasis ((⋂ i ∈ A, Xs i) ∩ B) (⋂ i ∈ A, Xs i) :=
  h.1.indep.inter_IsBasis_biInter hA (fun _ _ ↦ h.2 _)

@[aesop unsafe 5% (rule_sets := [Matroid])]
lemma IsModularBase.iInter_subset_ground [Nonempty ι] (h : M.IsModularBase B Xs) :
    ⋂ i, Xs i ⊆ M.E :=
  h.isBasis_iInter.subset_ground

lemma IsModularBase.biInter_subset_ground {Xs : η → Set α} (h : M.IsModularBase B Xs)
    (hA : A.Nonempty) : ⋂ i ∈ A, Xs i ⊆ M.E :=
  (h.isBasis_biInter hA).subset_ground

lemma IsModularBase.isBasis_biUnion {Xs : η → Set α} (h : M.IsModularBase B Xs) (A : Set η) :
    M.IsBasis ((⋃ i ∈ A, Xs i) ∩ B) (⋃ i ∈ A, Xs i) := by
  convert (h.subtype A).isBasis_iUnion <;> simp

lemma IsModularBase.isModularBase_of_forall_subset_subset_closure (hB : M.IsModularBase B Xs)
    (hXY : ∀ i, Xs i ⊆ Ys i) (hYX : ∀ i, Ys i ⊆ M.closure (Xs i)) : M.IsModularBase B Ys := by
  refine ⟨hB.isBase, fun i ↦ hB.indep.inter_isBasis_closure_iff_subset_closure_inter.2 ?_⟩
  refine (hYX i).trans (M.closure_subset_closure_of_subset_closure ?_)
  exact (hB.2 i).subset_closure.trans
    (M.closure_subset_closure (inter_subset_inter_left B (hXY i)))

lemma IsModularBase.isModularBase_cls (hB : M.IsModularBase B Xs) :
    M.IsModularBase B (fun i ↦ M.closure (Xs i)) :=
  hB.isModularBase_of_forall_subset_subset_closure (fun i ↦ M.subset_closure (Xs i))
    (fun _ ↦ Subset.rfl)

lemma IsModularBase.iInter_closure_eq_closure_iInter [Nonempty ι] (hB : M.IsModularBase B Xs) :
    (⋂ i : ι, M.closure (Xs i)) = M.closure (⋂ i : ι, Xs i) := by
  simp_rw [subset_antisymm_iff, subset_iInter_iff, ← hB.closure_inter_eq]
  rw [← closure_iInter_eq_iInter_closure_of_iUnion_indep, ← iInter_inter B Xs]
  · refine ⟨M.closure_subset_closure inter_subset_left, fun i ↦ ?_⟩
    rw [hB.closure_inter_eq]
    exact M.closure_subset_closure (iInter_subset _ i)
  exact hB.isBase.indep.subset (iUnion_subset (fun _ ↦ inter_subset_right))

/-- Given a modular base `B` for `Xs`, we can switch out the intersection of `B` with the
intersection of the `Xs` with any other base for the intersection of the `Xs`
and still have a modular base. -/
lemma IsModularBase.switch (hB : M.IsModularBase B Xs) (hIX : M.IsBasis I (⋂ i, Xs i)) :
    M.IsModularBase ((B \ ⋂ i, Xs i) ∪ I) Xs := by
  obtain hι | hι := isEmpty_or_nonempty ι
  · refine ⟨?_, by simp⟩
    rw [iInter_of_empty, diff_univ, empty_union, ← isBasis_ground_iff]
    exact hIX.isBasis_subset hIX.indep.subset_ground <| by simp
  set J := (⋂ i, Xs i) ∩ B with hJ

  have hJB : M.IsBasis J _ := hB.isBasis_iInter
  set B' := B \ J ∪ I with hB'
  have hB'E : B' ⊆ M.E :=
    union_subset (diff_subset.trans hB.isBase.subset_ground) hIX.indep.subset_ground
  have hdj : Disjoint (B \ J) I
  · rw [disjoint_iff_forall_ne]
    rintro e heBJ _ heI rfl
    apply hB.indep.not_mem_closure_diff_of_mem heBJ.1
    refine mem_of_mem_of_subset ?_ <| M.closure_subset_closure
      (show J ⊆ B \ {e} from subset_diff_singleton inter_subset_right heBJ.2)
    rw [hJB.closure_eq_closure, ← hIX.closure_eq_closure]
    exact (M.subset_closure I) heI

  simp_rw [isModularBase_iff, show B \ ⋂ i, Xs i = B \ J by rw [hJ, diff_inter_self_eq_diff]]
  refine ⟨?_, fun i ↦ ?_⟩
  · rw [← isBasis_ground_iff]
    refine hB.isBase.isBasis_ground.switch_subset_of_isBasis_closure inter_subset_right
      hIX.indep.subset_ground ?_
    rw [hJB.closure_eq_closure]
    exact hIX.isBasis_closure_right
  have hiX : I ⊆ Xs i := hIX.subset.trans (iInter_subset Xs i)
  have hJX : J ⊆ Xs i := inter_subset_left.trans (iInter_subset Xs i)
  rw [inter_union_distrib_left, ← inter_diff_assoc, inter_eq_self_of_subset_right hiX,  inter_comm,
    ← diff_inter_self_eq_diff, ← inter_assoc, inter_eq_self_of_subset_left
    (show J ⊆ B from inter_subset_right), inter_eq_self_of_subset_left hJX, inter_comm]
  refine IsBasis.switch_subset_of_isBasis_closure (hB.isBasis_inter i)
    (subset_inter hJX inter_subset_right) hiX ?_
  rw [hJB.closure_eq_closure]
  exact hIX.isBasis_closure_right


end IsModularBase
section IsModularFamily

/-- A set family is a `IsModularFamily` if it has a modular base. -/
def IsModularFamily (M : Matroid α) (Xs : ι → Set α) := ∃ B, M.IsModularBase B Xs

lemma Indep.isModularFamily (hI : M.Indep I) (hXs : ∀ i, M.IsBasis ((Xs i) ∩ I) (Xs i)) :
    M.IsModularFamily Xs := by
  simp_rw [hI.inter_isBasis_closure_iff_subset_closure_inter] at hXs
  obtain ⟨B, hB, hIB⟩ := hI.exists_isBase_superset
  refine ⟨B, hB, ?_⟩
  simp_rw [hB.indep.inter_isBasis_closure_iff_subset_closure_inter]
  exact fun i ↦ (hXs i).trans (M.closure_subset_closure (inter_subset_inter_right _ hIB))

lemma IsModularFamily.subset_ground_of_mem (h : M.IsModularFamily Xs) (i : ι) : Xs i ⊆ M.E :=
  let ⟨_, h⟩ := h
  h.subset_ground i

lemma IsModularFamily.iInter_closure_eq_closure_iInter [Nonempty ι] (hXs : M.IsModularFamily Xs) :
    (⋂ i : ι, M.closure (Xs i)) = M.closure (⋂ i : ι, Xs i) :=
  let ⟨_, h⟩ := hXs
  h.iInter_closure_eq_closure_iInter

lemma Indep.isModularFamily_of_subsets (hI : M.Indep I) (hJs : ⋃ i, Js i ⊆ I) :
    M.IsModularFamily Js := by
  refine hI.isModularFamily (fun i ↦ ?_)
  have hJI : Js i ⊆ I := (subset_iUnion _ i).trans hJs
  rw [inter_eq_self_of_subset_left hJI]
  exact (hI.subset hJI).isBasis_self

lemma IsModularFamily.isModularFamily_of_forall_subset_closure (h : M.IsModularFamily Xs)
    (hXY : ∀ i, Xs i ⊆ Ys i) (hYX : ∀ i, Ys i ⊆ M.closure (Xs i)) : M.IsModularFamily Ys :=
  let ⟨B, hB⟩ := h
  ⟨B, hB.isModularBase_of_forall_subset_subset_closure hXY hYX⟩

lemma IsModularFamily.cls_isModularFamily (h : M.IsModularFamily Xs) :
    M.IsModularFamily (fun i ↦ M.closure (Xs i)) :=
  let ⟨B, hB⟩ := h
  ⟨B, hB.isModularBase_cls⟩

@[simp] lemma isModularFamily_of_isEmpty [IsEmpty ι] : M.IsModularFamily Xs :=
  M.empty_indep.isModularFamily_of_subsets (by simp)

@[simp] lemma isModularFamily_iff_of_subsingleton [Subsingleton ι] :
    M.IsModularFamily Xs ↔ ∀ i, Xs i ⊆ M.E := by
  obtain (h | ⟨⟨i⟩⟩) := isEmpty_or_nonempty ι; simp
  refine ⟨fun h ↦ h.subset_ground_of_mem, fun h ↦ ?_⟩
  obtain ⟨I, hI⟩ := M.exists_isBasis (Xs i)
  obtain ⟨B, hB, hIB⟩ := hI.indep.exists_isBase_superset
  refine ⟨B, hB, fun j ↦ ?_⟩
  rwa [Subsingleton.elim j i, inter_comm, hI.inter_eq_of_subset_indep hIB hB.indep]

lemma isModularFamily_of_isLoopEquiv (h : M.IsModularFamily Xs)
    (he : ∀ i, M.IsLoopEquiv (Xs i) (Ys i)) : M.IsModularFamily Ys := by
  obtain ⟨B, hB⟩ := h
  refine ⟨B, hB.isBase, fun i ↦ ?_⟩
  rw [← (he i).isBasis_iff, ← (he i).inter_eq_of_indep hB.indep]
  exact hB.isBasis_inter i

lemma IsModularFamily.restrict {R : Set α} (h : M.IsModularFamily Xs) (hXR : ∀ i, Xs i ⊆ R) :
    (M ↾ R).IsModularFamily Xs := by
  obtain ⟨B, hB⟩ := h
  refine Indep.isModularFamily (I := B ∩ R) (by simpa using hB.indep.inter_right R) fun i ↦ ?_
  rw [isBasis_restrict_iff', inter_eq_self_of_subset_left (hB.subset_ground i),
    inter_comm B, ← inter_assoc, inter_eq_self_of_subset_left (hXR i), and_iff_left (hXR i)]
  exact hB.isBasis_inter i

lemma IsModularFamily.delete {D : Set α} (h : M.IsModularFamily Xs) (hXD : ∀ i, Disjoint (Xs i) D) :
    (M ＼ D).IsModularFamily Xs :=
  h.restrict fun i ↦ subset_diff.2 ⟨h.subset_ground_of_mem i, hXD i⟩

lemma IsModularFamily.ofRestrict' {R : Set α}
    (h : (M ↾ R).IsModularFamily Xs) : M.IsModularFamily (fun i ↦ (Xs i) ∩ M.E) := by
  obtain ⟨B, hBb, hB⟩ := h
  obtain ⟨B', hB'⟩ := hBb.indep.of_restrict.exists_isBase_superset
  refine ⟨B', hB'.1, fun i ↦ ?_⟩
  obtain IsBasis := hB i
  have R_B'_inter_eq : R ∩ B' = B := by
    refine Set.ext <| fun x ↦ ⟨fun x_mem ↦ ?_, fun x_mem ↦ ⟨hBb.subset_ground x_mem, hB'.2 x_mem⟩⟩
    by_contra x_nB
    apply (hB'.1.indep.subset (insert_subset x_mem.2 hB'.2)).not_dep
    rw [Dep, and_iff_left ((insert_subset x_mem.2 hB'.2).trans hB'.1.subset_ground)]
    exact (restrict_dep_iff.1 (hBb.insert_dep ⟨x_mem.1, x_nB⟩)).1
  rw [isBasis_restrict_iff'] at IsBasis
  rw [ ← inter_eq_self_of_subset_left IsBasis.2, inter_right_comm _ R, inter_assoc, R_B'_inter_eq,
    inter_assoc, inter_eq_self_of_subset_right (hB'.2.trans hB'.1.subset_ground),
    inter_right_comm, inter_eq_self_of_subset_left IsBasis.2]
  exact IsBasis.1

lemma IsModularFamily.ofRestrict {M : Matroid α} {R : Set α} (hR : R ⊆ M.E)
    (h : (M ↾ R).IsModularFamily Xs) : M.IsModularFamily Xs := by
  convert h.ofRestrict' with i
  rw [inter_eq_self_of_subset_left <| (h.subset_ground_of_mem i).trans hR]

/-- A subfamily of a modular family is a modular family. -/
lemma IsModularFamily.comp {ζ : Sort*} (h : M.IsModularFamily Xs) (t : ζ → ι) :
    M.IsModularFamily (Xs ∘ t) := by
  obtain ⟨B, hB, hBXs⟩ := h
  exact ⟨B, hB, fun i ↦ (by simpa using hBXs (t i))⟩

lemma IsModularFamily.set_biInter_comp {Xs : η → Set α} (h : M.IsModularFamily Xs) (t : ι → Set η)
    (ht : ∀ j, (t j).Nonempty) : M.IsModularFamily (fun j ↦ ⋂ i ∈ t j, (Xs i)) := by
  obtain ⟨B, hB⟩ := h
  exact ⟨B, hB.isBase, fun j ↦ hB.isBasis_biInter (ht j)⟩

lemma IsModularFamily.map {β : Type*} (f : α → β) (hf : InjOn f M.E) (h : M.IsModularFamily Xs) :
    (M.map f hf).IsModularFamily (fun i ↦ f '' (Xs i)) := by
  obtain ⟨B, hB, hBX⟩ := h
  refine ⟨f '' B, hB.map hf, fun i ↦ ?_⟩
  convert (hBX i).map hf
  rw [hf.image_inter (hBX i).subset_ground hB.subset_ground]

lemma isModularFamily_map_iff (f : α → η) (hf : InjOn f M.E) {Xs : ι → Set η} :
    (M.map f hf).IsModularFamily Xs ↔ ∃ Ys, M.IsModularFamily Ys ∧ ∀ i, Xs i = f '' (Ys i) := by
  refine ⟨fun h ↦ ?_, fun ⟨Ys, hYs, h_eq⟩ ↦ ?_⟩
  · obtain ⟨B, hB, h⟩ := h
    simp_rw [map_isBasis_iff'] at h
    rw [map_isBase_iff] at hB
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

lemma IsModularFamily.mapEmbedding {β : Type*} (f : α ↪ β) (h : M.IsModularFamily Xs) :
    (M.mapEmbedding f).IsModularFamily (fun i ↦ f '' (Xs i)) := by
  obtain ⟨B, hB, hBX⟩ := h
  refine ⟨f '' B, hB.mapEmbedding f, fun i ↦ ?_⟩
  convert (hBX i).mapEmbedding f
  rw [image_inter f.injective]

lemma IsModularFamily.of_contract_indep (h : (M ／ I).IsModularFamily Xs) (hI : M.Indep I) :
    M.IsModularFamily (fun i ↦ Xs i ∪ I) := by
  obtain ⟨B, hB, h⟩ := h
  rw [hI.contract_isBase_iff] at hB
  refine ⟨B ∪ I, hB.1, fun i ↦ Indep.isBasis_of_subset_of_subset_closure ?_ ?_ ?_⟩
  · exact hB.1.indep.inter_left _
  · exact inter_subset_left
  rw [← inter_union_distrib_right]
  refine union_subset ((h i).subset_closure.trans ?_)
    (M.subset_closure_of_subset' subset_union_right)
  simp [contract_closure_eq, diff_subset]

/-- A modular base can be chosen to contain a prescribed independent subset of the intersection. -/
lemma IsModularFamily.exists_isModularBase_superset_of_indep_of_subset_inter
    (h : M.IsModularFamily Xs) (hI : M.Indep I) (hIX : I ⊆ ⋂ i, Xs i) :
    ∃ B, M.IsModularBase B Xs ∧ I ⊆ B := by
  obtain he | hne := isEmpty_or_nonempty ι
  · obtain ⟨B, hB⟩ := hI.exists_isBase_superset
    refine ⟨B, ⟨hB.1, by simp⟩, hB.2⟩

  obtain ⟨B, hB⟩ := h
  obtain ⟨J, hJ, hIJ⟩ := hI.subset_isBasis_of_subset hIX
  exact ⟨_,  hB.switch hJ, hIJ.trans subset_union_right⟩

/-- If `C` is spanned by the intersection of a modular family `Xs`,
then we get a modular family in `M ／ C`.  -/
lemma IsModularFamily.contract (h : M.IsModularFamily Xs) {C : Set α}
    (hC : ∀ i, C ⊆ M.closure (Xs i)) : (M ／ C).IsModularFamily (fun i ↦ (Xs i) \ C) := by
  obtain he | hne := isEmpty_or_nonempty ι
  · simp

  obtain ⟨I, hI⟩ := M.exists_isBasis' C
  rw [hI.contract_eq_contract_delete]
  refine IsModularFamily.delete ?_ fun i ↦ disjoint_sdiff_left.mono_right diff_subset
  have hu := h.isModularFamily_of_forall_subset_closure (Ys := fun i ↦ (Xs i ∪ C))
    (fun _ ↦ subset_union_left)
    (fun i ↦ union_subset (M.subset_closure _ (h.subset_ground_of_mem i)) (hC i))

  obtain ⟨B, hB, hIB⟩ := hu.exists_isModularBase_superset_of_indep_of_subset_inter hI.indep
    (by simp [(hI.subset.trans subset_union_right)])

  have hi : (M ／ I).Indep (B \ I) := by simp [hI.indep.contract_indep_iff,
    union_eq_self_of_subset_right hIB, disjoint_sdiff_left, hB.indep]
  refine hi.isModularFamily fun i ↦ (hi.inter_left _).isBasis_of_subset_of_subset_closure
    inter_subset_left ?_

  rw [contract_closure_eq, inter_union_distrib_right, diff_union_of_subset hIB,
    union_inter_distrib_right, inter_eq_self_of_subset_left hIB,
    closure_union_congr_right hI.closure_eq_closure, inter_union_distrib_right,
    diff_union_self, ← inter_union_distrib_right, diff_subset_iff, union_comm,
    diff_union_eq_union_of_subset _ hI.subset]
  have hXb := (hB.isBasis_inter i).subset_closure

  refine (subset_union_left.trans (hXb.trans ?_))
  refine (M.closure_subset_closure ?_).trans subset_union_left
  rw [union_inter_distrib_right]
  refine union_subset_union_right _ inter_subset_left

/-- A `IsModularFamily` of flats in a finite-rank matroid is finite. -/
lemma IsModularFamily.finite_of_forall_isFlat [M.RankFinite] (h : M.IsModularFamily Xs)
    (h_isFlat : ∀ i, M.IsFlat (Xs i)) : (range Xs).Finite := by
  obtain ⟨B, hB⟩ := h
  refine Finite.of_finite_image (f := fun X ↦ X ∩ B)
    (hB.isBase.indep.finite.finite_subsets.subset (by simp)) ?_
  simp only [InjOn, mem_range, forall_exists_index, forall_apply_eq_imp_iff]
  intro i j h_eq
  rw [← (h_isFlat i).closure, ← (hB.isBasis_inter i).closure_eq_closure,
    ← (h_isFlat j).closure, ← (hB.isBasis_inter j).closure_eq_closure, h_eq]


  -- have := (subset_range_iff_exists_image_eq (α := ι) (s := C) (f := Xs)).1
  -- have := h.comp (fun X : C ↦ X)

-- lemma IsModularFamily_of_chain [Finitary M] (hX : IsChain (· ⊆ ·) (range Xs))
--  (hE : ∀ i, Xs i ⊆ M.E) :
--     M.IsModularFamily Xs := by
--   -- set Is := {I : Set α | ∀ i, M.IsBasis (I ∩ Xs i) (Xs i) ∨ I ⊆ M.closure (Xs i)}
--   -- refine Indep.isModularFamily (I := ⋃₀ Is) ?_ ?_
--   set Is : (Set (Set α)) :=
--     {I : Set α | M.Indep I ∧ ∀ i, M.IsBasis (Xs i ∩ I) (Xs i) ∨ I ⊆ Xs i}
--     with hIs
--   have h_chain : ∀ Ks ⊆ Is, IsChain (· ⊆ ·) Ks → ∃ J ∈ Is, ∀ I ∈ Ks, I ⊆ J
--   · intro Ks hKsIs h_chain
--     refine ⟨⋃₀ Ks, ⟨?_, fun i ↦ ?_⟩, fun _ ↦ subset_sUnion_of_mem⟩
--     · exact Indep.sUnion_chain (fun I hI ↦ (hKsIs hI).1) h_chain


--     simp only [sUnion_subset_iff, or_iff_not_imp_right, not_forall, Classical.not_imp,
--       forall_exists_index, and_imp]
--     intro K hK hKcl

--     have hbas : M.IsBasis (Xs i ∩ K) (Xs i) := by simpa [hKcl] using (hKsIs hK).2 i
--     convert hbas using 1
--     rw [subset_antisymm_iff, and_iff_left (inter_subset_inter_right _ (subset_sUnion_of_mem hK))]
--     simp +contextual only [subset_def, mem_inter_iff, mem_sUnion, true_and,
--       and_imp, forall_exists_index]

--     intro e heX K' hK' heK'
--     obtain hle | hle := h_chain.total hK' hK
--     · exact hle heK'

--     obtain hbas' | hcl := (hKsIs hK').2 i
--     · refine (hbas.mem_of_insert_indep heX (hbas'.indep.subset (insert_subset ⟨heX, heK'⟩ ?_))).2
--       exact inter_subset_inter_right _ hle

--     have h_eq := hbas.eq_of_subset_indep ?_ (inter_subset_inter_right _ hle) inter_subset_left
--     refine (h_eq.symm.subset ⟨heX, heK'⟩).2
--     exact (hKsIs hK').1.inter_left _

--   obtain ⟨I, hI⟩ := zorn_subset Is h_chain
--   refine hI.prop.1.isModularFamily fun i ↦ ?_
--   refine (hI.prop.2 i).elim id fun hIcl ↦ ?_




--   refine (hI.prop.1.inter_left (Xs i)).isBasis_of_forall_insert inter_subset_left ?_


--   simp only [inter_eq_self_of_subset_right hIcl, mem_diff, Dep, insert_subset_iff,
--     hIcl.trans (hE i), and_true, and_imp]
--   refine fun f hfX hfI ↦ ⟨fun hi ↦ hfI ?_, (hE i hfX)⟩




--   refine hI.mem_of_prop_insert ⟨hi, fun j ↦ ?_⟩
--   obtain hle | hle := hX.total (x := Xs i) (y := Xs j) (by simp) (by simp)
--   · exact .inr (insert_subset (hle hfX) (hIcl.trans hle))

--   obtain hbasj | b := (hI.prop.2 j)
--   · rw [← hbasj.eq_of_subset_indep (hi.inter_left _)
--       (inter_subset_inter_right _ (subset_insert _ _)) (inter_subset_left)]
--     exact .inl hbasj



end IsModularFamily

section IsModularPair

/-- Sets `X,Y` are a modular pair if some independent set contains bases for both. -/
def IsModularPair (M : Matroid α) (X Y : Set α) :=
  M.IsModularFamily (fun i : Bool ↦ bif i then X else Y)

lemma IsModularPair.symm (h : M.IsModularPair X Y) : M.IsModularPair Y X := by
   obtain ⟨B, hB⟩ := h
   exact ⟨B, hB.isBase, fun i ↦ by simpa using hB.2 !i⟩

lemma isModularPair_comm : M.IsModularPair X Y ↔ M.IsModularPair Y X :=
  ⟨IsModularPair.symm, IsModularPair.symm⟩

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma IsModularPair.subset_ground_left (h : M.IsModularPair X Y) : X ⊆ M.E :=
  h.subset_ground_of_mem true

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma IsModularPair.subset_ground_right (h : M.IsModularPair X Y) : Y ⊆ M.E :=
  h.subset_ground_of_mem false

lemma isModularPair_iff {M : Matroid α} {X Y : Set α} :
    M.IsModularPair X Y ↔ ∃ I, M.Indep I ∧ M.IsBasis (X ∩ I) X ∧ M.IsBasis (Y ∩ I) Y := by
  simp only [IsModularPair, IsModularFamily, mem_singleton_iff, isModularBase_pair_iff, indep_iff]
  refine ⟨fun ⟨B, hB, hB'⟩ ↦ ⟨B, indep_iff.1 hB.indep, ?_⟩,
    fun ⟨I, ⟨B, hB, hIB⟩, hIX, hIY⟩ ↦ ⟨B, hB, ?_⟩ ⟩
  · exact ⟨by simpa using hB' true, by simpa using hB' false⟩
  simp only [Bool.forall_bool, cond_false, cond_true]
  rw [← hIX.eq_of_subset_indep (hB.indep.inter_left X) (inter_subset_inter_right _ hIB)
    inter_subset_left, ← hIY.eq_of_subset_indep (hB.indep.inter_left Y)
    (inter_subset_inter_right _ hIB) inter_subset_left]
  exact ⟨hIY,hIX⟩

lemma IsModularFamily.isModularPair (h : M.IsModularFamily Xs) (i j : ι) :
    M.IsModularPair (Xs i) (Xs j) := by
  obtain ⟨B, hB⟩ := h
  exact isModularPair_iff.2 ⟨B, hB.indep, hB.isBasis_inter i, hB.isBasis_inter j⟩

lemma isModularPair_iff_exists_subsets_closure_inter :
    M.IsModularPair X Y ↔ ∃ I, M.Indep I ∧ X ⊆ M.closure (X ∩ I) ∧ Y ⊆ M.closure (Y ∩ I)  := by
  rw [isModularPair_iff]
  refine ⟨fun ⟨I,hI,h⟩ ↦ ⟨I,hI,?_⟩, fun ⟨I,hI,h⟩ ↦ ⟨I,hI,?_⟩⟩
  · rwa [← hI.inter_isBasis_closure_iff_subset_closure_inter,
      ← hI.inter_isBasis_closure_iff_subset_closure_inter]
  rwa [hI.inter_isBasis_closure_iff_subset_closure_inter,
    hI.inter_isBasis_closure_iff_subset_closure_inter]

lemma IsModularPair.exists_subsets_closure_inter (h : M.IsModularPair X Y) :
    ∃ I, M.Indep I ∧ X ⊆ M.closure (X ∩ I) ∧ Y ⊆ M.closure (Y ∩ I) :=
  isModularPair_iff_exists_subsets_closure_inter.1 h

lemma isModularPair_iff_exists_isBasis_isBasis :
    M.IsModularPair X Y ↔ ∃ I J, M.IsBasis I X ∧ M.IsBasis J Y ∧ M.Indep (I ∪ J) := by
  rw [isModularPair_iff]
  refine ⟨fun ⟨I,hI,hIX,hIY⟩ ↦ ⟨_, _, hIX, hIY, hI.subset (by simp)⟩,
    fun ⟨I,J,hI,hJ,hi⟩ ↦ ⟨_,hi, ?_⟩⟩
  simp_rw [hi.inter_isBasis_closure_iff_subset_closure_inter]
  use hI.subset_closure.trans (M.closure_subset_closure (subset_inter hI.subset subset_union_left))
  exact hJ.subset_closure.trans
    (M.closure_subset_closure (subset_inter hJ.subset subset_union_right))

lemma IsModularPair.exists_common_isBasis (h : M.IsModularPair X Y) : ∃ I,
    M.IsBasis I (X ∪ Y) ∧ M.IsBasis (I ∩ X) X ∧
    M.IsBasis (I ∩ Y) Y ∧ M.IsBasis (I ∩ X ∩ Y) (X ∩ Y) := by
  obtain ⟨B, hB⟩ := h
  refine ⟨(X ∪ Y) ∩ B, ?_⟩
  rw [inter_right_comm, inter_eq_self_of_subset_right subset_union_left,
    inter_right_comm, inter_eq_self_of_subset_right subset_union_right, inter_right_comm]
  refine ⟨?_, by simpa using hB.isBasis_inter true, by simpa using hB.isBasis_inter false, ?_⟩
  · have hu := hB.isBasis_iUnion
    rwa [← union_eq_iUnion] at hu
  have hi := hB.isBasis_iInter
  rwa [← inter_eq_iInter] at hi

lemma IsModularPair.inter_closure_eq (h : M.IsModularPair X Y) :
    M.closure (X ∩ Y) = M.closure X ∩ M.closure Y := by
  convert (IsModularFamily.iInter_closure_eq_closure_iInter h).symm
  · rw [inter_eq_iInter]
  simp_rw [Bool.cond_eq_ite, apply_ite, ← Bool.cond_eq_ite, inter_eq_iInter]

lemma isModularPair_of_subset (hXY : X ⊆ Y) (hY : Y ⊆ M.E) : M.IsModularPair X Y := by
  obtain ⟨I,J, hI, hJ, hIJ⟩ := M.exists_isBasis_subset_isBasis hXY
  refine isModularPair_iff.2 ⟨J, hJ.indep, ?_, by rwa [inter_eq_self_of_subset_right hJ.subset]⟩
  rwa [← hI.eq_of_subset_indep (hJ.indep.inter_left X) (subset_inter hI.subset hIJ)
    inter_subset_left]

lemma Indep.isModularPair_of_union (hi : M.Indep (I ∪ J)) : M.IsModularPair I J := by
  simpa only [iUnion_subset_iff, Bool.forall_bool, cond_false, subset_union_right, cond_true,
    subset_union_left, and_self, forall_true_left] using
    hi.isModularFamily_of_subsets (Js := fun i ↦ bif i then I else J)

lemma IsModularPair.of_subset_closure_subset_closure (h : M.IsModularPair X Y) (hXX' : X ⊆ X')
    (hX' : X' ⊆ M.closure X) (hYY' : Y ⊆ Y') (hY' : Y' ⊆ M.closure Y) : M.IsModularPair X' Y' := by
  apply IsModularFamily.isModularFamily_of_forall_subset_closure h
  · simp [hYY', hXX']
  simp [hY', hX']

lemma IsModularPair.of_subset_closure_left (h : M.IsModularPair X Y) (hXX' : X ⊆ X')
    (hX' : X' ⊆ M.closure X) : M.IsModularPair X' Y :=
  h.of_subset_closure_subset_closure hXX' hX' Subset.rfl (M.subset_closure Y)

lemma IsModularPair.of_subset_closure_right (h : M.IsModularPair X Y) (hYY' : Y ⊆ Y')
    (hY' : Y' ⊆ M.closure Y) : M.IsModularPair X Y' :=
  (h.symm.of_subset_closure_left hYY' hY').symm

lemma IsModularPair.of_isBasis_left (h : M.IsModularPair I Y) (hIX : M.IsBasis I X) :
    M.IsModularPair X Y :=
  h.of_subset_closure_left hIX.subset hIX.subset_closure

lemma IsModularPair.of_isBasis_right (h : M.IsModularPair X J) (hJY : M.IsBasis J Y) :
    M.IsModularPair X Y :=
  h.of_subset_closure_right hJY.subset hJY.subset_closure

lemma IsModularPair.of_isBasis_of_isBasis (h : M.IsModularPair I J) (hIX : M.IsBasis I X)
    (hJY : M.IsBasis J Y) : M.IsModularPair X Y :=
  (h.of_isBasis_left hIX).of_isBasis_right hJY

lemma IsModularPair.closure_left (h : M.IsModularPair X Y) : M.IsModularPair (M.closure X) Y :=
  h.of_subset_closure_left (M.subset_closure X) Subset.rfl

lemma IsModularPair.closure_right (h : M.IsModularPair X Y) : M.IsModularPair X (M.closure Y) :=
  h.symm.closure_left.symm

lemma IsModularPair.closure_closure (h : M.IsModularPair X Y) :
    M.IsModularPair (M.closure X) (M.closure Y) :=
  h.closure_left.closure_right

lemma isModularPair_loops (M : Matroid α) (hX : X ⊆ M.E) : M.IsModularPair X (M.closure ∅) :=
  ((M.isModularPair_of_subset (empty_subset X) hX).closure_left).symm

lemma isModularPair_singleton (he : e ∈ M.E) (hX : X ⊆ M.E) (heX : e ∉ M.closure X) :
    M.IsModularPair {e} X := by
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  have hi : M.Indep (insert e I) := by
    rw [hI.indep.insert_indep_iff, hI.closure_eq_closure]
    exact Or.inl ⟨he, heX⟩
  have hI' := hI.insert_isBasis_insert hi
  rw [← singleton_union] at hI'
  exact hI'.indep.isModularPair_of_union.of_isBasis_right hI

lemma IsModularPair.eRk_add_eRk (h : M.IsModularPair X Y) :
    M.eRk X + M.eRk Y = M.eRk (X ∩ Y) + M.eRk (X ∪ Y) := by
  obtain ⟨I, hIu, hIX, hIY, hIi⟩ := h.exists_common_isBasis
  rw [hIi.eRk_eq_encard, hIu.eRk_eq_encard, hIX.eRk_eq_encard, hIY.eRk_eq_encard,
    ← encard_union_add_encard_inter, ← inter_union_distrib_left, ← inter_inter_distrib_left,
    ← inter_assoc, inter_eq_self_of_subset_left hIu.subset, add_comm]

lemma IsRkFinite.isModularPair_iff_eRk (hXfin : M.IsRkFinite X) (hYfin : M.IsRkFinite Y)
    (hXE : X ⊆ M.E := by aesop_mat) (hYE : Y ⊆ M.E := by aesop_mat) :
    M.IsModularPair X Y ↔ M.eRk X + M.eRk Y = M.eRk (X ∩ Y) + M.eRk (X ∪ Y) := by
  refine ⟨fun h ↦ h.eRk_add_eRk, fun hr ↦ isModularPair_iff_exists_isBasis_isBasis.2 ?_ ⟩
  obtain ⟨Ii, hIi⟩ := M.exists_isBasis (X ∩ Y)
  have hifin : Ii.encard ≠ ⊤ := by
    simpa using hXfin.inter_right.finite_of_isBasis hIi
  obtain ⟨IX, hIX, hX⟩ := hIi.indep.subset_isBasis_of_subset
    (hIi.subset.trans inter_subset_left)
  obtain ⟨IY, hIY, hY⟩ := hIi.indep.subset_isBasis_of_subset
    (hIi.subset.trans inter_subset_right)
  refine ⟨IX, IY, hIX, hIY, ?_⟩
  rw [hIi.eRk_eq_encard, hIX.eRk_eq_encard, ← encard_diff_add_encard_of_subset hX,
    add_comm (encard _), add_assoc, WithTop.add_left_cancel_iff hifin, hIY.eRk_eq_encard,
    ← encard_union_add_encard_inter, ← union_eq_self_of_subset_left hY, ← union_assoc,
    diff_union_self, union_eq_self_of_subset_right hX] at hr
  refine IsBasis.indep <| (hXfin.union hYfin).isBasis_of_subset_closure_of_subset_of_encard_le ?_
    (union_subset_union hIX.subset hIY.subset) (le_of_add_le_left hr.le)
  rw [← M.closure_union_closure_left_eq, ← M.closure_union_closure_right_eq]
  exact (M.subset_closure _).trans
    (M.closure_subset_closure (union_subset_union hIX.subset_closure hIY.subset_closure))

-- TODO : this might be true without one of the `IsRkFinite` assumptions due to junk values.
lemma IsRkFinite.isModularPair_iff_rk (hXfin : M.IsRkFinite X) (hYfin : M.IsRkFinite Y)
    (hXE : X ⊆ M.E := by aesop_mat) (hYE : Y ⊆ M.E := by aesop_mat) :
    M.IsModularPair X Y ↔ M.rk X + M.rk Y = M.rk (X ∩ Y) + M.rk (X ∪ Y) := by
  rw [hXfin.isModularPair_iff_eRk hYfin, ← Nat.cast_inj (R := ℕ∞), ← hXfin.cast_rk_eq,
    ← hYfin.cast_rk_eq, ← hXfin.inter_right.cast_rk_eq, ← (hXfin.union hYfin).cast_rk_eq,
    Nat.cast_add, Nat.cast_add]

lemma isModularPair_iff_rk [RankFinite M] (hXE : X ⊆ M.E := by aesop_mat)
    (hYE : Y ⊆ M.E := by aesop_mat) :
    M.IsModularPair X Y ↔ M.rk X + M.rk Y = M.rk (X ∩ Y) + M.rk (X ∪ Y) := by
  rw [(M.isRkFinite_set X).isModularPair_iff_rk (M.isRkFinite_set Y)]

lemma IsModularFamily.isModularPair_compl_biUnion {Xs : η → Set α} (h : M.IsModularFamily Xs)
    (A : Set η) : M.IsModularPair (⋃ i ∈ A, Xs i) (⋃ i ∈ Aᶜ, Xs i) := by
  rw [isModularPair_iff]
  obtain ⟨B, hB⟩ := h
  exact ⟨B, hB.indep, hB.isBasis_biUnion A, hB.isBasis_biUnion Aᶜ⟩

lemma IsModularFamily.isModularPair_compl_biInter {Xs : η → Set α} (h : M.IsModularFamily Xs)
    (A : Set η) (hA : A.Nonempty) (hA' : A ≠ univ) :
    M.IsModularPair (⋂ i ∈ A, Xs i) (⋂ i ∈ Aᶜ, Xs i) := by
  rw [isModularPair_iff]
  obtain ⟨B, hB⟩ := h
  exact ⟨B, hB.indep, hB.isBasis_biInter hA, hB.isBasis_biInter (by rwa [nonempty_compl])⟩

lemma IsModularFamily.isModularPair_singleton_compl_biUnion {Xs : η → Set α}
    (h : M.IsModularFamily Xs) (i₀ : η) :
    M.IsModularPair (Xs i₀) (⋃ i ∈ ({i₀} : Set η)ᶜ, Xs i) := by
  convert h.isModularPair_compl_biUnion {i₀}; simp

lemma IsModularFamily.isModularPair_singleton_compl_biInter [Nontrivial η] {Xs : η → Set α}
    (h : M.IsModularFamily Xs) (i₀ : η) :
    M.IsModularPair (Xs i₀) (⋂ i ∈ ({i₀} : Set η)ᶜ, Xs i) := by
  convert h.isModularPair_compl_biInter {i₀} (by simp)
    (by simpa [ne_univ_iff_exists_not_mem, mem_singleton_iff] using exists_ne i₀); simp

lemma isModularPair_insert_closure (M : Matroid α) (X : Set α) (e f : α) :
    M.IsModularPair (M.closure (insert e X)) (M.closure (insert f X)) := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X

  rw [← closure_insert_closure_eq_closure_insert,
    ← closure_insert_closure_eq_closure_insert (e := f), ← hI.closure_eq_closure]
  obtain (he | he) := em' (e ∈ M.E)
  · rw [← closure_inter_ground, insert_inter_of_not_mem he, closure_inter_ground]
    exact isModularPair_of_subset (M.closure_subset_closure (subset_insert _ _))
      (M.closure_subset_ground _)
  obtain (hf | hf) := em' (f ∈ M.E)
  · rw [isModularPair_comm, ← closure_inter_ground, insert_inter_of_not_mem hf,
      closure_inter_ground]
    exact isModularPair_of_subset (M.closure_subset_closure (subset_insert _ _))
      (M.closure_subset_ground _)

  obtain (hfI | hfI) := em (f ∈ M.closure I)
  · rw [isModularPair_comm, insert_eq_of_mem hfI]
    exact isModularPair_of_subset (M.closure_subset_closure (subset_insert _ _))
      (M.closure_subset_ground _)
  rw [closure_insert_closure_eq_closure_insert, closure_insert_closure_eq_closure_insert]
  obtain (hef | hef) := em (e ∈ M.closure (insert f I))
  · refine isModularPair_of_subset (M.closure_subset_closure_of_subset_closure ?_)
      (M.closure_subset_ground _)
    exact insert_subset hef (M.subset_closure_of_subset (subset_insert _ _)
      (insert_subset hf hI.indep.subset_ground))

  refine IsModularPair.closure_closure ?_
  apply Indep.isModularPair_of_union
  rw [union_insert, union_eq_self_of_subset_right (subset_insert _ _), insert_comm,
    Indep.insert_indep_iff]
  · exact .inl ⟨he, hef⟩
  rw [hI.indep.insert_indep_iff]
  exact .inl ⟨hf, hfI⟩

lemma IsModularPair.restrict {R : Set α} (hXY : M.IsModularPair X Y) (hXR : X ⊆ R) (hYR : Y ⊆ R) :
    (M ↾ R).IsModularPair X Y :=
  IsModularFamily.restrict hXY <| by simp [hXR, hYR]

lemma IsModularPair.contract_subset_closure {C : Set α} (hXY : M.IsModularPair X Y)
    (hCX : C ⊆ M.closure X) (hCY : C ⊆ M.closure Y) : (M ／ C).IsModularPair (X \ C) (Y \ C) := by
  have hrw : (fun i ↦ bif i then X \ C else Y \ C) = fun i ↦ ((bif i then X else Y) \ C)
  · ext (rfl | rfl) <;> rfl
  rw [IsModularPair, hrw]
  simpa [hCX, hCY] using IsModularFamily.contract (C := C) hXY

lemma IsModularPair.contract {C : Set α} (hXY : M.IsModularPair X Y) (hCX : C ⊆ X) (hCY : C ⊆ Y) :
    (M ／ C).IsModularPair (X \ C) (Y \ C) :=
  hXY.contract_subset_closure (hCX.trans (M.subset_closure X)) (hCY.trans (M.subset_closure Y))



-- lemma IsFlat.isModularPair_iff_foo (hF : M.IsFlat F) (hX : M.IsFlat X) :
--     M.closure (F ∪ X) ∩ Y = M.closure (X ∪ (F ∩ Y))




end IsModularPair



end Matroid
