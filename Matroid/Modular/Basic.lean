import Matroid.Flat.Lattice
import Matroid.Simple
import Matroid.ForMathlib.Card
import Matroid.ForMathlib.Matroid.Basic
import Matroid.ForMathlib.GCongr

open Set BigOperators Set.Notation

namespace Matroid

variable {α : Type*} {ι : Sort*} {η : Type*} {A : Set η} {M : Matroid α} {B I J X X' Y Y' F : Set α}
    {e : α} {i j : ι} {Xs Ys Is Js : ι → Set α}

section IsMutualBasis

/-- An independent sets is a mutual basis for an indexed set family if it contains a basis
for each set in the family. -/
@[mk_iff]
structure IsMutualBasis (M : Matroid α) (B : Set α) (Xs : ι → Set α) : Prop where
  indep : M.Indep B
  forall_isBasis : ∀ i, M.IsBasis ((Xs i) ∩ B) (Xs i)

lemma IsMutualBasis.isBasis_inter (h : M.IsMutualBasis B Xs) (i : ι) :
    M.IsBasis ((Xs i) ∩ B) (Xs i) :=
  h.2 i

lemma IsMutualBasis.subset_closure_inter (h : M.IsMutualBasis B Xs) (i : ι) :
    Xs i ⊆ M.closure ((Xs i) ∩ B) :=
  (h.isBasis_inter i).subset_closure

lemma IsMutualBasis.closure_inter_eq (h : M.IsMutualBasis B Xs) (i : ι) :
    M.closure (Xs i ∩ B) = M.closure (Xs i) :=
  (h.isBasis_inter i).closure_eq_closure

@[aesop unsafe 5% (rule_sets := [Matroid])]
lemma IsMutualBasis.subset_ground (h : M.IsMutualBasis B Xs) (i : ι) : Xs i ⊆ M.E :=
  (h.isBasis_inter i).subset_ground

lemma IsMutualBasis.subtype {Xs : η → Set α} (h : M.IsMutualBasis B Xs) (A : Set η) :
    M.IsMutualBasis B (fun i : A ↦ Xs i) :=
  ⟨h.1, fun ⟨i,_⟩ ↦ h.2 i⟩

@[simp] lemma isMutualBasis_pair_iff {B X Y : Set α} :
    M.IsMutualBasis B (fun i : ({X,Y} : Set (Set α)) ↦ i) ↔
      M.Indep B ∧ M.IsBasis (X ∩ B) X ∧ M.IsBasis (Y ∩ B) Y := by
  simp [isMutualBasis_iff]

lemma IsMutualBasis.isBasis_iInter [Nonempty ι] (h : M.IsMutualBasis B Xs) :
    M.IsBasis ((⋂ i, Xs i) ∩ B) (⋂ i, Xs i) :=
  h.1.inter_isBasis_iInter (fun _ ↦ h.2 _)

lemma IsMutualBasis.isBasis_iUnion (h : M.IsMutualBasis B Xs) :
    M.IsBasis ((⋃ i, Xs i) ∩ B) (⋃ i, Xs i) := by
  simp_rw [h.1.inter_isBasis_closure_iff_subset_closure_inter, iUnion_subset_iff]
  exact fun i ↦ (h.subset_closure_inter i).trans
    (M.closure_subset_closure (inter_subset_inter_left _ (subset_iUnion _ i)))

lemma Indep.isMutualBasis_self (h : M.Indep (⋃ i, Xs i)) :
    M.IsMutualBasis (⋃ i, Xs i) Xs := by
  refine ⟨h, fun i ↦ ?_⟩
  rw [inter_eq_self_of_subset_left (subset_iUnion ..)]
  exact (h.subset (subset_iUnion ..)).isBasis_self

lemma Indep.isMutualBasis_of_forall_subset_closure (hB : M.Indep B)
    (h : ∀ i, Xs i ⊆ M.closure ((Xs i) ∩ B)) : M.IsMutualBasis B Xs := by
  exact ⟨hB, fun i ↦ hB.inter_isBasis_closure_iff_subset_closure_inter.2 (h i)⟩

lemma IsMutualBasis.isBasis_biInter {Xs : η → Set α} (h : M.IsMutualBasis B Xs) (hA : A.Nonempty) :
    M.IsBasis ((⋂ i ∈ A, Xs i) ∩ B) (⋂ i ∈ A, Xs i) :=
  h.1.inter_isBasis_biInter hA (fun _ _ ↦ h.2 _)

@[aesop unsafe 5% (rule_sets := [Matroid])]
lemma IsMutualBasis.iInter_subset_ground [Nonempty ι] (h : M.IsMutualBasis B Xs) :
    ⋂ i, Xs i ⊆ M.E :=
  h.isBasis_iInter.subset_ground

lemma IsMutualBasis.biInter_subset_ground {Xs : η → Set α} (h : M.IsMutualBasis B Xs)
    (hA : A.Nonempty) : ⋂ i ∈ A, Xs i ⊆ M.E :=
  (h.isBasis_biInter hA).subset_ground

lemma IsMutualBasis.isBasis_biUnion {Xs : η → Set α} (h : M.IsMutualBasis B Xs) (A : Set η) :
    M.IsBasis ((⋃ i ∈ A, Xs i) ∩ B) (⋃ i ∈ A, Xs i) := by
  convert (h.subtype A).isBasis_iUnion <;> simp

lemma IsMutualBasis.isMutualBasis_of_forall_subset_subset_closure (hB : M.IsMutualBasis B Xs)
    (hXY : ∀ i, Xs i ⊆ Ys i) (hYX : ∀ i, Ys i ⊆ M.closure (Xs i)) : M.IsMutualBasis B Ys := by
  refine ⟨hB.indep, fun i ↦ hB.indep.inter_isBasis_closure_iff_subset_closure_inter.2 ?_⟩
  refine (hYX i).trans (M.closure_subset_closure_of_subset_closure ?_)
  exact (hB.2 i).subset_closure.trans
    (M.closure_subset_closure (inter_subset_inter_left B (hXY i)))

lemma IsMutualBasis.isMutualBasis_cls (hB : M.IsMutualBasis B Xs) :
    M.IsMutualBasis B (fun i ↦ M.closure (Xs i)) :=
  hB.isMutualBasis_of_forall_subset_subset_closure (fun i ↦ M.subset_closure (Xs i))
    (fun _ ↦ Subset.rfl)

lemma IsMutualBasis.iInter_closure_eq_closure_iInter [Nonempty ι] (hB : M.IsMutualBasis B Xs) :
    (⋂ i : ι, M.closure (Xs i)) = M.closure (⋂ i : ι, Xs i) := by
  simp_rw [subset_antisymm_iff, subset_iInter_iff, ← hB.closure_inter_eq]
  rw [← closure_iInter_eq_iInter_closure_of_iUnion_indep, ← iInter_inter B Xs]
  · refine ⟨M.closure_subset_closure inter_subset_left, fun i ↦ ?_⟩
    rw [hB.closure_inter_eq]
    exact M.closure_subset_closure (iInter_subset _ i)
  exact hB.indep.subset (iUnion_subset (fun _ ↦ inter_subset_right))

lemma Indep.isMutualBasis_powerset (hB : M.Indep B) : M.IsMutualBasis B (fun (I : 𝒫 B) ↦ I.1) where
  indep := hB
  forall_isBasis I := by
    rw [inter_eq_self_of_subset_left I.2]
    exact (hB.subset I.2).isBasis_self

/-- Given a mutual basis `B` for `Xs`, we can switch out the intersection of `B` with the
intersection of the `Xs` with any other base for the intersection of the `Xs`
and still have a mutual basis. -/
lemma IsMutualBasis.switch (hB : M.IsMutualBasis B Xs) (hIX : M.IsBasis I (⋂ i, Xs i)) :
    M.IsMutualBasis ((B \ ⋂ i, Xs i) ∪ I) Xs := by
  obtain hι | hι := isEmpty_or_nonempty ι
  · refine ⟨?_, by simp⟩
    rw [iInter_of_empty, diff_univ, empty_union]
    exact hIX.indep
  set J := (⋂ i, Xs i) ∩ B with hJ

  have hJB : M.IsBasis J _ := hB.isBasis_iInter
  set B' := B \ J ∪ I with hB'
  have hB'E : B' ⊆ M.E :=
    union_subset (diff_subset.trans hB.indep.subset_ground) hIX.indep.subset_ground
  have hdj : Disjoint (B \ J) I
  · rw [disjoint_iff_forall_ne]
    rintro e heBJ _ heI rfl
    apply hB.indep.notMem_closure_diff_of_mem heBJ.1
    refine mem_of_mem_of_subset ?_ <| M.closure_subset_closure
      (show J ⊆ B \ {e} from subset_diff_singleton inter_subset_right heBJ.2)
    rw [hJB.closure_eq_closure, ← hIX.closure_eq_closure]
    exact (M.subset_closure I) heI

  simp_rw [isMutualBasis_iff, show B \ ⋂ i, Xs i = B \ J by rw [hJ, diff_inter_self_eq_diff]]
  refine ⟨?_, fun i ↦ ?_⟩
  · refine (hB.indep.isBasis_closure.switch_subset_of_isBasis_closure (I₀ := J) (J₀ := I)
      inter_subset_right (hIX.subset.trans ?_) ?_).indep
    · exact hB.isBasis_iInter.subset_closure.trans <| M.closure_mono inter_subset_right
    rw [hJ, hB.isBasis_iInter.closure_eq_closure]
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

lemma IsMutualBasis.comp {ζ : Sort*} {Xs : ι → Set α} (h : M.IsMutualBasis B Xs) (t : ζ → ι) :
    M.IsMutualBasis B (Xs ∘ t) where
  indep := h.indep
  forall_isBasis i := h.forall_isBasis (t i)

lemma IsMutualBasis.mono (hI : M.IsMutualBasis I Xs) (hIB : I ⊆ B) (hB : M.Indep B) :
    M.IsMutualBasis B Xs :=
  hB.isMutualBasis_of_forall_subset_closure fun i ↦ (hI.subset_closure_inter i).trans
    <| M.closure_subset_closure <| inter_subset_inter_right _ hIB

lemma IsMutualBasis.isMutualBasis_compl_dual {Xs : ι → Set α} (h : M.IsMutualBasis B Xs)
    (hB : M.IsBase B) : M✶.IsMutualBasis (M.E \ B) (fun i ↦ M.E \ Xs i) := by
  refine ⟨hB.compl_isBase_dual.indep, fun i ↦ ?_⟩
  have hi := h.isBasis_inter i
  rw [inter_comm]
  exact hB.compl_inter_isBasis_of_inter_isBasis (X := Xs i) (by rwa [inter_comm])

lemma IsMutualBasis.isMutualBasis_compl_ofDual {Xs : ι → Set α} (h : M✶.IsMutualBasis B Xs)
    (hB : M✶.IsBase B) : M.IsMutualBasis (M.E \ B) (fun i ↦ M.E \ Xs i) := by
  simpa using h.isMutualBasis_compl_dual hB

lemma IsMutualBasis.isMutualBasis_of_compl {Xs : ι → Set α} (hXs : ∀ i, Xs i ⊆ M.E)
    (h : M.IsMutualBasis B (fun i ↦ M.E \ Xs i)) (hB : M.IsBase B) :
    M✶.IsMutualBasis (M.E \ B) Xs := by
  convert h.isMutualBasis_compl_dual hB with i
  rw [diff_diff_cancel_left (hXs i)]


end IsMutualBasis
section IsModularFamily

/-- A set family is a `IsModularFamily` if it has a modular base. -/
def IsModularFamily (M : Matroid α) (Xs : ι → Set α) := ∃ B, M.IsMutualBasis B Xs

lemma Indep.isModularFamily (hI : M.Indep I) (hXs : ∀ i, M.IsBasis ((Xs i) ∩ I) (Xs i)) :
    M.IsModularFamily Xs := by
  simp_rw [hI.inter_isBasis_closure_iff_subset_closure_inter] at hXs
  refine ⟨I, hI, by simpa [hI.inter_isBasis_closure_iff_subset_closure_inter]⟩

lemma IsModularFamily.exists_isMutualBasis_isBase (h : M.IsModularFamily Xs) :
    ∃ B, M.IsBase B ∧ M.IsMutualBasis B Xs := by
  obtain ⟨I, hI⟩ := h
  obtain ⟨B, hB, hIB⟩ := hI.indep.exists_isBase_superset
  exact ⟨B, hB, hI.mono hIB hB.indep⟩

lemma IsMutualBasis.isModularFamily (hB : M.IsMutualBasis B Xs) : M.IsModularFamily Xs := ⟨B, hB⟩

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
  ⟨B, hB.isMutualBasis_of_forall_subset_subset_closure hXY hYX⟩

lemma IsModularFamily.cls_isModularFamily (h : M.IsModularFamily Xs) :
    M.IsModularFamily (fun i ↦ M.closure (Xs i)) :=
  let ⟨B, hB⟩ := h
  ⟨B, hB.isMutualBasis_cls⟩

@[simp] lemma isModularFamily_of_isEmpty [IsEmpty ι] : M.IsModularFamily Xs :=
  M.empty_indep.isModularFamily_of_subsets (by simp)

@[simp]
lemma isModularFamily_iff_of_subsingleton [Subsingleton ι] :
    M.IsModularFamily Xs ↔ ∀ i, Xs i ⊆ M.E := by
  obtain (h | ⟨⟨i⟩⟩) := isEmpty_or_nonempty ι; simp
  refine ⟨fun h ↦ h.subset_ground_of_mem, fun h ↦ ?_⟩
  obtain ⟨I, hI⟩ := M.exists_isBasis (Xs i)
  exact ⟨I, hI.indep,
    fun j ↦ by rwa [Subsingleton.elim j i, inter_eq_self_of_subset_right hI.subset] ⟩

lemma isModularFamily_of_isLoopEquiv (h : M.IsModularFamily Xs)
    (he : ∀ i, M.IsLoopEquiv (Xs i) (Ys i)) : M.IsModularFamily Ys := by
  obtain ⟨B, hB⟩ := h
  refine ⟨B, hB.indep, fun i ↦ ?_⟩
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
  -- obtain ⟨B', hB'⟩ := hBb.indep.of_restrict
  refine ⟨B, hBb.1, fun i ↦ ?_⟩
  obtain IsBasis := hB i
  rw [isBasis_restrict_iff'] at IsBasis
  rw [inter_assoc, inter_eq_self_of_subset_right hBb.of_restrict.subset_ground]
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
  exact ⟨B, hB.indep, fun j ↦ hB.isBasis_biInter (ht j)⟩

lemma IsModularFamily.map {β : Type*} (f : α → β) (hf : InjOn f M.E) (h : M.IsModularFamily Xs) :
    (M.map f hf).IsModularFamily (fun i ↦ f '' (Xs i)) := by
  obtain ⟨B, hB, hBX⟩ := h
  refine ⟨f '' B, hB.map _ hf , fun i ↦ ?_⟩
  convert (hBX i).map hf
  rw [hf.image_inter (hBX i).subset_ground hB.subset_ground]

lemma IsModularFamily.of_comap {β : Type*} {f : α → β} {M : Matroid β}
    (hX : (M.comap f).IsModularFamily Xs) : M.IsModularFamily (fun i ↦ f '' (Xs i)) := by
  obtain ⟨B, hB⟩ := hX
  refine ⟨f '' B, hB.indep.1, fun i ↦ ?_⟩
  obtain ⟨hBi, hBinj⟩ := comap_indep_iff.1 hB.indep
  have hB_inter := comap_isBasis_iff.1 <| hB.isBasis_inter i
  refine (hBi.inter_left _).isBasis_of_subset_of_subset_closure inter_subset_left ?_
  grw [← image_inter_subset, hB_inter.1.closure_eq_closure,
    ← subset_closure _ _ hB_inter.1.subset_ground]

lemma IsModularFamily.comap_iff {β : Type*} {f : α → β} {M : Matroid β} (hf : f.Injective):
    (M.comap f).IsModularFamily Xs ↔ M.IsModularFamily (fun i ↦ f '' (Xs i)) := by
  refine ⟨IsModularFamily.of_comap, fun ⟨B, hB⟩ ↦ ?_⟩
  have hss := hB.isBasis_iUnion.subset
  rw [← image_iUnion] at hss
  obtain ⟨B', hB', hinj⟩ :=
    exists_image_eq_injOn_of_subset_range (hss.trans (image_subset_range ..))
  refine ⟨B', ⟨hB.indep.subset (by simp [hB']), hinj⟩, fun i ↦ ?_⟩
  have hBi := hB.isBasis_inter i
  simp only [comap_isBasis_iff, inter_subset_left, and_true, image_inter hf]
  rwa [and_iff_left hf.injOn, hB', ← inter_assoc,
    inter_eq_self_of_subset_left (image_mono (subset_iUnion _ _))]

lemma isModularFamily_map_iff (f : α → η) (hf : InjOn f M.E) {Xs : ι → Set η} :
    (M.map f hf).IsModularFamily Xs ↔ ∃ Ys, M.IsModularFamily Ys ∧ ∀ i, Xs i = f '' (Ys i) := by
  refine ⟨fun h ↦ ?_, fun ⟨Ys, hYs, h_eq⟩ ↦ ?_⟩
  · obtain ⟨B, hB, h⟩ := h
    simp_rw [map_isBasis_iff'] at h
    rw [map_indep_iff] at hB
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
  rw [hI.contract_indep_iff] at hB
  refine ⟨B ∪ I, hB.2, fun i ↦ Indep.isBasis_of_subset_of_subset_closure ?_ ?_ ?_⟩
  · exact hB.2.inter_left _
  · exact inter_subset_left
  rw [← inter_union_distrib_right]
  refine union_subset ((h i).subset_closure.trans ?_)
    (M.subset_closure_of_subset' subset_union_right)
  simp [contract_closure_eq]

/-- A mutual basis can be chosen to contain a prescribed independent subset of the intersection. -/
lemma IsModularFamily.exists_isMutualBasis_superset_of_indep_of_subset_inter
    (h : M.IsModularFamily Xs) (hI : M.Indep I) (hIX : I ⊆ ⋂ i, Xs i) :
    ∃ B, M.IsMutualBasis B Xs ∧ I ⊆ B := by
  obtain he | hne := isEmpty_or_nonempty ι
  · exact ⟨I, ⟨hI, by simp⟩, rfl.subset⟩
  obtain ⟨B, hB⟩ := h
  obtain ⟨J, hJ, hIJ⟩ := hI.subset_isBasis_of_subset hIX
  exact ⟨_,  hB.switch hJ, hIJ.trans subset_union_right⟩

/-- If `C` is spanned by the intersection of a modular family `Xs`,
then we get a modular family in `M ／ C`.
TODO : Is this true for all `C ⊆ ⋃ i, X i`? -/
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

  obtain ⟨B, hB, hIB⟩ := hu.exists_isMutualBasis_superset_of_indep_of_subset_inter hI.indep
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
    (hB.indep.finite.finite_subsets.subset (by simp)) ?_
  simp only [InjOn, mem_range, forall_exists_index, forall_apply_eq_imp_iff]
  intro i j h_eq
  rw [← (h_isFlat i).closure, ← (hB.isBasis_inter i).closure_eq_closure,
    ← (h_isFlat j).closure, ← (hB.isBasis_inter j).closure_eq_closure, h_eq]

lemma isModularFamily_disjointSigma_iff (Xs : ι → Set α) {M : η → Matroid α} {hdj} :
    (Matroid.disjointSigma M hdj).IsModularFamily Xs ↔
    (∀ c, (M c).IsModularFamily (fun i ↦ Xs i ∩ (M c).E)) ∧ ∀ i, Xs i ⊆ ⋃ c, (M c).E := by
  refine ⟨fun h ↦ ⟨fun c ↦ ?_, fun i ↦ ?_⟩, fun ⟨h, hE⟩ ↦ ?_⟩
  · obtain ⟨B, hB, hBX⟩ := h.exists_isMutualBasis_isBase
    simp only [disjointSigma_isBase_iff] at hB
    refine ⟨B ∩ (M c).E, (hB.1 c).indep, fun i ↦ ?_⟩
    rw [← inter_assoc, inter_right_comm, inter_assoc (Xs i), inter_self, inter_right_comm]
    have hbas := hBX.isBasis_inter i
    simp only [disjointSigma_isBasis_iff, inter_subset_left, true_and] at hbas
    exact hbas.1 c
  · simpa using h.subset_ground_of_mem i
  choose B hB using fun c ↦ (h c)
  have hrw (c) : (⋃ i, B i) ∩ (M c).E = B c := by
    refine (subset_inter (subset_iUnion ..) (hB c).indep.subset_ground).antisymm' ?_
    rw [iUnion_inter, iUnion_subset_iff]
    intro d
    obtain rfl | hne := eq_or_ne c d
    · simp
    simp [((hdj hne.symm).mono_left (hB d).indep.subset_ground).inter_eq]
  use ⋃ i, B i
  simp only [isMutualBasis_iff, disjointSigma_indep_iff, hrw, iUnion_subset_iff,
    disjointSigma_isBasis_iff, inter_subset_left, true_and, inter_assoc]
  refine ⟨⟨fun c ↦ (hB c).indep, fun c ↦ subset_iUnion_of_subset c (hB c).indep.subset_ground⟩,
    fun i ↦ ⟨fun c ↦ ?_, hE i⟩⟩
  rw [← inter_eq_self_of_subset_right (hB c).indep.subset_ground, ← inter_assoc]
  exact (hB c).isBasis_inter i

 lemma isModularFamily_disjointSum_iff {Xs : ι → Set α} {M N : Matroid α} (hdj) :
    (M.disjointSum N hdj).IsModularFamily Xs ↔
      (M.IsModularFamily (fun i ↦ Xs i ∩ M.E)) ∧ (N.IsModularFamily (fun i ↦ Xs i ∩ N.E)) ∧
      ∀ i, Xs i ⊆ M.E ∪ N.E := by
  rw [disjointSum_eq_disjointSigma, isModularFamily_disjointSigma_iff]
  simp only [Bool.forall_bool, cond_false, cond_true, iUnion_bool]
  tauto

end IsModularFamily

section IsModularPair

/-- Sets `X,Y` are a modular pair if some independent set contains bases for both. -/
def IsModularPair (M : Matroid α) (X Y : Set α) :=
  M.IsModularFamily (fun i : Bool ↦ bif i then X else Y)

lemma IsModularPair.symm (h : M.IsModularPair X Y) : M.IsModularPair Y X := by
   obtain ⟨B, hB⟩ := h
   exact ⟨B, hB.indep, fun i ↦ by simpa using hB.2 !i⟩

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
  simp only [IsModularPair, IsModularFamily, indep_iff]
  refine ⟨fun ⟨B, hB, hB'⟩ ↦ ⟨B, indep_iff.1 hB, ?_⟩,
    fun ⟨I, ⟨B, hB, hIB⟩, hIX, hIY⟩ ↦ ⟨B, hB.indep, ?_⟩ ⟩
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

lemma IsModularPair.exists_isMutualBasis_isBase (h : M.IsModularPair X Y) : ∃ B,
    M.IsBase B ∧ M.IsBasis ((X ∪ Y) ∩ B) (X ∪ Y) ∧ M.IsBasis (X ∩ B) X ∧
    M.IsBasis (Y ∩ B) Y ∧ M.IsBasis (X ∩ Y ∩ B) (X ∩ Y) := by
  rw [IsModularPair] at h
  obtain ⟨B, hB, hB'⟩ := h.exists_isMutualBasis_isBase
  exact ⟨B, hB, by simpa using hB'.isBasis_iUnion,
    by simpa using hB'.isBasis_inter true, by simpa using hB'.isBasis_inter false,
    by simpa using hB'.isBasis_iInter⟩

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

lemma isModularPair_loops (M : Matroid α) (hX : X ⊆ M.E) : M.IsModularPair X (M.loops) :=
  ((M.isModularPair_of_subset (empty_subset X) hX).closure_left).symm

lemma Spanning.isModularPair_iff (hX : M.Spanning X) :
    M.IsModularPair X Y ↔ Y ⊆ M.closure (X ∩ Y) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨I, hIXY, hIX, hIY, hIi⟩ := h.exists_common_isBasis
    grw [← hIi.closure_eq_closure,
      (hIX.isBase_of_spanning hX).eq_of_subset_indep hIXY.indep inter_subset_left]
    exact hIY.subset_closure
  obtain ⟨I, J, hI, hJ, hIJ⟩ :=
    M.exists_isBasis_subset_isBasis (show X ∩ Y ⊆ X from inter_subset_left)
  rw [isModularPair_iff_exists_isBasis_isBasis]
  refine ⟨J, I, hJ, ?_, hJ.indep.subset <| by simpa⟩
  refine hI.indep.isBasis_of_subset_of_subset_closure (hI.subset.trans inter_subset_right) ?_
  grw [hI.closure_eq_closure, ← h]

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
    add_comm (encard _), add_assoc, add_right_inj_of_ne_top hifin, hIY.eRk_eq_encard,
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
  rw [hXfin.isModularPair_iff_eRk hYfin, ← ENat.coe_inj, ← hXfin.cast_rk_eq,
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
    (by simp); simp

lemma isModularPair_insert_closure (M : Matroid α) (X : Set α) (e f : α) :
    M.IsModularPair (M.closure (insert e X)) (M.closure (insert f X)) := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X

  rw [← closure_insert_closure_eq_closure_insert,
    ← closure_insert_closure_eq_closure_insert (e := f), ← hI.closure_eq_closure]
  obtain (he | he) := em' (e ∈ M.E)
  · rw [← closure_inter_ground, insert_inter_of_notMem he, closure_inter_ground]
    exact isModularPair_of_subset (M.closure_subset_closure (subset_insert _ _))
      (M.closure_subset_ground _)
  obtain (hf | hf) := em' (f ∈ M.E)
  · rw [isModularPair_comm, ← closure_inter_ground, insert_inter_of_notMem hf,
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

lemma Coindep.subset_closure_iff_isModularPair (hX : M.Coindep (X \ Y))
    (hY : Y ⊆ M.E := by aesop_mat) : X ⊆ M.closure Y ↔ M.IsModularPair (X ∪ Y) (M.E \ (X \ Y)) := by
  rw [isModularPair_comm, hX.compl_spanning.isModularPair_iff,
    show M.E \ (X \ Y) ∩ (X ∪ Y) = Y by grind, union_subset_iff, and_iff_left (M.subset_closure Y)]

lemma isModularPair_disjointSigma_iff (X Y : Set α) {M : η → Matroid α} {hdj} :
    (Matroid.disjointSigma M hdj).IsModularPair X Y ↔
    (∀ c, (M c).IsModularPair (X ∩ (M c).E) (Y ∩ (M c).E)) ∧ X ∪ Y ⊆ ⋃ c, (M c).E := by
  simp only [IsModularPair, isModularFamily_disjointSigma_iff, Bool.forall_bool, cond_false,
    cond_true, union_subset_iff]
  rw [and_comm (a := X ⊆ _)]
  convert Iff.rfl using 5 with i j
  grind

lemma isModularPair_disjointSum_iff (X Y : Set α) {M N : Matroid α} {hdj} :
    (M.disjointSum N hdj).IsModularPair X Y ↔ M.IsModularPair (X ∩ M.E) (Y ∩ M.E) ∧
      N.IsModularPair (X ∩ N.E) (Y ∩ N.E) ∧ X ∪ Y ⊆ M.E ∪ N.E := by
  simp only [disjointSum_eq_disjointSigma, isModularPair_disjointSigma_iff, Bool.forall_bool,
    cond_false, cond_true, iUnion_bool, union_subset_iff]
  tauto

end IsModularPair

end Matroid
