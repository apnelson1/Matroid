import Mathlib.Data.Matroid.Closure
import Mathlib.Data.Matroid.Map

open Set
namespace Matroid



variable {α : Type*} {ι : Sort*} {M : Matroid α} {F I J X Y B C R : Set α} {e f x y : α}

section Spanning

variable {S T : Set α}

/-- A set is `spanning` in `M` if its closure is equal to `M.E`, or equivalently if it contains
  a base of `M`. -/
@[mk_iff]
structure Spanning (M : Matroid α) (S : Set α) : Prop where
  closure_eq : M.closure S = M.E
  subset_ground : S ⊆ M.E

attribute [aesop unsafe 10% (rule_sets := [Matroid])] Spanning.subset_ground

lemma spanning_iff_closure (hS : S ⊆ M.E := by aesop_mat) : M.Spanning S ↔ M.closure S = M.E := by
  rw [spanning_iff, and_iff_left hS]

lemma closure_spanning_iff (hS : S ⊆ M.E := by aesop_mat) :
    M.Spanning (M.closure S) ↔ M.Spanning S := by
  rw [spanning_iff_closure, closure_closure, ← spanning_iff_closure]

lemma spanning_iff_ground_subset_closure (hS : S ⊆ M.E := by aesop_mat) :
    M.Spanning S ↔ M.E ⊆ M.closure S := by
  rw [spanning_iff_closure, subset_antisymm_iff, and_iff_right (closure_subset_ground _ _)]

lemma not_spanning_iff_closure (hS : S ⊆ M.E := by aesop_mat) :
    ¬M.Spanning S ↔ M.closure S ⊂ M.E := by
  rw [spanning_iff_closure, ssubset_iff_subset_ne, iff_and_self,
    iff_true_intro (M.closure_subset_ground _)]
  exact fun _ ↦ trivial

lemma Spanning.superset (hS : M.Spanning S) (hST : S ⊆ T) (hT : T ⊆ M.E := by aesop_mat) :
    M.Spanning T :=
  ⟨(M.closure_subset_ground _).antisymm
    (by rw [← hS.closure_eq]; exact M.closure_subset_closure hST), hT⟩

lemma Spanning.closure_superset_eq (hS : M.Spanning S) (hST : S ⊆ T) : M.closure T = M.E := by
  rw [← closure_inter_ground, ← spanning_iff_closure]
  exact hS.superset (subset_inter hST hS.subset_ground)

lemma Spanning.union_left (hS : M.Spanning S) (hX : X ⊆ M.E := by aesop_mat) : M.Spanning (S ∪ X) :=
  hS.superset subset_union_left

lemma Spanning.union_right (hS : M.Spanning S) (hX : X ⊆ M.E := by aesop_mat) :
    M.Spanning (X ∪ S) :=
  hS.superset subset_union_right

lemma Base.spanning (hB : M.Base B) : M.Spanning B :=
  ⟨hB.closure_eq, hB.subset_ground⟩

lemma ground_spanning (M : Matroid α) : M.Spanning M.E :=
  ⟨M.closure_ground, rfl.subset⟩

lemma Base.superset_spanning (hB : M.Base B) (hBX : B ⊆ X) (hX : X ⊆ M.E := by aesop_mat) :
    M.Spanning X :=
  hB.spanning.superset hBX

lemma spanning_iff_exists_base_subset' : M.Spanning S ↔ (∃ B, M.Base B ∧ B ⊆ S) ∧ S ⊆ M.E := by
  refine ⟨fun h ↦ ⟨?_, h.subset_ground⟩, fun ⟨⟨B, hB, hBS⟩, hSE⟩ ↦ hB.spanning.superset hBS⟩
  obtain ⟨B, hB⟩ := M.exists_basis S
  have hB' := hB.basis_closure_right
  rw [h.closure_eq, basis_ground_iff] at hB'
  exact ⟨B, hB', hB.subset⟩

lemma spanning_iff_exists_base_subset (hS : S ⊆ M.E := by aesop_mat) :
    M.Spanning S ↔ ∃ B, M.Base B ∧ B ⊆ S := by
  rw [spanning_iff_exists_base_subset', and_iff_left hS]

lemma Spanning.exists_base_subset (hS : M.Spanning S) : ∃ B, M.Base B ∧ B ⊆ S := by
  rwa [spanning_iff_exists_base_subset] at hS

lemma coindep_iff_compl_spanning (hI : I ⊆ M.E := by aesop_mat) :
    M.Coindep I ↔ M.Spanning (M.E \ I) := by
  rw [coindep_iff_exists, spanning_iff_exists_base_subset]

lemma spanning_iff_compl_coindep (hS : S ⊆ M.E := by aesop_mat) :
    M.Spanning S ↔ M.Coindep (M.E \ S) := by
  rw [coindep_iff_compl_spanning, diff_diff_cancel_left hS]

lemma Coindep.compl_spanning (hI : M.Coindep I) : M.Spanning (M.E \ I) :=
  (coindep_iff_compl_spanning hI.subset_ground).mp hI

lemma coindep_iff_closure_compl_eq_ground (hK : X ⊆ M.E := by aesop_mat) :
    M.Coindep X ↔ M.closure (M.E \ X) = M.E := by
  rw [coindep_iff_compl_spanning, spanning_iff_closure]

lemma Coindep.closure_compl (hX : M.Coindep X) : M.closure (M.E \ X) = M.E :=
  (coindep_iff_closure_compl_eq_ground hX.subset_ground).mp hX

lemma Indep.base_of_spanning (hI : M.Indep I) (hIs : M.Spanning I) : M.Base I := by
  obtain ⟨B, hB, hBI⟩ := hIs.exists_base_subset; rwa [← hB.eq_of_subset_indep hI hBI]

lemma Spanning.base_of_indep (hIs : M.Spanning I) (hI : M.Indep I) : M.Base I :=
  hI.base_of_spanning hIs

lemma ext_spanning {M M' : Matroid α} (h : M.E = M'.E)
    (hsp : ∀ S, S ⊆ M.E → (M.Spanning S ↔ M'.Spanning S )) : M = M' := by
  have hsp' : M.Spanning = M'.Spanning := by
    ext S
    refine (em (S ⊆ M.E)).elim (fun hSE ↦ by rw [hsp _ hSE] )
      (fun hSE ↦ iff_of_false (fun h ↦ hSE h.subset_ground)
      (fun h' ↦ hSE (h'.subset_ground.trans h.symm.subset)))
  rw [← dual_inj, eq_iff_indep_iff_indep_forall, dual_ground, dual_ground, and_iff_right h]
  intro I hIE
  rw [← coindep_def, ← coindep_def, coindep_iff_compl_spanning, coindep_iff_compl_spanning, hsp', h]

end Spanning

section Constructions

@[simp] lemma emptyOn_closure_eq (X : Set α) : (emptyOn α).closure X = ∅ := by
  rw [← subset_empty_iff, ← emptyOn_ground]; apply closure_subset_ground

@[simp] lemma loopyOn_closure_eq (E X : Set α) : (loopyOn E).closure X = E :=
  (closure_subset_ground _ _).antisymm
    (subset_trans (by rw [(loopyOn_base_iff.2 rfl).closure_eq])
      (closure_subset_closure _ (empty_subset _)))

lemma closure_empty_eq_ground_iff : M.closure ∅ = M.E ↔ M = loopyOn M.E := by
  refine ⟨fun h ↦ ext_closure ?_, fun h ↦ by rw [h, loopyOn_closure_eq, loopyOn_ground]⟩
  refine fun X ↦ subset_antisymm (by simp [closure_subset_ground]) ?_
  rw [loopyOn_closure_eq, ← h]
  exact M.closure_mono (empty_subset _)

@[simp] lemma uniqueBaseOn_closure_eq (I E X : Set α) :
    (uniqueBaseOn I E).closure X = (X ∩ I ∩ E) ∪ (E \ I) := by
  have hb : (uniqueBaseOn (I ∩ E) E).Basis (X ∩ E ∩ (I ∩ E)) (X ∩ E) :=
    (uniqueBaseOn_basis_iff inter_subset_right).2 rfl
  ext e
  rw [← uniqueBaseOn_inter_ground_eq I E, ← closure_inter_ground _ X, uniqueBaseOn_ground,
    ← hb.closure_eq_closure, hb.indep.mem_closure_iff, dep_iff, uniqueBaseOn_indep_iff',
    insert_subset_iff, uniqueBaseOn_ground, inter_assoc, inter_self,
    and_iff_left inter_subset_right, ← inter_inter_distrib_right, inter_assoc,
    inter_union_distrib_right, inter_comm I, inter_union_diff, insert_subset_iff, inter_comm X,
    inter_assoc, and_iff_left inter_subset_left, mem_inter_iff]
  simp only [not_and, mem_inter_iff, mem_union, mem_diff]
  tauto

@[simp] lemma restrict_closure_eq' (M : Matroid α) (X R : Set α) :
    (M ↾ R).closure X = (M.closure (X ∩ R) ∩ R) ∪ (R \ M.E) := by
  rw [← closure_inter_ground, restrict_ground_eq]
  ext e
  obtain ⟨I, hI⟩ := (M ↾ R).exists_basis (X ∩ R)
  have hI' := (basis_restrict_iff'.mp hI).1
  rw [← hI.closure_eq_closure, ← M.closure_inter_ground (X ∩ R), ← hI'.closure_eq_closure,
    mem_union, mem_inter_iff, hI'.indep.mem_closure_iff, hI.indep.mem_closure_iff, restrict_dep_iff,
    insert_subset_iff, dep_iff, insert_subset_iff, and_iff_left hI'.indep.subset_ground, mem_diff,
    and_iff_left (show I ⊆ R from hI.indep.subset_ground)]
  have hIR : I ⊆ R := hI.indep.subset_ground
  by_cases he : e ∈ M.E; aesop
  simp only [iff_false_intro he, and_false, false_or, and_true, ← mem_inter_iff, ← mem_union,
    inter_eq_self_of_subset_left hIR, union_comm I, and_iff_right
      (show ¬M.Indep (insert e I) from fun hi ↦ he (hi.subset_ground (mem_insert _ _))),
    not_false_iff]

lemma restrict_closure_eq (M : Matroid α) (hXR : X ⊆ R) (hR : R ⊆ M.E := by aesop_mat) :
    (M ↾ R).closure X = M.closure X ∩ R := by
  rw [restrict_closure_eq', diff_eq_empty.mpr hR, union_empty, inter_eq_self_of_subset_left hXR]

@[simp] lemma comap_closure_eq {β : Type*} (M : Matroid β) (f : α → β) (X : Set α) :
    (M.comap f).closure X = f ⁻¹' M.closure (f '' X) := by
  obtain ⟨I, hI⟩ := (M.comap f).exists_basis' X
  obtain ⟨hI', hIinj, -⟩ := comap_basis'_iff.1 hI
  rw [← hI.closure_eq_closure]
  ext x
  obtain (hxE | hxE) := em' (f x ∈ M.E)
  · apply iff_of_false <;> exact (fun h ↦ hxE (by simpa using mem_ground_of_mem_closure h))

  by_cases hxI : x ∈ I
  · exact iff_of_true (mem_closure_of_mem _ hxI hI.indep.subset_ground)
      (mem_closure_of_mem' _ (mem_image_of_mem f (hI.subset hxI))
        (hI'.indep.subset_ground (mem_image_of_mem f hxI)))
  have hss : insert x I ⊆ (M.comap f).E := insert_subset hxE hI.indep.subset_ground
  rw [hI.indep.mem_closure_iff_of_not_mem hxI, ← not_indep_iff hss, comap_indep_iff,
    injOn_insert hxI, not_and, not_and, not_not, iff_true_intro hIinj, true_imp_iff]

  by_cases hxI' : f x ∈ f '' I
  · simp [hxI', hxE, mem_closure_of_mem' _ (hI'.subset hxI') hxE]

  rw [iff_false_intro hxI', imp_false, mem_preimage, image_insert_eq,
    hI'.indep.insert_indep_iff_of_not_mem hxI', mem_diff, and_iff_right hxE, not_not,
    hI'.closure_eq_closure]

@[simp] lemma map_closure_eq {β : Type*} (M : Matroid α) (f : α → β) (hf) (X : Set β) :
    (M.map f hf).closure X = f '' M.closure (f ⁻¹' X) := by
  suffices h' : ∀ X ⊆ f '' M.E, (M.map f hf).closure X = f '' (M.closure (f ⁻¹' X)) by
    convert h' (X ∩ f '' M.E) inter_subset_right using 1
    · rw [← closure_inter_ground]; rfl
    rw [preimage_inter, eq_comm, ← closure_inter_ground, inter_assoc,
      hf.preimage_image_inter Subset.rfl, closure_inter_ground]
  clear X
  intro X hX
  obtain ⟨I, hI⟩ := (M.map f hf).exists_basis X

  obtain ⟨I, X, hI', rfl, rfl⟩ := (map_basis_iff').1 hI

  rw [eq_comm, ← closure_inter_ground, hf.preimage_image_inter hI'.subset_ground,
    ← hI.closure_eq_closure, ← hI'.closure_eq_closure]
  ext e
  simp only [mem_image, hI.indep.mem_closure_iff', map_ground, map_indep_iff, forall_exists_index,
    and_imp, hI'.indep.mem_closure_iff']

  refine ⟨?_, ?_⟩
  · rintro ⟨e, ⟨heE, hind⟩, rfl⟩
    refine ⟨⟨e, heE, rfl⟩, fun J hJ hins ↦ ⟨e, hind ?_, rfl⟩⟩
    rw [← image_insert_eq,
      hf.image_eq_image_iff (insert_subset heE hI'.indep.subset_ground) hJ.subset_ground] at hins
    rwa [hins]
  rintro ⟨⟨x, hx, rfl⟩, h⟩
  refine ⟨x, ⟨hx, fun hind ↦ ?_⟩, rfl⟩
  obtain ⟨x', hx', h_eq⟩ := h _ hind (by rw [image_insert_eq])
  rwa [← hf (hI'.indep.subset_ground hx') hx h_eq]

end Constructions

lemma Indep.inter_basis_closure_iff_subset_closure_inter {X : Set α} (hI : M.Indep I) :
    M.Basis (X ∩ I) X ↔ X ⊆ M.closure (X ∩ I) :=
  ⟨Basis.subset_closure,
    fun h ↦ (hI.inter_left X).basis_of_subset_of_subset_closure inter_subset_left h⟩

lemma Indep.interBasis_biInter {ι : Type*} (hI : M.Indep I) {X : ι → Set α} {A : Set ι}
    (hA : A.Nonempty) (h : ∀ i ∈ A, M.Basis ((X i) ∩ I) (X i)) :
    M.Basis ((⋂ i ∈ A, X i) ∩ I) (⋂ i ∈ A, X i) := by
  refine (hI.inter_left _).basis_of_subset_of_subset_closure inter_subset_left ?_
  have := biInter_inter hA X I
  simp_rw [← biInter_inter hA,
    closure_biInter_eq_biInter_closure_of_biUnion_indep hA (I := fun i ↦ (X i) ∩ I)
      (hI.subset (by simp)), subset_iInter_iff]
  exact fun i hiA ↦ (biInter_subset_of_mem hiA).trans (h i hiA).subset_closure

lemma Indep.interBasis_iInter [Nonempty ι] {X : ι → Set α} (hI : M.Indep I)
    (h : ∀ i, M.Basis ((X i) ∩ I) (X i)) : M.Basis ((⋂ i, X i) ∩ I) (⋂ i, X i) := by
  convert hI.interBasis_biInter (ι := PLift ι) univ_nonempty (X := fun i ↦ X i.down)
    (by simpa using fun (i : PLift ι) ↦ h i.down) <;>
  · simp only [mem_univ, iInter_true]
    exact (iInter_plift_down X).symm

lemma Indep.interBasis_sInter {Xs : Set (Set α)} (hI : M.Indep I) (hXs : Xs.Nonempty)
    (h : ∀ X ∈ Xs, M.Basis (X ∩ I) X) : M.Basis (⋂₀ Xs ∩ I) (⋂₀ Xs) := by
  rw [sInter_eq_biInter]
  exact hI.interBasis_biInter hXs h

lemma Basis.closure_inter_basis_closure (h : M.Basis (X ∩ I) X) (hI : M.Indep I) :
    M.Basis (M.closure X ∩ I) (M.closure X) := by
  rw [hI.inter_basis_closure_iff_subset_closure_inter] at h ⊢
  exact (M.closure_subset_closure_of_subset_closure h).trans (M.closure_subset_closure
    (inter_subset_inter_left _ (h.trans (M.closure_subset_closure inter_subset_left))))

end Matroid
