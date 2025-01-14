import Mathlib.Data.Matroid.Closure
import Mathlib.Data.Matroid.Map

open Set
namespace Matroid



variable {α : Type*} {ι : Sort*} {N M : Matroid α} {F S I J X Y B C R : Set α} {e f x y : α}

lemma Basis.insert_basis_insert_of_not_mem_closure (hIX : M.Basis I X) (heI : e ∉ M.closure I)
    (heE : e ∈ M.E := by aesop_mat) : M.Basis (insert e I) (insert e X) := by
  refine hIX.insert_basis_insert ?_
  rw [hIX.indep.insert_indep_iff]
  exact .inl ⟨heE, heI⟩

lemma Indep.union_indep_iff_forall_not_mem_closure_right (hI : M.Indep I) (hJ : M.Indep J) :
    M.Indep (I ∪ J) ↔ ∀ e ∈ J \ I, e ∉ M.closure (I ∪ (J \ {e})) := by
  refine ⟨fun h e heJ hecl ↦ h.not_mem_closure_diff_of_mem (.inr heJ.1) ?_, fun h ↦ ?_⟩
  · rwa [union_diff_distrib, diff_singleton_eq_self heJ.2]
  obtain ⟨K, hKIJ, hK⟩ := hI.subset_basis_of_subset (show I ⊆ I ∪ J from subset_union_left)
  obtain rfl | hssu := hKIJ.subset.eq_or_ssubset
  · exact hKIJ.indep
  exfalso
  obtain ⟨e, heI, heK⟩ := exists_of_ssubset hssu
  have heJI : e ∈ J \ I := by
    rw [← union_diff_right, union_comm]
    exact ⟨heI, not_mem_subset hK heK⟩
  refine h _ heJI ?_
  rw [← diff_singleton_eq_self heJI.2, ← union_diff_distrib]
  exact M.closure_subset_closure (subset_diff_singleton hKIJ.subset heK) <| hKIJ.subset_closure heI

lemma Indep.eq_of_spanning_subset (hI : M.Indep I) (hS : M.Spanning S) (hSI : S ⊆ I) : S = I :=
  ((hI.subset hSI).base_of_spanning hS).eq_of_subset_indep hI hSI

lemma Basis.spanning_iff_spanning (hIX : M.Basis I X) : M.Spanning I ↔ M.Spanning X := by
  rw [spanning_iff_closure_eq, spanning_iff_closure_eq, hIX.closure_eq_closure]

lemma Spanning.base_restrict_iff (hS : M.Spanning S) : (M ↾ S).Base B ↔ M.Base B ∧ B ⊆ S := by
  rw [base_restrict_iff', basis'_iff_basis]
  refine ⟨fun h ↦ ⟨?_, h.subset⟩, fun h ↦ h.1.indep.basis_of_subset_of_subset_closure h.2 ?_⟩
  · exact h.indep.base_of_spanning <| by rwa [h.spanning_iff_spanning]
  rw [h.1.closure_eq]
  exact hS.subset_ground

lemma Spanning.compl_coindep (hS : M.Spanning S) : M.Coindep (M.E \ S) := by
  rwa [← spanning_iff_compl_coindep]

lemma Basis.base_of_spanning (hIX : M.Basis I X) (hX : M.Spanning X) : M.Base I :=
  hIX.indep.base_of_spanning <| by rwa [hIX.spanning_iff_spanning]

lemma Restriction.base_iff_of_spanning (hR : N ≤r M) (hN : M.Spanning N.E) :
    N.Base B ↔ (M.Base B ∧ B ⊆ N.E) := by
  obtain ⟨R, hR : R ⊆ M.E, rfl⟩ := hR
  rw [Spanning.base_restrict_iff (show M.Spanning R from hN), restrict_ground_eq]

lemma closure_union_congr_left {X' : Set α} (h : M.closure X = M.closure X') :
    M.closure (X ∪ Y) = M.closure (X' ∪ Y) := by
  rw [← M.closure_union_closure_left_eq, h, M.closure_union_closure_left_eq]

lemma closure_union_congr_right {Y' : Set α} (h : M.closure Y = M.closure Y') :
    M.closure (X ∪ Y) = M.closure (X ∪ Y') := by
  rw [← M.closure_union_closure_right_eq, h, M.closure_union_closure_right_eq]

lemma closure_insert_congr_right (h : M.closure X = M.closure Y) :
    M.closure (insert e X) = M.closure (insert e Y) := by
  simp [← union_singleton, closure_union_congr_left h]
section Constructions

@[simp] lemma emptyOn_closure_eq (X : Set α) : (emptyOn α).closure X = ∅ := by
  rw [← subset_empty_iff, ← emptyOn_ground]; apply closure_subset_ground

@[simp] lemma loopyOn_closure_eq (E X : Set α) : (loopyOn E).closure X = E :=
  (closure_subset_ground _ _).antisymm
    (subset_trans (by rw [(loopyOn_base_iff.2 rfl).closure_eq])
      (closure_subset_closure _ (empty_subset _)))

@[simp] lemma loopyOn_spanning_iff {E : Set α} : (loopyOn E).Spanning X ↔ X ⊆ E := by
  rw [spanning_iff, loopyOn_closure_eq, loopyOn_ground, and_iff_right rfl]

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

lemma restrict_spanning_iff (hSR : S ⊆ R) (hR : R ⊆ M.E := by aesop_mat) :
    (M ↾ R).Spanning S ↔ R ⊆ M.closure S := by
  rw [spanning_iff, restrict_ground_eq, and_iff_left hSR, restrict_closure_eq _ hSR, inter_eq_right]

lemma restrict_spanning_iff' : (M ↾ R).Spanning S ↔ R ∩ M.E ⊆ M.closure S ∧ S ⊆ R := by
  rw [spanning_iff, restrict_closure_eq', restrict_ground_eq, and_congr_left_iff,
    diff_eq_compl_inter, ← union_inter_distrib_right, inter_eq_right, union_comm,
    ← diff_subset_iff, diff_compl]
  intro hSR
  rw [inter_eq_self_of_subset_left hSR]

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
