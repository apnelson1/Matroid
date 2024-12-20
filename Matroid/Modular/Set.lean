import Matroid.Connectivity.Local

namespace Matroid

open Set


variable {α : Type*} {M : Matroid α} {B I J X X' Y Y' F F' F₀ F₁ F₂ : Set α} {e : α}

section ModularSet


/-- A `ModularSet` is a set that is a modular pair with every flat. -/
def ModularSet (M : Matroid α) (X : Set α) := ∀ ⦃F⦄, M.Flat F → M.ModularPair X F

@[simp] lemma modularSet_def : M.ModularSet X ↔ ∀ ⦃F⦄, M.Flat F → M.ModularPair X F := Iff.rfl

@[aesop unsafe 5% (rule_sets := [Matroid])]
lemma ModularSet.subset_ground (h : M.ModularSet X) : X ⊆ M.E :=
  (h (M.closure_flat ∅)).subset_ground_left

@[simp] lemma modularSet_iff :
    M.ModularSet X ↔ ∀ ⦃F⦄, M.Flat F → ∃ I, M.Indep I ∧ M.Basis (X ∩ I) X ∧ M.Basis (F ∩ I) F := by
  simp [ModularSet, modularPair_iff]

lemma modularSet_iff_closure :
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

lemma ModularSet.restrict_flat (hF : M.ModularSet F) (hF' : M.Flat F') (hFF' : F ⊆ F') :
    (M ↾ F').ModularSet F := by
  intro F₁ hF₂
  obtain ⟨F₁, hF₁, rfl⟩ := (flat_restrict_iff hF'.subset_ground).1 hF₂
  exact (hF (hF₁.inter hF')).restrict hFF' inter_subset_right

lemma ModularSet.contract_subset {C : Set α} (hF : M.ModularSet F) (hC : C ⊆ M.closure F) :
    (M ／ C).ModularSet (F \ C) := by
  have hCE : C ⊆ M.E := hC.trans (M.closure_subset_ground _)
  intro F' hF'
  rw [flat_contract_iff] at hF'
  simpa [hF'.2.sdiff_eq_left] using
    (hF hF'.1).contract_subset_closure hC (M.subset_closure_of_subset' subset_union_right hCE)

end ModularSet


section Modular

/-- A modular matroid is one where every flat is modular. The simple finite modular matroids
are the free matroids, the rank-two uniform matroids, the projective planes, and the
finite Desarguesian projective geometries. -/
def Modular (M : Matroid α) : Prop := ∀ ⦃F⦄, M.Flat F → M.ModularSet F

lemma Modular.modularSet_of_flat (hM : M.Modular) (hF : M.Flat F) : M.ModularSet F :=
  hM hF

lemma modular_iff : M.Modular ↔ ∀ ⦃F⦄, M.Flat F → M.ModularSet F := Iff.rfl

lemma modular_iff_forall_modularPair :
    M.Modular ↔ ∀ ⦃F F'⦄, M.Flat F → M.Flat F' → M.ModularPair F F' :=
  forall_cond_comm

lemma Modular.modularPair (h : M.Modular) (hF : M.Flat F) (hF' : M.Flat F') : M.ModularPair F F' :=
  h hF hF'

lemma freeOn_modular (E : Set α) : (freeOn E).Modular := by
  intro F
  simp only [freeOn_flat_iff, modularSet_def, modularPair_iff, freeOn_indep_iff, freeOn_basis_iff,
    inter_eq_left]
  aesop

lemma Modular.restrict_flat (hM : M.Modular) (hF : M.Flat F) : (M ↾ F).Modular := by
  intro F' hF'
  obtain ⟨F₁, hF₁, rfl⟩ := (flat_restrict_iff hF.subset_ground).1 hF'
  exact ModularSet.restrict_flat (hM (hF₁.inter hF)) hF hF'.subset_ground

lemma Modular.contract (hM : M.Modular) (C : Set α) : (M ／ C).Modular := by
  wlog h : C ⊆ M.E generalizing C with h'
  · rw [← contract_inter_ground_eq]
    apply h' _ inter_subset_right
  intro F hF F' hF'
  rw [flat_contract_iff] at hF hF'
  convert (hM.modularPair (M.closure_flat (F ∪ C)) (M.closure_flat (F' ∪ C))).contract (C := C)
    (M.subset_closure_of_subset' subset_union_right)
    (M.subset_closure_of_subset' subset_union_right)

  · rw [hF.1.closure, union_diff_right, hF.2.sdiff_eq_left]
  rw [hF'.1.closure, union_diff_right, hF'.2.sdiff_eq_left]

-- lemma modular_foo : M.Modular ↔ ∀ ⦃L H⦄, M.Line L → M.Hyperplane H → M.er (L ∩ H) ≠ 0 := by
--   refine ⟨fun h L H hL hH ↦ ?_, fun h ↦ ?_⟩
--   · have := h.localConn




end Modular
