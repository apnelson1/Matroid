import Matroid.Intersection
import Matroid.Sum
import Matroid.Uniform.Basic

namespace Matroid

open Set Sum

variable {α : Type*} {M N : Matroid α} {E I J X Y : Set α} {x y : α}


def UnionIndep (M : Matroid α) (N : Matroid α) (I : Set α) : Prop :=
    ∃ J K, M.Indep J ∧ N.Indep K ∧ J ∪ K = I

lemma Indep.unionIndep (hI : M.Indep I) (hJ : N.Indep J) : M.UnionIndep N (I ∪ J) :=
  ⟨I, J, hI, hJ, rfl⟩

lemma UnionIndep.exists (h : M.UnionIndep N I) :
    ∃ J K, Disjoint J K ∧ M.Indep J ∧ N.Indep K ∧ I = J ∪ K := by
  obtain ⟨J, K, hJ, hK, rfl⟩ := h
  exact ⟨J, K \ J, disjoint_sdiff_right, hJ, hK.subset diff_subset, by simp⟩

lemma UnionIndep.subset (h : M.UnionIndep N J) (hIJ : I ⊆ J) : M.UnionIndep N I := by
  sorry

/-- There exists a pair of matroids with no union -/
theorem exists_no_union : ∃ (α : Type) (M N : Matroid α) (hMN : M.E = N.E),
  ∀ I, ¬ Maximal (M.UnionIndep N) I := sorry

def parallelSum (E : Set α) : Matroid (α ⊕ α) :=
    Matroid.disjointSigma (fun x : E ↦ unifOn {.inl x.1, .inr x.1} 1) (by simp [Pairwise, eq_comm])

@[simp]
lemma parallelSum_ground (E : Set α) : (parallelSum E).E = Sum.inl '' E ∪ Sum.inr '' E := by
  grind [parallelSum, disjointSigma_ground_eq, unifOn_ground_eq, iUnion_coe_set, mem_iUnion]

@[simp]
lemma parallelSum_indep_iff {I : Set (α ⊕ α)} : (parallelSum E).Indep I ↔
    Disjoint (.inl ⁻¹' I) (.inr ⁻¹' I) ∧ .inl ⁻¹' I ⊆ E ∧ .inr ⁻¹' I ⊆ E := by
  simp only [parallelSum, disjointSigma_indep_iff, unifOn_ground_eq, unifOn_indep_iff, Nat.cast_one,
    inter_subset_right, and_true, Subtype.forall, iUnion_coe_set, disjoint_left, mem_preimage]
  refine ⟨fun ⟨h1, h2⟩ ↦ ⟨fun a ha1 ha2 ↦ ?_, ?_⟩, fun ⟨h1, h2, h3⟩ ↦ ⟨fun a haE ↦ ?_, ?_⟩⟩
  · specialize h1 a (by simpa using h2 ha1)
    rw [inter_eq_self_of_subset_right (by grind), encard_pair (by simp)] at h1
    simp at h1
  · grw [h2]
    grind [preimage_iUnion, iUnion_subset_iff]
  · by_cases ha : .inl a ∈ I
    · rw [inter_insert_of_mem ha, inter_singleton_of_notMem (h1 ha), insert_empty_eq,
        encard_singleton]
    grw [inter_comm, insert_inter_of_notMem ha, inter_subset_left, encard_singleton]
  nth_grw 1 [← I.image_preimage_inl_union_image_preimage_inr, h2, h3,
    ← biUnion_congr (fun _ _ ↦ union_singleton ..), ← biUnion_of_singleton E,
    image_iUnion₂, union_comm, ← biUnion_of_singleton E, image_iUnion₂, ← iUnion_union_distrib]
  simp

@[simp]
lemma parallelSum_closure {X : Set (α ⊕ α)} (hX : X ⊆ (parallelSum E).E) :
    (parallelSum E).closure X = Sum.inl '' (Sum.inl ⁻¹' X ∪ Sum.inr ⁻¹' X)
        ∪ Sum.inr '' (Sum.inl ⁻¹' X ∪ Sum.inr ⁻¹' X) := by
  rw [parallelSum, disjointSigma_closure]
  simp_rw [closure_inter_ground, subset_antisymm_iff]
  sorry


    -- Disjoint (.inl ⁻¹' I) (.inr ⁻¹' I) ∧ .inl ⁻¹' I ⊆ E ∧ .inr ⁻¹' I ⊆ E := by

def MatroidIntersectionConjecture (M N : Matroid α) : Prop := M.E = N.E →
    ∃ (I J : Set α), Disjoint I J ∧ M.Indep (I ∪ J) ∧ N.Indep (I ∪ J) ∧
    M.closure I ∪ N.closure J = M.E

theorem foo (M N : Matroid α) (hME : M.E = E) (hNE : N.E = E) {I J : Set (α ⊕ α)}
    (hIJ : Disjoint I J) (hIJi : (M.sum N).Indep (I ∪ J)) (hIJpi : (parallelSum E).Indep (I ∪ J))
    (hcl : (M.sum N).closure I ∪ (parallelSum E).closure J = (M.sum N).E) :
    Maximal (M.UnionIndep N) (.inl ⁻¹' (I ∪ J) ∪ .inr ⁻¹' (I ∪ J)) := by
  refine (maximal_iff_forall_insert (fun _ _ ↦ UnionIndep.subset)).2 ⟨?_, fun x hx hxi ↦ ?_⟩
  -- refine maximal_subset_iff'.2 ⟨?_, fun U hU hUss ↦ ?_⟩
  · simp only [sum_indep_iff, preimage_union] at hIJi
    exact hIJi.1.unionIndep hIJi.2
  rw [sum_indep_iff] at hIJi

  rw [sum_closure_eq, parallelSum_closure (hIJpi.subset subset_union_right).subset_ground] at hcl
  simp_rw [parallelSum_indep_iff, preimage_union, disjoint_union_left, disjoint_union_right,
    union_subset_iff] at hIJpi
  simp_rw [preimage_union, image_union] at *
  set I0 := Sum.inl ⁻¹' I
  set I1 := Sum.inr ⁻¹' I
  set J0 := Sum.inl ⁻¹' J
  set J1 := Sum.inr ⁻¹' J
  rw [sum_ground, hME, hNE, union_assoc, union_comm (Sum.inr '' _), ← union_assoc,
    ← image_union, ← union_assoc, ← image_union, ← image_union, union_assoc, ← image_union] at hcl
  have hcl0 : M.closure I0 ∪ (J0 ∪ J1) = E := by simpa using congr_arg (Sum.inl ⁻¹' ·) hcl
  have hcl1 : N.closure I1 ∪ (J0 ∪ J1) = E := by
    simpa [union_comm (J0 ∪ J1)] using congr_arg (Sum.inr ⁻¹' ·) hcl
  clear hcl


  obtain ⟨P, Q, hPQ, hP, hQ, rfl⟩ := hU.exists

  rintro e (heP | heQ)
  · rw [sum_indep_iff, preimage_union] at hIJi
    rw [sum_closure_eq] at hcl
    sorry
  sorry

    -- rw [preimage_union, preimage_union]
  -- refine ⟨⟨hIJi, hIJpi⟩, ?_⟩

theorem matroidIntersectionConjecture_false : ∃ (α : Type) (M N : Matroid α),
    ¬ MatroidIntersectionConjecture M N := by
  obtain ⟨α, M, N, hE, h⟩ := exists_no_union
  refine ⟨α ⊕ α, M.sum N, parallelSum M.E, fun hc ↦ ?_⟩
  obtain ⟨I, J, hIJ, hi1, hi2, hcl⟩ := hc (by simp [hE])
  exact h _ <| foo (M := M) (N := N) (E := M.E) rfl hE.symm hIJ hi1 hi2 hcl
