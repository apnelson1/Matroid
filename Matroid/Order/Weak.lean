import Matroid.Minor.Rank
import Matroid.Flat.Hyperplane

universe u

open Set
namespace Matroid

variable {α : Type*} {M N M₁ M₂ : Matroid α} {X Y F : Set α}

section Weak

variable {I B D : Set α}

@[mk_iff]
structure WeakLE (N M : Matroid α) : Prop where
  forall_indep_of_indep : ∀ I, N.Indep I → M.Indep I
  ground_eq : N.E = M.E

infixl:50 " ≤w " => Matroid.WeakLE

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma WeakLE.subset_ground_of_subset_ground_left (h : N ≤w M) (hX : X ⊆ N.E := by aesop_mat) :
    X ⊆ M.E :=
  hX.trans h.ground_eq.subset

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma WeakLE.subset_ground_of_subset_ground_right (h : N ≤w M) (hX : X ⊆ M.E := by aesop_mat) :
    X ⊆ N.E :=
  hX.trans h.ground_eq.symm.subset

lemma WeakLE.indep_of_indep (h : N ≤w M) (hI : N.Indep I) : M.Indep I :=
  h.forall_indep_of_indep _ hI

lemma WeakLE.dep_of_dep (h : N ≤w M) (hD : M.Dep D) : N.Dep D := by
  have hIN := h.subset_ground_of_subset_ground_right hD.subset_ground
  contrapose! hD
  rw [not_dep_iff] at hD ⊢
  exact h.indep_of_indep hD

lemma weakLE_iff_forall_dep_of_dep : N ≤w M ↔ N.E = M.E ∧ ∀ D, M.Dep D → N.Dep D := by
  refine ⟨fun h ↦ ⟨h.ground_eq, fun _ ↦ h.dep_of_dep⟩, fun h ↦ ⟨fun D hD ↦ ?_, h.1⟩⟩
  have hDN : D ⊆ N.E := hD.subset_ground
  have hDM : D ⊆ M.E := hDN.trans_eq h.1
  contrapose! hD
  rw [not_indep_iff] at hD ⊢
  exact h.2 _ hD

lemma WeakLE.refl (M : Matroid α) : M ≤w M where
  forall_indep_of_indep := by simp
  ground_eq := rfl

lemma WeakLE.antisymm (h : N ≤w M) (h' : M ≤w N) : N = M :=
  ext_indep h.ground_eq fun _ _ ↦ ⟨h.indep_of_indep, h'.indep_of_indep⟩

lemma WeakLE.trans {M₁ M₂ M₃ : Matroid α} (h : M₁ ≤w M₂) (h' : M₂ ≤w M₃) : M₁ ≤w M₃ where
  forall_indep_of_indep _ := h'.indep_of_indep ∘ h.indep_of_indep
  ground_eq := h.ground_eq.trans h'.ground_eq

lemma WeakLE.delete (h : N ≤w M) (D : Set α) : N ＼ D ≤w M ＼ D := by
  suffices ∀ (I : Set α), N.Indep I → Disjoint I D → M.Indep I by
    simpa (config := { contextual := true }) [weakLE_iff, h.ground_eq]
  exact fun I hI _ ↦ h.indep_of_indep hI

lemma contract_weakLE_delete (M : Matroid α) (X : Set α) : M ／ X ≤w M ＼ X := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  rw [hI.contract_eq_contract_delete]
  simp only [weakLE_iff, delete_indep_iff, hI.indep.contract_indep_iff, and_imp, delete_ground,
    contract_ground, diff_diff, union_diff_self, union_eq_self_of_subset_left hI.subset, and_true]
  refine fun J hJI hi hJ'  ↦ ⟨hi.subset subset_union_left, ?_⟩
  simpa only [diff_union_self, disjoint_union_right, and_iff_left hJI] using hJ'.union_right hJI

end Weak
