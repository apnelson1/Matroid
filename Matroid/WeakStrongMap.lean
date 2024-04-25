import Matroid.Minor.RelRank
import Matroid.ForMathlib.PartialEquiv

open Set

namespace Matroid

variable {α β γ : Type*} {M : Matroid α} {N : Matroid β} {R : Matroid γ} {e : PartialEquiv α β}

section WeakMap

/-- A `PartialEquiv` is a weak map from `M` to `N` if the preimage of every independent set is
  independent-/
structure IsWeakMap (e : PartialEquiv α β) (M : Matroid α) (N : Matroid β) : Prop :=
  (source_eq : e.source = M.E)
  (target_eq : e.target = N.E)
  (symm_image_indep : ∀ ⦃I⦄, N.Indep I → M.Indep (e.symm '' I))

theorem IsWeakMap.subset_source (h : IsWeakMap e M N) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    X ⊆ e.source :=
  hX.trans (h.source_eq.symm.subset)

theorem IsWeakMap.subset_target (h : IsWeakMap e M N) (X : Set β) (hX : X ⊆ N.E := by aesop_mat) :
    X ⊆ e.target :=
  hX.trans (h.target_eq.symm.subset)

theorem IsWeakMap.dep_of_dep (h : IsWeakMap e M N) {D : Set α} (hD : M.Dep D) : N.Dep (e '' D) := by
  rw [dep_iff, ← h.target_eq]
  refine ⟨fun hi ↦ hD.not_indep ?_, e.image_subset_target (h.subset_source D)⟩
  replace hi := h.symm_image_indep hi
  rwa [e.symm_image_image_of_subset_source (h.subset_source D)] at hi

theorem isWeakMap_iff_dep_of_dep_forall : IsWeakMap e M N ↔ ∀ {D}, M.Dep D → N.Dep (e '' D) := by
  _

structure WeakMap (M : Matroid α) (N : Matroid β) where
  (toPartialEquiv : PartialEquiv α β)
  (weakMap : IsWeakMap toPartialEquiv M N)

theorem IsWeakMap.trans {e : PartialEquiv α β} {e' : PartialEquiv β γ} (he : IsWeakMap e M N)
    (he' : IsWeakMap e' N R) : IsWeakMap (e.trans e') M R where
  source_eq := by
    rw [e.trans_source, ← he.source_eq, he'.source_eq, ← he.target_eq, inter_eq_left]
    exact e.source_subset_preimage_target
  target_eq := by
    rw [e.trans_target, ← he'.target_eq, inter_eq_left, he.target_eq, ← he'.source_eq]
    exact e'.target_subset_preimage_source
  symm_image_indep := by
    intro I hI
    replace hI := he.symm_image_indep <| he'.symm_image_indep hI
    rw [image_image] at hI
    rwa [PartialEquiv.trans_symm_eq_symm_trans_symm]

def WeakMap.trans (e : WeakMap M N) (f : WeakMap N R) : WeakMap M R where
  toPartialEquiv := e.toPartialEquiv.trans f.toPartialEquiv
  weakMap := e.weakMap.trans f.weakMap

def WeakLE (M N : Matroid α) := IsWeakMap (PartialEquiv.refl _) M N

infixl:50 " ≤w " => Matroid.WeakLE

-- theorem WeakLE.trans



end WeakMap
