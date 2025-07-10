import Matroid.Connectivity.Local
import Mathlib.Data.Set.Prod

open Set Function

namespace Matroid

variable {α : Type*} {M : Matroid α} {B B' I I' J J' K X Y : Set α} {ι : Type*}

/-- An auxiliary version of multi-connectivity used in the real definition.
If the sets are disjoint, then this is equal to `multiConn`, but otherwise it is badly behaved.-/
private noncomputable def multiConnAux (M : Matroid α) (X : ι → Set α) : ℕ∞ :=
  ⨅ (I : {I : ι → Set α // ∀ i, M.IsBasis' (I i) (X i)}), M.nullity (⋃ i, I.1 i)

private lemma multiConnAux_eq_nullity_iUnion (M : Matroid α) {I X : ι → Set α}
    (hI : ∀ i, M.IsBasis' (I i) (X i)) (hdj : Pairwise (Disjoint on X)) :
    M.multiConnAux X = M.nullity (⋃ i, I i) := by
  have aux (J : ι → Set α) (hJ : ∀ i, M.IsBasis' (J i) (X i)) :
      M.nullity (⋃ i, J i) = M.nullity (⋃ i, I i) := by
    rw [nullity_iUnion_congr (Y := I)
      (hdj.mono fun i j ↦ Disjoint.mono (hJ i).subset (hJ j).subset)
      (hdj.mono fun i j ↦ Disjoint.mono (hI i).subset (hI j).subset)
      (fun i ↦ by rw [(hI i).indep.nullity_eq, (hJ i).indep.nullity_eq])
      (fun i ↦ by rw [(hI i).closure_eq_closure, (hJ i).closure_eq_closure])]
  exact ((iInf_le _ ⟨I, hI⟩).trans (by simp)).antisymm <| by simpa using fun i h ↦ (aux i h).symm.le

/-- The local connectivity of an indexed collection `X : ι → Set α` of sets.
This is defined indirectly using comaps so that it is meaningful even when the `X` are not disjoint.
If they are disjoint, it is equal to `M.nullity (⋃ i, I i)` for any bases `I i` for the `X i`;
see `multiConn_eq_nullity_iUnion`.
If the `X i` are not disjoint, then there is no simple formula in general, but for pairs,
an expression using cardinality is given in `multiConn_cond`. -/
noncomputable def multiConn (M : Matroid α) (X : ι → Set α) : ℕ∞ :=
  (M.comap Prod.fst).multiConnAux fun i ↦ ((· , i) '' (X i))

lemma multiConn_eq_nullity_iUnion (M : Matroid α) (X I : ι → Set α) (hdj : Pairwise (Disjoint on X))
    (hIX : ∀ i, M.IsBasis' (I i) (X i)) : M.multiConn X = M.nullity (⋃ i, I i) := by
  have hinj : InjOn Prod.fst (⋃ i, (·, i) '' I i) := by
    rintro ⟨x, i⟩ hx ⟨y, j⟩ hy (rfl : x = y)
    exact Prod.mk_inj.2 ⟨rfl, hdj.eq <| not_disjoint_iff.2
      ⟨x, (hIX i).subset (by simpa using hx), (hIX j).subset (by simpa using hy)⟩⟩
  have aux {i : ι} {Y : Set α} : Prod.fst '' ((· , i) '' Y) = Y := by simp [Set.ext_iff]
  have hbas (i : ι) :
      (M.comap Prod.fst).IsBasis' ((Prod.mk · i) '' (I i)) ((Prod.mk · i) '' (X i)) := by
    rw [comap_isBasis'_iff, and_iff_left (image_subset _ (hIX i).subset), aux,
      aux, and_iff_right (hIX i)]
    simp [InjOn]
  rw [multiConn, multiConnAux_eq_nullity_iUnion _ hbas, nullity_comap _ _ hinj, image_iUnion]
  · simp [aux]
  simp +contextual [Pairwise, Function.onFun, disjoint_right]

/-- The local connectivity of a pair of sets `X,Y` is the nullity of `I ∪ J` plus the
cardinality of `I ∩ J`, for any respective bases `I` and `J` for `X` and `Y`. -/
lemma multiConn_cond (M : Matroid α) (hIX : M.IsBasis' I X) (hJY : M.IsBasis' J Y) :
    M.multiConn (fun b ↦ bif b then X else Y) = M.nullity (I ∪ J) + (I ∩ J).encard := by
  have aux_dj {A B : Set α} : Disjoint
    ((·, true) '' A) ((·, false) '' B) := by simp [disjoint_left]
  have aux {i : Bool} {Y : Set α} : Prod.fst '' ((· , i) '' Y) = Y := by simp [Set.ext_iff]
  have hb (b : Bool) : (M.comap Prod.fst).IsBasis' ((· , b) '' (bif b then I else J))
      ((· , b) '' (bif b then X else Y)) := by
    refine comap_isBasis'_iff.2 ⟨?_, by simp [InjOn], image_subset _ ?_ ⟩
    · obtain rfl | rfl := b
      · convert hJY <;> simp [Set.ext_iff]
      convert hIX <;> simp [Set.ext_iff]
    obtain rfl | rfl := b
    · exact hJY.subset
    exact hIX.subset
  have hi : (M.comap Prod.fst).Indep ((fun x ↦ (x, true)) '' I) := by simp [aux, hIX.indep, InjOn]
  have hrw : I ∪ J = Prod.fst '' ((fun x ↦ (x, true)) '' I ∪ (fun x ↦ (x, false)) '' (J \ I)) := by
    suffices ∀ x, x ∈ I ∨ x ∈ J ↔ x ∈ J ∧ x ∉ I ∨ x ∈ I by simpa [Set.ext_iff]
    tauto
  rw [multiConn, multiConnAux_eq_nullity_iUnion _ hb]
  · simp only [iUnion_bool, cond_true, cond_false]
    rw [← hi.nullity_project_of_disjoint aux_dj,
      nullity_eq_nullity_add_encard_diff (X := (·, false) '' (J \ I))
        (image_subset _ (diff_subset)),
      hi.nullity_project_of_disjoint aux_dj, nullity_comap, ← image_diff (by simp [Injective]),
      ← hrw, (Prod.mk_left_injective _).encard_image]
    · simp [inter_comm]
    · suffices ∀ a, (a ∈ J → a ∉ I → ∀ b ∈ I, ¬a = b) ∧ (a ∈ I → ∀ b ∈ J, b ∉ I → ¬a = b)
        by simpa [InjOn]
      aesop
    · simp only [project_closure, comap_closure_eq, image_subset_iff]
      rw [← union_comm, ← hrw]
      simp only [subset_def, mem_preimage]
      exact fun x hx ↦ M.subset_closure_of_subset' subset_union_right hJY.indep.subset_ground hx
  simp [Pairwise, pairwise_on_bool, Function.onFun, aux_dj, aux_dj.symm]
