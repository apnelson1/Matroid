import Mathlib.Combinatorics.Matroid.Closure -- inefficient import
import Matroid.ForMathlib.Matroid.Dual

namespace Matroid

open Set

variable {α : Type*} {M : Matroid α} {X Y : Set α} {e : α}


lemma compl_bijOn_coindep : BijOn (M.E \ ·) {S | M.Spanning S} {I | M.Coindep I} := by
  refine ⟨fun S ↦ Spanning.compl_coindep, ?_, fun I hI ↦ ⟨M.E \ I, Coindep.compl_spanning hI, ?_⟩⟩
  · exact (diff_bijOn_subset M.E).injOn.mono fun _ ↦ Spanning.subset_ground
  simp [Coindep.subset_ground hI]

lemma closure_eq_ground (M : Matroid α) {X : Set α} (hX : M.E ⊆ X) : M.closure X = M.E := by
  rw [← closure_inter_ground, Set.inter_eq_self_of_subset_right hX, closure_ground]

@[simp]
lemma closure_ground_union_left (M : Matroid α) {X : Set α} : M.closure (M.E ∪ X) = M.E := by
  rw [M.closure_eq_ground Set.subset_union_left]

@[simp]
lemma closure_ground_union_right (M : Matroid α) {X : Set α} : M.closure (X ∪ M.E) = M.E := by
  rw [M.closure_eq_ground Set.subset_union_right]

/-- `M.Nonspanning X` means that `X` is a subset of `M.E` that is not `Spanning`. -/
@[mk_iff]
structure Nonspanning (M : Matroid α) (X : Set α) : Prop where
  not_spanning : ¬ M.Spanning X
  subset_ground : X ⊆ M.E

attribute [aesop unsafe 20% (rule_sets := [Matroid])] Nonspanning.subset_ground

lemma nonspanning_dual_iff (hXE : X ⊆ M.E := by aesop_mat) :
    M✶.Nonspanning X ↔ M.Dep (M.E \ X) := by
  rw [nonspanning_iff, spanning_iff_compl_coindep, dual_coindep_iff, not_indep_iff, dual_ground,
    and_iff_left hXE]

lemma nonspanning_compl_dual_iff (hXE : X ⊆ M.E := by aesop_mat) :
    M✶.Nonspanning (M.E \ X) ↔ M.Dep X := by
  rw [nonspanning_dual_iff, diff_diff_cancel_left hXE]

lemma Nonspanning.closure_nonspanning (h : M.Nonspanning X) : M.Nonspanning (M.closure X) := by
  rw [nonspanning_iff, closure_spanning_iff, and_iff_left <| M.closure_subset_ground ..]
  exact h.not_spanning

lemma codep_compl_iff (hXE : X ⊆ M.E := by aesop_mat) :
    M.Codep (M.E \ X) ↔ M.Nonspanning X := by
  rw [← M.dual_dual, nonspanning_dual_iff, dual_dual, dep_dual_iff, dual_ground]

lemma Nonspanning.codep_compl (h : M.Nonspanning X) : M.Codep (M.E \ X) := by
  rwa [codep_compl_iff]

lemma nonspanning_compl_iff (hXE : X ⊆ M.E := by aesop_mat) :
    M.Nonspanning (M.E \ X) ↔ M.Codep X := by
  rw [← M.dual_dual, nonspanning_dual_iff, dual_ground, dual_ground, dual_dual, dep_dual_iff,
    dual_ground, diff_diff_cancel_left hXE]

lemma Codep.nonspanning_compl (h : M.Codep X) : M.Nonspanning (M.E \ X) := by
  rwa [nonspanning_compl_iff]

lemma Nonspanning.subset (h : M.Nonspanning X) (hYX : Y ⊆ X) : M.Nonspanning Y :=
  ⟨fun hY ↦ h.not_spanning (hY.superset hYX), hYX.trans h.subset_ground⟩

lemma not_nonspanning_iff (hXE : X ⊆ M.E := by aesop_mat) :
    ¬ M.Nonspanning X ↔ M.Spanning X := by
  rw [nonspanning_iff, and_iff_left hXE, not_not]

lemma not_spanning_iff (hXE : X ⊆ M.E := by aesop_mat) :
    ¬ M.Spanning X ↔ M.Nonspanning X := by
  rw [nonspanning_iff, and_iff_left hXE]

lemma nonspanning_closure_iff (hXE : X ⊆ M.E := by aesop_mat) :
    M.Nonspanning (M.closure X) ↔ M.Nonspanning X := by
  rw [nonspanning_iff, closure_spanning_iff, and_iff_left (M.closure_subset_ground ..),
    not_spanning_iff]

lemma spanning_or_nonspanning (M : Matroid α) (X : Set α) (hXE : X ⊆ M.E := by aesop_mat) :
    M.Spanning X ∨ M.Nonspanning X := by
  rw [← not_spanning_iff]
  apply em

@[simp]
lemma compl_not_spanning_iff : ¬ M.Spanning (M.E \ X) ↔ M.Nonspanning (M.E \ X) := by
  rw [not_spanning_iff]

@[simp]
lemma compl_not_nonspanning_iff : ¬ M.Nonspanning (M.E \ X) ↔ M.Spanning (M.E \ X) := by
  rw [not_nonspanning_iff]

lemma Spanning.insert_dep (h : M.Spanning X) (heX : e ∉ X) (heE : e ∈ M.E) :
    M.Dep (insert e X) := by
  obtain ⟨B, hB, hBX⟩ := h.exists_isBase_subset
  exact (hB.insert_dep ⟨heE, notMem_subset hBX heX⟩).superset <| insert_subset_insert hBX

lemma Spanning.dep_of_ssuperset (h : M.Spanning X) (hssu : X ⊂ Y) (hY : Y ⊆ M.E := by aesop_mat) :
    M.Dep Y := by
  obtain ⟨B, hB, hBX⟩ := h.exists_isBase_subset
  exact hB.dep_of_ssubset (hBX.trans_ssubset hssu)

lemma IsRestriction.closure_eq' {N : Matroid α} (hNM : N ≤r M) (X : Set α) :
    N.closure X = M.closure (X ∩ N.E) ∩ N.E := by
  obtain ⟨R, hR, rfl⟩ := hNM
  simp [diff_eq_empty.2 hR]

lemma IsRestriction.closure_eq {N : Matroid α} (hNM : N ≤r M)
    (hX : X ⊆ N.E := by aesop_mat) : N.closure X = M.closure X ∩ N.E := by
  rw [hNM.closure_eq', inter_eq_self_of_subset_left hX]
-- lemma closure_iUnion_closure_eq_closure_iUnion'

-- lemma closure_iUnion_congr' {α : Type*} {ι : Sort*} {κ : ι → Sort*} (M : Matroid α)
--     {X Y : (i : ι) → κ i → Set α}
--     (hXY : ∀ i (j : κ i), M.closure (X i j) = M.closure (Y i j)) :
--     M.closure (⋃ i, ⋃ j, X i j) = M.closure (⋃ i, ⋃ j, Y i j) :=
--   M.closure_iUnion_congr _ _ fun i ↦ M.closure_iUnion_congr _ _ fun j ↦ hXY i j

-- lemma closure_iUnion₂_congr {α : Type*} {ι : Sort*} {κ : ι → Sort*} (M : Matroid α)
--     {X Y : (i : ι) → κ i → Set α}
--     (hXY : ∀ i (j : κ i), M.closure (X i j) = M.closure (Y i j)) :
--     M.closure (⋃ i, ⋃ j, X i j) = M.closure (⋃ i, ⋃ j, Y i j) := by
--   rw [← closure_iUnion_closure_eq_closure_iUnion]
  -- M.closure_iUnion_congr _ _ fun i ↦ M.closure_iUnion_congr _ _ fun j ↦ hXY i j
