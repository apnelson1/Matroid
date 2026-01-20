import Mathlib.Combinatorics.Matroid.Closure -- inefficient import
import Matroid.ForMathlib.Matroid.Closure

variable {α : Type*} {M N : Matroid α} {X : Set α}

open Set

namespace Matroid

lemma coindep_iff_subset_closure_compl : M.Coindep X ↔ X ⊆ M.closure (M.E \ X) := by
  by_cases hXE : X ⊆ M.E
  · rw [coindep_iff_compl_spanning, spanning_iff, and_iff_left diff_subset]
    refine ⟨fun h ↦ by rwa [h], fun h ↦ ?_⟩
    nth_grw 1 [subset_antisymm_iff, and_iff_right (M.closure_subset_ground ..),
      ← diff_union_of_subset hXE, union_subset_iff, and_iff_left h, ← M.subset_closure (M.E \ X)]
  exact iff_of_false (fun h ↦ hXE h.subset_ground)
    (fun h ↦ hXE (h.trans (M.closure_subset_ground ..)))

lemma Spanning.rankFinite_of_finite {S : Set α} (hS : M.Spanning S) (hSfin : S.Finite) :
    M.RankFinite := by
  obtain ⟨B, hB⟩ := hS.exists_isBase_subset
  refine hB.1.rankFinite_of_finite <| hSfin.subset hB.2

lemma IsRestriction.closure_subset_closure {M N : Matroid α} (h : M ≤r N) (X : Set α) :
    M.closure X ⊆ N.closure X := by
  obtain ⟨R, h', rfl⟩ := h.exists_eq_restrict
  grw [← closure_inter_ground, restrict_closure_eq _, inter_subset_left]
  · exact closure_mono _ inter_subset_left
  exact inter_subset_right

lemma spanning_empty_iff_eq_loopyOn : M.Spanning ∅ ↔ ∃ E, M = loopyOn E := by
  refine ⟨fun h ↦ ⟨M.E, ?_⟩, ?_⟩
  · exact empty_isBase_iff.1 (M.empty_indep.isBase_of_spanning h)
  rintro ⟨E, rfl⟩
  simp only [loopyOn_spanning_iff, empty_subset]

lemma spanning_empty_iff : M.Spanning ∅ ↔ M = loopyOn M.E := by
  rw [spanning_empty_iff_eq_loopyOn]
  refine ⟨?_, fun h ↦ ⟨M.E, h⟩⟩
  rintro ⟨E, rfl⟩
  rfl

lemma spanning_dual_iff  (hXE : X ⊆ M.E := by aesop_mat) :
    M✶.Spanning X ↔ M.Indep (M.E \ X) := by
  rw [spanning_iff_compl_coindep, dual_coindep_iff, dual_ground]

lemma spanning_compl_dual_iff (hXE : X ⊆ M.E := by aesop_mat) :
    M✶.Spanning (M.E \ X) ↔ M.Indep X := by
  rw [spanning_iff_compl_coindep, dual_coindep_iff, dual_ground, diff_diff_cancel_left hXE]

@[mk_iff]
structure IsSpanningRestriction (N M : Matroid α) : Prop where
  isRestriction : N ≤r M
  spanning : M.Spanning N.E

scoped infix:50  " ≤sr " => IsSpanningRestriction

lemma IsSpanningRestriction.subset (h : N ≤sr M) : N.E ⊆ M.E :=
  h.isRestriction.subset

lemma IsSpanningRestriction.refl : M.IsSpanningRestriction M :=
  ⟨IsRestriction.refl, M.ground_spanning⟩

lemma IsSpanningRestriction.spanning_of_spanning (h : N ≤sr M) (hX : N.Spanning X) :
    M.Spanning X := by
  grw [spanning_iff_ground_subset_closure (hX.subset_ground.trans h.subset),
    ← h.spanning.closure_eq, closure_subset_closure_iff_subset_closure h.subset,
    ← h.isRestriction.closure_subset_closure, hX.closure_eq]

lemma IsSpanningRestriction.spanning_iff (h : N ≤sr M) : N.Spanning X ↔ M.Spanning X ∧ X ⊆ N.E := by
  refine ⟨fun h' ↦ ⟨h.spanning_of_spanning h', h'.subset_ground⟩, fun h' ↦ ?_⟩
  grw [spanning_iff_ground_subset_closure, h.isRestriction.closure_eq, h'.1.closure_eq,
    ← h.subset, inter_self]

lemma IsSpanningRestriction.trans {M₁ M₂ M₃ : Matroid α} (h : M₁ ≤sr M₂) (h' : M₂ ≤sr M₃) :
    M₁ ≤sr M₃ :=
  ⟨h.isRestriction.trans h'.isRestriction,
    h'.spanning_of_spanning <| h.spanning_of_spanning M₁.ground_spanning⟩

@[simp]
lemma restrict_isSpanningRestriction_iff : (M ↾ X) ≤sr M ↔ M.Spanning X :=
  ⟨fun h ↦ by simpa using h.spanning, fun h ↦ ⟨restrict_isRestriction .., h⟩⟩

lemma Spanning.restrict_isSpanningRestriction (h : M.Spanning X) : M ↾ X ≤sr M := by
  simpa


-- lemma Coindep.delete_isSpanningRestriction (h : M.Coindep X) : M ＼ X →

  -- grw [spanning_iff_ground_subset_closure (h.subset.trans h'.subset), ← h'.spanning.closure_eq,
  --   closure_subset_closure_iff_subset_closure h'.subset, ← h.spanning.closure_eq,
  --   h'.isRestriction.closure_subset_closure]

-- lemma nonspanning_dual_iff (hXE : X ⊆ M.E := by aesop_mat) :
--     M✶.Nonspanning X ↔ M.Dep (M.E \ X) := by
--   rw []
