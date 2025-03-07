import Mathlib.Data.Matroid.Closure

variable {α : Type*} {X Y : Set α} {M : Matroid α}

open Set

lemma Set.diff_diff_invOn_Iic (s : Set α) : InvOn (s \ ·) (s \ ·) (Iic s) (Iic s) :=
  ⟨fun t ht ↦ by simpa, fun t ht ↦ by simpa⟩

lemma Set.diff_bijOn_subset (s : Set α) : BijOn (s \ ·) (Iic s) (Iic s) :=
  s.diff_diff_invOn_Iic.bijOn (fun _ _ ↦ diff_subset) fun _ _ ↦ diff_subset

namespace Matroid

lemma compl_bijOn_coindep : BijOn (M.E \ ·) {S | M.Spanning S} {I | M.Coindep I} := by
  refine ⟨fun S ↦ Spanning.compl_coindep, ?_, fun I hI ↦ ⟨M.E \ I, Coindep.compl_spanning hI, ?_⟩⟩
  · exact (diff_bijOn_subset M.E).injOn.mono fun _ ↦ Spanning.subset_ground
  simp [Coindep.subset_ground hI]
