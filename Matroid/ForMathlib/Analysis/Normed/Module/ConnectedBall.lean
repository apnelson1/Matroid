module

public import Mathlib.Analysis.Normed.Module.Connected

/-!
# Connectedness of the complement of a ball

In a real normed space of rank at least two, the complement of a closed ball is path connected.
This is where the dimension enters: in rank one the complement of a ball falls apart.

## Main statements

* `isPathConnected_compl_closedBall`, and the `isConnected` / `isPreconnected` forms.

The complement of a closed ball is the union of the spheres of radius `> r`, each path connected
by `isPathConnected_sphere` and each meeting a fixed ray; that union is realised here as the image
of `sphere 0 1 ×ˢ Ioi r` under `(u, t) ↦ x + t • u`.

Mathlib's home for these is `Mathlib/Analysis/Normed/Module/Connected.lean`, beside the sphere
lemmas they are proved from. They are not in this repo's
`Matroid/ForMathlib/Analysis/Normed/Module/Connected.lean` because that file is a *fork* of the
Mathlib module: it re-declares `isPathConnected_sphere`, `isPreconnected_sphere` and their
neighbours at their Mathlib names without importing Mathlib's copy. Importing both is not
rejected — Lean silently resolves those names to Mathlib's — so a file that drags the fork onto
downstream modules makes which copy they see a property of the import graph rather than of
anything written down. Fold this file into that one when the fork is rebased onto Mathlib's.
-/

@[expose] public section

open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- In a real normed space of rank at least two, the complement of a closed ball is
path connected. -/
theorem isPathConnected_compl_closedBall (h : 1 < Module.rank ℝ E) (x : E) (r : ℝ) :
    IsPathConnected (closedBall x r)ᶜ := by
  obtain hr | hr := lt_or_ge r 0
  · simpa [closedBall_eq_empty.2 hr] using isPathConnected_univ
  let f : E × ℝ → E := fun p ↦ x + p.2 • p.1
  have hpc : IsPathConnected (sphere (0 : E) 1 ×ˢ Ioi r) :=
    (isPathConnected_sphere h 0 zero_le_one).prod <| (convex_Ioi r).isPathConnected ⟨r + 1, by simp⟩
  refine (show f '' (sphere (0 : E) 1 ×ˢ Ioi r) = (closedBall x r)ᶜ from ?_) ▸
    hpc.image (by fun_prop : Continuous f)
  ext y
  refine ⟨?_, fun hy ↦ ?_⟩
  · rintro ⟨⟨u, t⟩, hUT, rfl⟩
    obtain ⟨hu : ‖u‖ = 1, ht : r < t⟩ := by simpa [mem_sphere_zero_iff_norm, mem_Ioi] using hUT
    rw [mem_compl_iff, mem_closedBall, dist_eq_norm, show f (u, t) = x + t • u from rfl,
      add_sub_cancel_left, norm_smul, hu, mul_one, Real.norm_of_nonneg (hr.trans ht.le)]
    exact not_le_of_gt ht
  rw [mem_compl_iff, mem_closedBall, dist_eq_norm, not_le] at hy
  have hy0 : ‖y - x‖ ≠ 0 := (hr.trans_lt hy).ne'
  refine ⟨(‖y - x‖⁻¹ • (y - x), ‖y - x‖), ⟨?_, hy⟩, ?_⟩
  · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Real.norm_of_nonneg (norm_nonneg _),
      inv_mul_cancel₀ hy0]
  unfold f
  rw [smul_smul, mul_inv_cancel₀ hy0, one_smul, add_sub_cancel]

/-- In a real normed space of rank at least two, the complement of a closed ball is connected. -/
theorem isConnected_compl_closedBall (h : 1 < Module.rank ℝ E) (x : E) (r : ℝ) :
    IsConnected (closedBall x r)ᶜ := (isPathConnected_compl_closedBall h x r).isConnected

/-- In a real normed space of rank at least two, the complement of a closed ball is
preconnected. -/
theorem isPreconnected_compl_closedBall (h : 1 < Module.rank ℝ E) (x : E) (r : ℝ) :
    IsPreconnected (closedBall x r)ᶜ := (isConnected_compl_closedBall h x r).isPreconnected

end
