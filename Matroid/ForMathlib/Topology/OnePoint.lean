module

public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Local connectedness of the one-point compactification

Mathlib gives `OnePoint X` compactness, `T0`/`T1`, normality and connectedness, but not local
connectedness, which is what makes the components of an open set open — the property that turns
"connected component of the complement of a drawing" into "open face".

It is not automatic: `OnePoint ℤ` is a convergent sequence, which is locally connected nowhere near
`∞`. The obstruction is entirely at `∞`, whose neighbourhoods have a basis of sets `{∞} ∪ Kᶜ` with
`K` compact *and closed* — the topology on `OnePoint` asks for both, since it does not assume `X` is
Hausdorff. So the criterion below asks exactly that such a `K` can be enlarged to one whose
complement is preconnected.

Two details of the statement are forced, and both were wrong in the first version:

* `L` must be **closed** as well as compact, or `{∞} ∪ Lᶜ` need not be open;
* the complement must be asked to be **preconnected**, not connected. If `X` is itself compact then
  `L = X` is allowed and `Lᶜ` is empty, and `{∞}` is exactly the connected neighbourhood wanted;
  demanding `IsConnected` would make the hypothesis unsatisfiable in that case for no reason.

## Main statements

* `OnePoint.locallyConnectedSpace_of_forall_exists_isPreconnected_compl` : the criterion.
* `exists_isCompact_isClosed_isPreconnected_compl_euclidean` : its hypothesis for a Euclidean space
  of dimension at least two, where a closed ball large enough to swallow `K` has preconnected
  complement.
* the instance for `OnePoint (EuclideanSpace ℝ (Fin 2))` — the sphere `𝕊` on which the faces of a
  plane drawing are taken.
-/

@[expose] public section

open Set Topology

/-- The complement of a closed ball in a Euclidean space of dimension at least two is preconnected.
This is where the dimension enters: in dimension one the complement of a ball falls apart.

Mathlib has `isPathConnected_sphere` for `1 < Module.rank ℝ E`; the complement of a ball is the
union of the spheres of radius `> r`, each path connected and each meeting a fixed ray. -/
theorem isPreconnected_compl_closedBall_euclideanSpace {n : ℕ} (hn : 2 ≤ n)
    (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) : IsPreconnected (Metric.closedBall x r)ᶜ := by
  refine (IsPathConnected.isConnected ?_).isPreconnected
  rcases lt_or_ge r 0 with hr | hr
  · simpa [Metric.closedBall_eq_empty.2 hr] using isPathConnected_univ
  let f : EuclideanSpace ℝ (Fin n) × ℝ → EuclideanSpace ℝ (Fin n) := fun p ↦ x + p.2 • p.1
  have hpc : IsPathConnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ×ˢ Ioi r) :=
    have hrank : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin n)) :=
      Module.one_lt_rank_of_one_lt_finrank
        (by simpa [finrank_euclideanSpace_fin] using Nat.succ_le_iff.mp hn)
    (isPathConnected_sphere hrank 0 zero_le_one).prod <|
      (convex_Ioi r).isPathConnected ⟨r + 1, by simp⟩
  have himg : f '' (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1 ×ˢ Ioi r) =
      (Metric.closedBall x r)ᶜ := by
    ext y
    refine ⟨?_, fun hy ↦ ?_⟩
    · rintro ⟨⟨u, t⟩, hUT, rfl⟩
      obtain ⟨hu : ‖u‖ = 1, ht : r < t⟩ := by simpa [mem_sphere_zero_iff_norm, mem_Ioi] using hUT
      rw [mem_compl_iff, Metric.mem_closedBall, dist_eq_norm, show f (u, t) = x + t • u from rfl,
        add_sub_cancel_left, norm_smul, hu, mul_one, Real.norm_of_nonneg (hr.trans ht.le)]
      exact not_le_of_gt ht
    rw [mem_compl_iff, Metric.mem_closedBall, dist_eq_norm, not_le] at hy
    have hy0 : ‖y - x‖ ≠ 0 := (hr.trans_lt hy).ne'
    refine ⟨(‖y - x‖⁻¹ • (y - x), ‖y - x‖), ⟨?_, hy⟩, ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Real.norm_of_nonneg (norm_nonneg _),
        inv_mul_cancel₀ hy0]
    · dsimp [f]
      rw [smul_smul, mul_inv_cancel₀ hy0, one_smul, add_sub_cancel]
  exact himg ▸ hpc.image (by fun_prop : Continuous f)

/-- Every compact set in a Euclidean plane sits inside a closed ball, whose complement is
preconnected. This is the hypothesis of the criterion, in the only case the project needs. -/
theorem exists_isCompact_isClosed_isPreconnected_compl_euclidean
    (K : Set (EuclideanSpace ℝ (Fin 2))) (hK : IsCompact K) :
    ∃ L : Set (EuclideanSpace ℝ (Fin 2)), IsCompact L ∧ IsClosed L ∧ K ⊆ L ∧ IsPreconnected Lᶜ := by
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : EuclideanSpace ℝ (Fin 2))
  exact ⟨Metric.closedBall 0 r, isCompact_closedBall _ _, Metric.isClosed_closedBall, hr,
    isPreconnected_compl_closedBall_euclideanSpace le_rfl _ _⟩

namespace OnePoint

variable {X : Type*} [TopologicalSpace X]

/-- If every compact closed set is contained in a compact closed set with preconnected complement,
then the one-point compactification of a locally connected space is locally connected.

At a point of `X` this is local connectedness of `X` transported along the open embedding. At `∞` a
neighbourhood contains `{∞} ∪ Kᶜ` with `K` compact and closed, and `{∞} ∪ Lᶜ` for `L ⊇ K` as in the
hypothesis is an open connected neighbourhood inside it: open because `L` is compact and closed,
connected because `Lᶜ` is preconnected and `∞` lies in its closure whenever it is nonempty — every
neighbourhood of `∞` is the complement of a compact set, and no compact set is all of a noncompact
`X`. -/
theorem locallyConnectedSpace_of_forall_exists_isPreconnected_compl [LocallyConnectedSpace X]
    (h : ∀ K : Set X, IsCompact K → IsClosed K →
      ∃ L : Set X, IsCompact L ∧ IsClosed L ∧ K ⊆ L ∧ IsPreconnected Lᶜ) :
    LocallyConnectedSpace (OnePoint X) := by
  refine locallyConnectedSpace_iff_subsets_isOpen_isConnected.2 fun x U hU ↦ ?_
  induction x using OnePoint.rec with
  | coe x =>
    rw [nhds_coe_eq, Filter.mem_map] at hU
    obtain ⟨V, hVU, hVo, hxV, hVc⟩ :=
      locallyConnectedSpace_iff_subsets_isOpen_isConnected.1 ‹_› x _ hU
    exact ⟨(↑) '' V, image_subset_iff.mpr hVU, isOpen_image_coe.2 hVo, mem_image_of_mem _ hxV,
      hVc.image _ continuous_coe.continuousOn⟩
  | infty =>
    by_cases hX : CompactSpace X
    · refine ⟨{∞}, singleton_subset_iff.mpr (mem_of_mem_nhds hU), ?_, mem_singleton _,
        isConnected_singleton⟩
      simpa [← compl_range_coe] using
        (isClosed_image_coe.mpr ⟨isClosed_univ, isCompact_univ⟩).isOpen_compl
    replace hX : NoncompactSpace X := not_compactSpace_iff.mp hX
    obtain ⟨K, ⟨hKc, hKk⟩, hKU⟩ := hasBasis_nhds_infty.mem_iff.mp hU
    obtain ⟨L, hLk, hLc, hKL, hLp⟩ := h K hKk hKc
    let coeX : X → OnePoint X := (↑)
    refine ⟨(coeX '' Lᶜ) ∪ {∞}, union_subset ((image_mono <| compl_subset_compl.mpr hKL).trans <|
      subset_union_left.trans hKU) (singleton_subset_iff.mpr <| hKU (Or.inr rfl)),
      compl_image_coe L ▸ isOpen_compl_image_coe.mpr ⟨hLc, hLk⟩, by simp [coeX], ⟨∞, Or.inr rfl⟩,
      ?_⟩
    have hcl : ∞ ∈ closure (coeX '' Lᶜ) := by
      refine mem_closure_iff_nhds.mpr fun N hN ↦ ?_
      obtain ⟨K', ⟨_, hK'k⟩, hK'N⟩ := hasBasis_nhds_infty.mem_iff.mp hN
      obtain ⟨y, hy⟩ : ((L ∪ K')ᶜ).Nonempty := by
        by_contra hne
        rw [not_nonempty_iff_eq_empty, compl_empty_iff] at hne
        exact hX.noncompact_univ (hne ▸ hLk.union hK'k)
      rw [compl_union, mem_inter_iff] at hy
      exact ⟨coeX y, hK'N (Or.inl ⟨y, hy.2, rfl⟩), ⟨y, hy.1, rfl⟩⟩
    exact (hLp.image coeX continuous_coe.continuousOn).subset_closure
      subset_union_left (union_subset subset_closure (by simpa [singleton_subset_iff] using hcl))

/-- The sphere `𝕊 = OnePoint ℝ²` is locally connected, so the components of the complement of a
drawing in it are open. -/
instance : LocallyConnectedSpace (OnePoint (EuclideanSpace ℝ (Fin 2))) :=
  locallyConnectedSpace_of_forall_exists_isPreconnected_compl fun K hK _ ↦
    exists_isCompact_isClosed_isPreconnected_compl_euclidean K hK

end OnePoint
