module

public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Local connectedness of the one-point compactification

Mathlib gives `OnePoint X` compactness, `T0`/`T1`, normality and connectedness, but not local
connectedness, which makes the components of an open set open — the property that turns
"connected component of an open complement" into an open set.

The criterion controls neighborhoods of `∞`, which have the form `{∞} ∪ Lᶜ` for compact closed
sets `L`. It requires such an `L` containing each compact set and having preconnected complement.

## Main statements

* `OnePoint.locallyConnectedSpace_of_forall_exists_isPreconnected_compl` : the criterion.
* `exists_isCompact_isClosed_isPreconnected_compl` : its hypothesis for a proper real normed space
  of rank at least two, where a closed ball large enough to swallow `K` has preconnected
  complement.
* `OnePoint.locallyConnectedSpace_of_one_lt_rank` and the corresponding instance on `OnePoint V`.

The normed-space result uses that complements of closed balls are preconnected in rank at least two.
It is then specialized to the plane to obtain local connectedness of `OnePoint V`.
-/

@[expose] public section

open Set Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The complement of a closed ball in a real normed space of rank at least two is preconnected.
This is where the dimension enters: in rank one the complement of a ball falls apart.

Mathlib has `isPathConnected_sphere` for `1 < Module.rank ℝ V`; the complement of a ball is the
union of the spheres of radius `> r`, each path connected and each meeting a fixed ray. -/
theorem isPreconnected_compl_closedBall (hV : 1 < Module.rank ℝ V) (x : V) (r : ℝ) :
    IsPreconnected (Metric.closedBall x r)ᶜ := by
  refine (IsPathConnected.isConnected ?_).isPreconnected
  rcases lt_or_ge r 0 with hr | hr
  · simpa [Metric.closedBall_eq_empty.2 hr] using isPathConnected_univ
  let f : V × ℝ → V := fun p ↦ x + p.2 • p.1
  have hpc : IsPathConnected (Metric.sphere (0 : V) 1 ×ˢ Ioi r) :=
    (isPathConnected_sphere hV 0 zero_le_one).prod <|
      (convex_Ioi r).isPathConnected ⟨r + 1, by simp⟩
  have himg : f '' (Metric.sphere (0 : V) 1 ×ˢ Ioi r) = (Metric.closedBall x r)ᶜ := by
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

/-- Every compact set in a proper real normed space of rank at least two sits inside a closed ball,
whose complement is preconnected. This is the hypothesis of the criterion below. -/
theorem exists_isCompact_isClosed_isPreconnected_compl [ProperSpace V]
    (hV : 1 < Module.rank ℝ V) (K : Set V) (hK : IsCompact K) :
    ∃ L : Set V, IsCompact L ∧ IsClosed L ∧ K ⊆ L ∧ IsPreconnected Lᶜ := by
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : V)
  exact ⟨Metric.closedBall 0 r, isCompact_closedBall _ _, Metric.isClosed_closedBall, hr,
    isPreconnected_compl_closedBall hV _ _⟩

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

/-- The sphere `OnePoint V` over a proper real normed space of rank at least two is locally
connected. -/
theorem locallyConnectedSpace_of_one_lt_rank {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [ProperSpace V] (hV : 1 < Module.rank ℝ V) : LocallyConnectedSpace (OnePoint V) :=
  locallyConnectedSpace_of_forall_exists_isPreconnected_compl fun K hK _ ↦
    exists_isCompact_isClosed_isPreconnected_compl hV K hK

/-- The sphere `OnePoint V` over a plane is locally connected. -/
instance {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [Fact (Module.finrank ℝ V = 2)] : LocallyConnectedSpace (OnePoint V) :=
  have : FiniteDimensional ℝ V := .of_fact_finrank_eq_two
  locallyConnectedSpace_of_one_lt_rank <| Module.one_lt_rank_of_one_lt_finrank <| by
    rw [Fact.out (p := Module.finrank ℝ V = 2)]; norm_num

end OnePoint
