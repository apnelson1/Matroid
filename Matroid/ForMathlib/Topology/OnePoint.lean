module

public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Matroid.ForMathlib.Analysis.Normed.Module.ConnectedBall

/-!
# Local connectedness of the one-point compactification

Mathlib gives `OnePoint X` compactness, `T0`/`T1`, normality and connectedness, but not local
connectedness, which makes the components of an open set open — the property that turns
"connected component of an open complement" into an open set.

The criterion controls neighborhoods of `∞`, which have the form `{∞} ∪ Lᶜ` for compact closed
sets `L`. It requires such an `L` containing each compact set and having preconnected complement.

## Main statements

* `OnePoint.infty_mem_closure_image_coe` : `∞` is in the closure of the image of `s` exactly when
  `s` escapes every compact closed set.
* `OnePoint.locallyConnectedSpace_of_forall_exists_isPreconnected_compl` : the criterion.
* `OnePoint.locallyConnectedSpace_of_one_lt_rank` : it applies to a proper real normed space of
  rank at least two, where a closed ball large enough to swallow `K` has preconnected complement
  by `isPreconnected_compl_closedBall`. The corresponding instance on `OnePoint V` specializes it
  to the plane.
-/

@[expose] public section

open Set Topology

namespace OnePoint

variable {X : Type*} [TopologicalSpace X] {s : Set X}

/-- `∞` is in the closure of the image of `s` exactly when `s` escapes every compact closed set —
those complements are a neighbourhood basis at `∞`. -/
theorem infty_mem_closure_image_coe :
    (∞ : OnePoint X) ∈ closure ((↑) '' s) ↔ ∀ K : Set X, IsClosed K → IsCompact K → ¬ s ⊆ K := by
  rw [mem_closure_iff_nhds_basis hasBasis_nhds_infty]
  refine ⟨fun h K hKc hKk hsK ↦ ?_, fun h K hK ↦ ?_⟩
  · obtain ⟨_, ⟨x, hx, rfl⟩, hy⟩ := h K ⟨hKc, hKk⟩
    simp only [mem_union, mem_singleton_iff, coe_ne_infty, or_false,
      coe_injective.mem_set_image, mem_compl_iff] at hy
    exact hy (hsK hx)
  obtain ⟨x, hx, hxK⟩ := not_subset.1 (h K hK.1 hK.2)
  exact ⟨x, mem_image_of_mem _ hx, Or.inl ⟨x, hxK, rfl⟩⟩

/-- In a noncompact space, `∞` is in the closure of the image of the complement of any compact
set: no compact set covers that complement, or the two together would cover the space. -/
theorem infty_mem_closure_image_coe_compl [NoncompactSpace X] (hs : IsCompact s) :
    (∞ : OnePoint X) ∈ closure ((↑) '' sᶜ) := infty_mem_closure_image_coe.2 fun _ _ hK hsub ↦
    noncompact_univ X (compl_subset_iff_union.1 hsub ▸ hs.union hK)

variable [LocallyConnectedSpace X]

/-- If every compact closed set is contained in a compact closed set with preconnected complement,
then the one-point compactification of a locally connected space is locally connected.

At a point of `X` this is local connectedness of `X` transported along the open embedding. At `∞` a
neighbourhood contains `{∞} ∪ Kᶜ` with `K` compact and closed, and `{∞} ∪ Lᶜ` for `L ⊇ K` as in the
hypothesis is an open connected neighbourhood inside it: open because `L` is compact and closed,
connected because `Lᶜ` is preconnected and `∞` lies in its closure. -/
theorem locallyConnectedSpace_of_forall_exists_isPreconnected_compl
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
    exact ⟨((↑) '' Lᶜ) ∪ {∞}, union_subset ((image_mono <| compl_subset_compl.mpr hKL).trans <|
      subset_union_left.trans hKU) (singleton_subset_iff.mpr <| hKU (Or.inr rfl)),
      compl_image_coe L ▸ isOpen_compl_image_coe.mpr ⟨hLc, hLk⟩, by simp, ⟨∞, Or.inr rfl⟩,
      (hLp.image _ continuous_coe.continuousOn).subset_closure subset_union_left
        (union_subset subset_closure
          (by simpa [singleton_subset_iff] using infty_mem_closure_image_coe_compl hLk))⟩

/-- The sphere `OnePoint V` over a proper real normed space of rank at least two is locally
connected: a closed ball swallowing a compact set has preconnected complement. -/
theorem locallyConnectedSpace_of_one_lt_rank {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [ProperSpace V] (hV : 1 < Module.rank ℝ V) : LocallyConnectedSpace (OnePoint V) :=
  locallyConnectedSpace_of_forall_exists_isPreconnected_compl fun _ hK _ ↦
    have ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : V)
    ⟨Metric.closedBall 0 r, isCompact_closedBall .., Metric.isClosed_closedBall, hr,
      isPreconnected_compl_closedBall hV _ _⟩

/-- The sphere `OnePoint V` over a plane is locally connected. -/
instance {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [Fact (Module.finrank ℝ V = 2)] : LocallyConnectedSpace (OnePoint V) :=
  have : FiniteDimensional ℝ V := .of_fact_finrank_eq_two
  locallyConnectedSpace_of_one_lt_rank <| Module.one_lt_rank_of_one_lt_finrank <| by
    rw [Fact.out (p := Module.finrank ℝ V = 2)]
    norm_num

end OnePoint
