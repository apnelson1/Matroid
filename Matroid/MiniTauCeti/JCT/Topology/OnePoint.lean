module

public import Mathlib.Topology.Compactification.OnePoint.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Matroid.MiniTauCeti.JCT.Analysis.Normed.Module.ConnectedBall
public import Matroid.MiniTauCeti.JCT.Topology.ExteriorComponent

/-!
# Region transport and local connectedness of the one-point compactification

`OnePoint.extendSet` extends a set with a specified infinity membership condition.
An indexed partition into open connected regions transports to `OnePoint X` when one region has
compact complement. That region receives `∞`. The transport preserves indices, exact preimages,
and frontiers. In a proper real normed space of rank greater than one, the unbounded complementary
component selects this region for every bounded removed set, without restricting the index type.

Mathlib gives `OnePoint X` compactness, `T0`/`T1`, normality and connectedness, but not local
connectedness, which makes the components of an open set open, the property that turns
"connected component of an open complement" into an open set.

The criterion controls neighborhoods of `∞`, which have the form `{∞} ∪ Lᶜ` for compact closed
sets `L`. It requires such an `L` containing each compact set and having preconnected complement.

## Main statements

* `OnePoint.infty_mem_closure_image_coe` : `∞` is in the closure of the image of `s` exactly when
  `s` escapes every compact closed set.
* `OnePoint.frontier_image_coe_eq_iff` characterizes frontier transport by compactness of
  the closure.
* `OnePoint.isConnected_compl_image_coe_of_isCompact` adjoins infinity to a preconnected set with
  compact complement in a noncompact space.
* `OnePoint.extendSet` and its set-operation laws work without a topology.
* `OnePoint.isOpen_extendSet`, `OnePoint.isClosed_extendSet`, and
  `OnePoint.frontier_extendSet_eq_iff` characterize the topological laws separately.
* `OnePoint.isConnected_extendSet` gives sufficient conditions for connectedness.
* `OnePoint.exists_unbounded_region` selects the unique unbounded index with compact complement
  in a proper real normed space of rank greater than one.
* `OnePoint.locallyConnectedSpace_of_forall_exists_isPreconnected_compl` : the criterion.
* `OnePoint.locallyConnectedSpace_of_one_lt_rank` : it applies to a proper real normed space of
  rank at least two, where a closed ball large enough to swallow `K` has preconnected complement
  by `isPreconnected_compl_closedBall`. The corresponding instance on `OnePoint V` specializes it
  to the plane.
-/

@[expose] public section

open Set Topology

namespace OnePoint

variable {V X ι : Type*} {s t : Set X} {p q : Prop}

/-- Extend a set to the one-point type, including infinity exactly when `p` holds. -/
def extendSet (s : Set X) (p : Prop) : Set (OnePoint X) :=
  {z | OnePoint.elim z p (fun x ↦ x ∈ s)}

@[simp] theorem coe_mem_extendSet {x : X} : (x : OnePoint X) ∈ extendSet s p ↔ x ∈ s :=
  Iff.rfl

@[simp] theorem infty_mem_extendSet : (∞ : OnePoint X) ∈ extendSet s p ↔ p := Iff.rfl

@[simp] theorem preimage_coe_extendSet : ((↑) : X → OnePoint X) ⁻¹' extendSet s p = s := rfl

/-- The finite preimage and infinity membership determine the extended set. -/
theorem eq_extendSet_iff {u : Set (OnePoint X)} :
    u = extendSet s p ↔ ((↑) : X → OnePoint X) ⁻¹' u = s ∧ (∞ ∈ u ↔ p) := by
  refine ⟨fun h ↦ h ▸ ⟨rfl, Iff.rfl⟩, fun ⟨hpre, hinfty⟩ ↦ ?_⟩
  ext z
  induction z using OnePoint.rec with
  | coe x => exact Set.ext_iff.mp hpre x
  | infty => exact hinfty

@[simp] theorem extendSet_false : extendSet s False = (↑) '' s := by
  ext z
  induction z using OnePoint.rec <;> simp

@[simp] theorem extendSet_true : extendSet s True = ((↑) '' sᶜ)ᶜ := by
  ext z
  induction z using OnePoint.rec <;> simp

@[simp] theorem compl_extendSet : (extendSet s p)ᶜ = extendSet sᶜ (¬ p) := by
  ext z
  induction z using OnePoint.rec <;> rfl

theorem inter_extendSet : extendSet s p ∩ extendSet t q = extendSet (s ∩ t) (p ∧ q) := by
  ext z
  induction z using OnePoint.rec <;> rfl

theorem union_extendSet : extendSet s p ∪ extendSet t q = extendSet (s ∪ t) (p ∨ q) := by
  ext z
  induction z using OnePoint.rec <;> rfl

theorem iUnion_extendSet (W : ι → Set X) (P : ι → Prop) :
    (⋃ i, extendSet (W i) (P i)) = extendSet (⋃ i, W i) (∃ i, P i) := by
  ext z
  induction z using OnePoint.rec <;> simp

theorem disjoint_extendSet_iff :
    Disjoint (extendSet s p) (extendSet t q) ↔ Disjoint s t ∧ ¬ (p ∧ q) := by
  simp only [disjoint_left]
  refine ⟨fun h ↦ ?_, fun ⟨h, hpq⟩ z hz ht↦ ?_⟩
  · exact ⟨fun x hx ht ↦ h (coe_mem_extendSet.mpr hx) (coe_mem_extendSet.mpr ht),
      fun hpq ↦ h (infty_mem_extendSet.mpr hpq.1) (infty_mem_extendSet.mpr hpq.2)⟩
  induction z using OnePoint.rec with
  | coe x => exact h hz ht
  | infty => exact hpq ⟨hz, ht⟩

/-- The extension is nonempty exactly when the set is nonempty or infinity is included. -/
theorem nonempty_extendSet : (extendSet s p).Nonempty ↔ s.Nonempty ∨ p := by
  refine ⟨fun ⟨z, hz⟩ ↦ ?_, ?_⟩
  · induction z using OnePoint.rec with
    | coe x => exact Or.inl ⟨x, hz⟩
    | infty => exact Or.inr hz
  rintro (⟨x, hx⟩ | hp)
  · exact ⟨↑x, hx⟩
  exact ⟨∞, hp⟩

variable [TopologicalSpace X]

theorem isOpen_extendSet : IsOpen (extendSet s p) ↔ IsOpen s ∧ (p → IsCompact sᶜ) := by
  simp only [isOpen_def, infty_mem_extendSet, preimage_coe_extendSet]
  tauto

theorem isClosed_extendSet : IsClosed (extendSet s p) ↔ IsClosed s ∧ (¬ p → IsCompact s) := by
  rw [← isOpen_compl_iff, compl_extendSet, isOpen_extendSet]
  simp only [isOpen_compl_iff, compl_compl]

/-- `∞` is in the closure of the image of `s` exactly when `s` escapes every compact closed set —
those complements are a neighbourhood basis at `∞`. -/
theorem infty_mem_closure_image_coe :
    (∞ : OnePoint X) ∈ closure ((↑) '' s) ↔ ∀ K : Set X, IsClosed K → IsCompact K → ¬ s ⊆ K := by
  rw [mem_closure_iff_nhds_basis hasBasis_nhds_infty]
  refine ⟨fun h K hKc hKk hsK ↦ ?_, fun h K hK ↦ ?_⟩
  · obtain ⟨_, ⟨x, hx, rfl⟩, hy⟩ := h K ⟨hKc, hKk⟩
    simp only [mem_union, coe_injective.mem_set_image, mem_compl_iff, mem_singleton_iff,
      coe_ne_infty, or_false] at hy
    exact hy (hsK hx)
  obtain ⟨x, hx, hxK⟩ := not_subset.mp (h K hK.left hK.right)
  exact ⟨x, mem_image_of_mem _ hx, Or.inl ⟨x, hxK, rfl⟩⟩

/-- In a noncompact space, `∞` is in the closure of the image of the complement of any compact
set: no compact set covers that complement, or the two together would cover the space. -/
theorem infty_mem_closure_image_coe_compl [NoncompactSpace X] (hs : IsCompact s) :
    (∞ : OnePoint X) ∈ closure ((↑) '' sᶜ) := infty_mem_closure_image_coe.2 fun _ _ hK hsub ↦
    noncompact_univ X (compl_subset_iff_union.1 hsub ▸ hs.union hK)

/-- The frontier of the image is the image of the frontier exactly when the closure is compact. -/
theorem frontier_image_coe_eq_iff :
    frontier ((↑) '' s : Set (OnePoint X)) = (↑) '' frontier s ↔ IsCompact (closure s) := by
  refine ⟨fun h ↦ ?_, fun hs ↦ ?_⟩
  · have hinfty : (∞ : OnePoint X) ∉ closure ((↑) '' s) := by
      intro hc
      have hfr : (∞ : OnePoint X) ∈ frontier ((↑) '' s) :=
        ⟨hc, (infty_notMem_image_coe <| interior_subset ·)⟩
      exact infty_notMem_image_coe <| h ▸ hfr
    rw [infty_mem_closure_image_coe] at hinfty
    push Not at hinfty
    obtain ⟨K, hKclosed, hKcompact, hsK⟩ := hinfty
    exact hKcompact.of_isClosed_subset isClosed_closure <| closure_minimal hsK hKclosed
  replace hs : IsClosed ((↑) '' closure s : Set (OnePoint X)) :=
    isClosed_image_coe.mpr ⟨isClosed_closure, hs⟩
  have hpre := isOpenMap_coe.preimage_frontier_eq_frontier_preimage continuous_coe
    ((↑) '' s : Set (OnePoint X))
  simp only [preimage_image_eq _ coe_injective] at hpre
  rw [← hpre]
  ext x
  induction x using OnePoint.rec with | coe x => simp | infty => _
  have : (∞ : OnePoint X) ∉ frontier ((↑) '' s : Set (OnePoint X)) :=
    (infty_notMem_image_coe <| closure_minimal (image_mono subset_closure) hs <|
      frontier_subset_closure ·)
  simp [this]

/-- Exact frontier transport depends on the closure on the side that excludes infinity. -/
theorem frontier_extendSet_eq_iff :
    frontier (extendSet s p) = (↑) '' frontier s ↔
      (p → IsCompact (closure sᶜ)) ∧ (¬ p → IsCompact (closure s)) := by
  classical
  by_cases hp : p
  · simp only [hp, extendSet_true, frontier_compl, true_implies, not_true_eq_false,
      false_implies, and_true]
    rw [← frontier_compl s, frontier_image_coe_eq_iff]
  · simp [hp, frontier_image_coe_eq_iff]

/-- Adjoining infinity preserves preconnectedness when infinity is in the closure. -/
theorem isPreconnected_extendSet (hs : IsPreconnected s)
    (hinfty : p → (∞ : OnePoint X) ∈ closure ((↑) '' s)) :
    IsPreconnected (extendSet s p) := by
  apply (hs.image _ continuous_coe.continuousOn).subset_closure
  · rintro _ ⟨x, hx, rfl⟩
    exact hx
  intro z hz
  induction z using OnePoint.rec with
  | coe x => exact subset_closure (mem_image_of_mem _ hz)
  | infty => exact hinfty hz

/-- Adjoining infinity gives a connected set when it lies in the closure of a preconnected set. -/
theorem isConnected_extendSet (hs : IsPreconnected s) (hne : s.Nonempty ∨ p)
    (hinfty : p → (∞ : OnePoint X) ∈ closure ((↑) '' s)) :
    IsConnected (extendSet s p) :=
  ⟨nonempty_extendSet.mpr hne, isPreconnected_extendSet hs hinfty⟩

/-- Adjoining infinity to a preconnected set with compact complement gives a connected set. -/
theorem isConnected_compl_image_coe_of_isCompact [NoncompactSpace X] (hs : IsPreconnected s)
    (hsc : IsCompact sᶜ) : IsConnected (((↑) '' sᶜ : Set (OnePoint X))ᶜ) := by
  rw [← extendSet_true]
  exact isConnected_extendSet hs (Or.inr trivial) fun _ ↦
    compl_compl s ▸ infty_mem_closure_image_coe_compl hsc

/-- An open preconnected partition of a bounded complement has a unique unbounded region,
and that region has compact complement. The index type need not be finite. -/
theorem exists_unbounded_region [NormedAddCommGroup V] [NormedSpace ℝ V]
    [ProperSpace V] {K : Set V} (hK : Bornology.IsBounded K) (hdim : 1 < Module.rank ℝ V)
    {W : ι → Set V} (hO : ∀ i, IsOpen (W i)) (hC : ∀ i, IsPreconnected (W i))
    (hd : Pairwise fun i j ↦ Disjoint (W i) (W j)) (hcover : (⋃ i, W i) = Kᶜ) :
    ∃ e : ι, IsCompact (W e)ᶜ ∧ ∀ i, ¬ Bornology.IsBounded (W i) ↔ i = e := by
  classical
  have : Nontrivial V := (rank_pos_iff_nontrivial (R := ℝ)).mp (zero_lt_one.trans hdim)
  obtain ⟨x, hx, hxb⟩ := Bornology.exists_unbounded_connectedComponentIn_compl hK
  obtain ⟨e, he⟩ := mem_iUnion.mp (hcover.symm ▸ (show x ∈ Kᶜ from hx))
  have heK : W e ⊆ Kᶜ := fun y hy ↦ hcover ▸ mem_iUnion.mpr ⟨e, hy⟩
  have hfront : frontier (W e) ⊆ K := by
    intro y hy
    by_contra hyK
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.symm ▸ (show y ∈ Kᶜ from hyK))
    by_cases hie : i = e
    · subst i
      exact disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr (hO e)) hy hi
    · exact disjoint_left.mp ((hd (Ne.symm hie)).frontier_left (hO i)) hy hi
  have heq : W e = connectedComponentIn Kᶜ x :=
    eq_connectedComponentIn_of_frontier_subset (hO e) (hC e)
      (disjoint_left.mpr fun y hy hyK ↦ heK hy hyK) hfront he
  have heb : ¬ Bornology.IsBounded (W e) := heq ▸ hxb
  have hebc : Bornology.IsBounded (W e)ᶜ := heq ▸
    Bornology.isBounded_compl_connectedComponentIn_compl hK hdim hxb
  have hec : IsCompact (W e)ᶜ := (hO e).isClosed_compl.closure_eq ▸ hebc.isCompact_closure
  have hunbounded (i : ι) : ¬ Bornology.IsBounded (W i) ↔ i = e := by
    refine ⟨fun hi ↦ ?_, fun hie ↦ hie ▸ heb⟩
    by_contra hie
    exact hi (hebc.subset (hd hie).subset_compl_right)
  exact ⟨e, hec, hunbounded⟩

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
    refine ⟨((↑) '' Lᶜ) ∪ {∞}, union_subset ((image_mono <| compl_subset_compl.mpr hKL).trans <|
      subset_union_left.trans hKU) (singleton_subset_iff.mpr <| hKU (Or.inr rfl)),
      compl_image_coe L ▸ isOpen_compl_image_coe.mpr ⟨hLc, hLk⟩, by simp, ?_⟩
    simpa only [compl_compl, compl_image_coe] using
      isConnected_compl_image_coe_of_isCompact hLp (by simpa using hLk)

/-- The sphere `OnePoint V` over a proper real normed space of rank at least two is locally
connected: a closed ball swallowing a compact set has preconnected complement. -/
theorem locallyConnectedSpace_of_one_lt_rank [NormedAddCommGroup V] [NormedSpace ℝ V]
    [ProperSpace V] (hV : 1 < Module.rank ℝ V) : LocallyConnectedSpace (OnePoint V) :=
  locallyConnectedSpace_of_forall_exists_isPreconnected_compl fun _ hK _ ↦
    have ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : V)
    ⟨Metric.closedBall 0 r, isCompact_closedBall .., Metric.isClosed_closedBall, hr,
      isPreconnected_compl_closedBall hV _ _⟩

/-- The sphere `OnePoint V` over a plane is locally connected. -/
instance [NormedAddCommGroup V] [NormedSpace ℝ V] [Fact (Module.finrank ℝ V = 2)] :
    LocallyConnectedSpace (OnePoint V) := by
  have : FiniteDimensional ℝ V := .of_fact_finrank_eq_two
  refine locallyConnectedSpace_of_one_lt_rank <| Module.one_lt_rank_of_one_lt_finrank ?_
  rw [Fact.out (p := Module.finrank ℝ V = 2)]
  norm_num

end OnePoint
