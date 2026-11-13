module

public import Matroid.MiniTauCeti.JCT.Geometry.ThetaRegions
public import Matroid.MiniTauCeti.JCT.Topology.OnePoint

/-!
# The polygonal theta-curve theorem

Three simple polygonal arcs with the same two endpoints and no other common points cut the
one-point compactification of the plane into exactly three regions.

`IsPrimitiveLink.regions` supplies the plane regions. The generic one-point transport preserves
their indices and frontiers and adds infinity to the unique unbounded region.
-/

open Function Set Topology

namespace IsPrimitiveLink

public noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {a b : V}
  [Fact (Module.finrank ℝ V = 2)]

/-- **Theta-curve theorem.** Three embedded polygonal arcs with the same two endpoints, meeting
nowhere else, cut the sphere into exactly three regions.  The region omitted by index `i` is bounded
by the other two arcs. -/
theorem exists_three_regions_theta (hab : a ≠ b) (A : Fin 3 → Set V)
    (hA : ∀ i, IsPrimitiveLink (A i) a b) (hpoly : ∀ i, IsSegmentFigure (A i))
    (hmeet : ∀ i j, i ≠ j → A i ∩ A j = {a, b}) :
    ∃ W : Fin 3 → Set (OnePoint V),
      (∀ i, IsOpen (W i)) ∧
      (∀ i, IsConnected (W i)) ∧
      (Pairwise fun i j ↦ Disjoint (W i) (W j)) ∧
      (⋃ i, W i) = ((↑) '' (⋃ i, A i))ᶜ ∧
      ∀ i, frontier (W i) =
        (↑) '' ⋃ j ∈ ({i}ᶜ : Set (Fin 3)), A j := by
  let : FiniteDimensional ℝ V := .of_fact_finrank_eq_two
  have hdim : 1 < Module.rank ℝ V := Module.one_lt_rank_of_one_lt_finrank (by
    rw [Fact.out (p := Module.finrank ℝ V = 2)]
    norm_num)
  have : Nontrivial V := (rank_pos_iff_nontrivial (R := ℝ)).mp (zero_lt_one.trans hdim)
  obtain ⟨W, hO, hC, hd, hcover, hf⟩ := IsPrimitiveLink.regions A hab hA hpoly hmeet
  obtain ⟨e, he, hunbounded⟩ := OnePoint.exists_unbounded_region
    (isCompact_iUnion fun i ↦ (hA i).isCompact).isBounded hdim
    hO (fun i ↦ (hC i).isPreconnected) hd hcover
  let W' i := OnePoint.extendSet (W i) (¬ Bornology.IsBounded (W i))
  refine ⟨W', ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    apply OnePoint.isOpen_extendSet.mpr
    refine ⟨hO i, fun hi ↦ ?_⟩
    have hie := (hunbounded i).mp hi
    subst i
    exact he
  · intro i
    apply OnePoint.isConnected_extendSet (hC i).isPreconnected (Or.inl (hC i).nonempty)
    intro hi
    have hie := (hunbounded i).mp hi
    subst i
    simpa only [compl_compl] using OnePoint.infty_mem_closure_image_coe_compl he
  · intro i j hij
    exact OnePoint.disjoint_extendSet_iff.mpr ⟨hd hij, fun h ↦
      hij (((hunbounded i).mp h.1).trans ((hunbounded j).mp h.2).symm)⟩
  · dsimp [W']
    rw [OnePoint.iUnion_extendSet, hcover]
    simp only [hunbounded, exists_eq, OnePoint.extendSet_true, compl_compl]
  intro i
  refine Eq.trans (OnePoint.frontier_extendSet_eq_iff.mpr ⟨?_, ?_⟩) (congrArg _ (hf i))
  · intro hi
    have hie := (hunbounded i).mp hi
    subst i
    exact (hO e).isClosed_compl.closure_eq.symm ▸ he
  intro hi
  have hie : i ≠ e := fun hie ↦ hi ((hunbounded i).mpr hie)
  exact he.of_isClosed_subset isClosed_closure
    (closure_minimal (hd hie).subset_compl_right (hO e).isClosed_compl)

end

end IsPrimitiveLink
