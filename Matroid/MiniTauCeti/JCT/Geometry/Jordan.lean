module

public import Matroid.MiniTauCeti.JCT.Geometry.JordanAssembly
public import Matroid.MiniTauCeti.JCT.Geometry.JordanSeparation
public import Matroid.MiniTauCeti.JCT.Geometry.JordanThreeComponents
public import Matroid.MiniTauCeti.JCT.Geometry.K33
public import Matroid.MiniTauCeti.JCT.Topology.Circuit.Accessibility
public import Matroid.MiniTauCeti.JCT.Topology.ArcComplement
public import Matroid.MiniTauCeti.JCT.Topology.ExteriorComponent
public import Matroid.MiniTauCeti.JCT.Topology.PrimitiveLink.Regions

/-!
# The Jordan curve theorem for intrinsic circuits

A compact circuit in the plane has two complementary components with common frontier equal to
the circuit. Polygonal Jordan separation and polygonal approximation supply the nonplanarity of
K₃,₃ used to exclude a connected complement and three distinct complementary components.

`IsCircuit.jordanCurveTheorem` selects the bounded component in any real normed plane.
-/

public section

open Set Topology Function Bornology

attribute [local instance] Complex.finrank_real_complex_fact

namespace IsCircuit

theorem not_isPreconnected_compl {C : Set ℂ} (hC : IsCircuit C) (hc : IsCompact C) :
    ¬ IsPreconnected Cᶜ := by
  intro hconn
  obtain ⟨v, L, hv, hL, hLV, hLL⟩ :=
    JordanConfigurations.of_connected_complement hC hc hconn
  exact K33.obstruction v L hv hL hLV hLL

theorem accessible_in_open_set {C O : Set ℂ} {p : ℂ}
    (hC : IsCircuit C) (hc : IsCompact C) (hO : IsOpen O) (hOC : (O ∩ C).Nonempty)
    (hp : p ∉ C) :
    ∃ q ∈ O ∩ C, ∃ L : Set ℂ, IsPrimitiveLink L p q ∧ IsSegmentFigure L ∧
      L \ {q} ⊆ connectedComponentIn Cᶜ p :=
  hC.accessibility_of_arc_complements hc (hC.not_isPreconnected_compl hc)
    (fun hA hab ↦ hA.isPathConnected_compl hab) hO hOC hp

theorem at_most_two_components {C : Set ℂ} (hC : IsCircuit C) (hc : IsCompact C)
    {p q r : ℂ} (hp : p ∉ C) (hq : q ∉ C) (hr : r ∉ C) :
    connectedComponentIn Cᶜ p = connectedComponentIn Cᶜ q ∨
    connectedComponentIn Cᶜ p = connectedComponentIn Cᶜ r ∨
    connectedComponentIn Cᶜ q = connectedComponentIn Cᶜ r := by
  classical
  by_contra! h
  have hout : ∀ i : Fin 3, ![p, q, r] i ∉ C := by
    intro i
    fin_cases i <;> simp_all
  have hdistinct : Pairwise fun i j : Fin 3 ↦
      connectedComponentIn Cᶜ (![p, q, r] i) ≠
        connectedComponentIn Cᶜ (![p, q, r] j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [ne_comm]
  obtain ⟨v, L, hv, hL, hLV, hLL⟩ :=
    JordanConfigurations.of_three_components hC hc ![p, q, r] hout hdistinct
      (fun i O hO hOC ↦ hC.accessible_in_open_set hc hO hOC (hout i))
  exact K33.obstruction v L hv hL hLV hLL

theorem jordan {C : Set ℂ} (hC : IsCircuit C) (hc : IsCompact C) :
    ∃ U V : Set ℂ, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
      Disjoint U V ∧ U ∪ V = Cᶜ ∧ frontier U = C ∧ frontier V = C :=
  hc.isClosed.isOpen_compl.exists_two_regions_of_card_connectedComponents_eq_two
    (ConnectedComponents.card_eq_two_of_not_isPreconnected
      (hC.not_isPreconnected_compl hc) (hC.at_most_two_components hc))
    (fun _ hp ↦ hc.isClosed.frontier_connectedComponentIn_compl_eq_of_accessibility
      fun O hO hOC ↦ by
        obtain ⟨q, hq, L, hL, -, hsub⟩ := hC.accessible_in_open_set hc hO hOC hp
        exact ⟨q, hq, L, hL, hsub⟩)

theorem bounded_jordan {C : Set ℂ} (hC : IsCircuit C) (hc : IsCompact C) :
    ∃ U : Set ℂ, U ⊆ Cᶜ ∧ IsBounded U ∧ IsConnected U ∧
      IsConnected (Cᶜ \ U) ∧ frontier U = C ∧ frontier (Cᶜ \ U) = C :=
  Bornology.exists_bounded_compl_region
    (Bornology.unbounded_connectedComponentIn_compl_eq hc.isBounded
      (by rw [Complex.rank_real_complex]; norm_num)) (hC.jordan hc)

/-- A compact intrinsic circuit in a real normed plane bounds a connected bounded region;
the rest of its complement is connected, and the circuit is the frontier of both regions. -/
theorem jordanCurveTheorem {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)] {C : Set E} (hC : IsCircuit C) (hc : IsCompact C) :
    ∃ U : Set E, U ⊆ Cᶜ ∧ IsBounded U ∧ IsConnected U ∧
      IsConnected (Cᶜ \ U) ∧ frontier U = C ∧ frontier (Cᶜ \ U) = C :=
  Jordan.bounded_regions_of_complex (fun hC hc ↦ hC.bounded_jordan hc) hC hc

/-- A compact circuit in a real normed plane is the frontier of every complementary component. -/
theorem frontier_connectedComponentIn_compl {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fact (Module.finrank ℝ E = 2)]
    {C : Set E} {p : E} (hC : IsCircuit C) (hc : IsCompact C) (hp : p ∉ C) :
    frontier (connectedComponentIn Cᶜ p) = C := by
  obtain ⟨U, hUC, _, hUconn, hVconn, hUfront, hVfront⟩ := hC.jordanCurveTheorem hc
  have hUopen : IsOpen U := by
    rw [← disjoint_frontier_iff_isOpen, hUfront, disjoint_comm]
    exact subset_compl_iff_disjoint_right.mp hUC
  have hVopen : IsOpen (Cᶜ \ U) := by
    rw [← disjoint_frontier_iff_isOpen, hVfront, disjoint_comm]
    exact subset_compl_iff_disjoint_right.mp sdiff_subset
  by_cases hpU : p ∈ U
  · rw [← eq_connectedComponentIn_of_frontier_subset hUopen hUconn.isPreconnected
      (subset_compl_iff_disjoint_right.mp hUC) hUfront.subset hpU]
    exact hUfront
  · rw [← eq_connectedComponentIn_of_frontier_subset hVopen hVconn.isPreconnected
      (subset_compl_iff_disjoint_right.mp sdiff_subset) hVfront.subset ⟨hp, hpU⟩]
    exact hVfront

end IsCircuit
