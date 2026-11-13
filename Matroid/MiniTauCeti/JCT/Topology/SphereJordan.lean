module

public import Matroid.MiniTauCeti.JCT.Topology.JordanCurve
public import Mathlib.Topology.Compactification.OnePoint.Sphere
public import Mathlib.Analysis.Normed.Module.Connected

/-! # Jordan separation on the sphere

A compact intrinsic circuit in any space homeomorphic to the two-dimensional sphere
has two complementary regions, each with that circuit as its frontier.
-/

@[expose] public section

open Set Topology

namespace IsCircuit

private lemma not_isCircuit_univ_onePoint_plane :
    ¬ IsCircuit (univ : Set (OnePoint (EuclideanSpace ℝ (Fin 2)))) := by
  intro h
  have hc := isConnected_compl_singleton_of_one_lt_rank
    (E := EuclideanSpace ℝ (Fin 2))
    (Module.one_lt_rank_of_one_lt_finrank (by simp)) 0
  have heq : (univ : Set (OnePoint (EuclideanSpace ℝ (Fin 2)))) \
      {OnePoint.infty, (↑(0 : EuclideanSpace ℝ (Fin 2)))} =
      (↑) '' ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 2))) := by
    ext x
    induction x using OnePoint.rec with
    | infty => simp
    | coe x => simp
  apply h.pair_puncture_not_isPreconnected (a := OnePoint.infty)
    (b := ↑(0 : EuclideanSpace ℝ (Fin 2))) (mem_univ _) (mem_univ _) (by simp)
  rw [heq]
  exact hc.isPreconnected.image _ OnePoint.continuous_coe.continuousOn

/-- The two sides have no distinguished order without a choice of pole or orientation,
so this theorem asserts their existence rather than choosing an ordering. -/
theorem exists_sides_sphere {X : Type*} [TopologicalSpace X] {J : Set X}
    (hJ : IsCircuit J) (hc : IsCompact J)
    (hX : Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :
    ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
      Disjoint U V ∧ U ∪ V = Jᶜ ∧ frontier U = J ∧ frontier V = J := by
  classical
  obtain ⟨f⟩ := hX
  let e₀ := onePointEquivSphereOfFinrankEq
    (V := EuclideanSpace ℝ (Fin 2)) (ι := Fin 3) (by simp)
  have hproper : f '' J ≠ univ := by
    intro heq
    have h := e₀.symm.isEmbedding.isCircuit_image.mpr (f.isEmbedding.isCircuit_image.mpr hJ)
    rw [heq, image_univ, e₀.symm.surjective.range_eq] at h
    exact not_isCircuit_univ_onePoint_plane h
  obtain ⟨p, hp⟩ := (Set.ne_univ_iff_exists_notMem _).mp hproper
  have hp_norm : ‖p.val‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using p.property
  let P := (ℝ ∙ p.val)ᗮ
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  let : Fact (Module.finrank ℝ P = 2) := ⟨by
    apply Submodule.finrank_orthogonal_span_singleton
    intro h
    simp [h] at hp_norm⟩
  let e : OnePoint P ≃ₜ X := (onePointHyperplaneHomeoUnitSphere hp_norm).trans f.symm
  have he_infty : e OnePoint.infty = f.symm p := rfl
  have hinfty : OnePoint.infty ∉ e ⁻¹' J := by
    intro h
    apply hp
    exact ⟨e OnePoint.infty, h, by rw [he_infty]; simp⟩
  let A : Set P := (↑) ⁻¹' (e ⁻¹' J)
  have hArange : e ⁻¹' J ⊆ range ((↑) : P → OnePoint P) := by
    intro x hx
    by_contra hn
    exact hinfty ((OnePoint.notMem_range_coe_iff.mp hn) ▸ hx)
  have hAimage : (↑) '' A = e ⁻¹' J := image_preimage_eq_of_subset hArange
  have hA : IsCircuit A := OnePoint.isOpenEmbedding_coe.isEmbedding.isCircuit_image.mp (by
    rw [hAimage]
    apply e.isEmbedding.isCircuit_image.mp
    simpa using hJ)
  have hcA : IsCompact A := OnePoint.isOpenEmbedding_coe.isEmbedding.isInducing.isCompact_preimage'
    (e.isCompact_preimage.mpr hc) hArange
  have heA : e '' ((↑) '' A) = J := by rw [hAimage]; simp
  refine ⟨e '' hA.insideOnePoint hcA, e '' hA.outsideOnePoint hcA,
    e.isOpenMap _ (hA.insideOnePoint_isOpen hcA),
    e.isOpenMap _ (hA.outsideOnePoint_isOpen hcA),
    (hA.insideOnePoint_isConnected hcA).image _ e.continuous.continuousOn,
    (hA.outsideOnePoint_isConnected hcA).image _ e.continuous.continuousOn,
    disjoint_image_of_injective e.injective (hA.insideOnePoint_disjoint_outsideOnePoint hcA),
    ?_, ?_, ?_⟩
  · rw [← image_union, hA.insideOnePoint_union_outsideOnePoint hcA, e.image_compl, heA]
  · rw [← e.image_frontier, hA.frontier_insideOnePoint hcA, heA]
  · rw [← e.image_frontier, hA.frontier_outsideOnePoint hcA, heA]

/-- A compact intrinsic circuit on the sphere has exactly two complementary components. -/
theorem card_connectedComponents_compl_sphere {X : Type*} [TopologicalSpace X] {J : Set X}
    (hJ : IsCircuit J) (hc : IsCompact J)
    (hX : Nonempty (X ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) :
    Nat.card (ConnectedComponents ↥Jᶜ) = 2 := by
  obtain ⟨U, V, hU, hV, hcU, hcV, hd, hu, _, _⟩ := hJ.exists_sides_sphere hc hX
  exact ConnectedComponents.card_eq_two hU hV hcU hcV hd hu

end IsCircuit
