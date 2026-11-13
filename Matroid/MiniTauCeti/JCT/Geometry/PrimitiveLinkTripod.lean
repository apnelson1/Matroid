module

public import Matroid.MiniTauCeti.JCT.Geometry.PolygonalPath.Approximation
public import Matroid.MiniTauCeti.JCT.Geometry.PolygonalPath.SegmentFigure

/-!
# Tripods with prescribed boundary endpoints

Three polygonal accesses to distinct boundary points of an open connected set contain a tripod
whose branch point is in the open set. First contact with a closed arc supplies the branch point.
-/

@[expose] public section

open Set Function Topology
open scoped unitInterval

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Three polygonal accesses from an open path-connected set to distinct points outside it
admit a tripod with those endpoints and its branch point in the open set. -/
theorem IsOpen.exists_primitiveLink_tripod {U : Set V} (hU : IsOpen U)
    (hc : IsPathConnected U) {p : V} (hp : p ∈ U) (a : Fin 3 → V)
    (ha : Injective a) (haU : ∀ i, a i ∉ U)
    (L : Fin 3 → Set V) (hL : ∀ i, IsPrimitiveLink (L i) p (a i))
    (hpoly : ∀ i, IsSegmentFigure (L i)) (hLU : ∀ i, L i \ {a i} ⊆ U) :
    ∃ b ∈ U, ∃ M : Fin 3 → Set V,
      (∀ i, IsPrimitiveLink (M i) b (a i)) ∧
      (∀ i, IsSegmentFigure (M i)) ∧ (∀ i, M i \ {a i} ⊆ U) ∧
      Pairwise (fun i j ↦ M i ∩ M j = {b}) := by
  obtain ⟨P₀, -, hP₀⟩ := (hL 0).symm.exists_polygonalPath (hpoly 0)
  obtain ⟨P₁, -, hP₁⟩ := (hL 1).exists_polygonalPath (hpoly 1)
  let A := (P₀.append P₁).simpleArc.toSet
  have hAsub := (P₀.append P₁).toSet_simpleArc_subset
  have hA : IsPrimitiveLink A (a 0) (a 1) := by
    rw [show A = (P₀.append P₁).simpleArc.toSet from rfl, PolygonalPath.toSet_eq_range_toPath]
    exact ((P₀.append P₁).isPrimitive_simpleArc (ha.ne (by decide))).isPrimitiveLink
  have hApoly := (P₀.append P₁).simpleArc.isSegmentFigure_toSet
  have hAsub' : A ⊆ L 0 ∪ L 1 := by
    simpa only [PolygonalPath.toSet_append, hP₀, hP₁] using hAsub
  have hAU : A \ {a 0, a 1} ⊆ U := by
    rintro z ⟨hz, hzends⟩
    obtain hz | hz := hAsub' hz
    · exact hLU 0 ⟨hz, fun h ↦ hzends (Or.inl h)⟩
    · exact hLU 1 ⟨hz, fun h ↦ hzends (Or.inr h)⟩
  obtain ⟨w, hwA, hwend⟩ := hA.diff_endpoints_nonempty
  have hwU : w ∈ U := hAU ⟨hwA, hwend⟩
  obtain ⟨R, hRU⟩ := (hc.joinedIn p hp w hwU).exists_polygonalPath_of_open hU
  obtain ⟨P₂, -, hP₂⟩ := (hL 2).symm.exists_polygonalPath (hpoly 2)
  let B := (P₂.append R).simpleArc.toSet
  have hBsub := (P₂.append R).toSet_simpleArc_subset
  have hB : IsPrimitiveLink B (a 2) w := by
    rw [show B = (P₂.append R).simpleArc.toSet from rfl, PolygonalPath.toSet_eq_range_toPath]
    exact ((P₂.append R).isPrimitive_simpleArc (fun h ↦ haU 2 (h ▸ hwU))).isPrimitiveLink
  have hBpoly := (P₂.append R).simpleArc.isSegmentFigure_toSet
  have hBU : B \ {a 2} ⊆ U := by
    rintro z ⟨hz, hz2⟩
    have hz' : z ∈ L 2 ∪ R.toSet := by
      simpa only [PolygonalPath.toSet_append, hP₂] using hBsub hz
    exact hz'.elim (fun hz ↦ hLU 2 ⟨hz, hz2⟩) (fun hz ↦ hRU hz)
  have ha2A : a 2 ∉ A := by
    intro h
    apply haU 2
    apply hAU ⟨h, ?_⟩
    simp only [mem_insert_iff, mem_singleton_iff]
    exact not_or.mpr ⟨ha.ne (by decide), ha.ne (by decide)⟩
  obtain ⟨b, hbA, M, hMB, hM, hMA⟩ := hB.exists_initial_sublink hA.isClosed ha2A hwA
  have hb2 : b ≠ a 2 := fun h ↦ ha2A (h ▸ hbA)
  have hbU : b ∈ U := hBU ⟨hMB hM.right_mem, hb2⟩
  have hb0 : b ≠ a 0 := fun h ↦ haU 0 (h ▸ hbU)
  have hb1 : b ≠ a 1 := fun h ↦ haU 1 (h ▸ hbU)
  let M₀ := hA.splitLeft b
  let M₁ := hA.splitRight b
  have hM₀ : IsPrimitiveLink M₀ b (a 0) := (hA.isPrimitiveLink_splitLeft hbA hb0).symm
  have hM₁ : IsPrimitiveLink M₁ b (a 1) := hA.isPrimitiveLink_splitRight hbA hb1
  have h01 : M₀ ∩ M₁ = {b} := by
    rw [hA.splitLeft_inter_splitRight hbA]
    simp [ha.ne (by decide : (1 : Fin 3) ≠ 0)]
  have hMsub : M \ {a 2} ⊆ U := fun z hz ↦ hBU ⟨hMB hz.1, hz.2⟩
  have h0U : M₀ \ {a 0} ⊆ U := by
    rintro z ⟨hz, hz0⟩
    apply hAU
    refine ⟨hA.splitLeft_subset b hz, ?_⟩
    rintro (hz0' | rfl)
    · exact hz0 hz0'
    · exact hb1 (h01.subset ⟨hz, hA.right_mem_splitRight b⟩).symm
  have h1U : M₁ \ {a 1} ⊆ U := by
    rintro z ⟨hz, hz1⟩
    apply hAU
    refine ⟨hA.splitRight_subset b hz, ?_⟩
    rintro (rfl | hz1')
    · exact hb0 (h01.subset ⟨hA.left_mem_splitLeft b, hz⟩).symm
    · exact hz1 hz1'
  have h02 : M₀ ∩ M = {b} := by
    apply subset_antisymm
    · exact fun z hz ↦ hMA.subset ⟨hz.2, hA.splitLeft_subset b hz.1⟩
    · rintro z rfl
      exact ⟨hM₀.left_mem, hM.right_mem⟩
  have h12 : M₁ ∩ M = {b} := by
    apply subset_antisymm
    · exact fun z hz ↦ hMA.subset ⟨hz.2, hA.splitRight_subset b hz.1⟩
    · rintro z rfl
      exact ⟨hM₁.left_mem, hM.right_mem⟩
  refine ⟨b, hbU, ![M₀, M₁, M], ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hM₀
    · exact hM₁
    · exact hM.symm
  · intro i
    fin_cases i
    · exact hApoly.of_isPrimitiveLink_subset hM₀ (hA.splitLeft_subset b)
    · exact hApoly.of_isPrimitiveLink_subset hM₁ (hA.splitRight_subset b)
    · exact hBpoly.of_isPrimitiveLink_subset hM.symm hMB
  · intro i
    fin_cases i
    · exact h0U
    · exact h1U
    · exact hMsub
  · intro i j hij
    fin_cases i <;> fin_cases j
    all_goals
      first
      | exact (hij rfl).elim
      | exact h01
      | exact h02
      | exact h12
      | exact (inter_comm _ _).trans h01
      | exact (inter_comm _ _).trans h02
      | exact (inter_comm _ _).trans h12
