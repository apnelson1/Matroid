module

public import Matroid.MiniTauCeti.JCT.Geometry.ThetaSphere
public import Matroid.MiniTauCeti.JCT.Geometry.PolygonalPath.SegmentFigure
public import Matroid.MiniTauCeti.JCT.Topology.Circuit.CompactParametrization

/-!
# Polygonal crosscuts

A polygonal arc across a complementary region of a polygonal circuit splits that region into
two regions. Two disjoint crosscuts of the same region cannot have alternating endpoints.
-/

open Function Set Topology

public noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (Module.finrank ℝ V = 2)] {s t s₁ s₂ t₁ t₂ : V}

/-- A polygonal crosscut splits a complementary region of a polygonal circuit into two regions. -/
theorem IsCircuit.exists_two_regions_crosscut {C A : Set V} (hC : IsCircuit C)
    (hCpoly : IsSegmentFigure C) (hA : IsPrimitiveLink A s t) (hApoly : IsSegmentFigure A)
    {F : Set (OnePoint V)} {q : OnePoint V}
    (hF : F = connectedComponentIn ((↑) '' C)ᶜ q) (hst : s ≠ t)
    (hAJ : A ∩ C = {s, t}) (hAF : (↑) '' (A \ {s, t}) ⊆ F) :
    ∃ (J₁ J₂ : Set V) (W₁ W₂ : Set (OnePoint V)),
      IsPrimitiveLink J₁ s t ∧ IsPrimitiveLink J₂ s t ∧
      J₁ ∩ J₂ = {s, t} ∧
      J₁ ∪ J₂ = C ∧
      IsOpen W₁ ∧ IsOpen W₂ ∧
      IsConnected W₁ ∧ IsConnected W₂ ∧
      Disjoint W₁ W₂ ∧
      W₁ ∪ W₂ = F \ ((↑) '' A) ∧
      frontier W₁ = (↑) '' (J₁ ∪ A) ∧
      frontier W₂ = (↑) '' (J₂ ∪ A) := by
  let : FiniteDimensional ℝ V := .of_fact_finrank_eq_two
  have hs : s ∈ C := (hAJ.ge (by simp)).2
  have ht : t ∈ C := (hAJ.ge (by simp)).2
  obtain ⟨J₁, J₂, hJ₁, hJ₂, hJcover, hJmeet⟩ :=
    hC.exists_two_arcs hCpoly.isCompact hs ht hst
  let θ : Fin 3 → Set V := fun i ↦
    if i = 0 then J₁ else if i = 1 then J₂ else A
  have hθ0 : θ 0 = J₁ := rfl
  have hθ1 : θ 1 = J₂ := rfl
  have hθ2 : θ 2 = A := rfl
  have hJ₁sub : J₁ ⊆ C := hJcover ▸ subset_union_left
  have hJ₂sub : J₂ ⊆ C := hJcover ▸ subset_union_right
  have hsA : s ∈ A := hA.left_mem
  have htA : t ∈ A := hA.right_mem
  have hJ₁A : J₁ ∩ A = {s, t} := by
    refine subset_antisymm ?_ ?_
    · intro x ⟨hxJ, hxA⟩
      have : x ∈ A ∩ C := ⟨hxA, hJ₁sub hxJ⟩
      rwa [hAJ] at this
    · intro x hx
      rw [mem_insert_iff, mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨hJ₁.left_mem, hsA⟩
      · exact ⟨hJ₁.right_mem, htA⟩
  have hJ₂A : J₂ ∩ A = {s, t} := by
    refine subset_antisymm ?_ ?_
    · intro x ⟨hxJ, hxA⟩
      have : x ∈ A ∩ C := ⟨hxA, hJ₂sub hxJ⟩
      rwa [hAJ] at this
    · intro x hx
      rw [mem_insert_iff, mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨hJ₂.left_mem, hsA⟩
      · exact ⟨hJ₂.right_mem, htA⟩
  have hθlink : ∀ i, IsPrimitiveLink (θ i) s t := by
    intro i
    fin_cases i <;> simp only [θ, Fin.isValue] <;> assumption
  have hθpoly : ∀ i, IsSegmentFigure (θ i) := by
    intro i
    fin_cases i
    · exact hCpoly.of_isPrimitiveLink_subset hJ₁ hJ₁sub
    · exact hCpoly.of_isPrimitiveLink_subset hJ₂ hJ₂sub
    · exact hApoly
  have hθmeet : ∀ i j, i ≠ j → θ i ∩ θ j = {s, t} := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hJmeet
    · exact hJ₁A
    · exact (inter_comm _ _).trans hJmeet
    · exact (hij rfl).elim
    · exact hJ₂A
    · exact (inter_comm _ _).trans hJ₁A
    · exact (inter_comm _ _).trans hJ₂A
    · exact (hij rfl).elim
  have hΘset : (⋃ i, θ i) = C ∪ A := by
    ext u
    simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨i, hu⟩
      fin_cases i
      · exact Or.inl (hJcover ▸ Or.inl (hθ0 ▸ hu))
      · exact Or.inl (hJcover ▸ Or.inr (hθ1 ▸ hu))
      · exact Or.inr (hθ2 ▸ hu)
    · rintro (hu | hu)
      · rw [← hJcover] at hu
        rcases hu with hu | hu
        · exact ⟨0, hθ0 ▸ hu⟩
        · exact ⟨1, hθ1 ▸ hu⟩
      · exact ⟨2, hθ2 ▸ hu⟩
  obtain ⟨W, hWopen, hWconn, hWdisj, hWcover, hWfront⟩ :=
    IsPrimitiveLink.exists_three_regions_theta hst θ hθlink hθpoly hθmeet
  have hfront1 : ⋃ j ∈ ({(1 : Fin 3)}ᶜ : Set (Fin 3)), θ j = J₁ ∪ A := by
    ext u
    simp only [mem_iUnion, mem_compl_iff, mem_singleton_iff, mem_union]
    constructor
    · rintro ⟨j, hj, huj⟩
      fin_cases j
      · exact Or.inl (hθ0 ▸ huj)
      · exact (hj rfl).elim
      · exact Or.inr (hθ2 ▸ huj)
    · rintro (hu | hu)
      · exact ⟨0, by decide, hθ0 ▸ hu⟩
      · exact ⟨2, by decide, hθ2 ▸ hu⟩
  have hfront0 : ⋃ j ∈ ({(0 : Fin 3)}ᶜ : Set (Fin 3)), θ j = J₂ ∪ A := by
    ext u
    simp only [mem_iUnion, mem_compl_iff, mem_singleton_iff, mem_union]
    constructor
    · rintro ⟨j, hj, huj⟩
      fin_cases j
      · exact (hj rfl).elim
      · exact Or.inl (hθ1 ▸ huj)
      · exact Or.inr (hθ2 ▸ huj)
    · rintro (hu | hu)
      · exact ⟨1, by decide, hθ1 ▸ hu⟩
      · exact ⟨2, by decide, hθ2 ▸ hu⟩
  have hfront2 : ⋃ j ∈ ({(2 : Fin 3)}ᶜ : Set (Fin 3)), θ j = C := by
    ext u
    simp only [mem_iUnion, mem_compl_iff, mem_singleton_iff]
    constructor
    · rintro ⟨j, hj, huj⟩
      fin_cases j
      · exact hJcover ▸ Or.inl (hθ0 ▸ huj)
      · exact hJcover ▸ Or.inr (hθ1 ▸ huj)
      · exact (hj rfl).elim
    · intro hu
      rw [← hJcover] at hu
      rcases hu with hu | hu
      · exact ⟨0, by decide, hθ0 ▸ hu⟩
      · exact ⟨1, by decide, hθ1 ▸ hu⟩
  obtain ⟨x, hx⟩ := hA.diff_endpoints_nonempty
  have hWall : (⋃ i, W i) = W 1 ∪ W 0 ∪ W 2 := by
    ext z
    simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i
      · exact Or.inl (Or.inr hi)
      · exact Or.inl (Or.inl hi)
      · exact Or.inr hi
    · rintro ((hz | hz) | hz)
      · exact ⟨1, hz⟩
      · exact ⟨0, hz⟩
      · exact ⟨2, hz⟩
  refine ⟨J₁, J₂, W 1, W 0, hJ₁, hJ₂, hJmeet, hJcover,
    hWopen 1, hWopen 0, hWconn 1, hWconn 0, hWdisj (by decide), ?_,
    (hWfront 1).trans (congrArg _ hfront1), (hWfront 0).trans (congrArg _ hfront0)⟩
  rw [hF]
  apply union_eq_connectedComponentIn_sdiff (hWconn 1).isPreconnected
    (hWconn 0).isPreconnected (W := W 2) (t := (x : OnePoint V))
  · rw [← hWall, hWcover, hΘset, image_union, compl_union, ← Set.sdiff_eq]
  · rw [hWfront 2, hfront2, compl_compl]
  · exact ⟨mem_image_of_mem _ hx.1, hF ▸ hAF ⟨x, hx, rfl⟩⟩
  · apply frontier_subset_closure
    rw [hWfront 1, hfront1]
    exact mem_image_of_mem _ (Or.inr hx.1)
  · apply frontier_subset_closure
    rw [hWfront 0, hfront0]
    exact mem_image_of_mem _ (Or.inr hx.1)

/-- Two disjoint crosscuts of the same polygonal region cannot have alternating endpoints. -/
theorem IsCircuit.not_alternating_crosscut {C A B : Set V} (hC : IsCircuit C)
    (hCpoly : IsSegmentFigure C) (hA : IsPrimitiveLink A s₁ s₂)
    (hApoly : IsSegmentFigure A) (hB : IsPrimitiveLink B t₁ t₂) (hs₁₂ : s₁ ≠ s₂)
    {F : Set (OnePoint V)} {q : OnePoint V}
    (hF : F = connectedComponentIn ((↑) '' C)ᶜ q)
    (hAB : Disjoint A B)
    (hAJ : A ∩ C = {s₁, s₂})
    (hAF : (↑) '' (A \ {s₁, s₂}) ⊆ F)
    (hBF : (↑) '' (B \ {t₁, t₂}) ⊆ F)
    {J₁ J₂ : Set V} (hJ₁ : IsPrimitiveLink J₁ s₁ s₂) (hJ₂ : IsPrimitiveLink J₂ s₁ s₂)
    (hJmeet : J₁ ∩ J₂ = {s₁, s₂})
    (hJcover : J₁ ∪ J₂ = C) :
    ¬ (t₁ ∈ J₁ \ {s₁, s₂} ∧ t₂ ∈ J₂ \ {s₁, s₂}) := by
  rintro ⟨ht₁, ht₂⟩
  obtain ⟨K₁, K₂, W₁, W₂, hK₁, hK₂, -, hKcover, hW1o, hW2o, -, -, hWdisj, hWunion, hfr1, hfr2⟩ :=
    hC.exists_two_regions_crosscut hCpoly hA hApoly hF hs₁₂ hAJ hAF
  have hK₁sub : K₁ ⊆ J₁ ∪ J₂ :=
    (hKcover.trans hJcover.symm) ▸ subset_union_left
  have hK₂sub : K₂ ⊆ J₁ ∪ J₂ :=
    (hKcover.trans hJcover.symm) ▸ subset_union_right
  have hinterB : IsConnected (B \ {t₁, t₂}) := hB.isConnected_diff_endpoints
  have hBimg : (↑) '' (B \ {t₁, t₂}) ⊆ W₁ ∪ W₂ := by
    rw [hWunion]
    intro p hp
    obtain ⟨x, hx, rfl⟩ := hp
    refine ⟨hBF ⟨x, hx, rfl⟩, ?_⟩
    intro hpA
    obtain ⟨y, hyA, hye⟩ := hpA
    exact hAB.notMem_of_mem_right hx.1 (OnePoint.coe_injective hye ▸ hyA)
  have hBconn : IsConnected (OnePoint.some '' (B \ {t₁, t₂})) :=
    hinterB.image (OnePoint.some : V → OnePoint V) OnePoint.continuous_coe.continuousOn
  have hBside : OnePoint.some '' (B \ {t₁, t₂}) ⊆ W₁ ∨
      OnePoint.some '' (B \ {t₁, t₂}) ⊆ W₂ :=
    hBconn.isPreconnected.subset_or_subset hW1o hW2o hWdisj hBimg
  have ht₂cl : t₂ ∈ closure (B \ {t₁, t₂}) :=
    hB.subset_closure_diff_endpoints hB.right_mem
  have ht₁cl : t₁ ∈ closure (B \ {t₁, t₂}) :=
    hB.subset_closure_diff_endpoints hB.left_mem
  have hFsub : F ⊆ ((↑) '' C)ᶜ := by
    rw [hF]
    exact connectedComponentIn_subset _ _
  have hnotW {W : Set (OnePoint V)} {x : V} (hW : W ⊆ F \ ((↑) '' A))
      (hxJ : x ∈ C) : (x : OnePoint V) ∉ W :=
    fun hxW ↦ hFsub (sdiff_subset (hW hxW)) ⟨x, hxJ, rfl⟩
  have hend_mem {K : Set V} {W : Set (OnePoint V)}
      (hfront : frontier W = (↑) '' (K ∪ A))
      (hWsub : W ⊆ F \ ((↑) '' A))
      (hBsub : (↑) '' (B \ {t₁, t₂}) ⊆ W) (x : V)
      (hxcl : x ∈ closure (B \ {t₁, t₂})) (hxB : x ∈ B)
      (hxJ : x ∈ C) : x ∈ K := by
    have hxclW : (x : OnePoint V) ∈ closure W :=
      closure_mono hBsub <|
        image_closure_subset_closure_image OnePoint.continuous_coe ⟨x, hxcl, rfl⟩
    have hxfr : (x : OnePoint V) ∈ frontier W := by
      have : (x : OnePoint V) ∈ W ∪ frontier W := by
        rw [← closure_eq_self_union_frontier]
        exact hxclW
      exact this.resolve_left (hnotW hWsub hxJ)
    rw [hfront, mem_image] at hxfr
    obtain ⟨z, hz, hze⟩ := hxfr
    have hz' : z = x := OnePoint.coe_injective hze
    subst z
    rcases hz with hzK | hzA
    · exact hzK
    · exact (hAB.notMem_of_mem_right hxB hzA).elim
  have hfalse (K : Set V) (hK : IsPrimitiveLink K s₁ s₂)
      (hKsub : K ⊆ J₁ ∪ J₂) (ht₁K : t₁ ∈ K) (ht₂K : t₂ ∈ K) : False := by
    have hKcover : K \ {s₁, s₂} ⊆ J₂ᶜ ∪ J₁ᶜ := by
      intro z hz
      have hzab : z ∉ J₁ ∩ J₂ := hJmeet ▸ hz.2
      rcases hKsub hz.1 with hz1 | hz2
      · exact Or.inl fun hz2' ↦ hzab ⟨hz1, hz2'⟩
      · exact Or.inr fun hz1' ↦ hzab ⟨hz1', hz2⟩
    have ht₁not : t₁ ∉ J₂ := fun h ↦ ht₁.2 (hJmeet ▸ ⟨ht₁.1, h⟩)
    have ht₂not : t₂ ∉ J₁ := fun h ↦ ht₂.2 (hJmeet ▸ ⟨h, ht₂.1⟩)
    obtain ⟨z, hzK, hzcompl⟩ := hK.isConnected_diff_endpoints.isPreconnected
      J₂ᶜ J₁ᶜ hJ₂.isClosed.isOpen_compl hJ₁.isClosed.isOpen_compl hKcover
      ⟨t₁, ⟨ht₁K, ht₁.2⟩, ht₁not⟩ ⟨t₂, ⟨ht₂K, ht₂.2⟩, ht₂not⟩
    rcases hKsub hzK.1 with hz1 | hz2
    · exact hzcompl.2 hz1
    · exact hzcompl.1 hz2
  have ht₁J : t₁ ∈ C := hJcover ▸ Or.inl ht₁.1
  have ht₂J : t₂ ∈ C := hJcover ▸ Or.inr ht₂.1
  have ht₁B : t₁ ∈ B := hB.left_mem
  have ht₂B : t₂ ∈ B := hB.right_mem
  have hW1sub : W₁ ⊆ F \ ((↑) '' A) := hWunion ▸ subset_union_left
  have hW2sub : W₂ ⊆ F \ ((↑) '' A) := hWunion ▸ subset_union_right
  rcases hBside with hW1 | hW2
  · exact hfalse K₁ hK₁ hK₁sub
      (hend_mem hfr1 hW1sub hW1 t₁ ht₁cl ht₁B ht₁J)
      (hend_mem hfr1 hW1sub hW1 t₂ ht₂cl ht₂B ht₂J)
  · exact hfalse K₂ hK₂ hK₂sub
      (hend_mem hfr2 hW2sub hW2 t₁ ht₁cl ht₁B ht₁J)
      (hend_mem hfr2 hW2sub hW2 t₂ ht₂cl ht₂B ht₂J)

end
