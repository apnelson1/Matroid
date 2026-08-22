module

public import Matroid.ForMathlib.Geometry.PolygonalPath.ThetaCurve

/-!
# Polygonal crosscuts

The theta-curve theorem gives the standard crosscut theorem for a polygonal Jordan curve: an
embedded arc across one complementary region splits that region into two.  A second disjoint
crosscut cannot have alternating endpoints.

The proofs split the polygon boundary into two arcs and apply the polygonal theta-curve theorem.

-/

open Function Set Topology Metric
open scoped unitInterval

namespace Polygon

public noncomputable section

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (Module.finrank ℝ V = 2)] {s t s₁ s₂ t₁ t₂ : V}

/-- **Crosscut theorem.** A simple polygon bounds two regions; a simple arc through one region,
meeting the polygon exactly at its endpoints, splits that region into two. -/
theorem IsSimple.exists_two_regions_crosscut {n : ℕ} {p : Polygon V n} (hp : p.IsSimple ℝ)
    {F : Set (OnePoint V)} {q : OnePoint V} (hq : q ∈ ((↑) '' p.boundary ℝ)ᶜ)
    {A : PolygonalPath s t} (hF : F = connectedComponentIn ((↑) '' p.boundary ℝ)ᶜ q) (hst : s ≠ t)
    (hs : s ∈ p.boundary ℝ) (ht : t ∈ p.boundary ℝ) (hA : A.IsSimple)
    (hAJ : A.toSet ∩ p.boundary ℝ = {s, t}) (hAF : (↑) '' (A.toSet \ {s, t}) ⊆ F) :
    ∃ (J₁ : PolygonalPath s t) (J₂ : PolygonalPath t s) (W₁ W₂ : Set (OnePoint V)),
      J₁.IsSimple ∧ J₂.IsSimple ∧
      J₁.toSet ∩ J₂.toSet = {s, t} ∧
      J₁.toSet ∪ J₂.toSet = p.boundary ℝ ∧
      IsOpen W₁ ∧ IsOpen W₂ ∧
      IsConnected W₁ ∧ IsConnected W₂ ∧
      Disjoint W₁ W₂ ∧
      W₁ ∪ W₂ = F \ ((↑) '' A.toSet) ∧
      frontier W₁ = (↑) '' (J₁.toSet ∪ A.toSet) ∧
      frontier W₂ = (↑) '' (J₂.toSet ∪ A.toSet) := by
  obtain ⟨J₁, J₂, hJ₁, hJ₂, hJmeet, hJcover⟩ := hp.exists_arcs hs ht hst
  let θ : Fin 3 → PolygonalPath s t := fun i ↦
    if i = 0 then J₁ else if i = 1 then J₂.reverse else A
  have hθ0 : θ 0 = J₁ := rfl
  have hθ1 : θ 1 = J₂.reverse := rfl
  have hθ2 : θ 2 = A := rfl
  have hJ₁sub : J₁.toSet ⊆ p.boundary ℝ := hJcover ▸ subset_union_left
  have hJ₂sub : J₂.toSet ⊆ p.boundary ℝ := hJcover ▸ subset_union_right
  have hsA : s ∈ A.toSet := A.mem_toSet_of_mem_vertices A.first_mem_vertices
  have htA : t ∈ A.toSet := A.mem_toSet_of_mem_vertices A.last_mem_vertices
  have hJ₁A : J₁.toSet ∩ A.toSet = {s, t} := by
    refine subset_antisymm ?_ ?_
    · intro x ⟨hxJ, hxA⟩
      have : x ∈ A.toSet ∩ p.boundary ℝ := ⟨hxA, hJ₁sub hxJ⟩
      rwa [hAJ] at this
    · intro x hx
      rw [mem_insert_iff, mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨J₁.mem_toSet_of_mem_vertices J₁.first_mem_vertices, hsA⟩
      · exact ⟨J₁.mem_toSet_of_mem_vertices J₁.last_mem_vertices, htA⟩
  have hJ₂A : J₂.toSet ∩ A.toSet = {s, t} := by
    refine subset_antisymm ?_ ?_
    · intro x ⟨hxJ, hxA⟩
      have : x ∈ A.toSet ∩ p.boundary ℝ := ⟨hxA, hJ₂sub hxJ⟩
      rwa [hAJ] at this
    · intro x hx
      rw [mem_insert_iff, mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ⟨J₂.mem_toSet_of_mem_vertices J₂.last_mem_vertices, hsA⟩
      · exact ⟨J₂.mem_toSet_of_mem_vertices J₂.first_mem_vertices, htA⟩
  have hθsimple : ∀ i, (θ i).IsSimple := by
    intro i
    fin_cases i
    · simpa [hθ0] using hJ₁
    · simpa [hθ1] using (PolygonalPath.isSimple_reverse.mpr hJ₂)
    · simpa [hθ2] using hA
  have hθtoSet (i : Fin 3) : (θ i).toSet =
      if i.val = 0 then J₁.toSet else if i.val = 1 then J₂.toSet else A.toSet := by
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => exact PolygonalPath.toSet_reverse (P := J₂)
    | ⟨2, _⟩ => rfl
  have hθmeet : ∀ i j, i ≠ j → (θ i).toSet ∩ (θ j).toSet = {s, t} := by
    intro i j hij
    rw [hθtoSet i, hθtoSet j]
    fin_cases i <;> fin_cases j <;> simp_all [inter_comm]
  have hΘset : (⋃ i, (θ i).toSet) = p.boundary ℝ ∪ A.toSet := by
    ext u
    simp only [mem_iUnion, mem_union]
    constructor
    · rintro ⟨i, hu⟩
      fin_cases i
      · exact Or.inl (hJcover ▸ Or.inl (hθ0 ▸ hu))
      · exact Or.inl (hJcover ▸ Or.inr (PolygonalPath.toSet_reverse (P := J₂) ▸ hθ1 ▸ hu))
      · exact Or.inr (hθ2 ▸ hu)
    · rintro (hu | hu)
      · rw [← hJcover] at hu
        rcases hu with hu | hu
        · exact ⟨0, hθ0 ▸ hu⟩
        · exact ⟨1, hθ1 ▸ PolygonalPath.toSet_reverse (P := J₂) ▸ hu⟩
      · exact ⟨2, hθ2 ▸ hu⟩
  obtain ⟨W, hWopen, hWconn, hWdisj, hWcover, hWfront⟩ :=
    PolygonalPath.exists_three_regions_theta hst θ hθsimple hθmeet
  have hfront1 : ⋃ j ∈ ({(1 : Fin 3)}ᶜ : Set (Fin 3)), (θ j).toSet = J₁.toSet ∪ A.toSet := by
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
  have hfront0 : ⋃ j ∈ ({(0 : Fin 3)}ᶜ : Set (Fin 3)), (θ j).toSet = J₂.toSet ∪ A.toSet := by
    ext u
    simp only [mem_iUnion, mem_compl_iff, mem_singleton_iff, mem_union]
    constructor
    · rintro ⟨j, hj, huj⟩
      fin_cases j
      · exact (hj rfl).elim
      · exact Or.inl (PolygonalPath.toSet_reverse (P := J₂) ▸ hθ1 ▸ huj)
      · exact Or.inr (hθ2 ▸ huj)
    · rintro (hu | hu)
      · exact ⟨1, by decide, hθ1 ▸ PolygonalPath.toSet_reverse (P := J₂) ▸ hu⟩
      · exact ⟨2, by decide, hθ2 ▸ hu⟩
  have hfront2 : ⋃ j ∈ ({(2 : Fin 3)}ᶜ : Set (Fin 3)), (θ j).toSet = p.boundary ℝ := by
    ext u
    simp only [mem_iUnion, mem_compl_iff, mem_singleton_iff]
    constructor
    · rintro ⟨j, hj, huj⟩
      fin_cases j
      · exact hJcover ▸ Or.inl (hθ0 ▸ huj)
      · exact hJcover ▸ Or.inr (PolygonalPath.toSet_reverse (P := J₂) ▸ hθ1 ▸ huj)
      · exact (hj rfl).elim
    · intro hu
      rw [← hJcover] at hu
      rcases hu with hu | hu
      · exact ⟨0, by decide, hθ0 ▸ hu⟩
      · exact ⟨1, by decide, hθ1 ▸ PolygonalPath.toSet_reverse (P := J₂) ▸ hu⟩
  have hW2sub : W 2 ⊆ ((↑) '' (⋃ i, (θ i).toSet))ᶜ :=
    (subset_iUnion W 2).trans hWcover.subset
  have hW2J : Disjoint (W 2) ((↑) '' p.boundary ℝ) := by
    refine (subset_compl_iff_disjoint_right.mp (hW2sub.trans (compl_subset_compl.mpr ?_)))
    exact image_mono (hΘset ▸ subset_union_left)
  let _ := hp.neZero
  have hJct : IsJordanCurve (p.boundary ℝ) := hp.isJordanCurve 0
  obtain ⟨w2, hw2⟩ := (hWconn 2).nonempty
  have hW2eq : W 2 = connectedComponentIn ((↑) '' p.boundary ℝ)ᶜ w2 :=
    eq_connectedComponentIn_of_frontier_subset (hWopen 2) (hWconn 2).isPreconnected hW2J
      (by rw [hWfront 2, hfront2]) hw2
  have hinter : (A.toSet \ {s, t}).Nonempty := by
    have hsa : A.IsSimpleArcOrLoop := Or.inl ⟨hA, A.length_pos_of_ne hst⟩
    rw [hsa.toSet_diff_endpoints]
    exact (nonempty_Ioo.2 (zero_lt_one : (0 : I) < 1)).image _
  have hFW : F ≠ W 2 := by
    intro hEq
    obtain ⟨x, hx⟩ := hinter
    have hxF : (x : OnePoint V) ∈ F := hAF ⟨x, hx, rfl⟩
    have hxW : (x : OnePoint V) ∉ W 2 := by
      have hxΘ : (x : OnePoint V) ∈ (↑) '' (⋃ i, (θ i).toSet) :=
        ⟨x, mem_iUnion.mpr ⟨2, hθ2 ▸ hx.1⟩, rfl⟩
      exact fun h ↦ hW2sub h hxΘ
    exact hxW (hEq ▸ hxF)
  have hw2J : w2 ∉ (↑) '' p.boundary ℝ := hW2J.notMem_of_mem_left hw2
  have hFside := hJct.connectedComponentIn_onePoint_eq_inside_or_outside hq
  have hWside := hJct.connectedComponentIn_onePoint_eq_inside_or_outside hw2J
  have hpartition : F ∪ W 2 = ((↑) '' p.boundary ℝ)ᶜ := by
    rw [← hF] at hFside
    rw [← hW2eq] at hWside
    rcases hFside with hFi | hFo <;> rcases hWside with hWi | hWo
    · exact absurd (hFi.trans hWi.symm) hFW
    · rw [hFi, hWo]
      exact hJct.insideOnePoint_union_outsideOnePoint
    · rw [hFo, hWi, union_comm]
      exact hJct.insideOnePoint_union_outsideOnePoint
    · exact absurd (hFo.trans hWo.symm) hFW
  have hFWdisj : Disjoint F (W 2) := by
    rw [hF, hW2eq, disjoint_iff_inter_eq_empty]
    ext z
    simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
    intro hzF hzW
    exact hFW <| by
      rw [hF, hW2eq]
      exact (connectedComponentIn_eq hzF).trans (connectedComponentIn_eq hzW).symm
  have hW2A : Disjoint (W 2) ((↑) '' A.toSet) :=
    subset_compl_iff_disjoint_right.mp <|
      hW2sub.trans (compl_subset_compl.mpr (image_mono (hΘset ▸ subset_union_right)))
  have hW01 : W 1 ∪ W 0 = F \ ((↑) '' A.toSet) := by
    have hW012 : (⋃ i, W i) = W 1 ∪ W 0 ∪ W 2 := by
      ext z
      simp only [mem_iUnion, mem_union]
      constructor
      · rintro ⟨i, hi⟩
        fin_cases i
        · exact Or.inl (Or.inr hi)
        · exact Or.inl (Or.inl hi)
        · exact Or.inr hi
      · rintro ((h | h) | h)
        · exact ⟨1, h⟩
        · exact ⟨0, h⟩
        · exact ⟨2, h⟩
    have hcover' : W 1 ∪ W 0 ∪ W 2 = ((↑) '' p.boundary ℝ)ᶜ \ ((↑) '' A.toSet) := by
      rw [← hW012, hWcover, hΘset, image_union, compl_union, ← Set.sdiff_eq]
    have hFdiff : F \ ((↑) '' A.toSet) ∪ W 2 =
        ((↑) '' p.boundary ℝ)ᶜ \ ((↑) '' A.toSet) := by
      rw [← hpartition, union_sdiff_distrib, sdiff_eq_left.mpr hW2A]
    have hdisj01 : Disjoint (W 1 ∪ W 0) (W 2) :=
      (hWdisj (by decide : (1 : Fin 3) ≠ 2)).union_left
        (hWdisj (by decide : (0 : Fin 3) ≠ 2))
    apply_fun (fun s ↦ s \ W 2) at hcover'
    rw [union_sdiff_right, sdiff_eq_left.mpr hdisj01, ← hFdiff, union_sdiff_right,
      sdiff_eq_left.mpr (hFWdisj.mono_left sdiff_subset)] at hcover'
    exact hcover'
  refine ⟨J₁, J₂, W 1, W 0, hJ₁, hJ₂, hJmeet, hJcover, hWopen 1, hWopen 0, hWconn 1, hWconn 0,
    hWdisj (by decide : (1 : Fin 3) ≠ 0), hW01, ?_, ?_⟩
  · rw [hWfront 1, hfront1]
  · rw [hWfront 0, hfront0]

/-- Two disjoint crosscuts of the same polygonal region cannot have alternating endpoints. -/
theorem IsSimple.not_alternating_crosscut {n : ℕ} {p : Polygon V n} (hp : p.IsSimple ℝ)
    {F : Set (OnePoint V)} {q : OnePoint V} (hq : q ∈ ((↑) '' p.boundary ℝ)ᶜ)
    {A : PolygonalPath s₁ s₂}
    (hF : F = connectedComponentIn ((↑) '' p.boundary ℝ)ᶜ q)
    {B : PolygonalPath t₁ t₂}
    (hA : A.IsSimple) (hB : B.IsSimple) (hAB : Disjoint A.toSet B.toSet)
    (hAJ : A.toSet ∩ p.boundary ℝ = {s₁, s₂})
    (hBJ : B.toSet ∩ p.boundary ℝ = {t₁, t₂})
    (hAF : (↑) '' (A.toSet \ {s₁, s₂}) ⊆ F)
    (hBF : (↑) '' (B.toSet \ {t₁, t₂}) ⊆ F)
    {J₁ : PolygonalPath s₁ s₂} {J₂ : PolygonalPath s₂ s₁}
    (hJ₁ : J₁.IsSimple) (hJ₂ : J₂.IsSimple)
    (hJmeet : J₁.toSet ∩ J₂.toSet = {s₁, s₂})
    (hJcover : J₁.toSet ∪ J₂.toSet = p.boundary ℝ) :
    ¬ (t₁ ∈ J₁.toSet \ {s₁, s₂} ∧ t₂ ∈ J₂.toSet \ {s₁, s₂}) := by
  rintro ⟨ht₁, ht₂⟩
  have hs₁₂ : s₁ ≠ s₂ := by
    intro h
    subst h
    have hlen : 0 < J₁.length := by
      refine Nat.pos_of_ne_zero fun h0 ↦ ?_
      have hnil : J₁ = PolygonalPath.nil s₁ := J₁.eq_nil_of_length_eq_zero h0
      have : t₁ ∈ ({s₁} : Set V) := by
        simpa [hnil] using ht₁.1
      exact ht₁.2 (by simp [this])
    exact hJ₁.ne hlen rfl
  have ht₁₂ : t₁ ≠ t₂ := fun h ↦
    ht₁.2 (hJmeet ▸ ⟨ht₁.1, h ▸ ht₂.1⟩)
  have hs₁J : s₁ ∈ p.boundary ℝ :=
    hJcover ▸ Or.inl (J₁.mem_toSet_of_mem_vertices J₁.first_mem_vertices)
  have hs₂J : s₂ ∈ p.boundary ℝ :=
    hJcover ▸ Or.inl (J₁.mem_toSet_of_mem_vertices J₁.last_mem_vertices)
  obtain ⟨K₁, K₂, W₁, W₂, hK₁, hK₂, -, hKcover, hW1o, hW2o, -, -, hWdisj, hWunion, hfr1, hfr2⟩ :=
    hp.exists_two_regions_crosscut hq hF hs₁₂ hs₁J hs₂J hA hAJ hAF
  have hK₁sub : K₁.toSet ⊆ J₁.toSet ∪ J₂.toSet :=
    (hKcover.trans hJcover.symm) ▸ subset_union_left
  have hK₂sub : K₂.toSet ⊆ J₁.toSet ∪ J₂.toSet :=
    (hKcover.trans hJcover.symm) ▸ subset_union_right
  have hBlen : 0 < B.length := B.length_pos_of_ne ht₁₂
  have hBsa : B.IsSimpleArcOrLoop := Or.inl ⟨hB, hBlen⟩
  have hinterB : IsConnected (B.toSet \ {t₁, t₂}) := by
    rw [hBsa.toSet_diff_endpoints]
    exact (isConnected_Ioo (zero_lt_one : (0 : I) < 1)).image
      (B.toPath : I → V) B.toPath.continuous.continuousOn
  have hBimg : (↑) '' (B.toSet \ {t₁, t₂}) ⊆ W₁ ∪ W₂ := by
    rw [hWunion]
    intro p hp
    obtain ⟨x, hx, rfl⟩ := hp
    refine ⟨hBF ⟨x, hx, rfl⟩, ?_⟩
    intro hpA
    obtain ⟨y, hyA, hye⟩ := hpA
    exact hAB.notMem_of_mem_right hx.1 (OnePoint.coe_injective hye ▸ hyA)
  have hBconn : IsConnected (OnePoint.some '' (B.toSet \ {t₁, t₂})) :=
    hinterB.image (OnePoint.some : V → OnePoint V) OnePoint.continuous_coe.continuousOn
  have hBside : OnePoint.some '' (B.toSet \ {t₁, t₂}) ⊆ W₁ ∨
      OnePoint.some '' (B.toSet \ {t₁, t₂}) ⊆ W₂ :=
    hBconn.isPreconnected.subset_or_subset hW1o hW2o hWdisj hBimg
  have ht₂cl : t₂ ∈ closure (B.toSet \ {t₁, t₂}) := by
    have hseg := B.segment_lastTip_subset_toSet hBlen
    have hlt := hB.lastTip_ne hBlen
    have hcl : t₂ ∈ closure (openSegment ℝ B.lastTip t₂) :=
      segment_subset_closure_openSegment (right_mem_segment ℝ B.lastTip t₂)
    rw [mem_closure_iff_nhds] at hcl ⊢
    intro U hU
    have hU' : U ∩ ball t₂ (dist t₁ t₂) ∈ nhds t₂ :=
      Filter.inter_mem hU (ball_mem_nhds t₂ (dist_pos.mpr ht₁₂))
    obtain ⟨z, hzU, hzo⟩ := hcl _ hU'
    have hzball : z ∈ ball t₂ (dist t₁ t₂) := hzU.2
    have hzt₁ : z ≠ t₁ := fun h ↦
      lt_irrefl (dist t₁ t₂) (by simpa [h] using mem_ball.mp hzball)
    have hzt₂ : z ≠ t₂ := fun h ↦
      hlt (right_mem_openSegment_iff.mp (show t₂ ∈ openSegment ℝ B.lastTip t₂ from h ▸ hzo))
    exact ⟨z, hzU.1, hseg (openSegment_subset_segment ℝ _ _ hzo), by simp [hzt₁, hzt₂]⟩
  have ht₁cl : t₁ ∈ closure (B.toSet \ {t₁, t₂}) := by
    have hseg := B.segment_firstTip_subset_toSet hBlen
    have hft := hB.firstTip_ne hBlen
    have hcl : t₁ ∈ closure (openSegment ℝ t₁ B.firstTip) :=
      segment_subset_closure_openSegment (left_mem_segment ℝ t₁ B.firstTip)
    rw [mem_closure_iff_nhds] at hcl ⊢
    intro U hU
    have hU' : U ∩ ball t₁ (dist t₁ t₂) ∈ nhds t₁ :=
      Filter.inter_mem hU (ball_mem_nhds t₁ (dist_pos.mpr ht₁₂))
    obtain ⟨z, hzU, hzo⟩ := hcl _ hU'
    have hzball : z ∈ ball t₁ (dist t₁ t₂) := hzU.2
    have hzt₂ : z ≠ t₂ := fun h ↦
      lt_irrefl (dist t₁ t₂) (by simpa [h, dist_comm] using mem_ball.mp hzball)
    have hzt₁ : z ≠ t₁ := fun h ↦
      hft (left_mem_openSegment_iff.mp (show t₁ ∈ openSegment ℝ t₁ B.firstTip from h ▸ hzo)).symm
    exact ⟨z, hzU.1, hseg (openSegment_subset_segment ℝ _ _ hzo), by simp [hzt₁, hzt₂]⟩
  have hFsub : F ⊆ ((↑) '' p.boundary ℝ)ᶜ := by
    rw [hF]
    exact connectedComponentIn_subset _ _
  have hnotW {W : Set (OnePoint V)} {x : V} (hW : W ⊆ F \ ((↑) '' A.toSet))
      (hxJ : x ∈ p.boundary ℝ) : (x : OnePoint V) ∉ W :=
    fun hxW ↦ hFsub (sdiff_subset (hW hxW)) ⟨x, hxJ, rfl⟩
  have hend_mem {K : PolygonalPath s₁ s₂} {W : Set (OnePoint V)}
      (hfront : frontier W = (↑) '' (K.toSet ∪ A.toSet))
      (hWsub : W ⊆ F \ ((↑) '' A.toSet))
      (hBsub : (↑) '' (B.toSet \ {t₁, t₂}) ⊆ W) (x : V)
      (hxcl : x ∈ closure (B.toSet \ {t₁, t₂})) (hxB : x ∈ B.toSet)
      (hxJ : x ∈ p.boundary ℝ) : x ∈ K.toSet := by
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
  have hfalse (K : PolygonalPath s₁ s₂) (hK : K.IsSimple)
      (hKsub : K.toSet ⊆ J₁.toSet ∪ J₂.toSet)
      (ht₁K : t₁ ∈ K.toSet) (ht₂K : t₂ ∈ K.toSet) : False := by
    have hKsa : K.IsSimpleArcOrLoop := Or.inl ⟨hK, K.length_pos_of_ne hs₁₂⟩
    have ht₁K' : t₁ ∈ K.toSet \ {s₁, s₂} := ⟨ht₁K, ht₁.2⟩
    have ht₂K' : t₂ ∈ K.toSet \ {s₁, s₂} := ⟨ht₂K, ht₂.2⟩
    rw [hKsa.toSet_diff_endpoints] at ht₁K' ht₂K'
    obtain ⟨u, hu, hu1⟩ := ht₁K'
    obtain ⟨v, hv, hv1⟩ := ht₂K'
    let a : I := min u v
    let b : I := max u v
    have hab : a ≤ b := min_le_max
    let C : Set V := K.toPath '' Icc a b
    have hCconn : IsPreconnected C :=
      (isConnected_Icc hab).isPreconnected.image _ K.toPath.continuous.continuousOn
    have hCI : Icc a b ⊆ Ioo (0 : I) 1 :=
      fun t ht ↦ ⟨(lt_min hu.1 hv.1).trans_le ht.1, ht.2.trans_lt (max_lt hu.2 hv.2)⟩
    have hCsubK : C ⊆ K.toSet \ {s₁, s₂} := by
      rw [hKsa.toSet_diff_endpoints]
      exact image_mono hCI
    have hCsubJ : C ⊆ J₁.toSet ∪ J₂.toSet :=
      (hCsubK.trans sdiff_subset).trans hKsub
    have ht₁C : t₁ ∈ C := ⟨u, ⟨min_le_left _ _, le_max_left _ _⟩, hu1⟩
    have ht₂C : t₂ ∈ C := ⟨v, ⟨min_le_right _ _, le_max_right _ _⟩, hv1⟩
    have hCu : (C ∩ (J₂.toSet)ᶜ).Nonempty :=
      ⟨t₁, ht₁C, fun h ↦ ht₁.2 (hJmeet ▸ ⟨ht₁.1, h⟩)⟩
    have hCv : (C ∩ (J₁.toSet)ᶜ).Nonempty :=
      ⟨t₂, ht₂C, fun h ↦ ht₂.2 (hJmeet ▸ ⟨h, ht₂.1⟩)⟩
    have hCcover : C ⊆ (J₂.toSet)ᶜ ∪ (J₁.toSet)ᶜ := by
      intro z hz
      have hzab : z ∉ ({s₁, s₂} : Set V) := (hCsubK hz).2
      rw [← hJmeet] at hzab
      rcases hCsubJ hz with hz1 | hz2
      · exact Or.inl fun hz2' ↦ hzab ⟨hz1, hz2'⟩
      · exact Or.inr fun hz1' ↦ hzab ⟨hz1', hz2⟩
    obtain ⟨z, hzC, hzcompl⟩ :=
      hCconn (J₂.toSet)ᶜ (J₁.toSet)ᶜ J₂.isClosed_toSet.isOpen_compl
        J₁.isClosed_toSet.isOpen_compl hCcover hCu hCv
    rcases hCsubJ hzC with hz1 | hz2
    · exact hzcompl.2 hz1
    · exact hzcompl.1 hz2
  have ht₁J : t₁ ∈ p.boundary ℝ := hJcover ▸ Or.inl ht₁.1
  have ht₂J : t₂ ∈ p.boundary ℝ := hJcover ▸ Or.inr ht₂.1
  have ht₁B : t₁ ∈ B.toSet := B.mem_toSet_of_mem_vertices B.first_mem_vertices
  have ht₂B : t₂ ∈ B.toSet := B.mem_toSet_of_mem_vertices B.last_mem_vertices
  have hW1sub : W₁ ⊆ F \ ((↑) '' A.toSet) := hWunion ▸ subset_union_left
  have hW2sub : W₂ ⊆ F \ ((↑) '' A.toSet) := hWunion ▸ subset_union_right
  rcases hBside with hW1 | hW2
  · exact hfalse K₁ hK₁ hK₁sub
      (hend_mem hfr1 hW1sub hW1 t₁ ht₁cl ht₁B ht₁J)
      (hend_mem hfr1 hW1sub hW1 t₂ ht₂cl ht₂B ht₂J)
  · exact hfalse K₂.reverse (PolygonalPath.isSimple_reverse.mpr hK₂)
      (PolygonalPath.toSet_reverse (P := K₂) ▸ hK₂sub)
      (hend_mem (by rw [PolygonalPath.toSet_reverse]; exact hfr2) hW2sub hW2 t₁ ht₁cl ht₁B ht₁J)
      (hend_mem (by rw [PolygonalPath.toSet_reverse]; exact hfr2) hW2sub hW2 t₂ ht₂cl ht₂B ht₂J)

end

end Polygon
