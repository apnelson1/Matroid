module

public import Matroid.MiniTauCeti.JCT.Geometry.PolygonalJordan
public import Matroid.MiniTauCeti.JCT.Topology.PrimitiveLink.Regions

/-!
# Polygonal theta regions

Local stars exhaust the complementary components supplied by pair separation.
Polygonal Jordan separation then supplies the hypotheses of that conditional result.
-/

@[expose] public section

open Set Topology Function Metric

namespace IsPrimitiveLink

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {a b : V}

private theorem endpoint_star_three (A : Fin 3 → Set V) (hab : a ≠ b)
    (hA : ∀ i, IsPrimitiveLink (A i) a b) (hpoly : ∀ i, IsSegmentFigure (A i))
    (hmeet : Pairwise fun i j ↦ A i ∩ A j = {a, b}) :
    ∃ r > 0, ∃ Y : Finset V, Y.card = 3 ∧ (Y : Set V) ⊆ sphere a r ∧
      closedBall a r ∩ (⋃ i, A i) = {a} ∪ ⋃ y ∈ Y, segment ℝ a y := by
  classical
  choose r₀ hr₀ hstar using fun i ↦ (hA i).exists_local_star_one hab (hpoly i)
  let r := min (dist a b / 2) (min (r₀ 0) (min (r₀ 1) (r₀ 2)))
  have hr : 0 < r := lt_min (half_pos (dist_pos.mpr hab))
    (lt_min (hr₀ 0) (lt_min (hr₀ 1) (hr₀ 2)))
  have hle (i : Fin 3) : r ≤ r₀ i := by
    have h := min_le_right (dist a b / 2) (min (r₀ 0) (min (r₀ 1) (r₀ 2)))
    fin_cases i
    · exact h.trans (min_le_left _ _)
    · exact h.trans ((min_le_right _ _).trans (min_le_left _ _))
    · exact h.trans ((min_le_right _ _).trans (min_le_right _ _))
  choose y hy using fun i ↦ (hstar i r hr (hle i)).exists
  have hyA (i) : y i ∈ A i := ((hy i).2.symm ▸ right_mem_segment ℝ a (y i)).2
  have hyn (i) : y i ≠ a := ne_of_mem_sphere (hy i).1 hr.ne'
  have hyb (i) : y i ≠ b := by
    intro heq
    have hdist : dist a b = r := by
      simpa only [heq, dist_comm] using mem_sphere.mp (hy i).1
    have := min_le_left (dist a b / 2) (min (r₀ 0) (min (r₀ 1) (r₀ 2)))
    change r ≤ dist a b / 2 at this
    linarith [dist_pos.mpr hab]
  have hinj : Injective y := by
    intro i j heq
    by_contra hij
    have hmem := (hmeet hij).subset ⟨hyA i, heq.symm ▸ hyA j⟩
    exact (show y i ∉ ({a, b} : Set V) by simp [hyn i, hyb i]) hmem
  refine ⟨r, hr, Finset.univ.image y, ?_, ?_, ?_⟩
  · simpa using Finset.card_image_of_injective Finset.univ hinj
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hz
    exact (hy i).1
  · have heq : closedBall a r ∩ (⋃ i, A i) = ⋃ i, segment ℝ a (y i) := by
      rw [inter_iUnion]
      exact iUnion_congr fun i ↦ (hy i).2
    rw [heq]
    ext z
    simp only [mem_iUnion, mem_union, mem_singleton_iff, Finset.mem_image, Finset.mem_univ,
      true_and]
    constructor
    · rintro ⟨i, hi⟩
      exact Or.inr ⟨y i, ⟨i, rfl⟩, hi⟩
    · rintro (rfl | ⟨w, ⟨i, rfl⟩, hi⟩)
      · exact ⟨0, left_mem_segment ..⟩
      · exact ⟨i, hi⟩

private theorem arm_star_two (A : Fin 3 → Set V)
    (hA : ∀ i, IsPrimitiveLink (A i) a b) (hpoly : ∀ i, IsSegmentFigure (A i))
    (hmeet : Pairwise fun i j ↦ A i ∩ A j = {a, b})
    (i : Fin 3) {p : V} (hp : p ∈ A i \ {a, b}) :
    ∃ r > 0, ∃ Y : Finset V, Y.card = 2 ∧ (Y : Set V) ⊆ sphere p r ∧
      closedBall p r ∩ (⋃ j, A j) = {p} ∪ ⋃ y ∈ Y, segment ℝ p y := by
  let K : Set V := ⋃ j : {j : Fin 3 // j ≠ i}, A j.1
  have hK : IsCompact K := isCompact_iUnion fun j ↦ (hA j.1).isCompact
  have hpK : p ∉ K := by
    intro h
    obtain ⟨j, hj⟩ := mem_iUnion.mp h
    exact hp.2 ((hmeet j.2.symm).subset ⟨hp.1, hj⟩)
  obtain ⟨δ, hδ, hdist⟩ := exists_pos_le_dist_of_notMem hK.isClosed hpK
  obtain ⟨r, hr, hrδ, Y, hYcard, hY, hstar⟩ :=
    (hA i).exists_local_star_two_le (hpoly i) hp.1 (Or.inr hp.2) (half_pos hδ)
  have hTK : (⋃ j, A j) = A i ∪ K := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      by_cases hji : j = i
      · exact Or.inl (hji ▸ hj)
      · exact Or.inr (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩)
    · rintro (h | h)
      · exact mem_iUnion.mpr ⟨i, h⟩
      · obtain ⟨j, hj⟩ := mem_iUnion.mp h
        exact mem_iUnion.mpr ⟨j.1, hj⟩
  have hball : closedBall p r ∩ K = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx, hxK⟩
    have hx' := mem_closedBall.mp hx
    linarith [hdist x hxK, dist_comm x p ▸ hx']
  refine ⟨r, hr, Y, hYcard, hY, ?_⟩
  rw [hTK, inter_union_distrib_left, hball, union_empty, hstar]

variable [Fact (Module.finrank ℝ V = 2)]

private theorem component_eq_region (A : Fin 3 → Set V) (hab : a ≠ b)
    (hA : ∀ i, IsPrimitiveLink (A i) a b) (hpoly : ∀ i, IsSegmentFigure (A i))
    (hmeet : Pairwise fun i j ↦ A i ∩ A j = {a, b}) (W : Fin 3 → Set V)
    (hcomp : ∀ i, ∃ w ∈ (⋃ k, A k)ᶜ, W i = connectedComponentIn (⋃ k, A k)ᶜ w)
    (hdisj : Pairwise fun i j ↦ Disjoint (W i) (W j))
    (hfront : ∀ i, frontier (W i) = ⋃ j ∈ ({i}ᶜ : Set (Fin 3)), A j)
    {z : V} (hz : z ∈ (⋃ k, A k)ᶜ) :
    ∃ i, connectedComponentIn (⋃ k, A k)ᶜ z = W i := by
  have hT : IsClosed (⋃ k, A k) := (isCompact_iUnion fun k ↦ (hA k).isCompact).isClosed
  obtain ⟨p, hp⟩ := frontier_connectedComponentIn_compl_nonempty
    ⟨a, mem_iUnion.mpr ⟨0, (hA 0).left_mem⟩⟩ hz
  have hpT := hT.frontier_connectedComponentIn_compl_subset hp
  by_cases he : p ∈ ({a, b} : Set V)
  · have hstar : ∃ r > 0, ∃ Y : Finset V, Y.card = 3 ∧ (Y : Set V) ⊆ sphere p r ∧
        closedBall p r ∩ (⋃ i, A i) = {p} ∪ ⋃ y ∈ Y, segment ℝ p y := by
      rcases he with rfl | he
      · exact endpoint_star_three A hab hA hpoly hmeet
      · obtain rfl := mem_singleton_iff.mp he
        exact endpoint_star_three A hab.symm (fun i ↦ (hA i).symm) hpoly
          (fun i j hij ↦ (hmeet hij).trans (pair_comm _ _))
    obtain ⟨r, hr, Y, hc, hY, hs⟩ := hstar
    apply exists_eq_connectedComponentIn_of_local_star hr (Finset.card_pos.mp (by omega)) hY hs
      (hc.trans (Fintype.card_fin 3).symm).le W hcomp hdisj ?_ ⟨p, hp, mem_ball_self hr⟩
    intro i
    refine ⟨p, ?_, mem_ball_self hr⟩
    rw [hfront i]
    have hne : i + 1 ≠ i := fun h ↦
      Fin.zero_ne_one.symm (add_left_cancel (h.trans (add_zero i).symm))
    refine mem_iUnion₂.mpr ⟨i + 1, hne, ?_⟩
    rcases he with rfl | he
    · exact (hA _).left_mem
    · exact mem_singleton_iff.mp he ▸ (hA _).right_mem
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hpT
    obtain ⟨r, hr, Y, hc, hY, hs⟩ := arm_star_two A hA hpoly hmeet i ⟨hi, he⟩
    have hcard : Y.card = Fintype.card {j : Fin 3 // j ≠ i} := by
      rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, Fintype.card_fin, hc]
    obtain ⟨j, hj⟩ := exists_eq_connectedComponentIn_of_local_star hr
      (Finset.card_pos.mp (by omega)) hY hs hcard.le
      (fun j : {j : Fin 3 // j ≠ i} ↦ W j.1) (fun j ↦ hcomp j.1)
      (fun j k hjk ↦ hdisj (Subtype.coe_ne_coe.mpr hjk))
      (fun j ↦ ⟨p, hfront j.1 ▸ mem_iUnion₂.mpr ⟨i, j.2.symm, hi⟩, mem_ball_self hr⟩)
      ⟨p, hp, mem_ball_self hr⟩
    exact ⟨j.1, hj⟩

/-- Every complementary component is a unique member of the supplied candidate family. -/
theorem existsUnique_region_eq_component (A : Fin 3 → Set V) (hab : a ≠ b)
    (hA : ∀ i, IsPrimitiveLink (A i) a b) (hpoly : ∀ i, IsSegmentFigure (A i))
    (hmeet : Pairwise fun i j ↦ A i ∩ A j = {a, b}) (W : Fin 3 → Set V)
    (hcomp : ∀ i, ∃ w ∈ (⋃ k, A k)ᶜ, W i = connectedComponentIn (⋃ k, A k)ᶜ w)
    (hfront : ∀ i, frontier (W i) = ⋃ j ∈ ({i}ᶜ : Set (Fin 3)), A j)
    {z : V} (hz : z ∈ (⋃ k, A k)ᶜ) :
    ∃! i, connectedComponentIn (⋃ k, A k)ᶜ z = W i := by
  have hinj := injective_regions A hA (fun i j hij ↦ (hmeet hij).subset) hfront
  have hd : Pairwise fun i j ↦ Disjoint (W i) (W j) := by
    intro i j hij
    obtain ⟨u, -, hu⟩ := hcomp i
    obtain ⟨v, -, hv⟩ := hcomp j
    refine disjoint_left.mpr fun x hxi hxj ↦ hij (hinj ?_)
    simp only [hu, hv] at hxi hxj ⊢
    exact (connectedComponentIn_eq hxi).trans (connectedComponentIn_eq hxj).symm
  obtain ⟨i, hi⟩ := component_eq_region A hab hA hpoly hmeet W hcomp hd hfront hz
  exact ⟨i, hi, fun j hj ↦ hinj (hj.symm.trans hi)⟩

/-- Polygonality makes the supplied candidate components exhaust the complement. -/
theorem iUnion_regions_eq_compl (A : Fin 3 → Set V) (hab : a ≠ b)
    (hA : ∀ i, IsPrimitiveLink (A i) a b) (hpoly : ∀ i, IsSegmentFigure (A i))
    (hmeet : Pairwise fun i j ↦ A i ∩ A j = {a, b}) (W : Fin 3 → Set V)
    (hcomp : ∀ i, ∃ w ∈ (⋃ k, A k)ᶜ, W i = connectedComponentIn (⋃ k, A k)ᶜ w)
    (hfront : ∀ i, frontier (W i) = ⋃ j ∈ ({i}ᶜ : Set (Fin 3)), A j) :
    (⋃ i, W i) = (⋃ i, A i)ᶜ := by
  apply subset_antisymm
  · apply iUnion_subset
    intro i
    obtain ⟨w, -, hw⟩ := hcomp i
    rw [hw]
    exact connectedComponentIn_subset ..
  · intro z hz
    obtain ⟨i, hi, -⟩ := existsUnique_region_eq_component A hab hA hpoly hmeet W hcomp hfront hz
    exact mem_iUnion.mpr ⟨i, hi ▸ mem_connectedComponentIn hz⟩

/-- Polygonal local stars show that the three candidate components exhaust the complement. -/
theorem regions_of_pair_separation (A : Fin 3 → Set V) (hab : a ≠ b)
    (hA : ∀ i, IsPrimitiveLink (A i) a b)
    (hpoly : ∀ i, IsSegmentFigure (A i))
    (hmeet : Pairwise fun i j ↦ A i ∩ A j = {a, b})
    (hsep : ∀ i, ∃ U W : Set V,
      IsOpen U ∧ IsOpen W ∧ IsConnected U ∧ IsConnected W ∧ Disjoint U W ∧
      U ∪ W = (⋃ j ∈ ({i}ᶜ : Set (Fin 3)), A j)ᶜ ∧
      frontier U = ⋃ j ∈ ({i}ᶜ : Set (Fin 3)), A j ∧
      frontier W = ⋃ j ∈ ({i}ᶜ : Set (Fin 3)), A j) :
    ∃ W : Fin 3 → Set V,
      (∀ i, IsOpen (W i)) ∧ (∀ i, IsConnected (W i)) ∧
      (Pairwise fun i j ↦ Disjoint (W i) (W j)) ∧
      (⋃ i, W i) = (⋃ i, A i)ᶜ ∧
      ∀ i, frontier (W i) = ⋃ j ∈ ({i}ᶜ : Set (Fin 3)), A j := by
  obtain ⟨W, hO, hC, hd, hcomp, hf⟩ :=
    candidate_regions_of_separation A hA (fun i j hij ↦ (hmeet hij).subset) hsep
  exact ⟨W, hO, hC, hd, iUnion_regions_eq_compl A hab hA hpoly hmeet W hcomp hf, hf⟩

variable {q : V}

/-- Three polygonal primitive links meeting only at their common endpoints bound three regions. -/
theorem regions (A : Fin 3 → Set V) (hab : a ≠ b)
    (hA : ∀ i, IsPrimitiveLink (A i) a b)
    (hpoly : ∀ i, IsSegmentFigure (A i))
    (hmeet : Pairwise fun i j ↦ A i ∩ A j = {a, b}) :
    ∃ W : Fin 3 → Set V,
      (∀ i, IsOpen (W i)) ∧ (∀ i, IsConnected (W i)) ∧
      (Pairwise fun i j ↦ Disjoint (W i) (W j)) ∧
      (⋃ i, W i) = (⋃ i, A i)ᶜ ∧
      ∀ i, frontier (W i) = ⋃ j ∈ ({i}ᶜ : Set (Fin 3)), A j := by
  apply regions_of_pair_separation A hab hA hpoly hmeet
  intro i
  let j : Fin 3 := i + 1
  let k : Fin 3 := i + 2
  have hjk : j ≠ k := fun h ↦
    absurd (add_left_cancel h) (by decide : (1 : Fin 3) ≠ 2)
  have hset : (⋃ t ∈ ({i}ᶜ : Set (Fin 3)), A t) = A j ∪ A k := by
    have heq : ({i}ᶜ : Set (Fin 3)) = {j, k} := by
      ext t
      fin_cases i <;> fin_cases t <;> simp [j, k]
    rw [heq]
    simp
  have hC := (hA j).isCircuit_union (hA k).symm hab (hmeet hjk).subset
  simpa only [hset] using
    hC.exists_complement_regions_of_isSegmentFigure ((hpoly j).union (hpoly k))

/-- A polygonal crosscut splits its prescribed complementary component into two regions. -/
theorem crosscut_regions {J₁ J₂ A : Set V} (hab : a ≠ b)
    (hJ₁ : IsPrimitiveLink J₁ a b) (hJ₂ : IsPrimitiveLink J₂ a b)
    (hA : IsPrimitiveLink A a b) (hmeet : J₁ ∩ J₂ = {a, b})
    (hpoly₁ : IsSegmentFigure J₁) (hpoly₂ : IsSegmentFigure J₂)
    (hpolyA : IsSegmentFigure A)
    (hAF : A \ {a, b} ⊆ connectedComponentIn (J₁ ∪ J₂)ᶜ q) :
    ∃ U V : Set V, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
      Disjoint U V ∧ U ∪ V = connectedComponentIn (J₁ ∪ J₂)ᶜ q \ A ∧
      frontier U = J₁ ∪ A ∧ frontier V = J₂ ∪ A := by
  have hJA {J : Set V} (hJ : IsPrimitiveLink J a b) (hsub : J ⊆ J₁ ∪ J₂) :
      J ∩ A = {a, b} := by
    apply subset_antisymm
    · rintro x ⟨hxJ, hxA⟩
      by_contra he
      exact connectedComponentIn_subset _ _ (hAF ⟨hxA, he⟩) (hsub hxJ)
    · intro x hx
      rcases hx with rfl | hx
      · exact ⟨hJ.left_mem, hA.left_mem⟩
      · obtain rfl := mem_singleton_iff.mp hx
        exact ⟨hJ.right_mem, hA.right_mem⟩
  have hJ₁A := hJA hJ₁ subset_union_left
  have hJ₂A := hJA hJ₂ subset_union_right
  let B : Fin 3 → Set V := ![J₁, J₂, A]
  have hB (i) : IsPrimitiveLink (B i) a b := by
    fin_cases i <;> assumption
  have hpolyB (i) : IsSegmentFigure (B i) := by
    fin_cases i <;> assumption
  have hmeetB : Pairwise fun i j ↦ B i ∩ B j = {a, b} := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hmeet
    · exact hJ₁A
    · exact (inter_comm _ _).trans hmeet
    · exact (hij rfl).elim
    · exact hJ₂A
    · exact (inter_comm _ _).trans hJ₁A
    · exact (inter_comm _ _).trans hJ₂A
    · exact (hij rfl).elim
  obtain ⟨W, hO, hC, hd, hcover, hf⟩ := regions B hab hB hpolyB hmeetB
  have hunion (C : Fin 3 → Set V) : (⋃ i, C i) = C 0 ∪ C 1 ∪ C 2 := by
    ext x
    simp [Fin.exists_fin_succ, or_assoc]
  simp only [hunion] at hcover hf
  have hfU : frontier (W 1) = J₁ ∪ A := by simpa [B] using hf 1
  have hfV : frontier (W 0) = J₂ ∪ A := by simpa [B] using hf 0
  have hfW : frontier (W 2) = J₁ ∪ J₂ := by simpa [B] using hf 2
  obtain ⟨t, ht⟩ := hA.diff_endpoints_nonempty
  refine ⟨W 1, W 0, hO 1, hO 0, hC 1, hC 0, hd (by decide), ?_, hfU, hfV⟩
  apply union_eq_connectedComponentIn_sdiff (S := (J₁ ∪ J₂)ᶜ) (t := t)
    (W := W 2) (hC 1).isPreconnected
    (hC 0).isPreconnected
  · simpa [B, compl_union, sdiff_eq, inter_assoc, union_assoc, union_comm,
      union_left_comm] using hcover
  · simpa only [compl_compl] using hfW.subset
  · exact ⟨ht.1, hAF ht⟩
  · exact frontier_subset_closure (hfU ▸ Or.inr ht.1)
  · exact frontier_subset_closure (hfV ▸ Or.inr ht.1)

end IsPrimitiveLink
