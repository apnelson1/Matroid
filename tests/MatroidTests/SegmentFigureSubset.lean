module

public import Matroid.ForMathlib.Geometry.SegmentFigure.Subset

/-! # Carrier-relative segment-figure subsets and interval gaps -/

open Set Topology

section Relative

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [ContinuousAdd V] [ContinuousSMul ℝ V] {S C : Set V}

-- Neither ambient Hausdorffness nor ambient closedness is available here.
example [T2Space S] (hS : IsSegmentFigure S) (hCS : C ⊆ S)
    (hc : IsClosed (Subtype.val ⁻¹' C : Set S)) (hconn : IsPreconnected C) :
    IsSegmentFigure C := hS.of_isClosed_preimage_isPreconnected hCS hc hconn

example [T2Space S] (hS : IsSegmentFigure S) (hCS : C ⊆ S)
    (hc : IsClosed (Subtype.val ⁻¹' C : Set S)) [Finite (ConnectedComponents C)] :
    IsSegmentFigure C :=
  (hS.iff_isClosed_preimage_finite_connectedComponents hCS).mpr ⟨hc, inferInstance⟩

example [T2Space S] (hS : IsSegmentFigure S) : IsSegmentFigure (∅ : Set V) :=
  hS.of_isClosed_preimage_isPreconnected (empty_subset S) (by simp) isPreconnected_empty

example {a b : V} [T2Space ↥(segment ℝ a b)] (hsub : C ⊆ segment ℝ a b)
    (hc : IsCompact C) (hconn : IsConnected C) : ∃ x y, C = segment ℝ x y :=
  hc.exists_eq_segment_of_isConnected_of_subset_segment hconn hsub

-- A singleton carrier is Hausdorff even when the ambient topology is not.
example (a : V) : IsSegmentFigure ({a} : Set V) := by
  have : Subsingleton ↥({a} : Set V) := by infer_instance
  exact (isSegmentFigure_singleton a).of_isClosed_preimage_isPreconnected
    subset_rfl (by simp) isPreconnected_singleton

-- This is the carrier-relative consumer proposed for finite straight-line spaces.
example {G : GraphLike V} [G.Finite] (hG : G.IsStraightLine)
    (hsub : C ⊆ G.carrier) (hc : IsClosed (Subtype.val ⁻¹' C : Set G.carrier))
    (hconn : IsPreconnected C) : IsSegmentFigure C :=
  hG.isSegmentFigure_carrier.of_isClosed_preimage_isPreconnected hsub hc hconn

end Relative

section Order

-- The attachment lemma has no vector-space, real-scalar, or connected-order assumptions.
example {α X : Type*} [LinearOrder α] [BoundedOrder α]
    [TopologicalSpace α] [OrderTopology α] [CompactSpace α]
    [TopologicalSpace X] [T2Space X] {f : α → X} (hf : Continuous f)
    (hinj : Function.Injective f) {C K : Set X} (hK : IsClosed K)
    (hattach : range f ∩ K ⊆ {f ⊥, f ⊤}) (hconn : IsPreconnected C)
    (hcover : C ⊆ range f ∪ K) (hout : ¬ C ⊆ range f) :
    OrdConnected (f ⁻¹' C)ᶜ :=
  hf.ordConnected_compl_preimage_of_isPreconnected hinj hK hattach hconn hcover hout

-- The union identity needs only a preorder, with no topology or compactness.
example {α : Type*} [Preorder α] {A : Set α} (hA : OrdConnected Aᶜ) :
    ((upperClosure Aᶜ).compl : Set α) ∪ (lowerClosure Aᶜ).compl = A := by
  simpa only [compl_compl] using hA.compl_upperClosure_union_compl_lowerClosure

-- With no gap, both canonical sets are the whole type.
example {α : Type*} [Preorder α] :
    (upperClosure (univ : Set α)ᶜ).compl = (⊤ : LowerSet α) := by simp

example {α : Type*} [Preorder α] :
    (lowerClosure (univ : Set α)ᶜ).compl = (⊥ : UpperSet α) := by simp

-- Both canonical pieces are nonempty for the remainder of this open gap.
example :
    let A : Set (Icc (0 : ℝ) 3) := Subtype.val ⁻¹' (Icc 0 1 ∪ Icc 2 3)
    let L : Set (Icc (0 : ℝ) 3) := (upperClosure Aᶜ).compl
    let R : Set (Icc (0 : ℝ) 3) := (lowerClosure Aᶜ).compl
    L ∪ R = A ∧ IsCompact L ∧ OrdConnected L ∧ IsCompact R ∧ OrdConnected R ∧
      L.Nonempty ∧ R.Nonempty := by
  dsimp only
  let A : Set (Icc (0 : ℝ) 3) := Subtype.val ⁻¹' (Icc 0 1 ∪ Icc 2 3)
  have hAc : IsCompact A :=
    ((isClosed_Icc.union isClosed_Icc).preimage continuous_subtype_val).isCompact
  have heq : Aᶜ = Subtype.val ⁻¹' Ioo (1 : ℝ) 2 := by
    ext x
    change ¬ (x.1 ∈ Icc 0 1 ∨ x.1 ∈ Icc 2 3) ↔ x.1 ∈ Ioo 1 2
    constructor
    · intro hn
      exact ⟨lt_of_not_ge (fun h ↦ hn (Or.inl ⟨x.2.1, h⟩)),
        lt_of_not_ge (fun h ↦ hn (Or.inr ⟨h, x.2.2⟩))⟩
    · rintro ⟨h1, h2⟩ (h | h)
      · exact h1.not_ge h.2
      · exact h2.not_ge h.1
  have hgap : OrdConnected Aᶜ := by
    rw [heq]
    exact ordConnected_Ioo.preimage_mono (fun _ _ h ↦ h)
  refine ⟨?_, hAc.compl_upperClosure_compl, (upperClosure Aᶜ).compl.lower.ordConnected,
    hAc.compl_lowerClosure_compl, (lowerClosure Aᶜ).compl.upper.ordConnected, ?_, ?_⟩
  · simpa only [compl_compl] using hgap.compl_upperClosure_union_compl_lowerClosure
  · refine ⟨⟨0, by norm_num⟩, ?_⟩
    rintro ⟨y, hy, hy0⟩
    have hy1 := ((heq ▸ hy : y ∈ Subtype.val ⁻¹' Ioo (1 : ℝ) 2)).1
    change y.1 ≤ 0 at hy0
    linarith
  · refine ⟨⟨3, by norm_num⟩, ?_⟩
    rintro ⟨y, hy, h3y⟩
    have hy2 := ((heq ▸ hy : y ∈ Subtype.val ⁻¹' Ioo (1 : ℝ) 2)).2
    change 3 ≤ y.1 at h3y
    linarith

end Order

namespace SegmentFigureSubsetTest

private abbrev a : ℝ × ℝ := (0, 0)
private abbrev b : ℝ × ℝ := (1, 0)
private abbrev c : ℝ × ℝ := (0, 1)
private def sides : Set (ℝ × ℝ) := segment ℝ a c ∪ segment ℝ c b
private def triangle : Set (ℝ × ℝ) := sides ∪ segment ℝ a b

-- The two other sides connect the endpoints outside the base segment.
private theorem sides_preconnected : IsPreconnected sides :=
  IsPreconnected.union c (right_mem_segment ℝ a c) (left_mem_segment ℝ c b)
    (convex_segment a c).isPreconnected (convex_segment c b).isPreconnected

private theorem sides_inter_base : sides ∩ segment ℝ a b = {a, b} := by
  ext x
  constructor
  · rintro ⟨hside, hbase⟩
    obtain ⟨t, ht, rfl⟩ := (segment_eq_image_lineMap ℝ a b) ▸ hbase
    rcases hside with hside | hside
    · obtain ⟨s, hs, heq⟩ := (segment_eq_image_lineMap ℝ a c) ▸ hside
      have hfst := congrArg Prod.fst heq
      simp [a, b, c, AffineMap.lineMap_apply_module] at hfst
      subst t
      simp [a]
    · obtain ⟨s, hs, heq⟩ := (segment_eq_image_lineMap ℝ c b) ▸ hside
      have hsnd := congrArg Prod.snd heq
      have hfst := congrArg Prod.fst heq
      simp [a, b, c, AffineMap.lineMap_apply_module] at hsnd hfst
      have ht1 : t = 1 := by linarith
      simp [ht1, b]
  · rintro (rfl | rfl)
    · exact ⟨Or.inl (left_mem_segment ℝ a c), left_mem_segment ℝ a b⟩
    · exact ⟨Or.inr (right_mem_segment ℝ c b), right_mem_segment ℝ a b⟩

example : IsSegmentFigure sides ∧ ¬ IsPreconnected (sides ∩ segment ℝ a b) := by
  have hfig : IsSegmentFigure triangle :=
    ((isSegmentFigure_segment a c).union (isSegmentFigure_segment c b)).union
      (isSegmentFigure_segment a b)
  refine ⟨hfig.of_isClosed_preimage_isPreconnected subset_union_left
    (((isCompact_segment a c).union (isCompact_segment c b)).isClosed.preimage
      continuous_subtype_val) sides_preconnected, ?_⟩
  rw [sides_inter_base]
  intro h
  have hi := (h.image Prod.fst continuous_fst.continuousOn).ordConnected
  rw [image_pair] at hi
  have hm := hi.out (by simp : (0 : ℝ) ∈ {a.1, b.1})
    (by simp : (1 : ℝ) ∈ {a.1, b.1}) (by norm_num : (1 / 2 : ℝ) ∈ Icc 0 1)
  norm_num [a, b] at hm

-- The finite-component reverse implication also handles a disconnected nonempty subset.
example : IsSegmentFigure ({(0 : ℝ), 1} : Set ℝ) := by
  have hsub : ({(0 : ℝ), 1} : Set ℝ) ⊆ Icc 0 1 := by
    intro x hx
    rcases hx with rfl | rfl <;> norm_num
  apply ((isSegmentFigure_Icc 0 1).iff_isClosed_preimage_finite_connectedComponents hsub).mpr
  exact ⟨(isClosed_singleton.union isClosed_singleton).preimage continuous_subtype_val,
    inferInstance⟩

end SegmentFigureSubsetTest

/-- info: 'Continuous.ordConnected_compl_preimage_of_isPreconnected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Continuous.ordConnected_compl_preimage_of_isPreconnected
/-- info: 'IsCompact.exists_eq_segment_of_isConnected_of_subset_segment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IsCompact.exists_eq_segment_of_isConnected_of_subset_segment
/-- info: 'IsSegmentFigure.of_isClosed_preimage_isPreconnected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IsSegmentFigure.of_isClosed_preimage_isPreconnected
/-- info: 'IsSegmentFigure.iff_isClosed_preimage_finite_connectedComponents' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IsSegmentFigure.iff_isClosed_preimage_finite_connectedComponents
