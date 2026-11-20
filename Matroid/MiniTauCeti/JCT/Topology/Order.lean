module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Order.UpperLower.Closure
public import Mathlib.Topology.Connected.Clopen

/-!
# Order topology and connected subsets of embedded linear orders

Open sets omit their supremum and infimum when there are points beyond them.
The preimage of a preconnected subset of the range of an embedding is order-convex.
If the subset is also nonempty and compact, it is the image of a closed interval.
Compactness and closed order rays also provide a complete order on the original linear order.
-/

@[expose] public section

open Set Function

variable {α X : Type*} [TopologicalSpace α] {f : α → X} {A : Set α} {S : Set X} {a b : α}

/-- Order-convex subspaces inherit compact closed intervals. -/
instance Set.OrdConnected.compactIccSpace {D : Type*} [Preorder D] [TopologicalSpace D]
    [CompactIccSpace D] {s : Set D} [OrdConnected s] : CompactIccSpace s where
  isCompact_Icc {a b} := by
    apply Topology.IsEmbedding.subtypeVal.isInducing.isCompact_iff.mpr
    rw [image_subtypeVal_Icc]
    exact isCompact_Icc

lemma IsOpen.sSup_notMem [CompleteLinearOrder α] [OrderTopology α] [DenselyOrdered α]
    (hs : ∃ x, sSup A < x) (h : IsOpen A) : sSup A ∉ A := by
  intro m
  obtain ⟨ub, hub, hubs⟩ := exists_Ico_subset_of_mem_nhds (mem_nhds h m) hs
  obtain ⟨x, hssx, hxub⟩ := exists_between hub
  exact (le_sSup <| hubs ⟨hssx.le, hxub⟩).not_gt hssx

lemma IsOpen.sInf_notMem [CompleteLinearOrder α] [OrderTopology α] [DenselyOrdered α]
    (hs : ∃ x, x < sInf A) (h : IsOpen A) : sInf A ∉ A :=
  IsOpen.sSup_notMem (α := αᵒᵈ) hs h

namespace Topology.IsEmbedding

variable [TopologicalSpace X] (hf : IsEmbedding f) (hsub : S ⊆ range f)

include hf hsub

section LinearOrder

variable [LinearOrder α] [OrderTopology α]

/-- A preconnected subset of an embedded linear order has order-convex preimage. -/
lemma ordConnected_preimage (hS : IsPreconnected S) : OrdConnected (f ⁻¹' S) := by
  refine (hf.isInducing.isPreconnected_image.mp ?_).ordConnected
  rwa [image_preimage_eq_of_subset hsub]

/-- A preconnected subset of an embedded linear order contains the interval between any
two of its points. -/
lemma image_Icc_subset_of_isPreconnected (hS : IsPreconnected S) (ha : f a ∈ S) (hb : f b ∈ S) :
    f '' Icc a b ⊆ S := image_subset_iff.mpr <| (hf.ordConnected_preimage hsub hS).out ha hb

/-- A nonempty compact connected subset of an embedded linear order is the image of a
closed interval. No completeness assumption on the order is needed. -/
lemma exists_eq_image_Icc_of_isConnected_isCompact (hS : IsConnected S) (hcompact : IsCompact S) :
    ∃ a b, a ≤ b ∧ S = f '' Icc a b := by
  have hpre : IsCompact (f ⁻¹' S) := hf.isInducing.isCompact_preimage' hcompact hsub
  have hne : (f ⁻¹' S).Nonempty := hS.nonempty.preimage' hsub
  obtain ⟨a, ha⟩ := hpre.exists_isLeast hne
  obtain ⟨b, hb⟩ := hpre.exists_isGreatest hne
  refine ⟨a, b, ha.right hb.left, (image_preimage_eq_of_subset hsub).symm.trans ?_⟩
  congr 1
  exact Subset.antisymm (fun _ hx ↦ ⟨ha.right hx, hb.right hx⟩) <|
    (hf.ordConnected_preimage hsub hS.isPreconnected).out ha.left hb.left

end LinearOrder

/-- In a conditionally complete linear order, the endpoints of the interval representing a
nonempty compact connected subset are the infimum and supremum of its preimage. -/
lemma eq_image_Icc_of_isConnected_isCompact [ConditionallyCompleteLinearOrder α] [OrderTopology α]
    (hS : IsConnected S) (hcompact : IsCompact S) :
    S = f '' Icc (sInf (f ⁻¹' S)) (sSup (f ⁻¹' S)) := by
  obtain h := image_preimage_eq_of_subset hsub
  refine h.symm.trans <| congrArg (f '' ·) <| eq_Icc_of_connected_compact
    ⟨hS.nonempty.preimage' hsub, ?_⟩ <| hf.isInducing.isCompact_preimage' hcompact hsub
  simpa only [← hf.isInducing.isPreconnected_image, h] using hS.isPreconnected

end Topology.IsEmbedding

/-- A strictly monotone map with order-connected range is an open embedding when its source
has no endpoints. -/
lemma StrictMono.isOpenEmbedding_of_ordConnected {A B : Type*}
    [LinearOrder A] [TopologicalSpace A] [OrderTopology A] [NoMinOrder A] [NoMaxOrder A]
    [LinearOrder B] [TopologicalSpace B] [OrderTopology B] {f : A → B}
    (hf : StrictMono f) (hc : OrdConnected (range f)) : Topology.IsOpenEmbedding f := by
  refine ⟨hf.isEmbedding_of_ordConnected hc, isOpen_iff_mem_nhds.mpr ?_⟩
  rintro _ ⟨x, rfl⟩
  obtain ⟨a, ha⟩ := exists_lt x
  obtain ⟨b, hb⟩ := exists_gt x
  exact Filter.mem_of_superset (Ioo_mem_nhds (hf ha) (hf hb))
    (Ioo_subset_Icc_self.trans (hc.out (mem_range_self a) (mem_range_self b)))

/-- The greatest lower set contained in a compact set is compact. -/
lemma IsCompact.compl_upperClosure_compl [LinearOrder α] [OrderClosedTopology α]
    (hA : IsCompact A) : IsCompact (upperClosure Aᶜ : Set α)ᶜ := by
  suffices (upperClosure Aᶜ : Set α)ᶜ = (A : Set α) ∩ ⋂ y ∈ Aᶜ, Iic y from
    this ▸ hA.inter_right (isClosed_biInter fun _ _ ↦ isClosed_Iic)
  ext x
  refine ⟨fun hx ↦ ⟨?_, mem_iInter₂.mpr fun y hy ↦ ?_⟩, fun ⟨hx, hb⟩ ⟨y, hy, hyx⟩ ↦ ?_⟩
  · by_contra hn
    exact hx ⟨x, hn, le_rfl⟩
  · exact (lt_of_not_ge fun hyx ↦ hx ⟨y, hy, hyx⟩).le
  exact hy ((hyx.antisymm (mem_iInter₂.mp hb y hy)).symm ▸ hx)

/-- The greatest upper set contained in a compact set is compact. -/
lemma IsCompact.compl_lowerClosure_compl [LinearOrder α] [OrderClosedTopology α]
    (hA : IsCompact A) : IsCompact (lowerClosure Aᶜ : Set α)ᶜ :=
  IsCompact.compl_upperClosure_compl (α := αᵒᵈ) hA

/-- The complement of an order-connected set is the union of the complements of its
upper and lower closures. This identity needs only a preorder, not topology. -/
lemma Set.OrdConnected.compl_upperClosure_union_compl_lowerClosure {α : Type*} [Preorder α]
    {A : Set α} (hA : OrdConnected A) :
    ((upperClosure A).compl : Set α) ∪ (lowerClosure A).compl = Aᶜ := by
  rw [UpperSet.coe_compl, LowerSet.coe_compl, ← compl_inter, hA.upperClosure_inter_lowerClosure]

/-- An embedded compact ordered interval attached to a closed remainder only at its
endpoints has an order-connected gap in every preconnected set reaching the remainder.
The preconnected set itself need not be closed. -/
lemma Continuous.ordConnected_compl_preimage_of_isPreconnected [LinearOrder α] [BoundedOrder α]
    [OrderTopology α] [CompactSpace α] [TopologicalSpace X] [T2Space X] (hf : Continuous f)
    (hinj : Injective f) {C K : Set X} (hK : IsClosed K) (hattach : range f ∩ K ⊆ {f ⊥, f ⊤})
    (hconn : IsPreconnected C) (hsub : C ⊆ range f ∪ K) (hout : ¬ C ⊆ range f) :
    OrdConnected (f ⁻¹' C)ᶜ := by
  obtain ⟨w, hwC, hw⟩ := not_subset.mp hout
  refine ⟨fun u hu v hv t ht htC ↦ ?_⟩
  let H := f '' Icc u v
  let L := (K ∪ f '' Iic u) ∪ f '' Ici v
  have hH : IsClosed H := (isClosed_Icc.isCompact.image hf).isClosed
  have hL : IsClosed L := (hK.union (isClosed_Iic.isCompact.image hf).isClosed).union
    (isClosed_Ici.isCompact.image hf).isClosed
  have hcover : C ⊆ H ∪ L := by grind
  obtain ⟨z, hzC, ⟨s, ⟨hsu, hsv⟩, rfl⟩, hzL⟩ := isPreconnected_closed_iff.mp hconn H L hH hL
    hcover ⟨f t, htC, t, ht, rfl⟩ ⟨w, hwC, Or.inl (Or.inl <| (hsub hwC).resolve_left hw)⟩
  suffices s = u ∨ s = v by exact this.elim (fun h ↦ hu (h ▸ hzC)) (fun h ↦ hv (h ▸ hzC))
  obtain (hzK | ⟨r, hr, hrs⟩) | ⟨r, hr, hrs⟩ := hzL <;> grind [hattach ⟨mem_range_self s, _⟩]


/-- Preconnectedness and open rays force order density, without compactness. -/
theorem denselyOrdered_of_isOpen_rays {D : Type*} [LinearOrder D] [TopologicalSpace D]
    [PreconnectedSpace D] (ho : ∀ x : D, IsOpen (Iio x) ∧ IsOpen (Ioi x)) :
    DenselyOrdered D where
  dense x y hxy := by
    obtain ⟨z, hzy, hxz⟩ := nonempty_inter (ho y).1 (ho x).2 (Iio_union_Ioi_of_lt hxy)
      ⟨x, hxy⟩ ⟨y, hxy⟩
    exact ⟨z, hxz, hzy⟩

/-! ## Compact ordered topologies -/

/-- Clamping to a closed interval is continuous for any linear order with closed rays.
The domain and codomain retain the given topology. -/
theorem continuous_clamp_of_closed_rays {D : Type*} [LinearOrder D] [TopologicalSpace D]
    [ClosedIicTopology D] [ClosedIciTopology D] (a b : D) :
    Continuous (fun x : D ↦ max a (min b x)) := by
  have hmin : Continuous (fun x : D ↦ min b x) := by
    have hl : ContinuousOn (fun x : D ↦ min b x) (Iic b) :=
      continuousOn_id.congr fun x hx ↦ min_eq_right hx
    have hr : ContinuousOn (fun x : D ↦ min b x) (Ici b) :=
      continuousOn_const.congr fun x hx ↦ min_eq_left hx
    simpa only [Iic_union_Ici, continuousOn_univ] using
      hl.union_of_isClosed hr isClosed_Iic isClosed_Ici
  have hmax : Continuous (fun x : D ↦ max a x) := by
    have hl : ContinuousOn (fun x : D ↦ max a x) (Iic a) :=
      continuousOn_const.congr fun x hx ↦ max_eq_left hx
    have hr : ContinuousOn (fun x : D ↦ max a x) (Ici a) :=
      continuousOn_id.congr fun x hx ↦ max_eq_right hx
    simpa only [Iic_union_Ici, continuousOn_univ] using
      hl.union_of_isClosed hr isClosed_Iic isClosed_Ici
  exact hmax.comp hmin

/-- Closed intervals remain preconnected when the given topology is finer than the order
topology, provided the whole space is preconnected and the order rays are closed. -/
theorem isPreconnected_Icc_of_closed_rays {D : Type*} [LinearOrder D] [TopologicalSpace D]
    [ClosedIicTopology D] [ClosedIciTopology D] [PreconnectedSpace D] (a b : D) :
    IsPreconnected (Icc a b) := by
  by_cases hab : a ≤ b
  · have heq : range (fun x : D ↦ max a (min b x)) = Icc a b := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
      · intro hx
        exact ⟨x, by simp [min_eq_right hx.2, max_eq_right hx.1]⟩
    rw [← heq]
    exact isPreconnected_range (continuous_clamp_of_closed_rays a b)
  rw [Icc_eq_empty hab]
  exact isPreconnected_empty

/-- Connectedness and open order rays imply the least-upper-bound property. The topology
may be strictly finer than the order topology. -/
theorem exists_isLUB_of_isOpen_rays {D : Type*} [LinearOrder D] [TopologicalSpace D]
    [PreconnectedSpace D] (ho : ∀ x : D, IsOpen (Ioi x) ∧ IsOpen (Iio x))
    {s : Set D} (hs : s.Nonempty) (hb : BddAbove s) : ∃ x, IsLUB s x := by
  classical
  by_contra hn
  have hclosed : IsClosed (upperBounds s) := by
    have heq : upperBounds s = ⋂ a ∈ s, (Iio a)ᶜ := by
      ext x
      simp [upperBounds]
    rw [heq]
    exact isClosed_biInter fun a _ ↦ (ho a).2.isClosed_compl
  have hopen : IsOpen (upperBounds s) := by
    have heq : upperBounds s = ⋃ a ∈ upperBounds s, Ioi a := by
      ext x
      simp only [mem_iUnion, mem_Ioi]
      constructor
      · intro hx
        by_contra hn'
        apply hn
        refine ⟨x, hx, fun y hy ↦ ?_⟩
        exact le_of_not_gt fun hyx ↦ hn' ⟨y, hy, hyx⟩
      · rintro ⟨a, ha, hax⟩ y hy
        exact (ha hy).trans hax.le
    rw [heq]
    exact isOpen_biUnion fun a _ ↦ (ho a).1
  have hall := (IsClopen.eq_univ ⟨hclosed, hopen⟩ hb)
  obtain ⟨a, ha⟩ := hs
  exact hn ⟨a, hall.symm ▸ mem_univ a, fun b hb ↦ hb ha⟩

/-- A connected bounded linear order with open rays is complete, even when its given
topology is finer than the order topology. -/
@[instance_reducible]
noncomputable def LinearOrder.completeLinearOrderOfConnected (D : Type*) [LinearOrder D]
    [BoundedOrder D] [TopologicalSpace D] [PreconnectedSpace D]
    (ho : ∀ x : D, IsOpen (Ioi x) ∧ IsOpen (Iio x)) : CompleteLinearOrder D := by
  have h (s : Set D) : ∃ x, IsLUB s x := by
    rcases s.eq_empty_or_nonempty with rfl | hs
    · exact ⟨⊥, isLUB_empty⟩
    exact exists_isLUB_of_isOpen_rays ho hs ⟨⊤, fun _ _ ↦ le_top⟩
  let : SupSet D := ⟨fun s ↦ (h s).choose⟩
  let c : CompleteLattice D :=
    { completeLatticeOfSup D (fun s ↦ (h s).choose_spec) with
      sup := max
      le_sup_left := le_max_left
      le_sup_right := le_max_right
      sup_le := fun _ _ _ ↦ max_le
      inf := min
      inf_le_left := min_le_left
      inf_le_right := min_le_right
      le_inf := fun _ _ _ ↦ le_min }
  exact { c, @LinearOrder.toBiheytingAlgebra D ‹LinearOrder D› c.toBoundedOrder,
    ‹LinearOrder D› with }

open Topology in
theorem orderTopology_of_compact_of_isOpen_rays {K : Type*}
    [TopologicalSpace K] [LinearOrder K] [CompactSpace K]
    (hopen : ∀ y : K, IsOpen (Ioi y) ∧ IsOpen (Iio y)) : OrderTopology K := by
  have hc : @Continuous K K ‹TopologicalSpace K› (Preorder.topology K) id := by
    apply continuous_generateFrom_iff.mpr
    rintro S ⟨y, rfl | rfl⟩
    · exact (hopen y).1
    · exact (hopen y).2
  have ho : @OrderTopology K (Preorder.topology K) _ :=
    @OrderTopology.mk K (Preorder.topology K) _ rfl
  have hT2 : @T2Space K (Preorder.topology K) := by
    let : TopologicalSpace K := Preorder.topology K
    infer_instance
  have he := @Continuous.isClosedEmbedding K K ‹TopologicalSpace K› (Preorder.topology K)
    inferInstance hT2 id hc Function.injective_id
  have he' := @IsClosedEmbedding.isEmbedding K K id _ (Preorder.topology K) he
  have he'' := @IsEmbedding.isInducing K K id _ (Preorder.topology K) he'
  exact ⟨(@IsInducing.eq_induced K K _ (Preorder.topology K) id he'').trans
    (@induced_id K (Preorder.topology K))⟩

/-- Compactness and closed order rays supply a complete linear order on the original order.
This is a non-instance construction to avoid cycling with compactness of complete orders. -/
@[instance_reducible]
noncomputable def LinearOrder.completeLinearOrderOfCompact (K : Type*) [LinearOrder K]
    [TopologicalSpace K] [ClosedIicTopology K] [ClosedIciTopology K] [CompactSpace K] [Nonempty K] :
    CompleteLinearOrder K := by
  have h (s : Set K) : ∃ x, IsLUB s x := by
    have hc : IsClosed (upperBounds s) := by
      have heq : upperBounds s = ⋂ a ∈ s, Ici a := by ext x; simp [upperBounds]
      rw [heq]
      exact isClosed_biInter fun _ _ ↦ isClosed_Ici
    obtain ⟨top, htop⟩ := isCompact_univ.exists_isGreatest
      (univ_nonempty : (univ : Set K).Nonempty)
    exact hc.isCompact.exists_isLeast ⟨top, fun x _ ↦ htop.2 (mem_univ x)⟩
  let : SupSet K := ⟨fun s ↦ (h s).choose⟩
  let c : CompleteLattice K :=
    { completeLatticeOfSup K (fun s ↦ (h s).choose_spec) with
      sup := max
      le_sup_left := le_max_left
      le_sup_right := le_max_right
      sup_le := fun _ _ _ ↦ max_le
      inf := min
      inf_le_left := min_le_left
      inf_le_right := min_le_right
      le_inf := fun _ _ _ ↦ le_min }
  exact { c, @LinearOrder.toBiheytingAlgebra K ‹LinearOrder K› c.toBoundedOrder,
    ‹LinearOrder K› with }
