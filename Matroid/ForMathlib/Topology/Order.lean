module

public import Mathlib.Topology.Order.Compact
public import Mathlib.Order.UpperLower.Closure

/-!
# Order topology and connected subsets of embedded linear orders

Open sets omit their supremum and infimum when there are points beyond them.
The preimage of a preconnected subset of the range of an embedding is order-convex.
If the subset is also nonempty and compact, it is the image of a closed interval.
-/

@[expose] public section

open Set Function

variable {α X : Type*} [TopologicalSpace α] {f : α → X} {A : Set α} {S : Set X} {a b : α}

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
