module

public import Mathlib.Topology.Order.Compact

/-!
# Order topology and connected subsets of embedded linear orders

Open sets omit their supremum and infimum when there are points beyond them.
The preimage of a preconnected subset of the range of an embedding is order-convex.
If the subset is also nonempty and compact, it is the image of a closed interval.
-/

@[expose] public section

open Set

lemma IsOpen.sSup_notMem {α : Type*} [CompleteLinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [DenselyOrdered α] {s : Set α} (hs : ∃ x, sSup s < x)
    (h : IsOpen s) : sSup s ∉ s := by
  intro m
  obtain ⟨ub, hub, hubs⟩ := exists_Ico_subset_of_mem_nhds (mem_nhds h m) hs
  obtain ⟨x, hssx, hxub⟩ := exists_between hub
  exact (le_sSup <| hubs ⟨hssx.le, hxub⟩).not_gt hssx

lemma IsOpen.sInf_notMem {α : Type*} [CompleteLinearOrder α] [TopologicalSpace α]
    [OrderTopology α] [DenselyOrdered α] {s : Set α} (hs : ∃ x, x < sInf s)
    (h : IsOpen s) : sInf s ∉ s :=
  IsOpen.sSup_notMem (α := αᵒᵈ) hs h

namespace Topology.IsEmbedding

variable {α X : Type*} [TopologicalSpace α] [TopologicalSpace X] {f : α → X} {S : Set X} {a b : α}
  (hf : IsEmbedding f) (hsub : S ⊆ range f)

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
    S = f '' (Icc (sInf (f ⁻¹' S)) <| sSup (f ⁻¹' S)) := by
  obtain h := image_preimage_eq_of_subset hsub
  refine h.symm.trans <| congrArg (f '' ·) <| eq_Icc_of_connected_compact
    ⟨hS.nonempty.preimage' hsub, ?_⟩ <| hf.isInducing.isCompact_preimage' hcompact hsub
  simpa only [← hf.isInducing.isPreconnected_image, h] using hS.isPreconnected

end Topology.IsEmbedding
