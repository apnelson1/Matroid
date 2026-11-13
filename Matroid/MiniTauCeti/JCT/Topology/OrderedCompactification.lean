module

public import Matroid.MiniTauCeti.JCT.Topology.Order
public import Matroid.MiniTauCeti.JCT.Topology.CompactConnected
public import Mathlib.Topology.Order.Basic

/-! # Ordered continua with totally disconnected remainders -/

@[expose] public section

open Set Topology Filter Function

/-- In a compact Hausdorff target, connected images of closed intervals give connected
cluster sets at every point of an order-topological domain. -/
theorem isPreconnected_setOf_mapClusterPt_of_Icc {D X : Type*}
    [LinearOrder D] [TopologicalSpace D] [OrderTopology D]
    [TopologicalSpace X] [CompactSpace X] [T2Space X] {f : D → X}
    (hc : ∀ a b, IsPreconnected (f '' Icc a b)) (c : D) :
    IsPreconnected {x | MapClusterPt x (𝓝 c) f} := by
  have hb : (𝓝 c).HasBasis (fun ab : D × D ↦ Icc ab.1 ab.2 ∈ 𝓝 c)
      (fun ab ↦ Icc ab.1 ab.2) := by
    refine ⟨fun s ↦ ⟨fun hs ↦ ?_, ?_⟩⟩
    · obtain ⟨a, b, _, hab, hs⟩ := exists_Icc_mem_subset_of_mem_nhds hs
      exact ⟨(a, b), hab, hs⟩
    · rintro ⟨ab, hab, hs⟩
      exact mem_of_superset hab hs
  exact (hb.map f).isPreconnected_setOf_clusterPt fun ab _ ↦ hc ab.1 ab.2

private theorem isCompact_range_of_ordered_equiv_of_compactSpace {E D X : Type*}
    [TopologicalSpace E] [LinearOrder D] [TopologicalSpace D] [OrderTopology D]
    [CompactSpace D] [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {e : E → X} (he : IsEmbedding e) (g : E ≃ D) (hg : Continuous g)
    (hc : ∀ a b, IsPreconnected (g ⁻¹' Icc a b))
    {V : Set X} (hV : IsClosed V) (hdisc : IsTotallyDisconnected V)
    (hrem : closure (range e) \ range e ⊆ V) : IsCompact (range e) := by
  let f : D → X := e ∘ g.symm
  have hrange : range f = range e := by
    change range (e ∘ g.symm) = range e
    rw [range_comp, g.symm.surjective.range_eq, image_univ]
  have hc' (a b : D) : IsPreconnected (f '' Icc a b) := by
    have heq : f '' Icc a b = e '' (g ⁻¹' Icc a b) := by
      change (e ∘ g.symm) '' Icc a b = _
      rw [image_comp, g.image_symm_eq_preimage]
    rw [heq]
    exact (hc a b).image e he.continuous.continuousOn
  have hf : Continuous f := by
    apply continuous_iff_continuousAt.mpr
    intro c
    apply tendsto_nhds_of_unique_mapClusterPt
    have hconn := isPreconnected_setOf_mapClusterPt_of_Icc hc' c
    have hnamed : MapClusterPt (f c) (𝓝 c) f := by
      apply clusterPt_iff_forall_mem_closure.mpr
      intro s hs
      exact subset_closure (show c ∈ f ⁻¹' s from mem_of_mem_nhds hs)
    have hsub : {x | MapClusterPt x (𝓝 c) f} ⊆ insert (f c) V := by
      intro x hx
      change MapClusterPt x (𝓝 c) f at hx
      by_cases hxe : x ∈ range e
      · obtain ⟨z, rfl⟩ := hxe
        have hz : MapClusterPt z (𝓝 c) g.symm := by
          apply he.isInducing.mapClusterPt_iff.mp
          simpa only [MapClusterPt, map_map, f] using hx
        have hz' := hz.continuousAt_comp hg.continuousAt
        have heq : g ∘ g.symm = id := funext g.apply_symm_apply
        rw [heq, mapClusterPt_id_iff] at hz'
        have hgc : g z = c := by
          exact eq_of_nhds_neBot hz'
        left
        change e z = e (g.symm c)
        rw [← hgc, g.symm_apply_apply]
      · right
        apply hrem ⟨?_, hxe⟩
        apply hx.clusterPt.mem_closure_of_mem
        rw [← hrange]
        exact range_mem_map
    have hsingle := (hdisc.insert_of_isClosed hV (f c)) _ hsub hconn
    exact fun x hx ↦ hsingle hx hnamed
  rw [← hrange]
  exact isCompact_range hf

/-- A continuous bijection to a compact ordered space recovers compactness of an embedded
space with compact closure when inverse images of closed intervals are connected and its
missing closure points lie in a closed totally disconnected set. -/
theorem Topology.IsEmbedding.isCompact_range_of_ordered_equiv {E D X : Type*}
    [TopologicalSpace E] [LinearOrder D] [TopologicalSpace D] [OrderTopology D]
    [CompactSpace D] [TopologicalSpace X] [T2Space X]
    {e : E → X} (he : IsEmbedding e) (hcompact : IsCompact (closure (range e)))
    (g : E ≃ D) (hg : Continuous g) (hc : ∀ a b, IsPreconnected (g ⁻¹' Icc a b))
    {V : Set X} (hV : IsClosed V) (hdisc : IsTotallyDisconnected V)
    (hrem : closure (range e) \ range e ⊆ V) : IsCompact (range e) := by
  let C := closure (range e)
  let : CompactSpace C := isCompact_iff_compactSpace.mp hcompact
  let e' : E → C := fun z ↦ ⟨e z, subset_closure (mem_range_self z)⟩
  have he' : IsEmbedding e' := he.codRestrict C _
  have hdisc' : IsTotallyDisconnected ((Subtype.val : C → X) ⁻¹' V) :=
    IsEmbedding.subtypeVal.isTotallyDisconnected
      (fun s hs ↦ hdisc s (hs.trans (image_preimage_subset _ _)))
  have hc' := isCompact_range_of_ordered_equiv_of_compactSpace he' g hg hc
    (hV.preimage continuous_subtype_val) hdisc' (by
      rintro z ⟨-, hz⟩
      apply hrem ⟨z.property, ?_⟩
      rintro ⟨w, hw⟩
      exact hz ⟨w, Subtype.ext hw⟩)
  simpa only [← range_comp, e', Function.comp_def] using hc'.image continuous_subtype_val

/-- A bounded connected linear order embedded with compact closure in a Hausdorff space
is compact if its rays are open and its missing closure points lie in a closed totally
disconnected set.
No equality with the order topology is assumed. -/
theorem Topology.IsEmbedding.isCompact_range_of_connected_order {E X : Type*}
    [TopologicalSpace E] [LinearOrder E] [BoundedOrder E] [PreconnectedSpace E]
    [TopologicalSpace X] [T2Space X] {e : E → X}
    (he : IsEmbedding e) (hcompact : IsCompact (closure (range e)))
    (ho : ∀ a : E, IsOpen (Ioi a) ∧ IsOpen (Iio a))
    {V : Set X} (hV : IsClosed V) (hdisc : IsTotallyDisconnected V)
    (hrem : closure (range e) \ range e ⊆ V) : IsCompact (range e) := by
  let t := ‹TopologicalSpace E›
  let : ClosedIicTopology E := ⟨fun a ↦ by simpa using (ho a).1.isClosed_compl⟩
  let : ClosedIciTopology E := ⟨fun a ↦ by simpa using (ho a).2.isClosed_compl⟩
  have hc (a b : E) : IsPreconnected (Icc a b) :=
    isPreconnected_Icc_of_closed_rays a b
  let : CompleteLinearOrder E := LinearOrder.completeLinearOrderOfConnected E ho
  have hid : @Continuous E E t (Preorder.topology E) id := by
    apply continuous_generateFrom_iff.mpr
    rintro s ⟨a, rfl | rfl⟩
    · exact (ho a).1
    · exact (ho a).2
  let : TopologicalSpace E := Preorder.topology E
  let : OrderTopology E := ⟨rfl⟩
  exact @Topology.IsEmbedding.isCompact_range_of_ordered_equiv E E X t
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance e he hcompact (Equiv.refl E) hid hc V hV hdisc hrem
