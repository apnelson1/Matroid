module

public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Order.Zorn

/-! # Compact connected sets -/

@[expose] public section

open Set Topology Filter

/-- A Hausdorff space is totally separated if the complement of one point is
locally compact and totally disconnected. -/
theorem totallySeparatedSpace_of_isTotallyDisconnected_compl_singleton
    {X : Type*} [TopologicalSpace X] [T2Space X]
    (p : X) [LocallyCompactSpace ({p}ᶜ : Set X)]
    (h : IsTotallyDisconnected ({p}ᶜ : Set X)) : TotallySeparatedSpace X := by
  let S : Set X := {p}ᶜ
  have hS : IsOpen S := isClosed_singleton.isOpen_compl
  let : TotallyDisconnectedSpace S := totallyDisconnectedSpace_subtype_iff.mpr h
  have hsep {x y : X} (hx : x ≠ p) (hxy : x ≠ y) :
      ∃ U : Set X, IsClopen U ∧ x ∈ U ∧ y ∉ U := by
    let x' : S := ⟨x, hx⟩
    obtain ⟨K, hK, hxK, hKy⟩ := exists_compact_subset
      ((isClosed_singleton (x := y)).isOpen_compl.preimage
        (continuous_subtypeVal : Continuous (Subtype.val : S → X)))
      (show x' ∈ Subtype.val ⁻¹' ({y}ᶜ : Set X) from hxy)
    obtain ⟨V, hV, hxV, hVK⟩ := exists_isClopen_mem_of_isOpen isOpen_interior hxK
    have hVc : IsCompact V := hK.of_isClosed_subset hV.isClosed
      (hVK.trans interior_subset)
    refine ⟨Subtype.val '' V, ⟨(hVc.image continuous_subtypeVal).isClosed,
      hS.isOpenMap_subtypeVal _ hV.isOpen⟩, ⟨x', hxV, rfl⟩, ?_⟩
    rintro ⟨z, hz, rfl⟩
    exact hKy (interior_subset (hVK hz)) rfl
  exact totallySeparatedSpace_iff_exists_isClopen.mpr (by
    intro x y hxy
    by_cases hx : x = p
    · obtain ⟨U, hU, hyU, hxU⟩ := hsep (fun hy ↦ hxy (hx.trans hy.symm)) hxy.symm
      exact ⟨Uᶜ, hU.compl, hxU, by simpa using hyU⟩
    · exact hsep hx hxy)

/-- A decreasing directed intersection of compact closed preconnected sets is preconnected.
Empty members and an empty intersection are allowed. -/
theorem isPreconnected_iInter_of_directed_isCompact_isClosed {X ι : Type*}
    [TopologicalSpace X] [NormalSpace X] [Nonempty ι] {C : ι → Set X}
    (hd : Directed (· ⊇ ·) C) (hc : ∀ i, IsCompact (C i))
    (hcl : ∀ i, IsClosed (C i)) (hp : ∀ i, IsPreconnected (C i)) :
    IsPreconnected (⋂ i, C i) := by
  rw [isPreconnected_iff_subset_of_fully_disjoint_closed (isClosed_iInter hcl)]
  intro a b ha hb hab hdisj
  obtain ⟨u, v, hu, hv, hau, hbv, huv⟩ := normal_separation ha hb hdisj
  obtain ⟨i, hi⟩ := exists_subset_nhds_of_isCompact' hd hc hcl
    ((hu.union hv).mem_nhdsSet.mpr (hab.trans (union_subset_union hau hbv)))
  have hside : C i ⊆ u ∨ C i ⊆ v :=
    isPreconnected_iff_subset_of_disjoint.mp (hp i) u v hu hv hi (by
      rw [huv.inter_eq, inter_empty])
  rcases hside with hi | hi
  · left
    intro x hx
    exact (hab hx).resolve_right fun hxb ↦
      huv.notMem_of_mem_left (hi (mem_iInter.mp hx i)) (hbv hxb)
  · right
    intro x hx
    exact (hab hx).resolve_left fun hxa ↦
      huv.notMem_of_mem_left (hau hxa) (hi (mem_iInter.mp hx i))

/-- Adjoining one point to a closed totally disconnected set preserves total
disconnectedness in a T1 space. -/
theorem IsTotallyDisconnected.insert_of_isClosed {X : Type*} [TopologicalSpace X] [T1Space X]
    {V : Set X} (hV : IsTotallyDisconnected V) (hc : IsClosed V) (x : X) :
    IsTotallyDisconnected (insert x V) := by
  by_cases hx : x ∈ V
  · simpa only [insert_eq_of_mem hx] using hV
  intro C hC hconn
  have hside : C ⊆ {x} ∨ C ⊆ V :=
    isPreconnected_iff_subset_of_disjoint_closed.mp hconn {x} V isClosed_singleton hc hC
      (by simp [hx])
  exact hside.elim (fun h ↦ (subsingleton_singleton (a := x)).anti h)
    (fun h ↦ hV C h hconn)

/-- A filter with a basis of preconnected sets has a preconnected set of cluster points
in a compact Hausdorff space. -/
theorem Filter.HasBasis.isPreconnected_setOf_clusterPt {X ι : Type*}
    [TopologicalSpace X] [CompactSpace X] [T2Space X]
    {F : Filter X} {p : ι → Prop} {s : ι → Set X} (hb : F.HasBasis p s)
    (hc : ∀ i, p i → IsPreconnected (s i)) : IsPreconnected {x | ClusterPt x F} := by
  obtain ⟨i, hi, _⟩ := hb.mem_iff.mp (univ_mem : (univ : Set X) ∈ F)
  let : Nonempty {i // p i} := ⟨⟨i, hi⟩⟩
  have heq : {x | ClusterPt x F} = ⋂ i : {i // p i}, closure (s i) := by
    ext x
    simp only [mem_ofPred_eq, hb.clusterPt_iff_forall_mem_closure, mem_iInter,
      Subtype.forall]
  rw [heq]
  apply isPreconnected_iInter_of_directed_isCompact_isClosed
  · intro i j
    obtain ⟨k, hk, hks⟩ := hb.mem_iff.mp (inter_mem (hb.mem_of_mem i.2) (hb.mem_of_mem j.2))
    exact ⟨⟨k, hk⟩, closure_mono (hks.trans inter_subset_left),
      closure_mono (hks.trans inter_subset_right)⟩
  · exact fun _ ↦ isClosed_closure.isCompact
  · exact fun _ ↦ isClosed_closure
  · exact fun i ↦ (hc i i.2).closure

/-- A compact totally disconnected subset of a nontrivial connected Hausdorff space
has empty interior. -/
theorem IsTotallyDisconnected.interior_eq_empty_of_isCompact {X : Type*}
    [TopologicalSpace X] [T2Space X] [PreconnectedSpace X] [Nontrivial X]
    {V : Set X} (hV : IsTotallyDisconnected V) (hc : IsCompact V) :
    interior V = ∅ := by
  let : CompactSpace V := isCompact_iff_compactSpace.mp hc
  let : TotallyDisconnectedSpace V := totallyDisconnectedSpace_subtype_iff.mpr hV
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨W, hW, hpW, hWV⟩ := exists_isClopen_mem_of_isOpen
    (isOpen_interior.preimage (continuous_subtypeVal : Continuous (Subtype.val : V → X)))
    (show (⟨p, interior_subset hp⟩ : V) ∈ Subtype.val ⁻¹' interior V from hp)
  have hclosed : IsClosed (Subtype.val '' W : Set X) :=
    (hW.isClosed.isCompact.image continuous_subtypeVal).isClosed
  obtain ⟨U, hU, hUW⟩ := IsInducing.subtypeVal.image_eq_isOpen_inter_range hW.isOpen
  have heq : Subtype.val '' W = U ∩ interior V := by
    apply subset_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨(hUW.subset ⟨x, hx, rfl⟩).1, hWV hx⟩
    · intro x hx
      exact hUW.symm.subset ⟨hx.1, by simpa using interior_subset hx.2⟩
  have hall : Subtype.val '' W = (univ : Set X) :=
    (show IsClopen (Subtype.val '' W) from ⟨hclosed, heq ▸ hU.inter isOpen_interior⟩).eq_univ
      ⟨p, ⟨p, interior_subset hp⟩, hpW, rfl⟩
  have hsub : (univ : Set X) ⊆ V := hall ▸ image_subset_iff.mpr (fun x _ ↦ x.2)
  obtain ⟨x, y, hxy⟩ := exists_pair_ne X
  exact hxy (hV univ hsub isPreconnected_univ (mem_univ x) (mem_univ y))

/-- A neighborhood of a component in a compact Hausdorff space contains a clopen
neighborhood of that component. -/
theorem exists_isClopen_between_component {X : Type*} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] (x : X) {U : Set X}
    (hU : IsOpen U) (hsub : connectedComponent x ⊆ U) :
    ∃ W : Set X, IsClopen W ∧ x ∈ W ∧ W ⊆ U := by
  let N := {s : Set X // IsClopen s ∧ x ∈ s}
  let : Nonempty N := ⟨⟨univ, isClopen_univ, mem_univ x⟩⟩
  have hd : Directed (· ⊇ ·) (fun s : N ↦ s.val) := by
    rintro ⟨s, hs, hxs⟩ ⟨t, ht, hxt⟩
    exact ⟨⟨s ∩ t, hs.inter ht, ⟨hxs, hxt⟩⟩, inter_subset_left, inter_subset_right⟩
  have hi : (⋂ s : N, s.val) ⊆ U := by
    simpa only [connectedComponent_eq_iInter_isClopen] using hsub
  obtain ⟨s, hs⟩ := exists_subset_nhds_of_compactSpace hd
    (fun s : N ↦ s.property.1.isClosed) (hU.mem_nhdsSet.mpr hi)
  exact ⟨s.val, s.property.1, s.property.2, hs⟩

/-- Every component of a proper compact subset of a preconnected Hausdorff space
meets the frontier of the subset. -/
theorem IsCompact.component_meets_frontier {X : Type*} [TopologicalSpace X]
    [T2Space X] [PreconnectedSpace X]
    {A : Set X} (hA : IsCompact A) (hproper : A ≠ univ) (x : A) :
    (connectedComponent x ∩ Subtype.val ⁻¹' frontier A).Nonempty := by
  let : CompactSpace A := isCompact_iff_compactSpace.mp hA
  by_contra hn
  have hsub : connectedComponent x ⊆ (Subtype.val : A → X) ⁻¹' interior A := by
    intro y hy
    by_contra hyint
    apply hn
    exact ⟨y, hy, by simpa only [mem_preimage, frontier, hA.isClosed.closure_eq,
      Set.mem_sdiff] using
      (show y.val ∈ A ∧ y.val ∉ interior A from ⟨y.property, hyint⟩)⟩
  obtain ⟨W, hW, hxW, hWsub⟩ := exists_isClopen_between_component x
    (isOpen_interior.preimage continuous_subtypeVal) hsub
  have hc : IsClosed ((Subtype.val : A → X) '' W) :=
    hA.isClosed.isClosedMap_subtypeVal _ hW.isClosed
  obtain ⟨O, hO, hOW⟩ := IsInducing.subtypeVal.image_eq_isOpen_inter_range hW.isOpen
  have heq : (Subtype.val : A → X) '' W = O ∩ interior A := by
    apply subset_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨(hOW.subset ⟨y, hy, rfl⟩).1, hWsub hy⟩
    · intro y hy
      exact hOW.symm.subset ⟨hy.1, by simpa using interior_subset hy.2⟩
  have ho : IsOpen ((Subtype.val : A → X) '' W) := heq ▸ hO.inter isOpen_interior
  have hall := (show IsClopen ((Subtype.val : A → X) '' W) from ⟨hc, ho⟩).eq_univ
    ⟨x.val, x, hxW, rfl⟩
  apply hproper
  apply subset_antisymm (subset_univ _)
  rw [← hall]
  exact Subtype.coe_image_subset A W

/-- A compact subset with finite frontier in a preconnected Hausdorff space has
finitely many connected components. -/
theorem IsCompact.finite_connectedComponents_of_finite_frontier {X : Type*}
    [TopologicalSpace X] [T2Space X] [PreconnectedSpace X] {A : Set X}
    (hA : IsCompact A) (hf : (frontier A).Finite) :
    Finite (ConnectedComponents A) := by
  by_cases hproper : A = univ
  · subst A
    let : PreconnectedSpace (univ : Set X) :=
      isPreconnected_iff_preconnectedSpace.mp isPreconnected_univ
    infer_instance
  have hfinite : ((Subtype.val : A → X) ⁻¹' frontier A).Finite :=
    hf.preimage Subtype.val_injective.injOn
  have heq : ConnectedComponents.mk '' ((Subtype.val : A → X) ⁻¹' frontier A) = univ := by
    apply eq_univ_of_forall
    intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    obtain ⟨y, hy, hyf⟩ := hA.component_meets_frontier hproper x
    exact ⟨y, hyf, ConnectedComponents.coe_eq_coe'.mpr hy⟩
  exact Set.finite_univ_iff.mp (heq ▸ hfinite.image ConnectedComponents.mk)

/-- Finite-frontier compact neighborhoods imply local connectedness in a preconnected
Hausdorff space. No compactness or countability of the whole space is required. -/
theorem locallyConnectedSpace_of_compact_finite_frontier_basis {X : Type*}
    [TopologicalSpace X] [T2Space X] [PreconnectedSpace X]
    (hb : ∀ (x : X) (U : Set X), U ∈ 𝓝 x →
      ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ closure W ⊆ U ∧
        IsCompact (closure W) ∧ (frontier W).Finite) : LocallyConnectedSpace X := by
  rw [locallyConnectedSpace_iff_connected_subsets]
  intro x U hU
  obtain ⟨W, hW, hxW, hWU, hc, hf⟩ := hb x U hU
  let A := closure W
  let x' : A := ⟨x, subset_closure hxW⟩
  let : CompactSpace A := isCompact_iff_compactSpace.mp hc
  let : Finite (ConnectedComponents A) :=
    hc.finite_connectedComponents_of_finite_frontier (hf.subset frontier_closure_subset)
  have ho : IsOpen (connectedComponent x') :=
    ConnectedComponents.discreteTopology_iff.mp inferInstance x'
  have hn : A ∈ 𝓝 x := mem_of_superset (hW.mem_nhds hxW) subset_closure
  have hn' := Topology.IsInducing.subtypeVal.image_mem_nhdsWithin
    (ho.mem_nhds (mem_connectedComponent (x := x')))
  rw [Subtype.range_coe, nhdsWithin_eq_nhds.mpr hn] at hn'
  exact ⟨Subtype.val '' connectedComponent x', hn',
    isPreconnected_connectedComponent.image _ continuous_subtypeVal.continuousOn,
    (Subtype.coe_image_subset A _).trans hWU⟩

/-- The finite-frontier neighborhood criterion in a compact Hausdorff space. -/
theorem locallyConnectedSpace_of_finite_frontier_basis {X : Type*}
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [PreconnectedSpace X]
    (hb : ∀ (x : X) (U : Set X), U ∈ 𝓝 x →
      ∃ W : Set X, IsOpen W ∧ x ∈ W ∧ closure W ⊆ U ∧ (frontier W).Finite) :
    LocallyConnectedSpace X := by
  apply locallyConnectedSpace_of_compact_finite_frontier_basis
  intro x U hU
  obtain ⟨W, ho, hx, hs, hf⟩ := hb x U hU
  exact ⟨W, ho, hx, hs, isClosed_closure.isCompact, hf⟩

/-- Compact Hausdorff preconnected subspaces inherit local connectedness from an ambient
finite-frontier neighborhood basis at their points. Separation is needed only on the subspace. -/
theorem IsCompact.locallyConnectedSpace_of_finite_frontier_basis {X : Type*}
    [TopologicalSpace X] {K : Set X} [T2Space K] (hc : IsCompact K)
    (hk : IsPreconnected K)
    (hb : ∀ (x : K) (U : Set X), U ∈ 𝓝 x.val →
      ∃ W : Set X, IsOpen W ∧ x.val ∈ W ∧ closure W ⊆ U ∧ (frontier W).Finite) :
    LocallyConnectedSpace K := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hc
  let : PreconnectedSpace K := isPreconnected_iff_preconnectedSpace.mp hk
  apply _root_.locallyConnectedSpace_of_finite_frontier_basis
  intro x U hU
  obtain ⟨V, hV, hVU⟩ := (mem_nhds_subtype K x U).mp hU
  obtain ⟨W, hW, hxW, hWV, hf⟩ := hb x V hV
  refine ⟨Subtype.val ⁻¹' W, hW.preimage continuous_subtypeVal, hxW, ?_, ?_⟩
  · exact (continuous_subtypeVal.closure_preimage_subset W).trans
      ((preimage_mono hWV).trans hVU)
  · exact (hf.preimage Subtype.val_injective.injOn).subset
      (continuous_subtypeVal.frontier_preimage_subset W)

/-- Locally compact locally connected regular spaces have arbitrarily small compact
connected neighborhoods. -/
theorem exists_isCompact_isConnected_mem_nhds {X : Type*} [TopologicalSpace X]
    [RegularSpace X] [LocallyCompactSpace X] [LocallyConnectedSpace X]
    (x : X) {U : Set X} (hU : U ∈ 𝓝 x) :
    ∃ K : Set X, K ∈ 𝓝 x ∧ IsCompact K ∧ IsConnected K ∧ K ⊆ U := by
  obtain ⟨O, hOU, hO, hxO⟩ := mem_nhds_iff.mp hU
  obtain ⟨V, hV, hxV, hVO, hc⟩ := exists_open_between_and_isCompact_closure
    isCompact_singleton hO (singleton_subset_iff.mpr hxO)
  obtain ⟨W, hWV, hW, hxW, hw⟩ :=
    locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp inferInstance x V
      (hV.mem_nhds (hxV (mem_singleton x)))
  exact ⟨closure W, mem_of_superset (hW.mem_nhds hxW) subset_closure,
    hc.of_isClosed_subset isClosed_closure (closure_mono hWV), hw.closure,
    (closure_mono hWV).trans (hVO.trans hOU)⟩

/-- Any two points of a locally compact locally connected preconnected regular space
lie in a compact connected set. -/
theorem exists_isCompact_isConnected_pair {X : Type*} [TopologicalSpace X]
    [RegularSpace X] [LocallyCompactSpace X] [LocallyConnectedSpace X] [PreconnectedSpace X]
    (a b : X) : ∃ K : Set X, IsCompact K ∧ IsConnected K ∧ a ∈ K ∧ b ∈ K := by
  let R : Set X := {x | ∃ K : Set X, IsCompact K ∧ IsConnected K ∧ a ∈ K ∧ x ∈ K}
  have hR : IsOpen R := by
    rw [isOpen_iff_mem_nhds]
    rintro x ⟨K, hc, hk, ha, hx⟩
    obtain ⟨L, hn, hlc, hl, _⟩ := exists_isCompact_isConnected_mem_nhds x
      (Filter.univ_mem : (univ : Set X) ∈ 𝓝 x)
    exact mem_of_superset hn fun y hy ↦
      ⟨K ∪ L, hc.union hlc, hk.union ⟨x, hx, mem_of_mem_nhds hn⟩ hl,
        Or.inl ha, Or.inr hy⟩
  have hRc : IsOpen Rᶜ := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨L, hn, hlc, hl, _⟩ := exists_isCompact_isConnected_mem_nhds x
      (Filter.univ_mem : (univ : Set X) ∈ 𝓝 x)
    apply mem_of_superset hn
    intro y hy hRy
    obtain ⟨K, hc, hk, ha, hyK⟩ := hRy
    exact hx ⟨K ∪ L, hc.union hlc, hk.union ⟨y, hyK, hy⟩ hl,
      Or.inl ha, Or.inr (mem_of_mem_nhds hn)⟩
  have heq : R = univ := (show IsClopen R from ⟨isOpen_compl_iff.mp hRc, hR⟩).eq_univ
    ⟨a, {a}, isCompact_singleton, isConnected_singleton, rfl, rfl⟩
  change b ∈ R
  rw [heq]
  trivial

private theorem exists_minimal_compact_connector_univ {X : Type*} [TopologicalSpace X]
    [T2Space X] [CompactSpace X] [PreconnectedSpace X] (a b : X) :
    ∃ L : Set X, Minimal (fun L : Set X ↦
      IsCompact L ∧ IsPreconnected L ∧ a ∈ L ∧ b ∈ L) L := by
  let S : Set (Set X) := {L | IsCompact L ∧ IsPreconnected L ∧ a ∈ L ∧ b ∈ L}
  apply zorn_superset S
  intro c hcs hchain
  rcases c.eq_empty_or_nonempty with rfl | hne
  · exact ⟨univ, ⟨isCompact_univ, isPreconnected_univ, mem_univ a, mem_univ b⟩,
      by simp⟩
  let : Nonempty c := hne.to_subtype
  refine ⟨⋂ L : c, L.val, ?_, fun L hL ↦ iInter_subset (fun L : c ↦ L.val) ⟨L, hL⟩⟩
  refine ⟨(isClosed_iInter fun L : c ↦ (hcs L.property).1.isClosed).isCompact, ?_,
    mem_iInter.mpr fun L ↦ (hcs L.property).2.2.1,
    mem_iInter.mpr fun L ↦ (hcs L.property).2.2.2⟩
  apply isPreconnected_iInter_of_directed_isCompact_isClosed
    (C := fun L : c ↦ L.val) ?_ (fun L ↦ (hcs L.property).1)
    (fun L ↦ (hcs L.property).1.isClosed) (fun L ↦ (hcs L.property).2.1)
  intro L M
  rcases hchain.total L.property M.property with h | h
  · exact ⟨L, subset_rfl, h⟩
  · exact ⟨M, h, subset_rfl⟩

/-- A compact Hausdorff preconnected set contains a minimal compact preconnected set
containing two prescribed endpoints. The endpoints may coincide. -/
theorem IsCompact.exists_minimal_isPreconnected_pair {X : Type*} [TopologicalSpace X]
    {K : Set X} [T2Space K] (hc : IsCompact K) (hk : IsPreconnected K)
    {a b : X} (ha : a ∈ K) (hb : b ∈ K) :
    ∃ L ⊆ K, Minimal (fun L : Set X ↦
      IsCompact L ∧ IsPreconnected L ∧ a ∈ L ∧ b ∈ L) L := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hc
  let : PreconnectedSpace K := isPreconnected_iff_preconnectedSpace.mp hk
  obtain ⟨L, hL⟩ := exists_minimal_compact_connector_univ (⟨a, ha⟩ : K) ⟨b, hb⟩
  refine ⟨Subtype.val '' L, Subtype.coe_image_subset K L, ⟨?_, ?_⟩⟩
  · exact ⟨hL.prop.1.image continuous_subtypeVal,
      hL.prop.2.1.image _ continuous_subtypeVal.continuousOn,
      ⟨⟨a, ha⟩, hL.prop.2.2.1, rfl⟩, ⟨⟨b, hb⟩, hL.prop.2.2.2, rfl⟩⟩
  · intro M hM hML
    have hMK := hML.trans (Subtype.coe_image_subset K L)
    have heq : Subtype.val '' ((Subtype.val : K → X) ⁻¹' M) = M := by
      simpa only [Subtype.image_preimage_coe] using inter_eq_right.mpr hMK
    have hp : IsCompact ((Subtype.val : K → X) ⁻¹' M) ∧
        IsPreconnected ((Subtype.val : K → X) ⁻¹' M) ∧
        (⟨a, ha⟩ : K) ∈ Subtype.val ⁻¹' M ∧ (⟨b, hb⟩ : K) ∈ Subtype.val ⁻¹' M :=
      ⟨IsInducing.subtypeVal.isCompact_iff.mpr (heq.symm ▸ hM.1),
        IsInducing.subtypeVal.isPreconnected_image.mp (heq.symm ▸ hM.2.1),
        hM.2.2.1, hM.2.2.2⟩
    have hsub : (Subtype.val : K → X) ⁻¹' M ⊆ L := by
      simpa only [preimage_image_eq _ Subtype.val_injective] using
        preimage_mono (f := (Subtype.val : K → X)) hML
    rintro _ ⟨x, hx, rfl⟩
    exact hL.le_of_le hp hsub hx
