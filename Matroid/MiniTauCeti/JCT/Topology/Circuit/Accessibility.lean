module

public import Matroid.MiniTauCeti.JCT.Topology.Circuit.CompactParametrization
public import Matroid.MiniTauCeti.JCT.Geometry.PolygonalPath.Approximation
public import Matroid.MiniTauCeti.JCT.Geometry.PolygonalPath.SegmentFigure

/-!
# Accessibility from arc nonseparation

A separating compact circuit in a real normed vector space is accessible in every
relative neighborhood from each component of its complement, provided embedded arcs do not
separate the ambient space.
-/

@[expose] public section

open Set Topology TopologicalSpace Function unitInterval

private theorem Path.exists_subpath_compl_subset
    {X : Type*} [TopologicalSpace X] {x y : X} (P : Path x y)
    {O : Set X} (hO : IsOpen O) (hx : x ∈ O) (hy : y ∈ O) :
    ∃ a b : unitInterval, 0 < a ∧ a < b ∧ b < 1 ∧
      range P \ range (P.subpath a b) ⊆ O := by
  have hzero : P ⁻¹' O ∈ 𝓝 (0 : unitInterval) :=
    (hO.preimage P.continuous).mem_nhds (by simpa using hx)
  have hone : P ⁻¹' O ∈ 𝓝 (1 : unitInterval) :=
    (hO.preimage P.continuous).mem_nhds (by simpa using hy)
  obtain ⟨a', ha', hleft⟩ := exists_Ico_subset_of_mem_nhds hzero
    (show ∃ t : unitInterval, 0 < t from ⟨half, zero_lt_half⟩)
  obtain ⟨b', hb', hright⟩ := exists_Ioc_subset_of_mem_nhds hone
    (show ∃ t : unitInterval, t < 1 from ⟨half, half_lt_one⟩)
  obtain ⟨a, ha0, haa⟩ := exists_between (lt_min ha' zero_lt_half)
  obtain ⟨b, hbb, hb1⟩ := exists_between (max_lt hb' half_lt_one)
  have hab : a < b := (lt_of_lt_of_le haa (min_le_right ..)).trans
    (lt_of_le_of_lt (le_max_right ..) hbb)
  refine ⟨a, b, ha0, hab, hb1, ?_⟩
  rintro z ⟨⟨t, rfl⟩, ht⟩
  have ht' : t ∉ Icc a b := by
    intro ht'
    exact ht (P.range_subpath_of_le a b hab.le ▸ mem_image_of_mem P ht')
  obtain hta | hbt := not_and_or.mp ht'
  · exact hleft ⟨t.property.1, (lt_of_not_ge hta).trans
      (lt_of_lt_of_le haa (min_le_left ..))⟩
  · exact hright ⟨(lt_of_le_of_lt (le_max_left ..) hbb).trans (lt_of_not_ge hbt),
      t.property.2⟩

/-- Arc nonseparation makes every relative neighborhood of a separating compact circuit
accessible from each complementary component by a polygonal primitive link. -/
theorem IsCircuit.accessibility_of_arc_complements
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {C : Set X}
    (hC : IsCircuit C) (hcompact : IsCompact C) (hsep : ¬ IsPreconnected Cᶜ)
    (harc : ∀ {A : Set X} {a b : X}, IsPrimitiveLink A a b → a ≠ b →
      IsPathConnected Aᶜ) {O : Set X} {p : X}
    (hO : IsOpen O) (hOC : (O ∩ C).Nonempty) (hp : p ∉ C) :
    ∃ q ∈ O ∩ C, ∃ L : Set X, IsPrimitiveLink L p q ∧ IsSegmentFigure L ∧
      L \ {q} ⊆ connectedComponentIn Cᶜ p := by
  let : SeparableSpace C := hcompact.isSeparable.separableSpace
  obtain ⟨x, hxO, hxC⟩ := hOC
  obtain ⟨P, hP, hPC⟩ := hC.exists_isSimpleLoop hcompact hxC
  obtain ⟨a, b, ha, hab, hb, hsmall⟩ := P.exists_subpath_compl_subset hO hxO hxO
  have hne : P a ≠ P b := fun heq ↦ hab.ne (hP ⟨ha.le, hab.trans hb⟩ ⟨(ha.trans hab).le, hb⟩ heq)
  have hlink := IsPrimitiveLink.of_injective (hP.isPrimitive.injective_subpath hne)
  have hsub : range (P.subpath a b) ⊆ C := by
    rw [← hPC, P.range_subpath_of_le a b hab.le]
    exact image_subset_range ..
  obtain ⟨r, hr, hpr⟩ := exists_connectedComponentIn_ne hsep p
  have hconn := harc hlink hne
  obtain ⟨Q, hQB⟩ := (hconn.joinedIn p (fun hz ↦ hp (hsub hz))
    r (fun hz ↦ hr (hsub hz))).exists_polygonalPath_of_open hlink.isClosed.isOpen_compl
  have hmeet : (Q.toSet ∩ C).Nonempty := by
    by_contra! hempty
    have hQC : Q.toSet ⊆ Cᶜ := by
      intro z hz hzC
      have : z ∈ (∅ : Set X) := hempty ▸ ⟨hz, hzC⟩
      exact this.elim
    have hrcomp := Q.isConnected_toSet.isPreconnected.subset_connectedComponentIn
      (Q.mem_toSet_of_mem_vertices Q.first_mem_vertices) hQC
      (Q.mem_toSet_of_mem_vertices Q.last_mem_vertices)
    exact hpr (connectedComponentIn_eq hrcomp)
  obtain ⟨q, ⟨hqQ, hqC⟩, L, hL, hpoly, -, hbefore⟩ :=
    Q.exists_primitiveLink_first_contact hcompact.isClosed hp hmeet
  refine ⟨q, ⟨?_, hqC⟩, L, hL, hpoly, hbefore⟩
  apply hsmall
  exact ⟨hPC.symm ▸ hqC, hQB hqQ⟩
