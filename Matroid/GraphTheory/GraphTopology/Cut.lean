module

public import Matroid.ForMathlib.Set
public import Matroid.GraphTheory.GraphTopology.Restriction
public import Mathlib.Order.Preorder.Finite

/-! # Topological edge cuts and bonds of graphlike spaces -/

@[expose] public section

open Set Topology TopologicalSpace symmDiff

namespace GraphLike

variable {X : Type*} [TopologicalSpace X] {G : GraphLike X} {x y : X} {B D : Set (Set X)}
  {e : Set X} {U W : Set X}

/-- The edges with one endpoint in a set of carrier points and the other outside it. -/
def edgeCut (G : GraphLike X) (U : Set X) : Set (Set X) :=
  {e | ∃ x y, G.IsLink e x y ∧ x ∈ U ∧ y ∉ U}

/-- A topological cut is witnessed by open sets disjoint on the carrier and
covering the vertices. -/
def IsEdgeCut (G : GraphLike X) (B : Set (Set X)) : Prop :=
  ∃ U W : Set X, IsOpen U ∧ IsOpen W ∧ Disjoint (↑G ∩ U) (G ∩ W) ∧ V(G) ⊆ U ∪ W ∧ G.edgeCut U = B

/-- A bond is an inclusion-minimal nonempty topological edge cut. -/
def IsBond (G : GraphLike X) (B : Set (Set X)) : Prop :=
  Minimal (fun B ↦ G.IsEdgeCut B ∧ B.Nonempty) B

lemma edgeCut_subset (G : GraphLike X) (U : Set X) : G.edgeCut U ⊆ E(G) := by
  rintro e ⟨x, y, hxy, -, -⟩
  exact hxy.edge_mem

lemma IsEdgeCut.subset (hB : G.IsEdgeCut B) : B ⊆ E(G) := by
  obtain ⟨U, W, -, -, -, -, rfl⟩ := hB
  exact G.edgeCut_subset U

lemma mem_edgeCut_iff (hxy : G.IsLink e x y) :
    e ∈ G.edgeCut U ↔ (x ∈ U ∧ y ∉ U) ∨ (y ∈ U ∧ x ∉ U) := by
  refine ⟨fun ⟨a, b, hab, ha, hb⟩ ↦ ?_, ?_⟩
  · grind [pair_eq_pair_iff.mp (hxy.2.symm.trans hab.2)]
  rintro (⟨hx, hy⟩ | ⟨hy, hx⟩)
  · exact ⟨x, y, hxy, hx, hy⟩
  exact ⟨y, x, hxy.symm, hy, hx⟩

lemma notMem_edgeCut_iff (he : e ∈ E(G)) :
    e ∉ G.edgeCut U ↔ G.edgeBoundary e ⊆ U ∨ G.edgeBoundary e ⊆ Uᶜ := by
  obtain ⟨x, _, y, _, hb, _⟩ := G.boundary_isPair he
  rw [mem_edgeCut_iff (show G.IsLink e x y from ⟨he, hb⟩), hb]
  simp only [pair_subset_iff, mem_compl_iff]
  tauto

/-- Edge cuts depend only on which vertices belong to the chosen side. -/
lemma edgeCut_congr (h : ∀ x ∈ V(G), x ∈ U ↔ x ∈ W) : G.edgeCut U = G.edgeCut W := by
  ext e
  constructor <;> rintro ⟨x, y, hxy, hx, hy⟩
  · exact ⟨x, y, hxy, (h x hxy.left_mem).mp hx, mt (h y hxy.right_mem).mpr hy⟩
  exact ⟨x, y, hxy, (h x hxy.left_mem).mpr hx, mt (h y hxy.right_mem).mp hy⟩

@[simp] lemma edgeCut_compl (G : GraphLike X) (U : Set X) : G.edgeCut Uᶜ = G.edgeCut U := by
  ext e
  constructor <;> rintro ⟨x, y, hxy, hx, hy⟩
  · exact ⟨y, x, hxy.symm, Classical.not_not.mp hy, hx⟩
  · exact ⟨y, x, hxy.symm, hy, fun h ↦ h hx⟩

lemma edgeCut_symmDiff (G : GraphLike X) (U W : Set X) :
    G.edgeCut (U ∆ W) = G.edgeCut U ∆ G.edgeCut W := by
  ext e
  by_cases he : e ∈ E(G)
  · obtain ⟨x, hx, y, hy, hb, _⟩ := G.boundary_isPair he
    have hxy : G.IsLink e x y := ⟨he, hb⟩
    simp only [mem_symmDiff, mem_edgeCut_iff hxy]
    tauto
  have hnot (S : Set X) : e ∉ G.edgeCut S := fun h ↦ he (G.edgeCut_subset S h)
  simp [mem_symmDiff, hnot]

/-- A region whose frontier avoids the vertices induces a topological edge cut. -/
lemma isEdgeCut_edgeCut_of_disjoint_frontier (h : Disjoint V(G) (frontier U)) :
    G.IsEdgeCut (G.edgeCut U) := by
  refine ⟨interior U, interior Uᶜ, isOpen_interior, isOpen_interior, ?_, ?_, edgeCut_congr ?_⟩
  · exact (disjoint_compl_right.mono interior_subset interior_subset).mono
      inter_subset_right inter_subset_right
  · intro x hx
    have hx' : x ∈ (frontier U)ᶜ := h.notMem_of_mem_left hx
    rwa [compl_frontier_eq_union_interior] at hx'
  exact fun x hx ↦ ⟨fun hi ↦ interior_subset hi, fun hxU ↦
    (mem_interior_iff_notMem_frontier hxU).mpr (h.notMem_of_mem_left hx)⟩

@[simp] lemma edgeCut_empty (G : GraphLike X) : G.edgeCut ∅ = ∅ := by
  ext e
  simp only [edgeCut, mem_empty_iff_false, not_false_eq_true, and_true, and_false, exists_false,
    ofPred_false]

@[simp] lemma edgeCut_univ (G : GraphLike X) : G.edgeCut univ = ∅ := by
  ext e
  simp only [edgeCut, mem_univ, not_true_eq_false, and_false, exists_false, ofPred_false,
    mem_empty_iff_false]

lemma empty_isEdgeCut (G : GraphLike X) : G.IsEdgeCut ∅ :=
  ⟨∅, univ, isOpen_empty, isOpen_univ, by simp, by simp, G.edgeCut_empty⟩

lemma restrict_edgeCut (G : GraphLike X) (A U : Set X) :
    (G.restrict A).edgeCut U = G.edgeCut U ∩ E(G.restrict A) := by
  ext e
  refine ⟨fun ⟨x, y, hxy, hx, hy⟩ ↦ ?_, fun ⟨⟨x, y, hxy, hx, hy⟩, he⟩ ↦ ⟨x, y, ⟨he, ?_⟩, hx, hy⟩⟩
  · have he := (G.restrict_edgeSet A).subset hxy.edge_mem
    refine ⟨⟨x, y, ⟨he.1, ?_⟩, hx, hy⟩, hxy.edge_mem⟩
    simpa only [G.restrict_edgeBoundary he.2] using hxy.2
  rw [G.restrict_edgeBoundary ((G.restrict_edgeSet A).subset he).2]
  exact hxy.2

/-- Restriction retains precisely the cut edges contained in the restricting set. -/
lemma IsEdgeCut.restrict (hB : G.IsEdgeCut B) (A : Set X) :
    (G.restrict A).IsEdgeCut (B ∩ E(G.restrict A)) := by
  obtain ⟨U, W, hU, hW, hd, hc, rfl⟩ := hB
  exact ⟨U, W, hU, hW, hd.mono (inter_subset_inter_left _ (G.restrict_subset_self A))
      (inter_subset_inter_left _ (G.restrict_subset_self A)),
    fun _ hx ↦ hc hx.2, restrict_edgeCut G A U⟩

lemma IsEdgeCut.symmDiff (hB : G.IsEdgeCut B) (hD : G.IsEdgeCut D) : G.IsEdgeCut (B ∆ D) := by
  obtain ⟨U, W, hU, hW, hd, hc, rfl⟩ := hB
  obtain ⟨V, Z, hV, hZ, hd', hc', rfl⟩ := hD
  refine ⟨(U ∩ Z) ∪ (W ∩ V), (U ∩ V) ∪ (W ∩ Z), (hU.inter hZ).union (hW.inter hV),
    (hU.inter hV).union (hW.inter hZ), ?_, fun x hx ↦ by grind, ?_⟩
  · simp_rw [disjoint_left, mem_inter_iff] at hd hd' ⊢
    grind
  rw [← edgeCut_symmDiff]
  refine edgeCut_congr (fun x hx ↦ ?_)
  have hW := mem_right_iff_notMem_left
    (hd.mono (inter_subset_inter_left _ G.subset) (inter_subset_inter_left _ G.subset)) hc hx
  have hZ := mem_right_iff_notMem_left
    (hd'.mono (inter_subset_inter_left _ G.subset) (inter_subset_inter_left _ G.subset)) hc' hx
  grind

lemma IsBond.isEdgeCut (h : G.IsBond B) : G.IsEdgeCut B := h.prop.1

lemma IsBond.nonempty (h : G.IsBond B) : B.Nonempty := h.prop.2

lemma IsBond.eq_of_subset (hB : G.IsBond B) (hD : G.IsEdgeCut D) (hDn : D.Nonempty) (hDB : D ⊆ B) :
    D = B := Minimal.eq_of_subset hB ⟨hD, hDn⟩ hDB

/-- Compactness forces every topological cut to have finitely many edges. -/
lemma IsEdgeCut.finite (hB : G.IsEdgeCut B) (hG : IsCompact G.carrier) : B.Finite := by
  let : CompactSpace G := isCompact_iff_compactSpace.mp hG
  obtain ⟨U, W, hU, hW, hd, hc, rfl⟩ := hB
  let K : Set G := Subtype.val ⁻¹' (U ∪ W)ᶜ
  have hK : IsCompact K := ((hU.union hW).isClosed_compl.preimage continuous_subtypeVal).isCompact
  refine (G.finite_edges_meeting hK (fun x hx hv ↦ hx (hc hv))).subset ?_
  rintro e ⟨x, y, hxy, hx, hy⟩
  have hyW := (hc hxy.right_mem).resolve_left hy
  obtain ⟨z, hze, hz⟩ := not_subset.mp
    ((G.edge_isConnected hxy.edge_mem).isPreconnected.not_subset_union hU hW
    (hd.mono (inter_subset_inter_left _ (G.edge_subset hxy.edge_mem))
      (inter_subset_inter_left _ (G.edge_subset hxy.edge_mem)))
    ⟨x, hxy.isPrimitiveLink.left_mem, hx⟩ ⟨y, hxy.isPrimitiveLink.right_mem, hyW⟩)
  exact ⟨hxy.edge_mem, ⟨z, G.edge_subset hxy.edge_mem hze⟩, hz, hze⟩

/-- The two vertex-induced carriers partition the carrier after removing the cut interiors. -/
lemma induce_union_compl (G : GraphLike X) (U : Set X) :
    (G.induce U : Set X) ∪ (G.induce Uᶜ : Set X) = V(G) ∪ ⋃₀ (E(G) \ G.edgeCut U) := by
  ext x
  constructor
  · rintro ((hx | hx) | (hx | hx))
    · exact Or.inl hx.1
    · obtain ⟨e, he, hxe⟩ := mem_sUnion.mp hx
      exact Or.inr (mem_sUnion.mpr ⟨e, ⟨he.1, (notMem_edgeCut_iff he.1).mpr (Or.inl he.2)⟩, hxe⟩)
    · exact Or.inl hx.1
    obtain ⟨e, he, hxe⟩ := mem_sUnion.mp hx
    exact Or.inr (mem_sUnion.mpr ⟨e, ⟨he.1, (notMem_edgeCut_iff he.1).mpr (Or.inr he.2)⟩, hxe⟩)
  rintro (hx | hx)
  · by_cases hxU : x ∈ U
    · exact Or.inl (Or.inl ⟨hx, hxU⟩)
    exact Or.inr (Or.inl ⟨hx, hxU⟩)
  obtain ⟨e, he, hxe⟩ := mem_sUnion.mp hx
  exact ((notMem_edgeCut_iff he.1).mp he.2).imp
    (fun h ↦ Or.inr (mem_sUnion.mpr ⟨e, ⟨he.1, h⟩, hxe⟩))
    (fun h ↦ Or.inr (mem_sUnion.mpr ⟨e, ⟨he.1, h⟩, hxe⟩))

/-- A cut admits compact sides, without selecting a preferred vertex partition.
For a supplied side, use `induce` and `isCompact_induce`. -/
lemma IsEdgeCut.exists_compact_partition (hB : G.IsEdgeCut B) (hG : IsCompact G.carrier) :
    ∃ K0 K1 : Set X, IsCompact K0 ∧ IsCompact K1 ∧ Disjoint K0 K1 ∧ K0 ∪ K1 = V(G) ∪ ⋃₀ (E(G) \ B) ∧
      ∀ e ∈ B, ∃ a b, G.IsLink e a b ∧ e ∩ K0 = {a} ∧ e ∩ K1 = {b} := by
  obtain ⟨U, W, hU, hW, hd, hc, rfl⟩ := hB
  have hVW := hd.mono (inter_subset_inter_left _ G.subset) (inter_subset_inter_left _ G.subset)
  have hWU : G.induce W = G.induce Uᶜ :=
    G.induce_congr fun x hx ↦ mem_right_iff_notMem_left hVW hc hx
  refine ⟨G.induce U, G.induce W, G.isCompact_induce hG hU hW hd hc,
    G.isCompact_induce hG hW hU hd.symm (by simpa only [union_comm] using hc),
    G.induce_disjoint hVW, ?_, ?_⟩
  · rw [hWU, G.induce_union_compl]
  exact fun e ⟨a, b, hab, ha, hb⟩ ↦ ⟨a, b, hab, hab.inter_induce ha hb,
    hWU ▸ hab.symm.inter_induce hb (fun h ↦ h ha)⟩

lemma IsBond.finite (hB : G.IsBond B) (hG : IsCompact G.carrier) : B.Finite :=
  hB.isEdgeCut.finite hG

/-- Every edge of a finite cut lies in a contained bond. This expresses coverage by
contained bonds, without selecting a distinguished bond for each edge. -/
lemma IsEdgeCut.exists_bond_subset_mem (hB : G.IsEdgeCut B) (hfin : B.Finite) (he : e ∈ B) :
    ∃ D ⊆ B, G.IsBond D ∧ e ∈ D := by
  have hfamily : {D | D ⊆ B ∧ G.IsEdgeCut D ∧ e ∈ D}.Finite :=
    hfin.powerset.subset fun _ h ↦ h.1
  obtain ⟨D, hD⟩ := hfamily.exists_minimal ⟨B, Subset.rfl, hB, he⟩
  refine ⟨D, hD.prop.1, ⟨⟨hD.prop.2.1, ⟨e, hD.prop.2.2⟩⟩, ?_⟩, hD.prop.2.2⟩
  intro A hA hAD
  by_cases heA : e ∈ A
  · exact hD.2 ⟨hAD.trans hD.prop.1, hA.1, heA⟩ hAD
  have hcut := hD.prop.2.1.symmDiff hA.1
  rw [symmDiff_of_ge hAD] at hcut
  have hsub := hD.2 ⟨sdiff_subset.trans hD.prop.1, hcut, hD.prop.2.2, heA⟩ sdiff_subset
  obtain ⟨a, ha⟩ := hA.2
  exact ((hsub (hAD ha)).2 ha).elim

/-- Eliminating a shared edge yields a bond in the remaining union.
This is an existence assertion for elimination, with no distinguished resulting bond. -/
lemma IsBond.elimination (hB : G.IsBond B) (hD : G.IsBond D) (hBfin : B.Finite) (hDfin : D.Finite)
    (hne : B ≠ D) (heB : e ∈ B) (heD : e ∈ D) : ∃ C ⊆ (B ∪ D) \ {e}, G.IsBond C ∧ C.Finite := by
  have hsym := hB.isEdgeCut.symmDiff hD.isEdgeCut
  obtain ⟨f, hf⟩ : (symmDiff B D).Nonempty := by
    rw [← ne_empty_iff_nonempty]
    exact fun h ↦ hne (Set.symmDiff_eq_empty.mp h)
  obtain ⟨C, hC, hbond, _⟩ := hsym.exists_bond_subset_mem (hBfin.symmDiff hDfin) hf
  exact ⟨C, by grind, hbond, (hBfin.symmDiff hDfin).subset hC⟩

end GraphLike
