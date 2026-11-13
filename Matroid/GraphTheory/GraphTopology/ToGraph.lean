module

public import Matroid.GraphTheory.GraphTopology.Basic
public import Matroid.GraphTheory.GraphTopology.Cut
public import Matroid.GraphTheory.GraphTopology.Circuit
public import Matroid.GraphTheory.Graph.Finite
public import Matroid.GraphTheory.Graph.Connected.Bond
public import Matroid.GraphTheory.Graph.AcyclicSet

/-! # Graphs associated with graph-like spaces -/

@[expose] public section

open Set Function TopologicalSpace Set.Notation Graph WList

variable {X : Type*} [TopologicalSpace X]

namespace GraphLike

def toGraph (hZ : GraphLike X) : Graph X (Set X) where
  vertexSet := hZ.vertexSet
  edgeSet := hZ.edgeSet
  IsLink := hZ.IsLink
  isLink_symm e _ := ⟨fun _ _ h ↦ h.symm⟩
  eq_or_eq_of_isLink_of_isLink e x y v w h h' := by
    have : x ∈ ({v, w} : Set X) := h'.2 ▸ h.2.symm ▸ mem_insert x {y}
    simpa using this
  edge_mem_iff_exists_isLink e := by
    refine ⟨fun he ↦ ?_, fun ⟨x, y, h⟩ ↦ h.edge_mem⟩
    obtain ⟨x, _, y, _, hb, _⟩ := hZ.boundary_isPair he
    exact ⟨x, y, he, hb⟩
  left_mem_of_isLink _ _ _ h := h.left_mem

instance (G : GraphLike X) [G.Finite] : G.toGraph.Finite where
  vertexSet_finite := Finite.vertexSet_finite
  edgeSet_finite := Finite.edgeSet_finite

@[simp]
lemma toGraph_finite_iff (G : GraphLike X) : G.toGraph.Finite ↔ G.Finite :=
  ⟨fun h ↦ ⟨h.vertexSet_finite, h.edgeSet_finite⟩, fun _ ↦ inferInstance⟩

variable {G : GraphLike X} {B : Set (Set X)}

lemma edgeCut_eq (G : GraphLike X) (U : Set X) : G.edgeCut U = δ(G.toGraph, U) := by
  ext e
  simp only [edgeCut, Graph.mem_setLinkEdges_iff, mem_sdiff]
  constructor
  · rintro ⟨x, y, hxy, hx, hy⟩
    exact ⟨x, hx, y, ⟨hxy.right_mem, hy⟩, hxy⟩
  rintro ⟨x, hx, y, ⟨_, hy⟩, hxy⟩
  exact ⟨x, y, hxy, hx, hy⟩

lemma IsEdgeCut.toGraph (h : G.IsEdgeCut B) : G.toGraph.IsEdgeCut B := by
  obtain ⟨U, W, hU, hW, hd, hV, rfl⟩ := h
  exact ⟨U, (G.edgeCut_eq U).symm⟩

lemma isEdgeCut_iff_toGraph (hV : V(G).Finite) : G.IsEdgeCut B ↔ G.toGraph.IsEdgeCut B := by
  refine ⟨IsEdgeCut.toGraph, ?_⟩
  rintro ⟨A, rfl⟩
  let : T2Space G := G.t2Space
  let L : Set G := Subtype.val ⁻¹' (V(G) ∩ A)
  let R : Set G := Subtype.val ⁻¹' (V(G) \ A)
  have hL : L.Finite := (hV.inter_of_left A).preimage Subtype.val_injective.injOn
  have hR : R.Finite := hV.sdiff.preimage Subtype.val_injective.injOn
  obtain ⟨U, W, hU, hW, hLU, hRW, hd⟩ :=
    SeparatedNhds.of_isCompact_isCompact hL.isCompact hR.isCompact
      (show Disjoint L R from disjoint_left.mpr fun x hx hy ↦ hy.2 hx.2)
  obtain ⟨U', hU', hpreU⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hU
  obtain ⟨W', hW', hpreW⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hW
  have hUeq (x : G) : x.1 ∈ U' ↔ x ∈ U := by rw [← hpreU]; rfl
  have hWeq (x : G) : x.1 ∈ W' ↔ x ∈ W := by rw [← hpreW]; rfl
  refine ⟨U', W', hU', hW', ?_, ?_, ?_⟩
  · exact disjoint_left.mpr fun x hx hy ↦
      hd.notMem_of_mem_left ((hUeq ⟨x, hx.1⟩).mp hx.2) ((hWeq ⟨x, hx.1⟩).mp hy.2)
  · intro x hx
    by_cases hxA : x ∈ A
    · exact Or.inl ((hUeq ⟨x, G.subset hx⟩).mpr (hLU ⟨hx, hxA⟩))
    exact Or.inr ((hWeq ⟨x, G.subset hx⟩).mpr (hRW ⟨hx, hxA⟩))
  rw [← G.edgeCut_eq]
  apply G.edgeCut_congr
  intro x hx
  refine ⟨fun hxU ↦ ?_, fun hxA ↦ (hUeq ⟨x, G.subset hx⟩).mpr (hLU ⟨hx, hxA⟩)⟩
  by_contra hxA
  exact hd.notMem_of_mem_left ((hUeq ⟨x, G.subset hx⟩).mp hxU) (hRW ⟨hx, hxA⟩)

lemma isBond_iff_toGraph (hV : V(G).Finite) : G.IsBond B ↔ G.toGraph.IsBond B := by
  simp only [IsBond, Graph.IsBond, Minimal, isEdgeCut_iff_toGraph hV]

/-! ### Cycles of the underlying graph and intrinsic circuits -/

variable {C : Set (Set X)}

lemma toGraph_inc_iff {e : Set X} {x : X} :
    G.toGraph.Inc e x ↔ e ∈ E(G) ∧ x ∈ e ∩ V(G) := by
  constructor
  · rintro ⟨y, he, hb⟩
    refine ⟨he, ?_⟩
    change x ∈ G.edgeBoundary e
    rw [hb]
    exact Or.inl rfl
  rintro ⟨he, hx⟩
  obtain ⟨a, ha, b, hb, hab, hl⟩ := G.boundary_isPair he
  obtain rfl | rfl := (show x ∈ ({a, b} : Set X) from hab ▸ hx)
  · exact ⟨b, he, hab⟩
  exact ⟨a, he, hab.trans (pair_comm _ _)⟩

lemma isPrimitiveLink_sUnion_of_isPath {P : WList X (Set X)}
    (hP : G.toGraph.IsPath P) (hne : P.Nonempty) :
    IsPrimitiveLink (⋃₀ E(P)) P.first P.last := by
  induction P with
  | nil x => simp at hne
  | cons x e P ih =>
    obtain ⟨he, hP', hxP⟩ := Graph.cons_isPath_iff.mp hP
    obtain hn | hn := P.nil_or_nonempty
    · obtain ⟨y, rfl⟩ := hn.exists_eq_nil
      simpa using (show G.IsLink e x _ from he).isPrimitiveLink
    have hx : x ≠ P.first := fun h ↦ hxP (h ▸ P.first_mem)
    have hp : P.first ≠ P.last := fun h ↦ hn.not_nil (hP'.first_eq_last_iff.mp h)
    have heP : e ∉ P.edge := (Graph.cons_isTrail_iff.mp hP.isTrail).2.2
    have hi : e ∩ ⋃₀ E(P) ⊆ {P.first} := by
      rintro z ⟨hze, hz⟩
      obtain ⟨f, hf, hzf⟩ := mem_sUnion.mp hz
      have hfG := hP'.isWalk.edge_mem_of_mem hf
      have hzV := G.edge_inter_subset_vertexSet he.edge_mem hfG (fun h ↦ heP (h ▸ hf)) ⟨hze, hzf⟩
      have hzP := hP'.isWalk.mem_of_mem_edge_of_inc hf (toGraph_inc_iff.mpr ⟨hfG, hzf, hzV⟩)
      obtain rfl | hz := (show z ∈ ({x, P.first} : Set X) from he.boundary_eq ▸ ⟨hze, hzV⟩)
      · exact (hxP hzP).elim
      exact hz
    simpa using (show G.IsLink e x P.first from he).isPrimitiveLink.union (ih hP' hn) hx hp hi

lemma isCircuit_sUnion_of_isCyclicWalk {W : WList X (Set X)}
    (hW : G.toGraph.IsCyclicWalk W) : IsCircuit (⋃₀ E(W)) := by
  have hsub : ⋃₀ E(W) ⊆ G.carrier :=
    sUnion_subset fun e he ↦ G.edge_subset (hW.isWalk.edge_mem_of_mem he)
  let : T2Space (⋃₀ E(W)) := (Topology.IsEmbedding.inclusion hsub).t2Space
  obtain ⟨x, e, rfl⟩ | hnt := hW.loop_or_nontrivial
  · have hl : G.IsLink e x x := (Graph.cons_isWalk_iff.mp hW.isWalk).1
    let : T2Space e := (Topology.IsEmbedding.inclusion (G.edge_subset hl.edge_mem)).t2Space
    simpa using hl.isPrimitiveLink.isCircuit_of_eq rfl
  obtain ⟨e, he⟩ := hW.nonempty.edgeSet_nonempty
  obtain ⟨n, P, hP, heP, hr⟩ := hW.exists_isPath_edge hnt he
  have hrot := hW.rotate n
  rw [hr] at hrot
  have hl : G.IsLink e P.last P.first := (Graph.cons_isWalk_iff.mp hrot.isWalk).1
  have hp : P.Nonempty := by
    obtain hp | hp := P.nil_or_nonempty
    · obtain ⟨y, rfl⟩ := hp.exists_eq_nil
      have := hnt.two_le_length
      have hlens := congrArg WList.length hr
      simp at hlens
      omega
    exact hp
  have hne : P.last ≠ P.first := fun h ↦ hp.not_nil (hP.first_eq_last_iff.mp h.symm)
  have hi : e ∩ ⋃₀ E(P) ⊆ {P.last, P.first} := by
    rintro z ⟨hze, hz⟩
    obtain ⟨f, hf, hzf⟩ := mem_sUnion.mp hz
    have hzV := G.edge_inter_subset_vertexSet hl.edge_mem (hP.isWalk.edge_mem_of_mem hf)
      (fun h ↦ heP (h ▸ hf)) ⟨hze, hzf⟩
    exact hl.boundary_eq ▸ ⟨hze, hzV⟩
  have heq : ⋃₀ E(W) = e ∪ ⋃₀ E(P) := by
    rw [← WList.rotate_edgeSet W n, hr, cons_edgeSet, sUnion_insert]
  rw [heq]
  let : T2Space ↥(e ∪ ⋃₀ E(P)) := heq ▸ inferInstanceAs (T2Space (⋃₀ E(W)))
  exact hl.isPrimitiveLink.isCircuit_union (isPrimitiveLink_sUnion_of_isPath hP hp) hne hi

lemma isCircuitSet_of_toGraph_isCycleSet (hC : G.toGraph.IsCycleSet C) : G.IsCircuitSet C := by
  obtain ⟨W, hW, rfl⟩ := hC
  exact ⟨⋃₀ E(W), sUnion_subset fun e he ↦ G.edge_subset (hW.isWalk.edge_mem_of_mem he),
    isCircuit_sUnion_of_isCyclicWalk hW,
    (G.setOf_edge_subset_sUnion_eq hW.isWalk.edgeSet_subset).symm⟩

/- A connected subset covered by finitely many edges and two endpoint vertices connects those
vertices in the underlying graph restricted to those edges. The cover hypothesis is shaped to the
circle-minus-an-edge argument below. -/
private lemma connBetween_of_isPreconnected {K : Set X} {F : Set (Set X)} {a b : X}
    (hK : IsPreconnected K) (hF : F.Finite) (hFE : F ⊆ E(G))
    (ha : a ∈ K) (hb : b ∈ K) (haV : a ∈ V(G)) (hbV : b ∈ V(G))
    (hcover : K ⊆ ⋃₀ F ∪ {a, b}) : (G.toGraph ↾ F).ConnBetween a b := by
  classical
  let H := G.toGraph ↾ F
  let L := {e ∈ F | ∃ z ∈ e ∩ V(G), H.ConnBetween a z}
  let R := F \ L
  have heconn {e : Set X} (he : e ∈ F) {z w : X} (hz : z ∈ e ∩ V(G))
      (hw : w ∈ e ∩ V(G)) : H.ConnBetween z w := by
    obtain ⟨x, hx, y, hy, hxy, hl⟩ := G.boundary_isPair (hFE he)
    have hh : H.IsLink e x y := by
      exact ⟨he, hFE he, hxy⟩
    have hz' : z ∈ ({x, y} : Set X) := hxy ▸ hz
    have hw' : w ∈ ({x, y} : Set X) := hxy ▸ hw
    rcases hz' with rfl | rfl <;> rcases hw' with rfl | rfl
    · exact .refl hh.left_mem
    · exact hh.connBetween
    · exact hh.symm.connBetween
    · exact .refl hh.right_mem
  have hLvertex {e : Set X} (he : e ∈ L) {z : X} (hz : z ∈ e ∩ V(G)) :
      H.ConnBetween a z := by
    obtain ⟨heF, w, hw, haw⟩ := he
    exact haw.trans (heconn heF hw hz)
  have hRvertex {e : Set X} (he : e ∈ R) {z : X} (hz : z ∈ e ∩ V(G)) :
      ¬ H.ConnBetween a z := fun h ↦ he.2 ⟨he.1, z, hz, h⟩
  by_contra hab
  have hdisj : Disjoint (insert a (⋃₀ L)) (insert b (⋃₀ R)) := by
    apply disjoint_left.mpr
    intro z hz hz'
    rcases hz with rfl | hz
    · rcases hz' with rfl | hz'
      · exact hab (.refl haV)
      obtain ⟨e, he, hze⟩ := mem_sUnion.mp hz'
      exact hRvertex he ⟨hze, haV⟩ (.refl haV)
    obtain ⟨e, he, hze⟩ := mem_sUnion.mp hz
    rcases hz' with rfl | hz'
    · exact hab (hLvertex he ⟨hze, hbV⟩)
    obtain ⟨f, hf, hzf⟩ := mem_sUnion.mp hz'
    have hzV := G.edge_inter_subset_vertexSet (hFE he.1) (hFE hf.1)
      (fun h ↦ hf.2 (h ▸ he)) ⟨hze, hzf⟩
    exact hRvertex hf ⟨hzf, hzV⟩ (hLvertex he ⟨hze, hzV⟩)
  have hcover' : K ⊆ insert a (⋃₀ L) ∪ insert b (⋃₀ R) := by
    intro z hz
    rcases hcover hz with hz | hz
    · obtain ⟨e, he, hze⟩ := mem_sUnion.mp hz
      by_cases heL : e ∈ L
      · exact Or.inl (Or.inr (mem_sUnion.mpr ⟨e, heL, hze⟩))
      exact Or.inr (Or.inr (mem_sUnion.mpr ⟨e, ⟨he, heL⟩, hze⟩))
    rcases hz with rfl | rfl
    · exact Or.inl (Or.inl rfl)
    exact Or.inr (Or.inl rfl)
  have hLG : insert a (⋃₀ L) ⊆ G.carrier :=
    insert_subset (G.subset haV) (sUnion_subset fun e he ↦ G.edge_subset (hFE he.1))
  have hRG : insert b (⋃₀ R) ⊆ G.carrier :=
    insert_subset (G.subset hbV) (sUnion_subset fun e he ↦ G.edge_subset (hFE he.1))
  have hcL : IsCompact (insert a (⋃₀ L)) :=
    ((hF.subset (show L ⊆ F from fun _ h ↦ h.1)).isCompact_sUnion
      (fun e he ↦ G.edge_isCompact (hFE he.1))).insert a
  have hcR : IsCompact (insert b (⋃₀ R)) :=
    ((hF.subset (show R ⊆ F from sdiff_subset)).isCompact_sUnion
      (fun e he ↦ G.edge_isCompact (hFE he.1))).insert b
  have hKG : K ⊆ G.carrier := hcover'.trans (union_subset hLG hRG)
  have hK' : IsPreconnected (G.carrier ↓∩ K) :=
    Topology.IsInducing.subtypeVal.isPreconnected_image.mp (by
      simpa only [Subtype.image_preimage_coe, inter_eq_right.mpr hKG] using hK)
  obtain ⟨z, hzK, hzL, hzR⟩ := isPreconnected_closed_iff.mp hK'
    (G.carrier ↓∩ insert a (⋃₀ L)) (G.carrier ↓∩ insert b (⋃₀ R))
    (Topology.IsInducing.subtypeVal.isCompact_preimage' hcL (by simpa using hLG)).isClosed
    (Topology.IsInducing.subtypeVal.isCompact_preimage' hcR (by simpa using hRG)).isClosed
    (fun z hz ↦ hcover' hz) ⟨⟨a, G.subset haV⟩, ha, Or.inl rfl⟩
    ⟨⟨b, G.subset hbV⟩, hb, Or.inl rfl⟩
  exact hdisj.notMem_of_mem_left hzL hzR

lemma IsCircuitSet.toGraph_isCycleSet (hC : G.IsCircuitSet C) (hfin : C.Finite) :
    G.toGraph.IsCycleSet C := by
  obtain ⟨K, hKG, hK, rfl⟩ := hC
  let C := {e | e ∈ E(G) ∧ e ⊆ K}
  have hKE : K = ⋃₀ C := G.isCircuit_eq_sUnion_edges_of_finite hK hKG hfin
  have hCne : C.Nonempty := by
    obtain ⟨x, hx⟩ := hK.nonempty
    obtain ⟨e, he, _⟩ := mem_sUnion.mp (hKE ▸ hx)
    exact ⟨e, he⟩
  obtain ⟨e, he⟩ := hCne
  obtain ⟨a, ha, b, hb, hab, hl⟩ := G.boundary_isPair he.1
  have heK : G.edgeInterior e ⊆ K := sdiff_subset.trans he.2
  have hp := (hK.isPreconnected_sdiff_iff heK).mpr (G.edgeInterior_isConnected he.1).isPreconnected
  have ha' : a ∈ K \ G.edgeInterior e := ⟨he.2 hl.left_mem, fun h ↦ h.2 ha⟩
  have hb' : b ∈ K \ G.edgeInterior e := ⟨he.2 hl.right_mem, fun h ↦ h.2 hb⟩
  have hcover : K \ G.edgeInterior e ⊆ ⋃₀ (C \ {e}) ∪ {a, b} := by
    intro x hx
    obtain ⟨f, hf, hxf⟩ := mem_sUnion.mp (hKE ▸ hx.1)
    by_cases hfe : f = e
    · subst f
      right
      have hxV : x ∈ V(G) := by by_contra hn; exact hx.2 ⟨hxf, hn⟩
      exact hab ▸ ⟨hxf, hxV⟩
    exact Or.inl (mem_sUnion.mpr ⟨f, ⟨hf, hfe⟩, hxf⟩)
  obtain ⟨P, hP, hPa, hPb⟩ :=
    (connBetween_of_isPreconnected hp hfin.sdiff (fun _ hf ↦ hf.1.1)
      ha' hb' ha hb hcover).exists_isPath
  have hP' : G.toGraph.IsPath P := hP.of_le Graph.restrict_le
  have hPE : E(P) ⊆ C \ {e} := fun f hf ↦ (hP.edgeSet_subset hf).2
  have heP : e ∉ P.edge := fun h ↦ (hPE h).2 rfl
  have hl' : G.toGraph.IsLink e P.first P.last := by
    rw [hPa, hPb]
    exact ⟨he.1, hab⟩
  have hW := hP'.cons_isCyclicWalk hl' heP
  have hWC : E(cons P.last e P) ⊆ C := by
    rw [cons_edgeSet]
    exact insert_subset he (hPE.trans sdiff_subset)
  have hWK : ⋃₀ E(cons P.last e P) ⊆ K := sUnion_subset fun f hf ↦ (hWC hf).2
  have heq := hK.eq_of_subset (isCircuit_sUnion_of_isCyclicWalk hW) hWK
  refine ⟨_, hW, ?_⟩
  rw [← G.setOf_edge_subset_sUnion_eq hW.isWalk.edgeSet_subset, heq]

end GraphLike
