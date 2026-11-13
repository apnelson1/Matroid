module

public import Matroid.GraphTheory.GraphTopology.Basic
public import Matroid.MiniTauCeti.JCT.Topology.PrimitiveLink.Crossing

/-!
# Directed geometric duality

`Dual S T` carries the edge and face equivalences witnessing directed geometric duality.
Vertices of `T` correspond to the complementary faces of `S`. No reverse face condition is
imposed. The definition applies to infinite and disconnected graphlike spaces.
Existence of a directed geometric dual is expressed by `Nonempty (Dual S T)`.
-/

@[expose] public section

open Set Function Topology

namespace GraphLike

variable {X : Type*} [TopologicalSpace X] {S T : GraphLike X} {C U : Set X} {e : E(S)} {x y : X}

/-- The edge and face equivalences witnessing that `T` is a directed geometric dual of `S`. -/
structure Dual (S T : GraphLike X) where
  edgeEquiv : E(S) ≃ E(T)
  faceEquiv : V(T) ≃ F(S)
  source_vertices_disjoint : Disjoint V(S) T
  face_mem : ∀ v : V(T), v.1 ∈ (faceEquiv v).1
  matched_of_inter : ∀ (e : E(S)) (f : E(T)), ¬ Disjoint e.1 f.1 → edgeEquiv e = f
  crosses : ∀ e : E(S), CrossesOnce (edgeEquiv e).1 e.1

namespace Dual

variable (D : Dual S T)

include D

lemma target_vertices_disjoint : Disjoint V(T) S :=
  disjoint_left.mpr fun v hv ↦
    subset_compl_of_mem_faceSet (D.faceEquiv ⟨v, hv⟩).2 (D.face_mem ⟨v, hv⟩)

lemma not_disjoint_iff (e : E(S)) (f : E(T)) : ¬ Disjoint e.1 f.1 ↔ D.edgeEquiv e = f := by
  refine ⟨D.matched_of_inter e f, ?_⟩
  rintro rfl
  exact fun hd ↦ (D.crosses e).not_disjoint hd.symm

lemma disjoint_iff (e : E(S)) (f : E(T)) : Disjoint e.1 f.1 ↔ D.edgeEquiv e ≠ f := by
  simpa only [not_not] using (D.not_disjoint_iff e f).not

lemma inter_subset_inter_edgeInterior (e : E(S)) (f : E(T)) :
    e.1 ∩ f.1 ⊆ S.edgeInterior e.1 ∩ T.edgeInterior f.1 := by
  intro p hp
  exact ⟨⟨hp.1, D.source_vertices_disjoint.notMem_of_mem_right (T.edge_subset f.2 hp.2)⟩,
    ⟨hp.2, D.target_vertices_disjoint.notMem_of_mem_right (S.edge_subset e.2 hp.1)⟩⟩

/-- A matched target edge has no additional contacts with the source carrier. -/
lemma carrier_inter_eq (e : E(S)) :
    S.carrier ∩ (D.edgeEquiv e).1 = e.1 ∩ (D.edgeEquiv e).1 := by
  refine Subset.antisymm (fun p hp ↦ ?_) (inter_subset_inter_left _ (S.edge_subset e.2))
  have hpV := D.source_vertices_disjoint.notMem_of_mem_right
    (T.edge_subset (D.edgeEquiv e).2 hp.2)
  obtain ⟨g, hg, hpg⟩ := S.exists_edge_of_mem ⟨hp.1, hpV⟩
  have hge : (⟨g, hg⟩ : E(S)) = e :=
    D.edgeEquiv.injective <| D.matched_of_inter ⟨g, hg⟩ (D.edgeEquiv e)
      (Set.not_disjoint_iff.mpr ⟨p, hpg.1, hp.2⟩)
  exact ⟨congrArg Subtype.val hge ▸ hpg.1, hp.2⟩

/-- A matched crossing persists when the source edge is enlarged inside the source carrier.
The enlarged set can be a circuit, a subspace, or the whole source carrier. -/
lemma crossesOnce_of_subset (heC : e.1 ⊆ C) (hCS : C ⊆ S.carrier) :
    CrossesOnce (D.edgeEquiv e).1 C := by
  refine (D.crosses e).congr_right ?_ fun p hp ↦ ?_
  · rw [inter_comm (D.edgeEquiv e).1 C, inter_comm (D.edgeEquiv e).1 e.1]
    exact (inter_subset_inter_left _ hCS |>.trans (D.carrier_inter_eq e).subset).antisymm
      (inter_subset_inter_left _ heC)
  have hpI := (D.inter_subset_inter_edgeInterior e (D.edgeEquiv e) ⟨hp.2, hp.1⟩).1
  filter_upwards [S.carrier_eventuallyEq_edge e.2 hpI] with q hq
  exact propext ⟨fun hqe ↦ heC hqe, fun hqC ↦ hq.mp (hCS hqC)⟩

lemma crossesOnce_carrier (e : E(S)) : CrossesOnce (D.edgeEquiv e).1 S.carrier :=
  D.crossesOnce_of_subset (S.edge_subset e.2) Subset.rfl

/-- A matched target edge crosses a source frontier from one complementary component to another.
The source frontier can be a circuit without being the whole source carrier. -/
theorem endpoints_separated (hlink : T.IsLink (D.edgeEquiv e).1 x y) (heU : e.1 ⊆ frontier U)
    (hUS : frontier U ⊆ S.carrier)
    (hlocal : ∀ p ∈ (D.edgeEquiv e).1 ∩ e.1, PreconnectedSidesAt U p) :
    x ∉ connectedComponentIn (frontier U)ᶜ y := by
  let : T2Space ↥(D.edgeEquiv e).1 :=
    (Topology.IsEmbedding.inclusion (T.edge_subset (D.edgeEquiv e).2)).t2Space
  refine (D.crossesOnce_of_subset heU hUS).not_mem_connectedComponentIn_compl
    hlink.isPrimitiveLink rfl ?_ ?_ fun p hp ↦ ?_
  · exact (D.target_vertices_disjoint.notMem_of_mem_left hlink.left_mem <| hUS ·)
  · exact (D.target_vertices_disjoint.notMem_of_mem_left hlink.right_mem <| hUS ·)
  have hp' : p ∈ e.1 ∩ (D.edgeEquiv e).1 := (D.carrier_inter_eq e) ▸ ⟨hUS hp.2, hp.1⟩
  exact hlocal p ⟨hp'.2, hp'.1⟩

@[simp] lemma faceEquiv_apply (v : V(T)) : (D.faceEquiv v).1 = S.faceAt v.1 :=
  (eq_connectedComponentIn_of_mem_faceSet (D.faceEquiv v).2 (D.face_mem v))

lemma faceEquiv_eq_iff (v : V(T)) (K : F(S)) : D.faceEquiv v = K ↔ v.1 ∈ K.1 := by
  rw [Subtype.ext_iff, faceEquiv_apply]
  exact (mem_iff_of_mem_faceSet K.2 (D.target_vertices_disjoint.notMem_of_mem_left v.2)).symm

lemma faceEquiv_symm_mem (K : F(S)) : (D.faceEquiv.symm K).1 ∈ K.1 :=
  (D.faceEquiv_eq_iff _ _).mp (D.faceEquiv.apply_symm_apply K)

/-- Unique existence records that face membership characterizes `D.faceEquiv.symm K`,
including faces with no incident edge. -/
lemma existsUnique_vertex_mem_face (K : F(S)) : ∃! v : V(T), v.1 ∈ K.1 := by
  refine ⟨D.faceEquiv.symm K, D.faceEquiv_symm_mem K, fun v hv ↦ D.faceEquiv.injective ?_⟩
  exact ((D.faceEquiv_eq_iff v K).mpr hv).trans (D.faceEquiv.apply_symm_apply K).symm

omit D in
/-- Geometry determines both equivalences uniquely. -/
instance : Subsingleton (Dual S T) where
  allEq D D' := by
    have he : D.edgeEquiv = D'.edgeEquiv := by
      apply Equiv.ext
      intro e
      exact (D'.matched_of_inter e (D.edgeEquiv e)
        fun hd ↦ (D.crosses e).not_disjoint hd.symm).symm
    have hf : D.faceEquiv = D'.faceEquiv := by
      apply Equiv.ext
      intro v
      exact Subtype.ext ((D.faceEquiv_apply v).trans (D'.faceEquiv_apply v).symm)
    cases D
    cases D'
    cases he
    cases hf
    rfl

omit D in
/-- Construct directed duality from an edge matching and the condition that every source face
contains exactly one target vertex. -/
noncomputable def ofExistsUnique (edgeEquiv : E(S) ≃ E(T))
    (source_vertices_disjoint : Disjoint V(S) T) (target_vertices_disjoint : Disjoint V(T) S)
    (matched_of_inter : ∀ (e : E(S)) (f : E(T)), ¬ Disjoint e.1 f.1 → edgeEquiv e = f)
    (crosses : ∀ e : E(S), CrossesOnce (edgeEquiv e).1 e.1)
    (face_existsUnique : ∀ K : F(S), ∃! v : V(T), v.1 ∈ K.1) : Dual S T where
  edgeEquiv := edgeEquiv
  faceEquiv := Equiv.ofBijective
    (fun v ↦ ⟨S.faceAt v, mem_faceSet_of_mem_faceAt <|
      target_vertices_disjoint.notMem_of_mem_left v.2⟩)
    ⟨fun v w hvw ↦ by
      obtain ⟨u, -, hu⟩ := face_existsUnique ⟨S.faceAt v, mem_faceSet_of_mem_faceAt <|
        target_vertices_disjoint.notMem_of_mem_left v.2⟩
      refine (hu v (mem_faceAt <| target_vertices_disjoint.notMem_of_mem_left v.2)).trans
        (hu w ?_).symm
      have h := congrArg Subtype.val hvw
      dsimp only at h
      change w.1 ∈ S.faceAt v.1
      rw [h]
      exact mem_faceAt (target_vertices_disjoint.notMem_of_mem_left w.2),
    fun K ↦ by
      obtain ⟨v, hv, -⟩ := face_existsUnique K
      exact ⟨v, Subtype.ext <| (mem_iff_of_mem_faceSet K.2
        (target_vertices_disjoint.notMem_of_mem_left v.2)).mp hv⟩⟩
  source_vertices_disjoint := source_vertices_disjoint
  face_mem v := mem_faceAt (target_vertices_disjoint.notMem_of_mem_left v.2)
  matched_of_inter := matched_of_inter
  crosses := crosses

end Dual

end GraphLike
