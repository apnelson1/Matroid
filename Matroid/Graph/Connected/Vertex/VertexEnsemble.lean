import Matroid.Graph.Connected.Set.Defs
import Matroid.Graph.Degree.Basic

open Set Function Nat WList

variable {α β ι ι' : Type*} {G H : Graph α β} {s t u v x x₁ x₂ y y₁ y₂ z : α} {e e' f g : β}
  {C U V S T : Set α} {F F' R R': Set β} {W P Q : WList α β} {n m : ℕ}

namespace Graph

@[simps]
def IsSetCut.cutBetween_of_neighbor (hC : (G - {s, t}).IsSetCut N(G, s) N(G, t) C) (hne : s ≠ t)
    (hadj : ¬ G.Adj s t) : G.CutBetween s t where
  carrier := C
  carrier_subset := by
    have := by simpa [subset_diff] using hC.subset_vertexSet
    exact this.1
  left_not_mem := by
    have := by simpa [subset_diff] using hC.subset_vertexSet
    exact this.2.1
  right_not_mem := by
    have := by simpa [subset_diff] using hC.subset_vertexSet
    exact this.2.2
  not_connectedBetween' h := hC.ST_disconnects <| G.vertexDelete_vertexDelete_comm _ _ ▸
      (h.neighbor_setConnected hne <| (hadj <| ·.of_le vertexDelete_le)).subset
      (neighbor_mono vertexDelete_le) (neighbor_mono vertexDelete_le)

lemma connectivityBetweenGe_iff_setConnectivityGe (hne : s ≠ t) (hadj : ¬ G.Adj s t) :
    G.ConnectivityBetweenGe s t n ↔ (G - {s, t}).SetConnectivityGe N(G, s) N(G, t) n := by
  refine ⟨fun h C hC => ?_, fun h C => ?_⟩
  · obtain ⟨hCsub, hCs, hCt⟩ := by simpa [subset_diff] using hC.subset_vertexSet
    simpa using h (hC.cutBetween_of_neighbor hne hadj)
  refine h ⟨?_, ?_⟩
  · simp only [vertexDelete_vertexSet, subset_diff, disjoint_insert_right, SetLike.mem_coe,
    disjoint_singleton_right]
    exact ⟨C.carrier_subset, C.left_not_mem, C.right_not_mem⟩
  have hh := C.not_connectedBetween
  contrapose! hh
  obtain ⟨a, ⟨hsane, hsa⟩, b, ⟨htbne, htb⟩, hab⟩ := hh
  have hsa' := (G.vertexDelete_adj_iff C).mpr ⟨hsa, C.left_not_mem, hab.left_mem.2⟩
  have htb' := (G.vertexDelete_adj_iff C).mpr ⟨htb, C.right_not_mem, hab.right_mem.2⟩
  exact (hsa'.connectedBetween.trans ((G.vertexDelete_vertexDelete_comm _ _ ▸ hab).of_le
    vertexDelete_le)).trans htb'.connectedBetween.symm

lemma ConnectivityBetweenGe.le_left_Neighbor_encard (hne : s ≠ t) (hadj : ¬ G.Adj s t)
    (hconn : G.ConnectivityBetweenGe s t n) : n ≤ N(G, s).encard := by
  rw [connectivityBetweenGe_iff_setConnectivityGe hne hadj] at hconn
  have := hconn.left_encard_le
  rwa [inter_eq_right.mpr (by simp [neighbor_subset_of_ne_not_adj hne hadj])] at this

lemma ConnectivityBetweenGe.le_right_Neighbor_encard (hne : s ≠ t) (hadj : ¬ G.Adj s t)
    (hconn : G.ConnectivityBetweenGe s t n) : n ≤ N(G, t).encard :=
  hconn.symm.le_left_Neighbor_encard hne.symm (by rwa [adj_comm])

noncomputable def link (G : Graph α β) (x : α) : N(G, x) → β := fun y ↦ y.prop.2.choose

@[simp]
lemma link_isLink (y : N(G, x)) : G.IsLink (G.link x y) x y := y.prop.2.choose_spec

@[simp]
lemma link_mem {y : N(G, x)} : G.link x y ∈ E(G) := y.prop.2.choose_spec.edge_mem

noncomputable def VertexEnsemble.ofSetEnsemble (x y : α) (hxy : x ≠ y)
    (A : (G - {x, y}).SetEnsemble) (hA : A.between N(G, x) N(G, y)) :
    G.VertexEnsemble x y (first '' A.paths) where
  f u := by
    let a := u.prop.choose
    let h : a ∈ _ ∧ a.first = u := u.prop.choose_spec
    let hl := hA h.1 |>.last_mem
    exact concat (cons x (G.link x ⟨u, h.2 ▸ (hA h.1).first_mem⟩) (A.of_vertex u (by
    have hu := u.prop
    nth_rw 1 [hA.image_first_eq_inter] at hu
    exact inter_subset_right hu))) (G.link y ⟨_, hl⟩) y
  isPath u := by
    simp only [cons_concat, cons_isPath_iff, concat_isPath_iff, concat_first, mem_concat, not_or]
    generalize_proofs hu huf hv huN
    have := A.valid (A.of_vertex_mem_setEnsemble hu) |>.vertexSet_subset
    simp only [vertexDelete_vertexSet, subset_diff, disjoint_insert_right, mem_vertexSet_iff,
      disjoint_singleton_right] at this
    refine ⟨⟨A.valid (A.of_vertex_mem_setEnsemble hu) |>.of_le vertexDelete_le, ?_, this.2.2⟩,
      ?_, this.2.1, hxy⟩
    · convert (link_isLink _).symm
      rw [A.eq_of_vertex_mem hu huf.choose_spec.1]
      convert first_mem
      exact huf.choose_spec.2.symm
    convert link_isLink _
    obtain ⟨P, hP, hPu⟩ := huf
    rw [← A.eq_of_vertex_mem hu hP (hPu ▸ first_mem)]
    simpa
  first_eq u := by simp
  last_eq u := by simp
  internallyDisjoint u v hne := by
    simp only [cons_concat, cons_vertexSet, concat_vertexSet_eq, ← insert_inter_distrib]
    generalize_proofs hu hv
    suffices V(A.of_vertex ↑u hu) ∩ V(A.of_vertex ↑v hv) = ∅ by
      simp [this]
    rw [← disjoint_iff_inter_eq_empty]
    apply A.disjoint (A.of_vertex_mem_setEnsemble hu) (A.of_vertex_mem_setEnsemble hv)
    rwa [ne_eq, A.of_vertex_injOn_first u.prop v.prop, Subtype.coe_inj]
