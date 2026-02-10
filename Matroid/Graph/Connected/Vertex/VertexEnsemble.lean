import Matroid.Graph.Connected.Set.Defs

open Set Function Nat WList

variable {α β ι ι' : Type*} {G H : Graph α β} {s t u v x x₁ x₂ y y₁ y₂ z : α} {e e' f g : β}
  {C U V S T : Set α} {F F' R R': Set β} {W P Q : WList α β} {n m : ℕ}

namespace Graph

@[simps (attr := grind =)]
def IsSetCut.isSepBetween_of_neighbor (hC : (G - ({s, t} : Set α)).IsSetCut (N(G, s) \ {s})
    (N(G, t) \ {t}) C) (hne : s ≠ t) (hadj : ¬ G.Adj s t) : G.IsSepBetween s t C where
  subset := by
    have := by simpa [subset_diff] using hC.subset_vertexSet
    exact this.1
  left_not_mem := by
    have := by simpa [subset_diff] using hC.subset_vertexSet
    exact this.2.1
  right_not_mem := by
    have := by simpa [subset_diff] using hC.subset_vertexSet
    exact this.2.2
  not_connBetween hst := hC.ST_disconnects <| G.vertexDelete_vertexDelete_comm _ _ ▸
      (hst.neighbor_setConnected hne <| (hadj <| ·.of_le vertexDelete_le)).subset
        (by grw [neighbor_mono vertexDelete_le]) (by grw [neighbor_mono vertexDelete_le])

lemma connBetweenGE_iff_setConnGE (hne : s ≠ t) (hadj : ¬ G.Adj s t) :
    G.ConnBetweenGE s t n ↔ (G - ({s, t} : Set α)).SetConnGE (N(G, s) \ {s}) (N(G, t) \ {t}) n := by
  refine ⟨fun h C hC => ?_, fun h C hC => ?_⟩
  · obtain ⟨hCsub, hCs, hCt⟩ := by simpa [subset_diff] using hC.subset_vertexSet
    simpa using h (hC.isSepBetween_of_neighbor (s := s) (t := t) hne hadj)
  refine h ⟨?_, ?_⟩
  · simp only [vertexDelete_vertexSet, subset_diff, disjoint_insert_right, disjoint_singleton_right]
    exact ⟨hC.subset, hC.left_not_mem, hC.right_not_mem⟩
  have hh := hC.not_connBetween
  contrapose! hh
  obtain ⟨a, ⟨hsa, hsane⟩, b, ⟨htb, htbne⟩, hab⟩ := hh
  have hsa' := (G.vertexDelete_adj_iff C).mpr ⟨hsa, hC.left_not_mem, hab.left_mem.2⟩
  have htb' := (G.vertexDelete_adj_iff C).mpr ⟨htb, hC.right_not_mem, hab.right_mem.2⟩
  exact (hsa'.connBetween.trans ((G.vertexDelete_vertexDelete_comm _ _ ▸ hab).mono
    vertexDelete_le)).trans htb'.connBetween.symm

lemma ConnBetweenGE.le_left_Neighbor_encard (hne : s ≠ t) (hadj : ¬ G.Adj s t)
    (hconn : G.ConnBetweenGE s t n) : n ≤ (N(G, s) \ {s}).encard := by
  rw [connBetweenGE_iff_setConnGE hne hadj] at hconn
  have := hconn.left_encard_le
  rwa [inter_eq_right.mpr (by simp [neighbor_subset_of_ne_not_adj hne hadj])] at this

lemma ConnBetweenGE.le_right_Neighbor_encard (hne : s ≠ t) (hadj : ¬ G.Adj s t)
    (hconn : G.ConnBetweenGE s t n) : n ≤ (N(G, t) \ {t}).encard :=
  hconn.symm.le_left_Neighbor_encard hne.symm (by rwa [adj_comm])

noncomputable def link (G : Graph α β) (x : α) : N(G, x) → β := fun y ↦ y.prop.choose

@[simp]
lemma link_isLink (y : N(G, x)) : G.IsLink (G.link x y) x y := y.prop.choose_spec

@[simp]
lemma link_mem {y : N(G, x)} : G.link x y ∈ E(G) := y.prop.choose_spec.edge_mem

noncomputable def VertexEnsemble.ofSetEnsemble (x y : α) (hxy : x ≠ y)
    (A : (G - ({x, y} : Set α)).SetEnsemble) (hA : A.between N(G, x) N(G, y)) :
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
    generalize_proofs huN hu huf hv
    have := A.valid (A.of_vertex_mem_setEnsemble hu) |>.vertexSet_subset
    simp only [vertexDelete_vertexSet, subset_diff, disjoint_insert_right, mem_vertexSet_iff,
      disjoint_singleton_right] at this
    refine ⟨?_, ⟨A.valid (A.of_vertex_mem_setEnsemble hu) |>.of_le vertexDelete_le, ?_, this.2.2⟩,
      this.2.1, hxy⟩
    · convert link_isLink _
      obtain ⟨P, hP, hPu⟩ := huf
      rw [← A.eq_of_vertex_mem hu hP (hPu ▸ first_mem)]
      simpa
    convert (link_isLink _).symm
    rw [A.eq_of_vertex_mem hu huf.choose_spec.1]
    convert first_mem
    exact huf.choose_spec.2.symm
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

lemma VertexEnsemble.of_linkEdges_edgeDelete (A : (G ＼ E(G, u, v)).VertexEnsemble u v ι) (i : ι) :
    (A.f i).length ≠ 1 := by
  by_contra h
  obtain ⟨x, e, y, heq⟩ := WList.length_eq_one_iff.mp h
  obtain rfl := by simpa [heq] using A.first_eq i
  obtain rfl := by simpa [heq] using A.last_eq i
  simpa [heq] using A.isPath i

def VertexEnsemble.extend_singleEdge [DecidableEq ι] (k : ι)
    (A : G.VertexEnsemble s t ({k}ᶜ : Set ι)) (hP : G.IsPath <| cons s e (nil t)) :
    G.VertexEnsemble s t ι where
  f i := if h : i = k then cons s e (nil t) else A.f ⟨i, h⟩
  isPath i := by
    by_cases h : i = k
    · simp [h, ↓reduceDIte, hP]
    simp [A.isPath ⟨i, h⟩, h]
  first_eq i := by
    by_cases h : i = k
    · simp [h]
    simp [h, A.first_eq ⟨i, h⟩]
  last_eq i := by
    by_cases h : i = k
    · simp [h]
    simp [h, A.last_eq ⟨i, h⟩]
  internallyDisjoint i j hne := by by_cases h : i = k <;> by_cases h' : j = k <;> simp_all

@[simp]
lemma VertexEnsemble.extend_singleEdge_of_eq [DecidableEq ι] (k : ι)
    (A : G.VertexEnsemble s t ({k}ᶜ : Set ι)) (hP : G.IsPath <| cons s e (nil t)) :
    (A.extend_singleEdge k hP).f k = cons s e (nil t) := by
  simp [extend_singleEdge]

@[simp]
lemma VertexEnsemble.extend_singleEdge_of_ne [DecidableEq ι] {i k : ι}
    (A : G.VertexEnsemble s t ({k}ᶜ : Set ι)) (hP : G.IsPath <| cons s e (nil t)) (hne : i ≠ k) :
    (A.extend_singleEdge k hP).f i = A.f ⟨i, hne⟩ := by
  simp [extend_singleEdge, hne]

lemma VertexEnsemble.map_second_inj {A : G.VertexEnsemble s t ι} (hne : s ≠ t)
    (hA : {i | (A.f i).length = 1}.Subsingleton) : Injective (A.f · |>.second) := by
  intro i j hij
  beta_reduce at hij
  obtain hi1 | hi1 := eq_or_ne (A.f i).length 1 <;> obtain hj1 | hj1 := eq_or_ne (A.f j).length 1
  · exact hA hi1 hj1
  · obtain ⟨s, e, t, hi⟩ := (A.f i).length_eq_one_iff.mp hi1
    obtain rfl := by simpa [hi] using A.first_eq i
    obtain rfl := by simpa [hi] using A.last_eq i
    have := A.nonempty_of_ne hne j |>.nontrivial_of_length_ne_one hj1
    |>.second_ne_last_of_nodup (A.isPath j).nodup
    obtain hl := by simpa [hij] using A.last_eq j
    simp [hi, ← hl, this.symm] at hij
  · obtain ⟨s, e, t, hj⟩ := (A.f j).length_eq_one_iff.mp hj1
    obtain rfl := by simpa [hj] using A.first_eq j
    obtain rfl := by simpa [hj] using A.last_eq j
    have := A.nonempty_of_ne hne i |>.nontrivial_of_length_ne_one hi1
    |>.second_ne_last_of_nodup (A.isPath i).nodup
    obtain hl := by simpa [hij] using A.last_eq i
    simp [hj, ← hl, this] at hij
  by_contra hijne
  have hnt := A.nonempty_of_ne hne i |>.nontrivial_of_length_ne_one hi1
  have := by simpa [Set.ext_iff] using A.internallyDisjoint hijne
  obtain hs | ht := this (A.f i).second |>.mp ⟨second_mem, hij ▸ second_mem⟩
  · obtain hf := by simpa [hs] using A.first_eq i
    exact hnt.first_ne_second_of_nodup (A.isPath i).nodup (hf.trans hs.symm)
  · obtain hf := by simpa [ht] using A.last_eq i
    exact hnt.second_ne_last_of_nodup (A.isPath i).nodup (ht.trans hf.symm)

lemma VertexEnsemble.map_second_mem (A : G.VertexEnsemble s t ι) (i : ι) :
    (A.f i).second ∈ V(G) := A.isPath i |>.vertexSet_subset (A.f i).second_mem

lemma VertexEnsemble.vertexSet_encard_of_length_one_subsingleton (hι : ENat.card ι = n)
    (hs : s ∈ V(G)) (hne : s ≠ t) {A : G.VertexEnsemble s t ι}
    (hA : {i | (A.f i).length = 1}.Subsingleton) : n < V(G).encard := by
  have := hι ▸ (A.map_second_inj hne hA).encard_range
  have hsn : s ∉ (range fun x ↦ (A.f x).second) := by
    simp only [mem_range, not_exists]
    rintro i hs
    generalize hi : A.f i = w
    match w with
    | .nil x =>
      obtain rfl := by simpa [hi] using A.first_eq i
      obtain rfl := by simpa [hi] using A.last_eq i
      simp at hne
    | .cons s e (nil t) =>
      obtain rfl := by simpa [hi] using A.first_eq i
      obtain rfl := by simpa [hi] using A.last_eq i
      simp [hi, hne.symm] at hs
    | .cons s e (cons x e' w) =>
      obtain rfl := by simpa [hi] using A.first_eq i
      obtain rfl := by simpa [hi] using A.last_eq i
      obtain rfl := by simpa [hi] using hs
      simpa [hi] using A.isPath i
  grw [← ENat.add_one_le_iff (by simp), this, ← encard_insert_of_notMem hsn]
  apply encard_le_encard
  simp only [insert_subset_iff, hs, true_and]
  rintro - ⟨i, rfl⟩
  exact A.isPath i |>.vertexSet_subset (A.f i).second_mem
