import Matroid.Graph.Walk.Path

open Set Function Nat WList

variable {α β ι ι' : Type*} {G H K : Graph α β} {s t u v x x₁ x₂ y y₁ y₂ z : α} {n m : ℕ}
  {e e' f g : β} {U V S S' T T' X Y : Set α} {F F' R R': Set β} {C W P Q : WList α β}

namespace Graph

noncomputable def inc_vert (e : E(G)) : α :=
  exists_isLink_of_mem_edgeSet e.prop |>.choose

@[simp]
lemma inc_vert_inc (e : E(G)) : G.Inc e (inc_vert e) :=
  exists_isLink_of_mem_edgeSet e.prop |>.choose_spec

lemma inc_vert_mem (e : E(G)) : inc_vert e ∈ V(G) :=
  inc_vert_inc e |>.vertex_mem

/-! ### Connectivity between two vertices -/

def ConnectedBetween (G : Graph α β) (x y : α) : Prop :=
  ∃ w : WList α β, G.IsWalk w ∧ w.first = x ∧ w.last = y

lemma ConnectedBetween.refl (hx : x ∈ V(G)) : G.ConnectedBetween x x :=
  ⟨nil x, by simpa, rfl, rfl⟩

@[symm]
lemma ConnectedBetween.symm (h : G.ConnectedBetween x y) : G.ConnectedBetween y x := by
  obtain ⟨w, hw, hx, hy⟩ := h
  exact ⟨w.reverse, hw.reverse, by simpa, by simpa⟩

instance : IsSymm _ G.ConnectedBetween where
  symm _ _ := ConnectedBetween.symm

lemma connectedBetween_comm : G.ConnectedBetween x y ↔ G.ConnectedBetween y x :=
  ⟨ConnectedBetween.symm, ConnectedBetween.symm⟩

lemma ConnectedBetween.left_mem (hxy : G.ConnectedBetween x y) : x ∈ V(G) :=
  let ⟨_, hw, hx, _⟩ := hxy
  hx ▸ hw.first_mem

lemma ConnectedBetween.right_mem (hxy : G.ConnectedBetween x y) : y ∈ V(G) :=
  hxy.symm.left_mem

lemma ConnectedBetween.trans (hxy : G.ConnectedBetween x y) (hyz : G.ConnectedBetween y z) :
    G.ConnectedBetween x z := by
  obtain ⟨w₁, hw₁, rfl, rfl⟩ := hxy
  obtain ⟨w₂, hw₂, heq, rfl⟩ := hyz
  exact ⟨w₁.append w₂, hw₁.append hw₂ heq.symm, by simp [heq], by simp⟩

instance : IsTrans _ G.ConnectedBetween where
  trans _ _ _ := ConnectedBetween.trans

@[simp]
lemma connectedBetween_self : G.ConnectedBetween x x ↔ x ∈ V(G) :=
  ⟨ConnectedBetween.left_mem, ConnectedBetween.refl⟩

lemma Adj.connectedBetween (h : G.Adj x y) : G.ConnectedBetween x y :=
  ⟨cons x h.choose (nil y), by simp [h.choose_spec, h.right_mem], by simp, by simp⟩

lemma IsLink.connectedBetween (h : G.IsLink e x y) : G.ConnectedBetween x y :=
  h.adj.connectedBetween

lemma ConnectedBetween.of_le (h : H.ConnectedBetween x y) (hle : H ≤ G) :
    G.ConnectedBetween x y := by
  obtain ⟨W, hW, rfl, rfl⟩ := h
  use W, hW.of_le hle

lemma ConnectedBetween.exists_isPath (h : G.ConnectedBetween x y) :
    ∃ P, G.IsPath P ∧ P.first = x ∧ P.last = y := by
  classical
  obtain ⟨W, hW, rfl, rfl⟩ := h
  exact ⟨W.dedup, by simp [hW.dedup_isPath]⟩

@[simp]
lemma not_connectedBetween_of_left_not_mem (hx : x ∉ V(G)) : ¬ G.ConnectedBetween x y := by
  rintro h
  exact hx h.left_mem

@[simp]
lemma not_connectedBetween_of_right_not_mem (hy : y ∉ V(G)) : ¬ G.ConnectedBetween x y := by
  rintro h
  exact hy h.right_mem

lemma IsWalk.connectedBetween_of_mem_of_mem (hW : G.IsWalk W) (hx : x ∈ W) (hy : y ∈ W) :
    G.ConnectedBetween x y := by
  suffices aux : ∀ ⦃z⦄, z ∈ W → G.ConnectedBetween z W.last from (aux hx).trans (aux hy).symm
  clear hx hy
  intro z hz
  induction hW generalizing z with
  | nil => simp_all
  | cons hW h ih =>
    obtain rfl | hz := by simpa using hz
    · exact h.connectedBetween.trans <| by simpa only [last_cons] using ih <| by simp
    simpa using ih hz

lemma IsWalk.connectedBetween_first_last (hW : G.IsWalk W) : G.ConnectedBetween W.first W.last :=
  hW.connectedBetween_of_mem_of_mem (by simp) <| by simp

lemma connectedBetween_induce_iff {X : Set α} (hx : x ∈ V(G)) :
    G[X].ConnectedBetween x y ↔ ∃ P, G.IsPath P ∧ P.first = x ∧ P.last = y ∧ V(P) ⊆ X := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨P, hP, rfl, rfl⟩ := h.exists_isPath
    refine ⟨P, ?_, rfl, rfl, hP.vertexSet_subset⟩
    cases P with
    | nil => simpa
    | cons u e W =>
      rw [isPath_induce_iff' (by simp)] at hP
      exact hP.1
  rintro ⟨P, h, rfl, rfl, hPX⟩
  cases P with
  | nil => simpa using hPX
  | cons u e W =>
    apply IsWalk.connectedBetween_first_last
    rw [isWalk_induce_iff' (by simp)]
    simp_all only [cons_isPath_iff, first_cons, cons_vertexSet, cons_isWalk_iff, true_and, and_true]
    exact h.1.isWalk

lemma IsComplete.connectedBetween (h : G.IsComplete) (hs : s ∈ V(G)) (ht : t ∈ V(G)) :
    G.ConnectedBetween s t := by
  obtain rfl | hne := eq_or_ne s t
  · simp [hs]
  exact (h s hs t ht hne).connectedBetween

lemma ConnectedBetween.isClosedSubgraph (h : G.ConnectedBetween x y) (hle : H ≤c G) (hx : x ∈ V(H))
    : H.ConnectedBetween x y := by
  obtain ⟨W, hW, rfl, rfl⟩ := h
  use W, hW.isWalk_isClosedSubgraph_of_first_mem hle hx

/-! ### Cut between two vertices -/

-- Beware that `CutBetween` does not check if `s` and `t` are in the graph.
structure CutBetween (G : Graph α β) (s t : α) where
  carrier : Set α
  carrier_subset : carrier ⊆ V(G)
  left_not_mem : s ∉ carrier
  right_not_mem : t ∉ carrier
  not_connectedBetween' : ¬ (G - carrier).ConnectedBetween s t

instance : SetLike (G.CutBetween s t) α where
  coe := (·.carrier)
  coe_injective' C1 C2 h := by rwa [CutBetween.mk.injEq]

@[ext]
lemma CutBetween.ext (C1 C2 : G.CutBetween s t) (h : (C1 : Set α) = C2) : C1 = C2 := by
  cases C1; cases C2; simp_all

@[simp]
lemma CutBetween.coe_subset (C : G.CutBetween s t) : (C : Set α) ⊆ V(G) := C.carrier_subset

@[simp]
lemma CutBetween.left_notMem (C : G.CutBetween s t) : s ∉ C := C.left_not_mem

@[simp]
lemma CutBetween.right_notMem (C : G.CutBetween s t) : t ∉ C := C.right_not_mem

@[simp]
lemma CutBetween.not_connectedBetween (C : G.CutBetween s t) : ¬ (G - C).ConnectedBetween s t :=
  C.not_connectedBetween'

@[simp]
lemma isEmtpy_cutBetween_self (hs : s ∈ V(G)) : IsEmpty (G.CutBetween s s) := by
  by_contra! h
  obtain ⟨C, _, hsC, _, h⟩ := h
  simp [hs, hsC] at h

@[simp]
lemma isEmpty_cutBetween_isLink (he : G.IsLink e s t) : IsEmpty (G.CutBetween s t) := by
  by_contra! h
  obtain ⟨C, _, hsC, htC, h⟩ := h
  exact h ⟨he.walk, by simp [hsC, htC], rfl, rfl⟩

def cutBetween_empty (h : ¬ G.ConnectedBetween s t) : G.CutBetween s t where
  carrier := ∅
  carrier_subset := empty_subset _
  left_not_mem := by simp
  right_not_mem := by simp
  not_connectedBetween' := by simpa

@[simp]
lemma cutBetween_empty_coe (h : ¬ G.ConnectedBetween s t) : (cutBetween_empty h : Set α) = ∅ := rfl

def CutBetween.symm (C : G.CutBetween s t) : G.CutBetween t s where
  carrier := C.carrier
  carrier_subset := C.carrier_subset
  left_not_mem := C.right_not_mem
  right_not_mem := C.left_not_mem
  not_connectedBetween' := by
    rw [← connectedBetween_comm]
    exact C.not_connectedBetween

@[simp]
lemma CutBetween.symm_coe (C : G.CutBetween s t) : (C.symm : Set α) = C := rfl

@[simp]
lemma CutBetween.symm_symm (C : G.CutBetween s t) : C.symm.symm = C := by
  ext x
  simp

def CutBetween.of_le (C : G.CutBetween s t) (hle : H ≤ G) : H.CutBetween s t where
  carrier := V(H) ∩ C
  carrier_subset := inter_subset_left
  left_not_mem := by simp [C.left_notMem]
  right_not_mem := by simp [C.right_notMem]
  not_connectedBetween' := by
    rw [vertexDelete_vertexSet_inter]
    exact mt (ConnectedBetween.of_le · (by gcongr)) C.not_connectedBetween

@[simp]
lemma CutBetween.of_le_coe (C : G.CutBetween s t) (hle : H ≤ G) :
    (C.of_le hle : Set α) = V(H) ∩ C := rfl

lemma IsWalk.not_disjoint_cutBetween (hW : G.IsWalk W) (C : G.CutBetween W.first W.last) :
    ¬ Disjoint V(W) C := by
  by_contra hc
  apply C.not_connectedBetween
  use W, hW.vertexDelete hc

lemma IsWalk.exists_mem_cutBetween (hW : G.IsWalk W) (C : G.CutBetween W.first W.last) :
    ∃ x ∈ V(W), x ∈ C := by
  have := hW.not_disjoint_cutBetween C
  rwa [not_disjoint_iff] at this

lemma IsComplete.cutBetween_isEmpty (h : G.IsComplete) (hs : s ∈ V(G)) (ht : t ∈ V(G)) :
    IsEmpty (G.CutBetween s t) := by
  by_contra! hc
  obtain ⟨C, hCG, hsC, htC, hconn⟩ := hc
  apply hconn
  obtain rfl | hne := eq_or_ne s t
  · simp [hsC, hs]
  apply Adj.connectedBetween
  simp only [vertexDelete_adj_iff]
  use h s hs t ht hne

@[simps]
def cutBetween_of_not_adj (hne : s ≠ t) (hnst : ¬ G.Adj s t) : G.CutBetween s t where
  carrier := V(G) \ {s, t}
  carrier_subset := diff_subset
  left_not_mem := by simp
  right_not_mem := by simp
  not_connectedBetween' := by
    contrapose! hnst
    obtain ⟨W, hW, rfl, rfl⟩ := hnst.exists_isPath
    match W with
    | .nil u => simp at hne
    | .cons u e (nil v) =>
      simp only [first_cons, last_cons, nil_last, cons_isPath_iff, nil_isPath_iff,
        vertexDelete_vertexSet, sdiff_sdiff_right_self, inf_eq_inter, mem_inter_iff, mem_insert_iff,
        mem_singleton_iff, or_true, and_true, nil_first, vertexDelete_isLink_iff, mem_diff, true_or,
        not_true_eq_false, and_false, not_false_eq_true, and_self, mem_nil_iff] at hW ⊢
      use e, hW.2.1
    | cons u e (cons v f w) =>
      simp_all only [first_cons, last_cons, ne_eq, cons_isPath_iff, isPath_vertexDelete_iff,
        vertexDelete_isLink_iff, mem_diff, mem_insert_iff, mem_singleton_iff, not_or, not_and,
        not_not, or_false, not_true_eq_false, and_false, not_false_eq_true, true_and, mem_cons_iff]
      obtain ⟨⟨⟨-, -⟩, ⟨-, hvwl, -⟩, -⟩, ⟨huv, -⟩, hne, -⟩ := hW
      obtain rfl := hvwl huv.right_mem (hne ·.symm)
      use e

structure EdgeCutBetween (G : Graph α β) (s t : α) where
  carrier : Set β
  carrier_subset : carrier ⊆ E(G)
  not_connectedBetween' : ¬ (G ＼ carrier).ConnectedBetween s t

instance : SetLike (G.EdgeCutBetween s t) β where
  coe := (·.carrier)
  coe_injective' C1 C2 h := by rwa [EdgeCutBetween.mk.injEq]

@[simp]
lemma EdgeCutBetween.coe_subset (C : G.EdgeCutBetween s t) : (C : Set β) ⊆ E(G) := C.carrier_subset

@[simp]
lemma EdgeCutBetween.not_connectedBetween (C : G.EdgeCutBetween s t) :
    ¬ (G ＼ C).ConnectedBetween s t :=
  C.not_connectedBetween'

@[simp]
lemma isEmpty_edgeCutBetween_self (hs : s ∈ V(G)) : IsEmpty (G.EdgeCutBetween s s) := by
  by_contra! h
  obtain ⟨C, _, h⟩ := h
  simp [hs] at h

def edgeCutBetween_empty (h : ¬ G.ConnectedBetween s t) : G.EdgeCutBetween s t where
  carrier := ∅
  carrier_subset := empty_subset _
  not_connectedBetween' := by simpa

@[simp]
lemma edgeCutBetween_empty_coe (h : ¬ G.ConnectedBetween s t) :
    (edgeCutBetween_empty h : Set β) = ∅ := rfl

def EdgeCutBetween.of_le (C : G.EdgeCutBetween s t) (hle : H ≤ G) : H.EdgeCutBetween s t where
  carrier := E(H) ∩ C
  carrier_subset := inter_subset_left
  not_connectedBetween' := by
    rw [edgeDelete_edgeSet_inter]
    exact mt (ConnectedBetween.of_le · (by gcongr)) C.not_connectedBetween

@[simp]
lemma EdgeCutBetween.of_le_coe (C : G.EdgeCutBetween s t) (hle : H ≤ G) :
    (C.of_le hle : Set β) = E(H) ∩ C := rfl

lemma IsWalk.not_disjoint_edgeCutBetween (hW : G.IsWalk W) (C : G.EdgeCutBetween W.first W.last) :
    ¬ Disjoint E(W) C := by
  intro hc
  apply C.not_connectedBetween
  use W, hW.edgeDelete hc

lemma IsWalk.exists_mem_edgeCutBetween (hW : G.IsWalk W) (C : G.EdgeCutBetween W.first W.last) :
    ∃ e ∈ E(W), e ∈ C := by
  have := hW.not_disjoint_edgeCutBetween C
  rwa [not_disjoint_iff] at this

/-! ### Ensemble of paths between two vertices -/

def internallyDisjoint (s t : α) {ι : Type*} (f : ι → WList α β) : Prop :=
  Pairwise (fun i j => V(f i) ∩ V(f j) = {s, t})

structure VertexEnsemble (G : Graph α β) (s t : α) (ι : Type*) where
  f : ι → WList α β
  isPath : ∀ i, G.IsPath (f i)
  first_eq : ∀ i, (f i).first = s
  last_eq : ∀ i, (f i).last = t
  internallyDisjoint : internallyDisjoint s t f

def VertexEnsemble.edgeDisjoint (P : G.VertexEnsemble s t ι) : Prop :=
  Pairwise (Disjoint on WList.edgeSet on P.f)

lemma VertexEnsemble.eq_or_eq_of_mem {i j} (P : G.VertexEnsemble s t ι) (hxi : x ∈ V(P.f i))
    (hxj : x ∈ V(P.f j)) (hne : i ≠ j) : x = s ∨ x = t := by
  have := P.internallyDisjoint hne ▸ (show x ∈ V(P.f i) ∩ V(P.f j) by simp [hxi, hxj])
  simpa

@[simps]
def vertexEnsemble_empty (G : Graph α β) (s t : α) (ι : Type*) [h : IsEmpty ι] :
    G.VertexEnsemble s t ι where
  f _ := nil s
  isPath := (h.elim ·)
  first_eq := (h.elim ·)
  last_eq := (h.elim ·)
  internallyDisjoint := (h.elim ·)

@[simp]
lemma vertexEnsemble_empty_edgeDisjoint [h : IsEmpty ι] :
    (G.vertexEnsemble_empty s t ι).edgeDisjoint := by
  simp [VertexEnsemble.edgeDisjoint]

@[simps]
def vertexEnsemble_nil (G : Graph α β) (h : s ∈ V(G)) (ι : Type*) : G.VertexEnsemble s s ι where
  f _ := nil s
  isPath i := by simpa
  first_eq i := by simp
  last_eq i := by simp
  internallyDisjoint i j h := by simp

@[simp]
lemma vertexEnsemble_nil_edgeDisjoint (h : s ∈ V(G)) :
    (G.vertexEnsemble_nil h ι).edgeDisjoint :=
  fun _ _ _ ↦ by simp [vertexEnsemble_nil]

@[simps]
def IsLink.vertexEnsemble (ι : Type*) (h : G.IsLink e s t) (hne : s ≠ t) :
    G.VertexEnsemble s t ι where
  f _ := cons s e (nil t)
  isPath i := by simpa [h, h.right_mem]
  first_eq i := by simp
  last_eq i := by simp
  internallyDisjoint i j h := by simp

@[simps]
def IsPath.vertexEnsemble (h : G.IsPath P) : G.VertexEnsemble P.first P.last PUnit where
  f _ := P
  isPath i := h
  first_eq i := by simp
  last_eq i := by simp
  internallyDisjoint i j h := by simp at h

@[simp]
lemma IsPath.vertexEnsemble_edgeDisjoint (h : G.IsPath P) : (h.vertexEnsemble).edgeDisjoint :=
  fun _ _ hne ↦ (hne rfl).elim

@[simps]
def VertexEnsemble.comp (P : G.VertexEnsemble s t ι) (f : ι' ↪ ι) : G.VertexEnsemble s t ι' where
  f := P.f ∘ f
  isPath i := P.isPath (f i)
  first_eq i := P.first_eq (f i)
  last_eq i := P.last_eq (f i)
  internallyDisjoint i j h := P.internallyDisjoint (by simpa)

@[simp]
lemma VertexEnsemble.comp_edgeDisjoint {P : G.VertexEnsemble s t ι} (hP : P.edgeDisjoint)
    (f : ι' ↪ ι) : (P.comp f).edgeDisjoint := by
  rintro i j hne
  simp only [onFun, comp, comp_apply]
  exact hP (f.inj'.ne hne)

@[simps]
def VertexEnsemble.of_le (P : H.VertexEnsemble s t ι) (hle : H ≤ G) : G.VertexEnsemble s t ι where
  f := P.f
  isPath i := P.isPath i |>.of_le hle
  first_eq i := P.first_eq i
  last_eq i := P.last_eq i
  internallyDisjoint _ _ h := P.internallyDisjoint h

@[simp]
lemma VertexEnsemble.of_le_edgeDisjoint {P : H.VertexEnsemble s t ι} (hP : P.edgeDisjoint)
    (hle : H ≤ G) : (P.of_le hle).edgeDisjoint :=
  hP

/-- internal vertex set of a vertex ensemble -/
def VertexEnsemble.vertexSet (P : G.VertexEnsemble s t ι) : Set α :=
  (⋃ i, V(P.f i)) \ {s, t}

lemma VertexEnsemble.subset_vertexSet_of_mem (P : G.VertexEnsemble s t ι) (i : ι) :
    V(P.f i) \ {s, t} ⊆ P.vertexSet :=
  diff_subset_diff_left <| subset_iUnion (fun i ↦ V(P.f i)) i

@[simps]
def VertexEnsemble.sum (P : G.VertexEnsemble s t ι) (Q : G.VertexEnsemble s t ι')
    (h : Disjoint P.vertexSet Q.vertexSet) : G.VertexEnsemble s t (ι ⊕ ι') where
  f i := i.elim P.f Q.f
  isPath i := match i with
  | Sum.inl i => P.isPath i
  | Sum.inr i => Q.isPath i
  first_eq i := match i with
  | Sum.inl i => P.first_eq i
  | Sum.inr i => Q.first_eq i
  last_eq i := match i with
  | Sum.inl i => P.last_eq i
  | Sum.inr i => Q.last_eq i
  internallyDisjoint i j hne := match i, j with
  | Sum.inl i, Sum.inl j => P.internallyDisjoint (by simpa using hne)
  | Sum.inl i, Sum.inr j => by
    simp only
    have := h.mono (P.subset_vertexSet_of_mem i) (Q.subset_vertexSet_of_mem j)
    rw [disjoint_iff_inter_eq_empty, diff_inter_diff_right, diff_eq_empty] at this
    apply this.antisymm
    simp only [subset_inter_iff]
    exact ⟨by simp [← P.first_eq i, first_mem, ← P.last_eq i, last_mem, pair_subset],
      by simp [← Q.first_eq j, first_mem, ← Q.last_eq j, last_mem, pair_subset]⟩
  | Sum.inr i, Sum.inl j => by
    simp only
    have := h.mono (P.subset_vertexSet_of_mem j) (Q.subset_vertexSet_of_mem i)
    rw [disjoint_iff_inter_eq_empty, diff_inter_diff_right, diff_eq_empty, inter_comm] at this
    apply this.antisymm
    simp only [subset_inter_iff]
    exact ⟨by simp [← Q.first_eq i, first_mem, ← Q.last_eq i, last_mem, pair_subset],
      by simp [← P.first_eq j, first_mem, ← P.last_eq j, last_mem, pair_subset]⟩
  | Sum.inr i, Sum.inr j => Q.internallyDisjoint (by simpa using hne)

/-! ### k-connectivity between two vertices -/

def ConnBetweenGe (G : Graph α β) (s t : α) (n : ℕ) : Prop :=
  ∀ C : G.CutBetween s t, n ≤ (↑C : Set α).encard

@[simp]
lemma connBetweenGe_zero (G : Graph α β) (s t : α) : G.ConnBetweenGe s t 0 := by
  simp [ConnBetweenGe]

lemma ConnBetweenGe.anti_right (hle : n ≤ m) (h : G.ConnBetweenGe s t m) : G.ConnBetweenGe s t n :=
  fun C ↦ le_trans (by norm_cast) (h C)

@[symm]
lemma ConnBetweenGe.symm (h : G.ConnBetweenGe s t n) : G.ConnBetweenGe t s n := (h <| ·.symm)

instance : IsSymm _ (G.ConnBetweenGe · · n) where
  symm _ _ := ConnBetweenGe.symm

lemma connBetweenGe_comm : G.ConnBetweenGe s t n ↔ G.ConnBetweenGe t s n :=
  ⟨ConnBetweenGe.symm, ConnBetweenGe.symm⟩

@[simp]
lemma connBetweenGe_one_iff : G.ConnBetweenGe s t 1 ↔ G.ConnectedBetween s t := by
  refine ⟨fun h => ?_, fun h C => ?_⟩
  · by_contra hc
    simpa using h <| cutBetween_empty hc
  obtain ⟨w, hw, rfl, rfl⟩ := h
  obtain ⟨x, hxw, hxC⟩ := hw.exists_mem_cutBetween C
  simp only [cast_one, one_le_encard_iff_nonempty]
  use x, hxC

lemma connBetweenGe_self (hs : s ∈ V(G)) (n : ℕ) : G.ConnBetweenGe s s n :=
  (isEmtpy_cutBetween_self hs).elim

lemma IsLink.connBetweenGe (h : G.IsLink e s t) (n : ℕ) : G.ConnBetweenGe s t n :=
  (isEmpty_cutBetween_isLink h).elim

lemma ConnBetweenGe.of_le (h : H.ConnBetweenGe s t n) (hle : H ≤ G) : G.ConnBetweenGe s t n := by
  rintro C
  have := by simpa using h (C.of_le hle)
  exact this.trans <| encard_le_encard inter_subset_right

lemma IsComplete.connBetweenGe (h : G.IsComplete) (hs : s ∈ V(G)) (ht : t ∈ V(G)) (n : ℕ) :
    G.ConnBetweenGe s t n :=
  h.cutBetween_isEmpty hs ht |>.elim

lemma connBetweenGe_le_diff_encard (h : G.ConnBetweenGe s t n) (hne : s ≠ t) (hadj : ¬ G.Adj s t) :
    n ≤ (V(G) \ {s, t}).encard := by
  simpa using h (cutBetween_of_not_adj hne hadj)

lemma connBetweenGe_le_encard (h : G.ConnBetweenGe s t n) (hne : s ≠ t) (hadj : ¬ G.Adj s t) :
    n ≤ V(G).encard :=
  (connBetweenGe_le_diff_encard h hne hadj).trans <| encard_le_encard diff_subset

def EdgeConnBetweenGe (G : Graph α β) (s t : α) (n : ℕ) : Prop :=
  ∀ C : G.EdgeCutBetween s t, n ≤ (↑C : Set β).encard

@[simp]
lemma EdgeConnBetweenGe_zero (G : Graph α β) (s t : α) :
    G.EdgeConnBetweenGe s t 0 := by
  simp [EdgeConnBetweenGe]

lemma EdgeConnBetweenGe.anti_right (hle : n ≤ m) (h : G.EdgeConnBetweenGe s t m) :
    G.EdgeConnBetweenGe s t n :=
  fun C ↦ le_trans (by norm_cast) (h C)

lemma edgeConnBetweenGe_one_iff :
    G.EdgeConnBetweenGe s t 1 ↔ G.ConnectedBetween s t := by
  refine ⟨fun h => ?_, fun h C => ?_⟩
  · by_contra hc
    simpa using h <| edgeCutBetween_empty hc
  obtain ⟨w, hw, rfl, rfl⟩ := h
  obtain ⟨x, hxw, hxC⟩ := hw.exists_mem_edgeCutBetween C
  simp only [cast_one, one_le_encard_iff_nonempty]
  use x, hxC

@[simp]
lemma edgeConnBetweenGe_self (hs : s ∈ V(G)) (n : ℕ) :
    G.EdgeConnBetweenGe s s n :=
  (isEmpty_edgeCutBetween_self hs).elim

lemma EdgeConnBetweenGe.of_le (h : H.EdgeConnBetweenGe s t n) (hle : H ≤ G) :
    G.EdgeConnBetweenGe s t n := by
  rintro C
  have := by simpa using h (C.of_le hle)
  exact this.trans <| encard_le_encard inter_subset_right
