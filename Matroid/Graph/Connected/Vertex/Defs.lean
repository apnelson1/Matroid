import Matroid.Graph.Lattice
import Matroid.Graph.Walk.Path

open Set Function Nat WList

variable {α β ι ι' : Type*} {G H K : Graph α β} {s t u v x x₁ x₂ y y₁ y₂ z : α} {n m : ℕ}
  {e e' f g : β} {U V S S' T T' X Y : Set α} {F F' R R': Set β} {C W P Q : WList α β}

namespace Graph


/-! ### Connectivity between two vertices -/

def ConnectedBetween (G : Graph α β) (x y : α) : Prop :=
  ∃ w : WList α β, G.IsWalk w ∧ w.first = x ∧ w.last = y

lemma ConnectedBetween.refl (hx : x ∈ V(G)) : G.ConnectedBetween x x :=
  ⟨nil x, by simpa, rfl, rfl⟩

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

lemma IsWalk.isWalk_or_isWalk_compl_of_closedSubgraph (H : G.ClosedSubgraph) (hW : G.IsWalk W) :
    H.val.IsWalk W ∨ Hᶜ.val.IsWalk W := by
  by_cases hx : W.first ∈ V(H.val)
  · exact .inl <| hW.isWalk_isClosedSubgraph H.prop hx
  exact .inr <| hW.isWalk_isClosedSubgraph Hᶜ.prop <| by simp [hx, hW.first_mem]

lemma ConnectedBetween.mem_vertexSet_iff (H : G.ClosedSubgraph) :
    ∀ {x y : α}, G.ConnectedBetween x y → (x ∈ V(H.val) ↔ y ∈ V(H.val)) := by
  suffices ∀ x y, G.ConnectedBetween x y → x ∈ V(H.val) → y ∈ V(H.val) by
    exact fun x y h => ⟨fun hx => this x y h hx, fun hy => this y x h.symm hy⟩
  rintro x y ⟨w, hw, rfl, rfl⟩ hx
  refine hw.isWalk_or_isWalk_compl_of_closedSubgraph H |>.resolve_right (fun h ↦ ?_) |>.last_mem
  simpa [hx] using h.first_mem

lemma IsWalk.isWalk_or_isWalk_of_union_of_disjoint (h : G.StronglyDisjoint H)
    (hW : (G ∪ H).IsWalk W) : G.IsWalk W ∨ H.IsWalk W := by
  obtain hCG | hCH := hW.isWalk_or_isWalk_compl_of_closedSubgraph ⟨G, h.isClosedSubgraph_union_left⟩
  · exact .inl hCG
  rw [ClosedSubgraph.compl_eq_of_stronglyDisjoint_union h] at hCH
  exact .inr hCH

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


/-! ### Cut between two vertices -/

structure CutBetween (G : Graph α β) (s t : α) where
  carrier : Set α
  carrier_subset : carrier ⊆ V(G)
  left_not_mem : s ∉ carrier
  right_not_mem : t ∉ carrier
  not_connectedBetween : ¬ (G - carrier).ConnectedBetween s t

instance : SetLike (G.CutBetween s t) α where
  coe := (·.carrier)
  coe_injective' C1 C2 h := by rwa [CutBetween.mk.injEq]

@[ext]
lemma CutBetween.ext (C1 C2 : G.CutBetween s t) (h : (C1 : Set α) = C2) : C1 = C2 := by
  cases C1; cases C2; simp_all

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
  not_connectedBetween := by simpa

@[simp]
lemma cutBetween_empty_coe (h : ¬ G.ConnectedBetween s t) : (cutBetween_empty h : Set α) = ∅ := rfl

def CutBetween.symm (C : G.CutBetween s t) : G.CutBetween t s where
  carrier := C.carrier
  carrier_subset := C.carrier_subset
  left_not_mem := C.right_not_mem
  right_not_mem := C.left_not_mem
  not_connectedBetween := by
    rw [← connectedBetween_comm]
    exact C.not_connectedBetween

@[simp]
lemma CutBetween.symm_coe (C : G.CutBetween s t) : (C.symm : Set α) = C := rfl

@[simp]
lemma CutBetween.symm_symm (C : G.CutBetween s t) : C.symm.symm = C := by
  ext x
  simp

lemma IsWalk.not_disjoint_cutBetween (hW : G.IsWalk W) (C : G.CutBetween W.first W.last) :
    ¬ Disjoint V(W) C := by
  by_contra hc
  apply C.not_connectedBetween
  use W, hW.vertexDelete hc

lemma IsWalk.exists_mem_cutBetween (hW : G.IsWalk W) (C : G.CutBetween W.first W.last) :
    ∃ x ∈ V(W), x ∈ C := by
  have := hW.not_disjoint_cutBetween C
  rwa [not_disjoint_iff] at this

structure EdgeCutBetween (G : Graph α β) (s t : α) where
  carrier : Set β
  carrier_subset : carrier ⊆ E(G)
  not_connectedBetween : ¬ (G ＼ carrier).ConnectedBetween s t

instance : SetLike (G.EdgeCutBetween s t) β where
  coe := (·.carrier)
  coe_injective' C1 C2 h := by rwa [EdgeCutBetween.mk.injEq]

@[simp]
lemma isEmpty_edgeCutBetween_self (hs : s ∈ V(G)) : IsEmpty (G.EdgeCutBetween s s) := by
  by_contra! h
  obtain ⟨C, _, h⟩ := h
  simp [hs] at h

def edgeCutBetween_empty (h : ¬ G.ConnectedBetween s t) : G.EdgeCutBetween s t where
  carrier := ∅
  carrier_subset := empty_subset _
  not_connectedBetween := by simpa

@[simp]
lemma edgeCutBetween_empty_coe (h : ¬ G.ConnectedBetween s t) :
    (edgeCutBetween_empty h : Set β) = ∅ := rfl

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
  first : ∀ i, (f i).first = s
  last : ∀ i, (f i).last = t
  internallyDisjoint : internallyDisjoint s t f

def vertexEnsemble_empty [h : IsEmpty ι] : G.VertexEnsemble s t ι where
  f := fun _ => nil s
  isPath := (h.elim ·)
  first := (h.elim ·)
  last := (h.elim ·)
  internallyDisjoint := (h.elim ·)

def vertexEnsemble_nil (ι : Type*) (h : s ∈ V(G)) : G.VertexEnsemble s s ι where
  f _ := nil s
  isPath i := by simpa
  first i := by simp
  last i := by simp
  internallyDisjoint i j h := by simp

def IsLink.vertexEnsemble (ι : Type*) (h : G.IsLink e s t) (hne : s ≠ t) :
    G.VertexEnsemble s t ι where
  f _ := cons s e (nil t)
  isPath i := by simpa [h, h.right_mem]
  first i := by simp
  last i := by simp
  internallyDisjoint i j h := by simp

def IsPath.vertexEnsemble (h : G.IsPath P) : G.VertexEnsemble P.first P.last PUnit where
  f _ := P
  isPath i := h
  first i := by simp
  last i := by simp
  internallyDisjoint i j h := by simp at h

def VertexEnsemble.comp (P : G.VertexEnsemble s t ι) (f : ι' ↪ ι) : G.VertexEnsemble s t ι' where
  f := P.f ∘ f
  isPath i := P.isPath (f i)
  first i := P.first (f i)
  last i := P.last (f i)
  internallyDisjoint i j h := P.internallyDisjoint (by simpa)

-- def VertexEnsemble.of_le (P : H.VertexEnsemble s t ι) (hle : H ≤ G) : G.VertexEnsemble s t ι :=
--   ⟨(P.f ·|>.of_le hle), P.internallyDisjoint, P.stConnected⟩

/-- internal vertex set of a vertex ensemble -/
def VertexEnsemble.vertexSet (P : G.VertexEnsemble s t ι) : Set α :=
  (⋃ i, V(P.f i)) \ {s, t}

lemma VertexEnsemble.subset_vertexSet_of_mem (P : G.VertexEnsemble s t ι) (i : ι) :
    V(P.f i) \ {s, t} ⊆ P.vertexSet :=
  diff_subset_diff_left <| subset_iUnion (fun i ↦ V(P.f i)) i

def VertexEnsemble.sum (P : G.VertexEnsemble s t ι) (Q : G.VertexEnsemble s t ι')
    (h : Disjoint P.vertexSet Q.vertexSet) : G.VertexEnsemble s t (ι ⊕ ι') where
  f i := match i with
  | Sum.inl i => P.f i
  | Sum.inr i => Q.f i
  isPath i := match i with
  | Sum.inl i => P.isPath i
  | Sum.inr i => Q.isPath i
  first i := match i with
  | Sum.inl i => P.first i
  | Sum.inr i => Q.first i
  last i := match i with
  | Sum.inl i => P.last i
  | Sum.inr i => Q.last i
  internallyDisjoint i j hne := match i, j with
  | Sum.inl i, Sum.inl j => P.internallyDisjoint (by simpa using hne)
  | Sum.inl i, Sum.inr j => by
    simp only
    have := h.mono (P.subset_vertexSet_of_mem i) (Q.subset_vertexSet_of_mem j)
    rw [disjoint_iff_inter_eq_empty, diff_inter_diff_right, diff_eq_empty] at this
    apply this.antisymm
    simp only [subset_inter_iff]
    exact ⟨by simp [← P.first i, first_mem, ← P.last i, last_mem, pair_subset],
      by simp [← Q.first j, first_mem, ← Q.last j, last_mem, pair_subset]⟩
  | Sum.inr i, Sum.inl j => by
    simp only
    have := h.mono (P.subset_vertexSet_of_mem j) (Q.subset_vertexSet_of_mem i)
    rw [disjoint_iff_inter_eq_empty, diff_inter_diff_right, diff_eq_empty, inter_comm] at this
    apply this.antisymm
    simp only [subset_inter_iff]
    exact ⟨by simp [← Q.first i, first_mem, ← Q.last i, last_mem, pair_subset],
      by simp [← P.first j, first_mem, ← P.last j, last_mem, pair_subset]⟩
  | Sum.inr i, Sum.inr j => Q.internallyDisjoint (by simpa using hne)

/-! ### k-connectivity between two vertices -/

def ConnectivityBetweenGe (G : Graph α β) (s t : α) (n : ℕ) : Prop :=
  ∀ C : G.CutBetween s t, n ≤ (↑C : Set α).encard

@[simp]
lemma connectivityBetweenGe_zero (G : Graph α β) (s t : α) : G.ConnectivityBetweenGe s t 0 := by
  simp [ConnectivityBetweenGe]

lemma ConnectivityBetweenGe.anti_right (hle : n ≤ m) (h : G.ConnectivityBetweenGe s t m) :
    G.ConnectivityBetweenGe s t n :=
  fun C ↦ le_trans (by norm_cast) (h C)

lemma ConnectivityBetweenGe.symm (h : G.ConnectivityBetweenGe s t n) :
    G.ConnectivityBetweenGe t s n := (h <| ·.symm)

instance : IsSymm _ (G.ConnectivityBetweenGe · · n) where
  symm _ _ := ConnectivityBetweenGe.symm

lemma connectivityBetweenGe_comm : G.ConnectivityBetweenGe s t n ↔ G.ConnectivityBetweenGe t s n :=
  ⟨ConnectivityBetweenGe.symm, ConnectivityBetweenGe.symm⟩

@[simp]
lemma connectivityBetweenGe_one_iff : G.ConnectivityBetweenGe s t 1 ↔ G.ConnectedBetween s t := by
  refine ⟨fun h => ?_, fun h C => ?_⟩
  · by_contra hc
    simpa using h <| cutBetween_empty hc
  obtain ⟨w, hw, rfl, rfl⟩ := h
  obtain ⟨x, hxw, hxC⟩ := hw.exists_mem_cutBetween C
  simp only [cast_one, one_le_encard_iff_nonempty]
  use x, hxC

lemma connectivityBetweenGe_self (hs : s ∈ V(G)) (n : ℕ) : G.ConnectivityBetweenGe s s n :=
  (isEmtpy_cutBetween_self hs).elim

lemma IsLink.connectivityBetweenGe (h : G.IsLink e s t) (n : ℕ) : G.ConnectivityBetweenGe s t n :=
  (isEmpty_cutBetween_isLink h).elim

def EdgeConnectivityBetweenGe (G : Graph α β) (s t : α) (n : ℕ) : Prop :=
  ∀ C : G.EdgeCutBetween s t, n ≤ (↑C : Set β).encard

@[simp]
lemma EdgeConnectivityBetweenGe_zero (G : Graph α β) (s t : α) :
    G.EdgeConnectivityBetweenGe s t 0 := by
  simp [EdgeConnectivityBetweenGe]

lemma EdgeConnectivityBetweenGe.anti_right (hle : n ≤ m) (h : G.EdgeConnectivityBetweenGe s t m) :
    G.EdgeConnectivityBetweenGe s t n :=
  fun C ↦ le_trans (by norm_cast) (h C)

lemma edgeConnectivityBetweenGe_one_iff :
    G.EdgeConnectivityBetweenGe s t 1 ↔ G.ConnectedBetween s t := by
  refine ⟨fun h => ?_, fun h C => ?_⟩
  · by_contra hc
    simpa using h <| edgeCutBetween_empty hc
  obtain ⟨w, hw, rfl, rfl⟩ := h
  obtain ⟨x, hxw, hxC⟩ := hw.exists_mem_edgeCutBetween C
  simp only [cast_one, one_le_encard_iff_nonempty]
  use x, hxC

@[simp]
lemma edgeConnectivityBetweenGe_self (hs : s ∈ V(G)) (n : ℕ) :
    G.EdgeConnectivityBetweenGe s s n :=
  (isEmpty_edgeCutBetween_self hs).elim
