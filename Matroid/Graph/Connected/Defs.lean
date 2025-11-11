import Matroid.Graph.Lattice
import Matroid.Graph.Finite
import Matroid.Graph.Degree.Defs
import Matroid.Graph.Degree.Constructions
import Mathlib.Data.Set.Insert
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Real.Basic
import Matroid.ForMathlib.Set

open Set Function Nat WList

variable {α β : Type*} {G H K : Graph α β} {s t u v x x₁ x₂ y y₁ y₂ z : α} {n m : ℕ}
  {e e' f g : β} {U V S S' T T' X Y : Set α} {F F' R R': Set β} {C W P Q : WList α β}

namespace Graph


/-! ### Connectivity between two vertices -/

def VertexConnected (G : Graph α β) (x y : α) : Prop :=
  ∃ w : WList α β, G.IsWalk w ∧ w.first = x ∧ w.last = y

lemma VertexConnected.refl (hx : x ∈ V(G)) : G.VertexConnected x x :=
  ⟨nil x, by simpa, rfl, rfl⟩

lemma VertexConnected.symm (h : G.VertexConnected x y) : G.VertexConnected y x := by
  obtain ⟨w, hw, hx, hy⟩ := h
  exact ⟨w.reverse, hw.reverse, by simpa, by simpa⟩

instance : IsSymm _ G.VertexConnected where
  symm _ _ := VertexConnected.symm

lemma VertexConnected_comm : G.VertexConnected x y ↔ G.VertexConnected y x :=
  ⟨VertexConnected.symm, VertexConnected.symm⟩

lemma VertexConnected.left_mem (hxy : G.VertexConnected x y) : x ∈ V(G) :=
  let ⟨_, hw, hx, _⟩ := hxy
  hx ▸ hw.first_mem

lemma VertexConnected.right_mem (hxy : G.VertexConnected x y) : y ∈ V(G) :=
  hxy.symm.left_mem

lemma VertexConnected.trans (hxy : G.VertexConnected x y) (hyz : G.VertexConnected y z) :
    G.VertexConnected x z := by
  obtain ⟨w₁, hw₁, rfl, rfl⟩ := hxy
  obtain ⟨w₂, hw₂, heq, rfl⟩ := hyz
  exact ⟨w₁.append w₂, hw₁.append hw₂ heq.symm, by simp [heq], by simp⟩

instance : IsTrans _ G.VertexConnected where
  trans _ _ _ := VertexConnected.trans

@[simp]
lemma vertexConnected_self : G.VertexConnected x x ↔ x ∈ V(G) :=
  ⟨VertexConnected.left_mem, VertexConnected.refl⟩

@[simp]
lemma not_vertexConnected_of_left_not_mem (hx : x ∉ V(G)) : ¬ G.VertexConnected x y := by
  rintro h
  exact hx h.left_mem

@[simp]
lemma not_vertexConnected_of_right_not_mem (hy : y ∉ V(G)) : ¬ G.VertexConnected x y := by
  rintro h
  exact hy h.right_mem

lemma Adj.vertexConnected (h : G.Adj x y) : G.VertexConnected x y :=
  ⟨cons x h.choose (nil y), by simp [h.choose_spec, h.right_mem], by simp, by simp⟩

lemma IsLink.vertexConnected (h : G.IsLink e x y) : G.VertexConnected x y :=
  h.adj.vertexConnected

lemma VertexConnected.of_le (h : H.VertexConnected x y) (hle : H ≤ G) : G.VertexConnected x y := by
  obtain ⟨W, hW, rfl, rfl⟩ := h
  use W, hW.of_le hle

lemma VertexConnected.exists_isPath (h : G.VertexConnected x y) :
    ∃ P, G.IsPath P ∧ P.first = x ∧ P.last = y := by
  classical
  obtain ⟨W, hW, rfl, rfl⟩ := h
  exact ⟨W.dedup, by simp [hW.dedup_isPath]⟩

lemma IsWalk.vertexConnected_of_mem_of_mem (hW : G.IsWalk W) (hx : x ∈ W) (hy : y ∈ W) :
    G.VertexConnected x y := by
  suffices aux : ∀ ⦃z⦄, z ∈ W → G.VertexConnected z W.last from (aux hx).trans (aux hy).symm
  clear hx hy
  intro z hz
  induction hW generalizing z with
  | nil => simp_all
  | cons hW h ih =>
    obtain rfl | hz := by simpa using hz
    · exact h.vertexConnected.trans <| by simpa only [last_cons] using ih <| by simp
    simpa using ih hz

lemma IsWalk.isWalk_or_isWalk_compl_of_closedSubgraph (H : G.ClosedSubgraph) (hW : G.IsWalk W) :
    H.val.IsWalk W ∨ Hᶜ.val.IsWalk W := by
  by_cases hx : W.first ∈ V(H.val)
  · exact .inl <| hW.isWalk_isClosedSubgraph H.prop hx
  exact .inr <| hW.isWalk_isClosedSubgraph Hᶜ.prop <| by simp [hx, hW.first_mem]

lemma VertexConnected.mem_vertexSet_iff (H : G.ClosedSubgraph) :
    ∀ {x y : α}, G.VertexConnected x y → (x ∈ V(H.val) ↔ y ∈ V(H.val)) := by
  suffices ∀ x y, G.VertexConnected x y → x ∈ V(H.val) → y ∈ V(H.val) by
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

lemma IsWalk.vertexConnected_first_last (hW : G.IsWalk W) : G.VertexConnected W.first W.last :=
  hW.vertexConnected_of_mem_of_mem (by simp) <| by simp

lemma vertexConnected_induce_iff {X : Set α} (hx : x ∈ V(G)) :
    G[X].VertexConnected x y ↔ ∃ P, G.IsPath P ∧ P.first = x ∧ P.last = y ∧ V(P) ⊆ X := by
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
    apply IsWalk.vertexConnected_first_last
    rw [isWalk_induce_iff' (by simp)]
    simp_all only [cons_isPath_iff, first_cons, cons_vertexSet, cons_isWalk_iff, true_and, and_true]
    exact h.1.isWalk

structure VertexCut (G : Graph α β) (s t : α) where
  carrier : Set α
  carrier_subset : carrier ⊆ V(G)
  left_not_mem : s ∉ carrier
  right_not_mem : t ∉ carrier
  not_vertexConnected : ¬ (G - carrier).VertexConnected s t

instance : SetLike (G.VertexCut s t) α where
  coe := (·.carrier)
  coe_injective' C1 C2 h := by rwa [VertexCut.mk.injEq]

def vertexCut_empty (h : ¬ G.VertexConnected s t) : G.VertexCut s t where
  carrier := ∅
  carrier_subset := empty_subset _
  left_not_mem := by simp
  right_not_mem := by simp
  not_vertexConnected := by simpa

@[simp]
lemma vertexCut_empty_coe (h : ¬ G.VertexConnected s t) : (vertexCut_empty h : Set α) = ∅ := rfl

def VertexConnectivityGe (G : Graph α β) (s t : α) (n : ℕ) : Prop :=
  ∀ X : G.VertexCut s t, n ≤ (↑X : Set α).encard

lemma VertexConnectivityGe_zero (G : Graph α β) (s t : α) : G.VertexConnectivityGe s t 0 := by
  simp [VertexConnectivityGe]


/-! ### Connectivity between two sets -/

structure SetCut (G : Graph α β) (S T : Set α) where
  carrier : Set α
  carrier_subset : carrier ⊆ V(G)
  ST_disconnects : ∀ s ∈ S, ∀ t ∈ T, ¬ (G - carrier).VertexConnected s t

instance : SetLike (G.SetCut S T) α where
  coe := (·.carrier)
  coe_injective' C1 C2 h := by rwa [SetCut.mk.injEq]

@[simp]
lemma SetCut.coe_subset (C : G.SetCut S T) : ↑C ⊆ V(G) := C.carrier_subset

@[simps]
def setCut_of_left (G : Graph α β) (S T : Set α) : G.SetCut S T where
  carrier := V(G) ∩ S
  carrier_subset := Set.inter_subset_left
  ST_disconnects s hs t ht h := by simpa [hs] using h.left_mem

@[simps]
def setCut_of_right (G : Graph α β) (S T : Set α) : G.SetCut S T where
  carrier := V(G) ∩ T
  carrier_subset := Set.inter_subset_left
  ST_disconnects s hs t ht h := by simpa [ht] using h.right_mem

@[simps]
def SetCut.vertexDelete (C : G.SetCut S T) (X : Set α) : (G - X).SetCut S T where
  carrier := C \ X
  carrier_subset := by
    rw [vertexDelete_vertexSet]
    exact diff_subset_diff_left C.coe_subset
  ST_disconnects s hs t ht h := by
    apply C.ST_disconnects s hs t ht
    simp only [vertexDelete_vertexDelete, union_diff_self] at h
    apply h.of_le
    rw [union_comm, ← vertexDelete_vertexDelete]
    exact vertexDelete_le

@[simps]
def SetCut.subset (C : G.SetCut S T) (hS : S' ⊆ S) (hT : T' ⊆ T) : G.SetCut S' T' where
  carrier := C
  carrier_subset := C.coe_subset
  ST_disconnects := fun s hs t ht h ↦ C.ST_disconnects s (hS hs) t (hT ht) h

@[simps]
def SetCut.of_vertexDelete (C : (G - X).SetCut S T) : G.SetCut S T where
  carrier := (X ∩ V(G)) ∪ C
  carrier_subset := by
    simp only [union_subset_iff, inter_subset_right, true_and]
    exact C.coe_subset.trans <| (G.vertexDelete_vertexSet X) ▸ diff_subset
  ST_disconnects s hs t ht h := by
    apply C.ST_disconnects s hs t ht
    rw [vertexDelete_vertexDelete]
    convert h using 1
    rw [← vertexDelete_vertexSet_inter, inter_comm, union_inter_distrib_right]
    congr
    exact inter_eq_left.mpr <| C.coe_subset.trans <| (G.vertexDelete_vertexSet X) ▸ diff_subset

@[simps]
def SetCut.of_vertexDelete' (C : (G - X).SetCut S T) : G.SetCut (S ∪ X) (T ∪ X) where
  carrier := (X ∩ V(G)) ∪ C
  carrier_subset := by
    simp only [union_subset_iff, inter_subset_right, true_and]
    exact C.coe_subset.trans <| (G.vertexDelete_vertexSet X) ▸ diff_subset
  ST_disconnects s hs t ht h := by
    obtain hs | hs := hs.symm
    · have := h.left_mem
      simp only [vertexDelete_vertexSet, mem_diff, mem_union, mem_inter_iff, hs, true_and,
        SetLike.mem_coe, not_or] at this
      tauto
    obtain ht | ht := ht.symm
    · have := h.right_mem
      simp only [vertexDelete_vertexSet, mem_diff, mem_union, mem_inter_iff, ht, true_and,
        SetLike.mem_coe, not_or] at this
      tauto
    exact C.of_vertexDelete.ST_disconnects s hs t ht h

def SetConnected (G : Graph α β) (S T : Set α) : Prop :=
  ∃ s ∈ S, ∃ t ∈ T, G.VertexConnected s t

lemma SetConnected.of_le (h : G.SetConnected S T) (hle : G ≤ H) : H.SetConnected S T := by
  obtain ⟨s, hs, t, ht, hst⟩ := h
  exact ⟨s, hs, t, ht, hst.of_le hle⟩

def SetConnectivityGe (G : Graph α β) (S T : Set α) (n : ℕ) : Prop :=
  ∀ C : G.SetCut S T, n ≤ (↑C : Set α).encard

lemma SetConnectivityGe_zero (G : Graph α β) (S T : Set α) : G.SetConnectivityGe S T 0 := by
  simp [SetConnectivityGe]

lemma SetConnectivityGe.SetConnected (h : G.SetConnectivityGe S T n) (hn : n ≠ 0) :
    G.SetConnected S T := by
  unfold SetConnectivityGe at h
  contrapose! h
  use ⟨∅, empty_subset _, by simpa [Graph.SetConnected] using h⟩
  change (∅ : Set α).encard < n
  rw [encard_empty]
  norm_cast
  exact pos_of_ne_zero hn

lemma SetConnectivityGe.exists_isPathFrom (h : G.SetConnectivityGe S T n) (hn : n ≠ 0) :
    ∃ P, G.IsPathFrom S T P := by
  classical
  obtain ⟨s, hs, t, ht, hst⟩ := h.SetConnected hn
  obtain ⟨P, hP, rfl, rfl⟩ := hst.exists_isPath
  exact ⟨P.extractPathFrom S T, hP.extractPathFrom_isPathFrom hs ht⟩

lemma SetConnectivityGe.vertexDelete (h : G.SetConnectivityGe S T n) (X : Set α) :
    (G - X).SetConnectivityGe S T (n - (X ∩ V(G)).encard).toNat := by
  intro C
  have := by simpa using h C.of_vertexDelete
  exact (ENat.coe_toNat_le_self _).trans <| tsub_le_iff_left.mpr <| this.trans <| encard_union_le ..

lemma SetConnectivityGe.vertexDelete' (h : G.SetConnectivityGe S T n) (X : Set α) :
    (G - X).SetConnectivityGe (S \ X) (T \ X) (n - (X ∩ V(G)).encard).toNat := by
  intro C
  have := by simpa using h ((C.of_vertexDelete').subset (by simp) (by simp))
  exact (ENat.coe_toNat_le_self _).trans <| tsub_le_iff_left.mpr <| this.trans <| encard_union_le ..

lemma SetConnectivityGe.downwards_closed (h : G.SetConnectivityGe S T n) (hle : m ≤ n) :
    G.SetConnectivityGe S T m :=
  fun C ↦ (by norm_cast : (m : ℕ∞) ≤ (n : ℕ∞)).trans (by simpa using h C)

lemma SetConnectivityGe.subset (h : G.SetConnectivityGe S T n) (hS : S ⊆ S') (hT : T ⊆ T') :
    G.SetConnectivityGe S' T' n :=
  fun C ↦ h (C.subset hS hT)


/-! ### Connectivity on a graph -/

/-- A partition of `G.V` into two parts with no edge between them. -/
structure Separation (G : Graph α β) where
  left : Set α
  right : Set α
  nonempty_left : left.Nonempty
  nonempty_right : right.Nonempty
  disjoint : Disjoint left right
  union_eq : left ∪ right = V(G)
  not_adj : ∀ ⦃x y⦄, x ∈ left → y ∈ right → ¬ G.Adj x y

namespace Separation

variable {S : G.Separation}

lemma left_subset (S : G.Separation) : S.left ⊆ V(G) := by
  simp [← S.union_eq]

lemma right_subset (S : G.Separation) : S.right ⊆ V(G) := by
  simp [← S.union_eq]

@[simps]
def symm (S : G.Separation) : G.Separation where
  left := S.right
  right := S.left
  nonempty_left := S.nonempty_right
  nonempty_right := S.nonempty_left
  disjoint := S.disjoint.symm
  union_eq := by rw [← S.union_eq, union_comm]
  not_adj x y hx hy := by simpa [adj_comm] using S.not_adj hy hx

lemma not_left_mem_iff (S : G.Separation) (hxV : x ∈ V(G)) : x ∉ S.left ↔ x ∈ S.right := by
  rw [← S.union_eq, mem_union] at hxV
  have := S.disjoint.notMem_of_mem_left (a := x)
  tauto

lemma not_right_mem_iff (S : G.Separation) (hxV : x ∈ V(G)) : x ∉ S.right ↔ x ∈ S.left := by
  simpa using S.symm.not_left_mem_iff hxV

lemma left_mem_of_adj (hx : x ∈ S.left) (hxy : G.Adj x y) : y ∈ S.left := by
  rw [← S.not_right_mem_iff hxy.right_mem]
  exact fun hy ↦ S.not_adj hx hy hxy

lemma right_mem_of_adj (hx : x ∈ S.right) (hxy : G.Adj x y) : y ∈ S.right :=
  S.symm.left_mem_of_adj hx (y := y) hxy

lemma mem_or_mem (S : G.Separation) (hxV : x ∈ V(G)) : x ∈ S.left ∨ x ∈ S.right := by
  rwa [← mem_union, S.union_eq]

lemma edge_induce_disjoint (S : G.Separation) : Disjoint E(G[S.left]) E(G[S.right]) := by
  refine disjoint_left.2 fun e he he' ↦ ?_
  simp only [induce_edgeSet, mem_setOf_eq] at he he'
  obtain ⟨x, y, hexy, hx, hy⟩ := he
  obtain ⟨x', y', hexy', hx', hy'⟩ := he'
  obtain rfl | rfl := hexy.left_eq_or_eq hexy'
  · exact S.disjoint.notMem_of_mem_left hx hx'
  exact S.disjoint.notMem_of_mem_left hx hy'

lemma eq_union (S : G.Separation) : G = G[S.left] ∪ G[S.right] := by
  refine Graph.ext (by simp [← S.union_eq]) fun e x y ↦ ?_
  rw [Compatible.union_isLink_iff (by simp)]
  simp +contextual only [induce_isLink_iff, iff_def, true_and]
  exact ⟨fun he ↦ (S.mem_or_mem he.left_mem).imp (fun hx ↦ ⟨hx, S.left_mem_of_adj hx he.adj⟩)
    (fun hx ↦ ⟨hx, S.right_mem_of_adj hx he.adj⟩), by tauto⟩

lemma edge_mem_or_mem (S : G.Separation) (he : e ∈ E(G)) :
    e ∈ E(G[S.left]) ∨ e ∈ E(G[S.right]) := by
  have := S.eq_union
  apply_fun edgeSet at this
  rwa [this, union_edgeSet] at he

lemma vertexSet_nontrivial (S : G.Separation) : V(G).Nontrivial :=
  ⟨_, S.left_subset S.nonempty_left.some_mem, _, S.right_subset S.nonempty_right.some_mem,
    S.disjoint.ne_of_mem S.nonempty_left.some_mem S.nonempty_right.some_mem⟩

lemma induce_left_isClosedSubgraph (S : G.Separation) : G[S.left].IsClosedSubgraph G where
  le := by simp [S.left_subset]
  closed e x hex hx := by
    contrapose! hx
    have := hex.of_le_of_mem (by simp [S.right_subset])
      (S.edge_mem_or_mem hex.edge_mem |>.resolve_left hx) |>.vertex_mem
    simp only [induce_vertexSet] at this ⊢
    rwa [S.not_left_mem_iff hex.vertex_mem]

def of_not_vertexConnected (h : ¬ G.VertexConnected x y) (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    G.Separation where
  left := {y ∈ V(G) | G.VertexConnected x y}
  right := {y ∈ V(G) | ¬ G.VertexConnected x y}
  nonempty_left := ⟨x, by simpa⟩
  nonempty_right := ⟨y, by simpa [h]⟩
  disjoint := by
    rw [disjoint_iff_forall_notMem]
    rintro z ⟨hz, hxz⟩ ⟨_, hyz⟩
    exact hyz hxz
  union_eq := by
    ext z
    by_cases hz : G.VertexConnected x z <;> simp [hz]
  not_adj a b ha hb hab := by
    simp only [mem_setOf_eq] at ha hb
    exact hb.2 <| ha.2.trans hab.vertexConnected

end Separation

/-- A graph is preconnected if the graph has no separation. -/
def Preconnected (G : Graph α β) : Prop := IsEmpty G.Separation

lemma preconnected_of_vertexSet_subsingleton (hV : V(G).Subsingleton) : G.Preconnected := by
  contrapose! hV
  obtain ⟨S⟩ := by simpa only [Preconnected, not_isEmpty_iff] using hV
  exact S.vertexSet_nontrivial

lemma Separation.not_vertexConnected (S : G.Separation) (hx : x ∈ S.left) (hy : y ∈ S.right) :
    ¬ G.VertexConnected x y := by
  intro h
  obtain ⟨W, hW, rfl, rfl⟩ := h
  rw [← S.not_left_mem_iff (S.right_subset hy)] at hy
  obtain ⟨e, x, y, hinc, hx, hy⟩ := exists_dInc_prop_not_prop hx hy
  exact hy <| S.left_mem_of_adj hx (hW.isLink_of_dInc hinc).adj

lemma exists_separation_of_not_vertexConnected (hxV : x ∈ V(G)) (hyV : y ∈ V(G))
    (hxy : ¬ G.VertexConnected x y) : ∃ S : G.Separation, x ∈ S.left ∧ y ∈ S.right :=
  ⟨⟨{w ∈ V(G) | G.VertexConnected x w}, {w ∈ V(G) | ¬ G.VertexConnected x w}, ⟨x, by simpa⟩,
    ⟨y, by aesop⟩, by simp +contextual [disjoint_left],
    by simp [Set.ext_iff, ← and_or_left, or_not],
    fun x' y' ⟨_, hx'⟩ ⟨_, hy'⟩ hxy' ↦  hy' <| hx'.trans hxy'.vertexConnected⟩, by simp_all⟩

lemma preconnected_iff_forall_vertexConnected :
    G.Preconnected ↔ ∀ x y, x ∈ V(G) → y ∈ V(G) → G.VertexConnected x y := by
  rw [← not_iff_not]
  simp only [Preconnected, not_isEmpty_iff, not_forall]
  refine ⟨fun ⟨S⟩ => ?_, fun ⟨x, y, hx, hy, h⟩ => ?_⟩
  · use S.nonempty_left.some, S.nonempty_right.some, S.left_subset S.nonempty_left.some_mem,
      S.right_subset S.nonempty_right.some_mem, S.not_vertexConnected S.nonempty_left.some_mem
      S.nonempty_right.some_mem
  obtain ⟨S, hxL, hyR⟩ := exists_separation_of_not_vertexConnected hx hy h
  exact ⟨S⟩

/- ### Connectedness -/

/-- A graph is connected if it is a minimal closed subgraph of itself -/
protected def Connected (G : Graph α β) : Prop := G.IsCompOf G

lemma Connected.nonempty (hG : G.Connected) : V(G).Nonempty := by
  rw [Graph.Connected, IsCompOf] at hG
  exact hG.prop.2

lemma connected_iff_forall_closed (hG : V(G).Nonempty) :
    G.Connected ↔ ∀ ⦃H⦄, H ≤c G → V(H).Nonempty → H = G := by
  refine ⟨fun h H hHG hHne ↦ ?_, fun h ↦ ⟨by simpa [-vertexSet_nonempty_iff],
    fun H ⟨hle, hH⟩ _ ↦ (h hle hH).symm.le⟩⟩
  rw [Graph.Connected, IsCompOf] at h
  exact h.eq_of_le ⟨hHG, hHne⟩ hHG.le

lemma connected_iff_forall_closed_ge (hG : V(G).Nonempty) :
    G.Connected ↔ ∀ ⦃H⦄, H ≤c G → V(H).Nonempty → G ≤ H := by
  rw [connected_iff_forall_closed hG]
  exact ⟨fun h H hle hne ↦ (h hle hne).symm.le, fun h H hle hne ↦ (h hle hne).antisymm' hle.le⟩

lemma Connected.eq_of_isClosedSubgraph (hG : G.Connected) (hH : H ≤c G) (hne : V(H).Nonempty) :
    H = G := by
  rw [connected_iff_forall_closed (hne.mono (vertexSet_mono hH.le))] at hG
  exact hG hH hne

lemma Connected.isSimpleOrder (hG : G.Connected) (hnonempty : G ≠ ⊥) :
    IsSimpleOrder G.ClosedSubgraph where
  exists_pair_ne := by
    use ⊥, ⊤
    apply_fun Subtype.val
    exact hnonempty.symm
  eq_bot_or_eq_top H := by
    refine (eq_empty_or_nonempty V(H.val)).imp (by simp) ?_
    convert hG.eq_of_isClosedSubgraph H.prop
    exact Iff.symm (StrictMono.apply_eq_top_iff fun ⦃a b⦄ a ↦ a)

lemma IsClosedSubgraph.disjoint_or_subset_of_isCompOf (h : H ≤c G) (hK : K.IsCompOf G) :
    K.IsCompOf H ∨ K.StronglyDisjoint H := by
  rw [or_iff_not_imp_right, StronglyDisjoint_iff_of_le_le hK.le h.le,
    not_disjoint_iff_nonempty_inter, inter_comm]
  intro hne
  have h_eq := hK.eq_of_le ⟨h.inter hK.isClosedSubgraph, by simpa⟩ Graph.inter_le_right
  rw [← h_eq] at hK ⊢
  refine ⟨⟨hK.isClosedSubgraph.of_le_of_le Graph.inter_le_left h.le, by simpa⟩, ?_⟩
  intro P ⟨hPH, hP⟩ hle
  rw [hK.eq_of_le ⟨?_, hP⟩ hle]
  exact (hPH.of_le_of_le hle Graph.inter_le_left).trans hK.isClosedSubgraph

lemma IsCompOf.of_le_le (h : K.IsCompOf G) (hKH : K ≤ H) (hHG : H ≤ G) : K.IsCompOf H := by
  refine ⟨⟨h.isClosedSubgraph.of_le_of_le hKH hHG, h.nonempty⟩, fun K' ⟨hK'H, hK'ne⟩ hK'K ↦ ?_⟩
  exact h.le_of_le ⟨(hK'H.of_le_of_le hK'K hKH).trans h.isClosedSubgraph, hK'ne⟩ hK'K

/-- A graph has preconnectivityGe n, if for every pair of vertices `s` and `t`, there is no
    `n`-vertex cut between them. -/
def PreconnectivityGe (G : Graph α β) (n : ℕ) : Prop :=
  ∀ {s t : α} (C : G.VertexCut s t), s ∈ V(G) → t ∈ V(G) → n ≤ (↑C : Set α).encard

/-- A graph has connectivityGe n, if for every pair of vertex sets `S` and `T`, there is no
    `n`-vertex cut between them. -/
def ConnectivityGe (G : Graph α β) (n : ℕ) : Prop :=
  ∀ {S T : Set α} (C : G.SetCut S T), S ⊆ V(G) → T ⊆ V(G) → n ≤ (↑C : Set α).encard

-- lemma preconnectivityGe_one_iff : G.PreconnectivityGe 1 ↔ G.Preconnected := by
--   rw [preconnected_iff_forall_vertexConnected]
--   refine ⟨fun h => ?_, fun h => ?_⟩
--   · unfold PreconnectivityGe at h
--     rintro x y hx hy
--     have := h x y
--     sorry
--   intro s t C
--   have := C.
--   have := h s t

-- lemma PreconnectivityGe.preconnected (h : G.PreconnectivityGe n) (hn : n ≠ 0) :
-- G.Preconnected := by

--   rintro x y hx hy
--   unfold PreconnectivityGe at h
--   contrapose! h
--   obtain ⟨S⟩ := h


-- lemma PreconnectivityGe.anti_right (hle : n ≤ m) (h : G.PreconnectivityGe m) :
--     G.PreconnectivityGe n := by
--   intro X hX
--   have : X.encard < (m : ℕ∞) := lt_of_lt_of_le hX <| by exact_mod_cast hle
--   exact h X this

-- @[simp]
-- lemma preconnectivityGe_zero : G.PreconnectivityGe 1 ↔ G.Preconnected := by
--   refine ⟨fun h => by simpa using (h ∅ (by simp)), fun h X hX => ?_⟩
--   rw [cast_one, ENat.lt_one_iff_eq_zero, encard_eq_zero] at hX
--   simpa [hX]

-- lemma vertexDelete_isPreconnected_iff (h : G.PreconnectivityGe (V(G) ∩ X).ncard.succ)
--     (hX : (V(G) ∩ X).Finite) : (G - X).Preconnected := by
--   rw [← vertexDelete_vertexSet_inter]
--   apply h
--   simpa [ENat.lt_add_one_iff, encard_le_coe_iff_finite_ncard_le]

-- lemma preConnectivityGe_one_iff : G.PreConnectivityGe 1 ↔ G.Preconnected := by
--   refine ⟨fun h => ?_, fun h s t C => ?_⟩
--   · unfold Preconnected
--     unfold PreConnectivityGe at h
--     contrapose! h
--     obtain ⟨S⟩ := h
--     use S.nonempty_left.some, S.nonempty_right.some
--     use vertexCut_empty ?_
--     rw [vertexCut_empty_coe]
--     simp


--   rw [cast_one, ENat.lt_one_iff_eq_zero, encard_eq_zero] at hC
--   simpa [hC]

end Graph
