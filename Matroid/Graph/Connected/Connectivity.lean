import Matroid.Graph.Connected.Subgraph


open Set Function Nat WList

variable {α β : Type*} {G H : Graph α β} {u v x x₁ x₂ y y₁ y₂ z : α} {e e' f g : β}
  {U V S T : Set α} {F F' R R': Set β} {C W P Q : WList α β}

namespace Graph

/-! ### Vertex-Connectivity -/

structure VertexCut (G : Graph α β) where
  carrier : Set α
  subset_vertexSet : carrier ⊆ V(G)
  disconnects : ¬ (G - carrier).Connected

instance : SetLike G.VertexCut α where
  coe := (·.carrier)
  coe_injective' C1 C2 h := by rwa [VertexCut.mk.injEq]

/-! ### ST-Connectivity -/

variable {S S' T T' : Set α}

structure STVertexCut (G : Graph α β) (S T : Set α) where
  carrier : Set α
  carrier_subset : carrier ⊆ V(G)
  left_subset : S ⊆ V(G)
  right_subset : T ⊆ V(G)
  ST_disconnects : ∀ s ∈ S, ∀ t ∈ T, ¬ (G - carrier).VertexConnected s t

instance : SetLike (G.STVertexCut S T) α where
  coe := (·.carrier)
  coe_injective' C1 C2 h := by rwa [STVertexCut.mk.injEq]

def sTVertexCut_of_left (G : Graph α β) (hS : S ⊆ V(G)) (hT : T ⊆ V(G)) : G.STVertexCut S T where
  carrier := S
  carrier_subset := hS
  left_subset := hS
  right_subset := hT
  ST_disconnects s hs t ht h := by simpa [hs] using h.left_mem

def sTVertexCut_of_right (G : Graph α β) (hS : S ⊆ V(G)) (hT : T ⊆ V(G)) : G.STVertexCut S T where
  carrier := T
  carrier_subset := hT
  left_subset := hS
  right_subset := hT
  ST_disconnects s hs t ht h := by simpa [ht] using h.right_mem




/-! ### st-Connectivity -/

open Cardinal
variable {ι ι' : Type*} {s t : α} {n m : Cardinal} {X Y : Set α}

@[mk_iff]
structure stCut (G : Graph α β) (s t : α) (X : Set α) where
  left_not_mem : s ∉ X
  right_not_mem : t ∉ X
  not_vertexConnected : ¬ (G - X).VertexConnected s t

@[simp]
lemma stCut_empty_iff : G.stCut s t ∅ ↔ ¬ G.VertexConnected s t :=
  ⟨fun h => G.vertexDelete_empty ▸ h.not_vertexConnected, fun h => by simpa [stCut_iff]⟩

lemma Adj.not_stCut (h : G.Adj s t) : ¬ G.stCut s t X := by
  simp only [stCut_iff, not_and, not_not]
  rintro hs ht
  have hGst : G[({s, t} : Set α)] ≤ G - X := by
    simp [le_vertexDelete_iff, hs, ht, h.left_mem, h.right_mem, Set.pair_subset_iff]
  exact ((h.induce (by simp) (by simp)).vertexConnected).of_le hGst

lemma stCut.of_le (h : G.stCut s t X) (hle : H ≤ G) : H.stCut s t X :=
  ⟨h.left_not_mem, h.right_not_mem,
    fun h' => h.not_vertexConnected <| h'.of_le <| vertexDelete_mono_left hle⟩



def stVxPreConn (G : Graph α β) (s t : α) (n : Cardinal) : Prop :=
  ∀ X, G.stCut s t X → n ≤ #X.Elem

@[simp]
lemma stVxPreConn_zero (G : Graph α β) (s t : α) : G.stVxPreConn s t 0 := by
  simp [stVxPreConn]

lemma stVxPreConn.of_le (h : H.stVxPreConn s t n) (hle : H ≤ G) : G.stVxPreConn s t n :=
  fun X hX => h X (hX.of_le hle)

lemma stVxPreConn.anti_right (hle : n ≤ m) (h : G.stVxPreConn s t m): G.stVxPreConn s t n :=
  fun X hX => hle.trans <| h X hX

lemma stVxPreConn_iff_forall_lt :
    G.stVxPreConn s t n ↔ ∀ X, #X.Elem < n → ¬ G.stCut s t X := by
  unfold stVxPreConn
  simp_rw [← imp_not_comm, not_lt]

@[simp]
lemma stVxPreConn_one_iff : G.stVxPreConn s t 1 ↔ G.VertexConnected s t := by
  simp [stVxPreConn_iff_forall_lt, mk_eq_zero_iff]


def internallyDisjoint (s t : α) {ι : Type*} (f : ι → G.Subgraph) : Prop :=
  Pairwise (fun i j => V((f i).val) ∩ V((f j).val) = {s, t})

structure stEnsemble (G : Graph α β) (s t : α) (ι : Type*) where
  f : ι → G.Subgraph
  internallyDisjoint : G.internallyDisjoint s t f
  stConnected : ∀ i, (f i).val.VertexConnected s t

def stEnsemble.of_le (P : H.stEnsemble s t ι) (hle : H ≤ G) : G.stEnsemble s t ι :=
  ⟨(P.f ·|>.of_le hle), P.internallyDisjoint, P.stConnected⟩

def stEmsemble.precomp (P : G.stEnsemble s t ι) (f : ι' ↪ ι) : G.stEnsemble s t ι' :=
  ⟨P.f ∘ f, P.internallyDisjoint.comp_of_injective f.injective, (P.stConnected <| f ·)⟩





def STVxConnectivity (G : Graph α β) (s t : α) (n : Cardinal) :=
  IsGreatest {m | m ≤ #V(G) ∧ G.stVxPreConn s t m} n
