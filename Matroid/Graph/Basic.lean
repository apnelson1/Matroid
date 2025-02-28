import Mathlib.Data.Set.Insert

variable {α β : Type*}

open Set Function

structure Graph (α β : Type*) where
  V : Set α
  E : Set β
  Inc : α → β → Prop
  vx_mem_of_inc : ∀ ⦃v e⦄, Inc v e → v ∈ V
  edge_mem_of_inc : ∀ ⦃v e⦄, Inc v e → e ∈ E
  exists_vertex_inc : ∀ ⦃e⦄, e ∈ E → ∃ v, Inc v e
  not_hypergraph : ∀ ⦃x y z e⦄, Inc x e → Inc y e → Inc z e → x = y ∨ y = z ∨ x = z

variable {G : Graph α β} {u v w x y : α} {e f g : β}

namespace Graph

def IsLoop (G : Graph α β) (e : β) := ∃! x, G.Inc x e

def Adj (G : Graph α β) (x y : α) : Prop :=
  ∃ e, (G.Inc x e ∧ G.Inc y e ∧ x ≠ y) ∨ (G.Inc x e ∧ G.IsLoop e ∧ x = y)

lemma Inc.vx_mem (h : G.Inc x e) : x ∈ G.V :=
  G.vx_mem_of_inc h

lemma Inc.edge_mem (h : G.Inc x e) : e ∈ G.E :=
  G.edge_mem_of_inc h

lemma adj_comm : G.Adj x y ↔ G.Adj y x := by
  simp [Adj, and_comm]

def edgeNhd (G : Graph α β) (v : α) : Set β := {e | G.Inc v e}

def vxNhd (G : Graph α β) (v : α) : Set α := {x | G.Adj v x}

def Connected (G : Graph α β) := Relation.TransGen (fun x y ↦ G.Adj x y ∨ x = y ∧ x ∈ G.V)

lemma Adj.connected (h : G.Adj x y) : G.Connected x y :=
  Relation.TransGen.single <| .inl h

lemma connected_self (hx : x ∈ G.V) : G.Connected x x :=
  Relation.TransGen.single <| .inr ⟨rfl, hx⟩

lemma Inc.connected_of_inc (hx : G.Inc x e) (hy : G.Inc y e) : G.Connected x y := by
  _

def restrict (G : Graph α β) (R : Set β) : Graph α β where
  V := G.V
  E := R ∩ G.E
  Inc v e := e ∈ R ∧ G.Inc v e
  vx_mem_of_inc _ _ h := G.vx_mem_of_inc h.2
  edge_mem_of_inc _ _ h := ⟨h.1, G.edge_mem_of_inc h.2⟩
  exists_vertex_inc e he := by
    obtain ⟨v, hv⟩ := G.exists_vertex_inc he.2
    exact ⟨v, he.1, hv⟩
  not_hypergraph _ _ _ _ hex hey hez := G.not_hypergraph hex.2 hey.2 hez.2

def edgeDel (G : Graph α β) (F : Set β) : Graph α β := G.restrict (G.E \ F)

def vxMap {α' : Type*} (G : Graph α β) (φ : α → α') : Graph α' β where
  V := φ '' G.V
  E := G.E
  Inc v e := ∃ v₀, φ v₀ = v ∧ G.Inc v₀ e
  vx_mem_of_inc v e := by
    rintro ⟨v₀, rfl, hv₀⟩
    exact mem_image_of_mem _ hv₀.vx_mem
  edge_mem_of_inc v e := by
    rintro ⟨v₀, rfl, hv₀⟩
    exact hv₀.edge_mem
  exists_vertex_inc e he := by
    obtain ⟨v, hv⟩ := G.exists_vertex_inc he
    exact ⟨φ v, v, rfl, hv⟩
  not_hypergraph x y z e := by
    rintro ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩ ⟨z, rfl, hz⟩
    obtain h | h | h := G.not_hypergraph hx hy hz <;>
    simp [h]

structure ContractFun (G : Graph α β) where
  toFun : α → α
  contractSet : Set β
  idem : ∀ x, toFun (toFun x) = toFun x
  map_not_mem : ∀ x, x ∉ G.V → toFun x = x
  map_connected : ∀ x ∈ G.V, (G.restrict contractSet).Connected x (toFun x)
  map_edge : ∀ ⦃x y e⦄, e ∈ contractSet → G.Inc x e → G.Inc y e → toFun x = toFun y

instance {G : Graph α β} : CoeFun G.ContractFun fun (_ : G.ContractFun) ↦ α → α where
  coe v := v.toFun


-- def ContractFun.comp (m₁ m₂ : G.ContractFun) : G.ContractFun where
--   toFun := m₁ ∘ m₂
--   contractSet := m₁.contractSet ∪ m₂.contractSet
--   idem x := by
--     simp
--   map_not_mem := _
--   map_edge := _

def contract (m : G.ContractFun) : Graph α β where
  V := m '' G.V
  E := G.E \ m.contractSet
  Inc v e := ∃ x, m x = v ∧ G.Inc x e ∧ e ∉ m.contractSet
  vx_mem_of_inc v e := by
    rintro ⟨x, rfl, h, -⟩
    exact ⟨x, h.vx_mem, rfl⟩
  edge_mem_of_inc v e := by
    rintro ⟨x, rfl, hx⟩
    exact ⟨hx.1.edge_mem, hx.2⟩
  exists_vertex_inc e he := by
    obtain ⟨v, hv⟩ := G.exists_vertex_inc he.1
    exact ⟨m v, v, rfl, hv, he.2⟩
  not_hypergraph _ _ _ e := by
    rintro ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩ ⟨z, rfl, hz⟩
    obtain h | h | h := G.not_hypergraph hx.1 hy.1 hz.1 <;>
    simp [h]

def Inc.contractFun (hxe : G.Inc x e) [DecidablePred (G.Inc · e)] : G.ContractFun where
  toFun y := if G.Inc y e then x else y
  contractSet := {e}
  idem y := by
    simp only
    split_ifs <;>
    simp
  map_not_mem y hy := by
    simp only
    split_ifs with hy'
    · exact False.elim <| hy hy'.vx_mem
    rfl
  map_connected y hy := by
    simp only
    split_ifs with hy'
    ·
  map_edge := _

def IsContraction (H G : Graph α β) := ∃ m, H = G.contract m

lemma isContraction_trans {G₁ G₂ G₃ : Graph α β} (hm : G₁.IsContraction G₂)
    (hm' : G₂.IsContraction G₃) : G₁.IsContraction G₃ := by
  sorry
