import Mathlib

structure Graph (α β : Type*) where
  V : Set α
  E : Set β
  incFun : β → α →₀ ℕ
  sum_eq : ∀ ⦃e⦄, e ∈ E → (incFun e).sum (fun _ x ↦ x) = 2
  vertex_support : ∀ ⦃e v⦄, incFun e v ≠ 0 → v ∈ V
  edge_support : ∀ ⦃e v⦄, incFun e v ≠ 0 → e ∈ E

variable {α β : Type*} {G : Graph α β} {x y : α} {e f : β}

def Graph.Inc (G : Graph α β) (e : β) (x : α) : Prop := G.incFun e x ≠ 0

def Graph.IsLoopAt (G : Graph α β) (e : β) (x : α) : Prop := G.incFun e x = 2

def Graph.IsNonloopAt (G : Graph α β) (e : β) (x : α) : Prop := G.incFun e x = 1

lemma Graph.Inc.vx_mem (h : G.Inc e x) : x ∈ G.V :=
  G.vertex_support h

lemma Graph.Inc.edge_mem (h : G.Inc e x) : e ∈ G.E :=
  G.edge_support h

@[simp]
lemma Graph.incFun_ne_zero : G.incFun e x ≠ 0 ↔ G.Inc e x := Iff.rfl

noncomputable def Graph.edgeDel (G : Graph α β) (D : Set β) : Graph α β where
  V := G.V
  E := G.E \ D
  incFun e :=
    haveI := Classical.dec (e ∈ D)
    if e ∈ D then 0 else G.incFun e
  sum_eq e he := by simp [he.2, G.sum_eq he.1]
  vertex_support e v h := G.vertex_support (e := e) <| by aesop
  edge_support e v h := ⟨G.edge_support (v := v) (by aesop), by aesop⟩

noncomputable def Graph.vxMap {α' : Type*} (G : Graph α β) (f : α → α') : Graph α' β where
  V := f '' G.V
  E := G.E
  incFun e := (G.incFun e).mapDomain f
  sum_eq e he := by rwa [Finsupp.sum_mapDomain_index (by simp) (by simp), G.sum_eq]
  vertex_support e v := by
    classical
    suffices ∀ (x : α), G.Inc e x → f x = v → ∃ x ∈ G.V, f x = v by
      simpa +contextual [Finsupp.mapDomain, Finsupp.sum, Finsupp.single_apply]
    rintro x h rfl
    exact ⟨x, h.vx_mem, rfl⟩
  edge_support e v := by
    classical
    suffices ∀ (x : α), G.Inc e x → f x = v → e ∈ G.E by
      simpa +contextual [Finsupp.mapDomain, Finsupp.sum, Finsupp.single_apply, Graph.Inc.edge_mem]
    exact fun x h _ ↦ h.edge_mem

@[simp]
lemma Graph.vxMap_inc_iff {α' : Type*} (G : Graph α β) (f : α → α') (x : α') (e : β) :
    (G.vxMap f).Inc e x ↔ ∃ v, f v = x ∧ G.Inc e v := by
  classical
  simp +contextual [← incFun_ne_zero, Graph.vxMap, Finsupp.mapDomain, Finsupp.sum,
    Finsupp.single_apply, and_comm]
