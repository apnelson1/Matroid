module

public import Matroid.Graph.Constructions.Cycle
public import Matroid.Graph.Map

open List Fin

@[expose] public section

variable {α β : Type*}

@[simp]
lemma PFun.res_get {α β : Type*} {f : α → β} {s : Set α} {x : α} (hxs : x ∈ s) :
    (PFun.res f s x).get hxs = f x :=
  rfl

@[simp]
lemma PFun.res_ran {α β : Type*} {f : α → β} {s : Set α} :
    (PFun.res f s).ran = f '' s := by
  ext
  simp [PFun.ran, PFun.mem_res]

@[simp]
lemma PFun.res_dom {α β : Type*} {f : α → β} {s : Set α} :
    (PFun.res f s).Dom = s := rfl

variable {α β : Type*} {X Y C K T : Set α} {e f g x y : α} {b c d : Bool}
     {n i j : ℕ} {F : List α} {J : Bool → ZMod n → α} {G : Graph α β}

-- open Set Option

namespace Graph

/-- The graph with vertices `V(G) ∪ {none}` and edges `E(G) ∪ V(G)`,
where the new edges go to the apex vertex. -/
def fullApex (G : Graph α β) : Graph (Option α) (β ⊕ α) := by
  let G' := (G.map Option.some).edgeMap (Sum.inl : β → β ⊕ α) (by grind)
  let H := StarGraph (α := Option α) (β := β ⊕ α) Option.none
    (PFun.res (Sum.elim (fun _ ↦ Option.none) Option.some) (.inr '' V(G)))
  exact G' ∪ H

@[simp]
lemma fullApex_vertexSet (G : Graph α β) :
    V(G.fullApex) = insert Option.none (Option.some '' V(G)) := by
  simp [fullApex, Set.image_image]

@[simp]
lemma fullApex_edgeSet (G : Graph α β) :
    E(G.fullApex) = .inl '' E(G) ∪ .inr '' V(G) := by
  simp [fullApex]

@[simp]
lemma fullApex_isLink_inl_iff {e : β} {x y : α} :
    G.fullApex.IsLink (.inl e) (some x) (some y) ↔ G.IsLink e x y := by
  simp [fullApex, union_isLink_iff]

@[simp]
lemma fullApex_isLink_inr_left_iff {e : α} {x : α} :
    G.fullApex.IsLink (.inr e) (some x) none ↔ x ∈ V(G) ∧ e = x := by
  simp +contextual [fullApex, union_isLink_iff]

@[simp]
lemma fullApex_isLink_inr_right_iff {e : α} {x : α} :
    G.fullApex.IsLink (.inr e) none (some x) ↔ x ∈ V(G) ∧ e = x := by
  rw [isLink_comm, fullApex_isLink_inr_left_iff]

@[simp]
lemma fullApex_not_isLink_inl_none_left {e : β} {x : Option α} :
    ¬ G.fullApex.IsLink (.inl e) none x := by
  simp [fullApex, union_isLink_iff]

@[simp]
lemma fullApex_not_isLink_inl_none_right {e : β} {x : Option α} :
    ¬ G.fullApex.IsLink (.inl e) x none := by
  simp [fullApex, union_isLink_iff]

@[simp]
lemma fullApex_not_isLink_inr_some_some {e : α} {x y : α} :
    ¬ G.fullApex.IsLink (.inr e) (some x) (some y) := by
  simp [fullApex, union_isLink_iff]

@[simp]
lemma fullApex_adj_some_some_iff {x y : α} :
    G.fullApex.Adj (some x) (some y) ↔ G.Adj x y := by
  simp [Adj]

@[simp]
lemma fullApex_adj_some_none {x : α} :
    G.fullApex.Adj (some x) none ↔ x ∈ V(G) := by
  simp [Adj]

@[simp]
lemma fullApex_adj_none_some {x : α} :
    G.fullApex.Adj none (some x) ↔ x ∈ V(G) := by
  simp [Adj]

@[simp]
lemma fullApex_isLoopAt_inl {e : β} {x : α} :
    G.fullApex.IsLoopAt (.inl e) (some x) ↔ G.IsLoopAt e x := by
  simp [← isLink_self_iff]

@[simp]
lemma fullApex_not_isLoopAt_inr (G : Graph α β) {y : Option α} :
    ¬ G.fullApex.IsLoopAt (.inr e) y := by
  cases y with simp [← isLink_self_iff, fullApex, union_isLink_iff]

@[simp]
lemma fullApex_not_isLoopAt_none (G : Graph α β) {e : β ⊕ α} : ¬ G.fullApex.IsLoopAt e none := by
  obtain b | a := e
  · rw [← isLink_self_iff]
    exact fullApex_not_isLink_inl_none_right
  simp

@[simp]
lemma fullApex_not_adj_none (G : Graph α β) : ¬ G.fullApex.Adj none none := by
  simp [Adj]

lemma Loopless.fullApex_loopless (hG : G.Loopless) : G.fullApex.Loopless := by
  rw [loopless_iff_forall_ne_of_adj]
  simp +contextual [Option.forall, Adj.ne (G := G)]

lemma Simple.fullApex_simple (hG : G.Simple) : G.fullApex.Simple := by
  rw [simple_iff, and_iff_right hG.fullApex_loopless]
  rintro (e | e) (f | f)
  · simpa [Option.forall] using fun _ _ h h' ↦ hG.eq_of_isLink h h'
  · simp [Option.forall]
  · simp [Option.forall]
  simp +contextual [Option.forall]

lemma fullApex_connected (G : Graph α β) : G.fullApex.Connected := by
  refine connected_of_vertex (u := none) (by simp) ?_
  rintro (rfl | y) hy
  · simp
  exact Adj.connBetween <| by simpa using hy

/-- The canonical `n`-wheel, with vertices `Option (Fin n)` and edges `Fin n × Bool`.
The `false` edges are the rim, and the `true` edges are the spokes. -/
def wheel (n : ℕ) : Graph (Option (Fin n)) (Fin n × Bool) :=
  ((cycle n).fullApex).edgeMap (Sum.elim (fun i ↦ ⟨i, false⟩) (fun i ↦ ⟨i, true⟩)) (by grind)

lemma wheel_isLink_none_left_iff {e : Fin n × Bool} {x : Fin n} :
    (wheel n).IsLink e none (some x) ↔ e.1 = x ∧ e.2 = true := by
  obtain ⟨i, b⟩ := e
  simp [wheel, eq_comm]

lemma wheel_isLink_none_right_iff {e : Fin n × Bool} {x : Fin n} :
    (wheel n).IsLink e (some x) none ↔ e.1 = x ∧ e.2 = true := by
  rw [isLink_comm, wheel_isLink_none_left_iff]
