import Matroid.Graph.Minor.Defs

variable {α β : Type*} {G H : Graph α β} {x y z : α} {e f g : β} {X : Set α} {F : Set β}
{P C W : WList α β} {n : ℕ}

open Set WList Function

namespace Graph

/-- `G` is a topological minor of `H` if `V(G) ⊆ V(H)` and there is a map `F : E(G) → WList α β`,
where `F e` is a path in `H` between `u` and `v` with property that `V(F e) ∩ V(G) = {u, v}` where
`e` is an edge between `u` and `v` in `G`. -/
structure TopologicalMinor (G : Graph α β) (H : Graph α β) where
  vertex_subset : V(G) ⊆ V(H)
  map : E(G) → WList α β
  mem_map : ∀ e, e.val ∈ E(map e)
  map_isPath : ∀ e, H.IsTrail (map e) -- This allows `map e` to be a cycle in case `e` is a loop.
  map_isLink : ∀ e : E(G), G.IsLink e (map e).first (map e).last
  map_ends : ∀ e, V(map e) ∩ V(G) = {(map e).first, (map e).last}
  map_internally_disjoint : ∀ e f, e ≠ f →
    V(map e) ∩ V(map f) ⊆ {(map e).first, (map e).last}

lemma TopologicalMinor.vertexSet_mono (h : G.TopologicalMinor H) : V(G) ⊆ V(H) :=
  h.vertex_subset

lemma TopologicalMinor.edgeSet_mono (h : G.TopologicalMinor H) : E(G) ⊆ E(H) :=
  fun e he ↦ h.map_isPath ⟨e, he⟩ |>.edgeSet_subset (h.mem_map ⟨e, he⟩)

noncomputable def TopologicalMinor.of_le (hle : G ≤ H) : G.TopologicalMinor H where
  vertex_subset := hle.vertexSet_mono
  map e :=
    let h := exists_isLink_of_mem_edgeSet e.prop
    cons h.choose e (nil h.choose_spec.choose)
  mem_map e := by simp
  map_isPath e := by
    let h := exists_isLink_of_mem_edgeSet e.prop
    simp [h.choose_spec.choose_spec.of_le hle, (h.choose_spec.choose_spec.of_le hle).right_mem]
  map_isLink e := by
    let h := exists_isLink_of_mem_edgeSet e.prop
    simp only [first_cons, last_cons, nil_last]
    exact h.choose_spec.choose_spec
  map_ends e := by
    let h := exists_isLink_of_mem_edgeSet e.prop
    simp only [cons_vertexSet, nil_vertexSet, first_cons, last_cons, nil_last, inter_eq_left,
      pair_subset_iff]
    exact ⟨h.choose_spec.choose_spec.left_mem, h.choose_spec.choose_spec.right_mem⟩
  map_internally_disjoint e f hne := by simp

end Graph
