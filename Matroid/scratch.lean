import Mathlib.Combinatorics.Graph.Basic

variable {α β : Type*}

namespace Graph

/-- Define endpoints in terms of the data in `Graph`.
Probably needs some decidability to define correctly.  -/
def endpoints [DecidableEq α] (G : Graph α β) (e : β) : Sym2 α := sorry

/-- Provided `Graph.endpoints` has been defined correctly, the following lemma will be provable. -/
@[simp]
lemma mem_endpoints_iff [DecidableEq α] {G : Graph α β} {x : α} {e : β} :
  x ∈ G.endpoints e ↔ G.Inc e x := sorry

/-- An alternative constructor for `Graph` given an `endpoints` function. -/
def mkEndpoints (vertexSet : Set α) (edgeSet : Set β) (endpoints : β → Sym2 α)
    (incidence : ∀ e ∈ edgeSet, ∀ v ∈ endpoints e, v ∈ vertexSet) : Graph α β where
  vertexSet := vertexSet
  IsLink e u v := (endpoints e = Sym2.mk u v)
  isLink_symm := sorry
  eq_or_eq_of_isLink_of_isLink := sorry
  edge_mem_iff_exists_isLink := sorry
  left_mem_of_isLink := sorry

/-- `mkEndpoints` builds a graph with the right `endpoints`.-/
@[simp]
lemma mkEndpoints_endpoints [DecidableEq α] (vertexSet : Set α) (edgeSet : Set β)
    (endpoints : β → Sym2 α) (incidence) :
    (mkEndpoints vertexSet edgeSet endpoints incidence).endpoints = endpoints := sorry



end Graph
