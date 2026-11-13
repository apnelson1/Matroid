module

public import Matroid.GraphTheory.Graph.Subdivision
public import Matroid.GraphTheory.Graph.Endpoint

/-! # Orienting the routes of a topological-minor model

The preferred source and target of an edge determine which direction to traverse its model route.
These statements concern graph walks and do not require topology or a realization.
-/

@[expose] public section

open Function Set WList

namespace Graph.TopologicalMinor

variable {α β γ δ : Type*} {G : Graph α β} {H : Graph γ δ} (M : H.TopologicalMinor G)

open Classical

lemma route_isWalk (e : E(H)) : G.IsWalk (M.route e) :=
  (M.route_isSimple e).elim (·.isWalk) (fun h ↦ h.isTrail.isWalk)

lemma route_ends_source_target (e : E(H)) :
    s(M.branchVertex (edgeSource e), M.branchVertex (edgeTarget e)) =
      s((M.route e).first, (M.route e).last) := by
  have hends : H.ends e = s(edgeSource e, edgeTarget e) :=
    (isLink_edgeSource_edgeTarget e).ends_eq
  rw [← M.route_ends e, hends, Sym2.map_mk]

/-- Reverse the model route when it runs from target to source. -/
noncomputable def orientedRoute (e : E(H)) : WList α β :=
  if (M.route e).first = M.branchVertex (edgeSource e) then M.route e
  else (M.route e).reverse

lemma orientedRoute_eq_or_reverse (e : E(H)) :
    M.orientedRoute e = M.route e ∨ M.orientedRoute e = (M.route e).reverse := by
  unfold orientedRoute
  split_ifs <;> simp

lemma orientedRoute_isWalk (e : E(H)) : G.IsWalk (M.orientedRoute e) := by
  unfold orientedRoute
  split_ifs
  · exact M.route_isWalk e
  · exact (M.route_isWalk e).reverse

lemma orientedRoute_nonempty (e : E(H)) : (M.orientedRoute e).Nonempty := by
  unfold orientedRoute
  split_ifs
  · exact M.route_nonempty e
  · exact (M.route_nonempty e).reverse

lemma orientedRoute_isSimple (e : E(H)) :
    G.IsPath (M.orientedRoute e) ∨ G.IsCyclicWalk (M.orientedRoute e) := by
  unfold orientedRoute
  split_ifs
  · exact M.route_isSimple e
  · exact (M.route_isSimple e).imp (·.reverse) (·.reverse)

lemma orientedRoute_first (e : E(H)) :
    (M.orientedRoute e).first = M.branchVertex (edgeSource e) := by
  unfold orientedRoute
  split_ifs with h
  · exact h
  · obtain ⟨h1, _⟩ | ⟨h1, _⟩ := Sym2.eq_iff.mp (M.route_ends_source_target e)
    · exact (h h1.symm).elim
    · simpa [reverse_first] using h1.symm

lemma orientedRoute_last (e : E(H)) :
    (M.orientedRoute e).last = M.branchVertex (edgeTarget e) := by
  unfold orientedRoute
  split_ifs with hf
  · obtain ⟨_, h2⟩ | ⟨h1, h2⟩ := Sym2.eq_iff.mp (M.route_ends_source_target e)
    · exact h2.symm
    · exact h1.symm.trans (hf.symm.trans h2.symm)
  · obtain ⟨h1, _⟩ | ⟨_, h2⟩ := Sym2.eq_iff.mp (M.route_ends_source_target e)
    · exact (hf h1.symm).elim
    · simpa [reverse_last] using h2.symm

end Graph.TopologicalMinor
