import Matroid.Graph.Connected.Basic
import Matroid.Graph.Minor.Defs

open Set Function Nat WList

variable {α α' β : Type*} {G H : Graph α β} {u v x x₁ x₂ y y₁ y₂ z : α} {e e' f g : β}
  {U V S T : Set α} {F F' R R': Set β} {C W P Q : WList α β}

namespace Graph

lemma ConnBetween.map (f : α → α') (h : G.ConnBetween x y) :
    (f ''ᴳ G).ConnBetween (f x) (f y) := by
  obtain ⟨W, hW, rfl, rfl⟩ := h
  exact ⟨W.map f, hW.map f, by simp, by simp⟩

@[simp]
lemma map_vertexDelete_preimage (f : α → α') (C : Set α') :
    f ''ᴳ (G - (f ⁻¹' C)) = (f ''ᴳ G) - C := by
  ext a b c <;> constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨⟨u, hu.1, rfl⟩, by simpa using hu.2⟩
  · rintro ⟨⟨u, hu, rfl⟩, hC⟩
    exact ⟨u, ⟨hu, by simpa using hC⟩, rfl⟩
  · rintro ⟨a, b, h, rfl, rfl⟩
    obtain ⟨hG, ha, hb⟩ := (G.vertexDelete_isLink_iff _).1 h
    exact (vertexDelete_isLink_iff _ C).2 ⟨hG.Map f, by simpa using ha, by simpa using hb⟩
  · intro h
    obtain ⟨⟨a, b, hG, rfl, rfl⟩, hx, hy⟩ := (vertexDelete_isLink_iff _ C).mp h
    exact ⟨a, b, (vertexDelete_isLink_iff (G := G) (X := f ⁻¹' C)).2
      ⟨hG, by simpa using hx, by simpa using hy⟩, rfl, rfl⟩

lemma Preconnected.map (f : α → α') (h : G.Preconnected) : (f ''ᴳ G).Preconnected := by
  intro x' y' hx' hy'
  obtain ⟨x, hx, rfl⟩ := by simpa [Map_vertexSet] using hx'
  obtain ⟨y, hy, rfl⟩ := by simpa [Map_vertexSet] using hy'
  exact (h _ _ hx hy).map f

@[simp]
lemma Connected.map (f : α → α') (h : G.Connected) : (f ''ᴳ G).Connected := by
  obtain ⟨⟨v, hv⟩, hpre⟩ := connected_iff.mp h
  exact connected_iff.mpr ⟨⟨f v, by simpa [Map_vertexSet] using Set.mem_image_of_mem f hv⟩,
      hpre.map f⟩

@[simps]
def Cut.of_map {f : α → α'} (C : (f ''ᴳ G).Cut) : G.Cut where
  carrier := V(G) ∩ f ⁻¹' C
  carrier_subset := fun v hv => hv.1
  not_connected' := fun h => C.not_connected <| by simpa [map_vertexDelete_preimage] using
      (by simpa [vertexDelete_vertexSet_inter] using h : (G - (f ⁻¹' C)).Connected).map f

-- private lemma noSepSet_of_adj [G.Finite] (hG : G.PreconnGe 3)
--     (h : ∀ (e : β) (x : α) (h : G.Inc e x), ¬(Inc.contract G h).PreconnGe 3) :
--     ∀ a b c, G.Adj a b → ¬ G.IsSepSet {a, b, c} := by
--   intro a b c hab hSep


-- -- need to add some condition for K4 case
-- theorem exists_contract_connGe_three [G.Finite] (hG : G.PreconnGe 3) :
--     ∃ (e : β) (x : α) (h : G.Inc e x), h.contract.PreconnGe 3 := by
--   by_contra! h
--   have H : ∀ a b c, G.Adj a b → ¬ G.IsSepSet {a, b, c} := by
--     intro a b c hab hSep



end Graph
