import Matroid.Graph.Basic

open Set Function

namespace Graph

variable {α α' α'' β β' β'' : Type*} {G : Graph α β} {H : Graph α' β'} {K : Graph α'' β''}
  {f : α → α'} {x y : α} {e : β}

structure Hom (G : Graph α β) (H : Graph α' β') where
  vertMap : α → α'
  vertMap_vertexSet : MapsTo vertMap V(G) V(H)
  edgeMap : β → β'
  map_isLink ⦃e : β⦄ ⦃x y : α⦄ : G.IsLink e x y → H.IsLink (edgeMap e) (vertMap x) (vertMap y)

lemma Hom.edgeMap_edgeSet (h : Hom G H) : MapsTo h.edgeMap E(G) E(H) := by
  intro e he
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet he
  exact h.map_isLink hxy |>.edge_mem

structure Emb (G : Graph α β) (H : Graph α' β') extends Hom G H where
  vertMap_injOn : InjOn vertMap V(G)
  edgeMap_injOn : InjOn edgeMap E(G)

structure Iso (G : Graph α β) (H : Graph α' β') where
  vertMap : α → α'
  invVertMap : α' → α
  vertMap_vertexSet : MapsTo vertMap V(G) V(H)
  invVertMap_vertexSet : MapsTo invVertMap V(H) V(G)
  vertex_left_inv : LeftInvOn vertMap invVertMap V(H)
  vertex_right_inv : RightInvOn vertMap invVertMap V(G)
  edgeMap : β → β'
  invEdgeMap : β' → β
  edgeMap_edgeSet : MapsTo edgeMap E(G) E(H)
  invEdgeMap_edgeSet : MapsTo invEdgeMap E(H) E(G)
  edge_left_inv : LeftInvOn edgeMap invEdgeMap E(H)
  edge_right_inv : RightInvOn edgeMap invEdgeMap E(G)
  map_isLink ⦃e : β⦄ ⦃x y : α⦄ : G.IsLink e x y → H.IsLink (edgeMap e) (vertMap x) (vertMap y)
  invMap_isLink ⦃e : β'⦄ ⦃x y : α'⦄ : H.IsLink e x y →
    G.IsLink (invEdgeMap e) (invVertMap x) (invVertMap y)

@[simps (attr := grind =)]
def Iso.id (G : Graph α β) : Iso G G where
  vertMap := _root_.id
  invVertMap := _root_.id
  vertMap_vertexSet := mapsTo_id V(G)
  invVertMap_vertexSet := mapsTo_id V(G)
  vertex_left_inv := leftInvOn_id V(G)
  vertex_right_inv := rightInvOn_id V(G)
  edgeMap := _root_.id
  invEdgeMap := _root_.id
  edgeMap_edgeSet := mapsTo_id E(G)
  invEdgeMap_edgeSet := mapsTo_id E(G)
  edge_left_inv := leftInvOn_id E(G)
  edge_right_inv := rightInvOn_id E(G)
  map_isLink := by simp
  invMap_isLink := by simp

@[simps (attr := grind =)]
def Iso.Emb (e : Iso G H) : Emb G H where
  vertMap := e.vertMap
  vertMap_vertexSet := e.vertMap_vertexSet
  vertMap_injOn := e.vertex_right_inv.injOn
  edgeMap := e.edgeMap
  edgeMap_injOn := e.edge_right_inv.injOn
  map_isLink := e.map_isLink

@[simps! (attr := grind =)]
def Iso.Hom (e : Iso G H) : Hom G H := e.Emb.toHom

@[simps (attr := grind =)]
def Hom.comp (f : Hom G H) (g : Hom H K) : Hom G K where
  vertMap := g.vertMap ∘ f.vertMap
  vertMap_vertexSet _ hv := g.vertMap_vertexSet (f.vertMap_vertexSet hv)
  edgeMap := g.edgeMap ∘ f.edgeMap
  map_isLink _ _ _ h := g.map_isLink (f.map_isLink h)

@[simps (attr := grind =)]
def Emb.comp (f : Emb G H) (g : Emb H K) : Emb G K where
  vertMap := g.vertMap ∘ f.vertMap
  vertMap_vertexSet _ hv := g.vertMap_vertexSet (f.vertMap_vertexSet hv)
  vertMap_injOn := g.vertMap_injOn.comp f.vertMap_injOn f.vertMap_vertexSet
  edgeMap := g.edgeMap ∘ f.edgeMap
  edgeMap_injOn := g.edgeMap_injOn.comp f.edgeMap_injOn f.edgeMap_edgeSet
  map_isLink _ _ _ h := g.map_isLink (f.map_isLink h)

@[simps (attr := grind =)]
def Iso.comp (f : Iso G H) (g : Iso H K) : Iso G K where
  vertMap := g.vertMap ∘ f.vertMap
  invVertMap := f.invVertMap ∘ g.invVertMap
  vertMap_vertexSet _ hv := g.vertMap_vertexSet (f.vertMap_vertexSet hv)
  invVertMap_vertexSet _ hv := f.invVertMap_vertexSet (g.invVertMap_vertexSet hv)
  vertex_left_inv := g.vertex_left_inv.comp f.vertex_left_inv g.invVertMap_vertexSet
  vertex_right_inv := g.vertex_right_inv.comp f.vertex_right_inv f.vertMap_vertexSet
  edgeMap := g.edgeMap ∘ f.edgeMap
  invEdgeMap := f.invEdgeMap ∘ g.invEdgeMap
  edgeMap_edgeSet _ he := g.edgeMap_edgeSet (f.edgeMap_edgeSet he)
  invEdgeMap_edgeSet _ he := f.invEdgeMap_edgeSet (g.invEdgeMap_edgeSet he)
  edge_left_inv := g.edge_left_inv.comp f.edge_left_inv g.invEdgeMap_edgeSet
  edge_right_inv := g.edge_right_inv.comp f.edge_right_inv f.edgeMap_edgeSet
  map_isLink _ _ _ h := g.map_isLink (f.map_isLink h)
  invMap_isLink _ _ _ h := f.invMap_isLink (g.invMap_isLink h)

@[simps (attr := grind =)]
def Hom.anti_left (G' : Graph α β) (hG' : G' ≤ G) (F : Hom G H) : Hom G' H where
  vertMap := F.vertMap
  vertMap_vertexSet _ hv := F.vertMap_vertexSet (hG'.vertexSet_mono hv)
  edgeMap := F.edgeMap
  map_isLink _ _ _ h := F.map_isLink (hG'.isLink_mono h)

@[simps (attr := grind =)]
def Emb.anti_left (G' : Graph α β) (hG' : G' ≤ G) (F : Emb G H) : Emb G' H where
  vertMap := F.vertMap
  vertMap_vertexSet _ hv := F.vertMap_vertexSet (hG'.vertexSet_mono hv)
  vertMap_injOn := F.vertMap_injOn.mono hG'.vertexSet_mono
  edgeMap := F.edgeMap
  edgeMap_injOn := F.edgeMap_injOn.mono hG'.edgeSet_mono
  map_isLink _ _ _ h := F.map_isLink (hG'.isLink_mono h)

@[simps (attr := grind =)]
def Hom.mono_right (H' : Graph α' β') (hH' : H ≤ H') (F : Hom G H) : Hom G H' where
  vertMap := F.vertMap
  vertMap_vertexSet _ hv := hH'.vertexSet_mono <| F.vertMap_vertexSet hv
  edgeMap := F.edgeMap
  map_isLink _ _ _ h := hH'.isLink_mono <| F.map_isLink h

@[simps (attr := grind =)]
def Emb.mono_right (H' : Graph α' β') (hH' : H ≤ H') (F : Emb G H) : Emb G H' where
  vertMap := F.vertMap
  vertMap_vertexSet _ hv := hH'.vertexSet_mono <| F.vertMap_vertexSet hv
  vertMap_injOn := F.vertMap_injOn
  edgeMap := F.edgeMap
  edgeMap_injOn := F.edgeMap_injOn
  map_isLink _ _ _ h := hH'.isLink_mono <| F.map_isLink h

end Graph
