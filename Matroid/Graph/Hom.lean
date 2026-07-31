module

public import Mathlib.Data.PEquiv
public import Matroid.Graph.Basic

@[expose] public section

open Set Function

namespace Graph

variable {α α' α'' β β' β'' : Type*} {G : Graph α β} {H : Graph α' β'} {K : Graph α'' β''}
  {x y : α} {e : β}

lemma option_isSome_iff_exists_mem {o : Option α} : o.isSome ↔ ∃ x, x ∈ o := by
  simp [Option.isSome_iff_exists]

/-- A graph homomorphism, represented by partial maps whose domains are exactly the vertex and
edge sets of the source graph. -/
structure Hom (G : Graph α β) (H : Graph α' β') where
  /-- The partial map on vertices. -/
  vertMap : α → Option α'
  /-- The vertex map is defined exactly on the vertices of the source graph. -/
  vertMap_isSome_iff (x : α) : (vertMap x).isSome ↔ x ∈ V(G)
  /-- The vertex map takes values in the vertex set of the target graph. -/
  vertMap_vertexSet ⦃x : α⦄ ⦃x' : α'⦄ : x' ∈ vertMap x → x' ∈ V(H)
  /-- The partial map on edges. -/
  edgeMap : β → Option β'
  /-- The edge map is defined exactly on the edges of the source graph. -/
  edgeMap_isSome_iff (e : β) : (edgeMap e).isSome ↔ e ∈ E(G)
  /-- The vertex and edge maps preserve links. -/
  map_isLink ⦃e : β⦄ ⦃x y : α⦄ ⦃e' : β'⦄ ⦃x' y' : α'⦄ :
    G.IsLink e x y → e' ∈ edgeMap e → x' ∈ vertMap x → y' ∈ vertMap y → H.IsLink e' x' y'

/-- The edge map of a graph homomorphism takes values in the target edge set. -/
lemma Hom.edgeMap_edgeSet (F : Hom G H) ⦃e : β⦄ ⦃e' : β'⦄ (he' : e' ∈ F.edgeMap e) : e' ∈ E(H) := by
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet <|
    (F.edgeMap_isSome_iff e).mp (option_isSome_iff_exists_mem.mpr ⟨e', he'⟩)
  obtain ⟨x', hx'⟩ := option_isSome_iff_exists_mem.mp ((F.vertMap_isSome_iff x).mpr hxy.left_mem)
  obtain ⟨y', hy'⟩ := option_isSome_iff_exists_mem.mp ((F.vertMap_isSome_iff y).mpr hxy.right_mem)
  exact (F.map_isLink hxy he' hx' hy').edge_mem

/-- A graph embedding, represented by partial equivalences into the vertex and edge types of the
target graph. -/
structure Emb (G : Graph α β) (H : Graph α' β') where
  /-- The partial equivalence on vertices. -/
  vertMap : α ≃. α'
  /-- The vertex map is defined exactly on the vertices of the source graph. -/
  vertMap_isSome_iff (x : α) : (vertMap x).isSome ↔ x ∈ V(G)
  /-- The vertex map takes values in the vertex set of the target graph. -/
  vertMap_vertexSet ⦃x : α⦄ ⦃x' : α'⦄ : x' ∈ vertMap x → x' ∈ V(H)
  /-- The partial equivalence on edges. -/
  edgeMap : β ≃. β'
  /-- The edge map is defined exactly on the edges of the source graph. -/
  edgeMap_isSome_iff (e : β) : (edgeMap e).isSome ↔ e ∈ E(G)
  /-- The vertex and edge maps preserve links. -/
  map_isLink ⦃e : β⦄ ⦃x y : α⦄ ⦃e' : β'⦄ ⦃x' y' : α'⦄ :
    G.IsLink e x y → e' ∈ edgeMap e → x' ∈ vertMap x → y' ∈ vertMap y →
      H.IsLink e' x' y'

/-- Regard a graph embedding as a graph homomorphism. -/
@[simps (attr := grind =)]
def Emb.toHom (F : Emb G H) : Hom G H where
  vertMap := F.vertMap
  vertMap_isSome_iff := F.vertMap_isSome_iff
  vertMap_vertexSet := F.vertMap_vertexSet
  edgeMap := F.edgeMap
  edgeMap_isSome_iff := F.edgeMap_isSome_iff
  map_isLink := F.map_isLink

/-- A graph isomorphism, represented by partial equivalences whose domains in both directions are
exactly the vertex and edge sets of the two graphs. -/
structure Iso (G : Graph α β) (H : Graph α' β') where
  /-- The partial equivalence on vertices. -/
  vertMap : α ≃. α'
  /-- The forward vertex map is defined exactly on the vertices of the source graph. -/
  vertMap_isSome_iff (x : α) : (vertMap x).isSome ↔ x ∈ V(G)
  /-- The inverse vertex map is defined exactly on the vertices of the target graph. -/
  invVertMap_isSome_iff (x : α') : (vertMap.symm x).isSome ↔ x ∈ V(H)
  /-- The partial equivalence on edges. -/
  edgeMap : β ≃. β'
  /-- The forward edge map is defined exactly on the edges of the source graph. -/
  edgeMap_isSome_iff (e : β) : (edgeMap e).isSome ↔ e ∈ E(G)
  /-- The inverse edge map is defined exactly on the edges of the target graph. -/
  invEdgeMap_isSome_iff (e : β') : (edgeMap.symm e).isSome ↔ e ∈ E(H)
  /-- The forward vertex and edge maps preserve links. -/
  map_isLink ⦃e : β⦄ ⦃x y : α⦄ ⦃e' : β'⦄ ⦃x' y' : α'⦄ :
    G.IsLink e x y → e' ∈ edgeMap e → x' ∈ vertMap x → y' ∈ vertMap y →
      H.IsLink e' x' y'
  /-- The inverse vertex and edge maps preserve links. -/
  invMap_isLink ⦃e' : β'⦄ ⦃x' y' : α'⦄ ⦃e : β⦄ ⦃x y : α⦄ :
    H.IsLink e' x' y' → e ∈ edgeMap.symm e' → x ∈ vertMap.symm x' →
      y ∈ vertMap.symm y' → G.IsLink e x y

/-- The identity graph isomorphism. -/
@[simps (attr := grind =)]
noncomputable def Iso.id (G : Graph α β) : Iso G G := by
  classical
  refine
    { vertMap := PEquiv.ofSet V(G)
      vertMap_isSome_iff := ?_
      invVertMap_isSome_iff := ?_
      edgeMap := PEquiv.ofSet E(G)
      edgeMap_isSome_iff := ?_
      invEdgeMap_isSome_iff := ?_
      map_isLink := ?_
      invMap_isLink := ?_ }
  all_goals simp_all [Option.isSome_iff_exists]

/-- Regard a graph isomorphism as a graph embedding. -/
@[simps (attr := grind =)]
def Iso.toEmb (F : Iso G H) : Emb G H where
  vertMap := F.vertMap
  vertMap_isSome_iff := F.vertMap_isSome_iff
  vertMap_vertexSet := fun _ _ h ↦ (F.invVertMap_isSome_iff _).mp <|
    option_isSome_iff_exists_mem.mpr ⟨_, (F.vertMap.eq_some_iff).mpr h⟩
  edgeMap := F.edgeMap
  edgeMap_isSome_iff := F.edgeMap_isSome_iff
  map_isLink := F.map_isLink

/-- Regard a graph isomorphism as a graph homomorphism. -/
@[simps! (attr := grind =)]
def Iso.toHom (F : Iso G H) : Hom G H := F.toEmb.toHom

/-- Compose graph homomorphisms. -/
@[simps (attr := grind =)]
def Hom.comp (F : Hom G H) (F' : Hom H K) : Hom G K where
  vertMap x := (F.vertMap x).bind F'.vertMap
  vertMap_isSome_iff x := by
    rw [option_isSome_iff_exists_mem]
    refine ⟨fun ⟨z, hz⟩ ↦ ?_, fun hx ↦ ?_⟩
    · obtain ⟨y, hy, -⟩ := Option.mem_bind_iff.mp hz
      exact (F.vertMap_isSome_iff x).mp (option_isSome_iff_exists_mem.mpr ⟨y, hy⟩)
    · obtain ⟨y, hy⟩ :=
        option_isSome_iff_exists_mem.mp ((F.vertMap_isSome_iff x).mpr hx)
      obtain ⟨z, hz⟩ := option_isSome_iff_exists_mem.mp <|
        (F'.vertMap_isSome_iff y).mpr (F.vertMap_vertexSet hy)
      exact ⟨z, Option.mem_bind_iff.mpr ⟨y, hy, hz⟩⟩
  vertMap_vertexSet := fun _ _ h ↦ by
    obtain ⟨_, -, h⟩ := Option.mem_bind_iff.mp h
    exact F'.vertMap_vertexSet h
  edgeMap e := (F.edgeMap e).bind F'.edgeMap
  edgeMap_isSome_iff e := by
    rw [option_isSome_iff_exists_mem]
    refine ⟨fun ⟨g, hg⟩ ↦ ?_, fun he ↦ ?_⟩
    · obtain ⟨f, hf, -⟩ := Option.mem_bind_iff.mp hg
      exact (F.edgeMap_isSome_iff e).mp (option_isSome_iff_exists_mem.mpr ⟨f, hf⟩)
    · obtain ⟨f, hf⟩ :=
        option_isSome_iff_exists_mem.mp ((F.edgeMap_isSome_iff e).mpr he)
      obtain ⟨g, hg⟩ := option_isSome_iff_exists_mem.mp <|
        (F'.edgeMap_isSome_iff f).mpr (F.edgeMap_edgeSet hf)
      exact ⟨g, Option.mem_bind_iff.mpr ⟨f, hf, hg⟩⟩
  map_isLink := fun _ _ _ _ _ _ h he hx hy ↦ by
    obtain ⟨f, hf, he⟩ := Option.mem_bind_iff.mp he
    obtain ⟨u, hu, hx⟩ := Option.mem_bind_iff.mp hx
    obtain ⟨v, hv, hy⟩ := Option.mem_bind_iff.mp hy
    exact F'.map_isLink (F.map_isLink h hf hu hv) he hx hy

/-- Compose graph embeddings. -/
@[simps (attr := grind =)]
def Emb.comp (F : Emb G H) (F' : Emb H K) : Emb G K where
  vertMap := F.vertMap.trans F'.vertMap
  vertMap_isSome_iff x := by
    rw [option_isSome_iff_exists_mem]
    refine ⟨fun ⟨z, hz⟩ ↦ ?_, fun hx ↦ ?_⟩
    · obtain ⟨y, hy, -⟩ := (F.vertMap.mem_trans F'.vertMap x z).mp hz
      exact (F.vertMap_isSome_iff x).mp (option_isSome_iff_exists_mem.mpr ⟨y, hy⟩)
    · obtain ⟨y, hy⟩ :=
        option_isSome_iff_exists_mem.mp ((F.vertMap_isSome_iff x).mpr hx)
      obtain ⟨z, hz⟩ := option_isSome_iff_exists_mem.mp <|
        (F'.vertMap_isSome_iff y).mpr (F.vertMap_vertexSet hy)
      exact ⟨z, (F.vertMap.mem_trans F'.vertMap x z).mpr ⟨y, hy, hz⟩⟩
  vertMap_vertexSet := fun _ _ h ↦ by
    obtain ⟨_, -, h⟩ := (F.vertMap.mem_trans F'.vertMap _ _).mp h
    exact F'.vertMap_vertexSet h
  edgeMap := F.edgeMap.trans F'.edgeMap
  edgeMap_isSome_iff e := by
    rw [option_isSome_iff_exists_mem]
    refine ⟨fun ⟨g, hg⟩ ↦ ?_, fun he ↦ ?_⟩
    · obtain ⟨f, hf, -⟩ := (F.edgeMap.mem_trans F'.edgeMap e g).mp hg
      exact (F.edgeMap_isSome_iff e).mp (option_isSome_iff_exists_mem.mpr ⟨f, hf⟩)
    · obtain ⟨f, hf⟩ :=
        option_isSome_iff_exists_mem.mp ((F.edgeMap_isSome_iff e).mpr he)
      obtain ⟨g, hg⟩ := option_isSome_iff_exists_mem.mp <|
        (F'.edgeMap_isSome_iff f).mpr (F.toHom.edgeMap_edgeSet hf)
      exact ⟨g, (F.edgeMap.mem_trans F'.edgeMap e g).mpr ⟨f, hf, hg⟩⟩
  map_isLink := fun _ _ _ _ _ _ h he hx hy ↦ by
    obtain ⟨f, hf, he⟩ := (F.edgeMap.mem_trans F'.edgeMap _ _).mp he
    obtain ⟨u, hu, hx⟩ := (F.vertMap.mem_trans F'.vertMap _ _).mp hx
    obtain ⟨v, hv, hy⟩ := (F.vertMap.mem_trans F'.vertMap _ _).mp hy
    exact F'.map_isLink (F.map_isLink h hf hu hv) he hx hy

/-- Reverse a graph isomorphism. -/
@[simps (attr := grind =)]
def Iso.symm (F : Iso G H) : Iso H G where
  vertMap := F.vertMap.symm
  vertMap_isSome_iff := F.invVertMap_isSome_iff
  invVertMap_isSome_iff := F.vertMap_isSome_iff
  edgeMap := F.edgeMap.symm
  edgeMap_isSome_iff := F.invEdgeMap_isSome_iff
  invEdgeMap_isSome_iff := F.edgeMap_isSome_iff
  map_isLink := F.invMap_isLink
  invMap_isLink := F.map_isLink

/-- Compose graph isomorphisms. -/
@[simps (attr := grind =)]
def Iso.comp (F : Iso G H) (F' : Iso H K) : Iso G K where
  vertMap := F.vertMap.trans F'.vertMap
  vertMap_isSome_iff := F.toEmb.comp F'.toEmb |>.vertMap_isSome_iff
  invVertMap_isSome_iff := by
    simp only [PEquiv.symm_trans_rev]
    exact (F'.symm.toEmb.comp F.symm.toEmb).vertMap_isSome_iff
  edgeMap := F.edgeMap.trans F'.edgeMap
  edgeMap_isSome_iff := F.toEmb.comp F'.toEmb |>.edgeMap_isSome_iff
  invEdgeMap_isSome_iff := by
    simp only [PEquiv.symm_trans_rev]
    exact (F'.symm.toEmb.comp F.symm.toEmb).edgeMap_isSome_iff
  map_isLink := F.toEmb.comp F'.toEmb |>.map_isLink
  invMap_isLink := F'.symm.toEmb.comp F.symm.toEmb |>.map_isLink

/-- Restrict the source of a graph homomorphism. -/
@[simps (attr := grind =)]
noncomputable def Hom.anti_left (G' : Graph α β) (hG' : G' ≤ G) (F : Hom G H) : Hom G' H := by
  classical
  exact
    { vertMap := fun x ↦ if x ∈ V(G') then F.vertMap x else none
      vertMap_isSome_iff := fun x ↦ by grind [F.vertMap_isSome_iff, hG'.vertexSet_mono]
      vertMap_vertexSet := fun _ _ hx' ↦ by
        split_ifs at hx'
        · exact F.vertMap_vertexSet hx'
        · simp at hx'
      edgeMap := fun e ↦ if e ∈ E(G') then F.edgeMap e else none
      edgeMap_isSome_iff := fun e ↦ by grind [F.edgeMap_isSome_iff, hG'.edgeSet_mono]
      map_isLink := fun _ _ _ _ _ _ hxy he' hx' hy' ↦ by
        simp only [hxy.edge_mem, hxy.left_mem, hxy.right_mem, ↓reduceIte] at he' hx' hy'
        exact F.map_isLink (hG'.isLink_mono hxy) he' hx' hy' }

/-- Restrict the source of a graph embedding. -/
@[simps (attr := grind =)]
noncomputable def Emb.anti_left (G' : Graph α β) (hG' : G' ≤ G) (F : Emb G H) : Emb G' H := by
  classical
  let v := (PEquiv.ofSet V(G')).trans F.vertMap
  let e := (PEquiv.ofSet E(G')).trans F.edgeMap
  exact
    { vertMap := v
      vertMap_isSome_iff := fun x ↦ by
        simp only [v, option_isSome_iff_exists_mem, PEquiv.mem_trans, PEquiv.mem_ofSet_iff]
        refine ⟨fun ⟨_, _, ⟨rfl, hx⟩, _⟩ ↦ hx, fun hx ↦ ?_⟩
        obtain ⟨z, hz⟩ := option_isSome_iff_exists_mem.mp <|
          (F.vertMap_isSome_iff x).mpr (hG'.vertexSet_mono hx)
        exact ⟨z, x, ⟨rfl, hx⟩, hz⟩
      vertMap_vertexSet := fun _ _ hx' ↦ by
        obtain ⟨_, -, hx'⟩ := (PEquiv.mem_trans _ _ _ _).mp hx'
        exact F.vertMap_vertexSet hx'
      edgeMap := e
      edgeMap_isSome_iff := fun f ↦ by
        simp only [e, option_isSome_iff_exists_mem, PEquiv.mem_trans, PEquiv.mem_ofSet_iff]
        refine ⟨fun ⟨_, _, ⟨rfl, hf⟩, _⟩ ↦ hf, fun hf ↦ ?_⟩
        obtain ⟨g, hg⟩ := option_isSome_iff_exists_mem.mp <|
          (F.edgeMap_isSome_iff f).mpr (hG'.edgeSet_mono hf)
        exact ⟨g, f, ⟨rfl, hf⟩, hg⟩
      map_isLink := fun f x y f' x' y' hxy hf' hx' hy' ↦ by
        simp only [e, v, PEquiv.mem_trans, PEquiv.mem_ofSet_iff] at hf' hx' hy'
        obtain ⟨_, ⟨rfl, -⟩, hf'⟩ := hf'
        obtain ⟨_, ⟨rfl, -⟩, hx'⟩ := hx'
        obtain ⟨_, ⟨rfl, -⟩, hy'⟩ := hy'
        exact F.map_isLink (hG'.isLink_mono hxy) hf' hx' hy' }

/-- Enlarge the target of a graph homomorphism. -/
@[simps (attr := grind =)]
def Hom.mono_right (H' : Graph α' β') (hH' : H ≤ H') (F : Hom G H) : Hom G H' where
  vertMap := F.vertMap
  vertMap_isSome_iff := F.vertMap_isSome_iff
  vertMap_vertexSet := fun _ _ h ↦ hH'.vertexSet_mono (F.vertMap_vertexSet h)
  edgeMap := F.edgeMap
  edgeMap_isSome_iff := F.edgeMap_isSome_iff
  map_isLink := fun _ _ _ _ _ _ h he hx hy ↦ hH'.isLink_mono (F.map_isLink h he hx hy)

/-- Enlarge the target of a graph embedding. -/
@[simps (attr := grind =)]
def Emb.mono_right (H' : Graph α' β') (hH' : H ≤ H') (F : Emb G H) : Emb G H' where
  vertMap := F.vertMap
  vertMap_isSome_iff := F.vertMap_isSome_iff
  vertMap_vertexSet := fun _ _ h ↦ hH'.vertexSet_mono (F.vertMap_vertexSet h)
  edgeMap := F.edgeMap
  edgeMap_isSome_iff := F.edgeMap_isSome_iff
  map_isLink := fun _ _ _ _ _ _ h he hx hy ↦ hH'.isLink_mono (F.map_isLink h he hx hy)

end Graph
