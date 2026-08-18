/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Data.PEquiv
public import Matroid.Graph.Subgraph.Basic

/-!
# Homomorphisms, embeddings and isomorphisms

This file supersedes `Matroid/Graph/Hom.lean`, which it was ported from: the graphs are now
Mathlib's two-carrier `Graph V E`, so there are no half-edges and the maps are on vertices and
edges alone. The structures are otherwise unchanged — `Hom` uses `Option`-valued maps, while `Emb`
and `Iso` use partial equivalences.

A map is *partial on the ambient carriers and total on the active sets*: `vertMap : V → Option V'`
with `(vertMap x).isSome ↔ x ∈ V(G)`. That is what lets a graph sit inside an arbitrarily large
ambient type without the maps having to say anything about the labels it does not use, and it is
why `Iso` carries an `isSome` condition per carrier in each direction — `vertMap_isSome_iff` and
`invVertMap_isSome_iff`, and likewise for edges — rather than a bare bijection. What an `Iso` sees
is therefore exactly `V(G)`, `E(G)` and `IsLink`, the same design point as `Graph.IsLinkEquiv` in
`Graph/Basic.lean`.

## Main definitions

* `Graph.Hom G H` — vertex/edge maps defined exactly on `V(G)`/`E(G)`, carrying links to links
* `Graph.Emb G H` — the same with partial *equivalences*, hence injective
* `Graph.Iso G H` — an `Emb` whose inverse is defined exactly on `V(H)`/`E(H)`
* `Graph.IsIsoTo G H` — `Nonempty (Iso G H)`
-/

@[expose] public section

open Set Function

namespace Graph

variable {V V' V'' E E' E'' : Type*} {G : Graph V E} {H : Graph V' E'}
  {K : Graph V'' E''} {x y : V} {e : E}

lemma option_isSome_iff_exists_mem {o : Option V} : o.isSome ↔ ∃ x, x ∈ o := by
  simp [Option.isSome_iff_exists]

/-- A graph homomorphism, represented by partial maps whose domains are exactly the vertex and
edge sets of the source graph. -/
structure Hom (G : Graph V E) (H : Graph V' E') where
  /-- The partial map on vertices. -/
  vertMap : V → Option V'
  /-- The vertex map is defined exactly on the vertices of the source graph. -/
  vertMap_isSome_iff (x : V) : (vertMap x).isSome ↔ x ∈ V(G)
  /-- The vertex map takes values in the vertex set of the target graph. -/
  vertMap_vertexSet ⦃x : V⦄ ⦃x' : V'⦄ : x' ∈ vertMap x → x' ∈ V(H)
  /-- The partial map on edges. -/
  edgeMap : E → Option E'
  /-- The edge map is defined exactly on the edges of the source graph. -/
  edgeMap_isSome_iff (e : E) : (edgeMap e).isSome ↔ e ∈ E(G)
  /-- The vertex and edge maps preserve links. -/
  map_isLink ⦃e : E⦄ ⦃x y : V⦄ ⦃e' : E'⦄ ⦃x' y' : V'⦄ :
    G.IsLink e x y → e' ∈ edgeMap e → x' ∈ vertMap x → y' ∈ vertMap y → H.IsLink e' x' y'

/-- The edge map of a graph homomorphism takes values in the target edge set. -/
lemma Hom.edgeMap_edgeSet (F : Hom G H) {e : E} {e' : E'} (he' : e' ∈ F.edgeMap e) : e' ∈ E(H) := by
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet <|
    (F.edgeMap_isSome_iff e).mp (option_isSome_iff_exists_mem.mpr ⟨e', he'⟩)
  obtain ⟨x', hx'⟩ := option_isSome_iff_exists_mem.mp ((F.vertMap_isSome_iff x).mpr hxy.left_mem)
  obtain ⟨y', hy'⟩ := option_isSome_iff_exists_mem.mp ((F.vertMap_isSome_iff y).mpr hxy.right_mem)
  exact (F.map_isLink hxy he' hx' hy').edge_mem

/-- A graph embedding, represented by partial equivalences into the vertex and edge types of the
target graph. -/
structure Emb (G : Graph V E) (H : Graph V' E') where
  /-- The partial equivalence on vertices. -/
  vertMap : V ≃. V'
  /-- The vertex map is defined exactly on the vertices of the source graph. -/
  vertMap_isSome_iff (x : V) : (vertMap x).isSome ↔ x ∈ V(G)
  /-- The vertex map takes values in the vertex set of the target graph. -/
  vertMap_vertexSet ⦃x : V⦄ ⦃x' : V'⦄ : x' ∈ vertMap x → x' ∈ V(H)
  /-- The partial equivalence on edges. -/
  edgeMap : E ≃. E'
  /-- The edge map is defined exactly on the edges of the source graph. -/
  edgeMap_isSome_iff (e : E) : (edgeMap e).isSome ↔ e ∈ E(G)
  /-- The vertex and edge maps preserve links. -/
  map_isLink ⦃e : E⦄ ⦃x y : V⦄ ⦃e' : E'⦄ ⦃x' y' : V'⦄ :
    G.IsLink e x y → e' ∈ edgeMap e → x' ∈ vertMap x → y' ∈ vertMap y → H.IsLink e' x' y'

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
structure Iso (G : Graph V E) (H : Graph V' E') where
  /-- The partial equivalence on vertices. -/
  vertMap : V ≃. V'
  /-- The forward vertex map is defined exactly on the vertices of the source graph. -/
  vertMap_isSome_iff (x : V) : (vertMap x).isSome ↔ x ∈ V(G)
  /-- The inverse vertex map is defined exactly on the vertices of the target graph. -/
  invVertMap_isSome_iff (x : V') : (vertMap.symm x).isSome ↔ x ∈ V(H)
  /-- The partial equivalence on edges. -/
  edgeMap : E ≃. E'
  /-- The forward edge map is defined exactly on the edges of the source graph. -/
  edgeMap_isSome_iff (e : E) : (edgeMap e).isSome ↔ e ∈ E(G)
  /-- The inverse edge map is defined exactly on the edges of the target graph. -/
  invEdgeMap_isSome_iff (e : E') : (edgeMap.symm e).isSome ↔ e ∈ E(H)
  /-- The forward vertex and edge maps preserve links. -/
  map_isLink ⦃e : E⦄ ⦃x y : V⦄ ⦃e' : E'⦄ ⦃x' y' : V'⦄ :
    G.IsLink e x y → e' ∈ edgeMap e → x' ∈ vertMap x → y' ∈ vertMap y → H.IsLink e' x' y'
  /-- The inverse vertex and edge maps preserve links. -/
  invMap_isLink ⦃e' : E'⦄ ⦃x' y' : V'⦄ ⦃e : E⦄ ⦃x y : V⦄ :
    H.IsLink e' x' y' → e ∈ edgeMap.symm e' → x ∈ vertMap.symm x' → y ∈ vertMap.symm y' →
      G.IsLink e x y

/-- The identity graph isomorphism. -/
noncomputable def Iso.id (G : Graph V E) : Iso G G := by
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
@[simps!]
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
noncomputable def Hom.anti_left (G' : Graph V E) (hG' : G' ≤ G) (F : Hom G H) : Hom G' H := by
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
noncomputable def Emb.anti_left (G' : Graph V E) (hG' : G' ≤ G) (F : Emb G H) : Emb G' H := by
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
def Hom.mono_right (H' : Graph V' E') (hH' : H ≤ H') (F : Hom G H) : Hom G H' where
  vertMap := F.vertMap
  vertMap_isSome_iff := F.vertMap_isSome_iff
  vertMap_vertexSet := fun _ _ h ↦ hH'.vertexSet_mono (F.vertMap_vertexSet h)
  edgeMap := F.edgeMap
  edgeMap_isSome_iff := F.edgeMap_isSome_iff
  map_isLink := fun _ _ _ _ _ _ h he hx hy ↦ hH'.isLink_mono (F.map_isLink h he hx hy)

/-- Enlarge the target of a graph embedding. -/
@[simps (attr := grind =)]
def Emb.mono_right (H' : Graph V' E') (hH' : H ≤ H') (F : Emb G H) : Emb G H' where
  vertMap := F.vertMap
  vertMap_isSome_iff := F.vertMap_isSome_iff
  vertMap_vertexSet := fun _ _ h ↦ hH'.vertexSet_mono (F.vertMap_vertexSet h)
  edgeMap := F.edgeMap
  edgeMap_isSome_iff := F.edgeMap_isSome_iff
  map_isLink := fun _ _ _ _ _ _ h he hx hy ↦ hH'.isLink_mono (F.map_isLink h he hx hy)

/-! ### Isomorphism as a relation

This is the mechanism that lets every containment relation stay label-coherent while still
supporting statements about named patterns. `CompleteGraph n : Graph ℕ (Sym2 ℕ) …` and
`CompleteBipartiteGraph m n` have *fixed* carriers, different from each other and from an
arbitrary `G : Graph V E`, so any statement of the form "`G` contains a `K₅`" must cross
carriers somewhere. Putting the carrier change in one place — here — keeps `≤`, `IsMinor` and
`TopologicalMinor` all label-coherent, and is why `Minor/Iso.lean` and `TopologicalMinor.lean`
need no bespoke normalisation machinery. -/

/-- `G` and `H` are isomorphic. -/
def IsIsoTo (G : Graph V E) (H : Graph V' E') : Prop := Nonempty (Iso G H)

@[refl] lemma IsIsoTo.refl (G : Graph V E) : G.IsIsoTo G := ⟨Iso.id G⟩

@[symm] lemma IsIsoTo.symm (h : G.IsIsoTo H) : H.IsIsoTo G := ⟨h.some.symm⟩

lemma IsIsoTo.trans (h : G.IsIsoTo H) (h' : H.IsIsoTo K) : G.IsIsoTo K := ⟨h.some.comp h'.some⟩

/-- The vertex map of an isomorphism embeds the source vertex set into the target vertex set. -/
def Iso.vertMapEmbedding (F : Iso G H) : V(G) ↪ V(H) where
  toFun x := ⟨(F.vertMap x.1).get ((F.vertMap_isSome_iff x.1).mpr x.2),
    F.toEmb.vertMap_vertexSet (Option.get_mem ((F.vertMap_isSome_iff x.1).mpr x.2))⟩
  inj' := by
    intro x y hxy
    apply Subtype.ext
    have hx : (F.vertMap x.1).isSome := (F.vertMap_isSome_iff x.1).mpr x.2
    have hy : (F.vertMap y.1).isSome := (F.vertMap_isSome_iff y.1).mpr y.2
    have hx' : (F.vertMap x.1).get hx ∈ F.vertMap x.1 := Option.get_mem hx
    have hy' : (F.vertMap y.1).get hy ∈ F.vertMap y.1 := Option.get_mem hy
    have hget : (F.vertMap x.1).get hx = (F.vertMap y.1).get hy := by
      simpa using congrArg Subtype.val hxy
    exact F.vertMap.inj hx' (by simp [hget])

/-- The edge map of an isomorphism embeds the source edge set into the target edge set. -/
def Iso.edgeMapEmbedding (F : Iso G H) : E(G) ↪ E(H) where
  toFun e := ⟨(F.edgeMap e.1).get ((F.edgeMap_isSome_iff e.1).mpr e.2),
    F.toHom.edgeMap_edgeSet (Option.get_mem ((F.edgeMap_isSome_iff e.1).mpr e.2))⟩
  inj' := by
    intro e f hef
    apply Subtype.ext
    have he : (F.edgeMap e.1).isSome := (F.edgeMap_isSome_iff e.1).mpr e.2
    have hf : (F.edgeMap f.1).isSome := (F.edgeMap_isSome_iff f.1).mpr f.2
    have he' : (F.edgeMap e.1).get he ∈ F.edgeMap e.1 := Option.get_mem he
    have hf' : (F.edgeMap f.1).get hf ∈ F.edgeMap f.1 := Option.get_mem hf
    have hget : (F.edgeMap e.1).get he = (F.edgeMap f.1).get hf := by
      simpa using congrArg Subtype.val hef
    exact F.edgeMap.inj he' (by simp [hget])

/-! ### The active carriers of an isomorphism

`Iso` transports `V(G)` and `E(G)`, never the ambient `V` and `E`: unused labels are invisible to
the graph, and the ambient types may even have different cardinalities. These two equivalences
are therefore the whole of what an isomorphism does to data, and everything that transports a
graph-dependent object along an isomorphism factors through them. -/

lemma Iso.vertMapEmbedding_surjective (F : Iso G H) :
    Function.Surjective F.vertMapEmbedding := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx⟩ := option_isSome_iff_exists_mem.mp <| (F.invVertMap_isSome_iff y).mpr hy
  have hyx : y ∈ F.vertMap x := F.vertMap.mem_iff_mem.mp hx
  refine ⟨⟨x, (F.vertMap_isSome_iff x).mp (option_isSome_iff_exists_mem.mpr ⟨y, hyx⟩)⟩,
    Subtype.ext ?_⟩
  simp [Iso.vertMapEmbedding, show F.vertMap x = some y from Option.mem_def.mp hyx]

lemma Iso.edgeMapEmbedding_surjective (F : Iso G H) :
    Function.Surjective F.edgeMapEmbedding := by
  rintro ⟨f, hf⟩
  obtain ⟨e, he⟩ := option_isSome_iff_exists_mem.mp <| (F.invEdgeMap_isSome_iff f).mpr hf
  have hfe : f ∈ F.edgeMap e := F.edgeMap.mem_iff_mem.mp he
  refine ⟨⟨e, (F.edgeMap_isSome_iff e).mp (option_isSome_iff_exists_mem.mpr ⟨f, hfe⟩)⟩,
    Subtype.ext ?_⟩
  simp [Iso.edgeMapEmbedding, show F.edgeMap e = some f from Option.mem_def.mp hfe]

/-- The bijection between vertex sets induced by an isomorphism. -/
def Iso.vertexEquiv (F : Iso G H) : V(G) ≃ V(H) where
  toFun := F.vertMapEmbedding
  invFun := F.symm.vertMapEmbedding
  left_inv _ := Subtype.ext <| Option.mem_unique (Option.get_mem _)
    <| F.vertMap.mem_iff_mem.mpr (Option.get_mem _)
  right_inv _ := Subtype.ext <| Option.mem_unique (Option.get_mem _)
    <| F.vertMap.mem_iff_mem.mp (Option.get_mem _)

/-- The bijection between edge sets induced by an isomorphism. -/
def Iso.edgeEquiv (F : Iso G H) : E(G) ≃ E(H) where
  toFun := F.edgeMapEmbedding
  invFun := F.symm.edgeMapEmbedding
  left_inv _ := Subtype.ext <| Option.mem_unique (Option.get_mem _)
    <| F.edgeMap.mem_iff_mem.mpr (Option.get_mem _)
  right_inv _ := Subtype.ext <| Option.mem_unique (Option.get_mem _)
    <| F.edgeMap.mem_iff_mem.mp (Option.get_mem _)

@[simp] lemma Iso.vertexEquiv_apply (F : Iso G H) (x : V(G)) :
    F.vertexEquiv x = F.vertMapEmbedding x := rfl

@[simp] lemma Iso.edgeEquiv_apply (F : Iso G H) (e : E(G)) :
    F.edgeEquiv e = F.edgeMapEmbedding e := rfl

/-- The characterising property of `vertexEquiv`: it picks out the value of the partial vertex
map. This, not the definition, is what downstream proofs should use. -/
lemma Iso.mem_vertMap_vertexEquiv (F : Iso G H) (x : V(G)) :
    ((F.vertexEquiv x : V(H)) : V') ∈ F.vertMap (x : V) :=
  Option.get_mem _

/-- The characterising property of `edgeEquiv`; see `Iso.mem_vertMap_vertexEquiv`. -/
lemma Iso.mem_edgeMap_edgeEquiv (F : Iso G H) (e : E(G)) :
    ((F.edgeEquiv e : E(H)) : E') ∈ F.edgeMap (e : E) :=
  Option.get_mem _

/-- Non-canonical enumeration of a 2-element set. -/
private noncomputable def equivFin2_of_encard_eq {α : Type*} {s : Set α} (h : s.encard = 2) :
    s ≃ Fin 2 :=
  have : Fintype s := (finite_of_encard_eq_coe h).fintype
  Fintype.equivFinOfCardEq <| by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    simp [ncard_def, h]

lemma IsIsoTo.vertexSet_encard_eq (h : G.IsIsoTo H) : V(G).encard = V(H).encard := by
  exact le_antisymm (Function.Embedding.encard_le h.some.vertMapEmbedding)
    (Function.Embedding.encard_le h.some.symm.vertMapEmbedding)

lemma IsIsoTo.edgeSet_encard_eq (h : G.IsIsoTo H) : E(G).encard = E(H).encard := by
  exact le_antisymm (Function.Embedding.encard_le h.some.edgeMapEmbedding)
    (Function.Embedding.encard_le h.some.symm.edgeMapEmbedding)

/-- Isomorphic graphs have isomorphic link relations, in the sense of `IsLinkEquiv`, after
transporting along the vertex and edge bijections. -/
lemma Iso.isLink_iff_isLink (F : Iso G H) ⦃e : E⦄ ⦃x y : V⦄ ⦃e' : E'⦄ ⦃x' y' : V'⦄
    (he : e' ∈ F.edgeMap e) (hx : x' ∈ F.vertMap x) (hy : y' ∈ F.vertMap y) :
    G.IsLink e x y ↔ H.IsLink e' x' y' := by
  constructor
  · exact fun h ↦ F.map_isLink h he hx hy
  · exact (F.invMap_isLink · ((F.edgeMap.eq_some_iff).mpr he)
      ((F.vertMap.eq_some_iff).mpr hx) ((F.vertMap.eq_some_iff).mpr hy))

end Graph
