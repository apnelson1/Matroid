/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Combinatorics.Graph.Subgraph
public import Matroid.ForMathlib.Tactic.IRw

/-!
# Graph homomorphisms, embeddings and isomorphisms

Maps act directly on `V(G)` and `E(G)`. `Emb` extends `Hom` with injectivity;
`Iso` extends `Emb` with explicit inverse functions and their two-sided inverse laws.
The forward functions and link-preservation proof are stored only once. Homomorphism
constructions and lemmas are consequently available to embeddings and isomorphisms by
inherited dot notation.

`Emb.vertEmbedding` and `Emb.edgeEmbedding` expose the full `Function.Embedding` interface;
`Iso.vertEquiv` and `Iso.edgeEquiv` expose the full `Equiv` interface. These are derived views,
with computation and composition laws relating them to the inherited functions. Constructors
from embeddings and equivalences accept these bundled interfaces without requiring callers
to unpack their laws. Inverse link preservation follows from forward preservation and vertex
injectivity; it is not an additional structure field.

Composition `F.comp F'` means first `F`, then `F'`.

All computational data, including inverse maps, is supplied by the definitions.
-/

@[expose] public section

open Set Function

namespace Graph

variable {V₀ E₀ V₁ E₁ V₂ E₂ V₃ E₃ : Type*} {G : Graph V₀ E₀} {H : Graph V₁ E₁} {K : Graph V₂ E₂}
  {L : Graph V₃ E₃} {e f : E(G)} {x y : V(G)}

/-- A link-preserving pair of maps on the vertex and edge sets. -/
structure Hom (G : Graph V₀ E₀) (H : Graph V₁ E₁) where
  /-- The function on vertices. -/
  vertMap : V(G) → V(H)
  /-- The function on edges. -/
  edgeMap : E(G) → E(H)
  /-- Mapped edges have the mapped endpoints. -/
  map_isLink ⦃e : E(G)⦄ ⦃x y : V(G)⦄ :
    G.IsLink e.1 x.1 y.1 → H.IsLink (edgeMap e).1 (vertMap x).1 (vertMap y).1

/-- A homomorphism injective on both vertex and edge sets. This need not be an induced embedding. -/
structure Emb (G : Graph V₀ E₀) (H : Graph V₁ E₁) extends Hom G H where
  /-- Distinct vertices have distinct images. -/
  vertMap_injective : Injective vertMap
  /-- Distinct edges have distinct images. -/
  edgeMap_injective : Injective edgeMap

/-- An embedding with specified two-sided inverses on both vertex and edge sets. -/
structure Iso (G : Graph V₀ E₀) (H : Graph V₁ E₁) extends Emb G H where
  /-- The specified inverse function on vertices. -/
  invVertMap : V(H) → V(G)
  /-- The specified inverse function on edges. -/
  invEdgeMap : E(H) → E(G)
  vertMap_leftInverse (x : V(G)) : invVertMap (vertMap x) = x
  vertMap_rightInverse (x : V(H)) : vertMap (invVertMap x) = x
  edgeMap_leftInverse (e : E(G)) : invEdgeMap (edgeMap e) = e
  edgeMap_rightInverse (e : E(H)) : edgeMap (invEdgeMap e) = e

attribute [irw_system] Graph.Iso
attribute [simp] Iso.vertMap_leftInverse Iso.vertMap_rightInverse
  Iso.edgeMap_leftInverse Iso.edgeMap_rightInverse

namespace Hom

@[ext]
theorem ext {F F' : Hom G H} (hV : ∀ x, F.vertMap x = F'.vertMap x)
    (hE : ∀ e, F.edgeMap e = F'.edgeMap e) : F = F' := by
  cases F
  cases F'
  cases funext hV
  cases funext hE
  rfl

/-- The identity homomorphism. -/
def id (G : Graph V₀ E₀) : Hom G G where
  vertMap := _root_.id
  edgeMap := _root_.id
  map_isLink := by tauto

/-- Composition in diagrammatic order. -/
def comp (F : Hom G H) (F' : Hom H K) : Hom G K where
  vertMap := F'.vertMap ∘ F.vertMap
  edgeMap := F'.edgeMap ∘ F.edgeMap
  map_isLink := fun _ _ _ h ↦ F'.map_isLink (F.map_isLink h)

@[simp]
theorem id_comp (F : Hom G H) : (id G).comp F = F := by
  apply ext <;> intro <;> rfl

@[simp]
theorem comp_id (F : Hom G H) : F.comp (id H) = F := by
  apply ext <;> intro <;> rfl

theorem comp_assoc (F : Hom G H) (F' : Hom H K) (F'' : Hom K L) :
    (F.comp F').comp F'' = F.comp (F'.comp F'') := by
  apply ext <;> intro <;> rfl

/-- Homomorphisms preserve adjacency, without injectivity assumptions. -/
theorem map_adj (F : Hom G H) (h : G.Adj x.1 y.1) : H.Adj (F.vertMap x).1 (F.vertMap y).1 := by
  obtain ⟨e, he⟩ := h
  exact ⟨(F.edgeMap ⟨e, he.edge_mem⟩).1, F.map_isLink he⟩

/-- Vertex injectivity reflects the endpoints of each specified source edge.
It does not assert reflection of arbitrary host adjacency. -/
theorem isLink_iff_of_injective {F : Hom G H} (hv : Injective F.vertMap) (e : E(G)) (x y : V(G)) :
    H.IsLink (F.edgeMap e).1 (F.vertMap x).1 (F.vertMap y).1 ↔ G.IsLink e.1 x.1 y.1 := by
  refine ⟨fun h ↦ ?_, (F.map_isLink .)⟩
  obtain ⟨u, v, huv⟩ := G.exists_isLink_of_mem_edgeSet e.2
  have h' := F.map_isLink (e := e) (x := ⟨u, huv.left_mem⟩) (y := ⟨v, huv.right_mem⟩) huv
  obtain ⟨hx, hy⟩ | ⟨hx, hy⟩ := h.eq_and_eq_or_eq_and_eq h' <;>
    rw [Subtype.val_inj, hv.eq_iff, ← Subtype.coe_inj] at hx hy <;> rw [hx, hy]
  · exact huv
  · exact huv.symm

/-- Adjacency reflection needs vertex injectivity and edge surjectivity, but not an
inverse vertex map or edge injectivity. -/
theorem adj_iff_of_injective_of_surjective {F : Hom G H} (hv : Injective F.vertMap)
    (he : Surjective F.edgeMap) (x y : V(G)) :
    G.Adj x.1 y.1 ↔ H.Adj (F.vertMap x).1 (F.vertMap y).1 := by
  refine ⟨F.map_adj, fun ⟨e, h⟩ ↦ ?_⟩
  obtain ⟨e', he'⟩ := he ⟨e, h.edge_mem⟩
  refine ⟨e'.1, (isLink_iff_of_injective hv e' x y).mp ?_⟩
  simpa [he'] using h

/-- Postcomposition cancels when both maps of the second factor are injective. -/
theorem comp_left_injective {F' : Hom H K} (hv : Injective F'.vertMap)
    (he : Injective F'.edgeMap) : Injective (fun F : Hom G H ↦ F.comp F') := by
  intro F₁ F₂ h
  apply ext (fun x ↦ hv ?_) (fun e ↦ he ?_)
  · exact congrArg (fun F : Hom G K ↦ F.vertMap x) h
  · exact congrArg (fun F : Hom G K ↦ F.edgeMap e) h

/-- Precomposition cancels when both maps of the first factor are surjective. -/
theorem comp_right_injective (F : Hom G H) (hv : Surjective F.vertMap)
    (he : Surjective F.edgeMap) : Injective (fun F' : Hom H K ↦ F.comp F') := by
  intro F₁ F₂ h
  apply ext (fun y ↦ ?_) (fun e ↦ ?_)
  · obtain ⟨x, rfl⟩ := hv y
    exact congrArg (fun F' : Hom G K ↦ F'.vertMap x) h
  · obtain ⟨e', rfl⟩ := he e
    exact congrArg (fun F' : Hom G K ↦ F'.edgeMap e') h

@[simp]
theorem id_vertMap (G : Graph V₀ E₀) : (id G).vertMap = _root_.id :=
  rfl

@[simp]
theorem comp_vertMap (F : Hom G H) (F' : Hom H K) : (F.comp F').vertMap = F'.vertMap ∘ F.vertMap :=
  rfl

@[grind =]
theorem comp_vertMap_apply (F : Hom G H) (F' : Hom H K) (x : V(G)) :
    (F.comp F').vertMap x = F'.vertMap (F.vertMap x) :=
  rfl

@[simp]
theorem id_edgeMap (G : Graph V₀ E₀) : (id G).edgeMap = _root_.id :=
  rfl

@[simp]
theorem comp_edgeMap (F : Hom G H) (F' : Hom H K) : (F.comp F').edgeMap = F'.edgeMap ∘ F.edgeMap :=
  rfl

@[grind =]
theorem comp_edgeMap_apply (F : Hom G H) (F' : Hom H K) (x : E(G)) :
    (F.comp F').edgeMap x = F'.edgeMap (F.edgeMap x) :=
  rfl

end Hom

namespace Emb

@[ext]
theorem ext {F F' : Emb G H} (hV : ∀ x, F.vertMap x = F'.vertMap x)
    (hE : ∀ e, F.edgeMap e = F'.edgeMap e) : F = F' := by
  have h : F.toHom = F'.toHom := Hom.ext hV hE
  cases F
  cases F'
  cases h
  rfl

theorem toHom_injective : Injective (toHom : Emb G H → Hom G H) := by
  intro F F' h
  apply ext (fun x ↦ ?_) (fun e ↦ ?_)
  · exact congrArg (fun F : Hom G H ↦ F.vertMap x) h
  · exact congrArg (fun F : Hom G H ↦ F.edgeMap e) h

/-- Bundle an injective homomorphism without changing its maps. -/
def ofInjective (F : Hom G H) (hv : Injective F.vertMap) (he : Injective F.edgeMap) : Emb G H where
  toHom := F
  vertMap_injective := hv
  edgeMap_injective := he

/-- Construct an embedding from bundled carrier embeddings. -/
def ofEmbeddings (v : V(G) ↪ V(H)) (e : E(G) ↪ E(H))
    (h : ∀ ⦃f : E(G)⦄ ⦃x y : V(G)⦄, G.IsLink f.1 x.1 y.1 → H.IsLink (e f).1 (v x).1 (v y).1) :
    Emb G H where
  vertMap := v
  edgeMap := e
  map_isLink := h
  vertMap_injective := v.injective
  edgeMap_injective := e.injective

/-- The identity embedding. -/
def id (G : Graph V₀ E₀) : Emb G G where
  toHom := Hom.id G
  vertMap_injective := injective_id
  edgeMap_injective := injective_id

/-- Composition of embeddings. -/
def comp (F : Emb G H) (F' : Emb H K) : Emb G K where
  toHom := F.toHom.comp F'.toHom
  vertMap_injective := F'.vertMap_injective.comp F.vertMap_injective
  edgeMap_injective := F'.edgeMap_injective.comp F.edgeMap_injective

/-- The identity-on-labels embedding of a subgraph. -/
def ofLe {G H : Graph V₀ E₀} (h : H ≤ G) : Emb H G where
  vertMap x := ⟨x.1, h.vertexSet_mono x.2⟩
  edgeMap e := ⟨e.1, h.edgeSet_mono e.2⟩
  map_isLink := fun _ _ _ hxy ↦ h.isLink_mono hxy
  vertMap_injective _ _ hxy := Subtype.ext (congrArg (fun z : V(G) ↦ z.1) hxy)
  edgeMap_injective _ _ hef := Subtype.ext (congrArg (fun z : E(G) ↦ z.1) hef)

@[simp]
theorem toHom_id (G : Graph V₀ E₀) : (id G).toHom = Hom.id G :=
  rfl

@[simp]
theorem toHom_comp (F : Emb G H) (F' : Emb H K) : (F.comp F').toHom = F.toHom.comp F'.toHom :=
  rfl

@[simp]
theorem id_comp (F : Emb G H) : (id G).comp F = F := by
  apply ext <;> intro <;> rfl

@[simp]
theorem comp_id (F : Emb G H) : F.comp (id H) = F := by
  apply ext <;> intro <;> rfl

theorem comp_assoc (F : Emb G H) (F' : Emb H K) (F'' : Emb K L) :
    (F.comp F').comp F'' = F.comp (F'.comp F'') := by
  apply ext <;> intro <;> rfl

@[simp]
theorem comp_left_inj {F F' : Emb G H} (F'' : Emb H K) : F.comp F'' = F'.comp F'' ↔ F = F' := by
  refine ⟨fun h ↦ ext (fun x ↦ ?_) fun e ↦ ?_, fun h ↦ h ▸ rfl⟩
  · exact F''.vertMap_injective <| congrArg (fun F : Emb G K ↦ F.vertMap x) h
  · exact F''.edgeMap_injective <| congrArg (fun F : Emb G K ↦ F.edgeMap e) h

/-- An embedding reflects links of mapped edges, without being induced. -/
theorem isLink_iff_isLink (F : Emb G H) (e : E(G)) (x y : V(G)) :
    G.IsLink e.1 x.1 y.1 ↔ H.IsLink (F.edgeMap e).1 (F.vertMap x).1 (F.vertMap y).1 :=
  (Hom.isLink_iff_of_injective (F := F.toHom) F.vertMap_injective e x y).symm

/-- The bundled embedding of vertices. -/
def vertEmbedding (F : Emb G H) : V(G) ↪ V(H) where
  toFun := F.vertMap
  inj' := F.vertMap_injective

@[simp]
theorem id_vertMap (G : Graph V₀ E₀) : (id G).vertMap = _root_.id :=
  rfl

@[simp]
theorem comp_vertMap (F : Emb G H) (F' : Emb H K) : (F.comp F').vertMap = F'.vertMap ∘ F.vertMap :=
  rfl

@[grind =]
theorem comp_vertMap_apply (F : Emb G H) (F' : Emb H K) (x : V(G)) :
    (F.comp F').vertMap x = F'.vertMap (F.vertMap x) :=
  rfl

@[simp]
theorem vertEmbedding_id (G : Graph V₀ E₀) : (id G).vertEmbedding = Function.Embedding.refl _ :=
  rfl

@[simp]
theorem vertEmbedding_comp (F : Emb G H) (F' : Emb H K) :
    (F.comp F').vertEmbedding = F.vertEmbedding.trans F'.vertEmbedding :=
  rfl

/-- The bundled embedding of edges. -/
def edgeEmbedding (F : Emb G H) : E(G) ↪ E(H) where
  toFun := F.edgeMap
  inj' := F.edgeMap_injective

@[simp]
theorem id_edgeMap (G : Graph V₀ E₀) : (id G).edgeMap = _root_.id :=
  rfl

@[simp]
theorem comp_edgeMap (F : Emb G H) (F' : Emb H K) : (F.comp F').edgeMap = F'.edgeMap ∘ F.edgeMap :=
  rfl

@[grind =]
theorem comp_edgeMap_apply (F : Emb G H) (F' : Emb H K) (x : E(G)) :
    (F.comp F').edgeMap x = F'.edgeMap (F.edgeMap x) :=
  rfl

@[simp]
theorem edgeEmbedding_id (G : Graph V₀ E₀) : (id G).edgeEmbedding = Function.Embedding.refl _ :=
  rfl

@[simp]
theorem edgeEmbedding_comp (F : Emb G H) (F' : Emb H K) :
    (F.comp F').edgeEmbedding = F.edgeEmbedding.trans F'.edgeEmbedding :=
  rfl

end Emb

@[simp]
lemma coe_ofLe_vertMap {G H : Graph V₀ E₀} (h : H ≤ G) (x : V(H)) :
    ((Emb.ofLe h).vertMap x).1 = x.1 :=
  rfl

@[simp]
lemma coe_ofLe_edgeMap {G H : Graph V₀ E₀} (h : H ≤ G) (e : E(H)) :
    ((Emb.ofLe h).edgeMap e).1 = e.1 :=
  rfl

@[simp]
lemma ofLe_comp_ofLe {G H K : Graph V₀ E₀} (hGH : H ≤ G) (hHK : K ≤ H) :
    (Emb.ofLe hHK).comp (Emb.ofLe hGH) = Emb.ofLe (hHK.trans hGH) := by
  apply Emb.ext <;> intro <;> rfl

@[simp]
theorem Emb.ofLe_refl (G : Graph V₀ E₀) : Emb.ofLe (le_refl G) = Emb.id G := by
  apply Emb.ext <;> intro <;> rfl

namespace Iso

@[ext]
theorem ext {F F' : Iso G H} (hV : ∀ x, F.vertMap x = F'.vertMap x)
    (hE : ∀ e, F.edgeMap e = F'.edgeMap e) : F = F' := by
  have hVInv : F.invVertMap = F'.invVertMap := by
    funext y
    apply F.vertMap_injective
    calc
      F.vertMap (F.invVertMap y) = y := F.vertMap_rightInverse y
      _ = F'.vertMap (F'.invVertMap y) := (F'.vertMap_rightInverse y).symm
      _ = F.vertMap (F'.invVertMap y) := (hV _).symm
  have hEInv : F.invEdgeMap = F'.invEdgeMap := by
    funext e
    apply F.edgeMap_injective
    calc
      F.edgeMap (F.invEdgeMap e) = e := F.edgeMap_rightInverse e
      _ = F'.edgeMap (F'.invEdgeMap e) := (F'.edgeMap_rightInverse e).symm
      _ = F.edgeMap (F'.invEdgeMap e) := (hE _).symm
  cases F
  cases F'
  cases Emb.ext hV hE
  cases hVInv
  cases hEInv
  rfl

theorem toEmb_injective : Injective (toEmb : Iso G H → Emb G H) := by
  intro F F' h
  apply ext (fun x ↦ ?_) (fun e ↦ ?_)
  · exact congrArg (fun F : Emb G H ↦ F.vertMap x) h
  · exact congrArg (fun F : Emb G H ↦ F.edgeMap e) h

theorem toHom_injective : Injective (fun F : Iso G H ↦ F.toHom) := by
  intro F F' h
  apply ext (fun x ↦ ?_) (fun e ↦ ?_)
  · exact congrArg (fun F : Hom G H ↦ F.vertMap x) h
  · exact congrArg (fun F : Hom G H ↦ F.edgeMap e) h

/-- Construct an isomorphism from carrier equivalences and forward link preservation. -/
def ofEquivs (v : V(G) ≃ V(H)) (e : E(G) ≃ E(H)) (h : ∀ ⦃f : E(G)⦄ ⦃x y : V(G)⦄,
    G.IsLink f.1 x.1 y.1 → H.IsLink (e f).1 (v x).1 (v y).1) : Iso G H where
  toEmb := Emb.ofEmbeddings v.toEmbedding e.toEmbedding h
  invVertMap := v.symm
  invEdgeMap := e.symm
  vertMap_leftInverse := v.symm_apply_apply
  vertMap_rightInverse := v.apply_symm_apply
  edgeMap_leftInverse := e.symm_apply_apply
  edgeMap_rightInverse := e.apply_symm_apply

/-- The identity isomorphism. -/
def id (G : Graph V₀ E₀) : Iso G G where
  toEmb := Emb.id G
  invVertMap := _root_.id
  invEdgeMap := _root_.id
  vertMap_leftInverse := by intro x; rfl
  vertMap_rightInverse := by intro x; rfl
  edgeMap_leftInverse := by intro e; rfl
  edgeMap_rightInverse := by intro e; rfl

/-- Inverse maps preserve links, by reflection and the inverse laws. -/
theorem invMap_isLink (F : Iso G H) ⦃e : E(H)⦄ ⦃x y : V(H)⦄ (h : H.IsLink e.1 x.1 y.1) :
    G.IsLink (F.invEdgeMap e).1 (F.invVertMap x).1 (F.invVertMap y).1 := by
  apply (Hom.isLink_iff_of_injective (F := F.toHom) F.vertMap_injective (F.invEdgeMap e)
    (F.invVertMap x) (F.invVertMap y)).1
  simpa only [F.edgeMap_rightInverse e, F.vertMap_rightInverse x, F.vertMap_rightInverse y] using h

/-- Reverse an isomorphism using its stored inverse functions. -/
def symm (F : Iso G H) : Iso H G where
  vertMap := F.invVertMap
  edgeMap := F.invEdgeMap
  map_isLink := F.invMap_isLink
  vertMap_injective x y hxy := by
    rw [(F.vertMap_rightInverse x).symm, congrArg F.vertMap hxy, F.vertMap_rightInverse y]
  edgeMap_injective e f hef := by
    rw [(F.edgeMap_rightInverse e).symm, congrArg F.edgeMap hef, F.edgeMap_rightInverse f]
  invVertMap := F.vertMap
  invEdgeMap := F.edgeMap
  vertMap_leftInverse := F.vertMap_rightInverse
  vertMap_rightInverse := F.vertMap_leftInverse
  edgeMap_leftInverse := F.edgeMap_rightInverse
  edgeMap_rightInverse := F.edgeMap_leftInverse

/-- Compose forward maps and compose inverse maps in the reverse order. -/
def comp (F : Iso G H) (F' : Iso H K) : Iso G K where
  toEmb := F.toEmb.comp F'.toEmb
  invVertMap := F.invVertMap ∘ F'.invVertMap
  invEdgeMap := F.invEdgeMap ∘ F'.invEdgeMap
  vertMap_leftInverse x := by
    change F.invVertMap (F'.invVertMap (F'.vertMap (F.vertMap x))) = x
    rw [F'.vertMap_leftInverse, F.vertMap_leftInverse]
  vertMap_rightInverse x := by
    change F'.vertMap (F.vertMap (F.invVertMap (F'.invVertMap x))) = x
    rw [F.vertMap_rightInverse, F'.vertMap_rightInverse]
  edgeMap_leftInverse e := by
    change F.invEdgeMap (F'.invEdgeMap (F'.edgeMap (F.edgeMap e))) = e
    rw [F'.edgeMap_leftInverse, F.edgeMap_leftInverse]
  edgeMap_rightInverse e := by
    change F'.edgeMap (F.edgeMap (F.invEdgeMap (F'.invEdgeMap e))) = e
    rw [F.edgeMap_rightInverse, F'.edgeMap_rightInverse]

/-- The vertex equivalence with the specified inverse. -/
@[irw_equiv]
def vertEquiv (F : Iso G H) : V(G) ≃ V(H) where
  toFun := F.vertMap
  invFun := F.invVertMap
  left_inv := F.vertMap_leftInverse
  right_inv := F.vertMap_rightInverse

@[simp, grind =]
theorem vertMap_comp (F : Iso G H) (F' : Iso H K) (x : V(G)) :
    (F.comp F').vertMap x = F'.vertMap (F.vertMap x) :=
  rfl

@[simp]
theorem vertEquiv_id (G : Graph V₀ E₀) : (id G).vertEquiv = Equiv.refl _ :=
  rfl

@[simp]
theorem vertEquiv_comp (F : Iso G H) (F' : Iso H K) :
    (F.comp F').vertEquiv = F.vertEquiv.trans F'.vertEquiv :=
  rfl

@[simp]
theorem vertEquiv_symm (F : Iso G H) : F.symm.vertEquiv = F.vertEquiv.symm :=
  rfl

/-- The edge equivalence with the specified inverse. -/
@[irw_equiv]
def edgeEquiv (F : Iso G H) : E(G) ≃ E(H) where
  toFun := F.edgeMap
  invFun := F.invEdgeMap
  left_inv := F.edgeMap_leftInverse
  right_inv := F.edgeMap_rightInverse

@[simp, grind =] theorem edgeMap_comp (F : Iso G H) (F' : Iso H K) (x : E(G)) :
    (F.comp F').edgeMap x = F'.edgeMap (F.edgeMap x) := by rfl

@[simp] theorem edgeEquiv_id (G : Graph V₀ E₀) : (id G).edgeEquiv = Equiv.refl _ := by rfl

@[simp] theorem edgeEquiv_comp (F : Iso G H) (F' : Iso H K) :
    (F.comp F').edgeEquiv = F.edgeEquiv.trans F'.edgeEquiv := by rfl

@[simp] theorem edgeEquiv_symm (F : Iso G H) : F.symm.edgeEquiv = F.edgeEquiv.symm := by rfl

/-- A bijective homomorphism determines an isomorphism. Inverses here use classical choice. -/
noncomputable def ofBijective (F : Hom G H) (hv : Bijective F.vertMap)
    (he : Bijective F.edgeMap) : Iso G H :=
  ofEquivs (Equiv.ofBijective F.vertMap hv) (Equiv.ofBijective F.edgeMap he) F.map_isLink

@[simp] theorem toEmb_id (G : Graph V₀ E₀) : (id G).toEmb = Emb.id G :=
  rfl

@[simp] theorem toHom_id (G : Graph V₀ E₀) : (id G).toHom = Hom.id G :=
  rfl

@[simp]
theorem toEmb_comp (F : Iso G H) (F' : Iso H K) : (F.comp F').toEmb = F.toEmb.comp F'.toEmb :=
  rfl

@[simp] theorem toHom_comp (F : Iso G H) (F' : Iso H K) :
    (F.comp F').toHom = F.toHom.comp F'.toHom :=
  rfl

@[simp] theorem id_comp (F : Iso G H) : (id G).comp F = F := by
  apply ext <;> intro <;> rfl

@[simp] theorem comp_id (F : Iso G H) : F.comp (id H) = F := by
  apply ext <;> intro <;> rfl

theorem comp_assoc (F : Iso G H) (F' : Iso H K) (F'' : Iso K L) :
    (F.comp F').comp F'' = F.comp (F'.comp F'') := by
  apply ext <;> intro <;> rfl

@[simp] theorem symm_symm (F : Iso G H) : F.symm.symm = F := by
  apply ext <;> intro <;> rfl

@[simp] theorem symm_id (G : Graph V₀ E₀) : (id G).symm = id G := by
  apply ext <;> intro <;> rfl

@[simp] theorem symm_comp (F : Iso G H) : F.symm.comp F = id H := by
  apply ext (fun x ↦ ?_) (fun e ↦ ?_)
  · exact F.vertMap_rightInverse x
  · exact F.edgeMap_rightInverse e

@[simp] theorem comp_symm (F : Iso G H) : F.comp F.symm = id G := by
  apply ext (fun x ↦ ?_) (fun e ↦ ?_)
  · exact F.vertMap_leftInverse x
  · exact F.edgeMap_leftInverse e

@[simp] theorem comp_symm_eq (F : Iso G H) (F' : Iso H K) :
    (F.comp F').symm = F'.symm.comp F.symm := by
  apply ext <;> intro <;> rfl

@[simp] theorem comp_left_inj {F F' : Iso G H} (F'' : Iso H K) :
    F.comp F'' = F'.comp F'' ↔ F = F' := by
  constructor
  · intro h
    apply ext
    · intro x
      apply F''.vertMap_injective
      exact congrArg (fun F : Iso G K ↦ F.vertMap x) h
    · intro e
      apply F''.edgeMap_injective
      exact congrArg (fun F : Iso G K ↦ F.edgeMap e) h
  · intro h
    cases h
    rfl

@[simp] theorem comp_right_inj (F : Iso G H) {F' F'' : Iso H K} :
    F.comp F' = F.comp F'' ↔ F' = F'' := by
  constructor
  · intro h
    apply ext
    · intro y
      obtain ⟨x, rfl⟩ := F.vertEquiv.surjective y
      exact congrArg (fun F' : Iso G K ↦ F'.vertMap x) h
    · intro e
      obtain ⟨e', rfl⟩ := F.edgeEquiv.surjective e
      exact congrArg (fun F' : Iso G K ↦ F'.edgeMap e') h
  · intro h
    cases h
    rfl

/-- Surjectivity on edges upgrades link reflection to adjacency reflection. -/
@[simp] theorem adj_vertMap (F : Iso G H) (x y : V(G)) :
    G.Adj x.1 y.1 ↔ H.Adj (F.vertMap x).1 (F.vertMap y).1 :=
  Hom.adj_iff_of_injective_of_surjective F.vertMap_injective F.edgeEquiv.surjective x y

end Iso

/-- Isomorphism of graphs, allowing different ambient vertex and edge types. -/
def IsIsoTo (G : Graph V₀ E₀) (H : Graph V₁ E₁) : Prop := Nonempty (Iso G H)

@[refl]
lemma IsIsoTo.refl (G : Graph V₀ E₀) : G.IsIsoTo G := ⟨Iso.id G⟩

@[symm]
lemma IsIsoTo.symm (h : G.IsIsoTo H) : H.IsIsoTo G := ⟨h.some.symm⟩

lemma IsIsoTo.trans (h : G.IsIsoTo H) (h' : H.IsIsoTo K) : G.IsIsoTo K :=
  ⟨h.some.comp h'.some⟩

lemma IsIsoTo.vertexSet_encard_eq (h : G.IsIsoTo H) : V(G).encard = V(H).encard :=
  h.some.vertEmbedding.encard_le.antisymm h.some.symm.vertEmbedding.encard_le

lemma IsIsoTo.edgeSet_encard_eq (h : G.IsIsoTo H) : E(G).encard = E(H).encard :=
  h.some.edgeEmbedding.encard_le.antisymm h.some.symm.edgeEmbedding.encard_le

end Graph
