/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Matroid.Graph.Iso.Hom
public import Mathlib.Data.PFun

/-!
# Copying a graph onto other carriers

`G.relabel fv fe` is the isomorphic copy of `G` obtained by pushing the vertex and edge data
forward along two embeddings, and `G.relabelIso` is the isomorphism onto it. `FitsOn` names the
hypothesis that the two embeddings exist.

**The embeddings are from the active sets, not from the ambient types.** A graph may have a tiny
vertex set inside an enormous ambient type, so `V(G) ↪ V'` is the right hypothesis and `V ↪ V'`
would be far too strong.

**The edge carrier is relabelled too, not only the vertices.** One might expect to keep `E` fixed
and move the vertices alone. That would be a mistake for the intended use: a proof that works on a
canonical carrier needs room to *add* an edge, so the edge type has to have space to spare as
well. `relabel` leaves exactly that, since only the images of the two embeddings are used.

This file is independent of `IsoAction.lean` and `Invariant.lean`: relabelling a graph is useful
without the invariance machinery, and vice versa. The theorems that combine them are in
`Transfer.lean`.
-/

@[expose] public section

open Set Function

namespace Graph

universe uV uE uV' uE'

variable {V : Type uV} {E : Type uE} {V' : Type uV'} {E' : Type uE'} {G : Graph V E}

/-! ### For Mathlib

Ways to regard an embedding defined on a subset as a partial map on the ambient type; all belong
in `ForMathlib`, and are here while this file is the only consumer. `PEquiv.ofEmbedding` and its
three characterisation lemmas are what `relabelIso` is built from; `toPFun` and `invPFun` have no
consumer yet. -/

/-- An embedding defined on a subset, as a partial function on the ambient type. -/
noncomputable def _root_.Function.Embedding.toPFun {α β : Type*} {s : Set α} (f : s ↪ β) :
    α →. β := fun a => ⟨a ∈ s, fun h => f ⟨a, h⟩⟩

/-- The partial inverse of an embedding defined on a subset, defined exactly on its range. -/
noncomputable def _root_.Function.Embedding.invPFun {α β : Type*} {s : Set α} (f : s ↪ β) :
    β →. α :=
  fun b => ⟨b ∈ Set.range f, fun h => ((Equiv.ofInjective f f.injective).symm ⟨b, h⟩ : s)⟩

/-- An embedding defined on a subset, as a partial equivalence. -/
noncomputable def _root_.PEquiv.ofEmbedding {α β : Type*} {s : Set α} (f : s ↪ β) : α ≃. β := by
  classical
  exact
    { toFun := fun a => if h : a ∈ s then some (f ⟨a, h⟩) else none
      invFun := fun b =>
        if h : b ∈ Set.range f then some (((Equiv.ofInjective f f.injective).symm ⟨b, h⟩ : s) : α)
        else none
      inv a b:= by
        by_cases ha : a ∈ s
        · by_cases hb : b ∈ Set.range (f : s → β)
          · simp only [ha, hb, ↓reduceDIte, Option.some.injEq]
            constructor
            · rintro rfl
              simpa using Equiv.apply_ofInjective_symm (f := (f : s → β)) f.injective ⟨b, hb⟩
            · rintro rfl
              simp
          · simp only [ha, hb, ↓reduceDIte, Option.some.injEq, reduceCtorEq, false_iff]
            exact fun h ↦ hb ⟨⟨a, ha⟩, h⟩
        · by_cases hb : b ∈ Set.range (f : s → β)
          · simp only [ha, hb, ↓reduceDIte, Option.some.injEq, reduceCtorEq, iff_false]
            exact fun h ↦ ha (h ▸ Subtype.coe_prop _)
          · simp [ha, hb] }

/-- The characterisation of `PEquiv.ofEmbedding`: it is defined exactly on `s`, where it is `f`.
Callers should use this rather than unfolding the `dite`s. -/
@[simp] theorem _root_.PEquiv.mem_ofEmbedding_iff {α β : Type*} {s : Set α} (f : s ↪ β) {a : α}
    {b : β} : b ∈ PEquiv.ofEmbedding f a ↔ ∃ h : a ∈ s, f ⟨a, h⟩ = b := by
  classical
  show PEquiv.ofEmbedding f a = some b ↔ _
  by_cases ha : a ∈ s <;> simp [PEquiv.ofEmbedding, ha]

@[simp] theorem _root_.PEquiv.ofEmbedding_isSome_iff {α β : Type*} {s : Set α} (f : s ↪ β)
    (a : α) : (PEquiv.ofEmbedding f a).isSome ↔ a ∈ s := by
  simp only [Option.isSome_iff_exists, ← Option.mem_def, PEquiv.mem_ofEmbedding_iff]
  exact ⟨fun ⟨_, h, _⟩ ↦ h, fun h ↦ ⟨f ⟨a, h⟩, h, rfl⟩⟩

@[simp] theorem _root_.PEquiv.ofEmbedding_symm_isSome_iff {α β : Type*} {s : Set α} (f : s ↪ β)
    (b : β) : ((PEquiv.ofEmbedding f).symm b).isSome ↔ b ∈ Set.range f := by
  simp only [Option.isSome_iff_exists, ← Option.mem_def, PEquiv.mem_iff_mem,
    PEquiv.mem_ofEmbedding_iff]
  exact ⟨fun ⟨_, h, heq⟩ ↦ ⟨_, heq⟩, fun ⟨x, hx⟩ ↦ ⟨x, x.2, by simpa using hx⟩⟩

/-! ### The copy -/

/-- The copy of `G` on the carriers `V'`, `E'` determined by two embeddings of its active sets.
Only the images of `V(G)` and `E(G)` are used; the rest of the target carriers stays unused, which
is exactly what makes fresh labels available there. -/
noncomputable def relabel (G : Graph V E) (fv : V(G) ↪ V') (fe : E(G) ↪ E') : Graph V' E' where
  vertexSet := Set.range fv
  edgeSet := Set.range fe
  IsLink e x y := ∃ e' x' y', e = fe e' ∧ x = fv x' ∧ y = fv y' ∧ G.IsLink e' x' y'
  isLink_symm e' := by
    simp only [mem_range, Subtype.exists, exists_and_left, exists_and_right, forall_exists_index]
    rintro e he rfl
    refine ⟨by grind [IsLink.symm]⟩
  eq_or_eq_of_isLink_of_isLink e' u' v' w' x' := by
    simp only [exists_and_left, Subtype.exists, exists_and_right, forall_exists_index, and_imp]
    rintro e he rfl u hu rfl v hv rfl huv f hf hef w hw rfl x hx rfl hwx
    simp only [EmbeddingLike.apply_eq_iff_eq, Subtype.mk.injEq] at hef
    grind [G.eq_or_eq_of_isLink_of_isLink huv (hef ▸ hwx)]
  edge_mem_iff_exists_isLink e' := by
    simp only [mem_range, Subtype.exists, ↓existsAndEq, true_and, exists_and_left, exists_prop,
      exists_and_right]
    grind [G.edge_mem_iff_exists_isLink]

variable (fv : V(G) ↪ V') (fe : E(G) ↪ E')

@[simp] theorem relabel_vertexSet : V(G.relabel fv fe) = Set.range fv := rfl

@[simp] theorem relabel_edgeSet : E(G.relabel fv fe) = Set.range fe := rfl

/-- The characterising property: `relabel` transports links along the embeddings. Callers should
use this rather than unfolding the definition. -/
@[simp] theorem relabel_isLink (e : E(G)) (x y : V(G)) :
    (G.relabel fv fe).IsLink (fe e) (fv x) (fv y) ↔ G.IsLink e x y := by
  refine ⟨fun ⟨e', x', y', he, hx, hy, h⟩ ↦ ?_, fun h ↦ ⟨e, x, y, rfl, rfl, rfl, h⟩⟩
  rwa [fe.injective he, fv.injective hx, fv.injective hy]

@[simp] theorem relabel_adj (x y : V(G)) :
    (G.relabel fv fe).Adj (fv x) (fv y) ↔ G.Adj x y := by
  refine ⟨fun ⟨e', he⟩ ↦ ?_, fun ⟨e, he⟩ ↦ ⟨fe ⟨e, he.edge_mem⟩, ?_⟩⟩
  · obtain ⟨e'', x'', y'', rfl, hx, hy, h⟩ := he
    obtain rfl := fv.injective hx
    obtain rfl := fv.injective hy
    exact ⟨e'', h⟩
  · exact (relabel_isLink fv fe ⟨e, he.edge_mem⟩ x y).2 he

/-- The isomorphism onto the copy. -/
noncomputable def relabelIso (G : Graph V E) (fv : V(G) ↪ V') (fe : E(G) ↪ E') :
    Iso G (G.relabel fv fe) where
  vertMap := PEquiv.ofEmbedding fv
  vertMap_isSome_iff x := by simp
  invVertMap_isSome_iff x := by simp
  edgeMap := PEquiv.ofEmbedding fe
  edgeMap_isSome_iff e := by simp
  invEdgeMap_isSome_iff e := by simp
  map_isLink := by
    rintro e x y e' x' y' h he hx hy
    rw [PEquiv.mem_ofEmbedding_iff] at he hx hy
    obtain ⟨he', rfl⟩ := he
    obtain ⟨hx', rfl⟩ := hx
    obtain ⟨hy', rfl⟩ := hy
    exact (relabel_isLink fv fe ⟨e, he'⟩ ⟨x, hx'⟩ ⟨y, hy'⟩).2 h
  invMap_isLink := by
    rintro e' x' y' e x y ⟨e'', x'', y'', rfl, rfl, rfl, h⟩ he hx hy
    rw [PEquiv.mem_iff_mem, PEquiv.mem_ofEmbedding_iff] at he hx hy
    obtain ⟨he', hee⟩ := he
    obtain ⟨hx', hxx⟩ := hx
    obtain ⟨hy', hyy⟩ := hy
    obtain rfl := fe.injective hee
    obtain rfl := fv.injective hxx
    obtain rfl := fv.injective hyy
    exact h

/-! ### `FitsOn` -/

/-- `G` can be represented on the carriers `V'`, `E'`: its active sets embed into them.

Stated with embeddings rather than cardinals because that is the form both the construction and
the callers want; `fitsOn_iff_cardinal` is the bridge for "sufficiently large" statements. -/
def FitsOn (G : Graph V E) (V' : Type uV') (E' : Type uE') : Prop :=
  Nonempty (V(G) ↪ V') ∧ Nonempty (E(G) ↪ E')

/-- A copy of `G` on given carriers, packaged with the isomorphism onto it. -/
structure CopyOn (G : Graph V E) (V' : Type uV') (E' : Type uE') where
  /-- The copy. -/
  graph : Graph V' E'
  /-- The isomorphism onto it. -/
  iso : Iso G graph

/-- Every graph that fits on some carriers has a copy there. -/
noncomputable def FitsOn.copyOn (h : G.FitsOn V' E') : G.CopyOn V' E' where
  graph := G.relabel h.1.some h.2.some
  iso := G.relabelIso h.1.some h.2.some

theorem fitsOn_iff_exists_iso : G.FitsOn V' E' ↔ ∃ H : Graph V' E', Nonempty (Iso G H) :=
  ⟨fun h ↦ ⟨h.copyOn.graph, ⟨h.copyOn.iso⟩⟩, fun ⟨_, ⟨i⟩⟩ ↦
    ⟨⟨i.vertMapEmbedding.trans (Function.Embedding.subtype _)⟩,
      ⟨i.edgeMapEmbedding.trans (Function.Embedding.subtype _)⟩⟩⟩

theorem fitsOn_iff_cardinal : G.FitsOn V' E' ↔
    Cardinal.lift.{uV'} (Cardinal.mk V(G)) ≤ Cardinal.lift.{uV} (Cardinal.mk V') ∧
    Cardinal.lift.{uE'} (Cardinal.mk E(G)) ≤ Cardinal.lift.{uE} (Cardinal.mk E') :=
  and_congr Cardinal.lift_mk_le'.symm Cardinal.lift_mk_le'.symm

end Graph
