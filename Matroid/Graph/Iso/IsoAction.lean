/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Matroid.Graph.Iso.Hom

/-!
# The action of graph isomorphisms on graph-dependent types

`IsoAction F` says how a graph isomorphism transports elements of `F G` to elements of `F H`,
with the identity and composition laws expected of a groupoid action.

There is deliberately no `Family`, `TypeFamily`, or `Property` abbreviation in the public interface.
Users write the Lean expression they mean, for example

```lean
IsoAction (fun G ↦ Set V(G))
Invariant (fun G ↦ 3 ≤ V(G).encard)
```

and Lean elaborates the carrier universes from context.  A local variable whose type spells out the
full graph-family Pi type is still monomorphic in its universe parameters, exactly like every other
local Lean term; universe polymorphism is recovered at declarations by elaborating each occurrence
at the required universes.

`IsoAction` itself intentionally stays *within one carrier-universe pair*.  Cross-universe
transport is the job of `IsoTransport` in `IsoTransport.lean`.
-/

@[expose] public section

open Set Function

namespace Graph

universe uV₁ uE₁ uV₂ uE₂ uV₃ uE₃ uO uO'

/-! ### `Iso` coherence

These lemmas are stated with independent carrier universes.  `Iso` itself is heterogeneous, and
`IsoTransport` needs composition lemmas where the source, middle and target graphs genuinely live
in different universes.
-/

@[ext] theorem Iso.ext
    {V : Type uV₁} {E : Type uE₁} {V' : Type uV₂} {E' : Type uE₂}
    {G : Graph V E} {H : Graph V' E'} {F F' : Iso G H}
    (hV : F.vertMap = F'.vertMap) (hE : F.edgeMap = F'.edgeMap) : F = F' := by
  cases F; cases F'; subst hV; subst hE; rfl

@[simp] theorem Iso.vertexEquiv_id {V : Type uV₁} {E : Type uE₁} (G : Graph V E)
    (x : V(G)) : (Iso.id G).vertexEquiv x = x :=
  Subtype.ext <| Option.mem_unique ((Iso.id G).mem_vertMap_vertexEquiv x) <| by
    simp [Iso.id, PEquiv.ofSet, x.2]

@[simp] theorem Iso.edgeEquiv_id {V : Type uV₁} {E : Type uE₁} (G : Graph V E)
    (e : E(G)) : (Iso.id G).edgeEquiv e = e :=
  Subtype.ext <| Option.mem_unique ((Iso.id G).mem_edgeMap_edgeEquiv e) <| by
    simp [Iso.id, PEquiv.ofSet, e.2]

@[simp] theorem Iso.vertexEquiv_comp
    {V : Type uV₁} {E : Type uE₁} {V' : Type uV₂} {E' : Type uE₂}
    {V'' : Type uV₃} {E'' : Type uE₃}
    {G : Graph V E} {H : Graph V' E'} {K : Graph V'' E''}
    (F : Iso G H) (F' : Iso H K) (x : V(G)) :
    (F.comp F').vertexEquiv x = F'.vertexEquiv (F.vertexEquiv x) :=
  Subtype.ext <| Option.mem_unique ((F.comp F').mem_vertMap_vertexEquiv x) <|
    (F.vertMap.mem_trans F'.vertMap _ _).2
      ⟨_, F.mem_vertMap_vertexEquiv x, F'.mem_vertMap_vertexEquiv _⟩

@[simp] theorem Iso.edgeEquiv_comp
    {V : Type uV₁} {E : Type uE₁} {V' : Type uV₂} {E' : Type uE₂}
    {V'' : Type uV₃} {E'' : Type uE₃}
    {G : Graph V E} {H : Graph V' E'} {K : Graph V'' E''}
    (F : Iso G H) (F' : Iso H K) (e : E(G)) :
    (F.comp F').edgeEquiv e = F'.edgeEquiv (F.edgeEquiv e) :=
  Subtype.ext <| Option.mem_unique ((F.comp F').mem_edgeMap_edgeEquiv e) <|
    (F.edgeMap.mem_trans F'.edgeMap _ _).2
      ⟨_, F.mem_edgeMap_edgeEquiv e, F'.mem_edgeMap_edgeEquiv _⟩

@[simp] theorem Iso.vertexEquiv_symm
    {V : Type uV₁} {E : Type uE₁} {V' : Type uV₂} {E' : Type uE₂}
    {G : Graph V E} {H : Graph V' E'} (F : Iso G H) :
    F.symm.vertexEquiv = F.vertexEquiv.symm :=
  Equiv.ext fun y ↦ F.vertexEquiv.eq_symm_apply.symm.mp <|
    Subtype.ext <| Option.mem_unique (F.mem_vertMap_vertexEquiv _) <|
      F.vertMap.mem_iff_mem.mp <| by
        simpa [Iso.symm_vertMap] using F.symm.mem_vertMap_vertexEquiv y

@[simp] theorem Iso.edgeEquiv_symm
    {V : Type uV₁} {E : Type uE₁} {V' : Type uV₂} {E' : Type uE₂}
    {G : Graph V E} {H : Graph V' E'} (F : Iso G H) :
    F.symm.edgeEquiv = F.edgeEquiv.symm :=
  Equiv.ext fun f ↦ F.edgeEquiv.eq_symm_apply.symm.mp <|
    Subtype.ext <| Option.mem_unique (F.mem_edgeMap_edgeEquiv _) <|
      F.edgeMap.mem_iff_mem.mp <| by
        simpa [Iso.symm_edgeMap] using F.symm.mem_edgeMap_edgeEquiv f

theorem Iso.comp_symm
    {V : Type uV₁} {E : Type uE₁} {V' : Type uV₂} {E' : Type uE₂}
    {G : Graph V E} {H : Graph V' E'} (i : Iso G H) : i.comp i.symm = Iso.id G := by
  refine Iso.ext ?_ ?_
  · ext x
    simp [Iso.comp_vertMap, Iso.symm_vertMap, Iso.id, PEquiv.self_trans_symm, PEquiv.ofSet,
      i.vertMap_isSome_iff]
  · ext e
    simp [Iso.comp_edgeMap, Iso.symm_edgeMap, Iso.id, PEquiv.self_trans_symm, PEquiv.ofSet,
      i.edgeMap_isSome_iff]

theorem Iso.symm_comp
    {V : Type uV₁} {E : Type uE₁} {V' : Type uV₂} {E' : Type uE₂}
    {G : Graph V E} {H : Graph V' E'} (i : Iso G H) : i.symm.comp i = Iso.id H := by
  refine Iso.ext ?_ ?_
  · ext x
    simp [Iso.comp_vertMap, Iso.symm_vertMap, Iso.id, PEquiv.symm_trans_self, PEquiv.ofSet,
      i.invVertMap_isSome_iff]
  · ext e
    simp [Iso.comp_edgeMap, Iso.symm_edgeMap, Iso.id, PEquiv.symm_trans_self, PEquiv.ofSet,
      i.invEdgeMap_isSome_iff]

/-! ### Actions -/

/-- How graph isomorphisms act on a graph-dependent Lean expression, within fixed vertex- and
edge-carrier universes. -/
class IsoAction (F : {V : Type uV₁} → {E : Type uE₁} → Graph V E → Sort uO) where
  /-- Transport along an isomorphism. -/
  map : {V V' : Type uV₁} → {E E' : Type uE₁} → {G : Graph V E} → {H : Graph V' E'} →
    Iso G H → F G ≃ F H
  /-- The identity isomorphism acts trivially. -/
  map_id : ∀ {V : Type uV₁} {E : Type uE₁} (G : Graph V E) (x : F G),
    map (Iso.id G) x = x
  /-- Transport respects composition. -/
  map_comp : ∀ {V V' V'' : Type uV₁} {E E' E'' : Type uE₁}
    {G : Graph V E} {H : Graph V' E'} {K : Graph V'' E''}
    (i : Iso G H) (j : Iso H K) (x : F G), map (i.comp j) x = map j (map i x)

namespace IsoAction

/-- The equivalence of proof types corresponding to an iff. -/
def equivOfIff {P Q : Prop} (h : P ↔ Q) : P ≃ Q where
  toFun := h.mp
  invFun := h.mpr
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

variable {F : {V : Type uV₁} → {E : Type uE₁} → Graph V E → Sort uO} [IsoAction F]

/-- Transport along the inverse isomorphism is the inverse transport. -/
theorem map_symm {V E V' E' : Type _} {G : Graph V E} {H : Graph V' E'} (i : Iso G H) :
    map (F := F) i.symm = (map (F := F) i).symm :=
  Equiv.ext fun y ↦ (map (F := F) i).eq_symm_apply.symm.mp <| by
    rw [← map_comp, i.symm_comp, map_id]

@[simp] theorem map_symm_apply {V E V' E' : Type _} {G : Graph V E} {H : Graph V' E'} (i : Iso G H)
    (y : F H) : map (F := F) i.symm y = (map (F := F) i).symm y := by rw [map_symm]

theorem map_id_eq_refl {V E : Type _} (G : Graph V E) : map (Iso.id G) = Equiv.refl (F G) :=
  Equiv.ext (map_id G)

theorem map_comp_eq_trans {V V' V'' : Type uV₁} {E E' E'' : Type uE₁} {G : Graph V E}
    {H : Graph V' E'} {K : Graph V'' E''} (i : Iso G H) (j : Iso H K) :
    map (F := F) (i.comp j) = (map (F := F) i).trans (map (F := F) j) :=
  Equiv.ext (map_comp i j)

/-- Build an action on a proposition-valued expression from preservation as an iff.
The coherence laws are automatic by proof irrelevance. -/
@[instance_reducible]
def of_iff (P : {V : Type uV₁} → {E : Type uE₁} → Graph V E → Prop)
    (h : ∀ {V V' : Type uV₁} {E E' : Type uE₁} {G : Graph V E} {H : Graph V' E'},
      Iso G H → (P G ↔ P H)) : IsoAction P where
  map i := IsoAction.equivOfIff (h i)
  map_id _ _ := Subsingleton.elim _ _
  map_comp _ _ _ := Subsingleton.elim _ _

/-- An action on a proposition-valued family supplies the corresponding iff. -/
theorem iff_of_iso
    {P : {V : Type uV₁} → {E : Type uE₁} → Graph V E → Prop} [IsoAction P]
    {V : Type uV₁} {E : Type uE₁} {V' : Type uV₁} {E' : Type uE₁}
    {G : Graph V E} {H : Graph V' E'} (i : Iso G H) : P G ↔ P H :=
  ⟨IsoAction.map (F := P) i, (IsoAction.map (F := P) i).symm⟩

end IsoAction

/-! ### Objects equal up to relabelling -/

/-- `x : F G` and `y : F H` name the same object up to relabelling. -/
def IsoRelated {F : {V : Type uV₁} → {E : Type uE₁} → Graph V E → Sort uO} [IsoAction F]
    {V : Type uV₁} {E : Type uE₁} {V' : Type uV₁} {E' : Type uE₁}
    {G : Graph V E} {H : Graph V' E'} (x : F G) (y : F H) : Prop :=
  ∃ i : Iso G H, IsoAction.map i x = y

namespace IsoRelated

variable {F : {V : Type uV₁} → {E : Type uE₁} → Graph V E → Sort uO} [IsoAction F]
  {V : Type uV₁} {E : Type uE₁} {V' : Type uV₁} {E' : Type uE₁} {V'' : Type uV₁} {E'' : Type uE₁}
  {G : Graph V E} {H : Graph V' E'} {K : Graph V'' E''}

@[refl] theorem refl (x : F G) : IsoRelated x x :=
  ⟨Iso.id G, IsoAction.map_id G x⟩

@[symm] theorem symm {x : F G} {y : F H} (h : IsoRelated x y) : IsoRelated y x := by
  obtain ⟨i, rfl⟩ := h
  exact ⟨i.symm, by rw [IsoAction.map_symm, Equiv.symm_apply_apply]⟩

theorem trans {x : F G} {y : F H} {z : F K} (h : IsoRelated x y) (h' : IsoRelated y z) :
    IsoRelated x z := by
  obtain ⟨i, rfl⟩ := h
  obtain ⟨j, rfl⟩ := h'
  exact ⟨i.comp j, IsoAction.map_comp i j x⟩

end IsoRelated

/-! ### Structural instances -/

/-- A graph-independent expression is transported trivially. -/
instance instConst (R : Sort _) : IsoAction (fun {_ _} _ ↦ R) where
  map _ := Equiv.refl R
  map_id _ _ := rfl
  map_comp _ _ _ := rfl

/-- The active vertex set. -/
instance instVertices : IsoAction (fun {V E} (G : Graph V E) ↦ V(G)) where
  map := Iso.vertexEquiv
  map_id := Iso.vertexEquiv_id
  map_comp := Iso.vertexEquiv_comp

/-- The active edge set. -/
instance instEdges : IsoAction (fun {V E} (G : Graph V E) ↦ E(G)) where
  map := Iso.edgeEquiv
  map_id := Iso.edgeEquiv_id
  map_comp := Iso.edgeEquiv_comp

/-- Function spaces are transported by conjugation. -/
instance instArrow (F : {V : Type uV₁} → {E : Type uE₁} → Graph V E → Sort uO)
    (K : {V : Type uV₁} → {E : Type uE₁} → Graph V E → Sort uO') [IsoAction F] [IsoAction K] :
    IsoAction (fun G ↦ F G → K G) where
  map i :=
    { toFun := fun f y ↦ IsoAction.map i (f ((IsoAction.map (F := F) i).symm y))
      invFun := fun g x ↦ (IsoAction.map (F := K) i).symm (g (IsoAction.map i x))
      left_inv := by intro f; funext x; simp
      right_inv := by intro g; funext y; simp }
  map_id := fun G f ↦ by
    change (fun y ↦ IsoAction.map (Iso.id G)
      (f ((IsoAction.map (F := F) (Iso.id G)).symm y))) = f
    rw [IsoAction.map_id_eq_refl (F := F), IsoAction.map_id_eq_refl (F := K)]
    rfl
  map_comp := fun i j f ↦ by
    change (fun y ↦ IsoAction.map (i.comp j)
        (f ((IsoAction.map (F := F) (i.comp j)).symm y))) =
      (fun y ↦ IsoAction.map j
        (IsoAction.map i (f ((IsoAction.map (F := F) i).symm
          ((IsoAction.map (F := F) j).symm y)))))
    rw [IsoAction.map_comp_eq_trans (F := F), IsoAction.map_comp_eq_trans (F := K)]
    rfl

instance instProd (F : {V : Type uV₁} → {E : Type uE₁} → Graph V E → Type uO)
    (K : {V : Type uV₁} → {E : Type uE₁} → Graph V E → Type uO') [IsoAction F] [IsoAction K] :
    IsoAction (fun G ↦ F G × K G) where
  map i := Equiv.prodCongr (IsoAction.map i) (IsoAction.map i)
  map_id := fun G x ↦ by
    rw [IsoAction.map_id_eq_refl (F := F), IsoAction.map_id_eq_refl (F := K)]
    rfl
  map_comp := fun i j x ↦ by
    rw [IsoAction.map_comp_eq_trans (F := F), IsoAction.map_comp_eq_trans (F := K)]
    rfl

instance instSum (F : {V : Type uV₁} → {E : Type uE₁} → Graph V E → Type uO)
    (K : {V : Type uV₁} → {E : Type uE₁} → Graph V E → Type uO') [IsoAction F] [IsoAction K] :
    IsoAction (fun G ↦ F G ⊕ K G) where
  map i := Equiv.sumCongr (IsoAction.map i) (IsoAction.map i)
  map_id := fun G x ↦ by
    rw [IsoAction.map_id_eq_refl (F := F), IsoAction.map_id_eq_refl (F := K)]
    cases x <;> rfl
  map_comp := fun i j x ↦ by
    rw [IsoAction.map_comp_eq_trans (F := F), IsoAction.map_comp_eq_trans (F := K)]
    cases x <;> rfl

instance instOption (F : {V : Type uV₁} → {E : Type uE₁} → Graph V E → Type uO) [IsoAction F] :
    IsoAction (fun G ↦ Option (F G)) where
  map i := Equiv.optionCongr (IsoAction.map i)
  map_id := fun G x ↦ by
    rw [IsoAction.map_id_eq_refl (F := F)]
    cases x <;> rfl
  map_comp := fun i j x ↦ by
    rw [IsoAction.map_comp_eq_trans (F := F)]
    cases x <;> rfl

instance instSet (F : {V : Type uV₁} → {E : Type uE₁} → Graph V E → Type uO) [IsoAction F] :
    IsoAction (fun G ↦ Set (F G)) where
  map i := Equiv.Set.congr (IsoAction.map i)
  map_id := fun G s ↦ by
    rw [IsoAction.map_id_eq_refl (F := F)]
    ext x
    simp [Equiv.Set.congr]
  map_comp := fun i j s ↦ by
    rw [IsoAction.map_comp_eq_trans (F := F)]
    exact (Set.image_image (IsoAction.map (F := F) j) (IsoAction.map (F := F) i) s).symm

end Graph
