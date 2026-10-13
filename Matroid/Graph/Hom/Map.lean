module

public import Matroid.Graph.Hom.Factorization
public import Matroid.Graph.Map

/-!
# Homomorphisms between vertex-mapped graphs

`toMap` is the canonical homomorphism to a vertex-mapped graph. A factorization on vertices
induces `mapHom`; mutual factorization induces `mapIso`. Both constructions specialize general
homomorphism factorization and fix every edge label. No hypothesis is imposed outside
`V(G)`.
-/

@[expose] public section

open Function Set

namespace Graph

variable {α β γ δ ε : Type*} {G : Graph α β} {u : α}

/-- The canonical homomorphism to a vertex-mapped graph. -/
def toMap (G : Graph α β) (f : α → γ) : Hom G (f ''ᴳ G) where
  vertMap := Set.imageFactorization f V(G)
  edgeMap := id
  map_isLink _ _ _ h := h.map f

@[simp]
theorem toMap_vertMap_val (f : α → γ) (x : V(G)) : ((G.toMap f).vertMap x).1 = f x.1 := by
  rfl

@[simp]
theorem toMap_edgeMap (f : α → γ) (e : E(G)) : (G.toMap f).edgeMap e = e := by
  rfl

theorem toMap_vertMap_surjective (G : Graph α β) (f : α → γ) : Surjective (G.toMap f).vertMap :=
  Set.imageFactorization_surjective

theorem toMap_edgeMap_surjective (G : Graph α β) (f : α → γ) : Surjective (G.toMap f).edgeMap :=
  surjective_id

/-- The canonical map is surjective, including on isolated vertices. -/
theorem toMap_surjective (G : Graph α β) (f : α → γ) : (G.toMap f).Surjective :=
  ((G.toMap f).surjective_iff).mpr
    ⟨G.toMap_vertMap_surjective f, G.toMap_edgeMap_surjective f⟩

variable {f : α → γ} {g : α → δ} {k : α → ε}

/-- A factorization of vertex labels gives a factorization of the canonical homomorphisms.
The general carrier bridge supplies an explicit homomorphism witness. -/
theorem toMap_factorsThrough (h : FactorsThrough (g ·.val) (fun x : V(G) ↦ f x.1)) :
    (G.toMap g).FactorsThrough (G.toMap f) :=
  Hom.factorsThrough_of_maps (G.toMap_surjective f)
    (fun {_ _} heq ↦ Subtype.ext (h (congrArg Subtype.val heq))) FactorsThrough.rfl

/-- The factor between the canonical homomorphisms fixes every edge label. -/
noncomputable def mapHom (h : FactorsThrough (g ·.val) (fun x : V(G) ↦ f x.1)) :
    Hom (f ''ᴳ G) (g ''ᴳ G) :=
  (toMap_factorsThrough h).factor

@[simp]
theorem mapHom_vertMap_val (h : FactorsThrough (g ·.val) (fun x : V(G) ↦ f x.1)) (hu : u ∈ V(G)) :
    ((mapHom h).vertMap ⟨f u, mem_image_of_mem f hu⟩).1 = g u :=
  congrArg Subtype.val ((toMap_factorsThrough h).factor_vertMap_apply ⟨u, hu⟩)

@[simp]
theorem mapHom_edgeMap (h : FactorsThrough (g ·.val : V(G) → δ) (fun x : V(G) ↦ f x.1)) (e : E(G)) :
    (mapHom h).edgeMap e = e :=
  (toMap_factorsThrough h).factor_edgeMap_apply e

theorem mapHom_vertMap_surjective (h : FactorsThrough (g ·.val) (fun x : V(G) ↦ f x.1)) :
    Surjective (mapHom h).vertMap := by
  exact ((toMap_factorsThrough h).factor_vertMap_surjective_iff
    (G.toMap_vertMap_surjective f)).mpr
    (G.toMap_vertMap_surjective g)

theorem mapHom_vertMap_injective_iff (h : FactorsThrough (g ·.val) (fun x : V(G) ↦ f x.1)) :
    Injective (mapHom h).vertMap ↔ FactorsThrough (fun x : V(G) ↦ f x.val) (g ·.val) := by
  rw [mapHom, (toMap_factorsThrough h).factor_vertMap_injective_iff
    (G.toMap_vertMap_surjective f)]
  exact ⟨fun hi x y hxy ↦ congrArg Subtype.val (hi (Subtype.ext hxy)),
    fun hi x y hxy ↦ Subtype.ext (hi (congrArg Subtype.val hxy))⟩

theorem toMap_comp_mapHom (h : FactorsThrough (g ·.val) (fun x : V(G) ↦ f x.1)) :
    (G.toMap f).comp (mapHom h) = G.toMap g :=
  (toMap_factorsThrough h).comp_factor

@[simp]
theorem mapHom_self : mapHom (G := G) (f := f) FactorsThrough.rfl = Hom.id (f ''ᴳ G) :=
  (toMap_factorsThrough (G := G) (f := f) FactorsThrough.rfl).factor_self (G.toMap_surjective f)

theorem mapHom_comp (h : FactorsThrough (g ·.val) (fun x : V(G) ↦ f x.1))
    (h' : FactorsThrough (fun x : V(G) ↦ k x.1) (g ·.val)) :
    (mapHom h).comp (mapHom h') = mapHom (h'.trans h) :=
  (toMap_factorsThrough h).factor_comp (toMap_factorsThrough h') (G.toMap_surjective f)

/-- Mutual factorization compares the targets of the two canonical homomorphisms. -/
noncomputable def mapIso (h : FactorsThrough (g ·.val) (fun x : V(G) ↦ f x.1))
    (h' : FactorsThrough (fun x : V(G) ↦ f x.1) (g ·.val)) : Iso (f ''ᴳ G) (g ''ᴳ G) :=
  Hom.isoOfFactorsThrough (G.toMap_surjective f) (G.toMap_surjective g)
    (toMap_factorsThrough h) (toMap_factorsThrough h')

@[simp]
theorem mapIso_toHom (h : FactorsThrough (g ·.val) (fun x : V(G) ↦ f x.1))
    (h' : FactorsThrough (fun x : V(G) ↦ f x.1) (g ·.val)) : (mapIso h h').toHom = mapHom h :=
  Hom.isoOfFactorsThrough_toHom (G.toMap_surjective f) (G.toMap_surjective g)
    (toMap_factorsThrough h) (toMap_factorsThrough h')

@[simp]
theorem mapIso_vertMap_val (h : FactorsThrough (g ·.val) (fun x : V(G) ↦ f x.1))
    (h' : FactorsThrough (fun x : V(G) ↦ f x.1) (g ·.val)) (hu : u ∈ V(G)) :
    ((mapIso h h').vertMap ⟨f u, mem_image_of_mem f hu⟩).1 = g u := by
  simpa only [mapIso_toHom] using (mapHom_vertMap_val h hu)

@[simp]
theorem mapIso_edgeMap (h : FactorsThrough (g ·.val) (fun x : V(G) ↦ f x.1))
    (h' : FactorsThrough (fun x : V(G) ↦ f x.1) (g ·.val)) (e : E(G)) :
    (mapIso h h').edgeMap e = e := by
  simpa only [mapIso_toHom] using (mapHom_edgeMap h e)

@[simp]
theorem mapIso_invVertMap_val (h : FactorsThrough (g ·.val) (fun x : V(G) ↦ f x.1))
    (h' : FactorsThrough (fun x : V(G) ↦ f x.1) (g ·.val)) (hu : u ∈ V(G)) :
    ((mapIso h h').invVertMap ⟨g u, mem_image_of_mem g hu⟩).1 = f u :=
  congrArg Subtype.val ((toMap_factorsThrough h').factor_vertMap_apply ⟨u, hu⟩)

@[simp]
theorem mapIso_invEdgeMap (h : FactorsThrough (g ·.val) (fun x : V(G) ↦ f x.1))
    (h' : FactorsThrough (fun x : V(G) ↦ f x.1) (g ·.val)) (e : E(G)) :
    (mapIso h h').invEdgeMap e = e :=
  (toMap_factorsThrough h').factor_edgeMap_apply e

@[simp]
theorem mapIso_symm (h : FactorsThrough (g ·.val) (fun x : V(G) ↦ f x.1))
    (h' : FactorsThrough (fun x : V(G) ↦ f x.1) (g ·.val)) : (mapIso h h').symm = mapIso h' h :=
  Hom.isoOfFactorsThrough_symm (G.toMap_surjective f) (G.toMap_surjective g)
    (toMap_factorsThrough h) (toMap_factorsThrough h')

@[simp]
theorem mapIso_self : mapIso FactorsThrough.rfl FactorsThrough.rfl = Iso.id (f ''ᴳ G) :=
  Hom.isoOfFactorsThrough_self (G.toMap_surjective f)
    (toMap_factorsThrough FactorsThrough.rfl) (toMap_factorsThrough FactorsThrough.rfl)

theorem mapIso_comp (h : FactorsThrough (g ·.val) (fun x : V(G) ↦ f x.1))
    (h' : FactorsThrough (fun x : V(G) ↦ f x.1) (g ·.val))
    (j : FactorsThrough (fun x : V(G) ↦ k x.1) (g ·.val))
    (j' : FactorsThrough (g ·.val) (fun x : V(G) ↦ k x.1)) :
    (mapIso h h').comp (mapIso j j') = mapIso (j.trans h) (h'.trans j') :=
  Hom.isoOfFactorsThrough_comp (G.toMap_surjective f) (G.toMap_surjective g)
    (G.toMap_surjective k) (toMap_factorsThrough h) (toMap_factorsThrough h')
    (toMap_factorsThrough j) (toMap_factorsThrough j')

end Graph
