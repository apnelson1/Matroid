import Matroid

variable {α ι : Type*}

open Matroid

/- ## Modularity -/

/-  ### Definition 1 : Mutual Basis
If `M` is a matroid, `B` is a set of elements of `M`,
and `X` is a family of sets in `M` indexed by `ι`,
then `M.IsMutualBasis B X` means that `B` is an `M`-independent set,
that intersects each `X i` in a basis for `X i`. -/
example (M : Matroid α) (B : Set α) (X : ι → Set α) :
    M.IsMutualBasis B X ↔ M.Indep B ∧ ∀ i, M.IsBasis (X i ∩ B) (X i) :=
  Matroid.isMutualBasis_iff ..

/- ### Definition 2 (i) : Modular Family
If `X` is a family of sets in `M`, then `M.IsModularFamily X`
means that `M` has a mutual basis for `X`. -/
example (M : Matroid α) (X : ι → Set α) :
    M.IsModularFamily X ↔ ∃ B, M.IsMutualBasis B X :=
  Iff.rfl

/- ### Definition 2 (ii) : Modular Pair
If `X` and `Y` are sets in a matroid `M`, then `M.IsModularPair X Y`
means that `M` has a mutual basis for `X` and `Y`. -/
example (M : Matroid α) (X Y : Set α) :
    M.IsModularPair X Y ↔ ∃ B, M.Indep B ∧ M.IsBasis (X ∩ B) X ∧ M.IsBasis (Y ∩ B) Y :=
  isModularPair_iff

/- ### Definition 2 (iii) : Modular Flat
If `F` is a flat of a matroid `M`, then `M.IsModularFlat F`
means that `F` and `G` is a modular pair for every flat `G` of `M`. -/
example (M : Matroid α) (F : Set α) :
    M.IsModularFlat F ↔ M.IsFlat F ∧ ∀ G, M.IsFlat G → M.IsModularPair F G :=
  isModularFlat_iff ..

/- ### Definition 2 (iv) : Modular Matroid
If `M` is a matroid, then `M.Modular` means that every flat of `M` is a modular flat. -/
example (M : Matroid α) :
    M.Modular ↔ ∀ F, M.IsFlat F → M.IsModularFlat F :=
  Iff.rfl

/- ### Theorem 1.15
Every modular matroid is finitary -/
example (M : Matroid α) (h : M.Modular) : M.Finitary :=
  Modular.finitary h

/- ### Theorem 1.16
A loopless matroid is modular if and only if every line intersects every hyperplane. -/
example (M : Matroid α) (hM : M.Loopless) :
    M.Modular ↔ ∀ ⦃L H⦄, M.IsLine L → M.IsHyperplane H → (L ∩ H).Nonempty :=
  modular_iff_forall_isLine_isHyperplane_nonempty_inter




structure ModularCut (M : Matroid α) where
  (U : Set (Set α))
  (forall_isFlat : ∀ F ∈ U, M.IsFlat F)
  (forall_superset : ∀ F F', F ∈ U → M.IsFlat F' → F ⊆ F' → F' ∈ U)
  (forall_inter : ∀ Fs ⊆ U,
    Fs.Nonempty → M.IsModularFamily (fun x : Fs ↦ x) → ⋂₀ Fs ∈ U)
