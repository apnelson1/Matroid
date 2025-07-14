import Matroid


/-! # Matroid definitions
This file contains formalized statements of the the main definitions in the article
`Modularity, Extensions, and Connectivity in Infinite Matroids`,
by Mattias Ehatamm, Peter Nelson and Fernanda Rivera Omana.

The purpose of this file is to convince a reader that the definitions
referred to in the accompanying formalized `Theorems` file actually correspond
to what they are intended to.

All these definitions already appear elsewhere in the `Matroid` repository;
to avoid making redundant copies of these existing definitions using `def`,
we structure this file differently. We encode each defined concept
using a formally verified statement that the definition has a certain property,
where the property is chosen to be enough to convince a reader that the definition
is equivalent to the one intended, even without examining the definition itself.
The fact that the lean proof assistant accepts this file with no errors
can be taken to mean that all these statements are true, and hence that the definitions
are correctly formalized.

(To give a very simple analogy outside matroid theory,
one could be convinced that a function `f : ℝ → ℝ` is the function sending `x` to `x/2`
by a formally verified proof is given that `2 * f(x) = x` for all `x`,
even if the location where `f` is defined is not visible.)

We limit the scope of the definitions included to just
-/

-- Define `α` as an ambient set of potential matroid elements,
-- And `ι` to be used as an nonempty indexing set.
variable {α ι : Type*} [Nonempty ι]

-- Open the namespaces containing basic set, function and matroid terminology
open Matroid Set Function

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

/- ### Definition 4 : Modular Cut
This is phrased slightly differently from other definitions,
since `ModularCut` is formalized as a mathematical object
rather than a predicate on set families;
the object `M.ModularCut` can be thought of as a set family
together with the information that Definition 4 is satisfied.
Syntactically, it is usually treated similarly to a plain set family.
We make two statements that together show that we have correctly formalized Definition 4 -/

/- The first statement shows that a family `𝓕` of sets satisfying Definition 4 gives rise
to an object `𝓕'` of type `M.ModularCut` with the same members as `𝓕`. -/
example (M : Matroid α) (𝓕 : Set (Set α))
    (forall_isFlat : ∀ F ∈ 𝓕, M.IsFlat F)
    (forall_superset : ∀ F F', F ∈ 𝓕 → M.IsFlat F' → F ⊆ F'→ F' ∈ 𝓕)
    (forall_inter : ∀ F F', F ∈ 𝓕 → F' ∈ 𝓕 → M.IsModularPair F F' → F ∩ F' ∈ 𝓕)
    (forall_inter_chain : ∀ 𝓒 ⊆ 𝓕, 𝓒.Infinite → M.IsModularFamily (fun C : 𝓒 ↦ C.1)
      → IsChain (· ⊆ ·) 𝓒 → ⋂₀ 𝓒 ∈ 𝓕) :
    ∃ 𝓕' : M.ModularCut, ∀ F, F ∈ 𝓕 ↔ F ∈ 𝓕' :=
  ⟨ModularCut.ofForallIsModularPairChainInter M 𝓕 forall_isFlat forall_superset
    forall_inter forall_inter_chain, by simp⟩

/- The second statement shows that the sets in any `ModularCut` satisfy the Definition 4
(in fact, they are closed under arbitrary intersections of modular families.) -/
example (M : Matroid α) (𝓕 : M.ModularCut) :
      (∀ F ∈ 𝓕, M.IsFlat F)
    ∧ (∀ F F', F ∈ 𝓕 → M.IsFlat F' → F ⊆ F'→ F' ∈ 𝓕)
    ∧ (∀ (F : ι → Set α), (∀ i, F i ∈ 𝓕) → M.IsModularFamily F → ⋂ i, F i ∈ 𝓕) :=
  ⟨𝓕.forall_isFlat, 𝓕.forall_superset, 𝓕.iInter_mem⟩

/- ### Definition 4 (ii) : Extension by a modular cut
If `𝓕` is a modular cut in a matroid `M`, then `P = M.extendBy e 𝓕`
is the extension of `M` by an element `e` using `𝓕`;
it satisfies `P \ e = M` and `e ∈ P.closure F ↔ F ∈ 𝓕` for each flat `F` of `M`.
The content of the statement below is essentially *Theorem 1.3* without the uniqueness part. -/
example (M : Matroid α) (e : α) (e_not_mem : e ∉ M.E) (𝓕 : M.ModularCut) :
    (M.extendBy e 𝓕) ＼ {e} = M ∧ ∀ F, M.IsFlat F → (e ∈ (M.extendBy e 𝓕).closure F ↔ F ∈ 𝓕) := by
  rw [and_iff_right <| ModularCut.extendBy_deleteElem _ e_not_mem]
  refine fun F hF ↦ ?_
  rw [ModularCut.mem_closure_extendBy_iff _ e_not_mem, hF.closure,
    or_iff_right (fun heF ↦ e_not_mem (hF.subset_ground heF))]

/- ### Definition 4 (iii) : Projection by a modular cut
`M.projectBy 𝓕` is obtained from `M.extendBy e 𝓕` by contracting `e`. -/
example (M : Matroid α) (e : α) (e_not_mem : e ∉ M.E) (𝓕 : M.ModularCut) :
    (M.extendBy e 𝓕) ／ {e} = M.projectBy 𝓕 :=
  extendBy_contract_eq _ e_not_mem

/- ### Definition 5 : Projection
For technical reasons, we do not make this a definition,
instead stating results about pairs of the form `P ／ X, P ＼ X` explicitly. -/

/- ### Definition 6 : Quotient
If `N` and `M` are matroids with ground set `E`, then
`N ≤q M` means that `M.closure X ⊆ N.closure X` for all `X`. -/
example (M N : Matroid α) (ground_eq : M.E = N.E) :
    N ≤q M ↔ ∀ X ⊆ M.E, M.closure X ⊆ N.closure X :=
  (TFAE_quotient ground_eq).out 0 2

/- ### Definition 7 : Skew
An indexed family `X i` of set in a matroid `M` is skew if it is modular,
and the intersection of any two distinct `X i` contains only loops -/
example (M : Matroid α) (X : ι → Set α) :
    M.IsSkewFamily X ↔ M.IsModularFamily X ∧ ∀ i j, i ≠ j → X i ∩ X j ⊆ M.closure ∅ := by
  simp [isSkewFamily_iff, closure_empty]

/- ### Definition 8 : Nullity
The nullity of a set `X` in a matroid `M` is the dual rank of the restriction of `M` to `X`,
given as a term in `ℕ∞ = ℕ ∪ {∞}`. -/
example (M : Matroid α) (X : Set α) :
    M.nullity X = (M ↾ X)✶.eRank :=
  rfl

/- ### Definition 10 : Connectivity of a set family
If `I i` and `X i` are indexed set families in a matroid `M` with `X i` disjoint,
and `I i` is a basis for `X i` for each `i`, then `λ(X)`, written `M.multiConn X`,
is the nullity of the union of the `I i`.

This is stated in a way that has mathematical content beyond a definition :
since `multiConn` is the same for each choice of bases, it shows well-definedness,
which is the content of *Corollary 5.7*  -/
example (M : Matroid α) (X I : ι → Set α) (disjoint : Pairwise (Disjoint on X))
    (basis : ∀ i, M.IsBasis (I i) (X i)) :
    M.multiConn X = M.nullity (⋃ i, I i) :=
  multiConn_eq_nullity_iUnion disjoint (fun i ↦ (basis i).isBasis')

/- ### Definition 11 : Local connectivity
If `X` and `Y` are sets in a matroid `M`, then `⊓ (X,Y)`, written `M.eLocalConn X Y`,
is the sum of the nullity of `I ∪ J` and the cardinality of `I ∩ J`,
for any bases `I`, `J` for `X` and `Y` respectively.

Like `multiConn`, this is stated in a way that gives well-definedness,
which is the content of *Corollary 5.4* -/
example (M : Matroid α) (I J X Y : Set α) (I_basis_X : M.IsBasis I X) (J_basis_Y : M.IsBasis J Y) :
    M.eLocalConn X Y = (I ∩ J).encard + M.nullity (I ∪ J) :=
  I_basis_X.eLocalConn_eq J_basis_Y

/- ### Definition 13 : Projection by a set
If `X` is a set in a matroid `M`, then `M // X`, written `M.project X`,
is the matroid with the same ground set as `M` and the same independent sets as `M ／ X`.
(This is easily seen to be the same as the definition in terms of the direct sum) -/
example (M : Matroid α) (X : Set α) :
    (M.project X).E = M.E ∧ ∀ I, (M.project X).Indep I ↔ (M ／ X).Indep I := by
  simp [project_indep_iff]

/- ### Definition 14 : Basis Pair
Our formalization omits this definition, instead referring to nested bases explicitly. -/

/- ### Definition 15 : Discrepancy
If `N` is a finitary quotient of `M`, then the discrepancy of a set `X` is equal to
the cardinality of `J - I`, where `(I,J)` is any `(N,M)`-basis pair for `X`.

Like `multiConn`, this is stated in a way that gives well-definedness,
which is the content of *Theorem 8.6 (i)* -/
example (M N : Matroid α) (finitary : N.Finitary) (quotient : N ≤q M) (X I J : Set α)
    (I_basis : N.IsBasis I X) (J_basis : M.IsBasis J X) (I_subset_J : I ⊆ J) :
    quotient.discrepancy X = (J \ I).encard :=
  .symm <| quotient.encard_isBasis_diff_eq_discrepancy I_basis J_basis I_subset_J
