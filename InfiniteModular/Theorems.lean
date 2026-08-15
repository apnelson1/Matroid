module

public import Matroid

/-! # Theorem statements
This file contains formalized statements of the the main theorems of the article
`Modularity, Extensions, and Connectivity in Infinite Matroids`,
by Mattias Ehatamm, Peter Nelson and Fernanda Rivera Omana.

Our goal is explicitly to only give the formalized statements;
the proofs are all given by references to theorems elsewhere in the `Matroid` repository.
Regardless, a reader should be convinced that all the theorem statements are true
by the fact that the lean typechecker (which examines all the linked proof)
accepts the file with no errors.

The only extra thing a fastidious reader must check
is that all the definitions used in the theorem statement correspond
correctly to their informal counterparts. The accompanying `Definitions` file
contains formally verified statements and documentation intended to convince
the reader that this is the case. -/

-- Define `α` as an ambient set of potential matroid elements,
-- And `ι` to be used as an nonempty indexing set.
open Matroid Set Function

-- Open the namespaces containing basic set, function and matroid terminology
variable {ι α : Type*}

/- ### Theorem 1.3
If `P` is an extension of `M` by `e`, and `𝓕` is the modular cut of `M`
comprising precisely the flats of `M` that span `e` in `P`, then `P` is equal to `M.extendBy 𝓕`.
This gives the uniqueness that completes the proof of Theorem 1.3;
the remainder of the content of the theorem is implicit in Definition 4 (ii) -/
example (M P : Matroid α) (e : α) (e_mem : e ∈ P.E) (𝓕 : M.ModularCut)
    (P_del_eq : P ＼ {e} = M) (P_flat_iff : ∀ F, M.IsFlat F → (e ∈ P.closure F ↔ F ∈ 𝓕)) :
    P = M.extendBy e 𝓕 := by
  subst P_del_eq; exact .symm <| ModularCut.eq_extendBy_of_forall_flat _ e_mem P_flat_iff

/- ### Theorem 1.8
If `N` is a quotient of `M` with `N` or `M✶` finitary, and the discrepancy is finite, then
`N` is a projection of `M`.

(We include a technical hypothesis that there are infinitely many potential matroid elements
in `α` that are not already in `M.E`.
This is to 'make room' for the quotient; it has no effect on the mathematical content.)-/
example (N M : Matroid α) (finitary : Finitary N ∨ Finitary M✶) (quot : N ≤q M)
    (hfin : quot.discrepancy M.E < ⊤) (h_inf : M.Eᶜ.Infinite) :
    ∃ (P : Matroid α) (X : Set α), X ⊆ P.E ∧ P ／ X = N ∧ P ＼ X = M := by
  obtain fin | fin := finitary
  · exact quot.exists_eq_contract_eq_delete_of_discrepancy_lt_encard_compl
      (by rwa [h_inf.encard_eq])
  exact quot.exists_eq_contract_eq_delete_of_discrepancy_lt_encard_compl' (by rwa [h_inf.encard_eq])

/- ### Theorem 1.9
If `M 0, ... , M n` is a sequence of matroids, and `𝓕 0, ..., 𝓕(n-1)` is a sequence so that
each `𝓕 i` is a modular cut of `M i` for which `M (i+1)` is the projection,
then for each finite `n`-element set `X` outside the common ground set of the `M`,
there is a matroid `P` for which `P ＼ X = M 0` and `P ／ X = M n`.
(The notation here is more intricate than most of our statements, due to the complexities of finite
indexing and the offsetting by one that links the `M` and `𝓕`.)-/
example {n : ℕ} (M : Fin (n+1) → Matroid α) (𝓕 : (i : Fin n) → (M i.castSucc).ModularCut)
    (projection : ∀ i, M i.succ = (M i.castSucc).projectBy (𝓕 i))
    {X : Finset α} (hX : X.card = n) (hdj : Disjoint (M 0).E X) :
    ∃ (P : Matroid α), (X : Set α) ⊆ P.E ∧ P ＼ X = M 0 ∧ P ／ X = M (Fin.last n) := by
  exact exists_eq_delete_eq_contract_of_projectBy_seq M 𝓕 projection hX hdj

/- ### Theorem 1.10
If `C` and `D` are disjoint sets, not both infinite,
and `M` and `N` are matroids with `M ／ C = N ＼ D`,
then there is a matroid `P` with `P ＼ D = M` and `P ／ C = N`. -/
example (M N : Matroid α) (C D : Set α) (hfin : C.Finite ∨ D.Finite) (disjoint : Disjoint C D)
    (con_eq_del : M ／ C = N ＼ D) : ∃ P, P ＼ D = M ∧ P ／ C = N :=
  exists_splice_of_contract_eq_delete' hfin disjoint con_eq_del

/- ### Theorem 1.11
One of the equivalent characterizations of skewness : an indexed collection `X i` of sets
is skew in a matroid `M` if and only if each circuit contained in the union of the `X i`
is contained in one of the `X i`. -/
example (M : Matroid α) (X : ι → Set α) (subset_ground : ∀ i, X i ⊆ M.E)
    (disjoint : Pairwise (Disjoint on X)) :
    M.IsSkewFamily X ↔ ∀ C, M.IsCircuit C → C ⊆ ⋃ i, X i → ∃ i, C ⊆ X i :=
  isSkewFamily_iff_forall_isCircuit subset_ground disjoint

/- ### Theorem 1.13
Given a collection `X i` of sets with union `M.E`, a flat `F` belongs to the guts modular cut
of `X` if and only if the sets in `X` are a skew family in `M.project F`.
The mathematical content of the theorem is contained not in the equivalence below, but
in the definition of `gutsModularCut`; the fact that flats whose projection makes `X` skew
form a modular cut is formalized just by the fact that `M.gutsModularCut X union`
is a valid term of type `M.modularCut`. -/
example (M : Matroid α) (X : ι → Set α) (union : ⋃ i, X i = M.E) (F : Set α) (flat : M.IsFlat F):
    F ∈ M.gutsModularCut X union ↔ (M.project F).IsSkewFamily X := by
  simp [gutsModularCut, flat]

/- ### Theorem 1.18
Every modular matroid is finitary. -/
example (M : Matroid α) (h : M.Modular) : M.Finitary :=
  Modular.finitary h

/- ### Theorem 1.19
A loopless matroid is modular if and only if every line intersects every hyperplane. -/
example (M : Matroid α) (hM : M.Loopless) :
    M.Modular ↔ ∀ ⦃L H⦄, M.IsLine L → M.IsHyperplane H → (L ∩ H).Nonempty :=
  modular_iff_forall_isLine_isHyperplane_nonempty_inter

/- ### Theorem 1.15(ii), Upper bound
If `A` is a finite set, disjoint from the ground set of `M`,
with size equal to the dual connectivity of a partition `X` of `M.E`,
then `M` has a projection by `A` in which `X` is skew. -/
example (M : Matroid α) (X : ι → Set α)
    (union_eq_ground : ⋃ i, X i = M.E) (disjoint : Pairwise (Disjoint on X))
    (A : Set α) (hAfin : A.Finite) (hA : A.encard = M✶.multiConn X)
    (disjoint_ground : Disjoint A M.E) :
    ∃ (P : Matroid α), A ⊆ P.E ∧ P ＼ A = M ∧ (P ／ A).IsSkewFamily X := by
  obtain ⟨P, hAE, rfl, hsk⟩ :=
     M.exists_contract_skew_delete_eq_of_card_eq_dual_multiConn X union_eq_ground
    disjoint (A := hAfin.toFinset) (by rw [← hA, hAfin.encard_eq_coe_toFinset_card]) (by simpa)
  exact ⟨P, by simpa using hAE, by simp, by simpa using hsk⟩

/- ### Theorem 1.15(ii), Upper bound
If `A` is a set in a matroid `P` with `P ＼ A = M`,
and `X` is a partition of `M.E` that is skew in `P ／ A`,
then `A` has cardinality at least the connectivity of `X` in `M`. -/
example (P M : Matroid α) (X : ι → Set α)
    (union_eq_ground : ⋃ i, X i = M.E) (disjoint : Pairwise (Disjoint on X))
    (A : Set α) (delete_eq : P ＼ A = M) (contract_skew : (P ／ A).IsSkewFamily X) :
    A.encard ≥ M✶.multiConn X :=
  M.multiConn_dual_le_encard_of_delete_isSkewFamily union_eq_ground disjoint delete_eq contract_skew
