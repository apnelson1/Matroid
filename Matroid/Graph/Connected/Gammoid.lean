import Matroid.Graph.Connected.Menger
import Mathlib.Combinatorics.Matroid.IndepAxioms

open Set Function Nat WList

variable {α β : Type*} {G : Graph α β} {T I J K : Set α}

namespace Graph

/-! ### Strict gammoid (cut-based interface) -/

/-- Cut-based strict gammoid independence with named fields.

`subset_ground` + `finite` allow us to use `Set.ncard` for cardinalities of subsets.
`fully_conn` states: every `I`–`T` vertex cut has size at least `|I|`. -/
@[mk_iff]
structure GammoidIndep (G : Graph α β) (T I : Set α) : Prop where
  subset_ground : I ⊆ V(G)
  finite : I.Finite
  fully_conn : G.SetConnGE T I I.ncard

lemma GammoidIndep.fully_conn_of_subset (h : G.GammoidIndep T I) (hJI : J ⊆ I) :
    G.SetConnGE T J J.ncard :=
  fun _ hKJ ↦ h.fully_conn.right_bound_anti h.finite hJI hKJ

lemma gammoidIndep_empty (G : Graph α β) (T : Set α) : G.GammoidIndep T (∅ : Set α) := by
  constructor <;> simp

lemma GammoidIndep.subset (h : G.GammoidIndep T I) (hJI : J ⊆ I) : G.GammoidIndep T J :=
  ⟨hJI.trans h.subset_ground, h.finite.subset hJI,
  fun _ hKJ ↦ h.fully_conn.right_bound_anti h.finite hJI hKJ⟩

lemma GammoidIndep.eq_of_superset (h : G.GammoidIndep T I) (hIT : T ⊆ I) : T = I := by
  have := h.fully_conn_of_subset (refl _) (C := T) <| by
    have := G.left_isSetCut T I
    rwa [inter_eq_right.mpr (hIT.trans h.subset_ground)] at this
  rw [h.finite.cast_ncard_eq] at this
  exact (h.finite.subset hIT).eq_of_subset_of_encard_le hIT this

lemma gammoidIndep_self (G : Graph α β) (hfin : T.Finite) : G.GammoidIndep T (V(G) ∩ T) where
  subset_ground := inter_subset_left
  finite := hfin.subset inter_subset_right
  fully_conn := G.setConnGE_self (hfin.subset inter_subset_right) inter_subset_left
    |>.subset inter_subset_right (refl _)

/-! ### Bridging to Menger (internal, finite graphs) -/

lemma GammoidIndep.exists_setEnsemble [G.Finite] (h : G.GammoidIndep T I) :
    ∃ A : G.SetEnsemble, A.between I T ∧ A.paths.encard = I.ncard := by
  have hconn := h.fully_conn.symm.vertexSet_inter_right
  obtain ⟨A, hA, hAcard⟩ := (Menger'sTheorem_set h.subset_ground inter_subset_left I.ncard).1 hconn
  rw [A.between_vertexSet_inter_right_iff] at hA
  exact ⟨A, hA, hAcard⟩

lemma setConnGE_of_exists_setEnsemble [G.Finite]
    (hA : ∃ A : G.SetEnsemble, A.between I T ∧ A.paths.encard = I.ncard) :
    G.SetConnGE I T I.ncard := by
  obtain ⟨A, hA, hAcard⟩ := hA
  rw [← A.between_vertexSet_inter_right_iff, ← A.between_vertexSet_inter_left_iff] at hA
  have := (Menger'sTheorem_set inter_subset_left inter_subset_left I.ncard).2 ⟨A, hA, hAcard⟩
  rwa [setConnGE_vertexSet_inter_left_iff, setConnGE_vertexSet_inter_right_iff] at this

/-! ### Restricting a linkage by start vertices (internal helper) -/

namespace SetEnsemble

open Set WList

variable {α β : Type*} {G : Graph α β} {A : G.SetEnsemble} {S T I : Set α} {P : WList α β}

/-- Keep only those paths of `A` whose first vertex lies in `I`. -/
def restrictFirst (A : G.SetEnsemble) (I : Set α) : G.SetEnsemble where
  paths := {P | P ∈ A.paths ∧ P.first ∈ I}
  disjoint _ hP _ hQ hne := A.disjoint hP.1 hQ.1 hne
  valid _ hP := A.valid hP.1

lemma restrictFirst_between (hA : A.between S T) : (A.restrictFirst I).between (S ∩ I) T := by
  intro P hP
  have hPT : G.IsPathFrom S T P := hA hP.1
  refine hPT.subset_left (S₀ := S ∩ I) inter_subset_left ⟨hPT.first_mem, hP.2⟩

lemma image_first_restrictFirst (A : G.SetEnsemble) (I : Set α) :
    first '' (A.restrictFirst I).paths = (first '' A.paths) ∩ I := by
  ext x
  constructor
  · rintro ⟨P, hP, rfl⟩
    refine ⟨?_, hP.2⟩
    exact ⟨P, hP.1, rfl⟩
  rintro ⟨⟨P, hP, rfl⟩, hxI⟩
  exact ⟨P, ⟨hP, hxI⟩, rfl⟩

lemma image_first_restrictFirst_eq (hI : I ⊆ first '' A.paths) :
    first '' (A.restrictFirst I).paths = I := by
  simp [image_first_restrictFirst, inter_eq_right.mpr hI]

end SetEnsemble

/-! ### The strict gammoid matroid (finite graph; axioms TBD) -/

variable (G) in
/-- `IndepMatroid` presentation of the strict gammoid (finite graph). -/
def gammoidIndepMatroid (T : Set α) [G.Finite] : IndepMatroid α where
  E := V(G)
  Indep := fun I => G.GammoidIndep T I
  indep_empty := by
    simpa using (Graph.gammoidIndep_empty (G := G) (T := T))
  indep_subset := by
    intro I J hJ hIJ
    exact (Graph.GammoidIndep.subset (G := G) (T := T) hJ hIJ)
  indep_aug I B hTI hnMI hMB := by
    have hconn := hMB.1.fully_conn.vertexSet_inter_left.vertexSet_inter_right
    obtain ⟨A, hA, hAcard⟩ := hTI.exists_setEnsemble
    have := G.Menger'sTheorem_aux inter_subset_left inter_subset_left hconn (A := A)
    
    rw [maximal_iff] at hnMI hMB
    obtain ⟨hTB, hMB⟩ := hMB
    obtain ⟨J, hTJ, hIJ⟩ := (by simpa [hTI] using hnMI); clear hnMI
    rw [← ssubset_iff_subset_ne] at hIJ
    rw [gammoidIndep_iff] at hTI hTJ hTB

    /-
    ⊢ ∃ x ∈ B \ I, G.GammoidIndep T (insert x I)
    hMB : Maximal (fun I ↦ G.GammoidIndep T I) B
    hnMI : ¬Maximal (fun I ↦ G.GammoidIndep T I) I
    hTI : G.GammoidIndep T I
    I B : Set α
    J K T : Set α
    G : Graph α β
    -/
    -- TODO: derive from `gammoidIndep_augment` (and/or directly from Menger) in the required form.
    sorry
  indep_maximal I hI J hJ hIJ := by
    -- TODO: finite-ground maximality.
    /-
    ⊢ ∃ J_1, J ⊆ J_1 ∧ Maximal (fun K ↦ (fun I ↦ G.GammoidIndep T I) K ∧ K ⊆ I) J_1
    hIJ : J ⊆ I
    hJ : (fun I ↦ G.GammoidIndep T I) J
    J : Set α
    hI : I ⊆ V(G)
    I : Set α
    K T : Set α
    G : Graph α β
    -/
    sorry
  subset_ground I hI :=  hI.subset_ground

variable (G) in
/-- Strict gammoid matroid on `V(G)` (finite graph). -/
def gammoid (T : Set α) [G.Finite] : Matroid α :=
  (Graph.gammoidIndepMatroid (G := G) T).matroid

end Graph
