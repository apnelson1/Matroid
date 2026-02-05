import Matroid.ForMathlib.Data.Set.IndexedPartition
import Mathlib.Data.Set.Card
import Batteries.CodeAction.Basic
import Batteries.CodeAction.Misc


open Set

variable {α R : Type*} {E F X Y S : Set α} {e f : α} [PartialOrder R] [Add R]

/-- A submodular function on `Set α` that is determined by its behaviour on a given ground set `E`,
and is invariant under taking complements within `E`. Examples include the connectivity function
of a matroid, and the vertex- and edge-connectivity functions of a graph. -/
structure ConnSystem (α R : Type*) [Add R] [LE R] where
  E : Set α
  toFun : Set α → R
  toFun_inter_ground : ∀ X, toFun (X ∩ E) = toFun X
  toFun_compl : ∀ X ⊆ E, toFun (E \ X) = toFun X
  toFun_submod : ∀ X Y, X ⊆ E → Y ⊆ E → toFun (X ∩ Y) + toFun (X ∪ Y) ≤ toFun X + toFun Y

namespace ConnSystem

variable {μ ν : ConnSystem α R}

instance : CoeFun (ConnSystem α R) (fun _ ↦ Set α → R) where
  coe := ConnSystem.toFun

attribute [coe] ConnSystem.toFun

protected lemma ext (μ ν : ConnSystem α R) (hE : μ.E = ν.E) (hf : ∀ X ⊆ μ.E, μ X = ν X) :
    μ = ν := by
  cases μ with
  | mk E f toFun_inter_ground toFun_compl toFun_submod =>
  cases ν with
  | mk E' f' toFun_inter_ground' toFun_compl' toFun_submod' =>
  obtain rfl : E = E' := by simpa using hE
  simp only [mk.injEq, true_and]
  ext X
  simp only at hf
  rw [← toFun_inter_ground, ← toFun_inter_ground', hf _ inter_subset_right]

@[simp]
lemma toFun_eq_coe (μ : ConnSystem α R) (X : Set α) : μ.toFun X = μ X := rfl

@[simp]
lemma conn_inter_ground (μ : ConnSystem α R) (X : Set α) : μ (X ∩ μ.E) = μ X :=
  μ.toFun_inter_ground X

@[simp]
lemma conn_compl (μ : ConnSystem α R) (X : Set α) : μ (μ.E \ X) = μ X := by
  simpa using μ.toFun_compl (X ∩ μ.E) inter_subset_right

lemma conn_submod (μ : ConnSystem α R) (X Y : Set α) : μ (X ∩ Y) + μ (X ∪ Y) ≤ μ X + μ Y := by
  grw [← μ.conn_inter_ground, inter_inter_distrib_right, ← μ.conn_inter_ground (X ∪ Y),
    union_inter_distrib_right, ← μ.conn_inter_ground X, ← μ.conn_inter_ground Y]
  exact μ.toFun_submod _ _ inter_subset_right inter_subset_right

/-- A connectivity system assigns a connectivity to each bipartition of its ground set. -/
def pConn (μ : ConnSystem α R) (P : μ.E.Bipartition) : R := μ <| P true

@[simp]
lemma pConn_symm {μ : ConnSystem α R} (P : μ.E.Bipartition) : μ.pConn P.symm = μ.pConn P := by
  rw [pConn, P.symm_true, ← P.compl_true, μ.conn_compl, pConn]

@[simp]
lemma pConn_ofSubset (μ : ConnSystem α R) (X : Set α) (hX : X ⊆ μ.E) (i : Bool) :
    μ.pConn (Bipartition.ofSubset hX i) = μ X := by
  cases i <;> simp [pConn]

@[simp]
lemma conn_eq_pConn (P : μ.E.Bipartition) (i : Bool) : μ (P i) = μ.pConn P := by
  cases i
  · rw [pConn, ← P.compl_true, μ.conn_compl]
  rfl

/-- Move a connectivity system to a larger ground set. -/
@[simps]
def induce (μ : ConnSystem α R) (hF : μ.E ⊆ F) : ConnSystem α R where
  E := F
  toFun := μ
  toFun_inter_ground X := by
    rw [← μ.conn_inter_ground, inter_assoc, inter_eq_self_of_subset_right hF, μ.conn_inter_ground]
  toFun_compl X hXF := by
    rw [← μ.conn_inter_ground, ← inter_diff_right_comm, inter_eq_self_of_subset_right hF,
      μ.conn_compl]
  toFun_submod _ _ _ _ := μ.conn_submod ..

@[simp]
lemma induce_pConn (μ : ConnSystem α R) (hF : μ.E ⊆ F) (P : F.Bipartition) :
    (μ.induce hF).pConn P = μ.pConn (P.induce hF) := by
  simp [pConn]

section normal

variable [Zero R] {μ : ConnSystem α R}

def Normal (μ : ConnSystem α R) : Prop := μ ∅ = 0

lemma Normal.conn_empty (hμ : μ.Normal) : μ ∅ = 0 := hμ

lemma Normal.conn_ground (hμ : μ.Normal) : μ μ.E = 0 := by
  rw [← μ.conn_compl, diff_self, hμ.conn_empty]

end normal

section Unitary

variable [Zero R] [One R] {μ : ConnSystem α R}

@[mk_iff]
structure Unitary (μ : ConnSystem α R) : Prop where
  conn_empty : μ ∅ = 0
  conn_singleton_le : ∀ e, μ {e} ≤ 1

lemma Unitary.normal (hμ : μ.Unitary) : μ.Normal :=
  hμ.1

lemma Unitary.conn_le_encard {μ : ConnSystem α ℕ∞} (hμ : μ.Unitary) (X : Set α) :
    μ X ≤ X.encard := by
  obtain hinf | hfin := X.finite_or_infinite.symm
  · simp [hinf.encard_eq]
  induction X, hfin using Finite.induction_on with
  | empty => simp [hμ.conn_empty]
  | @insert e X heX hfin ih =>
    have hsm := μ.conn_submod X {e}
    grw [hμ.conn_singleton_le, ih, inter_singleton_eq_empty.2 heX, hμ.conn_empty, zero_add] at hsm
    rwa [encard_insert_of_notMem heX, ← union_singleton]

end Unitary

instance : PartialOrder (ConnSystem α R) where
  le ν μ := ν.E ⊆ μ.E ∧ ∀ X, ν X ≤ μ X
  le_refl := by simp
  le_trans := by grind
  le_antisymm := by
    rintro μ ν ⟨hss, h⟩ ⟨hss', h'⟩
    exact @ConnSystem.ext _ _ _ _ _ _ (hss.antisymm hss') (fun X _ ↦ (h X).antisymm (h' X))

lemma subset_of_le (h : μ ≤ ν) : μ.E ⊆ ν.E := h.1

lemma conn_le_of_le (h : μ ≤ ν) : μ X ≤ ν X := h.2 X

@[simp]
lemma le_induce (μ : ConnSystem α R) (hF : μ.E ⊆ F) : μ ≤ μ.induce hF :=
  ⟨hF, by simp⟩

/-- If `μ, ν` are connectivity systems, and `P` is a bipartition of `ν.E`, then we say that
`SplitsIn P μ` if one side of `P` has a bipartition into two parts, each of which has connectivity
at most the connectivity of `P` in `ν`. -/
def SplitsIn (P : ν.E.Bipartition) (μ : ConnSystem α R) : Prop :=
    ∃ (i : Bool) (P₀ : (P i).Bipartition), ∀ j, μ (P₀ j) ≤ ν.pConn P

structure AdheresTo (ν μ : ConnSystem α R) : Prop where
  le : ν ≤ μ
  forall_splits : ∀ (P : ν.E.Bipartition), SplitsIn P μ

lemma AdheresTo.subset (h : ν.AdheresTo μ) : ν.E ⊆ μ.E :=
  h.1.1

lemma AdheresTo.conn_le (h : ν.AdheresTo μ) (X : Set α) : ν X ≤ μ X :=
  h.1.2 X

end ConnSystem
