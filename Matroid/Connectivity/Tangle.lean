import Matroid.Connectivity.Minor
import Matroid.Connectivity.Separation.Basic

open Set

variable {α R : Type*} {M : Matroid α} {X Y S : Set α} {e f : α} [Add R] [LE R]

structure ConnSystem (α R : Type*) [Add R] [LE R] where
  E : Set α
  toFun : Set α → R
  toFun_inter_ground : ∀ X, toFun (X ∩ E) = toFun X
  toFun_compl : ∀ X ⊆ E, toFun (E \ X) = toFun X
  toFun_submod : ∀ X Y, X ⊆ E → Y ⊆ E → toFun (X ∩ Y) + toFun (X ∪ Y) ≤ toFun X + toFun Y

namespace ConnSystem

variable {μ : ConnSystem α R}

instance : CoeFun (ConnSystem α R) (fun _ ↦ Set α → R) where
  coe := ConnSystem.toFun

attribute [coe] ConnSystem.toFun

@[simp]
lemma toFun_eq_coe (μ : ConnSystem α R) (X : Set α) : μ.toFun X = μ X := rfl

@[simp]
lemma inter_ground (μ : ConnSystem α R) (X : Set α) : μ (X ∩ μ.E) = μ X :=
  μ.toFun_inter_ground X

@[simp]
lemma compl (μ : ConnSystem α R) (X : Set α) : μ (μ.E \ X) = μ X := by
  simpa using μ.toFun_compl (X ∩ μ.E) inter_subset_right

lemma submod (μ : ConnSystem α R) (X Y : Set α) : μ (X ∩ Y) + μ (X ∪ Y) ≤ μ X + μ Y := by
  grw [← μ.inter_ground, inter_inter_distrib_right, ← μ.inter_ground (X ∪ Y),
    union_inter_distrib_right, ← μ.inter_ground X, ← μ.inter_ground Y]
  exact μ.toFun_submod _ _ inter_subset_right inter_subset_right

def pConn {μ : ConnSystem α R} (P : μ.E.Bipartition) : R := μ <| P true

@[simp]
lemma pConn_symm {μ : ConnSystem α R} (P : μ.E.Bipartition) : pConn P.symm = pConn P := by
  rw [pConn, P.symm_true, ← P.compl_true, μ.compl, pConn]

end ConnSystem

/-- The connectivity function on `ℕ∞` associated with a matroid. -/
@[simps E]
noncomputable def Matroid.eConnSystem (M : Matroid α) : ConnSystem α ℕ∞ where
  E := M.E
  toFun := M.eConn
  toFun_inter_ground := by simp
  toFun_compl := by simp
  toFun_submod _ _ _ _ := M.eConn_submod ..

@[simp]
lemma Matroid.eConnSystem_apply (M : Matroid α) (X : Set α) : M.eConnSystem X = M.eConn X := rfl

@[simp]
lemma Matroid.Separation.eConnSystem_pConn_apply (P : M.Separation) :
    M.eConnSystem.pConn P = P.eConn := by
  simp [ConnSystem.pConn, P.eConn_eq true]

structure Tangle (μ : ConnSystem α R) (k : R) where
  Small : Set α → Prop
  compl_singleton_not_small : ∀ e ∈ μ.E, ¬ Small (μ.E \ {e})
  conn_le_of_small : ∀ ⦃X⦄, Small X → μ X ≤ k
  small_or_small_compl : ∀ ⦃X⦄, X ⊆ μ.E → μ X ≤ k → Small X ∨ Small (μ.E \ X)
  union_union_ssubset : ∀ ⦃X Y Z⦄, Small X → Small Y → Small Z → X ∪ Y ∪ Z ⊂ μ.E

namespace Tangle

variable {R : Type*} [Preorder R] [Add R] {μ : ConnSystem α R} {k : R} {T : Tangle μ k}

@[grind .]
lemma Small.ssubset_ground (hX : T.Small X) : X ⊂ μ.E := by
  simpa using (T.union_union_ssubset hX hX hX)

lemma Small.subset_ground (hX : T.Small X) : X ⊆ μ.E :=
  hX.ssubset_ground.subset

lemma Small.conn_le (h : T.Small X) : μ X ≤ k :=
  T.conn_le_of_small h

lemma Small.union_ssubset (hX : T.Small X) (hY : T.Small Y) : X ∪ Y ⊂ μ.E := by
  simpa using T.union_union_ssubset hX hX hY

@[mk_iff]
structure Large (T : Tangle μ k) (X : Set α) : Prop where
  compl_small : T.Small <| μ.E \ X
  subset_ground : X ⊆ μ.E

attribute [grind .] Large.subset_ground

lemma small_or_large (hX : μ X ≤ k) (hXE : X ⊆ μ.E) : T.Small X ∨ T.Large X :=
  (T.small_or_small_compl hXE hX).elim Or.inl fun h ↦ Or.inr ⟨h, hXE⟩

lemma Small.compl_large (h : T.Small X) : T.Large (μ.E \ X) :=
  ⟨by rwa [diff_diff_cancel_left h.subset_ground], diff_subset⟩

lemma Small.subset (hX : T.Small X) (hYX : Y ⊆ X) (hY : μ Y ≤ k) : T.Small Y :=
  (T.small_or_large hY (hYX.trans hX.subset_ground)).elim id
    fun h ↦ by grind [h.compl_small.union_ssubset hX]

@[simps]
def truncate (T : Tangle μ k) {k'} (hk' : k' ≤ k) : Tangle μ k' where
  Small X := T.Small X ∧ μ X ≤ k'
  compl_singleton_not_small := by simp +contextual [T.compl_singleton_not_small]
  conn_le_of_small := by simp
  small_or_small_compl X hX hXk' := by simp [hXk', T.small_or_small_compl hX (hXk'.trans hk')]
  union_union_ssubset := by grind [T.union_union_ssubset]



-- def OrderGE (T : Tangle μ) (k : R) := ∀ X, μ X ≤ k → T.Small X ∨ T.Large X

end Tangle
