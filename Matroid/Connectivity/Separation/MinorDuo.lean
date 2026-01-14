import Matroid.Connectivity.Separation.Vertical

namespace Matroid

open Set

variable {i : Bool} {α : Type*} {e f g : α} {C K T X : Set α} {M : Matroid α} {P Q : M.Separation}
  {k : ℕ∞} {dg : Matroid α → Set α → Prop}

structure DeleteSepDuo (M : Matroid α) (dg : Matroid α → Set α → Prop) where
  pt : Bool → α
  sep : (i : Bool) → (M ＼ {pt i}).Separation
  isPredSep : ∀ i, (sep i).IsPredSeparation (fun _ ↦ dg)
  mem_true : ∀ i, pt (!i) ∈ sep i true

def DeleteSepDuo.del (S : M.DeleteSepDuo dg) : Set α := ⋃ i, {S.pt i}

lemma DeleteSepDuo.mem_ground (S : M.DeleteSepDuo dg) (i : Bool) : S.pt i ∈ M.E := by
  rw [← i.not_not]
  exact mem_of_mem_of_subset (S.mem_true !i) <|
    by grw [(S.sep !i).subset, delete_ground, diff_subset]

lemma DeleteSepDuo.notMem_false (S : M.DeleteSepDuo dg) (i : Bool) : S.pt (!i) ∉ S.sep i false :=
  ((S.sep i).disjoint_bool true).notMem_of_mem_left (S.mem_true i)

-- lemma DeleteSepDuo.apply_true (S : M.DeleteSepDuo) (i : Bool) : S.sep i

-- def DeleteSepDuo.pt (_ : M.DeleteSepDuo e f) (i : Bool) : α := bif i then e else f

-- def DeleteSepDuo.sep (S : M.DeleteSepDuo e f) (i : Bool) : (M ＼ {S.pt !i}).Separation :=
--   if (hi : i = true) then S.right.copy (by _) else sorry

lemma DeleteSepDuo.notMem_closure (S : M.DeleteSepDuo dg) (hdg : Monotone (dg M))
    (hdg_del : ∀ ⦃X D⦄, D ⊆ X → dg M X → dg (M ＼ D) (X \ D)) (i j : Bool)
    (hM : M.NumConnected dg ((S.sep i).eConn + 1 + 1)) : S.pt i ∉ M.closure (S.sep i j) := by
  intro hcl

  refine hM.not_isPredSeparation (P := (S.sep i).ofDelete j) ?_ ?_
  · rw [Separation.eConn_ofDelete_eq_of_subset_closure]
    simpa

  intro k hk
  obtain rfl | rfl := k.eq_or_eq_not j
  · rw [Separation.ofDelete_apply_self] at hk
    refine S.isPredSep i k ?_

    simp
    have := hdg_del subset_union_right hk
  have := hdg ((S.sep i).ofDelete_apply_superset k j)
  simp at this
  refine S.isPredSep i k ?_
  simp
