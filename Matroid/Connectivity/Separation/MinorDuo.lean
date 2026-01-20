import Matroid.Connectivity.Separation.Vertical

namespace Matroid

open Set

variable {i b : Bool} {α : Type*} {e f g : α} {C K T X : Set α} {M : Matroid α} {P Q : M.Separation}
  {k : ℕ∞} {w : Matroid α → Set α → ℕ∞} {f : ℕ∞ → ℕ∞}

/-- A pair of nondegenerate separations of single-element deletions of a matroid -/
structure DeleteSepDuo (M : Matroid α) (w : Matroid α → Set α → ℕ∞) (f : ℕ∞ → ℕ∞) where
  -- a pair of points `e,f`
  pt : Bool → α
  -- separations `P,Q` of `M ＼ {e}` and `M ＼ {f}`.
  sep : (b : Bool) → (M ＼ {pt b}).Separation
  -- `e` is on the `true` side of `Q`, and `f` is on the `true` side of `P`.
  mem_true : ∀ b, pt (!b) ∈ sep b true
  -- both sides of both separations are nondegenerate with respect to `w` and `f`.
  eConn_lt : ∀ b j, f (sep b).eConn < w (M ＼ {pt b}) (sep b j)

def DeleteSepDuo.del (S : M.DeleteSepDuo w f) : Set α := ⋃ b, {S.pt b}

@[simp]
lemma DeleteSepDuo.mem_del (S : M.DeleteSepDuo w f) (b : Bool) : S.pt b ∈ S.del :=
  mem_iUnion_of_mem b <| by simp

lemma DeleteSepDuo.del_eq_pair (S : M.DeleteSepDuo w f) (b : Bool) : S.del = {S.pt b, S.pt !b} := by
  rw [DeleteSepDuo.del, Set.iUnion_bool' _ b, singleton_union]

lemma DeleteSepDuo.ne (S : M.DeleteSepDuo w f) (b : Bool) : S.pt b ≠ S.pt !b :=
  fun h_eq ↦ (mem_of_mem_of_subset (h_eq.symm ▸ S.mem_true b) (S.sep b).subset).2 rfl

lemma DeleteSepDuo.mem_ground (S : M.DeleteSepDuo w f) (b : Bool) : S.pt b ∈ M.E := by
  rw [← b.not_not]
  exact mem_of_mem_of_subset (S.mem_true !b) <|
    by grw [(S.sep !b).subset, delete_ground, diff_subset]

lemma DeleteSepDuo.notMem_false (S : M.DeleteSepDuo w f) (i : Bool) : S.pt (!i) ∉ S.sep i false :=
  ((S.sep i).disjoint_bool true).notMem_of_mem_left (S.mem_true i)

lemma DeleteSepDuo.notMem_closure (S : M.DeleteSepDuo w f) (hw : IsFaithfulMono w)
    (hM : M.SeqConnected w f) (b j : Bool) (hnl : M✶.IsNonloop (S.pt b)) :
    S.pt b ∉ M.closure (S.sep b j) := by
  obtain ⟨i, hi⟩ := hM.exists ((S.sep b).ofDelete j)
  refine fun hcl ↦ (S.eConn_lt b i).not_ge ?_
  have hf : ((S.sep b).ofDelete j).Faithful (M ＼ {S.pt b}) := by
    rwa [Separation.faithful_delete_iff_subset_closure_of_subset (i := j),
      Separation.ofDelete_apply_self, union_diff_cancel_right, singleton_subset_iff]
    · grw [(S.sep b).subset, delete_ground]
      grind
    · exact hnl.indep
    grw [Separation.ofDelete_apply_self, ← subset_union_right]
  grw [← hf.eConn_delete_eq, Separation.ofDelete_delete] at hi
  grw [← hi, ← hw.le_of_delete hf, Separation.ofDelete_apply_diff]







-- lemma DeleteSepDuo.notMem_closure_of_tutteSeparation (S : M.DeleteSepDuo k) (hk : k ≠ ⊤)
--     (i j : Bool) (hsep : ∀ i, (S.sep i).IsTutteSeparation)
--     (hM : M.TutteConnected ((S.sep i).eConn + 1 + 1)) :
--     S.pt i ∉ M.closure (S.sep i j) := by
--   intro hcl
--   have hcon : ((S.sep i).ofDelete j).eConn = (S.sep i).eConn :=
--     Separation.eConn_ofDelete_eq_of_subset_closure _ _ (by simpa)

--   refine hM.not_isTutteSeparation (P := (S.sep i).ofDelete j) (by simp [hcon]) ?_
--   refine Separation.isTutteSeparation_of_lt_encard fun k ↦ ?_
--   grw [hcon, ← encard_le_encard (Separation.ofDelete_apply_superset ..)]
--   have := hsep
