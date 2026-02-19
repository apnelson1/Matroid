import Matroid.Connectivity.Separation.Vertical

namespace Matroid

open Set

variable {i b : Bool} {α : Type*} {e f g : α} {C K T X : Set α} {M : Matroid α} {P Q : M.Separation}
  {k : ℕ∞} {w : Matroid α → Set α → ℕ∞} {f : ℕ∞ → ℕ∞} {rem : Bool → Bool}

/-- A pair of nondegenerate separations of single-element removals of a matroid.
The separations are required to be nondegenerate in the sense of `SeqConnected` with
weight function `w` and connectivity threshold `f`.
The function `rem : Bool → Bool` says whether the removals are contractions or deletions,
with `true` corresponding to contraction and `false` to deletion.

This definition is given at the level of abstract separations and removals in order that
it can be specialized in many ways, such as to a pair of separations of `M ＼ {e}` and `M ＼ {f}`
respectively, or to separations of `M ／ {e}` and `M ＼ {e}` respectively.
-/
structure MinorSepDuo (M : Matroid α) (rem : Bool → Bool) (w : Matroid α → Set α → ℕ∞)
    (f : ℕ∞ → ℕ∞) where
  -- a pair of points `e,f`
  pt : Bool → α
  -- both points belong to the ground set
  mem_ground : ∀ b, pt b ∈ M.E
  -- separations of removals of `pt false` and `pt true` respectively
  removeSep : (b : Bool) → (M.remove {pt b} (rem b)).Separation
  -- for each separation `sep b`, the element `pt !b` is either gone, or on the `true` side.
  mem_true : ∀ b, pt (!b) ∈ insert (pt b) (removeSep b true)
  -- both separations are nondegenerate with respect to `w` and `f`.
  eConn_lt : ∀ b j, f (removeSep b).eConn < w (M.remove {pt b} (rem b)) (removeSep b j)

@[simps]
def MinorSepDuo.dual (S : M.MinorSepDuo rem w f) :
    M✶.MinorSepDuo (fun i ↦ !(rem i)) (fun N ↦ w N✶) f where
  pt := S.pt
  mem_ground := S.mem_ground
  removeSep b := (S.removeSep b).removeDual
  mem_true := S.mem_true
  eConn_lt b j := by convert S.eConn_lt b j using 1 <;> simp

@[simps]
def MinorSepDuo.copy (S : M.MinorSepDuo rem w f) {M' rem' w' f'} (hM : M = M') (hr : rem = rem')
    (hw : w = w') (hf : f = f') : M'.MinorSepDuo rem' w' f' where
  pt := S.pt
  mem_ground := hM ▸ S.mem_ground
  removeSep b := (S.removeSep b).copy <| by simp [hr, hM]
  mem_true b := by simpa using S.mem_true b
  eConn_lt b j := by simp [← hf, ← hM, ← hr, ← hw, S.eConn_lt b j]

def MinorSepDuo.removeSet (S : M.MinorSepDuo rem w f) : Set α := ⋃ b, {S.pt b}

@[simp]
lemma MinorSepDuo.mem_removeSet (S : M.MinorSepDuo rem w f) (b : Bool) :
    S.pt b ∈ S.removeSet :=
  mem_iUnion_of_mem b <| by simp

lemma MinorSepDuo.removeSet_eq_pair (S : M.MinorSepDuo rem w f) (b : Bool) :
    S.removeSet = {S.pt b, S.pt !b} := by
  rw [MinorSepDuo.removeSet, Set.iUnion_bool' _ b, singleton_union]

def MinorSepDuo.removeBoth (S : M.MinorSepDuo rem w f) :=
    (M.remove {S.pt true} (rem true)).remove {S.pt false} (rem false)

lemma MinorSepDuo.removeBoth_eq_remove (S : M.MinorSepDuo rem w f) (hrem : rem i = rem !i) :
    S.removeBoth = M.remove S.removeSet (rem i) := by
  cases i
  · rw [S.removeSet_eq_pair false, removeBoth, hrem, Bool.not_false, remove_remove, union_singleton]
  rw [S.removeSet_eq_pair true, removeBoth, hrem, Bool.not_true, remove_remove, singleton_union]

/-- The separation formed from `S.removeSep i` by removing `pt !i` in the intended way. -/
def MinorSepDuo.downSep (S : M.MinorSepDuo rem w f) (i : Bool) : S.removeBoth.Separation :=
  ((S.removeSep i).remove {S.pt !i} (rem !i)).copy' (by
    cases i <;> grind [remove_ground, diff_diff, union_singleton, removeBoth])

lemma MinorSep.downSep_eq_copy (S : M.MinorSepDuo rem w f) (hi : S.pt i ≠ S.pt (!i)) :
  S.downSep i = ((S.removeSep i).remove {S.pt !i} (rem !i)).copy
    (by
      cases i
      · rw [MinorSepDuo.removeBoth, remove_comm _ (by simpa), Bool.not_false]
      rw [MinorSepDuo.removeBoth, Bool.not_true]) := rfl

lemma MinorSepDuo.downSep_apply (S : M.MinorSepDuo rem w f) (i j : Bool) :
    S.downSep i j = S.removeSep i j \ {S.pt (!i)} := by
  simp [downSep, Separation.copy', Bipartition.copy]

-- def MinorSepDuo.minor (S : M.MinorSepDuo rem w f) (b : Bool) : Matroid α :=
--   bif rem b then M ／ {S.pt b} else M ＼ {S.pt b}

-- lemma MinorSepDuo.minor_eq_delete (S : M.MinorSepDuo rem w f) (hb : rem b = false) :
--     S.minor b = M ＼ {S.pt b} := by
--   simp [minor, hb]

-- lemma MinorSepDuo.minor_eq_contract (S : M.MinorSepDuo rem w f) (hb : rem b = true) :
--     S.minor b = M ／ {S.pt b} := by
--   simp [minor, hb]

-- def MinorSepDuo.minorSep (S : M.MinorSepDuo rem w f) (b : Bool) : (S.minor b).Separation :=
--   (S.sep b).induce (by simp [minor, Bool.apply_cond])

-- lemma MinorSepDuo.minorSep_eq_delete (S : M.MinorSepDuo rem w f) (hb : rem b = false) :
--     S.minorSep b = ((S.sep b).delete {S.pt b}).copy (S.minor_eq_delete hb).symm := by
--   refine Separation.ext ?_
--   rw [minorSep, ← Separation.induce_eq_delete, Separation.copy_apply, Separation.induce_apply,
--     Separation.induce_apply, S.minor_eq_delete hb]

-- lemma MinorSepDuo.minorSep_eq_contract (S : M.MinorSepDuo rem w f) (hb : rem b = true) :
--     S.minorSep b = ((S.sep b).contract {S.pt b}).copy (S.minor_eq_contract hb).symm := by
--   refine Separation.ext ?_
--   rw [minorSep, ← Separation.induce_eq_contract, Separation.copy_apply, Separation.induce_apply,
--     Separation.induce_apply, S.minor_eq_contract hb]

  -- simp [minorSep, S.minor_eq_delete hb]

-- lemma MinorSepDuo.eConn_minorSep_lt (S : M.MinorSepDuo rem w f) (b j : Bool) :
--     f (S.sep b).eConn < w (M.remove {S.pt b} (rem b)) (S.sep b j) := by
--   generalize h : rem b = d

  -- obtain h1 | h2 : rem b = true ∨ rem b = false := sorry
  -- ·





  -- · simp
  --   simp only [S.minor_eq_delete h, S.minorSep_eq_delete h,
  --     Separation.eConn_copy, Separation.copy_apply, ↓Separation.delete_apply]
  --   exact S.eConn_delete_lt h j
  -- simp only [S.minor_eq_contract h, S.minorSep_eq_contract h,
  --     Separation.eConn_copy, Separation.copy_apply, ↓Separation.contract_apply]
  -- exact S.eConn_contract_lt h j

    -- simp only [minor, minorSep, h, cond_false]
    -- rw [(S.sep b).induce_eq_delete]



-- If `rem b` is known to be `false`, then `S.sep b` as an explicit separation of `M ＼ {S.pt b}`.
@[simps!]
def MinorSepDuo.deleteSep (S : M.MinorSepDuo rem w f) (hb : rem b = false) :
    (M ＼ {S.pt b}).Separation :=
  (S.removeSep b).copy (by simp [hb])

-- If `rem b` is known to be `true`, then `S.sep b` as an explicit separation of `M ／ {S.pt b}`.
@[simps!]
def MinorSepDuo.contractSep (S : M.MinorSepDuo rem w f) (hb : rem b = true) :
    (M ／ {S.pt b}).Separation :=
  (S.removeSep b).copy (by simp [hb])

lemma MinorSepDuo.deleteSep_apply (S : M.MinorSepDuo rem w f) (hb : rem b = false) (i : Bool) :
    S.deleteSep hb i = S.removeSep b i := rfl

lemma MinorSepDuo.contractSep_apply (S : M.MinorSepDuo rem w f) (hb : rem b = true) (i : Bool) :
    S.contractSep hb i = S.removeSep b i := rfl

-- @[simps!]
-- def MinorSepDuo.contractSep (S : M.MinorSepDuo rem w f) (b : Bool) :
--     (M ／ {S.pt b}).Separation := (S.sep b).contract {S.pt b}

lemma MinorSepDuo.eConn_deleteSep_lt (S : M.MinorSepDuo rem w f) (hb : rem b = false)
    (j : Bool) : f (S.deleteSep hb).eConn < w (M ＼ {S.pt b}) (S.deleteSep hb j) := by
  simpa [deleteSep, hb] using S.eConn_lt b j

lemma MinorSepDuo.eConn_contractSep_lt (S : M.MinorSepDuo rem w f) (hb : rem b = true)
    (j : Bool) : f (S.contractSep hb).eConn < w (M ／ {S.pt b}) (S.contractSep hb j) := by
  simpa [contractSep, hb] using S.eConn_lt b j

@[simp]
lemma MinorSepDuo.notMem (S : M.MinorSepDuo rem w f) {b j : Bool} : S.pt b ∉ S.removeSep b j :=
  notMem_subset ((S.removeSep b).subset_ground) <| by simp

-- lemma MinorSepDuo.eConn_contractSep_lt (S : M.MinorSepDuo rem w f) (hb : rem b = true)
--     (j : Bool) : f (S.contractSep b).eConn < w (M ／ {S.pt b}) ((S.contractSep b) j) := by
--   simpa [contractSep] using S.eConn_contract_le hb j

-- lemma MinorSepDuo.minorSep_isPredSeparation (S : M.MinorSepDuo rem w f) :
--     (S.minorSep b).IsPredSeparation (fun _ M X ↦ w M X = 0) := by
--   intro j hw
--   have := S.e

-- @[simp]
-- lemma MinorSepDuo.minor_ground (S : M.MinorSepDuo rem w f) (b : Bool) :
--     (S.minor b).E = M.E \ {S.pt b} := by
--   cases h : rem b
--   · simp [S.eq_del h]
--   simp [S.eq_con h]

-- lemma MinorSepDuo.minor_isMinor (S : M.MinorSepDuo rem w f) {b : Bool} :
-- S.minor b ≤m M := by
--   cases h : rem b
--   · rw [S.eq_del h]
--     exact delete_isMinor ..
--   rw [S.eq_con h]
--   exact contract_isMinor ..

-- lemma MinorSepDuo.ne (S : M.MinorSepDuo rem w f) (b : Bool) : S.pt b ≠ S.pt !b := by
--   intro h_eq
--   have h := h_eq ▸ mem_of_mem_of_subset (S.mem_true b) (S.sep b).subset
--   simp [Bool.apply_cond] at h

lemma MinorSepDuo.subset_ground_diff (S : M.MinorSepDuo rem w f) {b j : Bool} :
    S.removeSep b j ⊆ M.E \ {S.pt b} := by
  grw [(S.removeSep b).subset, remove_ground]

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma MinorSepDuo.subset_ground (S : M.MinorSepDuo rem w f) {b j : Bool} :
    S.removeSep b j ⊆ M.E :=
  (S.removeSep b).subset.trans <| by simp

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma MinorSepDuo.deleteSep_subset_ground (S : M.MinorSepDuo rem w f) (hb : rem b = false) {j} :
    S.deleteSep hb j ⊆ M.E :=
  S.subset_ground

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma MinorSepDuo.contractSep_subset_ground (S : M.MinorSepDuo rem w f) (hb : rem b = true) {j} :
    S.contractSep hb j ⊆ M.E :=
  S.subset_ground

attribute [aesop unsafe 20% (rule_sets := [Matroid])] MinorSepDuo.mem_ground
-- (S : M.MinorSepDuo rem w f) (b : Bool) : S.pt b ∈ M.E := by
--   rw [← b.not_not]
--   refine mem_of_mem_of_subset (S.mem_true !b) ?_
--   grw [(S.sep !b).subset]
--   simp [Bool.apply_cond]



-- @[simps!]
-- def MinorSepDuo.contractSep (S : M.MinorSepDuo rem w f) (hb : rem b = true) :
--     (M ／ {S.pt b}).Separation :=
--   (S.sep b).copy <| S.eq_con hb

-- def MinorSepDuo.sepLift (S : M.MinorSepDuo rem w f) (b j : Bool) : M.Separation :=
--   (S.sep b).ofGroundSubset S.minor_isMinor.subset j

-- @[simp]
-- lemma sepLift_apply (S : M.MinorSepDuo rem w f) (b j : Bool) :
--     S.sepLift b j j = insert (S.pt b) (S.sep b j) := by
--   simp [MinorSepDuo.sepLift, inter_singleton_of_mem (S.mem_ground _)]

-- @[simp]
-- lemma sepLift_apply_not (S : M.MinorSepDuo rem w f) (b j : Bool) :
--     S.sepLift b j (!j) = S.sep b !j := by
--   simp [MinorSepDuo.sepLift]

lemma MinorSepDuo.mem_true_of_ne (S : M.MinorSepDuo rem w f) (h : S.pt i ≠ S.pt !i) :
    S.pt (!i) ∈ S.removeSep i true := by
  grind [S.mem_true i]

@[simp]
lemma MinorSepDuo.notMem_false (S : M.MinorSepDuo rem w f) (i : Bool) :
    S.pt (!i) ∉ S.removeSep i false := by
  intro hmem
  obtain heq | hne := eq_or_ne (S.pt (!i)) (S.pt i)
  · exact (S.subset_ground_diff hmem).2 <| by simp [heq]
  exact ((S.removeSep i).disjoint_bool true).notMem_of_mem_right hmem <| by grind [S.mem_true i]

lemma MinorSepDuo.isPredSeparation (S : M.MinorSepDuo rem w f) (b : Bool) :
    (S.removeSep b).IsPredSeparation (fun _ M X ↦ w M X = 0) :=
  fun j hw ↦ by simpa [hw] using S.eConn_lt b j

lemma MinorSepDuo.deleteSep_isPredSeparation (S : M.MinorSepDuo rem w f) (hb : rem b = false) :
    (S.deleteSep hb).IsPredSeparation (fun _ M X ↦ w M X = 0) :=
  fun j hw ↦ by simpa [hw] using S.eConn_deleteSep_lt hb j

lemma MinorSepDuo.contractSep_isPredSeparation (S : M.MinorSepDuo rem w f) (hb : rem b = true) :
    (S.contractSep hb).IsPredSeparation (fun _ M X ↦ w M X = 0) :=
  fun j hw ↦ by simpa [hw] using S.eConn_contractSep_lt hb j

/-- If `M` is `SeqConnected` with respect to `w` and `f`, and removal `b` is a deletion,
then because of the nondegeneracy of `sep b`, the point `pt b` is spanned by neither side of
`sep b` in the matroid `M`. -/
lemma MinorSepDuo.notMem_closure_of_delete (S : M.MinorSepDuo rem w f) (hw : IsFaithfulMono w)
    (hM : M.SeqConnected w f) (hb : rem b = false) (j : Bool) :
    S.pt b ∉ M.closure (S.deleteSep hb j) := by
  obtain hl | hnl := M✶.isLoop_or_isNonloop (S.pt b)
  · refine IsColoop.notMem_closure_of_notMem hl fun hm ↦ by simpa using S.subset_ground_diff hm
  obtain ⟨i, hi⟩ := hM.exists ((S.deleteSep hb).ofDelete j)
  refine fun hcl ↦ (S.eConn_deleteSep_lt hb i).not_ge ?_
  have hf : ((S.deleteSep hb).ofDelete j).Faithful (M ＼ {S.pt b}) := by
    rwa [Separation.faithful_delete_iff_subset_closure_of_subset (i := j) hnl.indep,
      Separation.ofDelete_apply_self, union_diff_cancel_right, singleton_subset_iff]
    · simp [deleteSep_apply]
    grw [Separation.ofDelete_apply_self, ← subset_union_right]
  grw [← hf.eConn_delete_eq, Separation.ofDelete_delete] at hi
  grw [← hi, ← hw.le_of_delete hf, Separation.ofDelete_apply_diff]

/-- A structure storing two points `e` and `f` in `M`, and Tutte separations of order at most
`k - 2` in removals (either contractions or deletions) of `e` and `f`. -/
def MinorTutteSepDuo (M : Matroid α) (rem : Bool → Bool) (k : ℕ∞) :=
  M.MinorSepDuo rem Matroid.tutteWeight (indicator {i | k < i + 1 + 1} ⊤)

lemma MinorTutteSepDuo.IsTutteSeparation (S : M.MinorTutteSepDuo rem k) {b : Bool} :
    (S.removeSep b).IsTutteSeparation := by
  simpa using MinorSepDuo.isPredSeparation S b

lemma MinorTutteSepDuo.eConn_lt (S : M.MinorTutteSepDuo rem (k + 1)) {b : Bool} :
    (S.removeSep b).eConn + 1 ≤ k := by
  by_contra! hlt
  have hlt := MinorSepDuo.eConn_lt S b true
  rw [indicator_of_mem (by simpa)] at hlt
  simp at hlt

lemma TutteConnected.exists_minorTutteSepDuo (h : M.TutteConnected k) {b c : Bool} {f : α}
    (he : ¬ (M.remove {e} b).TutteConnected k) (hf : ¬ (M.remove {f} c).TutteConnected k) :
    ∃ (S : M.MinorTutteSepDuo (fun i ↦ bif i then b else c) k), S.pt true = e ∧ S.pt false = f := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp at he
  set pt := fun i ↦ bif i then e else f
  set rem := fun i ↦ bif i then b else c
  have htc (i) : ¬ (M.remove {pt i} (bif i then b else c)).TutteConnected (k + 1) := by
    cases i <;> simpa [pt]
  have hE (i) : pt i ∈ M.E := by
    contrapose! h
    rw [← remove_singleton_of_notMem h (b := bif i then b else c)]
    exact htc i
  have hs (i) : ∃ (P : (M.remove {pt i} (rem i)).Separation),
      (P.eConn + 1 ≤ k) ∧ P.IsTutteSeparation ∧ pt (!i) ∈ insert (pt i) (P true) := by
    obtain ⟨Q, hQconn, hQsep⟩ := not_tutteConnected_iff_exists.1 <| htc i
    by_cases hmem : pt (!i) ∈ insert (pt i) (Q true)
    · exact ⟨Q, hQconn, hQsep, hmem⟩
    refine ⟨Q.symm, by simpa, by simpa, ?_⟩
    rw [Q.symm_true, mem_insert_iff, ← Q.compl_true, remove_ground]
    grind [hE (!i)]
  choose sep hsep using hs
  refine ⟨⟨pt, hE, sep, fun i ↦ (hsep i).2.2, fun b j ↦ ?_⟩, by simp [pt]⟩
  rw [indicator_of_notMem (by simpa using (hsep b).1)]
  exact (hsep b).2.1.tutteWeight_pos j

/-- A structure storing two points `e, f`, and Tutte separations of order at most `k - 2`
in `M ＼ {e}` and `M ＼ {f}`. -/
def DeleteTutteSepDuo (M : Matroid α) (k : ℕ∞) := M.MinorTutteSepDuo (fun _ ↦ false) k

/-- In a `DeleteTutteSepDuo`, we simply use `sep` to denote the separations. -/
def DeleteTutteSepDuo.sep (S : M.DeleteTutteSepDuo k) (b : Bool) := S.deleteSep (b := b) rfl

lemma DeleteTutteSepDuo.notMem_closure (S : M.DeleteTutteSepDuo k) (hM : M.TutteConnected k)
    (b j : Bool) : S.pt b ∉ M.closure (S.sep b j) := by
  rw [tutteConnected_iff_seqConnected'] at hM
  exact MinorSepDuo.notMem_closure_of_delete S isFaithfulMono_tutteWeight (by simpa) rfl j

lemma DeleteTutteSepDuo.IsTutteSeparation (S : M.DeleteTutteSepDuo k) {b : Bool} :
    (S.sep b).IsTutteSeparation := by
  simpa using MinorSepDuo.isPredSeparation S b

lemma DeleteTutteSepDuo.eConn_lt (S : M.DeleteTutteSepDuo (k + 1)) {b : Bool} :
    (S.sep b).eConn + 1 ≤ k := by
  by_contra! hlt
  have hlt := MinorSepDuo.eConn_lt S b true
  rw [indicator_of_mem (by simpa)] at hlt
  simp at hlt

/-- If `M` is `k`-connected, and deleting `e` or `f` destroys the `k`-connectedness,
then there is a `DeleteTutteSepDuo` with base points `e` and `f`. -/
lemma TutteConnected.exists_deleteTutteSepDuo {e f} (h : M.TutteConnected k)
    (he : ¬ (M ＼ {e}).TutteConnected k) (hf : ¬ (M ＼ {f}).TutteConnected k) :
    ∃ (S : M.DeleteTutteSepDuo k), S.pt true = e ∧ S.pt false = f := by
  obtain ⟨S, rfl, rfl⟩ := h.exists_minorTutteSepDuo (b := false) (c := false) he hf
  exact ⟨S.copy rfl (by simp) rfl rfl, rfl, rfl⟩














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
