import Matroid.Connectivity.Separation.Vertical

variable {α : Type*} {M : Matroid α} {N : Bool → Matroid α} {e f : α} {X C D : Set α}
  {i j b c : Bool} {k : ℕ∞}

open Set Matroid.Separation Bool

namespace Matroid


/-- A pair of separations of minors of `M`. -/
structure SepDuo (M : Matroid α) (N : Bool → Matroid α) where
  lhs : Bool → Set α
  diff : Bool → Set α
  subset_ground : ∀ i, lhs i ⊆ (N i).E
  isMinor : ∀ i, N i ≤m M
  diff_eq : ∀ i, diff i = M.E \ (N i).E

namespace SepDuo
protected lemma ext' {S S' : M.SepDuo N} (h : ∀ i, S.lhs i = S'.lhs i) : S = S' := by
  obtain ⟨f, d, h1, h2, h3⟩ := S
  obtain ⟨f', d', h1', h2', h3'⟩ := S'
  simpa [funext_iff, h3, h3', -forall_bool]

/-- A `SepDuo` behaves like an dependent function -/
instance {α : Type*} {M : Matroid α} {N : Bool → Matroid α} :
    DFunLike (M.SepDuo N) Bool (fun i ↦ (N i).Separation) where
  coe S i := (N i).ofSetSep (S.lhs i) true (S.subset_ground i)
  coe_injective' := fun S _ h ↦ S.ext' fun i ↦ (Separation.ext_iff_bool true).1 <| congr_fun h i

lemma apply_true (S : M.SepDuo N) (i : Bool) : S i true = S.lhs i := rfl

lemma apply_false (S : M.SepDuo N) (i : Bool) : S i false = (N i).E \ S.lhs i := rfl

@[simps]
def copyMinor (S : M.SepDuo N) {N'} (h : ∀ i, N i = N' i) : M.SepDuo N' where
  lhs := S.lhs
  diff := S.diff
  subset_ground i := h _ ▸ S.subset_ground i
  isMinor i := h _ ▸ S.isMinor i
  diff_eq i := h _ ▸ S.diff_eq i

@[simp]
lemma copyMinor_apply (S : M.SepDuo N) {N' : Bool → Matroid α} (h : ∀ i, N i = N' i) (i : Bool) :
    S.copyMinor h i = (S i).copy (h i) :=
  Separation.ext <| by simp [SepDuo.apply_true]

def upSep (S : M.SepDuo N) (i b : Bool) : M.Separation :=
  (S i).ofGroundSubset (S.isMinor i).subset b

def upSep_apply (S : M.SepDuo N) (i : Bool) (b c : Bool) :
    S.upSep i b c = bif b == c then (S i c ∪ S.diff i) else S i c := by
  rw [upSep, ofGroundSubset_apply, Bool.beq_comm, S.diff_eq]

@[simp]
def upSep_apply_self (S : M.SepDuo N) (i : Bool) (b : Bool) : S.upSep i b b = S i b ∪ S.diff i := by
  simp [S.upSep_apply]

@[simp]
def upSep_apply_not (S : M.SepDuo N) (i : Bool) (b : Bool) : S.upSep i b (!b) = S i (!b) := by
  simp [S.upSep_apply]

@[simp]
def upSep_not_apply (S : M.SepDuo N) (i : Bool) (b : Bool) : S.upSep i (!b) b = S i b := by
  simp [S.upSep_apply]

@[simp]
def upSep_false_true (S : M.SepDuo N) (i : Bool) : S.upSep i false true = S i true := by
  simp [S.upSep_apply]

@[simp]
def upSep_true_false (S : M.SepDuo N) (i : Bool) : S.upSep i true false = S i false := by
  simp [S.upSep_apply]

@[simp]
lemma upSep_copyMinor (S : M.SepDuo N) {N' : Bool → Matroid α} (h : ∀ i, N i = N' i) :
    (S.copyMinor h).upSep = S.upSep :=
  funext fun i ↦ funext fun b ↦ Separation.ext <| by simp [SepDuo.upSep_apply, SepDuo.apply_true]

@[grind =_]
lemma ground_eq (S : M.SepDuo N) : (N i).E = M.E \ S.diff i := by
  rw [S.diff_eq, diff_diff_cancel_left (S.isMinor i).subset]

lemma disjoint_diff (S : M.SepDuo N) (i b : Bool) : Disjoint (S i b) (S.diff i) := by
  grw [(S i).subset, S.diff_eq]
  exact disjoint_sdiff_right

@[grind .]
lemma subset_diff_diff (S : M.SepDuo N) : S i j ⊆ M.E \ S.diff i := by
  grw [(S i).subset, S.ground_eq]

def downSep {N₀ : Matroid α} (S : M.SepDuo N) (hN₀ : ∀ i, N₀.E ⊆ (N i).E) (i : Bool) :
    N₀.Separation :=
  (S i).induce (hN₀ i)


-- lemma SepDuo.ground_zero {N₀ N₁ : Matroid α} (S : M.SepDuo ![N₀, N₁]) : S

-- -- /-- A three-set generalization of the Bixby-Coullard inequality for `ℕ∞` -/
-- -- theorem eConn_inter_add_eConn_union_union_le (M : Matroid α) (hC : Disjoint C X)
-- --     (hD : Disjoint D X) :
-- --     M.eConn (C ∩ D) + M.eConn (X ∪ C ∪ D) ≤ (M ／ X).eConn C + (M ＼ X).eConn D + M.eConn X := by
-- -- -/

-- -- Contraction/Deletion pairs

variable {X Y : Set α} {b c i j : Bool}

lemma disjointRR (S : M.SepDuo b[M.remove b X, M.remove c Y]) :
    Disjoint (S i j) (bif i then Y else X) := by
  grw [(S i).subset]
  cases i with simp [disjoint_sdiff_left]

@[simp]
lemma disjointRR_self (S : M.SepDuo b[M.remove b X, M.remove c X])  :
    Disjoint (S i j) X := by
  convert S.disjointRR
  simp

@[simp]
lemma disjointCD_self (S : M.SepDuo b[M ／ X, M ＼ X]) : Disjoint (S i j) X :=
  S.disjointRR_self (b := true) (c := false)

def downSepRR (S : M.SepDuo b[M.remove b X, M.remove c Y]) (i : Bool) :
    ((M.remove b X).remove c Y).Separation :=
  S.downSep (by simp [diff_subset, diff_subset_diff_left diff_subset]) i

lemma downSepRR_apply_false (S : M.SepDuo b[M.remove b X, M.remove c Y]) (i : Bool) :
    S.downSepRR false i = S false i \ Y := by
  simp only [downSepRR, downSep, cond_false, induce_apply, remove_ground]
  rw [← inter_diff_assoc, inter_eq_self_of_subset_left]
  grw [(S false).subset, cond_false, remove_ground]

lemma downSepRR_apply_true (S : M.SepDuo b[M.remove b X, M.remove c Y]) (i : Bool) :
    S.downSepRR true i = S true i \ X := by
  simp only [downSepRR, downSep, cond_true, induce_apply, remove_ground]
  rw [diff_diff_comm, ← inter_diff_assoc, inter_eq_self_of_subset_left]
  grw [(S true).subset, cond_true, remove_ground]

@[simp]
lemma downSepRR_apply (S : M.SepDuo b[M.remove b X, M.remove c Y]) (i j : Bool) :
    S.downSepRR i j = S i j \ bif i then X else Y := by
  cases i with simp [downSepRR_apply_true, downSepRR_apply_false]

lemma diff_eqRR' (S : M.SepDuo b[M.remove b X, M.remove c Y]) (i : Bool) :
    S.diff i = bif i then Y ∩ M.E else X ∩ M.E := by
  cases i with simp [S.diff_eq, inter_comm]

lemma diff_eqRR (S : M.SepDuo b[M.remove b X, M.remove c Y]) (hX : X ⊆ M.E := by aesop_mat)
    (hY : Y ⊆ M.E := by aesop_mat) (i : Bool) : S.diff i = bif i then Y else X := by
  rw [diff_eqRR', inter_eq_self_of_subset_left hX, inter_eq_self_of_subset_left hY]

@[simp]
lemma upSep_induceRR (S : M.SepDuo b[M.remove b X, M.remove c Y]) (i j : Bool) :
    (S.upSep i j).induce (by grind) = S.downSepRR i := by
  have aux (i j) : S i j ⊆ M.E \ (bif i then Y else X) := by
    grw [S.subset_diff_diff, diff_eqRR']; grind
  refine Separation.ext ?_
  cases i <;> cases j <;>
  all_goals
  · simp only [upSep, cond_false, induce_apply, ↓ofGroundSubset_apply, beq_false, Bool.not_true,
    remove_ground, sdiff_sdiff_right_self, inf_eq_inter, downSepRR_apply]
    grind

def copyCD (S : M.SepDuo b[M ／ X, M ＼ Y]) : M.SepDuo b[M ／ (X ∩ M.E), M ＼ (Y ∩ M.E)] :=
  S.copyMinor <| fun i ↦ by cases i with simp

def copyDD (S : M.SepDuo b[M ＼ X, M ＼ Y]) : M.SepDuo b[M ＼ (X ∩ M.E), M ＼ (Y ∩ M.E)] :=
  S.copyMinor <| fun i ↦ by cases i with simp

def downSepCD (S : M.SepDuo b[M ／ X, M ＼ Y]) (i : Bool) : (M ／ X ＼ Y).Separation :=
  S.downSepRR (b := true) (c := false) i

@[simp]
lemma downSepCD_apply (S : M.SepDuo b[M ／ X, M ＼ Y]) (i j : Bool) :
    S.downSepCD i j = S i j \ bif i then X else Y :=
  downSepRR_apply ..

def downSepDD (S : M.SepDuo b[M ＼ X, M ＼ Y]) (i : Bool) : (M ＼ (X ∪ Y)).Separation :=
  (S.downSepRR (b := false) (c := false) i).copy <| by simp

@[simp]
lemma downSepDD_apply (S : M.SepDuo b[M ＼ X, M ＼ Y]) (i j : Bool) :
    S.downSepDD i j = S i j \ bif i then X else Y := by
  rw [downSepDD, copy_apply, downSepRR_apply]
  rfl

def downSepdd (S : M.SepDuo b[M ＼ {e}, M ＼ {f}]) (i : Bool) : (M ＼ {e, f}).Separation :=
  (S.downSepDD i).copy <| by simp [pair_comm]

@[simp]
lemma downSepdd_apply (S : M.SepDuo b[M ＼ {e}, M ＼ {f}]) (i j : Bool) :
    S.downSepdd i j = S i j \ bif i then {e} else {f} := by
  simp only [downSepdd, singleton_union, copy_rfl]
  exact downSepDD_apply ..

lemma diff_eqCD (S : M.SepDuo b[M ／ X, M ＼ Y]) (hXE : X ⊆ M.E := by aesop_mat)
    (hYE : Y ⊆ M.E := by aesop_mat) (i) : S.diff i = bif i then Y else X :=
  diff_eqRR (b := true) (c := false) ..

lemma diff_eqCD_self (S : M.SepDuo b[M ／ X, M ＼ X]) (hXE : X ⊆ M.E := by aesop_mat) (i : Bool) :
    S.diff i = X := by
  simp [diff_eqCD S]

lemma eConn_cross_add_eConn_cross_le (S : M.SepDuo b[M ／ X, M ＼ X]) (b c i j : Bool) :
    ((S.upSep false (!b)).cross (S.upSep true (!c)) b c i).eConn +
    ((S.upSep false b).cross (S.upSep true c) (!b) (!c) j).eConn ≤
    (S false).eConn + (S true).eConn + M.eConn X := by
  wlog hXE : X ⊆ M.E generalizing S X with aux
  · simpa [SepDuo.copyCD] using aux S.copyCD inter_subset_right

  convert M.eConn_inter_add_eConn_union_union_le (X := X) (C := S false b) (D := S true c)
    S.disjointCD_self S.disjointCD_self
  · simp [← Separation.eConn_eq _ i]
  · simp [← Separation.eConn_eq _ (!j), S.diff_eqCD_self hXE,
      show ∀ A B, A ∪ X ∪ (B ∪ X) = X ∪ A ∪ B by grind]
  · rw [← Separation.eConn_eq _ b]
    rfl
  rw [← Separation.eConn_eq _ c]
  rfl

lemma eConn_inter_add_eConn_union_le (S : M.SepDuo b[M ／ X, M ＼ X]) :
    ((S.upSep false false).inter (S.upSep true false)).eConn +
    ((S.upSep false true).union (S.upSep true true)).eConn ≤
      (S false).eConn + (S true).eConn + M.eConn X :=
  S.eConn_cross_add_eConn_cross_le ..

structure IsTutteTight (S : M.SepDuo N) (k : ℕ∞) : Prop where
  not_isTutteSeparation : ∀ i j, ¬ (S.upSep i j).IsTutteSeparation
  isTutteSeparation : ∀ i, (S i).IsTutteSeparation
  not_faithful : ∀ i j, ¬ (S.upSep i j).Faithful (N i)
  eConn_eq : ∀ i, (S i).eConn = k

lemma baz (h : M.TutteConnected (k + 1)) {e : Bool → α} {d : Bool → Bool}
    (hk : 2 * k < M.E.encard + 1) (hi : ∀ i, ¬ (M.remove (d i) {e i}).TutteConnected (k + 1)) :
    ∃ (S : M.SepDuo (fun i ↦ (M.remove (d i) {e i}))),
    ∀ i, (S i).eConn = k ∧ ∀ i j, ¬ (S.upSep i j).Faithful (M.remove (d i) {e i}) := by
  _

lemma bar (h : M.TutteConnected (k + 1)) (hk : 2 * k < M.E.encard + 1) (hNM : ∀ i, N i ≤m M)
    (hN : ∀ i, (M.E \ (N i).E).Subsingleton) (hi : ∀ i, ¬ (N i).TutteConnected (k + 1)) :
    ∃ (S : M.SepDuo N), ∀ i, (S i).eConn = k ∧ ∀ i j, ¬ (S.upSep i j).Faithful (N i) := by
  have hss (i) : ∃ b e, N i = M.remove b {e} := by
    obtain hNM' | h_eq := (hNM i).isStrictMinor_or_eq
    · exact hNM'.exists_eq_remove_singleton (hN i)
    exact False.elim <| hi i <| by rwa [h_eq]

  have htc (i) : (N i).TutteConnected k := by
    obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
    obtain ⟨b, e, h_eq⟩ := hss i



  sorry
  -- have := exists_of_tutteConnected_of_not_tutteConnected_add_one
    -- (hf : ¬ (M ＼ {f}).TutteConnected (k + 1)) (hef : (M ＼ {e,f}).TutteConnected k) :

-- lemma foo (h : M.TutteConnected (k + 1)) (he : ¬ (M ＼ {e}).TutteConnected (k + 1))
--     (hf : ¬ (M ＼ {f}).TutteConnected (k + 1)) (hef : (M ＼ {e,f}).TutteConnected k) :
--     ∃ (S : M.SepDuo b[M ＼ {e}, M ＼ {f}]),
--         ∀ i, (S i).eConn = k ∧ ∀ i, b[e, f] i ∈ S i true ∧ ∀ i j, b[e,f] i ∉ M.closure (S i j) := by
--   _
