import Matroid.Connectivity.Separation.Abstract

variable {α ι : Type*} {M : Matroid α} {N : ι → Matroid α} {e f : α} {X C D : Set α}

@[elab_as_elim]
def Fin.rec2 {motive : Fin 2 → Sort*} (i : Fin 2) (zero : motive 0) (one : motive 1) :
    motive i :=
  match i with
  | 1 => one
  | 0 => zero

notation "b[" x "," y "]" => fun i ↦ bif i then x else y

open Set Matroid.Separation

namespace Matroid


/-- A vector of separations of minors of `M`. -/
structure SepVec (M : Matroid α) (N : ι → Matroid α) where
  lhs : ι → Set α
  diff : ι → Set α
  subset_ground : ∀ i, lhs i ⊆ (N i).E
  isMinor : ∀ i, N i ≤m M
  diff_eq : ∀ i, diff i = M.E \ (N i).E

lemma SepVec.ext' {S S' : M.SepVec N} (h : ∀ i, S.lhs i = S'.lhs i) : S = S' := by
  obtain ⟨f, d, h1, h2, h3⟩ := S
  obtain ⟨f', d', h1', h2', h3'⟩ := S'
  simpa [funext_iff, h3, h3']

/-- A `SepVec` behaves like an dependent function -/
instance {ι α : Type*} {M : Matroid α} {N : ι → Matroid α} :
    DFunLike (M.SepVec N) ι (fun i ↦ (N i).Separation) where
  coe S i := (N i).ofSetSep (S.lhs i) true (S.subset_ground i)
  coe_injective' := fun S _ h ↦ S.ext' fun i ↦ (Separation.ext_iff_bool true).1 <| congr_fun h i

lemma SepVec.apply_true (S : M.SepVec N) (i : ι) : S i true = S.lhs i := rfl

lemma SepVec.apply_false (S : M.SepVec N) (i : ι) : S i false = (N i).E \ S.lhs i := rfl

@[simps]
def SepVec.copyMinor (S : M.SepVec N) {N'} (h : ∀ i, N i = N' i) : M.SepVec N' where
  lhs := S.lhs
  diff := S.diff
  subset_ground i := h _ ▸ S.subset_ground i
  isMinor i := h _ ▸ S.isMinor i
  diff_eq i := h _ ▸ S.diff_eq i

@[simp]
lemma copyMinor_apply (S : M.SepVec N) {N' : ι → Matroid α} (h : ∀ i, N i = N' i) (i) :
    S.copyMinor h i = (S i).copy (h i) :=
  Separation.ext <| by simp [SepVec.apply_true]

@[simp]
lemma copyMinor_diff (S : M.SepVec N) {N' : ι → Matroid α} (h : ∀ i, N i = N' i) :
    (S.copyMinor h).diff = S.diff := by
  refine funext fun i ↦ ?_
  rw [SepVec.diff_eq, ← h, S.diff_eq]

def SepVec.upSep (S : M.SepVec N) (i : ι) (b : Bool) : M.Separation :=
  (S i).ofGroundSubset (S.isMinor i).subset b

def SepVec.upSep_apply (S : M.SepVec N) (i : ι) (b c : Bool) :
    S.upSep i b c = bif b == c then (S i c ∪ S.diff i) else S i c := by
  rw [upSep, ofGroundSubset_apply, Bool.beq_comm, S.diff_eq]

@[simp]
def SepVec.upSep_apply_self (S : M.SepVec N) (i : ι) (b : Bool) :
    S.upSep i b b = S i b ∪ S.diff i := by
  simp [S.upSep_apply]

@[simp]
def SepVec.upSep_apply_not (S : M.SepVec N) (i : ι) (b : Bool) :
    S.upSep i b (!b) = S i (!b) := by
  simp [S.upSep_apply]

@[simp]
def SepVec.upSep_not_apply (S : M.SepVec N) (i : ι) (b : Bool) :
    S.upSep i (!b) b = S i b := by
  simp [S.upSep_apply]

@[simp]
lemma SepVec.upSep_copyMinor (S : M.SepVec N) {N' : ι → Matroid α} (h : ∀ i, N i = N' i) :
    (S.copyMinor h).upSep = S.upSep :=
  funext fun i ↦ funext fun b ↦ Separation.ext <| by simp [SepVec.upSep_apply, SepVec.apply_true]

lemma SepVec.ground_eq (S : M.SepVec N) (i : ι) : (N i).E = M.E \ S.diff i := by
  rw [S.diff_eq, diff_diff_cancel_left (S.isMinor i).subset]

lemma SepVec.disjoint_diff (S : M.SepVec N) (i : ι) (b : Bool) : Disjoint (S i b) (S.diff i) := by
  grw [(S i).subset, S.diff_eq]
  exact disjoint_sdiff_right

def SepVec.downSep {N₀ : Matroid α} (S : M.SepVec N) (hN₀ : ∀ i, N₀.E ⊆ (N i).E) (i : ι) :
    N₀.Separation :=
  (S i).induce (hN₀ i)

-- lemma SepVec.ground_zero {N₀ N₁ : Matroid α} (S : M.SepVec ![N₀, N₁]) : S

-- -- /-- A three-set generalization of the Bixby-Coullard inequality for `ℕ∞` -/
-- -- theorem eConn_inter_add_eConn_union_union_le (M : Matroid α) (hC : Disjoint C X)
-- --     (hD : Disjoint D X) :
-- --     M.eConn (C ∩ D) + M.eConn (X ∪ C ∪ D) ≤ (M ／ X).eConn C + (M ＼ X).eConn D + M.eConn X := by
-- -- -/

-- -- Contraction/Deletion pairs

variable {X Y : Set α}

def SepVec.downSepRR {b c : Bool} (S : M.SepVec b[M.remove X b, M.remove Y c]) (i : Bool) :
    ((M.remove X b).remove Y c).Separation :=
  S.downSep (by simp [diff_subset, diff_subset_diff_left diff_subset]) i

def SepVec.copyCD (S : M.SepVec b[M ／ X, M ＼ Y]) : M.SepVec b[M ／ (X ∩ M.E), M ＼ (Y ∩ M.E)] :=
  S.copyMinor <| fun i ↦ by cases i with simp

def SepVec.downSepCD (S : M.SepVec b[M ／ X, M ＼ Y]) (i : Bool) : (M ／ X ＼ Y).Separation :=
  S.downSep (fun i ↦ by cases i; simp [diff_subset_diff_left diff_subset]; simp [diff_subset] ) i

@[simp]
lemma SepVec.downSepCD_apply_false (S : M.SepVec b[M ／ X, M ＼ Y]) (i : Bool) :
    S.downSepCD false i = S false i \ X := by
  have := (S false).subset (i := i)
  simp only [cond_false, delete_ground] at this
  simp only [downSepCD, downSep, cond_false, induce_apply, delete_ground, contract_ground]
  grind


@[simp]
lemma SepVec.downSepCD_apply_one (S : M.SepVec b[M ／ X, M ＼ Y]) (i : Bool) :
    S.downSepCD true i = S true i \ X := by
  -- simp only [downSepCD, downSep, Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue,
  --   Matrix.cons_val_one, Matrix.cons_val_zero, induce_apply, delete_ground, contract_ground]
  -- rw [diff_diff_comm, ← delete_ground, ← inter_diff_assoc, inter_eq_self_of_subset_left]
  -- exact (S 1).subset

lemma SepVec.diff_eq_of_contract_delete (S : M.SepVec ![M ／ X, M ＼ Y])
    (hXE : X ⊆ M.E := by aesop_mat) (hYE : Y ⊆ M.E := by aesop_mat) : S.diff = ![X, Y] :=
  funext fun i ↦ by induction i using Fin.rec2 with simpa [S.diff_eq]

lemma SepVec.diff_eq_of_contract_delete_same' (S : M.SepVec ![M ／ X, M ＼ X])  (i : Fin 2) :
    S.diff i = X ∩ M.E := by
  induction i using Fin.rec2 with simp [S.diff_eq, inter_comm]

lemma SepVec.diff_eq_of_contract_delete_same (S : M.SepVec ![M ／ X, M ＼ X])
    (hXE : X ⊆ M.E := by aesop_mat) (i : Fin 2) : S.diff i = X := by
  rw [S.diff_eq_of_contract_delete_same', inter_eq_self_of_subset_left hXE]

lemma SepVec.disjoint_of_contract_delete (S : M.SepVec ![M ／ X, M ＼ X]) (i : Fin 2) (b : Bool) :
    Disjoint (S i b) X := by
  grw [(S i).subset, S.ground_eq, S.diff_eq]
  induction i using Fin.rec2 with simp [disjoint_sdiff_left]

lemma SepVec.bixbyCoullard' (S : M.SepVec ![M ／ X, M ＼ X]) (b c i j : Bool) :
    ((S.upSep 0 (!b)).cross (S.upSep 1 (!c)) b c i).eConn +
    ((S.upSep 0 b).cross (S.upSep 1 c) (!b) (!c) j).eConn ≤
    (S 0).eConn + (S 1).eConn + M.eConn X := by
  wlog hXE : X ⊆ M.E generalizing S X with aux
  · simpa [SepVec.copyCD] using aux S.copyCD inter_subset_right
  convert M.eConn_inter_add_eConn_union_union_le (X := X) (C := S 0 b) (D := S 1 c)
    (S.disjoint_of_contract_delete ..) (S.disjoint_of_contract_delete ..)
  · simp [← Separation.eConn_eq _ i]
  · simp [← Separation.eConn_eq _ (!j), S.diff_eq_of_contract_delete_same hXE,
      show ∀ A B, A ∪ X ∪ (B ∪ X) = X ∪ A ∪ B by grind]
  · rw [← Separation.eConn_eq _ b]
    rfl
  rw [← Separation.eConn_eq _ c]
  rfl

lemma SepVec.bixbyCoullard (S : M.SepVec ![M ／ X, M ＼ X]) :
    ((S.upSep 0 false).inter (S.upSep 1 false)).eConn +
    ((S.upSep 0 true).union (S.upSep 1 true)).eConn ≤
      (S 0).eConn + (S 1).eConn + M.eConn X :=
  S.bixbyCoullard' ..


-- Deletion/Deletion

def SepVec.copyDD (S : M.SepVec b[M ＼ X, M ＼ Y]) :
    M.SepVec (fun b ↦ bif b then M ＼ (X ∩ M.E) else M ＼ (Y ∩ M.E)) :=
  S.copyMinor <| fun i ↦ by cases i with simp

def SepVec.downSepDD (S : M.SepVec ![M ＼ X, M ＼ Y]) (i : Fin 2) : (M ＼ (X ∪ Y)).Separation :=
  S.downSep (by simp [Fin.forall_fin_two, diff_subset_diff_right subset_union_left,
      diff_subset_diff_right subset_union_right]) i

-- lemma SepVec.fooDD (S : M.SepVec ![M ＼ X, M ＼ Y]) :
