import Matroid.Extension.ProjectBy
import Matroid.Extension.Guts


open Set Function Set.Notation Option Matroid.ModularCut

variable {α : Type*} {M : Matroid α} {I J B F₀ F F' X Y : Set α} {e f : α} {U : M.ModularCut}

namespace Matroid

/-- The projection of `M` corresponding to adding a point freely in the span of `X`,
the contracting it. -/
def principalTruncate (M : Matroid α) (X : Set α) : Matroid α :=
    M.projectBy (ModularCut.principal M X)

@[simp]
lemma principalTruncate_ground (M : Matroid α) (X : Set α) : (M.principalTruncate X).E = M.E := rfl

lemma principalTruncate_eq_truncate (hX : M.Spanning X) : M.principalTruncate X = M.truncate := by
  rw [principalTruncate, ← principal_closure_eq, hX.closure_eq, ← truncate_def]

lemma principalTruncate_dep_self {X : Set α} (hXne : X.Nonempty) (hXE : X ⊆ M.E := by aesop_mat) :
    (M.principalTruncate X).Dep X := by
  rw [dep_iff, and_iff_left (by simpa), principalTruncate, projectBy_indep_iff]
  suffices M.Indep X → ¬ (X ∩ M.E) ⊆ M.loops by
    simpa [ModularCut.eq_top_iff, mem_principal_iff', inter_ground_subset_closure, loops]
  intro hXi h
  have hdj := hXi.disjoint_loops.mono_right h
  simp [inter_eq_self_of_subset_left hXE, hXne.ne_empty] at hdj

lemma principalTruncate_eRk_eq_eRk (M : Matroid α) (hY : ¬ (X ⊆ M.closure Y))
    (hX : X ⊆ M.E := by aesop_mat) : (M.principalTruncate X).eRk Y = M.eRk Y := by
  rw [← eRank_restrict, principalTruncate, ← projectBy_restrict,
    (ModularCut.principal_restrict_eq_bot_iff hX).2 hY, projectBy_bot, eRank_restrict]

lemma principalTruncate_eRk_add_one_eq (M : Matroid α) (hX : ¬ (X ⊆ M.loops))
    (hY : X ⊆ M.closure Y) : (M.principalTruncate X).eRk Y + 1 = M.eRk Y := by
  rw [← eRank_restrict, principalTruncate, ← projectBy_restrict, projectBy_eRank_add_one_eq,
    eRank_restrict]
  · rwa [Ne, principal_restrict_eq_top_iff]
  rwa [Ne, principal_restrict_eq_bot_iff, not_not]

/-- Lift `M` using the principal co-modular cut given by a set `X`.
I don't know the right intuitive way to think about this. -/
def principalLift (M : Matroid α) (X : Set α) : Matroid α := M.liftBy (ModularCut.principal M✶ X)

@[simp]
lemma principalLift_ground (M : Matroid α) (X : Set α) : (M.principalLift X).E = M.E := rfl

@[simp]
lemma principalLift_dual (M : Matroid α) (X : Set α) :
    (M.principalLift X)✶ = M✶.principalTruncate X := by
  rw [principalLift, liftBy_dual, principalTruncate]

@[simp]
lemma principalTruncate_dual (M : Matroid α) (X : Set α) :
    (M.principalTruncate X)✶ = M✶.principalLift X := by
  rw [eq_comm, eq_dual_comm, principalLift_dual, dual_dual]

lemma principalLift_codep (M : Matroid α) (hXne : X.Nonempty) (hX : X ⊆ M.E := by aesop_mat) :
    (M.liftBy (ModularCut.principal M✶ X)).Codep X := by
  rw [Codep, liftBy_dual]
  exact principalTruncate_dep_self hXne hX

/-- Project `M` by a point placed in the guts of the separation `(X, M.E \ X)`. -/
def gutsProject (M : Matroid α) (X : Set α) : Matroid α := M.projectBy (M.gutsModularCutSet X)

lemma gutsProject_compl (M : Matroid α) (X : Set α) :
    M.gutsProject (M.E \ X) = M.gutsProject X := by
  rw [gutsProject, gutsModularCutSet_compl, gutsProject]

lemma spanning_of_gutsProject_spanning_of_union_eq (hci : (M.gutsProject X).Spanning Y)
    (hXY : X ∪ Y = M.E) : M.Spanning Y := by
  contrapose! hci
  rw [gutsProject, ModularCut.projectBy_spanning_iff (by simp) (by grind),
    closure_mem_gutsModularCutSet_iff (by grind), or_iff_right hci, not_and, not_not]
  refine fun _ ↦ (skew_of_subset_loops ?_ ?_).symm
  <;> grind [project_loops]

lemma spanning_of_gutsProject_spanning_of_superset (hci : (M.gutsProject X).Spanning Y)
    (hXY : X ⊆ Y) : M.Spanning Y := by
  have hYE : Y ⊆ M.E := by simpa using hci.subset_ground
  contrapose! hci
  rw [gutsProject, ModularCut.projectBy_spanning_iff (by simp) (by grind),
    closure_mem_gutsModularCutSet_iff (by grind), or_iff_right hci, not_and, not_not]
  exact fun _ ↦ (skew_of_subset_loops (by grind [project_loops]) diff_subset)

/-- The matroid obtained from `M` by lifting the points of `X` outside the span of `M.E \ X`.
The restriction to `X` or its complement remains unchanged, but `X` becomes codependent.  -/
def localLift (M : Matroid α) (X : Set α) : Matroid α := M.liftBy (M✶.gutsModularCutSet X)

@[simp]
lemma localLift_ground (M : Matroid α) (X : Set α) : (M.localLift X).E = M.E := rfl

@[simp]
lemma localLift_dual (M : Matroid α) (X : Set α) : (M.localLift X)✶ = M✶.gutsProject X := by
  rw [localLift, liftBy_dual, gutsProject]

@[simp]
lemma gutsProject_dual (M : Matroid α) (X : Set α) : (M.gutsProject X)✶ = M✶.localLift X := by
  rw [gutsProject, localLift, ← projectBy_dual]
  convert rfl
  simp

lemma localLift_compl (M : Matroid α) (X : Set α) : M.localLift (M.E \ X) = M.localLift X := by
  rw [← dual_inj, localLift_dual, ← dual_ground, gutsProject_compl, localLift_dual]

lemma localLift_delete_self : (M.localLift X) ＼ X = M ＼ X := by
  rw [← dual_inj, dual_delete, localLift_dual, gutsProject, projectBy_contract,
    (contract_eq_top_iff _).2 (by simp), projectBy_top, dual_delete]

lemma localLift_restrict_self : (M.localLift X) ↾ X = M ↾ X := by
  wlog hXE : X ⊆ M.E generalizing X with aux
  · rw [← restrict_inter_ground_restrict, localLift, liftBy_ground,
      ← gutsModularCutSet_inter_ground, dual_ground, ← localLift, aux inter_subset_right,
      restrict_inter_ground_restrict]
  rw [← delete_compl, ← delete_compl, localLift_ground, ← localLift_compl, localLift_delete_self]

lemma localLift_codep_self (hX : X ⊆ M.E) (hXr : M.eRk X ≠ 0) : (M.localLift X).Codep X := by
  rw [localLift, liftBy, codep_dual_iff, ← not_indep_iff, projectBy_indep_iff,
    closure_mem_gutsModularCutSet_iff, Ne, gutsModularCutSet_eq_top_iff, not_and,
    not_imp_not, Classical.not_imp]
  refine fun (hXi : M.Coindep X) ↦
    ⟨(skew_of_subset_loops (by grind [project_loops]) diff_subset), ?_⟩
  rwa [← eLocalConn_eq_zero, ← eConn_eq_eLocalConn, eConn_dual, hXi.eConn_eq]
