import Matroid.Constructions.Relax
import Matroid.Uniform.Finite
import Matroid.ForMathlib.Matroid.Basic
import Matroid.Closure
import Matroid.ForMathlib.Matroid.Closure
import Matroid.ForMathlib.Tactic.TautoSet

open Set

variable {α : Type*} {N M : Matroid α} {B C D X : Set α} {e f : α}

namespace Matroid

/-- A `Paving` matroid is one whose truncation is uniform, or equivalently one where every
dependent set is a single insertion away from being spanning. -/
def IsPaving (M : Matroid α) : Prop := M.truncate.IsUniform

lemma IsPaving.truncate_isUniform (hM : M.IsPaving) : M.truncate.IsUniform :=
  hM

lemma IsUniform.isPaving (hM : M.IsUniform) : M.IsPaving :=
  hM.truncate

@[simp]
lemma unifOn_isPaving {E : Set α} {a : ℕ} : (unifOn E a).IsPaving :=
  IsUniform.isPaving <| by simp

@[simp]
lemma loopyOn_isPaving {E : Set α} : (loopyOn E).IsPaving :=
  IsUniform.isPaving <| by simp

@[simp]
lemma freeOn_isPaving {E : Set α} : (freeOn E).IsPaving :=
  IsUniform.isPaving <| by simp

def IsPaving.contract (hM : M.IsPaving) (C : Set α) : (M ／ C).IsPaving := by
  rw [IsPaving, truncate_contract]
  exact hM.truncate_isUniform.contract C

lemma IsPaving.eRank_contract_le_one_of_dep (hM : M.IsPaving) (hD : M.Dep D) :
    (M ／ D).eRank ≤ 1 := by
  obtain ⟨E, rfl⟩ | hpos := M.exists_eq_loopyOn_or_rankPos; simp
  obtain ⟨E, he⟩ | hpos' := (M ／ D).exists_eq_loopyOn_or_rankPos; simp [he]
  grw [← (M ／ D).truncate_eRank_add_one, truncate_contract, Spanning.contract_eq_loopyOn,
    eRank_loopyOn, zero_add]
  exact hM.truncate_isUniform.spanning_of_dep <| by simp [truncate_dep_iff, hD.not_indep,
    hD.subset_ground]

/-- In a paving matroid, any nonbase with finite exchange distance from a base is a circuit. -/
lemma IsPaving.isCircuit_of_isBase_of_finDiff_of_not_isBase (hM : M.IsPaving) (hB : M.IsBase B)
    (hBC : B.FinDiff C) (hC : ¬ M.IsBase C) (hCE : C ⊆ M.E := by aesop_mat) : M.IsCircuit C := by
  obtain ⟨E, rfl⟩ | hpos := M.exists_eq_loopyOn_or_rankPos
  · simp only [loopyOn_isBase_iff] at hC hB
    simpa [hB] using hBC.diff_nonempty_of_ne (by grind)
  obtain ⟨e, he⟩ := hB.nonempty
  obtain ⟨f, hf⟩ := hBC.nonempty_of_nonempty hB.nonempty
  have hb' : M.truncate.IsBase (C \ {f}) := hM.truncate_isUniform.isBase_of_isBase_of_finDiff
    (hB.diff_singleton_truncate_isBase he) (hBC.finDiff_diff_diff_singleton he hf) <| by grind
  have hC' := hM.truncate_isUniform.insert_isCircuit_of_isBase hb' (e := f) (by grind)
  rw [insert_diff_self_of_mem hf, truncate_isCircuit_iff, or_iff_left hC] at hC'
  exact hC'.1

lemma IsPaving.isCircuit_insert_diff_singleton_of_isBase_of_not_isBase (hM : M.IsPaving)
    (hB : M.IsBase B) (heB : e ∈ M.E \ B) (hfB : f ∈ B) (hB' : ¬ M.IsBase (insert e (B \ {f}))) :
    M.IsCircuit (insert e (B \ {f})) :=
  hM.isCircuit_of_isBase_of_finDiff_of_not_isBase hB
    (isExchange_diff_insert hfB heB.2).finDiff hB' <| by grind

lemma isPaving_iff_forall_isCircuit : M.IsPaving ↔ ∀ C, M.IsCircuit C → (M ／ C).eRank ≤ 1 := by
  refine ⟨fun h C hC ↦ h.eRank_contract_le_one_of_dep hC.dep, fun h ↦ ?_⟩
  obtain ⟨E, rfl⟩ | hpos := M.exists_eq_loopyOn_or_rankPos
  · simp
  simp only [IsPaving, isUniform_iff, or_iff_not_imp_left, truncate_indep_iff, not_and, not_not]
  intro X (hXE : X ⊆ M.E) hX
  rw [truncate_spanning_iff_eRank_contract_le]
  obtain hXi | hXd := M.indep_or_dep hXE
  · simp [(hX hXi).spanning.eRank_contract]
  obtain ⟨C, hCX, hC⟩ := hXd.exists_isCircuit_subset
  grw [← h C hC, (contract_isMinor_of_subset _ hCX).eRank_le]

def IsPaving.exists_insert_of_dep (hM : M.IsPaving) (hD : M.Dep D) :
    ∃ e ∈ M.E, M.Spanning (insert e D) := by
  obtain ⟨E, rfl⟩ := M.eq_loopyOn_or_rankPos'
  · simp only [loopyOn_ground, spanning_iff, loopyOn_closure_eq, true_and]
    obtain ⟨e, he⟩ := hD.nonempty
    exact ⟨e, hD.subset_ground he, insert_subset (hD.subset_ground he) hD.subset_ground⟩
  have h_or := hM.indep_or_spanning D hD.subset_ground
  simpa [truncate_indep_iff, truncate_spanning_iff, hD.not_indep] using h_or

/-- Every dependent set in a paving matroid contains a set that is either a base,
or an exchange away from being a base. -/
lemma IsPaving.exists_isExchange_isBase_subset_of_dep (hM : M.IsPaving) (hD : M.Dep D) :
    ∃ B, M.IsBase B ∧ (B ⊆ D ∨ ∃ X, B.IsExchange X ∧ X ⊆ D) := by
  obtain ⟨e, heE, heD⟩ := hM.exists_insert_of_dep hD
  obtain ⟨B, hB, hBeD⟩ := heD.exists_isBase_subset
  have hnss : ¬ D ⊆ B := fun hss ↦ hD.not_indep <| hB.indep.subset hss
  obtain ⟨f, hfD, hfB⟩ := not_subset.1 hnss
  by_cases hBD : B ⊆ D
  · exact ⟨B, hB, .inl hBD⟩
  exact ⟨B, hB, .inr ⟨(insert f (B \ {e})), isExchange_diff_insert (by grind) hfB, (by grind)⟩⟩

lemma IsPaving.exists_finDiff_isBase_subset_of_dep (hM : M.IsPaving) (hD : M.Dep D) :
    ∃ B X, M.IsBase B ∧ FinDiff B X ∧ X ⊆ D := by
  obtain ⟨B, hB, hBD | ⟨X, hBX, hXD⟩⟩ := hM.exists_isExchange_isBase_subset_of_dep hD
  · exact ⟨B, B, hB, by simp, hBD⟩
  exact ⟨B, X, hB, hBX.finDiff, hXD⟩

lemma paving_iff_forall_isCircuit :
    M.IsPaving ↔ ∀ C, M.IsCircuit C → ∃ e, M.Spanning (insert e C) := by
  refine ⟨fun h C hC ↦ ?_, fun h X (hXE : X ⊆ M.E) ↦ ?_⟩
  · obtain ⟨e, he⟩ := h.exists_insert_of_dep hC.dep
    exact ⟨e, he.2⟩
  obtain ⟨E, rfl⟩ | hpos := M.eq_loopyOn_or_rankPos'
  · simp [show X ⊆ E from hXE]
  rw [truncate_indep_iff, truncate_spanning_iff, ← not_dep_iff, ← not_or, ← imp_iff_not_or]
  rintro (hX | hX)
  · obtain ⟨C, hCX, hC⟩ := hX.exists_isCircuit_subset
    obtain ⟨e, he⟩ := h C hC
    have heE := he.subset_ground <| mem_insert _ _
    exact ⟨e, heE, he.superset (insert_subset_insert hCX)⟩
  obtain ⟨e, he⟩ := hX.nonempty
  exact ⟨e, hX.subset_ground he, by simp [he, hX.spanning]⟩

def IsPaving.exists_insert_of_dep_of_ssubset (hM : M.IsPaving) (hD : M.Dep D) (hDE : D ⊂ M.E) :
    ∃ e ∈ M.E \ D, M.Spanning (insert e D) := by
  obtain ⟨e, he, heD⟩ := hM.exists_insert_of_dep hD
  by_cases he' : e ∈ D
  · obtain ⟨f, hf⟩ := exists_of_ssubset hDE
    rw [insert_eq_of_mem he'] at heD
    exact ⟨f, hf, heD.superset (subset_insert _ _)⟩
  exact ⟨e, ⟨he, he'⟩, heD⟩

lemma IsPaving.insert_spanning_of_dep_of_notMem_closure (hM : M.IsPaving) (hD : M.Dep D)
    (he : e ∈ M.E \ M.closure D) : M.Spanning (insert e D) := by
  obtain ⟨f, -, hf⟩ := hM.exists_insert_of_dep hD
  rw [spanning_iff_closure_eq]
  have hf' := mem_closure_insert he.2 (f := f) (by simpa [hf.closure_eq] using he.1)
  rw [← closure_closure, ← insert_eq_of_mem hf', closure_insert_closure_eq_closure_insert,
    insert_comm, ← closure_insert_closure_eq_closure_insert, hf.closure_eq,
    insert_eq_of_mem he.1, closure_ground]

lemma IsPaving.closure_isHyperplane_of_dep_of_nonspanning (hM : M.IsPaving) (hD : M.Dep D)
    (hDs : M.Nonspanning D) : M.IsHyperplane (M.closure D) := by
  rw [isHyperplane_iff_maximal_nonspanning, maximal_iff_forall_insert,
    ← not_spanning_iff, spanning_iff_closure_eq,
    closure_closure, ← spanning_iff_closure_eq, and_iff_right hDs.not_spanning]
  · refine fun e he' h ↦ h.1 ?_
    have heE : e ∈ M.E := h.subset_ground (.inl rfl)
    rw [spanning_iff_closure_eq, closure_insert_closure_eq_closure_insert,
      (hM.insert_spanning_of_dep_of_notMem_closure hD ⟨heE, he'⟩).closure_eq]
  exact fun S T ⟨hT, hTE⟩ hST ↦ ⟨fun hS ↦ hT <| hS.superset hST, hST.trans hTE⟩

lemma IsPaving.restrict_uniform_of_nonspanning {R : Set α} (hM : M.IsPaving)
    (hRs : M.Nonspanning R) : (M ↾ R).IsUniform := by
  intro X (hXR : X ⊆ R)
  rw [restrict_indep_iff, restrict_spanning_iff hXR, and_iff_left hXR, or_iff_not_imp_left,
    not_indep_iff (hXR.trans hRs.subset_ground)]
  intro hXd
  have h1 := hM.closure_isHyperplane_of_dep_of_nonspanning (hXd.superset hXR) hRs
  have h2 := hM.closure_isHyperplane_of_dep_of_nonspanning hXd (hRs.subset hXR)
  rw [h2.eq_of_subset h1 (M.closure_subset_closure hXR)]
  exact M.subset_closure R

lemma IsPaving.eRelRk_ground_le_of_dep (hM : M.IsPaving) (h : M.Dep D) : M.eRelRk D M.E ≤ 1 := by
  rw [← eRelRk_closure_left]
  obtain h' | h' := M.spanning_or_nonspanning D
  · simp [h'.closure_eq]
  rw [(hM.closure_isHyperplane_of_dep_of_nonspanning h h').eRelRk_eq_one]

lemma IsPaving.eRank_le_eRk_add_one_of_dep (hM : M.IsPaving) (h : M.Dep D) :
    M.eRank ≤ M.eRk D + 1 := by
  grw [← eRk_ground, ← M.eRelRk_add_eRk_of_subset h.subset_ground, hM.eRelRk_ground_le_of_dep h,
    add_comm]

def IsPaving.delete (hM : M.IsPaving) (D : Set α) : (M ＼ D).IsPaving := by
  suffices aux : ∀ D ⊆ M.E, (M ＼ D).IsPaving
  · convert aux (D ∩ M.E) inter_subset_right using 1; simp [delete_inter_ground_eq]
  clear D
  intro D hDE
  rw [IsPaving]
  by_cases hD : M.Coindep D
  · rw [hD.truncate_delete]
    exact hM.truncate_isUniform.delete D
  rw [delete_eq_restrict]
  refine (hM.restrict_uniform_of_nonspanning ?_).truncate
  rwa [nonspanning_compl_iff, ← not_coindep_iff]
def IsPaving.isMinor (hM : M.IsPaving) (hNM : N ≤m M) : N.IsPaving := by
  obtain ⟨C, D, -, -, -, rfl⟩ := hNM
  exact (hM.contract _).delete _

lemma IsPaving.exists_diff_indep_of_nonspanning (hM : M✶.IsPaving) (hXs : M.Nonspanning X)
    (hne : X.Nonempty) : ∃ f ∈ X, M.Indep (X \ {f}) := by
  have hd : M✶.Dep (M.E \ X) := by rwa [← codep_def, codep_compl_iff]
  have hssu : M.E \ X ⊂ M.E := diff_ssubset hXs.subset_ground hne
  obtain ⟨f, hf, h⟩ := hM.exists_insert_of_dep_of_ssubset hd hssu
  rw [spanning_dual_iff, ← union_singleton, ← diff_diff,
    diff_diff_cancel_left hXs.subset_ground] at h
  simp only [dual_ground, sdiff_sdiff_right_self, inf_eq_inter, mem_inter_iff] at hf
  exact ⟨f, hf.2, h⟩

lemma IsPaving.encard_eq_or_eq_of_isCircuit (hM : M.IsPaving) (hC : M.IsCircuit C) :
    C.encard = M.eRank ∨ C.encard = M.eRank + 1 := by
  have := hM.eRelRk_ground_le_of_dep hC.dep
  rw [← eRk_ground, ← M.eRelRk_add_eRk_of_subset hC.subset_ground, ← hC.eRk_add_one_eq]
  eomega

/-- Every base in a non-free paving matroid is nearly a circuit. -/
lemma IsPaving.exists_isCircuit_of_isBase [M✶.RankPos] (hM : M.IsPaving) (hB : M.IsBase B) :
    ∃ C, M.IsCircuit C ∧ (C \ B).Subsingleton ∧ (B \ C).Subsingleton := by
  obtain rfl | hssu := hB.subset_ground.eq_or_ssubset
  · exact (M✶.eRank_ne_zero (by simp [← hB.compl_isBase_dual.encard_eq_eRank])).elim
  obtain ⟨e, heE, heB⟩ := exists_of_ssubset hssu
  obtain ⟨C, hCss, hC⟩ := (hB.insert_dep ⟨heE, heB⟩).exists_isCircuit_subset
  refine ⟨C, hC, ?_, ?_⟩
  · exact Subsingleton.anti (by simp [insert_diff_eq_singleton heB]) (diff_subset_diff_left hCss)
  rw [show B \ C = B \ (C \ {e}) by tauto_set!, ← encard_le_one_iff_subsingleton,
    ← hB.indep.eRelRk_of_subset (by simpa [diff_subset_iff]), ← eRelRk_closure_left,
    hC.closure_diff_singleton_eq, eRelRk_closure_left, ← eRelRk_closure_right, hB.closure_eq]
  exact hM.eRelRk_ground_le_of_dep hC.dep

/-- Every spanning set in a non-free paving matroid nearly contains a circuit. -/
lemma IsPaving.exists_isCircuit_of_spanning [M✶.RankPos] (hM : M.IsPaving) (hX : M.Spanning X) :
    ∃ C, M.IsCircuit C ∧ (C \ X).Subsingleton := by
  obtain ⟨B, hB, hBX⟩ := hX.exists_isBase_subset
  obtain ⟨C, hC, h, -⟩ := hM.exists_isCircuit_of_isBase hB
  exact ⟨C, hC, h.anti <| diff_subset_diff_right hBX⟩

/-- Every independent set in a non-free paving matroid is nearly contained in a circuit. -/
lemma IsPaving.exists_isCircuit_of_indep {I : Set α} [M✶.RankPos] (hM : M.IsPaving)
    (hI : M.Indep I) : ∃ C, M.IsCircuit C ∧ (I \ C).Subsingleton := by
  obtain ⟨B, hB, hIB⟩ := hI.exists_isBase_superset
  obtain ⟨C, hC, -, h⟩ := hM.exists_isCircuit_of_isBase hB
  exact ⟨C, hC, h.anti <| diff_subset_diff_left hIB⟩

lemma isPaving_iff_girth_ge [M.Finitary] : M.IsPaving ↔ M.eRank ≤ M.girth := by
  rw [isPaving_iff_forall_isCircuit, le_girth_iff]
  refine ⟨fun h C hC ↦ ?_, fun h C hC ↦ ?_⟩
  · grw [← M.eRank_contract_add_eRk C, h C hC, add_comm, hC.eRk_add_one_eq]
  specialize h C hC
  rwa [← M.eRank_contract_add_eRk C, ← hC.eRk_add_one_eq, add_comm, ENat.add_le_add_iff_left] at h
  rw [Ne, ← ENat.add_one_inj, hC.eRk_add_one_eq]
  simpa using hC.finite

/-- A `SparsePaving` matroid is a paving matroid with paving dual,
or equivalently one where every nonspanning dependent set is a circuit-hyperplane. -/
@[mk_iff]
structure IsSparsePaving (M : Matroid α) : Prop where
  isPaving : M.IsPaving
  isPaving_dual : M✶.IsPaving

theorem IsSparsePaving.dual (h : M.IsSparsePaving) : M✶.IsSparsePaving := by
  rwa [isSparsePaving_iff, dual_dual, and_comm, ← isSparsePaving_iff]

lemma IsUniform.isSparsePaving (h : M.IsUniform) : M.IsSparsePaving :=
  ⟨h.truncate, h.dual.truncate⟩

@[simp]
lemma IsSparsePaving_loopyOn (E : Set α) : (loopyOn E).IsSparsePaving :=
  IsUniform.isSparsePaving <| by simp

@[simp]
lemma IsSparsePaving_freeOn (E : Set α) : (freeOn E).IsSparsePaving :=
  IsUniform.isSparsePaving <| by simp

@[simp]
lemma IsSparsePaving_unifOn (E : Set α) (a : ℕ) : (unifOn E a).IsSparsePaving :=
  IsUniform.isSparsePaving <| by simp

@[simp]
lemma dual_isSparsePaving_iff : M✶.IsSparsePaving ↔ M.IsSparsePaving :=
  ⟨fun h ↦ by simpa using h.dual, IsSparsePaving.dual⟩

theorem IsSparsePaving.minor (h : M.IsSparsePaving) (hNM : N ≤m M) : N.IsSparsePaving :=
  ⟨h.1.isMinor hNM, h.dual.1.isMinor hNM.dual⟩

/-- Every nonspanning dependent set in a sparse paving matroid is a circuit-hyperplane. -/
lemma IsSparsePaving.isCircuitHyperplane_of_dep_of_nonspanning (hM : M.IsSparsePaving)
    (hC : M.Dep C) (hCs : M.Nonspanning C) : M.IsCircuitHyperplane C := by
  -- since `C` is a dependent set in a paving matroid, it contains a set `X` of finite exchange
  -- distance from a base.
  obtain ⟨B, X, hB, hBX, hXC⟩ := hM.isPaving.exists_finDiff_isBase_subset_of_dep hC
  -- since `M.E \ C` is co-dependent in a co-paving matroid, it contains a set `Y` of
  -- finite exchange distance from a co-base.
  have hd := hM.isPaving_dual.exists_finDiff_isBase_subset_of_dep (D := M.E \ C)
  rw [dep_dual_iff, codep_compl_iff, imp_iff_right hCs] at hd
  obtain ⟨B', Y, hB', hB'Y, hYC⟩ := hd
  have hfd := hB'Y.diff_right (show B' ⊆ M.E from hB'.subset_ground) (hYC.trans diff_subset)
  -- This means that `X ⊆ C ⊆ M.E \ Y`, and both `X` and `M.E \ Y` have finite exchange distance
  -- from bases of `M`. But these sets form an antichain, so `X = C = M.E \ Y`.
  obtain rfl : X = M.E \ Y := M.isAntichain_setOf_finDiff_isBase.eq (a := X) (b := M.E \ Y)
    (by grind) (by grind [hB'.compl_isBase_of_dual]) (by grind)
  obtain rfl : C = M.E \ Y := by grind
  -- Now `M.E \ Y` is dependent and has finite exchange distance from a base in a paving matroid,
  -- so is a circuit. Dually, `Y` is a cocircuit, so `M.E \ Y` is a hyperplane.
  have hC := hM.isPaving.isCircuit_of_isBase_of_finDiff_of_not_isBase hB hBX
    (fun h ↦ hC.not_indep h.indep)
  have hC' := hM.isPaving_dual.isCircuit_of_isBase_of_finDiff_of_not_isBase hB' hB'Y (fun h ↦ ?_)
  · exact ⟨hC, (M.dual_dual ▸ hC'.isCocircuit).compl_isHyperplane⟩
  exact hCs.not_spanning <| (M.dual_dual ▸ h.indep.coindep).compl_spanning

theorem IsSparsePaving.indep_or_spanning_or_isCircuitHyperplane (hM : M.IsSparsePaving)
    (hXE : X ⊆ M.E) : M.Indep X ∨ M.Spanning X ∨ M.IsCircuitHyperplane X := by
  obtain hX | hX := M.indep_or_dep hXE; simp [hX]
  obtain hX' | hX' := M.spanning_or_nonspanning X hXE; simp [hX']
  simp [hM.isCircuitHyperplane_of_dep_of_nonspanning hX hX']

theorem isSparsePaving_iff_forall_indep_or_spanning_or_isCircuitHyperplane :
    M.IsSparsePaving ↔ ∀ X ⊆ M.E, M.Indep X ∨ M.Spanning X ∨ M.IsCircuitHyperplane X := by
  refine ⟨fun h X hXE ↦ h.indep_or_spanning_or_isCircuitHyperplane hXE, fun h ↦ ⟨?_, ?_⟩⟩
  · simp only [IsPaving, isUniform_iff, truncate_ground_eq, truncate_indep_iff']
    grind [IsBase.spanning, Spanning.truncate_spanning, IsCircuitHyperplane.isHyperplane,
      IsHyperplane.truncate_spanning]
  simp only [IsPaving, isUniform_iff, truncate_ground_eq, truncate_indep_iff']
  intro X hXE
  specialize h (M.E \ X) diff_subset
  rw [← coindep_iff_compl_spanning, Coindep, ← dual_coindep_iff, coindep_iff_compl_spanning,
    dual_ground, diff_diff_cancel_left (by simpa), ← isCircuitHyperplane_dual_iff] at h
  grind [IsBase.spanning, Spanning.truncate_spanning, IsCircuitHyperplane.isHyperplane,
      IsHyperplane.truncate_spanning]

theorem IsSparsePaving.isBase_or_isCircuitHyperplane_of_finDiff (h : M.IsSparsePaving)
    (hB : M.IsBase B) (hX : X ⊆ M.E) (hBX : FinDiff B X) :
    M.IsBase X ∨ M.IsCircuitHyperplane X := by
  rw [or_iff_not_imp_left]
  intro hnb
  have hc := h.isPaving.isCircuit_of_isBase_of_finDiff_of_not_isBase hB hBX hnb
  have hcc := h.isPaving_dual.isCircuit_of_isBase_of_finDiff_of_not_isBase
    hB.compl_isBase_dual (hBX.diff_right hB.subset_ground hX)
    (by rwa [← base_iff_dual_isBase_compl])
  rw [← isCocircuit_def, isCocircuit_compl_iff_isHyperplane] at hcc
  exact ⟨hc, hcc⟩

section Relax

lemma IsSparsePaving.relax_all_isUniform (h : M.IsSparsePaving) :
    (M.relax {C | M.IsCircuitHyperplane C} (IsLawfulRelaxation.all M)).IsUniform := by
  simp only [isUniform_iff, relax_E, relax_Indep, mem_setOf_eq, relax_spanning_iff]
  grind [h.indep_or_spanning_or_isCircuitHyperplane]


lemma IsSparsePaving.exists_eq_relax_unifOn [M.RankFinite] (hM : M.IsSparsePaving) :
    ∃ (E : Set α) (r : ℕ), M.eRank = r ∧ E = M.E ∧ ∃ (T : Set (Set α))
    (h : (unifOn E r).IsLawfulTightening T), M = (unifOn E r).tighten T h := by
  obtain ⟨E, k, hkE, heq, hr⟩ := hM.relax_all_isUniform.exists_eq_unifOn
  have hh := (IsLawfulRelaxation.all M).isLawfulTightening_relax
  rw [heq] at hh
  simp only [relax_eRank_eq] at hr
  refine ⟨E, k, hr, ?_, _, hh, by simp_rw [← heq, IsLawfulRelaxation.tighten_relax]⟩
  simpa using congr_arg Matroid.E heq.symm

/-- A rank-`r` sparse paving matroid, specified by its set of circuit-hyperplanes.
`H` should be any set of `r`-sets, no two differing by a single exchange. -/
def finiteRankSparsePavingOn (E : Set α) (H : Set (Set α)) (r : ℕ)
    (card_eq : ∀ C ∈ H, C.encard = r) (exchange : H.Pairwise (fun C C' ↦ ¬ IsExchange C C'))
    (nonempty : ∀ C ∈ H, C.Nonempty) (ssubset_ground : ∀ C ∈ H, C ⊂ E) : Matroid α :=
  (unifOn E r).tighten H ⟨
    fun B hBH ↦ (unifOn_isUniform E r).isFreeBase <| by
      rw [unifOn_isBase_iff _ (ssubset_ground B hBH).subset, card_eq B hBH]
      grw [← card_eq B hBH, (ssubset_ground B hBH)],
    by grind [Set.Pairwise], fun hEH ↦ (ssubset_ground E hEH).ne rfl, by grind [Nonempty.ne_empty]⟩

lemma IsSparsePaving.exists_eq_finiteRankSparsePavingOn [M.RankFinite] (hM : M.IsSparsePaving) :
    ∃ (E : Set α) (r : ℕ) (T : Set (Set α)) (card_eq : _) (exchange : _) (nonempty : _)
        (ssubset_ground : _), M.eRank = r ∧ E = M.E ∧
        M = finiteRankSparsePavingOn E T r card_eq exchange nonempty ssubset_ground := by
  have h := (IsLawfulRelaxation.all M).isLawfulTightening_relax
  obtain ⟨E, k, hkE, h_eq, hk⟩ := hM.relax_all_isUniform.exists_eq_unifOn
  obtain rfl : k = M.rank := by simpa [← ENat.coe_inj] using hk.symm
  refine ⟨M.E, M.rank, {H | M.IsCircuitHyperplane H},
    fun C hC ↦ by simp [h.encard_eq_eRank_of_mem hC], h.pairwise_not_isExchange,
      fun _ ↦ h.nonempty, fun _ ↦ h.ssubset_ground, by simp, by simp, ?_⟩
  rw [finiteRankSparsePavingOn]
  obtain rfl : E = M.E := by simpa using congr_arg Matroid.E h_eq.symm
  simp [← h_eq]




  -- refine ⟨M.E, M.rank, {H | M.IsCircuitHyperplane H}, ?_⟩
  -- simp [cast_rank_eq, finiteRankSparsePavingOn, true_and, mem_setOf_eq]



  -- refine ⟨M.E, M.rank, {H | M.IsCircuitHyperplane H}, ?_, ?_, ?_, ?_, by simp, by simp, ?_⟩


  -- obtain ⟨E, k, hkE, heq, hr⟩ := hM.relax_all_isUniform.exists_eq_unifOn
  -- have hh := (IsLawfulRelaxation.all M).isLawfulTightening_relax

    --  M.eRank = r ∧ E = M.E ∧ ∃ (T : Set (Set α))
