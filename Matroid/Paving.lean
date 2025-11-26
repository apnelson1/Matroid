import Matroid.Uniform
import Matroid.ForMathlib.Matroid.Basic
import Matroid.Closure
import Matroid.ForMathlib.Matroid.Closure
import Matroid.ForMathlib.Tactic.TautoSet

open Set

variable {α : Type*} {N M : Matroid α} {B C D X : Set α} {e f : α}

namespace Matroid



/-- A `Paving` matroid is one whose truncation is uniform, or equivalently one where every
dependent set is a single insertion away from being spanning. -/
def Paving (M : Matroid α) : Prop := M.truncate.IsUniform

lemma Paving.truncate_uniform (hM : M.Paving) : M.truncate.IsUniform :=
  hM

/-- A Paving matroid is one where every circuit is spanning or nearly-spanning. -/
def Paving.exists_insert_of_dep (hM : M.Paving) (hD : M.Dep D) :
    ∃ e ∈ M.E, M.Spanning (insert e D) := by
  obtain ⟨E, rfl⟩ := M.eq_loopyOn_or_rankPos'
  · simp only [loopyOn_ground, spanning_iff, loopyOn_closure_eq, true_and]
    obtain ⟨e, he⟩ := hD.nonempty
    exact ⟨e, hD.subset_ground he, insert_subset (hD.subset_ground he) hD.subset_ground⟩
  have h_or := hM.indep_or_spanning D hD.subset_ground
  simpa [truncate_indep_iff, truncate_spanning_iff, hD.not_indep] using h_or

lemma paving_iff_forall_isCircuit :
    M.Paving ↔ ∀ C, M.IsCircuit C → ∃ e, M.Spanning (insert e C) := by
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

def Paving.exists_insert_of_dep_of_ssubset (hM : M.Paving) (hD : M.Dep D) (hDE : D ⊂ M.E) :
    ∃ e ∈ M.E \ D, M.Spanning (insert e D) := by
  obtain ⟨e, he, heD⟩ := hM.exists_insert_of_dep hD
  by_cases he' : e ∈ D
  · obtain ⟨f, hf⟩ := exists_of_ssubset hDE
    rw [insert_eq_of_mem he'] at heD
    exact ⟨f, hf, heD.superset (subset_insert _ _)⟩
  exact ⟨e, ⟨he, he'⟩, heD⟩

lemma Paving.insert_spanning_of_dep_of_notMem_closure (hM : M.Paving) (hD : M.Dep D)
    (he : e ∈ M.E \ M.closure D) : M.Spanning (insert e D) := by
  obtain ⟨f, -, hf⟩ := hM.exists_insert_of_dep hD
  rw [spanning_iff_closure_eq]
  have hf' := mem_closure_insert he.2 (f := f) (by simpa [hf.closure_eq] using he.1)
  rw [← closure_closure, ← insert_eq_of_mem hf', closure_insert_closure_eq_closure_insert,
    insert_comm, ← closure_insert_closure_eq_closure_insert, hf.closure_eq,
    insert_eq_of_mem he.1, closure_ground]

lemma Paving.closure_isHyperplane_of_dep_of_nonspanning (hM : M.Paving) (hD : M.Dep D)
    (hDs : M.Nonspanning D) : M.IsHyperplane (M.closure D) := by
  rw [isHyperplane_iff_maximal_nonspanning, maximal_iff_forall_insert,
    ← not_spanning_iff, spanning_iff_closure_eq,
    closure_closure, ← spanning_iff_closure_eq, and_iff_right hDs.not_spanning]
  · refine fun e he' h ↦ h.1 ?_
    have heE : e ∈ M.E := h.subset_ground (.inl rfl)
    rw [spanning_iff_closure_eq, closure_insert_closure_eq_closure_insert,
      (hM.insert_spanning_of_dep_of_notMem_closure hD ⟨heE, he'⟩).closure_eq]
  exact fun S T ⟨hT, hTE⟩ hST ↦ ⟨fun hS ↦ hT <| hS.superset hST, hST.trans hTE⟩

lemma Paving.isBase_exchange_isCircuit_of_not_isBase (hM : M.Paving) (hB : M.IsBase B)
    (heB : e ∈ M.E \ B) (hfB : f ∈ B) (hB' : ¬ M.IsBase (insert e (B \ {f}))) :
    M.IsCircuit (insert e (B \ {f})) := by
  replace hB' := show M.Dep (insert e (B \ {f})) by
    rw [dep_iff, and_iff_left (insert_subset heB.1 (diff_subset.trans hB.subset_ground))]
    contrapose! hB'
    refine hB.exchange_isBase_of_indep heB.2 hB'
  obtain ⟨C, hCB', hC⟩ := hB'.exists_isCircuit_subset
  have hcl : f ∉ M.closure C := by
    rw [← hC.closure_diff_singleton_eq e]
    exact notMem_subset (M.closure_subset_closure (by simpa)) <|
      hB.indep.notMem_closure_diff_of_mem hfB
  have hfC : f ∉ C := notMem_subset (M.subset_closure C) hcl
  have hCsp := hM.insert_spanning_of_dep_of_notMem_closure hC.dep ⟨hB.subset_ground hfB, hcl⟩
  have hss : insert f (C \ {e}) ⊆ B
  · refine insert_subset hfB ?_
    rw [diff_singleton_subset_iff]
    exact hCB'.trans (insert_subset_insert diff_subset)
  rw [spanning_iff, ← closure_insert_closure_eq_closure_insert,
    ← hC.closure_diff_singleton_eq e, closure_insert_closure_eq_closure_insert] at hCsp
  have h_eq : insert f (C \ {e}) = B :=
    hB.indep.eq_of_spanning_subset (by rw [spanning_iff_closure_eq, hCsp.1]) hss
  have hef : e ≠ f := by rintro rfl; exact heB.2 hfB
  have heC : e ∈ C
  · by_contra heC
    rw [← diff_singleton_subset_iff, diff_singleton_eq_self heC] at hCB'
    exact hC.dep.not_indep (hB.indep.subset (hCB'.trans diff_subset))
  rwa [← h_eq, insert_diff_of_mem _ (show f ∈ {f} from rfl), insert_diff_singleton_comm hef,
    insert_diff_singleton, diff_singleton_eq_self (by simp [hef.symm, hfC]), insert_eq_of_mem heC]

lemma Paving.restrict_uniform_of_nonspanning {R : Set α} (hM : M.Paving) (hRs : M.Nonspanning R) :
    (M ↾ R).IsUniform := by
  intro X (hXR : X ⊆ R)
  rw [restrict_indep_iff, restrict_spanning_iff hXR, and_iff_left hXR, or_iff_not_imp_left,
    not_indep_iff (hXR.trans hRs.subset_ground)]
  intro hXd
  have h1 := hM.closure_isHyperplane_of_dep_of_nonspanning (hXd.superset hXR) hRs
  have h2 := hM.closure_isHyperplane_of_dep_of_nonspanning hXd (hRs.subset hXR)
  rw [h2.eq_of_subset h1 (M.closure_subset_closure hXR)]
  exact M.subset_closure R

lemma Paving.eRelRk_ground_le_of_dep (hM : M.Paving) (h : M.Dep D) : M.eRelRk D M.E ≤ 1 := by
  rw [← eRelRk_closure_left]
  obtain h' | h' := M.spanning_or_nonspanning D
  · simp [h'.closure_eq]
  rw [(hM.closure_isHyperplane_of_dep_of_nonspanning h h').eRelRk_eq_one]

lemma Paving.eRank_le_eRk_add_one_of_dep (hM : M.Paving) (h : M.Dep D) : M.eRank ≤ M.eRk D + 1 := by
  grw [← eRk_ground, ← M.eRelRk_add_eRk_of_subset h.subset_ground, hM.eRelRk_ground_le_of_dep h,
    add_comm]

def Paving.delete (hM : M.Paving) (D : Set α) : (M ＼ D).Paving := by
  suffices aux : ∀ D ⊆ M.E, (M ＼ D).Paving
  · convert aux (D ∩ M.E) inter_subset_right using 1; simp [delete_inter_ground_eq]
  clear D
  intro D hDE
  rw [Paving]
  by_cases hD : M.Coindep D
  · rw [hD.truncate_delete]
    exact hM.truncate_uniform.delete D
  rw [delete_eq_restrict]
  refine (hM.restrict_uniform_of_nonspanning ?_).truncate
  rwa [nonspanning_compl_iff, ← not_coindep_iff]

def Paving.contract (hM : M.Paving) (C : Set α) : (M ／ C).Paving := by
  rw [Paving, truncate_contract]
  exact hM.truncate_uniform.contract C

def Paving.minor (hM : M.Paving) (hNM : N ≤m M) : N.Paving := by
  rw [hNM.eq_con_del]
  exact (hM.contract _).delete _

lemma Paving.exists_diff_indep_of_nonspanning (hM : M✶.Paving) (hXs : M.Nonspanning X)
    (hne : X.Nonempty) : ∃ f ∈ X, M.Indep (X \ {f}) := by
  have hd : M✶.Dep (M.E \ X) := by rwa [← codep_def, codep_compl_iff]
  have hssu : M.E \ X ⊂ M.E := diff_ssubset hXs.subset_ground hne
  obtain ⟨f, hf, h⟩ := hM.exists_insert_of_dep_of_ssubset hd hssu
  rw [spanning_dual_iff, ← union_singleton, ← diff_diff,
    diff_diff_cancel_left hXs.subset_ground] at h
  simp only [dual_ground, sdiff_sdiff_right_self, inf_eq_inter, mem_inter_iff] at hf
  exact ⟨f, hf.2, h⟩

lemma Paving.encard_eq_or_eq_of_isCircuit (hM : M.Paving) (hC : M.IsCircuit C) :
    C.encard = M.eRank ∨ C.encard = M.eRank + 1 := by
  have := hM.eRelRk_ground_le_of_dep hC.dep
  rw [← eRk_ground, ← M.eRelRk_add_eRk_of_subset hC.subset_ground, ← hC.eRk_add_one_eq]
  eomega

/-- Every base in a non-free paving matroid is nearly a circuit. -/
lemma Paving.exists_isCircuit_of_isBase [M✶.RankPos] (hM : M.Paving) (hB : M.IsBase B) :
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
lemma Paving.exists_isCircuit_of_spanning [M✶.RankPos] (hM : M.Paving) (hX : M.Spanning X) :
    ∃ C, M.IsCircuit C ∧ (C \ X).Subsingleton := by
  obtain ⟨B, hB, hBX⟩ := hX.exists_isBase_subset
  obtain ⟨C, hC, h, -⟩ := hM.exists_isCircuit_of_isBase hB
  exact ⟨C, hC, h.anti <| diff_subset_diff_right hBX⟩

/-- Every independent set in a non-free paving matroid is nearly contained in a circuit. -/
lemma Paving.exists_isCircuit_of_indep {I : Set α} [M✶.RankPos] (hM : M.Paving) (hI : M.Indep I) :
    ∃ C, M.IsCircuit C ∧ (I \ C).Subsingleton := by
  obtain ⟨B, hB, hIB⟩ := hI.exists_isBase_superset
  obtain ⟨C, hC, -, h⟩ := hM.exists_isCircuit_of_isBase hB
  exact ⟨C, hC, h.anti <| diff_subset_diff_left hIB⟩

/-- A `SparsePaving` matroid is a paving matroid with paving dual,
or equivalently one where every nonspanning dependent set is a circuit-hyperplane. -/
@[mk_iff]
structure SparsePaving (M : Matroid α) : Prop where
  paving : M.Paving
  paving_dual : M✶.Paving

theorem SparsePaving.dual (h : M.SparsePaving) : M✶.SparsePaving := by
  rwa [sparsePaving_iff, dual_dual, and_comm, ← sparsePaving_iff]

@[simp]
lemma dual_sparsePaving_iff : M✶.SparsePaving ↔ M.SparsePaving :=
  ⟨fun h ↦ by simpa using h.dual, SparsePaving.dual⟩

theorem SparsePaving.minor (h : M.SparsePaving) (hNM : N ≤m M) : N.SparsePaving :=
  ⟨h.1.minor hNM, h.dual.1.minor hNM.dual⟩

/-- This probably can be golfed with a nullity / relative rank argument. -/
lemma SparsePaving.isCircuit_of_dep_of_nonspanning (hM : M.SparsePaving) (hC : M.Dep C)
    (hCs : M.Nonspanning C) : M.IsCircuit C := by

  have hCE : C ⊂ M.E := hC.subset_ground.ssubset_of_ne <|
    by (rintro rfl; simpa [ground_spanning] using hCs.not_spanning)

  obtain ⟨f, hfX, hfXi⟩ := hM.2.exists_diff_indep_of_nonspanning hCs hC.nonempty
  obtain ⟨g, ⟨hgE, hgX⟩, hg⟩ := hM.1.exists_insert_of_dep_of_ssubset hC hCE
  obtain ⟨B, hB⟩ := hfXi.subset_isBasis_of_subset (diff_subset.trans (subset_insert g C))

  have hB' : M.IsBase B := by
    rw [← isBasis_ground_iff, ← hg.closure_eq]
    exact hB.1.isBasis_closure_right

  have hfg : f ≠ g := by rintro rfl; contradiction

  obtain rfl : B = insert g (C \ {f}) := by
    rw [subset_antisymm_iff, insert_subset_iff, and_iff_left hB.2,
      insert_diff_singleton_comm hfg.symm, subset_diff_singleton_iff, and_iff_right hB.1.subset]
    refine ⟨fun hfB ↦ ?_, by_contra fun hgB ↦ hCs.not_spanning (hB'.spanning.superset ?_)⟩
    · refine hC.not_indep <| hB'.indep.subset ?_
      rw [← insert_eq_of_mem hfB, ← diff_singleton_subset_iff]
      exact hB.2
    rw [← diff_singleton_eq_self hgB, diff_singleton_subset_iff]
    exact hB.1.subset

  have hfin : ¬M.IsBase (insert f C \ {g}) → M.IsCircuit (insert f C \ {g})
  · simpa [hCE.subset hfX, hfg, insert_diff_singleton_comm hfg] using
      hM.1.isBase_exchange_isCircuit_of_not_isBase hB' (e := f) (f := g)

  rw [diff_singleton_eq_self (by simp [hgX, hfX]), insert_eq_of_mem hfX] at hfin
  exact hfin (fun h ↦ hCs.not_spanning h.spanning)

lemma SparsePaving.isHyperplane_of_dep_of_nonspanning {H : Set α} (hM : M.SparsePaving)
    (hH : M.Dep H) (hHs : M.Nonspanning H) : M.IsHyperplane H := by
  rw [← isCocircuit_compl_iff_isHyperplane, IsCocircuit]
  apply hM.dual.isCircuit_of_dep_of_nonspanning
  · rwa [← codep_def, codep_compl_iff]
  rwa [nonspanning_compl_dual_iff]

theorem SparsePaving.indep_or_spanning_or_isCircuit_isHyperplane (hM : M.SparsePaving)
    (hXE : X ⊆ M.E) : M.Indep X ∨ M.Spanning X ∨ (M.IsCircuit X ∧ M.IsHyperplane X) := by
  rw [or_iff_not_imp_left, not_indep_iff, or_iff_not_imp_left, not_spanning_iff]
  exact fun hXd hXs ↦ ⟨hM.isCircuit_of_dep_of_nonspanning hXd hXs,
    hM.isHyperplane_of_dep_of_nonspanning hXd hXs⟩

theorem sparsePaving_iff_forall_indep_or_spanning_or_isCircuit_isHyperplane :
    M.SparsePaving ↔ ∀ X ⊆ M.E, M.Indep X ∨ M.Spanning X ∨ (M.IsCircuit X ∧ M.IsHyperplane X) := by
  suffices aux : ∀ (M : Matroid α),
    (∀ X ⊆ M.E, M.Indep X ∨ M.Spanning X ∨ M.IsCircuit X ∧ M.IsHyperplane X) → M.Paving
  · refine ⟨fun h X hX ↦ h.indep_or_spanning_or_isCircuit_isHyperplane hX,
      fun h ↦ ⟨aux M h, aux M✶ fun X hX ↦ ?_⟩⟩
    rw [← coindep_def, coindep_iff_compl_spanning, M✶.spanning_iff_compl_coindep,
      dual_coindep_iff, dual_ground, ← isCocircuit_def, ← isHyperplane_compl_iff_isCocircuit,
      ← M✶.isCocircuit_compl_iff_isHyperplane, dual_ground, dual_isCocircuit_iff]
    specialize h (M.E \ X) diff_subset
    tauto
  clear! M
  intro M hM X (hXE : X ⊆ M.E)
  obtain ⟨E, rfl⟩ | h := M.eq_loopyOn_or_rankPos'
  · simp [show X ⊆ E from hXE]

  rw [truncate_indep_iff]
  obtain h | h | h := hM X hXE
  · by_cases hI : M.IsBase X
    · exact .inr hI.spanning.truncate_spanning
    exact .inl ⟨h, hI⟩
  · exact .inr h.truncate_spanning

  rw [truncate_spanning_iff]
  obtain ⟨e, he⟩ := exists_of_ssubset h.2.ssubset_ground
  have hcl := h.2.closure_insert_eq_univ he
  rw [← spanning_iff_closure_eq] at hcl
  exact .inr ⟨e, he.1, hcl⟩

lemma IsUniform.sparsePaving (h : M.IsUniform) : M.SparsePaving := by
  rw [sparsePaving_iff_forall_indep_or_spanning_or_isCircuit_isHyperplane]
  rw [isUniform_iff] at h
  grind

section exp
