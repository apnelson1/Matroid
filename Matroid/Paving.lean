import Matroid.Uniform
import Matroid.ForMathlib.Matroid.Basic

open Set

variable {α : Type*} {N M : Matroid α} {B C D X : Set α} {e f : α}

namespace Matroid



/-- A `Paving` matroid is one whose truncation is uniform, or equivalently one where every
dependent set is a single insertion away from being spanning. -/
def Paving (M : Matroid α) : Prop := M.truncate.Uniform

lemma Paving.truncate_uniform (hM : M.Paving) : M.truncate.Uniform :=
  hM

/-- A Paving matroid is one where every circuit is spanning or nearly-spanning. -/
def Paving.exists_insert_of_dep (hM : M.Paving) (hD : M.Dep D) :
    ∃ e ∈ M.E, M.Spanning (insert e D) := by
  obtain ⟨E, rfl⟩ := M.eq_loopyOn_or_rkPos'
  · simp only [loopyOn_ground, spanning_iff, loopyOn_closure_eq, true_and]
    obtain ⟨e, he⟩ := hD.nonempty
    exact ⟨e, hD.subset_ground he, insert_subset (hD.subset_ground he) hD.subset_ground⟩
  have h_or := hM.indep_or_spanning D hD.subset_ground
  simpa [truncate_indep_iff, truncate_spanning_iff, hD.not_indep] using h_or

def Paving.exists_insert_of_dep_of_ssubset (hM : M.Paving) (hD : M.Dep D) (hDE : D ⊂ M.E) :
    ∃ e ∈ M.E \ D, M.Spanning (insert e D) := by
  obtain ⟨e, he, heD⟩ := hM.exists_insert_of_dep hD
  by_cases he' : e ∈ D
  · obtain ⟨f, hf⟩ := exists_of_ssubset hDE
    rw [insert_eq_of_mem he'] at heD
    exact ⟨f, hf, heD.superset (subset_insert _ _)⟩
  exact ⟨e, ⟨he, he'⟩, heD⟩

lemma Paving.insert_spanning_of_dep_of_not_mem_closure (hM : M.Paving) (hD : M.Dep D)
    (he : e ∈ M.E \ M.closure D) : M.Spanning (insert e D) := by
  obtain ⟨f, -, hf⟩ := hM.exists_insert_of_dep hD
  rw [spanning_iff_closure_eq]
  have hf' := mem_closure_insert he.2 (f := f) (by simpa [hf.closure_eq] using he.1)
  rw [← closure_closure, ← insert_eq_of_mem hf', closure_insert_closure_eq_closure_insert,
    insert_comm, ← closure_insert_closure_eq_closure_insert, hf.closure_eq,
    insert_eq_of_mem he.1, closure_ground]

lemma Paving.closure_hyperplane_of_dep_of_not_spanning (hM : M.Paving) (hD : M.Dep D)
    (hDs : ¬ M.Spanning D) : M.Hyperplane (M.closure D) := by
  rw [hyperplane_iff_maximal_nonspanning, maximal_iff_forall_insert, spanning_iff_closure_eq,
    closure_closure, ← spanning_iff_closure_eq, and_iff_right hDs,
    and_iff_right (M.closure_subset_ground D)]
  · refine fun e he' h ↦ h.1 ?_
    rw [spanning_iff_closure_eq, closure_insert_closure_eq_closure_insert,
      (hM.insert_spanning_of_dep_of_not_mem_closure hD ⟨?_, he'⟩).closure_eq]
    exact h.2 <| .inl rfl
  exact fun S T ⟨hT, hTE⟩ hST ↦ ⟨fun hS ↦ hT <| hS.superset hST, hST.trans hTE⟩

-- lemma Paving.base_exchange_circuit_of_not_base' (hM : M.Paving) (hB : M.Base B)
--     (heB : e ∈ M.E \ B) (hfB : f ∈ B) (hB' : ¬ M.Base (insert e (B \ {f}))) :
--     M.Circuit (insert e (B \ {f})) := by
--   obtain ⟨C, hC⟩

lemma Paving.base_exchange_circuit_of_not_base (hM : M.Paving) (hB : M.Base B)
    (heB : e ∈ M.E \ B) (hfB : f ∈ B) (hB' : ¬ M.Base (insert e (B \ {f}))) :
    M.Circuit (insert e (B \ {f})) := by
  set B' := insert e (B \ {f}) with hB'_def
  have hB'E : B' ⊆ M.E := insert_subset heB.1 (diff_subset.trans hB.subset_ground)
  have hB'd : M.Dep B' := by
    rw [← not_indep_iff]
    contrapose! hB'
    exact hB.exchange_base_of_indep heB.2 hB'

  rw [circuit_iff_dep_forall_diff_singleton_indep, and_iff_right hB'd]

  rintro x (rfl | ⟨hxB', hxf : x ≠ f⟩)
  · simp only [hB'_def, mem_singleton_iff, insert_diff_of_mem]
    exact hB.indep.subset (diff_subset.trans diff_subset)

  rw [← not_dep_iff (diff_subset.trans hB'E)]
  intro hd
  obtain ⟨C, hCB', hC⟩ := hd.exists_circuit_subset
  have hfE := hB.subset_ground hfB
  have hfC : f ∉ M.closure C := by
    rw [← hC.closure_diff_singleton_eq_closure e]
    apply not_mem_subset (M.closure_subset_closure (by simpa using hCB'.trans diff_subset))
    exact hB.indep.not_mem_closure_diff_of_mem hfB

  have hfC' := hM.insert_spanning_of_dep_of_not_mem_closure hC.dep ⟨hfE, hfC⟩

  rw [spanning_iff_closure_eq, ← closure_insert_closure_eq_closure_insert,
    ← hC.closure_diff_singleton_eq_closure e, closure_insert_closure_eq_closure_insert,
    ← spanning_iff_closure_eq] at hfC'

  obtain ⟨B₀, hB₀, hB₀ss⟩ := hfC'.exists_base_subset
  rw [hB₀.eq_of_subset_base hB (hB₀ss.trans ?_)] at hB₀ss
  · have hx := hB₀ss hxB'
    rw [mem_insert_iff, or_iff_right hxf, mem_diff] at hx
    simpa using hCB' hx.1
  refine insert_subset hfB ((diff_subset_diff_left hCB').trans ?_)
  simp only [hB'_def, diff_singleton_subset_iff, insert_comm]
  exact insert_subset_insert (diff_subset.trans (subset_insert _ _))

lemma Paving.restrict_uniform_of_nonspanning {R : Set α} (hM : M.Paving) (hRs : ¬ M.Spanning R)
    (hRE : R ⊆ M.E := by aesop_mat) : (M ↾ R).Uniform := by
  intro X (hXR : X ⊆ R)
  rw [restrict_indep_iff, restrict_spanning_iff hXR, and_iff_left hXR, or_iff_not_imp_left,
    not_indep_iff]
  intro hXd
  have h1 := hM.closure_hyperplane_of_dep_of_not_spanning (hXd.superset hXR) hRs
  have h2 := hM.closure_hyperplane_of_dep_of_not_spanning hXd (fun hs ↦ hRs (hs.superset hXR))
  rw [h2.eq_of_subset h1 (M.closure_subset_closure hXR)]
  exact M.subset_closure R

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
  refine (hM.restrict_uniform_of_nonspanning fun hs ↦ hD ?_).truncate
  rwa [coindep_iff_compl_spanning]

def Paving.contract (hM : M.Paving) (C : Set α) : (M ／ C).Paving := by
  rw [Paving, truncate_contract]
  exact hM.truncate_uniform.contract C

def Paving.minor (hM : M.Paving) (hNM : N ≤m M) : N.Paving := by
  rw [hNM.eq_con_del]
  exact (hM.contract _).delete _

lemma Paving.exists_diff_indep_of_not_spanning (hM : M✶.Paving) (hX : X ⊆ M.E)
    (hXs : ¬ M.Spanning X) (hne : X.Nonempty) : ∃ f ∈ X, M.Indep (X \ {f}) := by
  have hd : M✶.Dep (M.E \ X)
  · rwa [← not_indep_iff, ← coindep_def, ← spanning_iff_compl_coindep]
  have hssu : M.E \ X ⊂ M.E := diff_ssubset hX hne
  obtain ⟨f, hf, h⟩ := hM.exists_insert_of_dep_of_ssubset hd hssu
  rw [spanning_iff_compl_coindep, dual_coindep_iff, dual_ground, ← union_singleton, ← diff_diff,
    diff_diff_cancel_left hX] at h
  simp only [dual_ground, sdiff_sdiff_right_self, inf_eq_inter, mem_inter_iff] at hf
  exact ⟨f, hf.2, h⟩

/-- A `SparsePaving` matroid is a paving matroid with paving dual,
or equivalently one where every nonspanning dependent set is a circuit-hyperplane. -/
def SparsePaving (M : Matroid α) := M.Paving ∧ M✶.Paving

theorem SparsePaving.dual (h : M.SparsePaving) : M✶.SparsePaving := by
  rwa [SparsePaving, dual_dual, and_comm]

theorem SparsePaving.minor (h : M.SparsePaving) (hNM : N ≤m M) : N.SparsePaving :=
  ⟨h.1.minor hNM, h.dual.1.minor hNM.dual⟩

lemma SparsePaving.circuit_of_dep_of_not_spanning (hM : M.SparsePaving) (hC : M.Dep C)
    (hCs : ¬ M.Spanning C) : M.Circuit C := by

  have hCE : C ⊂ M.E := hC.subset_ground.ssubset_of_ne <|
    by (rintro rfl; simp [ground_spanning] at hCs)

  obtain ⟨f, hfX, hfXi⟩ := hM.2.exists_diff_indep_of_not_spanning hCE.subset hCs hC.nonempty
  obtain ⟨g, ⟨hgE, hgX⟩, hg⟩ := hM.1.exists_insert_of_dep_of_ssubset hC hCE
  obtain ⟨B, hB⟩ := hfXi.subset_basis_of_subset (diff_subset.trans (subset_insert g C))

  have hB' : M.Base B := by
    rw [← basis_ground_iff, ← hg.closure_eq]
    exact hB.1.basis_closure_right

  have hfg : f ≠ g := by rintro rfl; contradiction

  obtain rfl : B = insert g (C \ {f}) := by
    rw [subset_antisymm_iff, insert_subset_iff, and_iff_left hB.2,
      insert_diff_singleton_comm hfg.symm, subset_diff_singleton_iff, and_iff_right hB.1.subset]
    refine ⟨fun hfB ↦ ?_, by_contra fun hgB ↦ hCs (hB'.spanning.superset ?_)⟩
    · refine hC.not_indep <| hB'.indep.subset ?_
      rw [← insert_eq_of_mem hfB, ← diff_singleton_subset_iff]
      exact hB.2
    rw [← diff_singleton_eq_self hgB, diff_singleton_subset_iff]
    exact hB.1.subset

  have hfin : ¬M.Base (insert f C \ {g}) → M.Circuit (insert f C \ {g})
  · simpa [hCE.subset hfX, hfg, insert_diff_singleton_comm hfg] using
      hM.1.base_exchange_circuit_of_not_base hB' (e := f) (f := g)

  rw [diff_singleton_eq_self (by simp [hgX, hfX]), insert_eq_of_mem hfX] at hfin

  exact hfin (fun h ↦ hCs h.spanning)

lemma SparsePaving.hyperplane_of_dep_of_not_spanning {H : Set α} (hM : M.SparsePaving)
    (hH : M.Dep H) (hHs : ¬ M.Spanning H) : M.Hyperplane H := by
  rw [← compl_cocircuit_iff_hyperplane, Cocircuit]
  apply hM.dual.circuit_of_dep_of_not_spanning
  · rwa [← not_indep_iff, ← coindep_def, coindep_iff_compl_spanning,
      diff_diff_cancel_left hH.subset_ground]
  rwa [← M.dual_ground, ← coindep_iff_compl_spanning, dual_coindep_iff, not_indep_iff]

theorem SparsePaving.indep_or_spanning_or_circuit_hyperplane (hM : M.SparsePaving) (hXE : X ⊆ M.E) :
    M.Indep X ∨ M.Spanning X ∨ (M.Circuit X ∧ M.Hyperplane X) := by
  rw [or_iff_not_imp_left, not_indep_iff, or_iff_not_imp_left]
  exact fun hXd hXs ↦ ⟨hM.circuit_of_dep_of_not_spanning hXd hXs,
    hM.hyperplane_of_dep_of_not_spanning hXd hXs⟩

theorem sparsePaving_iff_forall_indep_or_spanning_or_circuit_hyperplane :
    M.SparsePaving ↔ ∀ X ⊆ M.E, M.Indep X ∨ M.Spanning X ∨ (M.Circuit X ∧ M.Hyperplane X) := by
  suffices aux : ∀ (M : Matroid α),
    (∀ X ⊆ M.E, M.Indep X ∨ M.Spanning X ∨ M.Circuit X ∧ M.Hyperplane X) → M.Paving
  · refine ⟨fun h X hX ↦ h.indep_or_spanning_or_circuit_hyperplane hX,
      fun h ↦ ⟨aux M h, aux M✶ fun X hX ↦ ?_⟩⟩
    rw [← coindep_def, coindep_iff_compl_spanning, M✶.spanning_iff_compl_coindep,
      dual_coindep_iff, dual_ground, ← cocircuit_def, ← compl_hyperplane_iff_cocircuit,
      ← M✶.compl_cocircuit_iff_hyperplane, dual_ground, dual_cocircuit_iff]
    specialize h (M.E \ X) diff_subset
    tauto
  clear! M
  intro M hM X (hXE : X ⊆ M.E)
  obtain ⟨E, rfl⟩ | h := M.eq_loopyOn_or_rkPos'
  · simp [show X ⊆ E from hXE]

  rw [truncate_indep_iff]
  obtain h | h | h := hM X hXE
  · by_cases hI : M.Base X
    · exact .inr hI.spanning.truncate_spanning
    exact .inl ⟨h, hI⟩
  · exact .inr h.truncate_spanning

  rw [truncate_spanning_iff]
  obtain ⟨e, he⟩ := exists_of_ssubset h.2.ssubset_ground
  have hcl := h.2.closure_insert_eq_univ he
  rw [← spanning_iff_closure_eq] at hcl
  exact .inr ⟨e, he.1, hcl⟩
