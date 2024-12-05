import Matroid.Circuit
import Matroid.Flat

open Set

variable {α : Type*} {N M : Matroid α} {B C D : Set α} {e f : α}

namespace Matroid

/-- A Paving matroid is one where every circuit is spanning or nearly-spanning. -/
def Paving (M : Matroid α) : Prop := ∀ ⦃C⦄, M.Circuit C → ∃ e, M.Spanning (insert e C)

/-- A Paving matroid is one where every circuit is spanning or nearly-spanning. -/
def Paving.exists_insert_of_dep (hM : M.Paving) (hD : M.Dep D) :
    ∃ e ∈ M.E, M.Spanning (insert e D) := by
  obtain ⟨C, hCD, hC⟩ := hD.exists_circuit_subset
  obtain ⟨e, he⟩ := hM hC
  exact ⟨e, he.subset_ground <| mem_insert _ _, he.superset (insert_subset_insert hCD)
    (insert_subset (he.subset_ground (mem_insert _ _)) hD.subset_ground)⟩

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

def Paving.delete (hM : M.Paving) (D : Set α) : (M ＼ D).Paving := by
  simp_rw [Paving, delete_circuit_iff, and_imp]
  intro C hC hCD
  suffices aux : ∃ e ∈ M.E \ D, M.E \ D ⊆ M.closure (insert e C) by
    obtain ⟨e, he, hss⟩ := aux
    use e
    rwa [spanning_iff, delete_closure_eq, insert_diff_of_not_mem _ he.2, sdiff_eq_left.2 hCD,
      delete_ground, insert_subset_iff, and_iff_right he, subset_diff, and_iff_left hCD,
      and_iff_left hC.subset_ground, subset_antisymm_iff,
      and_iff_right (diff_subset_diff_left (M.closure_subset_ground _)), subset_diff,
      and_iff_left disjoint_sdiff_left]

  by_contra! hcon
  obtain ⟨e, he⟩ := hC.nonempty
  refine hcon e ⟨hC.subset_ground he, fun heD ↦ hCD.ne_of_mem he heD rfl⟩
    fun f hf ↦ by_contra fun hfC ↦ hcon f hf ?_
  rw [insert_eq_of_mem he] at hfC
  rw [(hM.insert_spanning_of_dep_of_not_mem_closure hC.dep ⟨hf.1, hfC⟩).closure_eq]
  exact diff_subset

def Paving.contract (hM : M.Paving) (C : Set α) : (M ／ C).Paving := by
  suffices aux : ∀ C ⊆ M.E, (M ／ C).Paving  by
    rw [← contract_inter_ground_eq]; apply aux _ (by simp)
  clear C
  intro C hCE C' hC'
  have hC'E : C' ⊆ M.E := hC'.subset_ground.trans diff_subset
  have hdj : Disjoint C' C := (subset_diff.1 hC'.subset_ground).2
  simp_rw [contract_spanning_iff hCE, ← union_singleton, disjoint_union_left, and_iff_right hdj,
    disjoint_singleton_left, union_singleton, insert_union]
  obtain hi | hd := M.indep_or_dep (union_subset hC'E hCE)
  · refine (hC'.dep.not_indep ?_).elim
    rwa [(hi.subset subset_union_right).contract_indep_iff, and_iff_right hdj]
  by_cases hS : M.Spanning (C' ∪ C)
  · obtain ⟨e, he⟩ := hC'.nonempty
    exact ⟨e, hS.superset (subset_insert _ _), fun heC ↦ hdj.ne_of_mem he heC rfl⟩
  obtain ⟨e, -, he⟩ := hM.exists_insert_of_dep hd
  exact ⟨e, he, fun heC ↦ hS <| by rwa [insert_eq_of_mem (.inr heC)] at he⟩

def Paving.minor (hM : M.Paving) (hNM : N ≤m M) : N.Paving := by
  rw [hNM.eq_con_del]
  exact (hM.contract _).delete _

/-- A `SparsePaving` matroid is one where every circuit is a circuit-hyperplane. -/
def SparsePaving (M : Matroid α) := M.Paving ∧ M✶.Paving

theorem SparsePaving.dual (h : M.SparsePaving) : M✶.SparsePaving := by
  rw [SparsePaving, dual_dual]
  exact And.symm h

theorem SparsePaving.minor (h : M.SparsePaving) (hNM : N ≤m M) : N.SparsePaving :=
  ⟨h.1.minor hNM, h.dual.1.minor hNM.dual⟩

-- lemma sparsePaving_iff :
--     M.SparsePaving ↔ ∀ X ⊆ M.E, M.Indep X ∨ M.Spanning X ∨ (M.Circuit X ∧ M.Hyperplane X) := by
--   -- have aux : ∀ N X, Matroid.Paving N → X ⊆ N.E → N.Dep X →
--   refine ⟨fun ⟨h, hdu⟩ X hX ↦ ?_, fun h ↦ ?_⟩
--   ·
--     rw [← not_dep_iff]
--     by_contra! hcon
--     have hhp := h.closure_hyperplane_of_dep_of_not_spanning hcon.1 hcon.2.1
--     obtain ⟨e, heE : e ∈ M.E, he⟩ := hdu.exists_insert_of_dep hhp.compl_cocircuit.circuit.dep
--     rw [spanning_iff_compl_coindep, ← union_singleton, dual_ground, ← diff_diff,
--       diff_diff_cancel_left (M.closure_subset_ground _), dual_coindep_iff] at he

--     have hXi := he.subset (diff_subset_diff_left (M.subset_closure X))
--     -- obtain ⟨C, hCX, hC⟩ := hcon.1.exists_circuit_subset
--     -- have heC : e ∈ C :=
--     --   by_contra fun heC ↦ hC.dep.not_indep (hXi.subset (subset_diff_singleton hCX heC))
--     -- have heX : e ∈ M.closure (X \ {e}) :=
--     --   mem_of_mem_of_subset (hC.mem_closure_diff_singleton_of_mem heC)
--     --     (M.closure_subset_closure (diff_subset_diff_left hCX))

--     have hbas : M.Basis (X \ {e}) X := by
--       refine hXi.basis_of_forall_insert diff_subset fun x hx ↦ ?_
--       obtain ⟨heX, rfl⟩ : (x ∈ X) ∧ x = e := by simpa using hx
--       simp [hx.1, hcon.1]

--     have heX : e ∈ X :=
--       by_contra fun heX ↦ hcon.1.not_indep <| by rwa [diff_singleton_eq_self heX] at hXi


--     have hXcl : X = M.closure (X \ {e}) := by
--       rw [hbas.closure_eq_closure]
--       have h_eq := hbas.basis_closure_right.eq_of_subset_indep he
--         (diff_subset_diff_left (M.subset_closure _)) diff_subset
--       apply_fun (insert e) at h_eq
--       simpa only [insert_diff_singleton, heX, insert_eq_of_mem,
--         insert_eq_of_mem (M.mem_closure_of_mem heX hX)] using h_eq

--     have hXcl' : M.closure X = M.closure (X \ {e}) := by
--       rw [← hbas.closure_eq_closure]

--     rw [← hbas.closure_eq_closure, ← hXcl] at hhp
--     obtain ⟨B₀, hB₀⟩ := M.exists_base
--     obtain ⟨f, hf⟩ := hXi.exists_insert_of_not_base (fun hbas ↦ hcon.2.1 hbas.spanning)
--     -- obtain ⟨B, hB⟩ := hXi.ex







    -- have : X = M.closure (X \ {e}) := by
    --   refine subset_antisymm ?_ ?_

    -- obtain ⟨I, hI⟩ := M.exists_basis X
    -- obtain ⟨B, hB, rfl⟩ := hI.exists_base
    -- obtain ⟨e, he⟩ : (X \ B).Nonempty := sorry
    -- obtain ⟨f, hf⟩ : (B \ X).Nonempty := sorry
    -- have hfE : f ∈ M.E := hB.subset_ground hf.1
    -- have hfX : f ∉ M.closure X := by
    --   rw [← hI.closure_eq_closure, hI.indep.mem_closure_iff, or_iff_left (fun h ↦ hf.2 h.2)]
    --   exact (hB.indep.subset (insert_subset hf.1 inter_subset_left)).not_dep
    -- have hsp := h.insert_spanning_of_dep_of_not_mem_closure hcon.1 ⟨hfE, hfX⟩
    -- rw [spanning_iff_closure_eq, ← closure_insert_closure_eq_closure_insert,
    --   ← hI.closure_eq_closure, closure_insert_closure_eq_closure_insert] at hsp

      -- have := hB.indep.subset (insert_subset hf.1 inter_subset_left)

-- instance minorClosed_paving : MinorClosed.{u} Matroid.Paving where
--   forall_minor := fun h hN ↦ Paving.minor hN h

-- instance minorClosed_sparsePaving : MinorClosed.{u} Matroid.SparsePaving where
--   forall_minor := fun h hN ↦ SparsePaving.minor hN h
