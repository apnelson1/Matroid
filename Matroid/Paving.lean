import Matroid.Circuit
import Matroid.Flat
import Matroid.Class

open Set

variable {α : Type*} {M : Matroid α}

namespace Matroid

/-- A Paving matroid is one where every circuit is spanning. -/
def Paving (M : Matroid α) : Prop := ∀ C, M.Circuit C → M.Spanning C

theorem Paving.spanning_of_circuit (hM : M.Paving) (hC : M.Circuit C) : M.Spanning C :=
  hM _ hC

theorem Paving.spanning_of_dep (hM : M.Paving) (hD : M.Dep D) : M.Spanning D := by
  obtain ⟨C, hCD, hC⟩ := hD.exists_circuit_subset
  exact (hM.spanning_of_circuit hC).superset hCD

def Paving.delete (hM : M.Paving) (D : Set α) : (M ＼ D).Paving := by
  simp_rw [Paving, delete_circuit_iff, and_imp]
  intro C hC hCD
  rw [spanning_iff_cl _, delete_cl_eq, delete_ground, hCD.sdiff_eq_left,
    (hM.spanning_of_circuit hC).cl_eq]
  rw [delete_ground, subset_diff]
  exact ⟨hC.subset_ground, hCD⟩

def Paving.contract (hM : M.Paving) (C : Set α) : (M ／ C).Paving := by
  intro C' hC'
  have hdj : Disjoint C' C := (subset_diff.1 hC'.subset_ground).2
  rw [contract_spanning_iff', union_comm]
  rw [← contract_inter_ground_eq] at hC'
  exact ⟨hM.spanning_of_dep hC'.dep.of_contract, hdj⟩

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

instance minorClosed_paving : MinorClosed.{u} Matroid.Paving where
  forall_minor := fun h hN ↦ Paving.minor hN h

instance minorClosed_sparsePaving : MinorClosed.{u} Matroid.SparsePaving where
  forall_minor := fun h hN ↦ SparsePaving.minor hN h
