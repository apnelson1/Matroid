import Mathlib.Order.SupIndep
import Mathlib.Order.Atoms
import Mathlib.Tactic.ApplyFun

open Set

section Lattice

-- theorem sSup_iUnion {α ι : Type*} [CompleteLattice α] {s : ι → Set α} :
--     sSup (⋃ i, s i) = iSup (fun i ↦ sSup (s i)) := by
--   simp only [le_antisymm_iff, sSup_le_iff, mem_iUnion, forall_exists_index, iSup_le_iff]
--   exact ⟨fun a i h ↦ le_iSup_of_le i <| le_sSup h, fun i a h ↦ le_sSup <| mem_iUnion_of_mem i h⟩

-- @[simp] theorem sSupIndep_singleton {α : Type*} [CompleteLattice α] (s : α) :
--     CompleteLattice.SetIndependent {s} := by
--   simp [CompleteLattice.SetIndependent]


@[simp]
lemma orderIsoSetOfAtoms_sSup {α : Type*} [CompleteAtomicBooleanAlgebra α] (a : α) :
    sSup (Subtype.val '' (CompleteAtomicBooleanAlgebra.toSetOfIsAtom a)) = a :=
    CompleteAtomicBooleanAlgebra.toSetOfIsAtom.left_inv a

end Lattice
