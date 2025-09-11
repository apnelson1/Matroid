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
lemma bot_not_isAtom {α : Type*} [CompleteAtomicBooleanAlgebra α] : ¬ IsAtom (⊥ : α) := (·.1 rfl)

theorem exists_mem_le_of_le_sSup_of_isAtom {α : Type*} [CompleteAtomicBooleanAlgebra α] {a A : α}
    (ha : IsAtom a) (h : a ≤ A) {s : Set α} (hs : A ≤ sSup s) : ∃ b ∈ s, a ≤ b := by
  by_contra! hnle
  have : ⨆ s₀ ∈ s, a ⊓ s₀ = ⊥ := by
    simp only [iSup_eq_bot]
    intro s₀ hs₀
    simpa [hnle s₀ hs₀] using ha.le_iff.mp (inf_le_left (b := s₀))
  obtain rfl := (inf_eq_left.mpr (h.trans hs)).symm.trans <| inf_sSup_eq.trans this
  exact ha.1 rfl

lemma sSupIndep_atoms {α : Type*} [CompleteAtomicBooleanAlgebra α] {s : Set α}
    (hs : ∀ a ∈ s, IsAtom a) : sSupIndep s := by
  rintro a has b hba hbs
  rw [le_bot_iff]
  by_contra! hbne
  obtain rfl := by simpa [hbne] using (hs a has).le_iff.mp hba
  obtain ⟨c, hcs, hbc⟩ := exists_mem_le_of_le_sSup_of_isAtom (hs b has) hbs le_rfl
  obtain rfl := by simpa [hbne] using (hs c hcs.1).le_iff.mp hbc
  simp at hcs

lemma unique_decomposition_into_atoms {α : Type*} [CompleteAtomicBooleanAlgebra α]
    {S : Set α} (hS : ∀ a ∈ S, IsAtom a) : S = {a | IsAtom a ∧ a ≤ sSup S} := by
  ext a
  refine ⟨fun h => ⟨hS a h, CompleteLattice.le_sSup S a h⟩, fun ⟨hatom, hale⟩ => ?_⟩
  obtain ⟨b, hbS, hba⟩ := exists_mem_le_of_le_sSup_of_isAtom hatom hale le_rfl
  obtain rfl | rfl := (hS b hbS).le_iff.mp hba
  · simpa using hatom.1
  assumption

def orderIsoSetOfAtoms {α : Type*} [CompleteAtomicBooleanAlgebra α] :
    α ≃o (Set {a : α | IsAtom a}) where
  toFun A := {a | a ≤ A}
  invFun S := sSup (Subtype.val '' S)
  left_inv A := by simp [Subtype.coe_image]
  right_inv S := by
    apply_fun (Subtype.val '' ·) using Subtype.val_injective.image_injective
    beta_reduce
    rw [unique_decomposition_into_atoms (S := Subtype.val '' S)]; swap
    · rintro a ⟨a', ha', rfl⟩
      exact a'.prop
    ext a
    simp only [mem_setOf_eq, coe_setOf, sSup_atoms_le_eq, mem_image, Subtype.exists,
      exists_and_left, exists_prop, exists_eq_right_right]
    rw [and_comm]
  map_rel_iff' {a b} := by
    simp +contextual only [coe_setOf, mem_setOf_eq, Equiv.coe_fn_mk, le_eq_subset,
      setOf_subset_setOf, Subtype.forall]
    exact le_iff_atom_le_imp.symm

@[simp]
lemma orderIsoSetOfAtoms_sSup {α : Type*} [CompleteAtomicBooleanAlgebra α] (a : α) :
    sSup (Subtype.val '' (orderIsoSetOfAtoms a)) = a := orderIsoSetOfAtoms.left_inv a

end Lattice
