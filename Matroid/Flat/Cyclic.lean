import Matroid.Flat.Lattice

variable {α : Type*} {M : Matroid α} {I F X Y F' F₀ F₁ F₂ P L H H₁ H₂ H' B C K : Set α} {e f : α}

open Set

namespace Matroid

/-- A flat is a cyclic flat if it is a union of circuits. -/
@[mk_iff]
structure IsCyclicFlat (M : Matroid α) (F : Set α) : Prop where
  isFlat : M.IsFlat F
  cyclic : M.Cyclic F

@[aesop unsafe 10% (rule_sets := [Matroid]), grind →]
lemma IsCyclicFlat.subset_ground (h : M.IsCyclicFlat F) : F ⊆ M.E :=
  h.isFlat.subset_ground

lemma IsCyclicFlat.compl_isCyclicFlat_dual (h : M.IsCyclicFlat F) : M✶.IsCyclicFlat (M.E \ F) where
  isFlat := h.cyclic.compl_isFlat_dual
  cyclic := h.isFlat.compl_cyclic_dual

/-- The union of the circuits contained in a set `X`. If `X` is a flat, this is a cyclic flat. -/
def cycleClosure (M : Matroid α) (X : Set α) := ⋃₀ {C | M.IsCircuit C ∧ C ⊆ X}

lemma cycleClosure_def (M : Matroid α) (X : Set α) :
    M.cycleClosure X = ⋃₀ {C | M.IsCircuit C ∧ C ⊆ X} := rfl

@[simp]
lemma cycleClosure_cyclic (M : Matroid α) (X : Set α) : M.Cyclic <| M.cycleClosure X :=
  Cyclic.sUnion _ <| by grind [IsCircuit.cyclic]

lemma IsFlat.isCyclicFlat_cycleClosure (hF : M.IsFlat F) : M.IsCyclicFlat (M.cycleClosure F) where
  isFlat := by
    rw [isFlat_iff_forall_isCircuit] at ⊢ hF
    have hUF : ⋃₀ {C | M.IsCircuit C ∧ C ⊆ F} ⊆ F := by grind
    refine fun C e hC heC hCss ↦ mem_sUnion_of_mem heC ⟨hC, hCss.trans (insert_subset ?_ hUF)⟩
    exact hF C e hC heC <| hCss.trans <| insert_subset_insert hUF
  cyclic := cycleClosure_cyclic ..

lemma Cyclic.subset_cycleClosure_of_subset (hC : M.Cyclic C) (hCX : C ⊆ X) :
    C ⊆ M.cycleClosure X := by
  intro e heC
  rw [cyclic_iff_forall_exists] at hC
  obtain ⟨C', hC'C, hC', heC'⟩ := hC e heC
  exact mem_sUnion_of_mem heC' <| by grind

/-- If `F` is a collection of flats, then the union of the circuits contained in their
intersection is a cyclic flat. -/
lemma IsFlat.isCyclicFlat_sUnion_isCircuit_subset_iInter {ι : Type*} (F : ι → Set α)
    (hF : ∀ i, M.IsFlat (F i)) : M.IsCyclicFlat (⋃₀ {C | M.IsCircuit C ∧ ∀ i, C ⊆ F i}) := by
  obtain hι | hι := isEmpty_or_nonempty ι
  · convert M.ground_isFlat.isCyclicFlat_cycleClosure using 4 with C
    simp [cycleClosure_def, and_iff_left_of_imp IsCircuit.subset_ground]
  simpa [cycleClosure_def] using (IsFlat.iInter (fun i ↦ (hF i))).isCyclicFlat_cycleClosure

lemma isFlat_iff_foo (hF : F ⊆ M.E := by aesop_mat) : M.IsFlat F ↔
    (M.IsCyclicFlat (M.cycleClosure F)) ∧ ∀ F₀ ⊆ F, M.IsCyclicFlat F₀ → F₀ ⊆ M.cycleClosure F := by
  refine ⟨fun h ↦ ⟨h.isCyclicFlat_cycleClosure, fun F₀ hF₀F hF₀ ↦ ?_⟩, fun h ↦ ?_⟩
  · exact hF₀.cyclic.subset_cycleClosure_of_subset hF₀F
  · rw [isFlat_iff_forall_isCircuit]
    intro C e hC heC hCeF
    have := h.1.isFlat.
    have := hC.cyclic.subset_cycleClosure_of_subset hCeF

lemma ext_isCyclicFlat {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E) [M₁.RankFinite]
    (hr : ∀ (r : ℕ) F, (M₁.IsCyclicFlat F ∧ M₁.eRk F = r) ↔ (M₂.IsCyclicFlat F ∧ M₂.eRk F = r)) :
    M₁ = M₂ := by
  sorry
