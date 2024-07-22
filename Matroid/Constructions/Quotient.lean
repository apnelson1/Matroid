import Matroid.Minor.Rank

import Matroid.Flat

import Matroid.Constructions.RankAxioms

--relRank
open Set
namespace Matroid

variable {α : Type*} {M N : Matroid α} {X Y F : Set α}

def Quotient (M N : Matroid α) : Prop :=
  M.E = N.E ∧ ∀ F, M.Flat F → N.Flat F

def WeakLE (M N : Matroid α) : Prop :=
  M.E = N.E ∧ ∀ D, N.Dep D → M.Dep D

def Flat_Covers_Flat (M: Matroid α) (F₁ F₂ : Set α) : Prop :=
  M.Flat F₁ ∧ M.Flat F₂ ∧ F₂ ⊆ F₁ ∧ M.relRank F₂ F₁ = 1

def Quotient' (M₁ M₂ : Matroid α) : Prop :=
 M₁.E = M₂.E ∧ ∀ X Y, X ⊆ Y → Y ⊆ M₁.E → M₂.relRank X Y ≤ M₁.relRank X Y

infixl:50 " ≤q " => Matroid.Quotient

infixl:50 " ≤w " => Matroid.WeakLE
--(hE: M₁.E=M₂.E)

lemma Quotient.ground_eq (h : M ≤q N) : M.E = N.E :=
  h.1

lemma Quotient.flat_of_flat (h : M ≤q N) (hF : M.Flat F) : N.Flat F :=
  h.2 F hF

lemma cl_flat_idk (X F: Set α) (M : Matroid α) (hFlat : M.Flat F) (hXF: X ⊆ F) : M.cl X ⊆ F := by
  exact Flat.cl_subset_of_subset hFlat hXF

lemma top_thingy {a b : ℕ∞} (hab : a + b ≤ a) (ht : a ≠ ⊤) : b = 0 := by
  have haa : a + b ≤ a + 0 := le_add_right hab
  rwa [WithTop.add_le_add_iff_left ht, nonpos_iff_eq_zero] at haa

lemma Quotient.cl_subset_cl (h : M ≤q N) (X : Set α) : N.cl X ⊆ M.cl X := by
  rw [← cl_inter_ground, ← cl_inter_ground (M := M), ← h.ground_eq]
  rw [← (h.flat_of_flat (M.cl_flat _)).cl]
  apply N.cl_subset_cl
  exact M.subset_cl _

theorem Quotient.relRank_le {M₁ M₂: Matroid α} (hQ : M₂ ≤q M₁) {X : Set α} (hXY : X ⊆ Y)
    (hYE: Y ⊆ M₁.E) : M₂.relRank X Y ≤ M₁.relRank X Y := by
  have hcas:= lt_or_le (M₁.relRank X Y) ⊤
  --Divide into cases finite and infinite
  obtain(hfin|hinf):= hcas

  · by_cases hX : Y ⊆ M₁.cl X
    . rw [(relRank_eq_zero_iff (M := M₂) _).2]
      · apply zero_le
      · exact hX.trans (hQ.cl_subset_cl _)
      rwa [hQ.ground_eq]

    obtain ⟨y, hyY, hyX⟩ := not_subset.1 hX
    have hrw := fun M ↦
      relRank_add_of_subset_of_subset M (subset_insert y X) (insert_subset hyY hXY)
    have hy : y ∈ Y \ M₁.cl X ∧ M₁.relRank (insert y X) Y < M₁.relRank X Y := by
      refine ⟨⟨hyY, hyX⟩, ?_⟩
      rw [← hrw, relRank_insert_eq_one, add_comm, lt_iff_not_le]
      · intro hle
        have h' := (M₁.relRank_mono_left Y (subset_insert y X)).trans_lt hfin
        have h'' := top_thingy hle
        simp only [ne_eq, one_ne_zero, imp_false, Decidable.not_not] at h''
        exact h'.ne h''
      exact ⟨hYE hyY, hyX⟩

    obtain ⟨hy', hycard⟩ := hy

    have hiY: insert y X ⊆ Y := insert_subset hy'.1 hXY
    have ht := hQ.relRank_le hiY hYE

    have hycard1 : M₁.relRank (insert y X) Y + 1 ≤ M₁.relRank X Y := by
      exact ENat.add_one_le_of_lt hycard
    have h1 := (add_le_add_right ht 1).trans hycard1
    refine le_trans ?_ h1
    rw [← hrw, add_comm]
    apply add_le_add_left <| relRank_insert_le M₂ X y
  refine le_top.trans hinf
termination_by M₁.relRank X Y

theorem Flat_covers {M₁ M₂ : Matroid α} {X Y : Set α}
    (hYE : Y ⊆ M₁.E) (hX2: M₂.Flat X) (hco : Flat_Covers_Flat M₁ Y X) (hMX : M₁.relRank X (M₁.E)= M₂.relRank X (M₂.E) )
    (hQ' : Quotient' M₁ M₂):
    (Flat_Covers_Flat M₂ Y X) ∧ M₁.relRank Y (M₁.E)= M₂.relRank Y (M₁.E) := by
      --have hcas:= lt_or_le (M₁.relRank X Y) ⊤
      --obtain(hfin|hinf):= hcas
      --unfold Flat_Covers_Flat at hco
      have hey : ∃ y ∈ Y \ X, M₁.relRank X ({y}) = 1 := by
        sorry
      constructor
      · refine ⟨?_ ,hX2 , hco.2.2.1 , ?_⟩
        · sorry
        · sorry
      · sorry




  --cases' (M₁.relRank X Y) using ENat.recTopCoe with n
  --· exact OrderTop.le_top (M₂.relRank X Y)
