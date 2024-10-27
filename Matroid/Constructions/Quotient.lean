import Matroid.Minor.Rank

import Matroid.Flat

--import Mathlib.TFAE

--import Mathlib.Topology.Continuity

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

lemma closure_flat_idk (X F: Set α) (M : Matroid α) (hFlat : M.Flat F) (hXF: X ⊆ F) : M.closure X ⊆ F := by
  exact Flat.closure_subset_of_subset hFlat hXF

lemma top_thingy {a b : ℕ∞} (hab : a + b ≤ a) (ht : a ≠ ⊤) : b = 0 := by
  have haa : a + b ≤ a + 0 := le_add_right hab
  rwa [WithTop.add_le_add_iff_left ht, nonpos_iff_eq_zero] at haa

lemma Quotient.closure_subset_closure (h : M ≤q N) (X : Set α) : N.closure X ⊆ M.closure X := by
  rw [← closure_inter_ground, ← closure_inter_ground (M := M), ← h.ground_eq]
  rw [← (h.flat_of_flat (M.closure_flat _)).closure]
  apply N.closure_subset_closure
  exact M.subset_closure _

theorem Quotient.relRank_le {M₁ M₂: Matroid α} (hQ : M₂ ≤q M₁) {X : Set α} (hXY : X ⊆ Y)
    (hYE: Y ⊆ M₁.E) : M₂.relRank X Y ≤ M₁.relRank X Y := by
  have hcas:= lt_or_le (M₁.relRank X Y) ⊤
  --Divide into cases finite and infinite
  obtain(hfin|hinf):= hcas

  · by_cases hX : Y ⊆ M₁.closure X
    . rw [(relRank_eq_zero_iff (M := M₂) _).2]
      · apply zero_le
      · exact hX.trans (hQ.closure_subset_closure _)
      rwa [hQ.ground_eq]

    obtain ⟨y, hyY, hyX⟩ := not_subset.1 hX

    have hrw := fun M ↦ relRank_add_cancel M (subset_insert y X) (insert_subset hyY hXY)
    have hy : y ∈ Y \ M₁.closure X ∧ M₁.relRank (insert y X) Y < M₁.relRank X Y := by
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
      exact Order.add_one_le_of_lt hycard
    have h1 := (add_le_add_right ht 1).trans hycard1
    refine le_trans ?_ h1
    rw [← hrw, add_comm]
    apply add_le_add_left <| relRank_insert_le M₂ X y
  refine le_top.trans hinf
termination_by M₁.relRank X Y

lemma Insert_not_closure {M : Matroid α} {X : Set α }{x : α} (hx : x ∈ M.E) (hX : X ⊆ M.E) (hno : x ∈ M.closure X) :
    M.relRank X (insert x X) = 0 := by
  refine relRank_eq_zero_iff'.mpr ?_
  have hxx : (insert x X) ∩ M.E = insert x X := by
    refine inter_eq_left.mpr ?_
    exact insert_subset hx hX
  rw [hxx]
  refine insert_subset_iff.mpr ?_
  constructor
  exact hno
  exact subset_closure_of_subset' M (fun ⦃a⦄ a ↦ a) hX
  --refine relRank_insert_eq_one ?he ?hX

theorem Quo_2_3 {M₁ M₂ : Matroid α} {X: Set α} (hE : M₁.E = M₂.E) (hX: X ⊆ M₁.E)
    (hYZ: ∀ Y Z, Z ⊆ Y → Y ⊆ M₁.E → M₂.relRank Z Y ≤ M₁.relRank Z Y ) :
    M₁.closure X ⊆ M₂.closure X := by
  have hXg: X = X ∩ M₂.E := by
    refine left_eq_inter.mpr ?_
    rw [hE] at hX
    exact hX
  have hXin : X ⊆ M₂.closure X := by
    rw [hXg]
    simp only [closure_inter_ground]
    exact M₂.inter_ground_subset_closure X
  have hFlat : M₁.Flat (M₂.closure X) := by
    by_contra! hc
    have hsu : M₂.closure X ⊆ M₁.E:= by
      rw[hE]
      exact closure_subset_ground M₂ X
    have hex := exists_mem_closure_not_mem_of_not_flat hc hsu
    obtain⟨e , he ⟩:= hex
    have hee : e ∈ M₂.E \ M₂.closure (M₂.closure X) := by
        refine (mem_diff e).mpr ?_
        constructor
        have hsue : M₁.closure (M₂.closure X) ⊆ M₂.E:= by
          rw [hE.symm]
          exact closure_subset_ground M₁ (M₂.closure X)
        exact hsue (mem_of_mem_diff he)
        simp only [closure_closure]
        exact not_mem_of_mem_diff he
    have hc2 : M₂.relRank (M₂.closure X) (insert e (M₂.closure X)) = 1 := by
      have hXi: (M₂.closure X ⊆ M₂.E) := by exact closure_subset_ground M₂ X
      exact relRank_insert_eq_one hee hXi
    have hc1 : M₁.relRank (M₂.closure X) (insert e (M₂.closure X)) = 0 := Insert_not_closure (closure_subset_ground M₁ (M₂.closure X) (mem_of_mem_diff he)) hsu (mem_of_mem_diff he)
    have hi : M₂.closure X ⊆ insert e (M₂.closure X) := subset_insert e (M₂.closure X)
    have hhelp1 : e ∈ M₂.E := by exact mem_of_mem_diff hee
    have he1 : e ∈  M₁.E := by rwa[hE.symm] at hhelp1
    have hEi : insert e (M₂.closure X) ⊆ M₁.E := by exact insert_subset he1 hsu
    have hcon:= hYZ (insert e (M₂.closure X)) (M₂.closure X) hi hEi
    rw[hc1, hc2] at hcon
    norm_num at hcon
  exact closure_flat_idk X (M₂.closure X) M₁ hFlat hXin

theorem Quo_3_1 {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E) (hQ : ∀ X, M₁.closure X ⊆ M₂.closure X) :
    M₂ ≤q M₁ := by
  refine ⟨hE.symm, ?_ ⟩
  intro F hF
  apply flat_iff_closure_self.2
  have hFE2 : F ⊆ M₂.E := hF.subset_ground
  have hFE : F ⊆ M₁.E := by rwa[ hE.symm ] at hFE2
  have hF1 : F ⊆ M₁.closure F := subset_closure_of_subset' M₁ (fun ⦃a⦄ a ↦ a) hFE
  have hcl := hQ F
  have hF2 : M₂.closure F = F := flat_iff_closure_self.1 hF
  rw [hF2] at hcl
  exact Eq.symm (Subset.antisymm hF1 hcl)

--Write the following are equivalent thm

theorem TFAE_Quotient {M₁ M₂ : Matroid α} {X Y Z : Set α} (hE : M₁.E = M₂.E) :
 List.TFAE [M₂ ≤q M₁,
    ∀ Y Z, Z ⊆ Y → Y ⊆ M₁.E → M₂.relRank Z Y ≤ M₁.relRank Z Y,
    ∀ X, M₁.closure X ⊆ M₂.closure X] := by sorry
    --tfae_have 1 → 2



--Begin finite case

--Lemma about finte rank



theorem Flat_covers {M₁ M₂ : Matroid α} {X Y : Set α} [FiniteRk M]
    (hYE : Y ⊆ M₁.E) (hX2: M₂.Flat X) (hco : Flat_Covers_Flat M₁ Y X) (hMX : M₁.relRank X (M₁.E)= M₂.relRank X (M₂.E) )
    (hQ' : Quotient' M₁ M₂):
    (Flat_Covers_Flat M₂ Y X) ∧ M₁.relRank Y (M₁.E)= M₂.relRank Y (M₁.E) := by
      --have hcas:= lt_or_le (M₁.relRank X Y) ⊤
      --obtain(hfin|hinf):= hcas
      --unfold Flat_Covers_Flat at hco
      constructor
      · refine ⟨?_ ,hX2 , hco.2.2.1 , ?_⟩
        · sorry
        · sorry
      · sorry




  --cases' (M₁.relRank X Y) using ENat.recTopCoe with n
  --· exact OrderTop.le_top (M₂.relRank X Y)
