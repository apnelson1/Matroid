import Matroid.Minor.Rank

import Matroid.Flat

import Matroid.Constructions.RankAxioms

--relRank

namespace Matroid

variable {α : Type*}

def Quotient (M N : Matroid α) : Prop :=
  M.E = N.E ∧ ∀ F, M.Flat F → N.Flat F

def WeakLE (M N : Matroid α) : Prop :=
  M.E = N.E ∧ ∀ D, N.Dep D → M.Dep D

infixl:50 " ≤q " => Matroid.Quotient

infixl:50 " ≤w " => Matroid.WeakLE
--(hE: M₁.E=M₂.E)

lemma cl_flat_idk (X F: Set α) (M : Matroid α) (hFlat : M.Flat F) (hXF: X ⊆ F) : M.cl X ⊆ F := by
  exact Flat.cl_subset_of_subset hFlat hXF

lemma top_thingy (a b:ℕ∞) (hab: a+b ≤ a) (ht: a ≠ ⊤): b=0 := by
  have haa: a + b ≤ a + 0:= by
    exact le_add_right hab
  --exact WithTop.add_le_add_iff_left.1 (a:=a) (b:=b) (c:=0) ht haa
  sorry

lemma top_thingy_i (a b c : ℕ∞) (hab: b ≤ c): b + a ≤ c + a := by
  exact add_le_add_right hab a
  --exact WithTop.add_le_add_iff_left.1 (a:=a) (b:=b) (c:=0) ht haa
  --exact WithTop.add_le_add_iff_left.1 (a:=a) (b:=b) (c:=0) ht haa


theorem EqQuotient (X Y : Set α) (M₁ M₂: Matroid α) (hXY: X⊆ Y) (hYE: Y⊆ M₁.E) (hQ: Quotient M₂ M₁):
M₂.relRank X Y ≤ M₁.relRank X Y := by
  have hcas:= lt_or_le (M₁.relRank X Y) ⊤
  --Divide into cases finite and infinite
  obtain(hfin|hinf):= hcas

  by_cases hX : Y ⊆ M₁.cl X
  . have hflat: M₂.Flat (M₂.cl X) := by exact cl_flat M₂ X
    have hflat1: M₁.Flat (M₂.cl X) := by exact hQ.2 (M₂.cl X) hflat
    have hXM1: X ∩ M₂.E = X := by
      rw[hQ.1]
      ext x
      constructor
      intro h
      exact Set.mem_of_mem_inter_left h
      intro h
      exact Set.mem_inter h (hYE (hXY h))
    have hFX: X ∩ M₂.E ⊆ (M₂.cl X):= by exact inter_ground_subset_cl M₂ X
    rw[hXM1] at hFX
    have hcl: M₁.cl X ⊆ M₂.cl X:= by exact cl_flat_idk X (M₂.cl X) M₁ hflat1 hFX
    have hze1: M₁.relRank X Y = 0 := by exact (relRank_eq_zero_iff hYE).mpr hX
    have hY: Y ⊆ M₂.cl X:= by exact fun ⦃a⦄ a_1 ↦ hcl (hX a_1)
    have hXE: Y⊆ M₂.E := by
      rw[hQ.1]
      exact hYE
    have hze2: M₂.relRank X Y = 0 := by exact (relRank_eq_zero_iff hXE).mpr hY
    rw[hze2, hze1]

  have hy : ∃ y ∈ Y \ M₁.cl X, M₁.relRank (insert y X) Y < M₁.relRank X Y := by
    by_contra! h_con
    have hin: Y ⊆ M₁.cl X:= by
      intro y hy
      by_cases hyy: y ∈ M₁.cl X
      exact hyy
      have hyi: y ∈ Y \ M₁.cl X:= by exact Set.mem_diff_of_mem hy hyy
      have hp:= h_con y hyi
      suffices hm: M₁.relRank X (insert y X) = 0 by
        have hsu: X ⊆ insert y X:=by exact Set.subset_insert y X
        have hg:= relRank_eq_zero_iff'.1 hm
        have hi: insert y X ⊆ M₁.E:= by
          exact Set.insert_subset (hYE hy) fun ⦃a⦄ a_1 ↦ hYE (hXY a_1)
        have hg1: insert y X ⊆ M₁.cl X:= by exact (relRank_eq_zero_iff hi).mp hm
        have hyi: y ∈ insert y X:= by exact Set.mem_insert y X
        exact hg1 hyi
      have hp1: M₁.relRank X Y = M₁.relRank X (insert y X) + M₁.relRank (insert y X) Y:= by
        rw[relRank_add_of_subset_of_subset ]
        exact Set.subset_insert y X
        exact Set.insert_subset hy hXY
      rw[hp1, add_comm] at hp
      have hsu: X ⊆ insert y X:=by exact Set.subset_insert y X
      have hf1: M₁.relRank (insert y X) Y≤ M₁.relRank X Y := by exact relRank_mono_left M₁ hsu
      have hf: M₁.relRank (insert y X) Y < ⊤ := by exact lt_of_le_of_lt hf1 hfin
      have hfini: M₁.relRank (insert y X) Y ≠ ⊤ := by exact LT.lt.ne_top hf
      exact top_thingy (M₁.relRank (insert y X) Y) (M₁.relRank X (insert y X)) hp hfini

      --have hp2:
      --rw[rFin.relRank_eq_sub,rFin.relRank_eq_sub ] at hp
      -- have hp1: M₁.er (insert y X) ≤ M₁.er X:= by
        --rw[WithTop]
        --linarith [hp]--WithTop
        --simp only [tsub_le_iff_right] at hp
        --rw[le_sub_iff_add_le] at hp
        --rw[ int.add_assoc (M₁.er Y)  (M₁.er (insert y X))  (M₁.er X) , le_sub_iff_add_le] at hp

    exact hX hin

      --refine (mem_cl_iff_forall_mem_flat X fun ⦃a⦄ a_1 ↦ hYE (hXY a_1)).mpr ?_
      --intro F hF hFX
      --suffices hm: M₁.relRank F (insert y F) = 0 by
      --relRank_eq_er_contract, relRank_eq_er_contract


  obtain ⟨y, hy, hycard⟩ := hy
  have hsu: X ⊆ insert y X:=by exact Set.subset_insert y X
  have hiY: insert y X ⊆ Y:= by
    refine Set.insert_subset ?ha hXY
    exact Set.mem_of_mem_diff hy

  have ht := EqQuotient (insert y X) Y M₁ M₂ hiY hYE hQ

  have hycard1 : M₁.relRank (insert y X) Y +1 ≤ M₁.relRank X Y := by
    exact ENat.add_one_le_of_lt hycard

  have h3: M₂.relRank X (insert y X) + M₂.relRank (insert y X) Y= M₂.relRank X Y := by exact relRank_add_of_subset_of_subset M₂ hsu hiY
  have h4: M₂.relRank X (insert y X) ≤ 1:= by
    by_cases hx0: M₂.relRank X (insert y X)=0
    rw[hx0]
    exact zero_le_one' ℕ∞
    have hxne: M₂.relRank X (insert y X)≠ 0:= by exact hx0
    #check RankMatroid.relRank_insert_eq_one_of_ne
    --have h1:= relRank_insert_eq_one_of_ne hxne
    sorry
  have h2: M₂.relRank X Y ≤ M₂.relRank (insert y X) Y +1 := by
    rw[h3.symm, add_comm]
    exact add_le_add_left h4 (M₂.relRank (insert y X) Y)
  have ht1: M₂.relRank (insert y X) Y +1 ≤ M₁.relRank (insert y X) Y +1:= by exact add_le_add_right ht 1
  have hg:= le_trans h2 ht1
  exact le_trans hg hycard1
  have hin: M₁.relRank X Y = ⊤:= by exact eq_top_iff.mpr hinf
  rw[hin]
  exact OrderTop.le_top (M₂.relRank X Y)

termination_by M₁.relRank X Y






  --cases' (M₁.relRank X Y) using ENat.recTopCoe with n
  --· exact OrderTop.le_top (M₂.relRank X Y)
