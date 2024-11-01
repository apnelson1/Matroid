import Matroid.Minor.Rank

import Matroid.Flat

--import Mathlib.TFAE

--import Mathlib.Topology.Continuity

--relRank
open Set
namespace Matroid

variable {α : Type*} {M N M₁ M₂ : Matroid α} {X Y F : Set α}

@[mk_iff]
structure Quotient (M N : Matroid α) : Prop where
  forall_flat_of_flat : ∀ F, M.Flat F → N.Flat F
  ground_eq : M.E = N.E

@[mk_iff]
structure WeakLE (M N : Matroid α) : Prop where
  forall_dep_of_dep : ∀ D, N.Dep D → M.Dep D
  ground_eq : M.E = N.E

def Flat_Covers_Flat (M: Matroid α) (F₁ F₂ : Set α) : Prop :=
  M.Flat F₁ ∧ M.Flat F₂ ∧ F₂ ⊆ F₁ ∧ M.relRank F₂ F₁ = 1

def Quotient' (M₁ M₂ : Matroid α) : Prop :=
 M₁.E = M₂.E ∧ ∀ X Y, X ⊆ Y → Y ⊆ M₁.E → M₂.relRank X Y ≤ M₁.relRank X Y

infixl:50 " ≤q " => Matroid.Quotient

infixl:50 " ≤w " => Matroid.WeakLE
--(hE: M₁.E=M₂.E)

lemma Quotient.flat_of_flat (h : M ≤q N) (hF : M.Flat F) : N.Flat F :=
  h.forall_flat_of_flat _ hF

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
  exact hFlat.closure_subset_of_subset hXin

theorem Quo_3_1 {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
    (hQ : ∀ X ⊆ M₁.E, M₁.closure X ⊆ M₂.closure X) : M₂ ≤q M₁ := by
  refine ⟨fun F hF ↦ ?_, hE.symm⟩
  have hFE : F ⊆ M₁.E := hF.subset_ground.trans_eq hE.symm
  exact flat_iff_closure_self.2 <|
    ((hQ _ hFE).trans hF.closure.subset).antisymm <| subset_closure _ _ hFE

--Write the following are equivalent thm

theorem TFAE_Quotient {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E) :
 List.TFAE [M₂ ≤q M₁,
    ∀ Y Z, Z ⊆ Y → Y ⊆ M₁.E → M₂.relRank Z Y ≤ M₁.relRank Z Y,
    ∀ X ⊆ M₁.E, M₁.closure X ⊆ M₂.closure X] := by
  tfae_have 1 → 2 := by
    intro hQ
    intro X Y hXY hXE
    exact Quotient.relRank_le hQ hXY hXE

  tfae_have 2 → 3 := by
    intro hQ X hX
    exact Quo_2_3 hE hX hQ

  tfae_have 3 → 1 := by
    intro hQ
    exact Quo_3_1 hE hQ

  tfae_finish

--Begin finite case

lemma Quotient.finite {M₁ M₂ : Matroid α} [hM₁ : FiniteRk M₁] (hQ : M₂ ≤q M₁) : FiniteRk M₂ := by
  rw [finiteRk_iff, erk_def, ← lt_top_iff_ne_top, ← relRank_empty_left] at hM₁ ⊢
  rw [← hQ.ground_eq] at hM₁
  exact (hQ.relRank_le (empty_subset _) hQ.ground_eq.subset).trans_lt hM₁

theorem Quotient.covBy_of_covBy [FiniteRk M₁] (hQ : M₂ ≤q M₁) (hco : X ⋖[M₁] Y) (hX2 : M₂.Flat X)
    (hS : M₁.r X + M₂.rk = M₂.r X + M₁.rk) : ∃ y ∈ Y, Y = M₂.closure (insert y X) := by
  have hYE := hco.subset_ground_right
  have := hco.flat_left
  rw [rk_def, rk_def] at hS
  have hE : M₁.E = M₂.E := (Quotient.ground_eq hQ).symm
  have hfr : FiniteRk M₂ := hQ.finite
  have hXY : X ⊆ Y := by exact CovBy.subset hco
  obtain⟨y , hy, hyy ⟩:= CovBy.exists_eq_closure_insert hco
  use y
  refine ⟨ mem_of_mem_diff hy , ?_ ⟩
  --rw [hyy.symm]
  have hXy2 : M₂.Flat (M₂.closure (insert y X)) := closure_flat M₂ (insert y X)
  have hXy1 : M₁.Flat (M₂.closure (insert y X)) := Quotient.flat_of_flat hQ hXy2
  have h1 := hQ.relRank_le (M₂.closure_subset_ground (insert y X)) hE.symm.subset
  have h2 := add_le_add_right h1 (M₂.er (M₂.closure (insert y X)))
  -- have h1 : M₂.relRank (M₂.closure (insert y X)) (M₂.E) ≤ M₁.relRank (M₂.closure (insert y X)) (M₁.E):= by
  --   have := hQ.relRank_le (M₂.closure_subset_ground (insert y X)) hE.symm.subset
  --   rwa [← hE] at this ⊢


  --   sorry
    --exact (TFAE_Quotient hE) hQ
  -- have h2 : M₂.relRank (M₂.closure (insert y X)) (M₂.E) + M₂.er (M₂.closure (insert y X)) ≤
  --     M₁.relRank (M₂.closure (insert y X)) (M₁.E) + M₂.er (M₂.closure (insert y X)) := by
  --   exact add_le_add_right h1 (M₂.er (M₂.closure (insert y X)))
  have hcE1 : (M₂.closure (insert y X)) ⊆ M₂.E := closure_subset_ground M₂ (insert y X)
  rw [relRank_add_er_of_subset M₂ hcE1] at h2
  have h3 : M₂.er M₂.E + M₁.er (M₂.closure (insert y X)) ≤
      M₁.relRank (M₂.closure (insert y X)) M₁.E + M₂.er (M₂.closure (insert y X)) +
        M₁.er (M₂.closure (insert y X)):= by
    convert add_le_add_right h2 _
  rw [hE.symm] at hcE1
  rw [add_assoc, add_comm (M₂.er (M₂.closure (insert y X))) (M₁.er (M₂.closure (insert y X))),
    ←add_assoc, relRank_add_er_of_subset M₁ hcE1] at h3
  -- have h4 : M₂.r M₂.E + M₁.r (M₂.closure (insert y X)) ≤ M₁.r M₁.E + M₂.r (M₂.closure (insert y X)) := by
  simp_rw [← cast_r_eq] at h3
  norm_cast at h3
  --have hFin1 :  M₁.rFin
  -- have h4 : M₂.r M₂.E + M₁.r (M₂.closure (insert y X)) ≤ M₁.r M₁.E + M₂.r (M₂.closure (insert y X)) := by
  --   simp_rw [← cast_r_eq] at h3
  --   norm_cast at h3
  have h5 := Nat.add_le_add_left h3 (M₁.r X)
  -- have h5 : M₁.r X + (M₂.r M₂.E + M₁.r (M₂.closure (insert y X)))
  --     ≤ M₁.r X + (M₁.r M₁.E + M₂.r (M₂.closure (insert y X))) := Nat.add_le_add_left h3 (M₁.r X)
  rw [←add_assoc, hS, ←add_assoc, add_right_comm, add_right_comm (c := M₂.r _)] at h5
  have h7 := Nat.add_le_add_iff_right.mp h5
  -- have h6 : M₂.r X + M₁.r (M₂.closure (insert y X)) + M₁.r M₁.E
  --     ≤ M₁.r X + M₂.r (M₂.closure (insert y X)) + M₁.r M₁.E := by
  --   rwa [add_right_comm, add_right_comm (c := M₂.r _)] at h5
  have h7 : M₂.r X + M₁.r (M₂.closure (insert y X))
      ≤ M₁.r X + M₂.r (M₂.closure (insert y X)) := Nat.add_le_add_iff_right.mp h5
  have h8 : M₁.r (M₂.closure (insert y X))
      ≤ M₁.r X + M₂.r (M₂.closure (insert y X)) - M₂.r X  := Nat.le_sub_of_add_le' h7
  --rw[←add_sub_assoc' (M₁.r X) (M₂.r (M₂.closure (insert y X))) (M₂.r X) ] at h8
  have hFin1 : M₂.rFin X := to_rFin M₂ X
  have hXsub : X ⊆ (M₂.closure (insert y X)) :=
    (M₂.subset_closure X hX2.subset_ground).trans <| M₂.closure_subset_closure (subset_insert _ _)
  --have h9 : M₁.r (M₂.closure (insert y X))
    --  ≤ M₁.r X + M₂.er (M₂.closure (insert y X)) - M₂.er X := by sorry
  --have h10 : M₁.r (M₂.closure (insert y X))
      --≤ M₁.r X + M₂.relRank X (M₂.closure (insert y X)):= by sorry
  --rw [rFin.relRank_eq_sub.symm hFin1 hXsub] at h9
  have hclXf : X = M₂.closure X := Eq.symm (Flat.closure hX2)
  have hy' : y ∈ M₂.E \ M₂.closure X := by
    rw [← hclXf]
    refine ⟨?_ , not_mem_of_mem_diff hy ⟩
    rw [← hE]
    exact hYE (mem_of_mem_diff hy)
  have hX2 : X ⊆ M₂.E := hX2.subset_ground
  --have hfdsf : M₂.er (M₂.closure (insert y X)) - M₂.er X = M₂.relRank X (M₂.closure (insert y X)) := Eq.symm (rFin.relRank_eq_sub hFin1 hXsub)
  --have hhelp : M₂.relRank X (insert y X) = M₂.relRank X (M₂.closure (insert y X)) := Eq.symm (relRank_closure_right M₂ X (insert y X))
  have hdi : M₂.er (M₂.closure (insert y X)) - M₂.er X = 1 := by
    rw [← (rFin.relRank_eq_sub hFin1 hXsub), relRank_closure_right M₂ X (insert y X)]
    exact relRank_insert_eq_one hy' hX2

  rw [← cast_r_eq, ← cast_r_eq, ← ENat.coe_sub, ← Nat.cast_one, Nat.cast_inj] at hdi

  -- This ^^^  is how you convert `hdi` to a statement about `ℕ`,
  -- but it is unlikely you want to use `Nat` subtraction, since
  -- it won't work nicely with `linarith` or `ring` anyway. To exploit `hS`, you will need to
  -- phrase everything in terms of addition, and it probably makes sense to do things this
  -- way in `ℕ∞` in advance.

  sorry











  --cases' (M₁.relRank X Y) using ENat.recTopCoe with n
  --· exact OrderTop.le_top (M₂.relRank X Y)
