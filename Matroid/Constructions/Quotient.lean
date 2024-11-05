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

lemma Cov_Same_r {M : Matroid α} {X Y: Set α} [FiniteRk M] (hY : Y ⊆ M.E)
    (hFX : M.Flat X) (hXY : X ⊆ Y) (heq : M.r X = M.r Y) : X = Y := by
  refine Subset.antisymm hXY ?h₂
  apply Flat.subset_of_relRank_eq_zero hFX
  have hX : M.rFin X := by exact to_rFin M X
  have hY : M.rFin Y := by exact to_rFin M Y
  have ham2 : M.er Y - M.er X = 0 := by
    rw [(rFin.cast_r_eq hY).symm, (rFin.cast_r_eq hX).symm, ← ENat.coe_sub ]
    have heq2 : M.r Y - M.r X = 0 := by exact Eq.symm (Nat.eq_sub_of_add_eq' (id (Eq.symm heq.symm)))
    exact congrArg Nat.cast heq2
  rw [ham2.symm]
  exact rFin.relRank_eq_sub hX hXY


  --have ham : M.relRank X Y + M.er X = M.relRank X Y + M.er Y := by exact congrArg (HAdd.hAdd (M.relRank X Y)) heq1
  --rw [relRank_add_er_of_subset] at ham
    -- have ham1 : M.er Y - M.er Y = M.relRank X Y := by
    --   --have hYfin  : Y Finset α :=
    --   rw [(rFin.cast_r_eq hY).symm, ← ENat.coe_sub]
    --   have h1 : M.r Y - M.r Y = M.relRank X Y := by sorry

    -- rw[ham1.symm]
    -- exact tsub_self (M.er Y)

      -- refine AddLECancellable.tsub_eq_of_eq_add' ?ha ham
      -- unfold AddLECancellable
      -- refine fun ⦃b c⦄ ha ↦ ?_ha
      -- rw [(cast_r_eq M Y ).symm] at ha
      -- have ha2 : ↑(M.r Y + b) ≤ ↑(M.r Y + c) := by exact ha
      -- refine Cardinal.ofENat_le_ofENat.mp ?_

      --apply with_top.coe_le_coe


  --have hsub : M.r X - M.r Y = 0 := by exact Eq.symm (Nat.eq_sub_of_add_eq' (id (Eq.symm heq)))
  --have ham : M.er X - M.er Y = 0 := by
    --have hX : M.rFin X := by exact to_rFin M X
    --have hY : M.rFin Y := by exact to_rFin M Y

    --rw [rFin.cast_r_eq hX ]
  --obtain (ha | hb ) := Set.eq_or_ssubset_of_subset hXY

lemma CovBy_rank_one {M : Matroid α} {X Y: Set α} [FiniteRk M]
    (hFX : M.Flat X) (hFY : M.Flat Y) (hf :M.r Y = M.r X + 1) (hXY : X ⊂ Y ) :
    X ⋖[M] Y := by
  have hY : Y ⊆ M.E := by exact hFY.subset_ground
  apply covBy_iff.2
  refine ⟨hFX , hFY , hXY, ?_ ⟩
  intro F hF hXF hFcl
  have hX : F ⊆ M.E := by exact fun ⦃a⦄ a_1 ↦ hY (hFcl a_1)
  have hrX : M.r X ≤ M.r F := r_le_of_subset M hXF
  have hrY : M.r F ≤ M.r Y := r_le_of_subset M hFcl
  --have hc := le_iff_lt_or_eq.1 hrX
  obtain ( ha | hb ) := le_iff_lt_or_eq.1 hrX
  · right
    have hEq : M.r F = M.r X + 1 := by
      rw [hf] at hrY
      exact Nat.le_antisymm hrY ha
    rw [hf.symm] at hEq
    --exact (Cov_Same_r hFY hFcl hEq)
    exact Cov_Same_r hY hF hFcl hEq
  · left
    exact (Cov_Same_r hX hFX hXF hb).symm

--lemma CovBy_notequal {M : Matroid α} {X Y F: Set α} (hco : X ⋖[M₁] Y) (hF : M.Flat F) (hXF : X ⊆ F)
  --  (hFY : F ⊆ Y) :

lemma CovBy_equal_cont {M₁ : Matroid α} {X Y₁ Y₂: Set α} (hco1 : X ⋖[M₁] Y₁) (hco : X ⋖[M₁] Y₂)
   (hy : ∃ y, y ∈ Y₁ ∩ Y₂ ∧ y ∉ X ) : Y₁ = Y₂ := by
  have hEY1 : Y₁ ⊆ M₁.E := by exact CovBy.subset_ground_right hco1
  --have hEY2 : Y₂ ⊆ M₁.E := by exact CovBy.subset_ground_right hco
  --have hsub : Y₁ ∩ Y₂ ⊆ Y₁ := by exact inter_subset_left
  --have hhelp : M₁.Flat Y₁ := by exact CovBy.flat_right hco1
  have hflat1 : Y₁ = M₁.closure Y₁ := by exact Eq.symm (Flat.closure (CovBy.flat_right hco1))
  have hflat2 : Y₂ = M₁.closure Y₂ := by exact Eq.symm (Flat.closure (CovBy.flat_right hco))
  have hE1 : Y₁ ∩ Y₂ ⊆ M₁.E := by exact fun ⦃a⦄ a_1 ↦ hEY1 (inter_subset_left a_1)
  have hini : X ⊆ Y₁ ∩ Y₂ := by
    refine subset_inter ?rs ?rt
    exact CovBy.subset hco1
    exact CovBy.subset hco
  have hincl : X ⊆ M₁.closure (Y₁ ∩ Y₂) := by exact subset_closure_of_subset' M₁ hini fun ⦃a⦄ a_1 ↦ hE1 (hini a_1)
  obtain ⟨y , hyy, hyx⟩ := hy
  --have hyi : y ∈ M₁.closure (Y₁ ∩ Y₂) \ X := by
    --refine mem_diff_of_mem (mem_closure_of_mem M₁ hyy hE1) hyx
  have hF : M₁.Flat (M₁.closure (Y₁ ∩ Y₂)) := by exact closure_flat M₁ (Y₁ ∩ Y₂)
  have hsubF : M₁.closure (Y₁ ∩ Y₂) ⊆ Y₁ := by
    nth_rewrite 2 [hflat1]
    exact closure_subset_closure M₁ (inter_subset_left)
  have hsubF2 : M₁.closure (Y₁ ∩ Y₂) ⊆ Y₂ := by
    nth_rewrite 2 [hflat2]
    exact closure_subset_closure M₁ (inter_subset_right)
  have h1: M₁.closure (Y₁ ∩ Y₂) = Y₁ := by
    obtain (ha | hb ) := (covBy_iff.1 hco1).2.2.2 (M₁.closure (Y₁ ∩ Y₂)) hF hincl hsubF
    by_contra
    have hcon: M₁.closure (Y₁ ∩ Y₂) ≠ X := by
      refine Ne.symm ?h
      apply ne_of_not_superset
      apply Set.not_subset.2
      use y
      constructor
      exact mem_closure_of_mem M₁ hyy hE1
      exact hyx
    exact hcon ha
    exact hb
  have h2: M₁.closure (Y₁ ∩ Y₂) = Y₂ := by
    obtain (ha | hb ) := (covBy_iff.1 hco).2.2.2 (M₁.closure (Y₁ ∩ Y₂)) hF hincl hsubF2
    by_contra
    have hcon: X ≠ M₁.closure (Y₁ ∩ Y₂) := by
      apply ne_of_not_superset
      apply Set.not_subset.2
      use y
      constructor
      exact mem_closure_of_mem M₁ hyy hE1
      exact hyx
    exact hcon.symm ha
    exact hb
  rw [h1.symm]
  nth_rewrite 2 [h2.symm]
  rfl




theorem Quotient.covBy_of_covBy [FiniteRk M₁] (hQ : M₂ ≤q M₁) (hco : X ⋖[M₁] Y) (hX2 : M₂.Flat X)
    (hS : M₁.r X + M₂.rk = M₂.r X + M₁.rk) : ∃ y ∈ Y, Y = M₂.closure (insert y X) := by
  have hYE := hco.subset_ground_right
  have hF1X:= hco.flat_left
  rw [rk_def, rk_def] at hS
  have hE : M₁.E = M₂.E := (Quotient.ground_eq hQ).symm
  have hfr : FiniteRk M₂ := hQ.finite
  have hXY : X ⊆ Y := by exact CovBy.subset hco
  obtain⟨y , hy, _ ⟩:= CovBy.exists_eq_closure_insert hco
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
  --have h6 := Nat.add_le_add_iff_right.mp h5
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
  have hX2E: X ⊆ M₂.E := hX2.subset_ground
  --have hfdsf : M₂.er (M₂.closure (insert y X)) - M₂.er X = M₂.relRank X (M₂.closure (insert y X)) := Eq.symm (rFin.relRank_eq_sub hFin1 hXsub)
  --have hhelp : M₂.relRank X (insert y X) = M₂.relRank X (M₂.closure (insert y X)) := Eq.symm (relRank_closure_right M₂ X (insert y X))
  have hdi : M₂.er (M₂.closure (insert y X)) - M₂.er X = 1 := by
    rw [← (rFin.relRank_eq_sub hFin1 hXsub), relRank_closure_right M₂ X (insert y X)]
    exact relRank_insert_eq_one hy' hX2E

  rw [← cast_r_eq, ← cast_r_eq, ← ENat.coe_sub, ← Nat.cast_one, Nat.cast_inj] at hdi

  -- This ^^^  is how you convert `hdi` to a statement about `ℕ`,
  -- but it is unlikely you want to use `Nat` subtraction, since
  -- it won't work nicely with `linarith` or `ring` anyway. To exploit `hS`, you will need to
  -- phrase everything in terms of addition, and it probably makes sense to do things this
  -- way in `ℕ∞` in advance.
  have hXaidcl : insert y X ⊆ M₂.E := by
      rw[hE.symm]
      refine insert_subset ?ha fun ⦃a⦄ a_1 ↦ hYE (hXY a_1)
      exact hYE (mem_of_mem_diff hy)
  have hsubcl : insert y X ⊆ M₂.closure (insert y X) := subset_closure_of_subset' M₂ (fun ⦃a⦄ a ↦ a) hXaidcl

  have hFin2 : M₁.rFin X := to_rFin M₁ X
  have h9 : M₁.r (M₂.closure (insert y X)) ≤ M₁.r X + (M₂.r (M₂.closure (insert y X)) - M₂.r X) :=
    Nat.le_trans h8 (add_tsub_le_assoc )
  rw [hdi] at h9
  have hf : M₁.r (M₂.closure (insert y X)) = M₁.r X + 1 := by
    have hhm2 : M₁.r X + 1 = M₁.r (insert y X) := by
      have hhel : M₁.r (insert y X) = M₁.r (M₁.closure (insert y X)) := Eq.symm (r_closure_eq M₁)
      have hyEe : y ∈ M₁.E := by exact hYE (mem_of_mem_diff hy)
      have hcovy : X ⋖[M₁] M₁.closure (insert y X) := by exact Flat.covBy_closure_insert hF1X (not_mem_of_mem_diff hy) (hyEe)
      rw[hhel]
      exact (CovBy.r_eq_of_rFin hcovy hFin2).symm
    exact Nat.le_antisymm h9 (le_of_eq_of_le hhm2 (r_le_of_subset M₁ hsubcl))

  have hcovcl : X ⋖[M₁] M₂.closure (insert y X) := by
    have hX2 : M₁.Flat X := by exact Quotient.flat_of_flat hQ hX2
    have hcls : X ⊂ M₂.closure (insert y X) := by
      apply (ssubset_iff_of_subset hXsub).mpr
      use y
      refine ⟨hsubcl (mem_insert y X) , not_mem_of_mem_diff hy ⟩
    exact CovBy_rank_one hX2 hXy1 hf hcls
  -- have hny : ∃ y, y ∈ Y ∩ (M₂.closure (insert y X)) ∧ y ∉ X := by
  --   use y
  --   constructor
  --   exact mem_inter (mem_of_mem_diff hy) (hsubcl (mem_insert y X))
  --   exact not_mem_of_mem_diff hy
  apply CovBy_equal_cont hco hcovcl
  use y
  constructor
  exact mem_inter (mem_of_mem_diff hy) (hsubcl (mem_insert y X))
  exact not_mem_of_mem_diff hy





  --have hin : X ⊆ (M₂.closure (insert y X)) ∩ Y := by exact subset_inter hXsub hXY
  --have hin2 : (M₂.closure (insert y X)) ∩ Y ⊆ Y := by exact inter_subset_right

  --have hYneX : Y≠ X := by exact Ne.symm (CovBy.ne hco)
  --obtain (ha | hb ) := (covBy_iff.1 hcovcl).2.2.2 Y (CovBy.flat_right hco) hXY hYclosu
  -- · by_contra!
  --   exact hYneX ha
  -- · exact hb












  --cases' (M₁.relRank X Y) using ENat.recTopCoe with n
  --· exact OrderTop.le_top (M₂.relRank X Y)
