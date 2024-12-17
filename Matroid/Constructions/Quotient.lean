import Matroid.Minor.Rank
import Matroid.Constructions.Truncate
import Matroid.Flat

universe u

open Set
namespace Matroid

variable {α : Type*} {M N M₁ M₂ : Matroid α} {X Y F : Set α}

section Weak

variable {I B D : Set α}

@[mk_iff]
structure WeakLE (N M : Matroid α) : Prop where
  forall_indep_of_indep : ∀ I, N.Indep I → M.Indep I
  ground_eq : N.E = M.E

infixl:50 " ≤w " => Matroid.WeakLE

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma WeakLE.subset_ground_of_subset_ground_left (h : N ≤w M) (hX : X ⊆ N.E := by aesop_mat) :
    X ⊆ M.E :=
  hX.trans h.ground_eq.subset

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma WeakLE.subset_ground_of_subset_ground_right (h : N ≤w M) (hX : X ⊆ M.E := by aesop_mat) :
    X ⊆ N.E :=
  hX.trans h.ground_eq.symm.subset

lemma WeakLE.indep_of_indep (h : N ≤w M) (hI : N.Indep I) : M.Indep I :=
  h.forall_indep_of_indep _ hI

lemma WeakLE.dep_of_dep (h : N ≤w M) (hD : M.Dep D) : N.Dep D := by
  have hIN := h.subset_ground_of_subset_ground_right hD.subset_ground
  contrapose! hD
  rw [not_dep_iff] at hD ⊢
  exact h.indep_of_indep hD

lemma weakLE_iff_forall_dep_of_dep : N ≤w M ↔ N.E = M.E ∧ ∀ D, M.Dep D → N.Dep D := by
  refine ⟨fun h ↦ ⟨h.ground_eq, fun _ ↦ h.dep_of_dep⟩, fun h ↦ ⟨fun D hD ↦ ?_, h.1⟩⟩
  have hDN : D ⊆ N.E := hD.subset_ground
  have hDM : D ⊆ M.E := hDN.trans_eq h.1
  contrapose! hD
  rw [not_indep_iff] at hD ⊢
  exact h.2 _ hD

lemma WeakLE.refl (M : Matroid α) : M ≤w M where
  forall_indep_of_indep := by simp
  ground_eq := rfl

lemma WeakLE.antisymm (h : N ≤w M) (h' : M ≤w N) : N = M :=
  ext_indep h.ground_eq fun _ _ ↦ ⟨h.indep_of_indep, h'.indep_of_indep⟩

lemma WeakLE.trans {M₁ M₂ M₃ : Matroid α} (h : M₁ ≤w M₂) (h' : M₂ ≤w M₃) : M₁ ≤w M₃ where
  forall_indep_of_indep _ := h'.indep_of_indep ∘ h.indep_of_indep
  ground_eq := h.ground_eq.trans h'.ground_eq

lemma WeakLE.delete (h : N ≤w M) (D : Set α) : N ＼ D ≤w M ＼ D := by
  suffices ∀ (I : Set α), N.Indep I → Disjoint I D → M.Indep I by
    simpa (config := { contextual := true }) [weakLE_iff, h.ground_eq]
  exact fun I hI _ ↦ h.indep_of_indep hI

lemma contract_weakLE_delete (M : Matroid α) (X : Set α) : M ／ X ≤w M ＼ X := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  rw [hI.contract_eq_contract_delete]
  simp only [weakLE_iff, delete_indep_iff, hI.indep.contract_indep_iff, and_imp, delete_ground,
    contract_ground, diff_diff, union_diff_self, union_eq_self_of_subset_left hI.subset, and_true]
  refine fun J hJI hi hJ'  ↦ ⟨hi.subset subset_union_left, ?_⟩
  simpa only [diff_union_self, disjoint_union_right, and_iff_left hJI] using hJ'.union_right hJI

end Weak

@[mk_iff]
structure Quotient (M N : Matroid α) : Prop where
  forall_flat_of_flat : ∀ F, M.Flat F → N.Flat F
  ground_eq : M.E = N.E

infixl:50 " ≤q " => Matroid.Quotient

lemma Quotient.flat_of_flat (h : M ≤q N) (hF : M.Flat F) : N.Flat F :=
  h.forall_flat_of_flat _ hF

lemma Quotient.trans {M₁ M₂ M₃ : Matroid α} (h : M₁ ≤q M₂) (h' : M₂ ≤q M₃) : M₁ ≤q M₃ where
  forall_flat_of_flat _ := h'.flat_of_flat ∘ h.flat_of_flat
  ground_eq := h.ground_eq.trans h'.ground_eq

lemma Quotient.refl (M : Matroid α) : M ≤q M where
  forall_flat_of_flat := by simp
  ground_eq := rfl

lemma Quotient.antisymm (h : M₁ ≤q M₂) (h' : M₂ ≤q M₁) : M₁ = M₂ :=
  ext_flat fun _ ↦ ⟨h.flat_of_flat, h'.flat_of_flat⟩

lemma top_thingy {a b : ℕ∞} (hab : a + b ≤ a) (ht : a ≠ ⊤) : b = 0 := by
  have haa : a + b ≤ a + 0 := le_add_right hab
  rwa [WithTop.add_le_add_iff_left ht, nonpos_iff_eq_zero] at haa

lemma Quotient.closure_subset_closure (h : M ≤q N) (X : Set α) : N.closure X ⊆ M.closure X := by
  rw [← closure_inter_ground, ← closure_inter_ground (M := M), ← h.ground_eq]
  rw [← (h.flat_of_flat (M.closure_flat _)).closure]
  apply N.closure_subset_closure
  exact M.subset_closure _

lemma Quotient.weakLE (h : N ≤q M) : N ≤w M := by
  rw [weakLE_iff, and_iff_left h.ground_eq]
  intro I hI
  have hIE : I ⊆ M.E := hI.subset_ground.trans h.ground_eq.subset
  rw [indep_iff_forall_not_mem_closure_diff] at hI ⊢
  exact fun e heI hecl ↦ hI heI <| h.closure_subset_closure (I \ {e}) hecl

/-- Relative rank is monotone with respect to the quotient order for sets `X,Y` with `X ⊆ Y ⊆ E`.
This hypothesis isn't required, but is included to facilitate the inductive proof.
See `Quotient.relRank_le` for the stronger version applying to all `X` and `Y`.
Note : including `X` as an implicit parameter is needed for well-founded induction to work. -/
private theorem Quotient.relRank_le_aux (hQ : M₂ ≤q M₁) {X : Set α} (hXY : X ⊆ Y) (hYE: Y ⊆ M₁.E) :
    M₂.relRank X Y ≤ M₁.relRank X Y := by
  have hcas := lt_or_le (M₁.relRank X Y) ⊤
  --Divide into cases finite and infinite
  obtain hfin | hinf := hcas

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
    have ht := hQ.relRank_le_aux hiY hYE

    have hycard1 : M₁.relRank (insert y X) Y + 1 ≤ M₁.relRank X Y := by
      exact Order.add_one_le_of_lt hycard
    have h1 := (add_le_add_right ht 1).trans hycard1
    refine le_trans ?_ h1
    rw [← hrw, add_comm]
    apply add_le_add_left <| relRank_insert_le M₂ X y
  refine le_top.trans hinf
termination_by M₁.relRank X Y

/-- Relative rank is monotone with respect to the quotient order. -/
theorem Quotient.relRank_le (hQ : M₂ ≤q M₁) (X Y : Set α) : M₂.relRank X Y ≤ M₁.relRank X Y := by
  rw [← relRank_inter_ground_right, ← relRank_inter_ground_left,
    ← M₁.relRank_inter_ground_right, ← M₁.relRank_inter_ground_left, hQ.ground_eq,
      relRank_eq_union_right, M₁.relRank_eq_union_right]
  exact hQ.relRank_le_aux subset_union_right <| union_subset inter_subset_right inter_subset_right

theorem quotient_of_forall_closure_subset_closure (hE : M₁.E = M₂.E)
    (hQ : ∀ X ⊆ M₁.E, M₁.closure X ⊆ M₂.closure X) : M₂ ≤q M₁ := by
  refine ⟨fun F hF ↦ ?_, hE.symm⟩
  have hFE : F ⊆ M₁.E := hF.subset_ground.trans_eq hE.symm
  exact flat_iff_closure_self.2 <|
    ((hQ _ hFE).trans hF.closure.subset).antisymm <| subset_closure _ _ hFE

theorem quotient_of_forall_relRank_le (hE : M₁.E = M₂.E)
    (hYZ : ∀ Y Z, Y ⊆ Z → Z ⊆ M₁.E → M₂.relRank Y Z ≤ M₁.relRank Y Z) : M₂ ≤q M₁ := by
  refine quotient_of_forall_closure_subset_closure hE fun X hX ↦ ?_
  have hX' : X ⊆ M₂.E := hX.trans hE.subset

  have hXin : X ⊆ M₂.closure X := M₂.subset_closure X

  refine Flat.closure_subset_of_subset ?_ hXin

  by_contra! hc
  obtain ⟨e, he, he'⟩ := exists_mem_closure_not_mem_of_not_flat hc
    ((M₂.closure_subset_ground X).trans hE.symm.subset)
  have heE := mem_of_mem_of_subset he <| M₁.closure_subset_ground _
  have hrr := hYZ (M₂.closure X) (insert e (M₂.closure X)) (subset_insert _ _)
    (insert_subset heE ((M₂.closure_subset_ground X).trans hE.symm.subset))

  rw [(relRank_insert_eq_zero_iff).2 he, relRank_closure_left, nonpos_iff_eq_zero,
    ← relRank_closure_right, closure_insert_closure_eq_closure_insert,
    relRank_closure_right, relRank_insert_eq_zero_iff] at hrr
  contradiction

/-- If `M₂ ≤q M₁`, then every circuit of `M₁` is cyclic (a union of circuits) in `M₂`. -/
lemma Quotient.cyclic_of_circuit (hQ : M₂ ≤q M₁) {C : Set α} (hC : M₁.Circuit C) : M₂.Cyclic C := by
  rw [cyclic_iff_forall_exists]
  intro e heC
  have hcl := hQ.closure_subset_closure (C \ {e})
  rw [hC.closure_diff_singleton_eq_closure] at hcl
  have heN := (M₁.subset_closure C hC.subset_ground).trans hcl heC
  have hCN : C ⊆ M₂.E := hC.subset_ground.trans_eq hQ.ground_eq.symm
  rwa [mem_closure_iff_mem_or_exists_circuit (diff_subset.trans hCN), or_iff_right (by simp),
    insert_diff_singleton, insert_eq_of_mem heC] at heN

/-- If every circuit of `M₁` is cyclic (a union of circuits) in `M₂`, then `M₂ ≤q M₁`. -/
lemma quotient_of_forall_cyclic_of_circuit (hE : M₁.E = M₂.E)
    (h : ∀ C, M₁.Circuit C → M₂.Cyclic C) : M₂ ≤q M₁ := by
  refine quotient_of_forall_closure_subset_closure hE fun X hXE ↦ ?_
  obtain ⟨I, hI⟩ := M₁.exists_basis X
  simp_rw [← hI.closure_eq_closure, subset_def]
  refine fun e he ↦ ?_
  by_cases heI : e ∈ I
  · exact mem_of_mem_of_subset heI <| hI.subset.trans (M₂.subset_closure X (hXE.trans hE.subset))
  specialize h (M₁.fundCct e I) (hI.indep.fundCct_circuit ⟨he, heI⟩)
  obtain ⟨C, hC, heC, hCI⟩ := h.exists_of_mem (M₁.mem_fundCct e I)
  refine mem_of_mem_of_subset (hC.mem_closure_diff_singleton_of_mem heC)
    (M₂.closure_subset_closure ?_)
  rw [diff_singleton_subset_iff]
  exact hCI.trans ((fundCct_subset_insert e I).trans (insert_subset_insert hI.subset))

lemma Quotient.dual (hQ : M₂ ≤q M₁) : M₁✶ ≤q M₂✶ := by
  refine quotient_of_forall_cyclic_of_circuit hQ.ground_eq fun C hC ↦ ?_
  rw [cyclic_iff_compl_flat_dual
    (show C ⊆ M₁✶.E from hC.subset_ground.trans hQ.ground_eq.subset), dual_dual, dual_ground]
  rw [← cocircuit_def, ← compl_hyperplane_iff_cocircuit, hQ.ground_eq] at hC
  exact hQ.flat_of_flat hC.flat

lemma Quotient.of_dual (hQ : M₂✶ ≤q M₁✶) : M₁ ≤q M₂ := by
  simpa using hQ.dual

@[simp] lemma quotient_dual_iff : M₁✶ ≤q M₂✶ ↔ M₂ ≤q M₁ :=
  ⟨Quotient.of_dual, Quotient.dual⟩

lemma Quotient.spanning_of_spanning (hQ : M₂ ≤q M₁) {S : Set α} (hS : M₁.Spanning S) :
    M₂.Spanning S := by
  rw [spanning_iff, and_iff_left (hS.subset_ground.trans hQ.ground_eq.symm.subset),
    subset_antisymm_iff, and_iff_right <| M₂.closure_subset_ground _, hQ.ground_eq, ← hS.closure_eq]
  exact hQ.closure_subset_closure S

lemma Quotient.contract (hQ : M₂ ≤q M₁) (C : Set α) : M₂ ／ C ≤q M₁ ／ C := by
  refine quotient_of_forall_closure_subset_closure (by simp [hQ.ground_eq]) fun X _ ↦ ?_
  simp_rw [contract_closure_eq]
  exact diff_subset_diff_left <| hQ.closure_subset_closure (X ∪ C)

lemma Quotient.delete (hQ : M₂ ≤q M₁) (D : Set α) : M₂ ＼ D ≤q M₁ ＼ D := by
  rw [← quotient_dual_iff, delete_dual_eq_dual_contract, delete_dual_eq_dual_contract]
  exact hQ.dual.contract D

lemma Quotient.restrict (hQ : M₂ ≤q M₁) (R : Set α) : M₂ ↾ R ≤q M₁ ↾ R := by
  apply quotient_of_forall_closure_subset_closure (by simp)
  simp only [restrict_ground_eq, restrict_closure_eq', union_subset_iff]
  refine fun X hXR ↦ ⟨subset_trans ?_ subset_union_left,
    subset_trans (by simp [hQ.ground_eq]) subset_union_right⟩
  exact inter_subset_inter_left _ <| hQ.closure_subset_closure _

theorem TFAE_quotient (hE : M₁.E = M₂.E) : List.TFAE [
    M₂ ≤q M₁,
    ∀ Y Z, Y ⊆ Z → Z ⊆ M₁.E → M₂.relRank Y Z ≤ M₁.relRank Y Z,
    ∀ X ⊆ M₁.E, M₁.closure X ⊆ M₂.closure X,
    ∀ C, M₁.Circuit C → M₂.Cyclic C,
    M₁✶ ≤q M₂✶] := by
  tfae_have 1 → 2 := fun hQ Y Z _ _ ↦ hQ.relRank_le _ _
  tfae_have 2 → 1 := fun h ↦ quotient_of_forall_relRank_le hE fun Y Z ↦ h Y Z
  tfae_have 3 → 1 := fun hQ ↦ quotient_of_forall_closure_subset_closure hE hQ
  tfae_have 1 → 3 := fun hQ X _ ↦ hQ.closure_subset_closure X
  tfae_have 1 → 4 := fun hQ _ hC ↦ hQ.cyclic_of_circuit hC
  tfae_have 4 → 1 := fun h ↦ quotient_of_forall_cyclic_of_circuit hE h
  tfae_have 1 → 5 := Quotient.dual
  tfae_have 5 → 1 := Quotient.of_dual
  tfae_finish

--Begin finite case
lemma Quotient.finiteRk {M₁ M₂ : Matroid α} [hM₁ : FiniteRk M₁] (hQ : M₂ ≤q M₁) : FiniteRk M₂ := by
  rw [finiteRk_iff, erk_def, ← lt_top_iff_ne_top, ← relRank_empty_left] at hM₁ ⊢
  rw [← hQ.ground_eq] at hM₁
  exact (hQ.relRank_le _ _).trans_lt hM₁

/-- If `M₂` is a finitary quotient of a matroid `M₁`, and some base of `M₁` is independent in `M₂`,
then `M₁ = M₂`. This is not true for general matroids; see `Matroid.TruncateFamily`. -/
lemma Quotient.eq_of_base_indep [Finitary M₂] (hQ : M₂ ≤q M₁) {B : Set α} (hB₁ : M₁.Base B)
    (hB₂ : M₂.Indep B) : M₂ = M₁ := by
  replace hB₂ := show M₂.Base B from
    hB₂.base_of_maximal fun J hJ hBJ ↦ hB₁.eq_of_subset_indep (hQ.weakLE.indep_of_indep hJ) hBJ
  refine ext_circuit_not_indep hQ.ground_eq (fun C hC hCi ↦ ?_)
    (fun C hC ↦ ((hQ.cyclic_of_circuit hC).dep_of_nonempty hC.nonempty).not_indep)

  obtain ⟨e, heC, heB⟩ : ∃ e ∈ C, e ∉ B :=
    not_subset.1 fun hss ↦ hC.dep.not_indep (hB₂.indep.subset hss)

  obtain ⟨B', hB', hssB', hB'ss⟩ := hCi.exists_base_subset_union_base hB₁

  -- extend `C \ {e}` to a basis `B''` of `B'` in `M₂`.
  obtain ⟨B'', hB'', hssB''⟩ := (hC.diff_singleton_indep heC).subset_basis_of_subset
    (diff_subset.trans hssB') (hB'.subset_ground.trans_eq hQ.ground_eq.symm)

  have hB''ss := hB''.subset
  replace hB'' := hB''.base_of_spanning <| hQ.spanning_of_spanning hB'.spanning

  have hrw1 : B' \ B = C \ B
  · refine subset_antisymm ?_ (diff_subset_diff_left hssB')
    rw [← union_diff_right (s := C)]
    exact diff_subset_diff_left hB'ss

  have hrw2 : B'' \ B = (C \ {e}) \ B
  · rw [subset_antisymm_iff, and_iff_left (diff_subset_diff_left hssB''),
      diff_subset_iff, union_diff_self, ← diff_singleton_eq_self heB, ← union_diff_distrib,
      subset_diff_singleton_iff, union_comm, and_iff_right (hB''ss.trans hB'ss)]
    exact fun heB'' ↦ hC.dep.not_indep
      (hB''.indep.subset (by simpa [heC] using insert_subset heB'' hssB''))

  have hcard := hB'.encard_diff_comm hB₁

  rw [hrw1, ← encard_diff_singleton_add_one (show e ∈ C \ B from ⟨heC, heB⟩),
    diff_diff_comm, ← hrw2, hB''.encard_diff_comm hB₂] at hcard

  replace hcard := hcard.trans_le <| encard_mono <| diff_subset_diff_right hB''ss

  have hfin : (B \ B'').encard ≠ ⊤
  · rw [hB₂.encard_diff_comm hB'', hrw2, encard_ne_top_iff]
    exact (hC.finite.diff _).diff _

  rw [ENat.add_one_le_iff hfin] at hcard
  exact hcard.ne rfl
section Constructions

/-- This gives an exotic example of a proper quotient that leaves some bases unchanged. -/
lemma TruncateFamily.quotient (T : M.TruncateFamily) : T.matroid ≤q M := by
  refine quotient_of_forall_closure_subset_closure rfl fun X hX ↦ ?_
  by_cases hXs : T.matroid.Spanning X
  · simp [hXs.closure_eq, closure_subset_ground]
  rw [T.matroid_closure_eq_closure X hX hXs]

lemma truncate_quotient (M : Matroid α) : M.truncate ≤q M := by
  obtain hM | h := M.eq_loopyOn_or_rkPos
  · rw [hM]
    simp [Quotient.refl]
  rw [← TruncateFamily.matroid_top]
  exact TruncateFamily.quotient _

lemma Quotient.truncate (h : M₂ ≤q M₁) : M₂.truncate ≤q M₁.truncate := by
  refine quotient_of_forall_closure_subset_closure h.ground_eq.symm fun X (hXE : X ⊆ M₁.E) ↦ ?_
  obtain rfl | hssu := hXE.eq_or_ssubset
  · rw [← truncate_ground_eq, closure_ground, truncate_ground_eq, ← h.ground_eq,
      ← M₂.truncate_ground_eq, closure_ground]
  by_cases hX : M₁.truncate.Spanning X
  · suffices hsp : M₂.truncate.Spanning X
    · rw [hsp.closure_eq, truncate_ground_eq, h.ground_eq, ← truncate_ground_eq]
      apply closure_subset_ground
    rw [truncate_spanning_iff_of_ssubset (hssu.trans_eq h.ground_eq.symm)]
    rw [truncate_spanning_iff_of_ssubset hssu] at hX
    obtain ⟨e, ⟨heE, heX⟩, hS⟩ := hX
    exact ⟨e, ⟨h.ground_eq.symm.subset heE, heX⟩, h.spanning_of_spanning hS⟩
  rw [M₁.truncate_closure_eq_of_not_spanning hXE hX]
  exact (h.closure_subset_closure X).trans <| M₂.truncate_quotient.closure_subset_closure X

end Constructions

lemma Quotient.intCast_rank_sub_mono [FiniteRk M₁] (hQ : M₂ ≤q M₁) (hXY : X ⊆ Y) :
    (M₂.r Y : ℤ) - M₂.r X ≤ (M₁.r Y : ℤ) - M₁.r X := by
  have _ : FiniteRk M₂ := hQ.finiteRk
  rw [← Nat.cast_sub (M₂.r_mono hXY), ← Nat.cast_sub (M₁.r_mono hXY), Nat.cast_le,
    ← Nat.cast_le (α := ℕ∞), ENat.coe_sub, cast_r_eq, ENat.coe_sub, cast_r_eq, cast_r_eq ,
    cast_r_eq, ← (M₁.to_rFin X).relRank_eq_sub hXY, ← (M₂.to_rFin X).relRank_eq_sub hXY]
  exact relRank_le hQ X Y

lemma Quotient.rank_sub_mono [FiniteRk M₁] (hQ : M₂ ≤q M₁) (hXY : X ⊆ Y) :
    (M₁.r X : ℤ) - M₂.r X ≤ (M₁.r Y : ℤ) - M₂.r Y := by
  linarith [hQ.intCast_rank_sub_mono hXY]

theorem Quotient.wcovBy_of_covBy {F F' : Set α} (hQ : M₂ ≤q M₁) (hco : F ⋖[M₁] F') :
    M₂.closure F ⩿[M₂] M₂.closure F' := by
  obtain ⟨e, he, rfl⟩ := hco.exists_eq_closure_insert
  apply (M₂.closure_flat F).wCovby_of_subset_closure_insert (e := e) (M₂.closure_flat _)
  · exact M₂.closure_subset_closure <| (M₁.subset_closure F hco.subset_ground_left).trans
      <| M₁.closure_subset_closure (subset_insert _ _)
  exact (M₂.closure_subset_closure (hQ.closure_subset_closure _)).trans <| by simp

-- Use `Flat.covBy_iff_r_eq_add_one` instead of this
-- lemma CovBy_rank_one {M : Matroid α} {X Y: Set α} [FiniteRk M]
--     (hFX : M.Flat X) (hFY : M.Flat Y) (hf :M.r Y = M.r X + 1) (hXY : X ⊂ Y ) :
--     X ⋖[M] Y := by

-- lemma CovBy_equal_cont {M₁ : Matroid α} {X Y₁ Y₂: Set α} (hco1 : X ⋖[M₁] Y₁) (hco : X ⋖[M₁] Y₂)
--    (hy : ∃ y, y ∈ Y₁ ∩ Y₂ ∧ y ∉ X ) : Y₁ = Y₂ := by
--   contrapose! hy
--   simp [hco1.inter_eq_of_covby_of_ne hco hy]

theorem Quotient.covBy_of_covBy [FiniteRk M₁] (hQ : M₂ ≤q M₁) (hco : X ⋖[M₁] Y) (hX2 : M₂.Flat X)
    (hS : M₁.r X + M₂.rk = M₂.r X + M₁.rk) : ∃ y ∈ Y, Y = M₂.closure (insert y X) := by
  have hYE := hco.subset_ground_right
  have hF1X := hco.flat_left
  rw [rk_def, rk_def] at hS
  have hE : M₁.E = M₂.E := (Quotient.ground_eq hQ).symm
  have hfr : FiniteRk M₂ := hQ.finiteRk
  have hXY : X ⊆ Y := CovBy.subset hco
  obtain⟨y , hy, _ ⟩:= CovBy.exists_eq_closure_insert hco
  use y
  refine ⟨ mem_of_mem_diff hy , ?_ ⟩
  --rw [hyy.symm]
  have hXy2 : M₂.Flat (M₂.closure (insert y X)) := closure_flat M₂ (insert y X)
  have hXy1 : M₁.Flat (M₂.closure (insert y X)) := Quotient.flat_of_flat hQ hXy2
  have h1 := hQ.relRank_le (M₂.closure (insert y X)) M₂.E
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
      rw [hE.symm]
      refine insert_subset ?ha fun ⦃a⦄ a_1 ↦ hYE (hXY a_1)
      exact hYE (mem_of_mem_diff hy)
  have hsubcl : insert y X ⊆ M₂.closure (insert y X) := subset_closure_of_subset' M₂ (fun ⦃a⦄ a ↦ a) hXaidcl

  have h9 : M₁.r (M₂.closure (insert y X)) ≤ M₁.r X + (M₂.r (M₂.closure (insert y X)) - M₂.r X) :=
    Nat.le_trans h8 (add_tsub_le_assoc )
  rw [hdi] at h9
  have hf : M₁.r (M₂.closure (insert y X)) = M₁.r X + 1 := by
    have hhm2 : M₁.r X + 1 = M₁.r (insert y X) := by
      have hhel : M₁.r (insert y X) = M₁.r (M₁.closure (insert y X)) := Eq.symm (r_closure_eq M₁)
      have hyEe : y ∈ M₁.E :=  hYE (mem_of_mem_diff hy)
      have hcovy : X ⋖[M₁] M₁.closure (insert y X) := hF1X.covBy_closure_insert
        (not_mem_of_mem_diff hy) (hyEe)
      rw [hhel]
      exact (CovBy.r_eq_of_rFin hcovy (M₁.to_rFin X)).symm
    exact Nat.le_antisymm h9 (le_of_eq_of_le hhm2 (r_le_of_subset M₁ hsubcl))

  have hcovcl : X ⋖[M₁] M₂.closure (insert y X) := by
    have hX2 : M₁.Flat X := Quotient.flat_of_flat hQ hX2
    have hcls : X ⊂ M₂.closure (insert y X) := by
      rw [ssubset_iff_of_subset hXsub]
      exact ⟨ y, hsubcl (mem_insert y X) , not_mem_of_mem_diff hy ⟩
    sorry
  sorry
  --   exact CovBy_rank_one hX2 hXy1 hf hcls
  -- apply CovBy_equal_cont hco hcovcl
  -- exact ⟨y,mem_inter (mem_of_mem_diff hy) (hsubcl (mem_insert y X)), not_mem_of_mem_diff hy ⟩

theorem con_quotient_del (N : Matroid α) (X : Set α) : N ／ X ≤q N ＼ X := by
  simp only [(N.delete_inter_ground_eq X).symm, quotient_iff, flat_contract_iff', flat_delete_iff,
    and_imp, contract_ground, delete_ground, diff_inter_self_eq_diff, and_true]
  exact fun _ hF hdj ↦ ⟨_, hF, by simp [hdj.sdiff_eq_left]⟩

theorem Quotient.forall_superset_k [FiniteRk M₁] {k : ℤ} {F F' : Set α} (hQ : M₂ ≤q M₁)
    (hrk : (M₁.rk : ℤ) - M₂.rk = k) (hFF' : F ⊆ F') (hFk : (M₁.r F : ℤ) - M₂.r F = k) :
    (M₁.r F' : ℤ) - M₂.r F' = k := by
  refine Eq.symm ((fun {x y} ↦ Int.eq_iff_le_and_ge.mpr) ?_)
  refine ⟨ ?_, ?_⟩
  rw[ ←hFk ]
  exact hQ.rank_sub_mono hFF'
  rw [←hrk]
  have hE : M₁.E = M₂.E := Eq.symm hQ.ground_eq
  rw [rk_def M₁, rk_def M₂, ←hE, ← r_inter_ground (X := F'), ← r_inter_ground (X := F'),
    hQ.ground_eq]

  exact hQ.rank_sub_mono inter_subset_right

theorem Quotient.forall_superset_flat [FiniteRk M₁] {k : ℤ} {F F' : Set α} (hQ : M₂ ≤q M₁) (hrk : (M₁.rk : ℤ) - M₂.rk = k)
    (hFF' : F ⊆ F') (hF'E : F' ⊆ M₁.E) (hFk : (M₁.r F : ℤ) - M₂.r F = k) (hF'Flat1 : M₁.Flat F')
    : M₂.Flat F' := by
  by_contra! hcon
  have hE : M₁.E = M₂.E := Eq.symm hQ.ground_eq
  rw [hE] at hF'E
  obtain ⟨e, heEF', hin ⟩ := exists_insert_r_eq_of_not_flat hF'E hcon
  rw [← hE] at hF'E
  rw [← hE] at heEF'
  --have hF'eE : insert e F' ⊆ M₁.E := by exact insert_subset (mem_of_mem_diff heEF') hF'E
  have h1 : M₁.r (insert e F') - M₂.r (insert e F') ≤ k := by
    rw[ ←hrk, rk_def M₁, rk_def M₂, ←hE]
    exact hQ.rank_sub_mono (insert_subset (mem_of_mem_diff heEF') hF'E )
  have h2 : k < M₁.r (insert e F') - M₂.r (insert e F') := by
    rw [ ←(hQ.forall_superset_k hrk hFF' hFk) ]
    have hme : M₁.r (F') < M₁.r (insert e F') := by
      rw [ Flat.insert_r_eq hF'Flat1 heEF' ]
      exact lt_add_one (M₁.r F')
    rw [hin]
    linarith
  linarith


-- theorem Quotient.covBy_of_covBy_gen [FiniteRk M₁] (hQ : M₂ ≤q M₁) (hsub : X ⊆ Y) (hX2 : M₂.Flat X)
--     (hS : M₁.r X + M₂.rk = M₂.r X + M₁.rk) : M₂.Flat Y ∧ ( M₁.r Y + M₂.rk = M₂.r Y + M₁.rk ) := by
--   --let k := M₁.r Y - M₁.r X
--   suffices hi : ∀ i : ℕ, M₁.r Y = i + M₁.r X → M₂.Flat Y ∧ ( M₁.r Y + M₂.rk = M₂.r Y + M₁.rk )
--   · have hbig : M₁.r X ≤ M₁.r Y := by exact r_le_of_subset M₁ hsub
--     have hin: ∃ k, M₁.r X + k = M₁.r Y := Nat.le.dest hbig
--     obtain ⟨ k, hk ⟩ := hin
--     apply hi k
--     rw [add_comm] at hk
--     exact id (Eq.symm hk)
--   · intro i hi
--     induction' i with n IH generalizing Y
--     · simp only [zero_add] at hi
--       have h1xf : M₁.Flat X := by exact flat_of_flat hQ hX2
--       have hequal : X = Y := by sorry
--       rw [hequal] at hX2
--       rw [hequal] at hS
--       exact ⟨hX2, hS⟩
--     · sorry

def Quotient.modularCut_of_k {M₁ M₂ : Matroid α} {k : ℤ} [FiniteRk M₁] (hQ : M₂ ≤q M₁)
    (hrk : (M₁.rk : ℤ) - M₂.rk = k) := ModularCut.ofForallModularPairInter M₁
    (U := { F | M₁.Flat F ∧ M₂.Flat F ∧ ((M₁.r F : ℤ) - M₂.r F = k) })
    (h_flat := fun F hF ↦ hF.1)
    (h_superset := by
      intro F F' hF hF'Flat1 hFF'
      have hF'E : F' ⊆ M₁.E := hF'Flat1.subset_ground
      refine ⟨ hF'Flat1, ?_, ?_⟩
      · exact hQ.forall_superset_flat hrk hFF' hF'E (hF.2.2) hF'Flat1
      · exact hQ.forall_superset_k hrk hFF' (hF.2.2))
    (h_pair := by
      intro F F' hF hF' hFF'M
      refine ⟨Flat.inter hF.1 hF'.1, Flat.inter hF.2.1 hF'.2.1, ?_ ⟩
      refine Eq.symm ((fun {x y} ↦ Int.eq_iff_le_and_ge.mpr) ?_)
      rw [modularPair_iff_r] at hFF'M
      zify at hFF'M
      constructor
      · --have hhelp : ↑(M₁.r (F ∩ F')) ≤ ↑(M₂.r (F ∩ F')) := by sorry
        --rw [hFF'M.er_add]
        --ModularPair.er_add_er
        sorry
      · sorry
    )




lemma Quotient.exists_extension_quotient_contract_of_rk_lt {f : α} (hQ : M₂ ≤q M₁)
    (hr : M₂.rk < M₁.rk) (hf : f ∉ M₂.E) :
    ∃ M, M.Nonloop f ∧ ¬ M.Coloop f ∧ M ＼ f = M₁ ∧ M₂ ≤q M ／ f := by
  have hfin : M₁.FiniteRk
  · rw [finiteRk_iff]
    intro h
    simp [rk, h] at hr
  obtain ⟨k, hkpos, hrk⟩ := exists_pos_add_of_lt hr
  -- The discrepancy here is `k`. Now define the extension. The loop conditions stops you
  -- from cheating by choosing trivial modular cuts.
  sorry



theorem Quotient.of_foo_many {M₁ M₂ : Matroid α} {X : Finset α} [FiniteRk M₁] (hQ : M₂ ≤q M₁)
    (hr : M₂.rk + X.card = M₁.rk) (hX₁ : Disjoint (X : Set α) M₁.E) :
    ∃ (N : Matroid α), (X : Set α) ⊆ N.E ∧ N ＼ (X : Set α) = M₁ ∧ N ／ (X : Set α) = M₂ := by
  classical
  have hM₂fin := hQ.finiteRk

  induction' X using Finset.induction with e Y heY IH generalizing M₁
  · obtain ⟨B, hB⟩ := M₂.exists_base_finset
    have hB₁ : M₁.Base B := by simpa [← hr, hB.finset_card]
      using (hQ.weakLE.indep_of_indep hB.indep).base_of_card
    simp [hQ.eq_of_base_indep hB₁ hB.indep]

  rw [Finset.card_insert_of_not_mem heY] at hr
  obtain ⟨-, heM₂⟩ : Disjoint (↑Y) M₂.E ∧ e ∉ M₂.E := by
    simpa only [Finset.coe_insert, ← union_singleton, ← hQ.ground_eq, disjoint_union_left,
      disjoint_singleton_left] using hX₁

  obtain ⟨M, henl, hecl, rfl, hQ'⟩ :=
    hQ.exists_extension_quotient_contract_of_rk_lt (by linarith) heM₂

  have hfin' : M.FiniteRk
  · rwa [finiteRk_iff, ← lt_top_iff_ne_top, ← delete_elem_erk_eq hecl, lt_top_iff_ne_top,
      ← finiteRk_iff]

  have hre : (M ／ e).rk + 1 = (M ＼ e).rk
  · rw [henl.contract_rk_add_one_eq, M.delete_elem_rk_eq hecl]

  obtain ⟨N, hNss, hN_eq, hNc, hNd⟩ := IH hQ' (by linarith) (hX₁.mono_left (by simp))
  obtain ⟨P, rfl, rfl⟩ := exists_common_major_of_delete_eq_contractElem (by assumption) hNss hN_eq
  use P
  simp only [Finset.coe_insert, ← union_singleton, union_subset_iff, singleton_subset_iff, ←
    delete_delete, deleteElem, true_and]
  rw [union_comm, ← contract_contract, ← contract_elem, and_iff_left rfl]
  rw [contract_elem, contract_ground, subset_diff] at hNss

  exact ⟨hNss.1, mem_of_mem_of_subset henl.mem_ground diff_subset⟩


theorem Quotient.of_foo {α : Type u} {M₁ M₂ : Matroid α} [FiniteRk M₂] (h : M₁ ≤q M₂) :
  ∃ (β : Type u) (N : Matroid (α ⊕ β)),
      M₁ = (N ／ (Sum.inr '' univ : Set (α ⊕ β))).comap Sum.inl ∧
      M₂ = (N ＼ (Sum.inr '' univ : Set (α ⊕ β))).comap Sum.inl := sorry

-- `Sum.inr '' univ : Set (α ⊕ β)` means the set of all the stuff in `α ⊕ β` coming from `β`.

-- Construct a modular cut using `ModularCut.ofForallModularPairInter`,
-- which now works for finite-rank matroids.
-- Use `modularPair_iff_r` to rewrite `ModularPair` with the rank definition.

-- lemma something {M₁ M₂ : Matroid α} {X : Finset α} [FiniteRk M₂] (h : M₁ ≤q M₂)
--     (hr : M₁.rk + X.card = M₂.rk) (hX₁ : Disjoint (X : Set α) M₁.E) :
