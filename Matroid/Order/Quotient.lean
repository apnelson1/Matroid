import Matroid.Order.Weak
import Matroid.Constructions.Truncate

variable {α : Type*} {M N M₁ M₂ : Matroid α} {F F' X Y Z I : Set α}

open Set

namespace Matroid

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

theorem con_quotient_del (N : Matroid α) (X : Set α) : N ／ X ≤q N ＼ X := by
  simp only [(N.delete_inter_ground_eq X).symm, quotient_iff, flat_contract_iff', flat_delete_iff,
    and_imp, contract_ground, delete_ground, diff_inter_self_eq_diff, and_true]
  exact fun _ hF hdj ↦ ⟨_, hF, by simp [hdj.sdiff_eq_left]⟩

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

lemma Quotient.map {β : Type*} {f : α → β} (hQ : M₂ ≤q M₁) (hf : InjOn f M₂.E) :
    (M₂.map f hf) ≤q (M₁.map f (by rwa [← hQ.ground_eq])) := by
  simp only [quotient_iff, map_ground, hQ.ground_eq, and_true]
  intro F hF
  rw [flat_map_iff] at *
  obtain ⟨F₀, hF₀, rfl⟩ := hF
  exact ⟨_, hQ.flat_of_flat hF₀, rfl⟩

lemma Quotient.comap {β : Type*} {M₂ M₁ : Matroid β} (hQ : M₂ ≤q M₁) (f : α → β) :
    (M₂.comap f) ≤q (M₁.comap f) := by
  simp only [quotient_iff, comap_ground_eq, hQ.ground_eq, and_true, flat_comap_iff_exists,
    forall_exists_index, and_imp]
  rintro _ F hF rfl
  exact ⟨_, hQ.flat_of_flat hF, rfl⟩

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

lemma projectBy_quotient (U : M.ModularCut) : M.projectBy U ≤q M := by
  nth_rewrite 1 [projectBy_eq_map_comap]
  convert ((((M.map some _)).extendBy none
      (U.map some _)).con_quotient_del {none}).comap some
  nth_rewrite 1 [← comap_map (Option.some_injective α) (M := M)]
  rw [← deleteElem, ModularCut.extendBy_deleteElem _ (by simp)]

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