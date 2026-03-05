import Matroid.Order.Weak
import Matroid.Constructions.Truncate

variable {α : Type*} {M N M₁ M₂ : Matroid α} {F F' X Y Z I : Set α}

open Set

namespace Matroid

@[mk_iff]
structure Quotient (M N : Matroid α) : Prop where
  forall_isFlat_of_isFlat : ∀ F, M.IsFlat F → N.IsFlat F
  ground_eq : M.E = N.E

infixl:50 " ≤q " => Matroid.Quotient

lemma Quotient.isFlat_of_isFlat (h : M ≤q N) (hF : M.IsFlat F) : N.IsFlat F :=
  h.forall_isFlat_of_isFlat _ hF

lemma Quotient.trans {M₁ M₂ M₃ : Matroid α} (h : M₁ ≤q M₂) (h' : M₂ ≤q M₃) : M₁ ≤q M₃ where
  forall_isFlat_of_isFlat _ := h'.isFlat_of_isFlat ∘ h.isFlat_of_isFlat
  ground_eq := h.ground_eq.trans h'.ground_eq

lemma Quotient.refl (M : Matroid α) : M ≤q M where
  forall_isFlat_of_isFlat := by simp
  ground_eq := rfl

lemma Quotient.antisymm (h : M₁ ≤q M₂) (h' : M₂ ≤q M₁) : M₁ = M₂ :=
  ext_isFlat fun _ ↦ ⟨h.isFlat_of_isFlat, h'.isFlat_of_isFlat⟩

lemma Quotient.closure_subset_closure (h : M ≤q N) (X : Set α) : N.closure X ⊆ M.closure X := by
  rw [← closure_inter_ground, ← closure_inter_ground (M := M), ← h.ground_eq]
  rw [← (h.isFlat_of_isFlat (M.closure_isFlat _)).closure]
  apply N.closure_subset_closure
  exact M.subset_closure _

lemma Quotient.weakLE (h : N ≤q M) : N ≤w M := by
  rw [weakLE_iff, and_iff_left h.ground_eq]
  intro I hI
  have hIE : I ⊆ M.E := hI.subset_ground.trans h.ground_eq.subset
  rw [indep_iff_forall_notMem_closure_diff] at hI ⊢
  exact fun e heI hecl ↦ hI heI <| h.closure_subset_closure (I \ {e}) hecl

/-- Relative rank is monotone with respect to the quotient order for sets `X,Y` with `X ⊆ Y ⊆ E`.
This hypothesis isn't required, but is included to facilitate the inductive proof.
See `Quotient.eRelRk_le` for the stronger version applying to all `X` and `Y`.
Note : including `X` as an implicit parameter is needed for well-founded induction to work. -/
private theorem Quotient.eRelRk_le_aux (hQ : M₂ ≤q M₁) {X : Set α} (hXY : X ⊆ Y) (hYE: Y ⊆ M₁.E) :
    M₂.eRelRk X Y ≤ M₁.eRelRk X Y := by
  have hcas := lt_or_ge (M₁.eRelRk X Y) ⊤
  --Divide into cases finite and infinite
  obtain hfin | hinf := hcas

  · by_cases hX : Y ⊆ M₁.closure X
    . rw [(eRelRk_eq_zero_iff (M := M₂) _).2]
      · apply zero_le
      · exact hX.trans (hQ.closure_subset_closure _)
      rwa [hQ.ground_eq]

    obtain ⟨y, hyY, hyX⟩ := not_subset.1 hX

    have hrw := fun M ↦ eRelRk_add_cancel M (subset_insert y X) (insert_subset hyY hXY)
    have hy : y ∈ Y \ M₁.closure X ∧ M₁.eRelRk (insert y X) Y < M₁.eRelRk X Y := by
      refine ⟨⟨hyY, hyX⟩, ?_⟩
      rw [← hrw, eRelRk_insert_eq_one, add_comm, lt_iff_not_ge]
      · intro hle
        simp only [ENat.add_le_left_iff, one_ne_zero, or_false] at hle
        simpa [hle] using (M₁.eRelRk_mono_left Y (subset_insert y X)).trans_lt hfin
      exact ⟨hYE hyY, hyX⟩

    obtain ⟨hy', hycard⟩ := hy

    have hiY: insert y X ⊆ Y := insert_subset hy'.1 hXY
    have ht := hQ.eRelRk_le_aux hiY hYE

    have hycard1 : M₁.eRelRk (insert y X) Y + 1 ≤ M₁.eRelRk X Y := by
      exact Order.add_one_le_of_lt hycard
    have h1 := (add_le_add_left ht 1).trans hycard1
    refine le_trans ?_ h1
    rw [← hrw, add_comm]
    apply add_le_add_right <| eRelRk_insert_le M₂ X y
  refine le_top.trans hinf
termination_by M₁.eRelRk X Y

/-- Relative rank is monotone with respect to the quotient order. -/
theorem Quotient.eRelRk_le (hQ : M₂ ≤q M₁) (X Y : Set α) : M₂.eRelRk X Y ≤ M₁.eRelRk X Y := by
  rw [← eRelRk_inter_ground_right, ← eRelRk_inter_ground_left,
    ← M₁.eRelRk_inter_ground_right, ← M₁.eRelRk_inter_ground_left, hQ.ground_eq,
      eRelRk_eq_union_right, M₁.eRelRk_eq_union_right]
  exact hQ.eRelRk_le_aux subset_union_right <| union_subset inter_subset_right inter_subset_right

theorem quotient_of_forall_closure_subset_closure (hE : M₁.E = M₂.E)
    (hQ : ∀ X ⊆ M₁.E, M₁.closure X ⊆ M₂.closure X) : M₂ ≤q M₁ := by
  refine ⟨fun F hF ↦ ?_, hE.symm⟩
  have hFE : F ⊆ M₁.E := hF.subset_ground.trans_eq hE.symm
  exact isFlat_iff_closure_self.2 <|
    ((hQ _ hFE).trans hF.closure.subset).antisymm <| subset_closure _ _ hFE

theorem quotient_of_forall_eRelRk_le (hE : M₁.E = M₂.E)
    (hYZ : ∀ Y Z, Y ⊆ Z → Z ⊆ M₁.E → M₂.eRelRk Y Z ≤ M₁.eRelRk Y Z) : M₂ ≤q M₁ := by
  refine quotient_of_forall_closure_subset_closure hE fun X hX ↦ ?_
  have hX' : X ⊆ M₂.E := hX.trans hE.subset

  have hXin : X ⊆ M₂.closure X := M₂.subset_closure X

  refine IsFlat.closure_subset_of_subset ?_ hXin

  by_contra! hc
  obtain ⟨e, he, he'⟩ := exists_mem_closure_notMem_of_not_isFlat hc
    ((M₂.closure_subset_ground X).trans hE.symm.subset)
  have heE := mem_of_mem_of_subset he <| M₁.closure_subset_ground _
  have hrr := hYZ (M₂.closure X) (insert e (M₂.closure X)) (subset_insert _ _)
    (insert_subset heE ((M₂.closure_subset_ground X).trans hE.symm.subset))

  rw [(eRelRk_insert_eq_zero_iff).2 he, eRelRk_closure_left, nonpos_iff_eq_zero,
    ← eRelRk_closure_right, closure_insert_closure_eq_closure_insert,
    eRelRk_closure_right, eRelRk_insert_eq_zero_iff] at hrr
  contradiction

lemma quotient_of_forall_closure_subset_closure_indep (hE : M₁.E = M₂.E)
    (hQ : ∀ I, M₁.Indep I → M₁.closure I ⊆ M₂.closure I) : M₂ ≤q M₁ := by
  refine quotient_of_forall_closure_subset_closure hE fun X hX ↦ ?_
  obtain ⟨I, hI⟩ := M₁.exists_isBasis X
  grw [← hI.closure_eq_closure, hQ _ hI.indep, M₂.closure_subset_closure hI.subset]

lemma Quotient.closure_closure_eq_closure_right (h : M₂ ≤q M₁) (X : Set α) :
    M₂.closure (M₁.closure X) = M₂.closure X := by
  rw [← closure_inter_ground (X := X), ← closure_inter_ground (X := X), h.ground_eq]
  refine subset_antisymm ?_ (M₂.closure_subset_closure (M₁.subset_closure _))
  grw [h.closure_subset_closure, closure_closure]

lemma Quotient.closure_closure_eq_closure_left (h : M₂ ≤q M₁) (X : Set α) :
    M₁.closure (M₂.closure X) = M₂.closure X := by
  rw [IsFlat.closure]
  apply h.isFlat_of_isFlat (M₂.closure_isFlat _)

/-- If `M₂ ≤q M₁`, then every circuit of `M₁` is cyclic (a union of circuits) in `M₂`. -/
lemma Quotient.cyclic_of_isCircuit (hQ : M₂ ≤q M₁) {C : Set α} (hC : M₁.IsCircuit C) :
    M₂.Cyclic C := by
  rw [cyclic_iff_forall_exists]
  intro e heC
  have hcl := hQ.closure_subset_closure (C \ {e})
  rw [hC.closure_diff_singleton_eq] at hcl
  have heN := (M₁.subset_closure C hC.subset_ground).trans hcl heC
  have hCN : C ⊆ M₂.E := hC.subset_ground.trans_eq hQ.ground_eq.symm
  rwa [mem_closure_iff_mem_or_exists_isCircuit (diff_subset.trans hCN), or_iff_right (by simp),
    insert_diff_singleton, insert_eq_of_mem heC] at heN

/-- If every circuit of `M₁` is cyclic (a union of circuits) in `M₂`, then `M₂ ≤q M₁`. -/
lemma quotient_of_forall_cyclic_of_isCircuit (hE : M₁.E = M₂.E)
    (h : ∀ C, M₁.IsCircuit C → M₂.Cyclic C) : M₂ ≤q M₁ := by
  refine quotient_of_forall_closure_subset_closure hE fun X hXE ↦ ?_
  obtain ⟨I, hI⟩ := M₁.exists_isBasis X
  simp_rw [← hI.closure_eq_closure, subset_def]
  refine fun e he ↦ ?_
  by_cases heI : e ∈ I
  · exact mem_of_mem_of_subset heI <| hI.subset.trans (M₂.subset_closure X (hXE.trans hE.subset))
  specialize h (M₁.fundCircuit e I) (hI.indep.fundCircuit_isCircuit he heI)
  obtain ⟨C, hCI, hC, heC⟩ := h.exists_of_mem (M₁.mem_fundCircuit e I)
  refine mem_of_mem_of_subset (hC.mem_closure_diff_singleton_of_mem heC)
    (M₂.closure_subset_closure ?_)
  rw [diff_singleton_subset_iff]
  exact hCI.trans ((fundCircuit_subset_insert _ e I).trans (insert_subset_insert hI.subset))

lemma Quotient.dual (hQ : M₂ ≤q M₁) : M₁✶ ≤q M₂✶ := by
  refine quotient_of_forall_cyclic_of_isCircuit hQ.ground_eq fun C hC ↦ ?_
  rw [cyclic_iff_compl_isFlat_dual
    (show C ⊆ M₁✶.E from hC.subset_ground.trans hQ.ground_eq.subset), dual_dual, dual_ground]
  rw [← isCocircuit_def, ← isHyperplane_compl_iff_isCocircuit, hQ.ground_eq] at hC
  exact hQ.isFlat_of_isFlat hC.isFlat

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
  rw [← quotient_dual_iff, dual_delete, dual_delete]
  exact hQ.dual.contract D

theorem contract_quotient_delete (N : Matroid α) (X : Set α) : N ／ X ≤q N ＼ X := by
  simp only [(N.delete_inter_ground_eq X).symm, quotient_iff, isFlat_contract_iff',
    isFlat_delete_iff, and_imp, contract_ground, delete_ground, diff_inter_self_eq_diff, and_true]
  exact fun _ hF hdj ↦ ⟨_, hF, by simp [hdj.sdiff_eq_left]⟩

lemma Quotient.restrict (hQ : M₂ ≤q M₁) (R : Set α) : M₂ ↾ R ≤q M₁ ↾ R := by
  apply quotient_of_forall_closure_subset_closure (by simp)
  simp only [restrict_ground_eq, restrict_closure_eq', union_subset_iff]
  refine fun X hXR ↦ ⟨subset_trans ?_ subset_union_left,
    subset_trans (by simp [hQ.ground_eq]) subset_union_right⟩
  exact inter_subset_inter_left _ <| hQ.closure_subset_closure _

theorem TFAE_quotient (hE : M₁.E = M₂.E) : List.TFAE [
    M₂ ≤q M₁,
    ∀ Y Z, Y ⊆ Z → Z ⊆ M₁.E → M₂.eRelRk Y Z ≤ M₁.eRelRk Y Z,
    ∀ X ⊆ M₁.E, M₁.closure X ⊆ M₂.closure X,
    ∀ C, M₁.IsCircuit C → M₂.Cyclic C,
    M₁✶ ≤q M₂✶] := by
  tfae_have 1 → 2 := fun hQ Y Z _ _ ↦ hQ.eRelRk_le _ _
  tfae_have 2 → 1 := fun h ↦ quotient_of_forall_eRelRk_le hE fun Y Z ↦ h Y Z
  tfae_have 3 → 1 := fun hQ ↦ quotient_of_forall_closure_subset_closure hE hQ
  tfae_have 1 → 3 := fun hQ X _ ↦ hQ.closure_subset_closure X
  tfae_have 1 → 4 := fun hQ _ hC ↦ hQ.cyclic_of_isCircuit hC
  tfae_have 4 → 1 := fun h ↦ quotient_of_forall_cyclic_of_isCircuit hE h
  tfae_have 1 → 5 := Quotient.dual
  tfae_have 5 → 1 := Quotient.of_dual
  tfae_finish

--Begin finite case
lemma Quotient.rankFinite {M₁ M₂ : Matroid α} [hM₁ : RankFinite M₁] (hQ : M₂ ≤q M₁) :
    RankFinite M₂ := by
  rw [← eRank_ne_top_iff, eRank_def, ← lt_top_iff_ne_top, ← eRelRk_empty_left] at hM₁ ⊢
  rw [← hQ.ground_eq] at hM₁
  exact (hQ.eRelRk_le _ _).trans_lt hM₁

/-- If `M₂` is a finitary quotient of a matroid `M₁`, and some base of `M₁` is independent in `M₂`,
then `M₁ = M₂`. This is not true for general matroids; see `Matroid.TruncateFamily`. -/
lemma Quotient.eq_of_isBase_indep [Finitary M₂] (hQ : M₂ ≤q M₁) {B : Set α} (hB₁ : M₁.IsBase B)
    (hB₂ : M₂.Indep B) : M₂ = M₁ := by
  replace hB₂ := show M₂.IsBase B from
    hB₂.isBase_of_maximal fun J hJ hBJ ↦ hB₁.eq_of_subset_indep (hQ.weakLE.indep_of_indep hJ) hBJ
  refine ext_isCircuit_not_indep hQ.ground_eq (fun C hC hCi ↦ ?_)
    (fun C hC ↦ ((hQ.cyclic_of_isCircuit hC).dep_of_nonempty hC.nonempty).not_indep)

  obtain ⟨e, heC, heB⟩ : ∃ e ∈ C, e ∉ B :=
    not_subset.1 fun hss ↦ hC.dep.not_indep (hB₂.indep.subset hss)

  obtain ⟨B', hB', hssB', hB'ss⟩ := hCi.exists_isBase_subset_union_isBase hB₁

  -- extend `C \ {e}` to a basis `B''` of `B'` in `M₂`.
  obtain ⟨B'', hB'', hssB''⟩ := (hC.diff_singleton_indep heC).subset_isBasis_of_subset
    (diff_subset.trans hssB') (hB'.subset_ground.trans_eq hQ.ground_eq.symm)

  have hB''ss := hB''.subset
  replace hB'' := hB''.isBase_of_spanning <| hQ.spanning_of_spanning hB'.spanning

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
    exact hC.finite.diff.diff

  rw [ENat.add_one_le_iff hfin] at hcard
  exact hcard.ne rfl

lemma Quotient.eq_of_spanning_indep [Finitary M₂] (h : M₂ ≤q M₁) (hs : M₁.Spanning X)
    (hi : M₂.Indep X) : M₂ = M₁ :=
  h.eq_of_isBase_indep ((h.weakLE.indep_of_indep hi).isBase_of_spanning hs) hi

lemma Quotient.eq_of_closure_indep [Finitary M₂] (h : M₂ ≤q M₁) (hcl : M₁.E ⊆ M₁.closure X)
    (hi : M₂.Indep X) : M₂ = M₁ := by
  refine h.eq_of_spanning_indep ?_ hi
  rw [spanning_iff, subset_antisymm_iff, and_iff_left hcl,
    and_iff_right (closure_subset_ground ..), ← h.ground_eq]
  exact hi.subset_ground

lemma Quotient.eq_of_eRank_ge [M₂.RankFinite] (h : M₂ ≤q M₁) (hge : M₁.eRank ≤ M₂.eRank) :
    M₂ = M₁ := by
  obtain ⟨B, hB⟩ := M₂.exists_isBase
  obtain ⟨B', hB', hBB'⟩ := (h.weakLE.indep_of_indep hB.indep).exists_isBase_superset
  obtain rfl := hB.finite.eq_of_subset_of_encard_le hBB'
    (by rwa [hB.encard_eq_eRank, hB'.encard_eq_eRank])
  exact h.eq_of_isBase_indep hB' hB.indep

lemma Quotient.eq_of_eRank_ge' [M₁.RankFinite] (h : M₂ ≤q M₁) (hge : M₁.eRank ≤ M₂.eRank) :
    M₂ = M₁ := by
  suffices h' : M₂.RankFinite from h.eq_of_eRank_ge hge
  grw [← eRank_lt_top_iff, h.weakLE.eRank_le, eRank_lt_top_iff]
  assumption

lemma Quotient.map {β : Type*} {f : α → β} (hQ : M₂ ≤q M₁) (hf : InjOn f M₂.E) :
    (M₂.map f hf) ≤q (M₁.map f (by rwa [← hQ.ground_eq])) := by
  simp only [quotient_iff, map_ground, hQ.ground_eq, and_true]
  intro F hF
  rw [isFlat_map_iff] at *
  obtain ⟨F₀, hF₀, rfl⟩ := hF
  exact ⟨_, hQ.isFlat_of_isFlat hF₀, rfl⟩

lemma Quotient.comap {β : Type*} {M₂ M₁ : Matroid β} (hQ : M₂ ≤q M₁) (f : α → β) :
    (M₂.comap f) ≤q (M₁.comap f) := by
  simp only [quotient_iff, comap_ground_eq, hQ.ground_eq, and_true, isFlat_comap_iff_exists,
    forall_exists_index, and_imp]
  rintro _ F hF rfl
  exact ⟨_, hQ.isFlat_of_isFlat hF, rfl⟩

section Constructions

/-- This gives an exotic example of a proper quotient that leaves some bases unchanged. -/
lemma TruncateFamily.quotient (T : M.TruncateFamily) : T.matroid ≤q M := by
  refine quotient_of_forall_closure_subset_closure rfl fun X hX ↦ ?_
  by_cases hXs : T.matroid.Spanning X
  · simp [hXs.closure_eq, closure_subset_ground]
  rw [T.matroid_closure_eq_closure X hX hXs]

lemma truncate_quotient (M : Matroid α) : M.truncate ≤q M := by
  obtain hM | h := M.eq_loopyOn_or_rankPos
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
  nth_rewrite 1 [U.projectBy_eq_map_comap]
  convert ((((M.map some _)).extendBy none
      (U.map some ((Option.some_injective _).injOn))).contract_quotient_delete {none}).comap some
  nth_rewrite 1 [← comap_map (Option.some_injective α) (M := M)]
  rw [ModularCut.extendBy_deleteElem _ (by simp)]

lemma project_quotient (M : Matroid α) (X : Set α) : M.project X ≤q M := by
  refine quotient_of_forall_closure_subset_closure rfl fun Y _ ↦ ?_
  rw [project_closure]
  exact M.closure_subset_closure <| subset_union_left

lemma Quotient.project_quotient_project (h : M₂ ≤q M₁) (X : Set α) :
    M₂.project X ≤q M₁.project X :=
  quotient_of_forall_closure_subset_closure (by simpa using h.ground_eq.symm) fun Y _ ↦
    by simpa using h.closure_subset_closure ..

end Constructions

lemma Quotient.intCast_rank_sub_mono [RankFinite M₁] (hQ : M₂ ≤q M₁) (hXY : X ⊆ Y) :
    (M₂.rk Y : ℤ) - M₂.rk X ≤ (M₁.rk Y : ℤ) - M₁.rk X := by
  have _ : RankFinite M₂ := hQ.rankFinite
  rw [← Nat.cast_sub (M₂.rk_mono hXY), ← Nat.cast_sub (M₁.rk_mono hXY), Nat.cast_le,
    ← Nat.cast_le (α := ℕ∞), ENat.coe_sub, cast_rk_eq, ENat.coe_sub, cast_rk_eq, cast_rk_eq ,
    cast_rk_eq, ← (M₁.isRkFinite_set X).eRelRk_eq_sub hXY,
    ← (M₂.isRkFinite_set X).eRelRk_eq_sub hXY]
  exact eRelRk_le hQ X Y

lemma Quotient.rank_sub_mono [RankFinite M₁] (hQ : M₂ ≤q M₁) (hXY : X ⊆ Y) :
    (M₁.rk X : ℤ) - M₂.rk X ≤ (M₁.rk Y : ℤ) - M₂.rk Y := by
  linarith [hQ.intCast_rank_sub_mono hXY]

theorem Quotient.wcovBy_of_covBy {F F' : Set α} (hQ : M₂ ≤q M₁) (hco : F ⋖[M₁] F') :
    M₂.closure F ⩿[M₂] M₂.closure F' := by
  obtain ⟨e, he, rfl⟩ := hco.exists_eq_closure_insert
  apply (M₂.closure_isFlat F).wCovby_of_subset_closure_insert (e := e) (M₂.closure_isFlat _)
  · exact M₂.closure_subset_closure <| (M₁.subset_closure F hco.subset_ground_left).trans
      <| M₁.closure_subset_closure (subset_insert _ _)
  exact (M₂.closure_subset_closure (hQ.closure_subset_closure _)).trans <| by simp

/-- If there exist `P` and `X` so that `M = P ＼ X` and `N = P ／ X`,
then we can choose such a `P` and `X` so that `X` is independent and coindependent in `P`.-/
lemma exists_project_indep_coindep (P : Matroid α) (X : Set α) :
    ∃ (Q : Matroid α) (Y : Set α), Q.Indep Y ∧ Q.Coindep Y ∧ Q ／ Y = P ／ X ∧ Q ＼ Y = P ＼ X := by
  wlog hXE : X ⊆ P.E generalizing X with aux
  · obtain ⟨Q, Y, hYi, hYc, hc, hd⟩ := aux (X ∩ P.E) inter_subset_right
    exact ⟨Q, Y, hYi, hYc, by simpa using hc, by simpa [delete_inter_ground_eq] using hd⟩
  obtain ⟨I, hI⟩ := P.exists_isBasis X
  obtain ⟨J, hJ⟩ := (P ＼ (X \ I))✶.exists_isBasis I
    (by simp [subset_diff, hI.indep.subset_ground, disjoint_sdiff_right])
  refine ⟨P ＼ (X \ I) ／ (I \ J), J, ?_, ?_, ?_, ?_⟩
  · have hi : (P ＼ (X \ I)).Indep I := hI.indep.indep_delete_of_disjoint disjoint_sdiff_right
    rwa [Indep.contract_indep_iff, and_iff_right disjoint_sdiff_right, union_diff_cancel hJ.subset]
    exact hi.subset diff_subset
  · have hwin := hJ.indep.indep_delete_of_disjoint (D := I \ J) disjoint_sdiff_right
    rwa [← dual_coindep_iff, dual_delete_dual] at hwin
  · rw [contract_contract, diff_union_of_subset hJ.subset,
      ← contract_delete_comm _ disjoint_sdiff_right, hI.contract_eq_contract_delete]
  have hrw := congr_arg Matroid.dual <| hJ.contract_eq_contract_delete
  rwa [dual_contract_dual, delete_delete, diff_union_of_subset hI.subset,
    dual_delete, dual_contract, dual_dual, eq_comm,
    ← contract_delete_comm _ disjoint_sdiff_left] at hrw
