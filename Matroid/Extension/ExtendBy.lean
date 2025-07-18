import Matroid.Extension.ModularCut

universe u

open Set Function Set.Notation Option

variable {α : Type*} {M : Matroid α} {I J B F₀ F F' X Y : Set α} {e f : α} {U : M.ModularCut}

namespace Matroid

section extensions

/-- `U.ExtIndep e I` means that `I` is independent in the matroid obtained from `M`
by adding an element `e` using `U`, so either `I` is independent not containing `e`,
or `I = insert e J` for some `M`-independent set `J` whose closure isn't in `U`. -/
def ModularCut.ExtIndep (U : M.ModularCut) (e : α) (I : Set α) : Prop :=
  (M.Indep I ∧ e ∉ I) ∨ (M.Indep (I \ {e}) ∧ M.closure (I \ {e}) ∉ U ∧ e ∈ I)

lemma ModularCut.extIndep_iff_of_notMem (heI : e ∉ I) : U.ExtIndep e I ↔ M.Indep I := by
  simp [ExtIndep, heI]

lemma Indep.extIndep (hI : M.Indep I) (he : e ∉ M.E) : U.ExtIndep e I :=
  .inl ⟨hI, notMem_subset hI.subset_ground he⟩

lemma ModularCut.extIndep_iff_of_mem (heI : e ∈ I) :
    U.ExtIndep e I ↔ M.Indep (I \ {e}) ∧ M.closure (I \ {e}) ∉ U := by
  simp [ExtIndep, heI]

lemma ModularCut.ExtIndep.diff_singleton_indep {U : M.ModularCut} (h : U.ExtIndep e I) :
    M.Indep (I \ {e}) := by
  obtain (h | h) := h; exact h.1.diff _; exact h.1

lemma ModularCut.ExtIndep.subset (h : U.ExtIndep e I) (hJI : J ⊆ I) : U.ExtIndep e J := by
  by_cases heJ : e ∈ J
  · rw [extIndep_iff_of_mem (hJI heJ)] at h
    rw [extIndep_iff_of_mem heJ, and_iff_right (h.1.subset (diff_subset_diff_left hJI))]
    exact fun hJU ↦ h.2 <| U.closure_superset_mem' hJU <| diff_subset_diff_left hJI
  rw [extIndep_iff_of_notMem heJ]
  exact h.diff_singleton_indep.subset (subset_diff_singleton hJI heJ)

lemma ModularCut.ExtIndep.subset_insert_ground (h : U.ExtIndep e I) : I ⊆ insert e M.E :=
  diff_singleton_subset_iff.1 h.diff_singleton_indep.subset_ground

/-- This lemma gives the conditions under which `I` is a maximal `ExtIndep` subset of `X`;
it is essentially characterizing when `I` is a basis of `X` in the matroid
`M.extendBy e U` before `M.extendBy e U` has actually been shown to be a matroid.

We need the lemma here because it is invoked several times when defining `M.extendBy e U`,
but it should not be used elsewhere; good API versions should be stated in terms of
`(M.extendBy e U).IsBasis`, and have less of a dense mess of logic on the RHS. -/
private lemma ModularCut.maximal_extIndep_iff (hX : X ⊆ insert e M.E) (hI : U.ExtIndep e I)
    (hIX : I ⊆ X) : Maximal (fun J ↦ U.ExtIndep e J ∧ J ⊆ X) I ↔
        (M.closure (I \ {e}) = M.closure (X \ {e}) ∧ ((e ∈ I ↔ M.closure (X \ {e}) ∈ U) → e ∉ X))
      ∨ ((M.closure (I \ {e}) ⋖[M] M.closure (X \ {e})) ∧ e ∈ I ∧ M.closure (X \ {e}) ∈ U) := by

  have hss : I \ {e} ⊆ X \ {e} := diff_subset_diff_left hIX
  have hX' : X \ {e} ⊆ M.E := by simpa
  rw [maximal_iff_forall_insert (fun _ _ ht hst ↦ ⟨ht.1.subset hst, hst.trans ht.2⟩)]

  simp only [hI, hIX, and_self, insert_subset_iff, and_true, not_and, true_and, imp_not_comm]

  refine ⟨fun h ↦ ?_, fun h x hxI hi hind ↦ ?_⟩
  · simp only [ExtIndep, imp_not_comm, not_or, not_and, not_not] at h

    obtain (heI | heI) := em (e ∈ I)
    · rw [extIndep_iff_of_mem heI] at hI
      obtain (hclosure | hclosure) := em (M.closure (X \ {e}) ∈ U)
      · simp only [heI, hclosure, not_true_eq_false, imp_false, and_self, and_true]
        refine .inr <| U.covBy_of_maximal_closure (M.closure_subset_closure hss)
          hclosure hI.2 fun x ⟨hx, hxclosure⟩ ↦ ?_
        specialize h x
        have hxI : x ∉ I := by simpa [hx.2] using notMem_of_mem_diff_closure ⟨hX' hx, hxclosure⟩
        rw [← insert_diff_singleton_comm hx.2, hI.1.insert_indep_iff] at h
        exact (h hxI hx.1).2 (.inl ⟨hX' hx, hxclosure⟩) (.inr heI)

      simp only [heI, hclosure, iff_false, not_true_eq_false, not_false_eq_true, implies_true,
        and_true, and_false, or_false]
      refine (M.closure_subset_closure hss).antisymm
        (M.closure_subset_closure_of_subset_closure fun x hx ↦ by_contra fun hxcl ↦ hclosure ?_)
      have hxI : x ∉ I := by simpa [hx.2] using notMem_of_mem_diff_closure ⟨(hX' hx), hxcl⟩

      replace h := show M.closure (insert x (I \ {e})) ∈ U by
        simpa [hxI, hx.1, heI, ← insert_diff_singleton_comm hx.2, hI.1.insert_indep_iff,
          hX' hx, hxcl] using h x

      exact U.closure_superset_mem' h (insert_subset hx hss)
    simp only [mem_insert_iff, heI, or_false] at h
    have hXI : M.closure (X \ {e}) = M.closure (I \ {e}) := by
      refine (M.closure_subset_closure hss).antisymm'
        (M.closure_subset_closure_of_subset_closure fun x hx ↦ ?_)
      rw [hI.diff_singleton_indep.mem_closure_iff', and_iff_right (hX' hx), mem_diff,
        and_iff_left hx.2, diff_singleton_eq_self heI]
      exact fun h' ↦ by_contra fun hxI ↦ by simp [(h x hxI hx.1).1 h'] at hx

    simp only [heI, not_false_eq_true, diff_singleton_eq_self, hXI, false_iff, true_and, false_and,
      and_false, or_false]
    intro heX
    rw [extIndep_iff_of_notMem heI] at hI
    simpa [heI, hI] using (h e heI heX).2

  by_cases heI : e ∈ I
  · have hxe : x ≠ e := by rintro rfl; contradiction
    rw [extIndep_iff_of_mem heI] at hI
    rw [extIndep_iff_of_mem (.inr heI), ← insert_diff_singleton_comm hxe,
      hI.1.insert_indep_iff_of_notMem (by simp [hxI, hxe])] at hind
    simp only [hIX heI, heI, true_iff, true_implies, true_and] at h
    obtain (⟨h_eq, -⟩ | ⟨hcv, h⟩) := h
    · exact notMem_of_mem_diff_closure (h_eq ▸ hind.1) <| by simp [hi, hxe]
    rw [hcv.eq_closure_insert_of_mem_diff ⟨M.mem_closure_of_mem ⟨hi, hxe⟩, hind.1.2⟩,
      closure_insert_closure_eq_closure_insert] at h
    exact hind.2 h

  simp only [heI, not_false_eq_true, diff_singleton_eq_self, false_iff, not_not, false_and,
    and_false, or_false] at h
  obtain (rfl | hne) := eq_or_ne e x
  · rw [extIndep_iff_of_mem (.inl rfl)] at hind
    simp only [mem_singleton_iff, insert_diff_of_mem, hxI, not_false_eq_true,
      diff_singleton_eq_self, h.1] at hind
    exact hind.2 <| h.2 hi

  rw [extIndep_iff_of_notMem heI] at hI
  rw [extIndep_iff_of_notMem (by simp [heI, hne]), hI.insert_indep_iff_of_notMem hxI, h.1] at hind
  refine notMem_of_mem_diff_closure hind ⟨hi, hne.symm⟩

lemma ModularCut.extIndep_aug (hI : U.ExtIndep e I) (hInmax : ¬ Maximal (U.ExtIndep e) I)
    (hBmax : Maximal (U.ExtIndep e) B) : ∃ x ∈ B \ I, U.ExtIndep e (insert x I) := by
  -- TODO : comments to describe the steps of this proof.
  wlog he : ¬ M.IsColoop e with aux
  · rw [not_not] at he
    have hrw : (U.delete {e}).ExtIndep e = U.ExtIndep e := by
      ext I
      simp [ExtIndep, he.mem_closure_iff_mem]
    simp_rw [← hrw] at hInmax hBmax hI ⊢
    refine aux hI hInmax hBmax fun hcl ↦ hcl.mem_ground.2 rfl
  rw [isColoop_iff_diff_closure, not_not] at he
  by_contra! hcon

  have hB : U.ExtIndep e B := hBmax.1
  have hIeE := hI.diff_singleton_indep.subset_ground
  have hBeE := hB.diff_singleton_indep.subset_ground
  have hss : B \ {e} ⊆ (I ∪ B) \ {e} := diff_subset_diff_left subset_union_right

  have hIBe : I ∪ B ⊆ insert e M.E :=
    union_subset hI.subset_insert_ground hB.subset_insert_ground
  have hIBe' : (I ∪ B) \ {e} ⊆ M.E := by rwa [diff_singleton_subset_iff]

  have hImax : Maximal (fun J ↦ U.ExtIndep e J ∧ J ⊆ I ∪ B) I := by
    rw [maximal_iff_forall_insert (fun _ _ ht hst ↦ ⟨ht.1.subset hst, hst.trans ht.2⟩),
      and_iff_right hI, and_iff_right subset_union_left]
    intro x hxI h'
    rw [insert_subset_iff, mem_union, or_iff_right hxI] at h'
    exact hcon x ⟨h'.2.1, hxI⟩ h'.1

  have hrw : U.ExtIndep e = fun J ↦ U.ExtIndep e J ∧ J ⊆ insert e M.E := by
    ext x
    simp only [iff_self_and]
    exact ExtIndep.subset_insert_ground

  rw [hrw, U.maximal_extIndep_iff Subset.rfl hI hI.subset_insert_ground] at hInmax
  rw [hrw, U.maximal_extIndep_iff Subset.rfl hB hB.subset_insert_ground] at hBmax
  rw [U.maximal_extIndep_iff hIBe hI subset_union_left] at hImax

  obtain (rfl | hU) := U.eq_bot_or_ground_mem
  · replace hBmax := show M.Spanning (B \ {e}) ∧ e ∈ B by
      simpa [← spanning_iff_closure_eq hBeE, he] using hBmax
    replace hInmax := show M.Spanning (I \ {e}) → e ∉ I by
      simpa [← spanning_iff_closure_eq hIeE, he] using hInmax
    replace hImax := show M.Spanning (I \ {e}) ∧ e ∈ I by
      simpa [hBmax.2, he, hBmax.1.closure_eq_of_superset hss,
        ← spanning_iff_closure_eq hIeE] using hImax
    exact hInmax hImax.1 hImax.2

  simp only [mem_singleton_iff, insert_diff_of_mem, he, ← spanning_iff_closure_eq hBeE, hU,
    iff_true, mem_insert_iff, true_or, not_true_eq_false, imp_false, ← isHyperplane_iff_covBy,
    and_true, ← spanning_iff_closure_eq hIeE, not_or, not_and, not_not] at hBmax hInmax

  by_cases hsp : M.Spanning ((I ∪ B) \ {e})
  · by_cases heI : e ∈ I
    · replace hImax := show M.IsHyperplane (M.closure (I \ {e})) by
        simpa [hsp.closure_eq, heI, hU, ← isHyperplane_iff_covBy] using hImax
      exact hInmax.2 hImax heI
    replace hInmax := show ¬ M.Spanning (I \ {e}) by simpa [heI, hU] using hInmax
    replace hImax := show M.closure (I \ {e}) = M.E by
      simpa [hsp.closure_eq, heI, he, hU] using hImax
    rw [spanning_iff_closure_eq hIeE] at hInmax
    contradiction

  obtain (⟨hBsp, -⟩ | ⟨hBhp, heB⟩) := hBmax
  · exact hsp <| hBsp.superset hss hIBe'

  have hclclosure : M.closure (B \ {e}) = M.closure ((I ∪ B) \ {e}) := by
    refine by_contra fun hne ↦ hsp <| ?_
    rw [← closure_spanning_iff hIBe']
    have hssu := (M.closure_subset_closure hss).ssubset_of_ne hne
    exact hBhp.spanning_of_ssuperset hssu <| closure_subset_ground _ _

  rw [extIndep_iff_of_mem heB] at hB
  replace hImax := show M.closure (I \ {e}) = M.closure (B \ {e}) ∧ e ∈ I by
    simpa [heB, ← hclclosure, hB.2] using hImax

  replace hInmax := show ¬M.IsHyperplane (M.closure (I \ {e})) by simpa [hImax.2] using hInmax
  exact hInmax <| (hImax.1.symm ▸ hBhp)

private lemma ModularCut.existsMaximalSubsetProperty (U : M.ModularCut) (hXE : X ⊆ insert e M.E) :
  ExistsMaximalSubsetProperty (U.ExtIndep e) X := by
  intro I hI hIX
  obtain ⟨J, hJ, hIJ⟩ :=
    hI.diff_singleton_indep.subset_isBasis_of_subset (diff_subset_diff_left hIX)

  obtain ⟨hJX, heJ⟩ : J ⊆ X ∧ e ∉ J := by simpa [subset_diff] using hJ.subset
  have hJi : U.ExtIndep e J := .inl ⟨hJ.indep, heJ⟩
  by_contra! hcon

  have hconJe : e ∈ X → M.closure (X \ {e}) ∈ U := by
    refine fun heX ↦ by_contra fun hclosure ↦ ?_
    have hind : U.ExtIndep e (insert e J) := by
      rw [extIndep_iff_of_mem (.inl rfl)]
      simpa [heJ, hJ.indep, hJ.closure_eq_closure]
    specialize hcon (insert e J) (by simpa using hIJ)
    rw [maximal_extIndep_iff  hXE hind (insert_subset heX hJX)] at hcon
    simp [heJ, hJ.closure_eq_closure, hclosure] at hcon

  have heI : e ∈ I := by
    refine by_contra fun heI ↦ ?_
    rw [diff_singleton_eq_self heI] at hIJ
    have h' : M.closure (X \ {e}) ∉ U ∧ e ∈ X := by
      simpa [maximal_extIndep_iff hXE hJi hJX, heJ, hJ.closure_eq_closure] using hcon J hIJ
    exact h'.1 <| hconJe h'.2

  rw [extIndep_iff_of_mem heI] at hI
  specialize hconJe (hIX heI)

  obtain (rfl | hssu) := hIJ.eq_or_ssubset
  · rw [hJ.closure_eq_closure] at hI; exact hI.2 hconJe

  refine hI.2 <| U.mem_of_ssubset_indep_of_forall_diff hJ.indep hssu (fun x hx ↦ ?_)
  by_contra! hJu
  have hxe : x ≠ e := by rintro rfl; simp [heJ] at hx
  have hxJI : x ∈ J \ I := by simpa [hxe] using hx

  set J' := insert e (J \ {x}) with hJ'
  have hIeJx : I ⊆ J' := by
    simpa [hJ', insert_diff_singleton_comm hxe.symm, subset_diff, hxJI.2] using hIJ

  have hJ'e : J' \ {e} = J \ {x} := by simp [hJ', heJ]
  specialize hcon J' hIeJx

  have hind : U.ExtIndep e J' := by
    simp only [extIndep_iff_of_mem (show e ∈ J' from .inl rfl), hJ'e]
    exact ⟨hJ.indep.diff _, hJu⟩

  have hJ'X : J' ⊆ X := insert_subset (hIX heI) (diff_subset.trans hJX)

  have hconJ' : (M.closure (J \ {x}) = M.closure J → e ∈ X) ∧
    ¬M.CovBy (M.closure (J \ {x})) (M.closure J) := by
    rw [maximal_extIndep_iff hXE hind hJ'X, iff_true_intro hconJe] at hcon
    simpa [hJ'e, ← hJ.closure_eq_closure, show e ∈ J' from .inl rfl] using hcon

  exact hconJ'.2 <| hJ.indep.closure_diff_covBy hxJI.1

/-- Extend a matroid `M` by a new element `e` using a modular cut `U`.
(If `e` already belongs to `M`, then this deletes the existing element `e` first.) -/
@[simps!] def extendBy (M : Matroid α) (e : α) (U : M.ModularCut) : Matroid α :=
  IndepMatroid.matroid <| IndepMatroid.mk
    (E := insert e M.E)
    (Indep := U.ExtIndep e)
    (indep_empty := Or.inl ⟨M.empty_indep, notMem_empty _⟩)
    (indep_subset := fun _ _ ↦ ModularCut.ExtIndep.subset )
    (indep_aug := fun _ _ ↦ U.extIndep_aug)
    (indep_maximal := fun _ ↦ U.existsMaximalSubsetProperty)
    (subset_ground := fun _ ↦ ModularCut.ExtIndep.subset_insert_ground)

lemma ModularCut.deleteElem_extendBy (he : e ∈ M.E) :
    (M ＼ {e}).extendBy e (ModularCut.ofDeleteElem M e) = M := by
  refine Eq.symm <| ext_indep (by simp [he]) fun I hI ↦ ?_
  obtain (heI | heI) := em' (e ∈ I); simp [extIndep_iff_of_notMem heI, heI]
  obtain ⟨I, rfl, heI'⟩ : ∃ J, I = insert e J ∧ e ∉ J := ⟨I \ {e}, by simp [heI], by simp⟩
  suffices
    M.Indep (insert e I) ↔ M.Indep I ∧ (e ∈ M.closure (M.closure I \ {e}) →
      ¬M.IsFlat (insert e (M.closure I))) by
    simpa [extIndep_iff_of_mem heI, heI']

  refine ⟨fun h ↦ ⟨h.subset (subset_insert _ _), fun he _ ↦ ?_⟩, fun ⟨hIi, h⟩ ↦ ?_⟩
  · suffices e ∈ M.closure (M.closure I) from
      h.notMem_closure_diff_of_mem (.inl rfl) <| by simpa [heI']
    exact (M.closure_subset_closure diff_subset) he
  rw [hIi.insert_indep_iff_of_notMem heI', mem_diff, and_iff_right (hI (.inl rfl))]
  refine fun heclosure ↦ ?_
  simp only [heclosure, insert_eq_of_mem, closure_isFlat, not_true_eq_false, imp_false] at h
  exact h <| (M.closure_subset_closure <| subset_diff_singleton
    (M.subset_closure I hIi.subset_ground) heI') heclosure

lemma ModularCut.extendBy_deleteElem (U : M.ModularCut) (he : e ∉ M.E) :
    (M.extendBy e U) ＼ {e} = M := by
  refine ext_indep (by simpa) fun I hI ↦ ?_
  obtain ⟨-, heI⟩ := show I ⊆ M.E ∧ e ∉ I by simpa [subset_diff] using hI
  simp [extIndep_iff_of_notMem heI, heI]

lemma ModularCut.extendBy_deleteElem' (U : M.ModularCut) : (M.extendBy e U) ＼ {e} = M ＼ {e} := by
  refine ext_indep (by simp) fun I hI ↦ ?_
  obtain ⟨-, heI⟩ := show I ⊆ M.E ∧ e ∉ I by simpa [subset_diff] using hI
  simp [extIndep_iff_of_notMem heI, heI]

lemma ModularCut.isRestriction_extendBy (U : M.ModularCut) (he : e ∉ M.E) :
    M ≤r (M.extendBy e U) := by
  nth_rw 1 [← U.extendBy_deleteElem he]
  apply delete_isRestriction

lemma ModularCut.eq_extendBy_of_forall_flat (𝓕 : (M ＼ {e}).ModularCut) (he : e ∈ M.E)
    (h_flat : ∀ ⦃F⦄, (M ＼ {e}).IsFlat F → (e ∈ M.closure F ↔ F ∈ 𝓕)) :
    (M ＼ {e}).extendBy e 𝓕 = M := by
  have h : 𝓕 = ModularCut.ofDeleteElem M e := by
    ext F hF
    rw [← h_flat hF]
    rw [deleteElem_isFlat_iff] at hF
    obtain hFf | hins := hF.2
    · simp [hFf.closure, hF.1]
    simp [hins, hF.1]
  rwa [h, ModularCut.deleteElem_extendBy]

/-- Different modular cuts give different extensions. -/
lemma extendBy_injective (M : Matroid α) (he : e ∉ M.E) : Injective (M.extendBy e) := by
  refine fun U U' h_eq ↦ SetLike.coe_set_eq.1 (Set.ext fun F ↦ ?_)
  obtain (hF | hF) := em' (M.IsFlat F)
  · exact iff_of_false (hF ∘ U.isFlat_of_mem) (hF ∘ U'.isFlat_of_mem)
  obtain ⟨I, hI⟩ := M.exists_isBasis F
  have heI : e ∉ I := notMem_subset hI.indep.subset_ground he
  apply_fun (fun M ↦ M.Indep (insert e I)) at h_eq
  simpa [extendBy_Indep, ModularCut.extIndep_iff_of_mem (mem_insert e I), heI, hI.indep,
    not_iff_not, ← hF.eq_closure_of_isBasis hI] using h_eq

/-- Single-element extensions are equivalent to modular cuts. -/
def extensionEquivModularCut (M : Matroid α) (he : e ∉ M.E) :
    {N : Matroid α // (e ∈ N.E ∧ N ＼ {e} = M)} ≃ M.ModularCut where
  toFun N := (ModularCut.ofDeleteElem N e).copy N.2.2
  invFun U := ⟨M.extendBy e U, by simp, U.extendBy_deleteElem he⟩
  left_inv := by
    rintro ⟨N, heN, rfl⟩
    simp only [Subtype.mk.injEq]
    exact ModularCut.deleteElem_extendBy heN
  right_inv := by
    apply rightInverse_of_injective_of_leftInverse
    · exact fun U U' hUU' ↦ extendBy_injective M he (by simpa using hUU')
    rintro ⟨N, heN, rfl⟩
    simp only [Subtype.mk.injEq]
    exact ModularCut.deleteElem_extendBy heN

lemma ModularCut.mem_closure_extendBy_iff (U : M.ModularCut) (he : e ∉ M.E) :
    e ∈ (M.extendBy e U).closure X ↔ e ∈ X ∨ M.closure X ∈ U := by
  by_cases heX : e ∈ X
  · simp [heX, mem_closure_of_mem']
  obtain ⟨I, hI⟩ := (M.extendBy e U).exists_isBasis' X
  have hI' : M.IsBasis' I X
  · rwa [← U.extendBy_deleteElem he, delete_isBasis'_iff, diff_singleton_eq_self heX]
  have heI := notMem_subset hI'.subset heX
  rw [← hI.closure_eq_closure, ← hI'.closure_eq_closure, or_iff_right heX,
    ← not_iff_not, hI.indep.notMem_closure_iff_of_notMem heI, extendBy_Indep,
    U.extIndep_iff_of_mem (.inl rfl)]
  simp [heI, hI'.indep]

lemma ModularCut.closure_mem_iff_mem_closure_extendBy (U : M.ModularCut) (he : e ∉ M.E)
    (heX : e ∉ X) : M.closure X ∈ U ↔ e ∈ (M.extendBy e U).closure X := by
  rw [U.mem_closure_extendBy_iff he, or_iff_right heX]

lemma ModularCut.extendBy_closure_eq_self (U : M.ModularCut) (he : e ∉ M.E) (heX : e ∉ X)
    (hXU : M.closure X ∉ U) : (M.extendBy e U).closure X = M.closure X := by
  nth_rewrite 2 [← U.extendBy_deleteElem he]
  rw [delete_closure_eq, diff_singleton_eq_self heX, sdiff_eq_left.2]
  rw [disjoint_singleton_right, mem_closure_extendBy_iff _ he]
  simp [heX, hXU]

lemma ModularCut.extendBy_closure_eq_insert (U : M.ModularCut) (he : e ∉ M.E) (heX : e ∉ X)
    (hXSU : M.closure X ∈ U) : (M.extendBy e U).closure X = insert e (M.closure X) := by
  nth_rewrite 2 [← U.extendBy_deleteElem he]
  rw [delete_closure_eq, insert_diff_singleton]
  rw [diff_singleton_eq_self heX, eq_comm, insert_eq_self, U.mem_closure_extendBy_iff he]
  exact .inr hXSU

lemma ModularCut.extendBy_closure_insert_eq_insert (U : M.ModularCut) (he : e ∉ M.E) (heX : e ∉ X)
    (hXSU : M.closure X ∈ U) : (M.extendBy e U).closure (insert e X) = insert e (M.closure X) := by
  rw [← U.extendBy_closure_eq_insert he heX hXSU, closure_insert_eq_of_mem_closure]
  simp [U.extendBy_closure_eq_insert he heX hXSU]

lemma ModularCut.insert_isFlat_extendBy_of_mem (U : M.ModularCut) (hFU : F ∈ U) (he : e ∉ M.E) :
    (M.extendBy e U).IsFlat (insert e F) := by
  have heF : e ∉ F := notMem_subset (U.isFlat_of_mem hFU).subset_ground he
  have hmem : e ∈ (M.extendBy e U).closure F := by
    rw [U.extendBy_closure_eq_insert he heF (closure_mem_of_mem hFU)]
    apply mem_insert
  rw [isFlat_iff_closure_eq, closure_insert_eq_of_mem_closure hmem,
    U.extendBy_closure_eq_insert he heF (U.closure_mem_of_mem hFU),
    (U.isFlat_of_mem hFU).closure]

lemma ModularCut.isFlat_extendBy_of_isFlat_of_notMem (U : M.ModularCut) (he : e ∉ M.E)
    (hF : M.IsFlat F) (hFU : F ∉ U) : (M.extendBy e U).IsFlat F := by
  have heF := notMem_subset hF.subset_ground he
  rw [isFlat_iff_closure_eq, extendBy_closure_eq_self _ he heF, hF.closure]
  rwa [hF.closure]

lemma ModularCut.insert_isFlat_extendBy_of_not_covBy (U : M.ModularCut) (he : e ∉ M.E)
    (hF : M.IsFlat F) (h_not_covBy : ¬ ∃ F' ∈ U, F ⋖[M] F') :
    (M.extendBy e U).IsFlat (insert e F) := by
  have heF := notMem_subset hF.subset_ground he
  by_cases hFU : F ∈ U
  · obtain rfl | hne := eq_or_ne F M.E
    · simpa using (M.extendBy e U).ground_isFlat
    obtain ⟨F', hF'⟩ := hF.exists_covby_of_ne_ground hne
    exact False.elim <| h_not_covBy ⟨F', U.superset_mem hFU hF'.isFlat_right hF'.subset, hF'⟩
  contrapose! h_not_covBy
  obtain ⟨f, hfmem⟩ := exists_mem_closure_notMem_of_not_isFlat h_not_covBy
    (insert_subset_insert hF.subset_ground)
  simp only [mem_diff, mem_insert_iff, not_or] at hfmem
  refine ⟨M.closure (insert f F), ?_, ?_⟩
  · rw [U.closure_mem_iff_mem_closure_extendBy he (by simp [Ne.symm hfmem.2.1, heF])]
    refine mem_closure_insert (fun h ↦ hfmem.2.2 ?_) hfmem.1
    rwa [extendBy_closure_eq_self _ he heF, hF.closure] at h
    rwa [hF.closure]
  refine IsFlat.covBy_closure_insert hF hfmem.2.2 ?_
  simpa [hfmem.2.1] using mem_ground_of_mem_closure hfmem.1

/-- An extension of a finite-rank matroid is finite. -/
instance (U : M.ModularCut) (e : α) [M.RankFinite] : (M.extendBy e U).RankFinite := by
  refine RankFinite.ofDelete (D := {e}) isRkFinite_singleton ?_
  rw [ModularCut.extendBy_deleteElem']
  exact delete_rankFinite

lemma extendBy_isColoop_iff (U : M.ModularCut) (he : e ∉ M.E) :
    (M.extendBy e U).IsColoop e ↔ U = ⊥ := by
  simp_rw [isColoop_iff_forall_mem_closure_iff_mem, ModularCut.mem_closure_extendBy_iff _ he,
    or_iff_left_iff_imp, ModularCut.eq_bot_iff]
  rw [← M.closure_ground]
  refine ⟨fun h hEU ↦ he (h _ hEU), fun h X hX ↦ False.elim <| h ?_⟩
  exact U.superset_mem hX (M.closure_isFlat _) <| by simp [closure_subset_ground]

lemma extendBy_eRank_eq (U : M.ModularCut) (hU : U ≠ ⊥) (he : e ∉ M.E) :
    (M.extendBy e U).eRank = M.eRank := by
  nth_rw 2 [← U.extendBy_deleteElem he]
  rw [deleteElem_eRank_eq]
  rwa [extendBy_isColoop_iff _ he]

end extensions


end Matroid
