import Matroid.Rank.Skew
import Matroid.Order.Quotient
import Matroid.Order.Discrepancy
import Matroid.Extension.Minor
import Matroid.ForMathlib.Data.Set.Finite

open Set BigOperators Set.Notation Function

namespace Matroid

variable {α : Type*} {ι : Type*} {η : Type*} {A : Set η} {M N : Matroid α}
    {B I J X X' Y Y' F : Set α} {e : α} {i j : ι} {Xs Ys Is Js : ι → Set α}

/-- If `N` is a finitary quotient of `M`, then the collection of all flats `F` of `M`
for which `M.project F = N.project F` is a modular cut. -/
@[simps!]
def Quotient.modularCut [N.Finitary] (h : N ≤q M) : M.ModularCut :=
  ModularCut.ofForallIsModularPairChainInter
  (M := M)
  (U := {F | M.IsFlat F ∧ M.project F = N.project F})
  (h_isFlat := by simp +contextual)
  (h_superset := by
    refine fun F F' ⟨hF, hFe⟩ hF' hss ↦ ⟨hF', ?_⟩
    rw [← union_eq_self_of_subset_left hss, ← project_project, hFe, project_project])
  (h_pair := by
    refine fun F F' ⟨hF, hFe⟩ ⟨hF', hF'e⟩ hmod ↦ ⟨hF.inter hF', ?_⟩
    obtain ⟨B, hB, hBu, hBF, hBF', hBi⟩ := hmod.exists_isMutualBasis_isBase
    have hBi := hB.indep
    have h1 : (M.project F).Indep (B \ F) := by rwa [project_indep_iff,
      hBF.contract_indep_iff_of_disjoint disjoint_sdiff_right, inter_comm, diff_union_inter]
    have h1' : (M.project F').Indep (B \ F') := by rwa [project_indep_iff,
      hBF'.contract_indep_iff_of_disjoint disjoint_sdiff_right, inter_comm, diff_union_inter]
    set I := B ∩ (F' \ F) with hI_def
    rw [hF'e] at h1'
    have hI : (N.project (F ∩ F')).Indep I := by
      rw [hFe] at h1
      exact (h1.of_project_subset inter_subset_left).subset <| by tauto_set
    have h2 : ((N.project (F ∩ F')).project I).Indep (B \ F') := by
      rw [project_project]
      exact h1'.of_project_subset <| by (rw [hI_def]; tauto_set)
    rw [project_indep_iff, hI.contract_indep_iff, hI_def] at h2
    have hq := h.project_quotient_project (F ∩ F')
    refine Eq.symm <| hq.eq_of_closure_indep ?_ h2.2
    grw [project_closure,
      ← M.closure_subset_closure (show B ⊆ _ by tauto_set), hB.closure_eq, project_ground])
  (h_chain := by
    refine fun Fs hFs hCne hmod hchain ↦ ⟨?_, ?_⟩
    · exact IsFlat.sInter hCne.nonempty fun F hF ↦ (hFs hF).1
    simp only [subset_def, mem_setOf_eq] at hFs
    obtain ⟨B, hB, hBmut⟩ := hmod.exists_isMutualBasis_isBase
    simp only [isMutualBasis_iff, Subtype.forall] at hBmut
    refine Eq.symm <| (h.project_quotient_project _).eq_of_closure_indep (X := B \ ⋂₀ Fs) ?_ ?_
    · simp [hB.spanning.closure_eq_of_superset subset_union_left]
    rw [indep_iff_forall_subset_not_isCircuit', project_ground, h.ground_eq,
      and_iff_left (diff_subset.trans hB.subset_ground)]
    intro C hCss hC
    have aux (e) (he : e ∈ C) : ∃ F ∈ Fs, e ∉ F := by simpa using (hCss he).2
    choose! F' hF' using aux
    replace hchain : IsChain (fun a b ↦ b ≤ a) Fs := hchain.symm
    have hss' : F' '' C ⊆ Fs := by
      rw [image_subset_iff, subset_def]
      exact fun e heC ↦ (hF' e heC).1
    obtain ⟨F₀, hF₀, hF₀le : ∀ F ∈ F' '' C, F₀ ⊆ F⟩ :=
      hchain.directedOn.exists_forall_le hCne.nonempty hss' (hC.finite.image F')
    have hCi : (N.project F₀).Indep C := by
      rw [← (hFs _ hF₀).2, (hBmut.2 F₀ hF₀).project_eq_project, project_indep_iff,
        (hBmut.1.inter_left F₀).contract_indep_iff, inter_comm, disjoint_left]
      refine ⟨?_, hBmut.1.subset (union_subset (hCss.trans diff_subset) inter_subset_left)⟩
      rintro e heC ⟨heB, heF₀⟩
      exact (hF' e heC).2 <| hF₀le (F' e) (mem_image_of_mem _ heC) heF₀
    refine hC.not_indep (hCi.of_project_subset (sInter_subset_of_mem hF₀)))

lemma Quotient.mem_modularCut_iff [N.Finitary] (h : N ≤q M) {F : Set α} :
    F ∈ h.modularCut ↔ M.IsFlat F ∧ M.project F = N.project F := Iff.rfl

@[simp]
lemma Quotient.closure_mem_modularCut_iff [N.Finitary] (h : N ≤q M) :
    M.closure I ∈ h.modularCut ↔ M.project I = N.project I := by
  rw [h.mem_modularCut_iff, and_iff_right (M.closure_isFlat _), ← N.project_closure_eq,
    h.closure_closure_eq_closure_right, N.project_closure_eq, M.project_closure_eq]

@[simp]
lemma Quotient.modularCut_eq_top_iff [N.Finitary] (h : N ≤q M) :
    h.modularCut = ⊤ ↔ N = M := by
  simp only [ModularCut.eq_top_iff, ← closure_empty, mem_modularCut_iff, isFlat_closure,
    project_closure_eq, project_empty, true_and]
  rw [project_eq_self (h.closure_subset_closure _), eq_comm]

@[simp]
lemma Quotient.modularCut_ne_bot [N.Finitary] (h : N ≤q M) : h.modularCut ≠ ⊥ := by
  intro hbot
  have hcut := h.mem_modularCut_iff (F := M.E)
  rw [hbot, project_ground_self, and_iff_right (ground_isFlat _), ← h.ground_eq] at hcut
  simp at hcut

lemma Quotient.projectBy_modularCut_indep_iff [N.Finitary] (h : N ≤q M) (hne : N ≠ M) :
    (M.projectBy h.modularCut).Indep I ↔ M.Indep I ∧ ¬ N.project I = M.project I := by
  simp only [projectBy_indep_iff, ne_eq, modularCut_eq_top_iff, hne, not_false_eq_true,
    mem_modularCut_iff, isFlat_closure, project_closure_eq, true_and, forall_const,
    and_congr_right_iff]
  rw [← N.project_closure_eq, h.closure_closure_eq_closure_right, N.project_closure_eq, eq_comm]
  exact fun _ ↦ Iff.rfl

/-- If `U` is the modular cut arising from the quotient relation `N ≤q M`,
then `N` is also a quotient of `M.projectBy U`. -/
lemma Quotient.quotient_projectBy_modularCut [N.Finitary] (h : N ≤q M) :
    N ≤q (M.projectBy h.modularCut) := by
  set U := h.modularCut with hU
  obtain h_eq | hne := eq_or_ne h.modularCut ⊤
  · rwa [hU, h_eq, projectBy_top]
  rw [Ne, h.modularCut_eq_top_iff] at hne
  refine quotient_of_forall_closure_subset_closure_indep h.ground_eq.symm fun I hI e heU ↦ ?_
  have heE : e ∈ M.E := (M.projectBy U).mem_ground_of_mem_closure heU
  rw [mem_closure_projectBy_iff, hU, h.closure_mem_modularCut_iff, h.closure_mem_modularCut_iff]
    at heU
  obtain heI | ⟨h_eq, h_ne⟩ := heU
  · exact h.closure_subset_closure _ heI
  replace hI := (projectBy_quotient U).weakLE.indep_of_indep hI
  have heI : M.Indep (insert e I) := by
    rw [hI.insert_indep_iff]
    refine .inl ⟨heE, fun hcl ↦ h_ne ?_⟩
    rwa [← project_closure_eq, closure_insert_eq_of_mem_closure hcl, project_closure_eq,
      ← N.project_closure_eq, closure_insert_eq_of_mem_closure (h.closure_subset_closure _ hcl),
      project_closure_eq] at h_eq
  contrapose! h_ne
  obtain ⟨B, hB⟩ := (M.project (insert e I)).exists_isBase
  have hBi := hB.indep
  rw [h_eq, ← union_singleton, ← project_project, project_indep_iff, Indep.contract_indep_iff,
    union_singleton] at hBi
  · rw [(h.project_quotient_project I).eq_of_spanning_indep ?_ hBi.2]
    rw [project_spanning_iff, insert_union, union_comm, ← insert_union, union_comm]
    exact (project_spanning_iff ..).1 hB.spanning
  rw [project_indep_iff, indep_singleton, contract_isNonloop_iff, h.ground_eq]
  exact ⟨heE, h_ne⟩

/-- If `X` is a finite set of elements outside the ground set whose size is equal to the
discrepancy of a quotient `N ≤q M`, then there is a matroid `P` on `M.E ∪ X`
for which `P ＼ X = M` and `P ／ X = N`.   -/
lemma Quotient.exists_eq_contract_eq_delete_of_discrepancy_finite' (hQ : N ≤q M) [Finitary N]
    (hX : Disjoint X M.E) (hfin : X.Finite) (h_discr : hQ.discrepancy M.E ≤ X.encard) :
    ∃ (P : Matroid α), X ⊆ P.E ∧ P ／ X = N ∧ P ＼ X = M := by
  induction X, hfin using Set.Finite.induction_on generalizing M with
  | empty => simpa using h_discr
  | @insert a X haX hfin IH =>
  · obtain rfl | hne := eq_or_ne M N
    · refine ⟨M ↾ (M.E ∪ insert a X), subset_union_right, ?_⟩
      rw [contract_eq_delete_of_subset_loops, delete_eq_restrict, and_self,
        restrict_ground_eq, union_diff_cancel_right hX.symm.inter_eq.le,
        restrict_restrict_eq _ subset_union_left, restrict_ground_eq_self]
      grw [restrict_loops_eq', ← subset_union_right, union_diff_cancel_left hX.symm.inter_eq.le]
    have htop : hQ.modularCut ≠ ⊤ := by simpa using hne.symm
    obtain ⟨haE : a ∉ M.E, hdj : Disjoint X M.E⟩ := by simpa using hX
    set M' := M.projectBy hQ.modularCut with hM'
    have hQ' : N ≤q M' := hQ.quotient_projectBy_modularCut
    have hd : hQ'.discrepancy M'.E ≤ X.encard := by
      obtain ⟨I, J, hI, hJ, hIJ⟩ := hQ'.weakLE.exists_isBase_subset_isBase
      rw [← hQ'.encard_isBase_diff_eq_discrepancy_ground hI hJ hIJ]
      obtain ⟨K, hJK, hK⟩ : ∃ K, J ⊂ K ∧ M.IsBase K := by
        obtain ⟨hJM : M.Indep J, hJcl : M.closure J ∉ hQ.modularCut⟩ :=
          (projectBy_indep_iff_of_ne_top htop).1 <| hM' ▸ hJ.indep
        obtain ⟨K, hK, hJK⟩ := hJM.exists_isBase_superset
        refine ⟨K, hJK.ssubset_of_ne ?_, hK⟩
        rintro rfl
        obtain h1 | h2 := hQ.modularCut.eq_bot_or_ground_mem
        · exact hQ.modularCut_ne_bot h1
        rw [hK.closure_eq] at hJcl
        contradiction
      rw [← hQ.encard_isBase_diff_eq_discrepancy_ground hI hK (hIJ.trans hJK.subset),
        encard_insert_of_notMem haX] at h_discr
      obtain ⟨x, hxK, hxJ⟩ := exists_of_ssubset hJK
      grw [← WithTop.add_le_add_iff_right (z := 1) (by simp), ← h_discr,
        ← encard_insert_of_notMem (show x ∉ J \ I from notMem_subset diff_subset hxJ)]
      exact encard_le_encard
        (insert_subset ⟨hxK, notMem_subset hIJ hxJ⟩ (diff_subset_diff_left hJK.subset))
    obtain ⟨Q, hQE, rfl, hQdel⟩ := IH hQ' (by simpa) hd
    rw [hM', ← ModularCut.extendBy_contractElem _ haE] at hQdel
    obtain ⟨P, himp, rfl, hPM⟩ := exists_common_major_of_delete_eq_contractElem haX hQE hQdel
    refine ⟨P, insert_subset (himp (by simp)) (hQE.trans diff_subset), by simp, ?_⟩
    rw [← union_singleton, ← delete_delete, hPM, ModularCut.extendBy_deleteElem _ haE]

/-- If `N` is a finitary quotient of `M`, and the number of nonelements of the ground
set available is more than the discrepancy of the quotient, then `N` is a projection of `M`
within `Matroid α`.  -/
lemma Quotient.exists_eq_contract_eq_delete_of_discrepancy_lt_encard_compl [Finitary N]
    (hQ : N ≤q M) (hE : hQ.discrepancy M.E < M.Eᶜ.encard) :
    ∃ (P : Matroid α) (X : Set α), X ⊆ P.E ∧ P ／ X = N ∧ P ＼ X = M := by
  obtain ⟨X, hX, hXcard⟩ := exists_subset_encard_eq hE.le
  grw [le_top (a := M.Eᶜ.encard), ← hXcard, encard_lt_top_iff] at hE
  obtain ⟨P, hXP, hPN, hPM⟩ :=
    hQ.exists_eq_contract_eq_delete_of_discrepancy_finite'  (disjoint_left.2 hX) hE hXcard.symm.le
  exact ⟨P, X, hXP, hPN, hPM⟩

/-- The same as the previous statement, but with the assumption that `M` is cofinitary. -/
lemma Quotient.exists_eq_contract_eq_delete_of_discrepancy_lt_encard_compl' [Finitary M✶]
    (hQ : N ≤q M) (hE : hQ.discrepancy M.E < M.Eᶜ.encard) :
    ∃ (P : Matroid α) (X : Set α), X ⊆ P.E ∧ P ／ X = N ∧ P ＼ X = M := by
  obtain ⟨P, X, hXE, hPM, hPN⟩ :=
    hQ.dual.exists_eq_contract_eq_delete_of_discrepancy_lt_encard_compl
    (by rwa [hQ.discrepancy_ground_dual, dual_ground, hQ.ground_eq])
  exact ⟨P✶, X, hXE, by rw [← dual_inj, ← hPN, dual_contract_dual],
    by rw [← dual_inj, ← hPM, dual_delete_dual]⟩
