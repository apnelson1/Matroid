import Matroid.ForMathlib.Order.Minimal
import Matroid.ForMathlib.MatroidBasic
import Matroid.Modular
import Matroid.Flat

open Set Function Set.Notation




variable {α : Type*} {M : Matroid α} {I J B F F' X Y : Set α} {e f : α}



namespace Matroid

@[ext] structure ModularCut (M : Matroid α) where
  (carrier : Set (Set α))
  (forall_flat : ∀ F ∈ carrier, M.Flat F)
  (forall_superset : ∀ F F', F ∈ carrier → M.Flat F' → F ⊆ F' → F' ∈ carrier)
  (forall_inter : ∀ xs ⊆ carrier, xs.Nonempty → M.ModularFamily (fun x : xs ↦ x) → ⋂₀ xs ∈ carrier)

instance (M : Matroid α) : SetLike (ModularCut M) (Set α) where
  coe := ModularCut.carrier
  coe_injective' U U' := by cases U; cases U'; simp

@[simp] lemma ModularCut.mem_mk_iff (S : Set (Set α)) (h₁ : ∀ F ∈ S, M.Flat F)
  (h₂ : ∀ F F', F ∈ S → M.Flat F' → F ⊆ F' → F' ∈ S)
  (h₃ : ∀ xs ⊆ S, xs.Nonempty → M.ModularFamily (fun x : xs ↦ x) → ⋂₀ xs ∈ S) {X : Set α} :
  X ∈ ModularCut.mk S h₁ h₂ h₃ ↔ X ∈ S := Iff.rfl

lemma ModularCut.flat_of_mem (U : M.ModularCut) (hF : F ∈ U) : M.Flat F :=
    U.forall_flat F hF

lemma ModularCut.superset_mem (U : M.ModularCut) (hF : F ∈ U) (hF' : M.Flat F') (hFF' : F ⊆ F') :
    F' ∈ U :=
  U.forall_superset F F' hF hF' hFF'

lemma ModularCut.cl_superset_mem (U : M.ModularCut) (hF : F ∈ U) (hFX : F ⊆ M.cl X) : M.cl X ∈ U :=
  U.superset_mem hF (M.cl_flat _) hFX

lemma ModularCut.cl_superset_mem' (U : M.ModularCut) (hX : M.cl X ∈ U) (hXY : X ⊆ Y) : M.cl Y ∈ U :=
  U.cl_superset_mem hX (M.cl_subset_cl hXY)

lemma ModularCut.sInter_mem (U : M.ModularCut) {Fs : Set (Set α)} (hne : Fs.Nonempty) (hFs : Fs ⊆ U)
    (hFs_mod : M.ModularFamily (fun F : Fs ↦ F)) : ⋂₀ Fs ∈ U :=
  U.forall_inter Fs hFs hne hFs_mod

lemma ModularCut.iInter_mem (U : M.ModularCut) {ι : Type*} [Nonempty ι] (Fs : ι → Set α)
    (hFs : ∀ i, Fs i ∈ U) (hFs_mod : M.ModularFamily Fs) : ⋂ i, Fs i ∈ U := by
  have hwin := U.sInter_mem (Fs := range Fs) (range_nonempty Fs) ?_ ?_
  · simpa using hwin
  · rintro _ ⟨i, hi, rfl⟩; exact hFs i
  obtain ⟨B, hB, hB'⟩ := hFs_mod
  exact ⟨B, hB, by simpa⟩

lemma ModularCut.inter_mem (U : M.ModularCut) (hF : F ∈ U) (hF' : F' ∈ U) (h : M.ModularPair F F') :
    F ∩ F' ∈ U := by
  rw [inter_eq_iInter]
  apply U.iInter_mem
  · simp [hF, hF']
  exact h

def ModularCut.empty (M : Matroid α) : M.ModularCut where
  carrier := ∅
  forall_flat := by simp
  forall_superset := by simp
  forall_inter := by simp [subset_empty_iff]

lemma ModularCut.eq_empty_or_top_mem (U : M.ModularCut) : U = ModularCut.empty M ∨ M.E ∈ U := by
  obtain (hU | ⟨F, hF⟩) := (U : Set (Set α)).eq_empty_or_nonempty
  · left
    ext x
    change x ∈ (U : Set (Set α)) ↔ x ∈ ∅
    simp [hU]
  exact .inr <| U.superset_mem hF M.ground_flat (U.flat_of_mem hF).subset_ground

lemma ModularCut.covby_of_maximal (U : M.ModularCut) (hF : F ∈ U) {F₀ : Set α} (hF₀ : M.Flat F₀)
    (hF₀U : F₀ ∉ U) (hmax : ∀ x ∈ F \ F₀, M.cl (insert x F₀) ∈ U) : F₀ ⋖[M] F := by
  sorry

lemma ModularCut.covby_of_maximal_cl (U : M.ModularCut) {X Y : Set α} (h : M.cl Y ∈ U)
    (hF₀U : M.cl X ∉ U) (hmax : ∀ x ∈ Y \ M.cl X, M.cl (insert x X) ∈ U) : M.cl X ⋖[M] M.cl Y := by
  sorry


def ModularCut.ExtIndep (U : M.ModularCut) (e : α) (I : Set α) : Prop :=
  (M.Indep I ∨ (M.Indep (I \ {e}) ∧ M.cl (I \ {e}) ∉ U))

theorem ModularCut.ExtIndep.or {U : M.ModularCut} (hI : U.ExtIndep e I) (he : e ∉ M.E) :
    (M.Indep I ∧ e ∉ I) ∨ (M.Indep (I \ {e}) ∧ M.cl (I \ {e}) ∉ U ∧ e ∈ I) := by
  obtain (h | h) := hI
  · exact .inl ⟨h, not_mem_subset h.subset_ground he⟩
  obtain (heI | heI) := em (e ∈ I)
  · exact .inr ⟨h.1, h.2, heI⟩
  rw [diff_singleton_eq_self heI] at h
  exact .inl ⟨h.1, heI⟩

lemma ModularCut.extIndep_def {U : M.ModularCut} (he : e ∉ M.E) :
    U.ExtIndep e I ↔ (M.Indep I ∧ e ∉ I) ∨ (M.Indep (I \ {e}) ∧ M.cl (I \ {e}) ∉ U ∧ e ∈ I) := by
  refine ⟨fun h ↦ h.or he, ?_⟩
  rintro (h | h)
  · exact .inl h.1
  exact .inr ⟨h.1, h.2.1⟩

lemma ModularCut.extIndep_iff_of_not_mem {U : M.ModularCut} (he : e ∉ M.E) (heI : e ∉ I) :
    U.ExtIndep e I ↔ M.Indep I :=
  ⟨fun h ↦ (h.or he).elim (fun h ↦ h.1) (by tauto), Or.inl⟩

lemma ModularCut.extIndep_iff_of_mem {U : M.ModularCut} (he : e ∉ M.E) (heI : e ∈ I) :
    U.ExtIndep e I ↔ M.Indep (I \ {e}) ∧ M.cl (I \ {e}) ∉ U := by
  simp [extIndep_def he, heI]

lemma ModularCut.ExtIndep.subset {U : M.ModularCut} (h : U.ExtIndep e I) (hJI : J ⊆ I) :
    U.ExtIndep e J := by
  obtain (h | h) := h
  · exact .inl <| h.subset hJI
  exact .inr ⟨h.1.subset (diff_subset_diff_left hJI),
    fun hJe ↦ h.2 <| U.cl_superset_mem' hJe (diff_subset_diff_left hJI) ⟩

lemma ModularCut.ExtIndep.subset_insert_ground {U : M.ModularCut} (h : U.ExtIndep e I) :
    I ⊆ insert e M.E := by
  obtain (h | h) := h
  · exact h.subset_ground.trans (subset_insert _ _)
  simpa using h.1.subset_ground

lemma ModularCut.extIndep_insert_iff {U : M.ModularCut} (he : e ∉ M.E) (heI : e ∉ I) :
    U.ExtIndep e (insert e I) ↔ M.Indep I ∧ M.cl I ∉ U := by
  simp [extIndep_def he, show e ∈ insert e I from .inl rfl, diff_singleton_eq_self heI]

lemma ModularCut.extIndep_insert_iff' {U : M.ModularCut} (he : e ∉ M.E) :
    U.ExtIndep e (insert e I) ↔ M.Indep (I \ {e}) ∧ M.cl I ∉ U := by
  have hrw : M.cl I = M.cl (I \ {e}) := by
    rw [eq_comm, ← cl_inter_ground, diff_eq, inter_right_comm, inter_assoc, ← diff_eq,
      diff_singleton_eq_self he, cl_inter_ground]
  simp [extIndep_def he, ← hrw]

lemma ModularCut.ExtIndep.diff_singleton_indep {U : M.ModularCut} (h : U.ExtIndep e I) :
    M.Indep (I \ {e}) := by
  obtain (h | h) := h; exact h.diff _; exact h.1

lemma ModularCut.extIndep_iff {U : M.ModularCut} (he : e ∉ M.E) :
    U.ExtIndep e I ↔ (M.Indep I ∧ e ∉ I) ∨ (M.Indep (I \ {e}) ∧ M.cl (I \ {e}) ∉ U ∧ e ∈ I) := by
  refine ⟨fun h ↦ h.or he, ?_⟩
  rintro (h | h)
  · exact .inl h.1
  exact .inr ⟨h.1, h.2.1⟩


lemma ModularCut.foo2 {U : M.ModularCut} (he : e ∉ M.E) (hX : X ⊆ insert e M.E)
    (hI : U.ExtIndep e I) (hiX : I ⊆ X) :
    I ∈ maximals (· ⊆ ·) {J | U.ExtIndep e J ∧ J ⊆ X} ↔

      ( (e ∉ I ∧ e ∉ X ∧ M.cl (I \ {e}) = M.cl (X \ {e}))) ∨
        (e ∉ I ∧ e ∈ X ∧ M.cl (I \ {e}) = M.cl (X \ {e}) ∧ M.cl (X \ {e}) ∈ U) ∨
        (e ∈ I ∧ M.cl (I \ {e}) = M.cl (X \ {e}) ∧ M.cl (X \ {e}) ∉ U) ∨
        (e ∈ I ∧ (M.cl (I \ {e}) ⋖[M] M.cl (X \ {e})) ∧ M.cl (X \ {e}) ∈ U) := by
  sorry





lemma ModularCut.foo3 {U : M.ModularCut} (he : e ∉ M.E) (hX : X ⊆ insert e M.E)
    (hI : U.ExtIndep e I) (hIX : I ⊆ X) :
    I ∈ maximals (· ⊆ ·) {J | U.ExtIndep e J ∧ J ⊆ X} ↔
        (M.cl (I \ {e}) = M.cl (X \ {e}) ∧ ((e ∈ I ↔ M.cl (X \ {e}) ∈ U) → e ∉ I ∧ e ∉ X))
      ∨ ((M.cl (I \ {e}) ⋖[M] M.cl (X \ {e})) ∧ e ∈ I ∧ M.cl (X \ {e}) ∈ U) := by

  have hss : I \ {e} ⊆ X \ {e} := diff_subset_diff_left hIX
  have hX' : X \ {e} ⊆ M.E := by simpa

  have hrw : ∀ x, M.Indep (insert x I \ {e}) ↔ (x ≠ e → M.Indep (insert x (I \ {e}))) := by
    intro x
    obtain (rfl | hne) := eq_or_ne x e
    · simp [hI.diff_singleton_indep]
    simp [hne, insert_diff_singleton_comm]

  have hrw' : ∀ x, M.Indep (insert x I) ↔ (x ≠ e ∧ e ∉ I ∧ M.Indep (insert x (I \ {e}))) := by
    intro x
    obtain (rfl | hne) := eq_or_ne x e
    · simp
      sorry
    obtain (heI | heI) := em (e ∈ I)
    · simp [heI, hne]
      sorry
    simp [heI, hne]
    -- simp [hne]
  simp_rw [hI.diff_singleton_indep.insert_indep_iff] at hrw hrw'


  simp only [extIndep_def he, mem_maximals_iff_forall_insert sorry, hI.diff_singleton_indep,
    true_and, hIX, and_true, hrw', ne_eq, mem_diff, mem_singleton_iff, mem_insert_iff, not_or,
    ne_comm (a := e), hrw, insert_subset_iff, not_and]


  obtain (heI | heI) := em (e ∈ I)
  · have heX : e ∈ X := hIX heI
    rw [extIndep_iff_of_mem he heI] at hI
    simp only [heI, not_true_eq_false, and_false, hI.1, hI.2, not_false_eq_true, and_self, or_true,
      and_true, false_or, and_imp, true_and, true_iff, hIX heI, imp_false,
      hI.1.insert_diff_indep_iff heI]
    obtain (hXU | hXU) := em (M.cl (X \ {e}) ∈ U)
    · simp only [hXU, not_true_eq_false, and_false, and_true, false_or, not_imp_not]
      refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
      · apply U.covby_of_maximal_cl hXU hI.2
        simp only [mem_diff, mem_singleton_iff, and_imp, not_imp_not]
        intro x hx hxe hxcl
        have hxI : x ∉ I := sorry
        have hxE : x ∈ M.E := sorry
        simpa [hxI, hxe, hx, hxcl, hxE, insert_diff_singleton_comm hxe] using h x
      intro x hxI h' hx
      have hne : x ≠ e := by rintro rfl; contradiction
      simp [hne, hxI] at h'
      rwa [← h.cl_insert_eq (e := x) ⟨sorry, h'.2⟩, cl_insert_cl_eq_cl_insert,
        insert_diff_singleton_comm hne] at hXU

    simp only [hXU, not_false_eq_true, and_true, and_false, or_false]
    refine ⟨fun h ↦ (M.cl_subset_cl hss).antisymm
      (M.cl_subset_cl_of_subset_cl fun x ⟨hxX, (hne : x ≠ e)⟩ ↦ by_contra fun hcl ↦ ?_), fun h ↦ ?_⟩
    · have hxE : x ∈ M.E := Or.elim (hX hxX) (False.elim ∘ hne) id
      have hxI : x ∉ I := fun hxI ↦ hcl <| M.subset_cl (I \ {e}) hI.1.subset_ground ⟨hxI, hne⟩
      have hcl' : M.cl (insert x I \ {e}) ∈ U := by simpa [hne, hxX, hxE, hcl, hxI] using h x
      exact hXU <| U.cl_superset_mem' hcl' (diff_subset_diff_left (insert_subset hxX hIX))
    intro x hxI
    have hne : x ≠ e := by rintro rfl; contradiction
    simp only [hne, not_false_eq_true, hxI, and_true, or_false, true_implies, not_imp_not, and_imp]
    intro hxE hxcl hxX
    have := h.symm.subset (M.subset_cl (X \ {e}) (by simpa) ⟨hxX, hne⟩); contradiction

  rw [extIndep_iff_of_not_mem he heI] at hI
  simp only [hI, heI, not_false_eq_true, and_self, diff_singleton_eq_self, and_false, or_false,
    true_and, and_true, false_iff, not_imp_not, false_and]
  refine ⟨fun h ↦ ⟨?_, fun heX ↦ ?_⟩, fun h x hxI ↦ ?_⟩
  · refine (M.cl_subset_cl (subset_diff_singleton hIX heI)).antisymm
      (M.cl_subset_cl_of_subset_cl (fun x ⟨hxX, (hne : x ≠ e)⟩ ↦ by_contra fun hcl ↦ ?_))
    have hxE : x ∈ M.E := Or.elim (hX hxX) (False.elim ∘ hne) id
    suffices hxI : x ∈ I from  hcl <| (M.subset_cl I) hxI
    simpa [hcl, hne, hxX, hne.symm, hxE] using h x

  · have hIU : M.cl I ∈ U := by simpa [heI, heX] using h e
    exact U.cl_superset_mem' hIU (subset_diff_singleton hIX heI)
  obtain (rfl | hne) := eq_or_ne x e
  · simpa [heI, not_imp_not, h.1] using h.2
  simp only [hne, not_false_eq_true, h.1, hxI, and_true, or_false, true_and, true_implies]
  rintro (⟨hxE, hxcl⟩ | ⟨⟨hxE, hxcl⟩, -⟩) hxX <;>
  exact hxcl <| M.subset_cl (X \ {e}) (by simpa) (show x ∈ X \ {e} from ⟨hxX, hne⟩)


def ModularCut.extendIndepMatroid (U : ModularCut M) (he : e ∉ M.E) : IndepMatroid α where

  E := insert e M.E
  Indep := U.ExtIndep e
  indep_empty := Or.inl M.empty_indep
  indep_subset _ _ := ModularCut.ExtIndep.subset
  indep_aug := by

    intro I B hI hInmax hBmax
    by_contra! hcon

    have hB : U.ExtIndep e B := hBmax.1
    have hIeE := hI.diff_singleton_indep.subset_ground
    have hBeE := hB.diff_singleton_indep.subset_ground
    have hss : B \ {e} ⊆ (I ∪ B) \ {e} :=
      diff_subset_diff_left <| subset_union_right I B

    have hIBe : I ∪ B ⊆ insert e M.E :=
      union_subset hI.subset_insert_ground hB.subset_insert_ground

    have hImax : I ∈ maximals (· ⊆ ·) {J | U.ExtIndep e J ∧ J ⊆ I ∪ B} := by
      rw [mem_maximals_iff_forall_insert (fun _ _ ht hst ↦ ⟨ht.1.subset hst, hst.trans ht.2⟩),
        and_iff_right hI, and_iff_right (subset_union_left _ _)]
      intro x hxI h'
      rw [insert_subset_iff, mem_union, or_iff_right hxI] at h'
      exact hcon x ⟨h'.2.1, hxI⟩ h'.1

    have hrw : {J | U.ExtIndep e J} = {J | U.ExtIndep e J ∧ J ⊆ insert e M.E} := by
      simp only [ext_iff, mem_setOf_eq, iff_self_and]
      exact  fun _ ↦ ExtIndep.subset_insert_ground

    rw [hrw, U.foo3 he Subset.rfl hI hI.subset_insert_ground] at hInmax
    rw [hrw, U.foo3 he Subset.rfl hB hB.subset_insert_ground] at hBmax
    rw [U.foo3 he hIBe hI (subset_union_left _ _)] at hImax


    obtain (rfl | hU) := U.eq_empty_or_top_mem
    · replace hBmax := show M.Spanning (B \ {e}) ∧ e ∈ B by
        simpa [empty, ← spanning_iff_cl (S := B \ {e}), he] using hBmax
      replace hInmax := show M.Spanning (I \ {e}) → e ∉ I by
        simpa [empty, ← spanning_iff_cl (S := I \ {e}), he] using hInmax
      replace hImax := show M.Spanning (I \ {e}) ∧ e ∈ I by
        simpa [empty, hBmax.2, he, hBmax.1.cl_superset_eq hss, ← spanning_iff_cl (S := I \ {e})]
        using hImax
      exact hInmax hImax.1 hImax.2

    simp only [mem_singleton_iff, insert_diff_of_mem, he, not_false_eq_true, diff_singleton_eq_self,
      cl_ground, hU, iff_true, mem_insert_iff, or_false, not_true_eq_false, and_false, imp_false,
      and_true, not_or, not_and, not_not, mem_union, and_self_left,
      ← spanning_iff_cl hBeE, ← spanning_iff_cl hIeE, ← hyperplane_iff_covby] at hBmax hInmax

    obtain (hsp | hsp) := em <| M.Spanning ((I ∪ B) \ {e})
    · obtain (heI | heI) := em (e ∈ I)
      · replace hImax := show M.Hyperplane (M.cl (I \ {e})) by
          simpa [hsp.cl_eq, heI, hU, ← hyperplane_iff_covby] using hImax
        exact hInmax.2 hImax heI
      replace hInmax := show ¬ M.Spanning (I \ {e}) by simpa [heI, hU] using hInmax
      replace hImax := show M.cl (I \ {e}) = M.E by simpa [hsp.cl_eq, heI, he, hU] using hImax
      rw [spanning_iff_cl] at hInmax; contradiction

    obtain (⟨hBsp, heB⟩ | ⟨hBhp, heB⟩) := hBmax
    · exact hsp <| hBsp.superset hss

    have hclcl : M.cl (B \ {e}) = M.cl ((I ∪ B) \ {e}) := by
      refine by_contra fun hne ↦ hsp <| ?_
      rw [← cl_spanning_iff]
      have hssu := (M.cl_subset_cl hss).ssubset_of_ne hne
      exact hBhp.spanning_of_ssuperset hssu

    rw [extIndep_iff_of_mem he heB] at hB
    replace hImax := show M.cl (I \ {e}) = M.cl (B \ {e}) ∧ e ∈ I by
      simpa [heB, ← hclcl, hB.2] using hImax

    replace hInmax := show ¬M.Hyperplane (M.cl (I \ {e})) by simpa [hImax.2] using hInmax
    exact hInmax <| (hImax.1.symm ▸ hBhp)

  indep_maximal := by
    intro X hXE I hI hIX
    sorry
  subset_ground := sorry
