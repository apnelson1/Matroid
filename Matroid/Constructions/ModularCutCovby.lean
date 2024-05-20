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


def ModularCut.Base (U : M.ModularCut) (e : α) (B : Set α) :=
  M.Base B ∨ (e ∈ B ∧ ∀ F ∈ U, ∃ f ∈ F, M.Base (insert f (B \ {e})))

def ModularCut.Indep (U : M.ModularCut) (e : α) (I : Set α) :=
  M.Indep I ∨ (e ∈ I ∧ M.Indep (I \ {e}) ∧ M.cl (I \ {e}) ∉ U)

def ModularCut.ConIndep (U : M.ModularCut) (I : Set α) :=
  M.Indep I ∧ M.cl I ∉ U

def ModularCut.ConBase (U : M.ModularCut) (B : Set α) :=
  (M.Base B ∧ (U : Set (Set α)) = ∅) ∨
    ((U : Set (Set α)).Nonempty ∧ ∀ F ∈ U, ∃ f ∈ F, M.Base (insert f B))

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
    U.ExtIndep e I ↔ M.Indep (I \ {e}) ∧ M.cl I ∈ U :=
  sorry

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

lemma ModularCut.foo1 {U : M.ModularCut} (he : e ∉ M.E) (hX : X ⊆ insert e M.E) :
    I ∈ maximals (· ⊆ ·) {J | U.ExtIndep e J ∧ J ⊆ X} ↔
    I ⊆ X ∧ M.Indep (I \ {e}) ∧
      ( (e ∉ I ∧ e ∉ X ∧ M.cl (I \ {e}) = M.cl (X \ {e}))) ∨
        (e ∉ I ∧ e ∈ X ∧ M.cl (I \ {e}) = M.cl (X \ {e}) ∧ M.cl (X \ {e}) ∈ U) ∨
        (e ∈ I ∧ M.cl (I \ {e}) = M.cl (X \ {e}) ∧ M.cl (X \ {e}) ∉ U) ∨
        (e ∈ I ∧ (M.cl (I \ {e}) ⋖[M] M.cl (X \ {e})) ∧ M.cl (X \ {e}) ∈ U) := by
  sorry

-- example {PI PX Q R T : Prop} (hIX : PI → PX) :
--     ((¬ PI ∧ ¬ PX ∧ Q) ∨ (¬ PI ∧ PX ∧ Q ∧ R) ∨ (PI ∧ Q ∧ ¬ R) ∨ (PI ∧ ¬ Q ∧ R)) ↔
--       (PI ↔ ¬ R) := by
--   obtain (hQ | hQ) := em Q
--   · simp [hQ]
--     rw [← or_assoc, ← and_or_left, ← Classical.not_imp, ← imp_iff_or_not]
--     obtain (hPI | hPI) := em PI
--     · simp [hPI]
--     simp [hPI]





-- lemma ModularCut.foo2 {U : M.ModularCut} (he : e ∉ M.E) (hX : X ⊆ insert e M.E) :
--     I ∈ maximals (· ⊆ ·) {J | U.ExtIndep e J ∧ J ⊆ X} ↔
--     I ⊆ X ∧ M.Indep (I \ {e}) ∧ (e ∈ I → M.cl (X \ {e}) ∉ U) ∧
--       (M.cl (I \ {e}) = M.cl (X \ {e}))
--     ∨ ((M.cl (I \ {e}) ⋖[M] M.cl (X \ {e})) ∧ e ∈ I ∧ e ∈ X ∧ M.cl (I \ {e}) ∈ U) := by
--   simp_rw [mem_maximals_iff_forall_insert sorry, extIndep_def he]
--   obtain (heI | heI) := em' (e ∈ I)
--   · simp only [heI, not_false_eq_true, and_comm (a := M.Indep I), true_and, diff_singleton_eq_self,
--       and_false, false_and, or_false, mem_insert_iff, insert_subset_iff, not_and, and_assoc,
--       false_implies, and_congr_right_iff, and_congr_left_iff]
--     intro hIX hI
--     simp only [hIX, not_true_eq_false, imp_false]

--     refine ⟨fun h ↦ (M.cl_subset_cl (subset_diff_singleton hIX heI)).antisymm ?_, fun h ↦ ?_⟩
--     · refine M.cl_subset_cl_of_subset_cl fun x ⟨hx, (hne : x ≠ e)⟩ ↦ ?_
--       rw [hI.mem_cl_iff', and_iff_right (Or.elim (hX hx) (by simp [hne]) id)]
--       refine fun hxIi ↦ by_contra fun hxI ↦ ?_
--       specialize h x
--       tauto
--     rintro x hxI
--     obtain (rfl | hxe) := eq_or_ne e x
--     · simp [diff_singleton_eq_self hxI, hI]
    -- · refine M.cl_subset_cl_of_subset_cl fun x ⟨hx, (hne : x ≠ e)⟩ ↦ ?_

    -- rintro x hxI (⟨hxIi, hex⟩ | h) hxX
    -- ·
    -- have := h x hxI ⟨


        -- (e ∉ I ∧ e ∉ X ∧ M.cl (I \ {e}) = M.cl (X \ {e}))) ∨
        -- (e ∉ I ∧ e ∈ X ∧ M.cl (I \ {e}) = M.cl (X \ {e}) ∧ M.cl (X \ {e}) ∈ U) ∨
        -- (e ∈ I ∧ M.cl (X \ {e}) ∈ U ∧ (M.cl (I \ {e}) ⋖[M] M.cl (X \ {e}))) := by


-- lemma ModularCut.foo2 {U : M.ModularCut} (he : e ∉ M.E) (hU : M.cl (X \ {e}) ∈ U) :
--     I ∈ maximals (· ⊆ ·) {J | U.ExtIndep e J ∧ J ⊆ X} ↔
--     I ⊆ X ∧ M.Indep (I \ {e}) ∧ ((e ∉ I ∧ M.cl I = M.cl (X \ {e})))
--                         ∨ (e ∈ I ∧ (M.cl (I \ {e}) ⋖[M] M.cl (X \ {e}))) := by
--   sorry


def ModularCut.extendIndepMatroid (U : ModularCut M) (he : e ∉ M.E) : IndepMatroid α where

  E := insert e M.E
  Indep := U.ExtIndep e
  indep_empty := Or.inl M.empty_indep
  indep_subset _ _ := ModularCut.ExtIndep.subset
  indep_aug := by

    intro I B hI hInotmax hB
    by_contra! hcon

    have hBi : U.ExtIndep e B := hB.1
    have hss : B \ {e} ⊆ (I ∪ B) \ {e} := sorry
    -- have hIBe : (I ∪ B) \ {e} ⊆ M.E := sorry

    have hImax : I ∈ maximals (· ⊆ ·) {J | U.ExtIndep e J ∧ J ⊆ I ∪ B} := by
      rw [mem_maximals_iff_forall_insert (fun _ _ ht hst ↦ ⟨ht.1.subset hst, hst.trans ht.2⟩),
        and_iff_right hI, and_iff_right (subset_union_left _ _)]
      intro x hxI h'
      rw [insert_subset_iff, mem_union, or_iff_right hxI] at h'
      exact hcon x ⟨h'.2.1, hxI⟩ h'.1

    have hBmax : B ∈ maximals (· ⊆ ·) {J | U.ExtIndep e J ∧ J ⊆ insert e M.E} := by
      convert hB; rw [and_iff_left_of_imp ExtIndep.subset_insert_ground]

    have hInmax : I ∉ maximals (· ⊆ ·) {J | U.ExtIndep e J ∧ J ⊆ insert e M.E} := by
      convert hInotmax; rw [and_iff_left_of_imp ExtIndep.subset_insert_ground]
    clear hInotmax hB hcon

    -- simp only [U.foo1 he sorry, hI.diff_singleton_indep, mem_insert_iff, true_or, not_true_eq_false,
    --   mem_singleton_iff, insert_diff_of_mem, diff_singleton_eq_self he, cl_ground, ←
    --   spanning_iff_cl (hI.diff_singleton_indep.subset_ground), false_and, and_false, true_and,
    --   false_or, not_or, not_and, not_not, ← hyperplane_iff_covby,
    --   ← spanning_iff_cl (hBi.diff_singleton_indep.subset_ground), subset_union_left, mem_union]
    --   at hInmax hBmax hImax
    rw [U.foo1 he sorry] at hImax hBmax hInmax

    obtain (heI | heI) := em' (e ∈ I)
    · have hIs : M.cl I = M.E → M.E ∉ U := by simpa [heI, he] using hInmax
      rw [extIndep_iff_of_not_mem he heI] at hI
      rw [← spanning_iff_cl] at hIs
      -- simp [U.foo1 he sorry, heI, he] at hImax
      obtain (heB | heB) := em' (e ∈ B)
      · rw [extIndep_iff_of_not_mem he heB] at hBi
        have hBs : M.cl B = M.E ∧ M.E ∈ U := by simpa [heB, he] using hBmax
        have hIBs : M.cl I = M.cl (I ∪ B) := by simpa [heI, heB, hI] using hImax
        rw [← spanning_iff_cl] at hBs
        rw [hBs.1.cl_superset_eq (subset_union_right I B), ← spanning_iff_cl] at hIBs
        exact hIs hIBs hBs.2
      simp [heI, heB, he] at hBmax
      simp only [heI, not_false_eq_true, heB, not_true_eq_false, and_false, diff_singleton_eq_self,
        false_and, or_true, true_and, or_self, or_false, false_or, true_implies, false_implies,
        and_self, and_true, extIndep_def he] at hImax hBmax hInmax hI hBi
      obtain (⟨hB, hEU⟩ | ⟨hB, hEU⟩) := hBmax
      · exact hEU <| U.superset_mem hImax.2 M.ground_flat (M.cl_subset_ground _)
      obtain (h_eq | hssu) := (M.cl_subset_cl hss).eq_or_ssubset
      · rw [← h_eq] at hImax
        exact hBi.2 hImax.2
      rw [← hImax.1] at hssu
      have hI' := hB.cl_eq_ground_of_ssuperset hssu
      rw [cl_cl, ← spanning_iff_cl (S := I) hI.subset_ground] at hI'
      exact hInmax hI' hEU
    obtain (rfl | hU) := U.eq_empty_or_top_mem
    · simp only [heI, not_true_eq_false, false_and, and_self, true_or, empty, mem_mk_iff,
      mem_empty_iff_false, and_false, not_false_eq_true, and_true, true_and, or_false, false_or,
      implies_true, false_implies, imp_false, true_implies, imp_self] at hImax hInmax hBmax
      rw [hBmax.2.cl_superset_eq hss, ← spanning_iff_cl (hI.diff_singleton_indep.subset_ground)]
        at hImax
      contradiction
    obtain (heB | heB) := em (e ∈ B)
    · simp only [heI, not_true_eq_false, heB, and_self, false_and, or_self, true_and, false_or,
        false_implies, true_implies, extIndep_def he, and_false, and_true]
        at hImax hInmax hI hBmax hBi
      obtain (rfl | hU) := U.eq_empty_or_top_mem
      · simp only [diff_singleton_subset_iff, insert_diff_singleton, empty, mem_mk_iff,
          mem_empty_iff_false, not_false_eq_true, and_true, and_false, or_false, imp_false,
          implies_true] at hImax hInmax hBmax
        rw [hBmax.cl_superset_eq hss, ← spanning_iff_cl] at hImax
        contradiction
      simp only [hU, not_true_eq_false, and_false, and_true, false_or, implies_true, imp_false,
        true_and] at hBmax hInmax
      sorry
    simp [heB, heI, hU] at hImax hBmax hInmax
    have hcl := hBmax.cl_superset_eq
      (show B ⊆ (I ∪ B) \ {e} from subset_diff_singleton (subset_union_right I B) heB)
    simp only [hcl, hU, not_true_eq_false, and_false, and_true, false_or, ← hyperplane_iff_covby]
      at hImax
    exact hInmax hImax





  indep_maximal := by
    intro X hXE I hI hIX
    sorry
  subset_ground := sorry
