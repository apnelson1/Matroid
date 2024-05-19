import Matroid.ForMathlib.Order.Minimal
import Matroid.ForMathlib.MatroidBasic
import Matroid.Modular

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

theorem ModularCut.extIndep_iff {U : M.ModularCut} (he : e ∉ M.E) :
    U.ExtIndep e I ↔ (M.Indep I ∧ e ∉ I) ∨ (M.Indep (I \ {e}) ∧ M.cl (I \ {e}) ∉ U ∧ e ∈ I) := by
  refine ⟨fun h ↦ h.or he, ?_⟩
  rintro (h | h)
  · exact .inl h.1
  exact .inr ⟨h.1, h.2.1⟩



lemma ModularCut.insert_maximal_extIndep_subset_insert_iff {U : M.ModularCut} (heE : e ∉ M.E)
    (heI : e ∉ I) (hX : X ⊆ M.E) :
    insert e I ∈ maximals (· ⊆ ·) {J | U.ExtIndep e J ∧ J ⊆ insert e X} ↔
      (M.Indep I ∧ M.cl I ∉ U ∧ I ⊆ X ∧ ∀ x ∈ X \ I,
        M.Indep (insert x I) → X ⊆ M.cl (insert x I) ∧ M.cl (insert x I) ∈ U) := by


  rw [mem_maximals_iff_forall_insert (fun _ _ ht hst ↦ ⟨ht.1.subset hst, hst.trans ht.2⟩),
    insert_subset_insert_iff heI]
  simp_rw [insert_comm, extIndep_insert_iff heE heI, mem_insert_iff, not_or, not_and, and_imp,
    mem_diff]
  simp only [and_assoc, insert_subset_iff, mem_insert_iff, true_or,
    subset_insert_iff_of_not_mem heI, true_and, not_and, and_imp, and_congr_right_iff]


  refine fun _ hIU hIX ↦ ?_
  simp only [hIX, not_true_eq_false, imp_false, not_or]
  refine ⟨fun h x hxX hxI hxIi ↦ ?_, fun h x ↦ ?_⟩
  · have hxe : ¬ (x = e) := by rintro rfl; exact heE (hX hxX)
    have hxIU := h x hxe hxI

    rw [extIndep_insert_iff heE (by simp [Ne.symm hxe, heI]), and_iff_right hxIi, and_iff_right hxe,
      imp_not_comm, not_not, imp_iff_right hxX] at hxIU

    simp_rw [and_iff_left hxIU, subset_def, hxIi.mem_cl_iff', mem_insert_iff]
    by_contra! hcl
    obtain ⟨y, hyX, hcl⟩ := hcl
    obtain ⟨hyxI, hyx, hyI⟩ := hcl (hX hyX)
    have hye : ¬ (y = e) := by rintro rfl; exact heE (hX hyX)

    have hyIU := h y hye hyI
    rw [extIndep_insert_iff heE (by simp [heI, Ne.symm hye]), and_iff_right hye, iff_true_intro hyX,
      not_true, imp_false, and_iff_right (hyxI.subset (insert_subset_insert (subset_insert _ _))),
      not_not] at hyIU

    have h_inter_mem := U.inter_mem hxIU hyIU (modularPair_insert_cl M I x y)

    rw [← Indep.cl_inter_eq_inter_cl, insert_inter_of_not_mem (by simp [hyx.symm, hxI]),
      inter_eq_self_of_subset_left (subset_insert _ _)] at h_inter_mem
    · contradiction
    exact hyxI.subset (union_subset (subset_insert _ _) (insert_subset_insert (subset_insert _ _)))
  intro hxe hxI
  rw [extIndep_insert_iff heE (by simp [Ne.symm hxe, heI])]
  specialize h x
  tauto


lemma ModularCut.maximal_extIndep_subset_insert_iff {U : M.ModularCut} (heE : e ∉ M.E)
    (hX : X ⊆ M.E) (heI : e ∉ I) :
    I ∈ maximals (· ⊆ ·) {J | U.ExtIndep e J ∧ J ⊆ insert e X} ↔ M.Basis I X ∧ M.cl I ∈ U := by
  obtain (hIX | hIX) := em' (I ⊆ X)
  · simp [mem_maximals_iff, hIX, basis_iff', extIndep_iff_of_not_mem heE heI,
      subset_insert_iff_of_not_mem heI]
  rw [mem_maximals_iff_forall_insert (fun _ _ ht hst ↦ ⟨ht.1.subset hst, hst.trans ht.2⟩)]
  simp_rw [extIndep_iff_of_not_mem heE heI, insert_subset_iff, subset_insert_iff_of_not_mem heI,
    and_iff_left hIX, not_and, imp_not_comm]
  refine ⟨fun ⟨hI, hImax⟩ ↦ ⟨hI.basis_of_maximal_subset hIX ?_, ?_⟩, fun h ↦ ⟨h.1.indep, ?_⟩⟩
  · exact fun J hJ hIJ hJX x hxJ ↦ by_contra fun hxI ↦ hImax x hxI (.inr (hJX hxJ))
      (.inl (hJ.subset (insert_subset hxJ hIJ)))
  · refine by_contra fun hcl ↦ hImax e heI (.inl rfl) ?_
    rw [extIndep_insert_iff heE heI]
    exact ⟨hI, hcl⟩
  rintro x hxI (rfl | hxX) h'
  · rw [extIndep_insert_iff heE heI] at h'
    exact h'.2 h.2
  rw [extIndep_iff_of_not_mem heE] at h'
  · exact hxI <| h.1.mem_of_insert_indep hxX h'
  rintro (rfl | heI')
  · exact heE <| hX hxX
  contradiction

lemma ModularCut.maximal_extIndep_subset_iff {U : M.ModularCut} (heE : e ∉ M.E)
    (hX : X ⊆ M.E) : I ∈ maximals (· ⊆ ·) {J | U.ExtIndep e J ∧ J ⊆ X} ↔ M.Basis I X := by
  obtain (hIX | hIX) := em' (I ⊆ X)
  · simp [mem_maximals_iff, hIX, basis_iff']
  simp only [U.extIndep_def heE, mem_maximals_iff, mem_setOf_eq,
    show e ∉ I from fun h ↦ heE (hIX.trans hX h), not_false_eq_true, and_true,
    diff_singleton_eq_self, and_false, or_false, hIX, and_imp]
  refine ⟨fun h ↦ h.1.basis_of_maximal_subset hIX fun J hJ hIJ hJX ↦ ?_, fun h ↦ ⟨h.indep, ?_⟩⟩
  · rw [h.2 (.inl ⟨hJ, (fun heJ ↦ heE (hJX.trans hX heJ))⟩) hJX hIJ]
  rintro J (⟨hJ, -⟩ | ⟨-, -, heJ⟩) hJX hIJ
  · exact h.eq_of_subset_indep hJ hIJ hJX
  exact False.elim <| heE (hJX.trans hX heJ)

lemma ModularCut.insert_maximal_extIndep_iff_of_not_mem {U : M.ModularCut} (heE : e ∉ M.E)
    (hXU : M.cl X ∉ U) (hX : X ⊆ M.E) (heI : e ∉ I) :
    insert e I ∈ maximals (· ⊆ ·) {J | U.ExtIndep e J ∧ J ⊆ insert e X} ↔ M.Basis I X := by
  rw [mem_maximals_iff_forall_insert (fun _ _ ht hst ↦ ⟨ht.1.subset hst, hst.trans ht.2⟩),
    extIndep_insert_iff heE heI, insert_subset_insert_iff heI, and_assoc, and_assoc]
  simp_rw [insert_comm, extIndep_insert_iff' heE]
  refine ⟨fun ⟨hI, _, hIX, hImax⟩ ↦ ?_, fun h ↦ ?_⟩
  · refine hI.basis_of_forall_insert hIX (fun f hf ↦ ?_)
    have hfe : f ≠ e := by rintro rfl; exact heE (hX hf.1)
    have hefI : e ∉ insert f I := by rintro (rfl | heI) <;> contradiction
    have hfIX : insert f I ⊆ X := insert_subset hf.1 hIX
    rw [dep_iff, and_iff_left (insert_subset (hX hf.1) hI.subset_ground),
      ← diff_singleton_eq_self heI, insert_diff_singleton_comm hfe]
    refine fun hi ↦ hXU <| U.cl_superset_mem' (by_contra fun hxIU ↦ ?_) hfIX
    simpa [hfe, hf.2, hi, hxIU, insert_subset_insert_iff hefI, hfIX] using hImax f

  refine ⟨h.indep, fun hIU ↦ hXU <| U.cl_superset_mem' hIU h.subset, h.subset, fun x hx ↦ ?_⟩
  have hex : e ≠ x := by rintro rfl; exact hx <| .inl rfl
  have hexI : e ∉ insert x I := by rintro (rfl | h) <;> contradiction
  rw [insert_subset_insert_iff hexI, diff_singleton_eq_self hexI]
  simp only [not_and, and_imp, not_imp_not]
  exact fun hxIi hxIX ↦ False.elim <| hx (.inr (h.mem_of_insert_indep (hxIX (.inl rfl)) hxIi))

lemma ModularCut.insert_maximal_extIndep_subset_iff_of_mem {U : M.ModularCut} (heE : e ∉ M.E)
    (hXU : M.cl X ∈ U) (hX : X ⊆ M.E) (heI : e ∉ I) :
    insert e I ∈ maximals (· ⊆ ·) {J | U.ExtIndep e J ∧ J ⊆ insert e X} ↔
      M.cl I ∉ U ∧ ∃ y, M.Basis (insert y I) X := by
  rw [mem_maximals_iff_forall_insert (fun _ _ ht hst ↦ ⟨ht.1.subset hst, hst.trans ht.2⟩),
    extIndep_insert_iff heE heI, insert_subset_insert_iff heI, and_assoc, and_assoc]
  simp_rw [insert_comm, extIndep_insert_iff' heE]
  simp only [mem_insert_iff, not_or, not_and, and_imp, mem_diff]
  refine ⟨fun ⟨hI, hIU, hIX, hmax⟩ ↦ ⟨hIU, ?_⟩, fun ⟨hIU, y, hyI⟩ ↦ ?_⟩
  · by_contra! hcon
    obtain ⟨J, hJ, hIJ⟩ := hI.subset_basis_of_subset hIX
    have hmax' : ∀ w ∈ J \ I, M.cl (insert w I) ∈ U := by
      refine fun w ⟨hw, hwI⟩ ↦ by_contra fun hwIU ↦ ?_
      have hew : w ≠ e := (by rintro rfl; exact heE <| hJ.indep.subset_ground hw)
      apply hmax w hew hwI (hJ.indep.subset ((diff_subset _ _).trans (insert_subset hw hIJ))) hwIU
      rw [insert_subset_insert_iff (by simp [hew.symm, heI])]
      exact insert_subset (hJ.subset hw) (hIJ.trans hJ.subset)
    obtain (rfl | hss) := hIJ.eq_or_ssubset
    · rw [hJ.cl_eq_cl] at hIU; contradiction
    obtain ⟨x, hxJ, hxI⟩ := exists_of_ssubset hss
    have hJ' : insert x I ⊂ J :=
      (insert_subset hxJ hIJ).ssubset_of_ne (by rintro rfl; exact hcon x hJ)
    obtain ⟨y, hyJ, hyI⟩ := exists_of_ssubset hJ'
    simp only [mem_insert_iff, not_or] at hyI
    have h_inter_mem :=
      U.inter_mem (hmax' x ⟨hxJ, hxI⟩) (hmax' y ⟨hyJ, hyI.2⟩) (modularPair_insert_cl M I x y)
    rw [← Indep.cl_inter_eq_inter_cl, insert_inter_of_not_mem (by simp [Ne.symm hyI.1, hxI]),
      inter_eq_self_of_subset_left (subset_insert _ _)] at h_inter_mem
    · contradiction
    exact hJ.indep.subset (union_subset (insert_subset hxJ hIJ) (insert_subset hyJ hIJ))
  have hI : M.Indep I := hyI.indep.subset <| subset_insert _ _
  have hIX : I ⊆ X := (subset_insert _ _).trans hyI.subset
  refine ⟨hI, hIU, hIX, fun x hxe hxI ↦ ?_⟩
  have hexI : e ∉ insert x I := by simp [Ne.symm hxe, heI]
  rw [diff_singleton_eq_self hexI, insert_subset_insert_iff hexI, insert_subset_iff,
    and_iff_left hIX, not_imp_not]
  intro hxIi hxX
  have hxI' : x ∈ M.cl (insert y I) \ M.cl I := ⟨hyI.subset_cl hxX, hI.not_mem_cl_iff.2 ⟨hxIi, hxI⟩⟩
  obtain h' := mem_cl_insert hxI'.2 hxI'.1
  apply U.cl_superset_mem hXU (M.cl_subset_cl_of_subset_cl ?_)
  refine hyI.subset_cl.trans (M.cl_subset_cl_of_subset_cl (insert_subset h' ?_))
  exact (M.subset_cl I hI.subset_ground).trans (M.cl_subset_cl (subset_insert _ _))


@[simp] theorem ModularCut.empty_extIndep_iff :
    (ModularCut.empty M).ExtIndep e I ↔ M.Indep (I \ {e}) := by
  simp only [ExtIndep, empty, mem_mk_iff, mem_empty_iff_false, not_false_eq_true, and_true,
    or_iff_right_iff_imp]
  exact fun hI ↦ hI.diff _

def ModularCut.extendIndepMatroid (U : ModularCut M) (he : e ∉ M.E) : IndepMatroid α where

  E := insert e M.E
  Indep := U.ExtIndep e
  indep_empty := Or.inl M.empty_indep
  indep_subset _ _ := ModularCut.ExtIndep.subset
  indep_aug := by

    intro I B hI hInotmax hB
    by_contra! hcon

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

    obtain (heB | ⟨B, heB, rfl⟩) := not_mem_or_exists_eq_insert_not_mem B e
    · rw [maximal_extIndep_subset_insert_iff he Subset.rfl heB, basis_ground_iff] at hBmax
      obtain ⟨hB, hBU⟩ := hBmax
      rw [hB.cl_eq] at hBU
      obtain (heI | ⟨I, heI, rfl⟩) := not_mem_or_exists_eq_insert_not_mem I e
      · rw [maximal_extIndep_subset_insert_iff he Subset.rfl heI, basis_ground_iff] at hInmax

        rw [extIndep_iff_of_not_mem he heI] at hI
        rw [maximal_extIndep_subset_iff he (by aesop_mat), basis_union_iff_indep_cl,
          ← M.cl_subset_cl_iff_subset_cl, hB.cl_eq, ← hI.base_iff_ground_subset_cl] at hImax
        rw [hImax.2.cl_eq, and_iff_left hBU] at hInmax
        exact hInmax hImax.2

      rw [extIndep_insert_iff he heI] at hI; obtain ⟨hI, hIU⟩ := hI
      rw [insert_union, insert_maximal_extIndep_subset_insert_iff he heI (by aesop_mat),
        and_iff_right hI, and_iff_right hIU, and_iff_right (subset_union_left _ _),
        union_diff_left] at hImax
      simp_rw [insert_maximal_extIndep_subset_iff_of_mem he (by simpa) Subset.rfl heI,
        and_iff_right hIU, not_exists, basis_ground_iff] at hInmax
      obtain ⟨J, hJ, hIJ⟩ := hI.subset_basis_of_subset (subset_union_left I B)
      obtain (rfl | hssu) := hIJ.eq_or_ssubset
      · rw [(hB.base_of_basis_superset (subset_union_right _ _) hJ).cl_eq] at hIU; contradiction
      obtain ⟨x, hxJ, hxI⟩ := exists_of_ssubset hssu
      have hxB : x ∈ B := Or.elim (hJ.subset hxJ) (False.elim ∘ hxI) id
      have hxIi : M.Indep (insert x I) := (hJ.indep.subset (insert_subset hxJ hIJ))
      have hBxI : M.cl B ⊆ M.cl (insert x I) :=
        M.cl_subset_cl_of_subset_cl <| (subset_union_right _ _).trans (hImax x ⟨hxB, hxI⟩ hxIi).1
      rw [hB.cl_eq, ← hxIi.base_iff_ground_subset_cl] at hBxI
      exact hInmax x hBxI

    obtain (rfl | hU) := U.eq_empty_or_top_mem
    · rw [insert_maximal_extIndep_iff_of_not_mem he (by simp [ModularCut.empty]) Subset.rfl heB,
        basis_ground_iff] at hBmax
      obtain (heI | ⟨I, heI, rfl⟩) := not_mem_or_exists_eq_insert_not_mem I e
      · rw [empty_extIndep_iff, diff_singleton_eq_self heI] at hI
        rw [union_insert, maximal_extIndep_subset_insert_iff he
          (union_subset hI.subset_ground hBmax.subset_ground) heI] at hImax
        simp [ModularCut.empty] at hImax
      simp only [empty_extIndep_iff, mem_singleton_iff, insert_diff_of_mem,
        diff_singleton_eq_self heI] at hI
      rw [← insert_union_distrib, insert_maximal_extIndep_iff_of_not_mem he
        (by simp [ModularCut.empty]) (union_subset hI.subset_ground hBmax.subset_ground) heI,
        basis_union_iff_indep_cl] at hImax
      rw [insert_maximal_extIndep_iff_of_not_mem he (by simp [ModularCut.empty])
        Subset.rfl heI, basis_ground_iff] at hInmax
      rw [← M.cl_subset_cl_iff_subset_cl, hBmax.cl_eq, ← hI.base_iff_ground_subset_cl] at hImax
      exact hInmax hImax.2

    simp_rw [insert_maximal_extIndep_subset_iff_of_mem he (by simpa) Subset.rfl heB,
      basis_ground_iff] at hBmax
    obtain ⟨hBU, x, hxBb⟩ := hBmax
    have hBi : M.Indep B := hxBb.indep.subset (subset_insert _ _)
    obtain (heI | ⟨I, heI, rfl⟩) := not_mem_or_exists_eq_insert_not_mem I e
    · rw [maximal_extIndep_subset_insert_iff he Subset.rfl heI, basis_ground_iff, not_and] at hInmax
      have hInb : ¬ M.Base I :=
        fun hI ↦ by rw [hI.cl_eq, imp_iff_right hI] at hInmax; contradiction
      rw [extIndep_iff_of_not_mem he heI] at hI
      rw [union_insert, maximal_extIndep_subset_insert_iff he (by aesop_mat) heI,
        basis_union_iff_indep_cl, and_iff_right hI, ← M.cl_subset_cl_iff_subset_cl] at hImax

      obtain ⟨B', hB', hBB'⟩ := hBi.subset_basis_of_subset (subset_union_right I B)
      obtain (rfl | hssu) := hBB'.eq_or_ssubset
      · rw [union_comm, basis_union_iff_indep_cl, ← M.cl_subset_cl_iff_subset_cl] at hB'
        rw [hB'.2.antisymm hImax.1] at hImax
        exact hBU hImax.2
      obtain ⟨f, hfB', hfB⟩ := exists_of_ssubset hssu
      obtain (hxB | hxB) := em (x ∈ B)
      · rw [insert_eq_of_mem hxB] at hxBb
        rw [hxBb.cl_eq, ← hI.base_iff_ground_subset_cl] at hImax
        exact hInb hImax.1
      have hfBb : M.Base (insert f B) := M.insert_base_of_insert_indep hxB hfB hxBb
        (hB'.indep.subset (insert_subset hfB' hBB'))

      have hfI : f ∈ I := Or.elim (hB'.subset hfB') id (False.elim ∘ hfB)

      have hfBI : insert f B ⊆ M.cl I :=
        insert_subset (M.mem_cl_of_mem hfI) <| (M.subset_cl B).trans hImax.1

      rw [← cl_subset_cl_iff_subset_cl, hfBb.cl_eq, ← hI.base_iff_ground_subset_cl] at hfBI
      contradiction

    rw [extIndep_insert_iff he heI] at hI; obtain ⟨hI, hIU⟩ := hI

    rw [← insert_union_distrib, insert_maximal_extIndep_subset_insert_iff he heI (by aesop_mat),
      and_iff_right hI, and_iff_right hIU, union_diff_left, and_iff_right (subset_union_left _ _)]
      at hImax
    simp_rw [insert_maximal_extIndep_subset_iff_of_mem he (by simpa) Subset.rfl heI,
      and_iff_right hIU, basis_ground_iff, not_exists] at hInmax

    obtain ⟨J, hJ, hIJ⟩ := hI.subset_basis_of_subset (subset_union_left I B)
    have hJIcl : ∀ x ∈ J \ I, M.cl (insert x I) ∈ U := by
      rintro f ⟨hfJ, hfI⟩
      have hfB : f ∈ B := Or.elim (hJ.subset hfJ) (False.elim ∘ hfI) id
      exact And.right <| hImax f ⟨hfB, hfI⟩ (hJ.indep.subset (insert_subset hfJ hIJ))

    have hJIf : ∃ f ∉ I, J = insert f I := by
      obtain (hJI | ⟨x,hx,y,hy,hne⟩) := (J \ I).subsingleton_or_nontrivial
      · obtain (h_empty | ⟨f, hf⟩) := hJI.eq_empty_or_singleton
        · refine False.elim <| hInmax x ?_
          rw [diff_eq_empty] at h_empty; obtain rfl := hIJ.antisymm h_empty
          rw [basis_union_iff_indep_cl] at hJ
          have hxclI : x ∈ M.E \ M.cl I := by
            refine ⟨hxBb.subset_ground <| .inl rfl, fun hclI ↦ ?_⟩
            have hss := M.cl_subset_cl_of_subset_cl (insert_subset hclI hJ.2)
            rw [hxBb.cl_eq, ← hI.base_iff_ground_subset_cl] at hss
            rw [hss.cl_eq] at hIU; contradiction
          rw [Indep.base_iff_ground_subset_cl, ← hxBb.cl_eq]
          · refine M.cl_subset_cl_of_subset_cl (insert_subset (M.mem_cl_of_mem (.inl rfl))
              (hJ.2.trans (M.cl_subset_cl (subset_insert _ _))))
          exact hI.insert_indep_iff.2 <| .inl hxclI

        exact ⟨f, (hf.symm.subset rfl).2, by rw [← diff_union_of_subset hIJ, hf, singleton_union]⟩
      refine False.elim <| hIU ?_
      have hcl := U.inter_mem (hJIcl x hx) (hJIcl y hy) (M.modularPair_insert_cl _ _ _)
      rwa [← Indep.cl_inter_eq_inter_cl, insert_inter_of_not_mem (by simp [hx.2, hne]),
        inter_eq_self_of_subset_left (subset_insert _ _)] at hcl
      exact hJ.indep.subset (union_subset (insert_subset hx.1 hIJ) (insert_subset hy.1 hIJ))

    obtain ⟨f, hfI, rfl⟩ := hJIf
    obtain (hss | hnss) := em (I ⊆ M.cl B)
    · specialize hJIcl f ⟨.inl rfl, hfI⟩
      apply hBU
      refine U.cl_superset_mem hJIcl (M.cl_subset_cl_of_subset_cl (insert_subset ?_ hss))
      exact (hJ.subset.trans (union_subset hss (M.subset_cl B hBi.subset_ground))) (.inl rfl)
    refine hInmax f ?_
    rw [hJ.indep.base_iff_ground_subset_cl, ← hxBb.cl_eq]
    refine M.cl_subset_cl_of_subset_cl (insert_subset ?_ ?_)

    · rw [hJ.cl_eq_cl]
      obtain ⟨y, hyI, hyB⟩ := not_subset.1 hnss
      have hxyB : y ∈ M.cl (insert x B) := by
        rw [hxBb.cl_eq]; exact hI.subset_ground hyI
      replace hxyB := mem_cl_insert hyB hxyB
      exact M.cl_subset_cl (insert_subset (.inl hyI) (subset_union_right _ _)) hxyB

    exact (subset_union_right _ _).trans hJ.subset_cl

  indep_maximal := sorry
  subset_ground := sorry
