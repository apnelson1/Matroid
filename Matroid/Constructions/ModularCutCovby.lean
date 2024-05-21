import Matroid.ForMathlib.Order.Minimal
import Matroid.ForMathlib.MatroidBasic
import Matroid.Modular
import Matroid.Flat

open Set Function Set.Notation




variable {α : Type*} {M : Matroid α} {I J B F₀ F F' X Y : Set α} {e f : α}



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

def ModularCut.principal (M : Matroid α) (X : Set α) : M.ModularCut where
  carrier := {F | M.Flat F ∧ X ⊆ F}
  forall_flat _ h := h.1
  forall_superset _ _ hF hF' hFF' := ⟨hF', hF.2.trans hFF'⟩
  forall_inter _ hS hne _ := ⟨Flat.sInter hne fun _ h ↦ (hS h).1, subset_sInter fun _ h ↦ (hS h).2⟩

@[simp] lemma ModularCut.mem_principal_iff : F ∈ principal M X ↔ M.Flat F ∧ X ⊆ F := Iff.rfl

@[simps] def ModularCut.empty (M : Matroid α) : M.ModularCut where
  carrier := ∅
  forall_flat := by simp
  forall_superset := by simp
  forall_inter := by simp [subset_empty_iff]

instance (M : Matroid α) : PartialOrder M.ModularCut where
  le U U' := (U : Set (Set α)) ⊆ U'
  le_refl _ := Subset.rfl
  le_trans _ _ _ := Subset.trans
  le_antisymm U U' h h' := by simpa using subset_antisymm h h'

lemma ModularCut.le_iff_subset {U U' : M.ModularCut} :
  U ≤ U' ↔ (U : Set (Set α)) ⊆ U' := Iff.rfl

instance (M : Matroid α) : BoundedOrder M.ModularCut where
  top := ModularCut.principal M ∅
  le_top U x h := by simpa using U.flat_of_mem h
  bot := ModularCut.empty M
  bot_le _ _ := by simp

lemma ModularCut.eq_bot_or_ground_mem (U : M.ModularCut) : U = ⊥ ∨ M.E ∈ U := by
  obtain (hU | ⟨F, hF⟩) := (U : Set (Set α)).eq_empty_or_nonempty
  · left
    ext x
    change x ∈ (U : Set (Set α)) ↔ x ∈ ∅
    simp [hU]
  exact .inr <| U.superset_mem hF M.ground_flat (U.flat_of_mem hF).subset_ground

@[simp] protected lemma ModularCut.not_mem_bot (M : Matroid α) (X : Set α) :
    ¬ X ∈ (⊥ : M.ModularCut) :=
  not_mem_empty X

protected lemma ModularCut.mem_top_of_flat (hF : M.Flat F) : F ∈ (⊤ : M.ModularCut) :=
  ⟨hF, empty_subset F⟩

lemma ModularCut.mem_of_ssubset_indep_of_forall_diff (U : M.ModularCut) (hI : M.Indep I)
    (hJI : J ⊂ I) (h : ∀ e ∈ I \ J, M.cl (I \ {e}) ∈ U) : M.cl J ∈ U := by
  set Is : ↑(I \ J) → Set α := fun e ↦ I \ {e.1} with hIs
  have hmod : M.ModularFamily Is := hI.modularFamily_of_subsets (by simp [hIs])
  have hne := nonempty_of_ssubset hJI
  have h_inter : ⋂ e, Is e = J := by
    rw [hIs, ← biInter_eq_iInter (t := fun x _ ↦ I \ {x}), biInter_diff_singleton_eq_diff _ hne,
      diff_diff_right, diff_self, empty_union, inter_eq_self_of_subset_right hJI.subset]
  have _ := hne.coe_sort
  rw [← h_inter, ← hmod.iInter_cl_eq_cl_iInter]
  exact U.iInter_mem _ (fun ⟨i, hi⟩ ↦ h _ (by simpa)) hmod.cls_modularFamily

lemma ModularCut.covBy_of_maximal_cl (U : M.ModularCut) {X Y : Set α} (hXY : M.cl X ⊆ M.cl Y)
    (hYU : M.cl Y ∈ U) (hXU : M.cl X ∉ U) (hmax : ∀ x ∈ Y \ M.cl X, M.cl (insert x X) ∈ U) :
      M.cl X ⋖[M] M.cl Y := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_basis'_of_subset (hI.subset.trans (subset_union_left X Y))
  have hJ' := hJ.basis_cl_right
  rw [← cl_cl_union_cl_eq_cl_union, union_eq_self_of_subset_left hXY, cl_cl] at hJ'

  rw [← hI.cl_eq_cl, ← M.cl_cl Y, ← hJ'.cl_eq_cl]
  rw [← M.cl_cl Y, ← hJ'.cl_eq_cl] at hYU
  rw [← hI.cl_eq_cl] at hXU

  obtain (h | hnt) := (J \ I).subsingleton_or_nontrivial
  · obtain (he | ⟨e, he⟩) := h.eq_empty_or_singleton
    · rw [(diff_eq_empty.1 he).antisymm hIJ] at hYU; contradiction
    obtain rfl : J = insert e I := by rw [← union_diff_cancel hIJ, he, union_singleton]
    simpa [show e ∉ I from (he.symm.subset rfl).2] using hJ.indep.cl_diff_covBy (.inl rfl)

  obtain (rfl | hssu) := hIJ.eq_or_ssubset
  · simp at hnt

  refine by_contra fun _ ↦ hXU <| U.mem_of_ssubset_indep_of_forall_diff hJ.indep hssu fun x hx ↦ ?_
  obtain ⟨y, hy, hyx⟩ := hnt.exists_ne x
  have hyE : y ∈ M.E := hJ.indep.subset_ground hy.1
  have hyX : y ∉ M.cl X := by
    rw [← hI.cl_eq_cl, hI.indep.not_mem_cl_iff_of_not_mem hy.2 hyE]
    exact hJ.indep.subset (insert_subset hy.1 hIJ)
  have hyY : y ∈ Y := Or.elim (hJ.subset hy.1) (False.elim ∘ (not_mem_of_mem_diff_cl ⟨hyE, hyX⟩)) id

  specialize hmax y ⟨hyY, hyX⟩
  rw [← cl_insert_cl_eq_cl_insert, ← hI.cl_eq_cl, cl_insert_cl_eq_cl_insert] at hmax
  refine U.cl_superset_mem' hmax ?_
  simp [insert_subset_iff, subset_diff, hIJ, hy.1, hyx.symm, hx.2]

lemma ModularCut.wcovBy_of_maximal_cl (U : M.ModularCut) {X Y : Set α} (hXY : M.cl X ⊆ M.cl Y)
    (hYU : M.cl Y ∈ U) (hmax : ∀ x ∈ Y \ M.cl X, M.cl (insert x X) ∈ U) : M.cl X ⩿[M] M.cl Y := by
  sorry



-- lemma ModularCut.mem_of_forall_covBy_mem (U : M.ModularCut) (hF₀ : M.Flat F₀) (hF : F ∈ U)
--     (hF₀F : F₀ ⊆ F) (h_forall : ∀ F', F₀ ⊆ F' → F' ⋖[M] F → F' ∈ U) : F₀ ∈ U := by
--   obtain ⟨I, hI⟩ := M.exists_basis F₀
--   have hF_flat := U.flat_of_mem hF
--   obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_basis_of_subset (hI.subset.trans hF₀F)
--   obtain (h_empty | h_ne) := (J \ I).eq_empty_or_nonempty
--   · rw [diff_eq_empty] at h_empty
--     obtain rfl := hIJ.antisymm h_empty
--     rwa [← hF₀.cl, ← hI.cl_eq_cl, hJ.cl_eq_cl, hF_flat.cl]

--   set Js : ↑(J \ I) → Set α := fun e ↦ J \ {e.1} with hJs
--   have _ := h_ne.coe_sort
--   have hJscl : ∀ i, M.cl (Js i) ∈ U := by
--     refine fun ⟨e, he⟩ ↦ h_forall _ ?_ ?_
--     · rw [hJs, hF₀.eq_cl_of_basis hI]
--       exact M.cl_subset_cl <| subset_diff_singleton hIJ he.2
--     rw [hJs, hF_flat.eq_cl_of_basis hJ]
--     exact hJ.indep.cl_diff_covBy he.1

--   have h_iInter : ⋂ i, Js i = I := by
--     rwa [hJs, ← biInter_eq_iInter (t := fun x _ ↦ J \ {x}), biInter_diff_singleton_eq_diff _ h_ne,
--       diff_diff_right, diff_self, empty_union, inter_eq_right]

--   have hmod : M.ModularFamily Js := hJ.indep.modularFamily_of_subsets (by simp [Js])
--   have h_inter := U.iInter_mem _ hJscl hmod.cls_modularFamily
--   rwa [hmod.iInter_cl_eq_cl_iInter, h_iInter, ← hF₀.eq_cl_of_basis hI] at h_inter

-- -- lemma ModularCut.wcovBy_of_not_mem_of_forall_covBy_mem (U : M.ModularCut) (hF₀ : M.Flat F₀)
-- --     (hF : M.Flat F) (hF₀F : F₀ ⊆ F) (hF₀U : F₀ ∉ U)
-- --     (h_forall : ∀ F' ⊆ F, F₀ ⋖[M] F' → F' ∈ U) : F₀ ⩿[M] F := by

-- -- lemma ModularCut.mem_of_forall_covBy_mem' (U : M.ModularCut) (hF : M.Flat F) (hFX : F ⊆ M.cl X)
-- --     (hXU : M.cl X ∈ U) (h_forall : ∀ x ∈ X \ F, M.cl (insert x F) ∈ U) : F ∈ U

-- lemma ModularCut.wcovBy_of_not_mem_of_forall_covBy_mem (U : M.ModularCut) (hF₀ : M.Flat F₀)
--     (hF : M.Flat F) (hF₀F : F₀ ⊆ F) (hF₀U : F₀ ∉ U)
--     (h_forall : ∀ F' ⊆ F, F₀ ⋖[M] F' → F' ∈ U) : F₀ ⩿[M] F := by
--   obtain (rfl | hssu) := hF₀F.eq_or_ssubset
--   · exact hF₀.wCovBy_self
--   refine by_contra fun h_con ↦ hF₀U ?_
--   refine U.mem_of_forall_covBy_mem hF₀ ?_ hF₀F fun F' hF₀F' hF'F ↦ ?_
--   · obtain ⟨F', hF', hF'F⟩ := hF₀.exists_left_covBy_of_ssubset hF hssu
--     apply U.superset_mem (h_forall _ hF'F hF') hF hF'F
--   rw [hF₀.wCovby_iff_covBy_or_eq hF, or_iff_left hssu.ne] at h_con
--   replace hF₀F' := hF₀F'.ssubset_of_ne (by rintro rfl; contradiction)
--   obtain ⟨F'', hF'', h⟩ := hF₀.exists_left_covBy_of_ssubset hF'F.flat_left hF₀F'
--   exact U.superset_mem (h_forall F'' (h.trans hF'F.subset) hF'') hF'F.flat_left h

-- -- lemma ModularCut.covBy_of_maximal (U : M.ModularCut) (hF : F ∈ U) {F₀ : Set α} (hF₀ : M.Flat F₀)
-- --     (hF₀U : F₀ ∉ U) (hmax : ∀ x ∈ F \ F₀, M.cl (insert x F₀) ∈ U) : F₀ ⋖[M] F := by
-- --   sorry



--   -- have hwc := U.wcovBy_of_not_mem_of_forall_covBy_mem (M.cl_flat X) (M.cl_flat Y) hXY hXU ?_
--   -- · obtain (h_eq | h) := hwc.eq_or_covBy
--   --   · rw [h_eq] at hXU; contradiction
--   --   exact h
--   -- intro F hFY hXF



--   sorry


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

lemma ModularCut.maximal_extIndep_iff {U : M.ModularCut} (he : e ∉ M.E) (hX : X ⊆ insert e M.E)
    (hI : U.ExtIndep e I) (hIX : I ⊆ X) :
    I ∈ maximals (· ⊆ ·) {J | U.ExtIndep e J ∧ J ⊆ X} ↔
        (M.cl (I \ {e}) = M.cl (X \ {e}) ∧ ((e ∈ I ↔ M.cl (X \ {e}) ∈ U) → e ∉ X))
      ∨ ((M.cl (I \ {e}) ⋖[M] M.cl (X \ {e})) ∧ e ∈ I ∧ M.cl (X \ {e}) ∈ U) := by

  have hss : I \ {e} ⊆ X \ {e} := diff_subset_diff_left hIX
  have hX' : X \ {e} ⊆ M.E := by simpa

  rw [mem_maximals_iff_forall_insert (fun _ _ ht hst ↦ ⟨ht.1.subset hst, hst.trans ht.2⟩)]

  simp only [hI, hIX, and_self, insert_subset_iff, and_true, not_and, true_and, imp_not_comm]

  refine ⟨fun h ↦ ?_, fun h x hxI hi hind ↦ ?_⟩
  · simp only [ExtIndep, insert_subset_iff, hIX, and_true, imp_not_comm, not_or, not_and,
      not_not] at h

    obtain (heI | heI) := em (e ∈ I)
    · rw [extIndep_iff_of_mem he heI] at hI
      obtain (hcl | hcl) := em (M.cl (X \ {e}) ∈ U)
      · simp only [heI, hcl, true_implies, and_self, and_true]
        refine .inr <| U.covBy_of_maximal_cl (M.cl_subset_cl hss) hcl hI.2 fun x ⟨hx, hxcl⟩ ↦ ?_
        specialize h x
        have hxI : x ∉ I := by simpa [hx.2] using not_mem_of_mem_diff_cl ⟨hX' hx, hxcl⟩
        rw [← insert_diff_singleton_comm hx.2, hI.1.insert_indep_iff] at h
        exact (h hxI hx.1).2 <| .inl ⟨hX' hx, hxcl⟩

      simp only [heI, hcl, iff_false, not_true_eq_false, not_false_eq_true, implies_true, and_true,
        and_false, or_false]
      refine (M.cl_subset_cl hss).antisymm (M.cl_subset_cl_of_subset_cl fun x hx ↦
        by_contra fun hxcl ↦ hcl ?_)
      have hxI : x ∉ I := by simpa [hx.2] using not_mem_of_mem_diff_cl ⟨(hX' hx), hxcl⟩
      specialize h x

      simp only [hx.1, ← insert_diff_singleton_comm hx.2, hI.1.insert_indep_iff, mem_diff, hX' hx,
        hxcl, not_false_eq_true, and_self, hx.2, and_true, true_or, true_implies, hxI] at h
      exact U.cl_superset_mem' h.2 (insert_subset hx hss)

    have hXI : M.cl (X \ {e}) = M.cl (I \ {e}) := by
      refine (M.cl_subset_cl hss).antisymm' (M.cl_subset_cl_of_subset_cl fun x hx ↦ ?_)
      rw [hI.diff_singleton_indep.mem_cl_iff', and_iff_right (hX' hx), mem_diff, and_iff_left hx.2,
        diff_singleton_eq_self heI]
      exact fun h' ↦ by_contra fun hxI ↦ (h x hxI hx.1).1 h'
    simp only [heI, not_false_eq_true, diff_singleton_eq_self, hXI, false_iff, not_imp_not,
      true_and, false_and, and_false, or_false]
    intro heX
    rw [extIndep_iff_of_not_mem he heI] at hI
    simpa [heI, hI] using (h e heI heX).2

  obtain (heI | heI) := em (e ∈ I)
  · have hxe : x ≠ e := by rintro rfl; contradiction
    rw [extIndep_iff_of_mem he heI] at hI
    rw [extIndep_iff_of_mem he (.inr heI), ← insert_diff_singleton_comm hxe,
      hI.1.insert_indep_iff_of_not_mem (by simp [hxI, hxe])] at hind
    simp only [hIX heI, heI, true_iff, true_implies, true_and] at h
    obtain (⟨h_eq, -⟩ | ⟨hcv, h⟩) := h
    · exact not_mem_of_mem_diff_cl (h_eq ▸ hind.1) <| by simp [hi, hxe]
    rw [hcv.eq_cl_insert_of_mem_diff ⟨M.mem_cl_of_mem ⟨hi, hxe⟩, hind.1.2⟩,
      cl_insert_cl_eq_cl_insert] at h
    exact hind.2 h

  simp only [heI, not_false_eq_true, diff_singleton_eq_self, false_iff, not_not, false_and,
    and_false, or_false] at h
  obtain (rfl | hne) := eq_or_ne e x
  · rw [extIndep_iff_of_mem he (.inl rfl)] at hind
    simp only [mem_singleton_iff, insert_diff_of_mem, hxI, not_false_eq_true,
      diff_singleton_eq_self, h.1] at hind
    exact hind.2 <| h.2 hi

  rw [extIndep_iff_of_not_mem he heI] at hI
  rw [extIndep_iff_of_not_mem he (by simp [heI, hne]), hI.insert_indep_iff_of_not_mem hxI,
    h.1] at hind
  refine not_mem_of_mem_diff_cl hind ⟨hi, hne.symm⟩

def ModularCut.extendIndepMatroid (U : ModularCut M) (he : e ∉ M.E) : IndepMatroid α where

  E := insert e M.E
  Indep := U.ExtIndep e
  indep_empty := Or.inl M.empty_indep
  indep_subset _ _ := ModularCut.ExtIndep.subset
  indep_aug := by

    -- intro I B hI hInmax hBmax
    -- by_contra! hcon

    -- have hB : U.ExtIndep e B := hBmax.1
    -- have hIeE := hI.diff_singleton_indep.subset_ground
    -- have hBeE := hB.diff_singleton_indep.subset_ground
    -- have hss : B \ {e} ⊆ (I ∪ B) \ {e} :=
    --   diff_subset_diff_left <| subset_union_right I B

    -- have hIBe : I ∪ B ⊆ insert e M.E :=
    --   union_subset hI.subset_insert_ground hB.subset_insert_ground

    -- have hImax : I ∈ maximals (· ⊆ ·) {J | U.ExtIndep e J ∧ J ⊆ I ∪ B} := by
    --   rw [mem_maximals_iff_forall_insert (fun _ _ ht hst ↦ ⟨ht.1.subset hst, hst.trans ht.2⟩),
    --     and_iff_right hI, and_iff_right (subset_union_left _ _)]
    --   intro x hxI h'
    --   rw [insert_subset_iff, mem_union, or_iff_right hxI] at h'
    --   exact hcon x ⟨h'.2.1, hxI⟩ h'.1

    -- have hrw : {J | U.ExtIndep e J} = {J | U.ExtIndep e J ∧ J ⊆ insert e M.E} := by
    --   simp only [ext_iff, mem_setOf_eq, iff_self_and]
    --   exact  fun _ ↦ ExtIndep.subset_insert_ground

    -- rw [hrw, U.maximal_extIndep_iff he Subset.rfl hI hI.subset_insert_ground] at hInmax
    -- rw [hrw, U.maximal_extIndep_iff he Subset.rfl hB hB.subset_insert_ground] at hBmax
    -- rw [U.maximal_extIndep_iff he hIBe hI (subset_union_left _ _)] at hImax


    -- obtain (rfl | hU) := U.eq_bot_or_ground_mem
    -- · replace hBmax := show M.Spanning (B \ {e}) ∧ e ∈ B by
    --     simpa [← spanning_iff_cl (S := B \ {e}), he] using hBmax
    --   replace hInmax := show M.Spanning (I \ {e}) → e ∉ I by
    --     simpa [← spanning_iff_cl (S := I \ {e}), he] using hInmax
    --   replace hImax := show M.Spanning (I \ {e}) ∧ e ∈ I by
    --     simpa [hBmax.2, he, hBmax.1.cl_superset_eq hss, ← spanning_iff_cl (S := I \ {e})]
    --       using hImax
    --   exact hInmax hImax.1 hImax.2

    -- simp only [mem_singleton_iff, insert_diff_of_mem, he, not_false_eq_true, diff_singleton_eq_self,
    --   cl_ground, hU, iff_true, mem_insert_iff, or_false, not_true_eq_false, and_false, imp_false,
    --   and_true, not_or, not_and, not_not, mem_union, and_self_left,
    --   ← spanning_iff_cl hBeE, ← spanning_iff_cl hIeE, ← hyperplane_iff_covBy] at hBmax hInmax

    -- obtain (hsp | hsp) := em <| M.Spanning ((I ∪ B) \ {e})
    -- · obtain (heI | heI) := em (e ∈ I)
    --   · replace hImax := show M.Hyperplane (M.cl (I \ {e})) by
    --       simpa [hsp.cl_eq, heI, hU, ← hyperplane_iff_covBy] using hImax
    --     exact hInmax.2 hImax heI
    --   replace hInmax := show ¬ M.Spanning (I \ {e}) by simpa [heI, hU] using hInmax
    --   replace hImax := show M.cl (I \ {e}) = M.E by simpa [hsp.cl_eq, heI, he, hU] using hImax
    --   rw [spanning_iff_cl] at hInmax; contradiction

    -- obtain (⟨hBsp, heB⟩ | ⟨hBhp, heB⟩) := hBmax
    -- · exact hsp <| hBsp.superset hss

    -- have hclcl : M.cl (B \ {e}) = M.cl ((I ∪ B) \ {e}) := by
    --   refine by_contra fun hne ↦ hsp <| ?_
    --   rw [← cl_spanning_iff]
    --   have hssu := (M.cl_subset_cl hss).ssubset_of_ne hne
    --   exact hBhp.spanning_of_ssuperset hssu

    -- rw [extIndep_iff_of_mem he heB] at hB
    -- replace hImax := show M.cl (I \ {e}) = M.cl (B \ {e}) ∧ e ∈ I by
    --   simpa [heB, ← hclcl, hB.2] using hImax

    -- replace hInmax := show ¬M.Hyperplane (M.cl (I \ {e})) by simpa [hImax.2] using hInmax
    -- exact hInmax <| (hImax.1.symm ▸ hBhp)
    sorry

  indep_maximal := by
    intro X hXE I hI hIX
    suffices hJ : ∃ J, I ⊆ J ∧ J ∈ maximals (· ⊆ ·) {K | U.ExtIndep e K ∧ K ⊆ X} by
      obtain ⟨J, hIJ, hJ⟩ := hJ
      refine ⟨J, ?_⟩
      convert maximals_inter_subset (t := {K | I ⊆ K}) ⟨hJ, hIJ⟩ using 2
      ext
      simp only [mem_setOf_eq, mem_inter_iff]
      tauto
    obtain ⟨J, hJ, hIJ⟩ :=
      hI.diff_singleton_indep.subset_basis_of_subset (diff_subset_diff_left hIX)

    have heJ : e ∉ J := sorry
    by_contra! hcon

    obtain (heI | heI) := em' (e ∈ I)
    · have hJ' := hcon J sorry
      rw [maximal_extIndep_iff he hXE (.inl hJ.indep) (hJ.subset.trans (diff_subset _ _)),
        ← hJ.cl_eq_cl, diff_singleton_eq_self heJ, and_iff_right rfl] at hJ'
      simp only [heJ, false_iff, false_and, and_false, or_false, Classical.not_imp, not_not] at hJ'
      rw [hJ.cl_eq_cl] at hJ'
      specialize hcon (insert e J) (by simpa using hIJ)
      rw [maximal_extIndep_iff he hXE _ (insert_subset hJ'.2 sorry)] at hcon
      · simp [hJ'.2, hJ', diff_singleton_eq_self heJ, hJ.cl_eq_cl] at hcon
      rw [extIndep_iff_of_mem he <| .inl rfl]
      simp [heJ, hJ.cl_eq_cl, hJ'.1, hJ.indep]




    obtain (heX | heX) := em' (e ∈ X)
    · rw [diff_singleton_eq_self (not_mem_subset hIX heX)] at hIJ
      rw [diff_singleton_eq_self heX] at hJ
      refine ⟨J, hIJ, ?_⟩
      rw [maximal_extIndep_iff he hXE  (.inl hJ.indep) hJ.subset]
      simp [show e ∉ J from not_mem_subset hJ.subset heX, diff_singleton_eq_self, heX, hJ.cl_eq_cl]

    obtain (heI | heI) := em' (e ∈ I)
    · rw [diff_singleton_eq_self heI] at hIJ
      rw [extIndep_iff_of_not_mem he heI] at hI
      obtain (hXU | hXU) := em (X \ {e} ∈ U)
      · refine ⟨J, hIJ, ?_⟩
        rw [maximal_extIndep_iff he hXE (.inl hJ.indep)]
      sorry
    sorry
  subset_ground := sorry
