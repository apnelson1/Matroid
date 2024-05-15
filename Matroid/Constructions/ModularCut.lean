import Matroid.Modular

open Set Function Set.Notation

namespace Matroid

variable {α : Type*} {M : Matroid α} {F F' X Y : Set α} {e f : α}

structure ModularCut (M : Matroid α) where
  (carrier : Set (Set α))
  (forall_flat' : ∀ F ∈ carrier, M.Flat F)
  (forall_superset : ∀ F F', F ∈ carrier → M.Flat F' → F ⊆ F' → F' ∈ carrier)
  (forall_inter : ∀ xs ⊆ carrier, xs.Nonempty → M.ModularFamily (fun x : xs ↦ x) → ⋂₀ xs ∈ carrier)
  -- (forall_modular : ∀ F F', F ∈ carrier → F' ∈ carrier → M.ModularPair F F' → F ∩ F' ∈ carrier)

instance (M : Matroid α) : SetLike (ModularCut M) (Set α) where
  coe := ModularCut.carrier
  coe_injective' U U' := by cases U; cases U'; simp

lemma ModularCut.flat_of_mem (U : M.ModularCut) (hF : F ∈ U) : M.Flat F :=
    U.forall_flat' F hF

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

def ModularCut.Base (U : M.ModularCut) (e : α) (B : Set α) :=
  M.Base B ∨ (e ∈ B ∧ ∀ F ∈ U, ∃ f ∈ F, M.Base (insert f (B \ {e})))

def ModularCut.Indep (U : M.ModularCut) (e : α) (I : Set α) :=
  M.Indep I ∨ (e ∈ I ∧ M.Indep (I \ {e}) ∧ M.cl (I \ {e}) ∉ U)

def ModularCut.ConIndep (U : M.ModularCut) (I : Set α) :=
  M.Indep I ∧ M.cl I ∉ U

def ModularCut.ConBase (U : M.ModularCut) (B : Set α) :=
  (M.Base B ∧ (U : Set (Set α)) = ∅) ∨
    ((U : Set (Set α)).Nonempty ∧ ∀ F ∈ U, ∃ f ∈ F, M.Base (insert f B))

theorem ModularCut.conIndep_iff_subset_conBase (U : M.ModularCut)
    {I : Set α} : U.ConIndep I ↔ ∃ B, U.ConBase B ∧ I ⊆ B := by

  simp_rw [ModularCut.ConIndep, ModularCut.ConBase]
  obtain (hU | hU) := (U : Set (Set α)).eq_empty_or_nonempty
  · have h : ∀ F, F ∉ U := fun F (hF : F ∈ (U : Set (Set α))) ↦ by simp [hU] at hF
    simp [h, hU, indep_iff]
  simp only [hU.ne_empty, and_false, hU, true_and, false_or]
  refine ⟨fun ⟨hI, hIU⟩ ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨B, hB, hIB⟩ := hI.exists_base_superset
    simp_rw [and_comm]
    by_contra! hcon
    -- rw [and_comm, not_exists] at hcon
    -- have hx : ∀ x ∈ B \ I, ∃ F ∈ U, ∀ f ∈ F, ¬ M.Base (insert f (B \ {x})) :=
    --   fun x hx ↦ hcon (B \ {x}) (subset_diff_singleton hIB hx.2)
    have hdiff : ∀ x ∈ B \ I, M.cl (B \ {x}) ∈ U := by
      intro x hx
      obtain ⟨F, hFU, hF⟩ := hcon (B \ {x}) (subset_diff_singleton hIB hx.2)
      refine U.cl_superset_mem hFU (fun f hf ↦ ?_)
      rw [(hB.indep.diff {x}).mem_cl_iff', and_iff_right ((U.flat_of_mem hFU).subset_ground hf)]
      have hfx : f ≠ x := by
        rintro rfl; simpa [insert_eq_of_mem hx.1, hB] using hF f hf
      rw [mem_diff, mem_singleton_iff, and_iff_left hfx]
      exact fun hi ↦ by_contra fun hfB ↦ hF f hf <| hB.exchange_base_of_indep hfB hi
    have _ : Nonempty ↑(B \ I) := by
      rw [nonempty_iff_ne_empty', Ne, diff_eq_empty]; intro hBI
      rw [hIB.antisymm hBI, hB.cl_eq] at hIU
      obtain ⟨F, hF⟩ := hU
      exact hIU <| U.superset_mem hF M.ground_flat (U.flat_of_mem hF).subset_ground

    have h_inter := U.iInter_mem (Fs := fun x : ↑(B \ I) ↦ M.cl (B \ {x.1}))
    simp only [Subtype.forall, iInter_coe_set, iff_true_intro hdiff, true_imp_iff] at h_inter
    specialize h_inter ⟨B, hB, ?_⟩
    · simp only [Subtype.forall, mem_diff, and_imp]
      intro a haB haI
      refine (hB.indep.inter_left _).basis_of_subset_of_subset_cl (inter_subset_left _ _)
        (M.cl_subset_cl (subset_inter ?_ (diff_subset _ _)))
      exact M.subset_cl _ ((diff_subset _ _).trans hB.subset_ground)


    rw [biInter_eq_iInter, ← M.cl_iInter_eq_biInter_cl_of_iUnion_indep] at h_inter
    · apply hIU
      convert h_inter
      ext x
      simp

    -- rw [← M.cl_sInter_eq_biInter_cl_of_sUnion_indep] at h_inter
    -- have := M.cl_sInter_eq_biInter_cl_of_sUnion_indep









theorem ModularCut.indep_iff_subset_base (U : M.ModularCut) (he : e ∉ M.E) {I : Set α} :
    U.Indep e I ↔ ∃ B, I ⊆ B ∧ U.Base e B := by
  simp_rw [ModularCut.Indep, ModularCut.Base]
  constructor
  · rintro (hI | ⟨heI, hI, hIU⟩)
    · obtain ⟨B, hB⟩ := hI.exists_base_superset
      exact ⟨B, hB.2, .inl hB.1⟩
    obtain ⟨B', hB', hIB'⟩ := hI.exists_base_superset




-- lemma foo (U : ModularCut M) (B : Set α) (he : e ∉ M.E) :
--   B ∈ maximals (· ⊆ ·) {I | M.Indep I ∨ (M.Indep (I \ {e}) ∧ M.cl (I \ {e}) ∉ U)} ↔
--     (M.Base B ∨ e ∈ B ∧ ∀ F ∈ U, ∃ f ∈ F, M.Base (insert f (B \ {e}))) := by
--   simp only [mem_maximals_iff, mem_setOf_eq]
--   refine ⟨?_, fun h ↦ ?_⟩
--   · rintro ⟨(hBi | ⟨hB, hBU⟩), hBmax⟩
--     · exact .inl (hBi.base_of_maximal fun J hJ ↦ hBmax (.inl hJ))
--     obtain (heB | heB) := em' (e ∈ B)
--     · left
--       rw [hBmax (y := insert e B) (.inr ⟨by simpa, by simpa⟩) (subset_insert _ _)] at heB
--       simp at heB
--     refine .inr ⟨heB, fun F hF ↦ ?_⟩

--     by_contra! hcon
--     refine hBU (U.cl_superset_mem hF (fun x hx ↦ by_contra fun hx' ↦ ?_))
--     rw [hB.not_mem_cl_iff ((U.flat_of_mem hF).subset_ground hx)] at hx'

--     obtain (rfl | hne) := eq_or_ne x e
--     · obtain hx'' : M.Indep (insert x B) := by simpa using hx'.1
--       exact he (hx''.subset_ground (.inl rfl))

--     rw [hBmax (y := insert x B) (.inr ⟨?_, fun hBU' ↦ ?_⟩) (subset_insert _ _)] at hx'
--     · exact hne (by simpa using hx'.2)
--     · rw [← insert_diff_singleton_comm hne]; exact hx'.1
--     obtain ⟨y, ⟨-,hyB⟩, hy⟩ := hx'.1.exists_insert_of_not_base (hcon x hx)
--       (M.exists_base.choose_spec)
--     rw [hBmax (y := insert y B) (.inr ⟨hy.subset ?_, fun hyY ↦ ?_⟩) (subset_insert _ _)] at hyB
--     · simp only [mem_insert_iff, mem_diff, true_or, mem_singleton_iff, true_and, not_or, not_not]
--         at hyB
--       obtain rfl := hyB.2
--       exact he <| hy.subset_ground (.inl rfl)
--     · simp only [diff_singleton_subset_iff, insert_comm _ y, insert_comm e, insert_diff_singleton]
--       apply insert_subset_insert
--       exact (subset_insert _ B).trans (subset_insert _ _)
--     sorry
--   sorry



    -- -- obtain ⟨y, -, hy⟩ := hx'.1.exists_insert_of_not_base (hcon x hx) (M.exists_base.choose_spec)
    -- have := hBmax (y := insert x B) (.inr ⟨sorry, ?_⟩) (subset_insert _ _)
    -- refine hcon x hx (hx'.1.base_of_maximal fun J hJ hBJ ↦ ?_)



    -- have := hBmax (y := insert f (B \ {e}))
    -- rw [hB.mem_cl_iff]




    -- by_contra! hcon





def ModularCut.extendIndepMatroid (U : ModularCut M) (he : e ∉ M.E) : IndepMatroid α where
  E := insert e M.E
  Indep I := M.Indep I ∨ (M.Indep (I \ {e}) ∧ M.cl (I \ {e}) ∉ U)
  indep_empty := Or.inl M.empty_indep
  indep_subset := by
    rintro I J (hJ | hJ) hIJ
    · exact .inl <| hJ.subset hIJ
    obtain (heI | heI) := em (e ∈ I)
    · refine .inr ⟨hJ.1.subset (diff_subset_diff_left hIJ), fun hI ↦ hJ.2 ?_⟩
      exact U.cl_superset_mem' hI (diff_subset_diff_left hIJ)
    exact .inl (hJ.1.subset (subset_diff.2 ⟨hIJ, by simpa⟩))
  indep_aug := by
    rintro I B hI hInotmax hB
    simp only [mem_maximals_iff, mem_setOf_eq] at hB
    simp only [mem_maximals_iff, mem_setOf_eq, hI, true_and, not_forall, Classical.not_imp,
      exists_prop, exists_and_left, and_assoc, ← ssubset_iff_subset_ne] at hInotmax
    obtain ⟨J, hJ, hIJ⟩ := hInotmax
    obtain ⟨x, hxJ, hxI⟩ := exists_of_ssubset hIJ

    -- rintro (hBi | ⟨hBi, hBU⟩) hI'
    -- ·
  indep_maximal := _
  subset_ground := _
