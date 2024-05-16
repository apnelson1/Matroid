import Matroid.ForMathlib.Order.Minimal
import Matroid.Modular

open Set Function Set.Notation

variable {α : Type*} {M : Matroid α} {I J B F F' X Y : Set α} {e f : α}



namespace Matroid



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

lemma ModularCut.inter_mem (U : M.ModularCut) (hF : F ∈ U) (hF' : F' ∈ U) (h : M.ModularPair F F') :
    F ∩ F' ∈ U := by
  rw [inter_eq_iInter]
  apply U.iInter_mem
  · simp [hF, hF']
  exact h

def ModularCut.Base (U : M.ModularCut) (e : α) (B : Set α) :=
  M.Base B ∨ (e ∈ B ∧ ∀ F ∈ U, ∃ f ∈ F, M.Base (insert f (B \ {e})))

def ModularCut.Indep (U : M.ModularCut) (e : α) (I : Set α) :=
  M.Indep I ∨ (e ∈ I ∧ M.Indep (I \ {e}) ∧ M.cl (I \ {e}) ∉ U)

def ModularCut.ConIndep (U : M.ModularCut) (I : Set α) :=
  M.Indep I ∧ M.cl I ∉ U

def ModularCut.ConBase (U : M.ModularCut) (B : Set α) :=
  (M.Base B ∧ (U : Set (Set α)) = ∅) ∨
    ((U : Set (Set α)).Nonempty ∧ ∀ F ∈ U, ∃ f ∈ F, M.Base (insert f B))





    -- by_contra! hcon



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

theorem ModularCut.ExtIndep.or' {U : M.ModularCut} (hI : U.ExtIndep e I) (he : e ∉ M.E) :
    (M.Indep I ∧ e ∉ I) ∨ (∃ I₀, M.Indep I₀ ∧ M.cl I₀ ∉ U ∧ e ∉ I₀ ∧ I = insert e I₀) := sorry

lemma ModularCut.extIndep_iff_of_mem {U : M.ModularCut} (he : e ∉ M.E) (heI : e ∈ I) :
    U.ExtIndep e I ↔ (∃ I₀, M.Indep I₀ ∧ M.cl I₀ ∉ U ∧ e ∉ I₀ ∧ I = insert e I₀) := sorry

lemma ModularCut.extIndep_iff_of_not_mem {U : M.ModularCut} (he : e ∉ M.E) (heI : e ∉ I) :
    U.ExtIndep e I ↔ M.Indep I := sorry

lemma ModularCut.ExtIndep.subset {U : M.ModularCut} (h : U.ExtIndep e I) (hJI : J ⊆ I) :
    U.ExtIndep e J := by
  sorry

lemma ModularCut.extIndep_insert_iff {U : M.ModularCut} (he : e ∉ M.E) :
    U.ExtIndep e (insert e I) ↔ M.Indep I ∧ M.cl I ∉ U := by
sorry

lemma ModularCut.ground_mem {U : M.ModularCut} (h : (U : Set (Set α)).Nonempty) : M.E ∈ U := sorry

lemma ModularCut.ExtIndep.diff_singleton_indep {U : M.ModularCut} (h : U.ExtIndep e I) :
    M.Indep (I \ {e}) := by
  obtain (h | h) := h; exact h.diff _; exact h.1

theorem ModularCut.extIndep_iff {U : M.ModularCut} (he : e ∉ M.E) :
    U.ExtIndep e I ↔ (M.Indep I ∧ e ∉ I) ∨ (M.Indep (I \ {e}) ∧ M.cl (I \ {e}) ∉ U ∧ e ∈ I) := by
  refine ⟨fun h ↦ h.or he, ?_⟩
  rintro (h | h)
  · exact .inl h.1
  exact .inr ⟨h.1, h.2.1⟩

def ModularCut.extendIndepMatroid (U : ModularCut M) (he : e ∉ M.E) : IndepMatroid α where

  E := insert e M.E
  Indep := U.ExtIndep e
  indep_empty := Or.inl M.empty_indep
  indep_subset _ _ := ModularCut.ExtIndep.subset



    -- easy to fix
    -- obtain (heI | heI) := em (e ∈ I)
    -- · refine .inr ⟨hJ.1.subset (diff_subset_diff_left hIJ), fun hI ↦ hJ.2 ?_⟩
    --   exact U.cl_superset_mem' hI (diff_subset_diff_left hIJ)
    -- exact .inl (hJ.1.subset (subset_diff.2 ⟨hIJ, by simpa⟩))
  indep_aug := by

    rintro I B hI hInotmax hB
    have ⟨hBi, hBins⟩ := (mem_maximals_iff_forall_insert (fun _ _ ↦ ExtIndep.subset)).1 hB
    simp only [mem_maximals_iff, mem_setOf_eq, and_iff_right hBi] at hB
    rw [mem_maximals_iff_forall_insert (fun _ _ ↦ ExtIndep.subset), and_iff_right hI] at hInotmax
    push_neg at hInotmax


    -- split into cases depending on why `B` is extension-independent.
    obtain (⟨hBi, heB⟩ | ⟨B, hB, hBU, heB, rfl⟩) := hBi.or' he
    · -- Case where `B` is a base of `M`.
      replace hBi := hBi.base_of_maximal (fun J hJ ↦ hB (.inl hJ))

      -- `I \ {e}` is not a base; if it were, we wouldn't have been able to extend `I`.
      have hInb : ¬ M.Base (I \ {e}) := by
        intro hIb
        obtain ⟨x, hxI, hIx⟩ := hInotmax
        obtain (rfl | hne) := eq_or_ne e x
        · refine hBins e heB (.inr ⟨hBi.indep.subset (by simp), (fun hBU ↦ ?_)⟩)
          rw [diff_singleton_eq_self hxI] at hIb
          rw [U.extIndep_insert_iff he, hIb.cl_eq] at hIx
          exact hIx.2 <| U.ground_mem ⟨_, hBU⟩

        have hIex := (hIb.eq_of_subset_indep hIx.diff_singleton_indep
          (diff_subset_diff_left (subset_insert _ _)))
        rw [← insert_diff_singleton_comm hne.symm] at hIex
        exact hxI (hIex.symm.subset <| .inl rfl).1

      -- Therefore there is some `x ∈ B \ I` for which `I ∪ {x}` is independent.
      obtain ⟨x, hx, hIx⟩ := hI.diff_singleton_indep.exists_insert_of_not_base hInb hBi
      have hne : x ≠ e := by rintro rfl; simp [heB] at hx

      -- Now split into cases depending on why `I` is extension-independent.
      obtain (⟨hI, heI⟩ | ⟨I, hIi, hIU, heI, rfl⟩) := hI.or' he
      · -- If `I` is independent, we win by augmenting using `x`.
        exact ⟨x, by simpa [hne] using hx, .inl <| diff_singleton_eq_self heI ▸ hIx⟩

      -- Otherwise, replace `I` with `I ∪ {e}` everywhere, where `I` is `M`-independent
      -- and `M.cl I ∉ U`.
      simp only [mem_singleton_iff, insert_diff_of_mem, diff_singleton_eq_self heI] at hIx

      by_contra! hcon
      simp_rw [mem_diff, mem_insert_iff, not_or, and_imp, insert_comm, extIndep_insert_iff he,
        not_and, not_not] at hcon
      replace hcon := fun x hx ↦ hcon x hx (by rintro rfl; contradiction)
      have hxBI : x ∈ B \ I := by simpa [hne] using hx

      -- If `I ∪ {x}` is a base, then since `I ∪ {e}` is not maximally extension-indep,
      -- there is some `y` outside the span of `I` for which `cl (I ∪ {y}) ∉ U`.
      -- But `cl (I ∪ {y}) = M.E = cl (I ∪ {x})`, so this contradicts the choice of `x`.
      obtain (hIxb | hIxnb) := em (M.Base (insert x I))
      · simp_rw [insert_comm, extIndep_insert_iff he, mem_insert_iff, not_or] at hInotmax
        obtain ⟨y, ⟨hye, hyI⟩, hIy, hIyU⟩ := hInotmax
        have hyxI : y ∉ insert x I := by
          rintro (rfl | hyI)
          · exact hIyU <| hcon y hx.1 hyI hIx
          contradiction
        have hyIb := hIxb.exchange_base_of_indep (e := x) (f := y) hyxI
        simp only [mem_singleton_iff, insert_diff_of_mem, diff_singleton_eq_self hxBI.2, hIy,
          true_implies] at hyIb
        rw [hyIb.cl_eq, ← hIxb.cl_eq] at hIyU
        exact hIyU <| hcon x hxBI.1 hxBI.2 hIx

      -- If `I ∪ {x}` isn't a base, then there is some `y ∈ B` outside the span of `I ∪ {x}`.
      -- But now (the closures of `I ∪ {x}` and `I ∪ {y}`) are a modular pair contained in `U`,
      -- and we can contradict `cl I ∉ U`.
      obtain ⟨y, hy, hyxI⟩ := hIx.exists_insert_of_not_base hIxnb hBi
      simp only [mem_diff, mem_insert_iff, not_or] at hy
      have hmod := U.inter_mem (hcon x hxBI.1 hxBI.2 hIx)
        (hcon y hy.1 hy.2.2 (hyxI.subset (insert_subset_insert (subset_insert _ _)))) ?_
      · rw [← Indep.cl_inter_eq_inter_cl, inter_insert_of_not_mem (by simpa using hy.2),
          inter_eq_self_of_subset_right (subset_insert _ _)] at hmod
        · contradiction
        simpa [union_eq_self_of_subset_right (subset_insert _ _)]
      apply ModularPair.cl_cl
      apply Indep.modularPair_of_union
      simpa [union_eq_self_of_subset_right (subset_insert _ _)]
    rw [extIndep_insert_iff he] at hBi

  -- Now consider the case where `B` has the form `B₀ ∪ {e}` with `B₀` independent and `cl B₀ ∉ U`.














  indep_maximal := sorry
  subset_ground := sorry


      -- simp only [mem_diff, U.extIndep_iff he, mem_insert_iff, heI, or_true, not_true_eq_false,
      --   and_false, and_true, false_or, not_and, not_not, and_imp] at hcon



        -- have := U.cl_superset_mem' ?_ (show I ⊆ J \ {e} by sorry)


      -- obtain (hI | hI) := hI
      -- · -- `B` is a base and `I` is independent.



      --   ·
      --   -- have hI' : ¬ M.Base I := by
      --   --   obtain ⟨J, (hJ | hJ), hIJ⟩ := hInotmax
      --   --   · sorry --- easy


      --   -- have := hI.exists_insert_of_not_base ?_ hB
      -- sorry




    -- obtain (hI | hI) := hI
    -- · obtain ⟨(hB | hB), hBmax⟩ := hB
    --   · -- case where `I,B` are independent.



    -- rintro (hBi | ⟨hBi, hBU⟩) hI'
    -- ·

-- theorem ModularCut.conIndep_iff_subset_conBase (U : M.ModularCut)
--     {I : Set α} : U.ConIndep I ↔ ∃ B, U.ConBase B ∧ I ⊆ B := by

--   simp_rw [ModularCut.ConIndep, ModularCut.ConBase]
--   obtain (hU | hU) := (U : Set (Set α)).eq_empty_or_nonempty
--   · have h : ∀ F, F ∉ U := fun F (hF : F ∈ (U : Set (Set α))) ↦ by simp [hU] at hF
--     simp [h, hU, indep_iff]
--   simp only [hU.ne_empty, and_false, hU, true_and, false_or]
--   refine ⟨fun ⟨hI, hIU⟩ ↦ ?_, fun h ↦ ?_⟩
--   · obtain ⟨B, hB, hIB⟩ := hI.exists_base_superset
--     simp_rw [and_comm]
--     by_contra! hcon
--     -- rw [and_comm, not_exists] at hcon
--     -- have hx : ∀ x ∈ B \ I, ∃ F ∈ U, ∀ f ∈ F, ¬ M.Base (insert f (B \ {x})) :=
--     --   fun x hx ↦ hcon (B \ {x}) (subset_diff_singleton hIB hx.2)
--     have hdiff : ∀ x ∈ B \ I, M.cl (B \ {x}) ∈ U := by
--       intro x hx
--       obtain ⟨F, hFU, hF⟩ := hcon (B \ {x}) (subset_diff_singleton hIB hx.2)
--       refine U.cl_superset_mem hFU (fun f hf ↦ ?_)
--       rw [(hB.indep.diff {x}).mem_cl_iff', and_iff_right ((U.flat_of_mem hFU).subset_ground hf)]
--       have hfx : f ≠ x := by
--         rintro rfl; simpa [insert_eq_of_mem hx.1, hB] using hF f hf
--       rw [mem_diff, mem_singleton_iff, and_iff_left hfx]
--       exact fun hi ↦ by_contra fun hfB ↦ hF f hf <| hB.exchange_base_of_indep hfB hi
--     have _ : Nonempty ↑(B \ I) := by
--       rw [nonempty_iff_ne_empty', Ne, diff_eq_empty]; intro hBI
--       rw [hIB.antisymm hBI, hB.cl_eq] at hIU
--       obtain ⟨F, hF⟩ := hU
--       exact hIU <| U.superset_mem hF M.ground_flat (U.flat_of_mem hF).subset_ground

--     have h_inter := U.iInter_mem (Fs := fun x : ↑(B \ I) ↦ M.cl (B \ {x.1}))
--     simp only [Subtype.forall, iInter_coe_set, iff_true_intro hdiff, true_imp_iff] at h_inter
--     specialize h_inter ⟨B, hB, ?_⟩
--     · simp only [Subtype.forall, mem_diff, and_imp]
--       intro a haB haI
--       refine (hB.indep.inter_left _).basis_of_subset_of_subset_cl (inter_subset_left _ _)
--         (M.cl_subset_cl (subset_inter ?_ (diff_subset _ _)))
--       exact M.subset_cl _ ((diff_subset _ _).trans hB.subset_ground)


--     rw [biInter_eq_iInter, ← M.cl_iInter_eq_biInter_cl_of_iUnion_indep] at h_inter
--     · apply hIU
--       convert h_inter
--       ext x
--       simp

    -- rw [← M.cl_sInter_eq_biInter_cl_of_sUnion_indep] at h_inter
    -- have := M.cl_sInter_eq_biInter_cl_of_sUnion_indep









-- theorem ModularCut.indep_iff_subset_base (U : M.ModularCut) (he : e ∉ M.E) {I : Set α} :
--     U.Indep e I ↔ ∃ B, I ⊆ B ∧ U.Base e B := by
--   simp_rw [ModularCut.Indep, ModularCut.Base]
--   constructor
--   · rintro (hI | ⟨heI, hI, hIU⟩)
--     · obtain ⟨B, hB⟩ := hI.exists_base_superset
--       exact ⟨B, hB.2, .inl hB.1⟩
--     obtain ⟨B', hB', hIB'⟩ := hI.exists_base_superset




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
