import Matroid.Flat.Lattice
import Matroid.ForMathlib.Matroid.Closure

variable {α : Type*} {M : Matroid α} {I F X Y F' F₀ F₁ F₂ P L H H₁ H₂ H' B C K : Set α} {e f : α}

open Set
namespace Matroid

-- ### Hyperplanes
section IsHyperplane

/-- A hyperplane is a maximal set containing no base  -/
def IsHyperplane (M : Matroid α) (H : Set α) : Prop :=
  H ⋖[M] M.E

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma IsHyperplane.subset_ground (hH : M.IsHyperplane H) : H ⊆ M.E :=
  hH.isFlat_left.subset_ground

lemma isHyperplane_iff_covBy : M.IsHyperplane H ↔ H ⋖[M] M.E := Iff.rfl

lemma IsHyperplane.covBy (h : M.IsHyperplane H) : H ⋖[M] M.E :=
  h

lemma IsHyperplane.isFlat (hH : M.IsHyperplane H) : M.IsFlat H :=
  hH.covBy.isFlat_left

lemma IsHyperplane.ssubset_ground (hH : M.IsHyperplane H) : H ⊂ M.E :=
  hH.covBy.ssubset

lemma IsHyperplane.ssubset_univ (hH : M.IsHyperplane H) : H ⊂ univ :=
  hH.ssubset_ground.trans_subset (subset_univ _)

lemma IsFlat.isHyperplane_iff_eRelRk_ground_eq_one (hH : M.IsFlat H) :
    M.IsHyperplane H ↔ M.eRelRk H M.E = 1 := by
  rw [isHyperplane_iff_covBy, hH.covBy_iff_eRelRk_eq_one M.ground_isFlat,
    and_iff_right hH.subset_ground]

lemma IsHyperplane.closure_insert_eq (hH : M.IsHyperplane H) (heH : e ∉ H)
    (he : e ∈ M.E := by aesop_mat) : M.closure (insert e H) = M.E :=
  hH.covBy.closure_insert_eq ⟨he, heH⟩

lemma IsHyperplane.closure_eq_ground_of_ssuperset (hH : M.IsHyperplane H) (hX : H ⊂ X)
    (hX' : X ⊆ M.E := by aesop_mat) : M.closure X = M.E := by
  obtain ⟨e, heX, heH⟩ := exists_of_ssubset hX
  exact (M.closure_subset_ground _).antisymm ((hH.closure_insert_eq heH (hX' heX)).symm.trans_subset
    (M.closure_subset_closure (insert_subset heX hX.subset)))

lemma IsHyperplane.spanning_of_ssuperset (hH : M.IsHyperplane H) (hX : H ⊂ X)
    (hXE : X ⊆ M.E := by aesop_mat) :
    M.Spanning X := by rw [spanning_iff_closure_eq, hH.closure_eq_ground_of_ssuperset hX]

lemma IsHyperplane.not_spanning (hH : M.IsHyperplane H) : ¬M.Spanning H := by
  rw [hH.isFlat.spanning_iff]; exact hH.ssubset_ground.ne

lemma IsHyperplane.isFlat_superset_eq_ground (hH : M.IsHyperplane H) (hF : M.IsFlat F)
    (hHF : H ⊂ F) : F = M.E := by
  rw [← hF.closure, hH.closure_eq_ground_of_ssuperset hHF]

lemma isHyperplane_iff_maximal_proper_isFlat :
    M.IsHyperplane H ↔ Maximal (fun X ↦ M.IsFlat X ∧ X ⊂ M.E) H := by
  simp_rw [isHyperplane_iff_covBy, covBy_iff, and_iff_right M.ground_isFlat, maximal_subset_iff,
    and_assoc, and_congr_right_iff, or_iff_not_imp_right]
  exact fun _ _ ↦ ⟨fun h K hK hHK ↦ (h K hK.1 hHK hK.2.subset hK.2.ne).symm,
    fun h F hF hHF _ hne ↦ Eq.symm <| h ⟨hF, hF.subset_ground.ssubset_of_ne hne⟩ hHF⟩

lemma isHyperplane_iff_maximal_nonspanning :
    M.IsHyperplane H ↔ Maximal (fun X ↦ ¬ M.Spanning X ∧ X ⊆ M.E) H := by
  rw [isHyperplane_iff_maximal_proper_isFlat, iff_comm]
  refine maximal_iff_maximal_of_imp_of_forall
    (fun F hF ↦ ⟨fun hFs ↦ hF.2.ne (hF.1.eq_ground_of_spanning hFs), hF.2.subset⟩)
    (fun S ⟨hS, hSE⟩ ↦ ⟨M.closure S, M.subset_closure S, M.closure_isFlat S,
      (M.closure_subset_ground _).ssubset_of_ne ?_⟩)
  rwa [spanning_iff, and_iff_left hSE] at hS



@[simp] lemma compl_isCocircuit_iff_isHyperplane (hH : H ⊆ M.E := by aesop_mat) :
    M.IsCocircuit (M.E \ H) ↔ M.IsHyperplane H := by
  -- rw [isCocircuit_def, ← minimal_nonempty_cyclic_iff_isCircuit,
  --   isHyperplane_iff_maximal_proper_isFlat, iff_comm]
  -- apply maximal_apply_anti_bijOn_iff (f := fun s ↦ M.E \ s)
  -- · rw [bijOn_iff]
  -- -- refine maximal_apply_anti_iff (fun F ↦ ?_) (fun A hA ↦ ⟨M.E \ A, ?_, ?_⟩) ?_
  -- -- · by_cases hF : F ⊆ M.E

  rw [isCocircuit_iff_minimal_compl_nonspanning', isHyperplane_iff_maximal_nonspanning, iff_comm]

  have h_image := image_antitone_setOf_maximal_mem (f := fun X ↦ M.E \ X)
    (s := {X | ¬ M.Spanning X ∧ X ⊆ M.E}) (fun X Y hX hY ↦ sdiff_le_sdiff_iff_le hX.2 hY.2)

  have h_inj : InjOn (M.E \ ·) {X | X ⊆ M.E} := fun X hX Y hY h_eq ↦ eq_of_sdiff_eq_sdiff hX hY h_eq

  convert Set.ext_iff.1 h_image (M.E \ H) using 1
  · exact Iff.symm <| h_inj.mem_image_iff (s := {X | X ⊆ M.E}) (fun _ h ↦ h.prop.2) hH

  rw [iff_comm]
  apply minimal_iff_minimal_of_imp_of_forall
  · simp only [mem_image, mem_setOf_eq, and_imp]
    exact fun X hX hXE ↦ ⟨M.E \ X, ⟨hX, diff_subset⟩, by simp [inter_eq_self_of_subset_right hXE]⟩

  simp only [le_eq_subset, mem_image, mem_setOf_eq]
  rintro _ ⟨Y, ⟨hYsp, hYE⟩, rfl⟩
  refine ⟨_, rfl.subset, ?_, diff_subset⟩
  simpa [inter_eq_self_of_subset_right hYE]

@[simp] lemma compl_isHyperplane_iff_isCocircuit (h : K ⊆ M.E := by aesop_mat) :
    M.IsHyperplane (M.E \ K) ↔ M.IsCocircuit K := by
  rw [← compl_isCocircuit_iff_isHyperplane, diff_diff_right, diff_self, empty_union, inter_comm,
    inter_eq_left.mpr h]

lemma IsHyperplane.compl_isCocircuit (hH : M.IsHyperplane H) : M.IsCocircuit (M.E \ H) :=
  (compl_isCocircuit_iff_isHyperplane hH.subset_ground).mpr hH

lemma IsCocircuit.compl_isHyperplane {K : Set α} (hK : M.IsCocircuit K) :
    M.IsHyperplane (M.E \ K) :=
  (compl_isHyperplane_iff_isCocircuit hK.subset_ground).mpr hK

lemma univ_not_isHyperplane (M : Matroid α) : ¬M.IsHyperplane univ :=
  fun h ↦ h.ssubset_univ.ne rfl

lemma IsHyperplane.eq_of_subset (h₁ : M.IsHyperplane H₁) (h₂ : M.IsHyperplane H₂) (h : H₁ ⊆ H₂) :
    H₁ = H₂ :=
  (h₁.covBy.eq_or_eq h₂.isFlat h h₂.subset_ground).elim Eq.symm fun h' ↦
    (h₂.ssubset_ground.ne h').elim

lemma IsHyperplane.not_ssubset (h₁ : M.IsHyperplane H₁) (h₂ : M.IsHyperplane H₂) : ¬H₁ ⊂ H₂ :=
  fun hss ↦ hss.ne (h₁.eq_of_subset h₂ hss.subset)

lemma IsHyperplane.inter_ssubset_left_of_ne (h₁ : M.IsHyperplane H₁) (h₂ : M.IsHyperplane H₂)
    (hne : H₁ ≠ H₂) : H₁ ∩ H₂ ⊂ H₁ := by
  refine inter_subset_left.ssubset_of_ne fun h_eq ↦ hne <| h₁.eq_of_subset h₂ ?_
  rw [← h_eq]
  exact inter_subset_right

lemma IsHyperplane.inter_ssubset_right_of_ne (h₁ : M.IsHyperplane H₁) (h₂ : M.IsHyperplane H₂)
    (hne : H₁ ≠ H₂) : H₁ ∩ H₂ ⊂ H₂ := by
  rw [inter_comm]; exact h₂.inter_ssubset_left_of_ne h₁ hne.symm

lemma IsBase.isHyperplane_of_closure_diff_singleton (hB : M.IsBase B) (heB : e ∈ B) :
    M.IsHyperplane (M.closure (B \ {e})) := by
  rw [isHyperplane_iff_covBy, IsFlat.covBy_iff_eq_closure_insert (M.closure_isFlat _)]
  refine ⟨e, ⟨hB.subset_ground heB, ?_⟩, ?_⟩
  · rw [(hB.indep.diff {e}).notMem_closure_iff (hB.subset_ground heB)]
    simpa [insert_eq_of_mem heB] using hB.indep
  simpa [insert_eq_of_mem heB] using hB.closure_eq.symm

lemma IsHyperplane.ssuperset_eq_univ_of_isFlat (hH : M.IsHyperplane H) (hF : M.IsFlat F)
    (h : H ⊂ F) : F = M.E :=
  hH.covBy.eq_of_ssubset_of_subset hF h hF.subset_ground

lemma IsHyperplane.closure_insert_eq_univ (hH : M.IsHyperplane H) (he : e ∈ M.E \ H) :
    M.closure (insert e H) = M.E := by
  refine hH.ssuperset_eq_univ_of_isFlat (M.closure_isFlat _)
    ((ssubset_insert he.2).trans_subset (M.subset_closure _ ?_))
  rw [insert_eq, union_subset_iff, singleton_subset_iff]
  exact ⟨he.1, hH.subset_ground⟩

lemma exists_isHyperplane_sep_of_notMem_closure (h : e ∈ M.E \ M.closure X)
    (hX : X ⊆ M.E := by aesop_mat) : ∃ H, M.IsHyperplane H ∧ X ⊆ H ∧ e ∉ H := by
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  rw [← hI.closure_eq_closure, mem_diff, hI.indep.notMem_closure_iff] at h
  obtain ⟨B, hB, heIB⟩ := h.2.1.exists_isBase_superset
  rw [insert_subset_iff] at heIB
  refine ⟨_, hB.isHyperplane_of_closure_diff_singleton heIB.1, ?_, ?_⟩
  · exact hI.subset_closure.trans (M.closure_subset_closure (subset_diff_singleton heIB.2 h.2.2))
  exact hB.indep.notMem_closure_diff_of_mem heIB.1

lemma closure_eq_sInter_isHyperplane (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    M.closure X = ⋂₀ {H | M.IsHyperplane H ∧ X ⊆ H} ∩ M.E := by
  refine subset_antisymm (subset_inter ?_ (M.closure_subset_ground _)) ?_
  · rw [subset_sInter_iff]
    rintro H ⟨hH, hXH⟩
    exact hH.isFlat.closure_subset_of_subset hXH
  rintro e ⟨heH, heE⟩
  refine by_contra fun hx ↦ ?_
  obtain ⟨H, hH, hXH, heH'⟩ := exists_isHyperplane_sep_of_notMem_closure ⟨heE, hx⟩
  exact heH' (heH H ⟨hH, hXH⟩)

lemma isFlat_iff_eq_sInter_isHyperplanes : M.IsFlat F ↔
  ∃ Hs : Set (Set α), (∀ H ∈ Hs, M.IsHyperplane H) ∧ F = (⋂₀ Hs) ∩ M.E := by
  refine ⟨fun h ↦ ⟨{H | M.IsHyperplane H ∧ F ⊆ H}, by simp +contextual, ?_⟩, ?_⟩
  · rw [← M.closure_eq_sInter_isHyperplane F, h.closure]
  rintro ⟨Hs, hHs, rfl⟩
  exact IsFlat.sInter_inter_ground (fun H hH ↦ (hHs H hH).isFlat)

lemma IsFlat.eq_sInter_isHyperplanes_of_ne_ground (hF : M.IsFlat F) (hFE : F ≠ M.E) :
    ∃ (Hs : Set (Set α)), Hs.Nonempty ∧ (∀ H ∈ Hs, M.IsHyperplane H) ∧ F = ⋂₀ Hs := by
  obtain ⟨Hs, hHs, rfl⟩ := isFlat_iff_eq_sInter_isHyperplanes.1 hF
  obtain rfl | hne := Hs.eq_empty_or_nonempty
  · simp at hFE
  refine ⟨Hs, hne, hHs, inter_eq_left.2 ?_⟩
  exact (sInter_subset_of_mem hne.some_mem).trans (hHs _ hne.some_mem).subset_ground

lemma mem_closure_iff_forall_isHyperplane (hX : X ⊆ M.E := by aesop_mat)
    (he : e ∈ M.E := by aesop_mat) : e ∈ M.closure X ↔ ∀ H, M.IsHyperplane H → X ⊆ H → e ∈ H := by
  simp_rw [← M.closure_inter_ground X,
    M.closure_eq_sInter_isHyperplane _ (inter_subset_left.trans hX), mem_inter_iff,
    and_iff_left he, mem_sInter, mem_setOf_eq, and_imp]
  exact ⟨fun h H hH hXH ↦ h _ hH (inter_subset_left.trans hXH),
    fun h H hH hXH ↦ h H hH (by rwa [inter_eq_self_of_subset_left hX] at hXH )⟩

lemma mem_dual_closure_iff_forall_isCircuit (he : e ∈ M.E := by aesop_mat) :
    e ∈ M✶.closure X ↔ ∀ C, M.IsCircuit C → e ∈ C → (X ∩ C).Nonempty := by
  wlog hXE : X ⊆ M.E generalizing X with aux
  · rw [← closure_inter_ground, dual_ground, aux inter_subset_right]
    refine ⟨fun h C hC heC ↦ (h C hC heC).mono (by tauto_set), fun h C hC heC ↦ ?_⟩
    rw [inter_assoc, inter_eq_self_of_subset_right hC.subset_ground]
    exact h C hC heC
  rw [← dual_dual M]
  simp_rw [← isCocircuit_def, dual_dual M, mem_closure_iff_forall_isHyperplane (M := M✶) hXE he]
  refine ⟨fun h C hC heC ↦ by_contra fun hne ↦ ?_, fun h H hH hXE ↦ by_contra fun he' ↦ ?_⟩
  · rw [nonempty_iff_ne_empty, not_not, ← disjoint_iff_inter_eq_empty] at hne
    exact (h _ hC.compl_isHyperplane (subset_diff.mpr ⟨hXE, hne⟩)).2 heC
  obtain ⟨f, hf⟩ := h _ hH.compl_isCocircuit ⟨he, he'⟩
  exact hf.2.2 (hXE hf.1)

lemma mem_dual_closure_iff_notMem_closure_compl (heX : e ∉ X) (heE : e ∈ M.E := by aesop_mat) :
    e ∈ M✶.closure X ↔ e ∉ M.closure ((M.E \ X) \ {e}) := by
  rw [mem_dual_closure_iff_forall_isCircuit]
  refine ⟨fun h hecl ↦ ?_, fun h C hC heC ↦ by_contra fun he ↦ ?_⟩
  · obtain ⟨C, hCX, hC, heC⟩ := exists_isCircuit_of_mem_closure hecl (by simp)
    rw [insert_diff_singleton, ← insert_diff_of_notMem _ heX, subset_diff] at hCX
    exact (h C hC heC).ne_empty hCX.2.symm.inter_eq
  rw [not_nonempty_iff_eq_empty, ← disjoint_iff_inter_eq_empty] at he
  refine h <| mem_of_mem_of_subset (hC.mem_closure_diff_singleton_of_mem heC) ?_
  exact M.closure_subset_closure <| diff_subset_diff_left <| subset_diff.2
    ⟨hC.subset_ground, he.symm⟩

lemma IsFlat.subset_isHyperplane_of_ne_ground (hF : M.IsFlat F) (h : F ≠ M.E) :
    ∃ H, M.IsHyperplane H ∧ F ⊆ H := by
  obtain ⟨e, heE, heF⟩ := exists_of_ssubset (hF.subset_ground.ssubset_of_ne h)
  rw [← hF.closure] at heF
  obtain ⟨H, hH, hFH, -⟩ := exists_isHyperplane_sep_of_notMem_closure ⟨heE, heF⟩
  exact ⟨H, hH, hFH⟩

lemma subset_isHyperplane_iff_closure_ne_ground (hY : Y ⊆ M.E := by aesop_mat) :
    M.closure Y ≠ M.E ↔ ∃ H, M.IsHyperplane H ∧ Y ⊆ H := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨H, hH, hYH⟩ := (M.closure_isFlat Y).subset_isHyperplane_of_ne_ground h
    exact ⟨H, hH, (M.subset_closure Y).trans hYH⟩
  rintro ⟨H, hH, hYH⟩ hY
  refine hH.ssubset_ground.not_subset ?_
  rw [← hH.isFlat.closure]
  exact hY.symm.trans_subset (M.closure_mono hYH)

lemma IsHyperplane.inter_covBy_comm (hH₁ : M.IsHyperplane H₁) (hH₂ : M.IsHyperplane H₂) :
    M.CovBy (H₁ ∩ H₂) H₁ ↔ M.CovBy (H₁ ∩ H₂) H₂ := by
  obtain (rfl | hne) := eq_or_ne H₁ H₂; simp
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact And.left <| h.covBy_and_covBy_of_covBy_of_ssubset_of_ssubset hH₁.covBy hH₂.isFlat
      (hH₁.inter_ssubset_right_of_ne hH₂ hne) hH₂.ssubset_ground
  exact And.left <| h.covBy_and_covBy_of_covBy_of_ssubset_of_ssubset hH₂.covBy hH₁.isFlat
    (hH₁.inter_ssubset_left_of_ne hH₂ hne) (hH₁.ssubset_ground)

lemma IsHyperplane.isBasis_isHyperplane_delete (hH : M.IsHyperplane H) (hI : M.IsBasis I H) :
    (M ＼ (H \ I)).IsHyperplane I := by
  obtain ⟨e, he, heH⟩ := exists_of_ssubset hH.ssubset_ground
  have hB : M.IsBase (insert e I) := by
    refine Indep.isBase_of_spanning ?_ ?_
    · rwa [hI.indep.insert_indep_iff_of_notMem (notMem_subset hI.subset heH),
        hI.closure_eq_closure, hH.isFlat.closure, mem_diff, and_iff_left heH]
    rw [spanning_iff_closure_eq, closure_insert_congr_right hI.closure_eq_closure,
      hH.closure_insert_eq heH he]
  convert IsBase.isHyperplane_of_closure_diff_singleton (B := insert e I) (e := e) ?_ (.inl rfl)
  · simp only [mem_singleton_iff, insert_diff_of_mem, notMem_subset hI.subset heH,
    not_false_eq_true, diff_singleton_eq_self, delete_closure_eq]
    rw [disjoint_sdiff_right.sdiff_eq_left, hI.closure_eq_closure, hH.isFlat.closure,
      diff_diff_cancel_left]
    exact hI.subset
  simp only [delete_isBase_iff]
  refine hB.indep.isBasis_of_forall_insert ?_ fun x ⟨⟨hxE, _⟩, hx⟩ ↦ hB.insert_dep ⟨hxE, hx⟩
  suffices insert e I ∩ (H \ I) = ∅ by simpa [insert_subset_iff, he, heH, subset_diff,
    hI.indep.subset_ground, disjoint_iff_inter_eq_empty]
  rw [insert_inter_of_notMem (by simp [heH])]
  simp

lemma IsHyperplane.isBasis_isHyperplane_restrict (hH : M.IsHyperplane H) (hI : M.IsBasis I H) :
    (M ↾ (I ∪ (M.E \ H))).IsHyperplane I := by
  convert hH.isBasis_isHyperplane_delete hI using 1
  rw [delete_eq_restrict, diff_diff_right, inter_eq_self_of_subset_right hI.indep.subset_ground,
    union_comm]

lemma IsHyperplane.eRk_add_one_eq (hH : M.IsHyperplane H) : M.eRk H + 1 = M.eRank := by
  rw [← hH.covBy.eRk_eq, eRank_def]

lemma IsHyperplane.insert_isBase_of_isBasis (hH : M.IsHyperplane H) (hI : M.IsBasis I H)
    (he : e ∈ M.E \ H) : M.IsBase (insert e I) := by
  simpa using hH.covBy.insert_isBasis hI he

lemma IsHyperplane.exists_insert_isBase_of_isBasis (hH : M.IsHyperplane H) (hI : M.IsBasis I H) :
    ∃ e ∈ M.E \ H, M.IsBase (insert e I) := by
  obtain ⟨e, he⟩ := exists_of_ssubset hH.ssubset_ground
  exact ⟨e, he, hH.insert_isBase_of_isBasis hI he⟩

lemma IsHyperplane.inter_isHyperplane_spanning_restrict {S : Set α} (hH : M.IsHyperplane H)
    (hS : M.Spanning S) (hcl : H ⊆ M.closure (H ∩ S)) : (M ↾ S).IsHyperplane (H ∩ S) := by
  obtain ⟨I, hI⟩ := M.exists_isBasis (H ∩ S) (inter_subset_left.trans hH.subset_ground)
  have hIS := hI.subset.trans inter_subset_right
  have hIH := hI.subset.trans inter_subset_left
  have hIHb : M.IsBasis I H :=
    hI.indep.isBasis_of_subset_of_subset_closure hIH <| by rwa [hI.closure_eq_closure]

  obtain ⟨e, he⟩ : (S \ H).Nonempty
  · rw [nonempty_iff_ne_empty, Ne, diff_eq_empty]
    exact fun hSH ↦ hH.not_spanning <| hS.superset hSH

  have heI : e ∉ I := notMem_subset hIH.subset he.2

  have heB : (M ↾ S).IsBase (insert e I)
  · rw [hS.isBase_restrict_iff, and_iff_left (insert_subset he.1 hIS)]
    exact hH.insert_isBase_of_isBasis hIHb ⟨hS.subset_ground he.1, he.2⟩

  have hh := heB.isHyperplane_of_closure_diff_singleton (mem_insert _ _)
  simpa only [mem_singleton_iff, insert_diff_of_mem, heI, not_false_eq_true, diff_singleton_eq_self,
    restrict_closure_eq', inter_eq_self_of_subset_left hIS, hIHb.closure_eq_closure,
    hH.isFlat.closure, diff_eq_empty.2 hS.subset_ground, union_empty] using hh

lemma Spanning.isHyperplane_restrict_iff {S : Set α} (hS : M.Spanning S) :
    (M ↾ S).IsHyperplane H ↔ M.IsHyperplane (M.closure H) ∧ H = M.closure H ∩ S := by
  refine ⟨fun h ↦ ?_, fun ⟨hh, hcl⟩ ↦ ?_⟩
  · obtain ⟨I, hI⟩ := (M ↾ S).exists_isBasis H h.subset_ground
    obtain ⟨e, he : e ∈ S \ H, heB⟩ := h.exists_insert_isBase_of_isBasis hI
    have heI : e ∉ I := notMem_subset hI.subset he.2
    rw [hS.isBase_restrict_iff, insert_subset_iff] at heB

    rw [isBasis_restrict_iff] at hI
    have hh' := heB.1.isHyperplane_of_closure_diff_singleton (mem_insert _ _)

    refine ⟨by simpa [heI, hI.1.closure_eq_closure] using hh',
      subset_antisymm (subset_inter (M.subset_closure H hI.1.subset_ground) hI.2) ?_⟩
    nth_rw 2 [← h.isFlat.closure]
    rw [restrict_closure_eq _ hI.2]
  rw [hcl]
  apply hh.inter_isHyperplane_spanning_restrict hS (closure_subset_closure_of_subset_closure ?_)
  rw [← hcl]
  exact M.subset_closure _ (hcl.subset.trans (inter_subset_right.trans hS.subset_ground))



end IsHyperplane
