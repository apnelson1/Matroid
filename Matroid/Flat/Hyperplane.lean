import Matroid.Flat.Lattice

variable {α : Type*} {M : Matroid α} {I F X Y F' F₀ F₁ F₂ P L H H₁ H₂ H' B C K : Set α} {e f : α}

open Set
namespace Matroid

-- ### Hyperplanes
section Hyperplane

/-- A hyperplane is a maximal set containing no base  -/
def Hyperplane (M : Matroid α) (H : Set α) : Prop :=
  H ⋖[M] M.E

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma Hyperplane.subset_ground (hH : M.Hyperplane H) : H ⊆ M.E :=
  hH.flat_left.subset_ground

lemma hyperplane_iff_covBy : M.Hyperplane H ↔ H ⋖[M] M.E := Iff.rfl

lemma Hyperplane.covBy (h : M.Hyperplane H) : H ⋖[M] M.E :=
  h

lemma Hyperplane.flat (hH : M.Hyperplane H) : M.Flat H :=
  hH.covBy.flat_left

lemma Hyperplane.ssubset_ground (hH : M.Hyperplane H) : H ⊂ M.E :=
  hH.covBy.ssubset

lemma Hyperplane.ssubset_univ (hH : M.Hyperplane H) : H ⊂ univ :=
  hH.ssubset_ground.trans_subset (subset_univ _)

lemma Flat.hyperplane_iff_eRelRk_ground_eq_one (hH : M.Flat H) :
    M.Hyperplane H ↔ M.eRelRk H M.E = 1 := by
  rw [hyperplane_iff_covBy, hH.covBy_iff_eRelRk_eq_one M.ground_flat,
    and_iff_right hH.subset_ground]

lemma Hyperplane.closure_insert_eq (hH : M.Hyperplane H) (heH : e ∉ H)
    (he : e ∈ M.E := by aesop_mat) : M.closure (insert e H) = M.E :=
  hH.covBy.closure_insert_eq ⟨he, heH⟩

lemma Hyperplane.closure_eq_ground_of_ssuperset (hH : M.Hyperplane H) (hX : H ⊂ X)
    (hX' : X ⊆ M.E := by aesop_mat) : M.closure X = M.E := by
  obtain ⟨e, heX, heH⟩ := exists_of_ssubset hX
  exact (M.closure_subset_ground _).antisymm ((hH.closure_insert_eq heH (hX' heX)).symm.trans_subset
    (M.closure_subset_closure (insert_subset heX hX.subset)))

lemma Hyperplane.spanning_of_ssuperset (hH : M.Hyperplane H) (hX : H ⊂ X)
    (hXE : X ⊆ M.E := by aesop_mat) :
    M.Spanning X := by rw [spanning_iff_closure_eq, hH.closure_eq_ground_of_ssuperset hX]

lemma Hyperplane.not_spanning (hH : M.Hyperplane H) : ¬M.Spanning H := by
  rw [hH.flat.spanning_iff]; exact hH.ssubset_ground.ne

lemma Hyperplane.flat_superset_eq_ground (hH : M.Hyperplane H) (hF : M.Flat F) (hHF : H ⊂ F) :
    F = M.E := by rw [← hF.closure, hH.closure_eq_ground_of_ssuperset hHF]

lemma hyperplane_iff_maximal_proper_flat :
    M.Hyperplane H ↔ Maximal (fun X ↦ M.Flat X ∧ X ⊂ M.E) H := by
  simp_rw [hyperplane_iff_covBy, covBy_iff, and_iff_right M.ground_flat, maximal_subset_iff,
    and_assoc, and_congr_right_iff, or_iff_not_imp_right]
  exact fun _ _ ↦ ⟨fun h K hK hHK ↦ (h K hK.1 hHK hK.2.subset hK.2.ne).symm,
    fun h F hF hHF _ hne ↦ Eq.symm <| h ⟨hF, hF.subset_ground.ssubset_of_ne hne⟩ hHF⟩

lemma hyperplane_iff_maximal_nonspanning :
    M.Hyperplane H ↔ Maximal (fun X ↦ ¬ M.Spanning X ∧ X ⊆ M.E) H := by
  rw [hyperplane_iff_maximal_proper_flat, iff_comm]
  refine maximal_iff_maximal_of_imp_of_forall
    (fun F hF ↦ ⟨fun hFs ↦ hF.2.ne (hF.1.eq_ground_of_spanning hFs), hF.2.subset⟩)
    (fun S ⟨hS, hSE⟩ ↦ ⟨M.closure S, M.subset_closure S, M.closure_flat S,
      (M.closure_subset_ground _).ssubset_of_ne ?_⟩)
  rwa [spanning_iff, and_iff_left hSE] at hS

@[simp] lemma compl_cocircuit_iff_hyperplane (hH : H ⊆ M.E := by aesop_mat) :
    M.Cocircuit (M.E \ H) ↔ M.Hyperplane H := by
  rw [cocircuit_iff_minimal_compl_nonspanning', hyperplane_iff_maximal_nonspanning, iff_comm]

  have h_image := image_antitone_setOf_maximal_mem (f := fun X ↦ M.E \ X)
    (s := {X | ¬ M.Spanning X ∧ X ⊆ M.E}) (fun X Y hX hY ↦ sdiff_le_sdiff_iff_le hX.2 hY.2)

  have h_inj : InjOn (M.E \ ·) {X | X ⊆ M.E} := fun X hX Y hY h_eq ↦ eq_of_sdiff_eq_sdiff hX hY h_eq

  convert Set.ext_iff.1 h_image (M.E \ H) using 1
  · exact Iff.symm <| h_inj.mem_image_iff (s := {X | X ⊆ M.E}) (fun _ h ↦ h.prop.2) hH

  rw [iff_comm]
  apply minimal_iff_minimal_of_imp_of_forall
  · simp only [mem_image, mem_setOf_eq, and_imp]
    exact fun X hX hXE ↦ ⟨M.E \ X, ⟨hX, diff_subset⟩, by simp [inter_eq_self_of_subset_right hXE]⟩

  simp only [le_eq_subset, mem_image, mem_setOf_eq, and_imp]
  rintro _ ⟨Y, ⟨hYsp, hYE⟩, rfl⟩
  refine ⟨_, rfl.subset, ?_, diff_subset⟩
  simpa [inter_eq_self_of_subset_right hYE]

@[simp] lemma compl_hyperplane_iff_cocircuit (h : K ⊆ M.E := by aesop_mat) :
    M.Hyperplane (M.E \ K) ↔ M.Cocircuit K := by
  rw [← compl_cocircuit_iff_hyperplane, diff_diff_right, diff_self, empty_union, inter_comm,
    inter_eq_left.mpr h]

lemma Hyperplane.compl_cocircuit (hH : M.Hyperplane H) : M.Cocircuit (M.E \ H) :=
  (compl_cocircuit_iff_hyperplane hH.subset_ground).mpr hH

lemma Cocircuit.compl_hyperplane {K : Set α} (hK : M.Cocircuit K) : M.Hyperplane (M.E \ K) :=
  (compl_hyperplane_iff_cocircuit hK.subset_ground).mpr hK

lemma univ_not_hyperplane (M : Matroid α) : ¬M.Hyperplane univ :=
  fun h ↦ h.ssubset_univ.ne rfl

lemma Hyperplane.eq_of_subset (h₁ : M.Hyperplane H₁) (h₂ : M.Hyperplane H₂) (h : H₁ ⊆ H₂) :
    H₁ = H₂ :=
  (h₁.covBy.eq_or_eq h₂.flat h h₂.subset_ground).elim Eq.symm fun h' ↦
    (h₂.ssubset_ground.ne h').elim

lemma Hyperplane.not_ssubset (h₁ : M.Hyperplane H₁) (h₂ : M.Hyperplane H₂) : ¬H₁ ⊂ H₂ :=
  fun hss ↦ hss.ne (h₁.eq_of_subset h₂ hss.subset)

lemma Hyperplane.inter_ssubset_left_of_ne (h₁ : M.Hyperplane H₁) (h₂ : M.Hyperplane H₂)
    (hne : H₁ ≠ H₂) : H₁ ∩ H₂ ⊂ H₁ := by
  refine inter_subset_left.ssubset_of_ne fun h_eq ↦ hne <| h₁.eq_of_subset h₂ ?_
  rw [← h_eq]
  exact inter_subset_right

lemma Hyperplane.inter_ssubset_right_of_ne (h₁ : M.Hyperplane H₁) (h₂ : M.Hyperplane H₂)
    (hne : H₁ ≠ H₂) : H₁ ∩ H₂ ⊂ H₂ := by
  rw [inter_comm]; exact h₂.inter_ssubset_left_of_ne h₁ hne.symm

lemma Base.hyperplane_of_closure_diff_singleton (hB : M.Base B) (heB : e ∈ B) :
    M.Hyperplane (M.closure (B \ {e})) := by
  rw [hyperplane_iff_covBy, Flat.covBy_iff_eq_closure_insert (M.closure_flat _)]
  refine ⟨e, ⟨hB.subset_ground heB, ?_⟩, ?_⟩
  · rw [(hB.indep.diff {e}).not_mem_closure_iff (hB.subset_ground heB)]
    simpa [insert_eq_of_mem heB] using hB.indep
  simpa [insert_eq_of_mem heB] using hB.closure_eq.symm

lemma Hyperplane.ssuperset_eq_univ_of_flat (hH : M.Hyperplane H) (hF : M.Flat F) (h : H ⊂ F) :
    F = M.E :=
  hH.covBy.eq_of_ssubset_of_subset hF h hF.subset_ground

lemma Hyperplane.closure_insert_eq_univ (hH : M.Hyperplane H) (he : e ∈ M.E \ H) :
    M.closure (insert e H) = M.E := by
  refine hH.ssuperset_eq_univ_of_flat (M.closure_flat _)
    ((ssubset_insert he.2).trans_subset (M.subset_closure _ ?_))
  rw [insert_eq, union_subset_iff, singleton_subset_iff]
  exact ⟨he.1, hH.subset_ground⟩

lemma exists_hyperplane_sep_of_not_mem_closure (h : e ∈ M.E \ M.closure X)
    (hX : X ⊆ M.E := by aesop_mat) : ∃ H, M.Hyperplane H ∧ X ⊆ H ∧ e ∉ H := by
  obtain ⟨I, hI⟩ := M.exists_basis X
  rw [← hI.closure_eq_closure, mem_diff, hI.indep.not_mem_closure_iff] at h
  obtain ⟨B, hB, heIB⟩ := h.2.1.exists_base_superset
  rw [insert_subset_iff] at heIB
  refine ⟨_, hB.hyperplane_of_closure_diff_singleton heIB.1, ?_, ?_⟩
  · exact hI.subset_closure.trans (M.closure_subset_closure (subset_diff_singleton heIB.2 h.2.2))
  exact hB.indep.not_mem_closure_diff_of_mem heIB.1

lemma closure_eq_sInter_hyperplanes (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    M.closure X = ⋂₀ {H | M.Hyperplane H ∧ X ⊆ H} ∩ M.E := by
  refine subset_antisymm (subset_inter ?_ (M.closure_subset_ground _)) ?_
  · rw [subset_sInter_iff]
    rintro H ⟨hH, hXH⟩
    exact hH.flat.closure_subset_of_subset hXH
  rintro e ⟨heH, heE⟩
  refine by_contra fun hx ↦ ?_
  obtain ⟨H, hH, hXH, heH'⟩ := exists_hyperplane_sep_of_not_mem_closure ⟨heE, hx⟩
  exact heH' (heH H ⟨hH, hXH⟩)

lemma flat_iff_eq_sInter_hyperplanes : M.Flat F ↔
  ∃ Hs : Set (Set α), (∀ H ∈ Hs, M.Hyperplane H) ∧ F = (⋂₀ Hs) ∩ M.E := by
  refine ⟨fun h ↦ ⟨{H | M.Hyperplane H ∧ F ⊆ H}, by simp (config := {contextual := true}), ?_⟩, ?_⟩
  · rw [← M.closure_eq_sInter_hyperplanes F, h.closure]
  rintro ⟨Hs, hHs, rfl⟩
  exact Flat.sInter_inter_ground (fun H hH ↦ (hHs H hH).flat)

lemma Flat.eq_sInter_hyperplanes_of_ne_ground (hF : M.Flat F) (hFE : F ≠ M.E) :
    ∃ (Hs : Set (Set α)), Hs.Nonempty ∧ (∀ H ∈ Hs, M.Hyperplane H) ∧ F = ⋂₀ Hs := by
  obtain ⟨Hs, hHs, rfl⟩ := flat_iff_eq_sInter_hyperplanes.1 hF
  obtain rfl | hne := Hs.eq_empty_or_nonempty
  · simp at hFE
  refine ⟨Hs, hne, hHs, inter_eq_left.2 ?_⟩
  exact (sInter_subset_of_mem hne.some_mem).trans (hHs _ hne.some_mem).subset_ground

lemma mem_closure_iff_forall_hyperplane (hX : X ⊆ M.E := by aesop_mat)
    (he : e ∈ M.E := by aesop_mat) : e ∈ M.closure X ↔ ∀ H, M.Hyperplane H → X ⊆ H → e ∈ H := by
  simp_rw [← M.closure_inter_ground X,
    M.closure_eq_sInter_hyperplanes _ (inter_subset_left.trans hX), mem_inter_iff, and_iff_left he,
    mem_sInter, mem_setOf_eq, and_imp]
  exact ⟨fun h H hH hXH ↦ h _ hH (inter_subset_left.trans hXH),
    fun h H hH hXH ↦ h H hH (by rwa [inter_eq_self_of_subset_left hX] at hXH )⟩

lemma mem_dual_closure_iff_forall_circuit (hX : X ⊆ M.E := by aesop_mat)
  (he : e ∈ M.E := by aesop_mat) :
    e ∈ M✶.closure X ↔ ∀ C, M.Circuit C → e ∈ C → (X ∩ C).Nonempty := by
  rw [← dual_dual M]
  simp_rw [← cocircuit_def, dual_dual M, mem_closure_iff_forall_hyperplane (M := M✶) hX he]
  refine ⟨fun h C hC heC ↦ by_contra fun hne ↦ ?_, fun h H hH hXE ↦ by_contra fun he' ↦ ?_⟩
  · rw [nonempty_iff_ne_empty, not_not, ← disjoint_iff_inter_eq_empty] at hne
    exact (h _ hC.compl_hyperplane (subset_diff.mpr ⟨hX, hne⟩)).2 heC
  obtain ⟨f, hf⟩ := h _ hH.compl_cocircuit ⟨he, he'⟩
  exact hf.2.2 (hXE hf.1)

lemma Flat.subset_hyperplane_of_ne_ground (hF : M.Flat F) (h : F ≠ M.E) :
    ∃ H, M.Hyperplane H ∧ F ⊆ H := by
  obtain ⟨e, heE, heF⟩ := exists_of_ssubset (hF.subset_ground.ssubset_of_ne h)
  rw [← hF.closure] at heF
  obtain ⟨H, hH, hFH, -⟩ := exists_hyperplane_sep_of_not_mem_closure ⟨heE, heF⟩
  exact ⟨H, hH, hFH⟩

lemma subset_hyperplane_iff_closure_ne_ground (hY : Y ⊆ M.E := by aesop_mat) :
    M.closure Y ≠ M.E ↔ ∃ H, M.Hyperplane H ∧ Y ⊆ H := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨H, hH, hYH⟩ := (M.closure_flat Y).subset_hyperplane_of_ne_ground h
    exact ⟨H, hH, (M.subset_closure Y).trans hYH⟩
  rintro ⟨H, hH, hYH⟩ hY
  refine hH.ssubset_ground.not_subset ?_
  rw [← hH.flat.closure]
  exact hY.symm.trans_subset (M.closure_mono hYH)

lemma Hyperplane.inter_covBy_comm (hH₁ : M.Hyperplane H₁) (hH₂ : M.Hyperplane H₂) :
    M.CovBy (H₁ ∩ H₂) H₁ ↔ M.CovBy (H₁ ∩ H₂) H₂ := by
  obtain (rfl | hne) := eq_or_ne H₁ H₂; simp
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact And.left <| h.covBy_and_covBy_of_covBy_of_ssubset_of_ssubset hH₁.covBy hH₂.flat
      (hH₁.inter_ssubset_right_of_ne hH₂ hne) hH₂.ssubset_ground
  exact And.left <| h.covBy_and_covBy_of_covBy_of_ssubset_of_ssubset hH₂.covBy hH₁.flat
    (hH₁.inter_ssubset_left_of_ne hH₂ hne) (hH₁.ssubset_ground)

lemma Hyperplane.basis_hyperplane_delete (hH : M.Hyperplane H) (hI : M.Basis I H) :
    (M ＼ (H \ I)).Hyperplane I := by
  obtain ⟨e, he, heH⟩ := exists_of_ssubset hH.ssubset_ground
  have hB : M.Base (insert e I) := by
    refine Indep.base_of_spanning ?_ ?_
    · rwa [hI.indep.insert_indep_iff_of_not_mem (not_mem_subset hI.subset heH),
        hI.closure_eq_closure, hH.flat.closure, mem_diff, and_iff_left heH]
    rw [spanning_iff_closure_eq, closure_insert_congr_right hI.closure_eq_closure,
      hH.closure_insert_eq heH he]
  convert Base.hyperplane_of_closure_diff_singleton (B := insert e I) (e := e) ?_ (.inl rfl)
  · simp only [mem_singleton_iff, insert_diff_of_mem, not_mem_subset hI.subset heH,
    not_false_eq_true, diff_singleton_eq_self, delete_closure_eq]
    rw [disjoint_sdiff_right.sdiff_eq_left, hI.closure_eq_closure, hH.flat.closure,
      diff_diff_cancel_left]
    exact hI.subset
  simp only [delete_base_iff]
  refine hB.indep.basis_of_forall_insert ?_ fun x ⟨⟨hxE, _⟩, hx⟩ ↦ hB.insert_dep ⟨hxE, hx⟩
  suffices insert e I ∩ (H \ I) = ∅ by simpa [insert_subset_iff, he, heH, subset_diff,
    hI.indep.subset_ground, disjoint_iff_inter_eq_empty]
  rw [insert_inter_of_not_mem (by simp [heH])]
  simp

lemma Hyperplane.basis_hyperplane_restrict (hH : M.Hyperplane H) (hI : M.Basis I H) :
    (M ↾ (I ∪ (M.E \ H))).Hyperplane I := by
  convert hH.basis_hyperplane_delete hI using 1
  rw [delete_eq_restrict, diff_diff_right, inter_eq_self_of_subset_right hI.indep.subset_ground,
    union_comm]

lemma Hyperplane.eRk_add_one_eq (hH : M.Hyperplane H) : M.eRk H + 1 = M.eRank := by
  rw [← hH.covBy.eRk_eq, eRank_def]

lemma Hyperplane.insert_base_of_basis (hH : M.Hyperplane H) (hI : M.Basis I H) (he : e ∈ M.E \ H) :
    M.Base (insert e I) := by
  simpa using hH.covBy.insert_basis hI he

lemma Hyperplane.exists_insert_base_of_basis (hH : M.Hyperplane H) (hI : M.Basis I H) :
    ∃ e ∈ M.E \ H, M.Base (insert e I) := by
  obtain ⟨e, he⟩ := exists_of_ssubset hH.ssubset_ground
  exact ⟨e, he, hH.insert_base_of_basis hI he⟩

lemma Hyperplane.inter_hyperplane_spanning_restrict {S : Set α} (hH : M.Hyperplane H)
    (hS : M.Spanning S) (hcl : H ⊆ M.closure (H ∩ S)) : (M ↾ S).Hyperplane (H ∩ S) := by
  obtain ⟨I, hI⟩ := M.exists_basis (H ∩ S) (inter_subset_left.trans hH.subset_ground)
  have hIS := hI.subset.trans inter_subset_right
  have hIH := hI.subset.trans inter_subset_left
  have hIHb : M.Basis I H :=
    hI.indep.basis_of_subset_of_subset_closure hIH <| by rwa [hI.closure_eq_closure]

  obtain ⟨e, he⟩ : (S \ H).Nonempty
  · rw [nonempty_iff_ne_empty, Ne, diff_eq_empty]
    exact fun hSH ↦ hH.not_spanning <| hS.superset hSH

  have heI : e ∉ I := not_mem_subset hIH.subset he.2

  have heB : (M ↾ S).Base (insert e I)
  · rw [hS.base_restrict_iff, and_iff_left (insert_subset he.1 hIS)]
    exact hH.insert_base_of_basis hIHb ⟨hS.subset_ground he.1, he.2⟩

  have hh := heB.hyperplane_of_closure_diff_singleton (mem_insert _ _)
  simpa only [mem_singleton_iff, insert_diff_of_mem, heI, not_false_eq_true, diff_singleton_eq_self,
    restrict_closure_eq', inter_eq_self_of_subset_left hIS, hIHb.closure_eq_closure,
    hH.flat.closure, diff_eq_empty.2 hS.subset_ground, union_empty] using hh

lemma Spanning.hyperplane_restrict_iff {S : Set α} (hS : M.Spanning S) :
    (M ↾ S).Hyperplane H ↔ M.Hyperplane (M.closure H) ∧ H = M.closure H ∩ S := by
  refine ⟨fun h ↦ ?_, fun ⟨hh, hcl⟩ ↦ ?_⟩
  · obtain ⟨I, hI⟩ := (M ↾ S).exists_basis H h.subset_ground
    obtain ⟨e, he : e ∈ S \ H, heB⟩ := h.exists_insert_base_of_basis hI
    have heI : e ∉ I := not_mem_subset hI.subset he.2
    rw [hS.base_restrict_iff, insert_subset_iff] at heB

    rw [basis_restrict_iff] at hI
    have hh' := heB.1.hyperplane_of_closure_diff_singleton (mem_insert _ _)

    refine ⟨by simpa [heI, hI.1.closure_eq_closure] using hh',
      subset_antisymm (subset_inter (M.subset_closure H hI.1.subset_ground) hI.2) ?_⟩
    nth_rw 2 [← h.flat.closure]
    rw [restrict_closure_eq _ hI.2]
  rw [hcl]
  apply hh.inter_hyperplane_spanning_restrict hS (closure_subset_closure_of_subset_closure ?_)
  rw [← hcl]
  exact M.subset_closure _ (hcl.subset.trans (inter_subset_right.trans hS.subset_ground))

end Hyperplane

lemma Cyclic.compl_flat_dual {A : Set α} (hA : M.Cyclic A) : M✶.Flat (M.E \ A) := by
  rw [flat_iff_eq_sInter_hyperplanes]
  obtain ⟨Cs, rfl, hCs⟩ := hA
  refine ⟨(M.E \ ·) '' Cs, fun C hC ↦ ?_, ?_⟩
  · obtain ⟨H, hH, rfl⟩ := show ∃ x ∈ Cs, M.E \ x = C by simpa only [mem_image] using hC
    rw [← dual_ground, compl_hyperplane_iff_cocircuit, dual_cocircuit_iff]
    exact hCs H hH
  ext e
  simp (config := {contextual := true}) [and_comm (a := e ∈ M.E)]

lemma cyclic_iff_compl_flat_dual {A : Set α} (hA : A ⊆ M.E := by aesop_mat) :
    M.Cyclic A ↔ M✶.Flat (M.E \ A) := by
  refine ⟨Cyclic.compl_flat_dual, fun h ↦ ?_⟩
  simp_rw [flat_iff_eq_sInter_hyperplanes, dual_ground] at h
  obtain ⟨Hs, hHs, h_eq⟩ := h
  apply_fun (M.E \ ·) at h_eq
  rw [diff_diff_cancel_left hA, diff_inter_self_eq_diff, sInter_eq_iInter, diff_iInter] at h_eq
  obtain rfl := h_eq
  have hHs' : ∀ H ∈ Hs, M.Circuit (M.E \ H) := by
    refine fun H hH ↦ ?_
    rw [← M.dual_cocircuit_iff, ← dual_ground,
      compl_cocircuit_iff_hyperplane (show H ⊆ M✶.E from (hHs H hH).subset_ground)]
    exact hHs H hH
  exact ⟨(M.E \ ·) '' Hs, by simp, by simpa⟩

lemma Flat.compl_cyclic_dual (hF : M.Flat F) : M✶.Cyclic (M.E \ F) := by
  rwa [cyclic_iff_compl_flat_dual, dual_dual, dual_ground, diff_diff_cancel_left hF.subset_ground]

lemma flat_dual_iff_compl_cyclic (hF : F ⊆ M.E := by aesop_mat) :
    M✶.Flat F ↔ M.Cyclic (M.E \ F) := by
  rw [cyclic_iff_compl_flat_dual, diff_diff_cancel_left hF]
