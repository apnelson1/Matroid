import Matroid.Minor.RelRank
import Matroid.ForMathlib.SetPartition
import Matroid.ForMathlib.ENatTopology

variable {α : Type*} {M : Matroid α} {I F X Y F' F₀ F₁ F₂ P L H H₁ H₂ H' B C K : Set α} {e f : α}

open Set
namespace Matroid

theorem flat_def : M.Flat F ↔ (∀ I X, M.Basis I F → M.Basis I X → X ⊆ F) ∧ F ⊆ M.E :=
  Iff.rfl

theorem Flat.eq_ground_of_spanning (hF : M.Flat F) (h : M.Spanning F) : F = M.E := by
  rw [← hF.cl, h.cl_eq]

theorem Flat.spanning_iff (hF : M.Flat F) : M.Spanning F ↔ F = M.E :=
  ⟨hF.eq_ground_of_spanning, by rintro rfl; exact M.ground_spanning⟩

theorem Flat.iInter {ι : Type*} [Nonempty ι] {Fs : ι → Set α}
    (hFs : ∀ i, M.Flat (Fs i)) : M.Flat (⋂ i, Fs i) := by
  refine' ⟨fun I X hI hIX ↦ subset_iInter fun i ↦ _,
    (iInter_subset _ (Classical.arbitrary _)).trans (hFs _).subset_ground⟩
  obtain ⟨J, hIJ, hJ⟩ := hI.indep.subset_basis_of_subset (hI.subset.trans (iInter_subset _ i))
  refine' (subset_union_right _ _).trans ((hFs i).1 (X := Fs i ∪ X) hIJ _)
  convert hIJ.basis_union (hIX.basis_union_of_subset hIJ.indep hJ) using 1
  rw [← union_assoc, union_eq_self_of_subset_right hIJ.subset]

theorem Flat.inter (hF₁ : M.Flat F₁) (hF₂ : M.Flat F₂) : M.Flat (F₁ ∩ F₂) := by
  rw [inter_eq_iInter]; apply Flat.iInter; simp [hF₁, hF₂]

/-- The intersection of an arbitrary collection of flats with the ground set is a flat.
  `Flat.iInter` is often more convenient, but this works when the collection is empty. -/
theorem Flat.iInter_inter_ground {ι : Type*} {Fs : ι → Set α} (hFs : ∀ i, M.Flat (Fs i)) :
    M.Flat ((⋂ i, Fs i) ∩ M.E) := by
  obtain (hι | hι) := isEmpty_or_nonempty ι
  · simp
  exact (Flat.iInter hFs).inter M.ground_flat

theorem Flat.biInter {ι : Type*} {Fs : ι → Set α} {s : Set ι} (hs : s.Nonempty)
    (hFs : ∀ i ∈ s, M.Flat (Fs i)) : M.Flat (⋂ i ∈ s, Fs i) := by
  rw [biInter_eq_iInter]
  have := hs.to_subtype
  apply Flat.iInter (by simpa)

theorem Flat.biInter_inter_ground {ι : Type*} {Fs : ι → Set α} {s : Set ι}
    (hFs : ∀ i ∈ s, M.Flat (Fs i)) : M.Flat ((⋂ i ∈ s, Fs i) ∩ M.E) := by
  rw [biInter_eq_iInter]
  exact Flat.iInter_inter_ground (by simpa)

theorem Flat.sInter {Fs : Set (Set α)} (hF : Fs.Nonempty) (h : ∀ F ∈ Fs, M.Flat F) :
    M.Flat (⋂₀ Fs) := by
  rw [sInter_eq_iInter]
  have : Nonempty Fs
  · exact Iff.mpr nonempty_coe_sort hF
  exact Flat.iInter (fun ⟨F, hF⟩ ↦ h _ hF)

theorem Flat.sInter_inter_ground {Fs : Set (Set α)} (h : ∀ F ∈ Fs, M.Flat F) :
    M.Flat (⋂₀ Fs ∩ M.E) := by
  rw [sInter_eq_iInter]
  exact Flat.iInter_inter_ground (by simpa)

@[simp] theorem cl_flat (M : Matroid α) (X : Set α) : M.Flat (M.cl X) :=
  Flat.sInter ⟨M.E, M.ground_flat, inter_subset_right _ _⟩ fun _ ↦ And.left

theorem flat_iff_cl_self : M.Flat F ↔ M.cl F = F :=
  ⟨fun h ↦ subset_antisymm (sInter_subset_of_mem ⟨h, inter_subset_left F M.E⟩)
    (M.subset_cl F (Flat.subset_ground h)), fun h ↦ by rw [← h]; exact cl_flat _ _⟩

theorem flat_iff_subset_cl_self (hF : F ⊆ M.E := by aesop_mat) : M.Flat F ↔ M.cl F ⊆ F := by
  rw [flat_iff_cl_self, subset_antisymm_iff, and_iff_left_iff_imp]
  exact fun _ ↦ M.subset_cl F

theorem exists_mem_cl_not_mem_of_not_flat (h : ¬ M.Flat F) (hF : F ⊆ M.E := by aesop_mat) :
    ∃ e, e ∈ M.cl F \ F := by
  rw [flat_iff_cl_self, subset_antisymm_iff, and_iff_left (M.subset_cl F)] at h
  exact not_subset.1 h

theorem flat_iff_ssubset_cl_insert_forall (hF : F ⊆ M.E := by aesop_mat) :
    M.Flat F ↔ ∀ e ∈ M.E \ F, M.cl F ⊂ M.cl (insert e F) := by
  refine' ⟨fun h e he ↦ (M.cl_subset_cl (subset_insert _ _)).ssubset_of_ne _, fun h ↦ _⟩
  · rw [h.cl]
    exact fun h' ↦ mt ((Set.ext_iff.mp h') e).mpr (not_mem_of_mem_diff he)
      ((M.subset_cl _ (insert_subset he.1 hF)) (mem_insert _ _))
  rw [flat_iff_cl_self]
  by_contra h'
  obtain ⟨e, he', heF⟩ := exists_of_ssubset (ssubset_of_ne_of_subset (Ne.symm h') (M.subset_cl F))
  have h'' := h e ⟨(M.cl_subset_ground F) he', heF⟩
  rw [← M.cl_insert_cl_eq_cl_insert e F, insert_eq_of_mem he', M.cl_cl] at h''
  exact h''.ne rfl

theorem flat_iff_forall_circuit (hF : F ⊆ M.E := by aesop_mat) :
    M.Flat F ↔ ∀ C e, M.Circuit C → e ∈ C → C ⊆ insert e F → e ∈ F := by
  rw [flat_iff_cl_self]
  refine' ⟨fun h C e hC heC hCF ↦ _, fun h ↦ _⟩
  · rw [← h]
    refine' (M.cl_subset_cl _) (hC.subset_cl_diff_singleton e heC)
    rwa [diff_subset_iff, singleton_union]
  refine' (M.subset_cl F hF).antisymm' (fun e heF ↦ by_contra fun he' ↦ _)
  obtain ⟨C, hC, heC, hCF⟩ := (mem_cl_iff_exists_circuit_of_not_mem he').mp heF
  exact he' (h C e hC heC hCF)

theorem flat_iff_forall_circuit' :
    M.Flat F ↔ (∀ C e, M.Circuit C → e ∈ C → C ⊆ insert e F → e ∈ F) ∧ F ⊆ M.E := by
  refine' ⟨fun h ↦ ⟨(flat_iff_forall_circuit h.subset_ground).mp h, h.subset_ground⟩, fun h ↦
    (flat_iff_forall_circuit h.2).mpr h.1⟩

theorem Flat.cl_exchange (hF : M.Flat F) (he : e ∈ M.cl (insert f F) \ F) :
    f ∈ M.cl (insert e F) \ F := by
  nth_rw 2 [← hF.cl] at *; exact Matroid.cl_exchange he

theorem Flat.cl_insert_eq_cl_insert_of_mem (hF : M.Flat F) (he : e ∈ M.cl (insert f F) \ F) :
    M.cl (insert e F) = M.cl (insert f F) :=
  Matroid.cl_insert_eq_cl_insert_of_mem (by rwa [hF.cl])

theorem Flat.cl_subset_of_subset (hF : M.Flat F) (h : X ⊆ F) : M.cl X ⊆ F := by
  have h' := M.cl_mono h; rwa [hF.cl] at h'

@[simp] theorem Flat.cl_subset_iff_subset (hF : M.Flat F) (hX : X ⊆ M.E := by aesop_mat) :
    M.cl X ⊆ F ↔ X ⊆ F :=
  ⟨(M.subset_cl X).trans, hF.cl_subset_of_subset⟩

theorem Flat.cl_eq_iff_basis_of_indep (hF : M.Flat F) (hI : M.Indep I) : M.cl I = F ↔ M.Basis I F :=
  ⟨by rintro rfl; exact hI.basis_cl, fun h ↦ by rw [h.cl_eq_cl, hF.cl]⟩

theorem Flat.eq_cl_of_basis (hF : M.Flat F) (hI : M.Basis I F) : F = M.cl I :=
  hI.subset_cl.antisymm (hF.cl_subset_of_subset hI.subset)

theorem Flat.er_insert_eq_add_one (hF : M.Flat F) (he : e ∈ M.E \ F) :
    M.er (insert e F) = M.er F + 1 := by
  rw [Matroid.er_insert_eq_add_one]
  rwa [hF.cl]

theorem Flat.subset_of_relRank_eq_zero (hF : M.Flat F) (hr : M.relRank F X = 0)
    (hX : X ⊆ M.E := by aesop_mat) : X ⊆ F := by
  rwa [relRank_eq_zero_iff, hF.cl] at hr

theorem Flat.one_le_relRank_of_ssubset (hF : M.Flat F) (hss : F ⊂ X)
    (hX : X ⊆ M.E := by aesop_mat) : 1 ≤ M.relRank F X :=
  ENat.one_le_iff_ne_zero.2 (fun h_eq ↦ hss.not_subset <| hF.subset_of_relRank_eq_zero h_eq)


  -- TODO : Cyclic flats.

section Lattice

def Flats (M : Matroid α) : Type _ := {F // M.Flat F}

instance {M : Matroid α} : CoeOut M.Flats (Set α) where
  coe F := F.val

@[simp] theorem Flats.coe_flat (F : M.Flats) : M.Flat F :=
  F.2

def Flat.toFlats (h : M.Flat F) : M.Flats := ⟨_,h⟩

def flatCl (M : Matroid α) (X : Set α) : M.Flats := ⟨_, M.cl_flat X⟩

@[simp] theorem coe_flatCl (M : Matroid α) (X : Set α) : (M.flatCl X : Set α) = M.cl X := rfl

@[simp] theorem Flats.coe_inj {F F' : M.Flats} : (F : Set α) = (F' : Set α) ↔ F = F' :=
  Subtype.coe_inj

@[aesop unsafe 10% (rule_sets [Matroid])]
theorem Flats.coe_subset_ground (F : M.Flats) : (F : Set α) ⊆ M.E :=
  F.coe_flat.subset_ground

instance flatPartialOrder (M : Matroid α) : PartialOrder M.Flats where
  le F₁ F₂ := (F₁ : Set α) ⊆ F₂
  le_refl _ := Subset.rfl
  le_trans _ _ _ h h' := Subset.trans h h'
  le_antisymm := by
    rintro ⟨F, hF⟩ ⟨F', hF'⟩
    simp only [← Flats.coe_inj]
    exact Subset.antisymm

@[simp] theorem Flats.le_iff {F F' : M.Flats} : F ≤ F' ↔ (F : Set α) ⊆ (F' : Set α) := Iff.rfl

@[simp] theorem Flats.lt_iff {F F' : M.Flats} : F < F' ↔ (F : Set α) ⊂ (F' : Set α) := Iff.rfl

theorem flatCl_mono (M : Matroid α) : Monotone M.flatCl :=
  fun _ _ ↦ M.cl_subset_cl

/-- The flats of a matroid form a complete lattice. -/
instance flatLattice (M : Matroid α) : CompleteLattice M.Flats where
  sup F₁ F₂ := M.flatCl (F₁ ∪ F₂)
  le_sup_left F F' := (subset_union_left _ _).trans (M.subset_cl _)
  le_sup_right F F' := (subset_union_right _ _).trans (M.subset_cl _)
  sup_le := by
    rintro ⟨F₁, hF₁⟩ ⟨F₂, hF₂⟩ ⟨F₃, hF₃⟩ (h : F₁ ⊆ F₃) (h' : F₂ ⊆ F₃)
    exact (M.cl_subset_cl (union_subset h h')).trans_eq hF₃.cl
  inf F₁ F₂ := ⟨F₁ ∩ F₂, F₁.coe_flat.inter F₂.coe_flat⟩
  inf_le_left _ _ := inter_subset_left _ _
  inf_le_right _ _ := inter_subset_right _ _
  le_inf _ _ _ h h' := subset_inter h h'
  sSup Fs := M.flatCl (⋃ F ∈ Fs, F)
  le_sSup Fs F h := F.2.cl.symm.subset.trans <| M.cl_subset_cl (subset_biUnion_of_mem h)
  sSup_le Fs F h := by
    simp only [Flats.le_iff, coe_flatCl] at h ⊢
    refine F.coe_flat.cl_subset_of_subset ?_
    simp only [iUnion_subset_iff, F.coe_flat.cl]
    assumption
  sInf Fs := ⟨(⋂ F ∈ Fs, F) ∩ M.E, Flat.biInter_inter_ground (by simp)⟩
  sInf_le Fs F h := (inter_subset_left _ _).trans (biInter_subset_of_mem (by simpa))
  le_sInf Fs F h := subset_inter (by simpa) F.coe_subset_ground
  top := ⟨M.E, M.ground_flat⟩
  bot := M.flatCl ∅
  le_top F := F.coe_flat.subset_ground
  bot_le F := F.coe_flat.cl_subset_of_subset (empty_subset _)

@[simp] theorem Flats.coe_top (M : Matroid α) : ((⊤ : M.Flats) : Set α) = M.E := rfl

@[simp] theorem Flats.coe_bot (M : Matroid α) : ((⊥ : M.Flats) : Set α) = M.cl ∅ := rfl

@[simp] theorem Flats.coe_sup (F₁ F₂ : M.Flats) :
    ((F₁ ⊔ F₂ : M.Flats) : Set α) = M.cl (F₁ ∪ F₂) := rfl

@[simp] theorem Flats.coe_inf (F₁ F₂ : M.Flats) :
    ((F₁ ⊓ F₂ : M.Flats) : Set α) = (F₁ : Set α) ∩ F₂ := rfl

@[simp] theorem Flats.coe_sSup (Fs : Set M.Flats) : sSup Fs = M.cl (⋃ F ∈ Fs, F) := rfl

@[simp] theorem Flats.coe_sInf (Fs : Set M.Flats) : sInf Fs = (⋂ F ∈ Fs, F) ∩ M.E := rfl

theorem Flats.coe_sInf' {Fs : Set M.Flats} (hne : Fs.Nonempty) :
    sInf Fs = (⋂ F ∈ Fs, F : Set α) := by
  simp only [coe_sInf, inter_eq_left]
  exact (biInter_subset_of_mem hne.some_mem).trans (hne.some.coe_subset_ground)

end Lattice



-- ### Covering
/-- `F₀ ⋖[M] F₁` means that `F₀` and `F₁` are strictly nested flats with no flat between them.
  Defined in terms of the bundled `Covby` in the lattice of flats. -/
def Covby (M : Matroid α) (F₀ F₁ : Set α) : Prop :=
  ∃ (h₀ : M.Flat F₀) (h₁ : M.Flat F₁), h₀.toFlats ⋖ h₁.toFlats

notation:25 F₀:50 " ⋖[" M:25 "] " F₁ :75 => Covby M F₀ F₁

@[simp] theorem Flats.covby_iff (F₀ F₁ : M.Flats) : F₀ ⋖ F₁ ↔ (F₀ : Set α) ⋖[M] (F₁ : Set α) := by
  simp only [Matroid.Covby, coe_flat, exists_true_left]; rfl

theorem covby_iff : F₀ ⋖[M] F₁ ↔
    M.Flat F₀ ∧ M.Flat F₁ ∧ F₀ ⊂ F₁ ∧ ∀ F, M.Flat F → F₀ ⊆ F → F ⊆ F₁ → F = F₀ ∨ F = F₁ := by
  simp_rw [Covby, covby_iff_lt_and_eq_or_eq]
  refine ⟨fun ⟨h₀, h₁, hlt, hforall⟩ ↦ ⟨h₀, h₁, hlt, fun F hF hF₀ hF₁ ↦ ?_⟩,
    fun ⟨hF₀, hF₁, hss, hforall⟩ ↦ ⟨hF₀, hF₁, hss, ?_⟩⟩
  · obtain (h1 | h2) := hforall ⟨F, hF⟩ hF₀ hF₁
    · exact Or.inl <| congr_arg ((↑) : M.Flats → Set α) h1
    exact Or.inr <| congr_arg ((↑) : M.Flats → Set α) h2
  rintro ⟨F, hF⟩ (h₀ : F₀ ⊆ F) (h₁ : F ⊆ F₁)
  obtain (rfl | rfl) := hforall F hF h₀ h₁
  · exact Or.inl rfl
  exact Or.inr rfl

theorem Flat.covby_iff_of_flat (hF₀ : M.Flat F₀) (hF₁ : M.Flat F₁) :
    F₀ ⋖[M] F₁ ↔ F₀ ⊂ F₁ ∧ ∀ F, M.Flat F → F₀ ⊆ F → F ⊆ F₁ → F = F₀ ∨ F = F₁ := by
  rw [covby_iff, and_iff_right hF₀, and_iff_right hF₁]

theorem Covby.flat_left (h : F₀ ⋖[M] F₁) : M.Flat F₀ :=
  h.1

theorem Covby.flat_right (h : F₀ ⋖[M] F₁) : M.Flat F₁ :=
  h.2.1

@[aesop unsafe 10% (rule_sets [Matroid])]
theorem Covby.subset_ground_left (h : F₀ ⋖[M] F₁) : F₀ ⊆ M.E :=
  h.flat_left.subset_ground

@[aesop unsafe 10% (rule_sets [Matroid])]
theorem Covby.subset_ground_right (h : F₀ ⋖[M] F₁) : F₁ ⊆ M.E :=
  h.flat_right.subset_ground

theorem Covby.ssubset (h : F₀ ⋖[M] F₁) : F₀ ⊂ F₁ :=
  h.2.2.1

theorem Covby.ne (h : F₀ ⋖[M] F₁) : F₀ ≠ F₁ :=
  h.ssubset.ne

theorem Covby.subset (h : F₀ ⋖[M] F₁) : F₀ ⊆ F₁ :=
  h.ssubset.subset

theorem Covby.eq_or_eq (h : F₀ ⋖[M] F₁) (hF : M.Flat F) (h₀ : F₀ ⊆ F) (h₁ : F ⊆ F₁) :
    F = F₀ ∨ F = F₁ :=
  (covby_iff.1 h).2.2.2 F hF h₀ h₁

theorem Covby.eq_of_subset_of_ssubset (h : F₀ ⋖[M] F₁) (hF : M.Flat F) (hF₀ : F₀ ⊆ F)
    (hF₁ : F ⊂ F₁) : F = F₀ :=
  ((covby_iff.1 h).2.2.2 F hF hF₀ hF₁.subset).elim id fun h' ↦ (hF₁.ne h').elim

theorem Covby.eq_of_ssubset_of_subset (h : F₀ ⋖[M] F₁) (hF : M.Flat F) (hF₀ : F₀ ⊂ F)
    (hF₁ : F ⊆ F₁) : F = F₁ :=
  ((covby_iff.1 h).2.2.2 F hF hF₀.subset hF₁).elim (fun h' ↦ (hF₀.ne.symm h').elim) id

theorem Covby.cl_insert_eq (h : F₀ ⋖[M] F₁) (he : e ∈ F₁ \ F₀) : M.cl (insert e F₀) = F₁ := by
  refine'
    h.eq_of_ssubset_of_subset (M.cl_flat _)
      ((ssubset_insert he.2).trans_subset (M.subset_cl _ _))
      (h.flat_right.cl_subset_of_subset (insert_subset he.1 h.ssubset.subset))
  rw [insert_eq, union_subset_iff, singleton_subset_iff]
  exact ⟨h.flat_right.subset_ground he.1, h.flat_left.subset_ground⟩

theorem Covby.exists_eq_cl_insert (h : F₀ ⋖[M] F₁) : ∃ e ∈ F₁ \ F₀, M.cl (insert e F₀) = F₁ := by
  obtain ⟨e, he⟩ := exists_of_ssubset h.ssubset
  exact ⟨e, he, h.cl_insert_eq he⟩

theorem Flat.covby_iff_eq_cl_insert (hF₀ : M.Flat F₀) :
    F₀ ⋖[M] F₁ ↔ ∃ e ∈ M.E \ F₀, F₁ = M.cl (insert e F₀) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨e, he, rfl⟩ := h.exists_eq_cl_insert
    exact ⟨e, ⟨(M.cl_subset_ground _) he.1, he.2⟩, rfl⟩
  rintro ⟨e, heF₀, rfl⟩
  refine
    covby_iff.2 ⟨hF₀, M.cl_flat _, (M.subset_cl_of_subset (subset_insert _ _) ?_).ssubset_of_ne ?_,
      fun F hF hF₀F hFF₁ ↦ ?_⟩
  · rw [insert_eq, union_subset_iff, singleton_subset_iff]
    exact ⟨heF₀.1, hF₀.subset_ground⟩
  · exact fun h ↦ heF₀.2 (h.symm.subset (mem_cl_of_mem' _ (mem_insert _ _) heF₀.1))
  refine hF₀F.eq_or_ssubset.elim (fun h ↦ Or.inl h.symm)
    (fun hss ↦ Or.inr (hFF₁.antisymm (hF.cl_subset_of_subset (insert_subset ?_ hF₀F))))
  obtain ⟨f, hfF, hfF₀⟩ := exists_of_ssubset hss
  exact mem_of_mem_of_subset (hF₀.cl_exchange ⟨hFF₁ hfF, hfF₀⟩).1
    (hF.cl_subset_of_subset (insert_subset hfF hF₀F))

theorem Covby.er_eq (h : F ⋖[M] F') : M.er F' = M.er F + 1 := by
  obtain ⟨e, he, rfl⟩ := h.exists_eq_cl_insert
  rw [er_cl_eq, h.flat_left.er_insert_eq_add_one]
  exact ⟨M.cl_subset_ground _ he.1, he.2⟩

theorem cl_covby_iff : (M.cl X) ⋖[M] F ↔ ∃ e ∈ M.E \ M.cl X, F = M.cl (insert e X) := by
  simp_rw [(M.cl_flat X).covby_iff_eq_cl_insert, cl_insert_cl_eq_cl_insert]

theorem Flat.covby_cl_insert (hF : M.Flat F) (he : e ∉ F) (heE : e ∈ M.E := by aesop_mat) :
    F ⋖[M] M.cl (insert e F) :=
  hF.covby_iff_eq_cl_insert.2 ⟨e, ⟨heE, he⟩, rfl⟩

theorem Flat.covby_iff_relRank_eq_one (hF₀ : M.Flat F₀) (hF : M.Flat F) :
    F₀ ⋖[M] F ↔ F₀ ⊆ F ∧ M.relRank F₀ F = 1 := by
  simp_rw [hF₀.covby_iff_eq_cl_insert, relRank_eq_one_iff hF.subset_ground, hF₀.cl]
  refine ⟨?_, fun ⟨hss, e, he, h⟩ ↦ ⟨e, ?_, h.antisymm ?_⟩⟩
  · rintro ⟨e, ⟨he, heE⟩, rfl⟩
    refine ⟨M.subset_cl_of_subset (subset_insert _ _), ⟨e, ⟨?_, heE⟩, rfl.subset⟩⟩
    exact M.mem_cl_of_mem (mem_insert _ _)
  · apply diff_subset_diff_left hF.subset_ground he
  exact hF.cl_subset_iff_subset.2 <| insert_subset he.1 hss

theorem Covby.relRank_eq_one (h : F₀ ⋖[M] F₁) : M.relRank F₀ F₁ = 1 :=
  ((h.flat_left.covby_iff_relRank_eq_one h.flat_right).1 h).2

theorem covby_iff_relRank_eq_one :
    F₀ ⋖[M] F₁ ↔ M.Flat F₀ ∧ M.Flat F₁ ∧ F₀ ⊆ F₁ ∧ M.relRank F₀ F₁ = 1 :=
  ⟨fun h ↦ ⟨h.flat_left, h.flat_right, h.subset, h.relRank_eq_one⟩,
    fun ⟨hF₀, hF₁, hss, hr⟩ ↦ (hF₀.covby_iff_relRank_eq_one hF₁).2 ⟨hss, hr⟩⟩

theorem Flat.exists_unique_flat_of_not_mem (hF₀ : M.Flat F₀) (he : e ∈ M.E \ F₀) :
    ∃! F₁, e ∈ F₁ ∧ (F₀ ⋖[M] F₁) := by
  simp_rw [hF₀.covby_iff_eq_cl_insert]
  use M.cl (insert e F₀)
  refine' ⟨_, _⟩
  · constructor
    · exact (M.inter_ground_subset_cl (insert e F₀)) ⟨mem_insert _ _, he.1⟩
    use e, he
  simp only [exists_prop, and_imp, forall_exists_index]
  rintro X heX f _ rfl
  rw [hF₀.cl_insert_eq_cl_insert_of_mem ⟨heX, he.2⟩]

/-- If `F` covers distinct flats `F₀` and `F₁`, then `F` is their join. -/
theorem Covby.eq_cl_union_of_covby_of_ne (h₀ : F₀ ⋖[M] F) (h₁ : F₁ ⋖[M] F) (hne : F₀ ≠ F₁) :
    F = M.cl (F₀ ∪ F₁) := by
  refine subset_antisymm ?_ (h₁.flat_right.cl_subset_of_subset (union_subset h₀.subset h₁.subset))
  have hnss : ¬ (F₀ ⊆ F₁) :=
    fun hss ↦ hne.symm <| h₀.eq_of_subset_of_ssubset h₁.flat_left hss h₁.ssubset
  obtain ⟨e, he₀, he₁⟩ := not_subset.1 hnss
  obtain rfl := h₁.cl_insert_eq ⟨h₀.subset he₀, he₁⟩
  exact M.cl_subset_cl (insert_subset (Or.inl he₀) (subset_union_right _ _))

theorem Flat.exists_left_covby_of_ssubset (hF₀ : M.Flat F₀) (hF₁ : M.Flat F₁) (hss : F₀ ⊂ F₁) :
    ∃ F, ((F₀ ⋖[M] F) ∧ F ⊆ F₁) := by
  obtain ⟨e, he⟩ := exists_of_ssubset hss
  exact ⟨_, hF₀.covby_cl_insert he.2 (hF₁.subset_ground he.1),
    hF₁.cl_subset_of_subset <| insert_subset he.1 hss.subset⟩

theorem Flat.exists_covby_right_of_ssubset (hF₀ : M.Flat F₀) (hF₁ : M.Flat F₁) (hss : F₀ ⊂ F₁) :
    ∃ F, (F₀ ⊆ F ∧ (F ⋖[M] F₁)) := by
  obtain ⟨I, J, hI, hJ, hIJ⟩ := M.exists_basis_subset_basis hss.subset
  have hssu : I ⊂ J := hIJ.ssubset_of_ne <| by
    rintro rfl
    rw [hF₀.eq_cl_of_basis hI, hF₁.eq_cl_of_basis hJ] at hss
    exact hss.ne rfl
  obtain ⟨e, heJ, heI⟩ := exists_of_ssubset hssu
  refine ⟨M.cl (J \ {e}), hI.subset_cl.trans (M.cl_subset_cl (subset_diff_singleton hIJ heI)), ?_⟩
  convert (M.cl_flat (J \ {e})).covby_cl_insert ?_ (hJ.indep.subset_ground heJ)
  · rw [cl_insert_cl_eq_cl_insert, insert_diff_singleton, insert_eq_of_mem heJ,
      hF₁.eq_cl_of_basis hJ]
  exact hJ.indep.not_mem_cl_diff_of_mem heJ

theorem Covby.covby_cl_union_of_inter_covby (h₀ : F₀ ∩ F₁ ⋖[M] F₀) (h₁ : F₀ ∩ F₁ ⋖[M] F₁) :
    F₀ ⋖[M] M.cl (F₀ ∪ F₁) := by
  obtain ⟨e₀, -, h₀'⟩ := h₀.exists_eq_cl_insert
  obtain ⟨e₁, he₁, h₁'⟩ := h₁.exists_eq_cl_insert
  nth_rw 2 [← h₀', ← h₁']
  rw [cl_cl_union_cl_eq_cl_union, ← singleton_union, ← singleton_union,
    ← union_union_distrib_right, union_comm {e₀}, union_assoc, singleton_union, singleton_union,
    ← M.cl_insert_cl_eq_cl_insert, h₀']
  exact h₀.flat_right.covby_cl_insert (fun h ↦ he₁.2 ⟨h, he₁.1⟩) (h₁.flat_right.subset_ground he₁.1)

instance {M : Matroid α} : IsWeakUpperModularLattice M.Flats where
  covby_sup_of_inf_covby_covby := by
    rintro ⟨F₀, hF₀⟩ ⟨F₁, hF₁⟩
    simp only [ge_iff_le, Flats.le_iff, Flats.covby_iff, Flats.coe_inf, Flats.coe_sup]
    exact Covby.covby_cl_union_of_inter_covby

/-- If `M.relRank F₀ F₁ = 2` for flats `F₀, F₁`, then every flat strictly between
  `F₀` and `F₁` covers `F₀` and is covered by `F₁`. -/
theorem Flat.covby_and_covby_of_ssubset_of_ssubset_of_relRank_eq_two (hF₀ : M.Flat F₀)
    (hF₁ : M.Flat F₁) (h : M.relRank F₀ F₁ = 2) (hF : M.Flat F) (h₀ : F₀ ⊂ F) (h₁ : F ⊂ F₁) :
    (F₀ ⋖[M] F) ∧ (F ⋖[M] F₁) := by
  have h0le := hF₀.one_le_relRank_of_ssubset h₀
  have h1le := hF.one_le_relRank_of_ssubset h₁
  rw [← M.relRank_add_of_subset_of_subset h₀.subset h₁.subset] at h
  have h0top : M.relRank F₀ F ≠ ⊤
  · intro h'; rw [h'] at h; norm_cast at h
  have h1top : M.relRank F F₁ ≠ ⊤
  · intro h'; rw [h', add_top] at h; norm_cast at h
  have hle1 := WithTop.le_of_add_le_add_left h0top <| h.le.trans (add_le_add_right h0le 1)
  have hle0 := WithTop.le_of_add_le_add_right h1top <| h.le.trans (add_le_add_left h1le 1)
  rw [hF₀.covby_iff_relRank_eq_one hF, hF.covby_iff_relRank_eq_one hF₁,
    and_iff_right h₀.subset, and_iff_right h₁.subset]
  exact ⟨hle0.antisymm h0le, hle1.antisymm h1le⟩

/-- If some flat is covered by `F₁` and covers `F₀`,
  then this holds for every flat strictly between `F₀` and `F₁`. -/
theorem Covby.covby_and_covby_of_covby_of_ssubset_of_ssubset (hF₀F' : F₀ ⋖[M] F')
    (hF'F₁ : F' ⋖[M] F₁) (hF : M.Flat F) (h₀ : F₀ ⊂ F) (h₁ : F ⊂ F₁) :
    (F₀ ⋖[M] F) ∧ (F ⋖[M] F₁) := by
  apply hF₀F'.flat_left.covby_and_covby_of_ssubset_of_ssubset_of_relRank_eq_two hF'F₁.flat_right
    ?_ hF h₀ h₁
  rw [← M.relRank_add_of_subset_of_subset hF₀F'.subset hF'F₁.subset, hF'F₁.relRank_eq_one,
    hF₀F'.relRank_eq_one]
  rfl

/-- The flats covering a flat `F` induce a partition of `M.E \ F`. -/
@[simps!] def Flat.covbyPartition (hF : M.Flat F) : Partition (M.E \ F) :=
  Partition.ofPairwiseDisjoint'
    (parts := (· \ F) '' {F' | F ⋖[M] F'})
    (pairwiseDisjoint := by
      rintro _ ⟨F₁, hF₁, rfl⟩  _ ⟨F₂, hF₂, rfl⟩ hne
      refine disjoint_iff_forall_ne.2 ?_
      rintro e (he₁ : e ∈ F₁ \ F) _ (he₂ : _ ∈ F₂ \ F) rfl
      rw [← hF₁.cl_insert_eq he₁, ← hF₂.cl_insert_eq he₂] at hne
      exact hne rfl )
    (forall_nonempty := by rintro _ ⟨_, hF₁, rfl⟩; exact exists_of_ssubset hF₁.ssubset )
    (eq_sUnion := by
      simp only [sUnion_image, mem_setOf_eq, ext_iff, mem_diff, mem_iUnion, exists_and_left,
        exists_prop]
      exact fun e ↦ ⟨fun ⟨he,heF⟩ ↦
        ⟨M.cl (insert e F), M.mem_cl_of_mem (mem_insert _ _), hF.covby_cl_insert heF, heF⟩,
        fun ⟨F', heF', hlt, h⟩ ↦ ⟨hlt.flat_right.subset_ground heF', h⟩⟩ )

@[simp] theorem Flat.mem_covbyPartition_iff {X : Set α} (hF : M.Flat F) :
    X ∈ hF.covbyPartition ↔ ∃ F', ((F ⋖[M] F') ∧ F' \ F = X) := by
  simp [Flat.covbyPartition]

@[simp] theorem Flat.partOf_covbyPartition_eq (hF : M.Flat F) (e : α) :
    hF.covbyPartition.partOf e = M.cl (insert e F) \ F := by
  by_cases he : e ∈ M.E \ F
  · obtain ⟨F', hFF', hF'⟩ := hF.mem_covbyPartition_iff.1 (hF.covbyPartition.partOf_mem he)
    obtain rfl := hFF'.cl_insert_eq (hF'.symm.subset <| hF.covbyPartition.mem_partOf he)
    exact hF'.symm
  have hrw : insert e F ∩ M.E = F
  · refine subset_antisymm ?_ (subset_inter (subset_insert _ _) hF.subset_ground)
    rw [← singleton_union, inter_distrib_right, union_subset_iff,
       (and_iff_left (inter_subset_left _ _))]
    rintro f ⟨rfl, hf⟩
    exact by_contra fun hfF ↦ he ⟨hf, hfF⟩
  rw [← cl_inter_ground, hrw, hF.cl, diff_self, hF.covbyPartition.partOf_eq_empty he]

@[simp] theorem Flat.rel_covbyPartition_iff (hF : M.Flat F) {e f : α} :
    hF.covbyPartition.Rel e f ↔
      e ∈ M.E \ F ∧ f ∈ M.E \ F ∧ M.cl (insert e F) = M.cl (insert f F) := by
  simp only [hF.covbyPartition.rel_iff_partOf_eq_partOf', partOf_covbyPartition_eq, mem_diff,
    exists_prop, exists_and_left, and_congr_right_iff]
  refine fun _ _  ↦ ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
  rw [← union_eq_self_of_subset_right (M.cl_subset_cl (subset_insert e F)),
    ← union_eq_self_of_subset_right (M.cl_subset_cl (subset_insert f F)), hF.cl,
    ← diff_union_self, h, diff_union_self]

theorem Flat.rel_covbyPartition_iff' (hF : M.Flat F) (he : e ∈ M.E \ F) :
    hF.covbyPartition.Rel e f ↔ M.cl (insert e F) = M.cl (insert f F) := by
  rw [hF.rel_covbyPartition_iff, and_iff_right he, and_iff_right_iff_imp]
  refine fun hcl ↦ ⟨by_contra fun hf ↦ ?_, fun hfF ↦ ?_⟩
  · rw [← M.cl_inter_ground (insert f F), insert_inter_of_not_mem hf,
      inter_eq_self_of_subset_left hF.subset_ground, hF.cl] at hcl
    exact he.2 <| hcl.subset (M.mem_cl_of_mem (mem_insert e F))
  rw [insert_eq_of_mem hfF, hF.cl] at hcl
  exact he.2 <| hcl.subset (M.mem_cl_of_mem (mem_insert e F))

/-- Cells of the `covbyPartition` induced by `F₀` are equivalent to flats covering `F₀`.-/
@[simps] def Flat.equivCovbyPartition (hF₀ : M.Flat F₀) :
    ↑(hF₀.covbyPartition : Set (Set α)) ≃ {F // F₀ ⋖[M] F} where
  toFun F := ⟨F ∪ F₀, by
    obtain ⟨_, ⟨F, hF : F₀ ⋖[M] F, rfl⟩⟩ := F
    simpa [union_eq_self_of_subset_right hF.subset]⟩
  invFun F := ⟨F \ F₀, by
    simp only [SetLike.mem_coe, mem_covbyPartition_iff]
    exact ⟨_, F.prop, rfl⟩ ⟩
  left_inv := by rintro ⟨_, ⟨F, hF : F₀ ⋖[M] F, rfl⟩⟩; simp
  right_inv := by rintro ⟨F, hF⟩; simp [hF.subset]

theorem Flat.ground_encard_eq_tsum (hF₀ : M.Flat F₀) :
    M.E.encard = F₀.encard + ∑' F : {F // F₀ ⋖[M] F}, ((F : Set α) \ F₀).encard := by
  rw [← encard_diff_add_encard_of_subset hF₀.subset_ground, add_comm]
  apply congr_arg (_ + ·)
  have hcard := ENat.tsum_encard_eq_encard_sUnion hF₀.covbyPartition.pairwiseDisjoint
  simp only [SetLike.coe_sort_coe, Partition.sUnion_eq] at hcard
  rw [← ENat.tsum_comp_eq_tsum_of_equiv hF₀.equivCovbyPartition (fun F ↦ encard ((F : Set α) \ F₀)),
    ← hcard]
  apply tsum_congr
  rintro ⟨_, ⟨F, hF : F₀ ⋖[M] F, rfl⟩⟩
  rw [hF₀.equivCovbyPartition_apply_coe, diff_union_self, union_diff_right]

section Minor

theorem flat_contract (X C : Set α) : (M ⧸ C).Flat (M.cl (X ∪ C) \ C) := by
  rw [flat_iff_cl_self, contract_cl_eq, diff_union_self, ← M.cl_union_cl_right_eq,
    union_eq_self_of_subset_right (M.cl_subset_cl (subset_union_right _ _)), cl_cl]

@[simp] theorem flat_contract_iff (hC : C ⊆ M.E := by aesop_mat) :
    (M ⧸ C).Flat F ↔ M.Flat (F ∪ C) ∧ Disjoint F C := by
  rw [flat_iff_cl_self, contract_cl_eq, subset_antisymm_iff, subset_diff, diff_subset_iff,
    union_comm C, ← and_assoc, and_congr_left_iff, flat_iff_cl_self, subset_antisymm_iff,
    and_congr_right_iff]
  exact fun _ _ ↦ ⟨fun h ↦ M.subset_cl _ (union_subset (h.trans (M.cl_subset_ground _)) hC),
    fun h ↦ (subset_union_left _ _).trans h⟩

theorem Flat.union_flat_of_contract (hF : (M ⧸ C).Flat F) (hC : C ⊆ M.E := by aesop_mat) :
    M.Flat (F ∪ C) :=
  ((flat_contract_iff hC).1 hF).1

theorem flat_contract_iff' :
    (M ⧸ C).Flat F ↔ (M.Flat (F ∪ (C ∩ M.E)) ∧ Disjoint F (C ∩ M.E)) := by
  rw [← contract_inter_ground_eq, flat_contract_iff]

theorem Flat.union_flat_of_contract' (hF : (M ⧸ C).Flat F) : M.Flat (F ∪ M.cl C) := by
  replace hF := (flat_contract_iff'.1 hF).1.cl
  rw [← cl_union_cl_right_eq, cl_inter_ground] at hF
  rw [flat_iff_subset_cl_self (union_subset _ (M.cl_subset_ground _)), hF]
  · exact union_subset_union_right _ <| (M.subset_cl _).trans (M.cl_inter_ground _).subset
  exact (subset_union_left _ _).trans (hF.symm.subset.trans (M.cl_subset_ground _))

theorem Nonloop.contract_flat_iff (he : M.Nonloop e) :
    (M ⧸ e).Flat F ↔ M.Flat (insert e F) ∧ e ∉ F := by
  rw [contract_elem, flat_contract_iff, union_singleton, disjoint_singleton_right]

/-- Flats of `M ⧸ C` are equivalent to flats of `M` containing `C`-/
@[simps] def flatContractEquiv (M : Matroid α) (C : Set α) (hC : C ⊆ M.E := by aesop_mat) :
    {F // (M ⧸ C).Flat F} ≃ {F // M.Flat F ∧ C ⊆ F} where
  toFun F := ⟨F ∪ C, by simp [subset_union_right, F.prop.union_flat_of_contract]⟩
  invFun F := ⟨F \ C, by simp
    [flat_contract_iff hC, union_eq_self_of_subset_right F.prop.2, disjoint_sdiff_left, F.prop.1]⟩
  left_inv := by rintro ⟨-, hF⟩; simp [(subset_diff.1 hF.subset_ground).2]
  right_inv := by rintro ⟨F, hF⟩; simp [hF.2]



end Minor

-- ### Hyperplanes
section Hyperplane

/-- A hyperplane is a maximal set containing no base  -/
@[pp_dot] def Hyperplane (M : Matroid α) (H : Set α) : Prop :=
  H ⋖[M] M.E

@[aesop unsafe 10% (rule_sets [Matroid])]
theorem Hyperplane.subset_ground (hH : M.Hyperplane H) : H ⊆ M.E :=
  hH.flat_left.subset_ground

theorem hyperplane_iff_covby : M.Hyperplane H ↔ H ⋖[M] M.E := Iff.rfl

theorem Hyperplane.covby (h : M.Hyperplane H) : H ⋖[M] M.E :=
  h

theorem Hyperplane.flat (hH : M.Hyperplane H) : M.Flat H :=
  hH.covby.flat_left

theorem Hyperplane.ssubset_ground (hH : M.Hyperplane H) : H ⊂ M.E :=
  hH.covby.ssubset

theorem Hyperplane.ssubset_univ (hH : M.Hyperplane H) : H ⊂ univ :=
  hH.ssubset_ground.trans_subset (subset_univ _)

theorem Hyperplane.cl_insert_eq (hH : M.Hyperplane H) (heH : e ∉ H) (he : e ∈ M.E := by aesop_mat) :
    M.cl (insert e H) = M.E :=
  hH.covby.cl_insert_eq ⟨he, heH⟩

theorem Hyperplane.cl_eq_ground_of_ssuperset (hH : M.Hyperplane H) (hX : H ⊂ X)
    (hX' : X ⊆ M.E := by aesop_mat) : M.cl X = M.E := by
  obtain ⟨e, heX, heH⟩ := exists_of_ssubset hX
  exact (M.cl_subset_ground _).antisymm ((hH.cl_insert_eq heH (hX' heX)).symm.trans_subset
    (M.cl_subset_cl (insert_subset heX hX.subset)))

theorem Hyperplane.spanning_of_ssuperset (hH : M.Hyperplane H) (hX : H ⊂ X)
    (hXE : X ⊆ M.E := by aesop_mat) :
    M.Spanning X := by rw [spanning_iff_cl, hH.cl_eq_ground_of_ssuperset hX]

theorem Hyperplane.not_spanning (hH : M.Hyperplane H) : ¬M.Spanning H := by
  rw [hH.flat.spanning_iff]; exact hH.ssubset_ground.ne

theorem Hyperplane.flat_superset_eq_ground (hH : M.Hyperplane H) (hF : M.Flat F) (hHF : H ⊂ F) :
    F = M.E := by rw [← hF.cl, hH.cl_eq_ground_of_ssuperset hHF]

theorem hyperplane_iff_maximal_proper_flat :
    M.Hyperplane H ↔ M.Flat H ∧ H ⊂ M.E ∧ ∀ F, H ⊂ F → M.Flat F → F = M.E := by
  rw [hyperplane_iff_covby, covby_iff, and_iff_right M.ground_flat, and_congr_right_iff,
    and_congr_right_iff]
  simp_rw [or_iff_not_imp_left, ssubset_iff_subset_ne, and_imp, ← Ne.def]
  exact fun _ _ _  ↦
    ⟨fun h F hHF hne' hF ↦ h F hF hHF hF.subset_ground hne'.symm, fun h F hF hHF _ hne' ↦
      h F hHF hne'.symm hF⟩

theorem hyperplane_iff_maximal_nonspanning :
    M.Hyperplane H ↔ H ∈ maximals (· ⊆ ·) {X | ¬M.Spanning X ∧ X ⊆ M.E} := by
  simp_rw [and_comm (b := _ ⊆ _), mem_maximals_setOf_iff, and_imp]
  refine' ⟨fun h ↦ ⟨⟨h.subset_ground, h.not_spanning⟩, fun X hX hX' hHX ↦ _⟩, fun h ↦ _⟩
  · exact by_contra fun hne ↦ hX' (h.spanning_of_ssuperset (hHX.ssubset_of_ne hne))
  rw [hyperplane_iff_covby, covby_iff, and_iff_right M.ground_flat,
    flat_iff_ssubset_cl_insert_forall h.1.1]
  refine'
    ⟨fun e he ↦ _, h.1.1.ssubset_of_ne (by rintro rfl; exact h.1.2 M.ground_spanning),
      fun F hF hHF hFE ↦ or_iff_not_imp_right.mpr fun hFE' ↦ _⟩
  · have h' := h.2 (insert_subset he.1 h.1.1)
    simp only [subset_insert, forall_true_left, @eq_comm _ H, insert_eq_self, iff_false_intro he.2,
      imp_false, Classical.not_not, spanning_iff_cl]  at h'
    rw [spanning_iff_cl] at h'
    rw [h', ← not_spanning_iff_cl h.1.1]
    exact h.1.2
  have h' := h.2 hFE
  rw [hF.spanning_iff] at h'
  rw [h' hFE' hHF]

@[simp] theorem compl_cocircuit_iff_hyperplane (hH : H ⊆ M.E := by aesop_mat) :
    M.Cocircuit (M.E \ H) ↔ M.Hyperplane H := by
  simp_rw [cocircuit_iff_mem_minimals_compl_nonspanning, hyperplane_iff_maximal_nonspanning,
    (and_comm (b := _ ⊆ _)), mem_minimals_setOf_iff, mem_maximals_setOf_iff,
    diff_diff_cancel_left hH, and_iff_right hH, subset_diff, and_imp, and_congr_right_iff]
  refine' fun _ ↦ ⟨fun h X hXE hX hHX ↦ _, fun h X hX hXE hXH ↦ _⟩
  · rw [← diff_diff_cancel_left hH, ← diff_diff_cancel_left hXE,
      h (y := M.E \ X) (by rwa [diff_diff_cancel_left hXE]) (diff_subset _ _)]
    rw [← subset_compl_iff_disjoint_left, diff_eq, compl_inter, compl_compl]
    exact hHX.trans (subset_union_right _ _)
  rw [h (diff_subset _ _) hX, diff_diff_cancel_left hXE]
  rw [subset_diff]
  exact ⟨hH, hXH.symm⟩

@[simp] theorem compl_hyperplane_iff_cocircuit (h : K ⊆ M.E := by aesop_mat) :
    M.Hyperplane (M.E \ K) ↔ M.Cocircuit K := by
  rw [← compl_cocircuit_iff_hyperplane, diff_diff_right, diff_self, empty_union, inter_comm,
    inter_eq_left.mpr h]

theorem Hyperplane.compl_cocircuit (hH : M.Hyperplane H) : M.Cocircuit (M.E \ H) :=
  (compl_cocircuit_iff_hyperplane hH.subset_ground).mpr hH

theorem Cocircuit.compl_hyperplane {K : Set α} (hK : M.Cocircuit K) : M.Hyperplane (M.E \ K) :=
  (compl_hyperplane_iff_cocircuit hK.subset_ground).mpr hK

theorem univ_not_hyperplane (M : Matroid α) : ¬M.Hyperplane univ :=
  fun h ↦ h.ssubset_univ.ne rfl

theorem Hyperplane.eq_of_subset (h₁ : M.Hyperplane H₁) (h₂ : M.Hyperplane H₂) (h : H₁ ⊆ H₂) :
    H₁ = H₂ :=
  (h₁.covby.eq_or_eq h₂.flat h h₂.subset_ground).elim Eq.symm fun h' ↦
    (h₂.ssubset_ground.ne h').elim

theorem Hyperplane.not_ssubset (h₁ : M.Hyperplane H₁) (h₂ : M.Hyperplane H₂) : ¬H₁ ⊂ H₂ :=
  fun hss ↦ hss.ne (h₁.eq_of_subset h₂ hss.subset)

theorem Hyperplane.inter_ssubset_left_of_ne (h₁ : M.Hyperplane H₁) (h₂ : M.Hyperplane H₂)
    (hne : H₁ ≠ H₂) : H₁ ∩ H₂ ⊂ H₁ := by
  refine (inter_subset_left _ _).ssubset_of_ne fun h_eq ↦ hne <| h₁.eq_of_subset h₂ ?_
  rw [← h_eq]
  exact inter_subset_right _ _

theorem Hyperplane.inter_ssubset_right_of_ne (h₁ : M.Hyperplane H₁) (h₂ : M.Hyperplane H₂)
    (hne : H₁ ≠ H₂) : H₁ ∩ H₂ ⊂ H₂ := by
  rw [inter_comm]; exact h₂.inter_ssubset_left_of_ne h₁ hne.symm

theorem Base.hyperplane_of_cl_diff_singleton (hB : M.Base B) (heB : e ∈ B) :
    M.Hyperplane (M.cl (B \ {e})) := by
  rw [hyperplane_iff_covby, Flat.covby_iff_eq_cl_insert (M.cl_flat _)]
  refine' ⟨e, ⟨hB.subset_ground heB, _⟩, _⟩
  · rw [(hB.indep.diff {e}).not_mem_cl_iff (hB.subset_ground heB)]
    simpa [insert_eq_of_mem heB] using hB.indep
  simpa [insert_eq_of_mem heB] using hB.cl_eq.symm

theorem Hyperplane.ssuperset_eq_univ_of_flat (hH : M.Hyperplane H) (hF : M.Flat F) (h : H ⊂ F) :
    F = M.E :=
  hH.covby.eq_of_ssubset_of_subset hF h hF.subset_ground

theorem Hyperplane.cl_insert_eq_univ (hH : M.Hyperplane H) (he : e ∈ M.E \ H) :
    M.cl (insert e H) = M.E := by
  refine' hH.ssuperset_eq_univ_of_flat (M.cl_flat _)
    ((ssubset_insert he.2).trans_subset (M.subset_cl _ _))
  rw [insert_eq, union_subset_iff, singleton_subset_iff]
  exact ⟨he.1, hH.subset_ground⟩

theorem exists_hyperplane_sep_of_not_mem_cl (h : e ∈ M.E \ M.cl X) (hX : X ⊆ M.E := by aesop_mat) :
    ∃ H, M.Hyperplane H ∧ X ⊆ H ∧ e ∉ H := by
  obtain ⟨I, hI⟩ := M.exists_basis X
  rw [← hI.cl_eq_cl, mem_diff, hI.indep.not_mem_cl_iff] at h
  obtain ⟨B, hB, heIB⟩ := h.2.1.exists_base_superset
  rw [insert_subset_iff] at heIB
  refine ⟨_, hB.hyperplane_of_cl_diff_singleton heIB.1, ?_, ?_⟩
  · exact hI.subset_cl.trans (M.cl_subset_cl (subset_diff_singleton heIB.2 h.2.2))
  exact hB.indep.not_mem_cl_diff_of_mem heIB.1

theorem cl_eq_sInter_hyperplanes (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    M.cl X = ⋂₀ {H | M.Hyperplane H ∧ X ⊆ H} ∩ M.E := by
  refine' subset_antisymm (subset_inter _ (M.cl_subset_ground _)) _
  · rw [subset_sInter_iff]; rintro H ⟨hH, hXH⟩; exact hH.flat.cl_subset_of_subset hXH
  rintro e ⟨heH, heE⟩
  refine' by_contra fun hx ↦ _
  obtain ⟨H, hH, hXH, heH'⟩ := exists_hyperplane_sep_of_not_mem_cl ⟨heE, hx⟩
  exact heH' (heH H ⟨hH, hXH⟩)

theorem mem_cl_iff_forall_hyperplane (hX : X ⊆ M.E := by aesop_mat) (he : e ∈ M.E := by aesop_mat) :
    e ∈ M.cl X ↔ ∀ H, M.Hyperplane H → X ⊆ H → e ∈ H := by
  simp_rw [← M.cl_inter_ground X,
    M.cl_eq_sInter_hyperplanes _ ((inter_subset_left _ _).trans hX), mem_inter_iff, and_iff_left he,
    mem_sInter, mem_setOf_eq, and_imp]
  exact ⟨fun h H hH hXH ↦ h _ hH ((inter_subset_left _ _).trans hXH),
    fun h H hH hXH ↦ h H hH (by rwa [inter_eq_self_of_subset_left hX] at hXH )⟩

theorem mem_dual_cl_iff_forall_circuit (hX : X ⊆ M.E := by aesop_mat)
  (he : e ∈ M.E := by aesop_mat) :
    e ∈ M﹡.cl X ↔ ∀ C, M.Circuit C → e ∈ C → (X ∩ C).Nonempty := by
  rw [← dual_dual M]
  simp_rw [← cocircuit_def, dual_dual M, mem_cl_iff_forall_hyperplane (M := M﹡) hX he]
  refine' ⟨fun h C hC heC ↦ by_contra fun hne ↦ _, fun h H hH hXE ↦ by_contra fun he' ↦ _⟩
  · rw [nonempty_iff_ne_empty, not_not, ← disjoint_iff_inter_eq_empty] at hne
    exact (h _ hC.compl_hyperplane (subset_diff.mpr ⟨hX, hne⟩)).2 heC
  obtain ⟨f, hf⟩ := h _ hH.compl_cocircuit ⟨he, he'⟩
  exact hf.2.2 (hXE hf.1)

theorem Flat.subset_hyperplane_of_ne_ground (hF : M.Flat F) (h : F ≠ M.E) :
    ∃ H, M.Hyperplane H ∧ F ⊆ H := by
  obtain ⟨e, heE, heF⟩ := exists_of_ssubset (hF.subset_ground.ssubset_of_ne h)
  rw [← hF.cl] at heF
  obtain ⟨H, hH, hFH, -⟩ := exists_hyperplane_sep_of_not_mem_cl ⟨heE, heF⟩
  exact ⟨H, hH, hFH⟩

theorem subset_hyperplane_iff_cl_ne_ground (hY : Y ⊆ M.E := by aesop_mat) :
    M.cl Y ≠ M.E ↔ ∃ H, M.Hyperplane H ∧ Y ⊆ H := by
  refine' ⟨fun h ↦ _, _⟩
  · obtain ⟨H, hH, hYH⟩ := (M.cl_flat Y).subset_hyperplane_of_ne_ground h
    exact ⟨H, hH, (M.subset_cl Y).trans hYH⟩
  rintro ⟨H, hH, hYH⟩ hY
  refine' hH.ssubset_ground.not_subset _
  rw [← hH.flat.cl]
  exact hY.symm.trans_subset (M.cl_mono hYH)

theorem Hyperplane.inter_covby_comm (hH₁ : M.Hyperplane H₁) (hH₂ : M.Hyperplane H₂) :
    M.Covby (H₁ ∩ H₂) H₁ ↔ M.Covby (H₁ ∩ H₂) H₂ := by
  obtain (rfl | hne) := eq_or_ne H₁ H₂; simp
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact And.left <| h.covby_and_covby_of_covby_of_ssubset_of_ssubset hH₁.covby hH₂.flat
      (hH₁.inter_ssubset_right_of_ne hH₂ hne) hH₂.ssubset_ground
  exact And.left <| h.covby_and_covby_of_covby_of_ssubset_of_ssubset hH₂.covby hH₁.flat
    (hH₁.inter_ssubset_left_of_ne hH₂ hne) (hH₁.ssubset_ground)

end Hyperplane



section LowRank

@[reducible, pp_dot] def Point (M : Matroid α) (P : Set α) := M.Flat P ∧ M.er P = 1

theorem Point.flat (hP : M.Point P) : M.Flat P :=
  hP.1

theorem Point.er (hP : M.Point P) : M.er P = 1 :=
  hP.2

@[aesop unsafe 10% (rule_sets [Matroid])]
theorem Point.subset_ground (hP : M.Point P) : P ⊆ M.E :=
  hP.1.subset_ground

theorem Nonloop.cl_point (he : M.Nonloop e) : M.Point (M.cl {e}) :=
  ⟨M.cl_flat {e}, by rw [er_cl_eq, he.indep.er, encard_singleton]⟩

theorem loops_covby_iff : M.cl ∅ ⋖[M] P ↔ M.Point P := by
  simp only [covby_iff_relRank_eq_one, cl_flat, relRank_cl_left, relRank_empty_left, true_and,
    and_congr_right_iff, and_iff_right_iff_imp]
  exact fun h _ ↦ h.cl_subset_of_subset (empty_subset _)

theorem Point.covby (hP : M.Point P) : M.cl ∅ ⋖[M] P := loops_covby_iff.2 hP

theorem Point.exists_eq_cl_nonloop (hP : M.Point P) : ∃ e, M.Nonloop e ∧ P = M.cl {e} := by
  obtain ⟨I, hI⟩ := M.exists_basis P
  obtain ⟨e, rfl⟩ := encard_eq_one.1 <| hI.encard.trans hP.er
  obtain rfl := hP.flat.eq_cl_of_basis hI
  exact ⟨e, indep_singleton.1 hI.indep, rfl⟩

theorem Point.eq_cl_of_mem (hP : M.Point P) (he : M.Nonloop e) (heP : e ∈ P) : P = M.cl {e} := by
  rw [← indep_singleton] at he
  exact hP.flat.eq_cl_of_basis <| he.basis_of_subset_of_er_le_of_finite (singleton_subset_iff.2 heP)
    (by rw [hP.er, he.er, encard_singleton]) (finite_singleton e)

theorem point_iff_exists_eq_cl_nonloop : M.Point P ↔ ∃ e, M.Nonloop e ∧ P = M.cl {e} :=
  ⟨Point.exists_eq_cl_nonloop, by rintro ⟨e, he, rfl⟩; exact he.cl_point⟩

theorem point_contract_iff (hC : C ⊆ M.E := by aesop_mat) :
    (M ⧸ C).Point P ↔ (M.cl C ⋖[M] (C ∪ P)) ∧ Disjoint P C := by
  rw [Point, flat_contract_iff, covby_iff_relRank_eq_one, relRank_cl_left,
    union_comm C, ← relRank_eq_relRank_union, and_iff_right (cl_flat _ _),
    ← relRank_eq_er_contract, and_assoc, and_assoc, and_congr_right_iff, and_comm,
    and_congr_left_iff, iff_and_self]
  rintro h - -
  rw [← h.cl]
  exact M.cl_subset_cl (subset_union_right _ _)

/-- Points of `M ⧸ C` are equivalent to flats covering `M.cl C`. -/
@[simps] def pointContractCovbyEquiv (M : Matroid α) (C : Set α) :
    {P // (M ⧸ C).Point P} ≃ {F // M.cl C ⋖[M] F} where
  toFun P := ⟨P ∪ M.cl C, by
    obtain ⟨P, hP⟩ := P
    rw [← contract_inter_ground_eq, point_contract_iff, cl_inter_ground] at hP
    convert hP.1 using 1
    rw [subset_antisymm_iff, union_subset_iff, and_iff_right (subset_union_right _ _),
      union_subset_iff, and_iff_left (subset_union_left _ _), ← hP.1.flat_right.cl,
      ← cl_inter_ground]
    exact ⟨M.cl_subset_cl (subset_union_left _ _), (M.subset_cl _).trans (subset_union_right _ _)⟩⟩
  invFun P := ⟨P \ C, by
    obtain ⟨P, hP⟩ := P
    rw [← cl_inter_ground] at hP
    rwa [diff_eq_diff_inter_of_subset hP.subset_ground_right, ← contract_inter_ground_eq,
      point_contract_iff, and_iff_left disjoint_sdiff_left, union_diff_self,
      union_eq_self_of_subset_left, cl_inter_ground]
    exact (M.subset_cl _).trans hP.subset ⟩
  left_inv := by
    rintro ⟨P,hP⟩
    simp only [Subtype.mk.injEq]
    rw [← contract_inter_ground_eq, point_contract_iff] at hP
    rw [← cl_inter_ground, diff_eq_diff_inter_of_subset (union_subset _ (M.cl_subset_ground _)),
      subset_antisymm_iff, diff_subset_iff, union_subset_iff, subset_diff,
      and_iff_right (subset_union_right _ _), and_iff_right hP.1.subset, and_iff_left hP.2]
    · exact subset_union_left _ _
    exact (subset_union_right _ _).trans hP.1.subset_ground_right
  right_inv := by
    rintro ⟨P, hP⟩
    simp only [Subtype.mk.injEq]
    rw [diff_eq_diff_inter_of_subset hP.subset_ground_right, ← cl_inter_ground,
      diff_union_eq_union_of_subset P (M.subset_cl (C ∩ M.E)), union_eq_left, cl_inter_ground]
    exact hP.subset

theorem encard_ground_eq_encard_loops_add_sum_points (M : Matroid α) : M.E.encard =
    (M.cl ∅).encard + ∑' P : {P // M.Point P}, ((P : Set α) \ M.cl ∅).encard := by
  rw [(M.cl_flat ∅).ground_encard_eq_tsum, tsum_congr_subtype (f := fun F ↦ encard (F \ M.cl ∅))]
  simp [loops_covby_iff]

theorem Point.eq_or_eq_of_flat_of_subset (hP : M.Point P) (hF : M.Flat F) (h : F ⊆ P) :
    F = M.cl ∅ ∨ F = P :=
  hP.covby.eq_or_eq hF hF.loops_subset h

theorem Point.subset_or_inter_eq_loops_of_flat (hP : M.Point P) (hF : M.Flat F) :
    P ⊆ F ∨ P ∩ F = M.cl ∅ := by
  obtain (h | h) := hP.eq_or_eq_of_flat_of_subset (hP.flat.inter hF) (inter_subset_left _ _)
  · exact Or.inr h
  exact Or.inl (inter_eq_left.1 h)

-- /-- Each flat `F` induces a partition of the set of points not contained in `F`. -/
-- def Flat.covbyPointPartition {F : Set α} (hF : M.Flat F) :
--     Partition {P | M.Point P ∧ ¬ (P ⊆ F)} := Partition.ofPairwiseDisjoint'
--   (parts := (fun F' ↦ {P | P ⊆ F' ∧ ¬ (P ⊆ F)}) '' hF.covbyPartition)
--   (pairwiseDisjoint := by
--     rintro Ps ⟨_, h, rfl⟩
--     simp

--     )
--   (forall_nonempty := sorry)
--   (eq_sUnion := sorry)





@[pp_dot] abbrev Line (M : Matroid α) (L : Set α) := M.Flat L ∧ M.er L = 2

theorem Line.flat (hL : M.Line L) : M.Flat L :=
  hL.1

theorem Line.er (hL : M.Line L) : M.er L = 2 :=
  hL.2

@[aesop unsafe 10% (rule_sets [Matroid])]
theorem Line.subset_ground (hL : M.Line L) : L ⊆ M.E :=
  hL.1.subset_ground

theorem Line.mem_iff_covby (hL : M.Line L) (he : M.Nonloop e) : e ∈ L ↔ M.cl {e} ⋖[M] L := by
  rw [(M.cl_flat {e}).covby_iff_relRank_eq_one hL.flat, hL.flat.cl_subset_iff_subset,
    singleton_subset_iff, iff_self_and, relRank_cl_left]
  intro heL
  rw [(M.rFin_singleton e).relRank_eq_sub (by simpa), he.er_eq, hL.er]
  rfl

theorem Nonloop.cl_covby_iff (he : M.Nonloop e) : M.cl {e} ⋖[M] L ↔ M.Line L ∧ e ∈ L := by
  refine ⟨fun h ↦ ⟨⟨h.flat_right, ?_⟩,h.subset <| M.mem_cl_self e⟩,
    fun ⟨hL, heL⟩ ↦ by rwa [← hL.mem_iff_covby he]⟩
  rw [h.er_eq, er_cl_eq, he.er_eq]
  rfl

def Nonloop.lineContractPointEquiv (he : M.Nonloop e) :
    {P // (M ⧸ e).Point P} ≃ {L // M.Line L ∧ e ∈ L} :=
  (M.pointContractCovbyEquiv {e}).trans (Equiv.subtypeEquivRight (fun _ ↦ he.cl_covby_iff))

@[pp_dot] abbrev Plane (M : Matroid α) (P : Set α) := M.Flat P ∧ M.er P = 3

theorem Plane.flat (hP : M.Plane P) : M.Flat P :=
  hP.1

theorem Plane.er (hP : M.Plane P) : M.er P = 3 :=
  hP.2

end LowRank

-- section from_axioms
-- lemma matroid_of_flat_aux [finite E] (flat : set α → Prop) (univ_flat : flat univ)
-- (flat_inter : ∀ F₁ F₂, flat F₁ → flat F₂ → flat (F₁ ∩ F₂)) (X : set α) :
--   flat (⋂₀ {F | flat F ∧ X ⊆ F}) ∧ ∀ F₀, flat F₀ → ((⋂₀ {F | flat F ∧ X ⊆ F}) ⊆ F₀ ↔ X ⊆ F₀) :=
-- begin
--   set F₁ := ⋂₀ {F | flat F ∧ X ⊆ F} with hF₁,
--   refine ⟨_, λ F₀ hF₀, ⟨λ hF₁F₀, _, λ hXF, _⟩⟩ ,
--   { obtain ⟨F',⟨hF',hYF'⟩,hmin⟩ := finite.exists_minimal (λ F, flat F ∧ X ⊆ F)
--       ⟨univ, univ_flat, subset_univ _⟩,
--     convert hF',
--     refine subset_antisymm (sInter_subset_of_mem ⟨hF',hYF'⟩) (subset_sInter _),
--     rintro F ⟨hF,hYF⟩,
--     rw hmin _ ⟨flat_inter _ _ hF hF', subset_inter hYF hYF'⟩ _,
--     { apply inter_subset_left},
--     apply inter_subset_right},
--   { refine subset_trans (subset_sInter (λ F h, _)) hF₁F₀, exact h.2},
--   apply sInter_subset_of_mem,
--   exact ⟨hF₀, hXF⟩,
-- end
-- /-- A collection of sets satisfying the flat axioms determines a matroid -/
-- def matroid_of_flat [finite E] (flat : set α → Prop) (univ_flat : flat univ)
-- (flat_inter : ∀ F₁ F₂, flat F₁ → flat F₂ → flat (F₁ ∩ F₂))
-- (flat_partition : ∀ F₀ e, flat F₀ → e ∉ F₀ →
--   ∃! F₁, flat F₁ ∧ insert e F₀ ⊆ F₁ ∧ ∀ F, flat F → F₀ ⊆ F → F ⊂ F₁ → F₀ = F) :=
-- matroid_of_cl_of_finite (λ X, ⋂₀ {F | flat F ∧ X ⊆ F})
-- (λ X, subset_sInter (λ F, and.right))
-- (λ X Y hXY, subset_sInter (λ F hF, by {apply sInter_subset_of_mem, exact ⟨hF.1, hXY.trans hF.2⟩}))
-- (begin
--   refine λ X, (subset_sInter (λ F, and.right)).antisymm' _,
--   simp only [subset_sInter_iff, mem_set_of_eq, and_imp],
--   rintro F hF hXF,
--   apply sInter_subset_of_mem,
--   split, assumption,
--   apply sInter_subset_of_mem,
--   exact ⟨hF, hXF⟩,
-- end )
-- (begin
--   simp only [mem_diff, mem_sInter, mem_set_of_eq, and_imp, not_forall, exists_prop,
--     forall_exists_index],
--   refine λ X e f h F₀ hF₀ hXF₀ hfF₀, ⟨λ Ff hFf hfXf, _,
--     ⟨F₀, hF₀, hXF₀, λ heF₀, hfF₀ (h _ hF₀ (insert_subset.mpr ⟨heF₀,hXF₀⟩))⟩⟩,
--   obtain ⟨hFX, hX'⟩    := matroid_of_flat_aux flat univ_flat flat_inter X,
--   obtain ⟨hFXe, hXe'⟩  := matroid_of_flat_aux flat univ_flat flat_inter (insert e X),
--   obtain ⟨hFXf, hXf'⟩  := matroid_of_flat_aux flat univ_flat flat_inter (insert f X),
--   set FX := sInter {F | flat F ∧ X ⊆ F} with hFX_def,
--   set FXe := sInter {F | flat F ∧ insert e X ⊆ F} with hFXe_def,
--   set FXf := sInter {F | flat F ∧ insert f X ⊆ F} with hFXe_def,
--   apply (hXf' Ff hFf).mpr hfXf,
--   have heFXe : e ∈ FXe := mem_sInter.mpr (λ _ hF, hF.2 (mem_insert _ _)),
--   have hfFXf : f ∈ FXf := mem_sInter.mpr (λ _ hF, hF.2 (mem_insert _ _)),
--   have hXFX : X ⊆ FX := subset_sInter (λ _, and.right),
--   have hfFX : f ∉ FX := λ hfFX, hfF₀ ((hX' F₀ hF₀).mpr hXF₀ hfFX),
--   have heFX : e ∉ FX := λ heFX, hfFX (h _ hFX (insert_subset.mpr ⟨heFX, hXFX⟩)),
--   have hFXFXe : FX ⊆ FXe,
--   { rw [hX' FXe hFXe], exact subset_sInter (λ F hF, (subset_insert _ _).trans hF.2)},
--   have hFXFXf : FX ⊆ FXf,
--   { rw [hX' FXf hFXf], exact subset_sInter (λ F hF, (subset_insert _ _).trans hF.2)},
--   have hfFXe := h FXe hFXe (insert_subset.mpr ⟨heFXe,hXFX.trans hFXFXe⟩),
--   have hss := (hXf' _ hFXe).mpr (insert_subset.mpr ⟨hfFXe, hXFX.trans hFXFXe⟩),
--   suffices h_eq : FXf = FXe, by rwa h_eq,
--   by_contra h_ne, apply hfFX,
--   have hssu := ssubset_of_subset_of_ne hss h_ne,
--   obtain ⟨FXe',⟨hFXe',heFX',hmin⟩, hunique⟩ := flat_partition FX e hFX heFX,
--   have hFXemin : ∀ (F : set α), flat F → FX ⊆ F → F ⊂ FXe → FX = F, from
--   λ F hF hFXF hFFXe, hmin _ hF hFXF
--     (hFFXe.trans_subset ((hXe' _ hFXe').mpr ((insert_subset_insert hXFX).trans heFX'))),
--   rw hunique FXe ⟨hFXe, insert_subset.mpr ⟨heFXe, hFXFXe⟩, hFXemin⟩ at hssu,
--   rwa ← (hmin _ hFXf hFXFXf hssu) at hfFXf,
-- end)
-- @[simp] lemma matroid_of_flat_apply [finite E] (flat : set α → Prop) (univ_flat : flat univ)
-- (flat_inter : ∀ F₁ F₂, flat F₁ → flat F₂ → flat (F₁ ∩ F₂))
-- (flat_partition : ∀ F₀ e, flat F₀ → e ∉ F₀ →
-- ∃! F₁, flat F₁ ∧ insert e F₀ ⊆ F₁ ∧ ∀ F, flat F → F₀ ⊆ F → F ⊂ F₁ → F₀ = F) :
--   (matroid_of_flat flat univ_flat flat_inter flat_partition).flat = flat :=
-- begin
--   ext F,
--   simp_rw [matroid_of_flat, matroid.flat_iff_cl_self, matroid_of_cl_of_finite_apply],
--   refine ⟨λ hF, _, λ hF, _⟩,
--   { rw ← hF, exact (matroid_of_flat_aux flat univ_flat flat_inter _).1},
--   exact (subset_sInter (λ F', and.right)).antisymm' (sInter_subset_of_mem ⟨hF,rfl.subset⟩),
-- end
-- end from_axioms
end Matroid
