import Matroid.Minor.Rank
import Matroid.ForMathlib.SetPartition

variable {α : Type*} {M : Matroid α} {I F X Y F' F₀ F₁ F₂ P L H H₁ H₂ H' B C K : Set α} {e f : α}

open Set
namespace Matroid


lemma Flat.eq_ground_of_spanning (hF : M.Flat F) (h : M.Spanning F) : F = M.E := by
  rw [← hF.closure, h.closure_eq]

lemma Flat.spanning_iff (hF : M.Flat F) : M.Spanning F ↔ F = M.E :=
  ⟨hF.eq_ground_of_spanning, by rintro rfl; exact M.ground_spanning⟩

lemma Flat.inter (hF₁ : M.Flat F₁) (hF₂ : M.Flat F₂) : M.Flat (F₁ ∩ F₂) := by
  rw [inter_eq_iInter]; apply Flat.iInter; simp [hF₁, hF₂]

/-- The intersection of an arbitrary collection of flats with the ground set is a flat.
`Flat.iInter` is often more convenient, but this works when the collection is empty. -/
lemma Flat.iInter_inter_ground {ι : Type*} {Fs : ι → Set α} (hFs : ∀ i, M.Flat (Fs i)) :
    M.Flat ((⋂ i, Fs i) ∩ M.E) := by
  obtain (hι | hι) := isEmpty_or_nonempty ι
  · simp
  exact (Flat.iInter hFs).inter M.ground_flat

lemma Flat.biInter {ι : Type*} {Fs : ι → Set α} {s : Set ι} (hs : s.Nonempty)
    (hFs : ∀ i ∈ s, M.Flat (Fs i)) : M.Flat (⋂ i ∈ s, Fs i) := by
  rw [biInter_eq_iInter]
  have := hs.to_subtype
  apply Flat.iInter (by simpa)

lemma Flat.biInter_inter_ground {ι : Type*} {Fs : ι → Set α} {s : Set ι}
    (hFs : ∀ i ∈ s, M.Flat (Fs i)) : M.Flat ((⋂ i ∈ s, Fs i) ∩ M.E) := by
  rw [biInter_eq_iInter]
  exact Flat.iInter_inter_ground (by simpa)

lemma Flat.sInter {Fs : Set (Set α)} (hF : Fs.Nonempty) (h : ∀ F ∈ Fs, M.Flat F) :
    M.Flat (⋂₀ Fs) := by
  rw [sInter_eq_iInter]
  have : Nonempty Fs := Iff.mpr nonempty_coe_sort hF
  exact Flat.iInter (fun ⟨F, hF⟩ ↦ h _ hF)

lemma Flat.sInter_inter_ground {Fs : Set (Set α)} (h : ∀ F ∈ Fs, M.Flat F) :
    M.Flat (⋂₀ Fs ∩ M.E) := by
  rw [sInter_eq_iInter]
  exact Flat.iInter_inter_ground (by simpa)

lemma flat_iff_closure_self (hF : F ⊆ M.E := by aesop_mat) : M.Flat F ↔ M.closure F = F := by
  rw [flat_iff_isClosed', M.closure.isClosed_iff]
  rfl

lemma flat_iff_closure_self' : M.Flat F ↔ M.closure F = F ∧ F ⊆ M.E := by
  rw [flat_iff_isClosed, M.closure.isClosed_iff]
  rfl

lemma flat_map_iff {β : Type*} {f : α → β} (hf : M.E.InjOn f) {F : Set β} :
    (M.map f hf).Flat F ↔ ∃ F₀, M.Flat F₀ ∧ F = f '' F₀ := by
  simp only [flat_iff_closure_self', map_closure_eq, preimage_inter, union_eq_right,
    image_subset_iff, map_ground]
  rw [inter_assoc, inter_eq_self_of_subset_right (subset_preimage_image _ _), subset_image_iff]
  constructor
  · rintro ⟨h, ⟨F, hF, rfl⟩⟩
    replace h := subset_inter h (M.closure_subset_ground _)
    rw [hf.preimage_image_inter hF] at h
    refine ⟨F, ⟨h.antisymm (subset_closure _ _), hF⟩, rfl⟩
  rintro ⟨F, ⟨hF, hFE⟩, rfl⟩
  rw [hf.preimage_image_inter hFE, hF]
  exact ⟨subset_preimage_image _ _, F, hFE, rfl⟩

lemma Flat.map {β : Type*} {f : α → β} (hF : M.Flat F) (hf : M.E.InjOn f) :
    (M.map f hf).Flat (f '' F) :=
  (flat_map_iff hf).2 ⟨F, hF, rfl⟩

lemma flat_iff_closure_self_subset (hF : F ⊆ M.E := by aesop_mat) : M.Flat F ↔ M.closure F ⊆ F := by
  rw [flat_iff_closure_self, subset_antisymm_iff, and_iff_left_iff_imp]
  exact fun _ ↦ M.subset_closure F

lemma flat_iff_closure_self_subset' : M.Flat F ↔ M.closure F ⊆ F ∧ F ⊆ M.E := by
  by_cases hF : F ⊆ M.E
  · rw [and_iff_left hF, flat_iff_closure_self_subset]
  exact iff_of_false (fun h ↦ hF h.subset_ground) (by simp [hF])

lemma exists_mem_closure_not_mem_of_not_flat (h : ¬ M.Flat F) (hF : F ⊆ M.E := by aesop_mat) :
    ∃ e, e ∈ M.closure F \ F := by
  rw [flat_iff_closure_self, subset_antisymm_iff, and_iff_left (M.subset_closure F)] at h
  exact not_subset.1 h

lemma flat_iff_ssubset_closure_insert_forall (hF : F ⊆ M.E := by aesop_mat) :
    M.Flat F ↔ ∀ e ∈ M.E \ F, M.closure F ⊂ M.closure (insert e F) := by
  refine' ⟨fun h e he ↦ (M.closure_subset_closure (subset_insert _ _)).ssubset_of_ne _, fun h ↦ _⟩
  · rw [h.closure]
    exact fun h' ↦ mt ((Set.ext_iff.mp h') e).mpr (not_mem_of_mem_diff he)
      ((M.subset_closure _) (mem_insert _ _))
  rw [flat_iff_closure_self]
  by_contra h'
  obtain ⟨e, he', heF⟩ := exists_of_ssubset (ssubset_of_ne_of_subset (Ne.symm h') (M.subset_closure F))
  have h'' := h e ⟨(M.closure_subset_ground F) he', heF⟩
  rw [← M.closure_insert_closure_eq_closure_insert e F, insert_eq_of_mem he', M.closure_closure] at h''
  exact h''.ne rfl

lemma flat_iff_forall_circuit (hF : F ⊆ M.E := by aesop_mat) :
    M.Flat F ↔ ∀ C e, M.Circuit C → e ∈ C → C ⊆ insert e F → e ∈ F := by
  rw [flat_iff_closure_self]
  refine' ⟨fun h C e hC heC hCF ↦ _, fun h ↦ _⟩
  · rw [← h]
    refine' (M.closure_subset_closure _) (hC.subset_closure_diff_singleton e heC)
    rwa [diff_subset_iff, singleton_union]
  refine' (M.subset_closure F).antisymm' (fun e heF ↦ by_contra fun he' ↦ _)
  obtain ⟨C, hC, heC, hCF⟩ := (mem_closure_iff_exists_circuit_of_not_mem he').mp heF
  exact he' (h C e hC heC hCF)

lemma flat_iff_forall_circuit' :
    M.Flat F ↔ (∀ C e, M.Circuit C → e ∈ C → C ⊆ insert e F → e ∈ F) ∧ F ⊆ M.E := by
  refine' ⟨fun h ↦ ⟨(flat_iff_forall_circuit h.subset_ground).mp h, h.subset_ground⟩, fun h ↦
    (flat_iff_forall_circuit h.2).mpr h.1⟩

lemma Flat.closure_exchange (hF : M.Flat F) (he : e ∈ M.closure (insert f F) \ F) :
    f ∈ M.closure (insert e F) \ F := by
  nth_rw 2 [← hF.closure] at *; exact Matroid.closure_exchange he

lemma Flat.closure_insert_eq_closure_insert_of_mem (hF : M.Flat F) (he : e ∈ M.closure (insert f F) \ F) :
    M.closure (insert e F) = M.closure (insert f F) :=
  Matroid.closure_insert_eq_closure_insert_of_mem (by rwa [hF.closure])

lemma Flat.closure_subset_of_subset (hF : M.Flat F) (h : X ⊆ F) : M.closure X ⊆ F := by
  have h' := M.closure_mono h; rwa [hF.closure] at h'

@[simp] lemma Flat.closure_subset_iff_subset (hF : M.Flat F) : M.closure X ⊆ F ↔ X ⊆ F :=
  ⟨(M.subset_closure X).trans, hF.closure_subset_of_subset⟩

lemma Flat.closure_eq_iff_basis_of_indep (hF : M.Flat F) (hI : M.Indep I) :
    M.closure I = F ↔ M.Basis I F :=
  ⟨by rintro rfl; exact hI.basis_closure, fun h ↦ by rw [← h.closure_eq_closure, hF.closure]⟩

lemma Flat.eq_closure_of_basis (hF : M.Flat F) (hI : M.Basis I F) : F = M.closure I :=
  hI.subset_closure.antisymm (hF.closure_subset_of_subset hI.subset)

lemma Flat.er_insert_eq_add_one (hF : M.Flat F) (he : e ∈ M.E) (heF : e ∉ F) :
    M.er (insert e F) = M.er F + 1 :=
  M.er_insert_eq_add_one F he (hF.closure.symm ▸ heF)

lemma Flat.subset_of_relRank_eq_zero (hF : M.Flat F) (hr : M.relRank F X = 0)
    (hX : X ⊆ M.E := by aesop_mat) : X ⊆ F := by
  rwa [relRank_eq_zero_iff, hF.closure] at hr

lemma Flat.one_le_relRank_of_ssubset (hF : M.Flat F) (hss : F ⊂ X)
    (hX : X ⊆ M.E := by aesop_mat) : 1 ≤ M.relRank F X :=
  ENat.one_le_iff_ne_zero.2 (fun h_eq ↦ hss.not_subset <| hF.subset_of_relRank_eq_zero h_eq)

lemma finite_setOf_flat (M : Matroid α) [M.Finite] : {F | M.Flat F}.Finite :=
  M.ground_finite.finite_subsets.subset (fun _ hF ↦ hF.subset_ground)

lemma uniqueBaseOn_flat_iff {I E : Set α} (hIE : I ⊆ E) : (uniqueBaseOn E I).Flat F ↔ F ⊆ I := by
  simp [flat_iff_closure_self', diff_eq_empty.2 hIE]

@[simp] lemma loopyOn_flat_iff {E : Set α} : (loopyOn E).Flat F ↔ F = E := by
  simp [flat_iff_closure_self', ← subset_antisymm_iff, eq_comm (a := E)]

@[simp] lemma emptyOn_flat_iff : (emptyOn α).Flat F ↔ F = ∅ := by
  simp [← loopyOn_empty]

@[simp] lemma freeOn_flat_iff {E : Set α} : (freeOn E).Flat F ↔ F ⊆ E := by
  simp [← uniqueBaseOn_self, uniqueBaseOn_flat_iff Subset.rfl]



  -- TODO : Cyclic flats.

section Lattice

@[pp_nodot] def FlatOf (M : Matroid α) : Type _ := {F // M.Flat F}

instance {M : Matroid α} : CoeOut M.FlatOf (Set α) where
  coe F := F.val

@[simp] lemma FlatOf.coe_flat (F : M.FlatOf) : M.Flat F :=
  F.2

def Flat.toFlatOf (h : M.Flat F) : M.FlatOf := ⟨_,h⟩

def flatCl (M : Matroid α) (X : Set α) : M.FlatOf := ⟨_, M.closure_flat (X ∩ M.E)⟩

@[simp] lemma coe_flatCl (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    (M.flatCl X : Set α) = M.closure X := by
  nth_rw 2 [← inter_eq_self_of_subset_left hX]
  rfl

@[simp] lemma FlatOf.coe_inj {F F' : M.FlatOf} : (F : Set α) = (F' : Set α) ↔ F = F' :=
  Subtype.coe_inj

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma FlatOf.coe_subset_ground (F : M.FlatOf) : (F : Set α) ⊆ M.E :=
  F.coe_flat.subset_ground

instance flatPartialOrder (M : Matroid α) : PartialOrder M.FlatOf where
  le F₁ F₂ := (F₁ : Set α) ⊆ F₂
  le_refl _ := Subset.rfl
  le_trans _ _ _ h h' := Subset.trans h h'
  le_antisymm := by
    rintro ⟨F, hF⟩ ⟨F', hF'⟩
    simp only [← FlatOf.coe_inj]
    exact Subset.antisymm

@[simp] lemma FlatOf.le_iff {F F' : M.FlatOf} : F ≤ F' ↔ (F : Set α) ⊆ (F' : Set α) := Iff.rfl

@[simp] lemma FlatOf.lt_iff {F F' : M.FlatOf} : F < F' ↔ (F : Set α) ⊂ (F' : Set α) := Iff.rfl

lemma flatCl_mono (M : Matroid α) : Monotone M.flatCl :=
  fun _ _ h ↦ (M.closure_mono (inter_subset_inter_left _ h))

/-- The flats of a matroid form a complete lattice. -/
instance flatLattice (M : Matroid α) : CompleteLattice (FlatOf M) where
  sup F₁ F₂ := M.flatCl (F₁ ∪ F₂)
  le_sup_left F F' :=
    (subset_inter subset_union_left F.2.subset_ground).trans (M.subset_closure _)
  le_sup_right F F' :=
    (subset_inter subset_union_right F'.2.subset_ground).trans (M.subset_closure _)
  sup_le := by
    rintro ⟨F₁, hF₁⟩ ⟨F₂, hF₂⟩ ⟨F₃, hF₃⟩ (h : F₁ ⊆ F₃) (h' : F₂ ⊆ F₃)
    exact (M.closure_subset_closure (inter_subset_left.trans (union_subset h h'))).trans_eq
      hF₃.closure
  inf F₁ F₂ := ⟨F₁ ∩ F₂, F₁.coe_flat.inter F₂.coe_flat⟩
  inf_le_left _ _ := inter_subset_left
  inf_le_right _ _ := inter_subset_right
  le_inf _ _ _ h h' := subset_inter h h'
  sSup Fs := M.flatCl (⋃ F ∈ Fs, F)
  le_sSup Fs F h := F.2.closure.symm.subset.trans <|
    M.closure_subset_closure <| subset_inter (subset_biUnion_of_mem h) F.2.subset_ground
  sSup_le Fs F h := by
    simp only [FlatOf.le_iff, coe_flatCl] at h ⊢
    refine F.coe_flat.closure_subset_of_subset <| inter_subset_left.trans ?_
    simpa only [iUnion_subset_iff, F.coe_flat.closure]
  sInf Fs := ⟨(⋂ F ∈ Fs, F) ∩ M.E, Flat.biInter_inter_ground (by simp)⟩
  sInf_le Fs F h := inter_subset_left.trans (biInter_subset_of_mem (by simpa))
  le_sInf Fs F h := subset_inter (by simpa) F.coe_subset_ground
  top := ⟨M.E, M.ground_flat⟩
  bot := M.flatCl ∅
  le_top F := F.coe_flat.subset_ground
  bot_le F := F.coe_flat.closure_subset_of_subset (by simp)

@[simp] lemma FlatOf.coe_top (M : Matroid α) : ((⊤ : M.FlatOf) : Set α) = M.E := rfl

@[simp] lemma FlatOf.coe_bot (M : Matroid α) : ((⊥ : M.FlatOf) : Set α) = M.closure ∅ :=
  show (M.flatCl ∅ : Set α) = _ by simp [flatCl]

@[simp] lemma FlatOf.coe_sup (F₁ F₂ : M.FlatOf) :
    ((F₁ ⊔ F₂ : M.FlatOf) : Set α) = M.closure (F₁ ∪ F₂) :=
  show (M.flatCl _ : Set α) = _ by
    simp [flatCl, inter_eq_self_of_subset_left (union_subset F₁.2.subset_ground F₂.2.subset_ground)]

@[simp] lemma FlatOf.coe_inf (F₁ F₂ : M.FlatOf) :
    ((F₁ ⊓ F₂ : M.FlatOf) : Set α) = (F₁ : Set α) ∩ F₂ := rfl

@[simp] lemma FlatOf.coe_sSup (Fs : Set M.FlatOf) : sSup Fs = M.closure (⋃ F ∈ Fs, F) :=
  show (M.flatCl _ : Set α) = _ by
    simp only [flatCl]
    rw [inter_eq_self_of_subset_left]
    simpa [iUnion_subset_iff] using (fun F _ ↦ F.2.subset_ground)

@[simp] lemma FlatOf.coe_sInf (Fs : Set M.FlatOf) : sInf Fs = (⋂ F ∈ Fs, F) ∩ M.E := rfl

lemma FlatOf.coe_sInf' {Fs : Set M.FlatOf} (hne : Fs.Nonempty) :
    sInf Fs = (⋂ F ∈ Fs, F : Set α) := by
  simp only [coe_sInf, inter_eq_left]
  exact (biInter_subset_of_mem hne.some_mem).trans (hne.some.coe_subset_ground)

end Lattice



-- ### Covering
/-- `F₀ ⋖[M] F₁` means that `F₀` and `F₁` are strictly nested flats with no flat between them.
  Defined in terms of `CovBy` in the lattice of flats. -/
def CovBy (M : Matroid α) (F₀ F₁ : Set α) : Prop :=
  ∃ (h₀ : M.Flat F₀) (h₁ : M.Flat F₁), h₀.toFlatOf ⋖ h₁.toFlatOf

def WCovBy (M : Matroid α) (F₀ F₁ : Set α) : Prop :=
  ∃ (h₀ : M.Flat F₀) (h₁ : M.Flat F₁), h₀.toFlatOf ⩿ h₁.toFlatOf

notation:25 F₀:50 " ⋖[" M:25 "] " F₁ :75 => CovBy M F₀ F₁

notation:25 F₀:50 " ⩿[" M:25 "] " F₁ :75 => WCovBy M F₀ F₁

lemma FlatOf.covBy_iff (F₀ F₁ : FlatOf M) : F₀ ⋖ F₁ ↔ (F₀ : Set α) ⋖[M] (F₁ : Set α) := by
  simp only [Matroid.CovBy, coe_flat, exists_true_left]; rfl

lemma FlatOf.wcovBy_iff (F₀ F₁ : FlatOf M) : F₀ ⩿ F₁ ↔ (F₀ : Set α) ⩿[M] (F₁ : Set α) := by
  simp only [Matroid.WCovBy, coe_flat, exists_true_left]; rfl

lemma covBy_iff : F₀ ⋖[M] F₁ ↔
    M.Flat F₀ ∧ M.Flat F₁ ∧ F₀ ⊂ F₁ ∧ ∀ F, M.Flat F → F₀ ⊆ F → F ⊆ F₁ → F = F₀ ∨ F = F₁ := by
  simp_rw [CovBy, covBy_iff_lt_and_eq_or_eq]
  refine ⟨fun ⟨h₀, h₁, hlt, hforall⟩ ↦ ⟨h₀, h₁, hlt, fun F hF hF₀ hF₁ ↦ ?_⟩,
    fun ⟨hF₀, hF₁, hss, hforall⟩ ↦ ⟨hF₀, hF₁, hss, ?_⟩⟩
  · obtain (h1 | h2) := hforall ⟨F, hF⟩ hF₀ hF₁
    · exact Or.inl <| congr_arg ((↑) : M.FlatOf → Set α) h1
    exact Or.inr <| congr_arg ((↑) : M.FlatOf → Set α) h2
  rintro ⟨F, hF⟩ (h₀ : F₀ ⊆ F) (h₁ : F ⊆ F₁)
  obtain (rfl | rfl) := hforall F hF h₀ h₁
  · exact Or.inl rfl
  exact Or.inr rfl

lemma WCovBy.flat_left (h : F₀ ⩿[M] F₁) : M.Flat F₀ :=
  h.1

lemma WCovBy.flat_right (h : F₀ ⩿[M] F₁) : M.Flat F₁ :=
  h.2.1

lemma CovBy.flat_left (h : F₀ ⋖[M] F₁) : M.Flat F₀ :=
  h.1

lemma CovBy.flat_right (h : F₀ ⋖[M] F₁) : M.Flat F₁ :=
  h.2.1

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma CovBy.subset_ground_left (h : F₀ ⋖[M] F₁) : F₀ ⊆ M.E :=
  h.flat_left.subset_ground

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma CovBy.subset_ground_right (h : F₀ ⋖[M] F₁) : F₁ ⊆ M.E :=
  h.flat_right.subset_ground

lemma CovBy.ssubset (h : F₀ ⋖[M] F₁) : F₀ ⊂ F₁ :=
  h.2.2.1

lemma CovBy.ne (h : F₀ ⋖[M] F₁) : F₀ ≠ F₁ :=
  h.ssubset.ne

lemma CovBy.subset (h : F₀ ⋖[M] F₁) : F₀ ⊆ F₁ :=
  h.ssubset.subset

lemma WCovBy.subset (h : F₀ ⩿[M] F₁) : F₀ ⊆ F₁ :=
  h.2.2.1

lemma Flat.covBy_iff_wcovBy_and_ne (hF₀ : M.Flat F₀) (hF₁ : M.Flat F₁) :
    F₀ ⋖[M] F₁ ↔ (F₀ ⩿[M] F₁) ∧ F₀ ≠ F₁ := by
  rw [show F₀ = (hF₀.toFlatOf : Set α) from rfl, show F₁ = (hF₁.toFlatOf : Set α) from rfl,
    ← FlatOf.covBy_iff, ← FlatOf.wcovBy_iff, _root_.covBy_iff_wcovBy_and_ne, ne_eq, ne_eq,
    FlatOf.coe_inj]

lemma Flat.covBy_iff_wcovBy_and_ssubset (hF₀ : M.Flat F₀) (hF₁ : M.Flat F₁) :
    F₀ ⋖[M] F₁ ↔ (F₀ ⩿[M] F₁) ∧ F₀ ⊂ F₁ := by
  rw [hF₀.covBy_iff_wcovBy_and_ne hF₁, and_congr_right_iff, ssubset_iff_subset_ne,
    ne_eq, iff_and_self]
  exact fun h _ ↦ h.subset

@[simp] lemma Flat.wCovBy_self (hF : M.Flat F) : F ⩿[M] F := by
  simpa [WCovBy]

lemma Flat.wCovby_iff_covBy_or_eq (hF₀ : M.Flat F₀) (hF₁ : M.Flat F₁) :
    F₀ ⩿[M] F₁ ↔ (F₀ ⋖[M] F₁) ∨ F₀ = F₁ := by
  obtain (rfl | hne) := eq_or_ne F₀ F₁
  · simp [hF₀]
  simp [hF₀, hF₀.covBy_iff_wcovBy_and_ne hF₁, or_iff_not_imp_right, hne]

--TODO : More `WCovby` API.

lemma WCovBy.covBy_of_ne (h : F₀ ⩿[M] F₁) (hne : F₀ ≠ F₁) : F₀ ⋖[M] F₁ :=
    (h.flat_left.covBy_iff_wcovBy_and_ne h.flat_right).2 ⟨h, hne⟩

lemma WCovBy.eq_or_covBy (h : F₀ ⩿[M] F₁) : F₀ = F₁ ∨ (F₀ ⋖[M] F₁) := by
    rw [or_iff_not_imp_left]; exact h.covBy_of_ne

lemma CovBy.wCovby (h : F₀ ⋖[M] F₁) : F₀ ⩿[M] F₁ :=
    (h.flat_left.wCovby_iff_covBy_or_eq h.flat_right).2 <| .inl h

lemma Flat.covBy_iff_of_flat (hF₀ : M.Flat F₀) (hF₁ : M.Flat F₁) :
    F₀ ⋖[M] F₁ ↔ F₀ ⊂ F₁ ∧ ∀ F, M.Flat F → F₀ ⊆ F → F ⊆ F₁ → F = F₀ ∨ F = F₁ := by
  rw [covBy_iff, and_iff_right hF₀, and_iff_right hF₁]

lemma Flat.wcovBy_iff_of_flat (hF₀ : M.Flat F₀) (hF₁ : M.Flat F₁) :
    F₀ ⩿[M] F₁ ↔ F₀ ⊆ F₁ ∧ ∀ F, M.Flat F → F₀ ⊆ F → F ⊆ F₁ → F = F₀ ∨ F = F₁ := by
  obtain (rfl | hne) := eq_or_ne F₀ F₁
  · simp only [hF₀, wCovBy_self, or_self, true_iff]
    exact ⟨Subset.rfl, fun _ _  ↦ antisymm'⟩
  rw [wCovby_iff_covBy_or_eq hF₀ hF₁, subset_iff_ssubset_or_eq, or_iff_left hne, or_iff_left hne,
    hF₀.covBy_iff_of_flat hF₁]

lemma CovBy.eq_or_eq (h : F₀ ⋖[M] F₁) (hF : M.Flat F) (h₀ : F₀ ⊆ F) (h₁ : F ⊆ F₁) :
    F = F₀ ∨ F = F₁ :=
  (covBy_iff.1 h).2.2.2 F hF h₀ h₁

lemma CovBy.eq_of_subset_of_ssubset (h : F₀ ⋖[M] F₁) (hF : M.Flat F) (hF₀ : F₀ ⊆ F) (hF₁ : F ⊂ F₁) :
    F = F₀ :=
  ((covBy_iff.1 h).2.2.2 F hF hF₀ hF₁.subset).elim id fun h' ↦ (hF₁.ne h').elim

lemma CovBy.eq_of_ssubset_of_subset (h : F₀ ⋖[M] F₁) (hF : M.Flat F) (hF₀ : F₀ ⊂ F) (hF₁ : F ⊆ F₁) :
    F = F₁ :=
  ((covBy_iff.1 h).2.2.2 F hF hF₀.subset hF₁).elim (fun h' ↦ (hF₀.ne.symm h').elim) id

lemma CovBy.closure_insert_eq (h : F₀ ⋖[M] F₁) (he : e ∈ F₁ \ F₀) :
    M.closure (insert e F₀) = F₁ := by
  refine
    h.eq_of_ssubset_of_subset (M.closure_flat _ ?_)
      ((ssubset_insert he.2).trans_subset (M.subset_closure _))
      (h.flat_right.closure_subset_of_subset (insert_subset he.1 h.ssubset.subset))
  rw [insert_eq, union_subset_iff, singleton_subset_iff]
  exact ⟨h.flat_right.subset_ground he.1, h.flat_left.subset_ground⟩

lemma CovBy.exists_eq_closure_insert (h : F₀ ⋖[M] F₁) :
    ∃ e ∈ F₁ \ F₀, M.closure (insert e F₀) = F₁ := by
  obtain ⟨e, he⟩ := exists_of_ssubset h.ssubset
  exact ⟨e, he, h.closure_insert_eq he⟩

lemma CovBy.exists_eq_closure_insert' (h : M.closure X ⋖[M] F) :
    ∃ e ∈ F \ M.closure X, F = M.closure (insert e X) := by
  obtain ⟨e, he, rfl⟩ := h.exists_eq_closure_insert
  exact ⟨e, he, by simp⟩

lemma Flat.covBy_iff_eq_closure_insert (hF₀ : M.Flat F₀) :
    F₀ ⋖[M] F₁ ↔ ∃ e ∈ M.E \ F₀, F₁ = M.closure (insert e F₀) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨e, he, rfl⟩ := h.exists_eq_closure_insert
    refine ⟨e, ⟨(M.closure_subset_ground _ ?_) he.1, he.2⟩, rfl⟩
    exact (M.subset_closure _).trans h.subset_ground_right
  rintro ⟨e, heF₀, rfl⟩
  refine covBy_iff.2
    ⟨hF₀, M.closure_flat _, (M.subset_closure_of_subset (subset_insert _ _)).ssubset_of_ne ?_,
      fun F hF hF₀F hFF₁ ↦ ?_⟩
  · exact fun h ↦ heF₀.2 (h.symm.subset (mem_closure_of_mem _ (mem_insert _ _)))
  refine hF₀F.eq_or_ssubset.elim (fun h ↦ Or.inl h.symm)
    (fun hss ↦ Or.inr (hFF₁.antisymm (hF.closure_subset_of_subset (insert_subset ?_ hF₀F))))
  obtain ⟨f, hfF, hfF₀⟩ := exists_of_ssubset hss
  exact mem_of_mem_of_subset (hF₀.closure_exchange ⟨hFF₁ hfF, hfF₀⟩).1
    (hF.closure_subset_of_subset (insert_subset hfF hF₀F))

lemma CovBy.er_eq (h : F ⋖[M] F') : M.er F' = M.er F + 1 := by
  obtain ⟨e, he, rfl⟩ := h.exists_eq_closure_insert
  rw [er_closure_eq, h.flat_left.er_insert_eq_add_one (h.subset_ground_right he.1) he.2]

lemma closure_covBy_iff (hX : X ⊆ M.E := by aesop_mat):
    (M.closure X) ⋖[M] F ↔ ∃ e ∈ M.E \ M.closure X, F = M.closure (insert e X) := by
  simp_rw [(M.closure_flat X).covBy_iff_eq_closure_insert, closure_insert_closure_eq_closure_insert]

lemma Flat.covBy_closure_insert (hF : M.Flat F) (he : e ∉ F) (heE : e ∈ M.E := by aesop_mat) :
    F ⋖[M] M.closure (insert e F) :=
  hF.covBy_iff_eq_closure_insert.2 ⟨e, ⟨heE, he⟩, rfl⟩

lemma closure_covBy_closure_iff (hX : X ⊆ M.E := by aesop_mat) : (M.closure X) ⋖[M] (M.closure Y) ↔
    ∃ e ∈ M.E, e ∈ Y ∧ e ∉ M.closure X ∧ M.closure (insert e X) = M.closure Y := by
  by_cases hY : Y ⊆ M.E
  · refine ⟨fun h ↦ ?_, fun ⟨e, he, _, heX, h_eq⟩ ↦ ?_⟩
    · obtain ⟨e, heY, heX⟩ := exists_of_closure_ssubset h.ssubset
      refine ⟨e, hY heY, heY, heX, ?_⟩
      rw [← h.closure_insert_eq ⟨M.subset_closure Y heY, heX⟩,
        closure_insert_closure_eq_closure_insert]
    rw [← h_eq]
    rw [← closure_insert_closure_eq_closure_insert]
    exact (M.closure_flat X).covBy_closure_insert heX
  refine iff_of_false (fun h ↦ hY ((M.subset_closure Y).trans h.subset_ground_right))
    (fun ⟨e, he, _, _, h_eq⟩ ↦ hY (closure_subset_ground_iff.1 ?_))
  rw [← h_eq, closure_subset_ground_iff]
  exact insert_subset he hX

lemma Indep.closure_diff_covBy (hI : M.Indep I) (he : e ∈ I) :
    M.closure (I \ {e}) ⋖[M] M.closure I := by
  rw [closure_covBy_closure_iff (diff_subset.trans hI.subset_ground)]
  exact ⟨e, by simp [he, hI.subset_ground he, hI.not_mem_closure_diff_of_mem he]⟩

lemma Indep.covBy_closure_insert (hI : M.Indep I) (he : e ∈ M.E \ M.closure I) :
    M.closure I ⋖[M] M.closure (insert e I) := by
  simpa [not_mem_of_mem_diff_closure he] using
    (hI.insert_indep_iff.2 <| .inl he).closure_diff_covBy (.inl rfl)

lemma CovBy.eq_closure_insert_of_mem_diff (h : F ⋖[M] F') (he : e ∈ F' \ F) : F' = M.closure (insert e F) :=
  Eq.symm <| h.eq_of_ssubset_of_subset (M.closure_flat (insert e F)
      (insert_subset (h.subset_ground_right he.1) h.subset_ground_left))
    (h.flat_left.covBy_closure_insert he.2 (h.flat_right.subset_ground he.1)).ssubset
    (h.flat_right.closure_subset_of_subset (insert_subset he.1 h.subset))

lemma Flat.covBy_iff_relRank_eq_one (hF₀ : M.Flat F₀) (hF : M.Flat F) :
    F₀ ⋖[M] F ↔ F₀ ⊆ F ∧ M.relRank F₀ F = 1 := by
  simp_rw [hF₀.covBy_iff_eq_closure_insert, relRank_eq_one_iff hF.subset_ground, hF₀.closure]
  refine ⟨?_, fun ⟨hss, e, he, h⟩ ↦ ⟨e, ?_, h.antisymm ?_⟩⟩
  · rintro ⟨e, ⟨-, heE⟩, rfl⟩
    refine ⟨M.subset_closure_of_subset (subset_insert _ _), ⟨e, ⟨?_, heE⟩, rfl.subset⟩⟩
    exact M.mem_closure_of_mem (mem_insert _ _)
  · apply diff_subset_diff_left hF.subset_ground he
  exact hF.closure_subset_iff_subset.2 <| insert_subset he.1 hss

lemma CovBy.relRank_eq_one (h : F₀ ⋖[M] F₁) : M.relRank F₀ F₁ = 1 :=
  ((h.flat_left.covBy_iff_relRank_eq_one h.flat_right).1 h).2

lemma covBy_iff_relRank_eq_one :
    F₀ ⋖[M] F₁ ↔ M.Flat F₀ ∧ M.Flat F₁ ∧ F₀ ⊆ F₁ ∧ M.relRank F₀ F₁ = 1 :=
  ⟨fun h ↦ ⟨h.flat_left, h.flat_right, h.subset, h.relRank_eq_one⟩,
    fun ⟨hF₀, hF₁, hss, hr⟩ ↦ (hF₀.covBy_iff_relRank_eq_one hF₁).2 ⟨hss, hr⟩⟩

lemma Flat.exists_unique_flat_of_not_mem (hF₀ : M.Flat F₀) (he : e ∈ M.E \ F₀) :
    ∃! F₁, e ∈ F₁ ∧ (F₀ ⋖[M] F₁) := by
  simp_rw [hF₀.covBy_iff_eq_closure_insert]
  use M.closure (insert e F₀)
  refine ⟨⟨M.mem_closure_of_mem (mem_insert _ _), ⟨e, he, rfl⟩⟩, ?_⟩
  simp only [exists_prop, and_imp, forall_exists_index]
  rintro X heX f _ rfl
  rw [hF₀.closure_insert_eq_closure_insert_of_mem ⟨heX, he.2⟩]

/-- If `F` covers distinct flats `F₀` and `F₁`, then `F` is their join. -/
lemma CovBy.eq_closure_union_of_covBy_of_ne (h₀ : F₀ ⋖[M] F) (h₁ : F₁ ⋖[M] F) (hne : F₀ ≠ F₁) :
    F = M.closure (F₀ ∪ F₁) := by
  refine subset_antisymm ?_ (h₁.flat_right.closure_subset_of_subset (union_subset h₀.subset h₁.subset))
  have hnss : ¬ (F₀ ⊆ F₁) :=
    fun hss ↦ hne.symm <| h₀.eq_of_subset_of_ssubset h₁.flat_left hss h₁.ssubset
  obtain ⟨e, he₀, he₁⟩ := not_subset.1 hnss
  obtain rfl := h₁.closure_insert_eq ⟨h₀.subset he₀, he₁⟩
  exact M.closure_subset_closure (insert_subset (Or.inl he₀) subset_union_right)

lemma Flat.exists_left_covBy_of_ssubset (hF₀ : M.Flat F₀) (hF₁ : M.Flat F₁) (hss : F₀ ⊂ F₁) :
    ∃ F, ((F₀ ⋖[M] F) ∧ F ⊆ F₁) := by
  obtain ⟨e, he⟩ := exists_of_ssubset hss
  exact ⟨_, hF₀.covBy_closure_insert he.2 (hF₁.subset_ground he.1),
    hF₁.closure_subset_of_subset <| insert_subset he.1 hss.subset⟩

lemma Flat.exists_covBy_right_of_ssubset (hF₀ : M.Flat F₀) (hF₁ : M.Flat F₁) (hss : F₀ ⊂ F₁) :
    ∃ F, (F₀ ⊆ F ∧ (F ⋖[M] F₁)) := by
  obtain ⟨I, J, hI, hJ, hIJ⟩ := M.exists_basis_subset_basis hss.subset
  have hssu : I ⊂ J := hIJ.ssubset_of_ne <| by
    rintro rfl
    rw [hF₀.eq_closure_of_basis hI, hF₁.eq_closure_of_basis hJ] at hss
    exact hss.ne rfl
  obtain ⟨e, heJ, heI⟩ := exists_of_ssubset hssu
  refine ⟨M.closure (J \ {e}), hI.subset_closure.trans
    (M.closure_subset_closure (subset_diff_singleton hIJ heI)), ?_⟩
  convert (M.closure_flat (J \ {e})
    (diff_subset.trans hJ.indep.subset_ground)).covBy_closure_insert ?_ (hJ.indep.subset_ground heJ)
  · rw [closure_insert_closure_eq_closure_insert, insert_diff_singleton, insert_eq_of_mem heJ,
      hF₁.eq_closure_of_basis hJ]
  exact hJ.indep.not_mem_closure_diff_of_mem heJ

lemma CovBy.covBy_closure_union_of_inter_covBy (h₀ : F₀ ∩ F₁ ⋖[M] F₀) (h₁ : F₀ ∩ F₁ ⋖[M] F₁) :
    F₀ ⋖[M] M.closure (F₀ ∪ F₁) := by
  obtain ⟨e₀, -, h₀'⟩ := h₀.exists_eq_closure_insert
  obtain ⟨e₁, he₁, h₁'⟩ := h₁.exists_eq_closure_insert
  nth_rw 2 [← h₀', ← h₁']
  rw [closure_closure_union_closure_eq_closure_union, ← singleton_union, ← singleton_union,
    ← union_union_distrib_right, union_comm {e₀}, union_assoc, singleton_union, singleton_union,
    ← M.closure_insert_closure_eq_closure_insert, h₀']
  exact h₀.flat_right.covBy_closure_insert (fun h ↦ he₁.2 ⟨h, he₁.1⟩) (h₁.flat_right.subset_ground he₁.1)

instance {M : Matroid α} : IsWeakUpperModularLattice M.FlatOf where
  covBy_sup_of_inf_covBy_covBy := by
    rintro ⟨F₀, hF₀⟩ ⟨F₁, hF₁⟩
    simp only [ge_iff_le, FlatOf.le_iff, FlatOf.covBy_iff, FlatOf.coe_inf, FlatOf.coe_sup]
    exact CovBy.covBy_closure_union_of_inter_covBy

/-- If `M.relRank F₀ F₁ = 2` for flats `F₀, F₁`, then every flat strictly between
  `F₀` and `F₁` covers `F₀` and is covered by `F₁`. -/
lemma Flat.covBy_and_covBy_of_ssubset_of_ssubset_of_relRank_eq_two (hF₀ : M.Flat F₀)
    (hF₁ : M.Flat F₁) (h : M.relRank F₀ F₁ = 2) (hF : M.Flat F) (h₀ : F₀ ⊂ F) (h₁ : F ⊂ F₁) :
    (F₀ ⋖[M] F) ∧ (F ⋖[M] F₁) := by
  have h0le := hF₀.one_le_relRank_of_ssubset h₀
  have h1le := hF.one_le_relRank_of_ssubset h₁
  rw [← M.relRank_add_of_subset_of_subset h₀.subset h₁.subset] at h
  have h0top : M.relRank F₀ F ≠ ⊤ := by
    intro h'; rw [h'] at h; norm_cast at h
  have h1top : M.relRank F F₁ ≠ ⊤ := by
    intro h'; rw [h', add_top] at h; norm_cast at h
  have hle1 := WithTop.le_of_add_le_add_left h0top <| h.le.trans (add_le_add_right h0le 1)
  have hle0 := WithTop.le_of_add_le_add_right h1top <| h.le.trans (add_le_add_left h1le 1)
  rw [hF₀.covBy_iff_relRank_eq_one hF, hF.covBy_iff_relRank_eq_one hF₁,
    and_iff_right h₀.subset, and_iff_right h₁.subset]
  exact ⟨hle0.antisymm h0le, hle1.antisymm h1le⟩

/-- If some flat is covered by `F₁` and covers `F₀`,
  then this holds for every flat strictly between `F₀` and `F₁`. -/
lemma CovBy.covBy_and_covBy_of_covBy_of_ssubset_of_ssubset (hF₀F' : F₀ ⋖[M] F')
    (hF'F₁ : F' ⋖[M] F₁) (hF : M.Flat F) (h₀ : F₀ ⊂ F) (h₁ : F ⊂ F₁) :
    (F₀ ⋖[M] F) ∧ (F ⋖[M] F₁) := by
  apply hF₀F'.flat_left.covBy_and_covBy_of_ssubset_of_ssubset_of_relRank_eq_two hF'F₁.flat_right
    ?_ hF h₀ h₁
  rw [← M.relRank_add_of_subset_of_subset hF₀F'.subset hF'F₁.subset, hF'F₁.relRank_eq_one,
    hF₀F'.relRank_eq_one]
  rfl

/-- The flats covering a flat `F` induce a partition of `M.E \ F`. -/
@[simps!] def Flat.covByPartition (hF : M.Flat F) : Partition (M.E \ F) :=
  Partition.ofPairwiseDisjoint'
    (parts := (· \ F) '' {F' | F ⋖[M] F'})
    (pairwiseDisjoint := by
      rintro _ ⟨F₁, hF₁, rfl⟩  _ ⟨F₂, hF₂, rfl⟩ hne
      refine disjoint_iff_forall_ne.2 ?_
      rintro e (he₁ : e ∈ F₁ \ F) _ (he₂ : _ ∈ F₂ \ F) rfl
      rw [← hF₁.closure_insert_eq he₁, ← hF₂.closure_insert_eq he₂] at hne
      exact hne rfl )
    (forall_nonempty := by rintro _ ⟨_, hF₁, rfl⟩; exact exists_of_ssubset hF₁.ssubset )
    (eq_sUnion := by
      simp only [sUnion_image, mem_setOf_eq, ext_iff, mem_diff, mem_iUnion, exists_and_left,
        exists_prop]
      exact fun e ↦ ⟨fun ⟨he,heF⟩ ↦
        ⟨M.closure (insert e F), M.mem_closure_of_mem (mem_insert _ _), hF.covBy_closure_insert heF, heF⟩,
        fun ⟨F', heF', hlt, h⟩ ↦ ⟨hlt.flat_right.subset_ground heF', h⟩⟩ )

@[simp] lemma Flat.mem_covByPartition_iff {X : Set α} (hF : M.Flat F) :
    X ∈ hF.covByPartition ↔ ∃ F', ((F ⋖[M] F') ∧ F' \ F = X) := by
  simp [Flat.covByPartition]

@[simp] lemma Flat.partOf_covByPartition_eq (hF : M.Flat F) (e : α) (he : e ∈ M.E := by aesop_mat) :
    hF.covByPartition.partOf e = M.closure (insert e F) \ F := by
  by_cases heF : e ∈ F
  · rw [hF.covByPartition.partOf_eq_empty (fun h ↦ h.2 heF),
      insert_eq_of_mem heF, hF.closure, diff_self]
  obtain ⟨F', hFF', hF'⟩ :=
    hF.mem_covByPartition_iff.1 (hF.covByPartition.partOf_mem (show e ∈ M.E \ F from ⟨he, heF⟩))
  rw [← hF', hFF'.closure_insert_eq]
  rw [hF']
  exact Partition.mem_partOf hF.covByPartition ⟨he, heF⟩

@[simp] lemma Flat.rel_covByPartition_iff (hF : M.Flat F) {e f : α} :
    hF.covByPartition.Rel e f ↔
      e ∈ M.E \ F ∧ f ∈ M.E \ F ∧ M.closure (insert e F) = M.closure (insert f F) := by
  simp only [hF.covByPartition.rel_iff_partOf_eq_partOf', mem_diff, exists_prop,
    and_congr_right_iff, and_imp]
  intro he _ hf _
  rw [partOf_covByPartition_eq _ _ he, partOf_covByPartition_eq _ _ hf, subset_antisymm_iff,
    diff_subset_iff, diff_subset_iff]
  simp_rw [union_diff_self,
    union_eq_self_of_subset_left (subset_closure_of_subset _ (subset_insert _ _)),
    subset_antisymm_iff]

lemma Flat.rel_covByPartition_iff' (hF : M.Flat F) (he : e ∈ M.E \ F) :
    hF.covByPartition.Rel e f ↔ M.closure (insert e F) = M.closure (insert f F) := by
  rw [hF.rel_covByPartition_iff, and_iff_right he, and_iff_right_iff_imp]
  refine fun hcl ↦ ⟨mem_of_mem_of_subset ?_ (hcl.symm.subset.trans ?_), fun hfF ↦ ?_⟩
  · exact mem_closure_of_mem _ (by simp)
  · exact M.closure_subset_ground _ (by aesop_mat)
  rw [insert_eq_of_mem hfF, hF.closure] at hcl
  exact he.2 <| hcl.subset (M.mem_closure_of_mem (mem_insert e F))

/-- Cells of the `covByPartition` induced by `F₀` are equivalent to flats covering `F₀`.-/
@[simps] def Flat.equivCovByPartition (hF₀ : M.Flat F₀) :
    ↑(hF₀.covByPartition : Set (Set α)) ≃ {F // F₀ ⋖[M] F} where
  toFun F := ⟨F ∪ F₀, by
    obtain ⟨_, ⟨F, hF : F₀ ⋖[M] F, rfl⟩⟩ := F
    simpa [union_eq_self_of_subset_right hF.subset]⟩
  invFun F := ⟨F \ F₀, by
    simp only [SetLike.mem_coe, mem_covByPartition_iff]
    exact ⟨_, F.prop, rfl⟩ ⟩
  left_inv := by rintro ⟨_, ⟨F, hF : F₀ ⋖[M] F, rfl⟩⟩; simp
  right_inv := by rintro ⟨F, hF⟩; simp [hF.subset]

-- this needs `ENatTopology`
-- lemma Flat.ground_encard_eq_tsum (hF₀ : M.Flat F₀) :
--     M.E.encard = F₀.encard + ∑' F : {F // F₀ ⋖[M] F}, ((F : Set α) \ F₀).encard := by
--   rw [← encard_diff_add_encard_of_subset hF₀.subset_ground, add_comm]
--   apply congr_arg (_ + ·)
--   have hcard := ENat.tsum_encard_eq_encard_sUnion hF₀.covByPartition.pairwiseDisjoint
--   simp only [SetLike.coe_sort_coe, Partition.sUnion_eq] at hcard
--   rw [← ENat.tsum_comp_eq_tsum_of_equiv hF₀.equivCovByPartition (fun F ↦ encard ((F : Set α) \ F₀)),
--     ← hcard]
--   apply tsum_congr
--   rintro ⟨_, ⟨F, hF : F₀ ⋖[M] F, rfl⟩⟩
--   rw [hF₀.equivCovByPartition_apply_coe, diff_union_self, union_diff_right]

section Minor

lemma flat_contract (X C : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    (M ／ C).Flat (M.closure (X ∪ C) \ C) := by
  rw [flat_iff_closure_self _, contract_closure_eq]
  · simp [union_assoc, (sdiff_eq_left (x := C)).2 disjoint_sdiff_right]
  rw [contract_ground, diff_subset_iff, union_diff_self, union_comm (b := M.E)]
  refine (M.closure_subset_ground_union _).trans ?_
  rw [← union_assoc, union_eq_self_of_subset_right hX]

@[simp] lemma flat_contract_iff (hC : C ⊆ M.E := by aesop_mat) :
    (M ／ C).Flat F ↔ M.Flat (F ∪ C) ∧ Disjoint F C := by
  rw [flat_iff_closure_self_subset', contract_closure_eq, contract_ground, subset_diff,
    diff_subset_iff, diff_union_self, flat_iff_closure_self_subset', union_subset_iff,
    and_iff_left hC, union_comm, and_assoc]

lemma Flat.union_flat_of_contract (hF : (M ／ C).Flat F) (hC : C ⊆ M.E := by aesop_mat) :
    M.Flat (F ∪ C) :=
  ((flat_contract_iff hC).1 hF).1

lemma flat_contract_iff' :
    (M ／ C).Flat F ↔ (M.Flat (F ∪ (C ∩ M.E)) ∧ Disjoint F (C ∩ M.E)) := by
  rw [← contract_inter_ground_eq, flat_contract_iff]

lemma Flat.union_flat_of_contract' (hF : (M ／ C).Flat F) (hC : C ⊆ M.E := by aesop_mat) :
    M.Flat (F ∪ M.closure C) := by
  rw [flat_contract_iff] at hF
  rwa [flat_iff_closure_self_subset', closure_union_closure_right_eq, hF.1.closure,
    and_iff_right (union_subset_union_right _ (M.subset_closure C)), union_subset_iff,
    and_iff_right (subset_union_left.trans hF.1.subset_ground), closure_subset_ground_iff]

lemma Nonloop.contract_flat_iff (he : M.Nonloop e) :
    (M ／ e).Flat F ↔ M.Flat (insert e F) ∧ e ∉ F := by
  rw [contract_elem, flat_contract_iff, union_singleton, disjoint_singleton_right]

/-- Flats of `M ／ C` are equivalent to flats of `M` containing `C`-/
@[simps] def flatContractEquiv (M : Matroid α) (C : Set α) (hC : C ⊆ M.E := by aesop_mat) :
    {F // (M ／ C).Flat F} ≃ {F // M.Flat F ∧ C ⊆ F} where
  toFun F := ⟨F ∪ C, by simp [subset_union_right, F.prop.union_flat_of_contract]⟩
  invFun F := ⟨F \ C, by simp
    [flat_contract_iff hC, union_eq_self_of_subset_right F.prop.2, disjoint_sdiff_left, F.prop.1]⟩
  left_inv := by rintro ⟨-, hF⟩; simp [(subset_diff.1 hF.subset_ground).2]
  right_inv := by rintro ⟨F, hF⟩; simp [hF.2]

lemma flat_restrict_iff {R : Set α} (hR : R ⊆ M.E := by aesop_mat) :
    (M ↾ R).Flat F ↔ ∃ F', M.Flat F' ∧ F = F' ∩ R := by
  refine ⟨fun h ↦ ⟨M.closure F, M.closure_flat F (h.subset_ground.trans hR), ?_⟩, ?_⟩
  · nth_rw 1 [← h.closure]
    have hFR : F ⊆ R := h.subset_ground
    simpa [inter_eq_self_of_subset_left hFR, diff_subset, diff_eq_empty.2 hR]
  rintro ⟨F, hF, rfl⟩
  rw [flat_iff_closure_self_subset]
  suffices M.closure (F ∩ R) ∩ R ⊆ F by simpa [inter_assoc, diff_eq_empty.2 hR]
  exact inter_subset_left.trans (hF.closure_subset_of_subset inter_subset_left)

lemma flat_delete_iff {D : Set α} :
    (M ＼ D).Flat F ↔ ∃ F', M.Flat F' ∧ F = F' \ D := by
  simp_rw [delete_eq_restrict, flat_restrict_iff diff_subset, ← inter_diff_assoc]
  constructor <;>
  · rintro ⟨F, hF, rfl⟩
    refine ⟨F, hF, ?_⟩
    rw [inter_eq_self_of_subset_left hF.subset_ground]

@[simp] lemma flat_deleteElem_iff : (M ＼ e).Flat F ↔ e ∉ F ∧ (M.Flat F ∨ M.Flat (insert e F)) := by
  rw [deleteElem, flat_delete_iff]
  constructor
  · rintro ⟨F, hF, rfl⟩
    obtain (heF | heF) := em (e ∈ F) <;> simp [heF, hF]
  rintro ⟨heF, (hF | hF)⟩ <;> exact ⟨_, hF, by simp [heF]⟩

end Minor

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

lemma Hyperplane.closure_insert_eq (hH : M.Hyperplane H) (heH : e ∉ H) (he : e ∈ M.E := by aesop_mat) :
    M.closure (insert e H) = M.E :=
  hH.covBy.closure_insert_eq ⟨he, heH⟩

lemma Hyperplane.closure_eq_ground_of_ssuperset (hH : M.Hyperplane H) (hX : H ⊂ X)
    (hX' : X ⊆ M.E := by aesop_mat) : M.closure X = M.E := by
  obtain ⟨e, heX, heH⟩ := exists_of_ssubset hX
  exact (M.closure_subset_ground _).antisymm ((hH.closure_insert_eq heH (hX' heX)).symm.trans_subset
    (M.closure_subset_closure (insert_subset heX hX.subset)))

lemma Hyperplane.spanning_of_ssuperset (hH : M.Hyperplane H) (hX : H ⊂ X)
    (hXE : X ⊆ M.E := by aesop_mat) : M.Spanning X := by
  rw [spanning_def, hH.closure_eq_ground_of_ssuperset hX]

lemma Hyperplane.not_spanning (hH : M.Hyperplane H) : ¬M.Spanning H := by
  rw [hH.flat.spanning_iff]; exact hH.ssubset_ground.ne

lemma Hyperplane.flat_superset_eq_ground (hH : M.Hyperplane H) (hF : M.Flat F) (hHF : H ⊂ F) :
    F = M.E := by rw [← hF.closure, hH.closure_eq_ground_of_ssuperset hHF]

lemma hyperplane_iff_maximal_proper_flat :
    M.Hyperplane H ↔ M.Flat H ∧ H ⊂ M.E ∧ ∀ F, H ⊂ F → M.Flat F → F = M.E := by
  rw [hyperplane_iff_covBy, covBy_iff, and_iff_right M.ground_flat, and_congr_right_iff,
    and_congr_right_iff]
  simp_rw [or_iff_not_imp_left, ssubset_iff_subset_ne, and_imp]
  exact fun _ _ _  ↦
    ⟨fun h F hHF hne' hF ↦ h F hF hHF hF.subset_ground hne'.symm, fun h F hF hHF _ hne' ↦
      h F hHF (Ne.symm hne') hF⟩

lemma hyperplane_iff_maximal_nonspanning :
    M.Hyperplane H ↔ H ∈ maximals (· ⊆ ·) {X | ¬M.Spanning X ∧ X ⊆ M.E} := by
  simp_rw [and_comm (b := _ ⊆ _), mem_maximals_setOf_iff, and_imp]
  refine' ⟨fun h ↦ ⟨⟨h.subset_ground, h.not_spanning⟩, fun X hX hX' hHX ↦ _⟩, fun h ↦ _⟩
  · exact by_contra fun hne ↦ hX' (h.spanning_of_ssuperset (hHX.ssubset_of_ne hne))
  rw [hyperplane_iff_covBy, covBy_iff, and_iff_right M.ground_flat,
    flat_iff_ssubset_closure_insert_forall h.1.1]
  refine'
    ⟨fun e he ↦ _, h.1.1.ssubset_of_ne (by rintro rfl; exact h.1.2 M.ground_spanning),
      fun F hF hHF hFE ↦ or_iff_not_imp_right.mpr fun hFE' ↦ _⟩
  · have h' := h.2 (insert_subset he.1 h.1.1)
    simp only [subset_insert, forall_true_left, @eq_comm _ H, insert_eq_self, iff_false_intro he.2,
      imp_false, Classical.not_not, spanning_def] at h'
    rw [h', ← not_spanning_iff_closure h.1.1 ]
    exact h.1.2
  have h' := h.2 hFE
  rw [hF.spanning_iff] at h'
  rw [h' hFE' hHF]

@[simp] lemma compl_cocircuit_iff_hyperplane (hH : H ⊆ M.E := by aesop_mat) :
    M.Cocircuit (M.E \ H) ↔ M.Hyperplane H := by
  simp_rw [cocircuit_iff_mem_minimals_compl_nonspanning, hyperplane_iff_maximal_nonspanning,
    (and_comm (b := _ ⊆ _)), mem_minimals_setOf_iff, mem_maximals_setOf_iff,
    diff_diff_cancel_left hH, and_iff_right hH, subset_diff, and_imp, and_congr_right_iff]
  refine' fun _ ↦ ⟨fun h X hXE hX hHX ↦ _, fun h X hX hXE hXH ↦ _⟩
  · rw [← diff_diff_cancel_left hH, ← diff_diff_cancel_left hXE,
      h (y := M.E \ X) (by rwa [diff_diff_cancel_left hXE]) diff_subset]
    rw [← subset_compl_iff_disjoint_left, diff_eq, compl_inter, compl_compl]
    exact hHX.trans subset_union_right
  rw [h diff_subset hX, diff_diff_cancel_left hXE]
  rw [subset_diff]
  exact ⟨hH, hXH.symm⟩

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
  rw [hyperplane_iff_covBy, Flat.covBy_iff_eq_closure_insert
    (M.closure_flat _ (diff_subset.trans hB.subset_ground))]
  refine ⟨e, ⟨hB.subset_ground heB, ?_⟩, ?_⟩
  · rw [(hB.indep.diff {e}).not_mem_closure_iff (hB.subset_ground heB)]
    simpa [insert_eq_of_mem heB] using hB.indep
  simpa [insert_eq_of_mem heB] using hB.closure_eq.symm

lemma Hyperplane.ssuperset_eq_univ_of_flat (hH : M.Hyperplane H) (hF : M.Flat F) (h : H ⊂ F) :
    F = M.E :=
  hH.covBy.eq_of_ssubset_of_subset hF h hF.subset_ground

lemma Hyperplane.closure_insert_eq_univ (hH : M.Hyperplane H) (he : e ∈ M.E \ H) :
    M.closure (insert e H) = M.E :=
  hH.ssuperset_eq_univ_of_flat (M.closure_flat _)
    ((ssubset_insert he.2).trans_subset (M.subset_closure _))

lemma exists_hyperplane_sep_of_not_mem_closure (h : e ∈ M.E \ M.closure X)
    (hX : X ⊆ M.E := by aesop_mat) : ∃ H, M.Hyperplane H ∧ X ⊆ H ∧ e ∉ H := by
  obtain ⟨I, hI⟩ := M.exists_basis X
  rw [hI.closure_eq_closure, mem_diff, hI.indep.not_mem_closure_iff] at h
  obtain ⟨B, hB, heIB⟩ := h.2.1.exists_base_superset
  rw [insert_subset_iff] at heIB
  refine ⟨_, hB.hyperplane_of_closure_diff_singleton heIB.1, ?_, ?_⟩
  · exact hI.subset_closure.trans (M.closure_subset_closure (subset_diff_singleton heIB.2 h.2.2))
  exact hB.indep.not_mem_closure_diff_of_mem heIB.1

lemma closure_eq_sInter_hyperplanes (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    M.closure X = ⋂₀ {H | M.Hyperplane H ∧ X ⊆ H} ∩ M.E := by
  refine' subset_antisymm (subset_inter _ (M.closure_subset_ground _)) _
  · rw [subset_sInter_iff]; rintro H ⟨hH, hXH⟩; exact hH.flat.closure_subset_of_subset hXH
  rintro e ⟨heH, heE⟩
  refine' by_contra fun hx ↦ _
  obtain ⟨H, hH, hXH, heH'⟩ := exists_hyperplane_sep_of_not_mem_closure ⟨heE, hx⟩
  exact heH' (heH H ⟨hH, hXH⟩)

lemma mem_closure_iff_forall_hyperplane (hX : X ⊆ M.E := by aesop_mat)
    (he : e ∈ M.E := by aesop_mat) : e ∈ M.closure X ↔ ∀ H, M.Hyperplane H → X ⊆ H → e ∈ H := by
  simp [M.closure_eq_sInter_hyperplanes X, he]

lemma mem_dual_closure_iff_forall_circuit (hX : X ⊆ M.E := by aesop_mat)
  (he : e ∈ M.E := by aesop_mat) :
    e ∈ M✶.closure X ↔ ∀ C, M.Circuit C → e ∈ C → (X ∩ C).Nonempty := by
  rw [← dual_dual M]
  simp_rw [← cocircuit_def, dual_dual M, mem_closure_iff_forall_hyperplane (M := M✶) hX he]
  refine' ⟨fun h C hC heC ↦ by_contra fun hne ↦ _, fun h H hH hXE ↦ by_contra fun he' ↦ _⟩
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
  refine' ⟨fun h ↦ _, _⟩
  · obtain ⟨H, hH, hYH⟩ := (M.closure_flat Y).subset_hyperplane_of_ne_ground h
    exact ⟨H, hH, (M.subset_closure Y).trans hYH⟩
  rintro ⟨H, hH, hYH⟩ hY
  refine' hH.ssubset_ground.not_subset _
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
  have heI := not_mem_subset hI.subset heH
  have hB : M.Base (insert e I) := by
    refine Indep.base_of_spanning ?_ ?_
    · rwa [hI.indep.insert_indep_iff_of_not_mem (not_mem_subset hI.subset heH),
        ← hI.closure_eq_closure, hH.flat.closure, mem_diff, and_iff_left heH]
    rw [spanning_def, ← closure_insert_closure_eq_closure_insert, ← hI.closure_eq_closure,
      hH.flat.closure, hH.closure_eq_ground_of_ssuperset (ssubset_insert heH)]

  convert Base.hyperplane_of_closure_diff_singleton (B := insert e I) (e := e) ?_ (.inl rfl)
  · simp only [mem_singleton_iff, insert_diff_of_mem, heI, not_false_eq_true,
      diff_singleton_eq_self, delete_closure_eq]
    rw [inter_eq_self_of_subset_left, diff_diff_right, eq_comm, union_eq_right,
      union_subset_iff, and_iff_left inter_subset_right, ← hH.flat.closure, hI.closure_eq_closure]
    · simp
    exact subset_diff.2 ⟨hI.indep.subset_ground, disjoint_sdiff_right⟩

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

end Hyperplane



section LowRank

@[reducible] def Point (M : Matroid α) (P : Set α) := M.Flat P ∧ M.er P = 1

lemma Point.flat (hP : M.Point P) : M.Flat P :=
  hP.1

lemma Point.er (hP : M.Point P) : M.er P = 1 :=
  hP.2

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma Point.subset_ground (hP : M.Point P) : P ⊆ M.E :=
  hP.1.subset_ground

lemma Nonloop.closure_point (he : M.Nonloop e) : M.Point (M.closure {e}) :=
  ⟨M.closure_flat {e}, by rw [er_closure_eq, he.indep.er, encard_singleton]⟩

lemma loops_covBy_iff : M.closure ∅ ⋖[M] P ↔ M.Point P := by
  simp only [covBy_iff_relRank_eq_one, relRank_closure_left, relRank_empty_left, Point]
  rw [and_iff_right (M.closure_flat _), ← and_assoc, and_iff_left_of_imp (a := M.Flat P)]
  exact fun h ↦ h.closure_subset_of_subset (empty_subset _)

lemma Point.covBy (hP : M.Point P) : M.closure ∅ ⋖[M] P := loops_covBy_iff.2 hP

lemma Point.exists_eq_closure_nonloop (hP : M.Point P) : ∃ e, M.Nonloop e ∧ P = M.closure {e} := by
  obtain ⟨I, hI⟩ := M.exists_basis P
  obtain ⟨e, rfl⟩ := encard_eq_one.1 <| hI.encard.trans hP.er
  obtain rfl := hP.flat.eq_closure_of_basis hI
  exact ⟨e, indep_singleton.1 hI.indep, rfl⟩

lemma Point.eq_closure_of_mem (hP : M.Point P) (he : M.Nonloop e) (heP : e ∈ P) : P = M.closure {e} := by
  rw [← indep_singleton] at he
  exact hP.flat.eq_closure_of_basis <| he.basis_of_subset_of_er_le_of_finite (singleton_subset_iff.2 heP)
    (by rw [hP.er, he.er, encard_singleton]) (finite_singleton e)

lemma point_iff_exists_eq_closure_nonloop : M.Point P ↔ ∃ e, M.Nonloop e ∧ P = M.closure {e} :=
  ⟨Point.exists_eq_closure_nonloop, by rintro ⟨e, he, rfl⟩; exact he.closure_point⟩

lemma point_contract_iff (hC : C ⊆ M.E := by aesop_mat) :
    (M ／ C).Point P ↔ (M.closure C ⋖[M] (C ∪ P)) ∧ Disjoint P C := by
  rw [Point, flat_contract_iff, covBy_iff_relRank_eq_one, relRank_closure_left,
    union_comm C, ← relRank_eq_union_right, and_iff_right (closure_flat _ _),
    ← relRank_eq_er_contract, and_assoc, and_assoc, and_congr_right_iff, and_comm,
    and_congr_left_iff, iff_and_self]
  rintro h - -
  rw [← h.closure]
  exact M.closure_subset_closure subset_union_right

/-- Points of `M ／ C` are equivalent to flats covering `M.closure C`. -/
@[simps] def pointContractCovByEquiv (M : Matroid α) (C : Set α) (hC : C ⊆ M.E := by aesop_mat) :
    {P // (M ／ C).Point P} ≃ {F // M.closure C ⋖[M] F} where
  toFun P := ⟨P ∪ M.closure C, by
    obtain ⟨P, hP'⟩ := P
    rw [point_contract_iff] at hP'
    convert hP'.1 using 1
    exact subset_antisymm (union_subset subset_union_right hP'.1.subset)
      (union_subset ((M.subset_closure C).trans subset_union_right) subset_union_left) ⟩
  invFun P := ⟨P \ C, by
    obtain ⟨P, hP⟩ := P
    rwa [ point_contract_iff, and_iff_left disjoint_sdiff_left, union_diff_self,
      union_eq_self_of_subset_left]
    exact (M.subset_closure _).trans hP.subset ⟩
  left_inv := by
    rintro ⟨P,hP⟩
    simp only [Subtype.mk.injEq]
    rw [point_contract_iff] at hP
    rw [subset_antisymm_iff, diff_subset_iff, subset_diff, and_iff_right subset_union_left,
      and_iff_left hP.2, union_subset_iff, and_iff_right subset_union_right]
    exact hP.1.subset
  right_inv := by
    rintro ⟨P, hP⟩
    simp only [Subtype.mk.injEq]
    rw [subset_antisymm_iff, union_subset_iff, and_iff_left hP.subset, and_iff_right diff_subset,
      union_comm, union_diff_cancel' (M.subset_closure C)]
    exact hP.subset

-- lemma encard_ground_eq_encard_loops_add_sum_points (M : Matroid α) : M.E.encard =
--     (M.closure ∅).encard + ∑' P : {P // M.Point P}, ((P : Set α) \ M.closure ∅).encard := by
--   rw [(M.closure_flat ∅).ground_encard_eq_tsum, tsum_congr_subtype (f := fun F ↦ encard (F \ M.closure ∅))]
--   simp [loops_covBy_iff]

lemma Point.eq_or_eq_of_flat_of_subset (hP : M.Point P) (hF : M.Flat F) (h : F ⊆ P) :
    F = M.closure ∅ ∨ F = P :=
  hP.covBy.eq_or_eq hF hF.loops_subset h

lemma Point.subset_or_inter_eq_loops_of_flat (hP : M.Point P) (hF : M.Flat F) :
    P ⊆ F ∨ P ∩ F = M.closure ∅ := by
  obtain (h | h) := hP.eq_or_eq_of_flat_of_subset (hP.flat.inter hF) inter_subset_left
  · exact Or.inr h
  exact Or.inl (inter_eq_left.1 h)

-- /-- Each flat `F` induces a partition of the set of points not contained in `F`. -/
-- def Flat.covByPointPartition {F : Set α} (hF : M.Flat F) :
--     Partition {P | M.Point P ∧ ¬ (P ⊆ F)} := Partition.ofPairwiseDisjoint'
--   (parts := (fun F' ↦ {P | P ⊆ F' ∧ ¬ (P ⊆ F)}) '' hF.covByPartition)
--   (pairwiseDisjoint := by
--     rintro Ps ⟨_, h, rfl⟩
--     simp

--     )
--   (forall_nonempty := sorry)
--   (eq_sUnion := sorry)





abbrev Line (M : Matroid α) (L : Set α) := M.Flat L ∧ M.er L = 2

lemma Line.flat (hL : M.Line L) : M.Flat L :=
  hL.1

lemma Line.er (hL : M.Line L) : M.er L = 2 :=
  hL.2

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma Line.subset_ground (hL : M.Line L) : L ⊆ M.E :=
  hL.1.subset_ground

lemma Line.mem_iff_covBy (hL : M.Line L) (he : M.Nonloop e) : e ∈ L ↔ M.closure {e} ⋖[M] L := by
  rw [(M.closure_flat {e}).covBy_iff_relRank_eq_one hL.flat, hL.flat.closure_subset_iff_subset,
    singleton_subset_iff, iff_self_and, relRank_closure_left]
  intro heL
  rw [(M.finRank_singleton e).relRank_eq_sub (by simpa), he.er_eq, hL.er]
  rfl

lemma Nonloop.closure_covBy_iff (he : M.Nonloop e) : M.closure {e} ⋖[M] L ↔ M.Line L ∧ e ∈ L := by
  refine ⟨fun h ↦ ⟨⟨h.flat_right, ?_⟩,h.subset <| M.mem_closure_self e⟩,
    fun ⟨hL, heL⟩ ↦ by rwa [← hL.mem_iff_covBy he]⟩
  rw [h.er_eq, er_closure_eq, he.er_eq]
  rfl

def Nonloop.lineContractPointEquiv (he : M.Nonloop e) :
    {P // (M ／ e).Point P} ≃ {L // M.Line L ∧ e ∈ L} :=
  (M.pointContractCovByEquiv {e}).trans (Equiv.subtypeEquivRight (fun _ ↦ he.closure_covBy_iff))

abbrev Plane (M : Matroid α) (P : Set α) := M.Flat P ∧ M.er P = 3

lemma Plane.flat (hP : M.Plane P) : M.Flat P :=
  hP.1

lemma Plane.er (hP : M.Plane P) : M.er P = 3 :=
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
-- matroid_of_closure_of_finite (λ X, ⋂₀ {F | flat F ∧ X ⊆ F})
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
--   simp_rw [matroid_of_flat, matroid.flat_iff_closure_self, matroid_of_closure_of_finite_apply],
--   refine ⟨λ hF, _, λ hF, _⟩,
--   { rw ← hF, exact (matroid_of_flat_aux flat univ_flat flat_inter _).1},
--   exact (subset_sInter (λ F', and.right)).antisymm' (sInter_subset_of_mem ⟨hF,rfl.subset⟩),
-- end
-- end from_axioms
end Matroid
