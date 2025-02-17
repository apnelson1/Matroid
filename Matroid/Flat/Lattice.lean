import Matroid.Flat.Basic
import Matroid.ForMathlib.SetPartition

variable {α : Type*} {M : Matroid α} {I F X Y F' F₀ F₁ F₂ P L H H₁ H₂ H' B C K : Set α} {e f : α}

open Set
namespace Matroid

section Lattice

@[pp_nodot] def FlatOf (M : Matroid α) : Type _ := {F // M.IsFlat F}

instance {M : Matroid α} : CoeOut M.FlatOf (Set α) where
  coe F := F.val

@[simp] lemma FlatOf.coe_isFlat (F : M.FlatOf) : M.IsFlat F :=
  F.2

def IsFlat.toFlatOf (h : M.IsFlat F) : M.FlatOf := ⟨_,h⟩

def flatClosure (M : Matroid α) (X : Set α) : M.FlatOf := ⟨_, M.closure_isFlat X⟩

@[simp] lemma coe_flatClosure (M : Matroid α) (X : Set α) :
    (M.flatClosure X : Set α) = M.closure X := rfl

@[simp] lemma FlatOf.coe_inj {F F' : M.FlatOf} : (F : Set α) = (F' : Set α) ↔ F = F' :=
  Subtype.coe_inj

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma FlatOf.coe_subset_ground (F : M.FlatOf) : (F : Set α) ⊆ M.E :=
  F.coe_isFlat.subset_ground

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

lemma flatClosure_mono (M : Matroid α) : Monotone M.flatClosure :=
  fun _ _ ↦ M.closure_subset_closure

/-- The flats of a matroid form a complete lattice. -/
instance flatLattice (M : Matroid α) : CompleteLattice (FlatOf M) where
  sup F₁ F₂ := M.flatClosure (F₁ ∪ F₂)
  le_sup_left F F' := subset_union_left.trans (M.subset_closure _)
  le_sup_right F F' := subset_union_right.trans (M.subset_closure _)
  sup_le := by
    rintro ⟨F₁, hF₁⟩ ⟨F₂, hF₂⟩ ⟨F₃, hF₃⟩ (h : F₁ ⊆ F₃) (h' : F₂ ⊆ F₃)
    exact (M.closure_subset_closure (union_subset h h')).trans_eq hF₃.closure
  inf F₁ F₂ := ⟨F₁ ∩ F₂, F₁.coe_isFlat.inter F₂.coe_isFlat⟩
  inf_le_left _ _ := inter_subset_left
  inf_le_right _ _ := inter_subset_right
  le_inf _ _ _ h h' := subset_inter h h'
  sSup Fs := M.flatClosure (⋃ F ∈ Fs, F)
  le_sSup Fs F h := F.2.closure.symm.subset.trans <|
    M.closure_subset_closure (subset_biUnion_of_mem h)
  sSup_le Fs F h := by
    simp only [FlatOf.le_iff, coe_flatClosure] at h ⊢
    refine F.coe_isFlat.closure_subset_of_subset ?_
    simp only [iUnion_subset_iff, F.coe_isFlat.closure]
    assumption
  sInf Fs := ⟨(⋂ F ∈ Fs, F) ∩ M.E, IsFlat.biInter_inter_ground (by simp)⟩
  sInf_le Fs F h := inter_subset_left.trans (biInter_subset_of_mem (by simpa))
  le_sInf Fs F h := subset_inter (by simpa) F.coe_subset_ground
  top := ⟨M.E, M.ground_isFlat⟩
  bot := M.flatClosure ∅
  le_top F := F.coe_isFlat.subset_ground
  bot_le F := F.coe_isFlat.closure_subset_of_subset (empty_subset _)

@[simp] lemma FlatOf.coe_top (M : Matroid α) : ((⊤ : M.FlatOf) : Set α) = M.E := rfl

@[simp] lemma FlatOf.coe_bot (M : Matroid α) : ((⊥ : M.FlatOf) : Set α) = M.closure ∅ := rfl

@[simp] lemma FlatOf.coe_sup (F₁ F₂ : M.FlatOf) :
    ((F₁ ⊔ F₂ : M.FlatOf) : Set α) = M.closure (F₁ ∪ F₂) := rfl

@[simp] lemma FlatOf.coe_inf (F₁ F₂ : M.FlatOf) :
    ((F₁ ⊓ F₂ : M.FlatOf) : Set α) = (F₁ : Set α) ∩ F₂ := rfl

@[simp] lemma FlatOf.coe_sSup (Fs : Set M.FlatOf) : sSup Fs = M.closure (⋃ F ∈ Fs, F) := rfl

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
  ∃ (h₀ : M.IsFlat F₀) (h₁ : M.IsFlat F₁), h₀.toFlatOf ⋖ h₁.toFlatOf

def WCovBy (M : Matroid α) (F₀ F₁ : Set α) : Prop :=
  ∃ (h₀ : M.IsFlat F₀) (h₁ : M.IsFlat F₁), h₀.toFlatOf ⩿ h₁.toFlatOf

notation:25 F₀:50 " ⋖[" M:25 "] " F₁ :75 => CovBy M F₀ F₁

notation:25 F₀:50 " ⩿[" M:25 "] " F₁ :75 => WCovBy M F₀ F₁

lemma FlatOf.covBy_iff (F₀ F₁ : FlatOf M) : F₀ ⋖ F₁ ↔ (F₀ : Set α) ⋖[M] (F₁ : Set α) := by
  simp only [Matroid.CovBy, coe_isFlat, exists_true_left]; rfl

lemma FlatOf.wcovBy_iff (F₀ F₁ : FlatOf M) : F₀ ⩿ F₁ ↔ (F₀ : Set α) ⩿[M] (F₁ : Set α) := by
  simp only [Matroid.WCovBy, coe_isFlat, exists_true_left]; rfl

lemma covBy_iff : F₀ ⋖[M] F₁ ↔
    M.IsFlat F₀ ∧ M.IsFlat F₁ ∧ F₀ ⊂ F₁ ∧ ∀ F, M.IsFlat F → F₀ ⊆ F → F ⊆ F₁ → F = F₀ ∨ F = F₁ := by
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

lemma WCovBy.isFlat_left (h : F₀ ⩿[M] F₁) : M.IsFlat F₀ :=
  h.1

lemma WCovBy.isFlat_right (h : F₀ ⩿[M] F₁) : M.IsFlat F₁ :=
  h.2.1

lemma CovBy.isFlat_left (h : F₀ ⋖[M] F₁) : M.IsFlat F₀ :=
  h.1

lemma CovBy.isFlat_right (h : F₀ ⋖[M] F₁) : M.IsFlat F₁ :=
  h.2.1

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma CovBy.subset_ground_left (h : F₀ ⋖[M] F₁) : F₀ ⊆ M.E :=
  h.isFlat_left.subset_ground

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma CovBy.subset_ground_right (h : F₀ ⋖[M] F₁) : F₁ ⊆ M.E :=
  h.isFlat_right.subset_ground

lemma CovBy.ssubset (h : F₀ ⋖[M] F₁) : F₀ ⊂ F₁ :=
  h.2.2.1

lemma CovBy.ne (h : F₀ ⋖[M] F₁) : F₀ ≠ F₁ :=
  h.ssubset.ne

lemma CovBy.subset (h : F₀ ⋖[M] F₁) : F₀ ⊆ F₁ :=
  h.ssubset.subset

lemma WCovBy.subset (h : F₀ ⩿[M] F₁) : F₀ ⊆ F₁ :=
  h.2.2.1

lemma IsFlat.covBy_iff_wcovBy_and_ne (hF₀ : M.IsFlat F₀) (hF₁ : M.IsFlat F₁) :
    F₀ ⋖[M] F₁ ↔ (F₀ ⩿[M] F₁) ∧ F₀ ≠ F₁ := by
  rw [show F₀ = (hF₀.toFlatOf : Set α) from rfl, show F₁ = (hF₁.toFlatOf : Set α) from rfl,
    ← FlatOf.covBy_iff, ← FlatOf.wcovBy_iff, _root_.covBy_iff_wcovBy_and_ne, ne_eq, ne_eq,
    FlatOf.coe_inj]

lemma IsFlat.covBy_iff_wcovBy_and_ssubset (hF₀ : M.IsFlat F₀) (hF₁ : M.IsFlat F₁) :
    F₀ ⋖[M] F₁ ↔ (F₀ ⩿[M] F₁) ∧ F₀ ⊂ F₁ := by
  rw [hF₀.covBy_iff_wcovBy_and_ne hF₁, and_congr_right_iff, ssubset_iff_subset_ne,
    ne_eq, iff_and_self]
  exact fun h _ ↦ h.subset

@[simp] lemma IsFlat.wCovBy_self (hF : M.IsFlat F) : F ⩿[M] F := by
  simpa [WCovBy]

lemma IsFlat.wCovby_iff_covBy_or_eq (hF₀ : M.IsFlat F₀) (hF₁ : M.IsFlat F₁) :
    F₀ ⩿[M] F₁ ↔ (F₀ ⋖[M] F₁) ∨ F₀ = F₁ := by
  obtain (rfl | hne) := eq_or_ne F₀ F₁
  · simp [hF₀]
  simp [hF₀, hF₀.covBy_iff_wcovBy_and_ne hF₁, or_iff_not_imp_right, hne]


--TODO : More `WCovby` API.

lemma WCovBy.covBy_of_ne (h : F₀ ⩿[M] F₁) (hne : F₀ ≠ F₁) : F₀ ⋖[M] F₁ :=
    (h.isFlat_left.covBy_iff_wcovBy_and_ne h.isFlat_right).2 ⟨h, hne⟩

lemma WCovBy.eq_or_covBy (h : F₀ ⩿[M] F₁) : F₀ = F₁ ∨ (F₀ ⋖[M] F₁) := by
    rw [or_iff_not_imp_left]; exact h.covBy_of_ne

lemma CovBy.wCovby (h : F₀ ⋖[M] F₁) : F₀ ⩿[M] F₁ :=
    (h.isFlat_left.wCovby_iff_covBy_or_eq h.isFlat_right).2 <| .inl h

lemma IsFlat.covBy_iff_of_isFlat (hF₀ : M.IsFlat F₀) (hF₁ : M.IsFlat F₁) :
    F₀ ⋖[M] F₁ ↔ F₀ ⊂ F₁ ∧ ∀ F, M.IsFlat F → F₀ ⊆ F → F ⊆ F₁ → F = F₀ ∨ F = F₁ := by
  rw [covBy_iff, and_iff_right hF₀, and_iff_right hF₁]

lemma IsFlat.wcovBy_iff_of_isFlat (hF₀ : M.IsFlat F₀) (hF₁ : M.IsFlat F₁) :
    F₀ ⩿[M] F₁ ↔ F₀ ⊆ F₁ ∧ ∀ F, M.IsFlat F → F₀ ⊆ F → F ⊆ F₁ → F = F₀ ∨ F = F₁ := by
  obtain (rfl | hne) := eq_or_ne F₀ F₁
  · simp only [hF₀, wCovBy_self, or_self, true_iff]
    exact ⟨Subset.rfl, fun _ _  ↦ antisymm'⟩
  rw [wCovby_iff_covBy_or_eq hF₀ hF₁, subset_iff_ssubset_or_eq, or_iff_left hne, or_iff_left hne,
    hF₀.covBy_iff_of_isFlat hF₁]

lemma WCovBy.wCovBy_left_of_between (h : F₀ ⩿[M] F₁) (hF : M.IsFlat F) (hF₀F : F₀ ⊆ F)
    (hFF₁ : F ⊆ F₁) : F₀ ⩿[M] F := by
  have h' := (h.isFlat_left.wcovBy_iff_of_isFlat h.isFlat_right).1 h
  obtain rfl | rfl := h'.2 F hF hF₀F hFF₁
  · exact hF.wCovBy_self
  assumption

lemma WCovBy.wCovBy_right_of_between (h : F₀ ⩿[M] F₁) (hF : M.IsFlat F) (hF₀F : F₀ ⊆ F)
    (hFF₁ : F ⊆ F₁) : F ⩿[M] F₁ := by
  have h' := (h.isFlat_left.wcovBy_iff_of_isFlat h.isFlat_right).1 h
  obtain rfl | rfl := h'.2 F hF hF₀F hFF₁
  · assumption
  exact hF.wCovBy_self

lemma CovBy.eq_or_eq (h : F₀ ⋖[M] F₁) (hF : M.IsFlat F) (h₀ : F₀ ⊆ F) (h₁ : F ⊆ F₁) :
    F = F₀ ∨ F = F₁ :=
  (covBy_iff.1 h).2.2.2 F hF h₀ h₁

lemma CovBy.eq_of_subset_of_ssubset (h : F₀ ⋖[M] F₁) (hF : M.IsFlat F) (hF₀ : F₀ ⊆ F)
    (hF₁ : F ⊂ F₁) : F = F₀ :=
  ((covBy_iff.1 h).2.2.2 F hF hF₀ hF₁.subset).elim id fun h' ↦ (hF₁.ne h').elim

lemma CovBy.eq_of_ssubset_of_subset (h : F₀ ⋖[M] F₁) (hF : M.IsFlat F) (hF₀ : F₀ ⊂ F)
    (hF₁ : F ⊆ F₁) : F = F₁ :=
  ((covBy_iff.1 h).2.2.2 F hF hF₀.subset hF₁).elim (fun h' ↦ (hF₀.ne.symm h').elim) id

lemma CovBy.inter_eq_of_covby_of_ne (h₁ : F₀ ⋖[M] F₁) (h₂ : F₀ ⋖[M] F₂) (h_ne : F₁ ≠ F₂) :
    F₀ = F₁ ∩ F₂ := by
  contrapose! h_ne
  have h₁' := h₁.eq_or_eq (h₁.isFlat_right.inter h₂.isFlat_right) (subset_inter h₁.subset h₂.subset)
     inter_subset_left
  have h₂' := h₂.eq_or_eq (h₁.isFlat_right.inter h₂.isFlat_right) (subset_inter h₁.subset h₂.subset)
     inter_subset_right
  rw [or_iff_right h_ne.symm] at h₁' h₂'
  rw [← h₁', h₂']

lemma CovBy.closure_insert_eq (h : F₀ ⋖[M] F₁) (he : e ∈ F₁ \ F₀) :
    M.closure (insert e F₀) = F₁ := by
  refine
    h.eq_of_ssubset_of_subset (M.closure_isFlat _)
      ((ssubset_insert he.2).trans_subset (M.subset_closure _ ?_))
      (h.isFlat_right.closure_subset_of_subset (insert_subset he.1 h.ssubset.subset))
  rw [insert_eq, union_subset_iff, singleton_subset_iff]
  exact ⟨h.isFlat_right.subset_ground he.1, h.isFlat_left.subset_ground⟩

lemma CovBy.exists_eq_closure_insert (h : F₀ ⋖[M] F₁) :
    ∃ e ∈ F₁ \ F₀, M.closure (insert e F₀) = F₁ := by
  obtain ⟨e, he⟩ := exists_of_ssubset h.ssubset
  exact ⟨e, he, h.closure_insert_eq he⟩

lemma CovBy.exists_eq_closure_insert' (h : M.closure X ⋖[M] F) :
    ∃ e ∈ F \ M.closure X, F = M.closure (insert e X) := by
  obtain ⟨e, he, rfl⟩ := h.exists_eq_closure_insert
  exact ⟨e, he, by simp⟩

lemma IsFlat.covBy_iff_eq_closure_insert (hF₀ : M.IsFlat F₀) :
    F₀ ⋖[M] F₁ ↔ ∃ e ∈ M.E \ F₀, F₁ = M.closure (insert e F₀) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨e, he, rfl⟩ := h.exists_eq_closure_insert
    exact ⟨e, ⟨(M.closure_subset_ground _) he.1, he.2⟩, rfl⟩
  rintro ⟨e, heF₀, rfl⟩
  refine
    covBy_iff.2 ⟨hF₀, M.closure_isFlat _,
      (M.subset_closure_of_subset (subset_insert _ _) ?_).ssubset_of_ne ?_, fun F hF hF₀F hFF₁ ↦ ?_⟩
  · rw [insert_eq, union_subset_iff, singleton_subset_iff]
    exact ⟨heF₀.1, hF₀.subset_ground⟩
  · exact fun h ↦ heF₀.2 (h.symm.subset (mem_closure_of_mem' _ (mem_insert _ _) heF₀.1))
  refine hF₀F.eq_or_ssubset.elim (fun h ↦ Or.inl h.symm)
    (fun hss ↦ Or.inr (hFF₁.antisymm (hF.closure_subset_of_subset (insert_subset ?_ hF₀F))))
  obtain ⟨f, hfF, hfF₀⟩ := exists_of_ssubset hss
  exact mem_of_mem_of_subset (hF₀.closure_exchange ⟨hFF₁ hfF, hfF₀⟩).1
    (hF.closure_subset_of_subset (insert_subset hfF hF₀F))

lemma CovBy.eRk_eq (h : F ⋖[M] F') : M.eRk F' = M.eRk F + 1 := by
  obtain ⟨e, he, rfl⟩ := h.exists_eq_closure_insert
  rw [eRk_closure_eq, h.isFlat_left.eRk_insert_eq_add_one]
  exact ⟨M.closure_subset_ground _ he.1, he.2⟩

lemma Covby.eRk_eq_of_ssubset_of_subset (h : F ⋖[M] F') (hFX : F ⊂ X) (hXF' : X ⊆ F') :
    M.eRk X = M.eRk F + 1 := by
  obtain ⟨e, heX, heF⟩ := exists_of_ssubset hFX
  rw [← h.eRk_eq, le_antisymm_iff, and_iff_right (M.eRk_mono hXF'), h.eRk_eq,
    ← h.isFlat_left.eRk_insert_eq_add_one ⟨(h.subset_ground_right (hXF'.subset heX)), heF⟩]
  exact M.eRk_mono (insert_subset heX hFX.subset)

lemma CovBy.rk_eq_of_isRkFinite (h : F ⋖[M] F') (hFin : M.IsRkFinite F) : M.rk F' = M.rk F + 1 := by
  have hFin' : M.IsRkFinite F' := by
    rw [← eRk_lt_top_iff, h.eRk_eq]
    rw [← eRk_lt_top_iff] at hFin
    exact lt_tsub_iff_right.mp hFin
  have her := h.eRk_eq
  rw [← hFin.cast_rk_eq, ← hFin'.cast_rk_eq] at her
  norm_cast at her

lemma closure_covBy_iff :
    (M.closure X) ⋖[M] F ↔ ∃ e ∈ M.E \ M.closure X, F = M.closure (insert e X) := by
  simp_rw [(M.closure_isFlat X).covBy_iff_eq_closure_insert,
    closure_insert_closure_eq_closure_insert]

lemma closure_covBy_closure_iff : (M.closure X) ⋖[M] (M.closure Y) ↔
    ∃ e ∈ M.E, e ∈ Y ∧ e ∉ M.closure X ∧ M.closure (insert e X) = M.closure Y := by
  rw [closure_covBy_iff]
  refine ⟨fun ⟨e, he, hYX⟩ ↦ ?_, fun ⟨e, he, _, heX, h_eq⟩ ↦ ⟨e, ⟨he, heX⟩, h_eq.symm⟩ ⟩
  by_contra! hcon
  have hY : Y ∩ M.E ⊆ M.closure X := by
    refine fun f hf ↦ by_contra fun hfX ↦ hcon f hf.2 hf.1 hfX ?_
    rw [hYX]
    apply closure_insert_congr ⟨?_, hfX⟩
    rw [← hYX, ← closure_inter_ground]
    exact M.subset_closure _ (by aesop_mat) hf
  replace hY := M.closure_subset_closure_of_subset_closure hY
  rw [closure_inter_ground, hYX] at hY
  exact he.2 <| hY (M.mem_closure_of_mem' (mem_insert _ _) he.1)

lemma IsFlat.covBy_closure_insert (hF : M.IsFlat F) (he : e ∉ F) (heE : e ∈ M.E := by aesop_mat) :
    F ⋖[M] M.closure (insert e F) :=
  hF.covBy_iff_eq_closure_insert.2 ⟨e, ⟨heE, he⟩, rfl⟩

lemma IsFlat.wCovBy_closure_insert (hF : M.IsFlat F) (e : α) : F ⩿[M] M.closure (insert e F) := by
  by_cases heF : e ∈ F
  · simp [heF, hF.closure, hF.wCovBy_self]
  by_cases heE : e ∈ M.E
  · exact (hF.covBy_closure_insert heF heE).wCovby
  rw [← closure_inter_ground, insert_inter_of_not_mem heE, closure_inter_ground, hF.closure]
  exact hF.wCovBy_self

lemma IsFlat.wCovby_of_subset_closure_insert (hF₀ : M.IsFlat F₀) (hF₁ : M.IsFlat F₁) (hss : F₀ ⊆ F₁)
    (hF₁e : F₁ ⊆ M.closure (insert e F₀)) : F₀ ⩿[M] F₁ :=
  (hF₀.wCovBy_closure_insert e).wCovBy_left_of_between hF₁ hss hF₁e

lemma Indep.closure_diff_covBy (hI : M.Indep I) (he : e ∈ I) :
    M.closure (I \ {e}) ⋖[M] M.closure I := by
  simpa [closure_insert_closure_eq_closure_insert, he] using
    (M.closure_isFlat _).covBy_closure_insert (not_mem_closure_diff_of_mem hI he)
      (hI.subset_ground he)

lemma Indep.covBy_closure_insert (hI : M.Indep I) (he : e ∈ M.E \ M.closure I) :
    M.closure I ⋖[M] M.closure (insert e I) := by
  simpa [not_mem_of_mem_diff_closure he] using
    (hI.insert_indep_iff.2 <| .inl he).closure_diff_covBy (.inl rfl)

lemma CovBy.eq_closure_insert_of_mem_diff (h : F ⋖[M] F') (he : e ∈ F' \ F) :
    F' = M.closure (insert e F) :=
  Eq.symm <| h.eq_of_ssubset_of_subset (M.closure_isFlat (insert e F))
    (h.isFlat_left.covBy_closure_insert he.2 (h.isFlat_right.subset_ground he.1)).ssubset
    (h.isFlat_right.closure_subset_of_subset (insert_subset he.1 h.subset))

lemma IsFlat.covBy_iff_eRelRk_eq_one (hF₀ : M.IsFlat F₀) (hF : M.IsFlat F) :
    F₀ ⋖[M] F ↔ F₀ ⊆ F ∧ M.eRelRk F₀ F = 1 := by
  simp_rw [hF₀.covBy_iff_eq_closure_insert, eRelRk_eq_one_iff hF.subset_ground, hF₀.closure]
  refine ⟨?_, fun ⟨hss, e, he, h⟩ ↦ ⟨e, ?_, h.antisymm ?_⟩⟩
  · rintro ⟨e, ⟨he, heE⟩, rfl⟩
    refine ⟨M.subset_closure_of_subset (subset_insert _ _), ⟨e, ⟨?_, heE⟩, rfl.subset⟩⟩
    exact M.mem_closure_of_mem (mem_insert _ _)
  · apply diff_subset_diff_left hF.subset_ground he
  exact hF.closure_subset_iff_subset.2 <| insert_subset he.1 hss

lemma IsFlat.covBy_iff_eRelRk_eq_one_of_subset (hF₀ : M.IsFlat F₀) (hF : M.IsFlat F)
    (hss : F₀ ⊆ F) : F₀ ⋖[M] F ↔ M.eRelRk F₀ F = 1 := by
  rw [hF₀.covBy_iff_eRelRk_eq_one hF, and_iff_right hss]

lemma IsFlat.covBy_iff_rk_eq_add_one [RankFinite M] (hF₀ : M.IsFlat F₀) (hF : M.IsFlat F) :
    F₀ ⋖[M] F ↔ F₀ ⊆ F ∧ M.rk F = M.rk F₀ + 1 := by
  rw [hF₀.covBy_iff_eRelRk_eq_one hF, and_congr_right_iff]
  intro hss
  rw [(M.isRkFinite_set _).eRelRk_eq_sub hss, eq_comm, ← cast_rk_eq, ← cast_rk_eq, ← ENat.coe_sub,
    ← ENat.coe_one, Nat.cast_inj, eq_tsub_iff_add_eq_of_le (M.rk_mono hss), eq_comm, add_comm]

lemma CovBy.eRelRk_eq_one (h : F₀ ⋖[M] F₁) : M.eRelRk F₀ F₁ = 1 :=
  ((h.isFlat_left.covBy_iff_eRelRk_eq_one h.isFlat_right).1 h).2

lemma covBy_iff_eRelRk_eq_one :
    F₀ ⋖[M] F₁ ↔ M.IsFlat F₀ ∧ M.IsFlat F₁ ∧ F₀ ⊆ F₁ ∧ M.eRelRk F₀ F₁ = 1 :=
  ⟨fun h ↦ ⟨h.isFlat_left, h.isFlat_right, h.subset, h.eRelRk_eq_one⟩,
    fun ⟨hF₀, hF₁, hss, hr⟩ ↦ (hF₀.covBy_iff_eRelRk_eq_one hF₁).2 ⟨hss, hr⟩⟩

lemma IsFlat.exists_unique_isFlat_of_not_mem (hF₀ : M.IsFlat F₀) (he : e ∈ M.E \ F₀) :
    ∃! F₁, e ∈ F₁ ∧ (F₀ ⋖[M] F₁) := by
  simp_rw [hF₀.covBy_iff_eq_closure_insert]
  use M.closure (insert e F₀)
  refine ⟨⟨(M.inter_ground_subset_closure (insert e F₀)) ⟨mem_insert _ _, he.1⟩, ⟨e, he, rfl⟩⟩, ?_⟩
  simp only [exists_prop, and_imp, forall_exists_index]
  rintro X heX f _ rfl
  rw [hF₀.closure_insert_eq_closure_insert_of_mem ⟨heX, he.2⟩]

/-- If `F` covers distinct flats `F₀` and `F₁`, then `F` is their join. -/
lemma CovBy.eq_closure_union_of_covBy_of_ne (h₀ : F₀ ⋖[M] F) (h₁ : F₁ ⋖[M] F) (hne : F₀ ≠ F₁) :
    F = M.closure (F₀ ∪ F₁) := by
  refine subset_antisymm ?_
    (h₁.isFlat_right.closure_subset_of_subset (union_subset h₀.subset h₁.subset))
  have hnss : ¬ (F₀ ⊆ F₁) :=
    fun hss ↦ hne.symm <| h₀.eq_of_subset_of_ssubset h₁.isFlat_left hss h₁.ssubset
  obtain ⟨e, he₀, he₁⟩ := not_subset.1 hnss
  obtain rfl := h₁.closure_insert_eq ⟨h₀.subset he₀, he₁⟩
  exact M.closure_subset_closure (insert_subset (Or.inl he₀) subset_union_right)

lemma IsFlat.exists_left_covBy_of_ssubset (hF₀ : M.IsFlat F₀) (hF₁ : M.IsFlat F₁) (hss : F₀ ⊂ F₁) :
    ∃ F, ((F₀ ⋖[M] F) ∧ F ⊆ F₁) := by
  obtain ⟨e, he⟩ := exists_of_ssubset hss
  exact ⟨_, hF₀.covBy_closure_insert he.2 (hF₁.subset_ground he.1),
    hF₁.closure_subset_of_subset <| insert_subset he.1 hss.subset⟩

lemma IsFlat.exists_covBy_right_of_ssubset (hF₀ : M.IsFlat F₀) (hF₁ : M.IsFlat F₁) (hss : F₀ ⊂ F₁) :
    ∃ F, (F₀ ⊆ F ∧ (F ⋖[M] F₁)) := by
  obtain ⟨I, J, hI, hJ, hIJ⟩ := M.exists_isBasis_subset_isBasis hss.subset
  have hssu : I ⊂ J := hIJ.ssubset_of_ne <| by
    rintro rfl
    rw [hF₀.eq_closure_of_isBasis hI, hF₁.eq_closure_of_isBasis hJ] at hss
    exact hss.ne rfl
  obtain ⟨e, heJ, heI⟩ := exists_of_ssubset hssu
  refine ⟨M.closure (J \ {e}), hI.subset_closure.trans
    (M.closure_subset_closure (subset_diff_singleton hIJ heI)), ?_⟩
  convert (M.closure_isFlat (J \ {e})).covBy_closure_insert ?_ (hJ.indep.subset_ground heJ)
  · rw [closure_insert_closure_eq_closure_insert, insert_diff_singleton, insert_eq_of_mem heJ,
      hF₁.eq_closure_of_isBasis hJ]
  exact hJ.indep.not_mem_closure_diff_of_mem heJ

lemma CovBy.covBy_closure_union_of_inter_covBy (h₀ : F₀ ∩ F₁ ⋖[M] F₀) (h₁ : F₀ ∩ F₁ ⋖[M] F₁) :
    F₀ ⋖[M] M.closure (F₀ ∪ F₁) := by
  obtain ⟨e₀, -, h₀'⟩ := h₀.exists_eq_closure_insert
  obtain ⟨e₁, he₁, h₁'⟩ := h₁.exists_eq_closure_insert
  nth_rw 2 [← h₀', ← h₁']
  rw [closure_closure_union_closure_eq_closure_union, ← singleton_union, ← singleton_union,
    ← union_union_distrib_right, union_comm {e₀}, union_assoc, singleton_union, singleton_union,
    ← M.closure_insert_closure_eq_closure_insert, h₀']
  exact h₀.isFlat_right.covBy_closure_insert (fun h ↦ he₁.2 ⟨h, he₁.1⟩)
    (h₁.isFlat_right.subset_ground he₁.1)

instance {M : Matroid α} : IsWeakUpperModularLattice M.FlatOf where
  covBy_sup_of_inf_covBy_covBy := by
    rintro ⟨F₀, hF₀⟩ ⟨F₁, hF₁⟩
    simp only [ge_iff_le, FlatOf.le_iff, FlatOf.covBy_iff, FlatOf.coe_inf, FlatOf.coe_sup]
    exact CovBy.covBy_closure_union_of_inter_covBy

/-- If `M.eRelRk F₀ F₁ = 2` for flats `F₀, F₁`, then every flat strictly between
  `F₀` and `F₁` covers `F₀` and is covered by `F₁`. -/
lemma IsFlat.covBy_and_covBy_of_ssubset_of_ssubset_of_eRelRk_eq_two (hF₀ : M.IsFlat F₀)
    (hF₁ : M.IsFlat F₁) (h : M.eRelRk F₀ F₁ = 2) (hF : M.IsFlat F) (h₀ : F₀ ⊂ F) (h₁ : F ⊂ F₁) :
    (F₀ ⋖[M] F) ∧ (F ⋖[M] F₁) := by
  have h0le := hF₀.one_le_eRelRk_of_ssubset h₀
  have h1le := hF.one_le_eRelRk_of_ssubset h₁
  rw [← M.eRelRk_add_cancel h₀.subset h₁.subset] at h
  have h0top : M.eRelRk F₀ F ≠ ⊤ := by
    intro h'; rw [h'] at h; norm_cast at h
  have h1top : M.eRelRk F F₁ ≠ ⊤ := by
    intro h'; rw [h', add_top] at h; norm_cast at h
  have hle1 := WithTop.le_of_add_le_add_left h0top <| h.le.trans (add_le_add_right h0le 1)
  have hle0 := WithTop.le_of_add_le_add_right h1top <| h.le.trans (add_le_add_left h1le 1)
  rw [hF₀.covBy_iff_eRelRk_eq_one hF, hF.covBy_iff_eRelRk_eq_one hF₁,
    and_iff_right h₀.subset, and_iff_right h₁.subset]
  exact ⟨hle0.antisymm h0le, hle1.antisymm h1le⟩

/-- If some flat is covered by `F₁` and covers `F₀`,
  then this holds for every flat strictly between `F₀` and `F₁`. -/
lemma CovBy.covBy_and_covBy_of_covBy_of_ssubset_of_ssubset (hF₀F' : F₀ ⋖[M] F')
    (hF'F₁ : F' ⋖[M] F₁) (hF : M.IsFlat F) (h₀ : F₀ ⊂ F) (h₁ : F ⊂ F₁) :
    (F₀ ⋖[M] F) ∧ (F ⋖[M] F₁) := by
  apply hF₀F'.isFlat_left.covBy_and_covBy_of_ssubset_of_ssubset_of_eRelRk_eq_two hF'F₁.isFlat_right
    ?_ hF h₀ h₁
  rw [← M.eRelRk_add_cancel hF₀F'.subset hF'F₁.subset, hF'F₁.eRelRk_eq_one,
    hF₀F'.eRelRk_eq_one]
  rfl

lemma CovBy.insert_isBasis (hFF' : F ⋖[M] F') (hI : M.IsBasis I F) (he : e ∈ F' \ F) :
    M.IsBasis (insert e I) F' := by
  refine Indep.isBasis_of_subset_of_subset_closure ?_
    (insert_subset he.1 (hI.subset.trans hFF'.subset)) ?_
  · rw [hI.indep.insert_indep_iff, hI.closure_eq_closure, hFF'.isFlat_left.closure]
    exact .inl ⟨hFF'.subset_ground_right he.1, he.2⟩
  rw [← hFF'.closure_insert_eq he, closure_insert_congr_right hI.closure_eq_closure]

/-- The flats covering a flat `F` induce a partition of `M.E \ F`. -/
@[simps!] def IsFlat.covByPartition (hF : M.IsFlat F) : Partition (M.E \ F) :=
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
      simp only [sUnion_image, mem_setOf_eq, Set.ext_iff, mem_diff, mem_iUnion, exists_and_left,
        exists_prop]
      exact fun e ↦ ⟨fun ⟨he,heF⟩ ↦ ⟨M.closure (insert e F), M.mem_closure_of_mem (mem_insert _ _),
        hF.covBy_closure_insert heF, heF⟩,
        fun ⟨F', heF', hlt, h⟩ ↦ ⟨hlt.isFlat_right.subset_ground heF', h⟩⟩ )

@[simp] lemma IsFlat.mem_covByPartition_iff {X : Set α} (hF : M.IsFlat F) :
    X ∈ hF.covByPartition ↔ ∃ F', ((F ⋖[M] F') ∧ F' \ F = X) := by
  simp [IsFlat.covByPartition]

@[simp] lemma IsFlat.partOf_covByPartition_eq (hF : M.IsFlat F) (e : α) :
    hF.covByPartition.partOf e = M.closure (insert e F) \ F := by
  by_cases he : e ∈ M.E \ F
  · obtain ⟨F', hFF', hF'⟩ := hF.mem_covByPartition_iff.1 (hF.covByPartition.partOf_mem he)
    obtain rfl := hFF'.closure_insert_eq (hF'.symm.subset <| hF.covByPartition.mem_partOf he)
    exact hF'.symm
  have hrw : insert e F ∩ M.E = F := by
    refine subset_antisymm ?_ (subset_inter (subset_insert _ _) hF.subset_ground)
    rw [← singleton_union, union_inter_distrib_right, union_subset_iff,
       (and_iff_left inter_subset_left)]
    rintro f ⟨rfl, hf⟩
    exact by_contra fun hfF ↦ he ⟨hf, hfF⟩
  rw [← closure_inter_ground, hrw, hF.closure, diff_self, hF.covByPartition.partOf_eq_empty he]

@[simp] lemma IsFlat.rel_covByPartition_iff (hF : M.IsFlat F) {e f : α} :
    hF.covByPartition.Rel e f ↔
      e ∈ M.E \ F ∧ f ∈ M.E \ F ∧ M.closure (insert e F) = M.closure (insert f F) := by
  simp only [hF.covByPartition.rel_iff_partOf_eq_partOf', partOf_covByPartition_eq, mem_diff,
    exists_prop, exists_and_left, and_congr_right_iff]
  refine fun _ _  ↦ ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
  rw [← union_eq_self_of_subset_right (M.closure_subset_closure (subset_insert e F)),
    ← union_eq_self_of_subset_right (M.closure_subset_closure (subset_insert f F)), hF.closure,
    ← diff_union_self, h, diff_union_self]

lemma IsFlat.rel_covByPartition_iff' (hF : M.IsFlat F) (he : e ∈ M.E \ F) :
    hF.covByPartition.Rel e f ↔ M.closure (insert e F) = M.closure (insert f F) := by
  rw [hF.rel_covByPartition_iff, and_iff_right he, and_iff_right_iff_imp]
  refine fun hclosure ↦ ⟨by_contra fun hf ↦ ?_, fun hfF ↦ ?_⟩
  · rw [← M.closure_inter_ground (insert f F), insert_inter_of_not_mem hf,
      inter_eq_self_of_subset_left hF.subset_ground, hF.closure] at hclosure
    exact he.2 <| hclosure.subset (M.mem_closure_of_mem (mem_insert e F))
  rw [insert_eq_of_mem hfF, hF.closure] at hclosure
  exact he.2 <| hclosure.subset (M.mem_closure_of_mem (mem_insert e F))

/-- Cells of the `covByPartition` induced by `F₀` are equivalent to flats covering `F₀`.-/
@[simps] def IsFlat.equivCovByPartition (hF₀ : M.IsFlat F₀) :
    ↑(hF₀.covByPartition : Set (Set α)) ≃ {F // F₀ ⋖[M] F} where
  toFun F := ⟨F ∪ F₀, by
    obtain ⟨_, ⟨F, hF : F₀ ⋖[M] F, rfl⟩⟩ := F
    simpa [union_eq_self_of_subset_right hF.subset]⟩
  invFun F := ⟨F \ F₀, by
    simp only [SetLike.mem_coe, mem_covByPartition_iff]
    exact ⟨_, F.prop, rfl⟩ ⟩
  left_inv := by rintro ⟨_, ⟨F, hF : F₀ ⋖[M] F, rfl⟩⟩; simp
  right_inv := by rintro ⟨F, hF⟩; simp [hF.subset]


/-- This lemma is stating that the lattice of flats of a finitary matroid is meet-continuous.
This needs `Finitary`, even if the directed set is known to be a chain.
A counterexample would be the matroid on `[0,1]` whose ground set is a circuit,
where the `Xs` are the sets `[0,x)` for `x < 1`, and `F = {1}`. -/
lemma IsFlat.inter_iUnion_closure_of_directed [Finitary M] {ι : Type*} {Xs : ι → Set α}
    (hF : M.IsFlat F) (hXs : ∀ i, M.IsFlat (Xs i)) (h_dir : Directed (· ⊆ ·) Xs) :
    F ∩ M.closure (⋃ i, Xs i) = M.closure (⋃ i, F ∩ Xs i) := by
  obtain he | hne := isEmpty_or_nonempty ι
  · simp [hF.loops_subset]

  have aux : ∀ A : Set ι, A.Finite → ∃ j, ⋃ i ∈ A, Xs i ⊆ Xs j
  · intro A hA
    refine hA.induction_on_subset _ ⟨hne.some, by simp⟩ ?_
    rintro i B hiA hBA hiB ⟨jB, hssjb⟩
    obtain ⟨k, hk⟩ := h_dir i jB
    simp only [mem_insert_iff, iUnion_iUnion_eq_or_left, union_subset_iff]
    exact ⟨k, hk.1, hssjb.trans hk.2⟩


  refine (subset_inter ?_ ?_).antisymm' fun e ⟨heF, hecl⟩ ↦ ?_
  · exact hF.closure_subset_of_subset (iUnion_subset fun _ ↦ inter_subset_left)
  · exact M.closure_subset_closure (iUnion_mono fun _ ↦ inter_subset_right)


  obtain ⟨i, hei⟩ : ∃ i, e ∈ M.closure (Xs i)
  · obtain ⟨I, hIss, hIfin, hI, heI⟩ := exists_mem_finite_closure_of_mem_closure hecl
    obtain ⟨A, hA, hIA⟩ := finite_subset_iUnion hIfin hIss
    obtain ⟨i, hi⟩ := aux A hA
    exact ⟨i, M.closure_subset_closure (hIA.trans hi) heI⟩

  exact M.mem_closure_of_mem' (mem_iUnion.2 ⟨i, heF, by rwa [← (hXs i).closure]⟩)
