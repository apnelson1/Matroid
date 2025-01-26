import Matroid.Loop
import Matroid.ForMathlib.Other
import Matroid.ForMathlib.Matroid.Sum

/- The rank `M.er X` of a set `X` in a matroid `M` is the size of one of its bases,
as a term in `ℕ∞`.
When such bases are infinite, this quantity is too coarse to be useful for building API,
even though it is often the easiest way to do things for finite matroids. -/

open Set ENat

namespace Matroid

variable {α ι : Type*} {M N : Matroid α} {I B X X' Y Y' Z R : Set α} {n : ℕ∞} {e f : α}

section Basic

/-- The rank `erk M` of `M` is the `ℕ∞`-valued cardinality of a base of `M`. -/
noncomputable def erk (M : Matroid α) : ℕ∞ :=
  M.exists_base.choose.encard

/-- The rank `er X` of a set `X` is the `ℕ∞`-valued cardinality of one of its bases. -/
noncomputable def er (M : Matroid α) (X : Set α) : ℕ∞ := (M ↾ X).erk

lemma erk_def (M : Matroid α) : M.erk = M.er M.E := by
  rw [er, restrict_ground_eq_self]

@[simp] lemma erk_restrict (M : Matroid α) (X : Set α) : (M ↾ X).erk = M.er X := rfl

lemma Basis'.encard (hI : M.Basis' I X) : I.encard = M.er X := by
  rw [er, erk, (M ↾ X).exists_base.choose_spec.card_eq_card_of_base hI]

lemma Basis.encard (hI : M.Basis I X) : I.encard = M.er X :=
  hI.basis'.encard

lemma eq_er_iff (hX : X ⊆ M.E := by aesop_mat) :
    M.er X = n ↔ ∃ I, M.Basis I X ∧ I.encard = n :=
  ⟨fun h ↦ (M.exists_basis X).elim (fun I hI ↦ ⟨I, hI, by rw [hI.encard, ← h]⟩),
    fun ⟨ I, hI, hIc⟩ ↦ by rw [← hI.encard, hIc]⟩

lemma Indep.er (hI : M.Indep I) : M.er I = I.encard :=
  (eq_er_iff hI.subset_ground).mpr ⟨I, hI.basis_self, rfl⟩

lemma Basis'.er (hIX : M.Basis' I X) : M.er I = M.er X := by rw [← hIX.encard, hIX.indep.er]

lemma Basis.er (hIX : M.Basis I X) : M.er I = M.er X := by rw [← hIX.encard, hIX.indep.er]

lemma Basis'.er_eq_encard (hIX : M.Basis' I X) : M.er X = I.encard := by
  rw [← hIX.er, hIX.indep.er]

lemma Basis.er_eq_encard (hIX : M.Basis I X) : M.er X = I.encard := by
  rw [← hIX.er, hIX.indep.er]

lemma Base.er (hB : M.Base B) : M.er B = M.erk := by
  rw [hB.indep.er, erk_def, hB.basis_ground.encard]

lemma Base.encard (hB : M.Base B) : B.encard = M.erk := by
  rw [hB.basis_ground.encard, erk_def]

@[simp] lemma erk_map {β : Type*} (M : Matroid α) (f : α → β) (hf : InjOn f M.E) :
    (M.map f hf).erk = M.erk := by
  obtain ⟨B, hB⟩ := M.exists_base
  rw [← (hB.map hf).encard, ← hB.encard, (hf.mono hB.subset_ground).encard_image]

@[simp] lemma erk_loopyOn (E : Set α) : (loopyOn E).erk = 0 := by
  simp [← (show (loopyOn E).Base ∅ by simp).encard]

@[simp] lemma erk_emptyOn (α : Type*) : (emptyOn α).erk = 0 := by
  simp [← (show (emptyOn α).Base ∅ by simp).encard]

@[simp] lemma er_inter_ground (M : Matroid α) (X : Set α) : M.er (X ∩ M.E) = M.er X := by
  obtain ⟨I, hI⟩ := M.exists_basis' X; rw [← hI.basis_inter_ground.encard, ← hI.encard]

lemma er_eq_erk (hX : M.E ⊆ X) : M.er X = M.erk := by
  rw [← er_inter_ground, inter_eq_self_of_subset_right hX, erk_def]

lemma one_le_erk (M : Matroid α) [RkPos M] : 1 ≤ M.erk := by
  obtain ⟨B, hB⟩ := M.exists_base
  rw [← hB.encard, one_le_encard_iff_nonempty]
  exact hB.nonempty

lemma finiteRk_iff_erk_ne_top : M.FiniteRk ↔ M.erk ≠ ⊤ := by
  obtain ⟨B, hB⟩ := M.exists_base
  rw [← hB.encard, encard_ne_top_iff]
  exact ⟨fun h ↦ hB.finite, fun h ↦ hB.finiteRk_of_finite h⟩

@[simp] lemma er_map_eq {β : Type*} {f : α → β} (M : Matroid α) (hf : InjOn f M.E)
    (hX : X ⊆ M.E := by aesop_mat) : (M.map f hf).er (f '' X) = M.er X := by
  obtain ⟨I, hI⟩ := M.exists_basis X
  rw [hI.er_eq_encard, (hI.map hf).er_eq_encard, (hf.mono hI.indep.subset_ground).encard_image]

@[simp] lemma er_comap_eq {β : Type*} {f : α → β} (M : Matroid β) (X : Set α) :
    (M.comap f).er X = M.er (f '' X) := by
  obtain ⟨I, hI⟩ := (M.comap f).exists_basis' X
  obtain ⟨hI', hinj, -⟩ := comap_basis'_iff.1 hI
  rw [← hI.encard, ← hI'.encard, hinj.encard_image]

-- lemma Iso.er_image_eq {α β : Type*} {M : Matroid α} {N : Matroid β} (e : Iso M N) (X : Set α)
--     (hX : X ⊆ M.E := by aesop_mat) : N.er (e '' X) = M.er X := by
--   obtain ⟨I,hI⟩ := M.exists_basis X
--   rw [hI.er_eq_encard, (e.on_basis hI).er_eq_encard,
--     (e.injOn_ground.mono hI.indep.subset_ground).encard_image]

@[simp] lemma er_univ_eq (M : Matroid α) : M.er univ = M.erk := by
  rw [← er_inter_ground, univ_inter, erk_def]


-- lemma Iso.erk_eq_erk {α β : Type*} {M : Matroid α} {N : Matroid β} (e : Iso M N) :
--     M.erk = N.erk := by
--   rw [erk_def, ← e.er_image_eq M.E, e.image_ground, erk_def]

@[simp] lemma er_empty (M : Matroid α) : M.er ∅ = 0 := by
  rw [← M.empty_indep.basis_self.encard, encard_empty]

@[simp] lemma er_closure_eq (M : Matroid α) (X : Set α) : M.er (M.closure X) = M.er X := by
  rw [← closure_inter_ground, ← M.er_inter_ground X]
  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E)
  rw [← hI.er, ← hI.closure_eq_closure, hI.indep.basis_closure.er]

@[simp] lemma er_union_closure_right_eq (M : Matroid α) (X Y : Set α) :
    M.er (X ∪ M.closure Y) = M.er (X ∪ Y) :=
  by rw [← er_closure_eq, closure_union_closure_right_eq, er_closure_eq]

@[simp] lemma er_union_closure_left_eq (M : Matroid α) (X Y : Set α) :
    M.er (M.closure X ∪ Y) = M.er (X ∪ Y) := by
  rw [← er_closure_eq, closure_union_closure_left_eq, er_closure_eq]

@[simp] lemma er_insert_closure_eq (M : Matroid α) (e : α) (X : Set α) :
    M.er (insert e (M.closure X)) = M.er (insert e X) := by
  rw [← union_singleton, er_union_closure_left_eq, union_singleton]

@[simp] lemma restrict_er_eq' (M : Matroid α) (R X : Set α) : (M ↾ R).er X = M.er (X ∩ R) := by
  obtain ⟨I, hI⟩ := (M ↾ R).exists_basis' X
  rw [hI.er_eq_encard]
  rw [basis'_iff_basis_inter_ground, basis_restrict_iff', restrict_ground_eq] at hI
  rw [← er_inter_ground, ← hI.1.er_eq_encard]

@[simp] lemma restrict_er_eq (M : Matroid α) (h : X ⊆ R) : (M ↾ R).er X = M.er X := by
  rw [restrict_er_eq', inter_eq_self_of_subset_left h]

lemma er_lt_top_of_finite (M : Matroid α) (hX : X.Finite) : M.er X < ⊤ := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  rw [hI.er_eq_encard, encard_lt_top_iff]
  exact hX.subset hI.subset

lemma Basis'.er_eq_er_union (hIX : M.Basis' I X) (Y : Set α) : M.er (I ∪ Y) = M.er (X ∪ Y) := by
  rw [← er_union_closure_left_eq, hIX.closure_eq_closure, er_union_closure_left_eq]

lemma Basis'.er_eq_er_insert (hIX : M.Basis' I X) (e : α) :
    M.er (insert e I) = M.er (insert e X) := by
  rw [← union_singleton, hIX.er_eq_er_union, union_singleton]

lemma Basis.er_eq_er_union (hIX : M.Basis I X) (Y : Set α) : M.er (I ∪ Y) = M.er (X ∪ Y) :=
  hIX.basis'.er_eq_er_union Y

lemma Basis.er_eq_er_insert (hIX : M.Basis I X) (e : α) : M.er (insert e I) = M.er (insert e X) :=
  by rw [← union_singleton, hIX.er_eq_er_union, union_singleton]

lemma er_le_encard (M : Matroid α) (X : Set α) : M.er X ≤ X.encard := by
  obtain ⟨I, hI⟩ := M.exists_basis' X; rw [hI.er_eq_encard]; exact encard_mono hI.subset

lemma erk_le_encard_ground (M : Matroid α) : M.erk ≤ M.E.encard :=
  M.erk_def.trans_le $ M.er_le_encard M.E

lemma er_mono (M : Matroid α) : Monotone M.er := by
  rintro X Y (hXY : X ⊆ Y)
  obtain ⟨I, hI⟩ := M.exists_basis' X
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_basis'_of_subset (hI.subset.trans hXY)
  rw [hI.er_eq_encard, hJ.er_eq_encard]
  exact encard_mono hIJ

lemma er_le_erk (M : Matroid α) (X : Set α) : M.er X ≤ M.erk := by
  rw [erk_def, ← er_inter_ground]; exact M.er_mono inter_subset_right

lemma le_er_iff : n ≤ M.er X ↔ ∃ I, I ⊆ X ∧ M.Indep I ∧ I.encard = n := by
  refine ⟨fun h ↦ ?_, fun ⟨I, hIX, hI, hIc⟩ ↦ ?_⟩
  · obtain ⟨J, hJ⟩ := M.exists_basis' X
    rw [← hJ.encard] at h
    obtain ⟨I, hIJ, rfl⟩ :=  exists_subset_encard_eq h
    exact ⟨_, hIJ.trans hJ.subset, hJ.indep.subset hIJ, rfl⟩
  rw [← hIc, ← hI.er]
  exact M.er_mono hIX

lemma er_le_iff : M.er X ≤ n ↔ ∀ {I}, I ⊆ X → M.Indep I → I.encard ≤ n := by
  refine ⟨fun h I hIX hI ↦ (hI.er.symm.trans_le ((M.er_mono hIX).trans h)), fun h ↦ ?_⟩
  obtain ⟨I, hI⟩ := M.exists_basis' X
  rw [← hI.encard]
  exact h hI.subset hI.indep

lemma Indep.encard_le_er_of_subset (hI : M.Indep I) (hIX : I ⊆ X) : I.encard ≤ M.er X := by
  rw [← hI.er]; exact M.er_mono hIX

lemma Indep.encard_le_erk (hI : M.Indep I) : I.encard ≤ M.erk := by
  rw [← hI.er, erk_def]; exact M.er_mono hI.subset_ground

/-- The `ℕ∞`-valued rank function is submodular. -/
lemma er_inter_add_er_union_le_er_add_er (M : Matroid α) (X Y : Set α) :
    M.er (X ∩ Y) + M.er (X ∪ Y) ≤ M.er X + M.er Y := by
  obtain ⟨Ii, hIi⟩ := M.exists_basis' (X ∩ Y)
  obtain ⟨IX, hIX, hIX'⟩ :=
    hIi.indep.subset_basis'_of_subset (hIi.subset.trans inter_subset_left)
  obtain ⟨IY, hIY, hIY'⟩ :=
    hIi.indep.subset_basis'_of_subset (hIi.subset.trans inter_subset_right)
  rw [← hIX.er_eq_er_union, union_comm, ← hIY.er_eq_er_union, ← hIi.encard, ← hIX.encard,
    ← hIY.encard, union_comm, ← encard_union_add_encard_inter, add_comm]
  exact add_le_add (er_le_encard _ _) (encard_mono (subset_inter hIX' hIY'))

alias er_submod := er_inter_add_er_union_le_er_add_er

lemma er_eq_er_of_subset_le (hXY : X ⊆ Y) (hYX : M.er Y ≤ M.er X) : M.er X = M.er Y :=
  (M.er_mono hXY).antisymm hYX

lemma er_union_le_er_add_er (M : Matroid α) (X Y : Set α) : M.er (X ∪ Y) ≤ M.er X + M.er Y :=
  le_add_self.trans (M.er_submod X Y)

lemma er_eq_er_union_er_le_zero (X : Set α) (hY : M.er Y ≤ 0) : M.er (X ∪ Y) = M.er X :=
  (((M.er_union_le_er_add_er X Y).trans (add_le_add_left hY _)).trans_eq (add_zero _)).antisymm
    (M.er_mono subset_union_left)

lemma er_eq_er_diff_er_le_zero (X : Set α) (hY : M.er Y ≤ 0) : M.er (X \ Y) = M.er X := by
  rw [← er_eq_er_union_er_le_zero (X \ Y) hY, diff_union_self, er_eq_er_union_er_le_zero _ hY]

lemma er_le_er_inter_add_er_diff (X Y : Set α) : M.er X ≤ M.er (X ∩ Y) + M.er (X \ Y) := by
  nth_rw 1 [← inter_union_diff X Y]; apply er_union_le_er_add_er

lemma er_le_er_add_er_diff (h : Y ⊆ X) : M.er X ≤ M.er Y + M.er (X \ Y) := by
  nth_rw 1 [← union_diff_cancel h]; apply er_union_le_er_add_er

lemma indep_iff_er_eq_encard_of_finite (hI : I.Finite) : M.Indep I ↔ M.er I = I.encard := by
  refine ⟨fun h ↦ by rw [h.er], fun h ↦ ?_⟩
  obtain ⟨J, hJ⟩ := M.exists_basis' I
  rw [← hI.eq_of_subset_of_encard_le hJ.subset]
  · exact hJ.indep
  rw [← h, ← hJ.er_eq_encard]

lemma indep_iff_er_eq_card [Matroid.Finite M] (hI : I ⊆ M.E := by aesop_mat) :
    M.Indep I ↔ M.er I = I.encard :=
  indep_iff_er_eq_encard_of_finite (M.set_finite I)

lemma er_singleton_le (M : Matroid α) (e : α) : M.er {e} ≤ 1 := by
  obtain ⟨J, hJ⟩ := M.exists_basis' {e}
  rw [hJ.er_eq_encard, ← encard_singleton e]
  exact encard_mono hJ.subset

lemma er_lt_encard_of_dep_of_finite (h : X.Finite) (hX : M.Dep X) : M.er X < X.encard :=
  lt_of_le_of_ne (M.er_le_encard X) fun h' ↦
    ((indep_iff_er_eq_encard_of_finite h).mpr h').not_dep hX

lemma er_lt_encard_iff_dep_of_finite (hX : X.Finite) (hXE : X ⊆ M.E := by aesop_mat) :
    M.er X < X.encard ↔ M.Dep X := by
  refine ⟨fun h ↦ ?_, fun h ↦ er_lt_encard_of_dep_of_finite hX h⟩
  rw [← not_indep_iff, indep_iff_er_eq_encard_of_finite hX]
  exact h.ne

lemma er_lt_encard_of_dep [Matroid.Finite M] (hX : M.Dep X) : M.er X < X.encard :=
  er_lt_encard_of_dep_of_finite (M.set_finite X hX.subset_ground) hX

lemma r_lt_card_iff_dep [Matroid.Finite M] (hXE : X ⊆ M.E := by aesop_mat) :
    M.er X < X.encard ↔ M.Dep X :=
  er_lt_encard_iff_dep_of_finite (M.set_finite X)

lemma basis'_iff_indep_encard_eq_of_finite (hIfin : I.Finite) :
    M.Basis' I X ↔ I ⊆ X ∧ M.Indep I ∧ I.encard = M.er X := by
  refine ⟨fun h ↦ ⟨h.subset,h.indep, h.er_eq_encard.symm⟩, fun ⟨hIX, hI, hcard⟩ ↦ ?_⟩
  rw [basis'_iff_basis_inter_ground]
  obtain ⟨J, hJ, hIJ⟩ := hI.subset_basis_of_subset (subset_inter hIX hI.subset_ground)
  apply hI.basis_of_subset_of_subset_closure (subset_inter hIX hI.subset_ground)
  obtain rfl := hIfin.eq_of_subset_of_encard_le' hIJ
    (by rw [hcard, ← hJ.er_eq_encard, er_inter_ground ])
  exact hJ.subset_closure

lemma basis_iff_indep_encard_eq_of_finite (hIfin : I.Finite) (hX : X ⊆ M.E := by aesop_mat) :
    M.Basis I X ↔ I ⊆ X ∧ M.Indep I ∧ I.encard = M.er X := by
  rw [← basis'_iff_basis, basis'_iff_indep_encard_eq_of_finite hIfin]

lemma Indep.basis_of_subset_of_er_le_of_finite (hI : M.Indep I) (hIX : I ⊆ X)
    (h : M.er X ≤ M.er I) (hIfin : I.Finite) (hX : X ⊆ M.E := by aesop_mat) : M.Basis I X := by
  rw [basis_iff_indep_encard_eq_of_finite hIfin hX, and_iff_right hIX, and_iff_right hI,
     le_antisymm_iff, and_iff_left (h.trans hI.er.le), ← hI.er]
  exact M.er_mono hIX

lemma Indep.base_of_encard (hI : M.Indep I) (hIfin : I.Finite) (hIcard : M.erk ≤ I.encard) :
    M.Base I := by
  rw [← basis_ground_iff]
  refine hI.basis_of_subset_of_er_le_of_finite hI.subset_ground ?_ hIfin
  rwa [← erk_def, hI.er]

lemma er_insert_le_add_one (M : Matroid α) (e : α) (X : Set α) :
    M.er (insert e X) ≤ M.er X + 1 := by
  rw [← union_singleton]
  exact (M.er_union_le_er_add_er _ _).trans (add_le_add_left (er_singleton_le _ _) _)

lemma er_union_le_encard_add_er (M : Matroid α) (X Y : Set α) :
    M.er (X ∪ Y) ≤ X.encard + M.er Y :=
  (M.er_union_le_er_add_er X Y).trans (add_le_add_right (M.er_le_encard _) _)

lemma er_union_le_er_add_encard (M : Matroid α) (X Y : Set α) :
    M.er (X ∪ Y) ≤ M.er X + Y.encard :=
  (M.er_union_le_er_add_er X Y).trans (add_le_add_left (M.er_le_encard _) _)

lemma erk_le_encard_add_er_compl (M : Matroid α) (X : Set α) :
    M.erk ≤ X.encard + M.er (M.E \ X) :=
  le_trans (by rw [← er_inter_ground, erk_def, union_diff_self,
    union_inter_cancel_right]) (M.er_union_le_encard_add_er X (M.E \ X))

lemma er_insert_eq_add_one (M : Matroid α) (X : Set α) (he : e ∈ M.E \ M.closure X) :
    M.er (insert e X) = M.er X + 1 := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  rw [← hI.closure_eq_closure] at he
  rw [← er_closure_eq, ← closure_insert_closure_eq_closure_insert, ← hI.closure_eq_closure,
    hI.er_eq_encard, closure_insert_closure_eq_closure_insert, er_closure_eq, Indep.er,
    encard_insert_of_not_mem]
  · exact fun heI ↦ he.2 (M.subset_closure I hI.indep.subset_ground heI)
  rw [hI.indep.insert_indep_iff]
  exact Or.inl he

lemma er_augment (h : M.er X < M.er Z) : ∃ z ∈ Z \ X, M.er (insert z X) = M.er X + 1 := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_basis'_of_subset (hI.subset.trans subset_union_left)
  have hlt := h.trans_le (M.er_mono (subset_union_right (s := X)))
  rw [hI.er_eq_encard, hJ.er_eq_encard] at hlt
  obtain ⟨e, heJ, heI⟩ := exists_of_ssubset (hIJ.ssubset_of_ne (by rintro rfl; exact hlt.ne rfl))
  have heIi : M.Indep (insert e I) := hJ.indep.subset (insert_subset heJ hIJ)
  have heX : e ∉ X := fun h ↦
    heI (hI.basis_inter_ground.mem_of_insert_indep ⟨h, hJ.indep.subset_ground heJ⟩ heIi)
  refine ⟨e, ⟨Or.elim (hJ.subset heJ) (False.elim ∘ heX) id, heX⟩, ?_⟩
  rw [← hI.er_eq_er_insert, hI.er_eq_encard, heIi.er, encard_insert_of_not_mem heI]

lemma er_eq_of_er_insert_le_forall (hXY : X ⊆ Y) (hY : ∀ e ∈ Y \ X, M.er (insert e X) ≤ M.er X) :
    M.er X = M.er Y := by
  refine (M.er_mono hXY).eq_of_not_lt (fun hlt ↦ ?_)
  obtain ⟨e, he, hins⟩ := er_augment hlt
  specialize hY e he
  rw [← add_zero (M.er X), hins,
    WithTop.add_le_add_iff_left (fun htop ↦ not_top_lt (htop ▸ hlt))] at hY
  simp at hY

lemma Indep.exists_insert_of_encard_lt {I J : Set α} (hI : M.Indep I) (hJ : M.Indep J)
    (hcard : I.encard < J.encard) : ∃ e ∈ J \ I, M.Indep (insert e I) := by
  have hIfin : I.Finite := encard_lt_top_iff.1 <| hcard.trans_le le_top
  rw [← hI.er, ← hJ.er] at hcard
  obtain ⟨e, he, hIe⟩ := er_augment hcard
  refine ⟨e, he, ?_⟩
  rw [indep_iff_er_eq_encard_of_finite (hIfin.insert e), hIe, encard_insert_of_not_mem he.2,
    hI.er]

lemma spanning_iff_er' [FiniteRk M] : M.Spanning X ↔ M.erk ≤ M.er X ∧ X ⊆ M.E := by
  refine ⟨fun h ↦ ?_, fun ⟨hr, hX⟩ ↦ ?_⟩
  · rw [erk_def, ← er_closure_eq _ X, h.closure_eq]; exact ⟨rfl.le, h.subset_ground⟩
  obtain ⟨J, hJ⟩ := M.exists_basis X
  obtain ⟨B, hB, hJB⟩ := hJ.indep.exists_base_superset
  rw [← hJ.encard, ← hB.encard] at hr
  obtain rfl := hB.finite.eq_of_subset_of_encard_le hJB hr
  rw [spanning_iff_exists_base_subset]
  exact ⟨J, hB, hJ.subset⟩

lemma spanning_iff_er [FiniteRk M] (hX : X ⊆ M.E := by aesop_mat) :
    M.Spanning X ↔ M.erk ≤ M.er X := by
  rw [spanning_iff_er', and_iff_left hX]

lemma Spanning.er_eq (hX : M.Spanning X) : M.er X = M.erk := by
  obtain ⟨B, hB, hBX⟩ := hX.exists_base_subset
  rw [le_antisymm_iff, and_iff_right (M.er_le_erk _), ← hB.er]
  exact M.er_mono hBX

lemma Spanning.erk_restrict (hX : M.Spanning X) : (M ↾ X).erk = M.erk := by
  rw [erk_def, restrict_ground_eq, restrict_er_eq _ rfl.subset, hX.er_eq]

lemma Loop.er_eq (he : M.Loop e) : M.er {e} = 0 := by
  rw [← er_closure_eq, he.closure, er_closure_eq, er_empty]

lemma Nonloop.er_eq (he : M.Nonloop e) : M.er {e} = 1 := by
  rw [← he.indep.basis_self.encard, encard_singleton]

lemma er_singleton_eq [Loopless M] (he : e ∈ M.E := by aesop_mat) :
    M.er {e} = 1 :=
  (M.toNonloop he).er_eq

@[simp] lemma er_singleton_eq_one_iff {e : α} : M.er {e} = 1 ↔ M.Nonloop e := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.er_eq⟩
  rwa [← indep_singleton, indep_iff_er_eq_encard_of_finite (by simp), encard_singleton]

lemma LoopEquiv.er_eq_er (h : M.LoopEquiv X Y) : M.er X = M.er Y := by
  rw [← M.er_closure_eq, h.closure_eq_closure, M.er_closure_eq]

lemma er_eq_zero_iff (hX : X ⊆ M.E := by aesop_mat) :
    M.er X = 0 ↔ X ⊆ M.closure ∅ := by
  obtain ⟨I, hI⟩ := M.exists_basis X
  rw [← hI.encard, encard_eq_zero]
  exact ⟨by rintro rfl; exact hI.subset_closure, fun h ↦ eq_empty_of_forall_not_mem
    fun x hx ↦ (hI.indep.nonloop_of_mem hx).not_loop (h (hI.subset hx))⟩

lemma er_eq_zero_iff' : M.er X = 0 ↔ X ∩ M.E ⊆ M.closure ∅ := by
  rw [← er_inter_ground, er_eq_zero_iff]

@[simp] lemma er_loops (M : Matroid α) : M.er (M.closure ∅) = 0 := by
  rw [er_eq_zero_iff]

lemma er_eq_one_iff (hX : X ⊆ M.E := by aesop_mat) :
    M.er X = 1 ↔ ∃ e ∈ X, M.Nonloop e ∧ X ⊆ M.closure {e} := by
  refine ⟨?_, fun ⟨e, heX, he, hXe⟩ ↦ ?_⟩
  · obtain ⟨I, hI⟩ := M.exists_basis X
    rw [hI.er_eq_encard, encard_eq_one]
    rintro ⟨e, rfl⟩
    exact ⟨e, singleton_subset_iff.1 hI.subset, indep_singleton.1 hI.indep, hI.subset_closure⟩
  rw [← he.er_eq]
  exact ((M.er_mono hXe).trans (M.er_closure_eq _).le).antisymm
    (M.er_mono (singleton_subset_iff.2 heX))

lemma er_le_one_iff [M.Nonempty] (hX : X ⊆ M.E := by aesop_mat) :
    M.er X ≤ 1 ↔ ∃ e ∈ M.E, X ⊆ M.closure {e} := by
  refine ⟨fun h ↦ ?_, fun ⟨e, _, he⟩ ↦ ?_⟩
  · obtain ⟨I, hI⟩ := M.exists_basis X
    rw [hI.er_eq_encard, encard_le_one_iff_eq] at h
    obtain (rfl | ⟨e, rfl⟩) := h
    · exact ⟨M.ground_nonempty.some, M.ground_nonempty.some_mem,
        hI.subset_closure.trans ((M.closure_subset_closure (empty_subset _)))⟩
    exact ⟨e, hI.indep.subset_ground rfl,  hI.subset_closure⟩
  refine (M.er_mono he).trans ?_
  rw [er_closure_eq, ← encard_singleton e]
  exact M.er_le_encard {e}

lemma Base.encard_compl_eq (hB : M.Base B) : (M.E \ B).encard = M✶.erk :=
  (hB.compl_base_dual).encard

lemma dual_er_add_erk (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    M✶.er X + M.erk = M.er (M.E \ X) + X.encard := by
  obtain ⟨I, hI⟩ := M✶.exists_basis X
  obtain ⟨B, hB, hIB⟩ := hI.indep.exists_base_superset
  obtain rfl : I = X ∩ B :=
    hI.eq_of_subset_indep (hB.indep.inter_left X) (subset_inter hI.subset hIB) inter_subset_left
  rw [inter_comm] at hI
  have hIdual : M.Basis (M.E \ B ∩ (M.E \ X)) (M.E \ X) :=
    by simpa using hB.inter_basis_iff_compl_inter_basis_dual.1 hI
  rw [← hIdual.encard, ← hI.encard, ← hB.compl_base_of_dual.encard, ← encard_union_eq,
    ← encard_union_eq]
  · convert rfl using 2
    ext x
    simp only [mem_union, mem_inter_iff, mem_diff]
    tauto
  · exact disjoint_sdiff_left.mono_left inter_subset_right
  exact disjoint_sdiff_right.mono_left inter_subset_left

lemma dual_er_add_erk' (M : Matroid α) (X : Set α) :
    M✶.er X + M.erk = M.er (M.E \ X) + (X ∩ M.E).encard := by
  rw [← diff_inter_self_eq_diff, ← dual_er_add_erk .., ← dual_ground, er_inter_ground]

lemma erk_add_dual_erk (M : Matroid α) : M.erk + M✶.erk = M.E.encard := by
  obtain ⟨B, hB⟩ := M.exists_base
  rw [← hB.encard, ← hB.compl_base_dual.encard, ← encard_union_eq disjoint_sdiff_right,
    union_diff_cancel hB.subset_ground]

lemma Circuit.er_add_one_eq {C : Set α} (hC : M.Circuit C) : M.er C + 1 = C.encard := by
  obtain ⟨I, hI⟩ := M.exists_basis C
  obtain ⟨e, ⟨heC, heI⟩, rfl⟩ := hC.basis_iff_insert_eq.1 hI
  rw [hI.er_eq_encard, encard_insert_of_not_mem heI]

end Basic

section Constructions

variable {E : Set α}

@[simp] lemma loopyOn_er_eq (E X : Set α) : (loopyOn E).er X = 0 := by
  obtain ⟨I, hI⟩ := (loopyOn E).exists_basis' X
  rw [hI.er_eq_encard, loopyOn_indep_iff.1 hI.indep, encard_empty]

@[simp] lemma loopyOn_erk_eq (E : Set α) : (loopyOn E).erk = 0 := by
  rw [erk_def, loopyOn_er_eq]

-- @[simp] lemma loopyOn_r_eq (E X : Set α) : (loopyOn E).r X = 0 := by
--   rw [← er_toNat_eq_r, loopyOn_er_eq]; rfl

@[simp] lemma erk_eq_zero_iff : M.erk = 0 ↔ M = loopyOn M.E := by
  refine ⟨fun h ↦ closure_empty_eq_ground_iff.1 ?_, fun h ↦ by rw [h, loopyOn_erk_eq]⟩
  obtain ⟨B, hB⟩ := M.exists_base
  rw [← hB.encard, encard_eq_zero] at h
  rw [← h, hB.closure_eq]

@[simp] lemma erk_loopyOn_eq_zero (α : Type*) : (emptyOn α).erk = 0 := by
  rw [erk_eq_zero_iff, emptyOn_ground, loopyOn_empty]

lemma eq_loopyOn_iff_closure : M = loopyOn E ↔ M.closure ∅ = E ∧ M.E = E :=
  ⟨fun h ↦ by rw [h]; simp, fun ⟨h,h'⟩ ↦ by rw [← h', ← closure_empty_eq_ground_iff, h, h']⟩

lemma eq_loopyOn_iff_erk : M = loopyOn E ↔ M.erk = 0 ∧ M.E = E :=
  ⟨fun h ↦ by rw [h]; simp, fun ⟨h,h'⟩ ↦ by rw [← h', ← erk_eq_zero_iff, h]⟩

@[simp] lemma freeOn_erk_eq (E : Set α) : (freeOn E).erk = E.encard := by
  rw [erk_def, freeOn_ground, (freeOn_indep_iff.2 rfl.subset).er]

lemma freeOn_er_eq (hXE : X ⊆ E) : (freeOn E).er X = X.encard := by
  obtain ⟨I, hI⟩ := (freeOn E).exists_basis X
  rw [hI.er_eq_encard, (freeOn_indep hXE).eq_of_basis hI]

-- lemma freeOn_r_eq (hXE : X ⊆ E) : (freeOn E).r X = X.ncard := by
--   rw [← er_toNat_eq_r, freeOn_er_eq hXE, ncard_def]

@[simp] lemma disjointSum_er_eq (M N : Matroid α) (hMN : Disjoint M.E N.E) (X : Set α) :
    (M.disjointSum N hMN).er X = M.er (X ∩ M.E) + N.er (X ∩ N.E) := by
  obtain ⟨B₁, hB₁⟩ := M.exists_basis (X ∩ M.E)
  obtain ⟨B₂, hB₂⟩ := N.exists_basis (X ∩ N.E)
  rw [← er_inter_ground, disjointSum_ground_eq, inter_union_distrib_left,
    (hB₁.disjointSum_basis_union hB₂ hMN).er_eq_encard, hB₁.er_eq_encard, hB₂.er_eq_encard,
    encard_union_eq (hMN.mono hB₁.indep.subset_ground hB₂.indep.subset_ground)]

@[simp] lemma disjointSum_erk_eq (M N : Matroid α) (hMN : Disjoint M.E N.E) :
    (M.disjointSum N hMN).erk = M.erk + N.erk := by
  rw [erk_def, erk_def, erk_def, disjointSum_er_eq, disjointSum_ground_eq,
    inter_eq_self_of_subset_right subset_union_left,
    inter_eq_self_of_subset_right subset_union_right]

end Constructions

section Nullity
/-- The rank-deficiency of a set, as a term in `ℕ∞`. Cannot be defined with subtraction.
For the `ℕ` version, the simpler expression `X.ncard - M.r X` is preferable.

To reduce the number of `X ⊆ M.E` assumptions needed for lemmas,
this is defined so that elements in `X \ M.E` contribute to the nullity of `X` in `M`,
so `M.nullity X = M.nullity (X ∩ M.E) + (X \ M.E).encard`.
(see `Matroid.nullity_eq_nullity_inter_ground_add_encard_diff` )-/
noncomputable def nullity (M : Matroid α) (X : Set α) : ℕ∞ := (M ↾ X)✶.erk

lemma nullity_eq_erk_restrict_dual (M : Matroid α) (X : Set α) :
    M.nullity X = (M ↾ X)✶.erk := rfl

lemma nullity_restrict_of_subset (M : Matroid α) (hXY : X ⊆ Y) :
    (M ↾ Y).nullity X = M.nullity X := by
  rw [nullity, restrict_restrict_eq _ hXY, nullity]

lemma nullity_restrict_self (M : Matroid α) (X : Set α) : (M ↾ X).nullity X = M.nullity X :=
  M.nullity_restrict_of_subset rfl.subset

lemma Basis'.nullity_eq (hIX : M.Basis' I X) : M.nullity X = (X \ I).encard := by
  rw [M.nullity_eq_erk_restrict_dual, ← (base_restrict_iff'.2 hIX).compl_base_dual.encard,
    restrict_ground_eq]

lemma Basis.nullity_eq (hIX : M.Basis I X) : M.nullity X = (X \ I).encard :=
  hIX.basis'.nullity_eq

lemma er_add_nullity_eq_encard (M : Matroid α) (X : Set α) :
    M.er X + M.nullity X = X.encard := by
  have h := (M ↾ X)✶.erk_add_dual_erk
  simp only [dual_dual, erk_restrict, dual_ground, restrict_ground_eq] at h
  rw [← h, add_comm, nullity_eq_erk_restrict_dual]

lemma Indep.nullity_eq (hI : M.Indep I) : M.nullity I = 0 := by
  rw [hI.basis_self.nullity_eq, diff_self, encard_empty]

lemma nullity_eq_zero : M.nullity I = 0 ↔ M.Indep I := by
  rw [iff_def, and_iff_left Indep.nullity_eq]
  obtain ⟨J, hJI⟩ := M.exists_basis' I
  rw [hJI.nullity_eq, encard_eq_zero, diff_eq_empty]
  exact hJI.indep.subset

lemma nullity_eq_nullity_inter_ground_add_encard_diff :
    M.nullity X = M.nullity (X ∩ M.E) + (X \ M.E).encard := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  rw [hI.nullity_eq, hI.basis_inter_ground.nullity_eq, ← encard_union_eq]
  · nth_rw 1 [← inter_union_diff X M.E, union_diff_distrib, diff_diff,
      union_eq_self_of_subset_right hI.indep.subset_ground]
  exact disjoint_sdiff_right.mono_left (diff_subset.trans inter_subset_right)

lemma nullity_le_of_subset (M : Matroid α) (hXY : X ⊆ Y) : M.nullity X ≤ M.nullity Y := by
  rw [← M.nullity_restrict_of_subset hXY, ← M.nullity_restrict_self Y]
  obtain ⟨I, hI⟩ := (M ↾ Y).exists_basis X
  obtain ⟨B, hB, rfl⟩ := hI.exists_base
  rw [← basis_ground_iff, restrict_ground_eq] at hB
  rw [hI.nullity_eq, hB.nullity_eq, diff_inter_self_eq_diff]
  exact encard_le_card (diff_subset_diff_left hXY)

end Nullity
