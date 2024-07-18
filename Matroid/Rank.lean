import Matroid.Loop

/- The rank of a set in a matroid `M` is the size of one of its bases. When such bases are infinite,
  this quantity is too coarse to be useful for building API,
  even though it is often the easiest way to do things for finite matroids.
   -/

open Set
open ENat

namespace Matroid

variable {α ι : Type*} {M N : Matroid α} {I B X X' Y Y' Z R : Set α} {n : ℕ∞} {e f : α}
section Basic

/-- The rank `erk M` of `M` is the cardinality of a base of `M`. -/
noncomputable def erk (M : Matroid α) : ℕ∞ :=
  ⨅ B : {B | M.Base B}, (B : Set α).encard

/-- The rank `er X` of a set `X` is the cardinality of one of its bases -/
noncomputable def er (M : Matroid α) (X : Set α) : ℕ∞ := (M ↾ X).erk

lemma erk_eq_er_ground (M : Matroid α) : M.erk = M.er M.E := by
  rw [er, restrict_ground_eq_self]

@[simp] lemma erk_restrict (M : Matroid α) (X : Set α) : (M ↾ X).erk = M.er X := rfl

lemma Basis'.encard (hI : M.Basis' I X) : I.encard = M.er X := by
  rw [er,erk]
  rw [← base_restrict_iff'] at hI
  have : _root_.Nonempty ↑{B | (M ↾ X).Base B} := ⟨I, hI⟩
  rw [iInf_congr (_ : ∀ B : ↑{B | (M ↾ X).Base B}, (B : Set α).encard = I.encard), iInf_const]
  simp only [mem_setOf_eq, Subtype.forall]
  exact fun B' hB' ↦ hB'.card_eq_card_of_base hI

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
  rw [hB.indep.er, erk_eq_er_ground, hB.basis_ground.encard]

lemma Base.encard (hB : M.Base B) : B.encard = M.erk := by
  rw [hB.basis_ground.encard, erk_eq_er_ground]

@[simp] lemma erk_map {β : Type*} (M : Matroid α) (f : α → β) (hf : InjOn f M.E) :
    (M.map f hf).erk = M.erk := by
  obtain ⟨B, hB⟩ := M.exists_base
  rw [← (hB.map hf).encard, ← hB.encard, (hf.mono hB.subset_ground).encard_image]

@[simp] lemma erk_loopyOn (E : Set α) : (loopyOn E).erk = 0 := by
  simp [← (show (loopyOn E).Base ∅ by simp).encard]

@[simp] lemma erk_emptyOn (α : Type*) : (emptyOn α).erk = 0 := by
  simp [← (show (emptyOn α).Base ∅ by simp).encard]

@[simp] lemma er_inter_ground_eq (M : Matroid α) (X : Set α) : M.er (X ∩ M.E) = M.er X := by
  obtain ⟨I, hI⟩ := M.exists_basis' X; rw [← hI.basis_inter_ground.encard, ← hI.encard]

lemma er_map_eq {β : Type*} {f : α → β} (M : Matroid α) (hf : InjOn f M.E)
    (hX : X ⊆ M.E := by aesop_mat) : (M.map f hf).er (f '' X) = M.er X := by
  obtain ⟨I, hI⟩ := M.exists_basis X
  rw [hI.er_eq_encard, (hI.map hf).er_eq_encard, (hf.mono hI.indep.subset_ground).encard_image]

@[simp] lemma er_univ_eq (M : Matroid α) : M.er univ = M.erk := by
  rw [← er_inter_ground_eq, univ_inter, erk_eq_er_ground]

@[simp] lemma er_empty (M : Matroid α) : M.er ∅ = 0 := by
  rw [← M.empty_indep.basis_self.encard, encard_empty]

@[simp] lemma er_closure_eq (M : Matroid α) (X : Set α) : M.er (M.closure X) = M.er X := by
  rw [← M.er_inter_ground_eq X, ← M.er_inter_ground_eq, closure_self_inter_ground_eq]
  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E)
  rw [hI.closure_eq_closure, ← hI.indep.basis_closure.er, hI.er]

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
  rw [← er_inter_ground_eq, ← hI.1.er_eq_encard]

@[simp] lemma restrict_er_eq (M : Matroid α) (h : X ⊆ R) : (M ↾ R).er X = M.er X := by
  rw [restrict_er_eq', inter_eq_self_of_subset_left h]

@[simp] lemma restrict_univ_er_eq (M : Matroid α) (X : Set α) : (M ↾ univ).er X = M.er X := by
  simp [restrict_er_eq]

lemma er_lt_top_of_finite (M : Matroid α) (hX : X.Finite) : M.er X < ⊤ := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  rw [hI.er_eq_encard, encard_lt_top_iff]
  exact hX.subset hI.subset

lemma Basis'.er_eq_er_union (hIX : M.Basis' I X) (Y : Set α) : M.er (I ∪ Y) = M.er (X ∪ Y) := by
  rw [← er_union_closure_left_eq, hIX.closure_eq_closure, er_union_closure_left_eq,
    ← er_inter_ground_eq, union_inter_distrib_right, inter_assoc, inter_self, eq_comm,
    ← er_inter_ground_eq, union_inter_distrib_right]

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
  M.erk_eq_er_ground.trans_le $ M.er_le_encard M.E

lemma er_mono (M : Matroid α) : Monotone M.er := by
  rintro X Y (hXY : X ⊆ Y)
  obtain ⟨I, hI⟩ := M.exists_basis' X
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_basis'_of_subset (hI.subset.trans hXY)
  rw [hI.er_eq_encard, hJ.er_eq_encard]
  exact encard_mono hIJ

lemma er_le_erk (M : Matroid α) (X : Set α) : M.er X ≤ M.erk := by
  rw [erk_eq_er_ground, ← er_inter_ground_eq]; exact M.er_mono inter_subset_right

lemma le_er_iff : n ≤ M.er X ↔ ∃ I, I ⊆ X ∧ M.Indep I ∧ I.encard = n := by
  refine' ⟨fun h ↦ _, fun ⟨I, hIX, hI, hIc⟩ ↦ _⟩
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
  rw [← hI.er, erk_eq_er_ground]; exact M.er_mono hI.subset_ground

/-- The submodularity axiom for the extended rank function -/
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
  refine' ⟨fun h ↦ by rw [h.er], fun h ↦ _⟩
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
  refine' ⟨fun h ↦ _, fun h ↦ er_lt_encard_of_dep_of_finite hX h⟩
  rw [← not_indep_iff, indep_iff_er_eq_encard_of_finite hX]
  exact h.ne

lemma er_lt_encard_of_dep [Matroid.Finite M] (hX : M.Dep X) : M.er X < X.encard :=
  er_lt_encard_of_dep_of_finite (M.set_finite X hX.subset_ground) hX

lemma r_lt_card_iff_dep [Matroid.Finite M] (hXE : X ⊆ M.E := by aesop_mat) :
    M.er X < X.encard ↔ M.Dep X :=
  er_lt_encard_iff_dep_of_finite (M.set_finite X)

lemma basis'_iff_indep_encard_eq_of_finite (hIfin : I.Finite) :
    M.Basis' I X ↔ I ⊆ X ∧ M.Indep I ∧ I.encard = M.er X := by
  refine' ⟨fun h ↦ ⟨h.subset,h.indep, h.er_eq_encard.symm⟩, fun ⟨hIX, hI, hcard⟩  ↦ _⟩
  rw [basis'_iff_basis_inter_ground]
  obtain ⟨J, hJ, hIJ⟩ := hI.subset_basis_of_subset (subset_inter hIX hI.subset_ground)
  apply hI.basis_of_subset_of_subset_closure (subset_inter hIX hI.subset_ground)
  obtain rfl := hIfin.eq_of_subset_of_encard_le' hIJ
    (by rw [hcard, ← hJ.er_eq_encard, er_inter_ground_eq ])
  exact hJ.subset_closure

lemma basis_iff_indep_encard_eq_of_finite (hIfin : I.Finite) (hX : X ⊆ M.E := by aesop_mat) :
    M.Basis I X ↔ I ⊆ X ∧ M.Indep I ∧ I.encard = M.er X := by
  rw [← basis'_iff_basis, basis'_iff_indep_encard_eq_of_finite hIfin]

lemma Indep.basis_of_subset_of_er_le_of_finite (hI : M.Indep I) (hIX : I ⊆ X)
    (h : M.er X ≤ M.er I) (hIfin : I.Finite) (hX : X ⊆ M.E := by aesop_mat) : M.Basis I X := by
  rw [basis_iff_indep_encard_eq_of_finite hIfin hX, and_iff_right hIX, and_iff_right hI,
     le_antisymm_iff, and_iff_left (h.trans hI.er.le), ← hI.er]
  exact M.er_mono hIX

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
  le_trans (by rw [← er_inter_ground_eq, erk_eq_er_ground, union_diff_self,
    union_inter_cancel_right]) (M.er_union_le_encard_add_er X (M.E \ X))

lemma er_insert_eq_add_one (M : Matroid α) (X : Set α) (he : e ∈ M.E) (heX : e ∉ M.closure X) :
    M.er (insert e X) = M.er X + 1 := by
  rw [← er_inter_ground_eq, insert_inter_of_mem he, ← er_inter_ground_eq M X]
  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E)
  have hI' : M.Basis (insert e I) (insert e (X ∩ M.E)) := by
    refine hI.insert_basis_insert ?_
    rw [hI.indep.insert_indep_iff, ← hI.closure_eq_closure, mem_diff, and_iff_right he,
      ← imp_iff_not_or]
    exact fun h ↦ False.elim <| not_mem_subset (M.closure_mono inter_subset_left) heX h
  rw [hI.er_eq_encard, hI'.er_eq_encard, encard_insert_of_not_mem]
  exact not_mem_subset (hI.subset.trans (inter_subset_left.trans (M.subset_closure X))) heX

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
  refine' ⟨fun h ↦ _, fun ⟨hr, hX⟩ ↦ _⟩
  · rw [erk_eq_er_ground, ← er_closure_eq _ X, h.closure_eq]; exact ⟨rfl.le, h.subset_ground⟩
  obtain ⟨J, hJ⟩ := M.exists_basis X
  obtain ⟨B, hB, hJB⟩ := hJ.indep.exists_base_superset
  rw [← hJ.encard, ← hB.encard] at hr
  obtain rfl := hB.finite.eq_of_subset_of_encard_le hJB hr
  rw [spanning_iff_superset_base]
  exact ⟨J, hB, hJ.subset⟩

lemma spanning_iff_er [FiniteRk M] (hX : X ⊆ M.E := by aesop_mat) :
    M.Spanning X ↔ M.erk ≤ M.er X := by
  rw [spanning_iff_er', and_iff_left hX]

lemma Spanning.er_eq (hX : M.Spanning X) : M.er X = M.erk := by
  obtain ⟨B, hB, hBX⟩ := hX.exists_base_subset
  rw [le_antisymm_iff, and_iff_right (M.er_le_erk _), ← hB.er]
  exact M.er_mono hBX

lemma Loop.er_eq (he : M.Loop e) : M.er {e} = 0 := by
  rw [← er_closure_eq, he.closure, er_closure_eq, er_empty]

lemma Nonloop.er_eq (he : M.Nonloop e) : M.er {e} = 1 := by
  rw [← he.indep.basis_self.encard, encard_singleton]

lemma er_singleton_eq [Loopless M] (he : e ∈ M.E := by aesop_mat) :
    M.er {e} = 1 :=
  (M.toNonloop he).er_eq

lemma LoopEquiv.er_eq_er (h : M.LoopEquiv X Y) : M.er X = M.er Y := by
  rw [← M.er_closure_eq, h.closure_eq_closure, M.er_closure_eq]

lemma er_eq_zero_iff (hX : X ⊆ M.E := by aesop_mat) :
    M.er X = 0 ↔ X ⊆ M.closure ∅ := by
  obtain ⟨I, hI⟩ := M.exists_basis X
  rw [← hI.encard, encard_eq_zero]
  exact ⟨by rintro rfl; exact hI.subset_closure, fun h ↦ eq_empty_of_forall_not_mem
    fun x hx ↦ (hI.indep.nonloop_of_mem hx).not_loop (h (hI.subset hx))⟩

lemma er_eq_zero_iff' : M.er X = 0 ↔ X ∩ M.E ⊆ M.closure ∅ := by
  rw [← er_inter_ground_eq, er_eq_zero_iff]

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
  exact ((M.er_mono hXe).trans (M.er_closure_eq _).le).antisymm (M.er_mono (singleton_subset_iff.2 heX))

lemma er_le_one_iff [M.Nonempty] (hX : X ⊆ M.E := by aesop_mat) :
    M.er X ≤ 1 ↔ ∃ e ∈ M.E, X ⊆ M.closure {e} := by
  refine' ⟨fun h ↦ _, fun ⟨e, _, he⟩ ↦ _⟩
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

end Basic

section FinRank

def FinRank (M : Matroid α) (X : Set α) :=
  M.er X < ⊤

@[simp] lemma er_lt_top_iff : M.er X < ⊤ ↔ M.FinRank X := Iff.rfl

@[simp] lemma er_ne_top_iff : M.er X ≠ ⊤ ↔ M.FinRank X :=
  by rw [FinRank, ← lt_top_iff_ne_top]

lemma FinRank.ne (h : M.FinRank X) : M.er X ≠ ⊤ :=
  er_ne_top_iff.2 h

lemma FinRank.lt (h : M.FinRank X) : M.er X < ⊤ :=
  h

lemma er_eq_top_iff : M.er X = ⊤ ↔ ¬M.FinRank X := by rw [← er_ne_top_iff, not_ne_iff]

@[simp] lemma FinRank_inter_ground_iff : M.FinRank (X ∩ M.E) ↔ M.FinRank X := by
  rw [FinRank, er_inter_ground_eq, FinRank]

lemma FinRank.to_inter_ground (h : M.FinRank X) : M.FinRank (X ∩ M.E) :=
  FinRank_inter_ground_iff.2 h

lemma FinRank.finite_of_basis' (h : M.FinRank X) (hI : M.Basis' I X) : I.Finite := by
  rwa [← encard_lt_top_iff, hI.encard]

lemma FinRank.finite_of_basis (h : M.FinRank X) (hI : M.Basis I X) : I.Finite := by
  rwa [← encard_lt_top_iff, hI.encard]

lemma Basis'.finite_of_finRank (hI : M.Basis' I X) (h : M.FinRank X) : I.Finite :=
  h.finite_of_basis' hI

lemma Basis.finite_of_finRank (hI : M.Basis I X) (h : M.FinRank X) : I.Finite :=
  h.finite_of_basis hI

lemma finRank_iff' : M.FinRank X ↔ ∃ I, M.Basis' I X ∧ I.Finite :=
  ⟨fun h ↦ (M.exists_basis' X).elim (fun I hI ↦ ⟨I, hI, h.finite_of_basis' hI⟩),
    fun ⟨I, hI, hIfin⟩ ↦ by rwa [← er_lt_top_iff, hI.er_eq_encard, encard_lt_top_iff]⟩

lemma finRank_iff (hX : X ⊆ M.E := by aesop_mat) : M.FinRank X ↔ ∃ I, M.Basis I X ∧ I.Finite := by
  simp_rw [finRank_iff', M.basis'_iff_basis hX]

@[simp] lemma finRank_restrict_univ_iff : (M ↾ univ).FinRank X ↔ M.FinRank X := by
  rw [FinRank, restrict_univ_er_eq, FinRank]

lemma FinRank.exists_finite_basis' (h : M.FinRank X) : ∃ I, M.Basis' I X ∧ I.Finite :=
  finRank_iff'.1 h

lemma FinRank.exists_finite_basis (h : M.FinRank X) (hX : X ⊆ M.E := by aesop_mat) :
    ∃ I, M.Basis I X ∧ I.Finite :=
  (finRank_iff hX).1 h

lemma Basis'.finRank_of_finite (hIX : M.Basis' I X) (h : I.Finite) : M.FinRank X := by
  rwa [← er_ne_top_iff, ← hIX.encard, encard_ne_top_iff]

lemma Basis'.finRank_iff_finite (hIX : M.Basis' I X) : M.FinRank X ↔ I.Finite :=
  ⟨hIX.finite_of_finRank, hIX.finRank_of_finite⟩

lemma Basis.FinRank_of_finite (hIX : M.Basis I X) (h : I.Finite) : M.FinRank X := by
  rwa [← er_ne_top_iff, ← hIX.encard, encard_ne_top_iff]

lemma Basis.finRank_iff_finite (hIX : M.Basis I X) : M.FinRank X ↔ I.Finite :=
  ⟨hIX.finite_of_finRank, hIX.FinRank_of_finite⟩

lemma Indep.finRank_iff_finite (hI : M.Indep I) : M.FinRank I ↔ I.Finite :=
  hI.basis_self.finRank_iff_finite

lemma Indep.finite_of_finRank (hI : M.Indep I) (hfin : M.FinRank I) : I.Finite :=
  hI.basis_self.finite_of_finRank hfin

lemma FinRank_of_finite (M : Matroid α) (hX : X.Finite) : M.FinRank X :=
  (M.er_le_encard X).trans_lt (encard_lt_top_iff.mpr hX)

lemma Indep.subset_finite_basis'_of_subset_of_finRank (hI : M.Indep I) (hIX : I ⊆ X)
    (hX : M.FinRank X) : ∃ J, M.Basis' J X ∧ I ⊆ J ∧ J.Finite :=
  (hI.subset_basis'_of_subset hIX).imp fun _ hJ => ⟨hJ.1, hJ.2, hJ.1.finite_of_finRank hX⟩

lemma Indep.subset_finite_basis_of_subset_of_finRank (hI : M.Indep I) (hIX : I ⊆ X)
    (hX : M.FinRank X) (hXE : X ⊆ M.E := by aesop_mat) : ∃ J, M.Basis J X ∧ I ⊆ J ∧ J.Finite :=
  (hI.subset_basis_of_subset hIX).imp fun _ hJ => ⟨hJ.1, hJ.2, hJ.1.finite_of_finRank hX⟩

lemma finRank_singleton (M : Matroid α) (e : α) : M.FinRank {e} :=
  M.FinRank_of_finite (finite_singleton e)

@[simp] lemma finRank_empty (M : Matroid α) : M.FinRank ∅ :=
  M.FinRank_of_finite finite_empty

lemma FinRank.subset (h : M.FinRank Y) (hXY : X ⊆ Y) : M.FinRank X :=
  (M.er_mono hXY).trans_lt h

lemma not_finRank_superset (h : ¬M.FinRank X) (hXY : X ⊆ Y) : ¬M.FinRank Y :=
  fun h' ↦ h (h'.subset hXY)

lemma not_finRank_of_er_ge (h : ¬M.FinRank X) (hXY : M.er X ≤ M.er Y) : ¬M.FinRank Y :=
  fun h' ↦ h (hXY.trans_lt h')

lemma FinRank.finite_of_indep_subset (hX : M.FinRank X) (hI : M.Indep I) (hIX : I ⊆ X) : I.Finite :=
  hI.finite_of_finRank (hX.to_inter_ground.subset (subset_inter hIX hI.subset_ground))

@[simp] lemma FinRank_ground_iff_finiteRk : M.FinRank M.E ↔ M.FiniteRk := by
  obtain ⟨B, hB⟩ := M.exists_base
  use fun h => ⟨⟨B, hB, h.finite_of_indep_subset hB.indep hB.subset_ground⟩⟩
  simp_rw [finRank_iff rfl.subset, basis_ground_iff]
  exact fun ⟨h⟩ ↦ h

lemma FinRank_ground (M : Matroid α) [FiniteRk M] : M.FinRank M.E := by
  rwa [FinRank_ground_iff_finiteRk]

lemma erk_lt_top (M : Matroid α) [FiniteRk M] : M.erk < ⊤ := by
  rw [erk_eq_er_ground, er_lt_top_iff]; exact M.FinRank_ground

lemma Indep.finite_of_subset_finRank (hI : M.Indep I) (hIX : I ⊆ X) (hX : M.FinRank X) : I.Finite :=
  hX.finite_of_indep_subset hI hIX

lemma FinRank.indep_of_encard_le_er (hX : M.FinRank I) (h : encard I ≤ M.er I) : M.Indep I := by
  rw [indep_iff_er_eq_encard_of_finite _]
  · exact (M.er_le_encard I).antisymm h
  simpa using h.trans_lt hX.lt

lemma FinRank.to_cl (h : M.FinRank X) : M.FinRank (M.closure X) := by
  rwa [← er_lt_top_iff, er_closure_eq]

@[simp] lemma FinRank_closure_iff : M.FinRank (M.closure X) ↔ M.FinRank X := by
  rw [← er_ne_top_iff, er_closure_eq, er_ne_top_iff]

lemma FinRank.union (hX : M.FinRank X) (hY : M.FinRank Y) : M.FinRank (X ∪ Y) := by
  rw [← er_lt_top_iff] at *
  apply (M.er_union_le_er_add_er X Y).trans_lt
  rw [WithTop.add_lt_top]
  exact ⟨hX, hY⟩

lemma FinRank.FinRank_union_iff (hX : M.FinRank X) : M.FinRank (X ∪ Y) ↔ M.FinRank Y :=
  ⟨fun h ↦ h.subset subset_union_right, fun h ↦ hX.union h⟩

lemma FinRank.FinRank_diff_iff (hX : M.FinRank X) : M.FinRank (Y \ X) ↔ M.FinRank Y := by
  rw [← hX.FinRank_union_iff, union_diff_self, hX.FinRank_union_iff]

lemma FinRank.inter_right (hX : M.FinRank X) (Y : Set α) : M.FinRank (X ∩ Y) :=
  hX.subset inter_subset_left

lemma FinRank.inter_left (hX : M.FinRank X) (Y : Set α) : M.FinRank (Y ∩ X) :=
  hX.subset inter_subset_right

lemma FinRank.diff (hX : M.FinRank X) (D : Set α) : M.FinRank (X \ D) :=
  hX.subset diff_subset

lemma FinRank.insert (hX : M.FinRank X) (e : α) : M.FinRank (insert e X) := by
  rw [← union_singleton]; exact hX.union (M.finRank_singleton e)

@[simp] lemma FinRank_insert_iff : M.FinRank (insert e X) ↔ M.FinRank X := by
  rw [← singleton_union, (M.finRank_singleton e).FinRank_union_iff]

@[simp] lemma FinRank_diff_singleton_iff : M.FinRank (X \ {e}) ↔ M.FinRank X := by
  rw [(M.finRank_singleton e).FinRank_diff_iff]

lemma to_finRank (M : Matroid α) [FiniteRk M] (X : Set α) : M.FinRank X := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  rw [← er_lt_top_iff, hI.er_eq_encard, encard_lt_top_iff]
  exact hI.indep.finite_of_subset_finRank hI.indep.subset_ground M.FinRank_ground

lemma FinRank.closure_eq_closure_of_subset_of_er_ge_er (hX : M.FinRank X) (hXY : X ⊆ Y)
    (hr : M.er Y ≤ M.er X) (hY : Y ⊆ M.E := by aesop_mat) : M.closure X = M.closure Y := by
  obtain ⟨I, hI⟩ := M.exists_basis X
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_basis_of_subset (hI.subset.trans hXY)
  rw [hI.er_eq_encard, hJ.er_eq_encard] at hr
  obtain rfl : I = J := (hI.finite_of_finRank hX).eq_of_subset_of_encard_le' hIJ hr
  rw [hI.closure_eq_closure, hJ.closure_eq_closure]

lemma er_union_eq_of_subset_of_er_le_er (Z : Set α) (hXY : X ⊆ Y) (hr : M.er Y ≤ M.er X) :
    M.er (X ∪ Z) = M.er (Y ∪ Z) := by
  simp_rw [← M.restrict_univ_er_eq] at hr ⊢
  set M' := M ↾ univ
  by_cases hX' : M'.FinRank X
  · rw [← er_union_closure_left_eq, hX'.closure_eq_closure_of_subset_of_er_ge_er hXY hr,
      er_union_closure_left_eq]
  rw [er_eq_top_iff.2, er_eq_top_iff.2]
  · exact not_finRank_of_er_ge hX' (M'.er_mono (subset_union_of_subset_left hXY _))
  exact not_finRank_of_er_ge hX' (M'.er_mono subset_union_left)

lemma er_union_eq_of_subsets_of_ers_le (hX : X ⊆ X') (hY : Y ⊆ Y') (hXX' : M.er X' ≤ M.er X)
    (hYY' : M.er Y' ≤ M.er Y) : M.er (X ∪ Y) = M.er (X' ∪ Y') := by
  rw [er_union_eq_of_subset_of_er_le_er _ hX hXX', union_comm,
    er_union_eq_of_subset_of_er_le_er _ hY hYY', union_comm]

lemma FinRank.basis_of_subset_of_subset_closure_of_encard_le (hX : M.FinRank X)
    (hIX : I ⊆ X) (hXI : X ⊆ M.closure I) (hI : I.encard ≤ M.er X) (hIE : I ⊆ M.E := by aesop_mat) :
    M.Basis I X := by
  obtain ⟨J, hJ⟩ := M.exists_basis I
  have hJX := hJ.basis_closure_right.basis_subset (hJ.subset.trans hIX) hXI
  rwa [← (hJX.finite_of_finRank hX).eq_of_subset_of_encard_le' hJ.subset (hJX.encard ▸ hI)]

lemma FinRank.iUnion [Finite ι] {Xs : ι → Set α}
    (h : ∀ i, M.FinRank (Xs i)) : M.FinRank (⋃ i, Xs i) := by
  simp_rw [← M.finRank_restrict_univ_iff] at h ⊢
  set M' := M ↾ univ
  choose Is hIs using fun i ↦ M'.exists_basis (Xs i)
  have hfin : (⋃ i, Is i).Finite := finite_iUnion <| fun i ↦ (h i).finite_of_basis (hIs i)
  rw [← FinRank_closure_iff]
  have hcl := (M'.FinRank_of_finite hfin).to_cl
  rw [← M'.closure_iUnion_closure_eq_closure_iUnion]
  simp_rw [(hIs _).closure_eq_closure, M'.closure_iUnion_closure_eq_closure_iUnion]
  assumption

end FinRank

section Rank

/-- The rank function, with a junk value of zero for infinite-rank sets.
Intended to be used in a `FiniteRk` matroid; otherwise `er` is better.-/
noncomputable def r (M : Matroid α) (X : Set α) : ℕ :=
  ENat.toNat (M.er X)

/-- The rank of the ground set of a matroid -/
@[reducible] noncomputable def rk (M : Matroid α) : ℕ :=
  ENat.toNat M.erk

lemma rk_def (M : Matroid α) : M.rk = M.r M.E := by
  rw [rk,r,er,restrict_ground_eq_self]

@[simp] lemma er_toNat_eq_r (M : Matroid α) (X : Set α) : ENat.toNat (M.er X) = M.r X :=
  rfl

lemma Base.ncard (hB : M.Base B) : B.ncard = M.rk := by
  rw [rk_def, ← er_toNat_eq_r, ncard_def, hB.encard, erk_eq_er_ground]

lemma FinRank.coe_r_eq (hX : M.FinRank X) : (M.r X : ℕ∞) = M.er X := by
  rw [r, coe_toNat (by rwa [er_ne_top_iff])]

lemma coe_r_eq_er_of_finite (M : Matroid α) (hX : X.Finite) : (M.r X : ℕ∞) = M.er X :=
  (M.FinRank_of_finite hX).coe_r_eq

@[simp] lemma coe_r_eq (M : Matroid α) [FiniteRk M] (X : Set α) : (M.r X : ℕ∞) = M.er X :=
  (M.to_finRank X).coe_r_eq

@[simp] lemma coe_rk_eq (M : Matroid α) [FiniteRk M] : (M.rk : ℕ∞) = M.erk := by
  rw [erk_eq_er_ground, rk_def, coe_r_eq]

lemma r_eq_of_er_eq (h : M.er X = M.er Y) : M.r X = M.r Y := by
  rw [r, r, h]

lemma FinRank.er_eq_er_iff (hX : M.FinRank X) (hY : M.FinRank Y) :
    M.er X = M.er Y ↔ M.r X = M.r Y := by
  rw [← hX.coe_r_eq, ← hY.coe_r_eq, Nat.cast_inj]

lemma FinRank.er_le_er_iff (hX : M.FinRank X) (hY : M.FinRank Y) :
    M.er X ≤ M.er Y ↔ M.r X ≤ M.r Y := by
  rw [← hX.coe_r_eq, ← hY.coe_r_eq, Nat.cast_le]

@[simp] lemma er_eq_er_iff [FiniteRk M] : M.er X = M.er Y ↔ M.r X = M.r Y :=
  (M.to_finRank X).er_eq_er_iff (M.to_finRank Y)

@[simp] lemma er_le_er_iff [FiniteRk M] : M.er X ≤ M.er Y ↔ M.r X ≤ M.r Y := by
  rw [← coe_r_eq, ← coe_r_eq, Nat.cast_le]

@[simp] lemma er_eq_coe_iff [FiniteRk M] {n : ℕ} : M.er X = n ↔ M.r X = n := by
  rw [← coe_r_eq, Nat.cast_inj]

@[simp] lemma er_le_coe_iff [FiniteRk M] {n : ℕ} : M.er X ≤ n ↔ M.r X ≤ n := by
  rw [← coe_r_eq, Nat.cast_le]

@[simp] lemma coe_le_er_iff [FiniteRk M] {n : ℕ} : (n : ℕ∞) ≤ M.er X ↔ n ≤ M.r X := by
  rw [← coe_r_eq, Nat.cast_le]

lemma FinRank.r_le_r_of_er_le_er (hY : M.FinRank Y) (hle : M.er X ≤ M.er Y) : M.r X ≤ M.r Y := by
  rwa [← FinRank.er_le_er_iff _ hY]; exact hle.trans_lt hY.lt

lemma r_eq_r_inter_ground (M : Matroid α) (X : Set α) : M.r X = M.r (X ∩ M.E) := by
  rw [← er_toNat_eq_r, ← er_inter_ground_eq, er_toNat_eq_r]

lemma le_r_iff [FiniteRk M] {n : ℕ} : n ≤ M.r X ↔ ∃ I, I ⊆ X ∧ M.Indep I ∧ I.ncard = n := by
  simp_rw [← coe_le_er_iff, le_er_iff,]
  refine ⟨fun ⟨I, hIX, hI, hc⟩ ↦ ⟨I, hIX, hI, by rw [ncard_def, hc, toNat_coe]⟩,
    fun ⟨I, hIX, hI, hc⟩ ↦ ⟨I, hIX, hI, ?_⟩⟩
  rw [hI.finite.encard_eq_coe, ← hc]; rfl

lemma r_le_iff [FiniteRk M] {n : ℕ} : M.r X ≤ n ↔ ∀ {I}, I ⊆ X → M.Indep I → I.ncard ≤ n := by
  simp_rw [← er_le_coe_iff, er_le_iff, encard_le_coe_iff]
  refine ⟨fun h I hIX hI ↦ ?_, fun h I hIX hI ↦ ⟨hI.finite, ⟨_, hI.finite.encard_eq_coe, h hIX hI⟩⟩⟩
  obtain ⟨-, m, hm, hmn⟩ := h hIX hI
  rwa [ncard_def, hm, toNat_coe]

lemma r_mono (M : Matroid α) [FiniteRk M] : Monotone M.r := by
  rintro X Y (hXY : X ⊆ Y);
  rw [← er_le_er_iff]
  exact M.er_mono hXY

lemma r_le_of_subset (M : Matroid α) [FiniteRk M] (hXY : X ⊆ Y) : M.r X ≤ M.r Y :=
  M.r_mono hXY

@[simp] lemma r_empty (M : Matroid α) : M.r ∅ = 0 := by
  rw [r, er_empty]; rfl

@[simp] lemma r_closure_eq (M : Matroid α) : M.r (M.closure X) = M.r X := by
  rw [r, er_closure_eq, r]

lemma r_le_rk (M : Matroid α) [FiniteRk M] (X : Set α) : M.r X ≤ M.rk := by
  rw [r_eq_r_inter_ground, rk_def]; exact M.r_mono inter_subset_right

lemma Indep.r (hI : M.Indep I) : M.r I = I.ncard := by
  rw [← er_toNat_eq_r, hI.er, ncard_def]

lemma r_le_card (M : Matroid α) [Matroid.Finite M] (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    M.r X ≤ X.ncard :=
  r_le_iff.2 <| fun {I} hI _ ↦ (ncard_le_ncard hI (M.set_finite X))

lemma Indep.card_le_r_of_subset [FiniteRk M] (hI : M.Indep I) (h : I ⊆ X) : I.ncard ≤ M.r X := by
  rw [← hI.r]; exact M.r_mono h

lemma Indep.card_le_rk [FiniteRk M] (hI : M.Indep I) : I.ncard ≤ M.rk :=
  hI.r.symm.trans_le (M.r_le_rk I)

lemma Basis'.card (h : M.Basis' I X) : I.ncard = M.r X := by
  rw [ncard_def, h.encard, ← er_toNat_eq_r]

lemma Basis'.r (h : M.Basis' I X) : M.r I = M.r X := by
  rw [← h.card, h.indep.r]

lemma Basis.card (h : M.Basis I X) : I.ncard = M.r X :=
  h.basis'.card

lemma Basis.r (h : M.Basis I X) : M.r I = M.r X :=
  h.basis'.r

lemma r_eq_zero_iff [FiniteRk M] (hX : X ⊆ M.E) : M.r X = 0 ↔ X ⊆ M.closure ∅ := by
  rw [← er_eq_coe_iff, coe_zero, er_eq_zero_iff]

@[simp] lemma r_loops (M : Matroid α) : M.r (M.closure ∅) = 0 := by
  simp [r]

lemma Nonloop.r_eq (he : M.Nonloop e) : M.r {e} = 1 := by
  rw [r, he.er_eq]; rfl

lemma Loop.r_eq (he : M.Loop e) : M.r {e} = 0 := by
  rw [r, he.er_eq]; rfl

lemma FinRank.submod (hX : M.FinRank X) (hY : M.FinRank Y) :
    M.r (X ∩ Y) + M.r (X ∪ Y) ≤ M.r X + M.r Y := by
  obtain ⟨c, h_eq⟩ := le_iff_exists_add.1 <| M.er_inter_add_er_union_le_er_add_er X Y
  obtain (rfl | hc) := eq_or_ne c ⊤
  · rw [add_top, WithTop.add_eq_top] at h_eq
    simp [hX.ne, hY.ne] at h_eq
  have hi : M.FinRank (X ∩ Y) := hX.subset inter_subset_left
  have hu : M.FinRank (X ∪ Y) := hX.union hY
  rw [← ge_iff_le, r,r, ge_iff_le, ← toNat_add hX.ne hY.ne, h_eq, toNat_add _ hc,
    toNat_add hi.ne hu.ne, ← r, ← r]
  · apply Nat.le_add_right
  rw [Ne, WithTop.add_eq_top, not_or]
  exact ⟨hi.ne, hu.ne⟩

lemma r_submod (M : Matroid α) [FiniteRk M] (X Y : Set α) :
    M.r (X ∩ Y) + M.r (X ∪ Y) ≤ M.r X + M.r Y :=
  FinRank.submod (M.to_finRank X) (M.to_finRank Y)

lemma Indep.exists_insert_of_ncard_lt [FiniteRk M] {J : Set α} (hI : M.Indep I) (hJ : M.Indep J)
    (hcard : I.ncard < J.ncard) : ∃ e ∈ J \ I, M.Indep (insert e I) := by
  apply hI.exists_insert_of_encard_lt hJ
  rw [← hJ.finite.cast_ncard_eq, ← hI.finite.cast_ncard_eq]
  exact Nat.cast_lt.mpr hcard

@[simp] lemma rk_map {β : Type*} (M : Matroid α) (f : α → β) (hf : InjOn f M.E) :
    (M.map f hf).rk = M.rk := by
  simp [rk]

end Rank

section Constructions

variable {E : Set α}

@[simp] lemma loopyOn_er_eq (E X : Set α) : (loopyOn E).er X = 0 := by
  obtain ⟨I, hI⟩ := (loopyOn E).exists_basis' X
  rw [hI.er_eq_encard, loopyOn_indep_iff.1 hI.indep, encard_empty]

@[simp] lemma loopyOn_erk_eq (E : Set α) : (loopyOn E).erk = 0 := by
  rw [erk_eq_er_ground, loopyOn_er_eq]

@[simp] lemma loopyOn_r_eq (E X : Set α) : (loopyOn E).r X = 0 := by
  rw [← er_toNat_eq_r, loopyOn_er_eq]; rfl

@[simp] lemma erk_eq_zero_iff : M.erk = 0 ↔ M = loopyOn M.E := by
  refine ⟨fun h ↦ closure_empty_eq_ground_iff.1 ?_, fun h ↦ by rw [h, loopyOn_erk_eq]⟩
  obtain ⟨B, hB⟩ := M.exists_base
  rw [← hB.encard, encard_eq_zero] at h
  rw [← h, hB.closure_eq]

@[simp] lemma erk_loopyOn_eq_zero (α : Type*) : (emptyOn α).erk = 0 := by
  rw [erk_eq_zero_iff, emptyOn_ground, loopyOn_empty]

lemma eq_loopyOn_iff_cl : M = loopyOn E ↔ M.closure ∅ = E ∧ M.E = E :=
  ⟨fun h ↦ by rw [h]; simp, fun ⟨h,h'⟩ ↦ by rw [← h', ← closure_empty_eq_ground_iff, h, h']⟩

lemma eq_loopyOn_iff_erk : M = loopyOn E ↔ M.erk = 0 ∧ M.E = E :=
  ⟨fun h ↦ by rw [h]; simp, fun ⟨h,h'⟩ ↦ by rw [← h', ← erk_eq_zero_iff, h]⟩

@[simp] lemma freeOn_erk_eq (E : Set α) : (freeOn E).erk = E.encard := by
  rw [erk_eq_er_ground, freeOn_ground, (freeOn_indep_iff.2 rfl.subset).er]

lemma freeOn_er_eq (hXE : X ⊆ E) : (freeOn E).er X = X.encard := by
  obtain ⟨I, hI⟩ := (freeOn E).exists_basis X
  rw [hI.er_eq_encard, (freeOn_indep hXE).eq_of_basis hI]

lemma freeOn_r_eq (hXE : X ⊆ E) : (freeOn E).r X = X.ncard := by
  rw [← er_toNat_eq_r, freeOn_er_eq hXE, ncard_def]

-- lemma IsIso.erk_eq_erk {α β : Type*} {M : Matroid α} {N : Matroid β} (h : M ≂ N) :
--     M.erk = N.erk := by
--   obtain (⟨rfl, rfl⟩ | ⟨⟨e⟩⟩) := h; simp; exact e.erk_eq_erk

end Constructions
end Matroid
