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

@[simp] lemma er_inter_ground_eq (M : Matroid α) (X : Set α) : M.er (X ∩ M.E) = M.er X := by
  obtain ⟨I, hI⟩ := M.exists_basis' X; rw [← hI.basis_inter_ground.encard, ← hI.encard]

-- lemma Iso.er_image_eq {α β : Type*} {M : Matroid α} {N : Matroid β} (e : Iso M N) (X : Set α)
--     (hX : X ⊆ M.E := by aesop_mat) : N.er (e '' X) = M.er X := by
--   obtain ⟨I,hI⟩ := M.exists_basis X
--   rw [hI.er_eq_encard, (e.on_basis hI).er_eq_encard,
--     (e.injOn_ground.mono hI.indep.subset_ground).encard_image]

@[simp] lemma er_univ_eq (M : Matroid α) : M.er univ = M.erk := by
  rw [← er_inter_ground_eq, univ_inter, erk_eq_er_ground]

-- lemma Iso.erk_eq_erk {α β : Type*} {M : Matroid α} {N : Matroid β} (e : Iso M N) :
--     M.erk = N.erk := by
--   rw [erk_eq_er_ground, ← e.er_image_eq M.E, e.image_ground, erk_eq_er_ground]

@[simp] lemma er_empty (M : Matroid α) : M.er ∅ = 0 := by
  rw [← M.empty_indep.basis_self.encard, encard_empty]

@[simp] lemma er_cl_eq (M : Matroid α) (X : Set α) : M.er (M.cl X) = M.er X := by
  rw [← cl_inter_ground, ← M.er_inter_ground_eq X]
  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E)
  rw [← hI.er, ← hI.cl_eq_cl, hI.indep.basis_cl.er]

@[simp] lemma er_union_cl_right_eq (M : Matroid α) (X Y : Set α) :
    M.er (X ∪ M.cl Y) = M.er (X ∪ Y) :=
  by rw [← er_cl_eq, cl_union_cl_right_eq, er_cl_eq]

@[simp] lemma er_union_cl_left_eq (M : Matroid α) (X Y : Set α) :
    M.er (M.cl X ∪ Y) = M.er (X ∪ Y) := by
  rw [← er_cl_eq, cl_union_cl_left_eq, er_cl_eq]

@[simp] lemma er_insert_cl_eq (M : Matroid α) (e : α) (X : Set α) :
    M.er (insert e (M.cl X)) = M.er (insert e X) := by
  rw [← union_singleton, er_union_cl_left_eq, union_singleton]

@[simp] lemma restrict_er_eq' (M : Matroid α) (R X : Set α) : (M ↾ R).er X = M.er (X ∩ R) := by
  obtain ⟨I, hI⟩ := (M ↾ R).exists_basis' X
  rw [hI.er_eq_encard]
  rw [basis'_iff_basis_inter_ground, basis_restrict_iff', restrict_ground_eq] at hI
  rw [← er_inter_ground_eq, ← hI.1.er_eq_encard]

@[simp] lemma restrict_er_eq (M : Matroid α) (h : X ⊆ R) : (M ↾ R).er X = M.er X := by
  rw [restrict_er_eq', inter_eq_self_of_subset_left h]

lemma er_lt_top_of_finite (M : Matroid α) (hX : X.Finite) : M.er X < ⊤ := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  rw [hI.er_eq_encard, encard_lt_top_iff]
  exact hX.subset hI.subset

lemma Basis'.er_eq_er_union (hIX : M.Basis' I X) (Y : Set α) : M.er (I ∪ Y) = M.er (X ∪ Y) := by
  rw [← er_union_cl_left_eq, hIX.cl_eq_cl, er_union_cl_left_eq]

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
  apply hI.basis_of_subset_of_subset_cl (subset_inter hIX hI.subset_ground)
  obtain rfl := hIfin.eq_of_subset_of_encard_le' hIJ
    (by rw [hcard, ← hJ.er_eq_encard, er_inter_ground_eq ])
  exact hJ.subset_cl

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

lemma er_insert_eq_add_one (M : Matroid α) (X : Set α) (he : e ∈ M.E \ M.cl X) :
    M.er (insert e X) = M.er X + 1 := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  rw [← hI.cl_eq_cl] at he
  rw [← er_cl_eq, ← cl_insert_cl_eq_cl_insert, ← hI.cl_eq_cl, hI.er_eq_encard,
    cl_insert_cl_eq_cl_insert, er_cl_eq, Indep.er, encard_insert_of_not_mem]
  · exact fun heI ↦ he.2 (M.subset_cl I hI.indep.subset_ground heI)
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

lemma spanning_iff_er' [FiniteRk M] : M.Spanning X ↔ M.erk ≤ M.er X ∧ X ⊆ M.E := by
  refine' ⟨fun h ↦ _, fun ⟨hr, hX⟩ ↦ _⟩
  · rw [erk_eq_er_ground, ← er_cl_eq _ X, h.cl_eq]; exact ⟨rfl.le, h.subset_ground⟩
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
  rw [← er_cl_eq, he.cl, er_cl_eq, er_empty]

lemma Nonloop.er_eq (he : M.Nonloop e) : M.er {e} = 1 := by
  rw [← he.indep.basis_self.encard, encard_singleton]

lemma er_singleton_eq [Loopless M] (he : e ∈ M.E := by aesop_mat) :
    M.er {e} = 1 :=
  (M.toNonloop he).er_eq

lemma LoopEquiv.er_eq_er (h : M.LoopEquiv X Y) : M.er X = M.er Y := by
  rw [← M.er_cl_eq, h.cl_eq_cl, M.er_cl_eq]

lemma er_eq_zero_iff (hX : X ⊆ M.E := by aesop_mat) :
    M.er X = 0 ↔ X ⊆ M.cl ∅ := by
  obtain ⟨I, hI⟩ := M.exists_basis X
  rw [← hI.encard, encard_eq_zero]
  exact ⟨by rintro rfl; exact hI.subset_cl, fun h ↦ eq_empty_of_forall_not_mem
    fun x hx ↦ (hI.indep.nonloop_of_mem hx).not_loop (h (hI.subset hx))⟩

lemma er_eq_zero_iff' : M.er X = 0 ↔ X ∩ M.E ⊆ M.cl ∅ := by
  rw [← er_inter_ground_eq, er_eq_zero_iff]

@[simp] lemma er_loops (M : Matroid α) : M.er (M.cl ∅) = 0 := by
  rw [er_eq_zero_iff]

lemma er_eq_one_iff (hX : X ⊆ M.E := by aesop_mat) :
    M.er X = 1 ↔ ∃ e ∈ X, M.Nonloop e ∧ X ⊆ M.cl {e} := by
  refine ⟨?_, fun ⟨e, heX, he, hXe⟩ ↦ ?_⟩
  · obtain ⟨I, hI⟩ := M.exists_basis X
    rw [hI.er_eq_encard, encard_eq_one]
    rintro ⟨e, rfl⟩
    exact ⟨e, singleton_subset_iff.1 hI.subset, indep_singleton.1 hI.indep, hI.subset_cl⟩
  rw [← he.er_eq]
  exact ((M.er_mono hXe).trans (M.er_cl_eq _).le).antisymm (M.er_mono (singleton_subset_iff.2 heX))

lemma er_le_one_iff [M.Nonempty] (hX : X ⊆ M.E := by aesop_mat) :
    M.er X ≤ 1 ↔ ∃ e ∈ M.E, X ⊆ M.cl {e} := by
  refine' ⟨fun h ↦ _, fun ⟨e, _, he⟩ ↦ _⟩
  · obtain ⟨I, hI⟩ := M.exists_basis X
    rw [hI.er_eq_encard, encard_le_one_iff_eq] at h
    obtain (rfl | ⟨e, rfl⟩) := h
    · exact ⟨M.ground_nonempty.some, M.ground_nonempty.some_mem,
        hI.subset_cl.trans ((M.cl_subset_cl (empty_subset _)))⟩
    exact ⟨e, hI.indep.subset_ground rfl,  hI.subset_cl⟩
  refine (M.er_mono he).trans ?_
  rw [er_cl_eq, ← encard_singleton e]
  exact M.er_le_encard {e}

lemma Base.encard_compl_eq (hB : M.Base B) : (M.E \ B).encard = M✶.erk :=
  (hB.compl_base_dual).encard

end Basic



section rFin

def rFin (M : Matroid α) (X : Set α) :=
  M.er X < ⊤

@[simp] lemma er_lt_top_iff : M.er X < ⊤ ↔ M.rFin X := Iff.rfl

@[simp] lemma er_ne_top_iff : M.er X ≠ ⊤ ↔ M.rFin X :=
  by rw [rFin, ← lt_top_iff_ne_top]

lemma rFin.ne (h : M.rFin X) : M.er X ≠ ⊤ :=
  er_ne_top_iff.2 h

lemma rFin.lt (h : M.rFin X) : M.er X < ⊤ :=
  h

lemma er_eq_top_iff : M.er X = ⊤ ↔ ¬M.rFin X := by rw [← er_ne_top_iff, not_ne_iff]

@[simp] lemma rFin_inter_ground_iff : M.rFin (X ∩ M.E) ↔ M.rFin X := by
  rw [rFin, er_inter_ground_eq, rFin]

lemma rFin.to_inter_ground (h : M.rFin X) : M.rFin (X ∩ M.E) :=
  rFin_inter_ground_iff.2 h

lemma rFin.finite_of_basis' (h : M.rFin X) (hI : M.Basis' I X) : I.Finite := by
  rwa [← encard_lt_top_iff, hI.encard]

lemma rFin.finite_of_basis (h : M.rFin X) (hI : M.Basis I X) : I.Finite := by
  rwa [← encard_lt_top_iff, hI.encard]

lemma Basis'.finite_of_rFin (hI : M.Basis' I X) (h : M.rFin X) : I.Finite :=
  h.finite_of_basis' hI

lemma Basis.finite_of_rFin (hI : M.Basis I X) (h : M.rFin X) : I.Finite :=
  h.finite_of_basis hI

lemma rFin_iff' : M.rFin X ↔ ∃ I, M.Basis' I X ∧ I.Finite :=
  ⟨fun h ↦ (M.exists_basis' X).elim (fun I hI ↦ ⟨I, hI, h.finite_of_basis' hI⟩),
    fun ⟨I, hI, hIfin⟩ ↦ by rwa [← er_lt_top_iff, hI.er_eq_encard, encard_lt_top_iff]⟩

lemma rFin_iff (hX : X ⊆ M.E := by aesop_mat) : M.rFin X ↔ ∃ I, M.Basis I X ∧ I.Finite := by
  simp_rw [rFin_iff', M.basis'_iff_basis hX]

lemma rFin.exists_finite_basis' (h : M.rFin X) : ∃ I, M.Basis' I X ∧ I.Finite :=
  rFin_iff'.1 h

lemma rFin.exists_finite_basis (h : M.rFin X) (hX : X ⊆ M.E := by aesop_mat) :
    ∃ I, M.Basis I X ∧ I.Finite :=
  (rFin_iff hX).1 h

lemma Basis'.rFin_of_finite (hIX : M.Basis' I X) (h : I.Finite) : M.rFin X := by
  rwa [← er_ne_top_iff, ← hIX.encard, encard_ne_top_iff]

lemma Basis'.rFin_iff_finite (hIX : M.Basis' I X) : M.rFin X ↔ I.Finite :=
  ⟨hIX.finite_of_rFin, hIX.rFin_of_finite⟩

lemma Basis.rFin_of_finite (hIX : M.Basis I X) (h : I.Finite) : M.rFin X := by
  rwa [← er_ne_top_iff, ← hIX.encard, encard_ne_top_iff]

lemma Basis.rFin_iff_finite (hIX : M.Basis I X) : M.rFin X ↔ I.Finite :=
  ⟨hIX.finite_of_rFin, hIX.rFin_of_finite⟩

lemma Indep.rFin_iff_finite (hI : M.Indep I) : M.rFin I ↔ I.Finite :=
  hI.basis_self.rFin_iff_finite

lemma Indep.finite_of_rFin (hI : M.Indep I) (hfin : M.rFin I) : I.Finite :=
  hI.basis_self.finite_of_rFin hfin

lemma rFin_of_finite (M : Matroid α) (hX : X.Finite) : M.rFin X :=
  (M.er_le_encard X).trans_lt (encard_lt_top_iff.mpr hX)

lemma Indep.subset_finite_basis'_of_subset_of_rFin (hI : M.Indep I) (hIX : I ⊆ X)
    (hX : M.rFin X) : ∃ J, M.Basis' J X ∧ I ⊆ J ∧ J.Finite :=
  (hI.subset_basis'_of_subset hIX).imp fun _ hJ => ⟨hJ.1, hJ.2, hJ.1.finite_of_rFin hX⟩

lemma Indep.subset_finite_basis_of_subset_of_rFin (hI : M.Indep I) (hIX : I ⊆ X)
    (hX : M.rFin X) (hXE : X ⊆ M.E := by aesop_mat) : ∃ J, M.Basis J X ∧ I ⊆ J ∧ J.Finite :=
  (hI.subset_basis_of_subset hIX).imp fun _ hJ => ⟨hJ.1, hJ.2, hJ.1.finite_of_rFin hX⟩

lemma rFin_singleton (M : Matroid α) (e : α) : M.rFin {e} :=
  M.rFin_of_finite (finite_singleton e)

@[simp] lemma rFin_empty (M : Matroid α) : M.rFin ∅ :=
  M.rFin_of_finite finite_empty

lemma rFin.subset (h : M.rFin Y) (hXY : X ⊆ Y) : M.rFin X :=
  (M.er_mono hXY).trans_lt h

lemma not_rFin_superset (h : ¬M.rFin X) (hXY : X ⊆ Y) : ¬M.rFin Y :=
  fun h' ↦ h (h'.subset hXY)

lemma not_rFin_of_er_ge (h : ¬M.rFin X) (hXY : M.er X ≤ M.er Y) : ¬M.rFin Y :=
  fun h' ↦ h (hXY.trans_lt h')

lemma rFin.finite_of_indep_subset (hX : M.rFin X) (hI : M.Indep I) (hIX : I ⊆ X) : I.Finite :=
  hI.finite_of_rFin (hX.to_inter_ground.subset (subset_inter hIX hI.subset_ground))

@[simp] lemma rFin_ground_iff_finiteRk : M.rFin M.E ↔ M.FiniteRk := by
  obtain ⟨B, hB⟩ := M.exists_base
  use fun h => ⟨⟨B, hB, h.finite_of_indep_subset hB.indep hB.subset_ground⟩⟩
  simp_rw [rFin_iff (rfl.subset), basis_ground_iff]
  exact fun ⟨h⟩ ↦ h

lemma rFin_ground (M : Matroid α) [FiniteRk M] : M.rFin M.E := by
  rwa [rFin_ground_iff_finiteRk]

lemma erk_lt_top (M : Matroid α) [FiniteRk M] : M.erk < ⊤ := by
  rw [erk_eq_er_ground, er_lt_top_iff]; exact M.rFin_ground

lemma Indep.finite_of_subset_rFin (hI : M.Indep I) (hIX : I ⊆ X) (hX : M.rFin X) : I.Finite :=
  hX.finite_of_indep_subset hI hIX

lemma rFin.indep_of_encard_le_er (hX : M.rFin I) (h : encard I ≤ M.er I) : M.Indep I := by
  rw [indep_iff_er_eq_encard_of_finite _]
  · exact (M.er_le_encard I).antisymm h
  simpa using h.trans_lt hX.lt

lemma rFin.to_cl (h : M.rFin X) : M.rFin (M.cl X) := by
  rwa [← er_lt_top_iff, er_cl_eq]

@[simp] lemma rFin_cl_iff : M.rFin (M.cl X) ↔ M.rFin X := by
  rw [← er_ne_top_iff, er_cl_eq, er_ne_top_iff]

lemma rFin.union (hX : M.rFin X) (hY : M.rFin Y) : M.rFin (X ∪ Y) := by
  rw [← er_lt_top_iff] at *
  apply (M.er_union_le_er_add_er X Y).trans_lt
  rw [WithTop.add_lt_top]
  exact ⟨hX, hY⟩

lemma rFin.rFin_union_iff (hX : M.rFin X) : M.rFin (X ∪ Y) ↔ M.rFin Y :=
  ⟨fun h ↦ h.subset subset_union_right, fun h ↦ hX.union h⟩

lemma rFin.rFin_diff_iff (hX : M.rFin X) : M.rFin (Y \ X) ↔ M.rFin Y := by
  rw [← hX.rFin_union_iff, union_diff_self, hX.rFin_union_iff]

lemma rFin.inter_right (hX : M.rFin X) (Y : Set α) : M.rFin (X ∩ Y) :=
  hX.subset inter_subset_left

lemma rFin.inter_left (hX : M.rFin X) (Y : Set α) : M.rFin (Y ∩ X) :=
  hX.subset inter_subset_right

lemma rFin.diff (hX : M.rFin X) (D : Set α) : M.rFin (X \ D) :=
  hX.subset diff_subset

lemma rFin.insert (hX : M.rFin X) (e : α) : M.rFin (insert e X) := by
  rw [← union_singleton]; exact hX.union (M.rFin_singleton e)

@[simp] lemma rFin_insert_iff : M.rFin (insert e X) ↔ M.rFin X := by
  rw [← singleton_union, (M.rFin_singleton e).rFin_union_iff]

@[simp] lemma rFin_diff_singleton_iff : M.rFin (X \ {e}) ↔ M.rFin X := by
  rw [(M.rFin_singleton e).rFin_diff_iff]

lemma to_rFin (M : Matroid α) [FiniteRk M] (X : Set α) : M.rFin X := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  rw [← er_lt_top_iff, hI.er_eq_encard, encard_lt_top_iff]
  exact hI.indep.finite_of_subset_rFin hI.indep.subset_ground M.rFin_ground

lemma rFin.cl_eq_cl_of_subset_of_er_ge_er (hX : M.rFin X) (hXY : X ⊆ Y) (hr : M.er Y ≤ M.er X) :
    M.cl X = M.cl Y := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_basis'_of_subset (hI.subset.trans hXY)
  rw [hI.er_eq_encard, hJ.er_eq_encard] at hr
  rw [← cl_inter_ground, ← M.cl_inter_ground Y, ← hI.basis_inter_ground.cl_eq_cl,
    ← hJ.basis_inter_ground.cl_eq_cl, Finite.eq_of_subset_of_encard_le'
      (hI.indep.finite_of_subset_rFin hI.subset hX) hIJ hr]

lemma er_union_eq_of_subset_of_er_le_er (Z : Set α) (hXY : X ⊆ Y) (hr : M.er Y ≤ M.er X) :
    M.er (X ∪ Z) = M.er (Y ∪ Z) := by
  obtain hX' | hX' := em (M.rFin X)
  · rw [← er_union_cl_left_eq, hX'.cl_eq_cl_of_subset_of_er_ge_er hXY hr, er_union_cl_left_eq]
  rw [er_eq_top_iff.2, er_eq_top_iff.2]
  · exact not_rFin_of_er_ge hX' (M.er_mono (subset_union_of_subset_left hXY _))
  exact not_rFin_of_er_ge hX' (M.er_mono subset_union_left)

lemma er_union_eq_of_subsets_of_ers_le (hX : X ⊆ X') (hY : Y ⊆ Y') (hXX' : M.er X' ≤ M.er X)
    (hYY' : M.er Y' ≤ M.er Y) : M.er (X ∪ Y) = M.er (X' ∪ Y') := by
  rw [er_union_eq_of_subset_of_er_le_er _ hX hXX', union_comm,
    er_union_eq_of_subset_of_er_le_er _ hY hYY', union_comm]

lemma rFin.basis_of_subset_cl_of_subset_of_encard_le (hX : M.rFin X) (hXI : X ⊆ M.cl I)
    (hIX : I ⊆ X) (hI : I.encard ≤ M.er X) : M.Basis I X := by
  obtain ⟨J, hJ⟩ := M.exists_basis (I ∩ M.E)
  have hIJ := hJ.subset.trans inter_subset_left
  rw [← cl_inter_ground] at hXI
  replace hXI := hXI.trans <| M.cl_subset_cl_of_subset_cl hJ.subset_cl
  have hJX := hJ.indep.basis_of_subset_of_subset_cl (hIJ.trans hIX) hXI
  rw [← hJX.encard] at hI
  rwa [← Finite.eq_of_subset_of_encard_le' (hX.finite_of_basis hJX) hIJ hI]

lemma rFin.iUnion [Fintype ι] {Xs : ι → Set α} (h : ∀ i, M.rFin (Xs i)) : M.rFin (⋃ i, Xs i) := by
  choose Is hIs using fun i ↦ M.exists_basis' (Xs i)
  have hfin : (⋃ i, Is i).Finite := finite_iUnion <| fun i ↦ (h i).finite_of_basis' (hIs i)
  rw [← rFin_cl_iff]
  have hcl := (M.rFin_of_finite hfin).to_cl
  rw [← M.cl_iUnion_cl_eq_cl_iUnion]
  simp_rw [← (hIs _).cl_eq_cl, M.cl_iUnion_cl_eq_cl_iUnion]
  assumption


end rFin

section Rank

/-- The rank function. Intended to be used in a `FiniteRk` matroid; otherwise `er` is better.-/
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

lemma rFin.coe_r_eq (hX : M.rFin X) : (M.r X : ℕ∞) = M.er X := by
  rw [r, coe_toNat (by rwa [er_ne_top_iff])]

lemma coe_r_eq_er_of_finite (M : Matroid α) (hX : X.Finite) : (M.r X : ℕ∞) = M.er X :=
  (M.rFin_of_finite hX).coe_r_eq

@[simp] lemma coe_r_eq (M : Matroid α) [FiniteRk M] (X : Set α) : (M.r X : ℕ∞) = M.er X :=
  (M.to_rFin X).coe_r_eq

lemma r_eq_of_er_eq (h : M.er X = M.er Y) : M.r X = M.r Y := by
  rw [r, r, h]

lemma rFin.er_eq_er_iff (hX : M.rFin X) (hY : M.rFin Y) : M.er X = M.er Y ↔ M.r X = M.r Y := by
  rw [← hX.coe_r_eq, ← hY.coe_r_eq, Nat.cast_inj]

lemma rFin.er_le_er_iff (hX : M.rFin X) (hY : M.rFin Y) : M.er X ≤ M.er Y ↔ M.r X ≤ M.r Y := by
  rw [← hX.coe_r_eq, ← hY.coe_r_eq, Nat.cast_le]

@[simp] lemma er_eq_er_iff [FiniteRk M] : M.er X = M.er Y ↔ M.r X = M.r Y :=
  (M.to_rFin X).er_eq_er_iff (M.to_rFin Y)

@[simp] lemma er_le_er_iff [FiniteRk M] : M.er X ≤ M.er Y ↔ M.r X ≤ M.r Y := by
  rw [← coe_r_eq, ← coe_r_eq, Nat.cast_le]

@[simp] lemma er_eq_coe_iff [FiniteRk M] {n : ℕ} : M.er X = n ↔ M.r X = n := by
  rw [← coe_r_eq, Nat.cast_inj]

@[simp] lemma er_le_coe_iff [FiniteRk M] {n : ℕ} : M.er X ≤ n ↔ M.r X ≤ n := by
  rw [← coe_r_eq, Nat.cast_le]

@[simp] lemma coe_le_er_iff [FiniteRk M] {n : ℕ} : (n : ℕ∞) ≤ M.er X ↔ n ≤ M.r X := by
  rw [← coe_r_eq, Nat.cast_le]

lemma rFin.r_le_r_of_er_le_er (hY : M.rFin Y) (hle : M.er X ≤ M.er Y) : M.r X ≤ M.r Y := by
  rwa [← rFin.er_le_er_iff _ hY]; exact hle.trans_lt hY.lt

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

@[simp] lemma r_empty (M : Matroid α) : M.r ∅ = 0 := by
  rw [r, er_empty]; rfl

@[simp] lemma r_cl_eq (M : Matroid α) : M.r (M.cl X) = M.r X := by
  rw [r, er_cl_eq, r]

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

lemma r_eq_zero_iff [FiniteRk M] (hX : X ⊆ M.E) : M.r X = 0 ↔ X ⊆ M.cl ∅ := by
  rw [← er_eq_coe_iff, coe_zero, er_eq_zero_iff]

@[simp] lemma r_loops (M : Matroid α) : M.r (M.cl ∅) = 0 := by
  simp [r]

lemma Nonloop.r_eq (he : M.Nonloop e) : M.r {e} = 1 := by
  rw [r, he.er_eq]; rfl

lemma Loop.r_eq (he : M.Loop e) : M.r {e} = 0 := by
  rw [r, he.er_eq]; rfl

lemma rFin.submod (hX : M.rFin X) (hY : M.rFin Y) : M.r (X ∩ Y) + M.r (X ∪ Y) ≤ M.r X + M.r Y := by
  obtain ⟨c, h_eq⟩ := le_iff_exists_add.1 <| M.er_inter_add_er_union_le_er_add_er X Y
  obtain (rfl | hc) := eq_or_ne c ⊤
  · rw [add_top, WithTop.add_eq_top] at h_eq
    simp [hX.ne, hY.ne] at h_eq
  have hi : M.rFin (X ∩ Y) := hX.subset inter_subset_left
  have hu : M.rFin (X ∪ Y) := hX.union hY
  rw [← ge_iff_le, r,r, ge_iff_le, ← toNat_add hX.ne hY.ne, h_eq, toNat_add _ hc,
    toNat_add hi.ne hu.ne, ← r, ← r]
  · apply Nat.le_add_right
  rw [Ne, WithTop.add_eq_top, not_or]
  exact ⟨hi.ne, hu.ne⟩

lemma r_submod (M : Matroid α) [FiniteRk M] (X Y : Set α) :
    M.r (X ∩ Y) + M.r (X ∪ Y) ≤ M.r X + M.r Y :=
  rFin.submod (M.to_rFin X) (M.to_rFin Y)

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
  refine ⟨fun h ↦ cl_empty_eq_ground_iff.1 ?_, fun h ↦ by rw [h, loopyOn_erk_eq]⟩
  obtain ⟨B, hB⟩ := M.exists_base
  rw [← hB.encard, encard_eq_zero] at h
  rw [← h, hB.cl_eq]

@[simp] lemma erk_loopyOn_eq_zero (α : Type*) : (emptyOn α).erk = 0 := by
  rw [erk_eq_zero_iff, emptyOn_ground, loopyOn_empty]

lemma eq_loopyOn_iff_cl : M = loopyOn E ↔ M.cl ∅ = E ∧ M.E = E :=
  ⟨fun h ↦ by rw [h]; simp, fun ⟨h,h'⟩ ↦ by rw [← h', ← cl_empty_eq_ground_iff, h, h']⟩

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
