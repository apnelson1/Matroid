
import Mathlib.Data.Nat.Lattice
import Matroid.Minor.Rank
import Matroid.Flat.LowRank
import Mathlib.Tactic.Linarith

/- Here we prove Edmonds' matroid intersection theorem: given two matroids `M₁` and `M₂` on `α`, the
  largest set that is independent in both matroids has size equal to the min of `M₁.r X + M₂.r Xᶜ`,
  taken over all `X ⊆ E`.  -/

open Set

namespace Matroid

variable {α : Type*} {M M₁ M₂ : Matroid α} {A I X E : Set α}

lemma Indep.ncard_le_rk_add_rk [FiniteRk M₁] [FiniteRk M₂] (hI₁ : M₁.Indep I) (hI₂ : M₂.Indep I)
    (A : Set α) : I.ncard ≤ M₁.rk A + M₂.rk (M₂.E \ A) := by
  rw [← ncard_inter_add_ncard_diff_eq_ncard I A hI₂.finite,
    ← (hI₁.inter_right A).rk_eq_ncard, ← (hI₂.diff A).rk_eq_ncard]
  exact add_le_add (M₁.rk_mono inter_subset_right)
    (M₂.rk_mono (diff_subset_diff_left hI₂.subset_ground))

lemma Indep.basis'_basis'_of_ncard_eq [FiniteRk M₁] [FiniteRk M₂] (hI₁ : M₁.Indep I)
    (hI₂ : M₂.Indep I) (h : M₁.rk A + M₂.rk (M₂.E \ A) ≤ I.ncard) :
    M₁.Basis' (I ∩ A) A ∧ M₂.Basis' (I \ A) (M₂.E \ A) := by
  rw [basis'_iff_indep_encard_eq_of_finite (hI₁.finite.subset inter_subset_left),
    and_iff_right inter_subset_right, and_iff_right (hI₁.inter_right A),
    basis'_iff_indep_encard_eq_of_finite hI₁.finite.diff, and_iff_right (hI₂.diff A),
    and_iff_right (diff_subset_diff_left hI₂.subset_ground), ← (hI₂.diff A).er,
    eRk_eq_eRk_iff, ← (hI₁.inter_right A).er, eRk_eq_eRk_iff]

  rw [← ncard_inter_add_ncard_diff_eq_ncard I A hI₂.finite,
    ← (hI₁.inter_right A).rk_eq_ncard, ← (hI₂.diff A).rk_eq_ncard] at h
  constructor <;>
  linarith [M₁.rk_mono (show I ∩ A ⊆ A from inter_subset_right),
    M₂.rk_mono (show I \ A ⊆ M₂.E \ A from diff_subset_diff_left hI₂.subset_ground)]

private lemma exists_common_ind_aux (M₁ M₂ : Matroid α) [M₁.Finite] (hE : M₁.E = M₂.E) :
    ∃ I X, X ⊆ M₁.E ∧ M₁.Indep I ∧ M₂.Indep I ∧ I.ncard = M₁.rk X + M₂.rk (M₂.E \ X) := by
  have _ : M₂.Finite := ⟨hE.symm ▸ M₁.ground_finite⟩
  by_cases hloop : ∀ e ∈ M₁.E, M₁.Loop e ∨ M₂.Loop e
  · suffices 0 = M₂.rk (M₂.E \ M₁.closure ∅) from
      ⟨∅, M₁.closure ∅, closure_subset_ground _ _, by simpa⟩
    rw [eq_comm, rk_eq_zero_iff diff_subset, diff_subset_iff, ← hE]
    simpa [subset_def]
  push_neg at hloop
  obtain ⟨e, he, he₁, he₂⟩ := hloop
  rw [not_loop_iff] at he₁ he₂

  have : (M₁ ／ e).E.ncard < M₁.E.ncard := ncard_lt_ncard (by simpa) M₁.ground_finite
  have : (M₁ ＼ e).E.ncard < M₁.E.ncard := ncard_lt_ncard (by simpa) M₁.ground_finite

  obtain ⟨Id, Xd, hXd, hId₁, hId₂, hId⟩ := exists_common_ind_aux (M₁ ＼ e) (M₂ ＼ e) (by simp [hE])
  obtain ⟨Ic, Xc, hXc, hIc₁, hIc₂, hIc⟩ := exists_common_ind_aux (M₁ ／ e) (M₂ ／ e) (by simp [hE])

  rw [he₁.contract_indep_iff] at hIc₁
  rw [he₂.contract_indep_iff] at hIc₂

  simp only [contract_elem, contract_ground, deleteElem, delete_ground,
    subset_diff_singleton_iff] at hXc hXd

  by_contra! hcon
  replace hcon :=
    show ∀ I X, X ⊆ M₁.E → M₁.Indep I → M₂.Indep I → I.ncard + 1 ≤ M₁.rk X + M₂.rk (M₂.E \ X) from
    fun I X hX h h' ↦ Nat.add_one_le_iff.2 <| (h.ncard_le_rk_add_rk h' X).lt_of_ne <| hcon I X hX h h'

  have hcond := hcon Id (Xc ∩ Xd) (inter_subset_left.trans hXc.1) hId₁.of_delete hId₂.of_delete

  replace hcon := hcon (insert e Ic) (insert e (Xc ∪ Xd))
    (insert_subset he₁.mem_ground (union_subset hXc.1 hXd.1)) hIc₁.2 hIc₂.2
  rw [ncard_insert_of_not_mem hIc₁.1 (hIc₁.2.subset (subset_insert _ _)).finite,
    ← insert_union] at hcon

  have hsm := M₁.rk_submod (insert e Xc) Xd
  rw [insert_inter_of_not_mem hXd.2] at hsm

  have hsm2 := M₂.rk_submod (M₂.E \ Xc) ((M₂.E \ insert e Xd))
  simp_rw [diff_eq, ← inter_inter_distrib_left, ← inter_union_distrib_left, ← compl_inter,
    ← compl_union, union_insert, ← insert_union, inter_comm Xc, insert_inter_of_not_mem hXc.2,
    inter_comm Xd, ← diff_eq] at hsm2

  zify at hcon hcond hId hIc hsm hsm2

  rw [he₂.contract_rk_cast_int_eq, he₁.contract_rk_cast_int_eq, contract_elem, contract_ground,
    diff_diff_comm, insert_diff_singleton,
      insert_eq_of_mem (show e ∈ M₂.E \ Xc from ⟨he₂.mem_ground, hXc.2⟩)] at hIc
  rw [delete_elem_rk_eq _ hXd.2, delete_elem_rk_eq _ (by simp), deleteElem, delete_ground,
    diff_diff_comm, diff_diff, union_singleton] at hId

  linarith
termination_by M₁.E.ncard

/-- The matroid intersection theorem. The hypothesis `M₁.E = M₂.E` isn't required. -/
theorem exists_common_ind (M₁ M₂ : Matroid α) [M₁.Finite] :
    ∃ I X, M₁.Indep I ∧ M₂.Indep I ∧ I.ncard = M₁.rk X + M₂.rk (M₂.E \ X) := by
  obtain ⟨I, X, -, hI₁, hI₂, hcard⟩ := exists_common_ind_aux M₁ (M₂ ↾ M₁.E) rfl
  refine ⟨I, (M₂.E \ M₁.E) ∪ X, hI₁, hI₂.of_restrict, ?_⟩
  rw [← diff_diff, diff_diff_right_self, ← rk_inter_ground, union_inter_distrib_right,
    disjoint_sdiff_left.inter_eq, empty_union, rk_inter_ground, hcard,
    restrict_rk_eq _ (by simp [diff_subset]), restrict_ground_eq, ← M₂.rk_inter_ground,
    inter_diff_assoc, inter_comm]

/-- A minimizer can be chosen in the matroid intersection theorem that is a flat of `M₁`.-/
theorem exists_common_ind_with_flat_left (M₁ M₂ : Matroid α) [M₁.Finite] (hE : M₁.E = M₂.E) :
    ∃ I X, M₁.Flat X ∧ M₁.Indep I ∧ M₂.Indep I ∧ I.ncard = M₁.rk X + M₂.rk (M₂.E \ X) := by
  have : M₂.Finite := ⟨hE.symm ▸ M₁.ground_finite⟩
  obtain ⟨I,X, -, h1,h2, h⟩ := exists_common_ind_aux M₁ M₂ hE
  refine ⟨I, _, M₁.closure_flat X, h1, h2, (h1.ncard_le_rk_add_rk h2 _).antisymm ?_⟩
  rw [rk_closure_eq, h, ← diff_inter_self_eq_diff (t := X), ← hE]
  exact add_le_add_left (M₂.rk_mono (diff_subset_diff_right <| inter_ground_subset_closure M₁ X)) _

/-- The cardinality of a largest common independent set of matroids `M₁,M₂`. -/
noncomputable def maxCommonInd (M₁ M₂ : Matroid α) : ℕ :=
  sSup {n | ∃ I, M₁.Indep I ∧ M₂.Indep I ∧ I.ncard = n}

lemma Indep.le_maxCommonInd [M₁.Finite] (hI₁ : M₁.Indep I) (hI₂ : M₂.Indep I) :
    I.ncard ≤ maxCommonInd M₁ M₂ := by
  classical
  rw [maxCommonInd, Nat.sSup_def, Nat.le_find_iff]
  · simp only [mem_setOf_eq, forall_exists_index, and_imp, not_forall, Classical.not_imp, not_le]
    exact fun m hm ↦ ⟨_, I, hI₁, hI₂, rfl, hm⟩
  refine ⟨M₁.E.ncard, ?_⟩
  simp only [mem_setOf_eq, forall_exists_index, and_imp]
  rintro - J hJ₁ - rfl
  exact ncard_le_ncard hJ₁.subset_ground M₁.ground_finite

lemma maxCommonInd_exists (M₁ M₂ : Matroid α) [M₁.Finite] :
    ∃ I, M₁.Indep I ∧ M₂.Indep I ∧ I.ncard = maxCommonInd M₁ M₂ := by
  refine Nat.sSup_mem (s := {n | ∃ I, M₁.Indep I ∧ M₂.Indep I ∧ I.ncard = n}) ⟨0, ∅, by simp⟩
    ⟨M₁.E.ncard, ?_⟩
  simp only [upperBounds, mem_setOf_eq, forall_exists_index, and_imp]
  rintro _ I hI - rfl
  exact ncard_le_ncard hI.subset_ground M₁.ground_finite

theorem matroid_intersection_minmax (M₁ M₂ : Matroid α) [M₁.Finite] [M₂.FiniteRk] :
    maxCommonInd M₁ M₂ = ⨅ X, M₁.rk X + M₂.rk (M₂.E \ X) := by
  refine le_antisymm (le_ciInf fun X ↦ ?_) ?_
  · obtain ⟨I, hI₁, hI₂, hI⟩ := maxCommonInd_exists M₁ M₂
    rw [← hI]
    exact hI₁.ncard_le_rk_add_rk hI₂ X
  obtain ⟨I, X, hI₁, hI₂, h⟩ := exists_common_ind M₁ M₂
  exact (ciInf_le ⟨0, by simp [lowerBounds]⟩ X).trans (h.symm.le.trans (hI₁.le_maxCommonInd hI₂))

section Rado

variable {ι : Type*} {x : ι → α}

lemma rado_necessary [FiniteRk M] {f : α → ι} (hx : ∀ i, f (x i) = i) (h_ind : M.Indep (range x))
    (S : Set ι) : S.ncard ≤ M.rk (f ⁻¹' S) := by
  have hinj : Function.Injective x := fun i j h ↦ by rw [← hx i, ← hx j, h]
  have hS := (h_ind.subset (image_subset_range x S)).rk_eq_ncard
  rw [ncard_image_of_injective _ hinj] at hS
  refine hS.symm.le.trans (M.rk_le_of_subset ?_)
  rintro f ⟨i, hi, rfl⟩
  simpa [hx i]

end Rado

-- section rado

-- variables {ι : Type} [finite ι]

-- lemma rado_necessary {f : E → ι} {x : ι → E} (hx : ∀ i, f (x i) = i) (h_ind : M.indep (range x))
-- (S : set ι) :
--   S.ncard ≤ M.r (f ⁻¹' S) :=
-- begin
--   have hS := (h_ind.subset (image_subset_range x S)).r,
--   rw [ncard_image_of_injective _ (λ i j hij, by rw [←hx i, hij, hx j] : x.injective)] at hS,
--   rw ←hS,
--   refine M.rk_mono _,
--   rintro f ⟨i, hi, rfl⟩,
--   rwa [mem_preimage, hx],
-- end

-- lemma rado_sufficient (f : E → ι) (h : ∀ (S : set ι), S.ncard ≤ M.r (f ⁻¹' S)) :
--   ∃ (x : ι → E), (∀ i, f (x i) = i) ∧ M.indep (range x) :=
-- begin
--   set M' := partition_matroid_on f 1 with hM',
--   obtain ⟨I, X, hI₁, hI₂, hIX, hF⟩ := exists_common_ind_with_flat_right M M',
--   obtain ⟨hIb₁,hIb₂⟩ := common_ind_eq_spec hI₁ hI₂ hIX.symm.le,

--   have h_inj : inj_on f I,
--   { refine λ a ha b hb hab, by_contra (λ (hne : a ≠ b), _),
--     have hcard := (partition_matroid_on_indep_iff.mp hI₂) (f a),
--     rw [pi.one_apply, ncard_le_one_iff] at hcard,
--     exact hne (hcard ⟨ha, (by simp)⟩ ⟨hb, by simp [hab]⟩)},

--   have hXc := (h (f '' Xᶜ)ᶜ).trans (M.rk_mono _ : _ ≤ M.r X), swap,
--   { simp only [preimage_subset_iff, mem_compl_iff, mem_image, not_exists, not_and, not_imp_not],
--     exact λ a h, h _ rfl},

--   simp only [partition_matroid_on_one_rk_eq, pi.one_apply] at hIX,
--   have hineq := (add_le_add_right hXc _).trans_eq hIX.symm,
--   rw [add_comm, ncard_add_ncard_compl, ←ncard_univ, ←ncard_image_of_inj_on h_inj] at hineq,
--   have himage := eq_of_subset_of_ncard_le (subset_univ _) hineq,

--   have hinv : ∀ i, ∃ e ∈ I, f e = i,
--   { simp_rw [←mem_image_iff_bex, himage], exact mem_univ},

--   choose x hx using hinv,
--   refine ⟨x, λi, (hx i).2, hI₁.subset _⟩,
--   rintro e ⟨i,hi,rfl⟩,
--   exact (hx i).1,
-- end

-- /-- Rado's theorem: Given a partition `f : E → ι` of the ground set `E` of a matroid `M`, there is a
--   transversal of `f` that is independent in `M` if and only if the rank of the preimage of every set
--   `S` in `ι` is at least its cardinality. -/
-- theorem rado_iff {M : matroid E} {f : E → ι} :
--   (∃ (x : ι → E), (∀ i, f (x i) = i) ∧ M.indep (range x)) ↔ ∀ S, ncard S ≤ M.r (f ⁻¹' S) :=
-- ⟨λ h S, exists.elim h (λ x hx, rado_necessary hx.1 hx.2 _) , rado_sufficient _⟩


-- end rado
