import Matroid.Paving
import Matroid.Connectivity.Skew

open Set Set.Notation

namespace Matroid

variable {α β : Type*} {M : Matroid α} {C K X Y B I J : Set α} {e f : α}

section IsCrossing

/-- A `Crossing` is the intersection of a circuit and a cocircuit. -/
def IsCrossing (M : Matroid α) (X : Set α) : Prop :=
  ∃ C K, M.IsCircuit C ∧ M.IsCocircuit K ∧ X = C ∩ K

lemma IsCrossing.dual (h : M.IsCrossing X) : M✶.IsCrossing X := by
  obtain ⟨C, K, hC, hK, rfl⟩ := h
  exact ⟨K, C, hK, by simpa, inter_comm C K⟩

lemma IsCrossing.of_dual (h : M✶.IsCrossing X) : M.IsCrossing X :=
  M.dual_dual.symm ▸ h.dual

@[simp] lemma isCrossing_dual_iff : M✶.IsCrossing X ↔ M.IsCrossing X :=
  ⟨IsCrossing.of_dual, IsCrossing.dual⟩

lemma IsCrossing.subset_ground (h : M.IsCrossing X) : X ⊆ M.E := by
  obtain ⟨C, K, hC, -, rfl⟩ := h
  exact inter_subset_left.trans hC.subset_ground

lemma IsCrossing.encard_ne_one (h : M.IsCrossing X) : X.encard ≠ 1 := by
  rw [Ne, encard_eq_one]
  rintro ⟨e, rfl⟩
  obtain ⟨C, K, hC, hK, h'⟩ := h
  exact hC.inter_isCocircuit_ne_singleton hK h'.symm

lemma IsCrossing.of_contract (hC : (M ／ C).IsCrossing X) : M.IsCrossing X := by
  obtain ⟨X, Y, hX, hY, rfl⟩ := hC
  obtain ⟨X', hX', hXX', hX'X⟩ := hX.exists_subset_isCircuit_of_contract
  rw [contract_isCocircuit_iff] at hY
  refine ⟨X', Y, hX', hY.1, (inter_subset_inter_left _ hXX').antisymm
    (subset_inter ((inter_subset_inter_left Y hX'X).trans ?_) inter_subset_right)⟩
  rw [union_inter_distrib_right, hY.2.symm.inter_eq, union_empty]
  exact inter_subset_left

lemma IsCrossing.of_delete {D : Set α} (hD : (M ＼ D).IsCrossing X) : M.IsCrossing X := by
  have hd := hD.dual
  rw [dual_delete] at hd
  exact hd.of_contract.of_dual

lemma IsCrossing.of_isMinor {N : Matroid α} (hX : N.IsCrossing X) (hNM : N ≤m M) :
    M.IsCrossing X := by
  obtain ⟨C, D, -, -, -, rfl⟩ := hNM
  exact hX.of_delete.of_contract

lemma Iso.isCrossing_image {α β : Type*} {M : Matroid α} {N : Matroid β} {X : Set M.E} (i : M ≂ N)
    (hX : M.IsCrossing X) : N.IsCrossing ↑(i '' X) := by
  obtain ⟨C, K, hC, hK, hX⟩ := hX
  have hC' : M.IsCircuit (M.E ↓∩ C) := by simpa [inter_eq_self_of_subset_right hC.subset_ground]
  have hK' : M✶.IsCircuit (M✶.E ↓∩ K) := by simpa [inter_eq_self_of_subset_right hK.subset_ground]
  refine ⟨_, _, i.isCircuit_image hC', i.dual.isCircuit_image hK', ?_⟩
  simp only [dual_ground, dual_image]
  rw [← image_inter_on (by simp), ← image_inter_on (by simp), image_val_inj, ← preimage_inter, ← hX]
  simp

lemma IsCircuit.isCrossing_inter (hC : M.IsCircuit C) (hK : M.IsCocircuit K) :
    M.IsCrossing (C ∩ K) :=
  ⟨C, K, hC, hK, rfl⟩

lemma IsCocircuit.isCrossing_inter (hK : M.IsCocircuit K) (hC : M.IsCircuit C) :
    M.IsCrossing (K ∩ C) :=
  ⟨C, K, hC, hK, by rw [inter_comm]⟩

lemma IsCircuit.isCrossing_of_isCocircuit (hC : M.IsCircuit C) (hC' : M.IsCocircuit C) :
    M.IsCrossing C := by
  simpa using hC.isCrossing_inter hC'

end IsCrossing

section Tame

/-- A tame matroid is one whose circuit-cocircuit intersections (aka crossings) are all finite. -/
class Tame (M : Matroid α) : Prop where
  forall_isCrossing_finite : ∀ ⦃X⦄, M.IsCrossing X → X.Finite

lemma IsCrossing.finite [M.Tame] (h : M.IsCrossing X) : X.Finite :=
  Tame.forall_isCrossing_finite h

lemma IsCircuit.inter_finite_of_isCocircuit [M.Tame] (hC : M.IsCircuit C) (hK : M.IsCocircuit K) :
    (C ∩ K).Finite :=
  (hC.isCrossing_inter hK).finite

lemma Tame.dual (h : M.Tame) : M✶.Tame where
  forall_isCrossing_finite X hX := IsCrossing.finite (M := M) (by simpa using hX)

lemma tame_dual (M : Matroid α) [M.Tame] : M✶.Tame :=
  ‹M.Tame›.dual

@[simp]
lemma tame_dual_iff : M✶.Tame ↔ M.Tame :=
  ⟨fun h ↦ by simpa using h.dual, Tame.dual⟩

instance [M✶.Tame] : M.Tame := by
  rwa [← tame_dual_iff]

instance [M.Tame] (D : Set α) : (M ＼ D).Tame where
  forall_isCrossing_finite _ h := h.of_delete.finite

instance [M.Tame] (C : Set α) : (M ／ C).Tame where
  forall_isCrossing_finite _ h := h.of_contract.finite

instance [M.Finitary] : M.Tame where
  forall_isCrossing_finite X h := by
    obtain ⟨C, K, hC, hK, rfl⟩ := h
    exact hC.finite.inter_of_left _

instance [M✶.Finitary] : M.Tame where
  forall_isCrossing_finite X h := by
    obtain ⟨C, K, hC, hK, rfl⟩ := h
    exact hK.finite.inter_of_right _

lemma Tame.minor {N M : Matroid α} (h : M.Tame) (hNM : N ≤m M) : N.Tame := by
  obtain ⟨C, D, rfl⟩ := hNM
  infer_instance

/-- Every tame sparse paving matroid has finite rank or corank.
I am not sure if this is true or not for just `Paving`. -/
lemma SparsePaving.rankFinite_or_rankFinite_dual [M.Tame] (h : M.SparsePaving) :
    M.RankFinite ∨ M✶.RankFinite := by
  by_contra! hcon
  simp only [← eRank_lt_top_iff, not_lt, top_le_iff, eRank_eq_top_iff] at hcon
  cases hcon
  have : M✶✶.RankInfinite := by simpa
  obtain ⟨C, hC⟩ := M✶.exists_isCircuit
  obtain hi | hd := M.indep_or_dep hC.subset_ground
  · obtain ⟨K, hK, hCK⟩ := h.paving.exists_isCircuit_of_indep hi
    have hfin := hK.inter_finite_of_isCocircuit hC
    have hcon := h.paving_dual.eRank_le_eRk_add_one_of_dep hC.dep
    grw [M✶.eRank_eq_top, hC.eRk_add_one_eq, ← encard_diff_add_encard_inter C K,
      inter_comm, encard_le_one_iff_subsingleton.2 hCK] at hcon
    simp [hfin.not_infinite] at hcon
  obtain ⟨K, hKC, hK⟩ := hd.exists_isCircuit_subset
  have hfin := hK.inter_finite_of_isCocircuit hC
  grw [inter_eq_self_of_subset_left hKC, ← encard_lt_top_iff, ← hK.eRk_add_one_eq,
    ← h.paving.eRank_le_eRk_add_one_of_dep hK.dep] at hfin
  exact hfin.ne M.eRank_eq_top

end Tame
