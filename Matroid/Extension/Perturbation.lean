import Matroid.Uniform.Minor
import Matroid.Extension.ProjectionBy

variable {α β : Type*} {M N M' : Matroid α} {I X Y : Set α} {e f : α} {a k l : ℕ∞}
    {T : Set (Set α)}

open Set

namespace Matroid


/-- `M.IsPerturbation N k` means that `N` can be obtained from `M` by a finite sequence of lifts
and projections, with combined cardinality at most `k`.
(each lift/projection in the sequence is possibly by an infinite set. )
This is defined inductively; each matroid is a `0`-perturbation of itself,
and for all `M, N, N'` for which `N` is a `k`-perturbation of `M` and one of `N` or `N'`
is an `l`-projection of the other, then `M` is a `(k + l)`-perturbation of `N'`. -/
inductive IsPerturbation.{u} {α : Type u} : Matroid α → Matroid α → ℕ∞ → Prop
  | refl' (M : Matroid α) : M.IsPerturbation M 0
  | cons_left {M N N' : Matroid α} {k : ℕ∞} (h : IsPerturbation M N k)
      {β : Type u} (P : N.Projector N' β) : IsPerturbation M N' (k + P.pivot.encard)
  | cons_right {M N N' : Matroid α} {k : ℕ∞} (h : IsPerturbation M N k) {β : Type u}
       (P : N'.Projector N β) : IsPerturbation M N' (k + P.pivot.encard)

lemma IsPerturbation.trans {M₁ M₂ M₃ : Matroid α}
    (h : M₁.IsPerturbation M₂ l) (h' : M₂.IsPerturbation M₃ k) :
    M₁.IsPerturbation M₃ (l + k) := by
  induction h' generalizing M₁ with
  | refl' => simpa
  | cons_left h P ih => rw [← add_assoc]; exact (ih h).cons_left P
  | cons_right h P ih => rw [← add_assoc]; exact (ih h).cons_right P

@[simp]
lemma IsPerturbation.refl (M : Matroid α) {k : ℕ∞} : M.IsPerturbation M k := by
  have hwin := (IsPerturbation.refl' M).cons_left (β := ULift ℕ∞)
    (Projector.refl_set M (ULift.up '' (Iio k)))
  rwa [zero_add, Projector.refl_set_pivot, ULift.up_injective.encard_image, ENat.encard_Iio] at hwin

lemma IsPerturbation.mono (h : M.IsPerturbation N k) (hkl : k ≤ l) : M.IsPerturbation N l := by
  obtain ⟨d, rfl⟩ := exists_add_of_le hkl
  rw [add_comm]
  exact (IsPerturbation.refl M).trans h

lemma Projector.isPerturbation (P : M.Projector N β) : M.IsPerturbation N P.pivot.encard := by
  obtain ⟨γ, Q, hQu, hQi, hQci, -, ⟨f⟩⟩ := P.exists_good_projector
  refine ((IsPerturbation.refl' M).cons_left Q).mono ?_
  grw [hQu, encard_univ, Function.Injective.encard_range f.2, encard_le_card, ENat.card_coe_set_eq,
    zero_add]

lemma IsPerturbation.symm (h : M.IsPerturbation N k) : N.IsPerturbation M k := by
  induction h with
  | refl' => exact IsPerturbation.refl' M
  | cons_left h P ih =>
    obtain ⟨γ, Q, hQu, hQi, hQci, -, ⟨f⟩⟩ := P.exists_good_projector
    rw [add_comm]
    refine (((IsPerturbation.refl' _).cons_right Q).mono ?_).trans ih
    grw [hQu, encard_univ, Function.Injective.encard_range f.2, encard_le_card,
      ENat.card_coe_set_eq, zero_add]
  | cons_right h P ih => rw [add_comm]; exact P.isPerturbation.trans ih

lemma isPerturbation_comm : M.IsPerturbation N k ↔ N.IsPerturbation M k :=
  ⟨IsPerturbation.symm, IsPerturbation.symm⟩

lemma IsPerturbation.dual (h : M.IsPerturbation N k) : M✶.IsPerturbation N✶ k := by
  induction h with
  | refl' => exact IsPerturbation.refl M✶
  | cons_left h P ih => exact ih.trans P.dual.isPerturbation.symm
  | cons_right h P ih => exact ih.trans P.dual.isPerturbation

lemma IsPerturbation.ground_eq (h : M.IsPerturbation N k) : M.E = N.E := by
  induction h with
  | refl' => rfl
  | cons_left h P ih => rw [ih, P.ground_eq]
  | cons_right h P ih => rw [ih, P.ground_eq]

@[simp]
lemma IsPerturbation_dual_iff : M✶.IsPerturbation N✶ k ↔ M.IsPerturbation N k :=
  ⟨fun h ↦ by simpa using h.dual, IsPerturbation.dual⟩

lemma isPerturbation_dual_comm : M✶.IsPerturbation N k ↔ M.IsPerturbation N✶ k := by
  rw [← IsPerturbation_dual_iff, dual_dual]

/-- An induction principle for `IsPerturbation` that uses projections in only one direction,
and also duality. -/
@[elab_as_elim]
lemma IsPerturbation.recDual.{u} {α : Type u}
    {motive : (M N : Matroid α) → (k : ℕ∞) → M.IsPerturbation N k → Prop}
    (h0 : ∀ M, motive M M 0 (IsPerturbation.refl' M))
    (ih : ∀ (M N N' k) (h : M.IsPerturbation N k) {β : Type u} (P : N.Projector N' β),
      motive M N k h → motive M N' (k + P.pivot.encard) (h.trans P.isPerturbation))
    (dual : ∀ M N k h, motive M N k h → motive M✶ N✶ k h.dual)
    {M N : Matroid α} {k : ℕ∞} (h : M.IsPerturbation N k) : motive M N k h := by
  induction h with
  | refl' => exact h0 _
  | cons_left h P ih' => exact ih _ _ _ _ h _ ih'
  | @cons_right N₁ N₂ k h β P ih' =>
    simpa using dual _ _ _ _ <| ih _ _ _ _ h.dual P.dual (dual _ _ _ h ih')

lemma IsPerturbation.contract (h : M.IsPerturbation N k) (C : Set α) :
    (M ／ C).IsPerturbation (N ／ C) k := by
  induction h with
  | refl' => exact IsPerturbation.refl _
  | cons_left h P ih => exact ih.trans <| by simpa using (P.contract_contract C).isPerturbation
  | cons_right h P ih =>
    exact ih.trans <| by simpa using (P.contract_contract C).isPerturbation.symm

lemma IsPerturbation.delete (h : M.IsPerturbation N k) (D : Set α) :
    (M ＼ D).IsPerturbation (N ＼ D) k := by
  simpa using (h.dual.contract D).dual

lemma isPerturbation_loopyOn (M : Matroid α) : M.IsPerturbation (loopyOn M.E) M.eRank := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  refine hB.spanning.projector_loopyOn.isPerturbation.symm.mono ?_
  grw [encard_le_card, ENat.card_coe_set_eq, hB.encard_eq_eRank]

lemma isPerturbation_freeOn (M : Matroid α) : M.IsPerturbation (freeOn M.E) M✶.eRank := by
  simpa using M✶.isPerturbation_loopyOn.dual

lemma isPerturbation_eRank_add_eRank_of_ground_eq (h : M.E = N.E) :
    M.IsPerturbation N (M.eRank + N.eRank) :=
  (h ▸ (M.isPerturbation_loopyOn)).trans N.isPerturbation_loopyOn.symm

lemma IsPerturbation.exists_isPerturbation_minor (hM' : M.IsPerturbation M' k) (h : N ≤m M) :
    ∃ (N' : Matroid α), N' ≤m M' ∧ N.IsPerturbation N' k := by
  induction hM' using IsPerturbation.recDual generalizing N with
  | h0 M => exact ⟨N, h, by simp⟩
  | ih M M₁ M₂ k h P ih' =>
    obtain ⟨N₁', hN₁', h''⟩ := ih' h
    obtain ⟨C, D, hC, hD, hCD, rfl⟩ := hN₁'
    refine ⟨M₂ ／ C ＼ D, contract_delete_isMinor .., ?_⟩
    simpa using h''.trans ((P.contract_contract C).delete_delete D).isPerturbation
  | dual M M₁ k h ih =>
    obtain ⟨N₁, hN₁m, hN₁⟩ := ih (N := N✶) (by rwa [← dual_isMinor_iff, dual_dual])
    exact ⟨N₁✶, by simpa, by simpa using hN₁.dual⟩

lemma isPerturbation_project (M : Matroid α) (X : Set α) :
    M.IsPerturbation (M.project X) (M.eRk X) := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [hI.project_eq_project, hI.eRk_eq_encard]
  refine (M.projector_project I).isPerturbation.symm.mono ?_
  grw [encard_le_card, ENat.card_coe_set_eq]

lemma IsPerturbation.eRank_le_add (h : M.IsPerturbation N k) : M.eRank ≤ N.eRank + k := by
  induction h with
  | refl' => simp
  | @cons_left M' N k h β P ih' =>
    have h1 := congr_arg Matroid.eRank P.contract_image_pivot
    have h2 := congr_arg Matroid.eRank P.delete_image_pivot
    rw [eRank_map] at h1 h2
    grw [ih', add_comm k, ← add_assoc, ← h1, ← h2, eRank_contract_le_eRank_delete,
      add_right_comm, ← le_self_add (b := P.pivot.encard)]
  | @cons_right M' N k h β P ih' =>
    have h1 := congr_arg Matroid.eRank P.contract_image_pivot
    have h2 := congr_arg Matroid.eRank P.delete_image_pivot
    rw [eRank_map] at h1 h2
    grw [ih', ← h1, ← h2, ← add_assoc, add_right_comm,
      ← Function.Injective.encard_image Sum.inr_injective,
        ← eRk_le_encard (M := (P : Matroid (α ⊕ β))), eRank_contract_add_eRk,
        eRank_delete_le]

lemma isPerturbation_of_contract_eq_contract (h : M.E = N.E) (hMX : M ／ X = N ／ X) :
    M.IsPerturbation N (M.eRk X + N.eRk X) := by
  have hMX' : M.project X = N.project X :=
    ext_indep (by simpa) fun I hI ↦ by rw [project_indep_iff, hMX, project_indep_iff]
  refine (M.isPerturbation_project X).trans ?_
  rw [hMX']
  exact (N.isPerturbation_project X).symm

lemma isPerturbation_of_delete_eq_delete (h : M.E = N.E) (hMX : M ＼ X = N ＼ X) :
    M.IsPerturbation N (M✶.eRk X + N✶.eRk X) := by
  have h := isPerturbation_of_contract_eq_contract (M := M✶) (N := N✶) (by simpa) (X := X)
    <| by rwa [← dual_inj, dual_contract_dual, dual_contract_dual]
  simpa using h.dual

lemma isPerturbation_loopify (M : Matroid α) (X : Set α) :
    M.IsPerturbation (M.loopify X) (2 * X.encard) := by
  refine (M.isPerturbation_of_delete_eq_delete (N := M.loopify X) (X := X) rfl (by simp)).mono ?_
  grw [eRk_le_encard, eRk_le_encard, two_mul]

lemma ModularCut.isPerturbation_projectBy (U : M.ModularCut) :
    M.IsPerturbation (M.projectBy U) 1 :=
  U.Projector.isPerturbation.symm.mono <| (encard_le_card ..).trans <| by simp

/-- The minimum size of a perturbation needed to take `M` to `N`.
This is a little coarser than `IsPerturbation` in the information it contains,
since Matroids `M, N` with distinct ground sets satisfy `dist M N = ⊤`,
but are not perturbations of eachother.   -/
protected noncomputable def dist (M N : Matroid α) : ℕ∞ := sInf {k | M.IsPerturbation N k}

lemma IsPerturbation.dist_le (h : M.IsPerturbation N k) : M.dist N ≤ k :=
  sInf_le h

@[simp]
lemma dist_self (M : Matroid α) : M.dist M = 0 := by
  simp [Matroid.dist]

lemma dist_comm : M.dist N = N.dist M := by
  simp_rw [Matroid.dist, isPerturbation_comm]

lemma dist_le_eRank_add_eRank (h : M.E = N.E) : M.dist N ≤ M.eRank + N.eRank :=
  (isPerturbation_eRank_add_eRank_of_ground_eq h).dist_le

lemma isPerturbation_dist (h : M.E = N.E) : M.IsPerturbation N (M.dist N) :=
  ENat.sInf_mem (s := {k | M.IsPerturbation N k}) ⟨_, isPerturbation_eRank_add_eRank_of_ground_eq h⟩
