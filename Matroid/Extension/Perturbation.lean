import Matroid.Uniform.Minor
import Matroid.Extension.ProjectionBy
import Matroid.ForMathlib.Data.ENat.Powerset

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

lemma IsPerturbation.trans {M₁ M₂ M₃ : Matroid α} (h : M₁.IsPerturbation M₂ l)
    (h' : M₂.IsPerturbation M₃ k) : M₁.IsPerturbation M₃ (l + k) := by
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

lemma IsPerturbation.trans_le {M₁ M₂ M₃ : Matroid α} {j : ℕ∞} (h₁ : M₁.IsPerturbation M₂ j)
    (h₂ : M₂.IsPerturbation M₃ k) (hle : j + k ≤ l) : M₁.IsPerturbation M₃ l :=
  (h₁.trans h₂).mono hle

@[simp]
lemma isPerturbation_zero_iff : M.IsPerturbation N 0 ↔ M = N := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  generalize hk : (0 : ℕ∞) = k at h
  induction h with
  | refl' => rfl
  | @cons_left M' N' c h β P ih' =>
    rw [eq_comm, add_eq_zero, encard_eq_zero] at hk
    rw [ih' hk.1.symm, P.eq_of_pivot_eq_empty hk.2]
  | @cons_right M' N' c h β P ih' =>
    rw [eq_comm, add_eq_zero, encard_eq_zero] at hk
    rw [ih' hk.1.symm, P.eq_of_pivot_eq_empty hk.2]

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
  exact (M.isPerturbation_project X).trans <| hMX' ▸ (N.isPerturbation_project X).symm

lemma isPerturbation_eRk_dual_of_delete_eq_delete (h : M.E = N.E) (hMX : M ＼ X = N ＼ X) :
    M.IsPerturbation N (M✶.eRk X + N✶.eRk X) := by
  have h := isPerturbation_of_contract_eq_contract (M := M✶) (N := N✶) (by simpa) (X := X)
    <| by rwa [← dual_inj, dual_contract_dual, dual_contract_dual]
  simpa using h.dual

lemma isPerturbation_loopify_encard (M : Matroid α) (X : Set α) :
    M.IsPerturbation (M.loopify X) (2 * X.encard) := by
  refine (M.isPerturbation_eRk_dual_of_delete_eq_delete (N := M.loopify X) (X := X)
    rfl (by simp)).mono ?_
  grw [eRk_le_encard, eRk_le_encard, two_mul]

/-- A version of `isPerturbation_loopify_encard` where the bound is in terms of the rank
rather than the cardinality of `X`. -/
lemma isPerturbation_loopify (M : Matroid α) (X : Set α) :
    M.IsPerturbation (M.loopify X) (4 * M.eRk X) := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  have h1 := M.isPerturbation_project X
  rw [hI.project_eq_loopify_project] at h1
  have h2 := ((M.loopify (X \ I)).isPerturbation_project I).symm
  have h3 := (M.loopify (X \ I)).isPerturbation_loopify_encard I
  rw [loopify_loopify, union_comm, union_diff_cancel hI.subset] at h3
  convert (h1.trans h2).trans h3 using 1
  rw [hI.eRk_eq_encard, Indep.eRk_eq_encard]
  · ring
  rw [loopify_indep_iff]
  exact ⟨hI.indep, disjoint_sdiff_right⟩

lemma isPerturbation_eRk_of_delete_eq_delete (h : M.E = N.E) (hMX : M ＼ X = N ＼ X) :
    M.IsPerturbation N (4 * (M.eRk X + N.eRk X)) := by
  have hX' : M.loopify X = N.loopify X := by
    simpa [ext_iff_indep, loopify_indep_iff_delete_indep, hMX]
  have h1 := M.isPerturbation_loopify X
  rw [hX'] at h1
  replace h1 := h1.trans (N.isPerturbation_loopify X).symm
  rwa [← mul_add] at h1

lemma ModularCut.isPerturbation_projectBy (U : M.ModularCut) :
    M.IsPerturbation (M.projectBy U) 1 :=
  U.Projector.isPerturbation.symm.mono <| (encard_le_card ..).trans <| by simp

lemma ModularCut.isPerturbation_liftBy (U : M✶.ModularCut) :
    M.IsPerturbation (M.liftBy U) 1 := by
  have h := U.isPerturbation_projectBy.dual
  rwa [dual_dual, projectBy_dual] at h

example (M : Matroid α) (L : Set α) (hLr : ¬ (L ⊆ M.loops)) (hL : L ⊆ M.E) :
    ∃ (N : Matroid α), N.IsPerturbation M 2 ∧ N ＼ L = M ＼ L ∧ N.eRk L + 1 = M.eRk L := by
  set R := M.liftBy (ModularCut.principal M✶ L) with hR
  have hR1 : R ＼ L = M ＼ L := by
    rw [hR, ModularCut.liftBy_delete_eq_delete_of_dual_closure_mem _ (by simp)]
  set N := R.projectBy (ModularCut.principal R L) with hN
  have hRL : R.Codep L :=
    ModularCut.liftBy_principal_codep _ (by contrapose! hLr; simp [hLr]) hL
  -- have h' : (ModularCut.principal R L).delete L = ⊥ := by
  --   rw [ModularCut.principal_delete_eq_bot hRL]
    -- rw [ModularCut.eq_bot_iff, ModularCut.mem_delete_iff, and_iff_right (R ＼ L).ground_isFlat,
    --   ModularCut.mem_principal_iff]
  have hN1 : R ＼ L = N ＼ L := by
    rw [hN, ← ModularCut.projectBy_delete, (ModularCut.principal_delete_self_eq_bot_iff _).2 hRL,
      ModularCut.projectBy_bot]
  have hloops : ¬ (L ⊆ R.loops) := by
    grw [hR, (liftBy_quotient _).weakLE.loops_subset_loops]
    exact hLr
  have hr : N.eRk L + 1 = M.eRk L := by
    rw [hN, ModularCut.projectBy_eRk_add_one_eq _ hloops (subset_closure ..), hR]


    -- assumption


    -- , eq_comm, ModularCut.projectBy_eq_self_iff,
    --   ModularCut.eq_bot_iff, ModularCut.eq_top_iff]


  -- set U := ModularCut.principal M✶  L with hU

  -- set V := ModularCut.principal (M✶.projectBy U)✶ L with hV
  -- -- set R := (M✶.projectBy U)✶ with hR
  -- refine ⟨(M✶.projectBy U)✶.projectBy V, ?_, ?_, ?_⟩
  -- · refine V.isPerturbation_projectBy.symm.trans_le (M₂ := (M✶.projectBy U)✶) (k := 1)
  --     ?_ rfl.le
  --   have h1 := U.isPerturbation_projectBy.dual.symm
  --   rwa [dual_dual] at h1
  -- ·

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

section shift

variable {f : α → α} {C : Set α}

/-- `M.IsShift C f` means that `f` is a function that is the identity outside `M.E \ M.closure C`,
such that `f x` and `x` are parallel in `M ／ C` for all `x ∈ M.E \ M.closure C`. -/
@[mk_iff]
structure IsShift (M : Matroid α) (C : Set α) (f : α → α) : Prop where
  closure_eq_closure' :
    ∀ x ∈ M.E, x ∉ M.closure C → M.closure (insert x C) = M.closure (insert (f x) C)
  eq_self_of_mem_closure : ∀ x ∈ M.closure C, f x = x
  eq_self_of_notMem_ground : ∀ x ∉ M.E, f x = x

lemma IsShift.closure_eq_closure (h : M.IsShift C f) (x : α) :
    M.closure (insert x C) = M.closure (insert (f x) C) := by
  by_cases hxC : x ∈ M.closure C
  · rw [h.eq_self_of_mem_closure _ hxC]
  by_cases hxE : x ∈ M.E
  · rw [h.closure_eq_closure' _ hxE hxC]
  rw [h.eq_self_of_notMem_ground _ hxE]

lemma IsShift.apply_mem_iff_of_disjoint {x} (h : M.IsShift C f)
    (hX : Disjoint X (M.E \ M.closure C)) : f x ∈ X ↔ x ∈ X := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · by_cases hxE : x ∈ M.E
    · by_cases hxC : x ∈ M.closure C
      · rwa [h.eq_self_of_mem_closure _ hxC] at hx
      by_contra hcon
      have hxcl := (h.closure_eq_closure x).subset (M.mem_closure_of_mem' (by simp) hxE)
      refine hX.notMem_of_mem_left hx ⟨by_contra fun hcon' ↦ hxC ?_, fun hcl ↦ hxC ?_⟩
      · rwa [← closure_inter_ground, insert_inter_of_notMem hcon', closure_inter_ground] at hxcl
      rwa [closure_insert_eq_of_mem_closure hcl] at hxcl
    rwa [h.eq_self_of_notMem_ground _ hxE] at hx
  have himp : x ∈ M.E → x ∈ M.closure C := by simpa using hX.notMem_of_mem_left hx
  by_cases hxE : x ∈ M.E
  · rwa [h.eq_self_of_mem_closure _ (himp hxE)]
  rwa [h.eq_self_of_notMem_ground _ hxE]

lemma IsShift.apply_mem_closure_iff {x} (h : M.IsShift C f) :
    x ∈ M.closure C ↔ f x ∈ M.closure C := by
  rw [h.apply_mem_iff_of_disjoint disjoint_sdiff_right]

lemma IsShift.apply_mem_ground_iff {x} (h : M.IsShift C f) : f x ∈ M.E ↔ x ∈ M.E := by
  rw [← notMem_compl_iff, h.apply_mem_iff_of_disjoint (by grind), notMem_compl_iff]

lemma IsShift.mapsTo (h : M.IsShift C f) : MapsTo f M.E M.E := by
  simp [MapsTo, h.apply_mem_ground_iff]

lemma IsShift.preimage_eq (h : M.IsShift C f) : f ⁻¹' M.E = M.E :=
  subset_antisymm (fun x hx ↦ by_contra fun hxE ↦ hxE (by rwa [← h.eq_self_of_notMem_ground x hxE]))
    h.mapsTo.subset_preimage

lemma IsShift.eqOn (h : M.IsShift C f) : EqOn f id C := by
  intro x hx
  by_cases hxE : x ∈ M.E
  · rw [h.eq_self_of_mem_closure _ (M.mem_closure_of_mem' hx hxE), id_eq]
  rw [h.eq_self_of_notMem_ground _ hxE, id_eq]

lemma IsShift.eqOn_closure (h : M.IsShift C f) : EqOn f id (M.closure C) := by
  intro x hx
  exact h.eq_self_of_mem_closure _ hx

lemma IsShift.preimage_eq_of_subset_closure (h : M.IsShift C f) (hX : X ⊆ M.closure C) :
    f ⁻¹' X = X :=
  Set.ext fun x ↦ by rw [mem_preimage, h.apply_mem_iff_of_disjoint (by grind)]

lemma IsShift.comap_contract_eq (h : M.IsShift C f) : M ／ C = (M.comap f) ／ C := by
  refine ext_closure fun X ↦ ?_
  simp only [contract_closure_eq, comap_closure_eq, image_union, h.eqOn.image_eq, id_eq, image_id']
  obtain rfl | hne := X.eq_empty_or_nonempty
  · rw [empty_union, image_empty, empty_union, h.preimage_eq_of_subset_closure rfl.subset]
  have hrw (x) (hi : x ∈ X) : M.closure ({x} ∪ C) = M.closure ((f '' {x}) ∪ C) := by
    simp [singleton_union, h.closure_eq_closure x]
  rw [← biUnion_of_singleton X, biUnion_distrib_union _ hne,
    ← closure_biUnion_closure_eq_closure_biUnion, iUnion₂_congr hrw,
    closure_biUnion_closure_eq_closure_biUnion, ← biUnion_distrib_union _ hne,
    ← image_iUnion₂, biUnion_of_singleton]
  simp only [Set.ext_iff, mem_diff, mem_preimage, and_congr_left_iff]
  refine fun x hxC ↦ ?_
  refine ⟨fun hxcl ↦ ?_, fun hxcl ↦ ?_⟩
  · rw [← closure_insert_eq_of_mem_closure hxcl, ← union_insert, ← closure_union_closure_right_eq,
      h.closure_eq_closure, closure_union_closure_right_eq]
    exact mem_closure_of_mem' _ (by simp) <| h.apply_mem_ground_iff.2 <| by grind
  rw [← closure_insert_eq_of_mem_closure hxcl, ← union_insert, ← closure_union_closure_right_eq,
    ← h.closure_eq_closure, closure_union_closure_right_eq]
  exact mem_closure_of_mem' _ (by simp) <| h.apply_mem_ground_iff.1 <| by grind

/-- If `f` is a shift by a set `C`, then `M.comap f` is a perturbation of `M`
by a function of the rank of `C`.
Here, `M.comap f` is the matroid obtained from `M` by replacing each `x` with `f x`,
and the hypothesis implies that `x` and `f x` are always parallel in `M ／ C`.  -/
lemma IsShift.isPerturbation_comap (h : M.IsShift C f) :
    M.IsPerturbation (M.comap f) (2 * M.eRk C) := by
  refine (M.isPerturbation_of_contract_eq_contract ?_ h.comap_contract_eq).mono ?_
  · rw [comap_ground_eq, h.preimage_eq]
  rw [eRk_comap, h.eqOn.image_eq, image_id, two_mul]

/-- If `f` is a shift by a set `C`, and `L` is a set spanned by `C`,
then `M` has bounded (by a function of `M.eRk C`) perturbation distance
from the matroid `(M.comap f).loopify L`. -/
lemma IsShift.isPerturbation_loopify_comap (h : M.IsShift C f) {L : Set α} (hL : L ⊆ M.closure C) :
    M.IsPerturbation ((M.comap f).loopify L) (6 * M.eRk C) := by
  refine h.isPerturbation_comap.trans_le (isPerturbation_loopify _ _) ?_
  grw [eRk_comap, hL, h.eqOn_closure.image_eq_self, eRk_closure_eq, ← add_mul]
  rfl

end shift

section uniform



-- lemma foo (a b : ℕ) (X : Set α) (hxB : b + ∑ i < b, ENat.choose a i ≤ X.encard)
--     (U : (unifOn X (a + 1)).ModularCut) (hU : U ≠ ⊤) :
--     ∃ Y ⊆ X, Y.encard = b ∧ ((unifOn X (a + 1)).projectBy U ↾ Y).IsFiniteRankUniform a := by
--   let G := unifOn X (a + 1)
--   let M := G.projectBy U

--   sorry


end uniform
