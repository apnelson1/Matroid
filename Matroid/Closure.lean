import Mathlib.Data.Matroid.Map

open Set
namespace Matroid

variable {α ι : Type*} {M : Matroid α} {F I J X Y B C R : Set α} {e f x y : α}

/-- A flat is a maximal set having a given basis  -/
def Flat (M : Matroid α) (F : Set α) : Prop :=
  (∀ ⦃I X⦄, M.Basis I F → M.Basis I X → X ⊆ F) ∧ F ⊆ M.E

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma Flat.subset_ground (hF : M.Flat F) : F ⊆ M.E :=
  hF.2

@[simp] lemma ground_flat (M : Matroid α) : M.Flat M.E :=
  ⟨fun _ _ _ ↦ Basis.subset_ground, Subset.rfl⟩

/-- The closure of a subset of the ground set is the intersection of the flats containing it.
  A set `X` that doesn't satisfy `X ⊆ M.E` has the junk value `M.cl X := M.cl (X ∩ M.E)`. -/
def cl (M : Matroid α) (X : Set α) : Set α := ⋂₀ {F | M.Flat F ∧ X ∩ M.E ⊆ F}

lemma cl_def (M : Matroid α) (X : Set α) : M.cl X = ⋂₀ {F | M.Flat F ∧ X ∩ M.E ⊆ F} := rfl

lemma cl_def' (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    M.cl X = ⋂₀ {F | M.Flat F ∧ X ⊆ F} := by
  nth_rw 2 [← inter_eq_self_of_subset_left hX]; rfl

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma cl_subset_ground (M : Matroid α) (X : Set α) : M.cl X ⊆ M.E :=
  sInter_subset_of_mem ⟨M.ground_flat, inter_subset_right⟩

lemma ground_subset_cl_iff : M.E ⊆ M.cl X ↔ M.cl X = M.E := by
  simp [M.cl_subset_ground X, subset_antisymm_iff]

lemma cl_eq_sInter_of_subset (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    M.cl X = ⋂₀ {F : Set α | M.Flat F ∧ X ⊆ F} :=
  by rw [cl, inter_eq_self_of_subset_left hX]

@[simp] lemma cl_inter_ground (M : Matroid α) (X : Set α) : M.cl (X ∩ M.E) = M.cl X := by
  simp_rw [cl_def, inter_assoc, inter_self]

lemma inter_ground_subset_cl (M : Matroid α) (X : Set α) : X ∩ M.E ⊆ M.cl X := by
  simp_rw [cl_def, subset_sInter_iff]; aesop

lemma mem_cl_iff_forall_mem_flat (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    e ∈ M.cl X ↔ ∀ F, M.Flat F → X ⊆ F → e ∈ F := by
  simp_rw [cl_eq_sInter_of_subset X, mem_sInter, mem_setOf, and_imp]

lemma subset_cl_iff_forall_subset_flat (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    Y ⊆ M.cl X ↔ ∀ F, M.Flat F → X ⊆ F → Y ⊆ F := by
  simp_rw [cl_eq_sInter_of_subset X, subset_sInter_iff, mem_setOf, and_imp]

lemma subset_cl (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    X ⊆ M.cl X := by
  rw [cl_eq_sInter_of_subset X, subset_sInter_iff]; simp

lemma Flat.cl (hF : M.Flat F) : M.cl F = F :=
  (sInter_subset_of_mem (by simpa)).antisymm (M.subset_cl F)

@[simp] lemma cl_ground (M : Matroid α) : M.cl M.E = M.E :=
  (M.cl_subset_ground M.E).antisymm (M.subset_cl M.E)

@[simp] lemma cl_univ (M : Matroid α) : M.cl univ = M.E := by
  rw [← cl_inter_ground, univ_inter, cl_ground]

lemma cl_subset_cl (M : Matroid α) (h : X ⊆ Y) : M.cl X ⊆ M.cl Y :=
  subset_sInter (fun _ ⟨hF, hssF⟩ ↦
    sInter_subset_of_mem ⟨hF, subset_trans (inter_subset_inter_left _ h) hssF⟩)

lemma cl_mono (M : Matroid α) : Monotone M.cl :=
  fun _ _ ↦ M.cl_subset_cl

@[simp] lemma cl_cl (M : Matroid α) (X : Set α) : M.cl (M.cl X) = M.cl X :=
  (M.subset_cl _).antisymm' (subset_sInter
    (fun F hF ↦ (cl_subset_cl _  (sInter_subset_of_mem hF)).trans hF.1.cl.subset))

lemma cl_subset_cl_of_subset_cl (hXY : X ⊆ M.cl Y) : M.cl X ⊆ M.cl Y :=
    (M.cl_subset_cl hXY).trans_eq (M.cl_cl Y)

lemma cl_subset_cl_iff_subset_cl (hX : X ⊆ M.E := by aesop_mat) :
    M.cl X ⊆ M.cl Y ↔ X ⊆ M.cl Y :=
  ⟨(M.subset_cl X).trans, cl_subset_cl_of_subset_cl⟩

lemma subset_cl_of_subset (M : Matroid α) (hXY : X ⊆ Y) (hY : Y ⊆ M.E := by aesop_mat) :
    X ⊆ M.cl Y :=
  hXY.trans (M.subset_cl Y)

lemma subset_cl_of_subset' (M : Matroid α) (hXY : X ⊆ Y) (hX : X ⊆ M.E := by aesop_mat) :
    X ⊆ M.cl Y := by
  rw [← cl_inter_ground]; exact M.subset_cl_of_subset (subset_inter hXY hX)

lemma exists_of_cl_ssubset (hXY : M.cl X ⊂ M.cl Y) : ∃ e ∈ Y, e ∉ M.cl X := by
  by_contra! hcon
  exact hXY.not_subset (M.cl_subset_cl_of_subset_cl hcon)

lemma mem_cl_of_mem (M : Matroid α) (h : e ∈ X) (hX : X ⊆ M.E := by aesop_mat) :
    e ∈ M.cl X :=
  (M.subset_cl X) h

lemma mem_cl_of_mem' (M : Matroid α) (heX : e ∈ X) (h : e ∈ M.E := by aesop_mat) :
    e ∈ M.cl X := by
  rw [← cl_inter_ground]; exact M.mem_cl_of_mem ⟨heX, h⟩

lemma not_mem_of_mem_diff_cl (he : e ∈ M.E \ M.cl X) : e ∉ X :=
  fun heX ↦ he.2 <| M.mem_cl_of_mem' heX he.1

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma mem_ground_of_mem_cl (he : e ∈ M.cl X) : e ∈ M.E := (M.cl_subset_ground _) he

lemma cl_iUnion_cl_eq_cl_iUnion (M : Matroid α) (Xs : ι → Set α) :
    M.cl (⋃ i, M.cl (Xs i)) = M.cl (⋃ i, Xs i) := by
  refine (M.cl_subset_cl_of_subset_cl
    (iUnion_subset (fun i ↦ M.cl_subset_cl (subset_iUnion _ _)))).antisymm ?_
  rw [← cl_inter_ground, iUnion_inter]
  refine' M.cl_subset_cl (iUnion_subset (fun i ↦ (M.subset_cl _).trans _))
  rw [cl_inter_ground]
  exact subset_iUnion (fun i ↦ M.cl (Xs i)) i

lemma cl_iUnion_congr {ι : Type*} (Xs Ys : ι → Set α) (h : ∀ i, M.cl (Xs i) = M.cl (Ys i)) :
    M.cl (⋃ i, Xs i) = M.cl (⋃ i, Ys i) := by
  rw [← M.cl_iUnion_cl_eq_cl_iUnion]
  simp [h, M.cl_iUnion_cl_eq_cl_iUnion]

lemma cl_biUnion_cl_eq_cl_sUnion (M : Matroid α) (Xs : Set (Set α)) :
    M.cl (⋃ X ∈ Xs, M.cl X) = M.cl (⋃₀ Xs) := by
  rw [sUnion_eq_iUnion, biUnion_eq_iUnion, cl_iUnion_cl_eq_cl_iUnion]

lemma cl_biUnion_cl_eq_cl_biUnion (M : Matroid α) (Xs : ι → Set α) (A : Set ι) :
    M.cl (⋃ i ∈ A, M.cl (Xs i)) = M.cl (⋃ i ∈ A, Xs i) := by
  rw [biUnion_eq_iUnion, M.cl_iUnion_cl_eq_cl_iUnion, biUnion_eq_iUnion]

lemma cl_biUnion_congr (M : Matroid α) (Xs Ys : ι → Set α) (A : Set ι)
    (h : ∀ i ∈ A, M.cl (Xs i) = M.cl (Ys i)) :
    M.cl (⋃ i ∈ A, Xs i) = M.cl (⋃ i ∈ A, Ys i) := by
  rw [← cl_biUnion_cl_eq_cl_biUnion, iUnion₂_congr h, cl_biUnion_cl_eq_cl_biUnion]

@[simp] lemma cl_cl_union_cl_eq_cl_union (M : Matroid α) (X Y : Set α) :
    M.cl (M.cl X ∪ M.cl Y) = M.cl (X ∪ Y) := by
  rw [eq_comm, union_eq_iUnion, ← cl_iUnion_cl_eq_cl_iUnion, union_eq_iUnion]
  simp_rw [Bool.cond_eq_ite, apply_ite]

@[simp] lemma cl_union_cl_right_eq (M : Matroid α) (X Y : Set α) :
    M.cl (X ∪ M.cl Y) = M.cl (X ∪ Y) := by
  rw [← cl_cl_union_cl_eq_cl_union, cl_cl, cl_cl_union_cl_eq_cl_union]

@[simp] lemma cl_union_cl_left_eq (M : Matroid α) (X Y : Set α) :
    M.cl (M.cl X ∪ Y) = M.cl (X ∪ Y) := by
  rw [← cl_cl_union_cl_eq_cl_union, cl_cl, cl_cl_union_cl_eq_cl_union]

@[simp] lemma cl_insert_cl_eq_cl_insert (M : Matroid α) (e : α) (X : Set α) :
    M.cl (insert e (M.cl X)) = M.cl (insert e X) := by
  simp_rw [← singleton_union, cl_union_cl_right_eq]

@[simp] lemma cl_union_cl_empty_eq (M : Matroid α) (X : Set α) :
    M.cl X ∪ M.cl ∅ = M.cl X :=
  union_eq_self_of_subset_right (M.cl_subset_cl (empty_subset _))

@[simp] lemma cl_empty_union_cl_eq (M : Matroid α) (X : Set α) :
    M.cl ∅ ∪ M.cl X = M.cl X :=
  union_eq_self_of_subset_left (M.cl_subset_cl (empty_subset _))

lemma cl_insert_eq_of_mem_cl (he : e ∈ M.cl X) : M.cl (insert e X) = M.cl X := by
  rw [← cl_insert_cl_eq_cl_insert, insert_eq_of_mem he, cl_cl]

lemma mem_cl_self (M : Matroid α) (e : α) (he : e ∈ M.E := by aesop_mat) : e ∈ M.cl {e} :=
  mem_cl_of_mem' _ rfl


-- Independence and Bases

lemma Indep.cl_eq_setOf_basis_insert (hI : M.Indep I) : M.cl I = {x | M.Basis I (insert x I)} := by
  set F := {x | M.Basis I (insert x I)}
  have hIF : M.Basis I F := hI.basis_setOf_insert_basis

  have hF : M.Flat F := by
    refine' ⟨fun J X hJF hJX e heX ↦ (_ : M.Basis _ _), hIF.subset_ground⟩
    exact (hIF.basis_of_basis_of_subset_of_subset (hJX.basis_union hJF) hJF.subset
      (hIF.subset.trans subset_union_right)).basis_subset (subset_insert _ _)
      (insert_subset (Or.inl heX) (hIF.subset.trans subset_union_right))

  rw [subset_antisymm_iff, cl_def, subset_sInter_iff, and_iff_right (sInter_subset_of_mem _)]
  · rintro F' ⟨hF', hIF'⟩ e (he : M.Basis I (insert e I))
    rw [inter_eq_left.mpr (hIF.subset.trans hIF.subset_ground)] at hIF'
    obtain ⟨J, hJ, hIJ⟩ := hI.subset_basis_of_subset hIF' hF'.2
    exact (hF'.1 hJ (he.basis_union_of_subset hJ.indep hIJ)) (Or.inr (mem_insert _ _))
  exact ⟨hF, inter_subset_left.trans hIF.subset⟩

lemma Indep.insert_basis_iff_mem_cl (hI : M.Indep I) : M.Basis I (insert e I) ↔ e ∈ M.cl I := by
  rw [hI.cl_eq_setOf_basis_insert, mem_setOf]

lemma Indep.basis_cl (hI : M.Indep I) : M.Basis I (M.cl I) := by
  rw [hI.cl_eq_setOf_basis_insert]; exact hI.basis_setOf_insert_basis

lemma Basis.cl_eq_cl (h : M.Basis I X) : M.cl I = M.cl X := by
  refine' subset_antisymm (M.cl_subset_cl h.subset) _
  rw [← M.cl_cl I, h.indep.cl_eq_setOf_basis_insert]
  exact M.cl_subset_cl fun e he ↦ (h.basis_subset (subset_insert _ _) (insert_subset he h.subset))

lemma Basis.cl_eq_right (h : M.Basis I (M.cl X)) : M.cl I = M.cl X :=
  M.cl_cl X ▸ h.cl_eq_cl

lemma Basis'.cl_eq_cl (h : M.Basis' I X) : M.cl I = M.cl X := by
  rw [← cl_inter_ground _ X, h.basis_inter_ground.cl_eq_cl]

lemma Basis.subset_cl (h : M.Basis I X) : X ⊆ M.cl I := by
  rw [← cl_subset_cl_iff_subset_cl, h.cl_eq_cl]

lemma Basis'.basis_cl_right (h : M.Basis' I X) : M.Basis I (M.cl X) := by
  rw [← h.cl_eq_cl]; exact h.indep.basis_cl

lemma Basis.basis_cl_right (h : M.Basis I X) : M.Basis I (M.cl X) :=
  h.basis'.basis_cl_right

lemma Indep.mem_cl_iff (hI : M.Indep I) :
    x ∈ M.cl I ↔ M.Dep (insert x I) ∨ x ∈ I := by
  rwa [hI.cl_eq_setOf_basis_insert, mem_setOf, basis_insert_iff]

lemma Indep.mem_cl_iff' (hI : M.Indep I) :
    x ∈ M.cl I ↔ x ∈ M.E ∧ (M.Indep (insert x I) → x ∈ I) := by
  rw [hI.mem_cl_iff, dep_iff, insert_subset_iff, and_iff_left hI.subset_ground,
    imp_iff_not_or]
  have := hI.subset_ground
  aesop

lemma Indep.insert_dep_iff (hI : M.Indep I) : M.Dep (insert e I) ↔ e ∈ M.cl I \ I := by
  rw [mem_diff, hI.mem_cl_iff, or_and_right, and_not_self_iff, or_false,
    iff_self_and, imp_not_comm]
  intro heI; rw [insert_eq_of_mem heI]; exact hI.not_dep

lemma Indep.mem_cl_iff_of_not_mem (hI : M.Indep I) (heI : e ∉ I) :
    e ∈ M.cl I ↔ M.Dep (insert e I) := by
  rw [hI.insert_dep_iff, mem_diff, and_iff_left heI]

lemma Indep.not_mem_cl_iff (hI : M.Indep I) (he : e ∈ M.E := by aesop_mat) :
    e ∉ M.cl I ↔ M.Indep (insert e I) ∧ e ∉ I := by
  rw [hI.mem_cl_iff, dep_iff, insert_subset_iff, and_iff_right he,
    and_iff_left hI.subset_ground]; tauto

lemma Indep.not_mem_cl_iff_of_not_mem (hI : M.Indep I) (heI : e ∉ I)
    (he : e ∈ M.E := by aesop_mat) : e ∉ M.cl I ↔ M.Indep (insert e I) := by
  rw [hI.not_mem_cl_iff, and_iff_left heI]

lemma Indep.insert_indep_iff_of_not_mem (hI : M.Indep I) (heI : e ∉ I) :
    M.Indep (insert e I) ↔ e ∈ M.E \ M.cl I := by
  rw [mem_diff, hI.mem_cl_iff_of_not_mem heI, dep_iff, not_and, not_imp_not, insert_subset_iff,
    and_iff_left hI.subset_ground]
  exact ⟨fun h ↦ ⟨h.subset_ground (mem_insert e I), fun _ ↦ h⟩, fun h ↦ h.2 h.1⟩

lemma Indep.insert_indep_iff (hI : M.Indep I) :
    M.Indep (insert e I) ↔ e ∈ M.E \ M.cl I ∨ e ∈ I := by
  obtain (h | h) := em (e ∈ I)
  · simp_rw [insert_eq_of_mem h, iff_true_intro hI, true_iff, iff_true_intro h, or_true]
  rw [hI.insert_indep_iff_of_not_mem h, or_iff_left h]

lemma insert_indep_iff : M.Indep (insert e I) ↔ M.Indep I ∧ (e ∉ I → e ∈ M.E \ M.cl I) := by
  by_cases hI : M.Indep I
  · rw [hI.insert_indep_iff, and_iff_right hI, or_iff_not_imp_right]
  simp [hI, show ¬ M.Indep (insert e I) from fun h ↦ hI <| h.subset <| subset_insert _ _]

/-- This can be used for rewriting if the LHS is inside a quantifier where `f = e` is not known.-/
lemma Indep.insert_diff_indep_iff (hI : M.Indep (I \ {e})) (heI : e ∈ I) :
    M.Indep (insert f I \ {e}) ↔ f ∈ M.E \ M.cl (I \ {e}) ∨ f ∈ I := by
  obtain (rfl | hne) := eq_or_ne e f
  · simp [hI, heI]
  rw [← insert_diff_singleton_comm hne.symm, hI.insert_indep_iff, mem_diff_singleton,
    and_iff_left hne.symm]

lemma Indep.basis_of_subset_of_subset_cl (hI : M.Indep I) (hIX : I ⊆ X) (hXI : X ⊆ M.cl I) :
    M.Basis I X :=
  hI.basis_cl.basis_subset hIX hXI

lemma basis_iff_indep_subset_cl : M.Basis I X ↔ M.Indep I ∧ I ⊆ X ∧ X ⊆ M.cl I :=
  ⟨fun h ↦ ⟨h.indep, h.subset, h.subset_cl⟩, fun h ↦ h.1.basis_of_subset_of_subset_cl h.2.1 h.2.2⟩

lemma Indep.base_of_ground_subset_cl (hI : M.Indep I) (h : M.E ⊆ M.cl I) : M.Base I := by
  rw [← basis_ground_iff]; exact hI.basis_of_subset_of_subset_cl hI.subset_ground h

lemma Base.cl_eq (hB : M.Base B) : M.cl B = M.E := by
  rw [← basis_ground_iff] at hB; rw [hB.cl_eq_cl, cl_ground]

lemma Base.mem_cl (hB : M.Base B) (e : α) (he : e ∈ M.E := by aesop_mat) : e ∈ M.cl B := by
  rwa [hB.cl_eq]

lemma Base.cl_of_superset (hB : M.Base B) (hBX : B ⊆ X) : M.cl X = M.E :=
  subset_antisymm (M.cl_subset_ground _) (by rw [← hB.cl_eq]; exact M.cl_subset_cl hBX)

lemma base_iff_indep_cl_eq : M.Base B ↔ M.Indep B ∧ M.cl B = M.E := by
  rw [← basis_ground_iff, basis_iff_indep_subset_cl, and_congr_right_iff]
  exact fun hI ↦ ⟨fun h ↦ (M.cl_subset_ground _).antisymm h.2,
    fun h ↦ ⟨(M.subset_cl B).trans_eq h, h.symm.subset⟩⟩

lemma Indep.base_iff_ground_subset_cl (hI : M.Indep I) : M.Base I ↔ M.E ⊆ M.cl I :=
  ⟨fun h ↦ by rw [h.cl_eq], hI.base_of_ground_subset_cl⟩

lemma Indep.cl_inter_eq_self_of_subset (hI : M.Indep I) (hJI : J ⊆ I) : M.cl J ∩ I = J := by
  have hJ := hI.subset hJI
  rw [subset_antisymm_iff, and_iff_left (subset_inter (M.subset_cl _) hJI)]
  rintro e ⟨heJ, heI⟩
  exact hJ.basis_cl.mem_of_insert_indep heJ (hI.subset (insert_subset heI hJI))

lemma Indep.cl_sInter_eq_biInter_cl_of_forall_subset {Js : Set (Set α)} (hI : M.Indep I)
    (hne : Js.Nonempty) (hIs : ∀ J ∈ Js, J ⊆ I) : M.cl (⋂₀ Js) = (⋂ J ∈ Js, M.cl J)  := by
  rw [subset_antisymm_iff, subset_iInter₂_iff]
  have hiX : ⋂₀ Js ⊆ I := (sInter_subset_of_mem hne.some_mem).trans (hIs _ hne.some_mem)
  have hiI := hI.subset hiX
  refine' ⟨ fun X hX ↦ M.cl_subset_cl (sInter_subset_of_mem hX), fun e he ↦ by_contra fun he' ↦ _⟩
  rw [mem_iInter₂] at he
  have heEI : e ∈ M.E \ I := by
    refine' ⟨M.cl_subset_ground _ (he _ hne.some_mem), fun heI ↦ he' _⟩
    refine' mem_cl_of_mem _ (fun X hX' ↦ _) hiI.subset_ground
    rw [← hI.cl_inter_eq_self_of_subset (hIs X hX')]
    exact ⟨he X hX', heI⟩

  rw [hiI.not_mem_cl_iff_of_not_mem (not_mem_subset hiX heEI.2)] at he'
  obtain ⟨J, hJI, heJ⟩ := he'.subset_basis_of_subset (insert_subset_insert hiX)
    (insert_subset heEI.1 hI.subset_ground)

  have hIb : M.Basis I (insert e I) := by
    rw [hI.insert_basis_iff_mem_cl]; exact (M.cl_subset_cl (hIs _ hne.some_mem)) (he _ hne.some_mem)

  obtain ⟨f, hfIJ, hfb⟩ :=  hJI.exchange hIb ⟨heJ (mem_insert e _), heEI.2⟩
  obtain rfl := hI.eq_of_basis (hfb.basis_subset (insert_subset hfIJ.1
    (by (rw [diff_subset_iff, singleton_union]; exact hJI.subset))) (subset_insert _ _))

  refine' hfIJ.2 (heJ (mem_insert_of_mem _ fun X hX' ↦ by_contra fun hfX ↦ _))

  obtain (hd | heX) := ((hI.subset (hIs X hX')).mem_cl_iff).mp (he _ hX')
  · refine' (hJI.indep.subset (insert_subset (heJ (mem_insert _ _)) _)).not_dep hd
    specialize hIs _ hX'
    rw [← singleton_union, ← diff_subset_iff, diff_singleton_eq_self hfX] at hIs
    exact hIs.trans diff_subset
  exact heEI.2 (hIs _ hX' heX)

lemma cl_iInter_eq_iInter_cl_of_iUnion_indep {ι : Type*} [hι : Nonempty ι]
    (Is : ι → Set α) (h : M.Indep (⋃ i, Is i)) :  M.cl (⋂ i, Is i) = (⋂ i, M.cl (Is i)) := by
  convert h.cl_sInter_eq_biInter_cl_of_forall_subset (range_nonempty Is) (by simp [subset_iUnion])
  simp

lemma cl_sInter_eq_biInter_cl_of_sUnion_indep (Is : Set (Set α)) (hIs : Is.Nonempty)
    (h : M.Indep (⋃₀ Is)) :  M.cl (⋂₀ Is) = (⋂ I ∈ Is, M.cl I) :=
  h.cl_sInter_eq_biInter_cl_of_forall_subset hIs (fun _ ↦ subset_sUnion_of_mem)

lemma cl_biInter_eq_biInter_cl_of_biUnion_indep {ι : Type*} {A : Set ι} (hA : A.Nonempty)
    {I : ι → Set α} (h : M.Indep (⋃ i ∈ A, I i)) : M.cl (⋂ i ∈ A, I i) = ⋂ i ∈ A, M.cl (I i) := by
  have := hA.coe_sort
  convert cl_iInter_eq_iInter_cl_of_iUnion_indep (ι := A) (Is := fun i ↦ I i) (by simpa) <;> simp

lemma Indep.cl_iInter_eq_biInter_cl_of_forall_subset {ι : Type*} [hι : Nonempty ι] {Js : ι → Set α}
    (hI : M.Indep I) (hJs : ∀ i, Js i ⊆ I) : M.cl (⋂ i, Js i) = ⋂ i, M.cl (Js i) :=
  cl_iInter_eq_iInter_cl_of_iUnion_indep _ (hI.subset <| by simpa)

lemma Indep.cl_inter_eq_inter_cl (h : M.Indep (I ∪ J)) : M.cl (I ∩ J) = M.cl I ∩ M.cl J := by
  rw [inter_eq_iInter, cl_iInter_eq_iInter_cl_of_iUnion_indep, inter_eq_iInter]
  · exact iInter_congr (by simp)
  rwa [← union_eq_iUnion]

lemma basis_iff_basis_cl_of_subset (hIX : I ⊆ X) (hX : X ⊆ M.E := by aesop_mat) :
    M.Basis I X ↔ M.Basis I (M.cl X) :=
  ⟨fun h ↦ h.basis_cl_right, fun h ↦ h.basis_subset hIX (M.subset_cl X hX)⟩

lemma basis_iff_basis_cl_of_subset' (hIX : I ⊆ X) : M.Basis I X ↔ X ⊆ M.E ∧ M.Basis I (M.cl X) :=
  ⟨fun h ↦ ⟨h.subset_ground, h.basis_cl_right⟩, fun h ↦ h.2.basis_subset hIX (M.subset_cl X h.1)⟩

lemma basis'_iff_basis_cl : M.Basis' I X ↔ M.Basis I (M.cl X) ∧ I ⊆ X := by
  rw [← cl_inter_ground, basis'_iff_basis_inter_ground]
  exact ⟨fun h ↦ ⟨h.basis_cl_right, h.subset.trans inter_subset_left⟩,
    fun h ↦ h.1.basis_subset (subset_inter h.2 h.1.indep.subset_ground) (M.subset_cl _)⟩

lemma exists_basis_inter_ground_basis_cl (M : Matroid α) (X : Set α) :
    ∃ I, M.Basis I (X ∩ M.E) ∧ M.Basis I (M.cl X) := by
  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E)
  have hI' := hI.basis_cl_right; rw [cl_inter_ground] at hI'
  exact ⟨_, hI, hI'⟩

lemma Basis.basis_of_cl_eq_cl (hI : M.Basis I X) (hY : I ⊆ Y) (h : M.cl X = M.cl Y)
    (hYE : Y ⊆ M.E := by aesop_mat) : M.Basis I Y := by
  refine' hI.indep.basis_of_subset_of_subset_cl hY _
  rw [hI.cl_eq_cl, h]
  exact M.subset_cl Y

lemma basis_union_iff_indep_cl : M.Basis I (I ∪ X) ↔ M.Indep I ∧ X ⊆ M.cl I :=
  ⟨fun h ↦ ⟨h.indep, subset_union_right.trans h.subset_cl⟩, fun ⟨hI, hXI⟩ ↦
    hI.basis_cl.basis_subset subset_union_left (union_subset (M.subset_cl I) hXI)⟩

lemma basis_iff_indep_cl : M.Basis I X ↔ M.Indep I ∧ X ⊆ M.cl I ∧ I ⊆ X :=
  ⟨fun h ↦ ⟨h.indep, h.subset_cl, h.subset⟩, fun h ↦
    (basis_union_iff_indep_cl.mpr ⟨h.1, h.2.1⟩).basis_subset h.2.2 subset_union_right⟩

lemma Basis.eq_of_cl_subset (hI : M.Basis I X) (hJI : J ⊆ I) (hJ : X ⊆ M.cl J) : J = I := by
  rw [← hI.indep.cl_inter_eq_self_of_subset hJI, inter_eq_self_of_subset_right]
  exact hI.subset.trans hJ

@[simp] lemma empty_basis_iff : M.Basis ∅ X ↔ X ⊆ M.cl ∅ := by
  rw [basis_iff_indep_cl, and_iff_right M.empty_indep, and_iff_left (empty_subset _)]

-- Sets

lemma mem_cl_insert (he : e ∉ M.cl X) (hef : e ∈ M.cl (insert f X)) : f ∈ M.cl (insert e X) := by
  rw [← cl_inter_ground] at *
  have hfE : f ∈ M.E := by
    by_contra! hfE; rw [insert_inter_of_not_mem hfE] at hef; exact he hef
  have heE : e ∈ M.E := (M.cl_subset_ground _) hef
  rw [insert_inter_of_mem hfE] at hef; rw [insert_inter_of_mem heE]

  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E)
  rw [← hI.cl_eq_cl, hI.indep.not_mem_cl_iff] at he
  rw [← cl_insert_cl_eq_cl_insert, ← hI.cl_eq_cl, cl_insert_cl_eq_cl_insert, he.1.mem_cl_iff] at *
  rw [or_iff_not_imp_left, dep_iff, insert_comm,
    and_iff_left (insert_subset heE (insert_subset hfE hI.indep.subset_ground)), not_not]
  intro h
  rw [(h.subset (subset_insert _ _)).mem_cl_iff, or_iff_right (h.not_dep), mem_insert_iff,
    or_iff_left he.2] at hef
  subst hef; apply mem_insert

lemma cl_exchange (he : e ∈ M.cl (insert f X) \ M.cl X) : f ∈ M.cl (insert e X) \ M.cl X :=
  ⟨mem_cl_insert he.2 he.1, fun hf ↦
    by rwa [cl_insert_eq_of_mem_cl hf, diff_self, iff_false_intro (not_mem_empty _)] at he⟩

lemma cl_exchange_iff : e ∈ M.cl (insert f X) \ M.cl X ↔ f ∈ M.cl (insert e X) \ M.cl X :=
  ⟨cl_exchange, cl_exchange⟩

lemma cl_insert_eq_cl_insert_of_mem (he : e ∈ M.cl (insert f X) \ M.cl X) :
    M.cl (insert e X) = M.cl (insert f X) := by
  have hf := cl_exchange he
  rw [eq_comm, ← cl_cl, ← insert_eq_of_mem he.1, cl_insert_cl_eq_cl_insert, insert_comm, ← cl_cl,
    ← cl_insert_cl_eq_cl_insert, insert_eq_of_mem hf.1, cl_cl, cl_cl]

lemma cl_diff_singleton_eq_cl (h : e ∈ M.cl (X \ {e})) : M.cl (X \ {e}) = M.cl X := by
  refine' (em (e ∈ X)).elim (fun h' ↦ _) (fun h' ↦ by rw [diff_singleton_eq_self h'])
  convert M.cl_insert_cl_eq_cl_insert e (X \ {e}) using 1
  · rw [insert_eq_of_mem h, cl_cl]
  rw [insert_diff_singleton, insert_eq_of_mem h']

lemma mem_cl_diff_singleton_iff_cl (he : e ∈ X) (heE : e ∈ M.E := by aesop_mat) :
    e ∈ M.cl (X \ {e}) ↔ M.cl (X \ {e}) = M.cl X :=
  ⟨cl_diff_singleton_eq_cl, fun h ↦ by rw [h]; exact M.mem_cl_of_mem' he⟩

lemma indep_iff_not_mem_cl_diff_forall (hI : I ⊆ M.E := by aesop_mat) :
    M.Indep I ↔ ∀ e ∈ I, e ∉ M.cl (I \ {e}) := by
  use fun h e heI he ↦ ((h.cl_inter_eq_self_of_subset diff_subset).subset ⟨he, heI⟩).2 rfl
  intro h
  obtain ⟨J, hJ⟩ := M.exists_basis I
  convert hJ.indep
  refine' hJ.subset.antisymm' (fun e he ↦ by_contra fun heJ ↦ h _ he _)
  exact mem_of_mem_of_subset
    (hJ.subset_cl he) (M.cl_subset_cl (subset_diff_singleton hJ.subset heJ))

lemma indep_iff_not_mem_cl_diff_forall' : M.Indep I ↔ I ⊆ M.E ∧ ∀ e ∈ I, e ∉ M.cl (I \ {e}) :=
  ⟨fun h ↦ ⟨h.subset_ground, (indep_iff_not_mem_cl_diff_forall h.subset_ground).mp h⟩, fun h ↦
    (indep_iff_not_mem_cl_diff_forall h.1).mpr h.2⟩

lemma Indep.not_mem_cl_diff_of_mem (hI : M.Indep I) (he : e ∈ I) : e ∉ M.cl (I \ {e}) :=
  (indep_iff_not_mem_cl_diff_forall'.1 hI).2 e he

lemma indep_iff_cl_diff_ne_forall : M.Indep I ↔ ∀ e ∈ I, M.cl (I \ {e}) ≠ M.cl I := by
  rw [indep_iff_not_mem_cl_diff_forall']
  refine' ⟨fun ⟨hIE, h⟩ e heI h_eq ↦ h e heI (h_eq.symm.subset (M.mem_cl_of_mem heI)),
    fun h ↦ ⟨fun e heI ↦ by_contra fun heE ↦ h e heI _,fun e heI hin ↦ h e heI
      (by rw [cl_diff_singleton_eq_cl hin])⟩⟩
  rw [← cl_inter_ground, inter_comm, inter_diff_distrib_left,
    inter_singleton_eq_empty.mpr heE, diff_empty, inter_comm, cl_inter_ground]

lemma Indep.cl_diff_singleton_ssubset (hI : M.Indep I) (he : e ∈ I) : M.cl (I \ {e}) ⊂ M.cl I :=
  ssubset_of_subset_of_ne (M.cl_mono diff_subset) (indep_iff_cl_diff_ne_forall.mp hI _ he)

lemma indep_iff_cl_ssubset_ssubset_forall (hI : I ⊆ M.E := by aesop_mat) :
    M.Indep I ↔ (∀ J, J ⊂ I → M.cl J ⊂ M.cl I) := by
  rw [indep_iff_not_mem_cl_diff_forall]
  refine' ⟨fun h J hJI ↦ (M.cl_subset_cl hJI.subset).ssubset_of_ne (fun h_eq ↦ _),
    fun h e heI hin ↦ _⟩
  · obtain ⟨e,heJ,h'⟩ := ssubset_iff_insert.1 hJI
    apply h e (h' (mem_insert _ _))
    have heI := M.mem_cl_of_mem (h' (mem_insert e J))
    rw [← h_eq] at heI
    refine' mem_of_mem_of_subset heI (M.cl_subset_cl _)
    rw [subset_diff, disjoint_singleton_right, and_iff_left heJ]
    exact (subset_insert _ _).trans h'
  refine' (h (I \ {e}) (diff_singleton_sSubset.2 heI)).ne _
  rw [← cl_cl, ← insert_eq_of_mem hin, cl_insert_cl_eq_cl_insert, insert_diff_singleton,
    insert_eq_of_mem heI]

lemma eq_of_cl_eq_cl_forall {M₁ M₂ : Matroid α} (h : ∀ X, M₁.cl X = M₂.cl X) : M₁ = M₂ :=
  eq_of_indep_iff_indep_forall (by simpa using h univ)
    (fun _ _ ↦ by simp_rw [indep_iff_cl_diff_ne_forall, h])

@[simp] lemma restrict_cl_eq' (M : Matroid α) (X R : Set α) :
    (M ↾ R).cl X = (M.cl (X ∩ R) ∩ R) ∪ (R \ M.E) := by
  rw [← cl_inter_ground, restrict_ground_eq]
  ext e
  obtain ⟨I, hI⟩ := (M ↾ R).exists_basis (X ∩ R)
  have hI' := (basis_restrict_iff'.mp hI).1
  rw [← hI.cl_eq_cl, ← M.cl_inter_ground (X ∩ R), ← hI'.cl_eq_cl, mem_union, mem_inter_iff,
    hI'.indep.mem_cl_iff, hI.indep.mem_cl_iff, restrict_dep_iff, insert_subset_iff,
    dep_iff, insert_subset_iff, and_iff_left hI'.indep.subset_ground, mem_diff,
    and_iff_left (show I ⊆ R from hI.indep.subset_ground)]
  have hIR : I ⊆ R := hI.indep.subset_ground
  by_cases he : e ∈ M.E; aesop
  simp only [iff_false_intro he, and_false, false_or, and_true, ← mem_inter_iff, ← mem_union,
    inter_eq_self_of_subset_left hIR, union_comm I, and_iff_right
      (show ¬M.Indep (insert e I) from fun hi ↦ he (hi.subset_ground (mem_insert _ _))),
    not_false_iff]

lemma restrict_cl_eq (M : Matroid α) (hXR : X ⊆ R) (hR : R ⊆ M.E := by aesop_mat) :
    (M ↾ R).cl X = M.cl X ∩ R := by
  rw [restrict_cl_eq', diff_eq_empty.mpr hR, union_empty, inter_eq_self_of_subset_left hXR]

@[simp] lemma comap_cl_eq {β : Type*} (M : Matroid β) (f : α → β) (X : Set α) :
    (M.comap f).cl X = f ⁻¹' M.cl (f '' X) := by
  obtain ⟨I, hI⟩ := (M.comap f).exists_basis' X
  obtain ⟨hI', hIinj, -⟩ := comap_basis'_iff.1 hI
  rw [← hI.cl_eq_cl]
  ext x
  obtain (hxE | hxE) := em' (f x ∈ M.E)
  · apply iff_of_false <;> exact (fun h ↦ hxE (by simpa using mem_ground_of_mem_cl h))

  by_cases hxI : x ∈ I
  · exact iff_of_true (mem_cl_of_mem _ hxI hI.indep.subset_ground)
      (mem_cl_of_mem' _ (mem_image_of_mem f (hI.subset hxI))
        (hI'.indep.subset_ground (mem_image_of_mem f hxI)))
  have hss : insert x I ⊆ (M.comap f).E := insert_subset hxE hI.indep.subset_ground
  rw [hI.indep.mem_cl_iff_of_not_mem hxI, ← not_indep_iff hss, comap_indep_iff,
    injOn_insert hxI, not_and, not_and, not_not, iff_true_intro hIinj, true_imp_iff]

  by_cases hxI' : f x ∈ f '' I
  · simp [hxI', hxE, mem_cl_of_mem' _ (hI'.subset hxI') hxE]

  rw [iff_false_intro hxI', imp_false, mem_preimage, image_insert_eq,
    hI'.indep.insert_indep_iff_of_not_mem hxI', mem_diff, and_iff_right hxE, not_not, hI'.cl_eq_cl]

@[simp] lemma map_cl_eq {β : Type*} (M : Matroid α) (f : α → β) (hf) (X : Set β) :
    (M.map f hf).cl X = f '' M.cl (f ⁻¹' X) := by
  suffices h' : ∀ X ⊆ f '' M.E, (M.map f hf).cl X = f '' (M.cl (f ⁻¹' X)) by
    convert h' (X ∩ f '' M.E) inter_subset_right using 1
    · rw [← cl_inter_ground]; rfl
    rw [preimage_inter, eq_comm, ← cl_inter_ground, inter_assoc, hf.preimage_image_inter Subset.rfl,
      cl_inter_ground]
  clear X
  intro X hX
  obtain ⟨I, hI⟩ := (M.map f hf).exists_basis X

  obtain ⟨I, X, hI', rfl, rfl⟩ := (map_basis_iff').1 hI

  rw [eq_comm, ← cl_inter_ground, hf.preimage_image_inter hI'.subset_ground,
    ← hI.cl_eq_cl, ← hI'.cl_eq_cl]
  ext e
  simp only [mem_image, hI.indep.mem_cl_iff', map_ground, map_indep_iff, forall_exists_index,
    and_imp, hI'.indep.mem_cl_iff']

  refine ⟨?_, ?_⟩
  . rintro ⟨e, ⟨heE, hind⟩, rfl⟩
    refine ⟨⟨e, heE, rfl⟩, fun J hJ hins ↦ ⟨e, hind ?_, rfl⟩⟩
    rw [← image_insert_eq,
      hf.image_eq_image_iff (insert_subset heE hI'.indep.subset_ground) hJ.subset_ground] at hins
    rwa [hins]
  rintro ⟨⟨x, hx, rfl⟩, h⟩
  refine ⟨x, ⟨hx, fun hind ↦ ?_⟩, rfl⟩
  obtain ⟨x', hx', h_eq⟩ := h _ hind (by rw [image_insert_eq])
  rwa [← hf (hI'.indep.subset_ground hx') hx h_eq]

section Spanning

variable {S T : Set α}

/-- A set is `spanning` in `M` if its closure is equal to `M.E`, or equivalently if it contains
  a base of `M`. -/
def Spanning (M : Matroid α) (S : Set α) := M.cl S = M.E ∧ S ⊆ M.E

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma Spanning.subset_ground (hS : M.Spanning S) : S ⊆ M.E :=
  hS.2

lemma Spanning.cl_eq (hS : M.Spanning S) : M.cl S = M.E :=
  hS.1

lemma spanning_iff_cl (hS : S ⊆ M.E := by aesop_mat) : M.Spanning S ↔ M.cl S = M.E :=
  ⟨And.left, fun h ↦ ⟨h, hS⟩⟩

lemma cl_spanning_iff (hS : S ⊆ M.E := by aesop_mat) : M.Spanning (M.cl S) ↔ M.Spanning S := by
  rw [spanning_iff_cl, cl_cl, ← spanning_iff_cl]

lemma spanning_iff_ground_subset_cl (hS : S ⊆ M.E := by aesop_mat) :
    M.Spanning S ↔ M.E ⊆ M.cl S := by
  rw [spanning_iff_cl, subset_antisymm_iff, and_iff_right (cl_subset_ground _ _)]

lemma not_spanning_iff_cl (hS : S ⊆ M.E := by aesop_mat) : ¬M.Spanning S ↔ M.cl S ⊂ M.E := by
  rw [spanning_iff_cl, ssubset_iff_subset_ne, iff_and_self, iff_true_intro (M.cl_subset_ground _)]
  exact fun _ ↦ trivial

lemma Spanning.superset (hS : M.Spanning S) (hST : S ⊆ T) (hT : T ⊆ M.E := by aesop_mat) :
    M.Spanning T :=
  ⟨(M.cl_subset_ground _).antisymm (by rw [← hS.cl_eq]; exact M.cl_subset_cl hST), hT⟩

lemma Spanning.cl_superset_eq (hS : M.Spanning S) (hST : S ⊆ T) : M.cl T = M.E := by
  rw [← cl_inter_ground, ← spanning_iff_cl]
  exact hS.superset (subset_inter hST hS.subset_ground)

lemma Spanning.union_left (hS : M.Spanning S) (hX : X ⊆ M.E := by aesop_mat) :
    M.Spanning (S ∪ X) :=
  hS.superset subset_union_left

lemma Spanning.union_right (hS : M.Spanning S) (hX : X ⊆ M.E := by aesop_mat) :
    M.Spanning (X ∪ S) :=
  hS.superset subset_union_right

lemma Base.spanning (hB : M.Base B) : M.Spanning B :=
  ⟨hB.cl_eq, hB.subset_ground⟩

lemma ground_spanning (M : Matroid α) : M.Spanning M.E :=
  ⟨M.cl_ground, rfl.subset⟩

lemma Base.superset_spanning (hB : M.Base B) (hBX : B ⊆ X) (hX : X ⊆ M.E := by aesop_mat) :
    M.Spanning X :=
  hB.spanning.superset hBX

lemma spanning_iff_superset_base' : M.Spanning S ↔ (∃ B, M.Base B ∧ B ⊆ S) ∧ S ⊆ M.E := by
  refine' ⟨fun h ↦ ⟨_, h.subset_ground⟩, fun ⟨⟨B, hB, hBS⟩, hSE⟩ ↦ hB.spanning.superset hBS⟩
  obtain ⟨B, hB⟩ := M.exists_basis S
  have hB' := hB.basis_cl_right
  rw [h.cl_eq, basis_ground_iff] at hB'
  exact ⟨B, hB', hB.subset⟩

lemma spanning_iff_superset_base (hS : S ⊆ M.E := by aesop_mat) :
    M.Spanning S ↔ ∃ B, M.Base B ∧ B ⊆ S := by
  rw [spanning_iff_superset_base', and_iff_left hS]

lemma Spanning.exists_base_subset (hS : M.Spanning S) : ∃ B, M.Base B ∧ B ⊆ S := by
  rwa [spanning_iff_superset_base] at hS

lemma coindep_iff_compl_spanning (hI : I ⊆ M.E := by aesop_mat) :
    M.Coindep I ↔ M.Spanning (M.E \ I) := by
  rw [coindep_iff_exists, spanning_iff_superset_base]

lemma spanning_iff_compl_coindep (hS : S ⊆ M.E := by aesop_mat) :
    M.Spanning S ↔ M.Coindep (M.E \ S) := by
  rw [coindep_iff_compl_spanning, diff_diff_cancel_left hS]

lemma Coindep.compl_spanning (hI : M.Coindep I) : M.Spanning (M.E \ I) :=
  (coindep_iff_compl_spanning hI.subset_ground).mp hI

lemma coindep_iff_cl_compl_eq_ground (hK : X ⊆ M.E := by aesop_mat) :
    M.Coindep X ↔ M.cl (M.E \ X) = M.E := by
  rw [coindep_iff_compl_spanning, spanning_iff_cl]

lemma Coindep.cl_compl (hX : M.Coindep X) : M.cl (M.E \ X) = M.E :=
  (coindep_iff_cl_compl_eq_ground hX.subset_ground).mp hX

lemma Indep.base_of_spanning (hI : M.Indep I) (hIs : M.Spanning I) : M.Base I := by
  obtain ⟨B, hB, hBI⟩ := hIs.exists_base_subset; rwa [← hB.eq_of_subset_indep hI hBI]

lemma Spanning.base_of_indep (hIs : M.Spanning I) (hI : M.Indep I) : M.Base I :=
  hI.base_of_spanning hIs

lemma eq_of_spanning_iff_spanning_forall {M M' : Matroid α} (h : M.E = M'.E)
    (hsp : ∀ S, S ⊆ M.E → (M.Spanning S ↔ M'.Spanning S )) : M = M' := by
  have hsp' : M.Spanning = M'.Spanning := by
    ext S
    refine (em (S ⊆ M.E)).elim (fun hSE ↦ by rw [hsp _ hSE] )
      (fun hSE ↦ iff_of_false (fun h ↦ hSE h.subset_ground)
      (fun h' ↦ hSE (h'.subset_ground.trans h.symm.subset)))
  rw [← dual_inj, eq_iff_indep_iff_indep_forall, dual_ground, dual_ground, and_iff_right h]
  intro I hIE
  rw [← coindep_def, ← coindep_def, coindep_iff_compl_spanning, coindep_iff_compl_spanning, hsp', h]

end Spanning

section Constructions

@[simp] lemma emptyOn_cl_eq (X : Set α) : (emptyOn α).cl X = ∅ := by
  rw [← subset_empty_iff, ← emptyOn_ground]; apply cl_subset_ground

@[simp] lemma loopyOn_cl_eq (E X : Set α) : (loopyOn E).cl X = E :=
  (cl_subset_ground _ _).antisymm
    (subset_trans (by rw [(loopyOn_base_iff.2 rfl).cl_eq]) (cl_subset_cl _ (empty_subset _)))

lemma cl_empty_eq_ground_iff : M.cl ∅ = M.E ↔ M = loopyOn M.E := by
  refine ⟨fun h ↦ eq_of_cl_eq_cl_forall ?_, fun h ↦ by rw [h, loopyOn_cl_eq, loopyOn_ground]⟩
  refine fun X ↦ subset_antisymm (by simp [cl_subset_ground]) ?_
  rw [loopyOn_cl_eq, ← h]
  exact M.cl_mono (empty_subset _)

@[simp] lemma uniqueBaseOn_cl_eq (I E X : Set α) :
    (uniqueBaseOn I E).cl X = (X ∩ I ∩ E) ∪ (E \ I) := by
  have hb : (uniqueBaseOn (I ∩ E) E).Basis (X ∩ E ∩ (I ∩ E)) (X ∩ E) :=
    (uniqueBaseOn_basis_iff inter_subset_right inter_subset_right).2 rfl
  ext e
  rw [← uniqueBaseOn_inter_ground_eq I E, ← cl_inter_ground _ X, uniqueBaseOn_ground,
    ← hb.cl_eq_cl, hb.indep.mem_cl_iff, dep_iff, uniqueBaseOn_indep_iff', insert_subset_iff,
    uniqueBaseOn_ground, inter_assoc, inter_self,  and_iff_left inter_subset_right,
    ← inter_inter_distrib_right, inter_assoc, inter_union_distrib_right, inter_comm I,
    inter_union_diff, insert_subset_iff, inter_comm X, inter_assoc,
    and_iff_left inter_subset_left, mem_inter_iff]
  simp only [not_and, mem_inter_iff, mem_union, mem_diff]
  tauto

end Constructions

variable {Xs Ys : Set (Set α)} {ι : Type*}

lemma Indep.inter_basis_cl_iff_subset_cl_inter {X : Set α} (hI : M.Indep I) :
    M.Basis (X ∩ I) X ↔ X ⊆ M.cl (X ∩ I) :=
  ⟨Basis.subset_cl,
    fun h ↦ (hI.inter_left X).basis_of_subset_of_subset_cl inter_subset_left h⟩

lemma Indep.interBasis_biInter (hI : M.Indep I) {X : ι → Set α} {A : Set ι} (hA : A.Nonempty)
    (h : ∀ i ∈ A, M.Basis ((X i) ∩ I) (X i)) : M.Basis ((⋂ i ∈ A, X i) ∩ I) (⋂ i ∈ A, X i) := by
  refine (hI.inter_left _).basis_of_subset_of_subset_cl inter_subset_left ?_
  have := biInter_inter hA X I
  simp_rw [← biInter_inter hA,
    cl_biInter_eq_biInter_cl_of_biUnion_indep hA (I := fun i ↦ (X i) ∩ I) (hI.subset (by simp)),
    subset_iInter_iff]
  exact fun i hiA ↦ (biInter_subset_of_mem hiA).trans (h i hiA).subset_cl

lemma Indep.interBasis_iInter [Nonempty ι] {X : ι → Set α} (hI : M.Indep I)
    (h : ∀ i, M.Basis ((X i) ∩ I) (X i)) : M.Basis ((⋂ i, X i) ∩ I) (⋂ i, X i) := by
  rw [← biInter_univ]
  exact hI.interBasis_biInter (by simp) (by simpa)

lemma Indep.interBasis_sInter (hI : M.Indep I) (hXs : Xs.Nonempty)
    (h : ∀ X ∈ Xs, M.Basis (X ∩ I) X) : M.Basis (⋂₀ Xs ∩ I) (⋂₀ Xs) := by
  rw [sInter_eq_biInter]
  exact hI.interBasis_biInter hXs h

lemma Basis.cl_inter_basis_cl (h : M.Basis (X ∩ I) X) (hI : M.Indep I) :
    M.Basis (M.cl X ∩ I) (M.cl X) := by
  rw [hI.inter_basis_cl_iff_subset_cl_inter] at h ⊢
  exact (M.cl_subset_cl_of_subset_cl h).trans (M.cl_subset_cl
    (inter_subset_inter_left _ (h.trans (M.cl_subset_cl inter_subset_left))))

end Matroid





-- -- section from_axioms
-- -- lemma cl_diff_singleton_eq_cl' (cl : set α → set α) (M.subset_cl : ∀ X, X ⊆ cl X)
-- -- (cl_mono : ∀ X Y, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X )
-- -- {x : α} {I : set α} (h : x ∈ cl (I \ {x})) :
-- --   cl (I \ {x}) = cl I :=
-- -- begin
-- --   refine (cl_mono _ _ diff_subset).antisymm _,
-- --   have h' := cl_mono _ _ (insert_subset.mpr ⟨h, (M.subset_cl _ )⟩),
-- --   rw [insert_diff_singleton, cl_idem] at h',
-- --   exact (cl_mono _ _ (subset_insert _ _)).trans h',
-- -- end
-- -- /-- A set is independent relative to a closure function if none of its elements are contained in
-- --   the closure of their removal -/
-- -- def cl_indep (cl : set α → set α) (I : set α) : Prop := ∀ e ∈ I, e ∉ cl (I \ {e})
-- -- lemma cl_indep_mono {cl : set α → set α} (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) {I J : set α}
-- -- (hJ : cl_indep cl J) (hIJ : I ⊆ J) :
-- --   cl_indep cl I :=
-- -- (λ e heI hecl, hJ e (hIJ heI) (cl_mono (diff_subset_diff_left hIJ) hecl))
-- -- lemma cl_indep_aux {e : α} {I : set α} {cl : set α → set α}
-- -- (cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X )
-- -- (h : cl_indep cl I) (heI : ¬cl_indep cl (insert e I)) :
-- -- e ∈ cl I :=
-- -- begin
-- --   have he : α ∉ I, by { intro he, rw [insert_eq_of_mem he] at heI, exact heI h },
-- --   rw [cl_indep] at heI, push_neg at heI,
-- --   obtain ⟨f, ⟨(rfl | hfI), hfcl⟩⟩ := heI,
-- --   { rwa [insert_diff_self_of_not_mem he] at hfcl },
-- --   have hne : α ≠ f, by { rintro rfl, exact he hfI },
-- --   rw [← insert_diff_singleton_comm hne] at hfcl,
-- --   convert (cl_exchange (I \ {f}) e f ⟨hfcl,h f hfI⟩).1,
-- --   rw [insert_diff_singleton, insert_eq_of_mem hfI],
-- -- end
-- -- /-- If the closure axioms hold, then `cl`-independence gives rise to a matroid -/
-- -- def matroid_of_cl (cl : set α → set α) (M.subset_cl : ∀ X, X ⊆ cl X)
-- -- (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X )
-- -- (cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X )
-- -- (cl_indep_maximal : ∀ ⦃I X⦄, cl_indep cl I → I ⊆ X  →
-- --     (maximals (⊆) {J | cl_indep cl J ∧ I ⊆ J ∧ J ⊆ X }).nonempty) :
-- -- matroid_in α :=
-- -- matroid_of_indep (cl_indep cl)
-- -- (λ e he _, not_mem_empty _ he) (λ I J hJ hIJ, cl_indep_mono cl_mono hJ hIJ)
-- -- (begin
-- --   refine λ I I' hI hIn hI'm, _,
-- --   obtain ⟨B, hB⟩ := cl_indep_maximal hI (subset_union_left I I'),
-- --   have hB' : B ∈ maximals (⊆) {J | cl_indep cl J},
-- --   { refine ⟨hB.1.1,(λ B' hB' hBB' e heB', by_contra (λ heB, _) )⟩,
-- --     have he' : α ∈ cl I',
-- --     { refine (em (e ∈ I')).elim (λ heI', (M.subset_cl I') heI')
-- --         (λ heI', cl_indep_aux cl_exchange hI'm.1 (λ hi, _)),
-- --       exact heI' (hI'm.2 hi (subset_insert e _) (mem_insert e _)) },
-- --       have hI'B : I' ⊆ cl B,
-- --     { refine λ f hf, (em (f ∈ B)).elim (λ h', M.subset_cl B h')
-- --         (λ hfB', cl_indep_aux cl_exchange hB.1.1 (λ hi, hfB' _)),
-- --       refine hB.2 ⟨hi,hB.1.2.1.trans (subset_insert _ _),_⟩ (subset_insert _ _) (mem_insert _ _),
-- --       exact insert_subset.mpr ⟨or.inr hf,hB.1.2.2⟩ },
-- --     have heBcl := (cl_idem B).subset ((cl_mono hI'B) he'),
-- --     refine cl_indep_mono cl_mono hB' (insert_subset.mpr ⟨heB', hBB'⟩) e (mem_insert _ _) _,
-- --     rwa [insert_diff_of_mem _ (mem_singleton e), diff_singleton_eq_self heB] },
-- --   obtain ⟨f,hfB,hfI⟩ := exists_of_ssubset
-- --     (hB.1.2.1.ssubset_of_ne (by { rintro rfl, exact hIn hB' })),
-- --   refine ⟨f, ⟨_, hfI⟩, cl_indep_mono cl_mono hB.1.1 (insert_subset.mpr ⟨hfB,hB.1.2.1⟩)⟩,
-- --   exact or.elim (hB.1.2.2 hfB) (false.elim ∘ hfI) id,
-- -- end)
-- -- (λ I X hI hIX, cl_indep_maximal hI hIX)
-- -- lemma cl_indep_cl_eq {cl : set α → set α }
-- --   (M.subset_cl : ∀ X, X ⊆ cl X )
-- --   (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y )
-- --   (cl_idem : ∀ X, cl (cl X) = cl X )
-- --   (cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X )
-- --   (cl_indep_maximal : ∀ ⦃I X⦄, cl_indep cl I → I ⊆ X →
-- --     (maximals (⊆) {J | cl_indep cl J ∧ I ⊆ J ∧ J ⊆ X }).nonempty ) (X : set α) :
-- -- cl X = X ∪ {e | ∃ I ⊆ X, cl_indep cl I ∧ ¬cl_indep cl (insert e I) }  :=
-- -- begin
-- --   ext f,
-- --   refine ⟨λ h, (em (f ∈ X)).elim or.inl (λ hf, or.inr _),
-- --     λ h, or.elim h (λ g, M.subset_cl X g) _⟩,
-- --   { have hd : ¬ (cl_indep cl (insert f X)),
-- --     { refine λ hi, hi f (mem_insert _ _) _, convert h,
-- --       rw [insert_diff_of_mem _ (mem_singleton f), diff_singleton_eq_self hf] },
-- --     obtain ⟨I, hI⟩ := cl_indep_maximal (λ e he h', not_mem_empty _ he) (empty_subset X),
-- --     have hXI : X ⊆ cl I,
-- --     { refine λ x hx, (em (x ∈ I)).elim (λ h', M.subset_cl _ h') (λ hxI, _),
-- --       refine cl_indep_aux cl_exchange hI.1.1 (λ hi, hxI _),
-- --       refine hI.2 ⟨hi, empty_subset (insert x I), _⟩ (subset_insert x _) (mem_insert _ _),
-- --       exact insert_subset.mpr ⟨hx, hI.1.2.2⟩ },
-- --     have hfI : f ∈ cl I, from (cl_mono (hXI)).trans_eq (cl_idem I) h,
-- --     refine ⟨I, hI.1.2.2, hI.1.1, λ hi, hf (hi f (mem_insert f _) _).elim⟩,
-- --     rwa [insert_diff_of_mem _ (mem_singleton f), diff_singleton_eq_self],
-- --     exact not_mem_subset hI.1.2.2 hf },
-- --   rintro ⟨I, hIX, hI, hfI⟩,
-- --   exact (cl_mono hIX) (cl_indep_aux cl_exchange hI hfI),
-- -- end
-- -- @[simp] lemma matroid_of_cl_apply {cl : set α → set α} (M.subset_cl : ∀ X, X ⊆ cl X)
-- -- (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X)
-- -- (cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X)
-- -- (cl_indep_maximal : ∀ ⦃I X⦄, cl_indep cl I → I ⊆ X →
-- --     (maximals (⊆) {J | cl_indep cl J ∧ I ⊆ J ∧ J ⊆ X }).nonempty) :
-- -- (matroid_of_cl cl M.subset_cl cl_mono cl_idem cl_exchange cl_indep_maximal).cl = cl :=
-- -- begin
-- --   ext1 X,
-- --   rw [(cl_indep_cl_eq M.subset_cl cl_mono cl_idem cl_exchange cl_indep_maximal X : cl X = _),
-- --     matroid_of_cl, matroid.cl_eq_set_of_indep_not_indep],
-- --   simp,
-- -- end
-- -- @[simp] lemma matroid_of_cl_indep_iff {cl : set α → set α} (M.subset_cl : ∀ X, X ⊆ cl X)
-- -- (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X)
-- -- (cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X)
-- -- (cl_indep_maximal : ∀ ⦃I X⦄, cl_indep cl I → I ⊆ X →
-- --     (maximals (⊆) {J | cl_indep cl J ∧ I ⊆ J ∧ J ⊆ X }).nonempty) {I : set α}:
-- -- (matroid_of_cl cl M.subset_cl cl_mono cl_idem cl_exchange cl_indep_maximal).indep I ↔ cl_indep cl I :=
-- -- by rw [matroid_of_cl, matroid_of_indep_apply]
-- -- /-- The maximality axiom isn't needed if all independent sets are at most some fixed size. -/
-- -- def matroid_of_cl_of_indep_bounded (cl : set α → set α)
-- --   (M.subset_cl : ∀ X, X ⊆ cl X )
-- --   (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y )
-- --   (cl_idem : ∀ X, cl (cl X) = cl X )
-- --   (cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X )
-- --   (n : ℕ) (hn : ∀ I, cl_indep cl I → I.finite ∧ I.ncard ≤ n) :
-- -- matroid_in α := matroid_of_cl cl M.subset_cl cl_mono cl_idem cl_exchange
-- -- (exists_maximal_subset_property_of_bounded ⟨n, hn⟩)
-- -- @[simp] lemma matroid_of_cl_of_indep_bounded_apply (cl : set α → set α) (M.subset_cl : ∀ X, X ⊆ cl X )
-- -- (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X )
-- -- (cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X )
-- -- (n : ℕ) (hn : ∀ I, cl_indep cl I → I.finite ∧ I.ncard ≤ n) :
-- -- (matroid_of_cl_of_indep_bounded cl M.subset_cl cl_mono cl_idem cl_exchange n hn).cl = cl :=
-- -- by simp [matroid_of_cl_of_indep_bounded]
-- -- instance (cl : set α → set α) (M.subset_cl : ∀ X, X ⊆ cl X )
-- -- (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X )
-- -- (cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X )
-- -- (n : ℕ) (hn : ∀ I, cl_indep cl I → I.finite ∧ I.ncard ≤ n) :
-- -- matroid.finite_rk (matroid_of_cl_of_indep_bounded cl M.subset_cl cl_mono cl_idem cl_exchange n hn)
-- -- :=
-- -- begin
-- --   obtain ⟨B, h⟩ :=
-- --     (matroid_of_cl_of_indep_bounded cl M.subset_cl cl_mono cl_idem cl_exchange n hn).exists_base,
-- --   refine h.finite_rk_of_finite (hn _ _).1,
-- --   simp_rw [matroid_of_cl_of_indep_bounded, matroid_of_cl, matroid.base_iff_maximal_indep,
-- --     matroid_of_indep_apply] at h,
-- --   exact h.1,
-- -- end
-- -- /-- A finite matroid as defined by the closure axioms. -/
-- -- def matroid_of_cl_of_finite [finite E] (cl : set α → set α) (M.subset_cl : ∀ X, X ⊆ cl X )
-- -- (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X)
-- -- (cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X) :
-- -- matroid_in α   :=
-- -- matroid_of_cl_of_indep_bounded cl M.subset_cl cl_mono cl_idem cl_exchange (nat.card E)
-- -- (λ I hI, ⟨to_finite _, by { rw [← ncard_univ], exact ncard_le_of_subset (subset_univ _) }⟩)
-- -- @[simp] lemma matroid_of_cl_of_finite_apply [finite E] (cl : set α → set α)
-- -- (M.subset_cl : ∀ X, X ⊆ cl X )
-- -- (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X)
-- -- (cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X) :
-- -- (matroid_of_cl_of_finite cl M.subset_cl cl_mono cl_idem cl_exchange).cl = cl :=
-- -- by simp [matroid_of_cl_of_finite]
-- -- end from_axioms
-- end Matroid
