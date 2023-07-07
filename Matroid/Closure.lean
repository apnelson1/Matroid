import Matroid.Equiv
 
open scoped BigOperators

open Set

namespace Matroid

-- variable {α : Type _} {M : Matroid α} {I J B C X Y : Set α} {e f x y : α}

variable {α : Type _} {M : Matroid α}

/-- A flat is a maximal set having a given basis  -/
def Flat (M : Matroid α) (F : Set α) : Prop :=
  (∀ ⦃I X⦄, M.Basis I F → M.Basis I X → X ⊆ F) ∧ F ⊆ M.E
pp_extended_field_notation Flat

@[aesop unsafe 10% (rule_sets [Matroid])]
theorem Flat.subset_ground (hF : M.Flat F) : F ⊆ M.E := 
  hF.2

theorem ground_flat (M : Matroid α) : M.Flat M.E :=
  ⟨fun _ _ _ ↦ Basis.subset_ground, Subset.rfl⟩

/-- The closure of a subset of the ground set is the intersection of the flats containing it. 
  A set `X` that doesn't satisfy `X ⊆ M.E` has the junk value `M.cl X := M.cl (X ∩ M.E)`. -/
def cl (M : Matroid α) (X : Set α) : Set α :=
  ⋂₀ {F | M.Flat F ∧ X ∩ M.E ⊆ F}
pp_extended_field_notation cl

theorem cl_def (M : Matroid α) (X : Set α) : M.cl X = ⋂₀ {F | M.Flat F ∧ X ∩ M.E ⊆ F} :=
  rfl

theorem cl_def' (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) : 
    M.cl X = ⋂₀ {F | M.Flat F ∧ X ⊆ F} := by
  nth_rw 2 [←inter_eq_self_of_subset_left hX]; rfl 

@[aesop unsafe 10% (rule_sets [Matroid])]
theorem cl_subset_ground (M : Matroid α) (X : Set α) : M.cl X ⊆ M.E :=
  sInter_subset_of_mem ⟨M.ground_flat, inter_subset_right _ _⟩ 

theorem cl_eq_sInter_of_subset {M : Matroid α} (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    M.cl X = ⋂₀ {F : Set α | M.Flat F ∧ X ⊆ F} :=
  by rw [cl, inter_eq_self_of_subset_left hX]

theorem cl_eq_cl_inter_ground (M : Matroid α) (X : Set α) : M.cl X = M.cl (X ∩ M.E) := by
  simp_rw [cl_def, inter_assoc, inter_self]

theorem inter_ground_subset_cl (M : Matroid α) (X : Set α) : X ∩ M.E ⊆ M.cl X := by
  simp_rw [cl_def, subset_sInter_iff]; aesop

theorem mem_cl_iff_forall_mem_flat (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    e ∈ M.cl X ↔ ∀ F, M.Flat F → X ⊆ F → e ∈ F := by
  simp_rw [cl_eq_sInter_of_subset X, mem_sInter, mem_setOf, and_imp]

theorem subset_cl_iff_forall_subset_flat (X : Set α) (hX : X ⊆ M.E := by aesop_mat) : 
    Y ⊆ M.cl X ↔ ∀ F, M.Flat F → X ⊆ F → Y ⊆ F := by
  simp_rw [cl_eq_sInter_of_subset X, subset_sInter_iff, mem_setOf, and_imp]
  
theorem subset_cl (M : Matroid α) (X : Set α) (hX : X ⊆ M.E := by aesop_mat) :
    X ⊆ M.cl X := by 
  rw [cl_eq_sInter_of_subset X, subset_sInter_iff]; simp

theorem Flat.cl (hF : M.Flat F) : M.cl F = F :=
  (sInter_subset_of_mem (by simpa)).antisymm (M.subset_cl F)
-- Move back to `Flat`
-- theorem Flat.iInter {ι : Type _} [Nonempty ι] {Fs : ι → Set α} (hFs -: ∀ i, M.Flat (Fs i)) : 
--     M.Flat (⋂ i, Fs i) := by
--   refine' ⟨fun I X hI hIX ↦ subset_iInter fun i ↦ _,
--     (iInter_subset _ (Classical.arbitrary _)).trans (hFs _).subset_ground⟩ 
--   obtain ⟨J, hIJ, hJ⟩ := hI.indep.subset_basis_of_subset (hI.subset.trans (iInter_subset _ i))
--   refine' (subset_union_right _ _).trans ((hFs i).1 (X := Fs i ∪ X) hIJ _)
--   convert hIJ.basis_union (hIX.basis_union_of_subset hIJ.indep hJ) using 1
--   rw [←union_assoc, union_eq_self_of_subset_right hIJ.subset]

-- theorem Flat.sInter {Fs : Set (Set α)} (hF : Fs.Nonempty) (h : ∀ F, F ∈ Fs → M.Flat F) : 
--     M.Flat (⋂₀ Fs) := by
--   rw [sInter_eq_iInter]
--   have : Nonempty Fs
--   · exact Iff.mpr nonempty_coe_sort hF
--   exact Flat.iInter (fun ⟨F, hF⟩ ↦ h _ hF)

-- theorem cl_flat (M : Matroid α) (X : Set α) : M.Flat (M.cl X) :=
--   Flat.sInter ⟨M.E, M.ground_flat, inter_subset_right _ _⟩ fun _ ↦ And.left   

@[simp] theorem cl_ground (M : Matroid α) : M.cl M.E = M.E := 
  (M.cl_subset_ground M.E).antisymm (M.subset_cl M.E) 

@[simp] theorem cl_univ (M : Matroid α) : M.cl univ = M.E := by 
  rw [cl_eq_cl_inter_ground, univ_inter, cl_ground]

theorem cl_subset_cl (M : Matroid α) (h : X ⊆ Y) : M.cl X ⊆ M.cl Y :=
  subset_sInter (fun _ ⟨hF, hssF⟩ ↦ 
    sInter_subset_of_mem ⟨hF, subset_trans (inter_subset_inter_left _ h) hssF⟩)

theorem cl_mono (M : Matroid α) : Monotone M.cl := 
  fun _ _ ↦ M.cl_subset_cl 

@[simp] theorem cl_cl (M : Matroid α) (X : Set α) : M.cl (M.cl X) = M.cl X :=
  (M.subset_cl _).antisymm'
    (subset_sInter (fun F hF ↦ (cl_subset_cl _ (sInter_subset_of_mem hF)).trans hF.1.cl.subset)) 
    
theorem cl_subset_cl_of_subset_cl (hXY : X ⊆ M.cl Y) : M.cl X ⊆ M.cl Y :=
    (M.cl_subset_cl hXY).trans_eq (M.cl_cl Y)

theorem cl_subset_cl_iff_subset_cl (hX : X ⊆ M.E := by aesop_mat) : 
    M.cl X ⊆ M.cl Y ↔ X ⊆ M.cl Y :=
  ⟨(M.subset_cl X).trans, cl_subset_cl_of_subset_cl⟩ 

theorem subset_cl_of_subset (M : Matroid α) (hXY : X ⊆ Y) (hY : Y ⊆ M.E := by aesop_mat) : 
    X ⊆ M.cl Y := 
  hXY.trans (M.subset_cl Y)

theorem mem_cl_of_mem (M : Matroid α) (h : e ∈ X) (hX : X ⊆ M.E := by aesop_mat) : 
    e ∈ M.cl X := 
  (M.subset_cl X) h

theorem mem_cl_of_mem' (M : Matroid α) (heX : e ∈ X) (h : e ∈ M.E := by aesop_mat) :
    e ∈ M.cl X := by
  rw [cl_eq_cl_inter_ground]; exact M.mem_cl_of_mem ⟨heX, h⟩  

-- @[aesop unsafe 10% (rule_sets [Matroid])]
theorem mem_ground_of_mem_cl (he : e ∈ M.cl X) : e ∈ M.E := (M.cl_subset_ground _) he 

@[simp] theorem cl_union_cl_right_eq (M : Matroid α) (X Y : Set α) : 
    M.cl (X ∪ M.cl Y) = M.cl (X ∪ Y) := by
  rw [cl_eq_cl_inter_ground, M.cl_eq_cl_inter_ground (X ∪ Y), inter_distrib_right, 
   inter_distrib_right, subset_antisymm_iff] 
  refine' ⟨M.cl_subset_cl_of_subset_cl 
            (union_subset (M.subset_cl_of_subset (subset_union_left _ _)) _), 
              M.cl_subset_cl_of_subset_cl 
            (union_subset (M.subset_cl_of_subset (subset_union_left _ _)) _)⟩ 
  · rw [←inter_distrib_right, ←cl_eq_cl_inter_ground]
    exact (inter_subset_left _ _).trans (M.cl_subset_cl (subset_union_right _ _))
  refine' M.subset_cl_of_subset (subset_union_of_subset_right _ _)
  rw [cl_eq_cl_inter_ground]
  exact subset_inter (M.subset_cl _) (inter_subset_right _ _)

@[simp] theorem cl_union_cl_left_eq (M : Matroid α) (X Y : Set α) :
    M.cl (M.cl X ∪ Y) = M.cl (X ∪ Y) := by
  rw [union_comm, cl_union_cl_right_eq, union_comm]

@[simp] theorem cl_cl_union_cl_eq_cl_union (M : Matroid α) (X Y : Set α) :
    M.cl (M.cl X ∪ M.cl Y) = M.cl (X ∪ Y) := by rw [cl_union_cl_left_eq, cl_union_cl_right_eq]

@[simp] theorem cl_insert_cl_eq_cl_insert (M : Matroid α) (e : α) (X : Set α) :
    M.cl (insert e (M.cl X)) = M.cl (insert e X) := by
  simp_rw [← singleton_union, cl_union_cl_right_eq]

theorem cl_insert_eq_of_mem_cl (he : e ∈ M.cl X) : M.cl (insert e X) = M.cl X := by
  rw [←cl_insert_cl_eq_cl_insert, insert_eq_of_mem he, cl_cl]

theorem cl_union_eq_cl_of_subset_loops (M : Matroid α) (X : Set α) (hY : Y ⊆ M.cl ∅) :
    M.cl (X ∪ Y) = M.cl X :=
  (M.cl_subset_cl (subset_union_left _ _)).antisymm' 
    ((M.cl_subset_cl (union_subset_union_right X hY)).trans_eq (by simp))

theorem cl_diff_eq_cl_of_subset_loops (M : Matroid α) (X : Set α) (hY : Y ⊆ M.cl ∅) :
    M.cl (X \ Y) = M.cl X := by
  rw [←cl_union_eq_cl_of_subset_loops _ _ hY, diff_union_self, 
    cl_union_eq_cl_of_subset_loops _ _ hY]
  
@[simp] theorem cl_diff_loops_eq (M : Matroid α) (X : Set α) : M.cl (X \ M.cl ∅) = M.cl X :=
  M.cl_diff_eq_cl_of_subset_loops X rfl.subset

theorem mem_cl_self (M : Matroid α) (e : α) (he : e ∈ M.E := by aesop_mat) : e ∈ M.cl {e} :=
  mem_cl_of_mem' _ rfl

-- Independence and Bases

theorem Indep.cl_eq_setOf_basis_insert (hI : M.Indep I) :
    M.cl I = {x | M.Basis I (insert x I)} := by
  set F := {x | M.Basis I (insert x I)}
  have hIF : M.Basis I F := hI.basis_setOf_insert_basis

  have hF : M.Flat F
  · refine' ⟨fun J X hJF hJX e heX ↦ (_ : M.Basis _ _), hIF.subset_ground⟩
    exact (hIF.basis_of_basis_of_subset_of_subset (hJX.basis_union hJF) hJF.subset
      (hIF.subset.trans (subset_union_right _ _))).basis_subset (subset_insert _ _)
      (insert_subset (Or.inl heX) (hIF.subset.trans (subset_union_right _ _)))

  rw [subset_antisymm_iff, cl_def, subset_sInter_iff, and_iff_right (sInter_subset_of_mem _)]
  · rintro F' ⟨hF', hIF'⟩ e (he : M.Basis I (insert e I))
    rw [inter_eq_left_iff_subset.mpr (hIF.subset.trans hIF.subset_ground)] at hIF' 
    obtain ⟨J, hJ, hIJ⟩ := hI.subset_basis_of_subset hIF' hF'.2
    exact (hF'.1 hJ (he.basis_union_of_subset hJ.indep hIJ)) (Or.inr (mem_insert _ _))
  exact ⟨hF, (inter_subset_left _ _).trans hIF.subset⟩ 
  
theorem Indep.insert_basis_iff_mem_cl (hI : M.Indep I) : M.Basis I (insert e I) ↔ e ∈ M.cl I := by
  rw [hI.cl_eq_setOf_basis_insert, mem_setOf]

theorem Indep.basis_cl (hI : M.Indep I) : M.Basis I (M.cl I) := by
  rw [hI.cl_eq_setOf_basis_insert]; exact hI.basis_setOf_insert_basis

theorem Basis.cl_eq_cl (h : M.Basis I X) : M.cl I = M.cl X := by 
  refine' subset_antisymm (M.cl_subset_cl h.subset) _
  rw [←M.cl_cl I, h.indep.cl_eq_setOf_basis_insert]
  exact M.cl_subset_cl fun e he ↦ (h.basis_subset (subset_insert _ _) (insert_subset he h.subset))

theorem Basis.subset_cl (h : M.Basis I X) : X ⊆ M.cl I := by 
  rw [←cl_subset_cl_iff_subset_cl, h.cl_eq_cl]

theorem Basis.basis_cl_right (h : M.Basis I X) : M.Basis I (M.cl X) := by
  rw [←h.cl_eq_cl]; exact h.indep.basis_cl

theorem Indep.mem_cl_iff (hI : M.Indep I) :
    x ∈ M.cl I ↔ M.Dep (insert x I) ∨ x ∈ I := by 
  rwa [hI.cl_eq_setOf_basis_insert, mem_setOf, basis_insert_iff]

theorem Indep.insert_dep_iff (hI : M.Indep I) : M.Dep (insert e I) ↔ e ∈ M.cl I \ I := by 
  rw [mem_diff, hI.mem_cl_iff, or_and_right, and_not_self_iff, or_false, 
    iff_self_and, imp_not_comm]
  intro heI; rw [insert_eq_of_mem heI]; exact hI.not_dep
  
theorem Indep.mem_cl_iff_of_not_mem (hI : M.Indep I) (heI : e ∉ I) :
    e ∈ M.cl I ↔ M.Dep (insert e I) := by
  rw [hI.insert_dep_iff, mem_diff, and_iff_left heI]

theorem Indep.not_mem_cl_iff (hI : M.Indep I) (he : e ∈ M.E := by aesop_mat) : 
    e ∉ M.cl I ↔ M.Indep (insert e I) ∧ e ∉ I := by
  rw [hI.mem_cl_iff, dep_iff, insert_subset_iff, and_iff_right he, 
    and_iff_left hI.subset_ground]; tauto

theorem Indep.not_mem_cl_iff_of_not_mem (hI : M.Indep I) (heI : e ∉ I) 
    (he : e ∈ M.E := by aesop_mat) : e ∉ M.cl I ↔ M.Indep (insert e I) := by
  rw [hI.not_mem_cl_iff, and_iff_left heI]

theorem Indep.basis_of_subset_of_subset_cl (hI : M.Indep I) (hIX : I ⊆ X) (hXI : X ⊆ M.cl I) : 
    M.Basis I X :=
  hI.basis_cl.basis_subset hIX hXI

theorem basis_iff_indep_subset_cl : M.Basis I X ↔ M.Indep I ∧ I ⊆ X ∧ X ⊆ M.cl I :=
  ⟨fun h ↦ ⟨h.indep, h.subset, h.subset_cl⟩, fun h ↦ h.1.basis_of_subset_of_subset_cl h.2.1 h.2.2⟩

theorem Indep.base_of_ground_subset_cl (hI : M.Indep I) (h : M.E ⊆ M.cl I) : M.Base I := by
  rw [←basis_ground_iff]; exact hI.basis_of_subset_of_subset_cl hI.subset_ground h

theorem Base.cl_eq (hB : M.Base B) : M.cl B = M.E := by
  rw [←basis_ground_iff] at hB; rw [hB.cl_eq_cl, cl_ground]

theorem Base.mem_cl (hB : M.Base B) (e : α) (he : e ∈ M.E := by aesop_mat) : e ∈ M.cl B := by 
  rwa [hB.cl_eq]

theorem Base.cl_of_supset (hB : M.Base B) (hBX : B ⊆ X) : M.cl X = M.E :=
  subset_antisymm (M.cl_subset_ground _) (by rw [← hB.cl_eq]; exact M.cl_subset_cl hBX)

theorem base_iff_indep_cl_eq : M.Base B ↔ M.Indep B ∧ M.cl B = M.E := by
  rw [←basis_ground_iff, basis_iff_indep_subset_cl, and_congr_right_iff]
  exact fun hI ↦ ⟨fun h ↦ (M.cl_subset_ground _).antisymm h.2, 
    fun h ↦ ⟨(M.subset_cl B).trans_eq h, h.symm.subset⟩⟩

theorem Indep.cl_inter_eq_self_of_subset (hI : M.Indep I) (hJI : J ⊆ I) : M.cl J ∩ I = J := by
  have hJ := hI.subset hJI
  rw [subset_antisymm_iff, and_iff_left (subset_inter (M.subset_cl _) hJI)]
  rintro e ⟨heJ, heI⟩
  exact hJ.basis_cl.mem_of_insert_indep heJ (hI.subset (insert_subset heI hJI))
  
theorem Indep.cl_sInter_eq_iInter_cl_of_forall_subset {Js : Set (Set α)} (hI : M.Indep I) 
    (hne : Js.Nonempty) (hIs : ∀ J ∈ Js, J ⊆ I) : M.cl (⋂₀ Js) = (⋂ J ∈ Js, M.cl J)  := by
  rw [subset_antisymm_iff, subset_iInter₂_iff]
  have hiX : ⋂₀ Js ⊆ I := (sInter_subset_of_mem hne.some_mem).trans (hIs _ hne.some_mem)
  have hiI := hI.subset hiX
  refine' ⟨ fun X hX ↦ M.cl_subset_cl (sInter_subset_of_mem hX), fun e he ↦ by_contra fun he' ↦ _⟩
  rw [mem_iInter₂] at he
  have heEI : e ∈ M.E \ I
  · refine' ⟨M.cl_subset_ground _ (he _ hne.some_mem), fun heI ↦ he' _⟩
    refine' mem_cl_of_mem _ (fun X hX' ↦ _) hiI.subset_ground
    rw [←hI.cl_inter_eq_self_of_subset (hIs X hX')]
    exact ⟨he X hX', heI⟩  
  
  rw [hiI.not_mem_cl_iff_of_not_mem (not_mem_subset hiX heEI.2)] at he'
  obtain ⟨J, hJI, heJ⟩ := he'.subset_basis_of_subset (insert_subset_insert hiX) 
    (insert_subset heEI.1 hI.subset_ground)

  have hIb : M.Basis I (insert e I)
  · rw [hI.insert_basis_iff_mem_cl]; exact (M.cl_subset_cl (hIs _ hne.some_mem)) (he _ hne.some_mem)

  obtain ⟨f, hfIJ, hfb⟩ :=  hJI.exchange hIb ⟨heJ (mem_insert e _), heEI.2⟩ 
  obtain rfl := hI.eq_of_basis (hfb.basis_subset (insert_subset hfIJ.1 
    (by (rw [diff_subset_iff, singleton_union]; exact hJI.subset))) (subset_insert _ _))
  
  refine' hfIJ.2 (heJ (mem_insert_of_mem _ fun X hX' ↦ by_contra fun hfX ↦ _))
  
  obtain (hd | heX) := ((hI.subset (hIs X hX')).mem_cl_iff).mp (he _ hX')
  · refine' (hJI.indep.subset (insert_subset (heJ (mem_insert _ _)) _)).not_dep hd
    specialize hIs _ hX'
    rw [←singleton_union, ←diff_subset_iff, diff_singleton_eq_self hfX] at hIs
    exact hIs.trans (diff_subset _ _)
  exact heEI.2 (hIs _ hX' heX)

theorem cl_iInter_eq_iInter_cl_of_iUnion_indep {ι : Type _} (Is : ι → Set α) [hι : Nonempty ι]
    (h : M.Indep (⋃ i, Is i)) :  M.cl (⋂ i, Is i) = (⋂ i, M.cl (Is i)) := by
  convert h.cl_sInter_eq_iInter_cl_of_forall_subset (range_nonempty Is) (by simp [subset_iUnion])
  simp

theorem Indep.cl_inter_eq_inter_cl (h : M.Indep (I ∪ J)) : M.cl (I ∩ J) = M.cl I ∩ M.cl J := by 
  rw [inter_eq_iInter, cl_iInter_eq_iInter_cl_of_iUnion_indep, inter_eq_iInter]
  · exact iInter_congr (by simp) 
  rwa [←union_eq_iUnion]

theorem basis_iff_basis_cl_of_subset (hIX : I ⊆ X) (hX : X ⊆ M.E := by aesop_mat) :
    M.Basis I X ↔ M.Basis I (M.cl X) :=
  ⟨fun h ↦ h.basis_cl_right, fun h ↦ h.basis_subset hIX (M.subset_cl X hX)⟩

theorem basis_iff_basis_cl_of_subset' (hIX : I ⊆ X) : M.Basis I X ↔ X ⊆ M.E ∧ M.Basis I (M.cl X) :=
  ⟨fun h ↦ ⟨h.subset_ground, h.basis_cl_right⟩, fun h ↦ h.2.basis_subset hIX (M.subset_cl X h.1)⟩

theorem Basis.basis_of_cl_eq_cl (hI : M.Basis I X) (hY : I ⊆ Y) (h : M.cl X = M.cl Y) 
    (hYE : Y ⊆ M.E := by aesop_mat) : M.Basis I Y := by
  refine' hI.indep.basis_of_subset_of_subset_cl hY _
  rw [hI.cl_eq_cl, h] 
  exact M.subset_cl Y

theorem basis_union_iff_indep_cl : M.Basis I (I ∪ X) ↔ M.Indep I ∧ X ⊆ M.cl I :=
  ⟨fun h ↦ ⟨h.indep, (subset_union_right _ _).trans h.subset_cl⟩, fun ⟨hI, hXI⟩ ↦ 
    hI.basis_cl.basis_subset (subset_union_left _ _) (union_subset (M.subset_cl I) hXI)⟩
  
theorem basis_iff_indep_cl : M.Basis I X ↔ M.Indep I ∧ X ⊆ M.cl I ∧ I ⊆ X :=
  ⟨fun h ↦ ⟨h.indep, h.subset_cl, h.subset⟩, fun h ↦
    (basis_union_iff_indep_cl.mpr ⟨h.1, h.2.1⟩).basis_subset h.2.2 (subset_union_right _ _)⟩

theorem Basis.eq_of_cl_subset (hI : M.Basis I X) (hJI : J ⊆ I) (hJ : X ⊆ M.cl J) : J = I := by
  rw [←hI.indep.cl_inter_eq_self_of_subset hJI, inter_eq_right_iff_subset]; exact hI.subset.trans hJ

theorem empty_basis_iff : M.Basis ∅ X ↔ X ⊆ M.cl ∅ := by
  rw [basis_iff_indep_cl, and_iff_right M.empty_indep, and_iff_left (empty_subset _)]

-- Sets 

theorem mem_cl_insert (he : e ∉ M.cl X) (hef : e ∈ M.cl (insert f X)) : f ∈ M.cl (insert e X) := by
  rw [cl_eq_cl_inter_ground] at *
  have hfE : f ∈ M.E 
  · by_contra' hfE; rw [insert_inter_of_not_mem hfE] at hef; exact he hef
  have heE : e ∈ M.E := (M.cl_subset_ground _) hef
  rw [insert_inter_of_mem hfE] at hef; rw [insert_inter_of_mem heE]

  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E)
  rw [←hI.cl_eq_cl, hI.indep.not_mem_cl_iff] at he
  rw [←cl_insert_cl_eq_cl_insert, ←hI.cl_eq_cl, cl_insert_cl_eq_cl_insert, he.1.mem_cl_iff] at *
  rw [or_iff_not_imp_left, dep_iff, insert_comm, 
    and_iff_left (insert_subset heE (insert_subset hfE hI.indep.subset_ground)), not_not]
  intro h 
  rw [(h.subset (subset_insert _ _)).mem_cl_iff, or_iff_right (h.not_dep), mem_insert_iff, 
    or_iff_left he.2] at hef
  subst hef; apply mem_insert

theorem cl_exchange (he : e ∈ M.cl (insert f X) \ M.cl X) : f ∈ M.cl (insert e X) \ M.cl X :=
  ⟨mem_cl_insert he.2 he.1, fun hf ↦
    by rwa [cl_insert_eq_of_mem_cl hf, diff_self, iff_false_intro (not_mem_empty _)] at he⟩ 

theorem cl_exchange_iff : e ∈ M.cl (insert f X) \ M.cl X ↔ f ∈ M.cl (insert e X) \ M.cl X :=
  ⟨cl_exchange, cl_exchange⟩

theorem cl_insert_eq_cl_insert_of_mem (he : e ∈ M.cl (insert f X) \ M.cl X) : 
    M.cl (insert e X) = M.cl (insert f X) := by
  have hf := cl_exchange he
  rw [eq_comm, ←cl_cl, ←insert_eq_of_mem he.1, cl_insert_cl_eq_cl_insert, insert_comm, ←cl_cl,  
    ←cl_insert_cl_eq_cl_insert, insert_eq_of_mem hf.1, cl_cl, cl_cl]
  
theorem cl_diff_singleton_eq_cl (h : e ∈ M.cl (X \ {e})) : M.cl (X \ {e}) = M.cl X := by
  refine' (em (e ∈ X)).elim (fun h' ↦ _) (fun h' ↦ by rw [diff_singleton_eq_self h'])
  convert M.cl_insert_cl_eq_cl_insert e (X \ {e}) using 1
  · rw [insert_eq_of_mem h, cl_cl]
  rw [insert_diff_singleton, insert_eq_of_mem h']

theorem mem_cl_diff_singleton_iff_cl (he : e ∈ X) (heE : e ∈ M.E := by aesop_mat) :
    e ∈ M.cl (X \ {e}) ↔ M.cl (X \ {e}) = M.cl X :=
  ⟨cl_diff_singleton_eq_cl, fun h ↦ by rw [h]; exact M.mem_cl_of_mem' he⟩ 

theorem indep_iff_not_mem_cl_diff_forall (hI : I ⊆ M.E := by aesop_mat) :
    M.Indep I ↔ ∀ e ∈ I, e ∉ M.cl (I \ {e}) := by
  use fun h e heI he ↦ ((h.cl_inter_eq_self_of_subset (diff_subset I {e})).subset ⟨he, heI⟩).2 rfl
  intro h
  obtain ⟨J, hJ⟩ := M.exists_basis I
  convert hJ.indep
  refine' hJ.subset.antisymm' (fun e he ↦ by_contra fun heJ ↦ h _ he _)
  exact mem_of_mem_of_subset 
    (hJ.subset_cl he) (M.cl_subset_cl (subset_diff_singleton hJ.subset heJ))

theorem indep_iff_not_mem_cl_diff_forall' : M.Indep I ↔ I ⊆ M.E ∧ ∀ e ∈ I, e ∉ M.cl (I \ {e}) :=
  ⟨fun h ↦ ⟨h.subset_ground, (indep_iff_not_mem_cl_diff_forall h.subset_ground).mp h⟩, fun h ↦
    (indep_iff_not_mem_cl_diff_forall h.1).mpr h.2⟩

theorem indep_iff_cl_diff_ne_forall : M.Indep I ↔ ∀ e ∈ I, M.cl (I \ {e}) ≠ M.cl I := by
  rw [indep_iff_not_mem_cl_diff_forall']
  refine' ⟨fun ⟨hIE, h⟩ e heI h_eq ↦ h e heI (h_eq.symm.subset (M.mem_cl_of_mem heI)), 
    fun h ↦ ⟨fun e heI ↦ by_contra fun heE ↦ h e heI _,fun e heI hin ↦ h e heI (by rw [cl_diff_singleton_eq_cl hin])⟩⟩ 
  rw [cl_eq_cl_inter_ground, inter_comm, inter_diff_distrib_left, 
    inter_singleton_eq_empty.mpr heE, diff_empty, inter_comm, ←cl_eq_cl_inter_ground]

lemma indep_iff_cl_ssubset_ssubset_forall (hI : I ⊆ M.E := by aesop_mat) :
    M.Indep I ↔ (∀ J, J ⊂ I → M.cl J ⊂ M.cl I) := by  
  rw [indep_iff_not_mem_cl_diff_forall]
  refine' ⟨fun h J hJI ↦ (M.cl_subset_cl hJI.subset).ssubset_of_ne (fun h_eq ↦ _), 
    fun h e heI hin ↦ _⟩
  · obtain ⟨e,heJ,h'⟩ := ssubset_iff_insert.1 hJI
    apply h e (h' (mem_insert _ _))
    have heI := M.mem_cl_of_mem (h' (mem_insert e J))
    rw [←h_eq] at heI
    refine' mem_of_mem_of_subset heI (M.cl_subset_cl _)
    rw [subset_diff, disjoint_singleton_right, and_iff_left heJ]
    exact (subset_insert _ _).trans h'
  refine' (h (I \ {e}) (diff_singleton_sSubset.2 heI)).ne _
  rw [←cl_cl, ←insert_eq_of_mem hin, cl_insert_cl_eq_cl_insert, insert_diff_singleton, 
    insert_eq_of_mem heI]
    
theorem eq_of_cl_eq_cl_forall {M₁ M₂ : Matroid α} (h : ∀ X, M₁.cl X = M₂.cl X) : M₁ = M₂ :=
  eq_of_indep_iff_indep_forall (by simpa using h univ) 
    (fun _ _ ↦ by simp_rw [indep_iff_cl_diff_ne_forall, h])
  
  
section Spanning

variable {S T : Set α}

/-- A set is `spanning` in `M` if its closure is equal to `M.E`, or equivalently if it contains 
  a base of `M`. -/
def Spanning (M : Matroid α) (S : Set α) := M.cl S = M.E ∧ S ⊆ M.E

@[aesop unsafe 10% (rule_sets [Matroid])]
theorem Spanning.subset_ground (hS : M.Spanning S) : S ⊆ M.E :=
  hS.2

theorem Spanning.cl_eq (hS : M.Spanning S) : M.cl S = M.E :=
  hS.1

theorem spanning_iff_cl (hS : S ⊆ M.E := by aesop_mat) : M.Spanning S ↔ M.cl S = M.E :=
  ⟨And.left, fun h ↦ ⟨h, hS⟩⟩

theorem not_spanning_iff_cl (hS : S ⊆ M.E := by aesop_mat) : ¬M.Spanning S ↔ M.cl S ⊂ M.E := by
  rw [spanning_iff_cl, ssubset_iff_subset_ne, Ne.def, iff_and_self,
    iff_true_intro (M.cl_subset_ground _)]
  exact fun _ ↦ trivial

theorem Spanning.supset (hS : M.Spanning S) (hST : S ⊆ T) (hT : T ⊆ M.E := by aesop_mat) :
    M.Spanning T :=
  ⟨(M.cl_subset_ground _).antisymm (by rw [←hS.cl_eq]; exact M.cl_subset_cl hST), hT⟩
  
theorem Spanning.union_left (hS : M.Spanning S) (hX : X ⊆ M.E := by aesop_mat) :
    M.Spanning (S ∪ X) :=
  hS.supset (subset_union_left _ _)

theorem Spanning.union_right (hS : M.Spanning S) (hX : X ⊆ M.E := by aesop_mat) :
    M.Spanning (X ∪ S) :=
  hS.supset (subset_union_right _ _)

theorem Base.spanning (hB : M.Base B) : M.Spanning B :=
  ⟨hB.cl_eq, hB.subset_ground⟩

theorem ground_spanning (M : Matroid α) : M.Spanning M.E :=
  ⟨M.cl_ground, rfl.subset⟩

theorem Base.supset_spanning (hB : M.Base B) (hBX : B ⊆ X) (hX : X ⊆ M.E := by aesop_mat) : 
    M.Spanning X:= 
  hB.spanning.supset hBX

theorem spanning_iff_supset_base' : M.Spanning S ↔ (∃ B, M.Base B ∧ B ⊆ S) ∧ S ⊆ M.E := by 
  refine' ⟨fun h ↦ ⟨_, h.subset_ground⟩, fun ⟨⟨B, hB, hBS⟩, hSE⟩ ↦ hB.spanning.supset hBS⟩
  obtain ⟨B, hB⟩ := M.exists_basis S
  have hB' := hB.basis_cl_right
  rw [h.cl_eq, basis_ground_iff] at hB'
  exact ⟨B, hB', hB.subset⟩ 

theorem spanning_iff_supset_base (hS : S ⊆ M.E := by aesop_mat) : 
    M.Spanning S ↔ ∃ B, M.Base B ∧ B ⊆ S := by 
  rw [spanning_iff_supset_base', and_iff_left hS]

theorem coindep_iff_compl_spanning (hI : I ⊆ M.E := by aesop_mat) :
    M.Coindep I ↔ M.Spanning (M.E \ I) := by
  rw [Coindep, spanning_iff_supset_base, and_iff_left hI]
  simp_rw [subset_diff, ←and_assoc, and_iff_left_of_imp Base.subset_ground, disjoint_comm]



-- /- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
-- theorem spanning_iff_compl_coindep
--     (hI : S ⊆ M.E := by
--       run_tac
--         ssE) :
--     M.Spanning S ↔ M.Coindep (M.E \ S) := by simp [coindep_iff_compl_spanning]
-- #align matroid_in.spanning_iff_compl_coindep Matroid.spanning_iff_compl_coindep

-- theorem Coindep.compl_spanning (hI : M.Coindep I) : M.Spanning (M.E \ I) :=
--   coindep_iff_compl_spanning.mp hI
-- #align matroid_in.coindep.compl_spanning Matroid.Coindep.compl_spanning

-- theorem Spanning.compl_coindep (hS : M.Spanning S) : M.Coindep (M.E \ S) :=
--   spanning_iff_compl_coindep.mp hS
-- #align matroid_in.spanning.compl_coindep Matroid.Spanning.compl_coindep

-- /- ./././Mathport/Syntax/Translate/Tactic/Builtin.lean:69:18: unsupported non-interactive tactic ssE -/
-- theorem coindep_iff_cl_compl_eq_ground
--     (hK : X ⊆ M.E := by
--       run_tac
--         ssE) :
--     M.Coindep X ↔ M.cl (M.E \ X) = M.E := by rw [coindep_iff_compl_spanning, spanning_iff_cl]
-- #align matroid_in.coindep_iff_cl_compl_eq_ground Matroid.coindep_iff_cl_compl_eq_ground

-- theorem Coindep.cl_compl (hX : M.Coindep X) : M.cl (M.E \ X) = M.E :=
--   (coindep_iff_cl_compl_eq_ground hX.subset_ground).mp hX
-- #align matroid_in.coindep.cl_compl Matroid.Coindep.cl_compl

-- end Spanning
    

  
  
  


  



section modular

variable {Xs Ys : Set (Set α)} 

def Modular (M : Matroid α) (Xs : Set (Set α)) (I : Set α) := 
  M.Base I ∧ ∀ ⦃Ys⦄, Ys ⊆ Xs → Ys.Nonempty → M.Basis ((⋂₀ Ys) ∩ I) (⋂₀ Ys)
pp_extended_field_notation Modular

theorem Modular.base (h : M.Modular Xs I) : M.Base I := h.1

theorem Modular.indep (h : M.Modular Xs I) : M.Indep I := h.1.indep

theorem Modular.forall (h : M.Modular Xs I) (hYs : Ys ⊆ Xs) (hne : Ys.Nonempty):
    M.Basis ((⋂₀ Ys) ∩ I) (⋂₀ Ys) := 
  h.2 hYs hne

theorem Modular.inter_basis_of_mem (h : M.Modular Xs I) (hX : X ∈ Xs) : M.Basis (X ∩ I) X := by
  convert h.forall (singleton_subset_iff.mpr hX) (by simp); simp; simp

theorem Modular.subset (h : M.Modular Xs I) (hYs : Ys ⊆ Xs) : M.Modular Ys I := 
  ⟨h.base, fun _ hZs hne ↦ h.forall (hZs.trans hYs) hne⟩ 

@[aesop unsafe 5% (rule_sets [Matroid])]
theorem Modular.sInter_subset_ground (h : M.Modular Xs I) (hYs : Ys ⊆ Xs) (hne : Ys.Nonempty) : 
    ⋂₀ Ys ⊆ M.E :=
  (h.forall hYs hne).subset_ground

@[aesop unsafe 5% (rule_sets [Matroid])]
theorem Modular.mem_subset_ground (h : M.Modular Xs I) (hX : X ∈ Xs) : X ⊆ M.E := by
  convert h.sInter_subset_ground (Ys := {X}) (by simpa) (by simp); simp

@[aesop unsafe 5% (rule_sets [Matroid])]
theorem Modular.sUnion_subset_ground (h : M.Modular Xs I) : ⋃₀ Xs ⊆ M.E := by
  rw [sUnion_subset_iff]; exact fun X hX ↦ h.mem_subset_ground hX

theorem modular_of_sUnion_indep (h : M.Indep (⋃₀ Xs)) : ∃ I, M.Modular Xs I := by
  obtain ⟨I, hI, huI⟩ := h.exists_base_supset
  refine' ⟨I, hI, fun Ys hYs ⟨Y, hY⟩ ↦ _⟩
  have hss : ⋂₀ Ys ⊆ I := ((sInter_subset_of_mem hY).trans (subset_sUnion_of_mem hY)).trans 
    ((sUnion_subset_sUnion hYs).trans huI)
  rw [inter_eq_self_of_subset_left hss]
  exact (hI.indep.subset hss).basis_self
  
theorem Modular.basis_sUnion (h : M.Modular Xs I) : M.Basis (⋃₀ Xs ∩ I) (⋃₀ Xs) := by 
  refine' Indep.basis_of_subset_of_subset_cl (h.indep.inter_left _) (inter_subset_left _ _)
    (sUnion_subset (fun X hX ↦ _))
  have hb := h.inter_basis_of_mem hX
  rw [←cl_subset_cl_iff_subset_cl, ←hb.cl_eq_cl]
  exact M.cl_subset_cl (inter_subset_inter_left _ (subset_sUnion_of_mem hX))

theorem Modular.basis_sUnion_of_subset (h : M.Modular Xs I) (hYs : Ys ⊆ Xs) : 
    M.Basis (⋃₀ Ys ∩ I) (⋃₀ Ys) :=
  (h.subset hYs).basis_sUnion

theorem sInter_subset_sUnion (hXs : Xs.Nonempty) : ⋂₀ Xs ⊆ ⋃₀ Xs := 
  (sInter_subset_of_mem hXs.some_mem).trans (subset_sUnion_of_mem hXs.some_mem)
  
theorem iInter_cl_eq_cl_sInter_of_modular
    (hXs : ∃ I, M.Modular Xs I) (hne : Xs.Nonempty) : (⋂ X ∈ Xs, M.cl X) = M.cl (⋂₀ Xs) := by
  obtain ⟨I, hI⟩ := hXs
  have := hne.coe_sort
  have eq1 : (⋂ X ∈ Xs, M.cl X) = (⋂ X ∈ Xs, M.cl (X ∩ I))
  · convert rfl using 4 with X hX; rw [(hI.inter_basis_of_mem hX).cl_eq_cl]  
  rw [eq1, ←biInter_image, ←hI.indep.cl_sInter_eq_iInter_cl_of_forall_subset, 
    ←(hI.forall rfl.subset hne).cl_eq_cl, eq_comm, sInter_eq_iInter, iInter_inter]
  · convert rfl; simp
  · apply hne.image
  simp

theorem Indep.cl_diff_singleton_sSubset (hI : M.Indep I) (he : e ∈ I) : M.cl (I \ {e}) ⊂ M.cl I :=
  ssubset_of_subset_of_ne (M.cl_mono (diff_subset _ _)) (indep_iff_cl_diff_ne_forall.mp hI _ he)


end modular

end Matroid





-- -- section from_axioms
-- -- lemma cl_diff_singleton_eq_cl' (cl : set α → set α) (M.subset_cl : ∀ X, X ⊆ cl X)
-- -- (cl_mono : ∀ X Y, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X )
-- -- {x : α} {I : set α} (h : x ∈ cl (I \ {x})) :
-- --   cl (I \ {x}) = cl I :=
-- -- begin
-- --   refine (cl_mono _ _ (diff_subset _ _)).antisymm _,
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
-- --   rw [←insert_diff_singleton_comm hne] at hfcl, 
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
-- -- (λ I hI, ⟨to_finite _, by { rw [←ncard_univ], exact ncard_le_of_subset (subset_univ _) }⟩) 
-- -- @[simp] lemma matroid_of_cl_of_finite_apply [finite E] (cl : set α → set α) 
-- -- (M.subset_cl : ∀ X, X ⊆ cl X )
-- -- (cl_mono : ∀ ⦃X Y⦄, X ⊆ Y → cl X ⊆ cl Y) (cl_idem : ∀ X, cl (cl X) = cl X)
-- -- (cl_exchange : ∀ (X e f), f ∈ cl (insert e X) \ cl X → e ∈ cl (insert f X) \ cl X) :
-- -- (matroid_of_cl_of_finite cl M.subset_cl cl_mono cl_idem cl_exchange).cl = cl :=
-- -- by simp [matroid_of_cl_of_finite] 
-- -- end from_axioms
-- end Matroid

