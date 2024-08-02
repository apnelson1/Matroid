import Matroid.Constructions.Matching
import Matroid.Constructions.Sum
import Mathlib.Order.Disjointed
import Matroid.Constructions.Submodular
import Matroid.Rank
import Mathlib.Algebra.BigOperators.Ring


namespace Matroid

universe u

variable {α ι β: Type*}

open Set

def AdjIndep' (M : Matroid α) (Adj : α → β → Prop) (I : Set β) :=
  I = ∅ ∨ ∃ (I₀ : Set α) (f : β → α), M.Indep I₀ ∧ IsMatching Adj f I₀ I

@[simp] lemma adjMap_indep_iff' [DecidableEq β] [Fintype β] (M : Matroid α) (Adj : α → β → Prop)
  (E : Set β) {I : Set β} : (M.adjMap Adj E).Indep I ↔ M.AdjIndep' Adj I ∧ (I : Set β) ⊆ E := by
  classical
  simp [AdjIndep', adjMap, IndepMatroid.ofFinset, AdjIndep]
  refine fun hIE ↦ ⟨fun h ↦ ?_, fun h J hJ ↦ ?_⟩
  · obtain h | h := h I.toFinset (coe_toFinset I).subset
    simp only [toFinset_eq_empty.mp h, true_or]
    obtain ⟨I₀, hi, hm⟩ := h
    right
    refine ⟨I₀, hi, (coe_toFinset I) ▸ hm⟩
  · obtain rfl | hem := eq_or_ne I ∅
    · simp only [Finset.coe_eq_empty.mp (subset_eq_empty hJ rfl), Finset.coe_empty, true_or]
    · simp only [hem, false_or] at h
      obtain ⟨I₀, hi, ⟨f, hm⟩⟩ := h
      right
      refine ⟨Finset.image f J, Matroid.Indep.subset hi ((BijOn.image_eq hm.1) ▸ ?_), ⟨f, ?_, ?_⟩⟩
      simp only [Finset.coe_image, image_subset_iff]
      exact subset_trans hJ (subset_preimage_image _ _)
      simp only [Finset.coe_image]
      exact BijOn.subset_left hm.1 hJ
      refine fun v hv ↦ hm.2 v (hJ hv)


def N_singleton (Adj : α → β → Prop) (v : β) := {u | Adj u v}
def N (Adj : α → β → Prop) (V : Set β) := {u | ∃ v ∈ V, Adj u v}

protected def Union [DecidableEq α] (Ms : ι → Matroid α) : Matroid α :=
  (Matroid.sum' Ms).adjMap (fun x y ↦ x.2 = y) univ

protected def union [DecidableEq α] (M : Matroid α) (N : Matroid α) : Matroid α :=
  Matroid.Union (Bool.rec M N)

@[simp] lemma Union_empty [DecidableEq α] [IsEmpty ι] (Ms : ι → Matroid α) :
    Matroid.Union Ms = loopyOn univ := by
  simp [eq_iff_indep_iff_indep_forall, Matroid.Union, adjMap, IndepMatroid.ofFinset, AdjIndep]
  sorry
-- protected def TwoUnion [DecidableEq α] (M₁ : Matroid α) (M₂ : Matroid α) : Matroid α :=
--   (M₁.sum M₂).adjMap (fun x y ↦  x = .inl y ∨ x = .inr y) univ


lemma union_indep [DecidableEq α] [Fintype α] [Nonempty ι] {Ms : ι → Matroid α} {I : Set α}
    (hI : (Matroid.Union Ms).Indep I) :
    ∃ Is : ι → Set α, ⋃ (i : ι), Is i = (I : Set α) ∧ ∀ (i : ι), (Ms i).Indep (Is i) := by
    simp only [Matroid.Union, adjMap_indep_iff', AdjIndep', sum'_indep_iff, exists_and_left,
    subset_univ, and_true] at hI
    obtain heq | hne := eq_or_ne I ∅
    · refine ⟨(fun _ ↦ ∅), by simp only [iUnion_empty, heq, empty_indep, implies_true,
        and_self]⟩
    · simp only [hne, false_or] at hI
      obtain ⟨I', h, ⟨f, hB, hAdj⟩⟩ := hI
      refine ⟨(fun i ↦ (Prod.mk i ⁻¹' I') : ι → Set α), (BijOn.image_eq hB) ▸ ?_, h⟩
      refine subset_antisymm (fun v hv ↦ ?_) (fun v hv ↦ ?_)
      · simp only [mem_iUnion, mem_preimage, mem_image] at hv
        obtain ⟨i, x, hx, h⟩ := hv
        specialize hAdj x hx
        simp only [h ▸ hAdj ▸ hx]
      · specialize hAdj v hv
        simp only [mem_iUnion, mem_preimage, mem_image]
        refine ⟨(f v).1, v, hv, ?_⟩
        nth_rw 3 [← hAdj]

lemma finset_union_indep [DecidableEq α] [Fintype α] [Nonempty ι] {Ms : ι → Matroid α}
  {I : Finset α} (hI : (Matroid.Union Ms).Indep I) : ∃ Is : ι → Finset α,
  ⋃ (i : ι), Is i = (I : Set α)  ∧ ∀ i : ι , (Ms i).Indep (Is i) := by
  classical
  obtain ⟨Is, hIs, hI⟩ := union_indep hI
  refine ⟨fun i ↦ (Is i).toFinset, by simp only [coe_toFinset, hIs],
    by simp only [coe_toFinset, hI, implies_true]⟩

lemma union_indep' [DecidableEq α] [Fintype α] {Ms : ι → Matroid α}
  {I : Set α} (Is : ι → Set α) (hD : univ.PairwiseDisjoint Is)
  (hI : ⋃ (i : ι), Is i = (I : Set α) ∧ ∀ (i : ι), (Ms i).Indep (Is i)) :
    (Matroid.Union Ms).Indep I := by
    obtain hα | hα := isEmpty_or_nonempty α
    · simp [eq_empty_of_isEmpty I]
    obtain hι | hι := isEmpty_or_nonempty ι
    · sorry
    simp only [Matroid.Union, adjMap_indep_iff', AdjIndep', subset_univ, and_true]
    obtain rfl | h := eq_or_ne I ∅
    · simp only [true_or]
    · simp only [h, exists_and_left, false_or, sum'_indep_iff]
      refine ⟨{(i, v) | (i ∈ univ) ∧ v ∈ Is i}, fun i ↦ ?_, ?_⟩
      simp only [mem_univ, true_and, preimage_setOf_eq, setOf_mem_eq, hI.2 i]
      simp_rw [IsMatching, mem_univ, true_and]
      set f := fun x : ι × α ↦ x.2 with hf
      have himage : I = f '' {x : ι × α | x.2 ∈ Is x.1} := by
        rw [← hI.1]
        simp_all only [ne_eq, f]
        obtain ⟨left, _⟩ := hI
        subst left
        simp_all only [iUnion_eq_empty, not_forall]
        ext1 x
        simp_all only [mem_iUnion, mem_image, mem_setOf_eq, Prod.exists, exists_eq_right]
      have hinj: InjOn f {x : ι × α | x.2 ∈ Is x.1} := by
        refine fun x hx y hy hxy ↦ ?_
        simp only [hf] at hxy
        simp only [mem_setOf_eq] at hx hy
        obtain h := PairwiseDisjoint.elim_set hD (mem_univ x.1)
          (mem_univ y.1) x.2 hx (hxy ▸ hy)
        obtain ⟨_, _⟩ := x
        obtain ⟨_, _⟩ := y
        simp_all only
      obtain h := himage ▸ InjOn.bijOn_image hinj
      refine ⟨Function.invFunOn f {x | x.2 ∈ Is x.1},
        BijOn.symm (InvOn.symm (BijOn.invOn_invFunOn h)) h, fun v hv ↦ ?_⟩
      simp only [show (Function.invFunOn f {x | x.2 ∈ Is x.1} v).2 =
        f (Function.invFunOn f {x | x.2 ∈ Is x.1} v) by rfl, Function.invFunOn_eq (himage ▸ hv)]

lemma finset_union_indep' [DecidableEq α] [Fintype α] [Nonempty ι] [Nonempty α] {Ms : ι → Matroid α}
    {I : Finset α} (Is : ι → Finset α) (hD : univ.PairwiseDisjoint Is)
    (hI : (⋃ (i : ι), Is i) = (I : Set α) ∧ ∀ (i : ι), (Ms i).Indep (Is i)) :
    (Matroid.Union Ms).Indep I := by
  apply union_indep' (fun i ↦ Is i) (by simpa)
  simp [← hI.1, coe_toFinset, true_and, hI.2]

lemma union_indep_iff_aux [DecidableEq α] [Fintype α] [Nonempty α] {Ms : ℕ → Matroid α} {I : Set α} :
    (Matroid.Union Ms).Indep I ↔
    ∃ Is : ℕ → Set α, ⋃ (i : ℕ), Is i = (I : Set α) ∧ ∀ (i : ℕ), (Ms i).Indep (Is i) := by
    refine iff_def'.mpr ⟨fun ⟨Is, hU, hI⟩ ↦ ?_, union_indep⟩
    set Js := disjointed Is with hJ
    refine union_indep' Js (Pairwise.set_pairwise (hJ ▸ (disjoint_disjointed Is)) univ)
      ⟨by simp [hJ ▸ iUnion_disjointed ▸ hU],
      fun i ↦ Matroid.Indep.subset (hI i) (disjointed_subset Is i)⟩

-- lemma union_indep_iff [DecidableEq α] [Fintype α] [Nonempty α] {Ms : ι → Matroid α} {I : Set α} :
--     (Matroid.Union Ms).Indep I ↔
--     ∃ Is : ι → Set α, ⋃ i, Is i = (I : Set α) ∧ ∀ i, (Ms i).Indep (Is i) := by

lemma finunion_indep_iff [DecidableEq α] [Fintype α] [Fintype ι] [Nonempty α] [Nonempty ι]
  {Ms : ι → Matroid α} {I : Finset α} : (Matroid.Union Ms).Indep I ↔
    ∃ Is : ι → Finset α, ⋃ (i : ι), Is i = (I : Set α) ∧ ∀ (i : ι), (Ms i).Indep (Is i) := by
    sorry


lemma twounion_indep_iff [DecidableEq α] [Fintype α] [Nonempty α] {M₁ : Matroid α} {M₂ : Matroid α}
  {I : Set α} :
  (Matroid.union M₁ M₂).Indep I ↔ ∃ I₁ I₂, I = I₁ ∪ I₂ ∧ M₁.Indep I₁ ∧ M₂.Indep I₂ := by
  sorry


-- lemma twounion_indep_iff [DecidableEq α] [Fintype α] [Nonempty α] {M₁ : Matroid α} {M₂ : Matroid α}
--   {I : Set α} :
--   (Matroid.TwoUnion M₁ M₂).Indep I ↔ ∃ I₁ I₂, I = I₁ ∪ I₂ ∧ M₁.Indep I₁ ∧ M₂.Indep I₂ := by
--   classical
--   simp only [Matroid.TwoUnion, adjMap_indep_iff', AdjIndep', sum_indep_iff, exists_and_left,
--     subset_univ, and_true]
--   refine Iff.intro (fun hI ↦ ?_) (fun hI ↦ ?_)
--   · obtain rfl | hne := eq_or_ne I ∅
--     · refine ⟨ ∅, ∅, by simp only [union_self, empty_indep, and_self]⟩
--     · simp only [hne, false_or] at hI
--       obtain ⟨I', ⟨hI1, hI2⟩, ⟨f, hb, hadj⟩⟩ := hI
--       refine ⟨Sum.inl ⁻¹' (I' : Set (α ⊕ α)), Sum.inr ⁻¹' (I' : Set (α ⊕ α)), ?_,  hI1, hI2⟩
--       simp only [← BijOn.image_eq hb]
--       refine subset_antisymm (fun v hv ↦ ?_) (fun v hv ↦ ?_)
--       · specialize hadj v hv
--         simp only [mem_union, mem_preimage, mem_image]
--         obtain inl | inr := hadj
--         left
--         exact ⟨v, hv, inl⟩
--         right
--         exact ⟨v, hv, inr⟩
--       · simp only [mem_union, mem_preimage, mem_image] at hv
--         obtain ⟨x, hx, inl⟩ | ⟨x, hx, inr⟩ := hv
--         · specialize hadj x hx
--           obtain inl' | inr' := hadj
--           · rw [inl,  Sum.inl.inj_iff] at inl'
--             exact inl' ▸ hx
--           · simp only [inl] at inr'
--         · specialize hadj x hx
--           obtain inl' | inr' := hadj
--           · simp only [inr] at inl'
--           · rw [inr,  Sum.inr.inj_iff] at inr'
--             exact inr' ▸ hx
--   · obtain rfl | hne := eq_or_ne I ∅
--     · simp only [true_or]
--     · simp only [hne, false_or]
--       obtain ⟨I₁,I₂, hI, hI1, hI2⟩ := hI
--       rw [← union_diff_self] at hI
--       rw [hI]
--       refine ⟨(.inl '' I₁) ∪ (.inr '' (I₂ \ I₁)), ⟨?_, ?_⟩,
--         fun x ↦ if x ∈ I₁ then .inl x else .inr x, ⟨fun x hx ↦ ?_ , ?_, ?_⟩, fun v hv ↦ ?_⟩
--       · simp only [preimage_union, preimage_inl_image_inr, union_empty, preimage_image_eq
--           I₁ Sum.inl_injective, hI1]
--       · simp only [preimage_union, preimage_inr_image_inl, empty_union,
--           preimage_image_eq (I₂ \ I₁) Sum.inr_injective,  Matroid.Indep.subset hI2 diff_subset]
--       · simp only [mem_union, mem_image]
--         obtain h1 | h2 := hx
--         · left
--           refine ⟨x, h1, by simp only [h1, ↓reduceIte]⟩
--         · right
--           refine ⟨x, h2, by simp only [h2.2, ↓reduceIte]⟩
--       · refine fun x hx y hy hxy ↦ ?_
--         obtain hx | hx := hx
--         · obtain hy | hy := hy
--           · simpa only [hx, ↓reduceIte, hy, Sum.inl.injEq] using hxy
--           · simp only [hx, ↓reduceIte, hy.2] at hxy
--         · obtain hy | hy := hy
--           · simp only [hx.2, ↓reduceIte, hy] at hxy
--           · simpa only [hx.2, ↓reduceIte, hy.2, Sum.inr.injEq] using hxy
--       · refine fun x hx ↦ ?_
--         simp only [union_diff_self, mem_image, mem_union]
--         obtain inl | inr := hx
--         · simp only [mem_image] at inl
--           obtain ⟨x', hx', inl⟩ := inl
--           refine ⟨x', by simp only [hx', true_or], by simp only [hx', ↓reduceIte, inl]⟩
--         · simp only [mem_image] at inr
--           obtain ⟨x', hx', inr⟩ := inr
--           refine ⟨x', by simp only [hx'.1, or_true], by simp only [hx'.2, ↓reduceIte, inr]⟩
--       · simp only [ite_eq_left_iff, imp_false, Decidable.not_not, ite_eq_right_iff, imp_false]
--         tauto

noncomputable def PolymatroidFn_of_r (M : Matroid α) (_ : M.Finite): PolymatroidFn M.r where
  submodular := M.r_submod
  mono := M.r_mono
  zero_at_bot := M.r_empty

@[simp] theorem sum'_er_eq_er_sum_on_indep {α ι : Type*} [Fintype ι] [Fintype α]
  {Ms : ι → Matroid α} {I : Set (ι × α)} (h : (Matroid.sum' Ms).Indep I):
  (Matroid.sum' Ms).er I = ∑ i : ι, (Ms i).er (Prod.mk i ⁻¹' I) := by
  classical
  rw [Indep.er h]
  simp only [sum'_indep_iff] at h
  simp_rw [Indep.er (h _)]
  set f := fun x : ι × α ↦ x.1
  rw [← Finite.cast_ncard_eq I.toFinite,  I.ncard_eq_toFinset_card']
  rw [Finset.card_eq_sum_card_fiberwise (by refine fun x _ ↦ Finset.mem_univ (f x))]
  have himage : ∀ i : ι, (fun x : ι × α ↦ x.2) '' (Finset.filter (fun x ↦ f x = i) I.toFinset)
    = (Finset.filter (fun v ↦ (i, v) ∈ I) Finset.univ) := by
    refine fun i ↦ subset_antisymm ?_ ?_
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and, image_subset_iff,
        preimage_setOf_eq, setOf_subset_setOf, and_imp, Prod.forall, f]
      refine fun a b h h' ↦ mem_toFinset.mp (h' ▸ h)
    · refine fun x hx ↦ ?_
      simp only [Finset.coe_filter, mem_image, mem_setOf_eq, Prod.exists, exists_eq_right]
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, mem_setOf_eq] at hx
      exact mem_toFinset.mpr hx
  have hinj: ∀ i : ι, InjOn (fun x : ι × α ↦ x.2) (Finset.filter (fun x ↦ f x = i) I.toFinset)
    := by
    intro i x hx y hy hxy
    simp only [Finset.coe_filter, mem_setOf_eq, f] at hx hy
    simp only at hxy
    obtain ⟨_, _⟩ := x
    obtain ⟨_, _⟩ := y
    simp_all only
  obtain hcard := fun i : ι ↦ ncard_coe_Finset (Finset.filter (fun x_1 ↦ (i, x_1) ∈ I)
    Finset.univ) ▸ ncard_coe_Finset (Finset.filter (fun x ↦ f x = i) I.toFinset) ▸ (himage i) ▸
    ncard_image_of_injOn <| (hinj i)
  simp only [preimage]
  have : ∀ i, {x_1 | (i, x_1) ∈ I}.ncard =
    (Finset.filter (fun x_1 ↦ (i, x_1) ∈ I) Finset.univ).card := by
    intro i
    rw [ncard_eq_toFinset_card' ]
    simp only [mem_setOf_eq, toFinset_setOf]
  simp only [← Finite.cast_ncard_eq {x_1 | (_, x_1) ∈ I}.toFinite, this, hcard, Nat.cast_sum]


@[simp] theorem sum'_er_eq_er_sum {α ι : Type*} [Fintype ι] [Fintype α]
  (Ms : ι → Matroid α) (X : Set (ι × α)):
  (Matroid.sum' Ms).er X = ∑ i : ι, (Ms i).er (Prod.mk i ⁻¹' X) := by
  obtain ⟨I , hI⟩ := (Matroid.sum' Ms).exists_basis' X
  have : ∀ i : ι, (Ms i).Basis' (Prod.mk i ⁻¹' I) (Prod.mk i ⁻¹' X)  := by
    intro i
    simp_all only [Basis', maximals, mem_setOf_eq, and_imp]
    refine ⟨⟨sum'_indep_iff.mp hI.1.1 i, preimage_mono hI.1.2⟩, fun b hIb h h'↦ ?_⟩
    have : (∀ (j : ι), (Ms j).Indep (Prod.mk j ⁻¹' (I ∪ (Prod.mk i '' b)))) := by
      intro j
      by_cases h: j = i
      · rw [h, preimage_union]
        exact Matroid.Indep.subset hIb (union_subset h'
          (b.preimage_image_eq (Prod.mk.inj_left i)).subset)
      · have : (Prod.mk j ⁻¹' (Prod.mk i '' b)) = ∅ := by
          refine subset_antisymm (fun x hx ↦  ?_) (empty_subset _)
          simp only [mem_preimage, mem_image, Prod.mk.injEq, exists_eq_right_right] at hx
          simp only [mem_empty_iff_false]
          simp_all only [not_true_eq_false]
        simp only [preimage_union, this, union_empty, sum'_indep_iff.mp hI.1.1 j]
    obtain h'' := hI.2 (sum'_indep_iff.mpr this)
      (union_subset hI.1.2 (subset_trans (image_mono h) (image_preimage_subset _ _)))
      subset_union_left
    exact subset_trans (subset_preimage_image _ _)
      (preimage_mono (union_subset_iff.mp h'').2)
  simp_rw [← Basis'.er hI, ← Basis'.er (this _)]
  exact sum'_er_eq_er_sum_on_indep hI.1.1

@[simp] theorem sum'_r_eq_r_sum {α ι : Type*} [Fintype ι] [Fintype α]
  (Ms : ι → Matroid α) (X : Set (ι × α)):
  (Matroid.sum' Ms).r X = ∑ i : ι, (Ms i).r (Prod.mk i ⁻¹' X) := by
  obtain h := sum'_er_eq_er_sum Ms X
  rw [← Nat.cast_inj (R := ENat)]
  convert h
  rw [coe_r_eq]
  rw [Nat.cast_sum]
  simp_rw [coe_r_eq]



theorem polymatroid_of_adjMap [DecidableEq β] [Nonempty α] [Fintype α] [Fintype β] (M : Matroid α)
 (Adj : α → β → Prop) : ∃f, ∃h : (PolymatroidFn f), ofPolymatroidFn h = M.adjMap Adj univ ∧
 ∀ Y,  f Y = M.r {v | ∃ u ∈ Y, Adj v u} := by
 classical
  set N := fun i ↦ (N_singleton Adj i).toFinset
  set f := fun I : Finset β ↦ (M.r (I.biUnion N) : ℤ) with hf
  have hf_poly : PolymatroidFn f := by
    refine ⟨fun X Y ↦ hf ▸ ?_, ?_, ?_⟩
    · simp only [Finset.inf_eq_inter, Finset.sup_eq_union]
      have : ((X ∪ Y).biUnion N) =
        X.biUnion N ∪ Y.biUnion N:= by aesop
      rw [← Nat.cast_add ,← Nat.cast_add, Nat.cast_le]
      refine (le_trans
        ((Finset.coe_union (X.biUnion N) (Y.biUnion N)) ▸ this ▸
        (add_le_add_right  (M.r_mono ?_) _)) (M.r_submod _ _))
      simp only [Finset.coe_biUnion, Finset.coe_inter, mem_inter_iff, Finset.mem_coe,
        N_singleton, le_eq_subset, subset_inter_iff, iUnion_subset_iff, and_imp,
        mem_setOf_eq, toFinset_setOf, Finset.coe_filter, Finset.mem_univ, true_and]
      refine ⟨fun x h1 _ y h3 ↦ ?_, fun x _ h2 y h3 ↦ ?_⟩
      simp only [mem_iUnion, mem_setOf_eq, exists_prop]
      exact ⟨x, ⟨h1, h3⟩⟩
      simp only [mem_iUnion, mem_setOf_eq, exists_prop]
      exact ⟨x, ⟨h2, h3⟩⟩
    · refine fun X Y h ↦ hf ▸ Nat.cast_le.mpr (M.r_mono ?_)
      simp only [le_eq_subset, Finset.coe_biUnion, Finset.mem_coe, iUnion_subset_iff]
      refine fun x h1 y h2 ↦ ?_
      simp only [mem_iUnion, exists_prop]
      exact ⟨x, h h1, h2⟩
    · simp only [hf, Finset.bot_eq_empty, Finset.biUnion_empty, Finset.coe_empty, r_empty,
        Nat.cast_zero]

  have heq : ∀ I : Finset β , (ofPolymatroidFn hf_poly).Indep I ↔ (M.adjMap Adj univ).Indep I := by
    intro I
    simp only [IndepMatroid.ofFinset_indep, adjMap_indep_iff, Finset.coe_subset,
      indep_ofPolymatroidFn_iff]
    refine iff_def'.mpr ⟨fun ha I' hI' _ ↦ hf ▸ ?_, fun hp ↦ ?_⟩
    · simp only [Nat.cast_le]
      obtain h | _ := ha.1
      · obtain h := Finset.subset_empty.mp (h ▸ hI')
        simp only [h, Finset.card_empty, Finset.biUnion_empty, Finset.coe_empty, r_empty, le_refl]
      · obtain h | ⟨I₀, f, h', h''⟩ := (AdjIndep.subset ha.1 hI')
        · simp only [h, Finset.card_empty, Finset.biUnion_empty, Finset.coe_empty, r_empty, le_refl]
        · obtain h := IsMatching.card_eq h''
          rw [← h, ← ncard_coe_Finset I₀ , ← Indep.r h']
          apply r_mono
          refine fun x hx ↦ mem_setOf_eq ▸ ?_
          rw [← BijOn.image_eq (IsMatching.bijOn h''), image, mem_setOf_eq] at hx
          obtain ⟨u, hu, hadj⟩ := hx
          simp only [Finset.mem_biUnion, N_singleton]
          refine ⟨u, hu, ?_⟩
          simp only [N_singleton, N, mem_setOf_eq, toFinset_setOf, Finset.mem_filter,
            Finset.mem_univ, true_and]
          exact hadj ▸ (IsMatching.adj h'' hu)

    obtain h := (rado M <| fun i : ↑I ↦ (N_singleton Adj i).toFinset).mpr
    simp only [hf, Nat.cast_le] at hp
    have hp : ∀ I' ⊆ I, I'.card ≤ M.r ↑(I'.biUnion N) := by
      intro I' hI'
      obtain rfl | hem := eq_or_ne I' ∅
      simp only [Finset.card_empty, Finset.biUnion_empty, Finset.coe_empty, r_empty, le_refl]
      exact hp I' hI' <| Finset.nonempty_of_ne_empty hem
    have : ∀ (K : Finset { x // x ∈ I }), K.card ≤
      M.r ↑(K.biUnion fun i ↦ (N_singleton Adj ↑i).toFinset):= by
    -- thanks Max for this proof
      intro K
      have hsub : Finset.image Subtype.val K ⊆ I := by
        refine fun x hx ↦ ?_
        simp only [Finset.mem_image, Subtype.exists, exists_and_right, exists_eq_right] at hx
        exact hx.1
      have : (Finset.image Subtype.val K).card = K.card := by
        simp [Finset.card_image_iff.mpr injOn_subtype_val]
      specialize hp (Finset.image Subtype.val K) hsub
      simp only [this] at hp
      refine le_trans hp (le_of_eq ?_)
      apply congrArg
      apply congrArg
      exact Finset.image_biUnion
    obtain ⟨e, ⟨hinj, hin⟩, hi⟩ := h this
    refine ⟨?_, subset_univ _⟩
    simp only [AdjIndep, exists_and_left]
    obtain rfl | hem := eq_or_ne I ∅
    simp only [Finset.coe_empty, true_or]
    simp only [hem, false_or]
    set e' := fun x ↦ if h : x ∈ I then e ⟨x, h⟩ else Classical.arbitrary α
    refine ⟨(range e).toFinset, (coe_toFinset (range e)).symm ▸ hi, ⟨e', ⟨⟨fun x hx ↦ ?_,
      fun x hx y hy hxy ↦ ?_, fun x hx ↦ ?_⟩, ?_⟩⟩⟩
    · simp only [Finset.mem_coe] at hx
      simp only [hx, toFinset_range, Finset.univ_eq_attach, Finset.coe_image, mem_image,
        Finset.mem_coe, Finset.mem_attach, true_and, Subtype.exists, e']
      refine ⟨x, hx, by simp only [↓reduceDIte]⟩
    · simp only [Finset.mem_coe] at hx hy
      simp only [hx, ↓reduceDIte, hy, e'] at hxy
      exact Subtype.mk_eq_mk.mp (hinj hxy)
    · simp only [mem_image, Finset.mem_coe, e']
      simp only [toFinset_range, Finset.univ_eq_attach, Finset.coe_image, mem_image,
        Finset.mem_coe, Finset.mem_attach, true_and, Subtype.exists] at hx
      obtain ⟨a, b, hab⟩ := hx
      refine ⟨a, b, by simp only [b, ↓reduceDIte, hab]⟩
    · intro v hv
      simp only [Finset.mem_coe] at hv
      specialize hin ⟨v, hv⟩
      simp only [N_singleton, mem_setOf_eq, toFinset_setOf, Finset.mem_filter,
        Finset.mem_univ, true_and] at hin
      simp only [hv, ↓reduceDIte, e', hin]

  have h_eq' : (ofPolymatroidFn hf_poly) = M.adjMap Adj univ := by
    refine eq_of_indep_iff_indep_forall rfl (fun J _ ↦ ?_)
    simpa using heq J.toFinset

  have :  ∀ Y,  f Y = M.r {v | ∃ u ∈ Y, Adj v u} := by
    intro Y
    simp only [N_singleton, mem_setOf_eq, toFinset_setOf, Finset.coe_biUnion, Finset.mem_coe,
      Finset.coe_filter, Finset.mem_univ, true_and, Nat.cast_inj, f, N]
    have : (⋃ x ∈ Y, {x_2 | Adj x_2 x}) = {v | ∃ u ∈ Y, Adj v u} := by
      refine subset_antisymm (fun x ↦ ?_) (fun x ↦ ?_)
      simp only [mem_iUnion, mem_setOf_eq, exists_prop, imp_self]
      simp only [mem_setOf_eq, mem_iUnion, exists_prop, imp_self]
    rw [this]

  exact ⟨f, hf_poly, h_eq', this⟩

theorem adjMap_rank_eq [DecidableEq β] [Nonempty α] [Fintype α] [Fintype β] (M : Matroid α)
  (Adj : α → β → Prop) :
  (∃ Y , M.r {v | ∃ u ∈ Y, Adj v u} + (Finset.univ \ Y).card ≤ (M.adjMap Adj univ).rk) ∧
  (∀ Y , (M.adjMap Adj univ).rk ≤ M.r {v | ∃ u ∈ Y, Adj v u} + (Finset.univ \ Y).card) := by
  obtain ⟨f, hf_poly, heq, hf⟩ := polymatroid_of_adjMap M Adj
  rw [← heq]
  zify
  simp only [← (hf _), rk_def, ofPolymatroidFn_E]
  obtain hpoly := polymatroid_rank_eq hf_poly Finset.univ
  simp only [Finset.subset_univ, Finset.coe_univ, true_and, true_implies] at hpoly
  exact hpoly


theorem matroid_partition [DecidableEq α] [Nonempty α] [Nonempty ι] [Fintype ι] [Fintype α]
  (Ms : ι → Matroid α)
  : (∃ Y : Finset α, ∑ i : ι, (Ms i).r Y + (Finset.univ \ Y).card ≤
    (Matroid.Union Ms).rk) ∧
    (∀ Y : Finset α, (Matroid.Union Ms).rk ≤ ∑ i : ι, (Ms i).r Y +
    (Finset.univ \ Y).card) := by
    classical
    simp only [Matroid.Union]
    obtain ha := adjMap_rank_eq (Matroid.sum' Ms) (fun x y ↦ x.2 = y)
    simp_rw [sum'_r_eq_r_sum] at ha
    simp only [exists_eq_right', preimage_setOf_eq, Finset.setOf_mem] at ha
    exact ha

theorem twomatroid_partition [DecidableEq α] [Nonempty α] [Fintype α]
  (M₁ : Matroid α) (M₂ : Matroid α) : (∃ Y : Finset α, M₁.r Y + M₂.r Y + (Finset.univ \ Y).card ≤
    (Matroid.TwoUnion M₁ M₂).rk) ∧ (∀ Y : Finset α, (Matroid.TwoUnion M₁ M₂).rk ≤ M₁.r Y + M₂.r Y +
    (Finset.univ \ Y).card) := by
    simp only [Matroid.TwoUnion, Matroid.Union]
    obtain ha := adjMap_rank_eq (Matroid.sum' fun t ↦ Bool.rec M₁ M₂ t) (fun x y ↦ x.2 = y)
    simp_rw [sum'_r_eq_r_sum] at ha
    simp only [exists_eq_right', preimage_setOf_eq, Finset.setOf_mem] at ha
    sorry

theorem twomatroid_partition' [DecidableEq α] [Nonempty α] [Fintype α]
  (M₁ : Matroid α) (M₂ : Matroid α) : ∃ Y : Set α, M₁.er Y + M₂.er Y + (univ \ Y).encard =
    (Matroid.TwoUnion M₁ M₂).erk := by
  obtain ⟨⟨Y, hY⟩, h⟩ := twomatroid_partition M₁ M₂
  have : ∀ Y : Finset α, (Finset.univ \ Y).card = (univ \ Y.toSet).ncard := by
    intro Y
    rw [← Finset.coe_univ, ← Finset.coe_sdiff, ncard_coe_Finset]
  simp_rw [← coe_r_eq, ← coe_rk_eq,
    ← Finite.cast_ncard_eq (Finite.subset (toFinite univ) (subset_univ _)), ← Nat.cast_add,
    Nat.cast_inj]
  refine ⟨Y, le_antisymm (by simp only [← this _, hY]) (by simp only [← this _, h Y])⟩

lemma base_inter_encard_eq [DecidableEq α] {M₁ : Matroid α} {M₂ : Matroid α} {B₁ : Set α} {B₂ : Set α}
  (h₁ : M₁.Base B₁) (h₂ : M₂.Base B₂) (ground_eq : M₁.E = M₂.E) : (B₁ ∩ B₂).encard + M₂.dual.erk =
  (B₁ ∪ (M₂.E \ B₂)).encard  := by
  rw [← Base.encard_compl_eq h₂, ← encard_union_add_encard_inter, inter_assoc, inter_diff_self,
    inter_empty, encard_empty, add_zero, inter_union_distrib_right, union_diff_self,
    union_eq_self_of_subset_left (Base.subset_ground h₂), inter_eq_self_of_subset_left <|
    union_subset (ground_eq ▸ (Base.subset_ground h₁)) diff_subset]


lemma union_base_eq_base_union [DecidableEq α] [Fintype α] [Nonempty α] {M : Matroid α}
{N : Matroid α} : ∃ B C : Set α, (Matroid.TwoUnion M N).Base (B ∪ C):= by
  simp [base_iff_maximal_indep]
  obtain ⟨B, hB⟩ := (M.TwoUnion N).exists_base
  sorry

lemma asdf [DecidableEq α] [Fintype α] [Nonempty α] {M : Matroid α} {N : Matroid α} : 1 = 1 := by rfl


theorem matroid_intersection [DecidableEq α] (M₁ : Matroid α) (M₂ : Matroid α)
  (ground_eq : M₁.E = M₂.E) : ∃ I X, M₁.Indep I ∧ M₂.Indep I ∧ I.encard = M₁.er X + M₂.er (M₂.E \ X)
  := by

  sorry
