import Matroid.Constructions.Matching
import Matroid.Constructions.DirectSum
import Mathlib.Order.Disjointed
import Matroid.Constructions.Submodular
import Matroid.Rank

namespace Matroid

universe u

variable {α ι β: Type*}

open Classical

def AdjIndep' (M : Matroid α) (Adj : α → β → Prop) (I : Set β) :=
  I = ∅ ∨ ∃ (I₀ : Set α) (f : β → α), M.Indep I₀ ∧ IsMatching Adj f I₀ I

@[simp] lemma adjMap_indep_iff' [DecidableEq β] (M : Matroid α) (Adj : α → β → Prop) (E : Set β)
    {I : Set β} : (M.adjMap Adj E).Indep I ↔ M.AdjIndep' Adj I ∧ (I : Set β) ⊆ E := by
  sorry

noncomputable def N_singleton [Fintype α] (Adj : α → β → Prop) (v : β) := {u | Adj u v}.toFinset

protected def Union [DecidableEq α] (Ms : ι → Matroid α) : Matroid α :=
  (Matroid.prod Ms).adjMap (fun x y ↦ x.2 = y) Set.univ

-- lemma union_indep_Finset {Ms : ι → Matroid α} {I : Finset α} (hI : (Matroid.Union Ms).Indep I) :
--     ∃ Is : ι → Set α, ⋃ (i : ι), Is i = (I : Set α) ∧ ∀ (i : ι), (Ms i).Indep (Is i) := by
--     simp only [Matroid.Union, adjMap_indep_iff, AdjIndep, prod_indep_iff, exists_and_left,
--     Set.subset_univ, and_true] at hI
--     obtain heq | hne := eq_or_ne I ∅
--     · refine ⟨(fun ι ↦ ∅), by simp only [Set.iUnion_empty, heq, Finset.coe_empty,
--       empty_indep, implies_true, and_self]⟩
--     · simp only [hne, false_or] at hI
--       obtain ⟨I', h, ⟨f, hB, hAdj⟩⟩ := hI
--       refine ⟨(fun i ↦ (Prod.mk i ⁻¹' I') : ι → Set α), (Set.BijOn.image_eq hB) ▸ ?_, h⟩
--       refine subset_antisymm (fun v hv ↦ ?_) (fun v hv ↦ ?_)
--       · simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_image] at hv
--         obtain ⟨i, x, hx, h⟩ := hv
--         specialize hAdj x hx
--         simp only [h ▸ hAdj ▸ hx]
--       · specialize hAdj v hv
--         simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_image]
--         refine ⟨(f v).1, v, hv, ?_⟩
--         nth_rw 3 [← hAdj]

lemma union_indep [DecidableEq α] [Fintype α] [Nonempty ι] {Ms : ι → Matroid α}
  (h : ∀ i, (Ms i).Finite) {I : Set α} (hI : (Matroid.Union Ms).Indep I) :
    ∃ Is : ι → Set α, ⋃ (i : ι), Is i = (I : Set α) ∧ ∀ (i : ι), (Ms i).Indep (Is i) := by
    simp only [Matroid.Union, adjMap_indep_iff', AdjIndep', prod_indep_iff, exists_and_left,
    Set.subset_univ, and_true] at hI
    obtain heq | hne := eq_or_ne I ∅
    · refine ⟨(fun ι ↦ ∅), by simp only [Set.iUnion_empty, heq, empty_indep, implies_true,
        and_self]⟩
    · simp only [hne, false_or] at hI
      obtain ⟨I', h, ⟨f, hB, hAdj⟩⟩ := hI
      refine ⟨(fun i ↦ (Prod.mk i ⁻¹' I') : ι → Set α), (Set.BijOn.image_eq hB) ▸ ?_, h⟩
      refine subset_antisymm (fun v hv ↦ ?_) (fun v hv ↦ ?_)
      · simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_image] at hv
        obtain ⟨i, x, hx, h⟩ := hv
        specialize hAdj x hx
        simp only [h ▸ hAdj ▸ hx]
      · specialize hAdj v hv
        simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_image]
        refine ⟨(f v).1, v, hv, ?_⟩
        nth_rw 3 [← hAdj]

lemma union_indep' [DecidableEq α] [Fintype α] [Nonempty ι] [Nonempty α] {Ms : ι → Matroid α}
  (h : ∀ i, (Ms i).Finite) {I : Set α} (Is : ι → Set α) (hD : Set.univ.PairwiseDisjoint Is)
  (hI : ⋃ (i : ι), Is i = (I : Set α) ∧ ∀ (i : ι), (Ms i).Indep (Is i)) :
    (Matroid.Union Ms).Indep I := by
    simp only [Matroid.Union, adjMap_indep_iff', AdjIndep', Set.subset_univ, and_true]
    obtain rfl | h := eq_or_ne I ∅
    · simp only [true_or]
    · simp only [h, prod_indep_iff, exists_and_left, false_or]
      refine ⟨{(i, v) | (i ∈ Set.univ) ∧ v ∈ Is i}  , fun i ↦ ?_, ?_⟩
      simp only [Set.mem_univ, true_and, Set.preimage_setOf_eq, Set.setOf_mem_eq, hI.2 i]
      simp_rw [IsMatching, Set.mem_univ, true_and]
      set f := fun x : ι × α ↦ x.2 with hf
      have himage : I = f '' {x : ι × α | x.2 ∈ Is x.1} := by
        rw [← hI.1]
        simp_all only [ne_eq, f]
        obtain ⟨left, _⟩ := hI
        subst left
        simp_all only [Set.iUnion_eq_empty, not_forall]
        ext1 x
        simp_all only [Set.mem_iUnion, Set.mem_image, Set.mem_setOf_eq, Prod.exists, exists_eq_right]
      have hinj: Set.InjOn f {x : ι × α | x.2 ∈ Is x.1} := by
        refine fun x hx y hy hxy ↦ ?_
        simp only [hf] at hxy
        simp only [Set.mem_setOf_eq] at hx hy
        obtain h := Set.PairwiseDisjoint.elim_set hD (Set.mem_univ x.1)
          (Set.mem_univ y.1) x.2 hx (hxy ▸ hy)
        obtain ⟨_, _⟩ := x
        obtain ⟨_, _⟩ := y
        simp_all only
      obtain h := himage ▸ Set.InjOn.bijOn_image hinj
      refine ⟨Function.invFunOn f {x | x.2 ∈ Is x.1},
        Set.BijOn.symm (Set.InvOn.symm (Set.BijOn.invOn_invFunOn h)) h, fun v hv ↦ ?_⟩
      simp only [show (Function.invFunOn f {x | x.2 ∈ Is x.1} v).2 =
        f (Function.invFunOn f {x | x.2 ∈ Is x.1} v) by rfl, Function.invFunOn_eq (himage ▸ hv)]

lemma union_indep_iff [DecidableEq α] [Fintype α] [Nonempty α] {Ms : ℕ → Matroid α}
  (h : ∀ i, (Ms i).Finite) {I : Set α} : (Matroid.Union Ms).Indep I ↔
    ∃ Is : ℕ → Set α, ⋃ (i : ℕ), Is i = (I : Set α) ∧ ∀ (i : ℕ), (Ms i).Indep (Is i) := by
    refine iff_def'.mpr ⟨fun ⟨Is, hU, hI⟩ ↦ ?_, union_indep h⟩
    set Js := disjointed Is with hJ
    refine union_indep' h Js (Pairwise.set_pairwise (hJ ▸ (disjoint_disjointed Is)) Set.univ)
      ⟨by simp [hJ ▸ iUnion_disjointed ▸ hU],
      fun i ↦ Matroid.Indep.subset (hI i) (disjointed_subset Is i)⟩



def Intersection [DecidableEq α] (Ms : ι → Matroid α) : Set (Set α) :=
  sorry

noncomputable def PolymatroidFn_of_r (M : Matroid α) (_ : M.Finite): PolymatroidFn M.r where
 submodular := M.r_submod
 mono := M.r_mono
 zero_at_bot := M.r_empty

@[simp] theorem prod_rk_eq_rk_sum_on_indep {α ι : Type*} [Fintype ι] [Fintype α]
  {Ms : ι → Matroid α} {I : Set (ι × α)} (h : (Matroid.prod Ms).Indep I):
  (Matroid.prod Ms).r I = ∑ i : ι, (Ms i).r (Prod.mk i ⁻¹' I) := by
  rw [Indep.r h]
  simp only [prod_indep_iff] at h
  simp_rw [Indep.r (h _)]
  set f := fun x : ι × α ↦ x.1
  rw [I.ncard_eq_toFinset_card']
  rw [Finset.card_eq_sum_card_fiberwise (by refine fun x _ ↦ Finset.mem_univ (f x))]
  have himage : ∀ i : ι, (fun x : ι × α ↦ x.2) '' (Finset.filter (fun x ↦ f x = i) I.toFinset)
    = (Finset.filter (fun v ↦ (i, v) ∈ I) Finset.univ) := by
    refine fun i ↦ subset_antisymm ?_ ?_
    · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.image_subset_iff,
        Set.preimage_setOf_eq, Set.setOf_subset_setOf, and_imp, Prod.forall, f]
      refine fun a b h h' ↦ Set.mem_toFinset.mp (h' ▸ h)
    · refine fun x hx ↦ ?_
      simp only [Finset.coe_filter, Set.mem_image, Set.mem_setOf_eq, Prod.exists, exists_eq_right]
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hx
      exact Set.mem_toFinset.mpr hx
  have hinj: ∀ i : ι, Set.InjOn (fun x : ι × α ↦ x.2) (Finset.filter (fun x ↦ f x = i) I.toFinset)
    := by
    intro i x hx y hy hxy
    simp only [Finset.coe_filter, Set.mem_setOf_eq, f] at hx hy
    simp only at hxy
    obtain ⟨_, _⟩ := x
    obtain ⟨_, _⟩ := y
    simp_all only
  obtain hcard := fun i : ι ↦ Set.ncard_coe_Finset (Finset.filter (fun x_1 ↦ (i, x_1) ∈ I)
    Finset.univ) ▸ Set.ncard_coe_Finset (Finset.filter (fun x ↦ f x = i) I.toFinset) ▸ (himage i) ▸
    Set.ncard_image_of_injOn <| (hinj i)
  simp only [Set.preimage]
  have : ∀ i, {x_1 | (i, x_1) ∈ I}.ncard =
    (Finset.filter (fun x_1 ↦ (i, x_1) ∈ I) Finset.univ).card := by
    intro i
    rw [Set.ncard_eq_toFinset_card' ]
    simp only [Set.mem_setOf_eq, Set.toFinset_setOf]
  simp only [hcard, this]

@[simp] theorem prod_rk_eq_rk_sum {α ι : Type*} [Fintype ι] [Fintype α]
  (Ms : ι → Matroid α) (X : Set (ι × α)):
  (Matroid.prod Ms).r X = ∑ i : ι, (Ms i).r (Prod.mk i ⁻¹' X) := by
  obtain ⟨I , hI⟩ := (Matroid.prod Ms).exists_basis' X
  have : ∀ i : ι, (Ms i).Basis' (Prod.mk i ⁻¹' I) (Prod.mk i ⁻¹' X)  := by
    intro i
    simp_all only [Basis', maximals, Set.mem_setOf_eq, and_imp]
    refine ⟨⟨(prod_indep_iff Ms I).mp hI.1.1 i, Set.preimage_mono hI.1.2⟩, fun b hIb h h'↦ ?_⟩
    have : (∀ (j : ι), (Ms j).Indep (Prod.mk j ⁻¹' (I ∪ (Prod.mk i '' b)))) := by
      intro j
      by_cases h: j = i
      · rw [h, Set.preimage_union]
        exact Matroid.Indep.subset hIb (Set.union_subset h'
          (b.preimage_image_eq (Prod.mk.inj_left i)).subset)
      · have : (Prod.mk j ⁻¹' (Prod.mk i '' b)) = ∅ := by
          refine subset_antisymm (fun x hx ↦  ?_) (Set.empty_subset _)
          simp only [Set.mem_preimage, Set.mem_image, Prod.mk.injEq, exists_eq_right_right] at hx
          simp only [Set.mem_empty_iff_false]
          simp_all only [not_true_eq_false]
        simp only [Set.preimage_union, this, Set.union_empty, (prod_indep_iff Ms I).mp hI.1.1 j]
    obtain h'' := hI.2 ((prod_indep_iff Ms (I ∪ (Prod.mk i '' b))).mpr this)
      (Set.union_subset hI.1.2 (subset_trans (Set.image_mono h) (Set.image_preimage_subset _ _)))
      Set.subset_union_left
    exact subset_trans (Set.subset_preimage_image _ _)
      (Set.preimage_mono (Set.union_subset_iff.mp h'').2)
  simp_rw [← Basis'.r hI, ← Basis'.r (this _)]
  exact prod_rk_eq_rk_sum_on_indep hI.1.1

theorem adjMap_rank_eq [DecidableEq β] [Fintype α] [Fintype β] (M : Matroid α) (Adj : α → β → Prop)
  (E : Finset β) :
  (∃ Y ⊆ E, M.r {v | ∃ u ∈ Y, Adj v u} + (E \ Y).card ≤ (M.adjMap Adj E).rk) ∧
    (∀ Y ⊆ E, (M.adjMap Adj E).rk ≤ M.r {v | ∃ u ∈ Y, Adj v u} + (E \ Y).card) := by
  set f := fun I : Finset β ↦ (M.r (I.biUnion (N_singleton Adj)) : ℤ) with hf
  have : PolymatroidFn f := by
    refine ⟨fun X Y ↦ hf ▸ ?_, ?_, ?_⟩
    · simp only [Finset.inf_eq_inter, Finset.sup_eq_union]
      have : ((X ∪ Y).biUnion (N_singleton Adj)) =
        X.biUnion (N_singleton Adj) ∪ Y.biUnion (N_singleton Adj):= by aesop
      rw [← Nat.cast_add ,← Nat.cast_add, Nat.cast_le]
      refine (le_trans
        ((Finset.coe_union (X.biUnion (N_singleton Adj)) (Y.biUnion (N_singleton Adj))) ▸ this ▸
        (add_le_add_right  ( M.r_mono ?_) _)) (M.r_submod _ _))
      simp only [Finset.coe_biUnion, Finset.coe_inter, Set.mem_inter_iff, Finset.mem_coe,
        N_singleton, Set.le_eq_subset, Set.subset_inter_iff, Set.iUnion_subset_iff, and_imp,
        Set.mem_setOf_eq, Set.toFinset_setOf, Finset.coe_filter, Finset.mem_univ, true_and]
      refine ⟨fun x h1 h2 y h3 ↦ ?_, fun x h1 h2 y h3 ↦ ?_⟩
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
      exact ⟨x, ⟨h1, h3⟩⟩
      simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
      exact ⟨x, ⟨h2, h3⟩⟩
    · refine fun X Y h ↦ hf ▸ Nat.cast_le.mpr (M.r_mono ?_)
      simp only [Set.le_eq_subset, Finset.coe_biUnion, Finset.mem_coe, Set.iUnion_subset_iff]
      refine fun x h1 y h2 ↦ ?_
      simp only [Set.mem_iUnion, exists_prop]
      exact ⟨x, h h1, h2⟩
    · simp only [hf, Finset.bot_eq_empty, Finset.biUnion_empty, Finset.coe_empty, r_empty,
        Nat.cast_zero]

  rw [rk_def, adjMap_ground_eq]
  obtain h := polymatroid_rank_eq this E

  have heq : ∀ I : Finset β , (ofPolymatroidFn this).Indep I ↔ (M.adjMap Adj E).Indep I := by
    intro I
    simp only [IndepMatroid.ofFinset_indep, adjMap_indep_iff, Finset.coe_subset,
      indep_ofPolymatroidFn_iff]
    refine iff_def'.mpr ⟨fun ha I' hI' hem ↦ hf ▸ ?_, fun hp ↦ ?_⟩
    · simp only [Nat.cast_le]
      obtain h | h := ha.1
      · obtain h := Finset.subset_empty.mp (h ▸ hI')
        simp only [h, Finset.card_empty, Finset.biUnion_empty, Finset.coe_empty, r_empty, le_refl]
      · obtain hindep := Set.ncard_coe_Finset I' ▸ Indep.r <| (adjMap_indep_iff M Adj E).mpr
          ⟨AdjIndep.subset ha.1 hI', subset_trans hI' ha.2⟩
        obtain h | ⟨I₀, f, h', h''⟩ := (AdjIndep.subset ha.1 hI')
        · simp only [h, Finset.card_empty, Finset.biUnion_empty, Finset.coe_empty, r_empty, le_refl]
        · obtain h := IsMatching.card_eq h''
          rw [← h, ← Set.ncard_coe_Finset I₀ , ← Indep.r h']
          apply r_mono
          refine fun x hx ↦ Set.mem_setOf_eq ▸ ?_
          rw [← Set.BijOn.image_eq (IsMatching.bijOn h''), Set.image, Set.mem_setOf_eq] at hx
          obtain ⟨u, hu, hadj⟩ := hx
          simp only [Finset.mem_biUnion, N_singleton]
          refine ⟨u, hu, ?_⟩
          simp only [Set.mem_setOf_eq, Set.toFinset_setOf, Finset.mem_filter, Finset.mem_univ,
            true_and]
          exact hadj ▸ (IsMatching.adj h'' hu)

    obtain h := (rado M <| I.toSet.restrict (N_singleton Adj)).mpr



theorem Matroid_Partition [DecidableEq α] [Fintype ι] (Ms : ι → Matroid α) (h : ∀ i, (Ms i).Finite)
  : (∃ Y ⊆ (Matroid.Union Ms).E, ∑ i : ι, (Ms i).r Y + ((Matroid.Union Ms).E \ Y).ncard ≤
    (Matroid.Union Ms).rk) ∧
    (∀ Y ⊆ (Matroid.Union Ms).E, (Matroid.Union Ms).rk ≤ ∑ i : ι, (Ms i).r Y +
    ((Matroid.Union Ms).E \ Y).ncard) := by
    sorry
