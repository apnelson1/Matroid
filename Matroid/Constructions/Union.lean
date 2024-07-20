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


def N_singleton [Fintype α] (Adj : α → β → Prop) (v : β) := {u | Adj u v}

protected def Union [DecidableEq α] (Ms : ι → Matroid α) : Matroid α :=
  (Matroid.prod Ms).adjMap (fun x y ↦ x.2 = y) univ

-- lemma union_indep_Finset {Ms : ι → Matroid α} {I : Finset α} (hI : (Matroid.Union Ms).Indep I) :
--     ∃ Is : ι → Set α, ⋃ (i : ι), Is i = (I : Set α) ∧ ∀ (i : ι), (Ms i).Indep (Is i) := by
--     simp only [Matroid.Union, adjMap_indep_iff, AdjIndep, prod_indep_iff, exists_and_left,
--     subset_univ, and_true] at hI
--     obtain heq | hne := eq_or_ne I ∅
--     · refine ⟨(fun ι ↦ ∅), by simp only [iUnion_empty, heq, Finset.coe_empty,
--       empty_indep, implies_true, and_self]⟩
--     · simp only [hne, false_or] at hI
--       obtain ⟨I', h, ⟨f, hB, hAdj⟩⟩ := hI
--       refine ⟨(fun i ↦ (Prod.mk i ⁻¹' I') : ι → Set α), (BijOn.image_eq hB) ▸ ?_, h⟩
--       refine subset_antisymm (fun v hv ↦ ?_) (fun v hv ↦ ?_)
--       · simp only [mem_iUnion, mem_preimage, mem_image] at hv
--         obtain ⟨i, x, hx, h⟩ := hv
--         specialize hAdj x hx
--         simp only [h ▸ hAdj ▸ hx]
--       · specialize hAdj v hv
--         simp only [mem_iUnion, mem_preimage, mem_image]
--         refine ⟨(f v).1, v, hv, ?_⟩
--         nth_rw 3 [← hAdj]

lemma union_indep [DecidableEq α] [Fintype α] [Nonempty ι] {Ms : ι → Matroid α} {I : Set α}
    (hI : (Matroid.Union Ms).Indep I) :
    ∃ Is : ι → Set α, ⋃ (i : ι), Is i = (I : Set α) ∧ ∀ (i : ι), (Ms i).Indep (Is i) := by
    simp only [Matroid.Union, adjMap_indep_iff', AdjIndep', prod_indep_iff, exists_and_left,
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

lemma union_indep' [DecidableEq α] [Fintype α] [Nonempty ι] [Nonempty α] {Ms : ι → Matroid α}
  {I : Set α} (Is : ι → Set α) (hD : univ.PairwiseDisjoint Is)
  (hI : ⋃ (i : ι), Is i = (I : Set α) ∧ ∀ (i : ι), (Ms i).Indep (Is i)) :
    (Matroid.Union Ms).Indep I := by
    simp only [Matroid.Union, adjMap_indep_iff', AdjIndep', subset_univ, and_true]
    obtain rfl | h := eq_or_ne I ∅
    · simp only [true_or]
    · simp only [h, prod_indep_iff, exists_and_left, false_or]
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

-- lemma finset_union_indep' [DecidableEq α] [Fintype α] [Nonempty ι] [Nonempty α] {Ms : ι → Matroid α}
--     {I : Finset α} (Is : ι → Finset α) (hD : univ.PairwiseDisjoint Is)
--     (hI : (⋃ (i : ι), Is i).toFinset = I ∧ ∀ (i : ι), (Ms i).Indep (Is i)) :
--     (Matroid.Union Ms).Indep I := by
--   apply union_indep' (fun i ↦ Is i) (by simpa)
--   simp [← hI.1, coe_toFinset, true_and, hI.2]

lemma union_indep_iff [DecidableEq α] [Fintype α] [Nonempty α] {Ms : ℕ → Matroid α} {I : Set α} :
    (Matroid.Union Ms).Indep I ↔
    ∃ Is : ℕ → Set α, ⋃ (i : ℕ), Is i = (I : Set α) ∧ ∀ (i : ℕ), (Ms i).Indep (Is i) := by
    refine iff_def'.mpr ⟨fun ⟨Is, hU, hI⟩ ↦ ?_, union_indep⟩
    set Js := disjointed Is with hJ
    refine union_indep' Js (Pairwise.set_pairwise (hJ ▸ (disjoint_disjointed Is)) univ)
      ⟨by simp [hJ ▸ iUnion_disjointed ▸ hU],
      fun i ↦ Matroid.Indep.subset (hI i) (disjointed_subset Is i)⟩


noncomputable def PolymatroidFn_of_r (M : Matroid α) (_ : M.Finite): PolymatroidFn M.r where
  submodular := M.r_submod
  mono := M.r_mono
  zero_at_bot := M.r_empty

@[simp] theorem prod_er_eq_er_sum_on_indep {α ι : Type*} [Fintype ι] [Fintype α]
  {Ms : ι → Matroid α} {I : Set (ι × α)} (h : (Matroid.prod Ms).Indep I):
  (Matroid.prod Ms).er I = ∑ i : ι, (Ms i).er (Prod.mk i ⁻¹' I) := by
  classical
  rw [Indep.er h]
  simp only [prod_indep_iff] at h
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


@[simp] theorem prod_er_eq_er_sum {α ι : Type*} [Fintype ι] [Fintype α]
  (Ms : ι → Matroid α) (X : Set (ι × α)):
  (Matroid.prod Ms).er X = ∑ i : ι, (Ms i).er (Prod.mk i ⁻¹' X) := by
  obtain ⟨I , hI⟩ := (Matroid.prod Ms).exists_basis' X
  have : ∀ i : ι, (Ms i).Basis' (Prod.mk i ⁻¹' I) (Prod.mk i ⁻¹' X)  := by
    intro i
    simp_all only [Basis', maximals, mem_setOf_eq, and_imp]
    refine ⟨⟨(prod_indep_iff Ms I).mp hI.1.1 i, preimage_mono hI.1.2⟩, fun b hIb h h'↦ ?_⟩
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
        simp only [preimage_union, this, union_empty, (prod_indep_iff Ms I).mp hI.1.1 j]
    obtain h'' := hI.2 ((prod_indep_iff Ms (I ∪ (Prod.mk i '' b))).mpr this)
      (union_subset hI.1.2 (subset_trans (image_mono h) (image_preimage_subset _ _)))
      subset_union_left
    exact subset_trans (subset_preimage_image _ _)
      (preimage_mono (union_subset_iff.mp h'').2)
  simp_rw [← Basis'.er hI, ← Basis'.er (this _)]
  exact prod_er_eq_er_sum_on_indep hI.1.1

@[simp] theorem prod_r_eq_r_sum {α ι : Type*} [Fintype ι] [Fintype α]
  (Ms : ι → Matroid α) (X : Set (ι × α)):
  (Matroid.prod Ms).r X = ∑ i : ι, (Ms i).r (Prod.mk i ⁻¹' X) := by
  obtain h := prod_er_eq_er_sum Ms X
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
      refine ⟨x, hx, by simp only [↓reduceDite]⟩
    · simp only [Finset.mem_coe] at hx hy
      simp only [hx, ↓reduceDite, hy, e'] at hxy
      exact Subtype.mk_eq_mk.mp (hinj hxy)
    · simp only [mem_image, Finset.mem_coe, e']
      simp only [toFinset_range, Finset.univ_eq_attach, Finset.coe_image, mem_image,
        Finset.mem_coe, Finset.mem_attach, true_and, Subtype.exists] at hx
      obtain ⟨a, b, hab⟩ := hx
      refine ⟨a, b, by simp only [b, ↓reduceDite, hab]⟩
    · intro v hv
      simp only [Finset.mem_coe] at hv
      specialize hin ⟨v, hv⟩
      simp only [N_singleton, mem_setOf_eq, toFinset_setOf, Finset.mem_filter,
        Finset.mem_univ, true_and] at hin
      simp only [hv, ↓reduceDite, e', hin]

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
    obtain ha := adjMap_rank_eq (Matroid.prod Ms) (fun x y ↦ x.2 = y)
    simp_rw [prod_r_eq_r_sum] at ha
    simp only [exists_eq_right', preimage_setOf_eq, Finset.setOf_mem] at ha
    exact ha


theorem matroid_intersection [DecidableEq α] (M₁ : Matroid α) (M₂ : Matroid α)
  (ground_eq : M₁.E = M₂.E) : ∀ k, (∃ I ⊆ M₁.E, M₁.Indep I ∧ M₂.Indep I ∧ I.ncard = k) ↔
  ∀ X ⊆ M₁.E, k ≤ M₁.er X + M₂.er (M₂.E \ X) :=
  sorry
