import Matroid.Constructions.Matching
import Mathlib.Data.Matroid.Sum
import Mathlib.Order.Disjointed
import Matroid.Constructions.Submodular
import Matroid.Rank
import Mathlib.Algebra.BigOperators.Ring
import Matroid.ForMathlib.Set


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

lemma adjMap_isEmpty [DecidableEq β] [Fintype β] [IsEmpty α] (M : Matroid α) (Adj : α → β → Prop) :
 (M.adjMap Adj univ) = loopyOn univ := by
  refine eq_of_indep_iff_indep_forall rfl ?_
  simp only [adjMap_ground_eq, subset_univ, adjMap_indep_iff', AdjIndep', loopyOn_indep_iff,
    true_implies]
  refine fun I ↦ Iff.intro (fun hI ↦ ?_)
    (fun hI  ↦ by simp only [hI, exists_and_left, true_or, and_self])
  simp only [exists_and_left, and_true] at hI
  obtain rfl | ⟨I', _, _, hb, _⟩ := hI
  rfl
  exact bijOn_empty_iff_left.mp <| show I' = ∅ by simp only [eq_empty_of_isEmpty] ▸ hb



def N_singleton (Adj : α → β → Prop) (v : β) := {u | Adj u v}
def N (Adj : α → β → Prop) (V : Set β) := {u | ∃ v ∈ V, Adj u v}

protected def Union [DecidableEq α] (Ms : ι → Matroid α) : Matroid α :=
  (Matroid.sum' Ms).adjMap (fun x y ↦ x.2 = y) univ

protected def union [DecidableEq α] (M : Matroid α) (N : Matroid α) : Matroid α :=
  Matroid.Union (Bool.rec M N)

@[simp] lemma Union_empty [DecidableEq α] [IsEmpty ι] (Ms : ι → Matroid α) :
    Matroid.Union Ms = loopyOn univ := by
  obtain hα | hα := isEmpty_or_nonempty α
  · simp only [Matroid.Union, adjMap, IndepMatroid.ofFinset, AdjIndep, sum'_indep_iff,
    IsEmpty.forall_iff, true_and, eq_iff_indep_iff_indep_forall, restrict_ground_eq, loopyOn_ground,
    subset_univ, restrict_indep_iff, IndepMatroid.matroid_Indep, IndepMatroid.ofFinitary_indep,
    and_true, loopyOn_indep_iff, true_implies]
    refine fun I ↦ Iff.intro (fun _ ↦ ?_) (fun hI ↦ by simp only [hI, subset_empty_iff,
      Finset.coe_eq_empty, forall_eq, Finset.coe_empty, true_or])
    exact subset_empty_iff.mp <| (Set.univ_eq_empty_iff.mpr hα) ▸ subset_univ _
  · simp [eq_iff_indep_iff_indep_forall, Matroid.Union, adjMap, IndepMatroid.ofFinset, AdjIndep]
    refine fun I ↦ Iff.intro (fun hI ↦ ?_) (fun hI ↦ by simp only [hI, subset_empty_iff,
      Finset.coe_eq_empty, forall_eq, Finset.coe_empty, true_or])
    contrapose! hI
    choose a ha using hI
    refine ⟨{a}, by simp only [Finset.coe_singleton, singleton_subset_iff, ha], by simp only [ne_eq,
      Finset.singleton_ne_empty, not_false_eq_true]⟩


lemma union_indep_aux [DecidableEq α] [Fintype α] {Ms : ι → Matroid α} {I : Set α}
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

lemma union_indep_aux' [DecidableEq α] [Fintype α] {Ms : ι → Matroid α} {I : Set α} (Is : ι → Set α)
  (hI : ⋃ (i : ι), Is i = (I : Set α) ∧ ∀ (i : ι), (Ms i).Indep (Is i)) :
    (Matroid.Union Ms).Indep I := by
    obtain ⟨Is, hD, hIs, hsub⟩ := exists_pairwiseDisjoint_iUnion_eq Is
    obtain hD := Pairwise.pairwiseDisjoint hD univ
    have hI : ⋃ i, Is i = I ∧ ∀ (i : ι), (Ms i).Indep (Is i) :=
      ⟨hIs ▸ hI.1, fun i ↦ Matroid.Indep.subset (hI.2 i) (hsub i)⟩
    obtain hα | hα := isEmpty_or_nonempty α
    · simp [eq_empty_of_isEmpty I]
    obtain hι | hι := isEmpty_or_nonempty ι
    · simp only [Union_empty, loopyOn_indep_iff]
      simpa [iUnion_of_empty, IsEmpty.forall_iff, and_true] using Eq.symm hI.1
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

lemma union_indep_iff [DecidableEq α] [Fintype α] {Ms : ι → Matroid α} {I : Set α} :
    (Matroid.Union Ms).Indep I ↔
    ∃ Is : ι → Set α, ⋃ i, Is i = (I : Set α) ∧ ∀ i, (Ms i).Indep (Is i) := by
    refine Iff.intro union_indep_aux (fun ⟨Is, hI⟩ ↦ union_indep_aux' Is hI)

lemma union_indep_iff' [DecidableEq α] [Fintype α] {M₁ : Matroid α} {M₂ : Matroid α}
  {I : Set α} :
  (Matroid.union M₁ M₂).Indep I ↔ ∃ I₁ I₂, I = I₁ ∪ I₂ ∧ M₁.Indep I₁ ∧ M₂.Indep I₂ := by
  simp only [Matroid.union, union_indep_iff, Bool.forall_bool, union_eq_iUnion]
  refine Iff.intro (fun ⟨Is, hI, hI1, hI2⟩ ↦ ⟨Is false, Is true, hI ▸ ?_, hI1, hI2⟩)
    (fun ⟨I₁, I₂, hI, hI1, hI2⟩ ↦ ⟨fun i ↦ bif i then I₂ else I₁,hI ▸ ?_, hI1, hI2⟩)
  ext1 x
  simp only [mem_iUnion, Bool.exists_bool, cond_false, cond_true]
  tauto
  ext1 x
  simp only [mem_iUnion, Bool.exists_bool, cond_false, cond_true]
  tauto

noncomputable def PolymatroidFn_of_r (M : Matroid α) (_ : M.Finite): PolymatroidFn M.r where
  submodular := M.r_submod
  mono := M.r_mono
  zero_at_bot := M.r_empty

noncomputable def PolymatroidFn_of_zero [DecidableEq α]: PolymatroidFn (fun _ : Finset α ↦ (0 : ℤ))
  where
  submodular := by simp only [Submodular, add_zero, le_refl, implies_true]
  mono := by simp only [Monotone, le_eq_subset, le_refl, implies_true]
  zero_at_bot := by simp only

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
    simp_all only [Basis', Maximal, mem_setOf_eq, and_imp]
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
  rw [cast_r_eq]
  rw [Nat.cast_sum]
  simp_rw [cast_r_eq]



theorem polymatroid_of_adjMap [DecidableEq β] [Fintype α] [Fintype β] (M : Matroid α)
  (Adj : α → β → Prop) : ∃f, ∃h : (PolymatroidFn f), ofPolymatroidFn h = M.adjMap Adj univ ∧
  ∀ Y,  f Y = M.r {v | ∃ u ∈ Y, Adj v u} := by
classical
obtain hα | hα := isEmpty_or_nonempty α
· refine ⟨fun _ : Finset β ↦ (0 : ℤ), PolymatroidFn_of_zero, eq_of_indep_iff_indep_forall rfl
    (fun J _ ↦ ?_), ?_⟩
  · have heq : ∀ I : Finset β, (ofPolymatroidFn PolymatroidFn_of_zero).Indep I.toSet ↔
      (M.adjMap Adj univ).Indep I := by
      simp only [indep_ofPolymatroidFn_iff, Int.natCast_nonpos_iff, Finset.card_eq_zero,
        adjMap_indep_iff', subset_univ, and_true, AdjIndep', Finset.coe_eq_empty, exists_and_left]
      refine fun I ↦ Iff.intro (fun hI ↦ ?_) (fun hI ↦ ?_)
      · obtain rfl | h := eq_or_ne I ∅
        simp only [Finset.coe_empty, true_or]
        simp only [h, false_or]
        absurd hI
        simp only [not_forall, Classical.not_imp]
        exact ⟨I, subset_rfl, Finset.nonempty_of_ne_empty h, h⟩
      · refine fun I' hsub _ ↦ ?_
        obtain rfl | h := eq_or_ne I ∅
        exact Finset.subset_empty.mp hsub
        simp only [h, false_or] at hI
        obtain ⟨J, _, ⟨f, hm, _⟩⟩ := hI
        obtain hI := Finset.coe_eq_empty.mp <| bijOn_empty_iff_left.mp
          <| (eq_empty_of_isEmpty J) ▸ hm
        exact Finset.subset_empty.mp <| hI ▸ hsub
    exact coe_toFinset J ▸ (heq J.toFinset)

  · simp only
    intro Y
    simp only [eq_empty_of_isEmpty, M.r_empty, Nat.cast_zero]
· set N := fun i ↦ (N_singleton Adj i).toFinset
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

  have heq : ∀ I : Finset β, (ofPolymatroidFn hf_poly).Indep I ↔ (M.adjMap Adj univ).Indep I := by
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

theorem adjMap_rank_eq [DecidableEq β] [Fintype α] [Fintype β] (M : Matroid α)
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


theorem matroid_partition [DecidableEq α] [Fintype ι] [Fintype α]
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

theorem matroid_partition' [DecidableEq α] [Fintype α]
  (M₁ : Matroid α) (M₂ : Matroid α) : (∃ Y : Finset α, M₁.r Y + M₂.r Y + (Finset.univ \ Y).card ≤
    (Matroid.union M₁ M₂).rk) ∧ (∀ Y : Finset α, (Matroid.union M₁ M₂).rk ≤ M₁.r Y + M₂.r Y +
    (Finset.univ \ Y).card) := by
    simp only [Matroid.union, Matroid.Union]
    obtain ha := adjMap_rank_eq (Matroid.sum' fun t ↦ Bool.rec M₁ M₂ t) (fun x y ↦ x.2 = y)
    simp_rw [sum'_r_eq_r_sum] at ha
    simp only [exists_eq_right', preimage_setOf_eq, Finset.setOf_mem, Fintype.sum_bool] at ha
    simp_rw [add_comm] at ha
    exact ha

theorem matroid_partition_er' [DecidableEq α] [Fintype α]
  (M₁ : Matroid α) (M₂ : Matroid α) : ∃ Y : Set α, M₁.er Y + M₂.er Y + (univ \ Y).encard =
    (Matroid.union M₁ M₂).erk := by
  obtain ⟨⟨Y, hY⟩, h⟩ := matroid_partition' M₁ M₂
  have : ∀ Y : Finset α, (Finset.univ \ Y).card = (univ \ Y.toSet).ncard := by
    intro Y
    rw [← Finset.coe_univ, ← Finset.coe_sdiff, ncard_coe_Finset]
  simp_rw [← cast_r_eq, ← coe_rk_eq,
    ← Finite.cast_ncard_eq (Finite.subset (toFinite univ) (subset_univ _)), ← Nat.cast_add,
    Nat.cast_inj]
  refine ⟨Y, le_antisymm (by simp only [← this _, hY]) (by simp only [← this _, h Y])⟩

lemma base_inter_encard_eq [DecidableEq α] {M₁ : Matroid α} {M₂ : Matroid α} {B₁ : Set α} {B₂ : Set α}
  (h₁ : M₁.Base B₁) (h₂ : M₂.Base B₂) (ground_eq : M₁.E = M₂.E) : (B₁ ∩ B₂).encard + M₂.dual.erk =
  (B₁ ∪ (M₂.E \ B₂)).encard := by
  rw [← Base.encard_compl_eq h₂, ← encard_union_add_encard_inter, inter_assoc, inter_diff_self,
    inter_empty, encard_empty, add_zero, inter_union_distrib_right, union_diff_self,
    union_eq_self_of_subset_left (Base.subset_ground h₂), inter_eq_self_of_subset_left <|
    union_subset (ground_eq ▸ (Base.subset_ground h₁)) diff_subset]


lemma exists_union_base_of_indep_union [DecidableEq α] [Fintype α] (Ms : ι → Matroid α)
  : ∃ Is : ι → Set α, (Matroid.Union Ms).Base (⋃ i, Is i) ∧ ∀ i, (Ms i).Indep (Is i) := by
  obtain ⟨D, hD⟩ := (Matroid.Union Ms).exists_base
  obtain ⟨Is, hIs, hI⟩ := union_indep_iff.mp <| Base.indep hD
  exact ⟨Is, hIs ▸ hD, hI⟩

lemma exists_union_base_of_base_union [DecidableEq α] [Fintype α] (Ms : ι → Matroid α)
  : ∃ Is : ι → Set α, (Matroid.Union Ms).Base (⋃ i, Is i) ∧ ∀ i, (Ms i).Base (Is i) := by
  classical
  obtain ⟨Is, hIs, hI⟩ := exists_union_base_of_indep_union Ms
  obtain ⟨_, hmax⟩ := base_iff_maximal_indep.mp hIs
  choose Is' hIs' hIsub using fun i ↦ (Indep.subset_basis'_of_subset (hI i) (subset_iUnion Is i))
  have hB : ∀ i, (Ms i).Base (Is' i) := by
    intro i
    rw [base_iff_maximal_indep, maximal_subset_iff', and_iff_right (hIs' i).indep]
    contrapose! hmax
    obtain ⟨I, hI', hsub, hne⟩ := hmax
    set f := Function.update Is' i I with hf
    refine ⟨(⋃ i, f i), union_indep_iff.mpr ⟨f, rfl, fun a ↦ ?_⟩, iUnion_subset (fun a ↦
      subset_trans (hIsub a) ?_), ?_⟩
    · obtain h | h := eq_or_ne i a
      simp only [h, Function.update_same, f]
      exact h ▸ hI'
      simp only [Function.update_noteq h.symm _ _, f]
      exact (hIs' a).indep
    · obtain h | h := eq_or_ne i a
      exact subset_trans (h ▸ hsub) <| Function.update_same i I Is' ▸ hf ▸ (subset_iUnion _ _)
      exact hf ▸ Function.update_noteq h.symm _ Is' ▸ (subset_iUnion _ _)
    · contrapose! hne
      simp only [Basis', maximal_subset_iff', mem_setOf] at hIs'
      refine (hIs' i).2 ⟨hI', Function.update_same i I Is' ▸ hf ▸ iUnion_subset_iff.mp hne i ⟩ hsub
  have heq : ⋃ i, Is' i = ⋃ i, Is i := subset_antisymm
    (iUnion_subset_iff.mpr (fun i ↦ Basis'.subset <| hIs' i)) (iUnion_mono hIsub)
  exact ⟨Is', heq ▸ hIs, hB⟩


lemma exists_union'_base_of_indep_union' [DecidableEq α] [Fintype α] (M : Matroid α)
  (N : Matroid α) : ∃ B C : Set α, (Matroid.union M N).Base (B ∪ C) ∧ M.Indep B ∧ N.Indep C:= by
  obtain ⟨D, hD⟩ := (M.union N).exists_base
  obtain ⟨B, C, h', hB, hC⟩ := union_indep_iff'.mp <| Base.indep hD
  exact ⟨B, C, h' ▸ hD, hB, hC⟩

lemma exists_union'_base_of_base_union' [DecidableEq α] [Fintype α] (M : Matroid α)
  (N : Matroid α) : ∃ B C : Set α, (Matroid.union M N).Base (B ∪ C) ∧ M.Base B ∧ N.Base C:= by
  classical
  obtain ⟨B, C, h', hB, hC⟩ := exists_union'_base_of_indep_union' M N
  obtain ⟨_, hmax⟩ := base_iff_maximal_indep.mp h'
  obtain ⟨B', hB', hBsub⟩ := Indep.subset_basis'_of_subset hB (@subset_union_left α B C)
  have hBB': M.Base B' := by
    rw [base_iff_maximal_indep, maximal_subset_iff', and_iff_right hB'.indep]
    contrapose! hmax
    obtain ⟨I, hI, hsub, hne⟩ := hmax
    refine ⟨I ∪ C, union_indep_iff'.mpr ⟨I, C, rfl, hI, hC⟩, union_subset_union_left C <|
       subset_trans hBsub hsub, ?_⟩
    contrapose! hne
    simp only [Basis', maximal_subset_iff', mem_setOf] at hB'
    refine hB'.2 ⟨hI, subset_union_left.trans hne⟩ hsub
  obtain ⟨C', hC', hCsub⟩ := Indep.subset_basis'_of_subset hC (@subset_union_left α C B)
  have hBC': N.Base C' := by
    rw [base_iff_maximal_indep, maximal_subset_iff', and_iff_right hC'.indep]
    contrapose! hmax
    obtain ⟨I, hI, hsub, hne⟩ := hmax
    refine ⟨B ∪ I, union_indep_iff'.mpr ⟨B, I, rfl, hB, hI⟩, union_subset_union_right B <|
       subset_trans hCsub hsub, ?_⟩
    contrapose! hne
    simp only [Basis', maximal_subset_iff', mem_setOf] at hC'
    refine hC'.2 ⟨hI, (subset_union_right.trans hne).trans_eq (union_comm ..)⟩ hsub
  have heq : B' ∪ C' = B ∪ C := subset_antisymm (union_subset_iff.mpr ⟨Basis'.subset hB',
    union_comm B C ▸ Basis'.subset hC'⟩) (union_subset_union hBsub hCsub)
  exact ⟨ B', C', heq ▸ h', hBB', hBC'⟩

theorem matroid_intersection_aux [Fintype α] (M : Matroid α) (N : Matroid α) (ground_eq : M.E = N.E)
    (ground_univ : N.E = univ) : ∃ I X, M.Indep I ∧ N.Indep I ∧ I.encard =
    M.er X + N.er Xᶜ := by
  classical
  obtain ⟨B, C, h, hB, hC⟩ := exists_union'_base_of_base_union' M N.dual
  obtain ⟨X, heq⟩ := matroid_partition_er' M N.dual
  obtain h' := base_inter_encard_eq hB (Base.compl_base_of_dual hC) ground_eq ▸ dual_ground ▸
    diff_diff_cancel_left (N.dual.subset_ground C hC) ▸ heq ▸ Base.encard h
  obtain hX := encard_diff_add_encard_of_subset <| subset_univ X

  obtain hd := ground_univ ▸ N.dual_er_add_erk X
  obtain hg := ground_univ ▸ N.erk_add_dual_erk.symm
  refine ⟨B ∩ (N.E \ C), X, Matroid.Indep.subset (Matroid.Base.indep hB) inter_subset_left,
    Matroid.Indep.subset (Matroid.Base.indep (Base.compl_base_of_dual hC)) inter_subset_right, ?_⟩
  have hcard : (B ∩ (N.E \ C)).encard + N✶.erk + X.encard + N.erk =
    M.er X + N✶.er X + (univ \ X).encard + X.encard + N.erk := by
    rw [h']
  -- have aux : _ + X.encard + (N.erk + N✶.erk)
  --   = M.er X + (univ \ X).encard + X.encard + (N✶.er X + N.erk) := by
  --   convert hcard using 1 <;> ac_rfl
  -- rw [N.dual_er_add_erk, erk_add_dual_erk] at aux

  rwa [add_comm, add_comm (B ∩ (N.E \ C)).encard, ← add_assoc, ← add_assoc, ← hg, add_assoc (M.er X),
     add_comm (N✶.er X), add_assoc (M.er X), add_assoc (univ \ X).encard, add_comm (N✶.er X),
     add_assoc (M.er X), add_assoc (univ \ X).encard, add_assoc X.encard, hd,
     ← add_assoc (univ \ X).encard, hX, ← add_assoc univ.encard, add_comm (M.er X),
     add_assoc, add_assoc, add_assoc, WithTop.add_left_cancel_iff, add_comm (a := X.encard),
     ← add_assoc, WithTop.add_right_cancel_iff, add_comm, ← compl_eq_univ_diff] at hcard
  · exact encard_ne_top_iff.2 X.toFinite
  exact encard_ne_top_iff.2 univ.toFinite

theorem exists_common_ind (M₁ M₂ : Matroid α) [M₁.Finite] :
    ∃ I X, M₁.Indep I ∧ M₂.Indep I ∧ I.encard = M₁.er X + M₂.er (M₂.E \ X) := by
  suffices aux : ∀ (E : Set α) (M₁ M₂ : Matroid α), M₁.Finite → M₁.E = E → M₂.E = E →
      ∃ I X, X ⊆ M₁.E ∩ M₂.E ∧  M₁.Indep I ∧ M₂.Indep I ∧ I.encard = M₁.er X + M₂.er (E \ X) by
    obtain ⟨I, X, _, hI₁, hI₂, hIX⟩ := aux M₁.E M₁ (M₂ ↾ M₁.E) (by assumption) rfl rfl
    simp only [restrict_er_eq', inter_eq_self_of_subset_left diff_subset] at hIX
    refine ⟨I, X ∪ (M₂.E \ M₁.E), hI₁, hI₂.of_restrict, ?_⟩
    rwa [← er_inter_ground (X := _ ∪ _), union_inter_distrib_right, inter_comm (a := _ \ _),
      inter_diff_self, union_empty, er_inter_ground, ← diff_diff, diff_diff_comm,
      diff_diff_right_self, inter_diff_assoc, inter_comm, er_inter_ground]
  clear! M₁ M₂
  intro E M₁ M₂ hfin hM₁E hM₂E
  classical
  obtain := Finite.to_subtype <| hM₁E ▸ M₁.ground_finite
  obtain ⟨I, X, hI₁, hI₂, hIX⟩ :=
    @matroid_intersection_aux ↑E (Fintype.ofFinite ↑E) (M₁.restrictSubtype E) (M₂.restrictSubtype E)
    rfl (by simp)
  simp only [restrictSubtype, er_comap_eq, restrict_er_eq', image_val_inter_self_left_eq_coe,
    image_val_compl, inter_eq_self_of_subset_left diff_subset] at hIX
  refine ⟨I, X, by simp [hM₁E, hM₂E], (by simpa using hI₁), (by simpa using hI₂), ?_⟩
  rwa [Subtype.val_injective.injOn.encard_image]



  -- suffices aux1 : ∀ M₂' : Matroid α, M₂'.E = M₁.E →
  --     ∃ I X, X ⊆ M₁.E ∧ M₁.Indep I ∧ M₂'.Indep I ∧ I.ncard = M₁.r X + M₂.r (M₂.E \ X) by
  --   obtain ⟨I, X, hX, hI, hI', hIcard⟩ := aux1 (M₂ ↾ M₁.E) rfl
  --   refine ⟨I, (M₂.E \ M₁.E) ∪ X, hI, hI'.of_restrict, ?_⟩
  --   rw [r_eq_r_inter_ground, union_inter_distrib_right, diff_inter_self, empty_union,
  --     ← r_eq_r_inter_ground, ← diff_diff, diff_diff_right_self, diff_eq, inter_assoc]
  --   sorry
  -- intro M₂' h_eq
