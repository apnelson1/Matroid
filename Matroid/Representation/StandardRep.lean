import Matroid.Representation.Map
import Matroid.Flat.Hyperplane

variable {α β W W' 𝔽 R : Type*} {e f x : α} {I E B X Y : Set α} {M : Matroid α} [DivisionRing 𝔽]
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W']

open Set Function Submodule Finsupp Set.Notation Module

theorem Function.ExtendByZero.linearMap_injective (R : Type*) {ι η : Type _} [Semiring R]
  {s : ι → η} (hs : Function.Injective s) :
    Injective <| Function.ExtendByZero.linearMap R s := by
  intro x x' h
  ext i
  replace h := _root_.congr_fun h (s i)
  simp only [ExtendByZero.linearMap_apply] at h
  rwa [hs.extend_apply, hs.extend_apply] at h

namespace Matroid

lemma Rep.span_spanning_eq (v : M.Rep 𝔽 W) {S : Set α} (hS : M.Spanning S) :
    span 𝔽 (v '' S) = span 𝔽 (range v) := by
  rw [← image_univ]
  apply span_closure_congr
  simp [hS.closure_eq]

lemma Rep.spanning_iff (v : M.Rep 𝔽 W) {S : Set α} (hSE : S ⊆ M.E := by aesop_mat) :
    M.Spanning S ↔ span 𝔽 (v '' S) = span 𝔽 (range v) := by
  rw [← image_univ, ← v.span_closure_congr_iff, closure_univ, M.spanning_iff_closure_eq]

/-- A representation is `FullRank` if its vectors span the space -/
def Rep.FullRank (v : M.Rep 𝔽 W) : Prop := ⊤ ≤ span 𝔽 (range v)

/-- Restrict a representation to the submodule spanned by its image -/
@[simps] def Rep.restrictSpan (v : M.Rep 𝔽 W) : M.Rep 𝔽 (span 𝔽 (range v)) where
  to_fun := codRestrict v _ (fun x ↦ subset_span (mem_range_self _))
  indep_iff' := (by
    intro I
    rw [v.indep_iff]
    refine ⟨fun h ↦ LinearIndependent.of_comp (Submodule.subtype _) (by rwa [coe_subtype]),
      fun h ↦ h.map' (Submodule.subtype _) (ker_subtype _)⟩ )

@[simp] lemma Rep.restrictSpan_apply (v : M.Rep 𝔽 W) (e : α) :
    v.restrictSpan e = v e := rfl

lemma Rep.restrictSpan_comp (v : M.Rep 𝔽 W) :
    v.restrictSpan.comp' (Submodule.subtype _) (by simp) = v := by
  ext
  rfl

lemma Rep.FullRank.span_range {v : M.Rep 𝔽 W} (h : v.FullRank) : span 𝔽 (range v) = ⊤ := by
  rwa [eq_top_iff]

lemma Rep.FullRank.span_spanning {v : M.Rep 𝔽 W} (h : v.FullRank) {S : Set α} (hS : M.Spanning S) :
    span 𝔽 (v '' S) = ⊤ := by
  rw [← h.span_range, v.span_spanning_eq hS]

lemma Rep.FullRank.spanning_iff (v : M.Rep 𝔽 W) (h : v.FullRank) {S : Set α}
    (hSE : S ⊆ M.E := by aesop_mat) : M.Spanning S ↔ span 𝔽 (v '' S) = ⊤ := by
  rw [v.spanning_iff, h.span_range]

lemma Rep.fullRank_iff {v : M.Rep 𝔽 W} : v.FullRank ↔ span 𝔽 (range v) = ⊤ := by
  rw [FullRank, eq_top_iff]

lemma Rep.restrictSpan_eq_inclusion (v : M.Rep 𝔽 W) :
    (v.restrictSpan : α → _) = Set.inclusion subset_span ∘ rangeFactorization v := by
  ext; rfl

@[simp] lemma Rep.restrict_span_apply (v : M.Rep 𝔽 W) (e : α) :
    v.restrictSpan e = Set.inclusion subset_span (rangeFactorization v e) := rfl

lemma Rep.restrictSpan_fullRank (v : M.Rep 𝔽 W) : v.restrictSpan.FullRank := by
  change _ ≤ span 𝔽 _
  rw [restrictSpan_eq_inclusion]
  change _ ≤ span 𝔽 (range (Set.inclusion subset_span ∘ _))
  rw [range_comp, rangeFactorization_surjective.range_eq, image_univ, Set.range_inclusion]
  change _ ≤ span 𝔽 ((Submodule.subtype (span 𝔽 (range ↑v))) ⁻¹' _)
  simp

/-- A base of `M` gives a linear basis in a full-rank representation -/
noncomputable def Rep.FullRank.basis_of_isBase {v : M.Rep 𝔽 W} (h : v.FullRank) (hB : M.IsBase B) :
    Module.Basis B 𝔽 W :=
  Basis.mkImage (v.onIndep hB.indep) (h.span_spanning hB.spanning).symm.le

lemma Rep.FullRank.compEquiv {v : M.Rep 𝔽 W} (h : v.FullRank) (ψ : W ≃ₗ[𝔽] W') :
    (v.compEquiv ψ).FullRank := by
  rw [Rep.fullRank_iff, Rep.compEquiv, comp', comp, ← Rep.to_fun_eq_coe]
  simp [LinearEquiv.coe_coe, range_comp, h.span_range]

/-- A base of `M` gives a (linear) basis for the span of the range of a representation -/
noncomputable def Rep.isBasis_of_isBase (v : M.Rep 𝔽 W) (hB : M.IsBase B) :
    Module.Basis B 𝔽 (span 𝔽 (range v)) :=
  (Basis.spanImage (v.onIndep hB.indep)).map <|
    LinearEquiv.ofEq _ _ <| v.span_spanning_eq hB.spanning
  --
/-- The natural representation with rows indexed by a base with `Finsupp` -/
noncomputable def Rep.standardRep' (v : M.Rep 𝔽 W) (hB : M.IsBase B) :
    M.Rep 𝔽 (B →₀ 𝔽) :=
  v.restrictSpan.compEquiv (v.restrictSpan_fullRank.basis_of_isBase hB).repr

@[simp] lemma Rep.standardRep_eq_one' (v : M.Rep 𝔽 W) (hB : M.IsBase B) (e : B) :
    (v.standardRep' hB) e e = 1 := by
  simp only [standardRep', FullRank.basis_of_isBase, Basis.mkImage, restrict_span_apply,
    compEquiv_apply, Basis.mk_repr]
  rw [LinearIndependent.repr_eq_single (i := e) _ _ (by simp), single_eq_same]

lemma Rep.standardRep_eq_zero' (v : M.Rep 𝔽 W) (hB : M.IsBase B) (e f : B) (hef : e ≠ f) :
    (v.standardRep' hB) e f = 0 := by
  simp only [standardRep', FullRank.basis_of_isBase, Basis.mkImage, restrict_span_apply,
    compEquiv_apply, Basis.mk_repr]
  rw [LinearIndependent.repr_eq_single (i := e) _ _ (by simp), single_eq_of_ne hef.symm]

lemma Rep.standardRep_fullRank' (v : M.Rep 𝔽 W) (hB : M.IsBase B) : (v.standardRep' hB).FullRank :=
  v.restrictSpan_fullRank.compEquiv _

/-- The natural representation of a matroid with rows indexed by a base -/
noncomputable def Rep.standardRep (v : M.Rep 𝔽 W) (hB : M.IsBase B) : M.Rep 𝔽 (B → 𝔽) :=
  (v.standardRep' hB).comp Finsupp.lcoeFun (by simp [Submodule.disjoint_def, Finsupp.lcoeFun])

lemma Rep.standardRep_eq_one (v : M.Rep 𝔽 W) (hB : M.IsBase B) (e : B) :
    (v.standardRep hB) e e = 1 := by
  simp [standardRep]

lemma Rep.standardRep_eq_zero (v : M.Rep 𝔽 W) (hB : M.IsBase B) (e f : B) (hef : e ≠ f) :
    (v.standardRep hB) e f = 0 := by
  simp [standardRep, v.standardRep_eq_zero' hB _ _ hef]

lemma Rep.standardRep_eq_mapEquiv [RankFinite M] (v : M.Rep 𝔽 W) (hB : M.IsBase B) :
    v.standardRep hB = (v.standardRep' hB).compEquiv
      (@Finsupp.linearEquivFunOnFinite _ _ _ hB.finite.to_subtype ..) := by
  ext e f
  simp [standardRep]

lemma Rep.standardRep_fullRank [RankFinite M] (v : M.Rep 𝔽 W) (hB : M.IsBase B) :
    (v.standardRep hB).FullRank := by
  rw [v.standardRep_eq_mapEquiv]
  exact (v.standardRep_fullRank' hB).compEquiv _

lemma exists_eq_comp_standardRep' {𝔽 W : Type*} [Field 𝔽] [AddCommGroup W] [Module 𝔽 W]
    (v : M.Rep 𝔽 W) (hB : M.IsBase B) :
    ∃ (φ : (B →₀ 𝔽) →ₗ[𝔽] W) (hφ : LinearMap.ker φ = ⊥), v = (v.standardRep' hB).comp' φ hφ := by
  let ψ := (v.restrictSpan_fullRank.basis_of_isBase hB).repr
  let r := (span 𝔽 (range v)).subtype
  refine ⟨r.comp ψ.symm.toLinearMap, ?_, ?_⟩
  · rw [LinearMap.ker_comp, ker_subtype, comap_bot, LinearEquiv.ker]
  have h2 := v.restrictSpan_comp.symm
  rwa [← v.restrictSpan.compEquiv_compEquiv_symm ψ] at h2

-- Loopy matroids are trivially representable over every field.
def loopyRep (E : Set α) (𝔽 : Type*) [DivisionRing 𝔽] : (loopyOn E).Rep 𝔽 𝔽 where
  to_fun := 0
  indep_iff' := by simp

-- The empty matroid is trivially representable over every field.
def emptyRep (α : Type*) (𝔽 : Type*) [DivisionRing 𝔽] : (emptyOn α).Rep 𝔽 𝔽 where
  to_fun := 0
  indep_iff' := by simp

noncomputable def freeRep (E : Set α) [DecidablePred (· ∈ E)] (𝔽 : Type*) [DivisionRing 𝔽] :
    (freeOn E).Rep 𝔽 (E →₀ 𝔽) where
  to_fun x := if hx : x ∈ E then Finsupp.single ⟨x, hx⟩ 1 else 0
  indep_iff' I := by
    simp only [freeOn_indep_iff, LinearIndepOn]
    refine ⟨fun h ↦ ?_, fun h e heI ↦ by_contra fun heE ↦ ?_⟩
    · convert (Finsupp.basisSingleOne (R := 𝔽)).linearIndependent.comp _ (Set.inclusion_injective h)
        with ⟨x, hx⟩
      simp [dif_pos (h hx)]
    have hcon := h.ne_zero ⟨e, heI⟩
    rw [dif_neg heE] at hcon
    exact hcon rfl

protected noncomputable def ofBaseCobaseFun (B E : Set α) [DecidablePred (· ∈ B)]
    [DecidablePred (· ∈ E)] (v : (E \ B : Set α) → (B →₀ 𝔽)) : Matroid α :=
  Matroid.ofFun 𝔽 E <| fun e ↦
    if heB : e ∈ B then Finsupp.single ⟨e,heB⟩ 1
    else if heE : e ∈ E then v ⟨e, ⟨heE, heB⟩⟩
    else 0

section FunStandard

variable {i : β → α} {v : M.Rep 𝔽 (β → 𝔽)}

/-- Given an injection `i` from the rows to the columns of a matrix representation `v` of `M`,
`Rep.FunStandard v i` means that the range of `i` indexes an identity submatrix. -/
structure Rep.FunStandard (v : M.Rep 𝔽 (β → 𝔽)) (i : β → α) : Prop where
  apply_eq : ∀ b, v (i b) b = 1
  apply_ne : ∀ ⦃b b'⦄, b ≠ b' → v (i b) b' = 0

lemma Rep.FunStandard.injective (hv : v.FunStandard i) : Injective i :=
  fun _ _ hbb' ↦ by_contra fun hne ↦ by simpa [hbb', hv.apply_eq] using hv.apply_ne hne

lemma Rep.FunStandard.subset_ground (hv : v.FunStandard i) : range i ⊆ M.E := by
  rintro _ ⟨b, rfl⟩
  exact v.mem_ground_of_apply_ne_zero fun hb ↦ by simpa [hb] using hv.apply_eq b

lemma Rep.FunStandard.apply_eq_single [DecidableEq β] (hv : v.FunStandard i) (b : β) :
    v (i b) = Pi.single b 1 := by
  ext b'
  obtain rfl | hne := eq_or_ne b b'
  · simp [hv.apply_eq]
  rw [hv.apply_ne hne, Pi.single_eq_of_ne hne.symm]

set_option backward.isDefEq.respectTransparency false in
lemma Rep.FunStandard.IsBase [M.RankFinite] (hv : v.FunStandard i) : M.IsBase (range i) := by
  classical
  have h1 : M.Indep (range i) := by
    rw [v.indep_iff, linearIndepOn_range_iff hv.injective]
    convert (Finsupp.basisSingleOne (ι := β) (R := 𝔽)).linearIndependent.map
      (f := Finsupp.lcoeFun) (by simp)
    ext x y
    simp [Finsupp.single, Pi.single, hv.apply_eq_single]
  have hβ : Finite β := h1.finite.of_injective_finite_range hv.injective
  refine h1.isBase_of_spanning ?_
  rw [v.spanning_iff, le_antisymm_iff, and_iff_right (span_mono (image_subset_range ..))]
  have hss : range (Pi.basisFun 𝔽 β) ⊆ v '' (range i) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨i b, mem_range_self b, by rw [hv.apply_eq_single, Pi.basisFun_apply]⟩
  exact le_trans (by simp) <| span_mono hss

end FunStandard

section IsStandard





variable {γ : Type*} {B : Set α} [FunLike γ B 𝔽] [AddCommGroup γ] [Module 𝔽 γ]

/-- A representation over `B → 𝔽` or `B →₀ 𝔽` `IsStandard` if it is the identity on `B`.
The definition is agnostic as to whether the representation is `Finsupp` or `Function`,
and is phrased without `Function.Pi` to avoid decidability assumptions.

In the `Finsupp` case, this implies that `B` is a base - see `Matroid.Rep.IsStandard.isBase`.

In the `Function` case, we really need a `FiniteRank` assumption for this to be sensible,
since, if `I` is an infinite identity matrix and `1` means the all-ones vector, then `[I | 1]`
represents a free matroid in which `I` doesn't correspond to a base. -/
@[mk_iff]
structure Rep.IsStandard (v : M.Rep 𝔽 γ) : Prop where
  apply_eq : ∀ x : B, v x.1 x = 1
  apply_ne : ∀ ⦃x y : B⦄, x ≠ y → v x.1 y = 0

@[mk_iff]
structure Rep.IsStandard' (v : M.Rep 𝔽 (B → 𝔽)) : Prop where
  apply_eq : ∀ x : B, v x.1 x = 1
  apply_ne : ∀ ⦃x y : B⦄, x ≠ y → v x.1 y = 0

lemma Rep.IsStandard.apply_mem_eq {v : M.Rep 𝔽 γ} (hv : v.IsStandard) (he : e ∈ B) :
    v e ⟨e, he⟩ = 1 :=
  hv.apply_eq ⟨e,he⟩

lemma Rep.IsStandard.apply_mem_ne {v : M.Rep 𝔽 γ} (hv : v.IsStandard) (he : e ∈ B)
    (hf : f ∈ B) (hef : e ≠ f) : v e ⟨f, hf⟩ = 0 :=
  hv.apply_ne (x := ⟨e, he⟩) (y := ⟨f, hf⟩) (by simpa)

lemma Rep.IsStandard'.apply_eq_single [DecidableEq B] {v : M.Rep 𝔽 (B → 𝔽)} (hv : v.IsStandard')
    (x : B) : v x = Pi.single x 1 := by
  ext i
  obtain rfl | hne := eq_or_ne x i
  · simp [hv.apply_eq]
  rw [hv.apply_ne hne, Pi.single_eq_of_ne' hne]

lemma Rep.IsStandard.injOn {v : M.Rep 𝔽 γ} (hv : v.IsStandard) : Set.InjOn v B := by
  refine fun e he f hf hef ↦ by_contra fun hne ↦ ?_
  replace hef := DFunLike.congr_fun hef ⟨e, he⟩
  rw [hv.apply_mem_eq, hv.apply_mem_ne hf _ <| Ne.symm hne] at hef
  simp at hef

lemma Rep.IsStandard.image_coe_support_subset {v : M.Rep 𝔽 γ} (_ : v.IsStandard) {e : α} :
    (↑) '' (support (v e) : Set B) ⊆ B := by
  simp

lemma Rep.IsStandard.apply_finsupp {v : M.Rep 𝔽 (B →₀ 𝔽)} (hv : v.IsStandard) (e : B) :
    v e = Finsupp.single e 1 := by
  ext i
  obtain rfl | hne := eq_or_ne e i
  · rw [single_eq_same, hv.apply_eq]
  rw [single_eq_of_ne hne.symm, hv.apply_ne hne]

lemma isStandard_finsupp_iff {v : M.Rep 𝔽 (B →₀ 𝔽)} :
    v.IsStandard ↔ ∀ e : B, v e = Finsupp.single e 1 := by
  refine ⟨fun h e ↦ h.apply_finsupp e, fun h ↦ ?_⟩
  simp only [Rep.isStandard_iff, h, single_eq_same, implies_true, ne_eq, true_and]
  exact fun _ _ h ↦ single_eq_of_ne (Ne.symm h)

lemma Rep.IsStandard.apply_finsupp_mem {v : M.Rep 𝔽 (B →₀ 𝔽)} (hv : v.IsStandard) (he : e ∈ B) :
    v e = Finsupp.single ⟨e,he⟩ 1 :=
  hv.apply_finsupp ⟨e, he⟩

lemma Rep.IsStandard.isBase {v : M.Rep 𝔽 (B →₀ 𝔽)} (hv : v.IsStandard) : M.IsBase B := by
  rw [← v.ofFun_self]
  apply Finsupp.basisSingleOne.ofFun_isBase (fun x ↦ by simp [hv.apply_finsupp x])
  exact fun e heB ↦ v.mem_ground_of_apply_ne_zero <| by simp [hv.apply_finsupp_mem heB]

set_option backward.isDefEq.respectTransparency false in
lemma Rep.standardRep'_isStandard (v : M.Rep 𝔽 W) (hB : M.IsBase B) :
    (v.standardRep' hB).IsStandard := by
  simp only [standardRep', FullRank.basis_of_isBase, isStandard_iff, compEquiv_apply,
    restrict_span_apply, rangeFactorization, inclusion_mk, Basis.mkImage_repr, ne_eq]
  refine ⟨fun e ↦ ?_, fun e f hne ↦ ?_⟩
  · rw [LinearIndependent.repr_eq_single, single_eq_same]
    rfl
  rw [LinearIndependent.repr_eq_single, single_eq_of_ne (Ne.symm hne)]
  rfl

lemma Rep.IsStandard.image_eq {v : M.Rep 𝔽 (B →₀ 𝔽)} (hv : v.IsStandard) (I : Set B) :
    v '' I = Finsupp.basisSingleOne (ι := B) (R := 𝔽) '' I := by
  ext e
  simp only [mem_image, coe_basisSingleOne]
  constructor
  · rintro ⟨x, ⟨y : B, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, (hv.apply_finsupp y).symm⟩
  rintro ⟨x, hx, rfl⟩
  exact ⟨x, ⟨_, hx, rfl⟩, hv.apply_finsupp x⟩

lemma Rep.IsStandard.image_subset_eq {v : M.Rep 𝔽 (B →₀ 𝔽)} (hv : v.IsStandard) (hIB : I ⊆ B) :
    v '' I = Finsupp.basisSingleOne (ι := B) (R := 𝔽) '' (B ↓∩ I) := by
  rw [← hv.image_eq]
  simp [inter_eq_self_of_subset_right hIB]

lemma Rep.IsStandard.mem_closure_iff {v : M.Rep 𝔽 (B →₀ 𝔽)} (hv : v.IsStandard) (hIB : I ⊆ B)
    (heE : e ∈ M.E) : e ∈ M.closure I ↔ ((v e).support : Set B) ⊆ B ↓∩ I := by
  rw [v.closure_eq, mem_inter_iff, mem_preimage, hv.image_subset_eq hIB, SetLike.mem_coe,
    Finsupp.basisSingleOne.mem_span_image, basisSingleOne_repr, LinearEquiv.refl_apply,
    and_iff_left heE]

/-- For every column `e` of `M.E \ B`, the support of `v e` as a subset of `B`,
together with `e` itself, make a circuit of `M`. -/
lemma Rep.IsStandard.isCircuit_insert_support {v : M.Rep 𝔽 (B →₀ 𝔽)} (hv : v.IsStandard)
    (heB : e ∉ B) (heE : e ∈ M.E) : M.IsCircuit (insert e ((↑) '' ((v e).support : Set B))) := by
  let b := Finsupp.basisSingleOne (ι := B) (R := 𝔽)
  refine Indep.insert_isCircuit_of_forall (hv.isBase.indep.subset (by simp)) (by simp [heB]) ?_ ?_
  · rw [hv.mem_closure_iff (by simp) heE]
    simp
  intro f hf hecl
  rw [hv.mem_closure_iff (diff_subset.trans (by simp)) heE] at hecl
  simp only [preimage_diff, Subtype.val_injective, preimage_image_eq] at hecl
  obtain ⟨f,h,rfl⟩ := ((image_mono hecl) hf)
  simp at h

lemma Rep.IsStandard.image_val_support_eq {v : M.Rep 𝔽 (B →₀ 𝔽)} (hv : v.IsStandard) (he : e ∉ B) :
    ((v e).support : Set B) = (M.fundCircuit e B) ∩ B := by
  obtain heE | heE := em' (e ∈ M.E)
  · rw [v.eq_zero_of_notMem_ground heE, ← fundCircuit_diff_eq_inter _ he,
      fundCircuit_eq_of_notMem_ground heE]
    simp
  suffices hrw : insert e ((↑) '' ((v e).support : Set B)) = M.fundCircuit e B
  · rw [← fundCircuit_diff_eq_inter _ he, ← hrw, insert_diff_of_mem _ (by simp),
      diff_singleton_eq_self (by simp [he])]
  refine IsCircuit.eq_fundCircuit_of_subset ?_ hv.isBase.indep (insert_subset_insert (by simp))
  exact isCircuit_insert_support hv he heE

/-- For every `e ∈ B`, the support of the row of `v` corresponding to `e` is a cocircuit of `M`. -/
lemma Rep.IsStandard.isCocircuit_insert_support {v : M.Rep 𝔽 (B →₀ 𝔽)} (hv : v.IsStandard) (e : B) :
    M.IsCocircuit (v · e).support := by
  suffices h_eq : (v · e).support = M.E \ M.closure (B \ {e.1}) by
    rw [h_eq, isCocircuit_compl_iff_isHyperplane]
    exact hv.isBase.isHyperplane_of_closure_diff_singleton e.2
  ext x
  simp only [mem_support, ne_eq, mem_diff]
  obtain hxE | hxE := em' (x ∈ M.E)
  · simp [hxE, v.eq_zero_of_notMem_ground hxE]
  rw [hv.mem_closure_iff diff_subset hxE]
  simp [subset_diff, hxE, disjoint_iff_forall_ne]


end IsStandard
-- lemma Rep.IsStandard.support_eq (v : M.Rep 𝔽 (B →₀ F))

section Representable

/-- A `Representable` matroid is one that has a representation over `𝔽`.
To avoid quantifying over types, we require that the representation is over the module `α → 𝔽`.
`Rep.Representable`, which is defined later, makes this definition useful.  -/
def Representable (M : Matroid α) (𝔽 : Type*) [Semiring 𝔽] : Prop :=
  Nonempty (M.Rep 𝔽 (α → 𝔽))

/-- Any representation makes a matroid representable. -/
lemma Rep.representable (v : M.Rep 𝔽 W) : M.Representable 𝔽 :=
  let ⟨B, hB⟩ := M.exists_isBase
  ⟨(v.standardRep hB).comp' (ExtendByZero.linearMap 𝔽 ((↑) : B → α))
    (LinearMap.ker_eq_bot.2 (ExtendByZero.linearMap_injective _ Subtype.val_injective))⟩

@[simp] lemma loopyOn_representable (E : Set α) (𝔽 : Type*) [DivisionRing 𝔽] :
    (loopyOn E).Representable 𝔽 :=
  (loopyRep E 𝔽).representable

@[simp] lemma emptyOn_representable (α 𝔽: Type*) [DivisionRing 𝔽] :
    (emptyOn α).Representable 𝔽 :=
  (emptyRep α 𝔽).representable

lemma Representable.map (hM : M.Representable 𝔽) {f : α → β} (hf : InjOn f M.E) :
    (M.map f hf).Representable 𝔽 := by
  classical
  exact (hM.some.map f hf).representable

lemma Representable.iso {N : Matroid β} (hM : M.Representable 𝔽) (i : M ≂ N) :
    N.Representable 𝔽 := by
  classical
  obtain ⟨rfl, rfl⟩ | ⟨f, hf, rfl⟩ := i.empty_empty_or_exists_eq_map
  · exact ⟨0, by simp⟩
  exact hM.map hf

lemma Representable.exists_fullRank_rep (hM : M.Representable 𝔽) (hB : M.IsBase B) :
    ∃ v : M.Rep 𝔽 (B →₀ 𝔽), v.FullRank :=
  ⟨hM.some.standardRep' hB, (Nonempty.some hM).standardRep_fullRank' hB⟩

lemma Representable.exists_isStandard_rep (hM : M.Representable 𝔽) (hB : M.IsBase B) :
    ∃ v : M.Rep 𝔽 (B →₀ 𝔽), v.IsStandard :=
  ⟨hM.some.standardRep' hB, Rep.standardRep'_isStandard (Nonempty.some hM) hB⟩

lemma Representable.exists_fin_rep [RankFinite M] (hM : M.Representable 𝔽) :
    ∃ v : M.Rep 𝔽 (Fin M.rank → 𝔽), v.FullRank := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  obtain ⟨B, rfl⟩ := hB.finite.exists_finset_coe
  let e : ↥B ≃ Fin M.rank := B.equivFinOfCardEq hB.finset_card
  exact ⟨(hM.some.standardRep hB).compEquiv (LinearEquiv.funCongrLeft _ _ e.symm),
    (Rep.standardRep_fullRank _ hB).compEquiv _⟩

lemma Representable.exists_fin_rep_of_eq {n : ℕ} [RankFinite M] (hM : M.Representable 𝔽)
    (hr : M.rank = n) : ∃ v : M.Rep 𝔽 (Fin n → 𝔽), v.FullRank := by
  subst hr
  exact exists_fin_rep hM
