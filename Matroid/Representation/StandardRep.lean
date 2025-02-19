import Matroid.Representation.Map
import Matroid.Flat.Hyperplane

variable {α β W W' 𝔽 R : Type*} {e f x : α} {I E B X Y : Set α} {M : Matroid α} [DivisionRing 𝔽]
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W']

open Set Function Submodule Finsupp Set.Notation

theorem Function.ExtendByZero.linearMap_injective (R : Type*) {ι η : Type _} [Semiring R]
  {s : ι → η} (hs : Function.Injective s) :
    Injective <| Function.ExtendByZero.linearMap R s := by
  intro x x' h
  ext i
  replace h := _root_.congr_fun h (s i)
  simp only [ExtendByZero.linearMap_apply, exists_apply_eq_apply, not_true] at h
  rwa [hs.extend_apply, hs.extend_apply] at h

namespace Matroid

lemma Rep.range_subset_span_isBase (v : M.Rep 𝔽 W) (hB : M.IsBase B) :
    range v ⊆ span 𝔽 (v '' B) := by
  rintro _ ⟨e, he ,rfl⟩
  obtain (heB | heB) := em (e ∈ B)
  · exact subset_span (mem_image_of_mem _ heB)
  set f := v e
  by_contra h'
  have hind : LinearIndependent 𝔽 ((↑) : (insert f (v '' B) : Set W) → W) :=
    (LinearIndependent.insert ?_ h')
  · rw [← image_insert_eq, ← v.indep_iff_image_of_inj] at hind
    · exact heB (hB.mem_of_insert_indep hind)
    rw [injOn_insert heB, and_iff_right (v.injOn_of_indep hB.indep)]
    exact fun h'' ↦ h' <| mem_of_mem_of_subset h'' subset_span
  exact v.indep_image hB.indep

lemma Rep.span_isBase_eq (v : M.Rep 𝔽 W) (hB : M.IsBase B) :
    span 𝔽 (v '' B) = span 𝔽 (range v) := by
  rw [eq_comm]
  exact span_eq_of_le _ (v.range_subset_span_isBase hB) (span_mono (image_subset_range _ _))

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
def Rep.restrict_span (v : M.Rep 𝔽 W) : M.Rep 𝔽 (span 𝔽 (range v)) where
  to_fun := codRestrict v _ (fun x ↦ subset_span (mem_range_self _))
  valid' := (by
    intro I
    rw [v.indep_iff]
    refine ⟨fun h ↦ LinearIndependent.of_comp (Submodule.subtype _) (by rwa [coe_subtype]),
      fun h ↦ h.map' (Submodule.subtype _) (ker_subtype _)⟩ )

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

lemma Rep.restrict_span_eq_inclusion (v : M.Rep 𝔽 W) :
  (v.restrict_span : α → _) = Set.inclusion subset_span ∘ rangeFactorization v := by ext; rfl

@[simp] lemma Rep.restrict_span_apply (v : M.Rep 𝔽 W) (e : α) :
  v.restrict_span e = Set.inclusion subset_span (rangeFactorization v e) := rfl

lemma Rep.restrict_span_fullRank (v : M.Rep 𝔽 W) : v.restrict_span.FullRank := by
  change _ ≤ span 𝔽 _
  rw [restrict_span_eq_inclusion]
  change _ ≤ span 𝔽 (range (Set.inclusion subset_span ∘ _))
  rw [range_comp, surjective_onto_range.range_eq, image_univ, Set.range_inclusion]
  change _ ≤ span 𝔽 ((Submodule.subtype (span 𝔽 (range ↑v))) ⁻¹' _)
  simp

/-- A base of `M` gives a linear basis in a full-rank representation -/
noncomputable def Rep.FullRank.basis_of_isBase {v : M.Rep 𝔽 W} (h : v.FullRank)
    (hB : M.IsBase B) : _root_.Basis B 𝔽 W :=
  Basis.mk (v.onIndep hB.indep) ( by rw [← h.span_range, range_restrict, v.span_isBase_eq hB] )

lemma Rep.FullRank.mapEquiv {v : M.Rep 𝔽 W} (h : v.FullRank) (ψ : W ≃ₗ[𝔽] W') :
    (v.mapEquiv ψ).FullRank := by
  rw [Rep.fullRank_iff, Rep.mapEquiv, map', map, ← Rep.to_fun_eq_coe]
  simp [LinearEquiv.coe_coe, range_comp, h.span_range, span_image]

/-- A base of `M` gives a (linear) basis for the span of the range of a representation -/
noncomputable def Rep.isBasis_of_isBase (v : M.Rep 𝔽 W) (hB : M.IsBase B) :
    _root_.Basis B 𝔽 (span 𝔽 (range v)) :=
  (Basis.span (v.onIndep hB.indep)).map <| LinearEquiv.ofEq _ _ (by simp [v.span_isBase_eq hB])

/-- The natural representation with rows indexed by a base with `Finsupp` -/
noncomputable def Rep.standardRep' (v : M.Rep 𝔽 W) (hB : M.IsBase B) :
    M.Rep 𝔽 (B →₀ 𝔽) :=
  v.restrict_span.mapEquiv (v.restrict_span_fullRank.basis_of_isBase hB).repr

@[simp] lemma Rep.standardRep_eq_one' (v : M.Rep 𝔽 W) (hB : M.IsBase B) (e : B) :
    (v.standardRep' hB) e e = 1 := by
  simp only [Rep.standardRep', Rep.FullRank.basis_of_isBase, Rep.mapEquiv_apply,
    Rep.restrict_span_apply, Basis.mk_repr]
  rw [LinearIndependent.repr_eq_single (i := e) _ _ (by simp)]
  simp

lemma Rep.standardRep_eq_zero' (v : M.Rep 𝔽 W) (hB : M.IsBase B) (e f : B) (hef : e ≠ f) :
    (v.standardRep' hB) e f = 0 := by
  simp [Rep.standardRep', Rep.FullRank.basis_of_isBase, Rep.mapEquiv_apply,
    Rep.restrict_span_apply, Basis.mk_repr]
  rw [LinearIndependent.repr_eq_single (i := e) _ _ (by simp)]
  exact Finsupp.single_eq_of_ne hef

lemma Rep.standardRep_fullRank' (v : M.Rep 𝔽 W) (hB : M.IsBase B) : (v.standardRep' hB).FullRank :=
  v.restrict_span_fullRank.mapEquiv _

/-- The natural representation of a matroid with rows indexed by a base -/
noncomputable def Rep.standardRep (v : M.Rep 𝔽 W) (hB : M.IsBase B) : M.Rep 𝔽 (B → 𝔽) :=
  (v.standardRep' hB).map Finsupp.lcoeFun (by simp [Submodule.disjoint_def, Finsupp.lcoeFun])

lemma Rep.standardRep_eq_one (v : M.Rep 𝔽 W) (hB : M.IsBase B) (e : B) :
    (v.standardRep hB) e e = 1 := by
  simp [standardRep]

lemma Rep.standardRep_eq_zero (v : M.Rep 𝔽 W) (hB : M.IsBase B) (e f : B) (hef : e ≠ f) :
    (v.standardRep hB) e f = 0 := by
  simp [standardRep, v.standardRep_eq_zero' hB _ _ hef]

lemma Rep.standardRep_eq_mapEquiv [RankFinite M] (v : M.Rep 𝔽 W) (hB : M.IsBase B) :
    v.standardRep hB = (v.standardRep' hB).mapEquiv
      (@Finsupp.linearEquivFunOnFinite _ _ _ hB.finite.to_subtype ..) := by
  ext e f
  simp [standardRep]

lemma Rep.standardRep_fullRank [RankFinite M] (v : M.Rep 𝔽 W) (hB : M.IsBase B) :
    (v.standardRep hB).FullRank := by
  rw [v.standardRep_eq_mapEquiv]
  exact (v.standardRep_fullRank' hB).mapEquiv _

-- IsLoopy matroids are trivially representable over every field.
def loopyRep (E : Set α) (𝔽 : Type*) [DivisionRing 𝔽] : (loopyOn E).Rep 𝔽 𝔽 where
  to_fun := 0
  valid' := by
    refine fun I ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · obtain rfl := loopyOn_indep_iff.1 h
      apply linearIndependent_empty_type
    rw [loopyOn_indep_iff, eq_empty_iff_forall_not_mem]
    exact fun x hxI ↦ h.ne_zero ⟨x, hxI⟩ rfl

-- The empty matroid is trivially representable over every field.
def emptyRep (α : Type*) (𝔽 : Type*) [DivisionRing 𝔽] : (emptyOn α).Rep 𝔽 𝔽 where
  to_fun := 0
  valid' := by simp

protected noncomputable def ofBaseCobaseFun (B E : Set α) [DecidablePred (· ∈ B)]
    [DecidablePred (· ∈ E)] (v : (E \ B : Set α) → (B →₀ 𝔽)) : Matroid α :=
  Matroid.ofFun 𝔽 E <| fun e ↦
    if heB : e ∈ B then Finsupp.single ⟨e,heB⟩ 1
    else if heE : e ∈ E then v ⟨e, ⟨heE, heB⟩⟩
    else 0

section IsStandard



/-- A representation over `B → 𝔽` or `B →₀ 𝔽` `IsStandard` if it is the identity on `B`.
The definition is agnostic as to whether the representation is `Finsupp` or `Function`,
and is phrased without `Function.Pi` to avoid decidability assumptions.  -/
@[mk_iff]
structure Rep.IsStandard {γ : Type*} [FunLike γ B 𝔽] [AddCommGroup γ] [Module 𝔽 γ]
    (v : M.Rep 𝔽 γ) : Prop where
  apply_eq : ∀ x : B, v x.1 x = 1
  apply_ne : ∀ ⦃x y : B⦄, x ≠ y → v x.1 y = 0

variable {v : M.Rep 𝔽 (B →₀ 𝔽)}

lemma Rep.IsStandard.apply_finsupp {v : M.Rep 𝔽 (B →₀ 𝔽)} (hv : v.IsStandard) (e : B) :
    v e = Finsupp.single e 1 := by
  ext i
  obtain rfl | hne := eq_or_ne e i
  · rw [single_eq_same, hv.apply_eq]
  rw [single_eq_of_ne hne, hv.apply_ne hne]

-- `Rep.IsStandard` means that `v` is a representation comprising finitely
-- supported `B`-indexed vectors that is the identity on `B`. It follows that `B` is a base.
-- def Rep.IsStandard (v : M.Rep 𝔽 (B →₀ 𝔽)) : Prop := ∀ e : B, v e = Finsupp.single e 1

-- lemma Rep.IsStandard.apply (hv : v.IsStandard) (e : B) : v e = Finsupp.single e 1 :=
--   hv e

lemma Rep.IsStandard.apply_finsupp_mem (hv : v.IsStandard) (he : e ∈ B) :
    v e = Finsupp.single ⟨e,he⟩ 1 :=
  hv.apply_finsupp ⟨e, he⟩

lemma Rep.IsStandard.isBase (hv : v.IsStandard) : M.IsBase B := by
  rw [← v.ofFun_self]
  apply Finsupp.basisSingleOne.ofFun_isBase (fun x ↦ by simp [hv.apply_finsupp x])
  exact fun e heB ↦ v.mem_ground_of_apply_ne_zero <| by simp [hv.apply_finsupp_mem heB]

lemma Rep.standardRep'_isStandard (v : M.Rep 𝔽 W) (hB : M.IsBase B) :
    (v.standardRep' hB).IsStandard := by
  simp only [standardRep', FullRank.basis_of_isBase, isStandard_iff, to_fun_eq_coe, mapEquiv_apply,
    restrict_span_apply, rangeFactorization, inclusion_mk, Basis.mk_repr, ne_eq,
    Subtype.mk.injEq]
  refine ⟨fun e ↦ ?_, fun e f hef ↦ ?_⟩
  · rw [LinearIndependent.repr_eq_single _ e, single_eq_same]
    simp
  rw [LinearIndependent.repr_eq_single _ e, single_eq_of_ne hef]
  simp

lemma Rep.IsStandard.injOn (hv : v.IsStandard) : Set.InjOn v B := by
  intro e he f hf hef
  rw [hv.apply_finsupp_mem he, hv.apply_finsupp_mem hf] at hef
  simpa using (Finsupp.single_left_injective (by simp)) hef

lemma Rep.IsStandard.image_coe_support_subset (_hv : v.IsStandard) {e : α} :
    (↑) '' ((v e).support : Set B) ⊆ B := by
  simp

lemma Rep.IsStandard.image_eq (hv : v.IsStandard) (I : Set B) :
    v '' I = Finsupp.basisSingleOne (ι := B) (R := 𝔽) '' I := by
  ext e
  simp only [mem_image, exists_and_right, exists_eq_right, coe_basisSingleOne]
  constructor
  · rintro ⟨x, ⟨y : B, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, (hv.apply_finsupp y).symm⟩
  rintro ⟨x, hx, rfl⟩
  exact ⟨x, ⟨_, hx, rfl⟩, hv.apply_finsupp x⟩

lemma Rep.IsStandard.image_subset_eq (hv : v.IsStandard) (hIB : I ⊆ B) :
    v '' I = Finsupp.basisSingleOne (ι := B) (R := 𝔽) '' (B ↓∩ I) := by
  rw [← hv.image_eq]
  simp [inter_eq_self_of_subset_right hIB]

lemma Rep.IsStandard.mem_closure_iff (hv : v.IsStandard) (hIB : I ⊆ B) (heE : e ∈ M.E) :
    e ∈ M.closure I ↔ ((v e).support : Set B) ⊆ B ↓∩ I := by
  rw [v.closure_eq, mem_inter_iff, mem_preimage, hv.image_subset_eq hIB, SetLike.mem_coe,
    Finsupp.basisSingleOne.mem_span_image, basisSingleOne_repr, LinearEquiv.refl_apply,
    and_iff_left heE]

/-- For every column `e` of `M.E \ B`, the support of `v e` as a subset of `B`,
together with `e` itself, make a circuit of `M`. -/
lemma Rep.IsStandard.isCircuit_insert_support (hv : v.IsStandard) (heB : e ∉ B)
    (heE : e ∈ M.E) : M.IsCircuit (insert e ((↑) '' ((v e).support : Set B))) := by
  let b := Finsupp.basisSingleOne (ι := B) (R := 𝔽)
  refine Indep.insert_isCircuit_of_forall (hv.isBase.indep.subset (by simp)) (by simp [heB]) ?_ ?_
  · rw [hv.mem_closure_iff (by simp) heE]
    simp
  intro f hf hecl
  rw [hv.mem_closure_iff (diff_subset.trans (by simp)) heE] at hecl
  simp only [preimage_diff, Subtype.val_injective, preimage_image_eq, subset_diff_singleton_iff]
    at hecl
  obtain ⟨f,h,rfl⟩ := ((image_mono hecl) hf)
  simp at h

lemma Rep.IsStandard.image_val_support_eq (hv : v.IsStandard) (he : e ∉ B) :
    ((v e).support : Set B) = (M.fundCircuit e B) ∩ B := by
  obtain heE | heE := em' (e ∈ M.E)
  · rw [v.eq_zero_of_not_mem_ground heE, ← fundCircuit_diff_eq_inter _ he,
      fundCircuit_eq_of_not_mem_ground heE]
    simp
  suffices hrw : insert e ((↑) '' ((v e).support : Set B)) = M.fundCircuit e B
  · rw [← fundCircuit_diff_eq_inter _ he, ← hrw, insert_diff_of_mem _ (by simp),
      diff_singleton_eq_self (by simp [he])]
  refine IsCircuit.eq_fundCircuit_of_subset ?_ hv.isBase.indep (insert_subset_insert (by simp))
  exact isCircuit_insert_support hv he heE

/-- For every `e ∈ B`, the support of the row of `v` corresponding to `e` is a cocircuit of `M`. -/
lemma Rep.IsStandard.cocircuit_insert_support (hv : v.IsStandard) (e : B) :
    M.Cocircuit (v · e).support := by
  suffices h_eq : (v · e).support = M.E \ M.closure (B \ {e.1}) by
    rw [h_eq, compl_cocircuit_iff_isHyperplane]
    exact hv.isBase.isHyperplane_of_closure_diff_singleton e.2
  ext x
  simp only [mem_support, ne_eq, mem_diff]
  obtain hxE | hxE := em' (x ∈ M.E)
  · simp [hxE, v.eq_zero_of_not_mem_ground hxE]
  rw [hv.mem_closure_iff diff_subset hxE]
  simp [subset_diff, hxE, not_iff_not, disjoint_iff_forall_ne]


end IsStandard
-- lemma Rep.IsStandard.support_eq (v : M.Rep 𝔽 (B →₀ F))

section Representable

/- This can't currently be moved to somewhere earlier,
since the crucial `Rep.representable` relies on standard representations.
-/

lemma Rep.representable (v : M.Rep 𝔽 W) : M.Representable 𝔽 :=
  let ⟨B, hB⟩ := M.exists_isBase
  ⟨(v.standardRep hB).map' (ExtendByZero.linearMap 𝔽 ((↑) : B → α))
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
  exact (hM.some.matroidMap f hf).representable

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
  exact ⟨(hM.some.standardRep hB).mapEquiv (LinearEquiv.funCongrLeft _ _ e.symm),
    (Rep.standardRep_fullRank _ hB).mapEquiv _⟩

lemma Representable.exists_fin_rep_of_eq {n : ℕ} [RankFinite M] (hM : M.Representable 𝔽)
    (hr : M.rank = n) : ∃ v : M.Rep 𝔽 (Fin n → 𝔽), v.FullRank := by
  subst hr
  exact exists_fin_rep hM
