import Matroid.Representation.Map
import Matroid.Flat.Hyperplane

variable {α β W W' 𝔽 R : Type*} {e f x : α} {I E B X Y : Set α} {M : Matroid α} [DivisionRing 𝔽]
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W']

open Set Function Submodule Finsupp Set.Notation

namespace Matroid

lemma Rep.range_subset_span_base (v : M.Rep 𝔽 W) (hB : M.Base B) : range v ⊆ span 𝔽 (v '' B) := by
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

lemma Rep.span_range_eq_span_base (v : M.Rep 𝔽 W) (hB : M.Base B) :
     span 𝔽 (range (Set.restrict B v)) = span 𝔽 (range v) := by
  rw [range_restrict, eq_comm]
  exact span_eq_of_le _ (v.range_subset_span_base hB) (span_mono (image_subset_range _ _))

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
noncomputable def Rep.FullRank.basis_of_base {v : M.Rep 𝔽 W} (h : v.FullRank) (hB : M.Base B) :
    _root_.Basis B 𝔽 W :=
  Basis.mk (v.onIndep hB.indep) ( by rw [← h.span_range, v.span_range_eq_span_base hB] )

lemma Rep.FullRank.mapEquiv {v : M.Rep 𝔽 W} (h : v.FullRank) (ψ : W ≃ₗ[𝔽] W') :
    (v.mapEquiv ψ).FullRank := by
  rw [Rep.fullRank_iff, Rep.mapEquiv, map', map, ← Rep.to_fun_eq_coe]
  simp [LinearEquiv.coe_coe, range_comp, h.span_range, span_image]

/-- A base of `M` gives a (linear) basis for the span of the range of a representation -/
noncomputable def Rep.basis_of_base (v : M.Rep 𝔽 W) (hB : M.Base B) :
    _root_.Basis B 𝔽 (span 𝔽 (range v)) :=
  (Basis.span (v.onIndep hB.indep)).map <| LinearEquiv.ofEq _ _ (v.span_range_eq_span_base hB)

/-- The natural representation with rows indexed by a base with `Finsupp` -/
noncomputable def Rep.standardRep' (v : M.Rep 𝔽 W) (hB : M.Base B) :
    M.Rep 𝔽 (B →₀ 𝔽) :=
  v.restrict_span.mapEquiv (v.restrict_span_fullRank.basis_of_base hB).repr

lemma Rep.standardRep_eq_one' (v : M.Rep 𝔽 W) (hB : M.Base B) (e : B) :
    (v.standardRep' hB) e e = 1 := by
  simp only [Rep.standardRep', Rep.FullRank.basis_of_base, Rep.mapEquiv_apply,
    Rep.restrict_span_apply, Basis.mk_repr]
  rw [LinearIndependent.repr_eq_single (i := e) _ _ (by simp)]
  simp

lemma Rep.standardRep_eq_zero' (v : M.Rep 𝔽 W) (hB : M.Base B) (e f : B) (hef : e ≠ f) :
    (v.standardRep' hB) e f = 0 := by
  simp [Rep.standardRep', Rep.FullRank.basis_of_base, Rep.mapEquiv_apply,
    Rep.restrict_span_apply, Basis.mk_repr]
  rw [LinearIndependent.repr_eq_single (i := e) _ _ (by simp)]
  exact Finsupp.single_eq_of_ne hef

lemma Rep.standardRep_fullRank' (v : M.Rep 𝔽 W) (hB : M.Base B) : (v.standardRep' hB).FullRank :=
  v.restrict_span_fullRank.mapEquiv _

lemma Rep.representable (v : M.Rep 𝔽 W) : M.Representable 𝔽 :=
  ⟨_, ⟨v.standardRep' M.exists_base.choose_spec⟩⟩

/-- The natural representation of a `FiniteRk` matroid with rows indexed by a base -/
noncomputable def Rep.standardRep [FiniteRk M] (v : M.Rep 𝔽 W) (hB : M.Base B) :
    M.Rep 𝔽 (B → 𝔽) :=
  have := hB.finite.to_subtype
  (v.standardRep' hB).mapEquiv (Finsupp.linearEquivFunOnFinite 𝔽 𝔽 B)

lemma Rep.standardRep_eq_one [FiniteRk M] (v : M.Rep 𝔽 W) (hB : M.Base B) (e : B) :
    (v.standardRep hB) e e = 1 := by
  classical
  have := hB.finite.to_subtype
  simp [standardRep, v.standardRep_eq_one' hB]

lemma Rep.standardRep_eq_zero [FiniteRk M] (v : M.Rep 𝔽 W) (hB : M.Base B) (e f : B)
  (hef : e ≠ f) : (v.standardRep hB) e f = 0 := by
  classical
  have := hB.finite.to_subtype
  simp [standardRep, v.standardRep_eq_zero' hB _ _ hef]

lemma Rep.standardRep_fullRank [FiniteRk M] (v : M.Rep 𝔽 W) (hB : M.Base B) :
    (v.standardRep hB).FullRank :=
  (v.standardRep_fullRank' hB).mapEquiv _

-- Loopy matroids are trivially representable over every field.
def loopyRep (E : Set α) (𝔽 : Type*) [DivisionRing 𝔽] : (loopyOn E).Rep 𝔽 𝔽 where
  to_fun := 0
  valid' := by
    refine fun I ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · obtain rfl := loopyOn_indep_iff.1 h
      apply linearIndependent_empty_type
    rw [loopyOn_indep_iff, eq_empty_iff_forall_not_mem]
    exact fun x hxI ↦ h.ne_zero ⟨x, hxI⟩ rfl

-- The empty matroid is trivially representable over every field.
def emptyRep (α : Type*) (𝔽 : Type*) [DivisionRing 𝔽] : (emptyOn α).Rep 𝔽 𝔽 :=
  (loopyRep ∅ 𝔽).ofEq <| loopyOn_empty _

protected noncomputable def ofBaseCobaseFun (B E : Set α) [DecidablePred (· ∈ B)]
    [DecidablePred (· ∈ E)] (v : (E \ B : Set α) → (B →₀ 𝔽)) : Matroid α :=
  Matroid.ofFun 𝔽 E <| fun e ↦
    if heB : e ∈ B then Finsupp.single ⟨e,heB⟩ 1
    else if heE : e ∈ E then v ⟨e, ⟨heE, heB⟩⟩
    else 0

section FinitaryBase

variable {v : M.Rep 𝔽 (B →₀ 𝔽)}

/-- `Rep.FinitaryBase` means that `v` is a representation comprising finitely
supported `B`-indexed vectors that is the identity on `B`. It follows that `B` is a base. -/
def Rep.FinitaryBase (v : M.Rep 𝔽 (B →₀ 𝔽)) : Prop := ∀ e : B, v e = Finsupp.single e 1

lemma Rep.FinitaryBase.apply (hv : v.FinitaryBase) (e : B) : v e = Finsupp.single e 1 :=
  hv e

lemma Rep.FinitaryBase.apply_mem (hv : v.FinitaryBase) (he : e ∈ B) :
    v e = Finsupp.single ⟨e,he⟩ 1 :=
  hv ⟨e, he⟩

lemma Rep.FinitaryBase.base (hv : v.FinitaryBase) : M.Base B := by
  rw [← v.ofFun_self]
  exact Finsupp.basisSingleOne.ofFun_base (fun x ↦ hv x) fun x hxB ↦
    v.mem_ground_of_apply_ne_zero <| by simp [show v x = _ from hv ⟨x, hxB⟩]

lemma Rep.FinitaryBase.injOn (hv : v.FinitaryBase) : Set.InjOn v B := by
  intro e he f hf hef
  rw [hv.apply_mem he, hv.apply_mem hf] at hef
  simpa using (Finsupp.single_left_injective (by simp)) hef

lemma Rep.FinitaryBase.image_coe_support_subset (_hv : v.FinitaryBase) {e : α} :
    (↑) '' ((v e).support : Set B) ⊆ B := by
  simp

lemma Rep.FinitaryBase.image_eq (hv : v.FinitaryBase) (I : Set B) :
    v '' I = Finsupp.basisSingleOne (ι := B) (R := 𝔽) '' I := by
  ext e
  simp only [mem_image, exists_and_right, exists_eq_right, coe_basisSingleOne]
  constructor
  · rintro ⟨x, ⟨y : B, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, (hv.apply y).symm⟩
  rintro ⟨x, hx, rfl⟩
  exact ⟨x, ⟨_, hx, rfl⟩, hv.apply x⟩

lemma Rep.FinitaryBase.image_subset_eq (hv : v.FinitaryBase) (hIB : I ⊆ B) :
    v '' I = Finsupp.basisSingleOne (ι := B) (R := 𝔽) '' (B ↓∩ I) := by
  rw [← hv.image_eq]
  simp [inter_eq_self_of_subset_right hIB]

lemma Rep.FinitaryBase.mem_closure_iff (hv : v.FinitaryBase) (hIB : I ⊆ B) (heE : e ∈ M.E) :
    e ∈ M.closure I ↔ ((v e).support : Set B) ⊆ B ↓∩ I := by
  rw [v.closure_eq, mem_inter_iff, mem_preimage, hv.image_subset_eq hIB, SetLike.mem_coe,
    Finsupp.basisSingleOne.mem_span_image, basisSingleOne_repr, LinearEquiv.refl_apply,
    and_iff_left heE]

/-- For every column `e` of `M.E \ B`, the support of `v e` as a subset of `B`,
together with `e` itself, make a circuit of `M`. -/
lemma Rep.FinitaryBase.circuit_insert_support (hv : v.FinitaryBase) (heB : e ∉ B) (heE : e ∈ M.E) :
    M.Circuit (insert e ((↑) '' ((v e).support : Set B))) := by
  let b := Finsupp.basisSingleOne (ι := B) (R := 𝔽)
  refine Indep.insert_circuit_of_forall (hv.base.indep.subset (by simp)) (by simp [heB]) ?_ ?_
  · rw [hv.mem_closure_iff (by simp) heE]
    simp
  intro f hf hecl
  rw [hv.mem_closure_iff (diff_subset.trans (by simp)) heE] at hecl
  simp only [preimage_diff, Subtype.val_injective, preimage_image_eq, subset_diff_singleton_iff]
    at hecl
  obtain ⟨f,h,rfl⟩ := ((image_mono hecl) hf)
  simp at h

lemma Rep.FinitaryBase.image_val_support_eq (hv : v.FinitaryBase) (he : e ∉ B) :
    ((v e).support : Set B) = (M.fundCircuit e B) ∩ B := by
  obtain heE | heE := em' (e ∈ M.E)
  · rw [v.eq_zero_of_not_mem_ground heE, ← fundCircuit_diff_eq_inter _ he,
      fundCircuit_eq_of_not_mem_ground heE]
    simp
  suffices hrw : insert e ((↑) '' ((v e).support : Set B)) = M.fundCircuit e B
  · rw [← fundCircuit_diff_eq_inter _ he, ← hrw, insert_diff_of_mem _ (by simp),
      diff_singleton_eq_self (by simp [he])]
  refine Circuit.eq_fundCircuit_of_subset ?_ hv.base.indep (insert_subset_insert (by simp))
  exact circuit_insert_support hv he heE

/-- For every `e ∈ B`, the support of the row of `v` corresponding to `e` is a cocircuit of `M`. -/
lemma Rep.FinitaryBase.cocircuit_insert_support (hv : v.FinitaryBase) (e : B) :
    M.Cocircuit (v · e).support := by
  suffices h_eq : (v · e).support = M.E \ M.closure (B \ {e.1}) by
    rw [h_eq, compl_cocircuit_iff_hyperplane]
    exact hv.base.hyperplane_of_closure_diff_singleton e.2
  ext x
  simp only [mem_support, ne_eq, mem_diff]
  obtain hxE | hxE := em' (x ∈ M.E)
  · simp [hxE, v.eq_zero_of_not_mem_ground hxE]
  rw [hv.mem_closure_iff diff_subset hxE]
  simp [subset_diff, hxE, not_iff_not, disjoint_iff_forall_ne]


end FinitaryBase
-- lemma Rep.FinitaryBase.support_eq (v : M.Rep 𝔽 (B →₀ F))
