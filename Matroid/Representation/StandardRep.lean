import Matroid.Representation.Basic


variable {α β W W' 𝔽 R : Type*} {e f x : α} {I E B X Y : Set α} {M : Matroid α} [Field 𝔽]
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W']

open Set Function Submodule

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
def loopyRep (E : Set α) (𝔽 : Type*) [Field 𝔽] : (loopyOn E).Rep 𝔽 𝔽 where
  to_fun := 0
  valid' := by
    refine fun I ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · obtain rfl := loopyOn_indep_iff.1 h
      apply linearIndependent_empty_type
    rw [loopyOn_indep_iff, eq_empty_iff_forall_not_mem]
    exact fun x hxI ↦ h.ne_zero ⟨x, hxI⟩ rfl

-- The empty matroid is trivially representable over every field.
def emptyRep (α : Type*) (𝔽 : Type*) [Field 𝔽] : (emptyOn α).Rep 𝔽 𝔽 :=
  (loopyRep ∅ 𝔽).ofEq <| loopyOn_empty _

protected noncomputable def ofBaseCobaseFun (B E : Set α) [DecidablePred (· ∈ B)]
    [DecidablePred (· ∈ E)] (v : (E \ B : Set α) → (B →₀ 𝔽)) : Matroid α :=
  Matroid.ofFun 𝔽 E <| fun e ↦
    if heB : e ∈ B then Finsupp.single ⟨e,heB⟩ 1
    else if heE : e ∈ E then v ⟨e, ⟨heE, heB⟩⟩
    else 0
