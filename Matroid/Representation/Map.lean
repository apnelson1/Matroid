import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
import Matroid.Representation.Basic

variable {α β W W' 𝔽 R : Type*} {e f x : α} {I E B X Y : Set α} {M : Matroid α} [DivisionRing 𝔽]
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W']

open Function Set Submodule FiniteDimensional BigOperators Matrix Set.Notation Module

namespace Matroid

/-- Compose a representation `v` with a linear map that is injective on the range of `v`-/
def Rep.comp (v : M.Rep 𝔽 W) (ψ : W →ₗ[𝔽] W')
    (h_inj : Disjoint (span 𝔽 (range v)) (LinearMap.ker ψ)) : M.Rep 𝔽 W' where
  to_fun := ψ ∘ v
  indep_iff' := fun I ↦ by
    rw [LinearMap.linearIndepOn_iff_of_injOn, v.indep_iff]
    exact LinearMap.injOn_of_disjoint_ker (span_mono <| image_subset_range ..) h_inj

/-! ### Maps between representations -/

/-- Compose a representation with a linear injection. -/
def Rep.comp' (v : M.Rep 𝔽 W) (ψ : W →ₗ[𝔽] W') (hψ : LinearMap.ker ψ = ⊥) := v.comp ψ (by simp [hψ])

/-- Compose a representation with a linear equivalence. -/
def Rep.compEquiv (v : M.Rep 𝔽 W) (ψ : W ≃ₗ[𝔽] W') : M.Rep 𝔽 W' := v.comp' ψ ψ.ker

@[simp] lemma Rep.comp_apply (v : M.Rep 𝔽 W) (ψ : W →ₗ[𝔽] W') (h_inj) (e : α) :
    (v.comp ψ h_inj) e = ψ (v e) := rfl

@[simp] lemma Rep.comp_coeFun (v : M.Rep 𝔽 W) (ψ : W →ₗ[𝔽] W') (h_inj) :
    (v.comp ψ h_inj) = ψ ∘ v := rfl

@[simp] lemma Rep.comp'_apply (v : M.Rep 𝔽 W) (ψ : W →ₗ[𝔽] W') (hψ : LinearMap.ker ψ = ⊥) (e : α) :
    (v.comp' ψ hψ) e = ψ (v e) := rfl

@[simp] lemma Rep.comp'_coeFun (v : M.Rep 𝔽 W) (ψ : W →ₗ[𝔽] W') (h_inj) :
    (v.comp' ψ h_inj) = ψ ∘ v := rfl

@[simp] lemma Rep.compEquiv_apply (v : M.Rep 𝔽 W) (ψ : W ≃ₗ[𝔽] W') (e : α) :
    (v.compEquiv ψ) e = ψ (v e) := rfl

@[simp] lemma Rep.compEquiv_coeFun (v : M.Rep 𝔽 W) (ψ : W ≃ₗ[𝔽] W') :
    v.compEquiv ψ = ψ ∘ v := rfl

@[simp] lemma Rep.compEquiv_compEquiv_symm (v : M.Rep 𝔽 W) (ψ : W ≃ₗ[𝔽] W') :
    (v.compEquiv ψ).compEquiv ψ.symm = v := by
  ext
  simp

@[simp] lemma Rep.compEquiv_symm_compEquiv (v : M.Rep 𝔽 W') (ψ : W ≃ₗ[𝔽] W') :
    (v.compEquiv ψ.symm).compEquiv ψ = v := by
  ext
  simp

/--  Compose a representation with a module equality -/
def Rep.subtype_ofEq {W₁ W₂ : Submodule 𝔽 W} (v : M.Rep 𝔽 W₁) (h : W₁ = W₂) : M.Rep 𝔽 W₂ :=
  v.compEquiv <| LinearEquiv.ofEq _ _ h

@[simp] lemma Rep.subtype_ofEq_apply {W₁ W₂ : Submodule 𝔽 W} (v : M.Rep 𝔽 W₁) (h : W₁ = W₂)
    (e : α) : v.subtype_ofEq h e = LinearEquiv.ofEq _ _ h (v e) := rfl

@[simps!] noncomputable def Rep.finsuppToFun (v : M.Rep 𝔽 (β →₀ 𝔽)) : M.Rep 𝔽 (β → 𝔽) :=
  v.comp' Finsupp.lcoeFun (by simp)

/-- A representation gives a representation of a comap -/
@[simps] def Rep.comap {M : Matroid β} (v : M.Rep 𝔽 W) (f : α → β) : (M.comap f).Rep 𝔽 W where
  to_fun := v ∘ f
  indep_iff' I := by
    simp only [comap_indep_iff, v.indep_iff]
    exact ⟨fun h ↦ h.1.comp_of_image h.2, fun h ↦ ⟨h.image_of_comp, h.injOn.of_comp⟩⟩

lemma Rep.comap_coeFun_eq {M : Matroid β} (f : α → β) (v : M.Rep 𝔽 W) :
    (v.comap f : α → W) = v ∘ f := rfl

@[simp] lemma Rep.comap_apply {M : Matroid β} (f : α → β) (v : M.Rep 𝔽 W) (a : α) :
    v.comap f a = v (f a) := rfl

@[simps] def Rep.ofEq {M N : Matroid α} (v : M.Rep 𝔽 W) (h : M = N) : N.Rep 𝔽 W where
  to_fun := v
  indep_iff' := by simp [← v.indep_iff, h]

@[simp] lemma Rep.ofEq_apply {M N : Matroid α} (v : M.Rep 𝔽 W) (h : M = N) :
  (v.ofEq h : α → W) = v := rfl

noncomputable def Rep.restrictSubtype (v : M.Rep 𝔽 W) (X : Set α) : (M.restrictSubtype X).Rep 𝔽 W :=
  (v.restrict X).comap ((↑) : X → α)

/-- Transfer a `Rep` along a matroid map. The definition involves extending a function with zero,
so requires a `DecidablePred` assumption. -/
noncomputable def Rep.map (v : M.Rep 𝔽 W) (f : α → β) (hf : M.E.InjOn f)
    [DecidablePred (∃ y ∈ M.E, f y = ·)] : (M.map f hf).Rep 𝔽 W :=
  let v' := fun (x : β) ↦ if h : ∃ y ∈ M.E, f y = x then v h.choose else 0
  have h_eq : EqOn (v' ∘ f) v M.E := by
    intro x hx
    have h : ∃ y ∈ M.E, f y = f x := ⟨x, hx, rfl⟩
    simp [v', dif_pos h, show h.choose = x from hf h.choose_spec.1 hx h.choose_spec.2]
  Rep.ofGround
  ( v := v')
  ( h_support := fun x ↦ by
      simp only [mem_support, map_ground, v']
      split_ifs with h
      · exact fun hne ↦ ⟨_, v.support_subset_ground hne, h.choose_spec.2 ⟩
      simp )
  ( h_indep := by
      simp only [map_ground, map_indep_iff, forall_subset_image_iff]
      refine fun I hIE ↦ ⟨fun ⟨I', hI', hII'⟩ ↦ ?_, fun h ↦ ⟨_, ?_, rfl⟩⟩
      · rw [hII']
        exact ((v.onIndep hI').congr <| h_eq.symm.mono hI'.subset_ground).image_of_comp
      exact v.indep_iff.2 <| (h.comp_of_image (hf.mono hIE)).congr (h_eq.mono hIE) )

lemma Rep.matroidMap_apply (v : M.Rep 𝔽 W) {f : α → β} {hf} [DecidablePred (∃ y ∈ M.E, f y = ·)]
    {x : α} (hx : x ∈ M.E) : v.map f hf (f x) = v x := by
  have h : ∃ y ∈ M.E, f y = f x := ⟨x, hx, rfl⟩
  simp [map, dif_pos h, show h.choose = x from hf h.choose_spec.1 hx h.choose_spec.2]

lemma Rep.matroidMap_image (v : M.Rep 𝔽 W) (f : α → β) (hf) [DecidablePred (∃ y ∈ M.E, f y = ·)]
    (hX : X ⊆ M.E) : v.map f hf '' (f '' X) = v '' X := by
  ext x
  simp only [mem_image, exists_exists_and_eq_and]
  constructor <;>
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, by rw [v.matroidMap_apply (hX ha)]⟩

/-- Scale a representation by an invertible scalar for each element of `α`. -/
@[simps] def Rep.scale (v : M.Rep 𝔽 W) (c : α → 𝔽ˣ) : M.Rep 𝔽 W where
  to_fun := c • v
  indep_iff' I := by
    rw [v.indep_iff]
    exact (LinearIndependent.units_smul_iff ..).symm

/-- The `𝔽`-representable matroid whose ground set is a vector space `W` over `𝔽`,
and independence is linear independence.  -/
protected def _root_.Module.matroid (𝔽 W : Type*) [AddCommGroup W] [DivisionRing 𝔽] [Module 𝔽 W] :
    Matroid W :=
  IndepMatroid.matroid <| IndepMatroid.ofFinitaryCardAugment
  (E := univ)
  (Indep := fun I ↦ LinearIndepOn 𝔽 id I)
  (indep_empty := linearIndependent_empty _ _)
  (indep_subset := fun I J hJ hIJ ↦ hJ.mono hIJ)
  (indep_aug := by
    intro I J hI hIfin hJ hJfin hIJ
    have hssu : ¬ (J ⊆ span 𝔽 I) := by
      rw [← span_le]
      refine fun hss ↦ hIJ.not_ge ?_
      have _ := hIfin.fintype
      have _ := hJfin.fintype
      have _ : Module.Finite 𝔽 (span 𝔽 I) := FiniteDimensional.span_of_finite _ hIfin
      rw [ncard_eq_toFinset_card' J, ncard_eq_toFinset_card' I, ← finrank_span_set_eq_card hJ,
        ← finrank_span_set_eq_card hI]
      exact Submodule.finrank_mono hss
    obtain ⟨a, haJ, ha⟩ := not_subset.1 hssu
    refine ⟨a, haJ, notMem_subset subset_span ha, ?_⟩
    simp only [SetLike.mem_coe] at ha
    simpa [linearIndepOn_insert (notMem_subset subset_span ha), ha])
  (indep_compact := linearIndepOn_of_finite)
  (subset_ground := by simp)

@[simps!]
protected def _root_.Module.matroidRep (𝔽 W : Type*) [AddCommGroup W] [DivisionRing 𝔽]
    [Module 𝔽 W] : (Module.matroid 𝔽 W).Rep 𝔽 W where
  to_fun := id
  indep_iff' _ := by rfl

@[simp]
protected lemma _root_.Module.matroid_subsingleton (𝔽 W : Type*) [AddCommGroup W] [DivisionRing 𝔽]
    [Module 𝔽 W] [Subsingleton W] : Module.matroid 𝔽 W = loopyOn {0} := by
  simp [eq_loopyOn_iff, Module.matroid, Set.ext_iff, Subsingleton.eq_zero]

instance _root_.Module.matroid_finitary : Finitary (Module.matroid 𝔽 W) := by
  rw [Module.matroid]
  infer_instance

lemma Rep.eq_comap (v : M.Rep 𝔽 W) : M = (_root_.Module.matroid 𝔽 W).comapOn M.E v := by
  refine ext_indep rfl fun I hI ↦ ?_
  simp only [v.indep_iff, Module.matroid, comapOn_indep_iff, IndepMatroid.matroid_Indep,
    IndepMatroid.ofFinitaryCardAugment_indep, hI, and_true]
  rw [LinearIndepOn_iff_linearIndepOn_image_injOn]

lemma Rep.finitary (v : M.Rep 𝔽 W) : M.Finitary := by
  rw [v.eq_comap]
  exact comapOn_finitary

/-! ### Representations from functions -/

/-- The `𝔽`-representable matroid given by a function `f : α → W` for a vector space `W` over `𝔽`,
and a ground set `E : Set α`.  -/
protected def ofFun (𝔽 : Type*) [DivisionRing 𝔽] [Module 𝔽 W] (E : Set α) (f : α → W) : Matroid α :=
  (Module.matroid 𝔽 W).comapOn E f

lemma ofFun_congr {v v' : α → W} (hvv' : EqOn v v' E) :
    Matroid.ofFun 𝔽 E v = Matroid.ofFun 𝔽 E v' := by
  refine ext_indep rfl fun I (hI : I ⊆ E) ↦ ?_
  simp [Matroid.ofFun, (hvv'.mono hI).image_eq, (hvv'.mono hI).injOn_iff]

@[simp] lemma ofFun_indicator {v : α → W} :
    Matroid.ofFun 𝔽 E (E.indicator v) = Matroid.ofFun 𝔽 E v :=
  ofFun_congr <| eqOn_indicator

noncomputable def repOfFun (𝔽 : Type*) [DivisionRing 𝔽] [Module 𝔽 W] (E : Set α) (f : α → W) :
    (Matroid.ofFun 𝔽 E f).Rep 𝔽 W :=
  ((Module.matroidRep 𝔽 W).comap f).restrict E

lemma repOfFun_coeFun_eq (𝔽 : Type*) [DivisionRing 𝔽] [Module 𝔽 W] (E : Set α) (f : α → W) :
    (repOfFun 𝔽 E f : α → W) = indicator E f := rfl

lemma repOfFun_coeFun_eq' (𝔽 : Type*) [DivisionRing 𝔽] [Module 𝔽 W] (E : Set α) (f : α → W)
    (hf : support f ⊆ E) : (repOfFun 𝔽 E f : α → W) = f := by
  rwa [repOfFun_coeFun_eq, indicator_eq_self]

@[simp] lemma repOfFun_image_eq (𝔽 : Type*) [DivisionRing 𝔽] [Module 𝔽 W] (E : Set α) (f : α → W) :
    (repOfFun 𝔽 E f '' E) = f '' E := by
  rw [repOfFun_coeFun_eq]
  aesop

lemma repOfFun_apply (𝔽 : Type*) [DivisionRing 𝔽] [Module 𝔽 W] {v : α → W} (he : e ∈ E) :
    (repOfFun 𝔽 E v) e = v e := by
  change indicator E v e = v e
  simp [he]

instance matroidOfFun_finitary (𝔽 : Type*) [DivisionRing 𝔽] [Module 𝔽 W] (f : α → W) (E : Set α) :
    Finitary (Matroid.ofFun 𝔽 E f) := by
  rw [Matroid.ofFun, comapOn]
  infer_instance

lemma ofFun_finite (f : α → W) (E : Set α) (hfin : E.Finite) : (Matroid.ofFun 𝔽 E f).Finite :=
  ⟨hfin⟩

@[simp] lemma ofFun_ground_eq {v : α → W} {E : Set α} : (Matroid.ofFun 𝔽 E v).E = E := rfl

@[simp] lemma ofFun_indep_iff {v : α → W} {E : Set α} :
    (Matroid.ofFun 𝔽 E v).Indep I ↔ LinearIndepOn 𝔽 v I ∧ I ⊆ E := by
  rw [Matroid.ofFun, comapOn_indep_iff]
  by_cases hinj : InjOn v I
  · simp only [Module.matroid, IndepMatroid.matroid_Indep, and_iff_right hinj,
    IndepMatroid.ofFinitaryCardAugment_indep, ← linearIndepOn_iff_image hinj]
  exact iff_of_false (by simp [hinj]) fun hli ↦ hinj <| injOn_iff_injective.2 hli.1.injective

@[simp] lemma Rep.ofFun_self (v : M.Rep 𝔽 W) : Matroid.ofFun 𝔽 M.E v = M :=
  ext_indep rfl fun I (hIE : I ⊆ M.E) ↦ by rw [ofFun_indep_iff, ← v.indep_iff, and_iff_left hIE]

lemma ofFun_closure_eq {v : α → W} {E : Set α} (hvE : support v ⊆ E) :
    (Matroid.ofFun 𝔽 E v).closure X = v ⁻¹' (span 𝔽 (v '' X)) ∩ E := by
  rw [(repOfFun 𝔽 E v).closure_eq, repOfFun_coeFun_eq, ofFun_ground_eq, indicator_preimage]
  simp +contextual [indicator_eq_self.2 hvE]

lemma ofFun_closure_eq_of_subset_ground {v : α → W} {E : Set α} (hXE : X ⊆ E) :
    (Matroid.ofFun 𝔽 E v).closure X = v ⁻¹' (span 𝔽 (v '' X)) ∩ E := by
  rw [← ofFun_indicator, ofFun_closure_eq (by simp), indicator_preimage,
    ((Set.eqOn_indicator (f := v)).mono hXE).image_eq]
  simp

lemma _root_.Module.Basis.ofFun_isBase {v : α → W} {E : Set α} {B : Set α} (b : Module.Basis B 𝔽 W)
    (hfb : ∀ x : B, v x = b x) (hBE : B ⊆ E) : (Matroid.ofFun 𝔽 E v).IsBase B := by
  have hrw : v '' B = range b := by simp_rw [Set.ext_iff, mem_range, ← hfb]; aesop

  refine Indep.isBase_of_ground_subset_closure ?_ ?_
  · simp only [ofFun_indep_iff, LinearIndepOn, hfb, and_iff_left hBE]
    exact b.linearIndependent
  rw [ofFun_closure_eq_of_subset_ground hBE, hrw, b.span_eq]
  simp

@[simp] lemma ofFun_zero (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W] (E : Set α) :
    (Matroid.ofFun 𝔽 E (0 : α → W)) = loopyOn E := by
  simp +contextual [eq_loopyOn_iff]
