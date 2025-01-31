
import Matroid.Representation.Basic

variable {α β W W' 𝔽 R : Type*} {e f x : α} {I E B X Y : Set α} {M : Matroid α} [DivisionRing 𝔽]
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W']

open Function Set Submodule FiniteDimensional BigOperators Matrix Set.Notation

namespace Matroid

/-! ### Constructors -/

/-- A function with support contained in `M.E` that gives the correct independent sets
  within the ground set gives a representation -/
@[simps] def Rep.ofGround (f : α → W) (h_support : support f ⊆ M.E)
    (hf : ∀ I ⊆ M.E, (M.Indep I ↔ LinearIndependent 𝔽 (I.restrict f))) : M.Rep 𝔽 W where
  to_fun := f
  valid' := ( by
    intro I
    by_cases hI : I ⊆ M.E
    · rw [hf _ hI]
    rw [← not_iff_not, iff_true_left (fun hi ↦ hI hi.subset_ground)]
    intro h_ind
    obtain ⟨e, heI, heE⟩ := not_subset.1 hI
    have h0 := h_ind.ne_zero ⟨e, heI⟩
    simp only [Function.comp_apply, ne_eq] at h0
    apply not_mem_subset h_support heE
    exact h0 )

@[simp] lemma Rep.ofGround_apply (f : α → W) (hs : support f ⊆ M.E)
  (hf : ∀ I ⊆ M.E, (M.Indep I ↔ LinearIndependent 𝔽 (I.restrict f))) (a : α) :
    Rep.ofGround f hs hf a = f a := rfl

/-- A function from `M.E` to a module determines a representation -/
@[simps!] noncomputable def Rep.ofSubtypeFun (f : M.E → W) [DecidablePred (· ∈ M.E)]
    (hf : ∀ (I : Set M.E), M.Indep (Subtype.val '' I) ↔ LinearIndependent 𝔽 (I.restrict f)) :
    M.Rep 𝔽 W :=
  Rep.ofGround
  ( fun a ↦ if ha : a ∈ M.E then f ⟨a,ha⟩ else 0 )
  ( by aesop )
  ( by
    intro I hI
    rw [← Subtype.range_val (s := M.E), subset_range_iff_exists_image_eq] at hI
    obtain ⟨I, rfl⟩ := hI
    rw [hf]
    apply linearIndependent_equiv' <| Equiv.Set.image _ _ Subtype.val_injective
    ext ⟨⟨x,hx⟩, hx'⟩
    simp [dif_pos hx] )

-- @[simp] lemma Rep.offSubtypeFun_apply (f : M.E → W) [DecidablePred (· ∈ M.E)]
--     (hf : ∀ {I : Set M.E}, M.Indep (Subtype.val '' I) ↔ LinearIndependent 𝔽 (I.restrict f))
--     (e : M.E) : Rep.ofSubtypeFun f hf e = f e := by
--   simp [repOfSubtypeFun, rep_of_ground]

-- lemma repOfSubtypeFun_apply_mem (f : M.E → W) [DecidablePred (· ∈ M.E)]
--     (hf : ∀ {I : Set M.E}, M.Indep (Subtype.val '' I) ↔ LinearIndependent 𝔽 (I.restrict f))
--     {e : α} (he : e ∈ M.E) : repOfSubtypeFun f hf e = f ⟨e,he⟩ := by
--   simp [repOfSubtypeFun, rep_of_ground, dif_pos he]

-- lemma repOfSubtypeFun_apply_not_mem (f : M.E → W) [DecidablePred (· ∈ M.E)]
--     (hf : ∀ {I : Set M.E}, M.Indep (Subtype.val '' I) ↔ LinearIndependent 𝔽 (I.restrict f))
--     {e : α} (he : e ∉ M.E) : repOfSubtypeFun f hf e = 0 := by
--   simp [repOfSubtypeFun, rep_of_ground, dif_neg he]

-- lemma rep_of_ground_coe_eq (f : α → W) (h_support : support f ⊆ M.E)
--   (hf : ∀ {I}, I ⊆ M.E → (M.Indep I ↔ LinearIndependent 𝔽 (f ∘ ((↑) : I → α)))) :
--   (rep_of_ground f h_support hf : α → W) = f := rfl

/-- Compose a representation `v` with a linear map that is injective on the range of `v`-/
def Rep.map (v : M.Rep 𝔽 W) (ψ : W →ₗ[𝔽] W')
    (h_inj : Disjoint (span 𝔽 (range v)) (LinearMap.ker ψ)) : M.Rep 𝔽 W' where
  to_fun := ψ ∘ v
  valid' := fun I ↦ by
    rw [v.indep_iff, restrict_eq, restrict_eq, comp_assoc]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · apply h.map (h_inj.mono_left (span_mono _))
      rw [Set.range_comp]
      exact image_subset_range _ _
    exact LinearIndependent.of_comp _ h

/-! ### Maps between representations -/

/-- Compose a representation with a linear injection. -/
def Rep.map' (v : M.Rep 𝔽 W) (ψ : W →ₗ[𝔽] W') (hψ : LinearMap.ker ψ = ⊥) := v.map ψ (by simp [hψ])

/-- Compose a representation with a linear equivalence. -/
def Rep.mapEquiv (v : M.Rep 𝔽 W) (ψ : W ≃ₗ[𝔽] W') : M.Rep 𝔽 W' := v.map' ψ ψ.ker

@[simp] lemma Rep.map'_apply (v : M.Rep 𝔽 W) (ψ : W →ₗ[𝔽] W') (hψ : LinearMap.ker ψ = ⊥) (e : α) :
    (v.map' ψ hψ) e = ψ (v e) := rfl

@[simp] lemma Rep.mapEquiv_apply (v : M.Rep 𝔽 W) (ψ : W ≃ₗ[𝔽] W') (e : α) :
    (v.mapEquiv ψ) e = ψ (v e) := rfl

/--  Compose a representation with a module equality -/
def Rep.subtype_ofEq {W₁ W₂ : Submodule 𝔽 W} (v : M.Rep 𝔽 W₁) (h : W₁ = W₂) : M.Rep 𝔽 W₂ :=
  v.mapEquiv <| LinearEquiv.ofEq _ _ h

@[simp] lemma Rep.subtype_ofEq_apply {W₁ W₂ : Submodule 𝔽 W} (v : M.Rep 𝔽 W₁) (h : W₁ = W₂)
    (e : α) : v.subtype_ofEq h e = LinearEquiv.ofEq _ _ h (v e) := rfl

/-- A representation gives a representation of any restriction -/
noncomputable def Rep.restrict (v : M.Rep 𝔽 W) (X : Set α) : (M ↾ X).Rep 𝔽 W :=
  Rep.ofGround (indicator X v) ( by simp )
  ( by
    simp only [restrict_ground_eq, restrict_indep_iff]
    intro I hIX
    rw [v.indep_iff, and_iff_left hIX]
    convert Iff.rfl using 2
    ext ⟨e, he⟩
    simp [hIX he] )

@[simp] lemma Rep.restrict_apply (v : M.Rep 𝔽 W) (X : Set α) :
    (v.restrict X : α → W) = indicator X v := rfl

/-- A representation gives a representation of a comap -/
def Rep.comap {M : Matroid β} (f : α → β) (v : M.Rep 𝔽 W) : (M.comap f).Rep 𝔽 W :=
  Rep.ofGround (v ∘ f)
  ( by
    simp only [comap_ground_eq, support_subset_iff, Function.comp_apply, ne_eq, mem_preimage]
    exact fun x ↦ Not.imp_symm <| Rep.eq_zero_of_not_mem_ground _ )
  ( by
    intro I _
    rw [comap_indep_iff, v.indep_iff, restrict_eq, restrict_eq, comp_assoc]
    refine' ⟨fun ⟨h,hInj⟩ ↦ _, fun h ↦ ⟨LinearIndependent.image_of_comp _ _ _ h, ?_⟩⟩
    · exact h.comp (imageFactorization f I) (hInj.imageFactorization_injective)
    rintro x hx y hy hxy
    have hi := h.injective (a₁ := ⟨x,hx⟩) (a₂ := ⟨y,hy⟩)
    simpa only [Function.comp_apply, Subtype.mk.injEq, hxy, true_imp_iff] using hi )

lemma Rep.comap_coeFun_eq {M : Matroid β} (f : α → β) (v : M.Rep 𝔽 W) :
    (v.comap f : α → W) = v ∘ f := rfl

@[simp] lemma Rep.comap_apply {M : Matroid β} (f : α → β) (v : M.Rep 𝔽 W) (a : α) :
    v.comap f a = v (f a) := rfl

def Rep.ofEq {M N : Matroid α} (v : M.Rep 𝔽 W) (h : M = N) : N.Rep 𝔽 W :=
  Rep.ofGround v
  ( v.support_subset_ground.trans_eq (congr_arg _ h) )
  ( by intro I _; rw [← h, v.indep_iff] )

@[simp] lemma Rep.ofEq_apply {M N : Matroid α} (v : M.Rep 𝔽 W) (h : M = N) :
  (v.ofEq h : α → W) = v := rfl

noncomputable def Rep.restrictSubtype (v : M.Rep 𝔽 W) (X : Set α) : (M.restrictSubtype X).Rep 𝔽 W :=
  (v.restrict X).comap ((↑) : X → α)

/-- Transfer a `Rep` along a matroid map. The definition involves extending a function with zero,
so requires a `DecidablePred` assumption. -/
noncomputable def Rep.matroidMap (v : M.Rep 𝔽 W) (f : α → β) (hf : M.E.InjOn f)
    [DecidablePred (∃ y ∈ M.E, f y = ·)] : (M.map f hf).Rep 𝔽 W :=
  let v' := fun (x : β) ↦ if h : ∃ y ∈ M.E, f y = x then v h.choose else 0
  Rep.ofGround
  (f := v')
  ( h_support := fun x ↦ by
      simp only [mem_support, map_ground, v']
      split_ifs with h
      · exact fun hne ↦ ⟨_, v.support_subset_ground hne, h.choose_spec.2 ⟩
      simp )
  ( hf := by
      have hv' : ∀ x ∈ M.E, v' (f x) = v x := by
        intro x hx
        have h : ∃ y ∈ M.E, f y = f x := ⟨x, hx, rfl⟩
        simp only [v', dif_pos h, show h.choose = x from hf h.choose_spec.1 hx h.choose_spec.2]
      simp only [map_ground, map_indep_iff, forall_subset_image_iff]
      refine fun I hIE ↦ ⟨fun ⟨I', hI', h_eq⟩ ↦ ?_, fun h ↦ ⟨_, ?_, rfl⟩⟩
      · obtain rfl : I = I' := (hf.image_eq_image_iff hIE hI'.subset_ground).1 h_eq
        refine LinearIndependent.image_of_comp (f := f) (s := I) _ ?_
        convert v.indep_iff.1 hI' using 1
        ext ⟨x, hx⟩
        simp [hv' _ (hIE hx)]
      rw [← linearIndependent_equiv <| Equiv.Set.imageOfInjOn _ _ (hf.mono hIE)] at h
      rw [v.indep_iff]
      convert h
      ext ⟨x, hx⟩
      simp [Equiv.Set.imageOfInjOn, hv' _ (hIE hx)])

lemma Rep.matroidMap_apply (v : M.Rep 𝔽 W) {f : α → β} {hf} [DecidablePred (∃ y ∈ M.E, f y = ·)]
    {x : α} (hx : x ∈ M.E) : v.matroidMap f hf (f x) = v x := by
  have h : ∃ y ∈ M.E, f y = f x := ⟨x, hx, rfl⟩
  simp [matroidMap, dif_pos h, show h.choose = x from hf h.choose_spec.1 hx h.choose_spec.2]

lemma Rep.matroidMap_image (v : M.Rep 𝔽 W) (f : α → β) (hf) [DecidablePred (∃ y ∈ M.E, f y = ·)]
    (hX : X ⊆ M.E) : v.matroidMap f hf '' (f '' X) = v '' X := by
  ext x
  simp only [mem_image, exists_exists_and_eq_and]
  constructor <;>
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, by rw [v.matroidMap_apply (hX ha)]⟩

/-- The `𝔽`-representable matroid whose ground set is a vector space `W` over `𝔽`,
and independence is linear independence.  -/
protected def onModule (𝔽 W : Type*) [AddCommGroup W] [DivisionRing 𝔽] [Module 𝔽 W] : Matroid W :=
  IndepMatroid.matroid <| IndepMatroid.ofFinitaryCardAugment
  (E := univ)
  (Indep := fun I ↦ LinearIndependent 𝔽 ((↑) : I → W))
  (indep_empty := linearIndependent_empty _ _)
  (indep_subset := fun I J hJ hIJ ↦ hJ.mono hIJ)
  (indep_aug := by
    intro I J hI hIfin hJ hJfin hIJ
    have hssu : ¬ (J ⊆ span 𝔽 I) := by
      rw [← span_le]
      refine fun hss ↦ hIJ.not_le ?_
      have _ := hIfin.fintype
      have _ := hJfin.fintype
      have _ : Module.Finite 𝔽 (span 𝔽 I) := FiniteDimensional.span_of_finite _ hIfin
      rw [ncard_eq_toFinset_card' J, ncard_eq_toFinset_card' I, ← finrank_span_set_eq_card hJ,
        ← finrank_span_set_eq_card hI]
      exact Submodule.finrank_mono hss
    obtain ⟨a, haJ, ha⟩ := not_subset.1 hssu
    refine ⟨a, haJ, not_mem_subset subset_span ha, ?_⟩
    simp only [SetLike.mem_coe] at ha
    simpa [linearIndependent_insert (not_mem_subset subset_span ha), ha])
  (indep_compact := linearIndependent_of_finite)
  (subset_ground := by simp)

@[simps!] def repOnModule (𝔽 W : Type*) [AddCommGroup W] [DivisionRing 𝔽] [Module 𝔽 W] :
    (Matroid.onModule 𝔽 W).Rep 𝔽 W where
  to_fun := id
  valid' _ := by rfl

/-! ### Representations from functions -/

/-- The `𝔽`-representable matroid given by a function `f : α → W` for a vector space `W` over `𝔽`,
and a ground set `E : Set α`.  -/
protected def ofFun (𝔽 : Type*) [DivisionRing 𝔽] [Module 𝔽 W] (E : Set α) (f : α → W) : Matroid α :=
    (Matroid.onModule 𝔽 W).comapOn E f

noncomputable def repOfFun (𝔽 : Type*) [DivisionRing 𝔽] [Module 𝔽 W] (E : Set α) (f : α → W) :
    (Matroid.ofFun 𝔽 E f).Rep 𝔽 W :=
  ((repOnModule 𝔽 W).comap f).restrict E

@[simp] lemma repOfFun_coeFun_eq (𝔽 : Type*) [DivisionRing 𝔽] [Module 𝔽 W] (E : Set α) (f : α → W) :
    (repOfFun 𝔽 E f : α → W) = indicator E f := rfl

instance matroidOfFun_finitary (𝔽 : Type*) [DivisionRing 𝔽] [Module 𝔽 W] (f : α → W) (E : Set α) :
    Finitary (Matroid.ofFun 𝔽 E f) := by
  rw [Matroid.ofFun, Matroid.onModule, comapOn]; infer_instance

lemma ofFun_finite (f : α → W) (E : Set α) (hfin : E.Finite) : (Matroid.ofFun 𝔽 E f).Finite :=
  ⟨hfin⟩

@[simp] lemma ofFun_ground_eq {f : α → W} {E : Set α} : (Matroid.ofFun 𝔽 E f).E = E := rfl

@[simp] lemma ofFun_indep_iff {f : α → W} {E : Set α} :
    (Matroid.ofFun 𝔽 E f).Indep I ↔ LinearIndependent 𝔽 (I.restrict f) ∧ I ⊆ E := by
  rw [Matroid.ofFun, comapOn_indep_iff]
  by_cases hinj : InjOn f I
  · simp only [Matroid.onModule, IndepMatroid.matroid_Indep, and_iff_right hinj,
    IndepMatroid.ofFinitaryCardAugment_indep, ← linearIndependent_image hinj, and_congr_left_iff]
    exact fun _ ↦ Iff.rfl
  exact iff_of_false (by simp [hinj]) fun hli ↦ hinj <| injOn_iff_injective.2 hli.1.injective

@[simp] lemma Rep.ofFun_self (v : M.Rep 𝔽 W) : Matroid.ofFun 𝔽 M.E v = M :=
  ext_indep rfl fun I (hIE : I ⊆ M.E) ↦ by rw [ofFun_indep_iff, ← v.indep_iff, and_iff_left hIE]

lemma ofFun_congr {v v' : α → W} (hvv' : EqOn v v' E) :
    Matroid.ofFun 𝔽 E v = Matroid.ofFun 𝔽 E v' := by
  refine ext_indep rfl fun I (hI : I ⊆ E) ↦ ?_
  simp only [ofFun_indep_iff, hI, and_true]
  convert Iff.rfl using 2
  ext ⟨e, he⟩
  rw [restrict_apply, restrict_apply, hvv']
  exact hI he

@[simp] lemma ofFun_indicator {v : α → W} :
    Matroid.ofFun 𝔽 E (E.indicator v) = Matroid.ofFun 𝔽 E v :=
  ofFun_congr <| eqOn_indicator

lemma ofFun_closure_eq {v : α → W} {E : Set α} (hvE : support v ⊆ E) :
    (Matroid.ofFun 𝔽 E v).closure X = v ⁻¹' (span 𝔽 (v '' X)) ∩ E := by
  rw [(repOfFun 𝔽 E v).closure_eq, repOfFun_coeFun_eq, ofFun_ground_eq, indicator_preimage]
  simp +contextual [indicator_eq_self.2 hvE]

lemma ofFun_closure_eq_of_subset_ground {v : α → W} {E : Set α} (hXE : X ⊆ E) :
    (Matroid.ofFun 𝔽 E v).closure X = v ⁻¹' (span 𝔽 (v '' X)) ∩ E := by
  rw [← ofFun_indicator, ofFun_closure_eq (by simp), indicator_preimage,
    ((Set.eqOn_indicator (f := v)).mono hXE).image_eq]
  simp

lemma _root_.Basis.ofFun_base {v : α → W} {E : Set α} {B : Set α} (b : _root_.Basis B 𝔽 W)
    (hfb : ∀ x : B, v x = b x) (hBE : B ⊆ E) : (Matroid.ofFun 𝔽 E v).Base B := by
  have hrw : v '' B = range b := by simp_rw [Set.ext_iff, mem_range, ← hfb]; aesop

  refine Indep.base_of_ground_subset_closure ?_ ?_
  · rw [Matroid.ofFun_indep_iff, restrict_eq, and_iff_left hBE]
    convert b.linearIndependent
    ext e
    exact hfb e
  rw [ofFun_closure_eq_of_subset_ground hBE, hrw, b.span_eq]
  simp

@[simp] lemma ofFun_zero (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W] (E : Set α) :
    (Matroid.ofFun 𝔽 E (0 : α → W)) = loopyOn E := by
  simp +contextual [eq_loopyOn_iff]
