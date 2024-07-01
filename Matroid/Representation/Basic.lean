-- import Matroid.Minor.Iso
-- import Matroid.Simple
import Matroid.Constructions.ParallelExtension
-- import Matroid.ForMathlib.Card
import Matroid.ForMathlib.LinearAlgebra.LinearIndependent
import Matroid.ForMathlib.LinearAlgebra.Matrix.Rowspace
-- import Matroid.ForMathlib.Other


variable {α β W W' 𝔽 R : Type*} {e f x : α} {I E B X Y : Set α} {M : Matroid α} [Field 𝔽]
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W']

open Function Set Submodule FiniteDimensional BigOperators Matrix Set.Notation

namespace Matroid

/-- A function `v : α → W` represents `M` over `𝔽` if independence of `I` in `M` corresponds to
linear independence of `v '' I` in `W`. -/
def IsRep (M : Matroid α) (𝔽 : Type*) [CommSemiring 𝔽] [AddCommMonoid W] [Module 𝔽 W] (v : α → W) :=
  ∀ I, M.Indep I ↔ LinearIndependent 𝔽 (I.restrict v)

structure Rep (M : Matroid α) (𝔽 W : Type*) [CommSemiring 𝔽] [AddCommMonoid W] [Module 𝔽 W] where
  -- A representation assigns a vector to each element of `α`
  (to_fun : α → W)
  -- A set is independent in `M` if and only if its image is linearly independent over `𝔽` in `W`
  (valid' : M.IsRep 𝔽 to_fun)

instance : FunLike (M.Rep 𝔽 W) α W where
  coe v := v.to_fun
  coe_injective' := by rintro ⟨f,h⟩ ⟨f', h'⟩; simp

-- instance : DFunLike (M.Rep 𝔽 W) α (fun _ ↦ W) where
--   coe v := v.to_fun
--   coe_injective' := by rintro ⟨f,h⟩ ⟨f', h'⟩; simp

-- instance coeFun : CoeFun (M.Rep 𝔽 W) fun _ ↦ (α → W) :=
--   ⟨DFunLike.coe⟩

@[simp] lemma Rep.to_fun_eq_coe (v : M.Rep 𝔽 W) : v.to_fun = (v : α → W) := rfl

@[simp] lemma Rep.coe_mk (f : α → W) (valid' : M.IsRep 𝔽 f) : (Rep.mk f valid' : α → W) = f := rfl

lemma Rep.isRep (v : M.Rep 𝔽 W) : M.IsRep 𝔽 v := v.valid'

lemma Rep.indep_iff (v : M.Rep 𝔽 W) : M.Indep I ↔ LinearIndependent 𝔽 (I.restrict v) :=
  v.valid' I

lemma Rep.onIndep (v : M.Rep 𝔽 W) (hI : M.Indep I) : LinearIndependent 𝔽 (I.restrict v) :=
  v.indep_iff.1 hI

lemma Rep.injOn_of_indep (v : M.Rep 𝔽 W) (hI : M.Indep I) : InjOn v I :=
  injOn_iff_injective.2 ((v.onIndep hI).injective)

lemma Rep.indep_image (v : M.Rep 𝔽 W) (hI : M.Indep I) : LinearIndependent 𝔽 (v '' I).incl := by
  rw [← linearIndependent_image <| v.injOn_of_indep hI]
  exact v.onIndep hI

lemma Rep.indep_iff_image_of_inj (v : M.Rep 𝔽 W) (h_inj : InjOn v I) :
    M.Indep I ↔ LinearIndependent 𝔽 (v '' I).incl := by
  refine ⟨v.indep_image, fun hi ↦ ?_⟩
  rw [v.indep_iff, restrict_eq]
  exact (linearIndependent_image h_inj (R := 𝔽)).2 hi

lemma Rep.indep_iff_image (v : M.Rep 𝔽 W) :
    M.Indep I ↔ LinearIndependent 𝔽 (v '' I).incl ∧ InjOn v I :=
  ⟨fun h ↦ ⟨v.indep_image h, v.injOn_of_indep h⟩,
    fun h ↦ (v.indep_iff_image_of_inj h.2).2 h.1⟩

lemma Rep.eq_zero_iff_not_indep {v : M.Rep 𝔽 W} : v e = 0 ↔ ¬ M.Indep {e} := by
  simp [v.indep_iff, linearIndependent_unique_iff, -indep_singleton]

lemma Rep.eq_zero_of_not_mem_ground (v : M.Rep 𝔽 W) (he : e ∉ M.E) : v e = 0 := by
  rw [v.eq_zero_iff_not_indep, indep_singleton]
  exact fun hl ↦ he hl.mem_ground

lemma Rep.support_subset_ground (v : M.Rep 𝔽 W) : support v ⊆ M.E :=
  fun _ he ↦ by_contra <| fun h' ↦ he (v.eq_zero_of_not_mem_ground h')

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
    rw [v.indep_iff, restrict_eq, restrict_eq, comp.assoc]
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · apply h.map (h_inj.mono_left (span_mono _))
      rw [Set.range_comp]
      exact image_subset_range _ _
    exact LinearIndependent.of_comp _ h

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

/-- A representation gives a representation of a preimage -/
def Rep.comap {M : Matroid β} (f : α → β) (v : M.Rep 𝔽 W) : (M.comap f).Rep 𝔽 W :=
  Rep.ofGround (v ∘ f)
  ( by
    simp only [comap_ground_eq, support_subset_iff, comp_apply, ne_eq, mem_preimage]
    exact fun x ↦ Not.imp_symm <| Rep.eq_zero_of_not_mem_ground _ )
  ( by
    intro I _
    rw [comap_indep_iff, v.indep_iff, restrict_eq, restrict_eq, comp.assoc]
    refine' ⟨fun ⟨h,hInj⟩ ↦ _, fun h ↦ ⟨LinearIndependent.image_of_comp _ _ _ h, ?_⟩⟩
    · exact h.comp (imageFactorization f I) (hInj.imageFactorization_injective)
    rintro x hx y hy hxy
    have hi := h.injective (a₁ := ⟨x,hx⟩) (a₂ := ⟨y,hy⟩)
    simpa only [comp_apply, Subtype.mk.injEq, hxy, true_imp_iff] using hi )

lemma Rep.comap_coeFun_eq {M : Matroid β} (f : α → β) (v : M.Rep 𝔽 W) :
    (v.comap f : α → W) = v ∘ f := rfl

@[simp] lemma Rep.comap_apply {M : Matroid β} (f : α → β) (v : M.Rep 𝔽 W) (a : α) :
    v.comap f a = v (f a) := rfl


-- /- this proof is a mess. -/
-- lemma Rep.matroidOfFun_restrict_eq_onGround (v : M.Rep 𝔽 W) :
--     matroidOfFun 𝔽 (M.E.restrict v) univ = M.onGround M.E := by
--   rw [eq_iff_indep_iff_indep_forall, matroidOfFun_ground, onGround_ground Subset.rfl,
--     and_iff_right rfl, onGround]
--   simp only [subset_univ, preimage_indep_iff, forall_true_left, matroidOfFun_indep_iff,
--     v.indep_iff, and_iff_left (Subtype.val_injective.injOn _)]
--   refine fun I ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
--   · refine (linearIndependent_image ?_).2 ?_
--     · rintro _ ⟨a, ha, rfl⟩ _ ⟨b,hb,rfl⟩ hab
--       have := (h.injective.eq_iff (a := ⟨a, ha⟩) (b := ⟨b, hb⟩)).1 hab
--       simp only [Subtype.mk.injEq] at this
--       rw [this]
--     convert h.image <;> simp [restrict_eq, ← image_comp]
--   refine (linearIndependent_image ?_).2 ?_
--   · rw [restrict_eq]
--     rintro ⟨a,ha⟩ ha' ⟨b,hb⟩ hb' (hab : v a = v b)
--     have := (h.injective.eq_iff (a := ⟨a, by aesop⟩) (b := ⟨b,by aesop⟩)).1 hab
--     simp only [Subtype.mk.injEq] at this
--     simpa only [Subtype.mk.injEq]
--   convert h.image <;> simp [restrict_eq, ← image_comp]

def Rep.ofEq {M N : Matroid α} (v : M.Rep 𝔽 W) (h : M = N) : N.Rep 𝔽 W :=
  Rep.ofGround v
  ( v.support_subset_ground.trans_eq (congr_arg _ h) )
  ( by intro I _; rw [← h, v.indep_iff] )

@[simp] lemma Rep.ofEq_apply {M N : Matroid α} (v : M.Rep 𝔽 W) (h : M = N) :
  (v.ofEq h : α → W) = v := rfl

noncomputable def Rep.restrictSubtype (v : M.Rep 𝔽 W) (X : Set α) : (M.restrictSubtype X).Rep 𝔽 W :=
  (v.restrict X).comap (incl X)

noncomputable def Rep.matroidMap (v : M.Rep 𝔽 W) (f : α → β) (hf : M.E.InjOn f)
    [DecidablePred (∃ y, f y = ·)] :
    (M.map f hf).Rep 𝔽 W := by
  set v' := fun (x : β) ↦ if h : ∃ y, f y = x then v h.choose else 0 with hv'
  refine Rep.ofGround v' (fun x ↦ ?_) ?_
  · simp only [mem_support, map_ground, hv']
    split_ifs with h
    · exact fun hne ↦ ⟨_, v.support_subset_ground hne, h.choose_spec⟩
    simp
  simp only [map_ground, map_indep_iff, forall_subset_image_iff]
  refine fun I hIE ↦ ⟨fun ⟨I', hI', h_eq⟩ ↦ ?_, fun h ↦ ?_⟩
  · obtain rfl : I = I' := (hf.image_eq_image_iff hIE hI'.subset_ground).1 h_eq

    refine LinearIndependent.image_of_comp (f := f) (s := I) _ ?_

    convert v.indep_iff.1 hI' using 1
    ext ⟨x, hx⟩
    simp [hv']
    have := v.injOn_of_indep hI'




    -- simp only [map_ground, support_subset_iff, ne_eq, dite_eq_right_iff, forall_exists_index,
    --   not_forall, mem_image]
    -- rintro _ a rfl hne
    -- have := h.

  --   where
  -- to_fun x := if h : ∃ y, f y = x then v h.choose else 0
  -- valid' := by
  --   simp [IsRep]

/-- The `𝔽`-representable matroid whose ground set is a vector space `W` over `𝔽`,
and independence is linear independence.  -/
protected def onModule (𝔽 W : Type*) [AddCommGroup W] [Field 𝔽] [Module 𝔽 W] : Matroid W :=
  IndepMatroid.matroid <| IndepMatroid.ofFinitary
  (E := univ)
  (Indep := fun (I : Set W) ↦ LinearIndependent 𝔽 ((↑) : I → W))
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
      exact finrank_le_finrank_of_le hss
    obtain ⟨a, haJ, ha⟩ := not_subset.1 hssu
    refine ⟨a, haJ, not_mem_subset subset_span ha, ?_⟩
    simp only [SetLike.mem_coe] at ha
    simpa [linearIndependent_insert (not_mem_subset subset_span ha), ha])
  (indep_compact := fun I hI ↦ linearIndependent_of_finite_index _ fun t ht ↦ by
      simpa [← linearIndependent_image Subtype.val_injective.injOn] using
        hI ((↑) '' t) (by simp) (ht.image _) )
  (subset_ground := by simp)

@[simps!] def repOnModule (𝔽 W : Type*) [AddCommGroup W] [Field 𝔽] [Module 𝔽 W] :
    (Matroid.onModule 𝔽 W).Rep 𝔽 W where
  to_fun := id
  valid' _ := by rfl

/-- The `𝔽`-representable matroid given by a function `f : α → W` for a vector space `W` over `𝔽`,
and a ground set `E : Set α`.  -/
protected def ofFun (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W] (E : Set α) (f : α → W) :=
    (Matroid.onModule 𝔽 W).comapOn E f

@[simp] lemma ofFun_ground_eq {f : α → W} {E : Set α} : (Matroid.ofFun 𝔽 E f).E = E := rfl

@[simp] lemma ofFun_indep_iff {f : α → W} {E : Set α} :
    (Matroid.ofFun 𝔽 E f).Indep I ↔ LinearIndependent 𝔽 (I.restrict f) ∧ I ⊆ E := by
  rw [Matroid.ofFun, comapOn_indep_iff]
  by_cases hinj : InjOn f I
  · simp only [Matroid.onModule, comapOn_indep_iff, IndepMatroid.matroid_Indep,
      IndepMatroid.ofFinitary_indep, ← linearIndependent_image hinj, and_iff_right hinj]; rfl
  exact iff_of_false (by simp [hinj]) fun hli ↦ hinj <| injOn_iff_injective.2 hli.1.injective

noncomputable def repOfFun (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W] (E : Set α) (f : α → W) :
    (Matroid.ofFun 𝔽 E f).Rep 𝔽 W :=
  ((repOnModule 𝔽 W).comap f).restrict E

@[simp] lemma repOfFun_coeFun_eq (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W] (E : Set α) (f : α → W) :
    (repOfFun 𝔽 E f : α → W) = indicator E f := rfl

instance matroidOfFun_finitary (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W] (f : α → W) (E : Set α) :
    Finitary (Matroid.ofFun 𝔽 E f) := by
  rw [Matroid.ofFun, Matroid.onModule, comapOn]; infer_instance

lemma ofFun_finite (f : α → W) (E : Set α) (hfin : E.Finite) : (Matroid.ofFun 𝔽 E f).Finite :=
  ⟨hfin⟩

@[simp] lemma ofFun_zero (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W] (E : Set α) :
    (Matroid.ofFun 𝔽 E (0 : α → W)) = loopyOn E := by
  simp only [eq_loopyOn_iff, ofFun_ground_eq, ofFun_indep_iff, and_imp, true_and]
  rintro X _ hXi -
  rw [show X.restrict 0 = 0 by rfl] at hXi
  simpa using hXi



-- -- def Rep.onGround' (v : M.Rep 𝔽 W) (E : Set α) : (M.onGround E).Rep 𝔽 W := v.preimage (incl E)

-- -- /- Carry a representation across a matroid isomorphism -/
-- -- noncomputable def Rep.iso {M : Matroid α} {N : Matroid β} (v : M.Rep 𝔽 W) (i : Iso M N) :
-- --     N.Rep 𝔽 W :=
-- --   ((v.comap i.symm).restrict N.E).ofEq i.symm.eq_comap.symm

-- -- lemma Rep.iso_apply {M : Matroid α} {N : Matroid β} (v : M.Rep 𝔽 W) (i : Iso M N) {x : β}
-- --     (hx : x ∈ N.E) : v.iso i x = v (i.symm x) := by
-- --   simp [iso, indicator_of_mem hx]



-- -- /-- The `Matroid` whose independent sets are the sets with linearly independent image-/
-- -- @[simps!] protected def onUnivOfFun (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W] (v : α → W) : Matroid α :=



-- -- -- @[simp] lemma matroidOnUnivOfFun_apply (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W] (f : α → W)
-- -- --   (I : Set α) :
-- -- --    (matroidOnUnivOfFun 𝔽 f).Indep I ↔ LinearIndependent 𝔽 (I.restrict f) :=
-- -- --    by simp [matroidOnUnivOfFun, indepMatroidOnUnivOfFun]

-- -- -- @[simp] lemma matroidOnUnivOfFun_ground (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W] (f : α → W) :
-- -- --   (matroidOnUnivOfFun 𝔽 f).E = univ := rfl

-- instance matroidOnUnivOfFun_finitary (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W] (f : α → W) :
--     Finitary (matroidOnUnivOfFun 𝔽 f) := by
--   rw [matroidOnUnivOfFun, indepMatroidOnUnivOfFun]; infer_instance

-- -- @[simps!] protected def ofFun (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W] (f : α → W) (E : Set α) :=
-- --   (Matroid.onUnivOfFun 𝔽 f) ↾ E

-- lemma matroidOfFun_indep_iff (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W] (f : α → W)
--     (E : Set α) (hf : support f ⊆ E) (I : Set α) :
--     (Matroid.ofFun 𝔽 f E).Indep I ↔ LinearIndependent 𝔽 (I.restrict f) := by
--   simp only [ofFun_Indep, and_iff_left_iff_imp]
--   exact fun hli ↦ subset_trans (fun x hxI ↦ by exact hli.ne_zero ⟨x, hxI⟩) hf

-- instance matroidOfFun_finitary (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W] (f : α → W) (E : Set α) :
--     Finitary (Matroid.ofFun 𝔽 f E) := by
--   rw [Matroid.ofFun, Matroid.onUnivOfFun]; infer_instance

-- lemma matroidOfFun_finite (f : α → W) (E : Set α) (hfin : E.Finite) :
--     (Matroid.ofFun 𝔽 f E).Finite :=
--   ⟨hfin⟩

-- @[simps!] def Rep.ofFunUniv (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W] (f : α → W) :
--     (Matroid.onUnivOfFun 𝔽 f).Rep 𝔽 W where
--   to_fun := f
--   valid' := by simp [IsRep]

-- @[simp] lemma Rep.ofFunUniv_apply (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W] (f : α → W) (a : α) :
--     (Rep.ofFunUniv 𝔽 f) a = f a := rfl

-- @[simps!] noncomputable def Rep.ofFun (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W] (f : α → W) (E : Set α) :
--     (Matroid.ofFun 𝔽 f E).Rep 𝔽 W := (Rep.ofFunUniv 𝔽 f).restrict E

-- @[simp] lemma Rep.ofFun_apply (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W] (f : α → W) (a : α) :
--     (Rep.ofFun 𝔽 f E) a = indicator E f a := by
--   rfl

-- lemma Rep.ofFun_apply_mem (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W] (f : α → W) {a : α} (ha : a ∈ E) :
--     (Rep.ofFun 𝔽 f E) a = f a := by
--   simp [ha]

-- @[simp] lemma ofFun_indicator_eq (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W] (f : α → W) (E : Set α) :
--     Matroid.ofFun 𝔽 (indicator E f) E = Matroid.ofFun 𝔽 f E := by
--   simp only [eq_iff_indep_iff_indep_forall, ofFun_E, ofFun_Indep, and_congr_left_iff, true_and]
--   intro I hIE _
--   convert Iff.rfl using 2
--   ext ⟨x,hx⟩
--   simp [restrict_apply, indicator_of_mem (hIE hx)]

-- /-- A function from `↑(E : Set α)` to a vector space determines a matroid with ground set `E`. -/
-- protected def ofSubtypeFun (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W] (f : E → W) :
--     Matroid α := Matroid.ofFun 𝔽 (Function.extend Subtype.val f 0) E

-- @[simp] lemma ofSubtypeFun_indep_iff (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W] (f : E → W) (I : Set α) :
--     (Matroid.ofSubtypeFun 𝔽 f).Indep I
--       ↔ ∃ (I₀ : Set E), LinearIndependent 𝔽 (I₀.restrict f) ∧ I = ↑I₀ := by
--   simp only [Matroid.ofSubtypeFun, ofFun_Indep]
--   refine ⟨fun ⟨h,hIE⟩ ↦ ?_, ?_⟩
--   · rw [← Subtype.range_val (s := E), subset_range_iff_exists_image_eq] at hIE
--     obtain ⟨I₀, rfl⟩ := hIE
--     refine ⟨_, ?_, rfl⟩
--     convert h.comp (imageFactorization Subtype.val I₀) _
--     ext x
--     simp only [restrict_apply, comp_apply, Subtype.exists, exists_prop, exists_eq_right,
--       imageFactorization, exists_apply_eq_apply, not_true, Subtype.val_injective.extend_apply]
--     apply Subtype.val_injective.injOn.imageFactorization_injective
--   rintro ⟨I, hI, rfl⟩
--   simp only [image_subset_iff, Subtype.coe_preimage_self, subset_univ, and_true]
--   set  g : (Subtype.val '' I) → I := fun x ↦ ⟨⟨x,
--     ( by obtain ⟨_,⟨x,hx,rfl⟩⟩ := x; simp)⟩, (by obtain ⟨_,⟨x,hx,rfl⟩⟩ := x; simpa )⟩ with hg
--   convert hI.comp g ?_
--   · ext x
--     obtain ⟨_,⟨x,hx,rfl⟩⟩ := x
--     simp [Subtype.val_injective.extend_apply]
--   rintro ⟨_,⟨⟨x,hxE⟩,hx,rfl⟩⟩ ⟨_,⟨⟨y,hyE⟩,hy,rfl⟩⟩ hxy
--   simpa [hg] using hxy

-- @[simp] lemma ofSubtypeFun_ground (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W] (f : E → W) :
--     (Matroid.ofSubtypeFun 𝔽 f).E = E := rfl

-- /-- `f : (E : Set α) → W` gives a representation of the matroid on `α` it constructs-/
-- @[simps!] noncomputable def ofSubtypeFun_rep (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W] (f : E → W) :
--     (Matroid.ofSubtypeFun 𝔽 f).Rep 𝔽 W where
--       to_fun := Subtype.val.extend f 0
--       valid' := (by
--         classical
--         convert (Rep.ofFun 𝔽 (Subtype.val.extend f 0) E).isRep
--         ext a
--         rw [Rep.ofFun_apply, indicator_apply, extend]
--         simp only [Subtype.exists, exists_prop, exists_eq_right, Pi.zero_apply]
--         split_ifs <;> rfl )

-- -- @[simp] lemma matroidOfSubtypeFun_rep_apply {E : Set α} (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W]
-- --     (f : E → W) (e : E) : matroidOfSubtypeFun_rep 𝔽 f e = f e := by
-- --   change Subtype.val.extend f 0 e = f e
-- --   rw [Function.Injective.extend_apply Subtype.val_injective]

lemma Rep.range_subset_span_base (v : M.Rep 𝔽 W) (hB : M.Base B) : range v ⊆ span 𝔽 (v '' B) := by
  rintro _ ⟨e, he ,rfl⟩
  obtain (heB | heB) := em (e ∈ B)
  · exact subset_span (mem_image_of_mem _ heB)
  by_contra h'
  have hind : LinearIndependent 𝔽 ((insert (v e) (v '' B)).incl) :=
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
    refine ⟨fun h ↦ LinearIndependent.of_comp (Submodule.subtype _) (by rwa [coeSubtype]),
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

section Constructions



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

-- -- TODO: The free matroid is trivially representable over every field.
-- def freeRep [DecidableEq α] (E : Set α) [DecidablePred (· ∈ E)] (𝔽 : Type*) [Field 𝔽] :
--   (freeOn E).Rep 𝔽 (α → 𝔽) := by
--     have :=




-- end Constructions

section Representable

/-- A matroid is representable if it has a representation -/
def Representable (M : Matroid α) (𝔽 : Type*) [Field 𝔽] : Prop := Nonempty (M.Rep 𝔽 (α → 𝔽))

/-- Noncomputably extract a representation from proof of representability -/
noncomputable def Representable.rep (h : M.Representable 𝔽) : M.Rep 𝔽 (α → 𝔽) :=
  Nonempty.some h

lemma Rep.representable (v : M.Rep 𝔽 W) : M.Representable 𝔽 := by
  have ⟨B, hB⟩ := M.exists_base
  set v' := v.standardRep' hB
  refine ⟨(v'.map' Finsupp.lcoeFun ?_).map'
    (Function.ExtendByZero.linearMap _ Subtype.val) ?_⟩
  · rw [Submodule.eq_bot_iff]; rintro x hx; simpa [Finsupp.lcoeFun] using hx
  rw [Submodule.eq_bot_iff]
  rintro x hx
  ext i
  simp only [ExtendByZero.linearMap, LinearMap.mem_ker, LinearMap.coe_mk, AddHom.coe_mk] at hx
  convert congr_fun hx i
  rw [Subtype.val_injective.extend_apply]

lemma IsRep.representable {v : α → W} (h : M.IsRep 𝔽 v) : M.Representable 𝔽 :=
  Rep.representable ⟨v, h⟩

lemma ofFun_representable (𝔽 : Type*) [Field 𝔽] [Module 𝔽 W] (f : α → W) (E : Set α) :
    (Matroid.ofFun 𝔽 E f).Representable 𝔽 :=
  (repOfFun 𝔽 E f).representable

lemma Representable.exists_standardRep' (h : Representable M 𝔽) (hB : M.Base B) :
    ∃ v : M.Rep 𝔽 (B →₀ 𝔽), v.FullRank :=
  let ⟨v⟩ := h; ⟨v.standardRep' hB, v.standardRep_fullRank' hB⟩

lemma Representable.exists_standardRep [FiniteRk M] (h : Representable M 𝔽) (hB : M.Base B) :
    ∃ v : M.Rep 𝔽 (B → 𝔽), v.FullRank  :=
  let ⟨v⟩ := h; ⟨v.standardRep hB, v.standardRep_fullRank hB⟩

lemma Representable.exists_fin_rep [FiniteRk M] (h : Representable M 𝔽) :
    ∃ v : M.Rep 𝔽 (Fin M.rk → 𝔽), v.FullRank := by
  obtain ⟨B, hB⟩ := M.exists_base
  have _ := hB.finite.fintype
  obtain ⟨v, hv⟩ := h.exists_standardRep hB
  have hcard := hB.ncard
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card] at hcard
  use v.mapEquiv <| LinearEquiv.piCongrLeft' 𝔽 (fun _ ↦ 𝔽) (Fintype.equivFinOfCardEq hcard)
  exact hv.mapEquiv _

lemma representable_emptyOn (α 𝔽 : Type*) [Field 𝔽] : (emptyOn α).Representable 𝔽 :=
  (emptyRep α 𝔽).representable

lemma representable_loopyOn (E : Set α) (𝔽 : Type*) [Field 𝔽] :
    (loopyOn E).Representable 𝔽 :=
  (loopyRep E 𝔽).representable

lemma Representable.map (h : M.Representable 𝔽) (f : α → β) (hf : M.E.InjOn f) :
    (M.map f hf).Representable 𝔽 := by
  have := h.rep.map f hf


-- lemma Representable.of_isIso {α β : Type*} {M : Matroid α} {N : Matroid β}
--     (h : M.Representable 𝔽) (hMN : M ≂ N) : N.Representable 𝔽 := by
--   obtain (⟨-, rfl⟩ | ⟨⟨e⟩⟩) := hMN
--   · apply representable_emptyOn
--   exact (h.rep.iso e).representable

-- lemma IsIso.representable_iff {α β : Type*} {M : Matroid α} {N : Matroid β} (hMN : M ≂ N) :
--     M.Representable 𝔽 ↔ N.Representable 𝔽 :=
--   ⟨fun h ↦ h.of_isIso hMN, fun h ↦ h.of_isIso hMN.symm⟩

/-- The property of being a finite `𝔽`-representable matroid. -/
class FieldRep (𝔽 : Type*) [Field 𝔽] (M : Matroid α) : Prop where
  rep : M.Representable 𝔽
  finite : M.Finite

lemma finite_of_fieldRep {𝔽 : Type*} (M : Matroid α) [Field 𝔽] [FieldRep 𝔽 M] : M.Finite :=
  FieldRep.finite 𝔽

/-- The property of being finite and representable over all fields. -/
class FieldRegular (M : Matroid α) : Prop where
  (rep_forall : ∀ (𝔽 : Type) [Field 𝔽], FieldRep 𝔽 M)

/-- The property of being finite and representable over some field. -/
class FieldSomeRep (M : Matroid α) : Prop where
  (rep_some : ∃ (𝔽 : Type) (_ : Field 𝔽), FieldRep 𝔽 M)

lemma fieldRep_def (𝔽 : Type*) [Field 𝔽] : FieldRep 𝔽 M ↔ M.Representable 𝔽 ∧ M.Finite :=
  ⟨fun ⟨h1,h2⟩ ↦ ⟨h1, h2⟩, fun ⟨h1, h2⟩ ↦ ⟨h1, h2⟩⟩

end Representable

-- lemma Rep.subset_span_of_basis' (v : M.Rep 𝔽 W) (h : M.Basis' I X) :
--     v '' X ⊆ span 𝔽 (v '' I) := by
--   rintro _ ⟨e, he, rfl⟩
--   obtain (heI | heI) := em (v e ∈ v '' I)
--   · exact subset_span heI
--   obtain (heI' | heI') := em (e ∈ I)
--   · exact (heI (mem_image_of_mem _ heI')).elim
--   have hi := h.insert_not_indep ⟨he, heI'⟩
--   rw [v.indep_iff_image, injOn_insert heI', and_iff_left heI,
--     and_iff_left (v.injOn_of_indep h.indep), image_insert_eq, (linearIndependent_insert heI),
--     not_and, not_not] at hi
--   exact hi <| v.indep_image h.indep

-- lemma Rep.subset_span_of_basis (v : M.Rep 𝔽 W) (h : M.Basis I X) : v '' X ⊆ span 𝔽 (v '' I) :=
--   v.subset_span_of_basis' h.basis'

-- lemma Rep.span_eq_span_inter_ground (v : M.Rep 𝔽 W) (X : Set α) :
--     span 𝔽 (v '' X) = span 𝔽 (v '' (X ∩ M.E)) := by
--   refine le_antisymm ?_ (span_mono (image_subset v <| inter_subset_left))
--   rw [← span_insert_zero (s := v '' (X ∩ M.E)), ← inter_union_diff X M.E, image_union,
--     inter_union_diff]
--   apply span_mono (union_subset (subset_insert _ _) _)
--   rintro _ ⟨e, he, rfl⟩
--   left
--   rw [← nmem_support]
--   exact not_mem_subset v.support_subset_ground he.2

-- @[simp] lemma Rep.span_eq_span_cl (v : M.Rep 𝔽 W) (X : Set α) :
--     span 𝔽 (v '' M.cl X) = span 𝔽 (v '' X) := by
--   rw [v.span_eq_span_inter_ground X, ← cl_inter_ground, le_antisymm_iff,
--     and_iff_left (span_mono (image_subset _ (M.subset_cl _)))]
--   obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E)
--   rw [← hI.cl_eq_cl]
--   exact (span_mono <| v.subset_span_of_basis hI.indep.basis_cl).trans <|
--     span_le.2 (span_mono (image_subset _ hI.subset))

-- lemma Rep.span_eq_span_of_basis' (v : M.Rep 𝔽 W) (h : M.Basis' I X) :
--     span 𝔽 (v '' I) = span 𝔽 (v '' X) :=
--   le_antisymm (span_mono (image_subset _ h.subset)) (span_le.2 (v.subset_span_of_basis' h))

-- lemma Rep.span_eq_span_of_basis (v : M.Rep 𝔽 W) (h : M.Basis I X) :
--     span 𝔽 (v '' I) = span 𝔽 (v '' X) :=
--   v.span_eq_span_of_basis' h.basis'

-- lemma Rep.span_le_span_of_cl_subset_cl (v : M.Rep 𝔽 W) (h : M.cl X ⊆ M.cl Y) :
--     span 𝔽 (v '' X) ≤ span 𝔽 (v '' Y) := by
--   obtain ⟨I, hI⟩ := M.exists_basis' X
--   refine span_le.2 <| (v.subset_span_of_basis' hI).trans <| span_le.2 ?_
--   rw [← v.span_eq_span_cl]
--   exact (image_subset _ (hI.basis_cl_right.subset.trans h)).trans subset_span

-- lemma Rep.subset_span_iff (v : M.Rep 𝔽 W) (hX : X ⊆ M.E := by aesop_mat) :
--     v '' X ⊆ span 𝔽 (v '' Y) ↔ X ⊆ M.cl Y := by
--   -- obtain ⟨I, hI⟩ := M.exists_basis' X

--   refine ⟨fun h e heX ↦ ?_, fun h ↦ ?_⟩
--   · obtain ⟨I, hI⟩ := M.exists_basis' Y
--     -- have hsp := h (mem_image_of_mem _ heX)
--     rw [← v.span_eq_span_of_basis' hI] at h
--     rw [← hI.cl_eq_cl, hI.indep.mem_cl_iff', and_iff_right (hX heX)]

--     specialize h (mem_image_of_mem _ heX)
--     refine fun hi ↦ by_contra fun heI ↦ ?_
--     have hind := v.indep_image hi
--     rw [image_insert_eq, linearIndependent_insert] at hind
--     · exact (hind.2 h).elim
--     refine fun heI' ↦ heI ?_
--     rwa [← (v.injOn_of_indep hi).mem_image_iff (subset_insert _ _) (mem_insert _ _)]
--   rw [← v.span_eq_span_cl]
--   exact (image_subset v h).trans subset_span


-- -- Ugly proof in the second part
-- lemma Rep.cl_eq (v : M.Rep 𝔽 W) (X : Set α) : M.cl X = M.E ∩ v ⁻¹' (span 𝔽 (v '' X)) := by
--   obtain ⟨I, hI⟩ := M.exists_basis' (X)
--   rw [← hI.cl_eq_cl, subset_antisymm_iff, subset_inter_iff, and_iff_right (cl_subset_ground _ _),
--     ← image_subset_iff, and_iff_left]
--   · exact (v.subset_span_of_basis hI.indep.basis_cl).trans (span_mono (image_subset _ hI.subset))
--   rintro x ⟨hxE, hx⟩
--   rw [mem_preimage] at hx

--   rw [hI.indep.mem_cl_iff, or_iff_not_imp_right, dep_iff,
--     and_iff_left <| insert_subset hxE hI.indep.subset_ground]
--   refine fun hxI hi ↦ ?_
--   apply (v.onIndep hi).not_mem_span_image (s := Subtype.val ⁻¹' I)
--     (x := ⟨x, mem_insert _ _⟩) (by simpa)

--   have hsp := span_mono (v.subset_span_of_basis' hI) hx

--   rw [span_coe_eq_restrictScalars, restrictScalars_self] at hsp
--   convert hsp
--   aesop

-- lemma Rep.span_eq_span_of_cl_eq_cl (v : M.Rep 𝔽 W) (h : M.cl X = M.cl Y) :
--     span 𝔽 (v '' X) = span 𝔽 (v '' Y) := by
--   rw [span_eq_span_inter_ground, span_eq_span_inter_ground _ Y]
--   simp_rw [le_antisymm_iff, span_le, v.subset_span_iff inter_subset_right, cl_inter_ground]
--   constructor
--   · rw [← h, ← cl_inter_ground]; exact subset_cl _ _
--   rw [h, ← cl_inter_ground]
--   exact subset_cl _ _



section Extension

variable [DecidableEq α]

noncomputable def Rep.addLoop (v : M.Rep 𝔽 W) (e : α) : (M.addLoop e).Rep 𝔽 W :=
  v.restrict (insert e M.E)

noncomputable def Rep.parallelExtend (v : M.Rep 𝔽 W) (e f : α) : (M.parallelExtend e f).Rep 𝔽 W :=
  (v.comap (update id f e)).restrict (insert f M.E)

lemma Rep.parallelExtend_apply (v : M.Rep 𝔽 W) (e f : α) {x : α} (hx : x ≠ f) :
    v.parallelExtend e f x = v x := by
  rw [Rep.parallelExtend, Rep.restrict_apply, indicator, Rep.comap_apply]
  split_ifs with h
  · rw [update_noteq hx, id]
  rw [v.eq_zero_of_not_mem_ground (not_mem_subset (subset_insert _ _) h)]

@[simp] lemma Rep.parallelExtend_apply_same (v : M.Rep 𝔽 W) (e f : α) :
    v.parallelExtend e f f = v e := by
  rw [Rep.parallelExtend, Rep.restrict_apply, indicator, if_pos (mem_insert _ _)]
  simp

-- noncomputable def se_foo (𝔽 : Type*) [Field 𝔽] (v : α → W) (e f : α) (a : α) : W × 𝔽 :=
--     if a = f then ⟨v e, 1⟩ else ⟨v a, 0⟩

-- lemma foo (M : Matroid α) (v : M.Rep 𝔽 W) (he : e ∈ M.E) (hnl : ¬ M.Coloop e) (hf : f ∉ M.E) :
--     (Matroid.ofFun 𝔽 E (se_foo 𝔽 v e f)) = M.seriesExtend e f := by
--   rw [eq_seriesExtend_iff he hnl hf]
--   simp

-- noncomputable def Representable.seriesExtend (v : M.Rep 𝔽 W) (e f : α) :
--     (M.seriesExtend e f).Rep 𝔽 (W × 𝔽) where
--   to_fun x := if x = f then ⟨v e,1⟩ else ⟨v x,0⟩
--   valid' := by
--     _

-- lemma Representable.parallelExtend (h : M.Representable 𝔽) (e f : α) :
--     (M.parallelExtend e f).Representable 𝔽 :=
--   (h.rep.parallelExtend e f).representable

-- /-- This doesn't actually need finiteness; constructing the obvious explicit
--   representation for the series extension is TODO. -/
-- lemma Representable.seriesExtend [M.Finite] (v : M.Rep 𝔽 W) (e f : α) :
--     (M.seriesExtend e f).Representable 𝔽 := by
--   rw [← dual_representable_iff, seriesExtend_dual]
--   apply Representable.parallelExtend
--   exact v.representable.dual


end Extension
