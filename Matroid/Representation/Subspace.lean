import Matroid.Representation.Basic

variable {α β W W' 𝔽 R : Type _} {e f x : α} {I B X Y : Set α} {M : Matroid α} [Field 𝔽]
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W']

open Function Set Submodule FiniteDimensional BigOperators

namespace Matroid

-- /-- The 'row space' corresponding to the representation `v` -/
-- def Rep.subspaceRep (v : M.Rep 𝔽 W) : Submodule 𝔽 (α → 𝔽) := Submodule.ofFun 𝔽 v

/-- the subspace of `X → 𝔽` corresponding to a set `X` -/
def Rep.projSet (v : M.Rep 𝔽 W) (X : Set α) : Submodule 𝔽 (X → 𝔽) := ofFun 𝔽 (v ∘ Subtype.val)

theorem Rep.projSet_eq_map (v : M.Rep 𝔽 W) (X : Set α) :
    v.projSet X = (Submodule.ofFun 𝔽 v).map (LinearMap.fun_subtype 𝔽 X) := by
  ext x; simp only [projSet, mem_ofFun_iff, mem_map, exists_exists_eq_and]; aesop

theorem Rep.indep_iff_projSet_eq_top (v : M.Rep 𝔽 W) : M.Indep I ↔ v.projSet I = ⊤ := by
  rw [v.indep_iff, Rep.projSet, ofFun_eq_top_iff]; rfl

/-- A finite submodule of `α → 𝔽` determines a matroid on `α` -/
def matroid_on_univ_of_subspace (U : Submodule 𝔽 (α → 𝔽)) [FiniteDimensional 𝔽 U] : Matroid α :=
  matroid_of_indep_of_exists_matroid
    univ
    (fun I ↦ (U.map (LinearMap.fun_subtype 𝔽 I) = ⊤))
  ( by
    obtain ⟨s, ⟨b⟩⟩ := Basis.exists_basis 𝔽 U
    set v := rep_of_fun_univ 𝔽 <| fun a i ↦ (b i).1 a
    refine ⟨matroid_on_univ_of_fun 𝔽 <| fun a i ↦ (b i).1 a, rfl, fun I ↦ ?_⟩
    rw [v.indep_iff_projSet_eq_top, v.projSet_eq_map]
    have hUf : (ofFun 𝔽 <| fun a i ↦ (b i).1 a) = U := b.eq_ofFun
    simp_rw [←hUf]
    rfl )

def matroid_of_subspace (E : Set α) (U : Submodule 𝔽 (α → 𝔽)) [FiniteDimensional 𝔽 U] :
    Matroid α := (matroid_on_univ_of_subspace U) ↾ E

/-- A representation of `M` by a subspace where independence corresponds to projections having
  full dimension -/
structure SubspaceRep (M : Matroid α) (𝔽 : Type _) [Field 𝔽] where
  ( space : Submodule 𝔽 (α → 𝔽) )
  ( valid : ∀ I, M.Indep I ↔ space.map (LinearMap.fun_subtype 𝔽 I) = ⊤ )

instance {M : Matroid α} {𝔽 : Type _} [Field 𝔽] :
    CoeOut (SubspaceRep M 𝔽) (Submodule 𝔽 (α → 𝔽)) where
  coe := SubspaceRep.space

/-- This doesn't seem to work - coercion is just displayed as `U.carrier` in the pp. -/
@[simp] theorem SubspaceRep.carrier_eq_coe {M : Matroid α} {𝔽 : Type _} [Field 𝔽]
  (U : SubspaceRep M 𝔽) : U.space = (↑U : Submodule 𝔽 (α → 𝔽)) := rfl

@[simp] theorem SubspaceRep.indep_iff {M : Matroid α} {𝔽 : Type _} [Field 𝔽] (U : SubspaceRep M 𝔽)
    {I : Set α} : M.Indep I ↔ (U : Submodule 𝔽 (α → 𝔽)).map (LinearMap.fun_subtype 𝔽 I) = ⊤ :=
  U.valid I

/-- A representation `v` canonically gives a subspace representation (its 'row space')-/
def Rep.subspaceRep (v : M.Rep 𝔽 W) : M.SubspaceRep 𝔽 where
  space := ofFun 𝔽 v
  valid := fun I ↦ by rw [←v.projSet_eq_map, v.indep_iff_projSet_eq_top]

@[simp] theorem Rep.subspaceRep_apply (v : M.Rep 𝔽 W) :
    v.subspaceRep.space = ofFun 𝔽 v := rfl

theorem SubspaceRep.representable (U : M.SubspaceRep 𝔽) [FiniteDimensional 𝔽 U] :
    M.Representable 𝔽 := by
  obtain ⟨s, ⟨b⟩⟩ := Basis.exists_basis 𝔽 U
  have hM : M = matroid_of_fun 𝔽 (fun a i ↦ (b i).1 a : α → (s → 𝔽)) M.E
  · rw [eq_iff_indep_iff_indep_forall]
    refine ⟨rfl, fun I hIE ↦ ?_⟩
    rw [matroid_of_fun_indep_iff', and_iff_left hIE, U.indep_iff]
    simp_rw [←b.eq_ofFun, ←ofFun_comp_coe, ofFun_eq_top_iff]
    rfl
  rw [hM]
  apply matroid_of_fun_representable

end Matroid

@[pp_dot] noncomputable def Submodule.orthspace [Fintype α] (U : Submodule 𝔽 (α → 𝔽)) :
    Submodule 𝔽 (α → 𝔽) :=
  U.dualAnnihilator.map (Module.piEquiv α 𝔽 𝔽).symm

@[simp] theorem Module.piEquiv_apply_symm [Fintype α] [DecidableEq α]
    (y : Module.Dual 𝔽 (α → 𝔽)) (i : α) :
    (Module.piEquiv α 𝔽 𝔽).symm y i = y (Function.update 0 i 1) := by
  simp [piEquiv, Basis.constr, LinearMap.stdBasis_apply]

@[simp] theorem Module.Dual.sum_update [Fintype α] [DecidableEq α] (y : Module.Dual 𝔽 (α → 𝔽))
    (x : α → 𝔽) : ∑ i, y (update 0 i 1) * x i = y x := by
  rw [←LinearMap.congr_fun ((Pi.basisFun 𝔽 α).sum_dual_apply_smul_coord y) x]
  simp [LinearMap.stdBasis_apply]

@[simp] theorem mem_orthspace_iff [Fintype α] {U : Submodule 𝔽 (α → 𝔽)} {x : α → 𝔽} :
    x ∈ U.orthspace ↔ ∀ y ∈ U, ∑ i, x i * y i = 0 := by
  classical
  simp only [orthspace, mem_map, mem_dualAnnihilator]
  refine ⟨?_, fun h ↦ ⟨Module.piEquiv α 𝔽 𝔽 x, fun w hw ↦ ?_, by simp⟩⟩
  · rintro ⟨y, hy, rfl⟩ x hxU
    convert hy x hxU using 1
    simp [Module.piEquiv_apply_symm]
  convert h w hw using 1
  simp_rw [Module.piEquiv_apply_apply, smul_eq_mul, mul_comm]

@[simp] theorem orth_orth [Fintype α] (U : Subspace 𝔽 (α → 𝔽)) :
    U.orthspace.orthspace = U := by
  refine (eq_of_le_of_finrank_le (fun x hxU ↦ ?_) (le_of_eq ?_)).symm
  · simp_rw [mem_orthspace_iff]
    intro y hy
    simpa [mul_comm] using hy x hxU
  rw [orthspace, orthspace, LinearEquiv.finrank_map_eq', LinearEquiv.dualAnnihilator_map_eq, LinearEquiv.finrank_map_eq',
    ←Subspace.finrank_dualCoannihilator_eq, Subspace.dualAnnihilator_dualCoannihilator_eq]


noncomputable def foo [Fintype α] {B : Set α} (f : α → W) (b : _root_.Basis B 𝔽 W)
    (hfb : ∀ x, b x = f x) : _root_.Basis B 𝔽 (ofFun 𝔽 f) :=
  let w : B → (α → 𝔽) := fun i ↦ (b.coord i) ∘ f
  have _ := Fintype.ofFinite ↑B
  have hli : LinearIndependent 𝔽 w := by
    simp only
    -- simp [Fintype.linearIndependent_iff]
    -- intro g hg a haB
    have h := b.linearIndependent
    have hli' : LinearIndependent 𝔽 (B.restrict f)
    · sorry
    set e1 := b.equivFun.toLinearMap
    set e2 := Matrix.vecMulLinear w

    convert LinearIndependent.map hli' (f := e2.comp e1) ?_ using 1
    · ext a x
      rw [comp_apply, ←b.sum_equivFun (f x)]
      simp only [Basis.equivFun_apply, map_sum, map_smulₛₗ, RingHom.id_apply, Basis.coord_apply,
        Basis.repr_self, ne_eq, smul_eq_mul, LinearMap.coe_comp, LinearEquiv.coe_coe, comp_apply,
        restrict_apply, ← hfb, Matrix.vecMulLinear_apply, Matrix.vecMul, Matrix.dotProduct]

      apply Finset.sum_congr rfl
      rintro y -
      rw [mul_comm, Finsupp.single_swap]




  have hsp : span 𝔽 (range w) = ofFun 𝔽 f := by
    sorry
  (_root_.Basis.span hli).map (LinearEquiv.ofEq _ _ hsp)




  -- have := Basis.span (R := 𝔽) (v := w) sorry
  -- have : Basis B 𝔽 := _root_.Basis.mk (ι := B) (v := w) sorry sorry

-- theorem foo [Fintype α] {M N : Matroid α} (hME : M.E = univ) (hNE : N.E = univ)
--     (f : M.Rep 𝔽 W) (g : N.Rep 𝔽 W') {B : Set α} (hB : M.Base B)
--     (h_orth : f.subspaceRep.space.orthspace = g.subspaceRep) :
--     N.Indep Bᶜ :=

--   sorry






  -- simp only [mem_orthspace_iff, le_antisymm_iff]


-- theorem [Fintype α] (U U' : Submodule 𝔽 (α → 𝔽)) :






-- theorem foo [Fintype α] (U : Submodule 𝔽 (α → 𝔽)) (B : Set α) (hB : )

-- theorem dual_foo [Fintype α] {M M' : Matroid α} (hM : M.E = univ) (hM' : M'.E = univ)
--   (v : M.Rep 𝔽 W) (v' : M.Rep 𝔽 W')

-- theorem dual_foo (E : Set α) (U W : )


-- noncomputable def matroid_of_subspace_substype


-- theorem rep_of_subspace_rep (E : Set α) (U : Submodule 𝔽 (α → 𝔽)) [FiniteDimensional 𝔽 U] :
--     (matroid_of_subspace E U).Representable 𝔽 := by
--   rw [matroid_of_subspace]
--   -- apply Rep.representable
