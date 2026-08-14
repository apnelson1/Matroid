module

public import Matroid.Representation.Basic

variable {α β W W' 𝔽 R : Type*} {e f x : α} {I B X Y : Set α} {M : Matroid α} [Field 𝔽]
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W']

open Function Set Submodule FiniteDimensional BigOperators

namespace Matroid

-- /-- The 'row space' corresponding to the representation `v` -/
-- def Rep.subspaceRep (v : M.Rep 𝔽 W) : Submodule 𝔽 (α → 𝔽) := Submodule.ofFun 𝔽 v

/-- the subspace of `X → 𝔽` corresponding to a set `X` -/
def Rep.projSet (v : M.Rep 𝔽 W) (X : Set α) : Submodule 𝔽 (X → 𝔽) := ofFun 𝔽 (v ∘ Subtype.val)

theorem Rep.projSet_eq_map (v : M.Rep 𝔽 W) (X : Set α) :
    v.projSet X = (Submodule.ofFun 𝔽 v).map (IsLinearMap.fun_subtype 𝔽 X) := by
  ext x; simp only [projSet, mem_ofFun_iff, mem_map, exists_exists_eq_and]; aesop

theorem Rep.indep_iff_projSet_eq_top (v : M.Rep 𝔽 W) : M.Indep I ↔ v.projSet I = ⊤ := by
  rw [v.indep_iff, Rep.projSet, ofFun_eq_top_iff]; rfl

/-- A finite submodule of `α → 𝔽` determines a matroid on `α` -/
def matroidOnUnivOfSubspace (U : Submodule 𝔽 (α → 𝔽)) [FiniteDimensional 𝔽 U] : Matroid α :=
  matroid_of_indep_of_exists_matroid
    univ
    (fun I ↦ (U.map (IsLinearMap.fun_subtype 𝔽 I) = ⊤))
  ( by
    obtain ⟨s, ⟨b⟩⟩ := IsBasis.exists_isBasis 𝔽 U
    set v := repOfFunUniv 𝔽 <| fun a i ↦ (b i).1 a
    refine ⟨matroidOnUnivOfFun 𝔽 <| fun a i ↦ (b i).1 a, rfl, fun I ↦ ?_⟩
    rw [v.indep_iff_projSet_eq_top, v.projSet_eq_map]
    have hUf : (ofFun 𝔽 <| fun a i ↦ (b i).1 a) = U := b.eq_ofFun
    simp_rw [← hUf]
    rfl )

def matroid_of_subspace (E : Set α) (U : Submodule 𝔽 (α → 𝔽)) [FiniteDimensional 𝔽 U] :
    Matroid α := (matroidOnUnivOfSubspace U) ↾ E

/-- A representation of `M` by a subspace where independence corresponds to projections having
  full dimension -/
structure SubspaceRep (M : Matroid α) (𝔽 : Type*) [Field 𝔽] where
  ( space : Submodule 𝔽 (α → 𝔽) )
  ( valid : ∀ I, M.Indep I ↔ space.map (IsLinearMap.fun_subtype 𝔽 I) = ⊤ )

instance {M : Matroid α} {𝔽 : Type*} [Field 𝔽] :
    CoeOut (SubspaceRep M 𝔽) (Submodule 𝔽 (α → 𝔽)) where
  coe := SubspaceRep.space

/-- This doesn't seem to work - coercion is just displayed as `U.carrier` in the pp. -/
@[simp] theorem SubspaceRep.carrier_eq_coe {M : Matroid α} {𝔽 : Type*} [Field 𝔽]
  (U : SubspaceRep M 𝔽) : U.space = (↑U : Submodule 𝔽 (α → 𝔽)) := rfl

@[simp] theorem SubspaceRep.indep_iff {M : Matroid α} {𝔽 : Type*} [Field 𝔽] (U : SubspaceRep M 𝔽)
    {I : Set α} : M.Indep I ↔ (U : Submodule 𝔽 (α → 𝔽)).map (IsLinearMap.fun_subtype 𝔽 I) = ⊤ :=
  U.valid I

/-- A representation `v` canonically gives a subspace representation (its 'row space')-/
def Rep.subspaceRep (v : M.Rep 𝔽 W) : M.SubspaceRep 𝔽 where
  space := ofFun 𝔽 v
  valid := fun I ↦ by rw [← v.projSet_eq_map, v.indep_iff_projSet_eq_top]

@[simp] theorem Rep.subspaceRep_apply (v : M.Rep 𝔽 W) :
    v.subspaceRep.space = ofFun 𝔽 v := rfl

theorem SubspaceRep.representable (U : M.SubspaceRep 𝔽) [FiniteDimensional 𝔽 U] :
    M.Representable 𝔽 := by
  obtain ⟨s, ⟨b⟩⟩ := IsBasis.exists_isBasis 𝔽 U
  have hM : M = matroidOfFun 𝔽 (fun a i ↦ (b i).1 a : α → (s → 𝔽)) M.E
  · rw [ext_iff_indep]
    refine ⟨rfl, fun I hIE ↦ ?_⟩
    rw [matroidOfFun_indep_iff', and_iff_left hIE, U.indep_iff]
    simp_rw [← b.eq_ofFun, ← ofFun_comp_coe, ofFun_eq_top_iff]
    rfl
  rw [hM]
  apply matroidOfFun_representable

end Matroid

@[pp_dot] noncomputable def Submodule.orthspace [Fintype α] (U : Submodule 𝔽 (α → 𝔽)) :
    Submodule 𝔽 (α → 𝔽) :=
  U.dualAnnihilator.map (Module.piEquiv α 𝔽 𝔽).symm
