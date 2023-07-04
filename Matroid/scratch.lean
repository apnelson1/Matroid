import Matroid.Init
import Mathlib.Tactic




set_option trace.aesop true

@[ext] structure Matroid (α : Type _) where
  (ground : Set α)
  (Base : Set α → Prop)

namespace Matroid

def Basis (M : Matroid α) (I X : Set α) : Prop := I ⊆ X 
def cl : Set α → Set α := id  

theorem foo (α : Type _) (M : Matroid α) (I X : Set α) (hI : M.Basis I X) (e : α) (heX : e ∈ cl X)  :
    false := by
  aesop (options := {terminal := true})
-- aesop $c* (options := { terminal := true })
--   (rule_sets [$(Lean.mkIdent `Matroid):ident])
