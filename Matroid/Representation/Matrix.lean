import Matroid.Representation.Basic

variable {α β W W' 𝔽 R : Type _} {e f x : α} {I B X Y : Set α} {M : Matroid α} [Field 𝔽]
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W']


open Submodule Set
namespace Matroid

structure MatrixRep (M : Matroid α) (𝔽 R : Type _) [Field 𝔽] where
  ( A : Matrix R α 𝔽 )
  ( v : M.Rep 𝔽 (R → 𝔽) )
  ( compatible : ∀ i e, A i e = v e i )

def MatrixRep.Emat (P : M.MatrixRep 𝔽 R) : Matrix R M.E 𝔽 :=
  Matrix.of fun (i : R) (e : M.E) ↦ P.A i e
