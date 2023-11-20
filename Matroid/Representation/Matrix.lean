import Matroid.Representation.Basic
import Matroid.ForMathlib.LinearAlgebra.Matrix.Rowspace

variable {α β ι W W' 𝔽 R : Type*} {e f x : α} {I B X Y : Set α} {M : Matroid α} [Field 𝔽]
  [AddCommGroup W] [Module 𝔽 W] [AddCommGroup W'] [Module 𝔽 W']

open Submodule Set Matroid Matrix

namespace Matroid
