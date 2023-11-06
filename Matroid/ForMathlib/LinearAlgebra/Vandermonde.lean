import Mathlib.LinearAlgebra.Vandermonde
import Matroid.ForMathlib.LinearAlgebra.Matrix

open Set Function

def Matrix.vandermonde' {R : Type*} [CommRing R] (m : ℕ) {n : ℕ} (f : Fin n → R) :
    Matrix (Fin m) (Fin n) R := Matrix.of (fun (i : Fin m) j => (f j) ^ (i : ℕ))


-- theorem foo {m n : ℕ} (hmn : n ≤ m) [CommRing R] {n : ℕ} (f : fin n → R) (hf : Injective f) :
--   LinearIndependent ()
