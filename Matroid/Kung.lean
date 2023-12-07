import Matroid.Simple
import Matroid.ForMathlib.ENatTopology

open Set PSetoid
namespace Matroid

noncomputable def numPoints (M : Matroid α) : ℕ∞ := {P | M.Point P}.encard

theorem numPoints_eq_encard_parallelClasses (M : Matroid α) :
    M.numPoints = (classes M.Parallel).encard := by
  rw [numPoints, ← encard_univ_coe, M.parallelPointEquiv.symm.encard_univ_eq, encard_univ_coe]

theorem numPoints_eq_encard_ground_simplification (M : Matroid α) :
    M.numPoints = M.simplification.E.encard := by
  _
