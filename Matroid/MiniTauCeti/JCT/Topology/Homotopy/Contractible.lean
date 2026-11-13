module

public import Mathlib.Topology.Homotopy.Contractible

/-! # Homotopy retracts of contractible spaces -/

public section

/-- A homotopy retract of a contractible space is contractible. -/
theorem ContractibleSpace.of_homotopy_retract {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [ContractibleSpace X]
    (i : C(Y, X)) (r : C(X, Y)) (hri : (r.comp i).Homotopic (ContinuousMap.id Y)) :
    ContractibleSpace Y := by
  obtain ⟨y, hy⟩ : (r.comp i).Nullhomotopic := by
    simpa only [ContinuousMap.comp_id] using
      ((id_nullhomotopic X).comp_right r).comp_left i
  exact (contractible_iff_id_nullhomotopic Y).mpr ⟨y, hri.symm.trans hy⟩
