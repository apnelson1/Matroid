module

public import Matroid.ForMathlib.Topology.Circuit
public import Matroid.ForMathlib.Topology.Path.Crossing

/-!
# Boundary crossings of circuits

The current circuit parametrization supplies a path with equal endpoints. Path crossing parity
then gives evenness. This adapter isolates the parametrization from the general crossing API.
-/

@[expose] public section

open Set unitInterval

variable {X : Type*} [TopologicalSpace X]

/-- A circuit with Hausdorff carrier has an even number of boundary crossings whenever its
intersection with the boundary is finite. -/
theorem IsCircuit.even_ncard_boundaryCrossings {S U : Set X} [T2Space ↥S] (hS : IsCircuit S)
    (hfin : (S ∩ frontier U).Finite) : Even (boundaryCrossings S U).ncard := by
  classical
  obtain ⟨x, hxS, hx⟩ : ∃ x ∈ S, x ∉ frontier U := by
    by_contra h
    push Not at h
    exact hS.infinite (hfin.subset fun x hx ↦ ⟨hx, h x hx⟩)
  obtain ⟨P, hPinj, hPrange⟩ := hS.exists_path_injOn_Ico hxS
  have hinj : InjOn P (P ⁻¹' frontier U) := by
    apply hPinj.mono
    intro t ht
    refine ⟨t.2.1, lt_of_le_of_ne t.2.2 ?_⟩
    rintro rfl
    exact hx (P.target ▸ ht)
  rw [Nat.even_iff, P.ncard_boundaryCrossings_mod_two hPrange hfin
    (hinj.mono (fun _ h ↦ h.1.2)) hx hx]
  simp
