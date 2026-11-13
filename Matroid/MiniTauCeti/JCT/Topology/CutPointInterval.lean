module

public import Matroid.MiniTauCeti.JCT.Topology.CutPoint
public import Matroid.MiniTauCeti.JCT.Topology.OrderInterval
public import Mathlib.Topology.Path

/-!
# Recognizing intervals by endpoint separation

A compact separable T1 continuum in which every other point separates two fixed endpoints
admits a homeomorphism from the unit interval preserving those endpoints. The same
homeomorphism supplies an injective path covering the continuum.
-/

@[expose] public section

open Set Topology TopologicalSpace Function

namespace CutPoint

variable {K : Type*} [TopologicalSpace K] [T1Space K] [CompactSpace K]
  [SeparableSpace K] [PreconnectedSpace K]

/-- Strict separation of two endpoints by every other point recognizes a compact interval. -/
theorem exists_homeomorph_unitInterval (a b : K) (hab : a ≠ b)
    (hsep : ∀ z : K, z ≠ a → z ≠ b → Separates univ {z} a b) :
    ∃ e : unitInterval ≃ₜ K, e 0 = a ∧ e 1 = b := by
  let : LinearOrder K := separatorLinearOrder a b hsep
  obtain ⟨hlo, hhi⟩ := separatorLinearOrder_endpoints a b hsep
  let : BoundedOrder K := { bot := a, bot_le := hlo, top := b, le_top := hhi }
  let : Nontrivial K := ⟨⟨a, b, hab⟩⟩
  let : ConnectedSpace K := { toNonempty := ⟨a⟩ }
  let : OrderTopology K := separatorLinearOrder_orderTopology a b hsep
  obtain ⟨e⟩ := exists_orderIso_unitInterval K
  exact ⟨e.symm.toHomeomorph, e.symm.map_bot, e.symm.map_top⟩

/-- The interval recognition criterion supplies an injective path between the endpoints. -/
theorem exists_path_range_univ (a b : K) (hab : a ≠ b)
    (hsep : ∀ z : K, z ≠ a → z ≠ b → Separates univ {z} a b) :
    ∃ P : Path a b, Injective P ∧ range P = univ := by
  obtain ⟨e, he0, he1⟩ := exists_homeomorph_unitInterval a b hab hsep
  let P : Path a b :=
    { toFun := e
      continuous_toFun := e.continuous
      source' := he0
      target' := he1 }
  exact ⟨P, e.injective, e.surjective.range_eq⟩

end CutPoint
