module

public import Matroid.MiniTauCeti.JCT.Topology.Order
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Topology.UnitInterval
public import Mathlib.Order.CountableDenseLinearOrder
public import Mathlib.Order.CompleteLatticeIntervals
public import Matroid.MiniTauCeti.JCT.Order.Completion

/-!
# Parametrization of compact separable ordered continua

An order isomorphism between dense subsets extends to their complete linear orders.
Consequently a nontrivial compact separable connected linear order is order isomorphic
to the unit interval, with its endpoints preserved.
-/

@[expose] public section

open Set Topology Function TopologicalSpace

private theorem dense_subtype_order {D : Type*} [CompleteLinearOrder D]
    [TopologicalSpace D] [OrderTopology D]
    [DenselyOrdered D] [Nontrivial D] (u : Set D) (hu : Dense u)
    (hbot : ∀ x, IsBot x → x ∉ u) (htop : ∀ x, IsTop x → x ∉ u) :
    DenselyOrdered u ∧ NoMinOrder u ∧ NoMaxOrder u ∧ Nonempty u := by
  refine ⟨⟨fun a b hab ↦ ?_⟩, ⟨fun a ↦ ?_⟩, ⟨fun a ↦ ?_⟩, hu.nonempty.to_subtype⟩
  · obtain ⟨d, hd, had, hdb⟩ := hu.exists_between hab
    exact ⟨⟨d, hd⟩, had, hdb⟩
  · obtain ⟨d, hd, hbd, hda⟩ := hu.exists_between
      (show (⊥ : D) < a.val from bot_lt_iff_ne_bot.mpr
        fun h ↦ hbot a.val (h.symm ▸ isBot_bot) a.property)
    exact ⟨⟨d, hd⟩, hda⟩
  · obtain ⟨d, hd, had, hdt⟩ := hu.exists_between
      (show a.val < (⊤ : D) from lt_top_iff_ne_top.mpr
        fun h ↦ htop a.val (h.symm ▸ isTop_top) a.property)
    exact ⟨⟨d, hd⟩, had⟩

/-- A compact separable connected linear order with distinct endpoints is the unit interval. -/
theorem exists_orderIso_unitInterval (K : Type*) [TopologicalSpace K] [LinearOrder K]
    [OrderTopology K] [CompactSpace K] [ConnectedSpace K] [SeparableSpace K]
    [Nontrivial K] : Nonempty (K ≃o unitInterval) := by
  let : DenselyOrdered K := denselyOrdered_of_preconnectedSpace
  let : CompleteLinearOrder K := LinearOrder.completeLinearOrderOfCompact K
  obtain ⟨s, hsc, hsd, hsbot, hstop⟩ := exists_countable_dense_no_bot_top K
  obtain ⟨t, htc, htd, htbot, httop⟩ := exists_countable_dense_no_bot_top unitInterval
  let : Countable s := hsc.to_subtype
  let : Countable t := htc.to_subtype
  obtain ⟨hsd', hsmin, hsmax, hsne⟩ := dense_subtype_order (D := K) s hsd hsbot hstop
  obtain ⟨htd', htmin, htmax, htne⟩ := dense_subtype_order (D := unitInterval) t htd htbot httop
  obtain ⟨e⟩ := Order.iso_of_countable_dense s t
  exact ⟨e.completion (fun _ _ h ↦ hsd.exists_between h)
    (fun _ _ h ↦ htd.exists_between h)⟩
