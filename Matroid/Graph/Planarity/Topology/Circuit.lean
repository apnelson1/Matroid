import Mathlib.Analysis.InnerProductSpace.PiL2 -- inefficient import
import Mathlib.Topology.UniformSpace.Path
import Mathlib.Analysis.Complex.Circle
import Mathlib.Topology.MetricSpace.Basic

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β] {a b c u v w x y z : α}
  {C X Y : Set α}

open Set Function TopologicalSpace Topology Metric Nat unitInterval

-- instance : PathConnectedSpace Circle := sorry

instance : Neg Circle where
  neg x := by
    refine ⟨-x.val, ?_⟩
    simp [Submonoid.unitSphere]

def IsCircuit {α} [TopologicalSpace α] (C : Set α) : Prop :=
  ∃ f : Circle → α, Topology.IsEmbedding f ∧ range f = C

-- lemma IsCircuit.pathConnected (hC : IsCircuit C) : IsPathConnected C := by
--   obtain ⟨f, hf, rfl⟩ := hC
--   exact isPathConnected_range hf.continuous

lemma circle_isCircuit : IsCircuit (univ : Set Circle) := ⟨id, IsEmbedding.id, by simp⟩

-- lemma isCircuit_iff_exists_paths (C : Set α) :
--     IsCircuit C ↔ ∃ (x y : α) (P₁ P₂ : Path x y), x ≠ y ∧ (range P₁ ∩ range P₂ = {x, y}) := by
--   refine ⟨?_, fun ⟨x, y, P₁, P₂, hne, h⟩ ↦ ?_⟩
--   · rintro ⟨f, hf, rfl⟩
--     let P : Path (f 1) (f (-1)) := {
--       toFun x := Circle.exp (Real.pi * x.val)
--       source' := _
--       target' := _
--     }
--     refine ⟨f 1, f (-1), ?_, ?_, (hf.injective.ne ?_), ?_⟩
--     ·

-- lemma IsCircuit.twoConnected (hC : IsCircuit C) : ∀ x, IsPathConnected (C \ {x}) := by
--   sorry

def IsCircuit.isEmbedding (hC : IsCircuit C) (f : α → β) (hf : Topology.IsEmbedding f) :
    IsCircuit (f '' C) := by
  obtain ⟨f', hf', rfl⟩ := hC
  exact ⟨f ∘ f', hf.comp hf', by simp [range_comp]⟩

-- lemma not_isCircuit_real (S : Set ℝ) : ¬ IsCircuit S := by
--   sorry
