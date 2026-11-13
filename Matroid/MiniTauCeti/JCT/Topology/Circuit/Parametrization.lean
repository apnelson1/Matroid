module

public import Matroid.MiniTauCeti.JCT.Topology.Circuit.Basic
public import Matroid.MiniTauCeti.JCT.Topology.Circle

/-!
# Circuits from supplied parametrizations

An injective continuous circle map, or a simple loop, gives an intrinsic circuit when its
range is Hausdorff. No separation assumption on the ambient space is required. These are
one-way constructors, not classification theorems for intrinsic circuits.
-/

@[expose] public section

open Set Function Topology

lemma circle_isCircuit : IsCircuit (univ : Set Circle) := by
  refine ⟨isConnected_univ, fun x _ ↦ ?_, fun a _ b _ hab ↦ ?_⟩
  · simpa only [← compl_eq_univ_sdiff] using
      (Circle.isPathConnected_compl_singleton x).isConnected
  simpa only [← compl_eq_univ_sdiff] using Circle.not_isPreconnected_compl_pair hab

variable {X : Type*} [TopologicalSpace X] {x : X}

/-- A supplied injective circle map constructs a circuit in a Hausdorff range. -/
lemma isCircuit_range_of_injective_circle_map (f : C(Circle, X)) [T2Space ↥(range f)]
    (hf : Injective f) : IsCircuit (range f) := by
  have he : IsEmbedding (codRestrict f (range f) (mem_range_self)) :=
    (f.continuous.codRestrict mem_range_self).isClosedEmbedding
      (hf.codRestrict mem_range_self) |>.isEmbedding
  have he' : IsEmbedding f := IsEmbedding.subtypeVal.comp he
  simpa only [image_univ] using circle_isCircuit.image (he'.comp IsEmbedding.subtypeVal)

/-- A supplied simple loop constructs a circuit in a Hausdorff range. -/
lemma Path.IsSimpleLoop.isCircuit {P : Path x x} [T2Space ↥(range P)]
    (hP : P.IsSimpleLoop) : IsCircuit (range P) := by
  have : T2Space ↥(range P.onCircle) := by
    rw [P.range_onCircle]
    infer_instance
  simpa only [P.range_onCircle] using
    isCircuit_range_of_injective_circle_map P.onCircle (Path.onCircle_injective hP)
