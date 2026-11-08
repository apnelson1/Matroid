module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Data.Set.Subsingleton

/-!
# Intrinsic circuits

A circuit is a connected set whose singleton punctures are connected and whose punctures at
any two distinct points are not preconnected. In particular, an empty remainder does not count
as disconnected. Nontriviality follows from connectedness of the singleton punctures.

This definition imposes no compactness, separability, metrizability, or ambient separation
hypothesis. An intrinsic circuit need not admit an ordinary-circle parametrization.
-/

@[expose] public section

open Set Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {S : Set X} {T : Set Y}

/-- A circuit is connected, remains connected after deleting one point, and is disconnected
in the sense of non-preconnectedness after deleting any two distinct points. -/
structure IsCircuit (S : Set X) : Prop where
  isConnected : IsConnected S
  puncture_isConnected ⦃x : X⦄ : x ∈ S → IsConnected (S \ {x})
  pair_puncture_not_isPreconnected ⦃a b : X⦄ :
    a ∈ S → b ∈ S → a ≠ b → ¬ IsPreconnected (S \ {a, b})

namespace IsCircuit

lemma nonempty (hS : IsCircuit S) : S.Nonempty := hS.isConnected.nonempty

lemma nontrivial (hS : IsCircuit S) : S.Nontrivial := by
  obtain ⟨x, hx⟩ := hS.nonempty
  obtain ⟨y, hy, hyx⟩ := (hS.puncture_isConnected hx).nonempty
  exact ⟨x, hx, y, hy, fun h ↦ hyx (by simpa using h.symm)⟩

lemma isPreconnected (hS : IsCircuit S) : IsPreconnected S := hS.isConnected.isPreconnected

/-- Deleting a point outside the circuit leaves it unchanged. -/
lemma isConnected_sdiff_singleton (hS : IsCircuit S) (x : X) : IsConnected (S \ {x}) := by
  by_cases hx : x ∈ S
  · exact hS.puncture_isConnected hx
  simpa [sdiff_singleton_eq_self hx] using hS.isConnected

end IsCircuit

/-- An embedding preserves and reflects the intrinsic circuit conditions. -/
theorem Topology.IsEmbedding.isCircuit_image {f : X → Y} (hf : IsEmbedding f) :
    IsCircuit (f '' S) ↔ IsCircuit S := by
  have hconn (A : Set X) : IsConnected (f '' A) ↔ IsConnected A := by
    simp only [IsConnected, image_nonempty, hf.isInducing.isPreconnected_image]
  constructor
  · intro hS
    refine ⟨(hconn S).mp hS.isConnected, ?_, ?_⟩
    · intro x hx
      apply (hconn (S \ {x})).mp
      simpa only [image_sdiff hf.injective, image_singleton] using
        hS.puncture_isConnected (mem_image_of_mem f hx)
    intro a b ha hb hab hpre
    apply hS.pair_puncture_not_isPreconnected (mem_image_of_mem f ha)
      (mem_image_of_mem f hb) (hf.injective.ne hab)
    simpa only [image_sdiff hf.injective, image_pair] using
      hpre.image f hf.continuous.continuousOn
  intro hS
  refine ⟨(hconn S).mpr hS.isConnected, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    simpa only [image_sdiff hf.injective, image_singleton] using
      (hconn (S \ {x})).mpr (hS.puncture_isConnected hx)
  rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ hab hpre
  apply hS.pair_puncture_not_isPreconnected ha hb (fun h ↦ hab (congrArg f h))
  apply hf.isInducing.isPreconnected_image.mp
  simpa only [image_sdiff hf.injective, image_pair] using hpre

/-- The circuit conditions depend only on the topology of the carrier. -/
theorem isCircuit_iff_subtype : IsCircuit S ↔ IsCircuit (univ : Set ↥S) := by
  simpa using (IsEmbedding.subtypeVal (p := (· ∈ S))).isCircuit_image (S := univ)

/-- Restricting the ambient space to a set containing the circuit preserves its conditions. -/
theorem isCircuit_preimage_subtypeVal_iff {S T : Set X} (hST : S ⊆ T) :
    IsCircuit ((Subtype.val : ↥T → X) ⁻¹' S) ↔ IsCircuit S := by
  simpa only [Subtype.image_preimage_val, inter_eq_right.mpr hST] using
    (IsEmbedding.subtypeVal.isCircuit_image (S := (Subtype.val : ↥T → X) ⁻¹' S)).symm

/-- An embedding on the carrier preserves and reflects the circuit conditions. -/
theorem isCircuit_image_iff {f : X → Y} (hf : IsEmbedding (fun x : ↥S ↦ f x)) :
    IsCircuit (f '' S) ↔ IsCircuit S := by
  rw [isCircuit_iff_subtype (S := S)]
  simpa only [image_univ, ← image_eq_range] using hf.isCircuit_image (S := univ)

/-- Homeomorphic carriers have the same circuit conditions. -/
theorem isCircuit_iff_of_homeomorph (e : ↥S ≃ₜ ↥T) : IsCircuit S ↔ IsCircuit T := by
  rw [isCircuit_iff_subtype (S := S), isCircuit_iff_subtype (S := T)]
  simpa using (e.isEmbedding.isCircuit_image (S := univ)).symm

lemma IsCircuit.image (hS : IsCircuit S) {f : X → Y}
    (hf : IsEmbedding (fun x : ↥S ↦ f x)) : IsCircuit (f '' S) :=
  (isCircuit_image_iff hf).mpr hS

lemma IsCircuit.homeomorph_carrier (hS : IsCircuit S) (e : ↥S ≃ₜ ↥T) : IsCircuit T :=
  (isCircuit_iff_of_homeomorph e).mp hS
