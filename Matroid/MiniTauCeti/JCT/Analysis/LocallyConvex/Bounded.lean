module

public import Mathlib.Analysis.LocallyConvex.Bounded

/-! # Scalar contacts and avoiding rays of bounded sets -/

@[expose] public section

open Set Filter Topology

section Bounded

variable {𝕜 V : Type*} [NormedDivisionRing 𝕜] [Zero V] [MulAction 𝕜 V]
  [TopologicalSpace V] [T1Space V]

private theorem bounded_scalar_tail {S : Set V} (hS : Bornology.IsVonNBounded 𝕜 S)
    {v : V} (hv : v ≠ 0) :
    ∃ R > 0, ∀ c : 𝕜, R ≤ ‖c‖ → c • v ∉ S := by
  obtain ⟨R, hR, h⟩ := (hS (isClosed_singleton.isOpen_compl.mem_nhds
    (show (0 : V) ∈ ({v} : Set V)ᶜ from hv.symm))).exists_pos
  refine ⟨R, hR, fun c hc hcv ↦ ?_⟩
  have hc0 : c ≠ 0 := norm_pos_iff.mp (hR.trans_le hc)
  obtain ⟨w, hw, heq⟩ := h c hc hcv
  have : w = v := by
    have := congrArg (fun x ↦ c⁻¹ • x) heq
    simpa only [smul_smul, inv_mul_cancel₀ hc0, one_smul] using this
  exact hw (this ▸ mem_singleton v)

/-- A nonzero scalar orbit meets a bounded set only at bounded scalar parameters. -/
theorem Bornology.IsVonNBounded.isBounded_preimage_smul {S : Set V}
    (hS : Bornology.IsVonNBounded 𝕜 S)
    {v : V} (hv : v ≠ 0) :
    Bornology.IsBounded ((fun c : 𝕜 ↦ c • v) ⁻¹' S) := by
  obtain ⟨R, -, hR⟩ := bounded_scalar_tail hS hv
  rw [isBounded_iff_forall_norm_le]
  exact ⟨R, fun c hc ↦ le_of_lt (lt_of_not_ge fun h ↦ hR c h hc)⟩

end Bounded

section OrderedBounded

variable {𝕜 V : Type*} [NormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [IsOrderBornology 𝕜] [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [T1Space V]

/-- A bounded set admits a disjoint forward ray in every prescribed direction. -/
theorem Bornology.IsVonNBounded.exists_ray_avoiding [Nontrivial V] {S : Set V}
    (hS : Bornology.IsVonNBounded 𝕜 S) (v : V) :
    ∃ z ∉ S, ∀ t : 𝕜, 0 ≤ t → z + t • v ∉ S := by
  have htail {w : V} (hw : w ≠ 0) : ∃ c : 𝕜, ∀ t, c ≤ t → t • w ∉ S := by
    obtain ⟨B, hB⟩ := (hS.isBounded_preimage_smul hw).bddAbove
    exact ⟨B + 1, fun t ht hmem ↦ by linarith [hB hmem]⟩
  by_cases hv : v = 0
  · obtain ⟨w, hw⟩ := exists_ne (0 : V)
    obtain ⟨c, hc⟩ := htail hw
    exact ⟨c • w, hc c le_rfl, by simpa [hv] using fun (t : 𝕜) (_ : 0 ≤ t) ↦ hc c le_rfl⟩
  obtain ⟨c, hc⟩ := htail hv
  refine ⟨c • v, hc c le_rfl, fun t ht ↦ ?_⟩
  rw [← add_smul]
  exact hc (c + t) (by linarith)

end OrderedBounded

