
import Mathlib.Topology.Order.T5
import Mathlib.Data.Set.Basic
import Mathlib.Topology.Algebra.Monoid.Defs

open Set

variable {α β ι : Type*} [CompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]
  [CompleteLattice β] [TopologicalSpace β] {s : Set α} {f : α → β}

lemma Continuous.map_sSup [ClosedIicTopology β] (hcon : Continuous f) (hf : Monotone f)
    (hs : s.Nonempty) : f (sSup s) = ⨆ x ∈ s, f x := by
  suffices h' : ∀ x, IsLUB s x → IsLUB (range (fun (x : s) ↦ f x)) (f x) by
    simp only [le_antisymm_iff, iSup_le_iff]
    refine ⟨(h' (sSup s) (isLUB_sSup s)).2 ?_ , fun i hi ↦ hf (le_sSup hi)⟩
    simp only [mem_upperBounds, mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
      ← image_eq_range]
    exact fun y hys ↦ le_biSup _ hys
  intro x hx
  have := hs.to_subtype
  refine IsLUB.range_of_tendsto (f := fun (x : s) ↦ f x) (F := Filter.atTop) (a := f x)
    (fun a ↦ hf <| hx.1 a.2) ?_
  simp only [tendsto_atTop_nhds, Subtype.forall, Subtype.exists, Subtype.mk_le_mk, exists_prop]
  intro U hxU hU
  by_cases hxs : x ∈ s
  · exact ⟨x, hxs, fun y hys hxy ↦ by rwa [← hxy.antisymm (hx.1 hys)]⟩
  have hex : ∃ l, l < x := Exists.imp (fun z hzs ↦ (hx.1 hzs).lt_of_ne (by grind)) hs
  obtain ⟨l, hlx, hss⟩ := exists_Ioc_subset_of_mem_nhds ((hU.preimage hcon).mem_nhds hxU) hex
  by_cases hlb : l ∈ upperBounds s
  · exact False.elim <| (hx.2 hlb).not_gt hlx
  obtain ⟨z, hz, hlz⟩ : ∃ z ∈ s, l < z := by simpa [mem_upperBounds] using hlb
  exact ⟨z, hz, fun y hy hyz ↦ hss ⟨hlz.trans_le hyz, hx.1 hy⟩⟩

lemma Continuous.map_sInf [ClosedIciTopology β] {f : α → β} (hcon : Continuous f) (hf : Monotone f)
    (hs : s.Nonempty) : f (sInf s) = ⨅ x ∈ s, f x :=
  Continuous.map_sSup (α := αᵒᵈ) (β := βᵒᵈ) (f := f) hcon (by exact fun x y hxy ↦ hf hxy) hs

lemma Continuous.map_iSup [Nonempty ι] [ClosedIicTopology β] (hcon : Continuous f)
     (hf : Monotone f) (g : ι → α) : f (⨆ i, g i) = ⨆ i, f (g i) := by
  convert hcon.map_sSup hf (range_nonempty g)
  rw [iSup_range]

lemma Continuous.map_iInf [Nonempty ι] [ClosedIciTopology β] (hcon : Continuous f) (hf : Monotone f)
    (g : ι → α) : f (⨅ i, g i) = ⨅ i, f (g i) := by
  convert hcon.map_sInf hf (range_nonempty g)
  rw [iInf_range]

@[to_additive]
lemma mul_sSup [Mul α] [MulLeftMono α] [ContinuousMul α] (hs : s.Nonempty) (c : α) :
    c * sSup s = ⨆ i ∈ s, c * i :=
  (continuous_const_mul c).map_sSup (mul_right_mono ..) hs

@[to_additive]
lemma sSup_mul [Mul α] [MulRightMono α] [ContinuousMul α] (hs : s.Nonempty) (c : α) :
    (sSup s) * c = ⨆ i ∈ s, i * c :=
  (continuous_mul_const c).map_sSup (mul_left_mono ..) hs

@[to_additive]
lemma mul_iSup [Nonempty ι] [Mul α] [MulLeftMono α] [ContinuousMul α] (g : ι → α) (c : α) :
    c * ⨆ i, g i = ⨆ i, c * (g i) :=
  (continuous_const_mul c).map_iSup (mul_right_mono ..) g

@[to_additive]
lemma iSup_mul [Nonempty ι] [Mul α] [MulRightMono α] [ContinuousMul α] (g : ι → α) (c : α) :
    (⨆ i, g i) * c = ⨆ i, (g i) * c :=
  (continuous_mul_const c).map_iSup (mul_left_mono ..) g
