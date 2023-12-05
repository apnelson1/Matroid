import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Set.Intervals.WithBotTop
import Mathlib.Topology.Algebra.Order.MonotoneConvergence
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Instances.ENNReal

namespace ENat

open Set BigOperators Topology Filter

variable {α : Type*} {f g : α → ℕ∞}

section Topology

instance : TopologicalSpace ℕ∞ := Preorder.topology ℕ∞

instance : OrderTopology ℕ∞ := ⟨rfl⟩

@[simp] theorem range_coe' : range ((↑) : ℕ → ℕ∞) = Iio ⊤ :=
  WithTop.range_coe

theorem embedding_coe : Embedding ((↑) : ℕ → ℕ∞) :=
  Nat.strictMono_cast.embedding_of_ordConnected <| by rw [range_coe']; exact ordConnected_Iio

theorem openEmbedding_coe : OpenEmbedding ((↑) : ℕ → ℕ∞) :=
  ⟨embedding_coe, range_coe' ▸ isOpen_Iio⟩

@[simp] theorem isOpen_image_coe (s : Set ℕ) : IsOpen (((↑) : ℕ → ℕ∞) '' s) := by
  rw [←openEmbedding_coe.open_iff_image_open]; exact trivial

theorem isOpen_singleton {x : ℕ∞} (hx : x ≠ ⊤) : IsOpen {x} := by
  lift x to ℕ using hx
  rw [←image_singleton, ←openEmbedding_coe.open_iff_image_open]
  exact trivial

@[simp] theorem isOpen_coe_singleton (n : ℕ) : IsOpen {(n : ℕ∞)} :=
  isOpen_singleton (coe_ne_top n)

theorem isOpen_of_top_not_mem {s : Set ℕ∞} (h : ⊤ ∉ s) : IsOpen s := by
  convert isOpen_image_coe ((↑) ⁻¹' s)
  simp_rw [eq_comm (a := s), image_preimage_eq_iff, range_coe', Iio, lt_top_iff_ne_top,
    ← compl_singleton_eq, subset_compl_singleton_iff]
  assumption

theorem mem_nhds_iff {x : ℕ∞} {s : Set ℕ∞} (hx : x ≠ ⊤) : s ∈ 𝓝 x ↔ x ∈ s := by
  rw [_root_.mem_nhds_iff]
  exact ⟨fun ⟨_, h, _, h'⟩ ↦ h h', fun h ↦ ⟨_, singleton_subset_iff.2 h, isOpen_singleton hx, rfl⟩⟩

@[simp] theorem mem_nhds_coe_iff (n : ℕ) : s ∈ 𝓝 (n : ℕ∞) ↔ (n : ℕ∞) ∈ s :=
  mem_nhds_iff (coe_ne_top _)

@[simp] theorem nhds_coe_eq (n : ℕ) : 𝓝 (n : ℕ∞) = 𝓟 ({(n : ℕ∞)}) := by
  ext; simp

theorem nhds_eq {n : ℕ∞} (hn : n ≠ ⊤) : 𝓝 n = 𝓟 {n} := by
  lift n to ℕ using hn; simp

@[simp] theorem nhds_top : 𝓝 (⊤ : ℕ∞) = ⨅ (a) (_ : a ≠ ⊤), 𝓟 (Ioi a) := by
  simp_rw [nhds_top_order, Ioi, lt_top_iff_ne_top]

theorem nhds_cast_cast {m n : ℕ} :
    𝓝 ((Nat.cast m : ℕ∞), (Nat.cast n : ℕ∞)) = (𝓝 (m, n)).map fun p : ℕ × ℕ ↦ (↑p.1, ↑p.2) :=
  ((openEmbedding_coe.prod openEmbedding_coe).map_nhds_eq (m, n)).symm

@[norm_cast]
theorem tendsto_coe {f : Filter α} {m : α → ℕ} {a : ℕ} :
    Tendsto (fun a ↦ (m a : ℕ∞)) f (𝓝 ↑a) ↔ Tendsto m f (𝓝 a) :=
  embedding_coe.tendsto_nhds_iff.symm

instance : ContinuousAdd ℕ∞ := by
  refine' ⟨continuous_iff_continuousAt.2 _⟩
  rintro ⟨_ | a, b⟩
  · exact tendsto_nhds_top_mono' continuousAt_fst fun p ↦ le_add_right le_rfl
  rcases b with (_ | b)
  · exact tendsto_nhds_top_mono' continuousAt_snd fun p ↦ le_add_left le_rfl
  simp only [ContinuousAt, WithTop.some_eq_coe, ENat.some_eq_coe]
  rw [nhds_cast_cast]
  simp_rw [tendsto_map'_iff, (· ∘ ·), ←Nat.cast_add, tendsto_coe, tendsto_add]

end Topology

-- instance : T5Space ℕ∞ := by infer_instance





protected theorem hasSum : HasSum f (⨆ s : Finset α, ∑ a in s, f a) :=
  tendsto_atTop_iSup fun _ _ ↦ Finset.sum_le_sum_of_subset

@[simp] protected theorem summable : Summable f :=
  ⟨_, ENat.hasSum⟩

example (f g : α → ℕ∞) : ∑' a, (f a + g a) = ∑' a, f a + ∑' a, g a := by
  rw [tsum_add (by simp) (by simp)]

section SMul

variable {α : Type*} [DecidableEq α] [AddMonoid α]


-- instance [CanonicallyOrderedAddCommMonoid α] : DistribSMul ℕ∞ (WithTop α) where
--   smul n a := n.rec (if a = 0 then 0 else ⊤) (fun i ↦ i • a)
--   smul_zero := by
--     rintro (rfl | n)
--     · change ite _ _ _ = _
--       rw [if_pos rfl]
--     exact smul_zero n
--   smul_add := by
--     rintro (rfl | n) a b
--     · by_cases hab : a + b = 0
--       · rw [add_eq_zero_iff]
--       change ite _ _ _ = (ite _ _ _) + (ite _ _ _)

  -- smul n a := n.rec (⊤ * a) (fun i ↦ i • a)

noncomputable example : SMul ℕ∞ ENNReal :=
  inferInstanceAs (SMul ℕ∞ (WithTop NNReal))

theorem WithTop.smul_top (a : WithTop α) (ha : a ≠ 0) : (⊤ : ℕ∞) • a = ⊤ :=
  WithTop.top_mul ha

@[simp] theorem WithTop.smul_cast (i : ℕ) (a : WithTop α) : (i : ℕ∞) • a = i • a := rfl

@[simp] theorem WithTop.smul_zero [SMulZeroClass ℕ α] (n : ℕ∞) : n • (0 : WithTop α) = 0 := by
  obtain (rfl | n) := n
  · change ⊤ * _ = _
    rw [WithTop.mul_def, if_pos (Or.inr rfl)]
  convert WithTop.smul_cast n (0 : WithTop α)
  simp

instance [CanonicallyOrderedAddCommMonoid α] : DistribSMul ℕ∞ (WithTop α) where
  smul_zero := by
    rintro (rfl | n)
    · change ⊤ * _ = _
      rw [WithTop.mul_def, if_pos (Or.inr rfl)]
    convert WithTop.smul_cast n (0 : WithTop α)
    simp
  smul_add := by
    rintro (rfl | n) x y
    · change ⊤ * _ = (⊤ * _) + (⊤ * _)
      obtain (rfl | hx) := (zero_le x).eq_or_lt
      rw [mul_zero]


    -- rw [WithTop.smul_top]



theorem foo (n m : ℕ∞) : n • m = n * m := by
  have foo' : lalal.smul (α := ℕ∞) n m = n * m
  · cases n
    rfl
    rw [← smul_eq_mul]
    cases m
    simp

end SMul
