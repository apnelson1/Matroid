import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Nat.PartENat
import Mathlib.Topology.Order.Basic
import Mathlib.Data.Set.Card
import Mathlib.Topology.Instances.ENNReal


open Set 

universe u v

open scoped BigOperators ENNReal 

class SummableForall (α : Type u) [TopologicalSpace α] [AddCommMonoid α] [SupSet α] where
  (hasSum : ∀ (ι : Type v) (f : ι → α), HasSum f (⨆ s : Finset ι, ∑ a in s, f a))

namespace ENat

instance : TopologicalSpace ℕ∞ :=
  Preorder.topology ℕ∞

instance : OrderTopology ℕ∞ := 
  ⟨rfl⟩  

variable {f : ι → ℕ∞}

protected theorem hasSum : HasSum f (⨆ s : Finset ι, ∑ a in s, f a) :=
  tendsto_atTop_iSup fun _ _ => Finset.sum_le_sum_of_subset

noncomputable instance : SummableForall ℕ∞ where 
  hasSum := fun _ _ ↦ tendsto_atTop_iSup fun _ _ ↦ Finset.sum_le_sum_of_subset

noncomputable instance : SummableForall ℝ≥0∞ where 
  hasSum := fun _ _ ↦ tendsto_atTop_iSup fun _ _ ↦ Finset.sum_le_sum_of_subset

theorem toSummable {α : Type u} {ι : Type v} [TopologicalSpace α] [AddCommMonoid α] [SupSet α] 
    [SummableForall α] (f : ι → α) : Summable f := 
  ⟨(⨆ s : Finset ι, ∑ a in s, f a), by 
    have h := ‹SummableForall α› 
    have' := h.hasSum


    -- exact ‹SummableForall α›.hasSum f 
    ⟩ 


-- instance : SummableForall ℕ∞ where
--   summable := @fun ι f ↦ by
--     have : HasSum f (⨆ s : Finset ι, ∑ a in s, f a) 
--     · exact tendsto_atTop_iSup fun _ _ => Finset.sum_le_sum_of_subset
--     exact ⟨_, this⟩ 

-- theorem hasSum {α ι : Type _} [CanonicallyLinearOrderedAddMonoid α] [CompleteLattice α] 
--     [TopologicalSpace α]  [OrderTopology α] {f : ι → α} : 
--     HasSum f (⨆ s : Finset ι, ∑ a in s, f a) := by 
--   sorry
  -- Proof should be 
  -- exact tendsto_atTop_iSup fun _ _ => Finset.sum_le_sum_of_subset

-- open Set 
-- import Mathlib.Topology.Instances.ENNReal
-- import Matroid.ForMathlib.card
-- import Mathlib.Data.Finset.Sum
-- import Mathlib.Data.ENat.Basic
-- import Mathlib.Data.Nat.PartENat

  -- apply tendsto_atTop_iSup
  -- intro s s' (h : s ⊆ s')
  -- convert @Finset.sum_le_sum_of_subset ι α _ f s s' h
  -- ext
  
  -- refine fun _ _ => Finset.sum_le_sum_of_subset 
  
  

-- theorem hasSum [CanonicallyOrderedAddMonoid α] [ConditionallyCompleteLinearOrderBot α]
--     [TopologicalSpace (WithTop α)] [h : OrderTopology (WithTop α)] {f : ι → WithTop α} : 
--     HasSum f (⨆ s : Finset ι, ∑ a in s, f a) := by
--   have :=  @tendsto_atTop_iSup (WithTop α) (Finset ι) _ _ _ 
--     (@LinearOrder.supConvergenceClass)
--   have := @tendsto_atTop_iSup (WithTop α) (Finset ι) _ _
  

namespace ENat

instance : TopologicalSpace ℕ∞ :=
  Preorder.topology ℕ∞

instance : OrderTopology ℕ∞ := 
  ⟨rfl⟩  

variable {f : α → ℕ∞}

protected theorem hasSum : HasSum f (⨆ s : Finset α, ∑ a in s, f a) :=
  tendsto_atTop_iSup fun _ _ => Finset.sum_le_sum_of_subset
  
-- protected theorem summable : Summable f := 
--   ⟨_, ENat.hasSum⟩ 

-- protected theorem tsum_eq_iSup_sum : ∑' a, f a = ⨆ s : Finset α, ∑ a in s, f a :=
--   ENat.hasSum.tsum_eq

  
-- section tsum
 
-- variable [HasSummable β] {f g : α → β}

-- @[norm_cast]
-- protected theorem hasSum_coe {f : α → ℝ≥0} {r : ℝ≥0} :
--     HasSum (fun a => (f a : β)) ↑r ↔ HasSum f r := by
--   simp only [HasSum, ← coe_finset_sum, tendsto_coe]

-- protected theorem tsum_coe_eq {f : α → ℝ≥0} (h : HasSum f r) : (∑' a, (f a : β)) = r :=
--   (ENNReal.hasSum_coe.2 h).tsum_eq

-- protected theorem coe_tsum {f : α → ℝ≥0} : Summable f → ↑(tsum f) = ∑' a, (f a : β)
--   | ⟨r, hr⟩ => by rw [hr.tsum_eq, ENNReal.tsum_coe_eq hr]

-- protected theorem hasSum : HasSum f (⨆ s : Finset α, ∑ a in s, f a) :=
--   tendsto_atTop_iSup fun _ _ => Finset.sum_le_sum_of_subset

-- @[simp]
-- protected theorem summable : Summable f :=
--   ⟨_, ENNReal.hasSum⟩

-- theorem tsum_coe_ne_top_iff_summable {f : β → ℝ≥0} : (∑' b, (f b : β)) ≠ ∞ ↔ Summable f := by
--   refine ⟨fun h => ?_, fun h => ENNReal.coe_tsum h ▸ ENNReal.coe_ne_top⟩
--   lift ∑' b, (f b : β) to ℝ≥0 using h with a ha
--   refine' ⟨a, ENNReal.hasSum_coe.1 _⟩
--   rw [ha]
--   exact ENNReal.summable.hasSum

-- protected theorem tsum_eq_iSup_sum : ∑' a, f a = ⨆ s : Finset α, ∑ a in s, f a :=
--   ENNReal.hasSum.tsum_eq

-- protected theorem tsum_eq_iSup_sum' {ι : Type _} (s : ι → Finset α) (hs : ∀ t, ∃ i, t ⊆ s i) :
--     ∑' a, f a = ⨆ i, ∑ a in s i, f a := by
--   rw [ENNReal.tsum_eq_iSup_sum]
--   symm
--   change ⨆ i : ι, (fun t : Finset α => ∑ a in t, f a) (s i) = ⨆ s : Finset α, ∑ a in s, f a
--   exact (Finset.sum_mono_set f).iSup_comp_eq hs

-- protected theorem tsum_sigma {β : α → Type _} (f : ∀ a, β a → β) :
--     ∑' p : Σa, β a, f p.1 p.2 = ∑' (a) (b), f a b :=
--   tsum_sigma' (fun _ => ENNReal.summable) ENNReal.summable

-- protected theorem tsum_sigma' {β : α → Type _} (f : (Σa, β a) → β) :
--     ∑' p : Σa, β a, f p = ∑' (a) (b), f ⟨a, b⟩ :=
--   tsum_sigma' (fun _ => ENNReal.summable) ENNReal.summable

-- protected theorem tsum_prod {f : α → β → β} : ∑' p : α × β, f p.1 p.2 = ∑' (a) (b), f a b :=
--   tsum_prod' ENNReal.summable fun _ => ENNReal.summable

-- protected theorem tsum_prod' {f : α × β → β} : ∑' p : α × β, f p = ∑' (a) (b), f (a, b) :=
--   tsum_prod' ENNReal.summable fun _ => ENNReal.summable

-- protected theorem tsum_comm {f : α → β → β} : ∑' a, ∑' b, f a b = ∑' b, ∑' a, f a b :=
--   tsum_comm' ENNReal.summable (fun _ => ENNReal.summable) fun _ => ENNReal.summable

-- protected theorem tsum_add : ∑' a, (f a + g a) = ∑' a, f a + ∑' a, g a :=
--   tsum_add ENNReal.summable ENNReal.summable

-- protected theorem tsum_le_tsum (h : ∀ a, f a ≤ g a) : ∑' a, f a ≤ ∑' a, g a :=
--   tsum_le_tsum h ENNReal.summable ENNReal.summable

-- protected theorem sum_le_tsum {f : α → β} (s : Finset α) : ∑ x in s, f x ≤ ∑' x, f x :=
--   sum_le_tsum s (fun _ _ => zero_le _) ENNReal.summable

-- protected theorem tsum_eq_iSup_nat' {f : ℕ → β} {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) :
--     ∑' i : ℕ, f i = ⨆ i : ℕ, ∑ a in Finset.range (N i), f a :=
--   ENNReal.tsum_eq_iSup_sum' _ fun t =>
--     let ⟨n, hn⟩ := t.exists_nat_subset_range
--     let ⟨k, _, hk⟩ := exists_le_of_tendsto_atTop hN 0 n
--     ⟨k, Finset.Subset.trans hn (Finset.range_mono hk)⟩

-- protected theorem tsum_eq_iSup_nat {f : ℕ → β} :
--     ∑' i : ℕ, f i = ⨆ i : ℕ, ∑ a in Finset.range i, f a :=
--   ENNReal.tsum_eq_iSup_sum' _ Finset.exists_nat_subset_range

-- protected theorem tsum_eq_liminf_sum_nat {f : ℕ → β} :
--     ∑' i, f i = liminf (fun n => ∑ i in Finset.range n, f i) atTop :=
--   ENNReal.summable.hasSum.tendsto_sum_nat.liminf_eq.symm

-- protected theorem tsum_eq_limsup_sum_nat {f : ℕ → β} :
--     ∑' i, f i = limsup (fun n => ∑ i in Finset.range n, f i) atTop :=
--   ENNReal.summable.hasSum.tendsto_sum_nat.limsup_eq.symm

-- protected theorem le_tsum (a : α) : f a ≤ ∑' a, f a :=
--   le_tsum' ENNReal.summable a

-- @[simp]
-- protected theorem tsum_eq_zero : ∑' i, f i = 0 ↔ ∀ i, f i = 0 :=
--   tsum_eq_zero_iff ENNReal.summable

-- protected theorem tsum_eq_top_of_eq_top : (∃ a, f a = ∞) → ∑' a, f a = ∞
--   | ⟨a, ha⟩ => top_unique <| ha ▸ ENNReal.le_tsum a

-- protected theorem lt_top_of_tsum_ne_top {a : α → β} (tsum_ne_top : ∑' i, a i ≠ ∞) (j : α) :
--     a j < ∞ := by
--   contrapose! tsum_ne_top with h
--   exact ENNReal.tsum_eq_top_of_eq_top ⟨j, top_unique h⟩

-- @[simp]
-- protected theorem tsum_top [Nonempty α] : ∑' _ : α, ∞ = ∞ :=
--   let ⟨a⟩ := ‹Nonempty α›
--   ENNReal.tsum_eq_top_of_eq_top ⟨a, rfl⟩

-- theorem tsum_const_eq_top_of_ne_zero {α : Type _} [Infinite α] {c : β} (hc : c ≠ 0) :
--     ∑' _ : α, c = ∞ := by
--   have A : Tendsto (fun n : ℕ => (n : β) * c) atTop (𝓝 (∞ * c)) := by
--     apply ENNReal.Tendsto.mul_const tendsto_nat_nhds_top
--     simp only [true_or_iff, top_ne_zero, Ne.def, not_false_iff]
--   have B : ∀ n : ℕ, (n : β) * c ≤ ∑' _ : α, c := fun n => by
--     rcases Infinite.exists_subset_card_eq α n with ⟨s, hs⟩
--     simpa [hs] using @ENNReal.sum_le_tsum α (fun _ => c) s
--   simpa [hc] using le_of_tendsto' A B

-- protected theorem ne_top_of_tsum_ne_top (h : ∑' a, f a ≠ ∞) (a : α) : f a ≠ ∞ := fun ha =>
--   h <| ENNReal.tsum_eq_top_of_eq_top ⟨a, ha⟩

-- protected theorem tsum_mul_left : ∑' i, a * f i = a * ∑' i, f i := by
--   by_cases hf : ∀ i, f i = 0
--   · simp [hf]
--   · rw [← ENNReal.tsum_eq_zero] at hf
--     have : Tendsto (fun s : Finset α => ∑ j in s, a * f j) atTop (𝓝 (a * ∑' i, f i)) := by
--       simp only [← Finset.mul_sum]
--       exact ENNReal.Tendsto.const_mul ENNReal.summable.hasSum (Or.inl hf)
--     exact HasSum.tsum_eq this

-- protected theorem tsum_mul_right : ∑' i, f i * a = (∑' i, f i) * a := by
--   simp [mul_comm, ENNReal.tsum_mul_left]

-- protected theorem tsum_const_smul {R} [SMul R β] [IsScalarTower R β β] (a : R) :
--     ∑' i, a • f i = a • ∑' i, f i := by
--   simpa only [smul_one_mul] using @ENNReal.tsum_mul_left _ (a • (1 : β)) _

-- @[simp]
-- theorem tsum_iSup_eq {α : Type _} (a : α) {f : α → β} : (∑' b : α, ⨆ _ : a = b, f b) = f a :=
--   (tsum_eq_single a fun _ h => by simp [h.symm]).trans <| by simp

-- theorem hasSum_iff_tendsto_nat {f : ℕ → β} (r : β) :
--     HasSum f r ↔ Tendsto (fun n : ℕ => ∑ i in Finset.range n, f i) atTop (𝓝 r) := by
--   refine' ⟨HasSum.tendsto_sum_nat, fun h => _⟩
--   rw [← iSup_eq_of_tendsto _ h, ← ENNReal.tsum_eq_iSup_nat]
--   · exact ENNReal.summable.hasSum
--   · exact fun s t hst => Finset.sum_le_sum_of_subset (Finset.range_subset.2 hst)

-- theorem tendsto_nat_tsum (f : ℕ → β) :
--     Tendsto (fun n : ℕ => ∑ i in Finset.range n, f i) atTop (𝓝 (∑' n, f n)) := by
--   rw [← hasSum_iff_tendsto_nat]
--   exact ENNReal.summable.hasSum

-- theorem toNNReal_apply_of_tsum_ne_top {α : Type _} {f : α → β} (hf : ∑' i, f i ≠ ∞) (x : α) :
--     (((ENNReal.toNNReal ∘ f) x : ℝ≥0) : β) = f x :=
--   coe_toNNReal <| ENNReal.ne_top_of_tsum_ne_top hf _

-- theorem summable_toNNReal_of_tsum_ne_top {α : Type _} {f : α → β} (hf : ∑' i, f i ≠ ∞) :
--     Summable (ENNReal.toNNReal ∘ f) := by
--   simpa only [← tsum_coe_ne_top_iff_summable, toNNReal_apply_of_tsum_ne_top hf] using hf

-- theorem tendsto_cofinite_zero_of_tsum_ne_top {α} {f : α → β} (hf : ∑' x, f x ≠ ∞) :
--     Tendsto f cofinite (𝓝 0) := by
--   have f_ne_top : ∀ n, f n ≠ ∞ := ENNReal.ne_top_of_tsum_ne_top hf
--   have h_f_coe : f = fun n => ((f n).toNNReal : ENNReal) :=
--     funext fun n => (coe_toNNReal (f_ne_top n)).symm
--   rw [h_f_coe, ← @coe_zero, tendsto_coe]
--   exact NNReal.tendsto_cofinite_zero_of_summable (summable_toNNReal_of_tsum_ne_top hf)

-- theorem tendsto_atTop_zero_of_tsum_ne_top {f : ℕ → β} (hf : ∑' x, f x ≠ ∞) :
--     Tendsto f atTop (𝓝 0) := by
--   rw [← Nat.cofinite_eq_atTop]
--   exact tendsto_cofinite_zero_of_tsum_ne_top hf

-- /-- The sum over the complement of a finset tends to `0` when the finset grows to cover the whole
-- space. This does not need a summability assumption, as otherwise all sums are zero. -/
-- theorem tendsto_tsum_compl_atTop_zero {α : Type _} {f : α → β} (hf : ∑' x, f x ≠ ∞) :
--     Tendsto (fun s : Finset α => ∑' b : { x // x ∉ s }, f b) atTop (𝓝 0) := by
--   lift f to α → ℝ≥0 using ENNReal.ne_top_of_tsum_ne_top hf
--   convert ENNReal.tendsto_coe.2 (NNReal.tendsto_tsum_compl_atTop_zero f)
--   rw [ENNReal.coe_tsum]
--   exact NNReal.summable_comp_injective (tsum_coe_ne_top_iff_summable.1 hf) Subtype.coe_injective

-- protected theorem tsum_apply {ι α : Type _} {f : ι → α → β} {x : α} :
--     (∑' i, f i) x = ∑' i, f i x :=
--   tsum_apply <| Pi.summable.mpr fun _ => ENNReal.summable

-- theorem tsum_sub {f : ℕ → β} {g : ℕ → β} (h₁ : ∑' i, g i ≠ ∞) (h₂ : g ≤ f) :
--     ∑' i, (f i - g i) = ∑' i, f i - ∑' i, g i :=
--   have : ∀ i, f i - g i + g i = f i := fun i => tsub_add_cancel_of_le (h₂ i)
--   ENNReal.eq_sub_of_add_eq h₁ <| by simp only [← ENNReal.tsum_add, this]

-- theorem tsum_comp_le_tsum_of_injective {f : α → β} (hf : Injective f) (g : β → β) :
--     ∑' x, g (f x) ≤ ∑' y, g y :=
--   tsum_le_tsum_of_inj f hf (fun _ _ => zero_le _) (fun _ => le_rfl) ENNReal.summable
--     ENNReal.summable

-- theorem tsum_le_tsum_comp_of_surjective {f : α → β} (hf : Surjective f) (g : β → β) :
--     ∑' y, g y ≤ ∑' x, g (f x) :=
--   calc ∑' y, g y = ∑' y, g (f (surjInv hf y)) := by simp only [surjInv_eq hf]
--   _ ≤ ∑' x, g (f x) := tsum_comp_le_tsum_of_injective (injective_surjInv hf) _

-- theorem tsum_mono_subtype (f : α → β) {s t : Set α} (h : s ⊆ t) :
--     ∑' x : s, f x ≤ ∑' x : t, f x :=
--   tsum_comp_le_tsum_of_injective (inclusion_injective h) _

-- theorem tsum_iUnion_le_tsum {ι : Type _} (f : α → β) (t : ι → Set α) :
--     ∑' x : ⋃ i, t i, f x ≤ ∑' i, ∑' x : t i, f x :=
--   calc ∑' x : ⋃ i, t i, f x ≤ ∑' x : Σ i, t i, f x.2 :=
--     tsum_le_tsum_comp_of_surjective (sigmaToiUnion_surjective t) _
--   _ = ∑' i, ∑' x : t i, f x := ENNReal.tsum_sigma' _

-- theorem tsum_biUnion_le_tsum {ι : Type _} (f : α → β) (s : Set ι) (t : ι → Set α) :
--     ∑' x : ⋃ i ∈ s , t i, f x ≤ ∑' i : s, ∑' x : t i, f x :=
--   calc ∑' x : ⋃ i ∈ s, t i, f x = ∑' x : ⋃ i : s, t i, f x := tsum_congr_subtype _ <| by simp
--   _ ≤ ∑' i : s, ∑' x : t i, f x := tsum_iUnion_le_tsum _ _

-- theorem tsum_biUnion_le {ι : Type _} (f : α → β) (s : Finset ι) (t : ι → Set α) :
--     ∑' x : ⋃ i ∈ s, t i, f x ≤ ∑ i in s, ∑' x : t i, f x :=
--   (tsum_biUnion_le_tsum f s.toSet t).trans_eq (Finset.tsum_subtype s fun i => ∑' x : t i, f x)

-- theorem tsum_iUnion_le {ι : Type _} [Fintype ι] (f : α → β) (t : ι → Set α) :
--     ∑' x : ⋃ i, t i, f x ≤ ∑ i, ∑' x : t i, f x := by
--   rw [← tsum_fintype]
--   exact tsum_iUnion_le_tsum f t

-- theorem tsum_union_le (f : α → β) (s t : Set α) :
--     ∑' x : ↑(s ∪ t), f x ≤ ∑' x : s, f x + ∑' x : t, f x :=
--   calc ∑' x : ↑(s ∪ t), f x = ∑' x : ⋃ b, cond b s t, f x := tsum_congr_subtype _ union_eq_iUnion
--   _ ≤ _ := by simpa using tsum_iUnion_le f (cond · s t)

-- theorem tsum_eq_add_tsum_ite {f : β → β} (b : β) :
--     ∑' x, f x = f b + ∑' x, ite (x = b) 0 (f x) :=
--   tsum_eq_add_tsum_ite' b ENNReal.summable

-- theorem tsum_add_one_eq_top {f : ℕ → β} (hf : ∑' n, f n = ∞) (hf0 : f 0 ≠ ∞) :
--     ∑' n, f (n + 1) = ∞ := by
--   rw [tsum_eq_zero_add' ENNReal.summable, add_eq_top] at hf
--   exact hf.resolve_left hf0

-- /-- A sum of extended nonnegative reals which is finite can have only finitely many terms
-- above any positive threshold.-/
-- theorem finite_const_le_of_tsum_ne_top {ι : Type _} {a : ι → β} (tsum_ne_top : ∑' i, a i ≠ ∞)
--     {ε : β} (ε_ne_zero : ε ≠ 0) : { i : ι | ε ≤ a i }.Finite := by
--   by_contra h
--   have := Infinite.to_subtype h
--   refine tsum_ne_top (top_unique ?_)
--   calc ⊤ = ∑' _ : { i | ε ≤ a i }, ε := (tsum_const_eq_top_of_ne_zero ε_ne_zero).symm
--   _ ≤ ∑' i, a i := tsum_le_tsum_of_inj (↑) Subtype.val_injective (fun _ _ => zero_le _)
--     (fun i => i.2) ENNReal.summable ENNReal.summable

-- /-- Markov's inequality for `Finset.card` and `tsum` in `β`. -/
-- theorem finset_card_const_le_le_of_tsum_le {ι : Type _} {a : ι → β} {c : β} (c_ne_top : c ≠ ∞)
--     (tsum_le_c : ∑' i, a i ≤ c) {ε : β} (ε_ne_zero : ε ≠ 0) :
--     ∃ hf : { i : ι | ε ≤ a i }.Finite, ↑hf.toFinset.card ≤ c / ε := by
--   have hf : { i : ι | ε ≤ a i }.Finite :=
--     finite_const_le_of_tsum_ne_top (ne_top_of_le_ne_top c_ne_top tsum_le_c) ε_ne_zero
--   refine ⟨hf, (ENNReal.le_div_iff_mul_le (.inl ε_ne_zero) (.inr c_ne_top)).2 ?_⟩
--   calc ↑hf.toFinset.card * ε = ∑ _i in hf.toFinset, ε := by rw [Finset.sum_const, nsmul_eq_mul]
--     _ ≤ ∑ i in hf.toFinset, a i := Finset.sum_le_sum fun i => hf.mem_toFinset.1
--     _ ≤ ∑' i, a i := ENNReal.sum_le_tsum _
--     _ ≤ c := tsum_le_c

--  end tsum
