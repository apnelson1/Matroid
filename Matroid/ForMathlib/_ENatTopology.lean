import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Nat.PartENat
import Mathlib.Topology.Order.Basic
import Mathlib.Data.Set.Card
import Mathlib.Topology.Instances.ENNReal
import Mathlib.Topology.Instances.Discrete
import Matroid.ForMathlib.Card


open Set WithTop Filter

universe u v

open scoped BigOperators ENNReal Topology Filter

theorem tsum_support_eq {α β : Type*} {f : α → β} [TopologicalSpace β] [AddCommMonoid β]
    [T2Space β] : ∑' (x : f.support), f x = ∑' x, f x := by
  simp [tsum_subtype]

theorem tsum_subtype_eq_tsum_inter_support {α β : Type*} {f : α → β} [TopologicalSpace β]
    [AddCommMonoid β] [T2Space β] {s : Set α} :
    ∑' (x : ↑(s ∩ f.support)), f x = ∑' (x : s), f x := by
  rw [tsum_congr (show ∀ (a : s), f a = (s.indicator f) a from _),
    tsum_congr ((show ∀ (a : ↑ (s ∩ f.support)), f a = (s.indicator f) a from _)),
    tsum_subtype_eq_of_support_subset (by simp), tsum_subtype_eq_of_support_subset (by simp)]
  · rintro ⟨a,ha⟩; simp [indicator_of_mem ha.1]
  rintro ⟨a, ha⟩
  simp [indicator_of_mem ha]

theorem tsum_subtype_eq_tsum_subtype {α β : Type*} {f : α → β} [TopologicalSpace β]
    [AddCommMonoid β] [T2Space β] {s t : Set α} (h : s ∩ f.support = t ∩ f.support) :
    ∑' (x : s), f x = ∑' (x : t), f x := by
  rw [←tsum_subtype_eq_tsum_inter_support, eq_comm, ←tsum_subtype_eq_tsum_inter_support, h]

namespace ENat

section basic

@[simp] theorem range_coe' : range ((↑) : ℕ → ℕ∞) = Iio ⊤ :=
  WithTop.range_coe

@[simp] theorem zero_ne_top : (0 : ℕ∞) ≠ ⊤ :=
  coe_toNat_eq_self.mp rfl

theorem eq_top_iff_forall_lt {n : ℕ∞} : n = ⊤ ↔ ∀ m : ℕ, m < n := by
  refine ⟨fun h m ↦ h ▸ coe_lt_top m ,fun h ↦ ?_⟩
  rw [← not_not (a := (n = ⊤)), ← Ne.def, ne_top_iff_exists]
  rintro ⟨a, rfl⟩
  exact (h a).ne rfl

def neTopEquivNat : { a : ℕ∞ | a ≠ ⊤ } ≃ ℕ where
  toFun x := ENat.toNat x
  invFun x := ⟨x, coe_ne_top x⟩
  left_inv := fun x ↦ Subtype.eq <| coe_toNat x.2
  right_inv := toNat_coe

theorem cinfi_ne_top [InfSet α] (f : ℕ∞ → α) : ⨅ x : { x : ℕ∞ // x ≠ ⊤ }, f x = ⨅ x : ℕ, f x :=
  Eq.symm <| neTopEquivNat.symm.surjective.iInf_congr _ fun _ => rfl

theorem iInf_ne_top [CompleteLattice α] (f : ℕ∞ → α) :
    ⨅ (x) (_ : x ≠ ⊤), f x = ⨅ x : ℕ, f x := by
  rw [iInf_subtype', cinfi_ne_top]


end basic

variable {n : ℕ∞}

instance : TopologicalSpace ℕ∞ := Preorder.topology ℕ∞

instance : OrderTopology ℕ∞ := ⟨rfl⟩

instance : T5Space ℕ∞ := inferInstance

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

@[simp] theorem nhds_cast_eq (n : ℕ) : 𝓝 (n : ℕ∞) = 𝓟 ({(n : ℕ∞)}) := by
  ext; simp

theorem nhds_eq (hn : n ≠ ⊤) : 𝓝 n = 𝓟 {n} := by
  lift n to ℕ using hn; simp

@[simp] theorem nhds_top : 𝓝 (⊤ : ℕ∞) = ⨅ (a) (_ : a ≠ ⊤), 𝓟 (Ioi a) := by
  simp_rw [nhds_top_order, Ioi, lt_top_iff_ne_top]

theorem nhds_top' : 𝓝 (⊤ : ℕ∞) = ⨅ (a : ℕ), 𝓟 (Ioi (a :ℕ∞)) := by
  refine nhds_top.trans <| iInf_ne_top _

@[simp] theorem nhds_cast_cast {m n : ℕ} :
    𝓝 ((m : ℕ∞), (n : ℕ∞)) = 𝓟 {((m : ℕ∞),(n : ℕ∞))} := by
  rw [((openEmbedding_coe.prod openEmbedding_coe).map_nhds_eq (m, n)).symm]
  simp

@[simp] theorem nhds_cast_top {m : ℕ} :
    𝓝 ((m : ℕ∞), ⊤) = (𝓟 {(m : ℕ∞)}) ×ˢ (⨅ (a : ℕ∞) (_ : a ≠ ⊤), 𝓟 (Ioi a)) := by
  rw [nhds_prod_eq, nhds_cast_eq, nhds_top, principal_singleton]

@[norm_cast]
theorem tendsto_coe {f : Filter α} {m : α → ℕ} {a : ℕ} :
    Tendsto (fun a ↦ (m a : ℕ∞)) f (𝓝 ↑a) ↔ Tendsto m f (𝓝 a) :=
  embedding_coe.tendsto_nhds_iff.symm

theorem tendsto_nhds_top_iff {m : α → ℕ∞} {f : Filter α} :
    Tendsto m f (𝓝 ⊤) ↔ ∀ x : ℕ, ∀ᶠ a in f, ↑x < m a := by
  simp only [nhds_top', tendsto_iInf, tendsto_principal, mem_Ioi]

protected theorem tendsto_mul (ha : a ≠ 0 ∨ b ≠ ⊤) (hb : b ≠ 0 ∨ a ≠ ⊤) :
    Tendsto (fun p : ℕ∞ × ℕ∞ => p.1 * p.2) (𝓝 (a, b)) (𝓝 (a * b)) := by
  clear n
  wlog h : b ≤ a with h'
  · specialize h' hb ha (not_le.1 h).le
    rw [nhds_swap a b, mul_comm, tendsto_map'_iff]
    convert h'; simp [mul_comm]
  obtain (rfl | ha') := eq_or_ne a ⊤
  · rw [top_mul (by simpa using hb), tendsto_nhds_top_iff]
    intro x
    have hforall : ∀ᶠ c : ℕ∞ × ℕ∞ in 𝓝 (⊤, b), ↑x < c.1 ∧ 0 < c.2
    · refine (lt_mem_nhds (show (x : ℕ∞) < ⊤ from WithTop.coe_lt_top x)).prod_nhds ?_
      obtain (rfl | hbne) := eq_or_ne b ⊤
      · apply lt_mem_nhds (by simp)
      lift b to ℕ using hbne
      rw [nhds_cast_eq, principal_singleton, eventually_pure, Nat.cast_pos,
        ← Nat.ne_zero_iff_zero_lt]
      simpa using hb
    refine hforall.mono ?_
    simp only [and_imp, Prod.forall, ← ENat.one_le_iff_pos]
    exact fun y z hy hz ↦ hy.trans_le <| le_mul_of_one_le_right' hz

  lift a to ℕ using ha'
  lift b to ℕ using (h.trans_lt (WithTop.coe_lt_top a)).ne
  rw [← Nat.cast_mul, nhds_cast_cast, nhds_cast_eq]
  simp

protected theorem Tendsto.mul {f : Filter α} {ma : α → ℕ∞} {mb : α → ℕ∞} {a b : ℕ∞}
    (hma : Tendsto ma f (𝓝 a)) (ha : a ≠ 0 ∨ b ≠ ⊤) (hmb : Tendsto mb f (𝓝 b))
    (hb : b ≠ 0 ∨ a ≠ ⊤) : Tendsto (fun a => ma a * mb a) f (𝓝 (a * b)) :=
  show Tendsto ((fun p : ℕ∞ × ℕ∞ => p.1 * p.2) ∘ fun a => (ma a, mb a)) f (𝓝 (a * b)) from
    Tendsto.comp (ENat.tendsto_mul ha hb) (hma.prod_mk_nhds hmb)

theorem _root_.ContinuousOn.Enat_mul [TopologicalSpace α] {f g : α → ℕ∞} {s : Set α}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) (h₁ : ∀ x ∈ s, f x ≠ 0 ∨ g x ≠ ⊤)
    (h₂ : ∀ x ∈ s, g x ≠ 0 ∨ f x ≠ ⊤) : ContinuousOn (fun x => f x * g x) s := fun x hx =>
  Tendsto.mul (hf x hx) (h₁ x hx) (hg x hx) (h₂ x hx)

theorem _root_.Continuous.Enat_mul [TopologicalSpace α] {f g : α → ℕ∞} (hf : Continuous f)
    (hg : Continuous g) (h₁ : ∀ x, f x ≠ 0 ∨ g x ≠ ⊤) (h₂ : ∀ x, g x ≠ 0 ∨ f x ≠ ⊤) :
    Continuous fun x => f x * g x :=
  continuous_iff_continuousAt.2 fun x ↦ Tendsto.mul hf.continuousAt (h₁ x) hg.continuousAt (h₂ x)

protected theorem Tendsto.const_mul {f : Filter α} {m : α → ℕ∞} {a b : ℕ∞}
    (hm : Tendsto m f (𝓝 b)) (hb : b ≠ 0 ∨ a ≠ ⊤) : Tendsto (fun b => a * m b) f (𝓝 (a * b)) :=
  by_cases (fun (this : a = 0) => by simp [this, tendsto_const_nhds]) fun ha : a ≠ 0 =>
    Tendsto.mul tendsto_const_nhds (Or.inl ha) hm hb

instance : ContinuousAdd ℕ∞ := by
  refine ⟨continuous_iff_continuousAt.2 ?_⟩
  rintro ⟨_ | a, b⟩
  · exact tendsto_nhds_top_mono' continuousAt_fst fun p ↦ le_add_right le_rfl
  rcases b with (_ | b)
  · exact tendsto_nhds_top_mono' continuousAt_snd fun p ↦ le_add_left le_rfl
  simp only [ContinuousAt, WithTop.some_eq_coe, ENat.some_eq_coe]
  rw [nhds_cast_cast, ← Nat.cast_add, nhds_cast_eq]
  simp only [principal_singleton, Nat.cast_add, tendsto_pure, eventually_pure]

section Sup

variable {ι : Sort*}

@[simp] theorem iSup_eq_zero {f : ι → ℕ∞} : ⨆ i, f i = 0 ↔ ∀ i, f i = 0 :=
  iSup_eq_bot

@[simp] theorem iSup_zero_eq_zero : ⨆ _ : ι, (0 : ℕ∞) = 0 := by
  simp

theorem mul_iSup (c : ℕ∞) (f : ι → ℕ∞) : c * (⨆ i, f i) = ⨆ i, (c * f i) := by
  by_cases hf : ∀ i, f i = 0
  · obtain rfl : f = fun _ ↦ 0
    exact funext hf
    simp only [mul_zero, iSup_zero_eq_zero]
  refine' (monotone_id.const_mul' _).map_iSup_of_continuousAt _ (mul_zero c)
  refine' ENat.Tendsto.const_mul tendsto_id (Or.inl _)
  exact mt iSup_eq_zero.1 hf

theorem iSup_mul (c : ℕ∞) (f : ι → ℕ∞) : (⨆ i, f i) * c = ⨆ i, (f i * c) := by
  simp_rw [mul_comm, mul_iSup]

end Sup

section tsum

variable {f g : α → ℕ∞}

protected theorem hasSum : HasSum f (⨆ s : Finset α, ∑ a in s, f a) :=
  tendsto_atTop_iSup fun _ _ ↦ Finset.sum_le_sum_of_subset

@[simp] protected theorem summable : Summable f :=
  ⟨_, ENat.hasSum⟩

@[norm_cast]
protected theorem hasSum_coe {f : α → ℕ} {r : ℕ} :
    HasSum (fun a ↦ (f a : ℕ∞)) ↑r ↔ HasSum f r := by
  simp_rw [HasSum, ← Nat.cast_sum, tendsto_coe]

protected theorem tsum_coe_eq {f : α → ℕ} (h : HasSum f r) : (∑' a, (f a : ℕ∞)) = r :=
  (ENat.hasSum_coe.2 h).tsum_eq

protected theorem coe_tsum {f : α → ℕ} : Summable f → ↑(tsum f) = ∑' a, (f a : ℕ∞)
  | ⟨r, hr⟩ => by rw [hr.tsum_eq, ENat.tsum_coe_eq hr]

protected theorem tsum_coe_ne_top_iff_summable {f : β → ℕ} :
    (∑' b, (f b : ℕ∞)) ≠ ⊤ ↔ Summable f := by
  refine ⟨fun h ↦ ?_, fun h ↦ ENat.coe_tsum h ▸ WithTop.coe_ne_top⟩
  lift ∑' b, (f b : ℕ∞) to ℕ using h with a ha
  refine' ⟨a, ENat.hasSum_coe.1 _⟩
  rw [ha]
  exact ENat.summable.hasSum

protected theorem tsum_eq_iSup_sum : ∑' x, f x = (⨆ s : Finset α, ∑ a in s, f a) :=
  ENat.hasSum.tsum_eq

protected theorem tsum_comm {f : α → β → ℕ∞} :
    ∑' (a : α) (b : β), f a b = ∑' (b : β) (a : α), f a b :=
  tsum_comm' ENat.summable (fun _ ↦ ENat.summable) fun _ ↦ ENat.summable

protected theorem tsum_prod {f : α → β → ℕ∞} : ∑' p : α × β, f p.1 p.2 = ∑' (a) (b), f a b :=
  tsum_prod' ENat.summable fun _ ↦ ENat.summable

protected theorem tsum_add : ∑' a, (f a + g a) = ∑' a, f a + ∑' a, g a :=
  tsum_add ENat.summable ENat.summable

protected theorem tsum_le_tsum (h : f ≤ g) : ∑' a, f a ≤ ∑' a, g a :=
  tsum_le_tsum h ENat.summable ENat.summable

protected theorem sum_le_tsum {f : α → ℕ∞} (s : Finset α) : ∑ x in s, f x ≤ ∑' x, f x :=
  sum_le_tsum s (fun _ _ ↦ zero_le _) ENat.summable

protected theorem le_tsum (a : α) : f a ≤ ∑' a, f a :=
  le_tsum' ENat.summable a

@[simp] protected theorem tsum_eq_zero : ∑' i, f i = 0 ↔ ∀ i, f i = 0 :=
  tsum_eq_zero_iff ENat.summable

protected theorem tsum_eq_top_of_eq_top : (∃ a, f a = ⊤) → ∑' a, f a = ⊤
  | ⟨a, ha⟩ => top_unique <| ha ▸ ENat.le_tsum a

-- sets

protected theorem tsum_union_disjoint {s t : Set α} (hd : Disjoint s t) :
    ∑' (x : ↑(s ∪ t)), f x = ∑' (x : s), f x + ∑' (x : t), f x :=
  tsum_union_disjoint hd ENat.summable ENat.summable

protected theorem tsum_le_of_subset {s t : Set α} (h : s ⊆ t) :
    ∑' (x : s), f x ≤ ∑' (x : t), f x := by
  rw [←diff_union_of_subset h, ENat.tsum_union_disjoint disjoint_sdiff_left]
  exact le_add_self

protected theorem tsum_le_union (s t : Set α) :
    ∑' (x : ↑(s ∪ t)), f (x : α) ≤ ∑' (x : s), f x + ∑' (x : t), f x := by
  rw [←diff_union_self, ENat.tsum_union_disjoint disjoint_sdiff_left]
  exact add_le_add_right (ENat.tsum_le_of_subset (diff_subset _ _)) _

protected theorem tsum_insert {s : Set α} {a : α} (h : a ∉ s) :
    ∑' (x : ↑(insert a s)), f x = f a + ∑' (x : s), f x := by
  rw [←singleton_union, ENat.tsum_union_disjoint, tsum_singleton]
  rwa [disjoint_singleton_left]

protected theorem tsum_sub (hfin : ∑' a, g a ≠ ⊤) (h : g ≤ f) :
    ∑' a, (f a - g a) = ∑' a, f a - ∑' a, g a := by
  rw [←WithTop.add_right_cancel_iff hfin, ←ENat.tsum_add,
    tsum_congr (fun i ↦ tsub_add_cancel_of_le (h i)), tsub_add_cancel_of_le (ENat.tsum_le_tsum h)]

theorem Finite.tsum_eq_top_iff {s : Set α} (hs : s.Finite) :
    ∑' (x : s), f x = ⊤ ↔ ∃ a ∈ s, f a = ⊤ := by
  refine' ⟨hs.induction_on (by simp) @fun a s' has' _ IH htop ↦ _,
    fun ⟨a, has, ha⟩ ↦ ENat.tsum_eq_top_of_eq_top ⟨⟨a, has⟩, ha⟩⟩
  obtain (ht | hne) := eq_or_ne (f a) ⊤
  · exact ⟨a, mem_insert _ _, ht⟩
  rw [ENat.tsum_insert has', WithTop.add_eq_top, or_iff_right hne] at htop
  obtain ⟨b, hbs, hbtop⟩ := IH htop
  exact ⟨b, Or.inr hbs, hbtop⟩

protected theorem tsum_one (s : Set α) : ∑' (_ : s), 1 = s.encard := by
  classical
  suffices hfin : ∀ (t : Set α), t.Finite → ∑' (_ : t), 1 = t.encard
  · obtain (hs | hs) := s.finite_or_infinite
    · rw [hfin s hs]
    rw [hs.encard_eq, eq_top_iff_forall_lt]
    intro m
    obtain ⟨t, ht⟩ := exists_subset_encard_eq (show m+1 ≤ s.encard by simp [hs.encard_eq])
    have htfin : t.Finite := finite_of_encard_eq_coe ht.2
    have hle := ENat.tsum_le_of_subset ht.1 (f := 1)
    simp_rw [Pi.one_apply, hfin _ htfin, ht.2, add_one_le_iff (coe_ne_top m)] at hle
    exact hle
  intro t ht
  change ∑' (x : t), (1 : α → ℕ∞) x = _
  rw [tsum_subtype, tsum_eq_sum (s := ht.toFinset) (by simp), eq_comm]
  simp_rw [indicator_apply, ← Finset.sum_filter]
  simp only [Finite.mem_toFinset, imp_self, implies_true, Finset.filter_true_of_mem,
    Pi.one_apply, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [← encard_coe_eq_coe_finsetCard, Finite.coe_toFinset]

protected theorem mul_tsum (c : ℕ∞) : c * ∑' a, f a = ∑' a, c * f a := by
  simp_rw [ENat.tsum_eq_iSup_sum, mul_iSup, Finset.mul_sum]

@[simp] protected theorem tsum_const (s : Set α) (c : ℕ∞) : ∑' (_ : s), c = c * s.encard := by
  rw [← ENat.tsum_one s, ENat.mul_tsum, mul_one]

protected theorem encard_support_le_tsum : f.support.encard ≤ ∑' x, f x := by
  classical
  rw [← ENat.tsum_one, tsum_subtype f.support (fun _ ↦ 1)]
  apply ENat.tsum_le_tsum
  intro a
  simp only [Function.mem_support, ne_eq, not_not]
  rw [indicator_apply]
  split_ifs with h
  · rwa [ENat.one_le_iff_ne_zero]
  apply zero_le

protected theorem tsum_eq_top_of_support_infinite (hf : f.support.Infinite) : ∑' a, f a = ⊤ := by
  have := ENat.encard_support_le_tsum (f := f)
  rwa [hf.encard_eq, top_le_iff] at this

protected theorem tsum_eq_top_iff : ∑' a, f a = ⊤ ↔ f.support.Infinite ∨ ∃ a, f a = ⊤ := by
  refine' ⟨fun h ↦ _, _⟩
  · rw [or_iff_not_imp_left, not_infinite]
    intro hfin
    rw [←tsum_support_eq, Finite.tsum_eq_top_iff hfin] at h
    obtain ⟨a, -, h⟩ := h
    exact ⟨a, h⟩
  rintro (h | h)
  · exact ENat.tsum_eq_top_of_support_infinite h
  exact ENat.tsum_eq_top_of_eq_top h

protected theorem tsum_inter_fiber_eq {ι} {s : Set ι} (f : ι → α) :
    ∑' (a : α), (s ∩ f ⁻¹' {a}).encard = s.encard := by
  classical
  obtain (hs | hs) := s.finite_or_infinite
  · refine hs.induction_on (by simp) (@fun a t hat _ IH ↦ ?_)
    have hcong : ∀ x,
      encard ((insert a t) ∩ f⁻¹' {x}) = encard (t ∩ f ⁻¹' {x}) + (if x = f a then 1 else 0)
    · intro x
      split_ifs with h
      · rw [insert_inter_of_mem, encard_insert_of_not_mem (fun ha ↦ hat ha.1)]; exact h.symm
      rw [insert_inter_of_not_mem, add_zero]; exact Ne.symm h
    rw [tsum_congr hcong, ENat.tsum_add, IH, encard_insert_of_not_mem hat, tsum_ite_eq]
  rw [hs.encard_eq, ENat.tsum_eq_top_iff]
  by_contra' h
  simp_rw [not_infinite, encard_ne_top_iff] at h
  apply hs
  refine' (h.1.biUnion (t := fun (a : α) ↦ s ∩ f ⁻¹' {a}) fun a _ ↦ by simp [h.2 a]).subset
    (fun x hx ↦ _)
  simp only [Function.mem_support, ne_eq, encard_eq_zero, mem_iUnion, mem_inter_iff, mem_preimage,
    mem_singleton_iff, exists_and_left, exists_prop, exists_eq_right', ←nonempty_iff_ne_empty,
    and_iff_right hx]
  exact ⟨x, hx, rfl⟩

protected theorem tsum_fiber_eq {ι} (f : ι → α) :
    ∑' (a : α), (f ⁻¹' {a}).encard = (univ : Set ι).encard := by
  rw [←ENat.tsum_inter_fiber_eq (s := univ) f, tsum_congr]; intro b; rw [univ_inter]



theorem ENat.tsum_iUnion_eq {ι : Type*} {s : ι → Set α} (hI : univ.PairwiseDisjoint s) :
    ∑' i, (s i).encard = (⋃ i, s i).encard := by
  set f := fun i ↦ (s i).encard
  obtain (hfin | hinf) := (f.support).finite_or_infinite
  · rw [tsum_eq_sum (s := hfin.toFinset) (f := fun i ↦ (s i).encard) (by simp), ← encard_biUnion]
    · congr; aesop
    exact fun i _ j _ hij t hti htj ↦ (hI (mem_univ i) (mem_univ j) hij) hti htj
  rw [ENat.tsum_eq_top_of_support_infinite hinf, eq_comm, encard_eq_top_iff]

  -- have := hinf.image


  -- obtain (hfin | hinf) := (⋃ i, s i).finite_or_infinite
  -- · have hsupp : ((fun i ↦ (s i).encard).support).Finite
  --   · sorry



-- theorem ENat.tsum_sUnion_eq {c : Set (Set α)} (hc : c.PairwiseDisjoint id) :
--     ∑' (t : c), (t : Set α).encard = (⋃₀ c).encard := by
--   obtain (hs | hs) := c.finite_or_infinite
--   · have := hs.fintype
--     rw [tsum_fintype, encard_iUnion]



  -- obtain (hs | hs) := c.finite_or_infinite
  -- · refine hs.induction_on (by rw [sUnion_empty]; simp) (@fun a t hat _ IH ↦ ?_)
  --   rw [ENat.tsum_insert hat, IH, sUnion_insert, encard_union_eq]
  --   sorry


  -- have : ∀ (x : ⋃₀ c), ∃ (t : c), (x : α) ∈ (t : Set α)
  -- · sorry

  -- choose f hf using this
  -- rw [←encard_univ_coe, ←ENat.tsum_fiber_eq f, tsum_congr]
  -- rintro ⟨b, hb⟩
  -- rw [←Subtype.val_injective.encard_image]
  -- congr
  -- ext x
  -- simp only [mem_image, mem_preimage, mem_singleton_iff, Subtype.exists, mem_sUnion,
  --   exists_and_right, exists_eq_right]
  -- refine' ⟨fun h ↦ ⟨b, _⟩, fun h ↦ _⟩
  -- ·  simp











--   rw [←tsum_one, tsum_congr (fun (t : c) ↦ (tsum_one (t : Set α)).symm)]







  -- · simp
  -- · rw [tsum_subtype]
    -- simp_rw [ENat.tsum_eq_iSup_sum, htop, Finset.sum_const]
    -- rw [WithTop.top_mul hc, iSup_eq_top]
    -- intro b hb
    -- obtain ⟨t, hts, ht⟩ := exists_subset_encard_eq ((le_top (a := b+1)).trans_eq htop.symm)



    -- refine' ⟨((↑) : s → α)⁻¹' ht.to_Finset, _⟩





end tsum



-- theorem isOpen_ne_top : IsOpen {a : ℕ∞ | a ≠ ⊤} := isOpen_ne


-- theorem isOpen_top_not_mem (s : set ℕ∞) :


-- theorem WithTop.induced [Preorder β] (t : TopologicalSpace β) [OrderTopology β]
--     (tw : TopologicalSpace (WithTop β)) [OrderTopology (WithTop β)] :
--     t = TopologicalSpace.induced (↑) tw := by
--   ext s
--   simp_rw [isOpen_induced_eq, mem_image, mem_setOf]




-- theorem WithTop.inducing_coe {β : Type*} [Preorder β] [TopologicalSpace β] [OrderTopology β]
--     [TopologicalSpace (WithTop β)] [OrderTopology (WithTop β)] :
--     Inducing ((↑) : β → WithTop β) := by
--   rw [inducing_iff]

-- theorem WithTop.embedding_coe {β : Type*} [Preorder β] [TopologicalSpace β] [OrderTopology β]
--     [TopologicalSpace (WithTop β)] [OrderTopology (WithTop β)] :
--     Embedding ((↑) : β → WithTop β) := by



-- theorem foo_tendsto_coe {α β : Type*} [Preorder β] [TopologicalSpace β] [OrderTopology β]
--   [TopologicalSpace (WithTop β)] [OrderTopology (WithTop β)] {f : Filter α} {m : α → β} {a : β} :
--     Filter.Tendsto (fun a ↦ (m a : WithTop β)) f (nhds (a : WithTop β)) ↔ Filter.Tendsto m f (nhds a) := by
--   have := embedding_coe.tendsto_nhds_iff







-- example {α : Type*} [OrderedAddCommMonoid α] [TopologicalSpace α] [OrderTopology α]
--   [ContinuousAdd α] [TopologicalSpace (WithTop α)] [OrderTopology (WithTop α)] :
--     ContinuousAdd (WithTop α) := by
--   apply continuousAdd_of_comm_of_nhds_zero







-- protected theorem hasSum : HasSum f (⨆ s : Finset ι, ∑ a in s, f a) :=
--   tendsto_atTop_iSup fun _ _ ↦ Finset.sum_le_sum_of_subset

-- protected theorem summable : Summable f :=
--   ⟨_, ENat.hasSum⟩

-- theorem ENat.tsum_eq_iSup_sum : ∑' x, f x = (⨆ s : Finset ι, ∑ a in s, f a) :=
--   ENat.hasSum.tsum_eq

-- theorem ENat.tsum_comm {f : α → β → ℕ∞} :
--     ∑' (a : α) (b : β), f a b = ∑' (b : β) (a : α), f a b := by
--   have : ContinuousAdd ℕ∞
--   · exact
--     Enat.instContinuousAddEnatInstTopologicalSpaceEnatToAddToDistribToNonUnitalNonAssocSemiringToNonAssocSemiringToSemiringToOrderedSemiringToOrderedCommSemiringInstCanonicallyOrderedCommSemiringEnat




-- protected theorem tsum_eq_iSup_sum : ∑' a, f a = ⨆ s : Finset α, ∑ a in s, f a :=
--   ENat.hasSum.tsum_eq


-- section tsum

-- variable [HasSummable β] {f g : α → β}

-- @[norm_cast]
-- protected theorem hasSum_coe {f : α → ℝ≥0} {r : ℝ≥0} :
--     HasSum (fun a ↦ (f a : β)) ↑r ↔ HasSum f r := by
--   simp only [HasSum, ← coe_finset_sum, tendsto_coe]

-- protected theorem tsum_coe_eq {f : α → ℝ≥0} (h : HasSum f r) : (∑' a, (f a : β)) = r :=
--   (Enat.hasSum_coe.2 h).tsum_eq

-- protected theorem coe_tsum {f : α → ℝ≥0} : Summable f → ↑(tsum f) = ∑' a, (f a : β)
--   | ⟨r, hr⟩ ↦ by rw [hr.tsum_eq, Enat.tsum_coe_eq hr]

-- protected theorem hasSum : HasSum f (⨆ s : Finset α, ∑ a in s, f a) :=
--   tendsto_atTop_iSup fun _ _ ↦ Finset.sum_le_sum_of_subset

-- @[simp]
-- protected theorem summable : Summable f :=
--   ⟨_, Enat.hasSum⟩

-- theorem tsum_coe_ne_top_iff_summable {f : β → ℝ≥0} : (∑' b, (f b : β)) ≠ ∞ ↔ Summable f := by
--   refine ⟨fun h ↦ ?_, fun h ↦ Enat.coe_tsum h ▸ Enat.coe_ne_top⟩
--   lift ∑' b, (f b : β) to ℝ≥0 using h with a ha
--   refine' ⟨a, Enat.hasSum_coe.1 _⟩
--   rw [ha]
--   exact ENat.summable.hasSum

-- protected theorem tsum_eq_iSup_sum : ∑' a, f a = ⨆ s : Finset α, ∑ a in s, f a :=
--   Enat.hasSum.tsum_eq

-- protected theorem tsum_eq_iSup_sum' {ι : Type*} (s : ι → Finset α) (hs : ∀ t, ∃ i, t ⊆ s i) :
--     ∑' a, f a = ⨆ i, ∑ a in s i, f a := by
--   rw [Enat.tsum_eq_iSup_sum]
--   symm
--   change ⨆ i : ι, (fun t : Finset α ↦ ∑ a in t, f a) (s i) = ⨆ s : Finset α, ∑ a in s, f a
--   exact (Finset.sum_mono_set f).iSup_comp_eq hs

-- protected theorem tsum_sigma {β : α → Type*} (f : ∀ a, β a → β) :
--     ∑' p : Σa, β a, f p.1 p.2 = ∑' (a) (b), f a b :=
--   tsum_sigma' (fun _ ↦ ENat.summable) ENat.summable

-- protected theorem tsum_sigma' {β : α → Type*} (f : (Σa, β a) → β) :
--     ∑' p : Σa, β a, f p = ∑' (a) (b), f ⟨a, b⟩ :=
--   tsum_sigma' (fun _ ↦ ENat.summable) ENat.summable

-- protected theorem tsum_prod {f : α → β → β} : ∑' p : α × β, f p.1 p.2 = ∑' (a) (b), f a b :=
--   tsum_prod' ENat.summable fun _ ↦ ENat.summable

-- protected theorem tsum_prod' {f : α × β → β} : ∑' p : α × β, f p = ∑' (a) (b), f (a, b) :=
--   tsum_prod' ENat.summable fun _ ↦ ENat.summable

-- protected theorem tsum_comm {f : α → β → β} : ∑' a, ∑' b, f a b = ∑' b, ∑' a, f a b :=
--   tsum_comm' ENat.summable (fun _ ↦ ENat.summable) fun _ ↦ ENat.summable

-- protected theorem tsum_add : ∑' a, (f a + g a) = ∑' a, f a + ∑' a, g a :=
--   tsum_add ENat.summable ENat.summable

-- protected theorem tsum_le_tsum (h : ∀ a, f a ≤ g a) : ∑' a, f a ≤ ∑' a, g a :=
--   tsum_le_tsum h ENat.summable ENat.summable

-- protected theorem sum_le_tsum {f : α → β} (s : Finset α) : ∑ x in s, f x ≤ ∑' x, f x :=
--   sum_le_tsum s (fun _ _ ↦ zero_le _) ENat.summable

-- protected theorem tsum_eq_iSup_nat' {f : ℕ → β} {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) :
--     ∑' i : ℕ, f i = ⨆ i : ℕ, ∑ a in Finset.range (N i), f a :=
--   Enat.tsum_eq_iSup_sum' _ fun t ↦
--     let ⟨n, hn⟩ := t.exists_nat_subset_range
--     let ⟨k, _, hk⟩ := exists_le_of_tendsto_atTop hN 0 n
--     ⟨k, Finset.Subset.trans hn (Finset.range_mono hk)⟩

-- protected theorem tsum_eq_iSup_nat {f : ℕ → β} :
--     ∑' i : ℕ, f i = ⨆ i : ℕ, ∑ a in Finset.range i, f a :=
--   Enat.tsum_eq_iSup_sum' _ Finset.exists_nat_subset_range

-- protected theorem tsum_eq_liminf_sum_nat {f : ℕ → β} :
--     ∑' i, f i = liminf (fun n ↦ ∑ i in Finset.range n, f i) atTop :=
--   ENat.summable.hasSum.tendsto_sum_nat.liminf_eq.symm

-- protected theorem tsum_eq_limsup_sum_nat {f : ℕ → β} :
--     ∑' i, f i = limsup (fun n ↦ ∑ i in Finset.range n, f i) atTop :=
--   ENat.summable.hasSum.tendsto_sum_nat.limsup_eq.symm

-- protected theorem le_tsum (a : α) : f a ≤ ∑' a, f a :=
--   le_tsum' ENat.summable a

-- @[simp]
-- protected theorem tsum_eq_zero : ∑' i, f i = 0 ↔ ∀ i, f i = 0 :=
--   tsum_eq_zero_iff ENat.summable

-- protected theorem tsum_eq_top_of_eq_top : (∃ a, f a = ∞) → ∑' a, f a = ∞
--   | ⟨a, ha⟩ ↦ top_unique <| ha ▸ Enat.le_tsum a

-- protected theorem lt_top_of_tsum_ne_top {a : α → β} (tsum_ne_top : ∑' i, a i ≠ ∞) (j : α) :
--     a j < ∞ := by
--   contrapose! tsum_ne_top with h
--   exact Enat.tsum_eq_top_of_eq_top ⟨j, top_unique h⟩

-- @[simp]
-- protected theorem tsum_top [Nonempty α] : ∑' _ : α, ∞ = ∞ :=
--   let ⟨a⟩ := ‹Nonempty α›
--   Enat.tsum_eq_top_of_eq_top ⟨a, rfl⟩

-- theorem tsum_const_eq_top_of_ne_zero {α : Type*} [Infinite α] {c : β} (hc : c ≠ 0) :
--     ∑' _ : α, c = ∞ := by
--   have A : Tendsto (fun n : ℕ ↦ (n : β) * c) atTop (𝓝 (∞ * c)) := by
--     apply Enat.Tendsto.mul_const tendsto_nat_nhds_top
--     simp only [true_or_iff, top_ne_zero, Ne.def, not_false_iff]
--   have B : ∀ n : ℕ, (n : β) * c ≤ ∑' _ : α, c := fun n ↦ by
--     rcases Infinite.exists_subset_card_eq α n with ⟨s, hs⟩
--     simpa [hs] using @Enat.sum_le_tsum α (fun _ ↦ c) s
--   simpa [hc] using le_of_tendsto' A B

-- protected theorem ne_top_of_tsum_ne_top (h : ∑' a, f a ≠ ∞) (a : α) : f a ≠ ∞ := fun ha ↦
--   h <| Enat.tsum_eq_top_of_eq_top ⟨a, ha⟩

-- protected theorem tsum_mul_left : ∑' i, a * f i = a * ∑' i, f i := by
--   by_cases hf : ∀ i, f i = 0
--   · simp [hf]
--   · rw [← Enat.tsum_eq_zero] at hf
--     have : Tendsto (fun s : Finset α ↦ ∑ j in s, a * f j) atTop (𝓝 (a * ∑' i, f i)) := by
--       simp only [← Finset.mul_sum]
--       exact Enat.Tendsto.const_mul ENat.summable.hasSum (Or.inl hf)
--     exact HasSum.tsum_eq this

-- protected theorem tsum_mul_right : ∑' i, f i * a = (∑' i, f i) * a := by
--   simp [mul_comm, Enat.tsum_mul_left]

-- protected theorem tsum_const_smul {R} [SMul R β] [IsScalarTower R β β] (a : R) :
--     ∑' i, a • f i = a • ∑' i, f i := by
--   simpa only [smul_one_mul] using @Enat.tsum_mul_left _ (a • (1 : β)) _

-- @[simp]
-- theorem tsum_iSup_eq {α : Type*} (a : α) {f : α → β} : (∑' b : α, ⨆ _ : a = b, f b) = f a :=
--   (tsum_eq_single a fun _ h ↦ by simp [h.symm]).trans <| by simp

-- theorem hasSum_iff_tendsto_nat {f : ℕ → β} (r : β) :
--     HasSum f r ↔ Tendsto (fun n : ℕ ↦ ∑ i in Finset.range n, f i) atTop (𝓝 r) := by
--   refine' ⟨HasSum.tendsto_sum_nat, fun h ↦ _⟩
--   rw [← iSup_eq_of_tendsto _ h, ← Enat.tsum_eq_iSup_nat]
--   · exact ENat.summable.hasSum
--   · exact fun s t hst ↦ Finset.sum_le_sum_of_subset (Finset.range_subset.2 hst)

-- theorem tendsto_nat_tsum (f : ℕ → β) :
--     Tendsto (fun n : ℕ ↦ ∑ i in Finset.range n, f i) atTop (𝓝 (∑' n, f n)) := by
--   rw [← hasSum_iff_tendsto_nat]
--   exact ENat.summable.hasSum

-- theorem toNNReal_apply_of_tsum_ne_top {α : Type*} {f : α → β} (hf : ∑' i, f i ≠ ∞) (x : α) :
--     (((Enat.toNNReal ∘ f) x : ℝ≥0) : β) = f x :=
--   coe_toNNReal <| Enat.ne_top_of_tsum_ne_top hf _

-- theorem summable_toNNReal_of_tsum_ne_top {α : Type*} {f : α → β} (hf : ∑' i, f i ≠ ∞) :
--     Summable (Enat.toNNReal ∘ f) := by
--   simpa only [← tsum_coe_ne_top_iff_summable, toNNReal_apply_of_tsum_ne_top hf] using hf

-- theorem tendsto_cofinite_zero_of_tsum_ne_top {α} {f : α → β} (hf : ∑' x, f x ≠ ∞) :
--     Tendsto f cofinite (𝓝 0) := by
--   have f_ne_top : ∀ n, f n ≠ ∞ := Enat.ne_top_of_tsum_ne_top hf
--   have h_f_coe : f = fun n ↦ ((f n).toNNReal : Enat) :=
--     funext fun n ↦ (coe_toNNReal (f_ne_top n)).symm
--   rw [h_f_coe, ← @coe_zero, tendsto_coe]
--   exact NNReal.tendsto_cofinite_zero_of_summable (summable_toNNReal_of_tsum_ne_top hf)

-- theorem tendsto_atTop_zero_of_tsum_ne_top {f : ℕ → β} (hf : ∑' x, f x ≠ ∞) :
--     Tendsto f atTop (𝓝 0) := by
--   rw [← Nat.cofinite_eq_atTop]
--   exact tendsto_cofinite_zero_of_tsum_ne_top hf

-- /-- The sum over the complement of a finset tends to `0` when the finset grows to cover the whole
-- space. This does not need a summability assumption, as otherwise all sums are zero. -/
-- theorem tendsto_tsum_compl_atTop_zero {α : Type*} {f : α → β} (hf : ∑' x, f x ≠ ∞) :
--     Tendsto (fun s : Finset α ↦ ∑' b : { x // x ∉ s }, f b) atTop (𝓝 0) := by
--   lift f to α → ℝ≥0 using Enat.ne_top_of_tsum_ne_top hf
--   convert Enat.tendsto_coe.2 (NNReal.tendsto_tsum_compl_atTop_zero f)
--   rw [Enat.coe_tsum]
--   exact NNReal.summable_comp_injective (tsum_coe_ne_top_iff_summable.1 hf) Subtype.coe_injective

-- protected theorem tsum_apply {ι α : Type*} {f : ι → α → β} {x : α} :
--     (∑' i, f i) x = ∑' i, f i x :=
--   tsum_apply <| Pi.summable.mpr fun _ ↦ ENat.summable

-- theorem tsum_sub {f : ℕ → β} {g : ℕ → β} (h₁ : ∑' i, g i ≠ ∞) (h₂ : g ≤ f) :
--     ∑' i, (f i - g i) = ∑' i, f i - ∑' i, g i :=
--   have : ∀ i, f i - g i + g i = f i := fun i ↦ tsub_add_cancel_of_le (h₂ i)
--   Enat.eq_sub_of_add_eq h₁ <| by simp only [← Enat.tsum_add, this]

-- theorem tsum_comp_le_tsum_of_injective {f : α → β} (hf : Injective f) (g : β → β) :
--     ∑' x, g (f x) ≤ ∑' y, g y :=
--   tsum_le_tsum_of_inj f hf (fun _ _ ↦ zero_le _) (fun _ ↦ le_rfl) ENat.summable
--     ENat.summable

-- theorem tsum_le_tsum_comp_of_surjective {f : α → β} (hf : Surjective f) (g : β → β) :
--     ∑' y, g y ≤ ∑' x, g (f x) :=
--   calc ∑' y, g y = ∑' y, g (f (surjInv hf y)) := by simp only [surjInv_eq hf]
--   _ ≤ ∑' x, g (f x) := tsum_comp_le_tsum_of_injective (injective_surjInv hf) _

-- theorem tsum_mono_subtype (f : α → β) {s t : Set α} (h : s ⊆ t) :
--     ∑' x : s, f x ≤ ∑' x : t, f x :=
--   tsum_comp_le_tsum_of_injective (inclusion_injective h) _

-- theorem tsum_iUnion_le_tsum {ι : Type*} (f : α → β) (t : ι → Set α) :
--     ∑' x : ⋃ i, t i, f x ≤ ∑' i, ∑' x : t i, f x :=
--   calc ∑' x : ⋃ i, t i, f x ≤ ∑' x : Σ i, t i, f x.2 :=
--     tsum_le_tsum_comp_of_surjective (sigmaToiUnion_surjective t) _
--   _ = ∑' i, ∑' x : t i, f x := Enat.tsum_sigma' _

-- theorem tsum_biUnion_le_tsum {ι : Type*} (f : α → β) (s : Set ι) (t : ι → Set α) :
--     ∑' x : ⋃ i ∈ s , t i, f x ≤ ∑' i : s, ∑' x : t i, f x :=
--   calc ∑' x : ⋃ i ∈ s, t i, f x = ∑' x : ⋃ i : s, t i, f x := tsum_congr_subType* <| by simp
--   _ ≤ ∑' i : s, ∑' x : t i, f x := tsum_iUnion_le_tsum _ _

-- theorem tsum_biUnion_le {ι : Type*} (f : α → β) (s : Finset ι) (t : ι → Set α) :
--     ∑' x : ⋃ i ∈ s, t i, f x ≤ ∑ i in s, ∑' x : t i, f x :=
--   (tsum_biUnion_le_tsum f s.toSet t).trans_eq (Finset.tsum_subtype s fun i ↦ ∑' x : t i, f x)

-- theorem tsum_iUnion_le {ι : Type*} [Fintype ι] (f : α → β) (t : ι → Set α) :
--     ∑' x : ⋃ i, t i, f x ≤ ∑ i, ∑' x : t i, f x := by
--   rw [← tsum_fintype]
--   exact tsum_iUnion_le_tsum f t

-- theorem tsum_union_le (f : α → β) (s t : Set α) :
--     ∑' x : ↑(s ∪ t), f x ≤ ∑' x : s, f x + ∑' x : t, f x :=
--   calc ∑' x : ↑(s ∪ t), f x = ∑' x : ⋃ b, cond b s t, f x := tsum_congr_subType* union_eq_iUnion
--   _ ≤ _ := by simpa using tsum_iUnion_le f (cond · s t)

-- theorem tsum_eq_add_tsum_ite {f : β → β} (b : β) :
--     ∑' x, f x = f b + ∑' x, ite (x = b) 0 (f x) :=
--   tsum_eq_add_tsum_ite' b ENat.summable

-- theorem tsum_add_one_eq_top {f : ℕ → β} (hf : ∑' n, f n = ∞) (hf0 : f 0 ≠ ∞) :
--     ∑' n, f (n + 1) = ∞ := by
--   rw [tsum_eq_zero_add' ENat.summable, add_eq_top] at hf
--   exact hf.resolve_left hf0

-- /-- A sum of extended nonnegative reals which is finite can have only finitely many terms
-- above any positive threshold.-/
-- theorem finite_const_le_of_tsum_ne_top {ι : Type*} {a : ι → β} (tsum_ne_top : ∑' i, a i ≠ ∞)
--     {ε : β} (ε_ne_zero : ε ≠ 0) : { i : ι | ε ≤ a i }.Finite := by
--   by_contra h
--   have := Infinite.to_subtype h
--   refine tsum_ne_top (top_unique ?_)
--   calc ⊤ = ∑' _ : { i | ε ≤ a i }, ε := (tsum_const_eq_top_of_ne_zero ε_ne_zero).symm
--   _ ≤ ∑' i, a i := tsum_le_tsum_of_inj (↑) Subtype.val_injective (fun _ _ ↦ zero_le _)
--     (fun i ↦ i.2) ENat.summable ENat.summable

-- /-- Markov's inequality for `Finset.card` and `tsum` in `β`. -/
-- theorem finset_card_const_le_le_of_tsum_le {ι : Type*} {a : ι → β} {c : β} (c_ne_top : c ≠ ∞)
--     (tsum_le_c : ∑' i, a i ≤ c) {ε : β} (ε_ne_zero : ε ≠ 0) :
--     ∃ hf : { i : ι | ε ≤ a i }.Finite, ↑hf.toFinset.card ≤ c / ε := by
--   have hf : { i : ι | ε ≤ a i }.Finite :=
--     finite_const_le_of_tsum_ne_top (ne_top_of_le_ne_top c_ne_top tsum_le_c) ε_ne_zero
--   refine ⟨hf, (Enat.le_div_iff_mul_le (.inl ε_ne_zero) (.inr c_ne_top)).2 ?_⟩
--   calc ↑hf.toFinset.card * ε = ∑ _i in hf.toFinset, ε := by rw [Finset.sum_const, nsmul_eq_mul]
--     _ ≤ ∑ i in hf.toFinset, a i := Finset.sum_le_sum fun i ↦ hf.mem_toFinset.1
--     _ ≤ ∑' i, a i := Enat.sum_le_tsum _
--     _ ≤ c := tsum_le_c

--  end tsum
