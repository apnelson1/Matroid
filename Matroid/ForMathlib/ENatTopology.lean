import Mathlib.Data.ENat.Basic
import Mathlib.Data.Set.Card
import Mathlib.Topology.Instances.ENNReal
import Mathlib.Topology.Instances.Discrete
import Matroid.ForMathlib.Card


open Set Function WithTop Filter

universe u v

variable {α β ι : Type*} {s : Set α}

open scoped BigOperators ENNReal Topology Filter

theorem tsum_support_eq {α β : Type*} {f : α → β} [TopologicalSpace β] [AddCommMonoid β]
    [T2Space β] : ∑' (x : f.support), f x = ∑' x, f x := by
  simp [tsum_subtype]

theorem tsum_inter_support_eq_tsum_subtype {α β : Type*} {f : α → β} [TopologicalSpace β]
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
  rw [← tsum_inter_support_eq_tsum_subtype, eq_comm, ← tsum_inter_support_eq_tsum_subtype, h]

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

/-- The set of `ENat` that are not `⊤` is equivalent to `ℕ`. -/
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

theorem indicator_support_le (f : α → ℕ∞) (i : α) : indicator (support f) 1 i ≤ f i := by
  by_cases hi : i ∈ support f
  · rwa [indicator_apply_eq_self.2 (fun h ↦ (h hi).elim), Pi.one_apply, ENat.one_le_iff_ne_zero]
  rw [indicator_apply_eq_zero.2 (fun h ↦ (hi h).elim)]
  apply zero_le

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
  rw [← openEmbedding_coe.open_iff_image_open]; exact trivial

theorem isOpen_singleton {x : ℕ∞} (hx : x ≠ ⊤) : IsOpen {x} := by
  lift x to ℕ using hx
  rw [← image_singleton, ← openEmbedding_coe.open_iff_image_open]
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

@[simp] theorem mem_nhds_coe_iff (n : ℕ) {s : Set ℕ∞} : s ∈ 𝓝 (n : ℕ∞) ↔ (n : ℕ∞) ∈ s :=
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

protected theorem tendsto_mul {a b : ℕ∞} (ha : a ≠ 0 ∨ b ≠ ⊤) (hb : b ≠ 0 ∨ a ≠ ⊤) :
    Tendsto (fun p : ℕ∞ × ℕ∞ => p.1 * p.2) (𝓝 (a, b)) (𝓝 (a * b)) := by
  clear n ι β s α
  wlog h : b ≤ a with h'
  · specialize h' hb ha (not_le.1 h).le
    rw [nhds_swap a b, mul_comm, tendsto_map'_iff]
    convert h'; simp [mul_comm]
  obtain (rfl | ha') := eq_or_ne a ⊤
  · rw [top_mul (by simpa using hb), tendsto_nhds_top_iff]
    intro x
    have hforall : ∀ᶠ c : ℕ∞ × ℕ∞ in 𝓝 (⊤, b), ↑x < c.1 ∧ 0 < c.2 := by
      refine (lt_mem_nhds (show (x : ℕ∞) < ⊤ from WithTop.coe_lt_top x)).prod_nhds ?_
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

@[simp] protected theorem iSup_eq_zero {f : ι → ℕ∞} : ⨆ i, f i = 0 ↔ ∀ i, f i = 0 :=
  iSup_eq_bot

@[simp] protected theorem iSup_zero_eq_zero : ⨆ _ : ι, (0 : ℕ∞) = 0 := by
  simp

protected theorem mul_iSup (c : ℕ∞) (f : ι → ℕ∞) : c * (⨆ i, f i) = ⨆ i, (c * f i) := by
  by_cases hf : ∀ i, f i = 0
  · obtain rfl : f = fun _ ↦ 0
    exact funext hf
    simp only [mul_zero, ENat.iSup_zero_eq_zero]
  refine' (monotone_id.const_mul' _).map_iSup_of_continuousAt _ (mul_zero c)
  refine' ENat.Tendsto.const_mul tendsto_id (Or.inl _)
  exact mt ENat.iSup_eq_zero.1 hf

protected theorem iSup_mul (c : ℕ∞) (f : ι → ℕ∞) : (⨆ i, f i) * c = ⨆ i, (f i * c) := by
  simp_rw [mul_comm, ENat.mul_iSup]

end Sup

section tsum

variable {f g : α → ℕ∞}

protected theorem hasSum : HasSum f (⨆ s : Finset α, ∑ a in s, f a) :=
  tendsto_atTop_iSup fun _ _ ↦ Finset.sum_le_sum_of_subset

@[simp] protected theorem summable : Summable f :=
  ⟨_, ENat.hasSum⟩

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

protected theorem le_tsum_of_mem {s : Set α} {a : α} (ha : a ∈ s) : f a ≤ ∑' (x : s), f x :=
  ENat.le_tsum (⟨a,ha⟩ : s)

@[simp] protected theorem tsum_eq_zero : ∑' i, f i = 0 ↔ ∀ i, f i = 0 :=
  tsum_eq_zero_iff ENat.summable

protected theorem tsum_eq_top_of_eq_top : (∃ a, f a = ⊤) → ∑' a, f a = ⊤
  | ⟨a, ha⟩ => top_unique <| ha ▸ ENat.le_tsum a

protected theorem tsum_subtype_eq_top_of_eq_top {s : Set α} (h : ∃ a ∈ s, f a = ⊤) :
    ∑' a : s, f a = ⊤ :=
  let ⟨a, ha, has⟩ := h
  ENat.tsum_eq_top_of_eq_top ⟨⟨a, ha⟩, has⟩

-- sets

protected theorem tsum_union_disjoint {s t : Set α} (hd : Disjoint s t) :
    ∑' (x : ↑(s ∪ t)), f x = ∑' (x : s), f x + ∑' (x : t), f x :=
  tsum_union_disjoint hd ENat.summable ENat.summable

protected theorem tsum_le_of_subset {s t : Set α} (h : s ⊆ t) :
    ∑' (x : s), f x ≤ ∑' (x : t), f x := by
  rw [← diff_union_of_subset h, ENat.tsum_union_disjoint disjoint_sdiff_left]
  exact le_add_self

protected theorem tsum_le_union (s t : Set α) :
    ∑' (x : ↑(s ∪ t)), f (x : α) ≤ ∑' (x : s), f x + ∑' (x : t), f x := by
  rw [← diff_union_self, ENat.tsum_union_disjoint disjoint_sdiff_left]
  exact add_le_add_right (ENat.tsum_le_of_subset (diff_subset _ _)) _

protected theorem tsum_insert {s : Set α} {a : α} (h : a ∉ s) :
    ∑' (x : ↑(insert a s)), f x = f a + ∑' (x : s), f x := by
  rw [← singleton_union, ENat.tsum_union_disjoint, tsum_singleton]
  rwa [disjoint_singleton_left]

protected theorem tsum_sub (hfin : ∑' a, g a ≠ ⊤) (h : g ≤ f) :
    ∑' a, (f a - g a) = ∑' a, f a - ∑' a, g a := by
  rw [← WithTop.add_right_cancel_iff hfin, ← ENat.tsum_add,
    tsum_congr (fun i ↦ tsub_add_cancel_of_le (h i)), tsub_add_cancel_of_le (ENat.tsum_le_tsum h)]

protected theorem mul_tsum (c : ℕ∞) : c * ∑' a, f a = ∑' a, c * f a := by
  simp_rw [ENat.tsum_eq_iSup_sum, ENat.mul_iSup, Finset.mul_sum]

protected theorem tsum_mul (c : ℕ∞) : (∑' a, f a) * c = ∑' a, f a * c := by
  simp_rw [ENat.tsum_eq_iSup_sum, ENat.iSup_mul, Finset.sum_mul]

theorem Finite.tsum_eq_top_iff {s : Set α} (hs : s.Finite) :
    ∑' (x : s), f x = ⊤ ↔ ∃ a ∈ s, f a = ⊤ := by
  refine' ⟨hs.induction_on (by simp) @fun a s' has' _ IH htop ↦ _,
    fun ⟨a, has, ha⟩ ↦ ENat.tsum_eq_top_of_eq_top ⟨⟨a, has⟩, ha⟩⟩
  obtain (ht | hne) := eq_or_ne (f a) ⊤
  · exact ⟨a, mem_insert _ _, ht⟩
  rw [ENat.tsum_insert has', WithTop.add_eq_top, or_iff_right hne] at htop
  obtain ⟨b, hbs, hbtop⟩ := IH htop
  exact ⟨b, Or.inr hbs, hbtop⟩

protected theorem tsum_eq_top_of_support_infinite (hf : f.support.Infinite) : ∑' a, f a = ⊤ := by
  rw [ENat.tsum_eq_iSup_sum, iSup_eq_top]
  intro b hb
  lift b to ℕ using hb.ne
  obtain ⟨s, hss, hsc⟩ := exists_subset_encard_eq ((add_one_le_of_lt hb).trans_eq hf.encard_eq.symm)
  rw [← Nat.cast_one, ← Nat.cast_add] at hsc
  set s' := (finite_of_encard_eq_coe hsc).toFinset
  refine ⟨s', lt_of_lt_of_le ?_ (Finset.sum_le_sum (show ∀ i ∈ s', 1 ≤ f i from ?_))  ⟩
  · rw [Finset.sum_const, nsmul_eq_mul, mul_one,
      ← (finite_of_encard_eq_coe hsc).encard_eq_coe_toFinset_card, hsc, Nat.cast_lt]
    exact Nat.lt.base b
  simp only [Finite.mem_toFinset, ENat.one_le_iff_ne_zero, s']
  exact hss

protected theorem tsum_const_eq_top_of_ne_zero [Infinite ι] {c : ℕ∞} (hc : c ≠ 0) :
    ∑' (_ : ι), c = ⊤ :=
  ENat.tsum_eq_top_of_support_infinite (by rwa [support_const hc, infinite_univ_iff])

protected theorem tsum_eq_top_iff : ∑' a, f a = ⊤ ↔ f.support.Infinite ∨ ∃ a, f a = ⊤ := by
  refine' ⟨fun h ↦ _, _⟩
  · rw [or_iff_not_imp_left, not_infinite]
    intro hfin
    rw [← tsum_support_eq, Finite.tsum_eq_top_iff hfin] at h
    obtain ⟨a, -, h⟩ := h
    exact ⟨a, h⟩
  rintro (h | h)
  · exact ENat.tsum_eq_top_of_support_infinite h
  exact ENat.tsum_eq_top_of_eq_top h

protected theorem tsum_subtype_eq_top_iff {s : Set α} :
    ∑' (a : s), f a = ⊤ ↔ (s ∩ f.support).Infinite ∨ ∃ a ∈ s, f a = ⊤ := by
  simp_rw [ENat.tsum_eq_top_iff, Subtype.exists, exists_prop]
  convert Iff.rfl
  simp_rw [← Set.finite_coe_iff]
  exact Bijective.finite_iff (f := fun i ↦ ⟨⟨i,i.2.1⟩, i.2.2⟩)
    ⟨by rintro ⟨i, hi⟩ ⟨j, hj⟩ hij; simpa using hij, by rintro ⟨⟨i,his⟩, hi⟩; use ⟨i, ⟨his, hi⟩⟩⟩

protected theorem tsum_subtype_eq_top_of_inter_support_infinite {s : Set α}
    (hf : (s ∩ f.support).Infinite) : ∑' (a : s), f a = ⊤ :=
  ENat.tsum_subtype_eq_top_iff.2 (Or.inl hf)

protected theorem tsum_subtype_const_eq_top_of_ne_zero {s : Set α} (hs : s.Infinite) {c : ℕ∞}
    (hc : c ≠ 0) : ∑' (_ : s), c = ⊤ :=
  ENat.tsum_subtype_eq_top_of_inter_support_infinite (f := fun _ ↦ c)
    (by rwa [support_const hc, inter_univ])

protected theorem tsum_comp_le_tsum_of_injective {f : α → β} (hf : Injective f) (g : β → ℕ∞) :
    ∑' x, g (f x) ≤ ∑' y, g y :=
  tsum_le_tsum_of_inj f hf (fun _ _ ↦ zero_le _) (fun _ ↦ le_rfl) ENat.summable ENat.summable

protected theorem tsum_le_tsum_comp_of_surjective {f : α → β} (hf : Surjective f) (g : β → ℕ∞) :
    ∑' y, g y ≤ ∑' x, g (f x) :=
  calc ∑' y, g y = ∑' y, g (f (surjInv hf y)) := by simp only [surjInv_eq hf]
    _ ≤ ∑' x, g (f x) := ENat.tsum_comp_le_tsum_of_injective (injective_surjInv hf) _

protected theorem tsum_comp_eq_tsum_of_bijective {f : α → β} (hf : f.Bijective) (g : β → ℕ∞) :
    ∑' x, g (f x) = ∑' y, g y :=
  (ENat.tsum_comp_le_tsum_of_injective hf.injective g).antisymm
    (ENat.tsum_le_tsum_comp_of_surjective hf.surjective g)

protected theorem tsum_comp_eq_tsum_of_equiv (e : α ≃ β) (g : β → ℕ∞) :
    ∑' x, g (e x) = ∑' y, g y := by
  rw [ENat.tsum_comp_eq_tsum_of_bijective e.bijective]

protected theorem tsum_mono_subtype (f : α → ℕ∞) {s t : Set α} (h : s ⊆ t) :
    ∑' x : s, f x ≤ ∑' x : t, f x :=
  ENat.tsum_comp_le_tsum_of_injective (inclusion_injective h) _

protected theorem tsum_sigma {β : α → Type*} (f : ∀ a, β a → ℕ∞) :
    ∑' p : Σa, β a, f p.1 p.2 = ∑' (a) (b), f a b :=
  tsum_sigma' (fun _ ↦ ENat.summable) ENat.summable

protected theorem tsum_sigma' {β : α → Type*} (f : (Σ a, β a) → ℕ∞) :
    ∑' p : Σ a, β a, f p = ∑' (a) (b), f ⟨a, b⟩ :=
  tsum_sigma' (fun _ ↦ ENat.summable) ENat.summable

protected theorem tsum_iUnion_le_tsum (f : α → ℕ∞) (t : ι → Set α) :
    ∑' x : ⋃ i, t i, f x ≤ ∑' i, ∑' x : t i, f x :=
  calc ∑' x : ⋃ i, t i, f x ≤ ∑' x : Σ i, t i, f x.2 :=
    ENat.tsum_le_tsum_comp_of_surjective (sigmaToiUnion_surjective t) _
  _ = ∑' i, ∑' x : t i, f x := ENat.tsum_sigma' _

protected theorem tsum_biUnion_le_tsum (f : α → ℕ∞) (s : Set ι) (t : ι → Set α) :
    ∑' x : ⋃ i ∈ s , t i, f x ≤ ∑' i : s, ∑' x : t i, f x :=
  calc ∑' x : ⋃ i ∈ s, t i, f x = ∑' x : ⋃ i : s, t i, f x := by rw [tsum_congr_subtype]; simp
  _ ≤ ∑' i : s, ∑' x : t i, f x := ENat.tsum_iUnion_le_tsum _ _

protected theorem tsum_biUnion_le (f : α → ℕ∞) (s : Finset ι) (t : ι → Set α) :
    ∑' x : ⋃ i ∈ s, t i, f x ≤ ∑ i in s, ∑' x : t i, f x :=
  (ENat.tsum_biUnion_le_tsum f s.toSet t).trans_eq (Finset.tsum_subtype s fun i ↦ ∑' x : t i, f x)

protected theorem tsum_iUnion_le [Fintype ι] (f : α → ℕ∞) (t : ι → Set α) :
    ∑' x : ⋃ i, t i, f x ≤ ∑ i, ∑' x : t i, f x := by
  rw [← tsum_fintype]
  exact ENat.tsum_iUnion_le_tsum f t

theorem tsum_iUnion_eq_tsum (f : α → ℕ∞) (t : ι → Set α) (ht : univ.PairwiseDisjoint t) :
    ∑' x : ⋃ i, t i, f x = ∑' i, ∑' x : t i, f x :=
  calc ∑' x : ⋃ i, t i, f x = ∑' x : Σ i, t i, f x.2 :=
    (ENat.tsum_comp_eq_tsum_of_bijective (sigmaToiUnion_bijective t
      (fun i j hij ↦ ht (mem_univ i) (mem_univ j) hij)) _).symm
  _ = _ := ENat.tsum_sigma' _

-- cardinality

/-- A version of `ENat.tsum_one` where the `1` is explicitly a function from the type rather than
  from the subtype. Useful for rewriting. -/
protected theorem tsum_one' (s : Set α) : ∑' (i : s), (1 : α → ℕ∞) i = s.encard := by
  obtain (hfin | hinf) := s.finite_or_infinite
  · have := hfin.fintype
    convert tsum_eq_sum (β := s) (f := (1 : s → ℕ∞)) (s := Finset.univ) (by simp)
    simp only [Pi.one_apply, Finset.sum_const, nsmul_eq_mul, mul_one,
      encard_eq_coe_toFinset_card, toFinset_card, Nat.cast_inj]
    rfl
  rw [hinf.encard_eq, ENat.tsum_subtype_eq_top_of_inter_support_infinite]
  simpa

@[simp] protected theorem tsum_one (s : Set α) : ∑' (_ : s), 1 = s.encard :=
  ENat.tsum_one' s

@[simp] protected theorem tsum_subtype_const (s : Set α) (c : ℕ∞) :
    ∑' (_ : s), c = c * s.encard := by
  rw [← ENat.tsum_one s, ENat.mul_tsum, mul_one]

@[simp] protected theorem tsum_const (c : ℕ∞) : ∑' _ : ι, c = c * (univ : Set ι).encard := by
  rw [← tsum_univ, ENat.tsum_subtype_const]

protected theorem encard_support_le_tsum : f.support.encard ≤ ∑' x, f x := by
  rw [← ENat.tsum_one', tsum_subtype]
  exact ENat.tsum_le_tsum <| ENat.indicator_support_le _

protected theorem tsum_encard_eq_encard_iUnion {ι} {s : ι → Set α} (hI : univ.PairwiseDisjoint s) :
    ∑' i, (s i).encard = (⋃ i, s i).encard := by
  simp_rw [← ENat.tsum_one', ENat.tsum_iUnion_eq_tsum _ _ hI]

theorem encard_iUnion_le_tsum_encard {ι} {s : ι → Set α} :
    (⋃ i, s i).encard ≤ ∑' i, (s i).encard := by
  rw [← ENat.tsum_one]
  exact (ENat.tsum_iUnion_le_tsum 1 s).trans_eq (by simp)

theorem tsum_encard_eq_encard_biUnion {ι} {s : ι → Set α} {t : Set ι}
    (hI : t.PairwiseDisjoint s) : ∑' i : t, (s i).encard = (⋃ i ∈ t, s i).encard := by
  rw [biUnion_eq_iUnion, ← ENat.tsum_encard_eq_encard_iUnion]
  rintro ⟨i,hi⟩ - ⟨j,hj⟩ - hij
  exact hI hi hj (by simpa using hij)

theorem encard_biUnion_le_tsum_encard {ι} {s : ι → Set α} {I : Set ι} :
    (⋃ i ∈ I, s i).encard ≤ ∑' i : I, (s i).encard := by
  rw [biUnion_eq_iUnion]
  apply encard_iUnion_le_tsum_encard

protected theorem tsum_encard_eq_encard_sUnion {c : Set (Set α)} (hc : c.PairwiseDisjoint id) :
    ∑' (t : c), (t : Set α).encard = (⋃₀ c).encard := by
  rw [sUnion_eq_iUnion, ← ENat.tsum_encard_eq_encard_iUnion]
  rintro ⟨i,hi⟩ - ⟨j,hj⟩ - hij
  exact hc hi hj (by simpa using hij)

theorem encard_sUnion_le_tsum_encard {c : Set (Set α)} :
    (⋃₀ c).encard ≤ ∑' s : c, s.1.encard := by
  rw [sUnion_eq_iUnion]
  apply encard_iUnion_le_tsum_encard

protected theorem tsum_inter_fiber_eq {ι} {s : Set ι} (f : ι → α) :
    ∑' (a : α), (s ∩ f ⁻¹' {a}).encard = s.encard := by
  rw [ENat.tsum_encard_eq_encard_iUnion]
  · congr; aesop
  refine fun i _ j _ hij ↦ disjoint_iff_forall_ne.2 ?_
  rintro a ⟨-,rfl⟩ _ ⟨-,rfl⟩ rfl
  exact hij rfl

protected theorem tsum_fiber_eq {ι} (f : ι → α) :
    ∑' (a : α), (f ⁻¹' {a}).encard = (univ : Set ι).encard := by
  rw [← ENat.tsum_inter_fiber_eq (s := univ) f, tsum_congr]; intro b; rw [univ_inter]

end tsum



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
