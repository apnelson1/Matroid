module

public import Matroid.ForMathlib.Topology.Path

/-!
# Primitive paths

A **primitive path** is injectively parametrized except that a loop may identify its endpoints.
In a Hausdorff target, it parametrizes an embedded arc or an embedded loop.
-/

@[expose] public section

open Set Function unitInterval

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x y : X} {γ : Path x y} {s t : I}
  {f : X → Y}

namespace Path

private lemma eq_of_eq_of_pair (heq : γ s = γ t) (hp : ({s, t} : Set I) = {0, 1}) : x = y := by
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := pair_eq_pair_iff.mp hp
  · simpa [Path.source, Path.target] using heq
  simpa [Path.source, Path.target] using heq.symm

/-- A path is primitive if it is injectively parametrized, except that a loop may identify its
two endpoints. -/
def IsPrimitive (γ : Path x y) : Prop := ∀ ⦃s t : I⦄, γ s = γ t → s = t ∨ ({s, t} : Set I) = {0, 1}

lemma IsPrimitive.of_injective (h : Injective γ) : γ.IsPrimitive := fun _ _ hst ↦ Or.inl <| h hst

lemma IsPrimitive.injective (hγ : γ.IsPrimitive) (hxy : x ≠ y) : Injective γ :=
  fun _ _ hst ↦ (hγ hst).elim id fun hp ↦ (hxy <| eq_of_eq_of_pair hst hp).elim

lemma isPrimitive_iff_injective (hxy : x ≠ y) : γ.IsPrimitive ↔ Injective γ :=
  ⟨fun h ↦ h.injective hxy, IsPrimitive.of_injective⟩

/-- A primitive path is injective on each of the two half-open parameter intervals. -/
lemma isPrimitive_iff_injOn : γ.IsPrimitive ↔ InjOn γ (Ico 0 1) ∧ InjOn γ (Ioc 0 1) := by
  refine ⟨fun h ↦ ?_, fun ⟨hco, hoc⟩ s t heq ↦ ?_⟩
  · constructor <;> refine fun s hs t ht heq ↦ (h heq).resolve_right fun hst ↦ ?_ <;>
      obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := pair_eq_pair_iff.mp hst <;> simp_all
  obtain rfl | hs1 := eq_or_ne s 1 <;> obtain rfl | ht1 := eq_or_ne t 1
  · exact Or.inl rfl
  · obtain rfl | ht0 := eq_or_ne t 0
    · simp [pair_comm]
    exact Or.inl <| hoc (by simp) ⟨lt_of_le_of_ne t.prop.left <| ht0.symm, t.prop.right⟩ heq
  · obtain rfl | hs0 := eq_or_ne s 0
    · simp
    exact Or.inl <| hoc ⟨lt_of_le_of_ne s.prop.left <| hs0.symm, s.prop.right⟩ (by simp) heq
  exact Or.inl <| hco ⟨s.prop.left, lt_of_le_of_ne s.prop.right hs1⟩
    ⟨t.prop.left, lt_of_le_of_ne t.prop.right ht1⟩ heq

lemma IsSimpleLoop.isPrimitive {γ : Path x x} (h : γ.IsSimpleLoop) : γ.IsPrimitive :=
  isPrimitive_iff_injOn.mpr ⟨h, γ.injOn_ico_iff_injOn_ioc.1 h⟩

lemma IsPrimitive.map (h : γ.IsPrimitive) (hf : ContinuousOn f <| range γ)
    (hinj : InjOn f <| range γ) : (γ.map' hf).IsPrimitive :=
  fun s t hst ↦ h <| hinj (mem_range_self s) (mem_range_self t) hst

/-- Primitivity of a mapped path implies primitivity of the original path. -/
lemma IsPrimitive.of_map {hf : ContinuousOn f <| range γ} (h : (γ.map' hf).IsPrimitive) :
    γ.IsPrimitive :=
  fun _ _ hst ↦ h <| congrArg f hst

lemma isPrimitive_map_iff (hf : ContinuousOn f <| range γ) (hinj : InjOn f <| range γ) :
    (γ.map' hf).IsPrimitive ↔ γ.IsPrimitive := ⟨IsPrimitive.of_map, fun h ↦ h.map hf hinj⟩

lemma IsPrimitive.injOn_Ico (h : γ.IsPrimitive) : InjOn γ <| Ico 0 1 :=
  (isPrimitive_iff_injOn.mp h).left

lemma IsPrimitive.injOn_Ioc (h : γ.IsPrimitive) : InjOn γ <| Ioc 0 1 :=
  (isPrimitive_iff_injOn.mp h).right

lemma IsPrimitive.isSimpleLoop {γ : Path x x} (h : γ.IsPrimitive) : γ.IsSimpleLoop := h.injOn_Ico

lemma isPrimitive_iff_isSimpleLoop {γ : Path x x} : γ.IsPrimitive ↔ γ.IsSimpleLoop :=
  ⟨IsPrimitive.isSimpleLoop, IsSimpleLoop.isPrimitive⟩

lemma isPrimitive_iff : γ.IsPrimitive ↔ Injective γ ∨ ∃ h : x = y, (γ.cast rfl h).IsSimpleLoop := by
  refine ⟨fun h ↦ (eq_or_ne x y).symm.imp h.injective (⟨·, h.isSimpleLoop⟩), ?_⟩
  rintro (hinj | ⟨rfl, hloop⟩)
  · exact IsPrimitive.of_injective hinj
  exact hloop.isPrimitive

@[simp]
lemma not_isPrimitive_refl : ¬ (refl x).IsPrimitive := by
  simp [isPrimitive_iff_isSimpleLoop]

lemma IsPrimitive.finite_preimage (hγ : γ.IsPrimitive)
    {F : Set X} (hF : F.Finite) : (γ ⁻¹' F).Finite := by
  refine Finite.of_sdiff
    (Finite.of_injOn (f := γ) (fun _ ht ↦ ht.left) (hγ.injOn_Ico.mono ?_) hF) <| finite_singleton 1
  exact fun t ht ↦ ⟨t.prop.left, lt_of_le_of_ne t.prop.right ht.right⟩

variable (hγ : γ.IsPrimitive)
include hγ

lemma IsPrimitive.symm : γ.symm.IsPrimitive := by
  intro s t hst
  obtain hs | hp := hγ hst
  · exact Or.inl <| symm_inj.mp hs
  right
  rw [pair_eq_pair_iff] at hp ⊢
  simpa [symm_eq_zero, symm_eq_one, or_comm] using hp

omit hγ in
@[simp]
lemma isPrimitive_symm_iff : γ.symm.IsPrimitive ↔ γ.IsPrimitive :=
  ⟨fun h ↦ by simpa using h.symm, IsPrimitive.symm⟩

lemma IsPrimitive.injOn_Ioo : InjOn γ <| Ioo (0 : I) 1 := hγ.injOn_Ico.mono Ioo_subset_Ico_self

/-- A primitive path visits its source only at the start, and also at the end exactly when it
is a loop. -/
lemma IsPrimitive.apply_eq_source_iff : γ t = x ↔ t = 0 ∨ t = 1 ∧ y = x := by
  refine ⟨fun h ↦ ?_, by rintro (rfl | ⟨rfl, rfl⟩) <;> simp⟩
  obtain h0 | hp := hγ (h.trans γ.source.symm)
  · exact .inl h0
  obtain ⟨rfl, -⟩ | ⟨rfl, -⟩ := pair_eq_pair_iff.mp hp
  · exact .inl rfl
  exact .inr ⟨rfl, γ.target.symm.trans h⟩

/-- A primitive path visits its target only at the end, and also at the start exactly when it
is a loop. -/
lemma IsPrimitive.apply_eq_target_iff : γ t = y ↔ t = 1 ∨ t = 0 ∧ x = y := by
  refine ⟨fun h ↦ ?_, by rintro (rfl | ⟨rfl, rfl⟩) <;> simp⟩
  obtain h1 | hp := hγ (h.trans γ.target.symm)
  · exact .inl h1
  obtain ⟨rfl, -⟩ | ⟨rfl, -⟩ := pair_eq_pair_iff.mp hp
  · exact .inr ⟨rfl, γ.source.symm.trans h⟩
  exact .inl rfl

lemma IsPrimitive.source_notMem_interior : x ∉ γ.Interior := by
  rintro ⟨t, ht, htx⟩
  obtain rfl | ⟨rfl, -⟩ := hγ.apply_eq_source_iff.1 htx <;> simp at ht

lemma IsPrimitive.target_notMem_interior : y ∉ γ.Interior := by
  rintro ⟨t, ht, hty⟩
  obtain rfl | ⟨rfl, -⟩ := hγ.apply_eq_target_iff.1 hty <;> simp at ht

lemma IsPrimitive.range_diff_endpoints : range γ \ {x, y} = γ.Interior :=
  Path.range_diff_endpoints hγ.source_notMem_interior hγ.target_notMem_interior

lemma IsPrimitive.isPathConnected_range_diff_endpoints : IsPathConnected (range γ \ {x, y}) := by
  rw [hγ.range_diff_endpoints]
  exact γ.isPathConnected_interior

/-! ### Subpaths and halves -/

/-- Every subpath between distinct parameters of a primitive path is primitive, in either
orientation. -/
lemma IsPrimitive.subpath (hst : s ≠ t) : (γ.subpath s t).IsPrimitive := by
  wlog hlt : s < t generalizing s t
  · simpa using (this hst.symm <| hst.lt_or_gt.resolve_left hlt).symm
  obtain rfl | hs := eq_or_ne s 0
  obtain rfl | ht := eq_or_ne t 1
  · rwa [subpath_zero_one]
  all_goals refine of_injective <| injective_subpath_iff.mpr ⟨hst, ?_⟩; rw [uIcc_of_le hlt.le]
  · refine hγ.injOn_Ico.mono ?_
    exact (⟨·.prop.left, ·.right.trans_lt (lt_of_le_of_ne t.prop.right ht)⟩)
  refine hγ.injOn_Ioc.mono ?_
  exact fun u hu ↦ ⟨((bot_lt_iff_ne_bot.2 hs).trans_le hu.left), u.prop.right⟩

/-- A subpath of a primitive path is injective exactly when its endpoint values differ. -/
lemma IsPrimitive.injective_subpath_iff : (Injective <| γ.subpath s t) ↔ γ s ≠ γ t :=
  ⟨fun h heq ↦ zero_ne_one <| h <| (γ.subpath s t).source.trans <|
    heq.trans (γ.subpath s t).target.symm, fun h ↦ ((hγ.subpath (h <| congrArg γ ·)).injective h)⟩

lemma IsPrimitive.injective_subpath (hst : γ s ≠ γ t) : Injective <| γ.subpath s t :=
  hγ.injective_subpath_iff.2 hst

/-- The two pieces at any cut meet at the cut point and, for a loop, at the shared endpoint. -/
lemma IsPrimitive.subpath_range_inter_subpath_range (u : I) :
    (range <| γ.subpath 0 u) ∩ (range <| γ.subpath u 1) = {γ u} ∪ ({x} ∩ {y}) := by
  rw [γ.range_subpath_of_le 0 u u.prop.left, γ.range_subpath_of_le u 1 u.prop.right]
  refine Subset.antisymm (fun z ⟨⟨s, hs, hsz⟩, t, ht, htz⟩ ↦ ?_) ?_
  · obtain hst | hp := hγ <| hsz.trans htz.symm
    · obtain rfl : s = u := hs.right.antisymm (hst ▸ ht.left)
      tauto
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := pair_eq_pair_iff.mp hp
    · exact Or.inr ⟨hsz.symm.trans γ.source, htz.symm.trans γ.target⟩
    exact (zero_lt_one.not_ge <| hs.right.trans ht.left).elim
  rintro z (rfl | ⟨hx, hy⟩)
  · exact ⟨⟨u, ⟨u.prop.left, le_rfl⟩, rfl⟩, ⟨u, ⟨le_rfl, u.prop.right⟩, rfl⟩⟩
  exact ⟨⟨0, ⟨le_rfl, u.prop.left⟩, γ.source.trans hx.symm⟩,
    ⟨1, ⟨u.prop.right, le_rfl⟩, γ.target.trans hy.symm⟩⟩

lemma IsPrimitive.firstHalf_range_inter_secondHalf_range :
    range γ.firstHalf ∩ range γ.secondHalf = {γ half} ∪ ({x} ∩ {y}) :=
  hγ.subpath_range_inter_subpath_range half

lemma IsPrimitive.half_ne_source : γ half ≠ x :=
  (hγ.source_notMem_interior ⟨half, ⟨zero_lt_half, half_lt_one⟩, ·⟩)

lemma IsPrimitive.half_ne_target : γ half ≠ y :=
  (hγ.target_notMem_interior ⟨half, ⟨zero_lt_half, half_lt_one⟩, ·⟩)

lemma IsPrimitive.injective_firstHalf : Injective γ.firstHalf :=
  hγ.injective_subpath (show γ 0 ≠ γ half by simpa using hγ.half_ne_source.symm)

lemma IsPrimitive.injective_secondHalf : Injective γ.secondHalf :=
  hγ.injective_subpath (show γ half ≠ γ 1 by simpa using hγ.half_ne_target)

end Path

/-! ### Selecting subpaths of two paths -/

namespace Path

variable {a b c : X} {η : Path a b}

/-- If both endpoints of an injective path lie on the range of a primitive path, visited at a
closed set of parameters, a point of the first path outside that range lies in an excursion
subarc. A subarc of the second path joins its endpoints, in either parameter direction, and the
two subpaths meet exactly at those distinct endpoints. -/
theorem exists_subpaths_inter_eq_pair (hγ : Injective γ) (hη : η.IsPrimitive)
    (hηc : IsClosed (γ ⁻¹' range η)) (hx : x ∈ range η) (hy : y ∈ range η)
    (hc : c ∈ range γ \ range η) :
    ∃ u v s t : I, (u, v) ∈ γ.excursions (range η) ∧
      γ u = η s ∧ γ v = η t ∧ c ∈ γ '' Ioo u v ∧
      Injective (γ.subpath u v) ∧ Injective (η.subpath s t) ∧
      range (γ.subpath u v) ∩ range (η.subpath s t) = {γ u, γ v} := by
  obtain ⟨⟨r, rfl⟩, hr⟩ := hc
  obtain ⟨uv, huv, hruv⟩ := γ.exists_mem_excursions hηc hx hy hr
  obtain ⟨s, hs⟩ := huv.2.1
  obtain ⟨t, ht⟩ := huv.2.2.1
  refine ⟨uv.1, uv.2, s, t, huv, hs.symm, ht.symm, ⟨r, hruv, rfl⟩,
    injective_subpath hγ huv.1.ne, hη.injective_subpath (hs ▸ ht ▸ hγ.ne huv.1.ne), ?_⟩
  apply Subset.antisymm
  · intro z hz
    apply (γ.range_subpath_inter_of_mem_excursions huv).subset
    refine ⟨hz.1, ?_⟩
    rw [η.range_subpath] at hz
    exact image_subset_range η _ hz.2
  rintro z (rfl | rfl)
  · exact ⟨(γ.subpath uv.1 uv.2).source_mem_range, hs ▸ (η.subpath s t).source_mem_range⟩
  exact ⟨(γ.subpath uv.1 uv.2).target_mem_range, ht ▸ (η.subpath s t).target_mem_range⟩

end Path
