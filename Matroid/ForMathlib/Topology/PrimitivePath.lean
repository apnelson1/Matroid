module

public import Matroid.ForMathlib.Topology.Path

/-!
# Primitive paths

A **primitive path** is injectively parametrized except that a loop may identify its endpoints.
In a Hausdorff target, it parametrizes an embedded arc or an embedded loop.
-/

@[expose] public section

open Set Function unitInterval

variable {X : Type*} [TopologicalSpace X] {x y : X}

namespace Path

/-- A path is primitive if it is injectively parametrized, except that a loop may identify its
two endpoints. -/
def IsPrimitive (γ : Path x y) : Prop :=
  ∀ ⦃s t : I⦄, γ s = γ t → s = t ∨ ({s, t} : Set I) = {0, 1}

private lemma eq_of_eq_of_pair {γ : Path x y} {s t : I}
    (heq : γ s = γ t) (hp : ({s, t} : Set I) = {0, 1}) : x = y := by
  rcases pair_eq_pair_iff.mp hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simpa [Path.source, Path.target] using heq
  · simpa [Path.source, Path.target] using heq.symm

lemma IsPrimitive.of_injective {γ : Path x y} (h : Injective γ) : γ.IsPrimitive :=
  fun _ _ hst ↦ Or.inl (h hst)

lemma IsPrimitive.injective {γ : Path x y} (h : γ.IsPrimitive) (hxy : x ≠ y) :
    Injective γ := by
  intro s t hst
  exact (h hst).elim id fun hp ↦ (hxy (eq_of_eq_of_pair hst hp)).elim

lemma isPrimitive_iff_injective {γ : Path x y} (hxy : x ≠ y) :
    γ.IsPrimitive ↔ Injective γ :=
  ⟨fun h ↦ h.injective hxy, IsPrimitive.of_injective⟩

lemma IsSimpleLoop.isPrimitive {γ : Path x x} (h : γ.IsSimpleLoop) : γ.IsPrimitive := by
  intro s t hst
  by_cases hs1 : s = 1 <;> by_cases ht1 : t = 1
  · exact Or.inl (hs1.trans ht1.symm)
  · refine Or.inr ?_
    have htI : t ∈ Ico (0 : I) 1 := ⟨t.2.1, lt_of_le_of_ne t.2.2 ht1⟩
    have hγ : γ t = γ 0 :=
      (hst.symm.trans (congrArg γ hs1)).trans (γ.target.trans γ.source.symm)
    have ht0 : t = 0 := h htI (by simp) hγ
    rw [hs1, ht0, pair_comm]
  · refine Or.inr ?_
    have hsI : s ∈ Ico (0 : I) 1 := ⟨s.2.1, lt_of_le_of_ne s.2.2 hs1⟩
    have hγ : γ s = γ 0 :=
      (hst.trans (congrArg γ ht1)).trans (γ.target.trans γ.source.symm)
    have hs0 : s = 0 := h hsI (by simp) hγ
    rw [hs0, ht1]
  · exact Or.inl <| h ⟨s.2.1, lt_of_le_of_ne s.2.2 hs1⟩ ⟨t.2.1, lt_of_le_of_ne t.2.2 ht1⟩ hst

lemma IsPrimitive.isSimpleLoop {γ : Path x x} (h : γ.IsPrimitive) : γ.IsSimpleLoop := by
  intro s hs t ht hst
  obtain rfl | hp := h hst
  · rfl
  · have h1 : (1 : I) ∈ Ico (0 : I) 1 := by
      have : (1 : I) ∈ ({s, t} : Set I) := hp ▸ (by simp : (1 : I) ∈ ({0, 1} : Set I))
      exact this.elim (fun h1 ↦ h1 ▸ hs) (fun h1 ↦ h1 ▸ ht)
    exact (not_le_of_gt h1.2 le_rfl).elim

lemma isPrimitive_iff_isSimpleLoop {γ : Path x x} : γ.IsPrimitive ↔ γ.IsSimpleLoop :=
  ⟨IsPrimitive.isSimpleLoop, IsSimpleLoop.isPrimitive⟩

lemma isPrimitive_iff {γ : Path x y} :
    γ.IsPrimitive ↔ Injective γ ∨ ∃ h : x = y, (γ.cast rfl h).IsSimpleLoop := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · rcases eq_or_ne x y with rfl | hxy
    · exact Or.inr ⟨rfl, by
        rw [cast_rfl_rfl]
        exact h.isSimpleLoop⟩
    · exact Or.inl (h.injective hxy)
  · rintro (hinj | ⟨rfl, hloop⟩)
    · exact IsPrimitive.of_injective hinj
    · rw [cast_rfl_rfl] at hloop
      exact hloop.isPrimitive

@[simp]
lemma not_isPrimitive_refl : ¬ (Path.refl x).IsPrimitive := by
  intro h
  obtain h01 | hp := h (s := 0) (t := half) (by simp)
  · exact half_ne_zero h01.symm
  · rcases pair_eq_pair_iff.mp hp with ⟨_, h1⟩ | ⟨h1, _⟩
    · exact half_ne_one h1
    · exact zero_ne_one h1

lemma IsPrimitive.symm {γ : Path x y} (h : γ.IsPrimitive) : γ.symm.IsPrimitive := by
  intro s t hst
  rw [symm_apply, symm_apply] at hst
  obtain hs | hp := h hst
  · exact Or.inl (symm_inj.mp hs)
  · refine Or.inr ?_
    rw [pair_eq_pair_iff] at hp ⊢
    simpa [symm_eq_zero, symm_eq_one, or_comm] using hp

lemma IsPrimitive.injOn_Ioo {γ : Path x y} (h : γ.IsPrimitive) :
    InjOn γ (Ioo (0 : I) 1) := by
  intro s hs t _ht hst
  obtain rfl | hp := h hst
  · rfl
  · have hs01 : s ∈ ({0, 1} : Set I) := hp ▸ mem_insert s {t}
    have hsI := mem_Ioo_iff.mp hs
    exact hs01.elim (fun h0 ↦ (hsI.1 h0).elim)
      fun h1 ↦ (hsI.2 (mem_singleton_iff.mp h1)).elim

lemma IsPrimitive.source_notMem_interior {γ : Path x y} (h : γ.IsPrimitive) :
    x ∉ γ.Interior := by
  rintro ⟨t, ht, htx⟩
  obtain ht0 | hp := h (htx.trans γ.source.symm)
  · exact (mem_Ioo_iff.mp ht).1 ht0
  · rcases pair_eq_pair_iff.mp hp with ⟨rfl, h01⟩ | ⟨rfl, _⟩
    · exact zero_ne_one h01
    · exact (mem_Ioo_iff.mp ht).2 rfl

lemma IsPrimitive.target_notMem_interior {γ : Path x y} (h : γ.IsPrimitive) :
    y ∉ γ.Interior := by
  rintro ⟨t, ht, hty⟩
  obtain ht1 | hp := h (hty.trans γ.target.symm)
  · exact (mem_Ioo_iff.mp ht).2 ht1
  · rcases pair_eq_pair_iff.mp hp with ⟨rfl, _⟩ | ⟨rfl, h10⟩
    · exact (mem_Ioo_iff.mp ht).1 rfl
    · exact one_ne_zero h10

lemma IsPrimitive.range_diff_endpoints {γ : Path x y} (h : γ.IsPrimitive) :
    range γ \ {x, y} = γ.Interior := by
  ext z
  constructor
  · rintro ⟨⟨t, rfl⟩, hne⟩
    obtain ht0 | ht1 | ht := eq_zero_or_eq_one_or_mem_Ioo t
    · rw [ht0, Path.source] at hne
      exact (hne (mem_insert _ _)).elim
    · rw [ht1, Path.target] at hne
      exact (hne (by simp)).elim
    · exact ⟨t, ht, rfl⟩
  · intro hz
    refine ⟨interior_subset_range γ hz, ?_⟩
    rintro (rfl | rfl)
    · exact h.source_notMem_interior hz
    · exact h.target_notMem_interior hz

lemma IsPrimitive.range_diff_endpoints_nonempty {γ : Path x y} (h : γ.IsPrimitive) :
    (range γ \ {x, y}).Nonempty := by
  rw [h.range_diff_endpoints]
  exact (nonempty_Ioo.2 (zero_lt_one : (0 : I) < 1)).image _

lemma IsPrimitive.isPathConnected_range_diff_endpoints {γ : Path x y}
    (h : γ.IsPrimitive) : IsPathConnected (range γ \ {x, y}) := by
  rw [h.range_diff_endpoints]
  exact (isPathConnected_Ioo (zero_lt_one : (0 : I) < 1)).image γ.continuous

lemma IsPrimitive.isConnected_range_diff_endpoints {γ : Path x y} (h : γ.IsPrimitive) :
    IsConnected (range γ \ {x, y}) :=
  h.isPathConnected_range_diff_endpoints.isConnected

lemma IsPrimitive.map {Y : Type*} [TopologicalSpace Y] {γ : Path x y} {f : X → Y}
    (h : γ.IsPrimitive) (hf : ContinuousOn f (range γ)) (hinj : InjOn f (range γ)) :
    (γ.map' hf).IsPrimitive := by
  intro s t hst
  exact h (hinj (mem_range_self s) (mem_range_self t) hst)

end Path
