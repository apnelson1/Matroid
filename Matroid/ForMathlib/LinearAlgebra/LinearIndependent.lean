-- import Mathlib.LinearAlgebra.FiniteDimensional
-- import Mathlib.LinearAlgebra.Dual
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.LinearIndependent
import Matroid.ForMathlib.Function

-- import Mathlib.Data.FunLike.Basic

universe u v

variable {α ι W W' M R : Type*} [AddCommGroup W] [AddCommGroup W']

open Function Set Submodule BigOperators

theorem linearIndependent_iff_forall_finite_restrict {R M ι : Type*} [Semiring R] [AddCommGroup M]
    [Module R M] (f : ι → M) :
    LinearIndependent R f ↔ ∀ (t : Set ι), t.Finite → LinearIndependent R (t.restrict f) := by
  rw [linearIndependent_iff_finset_linearIndependent]
  exact ⟨fun h s hs ↦ (h hs.toFinset).comp (fun x : s ↦ ⟨x.1, by simp⟩)
    (fun ⟨x,hx⟩ ⟨y,hy⟩ ↦ by simp), fun h s ↦ (h s (by simp)).comp (fun x : s ↦ ⟨x.1, by simp⟩)
    (fun _ ↦ by simp)⟩

alias ⟨_, linearIndependent_of_forall_finite_restrict⟩ :=
  linearIndependent_iff_forall_finite_restrict

theorem linearIndependent_iUnion_restrict_of_directed {R M ι η : Type*} [Semiring R]
    [AddCommGroup M] [Module R M] (f : ι → M) (s : η → Set ι) (hs : Directed (· ⊆ ·) s)
    (h : ∀ j, LinearIndependent R ((s j).restrict f)) :
    LinearIndependent R ((⋃ j, s j).restrict f) := by
  obtain (h_empt | hne) := isEmpty_or_nonempty η
  · rw [iUnion_of_empty s]
    apply linearIndependent_empty_type
  apply linearIndependent_of_forall_finite_restrict _ (fun t ht ↦ ?_)
  obtain ⟨I, hIfin, hI⟩ :=
    finite_subset_iUnion (ht.image Subtype.val) (Subtype.coe_image_subset (⋃ j, s j) t)
  obtain ⟨z, hz⟩ := hs.finset_le hIfin.toFinset
  have hss : Subtype.val '' t ⊆ s z := by
    refine hI.trans (iUnion_subset fun i j h ↦ ?_)
    simp only [mem_iUnion, exists_prop] at h
    exact hz i (by simpa using h.1) h.2
  set emb : t → s z := (inclusion hss) ∘ (imageFactorization Subtype.val t)
  refine (h z).comp emb <| Function.Injective.comp (inclusion_injective hss) ?_
  exact Subtype.val_injective.injOn.imageFactorization_injective

theorem linearIndependent_sUnion_restrict_of_directed {R M ι : Type*} [DivisionRing R]
    [AddCommGroup M] [Module R M] (f : ι → M) (s : Set (Set ι)) (hs : DirectedOn (· ⊆ ·) s)
    (h : ∀ c ∈ s, LinearIndependent R (c.restrict f)) :
    LinearIndependent R ((⋃₀ s).restrict f) := by
  rw [sUnion_eq_iUnion]
  apply linearIndependent_iUnion_restrict_of_directed _ _ _ (by aesop)
  rintro x y
  specialize hs x x.prop y y.prop
  aesop

-- theorem LinearIndependent.finite_index {K : Type u} {V : Type v} [DivisionRing K] [AddCommGroup V]
--   [Module K V] [FiniteDimensional K V] {f : α → V} (h : LinearIndependent K f) : Finite α :=
--   Cardinal.lt_aleph0_iff_finite.1 <| LinearIndependent.lt_aleph0_of_finiteDimensional h

-- noncomputable def LinearIndependent.fintype_index {K : Type u} {V : Type v} [DivisionRing K]
--     [AddCommGroup V] [Module K V] [FiniteDimensional K V] {f : α → V} (h : LinearIndependent K f) :
--     Fintype α :=
--   have _ := h.finite_index
--   Fintype.ofFinite α

-- theorem LinearIndependent.finite_index_restrict {K : Type u} {V : Type v} [DivisionRing K]
--     [AddCommGroup V] [Module K V] [FiniteDimensional K V] {f : α → V} {s : Set α}
--     (h : LinearIndependent K (s.restrict f)) : s.Finite :=
--   have := h.finite_index
--   s.toFinite

variable {K V ι : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] {f : ι → V}
  {s₀ s t : Set ι}

theorem Submodule.disjoint_of_disjoint_span {R M : Type*} [Semiring R] [AddCommGroup M]
    [Module R M] {s t : Set M} (hst : Disjoint (span R s) (span R t)) :
    Disjoint (s \ {0}) t := by
  rw [disjoint_iff_forall_ne]
  rintro v ⟨hvs, hv0 : v ≠ 0⟩ _ hvt rfl
  exact hv0 <| (disjoint_def.1 hst) v (subset_span hvs) (subset_span hvt)

theorem Submodule.disjoint_of_disjoint_span₀ {R M : Type*} [Semiring R] [AddCommGroup M]
    [Module R M] {s t : Set M} (hst : Disjoint (span R s) (span R t)) (h0s : 0 ∉ s) :
    Disjoint s t := by
  convert disjoint_of_disjoint_span hst
  simp [h0s]

theorem LinearIndependent.zero_not_mem_image {R M ι : Type*} [Semiring R] [Nontrivial R]
    [AddCommGroup M] [Module R M] {s : Set ι} {f : ι → M}
    (hs : LinearIndependent R (s.restrict f)) : 0 ∉ f '' s := by
  simp only [mem_image, not_exists, not_and]
  exact fun i hi ↦ by simpa using hs.ne_zero ⟨i,hi⟩

theorem LinearIndependent.mono_restrict {R M ι : Type*} [DivisionRing R] [AddCommGroup M]
    [Module R M] {f : ι → M} {s t : Set ι} (h : LinearIndependent R (t.restrict f)) (hst : s ⊆ t) :
    LinearIndependent R (s.restrict f) :=
  (linearIndependent_image ((injOn_iff_injective.2 h.injective).mono hst )).2 <|
    h.image.mono (image_subset _ hst)

theorem linearIndependent_restrict_pair_iff {K V ι : Type*} [DivisionRing K] [AddCommGroup V]
  [Module K V] {i j : ι} (f : ι → V) (hij : i ≠ j) (hi : f i ≠ 0):
    LinearIndependent K (({i,j} : Set ι).restrict f) ↔ ∀ (c : K), c • f i ≠ f j := by
  rw [pair_comm]
  convert linearIndependent_insert' (s := {i}) (a := j) hij.symm
  simp [hi, mem_span_singleton, linearIndependent_unique_iff]

theorem LinearIndependent.restrict_union {R M ι : Type*} [DivisionRing R] [AddCommGroup M]
    [Module R M] {s t : Set ι} {f : ι → M} (hs : LinearIndependent R (s.restrict f))
    (ht : LinearIndependent R (t.restrict f)) (hdj : Disjoint (span R (f '' s)) (span R (f '' t))) :
    LinearIndependent R ((s ∪ t).restrict f) := by
  refine (linearIndependent_image ?_).2 <|
   (hs.image.union ht.image hdj).comp (Equiv.Set.ofEq (image_union ..)) (Equiv.injective _)
  have hst := Submodule.disjoint_of_disjoint_span₀ hdj hs.zero_not_mem_image
  rw [injOn_union hst.of_image, injOn_iff_injective, injOn_iff_injective]
  exact ⟨hs.injective, ht.injective,
    fun x hxs y hyt ↦ hst.ne_of_mem (mem_image_of_mem f hxs) (mem_image_of_mem f hyt)⟩

theorem linearIndependent_restrict_union_iff {R M ι : Type*} [DivisionRing R] [AddCommGroup M]
    [Module R M] {s t : Set ι} {f : ι → M} (hdj : Disjoint s t) :
    LinearIndependent R ((s ∪ t).restrict f) ↔
    (LinearIndependent R (s.restrict f)) ∧ (LinearIndependent R (t.restrict f))
    ∧ Disjoint (span R (f '' s)) (span R (f '' t)) := by
  refine ⟨fun h ↦ ⟨h.mono_restrict subset_union_left, h.mono_restrict subset_union_right, ?_⟩,
    fun h ↦ LinearIndependent.restrict_union h.1 h.2.1 h.2.2⟩
  convert h.disjoint_span_image (s := (↑) ⁻¹' s) (t := (↑) ⁻¹' t) (hdj.preimage _) <;>
  aesop

theorem LinearIndependent.restrict_union_of_quotient {R M ι : Type*} [DivisionRing R]
    [AddCommGroup M] [Module R M] {s t : Set ι} {f : ι → M}
    (hs : LinearIndependent R (s.restrict f))
    (ht : LinearIndependent R (t.restrict ( (mkQ (span R (f '' s)) ∘ f)))) :
    LinearIndependent R ((s ∪ t).restrict f) := by
  apply hs.restrict_union ht.of_comp
  convert (Submodule.range_ker_disjoint ht).symm
  · simp
  aesop

theorem linearIndependent_restrict_union_iff_quotient {R M ι : Type*} [DivisionRing R]
    [AddCommGroup M] [Module R M] {s t : Set ι} {f : ι → M} (hst : Disjoint s t) :
    LinearIndependent R ((s ∪ t).restrict f) ↔ LinearIndependent R (s.restrict f)
      ∧ LinearIndependent R (t.restrict ((mkQ (span R (f '' s)) ∘ f))) := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ h.1.restrict_union_of_quotient h.2⟩
  · exact h.mono_restrict (f := f) subset_union_left
  apply (h.mono_restrict (f := f) subset_union_right).map
  simp only [range_restrict, ker_mkQ]
  exact ((linearIndependent_restrict_union_iff hst).1 h).2.2.symm

theorem LinearIndependent.quotient_iff_union {R M ι : Type*} [DivisionRing R] [AddCommGroup M]
    [Module R M] {s t : Set ι} {f : ι → M} (hs : LinearIndependent R (s.restrict f))
    (hst : Disjoint s t) : LinearIndependent R (t.restrict ((mkQ (span R (f '' s)) ∘ f))) ↔
    LinearIndependent R ((s ∪ t).restrict f) := by
  rw [linearIndependent_restrict_union_iff_quotient hst, and_iff_right hs]

@[simp]
theorem linearIndependent_zero_coeSet_iff {R M ι : Type*} [Ring R] [Nontrivial R] [AddCommGroup M]
    [Module R M] {s : Set ι} : LinearIndependent R (0 : s → M) ↔ s = ∅ := by
  rw [linearIndependent_zero_iff, isEmpty_coe_sort]

section extend

theorem exists_linearIndependent_extension_restrict (hli : LinearIndependent K (s₀.restrict f))
    (hs₀t : s₀ ⊆ t) : ∃ s ⊆ t, s₀ ⊆ s ∧ f '' t ⊆ span K (f '' s) ∧
    LinearIndependent K (s.restrict f) := by
  have hzorn := zorn_subset_nonempty
    {r | s₀ ⊆ r ∧ r ⊆ t ∧ LinearIndependent K (r.restrict f)} ?_ s₀ ⟨Subset.rfl, hs₀t, hli⟩
  · obtain ⟨m, hs₀m, hmax⟩ := hzorn
    refine ⟨m, hmax.prop.2.1, hs₀m, ?_, hmax.prop.2.2⟩
    rintro _ ⟨x, hx, rfl⟩
    by_contra hxm
    have hxm' : x ∉ m := fun hxm' ↦ hxm <| subset_span <| mem_image_of_mem _ hxm'
    have hli' := (linearIndependent_insert' hxm').2 ⟨hmax.prop.2.2, hxm⟩
    exact hxm' <| hmax.mem_of_prop_insert (x := x) ⟨hmax.prop.1.trans (subset_insert ..),
      insert_subset hx hmax.prop.2.1, hli'⟩
  refine fun c hcss hchain ⟨r, hr⟩ ↦ ⟨⋃₀ c, ⟨(hcss hr).1.trans <| subset_sUnion_of_mem hr,
    sUnion_subset fun t' ht'c ↦ (hcss ht'c).2.1,?_⟩, fun _ ↦ subset_sUnion_of_mem⟩
  apply linearIndependent_sUnion_restrict_of_directed _ _ (IsChain.directedOn hchain)
    (fun s hs ↦ (hcss hs).2.2)

theorem exists_linearIndependent_extension' {s t : Set V}
    (hs : LinearIndependent K (fun (x : s) ↦ x.1))
    (hst : s ⊆ t) : ∃ b ⊆ t, s ⊆ b ∧ t ⊆ ↑(span K b) ∧ LinearIndependent K (fun (x : b) ↦ x.1) := by
  convert exists_linearIndependent_extension_restrict (f := id) hs hst <;>
  simp

noncomputable def LinearIndependent.extend_index (h : LinearIndependent K (s.restrict f)) (hst : s ⊆ t) :
    Set ι :=
  Classical.choose <| exists_linearIndependent_extension_restrict h hst

theorem LinearIndependent.extend_index_subset (h : LinearIndependent K (s.restrict f))
    (hst : s ⊆ t) : h.extend_index hst ⊆ t :=
  (Classical.choose_spec (exists_linearIndependent_extension_restrict h hst)).1

theorem LinearIndependent.subset_extend' (h : LinearIndependent K (s.restrict f)) (hst : s ⊆ t) :
    s ⊆ h.extend_index hst :=
  (Classical.choose_spec (exists_linearIndependent_extension_restrict h hst)).2.1

theorem LinearIndependent.subset_span_extend' (h : LinearIndependent K (s.restrict f))
    (hst : s ⊆ t) : f '' t ⊆ span K (f '' (h.extend_index hst)) :=
  (Classical.choose_spec (exists_linearIndependent_extension_restrict h hst)).2.2.1

theorem LinearIndependent.linearIndependent_extend' (h : LinearIndependent K (s.restrict f))
    (hst : s ⊆ t) : LinearIndependent K ((h.extend_index hst).restrict f) :=
  (Classical.choose_spec (exists_linearIndependent_extension_restrict h hst)).2.2.2
