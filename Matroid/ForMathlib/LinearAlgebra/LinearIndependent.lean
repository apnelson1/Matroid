-- import Mathlib.LinearAlgebra.FiniteDimensional
-- import Mathlib.LinearAlgebra.Dual
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.LinearIndependent
import Matroid.ForMathlib.Function

-- import Mathlib.Data.FunLike.Basic

universe u v

variable {α ι W W' M R : Type*} [AddCommGroup W] [AddCommGroup W']

open Function Set Submodule BigOperators

-- theorem Fintype.not_linearIndependent_restrict_iff [Fintype ι] [CommSemiring R] [AddCommMonoid M]
--     [Module R M] {s : Finset ι} {f : ι → M} : ¬ LinearIndependent R ((s : Set ι).restrict f) ↔
--       ∃ c : ι → R, ∑ i, c i • f i = 0 ∧ (∃ i ∈ s, c i ≠ 0) ∧ ∀ i, i ∉ s → c i = 0 := by
--   simp only [Finset.coe_sort_coe, not_linearIndependent_iff, Finset.univ_eq_attach, restrict_apply,
--     ne_eq, Subtype.exists, Finset.mem_coe]
--   refine ⟨fun ⟨g, hg0, b, hbs, hgb⟩ ↦ ?_, fun ⟨c,hc0,⟨b,hbs, hb0⟩,hc'⟩ ↦ ?_⟩
--   · set c := Function.extend Subtype.val g 0 with hc
--     have hc0 : ∀ x ∉ s, c x = 0 :=
--       fun x hxs ↦ by rw [hc, extend_apply' _ _ _ (by simpa), Pi.zero_apply]
--     have hc1 : ∀ x : s, c x = g x :=
--       fun ⟨x,hx⟩ ↦ by rw [hc, Subtype.val_injective.extend_apply]
--     refine ⟨c, ?_, ⟨b, hbs, by rwa [← hc1] at hgb⟩, hc0⟩
--     · rw [← Finset.sum_subset s.subset_univ (fun x _ hx ↦ by simp [hc0 x hx]), ← Finset.sum_attach]
--       simp_rw [hc1]; assumption
--   refine ⟨c ∘ Subtype.val, ?_, b, hbs, by simpa⟩
--   simp only [comp_apply]
--   rwa [s.sum_attach (fun x ↦ c x • f x),
--     Finset.sum_subset (s.subset_univ) (fun x _ hx ↦ by simp [hc' x hx])]

-- theorem Fintype.not_linearIndependent_restrict_iff' [Fintype ι] [CommSemiring R] [AddCommMonoid M]
--     [Module R M] {s : Set ι} {f : ι → M} : ¬ LinearIndependent R (s.restrict f) ↔
--       ∃ c : ι → R, ∑ i, c i • f i = 0 ∧ (∃ i ∈ s, c i ≠ 0) ∧ ∀ i, i ∉ s → c i = 0 := by
--   obtain ⟨s,rfl⟩ := s.toFinite.exists_finset_coe
--   exact Fintype.not_linearIndependent_restrict_iff

-- theorem linearIndependent_restrict_iff [Semiring R] [AddCommMonoid M] [Module R M] {s : Set ι}
--     {f : ι → M} : LinearIndependent R (s.restrict f) ↔
--       ∀ l : ι →₀ R, Finsupp.total ι M R f l = 0 → (l.support : Set ι) ⊆ s → l = 0 := by
--   classical
--   rw [linearIndependent_iff]
--   refine ⟨fun h l hl0 hls ↦ ?_, fun h l hl0 ↦ ?_⟩
--   · rw [Finsupp.total_apply, Finsupp.sum_of_support_subset _ Subset.rfl _ (by simp)] at hl0
--     specialize h (Finsupp.comapDomain ((↑) : s → ι) l Subtype.val_injective.injOn)
--     simp only [Finsupp.total_comapDomain, restrict_apply] at h
--     rw [Finset.sum_preimage _ _ _ (fun x ↦ l x • f x)
--       (fun x hx hx' ↦ (hx' (by simpa using hls hx)).elim )] at h
--     simp_rw [DFunLike.ext_iff] at h ⊢
--     exact fun i ↦ by_contra fun hi ↦ hi <|
--       by simpa using (h hl0) ⟨i, hls (show i ∈ l.support by simpa using hi)⟩
--   specialize h l.extendDomain
--   rw [Finsupp.extendDomain_eq_embDomain_subtype, Finsupp.total_embDomain] at h
--   simp only [Embedding.coe_subtype, Finsupp.support_embDomain, Finset.coe_map, image_subset_iff,
--     Subtype.coe_preimage_self, subset_univ, Finsupp.embDomain_eq_zero, forall_true_left] at h
--   exact h hl0

@[simp]
theorem linearIndependent_subsingleton_index {R M ι : Type*} [DivisionRing R] [AddCommGroup M]
    [Module R M] [Subsingleton ι] (f : ι → M) : LinearIndependent R f ↔ ∀ i, f i ≠ 0 := by
  obtain (he | he) := isEmpty_or_nonempty ι
  · simp [linearIndependent_empty_type]
  obtain ⟨_⟩ := (unique_iff_subsingleton_and_nonempty (α := ι)).2 ⟨by assumption, he⟩
  rw [linearIndependent_unique_iff]
  exact ⟨fun h i ↦ by rwa [Unique.eq_default i], fun h ↦ h _⟩

@[simp]
theorem linearIndependent_subsingleton_iff {R M ι : Type*} [DivisionRing R] [AddCommGroup M]
    [Module R M] [Subsingleton M] (f : ι → M) : LinearIndependent R f ↔ IsEmpty ι := by
  obtain h | i := isEmpty_or_nonempty ι
  · simpa
  exact iff_of_false (fun hli ↦ hli.ne_zero i.some (Subsingleton.eq_zero (f i.some))) (by simp)

theorem linearIndependent_of_finite_index {R M ι : Type*} [DivisionRing R] [AddCommGroup M]
    [Module R M] (f : ι → M) (h : ∀ (t : Set ι), t.Finite → LinearIndependent R (t.restrict f)) :
    LinearIndependent R f := by
  have hinj : f.Injective := by
    intro x y hxy
    have hli := (h {x,y} (toFinite _))
    have h : (⟨x, by simp⟩ : ({x,y} : Set ι)) = ⟨y, by simp⟩ := by
      rw [← hli.injective.eq_iff]; simpa
    simpa using h
  rw [← linearIndependent_subtype_range hinj]
  refine linearIndependent_of_finite _ fun t ht htfin ↦ ?_
  obtain ⟨t, rfl⟩ := subset_range_iff_exists_image_eq.1 ht
  exact (linearIndependent_image (injOn_of_injective hinj)).1 <|
    h t (htfin.of_finite_image (injOn_of_injective hinj))


theorem linearIndependent_iUnion_of_directed' {R M ι η : Type*} [DivisionRing R] [AddCommGroup M]
    [Module R M] (f : ι → M) (s : η → Set ι) (hs : Directed (· ⊆ ·) s)
    (h : ∀ j, LinearIndependent R ((s j).restrict f)) :
    LinearIndependent R ((⋃ j, s j).restrict f) := by
  obtain (h_empt | hne) := isEmpty_or_nonempty η
  · rw [iUnion_of_empty s]
    apply linearIndependent_empty_type
  apply linearIndependent_of_finite_index _ (fun t ht ↦ ?_)
  obtain ⟨I,hIfin, hI⟩ :=
    finite_subset_iUnion (ht.image Subtype.val) (Subtype.coe_image_subset (⋃ j, s j) t)
  obtain ⟨z, hz⟩ := hs.finset_le hIfin.toFinset
  have hss : Subtype.val '' t ⊆ s z := by
    refine hI.trans (iUnion_subset fun i j h ↦ ?_)
    simp only [mem_iUnion, exists_prop] at h
    exact hz i (by simpa using h.1) h.2
  set emb : t → s z := (inclusion hss) ∘ (imageFactorization Subtype.val t)
  refine (h z).comp emb <| Function.Injective.comp (inclusion_injective hss) ?_
  exact Subtype.val_injective.injOn.imageFactorization_injective

theorem linearIndependent_sUnion_of_directed' {R M ι : Type*} [DivisionRing R] [AddCommGroup M]
    [Module R M] (f : ι → M) (s : Set (Set ι)) (hs : DirectedOn (· ⊆ ·) s)
    (h : ∀ c ∈ s, LinearIndependent R (c.restrict f)) :
    LinearIndependent R ((⋃₀ s).restrict f) := by
  rw [sUnion_eq_iUnion]
  apply linearIndependent_iUnion_of_directed' _ _ _ (by aesop)
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


theorem LinearIndependent.mono_restrict {R M ι : Type*} [DivisionRing R] [AddCommGroup M]
    [Module R M] (f : ι → M) {s t : Set ι} (h : LinearIndependent R (t.restrict f)) (hst : s ⊆ t) :
    LinearIndependent R (s.restrict f) :=
  (linearIndependent_image ((injOn_iff_injective.2 h.injective).mono hst )).2 <|
    h.image.mono (image_subset _ hst)

theorem linearIndependent_restrict_pair_iff {K V ι : Type*} [DivisionRing K] [AddCommGroup V]
  [Module K V] {i j : ι} (f : ι → V) (hij : i ≠ j) (hi : f i ≠ 0):
    LinearIndependent K (({i,j} : Set ι).restrict f) ↔ ∀ (c : K), c • f i ≠ f j := by
  convert linearIndependent_insert' (s := {j}) (a := i) (by simpa using hij) using 2
  simp only [ne_eq, linearIndependent_unique_iff, default_coe_singleton, image_singleton,
    mem_span_singleton, not_exists]
  refine ⟨fun h ↦ ⟨fun h0 ↦ ?_, fun c hc ↦ h c⁻¹ ?_⟩, fun h c h' ↦ h.2 c⁻¹ ?_⟩
  · simp only [h0, smul_eq_zero] at h
    simpa using h 0
  · rw [← hc, smul_smul, inv_mul_cancel₀, one_smul]
    rintro rfl; exact hi <| by simp [← hc]
  rw [← h', smul_smul, inv_mul_cancel₀, one_smul]
  rintro rfl; exact h.1 <| by simp [← h']

theorem LinearIndependent.restrict_union {R M ι : Type*} [DivisionRing R] [AddCommGroup M] [Module R M]
    {s t : Set ι} {f : ι → M} (hs : LinearIndependent R (s.restrict f))
    (ht : LinearIndependent R (t.restrict f)) (hdj : Disjoint (span R (f '' s)) (span R (f '' t))) :
    LinearIndependent R ((s ∪ t).restrict f) := by
  have aux : ∀ x ∈ s, ∀ y ∈ t, f x ≠ f y := by
    refine fun x hx y hy hxy ↦ hs.ne_zero ⟨x, hx⟩ ?_
    exact Submodule.disjoint_def'.1 hdj _ (subset_span (mem_image_of_mem f hx)) _
      (subset_span (mem_image_of_mem f hy)) hxy
  have hdj' : Disjoint s t := by
    rw [disjoint_iff_forall_ne]
    rintro x hx _ hx' rfl
    exact aux _ hx _ hx' rfl
  have hli := LinearIndependent.union hs.image ht.image hdj
  rw [← image_union] at hli
  refine (linearIndependent_image ?_).2 hli
  rw [injOn_union hdj', injOn_iff_injective, injOn_iff_injective]
  exact ⟨hs.injective, ht.injective, aux⟩

theorem linearIndependent_restrict_union_iff {R M ι : Type*} [DivisionRing R] [AddCommGroup M]
    [Module R M] {s t : Set ι} {f : ι → M} (hdj : Disjoint s t) :
    LinearIndependent R ((s ∪ t).restrict f) ↔
    (LinearIndependent R (s.restrict f)) ∧ (LinearIndependent R (t.restrict f))
    ∧ Disjoint (span R (f '' s)) (span R (f '' t)) := by
  refine ⟨fun h ↦ ⟨?_, ?_, ?_⟩, fun h ↦ LinearIndependent.restrict_union  h.1 h.2.1 h.2.2⟩
  · exact LinearIndependent.mono_restrict (f := f) h subset_union_left
  · exact LinearIndependent.mono_restrict (f := f) h subset_union_right
  convert h.disjoint_span_image (s := (↑) ⁻¹' s) (t := (↑) ⁻¹' t) (hdj.preimage _) <;> aesop

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

theorem linearIndependent_zero_iff {R M ι : Type*} [Ring R] [Nontrivial R] [AddCommGroup M]
    [Module R M] : LinearIndependent R (0 : ι → M) ↔ IsEmpty ι := by
  refine ⟨fun h ↦ ?_, fun h ↦ linearIndependent_empty_type⟩
  obtain (h | ⟨⟨i⟩⟩) := isEmpty_or_nonempty ι; assumption
  exact False.elim <| h.ne_zero i rfl

@[simp] theorem linearIndependent_zero_iff' {R M ι : Type*} [Ring R] [Nontrivial R] [AddCommGroup M]
    [Module R M] {s : Set ι} : LinearIndependent R (0 : s → M) ↔ s = ∅ := by
  rw [linearIndependent_zero_iff, isEmpty_coe_sort]

-- /-- Independently scaling each vector by a unit preserves linear independence. -/
-- lemma LinearIndependent.unitMul {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M] {f : ι → M}
--     (h : LinearIndependent R f) (a : ι → Rˣ) : LinearIndependent R (fun i ↦ (a i) • (f i)) := by
--   refine linearIndependent_iff.2 fun c hc ↦ ?_
--   let c' : ι →₀ R := ⟨c.support, fun i ↦ (c i) * (a i), by simp⟩
--   have hc' : (Finsupp.linearCombination R f) c' = 0 := by
--     have hrw (x) : c' x • f x = c x • a x • f x := by
--       simp [c', ← smul_eq_mul, @Units.smul_def]
--     simp_rw [Finsupp.linearCombination_apply, Finsupp.sum, hrw]
--     rwa [Finsupp.linearCombination_apply, Finsupp.sum] at hc
--   simpa [c', Finsupp.ext_iff] using (linearIndependent_iff.1 h) c' hc'

-- @[simp] lemma LinearIndependent.unitMul_iff {R M ι : Type*} [Ring R] [AddCommGroup M]
--     [Module R M] {f : ι → M} {a : ι → Rˣ} :
--     LinearIndependent R (fun i ↦ (a i) • (f i)) ↔ LinearIndependent R f :=
--   ⟨fun h ↦ by simpa using h.unitMul fun i ↦ (a i)⁻¹ , fun h ↦ h.unitMul a⟩

section extend


theorem exists_linearIndependent_extension_index (hli : LinearIndependent K (s₀.restrict f))
    (hs₀t : s₀ ⊆ t) : ∃ (s : Set ι), s₀ ⊆ s ∧ s ⊆ t ∧ f '' t ⊆ span K (f '' s) ∧
      LinearIndependent K (s.restrict f) := by
  have hzorn := zorn_subset_nonempty {r | s₀ ⊆ r ∧ r ⊆ t ∧ LinearIndependent K (r.restrict f)}
    ?_ s₀ ⟨Subset.rfl, hs₀t, hli⟩
  · obtain ⟨m, hs₀m, hmax⟩ := hzorn
    refine ⟨m, hs₀m, hmax.prop.2.1, ?_, hmax.prop.2.2⟩
    rintro _ ⟨x, hx, rfl⟩
    by_contra hxm
    have hxm' : x ∉ m := fun hxm' ↦ hxm <| subset_span <| mem_image_of_mem _ hxm'
    have hli' := (linearIndependent_insert' hxm').2 ⟨hmax.prop.2.2, hxm⟩
    exact hxm' <| hmax.mem_of_prop_insert (x := x) ⟨hmax.prop.1.trans (subset_insert ..),
      insert_subset hx hmax.prop.2.1, hli'⟩
  rintro c hcss hchain ⟨r, hr⟩
  refine ⟨⋃₀ c, ⟨(hcss hr).1.trans <| subset_sUnion_of_mem hr,
    sUnion_subset fun t' ht'c ↦ (hcss ht'c).2.1,?_⟩, fun _ ↦ subset_sUnion_of_mem⟩
  apply linearIndependent_sUnion_of_directed' _ _ (IsChain.directedOn hchain)
    (fun s hs ↦ (hcss hs).2.2)

noncomputable def LinearIndependent.extend_index (h : LinearIndependent K (s.restrict f)) (hst : s ⊆ t) :
    Set ι :=
  Classical.choose <| exists_linearIndependent_extension_index h hst

theorem LinearIndependent.extend_index_subset (h : LinearIndependent K (s.restrict f)) (hst : s ⊆ t) :
    h.extend_index hst ⊆ t :=
  (Classical.choose_spec (exists_linearIndependent_extension_index h hst)).2.1

theorem LinearIndependent.subset_extend' (h : LinearIndependent K (s.restrict f)) (hst : s ⊆ t) :
    s ⊆ h.extend_index hst :=
  (Classical.choose_spec (exists_linearIndependent_extension_index h hst)).1

theorem LinearIndependent.subset_span_extend' (h : LinearIndependent K (s.restrict f))
    (hst : s ⊆ t) : f '' t ⊆ span K (f '' (h.extend_index hst)) :=
  (Classical.choose_spec (exists_linearIndependent_extension_index h hst)).2.2.1

theorem LinearIndependent.linearIndependent_extend' (h : LinearIndependent K (s.restrict f))
    (hst : s ⊆ t) : LinearIndependent K ((h.extend_index hst).restrict f) :=
  (Classical.choose_spec (exists_linearIndependent_extension_index h hst)).2.2.2

@[simp] theorem LinearIndependent.units_smul_iff {R M ι : Type*} [Ring R] [AddCommGroup M]
    [Module R M] {v : ι → M} {w : ι → Rˣ} :
    LinearIndependent R (w • v) ↔ LinearIndependent R v := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.units_smul w⟩
  convert h.units_smul (fun i ↦ (w i)⁻¹)
  simp [funext_iff]
