import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.Dual
import Mathlib.LinearAlgebra.Quotient
import Matroid.ForMathlib.Function

-- import Mathlib.Data.FunLike.Basic

universe u v

variable {α ι W W' M R : Type*} [AddCommGroup W] [AddCommGroup W']

open Function Set Submodule BigOperators

theorem Fintype.not_linearIndependent_restrict_iff [Fintype ι] [CommSemiring R]
    [AddCommMonoid M] [Module R M] {s : Finset ι} {f : ι → M} :
    ¬ LinearIndependent R ((s : Set ι).restrict f) ↔
      ∃ c : ι → R, ∑ i, c i • f i = 0 ∧ (∃ i ∈ s, c i ≠ 0) ∧ ∀ i, i ∉ s → c i = 0 := by
  simp only [Finset.coe_sort_coe, not_linearIndependent_iff, Finset.univ_eq_attach, restrict_apply,
    ne_eq, Subtype.exists, Finset.mem_coe]
  refine ⟨fun ⟨g, hg0, b, hbs, hgb⟩ ↦ ?_, fun ⟨c,hc0,⟨b,hbs, hb0⟩,hc'⟩ ↦ ?_⟩
  · set c := Function.extend Subtype.val g 0 with hc
    have hc0 : ∀ x ∉ s, c x = 0 :=
      fun x hxs ↦ by rw [hc, extend_apply' _ _ _ (by simpa), Pi.zero_apply]
    have hc1 : ∀ x : s, c x = g x :=
      fun ⟨x,hx⟩ ↦ by rw [hc, Subtype.val_injective.extend_apply]
    refine ⟨c, ?_, ⟨b, hbs, by rwa [← hc1] at hgb⟩, hc0⟩
    · rw [← Finset.sum_subset s.subset_univ (fun x _ hx ↦ by simp [hc0 x hx]), ← Finset.sum_attach]
      simp_rw [hc1]; assumption
  refine ⟨c ∘ Subtype.val, ?_, b, hbs, by simpa⟩
  simp only [comp_apply]
  rwa [s.sum_attach (fun x ↦ c x • f x),
    Finset.sum_subset (s.subset_univ) (fun x _ hx ↦ by simp [hc' x hx])]

theorem Fintype.not_linearIndependent_restrict_iff' [Fintype ι] [CommSemiring R]
    [AddCommMonoid M] [Module R M] {s : Set ι} {f : ι → M} :
    ¬ LinearIndependent R (s.restrict f) ↔
      ∃ c : ι → R, ∑ i, c i • f i = 0 ∧ (∃ i ∈ s, c i ≠ 0) ∧ ∀ i, i ∉ s → c i = 0 := by
  obtain ⟨s,rfl⟩ := s.toFinite.exists_finset_coe
  exact Fintype.not_linearIndependent_restrict_iff

theorem linearIndependent_restrict_iff [Semiring R] [AddCommMonoid M] [Module R M] {s : Set ι}
    {f : ι → M} : LinearIndependent R (s.restrict f) ↔
      ∀ l : ι →₀ R, Finsupp.total ι M R f l = 0 → (l.support : Set ι) ⊆ s → l = 0 := by
  classical
  rw [linearIndependent_iff]
  refine ⟨fun h l hl0 hls ↦ ?_, fun h l hl0 ↦ ?_⟩
  · rw [Finsupp.total_apply, Finsupp.sum_of_support_subset _ Subset.rfl _ (by simp)] at hl0
    specialize h (Finsupp.comapDomain ((↑) : s → ι) l (Subtype.val_injective.injOn _))
    simp only [Finsupp.total_comapDomain, restrict_apply] at h
    rw [Finset.sum_preimage _ _ _ (fun x ↦ l x • f x)
      (fun x hx hx' ↦ (hx' (by simpa using hls hx)).elim )] at h
    simp_rw [DFunLike.ext_iff] at h ⊢
    exact fun i ↦ by_contra fun hi ↦ hi <|
      by simpa using (h hl0) ⟨i, hls (show i ∈ l.support by simpa using hi)⟩
  specialize h l.extendDomain
  rw [Finsupp.extendDomain_eq_embDomain_subtype, Finsupp.total_embDomain] at h
  simp only [Embedding.coe_subtype, Finsupp.support_embDomain, Finset.coe_map, image_subset_iff,
    Subtype.coe_preimage_self, subset_univ, Finsupp.embDomain_eq_zero, forall_true_left] at h
  exact h hl0

theorem linearIndependent_subsingleton_index {R M ι : Type*} [DivisionRing R] [AddCommGroup M]
    [Module R M] [Subsingleton ι] {f : ι → M} : LinearIndependent R f ↔ ∀ i, f i ≠ 0 := by
  obtain (he | he) := isEmpty_or_nonempty ι
  · simp [linearIndependent_empty_type]
  obtain ⟨_⟩ := (unique_iff_subsingleton_and_nonempty (α := ι)).2 ⟨by assumption, he⟩
  rw [linearIndependent_unique_iff]
  exact ⟨fun h i ↦ by rwa [Unique.eq_default i], fun h ↦ h _⟩

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
  exact (linearIndependent_image (injOn_of_injective hinj t)).1 <|
    h t (htfin.of_finite_image (injOn_of_injective hinj t))

theorem LinearIndependent.mono_index {R M ι : Type*} [DivisionRing R] [AddCommGroup M]
    [Module R M] (f : ι → M) {s t : Set ι} (h : LinearIndependent R (t.restrict f)) (hst : s ⊆ t) :
    LinearIndependent R (s.restrict f) :=
  (linearIndependent_image ((injOn_iff_injective.2 h.injective).mono hst )).2 <|
    h.image.mono (image_subset _ hst)

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
  exact (Subtype.val_injective.injOn _).imageFactorization_injective

theorem linearIndependent_sUnion_of_directed' {R M ι : Type*} [DivisionRing R] [AddCommGroup M]
    [Module R M] (f : ι → M) (s : Set (Set ι)) (hs : DirectedOn (· ⊆ ·) s)
    (h : ∀ c ∈ s, LinearIndependent R (c.restrict f)) :
    LinearIndependent R ((⋃₀ s).restrict f) := by
  rw [sUnion_eq_iUnion]
  apply linearIndependent_iUnion_of_directed' _ _ _ (by aesop)
  rintro x y
  specialize hs x x.prop y y.prop
  aesop

theorem LinearIndependent.finite_index {K : Type u} {V : Type v} [DivisionRing K] [AddCommGroup V]
  [Module K V] [FiniteDimensional K V] {f : α → V} (h : LinearIndependent K f) : Finite α :=
  Cardinal.lt_aleph0_iff_finite.1 <| LinearIndependent.lt_aleph0_of_finiteDimensional h

noncomputable def LinearIndependent.fintype_index {K : Type u} {V : Type v} [DivisionRing K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {f : α → V} (h : LinearIndependent K f) :
    Fintype α :=
  have _ := h.finite_index
  Fintype.ofFinite α

theorem LinearIndependent.finite_index_restrict {K : Type u} {V : Type v} [DivisionRing K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {f : α → V} {s : Set α}
    (h : LinearIndependent K (s.restrict f)) : s.Finite :=
  have := h.finite_index
  s.toFinite

variable {K V ι : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] {f : ι → V}
  {s₀ s t : Set ι}

theorem exists_linearIndependent_extension' (hli : LinearIndependent K (s₀.restrict f))
    (hs₀t : s₀ ⊆ t) : ∃ (s : Set ι), s₀ ⊆ s ∧ s ⊆ t ∧ f '' t ⊆ span K (f '' s) ∧
      LinearIndependent K (s.restrict f) := by
  have hzorn := zorn_subset_nonempty {r | s₀ ⊆ r ∧ r ⊆ t ∧ LinearIndependent K (r.restrict f)}
    ?_ s₀ ⟨Subset.rfl, hs₀t, hli⟩
  · obtain ⟨m, ⟨hs₀m, hmt, hli⟩, -, hmax⟩ := hzorn
    refine ⟨m, hs₀m, hmt, ?_, hli⟩
    rintro _ ⟨x, hx, rfl⟩
    by_contra hxm
    have hxm' : x ∉ m := fun hxm' ↦ hxm <| subset_span <| mem_image_of_mem _ hxm'
    have hli' := (linearIndependent_insert' hxm').2 ⟨hli, hxm⟩
    rw [← hmax _ ⟨hs₀m.trans <| subset_insert _ _, insert_subset hx hmt, hli'⟩ (subset_insert _ _)]
      at hxm'
    exact hxm' <| mem_insert _ _
  rintro c hcss hchain ⟨r, hr⟩
  refine ⟨⋃₀ c, ⟨(hcss hr).1.trans <| subset_sUnion_of_mem hr,
    sUnion_subset fun t' ht'c ↦ (hcss ht'c).2.1,?_⟩, fun _ ↦ subset_sUnion_of_mem⟩
  apply linearIndependent_sUnion_of_directed' _ _ (IsChain.directedOn hchain)
    (fun s hs ↦ (hcss hs).2.2)

noncomputable def LinearIndependent.extend' (h : LinearIndependent K (s.restrict f)) (hst : s ⊆ t) :
    Set ι :=
  Classical.choose <| exists_linearIndependent_extension' h hst

theorem LinearIndependent.extend'_subset (h : LinearIndependent K (s.restrict f)) (hst : s ⊆ t) :
    h.extend' hst ⊆ t :=
  (Classical.choose_spec (exists_linearIndependent_extension' h hst)).2.1

theorem LinearIndependent.subset_extend' (h : LinearIndependent K (s.restrict f)) (hst : s ⊆ t) :
    s ⊆ h.extend' hst :=
  (Classical.choose_spec (exists_linearIndependent_extension' h hst)).1

theorem LinearIndependent.subset_span_extend' (h : LinearIndependent K (s.restrict f))
    (hst : s ⊆ t) : f '' t ⊆ span K (f '' (h.extend' hst)) :=
  (Classical.choose_spec (exists_linearIndependent_extension' h hst)).2.2.1

theorem LinearIndependent.linearIndependent_extend' (h : LinearIndependent K (s.restrict f))
    (hst : s ⊆ t) : LinearIndependent K ((h.extend' hst).restrict f) :=
  (Classical.choose_spec (exists_linearIndependent_extension' h hst)).2.2.2

theorem linearIndependent_restrict_pair_iff {K V ι : Type*} [DivisionRing K] [AddCommGroup V]
  [Module K V] {i j : ι} (f : ι → V) (hij : i ≠ j) (hi : f i ≠ 0):
    LinearIndependent K (({i,j} : Set ι).restrict f) ↔ ∀ (c : K), c • f i ≠ f j := by
  convert linearIndependent_insert' (s := {j}) (a := i) (by simpa using hij) using 2
  simp only [ne_eq, linearIndependent_unique_iff, default_coe_singleton, image_singleton,
    mem_span_singleton, not_exists]
  refine ⟨fun h ↦ ⟨fun h0 ↦ ?_, fun c hc ↦ h c⁻¹ ?_⟩, fun h c h' ↦ h.2 c⁻¹ ?_⟩
  · simp only [h0, smul_eq_zero] at h
    simpa using h 0
  · rw [← hc, smul_smul, inv_mul_cancel, one_smul]
    rintro rfl; exact hi <| by simp [← hc]
  rw [← h', smul_smul, inv_mul_cancel, one_smul]
  rintro rfl; exact h.1 <| by simp [← h']

theorem linearIndependent.union_index {R M ι : Type*} [Field R] [AddCommGroup M] [Module R M]
    {s t : Set ι} {f : ι → M} (hs : LinearIndependent R (s.restrict f))
    (ht : LinearIndependent R (t.restrict f)) (hdj : Disjoint (span R (f '' s)) (span R (f '' t))) :
    LinearIndependent R ((s ∪ t).restrict f) := by
  refine (linearIndependent_image ?_).2 ?_
  · rw [injOn_union, and_iff_right <| injOn_iff_injective.2 hs.injective,
      and_iff_right <| injOn_iff_injective.2 ht.injective]
    · intro x hx y hy he
      rw [Submodule.disjoint_def] at hdj
      apply hs.ne_zero ⟨x,hx⟩
      simp [hdj _ (subset_span (mem_image_of_mem _ hx))
        (by rw [he]; exact subset_span (mem_image_of_mem _ hy))]
    rw [disjoint_iff_forall_ne]
    rintro i his _ hit rfl
    apply hs.ne_zero ⟨i, his⟩
    exact (Submodule.disjoint_def.1 hdj) (f i) (subset_span (mem_image_of_mem _ his))
      (subset_span (mem_image_of_mem _ hit))
  rw [image_union]
  exact LinearIndependent.union hs.image ht.image hdj

theorem LinearIndependent.union_index' {R M ι : Type*} [Field R] [AddCommGroup M] [Module R M]
    {s t : Set ι} {f : ι → M} (hs : LinearIndependent R (s.restrict f))
    (ht : LinearIndependent R (t.restrict ( (mkQ (span R (f '' s)) ∘ f)))) :
    LinearIndependent R ((s ∪ t).restrict f) := by
  apply linearIndependent.union_index hs ht.of_comp
  convert (Submodule.range_ker_disjoint ht).symm
  · simp
  aesop
