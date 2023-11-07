import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.Dual
import Matroid.ForMathlib.Other

variable {α ι W W' R : Type*} [AddCommGroup W] [AddCommGroup W']

open Set Submodule BigOperators

theorem Fintype.linearIndependent_restrict_iff [Fintype ι] [CommSemiring R]
  [AddCommMonoid M] [Module R M] {s : Set ι} {v : ι → M} :
    ¬ LinearIndependent R (s.restrict v) ↔ ∃ c : ι → R, ∑ i, c i • v i = 0 ∧ (∃ i ∈ s, c i ≠ 0)
      ∧ ∀ i, i ∉ s → c i = 0 := by
  classical
  have _ := s.toFinite.fintype
  rw [Fintype.not_linearIndependent_iff]
  refine ⟨fun ⟨c', hc', i₀, hi₀⟩ ↦ ?_, fun ⟨c, hc0, ⟨i₀, hi₀, hne⟩, hi⟩ ↦ ?_⟩
  · set f := fun i ↦ if hi : i ∈ s then c' ⟨i,hi⟩ • (v i) else 0
    refine ⟨fun i ↦ if hi : i ∈ s then c' ⟨i,hi⟩ else 0, ?_, ⟨i₀, i₀.prop, by simpa⟩,
      fun i hi ↦ by simp [hi]⟩
    rw [←hc']
    convert Finset.sum_congr_set s f (fun i ↦ (c' i) • v i) (fun _ h ↦ by simp [h])
      (fun _ h ↦ by simp [h])
    · simp only; split_ifs; rfl; exact zero_smul _ _
  refine ⟨fun i ↦ c i, ?_, ⟨⟨i₀, hi₀⟩, hne⟩⟩
  rw [←hc0, eq_comm]
  convert Finset.sum_congr_set s (fun i ↦ (c i) • (v i)) (fun i ↦ (c i) • v i)
    (fun x _ ↦ rfl) (fun _ hx ↦ by simp [hi _ hx])

theorem linearIndependent_restrict_iff [CommSemiring R] [AddCommMonoid M] [Module R M] {s : Set ι}
    {v : ι → M} : LinearIndependent R (s.restrict v) ↔
      ∀ l : ι →₀ R, Finsupp.total ι M R v l = 0 → (l.support : Set ι) ⊆ s → l = 0 := by
  set incl : s ↪ ι := Function.Embedding.subtype (· ∈ s)
  rw [linearIndependent_iff]
  refine ⟨fun h l hl hsupp ↦ ?_, fun h l hl ↦ ?_⟩
  · specialize h (Finsupp.subtypeDomain (· ∈ s ) l) _
    · rw [Finsupp.total_apply, Finsupp.sum_of_support_subset _ (Subset.rfl)] at hl ⊢
      · simp only [Finsupp.subtypeDomain_apply, restrict_apply]
        convert (Finset.sum_map _ incl (fun x ↦ l x • v x)).symm
        convert hl.symm
        ext i
        aesop
      · aesop
      aesop
    ext i
    obtain (hi | hi) := em (i ∈ s)
    · exact FunLike.congr_fun h ⟨i,hi⟩
    simpa using not_mem_subset hsupp  hi
  specialize h <| Finsupp.embDomain incl l
  simp only [Finsupp.total_embDomain, Function.Embedding.coe_subtype, Finsupp.support_embDomain,
    Finset.coe_map, image_subset_iff, Subtype.coe_preimage_self, subset_univ,
    Finsupp.embDomain_eq_zero, forall_true_left] at h
  exact h hl

theorem linearIndependent_of_finite_index {R M ι : Type*} [DivisionRing R] [AddCommGroup M]
    [Module R M] (f : ι → M) (h : ∀ (t : Set ι), t.Finite → LinearIndependent R (t.restrict f)) :
    LinearIndependent R f := by
  have hinj : f.Injective
  · intro x y hxy
    have hli := (h {x,y} (toFinite _))
    have h : (⟨x, by simp⟩ : ({x,y} : Set ι)) = ⟨y, by simp⟩
    · rw [←hli.injective.eq_iff]; simpa
    simpa using h
  rw [←linearIndependent_subtype_range hinj]
  refine linearIndependent_of_finite _ fun t ht htfin ↦ ?_
  obtain ⟨t, rfl⟩ := subset_range_iff_exists_image_eq.1 ht
  exact (linearIndependent_image (injOn_of_injective hinj t)).1 <|
    h t (htfin.of_finite_image (injOn_of_injective hinj t))

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
  have hss : Subtype.val '' t ⊆ s z
  · refine hI.trans (iUnion_subset fun i j h ↦ ?_)
    simp only [mem_iUnion, exists_prop] at h
    exact hz i (by simpa using h.1) h.2
  set emb : t → s z := (inclusion hss) ∘ (imageFactorization Subtype.val t)
  refine (h z).comp emb <| Function.Injective.comp (inclusion_injective hss) ?_
  exact InjOn.imageFactorization_injective (Subtype.val_injective.injOn _)

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
  Cardinal.lt_aleph0_iff_finite.1 <| FiniteDimensional.lt_aleph0_of_linearIndependent h

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
    rw [←hmax _ ⟨hs₀m.trans <| subset_insert _ _, insert_subset hx hmt, hli'⟩ (subset_insert _ _)]
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
  · rw [←hc, smul_smul, inv_mul_cancel, one_smul]
    rintro rfl; exact hi <| by simp [←hc]
  rw [←h', smul_smul, inv_mul_cancel, one_smul]
  rintro rfl; exact h.1 <| by simp [← h']
