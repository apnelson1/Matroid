import Mathlib.LinearAlgebra.LinearIndependent
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions


variable {ι ι' : Type*} {R : Type*} {K : Type*} {s : Set ι} {M M' V : Type*} {v : ι → M}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M'] [Module R M] [Module R M']

open Function Set Submodule

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


@[simp]
theorem linearIndepOn_singleton_iff (R : Type*) {ι M : Type*} [Ring R] [Nontrivial R]
    [AddCommGroup M] [Module R M] [NoZeroSMulDivisors R M] {i : ι} {v : ι → M} :
    LinearIndepOn R v {i} ↔ v i ≠ 0 :=
  ⟨fun h ↦ h.ne_zero rfl, fun h ↦ LinearIndepOn.singleton h⟩

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]


theorem LinearIndepOn_iff_linearIndepOn_image_injOn [Nontrivial R] :
    LinearIndepOn R v s ↔ LinearIndepOn R id (v '' s) ∧ InjOn v s :=
  ⟨fun h ↦ ⟨h.id_image, h.injOn⟩, fun h ↦ (linearIndepOn_iff_image h.2).2 h.1⟩

@[simp]
theorem linearIndepOn_zero_iff [Nontrivial R] : LinearIndepOn R (0 : ι → M) s ↔ s = ∅ := by
  convert linearIndependent_zero_iff (ι := s) (R := R) (M := M)
  simp



theorem linearIndepOn_insert_iff {a : ι} {f : ι → V} :
    LinearIndepOn K f (insert a s) ↔ LinearIndepOn K f s ∧ (f a ∈ span K (f '' s) → a ∈ s) := by
  by_cases has : a ∈ s
  · simp [insert_eq_of_mem has, has]
  simp [linearIndepOn_insert has, has]

theorem linearIndepOn_id_insert_iff {a : V} {s : Set V} :
    LinearIndepOn K id (insert a s) ↔ LinearIndepOn K id s ∧ (a ∈ span K s → a ∈ s) := by
  simpa using linearIndepOn_insert_iff (a := a) (f := id)

theorem LinearIndepOn.not_mem_span_iff {a : ι} {f : ι → V} (h : LinearIndepOn K f s) :
    f a ∉ Submodule.span K (f '' s) ↔ a ∉ s ∧ LinearIndepOn K f (insert a s) := by
  by_cases has : a ∈ s
  · simp only [has, not_true_eq_false, insert_eq_of_mem, false_and, iff_false, not_not]
    exact subset_span <| mem_image_of_mem f has
  simp [linearIndepOn_insert_iff, has, h]

theorem LinearIndepOn.mem_span_iff {a : ι} {f : ι → V} (h : LinearIndepOn K f s) :
    f a ∈ Submodule.span K (f '' s) ↔ (LinearIndepOn K f (insert a s) → a ∈ s) := by
  rw [← not_iff_not, h.not_mem_span_iff, ← not_iff_not, not_and, not_not, not_imp_not]

theorem LinearIndepOn.not_mem_span_iff_id {s : Set V} {a : V} (h : LinearIndepOn K id s) :
    a ∉ Submodule.span K s ↔ a ∉ s ∧ LinearIndepOn K id (insert a s) := by
  simpa using h.not_mem_span_iff (a := a)

theorem LinearIndepOn.congr {v w : ι → M} {s : Set ι} (hli : LinearIndepOn R v s) (h : EqOn v w s) :
    LinearIndepOn R w s := by
  rw [← linearIndependent_comp_subtype_iff] at hli ⊢
  convert hli using 1
  ext x
  exact h.symm x.2

theorem linearIndepOn_congr {v w : ι → M} {s : Set ι} (h : EqOn v w s) :
    LinearIndepOn R v s ↔ LinearIndepOn R w s :=
  ⟨fun h' ↦ h'.congr h, fun h' ↦ h'.congr h.symm⟩

noncomputable def Basis.spanImage {ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {v : ι → M} {s : Set ι} (hli : LinearIndepOn R v s) : Basis s R (span R (v '' s)) :=
  (Basis.span hli.linearIndependent).map <| LinearEquiv.ofEq _ _ <| congr_arg _ <| by aesop

@[simp]
theorem Basis.spanImage_apply {ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {v : ι → M} {s : Set ι} (hli : LinearIndepOn R v s) {i : s} :
    (Basis.spanImage hli) i = v i := by
  simp [Basis.spanImage, Basis.span]

noncomputable def Basis.mkImage {ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {v : ι → M} {s : Set ι} (hli : LinearIndepOn R v s) (hsp : ⊤ ≤ Submodule.span R (v '' s)) :
    Basis s R M :=
  Basis.mk hli.linearIndependent <| by rwa [← image_eq_range]

-- theorem LinearIndepOn.ne_zero {R M ι : Type*} [Semiring R] [Nontrivial R]
--     [AddCommGroup M] [Module R M] {s : Set ι} {f : ι → M}
--     (hs : LinearIndepOn R f s) {i : ι} (hi : i ∈ s) : f i ≠ 0 := by
--   _

-- theorem LinearIndepOn.ne_zero {R M ι : Type*} [Semiring R] [Nontrivial R]
--     [AddCommGroup M] [Module R M] {s : Set ι} {v : ι → M} (hi : i ∈ s) : v i ≠ 0 := by
--   _

theorem LinearIndepOn.zero_not_mem_image {R M ι : Type*} [Semiring R] [Nontrivial R]
    [AddCommGroup M] [Module R M] {s : Set ι} {f : ι → M}
    (hs : LinearIndepOn R f s) : 0 ∉ f '' s :=
  fun ⟨_, hi, h0⟩ ↦ hs.ne_zero hi h0

/-- derive the `id` version from this -/
theorem LinearIndepOn.union {R M ι : Type*} [DivisionRing R] [AddCommGroup M] [Module R M]
    {s t : Set ι} {v : ι → M} (hs : LinearIndepOn R v s) (ht : LinearIndepOn R v t)
    (hdj : Disjoint (span R (v '' s)) (span R (v '' t))) : LinearIndepOn R v (s ∪ t) := by
  classical
  have hli := LinearIndependent.sum_type hs ht (by rwa [← image_eq_range, ← image_eq_range])
  have hdj := (disjoint_of_disjoint_span₀ hdj hs.zero_not_mem_image).of_image
  rw [LinearIndepOn]
  convert (hli.comp _ (Equiv.Set.union hdj).injective) with ⟨x, hx | hx⟩
  · rw [comp_apply, Equiv.Set.union_apply_left _ hx]
    simp
  rw [comp_apply, Equiv.Set.union_apply_right _ hx]
  simp

theorem linearIndepOn_union_iff {R M ι : Type*} [DivisionRing R] [AddCommGroup M] [Module R M]
    {s t : Set ι} {f : ι → M} (hdj : Disjoint s t) :
    LinearIndepOn R f (s ∪ t) ↔
    LinearIndepOn R f s ∧ LinearIndepOn R f t ∧ Disjoint (span R (f '' s)) (span R (f '' t)) := by
  refine ⟨fun h ↦ ⟨h.mono subset_union_left, h.mono subset_union_right, ?_⟩,
    fun h ↦ h.1.union h.2.1 h.2.2⟩
  convert h.disjoint_span_image (s := (↑) ⁻¹' s) (t := (↑) ⁻¹' t) (hdj.preimage _) <;>
  aesop

/-- Replace the unprimed version with this. -/
theorem LinearIndepOn.union_of_quotient' {R M ι : Type*} [DivisionRing R] [AddCommGroup M]
    [Module R M] {s t : Set ι} {f : ι → M}
    (hs : LinearIndepOn R f s) (ht : LinearIndepOn R (mkQ (span R (f '' s)) ∘ f) t) :
    LinearIndepOn R f (s ∪ t) := by
  apply hs.union ht.of_comp
  convert (Submodule.range_ker_disjoint ht).symm
  · simp
  aesop

theorem linearIndepOn_union_iff_quotient {R M ι : Type*} [DivisionRing R]
    [AddCommGroup M] [Module R M] {s t : Set ι} {f : ι → M} (hst : Disjoint s t) :
    LinearIndepOn R f (s ∪ t) ↔
      LinearIndepOn R f s ∧ LinearIndepOn R (mkQ (span R (f '' s)) ∘ f) t := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ h.1.union_of_quotient' h.2⟩
  · exact h.mono subset_union_left
  apply (h.mono subset_union_right).map
  simpa [← image_eq_range] using ((linearIndepOn_union_iff hst).1 h).2.2.symm

theorem LinearIndepOn.quotient_iff_union {R M ι : Type*} [DivisionRing R] [AddCommGroup M]
    [Module R M] {s t : Set ι} {f : ι → M} (hs : LinearIndepOn R f s) (hst : Disjoint s t) :
    LinearIndepOn R (mkQ (span R (f '' s)) ∘ f) t ↔ LinearIndepOn R f (s ∪ t) := by
  rw [linearIndepOn_union_iff_quotient hst, and_iff_right hs]

theorem linearIndepOn_pair_iff {K V ι : Type*} [DivisionRing K] [AddCommGroup V]
  [Module K V] {i j : ι} (f : ι → V) (hij : i ≠ j) (hi : f i ≠ 0):
    LinearIndepOn K f {i, j} ↔ ∀ (c : K), c • f i ≠ f j := by
  rw [pair_comm]
  convert linearIndepOn_insert (s := {i}) (a := j) hij.symm
  simp [hi, mem_span_singleton, linearIndependent_unique_iff]


@[simp]
theorem Basis.mkImage_apply {ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {v : ι → M} {s : Set ι} (hli : LinearIndepOn R v s) (hsp : ⊤ ≤ Submodule.span R (v '' s))
    (i : s) : Basis.mkImage hli hsp i = v i.1 := by
  rw [Basis.mkImage, Basis.mk_apply]

@[simp]
theorem Basis.mkImage_repr {ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {v : ι → M} {s : Set ι} (hli : LinearIndepOn R v s) (hsp : ⊤ ≤ Submodule.span R (v '' s))
    (x : M) : (Basis.mkImage hli hsp).repr x =
    hli.repr ⟨x, by rw [← image_eq_range, top_le_iff.1 hsp]; exact mem_top⟩  := by
  simp [Basis.mkImage]

@[simp]
lemma Finsupp.ker_lcoeFun {α M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M] :
    LinearMap.ker (Finsupp.lcoeFun (α := α) (M := M) (R := R)) = ⊥ := by
  ext f
  simp [lcoeFun]

section extend

variable {ι R M : Type*} [DivisionRing R] [AddCommGroup M] [Module R M] {s₀ s t : Set ι} {v : ι → M}

theorem LinearIndepOn.exists_maximal (hli : LinearIndepOn R v s₀) (hs₀t : s₀ ⊆ t) :
    ∃ s, s₀ ⊆ s ∧ Maximal (fun r ↦ r ⊆ t ∧ LinearIndepOn R v r) s :=
  zorn_subset_nonempty {r | r ⊆ t ∧ LinearIndepOn R v r}
    (fun c hcss hchain _ ↦ ⟨⋃₀ c, ⟨sUnion_subset fun _ hxc ↦ (hcss hxc).1,
      linearIndepOn_sUnion_of_directed hchain.directedOn fun _ hxc ↦ (hcss hxc).2⟩,
      fun _ hs ↦ subset_sUnion_of_mem hs⟩) s₀ ⟨hs₀t, hli⟩

noncomputable def LinearIndepOn.extension (hli : LinearIndepOn R v s) (hst : s ⊆ t) : Set ι :=
    (hli.exists_maximal hst).choose

lemma LinearIndepOn.extension_maximal (hli : LinearIndepOn R v s) (hst : s ⊆ t) :
    Maximal (fun r ↦ r ⊆ t ∧ LinearIndepOn R v r) (hli.extension hst) :=
  (hli.exists_maximal hst).choose_spec.2

lemma LinearIndepOn.subset_extension (hli : LinearIndepOn R v s) (hst : s ⊆ t) :
    s ⊆ (hli.extension hst) :=
  (hli.exists_maximal hst).choose_spec.1

lemma LinearIndepOn.span_eq_of_maximal_subset
    (hmax : Maximal (fun r ↦ r ⊆ t ∧ LinearIndepOn R v r) s) :
    span R (v '' s) = span R (v '' t) := by
  refine le_antisymm (span_mono (image_mono hmax.prop.1)) <| span_le.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  exact hmax.prop.2.mem_span_iff.2 <|
    fun h ↦ hmax.mem_of_prop_insert ⟨(insert_subset hx hmax.prop.1), h⟩

lemma LinearIndepOn.span_eq_top_of_maximal (hmax : Maximal (LinearIndepOn R v ·) s) :
    span R (v '' s) = span R (range v) := by
  rw [← image_univ, LinearIndepOn.span_eq_of_maximal_subset (t := univ) (by simpa)]

-- lemma linearIndepOn.extension_span_eq (hli : LinearIndepOn R v s) (hst : s ⊆ t) :

-- lemma LinearIndepOn.extension_subset (hli : LinearIndepOn R v s) (hst : s ⊆ t) :
--     (hli.extension hst) ⊆ t :=
--   (hli.extension_maximal hst).prop.1

-- lemma LinearIndepOn.subset_span_extension (hli : LinearIndepOn R v s) (hst : s ⊆ t) :
--     v '' t ⊆ span R (v '' hli.extension hst) := by
--   have := (hli.exists_maximal hst).choose_spec

-- lemma LinearIndepOn.span_extension (hli : LinearIndepOn R v s) (hst : s ⊆ t) :
--     span R (v '' hli.extension hst) = span R (v '' t) := by
--   have := (hli.exists_maximal hst).choose_spec



-- lemma LinearIndepOn.linearIndepOn_extension (hli : LinearIndepOn R v s) (hst : s ⊆ t) :
--     LinearIndepOn R v (hli.extension hst) :=
--   (hli.exists_extension hst).choose_spec.2.2.2

-- lemma LinearIndepOn.extension_maximal (hli : LinearIndepOn R v s) :
--     Maximal (LinearIndepOn R v ·) (hli.extension (subset_univ _)) := by


-- /-- Any linearly independent subset of `t` extends to a maximal such set. -/
-- theorem LinearIndepOn.exists_extension (hli : LinearIndepOn R v s₀) (hs₀t : s₀ ⊆ t) :
--         ∃ s ⊆ t, s₀ ⊆ s ∧ span R (v '' t) = span R (v '' s) ∧ LinearIndepOn R v s := by
--   have hzorn := zorn_subset_nonempty
--     {r | s₀ ⊆ r ∧ r ⊆ t ∧ LinearIndepOn R v r} ?_ s₀ ⟨Subset.rfl, hs₀t, hli⟩
--   · obtain ⟨m, hs₀m, hmax⟩ := hzorn
--     refine ⟨m, hmax.prop.2.1, hs₀m, ?_, hmax.prop.2.2⟩
--     refine span_eq_span ?_ ((image_mono (hmax.prop.2.1)).trans <| subset_span ..)
--     rintro _ ⟨x, hx, rfl⟩
--     by_contra hxm
--     rw [SetLike.mem_coe, hmax.prop.2.2.not_mem_span_iff] at hxm
--     exact hxm.1 <| hmax.mem_of_prop_insert
--       ⟨hs₀m.trans <| subset_insert .., insert_subset hx hmax.prop.2.1, hxm.2⟩
--   refine fun c hcss hchain ⟨r, hr⟩ ↦ ⟨⋃₀ c, ⟨(hcss hr).1.trans <| subset_sUnion_of_mem hr,
--     sUnion_subset fun t' ht'c ↦ (hcss ht'c).2.1,?_⟩, fun _ ↦ subset_sUnion_of_mem⟩
--   exact linearIndepOn_sUnion_of_directed hchain.directedOn fun a hac ↦ (hcss hac).2.2


--   _
