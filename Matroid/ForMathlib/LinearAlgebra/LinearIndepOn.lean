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

theorem LinearIndepOn.injOn [Nontrivial R] (hv : LinearIndepOn R v s) : InjOn v s :=
  injOn_iff_injective.2 <| LinearIndependent.injective hv

theorem LinearIndepOn.ne_zero [Nontrivial R] {i : ι} (hv : LinearIndepOn R v s) (hi : i ∈ s) :
    v i ≠ 0 :=
  LinearIndependent.ne_zero ⟨i, hi⟩ hv

theorem LinearIndepOn.linearIndependent {s : Set ι} (h : LinearIndepOn R v s) :
    LinearIndependent R (fun x : s ↦ v x) := h

theorem linearIndependent_set_coe_iff :
    LinearIndependent R (fun x : s ↦ v x) ↔ LinearIndepOn R v s := Iff.rfl

theorem linearIndependent_subtype_iff {s : Set M} :
    LinearIndependent R (Subtype.val : s → M) ↔ LinearIndepOn R id s := Iff.rfl

theorem linearIndependent_comp_subtype_iff :
    LinearIndependent R (v ∘ Subtype.val : s → M) ↔ LinearIndepOn R v s := Iff.rfl

theorem linearIndependent_restrict_iff' :
    LinearIndependent R (s.restrict v) ↔ LinearIndepOn R v s := Iff.rfl

theorem LinearIndepOn.of_comp (f : M →ₗ[R] M') (hfv : LinearIndepOn R (f ∘ v) s) :
    LinearIndepOn R v s :=
  LinearIndependent.of_comp f hfv

protected theorem LinearMap.linearIndepOn_iff_of_injOn (f : M →ₗ[R] M')
    (hf_inj : Set.InjOn f (span R (v '' s))) :
    LinearIndepOn R (f ∘ v) s ↔ LinearIndepOn R v s :=
  f.linearIndependent_iff_of_injOn (by rwa [← image_eq_range]) (v := fun i : s ↦ v i)

theorem LinearIndepOn.map_injOn (hv : LinearIndepOn R v s) (f : M →ₗ[R] M')
    (hf_inj : Set.InjOn f (span R (v '' s))) : LinearIndepOn R (f ∘ v) s :=
  (f.linearIndepOn_iff_of_injOn hf_inj).mpr hv

@[nontriviality]
theorem LinearIndepOn.of_subsingleton [Subsingleton R] : LinearIndepOn R v s :=
  linearIndependent_of_subsingleton

theorem linearIndepOn_equiv (e : ι ≃ ι') {f : ι' → M} {s : Set ι} :
    LinearIndepOn R (f ∘ e) s ↔ LinearIndepOn R f (e '' s) :=
  linearIndependent_equiv' (e.image s) <| by simp [funext_iff]

theorem linearIndepOn_iff_image {ι} {s : Set ι} {f : ι → M} (hf : Set.InjOn f s) :
    LinearIndepOn R f s ↔ LinearIndepOn R id (f '' s) :=
  linearIndependent_equiv' (Equiv.Set.imageOfInjOn _ _ hf) rfl

theorem linearIndepOn_range_iff {ι} {f : ι → ι'} (hf : Injective f) (g : ι' → M) :
    LinearIndepOn R g (range f) ↔ LinearIndependent R (g ∘ f) :=
  Iff.symm <| linearIndependent_equiv' (Equiv.ofInjective f hf) rfl

alias ⟨LinearIndependent.of_linearIndepOn_range, _⟩ := linearIndepOn_range_iff

theorem linearIndepOn_id_range_iff {ι} {f : ι → M} (hf : Injective f) :
    LinearIndepOn R id (range f) ↔ LinearIndependent R f :=
  linearIndepOn_range_iff hf id

theorem LinearIndependent.linearIndepOn_id (i : LinearIndependent R v) :
    LinearIndepOn R id (range v) := by
  simpa using i.comp _ (rangeSplitting_injective v)

theorem LinearIndependent.linearIndepOn_id' (hv : LinearIndependent R v) {t : Set M}
    (ht : Set.range v = t) : LinearIndepOn R id t :=
  ht ▸ hv.linearIndepOn_id

theorem LinearIndepOn.comp_of_image {s : Set ι'} {f : ι' → ι} (h : LinearIndepOn R v (f '' s))
    (hf : InjOn f s) : LinearIndepOn R (v ∘ f) s :=
  LinearIndependent.comp h _ (Equiv.Set.imageOfInjOn _ _ hf).injective

theorem LinearIndepOn.image_of_comp (f : ι → ι') (g : ι' → M) (hs : LinearIndepOn R (g ∘ f) s) :
    LinearIndepOn R g (f '' s) := by
  nontriviality R
  have : InjOn f s := injOn_iff_injective.2 hs.injective.of_comp
  exact (linearIndependent_equiv' (Equiv.Set.imageOfInjOn f s this) rfl).1 hs

theorem LinearIndepOn.id_image (hs : LinearIndepOn R v s) : LinearIndepOn R id (v '' s) :=
  LinearIndepOn.image_of_comp v id hs

theorem linearIndepOn_iffₛ : LinearIndepOn R v s ↔
      ∀ f ∈ Finsupp.supported R R s, ∀ g ∈ Finsupp.supported R R s,
        Finsupp.linearCombination R v f = Finsupp.linearCombination R v g → f = g := by
  simp only [LinearIndepOn, linearIndependent_iffₛ, (· ∘ ·), Finsupp.mem_supported,
    Finsupp.linearCombination_apply, Set.subset_def, Finset.mem_coe]
  refine ⟨fun h l₁ h₁ l₂ h₂ eq ↦ (Finsupp.subtypeDomain_eq_iff h₁ h₂).1 <| h _ _ <|
    (Finsupp.sum_subtypeDomain_index h₁).trans eq ▸ (Finsupp.sum_subtypeDomain_index h₂).symm,
    fun h l₁ l₂ eq ↦ ?_⟩
  refine Finsupp.embDomain_injective (Embedding.subtype s) <| h _ ?_ _ ?_ ?_
  iterate 2 simpa using fun _ h _ ↦ h
  simp_rw [Finsupp.embDomain_eq_mapDomain]
  rwa [Finsupp.sum_mapDomain_index, Finsupp.sum_mapDomain_index] <;>
    intros <;> simp only [zero_smul, add_smul]

/-- An indexed set of vectors is linearly dependent iff there are two distinct
`Finsupp.LinearCombination`s of the vectors with the same value. -/
theorem linearDepOn_iff'ₛ : ¬LinearIndepOn R v s ↔
      ∃ f g : ι →₀ R, f ∈ Finsupp.supported R R s ∧ g ∈ Finsupp.supported R R s ∧
        Finsupp.linearCombination R v f = Finsupp.linearCombination R v g ∧ f ≠ g := by
  simp [linearIndepOn_iffₛ, and_left_comm]

/-- A version of `linearDepOn_iff'ₛ` with `Finsupp.linearCombination` unfolded. -/
theorem linearDepOn_iffₛ : ¬LinearIndepOn R v s ↔
      ∃ f g : ι →₀ R, f ∈ Finsupp.supported R R s ∧ g ∈ Finsupp.supported R R s ∧
        ∑ i ∈ f.support, f i • v i = ∑ i ∈ g.support, g i • v i ∧ f ≠ g :=
  linearDepOn_iff'ₛ

theorem linearIndepOn_of_finite (s : Set ι) (H : ∀ t ⊆ s, Set.Finite t → LinearIndepOn R v t) :
    LinearIndepOn R v s :=
  linearIndepOn_iffₛ.2 fun f hf g hg eq ↦
    linearIndepOn_iffₛ.1 (H _ (union_subset hf hg) <| (Finset.finite_toSet _).union <|
      Finset.finite_toSet _) f Set.subset_union_left g Set.subset_union_right eq

theorem linearIndepOn_iUnion_of_directed {η : Type*} {s : η → Set ι} (hs : Directed (· ⊆ ·) s)
    (h : ∀ i, LinearIndepOn R v (s i)) : LinearIndepOn R v (⋃ i, s i) := by
  by_cases hη : Nonempty η
  · refine linearIndepOn_of_finite (⋃ i, s i) fun t ht ft => ?_
    rcases finite_subset_iUnion ft ht with ⟨I, fi, hI⟩
    rcases hs.finset_le fi.toFinset with ⟨i, hi⟩
    exact (h i).mono (Subset.trans hI <| iUnion₂_subset fun j hj => hi j (fi.mem_toFinset.2 hj))
  · refine (linearIndepOn_empty R v).mono (t := iUnion (s ·)) ?_
    rintro _ ⟨_, ⟨i, _⟩, _⟩
    exact hη ⟨i⟩

theorem linearIndepOn_sUnion_of_directed {s : Set (Set ι)} (hs : DirectedOn (· ⊆ ·) s)
    (h : ∀ a ∈ s, LinearIndepOn R v a) : LinearIndepOn R v (⋃₀ s) := by
  rw [sUnion_eq_iUnion]
  exact linearIndepOn_iUnion_of_directed hs.directed_val (by simpa using h)

theorem linearIndepOn_biUnion_of_directed {η} {s : Set η} {t : η → Set ι}
    (hs : DirectedOn (t ⁻¹'o (· ⊆ ·)) s) (h : ∀ a ∈ s, LinearIndepOn R v (t a)) :
    LinearIndepOn R v (⋃ a ∈ s, t a) := by
  rw [biUnion_eq_iUnion]
  exact linearIndepOn_iUnion_of_directed (directed_comp.2 <| hs.directed_val) (by simpa using h)


-- TODO - generalize this to non-identity functions
theorem LinearIndepOn.id_union {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {s t : Set M}
    (hs : LinearIndepOn R id s) (ht : LinearIndepOn R id t) (hst : Disjoint (span R s) (span R t)) :
    LinearIndepOn R id (s ∪ t) := by
  have := hs.linearIndependent
  have := ht.linearIndependent
  have h := hs.linearIndependent.sum_type ht.linearIndependent (by simpa)
  simpa using h.linearIndepOn_id

theorem LinearIndepOn.singleton (R : Type*) {ι M : Type*} [Ring R] [Nontrivial R] [AddCommGroup M]
    [Module R M] [NoZeroSMulDivisors R M] {v : ι → M} {i : ι} (hi : v i ≠ 0) :
    LinearIndepOn R v {i} :=
  linearIndependent_unique _ (by simpa)


theorem LinearIndepOn.id_singleton (R : Type*) {M : Type*} [Ring R] [Nontrivial R] [AddCommGroup M]
    [Module R M] [NoZeroSMulDivisors R M] {x : M} (hx : x ≠ 0) : LinearIndepOn R id {x} :=
  linearIndependent_unique Subtype.val hx

@[simp]
theorem linearIndepOn_singleton_iff (R : Type*) {ι M : Type*} [Ring R] [Nontrivial R]
    [AddCommGroup M] [Module R M] [NoZeroSMulDivisors R M] {i : ι} {v : ι → M} :
    LinearIndepOn R v {i} ↔ v i ≠ 0 := by
  refine ⟨fun h ↦ h.ne_zero rfl, fun h ↦ LinearIndepOn.singleton R h⟩

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]

protected theorem LinearIndepOn.insert {s : Set V} {x : V} (hs : LinearIndepOn K id s)

    (hx : x ∉ span K s) :
    LinearIndepOn K id (insert x s) := by
  rw [← union_singleton]
  have x0 : x ≠ 0 := mt (by rintro rfl; apply zero_mem (span K s)) hx
  apply hs.id_union (LinearIndepOn.singleton _ x0)
  rwa [disjoint_span_singleton' x0]


theorem linearIndepOn_insert {a : ι} {f : ι → V} (has : a ∉ s) :
    LinearIndepOn K f (insert a s) ↔ LinearIndepOn K f s ∧ f a ∉ Submodule.span K (f '' s) := by
  classical
  rw [LinearIndepOn, LinearIndepOn, ← linearIndependent_equiv
    ((Equiv.optionEquivSumPUnit _).trans (Equiv.Set.insert has).symm), linearIndependent_option]
  simp only [comp_def]
  rw [range_comp']
  simp

theorem linearIndepOn_id_pair {x y : V} (hx : x ≠ 0) (hy : ∀ a : K, a • x ≠ y) :
    LinearIndepOn K id {x, y} :=
  pair_comm y x ▸ (LinearIndepOn.id_singleton K hx).insert (x := y) <|
    mt mem_span_singleton.1 <| not_exists.2 hy


-- FOR MATHLIB
theorem LinearIndepOn_iff_linearIndepOn_image_injOn [Nontrivial R] :
    LinearIndepOn R v s ↔ LinearIndepOn R id (v '' s) ∧ InjOn v s :=
  ⟨fun h ↦ ⟨h.image, h.injOn⟩, fun h ↦ (linearIndepOn_iff_image h.2).2 h.1⟩

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

theorem linearIndepOn_id_insert {x : V} {s : Set V} (hxs : x ∉ s) :
    LinearIndepOn K id (insert x s) ↔ LinearIndepOn K id s ∧ x ∉ Submodule.span K s :=
  (linearIndepOn_insert (f := id) hxs).trans <| by simp

theorem LinearIndepOn.not_mem_span_iff {a : ι} {f : ι → V} (h : LinearIndepOn K f s) :
    f a ∉ Submodule.span K (f '' s) ↔ a ∉ s ∧ LinearIndepOn K f (insert a s) := by
  by_cases has : a ∈ s
  · simp only [has, not_true_eq_false, insert_eq_of_mem, false_and, iff_false, not_not]
    exact subset_span <| mem_image_of_mem f has
  simp [linearIndepOn_insert_iff, has, h]

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

theorem LinearIndepOn.zero_not_mem_image {R M ι : Type*} [Semiring R] [Nontrivial R]
    [AddCommGroup M] [Module R M] {s : Set ι} {f : ι → M}
    (hs : LinearIndepOn R f s) : 0 ∉ f '' s :=
  fun h0 ↦ hs.image.ne_zero ⟨_, h0⟩ rfl

theorem LinearIndepOn.union {R M ι : Type*} [DivisionRing R] [AddCommGroup M] [Module R M]
    {s t : Set ι} {f : ι → M} (hs : LinearIndepOn R f s) (ht : LinearIndepOn R f t)
    (hdj : Disjoint (span R (f '' s)) (span R (f '' t))) : LinearIndepOn R f (s ∪ t) := by
  refine (linearIndependent_image ?_).2 <|
   (hs.image.union ht.image hdj).comp (Equiv.Set.ofEq (image_union ..)) (Equiv.injective _)
  have hst := Submodule.disjoint_of_disjoint_span₀ hdj hs.zero_not_mem_image
  rw [injOn_union hst.of_image, injOn_iff_injective, injOn_iff_injective]
  exact ⟨hs.injective, ht.injective,
    fun x hxs y hyt ↦ hst.ne_of_mem (mem_image_of_mem f hxs) (mem_image_of_mem f hyt)⟩

theorem linearIndepOn_union_iff {R M ι : Type*} [DivisionRing R] [AddCommGroup M] [Module R M]
    {s t : Set ι} {f : ι → M} (hdj : Disjoint s t) :
    LinearIndepOn R f (s ∪ t) ↔
    LinearIndepOn R f s ∧ LinearIndepOn R f t ∧ Disjoint (span R (f '' s)) (span R (f '' t)) := by
  refine ⟨fun h ↦ ⟨h.mono subset_union_left, h.mono subset_union_right, ?_⟩,
    fun h ↦ h.1.union h.2.1 h.2.2⟩
  convert h.disjoint_span_image (s := (↑) ⁻¹' s) (t := (↑) ⁻¹' t) (hdj.preimage _) <;>
  aesop

theorem LinearIndepOn.union_of_quotient {R M ι : Type*} [DivisionRing R] [AddCommGroup M]
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
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ h.1.union_of_quotient h.2⟩
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
  convert linearIndependent_insert' (s := {i}) (a := j) hij.symm
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
