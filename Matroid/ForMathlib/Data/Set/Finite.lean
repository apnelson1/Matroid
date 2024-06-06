import Mathlib.Data.Set.Finite


open Set

variable {α : Type*} {s : Set α}


lemma infinite_iUnion {ι : Type*} [Infinite ι] {s : ι → Set α} (hs : Function.Injective s) :
    (⋃ i, s i).Infinite :=
  fun hfin ↦ @not_injective_infinite_finite ι _ _ hfin.finite_subsets.to_subtype
    (fun i ↦ ⟨s i, subset_iUnion _ _⟩) fun i j h_eq ↦ hs (by simpa using h_eq)

lemma Set.Infinite.biUnion {ι : Type*} {s : ι → Set α} {a : Set ι} (ha : a.Infinite)
    (hs : a.InjOn s) : (⋃ i ∈ a, s i).Infinite := by
  rw [biUnion_eq_iUnion]
  have _ := ha.to_subtype
  exact infinite_iUnion fun ⟨i,hi⟩ ⟨j,hj⟩ hij ↦ by simp [hs hi hj hij]

lemma Set.Infinite.sUnion {s : Set (Set α)} (hs : s.Infinite) : (⋃₀ s).Infinite := by
  rw [sUnion_eq_iUnion]
  have _ := hs.to_subtype
  exact infinite_iUnion Subtype.coe_injective

-- lemma Infinite.exists_natEmbedding_initialSegment {α : Type*} [Infinite α] {n : ℕ}
--     (f₀ : Fin n ↪ α) : ∃ f : ℕ ↪ α, ∀ i : Fin n, f₀ i = f i := by
--   let g := (infinite_univ.diff (finite_range f₀)).natEmbedding
--   refine ⟨⟨fun i ↦ if hi : i < n then f₀ ⟨i,hi⟩ else g (i - n), fun i j h ↦ ?_⟩, by simp⟩
--   simp only at h
--   split_ifs at h with hi hj hj
--   · simpa using f₀.injective h
--   · simpa [← h] using (g (j-n)).2.2
--   · simpa [h] using (g (i-n)).2.2
--   rw [Subtype.coe_inj, g.apply_eq_iff_eq] at h
--   exact tsub_inj_left (not_lt.1 hi) (not_lt.1 hj) h

-- lemma Infinite.exists_natEmbedding_initialVal {α : Type*} [Infinite α] (a : α) :
--     ∃ f : ℕ ↪ α, f 0 = a := by
--   obtain ⟨f, hf⟩ := Infinite.exists_natEmbedding_initialSegment
--     ⟨fun (_ : Fin 1) ↦ a, fun i j _ ↦ Subsingleton.elim _ _⟩
--   exact ⟨f, by simpa using (hf 0).symm⟩

lemma Set.Finite.subset_sUnion_directedOn_iff (hs : s.Finite) {C : Set (Set α)}
    (hC : DirectedOn (· ⊆ ·) C) (hne : C.Nonempty) : s ⊆ ⋃₀ C ↔ ∃ t ∈ C, s ⊆ t := by
  refine ⟨fun h ↦ ?_, fun ⟨t, ht, hst⟩ ↦ subset_sUnion_of_subset _ _ hst ht⟩
  apply hs.induction_on' (C := fun x ↦ ∃ u ∈ C, x ⊆ u) ⟨_, hne.some_mem,empty_subset _⟩
  rintro a t has - - ⟨u, huC, htu⟩
  obtain ⟨v, hvC, hav⟩ := h has
  obtain ⟨z, hzC, huz, hvz⟩ := hC _ huC _ hvC
  exact ⟨z, hzC, insert_subset (hvz hav) (htu.trans huz)⟩

lemma Set.Finite.subset_biUnion_mono_iff {ι : Type*} [LE ι] {v : ι → Set α} {a : Set ι}
    (hs : s.Finite) (ha : DirectedOn (· ≤ ·) a) (hne : a.Nonempty)
    (hv : ∀ ⦃i j⦄, i ≤ j → v i ⊆ v j) : s ⊆ ⋃ i ∈ a, v i ↔ ∃ i ∈ a, s ⊆ v i := by
  have doimage : DirectedOn (· ⊆ ·) (v '' a) := by
    rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
    obtain ⟨k, hka, hik, hjk⟩ := ha i hi j hj
    exact ⟨v k, ⟨k, hka, rfl⟩, hv hik, hv hjk⟩
  simpa using hs.subset_sUnion_directedOn_iff doimage (hne.image v)

/-- If `s` is an indexed family of nested sets, then a finite subset of their union is
a subset of a set in the family. -/
lemma Set.Finite.subset_iUnion_mono_iff {ι : Type*} [LE ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {v : ι → Set α} (hs : s.Finite) (hv : ∀ ⦃i j⦄, i ≤ j → v i ⊆ v j) :
    s ⊆ ⋃ i, v i ↔ ∃ i, s ⊆ v i := by
  simp [← biUnion_univ, hs.subset_biUnion_mono_iff directedOn_univ univ_nonempty hv]
