import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Set.Notation

open Set

variable {α : Type*} {s : Set α}


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
  apply hs.induction_on_subset (motive := fun x _ ↦ ∃ u ∈ C, x ⊆ u) _
    ⟨_, hne.some_mem,empty_subset _⟩
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

/-- If `s` is an indexed directed family of sets, then a finite subset of their union is
a subset of a set in the family. -/
lemma Set.Finite.subset_iUnion_mono_iff {ι : Type*} [LE ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    {v : ι → Set α} (hs : s.Finite) (hv : ∀ ⦃i j⦄, i ≤ j → v i ⊆ v j) :
    s ⊆ ⋃ i, v i ↔ ∃ i, s ⊆ v i := by
  simp [← biUnion_univ, hs.subset_biUnion_mono_iff directedOn_univ univ_nonempty hv]

@[simp] lemma insert_infinite_iff {x : α} {s : Set α} : (insert x s).Infinite ↔ s.Infinite := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.mono (subset_insert _ _)⟩
  contrapose! h
  exact h.insert x

/-- Every directed family of sets containing a finite set contains its intersection. -/
lemma Directed.iInter_mem_of_finite_mem {ι : Type*} {s : ι → Set α}
    (hdir : Directed (fun x y ↦ y ⊆ x) s) (i₀ : ι) (hi : (s i₀).Finite) : ∃ j, s j = ⋂ i, s i := by
  by_contra! hcon
  have hne := hcon i₀
  obtain ⟨j, hj⟩ : ∃ j, ¬ (s i₀ ⊆ s j) := by
    contrapose! hne
    exact subset_antisymm (by simpa) <| iInter_subset ..
  obtain ⟨j₀, hj₀i, hj₀j⟩ := hdir i₀ j
  have hssu : s j₀ ⊂ s i₀ := ssubset_of_subset_not_subset hj₀i (fun h' ↦ hj (h'.trans hj₀j))
  obtain ⟨k, hk⟩ := hdir.iInter_mem_of_finite_mem j₀ (hi.subset hj₀i)
  exact hcon k hk
termination_by hi.toFinset.card
decreasing_by exact Finset.card_lt_card <| by simpa

lemma DirectedOn.sInter_mem_of_finite_mem (s : Set (Set α)) (hdir : DirectedOn (fun x y ↦ y ⊆ x) s)
    {x : Set α} (hx : x ∈ s) (hfin : x.Finite) : ⋂₀ s ∈ s := by
  obtain ⟨⟨t, ht⟩, rfl⟩ := hdir.directed_val.iInter_mem_of_finite_mem ⟨x, hx⟩ hfin
  rwa [sInter_eq_iInter]

lemma Directed.exists_forall_ge {α ι : Type*} [Preorder α] [Nonempty ι] {f : ι → α}
    (hdir : Directed (· ≤ ·) f) {I : Set ι} (hI : I.Finite) : ∃ k, ∀ i ∈ I, f i ≤ f k := by
  induction I, hI using Set.Finite.induction_on with
  | empty => exact ⟨Classical.arbitrary ι, by simp⟩
  | @insert a s has hfin IH =>
  · obtain ⟨k', hk'⟩ := IH
    obtain ⟨k, hk'k, hak⟩ := hdir k' a
    exact ⟨k, by simpa [hak] using fun i his ↦ (hk' i his).trans hk'k⟩

lemma DirectedOn.exists_forall_ge {α : Type*} [Preorder α] {s t : Set α}
    (hdir : DirectedOn (· ≤ ·) s) (hne : s.Nonempty) (hts : t ⊆ s) (hfin : t.Finite) :
    ∃ x ∈ s, ∀ y ∈ t, y ≤ x := by
  have := hne.to_subtype
  have := hfin.to_subtype
  obtain ⟨⟨k,hks⟩, hk⟩ := hdir.directed_val.exists_forall_ge (I := range (inclusion hts))
    (finite_range ..)
  exact ⟨k, hks, fun y hyt ↦ by simpa [hyt] using hk ⟨y, hts hyt⟩⟩

lemma DirectedOn.exists_forall_le {α : Type*} [Preorder α] {s t : Set α}
    (hdir : DirectedOn (fun a b ↦ b ≤ a) s) (hne : s.Nonempty) (hts : t ⊆ s) (hfin : t.Finite) :
    ∃ x ∈ s, ∀ y ∈ t, x ≤ y :=
  hdir.exists_forall_ge (α := αᵒᵈ) hne hts hfin

lemma Directed.exists_eq_iSup {α ι : Type*} [CompleteLattice α] [Finite ι] [Nonempty ι] {f : ι → α}
    (hdir : Directed (· ≤ ·) f) : ∃ k, f k = ⨆ i, f i := by
  obtain ⟨k, h⟩ := hdir.exists_forall_ge finite_univ
  exact ⟨k, le_antisymm (le_iSup ..) (by simpa using h)⟩

lemma DirectedOn.iSup_mem {α : Type*} [CompleteLattice α] {s : Set α}
    (hdir : DirectedOn (· ≤ ·) s) (hs : s.Nonempty) (hfin : s.Finite) : sSup s ∈ s := by
  have := hs.to_subtype
  have := hfin.to_subtype
  obtain ⟨⟨x, hxs⟩, rfl⟩ := hdir.directed_val.exists_eq_iSup (ι := s)
  rwa [sSup_eq_iSup']

lemma Directed.exists_eq_iInf {α ι : Type*} [CompleteLattice α] [Finite ι] [Nonempty ι] {f : ι → α}
    (hdir : Directed (fun a b ↦ b ≤ a) f) : ∃ k, f k = ⨅ i, f i :=
  Directed.exists_eq_iSup (α := αᵒᵈ) hdir

lemma DirectedOn.iInf_mem {α : Type*} [CompleteLattice α] {s : Set α}
    (hdir : DirectedOn (fun a b ↦ b ≤ a) s) (hs : s.Nonempty) (hfin : s.Finite) : sInf s ∈ s :=
  DirectedOn.iSup_mem (α := αᵒᵈ) hdir hs hfin
