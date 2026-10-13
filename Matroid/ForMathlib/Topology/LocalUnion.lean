module

public import Mathlib.Topology.Neighborhoods

/-!
# Local structure of finite unions

If a point belongs to exactly a specified subfamily of a finite family of closed sets, then the
union agrees with that subfamily in a neighbourhood of the point. The result is useful for local
descriptions of finite unions of segments.

## Main statements

* `exists_nhds_inter_biUnion_eq_biUnion` : the general finite-index-set statement.
* `exists_nhds_inter_biUnion_eq` : the singleton specialization for a finite index set.
* `exists_nhds_inter_iUnion_eq_biUnion` : the finite-type specialization.
* `exists_nhds_inter_iUnion_eq` : the singleton-subfamily specialization.
-/

@[expose] public section

open Set Topology

/-- If a point belongs exactly to the members indexed by `t` of a closed family indexed by the
finite set `s`, then the union over `s` agrees locally with the union over `t`. -/
theorem exists_nhds_inter_biUnion_eq_biUnion {X ι : Type*} [TopologicalSpace X]
    {K : ι → Set X} {a : X} {s t : Set ι} (hs : s.Finite) (hts : t ⊆ s)
    (hK : ∀ i ∈ s, IsClosed (K i)) (ht : ∀ i ∈ s, a ∈ K i ↔ i ∈ t) :
    ∃ U ∈ 𝓝 a, U ∩ (⋃ i ∈ s, K i) = U ∩ ⋃ i ∈ t, K i := by
  let C : Set X := ⋃ i ∈ s \ t, K i
  have hC : IsClosed C := by
    dsimp only [C]
    exact hs.sdiff.isClosed_biUnion fun i hi ↦ hK i hi.1
  have haC : a ∉ C := by
    intro haC
    simp only [C, mem_iUnion] at haC
    obtain ⟨i, hi, hai⟩ := haC
    exact hi.2 ((ht i hi.1).mp hai)
  have hU : IsOpen Cᶜ := @IsClosed.isOpen_compl X _ C hC
  refine ⟨Cᶜ, IsOpen.mem_nhds hU haC, ?_⟩
  ext x
  constructor
  · rintro ⟨hxC, hxK⟩
    refine ⟨hxC, ?_⟩
    simp only [mem_iUnion] at hxK ⊢
    obtain ⟨i, hi, hxi⟩ := hxK
    refine ⟨i, ?_, hxi⟩
    by_contra hit
    exact hxC (mem_iUnion_of_mem i (mem_iUnion_of_mem ⟨hi, hit⟩ hxi))
  · rintro ⟨hxC, hxK⟩
    refine ⟨hxC, ?_⟩
    simp only [mem_iUnion] at hxK ⊢
    obtain ⟨i, hi, hxi⟩ := hxK
    exact ⟨i, hts hi, hxi⟩

/-- If a point belongs to exactly one member of a closed family indexed by the finite set `s`,
then the union over `s` agrees locally with that member. -/
theorem exists_nhds_inter_biUnion_eq {X ι : Type*} [TopologicalSpace X]
    {K : ι → Set X} {a : X} {s : Set ι} {i : ι} (hs : s.Finite)
    (hK : ∀ j ∈ s, IsClosed (K j)) (h : ∃! j, j ∈ s ∧ a ∈ K j)
    (hi : i ∈ s) (hai : a ∈ K i) :
    ∃ U ∈ 𝓝 a, U ∩ (⋃ j ∈ s, K j) = U ∩ K i := by
  have ht : ∀ j ∈ s, a ∈ K j ↔ j ∈ ({i} : Set ι) := by
    intro j hj
    constructor
    · intro haj
      rw [mem_singleton_iff]
      exact (h.unique ⟨hi, hai⟩ ⟨hj, haj⟩).symm
    · intro hji
      have hji : j = i := by simpa only [mem_singleton_iff] using hji
      subst j
      exact hai
  obtain ⟨U, hU, hEq⟩ :=
    exists_nhds_inter_biUnion_eq_biUnion hs (singleton_subset_iff.mpr hi) hK ht
  refine ⟨U, hU, ?_⟩
  simp at hEq
  exact hEq

/-- If a point belongs exactly to the members indexed by `t` of a finite family of closed sets,
then the union agrees locally with the union over `t`. -/
theorem exists_nhds_inter_iUnion_eq_biUnion {X ι : Type*} [TopologicalSpace X] [Finite ι]
    {K : ι → Set X} {a : X} {t : Set ι} (hK : ∀ i, IsClosed (K i))
    (ht : ∀ i, a ∈ K i ↔ i ∈ t) :
    ∃ U ∈ 𝓝 a, U ∩ (⋃ i, K i) = U ∩ ⋃ i ∈ t, K i := by
  simpa using
    exists_nhds_inter_biUnion_eq_biUnion (s := Set.univ) (t := t) Set.finite_univ
      (subset_univ t) (fun i _ ↦ hK i) (fun i _ ↦ ht i)

/-- If a point belongs to exactly one member of a finite family of closed sets, then the union
agrees locally with that member. -/
theorem exists_nhds_inter_iUnion_eq {X ι : Type*} [TopologicalSpace X] [Finite ι]
    {K : ι → Set X} {a : X} {i : ι} (hK : ∀ j, IsClosed (K j))
    (h : ∃! j, a ∈ K j) (hi : a ∈ K i) :
    ∃ U ∈ 𝓝 a, U ∩ (⋃ j, K j) = U ∩ K i := by
  have ht : ∀ j, a ∈ K j ↔ j ∈ ({i} : Set ι) := by
    intro j
    constructor
    · intro hj
      rw [mem_singleton_iff]
      exact (h.unique hi hj).symm
    · intro hji
      have hji : j = i := by simpa only [mem_singleton_iff] using hji
      subst j
      exact hi
  obtain ⟨U, hU, hEq⟩ :=
    exists_nhds_inter_iUnion_eq_biUnion (K := K) (a := a) (t := ({i} : Set ι)) hK ht
  refine ⟨U, hU, ?_⟩
  simp at hEq
  exact hEq

end
