import Matroid.Flat.Hyperplane
import Matroid.Paving

variable {α : Type} {M : Matroid α} {E I H B X : Set α} {e f : α} {Hs T : Set (Set α)}


namespace Matroid

open Set

section Relax

lemma IsCircuitHyperplane.insert_diff_singleton_isBase (hH : M.IsCircuitHyperplane H)
    (he : e ∈ H) (hf : f ∈ M.E \ H) : M.IsBase (insert f (H \ {e})) := by
  have hclosure := hH.isHyperplane.closure_insert_eq hf.2 hf.1
  rw [← closure_insert_closure_eq_closure_insert, ← hH.isCircuit.closure_diff_singleton_eq e,
    closure_insert_closure_eq_closure_insert,
    ← spanning_iff_closure_eq (insert_subset hf.1 (diff_subset.trans hH.subset_ground))] at hclosure
  apply hclosure.isBase_of_indep
  rw [← (hH.isCircuit.diff_singleton_indep he).notMem_closure_iff_of_notMem (fun hf' ↦ hf.2 hf'.1),
    hH.isCircuit.closure_diff_singleton_eq e, hH.isHyperplane.isFlat.closure]
  exact hf.2

lemma IsCircuitHyperplane.isBase_of_isExchange (hH : M.IsCircuitHyperplane H) (hB : B ⊆ M.E)
    (hHB : H.IsExchange B) : M.IsBase B := by
  obtain ⟨e, he, f, hf, rfl⟩ := hHB.exists
  apply hH.insert_diff_singleton_isBase he.1 (by grind)

lemma IsBase.exists_exchange_of_isCircuitHyperplane (hB : M.IsBase B) (hH : M.IsCircuitHyperplane H)
    (he : e ∈ B) : ∃ f, f ∈ H \ B ∧ (M.IsBase (insert f (B \ {e})) ∨ insert f (B \ {e}) = H) := by
  by_contra! h

  have h1 : H \ {e} ⊆ M.closure (B \ {e}) := by
    refine fun x hx ↦ by_contra fun hclosure ↦ ?_
    have hxB : x ∉ B := by
      exact fun hxB' ↦ hclosure (M.mem_closure_of_mem' ⟨hxB', hx.2⟩ (hH.subset_ground hx.1))

    refine (h x ⟨hx.1, hxB⟩).1 (hB.exchange_isBase_of_indep hxB ?_)
    rwa [← (hB.indep.diff {e}).notMem_closure_iff_of_notMem (notMem_subset diff_subset hxB)
      (hH.subset_ground hx.1)]

  rw [← closure_subset_closure_iff_subset_closure (diff_subset.trans hH.subset_ground),
    hH.isCircuit.closure_diff_singleton_eq, hH.isHyperplane.isFlat.closure] at h1
  obtain hBH := hH.isHyperplane.eq_of_subset (hB.isHyperplane_of_closure_diff_singleton he) h1

  have hb : M.IsBasis (B \ {e}) H := by
    exact (hB.indep.diff _).isBasis_of_subset_of_subset_closure
      ((M.subset_closure (B \ {e}) (diff_subset.trans hB.subset_ground)).trans hBH.symm.subset) h1
  obtain ⟨f, ⟨hfH, hfBe⟩, hfB⟩ := hH.isCircuit.isBasis_iff_insert_eq.1 hb
  refine (h _ ⟨hfH, fun hfB ↦ hfBe ⟨hfB, fun (hfe : f = e) ↦ ?_⟩⟩).2 hfB.symm
  apply hB.indep.notMem_closure_diff_of_mem he
  rwa [← hBH, ← hfe]

/-- `M.IsLawfulRelaxation T` means that `T` is a set of circuit-hyperplanes of `M`. -/
def IsLawfulRelaxation (M : Matroid α) (T : Set (Set α)) : Prop :=
  ∀ ⦃X⦄, X ∈ T → M.IsCircuitHyperplane X

@[grind →]
lemma IsLawfulRelaxation.ssubset_ground (h : M.IsLawfulRelaxation T) (hX : X ∈ T) : X ⊂ M.E :=
  (h hX).isHyperplane.ssubset_ground

lemma IsLawfulRelaxation.nonempty (h : M.IsLawfulRelaxation T) (hX : X ∈ T) : X.Nonempty :=
  (h hX).isCircuit.nonempty

lemma IsLawfulRelaxation.antichain (h : M.IsLawfulRelaxation T) :
    IsAntichain (· ⊆ ·) (T ∪ {B | M.IsBase B}) := by
  rintro B (hBT | (hB : M.IsBase B)) B' (hBT' | (hB' : M.IsBase B')) hne hss
  · exact hne <| (h hBT').isCircuit.eq_of_dep_subset (h hBT).isCircuit.dep hss
  · exact (hB'.indep.subset hss).not_dep <| (h hBT).isCircuit.dep
  · exact (h hBT').isHyperplane.not_spanning <| hB.spanning_of_superset hss
      (h.ssubset_ground hBT').subset
  exact hne <| hB.eq_of_subset_isBase hB' hss

lemma IsLawfulRelaxation.single {C} (hC : M.IsCircuitHyperplane C) :
    M.IsLawfulRelaxation {C} :=
  fun X hX ↦ by grind

/-- the set of all circuit hyperplanes is a lawful relaxation. -/
lemma IsLawfulRelaxation.all (M : Matroid α) :
    M.IsLawfulRelaxation {C | M.IsCircuitHyperplane C} := by
  simp [IsLawfulRelaxation]

/-- Relax a collection `T` of circuit-hyperplanes of a matroid `M` to obtain a new matroid whose
  bases are the old bases together with the sets in `T`. -/
@[simps]
def relax (M : Matroid α) (T : Set (Set α)) (hT : M.IsLawfulRelaxation T) :
    Matroid α where
  E := M.E
  IsBase B := M.IsBase B ∨ B ∈ T
  Indep I := M.Indep I ∨ I ∈ T
  indep_iff' I := by
    constructor
    · grind [Indep.exists_isBase_superset]
    rintro ⟨B, (hB | hBT), hIB⟩
    · exact .inl (hB.indep.subset hIB)
    obtain rfl | hssu := hIB.eq_or_ssubset
    · simp [hBT]
    simp [(hT hBT).isCircuit.ssubset_indep hssu]
  exists_isBase := by grind [M.exists_isBase]
  isBase_exchange := by
    rintro B B' (hB | hBT) hB' e he
    · obtain (hB' | hB'T) := hB'
      · grind [hB.exchange hB' he]
      grind [hB.exists_exchange_of_isCircuitHyperplane (hT hB'T) he.1]
    have hnss : ¬ (B' ⊆ B) := hT.antichain (by grind) (.inl hBT) (by grind)
    obtain ⟨f, hf⟩ := not_subset.1 hnss
    refine ⟨f, hf, .inl ?_⟩
    apply (hT hBT).insert_diff_singleton_isBase he.1 ⟨mem_of_mem_of_subset hf.1 ?_, hf.2⟩
    exact hB'.elim IsBase.subset_ground fun h ↦ (hT.ssubset_ground h).subset
  maximality := by
    rintro X hX I hI hIX
    obtain ⟨C, hIC, hCX, hCT⟩ | hnot := exists_or_forall_not (fun Y ↦ I ⊆ Y ∧ Y ⊆ X ∧ Y ∈ T)
    · refine ⟨C, hIC, maximal_iff_forall_ssuperset.2 ⟨⟨.inr hCT, hCX⟩, fun K hCK ↦ ?_⟩⟩
      rintro ⟨(hK | hK), hKX⟩
      · exact (hK.subset hCK.subset).not_dep (hT hCT).isCircuit.dep
      exact hT.antichain (.inl hCT) (.inl hK) hCK.ne hCK.subset
    rw [or_iff_left (by grind)] at hI
    obtain ⟨J, hJ, hIJ⟩ := hI.subset_isBasis_of_subset hIX
    refine ⟨J, hIJ, maximal_iff_forall_ssuperset.2 ⟨⟨.inl hJ.indep, hJ.subset⟩, fun K hJK ↦ ?_⟩⟩
    rintro ⟨(hK | hKT), hKX⟩
    · exact hJK.ne <| hJ.eq_of_subset_indep hK hJK.subset hKX
    grind
  subset_ground := by
    rintro B (hB | hBT)
    · exact hB.subset_ground
    exact (hT.ssubset_ground hBT).subset

lemma IsLawfulRelaxation.dual (h : M.IsLawfulRelaxation T) :
    M✶.IsLawfulRelaxation <| (fun X ↦ M.E \ X) '' T := by
  rintro _ ⟨C, hC, rfl⟩
  exact (h hC).compl_dual

@[simp]
lemma IsLawfulRelaxation.matroid_dual (h : M.IsLawfulRelaxation T) :
    (M.relax T h)✶ = M✶.relax _ h.dual := by
  refine ext_isBase rfl fun B (hBE : B ⊆ M.E) ↦ ?_
  simp only [relax_E, hBE, dual_isBase_iff, relax_IsBase, mem_image]
  convert Iff.rfl
  constructor
  · rintro ⟨B, hB, rfl⟩
    rwa [diff_diff_cancel_left (h.ssubset_ground hB).subset]
  exact fun h ↦ ⟨_, h, diff_diff_cancel_left hBE⟩

@[simp]
lemma relax_spanning_iff {S} (h : M.IsLawfulRelaxation T) :
    (M.relax T h).Spanning S ↔ M.Spanning S ∨ S ∈ T := by
  by_cases! hSE : ¬ S ⊆ M.E; grind
  rw [spanning_iff_compl_coindep, spanning_iff_compl_coindep, Coindep, h.matroid_dual, Coindep]
  simp only [relax_E, relax_Indep, mem_image]
  convert Iff.rfl
  refine ⟨fun h ↦ ⟨S, h, rfl⟩, fun ⟨X, hXT, hX⟩ ↦ ?_⟩
  rwa [← diff_diff_cancel_left hSE, ← hX, diff_diff_cancel_left (by grind)]

-- /-- Change a single nonbase `H` of `M` to a base, provided `H` is a circuit-hyperplane -/
-- def relax (M : Matroid α) (H : Set α) : Matroid α := M.relaxSet {H}

-- lemma relax_isBase_iff (hH : M.IsHyperplane X) (hC : M.IsCircuit X) :
--     (M.relax X).IsBase B ↔ (M.IsBase B ∨ B = X) := by
--   rw [relax, relaxSet_isBase_iff, mem_singleton_iff]; simp [hH, hC]

-- lemma relax_indep_iff (hH : M.IsHyperplane X) (hC : M.IsCircuit X) :
--     (M.relax X).Indep I ↔ (M.Indep I ∨ I = X) := by
--   rw [relax, relaxSet_indep_iff, mem_singleton_iff]; simp [hH, hC]

lemma SparsePaving.relax_all_isUniform (h : M.SparsePaving) :
    (M.relax _ (IsLawfulRelaxation.all M)).IsUniform := by
  simp only [isUniform_iff, relax_E, relax_Indep, mem_setOf_eq, relax_spanning_iff]
  grind [h.indep_or_spanning_or_isCircuitHyperplane]

lemma IsLawfulRelaxation.isFreeBase_relax (h : M.IsLawfulRelaxation T) (hX : X ∈ T) :
    (M.relax T h).IsFreeBase X :=
  ⟨by simp [hX], fun B' hB'E hB' ↦ .inl <| (h hX).isBase_of_isExchange hB'E hB'.symm⟩

end Relax

section Tighten

variable {T : Set (Set α)}

/-- A collection of free bases, with no pair of symmetric difference two.
Removing these sets from the collection of bases gives a matroid.
Doing this with some bases of a uniform matroid gives a sparse paving matroid. -/
structure IsLawfulTightening (M : Matroid α) (T : Set (Set α)) : Prop where
  isFreeBase_of_mem : ∀ ⦃B⦄, B ∈ T → M.IsFreeBase B
  pairwise_not_isExchange : T.Pairwise (fun B B' ↦ ¬ B.IsExchange B')
  ground_notMem : M.E ∉ T
  empty_notMem : ∅ ∉ T

@[grind →]
lemma IsLawfulTightening.ssubset_ground (hT : M.IsLawfulTightening T) (hBT : B ∈ T) : B ⊂ M.E :=
  (hT.isFreeBase_of_mem hBT).isBase.subset_ground.ssubset_of_ne
    fun hBE ↦ hT.ground_notMem <| hBE ▸ hBT

lemma IsLawfulTightening.nonempty (hT : M.IsLawfulTightening T) (hBT : B ∈ T) : B.Nonempty :=
  nonempty_iff_ne_empty.2 fun he ↦ hT.empty_notMem <| he ▸ hBT

lemma IsLawfulTightening.notMem_of_exchange {B'} (hT : M.IsLawfulTightening T) (hBT : B ∈ T)
    (hB' : B'.IsExchange B) : B' ∉ T :=
  fun hB'T ↦ hT.pairwise_not_isExchange hBT hB'T hB'.ne.symm hB'.symm

lemma IsLawfulTightening.exists_notMem_between {S} (hT : M.IsLawfulTightening T) (hI : M.Indep I)
    (hS : M.Spanning S) (hIS : I ⊆ S) (hIT : I ∉ T) (hST : S ∉ T) :
    ∃ B, I ⊆ B ∧ B ⊆ S ∧ M.IsBase B ∧ B ∉ T := by
  obtain ⟨B', hB', hIB', hB'S⟩ := hI.exists_isBase_subset_spanning hS hIS
  by_cases! hB'T : B' ∉ T; grind
  obtain ⟨e, he⟩ := exists_of_ssubset (hIB'.ssubset_of_ne (by grind))
  obtain ⟨f, hf⟩ := exists_of_ssubset (hB'S.ssubset_of_ne (by grind))
  have hex := (isExchange_diff_insert he.1 hf.2).symm
  exact ⟨insert f (B' \ {e}), by grind, by grind, (hT.isFreeBase_of_mem hB'T).isBase_of_exchange _
    (by grind) hex, hT.notMem_of_exchange hB'T hex⟩

lemma IsLawfulTightening.dual (h : M.IsLawfulTightening T) :
    M✶.IsLawfulTightening <| (fun B ↦ M.E \ B) '' T := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨B, hB, rfl⟩
    exact (h.isFreeBase_of_mem hB).compl_dual
  · rintro _ ⟨B, hB, rfl⟩ _ ⟨B', hB', rfl⟩ heq hex
    simp only [ne_eq] at hex heq
    rw [isExchange_diff_right_iff (h.ssubset_ground hB).subset (h.ssubset_ground hB').subset] at hex
    simp [h.pairwise_not_isExchange.eq hB hB' (by simpa)] at heq
  · rintro ⟨B, hB, h'⟩
    simp only [dual_ground, sdiff_eq_left] at h'
    rw [disjoint_iff_inter_eq_empty,
      inter_eq_self_of_subset_right (h.ssubset_ground hB).subset] at h'
    exact (h' ▸ h.empty_notMem) hB
  simp only [mem_image, diff_eq_empty, not_exists, not_and]
  refine fun B hBT hss ↦ h.ground_notMem ?_
  rwa [hss.antisymm (h.ssubset_ground hBT).subset]

/-- Given a collection of free bases of a matroid `M`, with no pair having symmetric difference
of size two, we can declare all these to be nonbases, and still have a matroid.  -/
@[simps!]
def tighten (M : Matroid α) (T : Set (Set α)) (hT : M.IsLawfulTightening T) : Matroid α where
  E := M.E
  IsBase B := M.IsBase B ∧ B ∉ T
  Indep I := M.Indep I ∧ I ∉ T
  indep_iff' I := by
    refine ⟨fun h ↦ ?_, fun ⟨B, ⟨hB, hBT⟩, hIB⟩ ↦ ?_⟩
    · grind [hT.exists_notMem_between h.1 M.ground_spanning h.1.subset_ground h.2 hT.ground_notMem]
    refine ⟨hB.indep.subset hIB, fun hIT ↦ hBT ?_⟩
    rwa [← (hT.isFreeBase_of_mem hIT).isBase.eq_of_subset_isBase hB hIB]
  exists_isBase := by grind [hT.exists_notMem_between M.empty_indep M.ground_spanning (by simp)
    hT.empty_notMem hT.ground_notMem]
  isBase_exchange := by
    intro B B' ⟨hB, hBT⟩ ⟨hB', hB'T⟩ e he
    have hnBe : ¬ M.IsBase (B \ {e}) := hB.not_isBase_of_ssubset (diff_singleton_ssubset.2 he.1)
    have hBeT : B \ {e} ∉ T := fun h' ↦ hnBe (hT.isFreeBase_of_mem h').isBase
    have huT : (B \ {e}) ∪ B' ∉ T := by
      intro h'
      grind [hB'.eq_of_subset_isBase (hT.isFreeBase_of_mem h').isBase (by simp)]
    obtain ⟨B₁, hBB₁, hB₁u, hB₁, hB₁T⟩ := hT.exists_notMem_between (hB.indep.diff {e})
      (hB'.spanning_of_superset (X := (B \ {e}) ∪ B')
      subset_union_right (by grind)) subset_union_left hBeT huT
    obtain ⟨f, hf⟩ := exists_of_ssubset (hBB₁.ssubset_of_ne (by grind))
    have hBef : M.IsBase (insert f (B \ {e})) :=
      hB.exchange_isBase_of_indep (f := f) (e := e) (by grind) (hB₁.indep.subset (by grind))
    obtain rfl : insert f (B \ {e}) = B₁ := hBef.eq_of_subset_isBase hB₁ (by grind)
    exact ⟨f, by grind, hB₁, hB₁T⟩
  maximality := by
    intro X hXE I ⟨hI, hIT⟩ hIX
    by_cases hX : M.Spanning X
    · by_cases hXT : X ∈ T
      · obtain ⟨e, he⟩ := exists_of_ssubset (hIX.ssubset_of_ne (by grind))
        refine ⟨X \ {e}, by grind, maximal_iff_forall_ssuperset.2 ?_⟩
        simp only [diff_singleton_subset_iff, subset_insert, and_true, not_and, and_imp]
        refine ⟨⟨(hT.isFreeBase_of_mem hXT).isBase.indep.diff _, fun h' ↦ ?_⟩,
          fun K hXK hK hKT hKX ↦ ?_⟩
        · grind [(hT.isFreeBase_of_mem h').isBase.eq_of_subset_isBase
            (hT.isFreeBase_of_mem hXT).isBase diff_subset]
        by_cases heK : e ∈ K
        · obtain rfl : K = X := by grind
          contradiction
        exact hXK.not_subset <| by grind
      obtain ⟨B, hIB, hBX, hB, hBT⟩ := hT.exists_notMem_between hI hX hIX hIT hXT
      refine ⟨B, hIB, maximal_iff_forall_ssuperset.2 ⟨⟨⟨hB.indep, hBT⟩, hBX⟩,
        fun K hBK ⟨⟨hIK, hKT⟩, hKX⟩ ↦ ?_⟩⟩
      obtain rfl : B = K := hB.eq_of_subset_indep hIK (by grind)
      exact hBK.ne rfl
    obtain ⟨J, hJ, hIJ⟩ := hI.subset_isBasis_of_subset hIX
    have hJT : J ∉ T := fun hJT ↦ hX <|
      (hT.isFreeBase_of_mem hJT).isBase.spanning.superset hJ.subset
    exact ⟨J, hIJ, maximal_iff_forall_ssuperset.2 ⟨⟨⟨hJ.indep, hJT⟩, hJ.subset⟩,
      fun K hJK ⟨⟨hKi, hKT⟩, hKX⟩ ↦ hJK.ne <| hJ.eq_of_subset_indep hKi hJK.subset hKX⟩⟩
  subset_ground := by grind

@[simp]
lemma IsLawfulTightening.matroid_dual (hT : M.IsLawfulTightening T) :
    (M.tighten T hT)✶ = M✶.tighten _ hT.dual := by
  refine ext_isBase rfl fun B (hB : B ⊆ M.E) ↦ ?_
  simp_rw [dual_isBase_iff', tighten_IsBase, tighten_E, dual_isBase_iff', mem_image,
    and_iff_left hB, and_congr_right_iff]
  refine fun hBc ↦ ⟨?_, fun hnot hBT ↦ hnot ⟨_, hBT, ?_⟩⟩
  · rintro hBT ⟨B', hB'T, rfl⟩
    rw [diff_diff_cancel_left (hT.ssubset_ground hB'T).subset] at hBT
    contradiction
  rw [diff_diff_cancel_left hB]

lemma IsLawfulTightening.isCircuitHyperplane_tighten (hT : M.IsLawfulTightening T) (hX : X ∈ T) :
    (M.tighten T hT).IsCircuitHyperplane X := by
  suffices aux (N : Matroid α) (Y : Set α) (T' : Set (Set α)) (hT' : N.IsLawfulTightening T')
      (hY : Y ∈ T') : (N.tighten T' hT').IsCircuit Y
  · refine ⟨aux _ _ _ hT hX, ?_⟩
    specialize aux _ (M.E \ X) _ hT.dual ⟨X, hX, rfl⟩
    rw [← hT.matroid_dual, ← IsCocircuit] at aux
    convert aux.compl_isHyperplane
    rw [tighten_E, diff_diff_cancel_left (by grind)]
  simp only [isCircuit_iff_dep_forall_diff_singleton_indep, dep_iff, tighten_Indep, hY,
    not_true_eq_false, and_false, not_false_eq_true, tighten_E, true_and, forall_mem_and]
  refine ⟨(hT'.ssubset_ground hY).subset,
    fun e heY ↦ (hT'.isFreeBase_of_mem hY).isBase.indep.diff _, fun e heY heYb ↦ ?_⟩
  have := (hT'.isFreeBase_of_mem heYb).isBase.eq_of_subset_isBase (hT'.isFreeBase_of_mem hY).isBase
    diff_subset
  grind

/-- Tighten a single free base. -/
@[simps!]
def tightenSingle (hB : M.IsFreeBase B) (hBne : B.Nonempty) (hBE : B ≠ M.E) : Matroid α :=
  M.tighten {B} ⟨by simpa, by simp, by simpa using hBE.symm, by simpa using hBne.ne_empty.symm⟩

-- @[simp]
-- lemma IsFreeBase.tighten_isBase_iff (hB : M.IsFreeBase B) (hBne : B.Nonempty) (hBE : B ≠ M.E)
--     {B' : Set α} : (hB.tighten hBne hBE).IsBase B' ↔ M.IsBase B' ∧ B' ≠ B := by
--   simp [IsFreeBase.tighten]

lemma IsLawfulRelaxation.isLawfulTightening_relax (hT : M.IsLawfulRelaxation T) :
    (M.relax T hT).IsLawfulTightening T := by
  refine ⟨fun B hB ↦ hT.isFreeBase_relax hB, fun B hB B' hB' hne hBB' ↦ ?_, ?_, ?_⟩
  · have hB'b := (hT hB).isBase_of_isExchange (by grind) hBB'
    exact (hT hB').isCircuit.not_indep hB'b.indep
  · exact fun hET ↦ (hT hET).isHyperplane.ssubset.ne rfl
  exact fun hET ↦ (hT hET).isCircuit.nonempty.ne_empty rfl

@[simp]
lemma IsLawfulRelaxation.tighten_relax (hT : M.IsLawfulRelaxation T) :
    (M.relax T hT).tighten T hT.isLawfulTightening_relax = M := by
  suffices ∀ B ⊆ M.E, M.IsBase B → B ∉ T from ext_isBase rfl <| by simpa [or_and_right]
  exact fun B _ hB hBT ↦ (hT hBT).isCircuit.not_indep hB.indep

lemma IsLawfulTightening.isLawfulRelaxation_tighten (hT : M.IsLawfulTightening T) :
    (M.tighten T hT).IsLawfulRelaxation T :=
  fun _ ↦ hT.isCircuitHyperplane_tighten

@[simp]
lemma IsLawfulTightening.relax_tighten (hT : M.IsLawfulTightening T) :
    (M.tighten T hT).relax T hT.isLawfulRelaxation_tighten = M := by
  refine ext_isBase rfl ?_
  have : ∀ B ∈ T, M.IsBase B := fun B hB ↦ (hT.isFreeBase_of_mem hB).isBase
  grind [relax_E, tighten_E, relax_IsBase, tighten_IsBase]

/-- A rank-`r` sparse paving matroid, specified by its set of circuit-hyperplanes.
`H` should be any set of `r`-sets, no two differing by a single exchange. -/
def finiteRankSparsePavingOn (E : Set α) {H : Set (Set α)} (r : ℕ)
    (card_eq : ∀ C ∈ H, C.encard = r) (exchange : ∀ C ∈ H, ∀ C' ∈ H, ¬ C.IsExchange C')
    (nonempty : ∀ C ∈ H, C.Nonempty) (ssubset_ground : ∀ C ∈ H, C ⊂ E) : Matroid α :=
  (unifOn E r).tighten H ⟨
    fun B hBH ↦ (unifOn_isUniform E r).isFreeBase <| by
      rw [unifOn_isBase_iff _ (ssubset_ground B hBH).subset, card_eq B hBH]
      grw [← card_eq B hBH, (ssubset_ground B hBH)],
    by grind [Set.Pairwise], fun hEH ↦ (ssubset_ground E hEH).ne rfl, by grind [Nonempty.ne_empty]⟩



end Tighten
