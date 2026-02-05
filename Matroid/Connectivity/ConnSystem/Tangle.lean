import Matroid.Connectivity.ConnSystem.Basic
import Matroid.Connectivity.Separation.Basic

open Set ConnSystem

variable {α R : Type*} {E F X Y S : Set α} {e f : α} [Add R] [PartialOrder R]

/-- A `Tangle` of order `k` assigns a `Small` side to exactly one side of each bipartition
of its ground set with connectivity at most `k`.  -/
structure Tangle (μ : ConnSystem α R) (k : R) where
  Small : Set α → Prop
  compl_singleton_not_small : ∀ e ∈ μ.E, ¬ Small (μ.E \ {e})
  conn_le_of_small : ∀ ⦃X⦄, Small X → μ X ≤ k
  small_or_small_compl : ∀ ⦃X⦄, X ⊆ μ.E → μ X ≤ k → Small X ∨ Small (μ.E \ X)
  union_union_ssubset : ∀ ⦃X Y Z⦄, Small X → Small Y → Small Z → X ∪ Y ∪ Z ⊂ μ.E

initialize_simps_projections Tangle (Small → small)

namespace Tangle

variable {R : Type*} [PartialOrder R] [Add R] {μ ν : ConnSystem α R} {k : R} {T : Tangle μ k}





@[grind .]
lemma Small.ssubset_ground (hX : T.Small X) : X ⊂ μ.E := by
  simpa using (T.union_union_ssubset hX hX hX)

lemma Small.subset_ground (hX : T.Small X) : X ⊆ μ.E :=
  hX.ssubset_ground.subset

lemma Small.conn_le (h : T.Small X) : μ X ≤ k :=
  T.conn_le_of_small h

lemma Small.union_ssubset (hX : T.Small X) (hY : T.Small Y) : X ∪ Y ⊂ μ.E := by
  simpa using T.union_union_ssubset hX hX hY

@[mk_iff]
structure Large (T : Tangle μ k) (X : Set α) : Prop where
  compl_small : T.Small <| μ.E \ X
  subset_ground : X ⊆ μ.E

lemma Large.conn_le (h : T.Large X) : μ X ≤ k := by
  simpa using h.compl_small.conn_le

attribute [grind .] Large.subset_ground

lemma small_or_large (hX : μ X ≤ k) (hXE : X ⊆ μ.E) : T.Small X ∨ T.Large X :=
  (T.small_or_small_compl hXE hX).elim Or.inl fun h ↦ Or.inr ⟨h, hXE⟩

lemma Small.compl_large (h : T.Small X) : T.Large (μ.E \ X) :=
  ⟨by rwa [diff_diff_cancel_left h.subset_ground], diff_subset⟩

lemma Small.subset (hX : T.Small X) (hYX : Y ⊆ X) (hY : μ Y ≤ k) : T.Small Y :=
  (T.small_or_large hY (hYX.trans hX.subset_ground)).elim id
    fun h ↦ by grind [h.compl_small.union_ssubset hX]

lemma Large.not_small (hX : T.Large X) : ¬ T.Small X :=
  fun hX' ↦ (hX'.union_ssubset hX.compl_small).ne <| by simpa using hX.subset_ground

lemma Small.not_large (hX : T.Small X) : ¬ T.Large X :=
  fun hX' ↦ (hX'.compl_small.union_ssubset hX).ne <| by simpa using hX.subset_ground

@[simp]
lemma ground_not_small (T : Tangle μ k) : ¬ T.Small μ.E :=
  fun h ↦ by simpa using (h.union_ssubset h).ne

@[simp]
lemma empty_not_large (T : Tangle μ k) : ¬ T.Large ∅ :=
  fun h ↦ T.ground_not_small <| by simpa using h.compl_small

@[simp]
lemma singleton_not_large (T : Tangle μ k) (e) : ¬ T.Large {e} :=
  fun h ↦ T.compl_singleton_not_small e (by simpa using h.subset_ground) h.compl_small

protected lemma ext {T T' : Tangle μ k} (h : ∀ ⦃X⦄, T.Small X → T'.Small X) : T = T' := by
  cases T with
  | mk Small h₁ h₂ h₃ h₄=>
  cases T' with
  | mk Small' h₁' h₂' h₃' h₄' =>
  simp_all only [mk.injEq]
  ext X
  refine ⟨fun X ↦ h X, fun h' ↦ ?_⟩
  by_contra hcon
  specialize h₃ (X := X) (by simpa using (h₄' h' h' h').subset) (h₂' h')
  rw [or_iff_right hcon] at h₃
  exact (h₄' (h h₃) h' h').not_subset (by grind)

lemma not_large_subsingleton (hX : X.Subsingleton) : ¬ T.Large X := by
  obtain rfl | ⟨e, rfl⟩ := hX.eq_empty_or_singleton
  · exact T.empty_not_large
  exact T.singleton_not_large e

lemma small_bnot_iff {P : μ.E.Bipartition} {i : Bool} : T.Small (P (!i)) ↔ T.Large (P i) := by
  rw [large_iff, P.compl_eq, and_iff_left P.subset]

lemma large_bnot_iff {P : μ.E.Bipartition} {i : Bool} : T.Large (P (!i)) ↔ T.Small (P i) := by
  rw [← small_bnot_iff, Bool.not_not]

lemma small_false_iff {P : μ.E.Bipartition} : T.Small (P false) ↔ T.Large (P true) :=
  small_bnot_iff (i := true)

lemma large_false_iff {P : μ.E.Bipartition} : T.Large (P false) ↔ T.Small (P true) :=
  large_bnot_iff (i := true)

lemma small_compl_iff (hXE : X ⊆ μ.E) : T.Small (μ.E \ X) ↔ T.Large X := by
  rw [large_iff, and_iff_left hXE]

lemma large_compl_iff (hXE : X ⊆ μ.E) : T.Large (μ.E \ X) ↔ T.Small X := by
  rw [large_iff, diff_diff_cancel_left hXE, and_iff_left diff_subset]

lemma not_small_iff (hX : μ X ≤ k) (hXE : X ⊆ μ.E) : ¬ T.Small X ↔ T.Large X :=
  ⟨fun h ↦ by grind [T.small_or_large hX hXE], Large.not_small⟩

lemma not_large_iff (hX : μ X ≤ k) (hXE : X ⊆ μ.E) : ¬ T.Large X ↔ T.Small X :=
  ⟨fun h ↦ by grind [T.small_or_large hX hXE], Small.not_large⟩

lemma Small.union_small (hX : T.Small X) (hY : T.Small Y) (hXY : μ (X ∪ Y) ≤ k) :
    T.Small (X ∪ Y) := by
  rw [← not_large_iff hXY (union_subset hX.subset_ground hY.subset_ground)]
  refine fun hl ↦ (T.union_union_ssubset hX hY hl.compl_small).not_subset ?_
  grw [union_diff_self, ← subset_union_right]

@[simps]
def truncate (T : Tangle μ k) {k'} (hk' : k' ≤ k) : Tangle μ k' where
  Small X := T.Small X ∧ μ X ≤ k'
  compl_singleton_not_small := by simp +contextual [T.compl_singleton_not_small]
  conn_le_of_small := by simp
  small_or_small_compl X hX hXk' := by simp [hXk', T.small_or_small_compl hX (hXk'.trans hk')]
  union_union_ssubset := by grind [T.union_union_ssubset]

@[simps]
def induce {μ ν : ConnSystem α R} (T : Tangle ν k) (h_le : ν ≤ μ) : Tangle μ k where
  Small X := X ⊆ μ.E ∧ μ X ≤ k ∧ T.Small (X ∩ ν.E)
  compl_singleton_not_small e heF h := by
    refine T.not_large_subsingleton ((subsingleton_singleton (a := e)).anti ?_) h.2.2.compl_large
    grind [ν.subset_of_le h_le]
  conn_le_of_small := by simp +contextual
  small_or_small_compl X hXE hXk := by
    rw [and_iff_right hXE, and_iff_right diff_subset, μ.conn_compl, and_iff_right hXk,
      and_iff_right hXk, inter_comm (_ \ _), ← inter_diff_assoc,
      inter_eq_self_of_subset_left h_le.1, ← diff_inter_self_eq_diff]
    exact T.small_or_small_compl inter_subset_right <| by grw [ν.conn_inter_ground, h_le.2, hXk]
  union_union_ssubset X Y Z hX hY hZ := by
    grind [ν.subset_of_le h_le, T.union_union_ssubset hX.2.2 hY.2.2 hZ.2.2]

@[simps!]
def induceSubset (T : Tangle μ k) (hF : μ.E ⊆ F) : Tangle (μ.induce hF) k :=
  T.induce <| μ.le_induce hF

lemma induce_small_iff_of_subset {T : Tangle ν k} {hle : ν ≤ μ} (hX : X ⊆ ν.E) :
    (T.induce hle).Small X ↔ μ X ≤ k ∧ T.Small X := by
  rw [induce_small, inter_eq_self_of_subset_left hX, and_iff_right]
  grw [hX, ConnSystem.subset_of_le hle]

lemma induce_large_iff {T : Tangle ν k} {hle : ν ≤ μ} :
    (T.induce hle).Large X ↔ X ⊆ μ.E ∧ μ X ≤ k ∧ T.Large (X ∩ ν.E) := by
  by_cases hXE : X ⊆ μ.E
  · by_cases hX : μ X ≤ k
    · rw [← not_small_iff hX hXE, induce_small, ← not_small_iff _ inter_subset_right]
      · tauto
      grw [ConnSystem.conn_inter_ground, ← hX, conn_le_of_le hle]
    exact iff_of_false (fun h ↦ hX h.conn_le) (by grind)
  exact iff_of_false (fun h ↦ hXE h.subset_ground) (fun h ↦ hXE h.1)

lemma induce_large_iff_of_subset {T : Tangle ν k} {hle : ν ≤ μ} (hX : X ⊆ ν.E) :
    (T.induce hle).Large X ↔ μ X ≤ k ∧ T.Large X := by
  rw [induce_large_iff, inter_eq_self_of_subset_left hX, and_iff_right]
  grw [hX, subset_of_le hle]

lemma Small.of_induce {T : Tangle ν k} {hle : ν ≤ μ} (h : (T.induce hle).Small X) :
    T.Small (X ∩ ν.E) := by
  grind [induce_small]

lemma Large.of_induce {T : Tangle ν k} {hle : ν ≤ μ} (h : (T.induce hle).Large X) :
    T.Large (X ∩ ν.E) := by
  grind [induce_large_iff]

lemma exists_of_ne {T' : Tangle μ k} (h_ne : T ≠ T') :
    ∃ X ⊆ μ.E, μ X ≤ k ∧ T.Small X ∧ T'.Large X := by
  contrapose! h_ne
  refine Tangle.ext fun Y hY ↦ ?_
  rw [← not_large_iff hY.conn_le hY.subset_ground]
  exact h_ne Y hY.subset_ground hY.conn_le hY

lemma exists_bipartition_bool_of_ne {T' : Tangle μ k} (h_ne : T ≠ T') (b : Bool) :
    ∃ (P : μ.E.Bipartition), μ.pConn P ≤ k ∧ T.Small (P b) ∧
      ∀ i, T.Small (P i) ↔ T'.Large (P i) := by
  obtain ⟨X, hXE, hXk, hX, hX'⟩ := exists_of_ne h_ne
  refine ⟨Bipartition.ofSubset hXE b, by simpa, by simpa, fun i ↦ ?_⟩
  obtain rfl | rfl := i.eq_or_eq_not b
  · simp [hX, hX']
  simp only [↓Bipartition.ofSubset_apply, Bool.not_beq_self, cond_false]
  exact iff_of_false hX.compl_large.not_small hX'.compl_small.not_large

lemma exists_bipartition_of_ne {T' : Tangle μ k} (h_ne : T ≠ T') :
    ∃ (P : μ.E.Bipartition), μ.pConn P ≤ k ∧ T.Small (P false) ∧ T'.Small (P true) := by
  obtain ⟨X, hXE, hXk, hX, hX'⟩ := exists_of_ne h_ne
  exact ⟨Bipartition.ofSubset hXE false, by simp [hXk, hX, hX'.compl_small]⟩

lemma empty_small {R : Type*} [AddZeroClass R] [PartialOrder R] [CanonicallyOrderedAdd R]
    {k : R} {μ : ConnSystem α R} (T : Tangle μ k) (hμ : μ.Normal) : T.Small ∅ := by
  have h := T.small_or_large (by simp [hμ.conn_empty]) (empty_subset _)
  rwa [or_iff_left T.empty_not_large] at h

lemma singleton_small {R : Type*} [One R] [Zero R] [Add R] [PartialOrder R]
    {k : R} {μ : ConnSystem α R} (T : Tangle μ k) (hk : 1 ≤ k) (hμ : μ.Unitary) (he : e ∈ μ.E) :
    T.Small {e} := by
  have h := T.small_or_large (X := {e}) (by grw [hμ.conn_singleton_le e, hk]) (by simpa)
  rwa [or_iff_left (T.singleton_not_large _)] at h

lemma small_of_encard_le {μ : ConnSystem α ℕ∞} {k : ℕ∞} (T : Tangle μ k) (hμ : μ.Unitary)
    (hk : k ≠ ⊤) (hX : X.encard ≤ k) (hXE : X ⊆ μ.E) : T.Small X := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one
  · rw [show X = ∅ by simpa using hX]
    exact T.empty_small hμ.conn_empty
  have hfin : X.Finite := by rw [← encard_lt_top_iff]; enat_to_nat!
  induction X, hfin using Finite.induction_on with
  | empty => apply T.empty_small hμ.conn_empty
  | @insert e X heX hfin ih =>
    specialize ih (by grw [← hXE, ← subset_insert]) (by grw [← hX, ← subset_insert])
    exact union_singleton ▸ ih.union_small (Y := {e}) (T.singleton_small (by simp) hμ (by grind))
      (by grw [union_singleton, hμ.conn_le_encard, hX])

end Tangle

namespace ConnSystem

open Tangle

variable {R : Type*} [PartialOrder R] [Add R] {μ ν : ConnSystem α R} {k : R}

lemma AdheresTo.eq_of_induce_eq {T₀ T₁ : Tangle ν k} (h : ν.AdheresTo μ)
    (hT : T₀.induce h.le = T₁.induce h.le) : T₀ = T₁ := by
  by_contra hcon
  obtain ⟨P, hPj, -, hP⟩ := Tangle.exists_bipartition_bool_of_ne hcon false
  obtain ⟨i, P₀, hP₀⟩ := h.forall_splits P
  wlog hi : T₀.Small (P i) generalizing T₀ T₁ with aux
  · refine aux hT.symm (Ne.symm hcon) (fun b ↦ ?_) ?_
    · rw [← Tangle.small_bnot_iff, hP, Tangle.large_bnot_iff]
    rwa [← not_large_iff (by rwa [ConnSystem.conn_eq_pConn]) P.subset, ← hP]
  have hle (j) : μ (P₀ j) ≤ k := by grw [hP₀, hPj]
  have hle' (j) : ν (P₀ j) ≤ k := (h.conn_le _).trans <| hle j
  obtain ⟨b, hb⟩ : ∃ b, T₁.Large (P₀ b) := by
    simp_rw [← not_small_iff (hle' _) (P₀.subset.trans P.subset)]
    by_contra! hcon
    rw [hP, ← small_bnot_iff] at hi
    have h' := T₁.union_union_ssubset (hcon true) (hcon false) hi
    rw [P₀.union_eq, P.union_bool_eq] at h'
    exact h'.ne rfl
  have h' : (T₀.induce h.le).Large (P₀ b) := by
    rwa [hT, induce_large_iff_of_subset (P₀.subset.trans P.subset), and_iff_right (hle _)]
  refine (h'.compl_small.of_induce.union_ssubset hi).not_subset ?_
  grw [← inter_diff_right_comm, inter_eq_self_of_subset_right h.subset, P₀.subset,
    diff_union_of_subset P.subset]

/-- A connectivity system is `k`-entangled if there is at most one tangle of each order `j < k`. -/
def Entangled (μ : ConnSystem α R) (k : R) := ∀ ⦃j⦄, j < k → Subsingleton (Tangle μ j)

lemma Entangled.entangled_of_adheresTo (hμ : μ.Entangled k) (h : ν.AdheresTo μ) :
    ν.Entangled k :=
  fun _ hjk ↦ ⟨fun _ _ ↦ h.eq_of_induce_eq ((hμ hjk).elim ..)⟩


--   have := T.induce h.subset
  -- have h_eq : T.induce h.subset = T'.induce h.subset := by
  --   have := (hμ hjk).elim (T.induce h.subset) (T'.induce h.subset)
