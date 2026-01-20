import Matroid.Connectivity.Separation.Faithful
import Matroid.ForMathlib.Matroid.Constructions
import Matroid.ForMathlib.Data.Set.Subsingleton
import Matroid.ForMathlib.Tactic.ENatToNat

open Set Matroid.Separation Function

variable {α : Type*} {M : Matroid α} {j k : ℕ∞} {d k : ℕ∞} {A X Y : Set α} {P : M.Separation}
  {i : Bool} {f g : ℕ∞ → ℕ∞} {w : ℕ∞ → ℕ∞ → ℕ∞} {d : Matroid α → Set α → ℕ∞}

namespace Matroid

variable {dg dg' dg_l dg_r : Bool → Matroid α → Set α → Prop}

namespace Separation

/-! ### Abstract Separations -/

/-- An abstract notion of nondegenerate separation : given a degeneracy predicate on sets in `M`,
`P.IsPredSeparation` means that neither side of `P` satisfies the degeneracy predicate. -/
def IsPredSeparation (dg : Bool → Matroid α → Set α → Prop) (P : M.Separation) :=
  ∀ i, ¬ dg i M (P i)

lemma isPredSeparation_iff : P.IsPredSeparation dg ↔ ∀ i, ¬ dg i M (P i) := Iff.rfl

lemma not_isPredSeparation_iff {dg} : ¬ P.IsPredSeparation dg ↔ ∃ i, dg i M (P i) := by
  simp only [IsPredSeparation, Bool.forall_bool, not_and, not_not, Bool.exists_bool]
  grind

lemma IsPredSeparation.dual {dg dg' : Bool → Matroid α → Set α → Prop}
    (hdg : ∀ ⦃M X i⦄, X ⊆ M.E → dg' i M X → dg i M✶ X) (hP : P.IsPredSeparation dg) :
    P.dual.IsPredSeparation dg' :=
  fun i h ↦ hP i <| by simpa using hdg (by simp) h

lemma IsPredSeparation.dual_compl (hdg : ∀ ⦃M X i⦄, X ⊆ M.E → dg' i M X → dg (!i) M✶ (M.E \ X))
    (hP : P.IsPredSeparation dg) : P.dual.IsPredSeparation dg' :=
  fun i h ↦ hP (!i) <| by simpa using hdg (by simp) h

lemma IsPredSeparation.of_dual (hdg : ∀ ⦃M X i⦄, X ⊆ M.E → dg' i M X → dg i M✶ X)
    (hP : P.dual.IsPredSeparation dg) : P.IsPredSeparation dg' :=
  fun i h ↦ hP i <| hdg (by simp) h

lemma isPredSeparation_dual_iff (hdg : ∀ ⦃M X i⦄, X ⊆ M.E → dg i M X → dg i M✶ X) :
    P.dual.IsPredSeparation dg ↔ P.IsPredSeparation dg :=
  ⟨IsPredSeparation.of_dual hdg, IsPredSeparation.dual hdg⟩

lemma isPredSeparation_ofDual_iff {P : M✶.Separation}
    (hdg : ∀ ⦃M X i⦄, X ⊆ M.E → dg i M X → dg i M✶ X) :
    P.ofDual.IsPredSeparation dg ↔ P.IsPredSeparation dg := by
  rw [← isPredSeparation_dual_iff hdg, ofDual_dual]

lemma IsPredSeparation.symm (hP : P.IsPredSeparation dg) :
    P.symm.IsPredSeparation (fun i ↦ dg !i) :=
  fun i ↦ hP !i

lemma IsPredSeparation.of_symm (hP : P.symm.IsPredSeparation dg) :
    P.IsPredSeparation (fun i ↦ dg !i) :=
  fun i ↦ by simpa using hP !i

lemma isPredSeparation_symm_iff :
    P.symm.IsPredSeparation dg ↔ P.IsPredSeparation (fun i ↦ dg !i) :=
  ⟨IsPredSeparation.of_symm, fun h ↦ by simpa using h.symm⟩

lemma IsPredSeparation.mono (h_imp : ∀ ⦃M X i⦄, X ⊆ M.E → dg' i M X → dg i M X)
    (hP : P.IsPredSeparation dg) : P.IsPredSeparation dg' :=
  fun i h ↦ hP i <| h_imp (by simp) h

lemma IsPredSeparation.nonempty (h : P.IsPredSeparation dg) (hdg : ∀ i, dg i M ∅) (i : Bool) :
    (P i).Nonempty := by
  rw [nonempty_iff_ne_empty]
  refine fun he ↦ h i ?_
  rw [he]
  apply hdg

lemma IsPredSeparation.nontrivial (h : P.IsPredSeparation dg) (hdg : ∀ i, dg i M ∅) :
    P.Nontrivial := by
  simp [P.nontrivial_def, h.nonempty hdg]

def IsOffsetSeparation (P : M.Separation) (f : ℕ∞ → ℕ∞) :=
  P.IsPredSeparation (fun _ M X ↦ M.nullity X + M✶.nullity X ≤ f (M.eConn X))

lemma IsOffsetSeparation_mono {f g : ℕ∞ → ℕ∞} (h : P.IsOffsetSeparation f) (hfg : ∀ n, g n ≤ f n) :
    P.IsOffsetSeparation g :=
  fun i h' ↦ h i (h'.trans (hfg _))

lemma IsOffsetSeparation.dual (h : P.IsOffsetSeparation f) : P.dual.IsOffsetSeparation f :=
  IsPredSeparation.dual (by simp [add_comm]) h

lemma IsOffsetSeparation.of_dual {P : M✶.Separation} (h : P.IsOffsetSeparation f) :
    P.ofDual.IsOffsetSeparation f :=
  IsPredSeparation.of_dual (by simp [add_comm]) h

lemma isOffsetSeparation_dual_iff : P.dual.IsOffsetSeparation f ↔ P.IsOffsetSeparation f :=
  isPredSeparation_dual_iff (by simp [add_comm])

end Separation


variable {dg dg' : Bool → ℕ∞ → Matroid α → Set α → Prop}

/-! ### Abstract Connectivity -/

/-- An abstract notion of connectivity. `dg` is a predicate-valued function that for each `t`,
specifies what it means for a set `X` with connectivity `t` to be degenerate in a matroid `M`.
`PredConnected dg M` means that in `M`, every set of connectivity `t` either satisfies
`dg t`, or its complement satisfies `dg t`.
`
For instance, for `k`-Tutte-connectivity, sets of connectivity `k-1` or higher are not degenerate,
and sets of connectivity `k-2` or less are degenerate iff they are independent and coindependent. -/
def PredConnected (dg : Bool → ℕ∞ → Matroid α → Set α → Prop) (M : Matroid α) :=
    ∀ P : M.Separation, ∃ i, dg i P.eConn M (P i)

lemma not_predConnected_iff :
    ¬ M.PredConnected dg ↔ ∃ P : M.Separation, P.IsPredSeparation (dg · P.eConn) := by
  simp [PredConnected, Separation.IsPredSeparation]

lemma PredConnected.not_IsPredSeparation (h : M.PredConnected dg) (P : M.Separation) :
    ¬ P.IsPredSeparation (dg · P.eConn) := by
  contrapose! h
  rw [not_predConnected_iff]
  exact ⟨P, h⟩

lemma PredConnected.mono'
    (hdegen : ∀ ⦃k i M X⦄, X ⊆ M.E → dg i k M X → (dg' i k M X ∨ dg' (!i) k M (M.E \ X)))
    (h : M.PredConnected dg) : M.PredConnected dg' := by
  refine fun P ↦ ?_
  obtain ⟨i, h'⟩ := h P
  obtain h1 | h2 := hdegen P.subset_ground h'
  · exact ⟨i, h1⟩
  exact ⟨!i, by simpa using h2⟩

lemma PredConnected.mono {dg : Bool → ℕ∞ → Matroid α → Set α → Prop}
    (hdegen : ∀ ⦃i k M X⦄, X ⊆ M.E → dg i k M X → dg' i k M X)
    (h : M.PredConnected dg) : M.PredConnected dg' :=
  h.mono' fun _ _ _ _ hX h' ↦ .inl <| hdegen hX h'

lemma PredConnected.mono_compl (hdegen : ∀ ⦃i k M X⦄, X ⊆ M.E → dg i k M X → dg' (!i) k M (M.E \ X))
    (h : M.PredConnected dg) : M.PredConnected dg' :=
  h.mono' fun _ _ _ _ hX h' ↦ .inr <| hdegen hX h'

lemma PredConnected.dual' (hdegen : ∀ ⦃i k M X⦄, X ⊆ M.E → dg i k M X →
    (dg' i k M✶ X ∨ dg' (!i) k M✶ (M.E \ X))) (h : M.PredConnected dg) :
    M✶.PredConnected dg' := by
  intro P
  obtain ⟨i, hb⟩ := h.mono' (dg' := fun i k N Y ↦ dg' i k N✶ Y) (P := P.ofDual)
    (fun _ _ _ _ hX h ↦ hdegen hX h)
  exact ⟨i, by simpa using hb⟩

lemma PredConnected.dual_compl (hdg : ∀ ⦃i k M X⦄, X ⊆ M.E → dg i k M X → dg' (!i) k M✶ (M.E \ X))
    (h : M.PredConnected dg) : M✶.PredConnected dg' :=
  h.dual' fun _ _ _ _ hX h' ↦ by simp [hdg hX h']

lemma PredConnected.dual (hdegen : ∀ ⦃i k M X⦄, X ⊆ M.E → dg i k M X → dg' i k M✶ X)
    (h : M.PredConnected dg) : M✶.PredConnected dg' :=
  h.dual' fun i k N X hX h' ↦ by simp [hdegen hX h']


section Monotone

structure DeleteMonotone (dg : Matroid α → Set α → Prop) : Prop where
  mono_subset : ∀ ⦃M X Y⦄, dg M Y → X ⊆ Y → dg M X
  mono_del : ∀ ⦃M : Matroid α⦄ ⦃D : Set α⦄ ⦃P : M.Separation⦄, M.Coindep D →
    (P.delete D).IsPredSeparation (fun _ ↦ dg) → P.IsPredSeparation (fun _ ↦ dg)

end Monotone
/-- A slightly more concrete notion of connectivity that still abstracts Tutte, vertical and cyclic
connectivity. `M.numConnected dg (k+1)` means that every separation of connectivity less than `k`
has a degenerate side in the of a specified `dg`.
Unlike `PredConnected`, this is required to be symmetric in the two sides.
Internal connectivity is not an example of this, since it has a nondegeneracy condition that
depends on the connectivity. -/
def NumConnected (M : Matroid α) (dg : Matroid α → Set α → Prop) (k : ℕ∞) : Prop :=
  M.PredConnected (fun _ j M X ↦ j + 1 + 1 ≤ k → dg M X)

lemma NumConnected.mono {dg} (h : M.NumConnected dg k) (hjk : j ≤ k) : M.NumConnected dg j :=
  PredConnected.mono (fun _ _ _ _ _ h hle ↦ h (hle.trans hjk)) h

/-- A version with `k`-connectedness rather than `(k+1)`. Usually the latter is preferred-/
lemma numConnected_iff_forall' {dg} : M.NumConnected dg k ↔
    ∀ (P : M.Separation), P.eConn + 1 + 1 ≤ k → ¬ P.IsPredSeparation (fun _ ↦ dg) := by
  simp only [NumConnected, PredConnected, Bool.exists_bool, IsPredSeparation, Bool.forall_bool]
  grind

lemma numConnected_iff_forall {dg} : M.NumConnected dg (k+1) ↔
    ∀ (P : M.Separation), P.eConn + 1 ≤ k → ¬ P.IsPredSeparation (fun _ ↦ dg) := by
  simp [numConnected_iff_forall']

lemma numConnected_iff_forall_set {dg} : M.NumConnected dg (k + 1) ↔
    ∀ ⦃X⦄, X ⊆ M.E → M.eConn X + 1 ≤ k → dg M X ∨ dg M (M.E \ X) := by
  simp only [numConnected_iff_forall, IsPredSeparation, not_forall_not]
  refine ⟨fun hP X hX hconn ↦ ?_, fun h P hP ↦ ?_⟩
  · obtain ⟨rfl | rfl, hb⟩ := hP (M.ofSetSep X true) (by simpa)
    · exact .inr <| by simpa using hb
    exact .inl <| by simpa using hb
  obtain h | h := h P.subset_ground (by simpa)
  · exact ⟨true, h⟩
  exact ⟨false, by simpa using h⟩

lemma numConnected_top_iff {dg} : M.NumConnected dg ⊤ ↔ ∀ (P : M.Separation),
    ¬ P.IsPredSeparation (fun _ ↦ dg) := by
  simp [numConnected_iff_forall']

lemma numConnected_top_iff' {dg} :
    M.NumConnected dg ⊤ ↔ ∀ ⦃X⦄, X ⊆ M.E → dg M X ∨ dg M (M.E \ X) := by
  rw [← top_add (a := 1), numConnected_iff_forall_set]
  simp

lemma NumConnected.not_isPredSeparation_of_eConn {dg} (h : M.NumConnected dg (k+1))
    (hP : P.eConn + 1 ≤ k) : ¬ P.IsPredSeparation (fun _ ↦ dg) := by
  rw [numConnected_iff_forall] at h
  exact h P hP

-- lemma exists_of_not_numConnected {dg} (h : ¬ M.NumConnected dg (k+1)) :
--     ∃ (P : M.Separation), P.eConn + 1 ≤ k ∧ P.IsPredSeparation (fun _ ↦ dg) := by

  -- simpa [numConnected_iff_forall] using h

-- lemma exists_right_le_of_not_numConnected {β : Type*} [LinearOrder β] {dg}
--     (h : ¬ M.NumConnected dg (k+1)) (f : Set α → β) :
--     ∃ (P : M.Separation), P.eConn + 1 ≤ k ∧ P.IsPredSeparation dg ∧ f P.right ≤ f P.left := by
--   obtain ⟨P, hPle, hP, hPf⟩ := exists_left_le_of_not_numConnected h f
--   exact ⟨P.symm, by simpa, hP.symm, by simpa⟩

lemma not_numConnected_iff_exists {dg} : ¬ M.NumConnected dg (k+1) ↔
    ∃ (P : M.Separation), P.eConn + 1 ≤ k ∧ P.IsPredSeparation (fun _ ↦ dg) := by
  simp [numConnected_iff_forall]

lemma Separation.IsPredSeparation.not_numConnected {dg} (h : P.IsPredSeparation (fun _ ↦ dg)) :
    ¬ M.NumConnected dg (P.eConn + 1 + 1) :=
  fun hM ↦ hM.not_isPredSeparation_of_eConn rfl.le h

@[simp]
lemma numConnected_zero (M : Matroid α) (dg) : M.NumConnected dg 0 := by
  simp [NumConnected, PredConnected]

@[simp]
lemma numConnected_one (M : Matroid α) (dg) : M.NumConnected dg 1 := by
  simp [NumConnected, PredConnected]

lemma NumConnected.compl_degen {dg} (h : M.NumConnected dg k) :
    M.NumConnected (fun M X ↦ dg M (M.E \ X)) k := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  simpa [numConnected_iff_forall, IsPredSeparation, not_imp_comm] using h

lemma NumConnected.mono_degen {dg dg'} (h : M.NumConnected dg k)
    (hdg : ∀ ⦃X⦄, X ⊆ M.E → dg M X → dg' M X) : M.NumConnected dg' k := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  simp_rw [numConnected_iff_forall, not_isPredSeparation_iff] at h ⊢
  rintro P hPconn
  obtain ⟨i, hb⟩ := h P hPconn
  exact ⟨i, hdg P.subset_ground hb⟩

lemma NumConnected.congr_degen {dg dg'} (hdg : ∀ ⦃X⦄, X ⊆ M.E → (dg M X ↔ dg' M X)) :
    M.NumConnected dg = M.NumConnected dg' := by
  ext k
  exact ⟨fun h ↦ h.mono_degen fun X hX ↦ (hdg hX).1, fun h ↦ h.mono_degen fun X hX ↦ (hdg hX).2⟩

lemma NumConnected.dual {dg} (h : M.NumConnected dg k) : M✶.NumConnected (fun M X ↦ dg M✶ X) k := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  simp_rw [numConnected_iff_forall, not_isPredSeparation_iff] at h ⊢
  exact fun P hP ↦ by simpa using h P.ofDual (by simpa)

lemma NumConnected.of_dual {dg} (h : M✶.NumConnected dg k) :
    M.NumConnected (fun M X ↦ dg M✶ X) k := by
  simpa using h.dual

lemma numConnected_of_subsingleton {dg} (h : M.E.Subsingleton) (k : ℕ∞) (hdg : dg M ∅) :
    M.NumConnected dg k := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one; simp
  rw [numConnected_iff_forall]
  refine fun P hPconn hP ↦ ?_
  obtain ⟨i, hi⟩ := (P.trivial_of_ground_subsingleton h).exists_eq_empty
  exact hP i <| by rwa [hi]

/-- An uncrossing lemma for an abstract connectivity notion. -/
lemma NumConnected.eConn_union_le_of_eConn_le_eConn_le_ge {w : Matroid α → Set α → ℕ∞}
    (hw : ∀ M ⦃X Y⦄, X ⊆ Y → M.eConn X + w M X ≤ M.eConn Y + w M Y)
    (hM : M.NumConnected (fun M X ↦ w M X = 0) (k + 1)) {P Q : M.Separation} (hP : P.eConn ≤ k)
    (hQ : Q.eConn ≤ k) {b c : Bool} (hwt : k ≤ (P.inter Q b c).eConn + w M (P b ∩ Q c)) :
    (P.union Q b c).eConn ≤ k := by
  by_contra! hlt
  have hk : k ≠ ⊤ := by enat_to_nat!
  have hsm := P.eConn_inter_add_eConn_union_le Q b c
  grw [hP, hQ] at hsm
  obtain hle | hlt' := le_or_gt k (P.inter Q b c).eConn
  · grw [← hle, ENat.add_le_add_iff_left hk] at hsm
    exact hlt.not_ge hsm
  refine hM.not_isPredSeparation_of_eConn (Order.add_one_le_of_lt hlt') <| isPredSeparation_iff.2 ?_
  rintro (rfl | rfl) hdg
  · grw [P.inter_apply_false] at hdg
    have hcon := hw M (show P (!b) ∩ Q (!c) ⊆ P (!b) ∪ Q (!c) by grind)
    grw [hdg, add_zero, ← P.inter_apply_false, eConn_eq, ← le_self_add, ← P.union_apply_false,
      eConn_eq] at hcon
    exact hlt.not_ge <| by grw [hcon, hlt']
  grw [hwt, ← P.inter_apply_true, hdg, add_zero] at hlt'
  simp at hlt'

/-- A numerical notion of connectivity. If `w` is a function assigning a `ℕ∞`-weight to each set `X`
in a matroid `M`, and `f : ℕ∞ → ℕ∞` is a sequence, then `SeqConnected w f M` means that, for
each separation `P` of order `k`, one side `P i` has weight at most `f k` in `M`.

If `f = (0, .., 0, ⊤, ⊤, ..., ⊤)` with the first `⊤` in position `(k - 1)`, then
this abstracts Tutte `k`-connectivity with `w M X = M.nullity X + M✶.nullity X`,
it abstracts vertical `k`-connectivity with `w M = M✶.nullity`,
and cyclical `k`-connectivity with `w M = M.nullity`.

If `f = (0, 0, ..., 1, ⊤, ⊤, ⊤, ...)` with the `1` in position `(k-2)`,
and `w M X = M.nullity X + M✶.nullity X`, then this is internal `k`-connectivity. -/
def SeqConnected (M : Matroid α) (w : Matroid α → Set α → ℕ∞) (f : ℕ∞ → ℕ∞) :=
    M.PredConnected (fun _ k M X ↦ w M X ≤ f k)

lemma SeqConnected.exists {w} (h : M.SeqConnected w f) (P : M.Separation) :
    ∃ i, w M (P i) ≤ f P.eConn := by
  simpa using h P

lemma seqConnected_iff_exists {w } : M.SeqConnected w f ↔
    ∀ (P : M.Separation), ∃ i, w M (P i) ≤ f P.eConn := Iff.rfl

lemma SeqConnected.dual {w} (h : M.SeqConnected w f) : M✶.SeqConnected (fun M X ↦ w M✶ X) f := by
  simp_rw [seqConnected_iff_exists, dual_dual]
  rw [seqConnected_iff_exists] at h
  convert fun (P : M✶.Separation) ↦ h P.ofDual using 3
  simp

lemma seqConnected_dual_iff {w} : M✶.SeqConnected w f ↔ M.SeqConnected (fun M X ↦ w M✶ X) f :=
  ⟨fun h ↦ M.dual_dual ▸ h.dual, fun h ↦ by simpa using h.dual⟩

lemma seqConnected_dual_iff_of_forall {w : Matroid α → Set α → ℕ∞} (hw : ∀ N X, w N X = w N✶ X):
    M✶.SeqConnected w f ↔ M.SeqConnected w f := by
  rw [seqConnected_dual_iff, show (fun M ↦ w M✶) = w by ext; simp [← hw]]

lemma SeqConnected.of_dual {w} (h : M✶.SeqConnected w f) : M.SeqConnected (fun M X ↦ w M✶ X) f := by
  simpa using h.dual

lemma SeqConnected.mono_right {w} (h : M.SeqConnected w f) (hfg : f ≤ g) : M.SeqConnected w g := by
  intro P
  obtain ⟨i, hP⟩ := h.exists P
  exact ⟨i, hP.trans <| hfg P.eConn⟩

lemma SeqConnected.mono_left {w w'} (h : M.SeqConnected w f) (hw : ∀ M X, w' M X ≤ w M X) :
    M.SeqConnected w' f := by
  intro P
  obtain ⟨i, hi⟩ := h.exists P
  exact ⟨i, (hw ..).trans hi⟩

@[simp]
lemma SeqConnected_top (M : Matroid α) (w) : M.SeqConnected w ⊤ := by
  simp [SeqConnected, PredConnected]

lemma seqConnected_indicator_iff_numConnected {w} : M.SeqConnected w (indicator {i | k < i + 1} ⊤) ↔
    M.NumConnected (fun M X ↦ w M X = 0) (k + 1) := by
  simp_rw [seqConnected_iff_exists, numConnected_iff_forall, isPredSeparation_iff, not_forall_not]
  convert Iff.rfl with P
  obtain hle | hlt := le_or_gt (P.eConn + 1) k
  · simp [hle]
  simp [hlt]

lemma seqConnected_indicator_iff_numConnected' {w} :
    M.SeqConnected w (indicator {i | k < i + 1 + 1} ⊤) ↔
    M.NumConnected (fun M X ↦ w M X = 0) k := by
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one
  · simp
  simp [← seqConnected_indicator_iff_numConnected]
