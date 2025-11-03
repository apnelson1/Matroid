import Matroid.Graph.Degree.Basic

open Set

variable {α β : Type*} [CompleteLattice α] {x y z u v w : α} {e f : β} {G H : Graph α β} {d : ℕ}

namespace Graph

/-- `G.DegreePos` means that `G` has no degree-zero vertices. -/
def DegreePos (G : Graph α β) : Prop := ∀ ⦃x⦄, x ∈ V(G) → ∃ e, G.Inc e x

lemma DegreePos.one_le_eDegree (hG : G.DegreePos) (hx : x ∈ V(G)) : 1 ≤ G.eDegree x := by
  rw [ENat.one_le_iff_ne_zero]
  simp only [ne_eq, eDegree_eq_zero_iff_inc, not_forall, not_not]
  exact hG hx

lemma DegreePos.one_le_degree [G.LocallyFinite] (hG : G.DegreePos) (hx : x ∈ V(G)) :
    1 ≤ G.degree x := by
  rw [← Nat.cast_le (α := ℕ∞), natCast_degree_eq]
  exact hG.one_le_eDegree hx

lemma degreePos_iff' : G.DegreePos ↔ ∀ ⦃x⦄, x ∈ V(G) → G.eDegree x ≠ 0 := by
  simp_rw [← ENat.one_le_iff_ne_zero]
  refine ⟨fun h _ ↦ h.one_le_eDegree, fun h x hx ↦ ?_⟩
  suffices hcard : {e | G.Inc e x}.encard ≠ 0 by simpa [eq_empty_iff_forall_notMem] using hcard
  exact fun h0 ↦ by simpa [h0] using (h hx).trans <| G.eDegree_le_two_mul_encard_setOf_inc x

lemma degreePos_iff [G.LocallyFinite] : G.DegreePos ↔ ∀ ⦃x⦄, x ∈ V(G) → G.degree x ≠ 0 := by
  simp [Ne, ← @Nat.cast_inj ℕ∞, natCast_degree_eq, degreePos_iff']

lemma DegreePos.finite_of_edgeSet_finite (hG : G.DegreePos) (hE : E(G).Finite) :
    G.Finite where
  vertexSet_finite := by
    have hle := ENat.tsum_le_tsum (f := fun x : V(G) ↦ 1) (g := fun x : V(G) ↦ G.eDegree x)
    simp only [Pi.le_def, Subtype.coe_prop, (fun x ↦ hG.one_le_eDegree), implies_true,
      ENat.tsum_subtype_const, one_mul, G.handshake_eDegree_subtype, forall_const] at hle
    rw [← encard_lt_top_iff] at hE ⊢
    generalize ha : E(G).encard = a at hle hE
    generalize hb : V(G).encard = b at hle
    enat_to_nat
  edgeSet_finite := hE

lemma DegreePos.edgeSet_finite_iff (hG : G.DegreePos) : E(G).Finite ↔ G.Finite :=
  ⟨hG.finite_of_edgeSet_finite, fun h ↦ h.edgeSet_finite⟩

lemma DegreePos.edgeSet_nonempty (hG : G.DegreePos) (hV : V(G).Nonempty) : E(G).Nonempty := by
  obtain ⟨e, he⟩ := hG hV.choose_spec
  exact ⟨e, he.edge_mem⟩

/-- `G.MaxDegreeLE d` means that `G` has maximum degree at most `d`.  -/
def MaxDegreeLE (G : Graph α β) (d : ℕ) : Prop := ∀ v, G.eDegree v ≤ d

lemma MaxDegreeLE.degree_le (h : G.MaxDegreeLE d) (v : α) : G.degree v ≤ d :=
  ENat.toNat_le_of_le_coe (h v)

lemma MaxDegreeLE.mono (h : G.MaxDegreeLE d) (hle : H ≤ G) : H.MaxDegreeLE d :=
  fun v ↦ (eDegree_mono hle _).trans <| h v

lemma MaxDegreeLE.locallyFinite (h : G.MaxDegreeLE d) : G.LocallyFinite where
  finite x := finite_of_encard_le_coe <| (G.encard_setOf_inc_le_eDegree x).trans (h x)

/-- A version of `maxDegreeLE_iff` for infinite graphs. -/
lemma maxDegreeLE_iff' : G.MaxDegreeLE d ↔ ∀ v ∈ V(G), G.eDegree v ≤ d :=
  ⟨fun h v _ ↦ h v, fun h v ↦ (em _).elim (h v) fun h ↦ by simp [eDegree_eq_zero_of_notMem h]⟩

lemma maxDegreeLE_iff [G.LocallyFinite] : G.MaxDegreeLE d ↔ ∀ v ∈ V(G), G.degree v ≤ d := by
  simp_rw [maxDegreeLE_iff', ← @Nat.cast_le ℕ∞, natCast_degree_eq]

lemma MaxDegreeLE.encard_edgeSet_le (h : G.MaxDegreeLE d) : 2 * E(G).encard ≤ d * V(G).encard := by
  rw [← handshake_eDegree_subtype, ← ENat.tsum_one, ENat.mul_tsum]
  exact ENat.tsum_le_tsum fun x ↦ (h x).trans_eq <| by simp

lemma MaxDegreeLE.ncard_edgeSet_le [G.Finite] (h : G.MaxDegreeLE d) :
    2 * E(G).ncard ≤ d * V(G).ncard := by
  simp_rw [← Nat.cast_le (α := ℕ∞), Nat.cast_mul, Nat.cast_ofNat]
  rw [G.edgeSet_finite.cast_ncard_eq, G.vertexSet_finite.cast_ncard_eq]
  exact h.encard_edgeSet_le

lemma MaxDegreeLE.finite_of_vertexSet_finite (h : G.MaxDegreeLE d) (hV : V(G).Finite) :
    G.Finite := by
  have := h.locallyFinite
  rwa [← vertexSet_finite_iff]

lemma maxDegreeLE_zero_iff : G.MaxDegreeLE 0 ↔ G = Graph.noEdge P(G) β := by
  refine ⟨fun h ↦ Graph.ext (by simp) fun e x y ↦ ?_, fun h ↦ ?_⟩
  · suffices ¬ G.IsLink e x y by simpa
    have hinc : ∀ f, ¬ G.Inc f x := by simpa [eDegree_eq_zero_iff_inc] using h x
    exact fun h ↦ hinc _ h.inc_left
  rw [h]
  simp only [MaxDegreeLE, Nat.cast_zero]
  exact fun v ↦ (eDegree_le_two_mul_encard_setOf_inc _ _).trans <| by simp

/-- `G.Regular d` means that every vertex has degree `d`. -/
protected def Regular (G : Graph α β) (d : ℕ) : Prop := ∀ ⦃v⦄, v ∈ V(G) → G.eDegree v = d

lemma Regular.degree (hG : G.Regular d) (hv : v ∈ V(G)) : G.degree v = d := by
  simp [Graph.degree, hG hv]

lemma regular_iff [G.LocallyFinite] : G.Regular d ↔ ∀ v ∈ V(G), G.degree v = d := by
  simp [Graph.Regular, ← @Nat.cast_inj ℕ∞]

lemma Regular.maxDegreeLE (hG : G.Regular d) : G.MaxDegreeLE d :=
  maxDegreeLE_iff'.2 fun _ hv ↦ (hG hv).le

lemma Regular.encard_edgeSet (hG : G.Regular d) : 2 * E(G).encard = d * V(G).encard := by
  simp_rw [← handshake_eDegree_subtype, fun v : V(G) ↦ hG v.2, ENat.tsum_subtype_const]

lemma Regular.degreePos (hG : G.Regular d) (hd : d ≠ 0) : G.DegreePos :=
  degreePos_iff'.2 fun x hx ↦ by simpa [hG hx]

lemma Regular.edgeSet_finite_iff (hG : G.Regular d) (hd : d ≠ 0) : E(G).Finite ↔ G.Finite :=
  (hG.degreePos hd).edgeSet_finite_iff

lemma Regular.ncard_edgeSet (hG : G.Regular d) : 2 * E(G).ncard = d * V(G).ncard := by
  obtain rfl | d := d
  · rw [maxDegreeLE_zero_iff.1 hG.maxDegreeLE]
    simp
  have := hG.maxDegreeLE.locallyFinite
  by_cases hfin : G.Finite
  · simp [← @Nat.cast_inj ℕ∞, hfin.vertexSet_finite.cast_ncard_eq,
      hfin.edgeSet_finite.cast_ncard_eq, hG.encard_edgeSet]
  rw [Infinite.ncard, Infinite.ncard, mul_zero, mul_zero]
  · rwa [Set.Infinite, vertexSet_finite_iff]
  rwa [Set.Infinite, hG.edgeSet_finite_iff (by simp)]

lemma Regular.of_isClosedSubgraph (hG : G.Regular d) (hH : H ≤c G) : H.Regular d :=
  fun _ h ↦ by rw [hH.eDegree_eq h, hG (vertexSet_mono hH.le h)]
