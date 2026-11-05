module

public import Matroid.Graph.Degree.Basic

@[expose] public section

open Set

variable {α β ι : Type*} {x y z u v w : α} {e f : β} {G H : Graph α β} {d : ℕ}

namespace Graph

/-- `G.DegreePos` means that `G` has no degree-zero vertices. -/
def DegreePos (G : Graph α β) : Prop := ∀ ⦃x⦄, x ∈ V(G) → ∃ e, G.Inc e x

lemma DegreePos.one_le_eDegree (hG : G.DegreePos) (hx : x ∈ V(G)) : 1 ≤ G.eDegree x := by
  rw [Order.one_le_iff_ne_zero]
  simp only [ne_eq, eDegree_eq_zero_iff_inc, not_forall, not_not]
  exact hG hx

lemma DegreePos.one_le_degree [G.LocallyFinite] (hG : G.DegreePos) (hx : x ∈ V(G)) :
    1 ≤ G.degree x := by
  rw [← ENat.natCast_le_natCast, natCast_degree_eq]
  exact hG.one_le_eDegree hx

lemma degreePos_iff' : G.DegreePos ↔ ∀ ⦃x⦄, x ∈ V(G) → G.eDegree x ≠ 0 := by
  simp_rw [← Order.one_le_iff_ne_zero]
  refine ⟨fun h _ ↦ h.one_le_eDegree, fun h x hx ↦ ?_⟩
  suffices hcard : E(G, x).encard ≠ 0 by simpa [eq_empty_iff_forall_notMem] using hcard
  exact fun h0 ↦ by simpa [h0] using (h hx).trans <| G.eDegree_le_two_mul_encard_setOf_inc x

lemma degreePos_iff [G.LocallyFinite] : G.DegreePos ↔ ∀ ⦃x⦄, x ∈ V(G) → G.degree x ≠ 0 := by
  simp [Ne, ← ENat.natCast_inj, natCast_degree_eq, degreePos_iff']

lemma DegreePos.finite_of_edgeSet_finite (hG : G.DegreePos) (hE : E(G).Finite) : G.Finite where
  vertexSet_finite := by
    have hle := tsum_le_tsum (f := fun x : V(G) ↦ 1) (g := fun x : V(G) ↦ G.eDegree x)
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
  ENat.toNat_le_of_le_natCast (h v)

lemma MaxDegreeLE.mono (h : G.MaxDegreeLE d) (hle : H ≤ G) : H.MaxDegreeLE d :=
  fun v ↦ (eDegree_mono hle _).trans <| h v

lemma MaxDegreeLE.locallyFinite (h : G.MaxDegreeLE d) : G.LocallyFinite where
  finite x := finite_of_encard_le_coe <| (G.encard_setOf_inc_le_eDegree x).trans (h x)

/-- A version of `maxDegreeLE_iff` for infinite graphs. -/
lemma maxDegreeLE_iff' : G.MaxDegreeLE d ↔ ∀ v ∈ V(G), G.eDegree v ≤ d :=
  ⟨fun h v _ ↦ h v, fun h v ↦ (em _).elim (h v) fun h ↦ by simp [eDegree_eq_zero_of_notMem h]⟩

lemma maxDegreeLE_iff [G.LocallyFinite] : G.MaxDegreeLE d ↔ ∀ v ∈ V(G), G.degree v ≤ d := by
  simp_rw [maxDegreeLE_iff', ← ENat.natCast_le_natCast, natCast_degree_eq]

lemma MaxDegreeLE.encard_edgeSet_le (h : G.MaxDegreeLE d) : 2 * E(G).encard ≤ d * V(G).encard := by
  rw [← handshake_eDegree_subtype, ← ENat.tsum_one, mul_tsum]
  exact tsum_le_tsum fun x ↦ (h x).trans_eq <| by simp

lemma MaxDegreeLE.ncard_edgeSet_le [G.Finite] (h : G.MaxDegreeLE d) :
    2 * E(G).ncard ≤ d * V(G).ncard := by
  simp_rw [← ENat.natCast_le_natCast, Nat.cast_mul, Nat.cast_ofNat]
  rw [G.edgeSet_finite.cast_ncard_eq, G.vertexSet_finite.cast_ncard_eq]
  exact h.encard_edgeSet_le

lemma MaxDegreeLE.finite_of_vertexSet_finite (h : G.MaxDegreeLE d) (hV : V(G).Finite) :
    G.Finite := by
  have := h.locallyFinite
  rwa [← vertexSet_finite_iff]

lemma maxDegreeLE_zero_iff : G.MaxDegreeLE 0 ↔ G = Graph.noEdge V(G) β := by
  refine ⟨fun h ↦ Graph.ext rfl fun e x y ↦ ?_, fun h ↦ ?_⟩
  · suffices ¬ G.IsLink e x y by simpa
    have hinc : ∀ f, ¬ G.Inc f x := by simpa [eDegree_eq_zero_iff_inc] using h x
    exact fun h ↦ hinc _ h.inc_left
  rw [h]
  simp only [MaxDegreeLE, Nat.cast_zero]
  exact fun v ↦ (eDegree_le_two_mul_encard_setOf_inc _ _).trans <| by simp

noncomputable def minEDegree (G : Graph α β) : ℕ∞ :=
  ⨅ x ∈ V(G), G.eDegree x

-- G.minDegree returns the minimum degree of its vertices if G is finite, else it returns 0
noncomputable def minDegree (G : Graph α β) : ℕ :=
  G.minEDegree.toNat

-- if G is Nonempty and LocallyFinite, then the two definitions agree
lemma natCast_minDegree_eq [G.LocallyFinite] (hG : V(G).Nonempty) :
    (G.minDegree : ℕ∞) = G.minEDegree := by
  simpa [minDegree, minEDegree]

@[simp]
lemma minEDegree_bot : (⊥ : Graph α β).minEDegree = ⊤ := by
  simp [minEDegree]

lemma minEDegree_eq_top (hG : G.minEDegree = ⊤) : G = ⊥ ∨ ¬ G.LocallyFinite := by
  by_contra! hcon
  obtain ⟨⟨x, hx⟩, hcon₂⟩ := hcon
  simp only [minEDegree, iInf_eq_top, eDegree_ne_top, imp_false] at hG
  exact hG _ hx

@[simp]
lemma minDegree_bot : (⊥ : Graph α β).minDegree = 0 := by
  simp [minDegree]

-- minEDegree is minimal among all degrees
lemma minEDegree_le_eDegree (hx : x ∈ V(G)) : G.minEDegree ≤ G.eDegree x :=
  biInf_le G.eDegree hx

lemma minDegree_le_degree [G.LocallyFinite] (hx : x ∈ V(G)) : G.minDegree ≤ G.degree x :=
  ENat.toNat_le_toNat (minEDegree_le_eDegree hx) eDegree_ne_top

-- TODO: shuffle into ENat
lemma ENat.exists_eq_biInf {S : Set ι} (hS : S.Nonempty) (f : ι → ℕ∞) :
    ∃ a ∈ S, f a = ⨅ x ∈ S, f x := by
  rw [←sInf_image]
  exact csInf_mem (hS.image f)

lemma exists_vertex_minEDegree (hG : V(G).Nonempty) : ∃ x ∈ V(G), G.eDegree x = G.minEDegree :=
  ENat.exists_eq_biInf hG _

lemma exists_vertex_minDegree (hG : V(G).Nonempty) : ∃ x ∈ V(G), G.degree x = G.minDegree := by
  obtain ⟨x, hxG, hx⟩ := exists_vertex_minEDegree hG
  refine ⟨x, hxG, ?_⟩
  simp [degree, minDegree, hx]

-- TODO: this should be moved to Graph.Basic
lemma encard_neighbors_le [G.Simple] (h : x ∈ V(G)) : N(G, x).encard + 1 ≤ V(G).encard := by
  rw [show 1 = ({x} : Set α).encard by simp, ← Set.encard_union_eq (by simp [not_adj_self])]
  exact encard_le_encard <| union_subset (neighbor_subset ..) (by simpa)

lemma eDegree_le_encard [G.Simple] (h : x ∈ V(G)) : G.eDegree x + 1 ≤ V(G).encard := by
  have solver : E(G, x) ≃ N(G, x) := G.incAdjEquiv x
  simp only [eDegree_eq_encard_inc, ge_iff_le]
  rw [solver.encard_eq]
  exact encard_neighbors_le h

lemma degree_le_ncard [G.Simple] [G.Finite] (h : x ∈ V(G)) : G.degree x + 1 ≤ V(G).ncard := by
  suffices hyp : G.eDegree x + 1 ≤ V(G).encard by
    rw [←natCast_degree_eq, ←Set.Finite.cast_ncard_eq vertexSet_finite] at hyp
    enat_to_nat!; assumption
  exact eDegree_le_encard h

lemma degree_lt_ncard [G.Simple] [G.Finite] (h : x ∈ V(G)) : G.degree x < V(G).ncard := by
  linarith [degree_le_ncard h]

lemma minEDegree_le_encard [G.Simple] (hne : V(G).Nonempty) : G.minEDegree + 1 ≤ V(G).encard := by
  obtain ⟨x, hx⟩ := hne
  have := eDegree_le_encard hx
  have h1 := minEDegree_le_eDegree hx
  enat_to_nat!
  omega

lemma minDegree_lt_ncard [G.Simple] [G.Finite] (hNe : V(G).Nonempty) :G.minDegree < V(G).ncard := by
  have ⟨v, hvG, vspec⟩ := G.exists_vertex_minDegree hNe
  rw [← vspec]
  exact degree_lt_ncard hvG

lemma unique_neighbor_of_eDegree_eq_one (hx : G.eDegree x = 1) (hxy : G.Adj x y) (hxz : G.Adj x z) :
    y = z := by
  have heq := hx ▸ G.eDegree_eq_encard_add_encard x
  have no_loops : {e | G.IsLoopAt e x}.encard = 0 := by
    enat_to_nat!
    omega
  rw [no_loops, mul_zero, zero_add, eq_comm] at heq
  simp only [encard_eq_zero, Set.ext_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false] at no_loops
  have h : {e | G.Inc e x}.Subsingleton := by
    intro e he f hf
    simp only [inc_iff_isLoopAt_or_isNonloopAt, no_loops, false_or, mem_ofPred_eq] at he hf
    exact encard_le_one_iff.mp heq.le e f he hf
  have hh : N(G, x).Subsingleton := by
    rw [← encard_le_one_iff_subsingleton] at h ⊢
    exact encard_adj_le_encard_inc.trans h
  exact hh hxy hxz

lemma IsSpanningSubgraph.minEDegree (h : H ≤s G) : H.minEDegree ≤ G.minEDegree :=
  le_iInf₂ fun v hv ↦ (minEDegree_le_eDegree (h.vertexSet_eq ▸ hv)).trans (eDegree_mono h.le v)


/-- `G.MinDegreeGE d` means that `G` has minimum degree at least `d`. -/
def MinDegreeGE (G : Graph α β) (d : ℕ) : Prop := ∀ v ∈ V(G), d ≤ G.eDegree v

lemma MinDegreeGE.le_degree [G.LocallyFinite] (h : G.MinDegreeGE d) (v : α) (hv : v ∈ V(G)) :
    d ≤ G.degree v := by
  have := h v hv
  rwa [← ENat.natCast_le_natCast, natCast_degree_eq]

lemma MinDegreeGE.mono (h : G.MinDegreeGE d) (hle : G ≤ H) (hV : V(H) ⊆ V(G)) : H.MinDegreeGE d :=
  fun v hv ↦ (h v (hV hv)).trans <| eDegree_mono hle _

lemma minDegreeGE_iff' : G.MinDegreeGE d ↔ ∀ v ∈ V(G), d ≤ G.eDegree v := Iff.rfl

lemma minDegreeGE_iff [G.LocallyFinite] : G.MinDegreeGE d ↔ ∀ v ∈ V(G), d ≤ G.degree v := by
  simp_rw [minDegreeGE_iff', ← ENat.natCast_le_natCast, natCast_degree_eq]

lemma MinDegreeGE.le_encard_edgeSet (h : G.MinDegreeGE d) : d * V(G).encard ≤ 2 * E(G).encard := by
  rw [← handshake_eDegree_subtype, ← ENat.tsum_one, mul_tsum]
  exact tsum_le_tsum fun x ↦ (h x.1 x.2).trans_eq' (by simp)

lemma MinDegreeGE.le_ncard_edgeSet [G.Finite] (h : G.MinDegreeGE d) :
    d * V(G).ncard ≤ 2 * E(G).ncard := by
  simp_rw [← ENat.natCast_le_natCast, Nat.cast_mul, Nat.cast_ofNat]
  rw [G.edgeSet_finite.cast_ncard_eq, G.vertexSet_finite.cast_ncard_eq]
  exact h.le_encard_edgeSet

/-- `G.Regular d` means that every vertex has degree `d`. -/
protected def Regular (G : Graph α β) (d : ℕ) : Prop := ∀ ⦃v⦄, v ∈ V(G) → G.eDegree v = d

lemma Regular.degree (hG : G.Regular d) (hv : v ∈ V(G)) : G.degree v = d := by
  simp [Graph.degree, hG hv]

lemma regular_iff [G.LocallyFinite] : G.Regular d ↔ ∀ v ∈ V(G), G.degree v = d := by
  simp [Graph.Regular, ← ENat.natCast_inj]

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
  · simp [← ENat.natCast_inj, hfin.vertexSet_finite.cast_ncard_eq,
      hfin.edgeSet_finite.cast_ncard_eq, hG.encard_edgeSet]
  rw [Infinite.ncard, Infinite.ncard, mul_zero, mul_zero]
  · rwa [Set.Infinite, vertexSet_finite_iff]
  rwa [Set.Infinite, hG.edgeSet_finite_iff (by simp)]

lemma Regular.of_isClosedSubgraph (hG : G.Regular d) (hH : H ≤c G) : H.Regular d :=
  fun _ h ↦ by rw [hH.eDegree_eq h, hG (vertexSet_mono hH.le h)]
