import Mathlib.Combinatorics.Graph.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Set.Card
import Matroid.ForMathlib.Card
import Matroid.ForMathlib.ENat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.ENat
import Mathlib.Algebra.BigOperators.WithTop
import Matroid.ForMathlib.Topology.ENat




open Set

variable {α β : Type*} {x y z u v w : α} {e f : β} {G H : Graph α β}


namespace Graph


/-
For mathlib
-/

@[simp]
lemma not_isLink_of_not_mem_edgeSet (he : e ∉ E(G)) : ¬ G.IsLink e x y :=
  mt IsLink.edge_mem he

@[simp]
lemma not_inc_of_not_mem_edgeSet (he : e ∉ E(G)) : ¬ G.Inc e x :=
  mt Inc.edge_mem he


/-- The set of ends of an edge `e`. -/
def endSet (G : Graph α β) (e : β) : Set α := {x | G.Inc e x}

@[simp]
lemma mem_endSet_iff : x ∈ G.endSet e ↔ G.Inc e x := Iff.rfl

lemma IsLink.endSet_eq (h : G.IsLink e x y) : G.endSet e = {x,y} := by
  ext a
  simp only [mem_endSet_iff, mem_insert_iff, mem_singleton_iff]
  refine ⟨fun h' ↦ h'.eq_or_eq_of_isLink h, ?_⟩
  rintro (rfl | rfl)
  · exact h.inc_left
  exact h.inc_right

lemma IsLoopAt.endSet_eq (h : G.IsLoopAt e x) : G.endSet e = {x} := by
  rw [IsLink.endSet_eq h, pair_eq_singleton]

lemma endSet_eq_of_not_mem_edgeSet (he : e ∉ E(G)) : G.endSet e = ∅ := by
  simp only [endSet, eq_empty_iff_forall_not_mem, mem_setOf_eq]
  exact fun x hx ↦ he hx.edge_mem

lemma endSet_encard_le (G : Graph α β) (e : β) : (G.endSet e).encard ≤ 2 := by
  by_cases heE : e ∈ E(G)
  · obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet heE
    rw [h.endSet_eq]
    exact encard_pair_le x y
  simp [endSet_eq_of_not_mem_edgeSet heE]

@[simp]
lemma subsingleton_setOf_isLink (G : Graph α β) (e : β) (x : α) :
    {y | G.IsLink e x y}.Subsingleton := by
  simp only [Set.Subsingleton, mem_setOf_eq]
  exact fun y hy z hz ↦ hy.right_unique hz

@[simp]
lemma endSet_finite (G : Graph α β) (e : β) : (G.endSet e).Finite :=
  finite_of_encard_le_coe <| G.endSet_encard_le e

/-- The 'incidence function' of a graph `G`. If `e : β` and `x : α`,
then `G.incFun e x` is equal to `0` if `e` is not incident to `x`,
`1` if `e` is a nonloop edge at `x` and `2` if `e` is a loop edge at `x`.
It is defined this way so that `G.incFun e` sums to two for each `e ∈ E(G)`,
which is natural for the handshake theorem and linear algebra on graphs.

The definition is contrivedly written in terms of `ncard` so it
does not require any explicit decidability assumptions. -/
noncomputable def incFun (G : Graph α β) (e : β) : α →₀ ℕ where
  support := (G.endSet_finite e).toFinset
  toFun x := {y | G.IsLink e x y}.ncard + ({y | G.IsLink e x y} ∩ {x}).ncard
  mem_support_toFun x := by
    obtain ⟨y, hy⟩ | hx := em <| G.Inc e x
    · simp [hy.isLink_iff_eq]
    simp [hx, isLink_iff_inc]

lemma IsLink.incFun_support_eq [DecidableEq α] (h : G.IsLink e x y) :
    (G.incFun e).support = {x,y} := by
  simp [incFun, h.endSet_eq]

@[simp] lemma _root_.Set.singleton_inter_eq (x : α) (s : Set α) [Decidable (x ∈ s)] :
     {x} ∩ s = if x ∈ s then {x} else ∅ := by
  split_ifs <;> simpa

@[simp] lemma _root_.Set.inter_singleton_eq (x : α) (s : Set α) [Decidable (x ∈ s)] :
    s ∩ {x} = if x ∈ s then {x} else ∅ := by
  split_ifs <;> simpa

-- noncomputable def incFun (G : Graph α β) (e : β) : α →₀ ℕ :=
--   (G.eIncFun e).mapRange ENat.toNat (by simp)

lemma incFun_eq_zero_of_not_mem (he : e ∉ E(G)) : G.incFun e = 0 := by
  simp [DFunLike.ext_iff, incFun, not_isLink_of_not_mem_edgeSet he]

lemma incFun_le_two (G : Graph α β) (e : β) (x : α) : G.incFun e x ≤ 2 := by
  obtain ⟨y, hy⟩ | hx := em <| G.Inc e x
  · suffices 1 + _ ≤ 2 by simpa [incFun, hy.isLink_iff_eq]
    have := ncard_singleton_inter y {x}
    omega
  simp [incFun, isLink_iff_inc, hx]

lemma IsNonloopAt.eIncFun_eq_one (h : G.IsNonloopAt e x) : G.incFun e x = 1 := by
  obtain ⟨y, hne, hxy⟩ := h
  simp [incFun, hxy.isLink_iff_eq, (show Disjoint {y} {x} by simpa).inter_eq]

@[simp]
lemma incFun_eq_one_iff : G.incFun e x = 1 ↔ G.IsNonloopAt e x := by
  obtain (⟨y, hxy⟩ | hex) := em <| G.Inc e x
  · simp [incFun, hxy.isLink_iff_eq, IsNonloopAt, toFinite ({y} ∩ {x}), eq_comm (a := x)]
  simp [incFun, mt IsLink.inc_left hex, mt IsNonloopAt.inc hex]

lemma IsNonloopAt.incFun_eq_one (h : G.IsNonloopAt e x) : G.incFun e x = 1 :=
  incFun_eq_one_iff.2 h

@[simp]
lemma incFun_eq_two_iff : G.incFun e x = 2 ↔ G.IsLoopAt e x := by
  obtain (⟨y, hxy⟩ | hex) := em <| G.Inc e x
  · suffices 1 + _ = 2 ↔ x = y by simpa [incFun, hxy.isLink_iff_eq, ← isLink_self_iff]
    obtain rfl | hne := eq_or_ne y x
    · simp
    simp [(show Disjoint {y} {x} by simpa).inter_eq, hne.symm]
  simp [incFun, mt IsLink.inc_left hex, hex, mt IsLoopAt.inc hex]

lemma IsLoopAt.incFun_eq_two (h : G.IsLoopAt e x) : G.incFun e x = 2 :=
  incFun_eq_two_iff.2 h

lemma Inc.incFun_ne_zero (h : G.Inc e x) : G.incFun e x ≠ 0 := by
  obtain h | h := h.isLoopAt_or_isNonloopAt
  · simp [h.incFun_eq_two]
  simp [h.incFun_eq_one]

@[simp]
lemma incFun_eq_zero_iff : G.incFun e = 0 ↔ e ∉ E(G) := by
  refine ⟨fun h he ↦ ?_, incFun_eq_zero_of_not_mem⟩
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
  obtain hx | hx := hxy.inc_left.isLoopAt_or_isNonloopAt
  · have := h ▸ hx.incFun_eq_two
    simp at this
  have := h ▸ hx.incFun_eq_one
  simp at this

lemma sum_incFun_eq_two (he : e ∈ E(G)) : (G.incFun e).sum (fun _ x ↦ x) = 2 := by
  classical
  obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet he
  obtain rfl | hne := eq_or_ne x y
  · simp [Finsupp.sum, hxy.incFun_support_eq, hxy.isLink_iff_eq, show G.IsLoopAt e x from hxy]
  simp only [Finsupp.sum, hxy.incFun_support_eq, Finset.sum_pair hne]
  rw [incFun_eq_one_iff.2 ⟨x, hne, hxy.symm⟩, incFun_eq_one_iff.2 ⟨y, hne.symm, hxy⟩]

@[simp]
lemma incFun_vertex_eq_zero_iff : G.incFun e x = 0 ↔ ¬ G.Inc e x := by
  refine ⟨fun h hinc ↦ hinc.incFun_ne_zero h, fun h ↦ ?_⟩
  simp only [incFun, Finsupp.coe_mk, Nat.add_eq_zero]
  have hrw (y) : ¬ G.IsLink e x y := mt IsLink.inc_left h
  simp [hrw]

/-! ### Vertex Degrees -/

/-- The degree of a vertex as a term in `ℕ∞`. -/
noncomputable def eDegree (G : Graph α β) (v : α) : ℕ∞ := ∑' e, G.incFun e v

/-- The degree of a vertex as a term in `ℕ` (with value zero if the degree is infinite). -/
noncomputable def degree (G : Graph α β) (v : α) : ℕ := (G.eDegree v).toNat

lemma eDegree_le_two_mul_card_edgeSet (G : Graph α β) (v : α) : G.eDegree v ≤ 2 * E(G).encard := by
  rw [eDegree, ← ENat.tsum_one, ← tsum_subtype_eq_of_support_subset (s := E(G))]
  · rw [ENat.mul_tsum]
    exact ENat.tsum_le_tsum <| by simp [Pi.le_def, G.incFun_le_two]
  simp only [Function.support_subset_iff, ne_eq, Nat.cast_eq_zero]
  simpa using fun _ ↦ Inc.edge_mem

lemma eDegree_eq_tsum_mem : G.eDegree x = ∑' e : {e | G.Inc e x}, (G.incFun e x : ℕ∞) :=
  Eq.symm <| tsum_subtype_eq_of_support_subset (f := fun e ↦ (G.incFun e x : ℕ∞)) <| by simp

@[simp] lemma natCast_degree_eq [Finite β] (G : Graph α β) (v : α) :
    (G.degree v : ℕ∞) = G.eDegree v := by
  rw [degree, ENat.coe_toNat_eq_self, ← lt_top_iff_ne_top]
  exact (G.eDegree_le_two_mul_card_edgeSet v).trans_lt <| by
    simp [lt_top_iff_ne_top, ENat.mul_eq_top_iff, E(G).toFinite]

lemma degree_eq_fintype_sum [Fintype β] (G : Graph α β) (v : α) :
    G.degree v = ∑ e, G.incFun e v := by
  rw [degree, eDegree, tsum_eq_sum (s := Finset.univ) (by simp), ← Nat.cast_inj (R := ℕ∞),
    Nat.cast_sum, ENat.coe_toNat]
  exact WithTop.sum_ne_top.2 fun i _ ↦ WithTop.coe_ne_top

lemma degree_eq_finsum (G : Graph α β) (v : α) : G.degree v = ∑ᶠ e, G.incFun e v := by
  obtain hfin | hinf := {e | G.Inc e v}.finite_or_infinite
  · rw [degree, eDegree, tsum_eq_sum (s := hfin.toFinset) (by simp), ← Nat.cast_inj (R := ℕ∞),
      ENat.coe_toNat, finsum_eq_sum_of_support_subset (s := hfin.toFinset), Nat.cast_sum]
    · simp
    intro h
    rw [(WithTop.sum_eq_top (s := hfin.toFinset) (f := fun e ↦ (G.incFun e v : ℕ∞)))] at h
    obtain ⟨e, he, h_eq⟩ := h
    simp [ENat.coe_ne_top (G.incFun e v)] at h_eq
  rw [degree, eDegree, ENat.toNat_eq_zero.2 (.inr _), ← finsum_of_infinite_support]
  · exact hinf.mono fun e hev ↦ by simpa
  rw [ENat.tsum_eq_top_iff]
  exact .inl <| hinf.mono fun e hev ↦ by simpa

lemma eDegree_eq_zero_iff_inc : G.eDegree v = 0 ↔ ∀ e, ¬ G.Inc e v := by
  simp [eDegree]

lemma eDegree_eq_zero_iff_adj : G.eDegree v = 0 ↔ ∀ x, ¬ G.Adj v x := by
  simp only [eDegree, ENat.tsum_eq_zero, Nat.cast_eq_zero, incFun_vertex_eq_zero_iff]
  exact ⟨fun h x ⟨e, hvx⟩ ↦ h e hvx.inc_left, fun h e ⟨y, hev⟩ ↦ h y hev.adj⟩

@[simp]
lemma finsum_incFun_eq (he : e ∈ E(G)) : ∑ᶠ v, G.incFun e v = 2 := by
  rw [← G.sum_incFun_eq_two he, Finsupp.sum, finsum_eq_finset_sum_of_support_subset]
  simp

@[simp]
lemma tsum_incFun_eq (he : e ∈ E(G)) : ∑' v, (G.incFun e v : ℕ∞) = 2 := by
  convert (Nat.cast_inj (R := ℕ∞)).2 <| G.sum_incFun_eq_two he
  rw [Finsupp.sum, tsum_eq_sum' (s := (G.incFun e).support) (by simp)]
  simp

theorem handshake_eDegree (G : Graph α β) : ∑' v, G.eDegree v = 2 * E(G).encard := by
  simp_rw [eDegree]
  rw [ENat.tsum_comm, ← ENat.tsum_subtype_const',
    ← tsum_subtype_eq_of_support_subset (s := E(G)) (by simpa using fun _ _ ↦ Inc.edge_mem)]
  simp

lemma handshake [Finite α] [Finite β] (G : Graph α β) : ∑ᶠ v, G.degree v = 2 * E(G).ncard := by
  have := Fintype.ofFinite α
  rw [← Nat.cast_inj (R := ℕ∞), finsum_eq_sum_of_fintype, Nat.cast_sum]
  simp [natCast_degree_eq, ← tsum_eq_sum (s := Finset.univ) (by simp), handshake_eDegree,
    E(G).toFinite.cast_ncard_eq]

lemma eDegree_eq_card_add_card (G : Graph α β) (x : α) : G.eDegree x =
    2 * {e | G.IsLoopAt e x}.encard + {e | G.IsNonloopAt e x}.encard := by
  have hrw : {e | G.Inc e x} = {e | G.IsLoopAt e x} ∪ {e | G.IsNonloopAt e x} := by
    simp +contextual [iff_def, Set.ext_iff, Inc.isLoopAt_or_isNonloopAt, or_imp,
      IsLoopAt.inc, IsNonloopAt.inc]
  have hdj : Disjoint {e | G.IsLoopAt e x} {e | G.IsNonloopAt e x} := by
    simp +contextual only [disjoint_left, mem_setOf_eq]
    exact fun e h ↦ h.not_isNonloopAt _
  rw [eDegree_eq_tsum_mem]
  rw [tsum_congr_set_coe (fun e ↦ (G.incFun e x : ℕ∞)) hrw,
    Summable.tsum_union_disjoint (f := (fun e ↦ (G.incFun e x : ℕ∞))) hdj ENat.summable
      ENat.summable]
  have hrw2 : ∀ e : {e | G.IsLoopAt e x}, (G.incFun e x : ℕ∞) = 2 :=
    fun ⟨e, he⟩ ↦ by simp [he.incFun_eq_two]
  have hrw1 : ∀ e : {e | G.IsNonloopAt e x}, (G.incFun e x : ℕ∞) = 1 :=
    fun ⟨e, he⟩ ↦ by simp [he.incFun_eq_one]
  simp_rw [hrw2, hrw1, ENat.tsum_subtype_const, one_mul]

/-! ### Leaves -/

/-- `G.IsLeafAt e x` means that `e` is a nonloop edge at `x`, and is also the only edge at `x`. -/
structure IsLeafAt (G : Graph α β) (e : β) (x : α) : Prop where
  isNonloopAt : G.IsNonloopAt e x
  edge_unique : ∀ ⦃f⦄, G.Inc f x → f = e

lemma IsLeafAt.not_isLoopAt (h : G.IsLeafAt e x) (f : β) : ¬ G.IsLoopAt f x := by
  refine fun h' ↦ h.isNonloopAt.not_isLoopAt x ?_
  rwa [← h.edge_unique h'.inc]

lemma IsLeafAt.eDegree (h : G.IsLeafAt e x) : G.eDegree x = 1 := by
  have hrw : {e | G.IsNonloopAt e x} = {e} := by
    simp +contextual only [Set.ext_iff, mem_setOf_eq, mem_singleton_iff, iff_def, h.isNonloopAt,
      implies_true, and_true]
    exact fun f hf ↦ h.edge_unique hf.inc
  simp [eDegree_eq_card_add_card, h.not_isLoopAt, hrw]

-- lemma isLeafAt_of_eDegree_eq_one (h : G.Inc e x) (hdeg : G.eDegree x = 1) : G.IsLeafAt e x := by
--   rw [eDegree_eq_card_add_card] at hdeg
--   refine ⟨h.isLoopAt_or_isNonloopAt.elim (fun h ↦ False.elim ?_) id, fun f hf ↦ ?_⟩
--   · have := le_self_add.trans hdeg.le
--     rw []


/-- A leaf vertex is a degree-one vertex. -/
def IsLeafVertex (G : Graph α β) (v : α) : Prop := G.degree v = 1



lemma eDegree_eq_one_iff : G.eDegree v = 1 ↔ G.IsLeafVertex v := by
  simp [IsLeafVertex, degree]

lemma IsLeafVertex.exists_unique_inc (h : G.IsLeafVertex x) : ∃! e, G.Inc e x := by
  classical
  obtain h0 | ⟨e, he : G.Inc e x⟩ := {e | G.Inc e x}.eq_empty_or_nonempty
  · rw [← eDegree_eq_one_iff, eDegree_eq_tsum_mem, ENat.tsum_eq_zero.2] at h
    · simp at h
    rw [h0]
    simp
  rw [IsLeafVertex, degree_eq_finsum] at h
  obtain hfin | hinf := {e | G.Inc e x}.finite_or_infinite
  · rw [finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (by simp),
      Finset.sum_eq_sum_diff_singleton_add (i := e) (by simpa)] at h
    have he0 := he.incFun_ne_zero
    have h0 : ∑ f ∈ hfin.toFinset \ {e}, G.incFun f x = 0 := by omega
    refine ⟨e, he, by simpa +contextual using h0⟩
  rw [finsum_of_infinite_support (hinf.mono <| by simp [subset_def])] at h
  simp at h

lemma IsLeafVertex.exists_unique_adj (h : G.IsLeafVertex x) : ∃! y, G.Adj x y := by
  obtain ⟨e, ⟨y, he⟩, hunique⟩ := h.exists_unique_inc
  refine ⟨y, he.adj, fun z ⟨f, hz⟩ ↦ ?_⟩
  rw [hunique f hz.inc_left] at hz
  exact hz.right_unique he

lemma IsLeafVertex.eq_of_adj_adj (h : G.IsLeafVertex x) (hu : G.Adj x u) (hv : G.Adj x v) :
    u = v := by
  obtain ⟨y, hy, hun⟩ := h.exists_unique_adj
  rw [hun u hu, hun v hv]

lemma IsLeafVertex.eq_of_inc_inc (h : G.IsLeafVertex x) (he : G.Inc e x) (hf : G.Inc f x) :
    e = f := by
  obtain ⟨g, hg, hun⟩ := h.exists_unique_inc
  rw [hun e he, hun f hf]

lemma IsLeafVertex.not_adj_self (h : G.IsLeafVertex x) : ¬ G.Adj x x := by
  rintro ⟨e, he⟩
  rw [← eDegree_eq_one_iff, eDegree] at h
  simpa [(isLink_self_iff.1 he).incFun_eq_two] using (ENat.le_tsum (a := e)).trans h.le

lemma IsLeafVertex.ne_of_adj (h : G.IsLeafVertex x) (hxy : G.Adj x y) : x ≠ y :=
  fun h' ↦ h.not_adj_self <| h' ▸ hxy

lemma IsLeafVertex.not_isLoopAt (h : G.IsLeafVertex x) (e) : ¬ G.IsLoopAt e x :=
  fun h' ↦ h.not_adj_self h'.adj

lemma isLeafVertex_iff_exists :
    G.IsLeafVertex x ↔ ∃ e, G.IsNonloopAt e x ∧ ∀ f, G.Inc f x → f = e := by
  refine ⟨fun h ↦ ?_, fun ⟨e, hex, heu⟩ ↦ ?_⟩
  · obtain ⟨e, ⟨y, hxy⟩, hu⟩ := h.exists_unique_inc
    exact ⟨e, ⟨y, (h.ne_of_adj hxy.adj).symm, hxy⟩, fun f hfx ↦ h.eq_of_inc_inc hfx hxy.inc_left⟩
  have h0 : {e | G.IsLoopAt e x} = ∅ :=
    eq_empty_iff_forall_not_mem.2 fun f hf ↦ hex.not_isLoopAt x <| by rwa [← heu f hf.inc]
  have h1 : {e | G.IsNonloopAt e x} = {e} := by
    simp +contextual only [Set.ext_iff, mem_setOf_eq, mem_singleton_iff, iff_def, hex,
      implies_true, and_true]
    exact fun f hf ↦ heu f hf.inc
  simp [← eDegree_eq_one_iff, eDegree_eq_card_add_card, h0, h1]

/-- A leaf edge is an edge incident with a degree-one vertex. -/
def IsLeafEdge (G : Graph α β) (e : β) := ∃ x, G.Inc e x ∧ G.IsLeafVertex x

end Graph
