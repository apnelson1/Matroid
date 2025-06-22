import Mathlib.Combinatorics.Graph.Basic
import Matroid.Graph.Simple
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Set.Card
import Matroid.Graph.Finite
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

lemma endSet_encard_le (G : Graph α β) (e : β) : (G.endSet e).encard ≤ 2 := by
  by_cases heE : e ∈ E(G)
  · obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet heE
    rw [h.endSet_eq]
    exact encard_pair_le x y
  simp [endSet_eq_of_notMem_edgeSet heE]

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
      exact hy.inc_left
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

lemma incFun_eq_zero_of_notMem (he : e ∉ E(G)) : G.incFun e = 0 := by
  simp [DFunLike.ext_iff, incFun, not_isLink_of_notMem_edgeSet he]

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

lemma Inc.one_le_incFun (h : G.Inc e x) : 1 ≤ G.incFun e x := by
  rw [Nat.one_le_iff_ne_zero]
  exact h.incFun_ne_zero

@[simp]
lemma incFun_eq_zero_iff : G.incFun e = 0 ↔ e ∉ E(G) := by
  refine ⟨fun h he ↦ ?_, incFun_eq_zero_of_notMem⟩
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

lemma eDegree_eq_tsum_mem : G.eDegree x = ∑' e : {e | G.Inc e x}, (G.incFun e x : ℕ∞) :=
  Eq.symm <| tsum_subtype_eq_of_support_subset (f := fun e ↦ (G.incFun e x : ℕ∞)) <| by simp

lemma eDegree_le_two_mul_encard_setOf_inc (G : Graph α β) (v : α) :
    G.eDegree v ≤ 2 * {e | G.Inc e v}.encard := by
  rw [eDegree_eq_tsum_mem, ← ENat.tsum_one, ENat.mul_tsum]
  exact ENat.tsum_le_tsum <| by simp [Pi.le_def, G.incFun_le_two]

lemma eDegree_le_two_mul_card_edgeSet (G : Graph α β) (v : α) : G.eDegree v ≤ 2 * E(G).encard :=
  (G.eDegree_le_two_mul_encard_setOf_inc v).trans <| mul_left_mono <|
    encard_le_encard fun _ he ↦ he.edge_mem

@[simp]
lemma natCast_degree_eq (G : Graph α β) [G.LocallyFinite] (v : α) :
    (G.degree v : ℕ∞) = G.eDegree v := by
  rw [degree, ENat.coe_toNat_eq_self, ← lt_top_iff_ne_top]
  refine (G.eDegree_le_two_mul_encard_setOf_inc v).trans_lt ?_
  simp [lt_top_iff_ne_top, Ne, ENat.mul_eq_top_iff, G.finite_setOf_inc]

@[simp]
lemma eDegree_lt_top [G.LocallyFinite] : G.eDegree x < ⊤ := by
  rw [← natCast_degree_eq]
  exact ENat.coe_lt_top (G.degree x)

@[simp]
lemma eDegree_ne_top [G.LocallyFinite] : G.eDegree x ≠ ⊤ :=
  eDegree_lt_top.ne

lemma eDegree_eq_zero_iff_inc : G.eDegree v = 0 ↔ ∀ e, ¬ G.Inc e v := by
  simp [eDegree]

lemma eDegree_eq_zero_iff_adj : G.eDegree v = 0 ↔ ∀ x, ¬ G.Adj v x := by
  simp only [eDegree, ENat.tsum_eq_zero, Nat.cast_eq_zero, incFun_vertex_eq_zero_iff]
  exact ⟨fun h x ⟨e, hvx⟩ ↦ h e hvx.inc_left, fun h e ⟨y, hev⟩ ↦ h y hev.adj⟩

lemma degree_eq_zero_iff_inc [G.LocallyFinite] : G.degree v = 0 ↔ ∀ e, ¬ G.Inc e v := by
  rw [← Nat.cast_inj (R := ℕ∞), natCast_degree_eq, Nat.cast_zero, eDegree_eq_zero_iff_inc]

lemma degree_eq_zero_iff_adj [G.LocallyFinite] : G.degree v = 0 ↔ ∀ x, ¬ G.Adj v x := by
  rw [← Nat.cast_inj (R := ℕ∞), natCast_degree_eq, Nat.cast_zero, eDegree_eq_zero_iff_adj]

lemma eDegree_eq_zero_of_notMem (hv : v ∉ V(G)) : G.eDegree v = 0 := by
  simp [eDegree_eq_tsum_mem, show ∀ e, ¬ G.Inc e v from fun e h ↦ hv h.vertex_mem]

lemma degree_eq_zero_of_notMem (hv : v ∉ V(G)) : G.degree v = 0 := by
  simp [degree, eDegree_eq_zero_of_notMem hv]

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

@[simp]
lemma finsum_incFun_eq (he : e ∈ E(G)) : ∑ᶠ v, G.incFun e v = 2 := by
  rw [← G.sum_incFun_eq_two he, Finsupp.sum, finsum_eq_finset_sum_of_support_subset]
  simp

@[simp]
lemma tsum_incFun_eq (he : e ∈ E(G)) : ∑' v, (G.incFun e v : ℕ∞) = 2 := by
  convert (Nat.cast_inj (R := ℕ∞)).2 <| G.sum_incFun_eq_two he
  rw [Finsupp.sum, tsum_eq_sum' (s := (G.incFun e).support) (by simp)]
  simp

lemma IsLoopAt.two_le_eDegree (h : G.IsLoopAt e x) : 2 ≤ G.eDegree x := by
  rw [eDegree]
  convert ENat.le_tsum e
  simp [h.incFun_eq_two]

lemma IsNonloopAt.one_le_eDegree (h : G.IsNonloopAt e x) : 1 ≤ G.eDegree x := by
  rw [eDegree]
  convert ENat.le_tsum e
  simp [h.incFun_eq_one]

lemma Inc.one_le_eDegree (h : G.Inc e x) : 1 ≤ G.eDegree x := by
  obtain h | h := h.isLoopAt_or_isNonloopAt
  · exact le_trans (by simp) h.two_le_eDegree
  exact h.one_le_eDegree

lemma IsLoopAt.two_le_degree [G.LocallyFinite] (h : G.IsLoopAt e x) : 2 ≤ G.degree x := by
  rw [← Nat.cast_le (α := ℕ∞), natCast_degree_eq]
  exact h.two_le_eDegree

lemma Inc.one_le_degree [G.LocallyFinite] (h : G.Inc e x) : 1 ≤ G.degree x := by
  rw [← Nat.cast_le (α := ℕ∞), natCast_degree_eq]
  exact h.one_le_eDegree

lemma IsNonloopAt.one_le_degree [G.LocallyFinite] (h : G.IsNonloopAt e x) : 1 ≤ G.degree x :=
  h.inc.one_le_degree

@[simp]
lemma support_degree_subset (G : Graph α β) : Function.support G.degree ⊆ V(G) :=
  fun _ hx ↦ by_contra fun hxv ↦ hx <| degree_eq_zero_of_notMem hxv

@[simp]
lemma support_eDegree_subset (G : Graph α β) : Function.support G.eDegree ⊆ V(G) :=
  fun _ hx ↦ by_contra fun hxv ↦ hx <| eDegree_eq_zero_of_notMem hxv

theorem handshake_eDegree (G : Graph α β) : ∑' v, G.eDegree v = 2 * E(G).encard := by
  simp_rw [eDegree]
  rw [ENat.tsum_comm, ← ENat.tsum_subtype_const',
    ← tsum_subtype_eq_of_support_subset (s := E(G)) (by simpa using fun _ _ ↦ Inc.edge_mem)]
  simp

theorem handshake_eDegree_subtype (G : Graph α β) :
    ∑' (v : V(G)), G.eDegree v = 2 * E(G).encard := by
  rw [← handshake_eDegree, tsum_subtype_eq_of_support_subset]
  refine fun x (hx : G.eDegree x ≠ 0) ↦ ?_
  obtain ⟨e, hex : G.Inc e x⟩ := by simpa [eDegree] using hx
  exact hex.vertex_mem

lemma handshake_degree_subtype (G : Graph α β) [G.Finite] :
    ∑ᶠ v ∈ V(G), G.degree v = 2 * E(G).ncard := by
  rw [finsum_mem_eq_finite_toFinset_sum _ G.vertexSet_finite, ← Nat.cast_inj (R := ℕ∞),
    Nat.cast_sum, ← tsum_eq_sum]
  · simp [G.edgeSet_finite.cast_ncard_eq, handshake_eDegree]
  simp +contextual [eDegree_eq_zero_of_notMem]

lemma handshake_degree_finset (G : Graph α β) [G.Finite] :
    ∑ v ∈ G.vertexSet_finite.toFinset, G.degree v = 2 * G.edgeSet_finite.toFinset.card := by
  rw [← ncard_eq_toFinset_card _ G.edgeSet_finite,
    ← finsum_mem_eq_finite_toFinset_sum _ G.vertexSet_finite, handshake_degree_subtype]

/-- This should only need `LocallyFinite` -/
lemma handshake (G : Graph α β) [G.Finite] : ∑ᶠ v, G.degree v = 2 * E(G).ncard := by
  rw [← handshake_degree_subtype, ← finsum_mem_univ, finsum_mem_inter_support_eq]
  rw [univ_inter, eq_comm, inter_eq_right]
  exact G.support_degree_subset

lemma eDegree_eq_encard_add_encard (G : Graph α β) (x : α) : G.eDegree x =
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

lemma encard_setOf_inc_le_eDegree (G : Graph α β) (x : α) :
    {e | G.Inc e x}.encard ≤ G.eDegree x := by
  rw [← ENat.tsum_one, eDegree_eq_tsum_mem]
  exact ENat.tsum_le_tsum fun ⟨e, (he : G.Inc e x)⟩ ↦ by simpa using he.one_le_incFun

lemma degree_eq_ncard_add_ncard (G : Graph α β) [G.LocallyFinite] (x : α) :
    G.degree x = 2 * {e | G.IsLoopAt e x}.ncard + {e | G.IsNonloopAt e x}.ncard := by
  rw [← Nat.cast_inj (R := ℕ∞), natCast_degree_eq, eDegree_eq_encard_add_encard]
  simp [G.finite_setOf_isLoopAt.cast_ncard_eq, G.finite_setOf_isNonloopAt.cast_ncard_eq]

lemma eDegree_eq_encard_inc [G.Loopless] : G.eDegree x = {e | G.Inc e x}.encard := by
  simp [eDegree_eq_encard_add_encard, not_isLoopAt, isNonloopAt_iff_inc_not_isLoopAt]

lemma degree_eq_ncard_inc [G.Loopless] : G.degree x = {e | G.Inc e x}.ncard := by
  simp [degree, eDegree_eq_encard_inc, ncard]

lemma eDegree_eq_encard_adj [G.Simple] : G.eDegree x = {y | G.Adj x y}.encard := by
  simp only [encard, coe_setOf, ← ENat.card_congr (G.incAdjEquiv x), eDegree_eq_encard_inc]

lemma degree_eq_ncard_adj [G.Simple] : G.degree x = {y | G.Adj x y}.ncard := by
  rw [degree, eDegree_eq_encard_adj, ncard]

/-! ### Subgraphs -/

lemma incFun_eq_of_le (hle : H ≤ G) (he : e ∈ E(H)) : H.incFun e x = G.incFun e x := by
  by_cases hex : H.Inc e x
  · obtain hl | hnl := hex.isLoopAt_or_isNonloopAt
    · rw [(hl.of_le hle).incFun_eq_two, hl.incFun_eq_two]
    rw [(hnl.of_le hle).incFun_eq_one, hnl.incFun_eq_one]
  rw [incFun_vertex_eq_zero_iff.2 hex, incFun_vertex_eq_zero_iff.2]
  contrapose! hex
  obtain ⟨y, hey⟩ := hex
  exact (hey.of_le_of_mem hle he).inc_left

lemma incFun_mono (hle : H ≤ G) (e : β) (x : α) : H.incFun e x ≤ G.incFun e x := by
  by_cases he : e ∈ E(H)
  · rw [incFun_eq_of_le hle he]
  simp [incFun_eq_zero_of_notMem he]

lemma eDegree_mono (hle : H ≤ G) (x : α) : H.eDegree x ≤ G.eDegree x :=
  ENat.tsum_le_tsum fun e ↦ by simp [incFun_mono hle]

lemma degree_mono [hG : G.LocallyFinite] (hle : H ≤ G) (x : α) : H.degree x ≤ G.degree x := by
  have := hG.mono hle
  rw [← Nat.cast_le (α := ℕ∞), natCast_degree_eq, natCast_degree_eq]
  exact eDegree_mono hle x

lemma IsClosedSubgraph.eDegree_eq (h : H ≤c G) (hx : x ∈ V(H)) : H.eDegree x = G.eDegree x := by
  simp_rw [eDegree_eq_encard_add_encard, ← isLink_self_iff, IsNonloopAt, h.isLink_iff_of_mem hx]

lemma IsClosedSubgraph.degree_eq (h : H ≤c G) (hx : x ∈ V(H)) : H.degree x = G.degree x := by
  rw [Graph.degree, h.eDegree_eq hx, Graph.degree]

end Graph
