import Mathlib.Combinatorics.Graph.Basic
import Matroid.Graph.Basic
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
  simp [lt_top_iff_ne_top, Ne, ENat.mul_eq_top_iff, (G.finite_setOf_inc v)]

@[simp]
lemma eDegree_lt_top [G.LocallyFinite] : G.eDegree x < ⊤ := by
  rw [← natCast_degree_eq]
  exact ENat.coe_lt_top (G.degree x)

@[simp]
lemma eDegree_ne_top [G.LocallyFinite] : G.eDegree x ≠ ⊤ :=
  eDegree_lt_top.ne

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

/-- This should only need `LocallyFinite` -/
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

/-! ### Degree-zero vertices -/

lemma eDegree_eq_zero_iff_inc : G.eDegree v = 0 ↔ ∀ e, ¬ G.Inc e v := by
  simp [eDegree]

lemma eDegree_eq_zero_iff_adj : G.eDegree v = 0 ↔ ∀ x, ¬ G.Adj v x := by
  simp only [eDegree, ENat.tsum_eq_zero, Nat.cast_eq_zero, incFun_vertex_eq_zero_iff]
  exact ⟨fun h x ⟨e, hvx⟩ ↦ h e hvx.inc_left, fun h e ⟨y, hev⟩ ↦ h y hev.adj⟩

lemma degree_eq_zero_iff_inc [G.LocallyFinite] : G.degree v = 0 ↔ ∀ e, ¬ G.Inc e v := by
  rw [← Nat.cast_inj (R := ℕ∞), natCast_degree_eq, Nat.cast_zero, eDegree_eq_zero_iff_inc]

lemma degree_eq_zero_iff_adj [G.LocallyFinite] : G.degree v = 0 ↔ ∀ x, ¬ G.Adj v x := by
  rw [← Nat.cast_inj (R := ℕ∞), natCast_degree_eq, Nat.cast_zero, eDegree_eq_zero_iff_adj]

/-- `G.MinDegreePos` means that `G` has no degree-zero vertices. -/
def MinDegreePos (G : Graph α β) : Prop := ∀ ⦃x⦄, x ∈ V(G) → ∃ e, G.Inc e x

lemma MinDegreePos.one_le_eDegree (hG : G.MinDegreePos) (hx : x ∈ V(G)) : 1 ≤ G.eDegree x := by
  rw [ENat.one_le_iff_ne_zero]
  simp only [ne_eq, eDegree_eq_zero_iff_inc, not_forall, not_not]
  exact hG hx

lemma MinDegreePos.one_le_degree [G.LocallyFinite] (hG : G.MinDegreePos) (hx : x ∈ V(G)) :
    1 ≤ G.degree x := by
  rw [← Nat.cast_le (α := ℕ∞), natCast_degree_eq]
  exact hG.one_le_eDegree hx

lemma MinDegreePos.finite_of_edgeSet_finite (hG : G.MinDegreePos) (hE : E(G).Finite) :
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

lemma MinDegreePos.edgeSet_finite_iff (hG : G.MinDegreePos) : E(G).Finite ↔ G.Finite :=
  ⟨hG.finite_of_edgeSet_finite, fun h ↦ h.edgeSet_finite⟩

/-! ### Leaves -/

/-- `G.IsPendant e x` means that `e` is a nonloop edge at `x`, and is also the only edge at `x`. -/
@[mk_iff]
structure IsPendant (G : Graph α β) (e : β) (x : α) : Prop where
  isNonloopAt : G.IsNonloopAt e x
  edge_unique : ∀ ⦃f⦄, G.Inc f x → f = e

lemma IsPendant.not_isLoopAt (h : G.IsPendant e x) (f : β) : ¬ G.IsLoopAt f x := by
  refine fun h' ↦ h.isNonloopAt.not_isLoopAt x ?_
  rwa [← h.edge_unique h'.inc]

lemma IsPendant.eDegree (h : G.IsPendant e x) : G.eDegree x = 1 := by
  have hrw : {e | G.IsNonloopAt e x} = {e} := by
    simp +contextual only [Set.ext_iff, mem_setOf_eq, mem_singleton_iff, iff_def, h.isNonloopAt,
      implies_true, and_true]
    exact fun f hf ↦ h.edge_unique hf.inc
  simp [eDegree_eq_card_add_card, h.not_isLoopAt, hrw]

lemma Inc.isPendant_of_eDegree_le_one (h : G.Inc e x) (hdeg : G.eDegree x ≤ 1) :
    G.IsPendant e x := by
  replace hdeg := hdeg.antisymm h.one_le_eDegree
  have hnl : ∀ f, ¬ G.IsLoopAt f x := fun f hf ↦ by simpa using hf.two_le_eDegree.trans_eq hdeg
  refine ⟨h.isLoopAt_or_isNonloopAt.elim (fun h ↦ (hnl _ h).elim) id, fun f hf ↦ ?_⟩
  rw [inc_iff_isLoopAt_or_isNonloopAt, or_iff_right (hnl _)] at h hf
  rw [eDegree_eq_card_add_card] at hdeg
  have hss := encard_le_one_iff_subsingleton.1 <| le_add_self.trans hdeg.le
  exact hss hf h

lemma Inc.isPendant_of_degree_eq_one (h : G.Inc e x) (hdeg : G.degree x = 1) : G.IsPendant e x := by
  refine h.isPendant_of_eDegree_le_one ?_
  simp only [degree, ENat.toNat_eq_iff_eq_coe, Nat.cast_one] at hdeg
  exact hdeg.le

lemma Inc.isPendant_of_degree_le_one [G.LocallyFinite] (h : G.Inc e x) (hdeg : G.degree x ≤ 1) :
    G.IsPendant e x :=
  h.isPendant_of_eDegree_le_one <| by rwa [← natCast_degree_eq, ← Nat.cast_one, Nat.cast_le]

lemma IsPendant.edgeSet_delete_vertex_eq (h : G.IsPendant e x) : E(G - {x}) = E(G) \ {e} := by
  ext f
  simp only [vertexDelete_edgeSet, mem_singleton_iff, mem_setOf_eq, mem_diff]
  refine ⟨fun ⟨z, y, h'⟩ ↦ ⟨h'.1.edge_mem, ?_⟩, fun ⟨hfE, hfe⟩ ↦ ?_⟩
  · rintro rfl
    cases h.isNonloopAt.inc.eq_or_eq_of_isLink h'.1 <;> simp_all
  obtain ⟨y, hyx, hy⟩ := h.isNonloopAt
  obtain ⟨z, w, hzw⟩ := exists_isLink_of_mem_edgeSet hfE
  refine ⟨z, w, hzw, fun h_eq ↦ hfe ?_, fun h_eq ↦ hfe ?_⟩
  · exact h.edge_unique ((h_eq ▸ hzw).inc_left)
  exact h.edge_unique (h_eq ▸ hzw.inc_right)

lemma IsPendant.eq_addEdge (h : G.IsPendant e x) :
    ∃ y ∈ V(G), G.IsLink e x y ∧ y ≠ x ∧ e ∉ E(G-{x}) ∧ G = (G - {x}).addEdge e x y := by
  obtain ⟨y, hne, hexy⟩ := h.isNonloopAt
  refine ⟨y, hexy.right_mem, hexy, hne, ?_, ext_of_le_le le_rfl ?_ ?_ ?_⟩
  · rw [h.edgeSet_delete_vertex_eq]
    simp
  · exact Graph.union_le (by simpa) (by simp)
  · rw [addEdge_vertexSet, vertexDelete_vertexSet, ← union_singleton, union_assoc]
    simp [insert_eq_of_mem hexy.right_mem, insert_eq_of_mem hexy.left_mem]
  rw [addEdge_edgeSet, h.edgeSet_delete_vertex_eq, insert_diff_singleton,
    insert_eq_of_mem hexy.edge_mem]

lemma IsPendant.exists_eq_addEdge (h : G.IsPendant e x) :
    ∃ (y : α) (H : Graph α β), x ∉ V(H) ∧ y ∈ V(H) ∧ e ∉ E(H) ∧ G = H.addEdge e x y := by
  obtain ⟨y, hyV, -, hyx, -, h_eq⟩ := h.eq_addEdge
  refine ⟨y, _, by simp, by simp [hyV, hyx], ?_, h_eq⟩
  rw [h.edgeSet_delete_vertex_eq]
  simp

/-- A leaf is a degree-one vertex. -/
def IsLeaf (G : Graph α β) (v : α) : Prop := ∃ e, G.IsPendant e v

lemma IsPendant.isLeaf (h : G.IsPendant e x) : G.IsLeaf x :=
  ⟨e, h⟩

@[simp]
lemma eDegree_eq_one_iff : G.eDegree v = 1 ↔ G.IsLeaf v := by
  refine ⟨fun h ↦ ?_, fun ⟨e, h⟩ ↦ h.eDegree⟩
  obtain ⟨e, he⟩ | hn := em <| ∃ e, G.Inc e v
  · exact ⟨e, he.isPendant_of_eDegree_le_one h.le⟩
  simp [← eDegree_eq_zero_iff_inc, h] at hn

@[simp]
lemma degree_eq_one_iff : G.degree v = 1 ↔ G.IsLeaf v := by
  simp [← eDegree_eq_one_iff, degree]

lemma IsLeaf.mem (h : G.IsLeaf v) : v ∈ V(G) :=
  h.choose_spec.isNonloopAt.vertex_mem

lemma IsLeaf.vertexSet_nontrivial (h : G.IsLeaf v) : V(G).Nontrivial := by
  obtain ⟨e, he⟩ := h
  exact he.isNonloopAt.vertexSet_nontrivial

/-- Maybe not needed with `IsPendant`. -/
lemma IsLeaf.exists_unique_inc (h : G.IsLeaf x) : ∃! e, G.Inc e x :=
  ⟨h.choose, h.choose_spec.isNonloopAt.inc, h.choose_spec.edge_unique⟩

lemma IsLeaf.exists_unique_adj (h : G.IsLeaf x) : ∃! y, G.Adj x y := by
  obtain ⟨e, ⟨y, he⟩, hunique⟩ := h.exists_unique_inc
  refine ⟨y, he.adj, fun z ⟨f, hz⟩ ↦ ?_⟩
  rw [hunique f hz.inc_left] at hz
  exact hz.right_unique he

lemma IsLeaf.eq_of_adj_adj (h : G.IsLeaf x) (hu : G.Adj x u) (hv : G.Adj x v) :
    u = v := by
  obtain ⟨y, hy, hun⟩ := h.exists_unique_adj
  rw [hun u hu, hun v hv]

lemma IsLeaf.eq_of_inc_inc (h : G.IsLeaf x) (he : G.Inc e x) (hf : G.Inc f x) :
    e = f := by
  obtain ⟨g, hg, hun⟩ := h.exists_unique_inc
  rw [hun e he, hun f hf]

lemma IsLeaf.not_adj_self (h : G.IsLeaf x) : ¬ G.Adj x x := by
  rintro ⟨e, he⟩
  rw [← eDegree_eq_one_iff, eDegree] at h
  simpa [(isLink_self_iff.1 he).incFun_eq_two] using (ENat.le_tsum (a := e)).trans h.le

lemma IsLeaf.ne_of_adj (h : G.IsLeaf x) (hxy : G.Adj x y) : x ≠ y :=
  fun h' ↦ h.not_adj_self <| h' ▸ hxy

lemma IsLeaf.not_isLoopAt (h : G.IsLeaf x) (e) : ¬ G.IsLoopAt e x :=
  fun h' ↦ h.not_adj_self h'.adj

/-- A leaf edge is an edge incident with a degree-one vertex. -/
def IsLeafEdge (G : Graph α β) (e : β) := ∃ x, G.IsPendant e x

/-! ### Constructions -/

@[simp]
lemma noEdge_eDegree (V : Set α) (β : Type*) (x : α) : (Graph.noEdge V β).eDegree x = 0 := by
  simp [eDegree]

lemma singleEdge_eDegree_left (hxy : x ≠ y) (e : β) :
    (Graph.singleEdge x y e).eDegree x = 1 := by
  rw [eDegree_eq_card_add_card, encard_eq_zero.2, ← encard_singleton e, mul_zero, zero_add]
  · convert rfl
    suffices ∃ z, ¬z = x ∧ (z = y ∨ x = y ∧ z = x) by
      simpa +contextual [iff_def, IsNonloopAt, Set.ext_iff]
    exact ⟨y, hxy.symm, by simp [hxy]⟩
  simp_rw [IsLoopAt, singleEdge_isLink_iff]
  simp [hxy]

lemma singleEdge_eDegree_right (hxy : x ≠ y) (e : β) :
    (Graph.singleEdge x y e).eDegree y = 1 := by
  rw [singleEdge_comm, singleEdge_eDegree_left hxy.symm]

lemma singleEdge_eDegree_of_ne (e : β) (hx : z ≠ x) (hy : z ≠ y) :
    (Graph.singleEdge x y e).eDegree z = 0 := by
  simpa [eDegree_eq_zero_iff_adj, hx]

lemma singleEdge_degree_left (hxy : x ≠ y) (e : β) :
    (Graph.singleEdge x y e).degree x = 1 := by
  simp [degree, singleEdge_eDegree_left hxy]

lemma singleEdge_degree_right (hxy : x ≠ y) (e : β) :
    (Graph.singleEdge x y e).degree y = 1 := by
  simp [degree, singleEdge_eDegree_right hxy]

lemma singleEdge_degree_of_ne (e : β) (hx : z ≠ x) (hy : z ≠ y) :
    (Graph.singleEdge x y e).eDegree z = 0 := by
  simp [degree, singleEdge_eDegree_of_ne _ hx hy]

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
  simp [incFun_eq_zero_of_not_mem he]

lemma eDegree_mono (hle : H ≤ G) (x : α) : H.eDegree x ≤ G.eDegree x :=
  ENat.tsum_le_tsum fun e ↦ by simp [incFun_mono hle]

lemma degree_mono [hG : G.LocallyFinite] (hle : H ≤ G) (x : α) : H.degree x ≤ G.degree x := by
  have := hG.mono hle
  rw [← Nat.cast_le (α := ℕ∞), natCast_degree_eq, natCast_degree_eq]
  exact eDegree_mono hle x

lemma union_incFun_eq (hdj : Disjoint E(G) E(H)) : (G ∪ H).incFun = G.incFun + H.incFun := by
  ext e x
  rw [Pi.add_apply, Finsupp.add_apply]
  by_cases heG : e ∈ E(G)
  · rw [incFun_eq_of_le (Graph.left_le_union G H) heG, Nat.left_eq_add, incFun_vertex_eq_zero_iff]
    exact fun h ↦ hdj.not_mem_of_mem_right h.edge_mem heG
  rw [incFun_eq_zero_of_not_mem heG, Finsupp.coe_zero, Pi.zero_apply, zero_add]
  by_cases heH : e ∈ E(H)
  · rw [incFun_eq_of_le (Compatible.of_disjoint_edgeSet hdj).right_le_union heH]
  rw [incFun_eq_zero_of_not_mem (by simp [heH, heG]), incFun_eq_zero_of_not_mem heH]

lemma union_eDegree_eq (hdj : Disjoint E(G) E(H)) (x : α) :
    (G ∪ H).eDegree x = G.eDegree x + H.eDegree x := by
  simp [eDegree, union_incFun_eq hdj, ENat.tsum_add]

lemma eDegree_addEdge_left {a b : α} (he : e ∉ E(G)) (hab : a ≠ b) :
    (G.addEdge e a b).eDegree a = G.eDegree a + 1 := by
  rw [Graph.addEdge, union_eDegree_eq (by simpa), add_comm, singleEdge_eDegree_left hab]

lemma eDegree_addEdge_right {a b : α} (he : e ∉ E(G)) (hab : a ≠ b) :
    (G.addEdge e a b).eDegree b = G.eDegree b + 1 := by
  rw [Graph.addEdge, union_eDegree_eq (by simpa), add_comm, singleEdge_eDegree_right hab]

lemma eDegree_addEdge_of_ne {a b : α} (he : e ∉ E(G)) (hxa : x ≠ a) (hxb : x ≠ b) :
    (G.addEdge e a b).eDegree x = G.eDegree x := by
  rw [Graph.addEdge, union_eDegree_eq (by simpa), singleEdge_eDegree_of_ne _ hxa hxb, zero_add]

lemma union_degree_eq [G.LocallyFinite] [H.LocallyFinite] (hdj : Disjoint E(G) E(H)) (x : α) :
    (G ∪ H).degree x = G.degree x + H.degree x := by
  simp only [degree, union_eDegree_eq hdj]
  rw [ENat.toNat_add (by simp) (by simp)]

lemma degree_addEdge_left [G.LocallyFinite] {a b : α} (he : e ∉ E(G)) (hab : a ≠ b) :
    (G.addEdge e a b).degree a = G.degree a + 1 := by
  rw [Graph.addEdge, union_degree_eq (by simpa), add_comm, singleEdge_degree_left hab]

lemma degree_addEdge_right [G.LocallyFinite] {a b : α} (he : e ∉ E(G)) (hab : a ≠ b) :
    (G.addEdge e a b).degree b = G.degree b + 1 := by
  rw [Graph.addEdge, singleEdge_comm, ← Graph.addEdge, degree_addEdge_left he hab.symm]

lemma degree_addEdge_of_ne {a b : α} (he : e ∉ E(G)) (hxa : x ≠ a) (hxb : x ≠ b) :
    (G.addEdge e a b).degree x = G.degree x := by
  rw [degree, eDegree_addEdge_of_ne he hxa hxb, degree]

end Graph
