import Matroid.Graph.Basic
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Set.Card
import Matroid.ForMathlib.Card

open Set

variable {α β : Type*} {x y z u v w : α} {e f : β} {G H : Graph α β}

namespace Graph

/-- The set of ends of an edge `e`. -/
def endSet (G : Graph α β) (e : β) : Set α := {x | G.Inc e x}

@[simp]
lemma mem_endSet_iff : x ∈ G.endSet e ↔ G.Inc e x := Iff.rfl

lemma Inc₂.endSet_eq (h : G.Inc₂ e x y) : G.endSet e = {x,y} := by
  ext a
  simp only [mem_endSet_iff, mem_insert_iff, mem_singleton_iff]
  refine ⟨fun h' ↦ h'.eq_or_eq_of_inc₂ h, ?_⟩
  rintro (rfl | rfl)
  · exact h.inc_left
  exact h.inc_right

lemma IsLoopAt.endSet_eq (h : G.IsLoopAt e x) : G.endSet e = {x} := by
  rw [Inc₂.endSet_eq h, pair_eq_singleton]

lemma endSet_eq_of_not_mem_edgeSet (he : e ∉ E(G)) : G.endSet e = ∅ := by
  simp only [endSet, eq_empty_iff_forall_not_mem, mem_setOf_eq]
  exact fun x hx ↦ he hx.edge_mem

lemma endSet_encard_le (G : Graph α β) (e : β) : (G.endSet e).encard ≤ 2 := by
  by_cases heE : e ∈ E(G)
  · obtain ⟨x, y, h⟩ := exists_inc₂_of_mem_edgeSet heE
    rw [h.endSet_eq]
    exact encard_pair_le x y
  simp [endSet_eq_of_not_mem_edgeSet heE]

@[simp]
lemma subsingleton_setOf_inc₂ (G : Graph α β) (e : β) (x : α) :
    {y | G.Inc₂ e x y}.Subsingleton := by
  simp only [Set.Subsingleton, mem_setOf_eq]
  exact fun y hy z hz ↦ hy.eq_of_inc₂ hz

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
  toFun x := {y | G.Inc₂ e x y}.ncard + ({y | G.Inc₂ e x y} ∩ {x}).ncard
  mem_support_toFun x := by
    obtain ⟨y, hy⟩ | hx := em <| G.Inc e x
    · simp [hy.inc₂_iff_eq]
    simp [hx, inc₂_iff_inc]

lemma Inc₂.incFun_support_eq [DecidableEq α] (h : G.Inc₂ e x y) :
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
  simp [DFunLike.ext_iff, incFun, not_inc₂_of_not_mem_edgeSet he]

lemma incFun_le_two (G : Graph α β) (e : β) (x : α) : G.incFun e x ≤ 2 := by
  obtain ⟨y, hy⟩ | hx := em <| G.Inc e x
  · suffices 1 + _ ≤ 2 by simpa [incFun, hy.inc₂_iff_eq]
    have := ncard_singleton_inter y {x}
    omega
  simp [incFun, inc₂_iff_inc, hx]

lemma IsNonloopAt.eIncFun_eq_one (h : G.IsNonloopAt e x) : G.incFun e x = 1 := by
  obtain ⟨y, hne, hxy⟩ := h.exists_inc₂_ne
  simp [incFun, hxy.inc₂_iff_eq, (show Disjoint {y} {x} by simpa).inter_eq]

@[simp]
lemma incFun_eq_one_iff : G.incFun e x = 1 ↔ G.IsNonloopAt e x := by
  obtain (⟨y, hxy⟩ | hex) := em <| G.Inc e x
  · simp [incFun, hxy.inc₂_iff_eq, isNonloopAt_iff, toFinite ({y} ∩ {x}), eq_comm (a := x)]
  simp [incFun, mt Inc₂.inc_left hex, mt IsNonloopAt.inc hex]

lemma IsNonloopAt.incFun_eq_one (h : G.IsNonloopAt e x) : G.incFun e x = 1 :=
  incFun_eq_one_iff.2 h

@[simp]
lemma incFun_eq_two_iff : G.incFun e x = 2 ↔ G.IsLoopAt e x := by
  obtain (⟨y, hxy⟩ | hex) := em <| G.Inc e x
  · suffices 1 + _ = 2 ↔ x = y by simpa [incFun, hxy.inc₂_iff_eq, ← inc₂_self_iff]
    obtain rfl | hne := eq_or_ne y x
    · simp
    simp [(show Disjoint {y} {x} by simpa).inter_eq, hne.symm]
  simp [incFun, mt Inc₂.inc_left hex, hex, mt IsLoopAt.inc hex]

lemma IsLoopAt.incFun_eq_two (h : G.IsLoopAt e x) : G.incFun e x = 2 :=
  incFun_eq_two_iff.2 h

@[simp]
lemma incFun_eq_zero_iff : G.incFun e = 0 ↔ e ∉ E(G) := by
  refine ⟨fun h he ↦ ?_, incFun_eq_zero_of_not_mem⟩
  obtain ⟨x, y, hxy⟩ := exists_inc₂_of_mem_edgeSet he
  obtain hx | hx := hxy.inc_left.isLoopAt_or_isNonloopAt
  · have := h ▸ hx.incFun_eq_two
    simp at this
  have := h ▸ hx.incFun_eq_one
  simp at this

lemma sum_incFun_eq_two (he : e ∈ E(G)) : (G.incFun e).sum (fun _ x ↦ x) = 2 := by
  classical
  obtain ⟨x, y, hxy⟩ := exists_inc₂_of_mem_edgeSet he
  obtain rfl | hne := eq_or_ne x y
  · simp [Finsupp.sum, hxy.incFun_support_eq, hxy.inc₂_iff_eq, show G.IsLoopAt e x from hxy]
  simp [Finsupp.sum, hxy.incFun_support_eq, Finset.sum_pair hne,
    (hxy.isNonloopAt_of_ne hne).incFun_eq_one, (hxy.isNonloopAt_right_of_ne hne).incFun_eq_one]


end Graph
