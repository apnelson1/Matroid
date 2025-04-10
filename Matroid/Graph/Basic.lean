import Mathlib.Data.Set.Card
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Instances.ENat
import Mathlib.Algebra.BigOperators.WithTop
import Matroid.ForMathlib.Topology.ENat


/-- This lemma should be in mathlib. -/
@[simp]
lemma finsum_mem_const {α M : Type*} (s : Set α) [AddCommMonoid M] (c : M) :
    ∑ᶠ x ∈ s, c = s.ncard • c := by
  obtain h | h := s.finite_or_infinite
  · rw [finsum_mem_eq_finite_toFinset_sum _ h, Set.ncard_eq_toFinset_card _ h]
    simp
  obtain rfl | hne := eq_or_ne c 0
  · simp
  rw [finsum_mem_eq_zero_of_infinite, h.ncard, zero_smul]
  simpa [Function.support_const hne]

/-- A graph where incidence is described by a map from `β` to `α →₀ ℕ`.
`incFun e` is the column of the incidence matrix at `e`, where loops give value `2`. -/
@[ext] structure Graph (α β : Type*) where
  V : Set α
  E : Set β
  incFun : β → α →₀ ℕ
  sum_eq : ∀ ⦃e⦄, e ∈ E → (incFun e).sum (fun _ x ↦ x) = 2
  vertex_support : ∀ ⦃e v⦄, incFun e v ≠ 0 → v ∈ V
  edge_support : ∀ ⦃e v⦄, incFun e v ≠ 0 → e ∈ E

variable {α α' β β' : Type*} {G : Graph α β} {x y v w : α} {e f : β}

namespace Graph

/-- Incidence -/
def Inc (G : Graph α β) (e : β) (x : α) : Prop := G.incFun e x ≠ 0

def IsLoopAt (G : Graph α β) (e : β) (x : α) : Prop := G.incFun e x = 2

def IsNonloopAt (G : Graph α β) (e : β) (x : α) : Prop := G.incFun e x = 1

/-- Is there a more direct way to define this?
`(G.IncFun e).support = {x,y}` is equivalent but requires decidability.
-/
def Inc₂ (G : Graph α β) (e : β) (x y : α) : Prop :=
  (G.IsNonloopAt e x ∧ G.IsNonloopAt e y ∧ x ≠ y) ∨ (G.IsLoopAt e x ∧ x = y)

lemma Inc.one_le_incFun (h : G.Inc e x) : 1 ≤ G.incFun e x := by
  rwa [Inc, ← Nat.one_le_iff_ne_zero] at h

@[simp]
lemma incFun_eq_one : G.incFun e x = 1 ↔ G.IsNonloopAt e x := Iff.rfl

@[simp]
lemma incFun_eq_two : G.incFun e x = 2 ↔ G.IsLoopAt e x := Iff.rfl

@[simp]
lemma Inc.vx_mem (h : G.Inc e x) : x ∈ G.V :=
  G.vertex_support h

@[simp]
lemma Inc.edge_mem (h : G.Inc e x) : e ∈ G.E :=
  G.edge_support h

lemma incFun_of_not_mem_edgeSet (he : e ∉ G.E) : G.incFun e = 0 := by
  simp_rw [DFunLike.ext_iff]
  exact fun x ↦ by_contra fun h' ↦ he <| G.edge_support h'

lemma incFun_of_not_mem_vertexSet (hv : v ∉ G.V) (e) : G.incFun e v = 0 :=
  by_contra fun h' ↦ hv <| G.vertex_support h'

@[simp]
lemma incFun_eq_zero : G.incFun e x = 0 ↔ ¬ G.Inc e x := by
  rw [iff_not_comm]
  rfl

lemma incFun_ne_zero : G.incFun e x ≠ 0 ↔ G.Inc e x := Iff.rfl

lemma incFun_le_two (G : Graph α β) (e) (v) : G.incFun e v ≤ 2 := by
  refine (em (G.Inc e v)).elim (fun h ↦ ?_) (fun h ↦ by simp [incFun_eq_zero.2 h])
  rw [← G.sum_eq h.edge_mem, Finsupp.sum]
  exact Finset.single_le_sum (by simp) (by simpa)

lemma incFun_eq_zero_or_one_or_two (G : Graph α β) (e) (v) :
    G.incFun e v = 0 ∨ G.incFun e v = 1 ∨ G.incFun e v = 2 := by
  have := G.incFun_le_two e v
  omega

lemma incFun_support_card_le (G : Graph α β) (e : β) : (G.incFun e).support.card ≤ 2 := by
  by_cases he : e ∈ G.E
  · simp only [← G.sum_eq he, Finsupp.sum, Finset.card_eq_sum_ones]
    refine Finset.sum_le_sum ?_
    simp only [Finsupp.mem_support_iff]
    exact fun i a ↦ Inc.one_le_incFun a
  simp [incFun_of_not_mem_edgeSet he]

lemma IsLoopAt.inc (h : G.IsLoopAt e v) : G.Inc e v := by
  rw [IsLoopAt] at h
  simp [h, ← incFun_ne_zero]

lemma IsLoopAt.incFun_eq (h : G.IsLoopAt e v) : G.incFun e v = 2 := h

lemma IsNonloopAt.inc (h : G.IsNonloopAt e v) : G.Inc e v := by
  rw [IsNonloopAt] at h
  simp [h, ← incFun_ne_zero]

lemma IsNonloopAt.incFun_eq (h : G.IsNonloopAt e v) : G.incFun e v = 1 := h

lemma inc_iff_isLoopAt_or_isNonloopAt :
    G.Inc e v ↔ G.IsLoopAt e v ∨ G.IsNonloopAt e v := by
  rw [← incFun_ne_zero, IsLoopAt, IsNonloopAt]
  have h := G.incFun_le_two e v
  omega

alias ⟨Inc.isLoopAt_or_isNonloopAt, _⟩ := inc_iff_isLoopAt_or_isNonloopAt

lemma isLoopAt_iff : G.IsLoopAt e v ↔ G.Inc e v ∧ ∀ x, G.Inc e x → x = v := by
  classical
  wlog hev : G.Inc e v
  · exact iff_of_false (fun h ↦ hev h.inc) (by simp [hev])
  rw [IsLoopAt, ← G.sum_eq hev.edge_mem, Finsupp.sum,
    Finset.sum_eq_sum_diff_singleton_add (i := v) (by simpa)]
  aesop

lemma IsLoopAt.eq_of_inc (h : G.IsLoopAt e v) (h_inc : G.Inc e x) : x = v :=
  (isLoopAt_iff.1 h).2 _ h_inc

lemma IsNonloopAt.not_isLoopAt (h : G.IsNonloopAt e v) : ¬ G.IsLoopAt e v := by
  rw [IsNonloopAt] at h
  simp [IsLoopAt, h]

lemma IsLoopAt.not_isNonloopAt (h : G.IsLoopAt e v) : ¬ G.IsNonloopAt e v := by
  rw [IsLoopAt] at h
  simp [IsNonloopAt, h]

lemma IsNonloopAt.exists_inc_ne (h : G.IsNonloopAt e v) : ∃ w, G.Inc e w ∧ w ≠ v := by
  simpa [isLoopAt_iff, and_iff_right h.inc] using h.not_isLoopAt

lemma IsNonloopAt.exists_isNonloopAt_ne (h : G.IsNonloopAt e v) :
    ∃ w, G.IsNonloopAt e w ∧ w ≠ v := by
  obtain ⟨w, hw, hne⟩ := h.exists_inc_ne
  obtain hw | hw := hw.isLoopAt_or_isNonloopAt
  · exact False.elim <| hne.symm <| hw.eq_of_inc h.inc
  exact ⟨w, hw, hne⟩

lemma isNonloopAt_iff : G.IsNonloopAt e v ↔ G.Inc e v ∧ ∃ x, G.Inc e x ∧ x ≠ v :=
  ⟨fun h ↦ ⟨h.inc, h.exists_inc_ne⟩, fun ⟨h, _, hex, hxv⟩ ↦ h.isLoopAt_or_isNonloopAt.elim
    (fun h' ↦ (hxv <| h'.eq_of_inc hex).elim) id⟩

lemma Inc₂.inc_left (h : G.Inc₂ e x y) : G.Inc e x :=
  Or.elim h (fun h ↦ h.1.inc) fun h ↦ h.1.inc

lemma Inc₂.inc_right (h : G.Inc₂ e x y) : G.Inc e y :=
  Or.elim h (fun h ↦ h.2.1.inc) fun h ↦ (h.2.symm ▸ h.1.inc)

lemma Inc₂.edge_mem (h : G.Inc₂ e x y) : e ∈ G.E :=
  h.inc_left.edge_mem

lemma Inc₂.vx_mem_left (h : G.Inc₂ e x y) : x ∈ G.V :=
  h.inc_left.vx_mem

lemma Inc₂.vx_mem_right (h : G.Inc₂ e x y) : y ∈ G.V :=
  h.inc_right.vx_mem

lemma Inc₂.symm (h : G.Inc₂ e x y) : G.Inc₂ e y x :=
  Or.elim h (fun h' ↦ .inl ⟨h'.2.1, h'.1, h'.2.2.symm⟩) fun h' ↦ .inr ⟨h'.2 ▸ h'.1, h'.2.symm⟩

lemma exists_inc_of_mem (he : e ∈ G.E) : ∃ x, G.Inc e x := by
  simp_rw [Inc]
  by_contra! hcon
  simpa [Finsupp.sum, hcon] using G.sum_eq he

lemma exists_inc₂_of_mem (he : e ∈ G.E) : ∃ x y, G.Inc₂ e x y := by
  obtain ⟨x, hx⟩ := exists_inc_of_mem he
  obtain hx | hx := hx.isLoopAt_or_isNonloopAt
  · exact ⟨x, x, .inr ⟨hx, rfl⟩⟩
  obtain ⟨y, hy, hyx⟩ := hx.exists_isNonloopAt_ne
  exact ⟨y, x, .inl ⟨hy, hx, hyx⟩⟩

@[simp]
lemma inc₂_self_iff : G.Inc₂ e x x ↔ G.IsLoopAt e x := by
  refine ⟨fun h ↦ ?_, fun h ↦ .inr ⟨h,rfl⟩⟩
  obtain h | h := h
  · simp at h
  exact h.1

lemma Inc₂.eq_or_eq_of_inc {u : α} (he : G.Inc₂ e x y) (he₁ : G.Inc e u) : u = x ∨ u = y := by
  classical
  by_contra! hcon
  have hcard := incFun_support_card_le G e
  obtain ⟨hex, hey, hxy⟩ | ⟨hex, rfl⟩ := he
  · have hss : {u, x, y} ⊆ (G.incFun e).support := by
      simp [Finset.insert_subset_iff, he₁, hex.inc, hey.inc]
    simpa [Finset.card_eq_three.2 ⟨u, x, y, by aesop⟩] using (Finset.card_le_card hss).trans hcard
  exact hcon.1 <| hex.eq_of_inc he₁

lemma Inc.exists_inc₂ (h : G.Inc e x) : ∃ y, G.Inc₂ e x y := by
  obtain ⟨u, v, huv⟩ := exists_inc₂_of_mem h.edge_mem
  obtain rfl | rfl := huv.eq_or_eq_of_inc h
  · exact ⟨_, huv⟩
  exact ⟨_, huv.symm⟩

lemma inc_iff_inc₂ : G.Inc e x ↔ ∃ y, G.Inc₂ e x y :=
  ⟨Inc.exists_inc₂, fun ⟨_, hy⟩ ↦ hy.inc_left⟩

-- lemma inc₂_iff_inc : G.Inc₂ e x y ↔ G.Inc e x ∧ G.Inc e y ∧ (G.Is)

lemma IsNonloopAt.exists_inc₂_ne (h : G.IsNonloopAt e x) : ∃ y ≠ x, G.Inc₂ e x y := by
  obtain ⟨y, hy⟩ := h.exists_isNonloopAt_ne
  exact ⟨y, hy.2, .inl ⟨h, hy.1, hy.2.symm⟩⟩

lemma Inc₂.isNonloop_at_left_of_ne (h : G.Inc₂ e x y) (hne : x ≠ y) : G.IsNonloopAt e x := by
  obtain ⟨he, -, -⟩ | ⟨he, rfl⟩ := h
  · assumption
  simp at hne

lemma Inc₂.isNonloop_at_right_of_ne (h : G.Inc₂ e x y) (hne : x ≠ y) : G.IsNonloopAt e y := by
  obtain ⟨-, he, -⟩ | ⟨he, rfl⟩ := h
  · assumption
  simp at hne

/-- Two graphs with the same vertices and incidences are the same. -/
lemma ext_inc {G H : Graph α β} (hV : G.V = H.V) (h : ∀ e x, G.Inc e x ↔ H.Inc e x) : G = H := by
  ext e x
  · rw [hV]
  · refine ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩
    · obtain ⟨x, hx⟩ := exists_inc_of_mem h'
      exact ((h _ _).1 hx).edge_mem
    obtain ⟨x, hx⟩ := exists_inc_of_mem h'
    exact ((h _ _).2 hx).edge_mem
  obtain h0 | h1 | h2 := H.incFun_eq_zero_or_one_or_two e x
  · rwa [h0, G.incFun_eq_zero, h, ← H.incFun_eq_zero]
  · simp_rw [h1, G.incFun_eq_one, isNonloopAt_iff, h, ← isNonloopAt_iff]
    rwa [← H.incFun_eq_one]
  simp_rw [h2, G.incFun_eq_two, isLoopAt_iff, h, ← isLoopAt_iff]
  rwa [← H.incFun_eq_two]

/-- Two graphs with the same vertices and 2-incidences are the same. -/
lemma ext_inc₂ {G H : Graph α β} (hV : G.V = H.V) (h : ∀ e x y, G.Inc₂ e x y ↔ H.Inc₂ e x y) :
    G = H :=
  ext_inc hV (by simp [inc_iff_inc₂, h])

/-- The degree of a vertex as a term in `ℕ∞`. -/
noncomputable def eDegree (G : Graph α β) (v : α) : ℕ∞ := ∑' e, G.incFun e v

/-- The degree of a vertex as a term in `ℕ` (with value zero if the degree is infinite). -/
noncomputable def degree (G : Graph α β) (v : α) : ℕ := (G.eDegree v).toNat

lemma eDegree_le_two_mul_card_edgeSet (G : Graph α β) (v : α) : G.eDegree v ≤ 2 * G.E.encard := by
  rw [eDegree, ← ENat.tsum_one, ← tsum_subtype_eq_of_support_subset (s := G.E)]
  · rw [ENat.mul_tsum]
    exact ENat.tsum_le_tsum <| by simp [Pi.le_def, G.incFun_le_two]
  simpa using fun _ ↦ Inc.edge_mem

@[simp] lemma natCast_degree_eq [Finite β] (G : Graph α β) (v : α) :
    (G.degree v : ℕ∞) = G.eDegree v := by
  rw [degree, ENat.coe_toNat_eq_self, ← lt_top_iff_ne_top]
  exact (G.eDegree_le_two_mul_card_edgeSet v).trans_lt <| by
    simp [lt_top_iff_ne_top, ENat.mul_eq_top_iff, G.E.toFinite]

lemma degree_eq_fintype_sum [Fintype β] (G : Graph α β) (v : α) :
    G.degree v = ∑ e, G.incFun e v := by
  rw [degree, eDegree, tsum_eq_sum (s := Finset.univ) (by simp), ← Nat.cast_inj (R := ℕ∞),
    Nat.cast_sum, ENat.coe_toNat]
  exact WithTop.sum_ne_top.2 fun i _ ↦ WithTop.coe_ne_top

lemma degree_eq_finsum [Finite β] (G : Graph α β) (v : α) : G.degree v = ∑ᶠ e, G.incFun e v := by
  have := Fintype.ofFinite β
  rw [degree_eq_fintype_sum, finsum_eq_sum_of_fintype]

@[simp]
lemma finsum_incFun_eq (he : e ∈ G.E) : ∑ᶠ v, G.incFun e v = 2 := by
  rw [← G.sum_eq he, Finsupp.sum, finsum_eq_finset_sum_of_support_subset]
  simp

@[simp]
lemma tsum_incFun_eq (he : e ∈ G.E) : ∑' v, (G.incFun e v : ℕ∞) = 2 := by
  convert (Nat.cast_inj (R := ℕ∞)).2 <| G.sum_eq he
  rw [Finsupp.sum, tsum_eq_sum' (s := (G.incFun e).support) (by simp)]
  simp

theorem handshake_eDegree (G : Graph α β) : ∑' v, G.eDegree v = 2 * G.E.encard := by
  simp_rw [eDegree]
  rw [ENat.tsum_comm, ← ENat.tsum_subtype_const',
    ← tsum_subtype_eq_of_support_subset (s := G.E) (by simpa using fun _ _ ↦ Inc.edge_mem)]
  simp

lemma handshake [Finite α] [Finite β] (G : Graph α β) : ∑ᶠ v, G.degree v = 2 * G.E.ncard := by
  have := Fintype.ofFinite α
  rw [← Nat.cast_inj (R := ℕ∞), finsum_eq_sum_of_fintype, Nat.cast_sum]
  simp [natCast_degree_eq, ← tsum_eq_sum (s := Finset.univ) (by simp), handshake_eDegree,
    G.E.toFinite.cast_ncard_eq]
