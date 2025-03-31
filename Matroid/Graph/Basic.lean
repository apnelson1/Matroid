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

lemma IsLoopAt.inc (h : G.IsLoopAt e v) : G.Inc e v := by
  rw [IsLoopAt] at h
  simp [h, ← incFun_ne_zero]

lemma IsNonloopAt.inc (h : G.IsNonloopAt e v) : G.Inc e v := by
  rw [IsNonloopAt] at h
  simp [h, ← incFun_ne_zero]

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

lemma isNonloopAt_iff : G.IsNonloopAt e v ↔ G.Inc e v ∧ ∃ x, G.Inc e x ∧ x ≠ v :=
  ⟨fun h ↦ ⟨h.inc, h.exists_inc_ne⟩, fun ⟨h, _, hex, hxv⟩ ↦ h.isLoopAt_or_isNonloopAt.elim
    (fun h' ↦ (hxv <| h'.eq_of_inc hex).elim) id⟩

/-- Two graphs with the same incidences are the same. -/
lemma ext_inc {G G' : Graph α β} (hV : G.V = G'.V) (hE : G.E = G'.E)
    (h : ∀ e x, G.Inc e x ↔ G'.Inc e x) : G = G' := by
  ext e x
  · rw [hV]
  · rw [hE]
  obtain h0 | h1 | h2 := G'.incFun_eq_zero_or_one_or_two e x
  · rwa [h0, G.incFun_eq_zero, h, ← G'.incFun_eq_zero]
  · simp_rw [h1, G.incFun_eq_one, isNonloopAt_iff, h, ← isNonloopAt_iff]
    rwa [← G'.incFun_eq_one]
  simp_rw [h2, G.incFun_eq_two, isLoopAt_iff, h, ← isLoopAt_iff]
  rwa [← G'.incFun_eq_two]

/-- Restrict a graph to a subset `R` of the edge set. -/
noncomputable def edgeRestrict (G : Graph α β) (R : Set β) : Graph α β where
  V := G.V
  E := G.E ∩ R
  incFun e :=
    have := Classical.dec (e ∈ R)
    if e ∈ R then G.incFun e else 0
  sum_eq e he := by simp [he.2, G.sum_eq he.1]
  vertex_support e v h := G.vertex_support (e := e) <| by aesop
  edge_support e v h := ⟨G.edge_support (v := v) (by aesop), by aesop⟩

/-- Delete a subset `D` of the edges. -/
noncomputable def edgeDel (G : Graph α β) (D : Set β) := G.edgeRestrict (G.E \ D)

lemma vxMap_aux (G : Graph α β) {f : α → α'} {x : α'} :
    (G.incFun e).mapDomain f x ≠ 0 ↔ ∃ v, f v = x ∧ G.Inc e v := by
  classical
  simp +contextual [← incFun_eq_zero, Finsupp.mapDomain, Finsupp.sum,
    Finsupp.single_apply, and_comm, ← incFun_ne_zero]

/-- Transport a graph to a new vertex type by mapping along a function.
Edges between identified vertices become loops. -/
noncomputable def vxMap {α' : Type*} (G : Graph α β) (f : α → α') : Graph α' β where
  V := f '' G.V
  E := G.E
  incFun e := (G.incFun e).mapDomain f
  sum_eq e he := by rwa [Finsupp.sum_mapDomain_index (by simp) (by simp), G.sum_eq]
  vertex_support e v := by
    simp only [ne_eq, vxMap_aux, Set.mem_image, forall_exists_index, and_imp]
    exact fun x hxv h ↦ ⟨x, h.vx_mem, hxv⟩
  edge_support e v := by
    simp only [ne_eq, vxMap_aux, forall_exists_index, and_imp]
    exact fun _ _ ↦ Inc.edge_mem

/-- `vxMap` has the expected incidence predicate. -/
@[simp]
lemma vxMap_inc_iff {α' : Type*} (G : Graph α β) (f : α → α') (x : α') (e : β) :
    (G.vxMap f).Inc e x ↔ ∃ v, f v = x ∧ G.Inc e v := by
  rw [← incFun_ne_zero, ← vxMap_aux]
  rfl

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
