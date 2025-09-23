import Matroid.Graph.Basic

variable {α β : Type*} {x y z u v w a b : Set α} {e f : β} {G H : Graph α β} {F F₁ F₂ : Set β}
  {X Y : Set (Set α)} {P Q : Partition (Set α)}

open Set Function Relation Partition

open scoped Sym2

namespace Graph

/-! # Repartition -/
/-- Given a graph `G` and a coarser partition `P'` of its vertex set, the repartition of `G` by `P'`
is the graph obtained by identifying the vertices of `G` according to `P'`. -/
@[simps]
def repartition (G : Graph α β) (P' : Partition (Set α)) (h : P(G) ≤ P') : Graph α β where
  vertexPartition := P'
  IsLink e x y := ∃ u v, G.IsLink e u v ∧ P'.foo u = x ∧ P'.foo v = y
  isLink_symm e he x y hxy := by
    obtain ⟨u, v, hu, rfl, rfl⟩ := hxy
    use v, u, hu.symm
  edgeSet := E(G)
  edge_mem_iff_exists_isLink e := by
    rw [edge_mem_iff_exists_isLink]
    refine ⟨fun ⟨x, y, hxy⟩ ↦ ?_, fun ⟨a, b, x, y, hxy, A, B⟩ ↦ ?_⟩
    · use P'.foo x, P'.foo y, x, y
    subst A B
    use x, y
  eq_or_eq_of_isLink_of_isLink e a b c d := by
    rintro ⟨u, v, huv, rfl, rfl⟩ ⟨w, x, hwx, rfl, rfl⟩
    apply (G.eq_or_eq_of_isLink_of_isLink huv hwx).imp <;> rintro rfl <;> rfl
  left_mem_of_isLink e x y hxy := by
    obtain ⟨u, v, huv, rfl, rfl⟩ := hxy
    exact mem_parts.mpr <| foo_mem_of_le h (huv.left_mem')

@[simp]
lemma repartition_idem (hP : P(G) ≤ P) (hQ : P ≤ Q) :
    (G.repartition P hP).repartition Q hQ = G.repartition Q (hP.trans hQ) := by
  refine vertexPartition_ext (by simp) fun e x y ↦ ?_
  have h : ∀ y ∈ P(G), Q.foo y = Q.foo (P.foo y) := by
    refine fun y hy ↦ (foo_foo_eq_foo hQ ?_).symm
    exact subset_trans (subset_of_mem hy) <| supp_le_of_le hP
  simp_rw [repartition_isLink]
  constructor
  · rintro ⟨u, v, ⟨x, y, hxy, rfl, rfl⟩, rfl, rfl⟩
    use x, y, hxy, h _ hxy.left_mem', h _ hxy.right_mem'
  · rintro ⟨x, y, hxy, rfl, rfl⟩
    use P.foo x, P.foo y, (by use x, y, hxy), (h _ hxy.left_mem').symm,
      (h _ hxy.right_mem').symm

@[simp]
lemma repartition_inc (h : P(G) ≤ P) :
    (G.repartition P h).Inc e x ↔ ∃ u, G.Inc e u ∧ P.foo u = x := by
  simp_rw [Inc, repartition_isLink]
  constructor
  · rintro ⟨u, v, w, hvw, rfl, rfl⟩
    use v, (by use w)
  · rintro ⟨u, ⟨v, huv⟩, rfl⟩
    use P.foo v, u, v
