import Matroid.Graph.Basic

variable {α β ι ι' : Type*} {x y z u v w : α} {e f : β} {G G₁ G₂ H H₁ H₂ : Graph α β}
  {F F₁ F₂ : Set β} {X Y : Set α} {s t : Set (Graph α β)} {P Q : Partition (Set α)}

open Set Function Partition

namespace Graph

section Repartition

/-- Repartition changes the labels of the graph. This can be used for adding new labels and
    vertices to a given graph but also identifying vertices. -/
@[simps!]
def Repartition (G : Graph α β) (P : Partition (Set α)) : Graph α β :=
  mk' P G.IsLink

@[simp]
lemma repartition_self (G : Graph α β) : G.Repartition G.Dup = G :=
  Graph.ext (by simp) fun e x y => by
    simp [G.dup_or_dup_of_isLink_of_isLink, Relation.domp_eq]

lemma repartition_isLink_of_dup_le (hP : G.Dup ≤ P) :
    (G.Repartition P).IsLink e = Relation.Domp P (G.IsLink e) := by
  ext x y
  simp [btwVx_mono_left hP (G.dup_or_dup_of_isLink_of_isLink (e := e))]

@[simp]
lemma repartition_inc_of_dup_le (hP : G.Dup ≤ P) :
    (G.Repartition P).Inc = Relation.Comp G.Inc P := by
  ext e x
  unfold Inc
  simp only [repartition_isLink_of_dup_le hP]
  exact ⟨fun ⟨y, a, hPxa, b, hlba, hPby⟩ ↦ ⟨a, ⟨b, hlba.symm⟩, hPxa.symm⟩,
    fun ⟨w, ⟨y, hlwy⟩, hPwx⟩ ↦ ⟨y, w, hPwx.symm, y, hlwy.symm, rel_le_of_le hP _ _ hlwy.right_refl⟩⟩

@[simp]
lemma repartition_adj_of_dup_le (hP : G.Dup ≤ P) :
    (G.Repartition P).Adj = Relation.Domp P G.Adj := by
  ext x y
  unfold Adj
  simp only [repartition_isLink_of_dup_le hP]
  exact ⟨fun ⟨e, a, hxa, b, hlba, hby⟩ ↦ ⟨a, hxa, b, ⟨e, hlba⟩, hby⟩,
    fun ⟨a, hxa, b, ⟨e, hlba⟩, hby⟩ ↦ ⟨e, a, hxa, b, hlba, hby⟩⟩

lemma repartition_le_repartition_of_subset {P Q : Partition (Set α)} (hPQ : P ⊆ Q) :
    G.Repartition P ≤ G.Repartition Q where
  dup_subset := by simp [hPQ]
  isLink_of_isLink e x y := by
    simp only [Repartition_isLink, and_imp]
    exact fun hbtw hPxy ↦ ⟨btwVx_mono_left (le_of_subset hPQ) hbtw,
      Relation.domp_mono (rel_le_of_le (le_of_subset hPQ)) le_rfl x y hPxy⟩

lemma repartition_le_repartition_iff {P Q : Partition (Set α)} :
    G.Repartition P ≤ G.Repartition Q ↔ P ⊆ Q :=
  ⟨fun h ↦ h.1, repartition_le_repartition_of_subset⟩

end Repartition

section LabelDelete

/-- The graph obtained from `G` by deleting a set of vertices. -/
@[simps]
protected def labelDelete (G : Graph α β) (X : Set α) : Graph α β where
  Dup := G.Dup.induce Xᶜ
  vertexSet := V(G) \ X
  vertexSet_eq := by aesop
  IsLink e x y := G.IsLink e x y ∧ x ∉ X ∧ y ∉ X
  isLink_symm e he a b := by
    intro ⟨hlab, ha, hb⟩
    exact ⟨hlab.symm, hb, ha⟩
  dup_or_dup_of_isLink_of_isLink e a b c d := by
    rintro ⟨hl, ha, hb⟩ ⟨hl', hc, hd⟩
    simp only [induce_apply, mem_compl_iff, ha, not_false_eq_true, hc, true_and, hd]
    exact (G.dup_or_dup_of_isLink_of_isLink hl hl').imp id id
  isLink_of_dup e x y z := by
    rintro ⟨S, hS, hxS, hyS⟩ ⟨hl, hxX, hzX⟩
    obtain ⟨hx, hy, hdup⟩ := G.Dup.induce_apply.mp <| rel_of_mem_of_mem hS hxS hyS
    use trans' hdup hl, hx
  mem_vertexSet_of_isLink := by
    rintro e x y ⟨hl, hx, hy⟩
    simp [hx, G.mem_vertexSet_of_isLink hl]


end LabelDelete

end Graph
