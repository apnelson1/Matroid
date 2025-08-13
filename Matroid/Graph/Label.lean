import Matroid.Graph.Constructions.Basic

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
lemma repartition_self (G : Graph α β) : G.Repartition V(G) = G :=
  Graph.ext (by simp) fun e x y => by
    simp [G.dup_or_dup_of_isLink_of_isLink, Relation.domp_eq]

lemma repartition_isLink_of_vertexSet_le (hP : V(G) ≤ P) :
    (G.Repartition P).IsLink e = Relation.Domp P (G.IsLink e) := by
  ext x y
  simp [btwVx_mono_left hP (G.dup_or_dup_of_isLink_of_isLink (e := e))]

@[simp]
lemma repartition_inc_of_vertexSet_le (hP : V(G) ≤ P) :
    (G.Repartition P).Inc = Relation.Comp G.Inc P := by
  ext e x
  unfold Inc
  simp only [repartition_isLink_of_vertexSet_le hP]
  exact ⟨fun ⟨y, a, hPxa, b, hlba, hPby⟩ ↦ ⟨a, ⟨b, hlba.symm⟩, hPxa.symm⟩,
    fun ⟨w, ⟨y, hlwy⟩, hPwx⟩ ↦ ⟨y, w, hPwx.symm, y, hlwy.symm, rel_le_of_le hP _ _ hlwy.right_refl⟩⟩

@[simp]
lemma repartition_adj_of_vertexSet_le (hP : V(G) ≤ P) :
    (G.Repartition P).Adj = Relation.Domp P G.Adj := by
  ext x y
  unfold Adj
  simp only [repartition_isLink_of_vertexSet_le hP]
  exact ⟨fun ⟨e, a, hxa, b, hlba, hby⟩ ↦ ⟨a, hxa, b, ⟨e, hlba⟩, hby⟩,
    fun ⟨a, hxa, b, ⟨e, hlba⟩, hby⟩ ↦ ⟨e, a, hxa, b, hlba, hby⟩⟩

lemma repartition_le_repartition_of_subset {P Q : Partition (Set α)} (hPQ : P ⊆ Q) :
    G.Repartition P ≤ G.Repartition Q where
  vertexSet_subset := by simp [hPQ]
  isLink_of_isLink e x y := by
    simp only [Repartition_isLink, and_imp]
    exact fun hbtw hPxy ↦ ⟨btwVx_mono_left (le_of_subset hPQ) hbtw,
      Relation.domp_mono (rel_le_of_le (le_of_subset hPQ)) le_rfl x y hPxy⟩

lemma repartition_le_repartition_iff {P Q : Partition (Set α)} :
    G.Repartition P ≤ G.Repartition Q ↔ P ⊆ Q :=
  ⟨fun h ↦ h.1, repartition_le_repartition_of_subset⟩

end Repartition

section LabelInduce

/-- The graph obtained from `G` by inducing a set of labels. -/
@[simps! vertexSet edgeSet isLink]
def labelInduce (G : Graph α β) (X : Set α) : Graph α β :=
  G.Repartition (V(G).induce X)

@[simp]
lemma labelInduce_labelSet (G : Graph α β) (X : Set α) : L(G.labelInduce X) = L(G) ∩ X := by
  simp [labelInduce, inter_comm, induce_supp']

end LabelInduce

section LabelDelete

/-- The graph obtained from `G` by deleting a set of labels. -/
@[simps! vertexSet edgeSet isLink]
def labelDelete (G : Graph α β) (X : Set α) : Graph α β :=
  G.Repartition (V(G).induce Xᶜ)

@[simp]
lemma labelDelete_labelSet (G : Graph α β) (X : Set α) :
    L(G.labelDelete X) = L(G) \ X := by
  simp only [labelDelete, Repartition_vertexSet, ↓induce_supp', inf_eq_inter]
  exact diff_eq_compl_inter.symm

end LabelDelete

end Graph
