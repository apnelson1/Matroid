import Matroid.Graph.Constructions.Basic

variable {α β ι ι' : Type*} {x y z u v w : α} {e f : β} {G G₁ G₂ H H₁ H₂ : Graph α β}
  {F F₁ F₂ : Set β} {X Y : Set α} {s t : Set (Graph α β)} {P Q : Partition (Set α)}

open Set Function Partition

namespace Graph

section Repartition

/-- Repartition changes the labels of the graph. This can be used for adding new labels and
    vertices to a given graph but also identifying vertices. -/
@[simps!]
def repartition (G : Graph α β) (P : Partition (Set α)) : Graph α β :=
  mk' P G.IsLink

@[simp]
lemma repartition_self (G : Graph α β) : G.repartition V(G) = G :=
  Graph.ext (by simp) fun e x y => by
    simp [G.dup_or_dup_of_isLink_of_isLink, Relation.domp_eq]

@[simp]
lemma repartition_isLink_of_vertexSet_le (hP : V(G) ≤ P) :
    (G.repartition P).IsLink e = Relation.Domp P (G.IsLink e) := by
  ext x y
  simp [btwVx_mono_left hP (G.dup_or_dup_of_isLink_of_isLink (e := e))]

@[simp]
lemma repartition_inc_of_vertexSet_le (hP : V(G) ≤ P) :
    (G.repartition P).Inc = Relation.Comp G.Inc P := by
  ext e x
  unfold Inc
  simp only [repartition_isLink_of_vertexSet_le hP]
  exact ⟨fun ⟨y, a, hPxa, b, hlba, hPby⟩ ↦ ⟨a, ⟨b, hlba.symm⟩, hPxa.symm⟩,
    fun ⟨w, ⟨y, hlwy⟩, hPwx⟩ ↦ ⟨y, w, hPwx.symm, y, hlwy.symm, rel_le_of_le hP _ _ hlwy.right_refl⟩⟩

@[simp]
lemma repartition_adj_of_vertexSet_le (hP : V(G) ≤ P) :
    (G.repartition P).Adj = Relation.Domp P G.Adj := by
  ext x y
  unfold Adj
  simp only [repartition_isLink_of_vertexSet_le hP]
  exact ⟨fun ⟨e, a, hxa, b, hlba, hby⟩ ↦ ⟨a, hxa, b, ⟨e, hlba⟩, hby⟩,
    fun ⟨a, hxa, b, ⟨e, hlba⟩, hby⟩ ↦ ⟨e, a, hxa, b, hlba, hby⟩⟩

lemma repartition_isLink_of_vertexSet_isInducedSubpartition (hP : P ≤ip V(G)) :
    (G.repartition P).IsLink e = fun x y ↦ G.IsLink e x y ∧ x ∈ P.supp ∧ y ∈ P.supp := by
  ext x y
  nth_rw 1 [← hP]
  simp only [repartition_isLink, ↓induce_supp', inf_eq_inter, induce_rel]
  refine ⟨fun ⟨h, x', hx', y', hy'x', hy'⟩ =>
    ⟨trans' (trans' hx'.2.2 hy'x'.symm) hy'.2.2, hx'.1, hy'.2.1⟩,
    fun ⟨hxy, hx, hy⟩ => ⟨?_, x, ⟨hx, hx, hxy.left_refl⟩, y, hxy.symm, ⟨hy, hy, hxy.right_refl⟩⟩⟩
  have := btwVx_restrict (@G.dup_or_dup_of_isLink_of_isLink e) (S := P.supp)
  apply btwVx_anti_right ?_ this
  apply Relation.restrict_subset
  exact inter_subset_left

lemma repartition_le_repartition_of_subset (hPQ : P ⊆ Q) (hV : V(G) ≤ Q) :
    G.repartition P ≤ G.repartition Q where
  vertexSet_subset := by simp [hPQ]
  isLink_of_isLink e x y := by
    simp only [repartition_isLink, and_imp]
    exact fun hbtwP hdompP ↦ ⟨fun a b c d ⟨hab, ha, hb⟩ ⟨hcd, hc, hd⟩ =>
      G.dup_or_dup_of_isLink_of_isLink hab hcd |>.imp (rel_le_of_le hV a c) (rel_le_of_le hV a d),
      Relation.domp_mono (rel_le_of_subset hPQ) le_rfl _ _ hdompP⟩

lemma repartition_le_repartition_iff (hV : V(G) ≤ Q) : G.repartition P ≤ G.repartition Q ↔ P ⊆ Q :=
  ⟨fun h ↦ h.1, (repartition_le_repartition_of_subset · hV)⟩

end Repartition

section LabelInduce

/-- The graph obtained from `G` by inducing a set of labels. -/
@[simps! vertexSet]
def labelInduce (G : Graph α β) (X : Set α) : Graph α β :=
  G.repartition (V(G).induce X)

@[simp]
lemma labelInduce_labelSet (G : Graph α β) (X : Set α) : L(G.labelInduce X) = L(G) ∩ X := by
  simp [labelInduce, inter_comm, induce_supp']

@[simp]
lemma labelInduce_isLink : (G.labelInduce X).IsLink e = Relation.restrict (G.IsLink e) X := by
  ext x y
  simp only [labelInduce, repartition_isLink, ↓induce_supp', inf_eq_inter, induce_rel]
  refine ⟨fun ⟨hl, x', ⟨hx, hx', hVx⟩, y', hxy, hy', hy, hVy⟩ ↦
    ⟨trans' (trans' hVx (symm hxy)) hVy, hx, hy⟩, fun ⟨hl, hx, hy⟩ ↦
    ⟨?_, x, ⟨hx, hx, hl.left_refl⟩, y, symm hl, ⟨hy, hy, hl.right_refl⟩⟩⟩
  apply btwVx_anti_right ?_ <| btwVx_restrict (@G.dup_or_dup_of_isLink_of_isLink e)
  exact Relation.restrict_subset _ inter_subset_left

@[simp]
lemma labelInduce_edgeSet :
    E(G.labelInduce X) = {e | ∃ x y, (Relation.restrict (G.IsLink e) X) x y} := by
  simp_rw [edgeSet_eq_setOf_exists_isLink, labelInduce_isLink]

end LabelInduce

section LabelDelete

/-- The graph obtained from `G` by deleting a set of labels. -/
@[simps! vertexSet]
def labelDelete (G : Graph α β) (X : Set α) : Graph α β := G.labelInduce Xᶜ

@[simp]
lemma labelDelete_labelSet : L(G.labelDelete X) = L(G) \ X := by
  simp only [labelDelete, labelInduce_vertexSet, induce_supp', inf_eq_inter]
  exact diff_eq_compl_inter.symm

@[simp]
lemma labelDelete_isLink : (G.labelDelete X).IsLink e = Relation.restrict (G.IsLink e) Xᶜ := by
  simp [labelDelete]

@[simp]
lemma labelDelete_edgeSet :
    E(G.labelDelete X) = {e | ∃ x y, (Relation.restrict (G.IsLink e) Xᶜ) x y} := by
  simp_rw [edgeSet_eq_setOf_exists_isLink, labelDelete_isLink]

end LabelDelete

end Graph
