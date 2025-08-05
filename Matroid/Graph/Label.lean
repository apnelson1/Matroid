import Matroid.Graph.Subgraph.Basic

variable {α β ι ι' : Type*} {x y z u v w : α} {e f : β} {G G₁ G₂ H H₁ H₂ : Graph α β}
  {F F₁ F₂ : Set β} {X Y : Set α} {s t : Set (Graph α β)} {P Q : Partition (Set α)}

open Set Function Partition

namespace Graph

section Repartition

/-- Repartition changes the labels of the graph. This can be used for adding new labels and
    vertices to a given graph but also identifying vertices. -/
@[simps!]
def Repartition (G : Graph α β) (P : Partition (Set α)) : Graph α β :=
  mk_of_domp (P.infer G.Dup) G.IsLink (by
    intro e a b c d hab hcd
    
    exact (G.dup_or_dup_of_isLink_of_isLink hlab hlcd).imp (hP _ _ ·) (hP _ _ ·))

-- @[simps!]
-- def Repartition (G : Graph α β) (P : Partition (Set α)) (hP : G.Dup ≤ P) : Graph α β :=
--   mk_of_domp P G.IsLink (fun hlab hlcd ↦ by
--     rw [← Partition.rel_le_iff_le] at hP
--     exact (G.dup_or_dup_of_isLink_of_isLink hlab hlcd).imp (hP _ _ ·) (hP _ _ ·))

@[simp]
lemma repartition_self (G : Graph α β) : G.Repartition G.Dup le_rfl = G :=
  Graph.ext (by simp) fun e x y => by rw [Repartition_isLink, Relation.domp_eq]

@[simp]
lemma repartition_inc (G : Graph α β) (hP : G.Dup ≤ P) :
    (G.Repartition P hP).Inc = Relation.Comp G.Inc P := by
  ext e x
  unfold Inc
  simp only [Repartition_isLink]
  exact ⟨fun ⟨y, a, hPxa, b, hlba, hPby⟩ ↦ ⟨a, ⟨b, hlba.symm⟩, hPxa.symm⟩,
    fun ⟨w, ⟨y, hlwy⟩, hPwx⟩ ↦ ⟨y, w, hPwx.symm, y, hlwy.symm, rel_le_of_le hP _ _ hlwy.right_refl⟩⟩

@[simp]
lemma repartition_adj (G : Graph α β) (hP : G.Dup ≤ P) :
    (G.Repartition P hP).Adj = Relation.Domp P G.Adj := by
  ext x y
  unfold Adj
  simp only [Repartition_isLink]
  exact ⟨fun ⟨e, a, hxa, b, hlba, hby⟩ ↦ ⟨a, hxa, b, ⟨e, hlba⟩, hby⟩,
    fun ⟨a, hxa, b, ⟨e, hlba⟩, hby⟩ ↦ ⟨e, a, hxa, b, hlba, hby⟩⟩

lemma repartition_le_repartition_of_subset (G : Graph α β) (hP : G.Dup ≤ P) (hPQ : P ⊆ Q) :
    G.Repartition P hP ≤ G.Repartition Q (le_trans hP (le_of_subset hPQ)) where
  dup_subset := by simp [hPQ]
  isLink_of_isLink e x y := Relation.domp_mono (rel_le_of_le (le_of_subset hPQ)) le_rfl x y

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

@[simp]
lemma vertexDelete_dup_apply (G : Graph α β) (X : Set α) (x y : α) :
    (G - X).Dup x y ↔ G.Dup x y ∧ x ∉ X ∧ y ∉ X := by
  ac_change G.Dup.induce _ x y ↔ x ∉ X ∧ y ∉ X ∧ G.Dup x y
  · exact and_rotate
  simp

@[simp]
lemma vertexDelete_empty (G : Graph α β) : G - ∅ = G := by
  ext a b c <;> simp

@[simp]
lemma vertexDelete_adj_iff (G : Graph α β) (X : Set α) :
    (G - X).Adj x y ↔ G.Adj x y ∧ x ∉ X ∧ y ∉ X := by
  simp [Adj]

lemma vertexDelete_mono_left (h : H ≤ G) : H - X ≤ G - X where
  dup_subset := induce_subset_induce_of_subset h.dup_subset
  isLink_of_isLink _ _ _ h' := by simp_all [h.isLink_of_isLink h'.1]

lemma vertexDelete_anti_right_iff : G - Y ≤l G - X ↔ V(G) \ Y ⊆ V(G) \ X := by
  refine ⟨fun h ↦ by simpa using h.vertexSet, fun h ↦ ⟨?_, fun e x y ⟨hl, hx, hy⟩ => ?_⟩⟩
  · refine (G.Dup.induce_induce _ _).trans (induce_eq_induce_iff.mpr ?_)
    ext x
    simp +contextual only [vertexDelete_vertexSet, vertexSet_def, mem_inter_iff, mem_compl_iff,
      mem_diff, and_congr_left_iff, true_and, and_iff_right_iff_imp]
    exact fun hxG hxY => h ⟨hxG, hxY⟩ |>.2
  simp [hl, (h ⟨hl.left_mem, hx⟩).2, (h ⟨hl.right_mem, hy⟩).2]

lemma vertexDelete_anti_right (hXY : X ⊆ Y) : G - Y ≤l G - X := by
  rw [vertexDelete_anti_right_iff]
  exact diff_subset_diff_right hXY

lemma vertexDelete_eq_vertexDelete_iff (G : Graph α β) (X Y : Set α) :
    G - X = G - Y ↔ V(G) \ X = V(G) \ Y := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← vertexDelete_vertexSet, ← vertexDelete_vertexSet, h]
  apply Graph.ext
  · exact induce_eq_induce_iff.mpr (by simp_rw [← diff_eq_compl_inter, G.vertexSet_def]; exact h)
  simp [Set.ext_iff] at h
  simp only [vertexDelete_isLink, and_congr_right_iff]
  exact fun e x y hl ↦ and_congr (h x hl.left_mem) (h y hl.right_mem)

@[simp]
lemma vertexDelete_isLabelSubgraph : G - X ≤l G where
  dup_induce := induce_eq_induce_iff.mpr <| by aesop
  isLink_of_isLink _ _ _ h := h.1

instance [G.Nodup] : Nodup (G - X) :=
  Nodup.of_isLabelSubgraph (vertexDelete_isLabelSubgraph)

lemma IsLink.mem_vertexDelete_iff [G.Nodup] {X : Set α} (hG : G.IsLink e x y) :
    e ∈ E(G - X) ↔ x ∉ X ∧ y ∉ X := by
  rw [vertexDelete_edgeSet, mem_setOf_eq]
  refine ⟨fun ⟨x, y, hl, hx, hy⟩ ↦ ?_, fun ⟨hx, hy⟩ ↦ ⟨x, y, hG, hx, hy⟩⟩
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hG.eq_and_eq_or_eq_and_eq hl <;> simp [hx, hy]

lemma edgeRestrict_vertexDelete (G : Graph α β) (F : Set β) (D : Set α) :
    (G ↾ F) - D = (G - D) ↾ F := by
  refine Graph.ext rfl fun e x y ↦ ?_
  simp only [vertexDelete_isLink, edgeRestrict_isLink]
  tauto

-- @[simp]
-- lemma induce_vertexDelete (G : Graph α β) (X D : Set α) : G[X] - D = G[X \ D] :=
--   Graph.ext (by ext; simp +contextual [iff_def]) <| by
--   simp only [vertexDelete_isLink_iff, induce_isLink_iff, mem_diff]
--   tauto

lemma vertexDelete_vertexDelete (G : Graph α β) (X Y : Set α) : (G - X) - Y = G - (X ∪ Y) :=
  Graph.ext (by ext; simp +contextual) <| by simp +contextual [iff_def]

lemma vertexDelete_vertexDelete_comm (G : Graph α β) (X Y : Set α) : (G - X) - Y = (G - Y) - X := by
  rw [vertexDelete_vertexDelete, vertexDelete_vertexDelete, union_comm]

-- @[simp]
-- lemma le_vertexDelete_iff : H ≤ G - X ↔ H ≤ G ∧ Disjoint V(H) X := by
--   simp only [vertexDelete_def]
--   exact fun h _ ↦ vertexSet_mono h

lemma IsClosedSubgraph.of_edgeDelete_iff (hclF : H ≤c G ＼ F) : H ≤c G ↔ E(G) ∩ F ⊆ E(G - V(H)) := by
  rw [vertexDelete_edgeSet]
  refine ⟨fun hcl f hf ↦ ?_, fun hF ↦ ⟨hclF.le.trans edgeDelete_le, ?_⟩⟩
  · by_contra! hfH
    simp only [mem_setOf_eq, not_exists, not_and, not_not] at hfH
    refine (hclF.edgeSet ?_).2 hf.2
    obtain ⟨x, y, hxy⟩ := exists_isLink_of_mem_edgeSet hf.1
    obtain hx | hy := or_iff_not_imp_left.mpr <| hfH x y hxy
    · exact hcl.closed ⟨_, hxy⟩ hx
    · exact hcl.closed ⟨_, hxy.symm⟩ hy
  · rintro e x he hxH
    have : ∀ y, G.Dup x y → y ∈ V(H) :=
      fun y h ↦ dup_right_mem (dup_of_le_of_mem hclF.le hxH <| edgeDelete_isSpanningSubgraph.dup h)
    have heF : e ∉ F := fun heF => by
      obtain ⟨u, v, heuv, hunH, hvnH⟩ := hF ⟨he.edge_mem, heF⟩
      obtain hxu | hxv := he.dup_or_dup_of_isLink heuv
      · exact hunH (this u hxu)
      · exact hvnH (this v hxv)
    exact hclF.closed (by simp [he, heF]) hxH

end LabelDelete

end Graph
