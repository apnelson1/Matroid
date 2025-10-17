import Matroid.Graph.Basic
import Matroid.ForMathlib.Partition.Foo

variable {α β : Type*} [Order.Frame α] {x y z u v w a b : α} {e f : β} {G H : Graph α β}
  {F F₁ F₂ : Set β} {X Y : Set α} {P Q : Partition (Set α)}

open Set Function Relation Partition

open scoped Sym2

namespace Graph

@[simps]
def VertexIdentification (G : Graph α β) (P : Partition (Set α)) (h : P.supp = V(G)) :
    Graph α β where
  vertexPartition := P.flatten (G.vertexSet_eq_parts ▸ h)
  IsLink e := (P.flatten (G.vertexSet_eq_parts ▸ h)).fuzzyRel (G.IsLink e)
  edgeSet := G.edgeSet
  edge_mem_iff_exists_isLink e := by
    rw [G.edge_mem_iff_exists_isLink, ← fuzzyRel_stuff (le_flatten _ _)]
    exact fun a b h ↦ ⟨h.left_mem', h.right_mem'⟩
  isLink_symm e he := fuzzyRel_symmetric <| G.isLink_symm he
  eq_or_eq_of_isLink_of_isLink e a b c d := by
    rintro ⟨ha, hb, x, y, hxy, hxa, hyb⟩ ⟨hc, hd, u, v, huv, huc, hvd⟩
    apply (G.eq_or_eq_of_isLink_of_isLink hxy huv).imp <;> rintro rfl
    <;> refine Partition.eq_of_not_disjoint ha (by assumption)
    <| not_disjoint_of_le_le hxa (by assumption) (P(G).ne_bot_of_mem hxy.left_mem')
  left_mem_of_isLink e x y hxy := hxy.1

@[simp]
lemma vertexIdentification_vertexPartition_supp (h : P.supp = V(G)) :
    (G.VertexIdentification P h).vertexPartition.supp = P(G).supp := by
  simp
