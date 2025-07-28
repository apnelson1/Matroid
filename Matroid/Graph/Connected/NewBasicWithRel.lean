import Matroid.Graph.Basic
import Matroid.Graph.Walk.Basic
import Matroid.ForMathlib.Partition.Lattice


variable {α β ι ι' : Type*} {x y z u v w : α} {e f : β} {G G₁ G₂ H H₁ H₂ : Graph α β}
  {F F₁ F₂ : Set β} {X Y : Set α} {s t : Set (Graph α β)}

open Set Function Partition Relation

namespace Graph

def ConnectedPartition (G : Graph α β) : Partition (Set α) :=
  G.Dup ⊔ ofRel' (⨆ e , G.IsLink e)

@[simp]
lemma connectedPartition_rel (G : Graph α β) :
    G.ConnectedPartition = Relation.TransClosure (G.Dup ⊔ (⨆ e , G.IsLink e)) := by
  simp [ConnectedPartition, ClosureOperator.closure_sup_closure_right]

lemma dup_le_connectedPartition (G : Graph α β) : G.Dup ≤ G.ConnectedPartition := by
  rw [← rel_le_iff_le, G.connectedPartition_rel]
  exact le_sup_left.trans <| ClosureOperator.le_closure _ _

lemma isLink_le_connectedPartition (G : Graph α β) : G.IsLink e ≤ G.ConnectedPartition := by
  rw [G.connectedPartition_rel]
  exact (le_iSup _ e).trans <| le_sup_right.trans <| ClosureOperator.le_closure _ _

lemma dup_trans_connectedPartition (hdup : G.Dup x y) (h : G.ConnectedPartition y z) :
    G.ConnectedPartition x z := by
  rw [connectedPartition_rel] at h ⊢
  apply TransGen.head ?_ h
  left
  exact hdup

instance : Trans G.Dup G.ConnectedPartition G.ConnectedPartition where
  trans := dup_trans_connectedPartition

lemma ConnectedPartition.exists_isWalkFrom (hxy : G.ConnectedPartition x y) :
    ∃ w, G.IsWalkFrom {x} {y} w := by
  simp only [connectedPartition_rel] at hxy
  induction hxy with
  | single h =>
    expose_names
    obtain h | h := h
    · exact ⟨WList.nil x, by simp [dup_left_mem h], by simp [dup_left_self h], by simpa⟩
    obtain ⟨e, he⟩ := by simpa using h
    exact ⟨he.walk, he.walk_isWalkFrom⟩
  | tail h1 h2 IH =>
    expose_names
    obtain ⟨w, hw⟩ := IH
    obtain h2 | h2 := h2
    · exact ⟨w, hw.dup_right h2⟩
    obtain ⟨e, he⟩ := by simpa using h2
    exact ⟨w ++ he.walk, hw.append he.walk_isWalkFrom⟩

lemma IsWalk.connectedPartition {w : WList α β} (hw : G.IsWalk w) :
    G.ConnectedPartition w.first w.last := by
  simp only [connectedPartition_rel]
  induction w with
  | nil a =>
    apply TransGen.single
    left
    simp only [nil_isWalk_iff, WList.nil_first, WList.nil_last] at hw ⊢
    exact dup_refl_iff.mpr hw
  | cons a e w' IH =>
    simp_all only [cons_isWalk_iff, WList.first_cons, WList.last_cons, forall_const]
    refine TransGen.head ?_ IH
    right
    simp only [iSup_apply, iSup_Prop_eq]
    use e, hw.1

lemma IsWalkFrom.connectedPartition {w : WList α β} (hxy : G.IsWalkFrom {x} {y} w) :
    G.ConnectedPartition x y := by
  have hx := hxy.first_mem
  have hy := hxy.last_mem
  simp only [mem_preimage_iff, mem_singleton_iff, exists_eq_left] at hx hy
  exact trans' (trans' (symm hx) hxy.isWalk.connectedPartition) hy

lemma connectedPartition_iff_isWalkFrom {x y : α} :
    G.ConnectedPartition x y ↔ ∃ w, G.IsWalkFrom {x} {y} w :=
  ⟨ConnectedPartition.exists_isWalkFrom, fun ⟨_, hw⟩ ↦ hw.connectedPartition⟩
