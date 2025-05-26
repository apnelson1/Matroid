import Matroid.Graph.Walk.Cycle
import Matroid.Graph.Constructions
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Finite.Prod

variable {α β : Type*} {G H T F : Graph α β} {u v x y z : α} {e e' f g : β} {X : Set α}
{P C Q : WList α β}
open Set WList

lemma finite_list_nodup (α : Type*) [Finite α] : {L : List α | L.Nodup}.Finite := by
  classical
  haveI := Fintype.ofFinite
  refine (List.finite_length_le α (Fintype.card α)).subset fun L hL ↦ ?_
  simp [List.Nodup.length_le_card hL]

@[simp]
theorem List.nodup_attachWith {α : Type*} {l : List α} (P : α → Prop) (hP : ∀ x ∈ l, P x) :
    (l.attachWith P hP).Nodup ↔ l.Nodup := by
  induction l with simp_all

namespace Graph

/-! ### Finiteness -/

@[mk_iff]
protected class Finite (G : Graph α β) : Prop where
  vertexSet_finite : V(G).Finite
  edgeSet_finite : E(G).Finite

lemma Finite.le (hG : G.Finite) (hHG : H ≤ G) : H.Finite where
  vertexSet_finite := hG.vertexSet_finite.subset <| vertexSet_subset_of_le hHG
  edgeSet_finite := hG.edgeSet_finite.subset <| edgeSet_subset_of_le hHG

lemma finite_of_le [G.Finite] (hHG : H ≤ G) : H.Finite :=
  ‹G.Finite›.le hHG

@[simp]
lemma vertexSet_finite [G.Finite] : G.vertexSet.Finite :=
  Finite.vertexSet_finite

@[simp]
lemma edgeSet_finite [G.Finite] : G.edgeSet.Finite :=
  Finite.edgeSet_finite

lemma isTrail_finite (G : Graph α β) [G.Finite] : {P | G.IsTrail P}.Finite := by
  have hVfin := G.vertexSet_finite.to_subtype
  have hEfin := G.edgeSet_finite.to_subtype
  have : Finite {L : List E(G) // L.Nodup} := finite_list_nodup E(G)
  let f (P : {P // G.IsTrail P}) : V(G) × {L : List E(G) // L.Nodup} :=
    ⟨⟨P.1.first, P.2.isWalk.vertex_mem_of_mem (by simp)⟩,
    ⟨P.1.edge.attachWith _ (fun _ ↦ P.2.isWalk.edge_mem_of_mem), by simp [P.2.edge_nodup]⟩⟩
  change Finite {P // G.IsTrail P}
  refine Finite.of_injective f fun ⟨P, hP⟩ ⟨P', hP'⟩ hPP' ↦ ?_
  simp only [Prod.mk.injEq, Subtype.mk.injEq, f] at hPP'
  simp only [Subtype.mk.injEq, f]
  apply hP.isWalk.eq_of_edge_eq_first_eq hP'.isWalk hPP'.1
  convert congr_arg (fun L ↦ L.map Subtype.val) hPP'.2 <;> simp

lemma isPath_finite (G : Graph α β) [G.Finite] : {P | G.IsPath P}.Finite :=
  G.isTrail_finite.subset fun _ ↦ IsPath.isTrail

lemma isCycle_finite (G : Graph α β) [G.Finite] : {C | G.IsCycle C}.Finite :=
  G.isTrail_finite.subset fun _ ↦ IsCycle.isTrail


/-! ### Local Finiteness -/

class LocallyFinite (G : Graph α β) where
  setOf_inc_finite : ∀ x, {e | G.Inc e x}.Finite



end Graph

-- lemma IsForest.exists_isLeaf [G.Finite] (hG : )
