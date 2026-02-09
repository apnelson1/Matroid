import Matroid.Graph.Walk.Cycle
import Matroid.Graph.Simple
import Matroid.Graph.Lattice
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Finite.Prod

variable {α β : Type*} {G H T F : Graph α β} {u v x y z : α} {e e' f g : β} {X : Set α}
{P C Q : WList α β} {F : Set β}

open Set

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
class EdgeFinite (G : Graph α β) : Prop where
  edgeSet_finite : E(G).Finite

lemma edgeFinite_of_le [G.EdgeFinite] (hHG : H ≤ G) : H.EdgeFinite where
  edgeSet_finite := ‹G.EdgeFinite›.edgeSet_finite.subset <| edgeSet_mono hHG

instance [G.EdgeFinite] (X : Set α) : (G - X).EdgeFinite :=
  edgeFinite_of_le vertexDelete_le

instance [G.EdgeFinite] (F : Set β) : (G ↾ F).EdgeFinite :=
  edgeFinite_of_le edgeRestrict_le

instance [G.EdgeFinite] (F : Set β) : (G ＼ F).EdgeFinite :=
  edgeFinite_of_le edgeDelete_le

lemma edgeFinite_induce [G.EdgeFinite] (hX : X ⊆ V(G)) : (G[X]).EdgeFinite :=
  edgeFinite_of_le (induce_le hX)

@[simp]
lemma edgeSet_finite [G.EdgeFinite] : E(G).Finite := EdgeFinite.edgeSet_finite

lemma endSetSet_finite (G : Graph α β) [G.EdgeFinite] (F : Set β) : V(G, F).Finite := by
  rw [← endSetSet_inter_edgeSet, ← encard_lt_top_iff]
  refine lt_of_le_of_lt (G.endSetSet_encard_le (F ∩ E(G)))
  <| WithTop.mul_lt_top (compareOfLessAndEq_eq_lt.mp rfl)
  <| encard_lt_top_iff.mpr G.edgeSet_finite |>.trans_le' (encard_le_encard inter_subset_right)

lemma nonempty_isTrail_finite (G : Graph α β) [G.EdgeFinite] :
    {P | P.Nonempty ∧ G.IsTrail P}.Finite := by
  have hVfin := G.endSetSet_finite E(G) |>.to_subtype
  have hEfin := G.edgeSet_finite.to_subtype
  have : Finite {L : List E(G) // L.Nodup} := finite_list_nodup E(G)
  let f (P : {P // P.Nonempty ∧ G.IsTrail P}) : V(G, E(G)) × {L : List E(G) // L.Nodup} :=
    ⟨⟨P.1.first, ?endSetSet⟩,
    ⟨P.1.edge.attachWith _ (fun _ ↦ P.2.2.isWalk.edge_mem_of_mem), by simp [P.2.2.edge_nodup]⟩⟩
  case endSetSet =>
    obtain ⟨v, e, w, hp⟩ := P.2.1.exists_cons
    obtain ⟨hl, hw⟩ := by simpa [hp] using P.2.2.isWalk
    exact hp ▸ ⟨e, hl.edge_mem, hl.inc_left⟩
  change Finite {P // P.Nonempty ∧ G.IsTrail P}
  refine Finite.of_injective f fun ⟨P, hP⟩ ⟨P', hP'⟩ hPP' ↦ ?_
  simp only [Prod.mk.injEq, Subtype.mk.injEq, f] at hPP'
  simp only [Subtype.mk.injEq]
  apply hP.2.isWalk.eq_of_edge_eq_first_eq hP'.2.isWalk hPP'.1
  convert congr_arg (fun L ↦ L.map Subtype.val) hPP'.2 <;> simp

private lemma eq_singleton_of_forall_nil {c : Set (WList α β)} {p : WList α β}
    (hch : IsChain (· ≤ ·) c) (hcne : ∀ x ∈ c, x.Nil) (hpc : p ∈ c) : c = {p} := by
  apply Subsingleton.eq_singleton_of_mem (fun x hx y hy ↦ ?_) hpc
  obtain hle | hle := hch.total hx hy
  · exact (hcne y hy).eq_of_le hle
  · exact (hcne x hx).eq_of_le hle |>.symm

lemma exists_le_maximal_isTrail [G.EdgeFinite] {t : WList α β} (ht : G.IsTrail t) :
    ∃ m, t ≤ m ∧ Maximal G.IsTrail m := by
  refine zorn_le_nonempty₀ {p | G.IsTrail p} (fun c hc hch p hpc ↦ ?_) t ht
  by_cases hcne : ∃ p' ∈ c, p'.Nonempty
  · obtain ⟨p', hp'c, hp'ne⟩ := hcne
    obtain ⟨ub, hub, hubmax⟩ := G.nonempty_isTrail_finite.subset inter_subset_right
      |>.exists_le_maximal ⟨hp'c, hp'ne, hc hp'c⟩
    use ub, hubmax.prop.2.2, fun z hz ↦ ?_
    obtain ⟨x, rfl⟩ | hzne := z.exists_eq_nil_or_nonempty
    · exact hch.total hubmax.prop.1 hz |>.resolve_left fun hle ↦ by simp_all
    exact hch.total hubmax.prop.1 hz |>.elim (hubmax.le_of_ge ⟨hz, hzne, hc hz⟩) id
  simp only [not_exists, not_and, WList.not_nonempty_iff] at hcne
  obtain rfl : c = {p} := eq_singleton_of_forall_nil hch hcne hpc
  use p, (by simpa using hc), by simp

lemma exists_le_maximal_isPath [G.EdgeFinite] {p : WList α β} (hp : G.IsPath p) :
    ∃ m, p ≤ m ∧ Maximal G.IsPath m := by
  refine zorn_le_nonempty₀ {p | G.IsPath p} (fun c hc hch p hpc ↦ ?_) p hp
  by_cases hcne : ∃ p' ∈ c, p'.Nonempty
  · obtain ⟨p', hp'c, hp'ne⟩ := hcne
    have hsu : c ∩ {P | P.Nonempty ∧ G.IsPath P} ⊆ {p' | p'.Nonempty ∧ G.IsTrail p'} :=
      fun _ ⟨hc, hne, hp⟩ ↦ ⟨hne, hp.isTrail⟩
    obtain ⟨ub, hub, hubmax⟩ := G.nonempty_isTrail_finite.subset hsu
      |>.exists_le_maximal ⟨hp'c, hp'ne, hc hp'c⟩
    use ub, hubmax.prop.2.2, fun z hz ↦ ?_
    obtain ⟨x, rfl⟩ | hzne := z.exists_eq_nil_or_nonempty
    · exact hch.total hubmax.prop.1 hz |>.resolve_left fun hle ↦ by simp_all
    exact hch.total hubmax.prop.1 hz |>.elim (hubmax.le_of_ge ⟨hz, hzne, hc hz⟩) id
  simp only [not_exists, not_and, WList.not_nonempty_iff] at hcne
  obtain rfl : c = {p} := eq_singleton_of_forall_nil hch hcne hpc
  use p, (by simpa using hc), by simp

lemma exists_le_maximal_isCyclicWalk [G.EdgeFinite] (hC : G.IsCyclicWalk C) :
    ∃ m, C ≤ m ∧ Maximal G.IsCyclicWalk m := by
  refine zorn_le_nonempty₀ {p | G.IsCyclicWalk p} (fun c hc hch p hpc ↦ ?_) C hC
  by_cases hcne : ∃ p' ∈ c, p'.Nonempty
  · obtain ⟨p', hp'c, hp'ne⟩ := hcne
    have hsu : c ∩ {P | P.Nonempty ∧ G.IsCyclicWalk P} ⊆ {p' | p'.Nonempty ∧ G.IsTrail p'} :=
      fun _ ⟨hc, hne, hp⟩ ↦ ⟨hne, hp.isTrail⟩
    obtain ⟨ub, hub, hubmax⟩ := G.nonempty_isTrail_finite.subset hsu
      |>.exists_le_maximal ⟨hp'c, hp'ne, hc hp'c⟩
    use ub, hubmax.prop.2.2, fun z hz ↦ ?_
    obtain ⟨x, rfl⟩ | hzne := z.exists_eq_nil_or_nonempty
    · exact hch.total hubmax.prop.1 hz |>.resolve_left fun hle ↦ by simp_all
    exact hch.total hubmax.prop.1 hz |>.elim (hubmax.le_of_ge ⟨hz, hzne, hc hz⟩) id
  simp only [not_exists, not_and, WList.not_nonempty_iff] at hcne
  obtain rfl : c = {p} := eq_singleton_of_forall_nil hch hcne hpc
  use p, (by simpa using hc), by simp

/-- A graph is finite if it has finitely many vertices and edges -/
@[mk_iff]
protected class Finite (G : Graph α β) : Prop extends G.EdgeFinite where
  vertexSet_finite : V(G).Finite

lemma Finite.mono (hG : G.Finite) (hHG : H ≤ G) : H.Finite where
  vertexSet_finite := hG.vertexSet_finite.subset <| vertexSet_mono hHG
  edgeSet_finite := hG.edgeSet_finite.subset <| edgeSet_mono hHG

lemma finite_of_le [G.Finite] (hHG : H ≤ G) : H.Finite :=
  ‹G.Finite›.mono hHG

instance [G.Finite] (X : Set α) : (G - X).Finite :=
  ‹G.Finite›.mono vertexDelete_le

instance [G.Finite] (F : Set β) : (G ↾ F).Finite :=
  ‹G.Finite›.mono edgeRestrict_le

instance [G.Finite] (F : Set β) : (G ＼ F).Finite :=
  ‹G.Finite›.mono edgeDelete_le

lemma Finite.induce (hG : G.Finite) (hX : X ⊆ V(G)) : G[X].Finite where
  vertexSet_finite := hG.vertexSet_finite.subset hX
  edgeSet_finite := hG.edgeSet_finite.subset (by simp)

@[simp]
lemma vertexSet_finite [G.Finite] : G.vertexSet.Finite :=
  Finite.vertexSet_finite

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
  simp only [Subtype.mk.injEq]
  apply hP.isWalk.eq_of_edge_eq_first_eq hP'.isWalk hPP'.1
  convert congr_arg (fun L ↦ L.map Subtype.val) hPP'.2 <;> simp

lemma isPath_finite (G : Graph α β) [G.Finite] : {P | G.IsPath P}.Finite :=
  G.isTrail_finite.subset fun _ ↦ IsPath.isTrail

lemma isCyclicWalk_finite (G : Graph α β) [G.Finite] : {C | G.IsCyclicWalk C}.Finite :=
  G.isTrail_finite.subset fun _ ↦ IsCyclicWalk.isTrail

/-- A finite graph has finitely many subgraphs. -/
lemma finite_setOf_le (G : Graph α β) [G.Finite] : {H | H ≤ G}.Finite := by
  refine Finite.of_finite_image (f := fun H ↦ (⟨V(H), E(H)⟩ : Set α × Set β)) ?_
    fun H₁ h₁ H₂ h₂ h_eq ↦ ?_
  · refine (G.vertexSet_finite.finite_subsets.prod G.edgeSet_finite.finite_subsets).subset ?_
    rintro _ ⟨H, hle : H ≤ G, rfl⟩
    simp [vertexSet_mono hle, edgeSet_mono hle]
  simp only [Prod.mk.injEq] at h_eq
  exact G.ext_of_le_le h₁ h₂ h_eq.1 h_eq.2

lemma finite_of_vertexSet_finite [G.Simple] (h : V(G).Finite) : G.Finite where
  vertexSet_finite := h
  edgeSet_finite := by
    change Finite _ at *
    exact Finite.of_injective _ G.ends_injective

@[simp]
lemma Simple.vertexSet_finite_iff [G.Simple] : V(G).Finite ↔ G.Finite :=
  ⟨finite_of_vertexSet_finite, fun _ ↦ Finite.vertexSet_finite⟩

instance (G : Graph α β) [G.Finite] : Finite G.Subgraph := finite_setOf_le G

instance (G : Graph α β) [G.Finite] : Finite G.ClosedSubgraph :=
  G.finite_setOf_le.subset fun _ hH ↦ hH.le

instance [G.Finite] [H.Finite] : (G ∪ H).Finite where
  vertexSet_finite := G.vertexSet_finite.union H.vertexSet_finite
  edgeSet_finite := G.edgeSet_finite.union H.edgeSet_finite

instance : (Graph.singleEdge x y e).Finite where
  vertexSet_finite := by simp
  edgeSet_finite := by simp

instance (W : WList α β) : W.toGraph.Finite where
  vertexSet_finite := by simp
  edgeSet_finite := by simp

lemma IsCycleGraph.finite (hC : H.IsCycleGraph) : H.Finite := by
  rw [isCycleGraph_iff_toGraph_isCyclicWalk] at hC
  obtain ⟨C, hC, rfl⟩ := hC
  infer_instance

/-- Used for well-founded induction on finite graphs by number of vertices -/
lemma encard_delete_vertex_lt [G.Finite] (hx : x ∈ V(G)) :
    V(G - ({x} : Set α)).encard < V(G).encard := by
  rw [vertexDelete_vertexSet]
  exact (G.vertexSet_finite.subset diff_subset).encard_lt_encard (by simpa)

lemma encard_delete_vertexSet_lt [G.Finite] (hX : (V(G) ∩ X).Nonempty) :
    V(G - X).encard < V(G).encard := by
  rw [vertexDelete_vertexSet]
  exact (G.vertexSet_finite.subset diff_subset).encard_lt_encard (by simpa)

/-- Used for well-founded induction on finite graphs by number of edges -/
lemma encard_delete_edge_lt [G.Finite] (he : e ∈ E(G)) :
    E(G ＼ {e}).encard < E(G).encard := by
  rw [edgeDelete_edgeSet]
  exact (G.edgeSet_finite.subset diff_subset).encard_lt_encard (by simpa)

lemma encard_delete_edgeSet_lt [G.Finite] (hF : (E(G) ∩ F).Nonempty) :
    E(G ＼ F).encard < E(G).encard := by
  rw [edgeDelete_edgeSet]
  exact (G.edgeSet_finite.subset diff_subset).encard_lt_encard (by simpa)

lemma of_not_exists_minimal {P : Graph α β → Prop} [G.Finite]
    (h : ∀ H, H ≤ G → H.Finite → ¬ Minimal (¬ P ·) H) : P G := by
  by_contra! hPG
  let P' := fun (H : G.Subgraph) ↦ ¬ P H.val
  obtain ⟨H, hH⟩ := exists_minimal_of_wellFoundedLT P' ⟨⟨G, le_refl _⟩, hPG⟩
  refine h H H.prop (‹G.Finite›.mono H.prop) ⟨hH.prop, fun H' hH' hH'' ↦ ?_⟩
  simpa [P', hH', hH''] using hH.2 (y := ⟨H', hH''.trans H.prop⟩)

-- instance [G.Finite] : WellFoundedLT G.Subgraph := inferInstance

-- instance [G.Finite] : WellFoundedLT G.ClosedSubgraph := inferInstance


/-! ### Local Finiteness -/

/-- A graph is `LocallyFinite` if each of its vertices is incident with finitely many edges. -/
@[mk_iff]
protected class LocallyFinite (G : Graph α β) where
  finite : ∀ x : α, Set.Finite E(G, x)

lemma finite_incEdges (G : Graph α β) [G.LocallyFinite] (x : α) : E(G, x).Finite :=
  LocallyFinite.finite x

lemma finite_neighbors (G : Graph α β) [G.LocallyFinite] : N(G, x).Finite := by
  change Finite N(G, x)
  have : Finite E(G, x) := G.finite_incEdges x
  refine Finite.of_injective (β := E(G, x))
    (fun y ↦ ⟨y.2.choose, y.2.choose_spec.inc_left⟩) fun ⟨y₁, hy₁⟩ ⟨y₂, hy₂⟩ ↦ ?_
  simp only [Subtype.mk.injEq]
  generalize_proofs h₁ h₂
  refine fun h ↦  h₁.choose_spec.right_unique ?_
  rw [h]
  exact h₂.choose_spec

lemma finite_setOf_isNonloopAt (G : Graph α β) [G.LocallyFinite] :
  {e | G.IsNonloopAt e x}.Finite := (G.finite_incEdges x).subset fun _ he ↦ he.inc

lemma finite_setOf_isLoopAt (G : Graph α β) [G.LocallyFinite] :
  {e | G.IsLoopAt e x}.Finite := (G.finite_incEdges x).subset fun _ he ↦ he.inc

instance [Finite β] (G : Graph α β) : G.LocallyFinite where
  finite _ := toFinite ..

lemma LocallyFinite.mono (hG : G.LocallyFinite) (hle : H ≤ G) : H.LocallyFinite where
  finite _ := (G.finite_incEdges _).subset fun _ he ↦ he.of_le hle

instance [G.LocallyFinite] (X : Set α) : G[X].LocallyFinite where
  finite _ := (G.finite_incEdges _).subset fun _ ⟨_, he⟩ ↦ ((induce_isLink ..) ▸ he).1.inc_left

instance [G.LocallyFinite] (X : Set α) : (G - X).LocallyFinite :=
  ‹G.LocallyFinite›.mono vertexDelete_le

instance [G.LocallyFinite] (F : Set β) : (G ↾ F).LocallyFinite :=
  ‹G.LocallyFinite›.mono edgeRestrict_le

instance [G.LocallyFinite] (F : Set β) : (G ＼ F).LocallyFinite :=
  ‹G.LocallyFinite›.mono edgeDelete_le

instance [G.EdgeFinite] : G.LocallyFinite where
  finite _ := ‹G.EdgeFinite›.edgeSet_finite.subset fun _ ↦ Inc.edge_mem

instance [G.LocallyFinite] [H.LocallyFinite] : (G ∪ H).LocallyFinite where
  finite x := by
    refine ((G.finite_incEdges (x := x)).union (H.finite_incEdges (x := x))).subset ?_
    simp_rw [IncEdges, union_inc_iff, subset_def]
    aesop

instance (V : Set α) : (Graph.noEdge V β).LocallyFinite where
  finite := by simp

@[simp]
lemma vertexSet_finite_iff [G.LocallyFinite] : V(G).Finite ↔ G.Finite := by
  refine ⟨fun h ↦ {vertexSet_finite := h, edgeSet_finite := ?_}, fun h ↦ Finite.vertexSet_finite⟩
  refine (h.biUnion (t := fun v ↦ E(G, v)) (fun i a ↦ LocallyFinite.finite i )).subset ?_
  simp only [subset_def, mem_iUnion, exists_prop]
  intro e he
  obtain ⟨x, y, hx⟩ := exists_isLink_of_mem_edgeSet he
  exact ⟨_, hx.left_mem, hx.inc_left⟩

-- instance instWellFoundedLTGraph [Finite α] [Finite β] : WellFoundedLT (Graph α β) := by
--   let f : Graph α β → ℕ := fun G ↦ V(G).ncard + E(G).ncard
--   have hf : StrictMono f := by
--     rintro G H hlt
--     simp only [f]
--     obtain ⟨hle, hne⟩ := lt_iff_le_and_ne.mp hlt
--     obtain hV | hV := ssubset_or_eq_of_subset <| vertexSet_mono hle
--     · have hE' : E(G) ⊆ E(H) := edgeSet_mono hle
--       have hE'ncard : E(G).ncard ≤ E(H).ncard := ncard_le_ncard hE'
--       have hVncard : V(G).ncard < V(H).ncard := ncard_lt_ncard hV (toFinite V(H))
--       exact Nat.add_lt_add_of_lt_of_le hVncard hE'ncard
--     rw [hV]
--     obtain hE | hE := ssubset_or_eq_of_subset <| edgeSet_mono hle
--     · have hEncard : E(G).ncard < E(H).ncard := ncard_lt_ncard hE (toFinite E(H))
--       exact Nat.add_lt_add_left hEncard V(H).ncard
--     obtain rfl := ext_of_le_le hle le_rfl hV hE
--     simp only [ne_eq, not_true_eq_false] at hne
--   exact hf.wellFoundedLT

-- lemma minimal_exist {P : Graph α β → Prop} [Finite α] [Finite β] (h : P G) :
--     ∃ G : Graph α β, Minimal P G :=
--   exists_minimal_of_wellFoundedLT _ (by use G)

-- lemma forall_of_minimal_not_exist {P : Graph α β → Prop} [Finite α] [Finite β]
--     (h : ¬ ∃ G : Graph α β, Minimal (¬ P ·) G) : P G := by
--   contrapose! h
--   exact minimal_exist h

end Graph

-- lemma IsForest.exists_isLeaf [G.Finite] (hG : )
