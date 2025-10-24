import Matroid.Graph.Lattice
import Matroid.Graph.Finite
import Matroid.Graph.Degree.Defs
-- import Matroid.Graph.Degree.Constructions

open Set Function Nat WList

variable {α β : Type*} [CompleteLattice α] {G H : Graph α β} {u v x x₁ x₂ y y₁ y₂ z : α}
  {e e' f g : β} {U V S T : Set α} {F F' R R': Set β} {C W P Q : WList α β}

namespace Graph

/-! ### Components -/


variable {G H H' H₁ H₂ : Graph α β}

lemma IsCompOf.ne_bot (hHco : H.IsCompOf G) : H ≠ ⊥ := by
  let H' : G.ClosedSubgraph := ⟨H, hHco.isClosedSubgraph⟩
  rw [← H'.isAtom_iff_isCompOf] at hHco
  exact Subtype.coe_ne_coe.mpr hHco.1

@[simp]
lemma bot_not_isCompOf : ¬ (⊥ : Graph α β).IsCompOf G := (·.ne_bot rfl)

@[simp]
lemma not_isCompOf_bot : ¬ G.IsCompOf ⊥ := by
  intro ⟨⟨hcl, hV⟩, _⟩
  rw [isClosedSubgraph_bot_iff] at hcl
  subst G
  simp at hV

lemma IsClosedSubgraph.le_isCompOf_iff (hH₁cl : H₁ ≤c G) (hH₂co : H₂.IsCompOf G) :
    H₁ ≤ H₂ ↔ (H₁ = ⊥ ∨ H₁ = H₂) := by
  let H₁' : G.ClosedSubgraph := ⟨H₁, hH₁cl⟩
  let H₂' : G.ClosedSubgraph := ⟨H₂, hH₂co.isClosedSubgraph⟩
  change H₁' ≤ H₂' ↔ H₁'.val = (⊥ : G.ClosedSubgraph).val ∨ H₁'.val = H₂'.val
  rw [← H₂'.isAtom_iff_isCompOf] at hH₂co
  rw [Subtype.coe_inj, Subtype.coe_inj]
  exact hH₂co.le_iff

lemma IsClosedSubgraph.lt_isCompOf_iff (hH₁cl : H₁ ≤c G) (hH₂co : H₂.IsCompOf G) :
    H₁ < H₂ ↔ H₁ = ⊥ := by
  rw [lt_iff_le_and_ne, hH₁cl.le_isCompOf_iff hH₂co]
  by_cases h : H₁ = H₂
  · simp [h, hH₂co.ne_bot]
  · simp [h]

lemma IsClosedSubgraph.eq_of_le_isCompOf_of_vertexSet_not_disjoint (hH₁cl : H₁ ≤c G)
    (hH₂co : H₂.IsCompOf G) (hle : H₁ ≤ H₂) (hV : ¬ Disjoint V(H₁) V(H₂)) : H₁ = H₂ := by
  rw [hH₁cl.le_isCompOf_iff hH₂co] at hle
  refine hle.resolve_left ?_
  rintro rfl
  simp at hV

lemma IsCompOf.of_isClosedSubgraph (hHcl : H ≤c G) (hH'co : H'.IsCompOf H) :
    H'.IsCompOf G := by
  obtain ⟨⟨hH'co, hVH'⟩, hH'min⟩ := hH'co
  exact ⟨⟨hH'co.trans hHcl, hVH'⟩, fun H₀ ⟨hH₀cl, hVH₀⟩ hH₀leH' =>
    hH'min ⟨hH₀cl.of_le_of_le (hH₀leH'.trans hH'co.le) hHcl.le, hVH₀⟩ hH₀leH'⟩


def walkable (G : Graph α β) (u : α) : Graph α β :=
  G[{x | ∃ W, G.IsWalk W ∧ W.first = u ∧ W.last = x}]

lemma mem_walkable (hx : x ∈ V(G)) : x ∈ V(G.walkable x) := by
  simp only [walkable, induce_vertexSet, mem_inter_iff, mem_setOf_eq]
  exact ⟨hx, ⟨.nil x, by simpa, rfl, rfl⟩⟩

lemma walkable_isClosedSubgraph : G.walkable u ≤c G where
  toIsSubgraph := induce_le
  closed := by
    rintro e x ⟨y₁, hl⟩ ⟨hx, W, hW, rfl, rfl⟩
    use W.last, y₁, hl, ⟨W, hW, rfl, rfl⟩, W.concat e y₁, ?_, concat_first, concat_last
    simp [hW, hl]

lemma Adj.mem_walkable (h : G.Adj x y) : y ∈ V(G.walkable x) := by
  obtain ⟨e, hl⟩ := h
  exact ⟨hl.right_mem, hl.walk, hl.walk_isWalk, hl.walk_first, hl.walk_last⟩

@[simp]
lemma mem_walkable_self_iff : x ∈ V(G.walkable x) ↔ x ∈ V(G) :=
  ⟨(walkable_isClosedSubgraph.vertexSet_mono ·), mem_walkable⟩

@[simp]
lemma walkable_eq_bot (hx : x ∉ V(G)) : G.walkable x = ⊥ := by
  rw [walkable, ← vertexSet_eq_empty_iff, induce_vertexSet, Set.eq_empty_iff_forall_notMem]
  simp only [mem_inter_iff, mem_setOf_eq, not_and, not_exists]
  rintro y hy W hW rfl rfl
  exact hx hW.first_mem

lemma exists_isWalk_of_mem_mem (hx : x ∈ V(G.walkable u)) (hy : y ∈ V(G.walkable u)) :
    ∃ W, G.IsWalk W ∧ W.first = x ∧ W.last = y := by
  obtain ⟨hx, W₁, hW₁, rfl, rfl⟩ := hx
  obtain ⟨hy, W₂, hW₂, hf, rfl⟩ := hy
  have hf' : W₁.reverse.last = W₂.first := by simp [hf]
  exact ⟨W₁.reverse.append W₂, hW₁.reverse.append hW₂ hf', by simp [hf'], by simp⟩

lemma mem_walkable_symm (hx : x ∈ V(G.walkable u)) : u ∈ V(G.walkable x) := by
  obtain ⟨hWl, W, hW, rfl, rfl⟩ := hx
  use hW.first_mem, W.reverse, hW.reverse, reverse_first, reverse_last

lemma mem_walkable_comm : x ∈ V(G.walkable u) ↔ u ∈ V(G.walkable x) :=
  ⟨mem_walkable_symm, mem_walkable_symm⟩

lemma mem_walkable_trans (huv : u ∈ V(G.walkable v)) (hvx : v ∈ V(G.walkable x)) :
    u ∈ V(G.walkable x) := by
  obtain ⟨h₁Wl, W₁, hW₁, rfl, rfl⟩ := huv
  obtain ⟨h₂Wf, W₂, hW₂, rfl, heq⟩ := hvx
  use hW₁.last_mem, W₂.append W₁, hW₂.append hW₁ heq, append_first_of_eq heq, append_last

lemma walkable_eq_walkable_of_mem (hx : x ∈ V(G.walkable u)) : G.walkable x = G.walkable u := by
  rw [walkable_isClosedSubgraph.vertexSet_inj walkable_isClosedSubgraph]
  ext y
  exact ⟨fun h => mem_walkable_trans h hx, fun h => mem_walkable_trans h (mem_walkable_symm hx)⟩

lemma IsClosedSubgraph.walkable_le_of_mem (hcl : H ≤c G) (hx : x ∈ V(H)) : G.walkable x ≤ H := by
  rw [walkable_isClosedSubgraph.le_iff_vertexSet_subset hcl]
  rintro y ⟨hy, W, hW, rfl, rfl⟩
  exact hW.isWalk_isClosedSubgraph hcl hx |>.last_mem

lemma walkable_isCompOf (hx : x ∈ V(G)) : (G.walkable x).IsCompOf G := by
  refine ⟨⟨walkable_isClosedSubgraph, ⟨x, mem_walkable hx⟩⟩, fun H' ⟨hH'cl, hxH'⟩ hH'leH => ?_⟩
  obtain ⟨y, hy⟩ := hxH'
  rw [← walkable_eq_walkable_of_mem <| vertexSet_mono hH'leH hy]
  exact hH'cl.walkable_le_of_mem hy

lemma exists_IsCompOf (hG : V(G).Nonempty) : ∃ (H : Graph α β), H.IsCompOf G :=
  ⟨_, walkable_isCompOf hG.choose_spec⟩

lemma IsCompOf.eq_walkable_of_mem_walkable (hHco : H.IsCompOf G) (hx : x ∈ V(H)) :
    H = G.walkable x := by
  rw [eq_comm]
  refine walkable_isClosedSubgraph.eq_of_le_isCompOf_of_vertexSet_not_disjoint hHco
    (hHco.isClosedSubgraph.walkable_le_of_mem hx) ?_
  rw [not_disjoint_iff]
  use x, mem_walkable <| vertexSet_mono hHco.le hx

lemma isCompOf_iff_exists_walkable : H.IsCompOf G ↔ ∃ x ∈ V(H), G.walkable x = H := by
  refine ⟨fun h => ?_, fun ⟨x, hx, h⟩ => ?_⟩
  · obtain ⟨y, hy⟩ := h.nonempty
    use y, hy
    exact (IsCompOf.eq_walkable_of_mem_walkable h hy).symm
  · subst H
    exact walkable_isCompOf <| mem_walkable_self_iff.mp hx

lemma exists_IsCompOf_vertex_mem (hx : x ∈ V(G)) : ∃ (H : Graph α β), H.IsCompOf G ∧ x ∈ V(H) :=
  ⟨_, walkable_isCompOf hx, by simpa⟩

lemma IsCompOf.le_of_mem_mem (hH₁ : H₁.IsCompOf G) (hH₂cl : H₂ ≤c G)
    (hx₁ : x ∈ V(H₁)) (hx₂ : x ∈ V(H₂)) : H₁ ≤ H₂ := by
  rw [hH₁.eq_walkable_of_mem_walkable hx₁]
  exact hH₂cl.walkable_le_of_mem hx₂



def Components (G : Graph α β) : Set (Graph α β) := {H | H.IsCompOf G}

@[simp]
lemma mem_components_iff_isCompOf : H ∈ G.Components ↔ H.IsCompOf G := by
  simp [Components]

@[simp]
lemma bot_not_mem_components (G : Graph α β) : ⊥ ∉ G.Components := by
  simp [Components]

lemma components_pairwise_stronglyDisjoint (G : Graph α β) :
    G.Components.Pairwise StronglyDisjoint :=
  fun _ hH₁ _ hH₂ hne => hH₁.stronglyDisjoint_of_ne hH₂ hne

lemma components_pairwise_disjoint (G : Graph α β) :
    G.Components.Pairwise Disjoint :=
  fun _ hH₁ _ hH₂ hne => (hH₁.stronglyDisjoint_of_ne hH₂ hne).disjoint

lemma components_pairwise_compatible (G : Graph α β) : G.Components.Pairwise Compatible :=
  fun _ hH₁ _ hH₂ hne => (hH₁.stronglyDisjoint_of_ne hH₂ hne).compatible

-- Graph is the union of its components
lemma eq_sUnion_components (G : Graph α β) : G = Graph.sUnion G.Components := by
  have h := sSup_atoms_eq_top (α := G.ClosedSubgraph)
  apply_fun Subtype.val at h
  rw [ClosedSubgraph.coe_sSup, eq_comm] at h
  convert h
  ext H
  simp only [mem_components_iff_isCompOf, ClosedSubgraph.isAtom_iff_isCompOf, mem_image,
    mem_setOf_eq, Subtype.exists, exists_and_left, exists_prop, exists_eq_right_right, iff_self_and]
  exact (·.isClosedSubgraph)

@[simp]
lemma components_eq_empty_iff : G.Components = ∅ ↔ G = ⊥ := by
  refine ⟨fun h => ?_, ?_⟩
  · rw [← vertexSet_eq_empty_iff, G.eq_sUnion_components]
    simp [h]
  rintro rfl
  ext H
  simp

lemma IsClosedSubgraph.components_subset_components (hcl : H ≤c G) :
    H.Components ⊆ G.Components := by
  rintro H' hH'
  rw [mem_components_iff_isCompOf] at hH' ⊢
  exact hH'.of_isClosedSubgraph hcl


def ClosedSubgraph.orderIso_set_components (G : Graph α β) :
    G.ClosedSubgraph ≃o Set {a : G.ClosedSubgraph | IsAtom a} :=
  orderIsoSetOfAtoms

-- def ComponentsPartition (G : Graph α β) : Partition (⊤ : G.ClosedSubgraph) :=
--   Partition.ofPairwiseDisjoint' G.components_pairwiseDisjoint_id (fun _ hH => hH.1)
--     sSup_atoms_eq_top.symm

@[simp]
lemma ClosedSubgraph.orderIso_set_components_sSup (H : G.ClosedSubgraph) :
    sSup (Subtype.val '' (ClosedSubgraph.orderIso_set_components G H)) = H :=
  orderIsoSetOfAtoms_sSup H

-- lemma ClosedSubgraph.orderIso_set_components_subset (H : G.ClosedSubgraph) :
--     Subtype.val '' (ClosedSubgraph.orderIso_set_components G H) ⊆ G.Components :=
--   fun _ ⟨H', _, h⟩ => h ▸ H'.prop

lemma ClosedSubgraph.le_of_mem_orderIso_set_components (H H' : G.ClosedSubgraph) :
    H' ∈ Subtype.val '' (ClosedSubgraph.orderIso_set_components G H) → H' ≤ H := by
  rintro ⟨H', hH'cl, rfl⟩
  rw [← orderIso_set_components_sSup H]
  exact CompleteLattice.le_sSup _ H'.val <| mem_image_of_mem Subtype.val hH'cl

-- lemma ClosedSubgraph.orderIso_set_components_apply (G : Graph α β) (H : G.ClosedSubgraph) :
--     Subtype.val '' (Subtype.val '' (ClosedSubgraph.orderIso_set_components G H)) =
--     Subtype.val '' H.val.Components := by
--   ext H'
--   simp only [le_eq_subset, mem_image, Subtype.exists, exists_and_right, exists_eq_right]
--   refine ⟨fun ⟨hH'Gcl, hH'Gco, hH'iso⟩ => ⟨hH'Gcl.of_le_of_le hH'iso H.prop.le, ?_⟩,
--     fun ⟨hH'Hcl, hH'Hco⟩ => ⟨hH'Hcl.trans H.prop, ?_, ?_⟩⟩
--   · rw [components_isAtom_iff] at hH'Gco ⊢
--     simp only [IsAtom, ne_eq, bot_isClosedSubgraph, Subtype.mk_eq_bot_iff, Subtype.forall,
--       Subtype.mk_lt_mk] at hH'Gco ⊢
--     exact ⟨hH'Gco.1, fun H₀ hH₀clH hH₀ltH' => hH'Gco.2 H₀ (hH₀clH.trans H.prop) hH₀ltH'⟩
--   · rw [components_isAtom_iff] at hH'Hco ⊢
--     simp only [IsAtom, ne_eq, bot_isClosedSubgraph, Subtype.mk_eq_bot_iff, Subtype.forall,
--       Subtype.mk_lt_mk] at hH'Hco ⊢
--     refine ⟨hH'Hco.1, fun H₀ hH₀clH hH₀ltH' => hH'Hco.2 H₀ ?_ hH₀ltH'⟩
--     exact hH₀clH.of_le_of_le (hH₀ltH'.le.trans hH'Hcl.le) H.prop.le
--   · simp?
--   all_goals sorry

-- lemma components_subset_components_iff (G H : Graph α β) :
--     Subtype.val '' G.Components ⊆ Subtype.val '' H.Components ↔ G ≤c H := by
--   refine ⟨fun h => ?_, fun h => ?_⟩
--   · rw [← components_sUnion G, ← components_sUnion H]
--     have : sSup G.Components ≤ sSup H.Components := by
--       rw [h]

--     have hle : H ≤c G := by
--       rw [← orderIso_set_components_sSup H]
--       exact CompleteLattice.le_sSup _ H' h
--   · have hle : H ≤c G := by
--       rw [← orderIso_set_components_sSup H]
--       exact CompleteLattice.le_sSup _ H' h

-- @[simp]
-- lemma ClosedSubgraph.mem_orderIso_set_components_iff (H : G.ClosedSubgraph)
-- {H' : G.ClosedSubgraph}:
--     H' ∈ Subtype.val '' (ClosedSubgraph.orderIso_set_components G H) ↔
-- H'.val.IsCompOf H.val := by
--   refine ⟨fun h => ?_, fun h => ?_⟩
--   · have hle : H' ≤ H := by
--       rw [← orderIso_set_components_sSup H]
--       exact CompleteLattice.le_sSup _ H' h






-- def vertexConnectedPartition (G : Graph α β) : Partition (V(G)) where
--   parts := {V(H.val) | H ∈ G.Components}
--   indep := by
--     rintro V ⟨H, hH, rfl⟩
--     simp only [sSup_eq_sUnion, disjoint_sUnion_right, mem_diff, mem_setOf_eq, mem_singleton_iff,
--       and_imp, forall_exists_index]
--     rintro W H₀ hH₀co rfl
--     have := not_imp_comm.mp <| G.components_pairwiseDisjoint_id.elim hH hH₀co
--     rwa [H.vertexSet_inj, eq_comm, (id H).disjoint_iff_vertexSet_disjoint] at this
--   bot_not_mem := by simp
--   sSup_eq' := by
--     simp only [sSup_eq_sUnion, sUnion_eq_biUnion, mem_setOf_eq, iUnion_exists, biUnion_and',
--       iUnion_iUnion_eq_right]
--     rw [← ClosedSubgraph.vertexSet_sSup, components_sUnion]
