import Matroid.ForMathlib.Graph.Walk
import Matroid.ForMathlib.Graph.Subgraph
import Mathlib.Data.Set.Insert

open Set Function List Nat

variable {α β : Type*} {G H : Graph α β} {u v x y z : α} {e e' f g : β} {S S' T T' U V : Set α}
  {F F' R R': Set β}

namespace Graph


/-- Connectedness of vertices-/
def VxConnected (G : Graph α β) : α → α → Prop :=
    Relation.TransGen (fun x y ↦ G.Adj x y ∨ (x = y ∧ x ∈ G.V))

lemma VxConnected.refl (h : v ∈ G.V) : G.VxConnected v v := by
  rw [VxConnected, Relation.transGen_iff]
  simp [h]

lemma VxConnected.trans (hxy : G.VxConnected x y) (hyz : G.VxConnected y z) : G.VxConnected x z :=
  Relation.TransGen.trans hxy hyz

lemma VxConnected.symm (hxy : G.VxConnected x y) : G.VxConnected y x := by
  rw [VxConnected, Relation.transGen_swap]
  rw [VxConnected] at hxy
  convert hxy using 4 with x y
  · rw [adj_comm]
  aesop

lemma VxConnected.mem_left (hxy : G.VxConnected x y) : x ∈ G.V := by
  induction hxy with
  | single h => exact h.elim Adj.mem_left And.right
  | tail _ _ h => exact h

lemma VxConnected.mem_right (hxy : G.VxConnected x y) : y ∈ G.V :=
  hxy.symm.mem_left

@[simp]
lemma vxConnected_self : G.VxConnected x x ↔ x ∈ G.V :=
  ⟨VxConnected.mem_left, VxConnected.refl⟩

lemma Adj.vxConnected (h : G.Adj x y) : G.VxConnected x y := by
  rw [VxConnected, Relation.transGen_iff]
  simp [h]

lemma Inc₂.vxConnected (h : G.Inc₂ e x y) : G.VxConnected x y :=
  h.adj.vxConnected

lemma Walk.ValidIn.vxConnected {w : Walk α β} (hw : w.ValidIn G) :
    G.VxConnected w.first w.last := by
  induction w with
  | nil u =>
  apply VxConnected.refl
  simpa using hw
  | cons u e W ih =>
  simp only [cons_first, cons_last]
  simp only [cons_validIn] at hw
  exact hw.1.vxConnected.trans <| ih hw.2

lemma VxConnected.exists_walk_validIn (h : G.VxConnected x y) :
    ∃ (w : Walk α β), w.ValidIn G ∧ w.first = x ∧ w.last = y := by
  rw [VxConnected] at h
  induction h using Relation.TransGen.head_induction_on with
  | @base a h =>
    obtain ⟨e, he⟩ | ⟨rfl, h⟩ := h
    · exact ⟨he.walk, by simp⟩
    exact ⟨Walk.nil a, by simp [h]⟩
  | @ih u v h₁ h₂ h₃ =>
  obtain ⟨w, hw, rfl, rfl⟩ := h₃
  obtain ⟨e, he⟩ | ⟨rfl, h⟩ := h₁
  · exact ⟨Walk.cons u e w, by simp [he, hw]⟩
  exact ⟨w, hw, rfl, rfl⟩

lemma vxConnected_iff_exists_walk :
    G.VxConnected x y ↔ ∃ (w : Walk α β), w.ValidIn G ∧ w.first = x ∧ w.last = y := by
  refine ⟨VxConnected.exists_walk_validIn, ?_⟩
  rintro ⟨w, hw, rfl, rfl⟩
  exact hw.vxConnected

@[mk_iff]
structure Connected (G : Graph α β) : Prop where
  nonempty : G.V.Nonempty
  forall_vxConnected : ∀ ⦃x y⦄, x ∈ G.V → y ∈ G.V → G.VxConnected x y

lemma exists_of_not_connected (h : ¬ G.Connected) (hne : G.V.Nonempty) :
    ∃ X ⊂ G.V, X.Nonempty ∧ ∀ ⦃u v⦄, u ∈ X → G.Adj u v → v ∈ X := by
  simp only [connected_iff, hne, true_and, not_forall, Classical.not_imp,
    exists_prop, exists_and_left] at h
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  refine ⟨{z | G.VxConnected x z}, ?_, ⟨x, by simpa⟩, fun u v (h : G.VxConnected x u) huv ↦ ?_⟩
  · exact HasSubset.Subset.ssubset_of_mem_not_mem
      (fun z hz ↦ VxConnected.mem_right hz) hy (by simpa)
  exact h.trans huv.vxConnected




-- structure VxSeparation (G : Graph α β) (k : ℕ) where
--   left : Set α
--   right : Set α
--   union_eq : left ∪ right = G.V
--   disjoint : Disjoint left right


-- lemma exists_partition_of_not_connected {G : Graph α β} (h : ¬ G.Connected) :
--     ∃ X Y, X.Nonempty ∧ Y.Nonempty ∧



-- section Connected

-- @[simp]
-- def reflAdj (G : Graph α β) (x y : α) :=
--   G.Adj x y ∨ x = y ∧ x ∈ G.V

-- lemma reflAdj.of_vxMem (h : x ∈ G.V) : G.reflAdj x x := by
--   simp only [reflAdj, h, and_self, or_true]

-- @[simp]
-- lemma reflAdj.refl (h : x ∈ G.V) : G.reflAdj x x := reflAdj.of_vxMem h

-- lemma reflAdj.symm (h : G.reflAdj x y) : G.reflAdj y x := by
--   apply h.imp
--   · exact fun h ↦ h.symm
--   · rintro ⟨rfl, hx⟩
--     exact ⟨rfl, hx⟩

-- lemma reflAdj.comm : G.reflAdj x y ↔ G.reflAdj y x := by
--   refine ⟨reflAdj.symm, reflAdj.symm⟩

-- lemma Inc.reflAdj_of_inc (hx : G.Inc e x) (hy : G.Inc e y) : G.reflAdj x y := by
--   by_cases hxy : x = y
--   · subst y
--     right
--     exact ⟨rfl, hx.vx_mem⟩
--   · left
--     use e
--     rw [inc₂_iff_inc_and_loop]
--     use hx, hy, fun h ↦ (hxy h).elim

-- @[simp]
-- lemma reflAdj.mem_left (h : G.reflAdj x y) : x ∈ G.V := by
--   apply h.elim
--   · exact fun a ↦ a.mem_left
--   · tauto

-- @[simp]
-- lemma reflAdj.mem_right (h : G.reflAdj x y) : y ∈ G.V := by
--   rw [reflAdj.comm] at h
--   exact h.mem_left

-- @[simp]
-- lemma Inc₂.reflAdj (h : G.Inc₂ e x y) : G.reflAdj x y := by
--   left
--   use e

-- @[simp]
-- lemma Adj.reflAdj (h : G.Adj x y) : G.reflAdj x y := by
--   left
--   exact h

-- lemma reflAdj.Adj_of_ne (h : G.reflAdj x y) (hne : x ≠ y) : G.Adj x y := by
--   obtain ⟨e, h⟩ | ⟨rfl, hx⟩ := h
--   · use e
--   · contradiction

-- @[simp]
-- lemma reflAdj.Adj_iff_ne (hne : x ≠ y) : G.reflAdj x y ↔ G.Adj x y :=
--   ⟨fun h => h.Adj_of_ne hne, fun h => h.reflAdj⟩

-- lemma reflAdj.le (h : G.reflAdj u v) (hle : G ≤ H) : H.reflAdj u v := by
--   obtain hadj | ⟨rfl, hu⟩ := h
--   · left
--     exact hadj.le hle
--   · right
--     simp only [vx_subset_of_le hle hu, and_self]


-- def Connected (G : Graph α β) := Relation.TransGen G.reflAdj

-- @[simp]
-- lemma Inc₂.connected (h : G.Inc₂ e x y) : G.Connected x y :=
--   Relation.TransGen.single h.reflAdj

-- @[simp]
-- lemma Adj.connected (h : G.Adj x y) : G.Connected x y := Relation.TransGen.single h.reflAdj

-- @[simp]
-- lemma reflAdj.connected (h : G.reflAdj x y) : G.Connected x y := Relation.TransGen.single h

-- lemma connected_self (hx : x ∈ G.V) : G.Connected x x :=
--   Relation.TransGen.single <| reflAdj.of_vxMem hx

-- lemma Inc.connected_of_inc (hx : G.Inc e x) (hy : G.Inc e y) : G.Connected x y :=
--   reflAdj.connected (hx.reflAdj_of_inc hy)

-- lemma Connected.comm : G.Connected x y ↔ G.Connected y x := by
--   unfold Connected
--   rw [Relation.transGen_swap]
--   congr! 1
--   ext
--   exact reflAdj.comm

-- @[simp]
-- lemma Connected.refl (hx : x ∈ G.V) : G.Connected x x :=
--   connected_self hx

-- @[simp]
-- lemma Connected.exists_connected (hx : x ∈ G.V) : ∃ y, G.Connected x y := by
--   use x, Connected.refl hx

-- lemma Connected.symm (h : G.Connected x y) : G.Connected y x := by
--   rwa [Connected.comm]

-- instance : IsSymm α (G.Connected) := ⟨fun _ _ ↦ Connected.symm⟩

-- lemma Connected.trans (hxy : G.Connected x y) (hyz : G.Connected y z) :
--     G.Connected x z := Relation.TransGen.trans hxy hyz

-- instance : IsTrans α (G.Connected) := ⟨fun _ _ _ ↦ Connected.trans⟩

-- @[simp]
-- lemma Connected.mem_left (hconn : G.Connected x y) : x ∈ G.V := by
--   simp only [Connected, Relation.TransGen.head'_iff, not_exists, not_and, not_or] at hconn
--   obtain ⟨a, hradj, hTG⟩ := hconn
--   exact hradj.mem_left

-- @[simp]
-- lemma Connected.mem_right (hconn : G.Connected x y) : y ∈ G.V := by
--   rw [Connected.comm] at hconn
--   exact hconn.mem_left

-- @[simp]
-- lemma not_connected_of_not_mem (h : x ∉ G.V) : ¬G.Connected x y := by
--   contrapose! h
--   exact h.mem_left

-- @[simp]
-- lemma not_connected_of_not_mem' (h : y ∉ G.V) : ¬G.Connected x y := by
--   rw [Connected.comm]
--   exact not_connected_of_not_mem h

-- @[simp]
-- lemma Connected.refl_iff : G.Connected x x ↔ x ∈ G.V := by
--   refine ⟨?_, Connected.refl⟩
--   rintro h
--   exact h.mem_left

-- lemma Connected.le (h : G.Connected u v) (hle : G ≤ H) : H.Connected u v := by
--   induction h with
--   | single huv => exact Relation.TransGen.single (huv.le hle)
--   | tail huv h ih => exact Relation.TransGen.tail ih (h.le hle)

-- class Conn (G : Graph α β) : Prop where
--   all_conn : ∃ x, ∀ y ∈ G.V, G.Connected x y

-- open Partition

-- def ConnectedPartition (G : Graph α β) : Partition (Set α) := Partition.ofRel (G.Connected)

-- def Component (G : Graph α β) (v : α) := {u | G.Connected v u}

-- def ComponentSets (G : Graph α β) (V : Set α) := {Component G u | u ∈ V}

-- @[simp]
-- lemma ComponentPartition.supp : G.ConnectedPartition.supp = G.V := by
--   simp [ConnectedPartition]

-- @[simp]
-- lemma set_spec_connected_comm : {x | G.Connected x y} = {x | G.Connected y x} := by
--   simp_rw [Connected.comm]

-- @[simp] lemma set_spec_connected_eq_componentSet : {x | G.Connected y x} = G.Component y := rfl

-- @[simp]
-- lemma Component.empty : G.Component x = ∅ ↔ x ∉ G.V := by
--   constructor
--   · intro h hx
--     rw [← mem_empty_iff_false, ← h]
--     exact Connected.refl hx
--   · intro h
--     ext y
--     simp [Component, h]

-- @[simp]
-- lemma Component.eq (hx : x ∈ G.V) : G.Component x = G.Component y ↔ G.Connected x y :=
--   (rel_iff_eqv_class_eq_left (Connected.refl hx)).symm

-- @[simp]
-- lemma Component.eq' (hy : y ∈ G.V) : G.Component x = G.Component y ↔ G.Connected x y := by
--   rw [eq_comm, Connected.comm, eq hy]

-- @[simp]
-- lemma Component.mem_partition : G.Component x ∈ G.ConnectedPartition ↔ x ∈ G.V := by
--   refine mem_ofRel_iff.trans ?_
--   simp +contextual only [Connected.refl_iff, set_spec_connected_eq_componentSet, iff_def,
--     forall_exists_index, and_imp, eq', eq]
--   refine ⟨fun y hy hconn ↦ hconn.mem_left, fun h ↦ ?_⟩
--   use x, h, Connected.refl h

-- @[simp] lemma Component.mem : y ∈ G.Component x ↔ G.Connected x y := by rfl

-- lemma Component.mem' : y ∈ G.Component x ↔ G.Connected y x := by
--   rw [Connected.comm, Component.mem]

-- -- @[simp] lemma ComponentSet.self_mem : x ∈ G.ComponentSet x ↔ x ∈ G.V := by simp

-- @[simp]
-- lemma ComponentSets.mem (hx : x ∈ G.V) :
--     G.Component x ∈ G.ComponentSets T ↔ ∃ y ∈ T, G.Connected x y := by
--   simp only [ComponentSets, mem_setOf_eq, hx, Component.eq']
--   simp_rw [Connected.comm]

-- lemma ComponentSets.componentSet (hx : x ∈ G.V) :
--     G.ComponentSets (G.Component x) = {G.Component x} := by
--   ext S
--   simp +contextual only [mem_singleton_iff, iff_def, hx, mem, Component.mem, and_self,
--     Connected.exists_connected, implies_true, and_true]
--   rintro ⟨y, hy, rfl⟩
--   simpa [hx, Connected.comm] using hy

-- lemma ConnectedPartition.le (hle : G ≤ H) : G.ConnectedPartition ≤ H.ConnectedPartition := by
--   simpa [ConnectedPartition] using fun u v ↦ (Connected.le · hle)

-- @[simp]
-- lemma ConnectedPartition.Rel : G.ConnectedPartition.Rel = G.Connected := by
--   unfold ConnectedPartition
--   rw [rel_ofRel_eq]

-- def SetConnected (G : Graph α β) (S T : Set α) : Prop := ∃ s ∈ S, ∃ t ∈ T, G.Connected s t

-- namespace SetConnected
-- variable {G : Graph α β} {S S' T T' U V : Set α}

-- lemma refl (h : ∃ x ∈ S, x ∈ G.V) : G.SetConnected S S := by
--   obtain ⟨x, hxS, hxV⟩ := h
--   use x, hxS, x, hxS, Connected.refl hxV

-- lemma symm (h : G.SetConnected S T) : G.SetConnected T S := by
--   obtain ⟨s, hs, t, ht, h⟩ := h
--   exact ⟨t, ht, s, hs, h.symm⟩

-- lemma comm : G.SetConnected S T ↔ G.SetConnected T S := ⟨SetConnected.symm, SetConnected.symm⟩

-- lemma left_subset (h : G.SetConnected S T) (hS : S ⊆ S') : G.SetConnected S' T := by
--   obtain ⟨s, hs, t, ht, h⟩ := h
--   use s, hS hs, t, ht

-- lemma right_subset (h : G.SetConnected S T) (hT : T ⊆ T') : G.SetConnected S T' := by
--   rw [SetConnected.comm] at h ⊢
--   exact h.left_subset hT

-- lemma subset (h : G.SetConnected S T) (hS : S ⊆ S') (hT : T ⊆ T') : G.SetConnected S' T' :=
--   (h.left_subset hS).right_subset hT

-- lemma left_supported : G.SetConnected S T ↔ G.SetConnected (S ∩ G.V) T := by
--   constructor
--   · rintro ⟨s, hsS, t, htT, h⟩
--     use s, ⟨hsS, h.mem_left⟩, t, htT
--   · rintro ⟨s, ⟨hsS, hs⟩, t, htT, h⟩
--     use s, hsS, t, htT

-- lemma right_supported : G.SetConnected S T ↔ G.SetConnected S (T ∩ G.V) := by
--   rw [comm, left_supported, comm]

-- lemma supported : G.SetConnected S T ↔ G.SetConnected (S ∩ G.V) (T ∩ G.V) := by
--   rw [left_supported, right_supported]

-- lemma le (h : G.SetConnected S T) (hle : G ≤ H) : H.SetConnected S T := by
--   obtain ⟨s, hs, t, ht, h⟩ := h
--   exact ⟨s, hs, t, ht, h.le hle⟩

-- @[simp]
-- lemma empty_source : ¬ G.SetConnected ∅ T := by
--   rintro ⟨s, hs, t, ht, h⟩
--   simp at hs

-- @[simp]
-- lemma empty_target : ¬ G.SetConnected S ∅ := by
--   rw [SetConnected.comm]
--   exact empty_source

-- @[simp]
-- lemma nonempty_inter (h : (S ∩ T ∩ G.V).Nonempty) : G.SetConnected S T := by
--   obtain ⟨x, ⟨hxS, hxT⟩, hx⟩ := h
--   use x, hxS, x, hxT, Connected.refl hx

-- lemma exists_mem_left (h : G.SetConnected S T) : ∃ x ∈ S, x ∈ G.V := by
--   obtain ⟨s, hs, t, ht, h⟩ := h
--   exact ⟨s, hs, h.mem_left⟩

-- lemma exists_mem_right (h : G.SetConnected S T) : ∃ x ∈ T, x ∈ G.V := by
--   rw [SetConnected.comm] at h
--   exact exists_mem_left h

-- end SetConnected
