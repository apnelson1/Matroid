import Matroid.ForMathlib.Graph.Walk.Defs

/-
This file defined predicates stating that an abstract walk `w` is a walk/trail/path of a graph `G`.
-/

variable {α β : Type*} {x y z u v : α} {e f : β} {G : Graph α β} {w : Graph.Walk α β} {S T : Set α}

namespace Graph

open Graph.Walk List Set

/-- `G.IsWalk w` means that the abstract walk `w` is a walk of the graph `G`. -/
inductive IsWalk (G : Graph α β) : Walk α β → Prop
  | nil (x) (hx : x ∈ G.V) : G.IsWalk (nil x)
  | cons (x) (e) (w : Walk α β) (h : G.Inc₂ e x w.first) (hw : G.IsWalk w) : G.IsWalk (cons x e w)

lemma nil_isWalk (hx : x ∈ G.V) : G.IsWalk (nil x) :=
  IsWalk.nil x hx

@[simp]
lemma nil_isWalk_iff : G.IsWalk (nil x) ↔ x ∈ G.V :=
  ⟨fun h ↦ by cases h with | _ => simp_all, nil_isWalk⟩

@[simp]
lemma cons_isWalk_iff : G.IsWalk (cons x e w) ↔ G.Inc₂ e x w.first ∧ G.IsWalk w :=
  ⟨fun h ↦ by cases h with | _ => simp_all, fun h ↦ h.2.cons _ _ _ h.1⟩

@[simp]
lemma IsWalk.of_cons (hw : G.IsWalk (.cons x e w)) : G.IsWalk w := by
  simp_all

lemma IsWalk.vx_mem_of_mem (h : G.IsWalk w) (hmem : x ∈ w) : x ∈ G.V := by
  induction w with
  | nil => simp_all
  | cons u e w ih =>
    obtain rfl | hxw := mem_cons_iff.1 hmem
    · simp only [cons_isWalk_iff] at h
      exact h.1.vx_mem_left
    exact ih h.of_cons hxw

lemma IsWalk.vx_mem_of_edge_mem (h : G.IsWalk w) (he : e ∈ w.edge) (heu : G.Inc e u) : u ∈ w := by
  induction h with
  | nil => simp at he
  | cons x f w h hw ih =>
    simp_all only [cons_edge, mem_cons, mem_cons_iff]
    obtain rfl | hew := he
    · obtain rfl | rfl := heu.eq_or_eq_of_inc₂ h <;> simp
    simp_all

lemma IsWalk.vxSet_subset (hVd : G.IsWalk w) : w.vxSet ⊆ G.V :=
  fun _ ↦ hVd.vx_mem_of_mem

lemma IsWalk.edge_mem_of_mem (h : G.IsWalk w) (hmem : e ∈ w.edge) : e ∈ G.E := by
  induction w with
  | nil u => simp_all
  | cons x f w ih =>
    simp only [cons_isWalk_iff] at h
    obtain (rfl : e = f) | hmem := by simpa using hmem
    · exact h.1.edge_mem
    exact ih h.2 hmem

lemma IsWalk.edgeSet_subset (h : G.IsWalk w) : w.edgeSet ⊆ G.E := fun _ ↦ h.edge_mem_of_mem

lemma IsWalk.mem_of_mem_edge_of_inc (hw : G.IsWalk w) (he : e ∈ w.edge) (h : G.Inc e u) :
    u ∈ w := by
  induction w with
  | nil x => simp at he
  | cons x e' w ih =>
    simp_all only [forall_const, cons_edge, mem_cons, mem_cons_iff, cons_isWalk_iff]
    obtain rfl | he := he
    · obtain rfl | rfl := h.eq_or_eq_of_inc₂ hw.1 <;> simp
    exact .inr (ih he)

/-- `G.IsTrail w` means that `w` is a walk of `G` with no repeated edges. -/
@[mk_iff]
structure IsTrail (G : Graph α β) (W : Walk α β) : Prop where
  isWalk : G.IsWalk W
  edge_nodup : W.edge.Nodup

@[simp] lemma IsTrail.isWalk_simp (h : G.IsTrail w) : G.IsWalk w := h.isWalk
@[simp] lemma IsTrail.edge_nodup_simp (h : G.IsTrail w) : w.edge.Nodup := h.edge_nodup
@[simp] lemma isTrail_simp (hVd : G.IsWalk w) (hed : w.edge.Nodup) :
    G.IsTrail w := IsTrail.mk hVd hed

/-- `G.IsPath w` means that `w` is a path of `G` with no repeated vertices. -/
@[mk_iff]
structure IsPath (G : Graph α β) (w : Walk α β) : Prop where
  isWalk : G.IsWalk w
  nodup : w.vx.Nodup

-- @[simp] lemma IsPath.isWalk_simp (h : G.IsPath w) : G.IsWalk w := h.isWalk
-- @[simp] lemma IsPath.nodup_simp (h : G.IsPath w) : w.vx.Nodup := h.nodup
-- @[simp] lemma isPath_simp (hVd : G.IsWalk w) (hnodup : w.vx.Nodup) :
--     G.IsPath w := IsPath.mk hVd hnodup

@[mk_iff]
structure IsWalkFrom (G : Graph α β) (S T : Set α) (w : Walk α β) : Prop where
  isWalk : G.IsWalk w
  first_mem : w.first ∈ S
  last_mem : w.last ∈ T

-- @[simp] lemma IsWalkFrom.isWalk_simp (h : G.IsWalkFrom S T w) : G.IsWalk w := h.isWalk
-- @[simp] lemma IsWalkFrom.first_mem_simp (h : G.IsWalkFrom S T w) : w.first ∈ S := h.first_mem
-- @[simp] lemma IsWalkFrom.last_mem_simp (h : G.IsWalkFrom S T w) : w.last ∈ T := h.last_mem
-- @[simp] lemma isWalkFrom_simp (hVd : G.IsWalk w) (hfirst : w.first ∈ S) (hlast : w.last ∈ T) :
--     G.IsWalkFrom S T w := IsWalkFrom.mk hVd hfirst hlast

@[mk_iff]
structure IsTrailFrom (G : Graph α β) (S T : Set α) (W : Walk α β) : Prop extends
  G.IsTrail W, G.IsWalkFrom S T W

@[mk_iff]
structure IsPathFrom (G : Graph α β) (S T : Set α) (W : Walk α β) : Prop extends
  G.IsPath W, G.IsWalkFrom S T W

lemma IsTrailFrom.isTrail (h : G.IsTrailFrom S T w) : G.IsTrail w where
  isWalk := h.isWalk
  edge_nodup := h.edge_nodup

lemma IsTrailFrom.isWalkFrom (h : G.IsTrailFrom S T w) : G.IsWalkFrom S T w where
  isWalk := h.isWalk
  first_mem := h.first_mem
  last_mem := h.last_mem

lemma IsPathFrom.isPath (h : G.IsPathFrom S T w) : G.IsPath w where
  isWalk := h.isWalk
  nodup := h.nodup

lemma IsPathFrom.isWalkFrom (h : G.IsPathFrom S T w) : G.IsWalkFrom S T w where
  isWalk := h.isWalk
  first_mem := h.first_mem
  last_mem := h.last_mem

-- lemma IsPathFrom.isTrailFrom (h : G.IsPathFrom S T w) : G.IsTrailFrom S T w where
--   isWalk := h.isWalk
--   edge_nodup := h.isPath.isTrail.edge_nodup
--   first_mem := h.first_mem
--   last_mem := h.last_mem

lemma IsWalk.isTrail (hVd : G.IsWalk w) (hedge : w.edge.Nodup) : G.IsTrail w := ⟨hVd, hedge⟩

lemma IsWalk.isPath (hVd : G.IsWalk w) (hvx : w.vx.Nodup) : G.IsPath w := ⟨hVd, hvx⟩

lemma IsWalk.isWalkFrom (hVd : G.IsWalk w) (hfirst : w.first ∈ S) (hlast : w.last ∈ T) :
    G.IsWalkFrom S T w := ⟨hVd, hfirst, hlast⟩

lemma IsWalk.isTrailFrom (hVd : G.IsWalk w) (hedge : w.edge.Nodup) (hfirst : w.first ∈ S)
    (hlast : w.last ∈ T) : G.IsTrailFrom S T w := ⟨⟨hVd, hedge⟩, hfirst, hlast⟩

lemma IsWalk.isPathFrom (hVd : G.IsWalk w) (hvx : w.vx.Nodup) (hfirst : w.first ∈ S)
    (hlast : w.last ∈ T) : G.IsPathFrom S T w := ⟨⟨hVd, hvx⟩, hfirst, hlast⟩

lemma IsTrail.isPath (hT : G.IsTrail w) (hvx : w.vx.Nodup) : G.IsPath w := ⟨hT.isWalk, hvx⟩

lemma IsTrail.isTrailFrom (hT : G.IsTrail w) (hfirst : w.first ∈ S) (hlast : w.last ∈ T) :
    G.IsTrailFrom S T w := ⟨hT, hfirst, hlast⟩

lemma IsTrail.isPathFrom (hT : G.IsTrail w) (hvx : w.vx.Nodup) (hfirst : w.first ∈ S)
    (hlast : w.last ∈ T) : G.IsPathFrom S T w := ⟨⟨hT.isWalk, hvx⟩, hfirst, hlast⟩

lemma IsPath.isPathFrom (hP : G.IsPath w) (hfirst : w.first ∈ S) (hlast : w.last ∈ T) :
    G.IsPathFrom S T w := ⟨hP, hfirst, hlast⟩

lemma nil_isTrail (hx : x ∈ G.V) : G.IsTrail (nil x) :=
  ⟨nil_isWalk hx, by simp⟩

lemma nil_isPath (hx : x ∈ G.V) : G.IsPath (nil x) :=
  ⟨nil_isWalk hx, by simp⟩

lemma nil_isWalkFrom (hx : x ∈ G.V) (hxS : x ∈ S) (hxT : x ∈ T) : G.IsWalkFrom S T (nil x) :=
  ⟨nil_isWalk hx, hxS, hxT⟩

@[simp] lemma nil_isWalkFrom_iff : G.IsWalkFrom S T (nil x) ↔ x ∈ G.V ∧ x ∈ S ∧ x ∈ T := by
  simp [isWalkFrom_iff]

@[simp] lemma nil_isTrail_iff : G.IsTrail (nil x) ↔ x ∈ G.V := by
  simp [isTrail_iff]

@[simp] lemma nil_isPath_iff : G.IsPath (nil x) ↔ x ∈ G.V := by
  simp [isPath_iff]

@[simp] lemma cons_isTrail : G.IsTrail (cons x e w) ↔
    G.IsTrail w ∧ G.Inc₂ e x w.first ∧ e ∉ w.edge := by
  simp only [isTrail_iff, cons_isWalk_iff, cons_edge, List.nodup_cons]
  tauto

@[simp] lemma cons_isPath : G.IsPath (cons x e w) ↔ G.IsPath w ∧ G.Inc₂ e x w.first ∧ x ∉ w := by
  simp only [isPath_iff, cons_isWalk_iff, cons_vx, nodup_cons, mem_vx]
  tauto

@[simp]
lemma cons_isTrailFrom : G.IsTrailFrom S T (cons x e w) ↔
    G.IsTrail w ∧ G.Inc₂ e x w.first ∧ e ∉ w.edge ∧ x ∈ S ∧ w.last ∈ T := by
  simp [isTrailFrom_iff, and_assoc]

@[simp]
lemma cons_isPathFrom : G.IsPathFrom S T (cons x e w) ↔
    G.IsPath w ∧ G.Inc₂ e x w.first ∧ x ∉ w ∧ x ∈ S ∧ w.last ∈ T := by
  simp [isPathFrom_iff, and_assoc]

@[simp]
lemma IsTrail.of_cons (h : G.IsTrail (cons x e w)) : G.IsTrail w := by
  rw [cons_isTrail] at h
  exact h.1

@[simp]
lemma IsPath.of_cons (h : G.IsPath (cons x e w)) : G.IsPath w := by
  rw [cons_isPath] at h
  exact h.1

@[simp]
lemma nil_isTrailFrom : G.IsTrailFrom S T (nil x) ↔ x ∈ G.V ∧ x ∈ S ∧ x ∈ T := by
  simp [isTrailFrom_iff]

@[simp] lemma nil_isPathFrom : G.IsPathFrom S T (nil x) ↔ x ∈ G.V ∧ x ∈ S ∧ x ∈ T := by
  simp [isPathFrom_iff]

lemma IsPath.isTrail (h : G.IsPath w) : G.IsTrail w where
  isWalk := h.1
  edge_nodup := by
    induction w with
    | nil u => simp
    | cons u e w ih =>
      simp_all only [cons_isPath, cons_edge, nodup_cons, and_true, forall_const]
      exact fun he ↦ h.2.2 <| h.1.isWalk.vx_mem_of_edge_mem he h.2.1.inc_left

def Inc₂.walk (_h : G.Inc₂ e u v) : Walk α β := cons u e (nil v)

namespace Inc₂

@[simp] lemma walk_first (h : G.Inc₂ e u v): h.walk.first = u := rfl

@[simp] lemma walk_last (h : G.Inc₂ e u v): h.walk.last = v := rfl

@[simp] lemma walk_vx (h : G.Inc₂ e u v): h.walk.vx = [u, v] := rfl

@[simp] lemma mem_walk_iff (h : G.Inc₂ e u v) (x : α) : x ∈ h.walk ↔ x = u ∨ x = v := by
  simp [walk]

@[simp] lemma walk_vxSet (h : G.Inc₂ e u v): h.walk.vxSet = {u, v} := by
  simp only [vxSet, mem_walk_iff]
  rfl

@[simp] lemma walk_edge (h : G.Inc₂ e u v): h.walk.edge = [e] := rfl

@[simp] lemma walk_edgeSet (h : G.Inc₂ e u v): h.walk.edgeSet = {e} := by simp [edgeSet]

@[simp] lemma walk_length (h : G.Inc₂ e u v): h.walk.length = 1 := rfl

@[simp]
lemma walk_isWalk (h : G.Inc₂ e u v) : G.IsWalk h.walk := by
  simp [walk, h, h.vx_mem_right]

lemma walk_isPath (h : G.Inc₂ e u v) (hne : u ≠ v) : G.IsPath h.walk :=
  ⟨h.walk_isWalk, by simp [hne]⟩

end Inc₂








-- @[simp] lemma cons_isWalkFrom : G.IsWalkFrom S T (cons x e w) ↔
--     G.IsWalk w ∧ G.Inc₂ e x w.first ∧ x ∈ S ∧ w.last ∈ T := by
--   refine ⟨fun ⟨h, hS, hT⟩ ↦ ⟨?_, ?_, ?_, ?_⟩, fun ⟨hV, hS, hVd, hT⟩ ↦ ⟨?_, ?_, ?_⟩⟩
--   <;> simp_all only [cons_isWalk, cons_first, cons_last, and_self]


end Graph
