import Matroid.ForMathlib.Graph.WList.Sublist
import Matroid.ForMathlib.Graph.Subgraph

/-
This file defined predicates stating that an abstract walk `w` is a walk/trail/path of a graph `G`.
-/

variable {α β : Type*} {x y z u v : α} {e f : β} {G : Graph α β}
  {w w₁ w₂ : WList α β} {S T : Set α}

namespace Graph

open WList List Set

/-- `G.IsWalk w` means that the abstract walk `w` is a walk of the graph `G`. -/
inductive IsWalk (G : Graph α β) : WList α β → Prop
  | nil (x) (hx : x ∈ G.V) : G.IsWalk (nil x)
  | cons' (x) (e) (w : WList α β) (h : G.Inc₂ e x w.first) (hw : G.IsWalk w) : G.IsWalk (cons x e w)

lemma nil_isWalk (hx : x ∈ G.V) : G.IsWalk (nil x) :=
  IsWalk.nil x hx

@[simp]
lemma nil_isWalk_iff : G.IsWalk (nil x) ↔ x ∈ G.V :=
  ⟨fun h ↦ by cases h with | _ => simp_all, nil_isWalk⟩

@[simp]
lemma cons_isWalk_iff : G.IsWalk (cons x e w) ↔ G.Inc₂ e x w.first ∧ G.IsWalk w :=
  ⟨fun h ↦ by cases h with | _ => simp_all, fun h ↦ h.2.cons' _ _ _ h.1⟩

lemma IsWalk.cons (h : G.IsWalk w) (hex : G.Inc₂ e x w.first) : G.IsWalk (cons x e w) :=
  cons' x e w hex h

@[simp]
lemma IsWalk.of_cons (hw : G.IsWalk (.cons x e w)) : G.IsWalk w := by
  simp_all

lemma IsWalk.vx_mem_of_mem (h : G.IsWalk w) (hmem : x ∈ w) : x ∈ G.V := by
  induction h with | nil => simp_all | cons' y e w h hw ih =>
    simp_all only [mem_cons_iff]
    exact hmem.elim (fun h' ↦ h' ▸ h.vx_mem_left) ih

lemma IsWalk.edge_mem_of_mem (h : G.IsWalk w) (hmem : e ∈ w.edge) : e ∈ G.E := by
  induction h with | nil => simp_all | cons' x f w h hw ih =>
    simp_all only [cons_edge, mem_cons]
    exact hmem.elim (fun h' ↦ h' ▸ h.edge_mem) ih

lemma IsWalk.vx_mem_of_edge_mem (h : G.IsWalk w) (he : e ∈ w.edge) (heu : G.Inc e u) : u ∈ w := by
  induction h with
  | nil => simp at he
  | cons' x f w h hw ih =>
    simp_all only [cons_edge, mem_cons, mem_cons_iff]
    refine he.elim ?_ fun h' ↦ .inr <| ih h'
    rintro rfl
    obtain rfl | rfl := heu.eq_or_eq_of_inc₂ h <;> simp

lemma IsWalk.vxSet_subset (hVd : G.IsWalk w) : w.vxSet ⊆ G.V :=
  fun _ ↦ hVd.vx_mem_of_mem

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

lemma IsWalk.subwalk (hw₂ : G.IsWalk w₂) (h : w₁.IsSublist w₂) : G.IsWalk w₁ := by
  induction h with
  | nil x w h => simp [hw₂.vx_mem_of_mem h]
  | cons x e w₁ w₂ h ih => exact ih hw₂.of_cons
  | cons₂ x e w₁ w₂ h h_eq ih =>
    rw [cons_isWalk_iff] at hw₂ ⊢
    rw [h_eq]
    exact ⟨hw₂.1, ih hw₂.2⟩

lemma IsWalk.prefix (hw : G.IsWalk w) (h : w₁.IsPrefix w) : G.IsWalk w₁ :=
  hw.subwalk h.isSublist

lemma IsWalk.suffix (hw : G.IsWalk w) (h : w₁.IsSuffix w) : G.IsWalk w₁ :=
  hw.subwalk h.isSublist

lemma IsWalk.append (h₁ : G.IsWalk w₁) (h₂ : G.IsWalk w₂) (h : w₁.last = w₂.first) :
  G.IsWalk (w₁ ++ w₂) := by
  induction h₁ with simp_all

lemma IsWalk.concat (h : G.IsWalk w) (he : G.Inc₂ e w.last x) : G.IsWalk (w.concat e x) := by
  induction h with
  | nil y hy =>
    simp only [nil_last] at he
    simp [he, he.vx_mem_right]
  | cons' => simp_all

lemma IsWalk.of_append_left (h : G.IsWalk (w₁ ++ w₂)) (h_eq : w₁.last = w₂.first) :
    G.IsWalk w₁ :=
  h.prefix <| isPrefix_append_right h_eq

lemma IsWalk.of_append_right (h : G.IsWalk (w₁ ++ w₂)) : G.IsWalk w₂ :=
  h.suffix <| isSuffix_append_left ..

lemma IsWalk.last_eq_first (h : G.IsWalk (w₁ ++ w₂)) (hw₁ : G.IsWalk w₁) (hne : w₁.Nonempty) :
    w₁.last = w₂.first := by
  induction hw₁ with
  | nil => simp_all
  | cons' x e w h' hw IH => cases w with
    | nil u =>
      simp only [nil_first, WList.cons_append, WList.nil_append, cons_isWalk_iff] at h' h
      exact h'.eq_of_inc₂ h.1
    | cons => simp_all

lemma IsWalk.reverse (hw : G.IsWalk w) : G.IsWalk w.reverse := by
  induction hw with
  | nil => simp_all
  | cons' x e w h hw ih =>
    simp_all only [WList.reverse_cons]
    apply ih.concat <| by simpa using h.symm

@[simp]
lemma isWalk_reverse_iff : G.IsWalk w.reverse ↔ G.IsWalk w :=
  ⟨fun h ↦ by simpa using h.reverse, IsWalk.reverse⟩

/-- `G.IsTrail w` means that `w` is a walk of `G` with no repeated edges. -/
@[mk_iff]
structure IsTrail (G : Graph α β) (W : WList α β) : Prop where
  isWalk : G.IsWalk W
  edge_nodup : W.edge.Nodup

@[simp] lemma IsTrail.isWalk_simp (h : G.IsTrail w) : G.IsWalk w := h.isWalk
@[simp] lemma IsTrail.edge_nodup_simp (h : G.IsTrail w) : w.edge.Nodup := h.edge_nodup
@[simp] lemma isTrail_simp (hVd : G.IsWalk w) (hed : w.edge.Nodup) :
    G.IsTrail w := IsTrail.mk hVd hed

/-- `G.IsPath w` means that `w` is a path of `G` with no repeated vertices. -/
@[mk_iff]
structure IsPath (G : Graph α β) (w : WList α β) : Prop where
  isWalk : G.IsWalk w
  nodup : w.vx.Nodup

-- @[simp] lemma IsPath.isWalk_simp (h : G.IsPath w) : G.IsWalk w := h.isWalk
-- @[simp] lemma IsPath.nodup_simp (h : G.IsPath w) : w.vx.Nodup := h.nodup
-- @[simp] lemma isPath_simp (hVd : G.IsWalk w) (hnodup : w.vx.Nodup) :
--     G.IsPath w := IsPath.mk hVd hnodup

@[mk_iff]
structure IsWalkFrom (G : Graph α β) (S T : Set α) (w : WList α β) : Prop where
  isWalk : G.IsWalk w
  first_mem : w.first ∈ S
  last_mem : w.last ∈ T

-- @[simp] lemma IsWalkFrom.isWalk_simp (h : G.IsWalkFrom S T w) : G.IsWalk w := h.isWalk
-- @[simp] lemma IsWalkFrom.first_mem_simp (h : G.IsWalkFrom S T w) : w.first ∈ S := h.first_mem
-- @[simp] lemma IsWalkFrom.last_mem_simp (h : G.IsWalkFrom S T w) : w.last ∈ T := h.last_mem
-- @[simp] lemma isWalkFrom_simp (hVd : G.IsWalk w) (hfirst : w.first ∈ S) (hlast : w.last ∈ T) :
--     G.IsWalkFrom S T w := IsWalkFrom.mk hVd hfirst hlast

@[mk_iff]
structure IsTrailFrom (G : Graph α β) (S T : Set α) (W : WList α β) : Prop extends
  G.IsTrail W, G.IsWalkFrom S T W

@[mk_iff]
structure IsPathFrom (G : Graph α β) (S T : Set α) (W : WList α β) : Prop extends
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

def Inc₂.walk (_h : G.Inc₂ e u v) : WList α β := cons u e (nil v)

namespace Inc₂

@[simp]
lemma walk_first (h : G.Inc₂ e u v): h.walk.first = u := rfl

@[simp]
lemma walk_last (h : G.Inc₂ e u v): h.walk.last = v := rfl

@[simp]
lemma walk_vx (h : G.Inc₂ e u v): h.walk.vx = [u, v] := rfl

lemma mem_walk_iff (h : G.Inc₂ e u v) (x : α) : x ∈ h.walk ↔ x = u ∨ x = v := by
  simp [walk]

@[simp]
lemma walk_vxSet (h : G.Inc₂ e u v): h.walk.vxSet = {u, v} := by
  simp [mem_walk_iff, Set.ext_iff]

@[simp]
lemma walk_edge (h : G.Inc₂ e u v): h.walk.edge = [e] := rfl

@[simp]
lemma walk_edgeSet (h : G.Inc₂ e u v): h.walk.edgeSet = {e} := by
  simp [edgeSet]

@[simp]
lemma walk_length (h : G.Inc₂ e u v): h.walk.length = 1 := rfl

@[simp]
lemma walk_isWalk (h : G.Inc₂ e u v) : G.IsWalk h.walk := by
  simp [walk, h, h.vx_mem_right]

lemma walk_isPath (h : G.Inc₂ e u v) (hne : u ≠ v) : G.IsPath h.walk :=
  ⟨h.walk_isWalk, by simp [hne]⟩

end Inc₂



variable {w₁ w₂ : WList α β}


-- lemma IsPath.prefix (hP : G.IsPath w) (hPf : w₁.IsPrefix w) : G.IsPath w₁ := by
--   refine ⟨hP.isWalk.prefix hPf, ?_⟩

  -- obtain ⟨w₂, heq, rfl⟩ := hPf.exists_eq_append
  -- exact append_left_isPath heq hP



-- lemma append_isWalkFrom (h : w₁.last = w₂.first) (h₁ : G.IsWalkFrom S T w₁)
--     (h₂ : G.IsWalkFrom T U w₂) : G.IsWalkFrom S U (w₁ ++ w₂) := by
--   obtain ⟨hw₁Vd, hw₁first, hw₁last⟩ := h₁
--   obtain ⟨hw₂Vd, hw₂first, hw₂last⟩ := h₂
--   refine ⟨?_, ?_, ?_⟩
--   · exact WList.append_isWalk h hw₁Vd hw₂Vd
--   · simpa [h]
--   · simpa



-- lemma append_isPath (h : w₁.last = w₂.first) (h₁ : G.IsPath w₁) (h₂ : G.IsPath w₂)
--     (hvxSet : w₁.vxSet ∩ w₂.vxSet ⊆ {w₁.last}) : G.IsPath (w₁ ++ w₂) where
--   isWalk := append_isWalk h h₁.isWalk h₂.isWalk
--   nodup := by
--     simp only [Set.subset_singleton_iff, Set.mem_inter_iff, mem_vxSet_iff, and_imp, append_vx,
--       nodup_append, h₁.nodup.sublist w₁.vx.dropLast_sublist, h₂.nodup, true_and] at hvxSet ⊢
--     rintro x hx₁ hx₂
--     obtain rfl := hvxSet x (List.mem_of_mem_dropLast hx₁) hx₂
--     /- This should be its own lemma -/
--     have aux {l : List α} (hl : l ≠ []) (hl' : l.Nodup) : l.getLast hl ∉ l.dropLast := by
--       rw [← dropLast_append_getLast hl, nodup_append] at hl'
--       obtain ⟨-, h'⟩ := by simpa using hl'
--       assumption
--     rw [last_eq_vx_getLast] at hx₁
--     apply aux (by simp) h₁.nodup hx₁

-- @[simp] lemma cons_isWalkFrom : G.IsWalkFrom S T (cons x e w) ↔
--     G.IsWalk w ∧ G.Inc₂ e x w.first ∧ x ∈ S ∧ w.last ∈ T := by
--   refine ⟨fun ⟨h, hS, hT⟩ ↦ ⟨?_, ?_, ?_, ?_⟩, fun ⟨hV, hS, hVd, hT⟩ ↦ ⟨?_, ?_, ?_⟩⟩
--   <;> simp_all only [cons_isWalk, cons_first, cons_last, and_self]


  -- induction w with
  -- | nil x => simp [reverse, hVd]
  -- | cons x e w ih =>
  --   simp only [cons_isWalk, reverse_cons] at hVd ⊢
  --   refine ValidIn.concat (ih hVd.2) ?_
  --   simp [hVd.1.symm]

lemma IsWalkFrom.reverse (h : G.IsWalkFrom S T w) : G.IsWalkFrom T S w.reverse where
  isWalk := h.isWalk.reverse
  first_mem := by simp [h.last_mem]
  last_mem := by simp [h.first_mem]

lemma IsPath.reverse (hp : G.IsPath w) : G.IsPath w.reverse where
  isWalk := hp.isWalk.reverse
  nodup := by simp [hp.nodup]

lemma IsPathFrom.reverse (p : G.IsPathFrom S T w) : G.IsPathFrom T S w.reverse where
  isWalk := p.isWalk.reverse
  nodup := by simp [p.nodup]
  first_mem := by simp [p.last_mem]
  last_mem := by simp [p.first_mem]

@[simp]
lemma reverse_isWalk_iff : G.IsWalk w.reverse ↔ G.IsWalk w :=
  ⟨fun h ↦ by simpa using h.reverse, IsWalk.reverse⟩

@[simp]
lemma reverse_isPath_iff : G.IsPath (reverse w) ↔ G.IsPath w :=
  ⟨fun h ↦ by simpa using h.reverse, IsPath.reverse⟩

lemma IsWalk.dedup [DecidableEq α] (h : G.IsWalk w) : G.IsWalk w.dedup :=
  h.subwalk w.dedup_isSublist

lemma IsWalk.dropLast (h : G.IsWalk w) : G.IsWalk w.dropLast :=
  h.prefix <| dropLast_isPrefix w

lemma IsWalk.dedup_isPath [DecidableEq α] (h : G.IsWalk w) : G.IsPath w.dedup :=
  ⟨h.dedup, w.dedup_vx_nodup⟩

-- lemma _root_.Graph.IsPath.IsSuffix (hPf : w₁.IsSuffix w) (hP : G.IsPath w) : G.IsPath w₁ := by
--   simpa using hP.reverse.IsPrefix <| reverse_isPrefix_reverse_iff.2 hPf

end Graph
