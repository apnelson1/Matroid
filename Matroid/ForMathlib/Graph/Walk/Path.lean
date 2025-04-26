import Matroid.ForMathlib.Graph.Walk.Basic

variable {α β : Type*} {x y z u v : α} {e f : β} {G H : Graph α β}
  {w w₁ w₂ : WList α β} {S T : Set α}

open WList

namespace Graph

/-! ### Trails -/

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
  ⟨IsWalk.nil hx, by simp⟩

lemma nil_isPath (hx : x ∈ G.V) : G.IsPath (nil x) :=
  ⟨IsWalk.nil hx, by simp⟩

lemma nil_isWalkFrom (hx : x ∈ G.V) (hxS : x ∈ S) (hxT : x ∈ T) : G.IsWalkFrom S T (nil x) :=
  ⟨IsWalk.nil hx, hxS, hxT⟩

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
  simp only [isPath_iff, cons_isWalk_iff, cons_vx, List.nodup_cons, mem_vx]
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
      simp_all only [cons_isPath, cons_edge, List.nodup_cons, and_true, forall_const]
      exact fun he ↦ h.2.2 <| h.1.isWalk.vx_mem_of_edge_mem he h.2.1.inc_left

lemma Inc₂.walk_isPath (h : G.Inc₂ e u v) (hne : u ≠ v) : G.IsPath h.walk :=
  ⟨h.walk_isWalk, by simp [hne]⟩

lemma IsPath.reverse (hp : G.IsPath w) : G.IsPath w.reverse where
  isWalk := hp.isWalk.reverse
  nodup := by simp [hp.nodup]

lemma IsPathFrom.reverse (p : G.IsPathFrom S T w) : G.IsPathFrom T S w.reverse where
  isWalk := p.isWalk.reverse
  nodup := by simp [p.nodup]
  first_mem := by simp [p.last_mem]
  last_mem := by simp [p.first_mem]

@[simp]
lemma reverse_isPath_iff : G.IsPath (reverse w) ↔ G.IsPath w :=
  ⟨fun h ↦ by simpa using h.reverse, IsPath.reverse⟩

lemma IsWalk.dedup_isPath [DecidableEq α] (h : G.IsWalk w) : G.IsPath w.dedup :=
  ⟨h.dedup, w.dedup_vx_nodup⟩

end Graph
