import Matroid.ForMathlib.Graph.Walk.Basic

variable {α β : Type*} {x y z u v : α} {e f : β} {G H : Graph α β}
  {w w₀ w₁ w₂ P P₀ P₁ P₂ : WList α β} {S T X : Set α}

open WList Set

namespace Graph

/-! ### Trails -/

/-- `G.IsTrail w` means that `w` is a walk of `G` with no repeated edges. -/
@[mk_iff]
structure IsTrail (G : Graph α β) (W : WList α β) : Prop where
  isWalk : G.IsWalk W
  edge_nodup : W.edge.Nodup

lemma IsTrail.sublist (h : G.IsTrail w₂) (hle : w₁.IsSublist w₂) : G.IsTrail w₁ :=
  ⟨h.isWalk.sublist hle, hle.edge_sublist.nodup h.edge_nodup⟩

@[simp]
lemma nil_isTrail_iff : G.IsTrail (nil x) ↔ x ∈ G.V := by
  simp [isTrail_iff]

@[simp]
lemma cons_isTrail_iff : G.IsTrail (cons x e w) ↔
    G.IsTrail w ∧ G.Inc₂ e x w.first ∧ e ∉ w.edge := by
  simp only [isTrail_iff, cons_isWalk_iff, cons_edge, List.nodup_cons]
  tauto

@[simp]
lemma IsTrail.of_cons (h : G.IsTrail (cons x e w)) : G.IsTrail w := by
  simp_all

lemma nil_isTrail (hx : x ∈ G.V) : G.IsTrail (nil x) :=
  ⟨IsWalk.nil hx, by simp⟩

lemma IsTrail.reverse (h : G.IsTrail w) : G.IsTrail w.reverse :=
  ⟨h.isWalk.reverse, by simp [h.edge_nodup]⟩

@[simp]
lemma reverse_isTrail_iff : G.IsTrail (reverse w) ↔ G.IsTrail w :=
  ⟨fun h ↦ by simpa using h.reverse, IsTrail.reverse⟩

lemma IsTrail.of_le (hw : G.IsTrail w) (hle : G ≤ H) : H.IsTrail w :=
  ⟨hw.isWalk.of_le hle, hw.edge_nodup⟩

lemma IsTrail.vxSet_subset (hw : G.IsTrail w) : w.V ⊆ G.V :=
  hw.isWalk.vxSet_subset

lemma IsTrail.induce (hw : G.IsTrail w) (hX : w.V ⊆ X) : G[X].IsTrail w :=
  ⟨hw.isWalk.induce hX, hw.edge_nodup⟩

/-- This is almost true without the `X ⊆ G.V` assumption; the exception is where
`w` is a nil walk on a vertex in `X \ G.V`. -/
lemma isTrail_induce_iff (hXV : X ⊆ G.V) :
    (G.induce X).IsTrail w ↔ G.IsTrail w ∧ w.V ⊆ X :=
  ⟨fun h ↦ ⟨h.of_le (G.induce_le hXV), h.vxSet_subset⟩, fun h ↦ h.1.induce h.2⟩

@[simp]
lemma isTrail_vxDelete_iff : (G - X).IsTrail w ↔ G.IsTrail w ∧ Disjoint w.V X := by
  rw [vxDelete_def, isTrail_induce_iff diff_subset, subset_diff, and_congr_right_iff,
    and_iff_right_iff_imp]
  exact fun h _ ↦ h.vxSet_subset

lemma IsTrail.isTrail_le (h : G.IsTrail w) (hle : H ≤ G) (hE : w.E ⊆ H.E)
    (hfirst : w.first ∈ H.V) : H.IsTrail w where
  isWalk := h.isWalk.isWalk_le hle hE hfirst
  edge_nodup := h.edge_nodup

lemma IsTrail.isTrail_le_of_nonempty (h : G.IsTrail w) (hle : H ≤ G) (hE : w.E ⊆ H.E)
    (hne : w.Nonempty) : H.IsTrail w where
  isWalk := h.isWalk.isWalk_le_of_nonempty hle hE hne
  edge_nodup := h.edge_nodup

/-! ### Paths -/

/-- `G.IsPath P` means that `w` is a walk of `G` with no repeated vertices
(and therefore no repeated edges). -/
@[mk_iff]
structure IsPath (G : Graph α β) (w : WList α β) : Prop where
  isWalk : G.IsWalk w
  nodup : w.vx.Nodup

lemma nil_isPath (hx : x ∈ G.V) : G.IsPath (nil x) :=
  ⟨IsWalk.nil hx, by simp⟩

@[simp] lemma nil_isPath_iff : G.IsPath (nil x) ↔ x ∈ G.V := by
  simp [isPath_iff]

@[simp]
lemma cons_isPath_iff : G.IsPath (cons x e P) ↔ G.IsPath P ∧ G.Inc₂ e x P.first ∧ x ∉ P := by
  simp only [isPath_iff, cons_isWalk_iff, cons_vx, List.nodup_cons, mem_vx]
  tauto

@[simp]
lemma IsPath.of_cons (h : G.IsPath (cons x e P)) : G.IsPath P := by
  simp_all

lemma IsPath.isTrail (h : G.IsPath P) : G.IsTrail P where
  isWalk := h.1
  edge_nodup := by
    induction P with
    | nil u => simp
    | cons u e w ih =>
      simp_all only [cons_isPath_iff, cons_edge, List.nodup_cons, and_true, forall_const]
      exact fun he ↦ h.2.2 <| h.1.isWalk.vx_mem_of_edge_mem he h.2.1.inc_left

lemma IsPath.reverse (hp : G.IsPath P) : G.IsPath P.reverse where
  isWalk := hp.isWalk.reverse
  nodup := by simp [hp.nodup]

@[simp]
lemma reverse_isPath_iff : G.IsPath (reverse P) ↔ G.IsPath P :=
  ⟨fun h ↦ by simpa using h.reverse, IsPath.reverse⟩

lemma IsWalk.dedup_isPath [DecidableEq α] (h : G.IsWalk P) : G.IsPath P.dedup :=
  ⟨h.dedup, P.dedup_vx_nodup⟩

lemma Inc₂.walk_isPath (h : G.Inc₂ e u v) (hne : u ≠ v) : G.IsPath h.walk :=
  ⟨h.walk_isWalk, by simp [hne]⟩

lemma IsPath.edge_nodup (h : G.IsPath P) : P.edge.Nodup :=
  h.isTrail.edge_nodup

lemma IsPath.of_le (hP : G.IsPath P) (hle : G ≤ H) : H.IsPath P :=
  ⟨hP.isWalk.of_le hle, hP.nodup⟩

lemma IsPath.vxSet_subset (hP : G.IsPath P) : P.V ⊆ G.V :=
  hP.isWalk.vxSet_subset

lemma IsPath.induce (hP : G.IsPath P) (hX : P.V ⊆ X) : (G.induce X).IsPath P :=
  ⟨hP.isWalk.induce hX, hP.nodup⟩

lemma IsPath.prefix (hP : G.IsPath P) (hP₀ : P₀.IsPrefix P) : G.IsPath P₀ where
  isWalk := hP.isWalk.prefix hP₀
  nodup := hP.nodup.sublist hP₀.vx_isPrefix.sublist

lemma IsPath.suffix (hP : G.IsPath P) (hP₀ : P₀.IsSuffix P) : G.IsPath P₀ where
  isWalk := hP.isWalk.suffix hP₀
  nodup := hP.nodup.sublist hP₀.vx_isSuffix.sublist

/-- This is almost true without the `X ⊆ G.V` assumption; the exception is where
`w` is a nil walk on a vertex in `X \ G.V`. -/
lemma isPath_induce_iff (hXV : X ⊆ G.V) : G[X].IsPath P ↔ G.IsPath P ∧ P.V ⊆ X :=
  ⟨fun h ↦ ⟨h.of_le (G.induce_le hXV), h.vxSet_subset⟩, fun h ↦ h.1.induce h.2⟩

@[simp]
lemma isPath_vxDelete_iff : (G - X).IsPath P ↔ G.IsPath P ∧ Disjoint P.V X := by
  rw [vxDelete_def, isPath_induce_iff diff_subset, subset_diff, and_congr_right_iff,
    and_iff_right_iff_imp]
  exact fun h _ ↦ h.vxSet_subset

lemma IsPath.isPath_le (h : G.IsPath w) (hle : H ≤ G) (hE : w.E ⊆ H.E)
    (hfirst : w.first ∈ H.V) : H.IsPath w where
  isWalk := h.isWalk.isWalk_le hle hE hfirst
  nodup := h.nodup

lemma IsPath.isPath_le_of_nonempty (h : G.IsPath w) (hle : H ≤ G) (hE : w.E ⊆ H.E)
    (hne : w.Nonempty) : H.IsPath w where
  isWalk := h.isWalk.isWalk_le_of_nonempty hle hE hne
  nodup := h.nodup

/-! ### Fixed ends. (To be cleaned up) -/

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

lemma IsPathFrom.isPath (h : G.IsPathFrom S T P) : G.IsPath P where
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

-- lemma IsWalk.isTrail (hVd : G.IsWalk w) (hedge : w.edge.Nodup) : G.IsTrail w := ⟨hVd, hedge⟩

-- lemma IsWalk.isPath (hw : G.IsWalk w) (hvx : w.vx.Nodup) : G.IsPath w := ⟨hw, hvx⟩

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

lemma IsPath.isPathFrom (hP : G.IsPath P) (hfirst : P.first ∈ S) (hlast : P.last ∈ T) :
    G.IsPathFrom S T P := ⟨hP, hfirst, hlast⟩

lemma nil_isWalkFrom (hx : x ∈ G.V) (hxS : x ∈ S) (hxT : x ∈ T) : G.IsWalkFrom S T (nil x) :=
  ⟨IsWalk.nil hx, hxS, hxT⟩

@[simp] lemma nil_isWalkFrom_iff : G.IsWalkFrom S T (nil x) ↔ x ∈ G.V ∧ x ∈ S ∧ x ∈ T := by
  simp [isWalkFrom_iff]

@[simp]
lemma cons_isTrailFrom : G.IsTrailFrom S T (cons x e w) ↔
    G.IsTrail w ∧ G.Inc₂ e x w.first ∧ e ∉ w.edge ∧ x ∈ S ∧ w.last ∈ T := by
  simp [isTrailFrom_iff, and_assoc]

@[simp]
lemma cons_isPathFrom : G.IsPathFrom S T (cons x e P) ↔
    G.IsPath P ∧ G.Inc₂ e x P.first ∧ x ∉ P ∧ x ∈ S ∧ P.last ∈ T := by
  simp [isPathFrom_iff, and_assoc]

@[simp]
lemma nil_isTrailFrom : G.IsTrailFrom S T (nil x) ↔ x ∈ G.V ∧ x ∈ S ∧ x ∈ T := by
  simp [isTrailFrom_iff]

@[simp] lemma nil_isPathFrom : G.IsPathFrom S T (nil x) ↔ x ∈ G.V ∧ x ∈ S ∧ x ∈ T := by
  simp [isPathFrom_iff]

lemma IsPathFrom.reverse (p : G.IsPathFrom S T w) : G.IsPathFrom T S w.reverse where
  isWalk := p.isWalk.reverse
  nodup := by simp [p.nodup]
  first_mem := by simp [p.last_mem]
  last_mem := by simp [p.first_mem]



end Graph
