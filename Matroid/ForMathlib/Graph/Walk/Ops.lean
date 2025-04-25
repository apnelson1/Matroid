import Matroid.ForMathlib.Graph.Walk.Defs
import Mathlib.Data.List.Nodup
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Data.Finset.Disjoint

namespace Graph
open Set Function List Nat Walk
variable {α β : Type*} {G H : Graph α β} {u v x y z : α} {e e' f g : β} {S T U: Set α}
  {F F' : Set β} {w w₁ w₂ : Walk α β}
namespace Walk

/-- Add an edge and a vertex to the end of a walk -/
def concat : Walk α β → β → α → Walk α β
| nil x, e, y => cons x e (nil y)
| cons x e w, f, y => cons x e (w.concat f y)


/-- Glue two walks `w₁, w₂` together. The last vertex of `w₁` is ignored,
so this is most reasonable if `w₁.last = w₂.first` -/
def append : Walk α β → Walk α β → Walk α β
| nil _x, w => w
| cons x e w, w' => cons x e (w.append w')

instance instAppend : Append (Walk α β) where
  append := append

/-- Properties of concat operation -/
@[simp]
lemma nil_concat : (nil x).concat e y = cons x e (nil y) := rfl

@[simp]
lemma cons_concat : (cons x e w).concat f y = cons x e (w.concat f y) := rfl

@[simp]
lemma concat_first : (w.concat e v).first = w.first := by
  induction w with
  | nil x => simp [concat]
  | cons x e w ih => simp [concat, ih]

@[simp]
lemma concat_last : (w.concat e v).last = v := by
  induction w with
  | nil x => simp [concat]
  | cons x e w ih => simp [concat, ih]

@[simp]
lemma concat_vx : (w.concat e v).vx = w.vx ++ [v] := by
  induction w with
  | nil x => simp [concat]
  | cons x e w ih => simp [concat, ih]

@[simp]
lemma concat_edge : (w.concat e v).edge = w.edge ++ [e] := by
  induction w with
  | nil x => simp [concat]
  | cons x e w ih => simp [concat, ih]

@[simp]
lemma concat_length : (w.concat e v).length = w.length + 1 := by
  induction w with
  | nil x => simp [concat]
  | cons x e w ih => simp [concat, ih]


@[simp]
lemma mem_concat : x ∈ w.concat e y ↔ x ∈ w ∨ x = y := by
  induction w with
  | nil => simp
  | cons u f w ih => simp [ih, or_assoc]

@[simp]
lemma concat_nonempty (w : Walk α β) (e x) : (w.concat e x).Nonempty := by
  induction w with simp_all

/- Properties of append operation -/
@[simp]
lemma append_notation : append w₁ w₂ = w₁ ++ w₂ := rfl

@[simp]
lemma nil_append : nil x ++ w₂ = w₂ := by
  simp only [← append_notation, append]

@[simp]
lemma cons_append : cons x e w₁ ++ w₂ = cons x e (w₁ ++ w₂) := by
  simp only [← append_notation, append]

@[simp]
lemma append_vx : (w₁ ++ w₂).vx = w₁.vx.dropLast ++ w₂.vx := by
  induction w₁ with
  | nil x => simp
  | cons x e w ih =>
    simp only [append_notation, append, cons_vx]
    rw [List.dropLast_cons_of_ne_nil vx_ne_nil, List.cons_append]
    simpa

lemma append_vx' {w₁ w₂ : Walk α β} (heq : w₁.last = w₂.first) :
    (w₁ ++ w₂).vx = w₁.vx ++ w₂.vx.tail := by
  match w₁ with
  | .nil x =>
    simp_all only [nil_last, append_vx, nil_vx, dropLast_single, nil_append, cons_append]
    rw [first_eq_vx_head]
    exact (head_cons_tail w₂.vx vx_ne_nil).symm
  | .cons x e w =>
    simp only [cons_last, cons_append, cons_vx, List.cons_append, List.cons.injEq,
      true_and] at heq ⊢
    exact append_vx' heq

protected lemma concat_eq_append (w : Walk α β) (e) (x) :
    w.concat e x = w ++ (cons w.last e (nil x)) := by
  induction w with
  | nil => simp
  | cons => simpa

@[simp]
lemma append_edge {w₁ w₂ : Walk α β} : (w₁ ++ w₂).edge = w₁.edge ++ w₂.edge := by
  induction w₁ with
  | nil x => simp only [nil_append, nil_edge, List.nil_append]
  | cons x e w ih => simp only [cons_append, cons_edge, ih, List.cons_append]

@[simp]
lemma append_length : (w₁ ++ w₂).length = w₁.length + w₂.length := by
  induction w₁ with
  | nil x => simp
  | cons x e w ih =>
    simp only [cons_append, cons_length, ih]
    omega

@[simp]
lemma append_nil (h : w.last = x) : w ++ (nil x) = w := by
  induction w with
  | nil u => simpa using h.symm
  | cons u e W ih =>
    rw [cons_last] at h
    rw [cons_append, ih h]

@[simp]
lemma append_first_of_eq (h : w₁.last = w₂.first):
  (w₁ ++ w₂).first = w₁.first := by
  induction w₁ with
  | nil x => simpa using h.symm
  | cons x e w ih => simp

@[simp]
lemma append_first_of_nonempty (h : w₁.Nonempty) :
  (w₁ ++ w₂).first = w₁.first := by
  induction w₁ with
  | nil x => simp at h
  | cons x e w ih => simp

@[simp]
lemma append_last : (w₁ ++ w₂).last = w₂.last := by
  induction w₁ with simp_all

lemma append_assoc (w1 w2 w3 : Walk α β) : (w1 ++ w2) ++ w3 = w1 ++ (w2 ++ w3) := by
  induction w1 with simp_all

lemma append_right_injective : Injective (w ++ ·) := by
  rintro w₁ w₂ h
  induction w with
  | nil x => simpa using h
  | cons x e w ih => exact ih <| by simpa using h

@[simp]
lemma append_right_inj : w ++ w₁ = w ++ w₂ ↔ w₁ = w₂ := by
  constructor
  · apply append_right_injective
  · rintro rfl
    rfl

@[simp]
lemma append_right_eq_self : w ++ w₁ = w ↔ w₁ = nil w.last := by
  induction w with
  | nil x => simp only [nil_append, nil_last]
  | cons x e w ih => simpa only [cons_append, cons.injEq, true_and, cons_last]

@[simp]
lemma append_left_eq_self : w₁ ++ w = w ↔ w₁.Nil :=
  ⟨fun h ↦ by simpa using congr_arg length h, fun h ↦ by rw [h.eq_nil_first, nil_append]⟩

@[simp]
lemma append_eq_nil_iff : w₁ ++ w₂ = nil x ↔ w₁.Nil ∧ w₂ = nil x := by
  induction w₁ with simp



-- lemma append_left_isPath (h : w₁.last = w₂.first) (hP : G.IsPath (w₁ ++ w₂)) : G.IsPath w₁ where
--   validIn := hP.validIn.append_left_validIn h
--   nodup := by
--     have := hP.nodup
--     rw [append_vx' h] at this
--     exact this.of_append_left

-- lemma append_right_isPath (hP : G.IsPath (w₁ ++ w₂)) : G.IsPath w₂ where
--   validIn := hP.validIn.append_right_validIn
--   nodup := by
--     have := hP.nodup
--     rw [append_vx] at this
--     exact this.of_append_right

-- lemma not_mem_prefix_of_mem_suffix_tail (heq : w₁.last = w₂.first) (hP : G.IsPath (w₁ ++ w₂))
--     (hmem : u ∈ w₂.vx.tail) : u ∉ w₁.vx := by
--   have := hP.nodup
--   rw [append_vx' heq, nodup_append] at this
--   exact (this.2.2 · hmem)

-- lemma not_mem_suffix_of_mem_prefix_dropLast (hP : G.IsPath (w₁ ++ w₂))
-- (hmem : u ∈ w₁.vx.dropLast) :
--     u ∉ w₂.vx := by
--   have := hP.nodup
--   rw [append_vx, nodup_append] at this
--   exact this.2.2 hmem

-- lemma eq_first_of_mem_prefix_suffix (hP : G.IsPath (w₁ ++ w₂)) (heq : w₁.last = w₂.first)
--     (hmem1 : u ∈ w₁.vx) (hmem2 : u ∈ w₂.vx) : u = w₂.first := by
--   have := hP.nodup
--   rw [append_vx' heq, nodup_append] at this
--   have := this.2.2 hmem1
--   rw [← w₂.vx.head_cons_tail vx_ne_nil, mem_cons, ← first_eq_vx_head] at hmem2
--   simp_all only [imp_false, or_false]

-- lemma eq_last_of_mem_prefix_suffix (hP : G.IsPath (w₁ ++ w₂)) (heq : w₁.last = w₂.first)
--     (hmem1 : u ∈ w₁.vx) (hmem2 : u ∈ w₂.vx) : u = w₁.last :=
--   heq ▸ eq_first_of_mem_prefix_suffix hP heq hmem1 hmem2

lemma eq_append_of_vx_mem {w : Walk α β} {u : α} (hmem : u ∈ w) :
    ∃ w₁ w₂ : Walk α β, w = w₁ ++ w₂ ∧ w₁.last = u ∧ w₂.first = u := by
  induction w with
  | nil x =>
    rw [mem_nil_iff] at hmem
    subst u
    exact ⟨nil x, nil x, rfl, rfl, rfl⟩
  | cons x e w ih =>
    rw [mem_cons_iff] at hmem
    obtain rfl | h := hmem
    · exact ⟨nil u, cons u e w, rfl, rfl, rfl⟩
    · obtain ⟨w₁, w₂, rfl, hfin, hfirst⟩ := ih h
      use cons x e w₁, w₂
      simp only [cons_append, cons_last, hfin, hfirst, and_self]

lemma eq_append_cons_of_edge_mem {w : Walk α β} {e : β} (he : e ∈ w.edge) :
    ∃ w₁ w₂ : Walk α β, w = w₁ ++ cons w₁.last e w₂ ∧ e ∉ w₁.edge := by
  induction w with
  | nil x => simp only [nil_edge, not_mem_nil] at he
  | cons x e' w ih =>
    simp only [cons_edge, mem_cons] at he
    obtain rfl | he' := he
    · use nil x, w, rfl, by simp only [nil_edge, not_mem_nil, not_false_eq_true]
    · by_cases h : e = e'
      · subst e'
        use nil x, w, rfl, by simp only [nil_edge, not_mem_nil, not_false_eq_true]
      · obtain ⟨w₁, w₂, rfl, hnin⟩ := ih he'
        use cons x e' w₁, w₂, by simp only [cons_last, cons_append]
        simp only [cons_edge, mem_cons, h, hnin, or_self, not_false_eq_true]



/-- Reverse the order of the vertices and edges of a walk. -/
def reverse : Walk α β → Walk α β
| nil x => nil x
| cons x e w => w.reverse.concat e x


/-- Properties of reverse operation -/
@[simp]
lemma reverse_nil : (nil x : Walk α β).reverse = nil x := rfl

@[simp]
lemma reverse_cons : (cons x e w).reverse = (w.reverse).concat e x := rfl

@[simp]
lemma reverse_nonempty (w : Walk α β) : w.reverse.Nonempty ↔ w.Nonempty := by
  induction w with simp_all

@[simp]
lemma reverse_first : (reverse w).first = w.last := by
  induction w with
  | nil x => simp [reverse]
  | cons x e w ih => simp [reverse, ih]

@[simp]
lemma reverse_last : (reverse w).last = w.first := by
  induction w with
  | nil x => simp [reverse]
  | cons x e w ih => simp [reverse, ih]

@[simp]
lemma reverse_vx : (reverse w).vx = w.vx.reverse := by
  induction w with
  | nil x => simp [reverse]
  | cons x e w ih => simp [reverse, ih]

@[simp]
lemma reverse_edge {w : Walk α β} : (reverse w).edge = w.edge.reverse := by
  induction w with
  | nil x => simp [reverse]
  | cons x e w ih => simp [reverse, ih]

@[simp]
lemma reverse_length {w : Walk α β} : (reverse w).length = w.length := by
  induction w with
  | nil x => simp [reverse]
  | cons x e w ih => simp [reverse, ih]


lemma reverse_append {w₁ w₂ : Walk α β} (h_eq : w₁.last = w₂.first) :
    (w₁ ++ w₂).reverse = w₂.reverse ++ w₁.reverse := by
  induction w₁ with
  | nil u => rw [nil_append, reverse_nil, append_nil (by simpa using h_eq.symm)]
  | cons u e w₁ ih =>
  simp only [cons_append, reverse_cons, ih (by simpa using h_eq)]
  rw [Walk.concat_eq_append, Walk.concat_eq_append, ← append_assoc]
  simp

@[simp]
lemma concat_reverse (w : Walk α β) (e) (x) : (w.concat e x).reverse = cons x e w.reverse := by
  rw [Walk.concat_eq_append, reverse_append (by simp)]
  simp

@[simp]
lemma reverse_reverse (w : Walk α β) : w.reverse.reverse = w := by
  induction w with | nil => simp | cons => simpa

lemma reverse_inj (h : w₁.reverse = w₂.reverse) : w₁ = w₂ := by
  rw [← reverse_reverse w₁, h, reverse_reverse]

@[simp]
lemma reverse_inj_iff : w₁.reverse = w₂.reverse ↔ w₁ = w₂ :=
  ⟨reverse_inj, fun h ↦ by rw [h]⟩

lemma reverse_eq_comm : w₁.reverse = w₂ ↔ w₁ = w₂.reverse := by
  rw [← reverse_reverse w₂, reverse_inj_iff, reverse_reverse]


@[simp]
lemma mem_reverse : x ∈ w.reverse ↔ x ∈ w := by
  induction w with
  | nil => simp
  | cons u e w ih => simp [ih, or_comm]

@[simp]
lemma reverse_vxSet (w : Walk α β) : w.reverse.vxSet = w.vxSet := by
  simp [vxSet]

end Walk


-- lemma Connected.exist_walk (h : G.Connected u v) : ∃ (W : Walk α β), W.ValidIn G ∧
--     W.first = u ∧ W.last = v := by
--   induction h with
--   | single hradj =>
--     obtain ⟨W, hW, hlength, hfirst, hlast⟩ := hradj.exist_walk
--     use W
--   | tail hconn hradj ih =>
--     expose_names
--     obtain ⟨W, hW, hfirst, hlast⟩ := ih
--     obtain ⟨W', hW', hlength, hfirst', hlast'⟩ := hradj.exist_walk
--     subst b c u
--     use W ++ W', append_validIn hfirst'.symm hW hW'
--     simp only [hfirst', append_first_of_eq, append_last, and_self]

-- theorem Connected.iff_walk : G.Connected u v ↔ ∃ w : Walk α β, w.ValidIn G
--  ∧ w.first = u ∧ w.last = v := by
--   constructor
--   · exact fun a ↦ exist_walk a
--   · rintro ⟨w, h1, rfl, rfl⟩
--     exact h1.connected

-- lemma SetConnected.exist_walk (h : G.SetConnected S T) :
  --∃ w : Walk α β, G.IsWalkFrom S T w := by
--   obtain ⟨x, hxS, y, hyT, h⟩ := h
--   obtain ⟨w, hVd, rfl, rfl⟩ := h.exist_walk
--   use w, hVd

-- theorem SetConnected.iff_walk : G.SetConnected S T ↔ ∃ w : Walk α β, G.IsWalkFrom S T w := by
--   constructor
--   · exact SetConnected.exist_walk
--   · rintro ⟨w, h⟩
--     exact h.setConnected

end Graph
