import Matroid.Graph.Subgraph

variable {α α' β β' : Type*} {G H : Graph α β} {e : β} {v x y : α}

inductive Walk (α β : Type*) where
  | nil (x : α) : Walk α β
  | cons (e : β) (x : α) (W : Walk α β) : Walk α β

variable {W : Walk α β}

namespace Walk

def last : Walk α β → α
  | nil x => x
  | cons _ x _ => x

def first : Walk α β → α
  | nil x => x
  | cons _ _ W => first W

@[simp]
lemma nil_first (x : α) : (Walk.nil (β := β) x).first = x := rfl

@[simp]
lemma nil_last (x : α) : (Walk.nil (β := β) x).last = x := rfl

@[simp]
lemma cons_last (e) (x) (W : Walk α β) : (W.cons e x).last = x := rfl

@[simp]
lemma cons_first (e) (x) (W : Walk α β) : (W.cons e x).first = W.first := rfl

def ValidIn (W : Walk α β) (G : Graph α β) : Prop :=
  match W with
  | nil x => x ∈ G.V
  | cons e x W => G.Inc₂ e x W.first ∧ W.ValidIn G

def vxSet : Walk α β → Set α
  | nil x => {x}
  | cons _ x W => insert x W.vxSet

def edgeSet : Walk α β → Set β
  | nil _ => ∅
  | cons e _ W => insert e W.edgeSet

def vxList : Walk α β → List α
  | nil x => [x]
  | cons _ x W => x :: W.vxList

instance : Membership α (Walk α β) where
  mem w x := x ∈ w.vxList

@[simp]
lemma mem_nil : x ∈ nil (β := β) y ↔ x = y := by
  change _ ∈ vxList _ ↔ _
  simp [vxList]

def edgeList : Walk α β → List β
  | nil _ => []
  | cons e _ W => e :: W.edgeList

def append : Walk α β → Walk α β → Walk α β
  | nil _, W => W
  | (cons e x W), W' => cons e x (W.append W')

def ofEdge (e : β) (x y : α) : Walk α β :=
  (Walk.nil x).cons e y

def dropLast : Walk α β → Walk α β
  | nil x => nil x
  | cons _ x (nil _) => nil x
  | cons e x (cons f y W) => cons e x (cons f y W).dropLast

@[simp]
lemma ofEdge_first (e : β) (x y : α) : (ofEdge e x y).first = x := rfl

@[simp]
lemma ofEdge_last (e : β) (x y : α) : (ofEdge e x y).last = y := rfl

@[simp]
lemma ofEdge_dropLast (e : β) (x y : α) : (ofEdge e x y).dropLast = nil x := by
  simp [ofEdge, dropLast]

@[simp]
lemma cons_validIn_iff : (W.cons e x).ValidIn G ↔ G.Inc₂ e x W.first ∧ W.ValidIn G := Iff.rfl

@[simp]
lemma ofEdge_validIn_iff : (Walk.ofEdge e x y).ValidIn G ↔ G.Inc₂ e x y :=
  ⟨fun h ↦ h.1.symm, fun h ↦ ⟨h.symm, h.vx_mem_left⟩⟩

def IsPathIn (W : Walk α β) (G : Graph α β) := W.ValidIn G ∧ W.vxList.Nodup

def IsClosed (W : Walk α β) : Prop := W.first = W.last

lemma Inc₂.ofEdge_isPathIn (h : G.Inc₂ e x y) (hne : x ≠ y) : (Walk.ofEdge e x y).IsPathIn G :=
  ⟨by simpa, by simpa [ofEdge, Walk.vxList, ne_comm]⟩

@[mk_iff]
structure IsCycleIn (W : Walk α β) (G : Graph α β) : Prop where
  closed : W.IsClosed
  validIn : W.ValidIn G
  nodup : W.dropLast.vxList.Nodup

lemma ofEdge_isCycleIn_iff : (Walk.ofEdge e x x).IsCycleIn G ↔ G.IsLoopAt e x := by
  simp [isCycleIn_iff, IsClosed, vxList]

lemma dropLast_cons (W : Walk α β) (e : β) (x : α) : (W.cons e x).dropLast = W := by
  cases W with
  | nil a =>
    simp [dropLast]
  | cons f a W =>
  simp [dropLast]

lemma mem_dropLast_or_eq_last (hu : x ∈ W) : x ∈ W.dropLast ∨ x = W.last := by
  cases W with
  | nil a =>
    obtain rfl : x = a := by simpa using hu
    exact .inr rfl
  | cons e a W =>
  simp [dropLast]


end Walk
