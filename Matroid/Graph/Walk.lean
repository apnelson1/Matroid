import Matroid.Graph.Subgraph

variable {α α' β β' : Type*} {G H : Graph α β} {e : β} {v x y : α}

inductive Walk (α β : Type*) where
  | nil (x : α) : Walk α β
  | cons (x : α) (e : β) (W : Walk α β) : Walk α β

variable {W : Walk α β}

namespace Walk

def last : Walk α β → α
  | nil x => x
  | cons _ _ W => W.last

def first : Walk α β → α
  | nil x => x
  | cons x _ _ => x

@[simp]
lemma nil_first (x : α) : (Walk.nil (β := β) x).first = x := rfl

@[simp]
lemma nil_last (x : α) : (Walk.nil (β := β) x).last = x := rfl

@[simp]
lemma first_cons (x) (e) (W : Walk α β) : (W.cons x e).first = x := rfl

@[simp]
lemma last_cons (x) (e) (W : Walk α β) : (W.cons x e).last = W.last := rfl

def ValidIn (W : Walk α β) (G : Graph α β) : Prop :=
  match W with
  | nil x => x ∈ G.V
  | cons x e W => G.Inc₂ e x W.first ∧ W.ValidIn G

def vxSet : Walk α β → Set α
  | nil x => {x}
  | cons x _ W => insert x W.vxSet

def edgeSet : Walk α β → Set β
  | nil _ => ∅
  | cons _ e W => insert e W.edgeSet

def vxList : Walk α β → List α
  | nil x => [x]
  | cons x _ W => x :: W.vxList

instance : Membership α (Walk α β) where
  mem w x := x ∈ w.vxList

@[simp]
lemma mem_nil : x ∈ nil (β := β) y ↔ x = y := by
  change _ ∈ vxList _ ↔ _
  simp [vxList]

@[simp]
lemma mem_cons : y ∈ cons x e W ↔ y = x ∨ y ∈ W := by
  change _ ∈ vxList _ ↔ _
  simp only [vxList, List.mem_cons]
  rfl

def edgeList : Walk α β → List β
  | nil _ => []
  | cons _ e W => e :: W.edgeList

def append : Walk α β → Walk α β → Walk α β
  | nil _, W => W
  | (cons e x W), W' => cons e x (W.append W')

def ofEdge (e : β) (x y : α) : Walk α β :=
  cons x e (Walk.nil y)

def dropLast : Walk α β → Walk α β
  | nil x => nil x
  | cons x _ (nil _) => nil x
  | cons x e (cons y f W) => cons x e (cons y f W).dropLast

def dropFirst : Walk α β → Walk α β
  | nil x => nil x
  | cons _ _ W => W

def Nonempty : Walk α β → Prop
  | nil _ => False
  | _ => True

@[simp]
lemma ofEdge_first (e : β) (x y : α) : (ofEdge e x y).first = x := rfl

@[simp]
lemma ofEdge_last (e : β) (x y : α) : (ofEdge e x y).last = y := rfl

@[simp]
lemma ofEdge_dropLast (e : β) (x y : α) : (ofEdge e x y).dropLast = nil x := by
  simp [ofEdge, dropLast]

@[simp]
lemma cons_validIn_iff : (W.cons x e).ValidIn G ↔ G.Inc₂ e x W.first ∧ W.ValidIn G := Iff.rfl

@[simp]
lemma ofEdge_validIn_iff : (Walk.ofEdge e x y).ValidIn G ↔ G.Inc₂ e x y :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h, h.vx_mem_right⟩⟩

def takeUntil [DecidableEq α] (W : Walk α β) (x : α) : Walk α β :=
  match W with
  | nil y => nil y
  | cons y e W =>
    if y = x then nil y
    else cons y e (W.takeUntil x)

lemma takeUntil_last [DecidableEq α] (W : Walk α β) (hxw : x ∈ W) : (W.takeUntil x).last = x := by
  induction W with
  | nil y =>
    obtain rfl : x = y := by simpa using hxw
    simp [takeUntil]
  | cons y e W ih =>
  obtain rfl | hne := eq_or_ne x y
  · simp [takeUntil]
  simp only [mem_cons, hne, false_or] at hxw
  simp [takeUntil, hne.symm, ih hxw]

@[simp] lemma takeUntil_first [DecidableEq α] (W : Walk α β) (x : α) :
    (W.takeUntil x).first = W.first := by
  cases W with
  | nil y => simp [takeUntil]
  | cons y e W =>
    simp [takeUntil]
    split_ifs <;>
    rfl

lemma Nonempty.cons_dropLast (hW : W.Nonempty) (e : β) (x : α)  :
    (cons x e W).dropLast = cons x e W.dropLast := by
  cases W with
  | nil a => simp [Nonempty] at hW
  | cons f a W => simp [dropLast]

lemma mem_dropLast_or_eq_last (hu : x ∈ W) : x ∈ W.dropLast ∨ x = W.last := by
  induction W with
  | nil x => simpa [dropLast] using hu
  | cons y e W ih =>
  cases W with
  | nil z => simpa [dropLast] using hu
  | cons z f W =>
  simp only [dropLast, mem_cons, last_cons, or_assoc]
  obtain rfl | rfl | h := by simpa using hu
  · simp
  · exact .inr <| ih <| by simp
  exact .inr <| ih <| by simp [h]



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



  -- match W with
  -- | nil a => by simpa [dropLast] using hu
  -- | cons a e (nil b) => by simpa [dropLast] using hu
  -- | cons a e (cons b f W) => by
  --   simp [dropLast]
  --   simp at hu



end Walk
