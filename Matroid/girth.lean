import Matroid.Graph.Forest

variable {α β : Type*} {G : Graph α β} {x y z u v w : α} {e f : β} {F : Set β} {X Y : Set α}

open Set

namespace Graph

noncomputable def eGirth (G : Graph α β) : ℕ∞ := ⨅ C ∈ {C | G.IsCycleSet C}, C.encard

noncomputable def girth (G : Graph α β) := (eGirth G).toNat



end Graph
