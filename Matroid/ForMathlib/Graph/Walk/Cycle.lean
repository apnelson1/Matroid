import Matroid.ForMathlib.Graph.Walk.Path
import Matroid.ForMathlib.Graph.Connected
import Matroid.ForMathlib.Graph.WList.Cycle

variable {α β : Type*} {x y z u v : α} {e f : β} {G H : Graph α β}
  {w w₁ w₂ : WList α β} {S T : Set α}

open WList

namespace Graph

@[mk_iff]
structure IsCycle (G : Graph α β) (C : WList α β) : Prop where
  isWalk : G.IsWalk C
  isClosed : C.IsClosed
  nodup : G.IsPath C.dropLast



end Graph
