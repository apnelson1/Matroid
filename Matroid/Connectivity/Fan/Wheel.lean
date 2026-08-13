import Matroid.Graphic
import Matroid.Graph.Constructions.Apex

variable {α β : Type*} {M : Matroid α} {X Y C K T : Set α} {e f g x y : α} {b c d : Bool}
     {n i j : ℕ} {F : List α} {J : Bool → ZMod n → α} {G : Graph α β}

namespace Matroid

open Set Option

/-- The wheel matroid with ground set `Fin n × Bool`. -/
protected def wheel (n : ℕ) : Matroid (Fin n × Bool) := (Graph.wheel n).cycleMatroid
