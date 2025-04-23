import Matroid.ForMathlib.Graph.Walk.Defs
import Matroid.ForMathlib.Graph.Subgraph

variable {α β : Type*} {x y z u v : α} {e f : β} {G H : Graph α β} {w : Graph.Walk α β}

open Set

namespace Graph

open Walk

def Walk.rotate (w : Walk α β) (hx : x ∈ w.vx) : Walk α β :=
  match w with
  | .nil u => nil u
  | .cons e u w =>
  sorry


def IsClosed (W : Walk α β) : Prop := W.first = W.last

@[mk_iff]
structure IsCycle (G : Graph α β) (W : Walk α β) : Prop where
  validIn : W.ValidIn G
  nodup' : W.vx.dropLast.Nodup
  closed : W.first = W.last

lemma IsPath.not_isCycle (hP : G.IsPath w) (hnonempty : w.Nonempty) : ¬ G.IsCycle w := by
  suffices heq : w.first ≠ w.last by
    rintro ⟨hVd, hnodup, hclosed⟩
    exact heq hclosed
  rwa [first_ne_last_iff hP.nodup]

lemma Walk.ValidIn.isCycle (hVd : w.ValidIn G) (hvx : w.vx.dropLast.Nodup)
    (hclosed : w.first = w.last) : G.IsCycle w := ⟨hVd, hvx, hclosed⟩

lemma IsTrail.isCycle (hT : G.IsTrail w) (hvx : w.vx.dropLast.Nodup) (hclosed : w.first = w.last) :
    G.IsCycle w := ⟨hT.validIn, hvx, hclosed⟩

@[simp]
lemma isCycle_simp (hVd : w.ValidIn G) (hnodup : w.vx.dropLast.Nodup) (hclosed : w.first = w.last) :
    G.IsCycle w :=
  IsCycle.mk hVd hnodup hclosed



lemma IsCycle.exist_paths_of_mem_of_mem {C : Walk α β} (hC : G.IsCycle C)
    (hx : x ∈ C.vx) (hy : y ∈ C.vx) (hne : x ≠ y) :
    ∃ P Q, G.IsPath P ∧ G.IsPath Q ∧ P.first = x ∧ Q.first = x ∧ P.first = y ∧ Q.first = y ∧
    P.toGraph ∪ Q.toGraph = C.toGraph := sorry
