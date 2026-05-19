import Mathlib
import Matroid.ForMathlib.Tactic.castData1

/-- `castData` pulls the cast outward; `eq_rec_constant` collapses `Eq.rec` on a fixed type. -/
example {α : Type*} {p q : α → Prop} {x : Subtype p} (h : p = q) : (h ▸ x).val = x.val := by
  simp only [castData, eq_rec_constant]
  -- rw [eq_rec_constant, eq_rec_constant]


example {α : Type*} {a b : α} (h : a = b) (x : {x : α // x = a}) : (h ▸ x).val = x.val := by
  simp only [castData, eq_rec_constant]

example {n m : ℕ} (h : n = m) (x : Fin n) : (h ▸ x).val = x.val := by
  simp only [castData, eq_rec_constant]

example {V : Type*} {G : SimpleGraph V} {u u' v v' : V} (h : u = u') (h' : v = v')
    (w : G.Walk u v) : (h ▸ h' ▸ w).edges = w.edges := by
  simp only [castData, eq_rec_constant]

example {V : Type*} {G : SimpleGraph V} {u u' v v' : V} (h : u = u') (h' : v = v')
    (w : G.Walk u v) (w' : G.Walk v' u) : (h ▸ h' ▸ w).append w' = (h ▸ w).append (h' ▸ w') := by
  simp only [castData, eq_rec_constant]
  simp
