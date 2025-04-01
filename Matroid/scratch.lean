import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Walk
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

namespace SimpleGraph
namespace Walk

universe u v
variable {V : Type u}
variable {G : SimpleGraph V}


example (u v w : V) (huv : G.Adj u v) (P : G.Walk v w) (hP : (Walk.cons huv P).IsPath) :
    u ∉ P.support := by
  simp_all only [cons_isPath_iff, not_false_eq_true]
  -- have := hP.support_nodup
  -- simp only [support_cons, List.nodup_cons] at this
  -- exact this.1

theorem Two_Paths_Contain_Cycle_v3 {u v : V} {p q : G.Walk u v} :
    p.IsPath → q.IsPath → p ≠ q → ¬(p.toSubgraph ⊔ q.toSubgraph).spanningCoe.IsAcyclic := by
  intro hp
  intro hq
  intro hne
  by_contra! con
  cases p with
  | nil =>
  simp[isPath_iff_eq_nil] at hq
  rw[hq] at hne
  contradiction
  | @cons _ x _ hux pyv =>
  cases q with
  | nil =>
  have pnil : (cons hux pyv).Nil := by
    simp [isPath_iff_eq_nil] at hp
  contradiction
  | @cons _ y _ cq pq =>
  have xeqy : x = y := by
    by_contra! xneqy
  rw [cons_isPath_iff] at hq
