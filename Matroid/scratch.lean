mport Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A connected component is *odd* if it has an add number of vertices
in its support. -/
-- Note: only connected components with finitely many vertices can be odd.
def ConnectedComponent.isOdd (c : G.ConnectedComponent) : Prop :=
  Odd (Nat.card c.supp)

noncomputable def cardOddComponents (G : SimpleGraph V) : Nat :=
  Set.ncard {c : G.ConnectedComponent | c.isOdd}

lemma ConnectedComponent.isOdd_iff (c : G.ConnectedComponent) [Fintype c.supp] :
    c.isOdd ↔ Odd (Fintype.card c.supp) := by
  rw [isOdd, Nat.card_eq_fintype_card]

/-- This is `Quot.recOn` specialized to connected components.
For convenience, it strengthens the assumptions in the hypothesis
to provide a path between the vertices. -/
@[elab_as_elim]
def ConnectedComponent.recOn
    {motive : G.ConnectedComponent → Sort*}
    (c : G.ConnectedComponent)
    (f : (v : V) → motive (G.connectedComponentMk v))
    (h : ∀ (u v : V) (p : G.Walk u v) (_ : p.IsPath),
      ConnectedComponent.sound p.reachable ▸ f u = f v) :
    motive c :=
  Quot.recOn c f (fun u v r => r.elim_path fun p => h u v p p.2)

instance [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (c : G.ConnectedComponent) (v : V) : Decidable (v ∈ c.supp) :=
  c.recOn
    (fun w => by simp only [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]; infer_instance)
    (fun _ _ _ _ => Subsingleton.elim _ _)


instance myInst [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (u : ConnectedComponent G) :
    Fintype u.supp := inferInstance



lemma oddComponentsIncrease [Fintype V] [Inhabited V] [DecidableEq V]  (G G' : SimpleGraph V)
    (h : G ≤  G') (u : Set V) [Finite u]:
    cardOddComponents ((⊤ : Subgraph G').deleteVerts u).coe ≤ cardOddComponents ((⊤ : Subgraph G).deleteVerts u).coe := by
      -- I left out [DecideableRel G.Adj] [Decidable G'.Adj] because it would be nice if this can be done without it
      -- it would need to proved for Gmax

      -- Seems doable but involved
      let g : ConnectedComponent ((⊤ : Subgraph G').deleteVerts u).coe → ConnectedComponent ((⊤ : Subgraph G).deleteVerts u).coe := sorry

      haveI : Finite (ConnectedComponent ((⊤ : Subgraph G).deleteVerts u).coe) := sorry

      exact Set.ncard_le_ncard_of_injOn g (by sorry) (by sorry)

def tutte [Fintype V] [Inhabited V] [DecidableEq V] [DecidableRel G.Adj] :
    (∃ (M : Subgraph G) , M.IsPerfectMatching) ↔
      (∀ (u : Set V),
        cardOddComponents ((⊤ : G.Subgraph).deleteVerts u).coe ≤ u.ncard) := by
  constructor
  {
    -- actually solved, omitted for brevity
    sorry
  }
  {
    contrapose!
    intro h

    have ⟨ Gmax , hGmax ⟩ : ∃ (G' : SimpleGraph V),
      G ≤ G' ∧
      (∀ (M : Subgraph G'), ¬ M.IsPerfectMatching)  ∧
      ∀ (G'' : SimpleGraph V), G' < G'' → ∃ (M : Subgraph G''), M.IsPerfectMatching := by
        by_contra' hc
        have ⟨ H , hH ⟩ := hc G (Eq.ge rfl) h
        have ⟨ H' , hH' ⟩ := hc H (le_of_lt hH.1) hH.2
        -- This sorry is kind of stumping me. I kind of want to make the argument
        -- that we can't have an infinite chain of strictly larger graphs.
        sorry

    suffices : ∃ u, Set.ncard u < cardOddComponents ((⊤ : Subgraph Gmax).deleteVerts u).coe
    · obtain ⟨u, hu ⟩ := this
      use u
      exact lt_of_lt_of_le hu (by
        exact oddComponentsIncrease G Gmax hGmax.1 u
        )

    let S : Set V := {v | G.degree v = Fintype.card V - 1}

    let Gsplit := ((⊤ : Subgraph Gmax).deleteVerts S)
    have ⟨K, v, w, hKvw ⟩ : ∃ (K : ConnectedComponent Gsplit.coe) (v w :  Set.Elem Gsplit.verts),
      v ∈ K.supp ∧ w ∈ K.supp ∧ v ≠ w ∧ ¬ Gmax.Adj v w := sorry

    sorry
  }
