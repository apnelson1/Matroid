import Mathlib.Combinatorics.Graph.Subgraph
import Mathlib.Data.Set.Card
import Mathlib.Data.ENat.Lattice

variable {α β κ : Type*} {x y z u v : α} {e f : β} {G : Graph α β}

open Function Set

-- this implicitly prepends `Graph.` to all declarations in scope.
namespace Graph

structure EdgeColoring (G : Graph α β) (κ : Type*) where
  -- the underlying function from the edge type to the color type
  toFun : β → κ
  -- a proof that the function is a proper edge coloring. This should not be used directly
  -- since it is phrased in terms of the implementation detail `toFun`.
  -- instead, see `EdgeColoring.apply_eq_of_inc_of_inc_of_eq`.
  apply_eq_of_inc_of_inc_of_eq' : ∀ x e f, G.Inc e x → G.Inc f x → toFun e = toFun f → e = f

/-- An edge coloring behaves like a function from `β → κ`. The following instance allows it
to be syntactically treated like one. -/
instance : FunLike (G.EdgeColoring κ) β κ where
  coe c := c.toFun
  coe_injective' c c' h := by grind [cases EdgeColoring]

/- This line can be ignored-/
initialize_simps_projections EdgeColoring (toFun → coe)

lemma EdgeColoring.apply_eq_of_inc_of_inc_of_eq (c : G.EdgeColoring κ) (hex : G.Inc e x)
    (hfx : G.Inc f x) (hef : c e = c f) : e = f :=
  c.apply_eq_of_inc_of_inc_of_eq' x e f hex hfx hef

/-- The contrapositive of the above; different incident edges get different colors.  -/
lemma EdgeColoring.apply_ne_of_inc_of_inc_of_ne (c : G.EdgeColoring κ) (hex : G.Inc e x)
    (hey : G.Inc f x) (hef : e ≠ f) : c e ≠ c f := by
  contrapose! hef
  exact c.apply_eq_of_inc_of_inc_of_eq hex hey hef

/-- Given a proper edge-coloring defined only on the subtype of edges of `G`, a classically
chosen proper edge-coloring of `G` obtained by assigning an arbitrary color to the junk edges. -/
noncomputable def edgeColoring.ofSubtypeFun [Nonempty κ] [DecidablePred (· ∈ E(G))] (c : E(G) → κ)
    (hc : ∀ x e f (he : G.Inc e x) (hf : G.Inc f x),
      c ⟨e, he.edge_mem⟩ = c ⟨f, hf.edge_mem⟩ → e = f) : G.EdgeColoring κ where
  toFun e := if he : e ∈ E(G) then c ⟨e, he⟩ else Classical.arbitrary κ
  apply_eq_of_inc_of_inc_of_eq' x e f he hf := by
    rw [dif_pos he.edge_mem, dif_pos hf.edge_mem]
    exact hc x e f he hf

/-- An edge-coloring is an injective function when restricted to an edge-neighborhood of a vertex.
The proof is an opaque one-liner that is exploiting the definitions of both `Set.InjOn`
and `Graph.IncidenceSet`. -/
lemma EdgeColoring.injOn_incidenceSet (c : G.EdgeColoring κ) (x : α) :
    Set.InjOn c (G.incidenceSet x) :=
  fun _ he _ ↦ c.apply_eq_of_inc_of_inc_of_eq he
  /-
  The following longer but less opaque proof also works.
  simp only [Set.InjOn, mem_incidenceSet]
  intro e he f hf hef
  exact c.apply_eq_of_inc_of_inc_of_eq he hf hef
  -/


/-- Relabel the colors in an edge coloring, or equivalently, compose the coloring as a function
with some function out of the color set which is injective on the range of the coloring.
The `[simps]` tag automatically generates a `@[simp]`
lemma that will unfold this definition in appropriate places.  -/
@[simps]
def EdgeColoring.map {ι : Type*} (c : G.EdgeColoring κ) (φ : κ → ι) (inj : InjOn φ (c '' E(G))) :
    G.EdgeColoring ι where
  toFun := φ ∘ c
  apply_eq_of_inc_of_inc_of_eq' x _ _ he hf hef := c.injOn_incidenceSet x he hf <|
    inj (mem_image_of_mem _ he.edge_mem) (mem_image_of_mem _ hf.edge_mem) hef

/-- `G.edgeColorable n` means that `G` has an edge coloring with colours in the type
`Fin n`, which is essentially the set `{0, ..., n-1}`. -/
def EdgeColorable (G : Graph α β) (n : ℕ) := Nonempty (G.EdgeColoring (Fin n))

/-- an `m`-edge-colorable graph is `n`-edge-colorable for `n ≥ m`. Since `Fin m` is not actually
formally a subset of `Fin n` (both are types, not sets), the proof uses `EdgeColoring.map`
together with the fact that there is an injection `Fin.castLE` from `Fin m` to `Fin n`. -/
lemma EdgeColorable_mono {m n : ℕ} (hG : G.EdgeColorable m) (hmn : m ≤ n) : G.EdgeColorable n := by
  obtain ⟨c⟩ := hG
  exact ⟨c.map _ (Fin.castLE_injective hmn).injOn⟩

/-- The edge-chromatic number of a graph, as a term in the type `ℕ∞`, which is essentially the
natural numbers with infinity. Don't worry about the way it is defined. -/
noncomputable def chromaticIndex (G : Graph α β) : ℕ∞ :=
    ⨅ n ∈ setOf {x | G.EdgeColorable x}, (n : ℕ∞)

-- /-- the chromatic index of `G` is at most the size of the range of a given edge-coloring. -/
-- lemma EdgeColoring.chromaticIndex_le (c : G.EdgeColoring κ) :
--     G.chromaticIndex ≤ (Set.range c).encard := by
--   classical
--   obtain hfin | hinf := (c '' E(G)).finite_or_infinite
--   · -- if `c` has finite range, produce a bijection between `c` and `Fin n` for some `n`,
--     -- and use `EdgeColoring.map`.
--     have hs := hfin.to_subtype
--     obtain ⟨n, ⟨φ⟩⟩ := Finite.exists_equiv_fin (c '' E(G))
--     have := Set.rangeFactorization c

end Graph
