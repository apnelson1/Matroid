Hi, I am Jun Kwon, a PhD student of Peter Nelson (@**Peter Nelson**). I would like to revive this thread and ask for some advice on the definition of a graph (multigraph).

Here, α (or `Set α`) will be the type of vertices, and β will be the type of edges. Also, "graph" will mean "multigraph" here.

First, we should ask what makes a definition of a graph good. I suggest that a good definition of a mathematical object is one that facilitates the fundamental operations on the object. In the case of graphs, that means removing and adding vertices and edges, and contracting edges; or equivalently, taking subgraphs, induced subgraphs, and minors.

Similar to the definition of a matroid, deletion of elements is a fundamental operation on graphs (e.g., induced subgraphs). To facilitate this operation, Peter defined matroids such that the structure contains the `ground set` field. Using this, `M \ e` does not have type `Matroid { f // f ≠ e }` but simply `Matroid β` with `e` removed from the ground set. In effect, the type `Matroid β` contains not only the matroids on `β`, but also all possible submatroids.

However, contraction of edges in graphs comes with an added complexity: what should the new supervertex be labelled with? For example, if an edge `e : β` between `u, v : α` is contracted, how can we deterministically provide a new label for the vertex created by identifying `u` and `v`? From here, I will talk about vertex identification rather than contraction as edge contraction can be done by identifying the ends of edges and removing the edges afterwards.

There are many different answers to this. One approach we tried is to ask the user to decide by providing a function `f` such that `f u = f v` and labelling the supervertex as `f u`. However, this is not great at facilitating contraction: if you perform ten edge contractions, you will have to create and remember ten different functions just to keep track of where each vertex was merged.

Mario has suggested a `PERGraph`.
## PERGraph

```lean4
import Mathlib.Tactic

structure PERGraph (α β : Type*) where
  /-- The partial equivalence relation on the vertex set.
  If `vertexRel a b`, then `a` and `b` represent the same vertex. -/
  vertexRel : α → α → Prop
  vertexRel_symm : vertexRel a b → vertexRel b a
  vertexRel_trans : vertexRel a b → vertexRel b c → vertexRel a c
  IsLink : β → α → α → Prop
  isLink_symm : IsLink e a b → IsLink e b a
  isLink_resp : IsLink e a b → vertexRel b b' → IsLink e a b'
  rel_of_isLink : IsLink e x y → IsLink e v w → vertexRel x v ∨ vertexRel x w
  left_mem_of_isLink : IsLink e x y → vertexRel x x
```

Here, `vertexRel` is a partial equivalence relation (PER) on `α`, and related vertices represent the same vertex. With this definition, vertices can be identified by changing the PER on `α` like the example below.

```lean4
def VxIdentify (G : PERGraph α β) (S : Set α) : PERGraph α β where
  vertexRel u v := vertexRel u v ∨ (u ∈ S ∧ v ∈ S)
  IsLink e u v := ∃ x y, (u = x ∨ u ∈ S ∧ x ∈ S) ∧ (v = y ∨ v ∈ S ∧ y ∈ S) ∧ G.IsLink e x y
  ...
```

However, this comes with some downsides.

Previously, since every object in `α` represented a unique vertex (or was not in the ground set), with some bijection fudging in our heads, you could imagine that `u` IS the vertex.

However, with this setup, `u : α` no longer uniquely represents a vertex, so the label `u` and the vertex represented by `u` are mathematically different objects. This is a mental overhead that does not exist in the usual graph theory.

Furthermore, having to control what happens to the vertices indirectly via the labels is not great. For example, given `S : Set α`, I would like to find `δ(S)`, the edge cut of `S`, the set of edges with exactly one end in `S`. Previously, it can be defined as `{e | ∃ u v, u ∈ S ∧ v ∉ S ∧ G.IsLink e u v}` (the set of edges between two vertices, one in `S` and another outside `S`). With this setup, it would have to be `{e | ∃ u v, u ∈ S ∧ (v ∉ S ∧ ∀ w ∈ S, ¬ vertexRel v w) ∧ G.IsLink e u v}` (the set of edges between two vertices, one in `S` and another not only outside `S` but also not vertex-related to any vertex in `S`). Also, every time we define a new property/function on graphs, we have to prove a lemma that the outputs agree when rewriting a label with a vertex-related one. These are problems that arise repeatedly, even in parts of the API that have nothing to do with contraction/identification. I am not saying it can't be done, but these are added complexities that do not exist in the usual graph theory.

I would like to step back and talk about what exactly is needed to facilitate edge contraction. First, we should be able to do contraction *in type*, i.e., the type of the input graph and the output graph should be the same. Without this, a minor graph would have a vertex type that is a subtype of a quotient of the original vertex type. Then, showing that a minor relation is transitive requires that a subtype of a quotient of a subtype of a quotient has an `Equiv` with a subtype of a quotient. The fact that the minor relation is transitive is a very trivial lemma in graph theory, yet, without in-type contraction, I do not know a way to prove it without spending a lot of time.

Semantically, this means that `Graph α β` contains not only graphs with those vertices and edges, but also all possible deletions and contractions of them. For that, we need some relabelling function `f` returning values in `α` to determine how the new vertices are labelled. The question is: when should `f` be provided?

To the best of my knowledge, there are three different answers to this question: *when contracting*, *when the graph is created*, and *when `α` is created*. The first answer, *when contracting*, leads to my original solution of asking the user to provide a function every single time they want to contract an edge. It looks like this:

## Old graph definition (requires function for every contraction)
```lean4
structure Graph (α β : Type*) where
  /-- The vertex set. -/
  vertexSet : Set α
  /-- The binary incidence predicate, stating that `x` and `y` are the ends of an edge `e`.
  If `G.IsLink e x y` then we refer to `e` as an `edge` and `x` and `y` as the `left` and `right`. -/
  IsLink : β → α → α → Prop
  /-- The edge set. -/
  edgeSet : Set β := {e | ∃ x y, IsLink e x y}
  /-- If `e` goes from `x` to `y`, it goes from `y` to `x`. -/
  isLink_symm : ∀ ⦃e⦄, e ∈ edgeSet → (Symmetric <| IsLink e)
  /-- An edge is incident with at most one pair of vertices. -/
  eq_or_eq_of_isLink_of_isLink : ∀ ⦃e x y v w⦄, IsLink e x y → IsLink e v w → x = v ∨ x = w
  /-- An edge `e` is incident to something if and only if `e` is in the edge set. -/
  edge_mem_iff_exists_isLink : ∀ e, e ∈ edgeSet ↔ ∃ x y, IsLink e x y := by exact fun _ ↦ Iff.rfl
  /-- If some edge `e` is incident to `x`, then `x ∈ V`. -/
  left_mem_of_isLink : ∀ ⦃e x y⦄, IsLink e x y → x ∈ vertexSet

def VxIdentify (G : Graph α β) (f : α → α) : Graph α β where
  vertexSet := f '' G.vertexSet
  IsLink e x y := ∃ x' y', G.IsLink e x' y' ∧ x = f x' ∧ y = f y'
  ...

/-- This is a valid contraction iff `f` sends exactly the vertices connected by edges in `C` to the same place. -/
def contract (G : Graph α β) (f : α → α) (C : Set β) := 
  (VxIdentify G f).edgeDelete C
```
As mentioned before, this would require the user to create and remember a function for every single contraction. Also, for any sane use case, the user would further need to prove that the function is *aligned* with the edge set. That is, the vertices that are mapped to the same vertex by `f` are exactly the vertices connected by edges in `C`.

The second option is to attach the function to the graph as a structure field. This allows the contraction to be performed without supplying a function every single time. However, it would need to be supplied whenever you create a graph. When augmenting a graph, there is a solution of simply retaining the function, but creating a graph from nothing would be harder. Also, two graphs would not be the same if they have different functions attached to them, even though they are the same graphically.

The last option is to attach the function to `α`. This enforces one choice of function for all graphs defined on `α`. This is currently my favourite option.

## Graph with `Set α`
```lean4
import Mathlib.Order.SupIndep

structure Partition (α : Type*) [CompleteLattice α] where
  parts : Set α
  indep : sSupIndep parts
  bot_not_mem : ⊥ ∉ parts

def Partition.supp {α} [CompleteLattice α] (P : Partition α) := sSup P.parts

def Partition.flatten {α} [CompleteLattice α] (Q : Partition (Set α)) {P : Partition α} 
    (hQ : Q.supp = P.parts) : Partition α where
  parts := sSup '' Q.parts
  ...

structure Graph (α β : Type*) where
  vertexPartition : Partition (Set α)
  /-- The vertex set. Note that each vertex has type `Set α` rather than `α`. -/
  vertexSet : Set (Set α) := vertexPartition.parts
  /-- The vertex set is equal to the parts of the vertex partition. -/
  vertexSet_eq_parts : vertexPartition.parts = vertexSet := by rfl
  /-- The binary incidence predicate, stating that `x` and `y` are the ends of an edge `e`.
  If `G.IsLink e x y` then we refer to `e` as `edge` and `x` and `y` as `left` and `right`. -/
  IsLink : β → Set α → Set α → Prop
  /-- The edge set. -/
  edgeSet : Set β := {e | ∃ x y, IsLink e x y}
  /-- If `e` goes from `x` to `y`, it goes from `y` to `x`. -/
  isLink_symm : ∀ ⦃e⦄, e ∈ edgeSet → (Symmetric <| IsLink e)
  /-- An edge is incident with at most one pair of vertices. -/
  eq_or_eq_of_isLink_of_isLink : ∀ ⦃e x y v w⦄, IsLink e x y → IsLink e v w → x = v ∨ x = w
  /-- An edge `e` is incident to something if and only if `e` is in the edge set. -/
  edge_mem_iff_exists_isLink : ∀ e, e ∈ edgeSet ↔ ∃ x y, IsLink e x y := by exact fun _ ↦ Iff.rfl
  /-- If some edge `e` is incident to `x`, then `x ∈ V`. -/
  left_mem_of_isLink : ∀ ⦃e x y⦄, IsLink e x y → x ∈ vertexSet

def VxIdentify {α β} (G : Graph α β) (P : Partition (Set (Set α))) (hP : P.supp = G.vertexSet) : Graph α β where
  vertexPartition := P.flatten (G.vertexSet_eq_parts ▸ hP) 
  IsLink e x y := ∃ x' y', G.IsLink e x' y' ∧ x' ⊆ x ∧ y' ⊆ y
  ...

/-- Connected components as a partition of the set of vertices. -/
def connPartition (G : Graph α β) : Partition (Set (Set α)) := sorry

lemma supp_connPartition (G : Graph α β) : (connPartition G).supp = G.vertexSet := sorry

/-- Restrict the edge set to a subset. -/
def edgeRestrict (G : Graph α β) (E : Set β) : Graph α β where
  vertexPartition := G.vertexPartition
  vertexSet := G.vertexSet
  edgeSet := G.edgeSet ∩ E
  IsLink e u v := G.IsLink e u v ∧ e ∈ E
  ...

def contract (G : Graph α β) (C : Set β) : Graph α β := 
  edgeRestrict (VxIdentify G (connPartition (edgeRestrict G C)) (supp_connPartition G)) (G.edgeSet \ C)
```

The glaring issue with my claim that these three are the only options is: where does PERGraph belong? My answer is `α`... with an asterisk. PERGraph is very close mechanically to the second option, as it attaches some extra information in the structure field. However, it comes with a relation, not a function, and unfortunately breaks label uniqueness. Actually, the way it facilitates contraction is very close to the last option. As the name suggests, PERGraph involves partially partitioning the elements of `α` into several parts where elements in the same part represent the same vertex. A very simple transformation that solves the uniqueness problem is to imagine each part represents a vertex rather than the individual labels in it. The type for the vertices is now `Set α`, sure, but it is exactly the same thing as PERGraph without the uniqueness problem. Through this lens, we notice that PERGraph is equivalent to a graph with `Set α` as its vertex type, which naturally comes with a `union`/`sUnion` function: with ℕ as the vertex type, identifying vertices `1` and `2` as vertex-related is equivalent to merging `{1}` and `{2}` by relabelling them as `{1} ∪ {2} = {1, 2}`.

I am fairly sure that the full generality of the vertex type is not just the set structure (or `CompleteAtomicBooleanAlgebra α`, which is order-isomorphic to the set structure). If we stick with `sup` as the operation, either `CompleteLattice α` or `Order.Frame α` seem sufficient, as `CompleteLattice α` is required for `Partition α` but `Order.Frame α` is required for `CompleteLattice (Partition α)`, which could be handy. 

## Graph with `CompleteLattice α` assumption
```lean4
import Mathlib.Order.SupIndep

structure Partition (α : Type*) [CompleteLattice α] where
  parts : Set α
  indep : sSupIndep parts
  bot_not_mem : ⊥ ∉ parts

structure Graph (α β : Type*) [CompleteLattice α] where
  vertexPartition : Partition α
  /-- The vertex set. -/
  vertexSet : Set α := vertexPartition.parts
  /-- The vertex set is equal to the parts of the vertex partition. -/
  vertexSet_eq_parts : vertexPartition.parts = vertexSet := by rfl
  /-- The binary incidence predicate, stating that `x` and `y` are the ends of an edge `e`.
  If `G.IsLink e x y` then we refer to `e` as `edge` and `x` and `y` as `left` and `right`. -/
  IsLink : β → α → α → Prop
  /-- The edge set. -/
  edgeSet : Set β := {e | ∃ x y, IsLink e x y}
  /-- If `e` goes from `x` to `y`, it goes from `y` to `x`. -/
  isLink_symm : ∀ ⦃e⦄, e ∈ edgeSet → (Symmetric <| IsLink e)
  /-- An edge is incident with at most one pair of vertices. -/
  eq_or_eq_of_isLink_of_isLink : ∀ ⦃e x y v w⦄, IsLink e x y → IsLink e v w → x = v ∨ x = w
  /-- An edge `e` is incident to something if and only if `e` is in the edge set. -/
  edge_mem_iff_exists_isLink : ∀ e, e ∈ edgeSet ↔ ∃ x y, IsLink e x y := by exact fun _ ↦ Iff.rfl
  /-- If some edge `e` is incident to `x`, then `x ∈ V`. -/
  left_mem_of_isLink : ∀ ⦃e x y⦄, IsLink e x y → x ∈ vertexSet
```

Of course, you could go further and create a bespoke class that contains the operation and the exact axioms we need for contraction—something like the following:

## Graph with bespoke class
```lean4
import Mathlib.Order.SupIndep

class contractFun (α : Type*) where
  f : Set α → α
  /-- This is not strictly necessary for identification, but this is required for the property 
    `G / (C ∪ D) = G / C / D`. -/
  partialEval : ∀ S T : Set α, S ⊆ T → f T = f (T \ S ∪ {f S})
  singleton : ∀ a : α, f {a} = a

variable {α β : Type*} [contractFun α]

structure Graph (α β : Type*) [contractFun α] where
  vertexSet : Set α
  /-- When identifying vertices, the new label should not clash with other labels. -/
  contractable : ∀ S T : Set α, S ⊆ vertexSet → T ⊆ vertexSet → Disjoint S T → contractFun.f S ≠ contractFun.f T
  IsLink : β → α → α → Prop
  edgeSet : Set β := {e | ∃ x y, IsLink e x y}
  isLink_symm : ∀ ⦃e⦄, e ∈ edgeSet → (Symmetric <| IsLink e)
  eq_or_eq_of_isLink_of_isLink : ∀ ⦃e x y v w⦄, IsLink e x y → IsLink e v w → x = v ∨ x = w
  edge_mem_iff_exists_isLink : ∀ e, e ∈ edgeSet ↔ ∃ x y, IsLink e x y := by exact fun _ ↦ Iff.rfl
  left_mem_of_isLink : ∀ ⦃e x y⦄, IsLink e x y → x ∈ vertexSet

structure Partition (α : Type*) [CompleteLattice α] where
  parts : Set α
  indep : sSupIndep parts
  bot_not_mem : ⊥ ∉ parts

def Partition.supp {α} [CompleteLattice α] (P : Partition α) := sSup P.parts

def VxIdentify (G : Graph α β) (P : Partition (Set α)) (hP : P.supp = G.vertexSet) : Graph α β where
  vertexPartition := {parts := f '' P.parts, ...} 
  IsLink e x y := ∃ x' y', G.IsLink e x' y' ∧ x' ≤ x ∧ y' ≤ y
  ...

/-- Connected components as a partition of the set of vertices. -/
def connPartition (G : Graph α β) : Partition (Set α) := sorry

lemma supp_connPartition (G : Graph α β) : (connPartition G).supp = G.vertexSet := sorry

/-- Restrict the edge set to a subset. -/
def edgeRestrict (G : Graph α β) (E : Set β) : Graph α β where
  vertexSet := G.vertexSet
  edgeSet := G.edgeSet ∩ E
  IsLink e u v := G.IsLink e u v ∧ e ∈ E
  ...

def contract (G : Graph α β) (C : Set β) : Graph α β := 
  edgeRestrict (VxIdentify G (connPartition (edgeRestrict G C)) (supp_connPartition G)) (G.edgeSet \ C)
```

My worry is something like this happening:\

Graph theorist: Oh, I heard Lean is cool! Let me try doing some graph theory with it!\

Lean: Okay, do you want to create a graph?\

Graph theorist: Yes!\

Lean: Sure, just give me a proof that your vertex type is a `CompleteLattice`.\

Graph theorist: **?????**

However, I do not have a better idea than requiring the vertex type to be either `Set α` or requiring an instance of `CompleteLattice α`. If you have a suggestion, please let me know. I would very much appreciate it.
