import Matroid.Graph.Matching.AugmentingPath

namespace Graph

variable {α β : Type*} {G H C : Graph α β} {S X Y : Set α} {M M' : Set β} {u v x y z : α} {e f : β}

open Set symmDiff WList

/-! ### Tutte-Berge formula -/

-- Matroid exercise 4 Q2

/-
\subsection{Part (a)}
Show that, if $S \subseteq E(M)$ is a set of size at least $2$ whose two-element subsets are
all series pairs of $M$, then $r_M(E(M) - S) = r(M) - |S| + 1$.

\begin{proof}
  Consider $r_{M^*}(S)$. In $M^*$, $S$ is subset of a parallel class so $r_{M^*}(S) = 1$.
  Simultaneously, $r_{M^*}(S) = r_M(E(M) - S) + |S| - r(M)$.
  By rearranging and substituting, we have $r_M(E(M) - S) = r(M) - |S| + 1$.
\end{proof}-/
lemma _root_.Matroid.eRk_pos_of_mem_nonloop {M : Matroid α} {e : α} (heX : e ∈ X)
    (he : M.IsNonloop e) : 0 < M.eRk X := by
  refine Order.one_le_iff_pos.mp ?_
  rw [← he.eRk_eq]
  apply M.eRk_mono
  simpa

lemma _root_.Matroid.fooA {M : Matroid α} (hS : S ⊆ M.E) (hnt : S.Nontrivial)
    (h : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → M.Series a b) : M.eRk (M.E \ S) + S.encard = M.eRank + 1 := by
  obtain ⟨s, hs, t, ht, hne⟩ := hnt
  have hnls := (h s hs t ht hne).isNonloop_left
  suffices M.dual.eRk S = 1 by
    rw [← this, add_comm M.eRank, M.eRk_dual_add_eRank S hS]
  refine le_antisymm ?_ (Order.one_le_iff_pos.mpr <| M✶.eRk_pos_of_mem_nonloop hs hnls)
  rw [← hnls.eRk_eq, ← M✶.eRk_closure_eq {s}]
  apply M✶.eRk_mono
  intro x hxS
  obtain rfl | hxs := eq_or_ne x s
  · exact M✶.subset_closure _ (by simpa using hnls.mem_ground) (by rfl)
  exact (h x hxS s hs hxs).mem_closure

/-
\subsection{Part (b)}
Let $G$ be a graph with vertex set $V$. We say that a set $X \subseteq V$ is matchable in $G$
if there is a matching of $G$ whose vertex set contains $X$. Show (using augmenting paths)
that the matchable sets of $G$ are the independent sets of a matroid on $V$. (We call this the
matchable sets matroid of $G$; note that this matroid has rank $2\nu(G)$).

\begin{proof}
\begin{itemize}
  \item[(I1)] $\emptyset$ is trivially matchable.
  \item[(I2)] Let $I$ is matchable. Then, for $J \subseteq I$, WTS $J$ is matchable using the
  exactly same matching.
  \item[(I3)] Let $I$ and $J$ be matchable s.t. $|I| < |J|$.
  Let $M_I$ and $M_J$ be the matchings of $G$ containing $I$ and $J$ respectively.
  Consider the symmetric difference $M_I \operatorname{\Delta} M_J$.
  Let $G' := (V(G), M_I \operatorname{\Delta} M_J)$.
  Since the max degree of $G'$ is at most $2$, $G'$ consists of alternating paths and cycles.
  Every vertex in $J \setminus I$ and $I \setminus J$ is an endpoint of an alternating path in $G'$.
  By $|I| < |J|$, $|I \setminus J| < |J \setminus I|$.
  If for every vertex in $J \setminus I$, the other endpoint is in $I \setminus J$, then
  we have a bijection between $J \setminus I$ and $I \setminus J$ which is a contradiction.
  Therefore, there exists some vertex $v \in J \setminus I$ in an alternating path in $G'$ s.t.
  the other endpoint is not in $I \setminus J$.
  If the other endpoint is matched by $M_J$, then the path is augmenting.
  Otherwise, the other endpoint is matched by $M_I$ but not in $I$, then the path is alternating.
  Regardless, we can create a new matching $M_I' := M_I \operatorname{\Delta} P$ where $P$ is the
  path in $G'$ containing $v$.
  This new matching matches all $I$ and also $v \in J$.
  Therefore, $I \cup \{v\}$ is matchable.
\end{itemize}
\end{proof}-/
def matchingIndepMatroid (G : Graph α β) : IndepMatroid α where
  E := V(G)
  Indep := fun S ↦ ∃ M, G.IsMatching M ∧ S ⊆ V(G, M)
  indep_empty := by
    sorry
  indep_subset := by
    sorry
  indep_aug := by
    sorry
  indep_maximal := by
    sorry
  subset_ground := by
    sorry

def matchingMatroid (G : Graph α β) : Matroid α := G.matchingIndepMatroid.matroid

/-
\subsection{Part (c)}
Let $G$ be a graph such that, for every vertex $v$ of $G$, there is a matching of $G$ of
size $\nu(G)$ whose vertex set does not include $v$.
\begin{enumerate}
    \item[i.] Show that the matchable sets matroid of $G$ has no coloop, and that every
    pair of adjacent vertices of $G$ is a series pair in this matroid.
    \item[ii.] Show that $G$ has a matching avoiding exactly one vertex from each of its
    components (and hence that each component of $G$ has an odd number of vertices).
\end{enumerate}

\begin{proof}
  \begin{enumerate}
    \item[i.] For every vertex $v$, there is a matching $M$ of $G$ of size $\nu(G)$ s.t. $v$ is not
    matched by $M$.
    Let $V(M)$ be the set of vertices matched by $M$.
    Then, $|V(M)| = 2 \nu(G)$ so $V(M)$ is a basis of the matchable sets matroid of $G$.
    Therefore, $v$ is not a coloop in the matchable sets matroid of $G$.
    $v$ was arbitrary, so every vertex is not a coloop in the matchable sets matroid of $G$.

    Let $u$ and $v$ be adjacent vertices of $G$.
    WTS: $\{u, v\}$ is a cocircuit or $E(G) \setminus \{u, v\}$ is a hyperplane.
    Since for every vertex $v$, there is a matching $M$ of $G$ of size $\nu(G)$ s.t. $v$ is not
    matched by $M$, the rank of $E(G) \setminus \{u\}$ is $2 \nu(G)$ and the rank of $E(G) \setminus \{v\}$
    is also $2 \nu(G)$.
    If $M$ does not match $v$, then we can extend $M$ to a bigger matching by adding the edge $uv$.
    so $v$ must be matched by $M$.
    Therefore, $E(G) \setminus \{u, v\}$ has rank $2 \nu(G) - 1$.
    As adding another element to $E(G) \setminus \{u, v\}$ increases the rank,
    $E(G) \setminus \{u, v\}$ is a closure.
    Since it has the rank $2 \nu(G) - 1$, it is a hyperplane.
    Therefore, $\{u, v\}$ is a cocircuit.
    $u$ and $v$ were arbitrary, so every pair of adjacent vertices is a series pair in the matchable sets matroid of $G$.
    \item[ii.] Consider a component $C$ of $G$.
    Then, by part i and the transitivity of series and parallel, $V(C)$ is a set whose two-element subsets
    are all series pairs.
    Therefore, the rank of $E(M) \setminus V(C)$ is $2 \nu(C) - |V(C)| + 1$.
    By diminishing return,
    \[|V(C)| - 1 = r(M) - r_M(E(M) \setminus V(C)) \leq r_M(V(C)) - r_M(\emptyset) = r_M(V(C))\]
    At the same time, $r_M(V(C)) < |V(C)|$ because a matching of $G$ is a disjoint union of matchings
    of each component and for each vertex, there is a matching of $G$ of size $\nu(G)$ that does
    not contain the vertex so the entire $V(C)$ is not matchable simultaneously.
    Therefore, $r_M(V(C)) = |V(C)| - 1$.
    Since $C$ was arbitrary, this is true for all components of $G$.
    Therefore, $G$ has a matching avoiding exactly one vertex from each of its components.
  \end{enumerate}
\end{proof}-/

lemma inessential_of_not_mem (hx : x ∉ V(G)) : G.inessential x := by
  sorry

lemma matchingMatroid.noColoop (h : ∀ x, G.inessential x) (hx : x ∈ V(G)) :
    ¬ G.matchingMatroid.IsColoop x := by
  sorry

lemma matchingMatroid.seriesPair_of_adj (h : ∀ x, G.inessential x) (h : G.Adj x y) :
    G.matchingMatroid.Series x y := by
  sorry

lemma foo_of_forall_inessential (h : ∀ x, G.inessential x) :
    ∃ M, G.IsMatching M ∧ ∀ H : Graph α β, H.IsCompOf G → ∃! x, x ∈ V(H) ∧ x ∉ V(G, M) := by
  sorry

/-
\subsection{Part (d)}
Let $G$ be a graph with vertex set $V$.
\begin{enumerate}
    \item[i.] Let $X \subseteq V$ be maximal such that $\nu(G - X) = \nu(G) - |X|$. Show
    using (d) that $\nu(G - X) = \frac{1}{2}(|V - X| - \text{odd}(G - X))$, where `odd'
    denotes the number of components with an odd number of vertices. Hence determine
    $\nu(G)$ in terms of $X$.
    \item[ii.] Show that $\nu(G) \leq \frac{1}{2}(|V| + |Y| - \text{odd}(G - Y))$ for all
    $Y \subseteq V$.
    \item[iii.] Conclude that $\nu(G) = \min_{Z \subseteq V} \frac{1}{2}(|V| + |Z| -
    \text{odd}(G - Z))$. This is the Tutte-Berge formula for the size of a maximum matching
    in an arbitrary graph.
\end{enumerate}

\begin{proof}
  \begin{enumerate}
    \item[i.] Let $X$ be maximal with $\nu(G-X)=\nu(G)-|X|$ and put $H := G-X$.
    WTS: $\nu(H-v)=\nu(H)$ for every $v\in V(H)$. Let $v\in V(H)$. Removing a vertex
    decreases the matching number by at most one, so
    $\nu(G-(X\cup\{v\})) \ge \nu(G) - |X| - 1$. If equality held, then
    $\nu(G-(X\cup\{v\})) = \nu(G) - (|X|+1)$, contradicting the maximality of $X$.
    Therefore $\nu(G-(X\cup\{v\})) \ge \nu(G)-|X| = \nu(H)$. Also
    $\nu(G-(X\cup\{v\})) \le \nu(H)$. Hence $\nu(H-v)=\nu(H)$.

    Let $C$ be any component of $H$ and $v\in V(C)$. Since $\nu(H-v)=\nu(H)$ and matching
    number is additive over components, we have $\nu(C-v)=\nu(C)$. If $|C|$ were even, then
    $|C-v|$ is odd and $\nu(C-v) \le \lfloor(|C|-1)/2\rfloor < |C|/2 \le \nu(C)$, a
    contradiction. Thus $|C|$ is odd and necessarily $\nu(C)=(|C|-1)/2$, with $C-v$ having a
    perfect matching for every $v\in V(C)$. Therefore each component of $H$ is
    of odd order. Therefore $H$ has a matching that leaves exactly one vertex unmatched in
    each component, and hence
    \[
      \nu(G-X)=\nu(H)=\frac12\big(|V(H)| - \text{odd}(H)\big) = \frac12\big(|V-X| - \text{odd}(G-X)\big).
    \]
    Using $\nu(G)=\nu(G-X)+|X|$, we obtain
    \[
      \nu(G) = |X| + \frac12\big(|V-X| - \text{odd}(G-X)\big)
      = \frac12\big(|V| + |X| - \text{odd}(G-X)\big).
    \]

    \item[ii.] For any $Y\subseteq V$, in $G-Y$ every odd component contributes at least one
    unmatched vertex to any matching, so
    \[
      \nu(G-Y) \le \frac12\big(|V-Y| - \text{odd}(G-Y)\big).
    \]
    Also, removing $Y$ can destroy at most $|Y|$ edges of a matching, so
    $\nu(G) \le \nu(G-Y) + |Y|$. Combining,
    \[
      \nu(G) \le \frac12\big(|V-Y| - \text{odd}(G-Y)\big) + |Y|
      = \frac12\big(|V| + |Y| - \text{odd}(G-Y)\big).
    \]

    \item[iii.] Let $X$ be as in (i). Then
    $\nu(G) = \frac12\big(|V| + |X| - \text{odd}(G-X)\big)$. By (ii), for every
    $Z\subseteq V$ we have $\nu(G) \le \frac12\big(|V| + |Z| - \text{odd}(G-Z)\big)$.
    Therefore
    \[
      \nu(G) = \min_{Z\subseteq V} \frac12\big(|V| + |Z| - \text{odd}(G-Z)\big),
    \]
    which is the Tutte--Berge formula.
  \end{enumerate}
\end{proof}
-/
lemma tutte_berge_of_maximal_vertexDelete (hX : Maximal (fun X ↦ ν(G - X) = ν(G) - X.encard) X) :
    2 * ν(G - X) = (V(G) \ X).encard - (G - X).OddComponents.encard := by
  sorry

lemma tutte_berge_le [G.Finite] :
    2 * ν(G) ≤ (V(G).encard + Y.encard) - (G - Y).OddComponents.encard := by

  sorry

lemma tutte_berge [G.Finite] :
    2 * ν(G) = ⨅ Z ⊆ V(G), (V(G).encard + Z.encard) - (G - Z).OddComponents.encard := by
  sorry

-- def HasPerfectMatching (G : Graph α β) : Prop :=
--   ∃ M, G.IsMatching M ∧ V(G, M) = V(G)

-- def IsFactorCritical (G : Graph α β) : Prop :=
--   ∀ v ∈ V(G), (G - {v}).HasPerfectMatching

-- lemma HasPerfectMatching.encard_even [G.Finite] (h : G.HasPerfectMatching) :
--     Even V(G).encard := by
--   -- Proof: A perfect matching partitions vertices into pairs, so |V| = 2 * |M|.
--   sorry

-- lemma IsFactorCritical.encard_odd [G.Finite] (h : G.IsFactorCritical) :
--     Odd V(G).encard := by
--   -- Proof: For any v, G-v has a perfect matching, so |V|-1 is even, implying |V| is odd.
--   sorry

-- lemma IsFactorCritical.hasPerfectMatching_of_vertexDelete [G.Finite] (h : G.IsFactorCritical)
--     (v : α) (hv : v ∈ V(G)) : (G - {v}).HasPerfectMatching := by
--   -- Proof: Follows directly from the definition.
--   sorry

-- def OddComponents (G : Graph α β) : Set (Graph α β) :=
--   {H | H.IsOddCompOf G}

-- noncomputable def maxMatchingSize (G : Graph α β) : ℕ∞ :=
--   sSup {n | ∃ M, G.IsMatching M ∧ n = M.encard}

-- def gallai_D (G : Graph α β) : Set α :=
--   {v | ∃ M, G.IsMaxMatching M ∧ v ∉ V(G, M)}

-- noncomputable def gallai_A (G : Graph α β) : Set α :=
--   N(G, G.gallai_D) \ G.gallai_D

-- noncomputable def gallai_C (G : Graph α β) : Set α :=
--   V(G) \ (G.gallai_D ∪ G.gallai_A)

-- lemma IsMatching.encard_le_div_two [G.Finite] (hM : G.IsMatching M) :
--     2 * M.encard ≤ V(G).encard := by
--   -- Proof: Each edge covers 2 vertices, and edges are disjoint. So 2|M| ≤ |V|.
--   sorry

-- lemma IsMatching.odd_comp_deficiency (hM : G.IsMatching M) {H : Graph α β} (hH : H.IsOddCompOf G) :
--     V(H).encard - 2 * (M ∩ E(H)).encard ≥ 1 := by
--   -- Proof: M restricted to H is a matching. 2|M_H| ≤ |V(H)|. Since |V(H)| is odd, strict inequality holds.
--   sorry

-- lemma sum_matching_in_components_eq (hM : G.IsMatching M) (U : Set α) :
--     (∑ᶠ H ∈ (G - U).OddComponents, (M ∩ E(H)).encard) + (M ∩ E(G[U])).encard + (M ∩ E(G, U)).encard = M.encard := by
--   -- Proof: Edges of M are disjoint. They are either in G[U], between U and G-U, or inside components of G-U.
--   -- No edge can connect two different components of G-U.
--   sorry

-- theorem tutte_berge_weak_duality [G.Finite] {M : Set β} (hM : G.IsMatching M)
--     {U : Set α} (hU : U ⊆ V(G)) :
--     (G - U).OddComponents.encard + 2 * M.encard ≤ V(G).encard + U.encard := by
--   -- Proof:
--   -- |V(G)| = |U| + sum(|V(K)| for K in G-U)
--   -- |M| = |M_U| + |M_cross| + sum(|M_K|)
--   -- Use |V(K)| ≥ 2|M_K| + 1 for odd K, and |V(K)| ≥ 2|M_K| for even K.
--   -- Rearrange terms to show the inequality.
--   sorry

-- lemma gallai_D_mem_iff (v : α) :
--     v ∈ G.gallai_D ↔ ∃ M, G.IsMaxMatching M ∧ v ∉ V(G, M) := by
--   -- Proof: Definition.
--   sorry

-- lemma gallai_D_component_factor_critical (C : Graph α β) (hC : C.IsCompOf G[G.gallai_D]) :
--     C.IsFactorCritical := by
--   -- Proof: Let v ∈ C. v ∈ D implies some max matching M misses v.
--   -- M must match C-{v} perfectly, otherwise we could augment M or find a larger deficiency.
--   sorry

-- lemma gallai_A_matched_to_D_explicit (hM : G.IsMaxMatching M) (v : α) (hv : v ∈ G.gallai_A) :
--     ∃ u ∈ G.gallai_D, ∃ e ∈ M, G.IsLink e v u := by
--   -- Proof: v ∈ A means v ∈ N(D) \ D. v cannot be unmatched (else v ∈ D).
--   -- v cannot be matched to A or C (structural properties of Gallai-Edmonds).
--   -- So v is matched to D.
--   sorry

-- lemma gallai_C_perfect_matching_explicit (hM : G.IsMaxMatching M) :
--     G[G.gallai_C].HasPerfectMatching := by
--   -- Proof: If not, C would contain an unmatched vertex in some max matching, putting it in D.
--   sorry

-- lemma maxMatchingSize_eq_gallai_formula [G.Finite] :
--     let H := G - G.gallai_A
--     2 * G.maxMatchingSize + H.OddComponents.encard = V(G).encard + G.gallai_A.encard := by
--   -- Proof: Construct M by:
--   -- 1. Perfect matchings in C.
--   -- 2. Matching each v ∈ A to a distinct component of D.
--   -- 3. Near-perfect matchings in components of D (leaving one root per component).
--   -- Count the size and show it meets the bound.
--   sorry

-- theorem tutte_berge [G.Finite] :
--     ∃ U ⊆ V(G),
--     (G - U).OddComponents.encard + 2 * G.maxMatchingSize = V(G).encard + U.encard := by
--   -- Proof: Use U = G.gallai_A and the previous formula.
--   sorry

end Graph
