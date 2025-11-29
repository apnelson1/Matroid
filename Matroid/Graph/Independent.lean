import Matroid.ForMathlib.Card
import Matroid.Graph.Simple

variable {α β : Type*} {x y z u v : α} {e f : β} {G H : Graph α β} {A : Set β}
  {W w w₁ w₂ : WList α β} {A S T : Set α}

open Graph WList Set

namespace Graph

@[mk_iff isIndependent_iff']
structure IsIndependent (G : Graph α β) (S : Set α) : Prop where
  subset : S ⊆ V(G)
  pairwise_nonadj : S.Pairwise (fun x y ↦ ¬ G.Adj x y)

lemma isIndependent_iff (hS : S ⊆ V(G)) :
    G.IsIndependent S ↔ ∀ ⦃x y⦄, x ∈ S → y ∈ S → x ≠ y → ¬ G.Adj x y := by
  rw [isIndependent_iff', and_iff_right hS]
  simp +contextual [Set.Pairwise, iff_def]

alias ⟨IsIndependent.not_adj, _⟩ := isIndependent_iff

lemma isIndependent_iff_forall_eq_of_adj (hS : S ⊆ V(G)) :
    G.IsIndependent S ↔ ∀ ⦃x y⦄, G.Adj x y → x ∈ S → y ∈ S → x = y := by
  rw [isIndependent_iff hS]
  grind

def IndepNumLE (G : Graph α β) (n : ℕ∞) : Prop :=
  ∀ S, G.IsIndependent S → S.encard ≤ n

structure IsMaxIndependent (G : Graph α β) (S : Set α) : Prop where
  isIndependent : G.IsIndependent S
  max : ∀ A, G.IsIndependent A → A.encard ≤ S.encard

lemma IsIndependent.not_adj_of_simple [G.Simple] (hS : G.IsIndependent S) :
    ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → ¬ G.Adj x y := by
  intro x hx y hy
  obtain (rfl | hnee) := eq_or_ne x y
  · exact G.not_adj_self x
  · exact hS.2 hx hy hnee

@[simp]
lemma isIndependent_empty : G.IsIndependent ∅ := ⟨empty_subset _, pairwise_empty _⟩

@[simp]
lemma isIndependent_singleton : G.IsIndependent {v} ↔ v ∈ V(G) :=
  ⟨fun h => by simpa using h.1, fun h => ⟨(by simpa), pairwise_singleton ..⟩⟩

lemma isIndependent_of_subsingleton [G.Simple] (hSV : S ⊆ V(G)) (hS : S.Subsingleton) :
    G.IsIndependent S := by
  obtain (rfl | ⟨v, rfl⟩) := hS.eq_empty_or_singleton
  · simp
  exact ⟨hSV, pairwise_singleton ..⟩

lemma isIndependent_mt [G.Simple] (hSV : S ⊆ V(G)) (hS : ¬G.IsIndependent S) :
    ∃ u ∈ S, ∃ v ∈ S, G.Adj u v := by
  simp only [isIndependent_iff hSV] at hS
  grind

@[simp]
lemma isIndependent_pair_iff_of_ne (h_ne : x ≠ y) (hx : x ∈ V(G)) (hy : y ∈ V(G)) :
    G.IsIndependent {x, y} ↔ ¬ G.Adj x y := by
  refine ⟨fun h ↦ (h.2 (mem_insert x {y}) (mem_insert_of_mem x rfl) h_ne), ?_⟩
  exact fun hc ↦ ⟨pair_subset hx hy, pairwise_pair.mpr fun _ ↦ ⟨hc, not_symm_not hc⟩⟩

lemma IsIndependent.mono (hS : G.IsIndependent S) (hle : A ⊆ S) : G.IsIndependent A :=
  ⟨hle.trans hS.subset, hS.pairwise_nonadj.mono hle⟩

lemma IsMaxIndependent.subset (hS : G.IsMaxIndependent S) : S ⊆ V(G) := hS.isIndependent.subset

@[simp]
lemma IsMaxIndependent.bot_iff : (⊥ : Graph α β).IsMaxIndependent S ↔ S = ∅ := by
  refine ⟨fun ⟨h, _⟩ ↦ by simpa using h.subset, ?_⟩
  rintro rfl
  constructor
  · simp
  intro A hA
  simpa using hA.subset

@[simp]
lemma isMaxIndependent_empty_iff : G.IsMaxIndependent ∅ ↔ G = ⊥ := by
  refine ⟨?_, ?_⟩
  · rw [← not_imp_not, ← ne_eq, ne_bot_iff]
    intro ⟨x, hx⟩ h
    simpa using h.2 _ <| isIndependent_singleton.mpr hx
  rintro rfl
  simp

@[simp]
lemma IsMaxIndependent.empty_iff (hS : G.IsMaxIndependent S) : S = ∅ ↔ G = ⊥ := by
  refine ⟨?_, ?_⟩ <;>
  · rintro rfl
    simpa using hS

lemma isIndependent_insert [G.Simple] {S : Set α} {s : α} (hS : G.IsIndependent S) (hs : s ∈ V(G)) :
  G.IsIndependent (insert s S) ↔ ∀ x, x ∈ S → ¬ G.Adj x y := by
refine ⟨?_, ?_ ⟩
· intro h x hxS
  -- Need to use h.not_adj_of_simple
  sorry
intro h
have hV : (insert s S) ⊆ V(G) := by sorry
apply (isIndependent_iff_forall_eq_of_adj hV).2
intro x y hAdj hx hy
simp only [mem_insert_iff] at hx
simp only [mem_insert_iff] at hy
obtain rfl | hxS := hx
· obtain rfl | hyS := hy
  · sorry
  sorry
obtain rfl | hyS := hy
· sorry
sorry

--You are going to need to use (isIndependent_iff_forall_eq_of_adj hS.subset).1
