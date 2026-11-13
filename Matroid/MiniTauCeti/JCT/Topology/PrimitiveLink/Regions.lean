module

public import Matroid.MiniTauCeti.JCT.Topology.PrimitiveLink
public import Matroid.MiniTauCeti.JCT.Topology.ConnectedComponent

/-!
# Conditional regions of primitive links

Primitive-link accessibility identifies the frontier of a complementary component.
Separation of the other links supplies a component with prescribed frontier, without asserting
that these components exhaust the complement.
-/

@[expose] public section

open Set Topology Function

/-- Primitive-link accessibility in every relative neighborhood identifies the frontier
of a complementary component. -/
theorem IsClosed.frontier_connectedComponentIn_compl_eq_of_accessibility
    {X : Type*} [TopologicalSpace X]
    [LocallyConnectedSpace X] {C : Set X} (hC : IsClosed C)
    {p : X} (haccess : ∀ O : Set X, IsOpen O → (O ∩ C).Nonempty →
      ∃ q ∈ O ∩ C, ∃ L : Set X, IsPrimitiveLink L p q ∧
        L \ {q} ⊆ connectedComponentIn Cᶜ p) :
    frontier (connectedComponentIn Cᶜ p) = C := by
  refine hC.frontier_connectedComponentIn_compl_subset.antisymm ?_
  intro z hz
  rw [frontier_eq_closure_inter_closure]
  refine ⟨?_, subset_closure (fun h ↦ connectedComponentIn_subset _ _ h hz)⟩
  apply mem_closure_iff.mpr
  intro O hO hzO
  obtain ⟨q, hq, L, hL, hsub⟩ := haccess O hO ⟨z, hzO, hz⟩
  have hsmall : L \ {p, q} ⊆ connectedComponentIn Cᶜ p :=
    fun w hw ↦ hsub ⟨hw.1, fun heq ↦ hw.2 (Or.inr heq)⟩
  have hqcl : q ∈ closure (connectedComponentIn Cᶜ p) :=
    closure_mono hsmall
      (hL.subset_closure_diff_endpoints hL.right_mem)
  exact mem_closure_iff.mp hqcl O hO hq.1

namespace IsPrimitiveLink

variable {X : Type*} [TopologicalSpace X] {a b : X} {ι : Type*}

private theorem opposite_region (A : ι → Set X)
    (hA : ∀ i, IsPrimitiveLink (A i) a b)
    (hmeet : Pairwise fun i j ↦ A i ∩ A j ⊆ {a, b}) (i : ι)
    (hsep : ∃ U V : Set X,
      IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧ Disjoint U V ∧
      U ∪ V = (⋃ j ∈ ({i}ᶜ : Set ι), A j)ᶜ ∧
      frontier U = ⋃ j ∈ ({i}ᶜ : Set ι), A j ∧
      frontier V = ⋃ j ∈ ({i}ᶜ : Set ι), A j) :
    ∃ W : Set X, IsOpen W ∧ IsConnected W ∧
      (∃ w ∈ (⋃ k, A k)ᶜ, W = connectedComponentIn (⋃ k, A k)ᶜ w) ∧
      frontier W = ⋃ j ∈ ({i}ᶜ : Set ι), A j := by
  obtain ⟨U, V, hU, hV, hcU, hcV, hd, hcover, hfU, hfV⟩ := hsep
  let J := ⋃ j ∈ ({i}ᶜ : Set ι), A j
  have hinter : A i \ {a, b} ⊆ Jᶜ := by
    rintro x ⟨hxi, hx⟩ hJ
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hJ
    exact hx (hmeet (Ne.symm hj) ⟨hxi, hxj⟩)
  have hsub : A i \ {a, b} ⊆ U ∪ V := hcover.symm ▸ hinter
  have choose_opposite {R S : Set X} (hR : IsOpen R) (hcR : IsConnected R)
      (hRS : Disjoint R S) (hRJ : R ⊆ Jᶜ) (hfR : frontier R = J)
      (hS : A i \ {a, b} ⊆ S) :
      ∃ W : Set X, IsOpen W ∧ IsConnected W ∧
        (∃ w ∈ (⋃ k, A k)ᶜ, W = connectedComponentIn (⋃ k, A k)ᶜ w) ∧
        frontier W = J := by
    have hdense : Disjoint R (closure (A i \ {a, b})) :=
      (hRS.mono_right hS).closure_right hR
    have hRT : Disjoint R (⋃ k, A k) := by
      refine disjoint_left.mpr fun x hx hT ↦ ?_
      obtain ⟨k, hxk⟩ := mem_iUnion.mp hT
      by_cases hki : k = i
      · exact hdense.notMem_of_mem_left hx ((hA i).subset_closure_diff_endpoints (hki ▸ hxk))
      · exact hRJ hx (mem_iUnion₂.mpr ⟨k, hki, hxk⟩)
    obtain ⟨w, hw⟩ := hcR.nonempty
    refine ⟨R, hR, hcR, ⟨w, hRT.subset_compl_right hw, ?_⟩, hfR⟩
    exact eq_connectedComponentIn_of_frontier_subset hR hcR.isPreconnected hRT
      (hfR ▸ iUnion₂_subset fun j _ ↦ subset_iUnion A j) hw
  rcases (hA i).isConnected_diff_endpoints.isPreconnected.subset_or_subset hU hV hd hsub
      with hSU | hSV
  · exact choose_opposite hV hcV hd.symm (hcover ▸ subset_union_right) hfV hSU
  · exact choose_opposite hU hcU hd (hcover ▸ subset_union_left) hfU hSV

/-- The omitted link is determined by the frontier of its region. -/
theorem injective_regions (A : ι → Set X) (hA : ∀ i, IsPrimitiveLink (A i) a b)
    (hmeet : Pairwise fun i j ↦ A i ∩ A j ⊆ {a, b}) {W : ι → Set X}
    (hf : ∀ i, frontier (W i) = ⋃ j ∈ ({i}ᶜ : Set ι), A j) : Injective W := by
  intro i j heq
  by_contra hij
  obtain ⟨x, hxi, hx⟩ := (hA i).diff_endpoints_nonempty
  have hxj : x ∈ frontier (W j) := hf j ▸ mem_iUnion₂.mpr ⟨i, hij, hxi⟩
  rw [← heq, hf i] at hxj
  obtain ⟨k, hki, hxk⟩ := mem_iUnion₂.mp hxj
  exact hx (hmeet (Ne.symm hki) ⟨hxi, hxk⟩)

/-- Each omitted link determines a component bounded by the remaining links. -/
theorem candidate_regions_of_separation (A : ι → Set X)
    (hA : ∀ i, IsPrimitiveLink (A i) a b)
    (hmeet : Pairwise fun i j ↦ A i ∩ A j ⊆ {a, b})
    (hsep : ∀ i, ∃ U V : Set X,
      IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧ Disjoint U V ∧
      U ∪ V = (⋃ j ∈ ({i}ᶜ : Set ι), A j)ᶜ ∧
      frontier U = ⋃ j ∈ ({i}ᶜ : Set ι), A j ∧
      frontier V = ⋃ j ∈ ({i}ᶜ : Set ι), A j) :
    ∃ W : ι → Set X,
      (∀ i, IsOpen (W i)) ∧ (∀ i, IsConnected (W i)) ∧
      (Pairwise fun i j ↦ Disjoint (W i) (W j)) ∧
      (∀ i, ∃ w ∈ (⋃ k, A k)ᶜ, W i = connectedComponentIn (⋃ k, A k)ᶜ w) ∧
      ∀ i, frontier (W i) = ⋃ j ∈ ({i}ᶜ : Set ι), A j := by
  classical
  choose W hO hC hcomp hf using fun i ↦ opposite_region A hA hmeet i (hsep i)
  refine ⟨W, hO, hC, ?_, hcomp, hf⟩
  intro i j hij
  have hne : W i ≠ W j := fun h ↦ hij (injective_regions A hA hmeet hf h)
  obtain ⟨u, -, hu⟩ := hcomp i
  obtain ⟨v, -, hv⟩ := hcomp j
  refine disjoint_left.mpr fun x hxi hxj ↦ hne ?_
  simp only [hu, hv] at hxi hxj ⊢
  exact (connectedComponentIn_eq hxi).trans (connectedComponentIn_eq hxj).symm

end IsPrimitiveLink
