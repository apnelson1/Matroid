module

public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Separation.Connected

public section

/-!
# Point sets, frontiers, and counting of connected components

`ConnectedComponents.toSet` extracts the points of a component in its underlying space.
For a component of a subspace, its image under subtype inclusion is relatively closed;
`ConnectedComponents.inter_closure_image_toSet` states that fact in the ambient space.

Small facts about `connectedComponentIn` and the frontiers of its components: where the frontier of
a component lies, when that frontier is nonempty, and when an open set is a component of a
complement.

`ConnectedComponents.card_eq_two` then counts the components of a set presented as two disjoint
nonempty open connected pieces.
-/

open Set Topology Function

variable {X ι : Type*} [TopologicalSpace X] {R S T U : Set X} {r x : X}

/-- A preconnected set meeting both of two relatively disjoint open sets cannot
be covered by them. -/
theorem IsPreconnected.not_subset_union {W : Set X} (hS : IsPreconnected S)
    (hU : IsOpen U) (hW : IsOpen W) (hd : Disjoint (S ∩ U) (S ∩ W))
    (hSU : (S ∩ U).Nonempty) (hSW : (S ∩ W).Nonempty) : ¬ S ⊆ U ∪ W := by
  intro hsub
  obtain ⟨x, hx, hxU, hxW⟩ := hS U W hU hW hsub hSU hSW
  exact hd.notMem_of_mem_left ⟨hx, hxU⟩ ⟨hx, hxW⟩

/-- Every member of a pairwise disjoint open cover is clopen. -/
theorem isClopen_of_pairwise_disjoint_open_cover {ι : Type*} {U : ι → Set X}
    (ho : ∀ i, IsOpen (U i)) (hd : Pairwise fun i j ↦ Disjoint (U i) (U j))
    (hcover : ⋃ i, U i = univ) (i : ι) : IsClopen (U i) := by
  have hc : (U i)ᶜ = ⋃ j : {j // j ≠ i}, U j := by
    simpa [iUnion_subtype] using
      biUnion_compl_eq_of_pairwise_disjoint_of_iUnion_eq_univ hcover hd {i}
  refine ⟨isOpen_compl_iff.mp ?_, ho i⟩
  rw [hc]
  exact isOpen_iUnion fun j ↦ ho j.1

/-- Components are relatively closed in the set defining them. -/
@[simp]
theorem closure_connectedComponentIn_inter :
    closure (connectedComponentIn U r) ∩ U = connectedComponentIn U r := by
  refine Subset.antisymm ?_
    (fun _ hz ↦ ⟨subset_closure hz, connectedComponentIn_subset _ _ hz⟩)
  by_cases hr : r ∈ U
  · exact isPreconnected_connectedComponentIn.subset_closure (t := _ ∩ U)
      (fun _ hz ↦ ⟨subset_closure hz, connectedComponentIn_subset U r hz⟩) inter_subset_left
      |>.subset_connectedComponentIn
      ⟨subset_closure (mem_connectedComponentIn hr), hr⟩ inter_subset_right
  simp [connectedComponentIn_eq_empty hr]

/-- Components of an open set with finitely many components are open. -/
theorem IsOpen.connectedComponentIn_of_finite (hU : IsOpen U) [Finite (ConnectedComponents ↥U)]
    (r : X) : IsOpen (connectedComponentIn U r) := by
  by_cases hr : r ∈ U
  · rw [connectedComponentIn_eq_image hr]
    exact hU.isOpenMap_subtypeVal _ <| ConnectedComponents.discreteTopology_iff.mp
        (inferInstance : DiscreteTopology (ConnectedComponents ↥U)) ⟨r, hr⟩
  simp [connectedComponentIn_eq_empty hr]

theorem IsPreconnected.disjoint_frontier_iff (hS : IsPreconnected S) :
    Disjoint S (frontier U) ↔ S ⊆ interior U ∨ S ⊆ interior Uᶜ := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · refine hS.subset_or_subset isOpen_interior isOpen_interior
      (disjoint_compl_right.mono interior_subset interior_subset) fun _ hx ↦ ?_
    rw [← compl_frontier_eq_union_interior]
    exact h.notMem_of_mem_left hx
  rintro (h | h)
  · exact disjoint_interior_frontier.mono_left h
  simpa only [frontier_compl] using disjoint_interior_frontier.mono_left h

/-- The part of a preconnected set's closure that remains in the domain lies in one component. -/
theorem IsPreconnected.inter_closure_subset_connectedComponentIn (hR : IsPreconnected R)
    (hRS : R ⊆ S) (hx : x ∈ S ∩ closure R) : S ∩ closure R ⊆ _root_.connectedComponentIn S x := by
  have hc : IsPreconnected (S ∩ closure R) :=
    hR.subset_closure (subset_inter hRS subset_closure) inter_subset_right
  exact hc.subset_connectedComponentIn hx inter_subset_left

/-- Localize a cover of a punctured set to a component that avoids the remainder's frontier. -/
theorem iUnion_eq_connectedComponentIn_sdiff {R : ι → Set X} (hR : ∀ i, IsPreconnected (R i))
    (hcover : (⋃ i, R i) ∪ U = S \ T)
    (hboundary : Disjoint (connectedComponentIn S x) (frontier U))
    (hattach : ∀ i, (closure (R i) ∩ connectedComponentIn S x).Nonempty)
    (hmiss : (connectedComponentIn S x \ U).Nonempty) :
    (⋃ i, R i) = connectedComponentIn S x \ T := by
  have hsub (i) : R i ⊆ S := fun x hx ↦ (hcover.subset (Or.inl (mem_iUnion.mpr ⟨i, hx⟩))).1
  have hRF (i) : R i ⊆ connectedComponentIn S x := by
    obtain ⟨t, htR, htF⟩ := hattach i
    have h := (hR i).inter_closure_subset_connectedComponentIn (hsub i)
      ⟨connectedComponentIn_subset _ _ htF, htR⟩
    rw [← connectedComponentIn_eq htF] at h
    exact (subset_inter (hsub i) subset_closure).trans h
  have hFW : connectedComponentIn S x ⊆ Uᶜ := by
    rcases isPreconnected_connectedComponentIn.disjoint_frontier_iff.mp hboundary with h | h
    · obtain ⟨t, htF, htW⟩ := hmiss
      exact False.elim (htW (interior_subset (h htF)))
    · exact h.trans interior_subset
  apply subset_antisymm
  · intro x hx
    exact ⟨iUnion_subset hRF hx, (hcover.subset (Or.inl hx)).2⟩
  · rintro x ⟨hxF, hxA⟩
    exact (hcover.superset ⟨connectedComponentIn_subset _ _ hxF, hxA⟩).resolve_right (hFW hxF)

/-- Two preconnected pieces attached through one removed point fill its punctured component. -/
theorem union_eq_connectedComponentIn_sdiff {A U V W : Set X} {q t : X}
    (hU : IsPreconnected U) (hV : IsPreconnected V)
    (hcover : U ∪ V ∪ W = S \ A) (hfront : frontier W ⊆ Sᶜ)
    (ht : t ∈ A ∩ connectedComponentIn S q)
    (htU : t ∈ closure U) (htV : t ∈ closure V) :
    U ∪ V = connectedComponentIn S q \ A := by
  have hbool : (⋃ b : Bool, cond b U V) = U ∪ V := by
    ext x
    simp [Bool.exists_bool, or_comm]
  have h := iUnion_eq_connectedComponentIn_sdiff
    (R := fun b : Bool ↦ cond b U V) (by intro b; cases b <;> assumption)
    (by rwa [hbool])
    (disjoint_left.mpr fun _ hx hxf ↦ hfront hxf (connectedComponentIn_subset _ _ hx))
    (by intro b; cases b <;> exact ⟨t, by assumption, ht.2⟩)
    ⟨t, ht.2, fun htW ↦ (hcover.subset (Or.inr htW)).2 ht.1⟩
  simpa only [hbool] using h

/-- In a locally connected space, the frontier of a connected component of an open set is outside
that open set. -/
theorem IsOpen.frontier_connectedComponentIn_subset_compl [LocallyConnectedSpace X]
    (hU : IsOpen U) : frontier (connectedComponentIn U x) ⊆ Uᶜ := by
  intro y hyfr
  by_contra hyU
  simp only [mem_compl_iff, not_not] at hyU
  have hyV : y ∈ connectedComponentIn U y := mem_connectedComponentIn hyU
  obtain ⟨z, hzV, hzK⟩ :=
    (mem_closure_iff.mp (frontier_subset_closure hyfr)) _ hU.connectedComponentIn hyV
  have hKopen : IsOpen (connectedComponentIn U x) := hU.connectedComponentIn
  refine (hKopen.frontier_eq ▸ hyfr).2 ?_
  rw [← ((connectedComponentIn_eq hzV).trans (connectedComponentIn_eq hzK).symm)]
  exact hyV

/-- If `S` is closed, the frontier of every component of `Sᶜ` lies in `S`. -/
theorem IsClosed.frontier_connectedComponentIn_compl_subset [LocallyConnectedSpace X]
    (hS : IsClosed S) : frontier (connectedComponentIn Sᶜ x) ⊆ S := by
  simpa using hS.isOpen_compl.frontier_connectedComponentIn_subset_compl

/-- A component of a proper set in a preconnected ambient space has nonempty frontier.

No openness or local-connectedness hypothesis is needed for this statement. -/
theorem frontier_connectedComponentIn_nonempty [PreconnectedSpace X]
    (hx : x ∈ U) (hU : U ≠ Set.univ) : (frontier (connectedComponentIn U x)).Nonempty := by
  rw [nonempty_frontier_iff]
  refine ⟨⟨x, mem_connectedComponentIn hx⟩, ?_⟩
  intro hK
  apply hU
  ext y
  simp only [mem_univ, iff_true]
  exact connectedComponentIn_subset _ _ (by
    rw [hK]
    exact mem_univ y)

/-- A component of the complement of a nonempty set has nonempty frontier in a preconnected
ambient space. -/
theorem frontier_connectedComponentIn_compl_nonempty [PreconnectedSpace X]
    (hS : S.Nonempty) (hx : x ∉ S) : (frontier (connectedComponentIn Sᶜ x)).Nonempty := by
  apply frontier_connectedComponentIn_nonempty hx
  intro hSc
  obtain ⟨s, hs⟩ := hS
  refine (show s ∈ Sᶜ from ?_) hs
  rw [hSc]
  exact mem_univ s

/-- An open connected set disjoint from `K` whose frontier lies in `K` is a connected component of
the complement of `K`. -/
theorem eq_connectedComponentIn_of_frontier_subset {W K : Set X} {a : X} (hW : IsOpen W)
    (hWc : IsPreconnected W) (hWK : Disjoint W K) (hfr : frontier W ⊆ K) (ha : a ∈ W) :
    W = connectedComponentIn Kᶜ a := by
  have hWKc : W ⊆ Kᶜ := hWK.subset_compl_right
  refine (hWc.subset_connectedComponentIn ha hWKc).antisymm
    <| isPreconnected_connectedComponentIn.subset_left_of_subset_union hW
    isClosed_closure.isOpen_compl (disjoint_compl_right_iff_subset.mpr subset_closure)
    (fun z hz ↦ (em (z ∈ closure W)).imp (fun hzc ↦ ?_) id)
    ⟨a, mem_connectedComponentIn (hWKc ha), ha⟩
  have hzf : z ∉ frontier W := fun h ↦ connectedComponentIn_subset _ _ hz (hfr h)
  rw [hW.frontier_eq] at hzf
  simp only [mem_sdiff, hzc, true_and, not_not] at hzf
  exact hzf

/-! ### Point sets of connected components -/

namespace ConnectedComponents

/-- The points in a connected component, as the fiber of the component quotient. -/
@[expose] def toSet (c : ConnectedComponents X) : Set X := mk ⁻¹' {c}

@[simp] lemma mem_toSet (c : ConnectedComponents X) (x : X) :
    x ∈ c.toSet ↔ mk x = c := Iff.rfl

@[simp] lemma toSet_mk (x : X) : (mk x).toSet = connectedComponent x :=
  connectedComponents_preimage_singleton

lemma toSet_nonempty (c : ConnectedComponents X) : c.toSet.Nonempty := by
  obtain ⟨x, rfl⟩ := surjective_coe c
  exact ⟨x, rfl⟩

lemma isConnected_toSet (c : ConnectedComponents X) : IsConnected c.toSet := by
  obtain ⟨x, rfl⟩ := surjective_coe c
  rw [toSet_mk]
  exact isConnected_connectedComponent

lemma isClosed_toSet (c : ConnectedComponents X) : IsClosed c.toSet := by
  obtain ⟨x, rfl⟩ := surjective_coe c
  rw [toSet_mk]
  exact isClosed_connectedComponent

lemma toSet_injective : Injective (toSet (X := X)) := by
  intro c d h
  obtain ⟨x, hx⟩ := c.toSet_nonempty
  exact hx.symm.trans (show x ∈ d.toSet from h ▸ hx)

lemma disjoint_toSet {c d : ConnectedComponents X} (h : c ≠ d) :
    Disjoint c.toSet d.toSet :=
  disjoint_left.mpr fun _ hc hd ↦ h (hc.symm.trans hd)

/-- A component of a subspace is closed in that subspace, without ambient closedness. -/
lemma inter_closure_image_toSet {S : Set X} (c : ConnectedComponents ↥S) :
    S ∩ closure (Subtype.val '' c.toSet) = Subtype.val '' c.toSet := by
  apply subset_antisymm
  · rintro x ⟨hxS, hx⟩
    exact ⟨⟨x, hxS⟩, c.isClosed_toSet.closure_subset (closure_subtype.mpr hx), rfl⟩
  · rintro x ⟨y, hy, rfl⟩
    exact ⟨y.2, subset_closure ⟨y, hy, rfl⟩⟩

/-- A set that splits into two disjoint nonempty open connected pieces has exactly two connected
components.

Three places in this repository compute this by hand from `equivOfIsClopenOfIsConnected`: the two
sides of a Jordan curve in the plane and on the sphere, and the two sides of a hyperplane
(`ContinuousLinearMap.connectedComponents_compl_hyperplane_card_eq_two`). What each of them repeats
is the `Bool`-indexed clopen cover of `↥s` built here.

That equivalence supplies `ConnectedComponents ↥s ≃ Bool` under these same hypotheses; only the
cardinality is stated, since that is what the callers hold and a promoted definition is a larger
commitment than a promoted lemma. `IsOpen` is taken in `X` rather than relative to `s` — more than
the proof needs, and what every call site has. -/
theorem card_eq_two {s u v : Set X} (hu : IsOpen u) (hv : IsOpen v) (hcu : IsConnected u)
    (hcv : IsConnected v) (hd : Disjoint u v) (huv : u ∪ v = s) :
    Nat.card (ConnectedComponents ↥s) = 2 := by
  have hpre {w : Set X} (hw : IsOpen w) (hcw : IsConnected w) (hws : w ⊆ s) :
      IsOpen ((↑) ⁻¹' w : Set ↥s) ∧ IsConnected ((↑) ⁻¹' w : Set ↥s) := by
    refine ⟨hw.preimage continuous_subtypeVal, ⟨?_, ?_⟩⟩
    · obtain ⟨x, hx⟩ := hcw.nonempty
      exact ⟨⟨x, hws hx⟩, hx⟩
    · refine IsInducing.subtypeVal.isPreconnected_image.1 ?_
      rw [Subtype.image_preimage_coe, inter_eq_right.2 hws]
      exact hcw.isPreconnected
  obtain ⟨hou, hnu⟩ := hpre hu hcu (huv ▸ subset_union_left)
  obtain ⟨hov, hnv⟩ := hpre hv hcv (huv ▸ subset_union_right)
  have hcompl : ((↑) ⁻¹' v : Set ↥s) = ((↑) ⁻¹' u : Set ↥s)ᶜ := by
    ext x
    have hx : (x : X) ∈ u ∪ v := huv ▸ x.2
    exact ⟨fun h hu' ↦ hd.notMem_of_mem_left hu' h, fun h ↦ hx.resolve_left h⟩
  refine (Nat.card_congr (equivOfIsClopenOfIsConnected
      (U := fun b : Bool ↦ ((↑) ⁻¹' (cond b u v) : Set ↥s)) (fun b ↦ ?_) ?_ ?_
      (fun b ↦ ?_))).trans (by simp)
  · cases b
    · exact ⟨hcompl ▸ hou.isClosed_compl, hov⟩
    · exact ⟨compl_compl ((↑) ⁻¹' u : Set ↥s) ▸ hcompl ▸ hov.isClosed_compl, hou⟩
  · intro b b' hbb'
    cases b <;> cases b' <;> simp only [Function.onFun, Bool.cond_true, Bool.cond_false] <;>
      first
        | exact absurd rfl hbb'
        | exact (hd.preimage _).symm
        | exact hd.preimage _
  · refine eq_univ_of_forall fun x ↦ ?_
    obtain h | h := (huv ▸ x.2 : (x : X) ∈ u ∪ v)
    · exact mem_iUnion.2 ⟨true, h⟩
    · exact mem_iUnion.2 ⟨false, h⟩
  · cases b
    · exact hnv
    · exact hnu

end ConnectedComponents

/-- The component indexed by a member of a clopen connected partition is that member. -/
theorem ConnectedComponents.preimage_singleton_equivOfIsClopenOfIsConnected_symm
    {ι : Type*} {U : ι → Set X}
    (hclopen : ∀ i, IsClopen (U i)) (hdisj : Pairwise (Disjoint on U))
    (hcover : ⋃ i, U i = univ) (hconn : ∀ i, IsConnected (U i)) (i : ι) :
    ConnectedComponents.mk ⁻¹'
      {(ConnectedComponents.equivOfIsClopenOfIsConnected hclopen hdisj hcover hconn).symm i} =
        U i := by
  let q := ConnectedComponents.equivOfIsClopenOfIsConnected hclopen hdisj hcover hconn
  ext x
  change ConnectedComponents.mk x = q.symm i ↔ x ∈ U i
  constructor
  · intro hx
    obtain ⟨j, hj⟩ := iUnion_eq_univ_iff.mp hcover x
    have hq : q (ConnectedComponents.mk x) = j :=
      ConnectedComponents.equivOfIsClopenOfIsConnected_mk hclopen hdisj hcover hconn x hj
    have hji : j = i := by simpa [hx] using hq.symm
    exact hji ▸ hj
  · intro hx
    exact q.injective (by simpa using
      ConnectedComponents.equivOfIsClopenOfIsConnected_mk hclopen hdisj hcover hconn x hx)

/-! ### Component partitions, restriction, and removal -/

/-- Distinct components of a set are disjoint, including components at outside points. -/
theorem disjoint_connectedComponentIn_of_ne {U : Set X} {u v : X}
    (hne : connectedComponentIn U u ≠ connectedComponentIn U v) :
    Disjoint (connectedComponentIn U u) (connectedComponentIn U v) :=
  disjoint_left.mpr fun _ hx hy ↦ hne
    ((connectedComponentIn_eq hx).trans (connectedComponentIn_eq hy).symm)

/-- A component of `S \ A` is disjoint from `A`, including components at outside points. -/
theorem disjoint_connectedComponentIn_sdiff {S A : Set X} {y : X} :
    Disjoint (connectedComponentIn (S \ A) y) A :=
  disjoint_sdiff_left.mono_left (connectedComponentIn_subset _ _)

/-- A nonpreconnected set has a component different from the component at any given point.
The given point need not belong to the set. -/
theorem exists_connectedComponentIn_ne {U : Set X} (hU : ¬ IsPreconnected U) (u : X) :
    ∃ v ∈ U, connectedComponentIn U u ≠ connectedComponentIn U v := by
  by_contra! h
  have heq : connectedComponentIn U u = U :=
    (connectedComponentIn_subset _ _).antisymm fun v hv ↦ by
      rw [h v hv]
      exact mem_connectedComponentIn hv
  exact hU (heq ▸ isPreconnected_connectedComponentIn)

/-- Two distinct components covering a set enumerate its component quotient.
No ambient openness or separation assumption is needed. -/
theorem ConnectedComponents.card_eq_two_of_connectedComponentIn_union {U : Set X} {u v : X}
    (hu : u ∈ U) (hv : v ∈ U) (hne : connectedComponentIn U u ≠ connectedComponentIn U v)
    (hcover : connectedComponentIn U u ∪ connectedComponentIn U v = U) :
    Nat.card (ConnectedComponents ↥U) = 2 := by
  have heq (w z : U) : ConnectedComponents.mk w = ConnectedComponents.mk z ↔
      connectedComponentIn U (w : X) = connectedComponentIn U (z : X) := by
    rw [ConnectedComponents.coe_eq_coe, connectedComponentIn_eq_image w.property,
      connectedComponentIn_eq_image z.property, Set.image_val_inj]
  refine Nat.card_eq_two_iff.mpr ⟨ConnectedComponents.mk (⟨u, hu⟩ : U),
    ConnectedComponents.mk (⟨v, hv⟩ : U), fun h ↦ hne ((heq _ _).mp h), ?_⟩
  apply eq_univ_of_forall
  intro c
  obtain ⟨z, rfl⟩ := ConnectedComponents.surjective_coe c
  have hz : (z : X) ∈ connectedComponentIn U u ∪ connectedComponentIn U v :=
    hcover.symm ▸ z.property
  rcases hz with hzu | hzv
  · exact Or.inl ((heq _ _).mpr (connectedComponentIn_eq hzu).symm)
  · exact Or.inr ((heq _ _).mpr (connectedComponentIn_eq hzv).symm)

/-- A nonpreconnected set with no three distinct components has exactly two components. -/
theorem ConnectedComponents.card_eq_two_of_not_isPreconnected {S : Set X}
    (hsep : ¬ IsPreconnected S)
    (hupper : ∀ {p q r : X}, p ∈ S → q ∈ S → r ∈ S →
      connectedComponentIn S p = connectedComponentIn S q ∨
      connectedComponentIn S p = connectedComponentIn S r ∨
      connectedComponentIn S q = connectedComponentIn S r) :
    Nat.card (ConnectedComponents ↥S) = 2 := by
  have hne : S.Nonempty := by
    by_contra h
    exact hsep (by simpa [not_nonempty_iff_eq_empty.mp h] using
      (isPreconnected_empty : IsPreconnected (∅ : Set X)))
  obtain ⟨p, hp⟩ := hne
  obtain ⟨q, hq, hpq⟩ := exists_connectedComponentIn_ne hsep p
  apply card_eq_two_of_connectedComponentIn_union hp hq hpq
  refine (union_subset (connectedComponentIn_subset _ _)
    (connectedComponentIn_subset _ _)).antisymm ?_
  intro z hz
  rcases hupper hp hq hz with h | h | h
  · exact (hpq h).elim
  · exact Or.inl (h ▸ mem_connectedComponentIn hz)
  · exact Or.inr (h ▸ mem_connectedComponentIn hz)

/-- An open set with exactly two components of the same frontier is the disjoint union
of two open connected regions with that frontier. Finite component count supplies openness,
so no local connectedness of the ambient space is required. -/
theorem IsOpen.exists_two_regions_of_card_connectedComponents_eq_two {S F : Set X}
    (hS : IsOpen S) (hcard : Nat.card (ConnectedComponents ↥S) = 2)
    (hfrontier : ∀ p ∈ S, frontier (connectedComponentIn S p) = F) :
    ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
      Disjoint U V ∧ U ∪ V = S ∧ frontier U = F ∧ frontier V = F := by
  have : Finite (ConnectedComponents ↥S) := Nat.finite_of_card_ne_zero (by omega)
  obtain ⟨c, d, hne, hcover⟩ := Nat.card_eq_two_iff.mp hcard
  obtain ⟨u, rfl⟩ := ConnectedComponents.surjective_coe c
  obtain ⟨v, rfl⟩ := ConnectedComponents.surjective_coe d
  refine ⟨connectedComponentIn S u.1, connectedComponentIn S v.1,
    hS.connectedComponentIn_of_finite _, hS.connectedComponentIn_of_finite _,
    isConnected_connectedComponentIn_iff.mpr u.2,
    isConnected_connectedComponentIn_iff.mpr v.2, ?_, ?_,
    hfrontier u.1 u.2, hfrontier v.1 v.2⟩
  · rw [connectedComponentIn_eq_image u.2, connectedComponentIn_eq_image v.2]
    exact disjoint_image_of_injective Subtype.val_injective
      (by simpa only [ConnectedComponents.toSet_mk] using ConnectedComponents.disjoint_toSet hne)
  · refine (union_subset (connectedComponentIn_subset ..)
      (connectedComponentIn_subset ..)).antisymm ?_
    intro z hz
    have he : ConnectedComponents.mk (⟨z, hz⟩ : ↥S) ∈
        ({ConnectedComponents.mk u, ConnectedComponents.mk v} : Set _) :=
      hcover.symm ▸ mem_univ _
    have hmem (w : ↥S) (he : ConnectedComponents.mk ⟨z, hz⟩ = ConnectedComponents.mk w) :
        z ∈ connectedComponentIn S w.1 := by
      rw [connectedComponentIn_eq_image w.2]
      exact ⟨⟨z, hz⟩, ConnectedComponents.coe_eq_coe'.mp he, rfl⟩
    exact he.elim (fun h ↦ Or.inl (hmem u h))
      (fun h ↦ Or.inr (hmem v (mem_singleton_iff.mp h)))

/-- Restricting to an intermediate set containing the whole component does not change it. -/
theorem connectedComponentIn_eq_of_subset_of_subset {T U : Set X} {y : X}
    (hTU : T ⊆ U) (hUT : connectedComponentIn U y ⊆ T) :
    connectedComponentIn T y = connectedComponentIn U y := by
  refine (connectedComponentIn_mono y hTU).antisymm ?_
  by_cases hy : y ∈ U
  · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (mem_connectedComponentIn hy) hUT
  · simp [connectedComponentIn_eq_empty hy]

/-- Adjoining one side of a relative closed separation of `S \ C` to the preconnected
set `C` preserves preconnectedness. Empty sets are allowed. -/
theorem isPreconnected_union_inter_of_closed_cover {S C u v : Set X}
    (hS : IsPreconnected S) (hC : IsPreconnected C) (hCS : C ⊆ S)
    (hu : IsClosed u) (hv : IsClosed v) (hcover : S \ C ⊆ u ∪ v)
    (hdisj : (S \ C) ∩ (u ∩ v) = ∅) : IsPreconnected (C ∪ (S ∩ v)) := by
  by_cases hCn : C.Nonempty
  swap
  · obtain rfl := Set.not_nonempty_iff_eq_empty.mp hCn
    simp only [sdiff_empty] at hcover hdisj
    simp only [empty_union]
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hS u v hu hv hcover hdisj with h | h
    · have heq : S ∩ v = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        rintro z ⟨hzS, hzv⟩
        have hz : z ∈ S ∩ (u ∩ v) := ⟨hzS, h hzS, hzv⟩
        simp [hdisj] at hz
      rw [heq]
      exact isPreconnected_empty
    · rwa [inter_eq_left.mpr h]
  rw [isPreconnected_iff_subset_of_disjoint_closed]
  intro p q hp hq hpq hdisj'
  have haux {p q : Set X} (hp : IsClosed p) (hq : IsClosed q)
      (hpq : C ∪ (S ∩ v) ⊆ p ∪ q)
      (hdisj' : (C ∪ (S ∩ v)) ∩ (p ∩ q) = ∅) (hCp : C ⊆ p) :
      C ∪ (S ∩ v) ⊆ p := by
    have hcover' : S ⊆ (u ∪ p) ∪ (v ∩ q) := by
      intro z hz
      by_cases hzC : z ∈ C
      · exact Or.inl (Or.inr (hCp hzC))
      rcases hcover ⟨hz, hzC⟩ with hzu | hzv
      · exact Or.inl (Or.inl hzu)
      rcases hpq (Or.inr ⟨hz, hzv⟩) with hzp | hzq
      · exact Or.inl (Or.inr hzp)
      · exact Or.inr ⟨hzv, hzq⟩
    have hdisj'' : S ∩ ((u ∪ p) ∩ (v ∩ q)) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro z ⟨hzS, hzu | hzp, hzv, hzq⟩
      · by_cases hzC : z ∈ C
        · have : z ∈ (C ∪ (S ∩ v)) ∩ (p ∩ q) :=
            ⟨Or.inl hzC, hCp hzC, hzq⟩
          simp [hdisj'] at this
        · have : z ∈ (S \ C) ∩ (u ∩ v) := ⟨⟨hzS, hzC⟩, hzu, hzv⟩
          simp [hdisj] at this
      · have : z ∈ (C ∪ (S ∩ v)) ∩ (p ∩ q) :=
          ⟨Or.inr ⟨hzS, hzv⟩, hzp, hzq⟩
        simp [hdisj'] at this
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hS
        (u ∪ p) (v ∩ q) (hu.union hp) (hv.inter hq) hcover' hdisj'' with h | h
    · rintro z (hzC | ⟨hzS, hzv⟩)
      · exact hCp hzC
      rcases h hzS with hzu | hzp
      · by_cases hzC : z ∈ C
        · exact hCp hzC
        · have : z ∈ (S \ C) ∩ (u ∩ v) := ⟨⟨hzS, hzC⟩, hzu, hzv⟩
          simp [hdisj] at this
      · exact hzp
    · obtain ⟨z, hzC⟩ := hCn
      have : z ∈ (C ∪ (S ∩ v)) ∩ (p ∩ q) :=
        ⟨Or.inl hzC, hCp hzC, (h (hCS hzC)).2⟩
      simp [hdisj'] at this
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hC
      p q hp hq (subset_union_left.trans hpq)
      (by exact subset_empty_iff.mp ((inter_subset_inter_left _ subset_union_left).trans
        hdisj'.subset)) with hCp | hCq
  · exact Or.inl (haux hp hq hpq hdisj' hCp)
  · exact Or.inr (haux hq hp (by simpa [union_comm] using hpq)
      (by simpa [inter_comm p q] using hdisj') hCq)

/-- If `C ⊆ T ⊆ S`, the sets `C` and `S` are preconnected, and `T \ C` is clopen
in `S \ C`, then `T` is preconnected. -/
theorem IsPreconnected.of_isClopen_sdiff {S C T : Set X}
    (hS : IsPreconnected S) (hC : IsPreconnected C) (hCT : C ⊆ T) (hTS : T ⊆ S)
    (hT : IsClopen ((Subtype.val : ↥(S \ C) → X) ⁻¹' T)) : IsPreconnected T := by
  obtain ⟨v, hv, hvT⟩ := isClosed_induced_iff.mp hT.isClosed
  obtain ⟨u, hu, huT⟩ := isClosed_induced_iff.mp hT.isOpen.isClosed_compl
  have hvmem (z : X) (hz : z ∈ S \ C) : z ∈ v ↔ z ∈ T := Set.ext_iff.mp hvT ⟨z, hz⟩
  have humem (z : X) (hz : z ∈ S \ C) : z ∈ u ↔ z ∉ T := Set.ext_iff.mp huT ⟨z, hz⟩
  convert isPreconnected_union_inter_of_closed_cover hS hC (hCT.trans hTS) hu hv
    (fun z hz ↦ (em (z ∈ T)).symm.imp (humem z hz).2 (hvmem z hz).2)
    (eq_empty_iff_forall_notMem.2 fun z ⟨hz, hzu, hzv⟩ ↦ (humem z hz).1 hzu ((hvmem z hz).1 hzv))
    using 1
  ext z
  by_cases hzC : z ∈ C
  · simp [hzC, hCT hzC]
  by_cases hzS : z ∈ S
  · simp [hzC, hzS, hvmem z ⟨hzS, hzC⟩]
  simpa [hzC, hzS] using fun h ↦ hzS (hTS h)

/-- Removing a component outside a preconnected subset preserves preconnectedness.
Both the subset and the resulting set may be empty. -/
theorem IsPreconnected.sdiff_connectedComponentIn_sdiff {S A : Set X} {y : X}
    (hS : IsPreconnected S) (hA : IsPreconnected A) (hAS : A ⊆ S) :
    IsPreconnected (S \ _root_.connectedComponentIn (S \ A) y) := by
  by_cases hy : y ∈ S \ A
  · let C := _root_.connectedComponentIn (S \ A) y
    have hCS : C ⊆ S := (connectedComponentIn_subset _ _).trans sdiff_subset
    have hAC : A ⊆ S \ C := fun z hz ↦
      ⟨hAS hz, disjoint_connectedComponentIn_sdiff.notMem_of_mem_right hz⟩
    rw [isPreconnected_iff_subset_of_disjoint_closed]
    intro u v hu hv hcover hdisj
    have haux {u v : Set X} (hu : IsClosed u) (hv : IsClosed v)
        (hcover : S \ C ⊆ u ∪ v) (hdisj : (S \ C) ∩ (u ∩ v) = ∅)
        (hAu : A ⊆ u) : S \ C ⊆ u := by
      have hconn := isPreconnected_union_inter_of_closed_cover hS
        isPreconnected_connectedComponentIn hCS hu hv hcover hdisj
      have hsub : C ∪ (S ∩ v) ⊆ S \ A := by
        rintro z (hzC | ⟨hzS, hzv⟩)
        · exact connectedComponentIn_subset _ _ hzC
        · refine ⟨hzS, fun hzA ↦ ?_⟩
          have hz : z ∈ (S \ C) ∩ (u ∩ v) := ⟨hAC hzA, hAu hzA, hzv⟩
          simp [hdisj] at hz
      have hmax : C ∪ (S ∩ v) ⊆ C := hconn.subset_connectedComponentIn
        (Or.inl (mem_connectedComponentIn hy)) hsub
      intro z hz
      exact (hcover hz).resolve_right (fun hzv ↦ hz.2 (hmax (Or.inr ⟨hz.1, hzv⟩)))
    have hAdisj : A ∩ (u ∩ v) = ∅ :=
      subset_empty_iff.mp ((inter_subset_inter_left _ hAC).trans hdisj.subset)
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hA u v hu hv
        (hAC.trans hcover) hAdisj with hAu | hAv
    · exact Or.inl (haux hu hv hcover hdisj hAu)
    · exact Or.inr (haux hv hu (by simpa [union_comm] using hcover)
        (by simpa [inter_comm u v] using hdisj) hAv)
  · simpa only [connectedComponentIn_eq_empty hy, sdiff_empty] using hS

private theorem IsPreconnected.sdiff_biUnion_connectedComponentIn_sdiff_of_finite {S A F : Set X}
    (hS : IsPreconnected S) (hA : IsPreconnected A) (hAS : A ⊆ S) (hF : F.Finite) :
    IsPreconnected (S \ ⋃ y ∈ F, _root_.connectedComponentIn (S \ A) y) := by
  classical
  induction F, hF using Set.Finite.induction_on with
  | empty => simpa using hS
  | @insert y F _ hF ih =>
    rw [biUnion_insert]
    let R := ⋃ z ∈ F, _root_.connectedComponentIn (S \ A) z
    change IsPreconnected (S \ (_root_.connectedComponentIn (S \ A) y ∪ R))
    by_cases hy : y ∈ S \ A
    · by_cases hyr : y ∈ R
      · obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.mp hyr
        have hsub : _root_.connectedComponentIn (S \ A) y ⊆ R := fun w hw ↦
          mem_iUnion₂.mpr ⟨z, hz, (connectedComponentIn_eq hyz).symm ▸ hw⟩
        simpa only [union_eq_right.mpr hsub] using ih
      · have hsub : _root_.connectedComponentIn (S \ A) y ⊆ (S \ R) \ A := by
          intro w hw
          refine ⟨⟨(connectedComponentIn_subset _ _ hw).1, ?_⟩,
            (connectedComponentIn_subset _ _ hw).2⟩
          intro hwr
          obtain ⟨z, hz, hwz⟩ := mem_iUnion₂.mp hwr
          have heq := (connectedComponentIn_eq hw).trans (connectedComponentIn_eq hwz).symm
          exact hyr (mem_iUnion₂.mpr ⟨z, hz, heq ▸ mem_connectedComponentIn hy⟩)
        have heq : _root_.connectedComponentIn ((S \ R) \ A) y =
            _root_.connectedComponentIn (S \ A) y :=
          connectedComponentIn_eq_of_subset_of_subset (fun w hw ↦ ⟨hw.1.1, hw.2⟩) hsub
        have hAR : A ⊆ S \ R := by
          intro w hw
          refine ⟨hAS hw, fun hwr ↦ ?_⟩
          obtain ⟨z, _, hwz⟩ := mem_iUnion₂.mp hwr
          exact disjoint_connectedComponentIn_sdiff.notMem_of_mem_right hw hwz
        have h := ih.sdiff_connectedComponentIn_sdiff (y := y) hA hAR
        rw [heq] at h
        convert h using 1
        ext w
        simp only [mem_sdiff, mem_union]
        tauto
    · simpa only [connectedComponentIn_eq_empty hy, empty_union] using ih

/-- Removing finitely many components outside a preconnected subset preserves preconnectedness.
Only the set of selected components must be finite: the representative set `F` may be infinite,
contain outside points, or contain many representatives of the same component. -/
theorem IsPreconnected.sdiff_biUnion_connectedComponentIn_sdiff {S A F : Set X}
    (hS : IsPreconnected S) (hA : IsPreconnected A) (hAS : A ⊆ S)
    (hF : (_root_.connectedComponentIn (S \ A) '' F).Finite) :
    IsPreconnected (S \ ⋃ y ∈ F, _root_.connectedComponentIn (S \ A) y) := by
  obtain ⟨G, _, hG, hGF⟩ := exists_subset_image_finite_and.mp
    (show ∃ T ⊆ _root_.connectedComponentIn (S \ A) '' F,
      T.Finite ∧ T = _root_.connectedComponentIn (S \ A) '' F from ⟨_, Subset.rfl, hF, rfl⟩)
  have h := hS.sdiff_biUnion_connectedComponentIn_sdiff_of_finite hA hAS hG
  have heq : (⋃ y ∈ G, _root_.connectedComponentIn (S \ A) y) =
      ⋃ y ∈ F, _root_.connectedComponentIn (S \ A) y := by
    simpa only [sUnion_image] using congrArg sUnion hGF
  rwa [heq] at h

/-- Removing finitely many components outside a connected subset leaves a connected set,
since the subset itself remains. -/
theorem IsPreconnected.isConnected_sdiff_biUnion_connectedComponentIn_sdiff {S A F : Set X}
    (hS : IsPreconnected S) (hA : IsConnected A) (hAS : A ⊆ S)
    (hF : (_root_.connectedComponentIn (S \ A) '' F).Finite) :
    IsConnected (S \ ⋃ y ∈ F, _root_.connectedComponentIn (S \ A) y) := by
  obtain ⟨x, hx⟩ := hA.nonempty
  refine ⟨⟨x, hAS hx, ?_⟩, hS.sdiff_biUnion_connectedComponentIn_sdiff hA.isPreconnected hAS hF⟩
  simp only [mem_iUnion, not_exists]
  exact fun y _ ↦ disjoint_connectedComponentIn_sdiff.notMem_of_mem_right hx

/-- Removing a component of a singleton puncture leaves a connected set.
The retained point supplies nonemptiness; the representative may be outside the puncture. -/
theorem IsPreconnected.isConnected_sdiff_connectedComponentIn_sdiff_singleton {S : Set X}
    {x y : X} (hS : IsPreconnected S) (hx : x ∈ S) :
    IsConnected (S \ _root_.connectedComponentIn (S \ {x}) y) :=
  ⟨⟨x, hx, disjoint_connectedComponentIn_sdiff.notMem_of_mem_right (mem_singleton x)⟩,
    hS.sdiff_connectedComponentIn_sdiff isPreconnected_singleton (singleton_subset_iff.mpr hx)⟩

section ComponentTransport
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {S : Set X} {x : X} {f : X → Y}

/-- An inducing map carries the component of a retained point onto its image component. -/
theorem Topology.IsInducing.image_connectedComponentIn (hf : IsInducing f) (hx : x ∈ S) :
    f '' connectedComponentIn S x = connectedComponentIn (f '' S) (f x) := by
  refine (hf.continuous.continuousOn.image_connectedComponentIn_subset hx).antisymm ?_
  let C := connectedComponentIn (f '' S) (f x)
  have himage : f '' (S ∩ f ⁻¹' C) = C := by
    rw [image_inter_preimage, inter_eq_right.mpr (connectedComponentIn_subset _ _)]
  have hpre : IsPreconnected (S ∩ f ⁻¹' C) :=
    hf.isPreconnected_image.mp (himage.symm ▸ isPreconnected_connectedComponentIn)
  have hsub := hpre.subset_connectedComponentIn
    (show x ∈ S ∩ f ⁻¹' C from ⟨hx, mem_connectedComponentIn (mem_image_of_mem f hx)⟩)
    inter_subset_left
  change C ⊆ f '' connectedComponentIn S x
  rw [← himage]
  exact image_mono hsub

/-- The embedding form is total, including outside points. -/
theorem Topology.IsEmbedding.image_connectedComponentIn (hf : IsEmbedding f) :
    f '' connectedComponentIn S x = connectedComponentIn (f '' S) (f x) := by
  by_cases hx : x ∈ S
  · exact hf.isInducing.image_connectedComponentIn hx
  · rw [connectedComponentIn_eq_empty hx, image_empty,
      connectedComponentIn_eq_empty (fun h ↦ hx (hf.injective.mem_set_image.mp h))]

end ComponentTransport
