module

public import Matroid.MiniTauCeti.JCT.Topology.Circuit.Basic
public import Matroid.MiniTauCeti.JCT.Topology.ConnectedComponent

/-!
# Components of intrinsic circuits

Deleting two distinct members leaves exactly two connected components; every other two-point
deletion is connected. The proof uses component removal in arbitrary spaces, without a separation
axiom or a parametrization.
The covering argument follows Khanfir–Seguin, *Flimsy Spaces*, Proposition 3.5.
-/

@[expose] public section

open Set Topology

namespace IsCircuit

variable {X : Type*} [TopologicalSpace X] {A B S : Set X} {a b u v : X}

/-- Counterfactual step: a hypothetical third component supplies the connected sets
used to contradict the pair-puncture axiom in the covering theorem. -/
private lemma puncture_sdiff_component_connected (hS : IsCircuit S) (ha : a ∈ S) (hb : b ∈ S)
    (hab : a ≠ b) (hu : u ∈ S \ {a, b}) (hv : v ∈ S \ {a, b})
    (hne : connectedComponentIn (S \ {a, b}) u ≠ connectedComponentIn (S \ {a, b}) v)
    (hrest : ((S \ {a, b}) \ (connectedComponentIn (S \ {a, b}) u ∪
      connectedComponentIn (S \ {a, b}) v)).Nonempty) :
    IsConnected ((S \ {u}) \ connectedComponentIn (S \ {a, b}) v) := by
  let C := connectedComponentIn (S \ {a, b}) u
  let D := connectedComponentIn (S \ {a, b}) v
  let E := connectedComponentIn (S \ {u, a}) v
  change IsConnected ((S \ {u}) \ D)
  have huC : u ∈ C := mem_connectedComponentIn hu
  have hvD : v ∈ D := mem_connectedComponentIn hv
  have hCD : Disjoint C D := disjoint_connectedComponentIn_of_ne hne
  have hDsub : D ⊆ S \ {a, b} := connectedComponentIn_subset _ _
  have hEsub : E ⊆ S \ {u, a} := connectedComponentIn_subset _ _
  have hDua : D ⊆ S \ {u, a} := by
    intro w hw
    have hwu : w ≠ u := fun h ↦ hCD.notMem_of_mem_left (h ▸ huC) hw
    have hwab := hDsub hw
    simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff] at hwab ⊢
    tauto
  have hvua := hDua hvD
  have hDE : D ⊆ E := isPreconnected_connectedComponentIn.subset_connectedComponentIn hvD hDua
  have hEconn : IsConnected E := isConnected_connectedComponentIn_iff.mpr hvua
  have hpun : (S \ {u}) \ {a} = S \ {u, a} := sdiff_sdiff_left
  have ha' : a ∈ S \ {u} := ⟨ha, fun h ↦ hu.2 (Or.inl h.symm)⟩
  have hremoveE : IsConnected ((S \ {u}) \ E) := by
    simpa only [hpun] using (hS.isConnected_sdiff_singleton u).isPreconnected
      |>.isConnected_sdiff_connectedComponentIn_sdiff_singleton (y := v) ha'
  by_cases hbE : b ∈ E
  · have hEmin : E \ {b} ⊆ S \ {a, b} := by
      intro w hw
      have hwua := hEsub hw.1
      simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff] at hwua hw ⊢
      tauto
    have hDmin : D ⊆ E \ {b} := by
      intro w hw
      exact ⟨hDE hw, fun h ↦ (hDsub hw).2 (Or.inr h)⟩
    have hrestriction : connectedComponentIn (E \ {b}) v = D :=
      connectedComponentIn_eq_of_subset_of_subset hEmin hDmin
    have hED : IsConnected (E \ D) := by
      simpa only [hrestriction] using
        hEconn.isPreconnected.isConnected_sdiff_connectedComponentIn_sdiff_singleton (y := v) hbE
    have hrem {p q : X} (hq : q ∈ S) (hpq : p ≠ q) (hpair : S \ {p, q} = S \ {a, b}) :
        IsConnected ((S \ {p}) \ (C ∪ D)) := by
      have h := (hS.isConnected_sdiff_singleton p).isPreconnected
        |>.isConnected_sdiff_biUnion_connectedComponentIn_sdiff (F := {u, v})
          isConnected_singleton (singleton_subset_iff.mpr ⟨hq, hpq.symm⟩)
          (((finite_singleton v).insert u).image _)
      rwa [biUnion_pair, show (S \ {p}) \ {q} = S \ {a, b} from sdiff_sdiff_left.trans hpair] at h
    have hRa := hrem hb hab rfl
    have hRb := hrem ha hab.symm (by rw [pair_comm])
    have hbRa : b ∈ (S \ {a}) \ (C ∪ D) := by
      refine ⟨⟨hb, hab.symm⟩, ?_⟩
      rintro (h | h) <;>
        exact disjoint_connectedComponentIn_sdiff.notMem_of_mem_right (Or.inr rfl) h
    have hRaSub : (S \ {a}) \ (C ∪ D) ⊆ S \ {u, a} := by
      intro w hw
      have hwu : w ≠ u := fun h ↦ hw.2 (Or.inl (h ▸ huC))
      simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff] at hw ⊢
      tauto
    have hRaE : (S \ {a}) \ (C ∪ D) ⊆ E := by
      have h := hRa.isPreconnected.subset_connectedComponentIn hbRa hRaSub
      rwa [← connectedComponentIn_eq hbE] at h
    obtain ⟨w, hwU, hwCD⟩ := hrest
    have hwRa : w ∈ (S \ {a}) \ (C ∪ D) :=
      ⟨⟨hwU.1, fun h ↦ hwU.2 (Or.inl h)⟩, hwCD⟩
    have hwRb : w ∈ (S \ {b}) \ (C ∪ D) :=
      ⟨⟨hwU.1, fun h ↦ hwU.2 (Or.inr h)⟩, hwCD⟩
    have hwED : w ∈ E \ D := ⟨hRaE hwRa, fun h ↦ hwCD (Or.inr h)⟩
    have hjoin : IsConnected ((E \ D) ∪ ((S \ {b}) \ (C ∪ D))) :=
      IsConnected.union ⟨w, hwED, hwRb⟩ hED hRb
    have haE : a ∉ E := disjoint_connectedComponentIn_sdiff.notMem_of_mem_right (Or.inr rfl)
    have haRb : a ∈ (S \ {b}) \ (C ∪ D) := by
      refine ⟨⟨ha, hab⟩, ?_⟩
      rintro (h | h) <;>
        exact disjoint_connectedComponentIn_sdiff.notMem_of_mem_right (Or.inl rfl) h
    have hall : IsConnected (((S \ {u}) \ E) ∪ ((E \ D) ∪ ((S \ {b}) \ (C ∪ D)))) :=
      IsConnected.union ⟨a, ⟨ha', haE⟩, Or.inr haRb⟩ hremoveE hjoin
    convert hall using 1
    ext z
    have hEz := hEsub (a := z)
    have hDz := hDE (a := z)
    have hzuC : z = u → z ∈ C := fun h ↦ h ▸ huC
    simp only [mem_sdiff, mem_union, mem_singleton_iff, mem_insert_iff] at hEz hDz ⊢
    tauto
  · have hEDsub : E ⊆ D := isPreconnected_connectedComponentIn.subset_connectedComponentIn
      (hDE hvD) (by
        intro w hw
        have hwua := hEsub hw
        have hwb : w ≠ b := fun h ↦ hbE (h ▸ hw)
        simp only [mem_sdiff, mem_insert_iff, mem_singleton_iff] at hwua ⊢
        tauto)
    have heq : E = D := hEDsub.antisymm hDE
    simpa only [heq] using hremoveE

/-- A two-point deletion is connected exactly when it does not delete two distinct members. -/
lemma isConnected_sdiff_pair_iff (hS : IsCircuit S) :
    IsConnected (S \ {a, b}) ↔ ¬ (a ∈ S ∧ b ∈ S ∧ a ≠ b) := by
  refine ⟨fun hc ⟨ha, hb, hab⟩ ↦ hS.pair_puncture_not_isPreconnected ha hb hab hc.isPreconnected,
    fun hbad ↦ ?_⟩
  obtain ha | ha := em' (a ∈ S)
  · rw [sdiff_insert_of_notMem ha]
    exact hS.isConnected_sdiff_singleton b
  obtain hb | hb := em' (b ∈ S)
  · rw [pair_comm, sdiff_insert_of_notMem hb]
    exact hS.isConnected_sdiff_singleton a
  obtain rfl : a = b := Classical.byContradiction fun hne ↦ hbad ⟨ha, hb, hne⟩
  simpa using hS.isConnected_sdiff_singleton a

/-- Two distinct components cover the two-point deletion. Their existence already forces
the deleted points to be distinct members of the circuit. -/
lemma connectedComponentIn_union_connectedComponentIn (hS : IsCircuit S) (hu : u ∈ S \ {a, b})
    (hv : v ∈ S \ {a, b})
    (hne : connectedComponentIn (S \ {a, b}) u ≠ connectedComponentIn (S \ {a, b}) v) :
    connectedComponentIn (S \ {a, b}) u ∪ connectedComponentIn (S \ {a, b}) v = S \ {a, b} := by
  obtain ⟨ha, hb, hab⟩ : a ∈ S ∧ b ∈ S ∧ a ≠ b := by
    contrapose hne
    have hc := (hS.isConnected_sdiff_pair_iff.mpr hne).isPreconnected
    exact (hc.connectedComponentIn hu).trans (hc.connectedComponentIn hv).symm
  let C := connectedComponentIn (S \ {a, b}) u
  let D := connectedComponentIn (S \ {a, b}) v
  change C ∪ D = S \ {a, b}
  have hCsub : C ⊆ S \ {a, b} := connectedComponentIn_subset _ _
  have hDsub : D ⊆ S \ {a, b} := connectedComponentIn_subset _ _
  have hCD : Disjoint C D := disjoint_connectedComponentIn_of_ne hne
  have huC : u ∈ C := mem_connectedComponentIn hu
  have hvD : v ∈ D := mem_connectedComponentIn hv
  refine (union_subset hCsub hDsub).antisymm ?_
  by_contra hsub
  obtain ⟨w, hw, hwr⟩ := Set.not_subset.mp hsub
  have hrest : ((S \ {a, b}) \ (C ∪ D)).Nonempty := ⟨w, hw, hwr⟩
  have hleft := puncture_sdiff_component_connected hS ha hb hab hu hv hne hrest
  have hright := puncture_sdiff_component_connected hS ha hb hab hv hu hne.symm
    (by simpa only [union_comm] using hrest)
  have haC : a ∉ C := disjoint_connectedComponentIn_sdiff.notMem_of_mem_right (Or.inl rfl)
  have haD : a ∉ D := disjoint_connectedComponentIn_sdiff.notMem_of_mem_right (Or.inl rfl)
  have hau : a ≠ u := fun h ↦ hu.2 (Or.inl h.symm)
  have hav : a ≠ v := fun h ↦ hv.2 (Or.inl h.symm)
  have huvn : u ≠ v := fun h ↦ hne (h ▸ rfl)
  have hc : IsConnected (((S \ {u}) \ D) ∪ ((S \ {v}) \ C)) :=
    IsConnected.union ⟨a, ⟨⟨ha, hau⟩, haD⟩, ⟨⟨ha, hav⟩, haC⟩⟩ hleft hright
  apply hS.pair_puncture_not_isPreconnected hu.1 hv.1 huvn
  convert hc.isPreconnected using 1
  ext z
  have hd : z ∈ C → z ∉ D := fun h ↦ hCD.notMem_of_mem_left h
  have hzu : z = u → z ∈ C := fun h ↦ h ▸ huC
  have hzv : z = v → z ∈ D := fun h ↦ h ▸ hvD
  simp only [mem_sdiff, mem_union, mem_insert_iff, mem_singleton_iff]
  tauto

/-- The relative complement of a puncture component is the component at any point in it. -/
lemma sdiff_connectedComponentIn_pair_eq (hS : IsCircuit S) (hu : u ∈ S \ {a, b})
    (hv : v ∈ (S \ {a, b}) \ connectedComponentIn (S \ {a, b}) u) :
    (S \ {a, b}) \ connectedComponentIn (S \ {a, b}) u = connectedComponentIn (S \ {a, b}) v := by
  have hne : connectedComponentIn (S \ {a, b}) u ≠ connectedComponentIn (S \ {a, b}) v :=
    fun h ↦ hv.2 (h.symm ▸ mem_connectedComponentIn hv.1)
  have hcover := hS.connectedComponentIn_union_connectedComponentIn hu hv.1 hne
  have hd := disjoint_connectedComponentIn_of_ne hne
  ext z
  exact ⟨fun hz ↦ ((congrArg (z ∈ ·) hcover).mpr hz.1).resolve_left hz.2,
    fun hz ↦ ⟨connectedComponentIn_subset _ _ hz, fun hzC ↦ hd.notMem_of_mem_left hzC hz⟩⟩

/-- The other component of a two-point deletion is connected. -/
lemma isConnected_sdiff_connectedComponentIn_pair (hS : IsCircuit S) (ha : a ∈ S) (hb : b ∈ S)
    (hab : a ≠ b) (hu : u ∈ S \ {a, b}) :
    IsConnected ((S \ {a, b}) \ connectedComponentIn (S \ {a, b}) u) := by
  obtain ⟨v, hv, hne⟩ := exists_connectedComponentIn_ne
    (hS.pair_puncture_not_isPreconnected ha hb hab) u
  rw [hS.sdiff_connectedComponentIn_pair_eq hu ⟨hv, fun h ↦ hne (connectedComponentIn_eq h)⟩]
  exact isConnected_connectedComponentIn_iff.mpr hv

/-- Deleting two distinct members of a circuit leaves exactly two connected components. -/
theorem card_connectedComponents_sdiff_pair (hS : IsCircuit S) (ha : a ∈ S) (hb : b ∈ S)
    (hab : a ≠ b) : Nat.card (ConnectedComponents ↥(S \ {a, b})) = 2 := by
  let U := S \ {a, b}
  have hnot : ¬ IsPreconnected U := hS.pair_puncture_not_isPreconnected ha hb hab
  rcases eq_empty_or_nonempty U with hU | ⟨u, hu⟩
  · exact (hnot (hU.symm ▸ isPreconnected_empty)).elim
  obtain ⟨v, hv, hne⟩ := exists_connectedComponentIn_ne hnot u
  exact ConnectedComponents.card_eq_two_of_connectedComponentIn_union hu hv hne
    (hS.connectedComponentIn_union_connectedComponentIn hu hv hne)

open scoped Classical in
/-- The exact count, including repeated points and points outside the circuit. -/
theorem card_connectedComponents_sdiff_pair_eq (hS : IsCircuit S) (a b : X) :
    Nat.card (ConnectedComponents ↥(S \ {a, b})) =
      if a ∈ S ∧ b ∈ S ∧ a ≠ b then 2 else 1 := by
  classical
  split_ifs with h
  · exact hS.card_connectedComponents_sdiff_pair h.1 h.2.1 h.2.2
  · let := isConnected_iff_connectedSpace.mp (hS.isConnected_sdiff_pair_iff.mpr h)
    exact Nat.card_unique

/-- Every two-point deletion has finitely many components, without restrictions on the points. -/
theorem finite_connectedComponents_sdiff_pair (hS : IsCircuit S) (a b : X) :
    Finite (ConnectedComponents ↥(S \ {a, b})) := by
  apply Nat.finite_of_card_ne_zero
  rw [hS.card_connectedComponents_sdiff_pair_eq a b]
  split_ifs <;> decide

/-- Adjoining one deleted endpoint to a component of a two-point puncture
preserves connectedness. -/
lemma isConnected_insert_connectedComponentIn_pair (hS : IsCircuit S) (ha : a ∈ S) :
    IsConnected (insert a (connectedComponentIn (S \ {a, b}) u)) := by
  obtain hu | hu := em' (u ∈ S \ {a, b})
  · simpa [connectedComponentIn_eq_empty hu] using isConnected_singleton (x := a)
  obtain hvalid | ⟨_, hb, hab⟩ := em' (a ∈ S ∧ b ∈ S ∧ a ≠ b)
  · rw [(hS.isConnected_sdiff_pair_iff.mpr hvalid).isPreconnected.connectedComponentIn hu]
    convert hS.isConnected
    grind
  obtain ⟨v, hv, hne⟩ := exists_connectedComponentIn_ne
    (hS.pair_puncture_not_isPreconnected ha hb hab) u
  rw [← hS.sdiff_connectedComponentIn_pair_eq hv ⟨hu, fun h ↦ hne (connectedComponentIn_eq h).symm⟩]
  convert (hS.isConnected_sdiff_singleton b).isPreconnected
    |>.isConnected_sdiff_connectedComponentIn_sdiff_singleton (y := v) ⟨ha, hab⟩
  rw [(show (S \ {b}) \ {a} = S \ {a, b} by grind)]
  ext z
  have haC : a ∉ connectedComponentIn (S \ {a, b}) v :=
    disjoint_connectedComponentIn_sdiff.notMem_of_mem_right (Or.inl rfl)
  obtain rfl | hza := eq_or_ne z a
  · simp [ha, hab, haC]
  simp [hza, and_assoc]

/-- Adjoining both deleted endpoints to a component of a two-point puncture
preserves connectedness. -/
lemma isConnected_union_pair_connectedComponentIn (hS : IsCircuit S) (ha : a ∈ S) (hb : b ∈ S)
    (hu : u ∈ S \ {a, b}) : IsConnected (connectedComponentIn (S \ {a, b}) u ∪ {a, b}) := by
  have haC := hS.isConnected_insert_connectedComponentIn_pair (b := b) (u := u) ha
  have hbC : IsConnected (insert b (connectedComponentIn (S \ {a, b}) u)) := by
    simpa only [pair_comm b a] using
      hS.isConnected_insert_connectedComponentIn_pair (b := a) (u := u) hb
  have huC := mem_connectedComponentIn hu
  convert haC.union ⟨u, mem_insert_of_mem _ huC, mem_insert_of_mem _ huC⟩ hbC using 1
  ext z
  grind

private lemma isConnected_sdiff_component_pair (hS : IsCircuit S) (ha : a ∈ S) (hb : b ∈ S)
    (hab : a ≠ b) (hu : u ∈ S \ {a, b}) :
    IsConnected (S \ connectedComponentIn (S \ {a, b}) u) := by
  obtain ⟨v, hv, hne⟩ := exists_connectedComponentIn_ne
    (hS.pair_puncture_not_isPreconnected ha hb hab) u
  convert hS.isConnected_union_pair_connectedComponentIn ha hb hv using 1
  rw [← hS.sdiff_connectedComponentIn_pair_eq hu ⟨hv, fun h ↦ hne (connectedComponentIn_eq h)⟩]
  ext z
  grind [connectedComponentIn_subset (S \ {a, b}) u (a := z)]

private lemma isPreconnected_sdiff (hS : IsCircuit S) (hAS : A ⊆ S) (hA : IsPreconnected A) :
    IsPreconnected (S \ A) := by
  obtain rfl | ⟨a, ha⟩ := A.eq_empty_or_nonempty
  · simpa using hS.isPreconnected
  refine isPreconnected_of_forall_pair fun x hx y hy ↦ ?_
  obtain rfl | hxy := eq_or_ne x y
  · exact ⟨{x}, singleton_subset_iff.mpr hx, rfl, rfl, isPreconnected_singleton⟩
  have hAp : A ⊆ S \ {x, y} := by grind
  have hAC := hA.subset_connectedComponentIn ha hAp
  refine ⟨S \ connectedComponentIn (S \ {x, y}) a, (fun z hz ↦ ⟨hz.1, fun hzA ↦ hz.2 (hAC hzA)⟩),
    ?_, ?_, (hS.isConnected_sdiff_component_pair hx.1 hy.1 hxy (hAp ha)).isPreconnected⟩
  · exact ⟨hx.1, disjoint_connectedComponentIn_sdiff.notMem_of_mem_right (Or.inl rfl)⟩
  exact ⟨hy.1, disjoint_connectedComponentIn_sdiff.notMem_of_mem_right (Or.inr rfl)⟩

/-- A subset of a circuit is preconnected exactly when its relative complement is preconnected. -/
lemma isPreconnected_sdiff_iff (hS : IsCircuit S) (hAS : A ⊆ S) :
    IsPreconnected (S \ A) ↔ IsPreconnected A := by
  refine ⟨fun h ↦ ?_, hS.isPreconnected_sdiff hAS⟩
  simpa only [sdiff_sdiff_cancel_left hAS] using hS.isPreconnected_sdiff sdiff_subset h

/-- Two preconnected subsets with proper union have preconnected intersection. -/
lemma isPreconnected_inter (hS : IsCircuit S) (hAS : A ⊆ S) (hBS : B ⊆ S) (hA : IsPreconnected A)
    (hB : IsPreconnected B) (hproper : A ∪ B ≠ S) : IsPreconnected (A ∩ B) := by
  obtain ⟨z, hzS, hz⟩ := not_subset.mp <| fun h ↦ hproper ((union_subset hAS hBS).antisymm h)
  have h := IsPreconnected.union (s := S \ A) (t := S \ B) z ⟨hzS, fun h ↦ hz (Or.inl h)⟩
    ⟨hzS, fun h ↦ hz (Or.inr h)⟩ ((hS.isPreconnected_sdiff_iff hAS).mpr hA)
    ((hS.isPreconnected_sdiff_iff hBS).mpr hB)
  rw [← hS.isPreconnected_sdiff_iff (inter_subset_left.trans hAS)]
  simpa only [sdiff_inter] using h

/-- The carrier of an intrinsic circuit is T1, without an ambient separation assumption. -/
lemma t1Space (hS : IsCircuit S) : T1Space ↥S := by
  have hU := isCircuit_iff_subtype.mp hS
  refine t1Space_iff_specializes_imp_eq.mpr fun x y hxy ↦ by_contra fun hne ↦ ?_
  refine hU.pair_puncture_not_isPreconnected (mem_univ x) (mem_univ y) hne
    ((hU.isPreconnected_sdiff_iff (subset_univ _)).mpr ?_)
  refine isPreconnected_singleton.subset_closure (singleton_subset_iff.mpr (Or.inl rfl)) ?_
  rintro z (rfl | rfl)
  · exact subset_closure (by simp)
  exact hxy.mem_closure

/-- A circuit contained in another circuit is the whole circuit. -/
theorem eq_of_subset {T : Set X} (hS : IsCircuit S) (hT : IsCircuit T) (hTS : T ⊆ S) : T = S := by
  classical
  by_contra hne
  obtain ⟨a, ha, b, hb, hab⟩ := hT.nontrivial
  have hproper : (T \ {a}) ∪ (T \ {b}) ≠ S := by
    intro heq
    apply hne
    exact hTS.antisymm (heq ▸ union_subset sdiff_subset sdiff_subset)
  have hc := hS.isPreconnected_inter (sdiff_subset.trans hTS) (sdiff_subset.trans hTS)
    (hT.isConnected_sdiff_singleton a).isPreconnected
    (hT.isConnected_sdiff_singleton b).isPreconnected hproper
  apply hT.pair_puncture_not_isPreconnected ha hb hab
  convert hc using 1
  ext t
  simp only [mem_sdiff, mem_inter_iff, mem_insert_iff, mem_singleton_iff]
  grind

end IsCircuit
