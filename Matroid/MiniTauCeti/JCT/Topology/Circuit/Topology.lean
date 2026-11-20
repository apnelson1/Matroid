module

public import Matroid.MiniTauCeti.JCT.Topology.Circuit.Components
public import Matroid.MiniTauCeti.JCT.Topology.PrimitivePath
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Perfect
public import Mathlib.Topology.Separation.Connected
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.Compact

/-!
# Relative topology of intrinsic circuits

Components of a pair puncture are open. The closure of a nonempty component adjoins exactly
the deleted points, which may coincide, and its frontier is the deleted pair. For distinct
deleted points, they are the only non-cut points of the completed component.
All closures and frontiers are taken in the circuit carrier, without ambient separation
assumptions. Openness and endpoint closure follow the argument of Khanfir–Seguin,
*Flimsy Spaces*, Lemma 4.2.
-/

@[expose] public section

open Set Topology

namespace IsCircuit

variable {X K : Type*} [TopologicalSpace X] [TopologicalSpace K] {S : Set X}

/-- A space whose universe is a circuit is T1. -/
lemma t1Space_univ (hK : IsCircuit (univ : Set K)) : T1Space K :=
  let := hK.t1Space
  (Homeomorph.Set.univ K).symm.isEmbedding.t1Space

/-- An intrinsic circuit has infinitely many points. -/
lemma infinite (hS : IsCircuit S) : S.Infinite :=
  let := hS.t1Space
  let := Subtype.connectedSpace hS.isConnected
  let := nontrivial_coe_sort.mpr hS.nontrivial
  infinite_coe_iff.mp PreconnectedSpace.infinite

/-- The carrier of an intrinsic circuit has no isolated points. -/
lemma perfectSpace (hS : IsCircuit S) : PerfectSpace ↥S :=
  let := hS.t1Space
  let := Subtype.connectedSpace hS.isConnected
  let := nontrivial_coe_sort.mpr hS.nontrivial
  inferInstance

variable (hK : IsCircuit (univ : Set K)) {p q r : K}
include hK

/-- Each component of a two-point puncture is open in the circuit carrier. -/
lemma isOpen_connectedComponentIn_pair : IsOpen (connectedComponentIn ({p, q}ᶜ : Set K) r) :=
  let := hK.t1Space_univ
  let : Finite (ConnectedComponents ↥({p, q}ᶜ : Set K)) :=
    (congrArg (fun U : Set K ↦ Finite (ConnectedComponents ↥U))
      (compl_eq_univ_sdiff {p, q})).mpr (hK.finite_connectedComponents_sdiff_pair p q)
  ((finite_singleton q).insert p).isClosed.isOpen_compl.connectedComponentIn_of_finite r

private lemma endpoint_mem_closure (hpq : p ≠ q) (hr : r ∉ ({p, q} : Set K)) :
    p ∈ closure (connectedComponentIn ({p, q}ᶜ : Set K) r) := by
  by_contra hp
  have hsub := (hK.isConnected_sdiff_singleton q).isPreconnected.subset_of_closure_inter_subset
    hK.isOpen_connectedComponentIn_pair
    (⟨r, ⟨trivial, (hr <| Or.inr ·)⟩, mem_connectedComponentIn hr⟩) (by
      refine fun z hz ↦ closure_connectedComponentIn_inter.subset ⟨hz.left, ?_⟩
      rintro (rfl | rfl)
      · exact hp hz.left
      exact hz.right.right rfl)
  exact connectedComponentIn_subset _ _ (hsub ⟨trivial, hpq⟩) <| Or.inl rfl

/-- Closing a nonempty component of a pair puncture adjoins exactly the deleted points,
which may coincide. -/
lemma closure_connectedComponentIn_pair (hr : r ∉ ({p, q} : Set K)) :
    closure (connectedComponentIn ({p, q}ᶜ : Set K) r) =
      connectedComponentIn ({p, q}ᶜ : Set K) r ∪ {p, q} := by
  by_cases hpq : p = q
  · subst q
    have hc : IsPreconnected ({p}ᶜ : Set K) := by
      simpa only [compl_eq_univ_sdiff] using (hK.isConnected_sdiff_singleton p).isPreconnected
    have hr' : r ∈ ({p}ᶜ : Set K) := by simpa using hr
    let := hK.t1Space_univ
    let := connectedSpace_iff_univ.mpr hK.isConnected
    let := Set.nontrivial_univ_iff.mp hK.nontrivial
    simp only [pair_eq_singleton, hc.connectedComponentIn hr', closure_compl_singleton,
      compl_union_self]
  apply Subset.antisymm
  · intro z hz
    by_cases hzp : z ∈ ({p, q} : Set K)
    · exact Or.inr hzp
    exact Or.inl (closure_connectedComponentIn_inter.subset ⟨hz, hzp⟩)
  apply union_subset subset_closure
  intro z hz
  rcases hz with hz | hz
  · rw [hz]
    exact hK.endpoint_mem_closure hpq hr
  · rw [hz]
    simpa only [pair_comm q p] using hK.endpoint_mem_closure (Ne.symm hpq)
      (show r ∉ ({q, p} : Set K) by simpa only [pair_comm] using hr)

/-- The frontier of a component of a two-point puncture is the deleted pair. -/
lemma frontier_connectedComponentIn_pair (hr : r ∉ ({p, q} : Set K)) :
    frontier (connectedComponentIn ({p, q}ᶜ : Set K) r) = {p, q} := by
  rw [hK.isOpen_connectedComponentIn_pair.frontier_eq,
    hK.closure_connectedComponentIn_pair hr]
  ext z
  have hz := connectedComponentIn_subset ({p, q}ᶜ : Set K) r (a := z)
  simp only [mem_sdiff, mem_union, mem_compl_iff] at hz ⊢
  exact ⟨fun h ↦ h.1.resolve_left h.2, fun h ↦ ⟨Or.inr h, fun hC ↦ hz hC h⟩⟩

/-- The two completed components cover the carrier and intersect exactly at the endpoints. -/
lemma closure_components_union_inter {s : K}
    (hr : r ∉ ({p, q} : Set K)) (hs : s ∉ ({p, q} : Set K))
    (hne : connectedComponentIn ({p, q}ᶜ : Set K) r ≠
      connectedComponentIn ({p, q}ᶜ : Set K) s) :
    closure (connectedComponentIn ({p, q}ᶜ : Set K) r) ∪
        closure (connectedComponentIn ({p, q}ᶜ : Set K) s) = univ ∧
      closure (connectedComponentIn ({p, q}ᶜ : Set K) r) ∩
        closure (connectedComponentIn ({p, q}ᶜ : Set K) s) = {p, q} := by
  rw [hK.closure_connectedComponentIn_pair hr,
    hK.closure_connectedComponentIn_pair hs]
  have hcover := hK.connectedComponentIn_union_connectedComponentIn
    (show r ∈ univ \ {p, q} from ⟨trivial, hr⟩)
    (show s ∈ univ \ {p, q} from ⟨trivial, hs⟩)
    (by simpa only [← compl_eq_univ_sdiff] using hne)
  simp only [← compl_eq_univ_sdiff] at hcover
  refine ⟨eq_univ_of_forall fun z ↦ ?_, ?_⟩
  · by_cases hz : z ∈ ({p, q} : Set K)
    · exact Or.inl (Or.inr hz)
    have h := (congrArg (z ∈ ·) hcover).mpr hz
    exact h.elim (fun h ↦ Or.inl (Or.inl h)) (fun h ↦ Or.inr (Or.inl h))
  ext z
  refine ⟨?_, fun h ↦ ⟨Or.inr h, Or.inr h⟩⟩
  rintro ⟨h | h, h' | h'⟩
  · exact ((disjoint_connectedComponentIn_of_ne hne).notMem_of_mem_left h h').elim
  all_goals assumption

/-- The only non-cut points of a completed puncture component are its endpoints. -/
lemma noncut_closure_component_iff (hpq : p ≠ q) {w : K}
    (hw : w ∈ closure (connectedComponentIn ({p, q}ᶜ : Set K) r)) :
    IsPreconnected (closure (connectedComponentIn ({p, q}ᶜ : Set K) r) \ {w}) ↔
      w = p ∨ w = q := by
  have hr : r ∉ ({p, q} : Set K) :=
    connectedComponentIn_nonempty_iff.mp (closure_nonempty_iff.mp ⟨w, hw⟩)
  rw [hK.closure_connectedComponentIn_pair hr] at hw ⊢
  refine ⟨fun hconn ↦ by_contra fun hwpq ↦ ?_, ?_⟩
  · have hwC : w ∈ connectedComponentIn ({p, q}ᶜ : Set K) r := hw.resolve_right hwpq
    obtain ⟨s, hs, hne⟩ := exists_connectedComponentIn_ne
      (hK.pair_puncture_not_isPreconnected (mem_univ p) (mem_univ q) hpq) r
    simp only [← compl_eq_univ_sdiff] at hs hne
    have hsC : s ∉ connectedComponentIn ({p, q}ᶜ : Set K) r := (hne <| connectedComponentIn_eq ·)
    let A := (connectedComponentIn ({p, q}ᶜ : Set K) r ∪ {p, q}) \ {w}
    have hcomp : IsPreconnected (univ \ A) :=
      (hK.isPreconnected_sdiff_iff (subset_univ A)).mpr hconn
    have hscomp : s ∈ univ \ A := ⟨trivial, fun h ↦ h.1.elim hsC hs⟩
    have hsub : univ \ A ⊆ ({p, q}ᶜ : Set K) :=
      fun z hz hzpq ↦ hz.2 ⟨Or.inr hzpq, fun hzw ↦ hwpq (hzw ▸ hzpq)⟩
    have hwcomp : w ∈ univ \ A := ⟨trivial, fun h ↦ h.2 rfl⟩
    have hwD := hcomp.subset_connectedComponentIn hscomp hsub hwcomp
    exact hne ((connectedComponentIn_eq hwC).trans (connectedComponentIn_eq hwD).symm)
  have hz := connectedComponentIn_subset ({p, q}ᶜ : Set K) r
  rintro (rfl | rfl)
  · have heq : (connectedComponentIn ({w, q}ᶜ : Set K) r ∪ {w, q}) \ {w} =
      insert q (connectedComponentIn ({w, q}ᶜ : Set K) r) := by grind
    simpa only [heq, pair_comm q w, ← compl_eq_univ_sdiff] using
      (hK.isConnected_insert_connectedComponentIn_pair (b := w) (u := r)
        (mem_univ q)).isPreconnected
  have heq : (connectedComponentIn ({p, w}ᶜ : Set K) r ∪ {p, w}) \ {w} =
      insert p (connectedComponentIn ({p, w}ᶜ : Set K) r) := by grind
  simpa only [heq, ← compl_eq_univ_sdiff] using
    (hK.isConnected_insert_connectedComponentIn_pair (b := w) (u := r)
      (mem_univ p)).isPreconnected

end IsCircuit

/-- No subset of a linear order with closed order relation is an intrinsic circuit. -/
lemma not_isCircuit_of_orderClosedTopology {α : Type*} [LinearOrder α] [TopologicalSpace α]
    [OrderClosedTopology α] (S : Set α) : ¬ IsCircuit S := by
  intro hS
  have hcut {a b c : α} (ha : a ∈ S) (hc : c ∈ S) (hab : a < b) (hbc : b < c) : False :=
    ((hS.isConnected_sdiff_singleton b).isPreconnected.Icc_subset
      ⟨ha, ne_of_lt hab⟩ ⟨hc, ne_of_gt hbc⟩ ⟨hab.le, hbc.le⟩).2 rfl
  have hpair {a b : α} (ha : a ∈ S) (hb : b ∈ S) (hab : a < b) : False := by
    obtain ⟨c, hc, hcab⟩ := (hS.infinite.sdiff ((finite_singleton b).insert a)).nonempty
    have hca : c ≠ a := fun h ↦ hcab (Or.inl h)
    have hcb : c ≠ b := fun h ↦ hcab (Or.inr h)
    rcases lt_or_gt_of_ne hca with hca | hac
    · exact hcut hc hb hca hab
    rcases lt_or_gt_of_ne hcb with hcb | hbc
    · exact hcut ha hb hac hcb
    · exact hcut ha hc hab hbc
  obtain ⟨a, ha, b, hb, hab⟩ := hS.nontrivial
  rcases lt_or_gt_of_ne hab with h | h
  · exact hpair ha hb h
  · exact hpair hb ha h

/-- No subset of the real line is an intrinsic circuit. -/
lemma not_isCircuit_real (S : Set ℝ) : ¬ IsCircuit S :=
  not_isCircuit_of_orderClosedTopology S

private lemma IsCircuit.false_of_ordered_triple {D X : Type*}
    [LinearOrder D] [TopologicalSpace D] [OrderTopology D] [CompactIccSpace D]
    [TopologicalSpace X] [T2Space X] {K : Set X} (hK : IsCircuit K)
    {f : D → X} (hf : IsOpenEmbedding f) {a b c : D}
    (hb : f b ∈ K) (hc : f c ∉ K)
    (hab : a < b) (hbc : b < c) : False := by
  have hout : ¬ K ⊆ range f := by
    intro hsub
    apply not_isCircuit_of_orderClosedTopology (f ⁻¹' K)
    apply hf.isEmbedding.isCircuit_image.mp
    rwa [image_preimage_eq_of_subset hsub]
  have hcl : closure (f '' Ioo a c) ⊆ f '' Icc a c :=
    closure_minimal (image_mono Ioo_subset_Icc_self)
      (isCompact_Icc.image hf.continuous).isClosed
  have hsub := (hK.isConnected_sdiff_singleton (f a)).isPreconnected
    |>.subset_of_closure_inter_subset (hf.isOpenMap _ isOpen_Ioo)
      ⟨f b, ⟨hb, hf.injective.ne hab.ne'⟩, b, ⟨hab, hbc⟩, rfl⟩ (by
        rintro x ⟨hxcl, hxK, hxa⟩
        obtain ⟨t, ht, rfl⟩ := hcl hxcl
        refine ⟨t, ⟨lt_of_le_of_ne ht.1 ?_, lt_of_le_of_ne ht.2 ?_⟩, rfl⟩
        · intro heq
          exact hxa (congrArg f heq.symm)
        · intro heq
          exact hc (heq ▸ hxK))
  apply hout
  intro x hx
  by_cases hxa : x = f a
  · exact hxa.symm ▸ mem_range_self a
  exact image_subset_range _ _ (hsub ⟨hx, hxa⟩)

/-- In an open interval chart with compact closed intervals, the trace of an intrinsic
circuit is closed. This uses no compactness of the circuit. -/
theorem IsCircuit.isClosed_preimage_of_isOpenEmbedding {D X : Type*}
    [LinearOrder D] [TopologicalSpace D] [OrderTopology D] [CompactIccSpace D]
    [TopologicalSpace X] [T2Space X] {K : Set X} (hK : IsCircuit K)
    {f : D → X} (hf : IsOpenEmbedding f) : IsClosed (f ⁻¹' K) := by
  classical
  by_cases hall : f ⁻¹' K = univ
  · rw [hall]
    exact isClosed_univ
  obtain ⟨z, hz⟩ := not_forall.mp (mt eq_univ_of_forall hall)
  have hleft : (f ⁻¹' K ∩ Iio z).Subsingleton := by
    intro a ha b hb
    rcases lt_trichotomy a b with hab | rfl | hba
    · exact (hK.false_of_ordered_triple hf hb.1 hz hab hb.2).elim
    · rfl
    · exact (hK.false_of_ordered_triple hf ha.1 hz hba ha.2).elim
  have hright : (f ⁻¹' K ∩ Ioi z).Subsingleton := by
    intro a ha b hb
    rcases lt_trichotomy a b with hab | rfl | hba
    · exact (hK.false_of_ordered_triple (D := Dᵒᵈ) hf ha.1 hz hab ha.2).elim
    · rfl
    · exact (hK.false_of_ordered_triple (D := Dᵒᵈ) hf hb.1 hz hba hb.2).elim
  have heq : f ⁻¹' K = (f ⁻¹' K ∩ Iio z) ∪ (f ⁻¹' K ∩ Ioi z) := by
    ext x
    simp only [mem_preimage, mem_union, mem_inter_iff, mem_Iio, mem_Ioi]
    exact ⟨fun hx ↦ (lt_or_gt_of_ne (fun (heq : x = z) ↦ hz (heq ▸ hx))).elim
      (fun h ↦ Or.inl ⟨hx, h⟩) (fun h ↦ Or.inr ⟨hx, h⟩), fun h ↦ h.elim And.left And.left⟩
  rw [heq]
  exact (hleft.finite.union hright.finite).isClosed

/-- A chart on an order without endpoints is either disjoint from an intrinsic circuit
or entirely contained in it. No compactness of the circuit is needed. -/
theorem IsCircuit.range_subset_of_isOpenEmbedding {D X : Type*}
    [LinearOrder D] [TopologicalSpace D] [OrderTopology D] [CompactIccSpace D]
    [NoMinOrder D] [NoMaxOrder D] [TopologicalSpace X] [T2Space X]
    {K : Set X} (hK : IsCircuit K) {f : D → X} (hf : IsOpenEmbedding f)
    (hne : (K ∩ range f).Nonempty) : range f ⊆ K := by
  obtain ⟨_, hb, b, rfl⟩ := hne
  rintro _ ⟨c, rfl⟩
  by_contra hc
  have hbc : b ≠ c := fun h ↦ hc (h ▸ hb)
  rcases lt_or_gt_of_ne hbc with hbc | hcb
  · obtain ⟨a, hab⟩ := exists_lt b
    exact hK.false_of_ordered_triple hf hb hc hab hbc
  · obtain ⟨a, hba⟩ := exists_gt b
    exact hK.false_of_ordered_triple (D := Dᵒᵈ) hf hb hc hba hcb

private lemma IsCircuit.source_mem_of_interior_subset {X : Type*}
    [TopologicalSpace X] [T2Space X] {K : Set X} (hK : IsCircuit K)
    {a b : X} {P : Path a b} (hP : P.IsPrimitive)
    (hopen : IsOpen P.Interior) (hsub : P.Interior ⊆ K) : a ∈ K := by
  open unitInterval in
  by_contra ha
  have hf : IsOpenEmbedding (fun t : Ioo (0 : unitInterval) 1 ↦ P t) :=
    ⟨IsEmbedding.subtypeVal.comp hP.isOpenEmbedding_interior.isEmbedding, by
      simpa only [← image_eq_range, Path.Interior] using hopen⟩
  let q : unitInterval := unitInterval.half
  obtain ⟨s, hs0, hsq⟩ := exists_between (show (0 : unitInterval) < q from
    unitInterval.zero_lt_half)
  obtain ⟨t, hqt, ht1⟩ := exists_between (show q < (1 : unitInterval) from
    unitInterval.half_lt_one)
  have hq : q ∈ Ioo (0 : unitInterval) 1 :=
    ⟨unitInterval.zero_lt_half, unitInterval.half_lt_one⟩
  have hs : s ∈ Ioo (0 : unitInterval) 1 := ⟨hs0, hsq.trans hq.2⟩
  have ht : t ∈ Ioo (0 : unitInterval) 1 := ⟨hq.1.trans hqt, ht1⟩
  have ho : IsOpen (P '' Ioo 0 q) := by
    convert hf.isOpenMap (Subtype.val ⁻¹' Ioo 0 q)
      (isOpen_Ioo.preimage continuous_subtypeVal) using 1
    ext z
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, ⟨hu.1, hu.2.trans hq.2⟩⟩, hu, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u, hu, rfl⟩
  have hcl : closure (P '' Ioo 0 q) ⊆ P '' Icc 0 q :=
    closure_minimal (image_mono Ioo_subset_Icc_self)
      (isCompact_Icc.image P.continuous).isClosed
  have hcontain := (hK.isConnected_sdiff_singleton (P q)).isPreconnected
    |>.subset_of_closure_inter_subset ho
      ⟨P s, ⟨hsub ⟨s, hs, rfl⟩, fun heq ↦ hsq.ne (hP.injOn_Ioo hs hq heq)⟩,
        s, ⟨hs0, hsq⟩, rfl⟩ (by
      rintro z ⟨hzcl, hzK, hzq⟩
      obtain ⟨u, hu, rfl⟩ := hcl hzcl
      refine ⟨u, ⟨lt_of_le_of_ne hu.1 ?_, lt_of_le_of_ne hu.2 ?_⟩, rfl⟩
      · intro heq
        exact ha (by simpa only [← heq, Path.source] using hzK)
      · intro heq
        exact hzq (congrArg P heq))
  obtain ⟨u, hu, heq⟩ := hcontain
    ⟨hsub ⟨t, ht, rfl⟩, fun heq ↦ hqt.ne' (hP.injOn_Ioo ht hq heq)⟩
  have hut := hP.injOn_Ioo ⟨hu.1, hu.2.trans hq.2⟩ ht heq
  exact (hu.2.trans hqt).ne hut

/-- A primitive path with open interior that meets an intrinsic circuit in its interior
lies entirely in the circuit. Compactness of the circuit is unnecessary. -/
theorem IsCircuit.range_subset_of_isPrimitive {X : Type*}
    [TopologicalSpace X] [T2Space X] {K : Set X} (hK : IsCircuit K)
    {a b : X} {P : Path a b} (hP : P.IsPrimitive)
    (hopen : IsOpen P.Interior) (hne : (K ∩ P.Interior).Nonempty) : range P ⊆ K := by
  have hf : IsOpenEmbedding (fun t : Ioo (0 : unitInterval) 1 ↦ P t) :=
    ⟨IsEmbedding.subtypeVal.comp hP.isOpenEmbedding_interior.isEmbedding, by
      simpa only [← image_eq_range, Path.Interior] using hopen⟩
  have hsub : P.Interior ⊆ K := by
    simpa only [← image_eq_range, Path.Interior] using
      hK.range_subset_of_isOpenEmbedding hf (by
        simpa only [← image_eq_range, Path.Interior] using hne)
  have ha := hK.source_mem_of_interior_subset hP hopen hsub
  have hb := hK.source_mem_of_interior_subset hP.symm
    (by simpa using hopen) (by simpa using hsub)
  rintro z ⟨t, rfl⟩
  obtain rfl | rfl | ht := unitInterval.eq_zero_or_eq_one_or_mem_Ioo t
  · simpa using ha
  · simpa using hb
  exact hsub ⟨t, ht, rfl⟩
