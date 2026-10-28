module

public import Matroid.ForMathlib.Card
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Topology.Maps.Basic
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Order.OrderClosed

/-!
# Boundary crossings

Two-sided crossings of a set boundary, their local character, and intersection laws.
-/

@[expose] public section

open Set Function TopologicalSpace Topology Set.Notation Classical

variable {X : Type*} [TopologicalSpace X] {S T U V : Set X} {x p : X}

/-- The points of a set `S` at which the set `U` changes side: points of `S ∩ ∂U` that lie
in the closure of both `S ∩ int U` and `S ∩ int Uᶜ`.

These are crossings in the two-sided neighborhood sense: either closure condition alone
would also be satisfied by a tangential touch of `∂U` from one side, but a point lying in both
closures has points of `S` on both sides of `∂U` arbitrarily close to it. -/
def boundaryCrossings (S U : Set X) : Set X :=
  {p | p ∈ S ∩ frontier U ∧ p ∈ closure (S ∩ interior U) ∧ p ∈ closure (S ∩ interior Uᶜ)}

theorem mem_boundaryCrossings_iff :
    p ∈ boundaryCrossings S U ↔ p ∈ S ∧
      p ∈ closure (S ∩ interior U) ∧ p ∈ closure (S ∩ interior Uᶜ) := by
  constructor
  · exact fun h ↦ ⟨h.1.1, h.2⟩
  · rintro ⟨hp, hi, ho⟩
    refine ⟨⟨hp, ?_⟩, hi, ho⟩
    rw [frontier_eq_closure_inter_closure]
    exact ⟨closure_mono (inter_subset_right.trans interior_subset) hi,
      closure_mono (inter_subset_right.trans interior_subset) ho⟩

theorem boundaryCrossings_mono (hST : S ⊆ T) :
    boundaryCrossings S U ⊆ boundaryCrossings T U := by
  intro p hp
  exact ⟨⟨hST hp.1.1, hp.1.2⟩,
    closure_mono (inter_subset_inter_left _ hST) hp.2.1,
    closure_mono (inter_subset_inter_left _ hST) hp.2.2⟩

theorem boundaryCrossings_subset_carrier (S U : Set X) : boundaryCrossings S U ⊆ S :=
  fun _ h ↦ h.1.1

theorem boundaryCrossings_subset_frontier (S U : Set X) : boundaryCrossings S U ⊆ frontier U :=
  fun _ h ↦ h.1.2

lemma boundaryCrossings_subset (S U : Set X) : boundaryCrossings S U ⊆ S ∩ frontier U :=
  fun _ h => h.1

lemma boundaryCrossings_finite (hfin : (S ∩ frontier U).Finite) :
    (boundaryCrossings S U).Finite :=
  hfin.subset (boundaryCrossings_subset S U)

@[simp]
lemma boundaryCrossings_compl (S U : Set X) : boundaryCrossings S Uᶜ = boundaryCrossings S U := by
  ext p
  simp only [boundaryCrossings, mem_ofPred_eq, frontier_compl, compl_compl]
  tauto

/-- Continuous open maps preserve the two-sided neighborhood condition defining crossings. -/
lemma IsOpenMap.preimage_boundaryCrossings {Y : Type*} [TopologicalSpace Y] {f : X → Y}
    (hfopen : IsOpenMap f) (hfcont : Continuous f) (S U : Set Y) :
    boundaryCrossings (f ⁻¹' S) (f ⁻¹' U) = f ⁻¹' boundaryCrossings S U := by
  simp only [boundaryCrossings, ← hfopen.preimage_frontier_eq_frontier_preimage hfcont,
    ← hfopen.preimage_interior_eq_interior_preimage hfcont, ← preimage_compl,
    ← preimage_inter, ← hfopen.preimage_closure_eq_closure_preimage hfcont]
  rfl

private theorem germ_closure {A B : Set X} (h : A =ᶠ[𝓝 p] B) :
    p ∈ closure A ↔ p ∈ closure B := by
  rw [mem_closure_iff_nhdsWithin_neBot, mem_closure_iff_nhdsWithin_neBot,
    nhdsWithin_eq_iff_eventuallyEqSet.mpr h]

/-- Boundary crossings depend only on the germs of the carrier and region at the point. -/
lemma mem_boundaryCrossings_congr_germs {T V : Set X}
    (hST : S =ᶠ[𝓝 p] T) (hUV : U =ᶠ[𝓝 p] V) :
    p ∈ boundaryCrossings S U ↔ p ∈ boundaryCrossings T V := by
  have hinterior {A B : Set X} (h : A =ᶠ[𝓝 p] B) :
      interior A =ᶠ[𝓝 p] interior B := by
    filter_upwards [eventually_eventually_nhds.mpr h] with q hq
    exact propext (Filter.EventuallyEqSet.mem_interior_iff hq)
  have hside {A B : Set X} (h : A =ᶠ[𝓝 p] B) :
      p ∈ closure (S ∩ interior A) ↔ p ∈ closure (T ∩ interior B) :=
    germ_closure (hST.inter (hinterior h))
  simp only [mem_boundaryCrossings_iff, hside hUV, hside hUV.compl, hST.eq_of_nhds]

@[simp]
lemma boundaryCrossings_empty (S : Set X) : boundaryCrossings S ∅ = ∅ := by
  simp [boundaryCrossings]

theorem Continuous.mem_boundaryCrossings_preimage_Ioi_of_mem_closure {α : Type*}
    [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α]
    {f : X → α} (hf : Continuous f) {c : α} (hp : p ∈ S) (hi : p ∈ closure (S ∩ f ⁻¹' Ioi c))
    (ho : p ∈ closure (S ∩ f ⁻¹' Iio c)) :
    p ∈ boundaryCrossings S (f ⁻¹' Ioi c) := by
  apply mem_boundaryCrossings_iff.mpr
  refine ⟨hp, ?_, closure_mono (inter_subset_inter_right _ ?_) ho⟩
  · simpa only [(isOpen_Ioi.preimage hf).interior_eq] using hi
  · apply interior_maximal _ (isOpen_Iio.preimage hf)
    exact fun q hq hq' ↦ lt_asymm hq hq'

theorem IsOpenMap.mem_boundaryCrossings_preimage_Ioi_iff {α : Type*}
    [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α] {f : X → α}
    (hopen : IsOpenMap f) (hf : Continuous f) {c : α} :
    p ∈ boundaryCrossings S (f ⁻¹' Ioi c) ↔ p ∈ S ∧
      p ∈ closure (S ∩ f ⁻¹' Ioi c) ∧ p ∈ closure (S ∩ f ⁻¹' Iio c) := by
  constructor
  · intro hp
    have hpc := (frontier_lt_subset_eq continuous_const hf hp.1.2).symm
    have hfp : c ∈ frontier (Ioi c) := by
      have hh := hp.1.2
      rw [← hopen.preimage_frontier_eq_frontier_preimage hf] at hh
      simpa only [mem_preimage, hpc] using hh
    have hn : c ∉ interior (Iic c) := by
      have hc : c ∈ frontier (Iic c) := by
        simpa only [← compl_Ioi, frontier_compl] using hfp
      exact disjoint_interior_frontier.notMem_of_mem_right hc
    have hcomp : interior (f ⁻¹' Ioi c)ᶜ ⊆ f ⁻¹' Iio c := by
      rw [← preimage_compl, compl_Ioi,
        ← hopen.preimage_interior_eq_interior_preimage hf]
      intro q hq
      exact lt_of_le_of_ne (interior_subset hq) (fun heq ↦ hn (heq ▸ hq))
    refine ⟨hp.1.1, ?_, closure_mono (inter_subset_inter_right _ hcomp) hp.2.2⟩
    simpa only [(isOpen_Ioi.preimage hf).interior_eq] using hp.2.1
  · rintro ⟨hp, hi, ho⟩
    exact Continuous.mem_boundaryCrossings_preimage_Ioi_of_mem_closure hf hp hi ho

theorem boundaryCrossings_congr_germs (hST : S =ᶠ[𝓝 p] T) (hUV : U =ᶠ[𝓝 p] V) :
    boundaryCrossings S U =ᶠ[𝓝 p] boundaryCrossings T V := by
  filter_upwards [eventually_eventually_nhds.mpr hST,
    eventually_eventually_nhds.mpr hUV] with q hqST hqUV
  exact propext (mem_boundaryCrossings_congr_germs hqST hqUV)

theorem IsPreconnected.disjoint_frontier_iff (hS : IsPreconnected S) :
    Disjoint S (frontier U) ↔ S ⊆ interior U ∨ S ⊆ interior Uᶜ := by
  constructor
  · intro h
    apply hS.subset_or_subset isOpen_interior isOpen_interior
      (disjoint_compl_right.mono interior_subset interior_subset)
    intro x hx
    rw [← compl_frontier_eq_union_interior]
    exact h.notMem_of_mem_left hx
  · rintro (h | h)
    · exact disjoint_interior_frontier.mono_left h
    · simpa only [frontier_compl] using
        (disjoint_interior_frontier (s := Uᶜ)).mono_left h

private theorem interior_region_iff_of_isolated_contact
    (hiso : ∀ᶠ q in 𝓝 p, q ∈ S ∩ frontier U → q = p) :
    p ∈ boundaryCrossings S (interior U) ↔ p ∈ boundaryCrossings S U := by
  have hout : interior Uᶜ ⊆ interior (interior U)ᶜ :=
    interior_mono (compl_subset_compl.mpr interior_subset)
  constructor
  · intro hp
    have hpin : p ∈ closure (S ∩ interior U) := by simpa using hp.2.1
    have hpcl : p ∈ closure (interior U) := closure_mono inter_subset_right hpin
    have hgerm : S ∩ interior (interior U)ᶜ =ᶠ[𝓝 p] S ∩ interior Uᶜ := by
      filter_upwards [hiso] with q hq
      apply propext
      constructor
      · intro h
        refine ⟨h.1, ?_⟩
        by_contra hnot
        have hfr : q ∈ frontier U := by
          by_contra hfr
          have hside : q ∈ interior U ∪ interior Uᶜ := by
            rw [← compl_frontier_eq_union_interior]
            exact hfr
          exact hside.elim (interior_subset h.2) hnot
        have heq := hq ⟨h.1, hfr⟩
        subst q
        exact (show p ∉ closure (interior U) by
          simpa only [interior_compl, mem_compl_iff] using h.2) hpcl
      · exact fun h ↦ ⟨h.1, hout h.2⟩
    exact mem_boundaryCrossings_iff.mpr ⟨hp.1.1, hpin, (germ_closure hgerm).mp hp.2.2⟩
  · intro hp
    apply mem_boundaryCrossings_iff.mpr
    exact ⟨hp.1.1, by simpa using hp.2.1,
      closure_mono (inter_subset_inter_right S hout) hp.2.2⟩

theorem boundaryCrossings_interior_of_isDiscrete (hdis : IsDiscrete (S ∩ frontier U)) :
    boundaryCrossings S (interior U) = boundaryCrossings S U := by
  ext p
  by_cases hp : p ∈ S ∩ frontier U
  · obtain ⟨W, hWo, hW⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp hdis p hp
    have hpW : p ∈ W := by
      have : p ∈ W ∩ (S ∩ frontier U) := by rw [hW]; exact mem_singleton p
      exact this.1
    apply interior_region_iff_of_isolated_contact
    filter_upwards [hWo.mem_nhds hpW] with q hq hqF
    exact mem_singleton_iff.mp (hW ▸ ⟨hq, hqF⟩)
  · constructor
    · exact fun h ↦ (hp ⟨h.1.1, frontier_interior_subset h.1.2⟩).elim
    · exact fun h ↦ (hp h.1).elim

theorem IsPreconnected.subset_interior_iff_of_mem_closure {X : Type*} [TopologicalSpace X]
    {A U : Set X} {p : X} (hA : IsPreconnected A) (hAU : Disjoint A (frontier U))
    (hp : p ∈ closure A) (hpU : p ∉ frontier U) :
    A ⊆ interior U ↔ p ∈ U := by
  constructor
  · intro h
    have hc : p ∈ closure U := closure_mono (h.trans interior_subset) hp
    exact interior_subset (closure_sdiff_frontier U ▸ ⟨hc, hpU⟩)
  · intro hpU'
    rcases hA.disjoint_frontier_iff.mp hAU with h | h
    · exact h
    have hc : p ∈ closure Uᶜ := closure_mono (h.trans interior_subset) hp
    exact (hpU (frontier_eq_closure_inter_closure (s := U) ▸ ⟨subset_closure hpU', hc⟩)).elim

private theorem frontier_closure_of_closed_remainder {X : Type*} [TopologicalSpace X]
    {A B : Set X} (hB : IsOpen B) (hd : Disjoint A B)
    (hc : IsClosed (closure A ∪ closure B)ᶜ) :
    frontier (closure A) = closure A ∩ closure B := by
  have hsub : B ⊆ (closure A)ᶜ := by
    have h := closure_minimal (show A ⊆ Bᶜ from fun _ hp ↦ disjoint_left.mp hd hp)
      hB.isClosed_compl
    exact fun p hp hpcl ↦ h hpcl hp
  have hout : (closure A)ᶜ ⊆ closure B ∪ (closure A ∪ closure B)ᶜ := by
    intro p hp
    by_cases hb : p ∈ closure B
    · exact Or.inl hb
    · exact Or.inr (fun h ↦ h.elim hp hb)
  ext p
  rw [frontier_eq_closure_inter_closure, closure_closure]
  constructor
  · rintro ⟨hpA, hp⟩
    refine ⟨hpA, ?_⟩
    exact (closure_minimal hout (isClosed_closure.union hc) hp).resolve_right
      (fun h ↦ h (Or.inl hpA))
  · exact fun ⟨hpA, hpB⟩ ↦ ⟨hpA, closure_mono hsub hpB⟩

theorem frontier_closure_preimage_interior_eq_boundaryCrossings {X : Type*} [TopologicalSpace X]
    {S U : Set X} (hcontact : IsDiscrete (S ∩ frontier U)) :
    frontier (closure ((Subtype.val : S → X) ⁻¹' interior U)) =
      Subtype.val ⁻¹' boundaryCrossings S U := by
  let A : Set S := Subtype.val ⁻¹' interior U
  let B : Set S := Subtype.val ⁻¹' interior Uᶜ
  have hB : IsOpen B := isOpen_interior.preimage continuous_subtype_val
  have hLA : closure A = Subtype.val ⁻¹' closure (S ∩ interior U) := by
    dsimp only [A]
    rw [IsInducing.subtypeVal.closure_eq_preimage_closure_image,
      image_preimage_eq_inter_range, Subtype.range_val, inter_comm]
  have hLB : closure B = Subtype.val ⁻¹' closure (S ∩ interior Uᶜ) := by
    dsimp only [B]
    rw [IsInducing.subtypeVal.closure_eq_preimage_closure_image,
      image_preimage_eq_inter_range, Subtype.range_val, inter_comm]
  have hd : Disjoint A B := by
    apply disjoint_left.mpr
    intro q hq hq'
    exact ((disjoint_compl_right.mono interior_subset interior_subset :
      Disjoint (interior U) (interior Uᶜ)).notMem_of_mem_left hq) hq'
  have hdis : IsDiscrete ((Subtype.val : S → X) ⁻¹' frontier U) := by
    have heq : (Subtype.val : S → X) ⁻¹' (S ∩ frontier U) =
        (Subtype.val : S → X) ⁻¹' frontier U := by
      ext q
      exact and_iff_right q.property
    rw [← heq]
    exact hcontact.preimage continuous_subtype_val.continuousOn Subtype.val_injective
  have hclosed : IsClosed (closure A ∪ closure B)ᶜ := by
    apply isClosed_of_subset_discrete_closed ?_ hdis
      (isClosed_frontier.preimage continuous_subtype_val)
    intro q hq
    by_contra hfr
    have hside : q.val ∈ interior U ∪ interior Uᶜ := by
      rwa [← compl_frontier_eq_union_interior]
    apply hq
    exact hside.elim (fun h ↦ Or.inl (subset_closure h))
      (fun h ↦ Or.inr (subset_closure h))
  rw [frontier_closure_of_closed_remainder hB hd hclosed, hLA, hLB]
  ext q
  simp only [mem_inter_iff, mem_preimage, mem_boundaryCrossings_iff, q.property, true_and]

private theorem isDiscrete_contact_of_finite [T1Space ↥S]
    (hfin : (S ∩ frontier U).Finite) :
    IsDiscrete (S ∩ frontier U) := by
  have hF : ((Subtype.val : S → X) ⁻¹' frontier U).Finite := by
    have heq : (Subtype.val : S → X) ⁻¹' (S ∩ frontier U) =
        (Subtype.val : S → X) ⁻¹' frontier U := by
      ext q
      exact and_iff_right q.property
    rw [← heq]
    exact hfin.preimage Subtype.val_injective.injOn
  simpa only [Subtype.image_preimage_coe] using
    hF.isDiscrete.image Topology.IsInducing.subtypeVal

theorem boundary_evenness_iff_open_regions {X : Type*} [TopologicalSpace X]
    (S : Set X) [T1Space ↥S] :
    (∀ U : Set X, (S ∩ frontier U).Finite → Even (boundaryCrossings S U).ncard) ↔
      (∀ U : Set X, IsOpen U → (S ∩ frontier U).Finite →
        Even (boundaryCrossings S U).ncard) := by
  refine ⟨fun h U _ hfin ↦ h U hfin, fun h U hfin ↦ ?_⟩
  rw [← boundaryCrossings_interior_of_isDiscrete (isDiscrete_contact_of_finite hfin)]
  exact h (interior U) isOpen_interior
    (hfin.subset (inter_subset_inter_right S frontier_interior_subset))

theorem boundaryCrossings_eq_empty_of_isDiscrete {X : Type*} [TopologicalSpace X]
    {S U : Set X} (hS : IsDiscrete S) : boundaryCrossings S U = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨W, hWo, hWS⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp hS p hp.1.1
  have hpWS : p ∈ W ∩ S := hWS.symm ▸ mem_singleton p
  obtain ⟨q, hqW, hqS, hqU⟩ := mem_closure_iff.mp hp.2.1 W hWo hpWS.1
  have hqp : q = p := mem_singleton_iff.mp (hWS ▸ ⟨hqW, hqS⟩)
  exact hp.1.2.2 (hqp ▸ hqU)

@[simp] theorem boundaryCrossings_empty_carrier (U : Set X) : boundaryCrossings ∅ U = ∅ := by
  simp [boundaryCrossings]

@[simp] theorem boundaryCrossings_singleton (x : X) (U : Set X) :
    boundaryCrossings {x} U = ∅ := by
  apply boundaryCrossings_eq_empty_of_isDiscrete
  exact Set.Subsingleton.isDiscrete subsingleton_singleton

@[simp] theorem boundaryCrossings_univ (S : Set X) : boundaryCrossings S univ = ∅ := by
  simpa only [compl_empty] using
    (boundaryCrossings_compl S ∅).trans (boundaryCrossings_empty S)

/-- Inside one region, crossing its intersection with another region means crossing the other. -/
lemma mem_boundaryCrossings_inter_of_mem_interior {V : Set X}
    (hp : p ∈ interior V) :
    p ∈ boundaryCrossings S (U ∩ V) ↔ p ∈ boundaryCrossings S U := by
  apply mem_boundaryCrossings_congr_germs Filter.EventuallyEq.rfl
  filter_upwards [mem_interior_iff_mem_nhds.mp hp] with q hq
  exact propext (and_iff_left hq)

private lemma notMem_boundaryCrossings_of_mem_interior_compl
    (hp : p ∈ interior Uᶜ) : p ∉ boundaryCrossings S U :=
  fun h ↦ disjoint_interior_frontier.notMem_of_mem_left hp
    (frontier_compl (s := U) ▸ h.1.2)

/-- Away from common frontier points, a crossing of an intersection is a crossing of one
region in the interior of the other. -/
lemma mem_boundaryCrossings_inter {V : Set X} (hp : p ∉ frontier U ∩ frontier V) :
    p ∈ boundaryCrossings S (U ∩ V) ↔
      (p ∈ boundaryCrossings S U ∧ p ∈ interior V) ∨
      (p ∈ boundaryCrossings S V ∧ p ∈ interior U) := by
  have side {A : Set X} (h : p ∉ frontier A) :
      p ∈ interior A ∨ p ∈ interior Aᶜ := by
    rwa [← mem_union, ← compl_frontier_eq_union_interior]
  have outside {A B : Set X} (h : p ∈ interior Bᶜ) :
      p ∉ boundaryCrossings S (A ∩ B) := by
    apply notMem_boundaryCrossings_of_mem_interior_compl
    exact interior_mono (by intro q hq h; exact hq h.2) h
  by_cases hu : p ∈ frontier U
  · have hv : p ∉ frontier V := fun hv ↦ hp ⟨hu, hv⟩
    have hiu : p ∉ interior U := disjoint_interior_frontier.notMem_of_mem_right hu
    rcases side hv with hv | hv
    · simp [mem_boundaryCrossings_inter_of_mem_interior hv, hv, hiu]
    · have hiv : p ∉ interior V :=
        (disjoint_compl_right.mono interior_subset interior_subset).notMem_of_mem_right hv
      simp [outside hv, hiv, hiu]
  · rcases side hu with hu | hu
    · have h := mem_boundaryCrossings_inter_of_mem_interior (S := S) (U := V) hu
      rw [inter_comm V U] at h
      have hnu : p ∉ boundaryCrossings S U := fun h ↦
        disjoint_interior_frontier.notMem_of_mem_left hu h.1.2
      simp [h, hu, hnu]
    · have hiu : p ∉ interior U :=
        (disjoint_compl_right.mono interior_subset interior_subset).notMem_of_mem_right hu
      have hout : p ∉ boundaryCrossings S (U ∩ V) := by
        rw [inter_comm]; exact outside hu
      simp [hout, hiu, notMem_boundaryCrossings_of_mem_interior_compl hu]

theorem boundaryCrossings_inter_diff_common_frontier :
    boundaryCrossings S (U ∩ V) \ (frontier U ∩ frontier V) =
      (boundaryCrossings S U ∩ interior V) ∪ (boundaryCrossings S V ∩ interior U) := by
  ext p
  constructor
  · rintro ⟨hp, hn⟩
    exact (mem_boundaryCrossings_inter hn).mp hp
  · rintro (⟨hp, hi⟩ | ⟨hp, hi⟩)
    · have hn : p ∉ frontier U ∩ frontier V :=
        fun h ↦ disjoint_interior_frontier.notMem_of_mem_left hi h.2
      exact ⟨(mem_boundaryCrossings_inter hn).mpr (Or.inl ⟨hp, hi⟩), hn⟩
    · have hn : p ∉ frontier U ∩ frontier V :=
        fun h ↦ disjoint_interior_frontier.notMem_of_mem_left hi h.1
      exact ⟨(mem_boundaryCrossings_inter hn).mpr (Or.inr ⟨hp, hi⟩), hn⟩

theorem boundaryCrossings_inter_eq_iff :
    boundaryCrossings S (U ∩ V) =
        (boundaryCrossings S U ∩ interior V) ∪ (boundaryCrossings S V ∩ interior U) ↔
      Disjoint (boundaryCrossings S (U ∩ V)) (frontier U ∩ frontier V) := by
  rw [← boundaryCrossings_inter_diff_common_frontier, eq_comm, sdiff_eq_self_iff_disjoint]
  exact disjoint_comm

theorem boundaryCrossings_union_diff_common_frontier :
    boundaryCrossings S (U ∪ V) \ (frontier U ∩ frontier V) =
      (boundaryCrossings S U ∩ interior Vᶜ) ∪
        (boundaryCrossings S V ∩ interior Uᶜ) := by
  simpa only [← compl_union, boundaryCrossings_compl, frontier_compl] using
    (boundaryCrossings_inter_diff_common_frontier (S := S) (U := Uᶜ) (V := Vᶜ))

theorem boundaryCrossings_union_of_disjoint_frontier_closure
    (hST : Disjoint (S ∩ frontier U) (closure T))
    (hTS : Disjoint (T ∩ frontier U) (closure S)) :
    boundaryCrossings (S ∪ T) U = boundaryCrossings S U ∪ boundaryCrossings T U := by
  have hlocal {A B : Set X} {p : X} (hpB : p ∉ closure B) :
      p ∈ boundaryCrossings (A ∪ B) U ↔ p ∈ boundaryCrossings A U := by
    apply mem_boundaryCrossings_congr_germs _ Filter.EventuallyEq.rfl
    filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hpB] with q hq
    exact propext (or_iff_left (fun h ↦ hq (subset_closure h)))
  apply Subset.antisymm
  · intro p hp
    rcases hp.1.1 with hpS | hpT
    · exact Or.inl ((hlocal (hST.notMem_of_mem_left ⟨hpS, hp.1.2⟩)).mp hp)
    · apply Or.inr
      exact (hlocal (hTS.notMem_of_mem_left ⟨hpT, hp.1.2⟩)).mp
        (by simpa only [union_comm] using hp)
  · exact union_subset (boundaryCrossings_mono subset_union_left)
      (boundaryCrossings_mono subset_union_right)

theorem even_ncard_boundaryCrossings_union_of_disjoint_frontier_closure
    (hST : Disjoint (S ∩ frontier U) (closure T))
    (hTS : Disjoint (T ∩ frontier U) (closure S))
    (hEvenS : Even (boundaryCrossings S U).ncard)
    (hEvenT : Even (boundaryCrossings T U).ncard) :
    Even (boundaryCrossings (S ∪ T) U).ncard := by
  rw [boundaryCrossings_union_of_disjoint_frontier_closure hST hTS]
  exact Set.even_ncard_union
    (hST.mono (boundaryCrossings_subset S U)
      ((boundaryCrossings_subset T U).trans (inter_subset_left.trans subset_closure)))
    hEvenS hEvenT

private theorem finite_union_crossings_of_disjoint_frontier_closures {ι : Type*}
    (I : Finset ι) (C : ι → Set X)
    (hsep : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (C i ∩ frontier U) (closure (C j))) :
    boundaryCrossings (⋃ i ∈ I, C i) U = ⋃ i ∈ I, boundaryCrossings (C i) U := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert i I hi ih =>
    have hsepI : ∀ j ∈ I, ∀ k ∈ I, j ≠ k →
        Disjoint (C j ∩ frontier U) (closure (C k)) :=
      fun j hj k hk ↦ hsep j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk)
    have hleft : Disjoint (C i ∩ frontier U) (closure (⋃ j ∈ I, C j)) := by
      have hclosure : closure (⋃ j ∈ I, C j) = ⋃ j ∈ I, closure (C j) :=
        I.finite_toSet.closure_biUnion C
      rw [hclosure]
      simp only [disjoint_iUnion_right]
      intro j hj
      exact hsep i (by simp) j (Finset.mem_insert_of_mem hj) (fun h ↦ hi (h ▸ hj))
    have hright : Disjoint ((⋃ j ∈ I, C j) ∩ frontier U) (closure (C i)) := by
      rw [iUnion_inter]
      simp only [disjoint_iUnion_left, iUnion_inter]
      intro j hj
      exact hsep j (Finset.mem_insert_of_mem hj) i (by simp) (fun h ↦ hi (h ▸ hj))
    simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left]
    rw [boundaryCrossings_union_of_disjoint_frontier_closure hleft hright, ih hsepI]

theorem boundaryCrossings_biUnion_of_disjoint_frontier_closures {ι : Type*} {I : Set ι}
    (hI : I.Finite) (C : ι → Set X)
    (hsep : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (C i ∩ frontier U) (closure (C j))) :
    boundaryCrossings (⋃ i ∈ I, C i) U = ⋃ i ∈ I, boundaryCrossings (C i) U := by
  classical
  simpa only [hI.mem_toFinset] using
    finite_union_crossings_of_disjoint_frontier_closures hI.toFinset C
      (by simpa only [hI.mem_toFinset] using hsep)
