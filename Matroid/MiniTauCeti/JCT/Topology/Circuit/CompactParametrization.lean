module

public import Matroid.MiniTauCeti.JCT.Topology.Circuit.Separation
public import Matroid.MiniTauCeti.JCT.Topology.Circuit.Parametrization
public import Matroid.MiniTauCeti.JCT.Topology.PrimitiveLink
public import Mathlib.Topology.DenseEmbedding
public import Matroid.MiniTauCeti.JCT.Topology.CutPointInterval

/-!
# Ordinary parametrizations of compact separable circuits

Completed two-puncture components carry the separator order with the prescribed endpoints
as its bounds. Their interval parametrizations give ordinary simple loops and circle
homeomorphisms. Compactness and separability are required only in this classification.
-/

@[expose] public section

open Set Topology TopologicalSpace Function

private lemma separates_subtype {K : Type*} [TopologicalSpace K] {E : Set K}
    {a b w : E} (h : CutPoint.Separates E {w.val} a.val b.val) :
    CutPoint.Separates univ {w} a b := by
  have hE : (Subtype.val : E → K) ⁻¹' E = univ := by ext z; simp
  have hw : (Subtype.val : E → K) ⁻¹' {w.val} = {w} := by
    ext z
    simp only [mem_preimage, mem_singleton_iff, Subtype.val_inj]
  simpa only [hE, hw] using h.preimage continuous_subtype_val.continuousOn

/-- Parametrize a compact separable completed two-puncture component, preserving its endpoints.
Compactness and separability are needed only on this component, not on the whole circuit. -/
theorem IsCircuit.exists_path_range_closure_component {K : Type*} [TopologicalSpace K]
    (hK : IsCircuit (univ : Set K)) {p q r : K}
    [CompactSpace ↥(closure (connectedComponentIn ({p, q}ᶜ : Set K) r))]
    [SeparableSpace ↥(closure (connectedComponentIn ({p, q}ᶜ : Set K) r))]
    (hpq : p ≠ q) (hr : r ∉ ({p, q} : Set K)) :
    ∃ P : Path p q, Injective P ∧
      range P = closure (connectedComponentIn ({p, q}ᶜ : Set K) r) := by
  let A := connectedComponentIn ({p, q}ᶜ : Set K) r
  let E := closure A
  have hcl : E = A ∪ {p, q} := hK.closure_connectedComponentIn_pair hr
  have hconn : IsConnected E := (isConnected_connectedComponentIn_iff.mpr hr).closure
  let lo : E := ⟨p, by rw [hcl]; exact Or.inr (Or.inl rfl)⟩
  let hi : E := ⟨q, by rw [hcl]; exact Or.inr (Or.inr rfl)⟩
  let : T1Space K := hK.t1Space_univ
  let : ConnectedSpace E := Subtype.connectedSpace hconn
  have hsep : ∀ z : E, z ≠ lo → z ≠ hi → CutPoint.Separates univ {z} lo hi := by
    intro z hzp hzq
    have hz : z.val ∈ A := by
      have hz := z.property
      simp only [hcl] at hz
      exact hz.resolve_right (by
        rintro (h | h)
        · exact hzp (Subtype.ext h)
        · exact hzq (Subtype.ext h))
    exact separates_subtype (hK.separates_endpoints_in_closure_component hpq hz)
  obtain ⟨P, hP, hPrange⟩ := CutPoint.exists_path_range_univ lo hi
    (fun h ↦ hpq (congrArg Subtype.val h)) hsep
  refine ⟨P.map continuous_subtype_val, Subtype.val_injective.comp hP, ?_⟩
  change range (Subtype.val ∘ P) = E
  rw [range_comp, hPrange, image_univ, Subtype.range_coe]

/-- Every compact separable circuit has a simple-loop parametrization at every carrier point. -/
theorem IsCircuit.exists_isSimpleLoop {X : Type*} [TopologicalSpace X] {S : Set X} {x : X}
    (hS : IsCircuit S) (hcompact : IsCompact S) [SeparableSpace S] (hx : x ∈ S) :
    ∃ P : Path x x, P.IsSimpleLoop ∧ range P = S := by
  let K := S
  let : CompactSpace K := isCompact_iff_compactSpace.mp hcompact
  let hK : IsCircuit (univ : Set K) := isCircuit_iff_subtype.mp hS
  let p : K := ⟨x, hx⟩
  obtain ⟨q, hq, hqp⟩ := (hK.puncture_isConnected (mem_univ p)).nonempty
  have hpq : p ≠ q := by simpa [mem_singleton_iff, ne_comm] using hqp
  have hnot := hK.pair_puncture_not_isPreconnected (mem_univ p) (mem_univ q) hpq
  have hnonempty : (univ \ {p, q} : Set K).Nonempty := by
    by_contra he
    exact hnot ((Set.not_nonempty_iff_eq_empty.mp he).symm ▸ isPreconnected_empty)
  obtain ⟨r, hr⟩ := hnonempty
  obtain ⟨s, hs, hne⟩ := exists_connectedComponentIn_ne hnot r
  simp only [← compl_eq_univ_sdiff] at hr hs hne
  let (t : K) : CompactSpace ↥(closure (connectedComponentIn ({p, q}ᶜ : Set K) t)) :=
    isCompact_iff_compactSpace.mp isClosed_closure.isCompact
  let (t : K) : SeparableSpace ↥(closure (connectedComponentIn ({p, q}ᶜ : Set K) t)) := by
    let A := connectedComponentIn ({p, q}ᶜ : Set K) t
    let : SeparableSpace A :=
      hK.isOpen_connectedComponentIn_pair.isOpenEmbedding_subtypeVal.separableSpace
    exact ((denseRange_inclusion_iff (show A ⊆ closure A from subset_closure)).mpr
      Subset.rfl).separableSpace (continuous_inclusion subset_closure)
  obtain ⟨P, hP, hPrange⟩ := hK.exists_path_range_closure_component hpq hr
  obtain ⟨Q, hQ, hQrange⟩ := hK.exists_path_range_closure_component hpq hs
  obtain ⟨hcover, hinter⟩ := hK.closure_components_union_inter hr hs hne
  have hloop : (P.trans Q.symm).IsSimpleLoop := by
    rw [Path.IsSimpleLoop, Path.trans_injOn_ico_iff]
    refine ⟨hP, hQ.comp unitInterval.symm_involutive.injective, disjoint_left.mpr fun z hz hz' ↦ ?_⟩
    have hzpair : z ∈ ({p, q} : Set K) := by
      rw [← hinter, ← hPrange, ← hQrange]
      exact ⟨hz.1, Q.symm_range ▸ hz'.1⟩
    exact hzpair.elim (fun h ↦ hz'.2 h) (fun h ↦ hz.2 h)
  let R := (P.trans Q.symm).map continuous_subtype_val
  refine ⟨R, Subtype.val_injective.injOn.comp hloop (mapsTo_univ _ _), ?_⟩
  change range (Subtype.val ∘ (P.trans Q.symm)) = S
  rw [range_comp, Path.trans_range, Path.symm_range, hPrange, hQrange, hcover]
  simp [K]

/-- A compact separable circuit splits at two distinct points into arcs meeting exactly there. -/
theorem IsCircuit.exists_two_arcs {X : Type*} [TopologicalSpace X] {C : Set X} {a b : X}
    (hC : IsCircuit C) (hcompact : IsCompact C) [SeparableSpace C]
    (ha : a ∈ C) (hb : b ∈ C) (hab : a ≠ b) :
    ∃ P Q : Set X, IsPrimitiveLink P a b ∧ IsPrimitiveLink Q a b ∧
      P ∪ Q = C ∧ P ∩ Q = {a, b} := by
  obtain ⟨γ, hγ, hrange⟩ := hC.exists_isSimpleLoop hcompact ha
  obtain ⟨t, ht⟩ := hrange.symm ▸ hb
  have ht0 : t ≠ 0 := by
    intro h
    exact hab (by simpa [h] using ht)
  have ht1 : t ≠ 1 := by
    intro h
    exact hab (by simpa [h] using ht)
  refine ⟨range (γ.subpath 0 t), range (γ.subpath t 1), ?_, ?_, ?_, ?_⟩
  · exact ⟨(γ.subpath 0 t).cast γ.source.symm ht.symm,
      hγ.isPrimitive.subpath ht0.symm, rfl⟩
  · exact ⟨((γ.subpath t 1).cast ht.symm γ.target.symm).symm,
      (hγ.isPrimitive.subpath ht1).symm, (γ.subpath t 1).symm_range⟩
  · rw [γ.range_subpath_of_le _ _ t.prop.1, γ.range_subpath_of_le _ _ t.prop.2,
      ← image_union, Icc_union_Icc_eq_Icc (show (0 : unitInterval) ≤ t from t.prop.1)
        (show t ≤ (1 : unitInterval) from t.prop.2),
      unitInterval.Icc_eq_univ, image_univ, hrange]
  · simpa [ht, pair_comm] using hγ.isPrimitive.subpath_range_inter_subpath_range t

/-- A compact separable intrinsic circuit is exactly a carrier homeomorphic to the circle. -/
theorem isCircuit_iff_nonempty_homeomorph_circle {X : Type*} [TopologicalSpace X] {S : Set X}
    [CompactSpace S] [SeparableSpace S] : IsCircuit S ↔ Nonempty (S ≃ₜ Circle) := by
  constructor
  · intro hS
    let : T2Space S := hS.t2Space
    have hK : IsCircuit (univ : Set S) := isCircuit_iff_subtype.mp hS
    obtain ⟨x, hx⟩ := hK.nonempty
    obtain ⟨P, hP, hPrange⟩ := hK.exists_isSimpleLoop isCompact_univ hx
    have he : IsEmbedding P.onCircle :=
      P.onCircle.continuous.isClosedEmbedding (P.onCircle_injective hP) |>.isEmbedding
    have hsurj : Surjective P.onCircle := by
      rw [← range_eq_univ, P.range_onCircle, hPrange]
    exact ⟨(he.toHomeomorphOfSurjective hsurj).symm⟩
  · rintro ⟨e⟩
    apply isCircuit_iff_subtype.mpr
    simpa only [e.symm.surjective.range_eq, image_univ] using
      e.symm.isEmbedding.isCircuit_image.mpr circle_isCircuit
