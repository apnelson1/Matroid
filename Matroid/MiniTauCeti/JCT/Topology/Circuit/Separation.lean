module

public import Matroid.MiniTauCeti.JCT.Topology.Circuit.Topology
public import Matroid.MiniTauCeti.JCT.Topology.CutPoint

/-!
# Intrinsic separation

Two distinct points separate two further points when the latter lie in different connected
components of their two-point deletion. This relation is defined for arbitrary sets, and its
transport under homeomorphisms of carriers does not require the circuit conditions.
-/

@[expose] public section

open Set Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {S : Set X}

/-- Unoriented separation, defined without choosing a circular order. -/
def IsCircuit.Separates (S : Set X) (a b c d : X) : Prop :=
  a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ c ∈ S \ {a, b} ∧ d ∈ S \ {a, b} ∧
    connectedComponentIn (S \ {a, b}) c ≠ connectedComponentIn (S \ {a, b}) d

/-- On a circuit, strict clopen separation forces a valid distinct deleted pair. -/
theorem IsCircuit.separates_iff_cutPoint_separates (hS : IsCircuit S) (a b c d : X) :
    IsCircuit.Separates S a b c d ↔ CutPoint.Separates S {a, b} c d := by
  let : Finite (ConnectedComponents ↥(S \ {a, b})) :=
    hS.finite_connectedComponents_sdiff_pair a b
  constructor
  · rintro ⟨_, _, _, hc, hd, hne⟩
    exact CutPoint.separates_iff_connectedComponentIn_ne.mpr ⟨hc, hd, hne⟩
  · intro h
    have hvalid : a ∈ S ∧ b ∈ S ∧ a ≠ b := by
      by_contra hn
      exact h.not_subset (hS.isConnected_sdiff_pair_iff.mpr hn).isPreconnected
        h.1 h.2.1 Subset.rfl
    exact ⟨hvalid.1, hvalid.2.1, hvalid.2.2,
      CutPoint.separates_iff_connectedComponentIn_ne.mp h⟩

/-- Exchanging the two deleted points preserves separation. -/
theorem IsCircuit.separates_swap_left (a b c d : X) :
    IsCircuit.Separates S a b c d ↔ IsCircuit.Separates S b a c d := by
  simp only [Separates, pair_comm b a]
  tauto

/-- Exchanging the two separated points preserves separation. -/
theorem IsCircuit.separates_swap_right (a b c d : X) :
    IsCircuit.Separates S a b c d ↔ IsCircuit.Separates S a b d c := by
  simp only [Separates]
  tauto

/-- An embedding preserves and reflects separation, without any circuit hypothesis. -/
theorem Topology.IsEmbedding.separates_image {f : X → Y} (hf : IsEmbedding f)
    (a b c d : X) :
    IsCircuit.Separates (f '' S) (f a) (f b) (f c) (f d) ↔
      IsCircuit.Separates S a b c d := by
  rw [IsCircuit.Separates, IsCircuit.Separates, ← image_pair,
    ← image_sdiff hf.injective]
  simp only [hf.injective.mem_set_image, ne_eq, hf.injective.eq_iff,
    ← hf.image_connectedComponentIn, (image_injective.mpr hf.injective).eq_iff]

/-- Separation on a carrier is separation on its universe subtype. -/
theorem IsCircuit.separates_iff_subtype (a b c d : ↥S) :
    IsCircuit.Separates S a b c d ↔ IsCircuit.Separates univ a b c d := by
  simpa using IsEmbedding.subtypeVal.separates_image (S := (univ : Set ↥S)) a b c d

/-- Only the topology of the carrier is needed for transport of carrier points. -/
theorem IsCircuit.separates_image_iff {f : X → Y}
    (hf : IsEmbedding (fun x : ↥S ↦ f x)) (a b c d : ↥S) :
    IsCircuit.Separates (f '' S) (f a) (f b) (f c) (f d) ↔
      IsCircuit.Separates S a b c d := by
  rw [IsCircuit.separates_iff_subtype]
  simpa only [image_univ, ← image_eq_range] using hf.separates_image (S := univ) a b c d

/-- Separation depends only on the topology of the carrier. -/
theorem separates_iff_of_homeomorph {T : Set Y} (e : ↥S ≃ₜ ↥T) (a b c d : ↥S) :
    IsCircuit.Separates S a b c d ↔ IsCircuit.Separates T (e a) (e b) (e c) (e d) := by
  rw [IsCircuit.separates_iff_subtype, IsCircuit.separates_iff_subtype]
  simpa using (e.isEmbedding.separates_image (S := univ) a b c d).symm

private theorem IsCircuit.separates_exchange (hS : IsCircuit S) {a b c d : X}
    (hsep : IsCircuit.Separates S a b c d) : IsCircuit.Separates S c d a b := by
  obtain ⟨ha, hb, hab, hc, hd, hne⟩ := hsep
  have hcd : c ≠ d := fun h ↦ hne (h ▸ rfl)
  have ha' : a ∈ S \ {c, d} := ⟨ha, by
    rintro (h | h)
    · exact hc.2 (Or.inl h.symm)
    · exact hd.2 (Or.inl h.symm)⟩
  have hb' : b ∈ S \ {c, d} := ⟨hb, by
    rintro (h | h)
    · exact hc.2 (Or.inr h.symm)
    · exact hd.2 (Or.inr h.symm)⟩
  refine ⟨hc.1, hd.1, hcd, ha', hb', ?_⟩
  intro heq
  obtain ⟨u, hu, hother⟩ := exists_connectedComponentIn_ne
    (hS.pair_puncture_not_isPreconnected hc.1 hd.1 hcd) a
  let F := connectedComponentIn (S \ {c, d}) u
  have haF : a ∉ F := fun h ↦ hother (connectedComponentIn_eq h).symm
  have hbF : b ∉ F := fun h ↦ hother (heq.trans (connectedComponentIn_eq h).symm)
  have hsub : F ∪ {c, d} ⊆ S \ {a, b} := by
    rintro z (hz | (rfl | rfl))
    · refine ⟨(connectedComponentIn_subset _ _ hz).1, ?_⟩
      rintro (rfl | rfl)
      · exact haF hz
      · exact hbF hz
    · exact hc
    · exact hd
  have hconn := hS.isConnected_union_pair_connectedComponentIn hc.1 hd.1 hu
  have hmax := hconn.isPreconnected.subset_connectedComponentIn
    (show c ∈ F ∪ {c, d} from Or.inr (Or.inl rfl)) hsub
  exact hne (connectedComponentIn_eq (hmax (Or.inr (Or.inr rfl))))

/-- The two pairs in a separation relation can be exchanged. -/
theorem IsCircuit.separates_comm (hS : IsCircuit S) (a b c d : X) :
    IsCircuit.Separates S a b c d ↔ IsCircuit.Separates S c d a b :=
  ⟨hS.separates_exchange, hS.separates_exchange⟩

/-- Every pair of distinct circuit points is separated by another pair. -/
theorem IsCircuit.exists_separating_pair (hS : IsCircuit S)
    {a b : X} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    ∃ c d, IsCircuit.Separates S c d a b := by
  rcases eq_empty_or_nonempty (S \ {a, b}) with h | ⟨c, hc⟩
  · exact (hS.pair_puncture_not_isPreconnected ha hb hab
      (h.symm ▸ isPreconnected_empty)).elim
  obtain ⟨d, hd, hne⟩ := exists_connectedComponentIn_ne
    (hS.pair_puncture_not_isPreconnected ha hb hab) c
  exact ⟨c, d, hS.separates_exchange ⟨ha, hb, hab, hc, hd, hne⟩⟩

/-- The carrier of an intrinsic circuit is Hausdorff, without an ambient separation assumption. -/
theorem IsCircuit.t2Space (hS : IsCircuit S) : T2Space ↥S := by
  have hK := isCircuit_iff_subtype.mp hS
  refine ⟨fun x y hxy ↦ ?_⟩
  obtain ⟨p, q, _, _, _, hx, hy, hne⟩ :=
    hK.exists_separating_pair (mem_univ x) (mem_univ y) hxy
  simp only [← compl_eq_univ_sdiff] at hx hy hne
  refine ⟨connectedComponentIn ({p, q}ᶜ : Set ↥S) x,
    connectedComponentIn ({p, q}ᶜ : Set ↥S) y,
    hK.isOpen_connectedComponentIn_pair, hK.isOpen_connectedComponentIn_pair,
    mem_connectedComponentIn hx, mem_connectedComponentIn hy, ?_⟩
  exact disjoint_connectedComponentIn_of_ne hne



section CompletedComponents
variable {K : Type*} [TopologicalSpace K]

theorem IsCircuit.separates_endpoints_in_closure_component
    (hK : IsCircuit (univ : Set K)) {p q r w : K}
    (hpq : p ≠ q)
    (hw : w ∈ connectedComponentIn ({p, q}ᶜ : Set K) r) :
    CutPoint.Separates (closure (connectedComponentIn ({p, q}ᶜ : Set K) r)) {w} p q := by
  have hr := connectedComponentIn_nonempty_iff.mp ⟨w, hw⟩
  obtain ⟨s, hs, hne⟩ := exists_connectedComponentIn_ne
    (hK.pair_puncture_not_isPreconnected (mem_univ p) (mem_univ q) hpq) r
  simp only [← compl_eq_univ_sdiff] at hs hne
  have hw' := connectedComponentIn_subset ({p, q}ᶜ : Set K) r hw
  have hsC : s ∉ connectedComponentIn ({p, q}ᶜ : Set K) r :=
    fun h ↦ hne (connectedComponentIn_eq h)
  have hsep : IsCircuit.Separates univ p q w s := by
    refine ⟨mem_univ p, mem_univ q, hpq, ⟨trivial, hw'⟩, ⟨trivial, hs⟩, ?_⟩
    simpa only [← compl_eq_univ_sdiff] using
      (show connectedComponentIn ({p, q}ᶜ : Set K) w ≠
        connectedComponentIn ({p, q}ᶜ : Set K) s from
          fun h ↦ hne ((connectedComponentIn_eq hw).trans h))
  obtain ⟨_, _, hws, hp, hq, hpqC⟩ := (hK.separates_comm p q w s).mp hsep
  simp only [← compl_eq_univ_sdiff] at hp hq hpqC
  have hwp : w ≠ p := fun h ↦ hw' (Or.inl h)
  have hwq : w ≠ q := fun h ↦ hw' (Or.inr h)
  have hpcl : p ∈ closure (connectedComponentIn ({p, q}ᶜ : Set K) r) := by
    rw [hK.closure_connectedComponentIn_pair hr]
    exact Or.inr (Or.inl rfl)
  have hqcl : q ∈ closure (connectedComponentIn ({p, q}ᶜ : Set K) r) := by
    rw [hK.closure_connectedComponentIn_pair hr]
    exact Or.inr (Or.inr rfl)
  refine ⟨⟨hpcl, Ne.symm hwp⟩, ⟨hqcl, Ne.symm hwq⟩,
    connectedComponentIn ({w, s}ᶜ : Set K) p, ⟨?_, ?_⟩,
    mem_connectedComponentIn hp, fun h ↦ hpqC (connectedComponentIn_eq h)⟩
  · have heq :
        (Subtype.val : ↥(closure (connectedComponentIn ({p, q}ᶜ : Set K) r) \ {w}) → K) ⁻¹'
          closure (connectedComponentIn ({w, s}ᶜ : Set K) p) =
        Subtype.val ⁻¹' connectedComponentIn ({w, s}ᶜ : Set K) p := by
      ext z
      rw [mem_preimage, hK.closure_connectedComponentIn_pair hp]
      change (z.val ∈ connectedComponentIn ({w, s}ᶜ : Set K) p ∨ z.val ∈ {w, s}) ↔ _
      have hz := z.property
      simp only [hK.closure_connectedComponentIn_pair hr] at hz
      constructor
      · rintro (h | (h | h))
        · exact h
        · exact (hz.2 h).elim
        · exact ((h ▸ hz.1).elim hsC hs).elim
      · exact Or.inl
    rw [← heq]
    exact isClosed_closure.preimage continuous_subtype_val
  · exact hK.isOpen_connectedComponentIn_pair.preimage continuous_subtype_val


end CompletedComponents
