module

public import Matroid.MiniTauCeti.JCT.Topology.Circuit.Separation
public import Matroid.MiniTauCeti.JCT.Topology.OrderedCompactification

/-! # Compactness of intrinsic circuits with totally disconnected remainders -/

@[expose] public section

open Set Topology Function

namespace IsCircuit

variable {X : Type*} [TopologicalSpace X] [T2Space X]
  {K V : Set X}

private lemma isCompact_completed_component (hK : IsCircuit K)
    (hcompact : IsCompact (closure K))
    (hV : IsClosed V) (hdisc : IsTotallyDisconnected V) (hrem : closure K \ K ⊆ V)
    {p q r : K} (hpq : p ≠ q) (hr : r ∉ ({p, q} : Set K)) :
    IsCompact (Subtype.val '' closure (connectedComponentIn ({p, q}ᶜ : Set K) r) : Set X) := by
  let hK' : IsCircuit (univ : Set K) := isCircuit_iff_subtype.mp hK
  let A := connectedComponentIn ({p, q}ᶜ : Set K) r
  let E := closure A
  have hcl : E = A ∪ {p, q} := hK'.closure_connectedComponentIn_pair hr
  have hconn : IsConnected E := (isConnected_connectedComponentIn_iff.mpr hr).closure
  let lo : E := ⟨p, by rw [hcl]; exact Or.inr (Or.inl rfl)⟩
  let hi : E := ⟨q, by rw [hcl]; exact Or.inr (Or.inr rfl)⟩
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
    have hs0 : CutPoint.Separates E {z.val} lo.val hi.val :=
      hK'.separates_endpoints_in_closure_component hpq hz
    have hs := hs0.preimage (f := (Subtype.val : E → K)) (a := lo) (b := hi)
      continuous_subtypeVal.continuousOn
    have hE : (Subtype.val : E → K) ⁻¹' E = univ := by ext z; simp
    have hw : (Subtype.val : E → K) ⁻¹' {z.val} = {z} := by
      ext w
      simp only [mem_preimage, mem_singleton_iff, Subtype.val_inj]
    simpa only [hE, hw] using hs
  let : LinearOrder E := CutPoint.separatorLinearOrder lo hi hsep
  obtain ⟨hlo, hhi⟩ := CutPoint.separatorLinearOrder_endpoints lo hi hsep
  let : BoundedOrder E := { bot := lo, bot_le := hlo, top := hi, le_top := hhi }
  let e : E → X := fun z ↦ z.val.val
  have he : IsEmbedding e := IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal
  have hrange : range e = Subtype.val '' E := by
    change range ((Subtype.val : K → X) ∘ (Subtype.val : E → K)) = _
    rw [range_comp, Subtype.range_coe]
  rw [← hrange]
  apply he.isCompact_range_of_connected_order
    (hcompact.of_isClosed_subset isClosed_closure
      (closure_mono (hrange ▸ Subtype.coe_image_subset K E)))
    (CutPoint.separatorLinearOrder_isOpen_rays lo hi hsep) hV hdisc
  rintro x ⟨hxcl, hxnot⟩
  apply hrem
  refine ⟨closure_mono (hrange ▸ Subtype.coe_image_subset K E) hxcl, ?_⟩
  intro hxK
  have hxE : (⟨x, hxK⟩ : K) ∈ closure E := by
    rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
    exact hrange ▸ hxcl
  rw [(show IsClosed E from isClosed_closure).closure_eq] at hxE
  exact hxnot (hrange.symm ▸ ⟨⟨x, hxK⟩, hxE, rfl⟩)

/-- An intrinsic circuit with compact closure in a Hausdorff space is compact if its
missing closure points lie in a closed totally disconnected set. -/
theorem isCompact_of_closure_diff_subset (hK : IsCircuit K) (hcompact : IsCompact (closure K))
    (hV : IsClosed V)
    (hdisc : IsTotallyDisconnected V) (hrem : closure K \ K ⊆ V) : IsCompact K := by
  have hK' : IsCircuit (univ : Set K) := isCircuit_iff_subtype.mp hK
  obtain ⟨p, _, q, _, hpq⟩ := hK'.nontrivial
  have hnot := hK'.pair_puncture_not_isPreconnected (mem_univ p) (mem_univ q) hpq
  have hnonempty : (univ \ {p, q} : Set K).Nonempty := by
    by_contra he
    exact hnot ((Set.not_nonempty_iff_eq_empty.mp he).symm ▸ isPreconnected_empty)
  obtain ⟨r, hr⟩ := hnonempty
  obtain ⟨s, hs, hne⟩ := exists_connectedComponentIn_ne hnot r
  simp only [← compl_eq_univ_sdiff] at hr hs hne
  have hcover := (hK'.closure_components_union_inter hr hs hne).1
  have hc := (hK.isCompact_completed_component hcompact hV hdisc hrem hpq hr).union
    (hK.isCompact_completed_component hcompact hV hdisc hrem hpq hs)
  simpa only [← image_union, hcover, image_univ, Subtype.range_coe] using hc

end IsCircuit
