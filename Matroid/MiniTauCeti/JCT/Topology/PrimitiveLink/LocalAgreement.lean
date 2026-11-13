module

public import Matroid.MiniTauCeti.JCT.Topology.PrimitiveLink

@[expose] public section

open Set Topology Filter Function unitInterval

variable {X : Type*} [TopologicalSpace X] {L M : Set X} {x y a b p : X}

/-- Primitive links which agree by inclusion near a common interior point agree there as sets.
Only the carrier of the second link needs to be Hausdorff. -/
theorem IsPrimitiveLink.local_agreement [T2Space M] (hL : IsPrimitiveLink L x y)
    (hM : IsPrimitiveLink M a b) (hpL : p ∈ L \ {x, y})
    (hpM : p ∈ M \ {a, b}) (hLM : L ≤ᶠ[𝓝 p] M) : L =ᶠ[𝓝 p] M := by
  obtain ⟨P, hP, rfl⟩ := hL
  obtain ⟨Q, hQ, rfl⟩ := hM
  have hpP : p ∈ P.Interior := hP.range_diff_endpoints ▸ hpL
  obtain ⟨t, ht, rfl⟩ := hpP
  have hpQ : P t ∈ Q.Interior := hQ.range_diff_endpoints ▸ hpM
  obtain ⟨q, hq, hqt⟩ := hpQ
  let D := Ioo (0 : I) 1
  let chart : D → range Q := fun s ↦ ⟨Q s, mem_range_self (s : I)⟩
  have hc : Topology.IsOpenEmbedding chart := hQ.isOpenEmbedding_interior
  let e : D ≃ₜ range chart := hc.isEmbedding.toHomeomorph
  let pQ : range Q := ⟨P t, hpM.1⟩
  have hpchart : pQ ∈ range chart := ⟨⟨q, hq⟩, Subtype.ext hqt⟩
  obtain ⟨V, hV, hVsub⟩ := (mem_nhds_subtype _ pQ (range chart)).mp
    (hc.isOpen_range.mem_nhds hpchart)
  have hloc : ∀ᶠ s in 𝓝 t, s ∈ D ∧ ∃ z : D, Q z = P s := by
    filter_upwards [isOpen_Ioo.mem_nhds ht,
      P.continuous.continuousAt.eventually hV,
      P.continuous.continuousAt.eventually hLM] with s hs hsV hsM
    have hPs : P s ∈ range Q := hsM (mem_range_self s)
    obtain ⟨z, hz⟩ := hVsub (show (⟨P s, hPs⟩ : range Q) ∈ Subtype.val ⁻¹' V from hsV)
    exact ⟨hs, z, congrArg Subtype.val hz⟩
  obtain ⟨⟨l, r⟩, ⟨hlt, htr⟩, hlocsub⟩ :=
    (nhds_basis_Ioo' (⟨0, ht.1⟩ : ∃ z : I, z < t) ⟨1, ht.2⟩).mem_iff.mp hloc
  have hsub (s : Ioo l r) : (s : I) ∈ D ∧ ∃ z : D, Q z = P s :=
    hlocsub s.property
  let g : Ioo l r → range chart := fun s ↦
    ⟨⟨P s, by obtain ⟨z, hz⟩ := (hsub s).2; exact ⟨z, hz⟩⟩,
      by obtain ⟨z, hz⟩ := (hsub s).2; exact ⟨z, Subtype.ext hz⟩⟩
  let f : Ioo l r → D := fun s ↦ e.symm (g s)
  have hg : Continuous g :=
    ((P.continuous.comp continuous_subtype_val).subtype_mk _).subtype_mk _
  have hf : Continuous f := e.symm.continuous.comp hg
  have hinj : Injective f := by
    intro s z hsz
    have h : g s = g z := e.symm.injective hsz
    exact Subtype.ext (hP.injOn_Ioo (hsub s).1 (hsub z).1
      (congrArg (fun w : range chart ↦ w.val.val) h))
  let : Inhabited (Ioo l r) := ⟨⟨t, hlt, htr⟩⟩
  have : PreconnectedSpace (Ioo l r) := Subtype.preconnectedSpace isPreconnected_Ioo
  have hconn := (isPreconnected_range hf).ordConnected
  have hopen : Topology.IsOpenEmbedding f := by
    obtain hmono | hanti := hf.strictMono_of_inj hinj
    · exact hmono.isOpenEmbedding_of_ordConnected hconn
    · exact hanti.dual_right.isOpenEmbedding_of_ordConnected hconn.dual
  have hcf (s : Ioo l r) : (chart (f s)).val = P s :=
    congrArg (fun w : range chart ↦ w.val.val) (e.apply_symm_apply (g s))
  let c : Ioo l r := ⟨t, hlt, htr⟩
  have hfc : chart (f c) = pQ := Subtype.ext (hcf c)
  have hnhds : (Subtype.val ⁻¹' range P : Set (range Q)) ∈ 𝓝 pQ := by
    rw [← hfc]
    apply mem_of_superset (hc.image_mem_nhds.mpr
      (hopen.isOpenMap.range_mem_nhds c))
    rintro z ⟨d, ⟨s, rfl⟩, rfl⟩
    exact ⟨s, (hcf s).symm⟩
  obtain ⟨U, hU, hUsub⟩ := (mem_nhds_subtype _ pQ _).mp hnhds
  filter_upwards [hLM, hU] with z hz hzU
  exact propext ⟨hz, fun hzQ ↦ hUsub (show (⟨z, hzQ⟩ : range Q) ∈
    Subtype.val ⁻¹' U from hzU)⟩
