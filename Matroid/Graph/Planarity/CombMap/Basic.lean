import Matroid.Graph.Planarity.CombMap.Equiv
import Matroid.Graph.Walk.Dart
import Matroid.Graph.Simple

open Set PFun Part Equiv Function Equiv.Perm

variable {V E D : Type*} {G H : Graph V E} {e : E} {v : V} {X : Set V} {F C : Set E}

namespace Graph

structure CombinatorialMap (G : Graph V E) (D : Type*) extends DartStructure G D where
  σ : Equiv.Perm D
  sigma_id ⦃d⦄ : d ∉ fₑ.Dom → σ d = d
  transtive_preimage : ∀ v, σ.IsCycleOn (fᵥ.preimage {v})

namespace CombinatorialMap

section CyclePerm

variable {S : Set D} {d : D}

noncomputable def cyclePerm (S : Set D) (hS : S.Countable) : Equiv.Perm D :=
  (hS.exists_cycleOn).choose

lemma cyclePerm_isCycleOn (hS : S.Countable) : (cyclePerm S hS).IsCycleOn S :=
  (hS.exists_cycleOn).choose_spec.1

lemma cyclePerm_fixed_of_notMem (hS : S.Countable) (hd : d ∉ S) : cyclePerm S hS d = d := by
  by_contra hne
  have hmem : d ∈ {x | cyclePerm S hS x ≠ x} := by simpa [Set.mem_setOf_eq, ne_eq] using hne
  exact hd ((hS.exists_cycleOn).choose_spec.2 hmem)

end CyclePerm

lemma sigma_finiteOrbit [G.LocallyFinite] (M : CombinatorialMap G D) :
    M.σ.finiteOrbit := by
  rw [Equiv.finiteOrbit_iff]
  rintro d
  simp only [IsPeriodicPt, IsFixedPt, Perm.iterate_eq_pow]
  obtain hd | hd := em' (d ∈ M.fₑ.Dom)
  · exact ⟨1, one_pos, M.sigma_id hd⟩
  rw [← M.dom_fᵥ] at hd
  have hs := M.fᵥ_preimage_finite ((M.fᵥ d).get hd)
  let s := hs.toFinset
  have hs_coe : (s : Set D) = M.fᵥ.preimage {(M.fᵥ d).get hd} := hs.coe_toFinset
  have hcycle : M.σ.IsCycleOn s := by simpa [hs_coe] using M.transtive_preimage _
  have hd_s : d ∈ s := by
    rw [← Finset.mem_coe, hs_coe]
    exact PFun.mem_preimage_self hd
  exact ⟨s.card, Finset.card_pos.mpr ⟨d, hd_s⟩, hcycle.pow_card_apply hd_s⟩

lemma alpha_finiteOrbit (M : CombinatorialMap G D) : M.α.finiteOrbit := by
  rw [Equiv.finiteOrbit_iff]
  intro d
  refine ⟨2, by norm_num, ?_⟩
  simp only [IsPeriodicPt, IsFixedPt, Perm.iterate_eq_pow]
  rw [sq, Perm.mul_apply]
  exact M.otherDart_invol d

lemma finite_preimage_fₑ_of_finite (M : CombinatorialMap G D) (hF : F.Finite) :
    (M.fₑ.preimage F).Finite := by
  rw [show M.fₑ.preimage F = ⋃ e ∈ F, M.fₑ.preimage {e} by
    ext d
    simp only [PFun.Preimage_def, mem_iUnion, exists_prop, mem_singleton_iff, exists_eq_left]
    rfl]
  refine hF.biUnion fun e heF ↦ ?_
  by_cases heG : e ∈ E(G)
  · exact finite_of_encard_eq_coe (k := 2) (M.preimage_encard heG)
  rw [show M.fₑ.preimage {e} = ∅ by
    ext d
    simp only [PFun.Preimage_def, mem_singleton_iff, exists_eq_left, mem_empty_iff_false,
      iff_false]
    intro hed
    exact heG (by rw [← M.ran_fₑ]; exact ⟨d, hed⟩)]
  exact finite_empty

noncomputable def copy (M : CombinatorialMap G D) (h : G = H) : CombinatorialMap H D where
  toDartStructure := M.toDartStructure.copy h
  σ := M.σ
  sigma_id _ hd := M.sigma_id hd
  transtive_preimage v := M.transtive_preimage v

noncomputable def restrict [G.LocallyFinite] (M : CombinatorialMap G D)
    (F : Set E) : CombinatorialMap (G ↾ F) D where
  toDartStructure := M.toDartStructure.restrict F
  σ := by
    classical
    exact M.σ.keep (M.fₑ.preimage F) M.sigma_finiteOrbit
  sigma_id d hd := by
    classical
    by_cases hkeep : d ∈ M.fₑ.preimage F
    · exact (hd <| by simpa [DartStructure.fₑ_restrict, PFun.dom_codRestrict] using
        ⟨PFun.mem_dom M.fₑ d |>.mp (M.fₑ.preimage_subset_dom F hkeep), hkeep⟩).elim
    exact Equiv.keep_apply_of_not_mem M.sigma_finiteOrbit hkeep
  transtive_preimage v := by
    classical
    rw [DartStructure.fᵥ_restrict, PFun.preimage_restrict]
    exact (M.transtive_preimage v).keep M.sigma_finiteOrbit (M.fₑ.preimage F)

noncomputable def induce [G.LocallyFinite] (M : CombinatorialMap G D)
    (X : Set V) : CombinatorialMap G[X] D where
  toDartStructure := M.toDartStructure.induce X
  σ := by
    classical
    exact M.σ.keep (M.fₑ.preimage E(G[X])) M.sigma_finiteOrbit
  sigma_id d hd := by
    classical
    by_cases hkeep : d ∈ M.fₑ.preimage E(G[X])
    · exact (hd <| by simpa [DartStructure.fₑ_induce, PFun.dom_codRestrict] using
        ⟨PFun.mem_dom M.fₑ d |>.mp (M.fₑ.preimage_subset_dom E(G[X]) hkeep), hkeep⟩).elim
    exact Equiv.keep_apply_of_not_mem M.sigma_finiteOrbit hkeep
  transtive_preimage v := by
    classical
    rw [M.preimage_fᵥ_induce]
    exact (M.transtive_preimage v).keep M.sigma_finiteOrbit (M.fₑ.preimage E(G[X]))

noncomputable def deleteVerts [G.LocallyFinite] (M : CombinatorialMap G D)
    (X : Set V) : CombinatorialMap (G - X) D :=
  (M.induce (V(G) \ X)).copy (G.deleteVerts_def X)

noncomputable def of_le [G.LocallyFinite] (h : H ≤ G) (M : CombinatorialMap G D) :
    CombinatorialMap H D where
  toDartStructure := M.toDartStructure.of_le h
  σ := by
    classical
    exact M.σ.keep (M.fₑ.preimage E(H)) M.sigma_finiteOrbit
  sigma_id d hd := by
    classical
    by_cases hkeep : d ∈ M.fₑ.preimage E(H)
    · exact (hd <| by simpa [DartStructure.fₑ_of_le, PFun.dom_codRestrict] using
        ⟨PFun.mem_dom M.fₑ d |>.mp (M.fₑ.preimage_subset_dom E(H) hkeep), hkeep⟩).elim
    exact Equiv.keep_apply_of_not_mem M.sigma_finiteOrbit hkeep
  transtive_preimage v := by
    classical
    rw [DartStructure.fᵥ_of_le, PFun.preimage_restrict]
    exact (M.transtive_preimage v).keep M.sigma_finiteOrbit (M.fₑ.preimage E(H))

noncomputable def deleteEdges [G.LocallyFinite] (M : CombinatorialMap G D) (F : Set E) :
    CombinatorialMap (G ＼ F) D where
  toDartStructure := M.toDartStructure.deleteEdges F
  σ := by
    classical
    exact M.σ.skip (M.fₑ.preimage F) M.sigma_finiteOrbit
  sigma_id d hd := by
    classical
    by_cases hdel : d ∈ M.fₑ.preimage F
    · simpa using Equiv.skip_apply_of_mem M.sigma_finiteOrbit hdel
    have hdom : d ∉ M.fₑ.Dom := by
      rw [DartStructure.dom_fₑ_deleteEdges] at hd
      exact by_contra fun hdom ↦ hd ⟨not_not.mp hdom, hdel⟩
    exact skip_apply_of_fixed M.sigma_finiteOrbit (M.sigma_id hdom)
  transtive_preimage v := by
    rw [M.preimage_fᵥ_deleteEdges]
    classical
    exact (M.transtive_preimage v).skip M.sigma_finiteOrbit (M.fₑ.preimage F)

noncomputable def φ (M : CombinatorialMap G D) : Equiv.Perm D := M.σ * M.α

@[simp] lemma φ_apply (M : CombinatorialMap G D) (d : D) : M.φ d = M.σ (M.α d) := rfl

lemma φ_fixed_of_notMem_dom (M : CombinatorialMap G D) {d : D} (hd : d ∉ M.fₑ.Dom) :
    IsFixedPt M.φ d := by
  unfold IsFixedPt
  rw [φ_apply, DartStructure.α_apply, M.otherDart_of_notMem_dom hd, M.sigma_id hd]

def faceCycles (M : CombinatorialMap G D) : Set (Cycle D) :=
  periodicOrbit M.φ '' M.fₑ.Dom



section Contract

variable {V' : Type*} {φ : V → V'}

noncomputable def contractφ (M : CombinatorialMap G D) (C : Set E) (hφ : M.φ.finiteOrbit)
    [DecidablePred (· ∈ M.fₑ.preimage C)] : Equiv.Perm D :=
  M.φ.skip (M.fₑ.preimage C) hφ

noncomputable def contractα (M : CombinatorialMap G D) (C : Set E)
    [DecidablePred (· ∈ M.fₑ.preimage C)] : Equiv.Perm D :=
  M.α.skip (M.fₑ.preimage C) M.alpha_finiteOrbit

noncomputable def contractσ (M : CombinatorialMap G D) (C : Set E) (hφ : M.φ.finiteOrbit)
    [DecidablePred (· ∈ M.fₑ.preimage C)] : Equiv.Perm D :=
  M.contractφ C hφ * M.contractα C

-- lemma alpha_mapsTo_contractFiber (M : CombinatorialMap G D) (hφ : G.IsContractClosed φ C) (w : V') :
--     Set.MapsTo M.α (M.fᵥ.preimage (φ ⁻¹' {w}) ∩ M.fₑ.preimage C)
--       (M.fᵥ.preimage (φ ⁻¹' {w}) ∩ M.fₑ.preimage C) := by
--   rintro d ⟨hdv, hdC⟩
--   obtain ⟨e, heC, hed⟩ := hdC
--   obtain ⟨u, huφ, hud⟩ := hdv
--   have hdom : d ∈ M.fₑ.Dom := (PFun.mem_dom M.fₑ d).mpr ⟨e, hed⟩
--   have heα : e ∈ M.fₑ (M.α d) := by
--     rw [DartStructure.α_apply, M.fₑ_otherDart d]
--     exact hed
--   have hdomα : M.α d ∈ M.fₑ.Dom := by
--     exact (PFun.mem_dom M.fₑ (M.α d)).mpr ⟨e, heα⟩
--   have hdomvα : M.α d ∈ M.fᵥ.Dom := by rwa [M.dom_fᵥ]
--   let u' := (M.fᵥ (M.α d)).get hdomvα
--   have hu'd : u' ∈ M.fᵥ (M.α d) := Part.get_mem _
--   have hinc : G.Inc e u := (M.inc_iff_exists_dart e u).mpr ⟨d, hed, hud⟩
--   have hinc' : G.Inc e u' := (M.inc_iff_exists_dart e u').mpr ⟨M.α d, heα, hu'd⟩
--   have huφ' : φ u' = w := by
--     obtain rfl | hu' := hinc'.eq_or_eq_of_isLink hinc.choose_spec
--     · exact huφ
--     rw [hu']
--     exact (hφ heC hinc.choose_spec).symm.trans huφ
--   refine ⟨?_, ?_⟩
--   · exact ⟨u', huφ', hu'd⟩
--   exact ⟨e, heC, heα⟩

-- lemma alpha_keep_mapsTo_contractFiber (M : CombinatorialMap G D) (hφ : G.IsContractClosed φ C)
--     (w : V') [DecidablePred (· ∈ M.fₑ.preimage C)] :
--     Set.MapsTo (M.α.keep (M.fₑ.preimage C) M.alpha_finiteOrbit)
--       (M.fᵥ.preimage (φ ⁻¹' {w})) (M.fᵥ.preimage (φ ⁻¹' {w})) := by
--   intro d hdv
--   by_cases hdC : d ∈ M.fₑ.preimage C
--   · obtain ⟨n, -, hkeep, -, -⟩ := Equiv.keep_apply_mem M.alpha_finiteOrbit hdC
--     have hpow : ∀ k, (M.α ^ k) d ∈ M.fᵥ.preimage (φ ⁻¹' {w}) ∩ M.fₑ.preimage C := by
--       intro k
--       induction k with
--       | zero => simpa using ⟨hdv, hdC⟩
--       | succ k ih =>
--         rw [pow_succ', Perm.mul_apply]
--         exact M.alpha_mapsTo_contractFiber hφ w ih
--     exact hkeep.symm ▸ (hpow n).1
--   simpa [Equiv.keep_apply_of_not_mem M.alpha_finiteOrbit hdC] using hdv

-- lemma sigma_mapsTo_contractFiber (M : CombinatorialMap G D) (w : V') :
--     Set.MapsTo M.σ (M.fᵥ.preimage (φ ⁻¹' {w})) (M.fᵥ.preimage (φ ⁻¹' {w})) := by
--   rintro d ⟨u, huφ, hdu⟩
--   have hpre : M.σ d ∈ M.fᵥ.preimage {u} := (M.transtive_preimage u).1.mapsTo (by
--     exact ⟨u, rfl, hdu⟩)
--   exact ⟨u, huφ, by simpa [PFun.Preimage_def] using hpre⟩

-- noncomputable def contract (M : CombinatorialMap G D) (C : Set E) (φ : V → V')
--     (hφfin : M.φ.finiteOrbit)  : CombinatorialMap (G /[C, φ]) D where
--   toDartStructure := M.toDartStructure.contract C φ
--   σ := by
--     classical
--     exact M.contractσ C hφfin
--   sigma_id d hd := by
--     classical
--     by_cases hdel : d ∈ M.fₑ.preimage C
--     · simp [contractσ, contractφ, contractα, Equiv.skip_apply_of_mem, hdel]
--     have hdom : d ∉ M.fₑ.Dom := by
--       rw [DartStructure.dom_fₑ_contract] at hd
--       exact by_contra fun hdom ↦ hd ⟨not_not.mp hdom, hdel⟩
--     have hα : M.contractα C d = d := by
--       exact Equiv.skip_apply_of_fixed M.alpha_finiteOrbit (by
--         unfold IsFixedPt
--         rw [DartStructure.α_apply, M.otherDart_of_notMem_dom hdom])
--     have hψ : M.contractφ C hφfin d = d :=
--       Equiv.skip_apply_of_fixed hφfin (M.φ_fixed_of_notMem_dom hdom)
--     rw [contractσ, Perm.mul_apply, hα, hψ]
--   transtive_preimage v := by
--     rw [DartStructure.preimage_fᵥ_contract]
--     refine ⟨?_, ?_⟩
--     · sorry
--     simp only [mem_diff, PFun.mem_preimage, Set.mem_preimage, mem_singleton_iff, not_exists,
--       not_and, and_imp, forall_exists_index]
--     rintro d u rfl hud hCd d' v hvu hvd' hCd'
--     simp [contractσ, SameCycle]
--     sorry

end Contract

-- def of_simplify {φ : E → E} (M : CombinatorialMap (G.simplify φ) (IncidenceType V E))
--     (hφ : G.parallelClasses.IsRepFun φ) : CombinatorialMap G (IncidenceType V E) where
--   fₑ d := (M.fₑ d).map φ
--   ran_fₑ := by
--     ext e
--     simp only [ran, mem_map_iff, mem_setOf_eq]


noncomputable def EulerCharacteristic [G.Finite] (M : CombinatorialMap G D) : ℤ :=
  (V(G).ncard - E(G).ncard) + M.faceCycles.ncard - G.Components.ncard

lemma Connected.eulerCharacteristic_eq (h : G.Connected) (M : CombinatorialMap G D) [G.Finite] :
    M.EulerCharacteristic = (V(G).ncard - E(G).ncard) + M.faceCycles.ncard - 1 := by
  have := h.numberOfComponents
  simp only [NumberOfComponents] at this
  simp [this, Set.ncard, EulerCharacteristic]

lemma noEdge_eulerCharacteristic (hX : X.Finite) (M : CombinatorialMap (Graph.noEdge X E) D) :
    letI : (Graph.noEdge X E).Finite := vertexSet_finite_iff.mp hX
    M.EulerCharacteristic = 0 := by
  simp only [EulerCharacteristic, vertexSet_noEdge, edgeSet_noEdge, ncard_empty, tsub_zero]
  have hD : M.fₑ.Dom = ∅ := by
    rw [← ran_eq_empty_iff_dom_eq_empty, M.ran_fₑ]
    rfl
  sorry

lemma EulerCharacteristic.induce_isol (h : V(G) \ Isol(G) ⊆ X) (M : CombinatorialMap G D) [G.Finite]
    (hX : X.Finite) : letI : (G[X]).Finite := vertexSet_finite_iff.mp hX
    M.EulerCharacteristic = (M.induce X).EulerCharacteristic := by

  sorry

lemma EulerCharacteristic.of_le (h : H ≤ G) (M : CombinatorialMap G D) [G.Finite] :
    letI : H.Finite := Finite.mono ‹G.Finite› h
    M.EulerCharacteristic ≤ (M.of_le h).EulerCharacteristic := by

  sorry



end CombinatorialMap
end Graph
