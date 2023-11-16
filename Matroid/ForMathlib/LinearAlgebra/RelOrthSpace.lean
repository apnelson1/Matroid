import Matroid.ForMathlib.LinearAlgebra.StdBasis

open Set BigOperators Submodule Function Finsupp

variable {R K ι : Type*} [CommRing R] [Field K] {s : Set ι}



#check Finset.sum_congr


-- theorem foo (s : Set ι) (U : Submodule K (ι → K)) (hU : U ≤ s.supportedFun K) :
--     s.relOrthSpace (s.relOrthSpace U) = U := by
--   sorry


-- theorem mem_relOrthSpace_iff_exists_finsupp (s : Set ι) (U : Submodule R (ι → R)) :
--     x ∈ s.relOrthSpace U ↔ x.support ⊆ s ∧
--       (∃ l : s →₀ R, (∀ x ∈ U, (Finsupp.total _ _ _ (x ∘ s.incl) l = 0) ∧ ∀ i, l i = x i)) := by
--   rw [relOrthSpace, mem_inf]


-- theorem relOrthSpace_eq_relOrthSpace_inf (s : Set ι) (U : Submodule R (ι → R)) :
--     s.relOrthSpace U = s.relOrthSpace (U ⊓ (s.supportedFun R)) := by
--   classical
--   ext x
--   rw [relOrthSpace, relOrthSpace, mem_inf, mem_supportedFun_iff, mem_inf, mem_supportedFun_iff,
--     and_congr_left_iff, orthSpace, mem_map, orthSpace, mem_map]
--   simp only [mem_orthSpace'_iff, ge_iff_le, mem_inf,
--     mem_supportedFun_iff, and_imp]
--   intro hx
--   refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
--   · obtain ⟨y, hy, rfl⟩ := h
--     refine ⟨y, fun x hxU _↦ hy x hxU, rfl⟩
--   obtain ⟨y, hy, rfl⟩ := h
--   refine ⟨y, fun x hxU ↦  ?_, rfl⟩
--   rw [Finsupp.total_apply, Finsupp.sum]



-- theorem Set.Finite.relOrthSpace_eq {s : Set ι} (hs : s.Finite) {U : Submodule R (ι → R)}:
--     s.relOrthSpace U =
--       (U.map (LinearMap.funLeft R R s.incl)).orthSpace.map (ExtendByZero.linearMap R s.incl) := by
--   have _ := hs.fintype
--   rw [relOrthSpace, orthSpace]
--   ext x
--   simp only [ge_iff_le, mem_inf, mem_map, mem_orthSpace'_iff, mem_supportedFun_iff,
--     mem_orthSpace_iff', forall_exists_index, and_imp,
--     forall_apply_eq_imp_iff₂, LinearMap.funLeft_apply, Finsupp.lcoeFun,
--     LinearMap.coe_mk, AddHom.coe_mk]
--   constructor
--   · rintro ⟨⟨y, hy, rfl⟩, h⟩
--     use Finsupp.lsubtypeDomain (R := R) (s := s) y
--     simp only [Finsupp.lsubtypeDomain, Finsupp.subtypeDomain, LinearMap.coe_mk, AddHom.coe_mk,
--       Finsupp.coe_mk, comp_apply]
--     refine ⟨fun a ha ↦ ?_, ?_⟩
--     · convert hy a ha
--       have hss : y.support ⊆ s.toFinset
--       · rwa [Set.subset_toFinset, ←Finsupp.fun_support_eq]
--       rw [Finsupp.total_apply, Finsupp.sum, Finset.sum_subset hss (by aesop)]
--       · simp_rw [(show ∀ i : s, a (incl s i) = a i from fun _↦ rfl)]
--         exact Finset.sum_set_coe (s := s) (f := fun x ↦ y x * a x)
--     · ext i
--       simp only [ExtendByZero.linearMap_apply, Subtype.exists, not_exists]
--       obtain (hi | hi) := em (i ∈ s)
--       · rw [← Subtype.coe_mk i hi, Subtype.val_injective.extend_apply]
--         simp
--       rw [extend_apply', eq_comm]
--       · rw [support_subset_iff] at h
--         simpa using (mt <| h i) hi
--       rintro ⟨i, rfl⟩
--       exact hi i.2







end relOrthSpace
