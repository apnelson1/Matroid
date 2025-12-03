import Mathlib.LinearAlgebra.LinearIndependent.Defs -- inefficient import
import Mathlib.LinearAlgebra.Basis.Basic -- inefficient import
import Mathlib.LinearAlgebra.Dimension.Constructions -- inefficient import
import Mathlib.Data.Set.Card -- inefficient import


variable {ι ι' : Type*} {R : Type*} {K : Type*} {s : Set ι} {M M' V : Type*} {v : ι → M}

variable [Semiring R] [AddCommMonoid M] [AddCommMonoid M'] [Module R M] [Module R M']

open Function Set Submodule Module


noncomputable def Basis.spanImage {ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {v : ι → M} {s : Set ι} (hli : LinearIndepOn R v s) : Basis s R (span R (v '' s)) :=
  (Basis.span hli.linearIndependent).map <| LinearEquiv.ofEq _ _ <| congr_arg _ <| by aesop

@[simp]
theorem Basis.spanImage_apply {ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {v : ι → M} {s : Set ι} (hli : LinearIndepOn R v s) {i : s} :
    (Basis.spanImage hli) i = v i := by
  simp [Basis.spanImage, Basis.span]

noncomputable def Basis.mkImage {ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {v : ι → M} {s : Set ι} (hli : LinearIndepOn R v s) (hsp : ⊤ ≤ Submodule.span R (v '' s)) :
    Basis s R M :=
  Basis.mk hli.linearIndependent <| by rwa [← image_eq_range]


/-- Replace the unprimed version with this. -/
theorem LinearIndepOn.union_of_quotient' {R M ι : Type*} [DivisionRing R] [AddCommGroup M]
    [Module R M] {s t : Set ι} {f : ι → M}
    (hs : LinearIndepOn R f s) (ht : LinearIndepOn R (mkQ (span R (f '' s)) ∘ f) t) :
    LinearIndepOn R f (s ∪ t) := by
  apply hs.union ht.of_comp
  convert (Submodule.range_ker_disjoint ht).symm
  · simp
  aesop

theorem linearIndepOn_pair_iff' {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M] {i j : ι}
    (f : ι → M) (hij : i ≠ j) :
    LinearIndepOn R f {i,j} ↔ ∀ c d : R, c • f i = d • f j → (c = 0 ∧ d = 0) := by
  classical
  rw [linearIndepOn_iff'']
  refine ⟨fun h c d hcd ↦ ?_, fun h t g ht hg0 h0 ↦ ?_⟩
  · specialize h {i, j} (Pi.single i c - Pi.single j d)
    simpa +contextual [Finset.sum_pair, Pi.single_apply, hij, hij.symm, hcd] using h
  have ht' : t ⊆ {i, j} := by simpa [← Finset.coe_subset]
  rw [Finset.sum_subset ht', Finset.sum_pair hij, add_eq_zero_iff_eq_neg, ← neg_smul] at h0
  · obtain ⟨hi0, hj0⟩ := h _ _ h0
    simp only [neg_eq_zero] at hj0
    exact fun k hkt ↦ Or.elim (ht hkt) (fun h ↦ h ▸ hi0) (fun h ↦ h ▸ hj0)
  simp +contextual [hg0]

theorem linearDepOn_pair_iff {K V ι : Type*} [DivisionRing K] [AddCommGroup V]
  [Module K V] {i j : ι} (f : ι → V) (hij : i ≠ j) :
    ¬ LinearIndepOn K f {i, j} ↔ ∃ c d : K, c • f i = d • f j ∧ ¬ (c = 0 ∧ d = 0) := by
  by_cases hi : f i = 0
  · exact iff_of_true (fun h ↦ h.ne_zero (by simp) hi) ⟨1, 0, by simp [hi]⟩
  simp only [linearIndepOn_pair_iff f hij hi, ne_eq, not_forall, not_not, not_and]
  refine ⟨fun ⟨c, hc⟩ ↦ ⟨c, 1, by simpa, by simp⟩, fun ⟨c, d, h, hcd⟩ ↦ ⟨d⁻¹ * c, ?_⟩⟩
  rw [mul_smul, h, inv_smul_smul₀]
  rintro rfl
  exact hcd (by simpa [hi] using h) rfl

@[simp]
theorem Basis.mkImage_apply {ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {v : ι → M} {s : Set ι} (hli : LinearIndepOn R v s) (hsp : ⊤ ≤ Submodule.span R (v '' s))
    (i : s) : Basis.mkImage hli hsp i = v i.1 := by
  rw [Basis.mkImage, Basis.mk_apply]

@[simp]
theorem Basis.mkImage_repr {ι R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {v : ι → M} {s : Set ι} (hli : LinearIndepOn R v s) (hsp : ⊤ ≤ Submodule.span R (v '' s))
    (x : M) : (Basis.mkImage hli hsp).repr x =
    hli.repr ⟨x, by rw [← image_eq_range, top_le_iff.1 hsp]; exact mem_top⟩  := by
  simp [Basis.mkImage]

@[simp]
lemma Finsupp.ker_lcoeFun {α M R : Type*} [Semiring R] [AddCommMonoid M] [Module R M] :
    LinearMap.ker (Finsupp.lcoeFun (α := α) (M := M) (R := R)) = ⊥ := by
  ext f
  simp [lcoeFun]

section extend

variable {ι R M : Type*} [DivisionRing R] [AddCommGroup M] [Module R M] {s₀ s t : Set ι} {v : ι → M}

theorem LinearIndepOn.exists_maximal (hli : LinearIndepOn R v s₀) (hs₀t : s₀ ⊆ t) :
    ∃ s, s₀ ⊆ s ∧ Maximal (fun r ↦ r ⊆ t ∧ LinearIndepOn R v r) s :=
  zorn_subset_nonempty {r | r ⊆ t ∧ LinearIndepOn R v r}
    (fun c hcss hchain _ ↦ ⟨⋃₀ c, ⟨sUnion_subset fun _ hxc ↦ (hcss hxc).1,
      linearIndepOn_sUnion_of_directed hchain.directedOn fun _ hxc ↦ (hcss hxc).2⟩,
      fun _ hs ↦ subset_sUnion_of_mem hs⟩) s₀ ⟨hs₀t, hli⟩

noncomputable def LinearIndepOn.extension (hli : LinearIndepOn R v s) (hst : s ⊆ t) : Set ι :=
  (hli.exists_maximal hst).choose

lemma LinearIndepOn.extension_maximal (hli : LinearIndepOn R v s) (hst : s ⊆ t) :
    Maximal (fun r ↦ r ⊆ t ∧ LinearIndepOn R v r) (hli.extension hst) :=
  (hli.exists_maximal hst).choose_spec.2

lemma LinearIndepOn.subset_extension (hli : LinearIndepOn R v s) (hst : s ⊆ t) :
    s ⊆ (hli.extension hst) :=
  (hli.exists_maximal hst).choose_spec.1

lemma LinearIndepOn.span_eq_of_maximal_subset
    (hmax : Maximal (fun r ↦ r ⊆ t ∧ LinearIndepOn R v r) s) :
    span R (v '' s) = span R (v '' t) := by
  refine le_antisymm (span_mono (image_mono hmax.prop.1)) <| span_le.2 ?_
  rintro _ ⟨x, hx, rfl⟩
  exact hmax.prop.2.mem_span_iff.2 <|
    fun h ↦ hmax.mem_of_prop_insert ⟨(insert_subset hx hmax.prop.1), h⟩

lemma LinearIndepOn.span_eq_top_of_maximal (hmax : Maximal (LinearIndepOn R v ·) s) :
    span R (v '' s) = span R (range v) := by
  rw [← image_univ, LinearIndepOn.span_eq_of_maximal_subset (t := univ) (by simpa)]

-- #check LinearIndepOn.encard_le_toENat_rank

-- lemma linearIndepOn.extension_span_eq (hli : LinearIndepOn R v s) (hst : s ⊆ t) :

-- lemma LinearIndepOn.extension_subset (hli : LinearIndepOn R v s) (hst : s ⊆ t) :
--     (hli.extension hst) ⊆ t :=
--   (hli.extension_maximal hst).prop.1

-- lemma LinearIndepOn.subset_span_extension (hli : LinearIndepOn R v s) (hst : s ⊆ t) :
--     v '' t ⊆ span R (v '' hli.extension hst) := by
--   have := (hli.exists_maximal hst).choose_spec

-- lemma LinearIndepOn.span_extension (hli : LinearIndepOn R v s) (hst : s ⊆ t) :
--     span R (v '' hli.extension hst) = span R (v '' t) := by
--   have := (hli.exists_maximal hst).choose_spec



-- lemma LinearIndepOn.linearIndepOn_extension (hli : LinearIndepOn R v s) (hst : s ⊆ t) :
--     LinearIndepOn R v (hli.extension hst) :=
--   (hli.exists_extension hst).choose_spec.2.2.2

-- lemma LinearIndepOn.extension_maximal (hli : LinearIndepOn R v s) :
--     Maximal (LinearIndepOn R v ·) (hli.extension (subset_univ _)) := by


-- /-- Any linearly independent subset of `t` extends to a maximal such set. -/
-- theorem LinearIndepOn.exists_extension (hli : LinearIndepOn R v s₀) (hs₀t : s₀ ⊆ t) :
--         ∃ s ⊆ t, s₀ ⊆ s ∧ span R (v '' t) = span R (v '' s) ∧ LinearIndepOn R v s := by
--   have hzorn := zorn_subset_nonempty
--     {r | s₀ ⊆ r ∧ r ⊆ t ∧ LinearIndepOn R v r} ?_ s₀ ⟨Subset.rfl, hs₀t, hli⟩
--   · obtain ⟨m, hs₀m, hmax⟩ := hzorn
--     refine ⟨m, hmax.prop.2.1, hs₀m, ?_, hmax.prop.2.2⟩
--     refine span_eq_span ?_ ((image_mono (hmax.prop.2.1)).trans <| subset_span ..)
--     rintro _ ⟨x, hx, rfl⟩
--     by_contra hxm
--     rw [SetLike.mem_coe, hmax.prop.2.2.notMem_span_iff] at hxm
--     exact hxm.1 <| hmax.mem_of_prop_insert
--       ⟨hs₀m.trans <| subset_insert .., insert_subset hx hmax.prop.2.1, hxm.2⟩
--   refine fun c hcss hchain ⟨r, hr⟩ ↦ ⟨⋃₀ c, ⟨(hcss hr).1.trans <| subset_sUnion_of_mem hr,
--     sUnion_subset fun t' ht'c ↦ (hcss ht'c).2.1,?_⟩, fun _ ↦ subset_sUnion_of_mem⟩
--   exact linearIndepOn_sUnion_of_directed hchain.directedOn fun a hac ↦ (hcss hac).2.2


--   _
