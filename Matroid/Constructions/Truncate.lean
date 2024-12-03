import Matroid.Extension
import Matroid.ForMathlib.FinDiff

variable {α : Type*} {M : Matroid α} {E I B : Set α} {k : ℕ∞}

namespace Matroid

open Set

section truncateTo

/-- The `IndepMatroid` whose independent sets are the `M`-independent sets of size at most `k`. -/
def truncateToNat (M : Matroid α) (k : ℕ) : Matroid α :=
  IndepMatroid.matroid <| IndepMatroid.ofBddAugment
  (E := M.E)
  (Indep := fun I ↦ M.Indep I ∧ I.encard ≤ k)
  (indep_empty := by simp)
  (indep_subset := fun I J hI hIJ ↦ ⟨hI.1.subset hIJ, (encard_mono hIJ).trans hI.2⟩)
  (indep_aug := by
    rintro I J ⟨hI, _⟩ ⟨hJ, hJc⟩ hIJ
    obtain ⟨e, he, hi⟩ := hI.augment hJ hIJ
    exact ⟨e, he.1, he.2, hi,
      (encard_insert_of_not_mem he.2).trans_le ((Order.add_one_le_of_lt hIJ).trans hJc)⟩)
  (indep_bdd := ⟨k, fun _ ↦ And.right⟩)
  (subset_ground := fun _ h ↦ h.1.subset_ground)

/-- The truncation of a matroid to rank `k`. The independent sets of the truncation
are the independent sets of the matroid of size at most `k`.  -/
def truncateTo (M : Matroid α) (k : ℕ∞) : Matroid α :=
  Matroid.ofExistsMatroid
    (E := M.E)
    (Indep := fun I ↦ M.Indep I ∧ I.encard ≤ k)
    (hM :=  k.recTopCoe ⟨M, rfl, by simp⟩
      (fun k ↦ ⟨M.truncateToNat k, rfl, fun _ ↦ by simp [truncateToNat]⟩))

@[simp] theorem truncateTo_top (M : Matroid α) : M.truncateTo ⊤ = M :=
  ext_indep rfl (by simp [truncateTo])

@[simp] theorem truncateTo_indep_iff : (M.truncateTo k).Indep I ↔ (M.Indep I ∧ I.encard ≤ k) :=
    Iff.rfl

theorem truncateTo_indep_eq : (M.truncateTo k).Indep = fun I ↦ M.Indep I ∧ I.encard ≤ k := rfl

@[simp] theorem truncateTo_ground_eq : (M.truncateTo k).E = M.E := rfl

@[simp] theorem truncateTo_zero (M : Matroid α) : M.truncateTo 0 = loopyOn M.E := by
  refine ext_indep rfl ?_
  suffices ∀ I ⊆ M.E, I = ∅ → M.Indep I by simpa
  rintro I - rfl; exact M.empty_indep

@[simp] theorem truncateTo_emptyOn (α : Type*) (k : ℕ∞) : (emptyOn α).truncateTo k = emptyOn α := by
  rw [← ground_eq_empty_iff, truncateTo_ground_eq, emptyOn_ground]

@[simp] theorem truncate_loopyOn (E : Set α) (k : ℕ∞) : (loopyOn E).truncateTo k = loopyOn E := by
  apply ext_indep (by simp)
  suffices ∀ I ⊆ E, I = ∅ → encard I ≤ k by simpa
  rintro _ - rfl; simp

theorem truncate_eq_self_of_rk_le (h_rk : M.erk ≤ k) : M.truncateTo k = M := by
  refine ext_indep truncateTo_ground_eq (fun I _ ↦ ?_)
  rw [truncateTo_indep_iff, and_iff_left_iff_imp]
  exact fun hi ↦ hi.encard_le_erk.trans h_rk

theorem truncateTo_base_iff {k : ℕ} (h_rk : k ≤ M.erk) :
    (M.truncateTo k).Base B ↔ M.Indep B ∧ B.encard = k := by
  simp_rw [base_iff_maximal_indep, truncateTo_indep_eq, maximal_subset_iff, and_assoc,
    and_congr_right_iff, and_imp]
  refine fun hi ↦ ⟨fun ⟨hle, hmax⟩ ↦ ?_, fun h ↦ ⟨h.le, fun J _ hcard hBJ ↦ ?_⟩⟩
  · obtain ⟨B', hB', hBB'⟩ := hi.exists_base_superset
    obtain ⟨J, hBJ, hJB', h'⟩ := exists_superset_subset_encard_eq hBB' hle (by rwa [hB'.encard])
    rwa [hmax (hB'.indep.subset hJB') h'.le hBJ]
  exact (finite_of_encard_le_coe hcard).eq_of_subset_of_encard_le hBJ <| hcard.trans_eq h.symm

theorem truncate_base_iff_of_finiteRk [FiniteRk M] (h_rk : k ≤ M.erk) :
    (M.truncateTo k).Base B ↔ M.Indep B ∧ B.encard = k := by
  lift k to ℕ using (h_rk.trans_lt M.erk_lt_top).ne; rwa [truncateTo_base_iff]

instance truncateTo.finite [Matroid.Finite M] : Matroid.Finite (M.truncateTo k) :=
⟨ by simp [ground_finite M] ⟩

instance truncateTo.finiteRk {k : ℕ} : FiniteRk (M.truncateTo k) := by
  obtain ⟨B, hB⟩ := (M.truncateTo k).exists_base
  refine ⟨B, hB, (le_or_lt M.erk k).elim (fun h ↦ ?_) (fun h ↦ ?_)⟩
  · rw [truncate_eq_self_of_rk_le h] at hB
    rw [← encard_lt_top_iff, hB.encard]
    exact h.trans_lt (WithTop.coe_lt_top _)
  rw [truncateTo_base_iff h.le] at hB
  rw [← encard_lt_top_iff, hB.2]
  apply WithTop.coe_lt_top

theorem Indep.of_truncateTo (h : (M.truncateTo k).Indep I) : M.Indep I := by
  rw [truncateTo_indep_iff] at h; exact h.1

theorem Indep.encard_le_of_truncateTo (h : (M.truncateTo k).Indep I) : I.encard ≤ k :=
  (truncateTo_indep_iff.mp h).2

theorem truncateTo_er_eq (M : Matroid α) (k : ℕ∞) (X : Set α) :
    (M.truncateTo k).er X = min (M.er X) k := by
  simp_rw [le_antisymm_iff, le_er_iff, er_le_iff, truncateTo_indep_iff]
  obtain ⟨I, hI⟩ := M.exists_basis' X
  refine ⟨?_, ?_⟩
  · intro J hJX hJi
    exact le_min (hJi.1.encard_le_er_of_subset hJX) hJi.2
  obtain ⟨I₀, hI₀, hI₀ss⟩ := exists_subset_encard_eq (min_le_of_left_le (b := k) hI.encard.symm.le)
  exact ⟨_, hI₀.trans hI.subset, ⟨hI.indep.subset hI₀, hI₀ss.trans_le (min_le_right _ _)⟩, hI₀ss⟩

end truncateTo

section truncate

/-- The matroid on `M.E` whose independent sets are the independent nonbases of `M`. -/
def truncate (M : Matroid α) := Matroid.ofExistsMatroid
  (E := M.E)
  (Indep := fun I ↦ M.Indep I ∧ (M.Base I → I = ∅))
  (hM := by
    refine ⟨M.projectBy (ModularCut.principal M M.E), rfl, fun I ↦ ?_⟩
    obtain (hM | hM) := M.eq_loopyOn_or_rkPos
    · rw [hM]; simp [ModularCut.eq_top_iff, Subset.rfl]
    suffices M.Indep I → (¬M.E ⊆ M.closure I ↔ M.Base I → I = ∅) by simpa [M.principal_ground_ne_top]
    refine fun hI ↦ ⟨fun h hIb ↦ by simp [hIb.closure_eq, Subset.rfl] at h, fun h hss ↦ ?_⟩
    have hIb := hI.base_of_ground_subset_closure hss
    exact hIb.nonempty.ne_empty (h hIb))

@[simp] lemma truncate_ground_eq : M.truncate.E = M.E := rfl

lemma truncate_indep_iff' : M.truncate.Indep I ↔ M.Indep I ∧ (M.Base I → I = ∅) := Iff.rfl

@[simp] lemma truncate_indep_iff [M.RkPos] : M.truncate.Indep I ↔ M.Indep I ∧ ¬ M.Base I := by
  simp only [truncate_indep_iff', and_congr_right_iff]
  exact fun _ ↦ ⟨fun h hB ↦ hB.nonempty.ne_empty (h hB), fun h hB ↦ by contradiction⟩

@[simp] lemma truncate_loopyOn_eq {E : Set α} : (loopyOn E).truncate = loopyOn E := by
  simp (config := {contextual := true}) [truncate, ModularCut.principal, eq_loopyOn_iff]

lemma truncate_base_iff [M.RkPos] : M.truncate.Base B ↔ ∃ e ∉ B, M.Base (insert e B) := by
  refine ⟨fun h ↦ ?_, fun ⟨e, he, hBe⟩ ↦ ?_⟩
  · obtain ⟨hB, hBb⟩ := truncate_indep_iff.1 h.indep
    obtain ⟨B', hB', hBB'⟩ := hB.exists_base_superset
    obtain ⟨e, heB', heB⟩ := exists_of_ssubset (hBB'.ssubset_of_ne (by rintro rfl; contradiction))
    refine ⟨e, heB, ?_⟩
    rwa [h.eq_of_subset_indep ?_ (subset_diff_singleton hBB' heB), insert_diff_singleton,
      insert_eq_of_mem heB']
    rw [truncate_indep_iff]
    exact ⟨hB'.indep.subset diff_subset, hB'.not_base_of_ssubset <| diff_singleton_sSubset.mpr heB'⟩
  refine Indep.base_of_forall_insert ?_ ?_
  · rw [truncate_indep_iff]
    exact ⟨hBe.indep.subset (subset_insert _ _), hBe.not_base_of_ssubset (ssubset_insert he)⟩
  simp only [truncate_ground_eq, mem_diff, truncate_indep_iff, not_and, not_not, and_imp]
  exact fun f _ hfB hfBi ↦ insert_base_of_insert_indep he hfB hBe hfBi

end truncate

section circuitOn

variable {C : Set α}

/-- The matroid on `E` whose ground set is a circuit. Empty if `E = ∅`. -/
def circuitOn (C : Set α) := (freeOn C).truncate

@[simp] lemma circuitOn_ground : (circuitOn C).E = C := rfl

lemma circuitOn_indep_iff (hC : C.Nonempty) : (circuitOn C).Indep I ↔ I ⊂ C := by
  have := freeOn_rkPos hC
  simp [circuitOn, truncate_indep_iff, ssubset_iff_subset_ne]

lemma circuitOn_dep_iff (hC : C.Nonempty) {D : Set α} : (circuitOn C).Dep D ↔ D = C := by
  simp only [Dep, circuitOn_indep_iff hC, ssubset_iff_subset_ne, ne_eq, not_and, not_not,
    circuitOn_ground]
  exact ⟨fun h ↦ h.1 h.2, by rintro rfl; simp [Subset.rfl]⟩

lemma circuitOn_base_iff (hC : C.Nonempty) : (circuitOn C).Base B ↔ ∃ e ∉ B, insert e B = C := by
  have _ := freeOn_rkPos hC; simp [circuitOn, truncate_base_iff]

lemma circuitOn_ground_circuit (hC : C.Nonempty) : (circuitOn C).Circuit C := by
  simp [circuit_iff_forall_ssubset, circuitOn_dep_iff hC, circuitOn_indep_iff hC]

lemma circuitOn_circuit_iff (hC : C.Nonempty) {C' : Set α} : (circuitOn C).Circuit C' ↔ C' = C := by
  refine ⟨fun h ↦ h.eq_of_subset_circuit (circuitOn_ground_circuit hC) h.subset_ground, ?_⟩
  rintro rfl
  exact circuitOn_ground_circuit hC

lemma ground_circuit_iff [M.Nonempty] : M.Circuit M.E ↔ M = circuitOn M.E := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine ext_circuit rfl <| fun C hC ↦ ?_
    rw [circuitOn_circuit_iff h.nonempty]
    exact ⟨fun h' ↦ h'.eq_of_subset_circuit h hC, by rintro rfl; assumption⟩
  rw [h]
  exact circuitOn_ground_circuit M.ground_nonempty

lemma circuit_iff_restr_eq_circuitOn (hCne : C.Nonempty) (hC : C ⊆ M.E := by aesop_mat) :
    M.Circuit C ↔ M ↾ C = circuitOn C := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine ext_circuit rfl fun C' hC' ↦ ?_
    rw [restrict_circuit_iff h.subset_ground, circuitOn_circuit_iff h.nonempty,
      and_iff_left (show C' ⊆ C from hC')]
    exact ⟨fun h' ↦ h'.eq_of_subset_circuit h hC', fun h' ↦ by rwa [h']⟩
  have h' := restrict_circuit_iff hC (C := C)
  rwa [and_iff_left Subset.rfl, h, iff_true_intro (circuitOn_ground_circuit hCne), true_iff] at h'

end circuitOn

section Local

variable {I J B : Set α} {Bs : Set (Set α)}


lemma Base.base_of_indep_of_finDiff (hB : M.Base B) (hI : M.Indep I) (hBI : FinDiff B I) :
    M.Base I := by
  obtain ⟨B', hB', hIB'⟩ := hI.exists_base_superset
  have hfin' : FinDiff B B' := by
    rw [finDiff_iff, hB'.encard_diff_comm hB, and_iff_left rfl]
    exact hBI.diff_left_finite.subset (diff_subset_diff_right hIB')
  rwa [(hBI.symm.trans hfin').eq_of_subset hIB']

def LocalTruncateIndep (M : Matroid α) (Bs : Set (Set α)) (I : Set α) : Prop := M.Indep I ∧ I ∉ Bs

lemma LocalTruncateIndep.subset (hI : M.LocalTruncateIndep Bs I) (hBs : ∀ ⦃B⦄, B ∈ Bs → M.Base B)
    (hJI : J ⊆ I) : M.LocalTruncateIndep Bs J :=
  ⟨hI.1.subset hJI, fun hJBs ↦ hI.2 <| by rwa [← (hBs hJBs).eq_of_subset_indep hI.1 hJI] ⟩

lemma maximal_localTruncateIndep_iff (hBs_base : ∀ ⦃B⦄, B ∈ Bs → M.Base B)
    (hBs_finDiff : ∀ ⦃B B'⦄, B ∈ Bs → M.Base B' → FinDiff B B' → B' ∈ Bs) :
    Maximal (M.LocalTruncateIndep Bs) B ↔ (M.Base B ∧ B ∉ Bs) ∨ (∃ e ∉ B, insert e B ∈ Bs) := by
  rw [maximal_subset_iff, LocalTruncateIndep]
  refine ⟨fun ⟨⟨hBi, hBb⟩, hmax⟩ ↦ ?_, ?_⟩
  · obtain ⟨B', hB', hBB'⟩ := hBi.exists_base_superset
    obtain rfl | hss := hBB'.eq_or_ssubset
    · exact .inl ⟨hB', hBb⟩
    right
    obtain ⟨e, heB', heB⟩ := exists_of_ssubset hss
    refine ⟨e, heB, by_contra fun heBb ↦ ?_⟩
    rw [hmax ⟨(hB'.indep.subset (insert_subset heB' hBB')), heBb⟩ (subset_insert _ _)] at heB
    simp at heB
  rintro (⟨hB, hBb⟩ | ⟨e, heB, heBb⟩)
  · exact ⟨⟨hB.indep, hBb⟩, fun J hJ hBJ ↦ hB.eq_of_subset_indep hJ.1 hBJ⟩
  refine ⟨⟨?_, fun hBs ↦ heB ?_⟩, fun J hJ hBJ ↦ by_contra fun hne ↦ ?_⟩
  · exact (hBs_base heBb).indep.subset (subset_insert _ _)
  · rw [(hBs_base hBs).eq_of_subset_base (hBs_base heBb) (subset_insert _ _)]
    simp
  obtain ⟨f, hfJ, hfB⟩ := exists_of_ssubset (hBJ.ssubset_of_ne hne)

  have hfB_base : M.Base (insert f B) :=
    (hBs_base heBb).base_of_indep_of_finDiff (hJ.1.subset (insert_subset hfJ hBJ))
    (finDiff_insert_insert heB hfB)
  obtain rfl : insert f B = J := hfB_base.eq_of_subset_indep hJ.1 (insert_subset hfJ hBJ)
  exact hJ.2 <| hBs_finDiff heBb hfB_base (finDiff_insert_insert heB hfB)



/- Truncate a uniform matroid at a base `B₀`, by squashing every base at finite distance to `B₀`.
For finite uniform matroids, this just reduces the rank by one. For infinite ones,
This is weird, since it forms a proper quotient that still has a common base with `M` -/


-- def LocalTruncateIndepMatroid (M : Matroid α) (hr : M.RkPos) (Bs : Set (Set α))
--     (hBs_base : ∀ ⦃B⦄, B ∈ Bs → M.Base B)
--     (hBs_finDiff : ∀ ⦃B B'⦄, B ∈ Bs → M.Base B' → FinDiff B B' → B' ∈ Bs) : IndepMatroid α where
--   E := M.E
--   Indep := M.LocalTruncateIndep Bs
--   indep_empty := ⟨M.empty_indep, fun h ↦ M.empty_not_base (hBs_base h)⟩

--   indep_subset I J hJ hIJ := hJ.subset hBs_base hIJ
--   indep_aug := by
--     simp only [maximal_localTruncateIndep_iff hBs_base hBs_finDiff, not_or, not_and, not_not,
--       not_exists, mem_diff, and_imp]
--     rintro I B hI hInotbase hBmax
--     replace hInotbase := show ¬ M.Base I by simpa [hI.2] using hInotbase
--     rintro (⟨hB, hBb⟩ | ⟨e, heB, heBb⟩)
--     · obtain ⟨e, ⟨heB, heI⟩, heIi⟩ := hI.1.exists_insert_of_not_base hInotbase hB
--       exact ⟨e, ⟨heB, heI⟩, heIi, hBmax e heI⟩
--     -- have heI : e ∈ I := by
--     --   by_contra heI
--     --   have := hBmax _ heI
--     obtain ⟨f, ⟨(rfl | hf), hfI⟩, hfi⟩ := hI.1.exists_insert_of_not_base hInotbase (hBs_base heBb)
--     ·
--       by_cases hbase : M.Base (insert f I)
--       · sorry
--       obtain ⟨g, hg, hgi⟩ := hfi.exists_insert_of_not_base hbase (hBs_base heBb)
--       simp only [mem_insert_iff, true_or, insert_diff_of_mem, mem_diff, not_or] at hg
--       rw [insert_comm] at hgi
--       refine ⟨g, ⟨hg.1, hg.2.2⟩, hgi.subset (subset_insert _ _), fun hgI ↦ ?_⟩
--       obtain (rfl | hfI) : f ∈ insert g I :=
--         ((hBs_base hgI).eq_of_subset_indep hgi (subset_insert _ _)).symm.subset (mem_insert f _)
--       · exact hg.2.1 rfl
--       contradiction
--       --   -- have := hbase.exchange (hBs_base heBb) (e := f)

--       -- sorry
--     sorry
        -- have := hbase.exchange (hBs_base heBb)






    -- have hInotbase : ¬ M.Base I := sorry
    -- by_cases hB : M.Base B
    -- · obtain ⟨e, heBI, heI⟩ := hI.1.exists_insert_of_not_base hInotbase hB
    --   obtain ⟨f, hfI, hins⟩ :=
    --     exists_insert_of_not_maximal (fun I J hJ hIJ ↦ hJ.subset hBs_base hIJ) hI hInotmax
    --   refine ⟨e, heBI, heI, fun heIBs ↦ hins.2 ?_⟩
    --   refine hBs_finDiff heIBs ?_ (finDiff_insert_insert heBI.2 hfI)
    --   exact (hBs_base heIBs).base_of_indep_of_finDiff hins.1 (finDiff_insert_insert heBI.2 hfI)

    -- obtain ⟨B₀, hB₀⟩ := M.exists_base
    -- obtain ⟨e, ⟨-, heB⟩, heBi⟩ := hBmax.prop.1.exists_insert_of_not_base hB hB₀
    -- have heBb : insert e B ∈ Bs :=
    --   by_contra fun h' ↦ hBmax.not_prop_of_ssuperset (ssubset_insert heB) ⟨heBi, h'⟩
    -- have :=

  -- indep_maximal := sorry
  -- subset_ground := sorry
-- def LocalTruncate (hM : M.Uniform) {B₀ : Set α} (hB₀ : M.Base B₀) (hne : B₀.Nonempty) : Matroid α :=
--   uniform_matroid_of_base M.E
--     (fun B ↦ (M.Base B ∧ ¬ FinDiff B B₀) ∨ (∃ e ∉ B, FinDiff (insert e B) B₀))
--     (by
--       obtain ⟨e, he⟩ := hne
--       exact ⟨B₀ \ {e}, .inr ⟨e, (by simp), by simp [he, finDiff_refl]⟩⟩)
--     (by

--       rintro B (⟨hB, hBB₀⟩ | ⟨e, heB, hBB₀⟩) B' (⟨hB', hB'B₀⟩ | ⟨e', he'B', hB'B₀⟩) hne hss
--       · obtain rfl : B = B' := hB.eq_of_subset_base hB' hss
--         contradiction
--       · have heB'ins := (hM.base_of_base_of_finDiff hB₀ hB'B₀.symm)
--         obtain rfl : B = insert e' B' :=
--           hB.eq_of_subset_base heB'ins <| hss.trans (subset_insert _ _)
--         exact he'B' (hss (mem_insert _ _))
--       · have heBins := (hM.base_of_base_of_finDiff hB₀ hBB₀.symm)
--         refine hB'B₀ (FinDiff.trans ?_ hBB₀)
--         obtain ⟨f, hfB', hfB⟩ := exists_of_ssubset (hss.ssubset_of_ne hne)
--         have hfBins : M.Base (insert f B) := insert_base_of_insert_indep heB hfB heBins
--           (hB'.indep.subset (insert_subset hfB' hss))
--         obtain rfl : insert f B = B' := hfBins.eq_of_subset_base hB' (insert_subset hfB' hss)
--         apply finDiff_insert_insert hfB heB

--       have heBins := hM.base_of_base_of_finDiff hB₀ hBB₀.symm
--       have he'B'ins := hM.base_of_base_of_finDiff hB₀ hB'B₀.symm

--       by_cases heB' : e ∈ B'
--       · have h_eq : insert e B = insert e' B' := heBins.eq_of_subset_base he'B'ins
--           (insert_subset (mem_insert_of_mem _ heB') (hss.trans (subset_insert _ _)))
--         obtain rfl | he'B := h_eq.symm.subset (mem_insert e' B')
--         · contradiction
--         exact he'B' (hss he'B)
--       have hb := hM.base_of_base_of_finDiff he'B'ins (finDiff_insert_insert he'B' heB')
--       have h_eq := heBins.eq_of_subset_base hb (insert_subset_insert hss)
--       apply_fun (fun X ↦ X \ {e}) at h_eq
--       obtain rfl : B = B' := by simpa [heB, heB'] using h_eq
--       contradiction )
--     (by
--       rintro B e f (⟨hB, hBB₀⟩ | ⟨g, hgB, hgBB₀⟩) heB hfB
--       · left
--         rw [finDiff_comm, ← finDiff_iff_exchange heB hfB, finDiff_comm, and_iff_left hBB₀]
--         exact hM.base_of_base_of_finDiff hB (finDiff_exchange heB hfB)

--       right
--       have hef : e ≠ f := by rintro rfl; contradiction
--       refine ⟨e, by simp [hef], FinDiff.trans ?_ hgBB₀⟩
--       rw [insert_diff_singleton_comm hef.symm, insert_diff_singleton,
--         insert_eq_of_mem (mem_insert_of_mem _ heB)]
--       exact finDiff_insert_insert hfB hgB )
--     (by
--       intro I X hIX hXE hinf
--       sorry
--     )
--     sorry




-- def tr (M : Matroid α) : Matroid α where
--   E := M.E
--   Base B := ∃ e ∉ B, M.Base (insert e B)
--   Indep I := M.Indep I ∧ ¬ M.Base I
--   indep_iff' I := by
--     refine ⟨fun ⟨hI, hIb⟩ ↦ ?_, fun ⟨B, ⟨e, heB, heB'⟩, hIB⟩ ↦ ?_⟩
--     · obtain ⟨B, hB, hIB⟩ := hI.exists_base_superset
--       obtain ⟨e, heB, heI⟩ := exists_of_ssubset (hIB.ssubset_of_ne (by rintro rfl; contradiction))
--       exact ⟨B \ {e}, ⟨e, by simp, by simpa [heB]⟩, subset_diff_singleton hIB heI⟩
--     have hIBe : I ⊆ insert e B := hIB.trans (subset_insert _ _)
--     refine ⟨heB'.indep.subset hIBe, fun hI ↦ heB (hIB ?_)⟩
--     simp [hI.eq_of_subset_base heB' hIBe]
--   exists_base := _
--   base_exchange := _
--   maximality := _
--   subset_ground := _

end Local
