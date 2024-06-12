import Matroid.Equiv
import Matroid.Closure
import Matroid.Constructions.Basic

/-!
  A `Circuit` of a matroid is a minimal dependent set.
-/

variable {α : Type*} {M : Matroid α} {C C' I X K C₁ C₂ R : Set α} {e f x y : α}

open Set Set.Notation
namespace Matroid

/-- A Circuit is a minimal dependent set -/
def Circuit (M : Matroid α) (C : Set α) : Prop := C ∈ minimals (· ⊆ ·) {X | M.Dep X}

lemma circuit_def : M.Circuit C ↔ C ∈ minimals (· ⊆ ·) {X | M.Dep X} := Iff.rfl

lemma Circuit.dep (hC : M.Circuit C) : M.Dep C :=
  hC.1

@[aesop unsafe 20% (rule_sets := [Matroid])]
lemma Circuit.subset_ground (hC : M.Circuit C) : C ⊆ M.E :=
  hC.dep.subset_ground

lemma circuit_iff : M.Circuit C ↔ M.Dep C ∧ ∀ ⦃I⦄, M.Dep I → I ⊆ C → I = C := by
  simp [Circuit, mem_minimals_setOf_iff, and_congr_right_iff, eq_comm (b := C)]

lemma Circuit.ssubset_indep (hC : M.Circuit C) (hXC : X ⊂ C) : M.Indep X := by
  rw [← not_dep_iff (hXC.subset.trans hC.subset_ground)]
  exact fun h ↦ hXC.ne ((circuit_iff.1 hC).2 h hXC.subset)

lemma circuit_iff_forall_ssubset : M.Circuit C ↔ M.Dep C ∧ ∀ ⦃I⦄, I ⊂ C → M.Indep I := by
  simp_rw [circuit_iff, dep_iff, and_congr_right_iff, ssubset_iff_subset_ne, and_imp]
  exact fun _ hC ↦ ⟨fun h I hIC hne ↦ by_contra fun hi ↦ hne (h hi (hIC.trans hC) hIC),
    fun h I hi _ hIC ↦ by_contra fun hne ↦ hi (h hIC hne)⟩

lemma Circuit.diff_singleton_indep (hC : M.Circuit C) (he : e ∈ C) : M.Indep (C \ {e}) :=
  hC.ssubset_indep (diff_singleton_sSubset.2 he)

lemma Circuit.diff_singleton_basis (hC : M.Circuit C) (he : e ∈ C) : M.Basis (C \ {e}) C := by
  nth_rw 2 [← insert_eq_of_mem he];
  rw [← insert_diff_singleton, (hC.diff_singleton_indep he).basis_insert_iff,
    insert_diff_singleton, insert_eq_of_mem he]
  exact Or.inl hC.dep

lemma Circuit.basis_iff_eq_diff_singleton (hC : M.Circuit C) :
    M.Basis I C ↔ ∃ e ∈ C, I = C \ {e} := by
  refine' ⟨fun h ↦ _, _⟩
  · obtain ⟨e, he⟩ := exists_of_ssubset
      (h.subset.ssubset_of_ne (by rintro rfl; exact hC.dep.not_indep h.indep))
    exact ⟨e, he.1, h.eq_of_subset_indep (hC.diff_singleton_indep he.1)
      (subset_diff_singleton h.subset he.2) diff_subset⟩
  rintro ⟨e, he, rfl⟩
  exact hC.diff_singleton_basis he

lemma Circuit.basis_iff_insert_eq (hC : M.Circuit C) :
    M.Basis I C ↔ ∃ e ∈ C \ I, C = insert e I := by
  rw [hC.basis_iff_eq_diff_singleton]
  refine' ⟨fun ⟨e, he, hI⟩ ↦ ⟨e, ⟨he, fun heI ↦ (hI.subset heI).2 rfl⟩, _⟩,
    fun ⟨e, he, hC⟩ ↦ ⟨e, he.1, _⟩⟩
  · rw [hI, insert_diff_singleton, insert_eq_of_mem he]
  rw [hC, insert_diff_self_of_not_mem he.2]

lemma Circuit.cl_diff_singleton_eq_cl (hC : M.Circuit C) (e : α) : M.cl (C \ {e}) = M.cl C :=
  (em (e ∈ C)).elim (fun he ↦ by rw [(hC.diff_singleton_basis he).cl_eq_cl])
    (fun he ↦ by rw [diff_singleton_eq_self he])

lemma Circuit.subset_cl_diff_singleton (hC : M.Circuit C) (e : α) : C ⊆ M.cl (C \ {e}) := by
  by_cases he : e ∈ C
  · rw [(hC.diff_singleton_basis he).cl_eq_cl]; exact M.subset_cl _
  rw [diff_singleton_eq_self he]; exact M.subset_cl _

lemma Circuit.subset_cl_diff_subsingleton (hC : M.Circuit C) {Z : Set α} (hZ : Z.encard ≤ 1) :
    C ⊆ M.cl (C \ Z) := by
  obtain (rfl | ⟨x, rfl⟩) := encard_le_one_iff_eq.1 hZ
  · rw [diff_empty]; apply M.subset_cl _
  exact hC.subset_cl_diff_singleton _

lemma Circuit.cl_diff_subsingleton_eq_cl (hC : M.Circuit C) {Z : Set α} (hZ : Z.encard ≤ 1) :
    M.cl (C \ Z) = M.cl C := by
  obtain (rfl | ⟨x, rfl⟩) := encard_le_one_iff_eq.1 hZ
  · simp
  rw [hC.cl_diff_singleton_eq_cl]

lemma Circuit.mem_cl_diff_singleton_of_mem (hC : M.Circuit C) (heC : e ∈ C) :
    e ∈ M.cl (C \ {e}) :=
  (hC.subset_cl_diff_singleton e) heC

lemma circuit_iff_mem_minimals : M.Circuit C ↔ C ∈ minimals (· ⊆ ·) {X | M.Dep X} := Iff.rfl

lemma Circuit.eq_of_not_indep_subset (hC : M.Circuit C) (hX : ¬ M.Indep X) (hXC : X ⊆ C) :
    X = C :=
  eq_of_le_of_not_lt hXC (hX ∘ hC.ssubset_indep)

lemma Circuit.eq_of_dep_subset (hC : M.Circuit C) (hX : M.Dep X) (hXC : X ⊆ C) : X = C :=
  hC.eq_of_not_indep_subset hX.not_indep hXC

lemma Circuit.not_ssubset (hC : M.Circuit C) (hC' : M.Circuit C') : ¬C' ⊂ C :=
  fun h' ↦ h'.ne (hC.eq_of_dep_subset hC'.dep h'.subset)

lemma Circuit.nonempty (hC : M.Circuit C) : C.Nonempty :=
  hC.dep.nonempty

lemma empty_not_circuit (M : Matroid α) : ¬M.Circuit ∅ :=
  fun h ↦ by simpa using h.nonempty

lemma Circuit.circuit_restrict_of_subset (hC : M.Circuit C) (hCR : C ⊆ R) :
    (M ↾ R).Circuit C := by
  simp_rw [circuit_iff, restrict_dep_iff, dep_iff, and_imp] at *
  refine' ⟨⟨hC.1.1, hCR⟩, fun I hI _ hIC ↦ hC.2 hI (hIC.trans hC.1.2) hIC⟩

lemma restrict_circuit_iff (hR : R ⊆ M.E := by aesop_mat) :
    (M ↾ R).Circuit C ↔ M.Circuit C ∧ C ⊆ R := by
  refine' ⟨_, fun h ↦ h.1.circuit_restrict_of_subset h.2⟩
  simp_rw [circuit_iff, restrict_dep_iff, and_imp, dep_iff]
  exact fun hC hCR h ↦ ⟨⟨⟨hC,hCR.trans hR⟩,fun I hI hIC ↦ h hI.1 (hIC.trans hCR) hIC⟩,hCR⟩

lemma circuit_iff_dep_forall_diff_singleton_indep :
    M.Circuit C ↔ M.Dep C ∧ ∀ e ∈ C, M.Indep (C \ {e}) := by
  rw [circuit_iff_forall_ssubset, and_congr_right_iff]
  refine' fun _ ↦ ⟨fun h e heC ↦ h (Iff.mpr diff_singleton_sSubset heC),
    fun h I hIC ↦ _⟩
  obtain ⟨e, he⟩ := exists_of_ssubset hIC
  exact (h e he.1).subset (subset_diff_singleton hIC.subset he.2)

lemma Circuit.eq_of_subset_circuit (hC₁ : M.Circuit C₁) (hC₂ : M.Circuit C₂) (h : C₁ ⊆ C₂) :
    C₁ = C₂ :=
  hC₂.eq_of_dep_subset hC₁.dep h

/-- For an independent set `I` that spans a point `e ∉ I`, the unique circuit contained in
`I ∪ {e}`. Has the junk value `{e}` if `e ∈ I` and `insert e I` if `e ∉ M.cl I`. -/
def fundCct (M : Matroid α) (e : α) (I : Set α) :=
  insert e (I ∩ (⋂₀ {J | J ⊆ I ∧ e ∈ M.cl J}))

lemma fundCct_eq_sInter (he : e ∈ M.cl I) :
    M.fundCct e I = insert e (⋂₀ {J | J ⊆ I ∧ e ∈ M.cl J}) := by
  rw [fundCct, inter_eq_self_of_subset_right]
  exact sInter_subset_of_mem ⟨Subset.rfl, he⟩

lemma fundCct_subset_insert (e : α) (I : Set α) : M.fundCct e I ⊆ insert e I :=
  insert_subset_insert inter_subset_left

lemma fundCct_subset_ground (he : e ∈ M.E) (hI : I ⊆ M.E := by aesop_mat) : M.fundCct e I ⊆ M.E :=
  (fundCct_subset_insert e I).trans (insert_subset he hI)

lemma mem_fundCct (M : Matroid α) (e : α) (I : Set α) : e ∈ fundCct M e I :=
  mem_insert _ _

/-- The fundamental circuit of `e` and `I` has the junk value `{e}` if `e ∈ I` -/
lemma Indep.fundCct_eq_of_mem (hI : M.Indep I) (he : e ∈ I) : M.fundCct e I = {e} := by
  rw [fundCct, ← union_singleton, union_eq_right]
  refine inter_subset_right.trans (sInter_subset_of_mem ?_)
  simp only [mem_setOf, singleton_subset_iff, and_iff_right he]
  exact M.mem_cl_self _ (hI.subset_ground he)

lemma Indep.fundCct_circuit (hI : M.Indep I) (he : e ∈ M.cl I \ I) :
    M.Circuit (M.fundCct e I) := by
  rw [circuit_iff_dep_forall_diff_singleton_indep,
    ← not_indep_iff (fundCct_subset_ground (M.cl_subset_ground I he.1)), fundCct_eq_sInter he.1]
  --   fundCct_eq_sInter he.1, circuit_iff_dep_forall_diff_singleton_indep,
  -- ← not_indep_iff ()]
  have hu : M.Indep (⋃₀ {J : Set α | J ⊆ I ∧ e ∈ M.cl J}) :=
    hI.subset (sUnion_subset fun J ↦ And.left)
  have hI' : I ∈ {J : Set α | J ⊆ I ∧ e ∈ M.cl J} := ⟨rfl.subset, he.1⟩
  refine' ⟨fun hi ↦ _, fun f hf ↦ _⟩
  · rw [Indep.insert_indep_iff_of_not_mem] at hi
    rw [cl_sInter_eq_biInter_cl_of_sUnion_indep _  ⟨_, hI'⟩ hu] at hi
    · simp at hi
    · exact hI.subset (sInter_subset_of_mem hI')
    exact fun heIs ↦ he.2 (sInter_subset_of_mem hI' heIs)
  obtain rfl | hne := em (e = f)
  · refine' hu.subset _
    simp only [insert_diff_of_mem, mem_singleton]
    exact
      subset_trans diff_subset ((sInter_subset_of_mem hI').trans (subset_sUnion_of_mem hI'))
  rw [mem_insert_iff, mem_sInter, eq_comm, iff_false_intro hne, false_or_iff] at hf
  have hi : M.Indep (⋂₀ {J : Set α | J ⊆ I ∧ e ∈ M.cl J} \ {f}) :=
    hI.subset (diff_subset.trans (sInter_subset_of_mem hI'))
  rw [← insert_diff_singleton_comm hne, hi.insert_indep_iff_of_not_mem, mem_diff,
    and_iff_right ((M.cl_subset_ground _) he.1)]
  · intro hcl
    exact (hf _ ⟨diff_subset.trans (sInter_subset_of_mem hI'), hcl⟩).2 rfl
  exact fun h'e ↦ he.2 (diff_subset.trans (sInter_subset_of_mem hI') h'e)

lemma Base.fundCct_circuit {B : Set α} (hB : M.Base B) (hx : x ∈ M.E \ B) :
    M.Circuit (M.fundCct x B) := by
  apply hB.indep.fundCct_circuit; rwa [hB.cl_eq]

lemma Dep.exists_circuit_subset (hX : M.Dep X) : ∃ C, C ⊆ X ∧ M.Circuit C := by
  rw [dep_iff, indep_iff_not_mem_cl_diff_forall] at hX; push_neg at hX
  obtain ⟨⟨e, he, heX⟩, hXE⟩ := hX
  -- Why doesn't `aesop_mat` work on the next line?
  obtain ⟨I, hI⟩ := M.exists_basis (X \ {e}) (diff_subset.trans hXE)
  rw [← hI.cl_eq_cl] at heX
  exact ⟨_, (fundCct_subset_insert e I).trans
    (insert_subset he (hI.subset.trans diff_subset)),
    hI.indep.fundCct_circuit ⟨heX, not_mem_subset hI.subset (not_mem_diff_of_mem rfl)⟩⟩

lemma dep_iff_superset_circuit (hX : X ⊆ M.E := by aesop_mat) :
    M.Dep X ↔ ∃ C, C ⊆ X ∧ M.Circuit C :=
  ⟨Dep.exists_circuit_subset, fun ⟨C, hCX, hC⟩ ↦ hC.dep.superset hCX⟩

lemma dep_iff_superset_circuit' : M.Dep X ↔ (∃ C, C ⊆ X ∧ M.Circuit C) ∧ X ⊆ M.E :=
  ⟨fun h ↦ ⟨h.exists_circuit_subset, h.subset_ground⟩, fun ⟨⟨C, hCX, hC⟩, h⟩ ↦ hC.dep.superset hCX⟩

lemma indep_iff_forall_subset_not_circuit' :
    M.Indep I ↔ (∀ C, C ⊆ I → ¬M.Circuit C) ∧ I ⊆ M.E := by
  simp_rw [indep_iff_not_dep, dep_iff_superset_circuit', not_and, imp_not_comm (b := _ ⊆ _)]; aesop

lemma indep_iff_forall_subset_not_circuit (hI : I ⊆ M.E := by aesop_mat) :
    M.Indep I ↔ ∀ C, C ⊆ I → ¬M.Circuit C := by
  rw [indep_iff_forall_subset_not_circuit', and_iff_left hI]

lemma mem_cl_iff_mem_or_exists_circuit (hX : X ⊆ M.E := by aesop_mat) :
    e ∈ M.cl X ↔ e ∈ X ∨ ∃ C, M.Circuit C ∧ e ∈ C ∧ C ⊆ insert e X := by
  refine' (em (e ∈ X)).elim (fun he ↦ iff_of_true (M.mem_cl_of_mem he) (Or.inl he)) (fun he ↦ _)
  rw [or_iff_right he]
  refine' ⟨fun h ↦ _, fun ⟨C, hC, heC, hCX⟩ ↦ _⟩
  · obtain ⟨I, hI⟩ := M.exists_basis X
    rw [← hI.cl_eq_cl] at h
    exact ⟨M.fundCct e I, hI.indep.fundCct_circuit ⟨h, not_mem_subset hI.subset he⟩,
      M.mem_fundCct e I, (fundCct_subset_insert _ _).trans (insert_subset_insert hI.subset)⟩
  refine' ((hC.subset_cl_diff_singleton e).trans (M.cl_subset_cl _)) heC
  rwa [diff_subset_iff, singleton_union]

lemma mem_cl_iff_exists_circuit_of_not_mem (he : e ∉ X) :
    e ∈ M.cl X ↔ ∃ C, M.Circuit C ∧ e ∈ C ∧ C ⊆ insert e X := by
  rw [← cl_inter_ground, mem_cl_iff_mem_or_exists_circuit, mem_inter_iff, iff_false_intro he,
    false_and_iff, false_or_iff]
  refine' ⟨
    fun ⟨C, hC, heC, h⟩ ↦ ⟨C, hC, heC, h.trans ((insert_subset_insert inter_subset_left))⟩,
    fun ⟨C, hC, heC, h⟩ ↦ ⟨C, hC, heC, (subset_inter h hC.subset_ground).trans _⟩⟩
  rw [insert_inter_of_mem (hC.subset_ground heC)]

/-- A generalization of the strong circuit elimination axiom. For finite matroids, this is
  equivalent to the case where `ι` is a singleton type, which is the usual two-circuit version.
  The stronger version is required for axiomatizing infinite matroids via circuits.

  TODO : The same fact should hold if there is no `z` chosen. This is not
    completely straightforward, since the proof really uses `z`, and the
    statement is not trivial if there is no choice available for `z`. The
    quickest proof probably uses closure.    -/
lemma Circuit.strong_multi_elimination {ι : Type*} (hC : M.Circuit C) (x : ι → α)
    (Cs : ι → Set α) (hCs : ∀ i, M.Circuit (Cs i)) (h_mem : ∀ i, x i ∈ C ∩ Cs i)
    (h_unique : ∀ i i', x i ∈ Cs i' → i = i') {z : α} (hz : z ∈ C \ ⋃ i, Cs i) :
    ∃ C', M.Circuit C' ∧ z ∈ C' ∧ C' ⊆ (C ∪ ⋃ i, Cs i) \ range x := by
  set Y := (C ∪ ⋃ x, Cs x) \ insert z (range x) with hY
  have hYE : Y ⊆ M.E := by
    refine' diff_subset.trans (union_subset hC.subset_ground _)
    exact iUnion_subset fun i ↦ (hCs i).subset_ground
  have h₁ : range x ⊆ M.cl (⋃ i, (Cs i \ {x i}) \ insert z (range x)) := by
    rintro e ⟨i, rfl⟩
    have h' := (hCs i).subset_cl_diff_singleton (x i) (h_mem i).2
    refine' mem_of_mem_of_subset h' (M.cl_subset_cl _)
    refine' subset_iUnion_of_subset i (subset_diff.mpr ⟨rfl.subset, _⟩)
    rw [disjoint_iff_forall_ne]
    rintro y hy z (rfl | ⟨j, rfl⟩) rfl
    · exact hz.2 (mem_iUnion_of_mem i hy.1)
    refine' hy.2 (mem_singleton_iff.mpr _)
    rw [h_unique _ _ hy.1]
  have h₂ : range x ⊆ M.cl Y := by
    refine' h₁.trans (M.cl_subset_cl (iUnion_subset fun x ↦ _))
    refine' diff_subset_diff_left (subset_union_of_subset_right _ _)
    exact subset_iUnion_of_subset x diff_subset
  have h₃ : C \ {z} ⊆ M.cl Y := by
    suffices C \ {z} ⊆ C \ insert z (range x) ∪ range x by
      rw [union_diff_distrib] at hY
      convert this.trans (union_subset_union (subset_union_left.trans_eq hY.symm) h₂) using 1
      rw [union_eq_right.mpr]
      exact M.subset_cl Y
    rw [← union_singleton, ← diff_diff, diff_subset_iff, singleton_union, ← insert_union,
      insert_diff_singleton, ← singleton_union, union_assoc, diff_union_self]
    exact subset_union_of_subset_right subset_union_left _
  rw [← M.cl_subset_cl_iff_subset_cl (diff_subset.trans hC.subset_ground)] at h₃
  have h₄ := h₃ (hC.subset_cl_diff_singleton z hz.1)
  obtain (hzY | ⟨C', hC', hzC', hCzY⟩) := (mem_cl_iff_mem_or_exists_circuit hYE).mp h₄
  · exact ((hY.subset hzY).2 (mem_insert z _)).elim
  refine' ⟨C', hC', hzC', subset_diff.mpr ⟨_, _⟩⟩
  · exact hCzY.trans (insert_subset (Or.inl hz.1) diff_subset)
  refine' disjoint_of_subset_left hCzY _
  rw [← singleton_union, disjoint_union_left, disjoint_singleton_left]
  refine' ⟨not_mem_subset _ hz.2, _⟩
  · rintro x' ⟨i, rfl⟩; exact mem_iUnion_of_mem i (h_mem i).2
  exact disjoint_of_subset_right (subset_insert z _) disjoint_sdiff_left

/-- The strong circuit elimination axiom. For any two circuits `C₁,C₂` and all `e ∈ C₁ ∩ C₂` and
  `f ∈ C₁ \ C₂`, there is a circuit `C` with `f ∈ C ⊆ (C₁ ∪ C₂) \ {e}`. -/
lemma Circuit.strong_elimination (hC₁ : M.Circuit C₁) (hC₂ : M.Circuit C₂) (he : e ∈ C₁ ∩ C₂)
    (hf : f ∈ C₁ \ C₂) : ∃ C, M.Circuit C ∧ C ⊆ (C₁ ∪ C₂) \ {e} ∧ f ∈ C := by
  obtain ⟨C, hC, hfC, hCss⟩ :=
    @Circuit.strong_multi_elimination _ M C₁ Unit hC₁ (fun _ ↦ e) (fun _ ↦ C₂) (by simpa)
      (by simpa) (by simp) f (by simpa)
  simp only [range_const, iUnion_const] at hCss
  exact ⟨C, hC, hCss, hfC⟩

/-- The circuit elimination axiom : for any pair of distinct circuits `C₁,C₂` and any `e`, some
  circuit is contained in `C₁ ∪ C₂ \ {e}`. Traditionally this is stated with the assumption that
  `e ∈ C₁ ∩ C₂`, but it is also true without it. --/
lemma Circuit.elimination (hC₁ : M.Circuit C₁) (hC₂ : M.Circuit C₂) (h : C₁ ≠ C₂) (e : α) :
    ∃ C, M.Circuit C ∧ C ⊆ (C₁ ∪ C₂) \ {e} := by
  have hne : (C₁ \ C₂).Nonempty := by
    rw [nonempty_iff_ne_empty, Ne, diff_eq_empty]
    -- simp_rw [nonempty_iff_ne_empty]
    exact fun hss ↦ h (hC₁.eq_of_subset_circuit hC₂ hss)
  obtain (he₁ | he₁) := em (e ∈ C₁)
  · obtain (he₂ | he₂) := em (e ∈ C₂)
    · obtain ⟨C, h⟩ :=  hC₁.strong_elimination hC₂ ⟨he₁,he₂⟩ hne.some_mem
      exact ⟨C, h.1, h.2.1⟩
    exact ⟨C₂, hC₂, subset_diff_singleton subset_union_right he₂⟩
  exact ⟨C₁, hC₁, subset_diff_singleton subset_union_left he₁⟩

lemma Circuit.eq_fundCct_of_subset_insert_indep (hC : M.Circuit C) (hI : M.Indep I)
    (hCI : C ⊆ insert e I) : C = M.fundCct e I := by
  have heI : e ∉ I := by
    intro heI; rw [insert_eq_of_mem heI] at hCI; exact (hC.dep.superset hCI).not_indep hI
  have heC : e ∈ C := by
    refine' by_contra fun heC ↦ (hI.subset _).not_dep hC.dep
    rwa [← singleton_union, ← diff_subset_iff, diff_singleton_eq_self heC] at hCI
  have he : e ∈ M.cl I := by
    rw [mem_cl_iff_exists_circuit_of_not_mem heI]; exact ⟨C, hC, heC, hCI⟩
  by_contra! hne
  obtain ⟨Cf, hCf, hCfss⟩ := hC.elimination (hI.fundCct_circuit ⟨he,heI⟩) hne e
  refine' hCf.dep.not_indep (hI.subset (hCfss.trans _))
  rw [diff_subset_iff, singleton_union, union_subset_iff, and_iff_right hCI]
  exact fundCct_subset_insert _ _

lemma eq_of_circuit_iff_circuit_forall {M₁ M₂ : Matroid α} (hE : M₁.E = M₂.E)
    (h : ∀ C, C ⊆ M₁.E → (M₁.Circuit C ↔ M₂.Circuit C)) : M₁ = M₂ := by
  have h' : ∀ C, M₁.Circuit C ↔ M₂.Circuit C := by
    exact fun C ↦ (em (C ⊆ M₁.E)).elim (h C)
      (fun hC ↦ iff_of_false (mt Circuit.subset_ground hC)
        (mt Circuit.subset_ground (fun hss ↦ hC (hss.trans_eq hE.symm))))
  refine' eq_of_indep_iff_indep_forall hE fun I hI ↦ _
  simp_rw [indep_iff_forall_subset_not_circuit hI, h',
    indep_iff_forall_subset_not_circuit (hI.trans_eq hE)]

section Dual

variable {B : Set α}

/-- A cocircuit is a circuit of the dual matroid, or equivalently the complement of a hyperplane -/
abbrev Cocircuit (M : Matroid α) (K : Set α) : Prop := M✶.Circuit K

lemma cocircuit_def : M.Cocircuit K ↔ M✶.Circuit K := Iff.rfl

lemma Cocircuit.circuit (hK : M.Cocircuit K) : M✶.Circuit K :=
  hK

lemma Circuit.cocircuit (hC : M.Circuit C) : M✶.Cocircuit C := by
  rwa [cocircuit_def, dual_dual]

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma Cocircuit.subset_ground (hC : M.Cocircuit C) : C ⊆ M.E :=
  hC.circuit.subset_ground

lemma coindep_iff_forall_subset_not_cocircuit :
    M.Coindep X ↔ (∀ K, K ⊆ X → ¬M.Cocircuit K) ∧ X ⊆ M.E :=
  indep_iff_forall_subset_not_circuit'

lemma cocircuit_iff_mem_minimals :
    M.Cocircuit K ↔ K ∈ minimals (· ⊆ ·) {X | ∀ B, M.Base B → (X ∩ B).Nonempty} := by
  revert K
  simp_rw [cocircuit_def, circuit_def, ← Set.ext_iff, dep_iff, ← coindep_def, dual_ground,
    coindep_iff_exists', not_and, imp_not_comm (b := (_ ⊆ _)), not_exists, not_and, subset_diff,
    not_and, not_disjoint_iff_nonempty_inter]
  apply (minimals_eq_minimals_of_subset_of_forall _ _).symm
  · exact fun K ⟨hK1, hK2⟩ B hB ↦ by rw [inter_comm]; exact hK1 hK2 B hB hB.subset_ground
  refine' fun K hK ↦ ⟨K ∩ M.E, _, inter_subset_left⟩
  simp only [mem_setOf_eq, inter_subset_right, forall_true_left, and_true]
  rintro B hB hBE
  rw [inter_comm, inter_assoc, inter_eq_self_of_subset_right hBE]
  exact hK B hB

lemma cocircuit_iff_mem_minimals_compl_nonspanning :
    M.Cocircuit K ↔ K ∈ minimals (· ⊆ ·) {X | ¬M.Spanning (M.E \ X)} := by
  convert cocircuit_iff_mem_minimals with K
  simp_rw [spanning_iff_superset_base (S := M.E \ K), not_exists, subset_diff, not_and,
    not_disjoint_iff_nonempty_inter, ← and_imp, and_iff_left_of_imp Base.subset_ground,
      inter_comm K]

lemma Circuit.cocircuit_disjoint_or_nontrivial_inter (hC : M.Circuit C) (hK : M.Cocircuit K) :
    Disjoint C K ∨ (C ∩ K).Nontrivial := by
  simp_rw [or_iff_not_imp_left, not_disjoint_iff]
  rintro ⟨e, heC, heK⟩
  simp_rw [nontrivial_iff_ne_singleton <| show e ∈ C ∩ K from ⟨heC, heK⟩]
  intro he
  simp_rw [cocircuit_iff_mem_minimals_compl_nonspanning, mem_minimals_iff_forall_ssubset_not_mem,
    mem_setOf, not_not] at hK
  have' hKe := hK.2 (y := K \ {e}) (diff_singleton_sSubset.2 (he.symm.subset rfl).2)
  apply hK.1
  rw [spanning_iff_ground_subset_cl]; nth_rw 1 [← hKe.cl_eq, diff_diff_eq_sdiff_union]
  · refine (M.cl_subset_cl (subset_union_left (t := C))).trans ?_
    rw [union_assoc, singleton_union, insert_eq_of_mem heC, ← cl_union_cl_right_eq,
      ← hC.cl_diff_singleton_eq_cl e, cl_union_cl_right_eq, union_eq_self_of_subset_right]
    rw [← he, diff_self_inter]
    exact diff_subset_diff_left hC.subset_ground
  rw [← he]; exact inter_subset_left.trans hC.subset_ground

lemma Circuit.cocircuit_inter_nontrivial (hC : M.Circuit C) (hK : M.Cocircuit K)
    (hCK : (C ∩ K).Nonempty) : (C ∩ K).Nontrivial := by
  simpa [or_iff_not_imp_left, not_disjoint_iff_nonempty_inter, imp_iff_right hCK] using
    hC.cocircuit_disjoint_or_nontrivial_inter hK

lemma dual_rkPos_iff_exists_circuit : M✶.RkPos ↔ ∃ C, M.Circuit C := by
  rw [rkPos_iff_empty_not_base, dual_base_iff, diff_empty, not_iff_comm, not_exists,
    ← ground_indep_iff_base, indep_iff_forall_subset_not_circuit]
  exact ⟨fun h C _ ↦ h C, fun h C hC ↦ h C hC.subset_ground hC⟩

lemma Circuit.dual_rkPos (hC : M.Circuit C) : M✶.RkPos :=
  dual_rkPos_iff_exists_circuit.mpr ⟨C, hC⟩

lemma exists_circuit [RkPos M✶] : ∃ C, M.Circuit C :=
  dual_rkPos_iff_exists_circuit.1 (by assumption)

lemma rk_Pos_iff_exists_cocircuit : M.RkPos ↔ ∃ K, M.Cocircuit K := by
  rw [← dual_dual M, dual_rkPos_iff_exists_circuit, dual_dual M]

/-- The fundamental cocircuit for `B`. Should be used when `B` is a base and `e ∈ B`. -/
def fundCocct (e : α) (B : Set α) := M✶.fundCct e (M✶.E \ B)

lemma fundCocct_cocircuit (he : e ∈ B) (hB : M.Base B) : M.Cocircuit <| M.fundCocct e B := by
  apply hB.compl_base_dual.indep.fundCct_circuit
  simp only [mem_diff, he, not_true_eq_false, and_false, not_false_eq_true, and_true]
  rw [hB.compl_base_dual.cl_eq, dual_ground]
  exact hB.subset_ground he

lemma mem_fundCocct (M : Matroid α) (e : α) (B : Set α) : e ∈ M.fundCocct e B :=
  mem_insert _ _

lemma fundCocct_subset_insert_compl (M : Matroid α) (e : α) (B : Set α) :
    M.fundCocct e B ⊆ insert e (M.E \ B) :=
  fundCct_subset_insert _ _

lemma fundCocct_inter_eq (M : Matroid α) {B : Set α} (he : e ∈ B) :
    (M.fundCocct e B) ∩ B = {e} := by
  refine subset_antisymm ?_ (singleton_subset_iff.2 ⟨M.mem_fundCocct _ _, he⟩)
  refine (inter_subset_inter_left _ (M.fundCocct_subset_insert_compl _ _)).trans ?_
  simp (config := {contextual := true})

lemma Indep.exists_cocircuit_inter_eq_mem (hI : M.Indep I) (heI : e ∈ I) :
    ∃ K, M.Cocircuit K ∧ K ∩ I = {e} := by
  obtain ⟨B, hB, hIB⟩ := hI.exists_base_superset
  refine ⟨M.fundCocct e B, fundCocct_cocircuit (hIB heI) hB, ?_⟩
  rw [subset_antisymm_iff, subset_inter_iff, singleton_subset_iff, and_iff_right
    (mem_fundCocct _ _ _), singleton_subset_iff, and_iff_left heI, ← M.fundCocct_inter_eq (hIB heI)]
  exact inter_subset_inter_right _ hIB

end Dual

section Finitary

lemma Circuit.finite [Finitary M] (hC : M.Circuit C) : C.Finite := by
  have hi := hC.dep.not_indep
  rw [indep_iff_forall_finite_subset_indep] at hi; push_neg at hi
  obtain ⟨J, hJC, hJfin, hJ⟩ := hi
  rwa [← hC.eq_of_not_indep_subset hJ hJC]

lemma finitary_iff_forall_circuit_finite : M.Finitary ↔ ∀ C, M.Circuit C → C.Finite := by
  refine ⟨fun _ _ ↦ Circuit.finite, fun h ↦
    ⟨fun I hI ↦ indep_iff_not_dep.2 ⟨fun hd ↦ ?_,fun x hx ↦ ?_⟩⟩ ⟩
  · obtain ⟨C, hCI, hC⟩ := hd.exists_circuit_subset
    exact hC.dep.not_indep <| hI _ hCI (h C hC)
  simpa using (hI {x} (by simpa) (finite_singleton _)).subset_ground

lemma Cocircuit.finite [Finitary (M✶)] (hK : M.Cocircuit K) : K.Finite :=
  Circuit.finite hK

end Finitary
section Girth

variable {k : ℕ∞}

/-- The `girth` of `M` is the cardinality of the smallest circuit of `M`, or `⊤` if none exists.-/
noncomputable def girth (M : Matroid α) : ℕ∞ := ⨅ C ∈ {C | M.Circuit C}, C.encard

lemma one_le_girth (M : Matroid α) : 1 ≤ M.girth := by
  simp_rw [girth, le_iInf_iff, one_le_encard_iff_nonempty]; exact fun _ ↦ Circuit.nonempty

lemma Circuit.girth_le_card (hC : M.Circuit C) : M.girth ≤ C.encard := by
  simp only [girth, mem_setOf_eq, iInf_le_iff, le_iInf_iff]
  exact fun b hb ↦ hb C hC

lemma girth_eq_top_iff : M.girth = ⊤ ↔ ∀ C, M.Circuit C → C.Infinite := by
  simp [girth, sInf_eq_top]

lemma le_girth_iff : k ≤ M.girth ↔ ∀ C, M.Circuit C → k ≤ C.encard := by
  simp [girth, le_sInf_iff]

lemma exists_circuit_girth (M : Matroid α) [RkPos M✶] :
    ∃ C, M.Circuit C ∧ C.encard = M.girth := by
  obtain ⟨⟨C,hC⟩, (hC' : C.encard = _)⟩ :=
    @ciInf_mem ℕ∞ (setOf M.Circuit) _ _ (nonempty_coe_sort.mpr M.exists_circuit)
      (fun C ↦ (C : Set α).encard)
  exact ⟨C, hC, by rw [hC', girth, iInf_subtype']⟩

lemma girth_le_iff (M : Matroid α) [RkPos M✶] : M.girth ≤ k ↔ ∃ C, M.Circuit C ∧ C.encard ≤ k :=
  let ⟨C, hC⟩ := M.exists_circuit_girth
  ⟨fun h ↦ ⟨C, hC.1, hC.2.le.trans h⟩, fun ⟨_, hC, hCc⟩ ↦ (hC.girth_le_card).trans hCc⟩

lemma girth_lt_iff (M : Matroid α) : M.girth < k ↔ ∃ C, M.Circuit C ∧ C.encard < k := by
  simp_rw [girth, iInf_lt_iff, mem_setOf_eq, bex_def]

lemma indep_of_card_lt_girth (hI : I.encard < M.girth) (hIE : I ⊆ M.E := by aesop_mat) :
    M.Indep I := by
  rw [indep_iff_forall_subset_not_circuit]
  exact fun C hCI hC ↦ ((hC.girth_le_card.trans (encard_mono hCI)).trans_lt hI).ne rfl

@[simp] lemma girth_eq_top_iff_ground_indep [Finitary M] : M.girth = ⊤ ↔ M.Indep M.E := by
  rw [girth_eq_top_iff, indep_iff_forall_subset_not_circuit]
  exact ⟨fun h C _ hC ↦ h C hC hC.finite, fun h C hC _ ↦ h C hC.subset_ground hC⟩

end Girth
section BasisExchange

variable {I₁ I₂ B₁ B₂ : Set α}

lemma Indep.rev_exchange_indep_iff (hI : M.Indep I) (he : e ∈ M.cl I \ I) :
    M.Indep (insert e I \ {f}) ↔ f ∈ M.fundCct e I := by
  simp_rw [indep_iff_forall_subset_not_circuit', and_iff_left (diff_subset.trans
    (insert_subset ((M.cl_subset_ground I) he.1) hI.subset_ground)), imp_not_comm, subset_diff,
    disjoint_singleton_right, not_and, not_not]
  exact ⟨fun h ↦ h _ (hI.fundCct_circuit he) (fundCct_subset_insert _ _),
    fun h C hC hCeI ↦ by rwa [hC.eq_fundCct_of_subset_insert_indep hI hCeI]⟩

/- Given two bases `B₁,B₂` of `M` and an element `e` of `B₁ \ B₂`, we can find an `f ∈ B₂ \ B₁`
  so that swapping `e` for `f` in yields bases in both `B₁` and `B₂`.  -/
lemma Base.strong_exchange (hB₁ : M.Base B₁) (hB₂ : M.Base B₂) (he : e ∈ B₁ \ B₂) :
    ∃ f ∈ B₂ \ B₁, M.Base (insert e B₂ \ {f}) ∧ M.Base (insert f B₁ \ {e}) := by
  suffices h1 : (∃ f, f ∈ B₂ \ B₁ ∧  M.Indep (insert e B₂ \ {f}) ∧ M.Indep (insert f B₁ \ {e})) by
    obtain ⟨f, hf, h₁, h₂⟩ := h1;
    exact ⟨f, hf, hB₂.exchange_base_of_indep' hf.1 he.2 h₁,
      hB₁.exchange_base_of_indep' he.1 hf.2 h₂⟩
  have he₁ : e ∈ M.cl B₂ \ B₂ := by
    rw [hB₂.cl_eq]; exact ⟨hB₁.subset_ground he.1, he.2⟩
  simp_rw [hB₂.indep.rev_exchange_indep_iff he₁]
  by_contra! h

  have hC := hB₂.indep.fundCct_circuit he₁
  have hCss : M.fundCct e B₂ \ {e} ⊆ B₂ := by
    rw [diff_subset_iff, singleton_union]; exact fundCct_subset_insert _ _

  have hcl : M.fundCct e B₂ ⊆ M.cl (B₁ \ {e}) := by
    refine' (hC.subset_cl_diff_singleton e).trans (cl_subset_cl_of_subset_cl (fun f hf ↦ _))
    have hef : f ≠ e := by rintro rfl; exact hf.2 rfl
    rw [(hB₁.indep.diff {e}).mem_cl_iff, dep_iff, insert_subset_iff,
      and_iff_left (diff_subset.trans hB₁.subset_ground), or_iff_not_imp_right, mem_diff,
      and_iff_left (hC.subset_ground hf.1), mem_singleton_iff,
      and_iff_left hef, insert_diff_singleton_comm hef]
    exact fun hfB₁ ↦ h _ ⟨hCss hf,hfB₁⟩ (diff_subset hf)

  exact hB₁.indep.not_mem_cl_diff_of_mem he.1 (hcl (mem_fundCct _ _ _))

/- Given two bases `I₁,I₂` of `X` and an element `e` of `I₁ \ I₂`, we can find an `f ∈ I₂ \ I₁`
  so that swapping `e` for `f` in yields bases for `X` in both `I₁` and `I₂`.  -/
lemma Basis.strong_exchange (hI₁ : M.Basis I₁ X) (hI₂ : M.Basis I₂ X) (he : e ∈ I₁ \ I₂) :
    ∃ f ∈ I₂ \ I₁, M.Basis (insert e I₂ \ {f}) X ∧ M.Basis (insert f I₁ \ {e}) X := by
  obtain ⟨f, hf, h₁, h₂⟩ := hI₁.base_restrict.strong_exchange hI₂.base_restrict he
  rw [base_restrict_iff] at h₁ h₂
  exact ⟨f, hf, h₁, h₂⟩

lemma Base.rev_exchange (hB₁ : M.Base B₁) (hB₂ : M.Base B₂) (he : e ∈ B₁ \ B₂) :
    ∃ f ∈ B₂ \ B₁, M.Base (insert e B₂ \ {f}) :=
  (hB₁.strong_exchange hB₂ he).imp fun _ ⟨hf, h, _⟩ ↦ ⟨hf, h⟩

lemma Basis.rev_exchange (hI₁ : M.Basis I₁ X) (hI₂ : M.Basis I₂ X) (he : e ∈ I₁ \ I₂) :
    ∃ f ∈ I₂ \ I₁, M.Basis (insert e I₂ \ {f}) X :=
  (hI₁.strong_exchange hI₂ he).imp
    (by simp only [mem_diff, mem_insert_iff, mem_singleton_iff]; tauto)

end BasisExchange
section Iso

variable {β : Type*} {N : Matroid β}

lemma Iso.circuit_image (e : M ≂ N) {C : Set M.E} (hC : M.Circuit C) : N.Circuit ↑(e '' C) := by
  simp_rw [circuit_iff, ← e.dep_image_iff, and_iff_right hC.dep]
  intro I hI hIC
  obtain ⟨I,rfl⟩ := Subset.eq_image_val hI.subset_ground
  replace hC := hC.eq_of_dep_subset (e.symm.image_dep hI)
  simp only [image_subset_iff, preimage_val_image_val_eq_self, image_symm_eq_preimage,
    preimage_subset_iff, image_val_inj] at hIC hC
  simp [← hC hIC]

def Iso.ofForallCircuit (e : M.E ≃ N.E) (h : ∀ (C : Set M.E), M.Circuit ↑C ↔ N.Circuit ↑(e '' C)) :
    M ≂ N := Iso.ofForallDep e (fun D ↦ by
    rw [dep_iff_superset_circuit, dep_iff_superset_circuit]
    refine ⟨fun ⟨C, hCD, hC⟩ ↦ ?_, fun ⟨C, hCD, hC⟩ ↦ ?_⟩
    · obtain ⟨C, rfl⟩ := Subset.eq_image_val hC.subset_ground
      refine ⟨_, ?_, (h _).1 hC⟩
      rw [image_subset_image_iff Subtype.val_injective] at hCD ⊢
      rwa [Equiv.image_subset e]
    obtain ⟨C, rfl⟩ := Subset.eq_image_val hC.subset_ground
    exact ⟨↑(e.symm '' C), by simpa [Set.preimage_val_image_val_eq_self] using hCD,
      by rw [h]; simpa⟩ )

end Iso

section constructions

variable {E D : Set α}

@[simp] lemma uniqueBaseOn_dep_iff : (uniqueBaseOn I E).Dep D ↔ D.Nonempty ∧ ¬ (D ⊆ I) ∧ D ⊆ E := by
  by_cases hD : D ⊆ E
  · simp (config := {contextual := true}) [← not_indep_iff (M := uniqueBaseOn I E) hD, hD,
      nonempty_iff_ne_empty, not_imp_not]
  exact iff_of_false (fun h ↦ hD h.subset_ground) (by simp [hD])

@[simp] lemma loopyOn_dep_iff : (loopyOn E).Dep D ↔ D.Nonempty ∧ D ⊆ E := by
  simp [Dep, nonempty_iff_ne_empty]

@[simp] lemma uniqueBaseOn_circuit_iff : (uniqueBaseOn I E).Circuit C ↔ ∃ e ∈ E \ I, C = {e} := by
  simp only [circuit_iff_dep_forall_diff_singleton_indep, uniqueBaseOn_dep_iff,
    uniqueBaseOn_indep_iff', subset_inter_iff, diff_singleton_subset_iff, mem_diff]
  refine ⟨fun ⟨⟨⟨e,he⟩, hCI, hCE⟩, h2⟩ ↦ ⟨e, ⟨hCE he, fun heI ↦ hCI ?_⟩, ?_⟩, ?_⟩
  · exact (h2 e he).1.trans (insert_subset heI Subset.rfl)
  · suffices hsub : C.Subsingleton from hsub.eq_singleton_of_mem he
    refine fun f hf f' hf' ↦ by_contra fun hne ↦ hCI ?_
    simpa [inter_insert_eq hne] using subset_inter (h2 f hf).1 (h2 f' hf').1
  rintro ⟨e, ⟨heI,heC⟩, rfl⟩
  simp [heI, heC]

@[simp] lemma loopyOn_circuit_iff {E : Set α} : (loopyOn E).Circuit C ↔ ∃ e ∈ E, C = {e} := by
  simp [← uniqueBaseOn_empty]

@[simp] lemma freeOn_not_circuit {E : Set α} : ¬ (freeOn E).Circuit C := by
  simp [← uniqueBaseOn_self]

@[simp] lemma emptyOn_not_circuit : ¬ (emptyOn α).Circuit C := by
  simp [← freeOn_empty]

@[simp] lemma girth_emptyOn : girth (emptyOn α) = ⊤ := by
  simp [girth]

@[simp] lemma girth_freeOn : girth (freeOn E) = ⊤ := by
  simp [Subset.rfl]

lemma girth_loopyOn (hE : E.Nonempty) : girth (loopyOn E) = 1 := by
  have _ : RkPos (loopyOn E)✶ := by rw [loopyOn_dual_eq]; exact freeOn_rkPos hE
  refine le_antisymm ?_ (one_le_girth _)
  simp only [girth_le_iff, loopyOn_circuit_iff]
  exact ⟨{hE.some}, ⟨_, hE.some_mem, rfl⟩, by simp⟩


end constructions
section Equiv

-- variable {β : Type*} {N : Matroid β}

-- /-- A `PartialEquiv` that maps circuits to and from circuits is a matroid isomorphism. -/
-- def iso_of_forall_circuit' (e : PartialEquiv α β) (hM : e.source = M.E) (hN : e.target = N.E)
--     (on_circuit : ∀ C, M.Circuit C → N.Circuit (e '' C))
--     (on_circuit_symm : ∀ C, N.Circuit C → M.Circuit (e.symm '' C)) : Iso M N := by
--   apply iso_of_forall_indep e hM hN _ _
--   · intro I
--     rw [indep_iff_forall_subset_not_circuit', indep_iff_forall_subset_not_circuit']
--     rintro ⟨no_circ, sub_ground⟩
--     constructor
--     · intro C C_sub_eI C_circ
--       apply no_circ _ _ (on_circuit_symm C C_circ)
--       rintro i ⟨c, c_C, ec_eq_i⟩
--       obtain ⟨i', i'_I, e_i'⟩ := C_sub_eI c_C
--       rw [← e_i', e.left_inv] at ec_eq_i
--       rwa [← ec_eq_i]
--       rw [hM]
--       exact sub_ground i'_I
--     · rintro i ⟨c, c_I, c_eq⟩
--       rw [← c_eq, ← hN]
--       rw [← hM] at sub_ground
--       exact e.map_source' (sub_ground c_I)
--   · intro I
--     rw [indep_iff_forall_subset_not_circuit', indep_iff_forall_subset_not_circuit']
--     rintro ⟨no_circ, sub_ground⟩
--     constructor
--     · intro C C_sub_eI C_circ
--       apply no_circ _ _ (on_circuit C C_circ)
--       rintro i ⟨c, c_C, ec_eq_i⟩
--       obtain ⟨i', i'_I, e_i'⟩ := C_sub_eI c_C
--       rw [← e_i', e.right_inv] at ec_eq_i
--       rwa [← ec_eq_i]
--       rw [hN]
--       exact sub_ground i'_I
--     · rintro i ⟨c, c_I, c_eq⟩
--       rw [← c_eq, ← hM]
--       rw [← hN] at sub_ground
--       exact e.map_target' (sub_ground c_I)
-- end Equiv

-- end Matroid


-- end BasisExchange

-- -- section from_axioms TODO : Fix this for `matroid_in`.
-- -- /-- A collection of sets satisfying the circuit axioms determines a matroid_in -/
-- -- def matroid_in_of_circuit_of_finite [finite E] (circuit : set α → Prop)
-- -- (empty_not_circuit : ¬ circuit ∅) (antichain : ∀ C₁ C₂, circuit C₁ → circuit C₂ → C₁ ⊆ C₂ → C₁ = C₂)
-- -- (elimination : ∀ C₁ C₂ e,
-- --     circuit C₁ → circuit C₂ → C₁ ≠ C₂ → e ∈ C₁ ∩ C₂ → ∃ C ⊆ (C₁ ∪ C₂) \ {e}, circuit C) :
-- -- matroid_in α :=
-- -- matroid_in_of_indep_of_finite (λ I, ∀ C ⊆ I, ¬circuit C) ⟨∅, λ C hC, (by rwa subset_empty_iff.mp hC)⟩
-- -- (λ I J hIJ hJ C hCI, hIJ C (hCI.trans hJ))
-- -- begin
-- --   by_contra! h,
-- --   obtain ⟨I,J,hI,hJ,hIJ,Hbad⟩ := h,
-- --   set indep := (λ I, ∀ C ⊆ I, ¬circuit C) with hi,
-- --   /- Choose an independent set `K ⊆ I ∪ J`, larger than `I`, for which `I \ K` is minimized -/
-- --   set sbad := {K : set α | indep K ∧ K ⊆ I ∪ J ∧ I.ncard < K.ncard} with hsbad,
-- --   have hbad_ne : sbad.nonempty := ⟨J, hJ, subset_union_right, hIJ⟩,
-- --   obtain ⟨K, ⟨hK, hKIJ, hIK⟩, hKmin⟩ :=
-- --     @set.finite.exists_minimal_wrt (set α) _ _ (λ X, (I \ X).ncard) sbad (to_finite sbad) hbad_ne,
-- --   simp only [hsbad, mem_set_of_eq, and_imp] at hKmin,
-- --   obtain hIK_empty | ⟨e, heI, heK⟩ := (I \ K).eq_empty_or_nonempty,
-- --   /- If `I \ K` is empty then we get an easy contradiction by augmenting `I` into `K`. -/
-- --   { obtain ⟨e,heK,heI⟩ := exists_mem_not_mem_of_ncard_lt_ncard hIK,
-- --     have heJ : e ∈ J := by_contra (λ heJ, not_or heI heJ (hKIJ heK)),
-- --     obtain ⟨C, hCeI, hC⟩ := Hbad e heJ heI,
-- --     exact hK C (hCeI.trans (insert_subset.mpr ⟨heK, diff_eq_empty.mp hIK_empty⟩)) hC},
-- --   have hCf : ∀ f ∈ K \ I, ∃ Cf ⊆ (insert e K), circuit Cf ∧ f ∉ Cf ∧ e ∈ Cf,
-- --   { rintro f ⟨hfK,hfI⟩,
-- --     have hef : e ≠ f, from λ h, hfI (h ▸heI ),
-- --     set T := ((insert e K) \ {f}) with hT,
-- --     have hTIJ : T ⊆ I ∪ J, from
-- --       (diff_subset.trans (insert_subset.mpr ⟨or.inl heI,hKIJ⟩)),
-- --     have hTcard : T.ncard = K.ncard, by rw [hT, ncard_exchange' heK hfK],
-- --     have hITcard : (I \ T).ncard < (I \ K).ncard,
-- --     { rw [nat.lt_iff_add_one_le, hT, ← insert_diff_singleton_comm hef, ← union_singleton, ← diff_diff,
-- --         ncard_diff_singleton_add_one ],
-- --       { convert rfl.le using 2,
-- --         rw [diff_eq_compl_inter, diff_eq_compl_inter, diff_eq_compl_inter, compl_inter,
-- --           inter_distrib_right, compl_compl, singleton_inter_eq_empty.mpr hfI, empty_union]},
-- --       exact ⟨heI,λ he', heK he'.1⟩},
-- --     have hTi : ¬indep T, from
-- --       λ hTi, hITcard.ne (hKmin _ hTi hTIJ (hIK.trans_eq hTcard.symm) hITcard.le).symm,
-- --     push_neg at hTi,
-- --     obtain ⟨Cf, hCfT, hCf⟩ := hTi,
-- --     refine ⟨Cf, hCfT.trans diff_subset, hCf, _, _⟩,
-- --     { exact mt (@hCfT f) (not_mem_diff_of_mem (mem_singleton f))},
-- --     refine by_contra (λ heCf, hK Cf (λ x hxCf, _) hCf),
-- --     exact mem_of_mem_insert_of_ne (hCfT hxCf).1 (by {rintro rfl, exact heCf hxCf})},
-- --   obtain ⟨g,hgK,hgI⟩ := exists_mem_not_mem_of_ncard_lt_ncard hIK,
-- --   obtain ⟨Cg, hCgss, hCg, hgCg, heCg⟩ := hCf g ⟨hgK,hgI⟩,
-- --   have hg_ex : ∃ g', g' ∈ Cg ∧ g' ∈ K \ I,
-- --   { by_contra! hg',
-- --     exact hI _ (λ x hx,
-- --       or.elim (hCgss hx) (λ h, h.symm ▸ heI) (λ hxK, by_contra (λ hxI, hg' _ hx ⟨hxK, hxI⟩))) hCg},
-- --   obtain ⟨g', hg', hg'KI⟩ := hg_ex,
-- --   obtain ⟨Cg', hCg'ss, hCg', hgCg', heCg'⟩ := hCf g' hg'KI,
-- --   have hne : Cg ≠ Cg',
-- --   { intro heq, rw ← heq at hgCg', exact hgCg' hg', },
-- --   obtain ⟨C, hCss, hC⟩ := elimination _ _ e hCg hCg' hne ⟨heCg, heCg'⟩,
-- --   refine hK C (hCss.trans _) hC,
-- --   rw [diff_subset_iff, singleton_union],
-- --   exact union_subset hCgss hCg'ss,
-- -- end
-- -- @[simp] lemma matroid_in_of_circuit_of_finite_apply [finite E] (circuit : set α → Prop)
-- --   (empty_not_circuit : ¬ circuit ∅)
-- --   (antichain : ∀ C₁ C₂, circuit C₁ → circuit C₂ → C₁ ⊆ C₂ → C₁ = C₂)
-- --   (elimination : ∀ C₁ C₂ e,
-- --     circuit C₁ → circuit C₂ → C₁ ≠ C₂ → e ∈ C₁ ∩ C₂ → ∃ C ⊆ (C₁ ∪ C₂) \ {e}, circuit C) :
-- --   (matroid_in_of_circuit_of_finite circuit empty_not_circuit antichain elimination).circuit = circuit :=
-- -- begin
-- --   ext C,
-- --   simp_rw [matroid_in_of_circuit_of_finite, matroid_in.circuit_iff_forall_ssubset,
-- --    matroid_in_of_indep_of_finite_apply,
-- -- not_forall, not_not, exists_prop],
-- --   refine ⟨λ h, _,λ h, ⟨⟨_,rfl.subset, h⟩,λ I hIC C' hC'I hC',
-- --     hIC.not_subset ((antichain C' C hC' h (hC'I.trans hIC.subset)) ▸ hC'I )⟩⟩,
-- --   obtain ⟨⟨C₀,hC₀C, hC₀⟩,hI⟩ := h,
-- --   obtain rfl | hC₀C := eq_or_ssubset_of_subset hC₀C,
-- --     assumption,
-- --   exact (hI _ hC₀C _ rfl.subset hC₀).elim,
-- -- end
-- -- end from_axioms
-- end Matroid
