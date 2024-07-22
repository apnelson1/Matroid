import Mathlib.Data.Matroid.Closure
import Mathlib.Data.Matroid.Map

open Set
namespace Matroid



variable {α ι : Type*} {M : Matroid α} {F I J X Y B C R : Set α} {e f x y : α}

-- Independence and Bases

-- lemma Flat.insert_indep_of_not_mem (hF : M.Flat F) (hI : M.Indep I) (hIF : I ⊆ F)
--     (he : e ∈ M.E) (heF : e ∉ F) : M.Indep (insert e I) := by
--   obtain ⟨J, hJ, hIJ⟩ := hI.subset_basis_of_subset hIF
--   obtain ⟨J', hJ', -⟩ := hJ.indep.subset_basis_of_subset (subset_insert e J)
--   have heJ := (mt <| hF.1 (X := insert e J) hJ) (by simp [insert_subset_iff, heF])
--   obtain ⟨f, hfJ', hfJ⟩ := hJ.indep.exists_insert_of_not_basis (subset_insert e J) heJ hJ'
--   refine hfJ.subset (insert_subset (.inl <| Eq.symm ?_) (hIJ.trans (subset_insert _ _)))
--   simpa [hfJ'.2] using mem_of_mem_of_subset hfJ' (diff_subset_diff_left hJ'.subset)

-- lemma flat_iff_forall_insert_indep :
--     M.Flat F ↔ (∀ ⦃I⦄, M.Indep I → I ⊆ F → ∀ e ∈ M.E, e ∉ F → M.Indep (insert e I)) ∧ F ⊆ M.E := by
--   refine ⟨fun h ↦ ⟨fun I hI h' e he heF ↦ h.insert_indep_of_not_mem hI h' he heF, h.subset_ground⟩,
--     fun ⟨h, hFE⟩ ↦ ⟨fun I X hIF hIX f hfX ↦ by_contra fun hfF ↦ ?_, hFE⟩⟩
--   exact hfF <| hIF.subset <| hIX.mem_of_insert_indep hfX <|
--     h hIX.indep hIF.subset f (hIX.subset_ground hfX) hfF

-- @[simp] theorem closure_flat (M : Matroid α) (X : Set α) : M.Flat (M.closure X) := by
--   rw [flat_iff_isClosed, closure_eq_subtypeClosure]
--   exact ⟨by simp [subtypeClosure], M.subtypeClosure.isClosed_closure ⟨X ∩ M.E, inter_subset_right⟩⟩


lemma mem_closure_insert (he : e ∉ M.closure X) (hef : e ∈ M.closure (insert f X)) :
    f ∈ M.closure (insert e X) := by
  rw [← closure_inter_ground] at *
  have hfE : f ∈ M.E := by
    by_contra! hfE; rw [insert_inter_of_not_mem hfE] at hef; exact he hef
  have heE : e ∈ M.E := (M.closure_subset_ground _) hef
  rw [insert_inter_of_mem hfE] at hef; rw [insert_inter_of_mem heE]

  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ M.E)
  rw [← hI.closure_eq_closure, hI.indep.not_mem_closure_iff] at he
  rw [← closure_insert_closure_eq_closure_insert, ← hI.closure_eq_closure,
    closure_insert_closure_eq_closure_insert, he.1.mem_closure_iff] at *
  rw [or_iff_not_imp_left, dep_iff, insert_comm,
    and_iff_left (insert_subset heE (insert_subset hfE hI.indep.subset_ground)), not_not]
  intro h
  rw [(h.subset (subset_insert _ _)).mem_closure_iff, or_iff_right (h.not_dep), mem_insert_iff,
    or_iff_left he.2] at hef
  subst hef; apply mem_insert

lemma closure_exchange (he : e ∈ M.closure (insert f X) \ M.closure X) :
    f ∈ M.closure (insert e X) \ M.closure X :=
  ⟨mem_closure_insert he.2 he.1, fun hf ↦ by
    rwa [closure_insert_eq_of_mem_closure hf, diff_self, iff_false_intro (not_mem_empty _)] at he⟩

lemma closure_exchange_iff :
    e ∈ M.closure (insert f X) \ M.closure X ↔ f ∈ M.closure (insert e X) \ M.closure X :=
  ⟨closure_exchange, closure_exchange⟩

lemma closure_insert_eq_closure_insert_of_mem (he : e ∈ M.closure (insert f X) \ M.closure X) :
    M.closure (insert e X) = M.closure (insert f X) := by
  have hf := closure_exchange he
  rw [eq_comm, ← closure_closure, ← insert_eq_of_mem he.1, closure_insert_closure_eq_closure_insert,
    insert_comm, ← closure_closure, ← closure_insert_closure_eq_closure_insert,
    insert_eq_of_mem hf.1, closure_closure, closure_closure]

lemma closure_diff_singleton_eq_closure (h : e ∈ M.closure (X \ {e})) :
    M.closure (X \ {e}) = M.closure X := by
  refine (em (e ∈ X)).elim (fun h' ↦ ?_) (fun h' ↦ by rw [diff_singleton_eq_self h'])
  convert M.closure_insert_closure_eq_closure_insert e (X \ {e}) using 1
  · rw [insert_eq_of_mem h, closure_closure]
  rw [insert_diff_singleton, insert_eq_of_mem h']

lemma mem_closure_diff_singleton_iff_closure (he : e ∈ X) (heE : e ∈ M.E := by aesop_mat) :
    e ∈ M.closure (X \ {e}) ↔ M.closure (X \ {e}) = M.closure X :=
  ⟨closure_diff_singleton_eq_closure, fun h ↦ by rw [h]; exact M.mem_closure_of_mem' he⟩

lemma indep_iff_not_mem_closure_diff_forall (hI : I ⊆ M.E := by aesop_mat) :
    M.Indep I ↔ ∀ e ∈ I, e ∉ M.closure (I \ {e}) := by
  use fun h e heI he ↦ ((h.closure_inter_eq_self_of_subset diff_subset).subset ⟨he, heI⟩).2 rfl
  intro h
  obtain ⟨J, hJ⟩ := M.exists_basis I
  convert hJ.indep
  refine hJ.subset.antisymm' (fun e he ↦ by_contra fun heJ ↦ h _ he ?_)
  exact mem_of_mem_of_subset
    (hJ.subset_closure he) (M.closure_subset_closure (subset_diff_singleton hJ.subset heJ))

lemma indep_iff_not_mem_closure_diff_forall' :
    M.Indep I ↔ I ⊆ M.E ∧ ∀ e ∈ I, e ∉ M.closure (I \ {e}) :=
  ⟨fun h ↦ ⟨h.subset_ground, (indep_iff_not_mem_closure_diff_forall h.subset_ground).mp h⟩, fun h ↦
    (indep_iff_not_mem_closure_diff_forall h.1).mpr h.2⟩

lemma Indep.not_mem_closure_diff_of_mem (hI : M.Indep I) (he : e ∈ I) : e ∉ M.closure (I \ {e}) :=
  (indep_iff_not_mem_closure_diff_forall'.1 hI).2 e he

lemma indep_iff_closure_diff_ne_forall : M.Indep I ↔ ∀ e ∈ I,
    M.closure (I \ {e}) ≠ M.closure I := by
  rw [indep_iff_not_mem_closure_diff_forall']
  refine ⟨fun ⟨hIE, h⟩ e heI h_eq ↦ h e heI (h_eq.symm.subset (M.mem_closure_of_mem heI)),
    fun h ↦ ⟨fun e heI ↦ by_contra fun heE ↦ h e heI ?_,fun e heI hin ↦ h e heI
      (by rw [closure_diff_singleton_eq_closure hin])⟩⟩
  rw [← closure_inter_ground, inter_comm, inter_diff_distrib_left,
    inter_singleton_eq_empty.mpr heE, diff_empty, inter_comm, closure_inter_ground]

lemma Indep.closure_diff_singleton_ssubset (hI : M.Indep I) (he : e ∈ I) :
    M.closure (I \ {e}) ⊂ M.closure I :=
  ssubset_of_subset_of_ne (M.closure_mono diff_subset) (indep_iff_closure_diff_ne_forall.mp hI _ he)

lemma indep_iff_closure_ssubset_ssubset_forall (hI : I ⊆ M.E := by aesop_mat) :
    M.Indep I ↔ (∀ J, J ⊂ I → M.closure J ⊂ M.closure I) := by
  rw [indep_iff_not_mem_closure_diff_forall]
  refine ⟨fun h J hJI ↦ (M.closure_subset_closure hJI.subset).ssubset_of_ne (fun h_eq ↦ ?_),
    fun h e heI hin ↦ ?_⟩
  · obtain ⟨e,heJ,h'⟩ := ssubset_iff_insert.1 hJI
    apply h e (h' (mem_insert _ _))
    have heI := M.mem_closure_of_mem (h' (mem_insert e J))
    rw [← h_eq] at heI
    refine mem_of_mem_of_subset heI (M.closure_subset_closure ?_)
    rw [subset_diff, disjoint_singleton_right, and_iff_left heJ]
    exact (subset_insert _ _).trans h'
  refine (h (I \ {e}) (diff_singleton_sSubset.2 heI)).ne ?_
  rw [← closure_closure, ← insert_eq_of_mem hin, closure_insert_closure_eq_closure_insert,
    insert_diff_singleton, insert_eq_of_mem heI]

lemma ext_closure {M₁ M₂ : Matroid α} (h : ∀ X, M₁.closure X = M₂.closure X) : M₁ = M₂ :=
  eq_of_indep_iff_indep_forall (by simpa using h univ)
    (fun _ _ ↦ by simp_rw [indep_iff_closure_diff_ne_forall, h])

@[simp] lemma restrict_closure_eq' (M : Matroid α) (X R : Set α) :
    (M ↾ R).closure X = (M.closure (X ∩ R) ∩ R) ∪ (R \ M.E) := by
  rw [← closure_inter_ground, restrict_ground_eq]
  ext e
  obtain ⟨I, hI⟩ := (M ↾ R).exists_basis (X ∩ R)
  have hI' := (basis_restrict_iff'.mp hI).1
  rw [← hI.closure_eq_closure, ← M.closure_inter_ground (X ∩ R), ← hI'.closure_eq_closure,
    mem_union, mem_inter_iff, hI'.indep.mem_closure_iff, hI.indep.mem_closure_iff, restrict_dep_iff,
    insert_subset_iff, dep_iff, insert_subset_iff, and_iff_left hI'.indep.subset_ground, mem_diff,
    and_iff_left (show I ⊆ R from hI.indep.subset_ground)]
  have hIR : I ⊆ R := hI.indep.subset_ground
  by_cases he : e ∈ M.E; aesop
  simp only [iff_false_intro he, and_false, false_or, and_true, ← mem_inter_iff, ← mem_union,
    inter_eq_self_of_subset_left hIR, union_comm I, and_iff_right
      (show ¬M.Indep (insert e I) from fun hi ↦ he (hi.subset_ground (mem_insert _ _))),
    not_false_iff]

lemma restrict_closure_eq (M : Matroid α) (hXR : X ⊆ R) (hR : R ⊆ M.E := by aesop_mat) :
    (M ↾ R).closure X = M.closure X ∩ R := by
  rw [restrict_closure_eq', diff_eq_empty.mpr hR, union_empty, inter_eq_self_of_subset_left hXR]

@[simp] lemma comap_closure_eq {β : Type*} (M : Matroid β) (f : α → β) (X : Set α) :
    (M.comap f).closure X = f ⁻¹' M.closure (f '' X) := by
  obtain ⟨I, hI⟩ := (M.comap f).exists_basis' X
  obtain ⟨hI', hIinj, -⟩ := comap_basis'_iff.1 hI
  rw [← hI.closure_eq_closure]
  ext x
  obtain (hxE | hxE) := em' (f x ∈ M.E)
  · apply iff_of_false <;> exact (fun h ↦ hxE (by simpa using mem_ground_of_mem_closure h))

  by_cases hxI : x ∈ I
  · exact iff_of_true (mem_closure_of_mem _ hxI hI.indep.subset_ground)
      (mem_closure_of_mem' _ (mem_image_of_mem f (hI.subset hxI))
        (hI'.indep.subset_ground (mem_image_of_mem f hxI)))
  have hss : insert x I ⊆ (M.comap f).E := insert_subset hxE hI.indep.subset_ground
  rw [hI.indep.mem_closure_iff_of_not_mem hxI, ← not_indep_iff hss, comap_indep_iff,
    injOn_insert hxI, not_and, not_and, not_not, iff_true_intro hIinj, true_imp_iff]

  by_cases hxI' : f x ∈ f '' I
  · simp [hxI', hxE, mem_closure_of_mem' _ (hI'.subset hxI') hxE]

  rw [iff_false_intro hxI', imp_false, mem_preimage, image_insert_eq,
    hI'.indep.insert_indep_iff_of_not_mem hxI', mem_diff, and_iff_right hxE, not_not,
    hI'.closure_eq_closure]

@[simp] lemma map_closure_eq {β : Type*} (M : Matroid α) (f : α → β) (hf) (X : Set β) :
    (M.map f hf).closure X = f '' M.closure (f ⁻¹' X) := by
  suffices h' : ∀ X ⊆ f '' M.E, (M.map f hf).closure X = f '' (M.closure (f ⁻¹' X)) by
    convert h' (X ∩ f '' M.E) inter_subset_right using 1
    · rw [← closure_inter_ground]; rfl
    rw [preimage_inter, eq_comm, ← closure_inter_ground, inter_assoc,
      hf.preimage_image_inter Subset.rfl, closure_inter_ground]
  clear X
  intro X hX
  obtain ⟨I, hI⟩ := (M.map f hf).exists_basis X

  obtain ⟨I, X, hI', rfl, rfl⟩ := (map_basis_iff').1 hI

  rw [eq_comm, ← closure_inter_ground, hf.preimage_image_inter hI'.subset_ground,
    ← hI.closure_eq_closure, ← hI'.closure_eq_closure]
  ext e
  simp only [mem_image, hI.indep.mem_closure_iff', map_ground, map_indep_iff, forall_exists_index,
    and_imp, hI'.indep.mem_closure_iff']

  refine ⟨?_, ?_⟩
  · rintro ⟨e, ⟨heE, hind⟩, rfl⟩
    refine ⟨⟨e, heE, rfl⟩, fun J hJ hins ↦ ⟨e, hind ?_, rfl⟩⟩
    rw [← image_insert_eq,
      hf.image_eq_image_iff (insert_subset heE hI'.indep.subset_ground) hJ.subset_ground] at hins
    rwa [hins]
  rintro ⟨⟨x, hx, rfl⟩, h⟩
  refine ⟨x, ⟨hx, fun hind ↦ ?_⟩, rfl⟩
  obtain ⟨x', hx', h_eq⟩ := h _ hind (by rw [image_insert_eq])
  rwa [← hf (hI'.indep.subset_ground hx') hx h_eq]

section Spanning

variable {S T : Set α}

/-- A set is `spanning` in `M` if its closure is equal to `M.E`, or equivalently if it contains
  a base of `M`. -/
def Spanning (M : Matroid α) (S : Set α) := M.closure S = M.E ∧ S ⊆ M.E

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma Spanning.subset_ground (hS : M.Spanning S) : S ⊆ M.E :=
  hS.2

lemma Spanning.closure_eq (hS : M.Spanning S) : M.closure S = M.E :=
  hS.1

lemma spanning_iff_closure (hS : S ⊆ M.E := by aesop_mat) : M.Spanning S ↔ M.closure S = M.E :=
  ⟨And.left, fun h ↦ ⟨h, hS⟩⟩

lemma closure_spanning_iff (hS : S ⊆ M.E := by aesop_mat) :
    M.Spanning (M.closure S) ↔ M.Spanning S := by
  rw [spanning_iff_closure, closure_closure, ← spanning_iff_closure]

lemma spanning_iff_ground_subset_closure (hS : S ⊆ M.E := by aesop_mat) :
    M.Spanning S ↔ M.E ⊆ M.closure S := by
  rw [spanning_iff_closure, subset_antisymm_iff, and_iff_right (closure_subset_ground _ _)]

lemma not_spanning_iff_closure (hS : S ⊆ M.E := by aesop_mat) :
    ¬M.Spanning S ↔ M.closure S ⊂ M.E := by
  rw [spanning_iff_closure, ssubset_iff_subset_ne, iff_and_self,
    iff_true_intro (M.closure_subset_ground _)]
  exact fun _ ↦ trivial

lemma Spanning.superset (hS : M.Spanning S) (hST : S ⊆ T) (hT : T ⊆ M.E := by aesop_mat) :
    M.Spanning T :=
  ⟨(M.closure_subset_ground _).antisymm
    (by rw [← hS.closure_eq]; exact M.closure_subset_closure hST), hT⟩

lemma Spanning.closure_superset_eq (hS : M.Spanning S) (hST : S ⊆ T) : M.closure T = M.E := by
  rw [← closure_inter_ground, ← spanning_iff_closure]
  exact hS.superset (subset_inter hST hS.subset_ground)

lemma Spanning.union_left (hS : M.Spanning S) (hX : X ⊆ M.E := by aesop_mat) :
    M.Spanning (S ∪ X) :=
  hS.superset subset_union_left

lemma Spanning.union_right (hS : M.Spanning S) (hX : X ⊆ M.E := by aesop_mat) :
    M.Spanning (X ∪ S) :=
  hS.superset subset_union_right

lemma Base.spanning (hB : M.Base B) : M.Spanning B :=
  ⟨hB.closure_eq, hB.subset_ground⟩

lemma ground_spanning (M : Matroid α) : M.Spanning M.E :=
  ⟨M.closure_ground, rfl.subset⟩

lemma Base.superset_spanning (hB : M.Base B) (hBX : B ⊆ X) (hX : X ⊆ M.E := by aesop_mat) :
    M.Spanning X :=
  hB.spanning.superset hBX

lemma spanning_iff_superset_base' : M.Spanning S ↔ (∃ B, M.Base B ∧ B ⊆ S) ∧ S ⊆ M.E := by
  refine ⟨fun h ↦ ⟨?_, h.subset_ground⟩, fun ⟨⟨B, hB, hBS⟩, hSE⟩ ↦ hB.spanning.superset hBS⟩
  obtain ⟨B, hB⟩ := M.exists_basis S
  have hB' := hB.basis_closure_right
  rw [h.closure_eq, basis_ground_iff] at hB'
  exact ⟨B, hB', hB.subset⟩

lemma spanning_iff_superset_base (hS : S ⊆ M.E := by aesop_mat) :
    M.Spanning S ↔ ∃ B, M.Base B ∧ B ⊆ S := by
  rw [spanning_iff_superset_base', and_iff_left hS]

lemma Spanning.exists_base_subset (hS : M.Spanning S) : ∃ B, M.Base B ∧ B ⊆ S := by
  rwa [spanning_iff_superset_base] at hS

lemma coindep_iff_compl_spanning (hI : I ⊆ M.E := by aesop_mat) :
    M.Coindep I ↔ M.Spanning (M.E \ I) := by
  rw [coindep_iff_exists, spanning_iff_superset_base]

lemma spanning_iff_compl_coindep (hS : S ⊆ M.E := by aesop_mat) :
    M.Spanning S ↔ M.Coindep (M.E \ S) := by
  rw [coindep_iff_compl_spanning, diff_diff_cancel_left hS]

lemma Coindep.compl_spanning (hI : M.Coindep I) : M.Spanning (M.E \ I) :=
  (coindep_iff_compl_spanning hI.subset_ground).mp hI

lemma coindep_iff_closure_compl_eq_ground (hK : X ⊆ M.E := by aesop_mat) :
    M.Coindep X ↔ M.closure (M.E \ X) = M.E := by
  rw [coindep_iff_compl_spanning, spanning_iff_closure]

lemma Coindep.closure_compl (hX : M.Coindep X) : M.closure (M.E \ X) = M.E :=
  (coindep_iff_closure_compl_eq_ground hX.subset_ground).mp hX

lemma Indep.base_of_spanning (hI : M.Indep I) (hIs : M.Spanning I) : M.Base I := by
  obtain ⟨B, hB, hBI⟩ := hIs.exists_base_subset; rwa [← hB.eq_of_subset_indep hI hBI]

lemma Spanning.base_of_indep (hIs : M.Spanning I) (hI : M.Indep I) : M.Base I :=
  hI.base_of_spanning hIs

lemma eq_of_spanning_iff_spanning_forall {M M' : Matroid α} (h : M.E = M'.E)
    (hsp : ∀ S, S ⊆ M.E → (M.Spanning S ↔ M'.Spanning S )) : M = M' := by
  have hsp' : M.Spanning = M'.Spanning := by
    ext S
    refine (em (S ⊆ M.E)).elim (fun hSE ↦ by rw [hsp _ hSE] )
      (fun hSE ↦ iff_of_false (fun h ↦ hSE h.subset_ground)
      (fun h' ↦ hSE (h'.subset_ground.trans h.symm.subset)))
  rw [← dual_inj, eq_iff_indep_iff_indep_forall, dual_ground, dual_ground, and_iff_right h]
  intro I hIE
  rw [← coindep_def, ← coindep_def, coindep_iff_compl_spanning, coindep_iff_compl_spanning, hsp', h]

end Spanning

section Constructions

@[simp] lemma emptyOn_closure_eq (X : Set α) : (emptyOn α).closure X = ∅ := by
  rw [← subset_empty_iff, ← emptyOn_ground]; apply closure_subset_ground

@[simp] lemma loopyOn_closure_eq (E X : Set α) : (loopyOn E).closure X = E :=
  (closure_subset_ground _ _).antisymm
    (subset_trans (by rw [(loopyOn_base_iff.2 rfl).closure_eq])
      (closure_subset_closure _ (empty_subset _)))

lemma closure_empty_eq_ground_iff : M.closure ∅ = M.E ↔ M = loopyOn M.E := by
  refine ⟨fun h ↦ ext_closure ?_, fun h ↦ by rw [h, loopyOn_closure_eq, loopyOn_ground]⟩
  refine fun X ↦ subset_antisymm (by simp [closure_subset_ground]) ?_
  rw [loopyOn_closure_eq, ← h]
  exact M.closure_mono (empty_subset _)

@[simp] lemma uniqueBaseOn_closure_eq (I E X : Set α) :
    (uniqueBaseOn I E).closure X = (X ∩ I ∩ E) ∪ (E \ I) := by
  have hb : (uniqueBaseOn (I ∩ E) E).Basis (X ∩ E ∩ (I ∩ E)) (X ∩ E) :=
    (uniqueBaseOn_basis_iff inter_subset_right inter_subset_right).2 rfl
  ext e
  rw [← uniqueBaseOn_inter_ground_eq I E, ← closure_inter_ground _ X, uniqueBaseOn_ground,
    ← hb.closure_eq_closure, hb.indep.mem_closure_iff, dep_iff, uniqueBaseOn_indep_iff',
    insert_subset_iff, uniqueBaseOn_ground, inter_assoc, inter_self,
    and_iff_left inter_subset_right, ← inter_inter_distrib_right, inter_assoc,
    inter_union_distrib_right, inter_comm I, inter_union_diff, insert_subset_iff, inter_comm X,
    inter_assoc, and_iff_left inter_subset_left, mem_inter_iff]
  simp only [not_and, mem_inter_iff, mem_union, mem_diff]
  tauto

end Constructions

variable {Xs Ys : Set (Set α)} {ι : Type*}

lemma Indep.inter_basis_closure_iff_subset_closure_inter {X : Set α} (hI : M.Indep I) :
    M.Basis (X ∩ I) X ↔ X ⊆ M.closure (X ∩ I) :=
  ⟨Basis.subset_closure,
    fun h ↦ (hI.inter_left X).basis_of_subset_of_subset_closure inter_subset_left h⟩

lemma Indep.interBasis_biInter (hI : M.Indep I) {X : ι → Set α} {A : Set ι} (hA : A.Nonempty)
    (h : ∀ i ∈ A, M.Basis ((X i) ∩ I) (X i)) : M.Basis ((⋂ i ∈ A, X i) ∩ I) (⋂ i ∈ A, X i) := by
  refine (hI.inter_left _).basis_of_subset_of_subset_closure inter_subset_left ?_
  have := biInter_inter hA X I
  simp_rw [← biInter_inter hA,
    closure_biInter_eq_biInter_closure_of_biUnion_indep hA (I := fun i ↦ (X i) ∩ I)
      (hI.subset (by simp)), subset_iInter_iff]
  exact fun i hiA ↦ (biInter_subset_of_mem hiA).trans (h i hiA).subset_closure

lemma Indep.interBasis_iInter [Nonempty ι] {X : ι → Set α} (hI : M.Indep I)
    (h : ∀ i, M.Basis ((X i) ∩ I) (X i)) : M.Basis ((⋂ i, X i) ∩ I) (⋂ i, X i) := by
  rw [← biInter_univ]
  exact hI.interBasis_biInter (by simp) (by simpa)

lemma Indep.interBasis_sInter (hI : M.Indep I) (hXs : Xs.Nonempty)
    (h : ∀ X ∈ Xs, M.Basis (X ∩ I) X) : M.Basis (⋂₀ Xs ∩ I) (⋂₀ Xs) := by
  rw [sInter_eq_biInter]
  exact hI.interBasis_biInter hXs h

lemma Basis.closure_inter_basis_closure (h : M.Basis (X ∩ I) X) (hI : M.Indep I) :
    M.Basis (M.closure X ∩ I) (M.closure X) := by
  rw [hI.inter_basis_closure_iff_subset_closure_inter] at h ⊢
  exact (M.closure_subset_closure_of_subset_closure h).trans (M.closure_subset_closure
    (inter_subset_inter_left _ (h.trans (M.closure_subset_closure inter_subset_left))))

end Matroid





-- -- section from_axioms
-- -- lemma closure_diff_singleton_eq_cl' (closure : set α → set α) (M.subset_closure : ∀ X, X ⊆ closure X)
-- -- (closure_mono : ∀ X Y, X ⊆ Y → closure X ⊆ closure Y) (closure_idem : ∀ X, closure (closure X) = closure X )
-- -- {x : α} {I : set α} (h : x ∈ closure (I \ {x})) :
-- --   closure (I \ {x}) = closure I :=
-- -- begin
-- --   refine (closure_mono _ _ diff_subset).antisymm _,
-- --   have h' := closure_mono _ _ (insert_subset.mpr ⟨h, (M.subset_closure _ )⟩),
-- --   rw [insert_diff_singleton, closure_idem] at h',
-- --   exact (closure_mono _ _ (subset_insert _ _)).trans h',
-- -- end
-- -- /-- A set is independent relative to a closure function if none of its elements are contained in
-- --   the closure of their removal -/
-- -- def closure_indep (closure : set α → set α) (I : set α) : Prop := ∀ e ∈ I, e ∉ closure (I \ {e})
-- -- lemma closure_indep_mono {closure : set α → set α} (closure_mono : ∀ ⦃X Y⦄, X ⊆ Y → closure X ⊆ closure Y) {I J : set α}
-- -- (hJ : closure_indep closure J) (hIJ : I ⊆ J) :
-- --   closure_indep closure I :=
-- -- (λ e heI heclosure, hJ e (hIJ heI) (closure_mono (diff_subset_diff_left hIJ) heclosure))
-- -- lemma closure_indep_aux {e : α} {I : set α} {closure : set α → set α}
-- -- (closure_exchange : ∀ (X e f), f ∈ closure (insert e X) \ closure X → e ∈ closure (insert f X) \ closure X )
-- -- (h : closure_indep closure I) (heI : ¬closure_indep closure (insert e I)) :
-- -- e ∈ closure I :=
-- -- begin
-- --   have he : α ∉ I, by { intro he, rw [insert_eq_of_mem he] at heI, exact heI h },
-- --   rw [closure_indep] at heI, push_neg at heI,
-- --   obtain ⟨f, ⟨(rfl | hfI), hfclosure⟩⟩ := heI,
-- --   { rwa [insert_diff_self_of_not_mem he] at hfclosure },
-- --   have hne : α ≠ f, by { rintro rfl, exact he hfI },
-- --   rw [← insert_diff_singleton_comm hne] at hfclosure,
-- --   convert (closure_exchange (I \ {f}) e f ⟨hfclosure,h f hfI⟩).1,
-- --   rw [insert_diff_singleton, insert_eq_of_mem hfI],
-- -- end
-- -- /-- If the closure axioms hold, then `cl`-independence gives rise to a matroid -/
-- -- def matroid_of_closure (closure : set α → set α) (M.subset_closure : ∀ X, X ⊆ closure X)
-- -- (closure_mono : ∀ ⦃X Y⦄, X ⊆ Y → closure X ⊆ closure Y) (closure_idem : ∀ X, closure (closure X) = closure X )
-- -- (closure_exchange : ∀ (X e f), f ∈ closure (insert e X) \ closure X → e ∈ closure (insert f X) \ closure X )
-- -- (closure_indep_maximal : ∀ ⦃I X⦄, closure_indep closure I → I ⊆ X  →
-- --     (maximals (⊆) {J | closure_indep closure J ∧ I ⊆ J ∧ J ⊆ X }).nonempty) :
-- -- matroid_in α :=
-- -- matroid_of_indep (closure_indep closure)
-- -- (λ e he _, not_mem_empty _ he) (λ I J hJ hIJ, closure_indep_mono closure_mono hJ hIJ)
-- -- (begin
-- --   refine λ I I' hI hIn hI'm, _,
-- --   obtain ⟨B, hB⟩ := closure_indep_maximal hI (subset_union_left I I'),
-- --   have hB' : B ∈ maximals (⊆) {J | closure_indep closure J},
-- --   { refine ⟨hB.1.1,(λ B' hB' hBB' e heB', by_contra (λ heB, _) )⟩,
-- --     have he' : α ∈ closure I',
-- --     { refine (em (e ∈ I')).elim (λ heI', (M.subset_closure I') heI')
-- --         (λ heI', closure_indep_aux closure_exchange hI'm.1 (λ hi, _)),
-- --       exact heI' (hI'm.2 hi (subset_insert e _) (mem_insert e _)) },
-- --       have hI'B : I' ⊆ closure B,
-- --     { refine λ f hf, (em (f ∈ B)).elim (λ h', M.subset_closure B h')
-- --         (λ hfB', closure_indep_aux closure_exchange hB.1.1 (λ hi, hfB' _)),
-- --       refine hB.2 ⟨hi,hB.1.2.1.trans (subset_insert _ _),_⟩ (subset_insert _ _) (mem_insert _ _),
-- --       exact insert_subset.mpr ⟨or.inr hf,hB.1.2.2⟩ },
-- --     have heBclosure := (closure_idem B).subset ((closure_mono hI'B) he'),
-- --     refine closure_indep_mono closure_mono hB' (insert_subset.mpr ⟨heB', hBB'⟩) e (mem_insert _ _) _,
-- --     rwa [insert_diff_of_mem _ (mem_singleton e), diff_singleton_eq_self heB] },
-- --   obtain ⟨f,hfB,hfI⟩ := exists_of_ssubset
-- --     (hB.1.2.1.ssubset_of_ne (by { rintro rfl, exact hIn hB' })),
-- --   refine ⟨f, ⟨_, hfI⟩, closure_indep_mono closure_mono hB.1.1 (insert_subset.mpr ⟨hfB,hB.1.2.1⟩)⟩,
-- --   exact or.elim (hB.1.2.2 hfB) (false.elim ∘ hfI) id,
-- -- end)
-- -- (λ I X hI hIX, closure_indep_maximal hI hIX)
-- -- lemma closure_indep_closure_eq {closure : set α → set α }
-- --   (M.subset_closure : ∀ X, X ⊆ closure X )
-- --   (closure_mono : ∀ ⦃X Y⦄, X ⊆ Y → closure X ⊆ closure Y )
-- --   (closure_idem : ∀ X, closure (closure X) = closure X )
-- --   (closure_exchange : ∀ (X e f), f ∈ closure (insert e X) \ closure X → e ∈ closure (insert f X) \ closure X )
-- --   (closure_indep_maximal : ∀ ⦃I X⦄, closure_indep closure I → I ⊆ X →
-- --     (maximals (⊆) {J | closure_indep closure J ∧ I ⊆ J ∧ J ⊆ X }).nonempty ) (X : set α) :
-- -- closure X = X ∪ {e | ∃ I ⊆ X, closure_indep closure I ∧ ¬closure_indep closure (insert e I) }  :=
-- -- begin
-- --   ext f,
-- --   refine ⟨λ h, (em (f ∈ X)).elim or.inl (λ hf, or.inr _),
-- --     λ h, or.elim h (λ g, M.subset_closure X g) _⟩,
-- --   { have hd : ¬ (closure_indep closure (insert f X)),
-- --     { refine λ hi, hi f (mem_insert _ _) _, convert h,
-- --       rw [insert_diff_of_mem _ (mem_singleton f), diff_singleton_eq_self hf] },
-- --     obtain ⟨I, hI⟩ := closure_indep_maximal (λ e he h', not_mem_empty _ he) (empty_subset X),
-- --     have hXI : X ⊆ closure I,
-- --     { refine λ x hx, (em (x ∈ I)).elim (λ h', M.subset_closure _ h') (λ hxI, _),
-- --       refine closure_indep_aux closure_exchange hI.1.1 (λ hi, hxI _),
-- --       refine hI.2 ⟨hi, empty_subset (insert x I), _⟩ (subset_insert x _) (mem_insert _ _),
-- --       exact insert_subset.mpr ⟨hx, hI.1.2.2⟩ },
-- --     have hfI : f ∈ closure I, from (closure_mono (hXI)).trans_eq (closure_idem I) h,
-- --     refine ⟨I, hI.1.2.2, hI.1.1, λ hi, hf (hi f (mem_insert f _) _).elim⟩,
-- --     rwa [insert_diff_of_mem _ (mem_singleton f), diff_singleton_eq_self],
-- --     exact not_mem_subset hI.1.2.2 hf },
-- --   rintro ⟨I, hIX, hI, hfI⟩,
-- --   exact (closure_mono hIX) (closure_indep_aux closure_exchange hI hfI),
-- -- end
-- -- @[simp] lemma matroid_of_closure_apply {closure : set α → set α} (M.subset_closure : ∀ X, X ⊆ closure X)
-- -- (closure_mono : ∀ ⦃X Y⦄, X ⊆ Y → closure X ⊆ closure Y) (closure_idem : ∀ X, closure (closure X) = closure X)
-- -- (closure_exchange : ∀ (X e f), f ∈ closure (insert e X) \ closure X → e ∈ closure (insert f X) \ closure X)
-- -- (closure_indep_maximal : ∀ ⦃I X⦄, closure_indep closure I → I ⊆ X →
-- --     (maximals (⊆) {J | closure_indep closure J ∧ I ⊆ J ∧ J ⊆ X }).nonempty) :
-- -- (matroid_of_closure closure M.subset_closure closure_mono closure_idem closure_exchange closure_indep_maximal).closure = closure :=
-- -- begin
-- --   ext1 X,
-- --   rw [(closure_indep_closure_eq M.subset_closure closure_mono closure_idem closure_exchange closure_indep_maximal X : closure X = _),
-- --     matroid_of_closure, matroid.closure_eq_set_of_indep_not_indep],
-- --   simp,
-- -- end
-- -- @[simp] lemma matroid_of_closure_indep_iff {closure : set α → set α} (M.subset_closure : ∀ X, X ⊆ closure X)
-- -- (closure_mono : ∀ ⦃X Y⦄, X ⊆ Y → closure X ⊆ closure Y) (closure_idem : ∀ X, closure (closure X) = closure X)
-- -- (closure_exchange : ∀ (X e f), f ∈ closure (insert e X) \ closure X → e ∈ closure (insert f X) \ closure X)
-- -- (closure_indep_maximal : ∀ ⦃I X⦄, closure_indep closure I → I ⊆ X →
-- --     (maximals (⊆) {J | closure_indep closure J ∧ I ⊆ J ∧ J ⊆ X }).nonempty) {I : set α}:
-- -- (matroid_of_closure closure M.subset_closure closure_mono closure_idem closure_exchange closure_indep_maximal).indep I ↔ closure_indep closure I :=
-- -- by rw [matroid_of_closure, matroid_of_indep_apply]
-- -- /-- The maximality axiom isn't needed if all independent sets are at most some fixed size. -/
-- -- def matroid_of_closure_of_indep_bounded (closure : set α → set α)
-- --   (M.subset_closure : ∀ X, X ⊆ closure X )
-- --   (closure_mono : ∀ ⦃X Y⦄, X ⊆ Y → closure X ⊆ closure Y )
-- --   (closure_idem : ∀ X, closure (closure X) = closure X )
-- --   (closure_exchange : ∀ (X e f), f ∈ closure (insert e X) \ closure X → e ∈ closure (insert f X) \ closure X )
-- --   (n : ℕ) (hn : ∀ I, closure_indep closure I → I.finite ∧ I.ncard ≤ n) :
-- -- matroid_in α := matroid_of_closure closure M.subset_closure closure_mono closure_idem closure_exchange
-- -- (exists_maximal_subset_property_of_bounded ⟨n, hn⟩)
-- -- @[simp] lemma matroid_of_closure_of_indep_bounded_apply (closure : set α → set α) (M.subset_closure : ∀ X, X ⊆ closure X )
-- -- (closure_mono : ∀ ⦃X Y⦄, X ⊆ Y → closure X ⊆ closure Y) (closure_idem : ∀ X, closure (closure X) = closure X )
-- -- (closure_exchange : ∀ (X e f), f ∈ closure (insert e X) \ closure X → e ∈ closure (insert f X) \ closure X )
-- -- (n : ℕ) (hn : ∀ I, closure_indep closure I → I.finite ∧ I.ncard ≤ n) :
-- -- (matroid_of_closure_of_indep_bounded closure M.subset_closure closure_mono closure_idem closure_exchange n hn).closure = closure :=
-- -- by simp [matroid_of_closure_of_indep_bounded]
-- -- instance (closure : set α → set α) (M.subset_closure : ∀ X, X ⊆ closure X )
-- -- (closure_mono : ∀ ⦃X Y⦄, X ⊆ Y → closure X ⊆ closure Y) (closure_idem : ∀ X, closure (closure X) = closure X )
-- -- (closure_exchange : ∀ (X e f), f ∈ closure (insert e X) \ closure X → e ∈ closure (insert f X) \ closure X )
-- -- (n : ℕ) (hn : ∀ I, closure_indep closure I → I.finite ∧ I.ncard ≤ n) :
-- -- matroid.finite_rk (matroid_of_closure_of_indep_bounded closure M.subset_closure closure_mono closure_idem closure_exchange n hn)
-- -- :=
-- -- begin
-- --   obtain ⟨B, h⟩ :=
-- --     (matroid_of_closure_of_indep_bounded closure M.subset_closure closure_mono closure_idem closure_exchange n hn).exists_base,
-- --   refine h.finite_rk_of_finite (hn _ _).1,
-- --   simp_rw [matroid_of_closure_of_indep_bounded, matroid_of_closure, matroid.base_iff_maximal_indep,
-- --     matroid_of_indep_apply] at h,
-- --   exact h.1,
-- -- end
-- -- /-- A finite matroid as defined by the closure axioms. -/
-- -- def matroid_of_closure_of_finite [finite E] (closure : set α → set α) (M.subset_closure : ∀ X, X ⊆ closure X )
-- -- (closure_mono : ∀ ⦃X Y⦄, X ⊆ Y → closure X ⊆ closure Y) (closure_idem : ∀ X, closure (closure X) = closure X)
-- -- (closure_exchange : ∀ (X e f), f ∈ closure (insert e X) \ closure X → e ∈ closure (insert f X) \ closure X) :
-- -- matroid_in α   :=
-- -- matroid_of_closure_of_indep_bounded closure M.subset_closure closure_mono closure_idem closure_exchange (nat.card E)
-- -- (λ I hI, ⟨to_finite _, by { rw [← ncard_univ], exact ncard_le_of_subset (subset_univ _) }⟩)
-- -- @[simp] lemma matroid_of_closure_of_finite_apply [finite E] (closure : set α → set α)
-- -- (M.subset_closure : ∀ X, X ⊆ closure X )
-- -- (closure_mono : ∀ ⦃X Y⦄, X ⊆ Y → closure X ⊆ closure Y) (closure_idem : ∀ X, closure (closure X) = closure X)
-- -- (closure_exchange : ∀ (X e f), f ∈ closure (insert e X) \ closure X → e ∈ closure (insert f X) \ closure X) :
-- -- (matroid_of_closure_of_finite closure M.subset_closure closure_mono closure_idem closure_exchange).closure = closure :=
-- -- by simp [matroid_of_closure_of_finite]
-- -- end from_axioms
-- end Matroid
