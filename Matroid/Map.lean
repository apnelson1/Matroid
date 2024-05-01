import Matroid.Constructions.Basic
import Matroid.ForMathlib.Function
import Matroid.ForMathlib.Logic_Embedding_Set
import Matroid.ForMathlib.Matroid_Basic
import Matroid.ForMathlib.PreimageVal
import Mathlib.Data.Set.Subset

open Set.Notation


/-
This file defines maps and comaps, which move a matroid on one type to a matroid on another
using a function between the types. The constructions are mathematically just combinations of
restrictions and parallel extensions, so are not difficult.

At least for finite matroids, both maps and comaps are a special case of a construction of
Perfect (1969) in which a matroid structure can be transported across a bipartite graph.
[See Oxley, Thm 11.2.12]. This is nontrivial, and I don't know whether this is known to extend to
infinite matroids. The proofs use cardinality. The construction would imply Konig's theorem
for infinite bipartite graphs, which isn't easy.

In particular, if things were generalized, it would allow the construction `map` not to require
injectivity, which would be nice. It might be easier than the full strength of the bipartite graph
construction; it corresponds to the case where one side of the graph has max degree one.
-/

universe u

open Set Function

namespace Matroid
variable {α β : Type*} {f : α → β} {E I s : Set α}

private def comapIndepMatroid (M : Matroid β) (f : α → β) : IndepMatroid α where
  E := f ⁻¹' M.E
  Indep I := M.Indep (f '' I) ∧ InjOn f I
  indep_empty := by simp
  indep_subset I J h hIJ := ⟨h.1.subset (image_subset _ hIJ), InjOn.mono hIJ h.2⟩
  indep_aug := by
    rintro I B ⟨hI, hIinj⟩ hImax hBmax
    simp only [mem_maximals_iff, mem_setOf_eq, hI, hIinj, and_self, and_imp,
      true_and, not_forall, exists_prop, exists_and_left] at hImax hBmax

    obtain ⟨I', hI', hI'inj, hII', hne⟩ := hImax

    have h₁ : ¬(M ↾ range f).Base (f '' I) := by
      refine fun hB ↦ hne ?_
      have h_im := hB.eq_of_subset_indep (by simpa) (image_subset _ hII')
      rwa [hI'inj.image_eq_image_iff_of_subset hII' Subset.rfl] at h_im

    have h₂ : (M ↾ range f).Base (f '' B) := by
      refine Indep.base_of_maximal (by simpa using hBmax.1.1) (fun J hJi hBJ ↦ ?_)
      simp only [restrict_indep_iff] at hJi
      obtain ⟨J₀, hBJ₀, hJ₀⟩ := hBmax.1.2.bijOn_image.extend hBJ hJi.2
      obtain rfl := hJ₀.image_eq
      rw [hBmax.2 hJi.1 hJ₀.injOn hBJ₀]

    obtain ⟨_, ⟨⟨e, he, rfl⟩, he'⟩, hei⟩ := Indep.exists_insert_of_not_base (by simpa) h₁ h₂
    have heI : e ∉ I := fun heI ↦ he' (mem_image_of_mem f heI)
    rw [← image_insert_eq, restrict_indep_iff] at hei
    exact ⟨e, ⟨he, heI⟩, hei.1, (injOn_insert heI).2 ⟨hIinj, he'⟩⟩
  indep_maximal := by
    rintro X - I ⟨hI, hIinj⟩ hIX
    obtain ⟨J, hJ⟩ := (M ↾ range f).existsMaximalSubsetProperty_indep (f '' X) (by simp)
      (f '' I) (by simpa) (image_subset _ hIX)
    simp only [restrict_indep_iff, image_subset_iff, mem_maximals_iff, mem_setOf_eq, and_imp] at hJ

    obtain ⟨J₀, hIJ₀, hJ₀X, hbj⟩ := hIinj.bijOn_image.extend_of_subset hIX
      (image_subset f hJ.1.2.1) (image_subset_iff.2 <| preimage_mono hJ.1.2.2)

    have him := hbj.image_eq; rw [image_preimage_eq_of_subset hJ.1.1.2] at him; subst him
    use J₀
    simp only [mem_maximals_iff, mem_setOf_eq, hJ.1.1.1, hbj.injOn, and_self, hIJ₀,
      hJ₀X, and_imp, true_and]
    intro K hK hinj hIK hKX hJ₀K
    rw [← hinj.image_eq_image_iff_of_subset hJ₀K Subset.rfl,
       hJ.2 hK (image_subset_range _ _) (fun e he ↦ ⟨e, hIK he, rfl⟩)
       (image_subset _ hKX) (image_subset _ hJ₀K)]
  subset_ground I hI e heI := hI.1.subset_ground ⟨e, heI, rfl⟩

/-- The pullback of a matroid on `β` by a function `f : α → β` to a matroid on `α`.
Elements with the same image are parallel and the ground set is `f ⁻¹' M.E`. -/
def comap (M : Matroid β) (f : α → β) : Matroid α := (comapIndepMatroid M f).matroid

@[simp] theorem comap_indep_iff {M : Matroid β} :
    (M.comap f).Indep I ↔ M.Indep (f '' I) ∧ InjOn f I := by
  simp [comap, comapIndepMatroid]

@[simp] theorem comap_ground_eq (M : Matroid β) (f : α → β) :
    (M.comap f).E = f ⁻¹' M.E := rfl

@[simp] theorem comap_dep_iff {M : Matroid β} :
    (M.comap f).Dep I ↔ M.Dep (f '' I) ∨ (M.Indep (f '' I) ∧ ¬ InjOn f I) := by
  rw [Dep, comap_indep_iff, not_and, comap_ground_eq, Dep, image_subset_iff]
  refine ⟨fun ⟨hi, h⟩ ↦ ?_, ?_⟩
  · rw [and_iff_left h, ← imp_iff_not_or]
    exact fun hI ↦ ⟨hI, hi hI⟩
  rintro (⟨hI, hIE⟩ | hI)
  · exact ⟨fun h ↦ (hI h).elim, hIE⟩
  rw [iff_true_intro hI.1, iff_true_intro hI.2, implies_true, true_and]
  simpa using hI.1.subset_ground

@[simp] theorem comap_id (M : Matroid β) : M.comap id = M :=
  eq_of_indep_iff_indep_forall (by simp) (by simp [injective_id.injOn _])

theorem comap_indep_iff_of_injOn {M : Matroid β} (hf : InjOn f (f ⁻¹' M.E)) :
    (M.comap f).Indep I ↔ M.Indep (f '' I) := by
  rw [comap_indep_iff, and_iff_left_iff_imp]
  refine fun hi ↦ hf.mono <| subset_trans ?_ (preimage_mono hi.subset_ground)
  apply subset_preimage_image

theorem comap_indep_iff_of_embedding (M : Matroid β) (f : α ↪ β) :
    (M.comap f).Indep I ↔ M.Indep (f '' I) :=
  comap_indep_iff_of_injOn (f.injective.injOn _)

@[simp] theorem comap_emptyOn (f : α → β) : comap (emptyOn β) f = emptyOn α := by
  simp [← ground_eq_empty_iff]

@[simp] theorem comap_loopyOn (f : α → β) (E : Set β) :
    comap (loopyOn E) f = loopyOn (f ⁻¹' E) := by
  rw [eq_loopyOn_iff]; aesop

/-- The pullback of a matroid on `β` by a function `f : α → β` to a matroid on `α`,
restricted to a ground set `E`. Elements with the same image are parallel. -/
def comapOn (M : Matroid β) (E : Set α) (f : α → β) : Matroid α := (M.comap f) ↾ E

theorem comapOn_preimage_eq (M : Matroid β) (f : α → β) : M.comapOn (f ⁻¹' M.E) f = M.comap f := by
  rw [comapOn, restrict_eq_self_iff]; rfl

@[simp] theorem comapOn_indep_iff {M : Matroid β} :
    (M.comapOn E f).Indep I ↔ (M.Indep (f '' I) ∧ InjOn f I ∧ I ⊆ E) := by
  simp [comapOn, and_assoc]

@[simp] theorem comapOn_ground_eq {M : Matroid β} :
    (M.comapOn E f).E = E := rfl

theorem comapOn_base_iff_of_surjOn {M : Matroid β} {E : Set α} (h : SurjOn f E M.E) {B : Set α} :
    (M.comapOn E f).Base B ↔ (M.Base (f '' B) ∧ InjOn f B ∧ B ⊆ E) := by
  simp only [base_iff_maximal_indep, comapOn_indep_iff, and_imp, image_subset_iff]
  rw [and_assoc, and_assoc, and_assoc, (show (∀ _, _) ∧ _ ↔ _ ∧ (∀ _, _) by rw [and_comm]),
    and_assoc, and_congr_right_iff, and_congr_right_iff, and_congr_right_iff]
  refine fun _ hinj hBE ↦ ⟨fun h' J hJ hBJ ↦ ?_, fun h' I hI hfI _ hBI ↦ ?_⟩
  · rw [subset_antisymm_iff, image_subset_iff, and_iff_right hBJ]
    refine fun x hxJ ↦ by_contra fun hcon ↦ ?_
    obtain ⟨x, hx, rfl⟩ := h (hJ.subset_ground hxJ)
    rw [h' (insert x B) (hJ.subset ?_) ?_ (insert_subset hx hBE) (subset_insert _ _)] at hcon
    · simp at hcon
    · exact image_subset_iff.2 <| insert_subset hxJ hBJ
    rwa [injOn_insert (fun hxB ↦ hcon (mem_image_of_mem _ hxB)), and_iff_right hinj]
  specialize h' _ hI (hBI.trans (subset_preimage_image _ _))
  rwa [hfI.image_eq_image_iff_of_subset hBI Subset.rfl] at h'

theorem comapOn_base_iff_of_bijOn {M : Matroid β} {E : Set α} (h : BijOn f E M.E) {B : Set α} :
    (M.comapOn E f).Base B ↔ M.Base (f '' B) ∧ B ⊆ E := by
  rw [comapOn_base_iff_of_surjOn h.surjOn, and_congr_right_iff, and_iff_right_iff_imp]
  exact fun _ ↦ h.injOn.mono

theorem comapOn_dual_eq_of_bijOn {M : Matroid β} {E : Set α} (h : BijOn f E M.E) :
    (M.comapOn E f)✶ = M✶.comapOn E f := by
  refine eq_of_base_iff_base_forall (by simp) (fun B hB ↦ ?_)
  rw [comapOn_base_iff_of_bijOn (by simpa), dual_base_iff, comapOn_base_iff_of_bijOn h,
    dual_base_iff _, comapOn_ground_eq, and_iff_left (diff_subset _ _), and_iff_left (by simpa),
    h.injOn.image_diff (by simpa), h.image_eq]
  exact (h.mapsTo.mono_left (show B ⊆ E by simpa)).image_subset

section Map

/-- Map a matroid `M` to an isomorphic copy in `β` using an embedding `M.E ↪ β`. -/
def mapSetEmbedding (M : Matroid α) (f : M.E ↪ β) : Matroid β := ofExistsMatroidIndep
  (E := range f)
  (Indep := fun I ↦ M.Indep ↑(f ⁻¹' I) ∧ I ⊆ range f)
  (hM := by
    classical
    obtain (rfl | ⟨⟨e,he⟩⟩) := eq_emptyOn_or_nonempty M
    · refine ⟨emptyOn β, ?_⟩
      simp only [emptyOn_ground] at f
      simp [range_eq_empty f, subset_empty_iff]
    have _ : Nonempty M.E := ⟨⟨e,he⟩⟩
    have _ : Nonempty α := ⟨e⟩
    refine ⟨M.comapOn (range f) (fun x ↦ ↑(invFunOn f univ x)), rfl, ?_⟩
    simp_rw [comapOn_indep_iff, ← and_assoc, and_congr_left_iff, subset_range_iff_exists_image_eq]
    rintro _ ⟨I, rfl⟩
    rw [← image_image, InjOn.invFunOn_image (f.injective.injOn _) (subset_univ _),
      preimage_image_eq _ f.injective, and_iff_left_iff_imp]
    rintro - x hx y hy
    simp only [EmbeddingLike.apply_eq_iff_eq, Subtype.val_inj]
    exact (invFunOn_injOn_image f univ) (image_subset f (subset_univ I) hx)
      (image_subset f (subset_univ I) hy) )

@[simp] theorem mapSetEmbedding_ground (M : Matroid α) (f : M.E ↪ β) :
    (M.mapSetEmbedding f).E = range f := rfl

@[simp] theorem mapSetEmbedding_indep_iff {M : Matroid α} {f : M.E ↪ β} {I : Set β} :
    (M.mapSetEmbedding f).Indep I ↔ M.Indep ↑(f ⁻¹' I) ∧ I ⊆ range f := by
  simp [mapSetEmbedding]

theorem mapSetEmbedding_indep_iff' {M : Matroid α} {f : M.E ↪ β} {I : Set β} :
    (M.mapSetEmbedding f).Indep I ↔ ∃ (I₀ : Set M.E), M.Indep ↑I₀ ∧ I = f '' I₀ := by
  simp only [mapSetEmbedding_indep_iff, subset_range_iff_exists_image_eq]
  constructor
  · rintro ⟨hI, I, rfl⟩
    exact ⟨I, by rwa [preimage_image_eq _ f.injective] at hI, rfl⟩
  rintro ⟨I, hI, rfl⟩
  rw [preimage_image_eq _ f.injective]
  exact ⟨hI, _, rfl⟩

/-- Given an injective function `f` on `M.E`, the isomorphic copy of `M` whose independent sets
are the images of those in `M`. -/
def map (M : Matroid α) (f : α → β) (hf : InjOn f M.E) : Matroid β := ofExistsMatroidIndep
  (E := f '' M.E)
  (Indep := fun I ↦ ∃ I₀, M.Indep I₀ ∧ I = f '' I₀)
  (hM := by
    refine ⟨M.mapSetEmbedding ⟨_, hf.injective⟩, by simp, fun I ↦ ?_⟩
    simp_rw [mapSetEmbedding_indep_iff', Embedding.coeFn_mk, restrict_apply]
    constructor
    · rintro ⟨I, hI, rfl⟩
      exact ⟨I, hI, by simp⟩
    rintro ⟨I, hI, rfl⟩
    refine ⟨M.E ↓∩ I, by rwa [image_val_preimage_val_of_subset hI.subset_ground], ?_⟩
    simp only [image_val_image_eq, image_val_preimage_val_of_subset hI.subset_ground])

@[simp] theorem map_ground (M : Matroid α) (f : α → β) (hf : InjOn f M.E) :
    (M.map f hf).E = f '' M.E := rfl

@[simp] theorem map_indep_iff {M : Matroid α} {f : α → β} {hf : InjOn f M.E} {I : Set β} :
    (M.map f hf).Indep I ↔ ∃ I₀, M.Indep I₀ ∧ I = f '' I₀ := by
  simp [map]

/-- Map `M : Matroid α` across an embedding defined on all of `α` -/
def mapEmbedding (M : Matroid α) (f : α ↪ β) : Matroid β := M.map f <| f.injective.injOn _

/-- Map `M : Matroid α` across an equivalence `α ≃ β` -/
def mapEquiv (M : Matroid α) (f : α ≃ β) : Matroid β := M.mapEmbedding f.toEmbedding

/-- Map `M : Matroid α` to a `Matroid β` with ground set `E` using an equivalence `M.E ≃ E`.
Defined using `Matroid.ofExistsMatroidIndep` for better defeq.  -/
def mapSetEquiv (M : Matroid α) {E : Set β} (e : M.E ≃ E) : Matroid β :=
  ofExistsMatroidIndep E (fun I ↦ I ⊆ E ∧ M.Indep ↑(e.symm '' (E ↓∩ I)))
  ⟨M.mapSetEmbedding (e.toEmbedding.trans <| Embedding.setSubtype E), by
    simp [Embedding.range_trans, and_comm, image_equiv_eq_preimage_symm]⟩

@[simp] theorem mapSetEquiv.ground (M : Matroid α) {E : Set β} (e : M.E ≃ E) :
    (M.mapSetEquiv e).E = E := rfl

@[simp] theorem mapSetEquiv_indep_iff (M : Matroid α) {E : Set β} (e : M.E ≃ E) {I : Set β} :
    (M.mapSetEquiv e).Indep I ↔ I ⊆ E ∧ M.Indep ↑(e.symm '' (E ↓∩ I)) := by
  simp [mapSetEquiv]

theorem map_image_indep_iff {M : Matroid α} {f : α → β} {hf : InjOn f M.E} {I : Set α}
    (hI : I ⊆ M.E) : (M.map f hf).Indep (f '' I) ↔ M.Indep I := by
  rw [map_indep_iff]
  refine ⟨fun ⟨J, hJ, hIJ⟩ ↦ ?_, fun h ↦ ⟨I, h, rfl⟩ ⟩
  rw [hf.image_eq_image_iff_of_subset hI hJ.subset_ground] at hIJ; rwa [hIJ]

@[simp] theorem mapEmbedding_indep_iff {M : Matroid α} {f : α ↪ β} {I : Set β} :
    (M.mapEmbedding f).Indep I ↔ M.Indep (f ⁻¹' I) ∧ I ⊆ range f := by
  rw [mapEmbedding, map_indep_iff]
  refine ⟨?_, fun ⟨h,h'⟩ ↦ ⟨f ⁻¹' I, h, by rwa [eq_comm, image_preimage_eq_iff]⟩⟩
  rintro ⟨I, hI, rfl⟩
  rw [preimage_image_eq _ f.injective]
  exact ⟨hI, image_subset_range _ _⟩

@[simp] theorem mapEquiv_indep_iff {M : Matroid α} {f : α ≃ β} {I : Set β} :
    (M.mapEquiv f).Indep I ↔ M.Indep (f.symm '' I) := by
  rw [mapEquiv, mapEmbedding, map_indep_iff, Equiv.coe_toEmbedding]
  refine ⟨?_, fun h ↦ ⟨_, h, by simp⟩ ⟩
  rintro ⟨I, hI, rfl⟩
  rwa [f.symm_image_image]

@[simp] theorem map_base_iff (M : Matroid α) (f : α → β) (hf : InjOn f M.E) {B : Set β} :
    (M.map f hf).Base B ↔ ∃ B₀, M.Base B₀ ∧ B = f '' B₀ := by
  rw [base_iff_maximal_indep, map_indep_iff]
  refine ⟨fun ⟨h, hB⟩ ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨B₀, hB₀, rfl⟩ := h
    refine ⟨_, hB₀.base_of_maximal fun J hJ hB₀J ↦ ?_, rfl⟩
    specialize hB (f '' J) ((map_image_indep_iff hJ.subset_ground).2 hJ) (image_subset _ hB₀J)
    rwa [hf.image_eq_image_iff_of_subset hB₀.subset_ground hJ.subset_ground] at hB
  obtain ⟨B₀, hB, rfl⟩ := h
  refine ⟨⟨B₀, hB.indep, rfl⟩, fun I hI hB₀I ↦ ?_⟩
  obtain ⟨I, hI', rfl⟩ := map_indep_iff.1 hI
  rw [hf.image_subset_image_iff_of_subset hB.subset_ground hI'.subset_ground] at hB₀I
  rw [hB.eq_of_subset_indep hI' hB₀I]

theorem map_image_base_iff {M : Matroid α} {f : α → β} {hf : InjOn f M.E} {B : Set α}
    (hB : B ⊆ M.E) : (M.map f hf).Base (f '' B) ↔ M.Base B := by
  rw [map_base_iff]
  refine ⟨fun ⟨J, hJ, hIJ⟩ ↦ ?_, fun h ↦ ⟨B, h, rfl⟩⟩
  rw [hf.image_eq_image_iff_of_subset hB hJ.subset_ground] at hIJ; rwa [hIJ]

@[simp] theorem map_dual {M : Matroid α} {f : α → β} {hf : InjOn f M.E} :
    (M.map f hf)✶ = M✶.map f hf := by
  apply eq_of_base_iff_base_forall (by simp)
  simp only [dual_ground, map_ground, subset_image_iff, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, dual_base_iff']
  intro B hB
  simp_rw [← hf.image_diff hB, map_image_base_iff (diff_subset _ _),
    map_image_base_iff (show B ⊆ M✶.E from hB), dual_base_iff hB, and_iff_left_iff_imp]
  exact fun _ ↦ ⟨B, hB, rfl⟩

@[simp] theorem map_emptyOn (f : α → β) : (emptyOn α).map f (by simp) = emptyOn β := by
  simp [← ground_eq_empty_iff]

@[simp] theorem map_loopyOn (f : α → β) (hf : InjOn f E) :
    (loopyOn E).map f hf = loopyOn (f '' E) := by
  simp [eq_loopyOn_iff]

@[simp] theorem map_freeOn (f : α → β) (hf : InjOn f E) :
    (freeOn E).map f hf = freeOn (f '' E) := by
  rw [← dual_inj]; simp

end Map

section restrictSubtype

variable {E X I : Set α} {M N : Matroid α}

/-- Given `M : Matroid α` and `X : Set α`, the restriction of `M` to `X`,
viewed as a matroid on type `X` with ground set `univ`.
Always isomorphic to `M ↾ X`. If `X = M.E`, then isomorphic to `M`. -/
def restrictSubtype (M : Matroid α) (X : Set α) : Matroid X := (M ↾ X).comap (↑)

@[simp] theorem restrictSubtype_ground : (M.restrictSubtype X).E = univ := by
  simp [restrictSubtype]

@[simp] theorem restrictSubtype_indep_iff {I : Set X} :
    (M.restrictSubtype X).Indep I ↔ M.Indep ((↑) '' I) := by
  simp [restrictSubtype, Subtype.val_injective.injOn I]

theorem restrictSubtype_indep_iff_of_subset (hIX : I ⊆ X) :
    (M.restrictSubtype X).Indep (X ↓∩ I) ↔ M.Indep I := by
  rw [restrictSubtype_indep_iff, image_preimage_eq_iff.2]; simpa

theorem restrictSubtype_inter_indep_iff :
    (M.restrictSubtype X).Indep (X ↓∩ I) ↔ M.Indep (X ∩ I) := by
  simp [restrictSubtype, Subtype.val_injective.injOn]

theorem eq_of_restrictSubtype_eq (hM : M.E = E) (hN : N.E = E)
    (h : M.restrictSubtype E = N.restrictSubtype E) : M = N := by
  subst hM
  refine eq_of_indep_iff_indep_forall (by rw [hN]) (fun I hI ↦ ?_)
  rwa [← restrictSubtype_indep_iff_of_subset hI, h, restrictSubtype_indep_iff_of_subset]

@[simp] theorem restrictSubtype_dual : (M.restrictSubtype M.E)✶ = M✶.restrictSubtype M.E := by
  rw [restrictSubtype, ← comapOn_preimage_eq, comapOn_dual_eq_of_bijOn, restrict_ground_eq_self,
    ← dual_ground, comapOn_preimage_eq, restrictSubtype, restrict_ground_eq_self]
  exact ⟨by simp [MapsTo], Subtype.val_injective.injOn _, by simp [SurjOn, Subset.rfl]⟩

theorem restrictSubtype_dual' (hM : M.E = E) : (M.restrictSubtype E)✶ = M✶.restrictSubtype E := by
  rw [← hM, restrictSubtype_dual]

end restrictSubtype
