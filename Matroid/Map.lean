import Matroid.ForMathlib.Function
import Mathlib.Data.Matroid.Constructions
import Matroid.ForMathlib.MatroidBasic

open Set.Notation

/-!
# Maps between matroids

This file defines maps and comaps, which move a matroid on one type to a matroid on another
using a function between the types. The constructions are (up to isomorphism)
just combinations of restrictions and parallel extensions, so are not difficult.
Isomorphism itself will be defined in future additions.

Because a matroid `M : Matroid α` is defined with am embedded ground set `M.E : Set α`
which contains all the structure of `M`, there are several types of map and comap
one could reasonably ask for;
for instance, we could map `M : Matroid α` to a `Matroid β` using either
a function `f : α → β`, a function `f : ↑M.E → β` or indeed a function `f : ↑M.E → ↑E`
for some `E : Set β`. We attempt to give definitions that capture most reasonable use cases.

## Main definitions

In the definitions below, `M` and `N` are matroids on `α` and `β` respectively.

* For `f : α → β`, `Matroid.comap N f` is the matroid on `α` with ground set `f ⁻¹' N.E`
  in which each `I` is independent if and only if `f` is injective on `I` and
  `f '' I` is independent in `N`.
  (If `x` is a nonloop of `N`, then `f ⁻¹' {x}` is a parallel class of `N.comap f`.)

* `Matroid.comapOn N f E` is the restriction of `N.comap f` to `E` for some `E : Set α`.

* For an embedding `f : M.E ↪ β` defined on the subtype `↑M.E`,
  `Matroid.mapSetEmbedding M f` is the matroid on `β` with ground set `range f`
  whose independent sets are the images of those in `M`. This matroid is isomorphic to `M`.

* For a function `f : α → β` and a proof `hf` that `f` is injective on `M.E`,
  `Matroid.map f hf` is the matroid on `β` with ground set `f '' M.E`
  whose independent sets are the images of those in `M`. This matroid is isomorphic to `M`,
  and does not depend on the values `f` takes outside `M.E`.

* `Matroid.mapEmbedding f` is a version of `Matroid.map` where `f : α ↪ β` is a bundled embedding.
  It is defined separately because the global injectivity of `f` gives some nicer `simp` lemmas.

* `Matroid.mapEquiv f` is a version of `Matroid.map` where `f : α ≃ β` is a bundled equivalence.
  It is defined separately because we get even nicer `simp` lemmas.

* `Matroid.mapSetEquiv f` is a version of `Matroid.map` where `f : M.E ≃ E` is an equivalence on
  subtypes. It gives a matroid on `β` with ground set `E`.

* For `X : Set α`, `Matroid.restrictSubtype M X` is the `Matroid X` with ground set
  `univ : Set X` that is isomorphic to `M ↾ X`.

## Implementation details

The definition of `comap` is the only place where we need to actually define a matroid from scratch.
After `comap` is defined, we can define `map` and its variants indirectly in terms of `comap`.

If `f : α → β` is injective on `M.E`, the independent sets of `M.map f hf` are the images of
the independent set of `M`; i.e. `(M.map f hf).Indep I ↔ ∃ I₀, M.Indep I₀ ∧ I = f '' I₀`.
But if `f` is globally injective, we can phrase this more directly;
indeed, `(M.map f _).Indep I ↔ M.Indep (f ⁻¹' I) ∧ I ⊆ range f`.
If `f` is an equivalence we have `(M.map f _).Indep I ↔ M.Indep (f.symm '' I)`.
In order that these stronger statements can be `@[simp]`,
we define `mapEmbedding` and `mapEquiv` separately from `map`.

## Notes

For finite matroids, both maps and comaps are a special case of a construction of
Perfect (1969) in which a matroid structure can be transported across an arbitrary
bipartite graph that doesn't correspond to a function at all [See Oxley, Thm 11.2.12].
It would have been nice to use this more general construction as a basis for the definition
of both `Matroid.map` and `Matroid.comap`.

Unfortunately, we can't do this, because the construction doesn't extend to infinite matroids.
Specifically, if `M₁` and `M₂` are matroids on the same type `α`,
and `f` is the natural function from `α ⊕ α` to `α`,
then the images under `f` of the independent sets of the direct sum `M₁ ⊕ M₂` are
the independent sets of a matroid if and only if the union of `M₁` and `M₂` is a matroid,
and unions do not exist for some pairs of infinite matroids: see [1].
For this reason, `Matroid.map` requires injectivity to be well-defined in general.

## References

[1] : E. Aigner-Horev, J. Carmesin, J. Fröhlic, Infinite Matroid Union, arXiv:1111.0602 [math.CO]
-/

universe u

open Set Function

namespace Matroid
variable {α β : Type*} {f : α → β} {E I s : Set α} {M : Matroid α} {N : Matroid β}

/-- The pullback of a matroid on `β` by a function `f : α → β` to a matroid on `α`.
Elements with the same image are parallel and the ground set is `f ⁻¹' M.E`. -/
def comap (N : Matroid β) (f : α → β) : Matroid α :=
  IndepMatroid.matroid <| IndepMatroid.mk
  ( E := f ⁻¹' N.E )
  ( Indep := fun I ↦ N.Indep (f '' I) ∧ InjOn f I )
  ( indep_empty := by simp )
  ( indep_subset := fun I J h hIJ ↦ ⟨h.1.subset (image_subset _ hIJ), InjOn.mono hIJ h.2⟩ )
  ( indep_aug := by
    rintro I B ⟨hI, hIinj⟩ hImax hBmax
    simp only [mem_maximals_iff, mem_setOf_eq, hI, hIinj, and_self, and_imp,
      true_and, not_forall, exists_prop, exists_and_left] at hImax hBmax

    obtain ⟨I', hI', hI'inj, hII', hne⟩ := hImax

    have h₁ : ¬(N ↾ range f).Base (f '' I) := by
      refine fun hB ↦ hne ?_
      have h_im := hB.eq_of_subset_indep (by simpa) (image_subset _ hII')
      rwa [hI'inj.image_eq_image_iff hII' Subset.rfl] at h_im

    have h₂ : (N ↾ range f).Base (f '' B) := by
      refine Indep.base_of_forall_insert (by simpa using hBmax.1.1) ?_
      rintro _ ⟨⟨e, heB, rfl⟩, hfe⟩ hi
      rw [restrict_indep_iff, ← image_insert_eq] at hi
      have hinj : InjOn f (insert e B) := by
        rw [injOn_insert (fun heB ↦ hfe (mem_image_of_mem f heB))]; exact ⟨hBmax.1.2, hfe⟩
      rw [hBmax.2 hi.1 hinj <| subset_insert _ _] at hfe; simp at hfe


    obtain ⟨_, ⟨⟨e, he, rfl⟩, he'⟩, hei⟩ := Indep.exists_insert_of_not_base (by simpa) h₁ h₂
    have heI : e ∉ I := fun heI ↦ he' (mem_image_of_mem f heI)
    rw [← image_insert_eq, restrict_indep_iff] at hei
    exact ⟨e, ⟨he, heI⟩, hei.1, (injOn_insert heI).2 ⟨hIinj, he'⟩⟩)
  ( indep_maximal := by

    rintro X - I ⟨hI, hIinj⟩ hIX
    obtain ⟨J, hJ⟩ := (N ↾ range f).existsMaximalSubsetProperty_indep (f '' X) (by simp)
      (f '' I) (by simpa) (image_subset _ hIX)

    simp only [restrict_indep_iff, image_subset_iff, mem_maximals_iff, mem_setOf_eq, and_imp] at hJ

    obtain ⟨J₀, hIJ₀, hJ₀X, hbj⟩ := hIinj.bijOn_image.exists_extend_of_subset hIX
      (image_subset f hJ.1.2.1) (image_subset_iff.2 <| preimage_mono hJ.1.2.2)

    have him := hbj.image_eq; rw [image_preimage_eq_of_subset hJ.1.1.2] at him; subst him
    use J₀
    simp only [mem_maximals_iff, mem_setOf_eq, hJ.1.1.1, hbj.injOn, and_self, hIJ₀,
      hJ₀X, and_imp, true_and]
    intro K hK hinj hIK hKX hJ₀K
    rw [← hinj.image_eq_image_iff hJ₀K Subset.rfl, hJ.2 hK (image_subset_range _ _)
      (fun e he ↦ ⟨e, hIK he, rfl⟩) (image_subset _ hKX) (image_subset _ hJ₀K)] )
  (subset_ground := fun I hI e heI  ↦ hI.1.subset_ground ⟨e, heI, rfl⟩ )

@[simp] lemma comap_indep_iff : (N.comap f).Indep I ↔ N.Indep (f '' I) ∧ InjOn f I := Iff.rfl

@[simp] lemma comap_ground_eq (N : Matroid β) (f : α → β) : (N.comap f).E = f ⁻¹' N.E := rfl

@[simp] lemma comap_dep_iff :
    (N.comap f).Dep I ↔ N.Dep (f '' I) ∨ (N.Indep (f '' I) ∧ ¬ InjOn f I) := by
  rw [Dep, comap_indep_iff, not_and, comap_ground_eq, Dep, image_subset_iff]
  refine ⟨fun ⟨hi, h⟩ ↦ ?_, ?_⟩
  · rw [and_iff_left h, ← imp_iff_not_or]
    exact fun hI ↦ ⟨hI, hi hI⟩
  rintro (⟨hI, hIE⟩ | hI)
  · exact ⟨fun h ↦ (hI h).elim, hIE⟩
  rw [iff_true_intro hI.1, iff_true_intro hI.2, implies_true, true_and]
  simpa using hI.1.subset_ground

@[simp] lemma comap_id (N : Matroid β) : N.comap id = N :=
  eq_of_indep_iff_indep_forall rfl <| by simp [injective_id.injOn]

lemma comap_indep_iff_of_injOn (hf : InjOn f (f ⁻¹' N.E)) :
    (N.comap f).Indep I ↔ N.Indep (f '' I) := by
  rw [comap_indep_iff, and_iff_left_iff_imp]
  refine fun hi ↦ hf.mono <| subset_trans ?_ (preimage_mono hi.subset_ground)
  apply subset_preimage_image

@[simp] lemma comap_emptyOn (f : α → β) : comap (emptyOn β) f = emptyOn α := by
  simp [← ground_eq_empty_iff]

@[simp] lemma comap_loopyOn (f : α → β) (E : Set β) : comap (loopyOn E) f = loopyOn (f ⁻¹' E) := by
  rw [eq_loopyOn_iff]; aesop

@[simp] lemma comap_basis_iff {I X : Set α} :
    (N.comap f).Basis I X ↔ N.Basis (f '' I) (f '' X) ∧ I ⊆ X ∧ I.InjOn f := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨hI, hinj⟩ := comap_indep_iff.1 h.indep
    refine ⟨hI.basis_of_forall_insert (image_subset f h.subset) fun e he ↦ ?_, h.subset, hinj⟩
    simp only [mem_diff, mem_image, not_exists, not_and, and_imp, forall_exists_index,
      forall_apply_eq_imp_iff₂] at he
    obtain ⟨⟨e, heX, rfl⟩, he⟩ := he
    have heI : e ∉ I := fun heI ↦ (he e heI rfl)
    replace h := h.insert_dep ⟨heX, heI⟩
    simp only [comap_dep_iff, image_insert_eq, or_iff_not_imp_right, injOn_insert heI,
      hinj, mem_image, not_exists, not_and, true_and, not_forall, Classical.not_imp, not_not] at h
    exact h (fun _ ↦ he)
  refine Indep.basis_of_forall_insert ?_ h.2.1 fun e ⟨heX, heI⟩ ↦ ?_
  · simp [comap_indep_iff, h.1.indep, h.2]
  have hIE : insert e I ⊆ (N.comap f).E := by
      simp_rw [comap_ground_eq, ← image_subset_iff]
      exact (image_subset _ (insert_subset heX h.2.1)).trans h.1.subset_ground
  suffices N.Indep (insert (f e) (f '' I)) → ∃ x ∈ I, f x = f e
    by simpa [← not_indep_iff hIE, injOn_insert heI, h.2.2, image_insert_eq]
  exact h.1.mem_of_insert_indep (mem_image_of_mem f heX)

@[simp] lemma comap_basis'_iff {I X : Set α} :
    (N.comap f).Basis' I X ↔ N.Basis' (f '' I) (f '' X) ∧ I ⊆ X ∧ I.InjOn f := by
  simp only [basis'_iff_basis_inter_ground, comap_ground_eq, comap_basis_iff, image_inter_preimage,
    subset_inter_iff, ← and_assoc, and_congr_left_iff, and_iff_left_iff_imp, and_imp]
  exact fun _ h _ ↦ (image_subset_iff.1 h.indep.subset_ground)

/-- The pullback of a matroid on `β` by a function `f : α → β` to a matroid on `α`,
restricted to a ground set `E`. Elements with the same image are parallel. -/
def comapOn (N : Matroid β) (E : Set α) (f : α → β) : Matroid α := (N.comap f) ↾ E

lemma comapOn_preimage_eq (N : Matroid β) (f : α → β) : N.comapOn (f ⁻¹' N.E) f = N.comap f := by
  rw [comapOn, restrict_eq_self_iff]; rfl

@[simp] lemma comapOn_indep_iff :
    (N.comapOn E f).Indep I ↔ (N.Indep (f '' I) ∧ InjOn f I ∧ I ⊆ E) := by
  simp [comapOn, and_assoc]

@[simp] lemma comapOn_ground_eq : (N.comapOn E f).E = E := rfl

lemma comapOn_base_iff {B E : Set α} :
    (N.comapOn E f).Base B ↔ N.Basis' (f '' B) (f '' E) ∧ B ⊆ E ∧ B.InjOn f := by
  rw [comapOn, base_restrict_iff', comap_basis'_iff]

lemma comapOn_base_iff_of_surjOn {E : Set α} (h : SurjOn f E N.E) {B : Set α} :
    (N.comapOn E f).Base B ↔ (N.Base (f '' B) ∧ B ⊆ E ∧ InjOn f B) := by
  simp_rw [comapOn_base_iff, and_congr_left_iff, and_imp,
    basis'_iff_basis_inter_ground, inter_eq_self_of_subset_right h, basis_ground_iff, implies_true]

lemma comapOn_base_iff_of_bijOn {E : Set α} (h : BijOn f E N.E) {B : Set α} :
    (N.comapOn E f).Base B ↔ N.Base (f '' B) ∧ B ⊆ E := by
  rw [← and_iff_left_of_imp (Base.subset_ground (M := N.comapOn E f) (B := B)),
    comapOn_ground_eq, and_congr_left_iff]
  suffices h' : B ⊆ E → InjOn f B from fun hB ↦
    by simp [hB, comapOn_base_iff_of_surjOn h.surjOn, h']
  exact fun hBE ↦ h.injOn.mono hBE

lemma comapOn_dual_eq_of_bijOn {E : Set α} (h : BijOn f E N.E) :
    (N.comapOn E f)✶ = N✶.comapOn E f := by
  refine eq_of_base_iff_base_forall (by simp) (fun B hB ↦ ?_)
  rw [comapOn_base_iff_of_bijOn (by simpa), dual_base_iff, comapOn_base_iff_of_bijOn h,
    dual_base_iff _, comapOn_ground_eq, and_iff_left diff_subset, and_iff_left (by simpa),
    h.injOn.image_diff_subset (by simpa), h.image_eq]
  exact (h.mapsTo.mono_left (show B ⊆ E by simpa)).image_subset

section mapSetEmbedding

/-- Map a matroid `M` to an isomorphic copy in `β` using an embedding `M.E ↪ β`. -/
def mapSetEmbedding (M : Matroid α) (f : M.E ↪ β) : Matroid β := Matroid.ofExistsMatroid
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
    rw [← image_image, InjOn.invFunOn_image f.injective.injOn (subset_univ _),
      preimage_image_eq _ f.injective, and_iff_left_iff_imp]
    rintro - x hx y hy
    simp only [EmbeddingLike.apply_eq_iff_eq, Subtype.val_inj]
    exact (invFunOn_injOn_image f univ) (image_subset f (subset_univ I) hx)
      (image_subset f (subset_univ I) hy) )

@[simp] lemma mapSetEmbedding_ground (M : Matroid α) (f : M.E ↪ β) :
    (M.mapSetEmbedding f).E = range f := rfl

@[simp] lemma mapSetEmbedding_indep_iff {f : M.E ↪ β} {I : Set β} :
    (M.mapSetEmbedding f).Indep I ↔ M.Indep ↑(f ⁻¹' I) ∧ I ⊆ range f := Iff.rfl

lemma Indep.exists_eq_image_of_mapSetEmbedding {f : M.E ↪ β} {I : Set β}
    (hI : (M.mapSetEmbedding f).Indep I) : ∃ (I₀ : Set M.E), M.Indep I₀ ∧ I = f '' I₀ :=
  ⟨f ⁻¹' I, hI.1, Eq.symm <| image_preimage_eq_of_subset hI.2⟩

lemma mapSetEmbedding_indep_iff' {f : M.E ↪ β} {I : Set β} :
    (M.mapSetEmbedding f).Indep I ↔ ∃ (I₀ : Set M.E), M.Indep ↑I₀ ∧ I = f '' I₀ := by
  simp only [mapSetEmbedding_indep_iff, subset_range_iff_exists_image_eq]
  constructor
  · rintro ⟨hI, I, rfl⟩
    exact ⟨I, by rwa [preimage_image_eq _ f.injective] at hI, rfl⟩
  rintro ⟨I, hI, rfl⟩
  rw [preimage_image_eq _ f.injective]
  exact ⟨hI, _, rfl⟩

end mapSetEmbedding

section map

/-- Given an injective function `f` on `M.E`, the isomorphic copy of `M` whose independent sets
are the images of those in `M`. -/
def map (M : Matroid α) (f : α → β) (hf : InjOn f M.E) : Matroid β := Matroid.ofExistsMatroid
  (E := f '' M.E)
  (Indep := fun I ↦ ∃ I₀, M.Indep I₀ ∧ I = f '' I₀)
  (hM := by
    refine ⟨M.mapSetEmbedding ⟨_, hf.injective⟩, by simp, fun I ↦ ?_⟩
    simp_rw [mapSetEmbedding_indep_iff', Embedding.coeFn_mk, restrict_apply,
      ← image_image f Subtype.val, Subtype.exists_set_subtype (p := fun J ↦ M.Indep J ∧ I = f '' J)]
    exact ⟨fun ⟨I₀, _, hI₀⟩ ↦ ⟨I₀, hI₀⟩, fun ⟨I₀, hI₀⟩ ↦ ⟨I₀, hI₀.1.subset_ground, hI₀⟩⟩)

@[simp] lemma map_ground (M : Matroid α) (f : α → β) (hf) : (M.map f hf).E = f '' M.E := rfl

@[simp] lemma map_indep_iff {hf} {I : Set β} :
    (M.map f hf).Indep I ↔ ∃ I₀, M.Indep I₀ ∧ I = f '' I₀ := Iff.rfl

lemma Indep.map (hI : M.Indep I) (f : α → β) (hf) : (M.map f hf).Indep (f '' I) :=
  map_indep_iff.2 ⟨I, hI, rfl⟩

lemma map_image_indep_iff {hf} {I : Set α} (hI : I ⊆ M.E) :
    (M.map f hf).Indep (f '' I) ↔ M.Indep I := by
  rw [map_indep_iff]
  refine ⟨fun ⟨J, hJ, hIJ⟩ ↦ ?_, fun h ↦ ⟨I, h, rfl⟩ ⟩
  rw [hf.image_eq_image_iff hI hJ.subset_ground] at hIJ; rwa [hIJ]

@[simp] lemma map_base_iff (M : Matroid α) (f : α → β) (hf) {B : Set β} :
    (M.map f hf).Base B ↔ ∃ B₀, M.Base B₀ ∧ B = f '' B₀ := by
  rw [base_iff_maximal_indep, map_indep_iff]
  refine ⟨fun ⟨h, hB⟩ ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨B₀, hB₀, rfl⟩ := h
    refine ⟨_, hB₀.base_of_maximal fun J hJ hB₀J ↦ ?_, rfl⟩
    specialize hB (f '' J) ((map_image_indep_iff hJ.subset_ground).2 hJ) (image_subset _ hB₀J)
    rwa [hf.image_eq_image_iff hB₀.subset_ground hJ.subset_ground] at hB
  obtain ⟨B₀, hB, rfl⟩ := h
  refine ⟨⟨B₀, hB.indep, rfl⟩, fun I hI hB₀I ↦ ?_⟩
  obtain ⟨I, hI', rfl⟩ := map_indep_iff.1 hI
  rw [hf.image_subset_image_iff hB.subset_ground hI'.subset_ground] at hB₀I
  rw [hB.eq_of_subset_indep hI' hB₀I]

lemma Base.map {B : Set α} (hB : M.Base B) {f : α → β} (hf) : (M.map f hf).Base (f '' B) := by
  rw [map_base_iff]; exact ⟨B, hB, rfl⟩

lemma map_dep_iff {hf} {D : Set β} :
    (M.map f hf).Dep D ↔ ∃ D₀, M.Dep D₀ ∧ D = f '' D₀ := by
  simp only [Dep, map_indep_iff, not_exists, not_and, map_ground, subset_image_iff]
  constructor
  · rintro ⟨h, D₀, hD₀E, rfl⟩
    exact ⟨D₀, ⟨fun hd ↦ h _ hd rfl, hD₀E⟩, rfl⟩
  rintro ⟨D₀, ⟨hD₀, hD₀E⟩, rfl⟩
  refine ⟨fun I hI h_eq ↦ ?_, ⟨_, hD₀E, rfl⟩⟩
  rw [hf.image_eq_image_iff hD₀E hI.subset_ground] at h_eq
  subst h_eq; contradiction

lemma map_image_base_iff {hf} {B : Set α} (hB : B ⊆ M.E) :
    (M.map f hf).Base (f '' B) ↔ M.Base B := by
  rw [map_base_iff]
  refine ⟨fun ⟨J, hJ, hIJ⟩ ↦ ?_, fun h ↦ ⟨B, h, rfl⟩⟩
  rw [hf.image_eq_image_iff hB hJ.subset_ground] at hIJ; rwa [hIJ]

lemma Basis.map {X : Set α} (hIX : M.Basis I X) {f : α → β} (hf) :
    (M.map f hf).Basis (f '' I) (f '' X) := by
  refine (hIX.indep.map f hf).basis_of_forall_insert (image_subset _ hIX.subset) ?_
  rintro _ ⟨⟨e,he,rfl⟩, he'⟩
  have hss := insert_subset (hIX.subset_ground he) hIX.indep.subset_ground
  rw [← not_indep_iff (by simpa [← image_insert_eq] using image_subset f hss)]
  simp only [map_indep_iff, not_exists, not_and]
  intro J hJ hins
  rw [← image_insert_eq, hf.image_eq_image_iff hss hJ.subset_ground] at hins
  obtain rfl := hins
  exact he' (mem_image_of_mem f (hIX.mem_of_insert_indep he hJ))

lemma map_basis_iff {I X : Set α} (f : α → β) (hf) (hI : I ⊆ M.E) (hX : X ⊆ M.E) :
    (M.map f hf).Basis (f '' I) (f '' X) ↔ M.Basis I X := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.map hf⟩
  obtain ⟨I', hI', hII'⟩ := map_indep_iff.1 h.indep
  rw [hf.image_eq_image_iff hI hI'.subset_ground] at hII'
  obtain rfl := hII'
  have hss := (hf.image_subset_image_iff hI hX).1 h.subset
  refine hI'.basis_of_maximal_subset hss (fun J hJ hIJ hJX ↦ ?_)
  have hIJ' := h.eq_of_subset_indep (hJ.map f hf) (image_subset f hIJ) (image_subset f hJX)
  rw [hf.image_eq_image_iff hI hJ.subset_ground] at hIJ'
  exact hIJ'.symm.subset

lemma map_basis_iff' {I X : Set β} {hf} :
    (M.map f hf).Basis I X ↔ ∃ I₀ X₀, M.Basis I₀ X₀ ∧ I = f '' I₀ ∧ X = f '' X₀ := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨I, hI, rfl⟩ := subset_image_iff.1 h.indep.subset_ground
    obtain ⟨X, hX, rfl⟩ := subset_image_iff.1 h.subset_ground
    rw [map_basis_iff _ _ hI hX] at h
    exact ⟨I, X, h, rfl, rfl⟩
  rintro ⟨I, X, hIX, rfl, rfl⟩
  exact hIX.map hf

@[simp] lemma map_dual {hf} : (M.map f hf)✶ = M✶.map f hf := by
  apply eq_of_base_iff_base_forall (by simp)
  simp only [dual_ground, map_ground, subset_image_iff, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, dual_base_iff']
  intro B hB
  simp_rw [← hf.image_diff_subset hB, map_image_base_iff diff_subset,
    map_image_base_iff (show B ⊆ M✶.E from hB), dual_base_iff hB, and_iff_left_iff_imp]
  exact fun _ ↦ ⟨B, hB, rfl⟩

@[simp] lemma map_emptyOn (f : α → β) : (emptyOn α).map f (by simp) = emptyOn β := by
  simp [← ground_eq_empty_iff]

@[simp] lemma map_loopyOn (f : α → β) (hf) : (loopyOn E).map f hf = loopyOn (f '' E) := by
  simp [eq_loopyOn_iff]

@[simp] lemma map_freeOn (f : α → β) (hf) : (freeOn E).map f hf = freeOn (f '' E) := by
  rw [← dual_inj]; simp


end map

section mapSetEquiv

/-- Map `M : Matroid α` to a `Matroid β` with ground set `E` using an equivalence `M.E ≃ E`.
Defined using `Matroid.ofExistsMatroid` for better defeq.  -/
def mapSetEquiv (M : Matroid α) {E : Set β} (e : M.E ≃ E) : Matroid β :=
  Matroid.ofExistsMatroid E (fun I ↦ (M.Indep ↑(e.symm '' (E ↓∩ I)) ∧ I ⊆ E))
  ⟨M.mapSetEmbedding (e.toEmbedding.trans <| Function.Embedding.subtype _), by
    have hrw : ∀ I : Set β, Subtype.val ∘ ⇑e ⁻¹' I = ⇑e.symm '' E ↓∩ I := fun I ↦ by ext; simp
    simp [Equiv.toEmbedding, Embedding.subtype, Embedding.trans, hrw]⟩

@[simp] lemma mapSetEquiv_indep_iff (M : Matroid α) {E : Set β} (e : M.E ≃ E) {I : Set β} :
    (M.mapSetEquiv e).Indep I ↔ M.Indep ↑(e.symm '' (E ↓∩ I)) ∧ I ⊆ E := Iff.rfl

@[simp] lemma mapSetEquiv.ground (M : Matroid α) {E : Set β} (e : M.E ≃ E) :
    (M.mapSetEquiv e).E = E := rfl

section mapEmbedding

/-- Map `M : Matroid α` across an embedding defined on all of `α` -/
def mapEmbedding (M : Matroid α) (f : α ↪ β) : Matroid β := M.map f f.injective.injOn

@[simp] lemma mapEmbedding_ground_eq (M : Matroid α) (f : α ↪ β) :
    (M.mapEmbedding f).E = f '' M.E := rfl

@[simp] lemma mapEmbedding_indep_iff {f : α ↪ β} {I : Set β} :
    (M.mapEmbedding f).Indep I ↔ M.Indep (f ⁻¹' I) ∧ I ⊆ range f := by
  rw [mapEmbedding, map_indep_iff]
  refine ⟨?_, fun ⟨h,h'⟩ ↦ ⟨f ⁻¹' I, h, by rwa [eq_comm, image_preimage_eq_iff]⟩⟩
  rintro ⟨I, hI, rfl⟩
  rw [preimage_image_eq _ f.injective]
  exact ⟨hI, image_subset_range _ _⟩

lemma Indep.mapEmbedding (hI : M.Indep I) (f : α ↪ β) : (M.mapEmbedding f).Indep (f '' I) := by
  simpa [preimage_image_eq I f.injective]

lemma Base.mapEmbedding {B : Set α} (hB : M.Base B) (f : α ↪ β) :
    (M.mapEmbedding f).Base (f '' B) := by
  rw [Matroid.mapEmbedding, map_base_iff]
  exact ⟨B, hB, rfl⟩

lemma Basis.mapEmbedding {X : Set α} (hIX : M.Basis I X) (f : α ↪ β) :
    (M.mapEmbedding f).Basis (f '' I) (f '' X) := by
  apply hIX.map

end mapEmbedding

section mapEquiv

variable {f : α ≃ β}

/-- Map `M : Matroid α` across an equivalence `α ≃ β` -/
def mapEquiv (M : Matroid α) (f : α ≃ β) : Matroid β := M.mapEmbedding f.toEmbedding

@[simp] lemma mapEquiv_ground_eq (M : Matroid α) (f : α ≃ β) :
    (M.mapEquiv f).E = f '' M.E := rfl

lemma mapEquiv_eq_map (f : α ≃ β) : M.mapEquiv f = M.map f f.injective.injOn := rfl

@[simp] lemma mapEquiv_indep_iff {I : Set β} : (M.mapEquiv f).Indep I ↔ M.Indep (f.symm '' I) := by
  rw [mapEquiv_eq_map, map_indep_iff]
  exact ⟨by rintro ⟨I, hI, rfl⟩; simpa, fun h ↦ ⟨_, h, by simp⟩⟩

@[simp] lemma mapEquiv_dep_iff {D : Set β} : (M.mapEquiv f).Dep D ↔ M.Dep (f.symm '' D) := by
  rw [mapEquiv_eq_map, map_dep_iff]
  exact ⟨by rintro ⟨I, hI, rfl⟩; simpa, fun h ↦ ⟨_, h, by simp⟩⟩

@[simp] lemma mapEquiv_base_iff {B : Set β} : (M.mapEquiv f).Base B ↔ M.Base (f.symm '' B) := by
  rw [mapEquiv_eq_map, map_base_iff]
  exact ⟨by rintro ⟨I, hI, rfl⟩; simpa, fun h ↦ ⟨_, h, by simp⟩⟩

end mapEquiv


section restrictSubtype

variable {E X I : Set α} {M N : Matroid α}

/-- Given `M : Matroid α` and `X : Set α`, the restriction of `M` to `X`,
viewed as a matroid on type `X` with ground set `univ`.
Always isomorphic to `M ↾ X`. If `X = M.E`, then isomorphic to `M`. -/
def restrictSubtype (M : Matroid α) (X : Set α) : Matroid X := (M ↾ X).comap (↑)

@[simp] lemma restrictSubtype_ground : (M.restrictSubtype X).E = univ := by
  simp [restrictSubtype]

@[simp] lemma restrictSubtype_indep_iff {I : Set X} :
    (M.restrictSubtype X).Indep I ↔ M.Indep ((↑) '' I) := by
  simp [restrictSubtype, Subtype.val_injective.injOn]

lemma restrictSubtype_indep_iff_of_subset (hIX : I ⊆ X) :
    (M.restrictSubtype X).Indep (X ↓∩ I) ↔ M.Indep I := by
  rw [restrictSubtype_indep_iff, image_preimage_eq_iff.2]; simpa

lemma restrictSubtype_inter_indep_iff :
    (M.restrictSubtype X).Indep (X ↓∩ I) ↔ M.Indep (X ∩ I) := by
  simp [restrictSubtype, Subtype.val_injective.injOn]

lemma eq_of_restrictSubtype_eq (hM : M.E = E) (hN : N.E = E)
    (h : M.restrictSubtype E = N.restrictSubtype E) : M = N := by
  subst hM
  refine eq_of_indep_iff_indep_forall (by rw [hN]) (fun I hI ↦ ?_)
  rwa [← restrictSubtype_indep_iff_of_subset hI, h, restrictSubtype_indep_iff_of_subset]

@[simp] lemma restrictSubtype_dual : (M.restrictSubtype M.E)✶ = M✶.restrictSubtype M.E := by
  rw [restrictSubtype, ← comapOn_preimage_eq, comapOn_dual_eq_of_bijOn, restrict_ground_eq_self,
    ← dual_ground, comapOn_preimage_eq, restrictSubtype, restrict_ground_eq_self]
  exact ⟨by simp [MapsTo], Subtype.val_injective.injOn, by simp [SurjOn, Subset.rfl]⟩

lemma restrictSubtype_dual' (hM : M.E = E) : (M.restrictSubtype E)✶ = M✶.restrictSubtype E := by
  rw [← hM, restrictSubtype_dual]

end restrictSubtype
