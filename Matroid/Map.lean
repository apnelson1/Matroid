import Matroid.Constructions.Basic
import Matroid.ForMathlib.Function
import Matroid.ForMathlib.Logic_Embedding_Set
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
injectivity. This would be nice. It might be easier than the full strength of the bipartite graph
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

section Image

/-- Given an injective function `f` on `M.E`, the isomorphic copy of `M` whose independent sets
are the images of those in `M`. Implicitly defined using the comap of an inverse function. -/
def map (M : Matroid α) (f : α → β) (hf : InjOn f M.E) : Matroid β :=
  IndepMatroid.matroid <| IndepMatroid.ofExistsMatroid
  (E := f '' M.E)
  (Indep := fun I ↦ ∃ I₀, M.Indep I₀ ∧ I = f '' I₀)
  (hM := by
    obtain (_ | _) := isEmpty_or_nonempty α
    · exact ⟨emptyOn β, by simp⟩
    refine ⟨M.comapOn _ (Function.invFunOn f M.E), rfl, fun I ↦ ?_⟩
    simp only [comapOn_indep_iff]
    refine ⟨fun ⟨h, _, hs⟩ ↦ ⟨_, h, Eq.symm <| SurjOn.image_invFun_image_eq fun x hx ↦ hs hx ⟩, ?_⟩
    rintro ⟨I, hI, rfl⟩
    rw [InjOn.invFunOn_image hf hI.subset_ground, and_iff_right hI,
      and_iff_right <| (invFunOn_injOn_image f M.E).mono (image_subset f hI.subset_ground)]
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, hI.subset_ground hy, rfl⟩ )

/-- Map a matroid `M` across an embedding. -/
def mapEmbedding (M : Matroid α) (f : α ↪ β) : Matroid β := M.map f <| f.injective.injOn _

def mapEquiv (M : Matroid α) (f : α ≃ β) : Matroid β := M.mapEmbedding f.toEmbedding

@[simp] theorem map_ground (M : Matroid α) (f : α → β) (hf : InjOn f M.E) :
    (M.map f hf).E = f '' M.E := rfl

@[simp] theorem map_indep_iff {M : Matroid α} {f : α → β} {hf : InjOn f M.E} {I : Set β} :
    (M.map f hf).Indep I ↔ ∃ I₀, M.Indep I₀ ∧ I = f '' I₀ := by
  simp [map, IndepMatroid.ofExistsMatroid]

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

end Image

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

section MapRel





    -- rw [extend_apply' _ _ _ (by simpa [embeddingOfSubset])] at hxy

    -- · obtain (rfl | ⟨y₀,rfl⟩) := aux y
    --   · rfl
    --   ·
    -- obtain
    -- rintro ⟨x, (rfl | hx)⟩ ⟨y, (rfl | hy)⟩ hxy; rfl

    -- · have :
      -- rw [extend_apply', extend_apply'] at hxy

-- theorem aux {α β : Type*} {s t : Set β} {f : s → α} {g : t → α} (a₀ : s) :
--   ∃

-- noncomputable def exhaust {α β : Type*} {s t : Set β} (f : s ↪ α) (g : t ↪ α)
--     [DecidablePred (· ∈ range g)] [DecidablePred (· ∈ s)] (b₀ : s) : ℕ → α ⊕ β
--   | 0 => .inr b₀.1
--   | n+1 => (exhaust f g b₀ n).rec
--     (fun a ↦ if ha : a ∈ range g then .inr (Classical.choose (mem_range.1 ha)).1 else .inl a)
--     (fun b ↦ if hb : b ∈ s then .inl (f ⟨b,hb⟩) else .inr b)


-- mutual
--   def repeat_left {α β : Type u} (f : α → β) (g : β → α) (a₀ : α) : ℕ → α
--     | 0 => a₀
--     | n+1 => g (repeat_right f g a₀ n)

--   def repeat_right {α β : Type u} (f : α → β) (g : β → α) (a₀ : α) : ℕ → β
--     | 0 => f a₀
--     | n+1 => f (repeat_left f g a₀ n)
-- end

-- def repeat_modify {α β : Type u} (f : α → β) (g : β → α) (a₀ : α) (b : β)
--     [DecidablePred fun n ↦ repeat_right f g a₀ n = b] [Decidable (∃ i, repeat_right f g a₀ i = b)] :
--     α :=
--   if h : ∃ i, repeat_right f g a₀ i = b then (repeat_left f g a₀) (Nat.find h) else g b


-- def ImageIndep (M : Matroid α) (r : α → β → Prop) (I : Set β) :=
--   ∃ (f : β → Option α), (∀ b ∈ I, ∃ a ∈ f b, r a b) ∧ (InjOn f I) ∧ M.Indep (some ⁻¹' (f '' I))


-- def mapRelIndepMatroid' (M : Matroid α) (r : α → β → Prop) : IndepMatroid β where
--   E := univ
--   Indep I := ∃ (f : Option β → Option α), ∀ a ∈ I, f (some a) ≠ none ∧ InjOn f (some '' I)
--     ∧ M.Indep (some ⁻¹' (f '' (some '' I)))
-- noncomputable def exhaust' (f g : α → Option β) (a₀ : α)
--   [DecidablePred (∃ a, g a = some ·)] : ℕ → Option (α ⊕ β)
--   | 0 => some <| .inl a₀
--   | n+1 => (exhaust' f g a₀ n).rec none (Sum.rec
--       (fun a ↦ (f a).rec none (fun b ↦ some (.inr b)))
--       fun b ↦ if h : ∃ a, g a = some b then some (.inl (Classical.choose h)) else none)

-- def inj' (f : α → Option β) := InjOn f ({x | f x ≠ none})

-- theorem exhaust_left (f g : α → Option β) (a₀ : α) [DecidablePred (∃ a, g a = some ·)]
--     {i : ℕ} {a : α} {b : β} (hfa : f a = some b) (hia : exhaust' f g a₀ i = some (.inl a)) :
--     exhaust' f g a₀ (i+1) = some (.inr b) := by
--   induction' i using Nat.recAux with i hi
--   · simp only [exhaust', Option.some.injEq, Sum.inl.injEq] at hia ⊢
--     simp [exhaust, hia, hfa]
--   simp [exhaust'] at hia
--   simp only [exhaust', Nat.add_eq, add_zero] at hia hi ⊢




-- theorem foo (f g : α → Option β) [DecidablePred (∃ a, g a = some ·)] (a₀ : α) (ha₀ : f a₀ ≠ none)
--     (h_exhaust : ∀ i, exhaust' f g a₀ i ≠ none) (h_inj : InjOn g ({x | g x ≠ none})) :
--     ∃ (g' : α → Option β), (g' a₀ ≠ none) ∧ (∀ a, g' a = none → g a = none) ∧
--       InjOn g' ({x | g' x ≠ none}) := by
--   classical
--   refine ⟨fun a ↦ if ∃ i, exhaust' f g a₀ i = some (.inl a) then f a else g a, ?_, ?_, ?_⟩
--   · simp only [ne_eq]; rwa [if_pos ⟨0, rfl⟩]
--   · intro a
--     simp only
--     split_ifs with h h
--     ·





-- noncomputable def flipAt {α β : Type*} {s t : Set β} (f : s ↪ α) (g : t ↪ α)
--     [DecidablePred (· ∈ range g)] [DecidablePred (· ∈ s)] (b₀ : s) (hb₀ : b₀.1 ∉ t) :
--     ↑(insert b₀.1 t) ↪ α where
--   toFun x := if h : ∃ i, exhaust f g b₀ i = .inr x then (Classical.choose h).
--   inj' := _

-- def mapRelIndepMatroid (M : Matroid α) (r : α → β → Prop) : IndepMatroid β where
--   E := univ
--   Indep I := ∃ (i : I ↪ α), M.Indep (range i) ∧ ∀ e, r (i e) e
--   indep_empty := ⟨⟨fun x ↦ (not_mem_empty x.1 x.2).elim, fun x ↦ (not_mem_empty x.1 x.2).elim⟩,
--     by convert M.empty_indep; simp, fun x ↦ (not_mem_empty x.1 x.2).elim⟩
--   indep_subset := by
--     rintro I J ⟨e, hei, her⟩ hIJ
--     refine ⟨(embeddingOfSubset I J hIJ).trans e, hei.subset ?_, fun ⟨x,hx⟩ ↦ her ⟨x, hIJ hx⟩ ⟩
--     rw [Embedding.range_trans]
--     apply image_subset_range
--   indep_aug := by
--     simp_rw [mem_maximals_iff, mem_setOf, not_and, not_forall, exists_prop]
--     rintro I B hI' hI ⟨⟨g, hg, hgr⟩, hBmax⟩
--     obtain ⟨K, ⟨eK, heK, heKr⟩, hIK, hIne⟩ := hI hI'
--     obtain ⟨b, hbK, hbI⟩ := exists_of_ssubset (hIK.ssubset_of_ne hIne)
--     set a := eK ⟨b,hbK⟩ with ha_def
--     set f := (embeddingOfSubset _ _ hIK).trans eK with hf_def

--     have haf : a ∉ range f := by
--       rintro ⟨⟨a₀,ha₀I⟩, ha₀ : eK _ = _⟩
--       simp_rw [ha_def, eK.apply_eq_iff_eq, ← Subtype.val_inj, embeddingOfSubset_apply_coe] at ha₀
--       subst ha₀; contradiction

--     have hab : r a b := by apply heKr

--     by_cases hac : ∃ c, r a c ∧ c ∈ B \ I
--     · obtain ⟨c, hac, hc⟩ := hac
--       refine ⟨c, hc, Subtype.embeddingInsert f hc.2 haf, heK.subset ?_, ?_⟩
--       · rw [Subtype.range_embeddingInsert, ha_def, hf_def, insert_subset_iff]
--         refine ⟨mem_range_self _, ?_⟩
--         rw [Embedding.range_trans]
--         apply image_subset_range
--       rintro ⟨x, (rfl | hxI)⟩
--       · rw [Subtype.embeddingInsert_apply']
--         · exact hac
--         exact hc.2
--       rw [Subtype.embeddingInsert_apply_mem _ _ _ (by simpa)]
--       exact heKr ⟨x, hIK hxI⟩

--     push_neg at hac

--     -- have hag : a ∉ range g := by
--     --   rintro ⟨a₀, ha₀⟩
--     --   -- have := hgr a₀
--     --   apply hac a₀ (by rw [← ha₀]; apply hgr)

--     have hbB : b ∉ B := fun hbB ↦ hac b hab ⟨hbB, hbI⟩

--     by_cases hag : a ∈ range g
--     · obtain ⟨⟨b₀,hb₀B⟩, hb₀⟩ := hag
--       have hrb₀ : r a b₀ := by rw [← hb₀]; apply hgr
--       have hb₀I : b₀ ∈ I := by_contra fun h' ↦ hac _ hrb₀ ⟨hb₀B, h'⟩
--       set a₀ := f ⟨b₀, hb₀I⟩ with ha₀_def
--       by_cases ha₀ : a₀ ∈ range g
--       · obtain ⟨b₁, hb₁⟩ := ha₀
--         -- define `f'` from `f` on `I ∪ {b₁}` by mapping `b₀` to `a` and `b₁` to `a₀`.




--     set g' := Subtype.embeddingInsert g (a := b) (b := a) hbB
--     -- have := @hBmax (insert b B)




    -- by_contra! hcon



    -- have ha_nbr : ∀ c, r a c → c ∈ B := by
    --   refine fun c hac ↦ by_contra fun hcB ↦ ?_
    --   rw [@hBmax (insert c B) ?_ (subset_insert _ _)] at hcB
    --   · simp at hcB
    --   have : Subtype.emb



      -- rw [@hBmax (insert c B) ?_ (subset_insert _ _)]; exact mem_insert _ _
      -- refine ⟨Subtype.embeddingInsert g


    -- obtain ⟨I, i, hIX, hIXne⟩ := hI hI'
    -- by_contra! hcon
    -- have hB : ∀ {x y}, y ∈ B → r x y → x ∈ range f := by
    --   rw [← diff_union_inter B I]
    --   rintro x y (hy | hy) hXY
    --   · by_contra hx'
    --     specialize hcon _ hy (Subtype.embeddingInsert f hy.2 hx')
    --     simp at hcon







    -- simp [mem_maximals_iff]


    -- rintro I B ⟨eI, heI, heIr⟩ hnotmax hmax
    -- by_contra! hcon
    -- push_neg at hcon
  -- indep_maximal := _
  -- subset_ground := _

end MapRel
