import Mathlib.Logic.Equiv.LocalEquiv
import Mathlib.Data.Set.Card
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.RowCol


open Set Function

theorem diff_eq_diff_iff_inter_eq_inter {s t r : Set α} : s \ t = s \ r ↔ (t ∩ s = r ∩ s) := by
  rw [←diff_inter_self_eq_diff, ←diff_inter_self_eq_diff (t := r)]
  refine' ⟨fun h ↦ _, fun h ↦ by rw [h]⟩
  rw [←diff_diff_cancel_left (inter_subset_right t s), h,
    diff_diff_cancel_left (inter_subset_right r s)]

@[simp] theorem Set.diff_inter_diff_right {s t r : Set α} : (t \ s) ∩ (r \ s) = (t ∩ r) \ s := by
  simp only [diff_eq, inter_assoc, inter_comm sᶜ, inter_self]

theorem inter_diff_right_comm {s t r : Set α} : (s ∩ t) \ r = (s \ r) ∩ t := by
  simp_rw [diff_eq, inter_right_comm]

theorem pair_diff_left {x y : α} (hne : x ≠ y) : ({x, y} : Set α) \ {x} = {y} := by
  rw [insert_diff_of_mem _ (by exact rfl : x ∈ {x}), diff_singleton_eq_self (by simpa)]

theorem pair_diff_right {x y : α} (hne : x ≠ y) : ({x, y} : Set α) \ {y} = {x} := by
  rw [pair_comm, pair_diff_left hne.symm]

@[simp] theorem pair_subset_iff {x y : α} {s : Set α} : {x,y} ⊆ s ↔ x ∈ s ∧ y ∈ s := by
  rw [insert_subset_iff, singleton_subset_iff]

theorem pair_subset {x y : α} {s : Set α} (hx : x ∈ s) (hy : y ∈ s) : {x,y} ⊆ s :=
  pair_subset_iff.2 ⟨hx,hy⟩

lemma Set.InjOn.image_eq_image_iff_of_subset {f : α → β} (h : InjOn f s) (h₁ : s₁ ⊆ s)
    (h₂ : s₂ ⊆ s) : f '' s₁ = f '' s₂ ↔ s₁ = s₂ :=
  ⟨fun h' ↦ by rw [←h.preimage_image_inter h₁, h', h.preimage_image_inter h₂], fun h' ↦ by rw [h']⟩

lemma Set.InjOn.image_subset_image_iff_of_subset {f : α → β} (h : InjOn f s) (h₁ : s₁ ⊆ s)
    (h₂ : s₂ ⊆ s) : f '' s₁ ⊆ f '' s₂ ↔ s₁ ⊆ s₂ := by
  refine' ⟨fun h' ↦ _, image_subset _⟩
  rw [←h.preimage_image_inter h₁, ←h.preimage_image_inter h₂]
  exact inter_subset_inter_left _ (preimage_mono h')

lemma Set.InjOn.image_diff' {f : α → β} (h : InjOn f s) :
    f '' (s \ t) = f '' s \ f '' (s ∩ t) := by
  refine' Set.ext (fun y ↦ ⟨_,_⟩)
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx.1, rfl⟩, fun h' ↦ hx.2 (h.mem_of_mem_image (inter_subset_left _ _) hx.1 h').2⟩
  rintro ⟨⟨x, hx, rfl⟩,h'⟩
  exact ⟨x, ⟨hx,fun hxt ↦ h' ⟨x, ⟨hx,hxt⟩, rfl⟩⟩, rfl⟩

lemma Set.InjOn.image_diff {f : α → β} (h : InjOn f s) (hst : t ⊆ s) :
    f '' (s \ t) = f '' s \ f '' t := by
  rw [h.image_diff', inter_eq_self_of_subset_right hst]

lemma Function.invFunOn_injOn_image_preimage [_root_.Nonempty α] (f : α → β) (S : Set α) :
    InjOn f ((invFunOn f S) '' (f '' S)) := by
  rintro _ ⟨_,⟨x,hx, rfl⟩,rfl⟩ _ ⟨_,⟨y,hy,rfl⟩,rfl⟩ h
  rw [invFunOn_eq (f := f) ⟨x, hx, rfl⟩, invFunOn_eq (f := f) ⟨y,hy,rfl⟩] at h
  rw [h]

-- lemma Set.InjOn.exists_injOn_superset {f : α → β} {s t : Set α} (hinj : InjOn f s) (hst : s ⊆ t) :
--     ∃ r, s ⊆ r ∧ r ⊆ t ∧ InjOn f r ∧ f '' r = f '' t := by

--   obtain (hα | hα) := isEmpty_or_nonempty α
--   · exact ⟨∅, by simp [eq_empty_of_isEmpty]⟩
--   set d := t ∩ (f ⁻¹' (f '' t \ f '' s)) with hd
--   set g := invFunOn f d with hg

--   have hdj : Disjoint (f '' s) (f '' d)
--   · rw [disjoint_iff_forall_ne]
--     rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ he
--     rw [hd, mem_inter_iff, mem_preimage, ←he] at hb
--     exact hb.2.2 (mem_image_of_mem f ha)

--   refine ⟨s ∪ g '' (f '' d), subset_union_left _ _, union_subset hst ?_, ?_, ?_⟩
--   · exact (f.invFunOn_image_image_subset _).trans (inter_subset_left _ _)
--   · rw [injOn_union, and_iff_right hinj, and_iff_right (invFunOn_injOn_image_preimage f _)]
--     · rintro x hx _ ⟨_,⟨y,hy,rfl⟩,rfl⟩ he
--       rw [hg, invFunOn_apply_eq (f := f) hy] at he
--       rw [disjoint_iff_forall_ne] at hdj
--       exact hdj (mem_image_of_mem f hx) (mem_image_of_mem f hy) he
--     · exact disjoint_of_subset_right (f.invFunOn_image_image_subset _) hdj.of_image
--   rw [image_union, subset_antisymm_iff, union_subset_iff, and_iff_right (image_subset _ hst),
--     and_iff_right (image_subset _ _)]
--   · rintro _ ⟨x, hxt, rfl⟩
--     rw [mem_union]
--     by_cases h : f x ∈ f '' s
--     · left; assumption
--     have hxd : x ∈ d
--     · rw [hd, mem_inter_iff, and_iff_right hxt]
--       exact ⟨mem_image_of_mem f hxt, h⟩
--     right

--     refine ⟨g (f x), ⟨f x, ⟨g (f x), ?_, ?_⟩, rfl⟩, ?_⟩
--     · exact mem_of_mem_of_subset (invFunOn_apply_mem (f := f) hxd) Subset.rfl
--     · rwa [invFunOn_apply_eq (f := f)]
--     · rwa [invFunOn_apply_eq (f := f)]
--   rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
--   exact mem_of_mem_of_subset (invFunOn_apply_mem (f := f) hx) (inter_subset_left _ _)

-- lemma Set.InjOn.exists_injOn_superset_image {f : α → β} {s s' : Set α} {t : Set β}
--     (hss' : s ⊆ s') (hinj : InjOn f s) (hst : f '' s ⊆ t) (ht : t ⊆ f '' s') :
--     ∃ r, s ⊆ r ∧ r ⊆ s' ∧ InjOn f r ∧ f '' r = t := by
--   rw [image_subset_iff] at hst
--   obtain ⟨r, hsr, hrs', hinj, heq⟩ := hinj.exists_injOn_superset (subset_inter hss' hst)
--   rw [subset_inter_iff] at hrs'
--   refine ⟨r, hsr, hrs'.1, hinj, ?_⟩
--   rw [heq, subset_antisymm_iff, image_subset_iff, and_iff_right (inter_subset_right _ _)]
--   intro x hxt
--   obtain ⟨y, hy, rfl⟩ := ht hxt
--   exact ⟨y, ⟨hy, hxt⟩, rfl⟩

/-- If `f` maps `s` bijectively to `t` and, then for any `s ⊆ s₁` and `t ⊆ t' ⊆ f '' s₁`,
  there is some `s ⊆ s' ⊆ s₁` so that `f` maps `s'` bijectively to `t'`. -/
theorem Set.BijOn.extend_of_subset {f : α → β} {s s₁ : Set α} {t : Set β}
    (h : BijOn f s t) (hss₁ : s ⊆ s₁) (htt' : t ⊆ t') (ht' : t' ⊆ f '' s₁) :
    ∃ s', s ⊆ s' ∧ s' ⊆ s₁ ∧ Set.BijOn f s' t' := by
  have hex : ∀ (b : ↑(t' \ t)),  ∃ a, a ∈ s₁ \ s ∧ f a = b
  · rintro ⟨b, hb⟩
    obtain ⟨a, ha, rfl⟩  := ht' hb.1
    exact ⟨_, ⟨ha, fun has ↦ hb.2 <| h.mapsTo has⟩, rfl⟩
  choose g hg using hex
  have hinj : InjOn f (s ∪ range g)
  · rw [injOn_union, and_iff_right h.injOn, and_iff_left]
    · rintro _ ⟨⟨x,hx⟩, rfl⟩ _ ⟨⟨x', hx'⟩,rfl⟩ hf
      simp only [(hg _).2, (hg _).2] at hf; subst hf; rfl
    · rintro x hx _ ⟨⟨y,hy⟩, hy', rfl⟩ h_eq
      rw [(hg _).2] at h_eq
      obtain (rfl : _ = y) := h_eq
      exact hy.2 <| h.mapsTo hx
    rw [disjoint_iff_forall_ne]
    rintro x hx _ ⟨y, hy, rfl⟩ rfl
    have h' := h.mapsTo hx
    rw [(hg _).2] at h'
    exact y.prop.2 h'
  have hp : BijOn f (range g) (t' \ t)
  · apply BijOn.mk
    · rintro _ ⟨x, hx, rfl⟩; rw [(hg _).2]; exact x.2
    · exact hinj.mono (subset_union_right _ _)
    exact fun x hx ↦ ⟨g ⟨x,hx⟩, by simp [(hg _).2] ⟩
  refine ⟨s ∪ range g, subset_union_left _ _, union_subset hss₁ <| ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩; exact (hg _).1.1
  convert h.union hp ?_
  · exact (union_diff_cancel htt').symm
  exact hinj

theorem Set.BijOn.extend {f : α → β} {s : Set α} {t : Set β} (h : BijOn f s t) (htt' : t ⊆ t')
    (ht' : t' ⊆ range f) : ∃ s', s ⊆ s' ∧ BijOn f s' t' := by
  simpa using h.extend_of_subset (subset_univ s) htt' (by simpa)

theorem Set.InjOn.imageFactorization_injective (h : InjOn f s) :
    Injective (s.imageFactorization f) := by
  rintro ⟨x,hx⟩ ⟨y,hy⟩ h'
  simp_rw [imageFactorization, Subtype.mk.injEq, h.eq_iff hx hy] at h'
  simp only [h']
section Lattice

lemma biUnion_insert_eq (hX : X.Nonempty) (Y : Set α) : ⋃ (x ∈ X), (insert x Y) = X ∪ Y := by
  have := hX.to_subtype
  simp_rw [←singleton_union, biUnion_eq_iUnion, ←iUnion_union, iUnion_singleton_eq_range,
    Subtype.range_coe_subtype, setOf_mem_eq]

theorem Finite.exists_localEquiv_of_encard_eq [Nonempty α] [Nonempty β] {s : Set α} {t : Set β}
    (hfin : s.Finite) (h : s.encard = t.encard) :
    ∃ (e : LocalEquiv α β), e.source = s ∧ e.target = t := by

  obtain ⟨f, hf⟩ := hfin.exists_bijOn_of_encard_eq h
  exact ⟨hf.toLocalEquiv, rfl, hf.toLocalEquiv_target⟩

theorem Equiv.exists_bijOn [Nonempty β] {s : Set α} {t : Set β} (e : s ≃ t) :
    ∃ f, BijOn f s t ∧ ∀ x, e x = f x := by
  classical
  use fun x ↦ if hx : x ∈ s then e ⟨x,hx⟩ else Classical.arbitrary β
  refine ⟨BijOn.mk (fun x hx ↦ ?_) (fun x hx y hy hxy ↦ ?_) (fun y hy ↦ ⟨e.symm ⟨y, hy⟩, by simp⟩),
    by simp⟩
  · rw [dif_pos hx]; exact Subtype.prop _
  simpa [dif_pos hx, dif_pos hy, Subtype.coe_inj] using hxy

noncomputable def LocalEquiv.ofSetEquiv [Nonempty α] [Nonempty β] {s : Set α} {t : Set β}
    (e : s ≃ t) : LocalEquiv α β :=
  let f := Classical.choose e.exists_bijOn
  BijOn.toLocalEquiv f s t (Classical.choose_spec e.exists_bijOn).1

 @[simp] theorem LocalEquiv.ofSetEquiv_source_eq [Nonempty α] [Nonempty β] {s : Set α} {t : Set β}
    (e : s ≃ t) : (LocalEquiv.ofSetEquiv e).source = s := by
  simp [ofSetEquiv]

@[simp] theorem LocalEquiv.ofSetEquiv_target_eq [Nonempty α] [Nonempty β] {s : Set α} {t : Set β}
    (e : s ≃ t) : (LocalEquiv.ofSetEquiv e).target = t := by
  simp [ofSetEquiv]

@[simp] theorem LocalEquiv.ofSetEquiv_apply [Nonempty α] [Nonempty β] {s : Set α} {t : Set β}
    (e : s ≃ t) (x : s) : LocalEquiv.ofSetEquiv e x = e x :=
  ((Classical.choose_spec e.exists_bijOn).2 x).symm

theorem Set.Finite.encard_le_iff_nonempty_embedding {s : Set α} {t : Set β} (hs : s.Finite) :
    s.encard ≤ t.encard ↔ Nonempty (s ↪ t) := by
  cases isEmpty_or_nonempty β
  · simp only [t.eq_empty_of_isEmpty, encard_empty, nonpos_iff_eq_zero, encard_eq_zero]
    constructor; rintro rfl; exact ⟨Embedding.ofIsEmpty⟩
    rintro ⟨e⟩
    exact isEmpty_coe_sort.1 e.toFun.isEmpty
  refine ⟨fun h ↦ ?_, fun ⟨e⟩ ↦ e.enccard_le⟩
  obtain ⟨f, hst, hf⟩ := hs.exists_injOn_of_encard_le h
  exact ⟨codRestrict (s.restrict f) t (fun x ↦ by aesop), hf.injective.codRestrict _⟩

theorem Set.Finite.encard_le_iff_nonempty_embedding' {s : Set α} {t : Set β} (ht : t.Finite) :
    s.encard ≤ t.encard ↔ Nonempty (s ↪ t) := by
  obtain (hs | hs) := s.finite_or_infinite
  · exact hs.encard_le_iff_nonempty_embedding
  rw [hs.encard_eq, top_le_iff, encard_eq_top_iff, Set.Infinite, iff_true_intro ht,
    not_true, false_iff]
  rintro ⟨e⟩
  have hle := e.enccard_le
  rw [hs.encard_eq, top_le_iff, encard_eq_top_iff] at hle
  exact hle ht

@[simp] theorem encard_univ_fin (a : ℕ) : (univ : Set (Fin a)).encard = a := by
  simp [encard_eq_coe_toFinset_card]




  -- refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩


theorem Set.Finite.encard_eq_iff_nonempty_equiv {s : Set α} {t : Set β} (ht : t.Finite) :
    s.encard = t.encard ↔ Nonempty (s ≃ t) := by
  cases isEmpty_or_nonempty α
  · simp only [s.eq_empty_of_isEmpty, eq_comm (a := (0 : ℕ∞)), encard_empty, encard_eq_zero]
    constructor; rintro rfl; exact ⟨Equiv.equivOfIsEmpty _ _⟩
    rintro ⟨e⟩
    exact isEmpty_coe_sort.1 e.symm.toFun.isEmpty
  refine ⟨fun h ↦ ?_, fun ⟨e⟩ ↦ encard_congr e⟩
  obtain ⟨f, hf⟩ := ht.exists_bijOn_of_encard_eq h.symm
  exact Nonempty.intro <| (hf.equiv _).symm





-- @[simp] theorem LocalEquiv.ofSetEquiv_apply_symm [Nonempty α] [Nonempty β] {s : Set α} {t : Set β}
--     (e : s ≃ t) (y : t) : (LocalEquiv.ofSetEquiv e).symm y = e.symm y := by

--   simp only [ofSetEquiv, Subtype.forall, BijOn.toLocalEquiv_symm_apply]

--   have := ((Classical.choose_spec e.exists_bijOn).2 (e.symm y)).symm





  -- use Function.extend Subtype.val (fun x ↦ (e x).1) (fun _ ↦ Classical.arbitrary β)
  -- simp

end Lattice
section Matrix

variable {m n R : Type} [Semiring R]

/-- For a semiring `R`, the modules `(n → R)` and `Matrix Unit n R` are linearly equivalent. -/
def Matrix.row_linearEquiv (n R : Type) [Semiring R] : (n → R) ≃ₗ[R] Matrix Unit n R where
  toFun := Matrix.row
  invFun A i := A () i
  map_add' := Matrix.row_add
  map_smul' := Matrix.row_smul
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl

@[simp] theorem Matrix.row_linearEquiv_apply (f : n → R) :
    Matrix.row_linearEquiv n R x = Matrix.row x := rfl

@[simp] theorem Matrix.row_linearEquiv_apply_symm (A : Matrix Unit n R) :
    (Matrix.row_linearEquiv n R).symm A = A () := rfl

/-- For a semiring `R`, the modules `(m → R)` and `Matrix m Unit r` are linearly equivalent. -/
def Matrix.col_linearEquiv (m R : Type) [Semiring R] : (m → R) ≃ₗ[R] Matrix m Unit R where
  toFun := Matrix.col
  invFun A i := A i ()
  map_add' := Matrix.col_add
  map_smul' := Matrix.col_smul
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl

@[simp] theorem Matrix.col_linearEquiv_apply (f : m → R) :
    Matrix.col_linearEquiv m R x = Matrix.col x := rfl

@[simp] theorem Matrix.col_linearEquiv_apply_symm (A : Matrix m Unit R) (i : m) :
    (Matrix.col_linearEquiv m R).symm A i = A i () := rfl

theorem exists_eq_image_subset_of_subset_image {α β : Type*} {f : α → β} {s : Set α} {t : Set β}
    (hst : t ⊆ f '' s) : ∃ t₀, t₀ ⊆ s ∧ t = f '' t₀ := by
  refine ⟨f ⁻¹' t ∩ s, inter_subset_right _ _, subset_antisymm (fun x hxt ↦ ?_) ?_⟩
  · obtain ⟨a, ha, rfl⟩ := hst hxt
    exact ⟨a, mem_inter hxt ha, rfl⟩
  simp [image_subset_iff, inter_subset_left]

theorem Set.restrict_id_eq (s : Set α) : s.restrict id = Subtype.val := rfl

abbrev Set.incl (s : Set α) : s → α := Subtype.val

@[simp] theorem isEmpty_fin_iff {b : ℕ} : IsEmpty (Fin b) ↔ b = 0 := by
  cases b <;> simp [Fin.isEmpty]
