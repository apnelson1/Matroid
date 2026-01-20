import Matroid.Minor.Rank
import Mathlib.Combinatorics.Matroid.Constructions -- inefficient import
import Matroid.Equiv
import Matroid.ForMathlib.Other

namespace Matroid

open Set Function Set.Notation Subtype

variable {α β β' : Type*} {M : Matroid α} {N : Matroid β} {C D X Y : Set α} {e : α}
section Iso

/-- Deletions of isomorphic matroids are isomorphic. -/
def Iso.delete (e : Iso M N) (D : Set α) :
    Iso (M ＼ D) (N ＼ (↑(e '' M.E ↓∩ D) : Set β)) :=
  e.restrict diff_subset diff_subset (by aesop)

/-- Contractions of isomorphic matroids are isomorphic. -/
def Iso.contract (e : Iso M N) (C : Set α) :
    Iso (M ／ C) (N ／ (↑(e '' M.E ↓∩ C) : Set β)) :=
  (e.dual.delete C).dual

/-- `N ≤ir M` means that `N` is isomorphic to a restriction of `M`.
Defined as a function from `N.E` to `M.E`. -/
@[pp_nodot] structure IsoRestr (N : Matroid β) (M : Matroid α) where
  (toFun : N.E → M.E)
  (inj' : Injective toFun)
  (indep_iff' : ∀ (I : Set N.E), N.Indep ↑I ↔ M.Indep ↑(toFun '' I))

scoped infix:65 " ≤ir " => IsoRestr

instance : FunLike (N ≤ir M) N.E M.E where
  coe f := f.toFun
  coe_injective' f g := by cases f; cases g; simp

instance : EmbeddingLike (N ≤ir M) N.E M.E where
  injective' f := f.inj'

theorem IsoRestr.indep_image_iff (i : N ≤ir M) {I : Set N.E} :
    M.Indep ↑(i '' I) ↔ N.Indep ↑I :=
  (i.indep_iff' I).symm

def Iso.isoRestr (e : N ≂ M) : N ≤ir M where
  toFun := e
  inj' := EmbeddingLike.injective' e
  indep_iff' _ := indep_image_iff e

@[simp]
lemma Iso.isoRestr_apply (e : N ≂ M) (x : N.E) : e.isoRestr x = e x := rfl

@[simp]
lemma Iso.range_isoRestr (e : N ≂ M) : range e.isoRestr = univ := by
  ext x
  simp only [mem_range, isoRestr_apply, Subtype.exists, mem_univ, iff_true]
  exact ⟨e.symm x, by simp⟩

def IsRestriction.isoRestr {M N : Matroid α} (h : N ≤r M) : N ≤ir M where
  toFun := inclusion h.subset
  inj' := inclusion_injective h.subset
  indep_iff' I := by simp [h.indep_iff]

noncomputable def IsoRestr.iso_restrict_range_comp (i : N ≤ir M) : N ≂ (M ↾ range (val ∘ i)) :=
  Iso.mk (Equiv.ofInjective _ <| Subtype.val_injective.comp (EmbeddingLike.injective i)) fun I ↦ by
    simp only [← i.indep_image_iff, restrict_ground_eq, Equiv.ofInjective_apply, comp_apply,
      restrict_indep_iff, image_subset_iff, coe_preimage_self, subset_univ, and_true]
    simp [image_image]

@[simp]
lemma IsoRestr.iso_restrict_range_comp_apply (i : N ≤ir M) (e : N.E) :
  (i.iso_restrict_range_comp e : range (val ∘ ⇑i)) = ⟨i e, by simp⟩ := rfl

@[simp]
lemma IsoRestr.iso_restrict_range_comp_apply_coe (i : N ≤ir M) (e : N.E) :
    (i.iso_restrict_range_comp e : α) = i e := rfl

theorem IsoRestr.exists_restr_iso (i : N ≤ir M) :
    ∃ (M₀ : Matroid α) (e : N ≂ M₀) (hr : M₀ ≤r M), (inclusion hr.subset) ∘ e = i := by
  refine
    ⟨_, i.iso_restrict_range_comp, restrict_isRestriction _ _ <| by simp [range_comp], ?_⟩
  ext x
  exact i.iso_restrict_range_comp_apply_coe x

/-- `≤ir ` is transitive. -/
def IsoRestr.trans {α₁ α₂ α₃ : Type*} {M₁ : Matroid α₁} {M₂ : Matroid α₂} {M₃ : Matroid α₃}
    (i₁ : M₁ ≤ir M₂) (i₂ : M₂ ≤ir M₃) : M₁ ≤ir M₃ where
  toFun := i₂ ∘ i₁
  inj' := Injective.comp (EmbeddingLike.injective i₂) (EmbeddingLike.injective i₁)
  indep_iff' I := by rw [← i₁.indep_image_iff, ← i₂.indep_image_iff]; simp [image_image]

@[simp]
def IsoRestr.trans_apply {α₁ α₂ α₃ : Type*} {M₁ : Matroid α₁} {M₂ : Matroid α₂} {M₃ : Matroid α₃}
    (i₁ : M₁ ≤ir M₂) (i₂ : M₂ ≤ir M₃) (x : M₁.E) : (i₁.trans i₂) x = i₂ (i₁ x) := rfl

@[simp]
lemma IsoRestr.range_trans {α₁ α₂ α₃ : Type*} {M₁ : Matroid α₁} {M₂ : Matroid α₂} {M₃ : Matroid α₃}
    (i₁ : M₁ ≤ir M₂) (i₂ : M₂ ≤ir M₃) : range (i₁.trans i₂) = i₂ '' (range i₁) :=
  range_comp i₂ i₁

/-- For `e : N ≤ir M`, `e.Spanning N M` means that `N` embeds in `M` as a spanning restriction. -/
def IsoRestr.Spanning (e : N ≤ir M) : Prop := M.Spanning ((↑) '' range e)

lemma IsoRestr.Spanning.exists_restr_iso {i : N ≤ir M} (hi : i.Spanning) :
    ∃ (M₀ : Matroid α) (e : N ≂ M₀) (hr : M₀ ≤r M),
        M.Spanning M₀.E ∧ (inclusion hr.subset) ∘ e = i:=
  ⟨_, i.iso_restrict_range_comp, restrict_isRestriction _ _ <| by simp [range_comp],
    by rwa [restrict_ground_eq, range_comp], by
    ext x
    exact i.iso_restrict_range_comp_apply_coe x ⟩

-- Disgusting proof!
lemma IsoRestr.Spanning.trans {α₁ α₂ α₃ : Type*} {M₁ : Matroid α₁} {M₂ : Matroid α₂}
    {M₃ : Matroid α₃} {e₁ : M₁ ≤ir M₂} {e₂ : M₂ ≤ir M₃} (he₁ : e₁.Spanning) (he₂ : e₂.Spanning) :
    (e₁.trans e₂).Spanning := by
  obtain ⟨M₂', i, hM₂, hsp₂, he₁'⟩ := he₁.exists_restr_iso
  obtain ⟨M₃', i', hM₃, hsp₃, he₂'⟩ := he₂.exists_restr_iso
  simp only [Spanning, range_trans, ← he₁', ← he₂',
    comp_apply, EquivLike.range_comp, range_inclusion, image_val_image_comp_inclusion]
  have hsp' : M₂.Spanning ↑(M₂.E ↓∩ M₂'.E) := by simpa [inter_eq_self_of_subset_right hM₂.subset]
  rw [i'.spanning_iff] at hsp'
  obtain ⟨R, hR, rfl⟩ := hM₃.exists_eq_restrict
  rw [restrict_spanning_iff (by simp)] at hsp'
  rw [spanning_iff_ground_subset_closure _]
  · replace hsp' := closure_subset_closure_of_subset_closure hsp'
    rw [restrict_ground_eq] at hsp₃
    rw [hsp₃.closure_eq] at hsp'
    exact hsp'.trans (M₃.closure_mono <| by simp [subset_def])
  refine (image_mono (image_subset_range _ _)).trans ?_
  rw [i'.range_eq]
  simpa using hM₃.subset

/-- Construct an `IsoRestr` from a function defined on all of `α` rather than a subtype. -/
@[simps] def IsoRestr.ofSubtypeFun (f : M.E → β) (hf : Injective f) (hfN : range f ⊆ N.E)
    (hfI : ∀ I : Set M.E, M.Indep I ↔ N.Indep ↑(f '' I)) : M ≤ir N where
  toFun e := ⟨f e, hfN (mem_range_self _)⟩
  inj' _ _ := by simp [hf.eq_iff]
  indep_iff' I := by
    rw [hfI]
    convert Iff.rfl
    aesop

@[simp] lemma IsoRestr_ofSubtypeFun_apply (f : M.E → β) (hf) (hfN : range f ⊆ N.E) (hfI)
    (e : M.E) : (IsoRestr.ofSubtypeFun f hf hfN hfI) e = ⟨f e, hfN (mem_range_self _)⟩ := rfl

lemma IsoRestr.ofSubtypeFun_spanning (f : M.E → β) (hf : Injective f) (hfI)
    (hfs : N.Spanning (range f)) : (IsoRestr.ofSubtypeFun f hf hfs.subset_ground hfI).Spanning := by
  have := hfs.subset_ground
  simp only [Spanning]
  convert hfs
  aesop

/-- Construct an `IsoRestr` from a function defined on all of `α` rather than a subtype. -/
@[simps] def IsoRestr.ofFun (f : α → β) (hf : InjOn f M.E) (hfN : f '' M.E ⊆ N.E)
    (hfI : ∀ I ⊆ M.E, M.Indep I ↔ N.Indep (f '' I)) : M ≤ir N where
  toFun e := ⟨f e, hfN (mem_image_of_mem _ e.2)⟩
  inj' _ _ := by simp [hf.eq_iff, Subtype.coe_inj]
  indep_iff' I := by
    rw [hfI _ (by simp)]
    convert Iff.rfl
    aesop

@[simp] lemma IsoRestr_ofFun_apply (f : α → β) (hf : InjOn f M.E) (hfN : f '' M.E ⊆ N.E) (hfI)
    (e : M.E) : (IsoRestr.ofFun f hf hfN hfI) e = ⟨f e, hfN (mem_image_of_mem _ e.2)⟩ := rfl

lemma IsoRestr.ofFun_spanning (f : α → β) (hf : InjOn f M.E) (hfI) (hfs : N.Spanning (f '' M.E)) :
    (IsoRestr.ofFun f hf hfs.subset_ground hfI).Spanning := by
  have := hfs.subset_ground
  simp only [Spanning]
  convert hfs
  aesop

lemma Iso.isoRestr_spanning (e : N ≂ M) : e.isoRestr.Spanning := by
  simp [IsoRestr.Spanning, spanning_iff_closure_eq]

def IsoRestr.ofEmptyOn (M : Matroid β) : emptyOn α ≤ir M :=
  (empty_iso_empty α β).isoRestr.trans (emptyOn_isRestriction M).isoRestr

/-- `N ≤i M` means that `M` has an `N`-minor; i.e. `N` is isomorphic to a minor of `M`.
The data a term of this type contains is just a function from `N.E` to `M.E` rather than a choice of
delete and contract-sets, which may not be unique.  -/
@[pp_nodot] structure IsoMinor (N : Matroid β) (M : Matroid α) where
  (toFun : N.E → M.E)
  (inj' : Injective toFun)
  (exists_isMinor' : ∃ M₀, M₀ ≤m M ∧ M₀.E = ↑(range toFun) ∧
    ∀ (I : Set N.E), N.Indep I ↔ M₀.Indep ↑(toFun '' I))

/-- `N <i M` means that `N` can be embeddeded in `M` as a minor via a function
that is not surjective. -/
@[pp_nodot] structure StrictIsoMinor (N : Matroid β) (M : Matroid α) where
  (toFun : N.E → M.E)
  (inj' : Injective toFun)
  (exists_isMinor' : ∃ M₀, M₀ ≤m M ∧ M₀.E = ↑(range toFun) ∧
    ∀ (I : Set N.E), N.Indep I ↔ M₀.Indep ↑(toFun '' I))
  (not_surj : ¬ Surjective toFun)

scoped infix:65 " ≤i " => IsoMinor

scoped infix:65 " <i " => StrictIsoMinor

instance : FunLike (N ≤i M) N.E M.E where
  coe f := f.toFun
  coe_injective' f g := by cases f; cases g; simp

instance : FunLike (N <i M) N.E M.E where
  coe f := f.toFun
  coe_injective' f g := by cases f; cases g; simp

instance {α β : Type*} {N : Matroid α} {M : Matroid β} : EmbeddingLike (N ≤i M) N.E M.E where
  injective' f := f.inj'

instance {α β : Type*} {N : Matroid α} {M : Matroid β} : EmbeddingLike (N <i M) N.E M.E where
  injective' f := f.inj'

@[simps]
def StrictIsoMinor.isoMinor (e : N <i M) : N ≤i M where
  toFun := e
  inj' := e.inj'
  exists_isMinor' := e.exists_isMinor'

lemma StrictIsoMinor.not_surjective (e : N <i M) : ¬ Surjective e := e.not_surj

theorem IsoMinor.injective (f : N ≤i M) : Injective f :=
  f.inj'

theorem IsoMinor.exists_isMinor (i : N ≤i M) :
    ∃ M₀, M₀ ≤m M ∧ M₀.E = ↑(range i) ∧ ∀ (I : Set N.E), N.Indep I ↔ M₀.Indep ↑(i '' I) :=
      i.exists_isMinor'

theorem StrictIsoMinor.exists_isMinor (i : N <i M) :
    ∃ M₀, M₀ <m M ∧ M₀.E = ↑(range i) ∧ ∀ (I : Set N.E), N.Indep I ↔ M₀.Indep ↑(i '' I) := by
  obtain ⟨M₀, hM₀, hE, hi⟩ := i.exists_isMinor'
  obtain hM₀ | rfl := hM₀.isStrictMinor_or_eq
  · exact ⟨M₀, hM₀, hE, hi⟩
  exfalso
  refine i.not_surjective ?_
  rintro ⟨e, he_mem⟩
  rw [hE] at he_mem
  simp only [mem_image, mem_range, Subtype.exists, exists_and_right, exists_eq_right] at he_mem
  obtain ⟨h1, a, ha, h_eq⟩ := he_mem
  exact ⟨⟨a,ha⟩, h_eq⟩

theorem IsoMinor.exists_iso (i : N ≤i M) :
    ∃ (M₀ : Matroid α) (hM₀ : M₀ ≤m M) (e : N ≂ M₀), ∀ x, inclusion hM₀.subset (e x) = i x := by
  obtain ⟨M₀, hM₀, hE, h⟩ := i.exists_isMinor
  refine ⟨M₀, hM₀,  ?_⟩
  let e := Equiv.ofInjective _ (Subtype.val_injective.comp (EmbeddingLike.injective i))
  exact ⟨Iso.mk (e.trans (Equiv.setCongr (by simp [hE, range_comp])))
    fun _ ↦ by simp [h, image_image, e], fun ⟨x,hx⟩ ↦ rfl⟩

theorem StrictIsoMinor.exists_iso (i : N <i M) :
    ∃ (M₀ : Matroid α) (hM₀ : M₀ <m M) (e : N ≂ M₀),
      ∀ x, inclusion hM₀.isMinor.subset (e x) = i x := by
  obtain ⟨M₀, hM₀, hE, h⟩ := i.exists_isMinor
  refine ⟨M₀, hM₀,  ?_⟩
  let e := Equiv.ofInjective _ (Subtype.val_injective.comp (EmbeddingLike.injective i))
  exact ⟨Iso.mk (e.trans (Equiv.setCongr (by simp [hE, range_comp])))
    fun _ ↦ by simp [h, image_image, e], fun ⟨x,hx⟩ ↦ rfl⟩

@[simps!]
def IsoMinor.strictIsoMinor_of_not_surjective (i : N ≤i M) (hi : ¬ Surjective i) : N <i M where
  toFun := i.toFun
  inj' := i.inj'
  exists_isMinor' := i.exists_isMinor'
  not_surj := hi

/-- If there is an isomorphism from `N` to a isMinor `M₀` of `M`, then `N ≤i M`. -/
@[simps] def IsoMinor.ofExistsIso (f : N.E → M.E)
  (h : ∃ (M₀ : Matroid α) (hM₀ : M₀ ≤m M) (e : N ≂ M₀), ∀ x, inclusion hM₀.subset (e x) = f x) :
  N ≤i M where
    toFun := f
    inj' x y hxy := by
      obtain ⟨M₀, hM₀, e, he⟩ := h
      simpa [← he, Subtype.val_inj] using hxy
    exists_isMinor' := by
      obtain ⟨M₀, hM₀, e, he⟩ := h
      refine ⟨M₀, hM₀, ?_, fun I ↦ ?_⟩
      · ext x
        simp only [mem_image, mem_range, ← he, Subtype.exists, exists_and_right, exists_eq_right]
        refine ⟨fun h ↦  ⟨hM₀.subset h, _, (e.symm ⟨x,h⟩).2, by simp⟩, fun ⟨h, a, ha, h'⟩ ↦ ?_⟩
        simp_rw [← Subtype.coe_inj] at h'
        subst h'
        simp
      rw [e.indep_image_iff]
      convert Iff.rfl using 2
      ext x
      simp [← he]

/-- If `N ≂ M₀` and `M₀ ≤m M` then `N ≤i M`. -/
@[simps] def Iso.transIsoMinor {M₀ : Matroid α} (e : N ≂ M₀) (hM₀ : M₀ ≤m M) : N ≤i M where
  toFun x := (inclusion hM₀.subset) (e x)
  inj' := by rintro ⟨x, hx⟩ ⟨y, hy⟩; simp [Subtype.val_inj]
  exists_isMinor' := ⟨M₀, hM₀, by simp, fun I ↦ by simp [e.indep_image_iff]⟩

/-- If `M` and `N` are isomorphic, then `M ≤i N`. -/
@[simps!] def Iso.isoMinor (e : M ≂ N) : M ≤i N := IsoMinor.ofExistsIso e
  ⟨N, IsMinor.refl, e, by simp⟩

/-- If `M ≤m N`, then `M ≤i M`. -/
@[simps!] def IsMinor.isoMinor {M N : Matroid α} (h : M ≤m N) : M ≤i N :=
  IsoMinor.ofExistsIso (inclusion h.subset) ⟨M, h, Iso.refl, fun _ ↦ rfl⟩

/-- If `N ≤i M` then `N✶ ≤i M✶`. -/
@[simps!] def IsoMinor.dual (N : Matroid β) (M : Matroid α) (i : N ≤i M) : N✶ ≤i M✶ :=
  IsoMinor.ofExistsIso i (by
    obtain ⟨M₀, hM₀, e, h⟩ := i.exists_iso
    exact ⟨M₀✶, hM₀.dual, e.dual, h⟩)

@[simps!]
def StrictIsoMinor.dual (e : N <i M) : N✶ <i M✶ :=
  e.isoMinor.dual.strictIsoMinor_of_not_surjective e.not_surjective

/-- If `M₁ ≤i M₂` and `M₂ ≂ M₃` then `M₁ ≤i M₃`. -/
def IsoMinor.trans_iso {α₁ α₂ α₃ : Type*} {M₁ : Matroid α₁} {M₂ : Matroid α₂} {M₃ : Matroid α₃}
    (i : M₁ ≤i M₂) (e : M₂ ≂ M₃) : M₁ ≤i M₃ := by
  refine IsoMinor.ofExistsIso (e ∘ i) ?_
  obtain ⟨N₂, ⟨C, D, hC, hD, hdj, rfl⟩, e', h⟩ := i.exists_iso
  refine ⟨_, contract_delete_isMinor _ _ _, e'.trans ((e.contract C).delete D), fun ⟨x,hx⟩ ↦ ?_⟩
  simp only [comp_apply, ← h]
  rfl

/-- If `M₁ ≤i M₂` and `M₂ ≤m M₃` then `M₁ ≤i M₃`. -/
def IsoMinor.trans_isMinor {M' : Matroid α} (i : N ≤i M) (hM : M ≤m M') : N ≤i M' where
  toFun := (inclusion hM.subset) ∘ i
  inj' := (inclusion_injective hM.subset).comp i.injective
  exists_isMinor' := by
    obtain ⟨M₀, hM₀M, e, he⟩ := i.exists_isMinor
    exact ⟨M₀, hM₀M.trans hM, by simp [range_comp, ← e], by simpa [image_comp]⟩

/-- Construct a term `N ≤i M` from an explicitly given embedding and an existence proof.
Useful for computability and defeq.  -/
@[simps] def IsoMinor.congr_exists (f : N.E → M.E) (h : ∃ (i : N ≤i M), ∀ x, i x = f x) :
    N ≤i M where
  toFun := f
  inj' x y hxy := by obtain ⟨i, hi⟩ := h; rwa [← hi, ← hi, i.injective.eq_iff] at hxy
  exists_isMinor' := by
    obtain ⟨i, hi⟩ := h
    obtain rfl : f = i := by ext; simp [hi]
    exact i.exists_isMinor

/-- `≤i` is transitive. -/
@[simps!] def IsoMinor.trans {α₁ α₂ α₃ : Type*} {M₁ : Matroid α₁} {M₂ : Matroid α₂}
    {M₃ : Matroid α₃} (i₁ : M₁ ≤i M₂) (i₂ : M₂ ≤i M₃) : M₁ ≤i M₃ :=
  IsoMinor.congr_exists (i₂ ∘ i₁) (by
    obtain ⟨N₃, h, e, h'⟩ := i₂.exists_iso
    refine ⟨(i₁.trans_iso e).trans_isMinor h, fun x ↦ ?_⟩
    simp only [comp_apply, ← h']
    rfl )

@[simps!]
def IsoMinor.trans_strictIsoMinor {α₁ α₂ α₃ : Type*} {M₁ : Matroid α₁} {M₂ : Matroid α₂}
    {M₃ : Matroid α₃} (i : M₁ ≤i M₂) (i' : M₂ <i M₃) : M₁ <i M₃ :=
  (i.trans i'.isoMinor).strictIsoMinor_of_not_surjective
    (fun h ↦ i'.not_surjective <| Surjective.of_comp h)

@[simps!]
def StrictIsoMinor.trans_isoMinor {α₁ α₂ α₃ : Type*} {M₁ : Matroid α₁} {M₂ : Matroid α₂}
    {M₃ : Matroid α₃} (i : M₁ <i M₂) (i' : M₂ ≤i M₃) : M₁ <i M₃ :=
  (i.isoMinor.trans i').strictIsoMinor_of_not_surjective
    fun h ↦ i.not_surjective <| Surjective.of_comp_left h i'.injective

@[simp] def emptyOn_isoMinor (α : Type*) (M : Matroid β) : emptyOn α ≤i M where
  toFun := IsEmpty.elim' (by simp)
  inj' x := IsEmpty.elim' (by simp) x
  exists_isMinor' := ⟨emptyOn β, by simp, by ext; simp, by simp⟩

noncomputable def IsoRestr.isoMinor (e : N ≤ir M) : N ≤i M :=
  have hex := e.exists_restr_iso
  hex.choose_spec.choose.isoMinor.trans <| hex.choose_spec.choose_spec.choose.isMinor.isoMinor

lemma IsoMinor.eRank_le (e : N ≤i M) : N.eRank ≤ M.eRank := by
  obtain ⟨M₀, hM₀, i, -⟩ := e.exists_iso
  exact i.eRank_eq.trans_le hM₀.eRank_le

lemma IsoMinor.rank_le (e : N ≤i M) [RankFinite M] : N.rank ≤ M.rank := by
  obtain ⟨M₀, hM₀, i, -⟩ := e.exists_iso
  exact i.rank_eq.trans_le hM₀.rank_le

lemma IsoMinor.encard_ground_le (e : N ≤i M) : N.E.encard ≤ M.E.encard := by
  obtain ⟨M₀, hM₀, i, -⟩ := e.exists_iso
  convert encard_le_encard hM₀.subset
  exact i.toEquiv.encard_eq

lemma StrictIsoMinor.encard_ground_lt (e : N <i M) (hN : N.Finite) : N.E.encard < M.E.encard := by
  obtain ⟨M₀, hM₀, i, -⟩ := e.exists_iso
  rw [i.toEquiv.encard_eq]
  refine Finite.encard_lt_encard ?_ hM₀.ssubset
  rw [← encard_lt_top_iff, ← i.toEquiv.encard_eq, encard_lt_top_iff]
  exact N.ground_finite

structure IsDeletableSet (M : Matroid α) (N : Matroid β) (D : Set α) where
  subset_ground : D ⊆ M.E
  has_minor : Nonempty (N ≤i M ＼ D)

structure IsContractibleSet (M : Matroid α) (N : Matroid β) (C : Set α) where
  subset_ground : C ⊆ M.E
  has_minor : Nonempty (N ≤i M ／ C)

abbrev IsDeletable (M : Matroid α) (N : Matroid β) (e : α) := M.IsDeletableSet N {e}

abbrev IsContractible (M : Matroid α) (N : Matroid β) (e : α) := M.IsContractibleSet N {e}

lemma IsDeletable.mem_ground (h : M.IsDeletable N e) : e ∈ M.E := by
  simpa using h.subset_ground

lemma IsContractible.mem_ground (h : M.IsContractible N e) : e ∈ M.E := by
  simpa using h.subset_ground

attribute [aesop unsafe 20% (rule_sets := [Matroid])] IsDeletableSet.subset_ground
  IsContractibleSet.subset_ground IsDeletable.mem_ground IsContractible.mem_ground

lemma IsDeletableSet.isContractibleSet_dual (h : M.IsDeletableSet N X) :
    M✶.IsContractibleSet N✶ X := by
  obtain ⟨hE, ⟨e⟩⟩ := h
  exact ⟨hE, ⟨e.dual.trans_iso <| Iso.ofEq (M.dual_delete ..)⟩⟩

lemma IsContractibleSet.isDeletableSet_dual (h : M.IsContractibleSet N X) :
    M✶.IsDeletableSet N✶ X := by
  obtain ⟨hE, ⟨e⟩⟩ := h
  exact ⟨hE, ⟨e.dual.trans_iso <| Iso.ofEq (M.dual_contract ..)⟩⟩

lemma isDeletableSet_dual_iff : M✶.IsDeletableSet N X ↔ M.IsContractibleSet N✶ X :=
  ⟨fun h ↦ M.dual_dual ▸ h.isContractibleSet_dual, fun h ↦ N.dual_dual ▸ h.isDeletableSet_dual⟩

lemma isContractibleSet_dual_iff : M✶.IsContractibleSet N X ↔ M.IsDeletableSet N✶ X := by
  rw [← M.dual_dual, isDeletableSet_dual_iff, dual_dual, dual_dual]

@[simp]
lemma dual_isDeletableSet_dual_iff : M✶.IsDeletableSet N✶ X ↔ M.IsContractibleSet N X := by
  rw [isDeletableSet_dual_iff, dual_dual]

@[simp]
lemma dual_isContractibleSet_dual_iff : M✶.IsContractibleSet N✶ X ↔ M.IsDeletableSet N X := by
  rw [isContractibleSet_dual_iff, dual_dual]

lemma isDeletable_dual_iff : M✶.IsDeletable N e ↔ M.IsContractible N✶ e :=
  isDeletableSet_dual_iff

lemma isContractible_dual_iff : M✶.IsContractible N e ↔ M.IsDeletable N✶ e :=
  isContractibleSet_dual_iff

@[simp]
lemma dual_isDeletable_dual_iff : M✶.IsDeletable N✶ e ↔ M.IsContractible N e :=
  dual_isDeletableSet_dual_iff

@[simp]
lemma dual_isContractible_dual_iff : M✶.IsContractible N✶ e ↔ M.IsDeletable N e :=
  dual_isContractibleSet_dual_iff

alias ⟨_, IsContractible.dual_isDeletable⟩ := dual_isContractible_dual_iff
alias ⟨_, IsDeletable.dual_isContractible⟩ := dual_isDeletable_dual_iff

lemma StrictIsoMinor.exists_isDeletable_or_isContractible (i : N <i M) : ∃ e,
    M.IsContractible N e ∨ M.IsDeletable N e := by
  obtain ⟨M₀, hm, φ, hφ⟩ := i.exists_iso
  obtain ⟨e, he, hc | hd⟩ := hm.exists_isMinor_contractElem_or_deleteElem
  · exact ⟨e, .inl ⟨by simpa, ⟨φ.isoMinor.trans hc.isoMinor⟩⟩⟩
  exact ⟨e, .inr ⟨by simpa, ⟨φ.isoMinor.trans hd.isoMinor⟩⟩⟩




-- @[simp] theorem IsoMinor.eq_emptyOn (f : M ≤i emptyOn β) : M = emptyOn α := by
--   rw [← ground_eq_empty_iff]
--   obtain ⟨M₀,h,e,-⟩ := f.exists_iso
--   obtain rfl : M₀ = emptyOn β := by simpa using h
--   have := iso_empt

-- theorem IsMinor.trans_isIso {M N : Matroid α} {M' : Matroid β} (h : N ≤m M) (hi : M ≂ M') :
--     N ≤i M' := by
--   obtain (⟨rfl,rfl⟩ | ⟨-, -, ⟨i⟩⟩) := hi.empty_or_nonempty_iso
--   · simpa using h
--   obtain ⟨C, D, hC, hD, hCD, rfl⟩ := h
--   exact ⟨_, contract_delete_isMinor _ _ _,
--     ((i.contract hC).delete (subset_diff.2 ⟨hD, hCD.symm⟩)).isIso⟩

-- theorem IsMinor.isoMinor {M N : Matroid α} (h : N ≤m M) : N ≤i M :=
--   ⟨N, h, (Iso.refl N).isIso⟩

-- theorem IsoMinor.trans {α₁ α₂ α₃ : Type*} {M₁ : Matroid α₁} {M₂ : Matroid α₂}
--     {M₃ : Matroid α₃} (h : M₁ ≤i M₂) (h' : M₂ ≤i M₃) : M₁ ≤i M₃ := by
--   obtain ⟨M₂', hM₂'M₃, i'⟩ := h'
--   obtain ⟨M₁', hM₁'M₂, i''⟩ := h
--   obtain ⟨N, hN, iN⟩ := hM₁'M₂.trans_isIso i'
--   exact ⟨N, hN.trans hM₂'M₃, i''.trans iN⟩

-- theorem Iso.trans_isoMinor {N' : Matroid β'} (e : Iso N N') (h : N' ≤i M) : N ≤i M :=
--   e.isoMinor.trans h

-- theorem IsoMinor.dual (h : N ≤i M) : N✶ ≤i M✶ :=
--   let ⟨N', hN', hN'M⟩ := h
--   ⟨N'✶, hN'.dual, hN'M.dual⟩

-- theorem isoMinor_dual_iff : N✶ ≤i M✶ ↔ N ≤i M :=
--   ⟨fun h ↦ by rw [← dual_dual M, ← dual_dual N]; exact h.dual, IsoMinor.dual⟩

-- theorem IsoMinor.eRank_le_eRank (h : N ≤i M) : N.eRank ≤ M.eRank := by
--   obtain ⟨N', hN', hNM⟩ := h
--   exact hNM.eRank_eq_eRank.le.trans hN'.eRank_le

-- theorem IsoMinor.encard_ground_le_encard_ground (h : N ≤i M) : N.E.encard ≤ M.E.encard := by
--   obtain ⟨N', hN', (⟨rfl,rfl⟩ | ⟨⟨e⟩⟩)⟩ := h; simp
--   have hss := encard_le_encard <| e.image_ground.subset.trans hN'.subset
--   rwa [e.injOn_ground.encard_image] at hss

-- end Iso

-- section IsoRestr

-- /-- Type-heterogeneous statement that `N` is isomorphic to a restriction of `M` -/
-- def IsoRestr (N : Matroid β) (M : Matroid α) : Prop :=
--   ∃ M' : Matroid α, M' ≤r M ∧ N ≂ M'

-- infixl:50 " ≤ir " => Matroid.IsoRestr

-- theorem IsoRestr.isoMinor (h : N ≤ir M) : N ≤i M := by
--   obtain ⟨M', hMM', hNM'⟩ := h
--   exact ⟨M', hMM'.isMinor, hNM'⟩

-- theorem IsRestriction.IsoRestr {N M : Matroid α} (h : N ≤r M) : N ≤ir M :=
--   ⟨N, h, IsIso.refl N⟩

-- theorem IsoRestr.refl (M : Matroid α) : M ≤ir M :=
--   IsRestriction.refl.IsoRestr

-- theorem IsIso.isoRestr (h : N ≂ M) : M ≤ir N :=
--   ⟨N, IsRestriction.refl, h.symm⟩

-- @[simp] theorem emptyOn_isoRestr (β : Type*) (M : Matroid α) : emptyOn β ≤ir M :=
--   ⟨emptyOn α, by simp only [emptyOn_isRestriction], by simp only [isIso_emptyOn_iff]⟩

-- @[simp] theorem isoRestr_emptyOn_iff {M : Matroid α} : M ≤ir emptyOn β ↔ M = emptyOn α :=
--   ⟨fun h ↦ isoMinor_emptyOn_iff.1 h.isoMinor, by rintro rfl; simp⟩

-- theorem IsRestriction.trans_isIso {N M : Matroid α} {M' : Matroid β} (h : N ≤r M) (h' : M ≂ M') :
--     N ≤ir M' := by
--   obtain (⟨rfl,rfl⟩ | ⟨⟨i⟩⟩) := h'
--   · simpa using h
--   obtain ⟨D, hD, rfl⟩ := h.exists_eq_delete
--   exact ⟨_, delete_isRestriction _ _, (i.delete hD).isIso⟩

-- theorem IsoRestr.trans {α₁ α₂ α₃ : Type*} {M₁ : Matroid α₁} {M₂ : Matroid α₂} {M₃ : Matroid α₃}
--     (h₁₂ : M₁ ≤ir M₂) (h₂₃ : M₂ ≤ir M₃) : M₁ ≤ir M₃ := by
--   obtain ⟨N₁, hN₁M₂, hN₁M₁⟩ := h₁₂
--   obtain ⟨N₂, hN₂M₃, hN₂M₂⟩ := h₂₃
--   obtain ⟨N₁', hN₁'N₂, hN₁N₁'⟩ := hN₁M₂.trans_isIso hN₂M₂
--   exact ⟨N₁', hN₁'N₂.trans hN₂M₃, hN₁M₁.trans hN₁N₁'⟩

-- theorem isoMinor_iff_exists_contract_isoRestr {N : Matroid α} {M : Matroid β} :
--     N ≤i M ↔ ∃ C, M.Indep C ∧ N ≤ir M ／ C := by
--   refine ⟨fun h ↦ ?_, fun ⟨C, _, hN⟩ ↦ hN.isoMinor.trans (M.contract_isMinor C).isoMinor ⟩
--   obtain ⟨N', hN'M, hi⟩ := h
--   obtain ⟨C, hC, hN', -⟩ := hN'M.exists_contract_spanning_restrict
--   exact ⟨C, hC, ⟨_, hN', hi⟩⟩

-- end IsoRestr

-- section free_loopy

-- theorem isoMinor_loopyOn_iff {E : Set β} :
--     M ≤i loopyOn E ↔ M = loopyOn M.E ∧ Nonempty (M.E ↪ E) := by
--   simp_rw [IsoMinor, isMinor_loopyOn_iff]
--   refine ⟨fun ⟨M₀, hM₀, hM₀M⟩ ↦ ?_, fun ⟨hM, ⟨e⟩⟩ ↦ ?_⟩
--   · rw [hM₀.1, isIso_loopyOn_iff] at hM₀M
--     obtain ⟨e⟩ := hM₀M.2
--     exact ⟨hM₀M.1, ⟨e.toEmbedding.trans ⟨inclusion hM₀.2, inclusion_injective hM₀.2⟩⟩⟩
--   refine ⟨(loopyOn E) ↾ (((↑) : E → β) '' range e), by simp, ?_⟩
--   simp only [loopyOn_restrict, isIso_loopyOn_iff, and_iff_right hM]
--   convert Nonempty.intro <| Equiv.ofInjective (e.trans (Function.Embedding.subtype _))
--     ((e.trans _).injective)
--   rw [← image_univ, image_image, image_univ]
--   rfl

-- theorem isoMinor_freeOn_iff {E : Set β} :
--     M ≤i freeOn E ↔ M = freeOn M.E ∧ Nonempty (M.E ↪ E) := by
--   rw [← isoMinor_dual_iff, freeOn_dual_eq, isoMinor_loopyOn_iff, dual_ground,
--     ← eq_dual_iff_dual_eq, loopyOn_dual_eq]

-- theorem isoMinor_loopyOn_iff_of_finite {E : Set β} (hE : E.Finite) :
--     M ≤i loopyOn E ↔ M = loopyOn M.E ∧ M.E.encard ≤ E.encard := by
--   simp [Matroid.isoMinor_loopyOn_iff, ← hE.encard_le_iff_nonempty_embedding']

-- theorem isoMinor_freeOn_iff_of_finite {E : Set β} (hE : E.Finite) :
--     M ≤i freeOn E ↔ M = freeOn M.E ∧ M.E.encard ≤ E.encard := by
--   simp [Matroid.isoMinor_freeOn_iff, ← hE.encard_le_iff_nonempty_embedding']

-- theorem freeOn_isoMinor_iff {E : Set α} {M : Matroid β} :
--     freeOn E ≤i M ↔ ∃ (f : E ↪ β), M.Indep (range f) := by
--   simp_rw [IsoMinor, IsIso.comm (M := freeOn E), isIso_freeOn_iff]
--   refine ⟨fun ⟨M₀, hM₀M, hM₀free, ⟨e⟩⟩ ↦ ?_, fun ⟨f, hf⟩ ↦ ?_⟩
--   · use e.symm.toEmbedding.trans (Function.Embedding.subtype _)
--     refine Indep.of_isMinor ?_ hM₀M
--     nth_rw 1 [hM₀free ]
--     simp only [freeOn_indep_iff]
--     rintro _ ⟨x,hx,rfl⟩
--     simp
--   refine ⟨M ↾ (range f), M.restrict_isMinor hf.subset_ground, ?_⟩
--   rw [restrict_ground_eq, ← indep_iff_restrict_eq_freeOn, and_iff_right hf]
--   exact ⟨(Equiv.ofInjective f f.2).symm⟩

-- theorem freeOn_isoMinor_iff_of_finite {E : Set α} (hE : E.Finite) :
--     freeOn E ≤i M ↔ E.encard ≤ M.eRank := by
--   rw [Matroid.freeOn_isoMinor_iff]
--   refine ⟨fun ⟨f, hf⟩  ↦ ?_, fun h ↦ ?_⟩
--   · rw [encard_congr <| Equiv.ofInjective f f.2, ← hf.eRk]
--     apply eRk_le_eRank
--   obtain ⟨B, hB⟩ := M.exists_isBase
--   rw [← hB.encard, hE.encard_le_iff_nonempty_embedding] at h
--   obtain ⟨e⟩ := h
--   refine ⟨e.trans (Function.Embedding.subtype _), hB.indep.subset ?_⟩
--   rintro _ ⟨x, hx, rfl⟩
--   simp

-- theorem loopyOn_isoMinor_iff_of_finite {E : Set α} (hE : E.Finite) :
--     loopyOn E ≤i M ↔ E.encard ≤ M✶.eRank := by
--   rw [← isoMinor_dual_iff, loopyOn_dual_eq, freeOn_isoMinor_iff_of_finite hE]

-- end free_loopy
