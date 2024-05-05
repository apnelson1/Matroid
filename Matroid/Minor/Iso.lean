import Matroid.Minor.Basic
import Matroid.Minor.Rank
import Matroid.Constructions.Basic
import Matroid.Equiv
import Matroid.ForMathlib.Other
import Mathlib.Data.FunLike.Embedding

-- open Lean PrettyPrinter Delaborator SubExpr in
-- @[delab app.Matroid.Restriction]
-- private def delabRestriction : Delab :=
--   whenPPOption getPPNotation <| whenNotPPOption getPPExplicit do
--     guard <| (← getExpr).getAppNumArgs = 3
--     let a ← withAppFn <| withAppArg delab
--     let b ← withAppArg delab
--     `($a ≤r $b)

namespace Matroid



open Set Function PartialEquiv Set.Notation

variable {α β β' : Type*} {M : Matroid α} {N : Matroid β} {C D : Set α}
section Iso

/-- Deletions of isomorphic matroids are isomorphic. -/
def Iso.delete (e : Iso M N) (D : Set α) :
    Iso (M ＼ D) (N ＼ (↑(e '' M.E ↓∩ D) : Set β)) :=
  e.restrict (diff_subset _ _) (diff_subset _ _) (by aesop)

/-- Contractions of isomorphic matroids are isomorphic. -/
def Iso.contract (e : Iso M N) (C : Set α) :
    Iso (M ／ C) (N ／ (↑(e '' M.E ↓∩ C) : Set β)) :=
  (e.dual.delete C).dual

@[pp_nodot] structure IsoRestr (N : Matroid β) (M : Matroid α) :=
  (toFun : N.E → M.E)
  (inj' : Injective toFun)
  (indep_iff' : ∀ (I : Set N.E), N.Indep ↑I ↔ M.Indep ↑(toFun '' I))

scoped infix:65 " ≤ir " => IsoRestr

instance {α β : Type*} {N : Matroid α} {M : Matroid β} : FunLike (N ≤ir M) N.E M.E where
  coe f := f.toFun
  coe_injective' f g := by cases f; cases g; simp

instance {α β : Type*} {N : Matroid α} {M : Matroid β} : EmbeddingLike (N ≤ir M) N.E M.E where
  injective' f := f.inj'

theorem IsoRestr.indep_image_iff {N : Matroid α} {M : Matroid β} (i : N ≤ir M) {I : Set N.E} :
    M.Indep ↑(i '' I) ↔ N.Indep ↑I :=
  (i.indep_iff' I).symm

theorem IsoRestr.exists_restr_iso (i : N ≤ir M) : ∃ (M₀ : Matroid α) (_ : N ≂ M₀), M₀ ≤r M :=
  ⟨M ↾ ↑(range (Subtype.val ∘ i)),
    Iso.mk (Equiv.ofInjective _ <| Subtype.val_injective.comp (EmbeddingLike.injective i))
    (fun I ↦ by
      simp only [← i.indep_image_iff, restrict_ground_eq, comp_apply, Equiv.ofInjective_apply,
        restrict_indep_iff, image_subset_iff, Subtype.coe_preimage_self, subset_univ, and_true]
      simp [image_image]),
     restrict_restriction _ _ <| by simp [range_comp]⟩

def IsoRestr.trans {α₁ α₂ α₃ : Type*} {M₁ : Matroid α₁} {M₂ : Matroid α₂} {M₃ : Matroid α₃}
    (i₁ : M₁ ≤ir M₂) (i₂ : M₂ ≤ir M₃) : M₁ ≤ir M₃ where
  toFun := i₂ ∘ i₁
  inj' := Injective.comp (EmbeddingLike.injective i₂) (EmbeddingLike.injective i₁)
  indep_iff' I := by rw [← i₁.indep_image_iff, ← i₂.indep_image_iff]; simp [image_image]

/-- We have `N ≤i M` if `M` has an `N`-minor; i.e. `N` is isomorphic to a minor of `M`. This is
  defined to be type-heterogeneous.  -/
@[pp_nodot] structure IsoMinor (N : Matroid α) (M : Matroid β) :=
  (toFun : N.E → M.E)
  (inj' : Injective toFun)
  (exists_minor' : ∃ M₀, M₀ ≤m M ∧ M₀.E = ↑(range toFun) ∧
    ∀ (I : Set N.E), N.Indep I ↔ M₀.Indep ↑(toFun '' I))

scoped infix:65 " ≤i " => IsoMinor

instance {α β : Type*} {N : Matroid α} {M : Matroid β} : FunLike (N ≤i M) N.E M.E where
  coe f := f.toFun
  coe_injective' f g := by cases f; cases g; simp

instance {α β : Type*} {N : Matroid α} {M : Matroid β} : EmbeddingLike (N ≤i M) N.E M.E where
  injective' f := f.inj'

theorem IsoMinor.exists_minor {N : Matroid α} {M : Matroid β} (i : N ≤i M) :
    ∃ M₀, M₀ ≤m M ∧ M₀.E = ↑(range i) ∧ ∀ (I : Set N.E), N.Indep I ↔ M₀.Indep ↑(i '' I) :=
      i.exists_minor'

theorem IsoMinor.exists_iso {N : Matroid α} {M : Matroid β} (i : N ≤i M) :
    ∃ (M₀ : Matroid β) (hM₀ : M₀ ≤m M) (e : N ≂ M₀), ∀ x, inclusion hM₀.subset (e x) = i x := by
  obtain ⟨M₀, hM₀, hE, h⟩ := i.exists_minor
  refine ⟨M₀, hM₀,  ?_⟩
  have : M₀.E ≃ N.E := (Equiv.setCongr hE).trans ?_
  --  ((Equiv.ofInjective _ (Subtype.val_injective.comp (EmbeddingLike.injective i))).trans
  --   (Equiv.setCongr sorry))

  -- have : N ≂ M₀ := Iso.mk ((Equiv.ofInjective _ (EmbeddingLike.injective i)).trans (Equiv.setCongr sorry)) sorry
  -- have := Equiv.ofInjective _ (EmbeddingLike.injective i)

def IsoMinor.of_exists_iso {N : Matroid α} {M : Matroid β} (f : N.E → M.E)
  (h : ∃ (M₀ : Matroid β) (hM₀ : M₀ ≤m M) (e : N ≂ M₀), ∀ x, inclusion hM₀.subset (e x) = f x) :
  N ≤i M where
    toFun := f
    inj' x y hxy := by obtain ⟨M₀, hM₀, e, he⟩ := h; simpa [← he] using hxy
    exists_minor' := by
      obtain ⟨M₀, hM₀, e, he⟩ := h
      refine ⟨M₀, hM₀, ?_, fun I ↦ ?_⟩
      · ext x
        simp only [mem_image, mem_range, ← he, Subtype.exists, exists_and_right, exists_eq_right]
        refine ⟨fun h ↦  ⟨hM₀.subset h, _, (e.symm ⟨x,h⟩).2, by simp⟩, fun ⟨h, a, ha, h'⟩ ↦ ?_⟩
        simp_rw [← Subtype.coe_inj, coe_inclusion] at h'
        subst h'
        simp
      rw [e.indep_image_iff]
      convert Iff.rfl using 2
      ext x
      simp [← he]



def IsoMinor.of_iso {N : Matroid α} {M₀ M : Matroid β} (e : N ≂ M₀) (hM₀ : M₀ ≤m M) : N ≤i M where
  toFun x := (inclusion hM₀.subset) (e x)
  inj' := by rintro ⟨x, hx⟩ ⟨y, hy⟩; simp
  exists_minor' := ⟨M₀, hM₀, by simp, fun I ↦ by simp [e.indep_image_iff]⟩



-- def IsoMinor.of_forall_base {N : Matroid α} {M : Matroid β} (f : N.E → M.E) (hinj : Injective f)
--     {M₀ : Matroid β} (hM₀ : M₀ ≤m M) (hE : M₀.E = range f)
--     (hf : ∀ B : Set N.E, N.Base ↑B ↔ M₀.Base ↑(f '' B)) : N ≤i M := by
--     refine IsoMinor.of_iso (Iso.ofForallBase ?_ ?_ ) hM₀

--     · refine (Equiv.ofInjective _ (Subtype.val_injective.comp hinj)).trans
--         (Equiv.setCongr (by simpa [range_comp] using hE.symm ))
--     sorry

    -- where
    --   toFun := f
    --   inj' := hinj
    --   exists_minor' := ⟨M₀, hM₀, hE, fun I ↦ by
    --     simp_rw [indep_iff_subset_base]
    --     refine ⟨fun ⟨B, hB, hIB⟩ ↦ ?_, fun ⟨B, hB, hIB⟩ ↦ ?_⟩
    --     · obtain ⟨B, rfl⟩ := eq_image_val_of_subset hB.subset_ground
    --       rw [hf] at hB
    --       refine ⟨_, hB, ?_⟩
    --       rw [image_subset_image_iff Subtype.val_injective] at hIB ⊢
    --       exact image_subset _ hIB
    --     obtain ⟨B, rfl⟩ := eq_image_val_of_subset hB.subset_ground

    --     have := (hB.subset_ground.trans hE.subset)
    --     specialize hf (f ⁻¹' (B.image (inclusion hM₀.subset)))
    --     rw [image_preimage_eq_iff.2, image_val_image_inclusion] at hf
    --     · rw [← hf] at hB
    --       refine ⟨_, hB, ?_⟩
    --       simp at hIB ⊢
    --       convert hIB
    --       aesop


    --     -- rw [image_subset_image_iff Subtype.val_injective] at this
    --     -- have := (image_subset_image_iff Subtype.val_injective).2
    --     -- have := subset_range_iff_exists_image_eq.1
    --       ⟩




def IsoMinor.dual (N : Matroid β) (M : Matroid α) (i : N ≤i M) : N✶ ≤i M✶ :=
  IsoMinor.of_exists_iso i (by
    obtain ⟨M₀, hM₀, hM₀E, h⟩ := i.exists_minor
    refine ⟨M₀✶, hM₀.dual, ?_⟩


    )
  -- toFun := i
  -- exists_minor' := by
  --   obtain ⟨M₀, hM₀, hE, h⟩ := i.exists_minor
  --   refine ⟨M₀✶, hM₀.dual, by simpa, fun (I : Set N.E) ↦ ?_⟩
  --   simp only [dual_ground, image_subset_iff, Subtype.coe_preimage_self, subset_univ, image_image]
  --   have aux : ∀ I ⊆ N.E, N.Indep I ↔ M.Indep ↑(i '' (N.E ↓∩ I)) := sorry

  --   simp_rw [indep_iff_subset_base, dual_base_iff', base_iff_maximal_indep,
  --     aux _ (diff_subset _ _), preimage_diff, Subtype.coe_preimage_self, image_subset_iff]


  -- M₀ := e.M₀✶
  -- minor := e.minor.dual
  -- iso := e.iso.dual

-- noncomputable def IsoRestr.isoMinor (N : Matroid β) (M : Matroid α) (i : N ≤ir M) : N ≤i M where
--   M₀ := i.exists_restr_iso.choose
--   minor := by
--     obtain ⟨-, hi⟩ := i.exists_restr_iso.choose_spec
--     exact hi.minor
--   iso := i.exists_restr_iso.choose_spec.choose




  -- obtain ⟨M₀, i, h⟩ := i.exists_restr_iso







-- @[pp_nodot] structure IsoRestr (N : Matroid β) (M : Matroid α) :=
--   (M₀ : Matroid α)
--   (restr : M₀ ≤r M)
--   (iso : N ≂ M₀)

-- scoped infix:65 " ≤ir " => IsoRestr'

-- noncomputable def IsoRestr.ofFun {M : Matroid α} {N : Matroid β} (e : N.E ↪ M.E)
--   (h : ∀ (I : Set N.E), N.Indep ↑I → M.Indep ↑(e '' I)) : N ≤ir M where
--     M₀ := M ↾ ↑(range e)
--     restr := restrict_restriction _ _ <| by simp
--     iso := Iso.mk
--       ((Equiv.ofInjective _ e.injective).trans <|
--       by
--         sorry

--         )
--       sorry

-- def Restriction.trans_iso {M₀ : Matroid α} (h : M₀ ≤r M) (i : M ≂ N) : M₀ ≤ir N where
--   M₀ := N ↾ ↑(i '' (M.E ↓∩ M₀.E))
--   restr := restrict_restriction _ _ <| by simp
--   iso := Iso.mk (Equiv.subsetEquivSubset (i : M.E ≃ N.E) h.subset (by simp)
--     ( by
--       suffices ∀ a ∈ M.E, a ∈ M₀.E → a ∈ M.E by simpa
--       exact fun _ h _ ↦ h))
--     ( fun I ↦ by
--       obtain ⟨R, hR, rfl⟩ := h
--       simp only [restrict_ground_eq, restrict_indep_iff, image_subset_iff, image_val_eq_coe,
--         Subtype.coe_preimage_self, subset_univ, and_true, Equiv.subsetEquivSubset_image_val,
--         EquivLike.coe_coe, preimage_val_image_val_eq_self, Iso.preimage_image]
--       convert i.indep_image_iff (I := inclusion hR '' I) using 1 <;> simp )

-- def IsoRestr.trans {α₁ α₂ α₃ : Type*} {M₁ : Matroid α₁} {M₂ : Matroid α₂} {M₃ : Matroid α₃}
--     (i₁ : M₁ ≤ir M₂) (i₂ : M₂ ≤ir M₃) : M₁ ≤ir M₃ :=
--   have h_eq : i₁.M₀ = M₂.restrict i₁.M₀.E := sorry
--   IsoRestr.mk
--   (M₀ := (i₁.restr.trans_iso i₂.iso).M₀)
--   (restr := (i₁.restr.trans_iso i₂.iso).restr.trans i₂.restr)
--   (iso := i₁.iso.trans ((Iso.ofEq h_eq).trans <| by


--     simp [Restriction.trans_iso]
--     refine i₂.iso.restrict (R := i₁.M₀.E) (i₁.restr.subset) (by simp) ?_
--     simp




--     ))


-- /-- We have `N ≤i M` if `M` has an `N`-minor; i.e. `N` is isomorphic to a minor of `M`. This is
--   defined to be type-heterogeneous.  -/
-- @[pp_nodot] structure IsoMinor (N : Matroid β) (M : Matroid α) :=
--   (M₀ : Matroid α)
--   (minor : M₀ ≤m M)
--   (iso : N ≂ M₀)

-- scoped infix:65 " ≤i " => IsoMinor

-- def IsoMinor.dual (N : Matroid β) (M : Matroid α) (e : N ≤i M) : N✶ ≤i M✶ where
--   M₀ := e.M₀✶
--   minor := e.minor.dual
--   iso := e.iso.dual

-- def IsoRestr.isoMinor (N : Matroid β) (M : Matroid α) (e : N ≤ir M) : N ≤i M where
--   M₀ := e.M₀
--   minor := e.restr.minor
--   iso := e.iso



-- def IsoMinor.trans {α₁ α₂ α₃ : Type*} {M₁ : Matroid α₁} {M₂ : Matroid α₂} {M₃ : Matroid α₃}
--     (i₁ : M₁ ≤i M₂) (i₂ : M₂ ≤i M₃) : M₁ ≤i M₃ where
--   M₀ := i₂.M₀
--   minor := by
--     have := i₁.minor

--   iso := sorry

-- noncomputable def foo {γ : Type*} (M₀ : Matroid α) (M₁ : Matroid β) (M₂ : Matroid γ)
--     (h0 : M₀ ≤ir M₁) (h1 : M₁✶ ≤ir M₂✶) :
--     M₀ ≤i M₂ := by
--   obtain ⟨N₀, hr, i₀⟩ := h0
--   obtain ⟨N₁, hrd, i₁⟩ := h1
--   have := hr.trans_isoRestr <| i₁.symm.dual_comm.symm

-- def Minor.trans_isoMinor {M₀ : Matroid α} (h : M₀ ≤m M) (i : M ≂ N) : M₀ ≤i N where
--   M₀ := M₀.mapSetSetEmbedding <| (embeddingOfSubset _ _ h.subset).trans (i : M.E ≃ N.E).toEmbedding
--   minor := by
--     sorry
--   iso := sorry
  -- have := (embeddingOfSubset _ _ h.subset).trans (i : M.E ≃ N.E).toEmbedding
  -- have := M₀.mapSetSetEmbedding _ this
  -- set f : M₀.E ↪ β := (Embedding.setSubtype h.subset).trans sorry
  -- have := (i : M.E ≃ N.E).subsetEquivSubset (a := M₀.E) (b := )
  -- have := M₀.mapSetEmbedding (Equiv.toEmbedding (i : M.E ≃ N.E))



-- /-- Deletions of isomorphic matroids are isomorphic. TODO : Actually define as a term. -/
-- noncomputable def Iso.delete (e : Iso M N) (hD : D ⊆ M.E) :
--     Iso (M ＼ D) (N ＼ e '' D) := by
--   convert Iso.restrict e (M.E \ D) using 1
--   rw [e.injOn_ground.image_diff hD, e.image_ground, ← restrict_compl]

-- noncomputable def Iso.contract (e : Iso M N) (hC : C ⊆ M.E) :
--     Iso (M ／ C) (N ／ e '' C) :=
--   (e.dual.delete hC).dual



-- infixl:50 " ≤i " => Matroid.IsoMinor

-- instance isoMinor_refl : IsRefl (Matroid α) (· ≤i ·) :=
--   ⟨fun M ↦ ⟨M, Minor.refl, IsIso.refl M⟩⟩

-- theorem IsIso.isoMinor (h : M ≂ N) : M ≤i N :=
--   ⟨N, Minor.refl, h⟩

-- theorem Iso.isoMinor (e : Iso N M) : N ≤i M :=
--   e.isIso.isoMinor

-- @[simp] theorem emptyOn_isoMinor (α : Type*) (M : Matroid β) : emptyOn α ≤i M := by
--   refine ⟨emptyOn β, ?_, isIso_emptyOn_emptyOn _ _⟩
--   rw [← M.delete_ground_self]
--   apply delete_minor

-- @[simp] theorem isoMinor_emptyOn_iff : M ≤i emptyOn β ↔ M = emptyOn α := by
--   refine ⟨fun h ↦ ?_, ?_⟩
--   · obtain ⟨N, hN, hMN⟩ := h
--     obtain rfl := minor_emptyOn_iff.1 hN
--     rwa [isIso_emptyOn_iff] at hMN
--   rintro rfl
--   apply emptyOn_isoMinor

-- theorem Minor.trans_isIso {M N : Matroid α} {M' : Matroid β} (h : N ≤m M) (hi : M ≂ M') :
--     N ≤i M' := by
--   obtain (⟨rfl,rfl⟩ | ⟨-, -, ⟨i⟩⟩) := hi.empty_or_nonempty_iso
--   · simpa using h
--   obtain ⟨C, D, hC, hD, hCD, rfl⟩ := h
--   exact ⟨_, contract_delete_minor _ _ _,
--     ((i.contract hC).delete (subset_diff.2 ⟨hD, hCD.symm⟩)).isIso⟩

-- theorem Minor.isoMinor {M N : Matroid α} (h : N ≤m M) : N ≤i M :=
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

-- theorem IsoMinor.erk_le_erk (h : N ≤i M) : N.erk ≤ M.erk := by
--   obtain ⟨N', hN', hNM⟩ := h
--   exact hNM.erk_eq_erk.le.trans hN'.erk_le

-- theorem IsoMinor.encard_ground_le_encard_ground (h : N ≤i M) : N.E.encard ≤ M.E.encard := by
--   obtain ⟨N', hN', (⟨rfl,rfl⟩ | ⟨⟨e⟩⟩)⟩ := h; simp
--   have hss := encard_le_card <| e.image_ground.subset.trans hN'.subset
--   rwa [e.injOn_ground.encard_image] at hss

-- end Iso

-- section IsoRestr

-- /-- Type-heterogeneous statement that `N` is isomorphic to a restriction of `M` -/
-- def IsoRestr (N : Matroid β) (M : Matroid α) : Prop :=
--   ∃ M' : Matroid α, M' ≤r M ∧ N ≂ M'

-- infixl:50 " ≤ir " => Matroid.IsoRestr

-- theorem IsoRestr.isoMinor (h : N ≤ir M) : N ≤i M := by
--   obtain ⟨M', hMM', hNM'⟩ := h
--   exact ⟨M', hMM'.minor, hNM'⟩

-- theorem Restriction.IsoRestr {N M : Matroid α} (h : N ≤r M) : N ≤ir M :=
--   ⟨N, h, IsIso.refl N⟩

-- theorem IsoRestr.refl (M : Matroid α) : M ≤ir M :=
--   Restriction.refl.IsoRestr

-- theorem IsIso.isoRestr (h : N ≂ M) : M ≤ir N :=
--   ⟨N, Restriction.refl, h.symm⟩

-- @[simp] theorem emptyOn_isoRestr (β : Type*) (M : Matroid α) : emptyOn β ≤ir M :=
--   ⟨emptyOn α, by simp only [emptyOn_restriction], by simp only [isIso_emptyOn_iff]⟩

-- @[simp] theorem isoRestr_emptyOn_iff {M : Matroid α} : M ≤ir emptyOn β ↔ M = emptyOn α :=
--   ⟨fun h ↦ isoMinor_emptyOn_iff.1 h.isoMinor, by rintro rfl; simp⟩

-- theorem Restriction.trans_isIso {N M : Matroid α} {M' : Matroid β} (h : N ≤r M) (h' : M ≂ M') :
--     N ≤ir M' := by
--   obtain (⟨rfl,rfl⟩ | ⟨⟨i⟩⟩) := h'
--   · simpa using h
--   obtain ⟨D, hD, rfl⟩ := h.exists_eq_delete
--   exact ⟨_, delete_restriction _ _, (i.delete hD).isIso⟩

-- theorem IsoRestr.trans {α₁ α₂ α₃ : Type*} {M₁ : Matroid α₁} {M₂ : Matroid α₂} {M₃ : Matroid α₃}
--     (h₁₂ : M₁ ≤ir M₂) (h₂₃ : M₂ ≤ir M₃) : M₁ ≤ir M₃ := by
--   obtain ⟨N₁, hN₁M₂, hN₁M₁⟩ := h₁₂
--   obtain ⟨N₂, hN₂M₃, hN₂M₂⟩ := h₂₃
--   obtain ⟨N₁', hN₁'N₂, hN₁N₁'⟩ := hN₁M₂.trans_isIso hN₂M₂
--   exact ⟨N₁', hN₁'N₂.trans hN₂M₃, hN₁M₁.trans hN₁N₁'⟩

-- theorem isoMinor_iff_exists_contract_isoRestr {N : Matroid α} {M : Matroid β} :
--     N ≤i M ↔ ∃ C, M.Indep C ∧ N ≤ir M ／ C := by
--   refine ⟨fun h ↦ ?_, fun ⟨C, _, hN⟩ ↦ hN.isoMinor.trans (M.contract_minor C).isoMinor ⟩
--   obtain ⟨N', hN'M, hi⟩ := h
--   obtain ⟨C, hC, hN', -⟩ := hN'M.exists_contract_spanning_restrict
--   exact ⟨C, hC, ⟨_, hN', hi⟩⟩

-- end IsoRestr

-- section free_loopy

-- theorem isoMinor_loopyOn_iff {E : Set β} :
--     M ≤i loopyOn E ↔ M = loopyOn M.E ∧ Nonempty (M.E ↪ E) := by
--   simp_rw [IsoMinor, minor_loopyOn_iff]
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
--     refine Indep.of_minor ?_ hM₀M
--     nth_rw 1 [hM₀free ]
--     simp only [freeOn_indep_iff]
--     rintro _ ⟨x,hx,rfl⟩
--     simp
--   refine ⟨M ↾ (range f), M.restrict_minor hf.subset_ground, ?_⟩
--   rw [restrict_ground_eq, ← indep_iff_restrict_eq_freeOn, and_iff_right hf]
--   exact ⟨(Equiv.ofInjective f f.2).symm⟩

-- theorem freeOn_isoMinor_iff_of_finite {E : Set α} (hE : E.Finite) :
--     freeOn E ≤i M ↔ E.encard ≤ M.erk := by
--   rw [Matroid.freeOn_isoMinor_iff]
--   refine ⟨fun ⟨f, hf⟩  ↦ ?_, fun h ↦ ?_⟩
--   · rw [encard_congr <| Equiv.ofInjective f f.2, ← hf.er]
--     apply er_le_erk
--   obtain ⟨B, hB⟩ := M.exists_base
--   rw [← hB.encard, hE.encard_le_iff_nonempty_embedding] at h
--   obtain ⟨e⟩ := h
--   refine ⟨e.trans (Function.Embedding.subtype _), hB.indep.subset ?_⟩
--   rintro _ ⟨x, hx, rfl⟩
--   simp

-- theorem loopyOn_isoMinor_iff_of_finite {E : Set α} (hE : E.Finite) :
--     loopyOn E ≤i M ↔ E.encard ≤ M✶.erk := by
--   rw [← isoMinor_dual_iff, loopyOn_dual_eq, freeOn_isoMinor_iff_of_finite hE]

-- end free_loopy
