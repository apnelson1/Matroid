module

public import Mathlib.Order.Hom.CompleteLattice

/-!
# Extending order isomorphisms between dense subsets

Lower-cut suprema extend an order isomorphism between order-dense subsets of complete
linear orders. The extension preserves the supplied isomorphism on its domain, is unique
among monotone extensions, and commutes with identities, composition, and inverses.
-/

@[expose] public section

open Set Function

namespace OrderIso

section Definition

variable {A B : Type*} [LE A] [LE B] [SupSet B] {s : Set A} {t : Set B}

/-- Extend a supplied order isomorphism of order-dense subsets by taking lower-cut suprema. -/
noncomputable def extendDense (e : s ≃o t) (x : A) : B :=
  sSup {y | ∃ d : s, d.val ≤ x ∧ (e d).val = y}

end Definition

section Bounds

variable {A B : Type*} [LE A] [CompleteSemilatticeSup B] {s : Set A} {t : Set B}

lemma extendDense_le (e : s ≃o t) {x : A} {y : B}
    (h : ∀ d : s, d.val ≤ x → (e d).val ≤ y) : e.extendDense x ≤ y := by
  apply sSup_le
  rintro _ ⟨d, hd, rfl⟩
  exact h d hd

lemma le_extendDense (e : s ≃o t) (d : s) {x : A} (hd : d.val ≤ x) :
    (e d).val ≤ e.extendDense x :=
  le_sSup ⟨d, hd, rfl⟩

end Bounds

section Extension

variable {A B : Type*} [Preorder A] [CompleteSemilatticeSup B] {s : Set A} {t : Set B}

lemma monotone_extendDense (e : s ≃o t) : Monotone e.extendDense := by
  intro x y hxy
  exact e.extendDense_le fun d hd ↦ e.le_extendDense d (hd.trans hxy)

@[simp]
lemma extendDense_coe (e : s ≃o t) (d : s) : e.extendDense d.val = (e d).val :=
  (e.extendDense_le fun _ hz ↦ e.monotone hz).antisymm (e.le_extendDense d le_rfl)

end Extension

section Comparison

variable {A B : Type*} [Preorder A] [@Std.Total A (· ≤ ·)] [CompleteSemilatticeSup B]
  {s : Set A} {t : Set B}

lemma le_extendDense_iff (e : s ≃o t)
    (hs : ∀ a b : A, a < b → ∃ d ∈ s, a < d ∧ d < b)
    (d : s) (x : A) : (e d).val ≤ e.extendDense x ↔ d.val ≤ x := by
  refine ⟨fun h ↦ ?_, e.le_extendDense d⟩
  by_contra hdx
  have hxd : x < d.val := lt_of_le_not_ge
    ((total_of (· ≤ ·) x d.val).resolve_right hdx) hdx
  obtain ⟨c, hc, hxc, hcd⟩ := hs x d.val hxd
  have hbound : e.extendDense x ≤ (e ⟨c, hc⟩).val :=
    e.extendDense_le fun z hz ↦ e.monotone (hz.trans hxc.le)
  exact (e.strictMono hcd).not_ge (h.trans hbound)

end Comparison

section Uniqueness

variable {A B : Type*} [Preorder A] [@Std.Total A (· ≤ ·)] [CompleteLinearOrder B]
  {s : Set A} {t : Set B}

/-- The lower-cut extension is the unique monotone map agreeing with a supplied map
whose image is order-dense. -/
lemma extendDense_unique (e : s ≃o t)
    (ht : ∀ a b : B, a < b → ∃ d ∈ t, a < d ∧ d < b)
    {g : A → B} (hg : Monotone g) (hagree : ∀ d : s, g d.val = (e d).val) :
    g = e.extendDense := by
  apply funext
  intro x
  apply le_antisymm
  · by_contra! h
    obtain ⟨d, hd, hxd, hdg⟩ := ht _ _ h
    let c : s := e.symm ⟨d, hd⟩
    have hcx : ¬ c.val ≤ x := by
      intro hcx
      have h := e.le_extendDense c hcx
      exact hxd.not_ge (by simpa only [c, apply_symm_apply] using h)
    have hbound := hg ((total_of (· ≤ ·) x c.val).resolve_right hcx)
    rw [hagree c] at hbound
    exact hdg.not_ge (by simpa only [c, apply_symm_apply] using hbound)
  · exact e.extendDense_le fun d hd ↦ (hagree d).symm.trans_le (hg hd)

end Uniqueness

section Completion

variable {A B : Type*} [CompleteLinearOrder A] [CompleteLinearOrder B]
  {s : Set A} {t : Set B}

lemma extendDense_leftInverse (e : s ≃o t)
    (hs : ∀ a b : A, a < b → ∃ d ∈ s, a < d ∧ d < b)
    (ht : ∀ a b : B, a < b → ∃ d ∈ t, a < d ∧ d < b) :
    LeftInverse e.symm.extendDense e.extendDense := by
  intro x
  have hcuts (d : s) : d.val ≤ e.symm.extendDense (e.extendDense x) ↔ d.val ≤ x := by
    simpa only [e.symm_apply_apply] using
      (e.symm.le_extendDense_iff ht (e d) (e.extendDense x)).trans
        (e.le_extendDense_iff hs d x)
  apply le_antisymm
  · by_contra! h
    obtain ⟨d, hd, hxd, hdg⟩ := hs x _ h
    exact hxd.not_ge ((hcuts ⟨d, hd⟩).mp hdg.le)
  · by_contra! h
    obtain ⟨d, hd, hgd, hdx⟩ := hs _ x h
    exact hgd.not_ge ((hcuts ⟨d, hd⟩).mpr hdx.le)

/-- Order-dense subsets determine their complete linear orders up to order isomorphism. -/
noncomputable def completion (e : s ≃o t)
    (hs : ∀ a b : A, a < b → ∃ d ∈ s, a < d ∧ d < b)
    (ht : ∀ a b : B, a < b → ∃ d ∈ t, a < d ∧ d < b) : A ≃o B where
  toFun := e.extendDense
  invFun := e.symm.extendDense
  left_inv := e.extendDense_leftInverse hs ht
  right_inv := e.symm.extendDense_leftInverse ht hs
  map_rel_iff' := by
    intro x y
    refine ⟨fun h ↦ le_of_not_gt fun hyx ↦ ?_, fun h ↦ ?_⟩
    · obtain ⟨d, hd, hyd, hdx⟩ := hs y x hyx
      have hdy : (e ⟨d, hd⟩).val ≤ e.extendDense y :=
        (e.le_extendDense ⟨d, hd⟩ hdx.le).trans h
      exact hyd.not_ge ((e.le_extendDense_iff hs ⟨d, hd⟩ y).mp hdy)
    · exact e.monotone_extendDense h

@[simp]
lemma completion_coe (e : s ≃o t)
    (hs : ∀ a b : A, a < b → ∃ d ∈ s, a < d ∧ d < b)
    (ht : ∀ a b : B, a < b → ∃ d ∈ t, a < d ∧ d < b) (d : s) :
    e.completion hs ht d.val = (e d).val :=
  e.extendDense_coe d

lemma completion_symm (e : s ≃o t)
    (hs : ∀ a b : A, a < b → ∃ d ∈ s, a < d ∧ d < b)
    (ht : ∀ a b : B, a < b → ∃ d ∈ t, a < d ∧ d < b) :
    (e.completion hs ht).symm = e.symm.completion ht hs := by
  ext x
  rfl

@[simp]
lemma completion_refl
    (hs : ∀ a b : A, a < b → ∃ d ∈ s, a < d ∧ d < b) :
    (OrderIso.refl s).completion hs hs = OrderIso.refl A := by
  apply DFunLike.ext
  intro x
  exact congrFun ((OrderIso.refl s).extendDense_unique hs monotone_id (fun _ ↦ rfl)).symm x

lemma completion_trans {C : Type*} [CompleteLinearOrder C] {u : Set C}
    (e : s ≃o t) (f : t ≃o u)
    (hs : ∀ a b : A, a < b → ∃ d ∈ s, a < d ∧ d < b)
    (ht : ∀ a b : B, a < b → ∃ d ∈ t, a < d ∧ d < b)
    (hu : ∀ a b : C, a < b → ∃ d ∈ u, a < d ∧ d < b) :
    (e.trans f).completion hs hu = (e.completion hs ht).trans (f.completion ht hu) := by
  apply DFunLike.ext
  intro x
  apply congrFun ((e.trans f).extendDense_unique hu
    ((f.completion ht hu).monotone.comp (e.completion hs ht).monotone) ?_).symm x
  intro d
  change f.completion ht hu (e.completion hs ht d.val) = (f (e d)).val
  rw [completion_coe, completion_coe]

end Completion

end OrderIso
