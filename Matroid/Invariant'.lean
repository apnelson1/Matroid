module

public import Matroid.ForMathlib.Matroid.Map
public import Matroid.ForMathlib.Matroid.Dual
public import Matroid.ForMathlib.Matroid.Closure

@[expose] public section

namespace Matroid

open Set Function

section InvariantSetPred

universe u v w u' v'

variable {α : Type u} {β : Type v} {M : Matroid α} {f : α → β}

/-- MatroidSupportClass `γ` means that for `M : Matroid α`, terms of type `γ α` have a notion of
'supported' that depends only on the ground set of `M`. For sets, this is containment in `M.E`,
and for elements, this is membership in `M.E`.  -/
class MatroidSupportClass (γ : Type u → Type u') where
  supported : ∀ {α : Type u}, Matroid α → γ α → Prop
  congr : ∀ {α} {M M' : Matroid α}, M.E = M'.E → ∀ X, supported M X ↔ supported M' X

instance : MatroidSupportClass Set where
  supported M X := X ⊆ M.E
  congr := by simp +contextual

instance : MatroidSupportClass id where
  supported M x := x ∈ M.E
  congr := by simp +contextual

class MatroidSupportedMonoClass (γ : Type u → Type u') [S : MatroidSupportClass γ]
    [∀ α, Preorder (γ α)] : Prop where
  mono : ∀ {α} {M : Matroid α} x y, S.supported M y → x ≤ y → S.supported M x

instance : MatroidSupportedMonoClass Set where
  mono := fun _ _ hY hXY ↦ hXY.trans hY

@[simp]
lemma supported_set_iff (M : Matroid α) (X) : MatroidSupportClass.supported M X ↔ X ⊆ M.E := Iff.rfl

@[simp]
lemma supported_elem_iff (M : Matroid α) (x : α) :
    MatroidSupportClass.supported (γ := id) M x ↔ x ∈ M.E := Iff.rfl

/-- A predicate of type `γ α → Prop` is grounded if it is only true for elements of `γ α`
that are grounded. -/
class GroundedPred {γ : Type u → Type u'} [S : MatroidSupportClass γ]
    (P : ∀ {α}, Matroid α → γ α → Prop) where
  supported : ∀ ⦃α⦄ ⦃M : Matroid α⦄ ⦃x⦄, P M x → S.supported M x

class GroundedPred₂ {γ γ' : Type u → Type u'} [S : MatroidSupportClass γ]
    [S' : MatroidSupportClass γ'] (P : ∀ {α}, Matroid α → γ α → γ' α → Prop) where
  supported : ∀ ⦃α⦄ ⦃M : Matroid α⦄ ⦃x y⦄, P M x y → (S.supported M x ∧ S'.supported M y)

instance : GroundedPred Indep where
  supported _ _ _ := Indep.subset_ground

instance : GroundedPred Dep where
  supported _ _ _ := Dep.subset_ground

instance : GroundedPred IsBase where
  supported _ _ _ := IsBase.subset_ground

instance : GroundedPred Spanning where
  supported _ _ _ := Spanning.subset_ground

instance : GroundedPred Nonspanning where
  supported _ _ _ := Nonspanning.subset_ground

instance : GroundedPred Coindep where
  supported _ _ _ := Coindep.subset_ground

instance : GroundedPred Codep where
  supported _ _ _ := Codep.subset_ground

instance : GroundedPred₂ IsBasis where
  supported _ _ _ _ h := ⟨h.indep.subset_ground, h.subset_ground⟩

class MatroidTransferClass (γ : Type u → Type u') (δ : Type v → Type v')
    [Sγ : MatroidSupportClass γ] [Sδ : MatroidSupportClass δ] where
  transfer : ∀ {α : Type u} {β : Type v}, (α → β) → (γ α → δ β)
  transferEmpty : ∀ (α β), IsEmpty β → (x : γ α) → Sγ.supported (emptyOn α) x → δ β
  supported_transfer : ∀ ⦃α β⦄ ⦃M : Matroid α⦄ ⦃f : α → β⦄ (hf : InjOn f M.E) ⦃x : γ α⦄,
    Sγ.supported M x → Sδ.supported (M.map f hf) (transfer f x)
  supported_transferEmpty : ∀ (α β) (hβ : IsEmpty β) (x : γ α) (hx : Sγ.supported (emptyOn α) x),
    Sδ.supported (emptyOn β) (transferEmpty α β hβ x hx)

class MatroidTransferClass' (γ : Type u → Type u') (δ : Type v → Type v')
    [Sγ : MatroidSupportClass γ] [Sδ : MatroidSupportClass δ] where
  transfer : ∀ {α : Type u} {β : Type v} {M : Matroid α} {N : Matroid β},
    (M.E ≃ N.E) → {x : γ α | Sγ.supported M x} → {y : δ β | Sδ.supported N y}
  --     (γ α → δ β)
  -- transferEmpty : ∀ (α β), IsEmpty β → (x : γ α) → Sγ.supported (emptyOn α) x → δ β
  -- supported_transfer : ∀ ⦃α β⦄ ⦃M : Matroid α⦄ ⦃f : α → β⦄ (hf : InjOn f M.E) ⦃x : γ α⦄,
  --   Sγ.supported M x → Sδ.supported (M.map f hf) (transfer f x)
  -- supported_transferEmpty : ∀ (α β) (hβ : IsEmpty β) (x : γ α) (hx : Sγ.supported (emptyOn α) x),
  --   Sδ.supported (emptyOn β) (transferEmpty α β hβ x hx)

instance instId : MatroidTransferClass id id where
  transfer := id
  transferEmpty _ _ _ _ h := by simp [supported_elem_iff] at h
  supported_transfer _ _ _ _ _ x hx := ⟨x, hx, rfl⟩
  supported_transferEmpty := by simp

instance instSet : MatroidTransferClass Set Set where
  transfer := Set.image
  transferEmpty := fun _ _ _ _ _ ↦ ∅
  supported_transfer _ _ _ _ _ _ := image_mono
  supported_transferEmpty := by simp

@[simp]
lemma transfer_set_eq (X : Set α) (f : α → β) :
    MatroidTransferClass.transfer f X = f '' X := rfl

@[simp]
lemma transferEmpty_set_eq [hβ : IsEmpty β] {X : Set α}
    (hX : MatroidSupportClass.supported (emptyOn α) X) :
  MatroidTransferClass.transferEmpty (γ := Set) (δ := Set) α β hβ X hX = ∅ := rfl

class InvariantFun {γ : Type u → Type u'} {δ : Type v → Type v'} {μ : Sort w}
    [S : MatroidSupportClass γ] [T : MatroidSupportClass δ] [C : MatroidTransferClass γ δ]
    (F : ∀ {α}, Matroid α → (γ α) → μ) (G : ∀ {β}, Matroid β → (δ β) → μ) : Prop where
  of_empty : ∀ ⦃α β⦄ (hβ : IsEmpty β) ⦃x : γ α⦄ (hx : S.supported (emptyOn α) x),
    F (emptyOn α) x = G (emptyOn β) (C.transferEmpty α β hβ x hx)
  map_eq : ∀ ⦃α β⦄ ⦃M : Matroid α⦄ ⦃f : α → β⦄ (hf : InjOn f M.E) ⦃x : γ α⦄,
    S.supported M x → F M x = G (M.map f hf) (C.transfer f x)

class InvariantFun₂ {γ γ' : Type u → Type u'} {δ δ' : Type v → Type v'} {μ : Sort w}
    [S : MatroidSupportClass γ] [T : MatroidSupportClass δ] [C : MatroidTransferClass γ δ]
    [S' : MatroidSupportClass γ'] [T' : MatroidSupportClass δ'] [C' : MatroidTransferClass γ' δ']
    (F : ∀ {α}, Matroid α → (γ α) → (γ' α) → μ) (G : ∀ {β}, Matroid β → (δ β) → (δ' β) → μ) : Prop
      where
  of_empty_left : ∀ ⦃α β⦄ (hβ : IsEmpty β) ⦃x : γ α⦄ (hx : S.supported (emptyOn α) x),
    F (emptyOn α) x = G (emptyOn β) (C.transferEmpty α β hβ x hx)
  map_eq : ∀ ⦃α β⦄ ⦃M : Matroid α⦄ ⦃f : α → β⦄ (hf : InjOn f M.E) ⦃x x'⦄, S.supported M x →
    S'.supported M x' → F M x x' = G (M.map f hf) (C.transfer f x) (C'.transfer f x')

namespace InvariantFun

variable {γ : Type u → Type u'} {δ : Type v → Type v'} {μ : Sort w}
    [S : MatroidSupportClass γ] [T : MatroidSupportClass δ] [C : MatroidTransferClass γ δ]
    {F : ∀ {α}, Matroid α → (γ α) → μ} {G : ∀ {β}, Matroid β → (δ β) → μ}

protected lemma comp_right (F : ∀ {α}, Matroid α → (γ α) → μ) (G : ∀ {β}, Matroid β → (δ β) → μ)
    [h : InvariantFun F G] (s : μ → μ) :
    InvariantFun (fun M x ↦ s (F M x)) (fun N y ↦ s (G N y)) where
  of_empty _ _ _ _ _ := by rw [h.of_empty]
  map_eq _ _ _ _ hf _ hx := by rw [h.map_eq hf hx]

protected lemma comp (F : ∀ {α}, Matroid α → (γ α) → μ) (G : ∀ {β}, Matroid β → (δ β) → μ)
    [h : InvariantFun F G] (a : ∀ {α}, Matroid α → γ α → γ α) (b : ∀ {β}, Matroid β → δ β → δ β)
    (ha : ∀ {α} (M : Matroid α) x, S.supported M x → S.supported M (a M x))
    (hab0 : ∀ {α β} (hβ : IsEmpty β) (x) (hx : S.supported (emptyOn α) x),
      C.transferEmpty α β hβ (a (emptyOn α) x) (ha _ _ hx)
      = b (emptyOn β) (C.transferEmpty α β hβ x hx))
    (hab : ∀ {α β} (M) (f : α → β) (hf : InjOn f M.E) (x), S.supported M x →
      (C.transfer f (a M x)) = b (M.map f hf) (C.transfer f x)) :
    InvariantFun (γ := γ) (δ := δ) (fun M X ↦ F M (a M X)) (fun N Y ↦ G N (b N Y)) where
  of_empty α β hβ x hx := by rw [h.of_empty hβ (ha _ _ hx), hab0]
  map_eq α β M f hf x hxE := by rw [h.map_eq hf (x := a M x) (ha _ _ hxE), hab _ _ _ _ hxE]

protected lemma combine (F F' : ∀ {α}, Matroid α → (γ α) → μ) (G G' : ∀ {β}, Matroid β → (δ β) → μ)
    [h : InvariantFun F G] [h' : InvariantFun F' G'] (φ : μ → μ → μ) :
    InvariantFun (fun {α} (M : Matroid α) (x : γ α) ↦ φ (F M x) (F' M x))
      (fun {β} (N : Matroid β) (x : δ β) ↦ φ (G N x) (G' N x)) where
  of_empty α β hβ x hx := by rw [h.of_empty hβ hx, h'.of_empty hβ hx]
  map_eq α β M f hf x hxE := by rw [h.map_eq hf hxE, h'.map_eq hf hxE]

protected lemma of_const (F : ∀ {α}, (γ α) → μ) (G : ∀ {β}, (δ β) → μ)
    (h0 : ∀ {α β} (hβ : IsEmpty β) ⦃x : γ α⦄ (hx : S.supported (emptyOn α) x),
      F x = G (C.transferEmpty α β hβ x hx))
    (hFG : ∀ {α β} (f : α → β) (X : γ α), F X = G (C.transfer f X)) :
    InvariantFun (γ := γ) (δ := δ) (fun _ X ↦ F X) (fun _ X ↦ G X) where
  of_empty _ _ _ _ _ := by rw [h0]
  map_eq _ _ _ _ _ _ _ := by rw [hFG]

protected lemma dual (F : ∀ {α}, Matroid α → γ α → μ) (G : ∀ {β}, Matroid β → δ β → μ)
    [h : InvariantFun F G] : InvariantFun (fun M X ↦ F M✶ X) (fun N Y ↦ G N✶ Y) where
  of_empty α β hβ x hx := by
    simp only [emptyOn_dual_eq]
    rw [h.of_empty]
  map_eq α β M f hf x hx := by
    rw [map_dual']
    exact h.map_eq (M := M✶) (f := f) (by simpa) (x := x) (by rwa [S.congr (M' := M) (by simp)])

protected lemma compl (F : ∀ {α}, Matroid α → Set α → μ) (G : ∀ {β}, Matroid β → Set β → μ)
    [h : InvariantFun F G] :
    InvariantFun (γ := Set) (δ := Set) (fun M X ↦ F M (M.E \ X)) (fun N Y ↦ G N (N.E \ Y)) := by
  apply InvariantFun.comp F G
  · simp only [supported_set_iff, emptyOn_ground, subset_empty_iff, empty_sdiff]
    rintro α β hβ x rfl
    rfl
  · intro α β M f hf X (hXE : X ⊆ M.E)
    simp only [transfer_set_eq, map_ground, hf.image_sdiff_subset hXE]
  simp

section Pred

variable {P : ∀ {α : Type u}, Matroid α → (γ α) → Prop}
  {Q : ∀ {β : Type v}, Matroid β → (δ β) → Prop}

protected lemma map [h : InvariantFun P Q] [hP : GroundedPred P] {M : Matroid α} {f : α → β} {x}
    (hx : P M x) (hf : InjOn f M.E) : Q (M.map f hf) (C.transfer f x) := by
  rwa [← h.map_eq _ (hP.supported hx)]

protected lemma map_set {P : ∀ {α}, Matroid α → Set α → Prop} {Q : ∀ {β}, Matroid β → Set β → Prop}
    [h : InvariantFun P Q] [hP : GroundedPred P] {M : Matroid α} {f : α → β} {x}
    (hx : P M x) (hf : InjOn f M.E) : Q (M.map f hf) (f '' x) :=
  h.map hx hf

protected lemma map_elem {P : ∀ {α}, Matroid α → α → Prop} {Q : ∀ {β}, Matroid β → β → Prop}
    [h : InvariantFun (γ := id) (δ := id) P Q] [hP : GroundedPred (γ := id) P]
    {M : Matroid α} {f : α → β} {x}
    (hx : P M x) (hf : InjOn f M.E) : Q (M.map f hf) (f x) :=
  h.map hx hf

protected lemma and (P P' : ∀ {α}, Matroid α → (γ α) → Prop)
    (Q Q' : ∀ {β}, Matroid β → (δ β) → Prop) [h : InvariantFun P Q] [h' : InvariantFun P' Q'] :
    InvariantFun.{u,v} (fun M X ↦ P M X ∧ P' M X) (fun M X ↦ Q M X ∧ Q' M X) :=
  InvariantFun.combine P P' Q Q' And

protected lemma andSupported (P : ∀ {α}, Matroid α → γ α → Prop) (Q : ∀ {β}, Matroid β → δ β → Prop)
    [h : InvariantFun P Q] :
    InvariantFun (fun M X ↦ P M X ∧ S.supported M X) (fun M X ↦ Q M X ∧ T.supported M X) where
  of_empty α β hβ x hx := by
    rw [← h.of_empty, and_iff_left (C.supported_transferEmpty α β hβ x hx), and_iff_left hx]
  map_eq α β M f hf x hx := by simp [← h.map_eq hf, hx, C.supported_transfer]

protected lemma notAndSupported (P : ∀ {α}, Matroid α → γ α → Prop)
    (Q : ∀ {β}, Matroid β → δ β → Prop) [h : InvariantFun P Q] :
    InvariantFun (fun M X ↦ ¬ P M X ∧ S.supported M X) (fun M X ↦ ¬ Q M X ∧ T.supported M X) :=
  (h.comp_right (F := P) (G := Q) Not).andSupported

protected lemma minimal (P : ∀ {α}, Matroid α → Set α → Prop) (Q : ∀ {β}, Matroid β → Set β → Prop)
    [h : InvariantFun P Q] [hP : GroundedPred P] :
    InvariantFun (fun {α} M (X : Set α) ↦ Minimal (P M) X)
      (fun {β} N {Y : Set β} ↦ Minimal (Q N) Y) where
  of_empty α β hβ x hx := by
    obtain rfl : x = ∅ := by simpa using hx
    simpa [Minimal] using h.of_empty (α := α) hβ (x := ∅)
  map_eq α β M f hf X (hX : X ⊆ M.E) := by
    simp_rw [eq_iff_iff, minimal_subset_iff, ← h.map_eq hf hX, transfer_set_eq, and_congr_right_iff]
    refine fun hPX ↦ ⟨fun h' Y hY hYX ↦ ?_, fun h' Y hPY hYX ↦ ?_⟩
    · obtain ⟨Y, hYX', rfl⟩ := subset_image_iff.1 hYX
      rw [← transfer_set_eq, ← h.map_eq hf (hYX'.trans hX)] at hY
      rw [h' hY hYX']
    rw [← hf.image_eq_image_iff hX (hYX.trans hX), h' (h.map_set hPY hf) (image_mono hYX)]

protected lemma maximal (P : ∀ {α}, Matroid α → Set α → Prop) (Q : ∀ {β}, Matroid β → Set β → Prop)
    [h : InvariantFun P Q] [hP : GroundedPred P] [hQ : GroundedPred Q] :
    InvariantFun (fun {α} M (X : Set α) ↦ Maximal (P M) X)
      (fun {β} N {Y : Set β} ↦ Maximal (Q N) Y) where
  of_empty α β hβ x hx := by
    obtain rfl : x = ∅ := by simpa using hx
    have aux ⦃y⦄ (hy : P (emptyOn α) y) : y = ∅ := by simpa using hP.supported hy
    simpa [Maximal, and_iff_left aux] using h.of_empty (α := α) hβ
  map_eq α β M f hf X (hX : X ⊆ M.E) := by
    simp_rw [eq_iff_iff, maximal_subset_iff, ← h.map_eq hf hX, transfer_set_eq, and_congr_right_iff]
    refine fun hPX ↦ ⟨fun h' Y hY hYX ↦ ?_, fun h' Y hPY hYX ↦ ?_⟩
    · obtain ⟨Y, hYE, rfl⟩ := subset_image_iff.1 <| hQ.supported hY
      rw [hf.image_subset_image_iff hX hYE] at hYX
      rw [← transfer_set_eq, ← h.map_eq _ hYE] at hY
      rw [h' hY hYX]
    rw [← hf.image_eq_image_iff hX (hP.supported hPY), h' (h.map_set hPY hf) (image_mono hYX)]

section SetPred

end SetPred

section instances

instance instIndep : InvariantFun Indep Indep where
  of_empty := by simp
  map_eq α β M f hf X (hX : X ⊆ M.E) := by simp only [transfer_set_eq, map_image_indep_iff hX]

instance instCoindep : InvariantFun Coindep Coindep :=
  InvariantFun.dual Indep Indep

instance instDep : InvariantFun Dep Dep := by
  simpa [← dep_iff] using InvariantFun.notAndSupported Indep Indep

instance instBase : InvariantFun IsBase IsBase := by
  simpa [← isBase_iff_maximal_indep] using InvariantFun.maximal Indep Indep

instance instCodep : InvariantFun Codep Codep :=
  InvariantFun.dual Dep Dep

instance instSpanning : InvariantFun Spanning Spanning := by
  simpa [← spanning_iff_compl_coindep'] using (InvariantFun.compl Coindep Coindep).andSupported

instance instNonspanning : InvariantFun Nonspanning Nonspanning := by
  simpa [← nonspanning_iff] using InvariantFun.notAndSupported Spanning Spanning

end instances


-- protected instance instNot {P Q} [h : InvariantSetPred P Q] :
--     InvariantSetPred.{u, v} (fun M X ↦ ¬ P M X ∧ X ⊆ M.E) (fun M X ↦ ¬ Q M X ∧ X ⊆ M.E) where

-- protected lemma of_const (P : ∀ {α : Type u}, Set α → Prop)
--     (Q : ∀ {β : Type v}, Set β → Prop) (hPQ : ∀ {α β} (f : α → β) X, Q (f '' X) ↔ P X) :
--     InvariantSetPred.{u,v} (fun M X ↦ P X ∧ X ⊆ M.E) (fun M X ↦ Q X ∧ X ⊆ M.E) where
--   subset_ground_left := by simp
--   subset_ground_right := by simp
--   map_iff' α β M X f hf hX := by
--     rw [map_ground, and_iff_left (image_mono hX), and_iff_left hX, ← hPQ f X]

-- protected lemma and_setPred {P Q} [InvariantSetPred P Q] (P' : ∀ {α : Type u}, Set α → Prop)
--     (Q' : ∀ {β : Type v}, Set β → Prop) (hPQ : ∀ {α β} (f : α → β) X, Q' (f '' X) ↔ P' X) :
--     InvariantSetPred (fun M X ↦ P M X ∧ P' X) (fun N X ↦ Q N X ∧ Q' X) := by
--   convert @InvariantSetPred.instAnd (P := P) (Q := Q) _ _ _ (InvariantSetPred.of_const P' Q' hPQ)
--     using 4 with α M X β N Y
--   · simp +contextual [InvariantSetPred.subset_ground_left (P := P) (Q := Q)]
--   simp +contextual [InvariantSetPred.subset_ground_right (P := P) (Q := Q)]

end Pred

end InvariantFun


class InvariantSetPred (P : ∀ {α : Type u}, Matroid α → Set α → Prop)
    (Q : ∀ {β : Type v}, Matroid β → Set β → Prop) where
  subset_ground_left : ∀ ⦃α : Type u⦄ ⦃M : Matroid α⦄ ⦃X⦄, P M X → X ⊆ M.E
  subset_ground_right : ∀ ⦃β : Type v⦄ ⦃M : Matroid β⦄ ⦃X⦄, Q M X → X ⊆ M.E
  map_iff' : ∀ ⦃α : Type u⦄ ⦃β : Type v⦄ ⦃M : Matroid α⦄ ⦃X⦄ ⦃f : α → β⦄ (hf : InjOn f M.E),
      X ⊆ M.E → (P M X ↔ Q (M.map f hf) (f '' X))

namespace InvariantSetPred


protected instance instAnd {P P' Q Q'} [h : InvariantSetPred P Q]
    [h' : InvariantSetPred P' Q'] :
    InvariantSetPred.{u,v} (fun M X ↦ P M X ∧ P' M X) (fun M X ↦ Q M X ∧ Q' M X) where
  subset_ground_left _ _ _ h' := h.subset_ground_left h'.1
  subset_ground_right _ _ _ h' := h.subset_ground_right h'.1
  map_iff' α β M X f hf hX := by rw [h.map_iff' hf hX, h'.map_iff' hf hX]

protected lemma of_const (P : ∀ {α : Type u}, Set α → Prop)
    (Q : ∀ {β : Type v}, Set β → Prop) (hPQ : ∀ {α β} (f : α → β) X, Q (f '' X) ↔ P X) :
    InvariantSetPred.{u,v} (fun M X ↦ P X ∧ X ⊆ M.E) (fun M X ↦ Q X ∧ X ⊆ M.E) where
  subset_ground_left := by simp
  subset_ground_right := by simp
  map_iff' α β M X f hf hX := by
    rw [map_ground, and_iff_left (image_mono hX), and_iff_left hX, ← hPQ f X]

protected lemma and_setPred {P Q} [InvariantSetPred P Q] (P' : ∀ {α : Type u}, Set α → Prop)
    (Q' : ∀ {β : Type v}, Set β → Prop) (hPQ : ∀ {α β} (f : α → β) X, Q' (f '' X) ↔ P' X) :
    InvariantSetPred (fun M X ↦ P M X ∧ P' X) (fun N X ↦ Q N X ∧ Q' X) := by
  convert @InvariantSetPred.instAnd (P := P) (Q := Q) _ _ _ (InvariantSetPred.of_const P' Q' hPQ)
    using 4 with α M X β N Y
  · simp +contextual [InvariantSetPred.subset_ground_left (P := P) (Q := Q)]
  simp +contextual [InvariantSetPred.subset_ground_right (P := P) (Q := Q)]

protected instance instNot {P Q} [h : InvariantSetPred P Q] :
    InvariantSetPred.{u, v} (fun M X ↦ ¬ P M X ∧ X ⊆ M.E) (fun M X ↦ ¬ Q M X ∧ X ⊆ M.E) where
  subset_ground_left _ _ _ := And.right
  subset_ground_right _ _ _ := And.right
  map_iff' α β M X f hf hXE := by
    rw [← h.map_iff' _ hXE, map_ground, hf.image_subset_image_iff hXE subset_rfl]

protected instance instCompl {P Q} [h : InvariantSetPred.{u, v} P Q] :
    InvariantSetPred.{u, v} (fun M X ↦ P M (M.E \ X) ∧ X ⊆ M.E)
      (fun M X ↦ Q M (M.E \ X) ∧ X ⊆ M.E) where
  subset_ground_left _ _ _ := And.right
  subset_ground_right _ _ _ := And.right
  map_iff' α β M X f hf hXE := by
    rw [map_ground, ← hf.image_sdiff_subset hXE, ← h.map_iff' _ sdiff_subset,
      hf.image_subset_image_iff hXE subset_rfl]

protected instance instDual {P Q} [h : InvariantSetPred.{u, v} P Q] :
    InvariantSetPred.{u, v} (fun M X ↦ P M✶ X) (fun M X ↦ Q M✶ X) where
  subset_ground_left _ _ _ hP := by simpa using h.subset_ground_left hP
  subset_ground_right _ _ _ hP := by simpa using h.subset_ground_right hP
  map_iff' α β M X f hf hXE := by rw [map_dual, h.map_iff' (by simpa) (by simpa)]

protected instance instMinimal {P Q} [h : InvariantSetPred.{u, v} P Q] :
    InvariantSetPred.{u,v} (fun M X ↦ Minimal (P M) X) (fun M X ↦ Minimal (Q M) X) where
  subset_ground_left _ _ _ hP := h.subset_ground_left hP.1
  subset_ground_right _ _ _ hP := h.subset_ground_right hP.1
  map_iff' α β M X f hf hXE := by
    simp_rw [minimal_subset_iff, ← h.map_iff' _ hXE, and_congr_right_iff]
    refine fun hPX ↦ ⟨fun h' Y hQY hYX ↦ ?_, fun h' Y hY hYX ↦ ?_⟩
    · obtain ⟨Y, hY, rfl⟩ := subset_image_iff.1 (h.subset_ground_right hQY)
      rw [← h.map_iff' _ hY] at hQY
      rw [hf.image_subset_image_iff hY hXE] at hYX
      rw [h' hQY hYX]
    specialize h' (t := f '' Y) (by rwa [← h.map_iff' _ (hYX.trans hXE)]) (image_mono hYX)
    rwa [hf.image_eq_image_iff hXE (hYX.trans hXE)] at h'

protected instance instMaximal {P Q} [h : InvariantSetPred.{u, v} P Q] :
    InvariantSetPred.{u,v} (fun M X ↦ Maximal (P M) X) (fun M X ↦ Maximal (Q M) X) where
  subset_ground_left _ _ _ hP := h.subset_ground_left hP.1
  subset_ground_right _ _ _ hP := h.subset_ground_right hP.1
  map_iff' α β M X f hf hXE := by
    simp_rw [maximal_subset_iff, ← h.map_iff' _ hXE, and_congr_right_iff]
    refine fun hPX ↦ ⟨fun h' Y hQY hYX ↦ ?_, fun h' Y hY hYX ↦ ?_⟩
    · obtain ⟨Y, hY, rfl⟩ := subset_image_iff.1 (h.subset_ground_right hQY)
      rw [← h.map_iff' _ hY] at hQY
      rw [hf.image_subset_image_iff hXE hY] at hYX
      rw [h' hQY hYX]
    have hYE := h.subset_ground_left hY
    specialize h' (t := f '' Y) (by rwa [← h.map_iff' _ hYE]) (image_mono hYX)
    rwa [hf.image_eq_image_iff hXE hYE] at h'

instance instIndep : InvariantSetPred Indep Indep where
  subset_ground_left _ _ _ := Indep.subset_ground
  subset_ground_right _ _ _ := Indep.subset_ground
  map_iff' α β M X f hf hX := by rwa [map_image_indep_iff]

instance instCoindep : InvariantSetPred Coindep Coindep :=
  InvariantSetPred.instDual (h := instIndep)

instance instDep : InvariantSetPred Dep Dep := by
  convert InvariantSetPred.instNot (h := instIndep) with α M I <;> rw [dep_iff]

instance instBase : InvariantSetPred IsBase IsBase := by
  convert InvariantSetPred.instMaximal (h := instIndep) with α M B <;> rw [isBase_iff_maximal_indep]

instance instCodep : InvariantSetPred Codep Codep :=
  InvariantSetPred.instDual (h := instDep)

instance instSpanning : InvariantSetPred Spanning Spanning := by
  convert InvariantSetPred.instCompl (P := Coindep) (Q := Coindep) with α M X β N X
  · by_cases hX : X ⊆ M.E
    · rw [spanning_iff_compl_coindep, and_iff_left hX]
    exact iff_of_false (fun h ↦ hX h.subset_ground) <| by simp [hX]
  by_cases hX : X ⊆ N.E
  · rw [spanning_iff_compl_coindep, and_iff_left hX]
  exact iff_of_false (fun h ↦ hX h.subset_ground) <| by simp [hX]

instance instNonspanning : InvariantSetPred Nonspanning Nonspanning := by
  convert InvariantSetPred.instNot (P := Spanning) (Q := Spanning) <;>
  simp [nonspanning_iff]

instance cardLE {k : ℕ∞} : InvariantSetPred (fun M X ↦ X.encard ≤ k ∧ X ⊆ M.E)
    (fun M X ↦ X.encard ≤ k ∧ X ⊆ M.E) where
  subset_ground_left _ _ _ := And.right
  subset_ground_right _ _ _ := And.right
  map_iff' α β M X f hf hXE := by
    rw [(hf.mono hXE).encard_image, map_ground, hf.image_subset_image_iff hXE subset_rfl]

protected lemma map_iff {P Q} [hi : InvariantSetPred P Q] {Y : Set β} (hf : InjOn f M.E) :
    Q (M.map f hf) Y ↔ ∃ X, P M X ∧ Y = f '' X := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨X, hX, rfl⟩ := subset_image_iff.1 <| hi.subset_ground_right h
    rw [← hi.map_iff' _ hX] at h
    exact ⟨X, h, rfl⟩
  rintro ⟨X, hX, rfl⟩
  rwa [← hi.map_iff' _ (hi.subset_ground_left hX)]

protected lemma mapEquiv_iff {P Q} [hi : InvariantSetPred P Q] {Y : Set β} (f : α ≃ β) :
    Q (M.mapEquiv f) Y ↔ P M (f ⁻¹' Y) := by
  simp_rw [mapEquiv_eq_map, InvariantSetPred.map_iff f.injective.injOn (P := P) (Q := Q),
    f.eq_image_iff_symm_image_eq, f.image_symm_eq_preimage]
  grind

protected lemma mapEmbedding_iff {P Q} [hi : InvariantSetPred P Q] {Y : Set β} (f : α ↪ β) :
    Q (M.mapEmbedding f) Y ↔ ∃ X, P M X ∧ Y = f '' X := by
  simp_rw [mapEmbedding, InvariantSetPred.map_iff f.injective.injOn (P := P) (Q := Q)]

protected lemma map {P Q} [hi : InvariantSetPred P Q] {X : Set α} (hX : P M X) (hf : InjOn f M.E) :
    Q (M.map f hf) (f '' X) := by
  rw [InvariantSetPred.map_iff (P := P) (Q := Q)]
  exact ⟨X, hX, rfl⟩

end InvariantSetPred

class InvariantElemPred (P : ∀ {α : Type u}, Matroid α → α → Prop)
    (Q : ∀ {β : Type v}, Matroid β → β → Prop) where
  mem_ground_left : ∀ ⦃α : Type u⦄ ⦃M : Matroid α⦄ ⦃x⦄, P M x → x ∈ M.E
  subset_ground_right : ∀ ⦃β : Type v⦄ ⦃M : Matroid β⦄ ⦃x⦄, Q M x → x ∈ M.E
  map_iff' : ∀ ⦃α : Type u⦄ ⦃β : Type v⦄ ⦃M : Matroid α⦄ ⦃x⦄ ⦃f : α → β⦄ (hf : InjOn f M.E),
      x ∈ M.E → (P M x ↔ Q (M.map f hf) (f x))

class InvariantSetPred₂ (P : ∀ {α : Type u}, Matroid α → Set α → Set α → Prop)
    (Q : ∀ {β : Type v}, Matroid β → Set β → Set β → Prop) where
  subset_ground_left : ∀ ⦃α : Type u⦄ ⦃M : Matroid α⦄ ⦃X Y⦄, P M X Y → X ⊆ M.E ∧ Y ⊆ M.E
  subset_ground_right : ∀ ⦃β : Type v⦄ ⦃M : Matroid β⦄ ⦃X Y⦄, Q M X Y → X ⊆ M.E ∧ Y ⊆ M.E
  map_iff' : ∀ ⦃α : Type u⦄ ⦃β : Type v⦄ ⦃M : Matroid α⦄ ⦃X Y⦄ ⦃f : α → β⦄ (hf : InjOn f M.E),
      X ⊆ M.E → Y ⊆ M.E → (P M X Y ↔ Q (M.map f hf) (f '' X) (f '' Y))

end InvariantSetPred

-- protected class hasSupport (M : Matroid α) (γ : Type u) where
--   supported : γ → Prop

-- instance {M : Matroid α} : M.hasSupport α where
--   supported e := e ∈ M.E

-- instance {M : Matroid α} : M.hasSupport (Set α) where
--   supported X := X ⊆ M.E

-- instance {M : Matroid α} : M.hasSupport (List α) where
--   supported L := {e | e ∈ L} ⊆ M.E

-- instance {M : Matroid α} : M.hasSupport (Finset α) where
--   supported X := (X : Set α) ⊆ M.E

-- -- class hasTransfer (α : Type u) (β : Type v) (γ : Type u) (δ : Type v) where
-- --   apply : (α → β) → γ → δ
-- --   valid : γ → δ → Prop

-- protected class Transfer (γ : Type u → Sort u') (δ : Type v → Sort v') where
--   -- apply : ∀ ⦃α : Type u⦄ ⦃β : Type v⦄, (α → β) → γ α → δ β
--   equiv : ∀ {α : Type u} {β : Type v}, (α → β) → Matroid α → γ α → Matroid β → δ β → Prop

-- instance : Matroid.Transfer (id : Type u → Type u) (id : Type v → Type v) where
--   equiv f M x N y := x ∈ M.E ∧ y ∈ N.E ∧ y = f x

-- instance : Matroid.Transfer Set Set where
--   equiv f M x N y := x ⊆ M.E ∧ y ⊆ N.E ∧ y = f '' x

-- instance : Matroid.Transfer List List where
--   equiv f M L N L' := {e | e ∈ L} ⊆ M.E ∧ {e | e ∈ L'} ⊆ N.E ∧ L' = L.map f

-- instance Transfer.instPred (γ : Type u → Type u) (δ : Type v → Type v) [h : Matroid.Transfer γ δ]
--     Matroid.Transfer (fun α ↦ (γ α) → Prop) (fun β ↦ (δ β) → Prop) where
--   equiv f M x N y := ∀ a b, (h.equiv f M a N b) → (x a ↔ y b)

-- instance Transfer.instFun (γ γ' : Type u → Type u) (δ δ' : Type v → Type v)
--     [h : Matroid.Transfer γ δ] [h' : Matroid.Transfer γ' δ'] :
--     Matroid.Transfer (fun α ↦ (γ α) → (γ' α)) (fun β ↦ (δ β) → (δ' β)) where
--   equiv f M x N y := ∀ a b , h.equiv f M a N b → h'.equiv f M (x a) N (y b)

-- @[simp]
-- lemma Transfer.map_iff_of_setPred (P : Set α → Prop) (Q : Set β → Prop) (M : Matroid α)
--     (f : α → β) (hf : InjOn f M.E) :
--     Transfer.equiv (γ := fun α ↦ (Set α → Prop)) (δ := fun β ↦ (Set β → Prop))
--       f M P (M.map f hf) Q ↔ ∀ X ⊆ M.E, P X ↔ Q (f '' X) := by
--   change (∀ a b, ((_ ∧ _) → _)) ↔ _
--   refine ⟨fun h X hX ↦ h X (f '' X) ⟨hX, by grw [map_ground, hX], rfl⟩, fun h X Y ↦ ?_⟩
--   rintro ⟨hX, -, rfl⟩
--   exact h X hX

-- @[mk_iff]
-- class Invariant {γ : Type u → Sort u'} {δ : Type v → Sort v'} [hT : Matroid.Transfer γ δ]
--     (P : ∀ {α : Type u}, Matroid α → (γ α)) (Q : ∀ {β : Type v}, Matroid β → (δ β)) where
--   equiv_map : ∀ ⦃α : Type u⦄ ⦃β : Type v⦄ ⦃M : Matroid α⦄ ⦃f : α → β⦄ (hf : InjOn f M.E),
--       hT.equiv f M (P M) (M.map f hf) (Q (M.map f hf))

-- instance invariant_indep : Invariant Matroid.Indep.{u} Matroid.Indep.{v} where
--   equiv_map := by
--     simp only [Transfer.map_iff_of_setPred]
--     intro α β M f hf X hXE
--     rw [map_image_indep_iff hXE]


-- protected lemma map_iff {P : ∀ {α : Type u}, Matroid α → Set α → Prop}
--     {Q : ∀ {β : Type v}, Matroid β → Set β → Prop} [hi : Invariant P Q] {Y : Set β}
--     (hf : InjOn f M.E) : Q (M.map f hf) Y ↔ ∃ X, P M X ∧ Y = f '' X := by
--   simp only [invariant_iff, Transfer.map_iff_of_setPred] at hi
--   refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
--   ·


  -- refine ⟨fun h ↦ ?_, ?_⟩
  -- · obtain ⟨X, hX, rfl⟩ := subset_image_iff.1 <| hi.subset_ground_right h
  --   rw [← hi.map_iff' _ hX] at h
  --   exact ⟨X, h, rfl⟩
  -- rintro ⟨X, hX, rfl⟩
  -- rwa [← hi.map_iff' _ (hi.subset_ground_left hX)]



-- instance : Transfer (fun (α : Type u) ↦ (Set α → Prop)) (fun (β : Type v) ↦ (Set β → Prop))
--     infer_instance





  -- eq_apply_of_equiv : ∀ ⦃α : Type u⦄ ⦃β : Type v⦄ ⦃x : γ α⦄ ⦃y : δ β⦄, equiv x y → y = apply f x
  -- valid_left : ∀ ⦃α : Type u⦄, Matroid α → γ α → Prop
  -- valid_right : ∀ ⦃β : Type v⦄, Matroid β → δ β → Prop

-- instance (α : Type u) (β : Type v) : hasTransfer α β (Set α) (Set β) where
--   apply := Set.image

-- instance (α : Type u) (β : Type v) : hasTransfer α β α β where
--   apply := id

-- instance (α : Type u) (β : Type v) : hasTransfer α β (List α) (List β) where
--   apply := List.map


-- protected class hasAction (γ : Type u) (γ' : Type v) where
